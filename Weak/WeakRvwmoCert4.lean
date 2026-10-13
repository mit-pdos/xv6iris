/-
Weak: **B2e-3b slice 3c — the cycle-order certification.**

Rocq: `iris/WeakRvwmoCert4.v` @ xxvzwolszwmp.

## The Rocq header, in substance

`WeakRvwmoCert3.certSegment'` certifies ONE hart's segment against a carried context `Ctx`;
slice 3c walks it around an `R`-cycle.  Three things are landed here.

(1) THE RENAMING RECONCILIATION (§2–§3).  `hullRealizableOfAcyclic` hands back rows equal to
the HULL's rows up to `lblRen pi`; composed with `gxhRow` (`hullRealizableRowsG`, §2.1) the
total renaming against `G`'s OWN rows is `pi ∘ hren G cs`.  `hren` IS the identity exactly when
the cut is gmo-DOWNWARD-CLOSED on writes (`wcutClosed`, §2.2) — then the hull's labels are
literally `G`'s (`gxhLblEq`, §2.3) and a `CtracePrefix` of the HULL is one of `G`
(`ctracePrefixOfHull`, §3.1).  `hullOk` does NOT imply `wcutClosed`.

(2) THE FLOOR DOES NOT TOLERATE A RENAMED LOG (§3.2): `ctpWix` FORCES the candidate's writes to
be appended in gmo order (`ctpWixGmoMono`, `certLogIsGmoPrefix`).

(3) THE CYCLE ITERATION (§4–§5).  `segsRun` is the walk around the cycle — a list of
per-segment certifications, each one a `segStep`, threaded through a `CycState` = (candidate,
process supply, device supply).  `certCycle`: the walk ends at a consistent candidate with a
real `execProgOk'` supply at the quiet fabric, and every segment's appended trace sits at a
KNOWN OFFSET in the final candidate (`segsRunStable`), so exit writes (`certCycleExitMsg`) and
entry reads (`certCyclePos`) are addressable.  `segStepOfSegment` (§4.3) shows the interface is
what `certSegment''` delivers; §5.1 that a one-segment cycle cannot exist; §5.6 non-vacuity on
the real `sw &started` block.  §6 (what the slice leaves open) and §7 (`Print Assumptions`) are
Rocq comments/audit, not ported (the lint's axiom/sorry ban is the audit).

## Deviations from Rocq

1. NAMES/TYPES as `WeakRvwmoCert3` deviation 1 (camelCase; `S k` ↦ `k + 1`; `l !! n` ↦
   `l[n]?`; `cd_log_end` ↦ `cdLogEnd`; `Racy` ↦ `racy`; `gpo` ↦ `WeakRvwmoGraph.gpo`;
   `WMsg b v t k` ↦ the `Wmsg` literal; `Forall2` ↦ `List.Forall₂`; `seq 0 N` ↦
   `List.range' 0 N`).  Constructors `segs_done`/`segs_more` ↦ `segsDone`/`segsMore`.
   Bound state names `S`/`S'` are `St`/`St'`.
2. `filterDownwardPrefix` is stated for a Boolean predicate `P : α → Bool` (Lean's
   `List.filter`), Rocq's decidable `P : A → Prop`; `cycleOk`'s `Forall cyseg_ok l` is
   `∀ o, o ∈ l → cysegOk o`.
3. O2 / STAGE C — THE PINNED LTS (`WeakRvwmoSupply` deviation 2, `WeakRvwmoCert2` deviation 4).
   `hullRealizableRowsG` is Rocq's `∃ c pst rho` again (Stage B's `candFetchInert` conditional
   is DELETED), its supply at `pstepPin c.cdImg pstepEv`; `cstOk` (hence `segStep`, `segsRun`)
   and `certCycle` state the supply at `pstepPin St.cstC.cdImg pstepEv`.
4. O2 / STAGE C, policy (`WeakRvwmoCert3b` deviation 8): `segStepOfSegment`'s Stage-B
   `lbFetchInert` conjunct of `Hpol''` is DELETED; `Hpol''` takes and returns
   `WeakRvwmoCert2.cblkPin c0.cdImg` blocks, `Hpolp : cpolpr …` is on pinned pair blocks, and
   the new premise `WeakRvwmoCert2.esPin St.cstC.cdImg es` follows `LDev ∉ es.map Prod.fst`;
   `segsRunWitness` supplies them through `polStore'` and `WeakRvwmoCert2.nvPin`.
5. Rocq's `Section nonvacuity4` context (`cpu rs ib d0`) is `nv4S0`/`nv4S0Ok`/
   `segsRunWitness`'s leading parameters; Rocq's `img0` notation is the literal `fun _ => none`.

**Rocq → Lean name map.**  `filter_downward_prefix` `filterDownwardPrefix`,
`fmap_id_pointwise` `fmapIdPointwise`, `gwix_pos_elem` `gwixPosElem`, `hull_realizable_rows_G`
`hullRealizableRowsG`, `wcut_closed` `wcutClosed`, `wcut_closed_prefix` `wcutClosedPrefix`,
`hull_gwix_eq` `hullGwixEq`, `hren_id` `hrenId`, `gxh_lbl_eq` `gxhLblEq`,
`ctrace_prefix_of_hull` `ctracePrefixOfHull`, `cpol_ctx_of_hull` `cpolCtxOfHull`,
`es_msg_len_w` `esMsgLenW`, `ctp_wix_gmo_mono` `ctpWixGmoMono`, `cert_log_is_gmo_prefix`
`certLogIsGmoPrefix`, `cyc_state` `CycState` (`CSt`/`cst_c`/`cst_pst`/`cst_dv` ↦
`mk`/`cstC`/`cstPst`/`cstDv`), `cst_ok` `cstOk`, `segout` `Segout` (`SegOut`/`so_hart`/
`so_row`/`so_off`/`so_tr` ↦ `mk`/`soHart`/`soRow`/`soOff`/`soTr`), `seg_step` `segStep`,
`segs_run` `segsRun`, `segs_run_ok` `segsRunOk`, `segs_run_start` `segsRunStart`,
`segs_run_prefix` `segsRunPrefix`, `segs_run_stable` `segsRunStable`, `segs_run_elem`
`segsRunElem`, `seg_step_of_segment` `segStepOfSegment`, `cyseg` `Cyseg` (`CySeg`/`cy_hart`/
`cy_entry`/`cy_exit` ↦ `mk`/`cyHart`/`cyEntry`/`cyExit`), `cyseg_ok` `cysegOk`, `cy_link`
`cyLink`, `cycle_ok` `cycleOk`, `cycle_two_segments` `cycleTwoSegments`, `cy_backward`
`cyBackward`, `cy_backward_not_aq` `cyBackwardNotAq`, `cert_cycle` `certCycle`,
`cert_cycle_pos` `certCyclePos`, `exit_msg_in_log` `exitMsgInLog`, `cert_cycle_exit_msg`
`certCycleExitMsg`, `segs_run_snoc` `segsRunSnoc`, `nv4_S0` `nv4S0`, `nv4_S0_ok` `nv4S0Ok`,
`segs_run_witness` `segsRunWitness`, `cycle_two_harts` `cycleTwoHarts`, `nv4_one_hart`
`nv4OneHart`.

**File-qualified names:** none (no name of this file is in `notes/weak-port-dupnames.json`;
no Lean-only helpers).

**Dropped:** none (Rocq 42 declarations + the `img0` notation; Lean 42).

**W12 (1) (plan §C W12; D25 (a) [OWN.5]) — statement edit (Lean-only).**  `hullRealizableRowsG` takes the core `rvwmoCoreD`.  RVWMO⁻ callers
are unchanged in text (`WeakRvwmoAcyc.coeCoreOfMinus`).
-/
import Weak.WeakRvwmoCert3b
import Weak.WeakRvwmoLinInd

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D
open Wlabel

/-- The parked-fence field, abbreviated (as in `WeakRvwmoCert2`). -/
local notation "Ofence" => Option (Bool × Bool × Bool × Bool)

/-! # 1. TWO LIST FACTS -/

/-- A filter whose predicate is DOWNWARD CLOSED along the list is a PREFIX of it. -/
theorem filterDownwardPrefix {α : Type _} (P : α → Bool) (l : List α) :
    (∀ (i j : Nat) (x y : α), i < j → l[i]? = some x → l[j]? = some y → P y = true →
      P x = true) →
    l.filter P = l.take (l.filter P).length := by
  induction l with
  | nil => intro _; rfl
  | cons x l ih =>
    intro hdc
    cases hx : P x with
    | true =>
      rw [List.filter_cons_of_pos hx, List.length_cons, List.take_succ_cons]
      congr 1
      exact ih (fun i j y z hij hi hj hz => hdc (i + 1) (j + 1) y z (by omega) hi hj hz)
    | false =>
      rw [List.filter_cons_of_neg (by simp [hx])]
      have hnil : l.filter P = [] := by
        cases hl : l.filter P with
        | nil => rfl
        | cons y tl =>
          exfalso
          have hy : y ∈ l.filter P := by rw [hl]; simp
          rw [List.mem_filter] at hy
          obtain ⟨j, hj⟩ := elem_of_list_lookup.1 hy.1
          have h := hdc 0 (j + 1) x y (by omega) rfl hj hy.2
          rw [hx] at h
          exact Bool.false_ne_true h
      rw [hnil]
      rfl

/-- A pointwise-identity `map`. -/
theorem fmapIdPointwise {α : Type _} (f : α → α) (l : List α) :
    (∀ (i : Nat) (x : α), l[i]? = some x → f x = x) → l.map f = l := by
  induction l with
  | nil => intro _; rfl
  | cons x l ih =>
    intro h
    rw [List.map_cons, h 0 x rfl]
    congr 1
    exact ih (fun i y hy => h (i + 1) y hy)

/-- `gwix` is positive only on writes. -/
theorem gwixPosElem (G : Gexec) (e : Geid) : 0 < gwix G e → e ∈ gwrites G := by
  unfold gwix
  cases hf : listFind (fun e' => decide (e' = e)) (gwrites G) with
  | some q =>
    obtain ⟨i, y⟩ := q
    intro _
    obtain ⟨hi, hy, _⟩ := list_find_Some.1 hf
    have : y = e := of_decide_eq_true hy
    subst this
    exact elem_of_list_lookup_2 hi
  | none => intro h; exact absurd h (Nat.lt_irrefl 0)

/-! # 2. THE RENAMING RECONCILIATION -/

/-! ## 2.1 The renaming a realized hull actually carries -/

theorem hullRealizableRowsG (boot : Nat → Pexv6) (d0 : Efab) (im : Image) (nh : Nat)
    (GD : Gdexec) (cs : List Nat) (N : Nat) :
    rvwmoCoreD GD →
    gdexecQconf boot d0 im nh GD →
    properCut GD.gdG cs →
    (∀ x, ¬ tc (racyD (gdHull GD cs)) x x) →
    GD.gdG.gxProg.length ≤ N →
    ∃ (c : Cand) (pst : Nat → List Pexv6) (rho : Nat → Nat),
      srvwmoConsistent c ∧
      c.cdImg = GD.gdG.gxImg ∧
      pst 0 = (List.range' 0 N).map boot ∧
      execProgOk' (pstepPin c.cdImg pstepEv) pclsEv pst (fun _ => d0) (candExec c) ∧
      (∀ i, (c.cdTr.filter (fun s => decide (s.esAg = i))).map (fun s => s.esLb) =
        (List.take ((cs[i]?).getD 0) ((GD.gdG.gxProg[i]?).getD [])).map (lblRen rho)) := by
  intro hcons hq hpc hacy hN
  obtain ⟨c, pst, pi, hc, himg, hpst0, hpst, hrow⟩ :=
    hullRealizableOfAcyclic boot d0 im nh GD cs N hcons hq hpc hacy hN
  refine ⟨c, pst, fun t => pi (hren GD.gdG cs t), hc, himg, hpst0, hpst, fun i => ?_⟩
  rw [hrow i, gxhRow]
  exact rowRenComp (hren GD.gdG cs) pi _ _ (fun _ => rfl)

/-! ## 2.2 When `hren` is the identity: a gmo-downward-closed cut -/

/-- THE SIDE CONDITION.  `hullOk` is po-closure + rf-closure; it says NOTHING about `co`. -/
def wcutClosed (G : Gexec) (cs : List Nat) : Prop :=
  ∀ w1 w2, w1 ∈ gwrites G → w2 ∈ gwrites G → gcut cs w2 = true →
    gwix G w1 < gwix G w2 → gcut cs w1 = true

/-- Under it the hull's writes are a PREFIX of `G`'s. -/
theorem wcutClosedPrefix (G : Gexec) (cs : List Nat) :
    G.gxGmo.Nodup → wcutClosed G cs →
    gwrites (gxHull G cs) = (gwrites G).take (gwrites (gxHull G cs)).length := by
  intro hnd hwc
  rw [gxhGwritesG]
  apply filterDownwardPrefix
  intro i j x y hij hi hj hy
  apply hwc x y (gwritesLookupElem G i x hi) (gwritesLookupElem G j y hj) hy
  rw [gwixOfLookup G i x hnd hi, gwixOfLookup G j y hnd hj]
  omega

/-- … so a hull write's index is unchanged. -/
theorem hullGwixEq (G : Gexec) (cs : List Nat) (w : Geid) :
    G.gxGmo.Nodup → wcutClosed G cs →
    w ∈ gwrites G → gcut cs w = true →
    gwix (gxHull G cs) w = gwix G w := by
  intro hnd hwc hw hc
  have hmem : w ∈ gwrites (gxHull G cs) := (gxhGwritesElem G cs w).2 ⟨hc, hw⟩
  obtain ⟨i, hi, heq⟩ := gwixLookup (gxHull G cs) w hmem
  rw [heq]
  symm
  apply gwixOfLookup G i w hnd
  rw [wcutClosedPrefix G cs hnd hwc] at hi
  exact (lookup_take_Some.1 hi).1

theorem hrenId (G : Gexec) (cs : List Nat) (t : Nat) :
    G.gxGmo.Nodup → wcutClosed G cs →
    (∀ w, gwriteAt G t = some w → gcut cs w = true) →
    hren G cs t = t := by
  intro hnd hwc hcut
  unfold hren
  cases ht : gwriteAt G t with
  | none => rfl
  | some w =>
    have hc : gcut cs w = true := hcut w ht
    simp only [hc, if_true]
    rw [← gxhGwix]
    obtain ⟨hw, rfl⟩ := gwriteAtInv G t w hnd ht
    exact hullGwixEq G cs w hnd hwc hw hc

/-! ## 2.3 THE PAYOFF: the hull's labels are `G`'s own -/

theorem gxhLblEq (G : Gexec) (cs : List Nat) (e : Geid) :
    gwf G → hullOk G cs → wcutClosed G cs → gcut cs e = true →
    gxLbl (gxHull G cs) e = gxLbl G e := by
  intro hwf hok hwc hc
  have hnd : G.gxGmo.Nodup := hwf.1
  rw [gxhLbl, hc, if_pos rfl]
  cases hl : gxLbl G e with
  | none => rfl
  | some l =>
    show some (lblRen (hren G cs) l) = some l
    have hts : ∀ base ts vs, lbRd l = some (base, ts, vs) → ts.map (hren G cs) = ts := by
      intro base ts vs hrd
      have hlen : vs.length = ts.length := by
        have hsh := WeakRvwmoFloor.gshape G hwf e l hl
        cases l with
        | LLoad aq b ts' vs' =>
          simp only [lbRd, Option.some.injEq, Prod.mk.injEq] at hrd
          obtain ⟨-, rfl, rfl⟩ := hrd
          exact hsh
        | LStore => simp [lbRd] at hrd
        | LFence => simp [lbRd] at hrd
        | LRmw aq rl b ts' rvs wvs k =>
          simp only [lbRd, Option.some.injEq, Prod.mk.injEq] at hrd
          obtain ⟨-, rfl, rfl⟩ := hrd
          exact hsh.2.2
        | LIo => simp [lbRd] at hrd
      apply fmapIdPointwise
      intro j t hj
      apply hrenId G cs t hnd hwc
      intro w hw
      obtain ⟨v, hv⟩ : ∃ v, vs[j]? = some v := by
        have hlt : j < vs.length := by rw [hlen]; exact lookup_lt_Some hj
        exact ⟨vs[j], List.getElem?_eq_getElem hlt⟩
      exact hullOkRf G cs e (accAddr base j) t v w hok hc ⟨l, base, ts, vs, j, hl, hrd, hj, hv, rfl⟩
        hw
    cases l with
    | LLoad aq base ts vs =>
      show some (Lbl.LLoad aq base (ts.map (hren G cs)) vs) = _
      rw [hts base ts vs rfl]
    | LStore => rfl
    | LFence => rfl
    | LRmw aq rl base ts rvs wvs kc =>
      show some (Lbl.LRmw aq rl base (ts.map (hren G cs)) rvs wvs kc) = _
      rw [hts base ts rvs rfl]
    | LIo => rfl

/-! # 3. THE BRIDGE, AND WHY IT CANNOT BE DONE UP TO A RENAMING -/

/-! ## 3.1 A certified prefix of the HULL is a certified prefix of `G` -/

theorem ctracePrefixOfHull (G : Gexec) (cs : List Nat) (c : Cand) (ev : Nat → Geid)
    (W : Geid → Prop) :
    gwf G → hullOk G cs → wcutClosed G cs →
    (∀ p s, c.cdTr[p]? = some s → gcut cs (ev p) = true) →
    CtracePrefix (gxHull G cs) c ev W →
    CtracePrefix G c ev W := by
  intro hwf hok hwc hcut hgt
  have hnd : G.gxGmo.Nodup := hwf.1
  have hlbl : ∀ e, gcut cs e = true → gxLbl (gxHull G cs) e = gxLbl G e :=
    fun e he => gxhLblEq G cs e hwf hok hwc he
  have hnd' : (gxHull G cs).gxGmo.Nodup := by
    show (G.gxGmo.filter (gcut cs)).Nodup
    exact NoDup_filter hnd
  -- a hull write index IS a G write index
  have hwix : ∀ e, 0 < gwix (gxHull G cs) e → gwix (gxHull G cs) e = gwix G e := by
    intro e he
    obtain ⟨hc, hw⟩ := (gxhGwritesElem G cs e).1 (gwixPosElem _ e he)
    exact hullGwixEq G cs e hnd hwc hw hc
  refine ⟨hgt.ctpImg.trans (gxhImg G cs), hgt.ctpAg, hgt.ctpPos, ?_, ?_, ?_⟩
  · intro p s hs
    have hle : gxLbl (gxHull G cs) (ev p) = gxLbl G (ev p) := hlbl _ (hcut p s hs)
    have hwit : cwitStep (gxHull G cs) c ev p s ↔ cwitStep G c ev p s := by
      unfold cwitStep
      rw [hle]
    have hpois : cpoisStep (gxHull G cs) c ev p s ↔ cpoisStep G c ev p s := by
      unfold cpoisStep
      rw [hle, hwit]
    rcases hgt.ctpStep p s hs with ⟨hnW, hl⟩ | ⟨hW, hw⟩ | hp
    · exact .inl ⟨hnW, hle ▸ hl⟩
    · exact .inr (.inl ⟨hW, hwit.1 hw⟩)
    · exact .inr (.inr (hpois.1 hp))
  · intro p s hs hw
    have h := hgt.ctpWix p s hs hw
    rw [← hwix (ev p) (by rw [h]; omega)]
    exact h
  · intro s hs hle
    obtain ⟨w, hw, heq⟩ := hgt.ctpLog s hs hle
    obtain ⟨hmem, hix⟩ := gwriteAtInv (gxHull G cs) s w hnd' hw
    obtain ⟨hc, hmem⟩ := (gxhGwritesElem G cs w).1 hmem
    have hg : gwix G w = s := by rw [← hix, hullGwixEq G cs w hnd hwc hmem hc]
    refine ⟨w, by rw [← hg]; exact gwriteAtGwix G w hmem, ?_⟩
    rw [heq]
    unfold gwmsg
    rw [hlbl w hc]

/-- The certification context transported the same way. -/
theorem cpolCtxOfHull (G : Gexec) (cs : List Nat) (W : Geid → Prop) (x : Nat) (c : Cand) :
    gwf G → hullOk G cs → wcutClosed G cs →
    (∃ ev, CtracePrefix (gxHull G cs) c ev W ∧
      (∀ p s, c.cdTr[p]? = some s → gcut cs (ev p) = true) ∧
      witFenceUb G c ev W (x, gcnt x c.cdTr) ∧
      poisOkHart G c ev x) →
    cpolCtx G W x c := by
  rintro hwf hok hwc ⟨ev, hgt, hcut, hub, hpd⟩
  exact ⟨ev, ctracePrefixOfHull G cs c ev W hwf hok hwc hcut hgt, hub, hpd⟩

/-! ## 3.2 THE OBSTRUCTION, as an identity rather than a counterexample -/

theorem esMsgLenW (s : Estep) : lbIsW s.esLb = true → (esMsg s).length = 1 := by
  intro hw
  obtain ⟨base, vs, hwr⟩ := lbIsWWr _ hw
  unfold esMsg
  rw [hwr]
  rfl

theorem ctpWixGmoMono (G : Gexec) (c : Cand) (ev : Nat → Geid) (W : Geid → Prop) (p q : Nat)
    (sp sq : Estep) :
    CtracePrefix G c ev W →
    c.cdTr[p]? = some sp → c.cdTr[q]? = some sq →
    lbIsW sp.esLb = true → lbIsW sq.esLb = true →
    p < q → gwix G (ev p) < gwix G (ev q) := by
  intro hgt hp hq hwp hwq hpq
  rw [hgt.ctpWix p sp hp hwp, hgt.ctpWix q sq hq hwq]
  have h1 : (cdLog c (p + 1)).length = (cdLog c p).length + 1 := by
    rw [cdLogS c p sp hp, List.length_append, esMsgLenW sp hwp]
  have h2 : (cdLog c (p + 1)).length ≤ (cdLog c q).length := cdLogLenLe c (p + 1) q (by omega)
  omega

/-- The certified log IS a gmo prefix. -/
theorem certLogIsGmoPrefix (G : Gexec) (c : Cand) (ev : Nat → Geid) (W : Geid → Prop) (p : Nat)
    (s : Estep) :
    CtracePrefix G c ev W → c.cdTr[p]? = some s →
    lbIsW s.esLb = true →
    gwriteAt G ((cdLog c p).length + 1) = some (ev p) ∧
    gwix G (ev p) = (cdLog c p).length + 1 := by
  intro hgt hs hw
  have hix : gwix G (ev p) = (cdLog c p).length + 1 := hgt.ctpWix p s hs hw
  refine ⟨?_, hix⟩
  rw [← hix]
  exact gwriteAtGwix G _ (gwixPosElem G _ (by omega))

/-! # 4. THE CYCLE ITERATION -/

/-! ## 4.1 The object that is threaded -/

structure CycState where
  cstC : Cand
  cstPst : Nat → List Pexv6
  cstDv : Nat → Efab

def cstOk (d0 : Efab) (St : CycState) : Prop :=
  srvwmoConsistent St.cstC ∧
  execProgOk' (pstepPin St.cstC.cdImg pstepEv) pclsEv St.cstPst St.cstDv (candExec St.cstC) ∧
  St.cstDv (cdEnd St.cstC) = d0

/-! ## 4.2 One segment, and the walk -/

structure Segout where
  soHart : Nat
  soRow : List Lbl
  soOff : Nat
  soTr : List Estep

def segStep (d0 : Efab) (o : Segout) (St St' : CycState) : Prop :=
  cstOk d0 St ∧
  cstOk d0 St' ∧
  o.soOff = cdEnd St.cstC ∧
  St'.cstC.cdTr = St.cstC.cdTr ++ o.soTr ∧
  (∀ s, s ∈ o.soTr → s.esAg = o.soHart) ∧
  List.Forall₂ lblReidxW o.soRow (o.soTr.map (fun s => s.esLb))

/-- THE WALK. -/
inductive segsRun (d0 : Efab) : List Segout → CycState → CycState → Prop where
  | segsDone (St : CycState) : cstOk d0 St → segsRun d0 [] St St
  | segsMore (o : Segout) (l : List Segout) (St St' St'' : CycState) :
      segStep d0 o St St' → segsRun d0 l St' St'' → segsRun d0 (o :: l) St St''

theorem segsRunOk (d0 : Efab) (l : List Segout) (St St' : CycState) :
    segsRun d0 l St St' → cstOk d0 St' := by
  intro h
  induction h with
  | segsDone _ hs => exact hs
  | segsMore _ _ _ _ _ _ _ ih => exact ih

theorem segsRunStart (d0 : Efab) (l : List Segout) (St St' : CycState) :
    segsRun d0 l St St' → cstOk d0 St := by
  intro h
  cases h with
  | segsDone _ hs => exact hs
  | segsMore _ _ _ _ _ hst _ => exact hst.1

theorem segsRunPrefix (d0 : Efab) (l : List Segout) (St St' : CycState) :
    segsRun d0 l St St' → ∃ ext, St'.cstC.cdTr = St.cstC.cdTr ++ ext := by
  intro h
  induction h with
  | segsDone _ _ => exact ⟨[], by rw [List.append_nil]⟩
  | segsMore o _ _ _ _ hst _ ih =>
    obtain ⟨ext, hext⟩ := ih
    obtain ⟨_, _, _, htr, _⟩ := hst
    exact ⟨o.soTr ++ ext, by rw [hext, htr, List.append_assoc]⟩

/-- THE POSITION FACT: every segment's appended steps sit at their recorded offset in the FINAL
candidate — later segments only append. -/
theorem segsRunStable (d0 : Efab) (l : List Segout) (St St' : CycState) :
    segsRun d0 l St St' →
    ∀ o, o ∈ l → ∀ k s, o.soTr[k]? = some s →
      St'.cstC.cdTr[o.soOff + k]? = some s := by
  intro h
  induction h with
  | segsDone _ _ => intro o ho; exact absurd ho List.not_mem_nil
  | segsMore o l S1 S2 S3 hst hrun ih =>
    intro o' ho' k s hk
    rcases List.mem_cons.1 ho' with heq | ho'
    · rw [heq] at hk ⊢
      obtain ⟨_, _, hoff, htr, _, _⟩ := hst
      obtain ⟨ext, hext⟩ := segsRunPrefix d0 l S2 S3 hrun
      have hk' := lookup_lt_Some hk
      have hlt : o.soOff + k < S2.cstC.cdTr.length := by
        rw [htr, List.length_append, hoff]
        unfold cdEnd
        omega
      rw [hext, List.getElem?_append_left hlt, htr,
        List.getElem?_append_right (by rw [hoff]; unfold cdEnd; omega), hoff]
      unfold cdEnd
      rw [show S1.cstC.cdTr.length + k - S1.cstC.cdTr.length = k by omega]
      exact hk
    · exact ih o' ho' k s hk

/-- … and every segment of the walk really was one `segStep`. -/
theorem segsRunElem (d0 : Efab) (l : List Segout) (St St' : CycState) :
    segsRun d0 l St St' → ∀ o, o ∈ l → ∃ S1 S2, segStep d0 o S1 S2 := by
  intro h
  induction h with
  | segsDone _ _ => intro o ho; exact absurd ho List.not_mem_nil
  | segsMore o l S1 S2 _ hst _ ih =>
    intro o' ho'
    rcases List.mem_cons.1 ho' with heq | ho'
    · rw [heq]; exact ⟨S1, S2, hst⟩
    · exact ih o' ho'

/-! ## 4.3 THE INTERFACE IS INHABITED BY `certSegment''` -/

theorem segStepOfSegment (x : Nat) (cpu : CPU) (d0 : Efab)
    (Tf : Nat → List Nat) (Q : Nat → Lbl → Prop)
    (Ctx : Nat → Cand → Prop) (Cls : Cand → Lbl → Prop)
    (Nd : Nat → SailM Unit → Prop)
    (Hmono : ∀ k, Tf k ⊆ Tf (k + 1))
    (Hpres : ∀ (k : Nat) (c0 : Cand) (lb lb' : Lbl),
      Ctx k c0 → srvwmoConsistent c0 → Q k lb → lblReidxW lb lb' →
      mstepOk (candLastSt c0) x lb' → Cls c0 lb' →
      Ctx (k + 1) (candSnoc c0 ⟨x, lb'⟩))
    (Hrdsp : ∀ (k : Nat) (lb : Lbl) (ws : Wstate) (l1 l2 : Wlabel) (rds : List Nat)
      (wrs : List Register) (m : SailM Unit) (rs : RegFile) (fn : Ofence) (ib : Ibch)
      (m' : SailM Unit) (rs' : RegFile) (fn' : Ofence) (ib' : Ibch),
      Q k lb → Nd k m →
      cblkp cpu d0 ws lb l1 l2 rds wrs m rs fn ib m' rs' fn' ib' →
      rdsOk (fun n => n ∉ Tf k) rds)
    (HNdadm : ∀ (k : Nat) (m m' : SailM Unit) (rs rs' : RegFile) (fn fn' : Ofence)
      (ib ib' : Ibch) (ls : List Wlabel) (rds : List Nat) (wrs : List Register) (ann : Bool),
      Nd k m → (∀ l0, l0 ∈ ls → lbAdmin true l0) →
      phrun cpu ls rds wrs ann m rs fn ib d0 m' rs' fn' ib' d0 → Nd k m')
    (HNdblk : ∀ (k : Nat) (m m' : SailM Unit) (ws : Wstate) (lb : Lbl) (l : Wlabel)
      (rds : List Nat) (wrs : List Register) (rs rs' : RegFile) (fn fn' : Ofence)
      (ib ib' : Ibch),
      Nd k m → Q k lb →
      cblk cpu d0 ws lb l rds wrs m rs fn ib m' rs' fn' ib' → Nd (k + 1) m')
    (HNdblkp : ∀ (k : Nat) (m m' : SailM Unit) (ws : Wstate) (lb : Lbl) (l1 l2 : Wlabel)
      (rds : List Nat) (wrs : List Register) (rs rs' : RegFile) (fn fn' : Ofence)
      (ib ib' : Ibch),
      Nd k m → Q k lb →
      cblkp cpu d0 ws lb l1 l2 rds wrs m rs fn ib m' rs' fn' ib' → Nd (k + 1) m')
    (Hpol'' : ∀ (k : Nat) (c0 : Cand) (ws : Wstate) (lb : Lbl) (l : Wlabel) (rds : List Nat)
      (wrs : List Register) (m : SailM Unit) (rs1 rs2 : RegFile) (fn : Ofence) (ib : Ibch)
      (m' : SailM Unit) (rs1' : RegFile) (fn' : Ofence) (ib' : Ibch),
      srvwmoConsistent c0 → Ctx k c0 → Q k lb →
      ((candLastSt c0).msWs x).wRelp = ws.wRelp →
      dregAgree (fun n => n ∉ Tf k) rs1 rs2 →
      Nd k m →
      WeakRvwmoCert2.cblkPin c0.cdImg cpu d0 ws lb l rds wrs m rs1 fn ib m' rs1' fn' ib' →
      ∃ (lb' : Lbl) (l' : Wlabel) (rds' : List Nat) (wrs' : List Register) (rs2' : RegFile)
        (m2' : SailM Unit) (fn2' : Ofence) (ib2' : Ibch),
        WeakRvwmoCert2.cblkPin c0.cdImg cpu d0 ws lb' l' rds' wrs' m rs2 fn ib m2' rs2' fn2' ib2' ∧
        mstepOk (candLastSt c0) x lb' ∧
        lblReidxW lb lb' ∧
        Cls c0 lb' ∧
        csync (Tf (k + 1)) m' rs1' fn' ib' m2' rs2' fn2' ib2' ∧
        (lbIsW lb = true → clockstep (Tf (k + 1)) m' rs1' fn' ib' m2' rs2' fn2' ib2'))
    (Hpolp : cpolpr x cpu d0 Tf Nd Ctx Cls Q)
    (k0 : Nat) (ws0 : Wstate) (rowseg : List Lbl) (es : List Eitem)
    (pfin : Pexv6) (m0 : SailM Unit) (rs10 : RegFile) (fn0 : Ofence)
    (ib0 : Ibch) (St : CycState) (m20 : SailM Unit) (rs20 : RegFile)
    (fn20 : Ofence) (ib20 : Ibch) :
    hemit (fun _ => d0) k0 ws0 rowseg (.PHart cpu m0 rs10 fn0 ib0) es pfin →
    (∀ kd ba bs, LDev kd ba bs ∉ es.map Prod.fst) →
    WeakRvwmoCert2.esPin St.cstC.cdImg es →
    (∀ i lb, rowseg[i]? = some lb → Q (k0 + i) lb) →
    cstOk d0 St →
    Ctx k0 St.cstC →
    (St.cstPst (cdEnd St.cstC))[x]? = some (.PHart cpu m20 rs20 fn20 ib20) →
    Nd k0 m0 →
    csync (Tf k0) m0 rs10 fn0 ib0 m20 rs20 fn20 ib20 →
    ((candLastSt St.cstC).msWs x).wRelp = ws0.wRelp →
    ∃ (St' : CycState) (tradd : List Estep),
      segStep d0 ⟨x, rowseg, cdEnd St.cstC, tradd⟩ St St' ∧
      Ctx (k0 + rowseg.length) St'.cstC ∧
      St'.cstC.cdImg = St.cstC.cdImg ∧
      St'.cstPst 0 = St.cstPst 0 ∧
      St'.cstDv 0 = St.cstDv 0 ∧
      (∃ (m1 : SailM Unit) (rs11 : RegFile) (fn1 : Ofence) (ib1 : Ibch)
         (m21 : SailM Unit) (rs21 : RegFile) (fn21 : Ofence) (ib21 : Ibch),
         pfin = .PHart cpu m1 rs11 fn1 ib1 ∧
         (St'.cstPst (cdEnd St'.cstC))[x]? = some (.PHart cpu m21 rs21 fn21 ib21) ∧
         csync (Tf (k0 + rowseg.length)) m1 rs11 fn1 ib1 m21 rs21 fn21 ib21 ∧
         (segLocked rowseg (clockstep (Tf k0) m0 rs10 fn0 ib0 m20 rs20 fn20 ib20) →
           clockstep (Tf (k0 + rowseg.length)) m1 rs11 fn1 ib1 m21 rs21 fn21 ib21) ∧
         Nd (k0 + rowseg.length) m1) ∧
      ((candLastSt St'.cstC).msWs x).wRelp = (rowWsAux k0 ws0 rowseg).wRelp ∧
      (∀ y, y ≠ x → (St'.cstPst (cdEnd St'.cstC))[y]? = (St.cstPst (cdEnd St.cstC))[y]?) ∧
      (∀ y, y ≠ x → ((candLastSt St'.cstC).msWs y).wRelp
        = ((candLastSt St.cstC).msWs y).wRelp) := by
  intro hem hdev hes hQ hS hctx hp hnd hsync hrelp
  obtain ⟨hc, hpo, hdv⟩ := hS
  obtain ⟨c', pst', dv', tradd, m1, rs11, fn1, ib1, m21, rs21, fn21, ib21, htr, hagf, hf2, hc',
    hctx', hpo', hp', hdv', hfin, hsyncf, hlockf, hrelpf, himg, hpst0, hdv0, hfr, hfrp, hndf⟩ :=
    certSegment'' x cpu d0 Tf Hmono Q Ctx Cls Hpres Nd Hrdsp HNdadm HNdblk HNdblkp Hpol'' Hpolp
      k0 ws0 rowseg _ es pfin hem hdev hQ m0 rs10 fn0 ib0 rfl hnd St.cstC St.cstPst St.cstDv
      m20 rs20 fn20 ib20 hc hctx hes hpo hp hdv hsync hrelp
  have hpo'' : execProgOk' (pstepPin c'.cdImg pstepEv) pclsEv pst' dv' (candExec c') := by
    rw [himg]; exact hpo'
  exact ⟨⟨c', pst', dv'⟩, tradd, ⟨⟨hc, hpo, hdv⟩, ⟨hc', hpo'', hdv'⟩, rfl, htr, hagf, hf2⟩, hctx',
    himg, hpst0, hdv0, ⟨m1, rs11, fn1, ib1, m21, rs21, fn21, ib21, hfin, hp', hsyncf, hlockf,
    hndf⟩, hrelpf, hfr, hfrp⟩

/-! # 5. THE CYCLE'S GEOMETRY, THE THEOREM, AND NON-VACUITY -/

/-! ## 5.1 The cycle, as data -/

structure Cyseg where
  cyHart : Nat
  cyEntry : Geid
  cyExit : Geid

def cysegOk (o : Cyseg) : Prop :=
  o.cyEntry.1 = o.cyHart ∧ o.cyExit.1 = o.cyHart ∧ o.cyEntry.2 ≤ o.cyExit.2

def cyLink (G : Gexec) (o1 o2 : Cyseg) : Prop :=
  o1.cyHart ≠ o2.cyHart ∧ racy G o1.cyExit o2.cyEntry

def cycleOk (G : Gexec) (l : List Cyseg) : Prop :=
  l ≠ [] ∧ (∀ o, o ∈ l → cysegOk o) ∧
  (∀ j o1 o2, l[j]? = some o1 → l[j + 1]? = some o2 → cyLink G o1 o2) ∧
  (∀ o1 o2, l[l.length - 1]? = some o1 → l[0]? = some o2 → cyLink G o1 o2)

/-- THE FIRST NON-VACUITY OBLIGATION: a ONE-segment "cycle" cannot exist. -/
theorem cycleTwoSegments (G : Gexec) (l : List Cyseg) : cycleOk G l → 2 ≤ l.length := by
  rintro ⟨hne, _, _, hwrap⟩
  cases l with
  | nil => exact absurd rfl hne
  | cons o l =>
    cases l with
    | nil => exact absurd rfl (hwrap o o rfl rfl).1
    | cons o2 l => simp

/-! ## 5.2 THE BACKWARD STEP, and why its entry is a plain load -/

def cyBackward (G : Gexec) (o : Cyseg) : Prop := gmoLt G o.cyExit o.cyEntry

theorem cyBackwardNotAq (G : Gexec) (o : Cyseg) :
    gppoGmo G → WeakRvwmoGraph.gpo G o.cyEntry o.cyExit →
    gmem G o.cyExit →
    glblIs G o.cyEntry lbIsR →
    cyBackward G o →
    ¬ glblIs G o.cyEntry lbAq :=
  fun hppo hpo hmem hr hb haq => witnessNotAq G o.cyEntry o.cyExit hppo hpo hmem hr haq hb

/-! ## 5.3 `certCycle` -/

theorem certCycle (d0 : Efab) (l : List Segout) (S0 Sf : CycState) :
    segsRun d0 l S0 Sf →
    -- (a) a real promise-free run at the quiet fabric
    srvwmoConsistent Sf.cstC ∧
    execProgOk' (pstepPin Sf.cstC.cdImg pstepEv) pclsEv Sf.cstPst Sf.cstDv (candExec Sf.cstC) ∧
    Sf.cstDv (cdEnd Sf.cstC) = d0 ∧
    -- (b) every segment's steps at a known offset
    (∀ o, o ∈ l → ∀ k s, o.soTr[k]? = some s → Sf.cstC.cdTr[o.soOff + k]? = some s) ∧
    -- (c) every exit write, with G's label, at a known position
    (∀ o, o ∈ l → ∀ j rl base vs kc,
      o.soRow[j]? = some (.LStore rl base vs kc) →
      Sf.cstC.cdTr[o.soOff + j]? = some ⟨o.soHart, .LStore rl base vs kc⟩) ∧
    -- (d) every appended step is the certifying hart's, and the row correspondence survives
    (∀ o, o ∈ l → (∀ s, s ∈ o.soTr → s.esAg = o.soHart) ∧
      List.Forall₂ lblReidxW o.soRow (o.soTr.map (fun s => s.esLb))) := by
  intro hrun
  obtain ⟨hc, hpo, hdv⟩ := segsRunOk d0 l S0 Sf hrun
  have hseg : ∀ o, o ∈ l → (∀ s, s ∈ o.soTr → s.esAg = o.soHart) ∧
      List.Forall₂ lblReidxW o.soRow (o.soTr.map (fun s => s.esLb)) := by
    intro o ho
    obtain ⟨S1, S2, _, _, _, _, hag, hf2⟩ := segsRunElem d0 l S0 Sf hrun o ho
    exact ⟨hag, hf2⟩
  refine ⟨hc, hpo, hdv, segsRunStable d0 l S0 Sf hrun, ?_, hseg⟩
  intro o ho j rl base vs kc hj
  obtain ⟨hag, hf2⟩ := hseg o ho
  exact segsRunStable d0 l S0 Sf hrun o ho j _
    (segExitWrite o.soHart o.soRow o.soTr j rl base vs kc hf2 hag hj)

/-- The entry read's position. -/
theorem certCyclePos (d0 : Efab) (l : List Segout) (S0 Sf : CycState) (o : Segout) (j : Nat)
    (lb : Lbl) :
    segsRun d0 l S0 Sf → o ∈ l →
    o.soTr[j]? = some ⟨o.soHart, lb⟩ →
    Sf.cstC.cdTr[o.soOff + j]? = some ⟨o.soHart, lb⟩ :=
  fun hrun ho hj => segsRunStable d0 l S0 Sf hrun o ho j _ hj

/-! ## 5.4 THE EXIT WRITE'S MESSAGE, AT A KNOWN LOG POSITION -/

theorem exitMsgInLog (c : Cand) (p : Nat) (x : Nat) (rl : Bool) (base : Int)
    (vs : List (BitVec 8)) (kc : WmClass) :
    c.cdTr[p]? = some ⟨x, .LStore rl base vs kc⟩ →
    ∀ q, p + 1 ≤ q →
      (cdLog c q)[(cdLog c p).length]? = some ⟨base, vs, some x, kc⟩ := by
  intro hp q hq
  have hs : cdLog c (p + 1) = cdLog c p ++ [⟨base, vs, some x, kc⟩] := by
    rw [cdLogS c p _ hp]
    rfl
  obtain ⟨ext, hext⟩ := cdLogSplit c (p + 1) q hq
  rw [hext, hs, List.append_assoc, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
  rfl

theorem certCycleExitMsg (d0 : Efab) (l : List Segout) (S0 Sf : CycState) (o : Segout)
    (j : Nat) (rl : Bool) (base : Int) (vs : List (BitVec 8)) (kc : WmClass) :
    segsRun d0 l S0 Sf → o ∈ l →
    o.soRow[j]? = some (.LStore rl base vs kc) →
    (cdLogEnd Sf.cstC)[(cdLog Sf.cstC (o.soOff + j)).length]?
      = some ⟨base, vs, some o.soHart, kc⟩ := by
  intro hrun ho hj
  obtain ⟨_, _, _, _, hex, _⟩ := certCycle d0 l S0 Sf hrun
  have hp := hex o ho j rl base vs kc hj
  unfold cdLogEnd cdEnd
  have := lookup_lt_Some hp
  exact exitMsgInLog Sf.cstC (o.soOff + j) o.soHart rl base vs kc hp _ (by omega)

/-! ## 5.5 APPENDING ONE MORE SEGMENT -/

theorem segsRunSnoc (d0 : Efab) (l : List Segout) (o : Segout) (St St' St'' : CycState) :
    segsRun d0 l St St' → segStep d0 o St' St'' → segsRun d0 (l ++ [o]) St St'' := by
  intro h
  induction h with
  | segsDone S1 _ =>
    intro hst
    exact .segsMore o [] S1 St'' St'' hst (.segsDone _ hst.2.1)
  | segsMore o1 l1 S1 S2 _ hst1 _ ih =>
    intro hst
    exact .segsMore o1 (l1 ++ [o]) S1 S2 St'' hst1 (ih hst)

/-! ## 5.6 NON-VACUITY: one REAL segment in the walk (Rocq `Section nonvacuity4`) -/

noncomputable def nv4S0 (cpu : CPU) (rs : RegFile) (ib : Ibch) (d0 : Efab) : CycState :=
  ⟨smC (fun _ => none), smPst cpu rs ib, smDv d0⟩

theorem nv4S0Ok (cpu : CPU) (rs : RegFile) (ib : Ibch) (d0 : Efab) :
    cstOk d0 (nv4S0 cpu rs ib d0) :=
  ⟨smConsistent _, smProg0 _ cpu rs ib d0, rfl⟩

theorem segsRunWitness (cpu : CPU) (rs : RegFile) (ib : Ibch) (d0 : Efab) :
    ∃ (Sf : CycState) (tradd : List Estep),
      segsRun d0 [⟨0, evRow, 0, tradd⟩] (nv4S0 cpu rs ib d0) Sf ∧
      Sf.cstC.cdTr[0]? = some ⟨0, .LStore false (paZ evFlag) (WeakInterpProj.wbytes 4 lockOne)
        .WCplain⟩ := by
  have hrds0 : ∀ rds : List Nat, rdsOk (fun n => n ∉ ([] : List Nat)) rds :=
    fun _ _ _ => List.not_mem_nil
  have hpol : ∀ (k : Nat) (c0 : Cand) (ws : Wstate) (lb : Lbl) (l : Wlabel) (rds : List Nat)
      (wrs : List Register) (m : SailM Unit) (rs1 rs2 : RegFile) (fn : Ofence) (ib0 : Ibch)
      (m' : SailM Unit) (rs1' : RegFile) (fn' : Ofence) (ib' : Ibch),
      srvwmoConsistent c0 → True → lbStoreNe lb →
      ((candLastSt c0).msWs 0).wRelp = ws.wRelp →
      dregAgree (fun n => n ∉ ([] : List Nat)) rs1 rs2 →
      True →
      WeakRvwmoCert2.cblkPin c0.cdImg cpu d0 ws lb l rds wrs m rs1 fn ib0 m' rs1' fn' ib' →
      ∃ (lb' : Lbl) (l' : Wlabel) (rds' : List Nat) (wrs' : List Register) (rs2' : RegFile)
        (m2' : SailM Unit) (fn2' : Ofence) (ib2' : Ibch),
        WeakRvwmoCert2.cblkPin c0.cdImg cpu d0 ws lb' l' rds' wrs' m rs2 fn ib0 m2' rs2' fn2' ib2' ∧
        mstepOk (candLastSt c0) 0 lb' ∧
        lblReidxW lb lb' ∧
        True ∧
        csync [] m' rs1' fn' ib' m2' rs2' fn2' ib2' ∧
        (lbIsW lb = true → clockstep [] m' rs1' fn' ib' m2' rs2' fn2' ib2') := by
    intro k c0 ws lb l rds wrs m rs1 rs2 fn ib0 m' rs1' fn' ib' hc _ hlb hrelp hag _ hblk
    obtain ⟨lb', l', rds', wrs', rs2', h1, h2, h3, _, h5⟩ :=
      polStore' 0 cpu d0 c0 ws lb l rds wrs m rs1 rs2 fn ib0 m' rs1' fn' ib' hc hlb hrelp hag hblk
    exact ⟨lb', l', rds', wrs', rs2', m', fn', ib', h1, h2, h3, trivial,
      .inl ⟨rfl, rfl, rfl, h5⟩, fun _ => ⟨rfl, rfl, rfl, h5⟩⟩
  obtain ⟨Sf, tradd, hstep, -⟩ :=
    segStepOfSegment 0 cpu d0 (fun _ => []) (fun _ => lbStoreNe) (fun _ _ => True)
      (fun _ _ => True) (fun _ _ => True) (fun _ => List.Subset.refl _)
      (fun _ _ _ _ _ _ _ _ _ _ => trivial)
      (fun _ _ _ _ _ rds _ _ _ _ _ _ _ _ _ _ _ _ => hrds0 rds)
      (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => trivial)
      (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => trivial)
      (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => trivial)
      hpol
      (cpolprOfCpolp 0 cpu d0 [] (fun _ _ => True) (fun _ _ => True) (fun _ _ => True)
        (fun _ => lbStoreNe)
        (cpolpOfRmwfree 0 cpu d0 [] _ _ _ (fun _ lb hlb => lbStoreNeRmwfree lb hlb)))
      0 wsInit evRow _ _ evX2.2 rs none ib (nv4S0 cpu rs ib d0) evX2.2 rs none ib
      (nvHemit cpu rs ib d0) (evEmDevfree cpu rs ib) (WeakRvwmoCert2.nvPin cpu rs ib _)
      (fun _ lb hi => nvRowClass lb (List.mem_of_getElem? hi))
      (nv4S0Ok cpu rs ib d0) trivial rfl trivial
      (.inl ⟨rfl, rfl, rfl, dregAgreeRefl _ _⟩) (by rw [show (nv4S0 cpu rs ib d0).cstC =
        smC (fun _ => none) from rfl, smWs])
  refine ⟨Sf, tradd, .segsMore _ _ _ _ _ hstep (.segsDone _ hstep.2.1), ?_⟩
  obtain ⟨_, _, _, htr, hag, hf2⟩ := hstep
  rw [htr]
  show ([] ++ tradd)[0]? = _
  rw [List.nil_append]
  exact segExitWrite 0 evRow tradd 0 _ _ _ _ hf2 hag rfl

/-! ## 5.7 WHY THERE IS NO 2-HART CYCLE WITNESS YET — recorded -/

theorem cycleTwoHarts (G : Gexec) (l : List Cyseg) :
    cycleOk G l → ∃ o1 o2, o1 ∈ l ∧ o2 ∈ l ∧ o1.cyHart ≠ o2.cyHart := by
  intro hok
  have hlen := cycleTwoSegments G l hok
  obtain ⟨_, _, hcons, _⟩ := hok
  have h1 : l[0]? = some l[0] := List.getElem?_eq_getElem (by omega)
  have h2 : l[1]? = some l[1] := List.getElem?_eq_getElem (by omega)
  exact ⟨l[0], l[1], List.getElem_mem _, List.getElem_mem _, (hcons 0 _ _ h1 h2).1⟩

theorem nv4OneHart (cpu : CPU) (rs : RegFile) (ib : Ibch) (d0 : Efab) (k : Nat) :
    ((nv4S0 cpu rs ib d0).cstPst k).length = 1 := rfl

end Weak
