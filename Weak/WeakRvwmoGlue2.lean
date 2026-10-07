/-
Weak: **THE THREE RESIDUAL PREMISES OF `WeakRvwmoGlue`** (route B).

Rocq: `iris/WeakRvwmoGlue2.v` @ xxvzwolszwmp.

## The Rocq header, in substance

`WeakRvwmoGlue` §9 leaves four premises open: (G-1) the L2′ per-site claim (the project's
remaining CONTENT, untouched here), and three pieces of bookkeeping — (G-2) `cutSupply`,
(G-3) `certSupply`, (G-4) `bootTie`.  This leaf discharges (G-2) and (G-4) outright and reduces
(G-3) to a single named supply, then restates the glue's theorem with the premise list that
remains.

  §1  (G-4) THE IMAGE CLAUSE, discharged: `gdexecQconf` carries the boot tie itself, so
      `bootTie`'s third conjunct is free (`bootTieOfQconf`).
  §2  (G-2) `cutSupply`, discharged by the ZERO CUT (`zcut`), which is `cutOk` at every graph
      with an event.  The FINDING (Rocq §2.4, a comment): the write-closed causal past of the
      cycle cannot be shown `properCut` in general — the rf-closure of the entries' prefixes may
      climb above another hart's entry (po into a READ is not an `racyD` arm) — so the interface
      as landed is discharged by the zero cut, and a per-cycle seed is the residue.
  §3  (G-3) `certSupply`, reduced: the (P-1) bookkeeping (`ctracePrefixSnoc`, `cpolCtxSnoc`,
      `cpolHpres` — the `Ctx := cpolCtx G W x` instantiation), the `CycState → RunData`
      bridge, `certSupplyOfWalk` (a walk supply gives `certSupply` verbatim), and (O-A)
      `walkExitsGmoForced` (the gmo order of the walk's exits is forced by `ctpWix`).
  §4  THE THEOREM: `cycleKillOfL2''` and `t2linOfL2''`, with the premise list that remains
      (boot plumbing, `l2Claim`, `walkSupply`, the WP package).
  §5  NON-VACUITY at LB: the zero cut is `[0, 0]`, the hull at it is empty.

§6 (the `Print Assumptions` audit) and §7 (the ledger) are Rocq commands/comments.  A LEAF:
nothing imports this file.

## Deviations from Rocq

1. NAMES / VOCABULARY: camelCase (map below); `S n` ↦ `n + 1`; `replicate` ↦ `List.replicate`;
   `default d o` ↦ `o.getD d`; `EStep x l` ↦ `(⟨x, l⟩ : Estep)`; `cyc_state` fields
   `cst_c/cst_pst/cst_dv` ↦ `cstC/cstPst/cstDv`; `segout` ↦ `Segout` (`soRow`, `soOff`).
2. THE BOOT DEVICE STATE (WeakRvwmoGlue deviation 2): Rocq's `d0 = wgdev σ0` is
   `d0 = efInit σ0.wgdev` in `bootTieOfQconf`, `cycleKillOfL2'`, `cycleKillOfL2''`,
   `t2linOfL2''`.
3. THE WP PACKAGES (WeakRvwmoGlue deviation 3): explicit `hlc GF` with
   `[MachGpreS hlc GF] [WeakGpreS GF]`, and `hD : ∀ c, (D c).Nodup`.
4. O2 — THE FETCH-VIEW PREMISE (WeakRvwmoGlue deviation 4), CARRIED: `cycleKillOfL2'`,
   `cycleKillOfL2''` and `t2linOfL2''` take
   `∀ ρ, rtc epfRun (epInit gen, σ0) ρ → efetchItvOk ρ.1 ρ.2` (placed right after the WP
   package premises).  Nothing here proves the text unwritten, so it cannot be discharged.
5. O2 / D1 — THE FETCH-INERTNESS PREMISE `WeakRvwmoGlue.hullRunFetchInert` (WeakRvwmoGlue
   deviation 5) is DISCHARGED here, not carried: the three theorems of this file never call
   `WeakRvwmoGlue.cycleKillOfL2` (which needs it at every cut) but the Lean-only
   `WeakRvwmoGlue2.cycleKillZ`, the glue's own proof run at the ZERO CUT.  There the hull's rows
   are empty, so the realized candidate's trace has no step and `candFetchInert` is vacuous
   (`WeakRvwmoGlue2.hullRunZcut`).  Consequently `cycleKillOfL2'` keeps Rocq's `cutSupply`
   premise but no longer uses it (it is discharged anyway by `cutSupplyOfCycle`); its
   conclusion is Rocq's.
6. PROOFS: `ctracePrefixSnoc` follows `WeakRvwmoFloor.gtracePrefixSnoc`'s Lean script; the
   below-the-end / at-the-end transports are the Lean-only `WeakRvwmoGlue2.snocLt` /
   `WeakRvwmoGlue2.snocEnd`.  Statements are Rocq's.

**Rocq → Lean name map.**  `boot_tie_of_qconf` `bootTieOfQconf`, `cycle_kill_of_l2'`
`cycleKillOfL2'`, `zcut` `zcut`, `zcut_length` `zcutLength`, `gcut_zcut` `gcutZcut`,
`zcut_hull_ok` `zcutHullOk`, `zcut_wcut_closed` `zcutWcutClosed`, `zcut_proper` `zcutProper`,
`zcut_cut_ok` `zcutCutOk`, `zcut_hull_rows` `zcutHullRows`, `glbl_nrow` `glblNrow`,
`cycle_has_event` `cycleHasEvent`, `cut_supply_of_cycle` `cutSupplyOfCycle`, `cstep_cls`
`cstepCls`, `latest_read_lbl_congr` `latestReadLblCongr`, `latest_read_not_w`
`latestReadNotW`, `cd_pre_snoc_img` `cdPreSnocImg`, `cd_pre_snoc_log` `cdPreSnocLog`,
`ctrace_prefix_snoc` `ctracePrefixSnoc`, `gcnt_cand_snoc_self` `gcntCandSnocSelf`,
`cstep_pois_ok` `cstepPoisOk`, `gcnt_snoc_le` `gcntSnocLe`, `pois_ok_hart_ev` `poisOkHartEv`,
`pois_ok_hart_snoc` `poisOkHartSnoc`, `cpol_ctx_snoc` `cpolCtxSnoc`, `cpol_Hpres` `cpolHpres`,
`run_data_of_cyc` `runDataOfCyc`, `walk_supply` `walkSupply`, `cert_supply_of_walk`
`certSupplyOfWalk`, `walk_exits_gmo_forced` `walkExitsGmoForced`, `cycle_kill_of_l2''`
`cycleKillOfL2''`, `t2lin_of_l2''` `t2linOfL2''`, `lbgd_cut_ok` `lbgdCutOk`,
`lbgd_zcut_empty` `lbgdZcutEmpty`, `lbgd_cut_drops_everything` `lbgdCutDropsEverything`,
`lbgd_hull_empty` `lbgdHullEmpty`.
Lean-only (file-qualified): `WeakRvwmoGlue2.zcutGetD`, `WeakRvwmoGlue2.snocLt`,
`WeakRvwmoGlue2.snocEnd`, `WeakRvwmoGlue2.hullRunZcut`, `WeakRvwmoGlue2.cycleKillZ`.

**File-qualified Rocq names:** none (no name of this file is in `notes/weak-port-dupnames.json`).

**Dropped:** none (Rocq 36 declarations; Lean 41 = 36 + the 5 Lean-only).
-/
import Weak.WeakRvwmoGlue

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std

/-! # 1. (G-4) THE IMAGE CLAUSE -/

theorem bootTieOfQconf (boot : Nat → Pexv6) (d0 : Efab) (N : Nat) (σ0 : WGState) :
    (List.range' 0 N).map boot = epsInit σ0 →
    d0 = efInit σ0.wgdev →
    bootTie boot d0 (imgZ σ0.wgimg) N N σ0 :=
  fun h1 h2 => ⟨h1, h2, fun GD hq =>
    ⟨gdexecQconfImg _ _ _ _ _ hq, gdexecQconfNharts _ _ _ _ _ hq⟩⟩

/-! # 2. (G-2) `cutSupply` -/

/-! ## 2.1 The zero cut -/

def zcut (G : Gexec) : List Nat := List.replicate G.gxProg.length 0

theorem zcutLength (G : Gexec) : (zcut G).length = G.gxProg.length := List.length_replicate

/-- Lean-only: every hart's cut position is `0`. -/
theorem WeakRvwmoGlue2.zcutGetD (G : Gexec) (i : Nat) : ((zcut G)[i]?).getD 0 = 0 := by
  by_cases h : i < G.gxProg.length <;> simp [zcut, h]

theorem gcutZcut (G : Gexec) (e : Geid) : gcut (zcut G) e = false := by
  by_cases h : e.1 < G.gxProg.length <;> simp [gcut, zcut, h]

theorem zcutHullOk (G : Gexec) : hullOk G (zcut G) :=
  ⟨zcutLength G, fun _ _ _ _ _ hc => by rw [gcutZcut] at hc; cases hc⟩

theorem zcutWcutClosed (G : Gexec) : wcutClosed G (zcut G) :=
  fun _ _ _ _ hc => by rw [gcutZcut] at hc; cases hc

theorem zcutProper (G : Gexec) (i : Nat) :
    i < G.gxProg.length → 0 < nrow G i → properCut G (zcut G) :=
  fun _ hn => ⟨zcutHullOk G, i, by rw [WeakRvwmoGlue2.zcutGetD]; exact hn⟩

theorem zcutCutOk (G : Gexec) (i : Nat) :
    i < G.gxProg.length → 0 < nrow G i → cutOk G (zcut G) :=
  fun hi hn => ⟨zcutHullOk G, zcutWcutClosed G, zcutProper G i hi hn⟩

/-- The hull at the zero cut is the EMPTY program: every row is dropped. -/
theorem zcutHullRows (G : Gexec) (i : Nat) :
    ((gxHull G (zcut G)).gxProg[i]?).getD [] = [] := by
  rw [gxhRow, WeakRvwmoGlue2.zcutGetD]
  simp

/-! ## 2.2 A cycle names an event, hence a nonempty row -/

theorem glblNrow (G : Gexec) (e : Geid) (l : Lbl) :
    gxLbl G e = some l → e.1 < G.gxProg.length ∧ e.2 < nrow G e.1 := by
  unfold gxLbl nrow
  cases hp : G.gxProg[e.1]? with
  | none => intro h; simp at h
  | some p =>
    intro hl
    simp only [Option.bind_some] at hl
    exact ⟨lookup_lt_Some hp, by simpa using lookup_lt_Some hl⟩

theorem cycleHasEvent (GD : Gdexec) (z : Geid) (ss : List Seg) :
    rvwmoMinusConsistent GD.gdG →
    ss ≠ [] → rawChain GD z z ss →
    ∃ i, i < GD.gdG.gxProg.length ∧ 0 < nrow GD.gdG i := by
  intro hcons hne hch
  cases ss with
  | nil => exact absurd rfl hne
  | cons s ss =>
    obtain ⟨hx, -, -⟩ := hch
    obtain ⟨-, hin, -⟩ := gcrossGmo GD.gdG z s.sgEntry hcons hx
    obtain ⟨l, hl, -⟩ := (hcons.1.2.1 s.sgEntry).1 hin
    obtain ⟨h1, h2⟩ := glblNrow GD.gdG s.sgEntry l hl
    exact ⟨s.sgEntry.1, h1, by omega⟩

/-! ## 2.3 (G-2), DISCHARGED -/

theorem cutSupplyOfCycle (boot : Nat → Pexv6) (d0 : Efab) (im : Image) (nh : Nat) :
    cutSupply boot d0 im nh := by
  intro GD z ss hcons _ hne hch
  obtain ⟨i, hi, hn⟩ := cycleHasEvent GD z ss hcons.1 hne hch
  exact ⟨zcut GD.gdG, zcutCutOk GD.gdG i hi hn⟩

/-! # 3. (G-3) `certSupply` -/

/-! ## 3.1 (P-1): `CtracePrefix` extends by one certified step -/

/-- THE STEP CLASSIFICATION: `CtracePrefix`'s `ctpStep` disjunction at the appended position. -/
def cstepCls (G : Gexec) (W : Geid → Prop) (x : Nat) (c : Cand) (l : Lbl) : Prop :=
  (¬ W (x, gcnt x c.cdTr) ∧ gxLbl G (x, gcnt x c.cdTr) = some l) ∨
  (W (x, gcnt x c.cdTr) ∧
   ∃ (base : Int) (n : Nat) (ts0 : List Nat) (vs0 : List (BitVec 8)),
     gxLbl G (x, gcnt x c.cdTr) = some (Lbl.LLoad false base ts0 vs0) ∧
     ts0.length = n ∧ l = latestReadLbl c false base n) ∨
  -- THE POISONED ARM (the per-hart taint migration)
  ((∃ lb0 : Lbl, gxLbl G (x, gcnt x c.cdTr) = some lb0 ∧ lbIsW lb0 = false) ∧
   cpoisLbl c l ∧
   gxLbl G (x, gcnt x c.cdTr) ≠ some l ∧
   ¬ (∃ (base : Int) (n : Nat) (ts0 : List Nat) (vs0 : List (BitVec 8)),
        gxLbl G (x, gcnt x c.cdTr) = some (Lbl.LLoad false base ts0 vs0) ∧
        ts0.length = n ∧ l = latestReadLbl c false base n))

theorem latestReadLblCongr (c1 c2 : Cand) (aq : Bool) (base : Int) (n : Nat) :
    c1.cdImg = c2.cdImg → cdLogEnd c1 = cdLogEnd c2 →
    latestReadLbl c1 aq base n = latestReadLbl c2 aq base n := by
  intro h1 h2
  unfold latestReadLbl lrdTs lrdVs
  rw [h1, h2]

theorem latestReadNotW (c : Cand) (aq : Bool) (base : Int) (n : Nat) :
    lbIsW (latestReadLbl c aq base n) = false := rfl

theorem cdPreSnocImg (c : Cand) (s : Estep) :
    (cdPre (candSnoc c s) c.cdTr.length).cdImg = c.cdImg := rfl

theorem cdPreSnocLog (c : Cand) (s : Estep) :
    cdLogEnd (cdPre (candSnoc c s) c.cdTr.length) = cdLogEnd c := by
  rw [cdPreLog]
  exact candSnocLog c s c.cdTr.length (Nat.le_refl _)

/-- Lean-only: the snoc's transports below the end. -/
theorem WeakRvwmoGlue2.snocLt (c : Cand) (t : Estep) (ev : Nat → Geid) (e : Geid) (p : Nat)
    (s : Estep) :
    (candSnoc c t).cdTr[p]? = some s → p < c.cdTr.length →
    c.cdTr[p]? = some s ∧ evSnoc c ev e p = ev p ∧
    (candSnoc c t).cdTr.take p = c.cdTr.take p ∧
    cdLog (candSnoc c t) p = cdLog c p ∧
    cdPre (candSnoc c t) p = cdPre c p := by
  intro hs hp
  rw [candSnocTrLt c _ p hp] at hs
  have htk : (candSnoc c t).cdTr.take p = c.cdTr.take p := take_app_le (Nat.le_of_lt hp)
  refine ⟨hs, evSnocLt c ev _ p hp, htk, candSnocLog c _ p (Nat.le_of_lt hp), ?_⟩
  show (⟨c.cdImg, (candSnoc c t).cdTr.take p⟩ : Cand) = ⟨c.cdImg, c.cdTr.take p⟩
  rw [htk]

/-- Lean-only: the snoc's only position at or beyond the end is the appended step. -/
theorem WeakRvwmoGlue2.snocEnd (c : Cand) (t : Estep) (p : Nat) (s : Estep) :
    (candSnoc c t).cdTr[p]? = some s → ¬ p < c.cdTr.length → p = c.cdTr.length ∧ s = t := by
  intro hs hp
  have hb := lookup_lt_Some hs
  simp only [candSnoc, List.length_append, List.length_singleton] at hb
  have hpe : p = c.cdTr.length := by omega
  subst hpe
  have he := candSnocTrEnd c t
  unfold cdEnd at he
  rw [he] at hs
  exact ⟨rfl, (Option.some.inj hs).symm⟩

theorem ctracePrefixSnoc (G : Gexec) (c : Cand) (ev : Nat → Geid) (W : Geid → Prop) (x : Nat)
    (l : Lbl) :
    gwf G →
    CtracePrefix G c ev W →
    cstepCls G W x c l →
    (lbIsW l = true → gwix G (x, gcnt x c.cdTr) = (cdLogEnd c).length + 1) →
    CtracePrefix G (candSnoc c ⟨x, l⟩) (evSnoc c ev (x, gcnt x c.cdTr)) W := by
  intro hwf hgt hcls hix
  have hte : c.cdTr.take c.cdTr.length = c.cdTr := take_ge (Nat.le_refl _)
  -- a WITNESS and a POISONED label are both loads, so an appended WRITE carries G's own label
  have hlblW : lbIsW l = true →
      ¬ W (x, gcnt x c.cdTr) ∧ gxLbl G (x, gcnt x c.cdTr) = some l := by
    intro hw
    rcases hcls with h | ⟨-, _, _, _, _, -, -, hleq⟩ | ⟨-, hpl, -⟩
    · exact h
    · rw [hleq, latestReadNotW] at hw; cases hw
    · rw [cpoisLblNotw _ _ hpl] at hw; cases hw
  -- the congruence of the latest-source read across the snoc's own prefix
  have hcg : ∀ base n, latestReadLbl c false base n =
      latestReadLbl (cdPre (candSnoc c ⟨x, l⟩) c.cdTr.length) false base n :=
    fun base n => latestReadLblCongr _ _ _ _ _ (cdPreSnocImg c _).symm (cdPreSnocLog c _).symm
  obtain ⟨himg, hag, hpos, hstep, hwix, hlog⟩ := hgt
  refine ⟨himg, ?_, ?_, ?_, ?_, ?_⟩
  · intro p s hs
    by_cases hp : p < c.cdTr.length
    · obtain ⟨hs', hev, -, -, -⟩ := WeakRvwmoGlue2.snocLt c _ ev (x, gcnt x c.cdTr) p s hs hp
      rw [hev]; exact hag p s hs'
    · obtain ⟨rfl, rfl⟩ := WeakRvwmoGlue2.snocEnd c _ p s hs hp
      rw [evSnocEnd]
  · intro p s hs
    by_cases hp : p < c.cdTr.length
    · obtain ⟨hs', hev, htk, -, -⟩ := WeakRvwmoGlue2.snocLt c _ ev (x, gcnt x c.cdTr) p s hs hp
      rw [hev, htk]; exact hpos p s hs'
    · obtain ⟨rfl, rfl⟩ := WeakRvwmoGlue2.snocEnd c _ p s hs hp
      rw [evSnocEnd]
      show gcnt x c.cdTr = gcnt x ((c.cdTr ++ [(⟨x, l⟩ : Estep)]).take c.cdTr.length)
      rw [take_app_le (Nat.le_refl _), hte]
  · intro p s hs
    by_cases hp : p < c.cdTr.length
    · obtain ⟨hs', hev, -, -, hpr⟩ := WeakRvwmoGlue2.snocLt c _ ev (x, gcnt x c.cdTr) p s hs hp
      rcases hstep p s hs' with ⟨hnW, hl⟩ | ⟨hW, hw⟩ | hpo
      · left; rw [hev]; exact ⟨hnW, hl⟩
      · right; left
        rw [hev]
        refine ⟨hW, ?_⟩
        unfold cwitStep at hw ⊢
        rw [hev, hpr]
        exact hw
      · right; right
        unfold cpoisStep cwitStep at hpo ⊢
        rw [hev, hpr]
        exact hpo
    · obtain ⟨rfl, rfl⟩ := WeakRvwmoGlue2.snocEnd c _ p s hs hp
      rcases hcls with ⟨hnW, hl⟩ | ⟨hW, base, n, ts0, vs0, hl, hn, hleq⟩ |
          ⟨hg0, ⟨base, n, hleq⟩, hne, hnw⟩
      · left; rw [evSnocEnd]; exact ⟨hnW, hl⟩
      · right; left
        rw [evSnocEnd]
        refine ⟨hW, ?_⟩
        unfold cwitStep
        rw [evSnocEnd]
        exact ⟨base, n, ts0, vs0, hl, hn, hleq.trans (hcg base n)⟩
      · right; right
        unfold cpoisStep cwitStep
        rw [evSnocEnd]
        refine ⟨hg0, ⟨base, n, hleq.trans (hcg base n)⟩, hne, ?_⟩
        rintro ⟨b1, n1, t1, v1, hl1, hn1, hlb1⟩
        exact hnw ⟨b1, n1, t1, v1, hl1, hn1, hlb1.trans (hcg b1 n1).symm⟩
  · intro p s hs hw
    by_cases hp : p < c.cdTr.length
    · obtain ⟨hs', hev, -, hlg, -⟩ := WeakRvwmoGlue2.snocLt c _ ev (x, gcnt x c.cdTr) p s hs hp
      rw [hev, hlg]; exact hwix p s hs' hw
    · obtain ⟨rfl, rfl⟩ := WeakRvwmoGlue2.snocEnd c _ p s hs hp
      rw [evSnocEnd, candSnocLog c ⟨x, l⟩ c.cdTr.length (Nat.le_refl _)]
      exact hix hw
  · -- the log clause
    intro s hs hle
    have hlg : cdLog (candSnoc c ⟨x, l⟩) (candSnoc c ⟨x, l⟩).cdTr.length
        = cdLogEnd c ++ esMsg ⟨x, l⟩ := cdLogEndSnoc c ⟨x, l⟩
    rw [hlg] at hle ⊢
    by_cases hin : s ≤ (cdLogEnd c).length
    · obtain ⟨w, hw, heq⟩ := hlog s hs hin
      refine ⟨w, hw, ?_⟩
      have hsl : s - 1 < (cdLogEnd c).length := by omega
      rw [lookup_app_l hsl]
      exact heq
    · rw [List.length_append] at hle
      have hwl : lbIsW l = true := by
        cases hwr : lbWr l with
        | some p => exact lbWrIsW l p hwr
        | none =>
          exfalso
          simp only [esMsg, hwr, List.length_nil, Nat.add_zero] at hle
          omega
      have hl : gxLbl G (x, gcnt x c.cdTr) = some l := (hlblW hwl).2
      obtain ⟨base, vs, hwr⟩ := lbIsWWr l hwl
      have hmsg : esMsg ⟨x, l⟩ = [⟨base, vs, some x, lbCls l⟩] := by simp only [esMsg, hwr]
      rw [hmsg] at hle ⊢
      simp only [List.length_singleton] at hle
      have hs' : s = (cdLogEnd c).length + 1 := by omega
      subst hs'
      have hgw : (x, gcnt x c.cdTr) ∈ gwrites G :=
        gisWGwrites G _ hwf (by rw [hl]; rfl) (by simp only [gisW, hl]; exact hwl)
      refine ⟨(x, gcnt x c.cdTr), ?_, ?_⟩
      · rw [← hix hwl]; exact gwriteAtGwix G _ hgw
      · rw [Nat.add_sub_cancel, lookup_app_r (Nat.le_refl _), Nat.sub_self]
        simp [gwmsg, hl, hwr]

/-- The appended step is the certifying hart's, so its own position advances by one. -/
theorem gcntCandSnocSelf (c : Cand) (x : Nat) (l : Lbl) :
    gcnt x (candSnoc c ⟨x, l⟩).cdTr = gcnt x c.cdTr + 1 := by
  simp [gcnt, candSnoc, List.filter_append]

/-! ## 3.1a `cpolCtx` is preserved -/

/-- THE POISONED STEP'S OWN OBLIGATION, at the label the policy appends. -/
def cstepPoisOk (G : Gexec) (x : Nat) (c : Cand) (l : Lbl) : Prop :=
  cpoisLbl c l →
  gxLbl G (x, gcnt x c.cdTr) ≠ some l →
  ¬ (∃ (base : Int) (n : Nat) (ts0 : List Nat) (vs0 : List (BitVec 8)),
       gxLbl G (x, gcnt x c.cdTr) = some (Lbl.LLoad false base ts0 vs0) ∧
       ts0.length = n ∧ l = latestReadLbl c false base n) →
  ∀ k, gcnt x c.cdTr + 1 ≤ k →
    (∀ a, gaccesses G (x, k) a → ¬ lblTouches l a) ∧
    (fhook G (x, k) (gcnt x c.cdTr + 1) true → gvisUb G (x, k) (cdLogEnd c).length)

theorem gcntSnocLe (c : Cand) (x y : Nat) (l : Lbl) :
    gcnt y c.cdTr ≤ gcnt y (candSnoc c ⟨x, l⟩).cdTr := by
  unfold gcnt
  rw [candSnocTr, List.filter_append, List.length_append]
  omega

/-- THE INVARIANT TRANSPORTS ALONG THE INDEXING. -/
theorem poisOkHartEv (G : Gexec) (c : Cand) (ev1 ev2 : Nat → Geid) (W : Geid → Prop)
    (x : Nat) :
    CtracePrefix G c ev1 W → CtracePrefix G c ev2 W →
    poisOkHart G c ev1 x → poisOkHart G c ev2 x := by
  intro h1 h2 h p s hs hpo hag k hk
  have hev : ev2 p = ev1 p := by
    rw [ctpEvEq G c ev2 W p s h2 hs, ctpEvEq G c ev1 W p s h1 hs]
  rw [hev]
  rw [hev] at hag
  refine h p s hs ?_ hag k hk
  unfold cpoisStep cwitStep at hpo ⊢
  rw [hev] at hpo
  exact hpo

theorem poisOkHartSnoc (G : Gexec) (x y : Nat) (c : Cand) (l : Lbl) (ev : Nat → Geid) :
    poisOkHart G c ev y →
    (x = y → cstepPoisOk G x c l) →
    poisOkHart G (candSnoc c ⟨x, l⟩) (evSnoc c ev (x, gcnt x c.cdTr)) y := by
  intro hpd hstp p s hs hpo hag k hk
  by_cases hp : p < c.cdTr.length
  · obtain ⟨hs', hev, -, hlg, hpr⟩ := WeakRvwmoGlue2.snocLt c _ ev (x, gcnt x c.cdTr) p s hs hp
    have hpo' : cpoisStep G c ev p s := by
      unfold cpoisStep cwitStep at hpo ⊢
      rw [hev, hpr] at hpo
      exact hpo
    rw [hlg, hev]
    rw [hev] at hag
    exact hpd p s hs' hpo' hag k (Nat.le_trans (gcntSnocLe c x y l) hk)
  · obtain ⟨rfl, rfl⟩ := WeakRvwmoGlue2.snocEnd c _ p s hs hp
    have hcg : ∀ base n, latestReadLbl c false base n =
        latestReadLbl (cdPre (candSnoc c ⟨x, l⟩) c.cdTr.length) false base n :=
      fun base n => latestReadLblCongr _ _ _ _ _ (cdPreSnocImg c _).symm (cdPreSnocLog c _).symm
    unfold cpoisStep cwitStep at hpo
    rw [evSnocEnd] at hpo hag
    obtain ⟨-, ⟨base, n, hlb⟩, hne, hnw⟩ := hpo
    have hxy : x = y := hag
    subst hxy
    rw [gcntCandSnocSelf] at hk
    rw [evSnocEnd, candSnocLog c _ c.cdTr.length (Nat.le_refl _)]
    exact hstp rfl ⟨base, n, hlb.trans (hcg base n).symm⟩ hne
      (fun ⟨b1, n1, t1, v1, hl1, hn1, hlb1⟩ =>
        hnw ⟨b1, n1, t1, v1, hl1, hn1, hlb1.trans (hcg b1 n1)⟩) k hk

theorem cpolCtxSnoc (G : Gexec) (W : Geid → Prop) (x : Nat) (c : Cand) (l : Lbl) :
    gwf G →
    cpolCtx G W x c →
    cstepCls G W x c l →
    (lbIsW l = true → gwix G (x, gcnt x c.cdTr) = (cdLogEnd c).length + 1) →
    (∀ ev', CtracePrefix G (candSnoc c ⟨x, l⟩) ev' W →
       witFenceUb G (candSnoc c ⟨x, l⟩) ev' W (x, gcnt x c.cdTr + 1)) →
    cstepPoisOk G x c l →
    cpolCtx G W x (candSnoc c ⟨x, l⟩) := by
  rintro hwf ⟨ev, hgt, -, hpd⟩ hcls hix hub hstp
  have hgt' := ctracePrefixSnoc G c ev W x l hwf hgt hcls hix
  refine ⟨_, hgt', ?_, poisOkHartSnoc G x x c l ev hpd (fun _ => hstp)⟩
  rw [gcntCandSnocSelf]
  exact hub _ hgt'

/-! ## 3.1b (P-1), in `certSegment'`'s own `Hpres` shape -/

theorem cpolHpres (G : Gexec) (W : Geid → Prop) (x : Nat) (Q : Lbl → Prop) :
    gwf G →
    -- the STEP CLASSIFICATION — the read policy's own output
    (∀ (c0 : Cand) (lb lb' : Lbl),
       cpolCtx G W x c0 → srvwmoConsistent c0 → Q lb → lblReidx lb lb' →
       mstepOk (candLastSt c0) x lb' →
       cstepCls G W x c0 lb' ∧
       (lbIsW lb' = true → gwix G (x, gcnt x c0.cdTr) = (cdLogEnd c0).length + 1) ∧
       cstepPoisOk G x c0 lb') →
    -- (P-3) `witFenceUb` at the next position
    (∀ (c0 : Cand) (lb' : Lbl) (ev' : Nat → Geid),
       CtracePrefix G (candSnoc c0 ⟨x, lb'⟩) ev' W →
       witFenceUb G (candSnoc c0 ⟨x, lb'⟩) ev' W (x, gcnt x c0.cdTr + 1)) →
    ∀ (c0 : Cand) (lb lb' : Lbl),
      cpolCtx G W x c0 → srvwmoConsistent c0 → Q lb → lblReidx lb lb' →
      mstepOk (candLastSt c0) x lb' →
      cpolCtx G W x (candSnoc c0 ⟨x, lb'⟩) := by
  intro hwf hcls hub c0 lb lb' hctx hc hQ hri hok
  obtain ⟨hcl, hix, hstp⟩ := hcls c0 lb lb' hctx hc hQ hri hok
  exact cpolCtxSnoc G W x c0 lb' hwf hctx hcl hix (hub c0 lb') hstp

/-! ## 3.2 A certified configuration IS a `RunData` -/

theorem runDataOfCyc (boot : Nat → Pexv6) (d0 : Efab) (N : Nat) (G : Gexec) (S : CycState) :
    cstOk d0 S →
    S.cstC.cdImg = G.gxImg →
    S.cstPst 0 = (List.range' 0 N).map boot →
    S.cstDv 0 = d0 →
    RunData boot d0 N G S.cstC S.cstPst S.cstDv :=
  fun ⟨hc, hpo, _⟩ himg hpst hdv => ⟨hc, himg, hpst, hdv, hpo⟩

/-! ## 3.3 `certSupply` from a WALK SUPPLY -/

def walkSupply (boot : Nat → Pexv6) (d0 : Efab) (im : Image) (nh : Nat) (N : Nat) : Prop :=
  ∀ (GD : Gdexec) (cs : List Nat) (c0 : Cand) (pst0 : Nat → List Pexv6)
    (z : Geid) (ss : List Seg),
    rvwmoMinusDepsConsistent GD → gdexecQconf boot d0 im nh GD →
    cutOk GD.gdG cs →
    RunData boot d0 N GD.gdG c0 pst0 (fun _ => d0) →
    ss ≠ [] → rawChain GD z z ss →
    ∃ (l : List Segout) (S0 Sf : CycState),
      segsRun d0 l S0 Sf ∧
      Sf.cstC.cdImg = GD.gdG.gxImg ∧
      Sf.cstPst 0 = (List.range' 0 N).map boot ∧
      Sf.cstDv 0 = d0 ∧
      logOf GD.gdG (cdLog Sf.cstC Sf.cstC.cdTr.length)

theorem certSupplyOfWalk (boot : Nat → Pexv6) (d0 : Efab) (im : Image) (nh : Nat) (N : Nat) :
    walkSupply boot d0 im nh N → certSupply boot d0 im nh N := by
  intro hw GD cs c0 pst0 z ss hcons hq hcut hrd0 hne hch
  obtain ⟨l, S0, Sf, hrun, himg, hpst, hdv, hlog⟩ :=
    hw GD cs c0 pst0 z ss hcons hq hcut hrd0 hne hch
  exact ⟨Sf.cstC, Sf.cstPst, Sf.cstDv,
    runDataOfCyc boot d0 N GD.gdG Sf (segsRunOk d0 l S0 Sf hrun) himg hpst hdv, hlog⟩

/-! ## 3.4 (O-A) THE MINIMAL ORDER CONDITION, exactly -/

theorem walkExitsGmoForced (G : Gexec) (d0 : Efab) (l : List Segout) (S0 Sf : CycState)
    (ev : Nat → Geid) (W : Geid → Prop) (o1 o2 : Segout) (j1 j2 : Nat)
    (rl1 rl2 : Bool) (b1 b2 : Int) (vs1 vs2 : List (BitVec 8)) (k1 k2 : WmClass) :
    segsRun d0 l S0 Sf →
    CtracePrefix G Sf.cstC ev W →
    o1 ∈ l → o2 ∈ l →
    o1.soRow[j1]? = some (Lbl.LStore rl1 b1 vs1 k1) →
    o2.soRow[j2]? = some (Lbl.LStore rl2 b2 vs2 k2) →
    o1.soOff + j1 < o2.soOff + j2 →
    gwix G (ev (o1.soOff + j1)) < gwix G (ev (o2.soOff + j2)) := by
  intro hrun hgt ho1 ho2 hj1 hj2 hlt
  obtain ⟨-, -, -, -, hex, -⟩ := certCycle d0 l S0 Sf hrun
  exact ctpWixGmoMono G Sf.cstC ev W _ _ _ _ hgt (hex o1 ho1 j1 rl1 b1 vs1 k1 hj1)
    (hex o2 ho2 j2 rl2 b2 vs2 k2 hj2) rfl rfl hlt

/-! # 4. THE THEOREM, WITH THE PREMISE LIST THAT REMAINS -/

/-- Lean-only (deviation 5): `hullRun` at the ZERO CUT, where the fetch-inertness premise is
free — the hull's rows are empty, so the realized candidate's trace has no step. -/
theorem WeakRvwmoGlue2.hullRunZcut (boot : Nat → Pexv6) (d0 : Efab) (im : Image) (nh : Nat)
    (GD : Gdexec) (N : Nat) :
    rvwmoMinusDepsConsistent GD →
    gdexecQconf boot d0 im nh GD →
    cutOk GD.gdG (zcut GD.gdG) →
    (∀ x, ¬ tc (racyD (gdHull GD (zcut GD.gdG))) x x) →
    GD.gdG.gxProg.length ≤ N →
    ∃ (c : Cand) (pst : Nat → List Pexv6) (rho : Nat → Nat),
      RunData boot d0 N GD.gdG c pst (fun _ => d0) ∧
      (∀ i, (c.cdTr.filter (fun s => decide (s.esAg = i))).map (fun s => s.esLb) =
        (List.take (((zcut GD.gdG)[i]?).getD 0) ((GD.gdG.gxProg[i]?).getD [])).map
          (lblRen rho)) := by
  intro hcons hq hcut hacy hN
  obtain ⟨c, rho, hc, himg, hpst, hrow⟩ :=
    hullRealizableRowsG boot d0 im nh GD (zcut GD.gdG) N hcons hq (cutOkProper _ _ hcut) hacy hN
  have hfi : candFetchInert boot d0 N c := by
    intro i em _ _ base tvs n k s _ hk hag _
    have hr := hrow i
    rw [WeakRvwmoGlue2.zcutGetD, List.take_zero, List.map_nil, List.map_eq_nil_iff,
      List.filter_eq_nil_iff] at hr
    exact absurd (decide_eq_true hag) (hr s (List.mem_of_getElem? hk))
  obtain ⟨pst, hpst0, hprog⟩ := hpst hfi
  exact ⟨c, pst, rho, ⟨hc, himg, hpst0, rfl, hprog⟩, hrow⟩

section glue

open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode
open Language.Notation PrimStep
open LeanRV64D

/-- Lean-only (deviation 5): `WeakRvwmoGlue.cycleKillOfL2`'s proof, run at the zero cut
(so neither `cutSupply` nor `WeakRvwmoGlue.hullRunFetchInert` is needed). -/
theorem WeakRvwmoGlue2.cycleKillZ (hlc : HasLC) (GF : BundledGFunctors) [MachGpreS hlc GF]
    [WeakGpreS GF]
    (gen : Nat) (σ0 : WGState) (D : CPU → List Register) (hD : ∀ c, (D c).Nodup)
    (Nm : Int → Int → Namespace) (P : Int → Int → Prop)
    (boot : Nat → Pexv6) (d0 : Efab) (N : Nat) :
    freshEra gen σ0 →
    (List.range' 0 N).map boot = epsInit σ0 →
    d0 = efInit σ0.wgdev →
    wpPackage hlc GF gen σ0 D →
    (∀ a base, P a base → wpPackageProt hlc GF gen σ0 D (Nm a base) a base) →
    (∀ ρ, rtc epfRun (epInit gen, σ0) ρ → efetchItvOk ρ.1 ρ.2) →
    certSupply boot d0 (imgZ σ0.wgimg) N N →
    l2Claim boot d0 (imgZ σ0.wgimg) N P (badRun gen σ0) →
    cycleKill boot d0 (imgZ σ0.wgimg) N := by
  intro hfr hb1 hb2 hwp hwpp hcov hcert hl2
  intro GD hcons hq hIH x hcyc
  -- (1) the cycle, as segments
  obtain ⟨z, ss, hne, hch⟩ := cycleSegments GD x hcons.2.1 hcyc
  -- (2) the zero cut, and the realized (empty) causal past
  obtain ⟨i, hi, hn⟩ := cycleHasEvent GD z ss hcons.1 hne hch
  have hcutok := zcutCutOk GD.gdG i hi hn
  have himg := gdexecQconfImg _ _ _ _ _ hq
  have hN := gdexecQconfNharts _ _ _ _ _ hq
  obtain ⟨c0, pst0, -, hrd0, -⟩ :=
    WeakRvwmoGlue2.hullRunZcut boot d0 _ N GD N hcons hq hcutok
      (hIH _ (cutOkProper _ _ hcutok)) hN
  -- (3) the certified configuration
  obtain ⟨c, pst, dv, hrd, hlog⟩ :=
    hcert GD (zcut GD.gdG) c0 pst0 z ss hcons hq hcutok hrd0 hne hch
  -- (4) the erased run, and the exports at its log
  obtain ⟨t2, σ2, hrtc, hlgeq⟩ :=
    runErased gen σ0 boot d0 N GD.gdG c pst dv hfr hcov hb1 hb2 himg hrd
  have hpr : protReg P (cdLog c c.cdTr.length) := by
    rw [← hlgeq]
    exact protRegOfRun hlc GF gen σ0 D hD Nm P t2 σ2 hfr hwpp hrtc
  -- (5) the per-site classification, and the kill
  have hnB : ¬ badRun gen σ0 := noBadRun hlc GF gen σ0 D hD hfr hwp
  exact cycleKillArms GD.gdG z ss hcons.1 hne
    (rawChainChain GD P (cdLog c c.cdTr.length) (badRun gen σ0) ss hcons hlog hpr hnB
      (hl2 GD hq (cdLog c c.cdTr.length) z ss hcons hlog hpr hne hch) z z ss
      (fun _ h => h) hch)

/-- Rocq `cycle_kill_of_l2'`: the glue's theorem without `bootTie` (deviations 2-5; the
`cutSupply` premise is kept but unused). -/
theorem cycleKillOfL2' (hlc : HasLC) (GF : BundledGFunctors) [MachGpreS hlc GF] [WeakGpreS GF]
    (gen : Nat) (σ0 : WGState) (D : CPU → List Register) (hD : ∀ c, (D c).Nodup)
    (Nm : Int → Int → Namespace) (P : Int → Int → Prop)
    (boot : Nat → Pexv6) (d0 : Efab) (N : Nat) :
    freshEra gen σ0 →
    (List.range' 0 N).map boot = epsInit σ0 →
    d0 = efInit σ0.wgdev →
    wpPackage hlc GF gen σ0 D →
    (∀ a base, P a base → wpPackageProt hlc GF gen σ0 D (Nm a base) a base) →
    -- THE FETCH-VIEW PREMISE (deviation 4)
    (∀ ρ, rtc epfRun (epInit gen, σ0) ρ → efetchItvOk ρ.1 ρ.2) →
    cutSupply boot d0 (imgZ σ0.wgimg) N →
    certSupply boot d0 (imgZ σ0.wgimg) N N →
    l2Claim boot d0 (imgZ σ0.wgimg) N P (badRun gen σ0) →
    cycleKill boot d0 (imgZ σ0.wgimg) N :=
  fun hfr hb1 hb2 hwp hwpp hcov _ hcert hl2 =>
    WeakRvwmoGlue2.cycleKillZ hlc GF gen σ0 D hD Nm P boot d0 N hfr hb1 hb2 hwp hwpp hcov hcert
      hl2

/-- Rocq `cycle_kill_of_l2''` (deviations 2-5). -/
theorem cycleKillOfL2'' (hlc : HasLC) (GF : BundledGFunctors) [MachGpreS hlc GF] [WeakGpreS GF]
    (gen : Nat) (σ0 : WGState) (D : CPU → List Register) (hD : ∀ c, (D c).Nodup)
    (Nm : Int → Int → Namespace) (P : Int → Int → Prop)
    (boot : Nat → Pexv6) (d0 : Efab) (N : Nat) :
    -- (i) the boot plumbing
    freshEra gen σ0 →
    (List.range' 0 N).map boot = epsInit σ0 →
    d0 = efInit σ0.wgdev →
    -- (ii) THE L2′ CLAIM
    l2Claim boot d0 (imgZ σ0.wgimg) N P (badRun gen σ0) →
    -- (iii) the certification walk — carrying (P-3) and (P-4)
    walkSupply boot d0 (imgZ σ0.wgimg) N N →
    -- (iv) the WP package
    wpPackage hlc GF gen σ0 D →
    (∀ a base, P a base → wpPackageProt hlc GF gen σ0 D (Nm a base) a base) →
    -- THE FETCH-VIEW PREMISE (deviation 4)
    (∀ ρ, rtc epfRun (epInit gen, σ0) ρ → efetchItvOk ρ.1 ρ.2) →
    cycleKill boot d0 (imgZ σ0.wgimg) N :=
  fun hfr hb1 hb2 hl2 hwalk hwp hwpp hcov =>
    cycleKillOfL2' hlc GF gen σ0 D hD Nm P boot d0 N hfr hb1 hb2 hwp hwpp hcov
      (cutSupplyOfCycle boot d0 _ N) (certSupplyOfWalk boot d0 _ N N hwalk) hl2

/-- … and T2-LIN itself, at the same premises. -/
theorem t2linOfL2'' (hlc : HasLC) (GF : BundledGFunctors) [MachGpreS hlc GF] [WeakGpreS GF]
    (gen : Nat) (σ0 : WGState) (D : CPU → List Register) (hD : ∀ c, (D c).Nodup)
    (Nm : Int → Int → Namespace) (P : Int → Int → Prop)
    (boot : Nat → Pexv6) (d0 : Efab) (N : Nat) :
    freshEra gen σ0 →
    (List.range' 0 N).map boot = epsInit σ0 →
    d0 = efInit σ0.wgdev →
    l2Claim boot d0 (imgZ σ0.wgimg) N P (badRun gen σ0) →
    walkSupply boot d0 (imgZ σ0.wgimg) N N →
    wpPackage hlc GF gen σ0 D →
    (∀ a base, P a base → wpPackageProt hlc GF gen σ0 D (Nm a base) a base) →
    (∀ ρ, rtc epfRun (epInit gen, σ0) ρ → efetchItvOk ρ.1 ρ.2) →
    ∀ GD : Gdexec,
      rvwmoMinusDepsConsistent GD →
      gdexecQconf boot d0 (imgZ σ0.wgimg) N GD →
      ∀ x, ¬ tc (racyD GD) x x :=
  fun hfr hb1 hb2 hl2 hwalk hwp hwpp hcov =>
    t2linOfCycleKill boot d0 _ N
      (cycleKillOfL2'' hlc GF gen σ0 D hD Nm P boot d0 N hfr hb1 hb2 hl2 hwalk hwp hwpp hcov)

end glue

/-! # 5. NON-VACUITY -/

theorem lbgdCutOk : cutOk lbgd.gdG (zcut lbgd.gdG) := by
  obtain ⟨z, ss, hne, hch⟩ := lbgdSegments
  obtain ⟨i, hi, hn⟩ := cycleHasEvent lbgd z ss lbGraphDepsConsistent.1 hne hch
  exact zcutCutOk _ i hi hn

theorem lbgdZcutEmpty : zcut lbgd.gdG = [0, 0] := rfl

theorem lbgdCutDropsEverything (e : Geid) : gcut (zcut lbgd.gdG) e = false := gcutZcut _ e

theorem lbgdHullEmpty (i : Nat) : ((gxHull lbg (zcut lbg)).gxProg[i]?).getD [] = [] :=
  zcutHullRows lbg i

end Weak
