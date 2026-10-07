/-
Weak: **R-2: THE CERTIFICATION WALK, part 2 — the chained walk** (Rocq §4.5–§4.6; §1–§4 are
`WeakRvwmoWalk`, §5 is `WeakRvwmoWalk3`).

Rocq: `iris/WeakRvwmoWalk.v` @ xxvzwolszwmp (split at its section boundaries; this part imports
`Weak.WeakRvwmoWalk`).  NOT to be confused with the Rocq file `WeakRvwmoWalk2.v`, whose Lean
port, if any, is a different file.

## The Rocq header, in substance

`WeakRvwmoWalk` §4.1–§4.4 build ONE segment at ONE state; chaining them generically needs two
changes.  (a) THE WITNESS SET IS FROZEN: `cpolCtx G (wwit G n) x` cannot be carried across a
step (`wwit G n` shrinks with `n` while `CtracePrefix` is not monotone that way), so the walk
carries ONE set `W` throughout and `wwit G n` survives only inside the per-position SITE DATUM
`wsiteCls`.  (b) THE INVARIANT CARRIES THE PROCESS STATES: `wlkInv'` records, for every hart, its
emission from its current row position (`wemit`), the walk state's process identified with it
(`pexDag`), its release-pending fold, the node reachability (`wnd`), and the ROW-POSITION
BOUNDARY (`wposLo`/`wposHi`).  The per-hart taint `tm x` is ACCUMULATED along the row and the
old global `wrdsFree` is replaced by two per-position obligations: the exit's read-set freedom
(`wexitUt`) and the POISONED arm (`wpoisSite`, which contains the fault boundary
`poisonedNoFault`).  The fused RMW is SERVED (§4.5b', `wcpolpAt`).  `wlkStep'OfSupply` DERIVES
the whole per-state datum from a per-GRAPH datum `wsupply`, and `walkSupplyOfSites` is the
theorem.

## Deviations from Rocq

1. NAMES / VOCABULARY as `WeakRvwmoWalk` deviation 1; `default [] (gx_prog G !! x)` ↦
   `(G.gxProg[x]?).getD []`; `T ⊆ T'` is `List.Subset`; `is_Some o` ↦ `o.isSome`.
2. O2 / D1 — FETCH-INERTNESS (`WeakRvwmoWalk` deviation 2, continued): `wsiteOk'` and
   `wsiteSupply` gain the conjunct `WeakRvwmoWalk.wfetchSite d0 Nd x p` (last), and `wpol'` /
   `wblkPolAt'` the conclusion conjunct `lbFetchInert (candLastSt c0) x l'` right after
   `mstepOk` (the shape `segStepOfSegment`'s `Hpol''` asks for).  The pair route needs none.
   `wsupply` therefore carries it through `wsiteSupply` (consumers of `walkSupplyOfSites` /
   `wlkStep'OfSupply` supply it per position).
3. `rdsOkDec` is `Classical.em` (Rocq: `decide` over `Forall`).  In `wlkStep'OfSupply`
   Rocq's `pose k0 := gcnt x …` is an equation `hk0 : gcnt x St.cstC.cdTr = k0`.
4. Lean-only `WeakRvwmoWalk2.candEmptyWs` (the empty candidate's machine `Wstate` is `wsInit`
   at every hart, `WeakRvwmoCert.smWs` at an arbitrary hart).

**Rocq → Lean name map.**  `qrow` `qrow`, `qrow_lbl` `qrowLbl`, `row_ws_aux_app` `rowWsAuxApp`,
`row_ws_seg` `rowWsSeg`, `wemit` `wemit`, `pex_dag` `pexDag`, `pex_dag_refl` `pexDagRefl`,
`src_in_log_of_pfx'` `srcInLogOfPfx'`, `wrmw_site` `wrmwSite`, `wcpolp_at` `wcpolpAt`, `wubA`
`wubA`, `wubA_wub` `wubAWub`, `pois_ok` `poisOk`, `pois_ok_mstep` `poisOkMstep`,
`pois_ok_cpois` `poisOkCpois`, `pois_ok_notw` `poisOkNotw`, `wcls_of_pois` `wclsOfPois`,
`wexit_ut` `wexitUt`, `poisoned_no_fault` `poisonedNoFault`, `wpois_site` `wpoisSite`,
`wpois_no_fault` `wpoisNoFault`, `rds_ok_dec` `rdsOkDec`, `wsite_cls` `wsiteCls`, `wsite_ok'`
`wsiteOk'`, `wQ'` `wQ'`, `wQ'_rmw_site` `wQ'RmwSite`, `wQ'_lbl` `wQ'Lbl`, `wQ'_exit_ut`
`wQ'ExitUt`, `wsite_cls_notW` `wsiteClsNotW`, `wpois_inv` `wpoisInv`, `wctx'` `wctx'`,
`wctx'_cpol` `wctx'Cpol`, `wblk_pol_at'` `wblkPolAt'`, `wpol'` `wpol'`, `wpol'_of_sites`
`wpol'OfSites`, `wctx'_pres` `wctx'Pres`, `wcpolp_of_sites` `wcpolpOfSites`,
`wlk_seg_of_cert2` `wlkSegOfCert2`, `wpos_lo` `wposLo`, `wpos_hi` `wposHi`, `wlk_inv'`
`wlkInv'`, `wlk_inv'_inv` `wlkInv'Inv`, `wlk_step'` `wlkStep'`, `wlk_run'` `wlkRun'`,
`wlk_start_inv'` `wlkStartInv'`, `wsite_supply` `wsiteSupply`, `gwrow_gmo` `gwrowGmo`,
`gwrow_gmo_of_rule14` `gwrowGmoOfRule14`, `wsupply` `wsupply`, `gcnt_app_ne` `gcntAppNe`,
`seg_split_exit` `segSplitExit`, `gwix_pin` `gwixPin`, `wlk_step'_of_supply`
`wlkStep'OfSupply`, `wemit_of_qconf` `wemitOfQconf`, `walk_steps'` `walkSteps'`,
`walk_supply_of_steps'` `walkSupplyOfSteps'`, `walk_supply_of_sites` `walkSupplyOfSites`.

**File-qualified names:** none of this part's Rocq names is in `notes/weak-port-dupnames.json`;
Lean-only (deviation 4): `WeakRvwmoWalk2.candEmptyWs`.

**Dropped:** none (§4.5–§4.6: Rocq 57 declarations; Lean 58 = 57 + the 1 Lean-only).
-/
import Weak.WeakRvwmoWalk

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D
open Wlabel

/-- The parked-fence field, abbreviated (as in `WeakRvwmoCert2`). -/
local notation "Ofence" => Option (Bool × Bool × Bool × Bool)

/-! # 4.5 THE CHAINED WALK: A FROZEN WITNESS SET, AND AN INVARIANT THAT CARRIES WHAT THE NEXT
STEP NEEDS -/

/-- Hart `x`'s row, as a list; `gxLbl` is its lookup. -/
def qrow (G : Gexec) (x : Nat) : List Lbl :=
  (G.gxProg[x]?).getD []

theorem qrowLbl (G : Gexec) (x : Nat) (k : Nat) : gxLbl G (x, k) = (qrow G x)[k]? := by
  unfold gxLbl qrow
  cases G.gxProg[x]? <;> simp

/-! ## 4.5a The row fold, over a segment -/

theorem rowWsAuxApp (t : Nat) (ws : Wstate) (r1 r2 : List Lbl) :
    rowWsAux t ws (r1 ++ r2) = rowWsAux (t + r1.length) (rowWsAux t ws r1) r2 := by
  induction r1 generalizing t ws with
  | nil => rfl
  | cons lb r1 ih =>
    show rowWsAux (t + 1) (lblPost t ws lb) (r1 ++ r2) = _
    rw [ih, List.length_cons, show t + 1 + r1.length = t + (r1.length + 1) by omega]
    rfl

theorem rowWsSeg (row : List Lbl) (k0 L : Nat) :
    k0 ≤ row.length →
    rowWsAux k0 (rowWs row k0) ((row.drop k0).take L) = rowWs row (k0 + L) := by
  intro hk
  unfold rowWs
  rw [← take_take_drop, rowWsAuxApp, List.length_take, Nat.zero_add,
    Nat.min_eq_left hk]

/-! ## 4.5b The per-hart emission tail, and the process identification -/

/-- "Hart `x`'s emission, from row position `k` on, starts at `p`" — DEVICE-QUIET. -/
def wemit (d0 : Efab) (G : Gexec) (x : Nat) (k : Nat) (p : Pexv6) : Prop :=
  ∃ (es : List Eitem) (pfin : Pexv6),
    hemit (fun _ => d0) k (rowWs (qrow G x) k) ((qrow G x).drop k) p es pfin ∧
    LDev ∉ es.map Prod.fst

/-- The walk state's process for a hart IS the emission's, off the taint. -/
def pexDag (T : List Nat) (p q : Pexv6) : Prop :=
  ∀ cpu m rs fn ib, p = .PHart cpu m rs fn ib →
    ∃ rs', q = .PHart cpu m rs' fn ib ∧ dregAgree (fun nn => nn ∉ T) rs rs'

theorem pexDagRefl (T : List Nat) (p : Pexv6) : pexDag T p p := by
  intro cpu m rs fn ib h
  exact ⟨rs, h, dregAgreeRefl _ _⟩

/-! ## 4.5b' THE FUSED RMW's POLICY, POINTWISE -/

theorem srcInLogOfPfx' (G : Gexec) (n : Nat) (c : Cand) (e : Geid) (l : Lbl) (base : Int)
    (ts : List Nat) (vs : List (BitVec 8)) :
    gloadValue G →
    c.cdImg = G.gxImg →
    wlogPfx G n (cdLogEnd c) →
    gxLbl G e = some l →
    lbRd l = some (base, ts, vs) →
    vs.length = ts.length →
    (∀ (j : Nat) (t : Nat), ts[j]? = some t → t ≤ n) →
    srcInLog c base ts vs := by
  rintro hlv himg ⟨_, hpfx⟩ hl hrd hlenv hle
  refine ⟨hlenv, ?_⟩
  intro j t v hj hv
  have hrb : greadsByte G e (accAddr base j) t v := ⟨l, base, ts, vs, j, hl, hrd, hj, hv, rfl⟩
  have hval := (hlv _ _ _ _ hrb).1
  have ht : t ≤ n := hle j t hj
  cases t with
  | zero =>
    rw [logByte0, himg]
    exact hval
  | succ t' =>
    obtain ⟨w, hw, hwb, _⟩ := hval
    rw [logByteS, ← hpfx t' w (by omega) hw]
    cases hm : WeakRvwmoKillArms.gmsg G w with
    | some mm => exact WeakRvwmoWalk.gmsgByte G w _ v mm hwb hm
    | none =>
      exfalso
      obtain ⟨l0, base', vs', j', hl0, hwr, _⟩ := hwb
      simp [WeakRvwmoKillArms.gmsg, hl0, hwr] at hm

/-- THE RMW SITE DATUM. -/
def wrmwSite (G : Gexec) (n : Nat) (x : Nat) (p : Nat) (lb : Lbl) : Prop :=
  gxLbl G (x, p) = some lb ∧
  (∀ (base : Int) (ts : List Nat) (vs : List (BitVec 8)),
     lbRd lb = some (base, ts, vs) →
     ∀ (j : Nat) (t : Nat), ts[j]? = some t → t ≤ n) ∧
  gwix G (x, p) = n + 1

/-- THE PAIR POLICY AT AN ALIGNED CANDIDATE. -/
theorem wcpolpAt (G : Gexec) (W : Geid → Prop) (n : Nat) (x : Nat) (cpu : CPU) (d0 : Efab)
    (c0 : Cand) (ws : Wstate) (lb : Lbl) (l1 l2 : Wlabel) (rds : List Nat) (wrs : List Register)
    (m : SailM Unit) (rs1 rs2 : RegFile) (fn : Ofence) (ib : Ibch) (m' : SailM Unit)
    (rs1' : RegFile) (fn' : Ofence) (ib' : Ibch) (T : List Nat) :
    rvwmoMinusConsistent G →
    c0.cdImg = G.gxImg →
    wlogPfx G n (cdLogEnd c0) →
    srvwmoConsistent c0 →
    cpolCtx G W x c0 →
    ¬ W (x, gcnt x c0.cdTr) →
    wrmwSite G n x (gcnt x c0.cdTr) lb →
    dregAgree (fun nn => nn ∉ T) rs1 rs2 →
    rdsOk (fun nn => nn ∉ T) rds →
    cblkp cpu d0 ws lb l1 l2 rds wrs m rs1 fn ib m' rs1' fn' ib' →
    ∃ rs2',
      cblkp cpu d0 ws lb l1 l2 rds wrs m rs2 fn ib m' rs2' fn' ib' ∧
      mstepOk (candLastSt c0) x lb ∧
      wclsAt G W x c0 lb ∧
      dregAgree (fun nn => nn ∉ T) rs1' rs2' := by
  rintro hcons himg hpfx hc ⟨ev, hgt, _⟩ hnW ⟨hl, hbnd, hix⟩ hag hrds hblk
  have hwf : gwf G := hcons.1
  have hlv : gloadValue G := hcons.2.2.1
  obtain ⟨rs2', hblk2, hag2⟩ := certBlockPairMirror (fun nn => nn ∉ T) cpu d0 ws lb l1 l2 rds wrs
    m rs1 fn ib m' rs1' fn' ib' rs2 hblk hrds hag
  have hrmw : ¬ lbRmwfree lb := cblkpRmw cpu d0 ws lb l1 l2 rds wrs m rs1 fn ib m' rs1' fn' ib' hblk
  cases lb with
  | LLoad => exact absurd trivial hrmw
  | LStore => exact absurd trivial hrmw
  | LFence => exact absurd trivial hrmw
  | LRmw aq rl base ts rvs wvs kc =>
    obtain ⟨_, _, hlenr⟩ := WeakRvwmoFloor.gshape G hwf _ _ hl
    have hlenlog : (cdLogEnd c0).length = n := hpfx.1
    have hsrc : srcInLog c0 base ts rvs :=
      srcInLogOfPfx' G n c0 (x, gcnt x c0.cdTr) _ base ts rvs hlv himg hpfx hl rfl hlenr
        (fun j t hj => hbnd base ts rvs rfl j t hj)
    refine ⟨rs2', hblk2, ?_, wclsOfPfx G W n x c0 _ hpfx hl hnW (fun _ => hix), hag2⟩
    exact certRmwOk G c0 ev W x aq rl base ts rvs wvs kc hcons hgt hc hl (by rw [hix, hlenlog])
      (fun j t hj => by rw [hlenlog]; exact hbnd base ts rvs rfl j t hj) hsrc

/-! ## 4.5c The frozen witness set: its side condition, and the site datum -/

/-- (W-2) FOR EVERY HART AT ONCE. -/
def wubA (G : Gexec) (W : Geid → Prop) : Prop :=
  ∀ (c : Cand) (ev : Nat → Geid) (y : Nat),
    CtracePrefix G c ev W → witFenceUb G c ev W (y, gcnt y c.cdTr)

theorem wubAWub (G : Gexec) (W : Geid → Prop) (x : Nat) : wubA G W → wub G W x := by
  intro hub c0 lb' ev' hct
  have h := hub _ ev' x hct
  rw [gcntCandSnocSelf] at h
  exact h

/-! ## 4.5c' THE POISONED BLOCK, THE EXIT, AND THE FAULT BOUNDARY -/

/-- THE CERTIFIED LABEL AT A POISONED POSITION. -/
def poisOk (c : Cand) (lb2 : Lbl) : Prop :=
  ∃ (base : Int) (n : Nat), lb2 = latestReadLbl c false base n ∧ latestBytesOk c base n

theorem poisOkMstep (c : Cand) (x : Nat) (lb2 : Lbl) :
    srvwmoConsistent c → poisOk c lb2 → mstepOk (candLastSt c) x lb2 := by
  rintro hc ⟨base, n, rfl, hb⟩
  exact certReadWitness c x false base n hc hb

theorem poisOkCpois (c : Cand) (lb2 : Lbl) : poisOk c lb2 → cpoisLbl c lb2 := by
  rintro ⟨base, n, rfl, _⟩
  exact ⟨base, n, rfl⟩

theorem poisOkNotw (c : Cand) (lb2 : Lbl) : poisOk c lb2 → lbIsW lb2 = false :=
  fun h => cpoisLblNotw c lb2 (poisOkCpois c lb2 h)

/-- THE CLASSIFICATION AT A POISONED POSITION — `cstepCls`'s third arm. -/
theorem wclsOfPois (G : Gexec) (W : Geid → Prop) (x : Nat) (c0 : Cand) (lb0 lb' : Lbl) :
    gxLbl G (x, gcnt x c0.cdTr) = some lb0 → lbIsW lb0 = false →
    cpoisLbl c0 lb' →
    gxLbl G (x, gcnt x c0.cdTr) ≠ some lb' →
    ¬ (∃ (base : Int) (n : Nat) (ts0 : List Nat) (vs0 : List (BitVec 8)),
         gxLbl G (x, gcnt x c0.cdTr) = some (Lbl.LLoad false base ts0 vs0) ∧
         ts0.length = n ∧ lb' = latestReadLbl c0 false base n) →
    cstepPoisOk G x c0 lb' →
    wclsAt G W x c0 lb' := by
  intro hl hw hpl hne hnw hstp
  refine ⟨.inr (.inr ⟨⟨lb0, hl, hw⟩, hpl, hne, hnw⟩), ?_, hstp⟩
  intro hw'
  rw [cpoisLblNotw c0 lb' hpl] at hw'
  cases hw'

/-- THE EXIT'S READ-SET FREEDOM. -/
def wexitUt (d0 : Efab) (T : List Nat) (Nd : Nat → CPU → SailM Unit → Prop) (p : Nat) : Prop :=
  ∀ (cpu : CPU) (ws : Wstate) (lb : Lbl) (l1 l2 : Wlabel) (rds : List Nat)
    (wrs : List Register) (m : SailM Unit) (rs : RegFile) (fn : Ofence) (ib : Ibch)
    (m' : SailM Unit) (rs' : RegFile) (fn' : Ofence) (ib' : Ibch),
    Nd p cpu m → lbIsW lb = true →
    (cblk cpu d0 ws lb l1 rds wrs m rs fn ib m' rs' fn' ib' ∨
     cblkp cpu d0 ws lb l1 l2 rds wrs m rs fn ib m' rs' fn' ib') →
    rdsOk (fun nn => nn ∉ T) rds

/-- THE FAULT BOUNDARY, NAMED. -/
def poisonedNoFault (d0 : Efab) (T : List Nat) (Nd : Nat → CPU → SailM Unit → Prop) (p : Nat) :
    Prop :=
  ∀ (cpu : CPU) (ws : Wstate) (lb : Lbl) (l : Wlabel) (rds : List Nat) (wrs : List Register)
    (m : SailM Unit) (rs1 rs2 : RegFile) (fn : Ofence) (ib : Ibch) (m' : SailM Unit)
    (rs1' : RegFile) (fn' : Ofence) (ib' : Ibch),
    Nd p cpu m → lbIsW lb = false →
    ¬ rdsOk (fun nn => nn ∉ T) rds →
    dregAgree (fun nn => nn ∉ T) rs1 rs2 →
    cblk cpu d0 ws lb l rds wrs m rs1 fn ib m' rs1' fn' ib' →
    ∃ (lb2 : Lbl) (l2 : Wlabel) (rds2 : List Nat) (wrs2 : List Register) (m2 : SailM Unit)
      (rs2' : RegFile) (fn2' : Ofence) (ib2' : Ibch),
      cblk cpu d0 ws lb2 l2 rds2 wrs2 m rs2 fn ib m2 rs2' fn2' ib2' ∧
      lblPoisoned lb lb2

/-- THE POISONED SITE DATUM. -/
def wpoisSite (G : Gexec) (W : Geid → Prop) (x : Nat) (d0 : Efab) (T T' : List Nat)
    (Nd : Nat → CPU → SailM Unit → Prop) (p : Nat) : Prop :=
  ∀ (c0 : Cand) (cpu : CPU) (ws : Wstate) (lb : Lbl) (l : Wlabel) (rds : List Nat)
    (wrs : List Register) (m : SailM Unit) (rs1 rs2 : RegFile) (fn : Ofence) (ib : Ibch)
    (m' : SailM Unit) (rs1' : RegFile) (fn' : Ofence) (ib' : Ibch),
    Nd p cpu m → lbIsW lb = false →
    gcnt x c0.cdTr = p →
    ¬ rdsOk (fun nn => nn ∉ T) rds →
    dregAgree (fun nn => nn ∉ T) rs1 rs2 →
    cblk cpu d0 ws lb l rds wrs m rs1 fn ib m' rs1' fn' ib' →
    ∃ (lb2 : Lbl) (l2 : Wlabel) (rds2 : List Nat) (wrs2 : List Register) (m2 : SailM Unit)
      (rs2' : RegFile) (fn2' : Ofence) (ib2' : Ibch),
      cblk cpu d0 ws lb2 l2 rds2 wrs2 m rs2 fn ib m2 rs2' fn2' ib2' ∧
      lblPoisoned lb lb2 ∧
      poisOk c0 lb2 ∧
      -- THE CLASSIFICATION at the appended poisoned label
      wclsAt G W x c0 lb2 ∧
      csync T' m' rs1' fn' ib' m2 rs2' fn2' ib2'

/-- … and the residual it CONTAINS, extracted. -/
theorem wpoisNoFault (G : Gexec) (W : Geid → Prop) (x : Nat) (d0 : Efab) (T T' : List Nat)
    (Nd : Nat → CPU → SailM Unit → Prop) (p : Nat) (c0 : Cand) :
    gcnt x c0.cdTr = p →
    wpoisSite G W x d0 T T' Nd p → poisonedNoFault d0 T Nd p := by
  intro hgc h cpu ws lb l rds wrs m rs1 rs2 fn ib m' rs1' fn' ib' hnd hw hrds hag hblk
  obtain ⟨lb2, l2, rds2, wrs2, m2, rs2', fn2', ib2', hblk2, hpo, _⟩ :=
    h c0 cpu ws lb l rds wrs m rs1 rs2 fn ib m' rs1' fn' ib' hnd hw hgc hrds hag hblk
  exact ⟨lb2, l2, rds2, wrs2, m2, rs2', fn2', ib2', hblk2, hpo⟩

/-- THE READ SET IS DECIDABLE against a taint LIST (deviation 3: classically). -/
theorem rdsOkDec (T rds : List Nat) :
    rdsOk (fun nn => nn ∉ T) rds ∨ ¬ rdsOk (fun nn => nn ∉ T) rds :=
  Classical.em _

/-- THE CLASSIFICATION, AS A SITE DATUM. -/
def wsiteCls (G : Gexec) (W : Geid → Prop) (d0 : Efab) (tm : Nat → List Nat)
    (Nd : Nat → CPU → SailM Unit → Prop) (n : Nat) (x : Nat) (p : Nat) : Prop :=
  (¬ W (x, p) ∧ WeakRvwmoWalk.wsrcLe G n (x, p)) ∨
  (W (x, p) ∧ wwit G n (x, p) ∧ wwitSite G d0 (tm (p + 1)) Nd n x p)

/-- (deviation 2: the last conjunct.) -/
def wsiteOk' (G : Gexec) (W : Geid → Prop) (d0 : Efab) (tm : Nat → List Nat)
    (Nd : Nat → CPU → SailM Unit → Prop) (n : Nat) (x : Nat) (p : Nat) (lb : Lbl) : Prop :=
  gxLbl G (x, p) = some lb ∧
  (lbIsW lb = true → gwix G (x, p) = n + 1) ∧
  (¬ lbRmwfree lb → wrmwSite G n x p lb) ∧
  wsiteCls G W d0 tm Nd n x p ∧
  wexitUt d0 (tm p) Nd p ∧
  wpoisSite G W x d0 (tm p) (tm (p + 1)) Nd p ∧
  WeakRvwmoWalk.wfetchSite d0 Nd x p

def wQ' (G : Gexec) (W : Geid → Prop) (d0 : Efab) (tm : Nat → List Nat)
    (Nd : Nat → CPU → SailM Unit → Prop) (n : Nat) (x : Nat) (k0 kz : Nat) (k : Nat) (lb : Lbl) :
    Prop :=
  k0 ≤ k ∧ k ≤ kz ∧
  wsiteOk' G W d0 tm Nd n x k lb ∧
  (lbIsW lb = true ↔ k = kz)

theorem wQ'RmwSite (G : Gexec) (W : Geid → Prop) (d0 : Efab) (tm : Nat → List Nat)
    (Nd : Nat → CPU → SailM Unit → Prop) (n x k0 kz k : Nat) (lb : Lbl) :
    wQ' G W d0 tm Nd n x k0 kz k lb → ¬ lbRmwfree lb → wrmwSite G n x k lb :=
  fun h => h.2.2.1.2.2.1

theorem wQ'Lbl (G : Gexec) (W : Geid → Prop) (d0 : Efab) (tm : Nat → List Nat)
    (Nd : Nat → CPU → SailM Unit → Prop) (n x k0 kz k : Nat) (lb : Lbl) :
    wQ' G W d0 tm Nd n x k0 kz k lb → gxLbl G (x, k) = some lb :=
  fun h => h.2.2.1.1

theorem wQ'ExitUt (G : Gexec) (W : Geid → Prop) (d0 : Efab) (tm : Nat → List Nat)
    (Nd : Nat → CPU → SailM Unit → Prop) (n x k0 kz k : Nat) (lb : Lbl) :
    wQ' G W d0 tm Nd n x k0 kz k lb → wexitUt d0 (tm k) Nd k :=
  fun h => h.2.2.1.2.2.2.2.1

/-- A WRITE POSITION IS NEVER IN `W` — the site datum's own content. -/
theorem wsiteClsNotW (G : Gexec) (W : Geid → Prop) (d0 : Efab) (tm : Nat → List Nat)
    (Nd : Nat → CPU → SailM Unit → Prop) (n x p : Nat) (lb : Lbl) :
    gxLbl G (x, p) = some lb → lbIsW lb = true →
    wsiteCls G W d0 tm Nd n x p → ¬ W (x, p) := by
  rintro hl hw (⟨h, _⟩ | ⟨_, hW, _⟩)
  · exact h
  · exact absurd hW (wwitNotW G n (x, p) lb hl hw)

/-- THE POISONED INVARIANT, hart-generic and `ev`-generic. -/
def wpoisInv (G : Gexec) (W : Geid → Prop) (c : Cand) : Prop :=
  ∀ ev, CtracePrefix G c ev W → ∀ y, poisOkHart G c ev y

/-- THE WALK'S CARRIED CONTEXT, at the frozen set. -/
def wctx' (G : Gexec) (W : Geid → Prop) (n : Nat) (x : Nat) (kz : Nat) (k : Nat) (c : Cand) :
    Prop :=
  (∃ ev, CtracePrefix G c ev W) ∧
  wpoisInv G W c ∧
  gcnt x c.cdTr = k ∧
  wlogPfx G (wlogn n kz k) (cdLogEnd c)

theorem wctx'Cpol (G : Gexec) (W : Geid → Prop) (n x kz k : Nat) (c : Cand) :
    wubA G W → wctx' G W n x kz k c → cpolCtx G W x c := by
  rintro hub ⟨⟨ev, hct⟩, hpd, _, _⟩
  exact ⟨ev, hct, hub c ev x hct, hpd ev hct x⟩

/-! ## 4.5d The policy, at the frozen set -/

/-- (deviation 2: the `lbFetchInert` conjunct.) -/
theorem wblkPolAt' (G : Gexec) (W : Geid → Prop) (n : Nat) (x : Nat) (cpu : CPU) (d0 : Efab)
    (tm : Nat → List Nat) (Nd : Nat → CPU → SailM Unit → Prop) (c0 : Cand) (ws : Wstate)
    (lb : Lbl) (l : Wlabel) (rds : List Nat) (wrs : List Register) (m : SailM Unit)
    (rs1 rs2 : RegFile) (fn : Ofence) (ib : Ibch) (m' : SailM Unit) (rs1' : RegFile)
    (fn' : Ofence) (ib' : Ibch) :
    rvwmoMinusConsistent G →
    WPolocClosed G W →
    (∀ k, tm k ⊆ tm (k + 1)) →
    srvwmoConsistent c0 →
    c0.cdImg = G.gxImg →
    wlogPfx G n (cdLogEnd c0) →
    cpolCtx G W x c0 →
    wsiteOk' G W d0 tm Nd n x (gcnt x c0.cdTr) lb →
    dregAgree (fun nn => nn ∉ tm (gcnt x c0.cdTr)) rs1 rs2 →
    Nd (gcnt x c0.cdTr) cpu m →
    cblk cpu d0 ws lb l rds wrs m rs1 fn ib m' rs1' fn' ib' →
    ∃ (lb' : Lbl) (l' : Wlabel) (rds' : List Nat) (wrs' : List Register) (rs2' : RegFile)
      (m2' : SailM Unit) (fn2' : Ofence) (ib2' : Ibch),
      cblk cpu d0 ws lb' l' rds' wrs' m rs2 fn ib m2' rs2' fn2' ib2' ∧
      mstepOk (candLastSt c0) x lb' ∧
      lbFetchInert (candLastSt c0) x l' ∧
      lblReidxW lb lb' ∧
      wclsAt G W x c0 lb' ∧
      csync (tm (gcnt x c0.cdTr + 1)) m' rs1' fn' ib' m2' rs2' fn2' ib2' ∧
      (lbIsW lb = true →
         clockstep (tm (gcnt x c0.cdTr + 1)) m' rs1' fn' ib' m2' rs2' fn2' ib2') := by
  intro hcons hpc hmono hc himg hpfx hctx hsite hag hnd hblk
  have hwf : gwf G := hcons.1
  have hlv : gloadValue G := hcons.2.2.1
  obtain ⟨hl, hix, hrmw, hcl, hut, hpois, hfi⟩ := hsite
  have hTT' : tm (gcnt x c0.cdTr) ⊆ tm (gcnt x c0.cdTr + 1) := hmono _
  rcases rdsOkDec (tm (gcnt x c0.cdTr)) rds with hrds | hnrds
  case inr =>
    -- THE POISONED ROUTE
    have hw : lbIsW lb = false := by
      cases hb : lbIsW lb with
      | false => rfl
      | true =>
        exact absurd (hut cpu ws lb l l rds wrs m rs1 fn ib m' rs1' fn' ib' hnd hb (.inl hblk))
          hnrds
    obtain ⟨lb2, l2, rds2, wrs2, m2, rs2', fn2', ib2', hblk2, hlp, hpok, hcls2, hsync⟩ :=
      hpois c0 cpu ws lb l rds wrs m rs1 rs2 fn ib m' rs1' fn' ib' hnd hw rfl hnrds hag hblk
    have hok := poisOkMstep c0 x lb2 hc hpok
    exact ⟨lb2, l2, rds2, wrs2, rs2', m2, fn2', ib2', hblk2, hok,
      hfi c0 cpu ws lb2 l2 rds2 wrs2 m rs2 fn ib m2 rs2' fn2' ib2' hc rfl hnd hblk2 hok,
      lblReidxWPois _ _ hlp, hcls2, hsync, fun h => by rw [hw] at h; cases h⟩
  obtain ⟨rs2', hblk2, hag2'⟩ := certBlockMirror (fun nn => nn ∉ tm (gcnt x c0.cdTr)) cpu d0 ws
    lb l rds wrs m rs1 fn ib m' rs1' fn' ib' rs2 hblk hrds hag
  have hag2 : dregAgree (fun nn => nn ∉ tm (gcnt x c0.cdTr + 1)) rs1' rs2' :=
    dregAgreeTaintMono _ _ rs1' rs2' hTT' hag2'
  rcases hcl with ⟨hnW, hle⟩ | ⟨hW, hwit, hwsite⟩
  · -- THE TRUE ROUTE
    have hok : mstepOk (candLastSt c0) x lb := by
      cases lb with
      | LLoad aq base ts vs =>
        exact cpolRead G W x c0 aq base ts vs hcons hpc hctx hnW hl
          (srcInLogOfPfx G n c0 (x, gcnt x c0.cdTr) aq base ts vs hlv himg hpfx hl
            (WeakRvwmoFloor.gshape G hwf _ _ hl) hle)
      | LStore rl base vs kc =>
        exact certWriteOk c0 x rl base vs kc (WeakRvwmoFloor.gshape G hwf _ _ hl)
      | LFence pr pw sr sw => exact certFenceOk c0 x pr pw sr sw
      | LRmw aq rl base ts rvs wvs kc =>
        -- THE FUSED RMW, served by 4.5b'
        obtain ⟨ev, hgt, _⟩ := hctx
        obtain ⟨_, hbnd, hix2⟩ := hrmw (fun h => h)
        have hlenlog : (cdLogEnd c0).length = n := hpfx.1
        obtain ⟨_, _, hlenr⟩ := WeakRvwmoFloor.gshape G hwf _ _ hl
        have hsrc : srcInLog c0 base ts rvs :=
          srcInLogOfPfx' G n c0 (x, gcnt x c0.cdTr) _ base ts rvs hlv himg hpfx hl rfl hlenr
            (fun j t hj => hbnd base ts rvs rfl j t hj)
        exact certRmwOk G c0 ev W x aq rl base ts rvs wvs kc hcons hgt hc hl
          (by rw [hix2, hlenlog])
          (fun j t hj => by rw [hlenlog]; exact hbnd base ts rvs rfl j t hj) hsrc
    exact ⟨lb, l, rds, wrs, rs2', m', fn', ib', hblk2, hok,
      hfi c0 cpu ws lb l rds wrs m rs2 fn ib m' rs2' fn' ib' hc rfl hnd hblk2 hok,
      lblReidxWRefl lb, wclsOfPfx G W n x c0 lb hpfx hl hnW hix,
      .inl ⟨rfl, rfl, rfl, hag2⟩, fun _ => ⟨rfl, rfl, rfl, hag2⟩⟩
  · -- THE WITNESS ROUTE
    obtain ⟨aq, base, ts, vs, hl', _⟩ := id hwit
    rw [hl'] at hl
    cases hl
    obtain ⟨hgs, hvf⟩ := hwsite
    obtain ⟨haq, hbytes⟩ := hgs c0 aq base ts vs himg hpfx hl'
    subst haq
    obtain ⟨l2, rds2, wrs2, m2, hblk3, hsync⟩ := hvf cpu ws false base ts vs l rds wrs
      m rs2 fn ib m' rs2' fn' ib' (witTvs c0 base ts.length) hnd hblk2
      (witTvsLength c0 base ts.length)
    rw [witTvsLbl c0 false base ts.length] at hblk3
    have hok : mstepOk (candLastSt c0) x (latestReadLbl c0 false base ts.length) :=
      certReadWitness c0 x false base ts.length hc hbytes
    refine ⟨latestReadLbl c0 false base ts.length, l2, rds2, wrs2, rs2', m2, fn', ib', hblk3, hok,
      hfi c0 cpu ws _ l2 rds2 wrs2 m rs2 fn ib m2 rs2' fn' ib' hc rfl hnd hblk3 hok, ?_,
      wclsOfWit G W x c0 base ts vs hl' hW,
      csyncRegs _ m' m2 rs2' rs1' rs2' fn' ib' hsync hag2, fun hw => by cases hw⟩
    refine .inr (.inl ?_)
    show false = false ∧ false = false ∧ base = base ∧
      (lrdTs c0 base ts.length).length = ts.length ∧
      (lrdVs c0 base ts.length).length = (lrdTs c0 base ts.length).length
    exact ⟨rfl, rfl, rfl, by simp [lrdTs], lrdLength _ _ _⟩

/-- (deviation 2: the `lbFetchInert` conjunct.) -/
def wpol' (G : Gexec) (W : Geid → Prop) (n : Nat) (x : Nat) (cpu : CPU) (d0 : Efab)
    (tm : Nat → List Nat) (Nd : Nat → CPU → SailM Unit → Prop) (k0 kz : Nat) : Prop :=
  ∀ (k : Nat) (c0 : Cand) (ws : Wstate) (lb : Lbl) (l : Wlabel) (rds : List Nat)
    (wrs : List Register) (m : SailM Unit) (rs1 rs2 : RegFile) (fn : Ofence) (ib : Ibch)
    (m' : SailM Unit) (rs1' : RegFile) (fn' : Ofence) (ib' : Ibch),
    srvwmoConsistent c0 →
    wctx' G W n x kz k c0 →
    wQ' G W d0 tm Nd n x k0 kz k lb →
    ((candLastSt c0).msWs x).wRelp = ws.wRelp →
    dregAgree (fun nn => nn ∉ tm k) rs1 rs2 →
    Nd k cpu m →
    cblk cpu d0 ws lb l rds wrs m rs1 fn ib m' rs1' fn' ib' →
    ∃ (lb' : Lbl) (l' : Wlabel) (rds' : List Nat) (wrs' : List Register) (rs2' : RegFile)
      (m2' : SailM Unit) (fn2' : Ofence) (ib2' : Ibch),
      cblk cpu d0 ws lb' l' rds' wrs' m rs2 fn ib m2' rs2' fn2' ib2' ∧
      mstepOk (candLastSt c0) x lb' ∧
      lbFetchInert (candLastSt c0) x l' ∧
      lblReidxW lb lb' ∧
      wclsAt G W x c0 lb' ∧
      csync (tm (k + 1)) m' rs1' fn' ib' m2' rs2' fn2' ib2' ∧
      (lbIsW lb = true → clockstep (tm (k + 1)) m' rs1' fn' ib' m2' rs2' fn2' ib2')

theorem wpol'OfSites (G : Gexec) (W : Geid → Prop) (n : Nat) (x : Nat) (cpu : CPU) (d0 : Efab)
    (tm : Nat → List Nat) (Nd : Nat → CPU → SailM Unit → Prop) (k0 kz : Nat) :
    rvwmoMinusConsistent G →
    WPolocClosed G W →
    wubA G W →
    (∀ k, tm k ⊆ tm (k + 1)) →
    wpol' G W n x cpu d0 tm Nd k0 kz := by
  intro hcons hpc hub hmono k c0 ws lb l rds wrs m rs1 rs2 fn ib m' rs1' fn' ib' hc hctx
    ⟨_, hkz, hsite, _⟩ _ hag hnd hblk
  have hcp : cpolCtx G W x c0 := wctx'Cpol G W n x kz k c0 hub hctx
  obtain ⟨_, _, hgc, hpfx⟩ := hctx
  have himg : c0.cdImg = G.gxImg := by
    obtain ⟨ev, hgt, _⟩ := hcp
    exact hgt.ctpImg
  have hpfx' : wlogPfx G n (cdLogEnd c0) := by
    rw [WeakRvwmoWalk.wlognLe n kz k hkz] at hpfx
    exact hpfx
  subst hgc
  exact wblkPolAt' G W n x cpu d0 tm Nd c0 ws lb l rds wrs m rs1 rs2 fn ib m' rs1' fn' ib' hcons
    hpc hmono hc himg hpfx' hcp hsite hag hnd hblk

/-! ## 4.5e The context is preserved, at the frozen set -/

theorem wctx'Pres (G : Gexec) (W : Geid → Prop) (d0 : Efab) (tm : Nat → List Nat)
    (Nd : Nat → CPU → SailM Unit → Prop) (n : Nat) (x : Nat) (k0 kz : Nat) :
    gwf G →
    wubA G W →
    ∀ (k : Nat) (c0 : Cand) (lb lb' : Lbl),
      wctx' G W n x kz k c0 → srvwmoConsistent c0 →
      wQ' G W d0 tm Nd n x k0 kz k lb →
      lblReidxW lb lb' → mstepOk (candLastSt c0) x lb' →
      wclsAt G W x c0 lb' →
      wctx' G W n x kz (k + 1) (candSnoc c0 ⟨x, lb'⟩) := by
  rintro hwf _ k c0 lb lb' ⟨⟨ev, hct⟩, hpd, hgc, hpfx⟩ _ ⟨_, hkz, hsite, hiff⟩ hri _
    ⟨hcl, hix, hstp⟩
  have hpfxn : wlogPfx G n (cdLogEnd c0) := by
    rw [WeakRvwmoWalk.wlognLe n kz k hkz] at hpfx
    exact hpfx
  have hlen : (cdLogEnd c0).length = n := hpfxn.1
  have hct2 : CtracePrefix G (candSnoc c0 ⟨x, lb'⟩) (evSnoc c0 ev (x, gcnt x c0.cdTr)) W :=
    ctracePrefixSnoc G c0 ev W x lb' hwf hct hcl hix
  refine ⟨⟨_, hct2⟩, ?_, by rw [gcntCandSnocSelf, hgc], ?_⟩
  · -- THE POISONED INVARIANT EXTENDS
    intro ev' hct' y
    exact poisOkHartEv G _ _ ev' W y hct2 hct'
      (poisOkHartSnoc G x y c0 lb' ev (hpd ev hct y) (fun _ => hstp))
  · rw [cdLogEndSnoc]
    by_cases hkk : k = kz
    · -- THE EXIT WRITE — a store, or a FUSED RMW, stated through `lbWr`
      subst hkk
      have hw : lbIsW lb = true := hiff.2 rfl
      obtain ⟨hl, _, _, hcls, _, _, _⟩ := hsite
      have hnW : ¬ W (x, gcnt x c0.cdTr) := by
        rw [hgc]
        exact wsiteClsNotW G W d0 tm Nd n x k _ hl hw hcls
      have hw' : lbIsW lb' = true := by rw [lblReidxWIsw lb lb' hri]; exact hw
      have hlbl : gxLbl G (x, gcnt x c0.cdTr) = some lb' := by
        rcases hcl with ⟨_, h⟩ | ⟨hW, _⟩ | ⟨_, hpl, _⟩
        · exact h
        · exact absurd hW hnW
        · rw [cpoisLblNotw c0 _ hpl] at hw'
          cases hw'
      obtain ⟨base, vs, hwr⟩ := lbIsWWr lb' hw'
      have hwix : gwix G (x, gcnt x c0.cdTr) = n + 1 := by rw [hix hw', hlen]
      have hmem : (x, gcnt x c0.cdTr) ∈ gwrites G :=
        gisWGwrites G _ hwf (by rw [hlbl]; rfl) (by simp only [gisW, hlbl]; exact hw')
      have hat : gwriteAt G (n + 1) = some (x, gcnt x c0.cdTr) := by
        rw [← hwix]
        exact gwriteAtGwix G _ hmem
      have hmsg : WeakRvwmoKillArms.gmsg G (x, gcnt x c0.cdTr)
          = some ⟨base, vs, some x, lbCls lb'⟩ := by
        simp [WeakRvwmoKillArms.gmsg, hlbl, hwr]
      have hes : esMsg ⟨x, lb'⟩ = [⟨base, vs, some x, lbCls lb'⟩] := by simp [esMsg, hwr]
      rw [WeakRvwmoWalk.wlognGt n k (k + 1) (by omega), hes]
      exact wlogPfxSnoc G n (cdLogEnd c0) _ _ hpfxn hat hmsg
    · -- A NON-WRITE BLOCK
      have hw : lbIsW lb = false := by
        cases hb : lbIsW lb with
        | false => rfl
        | true => exact absurd (hiff.1 hb) hkk
      have hw' : lbIsW lb' = false := lblReidxWNotw lb lb' hri hw
      rw [esMsgNotw ⟨x, lb'⟩ hw', List.append_nil,
        WeakRvwmoWalk.wlognLe n kz (k + 1) (by omega)]
      exact hpfxn

/-! ## 4.5f The segment, with the CHAINING data exposed -/

/-- THE PAIR POLICY, AT THE FROZEN SET. -/
theorem wcpolpOfSites (G : Gexec) (W : Geid → Prop) (n : Nat) (x : Nat) (cpu : CPU)
    (d0 : Efab) (tm : Nat → List Nat) (Nd : Nat → CPU → SailM Unit → Prop) (k0 kz : Nat) :
    rvwmoMinusConsistent G →
    wubA G W →
    cpolpr x cpu d0 tm (fun k m => Nd k cpu m) (wctx' G W n x kz) (wclsAt G W x)
      (wQ' G W d0 tm Nd n x k0 kz) := by
  intro hcons hub k c0 ws lb l1 l2 rds wrs m rs1 rs2 fn ib m' rs1' fn' ib' hc hctx hQ _ hag
    hrds _ hblk
  have hrmw : ¬ lbRmwfree lb := cblkpRmw cpu d0 ws lb l1 l2 rds wrs m rs1 fn ib m' rs1' fn' ib' hblk
  obtain ⟨_, hkz, hsite, _⟩ := hQ
  obtain ⟨hl, _, hrs, hcls, _, _, _⟩ := hsite
  have hcp : cpolCtx G W x c0 := wctx'Cpol G W n x kz k c0 hub hctx
  obtain ⟨_, _, hgc, hpfx⟩ := hctx
  have himg : c0.cdImg = G.gxImg := by
    obtain ⟨ev, hgt, _⟩ := hcp
    exact hgt.ctpImg
  have hpfx' : wlogPfx G n (cdLogEnd c0) := by
    rw [WeakRvwmoWalk.wlognLe n kz k hkz] at hpfx
    exact hpfx
  have hnW : ¬ W (x, gcnt x c0.cdTr) := by
    rw [hgc]
    rcases hcls with ⟨h, _⟩ | ⟨_, hw, _⟩
    · exact h
    · exfalso
      obtain ⟨aq0, b0, ts0, vs0, hlw, _⟩ := hw
      rw [hlw] at hl
      cases hl
      exact hrmw trivial
  obtain ⟨rs2', hblk2, hok, hcl, hag2⟩ :=
    wcpolpAt G W n x cpu d0 c0 ws lb l1 l2 rds wrs m rs1 rs2 fn ib m' rs1' fn' ib' (tm k) hcons
      himg hpfx' hc hcp hnW (by rw [hgc]; exact hrs hrmw) hag hrds hblk
  exact ⟨rs2', hblk2, hok, hcl, hag2⟩

theorem wlkSegOfCert2 (G : Gexec) (W : Geid → Prop) (n : Nat) (x : Nat) (cpu : CPU) (d0 : Efab)
    (tm : Nat → List Nat) (Nd : Nat → CPU → SailM Unit → Prop) (k0 kz : Nat) (ws0 : Wstate)
    (rowseg : List Lbl) (es : List Eitem) (pfin : Pexv6) (m0 : SailM Unit) (rs10 : RegFile)
    (fn0 : Ofence) (ib0 : Ibch) (St : CycState) (m20 : SailM Unit) (rs20 : RegFile)
    (fn20 : Ofence) (ib20 : Ibch) :
    rvwmoMinusConsistent G →
    WPolocClosed G W →
    wubA G W →
    (∀ k, tm k ⊆ tm (k + 1)) →
    wndOk cpu d0 (wQ' G W d0 tm Nd n x k0 kz) Nd →
    hemit (fun _ => d0) k0 ws0 rowseg (.PHart cpu m0 rs10 fn0 ib0) es pfin →
    LDev ∉ es.map Prod.fst →
    (∀ i lb, rowseg[i]? = some lb → wQ' G W d0 tm Nd n x k0 kz (k0 + i) lb) →
    cstOk d0 St →
    wctx' G W n x kz k0 St.cstC →
    (St.cstPst (cdEnd St.cstC))[x]? = some (.PHart cpu m20 rs20 fn20 ib20) →
    Nd k0 cpu m0 →
    csync (tm k0) m0 rs10 fn0 ib0 m20 rs20 fn20 ib20 →
    ((candLastSt St.cstC).msWs x).wRelp = ws0.wRelp →
    ∃ (St' : CycState) (tradd : List Estep),
      segStep d0 ⟨x, rowseg, cdEnd St.cstC, tradd⟩ St St' ∧
      wctx' G W n x kz (k0 + rowseg.length) St'.cstC ∧
      St'.cstC.cdImg = St.cstC.cdImg ∧
      St'.cstPst 0 = St.cstPst 0 ∧
      St'.cstDv 0 = St.cstDv 0 ∧
      (∃ (m1 : SailM Unit) (rs11 : RegFile) (fn1 : Ofence) (ib1 : Ibch)
         (m21 : SailM Unit) (rs21 : RegFile) (fn21 : Ofence) (ib21 : Ibch),
         pfin = .PHart cpu m1 rs11 fn1 ib1 ∧
         (St'.cstPst (cdEnd St'.cstC))[x]? = some (.PHart cpu m21 rs21 fn21 ib21) ∧
         csync (tm (k0 + rowseg.length)) m1 rs11 fn1 ib1 m21 rs21 fn21 ib21 ∧
         (segLocked rowseg (clockstep (tm k0) m0 rs10 fn0 ib0 m20 rs20 fn20 ib20) →
           clockstep (tm (k0 + rowseg.length)) m1 rs11 fn1 ib1 m21 rs21 fn21 ib21) ∧
         Nd (k0 + rowseg.length) cpu m1) ∧
      ((candLastSt St'.cstC).msWs x).wRelp = (rowWsAux k0 ws0 rowseg).wRelp ∧
      (∀ y, y ≠ x → (St'.cstPst (cdEnd St'.cstC))[y]? = (St.cstPst (cdEnd St.cstC))[y]?) ∧
      (∀ y, y ≠ x → ((candLastSt St'.cstC).msWs y).wRelp
        = ((candLastSt St.cstC).msWs y).wRelp) := by
  intro hcons hpc hub hmono hNok hem hdev hQ hok hctx hp hnd hsync hrelp
  obtain ⟨hNa, hNb, hNbp⟩ := hNok
  have hwf : gwf G := hcons.1
  exact segStepOfSegment x cpu d0 tm (wQ' G W d0 tm Nd n x k0 kz) (wctx' G W n x kz)
    (wclsAt G W x) (fun k m => Nd k cpu m) hmono
    (wctx'Pres G W d0 tm Nd n x k0 kz hwf hub)
    (fun k lb ws l1 l2 rds wrs m rs fn ib m' rs' fn' ib' hQ0 hnd0 hblk =>
      wQ'ExitUt G W d0 tm Nd n x k0 kz k lb hQ0 cpu ws lb l1 l2 rds wrs m rs fn ib m' rs' fn' ib'
        hnd0 (cblkpIsW cpu d0 ws lb l1 l2 rds wrs m rs fn ib m' rs' fn' ib' hblk) (.inr hblk))
    hNa hNb hNbp
    (wpol'OfSites G W n x cpu d0 tm Nd k0 kz hcons hpc hub hmono)
    (wcpolpOfSites G W n x cpu d0 tm Nd k0 kz hcons hub)
    k0 ws0 rowseg es pfin m0 rs10 fn0 ib0 St m20 rs20 fn20 ib20
    hem hdev hQ hok hctx hp hnd hsync hrelp

/-! # 4.6 THE CHAINED WALK ITSELF -/

def wposLo (G : Gexec) (n : Nat) (x : Nat) (k : Nat) : Prop :=
  ∀ j lb, j < k → gxLbl G (x, j) = some lb → lbIsW lb = true → gwix G (x, j) ≤ n

def wposHi (G : Gexec) (n : Nat) (x : Nat) (k : Nat) : Prop :=
  ∀ j lb, k ≤ j → gxLbl G (x, j) = some lb → lbIsW lb = true → n < gwix G (x, j)

/-- THE INVARIANT CARRIES THE TAINT MAP. -/
def wlkInv' (boot : Nat → Pexv6) (d0 : Efab) (N : Nat) (G : Gexec) (W : Geid → Prop)
    (tm : Nat → Nat → List Nat) (St : CycState) (n : Nat) : Prop :=
  wlkInv boot d0 N G St n ∧
  (∃ ev, CtracePrefix G St.cstC ev W) ∧
  wpoisInv G W St.cstC ∧
  (∀ x, x < N →
     ∃ (p q : Pexv6),
       wemit d0 G x (gcnt x St.cstC.cdTr) p ∧
       (St.cstPst (cdEnd St.cstC))[x]? = some q ∧
       pexDag (tm x (gcnt x St.cstC.cdTr)) p q ∧
       ((candLastSt St.cstC).msWs x).wRelp = (rowWs (qrow G x) (gcnt x St.cstC.cdTr)).wRelp ∧
       (∀ cpu m rs fn ib, boot x = .PHart cpu m rs fn ib →
          ∃ m' rs' fn' ib', p = .PHart cpu m' rs' fn' ib') ∧
       -- (N-D) THE NODE IS REACHABLE
       (∀ cpu m rs fn ib, p = .PHart cpu m rs fn ib →
          wnd d0 G boot x (gcnt x St.cstC.cdTr) cpu m)) ∧
  (∀ x, wposLo G n x (gcnt x St.cstC.cdTr)) ∧
  (∀ x, wposHi G n x (gcnt x St.cstC.cdTr))

theorem wlkInv'Inv (boot : Nat → Pexv6) (d0 : Efab) (N : Nat) (G : Gexec) (W : Geid → Prop)
    (tm : Nat → Nat → List Nat) (St : CycState) (n : Nat) :
    wlkInv' boot d0 N G W tm St n → wlkInv boot d0 N G St n :=
  fun h => h.1

/-- ONE CHAINED STEP. -/
def wlkStep' (boot : Nat → Pexv6) (d0 : Efab) (N : Nat) (G : Gexec) (W : Geid → Prop)
    (tm : Nat → Nat → List Nat) (St : CycState) (n : Nat) : Prop :=
  ∃ (o : Segout) (St' : CycState), segStep d0 o St St' ∧ wlkInv' boot d0 N G W tm St' (n + 1)

theorem wlkRun' (boot : Nat → Pexv6) (d0 : Efab) (N : Nat) (G : Gexec) (W : Geid → Prop)
    (tm : Nat → Nat → List Nat)
    (Hsup : ∀ St n, wlkInv' boot d0 N G W tm St n → n < (gwrites G).length →
      wlkStep' boot d0 N G W tm St n)
    (k : Nat) :
    ∀ n St, wlkInv' boot d0 N G W tm St n → n + k = (gwrites G).length →
      ∃ l Sf, segsRun d0 l St Sf ∧ wlkInv boot d0 N G Sf (gwrites G).length := by
  induction k with
  | zero =>
    intro n St hinv hn
    refine ⟨[], St, .segsDone St hinv.1.1, ?_⟩
    rw [← hn, Nat.add_zero]
    exact wlkInv'Inv boot d0 N G W tm St n hinv
  | succ k ih =>
    intro n St hinv hn
    obtain ⟨o, St', hst, hinv'⟩ := Hsup St n hinv (by omega)
    obtain ⟨l, Sf, hrun, hfin⟩ := ih (n + 1) St' hinv' (by omega)
    exact ⟨o :: l, Sf, .segsMore o l St St' Sf hst hrun, hfin⟩

/-- Lean-only (deviation 4): the empty candidate's machine `Wstate`, at every hart. -/
theorem WeakRvwmoWalk2.candEmptyWs (img : Image) (x : Nat) :
    (candLastSt ⟨img, []⟩).msWs x = wsInit := by
  unfold candLastSt
  rw [sttLookup _ _ _ (replay0 (candInit ⟨img, []⟩) ([] : List Estep))]
  rfl

/-! ## 4.6a The START, at the frozen set -/

theorem wlkStartInv' (boot : Nat → Pexv6) (d0 : Efab) (N : Nat) (G : Gexec) (W : Geid → Prop)
    (tm : Nat → Nat → List Nat) :
    gwf G →
    (∀ x, x < N → wemit d0 G x 0 (boot x)) →
    wlkInv' boot d0 N G W tm (wlkStart boot d0 N G) 0 := by
  intro hwf hem
  refine ⟨wlkStartInv boot d0 N G, ⟨fun _ => (0, 0), ctracePrefixEmpty G W⟩, ?_, ?_, ?_, ?_⟩
  · intro ev' _ y p s hs
    simp [wlkStart] at hs
  · intro x hx
    refine ⟨boot x, boot x, hem x hx, ?_, pexDagRefl _ _, ?_, ?_, ?_⟩
    · show ((List.range' 0 N).map boot)[x]? = some (boot x)
      rw [List.getElem?_map, lookup_seq_lt hx]
      simp
    · show ((candLastSt ⟨G.gxImg, []⟩).msWs x).wRelp = (rowWs (qrow G x) 0).wRelp
      rw [WeakRvwmoWalk2.candEmptyWs]
      rfl
    · intro cpu m rs fn ib h
      exact ⟨m, rs, fn, ib, h⟩
    · intro cpu m rs fn ib hb
      exact wndStart d0 G boot x cpu m rs fn ib hb
  · intro x j lb hj
    exact absurd hj (Nat.not_lt_zero j)
  · intro x j lb _ hl hw
    have hmem : (x, j) ∈ gwrites G :=
      gisWGwrites G _ hwf (by rw [hl]; rfl) (by simp only [gisW, hl]; exact hw)
    obtain ⟨i, _, h⟩ := gwixLookup G (x, j) hmem
    omega

/-! ## 4.6b THE PER-GRAPH DATUM the chained walk consumes -/

/-- (deviation 2: the last conjunct.) -/
def wsiteSupply (boot : Nat → Pexv6) (d0 : Efab) (G : Gexec) (W : Geid → Prop)
    (tm : Nat → Nat → List Nat) : Prop :=
  ∀ (n : Nat) (x : Nat) (kz p : Nat) (lb : Lbl),
    gwriteAt G (n + 1) = some (x, kz) →
    p ≤ kz →
    (∀ j lbj, p ≤ j → j < kz → gxLbl G (x, j) = some lbj → lbIsW lbj = false) →
    gxLbl G (x, p) = some lb →
    (¬ lbRmwfree lb → wrmwSite G n x p lb) ∧
    wsiteCls G W d0 (tm x) (wnd d0 G boot x) n x p ∧
    -- THE EXIT'S READ-SET FREEDOM and THE POISONED ARM, per position
    wexitUt d0 (tm x p) (wnd d0 G boot x) p ∧
    wpoisSite G W x d0 (tm x p) (tm x (p + 1)) (wnd d0 G boot x) p ∧
    WeakRvwmoWalk.wfetchSite d0 (wnd d0 G boot x) x p

/-- THE ORDER FACT THE WALK NEEDS, AND EXACTLY IT. -/
def gwrowGmo (G : Gexec) : Prop :=
  ∀ (x : Nat) (j k : Nat), j < k →
    glblIs G (x, j) lbIsW → glblIs G (x, k) lbIsW →
    gwix G (x, j) < gwix G (x, k)

theorem gwrowGmoOfRule14 (G : Gexec) : gwf G → grule14 G → gwrowGmo G := by
  intro hwf h14 x j k hjk hj hk
  have hnd : G.gxGmo.Nodup := hwf.1
  obtain ⟨lj, hlj, hwj⟩ := hj
  obtain ⟨lk, hlk, hwk⟩ := hk
  have hmj : (x, j) ∈ gwrites G :=
    gisWGwrites G _ hwf (by rw [hlj]; rfl) (by simp only [gisW, hlj]; exact hwj)
  have hmk : (x, k) ∈ gwrites G :=
    gisWGwrites G _ hwf (by rw [hlk]; rfl) (by simp only [gisW, hlk]; exact hwk)
  have hmo : gmoLt G (x, j) (x, k) :=
    h14 (x, j) (x, k) ⟨rfl, hjk, by rw [hlj]; rfl, by rw [hlk]; rfl⟩
      (WeakRvwmoGraph.glblIsWGmem G _ ⟨lj, hlj, hwj⟩) ⟨lk, hlk, hwk⟩
  exact (gwixGposLt G (x, j) (x, k) hnd hmj hmk).2 hmo.2.2

def wsupply (boot : Nat → Pexv6) (d0 : Efab) (G : Gexec) (W : Geid → Prop)
    (tm : Nat → Nat → List Nat) (N : Nat) : Prop :=
  gwrowGmo G ∧
  (∀ x k, (gxLbl G (x, k)).isSome → x < N) ∧
  (∀ x k lb, gxLbl G (x, k) = some lb → lbIsW lb = true →
     ∃ cpu m rs fn ib, boot x = .PHart cpu m rs fn ib) ∧
  WPolocClosed G W ∧
  wubA G W ∧
  -- THE PER-HART TAINT IS ACCUMULATED
  (∀ x k, tm x k ⊆ tm x (k + 1)) ∧
  wsiteSupply boot d0 G W tm

/-! ## 4.6c Two frames, and the row split -/

theorem gcntAppNe (tr tradd : List Estep) (x y : Nat) :
    (∀ s, s ∈ tradd → s.esAg = x) → y ≠ x →
    gcnt y (tr ++ tradd) = gcnt y tr := by
  intro hag hne
  unfold gcnt
  rw [List.filter_append, List.length_append]
  have h0 : tradd.filter (fun s => decide (s.esAg = y)) = [] := by
    rw [List.filter_eq_nil_iff]
    intro s hs h
    exact hne ((of_decide_eq_true h).symm.trans (hag s hs))
  rw [h0]
  rfl

theorem segSplitExit (row : List Lbl) (k0 kz : Nat) (lb : Lbl) :
    k0 ≤ kz → row[kz]? = some lb →
    (row.drop k0).take (kz + 1 - k0) = (row.drop k0).take (kz - k0) ++ [lb] := by
  intro hle hkz
  rw [show kz + 1 - k0 = kz - k0 + 1 by omega]
  apply take_S_r
  rw [lookup_drop, show k0 + (kz - k0) = kz by omega]
  exact hkz

/-- A write's index PINS it. -/
theorem gwixPin (G : Gexec) (e : Geid) (n : Nat) :
    G.gxGmo.Nodup → e ∈ gwrites G → gwix G e = n + 1 → gwriteAt G (n + 1) = some e := by
  intro _ he h
  rw [← h]
  exact gwriteAtGwix G e he

/-! ## 4.6d THE STEP, DERIVED -/

theorem wlkStep'OfSupply (boot : Nat → Pexv6) (d0 : Efab) (N : Nat) (G : Gexec)
    (W : Geid → Prop) (tm : Nat → Nat → List Nat) (St : CycState) (n : Nat) :
    rvwmoMinusConsistent G →
    wsupply boot d0 G W tm N →
    wlkInv' boot d0 N G W tm St n →
    n < (gwrites G).length →
    wlkStep' boot d0 N G W tm St n := by
  rintro hcons ⟨h14, hxN, hbh, hpc, hub, hmono, hsite⟩ hinv hn
  have hwf : gwf G := hcons.1
  have hnd : G.gxGmo.Nodup := hwf.1
  obtain ⟨hbase, ⟨ev0, hct0⟩, hpi, hproc, hlo, hhi⟩ := hinv
  obtain ⟨hok, himg, hpst0, hdv0, hpfx⟩ := hbase
  -- ---- 1. WHICH WRITE, AND WHOSE ----
  obtain ⟨w, hw⟩ := someOfIsSome (lookup_lt_is_Some_2 hn)
  have hat : gwriteAt G (n + 1) = some w := hw
  obtain ⟨x, kz⟩ := w
  obtain ⟨hmem, hwix⟩ := gwriteAtInv G (n + 1) (x, kz) hnd hat
  have hisw : gisW G (x, kz) = true := ((gwritesElemOf G _).1 hmem).2
  cases hlbz : gxLbl G (x, kz) with
  | none => simp [gisW, hlbz] at hisw
  | some lbz =>
  have hlbzw : lbIsW lbz = true := by simpa [gisW, hlbz] using hisw
  have hxLT : x < N := hxN x kz (by rw [hlbz]; rfl)
  obtain ⟨k0, hk0⟩ : ∃ k0, gcnt x St.cstC.cdTr = k0 := ⟨_, rfl⟩
  -- ---- 2. THE HART STANDS AT OR BEFORE ITS NEXT WRITE ----
  have hk0le : k0 ≤ kz := by
    by_cases h : k0 ≤ kz
    · exact h
    · exfalso
      have := hlo x kz lbz (by rw [hk0]; omega) hlbz hlbzw
      omega
  -- ---- 3. NOTHING IN BETWEEN IS A WRITE ----
  have hnwr : ∀ j lbj, k0 ≤ j → j < kz → gxLbl G (x, j) = some lbj → lbIsW lbj = false := by
    intro j lbj hj1 hj2 hlj
    cases hb : lbIsW lbj with
    | false => rfl
    | true =>
      exfalso
      have hgt := hhi x j lbj (by rw [hk0]; exact hj1) hlj hb
      have hlt := h14 x j kz hj2 ⟨lbj, hlj, hb⟩ ⟨lbz, hlbz, hlbzw⟩
      omega
  -- ---- 4. THE ROW STRETCH ----
  have hkzr : (qrow G x)[kz]? = some lbz := by rw [← qrowLbl]; exact hlbz
  have hkzlen : kz < (qrow G x).length := lookup_lt_Some hkzr
  have hrowseg : ((qrow G x).drop k0).take (kz + 1 - k0)
      = ((qrow G x).drop k0).take (kz - k0) ++ [lbz] :=
    segSplitExit (qrow G x) k0 kz lbz hk0le hkzr
  have hlenseg : (((qrow G x).drop k0).take (kz + 1 - k0)).length = kz - k0 + 1 := by
    rw [List.length_take, List.length_drop]
    omega
  have hkzeq : k0 + (((qrow G x).drop k0).take (kz + 1 - k0)).length = kz + 1 := by
    rw [hlenseg]
    omega
  -- ---- 5. THE EMISSION AT THE HART'S CURRENT POSITION ----
  obtain ⟨p, q, ⟨es, pfin, hem, hdevf⟩, hq, hdag, hrelp, hph, hndp⟩ := hproc x hxLT
  rw [hk0] at hem hdag hrelp hndp
  obtain ⟨cpu, mb, rsb, fnb, ibb, hbx⟩ := hbh x kz lbz hlbz hlbzw
  obtain ⟨m0, rs10, fn0, ib0, hp⟩ := hph cpu mb rsb fnb ibb hbx
  have hnd0 : wnd d0 G boot x k0 cpu m0 := hndp cpu m0 rs10 fn0 ib0 hp
  subst hp
  obtain ⟨rs20, hq2, hag⟩ := hdag cpu m0 rs10 fn0 ib0 rfl
  subst hq2
  have hdd : (qrow G x).drop k0
      = ((qrow G x).drop k0).take (kz + 1 - k0)
        ++ (qrow G x).drop (k0 + (((qrow G x).drop k0).take (kz + 1 - k0)).length) := by
    have h1 : (qrow G x).drop (k0 + (((qrow G x).drop k0).take (kz + 1 - k0)).length)
        = ((qrow G x).drop k0).drop (kz + 1 - k0) := by
      rw [drop_drop]
      congr 1
      omega
    rw [h1, List.take_append_drop]
  rw [hdd] at hem
  obtain ⟨pm, es1, es2, hem1, hem2, hessp⟩ :=
    hemitApp (fun _ => d0) k0 (rowWs (qrow G x) k0) _ _ _ es pfin hem
  have hdev1 : LDev ∉ es1.map Prod.fst := fun hin =>
    hdevf (by rw [hessp, List.map_append]; exact List.mem_append_left _ hin)
  have hdev2 : LDev ∉ es2.map Prod.fst := fun hin =>
    hdevf (by rw [hessp, List.map_append]; exact List.mem_append_right _ hin)
  have hws : rowWsAux k0 (rowWs (qrow G x) k0) (((qrow G x).drop k0).take (kz + 1 - k0))
      = rowWs (qrow G x) (k0 + (((qrow G x).drop k0).take (kz + 1 - k0)).length) := by
    rw [rowWsSeg (qrow G x) k0 (kz + 1 - k0) (by omega), hlenseg]
    congr 1
    omega
  -- ---- 6. THE SITE DATA ----
  have hQ : ∀ i lb, (((qrow G x).drop k0).take (kz + 1 - k0))[i]? = some lb →
      wQ' G W d0 (tm x) (wnd d0 G boot x) n x k0 kz (k0 + i) lb := by
    intro i lb hi
    have hilt : i < kz - k0 + 1 := by rw [← hlenseg]; exact lookup_lt_Some hi
    have hl : gxLbl G (x, k0 + i) = some lb := by
      rw [qrowLbl]
      have h2 := (lookup_take_Some.1 hi).1
      rw [lookup_drop] at h2
      exact h2
    have hiff : lbIsW lb = true ↔ k0 + i = kz := by
      constructor
      · intro hb
        by_cases hne : k0 + i = kz
        · exact hne
        · exfalso
          rw [hnwr (k0 + i) lb (by omega) (by omega) hl] at hb
          cases hb
      · intro heq
        rw [heq, hlbz] at hl
        cases hl
        exact hlbzw
    obtain ⟨hrmw, hcls, hut, hpois, hfs⟩ := hsite n x kz (k0 + i) lb hat (by omega)
      (fun j lbj hj1 hj2 hlj => hnwr j lbj (by omega) hj2 hlj) hl
    exact ⟨by omega, by omega,
      ⟨hl, fun hb => by rw [hiff.1 hb]; exact hwix, hrmw, hcls, hut, hpois, hfs⟩, hiff⟩
  -- ---- 7. THE SEGMENT ----
  have hctx : wctx' G W n x kz k0 St.cstC :=
    ⟨⟨ev0, hct0⟩, hpi, hk0, by rw [WeakRvwmoWalk.wlognLe n kz k0 hk0le]; exact hpfx⟩
  obtain ⟨St', tradd, hstep, hctx', himg', hpst0', hdv0',
      ⟨m1, rs11, fn1, ib1, m21, rs21, fn21, ib21, hpm, hpx, _, hlockx, hndx⟩, hrelpx, hfr,
      hfrp⟩ :=
    wlkSegOfCert2 G W n x cpu d0 (tm x) (wnd d0 G boot x) k0 kz (rowWs (qrow G x) k0)
      _ es1 pm m0 rs10 fn0 ib0 St m0 rs20 fn0 ib0 hcons hpc hub (hmono x)
      (wndWndOk cpu d0 G boot x _ (fun k lb h =>
        wQ'Lbl G W d0 (tm x) (wnd d0 G boot x) n x k0 kz k lb h))
      hem1 hdev1 hQ hok hctx hq hnd0 (.inl ⟨rfl, rfl, rfl, hag⟩) hrelp
  subst hpm
  -- THE SEGMENT'S ROW ENDS IN A WRITE, so its exit is in LOCKSTEP
  obtain ⟨hm21, hfn21, hib21, hagx⟩ :=
    hlockx (by rw [hrowseg]; exact segLockedSnoc _ _ _ hlbzw)
  subst hm21 hfn21 hib21
  rw [hkzeq] at hagx
  obtain ⟨⟨ev1, hct1⟩, hpi1, hgc1, hpfx1⟩ := hctx'
  rw [hkzeq] at hgc1 hpfx1 hndx
  have hokSt' : cstOk d0 St' := hstep.2.1
  obtain ⟨_, _, _, htr, hagt, _⟩ := id hstep
  refine ⟨_, St', hstep, ?_⟩
  have hlogS : wlogPfx G (n + 1) (cdLogEnd St'.cstC) := by
    rw [WeakRvwmoWalk.wlognGt n kz (kz + 1) (by omega)] at hpfx1
    exact hpfx1
  have hgcy : ∀ y, y ≠ x → gcnt y St'.cstC.cdTr = gcnt y St.cstC.cdTr := by
    intro y hyx
    rw [htr]
    exact gcntAppNe _ tradd x y hagt hyx
  -- ---- 8. THE INVARIANT, AGAIN ----
  refine ⟨⟨hokSt', by rw [himg', himg], by rw [hpst0', hpst0], by rw [hdv0', hdv0], hlogS⟩,
    ⟨ev1, hct1⟩, hpi1, ?_, ?_, ?_⟩
  · intro y hy
    by_cases hyx : y = x
    · subst hyx
      rw [hgc1]
      rw [hws, hkzeq] at hem2
      refine ⟨_, _, ⟨es2, pfin, hem2, hdev2⟩, hpx, ?_, ?_, ?_, ?_⟩
      · intro cpu' m' rs' fn' ib' h
        cases h
        exact ⟨rs21, rfl, hagx⟩
      · rw [hrelpx, hws, hkzeq]
      · intro cpu' m' rs' fn' ib' hb
        rw [hbx] at hb
        cases hb
        exact ⟨_, _, _, _, rfl⟩
      · intro cpu' m' rs' fn' ib' h
        cases h
        exact hndx
    · obtain ⟨py, qy, hemy, hqy, hdagy, hrelpy, hphy, hndy⟩ := hproc y hy
      rw [hgcy y hyx]
      exact ⟨py, qy, hemy, by rw [hfr y hyx]; exact hqy, hdagy,
        by rw [hfrp y hyx]; exact hrelpy, hphy, hndy⟩
  · -- `wposLo` at `n + 1`
    intro y j lb hj hl hb
    by_cases hyx : y = x
    · subst hyx
      rw [hgc1] at hj
      by_cases hlt : j < k0
      · have := hlo y j lb (by rw [hk0]; exact hlt) hl hb
        omega
      · by_cases hjz : j = kz
        · subst hjz
          rw [hlbz] at hl
          cases hl
          omega
        · exfalso
          rw [hnwr j lb (by omega) (by omega) hl] at hb
          cases hb
    · have := hlo y j lb (by rw [← hgcy y hyx]; exact hj) hl hb
      omega
  · -- `wposHi` at `n + 1`
    intro y j lb hj hl hb
    have hmemj : (y, j) ∈ gwrites G :=
      gisWGwrites G _ hwf (by rw [hl]; rfl) (by simp only [gisW, hl]; exact hb)
    have hne3 : gwix G (y, j) ≠ n + 1 := by
      intro heq
      have hpin := gwixPin G (y, j) n hnd hmemj heq
      rw [hat] at hpin
      simp only [Option.some.injEq, Prod.mk.injEq] at hpin
      obtain ⟨hxy, hkj⟩ := hpin
      subst hxy hkj
      rw [hgc1] at hj
      omega
    by_cases hyx : y = x
    · subst hyx
      rw [hgc1] at hj
      have := hhi y j lb (by rw [hk0]; omega) hl hb
      omega
    · have := hhi y j lb (by rw [← hgcy y hyx]; exact hj) hl hb
      omega

/-! ## 4.6e THE EMISSION AT THE START, from the conformance bundle -/

theorem wemitOfQconf (boot : Nat → Pexv6) (d0 : Efab) (im : Image) (nh : Nat) (GD : Gdexec)
    (x : Nat) :
    gdexecQconf boot d0 im nh GD → wemit d0 GD.gdG x 0 (boot x) := by
  intro hq
  cases hrow : GD.gdG.gxProg[x]? with
  | some row =>
    obtain ⟨em, hem, hdf, _⟩ := gdexecQconfRows boot d0 im nh GD hq x row hrow
    refine ⟨em.emItems, em.emFin, ?_, hdf⟩
    simp only [qrow, hrow, Option.getD_some, List.drop_zero]
    exact hem
  | none =>
    refine ⟨[], boot x, ?_, List.not_mem_nil⟩
    simp only [qrow, hrow, Option.getD_none, List.drop_nil]
    exact .HEnil _ _ _

/-! ## 4.6f THE WALK, AND ITS THEOREM -/

def walkSteps' (boot : Nat → Pexv6) (d0 : Efab) (N : Nat) (G : Gexec) (W : Geid → Prop)
    (tm : Nat → Nat → List Nat) : Prop :=
  ∀ St n, wlkInv' boot d0 N G W tm St n → n < (gwrites G).length →
    wlkStep' boot d0 N G W tm St n

theorem walkSupplyOfSteps' (boot : Nat → Pexv6) (d0 : Efab) (im : Image) (nh : Nat) (N : Nat) :
    (∀ GD : Gdexec,
       rvwmoMinusDepsConsistent GD → gdexecQconf boot d0 im nh GD →
       ∃ (W : Geid → Prop) (tm : Nat → Nat → List Nat), walkSteps' boot d0 N GD.gdG W tm) →
    walkSupply boot d0 im nh N := by
  intro hsup GD _ _ _ _ _ hcons hq _ _ _ _
  have hwf : gwf GD.gdG := hcons.1.1
  obtain ⟨W, tm, hsteps⟩ := hsup GD hcons hq
  obtain ⟨l, Sf, hrun, _, himg, hpst, hdv, hlog⟩ :=
    wlkRun' boot d0 N GD.gdG W tm hsteps (gwrites GD.gdG).length 0
      (wlkStart boot d0 N GD.gdG)
      (wlkStartInv' boot d0 N GD.gdG W tm hwf (fun x _ => wemitOfQconf boot d0 im nh GD x hq))
      (Nat.zero_add _)
  exact ⟨l, wlkStart boot d0 N GD.gdG, Sf, hrun, himg, hpst, hdv, logOfOfPfx _ _ hlog⟩

/-- THE THEOREM.  (R-2), at a residue that is a statement about the GRAPH. -/
theorem walkSupplyOfSites (boot : Nat → Pexv6) (d0 : Efab) (im : Image) (nh : Nat) (N : Nat) :
    (∀ GD : Gdexec,
       rvwmoMinusDepsConsistent GD → gdexecQconf boot d0 im nh GD →
       ∃ (W : Geid → Prop) (tm : Nat → Nat → List Nat), wsupply boot d0 GD.gdG W tm N) →
    walkSupply boot d0 im nh N := by
  intro hsup
  apply walkSupplyOfSteps'
  intro GD hcons hq
  obtain ⟨W, tm, hsup'⟩ := hsup GD hcons hq
  exact ⟨W, tm, fun St n hinv hn =>
    wlkStep'OfSupply boot d0 N GD.gdG W tm St n hcons.1 hsup' hinv hn⟩

end Weak
