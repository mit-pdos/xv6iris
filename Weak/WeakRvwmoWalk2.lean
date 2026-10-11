/-
Weak: **R-2's RESIDUE `walkSegData`: the parts the conformance bundle SUPPLIES, the OBSTRUCTION
that stopped the old shape, the repaired residue's capstones, and the generic walk RUN at `cyg`**
(a leaf).

Rocq: `iris/WeakRvwmoWalk2.v` @ xxvzwolszwmp.  (NOT `WeakRvwmoWalkb`, the Lean split part of
Rocq's `WeakRvwmoWalk.v`.)

## The Rocq header, in substance

Task: supply `WeakRvwmoProgress.walkSegData` from `WeakRvwmoSupply.gdexecQconf`.

  §1  THE EMISSION PER STATE, DELIVERED.  `gdexecQconf` hands out one `hartConf` emission of
      hart `x`'s WHOLE row; `hemitApp` splits it at the walk's current position `k0` and again
      after the exit write `kz`, leaving exactly the `hemit` the residue asks for, at the row
      fold `rowWs row k0`; `qconfSegData` puts it in the residue's own `pre ++ [store]` shape.
  §2  (moved to `WeakRvwmoWalk` §4.0c.)
  §3  THE RMW POLICY, POINTWISE, at an RMW-ALIGNED context (`wralign`, `cpolpOfAlign`, through
      `WeakRvwmoWalkb.wcpolpAt`).
  §4  THE OLD SHAPE'S OBSTRUCTION.  `WeakRvwmoWalk.wpolFlat` quantifies over EVERY context
      candidate while its classification is about `G`'s label AT THAT CANDIDATE'S OWN POSITION:
      `wpolPinsStore` (a `wpolFlat` carrying the exit store pins it to every context candidate's
      position), `wpolExitAtZero` (at the EMPTY candidate, position 0), and
      `walkSegDataPins`/`walkSegDataExitAtZero` (hence `WeakRvwmoProgress.walkSegDataFlat` pins
      every segment's exit write to its hart's row position 0).
  §5  THE REPAIRED RESIDUE: `walkSegDataOfQconf` supplies `walkSegData'` from the bundle plus
      one named per-state datum `wsegSupply`; `walkSupplyOfQconf` and the capstones
      `xv6RvwmoSafeModuloL2` (at `wsegSupply`) and `xv6RvwmoSafeModuloL2'` (at the per-GRAPH
      datum `WeakRvwmoWalkb.wsupply`).
  §6  NON-VACUITY at `WeakRvwmoCycWit.cyg`: the repaired site data hold at the second segment
      (exit store at row position 1, which §4 refuted under the old shape); the witness segment
      is served by the GENERIC engine (`cygStep0Generic`); and the whole walk runs out of
      `WeakRvwmoWalkb.wlkRun'` from the per-graph datum (`cygWsupply`, `cygWalk'`).

§7 (the `Print Assumptions` audit) and §8 (the ledger) are Rocq commands/comments.

## Deviations from Rocq

1. NAMES / VOCABULARY as `WeakRvwmoWalk` deviation 1 and `WeakRvwmoProgress` deviation 1
   (`Forall P l` ↦ `∀ x ∈ l, P x`; `take n (drop k l)` ↦ `(l.drop k).take n`;
   `default d o` ↦ `o.getD d`; `is_Some o` ↦ `o.isSome`; `Cand (gx_img G) []` ↦
   `⟨G.gxImg, []⟩`; the capstones take explicit `hlc GF` with `[MachGpreS hlc GF]
   [WeakGpreS GF]`, `D : CPU → List Register` with `hD : ∀ c, (D c).Nodup`, `wgdev σ0` ↦
   `efInit σ0.wgdev`, `reducible e σ` ↦ `Reducible (e, σ)`, `rtc erased_step` ↦ `-·->ₜₚ*`).
2. O2 / STAGE C.  (a) Both capstones carry the fetch-view premise
   `∀ ρ, rtc epfRun (epInit gen, σ0) ρ → efetchItvOk ρ.1 ρ.2` right after the WP package
   premises (as `WeakRvwmoWalk3.xv6RvwmoSafeModuloWalk`, `WeakRvwmoCapstone` Q4).
   (b) `walkSegData'` (`WeakRvwmoProgress` deviation 3b) asks for
   `WeakRvwmoCert2.esPin St.cstC.cdImg es`; `walkSegDataOfQconf` DERIVES it (no new premise:
   `wsegSupply` is Rocq's) from the bundle's `emFetchImg` clause through the Lean-only pinned
   twins `WeakRvwmoWalk2.qconfHemitPin`, `.hemitDropSub`, `.qconfHemitSegPin`,
   `.qconfSegTakePin` (each the Rocq lemma plus "the stretch's items are the row's items", so
   the pin survives the split); the Rocq-statement lemmas are corollaries of them.
   (c) `cpolpOfAlign` meets the tree's pinned pair policy (`WeakRvwmoCert3` deviation 4) through
   `WeakRvwmoWalkb.wcpolpAt` (its `rdsOk` premise is free at the empty taint, as in Rocq).
   (d) `cygWwitNd` is the pinned `wwitNd` (`∀ im`, `WeakRvwmoCert2.cblkPin im` blocks;
   `WeakRvwmoWalk` deviation 2), discharged by `WeakRvwmoCycWit.cyBlkSubstPin`; the poisoned
   arm of `cygWsiteSupply` is refuted at any image `im` (`WeakRvwmoWalkb` deviation 2).
   (e) `cygStep0Generic` passes `wlkSegOfCert`'s pin premise `WeakRvwmoCycWit.cyEmFetchImg`.
3. `wpolPinsStore`'s third arm is `cstepCls`'s POISONED arm (Lean `WeakRvwmoGlue2.cstepCls`
   has three arms; Rocq's destruct names them the same way): a store is not `latestReadLbl`.
4. `cygWQSeg1`/`cygWQSeg0`/`cygWsiteSupply` read `cyg`'s labels by `rfl` (`gxLbl` computes on
   the literal graph) instead of inverting `cygLbl`; `cygWsiteSupply` splits `n`/`p` with
   `omega` (Rocq `destruct`).

**Rocq → Lean name map.**  `qconf_hemit` `qconfHemit`, `hemit_drop` `hemitDrop`,
`qconf_hemit_seg` `qconfHemitSeg`, `seg_pre_nonwrite` `segPreNonwrite`, `qconf_seg_data`
`qconfSegData`, `wralign` `wralign`, `cpolp_of_align` `cpolpOfAlign`, `hemit_phart`
`hemitPhart`, `hemit_single_cblk` `hemitSingleCblk`, `wpol_pins_store` `wpolPinsStore`,
`empty_cand_consistent` `emptyCandConsistent`, `empty_cand_gcnt` `emptyCandGcnt`,
`wpol_exit_at_zero` `wpolExitAtZero`, `walk_seg_data_pins` `walkSegDataPins`,
`walk_seg_data_exit_at_zero` `walkSegDataExitAtZero`, `qrow_seg_lookup` `qrowSegLookup`,
`qconf_seg_take` `qconfSegTake`, `wseg_align` `wsegAlign`, `wseg_supply` `wsegSupply`,
`walk_seg_data_of_qconf` `walkSegDataOfQconf`, `walk_supply_of_qconf` `walkSupplyOfQconf`,
`xv6_rvwmo_safe_modulo_l2` `xv6RvwmoSafeModuloL2`, `xv6_rvwmo_safe_modulo_l2'`
`xv6RvwmoSafeModuloL2'`, `cyg_wQ_seg1` `cygWQSeg1`, `cyg_wnw_seg1` `cygWnwSeg1`, `cyg_wit00`
`cygWit00`, `cyg_ctx0` `cygCtx0`, `cyg_no_fhook` `cygNoFhook`, `cyg_wub` `cygWub`,
`cyg_W_poloc` `cygWPoloc`, `cyg_wwit_site00_graph` `cygWwitSite00Graph`, `cyg_wwit_nd`
`cygWwitNd`, `cyg_wwit_site00` `cygWwitSite00`, `cyg_wQ_seg0` `cygWQSeg0`,
`cyg_step0_generic` `cygStep0Generic`, `cyW` `cyW`, `cyW_ne` `cyWNe`, `cyg_hart` `cygHart`,
`cyg_w_at` `cygWAt`, `cyg_W_poloc'` `cygWPoloc'`, `cyg_wubA` `cygWubA`, `cyg_gwrow`
`cygGwrow`, `cyg_wsrc_le_store` `cygWsrcLeStore`, `cyg_wsite_supply` `cygWsiteSupply`,
`cyg_wsupply` `cygWsupply`, `cyg_walk'` `cygWalk'`.

**File-qualified names:** none of this file's Rocq names is in `notes/weak-port-dupnames.json`;
Lean-only (deviation 2b): `WeakRvwmoWalk2.qconfHemitPin`, `WeakRvwmoWalk2.hemitDropSub`,
`WeakRvwmoWalk2.qconfHemitSegPin`, `WeakRvwmoWalk2.qconfSegTakePin`.

**Dropped:** none (Rocq 46 declarations; Lean 50 = 46 + the 4 Lean-only).
-/
import Weak.WeakRvwmoProgress
import Weak.WeakRvwmoWalkb
import Weak.WeakRvwmoCycWit

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D
open Wlabel

/-- The parked-fence field, abbreviated (as in `WeakRvwmoCert2`). -/
local notation "Ofence" => Option (Bool × Bool × Bool × Bool)

/-! # 1. THE EMISSION PER STATE, FROM THE CONFORMANCE BUNDLE -/

/-! ## 1.1 The whole row's emission -/

theorem qconfHemit (boot : Nat → Pexv6) (d0 : Efab) (im : Image) (nh : Nat) (GD : Gdexec)
    (x : Nat) :
    gdexecQconf boot d0 im nh GD →
    ∃ (es : List Eitem) (pfin : Pexv6),
      hemit (fun _ => d0) 0 wsInit (qrow GD.gdG x) (boot x) es pfin := by
  intro hq
  obtain ⟨em, hem, _⟩ := qconfRows boot d0 im nh GD x hq
  exact ⟨em.emItems, em.emFin, hem⟩

/-- Lean-only (deviation 2b): … with its items pinned to the booted image. -/
theorem WeakRvwmoWalk2.qconfHemitPin (boot : Nat → Pexv6) (d0 : Efab) (im : Image) (nh : Nat)
    (GD : Gdexec) (x : Nat) :
    gdexecQconf boot d0 im nh GD →
    ∃ (es : List Eitem) (pfin : Pexv6),
      hemit (fun _ => d0) 0 wsInit (qrow GD.gdG x) (boot x) es pfin ∧
      WeakRvwmoCert2.esPin im es := by
  intro hq
  obtain ⟨em, hem, hfi⟩ := qconfRows boot d0 im nh GD x hq
  exact ⟨em.emItems, em.emFin, hem, hfi⟩

/-! ## 1.2 … SPLIT at the walk's current position -/

/-- Lean-only (deviation 2b): `hemitDrop`, keeping "the tail's items are the row's". -/
theorem WeakRvwmoWalk2.hemitDropSub (dv : Nat → Efab) (row : List Lbl) (k0 : Nat) (p : Pexv6)
    (es : List Eitem) (pfin : Pexv6) :
    hemit dv 0 wsInit row p es pfin →
    k0 ≤ row.length →
    ∃ (pm : Pexv6) (es2 : List Eitem),
      hemit dv k0 (rowWs row k0) (row.drop k0) pm es2 pfin ∧ ∀ e, e ∈ es2 → e ∈ es := by
  intro hem hk
  rw [← List.take_append_drop k0 row] at hem
  obtain ⟨pm, es1, es2, _, hem2, hes⟩ :=
    hemitApp dv 0 wsInit (row.take k0) (row.drop k0) p es pfin hem
  rw [List.length_take, Nat.min_eq_left hk, Nat.zero_add] at hem2
  exact ⟨pm, es2, hem2, fun e he => by rw [hes]; exact List.mem_append_right _ he⟩

theorem hemitDrop (dv : Nat → Efab) (row : List Lbl) (k0 : Nat) (p : Pexv6) (es : List Eitem)
    (pfin : Pexv6) :
    hemit dv 0 wsInit row p es pfin →
    k0 ≤ row.length →
    ∃ (pm : Pexv6) (es2 : List Eitem), hemit dv k0 (rowWs row k0) (row.drop k0) pm es2 pfin := by
  intro hem hk
  obtain ⟨pm, es2, hem2, _⟩ := WeakRvwmoWalk2.hemitDropSub dv row k0 p es pfin hem hk
  exact ⟨pm, es2, hem2⟩

/-- Lean-only (deviation 2b): `qconfHemitSeg`, with the stretch's items pinned. -/
theorem WeakRvwmoWalk2.qconfHemitSegPin (boot : Nat → Pexv6) (d0 : Efab) (im : Image)
    (nh : Nat) (GD : Gdexec) (x : Nat) (k0 len : Nat) :
    gdexecQconf boot d0 im nh GD →
    k0 ≤ (qrow GD.gdG x).length →
    ∃ (p1 p2 : Pexv6) (es : List Eitem),
      hemit (fun _ => d0) k0 (rowWs (qrow GD.gdG x) k0)
        (((qrow GD.gdG x).drop k0).take len) p1 es p2 ∧
      WeakRvwmoCert2.esPin im es := by
  intro hq hk
  obtain ⟨es, pfin, hem, hpin⟩ := WeakRvwmoWalk2.qconfHemitPin boot d0 im nh GD x hq
  obtain ⟨pm, es2, hem2, hsub⟩ :=
    WeakRvwmoWalk2.hemitDropSub (fun _ => d0) (qrow GD.gdG x) k0 (boot x) es pfin hem hk
  rw [← List.take_append_drop len ((qrow GD.gdG x).drop k0)] at hem2
  obtain ⟨pm2, es1', es2', hem3, _, hes⟩ :=
    hemitApp (fun _ => d0) k0 (rowWs (qrow GD.gdG x) k0) _ _ pm es2 pfin hem2
  refine ⟨pm, pm2, es1', hem3, fun l0 hl0 => hpin l0 ?_⟩
  obtain ⟨e, he, rfl⟩ := List.mem_map.1 hl0
  exact List.mem_map.2 ⟨e, hsub e (by rw [hes]; exact List.mem_append_left _ he), rfl⟩

/-- THE SEGMENT'S EMISSION.  `len` is the stretch's length. -/
theorem qconfHemitSeg (boot : Nat → Pexv6) (d0 : Efab) (im : Image) (nh : Nat) (GD : Gdexec)
    (x : Nat) (k0 len : Nat) :
    gdexecQconf boot d0 im nh GD →
    k0 ≤ (qrow GD.gdG x).length →
    ∃ (p1 p2 : Pexv6) (es : List Eitem),
      hemit (fun _ => d0) k0 (rowWs (qrow GD.gdG x) k0)
        (((qrow GD.gdG x).drop k0).take len) p1 es p2 := by
  intro hq hk
  obtain ⟨p1, p2, es, hem, _⟩ :=
    WeakRvwmoWalk2.qconfHemitSegPin boot d0 im nh GD x k0 len hq hk
  exact ⟨p1, p2, es, hem⟩

/-! ## 1.3 … in the residue's own `pre ++ [store]` shape -/

theorem segPreNonwrite (G : Gexec) (x : Nat) (k0 kz : Nat) :
    (∀ j lb, k0 ≤ j → j < kz → gxLbl G (x, j) = some lb → lbIsW lb = false) →
    ∀ lb ∈ ((qrow G x).drop k0).take (kz - k0), lbIsW lb = false := by
  intro hnw lb hlb
  obtain ⟨i, hi⟩ := elem_of_list_lookup.1 hlb
  obtain ⟨hi1, hlt⟩ := lookup_take_Some.1 hi
  rw [lookup_drop] at hi1
  exact hnw (k0 + i) lb (by omega) (by omega) (by rw [qrowLbl]; exact hi1)

/-- Lean-only (deviation 2b): `qconfSegTake`, with the stretch's items pinned. -/
theorem WeakRvwmoWalk2.qconfSegTakePin (boot : Nat → Pexv6) (d0 : Efab) (im : Image)
    (nh : Nat) (GD : Gdexec) (x : Nat) (k0 kz : Nat) (lb : Lbl) :
    gdexecQconf boot d0 im nh GD →
    k0 ≤ kz →
    gxLbl GD.gdG (x, kz) = some lb →
    ∃ (p1 p2 : Pexv6) (es : List Eitem),
      hemit (fun _ => d0) k0 (rowWs (qrow GD.gdG x) k0)
        (((qrow GD.gdG x).drop k0).take (kz - k0) ++ [lb]) p1 es p2 ∧
      WeakRvwmoCert2.esPin im es := by
  intro hq hle hkz
  have hkzr : (qrow GD.gdG x)[kz]? = some lb := by rw [← qrowLbl]; exact hkz
  have hk : k0 ≤ (qrow GD.gdG x).length := by
    have := lookup_lt_Some hkzr
    omega
  obtain ⟨p1, p2, es, hem, hpin⟩ :=
    WeakRvwmoWalk2.qconfHemitSegPin boot d0 im nh GD x k0 (kz + 1 - k0) hq hk
  rw [segSplitExit (qrow GD.gdG x) k0 kz lb hle hkzr] at hem
  exact ⟨p1, p2, es, hem, hpin⟩

/-- THE PACKAGE: the emission of the stretch `k0 .. kz`, in the shape the residue names it. -/
theorem qconfSegData (boot : Nat → Pexv6) (d0 : Efab) (im : Image) (nh : Nat) (GD : Gdexec)
    (x : Nat) (k0 kz : Nat) (lb : Lbl) :
    gdexecQconf boot d0 im nh GD →
    k0 ≤ kz →
    gxLbl GD.gdG (x, kz) = some lb →
    (∀ j lb0, k0 ≤ j → j < kz → gxLbl GD.gdG (x, j) = some lb0 → lbIsW lb0 = false) →
    ∃ (pre : List Lbl) (p1 p2 : Pexv6) (es : List Eitem),
      (∀ l ∈ pre, lbIsW l = false) ∧
      hemit (fun _ => d0) k0 (rowWs (qrow GD.gdG x) k0) (pre ++ [lb]) p1 es p2 := by
  intro hq hle hkz hnw
  obtain ⟨p1, p2, es, hem, _⟩ :=
    WeakRvwmoWalk2.qconfSegTakePin boot d0 im nh GD x k0 kz lb hq hle hkz
  exact ⟨_, p1, p2, es, segPreNonwrite GD.gdG x k0 kz hnw, hem⟩

/-! # 3. THE FUSED RMW's POLICY, POINTWISE -/

/-- `cpolp`, from the RMW alignment. -/
def wralign (G : Gexec) (n : Nat) (x : Nat) (Q : Lbl → Prop) : Prop :=
  ∀ (c0 : Cand) (lb : Lbl),
    srvwmoConsistent c0 → cpolCtx G (wwit G n) x c0 → Q lb →
    ¬ lbRmwfree lb →
    c0.cdImg = G.gxImg ∧ wlogPfx G n (cdLogEnd c0) ∧
    wrmwSite G n x (gcnt x c0.cdTr) lb

/-- (Deviation 2c: the tree's pinned pair policy.) -/
theorem cpolpOfAlign (G : Gexec) (n : Nat) (x : Nat) (cpu : CPU) (d0 : Efab) (Q : Lbl → Prop) :
    rvwmoMinusConsistent G →
    wralign G n x Q →
    cpolp x cpu d0 [] (fun _ : Nat => cpolCtx G (wwit G n) x)
      (wclsAt G (wwit G n) x) (fun _ : Nat => Q) := by
  intro hcons hal k c0 ws lb l1 l2 rds wrs m rs1 rs2 fn ib m' rs1' fn' ib' hc hctx hQ _ hag hblk
  have hrmw : ¬ lbRmwfree lb :=
    cblkpRmw cpu d0 ws lb l1 l2 rds wrs m rs1 fn ib m' rs1' fn' ib'
      (WeakRvwmoCert3.cblkpPinCblkp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hblk)
  obtain ⟨himg, hpfx, hsite⟩ := hal c0 lb hc hctx hQ hrmw
  have hnW : ¬ wwit G n (x, gcnt x c0.cdTr) := by
    rintro ⟨aq0, b0, ts0, vs0, hl0, _⟩
    rw [hsite.1] at hl0
    cases hl0
    exact hrmw trivial
  exact wcpolpAt G (wwit G n) n x cpu d0 c0 ws lb l1 l2 rds wrs m rs1 rs2 fn ib m' rs1' fn' ib'
    [] hcons himg hpfx hc hctx hnW hsite hag (fun _ _ => List.not_mem_nil) hblk

/-! # 4. THE OBSTRUCTION: `wpolFlat`'s UNIVERSAL CANDIDATE -/

/-! ## 4.0 Two shape facts about the emission -/

theorem hemitPhart (d0 : Efab) (k : Nat) (ws : Wstate) (row : List Lbl) (p : Pexv6)
    (es : List Eitem) (pfin : Pexv6) :
    hemit (fun _ => d0) k ws row p es pfin →
    ∀ (cpu : CPU) (m : SailM Unit) (rs : RegFile) (fn : Ofence) (ib : Ibch),
      p = .PHart cpu m rs fn ib →
      ∃ m' rs' fn' ib', pfin = .PHart cpu m' rs' fn' ib' := by
  intro hem
  induction hem with
  | HEnil k ws p =>
    intro cpu m rs fn ib hp
    exact ⟨m, rs, fn, ib, hp⟩
  | HEone k ws lb row p ls pa da l p' es pfin har _ hst _ ih =>
    intro cpu m rs fn ib hp
    obtain ⟨ma, rsa, fna, iba, rfl⟩ := admRunPhart true _ _ _ ls da har cpu m rs fn ib hp
    obtain ⟨m1, rs1, fn1, ib1, rfl⟩ := pstepEvPhart cpu ma rsa fna iba da l p' _ hst
    exact ih cpu m1 rs1 fn1 ib1 rfl
  | HEpair k ws lb row p ls1 pa da l1 pm dm ls2 pm2 dm2 l2 p' es pfin har1 _ hst1 har2 hst2 _
      ih =>
    intro cpu m rs fn ib hp
    obtain ⟨ma, rsa, fna, iba, rfl⟩ := admRunPhart true _ _ _ ls1 da har1 cpu m rs fn ib hp
    obtain ⟨mb, rsb, fnb, ibb, rfl⟩ := pstepEvPhart cpu ma rsa fna iba da l1 pm dm hst1
    obtain ⟨mc, rsc, fnc, ibc, rfl⟩ :=
      admRunPhart false _ _ dm ls2 dm2 har2 cpu mb rsb fnb ibb rfl
    obtain ⟨m1, rs1, fn1, ib1, rfl⟩ := pstepEvPhart cpu mc rsc fnc ibc dm2 l2 p' _ hst2
    exact ih cpu m1 rs1 fn1 ib1 rfl

/-- A ONE-LABEL emission IS a `cblk`. -/
theorem hemitSingleCblk (d0 : Efab) (k : Nat) (ws : Wstate) (lb : Lbl) (cpu : CPU)
    (m : SailM Unit) (rs : RegFile) (fn : Ofence) (ib : Ibch) (es : List Eitem) (pfin : Pexv6) :
    hemit (fun _ => d0) k ws [lb] (.PHart cpu m rs fn ib) es pfin →
    lbRmwfree lb →
    ∃ (l : Wlabel) (rds : List Nat) (wrs : List Register) (m' : SailM Unit) (rs' : RegFile)
      (fn' : Ofence) (ib' : Ibch),
      cblk cpu d0 ws lb l rds wrs m rs fn ib m' rs' fn' ib' := by
  intro hem hrmw
  cases hem with
  | HEone _ _ _ _ _ ls pa da l p' es' _ har hre hst _ =>
    obtain ⟨ma, rsa, fna, iba, rfl⟩ := admRunPhart true _ _ _ ls da har cpu m rs fn ib rfl
    obtain ⟨m1, rs1, fn1, ib1, rfl⟩ := pstepEvPhart cpu ma rsa fna iba da l p' _ hst
    obtain ⟨rds, wrs, hblk⟩ :=
      cblkIntro cpu d0 ws lb l ls _ da m rs fn ib m1 rs1 fn1 ib1 har hre hst
    exact ⟨l, rds, wrs, m1, rs1, fn1, ib1, hblk⟩
  | HEpair _ _ _ _ _ ls1 pa da l1 pm dm ls2 pm2 dm2 l2 p' es' _ _ hre _ _ _ _ =>
    obtain ⟨aq, rl, base, tvs, data, asrc1, asrc2, vsrc2, -, -, -, -, rfl⟩ := hre
    exact (show False from hrmw).elim

/-! ## 4.1 `wpolFlat` PINS the segment's exit store -/

theorem wpolPinsStore (G : Gexec) (n : Nat) (x : Nat) (cpu : CPU) (d0 : Efab) (T : List Nat)
    (Q : Lbl → Prop) (c0 : Cand) (ws : Wstate) (rl : Bool) (base : Int) (vs : List (BitVec 8))
    (kc : WmClass) (l : Wlabel) (rds : List Nat) (wrs : List Register) (m : SailM Unit)
    (rs1 rs2 : RegFile) (fn : Ofence) (ib : Ibch) (m' : SailM Unit) (rs1' : RegFile)
    (fn' : Ofence) (ib' : Ibch) :
    wpolFlat G (wwit G n) x cpu d0 T Q →
    srvwmoConsistent c0 →
    cpolCtx G (wwit G n) x c0 →
    Q (.LStore rl base vs kc) →
    ((candLastSt c0).msWs x).wRelp = ws.wRelp →
    dregAgree (fun nn => nn ∉ T) rs1 rs2 →
    cblk cpu d0 ws (.LStore rl base vs kc) l rds wrs m rs1 fn ib m' rs1' fn' ib' →
    gxLbl G (x, gcnt x c0.cdTr) = some (.LStore rl base vs kc) := by
  intro hpol hc hctx hQ hrelp hag hblk
  obtain ⟨lb', l', rds', wrs', rs2', -, -, hri, ⟨hcl, -⟩, -⟩ :=
    hpol c0 ws _ l rds wrs m rs1 rs2 fn ib m' rs1' fn' ib' hc hctx hQ hrelp hag hblk
  have hlb := lblReidxWStore rl base vs kc lb' hri
  subst hlb
  rcases hcl with ⟨-, hl⟩ | ⟨-, base0, n0, ts0, vs0, -, -, heq⟩ | ⟨-, ⟨base0, n0, heq⟩, -, -⟩
  · exact hl
  · unfold latestReadLbl at heq
    cases heq
  · unfold latestReadLbl at heq
    cases heq

/-! ## 4.2 … at the EMPTY candidate, whose position is 0 -/

theorem emptyCandConsistent (G : Gexec) : srvwmoConsistent ⟨G.gxImg, []⟩ :=
  srvwmoOfWf _ (candReachable _ (fun _ _ hs => absurd hs (by simp))).1

theorem emptyCandGcnt (G : Gexec) (x : Nat) : gcnt x (⟨G.gxImg, []⟩ : Cand).cdTr = 0 := rfl

theorem wpolExitAtZero (G : Gexec) (n : Nat) (x : Nat) (cpu : CPU) (d0 : Efab) (T : List Nat)
    (Q : Lbl → Prop) (ws : Wstate) (rl : Bool) (base : Int) (vs : List (BitVec 8))
    (kc : WmClass) (l : Wlabel) (rds : List Nat) (wrs : List Register) (m : SailM Unit)
    (rs1 rs2 : RegFile) (fn : Ofence) (ib : Ibch) (m' : SailM Unit) (rs1' : RegFile)
    (fn' : Ofence) (ib' : Ibch) :
    wpolFlat G (wwit G n) x cpu d0 T Q →
    Q (.LStore rl base vs kc) →
    ((candLastSt ⟨G.gxImg, []⟩).msWs x).wRelp = ws.wRelp →
    dregAgree (fun nn => nn ∉ T) rs1 rs2 →
    cblk cpu d0 ws (.LStore rl base vs kc) l rds wrs m rs1 fn ib m' rs1' fn' ib' →
    gxLbl G (x, 0) = some (.LStore rl base vs kc) := by
  intro hpol hQ hrelp hag hblk
  show gxLbl G (x, gcnt x (⟨G.gxImg, []⟩ : Cand).cdTr) = _
  exact wpolPinsStore G n x cpu d0 T Q _ ws rl base vs kc l rds wrs m rs1 rs2 fn ib m' rs1' fn'
    ib' hpol (emptyCandConsistent G) (cpolCtxEmpty G (wwit G n) x) hQ hrelp hag hblk

/-! ## 4.3 … hence `walkSegDataFlat` itself pins the exit write -/

theorem walkSegDataPins (boot : Nat → Pexv6) (d0 : Efab) (N : Nat) (G : Gexec) :
    walkSegDataFlat boot d0 N G →
    ∀ (St : CycState) (n : Nat),
      wlkInv boot d0 N G St n → n < (gwrites G).length →
      ∃ (x : Nat) (rl : Bool) (base : Int) (vs : List (BitVec 8)) (kc : WmClass) (ws : Wstate)
        (w : Geid),
        gwriteAt G (n + 1) = some w ∧
        WeakRvwmoKillArms.gmsg G w = some ⟨base, vs, some x, kc⟩ ∧
        wrowInLog' G x n ∧
        ∀ c0 : Cand,
          srvwmoConsistent c0 → cpolCtx G (wwit G n) x c0 →
          ((candLastSt c0).msWs x).wRelp = ws.wRelp →
          gxLbl G (x, gcnt x c0.cdTr) = some (.LStore rl base vs kc) := by
  intro hdata St n hinv hn
  obtain ⟨x, cpu, T, Q, k0, ws0, pre, rl, base, vs, kc, es, pfin, m0, rs10, rs20, fn0, ib0, w,
    hw, hm, -, hem, hQ, -, -, -, -, hrow, hpol, -⟩ := hdata St n hinv hn
  obtain ⟨pm, es1, es2, hem1, hem2, -⟩ :=
    hemitApp (fun _ => d0) k0 ws0 pre [.LStore rl base vs kc] _ es pfin hem
  obtain ⟨m1, rs11, fn1, ib1, rfl⟩ :=
    hemitPhart d0 k0 ws0 pre _ es1 pm hem1 cpu m0 rs10 fn0 ib0 rfl
  obtain ⟨l, rds, wrs, m', rs', fn', ib', hblk⟩ :=
    hemitSingleCblk d0 (k0 + pre.length) (rowWsAux k0 ws0 pre) _ cpu m1 rs11 fn1 ib1 es2 pfin
      hem2 trivial
  have hQ2 : Q (.LStore rl base vs kc) :=
    hQ _ (List.mem_append_right _ (List.mem_singleton_self _))
  refine ⟨x, rl, base, vs, kc, rowWsAux k0 ws0 pre, w, hw, hm, hrow, ?_⟩
  intro c0 hc hctx0 hrelp0
  exact wpolPinsStore G n x cpu d0 T Q c0 (rowWsAux k0 ws0 pre) rl base vs kc l rds wrs m1 rs11
    rs11 fn1 ib1 m' rs' fn' ib' hpol hc hctx0 hQ2 hrelp0 (dregAgreeRefl _ _) hblk

/-- THE FINDING, at its sharpest. -/
theorem walkSegDataExitAtZero (boot : Nat → Pexv6) (d0 : Efab) (N : Nat) (G : Gexec) :
    walkSegDataFlat boot d0 N G →
    ∀ (St : CycState) (n : Nat),
      wlkInv boot d0 N G St n → n < (gwrites G).length →
      ∃ (x : Nat) (rl : Bool) (base : Int) (vs : List (BitVec 8)) (kc : WmClass) (ws : Wstate)
        (w : Geid),
        gwriteAt G (n + 1) = some w ∧
        WeakRvwmoKillArms.gmsg G w = some ⟨base, vs, some x, kc⟩ ∧
        (((candLastSt ⟨G.gxImg, []⟩).msWs x).wRelp = ws.wRelp →
         gxLbl G (x, 0) = some (.LStore rl base vs kc)) := by
  intro hdata St n hinv hn
  obtain ⟨x, rl, base, vs, kc, ws, w, hw, hm, _, hpin⟩ :=
    walkSegDataPins boot d0 N G hdata St n hinv hn
  refine ⟨x, rl, base, vs, kc, ws, w, hw, hm, fun hrelp0 => ?_⟩
  show gxLbl G (x, gcnt x (⟨G.gxImg, []⟩ : Cand).cdTr) = _
  exact hpin _ (emptyCandConsistent G) (cpolCtxEmpty G (wwit G n) x) hrelp0

/-! ## 4.4 THE REPAIR, LANDED -/

/-- The site hypothesis is READ OFF the graph at the walk's own segment. -/
theorem qrowSegLookup (G : Gexec) (x : Nat) (k0 len i : Nat) (lb : Lbl) :
    (((qrow G x).drop k0).take len)[i]? = some lb → gxLbl G (x, k0 + i) = some lb := by
  intro hi
  have h := (lookup_take_Some.1 hi).1
  rw [lookup_drop] at h
  rw [qrowLbl]
  exact h

/-! # 5. THE REPAIRED RESIDUE, AND WHAT THE CONFORMANCE BUNDLE SUPPLIES -/

/-! ## 5.1 The emission of the stretch, with its PREFIX FIXED -/

theorem qconfSegTake (boot : Nat → Pexv6) (d0 : Efab) (im : Image) (nh : Nat) (GD : Gdexec)
    (x : Nat) (k0 kz : Nat) (lb : Lbl) :
    gdexecQconf boot d0 im nh GD →
    k0 ≤ kz →
    gxLbl GD.gdG (x, kz) = some lb →
    ∃ (p1 p2 : Pexv6) (es : List Eitem),
      hemit (fun _ => d0) k0 (rowWs (qrow GD.gdG x) k0)
        (((qrow GD.gdG x).drop k0).take (kz - k0) ++ [lb]) p1 es p2 := by
  intro hq hle hkz
  obtain ⟨p1, p2, es, hem, _⟩ :=
    WeakRvwmoWalk2.qconfSegTakePin boot d0 im nh GD x k0 kz lb hq hle hkz
  exact ⟨p1, p2, es, hem⟩

/-! ## 5.2 The per-state datum the bundle does NOT supply -/

/-- The walk state's process for `x` IS the emission's own starting process. -/
def wsegAlign (d0 : Efab) (G : Gexec) (T : List Nat) (St : CycState) (x : Nat) (k0 : Nat)
    (stretch : List Lbl) : Prop :=
  ∀ (p1 : Pexv6) (es : List Eitem) (p2 : Pexv6),
    hemit (fun _ => d0) k0 (rowWs (qrow G x) k0) stretch p1 es p2 →
    ∃ (cpu : CPU) (m0 : SailM Unit) (rs10 rs20 : RegFile) (fn0 : Ofence) (ib0 : Ibch),
      p1 = .PHart cpu m0 rs10 fn0 ib0 ∧
      (St.cstPst (cdEnd St.cstC))[x]? = some (.PHart cpu m0 rs20 fn0 ib0) ∧
      dregAgree (fun nn => nn ∉ T) rs10 rs20 ∧
      ((candLastSt St.cstC).msWs x).wRelp = (rowWs (qrow G x) k0).wRelp

def wsegSupply (boot : Nat → Pexv6) (d0 : Efab) (N : Nat) (GD : Gdexec) : Prop :=
  ∀ St n, wlkInv boot d0 N GD.gdG St n →
    n < (gwrites GD.gdG).length →
  ∃ (x : Nat) (k0 kz : Nat) (T : List Nat) (Nd : Nat → CPU → SailM Unit → Prop),
    -- WHICH WRITE: `G`'s `(n+1)`-st, and where the hart stands now
    gwriteAt GD.gdG (n + 1) = some (x, kz) ∧
    k0 ≤ kz ∧
    gcnt x St.cstC.cdTr = k0 ∧
    -- THE SITE FACTS over the covered positions
    (∀ k lb, k0 ≤ k → k < kz → gxLbl GD.gdG (x, k) = some lb → lbIsW lb = false) ∧
    (∀ k lb, k0 ≤ k → k ≤ kz → gxLbl GD.gdG (x, k) = some lb → lbRmwfree lb) ∧
    (∀ k, k0 ≤ k → k ≤ kz → wwit GD.gdG n (x, k) → wwitSite GD.gdG d0 T Nd n x k) ∧
    -- the two side conditions the `csync` iteration names, and the device-quiet emission
    wrdsFree d0 T ∧
    (∀ cpu : CPU, wndOk cpu d0 (wQ GD.gdG d0 T Nd n x k0 kz) Nd) ∧
    (∀ (cpu : CPU) (m0 : SailM Unit) (rs10 : RegFile) (fn0 : Ofence) (ib0 : Ibch)
       (es : List Eitem) (pfin : Pexv6),
       hemit (fun _ => d0) k0 (rowWs (qrow GD.gdG x) k0)
         (((qrow GD.gdG x).drop k0).take (kz - k0) ++
          [(gxLbl GD.gdG (x, kz)).getD (.LFence false false false false)])
         (.PHart cpu m0 rs10 fn0 ib0) es pfin →
       (∀ kd ba bs, LDev kd ba bs ∉ es.map Prod.fst) ∧ Nd k0 cpu m0) ∧
    -- THE WITNESS SET's side conditions
    cpolCtx GD.gdG (wwit GD.gdG n) x St.cstC ∧
    WPolocClosed GD.gdG (wwit GD.gdG n) ∧
    wub GD.gdG (wwit GD.gdG n) x ∧
    -- THE STATE IDENTIFICATION
    wsegAlign d0 GD.gdG T St x k0
      (((qrow GD.gdG x).drop k0).take (kz - k0) ++
       [(gxLbl GD.gdG (x, kz)).getD (.LFence false false false false)])

/-! ## 5.3 … and then the residue IS supplied -/

/-- (Deviation 2b: `walkSegData'`'s pin conjunct is derived.) -/
theorem walkSegDataOfQconf (boot : Nat → Pexv6) (d0 : Efab) (im : Image) (nh N : Nat)
    (GD : Gdexec) :
    rvwmoMinusDepsConsistent GD →
    gdexecQconf boot d0 im nh GD →
    wsegSupply boot d0 N GD →
    walkSegData' boot d0 N GD.gdG := by
  intro hcons hq hsup St n hinv hn
  have hwf : gwf GD.gdG := hcons.1.1
  have hnd : GD.gdG.gxGmo.Nodup := hwf.1
  obtain ⟨x, k0, kz, T, Nd, hat, hle, hgc, hnwr, hrmw, hwitd, hrdsf, hndok, hemd, hctx, hpc,
    hub, hal⟩ := hsup St n hinv hn
  obtain ⟨hmem, hwix⟩ := gwriteAtInv GD.gdG (n + 1) (x, kz) hnd hat
  have hisw : gisW GD.gdG (x, kz) = true := ((gwritesElemOf GD.gdG _).1 hmem).2
  cases hlb : gxLbl GD.gdG (x, kz) with
  | none => simp [gisW, hlb] at hisw
  | some lb =>
  have hlbw : lbIsW lb = true := by simpa [gisW, hlb] using hisw
  have hlbr : lbRmwfree lb := hrmw kz lb hle (Nat.le_refl _) hlb
  rw [hlb, Option.getD_some] at hemd hal
  cases lb with
  | LLoad => exact absurd hlbw (by simp [lbIsW])
  | LFence => exact absurd hlbw (by simp [lbIsW])
  | LRmw => exact (show False from hlbr).elim
  | LIo => exact absurd hlbw (by simp [lbIsW])
  | LStore rl base vs kc =>
  obtain ⟨p1, p2, es, hem, hpin⟩ :=
    WeakRvwmoWalk2.qconfSegTakePin boot d0 im nh GD x k0 kz _ hq hle hlb
  obtain ⟨cpu, m0, rs10, rs20, fn0, ib0, rfl, hp, hag, hrelp⟩ := hal p1 es p2 hem
  have hkzr : (qrow GD.gdG x)[kz]? = some (.LStore rl base vs kc) := by
    rw [← qrowLbl]; exact hlb
  have hlenpre : (((qrow GD.gdG x).drop k0).take (kz - k0)).length = kz - k0 := by
    rw [List.length_take, List.length_drop]
    have := lookup_lt_Some hkzr
    omega
  have hkz : k0 + (((qrow GD.gdG x).drop k0).take (kz - k0)).length = kz := by omega
  obtain ⟨hdev, hnd0⟩ := hemd cpu m0 rs10 fn0 ib0 es p2 hem
  refine ⟨x, cpu, k0, rowWs (qrow GD.gdG x) k0, ((qrow GD.gdG x).drop k0).take (kz - k0), rl,
    base, vs, kc, es, p2, m0, rs10, rs20, fn0, ib0, (x, kz), T, Nd, hat, ?_,
    segPreNonwrite GD.gdG x k0 kz hnwr, hem, hdev, ?_, ?_, ?_, hp, hag, hrelp, hrdsf, ?_, hnd0,
    hpc, hub⟩
  · unfold WeakRvwmoKillArms.gmsg
    rw [hlb]
    rfl
  · intro l0 hl0
    rw [hinv.2.1, gdexecQconfImg boot d0 im nh GD hq]
    exact hpin l0 hl0
  · rw [hkz]
    intro i lb0 hi
    by_cases hlt : i < (((qrow GD.gdG x).drop k0).take (kz - k0)).length
    · rw [lookup_app_l hlt] at hi
      have hl0 := qrowSegLookup GD.gdG x k0 (kz - k0) i lb0 hi
      have hnw0 : lbIsW lb0 = false := hnwr (k0 + i) lb0 (by omega) (by omega) hl0
      refine ⟨by omega, by omega,
        ⟨hl0, fun h => (by rw [hnw0] at h; cases h), hrmw (k0 + i) lb0 (by omega) (by omega) hl0,
          hwitd (k0 + i) (by omega) (by omega)⟩, ?_⟩
      rw [hnw0]
      constructor
      · intro h; cases h
      · intro h; omega
    · rw [lookup_app_r (by omega)] at hi
      have hi0 : i - (((qrow GD.gdG x).drop k0).take (kz - k0)).length = 0 := by
        have := lookup_lt_Some hi
        rw [List.length_singleton] at this
        omega
      have hik : k0 + i = kz := by omega
      rw [hi0] at hi
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
      subst hi
      rw [hik]
      exact ⟨hle, Nat.le_refl _, ⟨hlb, fun _ => hwix, trivial, hwitd kz hle (Nat.le_refl _)⟩,
        ⟨fun _ => rfl, fun _ => rfl⟩⟩
  · exact ⟨hctx, hgc, by rw [WeakRvwmoWalk.wlognLe n _ k0 (by omega)]; exact hinv.2.2.2.2⟩
  · rw [hkz]
    exact hndok cpu

/-! ## 5.4 THE WALK, AND THE CAPSTONE AT (R-1) PLUS `wsegSupply` -/

theorem walkSupplyOfQconf (boot : Nat → Pexv6) (d0 : Efab) (im : Image) (nh N : Nat) :
    (∀ GD : Gdexec,
       rvwmoMinusDepsConsistent GD → gdexecQconf boot d0 im nh GD →
       wsegSupply boot d0 N GD) →
    walkSupply boot d0 im nh N :=
  fun hsup => walkSupplyOfWp' boot d0 im nh N
    (fun GD hcons hq => walkSegDataOfQconf boot d0 im nh N GD hcons hq (hsup GD hcons hq))

section capstone

open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode
open Language.Notation PrimStep

/-- Rocq `xv6_rvwmo_safe_modulo_l2` (deviations 1, 2a). -/
theorem xv6RvwmoSafeModuloL2 (hlc : HasLC) (GF : BundledGFunctors) [MachGpreS hlc GF]
    [WeakGpreS GF]
    (gen : Nat) (σ0 : WGState) (D : CPU → List Register) (hD : ∀ c, (D c).Nodup)
    (Nm : Int → Int → Namespace) (P : Int → Int → Prop) :
    freshEra gen σ0 →
    wpPackage hlc GF gen σ0 D →
    (∀ a base, P a base → wpPackageProt hlc GF gen σ0 D (Nm a base) a base) →
    -- THE FETCH-VIEW PREMISE (deviation 2a)
    (∀ ρ, rtc epfRun (epInit gen, σ0) ρ → efetchItvOk ρ.1 ρ.2) →
    -- (R-1)
    l2Claim (xboot σ0) (efInit σ0.wgdev) (imgZ σ0.wgimg) (xN σ0) P (badRun gen σ0) →
    -- (R-2), reduced to the per-state SITE/STATE datum
    (∀ GD : Gdexec,
       rvwmoMinusDepsConsistent GD →
       gdexecQconf (xboot σ0) (efInit σ0.wgdev) (imgZ σ0.wgimg) (xN σ0) GD →
       wsegSupply (xboot σ0) (efInit σ0.wgdev) (xN σ0) GD) →
    ∀ GD : Gdexec,
      rvwmoMinusDepsConsistent GD →
      gdexecQconf (xboot σ0) (efInit σ0.wgdev) (imgZ σ0.wgimg) (xN σ0) GD →
      (∀ x, ¬ tc (racyD GD) x x) ∧
      (∃ (c : Cand) (pst : Nat → List Pexv6) (P' : Epool) (σ' : WGState),
        srvwmoConsistent c ∧
        c.cdImg = imgZ σ0.wgimg ∧
        pst 0 = epsInit σ0 ∧
        execProgOk' pstepEv pclsEv pst (fun _ => efInit σ0.wgdev) (candExec c) ∧
        rtc epfRun (epInit gen, σ0) (P', σ') ∧
        σ'.wglog = cdLog c c.cdTr.length ∧
        (ecfgOf P' σ').pcAgs.map Wpagent.paSt = pst c.cdTr.length) ∧
      (∀ ρ, rtc epfRun (epInit gen, σ0) ρ → ¬ violationHart clsOf pubOf nDisk (ecfgOf ρ.1 ρ.2)) ∧
      (∀ (t2 : List EExpr) (σ2 : WGState) (e2 : EExpr),
        (epowerFork gen, σ0) -·->ₜₚ* (t2, σ2) → e2 ∈ t2 → Reducible (e2, σ2)) :=
  fun hfr hwp hwpp hcov hl2 hsup =>
    xv6RvwmoSafeModulo hlc GF gen σ0 D hD Nm P hfr hwp hwpp hcov hl2
      (walkSupplyOfQconf _ _ _ _ _ hsup)

/-! ## 5.5 THE CAPSTONE AT THE CHAINED WALK — (R-2) AS A STATEMENT ABOUT THE GRAPH -/

/-- Rocq `xv6_rvwmo_safe_modulo_l2'` (deviations 1, 2a). -/
theorem xv6RvwmoSafeModuloL2' (hlc : HasLC) (GF : BundledGFunctors) [MachGpreS hlc GF]
    [WeakGpreS GF]
    (gen : Nat) (σ0 : WGState) (D : CPU → List Register) (hD : ∀ c, (D c).Nodup)
    (Nm : Int → Int → Namespace) (P : Int → Int → Prop) :
    freshEra gen σ0 →
    wpPackage hlc GF gen σ0 D →
    (∀ a base, P a base → wpPackageProt hlc GF gen σ0 D (Nm a base) a base) →
    -- THE FETCH-VIEW PREMISE (deviation 2a)
    (∀ ρ, rtc epfRun (epInit gen, σ0) ρ → efetchItvOk ρ.1 ρ.2) →
    -- (R-1)
    l2Claim (xboot σ0) (efInit σ0.wgdev) (imgZ σ0.wgimg) (xN σ0) P (badRun gen σ0) →
    -- (R-2), reduced to a per-GRAPH datum
    (∀ GD : Gdexec,
       rvwmoMinusDepsConsistent GD →
       gdexecQconf (xboot σ0) (efInit σ0.wgdev) (imgZ σ0.wgimg) (xN σ0) GD →
       ∃ (W : Geid → Prop) (tm : Nat → Nat → List Nat),
         wsupply (xboot σ0) (efInit σ0.wgdev) GD.gdG W tm (xN σ0)) →
    ∀ GD : Gdexec,
      rvwmoMinusDepsConsistent GD →
      gdexecQconf (xboot σ0) (efInit σ0.wgdev) (imgZ σ0.wgimg) (xN σ0) GD →
      (∀ x, ¬ tc (racyD GD) x x) ∧
      (∃ (c : Cand) (pst : Nat → List Pexv6) (P' : Epool) (σ' : WGState),
        srvwmoConsistent c ∧
        c.cdImg = imgZ σ0.wgimg ∧
        pst 0 = epsInit σ0 ∧
        execProgOk' pstepEv pclsEv pst (fun _ => efInit σ0.wgdev) (candExec c) ∧
        rtc epfRun (epInit gen, σ0) (P', σ') ∧
        σ'.wglog = cdLog c c.cdTr.length ∧
        (ecfgOf P' σ').pcAgs.map Wpagent.paSt = pst c.cdTr.length) ∧
      (∀ ρ, rtc epfRun (epInit gen, σ0) ρ → ¬ violationHart clsOf pubOf nDisk (ecfgOf ρ.1 ρ.2)) ∧
      (∀ (t2 : List EExpr) (σ2 : WGState) (e2 : EExpr),
        (epowerFork gen, σ0) -·->ₜₚ* (t2, σ2) → e2 ∈ t2 → Reducible (e2, σ2)) :=
  fun hfr hwp hwpp hcov hl2 hsup =>
    xv6RvwmoSafeModulo hlc GF gen σ0 D hD Nm P hfr hwp hwpp hcov hl2
      (walkSupplyOfSites _ _ _ _ _ hsup)

end capstone

/-! # 6. NON-VACUITY, AT `cyg` -/

/-! ## 6.1 The repaired site data, at `cyg`'s second segment -/

theorem cygWQSeg1 (d0 : Efab) (T : List Nat) (Nd : Nat → CPU → SailM Unit → Prop) (i : Nat)
    (lb : Lbl) :
    (cyRow cyB cyA cyTs1)[i]? = some lb →
    wQ cyg d0 T Nd 1 1 0 1 (0 + i) lb := by
  intro hi
  obtain rfl | rfl | hi2 : i = 0 ∨ i = 1 ∨ 2 ≤ i := by omega
  · -- the TRUE read: its source is write 1, which the log holds
    simp only [cyRow, List.getElem?_cons_zero, Option.some.injEq] at hi
    subst hi
    have h0 : gxLbl cyg (1, 0 + 0) = some (.LLoad false (paZ cyB) cyTs1 cyBytes) := rfl
    refine ⟨by omega, by omega, ⟨h0, fun h => absurd h (by simp [lbIsW]), trivial, ?_⟩,
      ⟨fun h => absurd h (by simp [lbIsW]), fun h => absurd h (by omega)⟩⟩
    rintro ⟨aq, base, ts, vs, hl, j, t, hj, hlt⟩
    rw [h0] at hl
    cases hl
    have ht := elem_of_list_lookup_2 hj
    simp [cyTs1] at ht
    omega
  · -- THE EXIT STORE, AT ROW POSITION 1 — not 0
    simp only [cyRow, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hi
    subst hi
    have h0 : gxLbl cyg (1, 0 + 1) = some (.LStore false (paZ cyA) cyBytes .WCplain) := rfl
    refine ⟨by omega, by omega, ⟨h0, fun _ => cygWix2, trivial, ?_⟩,
      ⟨fun _ => rfl, fun _ => rfl⟩⟩
    rintro ⟨aq, base, ts, vs, hl, -⟩
    rw [h0] at hl
    cases hl
  · exact absurd hi (by rw [List.getElem?_eq_none (by simp [cyRow]; omega)]; simp)

/-- … and the segment-restricted (W-4) at it. -/
theorem cygWnwSeg1 : wnwSeg cyg 1 1 0 1 := by
  rintro k - - ⟨aq, base, ts, vs, hl, -⟩
  rcases cygLbl _ _ hl with ⟨he, h⟩ | ⟨he, h⟩ | ⟨he, h⟩ | ⟨he, h⟩ <;>
    first
    | (simp at he; done)
    | cases h

/-! ## 6.2 THE OBSTRUCTION, GONE — `cyg`'s WITNESS SEGMENT, SERVED BY THE GENERIC ENGINE -/

/-- Hart 0's load IS a witness at log length 0. -/
theorem cygWit00 : wwit cyg 0 (0, 0) :=
  ⟨false, zA, cyTs2, cyBytes, rfl, 0, 2, rfl, by omega⟩

/-- … and the EMPTY candidate DOES carry the certification context for hart 0. -/
theorem cygCtx0 : cpolCtx cyg (wwit cyg 0) 0 cwC0 := cpolCtxEmpty cyg (wwit cyg 0) 0

/-- `cyg` carries no fence at all. -/
theorem cygNoFhook (r : Geid) (k : Nat) (pb : Bool) : ¬ fhook cyg r k pb := by
  rintro ⟨kf, pr, pw, sr, sw, -, -, hl, -⟩
  rcases cygLbl _ _ hl with ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ <;> cases h

theorem cygWub (n : Nat) (x : Nat) : wub cyg (wwit cyg n) x := by
  intro c0 lb' ev' _ p s _ _ _ hfh
  exact absurd hfh (cygNoFhook _ _ _)

/-- (W-a) at `cyg`. -/
theorem cygWPoloc (n : Nat) : WPolocClosed cyg (wwit cyg n) := by
  rintro e1 e2 a - hpo - - ⟨l, hl, hr⟩
  rcases cygLbl e2 l hl with ⟨rfl, -⟩ | ⟨-, rfl⟩ | ⟨rfl, -⟩ | ⟨-, rfl⟩
  · exact absurd hpo.2.1 (Nat.not_lt_zero _)
  · exact absurd hr (by simp [lbIsR])
  · exact absurd hpo.2.1 (Nat.not_lt_zero _)
  · exact absurd hr (by simp [lbIsR])

/-- THE WITNESS SITE DATUM at hart 0's load, GRAPH HALF. -/
theorem cygWwitSite00Graph :
    ∀ (c : Cand) (aq : Bool) (base : Int) (ts : List Nat) (vs : List (BitVec 8)),
      c.cdImg = cyg.gxImg →
      wlogPfx cyg 0 (cdLogEnd c) →
      gxLbl cyg (0, 0) = some (.LLoad aq base ts vs) →
      aq = false ∧ latestBytesOk c base ts.length := by
  intro c aq base ts vs himg hpfx hl
  have hlog : cdLogEnd c = [] := List.eq_nil_of_length_eq_zero hpfx.1
  have h0 : gxLbl cyg (0, 0) = some (.LLoad false zA cyTs2 cyBytes) := rfl
  rw [h0] at hl
  cases hl
  refine ⟨rfl, ?_⟩
  have hb := cwBytes0
  unfold latestBytesOk at hb ⊢
  rw [himg, hlog]
  exact hb

/-- … AND THE MACHINE HALF (deviation 2d: on pinned blocks, at any image). -/
theorem cygWwitNd (cpu0 cpu1 : CPU) (rs0 rs1 : RegFile) (d0 : Efab) :
    wwitNd d0 [] (wnd d0 cyg (cyBoot cpu0 cpu1 rs0 rs1) 0) 0 := by
  intro im cpu ws aq base ts vs l rds wrs m rs fn ib m' rs' fn' ib' tvs2 hnd hblk hlen
  have hm : m = cyM cyA cyB := by
    refine wndFix d0 cyg (cyBoot cpu0 cpu1 rs0 rs1) 0 (fun mm => mm = cyM cyA cyB) cpu m ?_ ?_
      hnd
    · intro m0 rs00 fn00 ib00 hb
      change Pexv6.PHart cpu0 (cyM cyA cyB) rs0 none ibNone = _ at hb
      cases hb
      rfl
    · intro m1 m2 rs1' rs2' fn1 fn2 ib1 ib2 ls rds' wrs' ann hm1 hadm hrun
      exact cyMAdmFix cyA cyB cpu ls rds' wrs' ann m1 rs1' fn1 ib1 d0 m2 rs2' fn2 ib2 d0 cyARam
        hrun hadm hm1
  subst hm
  obtain ⟨l2, rds2, wrs2, hblk2⟩ :=
    WeakRvwmoCycWit.cyBlkSubstPin im cyA cyB cpu d0 ws aq base ts vs l rds wrs rs fn ib m' rs'
      fn' ib' tvs2 cyARam hlen hblk
  exact ⟨l2, rds2, wrs2, m', hblk2, .inl ⟨rfl, rfl, rfl, dregAgreeRefl _ _⟩⟩

theorem cygWwitSite00 (cpu0 cpu1 : CPU) (rs0 rs1 : RegFile) (d0 : Efab) :
    wwitSite cyg d0 [] (wnd d0 cyg (cyBoot cpu0 cpu1 rs0 rs1) 0) 0 0 0 :=
  ⟨cygWwitSite00Graph, cygWwitNd cpu0 cpu1 rs0 rs1 d0⟩

/-- THE SITE DATA at `cyg`'s FIRST segment: row position 0 is a WITNESS. -/
theorem cygWQSeg0 (cpu0 cpu1 : CPU) (rs0 rs1 : RegFile) (d0 : Efab) (i : Nat) (lb : Lbl) :
    (cyRow cyA cyB cyTs2)[i]? = some lb →
    wQ cyg d0 [] (wnd d0 cyg (cyBoot cpu0 cpu1 rs0 rs1) 0) 0 0 0 1 (0 + i) lb := by
  intro hi
  obtain rfl | rfl | hi2 : i = 0 ∨ i = 1 ∨ 2 ≤ i := by omega
  · -- THE WITNESS READ, at row position 0
    simp only [cyRow, List.getElem?_cons_zero, Option.some.injEq] at hi
    subst hi
    exact ⟨by omega, by omega,
      ⟨rfl, fun h => absurd h (by simp [lbIsW]), trivial,
        fun _ => cygWwitSite00 cpu0 cpu1 rs0 rs1 d0⟩,
      ⟨fun h => absurd h (by simp [lbIsW]), fun h => absurd h (by omega)⟩⟩
  · -- the exit store, at row position 1
    simp only [cyRow, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hi
    subst hi
    have h0 : gxLbl cyg (0, 0 + 1) = some (.LStore false (paZ cyB) cyBytes .WCplain) := rfl
    refine ⟨by omega, by omega, ⟨h0, fun _ => cygWix1, trivial, ?_⟩,
      ⟨fun _ => rfl, fun _ => rfl⟩⟩
    rintro ⟨aq, base, ts, vs, hl, -⟩
    rw [h0] at hl
    cases hl
  · exact absurd hi (by rw [List.getElem?_eq_none (by simp [cyRow]; omega)]; simp)

/-- THE ACCEPTANCE TEST: one step of the walk at `cyg`'s FIRST write, by the GENERIC engine. -/
theorem cygStep0Generic (cpu0 cpu1 : CPU) (rs0 rs1 : RegFile) (d0 : Efab) :
    wlkStep cyg d0 (cwS0 cpu0 cpu1 rs0 rs1 d0) 0 := by
  obtain ⟨St', tradd, hstep, -, himg, hpst, hdv⟩ :=
    wlkSegOfCert cyg 0 0 cpu0 d0 [] (wnd d0 cyg (cyBoot cpu0 cpu1 rs0 rs1) 0) 0 1 wsInit
      (cyRow cyA cyB cyTs2) (cyEm cyA cyB cyTs2 cpu0 rs0).emItems
      (cyEm cyA cyB cyTs2 cpu0 rs0).emFin (cyM cyA cyB) rs0 none ibNone
      (cwS0 cpu0 cpu1 rs0 rs1 d0) (cyM cyA cyB) rs0 none ibNone
      cygConsistent (cygWPoloc 0) (cygWub 0 0) (wrdsFreeNil d0)
      (wndWndOk cpu0 d0 cyg (cyBoot cpu0 cpu1 rs0 rs1) 0
        (wQ cyg d0 [] (wnd d0 cyg (cyBoot cpu0 cpu1 rs0 rs1) 0) 0 0 0 1)
        (fun k lb h => wQLbl cyg d0 [] (wnd d0 cyg (cyBoot cpu0 cpu1 rs0 rs1) 0) 0 0 0 1 k lb h))
      (cyHartConf 0 cyA cyB cyTs2 cpu0 rs0 d0 cyARam cyBRam rfl)
      (cyEmDevfree cyA cyB cyTs2 cpu0 rs0)
      (WeakRvwmoCycWit.cyEmFetchImg _ cyA cyB cyTs2 cpu0 rs0)
      (cygWQSeg0 cpu0 cpu1 rs0 rs1 d0)
      (cwS0Ok cpu0 cpu1 rs0 rs1 d0)
      ⟨cygCtx0, rfl, by rw [WeakRvwmoWalk.wlognLe 0 1 0 (by omega)]; exact wlogPfxNil cyg⟩
      rfl
      (wndStart d0 cyg (cyBoot cpu0 cpu1 rs0 rs1) 0 cpu0 (cyM cyA cyB) rs0 none ibNone rfl)
      (.inl ⟨rfl, rfl, rfl, dregAgreeRefl _ _⟩)
      rfl
  exact wlkStepOfSeg cyg d0 _ St' 0 _ [.LLoad false zA cyTs2 cyBytes] false zB cyBytes .WCplain
    (0, 1) hstep rfl (fun lb h => by rw [List.mem_singleton] at h; subst h; rfl) himg hpst hdv
    cygAt1 cwGmsg1

/-! ## 6.3 THE ACCEPTANCE TEST: THE WHOLE WALK AT `cyg`, FROM THE GENERIC ENGINE -/

/-- THE FROZEN SET: exactly the cycle's backward step. -/
def cyW : Geid → Prop := fun e => e = (0, 0)

theorem cyWNe (e : Geid) : e ≠ (0, 0) → ¬ cyW e := fun h => h

theorem cygHart (e : Geid) : (gxLbl cyg e).isSome → e.1 < 2 := by
  intro h
  obtain ⟨l, hl⟩ := someOfIsSome h
  rcases cygLbl e l hl with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> decide

theorem cygWAt (e : Geid) (l : Lbl) : gxLbl cyg e = some l → lbIsW l = true → e.2 = 1 := by
  intro hl hw
  rcases cygLbl e l hl with ⟨-, rfl⟩ | ⟨rfl, -⟩ | ⟨-, rfl⟩ | ⟨rfl, -⟩
  · exact absurd hw (by simp [lbIsW])
  · rfl
  · exact absurd hw (by simp [lbIsW])
  · rfl

theorem cygWPoloc' : WPolocClosed cyg cyW := by
  rintro e1 e2 a hW hpo - - ⟨l, hl, hr⟩
  rcases cygLbl e2 l hl with ⟨rfl, -⟩ | ⟨-, rfl⟩ | ⟨rfl, -⟩ | ⟨-, rfl⟩
  · rfl
  · exact absurd hr (by simp [lbIsR])
  · exfalso
    have h1 := hpo.1
    rw [show e1 = (0, 0) from hW] at h1
    exact absurd h1 (by decide)
  · exact absurd hr (by simp [lbIsR])

theorem cygWubA : wubA cyg cyW := by
  intro c ev y _ p s _ _ _ hfh
  exact absurd hfh (cygNoFhook _ _ _)

/-- ONE WRITE PER HART, so the order fact the walk needs holds vacuously. -/
theorem cygGwrow : gwrowGmo cyg := by
  rintro x j k hjk ⟨lj, hlj, hwj⟩ ⟨lk, hlk, hwk⟩
  have hj1 : j = 1 := cygWAt (x, j) lj hlj hwj
  have hk1 : k = 1 := cygWAt (x, k) lk hlk hwk
  omega

theorem cygWsrcLeStore (n : Nat) (e : Geid) (lb : Lbl) :
    gxLbl cyg e = some lb → lbIsW lb = true → WeakRvwmoWalk.wsrcLe cyg n e := by
  intro hl hw aq base ts vs hl2
  rw [hl2] at hl
  cases hl
  exact absurd hw (by simp [lbIsW])

theorem cygWsiteSupply (cpu0 cpu1 : CPU) (rs0 rs1 : RegFile) (d0 : Efab) :
    wsiteSupply (cyBoot cpu0 cpu1 rs0 rs1) d0 cyg cyW (fun _ _ => []) := by
  -- AT THE EMPTY TAINT both new clauses are free
  have hut1 : ∀ (y : Nat) (p : Nat),
      wexitUt d0 [] (wnd d0 cyg (cyBoot cpu0 cpu1 rs0 rs1) y) p := by
    intro y p cpu ws lb l1 l2 rds wrs m rs fn ib m' rs' fn' ib' _ _ _ nn _
    exact List.not_mem_nil
  have hpo1 : ∀ (y : Nat) (p : Nat),
      wpoisSite cyg cyW y d0 [] [] (wnd d0 cyg (cyBoot cpu0 cpu1 rs0 rs1) y) p := by
    intro y p im c0 cpu ws lb l rds wrs m rs1' rs2' fn ib m' rs1'' fn' ib'' _ _ _ hnr _ _
    exact (hnr (by intro nn _; exact List.not_mem_nil)).elim
  intro n x kz p lb hat hp _ hl
  obtain rfl | rfl | hn2 : n = 0 ∨ n = 1 ∨ 2 ≤ n := by omega
  · -- THE FIRST WRITE: hart 0's store, at row position 1
    have h := cygAt1.symm.trans hat
    cases h
    obtain rfl | rfl : p = 0 ∨ p = 1 := by omega
    · have h0 : gxLbl cyg (0, 0) = some (.LLoad false zA cyTs2 cyBytes) := rfl
      rw [h0] at hl
      cases hl
      exact ⟨fun h => absurd trivial h,
        .inr ⟨rfl, cygWit00, cygWwitSite00 cpu0 cpu1 rs0 rs1 d0⟩, hut1 0 0, hpo1 0 0⟩
    · have h0 : gxLbl cyg (0, 1) = some (.LStore false zB cyBytes .WCplain) := rfl
      have hl' := hl
      rw [h0] at hl'
      cases hl'
      exact ⟨fun h => absurd trivial h,
        .inl ⟨cyWNe _ (by decide), cygWsrcLeStore 0 _ _ hl rfl⟩, hut1 0 1, hpo1 0 1⟩
  · -- THE SECOND WRITE: hart 1's store, at row position 1
    have h := cygAt2.symm.trans hat
    cases h
    obtain rfl | rfl : p = 0 ∨ p = 1 := by omega
    · have h0 : gxLbl cyg (1, 0) = some (.LLoad false zB cyTs1 cyBytes) := rfl
      rw [h0] at hl
      cases hl
      refine ⟨fun h => absurd trivial h, .inl ⟨cyWNe _ (by decide), ?_⟩, hut1 1 0, hpo1 1 0⟩
      intro aq base ts vs hl2 j t hj
      rw [h0] at hl2
      cases hl2
      have ht := elem_of_list_lookup_2 hj
      simp [cyTs1] at ht
      omega
    · have h0 : gxLbl cyg (1, 1) = some (.LStore false zA cyBytes .WCplain) := rfl
      have hl' := hl
      rw [h0] at hl'
      cases hl'
      exact ⟨fun h => absurd trivial h,
        .inl ⟨cyWNe _ (by decide), cygWsrcLeStore 1 _ _ hl rfl⟩, hut1 1 1, hpo1 1 1⟩
  · exfalso
    have h : (gwrites cyg)[n]? = some (x, kz) := hat
    rw [cygGwrites, List.getElem?_eq_none (by simp only [List.length_cons, List.length_nil]; omega)]
      at h
    cases h

theorem cygWsupply (cpu0 cpu1 : CPU) (rs0 rs1 : RegFile) (d0 : Efab) :
    wsupply (cyBoot cpu0 cpu1 rs0 rs1) d0 cyg cyW (fun _ _ => []) 2 := by
  refine ⟨cygGwrow, fun x k hs => cygHart (x, k) hs, ?_, cygWPoloc', cygWubA,
    fun _ _ => List.Subset.refl _, cygWsiteSupply cpu0 cpu1 rs0 rs1 d0⟩
  intro x k lb hl _
  have hx : x < 2 := cygHart (x, k) (by rw [hl]; rfl)
  obtain rfl | rfl : x = 0 ∨ x = 1 := by omega
  · exact ⟨cpu0, cyM cyA cyB, rs0, none, ibNone, rfl⟩
  · exact ⟨cpu1, cyM cyB cyA, rs1, none, ibNone, rfl⟩

/-- THE ACCEPTANCE TEST: `WeakRvwmoCycWit.cygWalk`'s conclusion, from the generic engine. -/
theorem cygWalk' (cpu0 cpu1 : CPU) (rs0 rs1 : RegFile) (d0 : Efab) :
    ∃ (l : List Segout) (S0 Sf : CycState),
      segsRun d0 l S0 Sf ∧
      Sf.cstC.cdImg = cyg.gxImg ∧
      Sf.cstPst 0 = (List.range' 0 2).map (cyBoot cpu0 cpu1 rs0 rs1) ∧
      Sf.cstDv 0 = d0 ∧
      logOf cyg (cdLog Sf.cstC Sf.cstC.cdTr.length) := by
  have hwf : gwf cyg := cygConsistent.1
  have hem0 : ∀ x, x < 2 → wemit d0 cyg x 0 (cyBoot cpu0 cpu1 rs0 rs1 x) :=
    fun x _ => wemitOfQconf (cyBoot cpu0 cpu1 rs0 rs1) d0 cyImg 2 cygd x
      (cygQconf cpu0 cpu1 rs0 rs1 d0)
  obtain ⟨l, Sf, hrun, _, himg, hpst, hdv, hpfx⟩ :=
    wlkRun' (cyBoot cpu0 cpu1 rs0 rs1) d0 2 cyg cyW (fun _ _ => [])
      (fun St n hinv hn => wlkStep'OfSupply (cyBoot cpu0 cpu1 rs0 rs1) d0 2 cyg cyW
        (fun _ _ => []) St n cygConsistent (cygWsupply cpu0 cpu1 rs0 rs1 d0) hinv hn)
      2 0 (wlkStart (cyBoot cpu0 cpu1 rs0 rs1) d0 2 cyg)
      (wlkStartInv' (cyBoot cpu0 cpu1 rs0 rs1) d0 2 cyg cyW (fun _ _ => []) hwf hem0)
      (by rw [cygGwrites]; rfl)
  exact ⟨l, wlkStart (cyBoot cpu0 cpu1 rs0 rs1) d0 2 cyg, Sf, hrun, himg, hpst, hdv,
    logOfOfPfx _ _ hpfx⟩

end Weak
