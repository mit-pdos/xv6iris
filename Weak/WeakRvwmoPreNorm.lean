/-
Weak: **the WRITE-ORDER PRE-NORMALIZATION** (`wsupply`'s `gwrowGmo` residual).  A leaf.

Rocq: `iris/WeakRvwmoPreNorm.v` @ xxvzwolszwmp.

## The Rocq header, in substance

`WeakRvwmoWalkb.wsupply`'s first clause is `gwrowGmo`: one hart's writes reach the log in
PROGRAM order.  RVWMO⁻ does not imply it (same-hart byte-disjoint stores are unordered by
`gppo`) and `grule14` does — but the walk exists to REFUTE rule 14, so it must not be assumed.
This file runs `WeakRvwmoNorm`'s exchange normalization at the WEAKER target "every po-earlier
WRITE OF THE SAME HART is gmo-earlier".

  - THE DESCENDING EVENT IS ALWAYS A WRITE: the measure counts only WRITE-witness inversions
    (`gviolw`), so the descent never runs the read-down move and `WeakRvwmoNorm.killK1` — the
    kill the LB witness refutes — does not arise.
  - The po-minimality is over WRITE witnesses only, so interior READS po-before the descending
    write are a new blocker (K4).

THE THREE RESIDUALS (§2): `killWwK2` (an interval read of one of `e`'s bytes at an older write
index), `killWwK3` (a cross-hart same-byte interval write), `killWwK4` (an interval read ppo-
or dep-ordered before `e`).  §4: `normalizeWw` under them.  §4.1: `lbg` has no write-witness
inversion (`lbgGwrow`).  §5 (the R-cycle analysis): each kill carries the two-edge `racyD` path
`z → e → w`, so `racyD`-acyclicity over the orbit plus the one named missing edge `wwGapLink`
discharges all three (`killWwOfAcyclic`, `normalizeWwOfAcyclic`).  §6: what `wsupply` still
costs (`wsupplyRes`; the hart bound is `qconfHartBound`; the disk scope
`wsupplyResNoDiskWrites`), the orbit pull-back named (`wsupplyOrbitPull`), and the capstones
`xv6RvwmoSafeModuloL2''` / `xv6RvwmoSafeModuloL2''Prenorm`.  §7 of the Rocq file (the closing
note: a two-hart graph, acyclic `R`, blocked by K4, normalizable only by an ASCENT of `w`, so
`wwGapLink` is a genuine hypothesis) is a comment; the `Print Assumptions` are Rocq commands.

## Deviations from Rocq

1. NAMES / VOCABULARY as `WeakRvwmoNorm` deviations 1–3 and `WeakRvwmoWalk2` deviation 1
   (`S n` ↦ `n + 1`, `l !! i` ↦ `l[i]?`, `is_Some o` ↦ `o.isSome`, filter lengths over
   `decide`; `gis_w_glbl_is`/`gis_w_gmem` are `WeakRvwmoAcyc.gisWGlblIs`/`.gisWGmem`; Rocq `tc`
   is `MachCSL.tc`, `RacyD` is `racyD`; `wgdev σ0` ↦ `efInit σ0.wgdev`, `img_z (wgimg σ0)` ↦
   `imgZ σ0.wgimg`; the capstones take explicit `hlc GF` with `[MachGpreS hlc GF]
   [WeakGpreS GF]`, `D : CPU → List Register` with `hD : ∀ c, (D c).Nodup`).
2. The `Local Instance pn_*_dec` are `local instance`s built by `unfold; infer_instance` (as
   `WeakRvwmoNorm` deviation 4); `violwp`/`nviolw` use them.
3. Rocq's `Section descent_ww` (contexts `GD0 HK2 HK3 HK4`) is flattened: `descentWw` takes them
   as its first four arguments.
4. O2 / STAGE C.  Both capstones carry the fetch-view premise
   `∀ ρ, rtc epfRun (epInit gen, σ0) ρ → efetchItvOk ρ.1 ρ.2` right after the WP package
   premises (as `WeakRvwmoWalk2.xv6RvwmoSafeModuloL2'`, which they call).  `wsupplyRes`'s
   `wsiteSupply` is the Lean (Stage C) one: no `wfetchSite` conjunct.
5. `tc_app` is `tc_transitive` (Lean's `tc` is core `TransGen`); kept as `tcApp` for the map.

**Rocq → Lean name map.**  `gviolw` `gviolw`, `pn_gmem_dec` `pnGmemDec`, `pn_glbl_is_dec`
`pnGlblIsDec`, `pn_gpo_dec` `pnGpoDec`, `pn_gmo_lt_dec` `pnGmoLtDec`, `pn_gviol_dec`
`pnGviolDec`, `pn_gviolw_dec` `pnGviolwDec`, `violwp` `violwp`, `pn_violwp_dec` `pnViolwpDec`,
`nviolw` `nviolw`, `gviolw_gpairs` `gviolwGpairs`, `violw_mono_rows` `violwMonoRows`,
`nviolw_le` `nviolwLe`, `nviolw_lt` `nviolwLt`, `nviolw_zero` `nviolwZero`, `ww_min` `wwMin`,
`ww_pomin` `wwPomin`, `kill_ww_K2`/`K3`/`K4` `killWwK2`/`killWwK3`/`killWwK4`,
`gswap_violw_mono_rw` `gswapViolwMonoRw`, `swap_invariant_w` `swapInvariantW`, `descent_ww`
`descentWw`, `normalize_ww_aux` `normalizeWwAux`, `normalize_ww` `normalizeWw`,
`lbg_row_short` `lbgRowShort`, `lbg_pos0_notw` `lbgPos0Notw`, `lbg_no_violw` `lbgNoViolw`,
`lbg_gwrow` `lbgGwrow`, `tc_app` `tcApp`, `gviolw_gpow` `gviolwGpow`, `kill_ww_K2_Rpath`/`K3`/
`K4` `killWwK2Rpath`/`killWwK3Rpath`/`killWwK4Rpath`, `ww_gap_link` `wwGapLink`,
`kill_ww_of_acyclic` `killWwOfAcyclic`, `normalize_ww_of_acyclic` `normalizeWwOfAcyclic`,
`qconf_hart_bound` `qconfHartBound`, `wsupply_res` `wsupplyRes`, `wsupply_res_no_disk_writes`
`wsupplyResNoDiskWrites`, `wsupply_of_gwrow` `wsupplyOfGwrow`, `wsupply_orbit_pull`
`wsupplyOrbitPull`, `wsupply_of_prenorm` `wsupplyOfPrenorm`, `xv6_rvwmo_safe_modulo_l2''`
`xv6RvwmoSafeModuloL2''`, `xv6_rvwmo_safe_modulo_l2''_prenorm` `xv6RvwmoSafeModuloL2''Prenorm`.

**File-qualified names:** none (no name of this file is in `notes/weak-port-dupnames.json`;
no Lean-only helpers).

**Dropped:** none (Rocq 45 declarations; Lean 45).
-/
import Weak.WeakRvwmoNorm
import Weak.WeakRvwmoAcyc
import Weak.WeakRvwmoSupply
import Weak.WeakRvwmoWalk2

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open LeanRV64D
open Lbl

/-! # 1. THE MEASURE: same-hart WRITE inversions -/

def gviolw (G : Gexec) (e w : Geid) : Prop :=
  gviol G e w ∧ gisW G e = true

local instance pnGmemDec (G : Gexec) (e : Geid) : Decidable (gmem G e) :=
  match h : gxLbl G e with
  | some l =>
    if hm : lbIsMem l = true then isTrue ⟨l, h, hm⟩
    else isFalse (fun ⟨l', hl', hm'⟩ => hm (by rw [h] at hl'; cases hl'; exact hm'))
  | none => isFalse (fun ⟨l', hl', _⟩ => by rw [h] at hl'; cases hl')

local instance pnGlblIsDec (G : Gexec) (e : Geid) (P : Lbl → Bool) :
    Decidable (glblIs G e P) :=
  match h : gxLbl G e with
  | some l =>
    if hm : P l = true then isTrue ⟨l, h, hm⟩
    else isFalse (fun ⟨l', hl', hm'⟩ => hm (by rw [h] at hl'; cases hl'; exact hm'))
  | none => isFalse (fun ⟨l', hl', _⟩ => by rw [h] at hl'; cases hl')

local instance pnGpoDec (G : Gexec) (e1 e2 : Geid) :
    Decidable (WeakRvwmoGraph.gpo G e1 e2) := by
  unfold WeakRvwmoGraph.gpo; infer_instance

local instance pnGmoLtDec (G : Gexec) (e1 e2 : Geid) : Decidable (gmoLt G e1 e2) := by
  unfold gmoLt; infer_instance

local instance pnGviolDec (G : Gexec) (e w : Geid) : Decidable (gviol G e w) := by
  unfold gviol; infer_instance

local instance pnGviolwDec (G : Gexec) (e w : Geid) : Decidable (gviolw G e w) := by
  unfold gviolw; infer_instance

def violwp (G : Gexec) (p : Geid × Geid) : Prop := gviolw G p.1 p.2

local instance pnViolwpDec (G : Gexec) (p : Geid × Geid) : Decidable (violwp G p) := by
  unfold violwp; infer_instance

def nviolw (G : Gexec) : Nat := ((gpairs G).filter (fun p => decide (violwp G p))).length

theorem gviolwGpairs (G : Gexec) (e w : Geid) : gviolw G e w → (e, w) ∈ gpairs G :=
  fun h => gviolGpairs G e w h.1

/-- `gisW` TRANSPORTS along `rowsRel`, so a monotone `gviol` gives a monotone `gviolw`. -/
theorem violwMonoRows (π : Nat → Nat) (G G' : Gexec) :
    rowsRel π G G' →
    (∀ e' w', gviolw G' e' w' → gviol G e' w') →
    ∀ e' w', gviolw G' e' w' → gviolw G e' w' := by
  intro hr hmono e' w' hv
  exact ⟨hmono e' w' hv, by rw [← rowsRelGisW π G G' e' hr]; exact hv.2⟩

theorem nviolwLe (G G' : Gexec) :
    gpairs G' = gpairs G → (∀ e w, gviolw G' e w → gviolw G e w) → nviolw G' ≤ nviolw G := by
  intro hp hmono
  unfold nviolw
  rw [hp]
  apply filterLengthLe
  intro ⟨e, w⟩ h
  simp only [decide_eq_true_eq] at h ⊢
  exact hmono e w h

theorem nviolwLt (G G' : Gexec) (e w : Geid) :
    gpairs G' = gpairs G → (∀ e' w', gviolw G' e' w' → gviolw G e' w') →
    gviolw G e w → ¬ gviolw G' e w → nviolw G' < nviolw G := by
  intro hp hmono hv hnv
  unfold nviolw
  rw [hp]
  refine filterLengthLt _ _ _ (e, w) ?_ (gviolwGpairs G e w hv)
    (by simp only [decide_eq_true_eq]; exact hv)
    (by simp only [decide_eq_false_iff_not]; exact hnv)
  intro ⟨e', w'⟩ h
  simp only [decide_eq_true_eq] at h ⊢
  exact hmono e' w' h

/-- THE TARGET.  No same-hart write inversion IS `gwrowGmo`. -/
theorem nviolwZero (G : Gexec) : gwf G → nviolw G = 0 → gwrowGmo G := by
  intro hwf h0 x j k hjk hj hk
  have hnd := hwf.1
  obtain ⟨lj, hlj, hwj⟩ := id hj
  obtain ⟨lk, hlk, hwk⟩ := id hk
  have hje : (x, j) ∈ gwrites G :=
    gisWGwrites G _ hwf (by rw [hlj]; rfl) (by simp only [gisW, hlj]; exact hwj)
  have hke : (x, k) ∈ gwrites G :=
    gisWGwrites G _ hwf (by rw [hlk]; rfl) (by simp only [gisW, hlk]; exact hwk)
  have hjg : (x, j) ∈ G.gxGmo := ((gwritesElemOf G _).1 hje).1
  have hkg : (x, k) ∈ G.gxGmo := ((gwritesElemOf G _).1 hke).1
  have hne : (x, j) ≠ (x, k) := by
    intro h
    simp only [Prod.mk.injEq] at h
    omega
  apply (gwixGposLt G _ _ hnd hje hke).2
  rcases gmoLtTotal G _ _ hnd hjg hkg hne with ⟨_, _, h⟩ | hbad
  · exact h
  · exfalso
    have hv : gviolw G (x, j) (x, k) :=
      ⟨⟨⟨rfl, hjk, by rw [hlj]; rfl, by rw [hlk]; rfl⟩, WeakRvwmoGraph.glblIsWGmem G _ hj, hk,
        hbad⟩, glblIsWGisW G _ hj⟩
    have := filterPos (fun p => decide (violwp G p)) (gpairs G) ((x, j), (x, k))
      (gviolwGpairs G _ _ hv) (by simp only [decide_eq_true_eq]; exact hv)
    unfold nviolw at h0
    omega

/-! # 2. THE THREE KILL CONFIGURATIONS -/

def wwMin (GD' : Gdexec) (w : Geid) : Prop :=
  ∀ e' w', gviolw GD'.gdG e' w' → ¬ gmoLt GD'.gdG w' w

def wwPomin (GD' : Gdexec) (w e : Geid) : Prop :=
  ∀ e', gviolw GD'.gdG e' w → ¬ e'.2 < e.2

/-- K2: an interval READ reads one of the descending write's bytes at an OLDER write index. -/
def killWwK2 (GD : Gdexec) : Prop :=
  ∀ GD', gdEquiv GD GD' →
  ∀ (w e z : Geid) (a : Int) (t : Nat) (v v' : BitVec 8),
    gviolw GD'.gdG e w →
    wwMin GD' w → wwPomin GD' w e →
    gisW GD'.gdG z = false →
    gmoLt GD'.gdG w z → gmoLt GD'.gdG z e →
    greadsByte GD'.gdG z a t v →
    gwritesByte GD'.gdG e a v' →
    t < gwix GD'.gdG e →
    False

/-- K3: a CROSS-HART SAME-BYTE write sits gmo-inside the interval. -/
def killWwK3 (GD : Gdexec) : Prop :=
  ∀ GD', gdEquiv GD GD' →
  ∀ (w e z : Geid) (a : Int) (v v' : BitVec 8),
    gviolw GD'.gdG e w →
    wwMin GD' w → wwPomin GD' w e →
    gisW GD'.gdG z = true → z.1 ≠ e.1 →
    gmoLt GD'.gdG w z → gmoLt GD'.gdG z e →
    gwritesByte GD'.gdG z a v → gwritesByte GD'.gdG e a v' →
    False

/-- K4 — THE NEW ONE.  An interval READ that is ppo- (or dep-) ordered before the descending
write. -/
def killWwK4 (GD : Gdexec) : Prop :=
  ∀ GD', gdEquiv GD GD' →
  ∀ (w e z : Geid),
    gviolw GD'.gdG e w →
    wwMin GD' w → wwPomin GD' w e →
    gisW GD'.gdG z = false →
    gmoLt GD'.gdG w z → gmoLt GD'.gdG z e →
    (gppo GD'.gdG z e ∨ (z, e) ∈ GD'.gdDeps) →
    False

/-! # 3. ONE DESCENT STEP, ABSTRACTLY -/

/-- The (R,W) move's violation monotonicity at `gviolw`: the only pair the swap can newly
invert is `(z, e)`, and a READ `z` never gives a `gviolw`. -/
theorem gswapViolwMonoRw (G : Gexec) (n : Nat) (z e : Geid) :
    G.gxGmo.Nodup → G.gxGmo[n]? = some z → G.gxGmo[n + 1]? = some e →
    gisW G z = false →
    ∀ e' w', gviolw (gswap G n) e' w' → gviol G e' w' := by
  rintro hnd hz he hzw e' w' ⟨⟨hpo, hme, hw, hgmo⟩, hisw⟩
  refine ⟨hpo, hme, hw, ?_⟩
  rcases gswapGmoLtInv G n z e w' e' hnd hz he hgmo with h | ⟨_, h2⟩
  · exact h
  · exfalso
    have h3 : gisW G z = true := h2 ▸ hisw
    rw [hzw] at h3
    cases h3

theorem swapInvariantW (π : Nat → Nat) (G G' : Gexec) (w e z : Geid) (n : Nat) :
    gwf G →
    G.gxGmo[n]? = some z → G.gxGmo[n + 1]? = some e →
    rowsRel π G G' →
    G'.gxGmo = (gswap G n).gxGmo →
    (∀ e' w', gviolw G' e' w' → gviolw G e' w') →
    gviolw G e w → gpos G w < n →
    (∀ e' w', gviolw G e' w' → ¬ gmoLt G w' w) →
    (∀ e', gviolw G e' w → ¬ e'.2 < e.2) →
    nviolw G' ≤ nviolw G ∧
    gviolw G' e w ∧
    (∀ e' w', gviolw G' e' w' → ¬ gmoLt G' w' w) ∧
    (∀ e', gviolw G' e' w → ¬ e'.2 < e.2) ∧
    gpos G' e = n ∧ gpos G' w = gpos G w := by
  intro hwf hz he hrows hgmo hmono hv hwn hmin hpmin
  have hnd := hwf.1
  have hzne : w ≠ z := by
    intro h
    subst h
    rw [gposOfLookup G n _ hnd hz] at hwn
    omega
  obtain ⟨⟨hpo, hme, hww, hmo⟩, hew⟩ := id hv
  have hwin : w ∈ G.gxGmo := hmo.1
  refine ⟨nviolwLe G G' (rowsRelGpairs π G G' hrows) hmono,
    ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩, ?_, ?_, ?_, ?_⟩
  · exact (rowsRelGpo π G G' e w hrows).2 hpo
  · exact (rowsRelGmem π G G' e hrows).2 hme
  · exact (rowsRelGlblIs π G G' w lbIsW hrows (lblRenIsW π)).2 hww
  · rw [gmoLtGmoEq G' (gswap G n) w e hgmo]
    exact gswapGmoLt G n z e w e hnd hz he hmo (fun ⟨h, _⟩ => hzne h)
  · rw [rowsRelGisW π G G' e hrows]
    exact hew
  · intro e' w' hv' hlt'
    rw [gmoLtGmoEq G' (gswap G n) w' w hgmo] at hlt'
    rcases gswapGmoLtInv G n z e w' w hnd hz he hlt' with hg | ⟨_, h⟩
    · exact hmin e' w' (hmono e' w' hv') hg
    · exact hzne h
  · intro e' hv'
    exact hpmin e' (hmono e' w hv')
  · rw [gposGmoEq G' (gswap G n) e hgmo]
    exact gswapGposUpper G n z e hnd hz he
  · rw [gposGmoEq G' (gswap G n) w hgmo, gswapGpos G n z e w hnd hz he hwin]
    apply sidxId <;> omega

/-! # 4. THE DESCENT, AND THE NORMALIZATION -/

theorem descentWw (GD0 : Gdexec) (hK2 : killWwK2 GD0) (hK3 : killWwK3 GD0)
    (hK4 : killWwK4 GD0) (D : Nat) (GD : Gdexec) (w e : Geid) :
    gdEquiv GD0 GD →
    gviolw GD.gdG e w →
    wwMin GD w →
    wwPomin GD w e →
    gpos GD.gdG e - gpos GD.gdG w ≤ D →
    ∃ GD', gdEquiv GD0 GD' ∧ nviolw GD'.gdG < nviolw GD.gdG := by
  induction D generalizing GD w e with
  | zero =>
    intro _ hv _ _ hd
    exfalso
    obtain ⟨⟨_, _, _, ⟨_, _, hlt⟩⟩, _⟩ := hv
    omega
  | succ D ih =>
    intro heq hv hmin hpmin hd
    obtain ⟨π, hrows0, hwp0, hdeps0, hcons⟩ := id heq
    have hc := hcons.1
    have hdwf := hcons.2.1
    have hwf := hc.1
    have hppo := hc.2.1
    have hnd := hwf.1
    obtain ⟨⟨⟨hag_ew, hlt_ew, hse, hsw⟩, _, hlw, hmo_we⟩, hewisw⟩ := id hv
    obtain ⟨hwin, hein, _⟩ := id hmo_we
    have hwisw : gisW GD.gdG w = true := glblIsWGisW _ _ hlw
    have hSn : GD.gdG.gxGmo[gpos GD.gdG e]? = some e := gposElemLookup _ _ hein
    -- THE VACUITY LEMMA, write-restricted
    have hnoblock : ∀ y, gisW GD.gdG y = true →
        gmoLt GD.gdG w y → y.1 = e.1 → y.2 < e.2 → False := by
      intro y hyw hmo hag hlt
      have hys : (gxLbl GD.gdG y).isSome = true := by
        obtain ⟨l, hl, _⟩ := WeakRvwmoAcyc.gisWGlblIs _ _ hyw
        simp [hl]
      exact hpmin y ⟨⟨⟨hag.trans hag_ew, by omega, hys, hsw⟩, WeakRvwmoAcyc.gisWGmem _ _ hyw,
        hlw, hmo⟩, hyw⟩ hlt
    by_cases hfin : gpos GD.gdG e = gpos GD.gdG w + 1
    · -- THE FINAL SWAP: two same-hart writes, byte-disjoint by poloc.
      have hn : GD.gdG.gxGmo[gpos GD.gdG w]? = some w := gposElemLookup _ _ hwin
      have hSn' : GD.gdG.gxGmo[gpos GD.gdG w + 1]? = some e := by rw [← hfin]; exact hSn
      have hnppo : ¬ gppo GD.gdG w e := by
        intro hp
        have := (gppoPoLt _ _ _ hp).2
        omega
      have hdisj : ∀ a, (∃ v, gwritesByte GD.gdG w a v) →
          ¬ ∃ v', gwritesByte GD.gdG e a v' := by
        rintro a ⟨v, hwv⟩ ⟨v', hev⟩
        have hpl : gppo GD.gdG e w :=
          Or.inl ⟨⟨hag_ew, hlt_ew, hse, hsw⟩, a, Or.inl ⟨v', hev⟩, Or.inl ⟨v, hwv⟩⟩
        have := (hppo e w hpl).2.2
        omega
      have hdep : (w, e) ∉ GD.gdDeps := by
        intro hin
        have : w.2 < e.2 := (hdwf (w, e) hin).2.1
        omega
      have hcons' := gswapwWwDeps GD (gpos GD.gdG w) w e hcons hn hSn' hwisw hewisw
        hdisj hnppo hdep
      have hk : 0 < gwix GD.gdG w :=
        WeakRvwmoGraph.gwixPos _ _ (gisWGwrites _ _ hwf hsw hwisw)
      refine ⟨⟨gswapw GD.gdG (gpos GD.gdG w) (gwix GD.gdG w), GD.gdDeps⟩,
        ⟨fun t => tswap (gwix GD.gdG w) (π t), ?_, ?_, hdeps0, hcons'⟩, ?_⟩
      · exact rowsRelTrans _ _ _ _ _ _ hrows0 (rowsRelGswapw GD.gdG _ _ hk) (fun _ => rfl)
      · exact wpermTrans _ _ _ _ _ _ hwp0
          (wpermGswapw GD.gdG _ w e hnd hn hSn' hwisw hewisw) (fun _ => rfl)
      · have hres :=
          (gswapwResolves GD.gdG _ w e hwf hn hSn' hwisw hewisw hag_ew hlt_ew).2
        refine nviolwLt GD.gdG _ e w (rowsRelGpairs _ _ _ (rowsRelGswapw GD.gdG _ _ hk)) ?_ hv
          (fun h => hres h.1)
        refine violwMonoRows (tswap (gwix GD.gdG w)) _ _ (rowsRelGswapw GD.gdG _ _ hk) ?_
        intro e' w' hv'
        exact gswapwViolMono GD.gdG _ (gwix GD.gdG w) w e e' w' hnd hn hSn'
          (fun hp => by have := hp.2.1; omega) hv'.1
    · -- AN INTERIOR SWAP.
      have hgap : gpos GD.gdG w + 1 < gpos GD.gdG e := by
        have := hmo_we.2.2
        omega
      obtain ⟨n, hn_def⟩ : ∃ n, n = gpos GD.gdG e - 1 := ⟨_, rfl⟩
      have hSn' : GD.gdG.gxGmo[n + 1]? = some e := by
        rw [show n + 1 = gpos GD.gdG e by omega]
        exact hSn
      have hnlt : n < GD.gdG.gxGmo.length := by
        have := gposLtLen GD.gdG e hein
        omega
      obtain ⟨z, hz⟩ := someOfIsSome (lookup_lt_is_Some_2 hnlt)
      have hzin : z ∈ GD.gdG.gxGmo := elem_of_list_lookup_2 hz
      have hzpos : gpos GD.gdG z = n := gposOfLookup _ _ _ hnd hz
      have hzmem : gmem GD.gdG z := gwfGmoMem _ _ hwf hzin
      have hwn : gpos GD.gdG w < n := by omega
      have hmo_wz : gmoLt GD.gdG w z := ⟨hwin, hzin, by omega⟩
      have hmo_ze : gmoLt GD.gdG z e := ⟨hzin, hein, by omega⟩
      have hzs : (gxLbl GD.gdG z).isSome = true := by
        obtain ⟨l, hl, _⟩ := hzmem
        simp [hl]
      have hzne_e : z ≠ e := by
        intro h
        rw [h] at hmo_ze
        exact gmoLtIrrefl _ _ hmo_ze
      have hstep : ∃ (π' : Nat → Nat) (G' : Gexec),
          rowsRel π' GD.gdG G' ∧ wperm π' GD.gdG G' ∧
          G'.gxGmo = (gswap GD.gdG n).gxGmo ∧
          rvwmoMinusDepsConsistent ⟨G', GD.gdDeps⟩ ∧
          (∀ e' w', gviolw G' e' w' → gviol GD.gdG e' w') := by
        cases hzw : gisW GD.gdG z with
        | true =>
          -- (W,W): byte-disjoint, or K3
          have hnppo : ¬ gppo GD.gdG z e := by
            intro hp
            obtain ⟨hag, hlt⟩ := gppoPoLt _ _ _ hp
            exact hnoblock z hzw hmo_wz hag hlt
          have hnpo : ¬ WeakRvwmoGraph.gpo GD.gdG z e := by
            rintro ⟨hag, hlt, _, _⟩
            exact hnoblock z hzw hmo_wz hag hlt
          have hdep : (z, e) ∉ GD.gdDeps := by
            intro hin
            obtain ⟨hag, hlt, _, _⟩ := hdwf (z, e) hin
            exact hnoblock z hzw hmo_wz hag hlt
          have hkz : 0 < gwix GD.gdG z :=
            WeakRvwmoGraph.gwixPos _ _ (gisWGwrites _ _ hwf hzs hzw)
          have hdisj : ∀ a, (∃ v, gwritesByte GD.gdG z a v) →
              ¬ ∃ v', gwritesByte GD.gdG e a v' := by
            rintro a ⟨v, hzv⟩ ⟨v', hev⟩
            by_cases hag : z.1 = e.1
            · by_cases hlt : z.2 < e.2
              · exact hnoblock z hzw hmo_wz hag hlt
              · by_cases heq2 : z.2 = e.2
                · exact hzne_e (Prod.ext hag heq2)
                · have hpl : gppo GD.gdG e z :=
                    Or.inl ⟨⟨hag.symm, by omega, hse, hzs⟩, a, Or.inl ⟨v', hev⟩,
                      Or.inl ⟨v, hzv⟩⟩
                  have := (hppo e z hpl).2.2
                  omega
            · exact hK3 GD heq w e z a v v' hv hmin hpmin hzw hag hmo_wz hmo_ze hzv hev
          refine ⟨tswap (gwix GD.gdG z), gswapw GD.gdG n (gwix GD.gdG z),
            rowsRelGswapw GD.gdG n _ hkz, wpermGswapw GD.gdG n z e hnd hz hSn' hzw hewisw, rfl,
            gswapwWwDeps GD n z e hcons hz hSn' hzw hewisw hdisj hnppo hdep, ?_⟩
          intro e' w' hv'
          exact gswapwViolMono GD.gdG n (gwix GD.gdG z) z e e' w' hnd hz hSn' hnpo hv'.1
        | false =>
          -- (R,W): the co-max condition (else K2), the ppo/dep block (K4)
          have hnppo : ¬ gppo GD.gdG z e := fun hp =>
            hK4 GD heq w e z hv hmin hpmin hzw hmo_wz hmo_ze (Or.inl hp)
          have hdep : (z, e) ∉ GD.gdDeps := fun hin =>
            hK4 GD heq w e z hv hmin hpmin hzw hmo_wz hmo_ze (Or.inr hin)
          have hcomax : ∀ a t v, greadsByte GD.gdG z a t v →
              (∃ v', gwritesByte GD.gdG e a v') → gwix GD.gdG e ≤ t := by
            rintro a t v hrd ⟨v', hwb⟩
            by_cases hle : gwix GD.gdG e ≤ t
            · exact hle
            · exact (hK2 GD heq w e z a t v v' hv hmin hpmin hzw hmo_wz hmo_ze hrd hwb
                (by omega)).elim
          exact ⟨fun t => t, gswap GD.gdG n, rowsRelGswap GD.gdG n,
            wpermGswapLo GD.gdG n z e hz hSn' hzw, rfl,
            gswapWriteDownDeps GD n z e hcons hz hSn' hzw hewisw hnppo hcomax hdep,
            gswapViolwMonoRw GD.gdG n z e hnd hz hSn' hzw⟩
      obtain ⟨π', G', hrows', hwp', hgmo', hcons', hmono0⟩ := hstep
      have hmono' : ∀ e' w', gviolw G' e' w' → gviolw GD.gdG e' w' :=
        violwMonoRows π' GD.gdG G' hrows' hmono0
      obtain ⟨_, hv', hmin', hpmin', hpe', hpw'⟩ :=
        swapInvariantW π' GD.gdG G' w e z n hwf hz hSn' hrows' hgmo' hmono' hv hwn hmin hpmin
      have heq' : gdEquiv GD0 ⟨G', GD.gdDeps⟩ :=
        ⟨fun t => π' (π t), rowsRelTrans _ _ _ _ _ _ hrows0 hrows' (fun _ => rfl),
          wpermTrans _ _ _ _ _ _ hwp0 hwp' (fun _ => rfl), hdeps0, hcons'⟩
      obtain ⟨GD'', heq'', hlt''⟩ := ih ⟨G', GD.gdDeps⟩ w e heq' hv' hmin' hpmin'
        (by show gpos G' e - gpos G' w ≤ D; rw [hpe', hpw']; omega)
      have hlt2 : nviolw GD''.gdG < nviolw G' := hlt''
      have hnle : nviolw G' ≤ nviolw GD.gdG :=
        nviolwLe GD.gdG G' (rowsRelGpairs π' GD.gdG G' hrows') hmono'
      exact ⟨GD'', heq'', by omega⟩

theorem normalizeWwAux (GD0 : Gdexec) (N : Nat) :
    killWwK2 GD0 → killWwK3 GD0 → killWwK4 GD0 →
    ∀ GD, gdEquiv GD0 GD → nviolw GD.gdG ≤ N →
    ∃ GD', gdEquiv GD0 GD' ∧ gwrowGmo GD'.gdG := by
  intro hK2 hK3 hK4
  induction N with
  | zero =>
    intro GD heq hN
    have hwf : gwf GD.gdG := by
      obtain ⟨_, _, _, _, hc⟩ := heq
      exact hc.1.1
    exact ⟨GD, heq, nviolwZero _ hwf (by omega)⟩
  | succ N ih =>
    intro GD heq hN
    have hwf : gwf GD.gdG := by
      obtain ⟨_, _, _, _, hc⟩ := heq
      exact hc.1.1
    by_cases h0 : nviolw GD.gdG = 0
    · exact ⟨GD, heq, nviolwZero _ hwf h0⟩
    have hne : (gpairs GD.gdG).filter (fun p => decide (violwp GD.gdG p)) ≠ [] := by
      intro hnil
      apply h0
      simp only [nviolw, hnil, List.length_nil]
    obtain ⟨⟨e0, w⟩, hin, hmin0⟩ := listMinBy (fun p : Geid × Geid => gpos GD.gdG p.2) _ hne
    simp only [List.mem_filter, decide_eq_true_eq] at hin
    obtain ⟨_, hv0⟩ := hin
    have hv0' : gviolw GD.gdG e0 w := hv0
    have hmin : wwMin GD w := by
      rintro e' w' hv' ⟨_, _, hlt⟩
      have hin' : (e', w') ∈ (gpairs GD.gdG).filter (fun p => decide (violwp GD.gdG p)) :=
        List.mem_filter.2 ⟨gviolwGpairs _ _ _ hv', by simp only [decide_eq_true_eq]; exact hv'⟩
      have hle : gpos GD.gdG w ≤ gpos GD.gdG w' := hmin0 _ hin'
      omega
    have hne2 : (gevs' GD.gdG).filter (fun e' => decide (gviolw GD.gdG e' w)) ≠ [] := by
      intro hnil
      have he0 : e0 ∈ (gevs' GD.gdG).filter (fun e' => decide (gviolw GD.gdG e' w)) := by
        refine List.mem_filter.2 ⟨?_, by simp only [decide_eq_true_eq]; exact hv0'⟩
        obtain ⟨⟨_, ⟨l, hl, _⟩, _, _⟩, _⟩ := hv0'
        exact elemOfGevs' _ _ (by simp [hl])
      rw [hnil] at he0
      simp at he0
    obtain ⟨e, hin2, hmin2⟩ := listMinBy (fun e' : Geid => e'.2) _ hne2
    simp only [List.mem_filter, decide_eq_true_eq] at hin2
    obtain ⟨_, hv⟩ := hin2
    have hpmin : wwPomin GD w e := by
      intro e' hv' hlt
      have hin' : e' ∈ (gevs' GD.gdG).filter (fun e'' => decide (gviolw GD.gdG e'' w)) := by
        refine List.mem_filter.2 ⟨?_, by simp only [decide_eq_true_eq]; exact hv'⟩
        obtain ⟨⟨_, ⟨l, hl, _⟩, _, _⟩, _⟩ := hv'
        exact elemOfGevs' _ _ (by simp [hl])
      have hle : e.2 ≤ e'.2 := hmin2 _ hin'
      omega
    obtain ⟨GD1, heq1, hlt1⟩ := descentWw GD0 hK2 hK3 hK4
      (gpos GD.gdG e - gpos GD.gdG w) GD w e heq hv hmin hpmin (Nat.le_refl _)
    exact ih GD1 heq1 (by omega)

/-- THE DELIVERABLE: a `gdEquiv` member whose same-hart writes reach the log in PROGRAM
ORDER. -/
theorem normalizeWw (GD : Gdexec) :
    rvwmoMinusDepsConsistent GD →
    killWwK2 GD → killWwK3 GD → killWwK4 GD →
    ∃ GD', gdEquiv GD GD' ∧ gwrowGmo GD'.gdG := by
  intro hcons hK2 hK3 hK4
  exact normalizeWwAux GD (nviolw GD.gdG) hK2 hK3 hK4 GD (gdEquivRefl GD hcons) (Nat.le_refl _)

/-! ## 4.1 THE NON-COLLAPSE WITNESS DOES NOT REFUTE THIS NORMALIZATION -/

theorem lbgRowShort (x k : Nat) : (gxLbl lbg (x, k)).isSome = true → k < 2 := by
  intro h
  obtain ⟨l, hl⟩ := someOfIsSome h
  rcases lbgLbl _ l hl with ⟨he, _⟩ | ⟨he, _⟩ | ⟨he, _⟩ | ⟨he, _⟩ <;>
    simp only [Prod.mk.injEq] at he <;> omega

theorem lbgPos0Notw (x : Nat) : gisW lbg (x, 0) = false := by
  rcases x with _ | _ | x <;> simp [gisW, gxLbl, lbg, lbIsW]

theorem lbgNoViolw (e w : Geid) : ¬ gviolw lbg e w := by
  rintro ⟨⟨⟨hag, hlt, hse, hsw⟩, _, _, _⟩, he⟩
  obtain ⟨ex, ek⟩ := e
  obtain ⟨wx, wk⟩ := w
  simp only at hag hlt hse hsw
  subst hag
  have hk2 : wk < 2 := lbgRowShort ex wk hsw
  cases ek with
  | zero => rw [lbgPos0Notw] at he; cases he
  | succ ek => omega

theorem lbgGwrow : gwrowGmo lbg := by
  apply nviolwZero lbg lbGraphConsistent.1
  unfold nviolw
  cases hf : (gpairs lbg).filter (fun p => decide (violwp lbg p)) with
  | nil => rfl
  | cons p l =>
    exfalso
    have hp : p ∈ (gpairs lbg).filter (fun p => decide (violwp lbg p)) := by
      rw [hf]; simp
    rw [List.mem_filter] at hp
    exact lbgNoViolw p.1 p.2 (of_decide_eq_true hp.2)

/-! # 5. THE R-CYCLE ANALYSIS — WHAT EACH RESIDUAL ACTUALLY IS -/

/-- `tc` is transitive. -/
theorem tcApp {A : Type _} (R : A → A → Prop) (x y z : A) :
    tc R x y → tc R y z → tc R x z :=
  fun h1 h2 => tc_transitive h1 h2

theorem gviolwGpow (G : Gexec) (e w : Geid) : gviolw G e w → gpow G e w := by
  rintro ⟨⟨hpo, hme, hlw, _⟩, _⟩
  exact ⟨hpo, hme, glblIsWGisW _ _ hlw⟩

theorem killWwK2Rpath (GD' : Gdexec) (w e z : Geid) (a : Int) (t : Nat) (v v' : BitVec 8) :
    gviolw GD'.gdG e w →
    gmoLt GD'.gdG z e →
    greadsByte GD'.gdG z a t v →
    gwritesByte GD'.gdG e a v' →
    t < gwix GD'.gdG e →
    tc (racyD GD') z w := by
  intro hv hze hrd hwb hlt
  refine tc_l ?_ (tc_once (Or.inl (Or.inl (gviolwGpow _ _ _ hv))))
  refine Or.inl (Or.inr (Or.inr (Or.inr (Or.inl ⟨?_, a, t, v, v', hrd, hwb, hlt⟩))))
  intro h
  rw [h] at hze
  exact gmoLtIrrefl _ _ hze

theorem killWwK3Rpath (GD' : Gdexec) (w e z : Geid) (a : Int) (v v' : BitVec 8) :
    gwf GD'.gdG →
    gviolw GD'.gdG e w →
    gmoLt GD'.gdG z e →
    gwritesByte GD'.gdG z a v →
    gwritesByte GD'.gdG e a v' →
    tc (racyD GD') z w := by
  intro hwf hv hze hzb heb
  have hnd := hwf.1
  refine tc_l ?_ (tc_once (Or.inl (Or.inl (gviolwGpow _ _ _ hv))))
  refine Or.inl (Or.inr (Or.inr (Or.inl ⟨a, v, v', hzb, heb, ?_⟩)))
  exact (gwixGposLt GD'.gdG z e hnd (gwritesByteInGwrites _ z a v hwf hzb)
    (gwritesByteInGwrites _ e a v' hwf heb)).2 hze.2.2

theorem killWwK4Rpath (GD' : Gdexec) (w e z : Geid) :
    gviolw GD'.gdG e w →
    (gppo GD'.gdG z e ∨ (z, e) ∈ GD'.gdDeps) →
    tc (racyD GD') z w := by
  intro hv hor
  refine tc_l ?_ (tc_once (Or.inl (Or.inl (gviolwGpow _ _ _ hv))))
  rcases hor with hp | hd
  · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr hp))))
  · exact Or.inr hd

/-- THE ONE MISSING EDGE, NAMED — at exactly the descent's own interval. -/
def wwGapLink (GD : Gdexec) : Prop :=
  ∀ GD', gdEquiv GD GD' →
  ∀ (w e z : Geid),
    gviolw GD'.gdG e w →
    gmoLt GD'.gdG w z → gmoLt GD'.gdG z e →
    tc (racyD GD') w z

/-- … and with it, `racyD`-acyclicity over the orbit discharges all three residuals. -/
theorem killWwOfAcyclic (GD : Gdexec) :
    (∀ GD', gdEquiv GD GD' → ∀ x, ¬ tc (racyD GD') x x) →
    wwGapLink GD →
    killWwK2 GD ∧ killWwK3 GD ∧ killWwK4 GD := by
  intro hacy hlink
  refine ⟨?_, ?_, ?_⟩
  · intro GD' heq w e z a t v v' hv _ _ _ hwz hze hrd hwb hlt
    exact hacy GD' heq w (tcApp _ _ _ _ (hlink GD' heq w e z hv hwz hze)
      (killWwK2Rpath GD' w e z a t v v' hv hze hrd hwb hlt))
  · intro GD' heq w e z a v v' hv _ _ _ _ hwz hze hzb heb
    have hwf : gwf GD'.gdG := by
      obtain ⟨_, _, _, _, hc⟩ := heq
      exact hc.1.1
    exact hacy GD' heq w (tcApp _ _ _ _ (hlink GD' heq w e z hv hwz hze)
      (killWwK3Rpath GD' w e z a v v' hwf hv hze hzb heb))
  · intro GD' heq w e z hv _ _ _ hwz hze hor
    exact hacy GD' heq w (tcApp _ _ _ _ (hlink GD' heq w e z hv hwz hze)
      (killWwK4Rpath GD' w e z hv hor))

theorem normalizeWwOfAcyclic (GD : Gdexec) :
    rvwmoMinusDepsConsistent GD →
    (∀ GD', gdEquiv GD GD' → ∀ x, ¬ tc (racyD GD') x x) →
    wwGapLink GD →
    ∃ GD', gdEquiv GD GD' ∧ gwrowGmo GD'.gdG := by
  intro hcons hacy hlink
  obtain ⟨hK2, hK3, hK4⟩ := killWwOfAcyclic GD hacy hlink
  exact normalizeWw GD hcons hK2 hK3 hK4

/-! # 6. WHAT `wsupply` STILL COSTS, AND THE CAPSTONE AT THAT RESIDUE -/

/-- THE HART BOUND IS NOT A HYPOTHESIS — it is `gdexecQconf`'s hart-count clause. -/
theorem qconfHartBound (boot : Nat → Pexv6) (d0 : Efab) (im : Image) (nh : Nat)
    (GD : Gdexec) :
    gdexecQconf boot d0 im nh GD →
    ∀ x k, (gxLbl GD.gdG (x, k)).isSome → x < nh := by
  intro hq x k hs
  have hnh := gdexecQconfNharts boot d0 im nh GD hq
  obtain ⟨l, hl⟩ := someOfIsSome hs
  cases hrow : GD.gdG.gxProg[x]? with
  | none => simp [gxLbl, hrow] at hl
  | some row =>
    have := lookup_lt_Some hrow
    omega

/-- THE RESIDUE, with the drift removed: the writer scope and the witness set. -/
def wsupplyRes (boot : Nat → Pexv6) (d0 : Efab) (G : Gexec) (_N : Nat) : Prop :=
  (∀ x k lb, gxLbl G (x, k) = some lb → lbIsW lb = true →
     ∃ cpu m rs fn ib, boot x = .PHart cpu m rs fn ib) ∧
  (∃ (W : Geid → Prop) (tm : Nat → Nat → List Nat),
     WPolocClosed G W ∧ wubA G W ∧
     -- the PER-HART ACCUMULATED taint, monotone along each row
     (∀ x k, tm x k ⊆ tm x (k + 1)) ∧
     wsiteSupply boot d0 G W tm)

/-- THE DISK SCOPE, MADE EXPLICIT. -/
theorem wsupplyResNoDiskWrites (boot : Nat → Pexv6) (d0 : Efab) (G : Gexec) (N : Nat)
    (x : Nat) :
    wsupplyRes boot d0 G N →
    (∀ cpu m rs fn ib, boot x ≠ .PHart cpu m rs fn ib) →
    ∀ k lb, gxLbl G (x, k) = some lb → lbIsW lb = false := by
  rintro ⟨hw, _⟩ hnp k lb hl
  cases hb : lbIsW lb with
  | false => rfl
  | true =>
    exfalso
    obtain ⟨cpu, m, rs, fn, ib, hp⟩ := hw x k lb hl hb
    exact hnp cpu m rs fn ib hp

theorem wsupplyOfGwrow (boot : Nat → Pexv6) (d0 : Efab) (G : Gexec) (N : Nat) :
    gwrowGmo G →
    (∀ x k, (gxLbl G (x, k)).isSome → x < N) →
    wsupplyRes boot d0 G N →
    ∃ W tm, wsupply boot d0 G W tm N := by
  rintro h14 h1 ⟨h2, W, tm, h3, h4, h5, h6⟩
  exact ⟨W, tm, h14, h1, h2, h3, h4, h5, h6⟩

/-- THE ONE STEP THE ORBIT COSTS, NAMED. -/
def wsupplyOrbitPull (boot : Nat → Pexv6) (d0 : Efab) (N : Nat) : Prop :=
  ∀ GD GD', gdEquiv GD GD' →
    (∃ W tm, wsupply boot d0 GD'.gdG W tm N) →
    ∃ W tm, wsupply boot d0 GD.gdG W tm N

theorem wsupplyOfPrenorm (boot : Nat → Pexv6) (d0 : Efab) (im : Image) (nh N : Nat)
    (GD : Gdexec) :
    nh ≤ N →
    rvwmoMinusDepsConsistent GD →
    gdexecQconf boot d0 im nh GD →
    wsupplyOrbitPull boot d0 N →
    (∀ GD' : Gdexec,
       rvwmoMinusDepsConsistent GD' → gdexecQconf boot d0 im nh GD' →
       wsupplyRes boot d0 GD'.gdG N) →
    killWwK2 GD → killWwK3 GD → killWwK4 GD →
    ∃ W tm, wsupply boot d0 GD.gdG W tm N := by
  intro hnN hcons hq hpull hres hK2 hK3 hK4
  obtain ⟨GD', heq, hrow⟩ := normalizeWw GD hcons hK2 hK3 hK4
  obtain ⟨π, hrows, _, hdeps, hcons'⟩ := id heq
  have hq' := gdexecQconfRen π boot d0 im nh GD GD' hrows hdeps hq
  apply hpull GD GD' heq
  refine wsupplyOfGwrow boot d0 GD'.gdG N hrow ?_ (hres GD' hcons' hq')
  intro x k hs
  have := qconfHartBound boot d0 im nh GD' hq' x k hs
  omega

section capstone

open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode
open Language.Notation PrimStep

/-- THE CAPSTONE, with (R-2) SPLIT into (R-2a) `wsupplyRes` and (R-2b) `gwrowGmo`
(deviations 1, 4). -/
theorem xv6RvwmoSafeModuloL2'' (hlc : HasLC) (GF : BundledGFunctors) [MachGpreS hlc GF]
    [WeakGpreS GF]
    (gen : Nat) (σ0 : WGState) (D : CPU → List Register) (hD : ∀ c, (D c).Nodup)
    (Nm : Int → Int → Namespace) (P : Int → Int → Prop) :
    freshEra gen σ0 →
    wpPackage hlc GF gen σ0 D →
    (∀ a base, P a base → wpPackageProt hlc GF gen σ0 D (Nm a base) a base) →
    -- THE FETCH-VIEW PREMISE (deviation 4)
    (∀ ρ, rtc epfRun (epInit gen, σ0) ρ → efetchItvOk ρ.1 ρ.2) →
    -- (R-1)
    l2Claim (xboot σ0) (efInit σ0.wgdev) (imgZ σ0.wgimg) (xN σ0) P (badRun gen σ0) →
    -- (R-2a) the witness set and the booted-hart bounds
    (∀ GD : Gdexec,
       rvwmoMinusDepsConsistent GD →
       gdexecQconf (xboot σ0) (efInit σ0.wgdev) (imgZ σ0.wgimg) (xN σ0) GD →
       wsupplyRes (xboot σ0) (efInit σ0.wgdev) GD.gdG (xN σ0)) →
    -- (R-2b) the write-order gate
    (∀ GD : Gdexec,
       rvwmoMinusDepsConsistent GD →
       gdexecQconf (xboot σ0) (efInit σ0.wgdev) (imgZ σ0.wgimg) (xN σ0) GD →
       gwrowGmo GD.gdG) →
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
  fun hfr hwp hwpp hcov hl2 hres hrow =>
    xv6RvwmoSafeModuloL2' hlc GF gen σ0 D hD Nm P hfr hwp hwpp hcov hl2
      (fun GD hcons hq =>
        wsupplyOfGwrow _ _ _ _ (hrow GD hcons hq)
          (qconfHartBound _ _ _ _ GD hq) (hres GD hcons hq))

/-- … and the same capstone with (R-2b) traded for the orbit pull-back and the three
residuals (deviations 1, 4). -/
theorem xv6RvwmoSafeModuloL2''Prenorm (hlc : HasLC) (GF : BundledGFunctors)
    [MachGpreS hlc GF] [WeakGpreS GF]
    (gen : Nat) (σ0 : WGState) (D : CPU → List Register) (hD : ∀ c, (D c).Nodup)
    (Nm : Int → Int → Namespace) (P : Int → Int → Prop) :
    freshEra gen σ0 →
    wpPackage hlc GF gen σ0 D →
    (∀ a base, P a base → wpPackageProt hlc GF gen σ0 D (Nm a base) a base) →
    -- THE FETCH-VIEW PREMISE (deviation 4)
    (∀ ρ, rtc epfRun (epInit gen, σ0) ρ → efetchItvOk ρ.1 ρ.2) →
    l2Claim (xboot σ0) (efInit σ0.wgdev) (imgZ σ0.wgimg) (xN σ0) P (badRun gen σ0) →
    (∀ GD : Gdexec,
       rvwmoMinusDepsConsistent GD →
       gdexecQconf (xboot σ0) (efInit σ0.wgdev) (imgZ σ0.wgimg) (xN σ0) GD →
       wsupplyRes (xboot σ0) (efInit σ0.wgdev) GD.gdG (xN σ0)) →
    wsupplyOrbitPull (xboot σ0) (efInit σ0.wgdev) (xN σ0) →
    (∀ GD : Gdexec,
       rvwmoMinusDepsConsistent GD →
       gdexecQconf (xboot σ0) (efInit σ0.wgdev) (imgZ σ0.wgimg) (xN σ0) GD →
       killWwK2 GD ∧ killWwK3 GD ∧ killWwK4 GD) →
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
  fun hfr hwp hwpp hcov hl2 hres hpull hkill =>
    xv6RvwmoSafeModuloL2' hlc GF gen σ0 D hD Nm P hfr hwp hwpp hcov hl2
      (fun GD hcons hq =>
        wsupplyOfPrenorm (xboot σ0) (efInit σ0.wgdev) (imgZ σ0.wgimg) (xN σ0) (xN σ0) GD
          (Nat.le_refl _) hcons hq hpull hres (hkill GD hcons hq).1 (hkill GD hcons hq).2.1
          (hkill GD hcons hq).2.2)

end capstone

end Weak
