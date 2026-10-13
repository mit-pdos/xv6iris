/-
Weak: **(W-1)'s PROGRESS AND (W-2) `wub`, AS ADEQUACY FACTS** (a leaf).

Rocq: `iris/WeakRvwmoProgress.v` @ xxvzwolszwmp.

## The Rocq header, in substance

`WeakRvwmoWalk` closed (R-2) to a per-state certification policy whose honest ledger is two
items: (W-1) `wpol` (the read/register policy, "carrying (P-4) progress") and (W-2) `wub`
(`WeakRvwmoCert3.witFenceUb` at the next position).  This leaf:

  §1–§2  PROGRESS, FROM TIER 1.  The adequacy theorem's progress conjunct (every thread of every
      erased-reachable configuration is `Reducible`) becomes, at every pf-reachable
      configuration, "the hart's own program state can take a `pstepEv` step"
      (`epfProgressHart`), and hence at every CERTIFIED CANDIDATE (`RunData`) every hart's
      current `Pexv6` can step (`certProgress`).
  §3  THE BRIDGE the read answer needs: the program half is ANSWER-GENERIC, so progress plus
      "the node is a plain load node of width `w`" gives a step at EVERY `tvs2` of width `w`
      (`stepAtChosenAnswer`); `stepAtSameValues` is the re-indexing twin.
  §4  (W-2) `wub`, DERIVED: in general a witness has no publishing fence over its own backward
      step (`wubOfWitness`, `noFenceOverBackstep`); at the walk, the widened graph-side datum
      `wrowInLog'` says hart `x` has NO witness at all, so `witFenceUb` is vacuous (`wubOfRow`,
      `cpolCtxOfCtrace`).
  §5  THE RESTATEMENTS: `wlkSegOfCert'` (§4.1 of the walk with (W-2) gone), `walkSegData'` (the
      per-state residue), `walkPolicyOfSegData'`, `walkSupplyOfWp'`,
      `xv6RvwmoSafeModuloWalk'`; `walkSegDataFlat` is the old, over-quantified residue (kept as
      the subject of the Rocq `WeakRvwmoWalk2.v` refutation).

§6 (the `Print Assumptions` audit) and §7 (the ledger) are Rocq commands/comments.

## Deviations from Rocq

1. NAMES / VOCABULARY as `WeakRvwmoWalk` deviation 1 and `WeakRvwmoWalk3` deviation 1
   (explicit `hlc GF` with `[MachGpreS hlc GF] [WeakGpreS GF]`; `D : CPU → List Register` with
   `hD : ∀ c, (D c).Nodup` wherever the adequacy export is called; `reducible e σ` ↦
   `Reducible (e, σ)`; `rtc erased_step` ↦ `-·->ₜₚ*`; `d0 = wgdev σ0` ↦ `d0 = efInit σ0.wgdev`;
   `wgdev σ0` in the capstone ↦ `efInit σ0.wgdev`; `Forall Q l` ↦ `∀ lb ∈ l, Q lb`).
2. THE FABRIC (WeakEvPf deviation 9): the program step's device argument is an `Efab`, not a
   `dev_state`.  `reducibleHartPstep` is stated at ANY fabric `F` with `F.efDev = σ.wgdev`
   (extra premise; Rocq: at `wgdev σ`), and `epfProgressHart` at the pf machine's own fabric
   `efabOf P' σ'` (Rocq: `wgdev σ'`) — the fabric `(ecfgOf P' σ').pcDev` that `certProgress`
   needs.  `eprimStep` has no corpse arm in Lean (four arms; the dead-thread branch is the
   second disjunct of the `Sail` arm, refuted by `ethreadLive` as in Rocq).
3. O2 / STAGE C.  (a) `certProgress` CARRIES the fetch-view premise
   `∀ ρ, rtc epfRun (epInit gen, σ0) ρ → efetchItvOk ρ.1 ρ.2` (the language lift
   `wpPfRtcEpfRtc` needs it; `WeakRvwmoGlue` deviation 4), placed after `freshEra`, and replays
   `RunData`'s PINNED program LTS through `WeakAxRealize.execWfPfRunPin` (`WeakRvwmoGlue`
   deviation 5).  (b) `wlkSegOfCert'` takes `WeakRvwmoCert2.esPin St.cstC.cdImg es` after
   `LDev ∉ es.map Prod.fst` (`wlkSegOfCert`'s premise, `WeakRvwmoWalk` deviation 2), and
   `walkSegData'` gains the matching conjunct right after its device-quiet conjunct.
   (c) `xv6RvwmoSafeModuloWalk'` carries the fetch-view premise after the WP package premises
   (as `WeakRvwmoWalk3.xv6RvwmoSafeModuloWalk`).  (d) `walkSegDataFlat`'s `cpolp` is the
   tree's pinned pair policy (`WeakRvwmoCert3` deviation 4); its `wpolFlat` keeps Rocq's `cblk`.

**Rocq → Lean name map.**  `estep_exists` `estepExists`, `reducible_hart_pstep`
`reducibleHartPstep`, `epf_progress_hart` `epfProgressHart`, `cert_progress` `certProgress`,
`load_node` `loadNode`, `step_at_chosen_answer` `stepAtChosenAnswer`, `step_at_same_values`
`stepAtSameValues`, `gmo_lt_asym` `gmoLtAsym`, `no_fence_over_backstep` `noFenceOverBackstep`,
`fhook_gfence_covers` `fhookGfenceCovers`, `wub_of_witness` `wubOfWitness`, `wrow_in_log'`
`wrowInLog'`, `wrow_in_log'_weaken` `wrowInLog'Weaken`, `wrow_no_wit` `wrowNoWit`,
`wit_fence_ub_vacuous` `witFenceUbVacuous`, `wub_of_row` `wubOfRow`, `cpol_ctx_of_ctrace`
`cpolCtxOfCtrace`, `wlk_seg_of_cert'` `wlkSegOfCert'`, `walk_seg_data'` `walkSegData'`,
`walk_policy_of_seg_data'` `walkPolicyOfSegData'`, `walk_supply_of_wp'` `walkSupplyOfWp'`,
`xv6_rvwmo_safe_modulo_walk'` `xv6RvwmoSafeModuloWalk'`, `walk_seg_data_flat`
`walkSegDataFlat`.

**File-qualified names:** none (no name of this file is in `notes/weak-port-dupnames.json`; no
Lean-only helpers).

**Dropped:** none (Rocq 23 declarations; Lean 23).
-/
import Weak.WeakRvwmoWalk3

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D
open Wlabel

/-- The parked-fence field, abbreviated (as in `WeakRvwmoCert2`). -/
local notation "Ofence" => Option (Bool × Bool × Bool × Bool)

section progress

open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode
open Language.Notation PrimStep

/-! # 1. PROGRESS AT THE MACHINE -/

def estepExists (p : Pexv6) (d : Efab) : Prop :=
  ∃ (l : Wlabel) (p' : Pexv6) (d' : Efab), pstepEv p d l p' d'

/-- THE TRANSLATION (deviation 2: at any fabric over σ's device states).  The dead-thread
branch is refuted by `ethreadLive`. -/
theorem reducibleHartPstep (gen : Nat) (c : CPU) (m : SailM Unit) (fn : Ofence) (σ : WGState)
    (F : Efab) :
    F.efDev = σ.wgdev →
    ethreadLive σ gen →
    Reducible (EExpr.Sail gen c m fn, σ) →
    estepExists (.PHart c m (σ.wgregs c) fn (σ.wgib c)) F := by
  rintro hF hlive ⟨κ, e', σ', efs, hstep⟩
  obtain ⟨-, -, ⟨-, hcy⟩ | ⟨hnl, -⟩⟩ := hstep
  · obtain ⟨l, m', ors, fn', d', oib, obar, -, hph, -, -⟩ :=
      ecycleStepPstepHart gen σ c m fn e' σ' F hF hcy
    exact ⟨l, .PHart c m' (ors.getD (σ.wgregs c)) fn' (oib.getD (σ.wgib c)),
      { F with efDev := d' }, rfl, ors, oib, obar, rfl, rfl, hph⟩
  · exact (hnl hlive).elim

/-- THE EXPORT (deviations 1-2).  Under the WP package, at EVERY pf-reachable configuration of
the fresh era, EVERY hart's own program state can take a `pstepEv` step. -/
theorem epfProgressHart (hlc : HasLC) (GF : BundledGFunctors) [MachGpreS hlc GF]
    [WeakGpreS GF] (gen : Nat) (σ0 : WGState) (D : CPU → List Register)
    (hD : ∀ c, (D c).Nodup) :
    freshEra gen σ0 →
    wpPackage hlc GF gen σ0 D →
    ∀ (P' : Epool) (σ' : WGState),
      rtc epfRun (epInit gen, σ0) (P', σ') →
      ∀ c : CPU,
        estepExists
          (.PHart c (ehartM (P'.epH c)) (σ'.wgregs c) (ehartFn (P'.epH c)) (σ'.wgib c))
          (efabOf P' σ') := by
  rintro ⟨hgen, hpow, hgen0, hlog, hws⟩ hwp P' σ' hrun c
  have hlive0 : ethreadLive σ0 gen := ⟨hpow, by rw [hgen0, hgen]⟩
  obtain ⟨hlive', hgen'⟩ := epfRunLive gen (epInit gen, σ0) (P', σ') hlive0 rfl hrun
  have herased : (epowerFork gen, σ0) -·->ₜₚ* (epoolList P', σ') := by
    have he := epfRtcErased (epInit gen, σ0) (P', σ') hrun
    rw [show (epInit gen, σ0).1 = epInit gen from rfl, epoolListInit] at he
    exact he
  have hin : ehexpr P' c ∈ epoolList P' := elem_of_list_lookup_2 (epoolListHartLookup P' c)
  have hred := weakEvAdequacyReducible (hlc := hlc) (GF := GF) gen σ0 D hD hgen hpow hgen0 hlog
    hws hwp (epoolList P') σ' (ehexpr P' c) herased hin
  unfold ehexpr at hred
  rw [ehexpSail, show P'.epGen = gen from hgen'] at hred
  exact reducibleHartPstep gen c _ _ σ' (efabOf P' σ') rfl hlive' hred

/-! # 2. PROGRESS AT A CERTIFIED CANDIDATE -/

/-- Rocq `cert_progress` (deviations 1-3). -/
theorem certProgress (hlc : HasLC) (GF : BundledGFunctors) [MachGpreS hlc GF] [WeakGpreS GF]
    (gen : Nat) (σ0 : WGState) (D : CPU → List Register) (hD : ∀ c, (D c).Nodup)
    (boot : Nat → Pexv6) (d0 : Efab) (N : Nat) (G : Gexec)
    (c : Cand) (pst : Nat → List Pexv6) (dv : Nat → Efab) :
    freshEra gen σ0 →
    -- THE FETCH-VIEW PREMISE (deviation 3a)
    (∀ ρ, rtc epfRun (epInit gen, σ0) ρ → efetchItvOk ρ.1 ρ.2) →
    (List.range' 0 N).map boot = epsInit σ0 →
    d0 = efInit σ0.wgdev →
    G.gxImg = imgZ σ0.wgimg →
    wpPackage hlc GF gen σ0 D →
    RunData boot d0 N G c pst dv →
    ∀ (cc : CPU) (p : Pexv6),
      (pst c.cdTr.length)[cc.val]? = some p →
      estepExists p (dv c.cdTr.length) := by
  intro hfr hcov hb1 hb2 hb3 hwp ⟨hcons, himg, hpst0, hdv0, hprog⟩ cc p hp
  obtain ⟨hgen, hpow, hgen0, hlog, hws⟩ := hfr
  have hlive : ethreadLive σ0 gen := ⟨hpow, by rw [hgen0, hgen]⟩
  obtain ⟨hwf, -, heximg⟩ := srvwmoRealizable c hcons
  obtain ⟨cf, hrun, hpg, hdev, -⟩ :=
    execWfPfRunPin pstepEv pclsEv c.cdImg pst dv (candExec c) pclsEvEqr heximg hwf hprog
  rw [heximg, himg, hb3, hpst0, hb1, hdv0, hb2, ← ecfgOfInit gen σ0 hlog hws] at hrun
  obtain ⟨P', σ', hr, heq⟩ := wpPfRtcEpfRtc (epInit gen) σ0 cf hlive hcov hrun
  subst heq
  rw [candExTr] at hpg hdev
  -- the fabric: `dv` at the endpoint IS the reached configuration's fabric
  rw [← hdev]
  -- the program state: the candidate's `pst` entry IS the hart's agent
  rw [← hpg, List.getElem?_map, show (ecfgOf P' σ').pcAgs = eags P' σ' from rfl, eagsHart]
    at hp
  simp only [Option.map_some, Option.some.injEq] at hp
  subst hp
  exact epfProgressHart hlc GF gen σ0 D hD ⟨hgen, hpow, hgen0, hlog, hws⟩ hwp P' σ' hr cc

end progress

/-! # 3. THE BRIDGE: THE STEP AT THE CHOSEN ANSWER -/

/-- "The node is a plain load node of width `w` at `(aq, base)`" — read off the steps it
admits. -/
def loadNode (p : Pexv6) (d : Efab) (aq : Bool) (base : Int) (w : Nat) : Prop :=
  ∀ (l : Wlabel) (p' : Pexv6) (d' : Efab),
    pstepEv p d l p' d' →
    ∃ tvs : List (Nat × BitVec 8), l = LLoad aq false base tvs [] ∧ tvs.length = w

theorem stepAtChosenAnswer (cpu : CPU) (m : SailM Unit) (rs : RegFile) (fn : Ofence)
    (ib : Ibch) (d : Efab) (aq : Bool) (base : Int) (w : Nat)
    (tvs2 : List (Nat × BitVec 8)) :
    estepExists (.PHart cpu m rs fn ib) d →
    loadNode (.PHart cpu m rs fn ib) d aq base w →
    tvs2.length = w →
    ∃ (m2 : SailM Unit) (rs' : RegFile) (fn' : Ofence) (ib' : Ibch) (d' : Efab),
      pstepEv (.PHart cpu m rs fn ib) d (LLoad aq false base tvs2 [])
        (.PHart cpu m2 rs' fn' ib') d' := by
  rintro ⟨l, p', d', hst⟩ hnode hlen
  obtain ⟨tvs, rfl, htvs⟩ := hnode l p' d' hst
  obtain ⟨m', rs', fn', ib', rfl⟩ := pstepEvPhart cpu m rs fn ib d _ p' d' hst
  obtain ⟨m2, hst2⟩ :=
    pstepEvLoadSubst cpu m rs fn ib d aq base tvs tvs2 m' rs' fn' ib' d' hst (by omega)
  exact ⟨m2, rs', fn', ib', d', hst2⟩

/-- THE RE-INDEXING TWIN: at the SAME values the successor node does not move. -/
theorem stepAtSameValues (p : Pexv6) (d : Efab) (aq : Bool) (base : Int)
    (tvs tvs2 : List (Nat × BitVec 8)) (p' : Pexv6) (d' : Efab) :
    pstepEv p d (LLoad aq false base tvs []) p' d' →
    tvs2.map Prod.snd = tvs.map Prod.snd →
    pstepEv p d (LLoad aq false base tvs2 []) p' d' :=
  pstepEvTsLoad p d aq base tvs tvs2 p' d'

/-! # 4. (W-2) `wub`, DISCHARGED -/

/-! ## 4.1 The general fact: a witness has no publishing fence over its own backward step -/

theorem gmoLtAsym (G : Gexec) (e1 e2 : Geid) : gmoLt G e1 e2 → ¬ gmoLt G e2 e1 := by
  rintro ⟨-, -, h1⟩ ⟨-, -, h2⟩
  omega

theorem noFenceOverBackstep (G : Gexec) (e z : Geid) :
    gppoGmo G → gmoLt G z e → ¬ gfenceCovers G e z :=
  fun hppo hlt hfc => gmoLtAsym G z e hlt (hppo e z (.inr (.inl hfc)))

/-- The hook IS rule 4's fence, at a read/read pair of one hart. -/
theorem fhookGfenceCovers (G : Gexec) (e r : Geid) :
    e.1 = r.1 → glblIs G e lbIsR → glblIs G r lbIsR →
    fhook G r (e.2 + 1) true → gfenceCovers G e r := by
  rintro hag he hr ⟨kf, pr, pw, sr, sw, h1, h2, h3, h4, h5⟩
  refine ⟨pr, pw, sr, sw, ⟨hag, by omega, kf, by omega, h2, by rw [hag]; exact h3⟩,
    .inl ⟨he, h4⟩, .inl ⟨hr, h5⟩⟩

/-- (W-2)'s CONTENT, in general. -/
theorem wubOfWitness (G : Gexec) (e r : Geid) :
    gppoGmo G → e.1 = r.1 →
    glblIs G e lbIsR → glblIs G r lbIsR →
    gmoLt G r e →
    ¬ fhook G r (e.2 + 1) true :=
  fun hppo hag he hr hlt hfh =>
    noFenceOverBackstep G e r hppo hlt (fhookGfenceCovers G e r hag he hr hfh)

/-! ## 4.2 At the WALK: `wub` is VACUOUS -/

def wrowInLog' (G : Gexec) (x : Nat) (n : Nat) : Prop :=
  ∀ k : Nat, WeakRvwmoWalk.wsrcLe G n (x, k)

theorem wrowInLog'Weaken (G : Gexec) (x : Nat) (n : Nat) :
    wrowInLog' G x n → wrowInLog G x n :=
  fun h k _ => h k

theorem wrowNoWit (G : Gexec) (x : Nat) (n k : Nat) :
    wrowInLog' G x n → ¬ wwit G n (x, k) :=
  fun h => wsrcLeNotWwit G n (x, k) (h k)

/-- THE VACUITY, once. -/
theorem witFenceUbVacuous (G : Gexec) (x : Nat) (n : Nat) (c : Cand) (ev : Nat → Geid)
    (k : Nat) :
    wrowInLog' G x n → witFenceUb G c ev (wwit G n) (x, k) := by
  intro hrow p s _ hW hag _
  exfalso
  have heq : ev p = (x, (ev p).2) := Prod.ext hag rfl
  rw [heq] at hW
  exact wrowNoWit G x n _ hrow hW

/-- (W-2), DISCHARGED. -/
theorem wubOfRow (G : Gexec) (x : Nat) (n : Nat) :
    wrowInLog' G x n → wub G (wwit G n) x :=
  fun hrow _ _ ev' _ => witFenceUbVacuous G x n _ ev' _ hrow

/-- ... and the same argument removes `witFenceUb` from the CONTEXT. -/
theorem cpolCtxOfCtrace (G : Gexec) (x : Nat) (n : Nat) (c : Cand) (ev : Nat → Geid) :
    wrowInLog' G x n →
    CtracePrefix G c ev (wwit G n) →
    poisOkHart G c ev x →
    cpolCtx G (wwit G n) x c :=
  fun hrow hpc hpd => ⟨ev, hpc, witFenceUbVacuous G x n c ev _ hrow, hpd⟩

/-! # 5. THE RESTATEMENTS, AT THE REPAIRED INTERFACE -/

/-! ## 5.1 The segment, with (W-2) gone -/

/-- Rocq `wlk_seg_of_cert'` (deviation 3b). -/
theorem wlkSegOfCert' (G : Gexec) (n : Nat) (x : Nat) (cpu : CPU) (d0 : Efab) (T : List Nat)
    (Nd : Nat → CPU → SailM Unit → Prop) (k0 kz : Nat) (ws0 : Wstate) (rowseg : List Lbl)
    (es : List Eitem) (pfin : Pexv6) (m0 : SailM Unit) (rs10 : RegFile) (fn0 : Ofence)
    (ib0 : Ibch) (St : CycState) (m20 : SailM Unit) (rs20 : RegFile) (fn20 : Ofence)
    (ib20 : Ibch) :
    rvwmoMinusConsistent G →
    WPolocClosed G (wwit G n) →
    wrowInLog' G x n →
    wrdsFree d0 T →
    wndOk cpu d0 (wQ G d0 T Nd n x k0 kz) Nd →
    hemit (fun _ => d0) k0 ws0 rowseg (.PHart cpu m0 rs10 fn0 ib0) es pfin →
    (∀ kd ba bs sa sv, LDev kd ba bs sa sv ∉ es.map Prod.fst) →
    WeakRvwmoCert2.esPin St.cstC.cdImg es →
    (∀ i lb, rowseg[i]? = some lb → wQ G d0 T Nd n x k0 kz (k0 + i) lb) →
    cstOk d0 St →
    wctx G n x kz k0 St.cstC →
    (St.cstPst (cdEnd St.cstC))[x]? = some (.PHart cpu m20 rs20 fn20 ib20) →
    Nd k0 cpu m0 →
    csync T m0 rs10 fn0 ib0 m20 rs20 fn20 ib20 →
    ((candLastSt St.cstC).msWs x).wRelp = ws0.wRelp →
    ∃ (St' : CycState) (tradd : List Estep),
      segStep d0 ⟨x, rowseg, cdEnd St.cstC, tradd⟩ St St' ∧
      wctx G n x kz (k0 + rowseg.length) St'.cstC ∧
      St'.cstC.cdImg = St.cstC.cdImg ∧
      St'.cstPst 0 = St.cstPst 0 ∧
      St'.cstDv 0 = St.cstDv 0 :=
  fun hcons hpc hrow hrdsf hndok hem hdev hes hQ hok hctx hp hnd hsync hrelp =>
    wlkSegOfCert G n x cpu d0 T Nd k0 kz ws0 rowseg es pfin m0 rs10 fn0 ib0 St m20 rs20 fn20
      ib20 hcons hpc (wubOfRow G x n hrow) hrdsf hndok hem hdev hes hQ hok hctx hp hnd hsync
      hrelp

/-! ## 5.2 THE PER-STATE RESIDUE, REPAIRED -/

/-- Rocq `walk_seg_data'` (deviation 3b: the `esPin` conjunct). -/
def walkSegData' (boot : Nat → Pexv6) (d0 : Efab) (N : Nat) (G : Gexec) : Prop :=
  ∀ St n, wlkInv boot d0 N G St n → n < (gwrites G).length →
  ∃ (x : Nat) (cpu : CPU) (k0 : Nat) (ws0 : Wstate) (pre : List Lbl)
    (rl : Bool) (base : Int) (vs : List (BitVec 8)) (kc : WmClass)
    (es : List Eitem) (pfin : Pexv6) (m0 : SailM Unit) (rs10 rs20 : RegFile)
    (fn0 : Ofence) (ib0 : Ibch) (w : Geid) (T : List Nat)
    (Nd : Nat → CPU → SailM Unit → Prop),
    -- the graph side: the segment's exit IS `G`'s `(n+1)`-st write
    gwriteAt G (n + 1) = some w ∧
    WeakRvwmoKillArms.gmsg G w = some ⟨base, vs, some x, kc⟩ ∧
    (∀ lb ∈ pre, lbIsW lb = false) ∧
    -- THE EMISSION — the progress-carrying input — and its fabric quiet
    hemit (fun _ => d0) k0 ws0 (pre ++ [Lbl.LStore rl base vs kc])
      (.PHart cpu m0 rs10 fn0 ib0) es pfin ∧
    (∀ kd ba bs sa sv, LDev kd ba bs sa sv ∉ es.map Prod.fst) ∧
    WeakRvwmoCert2.esPin St.cstC.cdImg es ∧
    -- THE SITE DATA, INDEXED BY ROW POSITION
    (∀ i lb, (pre ++ [Lbl.LStore rl base vs kc])[i]? = some lb →
       wQ G d0 T Nd n x k0 (k0 + pre.length) (k0 + i) lb) ∧
    -- the walk's state, ALIGNED to the segment's first position
    wctx G n x (k0 + pre.length) k0 St.cstC ∧
    (St.cstPst (cdEnd St.cstC))[x]? = some (.PHart cpu m0 rs20 fn0 ib0) ∧
    dregAgree (fun nn => nn ∉ T) rs10 rs20 ∧
    ((candLastSt St.cstC).msWs x).wRelp = ws0.wRelp ∧
    -- the two side conditions the `csync` iteration names
    wrdsFree d0 T ∧
    wndOk cpu d0 (wQ G d0 T Nd n x k0 (k0 + pre.length)) Nd ∧
    Nd k0 cpu m0 ∧
    -- the witness set's side conditions
    WPolocClosed G (wwit G n) ∧
    wub G (wwit G n) x

theorem walkPolicyOfSegData' (boot : Nat → Pexv6) (d0 : Efab) (N : Nat) (G : Gexec) :
    rvwmoMinusConsistent G → walkSegData' boot d0 N G → walkPolicy boot d0 N G := by
  intro hcons hdata St n hinv hn
  obtain ⟨x, cpu, k0, ws0, pre, rl, base, vs, kc, es, pfin, m0, rs10, rs20, fn0, ib0, w, T, Nd,
    hw, hm, hpre, hem, hdev, hes, hQ, hctx, hp, hag, hrelp, hrdsf, hndok, hnd, hpc, hub⟩ :=
    hdata St n hinv hn
  have hok : cstOk d0 St := hinv.1
  obtain ⟨St', tradd, hstep, -, himg, hpst, hdv⟩ :=
    wlkSegOfCert G n x cpu d0 T Nd k0 (k0 + pre.length) ws0
      (pre ++ [Lbl.LStore rl base vs kc]) es pfin m0 rs10 fn0 ib0 St m0 rs20 fn0 ib0 hcons hpc
      hub hrdsf hndok hem hdev hes hQ hok hctx hp hnd (.inl ⟨rfl, rfl, rfl, hag⟩) hrelp
  exact ⟨x, rl, base, vs, kc, pre, tradd, St', w, hw, hm, hpre, hstep, himg, hpst, hdv⟩

/-! ## 5.3 THE WALK'S THEOREM, at the repaired residue -/

theorem walkSupplyOfWp' (boot : Nat → Pexv6) (d0 : Efab) (im : Image) (nh : Nat) (N : Nat) :
    (∀ GD : Gdexec,
       rvwmoMinusDepsConsistent GD → gdexecQconf boot d0 im nh GD →
       walkSegData' boot d0 N GD.gdG) →
    walkSupply boot d0 im nh N :=
  fun hdata => walkSupplyOfPolicy boot d0 im nh N
    (fun GD hcons hq => walkPolicyOfSegData' boot d0 N GD.gdG hcons.1 (hdata GD hcons hq))

/-! ## 5.4 THE CAPSTONE, with (R-2) at the repaired residue -/

section capstone

open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode
open Language.Notation PrimStep

/-- Rocq `xv6_rvwmo_safe_modulo_walk'` (deviations 1, 3c). -/
theorem xv6RvwmoSafeModuloWalk' (hlc : HasLC) (GF : BundledGFunctors) [MachGpreS hlc GF]
    [WeakGpreS GF]
    (gen : Nat) (σ0 : WGState) (D : CPU → List Register) (hD : ∀ c, (D c).Nodup)
    (Nm : Int → Int → Namespace) (P : Int → Int → Prop) :
    freshEra gen σ0 →
    wpPackage hlc GF gen σ0 D →
    (∀ a base, P a base → wpPackageProt hlc GF gen σ0 D (Nm a base) a base) →
    -- THE FETCH-VIEW PREMISE (deviation 3c)
    (∀ ρ, rtc epfRun (epInit gen, σ0) ρ → efetchItvOk ρ.1 ρ.2) →
    -- (R-1)
    l2Claim (xboot σ0) (efInit σ0.wgdev) (imgZ σ0.wgimg) (xN σ0) P (badRun gen σ0) →
    -- (R-2), at the repaired, position-indexed residue
    (∀ GD : Gdexec,
       rvwmoMinusDepsConsistent GD →
       gdexecQconf (xboot σ0) (efInit σ0.wgdev) (imgZ σ0.wgimg) (xN σ0) GD →
       walkSegData' (xboot σ0) (efInit σ0.wgdev) (xN σ0) GD.gdG) →
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
  fun hfr hwp hwpp hcov hl2 hdata =>
    xv6RvwmoSafeModulo hlc GF gen σ0 D hD Nm P hfr hwp hwpp hcov hl2
      (walkSupplyOfWp' _ _ _ _ _ hdata)

end capstone

/-! ## 5.5 THE OLD, OVER-QUANTIFIED RESIDUE (deviation 3d) -/

def walkSegDataFlat (boot : Nat → Pexv6) (d0 : Efab) (N : Nat) (G : Gexec) : Prop :=
  ∀ St n, wlkInv boot d0 N G St n → n < (gwrites G).length →
  ∃ (x : Nat) (cpu : CPU) (T : List Nat) (Q : Lbl → Prop)
    (k0 : Nat) (ws0 : Wstate) (pre : List Lbl) (rl : Bool) (base : Int)
    (vs : List (BitVec 8)) (kc : WmClass) (es : List Eitem) (pfin : Pexv6)
    (m0 : SailM Unit) (rs10 rs20 : RegFile) (fn0 : Ofence) (ib0 : Ibch)
    (w : Geid),
    gwriteAt G (n + 1) = some w ∧
    WeakRvwmoKillArms.gmsg G w = some ⟨base, vs, some x, kc⟩ ∧
    (∀ lb ∈ pre, lbIsW lb = false) ∧
    hemit (fun _ => d0) k0 ws0 (pre ++ [Lbl.LStore rl base vs kc])
      (.PHart cpu m0 rs10 fn0 ib0) es pfin ∧
    (∀ lb ∈ pre ++ [Lbl.LStore rl base vs kc], Q lb) ∧
    cpolCtx G (wwit G n) x St.cstC ∧
    (St.cstPst (cdEnd St.cstC))[x]? = some (.PHart cpu m0 rs20 fn0 ib0) ∧
    dregAgree (fun nn => nn ∉ T) rs10 rs20 ∧
    ((candLastSt St.cstC).msWs x).wRelp = ws0.wRelp ∧
    wrowInLog' G x n ∧
    wpolFlat G (wwit G n) x cpu d0 T Q ∧
    cpolp x cpu d0 T (fun _ : Nat => cpolCtx G (wwit G n) x)
      (wclsAt G (wwit G n) x) (fun _ : Nat => Q)

end Weak
