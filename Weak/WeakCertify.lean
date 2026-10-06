/-
Weak: **the certification step relation and its two `wVcap` lemmas** (D8, slice 1).

Rocq: `iris/WeakCertify.v` @ xxvzwolszwmp (338 lines, 20 declarations).

The port of Promising-ARM's `lcertify/Certify.v` to this tree's full promising machine
(`WeakPromise.wpstep`).  THE RELATION: PARM's `certify_step tid = state_step tid ∪ write_step tid`
(Certify.v:38), as `wpAstepOf pstep i` (the non-`WPPromise` arms, whose fulfil arms consume an
EXISTING promise) united with `wpPfStep pstep pcls i` (the promise-free fragment, whose
`PFStore`/`PFRmw`/`PFExStore` arms are PARM's `write_step`: append at `log.length + 1` and consume
in the same step).  WHAT IT PROVES (Certify.v:128/144/166): `wVcap` is monotone along a
certifying run, and once `wVcap` has reached a promise's timestamp that promise can never be
fulfilled, because `fulfilOkD`'s EXT conjunct puts the pre-view (which dominates `wVcap`)
strictly below the fulfilled timestamp — the termination guard of the restriction simulation.
Finally a certifying run is a run of the full machine (from `cfgWf` alone, no `noPromises`).

**Deviations from Rocq.**

1. The section variables `pstep`, `pcls` are explicit arguments of the declarations that use
   them (tree convention); Rocq's `Global Arguments` make the same choice.
2. `is_Some o` ↦ `o.isSome = true` (as `Weak/AxGraph.lean`), in `rtcCertStepIsSome`.
3. O2 / D2 (Lean-only label `LIFetch`): `astepOkDelVcap` and `wpPfStepProm` /
   `wpPfStepRtcWpstepWf` have one more arm (`LIFetch` / `PFIFetch`, mapped to `WPIFetch`); it
   deletes no promise, so the arms are the trivial ones.
4. Rocq's head-style `rtc` inductions are tail inductions here (stdpp's `rtc` is the library
   closure built from the last step, `MachCSL.Rel`); statements unchanged.

**Name map (Rocq → Lean)** (none is a duplicated name):
`fulfil_ok_d_vcap` → `fulfilOkDVcap`; `astep_ok_del_vcap` → `astepOkDelVcap`;
`wp_cert_step` → `wpCertStep`; `prom_free` → `promFree`; `wp_certify` → `wpCertify`;
`no_promises_prom_free` → `noPromisesPromFree`; `wp_certify_prom_free` → `wpCertifyPromFree`;
`cert_step_shape` → `certStepShape`; `cert_step_lookup` → `certStepLookup`;
`rtc_cert_step_is_Some` → `rtcCertStepIsSome`; `cert_step_vcap` → `certStepVcap`;
`rtc_cert_step_vcap` → `rtcCertStepVcap`; `wp_pf_step_prom` → `wpPfStepProm`;
`cert_step_vcap_promise` → `certStepVcapPromise`;
`rtc_cert_step_vcap_promise` → `rtcCertStepVcapPromise`;
`rtc_cert_step_prom_free_vcap` → `rtcCertStepPromFreeVcap`;
`wp_pf_step_rtc_wpstep_wf` → `wpPfStepRtcWpstepWf`; `cert_step_rtc_wpstep` → `certStepRtcWpstep`;
`cfg_wf_cert_step` → `cfgWfCertStep`; `rtc_cert_step_rtc_wpstep` → `rtcCertStepRtcWpstep`.

Lean-only helper: `setLookupProm` (private).

Dropped: none.
-/
import Weak.WeakPromise
import Weak.WeakPromiseFact
import Weak.WeakPromiseBridge
import Weak.WeakRobustGraph
import Weak.WeakRobustL2
import Weak.WeakRobustBlocks

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std Wlabel

/-! ## A fulfil pushes its own timestamp above `wVcap` -/

/-- PARM's `writable` EXT with `view_pre ⊒ vcap`: `fulfilOkD`'s second conjunct. -/
theorem fulfilOkDVcap (ws : Wstate) (rl : Bool) (base : Int) (n ts vd : Nat) :
    fulfilOkD ws rl base n ts vd → ws.wVcap < ts := by
  rintro ⟨_, hext⟩
  have := fulfilVpreDVcap ws rl vd
  omega

/-- The rules that delete a promise put the deleted timestamp strictly above `wVcap`. -/
theorem astepOkDelVcap {P : Type} (img : Image) (log : List Wmsg) (i : Nat) (ag : Wpagent P)
    (l : Wlabel) (f : Wstate → Wstate) (ts : Nat) :
    astepOk img log i ag l f (some ts) → ag.paWs.wVcap < ts := by
  intro h
  cases l with
  | LSilent => obtain ⟨_, h⟩ := h; cases h
  | LLoad aq lat base tvs asrc => obtain ⟨_, _, h⟩ := h; cases h
  | LStore rl base data asrc vsrc =>
    obtain ⟨ts', k, _, _, hok, _, hdl⟩ := h
    cases hdl
    exact fulfilOkDVcap _ _ _ _ _ _ hok
  | LRmw aq rl base tvs data asrc vsrc =>
    obtain ⟨ts', k, _, _, _, _, _, hok, _, hdl⟩ := h
    cases hdl
    -- the rmw checks EXT on the state AFTER its read half
    have hlt := fulfilOkDVcap _ _ _ _ _ _ hok
    have hle := wsLeVcap _ _ (loadPostRunDLe ag.paWs aq (srcsView ag.paWs asrc) base
      (tvs.map Prod.fst))
    omega
  | LFence pr pw sr sw => obtain ⟨_, h⟩ := h; cases h
  | LDev => obtain ⟨_, h⟩ := h; cases h
  | LRegW rd srcs => obtain ⟨_, h⟩ := h; cases h
  | LCtrl srcs => obtain ⟨_, h⟩ := h; cases h
  | LInstr => obtain ⟨_, h⟩ := h; cases h
  -- THE RMW SPLIT (S2): the conditional write checks EXT on its OWN pre-state
  | LExLoad aq base tvs asrc => obtain ⟨_, _, h⟩ := h; cases h
  | LExStore rl base data asrc vsrc =>
    obtain ⟨ts', k, R, _, _, _, _, _, _, hok, _, hdl⟩ := h
    cases hdl
    exact fulfilOkDVcap _ _ _ _ _ _ hok
  | LIFetch base tvs => obtain ⟨_, _, h⟩ := h; cases h

/-! ## The certification relation -/

section certify

variable {P D : Type}
variable (pstep : P → D → Wlabel → P → D → Prop)
variable (pcls : P → Wlabel → Wstate → WmClass)

/-- PARM `Certify.v:38`.  No new promises: neither disjunct is `WPPromise`, and the pf
fragment's appends are consumed in the step that makes them. -/
def wpCertStep (i : Nat) (c c' : Wpcfg P D) : Prop :=
  wpAstepOf pstep i c c' ∨ ∃ l, wpPfStep pstep pcls i l c c'

/-- Agent `i`'s outstanding promises are discharged (PARM `lc.(Local.promises) = bot`). -/
def promFree (i : Nat) (c : Wpcfg P D) : Prop :=
  ∀ ag, c.pcAgs[i]? = some ag → ag.paProm = ∅

/-- PARM `Certify.v:48`. -/
def wpCertify (i : Nat) (c : Wpcfg P D) : Prop :=
  ∃ c', rtc (wpCertStep pstep pcls i) c c' ∧ promFree i c'

theorem noPromisesPromFree (i : Nat) (c : Wpcfg P D) : noPromises c → promFree i c :=
  fun hnp ag hlk => hnp i ag hlk

/-- A configuration with nothing outstanding at `i` certifies in zero steps. -/
theorem wpCertifyPromFree (i : Nat) (c : Wpcfg P D) : promFree i c → wpCertify pstep pcls i c :=
  fun hpf => ⟨c, rtc_refl c, hpf⟩

/-! ### The shape of a certification step -/

theorem certStepShape (i : Nat) (c c' : Wpcfg P D) :
    wpCertStep pstep pcls i c c' →
    ∃ ag ag', c.pcAgs[i]? = some ag ∧ c'.pcAgs = c.pcAgs.set i ag' ∧ wsLe ag.paWs ag'.paWs := by
  rintro (⟨l, hs⟩ | ⟨l, hs⟩)
  · obtain ⟨ag, st', d', f, Dl, hlk, _, hok, rfl⟩ := wpAstepInv pstep i l c c' hs
    exact ⟨ag, _, hlk, rfl, astepOkFLe _ _ _ _ _ _ _ hok _⟩
  · exact (wpPfStepShape pstep pcls i l c c' hs).2.1

theorem certStepLookup (i : Nat) (c c' : Wpcfg P D) (ag : Wpagent P) :
    wpCertStep pstep pcls i c c' → c.pcAgs[i]? = some ag →
    ∃ ag', c'.pcAgs[i]? = some ag' ∧ wsLe ag.paWs ag'.paWs := by
  intro hs hlk
  obtain ⟨ag0, ag', hlk0, heq, hle⟩ := certStepShape pstep pcls i c c' hs
  rw [hlk] at hlk0
  cases hlk0
  exact ⟨ag', by rw [heq]; exact list_lookup_insert (lookup_lt_Some hlk), hle⟩

theorem rtcCertStepIsSome (i : Nat) (c c' : Wpcfg P D) :
    rtc (wpCertStep pstep pcls i) c c' → (c.pcAgs[i]?).isSome = true →
    (c'.pcAgs[i]?).isSome = true := by
  intro hr
  induction hr with
  | refl => exact id
  | tail _ hs ih =>
    intro h
    obtain ⟨ag, hlk⟩ := Option.isSome_iff_exists.1 (ih h)
    obtain ⟨ag', hlk', _⟩ := certStepLookup pstep pcls i _ _ ag hs hlk
    rw [hlk']; rfl

/-! ### (1) `wVcap` is monotone — PARM `Certify.v:128` -/

theorem certStepVcap (i : Nat) (c c' : Wpcfg P D) (ag ag' : Wpagent P) :
    wpCertStep pstep pcls i c c' →
    c.pcAgs[i]? = some ag → c'.pcAgs[i]? = some ag' →
    ag.paWs.wVcap ≤ ag'.paWs.wVcap := by
  intro hs hlk hlk'
  obtain ⟨ag0, hlk0, hle⟩ := certStepLookup pstep pcls i c c' ag hs hlk
  rw [hlk'] at hlk0
  cases hlk0
  exact wsLeVcap _ _ hle

theorem rtcCertStepVcap (i : Nat) (c c' : Wpcfg P D) (ag ag' : Wpagent P) :
    rtc (wpCertStep pstep pcls i) c c' →
    c.pcAgs[i]? = some ag → c'.pcAgs[i]? = some ag' →
    ag.paWs.wVcap ≤ ag'.paWs.wVcap := by
  intro hr hlk
  revert ag'
  induction hr with
  | refl =>
    intro ag' hlk'
    rw [hlk] at hlk'
    cases hlk'
    exact Nat.le_refl _
  | tail hxy hs ih =>
    intro ag' hlk'
    obtain ⟨agy, hlky⟩ := Option.isSome_iff_exists.1
      (rtcCertStepIsSome pstep pcls i _ _ hxy (by rw [hlk]; rfl))
    have h1 := ih agy hlky
    have h2 := certStepVcap pstep pcls i _ _ agy ag' hs hlky hlk'
    omega

/-! ### (2) A promise at or below `wVcap` can never be fulfilled — PARM `Certify.v:144` -/

private theorem setLookupProm {l : List (Wpagent P)} {i : Nat} {ag0 ag ag' : Wpagent P} {st : P}
    {ws : Wstate} :
    l[i]? = some ag0 → l[i]? = some ag →
    (l.set i ⟨st, ws, ag0.paProm⟩)[i]? = some ag' → ag'.paProm = ag.paProm := by
  intro h0 h h'
  rw [h0] at h
  cases h
  rw [list_lookup_insert (lookup_lt_Some h0)] at h'
  cases h'
  rfl

/-- The write half deletes nothing: a `wpPfStep` leaves the promise set alone. -/
theorem wpPfStepProm (i : Nat) (l : Wlabel) (c c' : Wpcfg P D) (ag ag' : Wpagent P) :
    wpPfStep pstep pcls i l c c' →
    c.pcAgs[i]? = some ag → c'.pcAgs[i]? = some ag' →
    ag'.paProm = ag.paProm := by
  intro hs hlk hlk'
  cases hs with
  | PFSilent _ _ _ _ h0 _ => exact setLookupProm h0 hlk hlk'
  | PFLoad _ _ _ _ _ _ _ _ _ h0 _ _ => exact setLookupProm h0 hlk hlk'
  | PFStore _ _ _ _ _ _ _ _ _ _ h0 _ _ _ => exact setLookupProm h0 hlk hlk'
  | PFRmw _ _ _ _ _ _ _ _ _ _ _ _ h0 _ _ _ _ _ _ => exact setLookupProm h0 hlk hlk'
  | PFFence _ _ _ _ _ _ _ _ h0 _ => exact setLookupProm h0 hlk hlk'
  | PFDev _ _ _ _ h0 _ => exact setLookupProm h0 hlk hlk'
  | PFRegW _ _ _ _ _ _ h0 _ => exact setLookupProm h0 hlk hlk'
  | PFCtrl _ _ _ _ _ h0 _ => exact setLookupProm h0 hlk hlk'
  | PFInstr _ _ _ _ h0 _ => exact setLookupProm h0 hlk hlk'
  | PFExLoad _ _ _ _ _ _ _ _ h0 _ _ => exact setLookupProm h0 hlk hlk'
  | PFExStore _ _ _ _ _ _ _ _ _ _ _ h0 _ _ _ _ _ _ _ => exact setLookupProm h0 hlk hlk'
  | PFIFetch _ _ _ _ _ _ h0 _ _ => exact setLookupProm h0 hlk hlk'

theorem certStepVcapPromise (i : Nat) (c c' : Wpcfg P D) (ts : Nat) (ag ag' : Wpagent P) :
    wpCertStep pstep pcls i c c' →
    c.pcAgs[i]? = some ag → c'.pcAgs[i]? = some ag' →
    ts ≤ ag.paWs.wVcap → ts ∈ ag.paProm → ts ∈ ag'.paProm := by
  rintro (⟨l, hs⟩ | ⟨l, hs⟩) hlk hlk' hvcap hts
  · obtain ⟨ag0, st', d', f, Dl, hlk0, _, hok, rfl⟩ := wpAstepInv pstep i l c c' hs
    rw [hlk0] at hlk
    cases hlk
    dsimp only at hlk'
    rw [list_lookup_insert (lookup_lt_Some hlk0)] at hlk'
    cases hlk'
    cases Dl with
    | none => exact hts
    | some ts0 =>
      have hvc := astepOkDelVcap _ _ _ _ _ _ _ hok
      have hne : ts ≠ ts0 := by omega
      show ts ∈ ag.paProm \ {ts0}
      set_solver
  · rw [wpPfStepProm pstep pcls i l c c' ag ag' hs hlk hlk']
    exact hts

/-- PARM `Certify.v:166`. -/
theorem rtcCertStepVcapPromise (i : Nat) (c c' : Wpcfg P D) (ts : Nat) (ag ag' : Wpagent P) :
    rtc (wpCertStep pstep pcls i) c c' →
    c.pcAgs[i]? = some ag → c'.pcAgs[i]? = some ag' →
    ts ≤ ag.paWs.wVcap → ts ∈ ag.paProm → ts ∈ ag'.paProm := by
  intro hr hlk
  revert ag'
  induction hr with
  | refl =>
    intro ag' hlk' _ hts
    rw [hlk] at hlk'
    cases hlk'
    exact hts
  | tail hxy hs ih =>
    intro ag' hlk' hvcap hts
    obtain ⟨agy, hlky⟩ := Option.isSome_iff_exists.1
      (rtcCertStepIsSome pstep pcls i _ _ hxy (by rw [hlk]; rfl))
    have hvy := rtcCertStepVcap pstep pcls i _ _ ag agy hxy hlk hlky
    exact certStepVcapPromise pstep pcls i _ _ ts agy ag' hs hlky hlk' (by omega)
      (ih agy hlky hvcap hts)

/-- The contrapositive, in the shape the simulation's stopping case wants: if the promise is
gone at the end, `wVcap` never reached it. -/
theorem rtcCertStepPromFreeVcap (i : Nat) (c c' : Wpcfg P D) (ts : Nat) (ag : Wpagent P) :
    rtc (wpCertStep pstep pcls i) c c' → promFree i c' →
    c.pcAgs[i]? = some ag → ts ∈ ag.paProm →
    ag.paWs.wVcap < ts := by
  intro hr hpf hlk hts
  by_cases hle : ts ≤ ag.paWs.wVcap
  · exfalso
    obtain ⟨ag', hlk'⟩ := Option.isSome_iff_exists.1
      (rtcCertStepIsSome pstep pcls i c c' hr (by rw [hlk]; rfl))
    have h := rtcCertStepVcapPromise pstep pcls i c c' ts ag ag' hr hlk hlk' hle hts
    rw [hpf ag' hlk'] at h
    set_solver
  · omega

/-! ### A certifying run is a run of the full machine -/

/-- The freshness the fused store needs (`log.length + 1 ∉ paProm`) comes from `cfgWf`
alone: `promWf` bounds every outstanding timestamp by `log.length`. -/
theorem wpPfStepRtcWpstepWf (i : Nat) (l : Wlabel) (c c' : Wpcfg P D) :
    cfgWf c → wpPfStep pstep pcls i l c c' → rtc (wpstep pstep) c c' := by
  intro hwf hstep
  have hfresh : ∀ ag, c.pcAgs[i]? = some ag → c.pcLog.length + 1 ∉ ag.paProm := by
    intro ag hlk hin
    obtain ⟨_, hp⟩ := hwf i ag hlk
    obtain ⟨_, hle, _⟩ := hp _ hin
    omega
  cases hstep with
  | PFSilent cfg ag st' d' hlk hps =>
    exact rtc_once (wpstep.WPSilent c i ag st' d' hlk hps)
  | PFLoad cfg ag aq lat base tvs asrc st' d' hlk hps hr =>
    exact rtc_once (wpstep.WPLoad c i ag aq lat base tvs asrc st' d' hlk hps hr)
  | PFStore cfg ag rl base data asrc vsrc k st' d' hlk hps hnn _ =>
    exact wpstepStoreNow pstep c i ag rl base data asrc vsrc k st' d' hlk hps hnn
      (hwf i ag hlk).1 (hfresh ag hlk)
  | PFRmw cfg ag aq rl base tvs data asrc vsrc k st' d' hlk hps hnn hlen hr he _ =>
    exact wpstepRmwNow pstep c i ag aq rl base tvs data asrc vsrc k st' d' hlk hps hnn hlen
      (hwf i ag hlk).1 (hfresh ag hlk) hr he
  | PFFence cfg ag pr pw sr sw st' d' hlk hps =>
    exact rtc_once (wpstep.WPFence c i ag pr pw sr sw st' d' hlk hps)
  | PFDev cfg ag st' d' hlk hps =>
    exact rtc_once (wpstep.WPDev c i ag st' d' hlk hps)
  | PFRegW cfg ag rd srcs st' d' hlk hps =>
    exact rtc_once (wpstep.WPRegW c i ag rd srcs st' d' hlk hps)
  | PFCtrl cfg ag srcs st' d' hlk hps =>
    exact rtc_once (wpstep.WPCtrl c i ag srcs st' d' hlk hps)
  | PFInstr cfg ag st' d' hlk hps =>
    exact rtc_once (wpstep.WPInstr c i ag st' d' hlk hps)
  -- THE RMW SPLIT (S2)
  | PFExLoad cfg ag aq base tvs asrc st' d' hlk hps hr =>
    exact rtc_once (wpstep.WPExLoad c i ag aq base tvs asrc st' d' hlk hps hr)
  | PFExStore cfg ag rl base data asrc vsrc k R st' d' hlk hps hnn hres hrb hrlen he _ =>
    exact wpstepExstoreNow pstep c i ag rl base data asrc vsrc k R st' d' hlk hps hnn
      (hwf i ag hlk).1 (hfresh ag hlk) hres hrb hrlen he
  | PFIFetch cfg ag base tvs st' d' hlk hps hif =>
    exact rtc_once (wpstep.WPIFetch c i ag base tvs st' d' hlk hps hif)

theorem certStepRtcWpstep (i : Nat) (c c' : Wpcfg P D) :
    cfgWf c → wpCertStep pstep pcls i c c' → rtc (wpstep pstep) c c' := by
  rintro hwf (⟨l, hs⟩ | ⟨l, hs⟩)
  · exact rtc_once (wpAstepWpstep pstep i l c c' hs)
  · exact wpPfStepRtcWpstepWf pstep pcls i l c c' hwf hs

theorem cfgWfCertStep (i : Nat) (c c' : Wpcfg P D) :
    cfgWf c → wpCertStep pstep pcls i c c' → cfgWf c' := fun hwf hs =>
  cfgWfReach pstep c c' hwf (certStepRtcWpstep pstep pcls i c c' hwf hs)

theorem rtcCertStepRtcWpstep (i : Nat) (c c' : Wpcfg P D) :
    cfgWf c → rtc (wpCertStep pstep pcls i) c c' → rtc (wpstep pstep) c c' ∧ cfgWf c' := by
  intro hwf hr
  induction hr with
  | refl => exact ⟨rtc_refl _, hwf⟩
  | tail _ hs ih =>
    have hyz := certStepRtcWpstep pstep pcls i _ _ ih.2 hs
    exact ⟨rtc_transitive ih.1 hyz, cfgWfReach pstep _ _ ih.2 hyz⟩

end certify

end Weak
