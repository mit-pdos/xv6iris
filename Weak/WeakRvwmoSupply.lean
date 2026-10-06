/-
Weak: **B1b-1 — the supply derivation under fabric quiescence**.

Rocq: `iris/WeakRvwmoSupply.v` @ xxvzwolszwmp.

## The Rocq header, in substance

Design `claude-notes/design/weak-memory-route-b.md` §4b / §4d.4 (B1b-1 = fabric quiescence,
B1b-2 = the fabric order as bundle data).

THE GAP THIS CLOSES.  `WeakRvwmoConf.gdexecConf` says every hart's ROW is emittable, one
`admRun`-then-realizing-step block per row event, at the hart's OWN row-position-indexed fabric.
`WeakAxRealize.execProgOk'` — the hypothesis T1 consumes — wants the same blocks indexed by
GLOBAL TRACE POSITION, with ONE program state list per position and ONE global fabric.  B1b is the
interleaving that turns the former into the latter.

WHY QUIESCENCE IS A REAL MILESTONE.  MMIO accesses are not memory events: the node emits the
administrative `LDev` for any device access and `projLbl _ LDev = none`, so the fabric moves only
inside the administrative stars.  Under QUIESCENCE — no `LDev` in any emission (`emDevfree`) —
`WeakEvInst.pdevEvOk` makes every step fabric-PRESERVING and fabric-BLIND, so the global
`dv := fun _ => d0` threads through ANY interleaving.  Executions whose harts genuinely touch the
fabric are B1b-2's.

WHAT IS HERE.
(1) §2 — FABRIC BLINDNESS of a devfree emission: `admRunDevfree` / `hemitDevfreeConst` and
    `hemitDevfreeRefab` / `hemitDevfreeReindex`.  STATEMENT CORRECTION (Rocq's): the form
    `∀ dv', dv' k = dv k → hemit dv' k …` is FALSE; what holds is replay at any fabric
    assignment CONSTANT on the block's index range.
(2) §3 — `emDevfree`, the quiescent bundle `gdexecQconf` (with the BOOT TIE: the booted image and
    a hart-count bound), `gdexecQconfHull` and `gdexecQconfRen`.
(3) §4 — `hblock` / `hemitStates`: the emission's INTERMEDIATE PROGRAM STATES as an honest
    function, the witness built by the induction (no choice principle).
(4) §5 — the per-agent wstate bridge `candWsRelp`.
(5) §6 — THE INTERLEAVING THEOREM `supplyOfQconf`; §7 the compositions `hullSupply` and
    `topoSupply`.

## Deviations from Rocq

1. NAMES: the tree's camelCase (map below); `seq 0 N` ↦ `List.range' 0 N`; `l !! n` ↦ `l[n]?`;
   `.*1` ↦ `map Prod.fst`; `default [] o` ↦ `o.getD []`; `S k` ↦ `k + 1`; `filter (λ s, es_ag s
   = i)` ↦ `filter (fun s => decide (s.esAg = i))`; `Decision (RacyD …)` ↦ `Decidable (racyD …)`;
   `omap` ↦ `filterMap`.  `row_deps_aux_app` is a duplicated Rocq name: declared
   `WeakRvwmoSupply.rowDepsAuxApp`.  `gmsg` is `WeakRvwmoLin.gmsg` (the one `hullLinearizes`
   uses).  `nat_bounded_choice`'s witness type is any `A`; `filter_take_prefix` takes a Boolean
   predicate.  `dev_state` ↦ `Efab` (the event instance's fabric: the device states plus the
   residual UART/PLIC programs, `WeakEvPf` deviation 9 / owner decision Q1).
2. O2 / D1 — THE FETCH-INERTNESS OBLIGATION (`WeakRvwmoConf` deviation 3).
   `WeakRvwmoConf.hlblRealizesAx` is now `lblRealizes … ↔ hlblRealizes … ∧ lbFetchInert σ i l`:
   turning a per-hart block back into `lblRealizes` at the MACHINE state needs `lbFetchInert`
   there, which the row's representative `rowWs` cannot supply (it reads the axiomatic
   coherence/views).  So:
   - Lean-only `hblockIn es …` / `hemitStatesIn` / `hartConfStatesIn`: `hblock` whose single-step
     arm also records that the realizing item `(l, some k)` is IN the emission (Rocq's
     `hblock`/`hemitStates`/`hartConfStates` are kept, derived via `hblockInHblock`).
   - Lean-only `emFetchInert c i em` (every fetch item `(LIFetch base tvs, some n)` of `em` is
     inert at the candidate's machine state at the trace position of `i`'s `n`-th event) and
     `candFetchInert boot d0 N c` (this holds for EVERY constant-fabric emission of every row
     `trow i c.cdTr`, `i < N`).  Only the fetch arm reads it; for every other label it is `True`.
   - `supplyOfQconf` gains the FOURTH premise `candFetchInert boot d0 N c`.
   - `hullSupply` / `topoSupply`: the candidate is produced INSIDE the theorem, so the premise
     cannot be stated up front; the supply conjunct becomes CONDITIONAL —
     `candFetchInert boot d0 N c → ∃ pst, pst 0 = … ∧ execProgOk' …` (the `∃ pst` moves under
     the implication; the other conjuncts are Rocq's).  The consumer discharges it at the
     candidate it gets back.
3. PROOFS: per-constructor case analysis and `omega`; the smoke tests (Rocq `Example …
   vm_compute`) are `theorem`s closed by `decide` / the bridge; Rocq's `Print Assumptions` audit
   is not reproduced (the lint bans axioms).
4. Lean-only helpers: `filterTakeSucc` (the `take (k+1)` step of a filter), `hblockInMono`.

**Rocq → Lean name map.**  `eadm_fst` `eadmFst`, `eblock_fst` `eblockFst`, `not_elem_of_block`
`notElemOfBlock`, `nat_bounded_choice` `natBoundedChoice`, `fmap_seq_default` `fmapSeqDefault`,
`pdev_ev_false` `pdevEvFalse`, `pstep_ev_devfree` `pstepEvDevfree`, `adm_run_devfree`
`admRunDevfree`, `adm_run_refab` `admRunRefab`, `hemit_devfree_const` `hemitDevfreeConst`,
`hemit_devfree_refab` `hemitDevfreeRefab`, `hemit_devfree_reindex` `hemitDevfreeReindex`,
`em_devfree` `emDevfree`, `gdexec_qconf` `gdexecQconf`, `gdexec_qconf_img` `gdexecQconfImg`,
`gdexec_qconf_nharts` `gdexecQconfNharts`, `gdexec_qconf_rows` `gdexecQconfRows`,
`gdexec_qconf_conf` `gdexecQconfConf`, `wlbl_ren_dev` `wlblRenDev`, `em_devfree_ren`
`emDevfreeRen`, `em_devfree_prefix` `emDevfreePrefix`, `row_deps_aux_app`
`WeakRvwmoSupply.rowDepsAuxApp`, `row_deps_prefix` `rowDepsPrefix`, `gdexec_qconf_hull`
`gdexecQconfHull`, `gdexec_qconf_ren` `gdexecQconfRen`, `hblock` `hblock`, `hemit_states`
`hemitStates`, `hart_conf_states` `hartConfStates`, `trow` `trow`, `tcnt` `tcnt`,
`filter_take_prefix` `filterTakePrefix`, `trow_at` `trowAt`, `tcnt_step_eq` `tcntStepEq`,
`tcnt_step_ne` `tcntStepNe`, `mnext_ws_relp` `mnextWsRelp`, `cand_ws_relp` `candWsRelp`,
`hlbl_realizes_relp` `hlblRealizesRelp`, `hlbl_realizes_pair_relp` `hlblRealizesPairRelp`,
`supply_of_qconf` `supplyOfQconf`, `qconf_rows` `qconfRows`, `prog_row_nil` `progRowNil`,
`gxh_nharts` `gxhNharts`, `hull_supply` `hullSupply`, `topo_supply` `topoSupply`, `smoke_tr`
`smokeTr`, `smoke_c` `smokeC`, `smoke_trow0` `smokeTrow0`, `smoke_trow1` `smokeTrow1`,
`smoke_tcnt0` `smokeTcnt0`, `smoke_tcnt1` `smokeTcnt1`, `smoke_row_relp` `smokeRowRelp`,
`smoke_cand_relp` `smokeCandRelp`, `smoke_cand_relp0` `smokeCandRelp0`.

**Not ported:** nothing — every Rocq definition and lemma has a Lean twin.
-/
import Weak.WeakRvwmoConf
import Weak.WeakRvwmoHull
import Weak.WeakRvwmoTopo
import Weak.WeakRvwmoLin

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open Wlabel

/-! ## 1. List preliminaries -/

theorem eadmFst (ls : List Wlabel) : (eadm ls).map Prod.fst = ls := by
  induction ls with
  | nil => rfl
  | cons l ls ih => simp only [eadm, List.map_cons, List.map_map] at ih ⊢; exact congrArg _ ih

/-- The label sequence of ONE emission block. -/
theorem eblockFst (ls : List Wlabel) (l : Wlabel) (k : Nat) (es : List Eitem) :
    (eadm ls ++ (l, some k) :: es).map Prod.fst = ls ++ l :: es.map Prod.fst := by
  rw [List.map_append, List.map_cons, eadmFst]

theorem notElemOfBlock {A : Type _} (x : A) (ls : List A) (l : A) (es : List A) :
    x ∉ ls ++ l :: es → x ∉ ls ∧ l ≠ x ∧ x ∉ es := by
  intro h
  refine ⟨fun hin => h (List.mem_append_left _ hin), fun he => h (by simp [he]),
    fun hin => h (by simp [hin])⟩

/-- A FINITE choice principle, proved by induction (no axiom). -/
theorem natBoundedChoice {A : Type _} (a0 : A) (P : Nat → A → Prop) (N : Nat) :
    (∀ i, i < N → ∃ a, P i a) → ∃ F : Nat → A, ∀ i, i < N → P i (F i) := by
  induction N with
  | zero => intro _; exact ⟨fun _ => a0, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
  | succ N ih =>
    intro H
    obtain ⟨F, hF⟩ := ih (fun i hi => H i (by omega))
    obtain ⟨a, ha⟩ := H N (by omega)
    refine ⟨fun i => if i = N then a else F i, ?_⟩
    intro i hi
    by_cases hc : i = N
    · subst hc; simpa using ha
    · simp only [hc, if_false]; exact hF i (by omega)

/-- The pointwise-lookup rebuild of a list. -/
theorem fmapSeqDefault {A : Type _} (x : A) (l : List A) :
    (List.range' 0 l.length).map (fun i => (l[i]?).getD x) = l := by
  apply List.ext_getElem?
  intro j
  rw [List.getElem?_map]
  by_cases hj : j < l.length
  · rw [lookup_seq_lt hj]
    simp [List.getElem?_eq_getElem hj]
  · rw [lookup_seq_ge (by omega), List.getElem?_eq_none (by omega)]
    rfl

/-! ## 2. Fabric blindness of an `LDev`-free emission -/

theorem pdevEvFalse (p : Pexv6) (l : Wlabel) (p' : Pexv6) : l ≠ LDev → pdevEv p l p' = false := by
  intro h
  cases l <;> first | rfl | exact absurd rfl h

theorem pstepEvDevfree (p : Pexv6) (d : Efab) (l : Wlabel) (p' : Pexv6) (d' : Efab) :
    pstepEv p d l p' d' → l ≠ LDev → d' = d ∧ ∀ d0, pstepEv p d0 l p' d0 :=
  fun hs hne => pdevEvOk p d l p' d' hs (pdevEvFalse p l p' hne)

/-! ### 2.1 The administrative run -/

theorem admRunDevfree (instr : Bool) (p : Pexv6) (d : Efab) (ls : List Wlabel) (p' : Pexv6)
    (d' : Efab) : admRun instr p d ls p' d' → LDev ∉ ls → d' = d := by
  intro h
  induction h with
  | ARnil => intro _; rfl
  | ARcons p d l p1 d1 ls p' d' _ hs _ ih =>
    intro hnd
    have hne : l ≠ LDev := fun he => hnd (by simp [he])
    obtain ⟨hd, _⟩ := pstepEvDevfree _ _ _ _ _ hs hne
    rw [ih (fun hin => hnd (List.mem_cons_of_mem _ hin)), hd]

theorem admRunRefab (instr : Bool) (p : Pexv6) (d : Efab) (ls : List Wlabel) (p' : Pexv6)
    (d' : Efab) : admRun instr p d ls p' d' → LDev ∉ ls →
    ∀ d0, admRun instr p d0 ls p' d0 := by
  intro h
  induction h with
  | ARnil p d => intro _ d0; exact .ARnil p d0
  | ARcons p d l p1 d1 ls p' d' ha hs _ ih =>
    intro hnd d0
    have hne : l ≠ LDev := fun he => hnd (by simp [he])
    have hrest : LDev ∉ ls := fun hin => hnd (List.mem_cons_of_mem _ hin)
    obtain ⟨_, hall⟩ := pstepEvDevfree _ _ _ _ _ hs hne
    exact .ARcons p d0 l p1 d0 ls p' d0 ha (hall d0) (ih hrest d0)

/-! ### 2.2 The emission -/

theorem hemitDevfreeConst (dv : Nat → Efab) (k : Nat) (ws : Wstate) (row : List Lbl)
    (p : Pexv6) (es : List Eitem) (pfin : Pexv6) :
    hemit dv k ws row p es pfin → LDev ∉ es.map Prod.fst →
    ∀ j, k ≤ j → j ≤ k + row.length → dv j = dv k := by
  intro h
  induction h with
  | HEnil k ws p =>
    intro _ j hlo hhi
    simp only [List.length_nil, Nat.add_zero] at hhi
    have : j = k := by omega
    subst this; rfl
  | HEone k ws lb row p ls pa da l p' es pfin har _ hst _ ih =>
    intro hnd j hlo hhi
    rw [eblockFst] at hnd
    obtain ⟨hne1, hnel, hrest⟩ := notElemOfBlock _ _ _ _ hnd
    have hda : da = dv k := admRunDevfree _ _ _ _ _ _ har hne1
    obtain ⟨hd, _⟩ := pstepEvDevfree _ _ _ _ _ hst hnel
    have hsk : dv (k + 1) = dv k := by rw [hd, hda]
    by_cases hjk : j = k
    · subst hjk; rfl
    · simp only [List.length_cons] at hhi
      rw [ih hrest j (by omega) (by omega), hsk]
  | HEpair k ws lb row p ls1 pa da l1 pm dm ls2 pm2 dm2 l2 p' es pfin har1 _ hst1 har2 hst2 _ ih =>
    intro hnd j hlo hhi
    rw [eblockFst, eblockFst] at hnd
    obtain ⟨hne1, hnel1, hnd2⟩ := notElemOfBlock _ _ _ _ hnd
    obtain ⟨hne2, hnel2, hrest⟩ := notElemOfBlock _ _ _ _ hnd2
    have hda : da = dv k := admRunDevfree _ _ _ _ _ _ har1 hne1
    obtain ⟨hd1, _⟩ := pstepEvDevfree _ _ _ _ _ hst1 hnel1
    have hdm2 : dm2 = dm := admRunDevfree _ _ _ _ _ _ har2 hne2
    obtain ⟨hd2, _⟩ := pstepEvDevfree _ _ _ _ _ hst2 hnel2
    have hsk : dv (k + 1) = dv k := by rw [hd2, hdm2, hd1, hda]
    by_cases hjk : j = k
    · subst hjk; rfl
    · simp only [List.length_cons] at hhi
      rw [ih hrest j (by omega) (by omega), hsk]

/-- THE REFABRICATION (Rocq's recorded STATEMENT CORRECTION: the emission replays at any fabric
assignment CONSTANT on the block's index range, with no relation to `dv` at all). -/
theorem hemitDevfreeRefab (dv : Nat → Efab) (k : Nat) (ws : Wstate) (row : List Lbl)
    (p : Pexv6) (es : List Eitem) (pfin : Pexv6) :
    hemit dv k ws row p es pfin → LDev ∉ es.map Prod.fst →
    ∀ (dv' : Nat → Efab) (d0 : Efab),
      (∀ j, k ≤ j → j ≤ k + row.length → dv' j = d0) →
      hemit dv' k ws row p es pfin := by
  intro h
  induction h with
  | HEnil k ws p => intro _ dv' d0 _; exact .HEnil k ws p
  | HEone k ws lb row p ls pa da l p' es pfin har hre hst _ ih =>
    intro hnd dv' d0 hc
    rw [eblockFst] at hnd
    obtain ⟨hne1, hnel, hrest⟩ := notElemOfBlock _ _ _ _ hnd
    obtain ⟨_, hall⟩ := pstepEvDevfree _ _ _ _ _ hst hnel
    refine .HEone k ws lb row p ls pa d0 l p' es pfin ?_ hre ?_ ?_
    · rw [hc k (Nat.le_refl _) (by simp)]
      exact admRunRefab _ _ _ _ _ _ har hne1 d0
    · rw [hc (k + 1) (by omega) (by simp only [List.length_cons]; omega)]
      exact hall d0
    · exact ih hrest dv' d0 (fun j hlo hhi => hc j (by omega) (by simp only [List.length_cons]; omega))
  | HEpair k ws lb row p ls1 pa da l1 pm dm ls2 pm2 dm2 l2 p' es pfin har1 hre hst1 har2 hst2 _ ih =>
    intro hnd dv' d0 hc
    rw [eblockFst, eblockFst] at hnd
    obtain ⟨hne1, hnel1, hnd2⟩ := notElemOfBlock _ _ _ _ hnd
    obtain ⟨hne2, hnel2, hrest⟩ := notElemOfBlock _ _ _ _ hnd2
    obtain ⟨_, hall1⟩ := pstepEvDevfree _ _ _ _ _ hst1 hnel1
    obtain ⟨_, hall2⟩ := pstepEvDevfree _ _ _ _ _ hst2 hnel2
    refine .HEpair k ws lb row p ls1 pa d0 l1 pm d0 ls2 pm2 d0 l2 p' es pfin ?_ hre (hall1 d0)
      (admRunRefab _ _ _ _ _ _ har2 hne2 d0) ?_ ?_
    · rw [hc k (Nat.le_refl _) (by simp)]
      exact admRunRefab _ _ _ _ _ _ har1 hne1 d0
    · rw [hc (k + 1) (by omega) (by simp only [List.length_cons]; omega)]
      exact hall2 d0
    · exact ih hrest dv' d0 (fun j hlo hhi => hc j (by omega) (by simp only [List.length_cons]; omega))

theorem hemitDevfreeReindex (dv : Nat → Efab) (k : Nat) (ws : Wstate) (row : List Lbl)
    (p : Pexv6) (es : List Eitem) (pfin : Pexv6) :
    hemit dv k ws row p es pfin → LDev ∉ es.map Prod.fst →
    ∀ d0 : Efab, hemit (fun _ => d0) k ws row p es pfin :=
  fun hem hnd d0 => hemitDevfreeRefab dv k ws row p es pfin hem hnd _ d0 (fun _ _ _ => rfl)

/-! ## 3. The quiescent conformance bundle -/

def emDevfree (em : Hemission) : Prop := LDev ∉ emLabels em

/-- THE QUIESCENT BUNDLE, with the BOOT TIE (`im` the booted image, `nh` the booted hart count). -/
def gdexecQconf (boot : Nat → Pexv6) (d0 : Efab) (im : Image) (nh : Nat) (GD : Gdexec) :
    Prop :=
  GD.gdG.gxImg = im ∧
  GD.gdG.gxProg.length ≤ nh ∧
  (∀ i row, GD.gdG.gxProg[i]? = some row →
    ∃ em, hartConf i row (boot i) (fun _ => d0) em ∧
          emDevfree em ∧
          (∀ jk, jk ∈ rowDeps em.emItems → ((i, jk.1), (i, jk.2)) ∈ GD.gdDeps))

theorem gdexecQconfImg (boot : Nat → Pexv6) (d0 : Efab) (im : Image) (nh : Nat)
    (GD : Gdexec) : gdexecQconf boot d0 im nh GD → GD.gdG.gxImg = im :=
  fun h => h.1

theorem gdexecQconfNharts (boot : Nat → Pexv6) (d0 : Efab) (im : Image) (nh : Nat)
    (GD : Gdexec) : gdexecQconf boot d0 im nh GD → GD.gdG.gxProg.length ≤ nh :=
  fun h => h.2.1

theorem gdexecQconfRows (boot : Nat → Pexv6) (d0 : Efab) (im : Image) (nh : Nat)
    (GD : Gdexec) : gdexecQconf boot d0 im nh GD →
    ∀ i row, GD.gdG.gxProg[i]? = some row →
      ∃ em, hartConf i row (boot i) (fun _ => d0) em ∧
            emDevfree em ∧
            (∀ jk, jk ∈ rowDeps em.emItems → ((i, jk.1), (i, jk.2)) ∈ GD.gdDeps) :=
  fun h => h.2.2

/-- The bundle IS a `gdexecConf` bundle. -/
theorem gdexecQconfConf (boot : Nat → Pexv6) (d0 : Efab) (im : Image) (nh : Nat)
    (GD : Gdexec) : gdexecQconf boot d0 im nh GD → gdexecConf boot (fun _ _ => d0) GD := by
  rintro ⟨_, _, h⟩ i row hrow
  obtain ⟨em, hem, _, hdep⟩ := h i row hrow
  exact ⟨em, hem, hdep⟩

/-! ### 3.1 `emDevfree` is stable under the two emission operations -/

theorem wlblRenDev (π : Nat → Nat) (l : Wlabel) : wlblRen π l = LDev → l = LDev := by
  cases l <;> simp [wlblRen]

theorem emDevfreeRen (π : Nat → Nat) (em : Hemission) : emDevfree em → emDevfree (emRen π em) := by
  unfold emDevfree
  rw [emLabelsRen]
  intro h hin
  obtain ⟨l, hl, heq⟩ := List.mem_map.1 hin
  rw [wlblRenDev π l heq] at hl
  exact h hl

theorem emDevfreePrefix (em em' : Hemission) :
    em'.emItems <+: em.emItems → emDevfree em → emDevfree em' := by
  rintro ⟨t, ht⟩ h hin
  apply h
  unfold emLabels at hin ⊢
  rw [← ht, List.map_append]
  exact List.mem_append_left _ hin

/-! ### 3.2 `rowDeps` of a prefix of the ITEM list -/

theorem WeakRvwmoSupply.rowDepsAuxApp (s : WeakRvwmoConf.Dstate) (es1 es2 : List Eitem) (jk : Nat × Nat) :
    jk ∈ rowDepsAux s es1 → jk ∈ rowDepsAux s (es1 ++ es2) := by
  induction es1 generalizing s with
  | nil => intro h; simp [rowDepsAux] at h
  | cons it es1 ih =>
    intro h
    simp only [rowDepsAux, List.cons_append, List.mem_append] at h ⊢
    rcases h with h | h
    · exact Or.inl h
    · exact Or.inr (ih _ h)

theorem rowDepsPrefix (es1 es2 : List Eitem) (jk : Nat × Nat) :
    es1 <+: es2 → jk ∈ rowDeps es1 → jk ∈ rowDeps es2 := by
  rintro ⟨t, rfl⟩ h
  exact WeakRvwmoSupply.rowDepsAuxApp _ _ _ _ h

/-! ### 3.3 The hull transport -/

theorem gdexecQconfHull (boot : Nat → Pexv6) (d0 : Efab) (im : Image) (nh : Nat)
    (GD : Gdexec) (cs : List Nat) :
    gdexecQconf boot d0 im nh GD → gdexecQconf boot d0 im nh (gdHull GD cs) := by
  rintro ⟨himg, hnh, hq⟩
  refine ⟨himg, ?_, ?_⟩
  · show (gxHull GD.gdG cs).gxProg.length ≤ nh
    simp only [gxHull, List.length_map, List.length_zipWith]
    omega
  · intro i row' hrow'
    change (gxHull GD.gdG cs).gxProg[i]? = some row' at hrow'
    rw [gxhProgLookup] at hrow'
    cases hc : cs[i]? with
    | none => rw [hc] at hrow'; simp at hrow'
    | some c =>
      rw [hc] at hrow'
      cases hp : GD.gdG.gxProg[i]? with
      | none => rw [hp] at hrow'; simp at hrow'
      | some p =>
        rw [hp] at hrow'
        simp only [Option.bind_some, Option.some.injEq] at hrow'
        subst hrow'
        obtain ⟨em, hem, hdf, hdep⟩ := hq i p hp
        obtain ⟨em', hem', hpre⟩ := hartConfPrefix i p (boot i) (fun _ => d0) em c hem
        refine ⟨emRen (hren GD.gdG cs) em', hartConfRen _ _ _ _ _ _ hem',
          emDevfreeRen _ _ (emDevfreePrefix em em' hpre hdf), ?_⟩
        intro jk hjk
        simp only [emRen] at hjk
        rw [rowDepsRen] at hjk
        obtain ⟨_, ⟨lb1, hl1, _⟩, ⟨lb2, hl2, _⟩⟩ :=
          hartConfRowDepsWf i (p.take c) (boot i) (fun _ => d0) em' jk hem' hjk
        have hlt1 : jk.1 < c := by
          have := lookup_lt_Some hl1
          rw [List.length_take] at this
          omega
        have hlt2 : jk.2 < c := by
          have := lookup_lt_Some hl2
          rw [List.length_take] at this
          omega
        exact (gdHullDeps GD cs _).2 ⟨hdep jk (rowDepsPrefix _ _ _ hpre hjk),
          gcutIntro cs _ c hc hlt1, gcutIntro cs _ c hc hlt2⟩

/-! ### 3.4 The orbit transport -/

theorem gdexecQconfRen (π : Nat → Nat) (boot : Nat → Pexv6) (d0 : Efab) (im : Image)
    (nh : Nat) (GD GD' : Gdexec) :
    rowsRel π GD.gdG GD'.gdG →
    GD'.gdDeps = GD.gdDeps →
    gdexecQconf boot d0 im nh GD → gdexecQconf boot d0 im nh GD' := by
  intro hrr hdeps hq0
  obtain ⟨himg, hnh, hq⟩ := hq0
  refine ⟨by rw [rowsRelImg π _ _ hrr]; exact himg,
    by rw [rowsRelNharts π _ _ hrr]; exact hnh, ?_⟩
  intro i row' hrow'
  obtain ⟨_, hprog, _⟩ := hrr
  rw [hprog, List.getElem?_map] at hrow'
  cases hrow0 : GD.gdG.gxProg[i]? with
  | none => rw [hrow0] at hrow'; simp at hrow'
  | some row =>
    rw [hrow0] at hrow'
    simp only [Option.map_some, Option.some.injEq] at hrow'
    subst hrow'
    obtain ⟨em, hem, hdf, hdep⟩ := hq i row hrow0
    refine ⟨emRen π em, hartConfRen π i row (boot i) _ em hem, emDevfreeRen π em hdf, ?_⟩
    intro jk hjk
    rw [hdeps]
    apply hdep
    simp only [emRen] at hjk
    rw [rowDepsRen] at hjk
    exact hjk

/-! ## 4. The emission's intermediate program states -/

def hblock (dv : Nat → Efab) (k : Nat) (ws : Wstate) (lb : Lbl) (p p' : Pexv6) : Prop :=
  ∃ (pa : Pexv6) (da : Efab),
    admStar pstepEv true p (dv k) pa da ∧
    ((∃ l, hlblRealizes pa ws lb l ∧ pstepEv pa da l p' (dv (k + 1)))
     ∨ (∃ (pm : Pexv6) (dm : Efab) (pm2 : Pexv6) (dm2 : Efab) (l1 l2 : Wlabel),
          hlblRealizesPair pa pm2 ws lb l1 l2 ∧
          pstepEv pa da l1 pm dm ∧
          admStar pstepEv false pm dm pm2 dm2 ∧
          pstepEv pm2 dm2 l2 p' (dv (k + 1))))

/-- (Lean-only, deviation 2) `hblock` whose single-step arm records its item in `es`. -/
def hblockIn (es : List Eitem) (dv : Nat → Efab) (k : Nat) (ws : Wstate) (lb : Lbl)
    (p p' : Pexv6) : Prop :=
  ∃ (pa : Pexv6) (da : Efab),
    admStar pstepEv true p (dv k) pa da ∧
    ((∃ l, (l, some k) ∈ es ∧ hlblRealizes pa ws lb l ∧ pstepEv pa da l p' (dv (k + 1)))
     ∨ (∃ (pm : Pexv6) (dm : Efab) (pm2 : Pexv6) (dm2 : Efab) (l1 l2 : Wlabel),
          hlblRealizesPair pa pm2 ws lb l1 l2 ∧
          pstepEv pa da l1 pm dm ∧
          admStar pstepEv false pm dm pm2 dm2 ∧
          pstepEv pm2 dm2 l2 p' (dv (k + 1))))

theorem hblockInHblock (es : List Eitem) (dv : Nat → Efab) (k : Nat) (ws : Wstate)
    (lb : Lbl) (p p' : Pexv6) : hblockIn es dv k ws lb p p' → hblock dv k ws lb p p' := by
  rintro ⟨pa, da, hs, ⟨l, _, h1, h2⟩ | h⟩
  · exact ⟨pa, da, hs, .inl ⟨l, h1, h2⟩⟩
  · exact ⟨pa, da, hs, .inr h⟩

theorem hblockInMono (es es' : List Eitem) (dv : Nat → Efab) (k : Nat) (ws : Wstate)
    (lb : Lbl) (p p' : Pexv6) :
    hblockIn es dv k ws lb p p' → (∀ x, x ∈ es → x ∈ es') → hblockIn es' dv k ws lb p p' := by
  rintro ⟨pa, da, hs, ⟨l, hm, h1, h2⟩ | h⟩ hsub
  · exact ⟨pa, da, hs, .inl ⟨l, hsub _ hm, h1, h2⟩⟩
  · exact ⟨pa, da, hs, .inr h⟩

/-- (Lean-only) `hemitStates`, with the realizing items located in the emission. -/
theorem hemitStatesIn (dv : Nat → Efab) (k : Nat) (ws : Wstate) (row : List Lbl)
    (p : Pexv6) (es : List Eitem) (pfin : Pexv6) :
    hemit dv k ws row p es pfin →
    ∃ f : Nat → Pexv6, f 0 = p ∧
      ∀ n lb, row[n]? = some lb →
        hblockIn es dv (n + k) (rowWsAux k ws (row.take n)) lb (f n) (f (n + 1)) := by
  intro h
  induction h with
  | HEnil k ws p => exact ⟨fun _ => p, rfl, fun n lb hn => by simp at hn⟩
  | HEone k ws lb row p ls pa da l p' es pfin har hre hst _ ih =>
    obtain ⟨f', hf0, hf⟩ := ih
    refine ⟨fun n => match n with | 0 => p | n' + 1 => f' n', rfl, ?_⟩
    intro n lb0 hn
    cases n with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hn
      subst hn
      rw [Nat.zero_add]
      refine ⟨pa, da, admRunStar _ _ _ _ _ _ har, .inl ⟨l, by simp, hre, ?_⟩⟩
      show pstepEv pa da l (f' 0) (dv (k + 1))
      rw [hf0]; exact hst
    | succ n =>
      simp only [List.getElem?_cons_succ] at hn
      have e : n + 1 + k = n + (k + 1) := by omega
      rw [e]
      exact hblockInMono _ _ _ _ _ _ _ _ (hf n lb0 hn) (fun x hx => by simp [hx])
  | HEpair k ws lb row p ls1 pa da l1 pm dm ls2 pm2 dm2 l2 p' es pfin har1 hre hst1 har2 hst2 _ ih =>
    obtain ⟨f', hf0, hf⟩ := ih
    refine ⟨fun n => match n with | 0 => p | n' + 1 => f' n', rfl, ?_⟩
    intro n lb0 hn
    cases n with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hn
      subst hn
      rw [Nat.zero_add]
      refine ⟨pa, da, admRunStar _ _ _ _ _ _ har1,
        .inr ⟨pm, dm, pm2, dm2, l1, l2, hre, hst1, admRunStar _ _ _ _ _ _ har2, ?_⟩⟩
      show pstepEv pm2 dm2 l2 (f' 0) (dv (k + 1))
      rw [hf0]; exact hst2
    | succ n =>
      simp only [List.getElem?_cons_succ] at hn
      have e : n + 1 + k = n + (k + 1) := by omega
      rw [e]
      exact hblockInMono _ _ _ _ _ _ _ _ (hf n lb0 hn) (fun x hx => by simp [hx])

theorem hemitStates (dv : Nat → Efab) (k : Nat) (ws : Wstate) (row : List Lbl)
    (p : Pexv6) (es : List Eitem) (pfin : Pexv6) :
    hemit dv k ws row p es pfin →
    ∃ f : Nat → Pexv6, f 0 = p ∧
      ∀ n lb, row[n]? = some lb →
        hblock dv (n + k) (rowWsAux k ws (row.take n)) lb (f n) (f (n + 1)) := by
  intro hem
  obtain ⟨f, hf0, hf⟩ := hemitStatesIn dv k ws row p es pfin hem
  exact ⟨f, hf0, fun n lb hn => hblockInHblock _ _ _ _ _ _ _ (hf n lb hn)⟩

/-- (Lean-only) `hartConfStates`, with the realizing items located in the emission. -/
theorem hartConfStatesIn (i : Nat) (row : List Lbl) (p0 : Pexv6) (dv : Nat → Efab)
    (em : Hemission) :
    hartConf i row p0 dv em →
    ∃ f : Nat → Pexv6, f 0 = p0 ∧
      ∀ n lb, row[n]? = some lb → hblockIn em.emItems dv n (rowWs row n) lb (f n) (f (n + 1)) := by
  intro hem
  obtain ⟨f, hf0, hf⟩ := hemitStatesIn _ _ _ _ _ _ _ hem
  refine ⟨f, hf0, fun n lb hn => ?_⟩
  have h := hf n lb hn
  rw [Nat.add_zero] at h
  exact h

theorem hartConfStates (i : Nat) (row : List Lbl) (p0 : Pexv6) (dv : Nat → Efab)
    (em : Hemission) :
    hartConf i row p0 dv em →
    ∃ f : Nat → Pexv6, f 0 = p0 ∧
      ∀ n lb, row[n]? = some lb → hblock dv n (rowWs row n) lb (f n) (f (n + 1)) := by
  intro hem
  obtain ⟨f, hf0, hf⟩ := hartConfStatesIn i row p0 dv em hem
  exact ⟨f, hf0, fun n lb hn => hblockInHblock _ _ _ _ _ _ _ (hf n lb hn)⟩

/-! ## 5. The per-agent wstate, at a global trace position -/

def trow (i : Nat) (tr : List Estep) : List Lbl :=
  (tr.filter (fun s => decide (s.esAg = i))).map (fun s => s.esLb)

def tcnt (i : Nat) (tr : List Estep) : Nat :=
  (tr.filter (fun s => decide (s.esAg = i))).length

theorem filterTakePrefix (P : Estep → Bool) (tr : List Estep) (n : Nat) :
    (tr.take n).filter P <+: tr.filter P :=
  ⟨(tr.drop n).filter P, by rw [← List.filter_append, List.take_append_drop]⟩

/-- (Lean-only) The `take (k+1)` step of a filter. -/
theorem filterTakeSucc (P : Estep → Bool) (tr : List Estep) (k : Nat) (s : Estep) :
    tr[k]? = some s →
    (tr.take (k + 1)).filter P = (tr.take k).filter P ++ [s].filter P := by
  intro hk
  rw [List.take_add_one, hk, Option.toList_some, List.filter_append]

/-- The `k`-th trace step of agent `i` is the `tcnt`-th element of `i`'s row. -/
theorem trowAt (i : Nat) (tr : List Estep) (k : Nat) (s : Estep) :
    tr[k]? = some s → s.esAg = i →
    (trow i tr)[tcnt i (tr.take k)]? = some s.esLb := by
  intro hk hag
  have h1 : tr.filter (fun s => decide (s.esAg = i)) =
      (tr.take k).filter (fun s => decide (s.esAg = i)) ++
        s :: (tr.drop (k + 1)).filter (fun s => decide (s.esAg = i)) := by
    conv => lhs; rw [← List.take_append_drop (k + 1) tr]
    rw [List.filter_append, filterTakeSucc _ _ k s hk]
    simp [hag]
  simp only [trow, tcnt]
  rw [List.getElem?_map, h1, List.getElem?_append_right (Nat.le_refl _)]
  simp

theorem tcntStepEq (i : Nat) (tr : List Estep) (k : Nat) (s : Estep) :
    tr[k]? = some s → s.esAg = i → tcnt i (tr.take (k + 1)) = tcnt i (tr.take k) + 1 := by
  intro hk hag
  simp only [tcnt]
  rw [filterTakeSucc _ _ k s hk]
  simp [hag]

theorem tcntStepNe (i : Nat) (tr : List Estep) (k : Nat) (s : Estep) :
    tr[k]? = some s → s.esAg ≠ i → tcnt i (tr.take (k + 1)) = tcnt i (tr.take k) := by
  intro hk hag
  simp only [tcnt]
  rw [filterTakeSucc _ _ k s hk]
  simp [hag]

/-- The machine's per-agent post-state, at `wRelp`. -/
theorem mnextWsRelp (σ : Mstate) (i : Nat) (l : Lbl) :
    ((mnext σ i l).msWs i).wRelp = lpostRelp (σ.msWs i).wRelp l := by
  cases l with
  | LLoad aq base ts vs =>
    simp only [mnext, updWsEq]
    exact WeakRvwmoConf.loadPostRunRelp _ _ _ _
  | LStore rl base vs k =>
    simp only [mnext, updWsEq, lpostRelp]
    rw [storePostRunRelp]
    cases vs <;> rfl
  | LFence pr pw sr sw =>
    simp only [mnext, updWsEq]
    rfl
  | LRmw aq rl base ts rvs wvs k =>
    simp only [mnext, updWsEq, lpostRelp]
    rw [storePostRunRelp]
    cases wvs <;> simp only [List.length_nil, List.length_cons, WeakRvwmoConf.loadPostRunRelp]

/-- THE BRIDGE. -/
theorem candWsRelp (c : Cand) (i k : Nat) :
    k ≤ c.cdTr.length →
    ((stt (candExec c) k).msWs i).wRelp =
      (rowWs (trow i c.cdTr) (tcnt i (c.cdTr.take k))).wRelp := by
  induction k with
  | zero =>
    intro _
    rw [sttLookup _ _ _ (replay0 (candInit c) c.cdTr)]
    rfl
  | succ k ih =>
    intro hk
    obtain ⟨s, hs⟩ : ∃ s, c.cdTr[k]? = some s := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    rw [candNext c k s hs]
    by_cases hag : s.esAg = i
    · subst hag
      rw [mnextWsRelp, tcntStepEq _ _ k s hs rfl,
        rowWsStep _ _ _ (trowAt _ _ k s hs rfl), lblPostRelp, ih (by omega)]
    · rw [mnextWsNe _ _ _ _ (fun h => hag h.symm), tcntStepNe _ _ k s hs hag]
      exact ih (by omega)

/-! ## 6. The interleaving theorem -/

/-- The projection equation reads the wstate ONLY through `wRelp`. -/
theorem hlblRealizesRelp (p : Pexv6) (ws ws' : Wstate) (lb : Lbl) (l : Wlabel) :
    ws'.wRelp = ws.wRelp → hlblRealizes p ws lb l → hlblRealizes p ws' lb l := by
  rintro hr ⟨h1, h2, h3, h4⟩
  refine ⟨h1, h2, h3, ?_⟩
  rw [WeakRvwmoConf.pclsEvRelp p l ws' ws hr]
  exact h4

theorem hlblRealizesPairRelp (p pm : Pexv6) (ws ws' : Wstate) (lb : Lbl) (l1 l2 : Wlabel) :
    ws'.wRelp = ws.wRelp →
    hlblRealizesPair p pm ws lb l1 l2 → hlblRealizesPair p pm ws' lb l1 l2 := by
  rintro hr ⟨aq, rl, base, tvs, data, a1, a2, v2, rfl, rfl, hne, hlen, rfl⟩
  refine ⟨aq, rl, base, tvs, data, a1, a2, v2, rfl, rfl, hne, hlen, ?_⟩
  rw [WeakRvwmoConf.pclsEvRelp pm _ (loadPostRun ws' aq base (tvs.map Prod.fst))
    (loadPostRun ws aq base (tvs.map Prod.fst))
    (by rw [WeakRvwmoConf.loadPostRunRelp, WeakRvwmoConf.loadPostRunRelp, hr])]

/-- (Lean-only, deviation 2) Every fetch item of `em` is inert at the candidate's machine state,
at the trace position of agent `i`'s matching row event. -/
def emFetchInert (c : Cand) (i : Nat) (em : Hemission) : Prop :=
  ∀ (base : Int) (tvs : List (Nat × BitVec 8)) (n k : Nat) (s : Estep),
    (LIFetch base tvs, some n) ∈ em.emItems → c.cdTr[k]? = some s → s.esAg = i →
    tcnt i (c.cdTr.take k) = n → lbFetchInert (stt (candExec c) k) i (LIFetch base tvs)

/-- (Lean-only, deviation 2) The candidate-level fetch obligation: every constant-fabric emission
of every row of the trace (agents below `N`) is fetch-inert at `c`. -/
def candFetchInert (boot : Nat → Pexv6) (d0 : Efab) (N : Nat) (c : Cand) : Prop :=
  ∀ i em, i < N → hartConf i (trow i c.cdTr) (boot i) (fun _ => d0) em → emFetchInert c i em

theorem supplyOfQconf (c : Cand) (boot : Nat → Pexv6) (d0 : Efab)
    (rows : Nat → List Lbl) (N : Nat) :
    -- the trace is an interleaving of the rows ...
    (∀ i, (c.cdTr.filter (fun s => decide (s.esAg = i))).map (fun s => s.esLb) = rows i) →
    -- ... over the agents below `N` ...
    (∀ i, N ≤ i → rows i = []) →
    -- ... every such agent's row is emittable at the CONSTANT fabric ...
    (∀ i, i < N → ∃ em, hartConf i (rows i) (boot i) (fun _ => d0) em) →
    -- ... (Lean-only, deviation 2) and the emissions' fetches are inert at `c`
    candFetchInert boot d0 N c →
    ∃ pst : Nat → List Pexv6,
      pst 0 = (List.range' 0 N).map boot ∧
      execProgOk' pstepEv pclsEv pst (fun _ => d0) (candExec c) := by
  intro hrows hbnd hconf hfi
  have hch : ∀ i, i < N → ∃ fe : Hemission × (Nat → Pexv6),
      fe.2 0 = boot i ∧ emFetchInert c i fe.1 ∧
      ∀ n lb, (rows i)[n]? = some lb →
        hblockIn fe.1.emItems (fun _ => d0) n (rowWs (rows i) n) lb (fe.2 n) (fe.2 (n + 1)) := by
    intro i hi
    obtain ⟨em, hem⟩ := hconf i hi
    obtain ⟨f, hf0, hf⟩ := hartConfStatesIn i _ _ _ em hem
    refine ⟨(em, f), hf0, hfi i em hi ?_, hf⟩
    unfold trow
    rw [hrows i]
    exact hem
  obtain ⟨F, hF⟩ := natBoundedChoice (⟨[], .PDisk none⟩, fun _ => .PDisk none) _ N hch
  refine ⟨fun k => (List.range' 0 N).map (fun i => (F i).2 (tcnt i (c.cdTr.take k))), ?_, ?_⟩
  · apply List.ext_getElem?
    intro j
    simp only [List.getElem?_map]
    by_cases hj : j < N
    · rw [lookup_seq_lt hj]
      simp only [Option.map_some, Nat.zero_add]
      exact congrArg some (hF j hj).1
    · rw [lookup_seq_ge (by omega)]
      rfl
  · intro k s hs
    change c.cdTr[k]? = some s at hs
    have hklen : k ≤ c.cdTr.length := by have := lookup_lt_Some hs; omega
    have hrow : (rows s.esAg)[tcnt s.esAg (c.cdTr.take k)]? = some s.esLb := by
      rw [← hrows]; exact trowAt _ _ k s hs rfl
    have hiN : s.esAg < N := by
      by_cases hge : s.esAg < N
      · exact hge
      · rw [hbnd _ (by omega)] at hrow; simp at hrow
    obtain ⟨_, hfe, hfb⟩ := hF _ hiN
    obtain ⟨pa, da, hstar, hdisj⟩ := hfb _ _ hrow
    have hrelp : ((stt (candExec c) k).msWs s.esAg).wRelp =
        (rowWs (rows s.esAg) (tcnt s.esAg (c.cdTr.take k))).wRelp := by
      rw [candWsRelp c _ k hklen]
      unfold trow
      rw [hrows]
    refine ⟨(F s.esAg).2 (tcnt s.esAg (c.cdTr.take k)), pa, da,
      (F s.esAg).2 (tcnt s.esAg (c.cdTr.take k) + 1), ?_, ?_, hstar, ?_⟩
    · simp only [List.getElem?_map]
      rw [lookup_seq_lt hiN]
      simp
    · apply List.ext_getElem?
      intro j
      by_cases hj : j = s.esAg
      · rw [hj, List.getElem?_set_self (by simp only [List.length_map, List.length_range']; omega),
          List.getElem?_map, lookup_seq_lt hiN]
        simp only [Option.map_some, Nat.zero_add, tcntStepEq _ _ k s hs rfl]
      · rw [List.getElem?_set_ne (fun h => hj h.symm)]
        simp only [List.getElem?_map]
        by_cases hjN : j < N
        · rw [lookup_seq_lt hjN]
          simp only [Option.map_some, Nat.zero_add, tcntStepNe j _ k s hs (fun h => hj h.symm)]
        · rw [lookup_seq_ge (by omega)]
          rfl
    · rcases hdisj with ⟨l, hmem, hre, hst⟩ | ⟨pm, dm, pm2, dm2, l1, l2, hre, hs1, hs2, hs3⟩
      · left
        refine ⟨l, (hlblRealizesAx _ _ _ _ _).2 ⟨hlblRealizesRelp _ _ _ _ _ hrelp hre, ?_⟩, hst⟩
        cases l with
        | LIFetch base tvs => exact hfe base tvs _ k s hmem hs rfl rfl
        | _ => trivial
      · right
        exact ⟨pm, dm, pm2, dm2, l1, l2,
          (hlblRealizesPairAx _ _ _ _ _ _ _).1 (hlblRealizesPairRelp _ _ _ _ _ _ _ hrelp hre),
          hs1, hs2, hs3⟩

/-! ## 7. The compositions -/

theorem qconfRows (boot : Nat → Pexv6) (d0 : Efab) (im : Image) (nh : Nat) (GD : Gdexec)
    (i : Nat) :
    gdexecQconf boot d0 im nh GD →
    ∃ em, hartConf i ((GD.gdG.gxProg[i]?).getD []) (boot i) (fun _ => d0) em := by
  intro hq
  cases h : GD.gdG.gxProg[i]? with
  | none => exact ⟨⟨[], boot i⟩, hartConfNil i (boot i) _⟩
  | some row =>
    obtain ⟨em, hem, _, _⟩ := gdexecQconfRows _ _ _ _ _ hq i row h
    exact ⟨em, hem⟩

theorem progRowNil (G : Gexec) (i : Nat) : G.gxProg.length ≤ i → (G.gxProg[i]?).getD [] = [] := by
  intro h
  rw [List.getElem?_eq_none h]
  rfl

theorem gxhNharts (G : Gexec) (cs : List Nat) :
    (gxHull G cs).gxProg.length ≤ G.gxProg.length := by
  simp only [gxHull, List.length_map, List.length_zipWith]
  omega

/-! ### 7.1 The hull route -/

theorem hullSupply (boot : Nat → Pexv6) (d0 : Efab) (GD : Gdexec) (cs : List Nat)
    (N : Nat) :
    rvwmoMinusDepsConsistent GD →
    hullOk GD.gdG cs →
    (∀ e w, gcut cs e = true → gcut cs w = true → ¬ gviol GD.gdG e w) →
    ∀ im nh, gdexecQconf boot d0 im nh GD →
    GD.gdG.gxProg.length ≤ N →
    ∃ c : Cand,
      srvwmoConsistent c ∧
      c.cdImg = GD.gdG.gxImg ∧
      (candFetchInert boot d0 N c →
        ∃ pst : Nat → List Pexv6,
          pst 0 = (List.range' 0 N).map boot ∧
          execProgOk' pstepEv pclsEv pst (fun _ => d0) (candExec c)) ∧
      cdLog c c.cdTr.length =
        ((gwrites GD.gdG).filter (gcut cs)).filterMap (WeakRvwmoLin.gmsg GD.gdG) := by
  intro hcons hok hvf im nh hq hN
  obtain ⟨c, hsr, himg, hrow, hlog⟩ := hullLinearizes GD cs hcons hok hvf
  refine ⟨c, hsr, himg, fun hfi => ?_, hlog⟩
  exact supplyOfQconf c boot d0 (fun i => ((gxHull GD.gdG cs).gxProg[i]?).getD []) N
    (fun i => by rw [hrow i, gxhRow])
    (fun i hi => progRowNil _ _ (by have := gxhNharts GD.gdG cs; omega))
    (fun i _ => qconfRows boot d0 im nh (gdHull GD cs) i (gdexecQconfHull boot d0 im nh GD cs hq))
    hfi

/-! ### 7.2 The acyclicity route -/

theorem topoSupply (boot : Nat → Pexv6) (d0 : Efab) (GD : Gdexec) (N : Nat) :
    rvwmoMinusDepsConsistent GD →
    (∀ x y, Decidable (racyD GD x y)) →
    (∀ x, ¬ tc (racyD GD) x x) →
    ∀ im nh, gdexecQconf boot d0 im nh GD →
    GD.gdG.gxProg.length ≤ N →
    ∃ c : Cand,
      srvwmoConsistent c ∧
      c.cdImg = GD.gdG.gxImg ∧
      (candFetchInert boot d0 N c →
        ∃ pst : Nat → List Pexv6,
          pst 0 = (List.range' 0 N).map boot ∧
          execProgOk' pstepEv pclsEv pst (fun _ => d0) (candExec c)) := by
  intro hcons hdec hacy im nh hq hN
  obtain ⟨GD', pi, hcons', h14, hrr, hdeps, _⟩ := normalizeOfAcyclic GD hcons hdec hacy
  have hq' := gdexecQconfRen pi boot d0 im nh GD GD' hrr hdeps hq
  obtain ⟨c, hsr, himg, hrow, _⟩ := rule14Linearization GD'.gdG hcons'.1 h14
  refine ⟨c, hsr, by rw [himg]; exact rowsRelImg pi _ _ hrr, fun hfi => ?_⟩
  exact supplyOfQconf c boot d0 (fun i => (GD'.gdG.gxProg[i]?).getD []) N hrow
    (fun i hi => progRowNil _ _ (by rw [rowsRelNharts pi _ _ hrr]; omega))
    (fun i _ => qconfRows boot d0 im nh GD' i hq') hfi

/-! ## 8. Smoke tests -/

def smokeTr : List Estep :=
  [⟨0, .LStore false 0 [0#8] .WCplain⟩,
   ⟨1, .LFence false true false true⟩,
   ⟨0, .LStore false 8 [0#8] .WCplain⟩]

def smokeC : Cand := ⟨fun _ => none, smokeTr⟩

theorem smokeTrow0 :
    trow 0 smokeTr = [.LStore false 0 [0#8] .WCplain, .LStore false 8 [0#8] .WCplain] := by
  decide

theorem smokeTrow1 : trow 1 smokeTr = [.LFence false true false true] := by decide

theorem smokeTcnt0 : tcnt 0 (smokeTr.take 2) = 1 := by decide

theorem smokeTcnt1 : tcnt 1 (smokeTr.take 2) = 1 := by decide

theorem smokeRowRelp : (rowWs (trow 1 smokeTr) (tcnt 1 (smokeTr.take 2))).wRelp = true := by
  decide

theorem smokeCandRelp : ((stt (candExec smokeC) 2).msWs 1).wRelp = true :=
  (candWsRelp smokeC 1 2 (by decide)).trans smokeRowRelp

/-- ... and the agent that has NOT fenced still has it clear. -/
theorem smokeCandRelp0 : ((stt (candExec smokeC) 2).msWs 0).wRelp = false := by
  rw [candWsRelp smokeC 0 2 (by decide)]
  decide

end Weak
