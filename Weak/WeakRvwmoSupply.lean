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
2. O2 / STAGE C — THE FETCH IS ADMINISTRATIVE, PINNED TO THE BOOT IMAGE (`WeakRvwmoConf`
   deviation 3, `WeakAxRealize` deviation 4; owner ruling Q-C1, `notes/weak-port-o2-stageC.md`
   §B).  Rocq's fetch was an `LLoad false` row item whose value came from rf-from-init; in Lean
   the fetch `LIFetch base tvs` is an administrative label (no row item), and its only
   graph-tier content — the bytes are the boot image at timestamp 0 — is stated ONCE, on the
   emission, and carried into the supply by the PINNED program LTS
   `WeakAxRealize.pstepPin im pstepEv`.  So:
   - Lean-only `emFetchImg im em` (every label of the emission is `WeakAxRealize.fetchPin im`, i.e. every fetch
     item reads the image at timestamp 0; `True` off the fetch) and the extra `gdexecQconf`
     conjunct `emFetchImg im em` (between `emDevfree em` and the deps clause; also returned by
     `gdexecQconfRows` and `qconfRows`).  Stable under the hull (`emFetchImgPrefix`) and the
     renaming (`emFetchImgRen`, since `wlblRen` fixes `LIFetch`, Q-C4).
   - Lean-only `admRunPin` (an `admRun` whose labels are pinned is an `admStar` of the pinned
     LTS) and `hblockPin` / `hemitStatesPin` / `hartConfStatesPin` (Rocq's `hblock` /
     `hemitStates` / `hartConfStates` at the pinned LTS, from a pinned emission; Rocq's three
     are kept as stated).
   - `supplyOfQconf`: Rocq's three premises, the third with `∧ emFetchImg c.cdImg em`, and the
     conclusion `execProgOk' (pstepPin c.cdImg pstepEv) pclsEv …` (the pinned LTS).
   - `hullSupply` / `topoSupply`: Rocq's statements, the supply at `pstepPin c.cdImg pstepEv`
     (unconditional).  Stage B's `emFetchInert`, `candFetchInert`, `hblockIn`,
     `hblockInHblock`, `hblockInMono`, `hemitStatesIn`, `hartConfStatesIn` are DELETED.
3. PROOFS: per-constructor case analysis and `omega`; the smoke tests (Rocq `Example …
   vm_compute`) are `theorem`s closed by `decide` / the bridge; Rocq's `Print Assumptions` audit
   is not reproduced (the lint bans axioms).
4. Lean-only helpers: `filterTakeSucc` (the `take (k+1)` step of a filter), `fetchPinRen`,
   and deviation 2's `emFetchImg`/`emFetchImgRen`/`emFetchImgPrefix`/`admRunPin`/`hblockPin`/
   `hblockPinHblock`/`hemitStatesPin`/`hartConfStatesPin`.
5. W-DISK (plan `notes/weak-allocproc-plan.md` §C "W-DISK", [R17.3]): `WeakEvInst.pdevEv` is
   STATE-AWARE (a disk at a `DWriteDev` node moves the fabric under an `LDev`-free label), so
   Rocq's §2 statements quantified over an arbitrary start `p` are FALSE as stated.  They gain the
   START-STATE hypothesis `devQuiet p` (the Lean-only `devQuiet`: the disk between bursts, any
   hart), kept along an `LDev`-free run by `devQuietStep` / `admRunQuiet`: `pdevEvFalse` (a NEW
   proof by cases on `p`), `pstepEvDevfree`, `admRunDevfree`, `admRunRefab`,
   `hemitDevfreeConst`, `hemitDevfreeRefab`, `hemitDevfreeReindex`.  The quiescent bundle's
   consumers do not use them (its supply reads the fabric off `fun _ => d0` directly).

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

**W12 (1) (plan §C W12; D25 (a) [OWN.5]) — statement edit (Lean-only).**  `topoSupply` takes the core `rvwmoCoreD`.  RVWMO⁻ callers
are unchanged in text (`WeakRvwmoAcyc.coeCoreOfMinus`).
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

/-- W13 (E) (Lean-only): `notElemOfBlock` at every payload of the fabric marker. -/
theorem notDevOfBlock (ls : List Wlabel) (l : Wlabel) (es : List Wlabel) :
    (∀ kd ba bs, LDev kd ba bs ∉ ls ++ l :: es) →
    (∀ kd ba bs, LDev kd ba bs ∉ ls) ∧ (∀ kd ba bs, l ≠ LDev kd ba bs) ∧
      (∀ kd ba bs, LDev kd ba bs ∉ es) :=
  fun h => ⟨fun kd ba bs => (notElemOfBlock _ _ _ _ (h kd ba bs)).1,
    fun kd ba bs => (notElemOfBlock _ _ _ _ (h kd ba bs)).2.1,
    fun kd ba bs => (notElemOfBlock _ _ _ _ (h kd ba bs)).2.2⟩

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

/-- **THE START-STATE HYPOTHESIS** (W-DISK, plan [R17.3]): the disk agent is BETWEEN bursts
(no residual program); a hart state is always quiet.  Under W-DISK's state-aware `pdevEv` an
`LDev`-free disk step MOVES the fabric at a `DWriteDev` node, so the fabric-blindness lemmas
below quantify over quiet starts only (discharged at the boot pool `epsInit`, whose disk is
`.PDisk none`). -/
def devQuiet : Pexv6 → Prop
  | .PDisk (some _) => False
  | _ => True

/-- No START, no burst: every arm out of `.PDisk none` (START, the UART / PLIC moves) is
`LDev`, so an `LDev`-free step keeps the state quiet. -/
theorem devQuietStep (p : Pexv6) (d : Efab) (l : Wlabel) (p' : Pexv6) (d' : Efab) :
    pstepEv p d l p' d' → (∀ kd ba bs, l ≠ LDev kd ba bs) → devQuiet p → devQuiet p' := by
  intro hs hne hq
  cases p with
  | PHart cpu m rs fn ib =>
    cases p' with
    | PHart => trivial
    | PDisk => exact hs.elim
  | PDisk dp =>
    cases dp with
    | some _ => exact hq.elim
    | none =>
      cases p' with
      | PHart => exact hs.elim
      | PDisk dp' =>
        exfalso
        rcases hs with ⟨h, -⟩ | ⟨_, hl, _⟩
        · rcases h with ⟨_, hl, _⟩ | ⟨_, _, _, _, _, hdp, _⟩ | ⟨_, hdp, _⟩ |
            ⟨_, _, _, _, _, _, _, hdp, _⟩ | ⟨_, _, _, _, _, _, hdp, _⟩ |
            ⟨_, _, _, _, _, _, hdp, _⟩ | ⟨_, _, hdp, _⟩ | ⟨_, _, hdp, _⟩ | ⟨hdp, _⟩ | ⟨hdp, _⟩
          · exact hne _ _ _ hl
          all_goals exact nomatch hdp
        · exact hne _ _ _ hl

/-- The marker vanishes on an `LDev`-free step FROM A QUIET STATE (W-DISK: a new proof by
cases on `p`; the label alone no longer decides it). -/
theorem pdevEvFalse (p : Pexv6) (l : Wlabel) (p' : Pexv6) :
    devQuiet p → (∀ kd ba bs, l ≠ LDev kd ba bs) → pdevEv p l p' = false := by
  intro hq h
  cases p with
  | PHart => cases l <;> first | rfl | exact absurd rfl (h _ _ _)
  | PDisk dp =>
    cases dp with
    | some _ => exact hq.elim
    | none => cases l <;> first | rfl | exact absurd rfl (h _ _ _)

theorem pstepEvDevfree (p : Pexv6) (d : Efab) (l : Wlabel) (p' : Pexv6) (d' : Efab) :
    devQuiet p → pstepEv p d l p' d' → (∀ kd ba bs, l ≠ LDev kd ba bs) →
    d' = d ∧ ∀ d0, pstepEv p d0 l p' d0 :=
  fun hq hs hne => pdevEvOk p d l p' d' hs (pdevEvFalse p l p' hq hne)

/-! ### 2.1 The administrative run -/

/-- (Lean-only, W-DISK) An `LDev`-free administrative run keeps the state quiet. -/
theorem admRunQuiet (instr : Bool) (p : Pexv6) (d : Efab) (ls : List Wlabel) (p' : Pexv6)
    (d' : Efab) : admRun instr p d ls p' d' → (∀ kd ba bs, LDev kd ba bs ∉ ls) →
    devQuiet p → devQuiet p' := by
  intro h
  induction h with
  | ARnil => intro _ hq; exact hq
  | ARcons p d l p1 d1 ls p' d' _ hs _ ih =>
    intro hnd hq
    have hne : (∀ kd ba bs, l ≠ LDev kd ba bs) := fun kd ba bs he => hnd kd ba bs (by simp [he])
    exact ih (fun kd ba bs hin => hnd kd ba bs (List.mem_cons_of_mem _ hin))
      (devQuietStep _ _ _ _ _ hs hne hq)

theorem admRunDevfree (instr : Bool) (p : Pexv6) (d : Efab) (ls : List Wlabel) (p' : Pexv6)
    (d' : Efab) : admRun instr p d ls p' d' → devQuiet p → (∀ kd ba bs, LDev kd ba bs ∉ ls) →
    d' = d := by
  intro h
  induction h with
  | ARnil => intro _ _; rfl
  | ARcons p d l p1 d1 ls p' d' _ hs _ ih =>
    intro hq hnd
    have hne : (∀ kd ba bs, l ≠ LDev kd ba bs) := fun kd ba bs he => hnd kd ba bs (by simp [he])
    obtain ⟨hd, _⟩ := pstepEvDevfree _ _ _ _ _ hq hs hne
    rw [ih (devQuietStep _ _ _ _ _ hs hne hq)
      (fun kd ba bs hin => hnd kd ba bs (List.mem_cons_of_mem _ hin)), hd]

theorem admRunRefab (instr : Bool) (p : Pexv6) (d : Efab) (ls : List Wlabel) (p' : Pexv6)
    (d' : Efab) : admRun instr p d ls p' d' → devQuiet p → (∀ kd ba bs, LDev kd ba bs ∉ ls) →
    ∀ d0, admRun instr p d0 ls p' d0 := by
  intro h
  induction h with
  | ARnil p d => intro _ _ d0; exact .ARnil p d0
  | ARcons p d l p1 d1 ls p' d' ha hs _ ih =>
    intro hq hnd d0
    have hne : (∀ kd ba bs, l ≠ LDev kd ba bs) := fun kd ba bs he => hnd kd ba bs (by simp [he])
    have hrest : ∀ kd ba bs, LDev kd ba bs ∉ ls :=
      fun kd ba bs hin => hnd kd ba bs (List.mem_cons_of_mem _ hin)
    obtain ⟨_, hall⟩ := pstepEvDevfree _ _ _ _ _ hq hs hne
    exact .ARcons p d0 l p1 d0 ls p' d0 ha (hall d0) (ih (devQuietStep _ _ _ _ _ hs hne hq) hrest d0)

/-! ### 2.2 The emission -/

theorem hemitDevfreeConst (dv : Nat → Efab) (k : Nat) (ws : Wstate) (row : List Lbl)
    (p : Pexv6) (es : List Eitem) (pfin : Pexv6) :
    hemit dv k ws row p es pfin → devQuiet p → (∀ kd ba bs, LDev kd ba bs ∉ es.map Prod.fst) →
    ∀ j, k ≤ j → j ≤ k + row.length → dv j = dv k := by
  intro h
  induction h with
  | HEnil k ws p =>
    intro _ _ j hlo hhi
    simp only [List.length_nil, Nat.add_zero] at hhi
    have : j = k := by omega
    subst this; rfl
  | HEone k ws lb row p ls pa da l p' es pfin har _ hst _ ih =>
    intro hq hnd j hlo hhi
    rw [eblockFst] at hnd
    obtain ⟨hne1, hnel, hrest⟩ := notDevOfBlock _ _ _ hnd
    have hda : da = dv k := admRunDevfree _ _ _ _ _ _ har hq hne1
    have hqa := admRunQuiet _ _ _ _ _ _ har hne1 hq
    obtain ⟨hd, _⟩ := pstepEvDevfree _ _ _ _ _ hqa hst hnel
    have hsk : dv (k + 1) = dv k := by rw [hd, hda]
    by_cases hjk : j = k
    · subst hjk; rfl
    · simp only [List.length_cons] at hhi
      rw [ih (devQuietStep _ _ _ _ _ hst hnel hqa) hrest j (by omega) (by omega), hsk]
  | HEpair k ws lb row p ls1 pa da l1 pm dm ls2 pm2 dm2 l2 p' es pfin har1 _ hst1 har2 hst2 _ ih =>
    intro hq hnd j hlo hhi
    rw [eblockFst, eblockFst] at hnd
    obtain ⟨hne1, hnel1, hnd2⟩ := notDevOfBlock _ _ _ hnd
    obtain ⟨hne2, hnel2, hrest⟩ := notDevOfBlock _ _ _ hnd2
    have hda : da = dv k := admRunDevfree _ _ _ _ _ _ har1 hq hne1
    have hqa := admRunQuiet _ _ _ _ _ _ har1 hne1 hq
    obtain ⟨hd1, _⟩ := pstepEvDevfree _ _ _ _ _ hqa hst1 hnel1
    have hqm := devQuietStep _ _ _ _ _ hst1 hnel1 hqa
    have hdm2 : dm2 = dm := admRunDevfree _ _ _ _ _ _ har2 hqm hne2
    have hqm2 := admRunQuiet _ _ _ _ _ _ har2 hne2 hqm
    obtain ⟨hd2, _⟩ := pstepEvDevfree _ _ _ _ _ hqm2 hst2 hnel2
    have hsk : dv (k + 1) = dv k := by rw [hd2, hdm2, hd1, hda]
    by_cases hjk : j = k
    · subst hjk; rfl
    · simp only [List.length_cons] at hhi
      rw [ih (devQuietStep _ _ _ _ _ hst2 hnel2 hqm2) hrest j (by omega) (by omega), hsk]

/-- THE REFABRICATION (Rocq's recorded STATEMENT CORRECTION: the emission replays at any fabric
assignment CONSTANT on the block's index range, with no relation to `dv` at all). -/
theorem hemitDevfreeRefab (dv : Nat → Efab) (k : Nat) (ws : Wstate) (row : List Lbl)
    (p : Pexv6) (es : List Eitem) (pfin : Pexv6) :
    hemit dv k ws row p es pfin → devQuiet p → (∀ kd ba bs, LDev kd ba bs ∉ es.map Prod.fst) →
    ∀ (dv' : Nat → Efab) (d0 : Efab),
      (∀ j, k ≤ j → j ≤ k + row.length → dv' j = d0) →
      hemit dv' k ws row p es pfin := by
  intro h
  induction h with
  | HEnil k ws p => intro _ _ dv' d0 _; exact .HEnil k ws p
  | HEone k ws lb row p ls pa da l p' es pfin har hre hst _ ih =>
    intro hq hnd dv' d0 hc
    rw [eblockFst] at hnd
    obtain ⟨hne1, hnel, hrest⟩ := notDevOfBlock _ _ _ hnd
    have hqa := admRunQuiet _ _ _ _ _ _ har hne1 hq
    obtain ⟨_, hall⟩ := pstepEvDevfree _ _ _ _ _ hqa hst hnel
    refine .HEone k ws lb row p ls pa d0 l p' es pfin ?_ hre ?_ ?_
    · rw [hc k (Nat.le_refl _) (by simp)]
      exact admRunRefab _ _ _ _ _ _ har hq hne1 d0
    · rw [hc (k + 1) (by omega) (by simp only [List.length_cons]; omega)]
      exact hall d0
    · exact ih (devQuietStep _ _ _ _ _ hst hnel hqa) hrest dv' d0
        (fun j hlo hhi => hc j (by omega) (by simp only [List.length_cons]; omega))
  | HEpair k ws lb row p ls1 pa da l1 pm dm ls2 pm2 dm2 l2 p' es pfin har1 hre hst1 har2 hst2 _ ih =>
    intro hq hnd dv' d0 hc
    rw [eblockFst, eblockFst] at hnd
    obtain ⟨hne1, hnel1, hnd2⟩ := notDevOfBlock _ _ _ hnd
    obtain ⟨hne2, hnel2, hrest⟩ := notDevOfBlock _ _ _ hnd2
    have hqa := admRunQuiet _ _ _ _ _ _ har1 hne1 hq
    obtain ⟨_, hall1⟩ := pstepEvDevfree _ _ _ _ _ hqa hst1 hnel1
    have hqm := devQuietStep _ _ _ _ _ hst1 hnel1 hqa
    have hqm2 := admRunQuiet _ _ _ _ _ _ har2 hne2 hqm
    obtain ⟨_, hall2⟩ := pstepEvDevfree _ _ _ _ _ hqm2 hst2 hnel2
    refine .HEpair k ws lb row p ls1 pa d0 l1 pm d0 ls2 pm2 d0 l2 p' es pfin ?_ hre (hall1 d0)
      (admRunRefab _ _ _ _ _ _ har2 hqm hne2 d0) ?_ ?_
    · rw [hc k (Nat.le_refl _) (by simp)]
      exact admRunRefab _ _ _ _ _ _ har1 hq hne1 d0
    · rw [hc (k + 1) (by omega) (by simp only [List.length_cons]; omega)]
      exact hall2 d0
    · exact ih (devQuietStep _ _ _ _ _ hst2 hnel2 hqm2) hrest dv' d0
        (fun j hlo hhi => hc j (by omega) (by simp only [List.length_cons]; omega))

theorem hemitDevfreeReindex (dv : Nat → Efab) (k : Nat) (ws : Wstate) (row : List Lbl)
    (p : Pexv6) (es : List Eitem) (pfin : Pexv6) :
    hemit dv k ws row p es pfin → devQuiet p → (∀ kd ba bs, LDev kd ba bs ∉ es.map Prod.fst) →
    ∀ d0 : Efab, hemit (fun _ => d0) k ws row p es pfin :=
  fun hem hq hnd d0 => hemitDevfreeRefab dv k ws row p es pfin hem hq hnd _ d0 (fun _ _ _ => rfl)

/-! ## 3. The quiescent conformance bundle -/

def emDevfree (em : Hemission) : Prop := ∀ kd ba bs, LDev kd ba bs ∉ emLabels em

/-- (Lean-only, deviation 2) Every administrative fetch item of the emission reads the booted
image at timestamp 0 (`fetchPin` is `True` off the fetch). -/
def emFetchImg (im : Image) (em : Hemission) : Prop := ∀ l, l ∈ emLabels em → WeakAxRealize.fetchPin im l

/-- THE QUIESCENT BUNDLE, with the BOOT TIE (`im` the booted image, `nh` the booted hart count);
deviation 2: the emission's fetches are pinned to `im`. -/
def gdexecQconf (boot : Nat → Pexv6) (d0 : Efab) (im : Image) (nh : Nat) (GD : Gdexec) :
    Prop :=
  GD.gdG.gxImg = im ∧
  GD.gdG.gxProg.length ≤ nh ∧
  (∀ i row, GD.gdG.gxProg[i]? = some row →
    ∃ em, hartConf i row (boot i) (fun _ => d0) em ∧
          emDevfree em ∧
          emFetchImg im em ∧
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
            emFetchImg im em ∧
            (∀ jk, jk ∈ rowDeps em.emItems → ((i, jk.1), (i, jk.2)) ∈ GD.gdDeps) :=
  fun h => h.2.2

/-- The bundle IS a `gdexecConf` bundle. -/
theorem gdexecQconfConf (boot : Nat → Pexv6) (d0 : Efab) (im : Image) (nh : Nat)
    (GD : Gdexec) : gdexecQconf boot d0 im nh GD → gdexecConf boot (fun _ _ => d0) GD := by
  rintro ⟨_, _, h⟩ i row hrow
  obtain ⟨em, hem, _, _, hdep⟩ := h i row hrow
  exact ⟨em, hem, hdep⟩

/-! ### 3.1 `emDevfree` is stable under the two emission operations -/

theorem wlblRenDev (π : Nat → Nat) (l : Wlabel) (kd : IoKind) (ba : Int) (bs : List (BitVec 8)) :
    wlblRen π l = LDev kd ba bs → l = LDev kd ba bs := by
  cases l <;> simp [wlblRen]

theorem emDevfreeRen (π : Nat → Nat) (em : Hemission) : emDevfree em → emDevfree (emRen π em) := by
  unfold emDevfree
  rw [emLabelsRen]
  intro h kd ba bs hin
  obtain ⟨l, hl, heq⟩ := List.mem_map.1 hin
  rw [wlblRenDev π l kd ba bs heq] at hl
  exact h kd ba bs hl

theorem emDevfreePrefix (em em' : Hemission) :
    em'.emItems <+: em.emItems → emDevfree em → emDevfree em' := by
  rintro ⟨t, ht⟩ h kd ba bs hin
  apply h kd ba bs
  unfold emLabels at hin ⊢
  rw [← ht, List.map_append]
  exact List.mem_append_left _ hin

/-! ### 3.1b `emFetchImg` is stable under the two emission operations (deviation 2) -/

/-- (Lean-only) `wlblRen` fixes the fetch (Q-C4), so the pin is renaming-invariant. -/
theorem fetchPinRen (π : Nat → Nat) (im : Image) (l : Wlabel) :
    WeakAxRealize.fetchPin im (wlblRen π l) ↔ WeakAxRealize.fetchPin im l := by
  cases l <;> exact Iff.rfl

theorem emFetchImgRen (π : Nat → Nat) (im : Image) (em : Hemission) :
    emFetchImg im em → emFetchImg im (emRen π em) := by
  unfold emFetchImg
  rw [emLabelsRen]
  intro h l hl
  obtain ⟨l0, hl0, rfl⟩ := List.mem_map.1 hl
  exact (fetchPinRen π im l0).2 (h l0 hl0)

theorem emFetchImgPrefix (im : Image) (em em' : Hemission) :
    em'.emItems <+: em.emItems → emFetchImg im em → emFetchImg im em' := by
  rintro ⟨t, ht⟩ h l hin
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
        obtain ⟨em, hem, hdf, hfi, hdep⟩ := hq i p hp
        obtain ⟨em', hem', hpre⟩ := hartConfPrefix i p (boot i) (fun _ => d0) em c hem
        refine ⟨emRen (hren GD.gdG cs) em', hartConfRen _ _ _ _ _ _ hem',
          emDevfreeRen _ _ (emDevfreePrefix em em' hpre hdf),
          emFetchImgRen _ _ _ (emFetchImgPrefix im em em' hpre hfi), ?_⟩
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
    obtain ⟨em, hem, hdf, hfi, hdep⟩ := hq i row hrow0
    refine ⟨emRen π em, hartConfRen π i row (boot i) _ em hem, emDevfreeRen π em hdf,
      emFetchImgRen π im em hfi, ?_⟩
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

/-- (Lean-only, deviation 2) An `admRun` whose labels are pinned is a run of the pinned LTS. -/
theorem admRunPin (im : Image) (instr : Bool) (p : Pexv6) (d : Efab) (ls : List Wlabel)
    (p' : Pexv6) (d' : Efab) :
    admRun instr p d ls p' d' → (∀ l, l ∈ ls → WeakAxRealize.fetchPin im l) →
    admStar (pstepPin im pstepEv) instr p d p' d' := by
  intro h
  induction h with
  | ARnil p d => intro _; exact admStarRefl _ instr p d
  | ARcons p d l p1 d1 ls p' d' ha hs _ ih =>
    intro hpin
    exact admStarL (pstepPin im pstepEv) instr p d l p1 d1 p' d' ha
      ⟨hs, hpin l List.mem_cons_self⟩ (ih (fun x hx => hpin x (List.mem_cons_of_mem _ hx)))

/-- (Lean-only, deviation 2) `hblock` at the pinned LTS. -/
def hblockPin (im : Image) (dv : Nat → Efab) (k : Nat) (ws : Wstate) (lb : Lbl)
    (p p' : Pexv6) : Prop :=
  ∃ (pa : Pexv6) (da : Efab),
    admStar (pstepPin im pstepEv) true p (dv k) pa da ∧
    ((∃ l, hlblRealizes pa ws lb l ∧ pstepPin im pstepEv pa da l p' (dv (k + 1)))
     ∨ (∃ (pm : Pexv6) (dm : Efab) (pm2 : Pexv6) (dm2 : Efab) (l1 l2 : Wlabel),
          hlblRealizesPair pa pm2 ws lb l1 l2 ∧
          pstepPin im pstepEv pa da l1 pm dm ∧
          admStar (pstepPin im pstepEv) false pm dm pm2 dm2 ∧
          pstepPin im pstepEv pm2 dm2 l2 p' (dv (k + 1))))

theorem hblockPinHblock (im : Image) (dv : Nat → Efab) (k : Nat) (ws : Wstate) (lb : Lbl)
    (p p' : Pexv6) : hblockPin im dv k ws lb p p' → hblock dv k ws lb p p' := by
  have hsub : ∀ (instr : Bool) (p d p' d'),
      admStar (pstepPin im pstepEv) instr p d p' d' → admStar pstepEv instr p d p' d' :=
    fun _ _ _ _ _ h => rtc_subrel (fun _ _ ⟨l, ha, hs⟩ => ⟨l, ha, hs.1⟩) h
  rintro ⟨pa, da, hs, ⟨l, h1, h2⟩ | ⟨pm, dm, pm2, dm2, l1, l2, h1, h2, h3, h4⟩⟩
  · exact ⟨pa, da, hsub _ _ _ _ _ hs, .inl ⟨l, h1, h2.1⟩⟩
  · exact ⟨pa, da, hsub _ _ _ _ _ hs,
      .inr ⟨pm, dm, pm2, dm2, l1, l2, h1, h2.1, hsub _ _ _ _ _ h3, h4.1⟩⟩

theorem hemitStates (dv : Nat → Efab) (k : Nat) (ws : Wstate) (row : List Lbl)
    (p : Pexv6) (es : List Eitem) (pfin : Pexv6) :
    hemit dv k ws row p es pfin →
    ∃ f : Nat → Pexv6, f 0 = p ∧
      ∀ n lb, row[n]? = some lb →
        hblock dv (n + k) (rowWsAux k ws (row.take n)) lb (f n) (f (n + 1)) := by
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
      refine ⟨pa, da, admRunStar _ _ _ _ _ _ har, .inl ⟨l, hre, ?_⟩⟩
      show pstepEv pa da l (f' 0) (dv (k + 1))
      rw [hf0]; exact hst
    | succ n =>
      simp only [List.getElem?_cons_succ] at hn
      have e : n + 1 + k = n + (k + 1) := by omega
      rw [e]
      exact hf n lb0 hn
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
      exact hf n lb0 hn

/-- (Lean-only, deviation 2) `hemitStates` at the pinned LTS, from a pinned emission. -/
theorem hemitStatesPin (im : Image) (dv : Nat → Efab) (k : Nat) (ws : Wstate) (row : List Lbl)
    (p : Pexv6) (es : List Eitem) (pfin : Pexv6) :
    hemit dv k ws row p es pfin → (∀ x, x ∈ es.map Prod.fst → WeakAxRealize.fetchPin im x) →
    ∃ f : Nat → Pexv6, f 0 = p ∧
      ∀ n lb, row[n]? = some lb →
        hblockPin im dv (n + k) (rowWsAux k ws (row.take n)) lb (f n) (f (n + 1)) := by
  intro h
  induction h with
  | HEnil k ws p => intro _; exact ⟨fun _ => p, rfl, fun n lb hn => by simp at hn⟩
  | HEone k ws lb row p ls pa da l p' es pfin har hre hst _ ih =>
    intro hpin
    rw [eblockFst] at hpin
    obtain ⟨f', hf0, hf⟩ :=
      ih (fun x hx => hpin x (List.mem_append_right _ (List.mem_cons_of_mem _ hx)))
    refine ⟨fun n => match n with | 0 => p | n' + 1 => f' n', rfl, ?_⟩
    intro n lb0 hn
    cases n with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hn
      subst hn
      rw [Nat.zero_add]
      refine ⟨pa, da, admRunPin im _ _ _ _ _ _ har
          (fun x hx => hpin x (List.mem_append_left _ hx)),
        .inl ⟨l, hre, ?_, hpin l (List.mem_append_right _ List.mem_cons_self)⟩⟩
      show pstepEv pa da l (f' 0) (dv (k + 1))
      rw [hf0]; exact hst
    | succ n =>
      simp only [List.getElem?_cons_succ] at hn
      have e : n + 1 + k = n + (k + 1) := by omega
      rw [e]
      exact hf n lb0 hn
  | HEpair k ws lb row p ls1 pa da l1 pm dm ls2 pm2 dm2 l2 p' es pfin har1 hre hst1 har2 hst2 _ ih =>
    intro hpin
    rw [eblockFst, eblockFst] at hpin
    have h2 : ∀ x, x ∈ ls2 ++ l2 :: es.map Prod.fst → WeakAxRealize.fetchPin im x :=
      fun x hx => hpin x (List.mem_append_right _ (List.mem_cons_of_mem _ hx))
    obtain ⟨f', hf0, hf⟩ :=
      ih (fun x hx => h2 x (List.mem_append_right _ (List.mem_cons_of_mem _ hx)))
    refine ⟨fun n => match n with | 0 => p | n' + 1 => f' n', rfl, ?_⟩
    intro n lb0 hn
    cases n with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hn
      subst hn
      rw [Nat.zero_add]
      refine ⟨pa, da, admRunPin im _ _ _ _ _ _ har1
          (fun x hx => hpin x (List.mem_append_left _ hx)),
        .inr ⟨pm, dm, pm2, dm2, l1, l2, hre,
          ⟨hst1, hpin l1 (List.mem_append_right _ List.mem_cons_self)⟩,
          admRunPin im _ _ _ _ _ _ har2 (fun x hx => h2 x (List.mem_append_left _ hx)),
          ?_, h2 l2 (List.mem_append_right _ List.mem_cons_self)⟩⟩
      show pstepEv pm2 dm2 l2 (f' 0) (dv (k + 1))
      rw [hf0]; exact hst2
    | succ n =>
      simp only [List.getElem?_cons_succ] at hn
      have e : n + 1 + k = n + (k + 1) := by omega
      rw [e]
      exact hf n lb0 hn

theorem hartConfStates (i : Nat) (row : List Lbl) (p0 : Pexv6) (dv : Nat → Efab)
    (em : Hemission) :
    hartConf i row p0 dv em →
    ∃ f : Nat → Pexv6, f 0 = p0 ∧
      ∀ n lb, row[n]? = some lb → hblock dv n (rowWs row n) lb (f n) (f (n + 1)) := by
  intro hem
  obtain ⟨f, hf0, hf⟩ := hemitStates _ _ _ _ _ _ _ hem
  refine ⟨f, hf0, fun n lb hn => ?_⟩
  have h := hf n lb hn
  rw [Nat.add_zero] at h
  exact h

/-- (Lean-only, deviation 2) `hartConfStates` at the pinned LTS, from a pinned emission. -/
theorem hartConfStatesPin (im : Image) (i : Nat) (row : List Lbl) (p0 : Pexv6)
    (dv : Nat → Efab) (em : Hemission) :
    hartConf i row p0 dv em → emFetchImg im em →
    ∃ f : Nat → Pexv6, f 0 = p0 ∧
      ∀ n lb, row[n]? = some lb → hblockPin im dv n (rowWs row n) lb (f n) (f (n + 1)) := by
  intro hem hfi
  obtain ⟨f, hf0, hf⟩ := hemitStatesPin im _ _ _ _ _ _ _ hem hfi
  refine ⟨f, hf0, fun n lb hn => ?_⟩
  have h := hf n lb hn
  rw [Nat.add_zero] at h
  exact h

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
  | LIo => rfl

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

theorem supplyOfQconf (c : Cand) (boot : Nat → Pexv6) (d0 : Efab)
    (rows : Nat → List Lbl) (N : Nat) :
    -- the trace is an interleaving of the rows ...
    (∀ i, (c.cdTr.filter (fun s => decide (s.esAg = i))).map (fun s => s.esLb) = rows i) →
    -- ... over the agents below `N` ...
    (∀ i, N ≤ i → rows i = []) →
    -- ... every such agent's row is emittable at the CONSTANT fabric, its fetches pinned to
    -- the candidate's image (deviation 2) ...
    (∀ i, i < N → ∃ em, hartConf i (rows i) (boot i) (fun _ => d0) em ∧ emFetchImg c.cdImg em) →
    -- ... so the trace is supplied by the PINNED program LTS
    ∃ pst : Nat → List Pexv6,
      pst 0 = (List.range' 0 N).map boot ∧
      execProgOk' (pstepPin c.cdImg pstepEv) pclsEv pst (fun _ => d0) (candExec c) := by
  intro hrows hbnd hconf
  have hch : ∀ i, i < N → ∃ fe : Hemission × (Nat → Pexv6),
      fe.2 0 = boot i ∧
      ∀ n lb, (rows i)[n]? = some lb →
        hblockPin c.cdImg (fun _ => d0) n (rowWs (rows i) n) lb (fe.2 n) (fe.2 (n + 1)) := by
    intro i hi
    obtain ⟨em, hem, hfi⟩ := hconf i hi
    obtain ⟨f, hf0, hf⟩ := hartConfStatesPin c.cdImg i _ _ _ em hem hfi
    exact ⟨(em, f), hf0, hf⟩
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
    obtain ⟨_, hfb⟩ := hF _ hiN
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
    · rcases hdisj with ⟨l, hre, hst⟩ | ⟨pm, dm, pm2, dm2, l1, l2, hre, hs1, hs2, hs3⟩
      · left
        exact ⟨l, (hlblRealizesAx _ _ _ _ _).2 (hlblRealizesRelp _ _ _ _ _ hrelp hre), hst⟩
      · right
        exact ⟨pm, dm, pm2, dm2, l1, l2,
          (hlblRealizesPairAx _ _ _ _ _ _ _).1 (hlblRealizesPairRelp _ _ _ _ _ _ _ hrelp hre),
          hs1, hs2, hs3⟩

/-! ## 7. The compositions -/

theorem qconfRows (boot : Nat → Pexv6) (d0 : Efab) (im : Image) (nh : Nat) (GD : Gdexec)
    (i : Nat) :
    gdexecQconf boot d0 im nh GD →
    ∃ em, hartConf i ((GD.gdG.gxProg[i]?).getD []) (boot i) (fun _ => d0) em ∧
      emFetchImg im em := by
  intro hq
  cases h : GD.gdG.gxProg[i]? with
  | none =>
    exact ⟨⟨[], boot i⟩, hartConfNil i (boot i) _, fun l hl => by simp [emLabels] at hl⟩
  | some row =>
    obtain ⟨em, hem, _, hfi, _⟩ := gdexecQconfRows _ _ _ _ _ hq i row h
    exact ⟨em, hem, hfi⟩

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
      (∃ pst : Nat → List Pexv6,
        pst 0 = (List.range' 0 N).map boot ∧
        execProgOk' (pstepPin c.cdImg pstepEv) pclsEv pst (fun _ => d0) (candExec c)) ∧
      cdLog c c.cdTr.length =
        ((gwrites GD.gdG).filter (gcut cs)).filterMap (WeakRvwmoLin.gmsg GD.gdG) := by
  intro hcons hok hvf im nh hq hN
  obtain ⟨c, hsr, himg, hrow, hlog⟩ := hullLinearizes GD cs hcons hok hvf
  have hci : c.cdImg = im := himg.trans (gdexecQconfImg _ _ _ _ _ hq)
  refine ⟨c, hsr, himg, ?_, hlog⟩
  exact supplyOfQconf c boot d0 (fun i => ((gxHull GD.gdG cs).gxProg[i]?).getD []) N
    (fun i => by rw [hrow i, gxhRow])
    (fun i hi => progRowNil _ _ (by have := gxhNharts GD.gdG cs; omega))
    (fun i _ => by
      rw [hci]
      exact qconfRows boot d0 im nh (gdHull GD cs) i (gdexecQconfHull boot d0 im nh GD cs hq))

/-! ### 7.2 The acyclicity route -/

theorem topoSupply (boot : Nat → Pexv6) (d0 : Efab) (GD : Gdexec) (N : Nat) :
    rvwmoCoreD GD →
    (∀ x y, Decidable (racyD GD x y)) →
    (∀ x, ¬ tc (racyD GD) x x) →
    ∀ im nh, gdexecQconf boot d0 im nh GD →
    GD.gdG.gxProg.length ≤ N →
    ∃ c : Cand,
      srvwmoConsistent c ∧
      c.cdImg = GD.gdG.gxImg ∧
      (∃ pst : Nat → List Pexv6,
        pst 0 = (List.range' 0 N).map boot ∧
        execProgOk' (pstepPin c.cdImg pstepEv) pclsEv pst (fun _ => d0) (candExec c)) := by
  intro hcons hdec hacy im nh hq hN
  obtain ⟨GD', pi, hcons', h14, hrr, hdeps, _⟩ := normalizeOfAcyclic GD hcons hdec hacy
  have hq' := gdexecQconfRen pi boot d0 im nh GD GD' hrr hdeps hq
  obtain ⟨c, hsr, himg, hrow, _⟩ := rule14Linearization GD'.gdG hcons'.1 h14
  have hci : c.cdImg = im := himg.trans (gdexecQconfImg _ _ _ _ _ hq')
  refine ⟨c, hsr, by rw [himg]; exact rowsRelImg pi _ _ hrr, ?_⟩
  exact supplyOfQconf c boot d0 (fun i => (GD'.gdG.gxProg[i]?).getD []) N hrow
    (fun i hi => progRowNil _ _ (by rw [rowsRelNharts pi _ _ hrr]; omega))
    (fun i _ => by rw [hci]; exact qconfRows boot d0 im nh GD' i hq')

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
