/-
Weak: **the PROGRAM-CARRYING reverse bridge** (A3(iii), T1-D).

Rocq: `iris/WeakAxRealize.v` @ xxvzwolszwmp (1cc222280).

The Rocq header, in substance: `WeakPromiseBridge` part (E) replays an
axiomatic execution as a promise-free run of the FULL machine, but only for a
program LTS that admits every label (`progFree`).  xv6 is not free, so this
file replaces `progFree` by a PER-EVENT SUPPLY of program steps along the
execution's trace (`execProgOk'`): before each trace event an ADMINISTRATIVE
STAR (labels `projLbl` sends to `none`: `LSilent`, `LDev`, `LRegW`, `LCtrl`,
`LInstr`), then either ONE realizing step (`lblRealizes`: a label outside the
gates whose projection, at the class the machine would stamp, is the event's
label) or the exclusive PAIR (`lblRealizesPair`: `LExLoad`, an `LInstr`-free
admin star, `LExStore`) realizing one axiomatic `LRmw`.  The class premise
`execClsOk` is absorbed into `lblRealizes`; what is added is the
instance-discharged `pclsEqr pcls`.  The conclusion is `cfgMatchd` (image and
LOG equal, per-agent `Wstate`s `wsEqr`-related), not `cfgMatch`.  The three
gates (Rocq table): `lbNobarex` (no bare `LExStore`; a dangling `LExLoad`
realizes a plain load), `latFree`, `lbRfoldfree` (only the operand lists that
still reach a byte fold — a plain load's `asrc` and the fused rmw's `asrc` —
must be empty).  Main results: `mstepWpPfStepProg` (one step),
`mstepWpPfStepPair` (the pair), `execPrefixPfRunProg` / `execWfPfRunProg`
(THE PROGRAM-CARRYING REVERSE BRIDGE), and the `progFree` corollaries
`execPrefixPfRunPf` / `execWfPfRunPf` (the `cfgMatchd` shadows of the
bridge's `execPrefixPfRun` / `execWfPfRun`).

**Deviations from Rocq.**

1. NAMES / VOCABULARY: as `Weak/WeakPromiseBridge.lean` deviations 1-3
   (`<[i := x]> l` ↦ `l.set i x`, `pa_st <$> pc_ags c` ↦
   `c.pcAgs.map Wpagent.paSt`, `S k` ↦ `k + 1`; the section variables `pstep`
   / `pcls` are explicit arguments, in Rocq's order, of every declaration
   that uses them).  `zip_fst_snd` is `MachCSL.Stdpp.zip_fst_snd`;
   `list_insert_id` is the Lean-only helper `listSetLookupId`.
2. CONVERSIONS: as the bridge's deviation 4 (`srcsViewNil`, `readOkD0`,
   `loadPostRunD0` rewrites where Rocq used conversion).  Statements
   unchanged.
3. PROOFS: `adm_star_pf_run` goes by TAIL induction on `rtc` (Rocq: head
   induction; Lean's `rtc` is built from the last step); the
   `admStarMonoRtc` inclusion is `rtc_subrel`.  Statements unchanged.
4. O2 / STAGE C — THE INSTRUCTION FETCH (the Lean-only label `LIFetch`, bridge
   deviation 6; owner rulings Q-C1/Q-C3, `notes/weak-port-o2-stageC.md` §B1).
   The fetch is NOT an axiomatic event: `projLbl (LIFetch ..) = none`, and it is
   an ADMINISTRATIVE label sitting where `LInstr` sits (`lbAdmin instr (LIFetch
   ..) := instr = true`; a fetch never occurs inside a fused pair).  The
   Stage-B fetch-inertness gate (`lbFetchInert`, `lbNoFetch`, the fifth
   `lblRealizes` conjunct, the `LIFetch` arm of `mstepWpPfStepProg`, the
   `lbNoFetch` premise of `lblRealizesUnproj`) is DELETED: `lblRealizes` and
   `lblRealizesUnproj` are Rocq's again.  The graph tier's only fetch content —
   the bytes are the boot image at timestamp 0 — is the PIN `WeakAxRealize.fetchPin img l`
   (`True` off the fetch), carried by the pinned program LTS `pstepPin img
   pstep` (a sub-LTS: `pstepPinSub`, `wpPfStepPinSub`, `wpPfRunPinSub`).
   Replaying an admin fetch (`PFIFetch`, `ifetchOk img log 0 …`) needs the pin,
   so the replay chain takes the Lean-only premise `pstepPinned img pstep`
   (every step of the LTS is pinned to `img`; `pstepPinPinned` for the pinned
   LTS): `admStepPf` (label form `WeakAxRealize.fetchPin c.pcImg l`), `admStarPfRun`,
   `admStarPf`, `mstepWpPfStepPair` (at `c.pcImg`), `execPrefixPfRunProg`,
   `execWfPfRunProg` (at `exImg E`).  The `progFree` corollaries keep Rocq's
   statements (they replay at `pstepPin (exImg E) pstep`, `progFreeExecProgOkPin`,
   and project back).  Lean-only: `fetchPin`, `fetchPinIfetchOk`, `pstepPin`,
   `pstepPinSub`, `pstepPinned`, `pstepPinPinned`, `wpPfStepPinSub`,
   `wpPfRunPinSub`, `progFreeExecProgOkPin`, `execWfPfRunPin` (the replay of a
   pinned supply, projected to the unpinned LTS).
5. W13 (I) (plan `notes/weak-allocproc-plan.md` §C W13 (I); D38 RULED [OWN.14], [OWN.27]):
   an MMIO access / device-side fabric move is an I/O-CLASS EVENT.  `projLbl (LDev kd b vs)
   = some (LIo kd b vs)` (bridge), so `LDev` is DROPPED from `lbAdmin` (the admin alphabet is
   still exactly what `projLbl` sends to `none`); `lblRealizes` is unchanged in text and now
   admits the fabric marker as a LEFT-ARM realizing step of its `LIo` event
   (`lblRealizesUnproj`/`lblRealizesIntro`/`mstepWpPfStepProg` gain the `LDev`/`MStepIo`
   arm, replayed as `PFDev`); `admStepPf` loses its `LDev` arm.  `execProgOk'` is UNCHANGED in
   statement: the I/O step's fabric endpoints are the supply's `dv k → dv (k + 1)`.

**Rocq → Lean name map.**  `lb_nobarex` ↦ `lbNobarex`; `lb_rfoldfree` ↦
`lbRfoldfree`; `lb_depfree_rfoldfree` ↦ `lbDepfreeRfoldfree`;
`lb_rfoldfree_ldepfree` ↦ `lbRfoldfreeLdepfree`; `lb_fused_nobarex` ↦
`lbFusedNobarex`; `lb_admin` ↦ `lbAdmin`; `lb_admin_mono` ↦ `lbAdminMono`;
`lb_admin_proj` ↦ `lbAdminProj`; `lbl_realizes` ↦ `lblRealizes`;
`lbl_realizes_unproj` ↦ `lblRealizesUnproj`; `lbl_realizes_intro` ↦
`lblRealizesIntro`; `lbl_realizes_pair` ↦ `lblRealizesPair`;
`store_post_run_d_res_pair` ↦ `storePostRunDResPair`;
`rmw_latest_excl_ok_ts` ↦ `rmwLatestExclOkTs`; `adm_step` ↦ `admStep`;
`adm_star` ↦ `admStar`; `adm_star_refl` ↦ `admStarRefl`; `adm_star_l` ↦
`admStarL`; `adm_step_mono` ↦ `admStepMono`; `adm_star_mono_rtc` ↦
`admStarMonoRtc`; `adm_star_mono` ↦ `admStarMono`; `exec_prog_ok'` ↦
`execProgOk'`; `exec_prog_ok` ↦ `execProgOk`; `exec_prog_ok_star` ↦
`execProgOkStar`; `exec_prog_ok_single` ↦ `execProgOkSingle`; `adm_step_pf`
↦ `admStepPf`; `adm_star_pf_run` ↦ `admStarPfRun`; `adm_star_pf` ↦
`admStarPf`; `mstep_wp_pf_step_prog` ↦ `mstepWpPfStepProg`;
`mstep_wp_pf_step_pair` ↦ `mstepWpPfStepPair`; `exec_prefix_pf_run_prog` ↦
`execPrefixPfRunProg`; `exec_wf_pf_run_prog` ↦ `execWfPfRunProg`;
`prog_free_exec_prog_ok` ↦ `progFreeExecProgOk`; `exec_prefix_pf_run_pf` ↦
`execPrefixPfRunPf`; `exec_wf_pf_run_pf` ↦ `execWfPfRunPf`.  Lean-only:
`listSetLookupId` and the deviation-4 declarations.

**Not ported:** nothing — every Rocq definition and lemma has a Lean twin.
-/
import Weak.WeakPromiseBridge

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std

/-! ## (0) THE THREE LABEL GATES -/

/-- `l` IS NOT A BARE CONDITIONAL WRITE (`lbFused`'s T1-D replacement: only
`LExStore` is excluded; a dangling `LExLoad` realizes a plain load). -/
def lbNobarex (l : Wlabel) : Prop :=
  match l with
  | .LExStore .. => False
  | _ => True

/-- EVERY OPERAND LIST THAT STILL REACHES A BYTE FOLD IS EMPTY (`lbDepfree`'s
T1-D replacement): a plain load's `asrc` and the fused rmw's `asrc`. -/
def lbRfoldfree (l : Wlabel) : Prop :=
  match l with
  | .LLoad _ _ _ _ asrc => asrc = []
  | .LRmw _ _ _ _ _ asrc _ => asrc = []
  | _ => True

theorem lbDepfreeRfoldfree (l : Wlabel) : lbDepfree l → lbRfoldfree l := by
  cases l <;> simp only [lbDepfree, lbRfoldfree] <;>
    first | exact fun h => h | exact fun h => h.1 | exact fun _ => trivial

theorem lbRfoldfreeLdepfree (l : Wlabel) : lbRfoldfree l → lbLdepfree l := by
  cases l <;> simp only [lbRfoldfree, lbLdepfree] <;>
    first | exact fun h => h | exact fun _ => trivial

theorem lbFusedNobarex (l : Wlabel) : lbFused l → lbNobarex l := by
  cases l <;> simp [lbFused, lbNobarex]

/-! ## (0b) THE ADMINISTRATIVE ALPHABET

Exactly the labels `projLbl` sends to `none`; the Boolean index is `LInstr`'s
(`instrPost` clears `wRes`, so the intra-pair star runs at `instr := false`).
Deviation 4 (Stage C): the fetch sits where `LInstr` sits.  Deviation 7 (W13 (I),
[OWN.27]): the fabric marker `LDev` is NO LONGER administrative — it projects to the
I/O-class event `LIo` and is a REALIZING step of its own. -/

def lbAdmin (instr : Bool) (l : Wlabel) : Prop :=
  match l with
  | .LSilent | .LRegW .. | .LCtrl _ => True
  | .LInstr | .LIFetch .. => instr = true
  | _ => False

/-- The `LInstr`-free star is a sub-alphabet of the full one. -/
theorem lbAdminMono (instr : Bool) (l : Wlabel) : lbAdmin false l → lbAdmin instr l := by
  cases l <;> simp [lbAdmin]

/-- ... and the whole alphabet is invisible to the projection. -/
theorem lbAdminProj (k : WmClass) (instr : Bool) (l : Wlabel) :
    lbAdmin instr l → projLbl k l = none := by
  cases l <;> simp [lbAdmin, projLbl]

/-- (Lean helper, stdpp `list_insert_id`.) -/
theorem listSetLookupId {α : Type _} {l : List α} {i : Nat} {x : α} (h : l[i]? = some x) :
    l.set i x = l := by
  apply List.ext_getElem?
  intro j
  by_cases hij : i = j
  · subst hij; rw [list_lookup_insert (lookup_lt_Some h), h]
  · rw [list_lookup_insert_ne hij]

/-! ## (0c) THE FETCH PIN (deviation 4, Stage C)

The graph tier's fetch oracle: a fetch answers the boot image at timestamp 0.
It is a property of the PROGRAM's emitted label, carried by the pinned LTS. -/

/-- The graph tier's fetch oracle: image bytes, timestamp 0.  `True` off the fetch. -/
def WeakAxRealize.fetchPin (img : Image) (l : Wlabel) : Prop :=
  match l with
  | .LIFetch base tvs =>
      (∀ t ∈ tvs.map Prod.fst, t = 0) ∧
      ∀ j, j < tvs.length → img (base + (j : Int)) = (tvs.map Prod.snd)[j]?
  | _ => True

/-- A pinned fetch passes the pf machine's view-0 fetch check, at any log. -/
theorem fetchPinIfetchOk (img : Image) (log : List Wmsg) (base : Int)
    (tvs : List (Nat × BitVec 8)) :
    WeakAxRealize.fetchPin img (.LIFetch base tvs) → ifetchOk img log 0 base tvs := by
  rintro ⟨h0, himg⟩ j t v hj
  have hlt : j < tvs.length := lookup_lt_Some hj
  have ht : t = 0 := h0 t (List.mem_map.2 ⟨(t, v), List.mem_iff_getElem?.2 ⟨j, hj⟩, rfl⟩)
  subst ht
  refine (ifetchByteOk0 img log _ 0 v).2 ?_
  rw [logByte0, himg j hlt, List.getElem?_map, hj]
  rfl

/-- `unprojLbl` never yields a fetch. -/
theorem fetchPinUnproj (img : Image) (lb : Lbl) : WeakAxRealize.fetchPin img (unprojLbl lb) := by
  cases lb <;> trivial

/-- The program LTS with its fetches pinned (a sub-LTS of `pstep`). -/
def pstepPin {P D : Type} (img : Image) (pstep : P → D → Wlabel → P → D → Prop) :
    P → D → Wlabel → P → D → Prop :=
  fun p d l p' d' => pstep p d l p' d' ∧ WeakAxRealize.fetchPin img l

theorem pstepPinSub {P D : Type} (img : Image) (pstep : P → D → Wlabel → P → D → Prop)
    (p : P) (d : D) (l : Wlabel) (p' : P) (d' : D) :
    pstepPin img pstep p d l p' d' → pstep p d l p' d' :=
  fun h => h.1

/-- (Lean-only) Every step of the LTS is pinned to `img`. -/
def pstepPinned {P D : Type} (img : Image) (pstep : P → D → Wlabel → P → D → Prop) : Prop :=
  ∀ p d l p' d', pstep p d l p' d' → WeakAxRealize.fetchPin img l

theorem pstepPinPinned {P D : Type} (img : Image) (pstep : P → D → Wlabel → P → D → Prop) :
    pstepPinned img (pstepPin img pstep) :=
  fun _ _ _ _ _ h => h.2

/-- A pf step of the pinned LTS is one of the LTS. -/
theorem wpPfStepPinSub {P D : Type} (img : Image) (pstep : P → D → Wlabel → P → D → Prop)
    (pcls : P → Wlabel → Wstate → WmClass) (i : Nat) (l : Wlabel) (c c' : Wpcfg P D) :
    wpPfStep (pstepPin img pstep) pcls i l c c' → wpPfStep pstep pcls i l c c' := by
  intro h
  cases h with
  | PFSilent c ag st' d' hlk hps => exact .PFSilent c ag st' d' hlk hps.1
  | PFLoad c ag aq lat base tvs asrc st' d' hlk hps hr =>
    exact .PFLoad c ag aq lat base tvs asrc st' d' hlk hps.1 hr
  | PFStore c ag rl base data asrc vsrc k st' d' hlk hps hnn hk =>
    exact .PFStore c ag rl base data asrc vsrc k st' d' hlk hps.1 hnn hk
  | PFRmw c ag aq rl base tvs data asrc vsrc k st' d' hlk hps hnn hlen hr he hk =>
    exact .PFRmw c ag aq rl base tvs data asrc vsrc k st' d' hlk hps.1 hnn hlen hr he hk
  | PFFence c ag pr pw sr sw st' d' hlk hps => exact .PFFence c ag pr pw sr sw st' d' hlk hps.1
  | PFDev c ag st' d' hlk hps => exact .PFDev c ag st' d' hlk hps.1
  | PFRegW c ag rd srcs st' d' hlk hps => exact .PFRegW c ag rd srcs st' d' hlk hps.1
  | PFCtrl c ag srcs st' d' hlk hps => exact .PFCtrl c ag srcs st' d' hlk hps.1
  | PFInstr c ag st' d' hlk hps => exact .PFInstr c ag st' d' hlk hps.1
  | PFExLoad c ag aq base tvs asrc st' d' hlk hps hr =>
    exact .PFExLoad c ag aq base tvs asrc st' d' hlk hps.1 hr
  | PFExStore c ag rl base data asrc vsrc k R st' d' hlk hps hnn hres hrb hrlen he hk =>
    exact .PFExStore c ag rl base data asrc vsrc k R st' d' hlk hps.1 hnn hres hrb hrlen he hk
  | PFIFetch c ag base tvs st' d' hlk hps hif => exact .PFIFetch c ag base tvs st' d' hlk hps.1 hif

theorem wpPfRunPinSub {P D : Type} (img : Image) (pstep : P → D → Wlabel → P → D → Prop)
    (pcls : P → Wlabel → Wstate → WmClass) (c c' : Wpcfg P D) :
    rtc (wpPfRun (pstepPin img pstep) pcls) c c' → rtc (wpPfRun pstep pcls) c c' :=
  rtc_subrel (fun _ _ ⟨i, l, h⟩ => ⟨i, l, wpPfStepPinSub img pstep pcls i l _ _ h⟩)

section realize

variable {P D : Type}
variable (pstep : P → D → Wlabel → P → D → Prop)
variable (pcls : P → Wlabel → Wstate → WmClass)

/-! ## (1) The label-supply relation -/

/-- `l` REALIZES the axiomatic label `lb` for agent `i` at state `σ`, run at
the acting agent's program state `p`.  (`σ` is read only through `σ.msWs i`.) -/
def lblRealizes (p : P) (σ : Mstate) (i : Nat) (lb : Lbl) (l : Wlabel) : Prop :=
  lbNobarex l ∧ latFree l ∧ lbRfoldfree l ∧
  projLbl (pcls p l (σ.msWs i)) l = some lb

/-- Under the PRE-T1-D gates the relation is FUNCTIONAL, its value the
canonical `unprojLbl`, and its class side condition exactly `mstepClsOk`. -/
theorem lblRealizesUnproj (p : P) (σ : Mstate) (i : Nat) (lb : Lbl) (l : Wlabel) :
    lbDepfree l → lbFused l → lblRealizes pcls p σ i lb l →
    l = unprojLbl lb ∧ mstepClsOk pcls p σ i lb := by
  rintro hdf hfu ⟨_, hlat, _, hpr⟩
  cases l with
  | LLoad aq lat base tvs asrc =>
    simp only [latFree] at hlat
    simp only [lbDepfree] at hdf
    subst hlat hdf
    simp only [projLbl, Option.some.injEq] at hpr
    subst hpr
    exact ⟨by simp only [unprojLbl, zip_fst_snd], trivial⟩
  | LStore rl base data asrc vsrc =>
    simp only [lbDepfree] at hdf
    obtain ⟨rfl, rfl⟩ := hdf
    simp only [projLbl, Option.some.injEq] at hpr
    subst hpr
    exact ⟨rfl, rfl⟩
  | LRmw aq rl base tvs data asrc vsrc =>
    simp only [lbDepfree] at hdf
    obtain ⟨rfl, rfl⟩ := hdf
    simp only [projLbl, Option.some.injEq] at hpr
    subst hpr
    exact ⟨by simp only [unprojLbl, zip_fst_snd], by simp only [mstepClsOk, unprojLbl, zip_fst_snd]⟩
  | LFence pr pw sr sw =>
    simp only [projLbl, Option.some.injEq] at hpr
    subst hpr
    exact ⟨rfl, trivial⟩
  | LDev kd base vs =>
    -- W13 (I): the fabric marker realizes its own I/O-class event
    simp only [projLbl, Option.some.injEq] at hpr
    subst hpr
    exact ⟨rfl, trivial⟩
  | _ => simp [projLbl, lbFused] at hpr hfu

/-- The converse, at a label the axiomatic side actually stepped with. -/
theorem lblRealizesIntro (p : P) (σ σ' : Mstate) (i : Nat) (lb : Lbl) :
    mstep σ i lb σ' → mstepClsOk pcls p σ i lb → lblRealizes pcls p σ i lb (unprojLbl lb) := by
  intro hms hck
  cases hms with
  | MStepLoad aq base ts vs hrd =>
    have hl := hrd.1
    refine ⟨trivial, rfl, rfl, ?_⟩
    simp only [unprojLbl, projLbl]
    rw [List.map_fst_zip (by omega), List.map_snd_zip (by omega)]
  | MStepStore rl base vs kc _ =>
    refine ⟨trivial, trivial, trivial, ?_⟩
    simp only [mstepClsOk] at hck
    rw [hck]
    rfl
  | MStepFence pr pw sr sw => exact ⟨trivial, trivial, trivial, rfl⟩
  | MStepRmw aq rl base ts rvs wvs kc _ _ hrd _ =>
    have hl := hrd.1
    refine ⟨trivial, trivial, rfl, ?_⟩
    simp only [mstepClsOk] at hck
    simp only [unprojLbl, projLbl]
    rw [List.map_fst_zip (by omega), List.map_snd_zip (by omega), hck]
    rfl
  | MStepIo kd base vs => exact ⟨trivial, trivial, trivial, rfl⟩

/-! ## (1b) THE PAIR (A3(iv)): one axiomatic rmw, two machine steps

The class is read at the CONDITIONAL WRITE's own program state `pm` and at
the AXIOMATIC read post-state `loadPostRun (σ.msWs i) …`. -/

def lblRealizesPair (_p pm : P) (σ : Mstate) (i : Nat) (lb : Lbl) (l1 l2 : Wlabel) : Prop :=
  ∃ (aq rl : Bool) (base : Int) (tvs : List (Nat × BitVec 8)) (data : List (BitVec 8))
    (asrc1 asrc2 vsrc2 : List Dsrc),
    l1 = .LExLoad aq base tvs asrc1 ∧
    l2 = .LExStore rl base data asrc2 vsrc2 ∧
    data ≠ [] ∧ tvs.length = data.length ∧
    lb = .LRmw aq rl base (tvs.map Prod.fst) (tvs.map Prod.snd) data
           (pcls pm l2 (loadPostRun (σ.msWs i) aq base (tvs.map Prod.fst)))

/-- The pair's composition, as a state equation: `wsResSet` is invisible to a
store run that writes at least one byte. -/
theorem storePostRunDResPair (ws : Wstate) (r : Option Wresv) (rl : Bool) (vaddr vdata : Nat)
    (base : Int) (n t : Nat) :
    0 < n →
    storePostRunD (wsResSet ws r) rl vaddr vdata base n t
    = storePostRunD ws rl vaddr vdata base n t := by
  intro hn
  cases n with
  | zero => omega
  | succ m => rfl

/-- `exclOk` on the reservation's timestamp column — the shape `PFExStore`
asks for. -/
theorem rmwLatestExclOkTs (img : Image) (log : List Wmsg) (i : Nat) (base : Int)
    (ts : List Nat) :
    rmwLatest img log base ts → exclOkTs log i base ts (log.length + 1) := by
  intro hlat j t ht hw
  obtain ⟨_, hnw⟩ := hlat j t ht
  apply hnw
  exact writesInMono log _ t (log.length + 1 - 1) t log.length (Nat.le_refl _) (by omega)
    (writesInByWritesIn _ _ _ _ _ hw)

/-! ## (2) The administrative star, on the PROGRAM side -/

def admStep (instr : Bool) (x y : P × D) : Prop :=
  ∃ l, lbAdmin instr l ∧ pstep x.1 x.2 l y.1 y.2

/-- A finite run of administrative program steps, fabric threaded. -/
def admStar (instr : Bool) (p : P) (d : D) (p' : P) (d' : D) : Prop :=
  rtc (admStep pstep instr) (p, d) (p', d')

theorem admStarRefl (instr : Bool) (p : P) (d : D) : admStar pstep instr p d p d := rtc_refl _

theorem admStarL (instr : Bool) (p : P) (d : D) (l : Wlabel) (p1 : P) (d1 : D) (p' : P) (d' : D) :
    lbAdmin instr l → pstep p d l p1 d1 → admStar pstep instr p1 d1 p' d' →
    admStar pstep instr p d p' d' :=
  fun ha hs hr => rtc_l ⟨l, ha, hs⟩ hr

theorem admStepMono (instr : Bool) (x y : P × D) :
    admStep pstep false x y → admStep pstep instr x y := by
  rintro ⟨l, ha, hs⟩
  exact ⟨l, lbAdminMono instr l ha, hs⟩

theorem admStarMonoRtc (instr : Bool) (x y : P × D) :
    rtc (admStep pstep false) x y → rtc (admStep pstep instr) x y :=
  rtc_subrel (fun x y => admStepMono pstep instr x y)

theorem admStarMono (instr : Bool) (p : P) (d : D) (p' : P) (d' : D) :
    admStar pstep false p d p' d' → admStar pstep instr p d p' d' :=
  admStarMonoRtc pstep instr _ _

/-! ## (3) The program-carrying hypothesis

A per-event assignment of program states (`pst k`) and of the FABRIC (`dv k`),
with the `pstep`s carrying position `k` to `k + 1`: an administrative star and
then the realizing step, or, for the exclusive PAIR, an administrative star,
the exclusive read, an `LInstr`-free administrative star and the conditional
write. -/
def execProgOk' (pst : Nat → List P) (dv : Nat → D) (E : Exec) : Prop :=
  ∀ (k : Nat) (s : Estep), E.exTr[k]? = some s →
    ∃ (p pa : P) (da : D) (p' : P),
      (pst k)[s.esAg]? = some p ∧
      pst (k + 1) = (pst k).set s.esAg p' ∧
      admStar pstep true p (dv k) pa da ∧
      ((∃ l, lblRealizes pcls pa (stt E k) s.esAg s.esLb l ∧ pstep pa da l p' (dv (k + 1)))
       ∨ (∃ (pm : P) (dm : D) (pm2 : P) (dm2 : D) (l1 l2 : Wlabel),
            lblRealizesPair pcls pa pm2 (stt E k) s.esAg s.esLb l1 l2 ∧
            pstep pa da l1 pm dm ∧
            admStar pstep false pm dm pm2 dm2 ∧
            pstep pm2 dm2 l2 p' (dv (k + 1))))

/-- THE EMPTY-STAR SPECIALIZATION — the pre-T1-D shape (what a `progFree`
instance supplies). -/
def execProgOk (pst : Nat → List P) (dv : Nat → D) (E : Exec) : Prop :=
  ∀ (k : Nat) (s : Estep), E.exTr[k]? = some s →
    ∃ (p p' : P),
      (pst k)[s.esAg]? = some p ∧
      pst (k + 1) = (pst k).set s.esAg p' ∧
      ((∃ l, lblRealizes pcls p (stt E k) s.esAg s.esLb l ∧ pstep p (dv k) l p' (dv (k + 1)))
       ∨ (∃ (pm : P) (dm : D) (l1 l2 : Wlabel),
            lblRealizesPair pcls p pm (stt E k) s.esAg s.esLb l1 l2 ∧
            pstep p (dv k) l1 pm dm ∧ pstep pm dm l2 p' (dv (k + 1))))

theorem execProgOkStar (pst : Nat → List P) (dv : Nat → D) (E : Exec) :
    execProgOk pstep pcls pst dv E → execProgOk' pstep pcls pst dv E := by
  intro h k s hs
  obtain ⟨p, p', hp, hn, hsup⟩ := h k s hs
  refine ⟨p, p, dv k, p', hp, hn, admStarRefl pstep true p (dv k), ?_⟩
  rcases hsup with ⟨l, hre, hps⟩ | ⟨pm, dm, l1, l2, hre, hps1, hps2⟩
  · exact .inl ⟨l, hre, hps⟩
  · exact .inr ⟨pm, dm, pm, dm, l1, l2, hre, hps1, admStarRefl pstep false pm dm, hps2⟩

/-- The old one-step form is the left disjunct of the empty-star shape. -/
theorem execProgOkSingle (pst : Nat → List P) (dv : Nat → D) (E : Exec) :
    (∀ (k : Nat) (s : Estep), E.exTr[k]? = some s →
       ∃ (p p' : P) (l : Wlabel),
         (pst k)[s.esAg]? = some p ∧
         lblRealizes pcls p (stt E k) s.esAg s.esLb l ∧
         pstep p (dv k) l p' (dv (k + 1)) ∧
         pst (k + 1) = (pst k).set s.esAg p') →
    execProgOk pstep pcls pst dv E := by
  intro h k s hs
  obtain ⟨p, p', l, hp, hre, hps, hn⟩ := h k s hs
  exact ⟨p, p', hp, hn, .inl ⟨l, hre, hps⟩⟩

/-! ## (4) The administrative star, on the MACHINE side

The configuration moves within `cfgEqr`, and (off `LInstr`) the acting agent's
reservation survives. -/

theorem admStepPf (instr : Bool) (c : Wpcfg P D) (i : Nat) (ag : Wpagent P) (l : Wlabel) (p' : P)
    (d' : D) :
    lbAdmin instr l →
    WeakAxRealize.fetchPin c.pcImg l →
    c.pcAgs[i]? = some ag →
    pstep ag.paSt c.pcDev l p' d' →
    ∃ (c' : Wpcfg P D) (ag' : Wpagent P),
      wpPfStep pstep pcls i l c c' ∧ cfgEqr c c' ∧ c'.pcDev = d' ∧
      c'.pcAgs[i]? = some ag' ∧ ag'.paSt = p' ∧
      wsEqr ag.paWs ag'.paWs ∧
      (instr = false → ag'.paWs.wRes = ag.paWs.wRes) ∧
      c'.pcAgs.map Wpagent.paSt = (c.pcAgs.map Wpagent.paSt).set i p' := by
  intro hadm hpin hlk hps
  have hlt := lookup_lt_Some hlk
  -- the three configuration facts are the same in every arm
  have hpkg : ∀ (w : Wstate) (d0 : D), wsEqr ag.paWs w →
      cfgEqr c (⟨c.pcImg, c.pcLog, d0, c.pcAgs.set i ⟨p', w, ag.paProm⟩⟩ : Wpcfg P D) ∧
      (c.pcAgs.set i ⟨p', w, ag.paProm⟩)[i]? = some ⟨p', w, ag.paProm⟩ ∧
      (c.pcAgs.set i ⟨p', w, ag.paProm⟩).map Wpagent.paSt
        = (c.pcAgs.map Wpagent.paSt).set i p' := by
    intro w d0 he
    refine ⟨⟨rfl, rfl, fun j agj' hj => ?_⟩, list_lookup_insert hlt, list_fmap_insert⟩
    rcases lookupSetCases hj with ⟨rfl, rfl⟩ | ⟨_, hj⟩
    · exact ⟨ag, hlk, he⟩
    · exact ⟨agj', hj, wsEqrRefl _⟩
  cases l with
  | LSilent =>
    obtain ⟨h1, h2, h3⟩ := hpkg ag.paWs d' (wsEqrRefl _)
    exact ⟨_, _, wpPfStep.PFSilent c ag p' d' hlk hps, h1, rfl, h2, rfl, wsEqrRefl _,
      fun _ => rfl, h3⟩
  | LRegW rd srcs =>
    obtain ⟨h1, h2, h3⟩ :=
      hpkg (regwPost ag.paWs rd (srcsView ag.paWs srcs)) d' (wsEqrRegwPost _ _ _)
    exact ⟨_, _, wpPfStep.PFRegW c ag rd srcs p' d' hlk hps, h1, rfl, h2, rfl,
      wsEqrRegwPost _ _ _, fun _ => rfl, h3⟩
  | LCtrl srcs =>
    obtain ⟨h1, h2, h3⟩ :=
      hpkg (ctrlPost ag.paWs (srcsView ag.paWs srcs)) d' (wsEqrCtrlPost _ _)
    exact ⟨_, _, wpPfStep.PFCtrl c ag srcs p' d' hlk hps, h1, rfl, h2, rfl,
      wsEqrCtrlPost _ _, fun _ => rfl, h3⟩
  | LInstr =>
    -- only in the `instr = true` star, so the reservation obligation is vacuous
    obtain ⟨h1, h2, h3⟩ := hpkg (instrPost ag.paWs) d' (wsEqrInstrPost _)
    refine ⟨_, _, wpPfStep.PFInstr c ag p' d' hlk hps, h1, rfl, h2, rfl,
      wsEqrInstrPost _, fun hf => ?_, h3⟩
    simp only [lbAdmin] at hadm
    rw [hf] at hadm
    cases hadm
  | LIFetch base tvs =>
    -- (deviation 4) the PINNED fetch: state unchanged, the view-0 check from the pin
    obtain ⟨h1, h2, h3⟩ := hpkg ag.paWs d' (wsEqrRefl _)
    exact ⟨_, _, wpPfStep.PFIFetch c ag base tvs p' d' hlk hps
      (fetchPinIfetchOk _ _ _ _ hpin), h1, rfl, h2, rfl, wsEqrRefl _, fun _ => rfl, h3⟩
  | _ => simp only [lbAdmin] at hadm

theorem admStarPfRun (instr : Bool) (x y : P × D) :
    rtc (admStep pstep instr) x y →
    ∀ (c : Wpcfg P D) (i : Nat) (ag : Wpagent P),
      pstepPinned c.pcImg pstep →
      c.pcAgs[i]? = some ag → ag.paSt = x.1 → c.pcDev = x.2 →
      ∃ (c' : Wpcfg P D) (ag' : Wpagent P),
        rtc (wpPfRun pstep pcls) c c' ∧ cfgEqr c c' ∧ c'.pcDev = y.2 ∧
        c'.pcAgs[i]? = some ag' ∧ ag'.paSt = y.1 ∧
        wsEqr ag.paWs ag'.paWs ∧
        (instr = false → ag'.paWs.wRes = ag.paWs.wRes) ∧
        c'.pcAgs.map Wpagent.paSt = (c.pcAgs.map Wpagent.paSt).set i y.1 := by
  intro h
  induction h with
  | refl =>
    intro c i ag _ hlk hst hdev
    refine ⟨c, ag, rtc_refl _, cfgEqrRefl c, hdev, hlk, hst, wsEqrRefl _, fun _ => rfl, ?_⟩
    exact (listSetLookupId (by simp [List.getElem?_map, hlk, hst])).symm
  | tail _ hyz ih =>
    intro c i ag hpin hlk hst hdev
    obtain ⟨c1, ag1, hrun, he1, hd1, hl1, hs1, hw1, hr1, hf1⟩ := ih c i ag hpin hlk hst hdev
    obtain ⟨l, hadm, hps⟩ := hyz
    obtain ⟨c2, ag2, hstep, he2, hd2, hl2, hs2, hw2, hr2, hf2⟩ :=
      admStepPf pstep pcls instr c1 i ag1 l _ _ hadm (by rw [he1.1]; exact hpin _ _ _ _ _ hps) hl1
        (by rw [hs1, hd1]; exact hps)
    refine ⟨c2, ag2, rtc_r hrun ⟨i, l, hstep⟩, cfgEqrTrans _ _ _ he1 he2, hd2, hl2, hs2,
      wsEqrTrans hw1 hw2, fun hi => (hr2 hi).trans (hr1 hi), ?_⟩
    rw [hf2, hf1, list_insert_insert]

theorem admStarPf (instr : Bool) (c : Wpcfg P D) (i : Nat) (ag : Wpagent P) (p' : P) (d' : D) :
    pstepPinned c.pcImg pstep →
    c.pcAgs[i]? = some ag →
    admStar pstep instr ag.paSt c.pcDev p' d' →
    ∃ (c' : Wpcfg P D) (ag' : Wpagent P),
      rtc (wpPfRun pstep pcls) c c' ∧ cfgEqr c c' ∧ c'.pcDev = d' ∧
      c'.pcAgs[i]? = some ag' ∧ ag'.paSt = p' ∧
      wsEqr ag.paWs ag'.paWs ∧
      (instr = false → ag'.paWs.wRes = ag.paWs.wRes) ∧
      c'.pcAgs.map Wpagent.paSt = (c.pcAgs.map Wpagent.paSt).set i p' :=
  fun hpin hlk hst =>
    admStarPfRun pstep pcls instr (ag.paSt, c.pcDev) (p', d') hst c i ag hpin hlk rfl rfl

/-! ## (5) One realizing step

`mstepWpPfStep` with the `progFree` supply replaced by the given `pstep`, the
"program states are untouched" conclusion replaced by the insert, and the
state relation weakened to `cfgMatchd`; the case analysis is on the MACHINE
label. -/
theorem mstepWpPfStepProg (σ σ' : Mstate) (i : Nat) (lb : Lbl) (c : Wpcfg P D) (ag : Wpagent P)
    (p p' : P) (l : Wlabel) (dn : D) :
    pclsEqr pcls →
    cfgMatchd c σ → c.pcAgs[i]? = some ag → ag.paSt = p →
    lblRealizes pcls p σ i lb l →
    pstep p c.pcDev l p' dn →
    mstep σ i lb σ' →
    ∃ c', wpPfStep pstep pcls i l c c' ∧ cfgMatchd c' σ' ∧
      c'.pcAgs.map Wpagent.paSt = (c.pcAgs.map Wpagent.paSt).set i p' ∧
      c'.pcDev = dn := by
  rintro hce hm hlk hag ⟨hnb, hlat, hrf, hpr⟩ hps hms
  subst hag
  have hew := cfgMatchdWs c σ i ag hm hlk
  obtain ⟨img, lg, f⟩ := σ
  obtain ⟨himg, hlg, hf⟩ := hm
  dsimp only at himg hlg hf hew
  subst himg hlg
  -- the `cfgMatchd` obligation is the same three lines in every arm
  have hmatch : ∀ (st' : P) (w : Wstate) (pr : GSet Nat) (lg' : List Wmsg) (d' : D)
      (g : Nat → Wstate),
      wsEqr (g i) w → (∀ j, j ≠ i → g j = f j) →
      cfgMatchd (⟨c.pcImg, lg', d', c.pcAgs.set i ⟨st', w, pr⟩⟩ : Wpcfg P D) ⟨c.pcImg, lg', g⟩ :=
    fun st' w pr lg' d' g hgi hgne => cfgMatchdUpdGen _ _ _ _ i ag st' w pr f g hf hlk hgi hgne
  -- the program projection moves by exactly the insert
  have hst : ∀ (st' : P) (w : Wstate) (pr : GSet Nat),
      (c.pcAgs.set i ⟨st', w, pr⟩).map Wpagent.paSt = (c.pcAgs.map Wpagent.paSt).set i st' :=
    fun _ _ _ => list_fmap_insert
  have hro : ∀ (aq : Bool) (base : Int) (tvs : List (Nat × BitVec 8)),
      rdOk c.pcImg c.pcLog (f i) aq base (tvs.map Prod.fst) (tvs.map Prod.snd) →
      readOk c.pcImg c.pcLog ag.paWs aq false base tvs := by
    intro aq base tvs hrd
    have h := wsEqrReadOk _ _ _ _ _ _ _ _ hew (rdOkReadOk _ _ _ _ _ _ _ hrd)
    rwa [zip_fst_snd] at h
  cases l with
  | LLoad aq lat base tvs asrc =>
    -- PLAIN LOAD: `lbRfoldfree` pins `asrc = []`
    simp only [latFree] at hlat
    simp only [lbRfoldfree] at hrf
    subst hlat hrf
    simp only [projLbl, Option.some.injEq] at hpr
    subst hpr
    cases hms with
    | MStepLoad _ _ _ _ hrd =>
      refine ⟨_, wpPfStep.PFLoad c ag aq false base tvs [] p' dn hlk hps ?_, ?_, hst _ _ _, rfl⟩
      · rw [srcsViewNil, readOkD0]
        exact hro aq base tvs hrd
      · dsimp only
        rw [srcsViewNil, loadPostRunD0]
        exact hmatch _ _ _ _ _ _ (by rw [updWsEq]; exact wsEqrLoadPostRun _ _ _ _ _ hew)
          (fun j hne => updWsNe _ _ _ _ hne)
  | LStore rl base data asrc vsrc =>
    -- STORE at a REAL operand list; the class equation is `pclsEqr`
    simp only [projLbl, Option.some.injEq] at hpr
    subst hpr
    cases hms with
    | MStepStore _ _ _ _ hnn =>
      have hk : pcls ag.paSt (.LStore rl base data asrc vsrc) (f i)
          = pcls ag.paSt (.LStore rl base data asrc vsrc) ag.paWs := hce _ _ _ _ hew
      refine ⟨_, wpPfStep.PFStore c ag rl base data asrc vsrc
        (pcls ag.paSt (.LStore rl base data asrc vsrc) ag.paWs) p' dn hlk hps hnn rfl, ?_,
        hst _ _ _, rfl⟩
      dsimp only
      rw [hk]
      exact hmatch _ _ _ _ _ _
        (by rw [updWsEq]; exact wsEqrStorePostRunD _ _ _ _ _ _ _ _ hew)
        (fun j hne => updWsNe _ _ _ _ hne)
  | LRmw aq rl base tvs data asrc vsrc =>
    -- THE FUSED RMW: `lbRfoldfree` pins `asrc = []`
    simp only [lbRfoldfree] at hrf
    subst hrf
    simp only [projLbl, Option.some.injEq] at hpr
    subst hpr
    cases hms with
    | MStepRmw _ _ _ _ _ _ _ hnn hlen hrd hlt =>
      have hk : pcls ag.paSt (.LRmw aq rl base tvs data [] vsrc) (f i)
          = pcls ag.paSt (.LRmw aq rl base tvs data [] vsrc) ag.paWs := hce _ _ _ _ hew
      refine ⟨_, wpPfStep.PFRmw c ag aq rl base tvs data [] vsrc
        (pcls ag.paSt (.LRmw aq rl base tvs data [] vsrc) ag.paWs) p' dn hlk hps hnn ?_
        (hro aq base tvs hrd) ?_ rfl, ?_, hst _ _ _, rfl⟩
      · rw [List.length_map] at hlen; omega
      · have h := rmwLatestExclOk c.pcImg c.pcLog i base (tvs.map Prod.fst) (tvs.map Prod.snd) hlt
        rwa [zip_fst_snd] at h
      · dsimp only
        rw [hk, srcsViewNil, loadPostRunD0]
        exact hmatch _ _ _ _ _ _
          (by
            rw [updWsEq]
            exact wsEqrStorePostRunD _ _ _ _ _ _ _ _ (wsEqrLoadPostRun _ _ _ _ _ hew))
          (fun j hne => updWsNe _ _ _ _ hne)
  | LFence pr pw sr sw =>
    simp only [projLbl, Option.some.injEq] at hpr
    subst hpr
    cases hms with
    | MStepFence _ _ _ _ =>
      refine ⟨_, wpPfStep.PFFence c ag pr pw sr sw p' dn hlk hps, ?_, hst _ _ _, rfl⟩
      exact hmatch _ _ _ _ _ _ (by rw [updWsEq]; exact wsEqrFencePost _ _ _ _ _ _ hew)
        (fun j hne => updWsNe _ _ _ _ hne)
  | LExLoad aq base tvs asrc =>
    -- THE DANGLING EXCLUSIVE READ, realizing a PLAIN axiomatic load
    simp only [projLbl, Option.some.injEq] at hpr
    subst hpr
    cases hms with
    | MStepLoad _ _ _ _ hrd =>
      refine ⟨_, wpPfStep.PFExLoad c ag aq base tvs asrc p' dn hlk hps (hro aq base tvs hrd), ?_,
        hst _ _ _, rfl⟩
      exact hmatch _ _ _ _ _ _ (by rw [updWsEq]; exact wsEqrExloadPostRunD _ _ _ _ _ _ hew)
        (fun j hne => updWsNe _ _ _ _ hne)
  | LDev kd base vs =>
    -- W13 (I): THE I/O-CLASS EVENT — the fabric marker realizes `LIo`, replayed inertly
    simp only [projLbl, Option.some.injEq] at hpr
    subst hpr
    cases hms with
    | MStepIo _ _ _ =>
      refine ⟨_, wpPfStep.PFDev c ag p' dn hlk hps, ?_, hst _ _ _, rfl⟩
      exact hmatch _ _ _ _ _ _ hew (fun _ _ => rfl)
  | _ => simp [lbNobarex, projLbl] at hnb hpr

/-! ## (5b) The PAIR step (A3(iv))

The reservation is created by the first step, SURVIVES the `LInstr`-free star
and is consumed by the last step; `cfgMatchd` is restored only at the END. -/
theorem mstepWpPfStepPair (σ σ' : Mstate) (i : Nat) (lb : Lbl) (c : Wpcfg P D) (ag : Wpagent P)
    (p pm pm2 p' : P) (l1 l2 : Wlabel) (dm dm2 dn : D) :
    pclsEqr pcls → pstepPinned c.pcImg pstep →
    cfgMatchd c σ → c.pcAgs[i]? = some ag → ag.paSt = p →
    lblRealizesPair pcls p pm2 σ i lb l1 l2 →
    pstep p c.pcDev l1 pm dm →
    admStar pstep false pm dm pm2 dm2 →
    pstep pm2 dm2 l2 p' dn →
    mstep σ i lb σ' →
    ∃ c', rtc (wpPfRun pstep pcls) c c' ∧ cfgMatchd c' σ' ∧
      c'.pcAgs.map Wpagent.paSt = (c.pcAgs.map Wpagent.paSt).set i p' ∧
      c'.pcDev = dn := by
  intro hce hpin hm hlk hag hre hps1 hstar hps2 hms
  subst hag
  have hew := cfgMatchdWs c σ i ag hm hlk
  have hlti := lookup_lt_Some hlk
  obtain ⟨aq, rl, base, tvs, data, asrc1, asrc2, vsrc2, rfl, rfl, hnn, hlen, hlb⟩ := hre
  obtain ⟨img, lg, f⟩ := σ
  obtain ⟨himg, hlg, hf⟩ := hm
  dsimp only at himg hlg hf hew hlb
  subst himg hlg hlb
  cases hms with
  | MStepRmw _ _ _ _ _ _ _ _ _ hrd hlt =>
    -- the configuration after the exclusive read
    have hro : readOk c.pcImg c.pcLog ag.paWs aq false base tvs := by
      have h := wsEqrReadOk _ _ _ _ _ _ _ _ hew (rdOkReadOk _ _ _ _ _ _ _ hrd)
      rwa [zip_fst_snd] at h
    have hstep1 : wpPfStep pstep pcls i (.LExLoad aq base tvs asrc1) c
        ⟨c.pcImg, c.pcLog, dm, c.pcAgs.set i
          ⟨pm, exloadPostRunD ag.paWs aq (srcsView ag.paWs asrc1) base (tvs.map Prod.fst),
           ag.paProm⟩⟩ :=
      wpPfStep.PFExLoad c ag aq base tvs asrc1 pm dm hlk hps1 hro
    have hlk1 : (c.pcAgs.set i
          ⟨pm, exloadPostRunD ag.paWs aq (srcsView ag.paWs asrc1) base (tvs.map Prod.fst),
           ag.paProm⟩)[i]?
        = some ⟨pm, exloadPostRunD ag.paWs aq (srcsView ag.paWs asrc1) base (tvs.map Prod.fst),
            ag.paProm⟩ :=
      list_lookup_insert hlti
    -- the intra-pair administrative star (NOTE: no `cfgEqr c c1` — the exclusive
    -- read is a MEMORY step)
    obtain ⟨c2, ag2, hrun2, heq2, hd2, hlk2, hs2, hw2, hr2, hfm2⟩ :=
      admStarPf pstep pcls false
        ⟨c.pcImg, c.pcLog, dm, c.pcAgs.set i
          ⟨pm, exloadPostRunD ag.paWs aq (srcsView ag.paWs asrc1) base (tvs.map Prod.fst),
           ag.paProm⟩⟩ i
        ⟨pm, exloadPostRunD ag.paWs aq (srcsView ag.paWs asrc1) base (tvs.map Prod.fst),
         ag.paProm⟩ pm2 dm2 hpin hlk1 hstar
    have hres2 : ag2.paWs.wRes
        = some ⟨base, tvs.map Prod.fst, ldvOf ag.paWs aq 0 base (tvs.map Prod.fst)⟩ :=
      (hr2 rfl).trans (exloadPostRunDRes _ _ _ _ _)
    have himg2 : c2.pcImg = c.pcImg := heq2.1
    have hlog2 : c2.pcLog = c.pcLog := heq2.2.1
    have hoth : ∀ j agj, j ≠ i → c2.pcAgs[j]? = some agj → wsEqr (f j) agj.paWs := by
      intro j agj hne hj
      obtain ⟨agj1, hj1, he1⟩ := heq2.2.2 j agj hj
      rcases lookupSetCases hj1 with ⟨hji, _⟩ | ⟨_, hj1'⟩
      · exact absurd hji hne
      · exact wsEqrTrans (hf j agj1 hj1') he1
    -- the wstate the class is read at
    have hwm : wsEqr (loadPostRun (f i) aq base (tvs.map Prod.fst)) ag2.paWs :=
      wsEqrTrans (wsEqrExloadPostRunD _ _ _ _ _ _ hew) hw2
    have hk : pcls pm2 (.LExStore rl base data asrc2 vsrc2)
          (loadPostRun (f i) aq base (tvs.map Prod.fst))
        = pcls ag2.paSt (.LExStore rl base data asrc2 vsrc2) ag2.paWs := by
      rw [hs2]; exact hce _ _ _ _ hwm
    -- the conditional write
    have hstep2 : wpPfStep pstep pcls i (.LExStore rl base data asrc2 vsrc2) c2
        ⟨c2.pcImg, c2.pcLog ++
            [⟨base, data, some i, pcls ag2.paSt (.LExStore rl base data asrc2 vsrc2) ag2.paWs⟩],
          dn, c2.pcAgs.set i
          ⟨p', storePostRunD ag2.paWs rl (srcsView ag2.paWs asrc2) (srcsView ag2.paWs vsrc2)
                base data.length (c2.pcLog.length + 1), ag2.paProm⟩⟩ :=
      wpPfStep.PFExStore c2 ag2 rl base data asrc2 vsrc2 _
        ⟨base, tvs.map Prod.fst, ldvOf ag.paWs aq 0 base (tvs.map Prod.fst)⟩ p' dn hlk2
        (by rw [hs2, hd2]; exact hps2) hnn hres2 rfl
        (by show (tvs.map Prod.fst).length = data.length; rw [List.length_map]; exact hlen)
        (by rw [hlog2]; exact rmwLatestExclOkTs c.pcImg c.pcLog i base _ hlt) rfl
    refine ⟨_, rtc_r (rtc_l ⟨i, _, hstep1⟩ hrun2) ⟨i, _, hstep2⟩, ?_, ?_, rfl⟩
    · dsimp only
      rw [hlog2, himg2, hk]
      refine cfgMatchdUpdGen _ _ _ _ i ag2 p' _ _ (updWs f i ag2.paWs) _ ?_ hlk2 ?_ ?_
      · intro j agj hj
        by_cases hji : j = i
        · subst hji
          rw [hlk2] at hj
          cases hj
          rw [updWsEq]
          exact wsEqrRefl _
        · rw [updWsNe _ _ _ _ hji]
          exact hoth j agj hji hj
      · rw [updWsEq]
        exact wsEqrStorePostRunD _ _ _ _ _ _ _ _ hwm
      · intro j hne
        rw [updWsNe _ _ _ _ hne, updWsNe _ _ _ _ hne]
    · dsimp only
      rw [list_fmap_insert, hfm2, list_insert_insert]
      dsimp only
      rw [list_fmap_insert, list_insert_insert]

/-! ## (6) The replay -/

theorem execPrefixPfRunProg (pst : Nat → List P) (dv : Nat → D) (E : Exec) (n : Nat) :
    pclsEqr pcls → pstepPinned (exImg E) pstep →
    execWf E → execProgOk' pstep pcls pst dv E →
    n ≤ E.exTr.length →
    ∃ c, rtc (wpPfRun pstep pcls) (wpInit (exImg E) (dv 0) (pst 0)) c ∧
      c.pcAgs.map Wpagent.paSt = pst n ∧ c.pcDev = dv n ∧
      cfgMatchd c (stt E n) := by
  intro hce hpin hE hpr
  induction n with
  | zero =>
    intro _
    refine ⟨wpInit (exImg E) (dv 0) (pst 0), rtc_refl _,
      by simp [wpInit, List.map_map, Function.comp_def], rfl, rfl, execLogInit E hE, ?_⟩
    intro i ag hlk
    simp only [wpInit, List.getElem?_map] at hlk
    cases hp : (pst 0)[i]? with
    | none => rw [hp] at hlk; cases hlk
    | some p =>
      rw [hp] at hlk; injection hlk with hlk; subst hlk
      show wsEqr (ews E 0 i) wsInit
      rw [execWsInit E i hE]
      exact wsEqrRefl _
  | succ n ih =>
    intro hn
    obtain ⟨c, hrun, hst, hdev, hm⟩ := ih (by omega)
    obtain ⟨s, hs⟩ := someOfIsSome (execTrLookup E n (by omega))
    have hms := execStepAt E n s hE hs
    obtain ⟨p, pa, da, p', hp, hnext, hstar, hsup⟩ := hpr n s hs
    have hex : ∃ ag, c.pcAgs[s.esAg]? = some ag ∧ ag.paSt = p := by
      rw [← hst, List.getElem?_map] at hp
      cases hag : c.pcAgs[s.esAg]? with
      | none => rw [hag] at hp; cases hp
      | some ag => rw [hag] at hp; injection hp with hp; exact ⟨ag, rfl, hp⟩
    obtain ⟨ag, hag, hagp⟩ := hex
    have hpc : pstepPinned c.pcImg pstep := by
      have himg : c.pcImg = exImg E := by
        rw [← hm.1]; exact execImgConst E n hE (by omega)
      rw [himg]; exact hpin
    -- the leading administrative star
    obtain ⟨c0, ag0, hrun0, heq0, hd0, hlk0, hs0, _, _, hfm0⟩ :=
      admStarPf pstep pcls true c s.esAg ag pa da hpc hag (by rw [hagp, hdev]; exact hstar)
    have hm0 : cfgMatchd c0 (stt E n) := cfgEqrMatchd _ _ _ heq0 hm
    rcases hsup with ⟨l, hre, hps⟩ | ⟨pm, dm, pm2, dm2, l1, l2, hre, hps1, hstar2, hps2⟩
    · obtain ⟨c2, hstep, hm2, hst2, hdev2⟩ :=
        mstepWpPfStepProg pstep pcls (stt E n) (stt E (n + 1)) s.esAg s.esLb c0 ag0 pa p' l
          (dv (n + 1)) hce hm0 hlk0 hs0 hre (by rw [hd0]; exact hps) hms
      refine ⟨c2, rtc_r (rtc_transitive hrun hrun0) ⟨s.esAg, l, hstep⟩, ?_, hdev2, hm2⟩
      rw [hst2, hfm0, hst, list_insert_insert, ← hnext]
    · obtain ⟨c2, hstep, hm2, hst2, hdev2⟩ :=
        mstepWpPfStepPair pstep pcls (stt E n) (stt E (n + 1)) s.esAg s.esLb c0 ag0 pa pm pm2 p'
          l1 l2 dm dm2 (dv (n + 1)) hce (by rw [heq0.1]; exact hpc) hm0 hlk0 hs0 hre (by rw [hd0]; exact hps1) hstar2 hps2 hms
      refine ⟨c2, rtc_transitive (rtc_transitive hrun hrun0) hstep, ?_, hdev2, hm2⟩
      rw [hst2, hfm0, hst, list_insert_insert, ← hnext]

/-- THE PROGRAM-CARRYING REVERSE BRIDGE.  Every `execWf` execution whose trace
is carried by a run of the given program LTS is the projection of a
promise-free run of the full machine, with the SAME LOG. -/
theorem execWfPfRunProg (pst : Nat → List P) (dv : Nat → D) (E : Exec) :
    pclsEqr pcls → pstepPinned (exImg E) pstep →
    execWf E → execProgOk' pstep pcls pst dv E →
    ∃ c, rtc (wpPfRun pstep pcls) (wpInit (exImg E) (dv 0) (pst 0)) c ∧
      c.pcAgs.map Wpagent.paSt = pst E.exTr.length ∧
      c.pcDev = dv E.exTr.length ∧
      cfgMatchd c (stt E E.exTr.length) := by
  intro hce hpin hE hpr
  exact execPrefixPfRunProg pstep pcls pst dv E E.exTr.length hce hpin hE hpr (Nat.le_refl _)

/-- (Lean-only, deviation 4) THE REPLAY OF A PINNED SUPPLY, projected to the
unpinned LTS: the form the graph-tier consumers use. -/
theorem execWfPfRunPin (img : Image) (pst : Nat → List P) (dv : Nat → D) (E : Exec) :
    pclsEqr pcls → exImg E = img →
    execWf E → execProgOk' (pstepPin img pstep) pcls pst dv E →
    ∃ c, rtc (wpPfRun pstep pcls) (wpInit (exImg E) (dv 0) (pst 0)) c ∧
      c.pcAgs.map Wpagent.paSt = pst E.exTr.length ∧
      c.pcDev = dv E.exTr.length ∧
      cfgMatchd c (stt E E.exTr.length) := by
  intro hce himg hE hpr
  subst himg
  obtain ⟨c, h1, h2, h3, h4⟩ :=
    execWfPfRunProg (pstepPin (exImg E) pstep) pcls pst dv E hce (pstepPinPinned _ _) hE hpr
  exact ⟨c, wpPfRunPinSub _ pstep pcls _ _ h1, h2, h3, h4⟩

/-! ## (7) The `progFree` forms are corollaries

THE `cfgMatchd` SHADOWS of `WeakPromiseBridge.execPrefixPfRun` /
`.execWfPfRun`, not replacements for them. -/

theorem progFreeExecProgOk (ps : List P) (d0 : D) (E : Exec) :
    progFree pstep → execWf E → execClsOk pcls ps E →
    (∀ (k : Nat) (s : Estep), E.exTr[k]? = some s → s.esAg < ps.length) →
    execProgOk pstep pcls (fun _ => ps) (fun _ => d0) E := by
  intro hpf hE hck hag
  apply execProgOkSingle
  intro k s hs
  obtain ⟨p, hp⟩ := someOfIsSome (lookup_lt_is_Some_2 (hag k s hs))
  exact ⟨p, p, unprojLbl s.esLb, hp,
    lblRealizesIntro pcls p (stt E k) (stt E (k + 1)) s.esAg s.esLb (execStepAt E k s hE hs)
      (hck k s p hs hp),
    hpf _ _ _ _, (listSetLookupId hp).symm⟩

/-- (Lean-only, deviation 4) The same supply, at the pinned LTS (`unprojLbl`
never yields a fetch). -/
theorem progFreeExecProgOkPin (ps : List P) (d0 : D) (E : Exec) :
    progFree pstep → execWf E → execClsOk pcls ps E →
    (∀ (k : Nat) (s : Estep), E.exTr[k]? = some s → s.esAg < ps.length) →
    execProgOk (pstepPin (exImg E) pstep) pcls (fun _ => ps) (fun _ => d0) E := by
  intro hpf hE hck hag
  apply execProgOkSingle
  intro k s hs
  obtain ⟨p, hp⟩ := someOfIsSome (lookup_lt_is_Some_2 (hag k s hs))
  exact ⟨p, p, unprojLbl s.esLb, hp,
    lblRealizesIntro pcls p (stt E k) (stt E (k + 1)) s.esAg s.esLb (execStepAt E k s hE hs)
      (hck k s p hs hp),
    ⟨hpf _ _ _ _, fetchPinUnproj _ _⟩, (listSetLookupId hp).symm⟩

theorem execPrefixPfRunPf (ps : List P) (d0 : D) (E : Exec) (n : Nat) :
    pclsEqr pcls →
    progFree pstep → execWf E → execClsOk pcls ps E →
    (∀ (k : Nat) (s : Estep), E.exTr[k]? = some s → s.esAg < ps.length) →
    n ≤ E.exTr.length →
    ∃ c, rtc (wpPfRun pstep pcls) (wpInit (exImg E) d0 ps) c ∧
      c.pcAgs.length = ps.length ∧ c.pcAgs.map Wpagent.paSt = ps ∧
      cfgMatchd c (stt E n) := by
  intro hce hpf hE hck hag hn
  obtain ⟨c, hrun, hst, _, hm⟩ :=
    execPrefixPfRunProg (pstepPin (exImg E) pstep) pcls (fun _ => ps) (fun _ => d0) E n hce
      (pstepPinPinned _ _) hE
      (execProgOkStar _ pcls _ _ _ (progFreeExecProgOkPin pstep pcls ps d0 E hpf hE hck hag)) hn
  have hst' : c.pcAgs.map Wpagent.paSt = ps := hst
  exact ⟨c, wpPfRunPinSub _ pstep pcls _ _ hrun, by rw [← hst', List.length_map], hst', hm⟩

theorem execWfPfRunPf (ps : List P) (d0 : D) (E : Exec) :
    pclsEqr pcls →
    progFree pstep → execWf E → execClsOk pcls ps E →
    (∀ (k : Nat) (s : Estep), E.exTr[k]? = some s → s.esAg < ps.length) →
    ∃ c, rtc (wpPfRun pstep pcls) (wpInit (exImg E) d0 ps) c ∧
      cfgMatchd c (stt E E.exTr.length) := by
  intro hce hpf hE hck hag
  obtain ⟨c, h1, _, _, h4⟩ :=
    execPrefixPfRunPf pstep pcls ps d0 E E.exTr.length hce hpf hE hck hag (Nat.le_refl _)
  exact ⟨c, h1, h4⟩

end realize

end Weak
