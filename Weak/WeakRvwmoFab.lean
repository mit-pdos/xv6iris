/-
Weak: **B1b-2 — the fabric order as bundle data**.

Rocq: `iris/WeakRvwmoFab.v` @ xxvzwolszwmp.

## The Rocq header, in substance

Design `claude-notes/design/weak-memory-route-b.md` §4d.4 (the B1b-2 paragraph).
`WeakRvwmoSupply` is B1b-1 (fabric QUIESCENCE: no `LDev` anywhere, so the global fabric is the
constant `fun _ => d0`); this file lifts the quiescence restriction by making the FABRIC ORDER part
of the conformance bundle.

THE SHAPE.  A row event's EMISSION BLOCK is the administrative stretch that precedes it together
with the realizing step(s).  MMIO is administrative (`WeakEvInst` emits `LDev`, and
`projLbl _ LDev = none`), so the fabric moves ONLY inside blocks, and a block either contains an
`LDev` (a DEV BLOCK: it moves the fabric) or does not (then it is fabric-PRESERVING and
fabric-BLIND — `WeakEvInst.pdevEvOk`, reached here only through `WeakRvwmoSupply.pstepEvDevfree`).
The bundle carries `gfDev : List Geid` (the dev blocks, IN FABRIC ORDER) and
`fab : Nat → Efab` (the global fabric trace; the `n`-th dev block runs `fab n → fab (n+1)`).
A whole dev block is ONE fabric transition, so the fabric ordinal indexes BLOCKS, not `LDev`
steps; hence `gfDev.Nodup` is the right well-formedness clause.

THE DESIGN CORRECTION (Rocq's).  The one-fabric `WeakRvwmoConf.hartConf` is JOINTLY
UNSATISFIABLE as soon as a hart has two dev blocks with another hart's dev block between them
(`hartConfNoGap` below machine-checks why: across a non-dev block the per-hart fabric is constant).
The fix, additive and local: `hemitf`, the emission with the block's two fabric endpoints carried
by SEPARATE functions (`dvi k → dvo k`, no relation between `dvo k` and `dvi (k+1)`); `hartConf`
embeds (`hartConfHemitf`, `dvo := dv ∘ succ`).

WHAT IS HERE.  §2 dev blocks (`emDev`, `isDevBlock`); §3 `hemitf`, `hartConff`, the embedding and
`hemitfStates` (per block the `hblk` fact plus, for a non-dev block, fabric preservation and full
blindness); §4 the bundle `Gfexec` / `gfexecConfIO` (W13 (I), deviation 5); §5 the model arm (`gdevAdj`,
`gfexecConsistent`, `racyF`, `rfAcyclic`, decidability, `linExtF`, `topoLinearizesF`,
`linExtFDevBefore`, `topoExistsF`); §6 non-vacuity (`gfexecConfOfQconf`: B1b-1's bundle embeds
with `gfDev = []`; a witness with a non-empty `gfDev` is not available — no `LDev`-emitting run
witness exists in the tree); §7 the supply at a moving fabric (`supplyOfFconf`, `fconfSupply`);
§8 hulls (`gfHull`, `dclosed`, `dclosedPrefix`, `gfHullConsistent`).  Rocq §8's closing comments
enumerate the conformance restriction (O1–O5) and the `cycle_kill` mirror as OBLIGATIONS, not
proved there — likewise not here (nothing admitted, no axiom).

A LEAF: nothing imports this file.

## WeakEvInst device arms used

W13 (I) (deviation 5): the fabric MARKER `WeakEvInst.pdevEv` and its law `WeakEvInst.pdevEvOk`
(a `pdevEv`-false step is fabric-preserving and fabric-blind) are used DIRECTLY -- `hemitf`
records each block's contact bit and the non-member folding rests on `pdevEvOk` alone, at any
start state.  The quiet-row lemmas `WeakRvwmoSupply.pdevEvFalse` / `devQuietStep` (W-DISK) are
used only to relate contact to the label-based `emDev` on a quiet row
(`WeakRvwmoFab.hemitfQuietTq`: `hartConfNoGap`, `gfexecConfOfQconf`).
`pstepEv` / `pclsEv` / `Pexv6.PDisk` are named only as the parameters of `execProgOk'` and as a
dummy default.

## Deviations from Rocq

1. NAMES: the tree's camelCase (map below); `S k` ↦ `k + 1`; `l !! n` ↦ `l[n]?`; `.*1` ↦
   `map Prod.fst`; `seq 0 N` ↦ `List.range' 0 N`; `default [] o` ↦ `o.getD []`;
   `bool_decide (j = k)` ↦ `if j = k`; `Decision` ↦ `Decidable`; the record `gfexec` ↦ structure
   `Gfexec` (constructor `GFExec`, fields `gfGd`, `gfDev`); `tc` is `MachCSL`'s (`TransGen`).
   `dev_state` ↦ `Efab` (the event instance's fabric: device states plus the residual UART/PLIC
   programs, `WeakEvPf` deviation 9 / owner decision Q1).
2. O2 / STAGE C — THE FETCH IS ADMINISTRATIVE, PINNED TO THE BOOT IMAGE, exactly as in
   `WeakRvwmoSupply` (its deviation 2; owner ruling Q-C1, `notes/weak-port-o2-stageC.md` §B).
   - `gfexecConfIO` gains, per row, the clause `emFetchImg GF.gfGd.gdG.gxImg em` (every fetch
     item of the emission reads the graph's image at timestamp 0; W13 (I) [R28.s5] called it the
     `emZifencei` slot until W5d-G G1 gave that slot its Zifencei content in `gfexecConfZ`,
     deviation 6), between the fabric clause and the deps clause; `gfexecConfOfQconf` takes it
     from `gdexecQconf`'s.
   - Lean-only `WeakRvwmoFab.pstepQ Q` (`pstepEv` restricted to labels satisfying `Q`;
     `pstepQ (WeakAxRealize.fetchPin im)` is `pstepPin im pstepEv`, `WeakRvwmoFab.pstepQPin`),
     `WeakRvwmoFab.admRunQ`, `hblkQ Q` (`hblk` at `pstepQ Q`), `hblkQHblk`, `hemitfStatesQ`,
     `hartConffStatesQ`, `fconfRowsPin`.  Rocq's `hblk` / `hemitfStates` / `hartConffStates` /
     `fconfRows` are kept as stated, derived at `Q := fun _ => True`.
   - `supplyOfFconf` takes an image `im`; its third premise has the blocks as
     `hblkQ (WeakAxRealize.fetchPin im) …` (Rocq: `hblk`) and its conclusion is
     `execProgOk' (pstepPin im pstepEv) …`.
   - `fconfSupply`: Rocq's premises; conclusion at `pstepPin GF.gfGd.gdG.gxImg pstepEv`.
   Stage B's `hblkIn`, `hblkInHblk`, `hblkInMono`, `hemitfStatesIn`, `hartConffStatesIn`,
   `fconfRowsIn` and `candFetchInertF` are DELETED.
3. PROOFS: per-constructor case analysis and `omega`; `gdevAdjDec` searches `List.range` (Rocq
   `seq`); `linExtFDevBefore` inducts on the gap `n - (m+1)` as Rocq does.  Rocq's
   `Print Assumptions` audit is not reproduced (the lint bans axioms).  Lean-only helper
   `lbIsdevRen` (the per-label step of `hasDevRen` / `emDevRen`).
4. W-DISK (plan `notes/weak-allocproc-plan.md` §C "W-DISK", [R17.3][R18.2]; SUPERSEDED by
   deviation 5 -- kept as the record): under the
   STATE-AWARE `WeakEvInst.pdevEv` a disk block can move the fabric with no `LDev` in it (a
   `DWriteDev` store / skip / abort), so Rocq's `hemitfStates` family -- stated for an ARBITRARY
   start -- is FALSE for a device-active disk row.  (b) `hemitfStatesQ`, `hemitfStates`,
   `hartConffStatesQ`, `hartConffStates`, `hartConfNoGap` take the QUIET-ROW hypothesis
   `devQuiet p ∧ (∀ dp, p = .PDisk dp → ∀ kd ba bs sa sv, LDev kd ba bs sa sv ∉ labels)` (a hart row is
   unconstrained; a disk row must be `LDev`-free), carried by the induction through the
   Lean-only `WeakRvwmoFab.quietStep` / `WeakRvwmoFab.quietAdm`; (a) `gfexecConf` gains the
   INTERIM per-row clause `boot i = .PDisk dp → emDevfree em` (DELETED BY W13 (I); until then
   the internal bundle is vacuous for a device-active disk row, the `ioResidueGwfInterim`
   pattern); `fconfRowsPin` / `fconfRows` take `devQuiet (boot i)` and extract the rest from (a);
   `fconfSupply` takes `∀ i, i < N → devQuiet (boot i)` (discharged at the boot pool
   `epsInit`).  `gfexecConfOfQconf` supplies (a) from `gdexecQconf`'s `emDevfree`.
5. **W13 (I) — MEMBERSHIP BY FABRIC CONTACT** (plan §C W13 (I) bundle half, ruling [OWN.43],
   superseding [R22.2]; `PROGRESS-W13I.md`).  The bundle is `gfexecConfIO` (Rocq's
   `gfexec_conf`, restated; `gfexecConf` is DELETED): its `isDevBlock em k ↔ (i, k) ∈ gfDev`
   clause is REPLACED by `(i, k) ∈ gfDev ↔ gisIo (i, k) ∨ dvi k ≠ dvo k ∨ tq k`, and W-DISK's
   INTERIM `.PDisk` `LDev`-free clause (deviation 4 (a)) is DELETED.  `tq k` is the block's
   fabric-CONTACT bit, recorded by `hemitf` (a third parameter beside `dvi`/`dvo`): each
   administrative run is a Lean-only `WeakRvwmoFab.admRunT` (the `admRun` that also returns
   "some step is `pdevEv`-true"), and each tagged constructor fixes `tq k` to the OR of the
   block's bits.  Consequences: `hartConff` takes `tq`; `hemitHemitf` / `hartConfHemitf` produce
   the bits (`∃ tq`, read off the derivation; `WeakRvwmoFab.hemitfTqCongr`); `hemitfStatesQ`,
   `hemitfStates`, `hartConffStatesQ`, `hartConffStates` LOSE deviation 4 (b)'s quiet-row
   hypothesis and classify by contact -- `tq k = false` gives fabric preservation, NOT I/O-class
   (`WeakRvwmoFab.realizesIoTouch`: an `LIo` event is realized by an `LDev` step), and the
   `hblkQ … d d` folding at EVERY fabric `d` (the folding GENERALIZED, from `pdevEvOk`);
   `fconfRowsPin` DERIVES its non-member conjunct from contact, and `fconfRowsPin` / `fconfRows` /
   `fconfSupply` take NO quiet-boot hypothesis; `hartConfNoGap`'s statement is unchanged (proof via
   `WeakRvwmoFab.hemitfQuietTq`); `gfexecConfOfQconf` takes `∀ i, devQuiet (boot i)` (a quiescent
   emission from inside a disk burst touches the fabric with no `LDev`).  `gisIo` moved here from
   `GraphFabResidue`.  Marks: FAITHFUL to RVWMO (no ISA order added -- RVWMO/Sail/Zifencei/PMAs
   have no device-internal events; `gfDev` is device-model/trusted-surface text, D45/D49 class),
   EQUAL to [R22.2] on every xv6 run, STRONGER as generic trusted text only by unreachable
   non-moving fabric-touching blocks ((R3) orders them).  `supplyOfFconf` is unchanged.

6. **W5d-G G1 — THE ZIFENCEI FETCH CLAUSE** (plan rev 45 §C W5d-G G1; D27 (a) [OWN.6], D40
   [OWN.15], D43 (a) [OWN.18], [OWN.26]).  The slot `emZifencei` gets its Zifencei content:
   `emZifencei G i em := GraphFetch.emZif G i em` (`Weak/GraphFetch.lean`: every administrative
   fetch item of hart `i`'s emission satisfies the trusted-base item `gzFetch` at its real slot
   tag, with the emission's fence.i contributors `gzContrib G (emFenceI em) i`).  The bundle that
   carries it is **`gfexecConfZ`** -- `gfexecConfIO`'s text with the slot `emZifencei
   GF.gfGd.gdG i em` (`gfexecConfZ` is `xv6ConfS`'s fabric half, W13 (W)).  DEVIATION from the
   plan's "the slot is replaced in `gfexecConfIO`": the PINNED supply (`fconfRowsPin`,
   `supplyOfFconf`, `fconfSupply`, and W13's chain over them in `FabInd`/`Lin2`/`KillIO`) needs
   every block's labels pinned (`hblkQ (fetchPin im)`), and D43 (a) keeps `pstepPin`/`fetchPin`
   as the M1 kernel-text instance until G6 re-threads the supply onto `execProgOk'S`; and the
   Zifencei clause is not transported by `gfexecConfRen`/`gfexecConfHull` before G2 (tags =
   gmo indices), G3/G4 (the fetch fragment in `racyD`, `retimeZifencei`) and the hull closure
   (R1 (a)).  So `gfexecConfIO` stays the PINNED bundle -- its slot is now written
   `emFetchImg GF.gfGd.gdG.gxImg em` directly (TEXT of the clause unchanged; the old slot def is
   gone) -- and `gfexecConfZOfIO` moves a pinned bundle to the Zifencei one given the per-row
   slot, e.g. by the kernel-text instance `GraphFetch.emZifOfPinC` (pinned fetches of unwritten
   bytes).  G6 collapses the two.  Spec: an encoding choice (the ISA is silent on proof
   organisation); `gfexecConfZ` is FAITHFUL to the Zifencei reading of `gzFetch`, `gfexecConfIO`
   is the pinned (kernel-only, STRONGER) M1 instance.

**Rocq → Lean name map.**  `orb_false_split` `orbFalseSplit`, `lb_isdev` `lbIsdev`,
`lb_isdev_ne` `lbIsdevNe`, `has_dev` `hasDev`, `has_dev_false` `hasDevFalse`, `em_dev` `emDev`,
`is_dev_block` `isDevBlock`, `is_dev_block_dec` `isDevBlockDec`, `em_dev_eadm` `emDevEadm`,
`em_dev_tag_eq` `emDevTagEq`, `em_dev_tag_ne` `emDevTagNe`, `em_dev_devfree` `emDevDevfree`,
`em_devfree_no_dev_block` `emDevfreeNoDevBlock`, `has_dev_ren` `hasDevRen`, `em_dev_ren`
`emDevRen`, `hemitf` `hemitf` (`HFnil` `HFone` `HFpair`), `hart_conff` `hartConff`,
`hemit_hemitf` `hemitHemitf`, `hart_conf_hemitf` `hartConfHemitf`, `hblk` `hblk`,
`hblock_hblk` `hblockHblk`, `hemitf_states` `hemitfStates`, `hart_conff_states`
`hartConffStates`, `hart_conf_no_gap` `hartConfNoGap`, `gfexec` `Gfexec` (`GFExec`, `gf_gd`
`gfGd`, `gf_dev` `gfDev`), `gfexec_conf` `gfexecConfIO` (deviation 5), `gdev_adj` `gdevAdj`,
`gfexec_consistent` `gfexecConsistent`, `RacyF` `racyF`, `RF_gmo` `WeakRvwmoFab.rfGmo` (a Lean-side clash with `Weak.rfGmo`), `tc_RF_gmo`
`tcRfGmo`, `RF_acyclic` `rfAcyclic`, `gdev_adj_dec` `gdevAdjDec`, `racyF_dec` `racyFDec`,
`lin_extF` `linExtF`, `lin_extF_lin_extD` `linExtFLinExtD`, `topo_linearizes_F`
`topoLinearizesF`, `before_trans` `beforeTrans`, `lin_extF_nodup` `linExtFNodup`,
`lin_extF_dev_before` `linExtFDevBefore`, `RacyF_mem` `racyFMem`, `topo_exists_F` `topoExistsF`,
`gfexec_conf_of_qconf` `gfexecConfOfQconf`, `dstep_at` `dstepAt`, `dcnt` `dcnt`, `dcnt_0`
`dcnt0`, `dcnt_step_dev` `dcntStepDev`, `dcnt_step_ne` `dcntStepNe`, `supply_of_fconf`
`supplyOfFconf`, `fconf_rows` `fconfRows`, `fconf_supply` `fconfSupply`, `gf_hull` `gfHull`,
`dclosed` `dclosed`, `dclosed_cons` `dclosedCons`, `filter_none_nil` `filterNoneNil`,
`dclosed_prefix` `dclosedPrefix`, `gf_hull_dev_lookup` `gfHullDevLookup`, `gf_hull_dev_cut`
`gfHullDevCut`, `gf_hull_consistent` `gfHullConsistent`.

**Not ported:** nothing — every Rocq definition and lemma has a Lean twin.

**W12 (1) (plan §C W12; D25 (a) [OWN.5]) — statement edit (Lean-only).**  `topoLinearizesF` takes the core `rvwmoCoreD GF.gfGd` (the only part of `gfexecConsistent` it used).  RVWMO⁻ callers
are unchanged in text (`WeakRvwmoAcyc.coeCoreOfMinus`).
-/
import Weak.WeakRvwmoSupply
import Weak.WeakRvwmoDec
import Weak.GraphFetch

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open Wlabel

/-! ## 1. Boolean preliminaries -/

theorem orbFalseSplit (b1 b2 : Bool) : (b1 || b2) = false → b1 = false ∧ b2 = false := by
  cases b1 <;> cases b2 <;> simp

/-! ## 2. Dev blocks -/

def lbIsdev (l : Wlabel) : Bool :=
  match l with
  | LDev .. => true
  | _ => false

theorem lbIsdevNe (l : Wlabel) : lbIsdev l = false → ∀ kd ba bs sa sv, l ≠ LDev kd ba bs sa sv := by
  intro h kd ba bs sa sv he; subst he; simp [lbIsdev] at h

def hasDev (ls : List Wlabel) : Bool :=
  match ls with
  | [] => false
  | l :: ls' => lbIsdev l || hasDev ls'

theorem hasDevFalse (ls : List Wlabel) : hasDev ls = false → ∀ kd ba bs sa sv, LDev kd ba bs sa sv ∉ ls := by
  induction ls with
  | nil => intro _ _ _ _ _ _ h; simp at h
  | cons l ls ih =>
    intro h kd ba bs sa sv hin
    obtain ⟨hl, hls⟩ := orbFalseSplit _ _ h
    rcases List.mem_cons.1 hin with he | hin'
    · rw [← he] at hl; simp [lbIsdev] at hl
    · exact ih hls kd ba bs sa sv hin'

/-- An administrative item belongs to the block of the NEAREST TAGGED ITEM AT OR AFTER IT;
`pend` = "an `LDev` has been seen since the last tagged item". -/
def emDev (pend : Bool) (k : Nat) (es : List Eitem) : Bool :=
  match es with
  | [] => false
  | (l, none) :: es' => emDev (pend || lbIsdev l) k es'
  | (l, some j) :: es' =>
      if j = k then ((pend || lbIsdev l) || emDev false k es')
      else emDev false k es'

def isDevBlock (em : Hemission) (k : Nat) : Prop := emDev false k em.emItems = true

instance isDevBlockDec (em : Hemission) (k : Nat) : Decidable (isDevBlock em k) :=
  inferInstanceAs (Decidable (emDev false k em.emItems = true))

/-- The administrative stretch folds into `pend`. -/
theorem emDevEadm (ls : List Wlabel) (pend : Bool) (k : Nat) (rest : List Eitem) :
    emDev pend k (eadm ls ++ rest) = emDev (pend || hasDev ls) k rest := by
  induction ls generalizing pend with
  | nil => simp [eadm, hasDev]
  | cons l ls ih =>
    show emDev (pend || lbIsdev l) k (eadm ls ++ rest) = _
    rw [ih]
    simp only [hasDev, Bool.or_assoc]

/-- ONE BLOCK, at its own row position … -/
theorem emDevTagEq (pend : Bool) (ls : List Wlabel) (l : Wlabel) (k : Nat) (es : List Eitem) :
    emDev pend k (eadm ls ++ (l, some k) :: es) =
      (((pend || hasDev ls) || lbIsdev l) || emDev false k es) := by
  rw [emDevEadm]
  show (if k = k then _ else _) = _
  rw [if_pos rfl]

/-- … and at any other. -/
theorem emDevTagNe (pend : Bool) (ls : List Wlabel) (l : Wlabel) (k n : Nat) (es : List Eitem) :
    k ≠ n → emDev pend n (eadm ls ++ (l, some k) :: es) = emDev false n es := by
  intro hne
  rw [emDevEadm]
  show (if k = n then _ else _) = _
  rw [if_neg hne]

/-- An `LDev`-free item list has no dev block. -/
theorem emDevDevfree (k : Nat) (es : List Eitem) :
    (∀ kd ba bs sa sv, LDev kd ba bs sa sv ∉ es.map Prod.fst) → emDev false k es = false := by
  induction es with
  | nil => intro _; rfl
  | cons it es ih =>
    intro hnd
    obtain ⟨l, o⟩ := it
    have hl : lbIsdev l = false := by
      cases l <;> first | rfl | exact absurd (List.mem_cons_self ..) (hnd _ _ _ _ _)
    have hrest : ∀ kd ba bs sa sv, LDev kd ba bs sa sv ∉ es.map Prod.fst :=
      fun kd ba bs sa sv hin => hnd kd ba bs sa sv (List.mem_cons_of_mem _ hin)
    cases o with
    | some j =>
      show (if j = k then _ else _) = false
      split
      · rw [hl, ih hrest]; rfl
      · exact ih hrest
    | none =>
      show emDev (false || lbIsdev l) k es = false
      rw [hl]; exact ih hrest

theorem emDevfreeNoDevBlock (em : Hemission) (k : Nat) : emDevfree em → ¬ isDevBlock em k := by
  intro h hd
  unfold isDevBlock at hd
  rw [emDevDevfree k em.emItems h] at hd
  exact absurd hd (by decide)

theorem lbIsdevRen (π : Nat → Nat) (l : Wlabel) : lbIsdev (wlblRen π l) = lbIsdev l := by
  cases l <;> rfl

/-- `emDev` is blind to the ts renaming. -/
theorem hasDevRen (π : Nat → Nat) (ls : List Wlabel) : hasDev (ls.map (wlblRen π)) = hasDev ls := by
  induction ls with
  | nil => rfl
  | cons l ls ih =>
    show (lbIsdev (wlblRen π l) || hasDev (ls.map (wlblRen π))) = _
    rw [ih, lbIsdevRen]; rfl

theorem emDevRen (π : Nat → Nat) (pend : Bool) (k : Nat) (es : List Eitem) :
    emDev pend k (es.map (eitemRen π)) = emDev pend k es := by
  induction es generalizing pend with
  | nil => rfl
  | cons it es ih =>
    obtain ⟨l, o⟩ := it
    cases o with
    | some j =>
      show (if j = k then ((pend || lbIsdev (wlblRen π l)) || emDev false k (es.map (eitemRen π)))
          else emDev false k (es.map (eitemRen π))) = (if j = k then _ else _)
      rw [lbIsdevRen, ih]
    | none =>
      show emDev (pend || lbIsdev (wlblRen π l)) k (es.map (eitemRen π)) = _
      rw [lbIsdevRen, ih]; rfl

/-! ## 3. `hemitf`: the emission with two fabric endpoints and per-item fabric CONTACT -/

/-- (Lean-only, W13 (I) [OWN.43]) The label-carrying administrative run that RECORDS its fabric
CONTACT: the last index is `true` iff some step of the run is `pdevEv`-true. -/
inductive WeakRvwmoFab.admRunT (instr : Bool) :
    Pexv6 → Efab → List Wlabel → Pexv6 → Efab → Bool → Prop where
  | ATnil (p : Pexv6) (d : Efab) : WeakRvwmoFab.admRunT instr p d [] p d false
  | ATcons (p : Pexv6) (d : Efab) (l : Wlabel) (p1 : Pexv6) (d1 : Efab)
      (ls : List Wlabel) (p' : Pexv6) (d' : Efab) (b : Bool) :
      lbAdmin instr l → pstepEv p d l p1 d1 →
      WeakRvwmoFab.admRunT instr p1 d1 ls p' d' b →
      WeakRvwmoFab.admRunT instr p d (l :: ls) p' d' (pdevEv p l p1 || b)

/-- (Lean-only, W13 (I)) Forgetting the contact bit. -/
theorem WeakRvwmoFab.admRunTRun (instr : Bool) (p : Pexv6) (d : Efab) (ls : List Wlabel)
    (p' : Pexv6) (d' : Efab) (b : Bool) :
    WeakRvwmoFab.admRunT instr p d ls p' d' b → admRun instr p d ls p' d' := by
  intro h
  induction h with
  | ATnil p d => exact .ARnil p d
  | ATcons p d l p1 d1 ls p' d' b ha hs _ ih => exact .ARcons p d l p1 d1 ls p' d' ha hs ih

/-- (Lean-only, W13 (I)) Every run has its contact bit. -/
theorem WeakRvwmoFab.admRunTOfRun (instr : Bool) (p : Pexv6) (d : Efab) (ls : List Wlabel)
    (p' : Pexv6) (d' : Efab) :
    admRun instr p d ls p' d' → ∃ b, WeakRvwmoFab.admRunT instr p d ls p' d' b := by
  intro h
  induction h with
  | ARnil p d => exact ⟨false, .ATnil p d⟩
  | ARcons p d l p1 d1 ls p' d' ha hs _ ih =>
    obtain ⟨b, hb⟩ := ih
    exact ⟨_, .ATcons p d l p1 d1 ls p' d' b ha hs hb⟩

/-- (Lean-only, W13 (I)) THE GENERALIZED FOLDING, one run: a CONTACT-FREE run is
fabric-preserving and fabric-BLIND (`WeakEvInst.pdevEvOk`) -- at any start state. -/
theorem WeakRvwmoFab.admRunTQuiet (instr : Bool) (p : Pexv6) (d : Efab) (ls : List Wlabel)
    (p' : Pexv6) (d' : Efab) (b : Bool) :
    WeakRvwmoFab.admRunT instr p d ls p' d' b → b = false →
    d' = d ∧ ∀ d0, WeakRvwmoFab.admRunT instr p d0 ls p' d0 false := by
  intro h
  induction h with
  | ATnil p d => intro _; exact ⟨rfl, fun d0 => .ATnil p d0⟩
  | ATcons p d l p1 d1 ls p' d' b ha hs _ ih =>
    intro hb
    obtain ⟨hl, hb'⟩ := Bool.or_eq_false_iff.mp hb
    obtain ⟨hd1, hall⟩ := pdevEvOk p d l p1 d1 hs hl
    obtain ⟨hd', hall'⟩ := ih hb'
    refine ⟨by rw [hd', hd1], fun d0 => ?_⟩
    have h := WeakRvwmoFab.admRunT.ATcons p d0 l p1 d0 ls p' d0 false ha (hall d0) (hall' d0)
    rw [hl] at h
    exact h

/-- (Lean-only, W13 (I)) An `LDev`-free run from a QUIET state (`devQuiet`, W-DISK) is
contact-free. -/
theorem WeakRvwmoFab.admRunTFalse (instr : Bool) (p : Pexv6) (d : Efab) (ls : List Wlabel)
    (p' : Pexv6) (d' : Efab) (b : Bool) :
    WeakRvwmoFab.admRunT instr p d ls p' d' b → devQuiet p →
    (∀ kd ba bs sa sv, LDev kd ba bs sa sv ∉ ls) → b = false := by
  intro h
  induction h with
  | ATnil => intro _ _; rfl
  | ATcons p d l p1 d1 ls p' d' b _ hs _ ih =>
    intro hq hnd
    have hne : ∀ kd ba bs sa sv, l ≠ LDev kd ba bs sa sv := fun kd ba bs sa sv he => hnd kd ba bs sa sv (by simp [he])
    have h1 := pdevEvFalse p l p1 hq hne
    have h2 := ih (devQuietStep _ _ _ _ _ hs hne hq)
      (fun kd ba bs sa sv hin => hnd kd ba bs sa sv (List.mem_cons_of_mem _ hin))
    simp only [h1, h2, Bool.or_self]

/-- (Lean-only, W13 (I)) An I/O-class row event is realized by an `LDev` step (`projLbl`), which
is `pdevEv`-true: an I/O item is a fabric CONTACT by class. -/
theorem WeakRvwmoFab.realizesIoTouch (p : Pexv6) (ws : Wstate) (lb : Lbl) (l : Wlabel)
    (p' : Pexv6) : hlblRealizes p ws lb l → lbIsIo lb = true → pdevEv p l p' = true := by
  rintro ⟨_, _, _, hpr⟩ hio
  cases l <;> simp only [projLbl, Option.some.injEq, reduceCtorEq] at hpr <;>
    first | rfl | (subst hpr; simp [lbIsIo] at hio)

/-- The emission with the block's two fabric endpoints `dvi k → dvo k` AND (W13 (I) [OWN.43],
deviation 5) its fabric CONTACT bit `tq k`: `true` iff some step of the block (admin run +
tagged step(s)) is `pdevEv`-true. -/
inductive hemitf (dvi dvo : Nat → Efab) (tq : Nat → Bool) :
    Nat → Wstate → List Lbl → Pexv6 → List Eitem → Pexv6 → Prop where
  | HFnil (k : Nat) (ws : Wstate) (p : Pexv6) : hemitf dvi dvo tq k ws [] p [] p
  | HFone (k : Nat) (ws : Wstate) (lb : Lbl) (row : List Lbl) (p : Pexv6) (ls : List Wlabel)
      (pa : Pexv6) (da : Efab) (l : Wlabel) (p' : Pexv6) (es : List Eitem) (pfin : Pexv6)
      (b : Bool) :
      WeakRvwmoFab.admRunT true p (dvi k) ls pa da b →
      hlblRealizes pa ws lb l →
      pstepEv pa da l p' (dvo k) →
      tq k = (b || pdevEv pa l p') →
      hemitf dvi dvo tq (k + 1) (lblPost k ws lb) row p' es pfin →
      hemitf dvi dvo tq k ws (lb :: row) p (eadm ls ++ (l, some k) :: es) pfin
  | HFpair (k : Nat) (ws : Wstate) (lb : Lbl) (row : List Lbl) (p : Pexv6) (ls1 : List Wlabel)
      (pa : Pexv6) (da : Efab) (l1 : Wlabel) (pm : Pexv6) (dm : Efab)
      (ls2 : List Wlabel) (pm2 : Pexv6) (dm2 : Efab) (l2 : Wlabel) (p' : Pexv6)
      (es : List Eitem) (pfin : Pexv6) (b1 b2 : Bool) :
      WeakRvwmoFab.admRunT true p (dvi k) ls1 pa da b1 →
      hlblRealizesPair pa pm2 ws lb l1 l2 →
      pstepEv pa da l1 pm dm →
      WeakRvwmoFab.admRunT false pm dm ls2 pm2 dm2 b2 →
      pstepEv pm2 dm2 l2 p' (dvo k) →
      tq k = (((b1 || pdevEv pa l1 pm) || b2) || pdevEv pm2 l2 p') →
      hemitf dvi dvo tq (k + 1) (lblPost k ws lb) row p' es pfin →
      hemitf dvi dvo tq k ws (lb :: row) p
        (eadm ls1 ++ (l1, some k) :: (eadm ls2 ++ (l2, some k) :: es)) pfin

def hartConff (_i : Nat) (row : List Lbl) (p0 : Pexv6) (dvi dvo : Nat → Efab)
    (tq : Nat → Bool) (em : Hemission) : Prop :=
  hemitf dvi dvo tq 0 wsInit row p0 em.emItems em.emFin

/-- (Lean-only, W13 (I)) The contact bits are read only at the emission's own positions. -/
theorem WeakRvwmoFab.hemitfTqCongr (dvi dvo : Nat → Efab) (tq tq' : Nat → Bool) (k : Nat)
    (ws : Wstate) (row : List Lbl) (p : Pexv6) (es : List Eitem) (pfin : Pexv6) :
    hemitf dvi dvo tq k ws row p es pfin → (∀ n, k ≤ n → tq' n = tq n) →
    hemitf dvi dvo tq' k ws row p es pfin := by
  intro h
  induction h with
  | HFnil k ws p => intro _; exact .HFnil k ws p
  | HFone k ws lb row p ls pa da l p' es pfin b har hre hst htq _ ih =>
    intro hag
    exact .HFone k ws lb row p ls pa da l p' es pfin b har hre hst
      (by rw [hag k (Nat.le_refl _)]; exact htq) (ih (fun n hn => hag n (by omega)))
  | HFpair k ws lb row p ls1 pa da l1 pm dm ls2 pm2 dm2 l2 p' es pfin b1 b2 har1 hre hst1 har2
      hst2 htq _ ih =>
    intro hag
    exact .HFpair k ws lb row p ls1 pa da l1 pm dm ls2 pm2 dm2 l2 p' es pfin b1 b2 har1 hre hst1
      har2 hst2 (by rw [hag k (Nat.le_refl _)]; exact htq) (ih (fun n hn => hag n (by omega)))

/-- THE EMBEDDING: the landed one-fabric emission is the case `dvo = dv ∘ succ` (W13 (I): with
the contact bits read off the derivation). -/
theorem hemitHemitf (dv : Nat → Efab) (k : Nat) (ws : Wstate) (row : List Lbl) (p : Pexv6)
    (es : List Eitem) (pfin : Pexv6) :
    hemit dv k ws row p es pfin → ∃ tq, hemitf dv (fun n => dv (n + 1)) tq k ws row p es pfin := by
  intro h
  induction h with
  | HEnil k ws p => exact ⟨fun _ => false, .HFnil k ws p⟩
  | HEone k ws lb row p ls pa da l p' es pfin har hre hst _ ih =>
    obtain ⟨tq, htq⟩ := ih
    obtain ⟨b, hb⟩ := WeakRvwmoFab.admRunTOfRun _ _ _ _ _ _ har
    refine ⟨fun n => if n = k then (b || pdevEv pa l p') else tq n,
      .HFone k ws lb row p ls pa da l p' es pfin b hb hre hst (by simp) ?_⟩
    exact WeakRvwmoFab.hemitfTqCongr _ _ _ _ _ _ _ _ _ _ htq
      (fun n hn => by simp only [if_neg (show n ≠ k by omega)])
  | HEpair k ws lb row p ls1 pa da l1 pm dm ls2 pm2 dm2 l2 p' es pfin har1 hre hst1 har2 hst2 _ ih =>
    obtain ⟨tq, htq⟩ := ih
    obtain ⟨b1, hb1⟩ := WeakRvwmoFab.admRunTOfRun _ _ _ _ _ _ har1
    obtain ⟨b2, hb2⟩ := WeakRvwmoFab.admRunTOfRun _ _ _ _ _ _ har2
    refine ⟨fun n => if n = k then (((b1 || pdevEv pa l1 pm) || b2) || pdevEv pm2 l2 p')
      else tq n, .HFpair k ws lb row p ls1 pa da l1 pm dm ls2 pm2 dm2 l2 p' es pfin b1 b2 hb1 hre
        hst1 hb2 hst2 (by simp) ?_⟩
    exact WeakRvwmoFab.hemitfTqCongr _ _ _ _ _ _ _ _ _ _ htq
      (fun n hn => by simp only [if_neg (show n ≠ k by omega)])

theorem hartConfHemitf (i : Nat) (row : List Lbl) (p0 : Pexv6) (dv : Nat → Efab)
    (em : Hemission) :
    hartConf i row p0 dv em → ∃ tq, hartConff i row p0 dv (fun n => dv (n + 1)) tq em :=
  hemitHemitf _ _ _ _ _ _ _

/-! ### 3.1 The block, with its two fabric endpoints explicit -/

def hblk (d d' : Efab) (ws : Wstate) (lb : Lbl) (p p' : Pexv6) : Prop :=
  ∃ (pa : Pexv6) (da : Efab),
    admStar pstepEv true p d pa da ∧
    ((∃ l, hlblRealizes pa ws lb l ∧ pstepEv pa da l p' d')
     ∨ (∃ (pm : Pexv6) (dm : Efab) (pm2 : Pexv6) (dm2 : Efab) (l1 l2 : Wlabel),
          hlblRealizesPair pa pm2 ws lb l1 l2 ∧
          pstepEv pa da l1 pm dm ∧
          admStar pstepEv false pm dm pm2 dm2 ∧
          pstepEv pm2 dm2 l2 p' d'))

/-- (Lean-only, deviation 2) `pstepEv` restricted to the labels satisfying `Q`;
`pstepQ (WeakAxRealize.fetchPin im)` is `WeakAxRealize.pstepPin im pstepEv` (by `rfl`). -/
def WeakRvwmoFab.pstepQ (Q : Wlabel → Prop) (p : Pexv6) (d : Efab) (l : Wlabel) (p' : Pexv6)
    (d' : Efab) : Prop :=
  pstepEv p d l p' d' ∧ Q l

theorem WeakRvwmoFab.pstepQPin (im : Image) :
    WeakRvwmoFab.pstepQ (WeakAxRealize.fetchPin im) = pstepPin im pstepEv := rfl

/-- (Lean-only, deviation 2) An `admRun` whose labels satisfy `Q` is a run of `pstepQ Q`. -/
theorem WeakRvwmoFab.admRunQ (Q : Wlabel → Prop) (instr : Bool) (p : Pexv6) (d : Efab)
    (ls : List Wlabel) (p' : Pexv6) (d' : Efab) :
    admRun instr p d ls p' d' → (∀ l, l ∈ ls → Q l) →
    admStar (WeakRvwmoFab.pstepQ Q) instr p d p' d' := by
  intro h
  induction h with
  | ARnil p d => intro _; exact admStarRefl _ instr p d
  | ARcons p d l p1 d1 ls p' d' ha hs _ ih =>
    intro hq
    exact admStarL (WeakRvwmoFab.pstepQ Q) instr p d l p1 d1 p' d' ha
      ⟨hs, hq l List.mem_cons_self⟩ (ih (fun x hx => hq x (List.mem_cons_of_mem _ hx)))

/-- (Lean-only, deviation 2) `hblk` at the restricted LTS `pstepQ Q`. -/
def hblkQ (Q : Wlabel → Prop) (d d' : Efab) (ws : Wstate) (lb : Lbl) (p p' : Pexv6) : Prop :=
  ∃ (pa : Pexv6) (da : Efab),
    admStar (WeakRvwmoFab.pstepQ Q) true p d pa da ∧
    ((∃ l, hlblRealizes pa ws lb l ∧ WeakRvwmoFab.pstepQ Q pa da l p' d')
     ∨ (∃ (pm : Pexv6) (dm : Efab) (pm2 : Pexv6) (dm2 : Efab) (l1 l2 : Wlabel),
          hlblRealizesPair pa pm2 ws lb l1 l2 ∧
          WeakRvwmoFab.pstepQ Q pa da l1 pm dm ∧
          admStar (WeakRvwmoFab.pstepQ Q) false pm dm pm2 dm2 ∧
          WeakRvwmoFab.pstepQ Q pm2 dm2 l2 p' d'))

theorem hblkQHblk (Q : Wlabel → Prop) (d d' : Efab) (ws : Wstate) (lb : Lbl) (p p' : Pexv6) :
    hblkQ Q d d' ws lb p p' → hblk d d' ws lb p p' := by
  have hsub : ∀ (instr : Bool) (p d p' d'),
      admStar (WeakRvwmoFab.pstepQ Q) instr p d p' d' → admStar pstepEv instr p d p' d' :=
    fun _ _ _ _ _ h => rtc_subrel (fun _ _ ⟨l, ha, hs⟩ => ⟨l, ha, hs.1⟩) h
  rintro ⟨pa, da, hs, ⟨l, h1, h2⟩ | ⟨pm, dm, pm2, dm2, l1, l2, h1, h2, h3, h4⟩⟩
  · exact ⟨pa, da, hsub _ _ _ _ _ hs, .inl ⟨l, h1, h2.1⟩⟩
  · exact ⟨pa, da, hsub _ _ _ _ _ hs,
      .inr ⟨pm, dm, pm2, dm2, l1, l2, h1, h2.1, hsub _ _ _ _ _ h3, h4.1⟩⟩

/-- `WeakRvwmoSupply.hblock` IS `hblk` at the two fabric values it reads. -/
theorem hblockHblk (dv : Nat → Efab) (k : Nat) (ws : Wstate) (lb : Lbl) (p p' : Pexv6) :
    hblock dv k ws lb p p' ↔ hblk (dv k) (dv (k + 1)) ws lb p p' :=
  Iff.rfl

/-! ### 3.2 The state extraction, with block classification by CONTACT -/

/-- (Lean-only, W-DISK) One step keeps the QUIET-ROW invariant: a quiet start stays quiet when
a disk start's label is `LDev`-free, and a disk state comes only from a disk state. -/
theorem WeakRvwmoFab.quietStep (p : Pexv6) (d : Efab) (l : Wlabel) (p' : Pexv6) (d' : Efab) :
    pstepEv p d l p' d' → devQuiet p → (∀ dp, p = .PDisk dp → ∀ kd ba bs sa sv, l ≠ LDev kd ba bs sa sv) →
    devQuiet p' ∧ (∀ dp', p' = .PDisk dp' → ∃ dp, p = .PDisk dp) := by
  intro hs hq hnd
  cases p with
  | PHart =>
    cases p' with
    | PHart => exact ⟨trivial, fun _ h => nomatch h⟩
    | PDisk => exact hs.elim
  | PDisk dp =>
    cases p' with
    | PHart => exact hs.elim
    | PDisk dp' => exact ⟨devQuietStep _ _ _ _ _ hs (hnd dp rfl) hq, fun _ _ => ⟨dp, rfl⟩⟩

/-- (Lean-only, W-DISK) ... and so does an administrative run. -/
theorem WeakRvwmoFab.quietAdm (instr : Bool) (p : Pexv6) (d : Efab) (ls : List Wlabel) (p' : Pexv6)
    (d' : Efab) : admRun instr p d ls p' d' → devQuiet p →
    (∀ dp, p = .PDisk dp → ∀ kd ba bs sa sv, LDev kd ba bs sa sv ∉ ls) →
    devQuiet p' ∧ (∀ dp', p' = .PDisk dp' → ∃ dp, p = .PDisk dp) := by
  intro h
  induction h with
  | ARnil p d => intro hq _; exact ⟨hq, fun dp' h => ⟨dp', h⟩⟩
  | ARcons p d l p1 d1 ls p' d' _ hs _ ih =>
    intro hq hnd
    obtain ⟨hq1, hk1⟩ := WeakRvwmoFab.quietStep _ _ _ _ _ hs hq
      (fun dp hp kd ba bs sa sv he => hnd dp hp kd ba bs sa sv (by simp [he]))
    obtain ⟨hq', hk'⟩ := ih hq1 (fun dp1 hp1 kd ba bs sa sv hin => by
      obtain ⟨dp, hp⟩ := hk1 dp1 hp1
      exact hnd dp hp kd ba bs sa sv (List.mem_cons_of_mem _ hin))
    refine ⟨hq', fun dp' hp' => ?_⟩
    obtain ⟨dp1, hp1⟩ := hk' dp' hp'
    exact hk1 dp1 hp1

/-- (Lean-only, deviation 2) `hemitfStates` at `pstepQ Q`, from an emission whose labels
satisfy `Q`.  (W13 (I), deviation 5: NO start-state hypothesis -- a block whose contact bit is
`false` is fabric-preserving, not I/O-class, and replayable at ANY fabric: the GENERALIZED
`∀ d` folding, from `pdevEvOk`.) -/
theorem hemitfStatesQ (Q : Wlabel → Prop) (dvi dvo : Nat → Efab) (tq : Nat → Bool) (k : Nat)
    (ws : Wstate) (row : List Lbl) (p : Pexv6) (es : List Eitem) (pfin : Pexv6) :
    hemitf dvi dvo tq k ws row p es pfin → (∀ x, x ∈ es.map Prod.fst → Q x) →
    ∃ f : Nat → Pexv6, f 0 = p ∧
      ∀ n lb, row[n]? = some lb →
        hblkQ Q (dvi (n + k)) (dvo (n + k)) (rowWsAux k ws (row.take n)) lb (f n) (f (n + 1))
        ∧ (tq (n + k) = false →
           dvo (n + k) = dvi (n + k) ∧ lbIsIo lb = false ∧
           ∀ d, hblkQ Q d d (rowWsAux k ws (row.take n)) lb (f n) (f (n + 1))) := by
  intro h
  induction h with
  | HFnil k ws p => intro _; exact ⟨fun _ => p, rfl, fun n lb hn => by simp at hn⟩
  | HFone k ws lb row p ls pa da l p' es pfin b har hre hst htq _ ih =>
    intro hq
    rw [eblockFst] at hq
    have hqls : ∀ x, x ∈ ls → Q x := fun x hx => hq x (List.mem_append_left _ hx)
    have hql : Q l := hq l (List.mem_append_right _ List.mem_cons_self)
    have har' := WeakRvwmoFab.admRunTRun _ _ _ _ _ _ _ har
    have hio : pdevEv pa l p' = false → lbIsIo lb = false := by
      intro hpl
      cases hc : lbIsIo lb with
      | false => rfl
      | true =>
        rw [WeakRvwmoFab.realizesIoTouch pa ws lb l p' hre hc] at hpl
        exact absurd hpl (by decide)
    obtain ⟨f', hf0, hf⟩ :=
      ih (fun x hx => hq x (List.mem_append_right _ (List.mem_cons_of_mem _ hx)))
    refine ⟨fun n => match n with | 0 => p | n' + 1 => f' n', rfl, ?_⟩
    intro n lb0 hn
    cases n with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hn
      subst hn
      rw [Nat.zero_add]
      refine ⟨⟨pa, da, WeakRvwmoFab.admRunQ Q _ _ _ _ _ _ har' hqls,
        .inl ⟨l, hre, ?_, hql⟩⟩, ?_⟩
      · show pstepEv pa da l (f' 0) (dvo k)
        rw [hf0]; exact hst
      · intro hk
        rw [hk] at htq
        obtain ⟨hb, hpl⟩ := Bool.or_eq_false_iff.mp htq.symm
        obtain ⟨hda, hall0⟩ := WeakRvwmoFab.admRunTQuiet _ _ _ _ _ _ _ har hb
        obtain ⟨hd, hall⟩ := pdevEvOk pa da l p' (dvo k) hst hpl
        refine ⟨by rw [hd, hda], hio hpl, fun d => ⟨pa, d, ?_, .inl ⟨l, hre, ?_, hql⟩⟩⟩
        · exact WeakRvwmoFab.admRunQ Q _ _ _ _ _ _
            (WeakRvwmoFab.admRunTRun _ _ _ _ _ _ _ (hall0 d)) hqls
        · show pstepEv pa d l (f' 0) d
          rw [hf0]; exact hall d
    | succ n =>
      simp only [List.getElem?_cons_succ] at hn
      have e : n + 1 + k = n + (k + 1) := by omega
      rw [e]
      exact hf n lb0 hn
  | HFpair k ws lb row p ls1 pa da l1 pm dm ls2 pm2 dm2 l2 p' es pfin b1 b2 har1 hre hst1 har2
      hst2 htq _ ih =>
    intro hq
    rw [eblockFst, eblockFst] at hq
    have hq1 : ∀ x, x ∈ ls1 → Q x := fun x hx => hq x (List.mem_append_left _ hx)
    have hql1 : Q l1 := hq l1 (List.mem_append_right _ List.mem_cons_self)
    have h2' : ∀ x, x ∈ ls2 ++ l2 :: es.map Prod.fst → Q x :=
      fun x hx => hq x (List.mem_append_right _ (List.mem_cons_of_mem _ hx))
    have hq2 : ∀ x, x ∈ ls2 → Q x := fun x hx => h2' x (List.mem_append_left _ hx)
    have hql2 : Q l2 := h2' l2 (List.mem_append_right _ List.mem_cons_self)
    have har1' := WeakRvwmoFab.admRunTRun _ _ _ _ _ _ _ har1
    have har2' := WeakRvwmoFab.admRunTRun _ _ _ _ _ _ _ har2
    -- an exclusive pair realizes an `LRmw`: never I/O-class
    have hio : lbIsIo lb = false := by
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hlb⟩ := hre
      rw [hlb]; rfl
    obtain ⟨f', hf0, hf⟩ :=
      ih (fun x hx => h2' x (List.mem_append_right _ (List.mem_cons_of_mem _ hx)))
    refine ⟨fun n => match n with | 0 => p | n' + 1 => f' n', rfl, ?_⟩
    intro n lb0 hn
    cases n with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hn
      subst hn
      rw [Nat.zero_add]
      refine ⟨⟨pa, da, WeakRvwmoFab.admRunQ Q _ _ _ _ _ _ har1' hq1,
        .inr ⟨pm, dm, pm2, dm2, l1, l2, hre, ⟨hst1, hql1⟩,
          WeakRvwmoFab.admRunQ Q _ _ _ _ _ _ har2' hq2, ?_, hql2⟩⟩, ?_⟩
      · show pstepEv pm2 dm2 l2 (f' 0) (dvo k)
        rw [hf0]; exact hst2
      · intro hk
        rw [hk] at htq
        have htq' := htq.symm
        simp only [Bool.or_eq_false_iff] at htq'
        obtain ⟨⟨⟨hb1, hp1⟩, hb2⟩, hp2⟩ := htq'
        obtain ⟨hda, hall1a⟩ := WeakRvwmoFab.admRunTQuiet _ _ _ _ _ _ _ har1 hb1
        obtain ⟨hdm, hall1⟩ := pdevEvOk pa da l1 pm dm hst1 hp1
        obtain ⟨hdm2, hall2a⟩ := WeakRvwmoFab.admRunTQuiet _ _ _ _ _ _ _ har2 hb2
        obtain ⟨hd2, hall2⟩ := pdevEvOk pm2 dm2 l2 p' (dvo k) hst2 hp2
        refine ⟨by rw [hd2, hdm2, hdm, hda], hio, fun d =>
          ⟨pa, d, WeakRvwmoFab.admRunQ Q _ _ _ _ _ _
              (WeakRvwmoFab.admRunTRun _ _ _ _ _ _ _ (hall1a d)) hq1,
            .inr ⟨pm, d, pm2, d, l1, l2, hre, ⟨hall1 d, hql1⟩,
              WeakRvwmoFab.admRunQ Q _ _ _ _ _ _
                (WeakRvwmoFab.admRunTRun _ _ _ _ _ _ _ (hall2a d)) hq2,
              ?_, hql2⟩⟩⟩
        show pstepEv pm2 d l2 (f' 0) d
        rw [hf0]; exact hall2 d
    | succ n =>
      simp only [List.getElem?_cons_succ] at hn
      have e : n + 1 + k = n + (k + 1) := by omega
      rw [e]
      exact hf n lb0 hn

theorem hemitfStates (dvi dvo : Nat → Efab) (tq : Nat → Bool) (k : Nat) (ws : Wstate)
    (row : List Lbl) (p : Pexv6) (es : List Eitem) (pfin : Pexv6) :
    hemitf dvi dvo tq k ws row p es pfin →
    ∃ f : Nat → Pexv6, f 0 = p ∧
      ∀ n lb, row[n]? = some lb →
        hblk (dvi (n + k)) (dvo (n + k)) (rowWsAux k ws (row.take n)) lb (f n) (f (n + 1))
        ∧ (tq (n + k) = false →
           dvo (n + k) = dvi (n + k) ∧ lbIsIo lb = false ∧
           ∀ d, hblk d d (rowWsAux k ws (row.take n)) lb (f n) (f (n + 1))) := by
  intro hem
  obtain ⟨f, hf0, hf⟩ :=
    hemitfStatesQ (fun _ => True) dvi dvo tq k ws row p es pfin hem (fun _ _ => trivial)
  refine ⟨f, hf0, fun n lb hn => ?_⟩
  obtain ⟨h1, h2⟩ := hf n lb hn
  refine ⟨hblkQHblk _ _ _ _ _ _ _ h1, fun htq => ?_⟩
  obtain ⟨h3, h4, h5⟩ := h2 htq
  exact ⟨h3, h4, fun d => hblkQHblk _ _ _ _ _ _ _ (h5 d)⟩

/-- (Lean-only, deviation 2) `hartConffStates` at `pstepQ Q`. -/
theorem hartConffStatesQ (Q : Wlabel → Prop) (i : Nat) (row : List Lbl) (p0 : Pexv6)
    (dvi dvo : Nat → Efab) (tq : Nat → Bool) (em : Hemission) :
    hartConff i row p0 dvi dvo tq em → (∀ x, x ∈ emLabels em → Q x) →
    ∃ f : Nat → Pexv6, f 0 = p0 ∧
      ∀ n lb, row[n]? = some lb →
        hblkQ Q (dvi n) (dvo n) (rowWs row n) lb (f n) (f (n + 1))
        ∧ (tq n = false →
           dvo n = dvi n ∧ lbIsIo lb = false ∧
           ∀ d, hblkQ Q d d (rowWs row n) lb (f n) (f (n + 1))) :=
  fun hem hq => hemitfStatesQ Q _ _ _ _ _ _ _ _ _ hem hq

theorem hartConffStates (i : Nat) (row : List Lbl) (p0 : Pexv6) (dvi dvo : Nat → Efab)
    (tq : Nat → Bool) (em : Hemission) :
    hartConff i row p0 dvi dvo tq em →
    ∃ f : Nat → Pexv6, f 0 = p0 ∧
      ∀ n lb, row[n]? = some lb →
        hblk (dvi n) (dvo n) (rowWs row n) lb (f n) (f (n + 1))
        ∧ (tq n = false →
           dvo n = dvi n ∧ lbIsIo lb = false ∧
           ∀ d, hblk d d (rowWs row n) lb (f n) (f (n + 1))) :=
  fun hem => hemitfStates _ _ _ _ _ _ _ _ _ hem

/-- (Lean-only, W13 (I)) On a QUIET ROW (W-DISK's hypothesis: a hart row, or a disk row that
starts between bursts and emits no `LDev`) the label-based classification still decides contact:
a block that is not a dev block (`emDev`) is contact-free. -/
theorem WeakRvwmoFab.hemitfQuietTq (dvi dvo : Nat → Efab) (tq : Nat → Bool) (k : Nat)
    (ws : Wstate) (row : List Lbl) (p : Pexv6) (es : List Eitem) (pfin : Pexv6) :
    hemitf dvi dvo tq k ws row p es pfin →
    devQuiet p ∧ (∀ dp, p = .PDisk dp → ∀ kd ba bs sa sv, LDev kd ba bs sa sv ∉ es.map Prod.fst) →
    ∀ n, n < row.length → emDev false (n + k) es = false → tq (n + k) = false := by
  intro h
  induction h with
  | HFnil k ws p => intro _ n hn; simp at hn
  | HFone k ws lb row p ls pa da l p' es pfin b har hre hst htq _ ih =>
    intro ⟨hdq, hdk⟩ n hn hnd
    rw [eblockFst] at hdk
    have har' := WeakRvwmoFab.admRunTRun _ _ _ _ _ _ _ har
    obtain ⟨hqa, hka⟩ := WeakRvwmoFab.quietAdm _ _ _ _ _ _ har' hdq
      (fun dp hp kd ba bs sa sv hin => hdk dp hp kd ba bs sa sv (List.mem_append_left _ hin))
    obtain ⟨hq', hk'⟩ := WeakRvwmoFab.quietStep _ _ _ _ _ hst hqa (fun dpa hpa kd ba bs sa sv he => by
      obtain ⟨dp, hp⟩ := hka dpa hpa
      exact hdk dp hp kd ba bs sa sv (List.mem_append_right _ (by rw [he]; exact List.mem_cons_self)))
    cases n with
    | zero =>
      rw [Nat.zero_add] at hnd ⊢
      rw [emDevTagEq] at hnd
      obtain ⟨hnd1, _⟩ := orbFalseSplit _ _ hnd
      obtain ⟨hls, hl⟩ := orbFalseSplit _ _ hnd1
      obtain ⟨_, hls'⟩ := orbFalseSplit _ _ hls
      have hb := WeakRvwmoFab.admRunTFalse _ _ _ _ _ _ _ har hdq (hasDevFalse ls hls')
      have hpl := pdevEvFalse pa l p' hqa (lbIsdevNe l hl)
      simp only [htq, hb, hpl, Bool.or_self]
    | succ n =>
      have e : n + 1 + k = n + (k + 1) := by omega
      rw [e] at hnd ⊢
      rw [emDevTagNe false ls l k (n + (k + 1)) es (by omega)] at hnd
      exact ih ⟨hq', fun dp' hp' kd ba bs sa sv hin => by
          obtain ⟨dpa, hpa⟩ := hk' dp' hp'
          obtain ⟨dp, hp⟩ := hka dpa hpa
          exact hdk dp hp kd ba bs sa sv (List.mem_append_right _ (List.mem_cons_of_mem _ hin))⟩ n
        (by simp only [List.length_cons] at hn; omega) hnd
  | HFpair k ws lb row p ls1 pa da l1 pm dm ls2 pm2 dm2 l2 p' es pfin b1 b2 har1 hre hst1 har2
      hst2 htq _ ih =>
    intro ⟨hdq, hdk⟩ n hn hnd
    rw [eblockFst, eblockFst] at hdk
    have har1' := WeakRvwmoFab.admRunTRun _ _ _ _ _ _ _ har1
    have har2' := WeakRvwmoFab.admRunTRun _ _ _ _ _ _ _ har2
    have hdk2 : ∀ dp, p = .PDisk dp → ∀ kd ba bs sa sv, LDev kd ba bs sa sv ∉ ls2 ++ l2 :: es.map Prod.fst :=
      fun dp hp kd ba bs sa sv hin => hdk dp hp kd ba bs sa sv (List.mem_append_right _ (List.mem_cons_of_mem _ hin))
    obtain ⟨hqa, hka⟩ := WeakRvwmoFab.quietAdm _ _ _ _ _ _ har1' hdq
      (fun dp hp kd ba bs sa sv hin => hdk dp hp kd ba bs sa sv (List.mem_append_left _ hin))
    obtain ⟨hqm, hkm⟩ := WeakRvwmoFab.quietStep _ _ _ _ _ hst1 hqa (fun dpa hpa kd ba bs sa sv he => by
      obtain ⟨dp, hp⟩ := hka dpa hpa
      exact hdk dp hp kd ba bs sa sv (List.mem_append_right _ (by rw [he]; exact List.mem_cons_self)))
    have hkm' : ∀ dpm, pm = .PDisk dpm → ∃ dp, p = .PDisk dp := fun dpm hpm => by
      obtain ⟨dpa, hpa⟩ := hkm dpm hpm
      exact hka dpa hpa
    obtain ⟨hqm2, hkm2⟩ := WeakRvwmoFab.quietAdm _ _ _ _ _ _ har2' hqm
      (fun dpm hpm kd ba bs sa sv hin => by
        obtain ⟨dp, hp⟩ := hkm' dpm hpm
        exact hdk2 dp hp kd ba bs sa sv (List.mem_append_left _ hin))
    have hkm2' : ∀ dpm, pm2 = .PDisk dpm → ∃ dp, p = .PDisk dp := fun dpm hpm => by
      obtain ⟨dpm1, hpm1⟩ := hkm2 dpm hpm
      exact hkm' dpm1 hpm1
    obtain ⟨hq', hk'⟩ := WeakRvwmoFab.quietStep _ _ _ _ _ hst2 hqm2 (fun dpm hpm kd ba bs sa sv he => by
      obtain ⟨dp, hp⟩ := hkm2' dpm hpm
      exact hdk2 dp hp kd ba bs sa sv (List.mem_append_right _ (by rw [he]; exact List.mem_cons_self)))
    cases n with
    | zero =>
      rw [Nat.zero_add] at hnd ⊢
      rw [emDevTagEq, emDevTagEq] at hnd
      obtain ⟨hnd1, hnd2⟩ := orbFalseSplit _ _ hnd
      obtain ⟨hls1, hl1⟩ := orbFalseSplit _ _ hnd1
      obtain ⟨_, hls1'⟩ := orbFalseSplit _ _ hls1
      obtain ⟨hnd3, _⟩ := orbFalseSplit _ _ hnd2
      obtain ⟨hls2, hl2⟩ := orbFalseSplit _ _ hnd3
      obtain ⟨_, hls2'⟩ := orbFalseSplit _ _ hls2
      have hb1 := WeakRvwmoFab.admRunTFalse _ _ _ _ _ _ _ har1 hdq (hasDevFalse ls1 hls1')
      have hp1 := pdevEvFalse pa l1 pm hqa (lbIsdevNe l1 hl1)
      have hb2 := WeakRvwmoFab.admRunTFalse _ _ _ _ _ _ _ har2 hqm (hasDevFalse ls2 hls2')
      have hp2 := pdevEvFalse pm2 l2 p' hqm2 (lbIsdevNe l2 hl2)
      simp only [htq, hb1, hp1, hb2, hp2, Bool.or_self]
    | succ n =>
      have e : n + 1 + k = n + (k + 1) := by omega
      rw [e] at hnd ⊢
      rw [emDevTagNe false ls1 l1 k (n + (k + 1)) _ (by omega),
        emDevTagNe false ls2 l2 k (n + (k + 1)) es (by omega)] at hnd
      exact ih ⟨hq', fun dp' hp' kd ba bs sa sv hin => by
          obtain ⟨dpm, hpm⟩ := hk' dp' hp'
          obtain ⟨dp, hp⟩ := hkm2' dpm hpm
          exact hdk2 dp hp kd ba bs sa sv (List.mem_append_right _ (List.mem_cons_of_mem _ hin))⟩ n
        (by simp only [List.length_cons] at hn; omega) hnd

/-! ### 3.3 The obstruction, machine-checked -/

theorem hartConfNoGap (i : Nat) (row : List Lbl) (p0 : Pexv6) (dv : Nat → Efab)
    (em : Hemission) (n : Nat) (lb : Lbl) :
    hartConf i row p0 dv em →
    devQuiet p0 ∧ (∀ dp, p0 = .PDisk dp → ∀ kd ba bs sa sv, LDev kd ba bs sa sv ∉ emLabels em) →
    row[n]? = some lb → ¬ isDevBlock em n → dv (n + 1) = dv n := by
  intro hem hdq hn hnd
  obtain ⟨tq, hemf⟩ := hartConfHemitf i row p0 dv em hem
  obtain ⟨_, _, hf⟩ := hartConffStates i row p0 dv (fun m => dv (m + 1)) tq em hemf
  have htq : tq n = false :=
    WeakRvwmoFab.hemitfQuietTq _ _ _ _ _ _ _ _ _ hemf hdq n (lookup_lt_Some hn)
      (Bool.eq_false_iff.2 hnd)
  exact ((hf n lb hn).2 htq).1

/-! ## 4. The bundle -/

structure Gfexec where
  GFExec ::
  gfGd : Gdexec
  gfDev : List Geid

/-- An I/O-class event (`Lbl.LIo`, any kind).  (W13 (I): moved here from `GraphFabResidue`, whose
residue still uses it, so that the bundle's membership clause can name it.) -/
def gisIo (G : Gexec) (e : Geid) : Bool :=
  match gxLbl G e with
  | some l => lbIsIo l
  | none => false

/-- (Lean-only, W13 (I)) `gisIo` read off a row. -/
theorem WeakRvwmoFab.gisIoRow (G : Gexec) (i k : Nat) (row : List Lbl) (lb : Lbl) :
    G.gxProg[i]? = some row → row[k]? = some lb → gisIo G (i, k) = lbIsIo lb := by
  intro hrow hlb
  unfold gisIo gxLbl
  rw [hrow]
  simp only [Option.bind_some, hlb]

/-- **THE FETCH CLAUSE** (`xv6ConfS`'s `emZifencei`, §A(†); W5d-G G1, deviation 6): every
administrative fetch item of hart `i`'s emission satisfies the trusted-base item `gzFetch`
(readings (H1)–(H3), (Z2) in E1′ form; `Weak/GraphFetchSpike.lean`) at its REAL slot tag
`GraphFetchSpike.emSlot` [OWN.26], with the fence.i contributors of the emission's sites
`emFenceI em` (D40 [OWN.15], D41 (a) [OWN.16]).  It is the slot of the Zifencei bundle
`gfexecConfZ`; the pinned bundle `gfexecConfIO` carries the stage-C `emFetchImg` (D43 (a)). -/
def emZifencei (G : Gexec) (i : Nat) (em : Hemission) : Prop := GraphFetch.emZif G i em

/-- **THE FABRIC BUNDLE `gfexecConfIO`** (W13 (I), deviation 5; Rocq's `gfexec_conf` with its
`isDevBlock` clause replaced and W-DISK's interim disk-row clause deleted).

Per row: an emission `em` with the blocks' fabric endpoints `dvi k → dvo k` and CONTACT bits
`tq k` (`hartConff`), and

* **MEMBERSHIP BY FABRIC CONTACT [OWN.43]** (superseding [R22.2]'s two-disjunct form):
  `(i, k) ∈ gfDev ↔ gisIo (i, k) ∨ dvi k ≠ dvo k ∨ tq k` -- every I/O-class event BY CLASS (its
  value depends on the fabric at its position even when it moves nothing), every block that MOVES
  the fabric, and every block with a `pdevEv`-true step (a block that READS the fabric without
  moving it, e.g. a disk `DWriteDev` store at an identity guard, is a member).  Hence every
  NON-member block is `pdevEv`-quiet, so fabric-preserving AND fabric-BLIND
  (`WeakEvInst.pdevEvOk`) -- which is what `supplyOfFconf`'s replay at the global fabric
  `fab ∘ dcnt` needs (`fconfRowsPin`);
* the members' endpoints pinned to the global fabric trace `fab` in `gfDev`'s order;
* the PINNED fetch clause `emFetchImg` (the stage-C clause: every fetch item reads the image at
  timestamp 0) -- D43 (a): the M1 kernel-text instance, kept for the pinned supply until G6; the
  Zifencei bundle is `gfexecConfZ` (deviation 6);
* the row's dependency edges in `gdDeps`.

TRUSTED-SURFACE MARKS (§A(†), rev 35).  RVWMO / riscv.cat / Sail have NO device-internal events;
Zifencei and the PMAs are silent; virtio 1.x says nothing about when the device re-reads its
state.  `gfDev` and (R1)–(R3) are device-MODEL / trusted-surface text (D45/D49 class), and no ISA
order is at stake: the contact criterion is FAITHFUL to RVWMO (it adds no ISA order), EQUAL to
[R22.2] on every xv6 run, and STRONGER than [R22.2] as generic trusted text only by unreachable
non-moving fabric-touching blocks, which (R3) then orders (`PROGRESS-W13I.md`; plan §D
Q-GFDEV-contact). -/
def gfexecConfIO (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (GF : Gfexec) :
    Prop :=
  fab 0 = d0 ∧
  GF.gfDev.Nodup ∧
  (∀ (n i k : Nat), GF.gfDev[n]? = some (i, k) →
     ∃ row, GF.gfGd.gdG.gxProg[i]? = some row ∧ k < row.length) ∧
  (∀ (i : Nat) (row : List Lbl), GF.gfGd.gdG.gxProg[i]? = some row →
     ∃ (em : Hemission) (dvi dvo : Nat → Efab) (tq : Nat → Bool),
       hartConff i row (boot i) dvi dvo tq em ∧
       (∀ k : Nat, k < row.length →
          ((i, k) ∈ GF.gfDev ↔ (gisIo GF.gfGd.gdG (i, k) = true ∨ dvi k ≠ dvo k ∨ tq k = true))) ∧
       (∀ (k n : Nat), GF.gfDev[n]? = some (i, k) → dvi k = fab n ∧ dvo k = fab (n + 1)) ∧
       emFetchImg GF.gfGd.gdG.gxImg em ∧
       (∀ jk, jk ∈ rowDeps em.emItems → ((i, jk.1), (i, jk.2)) ∈ GF.gfGd.gdDeps))

/-- **THE ZIFENCEI FABRIC BUNDLE `gfexecConfZ`** (W5d-G G1, deviation 6): `gfexecConfIO`'s text
with the fetch clause `emZifencei GF.gfGd.gdG i em` (the trusted-base item `gzFetch` at every
administrative fetch item, real slot tag, emission fence.i contributors) in place of the pinned
`emFetchImg` -- UNPINNED: a fetch may read any write the Zifencei reading allows.  `xv6ConfS`'s
fabric half (W13 (W)); the fetch fragment `F_em ⊆ gdFetch` joins at G3. -/
def gfexecConfZ (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (GF : Gfexec) :
    Prop :=
  fab 0 = d0 ∧
  GF.gfDev.Nodup ∧
  (∀ (n i k : Nat), GF.gfDev[n]? = some (i, k) →
     ∃ row, GF.gfGd.gdG.gxProg[i]? = some row ∧ k < row.length) ∧
  (∀ (i : Nat) (row : List Lbl), GF.gfGd.gdG.gxProg[i]? = some row →
     ∃ (em : Hemission) (dvi dvo : Nat → Efab) (tq : Nat → Bool),
       hartConff i row (boot i) dvi dvo tq em ∧
       (∀ k : Nat, k < row.length →
          ((i, k) ∈ GF.gfDev ↔ (gisIo GF.gfGd.gdG (i, k) = true ∨ dvi k ≠ dvo k ∨ tq k = true))) ∧
       (∀ (k n : Nat), GF.gfDev[n]? = some (i, k) → dvi k = fab n ∧ dvo k = fab (n + 1)) ∧
       emZifencei GF.gfGd.gdG i em ∧
       (∀ jk, jk ∈ rowDeps em.emItems → ((i, jk.1), (i, jk.2)) ∈ GF.gfGd.gdDeps))

/-- A pinned bundle is a Zifencei bundle once every row's pinned emission satisfies the slot
(deviation 6; the two share every other clause). -/
theorem gfexecConfZOfIO (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (GF : Gfexec) :
    gfexecConfIO boot d0 fab GF →
    (∀ (i : Nat) (row : List Lbl) (em : Hemission) (dvi dvo : Nat → Efab) (tq : Nat → Bool),
      GF.gfGd.gdG.gxProg[i]? = some row → hartConff i row (boot i) dvi dvo tq em →
      emFetchImg GF.gfGd.gdG.gxImg em → emZifencei GF.gfGd.gdG i em) →
    gfexecConfZ boot d0 fab GF := by
  rintro ⟨h0, hnd, hbnd, hc⟩ hz
  refine ⟨h0, hnd, hbnd, fun i row hrow => ?_⟩
  obtain ⟨em, dvi, dvo, tq, hem, hiff, hpin, hfi, hdep⟩ := hc i row hrow
  exact ⟨em, dvi, dvo, tq, hem, hiff, hpin, hz i row em dvi dvo tq hrow hem hfi, hdep⟩

/-- THE KERNEL-TEXT INSTANCE at the bundle (D43 (a)): a pinned bundle whose rows' fetched bytes
the graph never writes is a Zifencei bundle (`GraphFetch.emZifOfPinC`). -/
theorem gfexecConfZOfText (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (GF : Gfexec) :
    gfexecConfIO boot d0 fab GF →
    (∀ (i : Nat) (row : List Lbl) (em : Hemission) (dvi dvo : Nat → Efab) (tq : Nat → Bool),
      GF.gfGd.gdG.gxProg[i]? = some row → hartConff i row (boot i) dvi dvo tq em →
      GraphFetch.emFetchUnwritten GF.gfGd.gdG em) →
    gfexecConfZ boot d0 fab GF :=
  fun hc hnw => gfexecConfZOfIO boot d0 fab GF hc
    (fun i row em dvi dvo tq hrow hem hfi =>
      GraphFetch.emZifOfPinC _ i em hfi (hnw i row em dvi dvo tq hrow hem))

/-- A graph that writes no byte at all (e.g. a kernel-boot prefix up to the first store)
satisfies every row's unwritten-fetch condition. -/
theorem gfexecConfZOfNoWrite (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (GF : Gfexec) :
    gfexecConfIO boot d0 fab GF →
    (∀ w a v, ¬ gwritesByte GF.gfGd.gdG w a v) →
    gfexecConfZ boot d0 fab GF :=
  fun hc hnw => gfexecConfZOfText boot d0 fab GF hc
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ w v => hnw w _ v)

/-! ## 5. The model arm -/

def gdevAdj (GF : Gfexec) (a b : Geid) : Prop :=
  ∃ n, GF.gfDev[n]? = some a ∧ GF.gfDev[n + 1]? = some b

def gfexecConsistent (GF : Gfexec) : Prop :=
  rvwmoMinusDepsConsistent GF.gfGd ∧
  (∀ a b, gdevAdj GF a b → gmoLt GF.gfGd.gdG a b)

def racyF (GF : Gfexec) (x y : Geid) : Prop :=
  racyD GF.gfGd x y ∨ gdevAdj GF x y

theorem WeakRvwmoFab.rfGmo (GF : Gfexec) (x y : Geid) :
    gfexecConsistent GF → grule14 GF.gfGd.gdG → racyF GF x y → gmoLt GF.gfGd.gdG x y := by
  rintro ⟨hc, hdev⟩ h14 (hR | hd)
  · exact rdGmo _ x y hc h14 hR
  · exact hdev x y hd

theorem tcRfGmo (GF : Gfexec) (x y : Geid) :
    gfexecConsistent GF → grule14 GF.gfGd.gdG → tc (racyF GF) x y → gmoLt GF.gfGd.gdG x y := by
  intro hc h14 htc
  induction htc with
  | single h => exact WeakRvwmoFab.rfGmo GF _ _ hc h14 h
  | tail _ h ih => exact gmoLtTrans _ _ _ _ ih (WeakRvwmoFab.rfGmo GF _ _ hc h14 h)

theorem rfAcyclic (GF : Gfexec) (x : Geid) :
    gfexecConsistent GF → grule14 GF.gfGd.gdG → tc (racyF GF) x x → False :=
  fun hc h14 htc => gmoLtIrrefl _ _ (tcRfGmo GF x x hc h14 htc)

/-! ### 5.1 Decidability: bounded search over `gfDev` -/

instance gdevAdjDec (GF : Gfexec) (a b : Geid) : Decidable (gdevAdj GF a b) :=
  decidable_of_iff (∃ n ∈ List.range GF.gfDev.length,
      GF.gfDev[n]? = some a ∧ GF.gfDev[n + 1]? = some b)
    ⟨fun ⟨n, _, h⟩ => ⟨n, h⟩,
     fun ⟨n, h1, h2⟩ => ⟨n, List.mem_range.2 (lookup_lt_Some h1), h1, h2⟩⟩

instance racyFDec (GF : Gfexec) (x y : Geid) : Decidable (racyF GF x y) :=
  inferInstanceAs (Decidable (racyD GF.gfGd x y ∨ gdevAdj GF x y))

/-! ### 5.2 Linear extensions -/

def linExtF (GF : Gfexec) (L : List Geid) : Prop :=
  L.Perm GF.gfGd.gdG.gxGmo ∧ ∀ x y, racyF GF x y → before L x y

theorem linExtFLinExtD (GF : Gfexec) (L : List Geid) : linExtF GF L → linExtD GF.gfGd L := by
  rintro ⟨hL, hord⟩
  exact ⟨hL, fun x y hR => hord x y (.inl hR)⟩

/-- `topoLinearizes` applies VERBATIM — the fabric arm only strengthens the hypothesis. -/
theorem topoLinearizesF (GF : Gfexec) (L : List Geid) :
    rvwmoCoreD GF.gfGd → linExtF GF L →
    rvwmoMinusDepsConsistent ⟨retime GF.gfGd.gdG L, GF.gfGd.gdDeps, GF.gfGd.gdFetch⟩ ∧
    grule14 (retime GF.gfGd.gdG L) ∧
    rowsRel (tren GF.gfGd.gdG L) GF.gfGd.gdG (retime GF.gfGd.gdG L) ∧
    wperm (tren GF.gfGd.gdG L) GF.gfGd.gdG (retime GF.gfGd.gdG L) :=
  fun hc hlin => topoLinearizes GF.gfGd L hc (linExtFLinExtD GF L hlin)

theorem beforeTrans {A : Type _} (L : List A) (x y z : A) :
    L.Nodup → before L x y → before L y z → before L x z := by
  rintro hnd ⟨i, j, hi, hj, hij⟩ ⟨i', j', hi', hj', hij'⟩
  have hji : j = i' := NoDup_lookup hnd hj hi'
  exact ⟨i, j', hi, hj', by omega⟩

theorem linExtFNodup (GF : Gfexec) (L : List Geid) :
    gfexecConsistent GF → linExtF GF L → L.Nodup := by
  rintro ⟨hc, _⟩ ⟨hL, _⟩
  exact hL.nodup_iff.2 hc.1.1.1

/-- THE NEW CONTENT: a linear extension of `racyF` ORDERS the fabric list. -/
theorem linExtFDevBefore (GF : Gfexec) (L : List Geid) (m n : Nat) (e e' : Geid) :
    gfexecConsistent GF → linExtF GF L → m < n →
    GF.gfDev[m]? = some e → GF.gfDev[n]? = some e' → before L e e' := by
  intro hc hlin hlt hm hn
  have hnd : L.Nodup := linExtFNodup GF L hc hlin
  have key : ∀ d m e, m + 1 + d = n → GF.gfDev[m]? = some e → before L e e' := by
    intro d
    induction d with
    | zero =>
      intro m e hmn hm
      have : n = m + 1 := by omega
      subst this
      exact hlin.2 _ _ (.inr ⟨m, hm, hn⟩)
    | succ d ih =>
      intro m e hmn hm
      obtain ⟨e2, he2⟩ : ∃ e2, GF.gfDev[m + 1]? = some e2 :=
        ⟨_, List.getElem?_eq_getElem (by have := lookup_lt_Some hn; omega)⟩
      exact beforeTrans L e e2 e' hnd (hlin.2 _ _ (.inr ⟨m, hm, he2⟩))
        (ih (m + 1) e2 (by omega) he2)
  exact key (n - (m + 1)) m e (by omega) hm

/-! ### 5.3 Existence -/

theorem racyFMem (GF : Gfexec) (x y : Geid) :
    gfexecConsistent GF → racyF GF x y → x ∈ GF.gfGd.gdG.gxGmo ∧ y ∈ GF.gfGd.gdG.gxGmo := by
  rintro ⟨hc, hdev⟩ (hR | hd)
  · exact racyDMem _ x y hc hR
  · obtain ⟨hx, hy, _⟩ := hdev x y hd
    exact ⟨hx, hy⟩

theorem topoExistsF (GF : Gfexec) :
    gfexecConsistent GF → (∀ x, ¬ tc (racyF GF) x x) → ∃ L, linExtF GF L := by
  intro hc hacy
  have hnd : GF.gfGd.gdG.gxGmo.Nodup := hc.1.1.1.1
  obtain ⟨L, hL, hord⟩ := topoSortExists (racyF GF) (fun x y => racyFDec GF x y) hacy _ hnd
  refine ⟨L, hL, fun x y hR => ?_⟩
  obtain ⟨hx, hy⟩ := racyFMem GF x y hc hR
  exact hord x y hx hy hR

/-! ## 6. Non-vacuity: B1b-1's bundle embeds -/

/-- (W13 (I), deviation 5: at QUIET boot states -- a quiescent emission from a disk state inside
a burst can touch the fabric with no `LDev`, and then the empty fabric list is not the contact
list.) -/
theorem gfexecConfOfQconf (boot : Nat → Pexv6) (d0 : Efab) (im : Image) (nh : Nat)
    (GD : Gdexec) :
    gdexecQconf boot d0 im nh GD → (∀ i, devQuiet (boot i)) →
    gfexecConfIO boot d0 (fun _ => d0) ⟨GD, []⟩ := by
  intro hq0 hquiet
  have hq := gdexecQconfRows _ _ _ _ _ hq0
  refine ⟨rfl, List.nodup_nil, fun n i k hn => by simp at hn, ?_⟩
  intro i row hrow
  obtain ⟨em, hem, hdf, hfi, hdep⟩ := hq i row hrow
  obtain ⟨tq, hemf⟩ := hartConfHemitf i row (boot i) (fun _ => d0) em hem
  refine ⟨em, fun _ => d0, fun _ => d0, tq, hemf, ?_, fun k n hn => by simp at hn,
    by rw [gdexecQconfImg _ _ _ _ _ hq0]; exact hfi, hdep⟩
  intro k hk
  have htq : tq k = false :=
    WeakRvwmoFab.hemitfQuietTq _ _ _ _ _ _ _ _ _ hemf ⟨hquiet i, fun _ _ => hdf⟩ k hk
      (emDevDevfree k em.emItems hdf)
  obtain ⟨_, _, hf⟩ := hartConffStates i row (boot i) _ _ tq em hemf
  obtain ⟨lb, hlb⟩ : ∃ lb, row[k]? = some lb := ⟨_, List.getElem?_eq_getElem hk⟩
  have hgio : gisIo GD.gdG (i, k) = false := by
    rw [WeakRvwmoFab.gisIoRow GD.gdG i k row lb hrow hlb]
    exact ((hf k lb hlb).2 htq).2.1
  constructor
  · intro hin; simp at hin
  · rintro (h | h | h)
    · rw [hgio] at h; exact absurd h (by decide)
    · exact absurd rfl h
    · rw [htq] at h; exact absurd h (by decide)

/-! ## 7. The supply at a moving fabric -/

def dstepAt (GF : Gfexec) (tr : List Estep) (j : Nat) : Bool :=
  match tr[j]? with
  | some s => decide ((s.esAg, tcnt s.esAg (tr.take j)) ∈ GF.gfDev)
  | none => false

def dcnt (GF : Gfexec) (tr : List Estep) (k : Nat) : Nat :=
  match k with
  | 0 => 0
  | k' + 1 => dcnt GF tr k' + (if dstepAt GF tr k' then 1 else 0)

theorem dcnt0 (GF : Gfexec) (tr : List Estep) : dcnt GF tr 0 = 0 := rfl

theorem dcntStepDev (GF : Gfexec) (tr : List Estep) (k : Nat) :
    dstepAt GF tr k = true → dcnt GF tr (k + 1) = dcnt GF tr k + 1 := by
  intro h
  simp [dcnt, h]

theorem dcntStepNe (GF : Gfexec) (tr : List Estep) (k : Nat) :
    dstepAt GF tr k = false → dcnt GF tr (k + 1) = dcnt GF tr k := by
  intro h
  simp [dcnt, h]

/-- THE INTERLEAVING THEOREM, at the fabric `fab ∘ dcnt`.  (Deviation 2: the blocks are at the
pinned LTS `pstepQ (WeakAxRealize.fetchPin im)`, and so is the supply.) -/
theorem supplyOfFconf (c : Cand) (boot : Nat → Pexv6) (fab : Nat → Efab) (GF : Gfexec)
    (rows : Nat → List Lbl) (N : Nat) (im : Image) :
    -- the trace is an interleaving of the rows ...
    (∀ i, (c.cdTr.filter (fun s => decide (s.esAg = i))).map (fun s => s.esLb) = rows i) →
    -- ... over the agents below `N` ...
    (∀ i, N ≤ i → rows i = []) →
    -- ... every row emits, its member blocks pinned to `fab`, its non-member blocks
    -- fabric-blind -- the `∀ d` folding (W13 (I): derived from CONTACT, `fconfRowsPin`)
    -- (Lean-only: its fetches pinned to `im`) ...
    (∀ i, i < N → ∃ f : Nat → Pexv6, f 0 = boot i ∧
       ∀ n lb, (rows i)[n]? = some lb →
         (∀ m, GF.gfDev[m]? = some (i, n) →
               hblkQ (WeakAxRealize.fetchPin im) (fab m) (fab (m + 1)) (rowWs (rows i) n) lb (f n) (f (n + 1)))
         ∧ ((i, n) ∉ GF.gfDev →
            ∀ d, hblkQ (WeakAxRealize.fetchPin im) d d (rowWs (rows i) n) lb (f n) (f (n + 1)))) →
    -- ... and the trace respects `gfDev`'s order.
    (∀ k s, c.cdTr[k]? = some s →
       (s.esAg, tcnt s.esAg (c.cdTr.take k)) ∈ GF.gfDev →
       GF.gfDev[dcnt GF c.cdTr k]? = some (s.esAg, tcnt s.esAg (c.cdTr.take k))) →
    ∃ pst : Nat → List Pexv6,
      pst 0 = (List.range' 0 N).map boot ∧
      execProgOk' (pstepPin im pstepEv) pclsEv pst (fun k => fab (dcnt GF c.cdTr k))
        (candExec c) := by
  intro hrows hbnd hch hord
  obtain ⟨F, hF⟩ := natBoundedChoice (fun _ => .PDisk none) _ N hch
  refine ⟨fun k => (List.range' 0 N).map (fun i => F i (tcnt i (c.cdTr.take k))), ?_, ?_⟩
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
    obtain ⟨hdev, hnodev⟩ := hfb _ _ hrow
    -- THE BLOCK, at the two GLOBAL fabric values
    have hblk' : hblkQ (WeakAxRealize.fetchPin im)
        (fab (dcnt GF c.cdTr k)) (fab (dcnt GF c.cdTr (k + 1)))
        (rowWs (rows s.esAg) (tcnt s.esAg (c.cdTr.take k))) s.esLb
        (F s.esAg (tcnt s.esAg (c.cdTr.take k)))
        (F s.esAg (tcnt s.esAg (c.cdTr.take k) + 1)) := by
      by_cases hin : (s.esAg, tcnt s.esAg (c.cdTr.take k)) ∈ GF.gfDev
      · have hda : dstepAt GF c.cdTr k = true := by
          unfold dstepAt; rw [hs]; exact decide_eq_true hin
        rw [dcntStepDev _ _ _ hda]
        exact hdev _ (hord k s hs hin)
      · have hda : dstepAt GF c.cdTr k = false := by
          unfold dstepAt; rw [hs]; exact decide_eq_false hin
        rw [dcntStepNe _ _ _ hda]
        exact hnodev hin _
    obtain ⟨pa, da, hstar, hdisj⟩ := hblk'
    have hrelp : ((stt (candExec c) k).msWs s.esAg).wRelp =
        (rowWs (rows s.esAg) (tcnt s.esAg (c.cdTr.take k))).wRelp := by
      rw [candWsRelp c _ k hklen]
      unfold trow
      rw [hrows]
    refine ⟨F s.esAg (tcnt s.esAg (c.cdTr.take k)), pa, da,
      F s.esAg (tcnt s.esAg (c.cdTr.take k) + 1), ?_, ?_, hstar, ?_⟩
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

/-! ### 7.1 The bundle supplies `supplyOfFconf`'s third hypothesis -/

/-- (Lean-only, deviation 2) `fconfRows` at the pinned LTS: the bundle's `emFetchImg` clause
pins the blocks to the graph's image.  (W13 (I), deviation 5: the non-member conjunct -- the
`∀ d` folding -- is DERIVED from contact: a non-member's contact bit is `false`.) -/
theorem fconfRowsPin (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (GF : Gfexec)
    (i : Nat) (row : List Lbl) :
    gfexecConfIO boot d0 fab GF →
    GF.gfGd.gdG.gxProg[i]? = some row →
    ∃ f : Nat → Pexv6, f 0 = boot i ∧
      ∀ n lb, row[n]? = some lb →
        (∀ m, GF.gfDev[m]? = some (i, n) →
              hblkQ (WeakAxRealize.fetchPin GF.gfGd.gdG.gxImg) (fab m) (fab (m + 1)) (rowWs row n) lb
                (f n) (f (n + 1)))
        ∧ ((i, n) ∉ GF.gfDev →
           ∀ d, hblkQ (WeakAxRealize.fetchPin GF.gfGd.gdG.gxImg) d d (rowWs row n) lb (f n) (f (n + 1))) := by
  rintro ⟨_, _, _, hc⟩ hrow
  obtain ⟨em, dvi, dvo, tq, hem, hiff, hpin, hfi, _⟩ := hc i row hrow
  obtain ⟨f, hf0, hf⟩ := hartConffStatesQ _ i row (boot i) dvi dvo tq em hem hfi
  refine ⟨f, hf0, fun n lb hn => ?_⟩
  obtain ⟨h1, h2⟩ := hf n lb hn
  refine ⟨fun m hm => ?_, fun hnin d => ?_⟩
  · obtain ⟨hi, ho⟩ := hpin n m hm
    rw [← hi, ← ho]; exact h1
  · have htq : tq n = false := by
      cases h : tq n with
      | false => rfl
      | true => exact absurd ((hiff n (lookup_lt_Some hn)).2 (Or.inr (Or.inr h))) hnin
    exact (h2 htq).2.2 d

theorem fconfRows (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (GF : Gfexec)
    (i : Nat) (row : List Lbl) :
    gfexecConfIO boot d0 fab GF →
    GF.gfGd.gdG.gxProg[i]? = some row →
    ∃ f : Nat → Pexv6, f 0 = boot i ∧
      ∀ n lb, row[n]? = some lb →
        (∀ m, GF.gfDev[m]? = some (i, n) →
              hblk (fab m) (fab (m + 1)) (rowWs row n) lb (f n) (f (n + 1)))
        ∧ ((i, n) ∉ GF.gfDev → ∀ d, hblk d d (rowWs row n) lb (f n) (f (n + 1))) := by
  intro hconf hrow
  obtain ⟨f, hf0, hf⟩ := fconfRowsPin boot d0 fab GF i row hconf hrow
  refine ⟨f, hf0, fun n lb hn => ?_⟩
  obtain ⟨h1, h2⟩ := hf n lb hn
  exact ⟨fun m hm => hblkQHblk _ _ _ _ _ _ _ (h1 m hm),
    fun hnin d => hblkQHblk _ _ _ _ _ _ _ (h2 hnin d)⟩

/-- THE COMPOSITION: a bundle plus a fabric-order-respecting interleaving of its rows IS an
`execProgOk'` supply (deviation 2: at the LTS pinned to the graph's image), and the run starts
at `d0`. -/
theorem fconfSupply (c : Cand) (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab)
    (GF : Gfexec) (N : Nat) :
    gfexecConfIO boot d0 fab GF →
    (∀ i, (c.cdTr.filter (fun s => decide (s.esAg = i))).map (fun s => s.esLb) =
        (GF.gfGd.gdG.gxProg[i]?).getD []) →
    GF.gfGd.gdG.gxProg.length ≤ N →
    (∀ k s, c.cdTr[k]? = some s →
       (s.esAg, tcnt s.esAg (c.cdTr.take k)) ∈ GF.gfDev →
       GF.gfDev[dcnt GF c.cdTr k]? = some (s.esAg, tcnt s.esAg (c.cdTr.take k))) →
    ∃ pst : Nat → List Pexv6,
      pst 0 = (List.range' 0 N).map boot ∧
      (fun k => fab (dcnt GF c.cdTr k)) 0 = d0 ∧
      execProgOk' (pstepPin GF.gfGd.gdG.gxImg pstepEv) pclsEv pst
        (fun k => fab (dcnt GF c.cdTr k)) (candExec c) := by
  intro hconf hrows hN hord
  obtain ⟨pst, hpst0, hprog⟩ := supplyOfFconf c boot fab GF
    (fun i => (GF.gfGd.gdG.gxProg[i]?).getD []) N GF.gfGd.gdG.gxImg hrows
    (fun i hi => progRowNil _ _ (by omega))
    (by
      intro i _
      cases e : GF.gfGd.gdG.gxProg[i]? with
      | some row =>
        obtain ⟨f, hf0, hf⟩ := fconfRowsPin boot d0 fab GF i row hconf e
        exact ⟨f, hf0, hf⟩
      | none =>
        refine ⟨fun _ => boot i, rfl, ?_⟩
        intro n lb hn
        simp at hn)
    hord
  exact ⟨pst, hpst0, hconf.1, hprog⟩

/-! ## 8. Hulls -/

def gfHull (GF : Gfexec) (cs : List Nat) : Gfexec :=
  ⟨gdHull GF.gfGd cs, GF.gfDev.filter (gcut cs)⟩

def dclosed (cs : List Nat) (l : List Geid) : Prop :=
  ∀ (m n : Nat) (e e' : Geid), m < n → l[m]? = some e → l[n]? = some e' → gcut cs e' = true → gcut cs e = true

theorem dclosedCons (cs : List Nat) (e : Geid) (l : List Geid) :
    dclosed cs (e :: l) → dclosed cs l := by
  intro h m n x y hlt hm hn hc
  exact h (m + 1) (n + 1) x y (by omega) hm hn hc

theorem filterNoneNil (l : List Geid) (cs : List Nat) :
    (∀ (n : Nat) (e : Geid), l[n]? = some e → gcut cs e = false) → l.filter (gcut cs) = [] := by
  induction l with
  | nil => intro _; rfl
  | cons e l ih =>
    intro h
    have he : gcut cs e = false := h 0 e rfl
    rw [List.filter_cons, he]
    exact ih (fun n x hx => h (n + 1) x hx)

/-- UNDER `dclosed` THE FILTERED FABRIC ORDER IS A PREFIX. -/
theorem dclosedPrefix (cs : List Nat) (l : List Geid) :
    dclosed cs l → l.filter (gcut cs) <+: l := by
  induction l with
  | nil => intro _; exact List.nil_prefix
  | cons e l ih =>
    intro hdc
    rw [List.filter_cons]
    cases he : gcut cs e with
    | true =>
      simp only [if_true]
      exact (List.prefix_cons_inj e).2 (ih (dclosedCons cs e l hdc))
    | false =>
      simp only [Bool.false_eq_true, if_false]
      rw [filterNoneNil l cs]
      · exact List.nil_prefix
      · intro n x hx
        cases hx' : gcut cs x with
        | false => rfl
        | true =>
          have := hdc 0 (n + 1) e x (by omega) rfl hx hx'
          rw [he] at this
          exact absurd this (by decide)

theorem gfHullDevLookup (GF : Gfexec) (cs : List Nat) (n : Nat) (e : Geid) :
    dclosed cs GF.gfDev → (gfHull GF cs).gfDev[n]? = some e → GF.gfDev[n]? = some e := by
  intro hdc hn
  obtain ⟨t, ht⟩ := dclosedPrefix cs GF.gfDev hdc
  rw [← ht]
  exact lookup_app_l_Some hn

theorem gfHullDevCut (GF : Gfexec) (cs : List Nat) (n : Nat) (e : Geid) :
    (gfHull GF cs).gfDev[n]? = some e → gcut cs e = true := by
  intro hn
  have hin : e ∈ GF.gfDev.filter (gcut cs) := elem_of_list_lookup_2 hn
  exact (List.mem_filter.1 hin).2

/-- CONSISTENCY RESTRICTS. -/
theorem gfHullConsistent (GF : Gfexec) (cs : List Nat) :
    gfexecConsistent GF → hullOk GF.gfGd.gdG cs → dclosed cs GF.gfDev →
    gfexecConsistent (gfHull GF cs) := by
  rintro ⟨hc, hdev⟩ hok hdc
  refine ⟨hullDepsConsistent _ cs hc hok, ?_⟩
  rintro a b ⟨n, ha, hb⟩
  have hca : gcut cs a = true := gfHullDevCut GF cs n a ha
  have hcb : gcut cs b = true := gfHullDevCut GF cs (n + 1) b hb
  have hmo : gmoLt GF.gfGd.gdG a b :=
    hdev a b ⟨n, gfHullDevLookup GF cs n a hdc ha, gfHullDevLookup GF cs (n + 1) b hdc hb⟩
  show gmoLt (gxHull GF.gfGd.gdG cs) a b
  exact (gxhGmoLt GF.gfGd.gdG cs a b hc.1.1.1).2 ⟨hca, hcb, hmo⟩

/- THE CONFORMANCE RESTRICTION and THE cycle_kill MIRROR are, as in Rocq §8, OBLIGATIONS recorded
in prose (O1: hemitf_prefix; O2: hemitf_ren, with emDevRen above; O3: emDev under an item prefix,
via tag monotonicity of hemitf; O4: the gfDev membership clause; O5: the fab clause, by
gfHullDevLookup).  Nothing is admitted. -/

end Weak
