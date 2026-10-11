/-
Weak: **B2e-3b slice 3c(a), part 2 — re-convergence after a witness, `certSegment''`,
non-vacuity** (Rocq §5, §5b, §6; §1–§4 are `WeakRvwmoCert3`).

Rocq: `iris/WeakRvwmoCert3.v` @ xxvzwolszwmp (the file split in two for elaboration time, as
planned; this half imports `Weak.WeakRvwmoCert3`).

## The Rocq header, in substance

§5 (obligation O-2): after a substituted read the certified run and the emission sit at
different monad nodes; they re-converge at the next instruction BOUNDARY, which is the CONSTANT
`.pure ()` of `SailM Unit` (`boundaryNodeConst`), and the boundary step is uniform
(`boundaryStepInv`/`boundaryStepExists`), so both runs take the same tick and are back in
lockstep off the grown taint set (`boundaryReconverge`/`boundaryReconvergeRun`, via
`WeakEvProv.taintClosureLoad`).  §5b integrates this into the segment iteration: the invariant
is `csync` — the same node (`clockstep`), OR both runs inside the SAME instruction's silent tail
(`tailSilent`, a structural property of the node; TERMINATION IS A THEOREM, `tailSilentRun`,
because `SailM` is inductive).  Between a witness and the next boundary there is no memory label
(`witnessInstrTailSilent`), so `csyncAdvance` re-establishes lockstep; `certSegment''` carries a
per-row-position taint `Tf`, a reachability parameter `Nd` (canonical instance `ndreach`), the
pair policy `cpolpr`, and the exit lock `segLocked`.  §6: the empty candidate is a certified
prefix (`ctracePrefixEmpty`, `cpolCtxEmpty`), the floor at a real first read
(`certFloorOkImage`), `certSegment'` on the real `sw &started` block
(`certSegment'Witness`/`certSegment'Nonvacuous`), and the boundary at `WeakEvProv.witM`
(`witMBoundary`, `boundaryReconvergeNonvacuous`).

## Deviations from Rocq

1. NAMES/TYPES as `WeakRvwmoCert3` deviation 1.  `Interface.Ret tt` ↦ `.pure ()`;
   `Interface.Next oc k` ↦ `.impure (.ok o) k` with `o : Outcome Register RegisterType`,
   `k : o.ret → SailM Unit` (Rocq's `A : Type` index is the outcome's own `ret`);
   `riscv_step` ↦ `riscvStep`; `ib_none` ↦ `ibNone`; `es.*1` ↦ `es.map Prod.fst`; `wit_m` ↦
   `witM`; `R_bitvector_64 x14` ↦ `.x14`; `T ⊆ T'` is `List.Subset`.
2. `ocSilent`'s twelve outcomes: `regRead`, `regWrite`, `branchAnnounce`, `cacheOp`, `tlbi`,
   `takeException`, `returnException`, `translationStart`, `translationEnd`, `cycleCount`,
   `message`, `getCycleCount` (Rocq's `TlbOp` ↦ `tlbi`; `choose` excluded, as Rocq).
3. THE NODE STEP's Lean shape (`WeakEvInst` deviations 4/5): `pnodeStep` takes a barrier report
   `obar` (quantified in `boundaryStepInv`/`ocSilentStep`, existential in
   `boundaryStepExists`/`ocSilentStepExists` (`none`)) and works over `DevStates` (`d.efDev`).
   `admStepNode` therefore returns `obar`, the node step at `d.efDev`/`d1.efDev` and the fabric
   equation `d1 = {d with efDev := d1.efDev}` (Rocq: `pnode_step … d … d1`); its PLIC arm is
   refuted by `l ≠ LDev`, as Rocq's.
4. O2 / STAGE C — THE PINNED LTS: `certSegment''`'s Stage-B `lbFetchInert` conjunct of `Hpol''`
   is DELETED; see deviation 8 for the pinned statements.
5. Rocq's `Section segment''` context (`x cpu d0 Tf Hmono Q Ctx Cls Hpres Nd Hrdsp HNdadm HNdblk
   HNdblkp Hpol'' Hpolp`) is `certSegment''`'s leading parameters in Rocq's order; Rocq's
   `Section nonvacuity3` (`cpu rs ib d0`) is `certSegment'Witness`'s parameters.
   `cert_segment'_nonvacuous`'s witnesses: CPU `⟨0, _⟩`, `evRs0`, `ibNone`,
   `efInit ⟨fun _ => default⟩` (as `WeakRvwmoCert2.certSegmentNonvacuous`).
6. `WeakRvwmoCert3.phrunApp`'s binders are implicit (statement unchanged).  Lean-only helper
   `WeakRvwmoCert3.phrunBoundary` (the one-step `[LInstr]` run at a tick, which Rocq builds
   inline in `boundary_reconverge_run` and `csync_advance`).
7. `wit_m_boundary`'s `vm_compute` and the `ereg_num` side goal are `rfl`/`decide`.
8. O2 / STAGE C — THE PINNED LTS (`WeakRvwmoCert2` deviation 4, `WeakRvwmoCert3` deviation 4).
   `certSegment''`: the supply at `pstepPin c.cdImg pstepEv` (premise and conclusion), the new
   premise `WeakRvwmoCert2.esPin c.cdImg es` (after `Ctx k0 c`), `Hpol''` takes and returns
   `WeakRvwmoCert2.cblkPin c0.cdImg` blocks, `cpolpr` takes and returns
   `WeakRvwmoCert3.cblkpPin c0.cdImg` blocks (`HNdblk`/`HNdblkp`/`Hrdsp` keep Rocq's unpinned
   blocks).  The certified block's re-convergence prefix needs its pins, so `tailSilentRun` gains
   the last conjunct `∀ l0 ∈ ls, ∀ im, WeakAxRealize.fetchPin im l0` (a silent tail never
   fetches: Lean-only `WeakRvwmoCert3b.ocSilentStepPin`) and `csyncAdvance` the two last
   conjuncts `∀ l0 ∈ lsc, l0 ∈ ls` and `∀ l0 ∈ lspre, ∀ im, WeakAxRealize.fetchPin im l0`.
   Lean-only transports `WeakRvwmoCert3b.cblkPreG` / `cblkpPreG` (Rocq's `cblkPre` / `cblkpPre`
   are their `lbAdmin true` instances).  `certSegment'Witness` / `certSegment'Nonvacuous`
   state the pinned supply (image `fun _ => none`).

**Rocq → Lean name map.**  `at_boundary` `WeakRvwmoCert3.atBoundary`, `at_boundary_ret`
`atBoundaryRet`, `boundary_node_const` `boundaryNodeConst`, `boundary_step_inv`
`boundaryStepInv`, `boundary_step_exists` `boundaryStepExists`, `boundary_reconverge`
`boundaryReconverge`, `boundary_reconverge_run` `boundaryReconvergeRun`, `oc_silent`
`ocSilent`, `tail_silent` `tailSilent` (`ts_ret`/`ts_next` ↦ `tsRet`/`tsNext`),
`oc_silent_step` `ocSilentStep`, `oc_silent_step_exists` `ocSilentStepExists`,
`tail_silent_run` `tailSilentRun`, `adm_step_node` `admStepNode`, `tail_silent_adm`
`tailSilentAdm`, `tail_silent_no_label` `tailSilentNoLabel`, `witness_instr_tail_silent`
`witnessInstrTailSilent`, `phrun_app` `WeakRvwmoCert3.phrunApp`, `cblk_pre` `cblkPre`,
`clockstep` `clockstep`, `csync` `csync`, `dreg_agree_taint_mono` `dregAgreeTaintMono`,
`rds_ok_taint_mono` `rdsOkTaintMono`, `tail_silent_mono` `tailSilentMono`, `clockstep_mono`
`clockstepMono`, `csync_mono` `csyncMono`, `boundary_step_tick` `boundaryStepTick`,
`csync_advance` `csyncAdvance`, `cblkp_pre` `cblkpPre`, `cpolpr` `cpolpr`, `cpolpr_of_cpolp`
`cpolprOfCpolp`, `ndreach` `ndreach` (`nd_start`/`nd_adm`/`nd_blk`/`nd_blkp` ↦
`ndStart`/`ndAdm`/`ndBlk`/`ndBlkp`), `lastlb` `lastlb`, `seg_locked` `segLocked`,
`lastlb_cons` `lastlbCons`, `seg_locked_cons` `segLockedCons`, `lastlb_app_single`
`lastlbAppSingle`, `seg_locked_snoc` `segLockedSnoc`, `csync_regs` `csyncRegs`,
`hlbl_realizes_pair_notadm` `hlblRealizesPairNotadm`, `cert_segment''` `certSegment''`,
`ctrace_prefix_empty` `ctracePrefixEmpty`, `wit_fence_ub_empty` `witFenceUbEmpty`,
`pois_ok_at_empty` `poisOkAtEmpty`, `pois_ok_hart_empty` `poisOkHartEmpty`, `cpol_ctx_empty`
`cpolCtxEmpty`, `cert_floor_ok_image` `certFloorOkImage`, `cert_segment'_witness`
`certSegment'Witness`, `cert_segment'_nonvacuous` `certSegment'Nonvacuous`, `wit_m_boundary`
`witMBoundary`, `boundary_reconverge_nonvacuous` `boundaryReconvergeNonvacuous`.

**File-qualified names:** `WeakRvwmoCert3.atBoundary`, `WeakRvwmoCert3.phrunApp` (in
`notes/weak-port-dupnames.json`); Lean-only helpers `WeakRvwmoCert3.phrunBoundary`,
`WeakRvwmoCert3b.ocSilentStepPin`, `WeakRvwmoCert3b.cblkPreG`, `WeakRvwmoCert3b.cblkpPreG`.

**Dropped:** none (Rocq §5–§6: 50 declarations + the `img0` notation, which is the literal
`fun _ => none`; Lean 50 + 1 helper).
-/
import Weak.WeakRvwmoCert3

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D
open Wlabel

/-- The parked-fence field, abbreviated (as in `WeakRvwmoCert2`). -/
local notation "Ofence" => Option (Bool × Bool × Bool × Bool)

/-! # 5. OBLIGATION (O-2): RE-CONVERGENCE AFTER A WITNESS -/

def WeakRvwmoCert3.atBoundary (m : SailM Unit) : Prop := ∃ y : Unit, m = .pure y

theorem atBoundaryRet : WeakRvwmoCert3.atBoundary (.pure ()) := ⟨(), rfl⟩

/-- THE BOUNDARY CONTINUATION IS A CONSTANT. -/
theorem boundaryNodeConst (m1 m2 : SailM Unit) :
    WeakRvwmoCert3.atBoundary m1 → WeakRvwmoCert3.atBoundary m2 → m1 = m2 := by
  rintro ⟨⟨⟩, rfl⟩ ⟨⟨⟩, rfl⟩
  rfl

/-- Every boundary step has the same shape ... -/
theorem boundaryStepInv (m : SailM Unit) (rs : RegFile) (ib : Ibch) (d : DevStates) (l : Wlabel)
    (m' : SailM Unit) (ors : Option RegFile) (fn' : Ofence) (d' : DevStates) (oib : Option Ibch)
    (obar : Option barrier_kind) :
    WeakRvwmoCert3.atBoundary m →
    pnodeStep m rs ib d l m' ors fn' d' oib obar →
    ∃ tick : Bool, l = LInstr ∧ m' = riscvStep tick ∧ ors = none ∧ fn' = none ∧ d' = d ∧
      oib = some ibNone := by
  rintro ⟨⟨⟩, rfl⟩ ⟨tick, h1, h2, h3, h4, h5, h6, _⟩
  exact ⟨tick, h1, h2, h3, h4, h5, h6⟩

/-- ... and it always exists, at any register file, channel and fabric. -/
theorem boundaryStepExists (m : SailM Unit) (rs : RegFile) (ib : Ibch) (d : DevStates) :
    WeakRvwmoCert3.atBoundary m →
    pnodeStep m rs ib d LInstr (riscvStep true) none none d (some ibNone) none := by
  rintro ⟨⟨⟩, rfl⟩
  exact ⟨true, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- THE RE-CONVERGENCE. -/
theorem boundaryReconverge (T : List Nat) (rd : Nat)
    (cpu1 : CPU) (ls1 : List Wlabel) (rds1 : List Nat) (wrs1 : List Register) (ann1 : Bool)
    (m1 : SailM Unit) (rs1 : RegFile) (fn1 : Ofence) (ib1 : Ibch) (d1 : Efab)
    (m1' : SailM Unit) (rs1' : RegFile) (fn1' : Ofence) (ib1' : Ibch) (d1' : Efab)
    (cpu2 : CPU) (ls2 : List Wlabel) (rds2 : List Nat) (wrs2 : List Register) (ann2 : Bool)
    (m2 : SailM Unit) (rs2 : RegFile) (fn2 : Ofence) (ib2 : Ibch) (d2 : Efab)
    (m2' : SailM Unit) (rs2' : RegFile) (fn2' : Ofence) (ib2' : Ibch) (d2' : Efab) :
    dregAgree (fun n => n ∉ T) rs1 rs2 →
    phrun cpu1 ls1 rds1 wrs1 ann1 m1 rs1 fn1 ib1 d1 m1' rs1' fn1' ib1' d1' →
    phrun cpu2 ls2 rds2 wrs2 ann2 m2 rs2 fn2 ib2 d2 m2' rs2' fn2' ib2' d2' →
    (∀ r, r ∈ wrs1 ++ wrs2 → ∃ n, eregNum r = some n ∧ n ∈ rd :: T) →
    WeakRvwmoCert3.atBoundary m1' → WeakRvwmoCert3.atBoundary m2' →
    m1' = m2' ∧ dregAgree (fun n => n ∉ rd :: T) rs1' rs2' := by
  intro hag hr1 hr2 hws hb1 hb2
  exact ⟨boundaryNodeConst _ _ hb1 hb2,
    taintClosureLoad T rd cpu1 ls1 rds1 wrs1 ann1 m1 rs1 fn1 ib1 d1 m1' rs1' fn1' ib1' d1'
      cpu2 ls2 rds2 wrs2 ann2 m2 rs2 fn2 ib2 d2 m2' rs2' fn2' ib2' d2' hag hr1 hr2 hws⟩

/-- (Lean-only) The one-step boundary run, at any tick (Rocq builds it inline). -/
theorem WeakRvwmoCert3.phrunBoundary (cpu : CPU) (rs : RegFile) (ib : Ibch) (d : Efab)
    (tick : Bool) :
    phrun cpu [LInstr] [] [] true (.pure ()) rs none ib d (riscvStep tick) rs none ibNone d :=
  phrun.more (rds := []) (rds' := []) (ws := []) (ws' := []) (ann := true) (ann' := false)
    (ors := none) (oib := some ibNone) (obar := none) (d1 := d)
    (Or.inl ⟨rfl, ⟨⟨tick, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl⟩, rfl, rfl, rfl⟩)
    (phrun.nil _ _ _ _ _)

/-- ... and the step that puts the two runs back in lockstep. -/
theorem boundaryReconvergeRun (T : List Nat) (rd : Nat)
    (cpu1 : CPU) (ls1 : List Wlabel) (rds1 : List Nat) (wrs1 : List Register) (ann1 : Bool)
    (m1 : SailM Unit) (rs1 : RegFile) (fn1 : Ofence) (ib1 : Ibch) (d1 : Efab)
    (m1' : SailM Unit) (rs1' : RegFile) (ib1' : Ibch) (d1' : Efab)
    (cpu2 : CPU) (ls2 : List Wlabel) (rds2 : List Nat) (wrs2 : List Register) (ann2 : Bool)
    (m2 : SailM Unit) (rs2 : RegFile) (fn2 : Ofence) (ib2 : Ibch) (d2 : Efab)
    (m2' : SailM Unit) (rs2' : RegFile) (ib2' : Ibch) (d2' : Efab) :
    dregAgree (fun n => n ∉ T) rs1 rs2 →
    phrun cpu1 ls1 rds1 wrs1 ann1 m1 rs1 fn1 ib1 d1 m1' rs1' none ib1' d1' →
    phrun cpu2 ls2 rds2 wrs2 ann2 m2 rs2 fn2 ib2 d2 m2' rs2' none ib2' d2' →
    (∀ r, r ∈ wrs1 ++ wrs2 → ∃ n, eregNum r = some n ∧ n ∈ rd :: T) →
    WeakRvwmoCert3.atBoundary m1' → WeakRvwmoCert3.atBoundary m2' →
    ∃ (m0 : SailM Unit) (rdsA : List Nat) (wrsA : List Register) (annA : Bool)
      (rdsB : List Nat) (wrsB : List Register) (annB : Bool),
      phrun cpu1 [LInstr] rdsA wrsA annA m1' rs1' none ib1' d1' m0 rs1' none ibNone d1' ∧
      phrun cpu2 [LInstr] rdsB wrsB annB m2' rs2' none ib2' d2' m0 rs2' none ibNone d2' ∧
      dregAgree (fun n => n ∉ rd :: T) rs1' rs2' := by
  intro hag hr1 hr2 hws hb1 hb2
  obtain ⟨_, hag'⟩ := boundaryReconverge T rd cpu1 ls1 rds1 wrs1 ann1 m1 rs1 fn1 ib1 d1 m1' rs1'
    none ib1' d1' cpu2 ls2 rds2 wrs2 ann2 m2 rs2 fn2 ib2 d2 m2' rs2' none ib2' d2' hag hr1 hr2 hws
    hb1 hb2
  obtain ⟨⟨⟩, rfl⟩ := hb1
  obtain ⟨⟨⟩, rfl⟩ := hb2
  exact ⟨riscvStep true, _, _, _, _, _, _, WeakRvwmoCert3.phrunBoundary cpu1 rs1' ib1' d1' true,
    WeakRvwmoCert3.phrunBoundary cpu2 rs2' ib2' d2' true, hag'⟩

/-! # 5b. RE-CONVERGENCE, INTEGRATED: `certSegment''` -/

/-- The always-steppable administrative outcomes (Rocq's twelve; `choose` excluded). -/
def ocSilent (o : Outcome Register RegisterType) : Prop :=
  match o with
  | .regRead _ | .regWrite _ _ | .branchAnnounce _ _ | .cacheOp _ | .tlbi _
  | .takeException _ | .returnException _ | .translationStart _ | .translationEnd _
  | .cycleCount | .message _ | .getCycleCount => True
  | _ => False

inductive tailSilent (T : List Nat) : SailM Unit → Prop where
  | tsRet (y : Unit) : tailSilent T (.pure y)
  | tsNext (o : Outcome Register RegisterType) (k : o.ret → SailM Unit) :
      ocSilent o →
      (∀ r, r ∈ pnodeWrs (.impure (.ok o) k) → ∃ n, eregNum r = some n ∧ n ∈ T) →
      (∀ v, tailSilent T (k v)) →
      tailSilent T (.impure (.ok o) k)

theorem ocSilentStep (o : Outcome Register RegisterType) (k : o.ret → SailM Unit) (rs : RegFile)
    (ib : Ibch) (d : DevStates) (l : Wlabel) (m' : SailM Unit) (ors : Option RegFile)
    (fn' : Ofence) (d' : DevStates) (oib : Option Ibch) (obar : Option barrier_kind) :
    ocSilent o →
    pnodeStep (.impure (.ok o) k) rs ib d l m' ors fn' d' oib obar →
    lbAdmin true l ∧ l ≠ LInstr ∧ ibnAnn (.impure (.ok o) k) = false ∧
      fn' = none ∧ d' = d ∧ ∃ v, m' = k v := by
  intro hs hst
  cases o with
  | regWrite r v =>
    obtain ⟨rfl, rfl, -, rfl, rfl, -, -⟩ := hst
    refine ⟨?_, erwLabelNeInstr _, rfl, rfl, rfl, _, rfl⟩
    rcases erwLabelCases (erwOf (depsOfIb ib.ibBits) ib.ibRds r) with h | ⟨_, _, h⟩ | ⟨_, h⟩ <;>
      rw [h] <;> trivial
  | memRead => exact False.elim hs
  | memWrite => exact False.elim hs
  | readRam => exact False.elim hs
  | writeRam => exact False.elim hs
  | barrier => exact False.elim hs
  | choose => exact False.elim hs
  | instrAnnounce => exact False.elim hs
  | _ =>
    obtain ⟨rfl, rfl, -, rfl, rfl, -, -⟩ := hst
    exact ⟨trivial, (fun h => nomatch h), rfl, rfl, rfl, _, rfl⟩

/-- (Lean-only, deviation 8) A silent outcome's label is never a fetch. -/
theorem WeakRvwmoCert3b.ocSilentStepPin (o : Outcome Register RegisterType)
    (k : o.ret → SailM Unit) (rs : RegFile) (ib : Ibch) (d : DevStates) (l : Wlabel)
    (m' : SailM Unit) (ors : Option RegFile) (fn' : Ofence) (d' : DevStates) (oib : Option Ibch)
    (obar : Option barrier_kind) (im : Image) :
    ocSilent o →
    pnodeStep (.impure (.ok o) k) rs ib d l m' ors fn' d' oib obar →
    WeakAxRealize.fetchPin im l := by
  intro hs hst
  cases o with
  | regWrite r v =>
    obtain ⟨rfl, rfl, -, rfl, rfl, -, -⟩ := hst
    rcases erwLabelCases (erwOf (depsOfIb ib.ibBits) ib.ibRds r) with h | ⟨_, _, h⟩ | ⟨_, h⟩ <;>
      rw [h] <;> trivial
  | memRead => exact False.elim hs
  | memWrite => exact False.elim hs
  | readRam => exact False.elim hs
  | writeRam => exact False.elim hs
  | barrier => exact False.elim hs
  | choose => exact False.elim hs
  | instrAnnounce => exact False.elim hs
  | _ =>
    obtain ⟨rfl, rfl, -, rfl, rfl, -, -⟩ := hst
    trivial

theorem ocSilentStepExists (o : Outcome Register RegisterType) (k : o.ret → SailM Unit)
    (rs : RegFile) (ib : Ibch) (d : DevStates) :
    ocSilent o →
    ∃ l m' ors oib obar, pnodeStep (.impure (.ok o) k) rs ib d l m' ors none d oib obar := by
  intro hs
  cases o with
  | memRead => exact False.elim hs
  | memWrite => exact False.elim hs
  | readRam => exact False.elim hs
  | writeRam => exact False.elim hs
  | barrier => exact False.elim hs
  | choose => exact False.elim hs
  | instrAnnounce => exact False.elim hs
  | _ => exact ⟨_, _, _, _, _, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- TERMINATION IS A THEOREM: `SailM` is inductive, so a silent tail reaches the boundary. -/
theorem tailSilentRun (T : List Nat) (cpu : CPU) (d0 : Efab) (m : SailM Unit) :
    tailSilent T m →
    ∀ (rs : RegFile) (ib : Ibch),
    ∃ (ls : List Wlabel) (rds : List Nat) (wrs : List Register) (ann : Bool) (rs' : RegFile)
      (ib' : Ibch),
      (∀ l0, l0 ∈ ls → lbAdmin true l0) ∧ LInstr ∉ ls ∧
      phrun cpu ls rds wrs ann m rs none ib d0 (.pure ()) rs' none ib' d0 ∧
      (∀ r, r ∈ wrs → ∃ n, eregNum r = some n ∧ n ∈ T) ∧
      (∀ l0, l0 ∈ ls → ∀ im, WeakAxRealize.fetchPin im l0) := by
  intro h
  induction h with
  | tsRet y =>
    intro rs ib
    exact ⟨[], [], [], false, rs, ib, fun _ h => absurd h List.not_mem_nil, List.not_mem_nil,
      phrun.nil _ _ _ _ _, fun _ h => absurd h List.not_mem_nil,
      fun _ h => absurd h List.not_mem_nil⟩
  | tsNext o k hs hw _ ih =>
    intro rs ib
    obtain ⟨l, m', ors, oib, obar, hst⟩ := ocSilentStepExists o k rs ib d0.efDev hs
    obtain ⟨had, hne, -, -, -, v, rfl⟩ :=
      ocSilentStep o k rs ib d0.efDev l m' ors none d0.efDev oib obar hs hst
    obtain ⟨ls, rds, wrs, ann, rs', ib', hadm, hni, hrun, hws, hpin⟩ :=
      ih v (ors.getD rs) (oib.getD ib)
    refine ⟨l :: ls, _, _, _, rs', ib', ?_, ?_,
      phrun.more (Or.inl ⟨rfl, ⟨hst, rfl⟩, rfl, rfl, rfl⟩) hrun, ?_, ?_⟩
    · intro l0 hl0
      rcases List.mem_cons.1 hl0 with rfl | h
      · exact had
      · exact hadm l0 h
    · intro hin
      rcases List.mem_cons.1 hin with h | h
      · exact hne h.symm
      · exact hni h
    · intro r hr
      rcases List.mem_append.1 hr with h | h
      · exact hw r h
      · exact hws r h
    · intro l0 hl0 im
      rcases List.mem_cons.1 hl0 with rfl | h
      · exact WeakRvwmoCert3b.ocSilentStepPin o k rs ib d0.efDev l0 _ ors none d0.efDev oib obar im
          hs hst
      · exact hpin l0 h im

/-- Lean shape (`WeakEvInst` deviation 4): the node step carries `obar` and the fabric equation
`d1 = {d with efDev := d1.efDev}`; the PLIC arm is refuted by its `LDev` label. -/
theorem admStepNode (cpu : CPU) (m : SailM Unit) (rs : RegFile) (ib : Ibch) (d : Efab)
    (l : Wlabel) (p1 : Pexv6) (d1 : Efab) :
    (∀ kd ba bs, l ≠ LDev kd ba bs) →
    pstepEv (.PHart cpu m rs none ib) d l p1 d1 →
    ∃ (m' : SailM Unit) (ors : Option RegFile) (fn' : Ofence) (oib : Option Ibch)
      (obar : Option barrier_kind),
      p1 = .PHart cpu m' (ors.getD rs) fn' (oib.getD ib) ∧
      pnodeStep m rs ib d.efDev l m' ors fn' d1.efDev oib obar ∧
      d1 = { d with efDev := d1.efDev } := by
  intro hne hst
  cases p1 with
  | PDisk _ => exact hst.elim
  | PHart cpu1 m1 rs1 fn1 ib1 =>
    obtain ⟨rfl, ors, oib, obar, rfl, rfl, ⟨hn, hd⟩ | hp⟩ := hst
    · exact ⟨m1, ors, fn1, oib, obar, rfl, hn, hd⟩
    · obtain ⟨_, _, _, _, hl, _⟩ := hp
      exact absurd hl (hne _ _ _)

theorem tailSilentAdm (T : List Nat) (cpu : CPU) (ls : List Wlabel) (p pa : Pexv6)
    (d da : Efab) :
    admRun true p d ls pa da →
    ∀ (m : SailM Unit) (rs : RegFile) (ib : Ibch),
      p = .PHart cpu m rs none ib → tailSilent T m → (∀ kd ba bs, LDev kd ba bs ∉ ls) →
      (∃ (ma : SailM Unit) (rsa : RegFile) (iba : Ibch) (rds : List Nat) (wrs : List Register)
         (ann : Bool),
         pa = .PHart cpu ma rsa none iba ∧ da = d ∧ tailSilent T ma ∧
         phrun cpu ls rds wrs ann m rs none ib d ma rsa none iba d ∧
         (∀ r, r ∈ wrs → ∃ n, eregNum r = some n ∧ n ∈ T))
      ∨ (∃ (ls1 ls2 : List Wlabel) (rds1 : List Nat) (wrs1 : List Register) (ann1 : Bool)
           (rsb : RegFile) (ibb : Ibch) (tick : Bool),
           ls = ls1 ++ LInstr :: ls2 ∧
           phrun cpu ls1 rds1 wrs1 ann1 m rs none ib d (.pure ()) rsb none ibb d ∧
           (∀ r, r ∈ wrs1 → ∃ n, eregNum r = some n ∧ n ∈ T) ∧
           admRun true (.PHart cpu (riscvStep tick) rsb none ibNone) d ls2 pa da) := by
  intro h
  induction h with
  | ARnil p d =>
    intro m rs ib hp hts _
    subst hp
    exact .inl ⟨m, rs, ib, [], [], false, rfl, rfl, hts, phrun.nil _ _ _ _ _,
      fun _ h => absurd h List.not_mem_nil⟩
  | ARcons p d l p1 d1 ls pa da _ hs hrun ih =>
    intro m rs ib hp hts hni
    subst hp
    have hld : (∀ kd ba bs, l ≠ LDev kd ba bs) := fun kd ba bs h => hni kd ba bs (h ▸ List.mem_cons_self)
    have hni' : ∀ kd ba bs, LDev kd ba bs ∉ ls :=
      fun kd ba bs h => hni kd ba bs (List.mem_cons_of_mem _ h)
    obtain ⟨m', ors, fn', oib, obar, rfl, hnst, hd⟩ := admStepNode cpu m rs ib d l p1 d1 hld hs
    cases hts with
    | tsRet y =>
      obtain ⟨tick, rfl, rfl, rfl, rfl, hdd, rfl, -⟩ := hnst
      have hd1 : d1 = d := by rw [hd, hdd]
      subst hd1
      exact .inr ⟨[], ls, [], [], false, rs, ib, tick, rfl, phrun.nil _ _ _ _ _,
        fun _ h => absurd h List.not_mem_nil, hrun⟩
    | tsNext o k hsil hw hts =>
      obtain ⟨_, _, _, rfl, hdd, v, rfl⟩ :=
        ocSilentStep o k rs ib d.efDev l m' ors fn' d1.efDev oib obar hsil hnst
      have hd1 : d1 = d := by rw [hd, hdd]
      subst hd1
      have hstep : pstepHw cpu (.impure (.ok o) k) rs none ib d1 l
          (pnodeRds (.impure (.ok o) k)) (pnodeWrs (.impure (.ok o) k))
          (ibnAnn (.impure (.ok o) k)) (k v) ors none d1 oib obar :=
        Or.inl ⟨rfl, ⟨hnst, rfl⟩, rfl, rfl, rfl⟩
      rcases ih (k v) (ors.getD rs) (oib.getD ib) rfl (hts v) hni' with
        ⟨ma, rsa, iba, rds, wrs, ann, rfl, rfl, htsa, hrun2, hws⟩ |
        ⟨ls1, ls2, rds1, wrs1, ann1, rsb, ibb, tick, rfl, hrun2, hws, hadm2⟩
      · refine .inl ⟨ma, rsa, iba, _, _, _, rfl, rfl, htsa, phrun.more hstep hrun2, ?_⟩
        intro r hr
        rcases List.mem_append.1 hr with h | h
        · exact hw r h
        · exact hws r h
      · refine .inr ⟨l :: ls1, ls2, _, _, _, rsb, ibb, tick, rfl, phrun.more hstep hrun2, ?_,
          hadm2⟩
        intro r hr
        rcases List.mem_append.1 hr with h | h
        · exact hw r h
        · exact hws r h

theorem tailSilentNoLabel (T : List Nat) (cpu : CPU) (ma : SailM Unit) (rsa : RegFile)
    (iba : Ibch) (da : Efab) (l : Wlabel) (p' : Pexv6) (d' : Efab) :
    tailSilent T ma →
    ¬ lbAdmin true l →
    pstepEv (.PHart cpu ma rsa none iba) da l p' d' → False := by
  intro hts hna hst
  have hld : (∀ kd ba bs, l ≠ LDev kd ba bs) := fun kd ba bs h => hna (by subst h; trivial)
  obtain ⟨m', ors, fn', oib, obar, _, hnst, _⟩ := admStepNode cpu ma rsa iba da l p' d' hld hst
  cases hts with
  | tsRet y =>
    obtain ⟨tick, rfl, _⟩ := hnst
    exact hna rfl
  | tsNext o k hsil _ _ =>
    exact hna (ocSilentStep o k rsa iba _ l m' ors fn' _ oib obar hsil hnst).1

/-- BETWEEN A WITNESS READ AND THE NEXT INSTRUCTION BOUNDARY THERE IS NO MEMORY LABEL. -/
theorem witnessInstrTailSilent (T : List Nat) (cpu : CPU) (m : SailM Unit) (rs : RegFile)
    (ib : Ibch) (d da : Efab) (ls : List Wlabel) (ma : SailM Unit) (rsa : RegFile) (fna : Ofence)
    (iba : Ibch) (l : Wlabel) (p' : Pexv6) (d' : Efab) :
    tailSilent T m →
    (∀ kd ba bs, LDev kd ba bs ∉ ls) →
    admRun true (.PHart cpu m rs none ib) d ls (.PHart cpu ma rsa fna iba) da →
    ¬ lbAdmin true l →
    pstepEv (.PHart cpu ma rsa fna iba) da l p' d' →
    ∃ (ls1 ls2 : List Wlabel) (rds1 : List Nat) (wrs1 : List Register) (ann1 : Bool)
      (rsb : RegFile) (ibb : Ibch) (tick : Bool),
      ls = ls1 ++ LInstr :: ls2 ∧
      phrun cpu ls1 rds1 wrs1 ann1 m rs none ib d (.pure ()) rsb none ibb d ∧
      (∀ r, r ∈ wrs1 → ∃ n, eregNum r = some n ∧ n ∈ T) ∧
      admRun true (.PHart cpu (riscvStep tick) rsb none ibNone) d ls2
        (.PHart cpu ma rsa fna iba) da := by
  intro hts hni hadm hre hst
  rcases tailSilentAdm T cpu ls _ _ d da hadm m rs ib rfl hts hni with
    ⟨ma2, rsa2, iba2, _, _, _, heq, rfl, htsa, _, _⟩ | h
  · cases heq
    exact (tailSilentNoLabel T cpu _ _ _ _ l p' d' htsa hre hst).elim
  · exact h

theorem WeakRvwmoCert3.phrunApp {cpu : CPU} {ls1 : List Wlabel} {rds1 : List Nat}
    {wrs1 : List Register} {ann1 : Bool} {ls2 : List Wlabel} {rds2 : List Nat}
    {wrs2 : List Register} {ann2 : Bool} {m : SailM Unit} {rs : RegFile} {fn : Ofence}
    {ib : Ibch} {d : Efab} {m1 : SailM Unit} {rs1' : RegFile} {fn1 : Ofence} {ib1 : Ibch}
    {d1 : Efab} {m2 : SailM Unit} {rs2' : RegFile} {fn2 : Ofence} {ib2 : Ibch} {d2 : Efab} :
    phrun cpu ls1 rds1 wrs1 ann1 m rs fn ib d m1 rs1' fn1 ib1 d1 →
    phrun cpu ls2 rds2 wrs2 ann2 m1 rs1' fn1 ib1 d1 m2 rs2' fn2 ib2 d2 →
    phrun cpu (ls1 ++ ls2) (rds1 ++ rds2) (wrs1 ++ wrs2) (ann1 || ann2)
      m rs fn ib d m2 rs2' fn2 ib2 d2 := by
  intro h1
  induction h1 with
  | nil => intro h2; exact h2
  | more hstep _ ih =>
    intro h2
    simp only [List.cons_append, List.append_assoc, Bool.or_assoc]
    exact phrun.more hstep (ih h2)

/-- (Lean-only, deviation 8) `cblkPre` at any admin predicate `A`. -/
theorem WeakRvwmoCert3b.cblkPreG (A : Wlabel → Prop) (cpu : CPU) (d0 : Efab) (ws : Wstate)
    (lb : Lbl) (l : Wlabel) (rds : List Nat)
    (wrs : List Register) (ls0 : List Wlabel) (rds0 : List Nat) (wrs0 : List Register)
    (ann0 : Bool) (m0 : SailM Unit) (rs0 : RegFile) (fn0 : Ofence) (ib0 : Ibch)
    (m : SailM Unit) (rs : RegFile) (fn : Ofence) (ib : Ibch)
    (m' : SailM Unit) (rs' : RegFile) (fn' : Ofence) (ib' : Ibch) :
    (∀ l0, l0 ∈ ls0 → A l0) →
    phrun cpu ls0 rds0 wrs0 ann0 m0 rs0 fn0 ib0 d0 m rs fn ib d0 →
    WeakRvwmoCert2.cblkG A cpu d0 ws lb l rds wrs m rs fn ib m' rs' fn' ib' →
    WeakRvwmoCert2.cblkG A cpu d0 ws lb l (rds0 ++ rds) (wrs0 ++ wrs) m0 rs0 fn0 ib0 m' rs' fn'
      ib' := by
  rintro hadm0 hrun0 ⟨ls, ma, rsa, fna, iba, da, rdsA, wrsA, annA, rdsB, wrsB, annB, hadm, hA,
    hre, hB, rfl, rfl⟩
  exact ⟨ls0 ++ ls, ma, rsa, fna, iba, da, rds0 ++ rdsA, wrs0 ++ wrsA, ann0 || annA, rdsB, wrsB,
    annB, fun l0 hl0 => (List.mem_append.1 hl0).elim (hadm0 l0) (hadm l0),
    WeakRvwmoCert3.phrunApp hrun0 hA, hre, hB, (List.append_assoc _ _ _).symm,
    (List.append_assoc _ _ _).symm⟩

theorem cblkPre (cpu : CPU) (d0 : Efab) (ws : Wstate) (lb : Lbl) (l : Wlabel) (rds : List Nat)
    (wrs : List Register) (ls0 : List Wlabel) (rds0 : List Nat) (wrs0 : List Register)
    (ann0 : Bool) (m0 : SailM Unit) (rs0 : RegFile) (fn0 : Ofence) (ib0 : Ibch)
    (m : SailM Unit) (rs : RegFile) (fn : Ofence) (ib : Ibch)
    (m' : SailM Unit) (rs' : RegFile) (fn' : Ofence) (ib' : Ibch) :
    (∀ l0, l0 ∈ ls0 → lbAdmin true l0) →
    phrun cpu ls0 rds0 wrs0 ann0 m0 rs0 fn0 ib0 d0 m rs fn ib d0 →
    cblk cpu d0 ws lb l rds wrs m rs fn ib m' rs' fn' ib' →
    cblk cpu d0 ws lb l (rds0 ++ rds) (wrs0 ++ wrs) m0 rs0 fn0 ib0 m' rs' fn' ib' :=
  WeakRvwmoCert3b.cblkPreG (lbAdmin true) cpu d0 ws lb l rds wrs ls0 rds0 wrs0 ann0 m0 rs0 fn0
    ib0 m rs fn ib m' rs' fn' ib'

def clockstep (T : List Nat) (m1 : SailM Unit) (rs1 : RegFile) (fn1 : Ofence) (ib1 : Ibch)
    (m2 : SailM Unit) (rs2 : RegFile) (fn2 : Ofence) (ib2 : Ibch) : Prop :=
  m2 = m1 ∧ fn2 = fn1 ∧ ib2 = ib1 ∧ dregAgree (fun n => n ∉ T) rs1 rs2

def csync (T : List Nat) (m1 : SailM Unit) (rs1 : RegFile) (fn1 : Ofence) (ib1 : Ibch)
    (m2 : SailM Unit) (rs2 : RegFile) (fn2 : Ofence) (ib2 : Ibch) : Prop :=
  clockstep T m1 rs1 fn1 ib1 m2 rs2 fn2 ib2 ∨
  (fn1 = none ∧ fn2 = none ∧ tailSilent T m1 ∧ tailSilent T m2 ∧
    dregAgree (fun n => n ∉ T) rs1 rs2)

/-! ## 5b.2' THE TAINT GROWS, AND EVERY INVARIANT WEAKENS WITH IT -/

theorem dregAgreeTaintMono (T T' : List Nat) (rs1 rs2 : RegFile) :
    T ⊆ T' → dregAgree (fun n => n ∉ T) rs1 rs2 → dregAgree (fun n => n ∉ T') rs1 rs2 :=
  fun hsub => dregAgreeMono _ _ rs1 rs2 (fun _ hn hin => hn (hsub hin))

theorem rdsOkTaintMono (T T' : List Nat) (l : List Nat) :
    T ⊆ T' → rdsOk (fun n => n ∉ T') l → rdsOk (fun n => n ∉ T) l :=
  fun hsub h n hn hin => h n hn (hsub hin)

theorem tailSilentMono (T T' : List Nat) (m : SailM Unit) :
    T ⊆ T' → tailSilent T m → tailSilent T' m := by
  intro hsub h
  induction h with
  | tsRet y => exact .tsRet y
  | tsNext o k hs hw _ ih =>
    refine .tsNext o k hs ?_ ih
    intro r hr
    obtain ⟨n, hn, hin⟩ := hw r hr
    exact ⟨n, hn, hsub hin⟩

theorem clockstepMono (T T' : List Nat) (m1 : SailM Unit) (rs1 : RegFile) (fn1 : Ofence)
    (ib1 : Ibch) (m2 : SailM Unit) (rs2 : RegFile) (fn2 : Ofence) (ib2 : Ibch) :
    T ⊆ T' → clockstep T m1 rs1 fn1 ib1 m2 rs2 fn2 ib2 →
    clockstep T' m1 rs1 fn1 ib1 m2 rs2 fn2 ib2 := by
  rintro hsub ⟨rfl, rfl, rfl, hag⟩
  exact ⟨rfl, rfl, rfl, dregAgreeTaintMono T T' _ _ hsub hag⟩

theorem csyncMono (T T' : List Nat) (m1 : SailM Unit) (rs1 : RegFile) (fn1 : Ofence)
    (ib1 : Ibch) (m2 : SailM Unit) (rs2 : RegFile) (fn2 : Ofence) (ib2 : Ibch) :
    T ⊆ T' → csync T m1 rs1 fn1 ib1 m2 rs2 fn2 ib2 →
    csync T' m1 rs1 fn1 ib1 m2 rs2 fn2 ib2 := by
  rintro hsub (hc | ⟨rfl, rfl, ht1, ht2, hag⟩)
  · exact .inl (clockstepMono T T' _ _ _ _ _ _ _ _ hsub hc)
  · exact .inr ⟨rfl, rfl, tailSilentMono T T' _ hsub ht1, tailSilentMono T T' _ hsub ht2,
      dregAgreeTaintMono T T' _ _ hsub hag⟩

theorem boundaryStepTick (rs : RegFile) (ib : Ibch) (d : DevStates) (tick : Bool) :
    pnodeStep (.pure ()) rs ib d LInstr (riscvStep tick) none none d (some ibNone) none :=
  ⟨tick, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem csyncAdvance (T : List Nat) (cpu : CPU) (d0 : Efab)
    (m1 : SailM Unit) (rs1 : RegFile) (fn1 : Ofence) (ib1 : Ibch)
    (m2 : SailM Unit) (rs2 : RegFile) (fn2 : Ofence) (ib2 : Ibch)
    (ls : List Wlabel) (ma : SailM Unit) (rsa : RegFile) (fna : Ofence) (iba : Ibch) (da : Efab)
    (l : Wlabel) (p' : Pexv6) (d' : Efab) :
    csync T m1 rs1 fn1 ib1 m2 rs2 fn2 ib2 →
    (∀ kd ba bs, LDev kd ba bs ∉ ls) →
    admRun true (.PHart cpu m1 rs1 fn1 ib1) d0 ls (.PHart cpu ma rsa fna iba) da →
    ¬ lbAdmin true l →
    pstepEv (.PHart cpu ma rsa fna iba) da l p' d' →
    ∃ (mc : SailM Unit) (rs1c rs2c : RegFile) (fnc : Ofence) (ibc : Ibch)
      (lsc lspre lsq : List Wlabel) (rdsp rdsq : List Nat) (wrsp wrsq : List Register)
      (annp annq : Bool),
      admRun true (.PHart cpu mc rs1c fnc ibc) d0 lsc (.PHart cpu ma rsa fna iba) da ∧
      (∀ l0, l0 ∈ lspre → lbAdmin true l0) ∧
      phrun cpu lspre rdsp wrsp annp m2 rs2 fn2 ib2 d0 mc rs2c fnc ibc d0 ∧
      (∀ l0, l0 ∈ lsq → lbAdmin true l0) ∧
      phrun cpu lsq rdsq wrsq annq m1 rs1 fn1 ib1 d0 mc rs1c fnc ibc d0 ∧
      dregAgree (fun n => n ∉ T) rs1c rs2c ∧
      (∀ l0, l0 ∈ lsc → l0 ∈ ls) ∧
      (∀ l0, l0 ∈ lspre → ∀ im, WeakAxRealize.fetchPin im l0) := by
  rintro (⟨rfl, rfl, rfl, hag⟩ | ⟨rfl, rfl, hts1, hts2, hag⟩) hni hadm hre hst
  · exact ⟨_, rs1, rs2, _, _, ls, [], [], [], [], [], [], false, false, hadm,
      fun _ h => absurd h List.not_mem_nil, phrun.nil _ _ _ _ _,
      fun _ h => absurd h List.not_mem_nil, phrun.nil _ _ _ _ _, hag, fun _ h => h,
      fun _ h => absurd h List.not_mem_nil⟩
  · obtain ⟨ls1, ls2, rds1, wrs1, ann1, rsb, ibb, tick, hsp, hrun1, hws1, hadm2⟩ :=
      witnessInstrTailSilent T cpu m1 rs1 ib1 d0 da ls ma rsa fna iba l p' d' hts1 hni hadm hre
        hst
    obtain ⟨lsq, rdsq, wrsq, annq, rs2b, ib2b, hadmq, _, hrunq, hwsq, hpinq⟩ :=
      tailSilentRun T cpu d0 m2 hts2 rs2 ib2
    have hadm1 : ∀ l0, l0 ∈ ls1 → lbAdmin true l0 := fun l0 hl0 =>
      admRunAdmin true _ d0 ls _ da hadm l0 (by rw [hsp]; exact List.mem_append_left _ hl0)
    refine ⟨riscvStep tick, rsb, rs2b, none, ibNone, ls2, lsq ++ [LInstr], ls1 ++ [LInstr],
      _, _, _, _, _, _, hadm2, ?_,
      WeakRvwmoCert3.phrunApp hrunq (WeakRvwmoCert3.phrunBoundary cpu rs2b ib2b d0 tick), ?_,
      WeakRvwmoCert3.phrunApp hrun1 (WeakRvwmoCert3.phrunBoundary cpu rsb ibb d0 tick), ?_, ?_,
      ?_⟩
    · intro l0 hl0
      rcases List.mem_append.1 hl0 with h | h
      · exact hadmq l0 h
      · rw [List.mem_singleton.1 h]; rfl
    · intro l0 hl0
      rcases List.mem_append.1 hl0 with h | h
      · exact hadm1 l0 h
      · rw [List.mem_singleton.1 h]; rfl
    · refine taintClosure (fun n => n ∉ T) cpu ls1 rds1 wrs1 ann1 m1 rs1 none ib1 d0 (.pure ()) rsb
        none ibb d0 cpu lsq rdsq wrsq annq m2 rs2 none ib2 d0 (.pure ()) rs2b none ib2b d0 hag
        hrun1 hrunq ?_
      intro r hr
      rcases List.mem_append.1 hr with h | h
      · obtain ⟨n, hn, hin⟩ := hws1 r h
        exact ⟨n, hn, fun hno => hno hin⟩
      · obtain ⟨n, hn, hin⟩ := hwsq r h
        exact ⟨n, hn, fun hno => hno hin⟩
    · intro l0 hl0
      rw [hsp]
      exact List.mem_append_right _ (List.mem_cons_of_mem _ hl0)
    · intro l0 hl0 im
      rcases List.mem_append.1 hl0 with h | h
      · exact hpinq l0 h im
      · rw [List.mem_singleton.1 h]; trivial

/-- (Lean-only, deviation 8) `cblkpPre` at any admin predicate `A`. -/
theorem WeakRvwmoCert3b.cblkpPreG (A : Wlabel → Prop) (cpu : CPU) (d0 : Efab) (ws : Wstate)
    (lb : Lbl) (l1 l2 : Wlabel)
    (rds : List Nat) (wrs : List Register) (ls0 : List Wlabel) (rds0 : List Nat)
    (wrs0 : List Register) (ann0 : Bool) (m0 : SailM Unit) (rs0 : RegFile) (fn0 : Ofence)
    (ib0 : Ibch) (m : SailM Unit) (rs : RegFile) (fn : Ofence) (ib : Ibch)
    (m' : SailM Unit) (rs' : RegFile) (fn' : Ofence) (ib' : Ibch) :
    (∀ l0, l0 ∈ ls0 → A l0) →
    phrun cpu ls0 rds0 wrs0 ann0 m0 rs0 fn0 ib0 d0 m rs fn ib d0 →
    WeakRvwmoCert3.cblkpG A cpu d0 ws lb l1 l2 rds wrs m rs fn ib m' rs' fn' ib' →
    WeakRvwmoCert3.cblkpG A cpu d0 ws lb l1 l2 (rds0 ++ rds) (wrs0 ++ wrs) m0 rs0 fn0 ib0 m' rs'
      fn' ib' := by
  rintro hadm0 hrun0 ⟨ls1, ma, rsa, fna, iba, da, rdsA, wrsA, annA, mm, rsm, fnm, ibm, dm, rdsB,
    wrsB, annB, ls2, mm2, rsm2, fnm2, ibm2, dm2, rdsC, wrsC, annC, rdsD, wrsD, annD, had1, hA, hre,
    hB, had2, hC, hD, rfl, rfl⟩
  exact ⟨ls0 ++ ls1, ma, rsa, fna, iba, da, rds0 ++ rdsA, wrs0 ++ wrsA, ann0 || annA, mm, rsm,
    fnm, ibm, dm, rdsB, wrsB, annB, ls2, mm2, rsm2, fnm2, ibm2, dm2, rdsC, wrsC, annC, rdsD, wrsD,
    annD, fun l0 hl0 => (List.mem_append.1 hl0).elim (hadm0 l0) (had1 l0),
    WeakRvwmoCert3.phrunApp hrun0 hA, hre, hB, had2, hC, hD, (List.append_assoc _ _ _).symm,
    (List.append_assoc _ _ _).symm⟩

theorem cblkpPre (cpu : CPU) (d0 : Efab) (ws : Wstate) (lb : Lbl) (l1 l2 : Wlabel)
    (rds : List Nat) (wrs : List Register) (ls0 : List Wlabel) (rds0 : List Nat)
    (wrs0 : List Register) (ann0 : Bool) (m0 : SailM Unit) (rs0 : RegFile) (fn0 : Ofence)
    (ib0 : Ibch) (m : SailM Unit) (rs : RegFile) (fn : Ofence) (ib : Ibch)
    (m' : SailM Unit) (rs' : RegFile) (fn' : Ofence) (ib' : Ibch) :
    (∀ l0, l0 ∈ ls0 → lbAdmin true l0) →
    phrun cpu ls0 rds0 wrs0 ann0 m0 rs0 fn0 ib0 d0 m rs fn ib d0 →
    cblkp cpu d0 ws lb l1 l2 rds wrs m rs fn ib m' rs' fn' ib' →
    cblkp cpu d0 ws lb l1 l2 (rds0 ++ rds) (wrs0 ++ wrs) m0 rs0 fn0 ib0 m' rs' fn' ib' :=
  WeakRvwmoCert3b.cblkpPreG (lbAdmin true) cpu d0 ws lb l1 l2 rds wrs ls0 rds0 wrs0 ann0 m0 rs0
    fn0 ib0 m rs fn ib m' rs' fn' ib'

/-- (Deviation 8: on pinned pair blocks.) -/
def cpolpr (x : Nat) (cpu : CPU) (d0 : Efab) (Tf : Nat → List Nat)
    (Nd : Nat → SailM Unit → Prop) (Ctx : Nat → Cand → Prop) (Cls : Cand → Lbl → Prop)
    (Q : Nat → Lbl → Prop) : Prop :=
  ∀ (k : Nat) (c0 : Cand) (ws : Wstate) (lb : Lbl) (l1 l2 : Wlabel) (rds : List Nat)
    (wrs : List Register) (m : SailM Unit) (rs1 rs2 : RegFile) (fn : Ofence) (ib : Ibch)
    (m' : SailM Unit) (rs1' : RegFile) (fn' : Ofence) (ib' : Ibch),
    srvwmoConsistent c0 →
    Ctx k c0 →
    Q k lb →
    ((candLastSt c0).msWs x).wRelp = ws.wRelp →
    dregAgree (fun n => n ∉ Tf k) rs1 rs2 →
    rdsOk (fun n => n ∉ Tf k) rds →
    Nd k m →
    WeakRvwmoCert3.cblkpPin c0.cdImg cpu d0 ws lb l1 l2 rds wrs m rs1 fn ib m' rs1' fn' ib' →
    ∃ rs2',
      WeakRvwmoCert3.cblkpPin c0.cdImg cpu d0 ws lb l1 l2 rds wrs m rs2 fn ib m' rs2' fn' ib' ∧
      mstepOk (candLastSt c0) x lb ∧
      Cls c0 lb ∧
      dregAgree (fun n => n ∉ Tf k) rs1' rs2'

theorem cpolprOfCpolp (x : Nat) (cpu : CPU) (d0 : Efab) (T : List Nat)
    (Nd : Nat → SailM Unit → Prop) (Ctx : Nat → Cand → Prop) (Cls : Cand → Lbl → Prop)
    (Q : Nat → Lbl → Prop) :
    cpolp x cpu d0 T Ctx Cls Q → cpolpr x cpu d0 (fun _ => T) Nd Ctx Cls Q :=
  fun H k c0 ws lb l1 l2 rds wrs m rs1 rs2 fn ib m' rs1' fn' ib' hc hctx hq hrelp hag _ _ hblk =>
    H k c0 ws lb l1 l2 rds wrs m rs1 rs2 fn ib m' rs1' fn' ib' hc hctx hq hrelp hag hblk

/-! ## 5b.4 `ndreach` — THE REACHABILITY PARAMETER -/

inductive ndreach (cpu : CPU) (d0 : Efab) (Q : Nat → Lbl → Prop) (k0 : Nat) (m0 : SailM Unit) :
    Nat → SailM Unit → Prop where
  | ndStart : ndreach cpu d0 Q k0 m0 k0 m0
  | ndAdm (k : Nat) (m m' : SailM Unit) (rs rs' : RegFile) (fn fn' : Ofence) (ib ib' : Ibch)
      (ls : List Wlabel) (rds : List Nat) (wrs : List Register) (ann : Bool) :
      ndreach cpu d0 Q k0 m0 k m →
      (∀ l0, l0 ∈ ls → lbAdmin true l0) →
      phrun cpu ls rds wrs ann m rs fn ib d0 m' rs' fn' ib' d0 →
      ndreach cpu d0 Q k0 m0 k m'
  | ndBlk (k : Nat) (m m' : SailM Unit) (ws : Wstate) (lb : Lbl) (l : Wlabel) (rds : List Nat)
      (wrs : List Register) (rs rs' : RegFile) (fn fn' : Ofence) (ib ib' : Ibch) :
      ndreach cpu d0 Q k0 m0 k m → Q k lb →
      cblk cpu d0 ws lb l rds wrs m rs fn ib m' rs' fn' ib' →
      ndreach cpu d0 Q k0 m0 (k + 1) m'
  | ndBlkp (k : Nat) (m m' : SailM Unit) (ws : Wstate) (lb : Lbl) (l1 l2 : Wlabel)
      (rds : List Nat) (wrs : List Register) (rs rs' : RegFile) (fn fn' : Ofence)
      (ib ib' : Ibch) :
      ndreach cpu d0 Q k0 m0 k m → Q k lb →
      cblkp cpu d0 ws lb l1 l2 rds wrs m rs fn ib m' rs' fn' ib' →
      ndreach cpu d0 Q k0 m0 (k + 1) m'

def lastlb : List Lbl → Option Lbl
  | [] => none
  | [a] => some a
  | _ :: t => lastlb t

def segLocked (rowseg : List Lbl) (Pin : Prop) : Prop :=
  match lastlb rowseg with
  | none => Pin
  | some lbz => lbIsW lbz = true

theorem lastlbCons (a : Lbl) (l : List Lbl) : ∃ z, lastlb (a :: l) = some z := by
  induction l generalizing a with
  | nil => exact ⟨a, rfl⟩
  | cons b l ih => exact ih b

theorem segLockedCons (lb : Lbl) (row : List Lbl) (Pin Pmid : Prop) :
    segLocked (lb :: row) Pin → (lbIsW lb = true → Pmid) → segLocked row Pmid := by
  cases row with
  | nil => intro h hp; exact hp h
  | cons a row' =>
    obtain ⟨z, hz⟩ := lastlbCons a row'
    have he : lastlb (lb :: a :: row') = lastlb (a :: row') := rfl
    unfold segLocked
    rw [he, hz]
    intro h _
    exact h

theorem lastlbAppSingle (l : List Lbl) (a : Lbl) : lastlb (l ++ [a]) = some a := by
  induction l with
  | nil => rfl
  | cons b l ih =>
    cases l with
    | nil => rfl
    | cons c l' => exact ih

theorem segLockedSnoc (row : List Lbl) (a : Lbl) (Pin : Prop) :
    lbIsW a = true → segLocked (row ++ [a]) Pin := by
  intro h
  unfold segLocked
  rw [lastlbAppSingle]
  exact h

/-- `csync` transports along any other agreeing pair of register files. -/
theorem csyncRegs (T : List Nat) (m1 m2 : SailM Unit) (rs rs1 rs2 : RegFile) (fn : Ofence)
    (ib : Ibch) :
    csync T m1 rs fn ib m2 rs fn ib →
    dregAgree (fun n => n ∉ T) rs1 rs2 →
    csync T m1 rs1 fn ib m2 rs2 fn ib := by
  rintro (⟨rfl, -, -, -⟩ | ⟨h1, h2, hts1, hts2, -⟩) hag
  · exact .inl ⟨rfl, rfl, rfl, hag⟩
  · exact .inr ⟨h1, h2, hts1, hts2, hag⟩

theorem hlblRealizesPairNotadm (p pm : Pexv6) (ws : Wstate) (lb : Lbl) (l1 l2 : Wlabel)
    (instr : Bool) :
    hlblRealizesPair p pm ws lb l1 l2 → ¬ lbAdmin instr l1 := by
  rintro ⟨_, _, _, _, _, _, _, _, rfl, -⟩ h
  exact h

/-! ## 5b.5 `certSegment''` — Rocq's `Section segment''` context is the leading parameters -/

theorem certSegment'' (x : Nat) (cpu : CPU) (d0 : Efab) (Tf : Nat → List Nat)
    (Hmono : ∀ k, Tf k ⊆ Tf (k + 1))
    (Q : Nat → Lbl → Prop) (Ctx : Nat → Cand → Prop) (Cls : Cand → Lbl → Prop)
    (Hpres : ∀ (k : Nat) (c0 : Cand) (lb lb' : Lbl),
      Ctx k c0 → srvwmoConsistent c0 → Q k lb → lblReidxW lb lb' →
      mstepOk (candLastSt c0) x lb' →
      Cls c0 lb' →
      Ctx (k + 1) (candSnoc c0 ⟨x, lb'⟩))
    (Nd : Nat → SailM Unit → Prop)
    (Hrdsp : ∀ (k : Nat) (lb : Lbl) (ws : Wstate) (l1 l2 : Wlabel) (rds : List Nat)
      (wrs : List Register) (m : SailM Unit) (rs : RegFile) (fn : Ofence) (ib : Ibch)
      (m' : SailM Unit) (rs' : RegFile) (fn' : Ofence) (ib' : Ibch),
      Q k lb → Nd k m →
      cblkp cpu d0 ws lb l1 l2 rds wrs m rs fn ib m' rs' fn' ib' →
      rdsOk (fun n => n ∉ Tf k) rds)
    (HNdadm : ∀ (k : Nat) (m m' : SailM Unit) (rs rs' : RegFile) (fn fn' : Ofence)
      (ib ib' : Ibch) (ls : List Wlabel) (rds : List Nat) (wrs : List Register) (ann : Bool),
      Nd k m → (∀ l0, l0 ∈ ls → lbAdmin true l0) →
      phrun cpu ls rds wrs ann m rs fn ib d0 m' rs' fn' ib' d0 → Nd k m')
    (HNdblk : ∀ (k : Nat) (m m' : SailM Unit) (ws : Wstate) (lb : Lbl) (l : Wlabel)
      (rds : List Nat) (wrs : List Register) (rs rs' : RegFile) (fn fn' : Ofence)
      (ib ib' : Ibch),
      Nd k m → Q k lb →
      cblk cpu d0 ws lb l rds wrs m rs fn ib m' rs' fn' ib' → Nd (k + 1) m')
    (HNdblkp : ∀ (k : Nat) (m m' : SailM Unit) (ws : Wstate) (lb : Lbl) (l1 l2 : Wlabel)
      (rds : List Nat) (wrs : List Register) (rs rs' : RegFile) (fn fn' : Ofence)
      (ib ib' : Ibch),
      Nd k m → Q k lb →
      cblkp cpu d0 ws lb l1 l2 rds wrs m rs fn ib m' rs' fn' ib' → Nd (k + 1) m')
    (Hpol'' : ∀ (k : Nat) (c0 : Cand) (ws : Wstate) (lb : Lbl) (l : Wlabel) (rds : List Nat)
      (wrs : List Register) (m : SailM Unit) (rs1 rs2 : RegFile) (fn : Ofence) (ib : Ibch)
      (m' : SailM Unit) (rs1' : RegFile) (fn' : Ofence) (ib' : Ibch),
      srvwmoConsistent c0 →
      Ctx k c0 →
      Q k lb →
      ((candLastSt c0).msWs x).wRelp = ws.wRelp →
      dregAgree (fun n => n ∉ Tf k) rs1 rs2 →
      Nd k m →
      WeakRvwmoCert2.cblkPin c0.cdImg cpu d0 ws lb l rds wrs m rs1 fn ib m' rs1' fn' ib' →
      ∃ (lb' : Lbl) (l' : Wlabel) (rds' : List Nat) (wrs' : List Register) (rs2' : RegFile)
        (m2' : SailM Unit) (fn2' : Ofence) (ib2' : Ibch),
        WeakRvwmoCert2.cblkPin c0.cdImg cpu d0 ws lb' l' rds' wrs' m rs2 fn ib m2' rs2' fn2' ib2' ∧
        mstepOk (candLastSt c0) x lb' ∧
        lblReidxW lb lb' ∧
        Cls c0 lb' ∧
        csync (Tf (k + 1)) m' rs1' fn' ib' m2' rs2' fn2' ib2' ∧
        (lbIsW lb = true → clockstep (Tf (k + 1)) m' rs1' fn' ib' m2' rs2' fn2' ib2'))
    (Hpolp : cpolpr x cpu d0 Tf Nd Ctx Cls Q)
    (k0 : Nat) (ws0 : Wstate) (rowseg : List Lbl) (p : Pexv6) (es : List Eitem)
    (pfin : Pexv6) :
    hemit (fun _ => d0) k0 ws0 rowseg p es pfin →
    (∀ kd ba bs, LDev kd ba bs ∉ es.map Prod.fst) →
    (∀ i lb, rowseg[i]? = some lb → Q (k0 + i) lb) →
    ∀ m0 rs10 fn0 ib0, p = .PHart cpu m0 rs10 fn0 ib0 →
    Nd k0 m0 →
    ∀ (c : Cand) (pst : Nat → List Pexv6) (dv : Nat → Efab) (m20 : SailM Unit) (rs20 : RegFile)
      (fn20 : Ofence) (ib20 : Ibch),
      srvwmoConsistent c →
      Ctx k0 c →
      WeakRvwmoCert2.esPin c.cdImg es →
      execProgOk' (pstepPin c.cdImg pstepEv) pclsEv pst dv (candExec c) →
      (pst (cdEnd c))[x]? = some (.PHart cpu m20 rs20 fn20 ib20) →
      dv (cdEnd c) = d0 →
      csync (Tf k0) m0 rs10 fn0 ib0 m20 rs20 fn20 ib20 →
      ((candLastSt c).msWs x).wRelp = ws0.wRelp →
      ∃ (c' : Cand) (pst' : Nat → List Pexv6) (dv' : Nat → Efab) (tradd : List Estep)
        (m1 : SailM Unit) (rs11 : RegFile) (fn1 : Ofence) (ib1 : Ibch)
        (m21 : SailM Unit) (rs21 : RegFile) (fn21 : Ofence) (ib21 : Ibch),
        c'.cdTr = c.cdTr ++ tradd ∧
        (∀ s, s ∈ tradd → s.esAg = x) ∧
        List.Forall₂ lblReidxW rowseg (tradd.map (fun s => s.esLb)) ∧
        srvwmoConsistent c' ∧
        Ctx (k0 + rowseg.length) c' ∧
        execProgOk' (pstepPin c.cdImg pstepEv) pclsEv pst' dv' (candExec c') ∧
        (pst' (cdEnd c'))[x]? = some (.PHart cpu m21 rs21 fn21 ib21) ∧
        dv' (cdEnd c') = d0 ∧
        pfin = .PHart cpu m1 rs11 fn1 ib1 ∧
        csync (Tf (k0 + rowseg.length)) m1 rs11 fn1 ib1 m21 rs21 fn21 ib21 ∧
        (segLocked rowseg (clockstep (Tf k0) m0 rs10 fn0 ib0 m20 rs20 fn20 ib20) →
          clockstep (Tf (k0 + rowseg.length)) m1 rs11 fn1 ib1 m21 rs21 fn21 ib21) ∧
        ((candLastSt c').msWs x).wRelp = (rowWsAux k0 ws0 rowseg).wRelp ∧
        c'.cdImg = c.cdImg ∧
        pst' 0 = pst 0 ∧
        dv' 0 = dv 0 ∧
        (∀ y, y ≠ x → (pst' (cdEnd c'))[y]? = (pst (cdEnd c))[y]?) ∧
        (∀ y, y ≠ x → ((candLastSt c').msWs y).wRelp = ((candLastSt c).msWs y).wRelp) ∧
        Nd (k0 + rowseg.length) m1 := by
  intro hem
  induction hem with
  | HEnil k ws p =>
    intro _ _ m0 rs10 fn0 ib0 hp0 hnd c pst dv m20 rs20 fn20 ib20 hc hctx _ hpo hp hdvc hsync hrelp
    exact ⟨c, pst, dv, [], m0, rs10, fn0, ib0, m20, rs20, fn20, ib20, by simp,
      fun s hs => absurd hs List.not_mem_nil, .nil, hc, hctx, hpo, hp, hdvc, hp0, hsync,
      fun h => h, hrelp, rfl, rfl, rfl, fun _ _ => rfl, fun _ _ => rfl, hnd⟩
  | HEone k ws lb row p ls pa da l p' es pfin har hre hst _ ih =>
    intro hdev hrf m0 rs10 fn0 ib0 hp0 hnd c pst dv m20 rs20 fn20 ib20 hc hctx hes hpo hp hdvc
      hsync hrelp
    subst hp0
    have hlb : Q k lb := hrf 0 lb rfl
    have hrf' : ∀ i lb0, row[i]? = some lb0 → Q (k + 1 + i) lb0 := by
      intro i lb0 hi
      have h0 := hrf (i + 1) lb0 hi
      rwa [show k + (i + 1) = k + 1 + i by omega] at h0
    have hkk : k + (lb :: row).length = k + 1 + row.length := by
      rw [List.length_cons]; omega
    rw [eblockFst] at hdev
    obtain ⟨hni, _, hdev'⟩ := notDevOfBlock _ _ _ hdev
    obtain ⟨ma, rsa, fna, iba, rfl⟩ := admRunPhart true _ _ d0 ls da har cpu m0 rs10 fn0 ib0 rfl
    obtain ⟨m1, rs11, fn1, ib1, rfl⟩ := pstepEvPhart cpu ma rsa fna iba da l p' d0 hst
    obtain ⟨hpinls, hes'⟩ := WeakRvwmoCert2.esPinBlock c.cdImg ls l k es hes
    obtain ⟨mc, rs1c, rs2c, fnc, ibc, lsc, lspre, lsq, rdsp, rdsq, wrsp, wrsq, annp, annq, hadmc,
      hadmpre, hrunpre, hadmq, hrunq, hagc, hsub, hpinpre⟩ :=
      csyncAdvance (Tf k) cpu d0 m0 rs10 fn0 ib0 m20 rs20 fn20 ib20 ls ma rsa fna iba da l _ _
        hsync hni har (hlblRealizesNotadm _ _ _ _ true hre) hst
    obtain ⟨rds, wrs, hblkp⟩ := WeakRvwmoCert2.cblkIntroPin c.cdImg cpu d0 ws lb l lsc
      (.PHart cpu ma rsa fna iba) da mc rs1c fnc ibc m1 rs11 fn1 ib1 hadmc
      (fun l0 h => hpinls l0 (hsub l0 h)) hre hst
    have hblk := WeakRvwmoCert2.cblkPinCblk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hblkp
    have hndc : Nd k mc := HNdadm k m0 mc rs10 rs1c fn0 fnc ib0 ibc lsq rdsq wrsq annq hnd hadmq
      hrunq
    have hnd1 : Nd (k + 1) m1 :=
      HNdblk k mc m1 ws lb l rds wrs rs1c rs11 fnc fn1 ibc ib1 hndc hlb hblk
    obtain ⟨lb', l', rds', wrs', rs2', m2', fn2', ib2', hblk2, hok, hri, hcl, hsync2, hw2⟩ :=
      Hpol'' k c ws lb l rds wrs mc rs1c rs2c fnc ibc m1 rs11 fn1 ib1 hc hctx hlb hrelp hagc hndc
        hblkp
    have hblk3 : WeakRvwmoCert2.cblkPin c.cdImg cpu d0 ((candLastSt c).msWs x) lb' l'
        (rdsp ++ rds') (wrsp ++ wrs') m20 rs20 fn20 ib20 m2' rs2' fn2' ib2' :=
      WeakRvwmoCert2.cblkRelpG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hrelp
        (WeakRvwmoCert3b.cblkPreG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
          (fun l0 h => ⟨hadmpre l0 h, hpinpre l0 h _⟩) hrunpre hblk2)
    obtain ⟨hc2, hpo2⟩ := certBlockSnoc c x pst dv cpu d0 lb' l' _ _ m20 rs20 fn20 ib20 m2' rs2'
      fn2' ib2' hc hpo hp hdvc hblk3 hok
    have hctx2 : Ctx (k + 1) (candSnoc c ⟨x, lb'⟩) := Hpres k c lb lb' hctx hc hlb hri hok hcl
    have hend : cdEnd (candSnoc c ⟨x, lb'⟩) = cdEnd c + 1 := cdEndSnoc c _
    have hp2 : (pstSnoc c pst x (.PHart cpu m2' rs2' fn2' ib2') (cdEnd (candSnoc c ⟨x, lb'⟩)))[x]?
        = some (.PHart cpu m2' rs2' fn2' ib2') := by
      rw [hend, pstSnocGt c pst x _ (cdEnd c + 1) (by omega)]
      exact List.getElem?_set_self (lookup_lt_Some hp)
    have hdv2 : dvSnoc c dv d0 (cdEnd (candSnoc c ⟨x, lb'⟩)) = d0 := by
      rw [hend, dvSnocGt c dv d0 (cdEnd c + 1) (by omega)]
    have hrelp2 : ((candLastSt (candSnoc c ⟨x, lb'⟩)).msWs x).wRelp
        = (lblPost k ws lb).wRelp := by
      rw [candSnocRelp, hrelp, lblReidxWRelp _ lb lb' hri, lblPostRelp]
    obtain ⟨c', pst', dv', tradd, m2, rs12, fn2, ib2, m22, rs22, fn22, ib22, htr, hag', hf2, hc',
      hctx', hpo', hp'', hdv', hfin, hsyncf, hlockf, hrelpf, himg2, hpst02, hdv02, hfr2, hfrp2,
      hndf⟩ :=
      ih hdev' hrf' m1 rs11 fn1 ib1 rfl hnd1 (candSnoc c ⟨x, lb'⟩)
        (pstSnoc c pst x (.PHart cpu m2' rs2' fn2' ib2')) (dvSnoc c dv d0) m2' rs2' fn2' ib2'
        hc2 hctx2 hes' hpo2 hp2 hdv2 hsync2 hrelp2
    refine ⟨c', pst', dv', ⟨x, lb'⟩ :: tradd, m2, rs12, fn2, ib2, m22, rs22, fn22, ib22, ?_, ?_,
      .cons hri hf2, hc', by rw [hkk]; exact hctx', hpo', hp'', hdv', hfin,
      by rw [hkk]; exact hsyncf, ?_, hrelpf, ?_, ?_, ?_, ?_, ?_, by rw [hkk]; exact hndf⟩
    · rw [htr, candSnocTr, List.append_assoc]
      rfl
    · intro s hs
      rcases List.mem_cons.1 hs with rfl | hs
      · rfl
      · exact hag' s hs
    · rw [hkk]
      intro hlk
      exact hlockf (segLockedCons lb row _ _ hlk hw2)
    · rw [himg2]; rfl
    · rw [hpst02, pstSnocLe c pst x _ 0 (Nat.zero_le _)]
    · rw [hdv02, dvSnocLe c dv d0 0 (Nat.zero_le _)]
    · intro y hy
      rw [hfr2 y hy, hend, pstSnocGt c pst x _ (cdEnd c + 1) (by omega)]
      exact List.getElem?_set_ne (Ne.symm hy)
    · intro y hy
      rw [hfrp2 y hy, candSnocRelpNe c x y lb' hy]
  | HEpair k ws lb row p ls1 pa da l1 pm dm ls2 pm2 dm2 l2 p' es pfin har1 hre hst1 har2 hst2 _
      ih =>
    intro hdev hrf m0 rs10 fn0 ib0 hp0 hnd c pst dv m20 rs20 fn20 ib20 hc hctx hes hpo hp hdvc
      hsync hrelp
    subst hp0
    have hlb : Q k lb := hrf 0 lb rfl
    have hrf' : ∀ i lb0, row[i]? = some lb0 → Q (k + 1 + i) lb0 := by
      intro i lb0 hi
      have h0 := hrf (i + 1) lb0 hi
      rwa [show k + (i + 1) = k + 1 + i by omega] at h0
    have hkk : k + (lb :: row).length = k + 1 + row.length := by
      rw [List.length_cons]; omega
    rw [eblockFst, eblockFst] at hdev
    obtain ⟨hni1, _, hdev1⟩ := notDevOfBlock _ _ _ hdev
    obtain ⟨_, _, hdev'⟩ := notDevOfBlock _ _ _ hdev1
    obtain ⟨ma, rsa, fna, iba, rfl⟩ :=
      admRunPhart true _ _ d0 ls1 da har1 cpu m0 rs10 fn0 ib0 rfl
    obtain ⟨mb, rsb, fnb, ibb, rfl⟩ := pstepEvPhart cpu ma rsa fna iba da l1 pm dm hst1
    obtain ⟨mc2, rsc2, fnc2, ibc2, rfl⟩ :=
      admRunPhart false _ _ dm ls2 dm2 har2 cpu mb rsb fnb ibb rfl
    obtain ⟨m1, rs11, fn1, ib1, rfl⟩ := pstepEvPhart cpu mc2 rsc2 fnc2 ibc2 dm2 l2 p' d0 hst2
    obtain ⟨hpin1, hes1⟩ := WeakRvwmoCert2.esPinBlock c.cdImg ls1 l1 k _ hes
    obtain ⟨-, hes'⟩ := WeakRvwmoCert2.esPinBlock c.cdImg ls2 l2 k es hes1
    obtain ⟨mc, rs1c, rs2c, fnc, ibc, lsc, lspre, lsq, rdsp, rdsq, wrsp, wrsq, annp, annq, hadmc,
      hadmpre, hrunpre, hadmq, hrunq, hagc, hsub, hpinpre⟩ :=
      csyncAdvance (Tf k) cpu d0 m0 rs10 fn0 ib0 m20 rs20 fn20 ib20 ls1 ma rsa fna iba da l1 _ _
        hsync hni1 har1 (hlblRealizesPairNotadm _ _ _ _ _ _ true hre) hst1
    obtain ⟨rds, wrs, hblkp⟩ := WeakRvwmoCert3.cblkpIntroPin c.cdImg cpu d0 ws lb l1 l2 lsc
      (.PHart cpu ma rsa fna iba) da (.PHart cpu mb rsb fnb ibb) dm ls2
      (.PHart cpu mc2 rsc2 fnc2 ibc2) dm2 mc rs1c fnc ibc m1 rs11 fn1 ib1 hadmc
      (fun l0 h => hpin1 l0 (hsub l0 h)) hre hst1 har2 hst2
    have hblk := WeakRvwmoCert3.cblkpPinCblkp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hblkp
    have hndc : Nd k mc := HNdadm k m0 mc rs10 rs1c fn0 fnc ib0 ibc lsq rdsq wrsq annq hnd hadmq
      hrunq
    have hrdsok : rdsOk (fun n => n ∉ Tf k) rds :=
      Hrdsp k lb ws l1 l2 rds wrs mc rs1c fnc ibc m1 rs11 fn1 ib1 hlb hndc hblk
    have hnd1 : Nd (k + 1) m1 :=
      HNdblkp k mc m1 ws lb l1 l2 rds wrs rs1c rs11 fnc fn1 ibc ib1 hndc hlb hblk
    obtain ⟨rs2', hblk2, hok, hcl, hag2⟩ :=
      Hpolp k c ws lb l1 l2 rds wrs mc rs1c rs2c fnc ibc m1 rs11 fn1 ib1 hc hctx hlb hrelp hagc
        hrdsok hndc hblkp
    have hblk3 : WeakRvwmoCert3.cblkpPin c.cdImg cpu d0 ((candLastSt c).msWs x) lb l1 l2
        (rdsp ++ rds) (wrsp ++ wrs) m20 rs20 fn20 ib20 m1 rs2' fn1 ib1 :=
      WeakRvwmoCert3.cblkpRelpG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hrelp
        (WeakRvwmoCert3b.cblkpPreG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
          (fun l0 h => ⟨hadmpre l0 h, hpinpre l0 h _⟩) hrunpre hblk2)
    obtain ⟨hc2, hpo2⟩ := certBlockSnocPair c x pst dv cpu d0 lb l1 l2 _ _ m20 rs20 fn20 ib20 m1
      rs2' fn1 ib1 hc hpo hp hdvc hblk3 hok
    have hctx2 : Ctx (k + 1) (candSnoc c ⟨x, lb⟩) :=
      Hpres k c lb lb hctx hc hlb (lblReidxWRefl lb) hok hcl
    have hend : cdEnd (candSnoc c ⟨x, lb⟩) = cdEnd c + 1 := cdEndSnoc c _
    have hp2 : (pstSnoc c pst x (.PHart cpu m1 rs2' fn1 ib1) (cdEnd (candSnoc c ⟨x, lb⟩)))[x]?
        = some (.PHart cpu m1 rs2' fn1 ib1) := by
      rw [hend, pstSnocGt c pst x _ (cdEnd c + 1) (by omega)]
      exact List.getElem?_set_self (lookup_lt_Some hp)
    have hdv2 : dvSnoc c dv d0 (cdEnd (candSnoc c ⟨x, lb⟩)) = d0 := by
      rw [hend, dvSnocGt c dv d0 (cdEnd c + 1) (by omega)]
    have hrelp2 : ((candLastSt (candSnoc c ⟨x, lb⟩)).msWs x).wRelp
        = (lblPost k ws lb).wRelp := by
      rw [candSnocRelp, hrelp, lblPostRelp]
    have hagm : dregAgree (fun n => n ∉ Tf (k + 1)) rs11 rs2' :=
      dregAgreeTaintMono _ _ _ _ (Hmono k) hag2
    have hsync2 : csync (Tf (k + 1)) m1 rs11 fn1 ib1 m1 rs2' fn1 ib1 := .inl ⟨rfl, rfl, rfl, hagm⟩
    obtain ⟨c', pst', dv', tradd, m2, rs12, fn2, ib2, m22, rs22, fn22, ib22, htr, hag', hf2, hc',
      hctx', hpo', hp'', hdv', hfin, hsyncf, hlockf, hrelpf, himg2, hpst02, hdv02, hfr2, hfrp2,
      hndf⟩ :=
      ih hdev' hrf' m1 rs11 fn1 ib1 rfl hnd1 (candSnoc c ⟨x, lb⟩)
        (pstSnoc c pst x (.PHart cpu m1 rs2' fn1 ib1)) (dvSnoc c dv d0) m1 rs2' fn1 ib1
        hc2 hctx2 hes' hpo2 hp2 hdv2 hsync2 hrelp2
    refine ⟨c', pst', dv', ⟨x, lb⟩ :: tradd, m2, rs12, fn2, ib2, m22, rs22, fn22, ib22, ?_, ?_,
      .cons (lblReidxWRefl lb) hf2, hc', by rw [hkk]; exact hctx', hpo', hp'', hdv', hfin,
      by rw [hkk]; exact hsyncf, ?_, hrelpf, ?_, ?_, ?_, ?_, ?_, by rw [hkk]; exact hndf⟩
    · rw [htr, candSnocTr, List.append_assoc]
      rfl
    · intro s hs
      rcases List.mem_cons.1 hs with rfl | hs
      · rfl
      · exact hag' s hs
    · rw [hkk]
      intro hlk
      exact hlockf (segLockedCons lb row _ _ hlk (fun _ => ⟨rfl, rfl, rfl, hagm⟩))
    · rw [himg2]; rfl
    · rw [hpst02, pstSnocLe c pst x _ 0 (Nat.zero_le _)]
    · rw [hdv02, dvSnocLe c dv d0 0 (Nat.zero_le _)]
    · intro y hy
      rw [hfr2 y hy, hend, pstSnocGt c pst x _ (cdEnd c + 1) (by omega)]
      exact List.getElem?_set_ne (Ne.symm hy)
    · intro y hy
      rw [hfrp2 y hy, candSnocRelpNe c x y lb hy]

/-! # 6. NON-VACUITY -/

/-! ## 6.1 The empty candidate is a certified prefix of every graph, at every witness set -/

theorem ctracePrefixEmpty (G : Gexec) (W : Geid → Prop) :
    CtracePrefix G ⟨G.gxImg, []⟩ (fun _ => (0, 0)) W := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_⟩
  · intro p s hs; simp at hs
  · intro p s hs; simp at hs
  · intro p s hs; simp at hs
  · intro p s hs; simp at hs
  · intro s hs hle
    simp [cdLog, trMsgs] at hle
    omega

theorem witFenceUbEmpty (G : Gexec) (W : Geid → Prop) (r : Geid) :
    witFenceUb G ⟨G.gxImg, []⟩ (fun _ => (0, 0)) W r := by
  intro p s hs; simp at hs

theorem poisOkAtEmpty (G : Gexec) (r : Geid) : poisOkAt G ⟨G.gxImg, []⟩ (fun _ => (0, 0)) r := by
  intro p s hs; simp at hs

theorem poisOkHartEmpty (G : Gexec) (x : Nat) :
    poisOkHart G ⟨G.gxImg, []⟩ (fun _ => (0, 0)) x := by
  intro p s hs; simp at hs

theorem cpolCtxEmpty (G : Gexec) (W : Geid → Prop) (x : Nat) : cpolCtx G W x ⟨G.gxImg, []⟩ :=
  ⟨fun _ => (0, 0), ctracePrefixEmpty G W, witFenceUbEmpty G W _, poisOkHartEmpty G x⟩

/-! ## 6.2 THE FLOOR, at a real graph read -/

theorem certFloorOkImage (G : Gexec) (i : Nat) (W : Geid → Prop) (aq : Bool) (base : Int)
    (ts : List Nat) (vs : List (BitVec 8)) :
    rvwmoMinusConsistent G →
    WPolocClosed G W →
    ¬ W (i, 0) →
    gxLbl G (i, 0) = some (.LLoad aq base ts vs) →
    floorOk ⟨G.gxImg, []⟩ i aq base ts :=
  fun hcons hpc hnW hl =>
    certFloorOk G ⟨G.gxImg, []⟩ (fun _ => (0, 0)) W i aq base ts vs hcons
      (ctracePrefixEmpty G W) hpc (witFenceUbEmpty G W _) (poisOkAtEmpty G _) hnW hl

/-! ## 6.3 `certSegment'` on the REAL `sw &started` block (Rocq `Section nonvacuity3`) -/

theorem certSegment'Witness (cpu : CPU) (rs : RegFile) (ib : Ibch) (d0 : Efab) :
    ∃ (c' : Cand) (pst' : Nat → List Pexv6) (dv' : Nat → Efab) (tradd : List Estep),
      c'.cdTr = tradd ∧
      (∀ s, s ∈ tradd → s.esAg = 0) ∧
      List.Forall₂ lblReidxW evRow (tradd.map (fun s => s.esLb)) ∧
      srvwmoConsistent c' ∧
      execProgOk' (pstepPin (fun _ => none) pstepEv) pclsEv pst' dv' (candExec c') ∧
      tradd[0]? = some ⟨0, .LStore false (paZ evFlag) (WeakInterpProj.wbytes 4 lockOne)
        .WCplain⟩ := by
  obtain ⟨c', pst', dv', tradd, _, _, _, _, _, htr, hag, hf2, hc', _, hpo', -⟩ :=
    certSegment' 0 cpu d0 [] (fun _ => lbStoreNe) (fun _ _ => True) (fun _ _ => True)
      (fun _ _ _ _ _ _ _ _ _ _ => trivial)
      (fun _ c0 ws lb l rds wrs m rs1 rs2 fn ib0 m' rs1' fn' ib' hc _ hlb h1 h2 h3 =>
        polStore' 0 cpu d0 c0 ws lb l rds wrs m rs1 rs2 fn ib0 m' rs1' fn' ib' hc hlb h1 h2 h3)
      (cpolpOfRmwfree 0 cpu d0 [] _ _ _ (fun _ lb hlb => lbStoreNeRmwfree lb hlb))
      0 wsInit evRow (evP0 cpu rs ib) _ _ (nvHemit cpu rs ib d0)
      (fun _ lb hi => nvRowClass lb (List.mem_of_getElem? hi)) evX2.2 rs none ib rfl
      (smC (fun _ => none)) (smPst cpu rs ib) (smDv d0) rs (smConsistent _) trivial
      (WeakRvwmoCert2.nvPin cpu rs ib _) (smProg0 _ cpu rs ib d0) rfl rfl (dregAgreeRefl _ _) (by rw [smWs])
  refine ⟨c', pst', dv', tradd, by rw [htr]; rfl, hag, hf2, hc', hpo', ?_⟩
  exact segExitWrite 0 evRow tradd 0 _ _ _ _ hf2 hag rfl

theorem certSegment'Nonvacuous :
    ∃ (c' : Cand) (pst' : Nat → List Pexv6) (dv' : Nat → Efab) (tradd : List Estep),
      tradd ≠ [] ∧ c'.cdTr = tradd ∧
      (∀ s, s ∈ tradd → s.esAg = 0) ∧
      srvwmoConsistent c' ∧
      execProgOk' (pstepPin (fun _ => none) pstepEv) pclsEv pst' dv' (candExec c') ∧
      tradd[0]? = some ⟨0, .LStore false (paZ evFlag) (WeakInterpProj.wbytes 4 lockOne)
        .WCplain⟩ := by
  obtain ⟨c', pst', dv', tradd, htr, hag, -, hc', hpo', hlk⟩ :=
    certSegment'Witness ⟨0, by decide⟩ evRs0 ibNone (efInit ⟨fun _ => default⟩)
  refine ⟨c', pst', dv', tradd, ?_, htr, hag, hc', hpo', hlk⟩
  rintro rfl
  simp at hlk

/-! ## 6.4 The boundary, at a real two-node run -/

theorem witMBoundary (cpu : CPU) (rs : RegFile) (d : Efab) :
    ∃ (ls : List Wlabel) (rds : List Nat) (wrs : List Register) (ann : Bool) (ib' : Ibch)
      (rs' : RegFile),
      phrun cpu ls rds wrs ann witM rs none ibNone d (.pure ()) rs' none ib' d ∧
      wrs = [(.x14 : Register)] :=
  ⟨_, _, _, _, _, _,
    phrun.more (Or.inl ⟨rfl, ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl⟩, rfl, rfl, rfl⟩)
      (phrun.more (Or.inl ⟨rfl, ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl⟩, rfl, rfl, rfl⟩)
        (phrun.nil _ _ _ _ _)), rfl⟩

theorem boundaryReconvergeNonvacuous (cpu : CPU) (rs1 rs2 : RegFile) (d : Efab) :
    dregAgree (fun n => n ∉ ([] : List Nat)) rs1 rs2 →
    ∃ (m0 : SailM Unit) (rs1' rs2' : RegFile) (ib1' ib2' : Ibch) (rdsA : List Nat)
      (wrsA : List Register) (annA : Bool) (rdsB : List Nat) (wrsB : List Register)
      (annB : Bool),
      phrun cpu [LInstr] rdsA wrsA annA (.pure ()) rs1' none ib1' d m0 rs1' none ibNone d ∧
      phrun cpu [LInstr] rdsB wrsB annB (.pure ()) rs2' none ib2' d m0 rs2' none ibNone d ∧
      dregAgree (fun n => n ∉ [14]) rs1' rs2' := by
  intro hag
  obtain ⟨ls1, rds1, wrs1, ann1, ib1', rs1', hr1, hw1⟩ := witMBoundary cpu rs1 d
  obtain ⟨ls2, rds2, wrs2, ann2, ib2', rs2', hr2, hw2⟩ := witMBoundary cpu rs2 d
  obtain ⟨m0, rdsA, wrsA, annA, rdsB, wrsB, annB, hA, hB, hag2⟩ :=
    boundaryReconvergeRun [] 14 cpu ls1 rds1 wrs1 ann1 witM rs1 none ibNone d (.pure ()) rs1' ib1'
      d cpu ls2 rds2 wrs2 ann2 witM rs2 none ibNone d (.pure ()) rs2' ib2' d hag hr1 hr2
      (by
        subst hw1 hw2
        intro r hr
        have hr' : r = .x14 := by simpa using hr
        subst hr'
        exact ⟨14, by decide, List.mem_singleton_self _⟩)
      atBoundaryRet atBoundaryRet
  exact ⟨m0, rs1', rs2', ib1', ib2', rdsA, wrsA, annA, rdsB, wrsB, annB, hA, hB, hag2⟩

end Weak
