/-
Weak: **A7-T2c capstone: `wpdWriterHart`, the per-hart `WPd` Löb induction for the lock3s WRITER
row** (`AxLock3Prog.l3pWRow`), at the `AxTierA2.axGA2` adequacy instance (AxSL tier).

Rocq: `iris/AxLock3Writer.v` @ xxvzwolszwmp.

## The Rocq header, in substance

Design `claude-notes/design/weak-memory-lb-axsl.md` §7.A7.  Builds on `AxLock3Prog` (the
hand-written writer program, its step facts), `AxLock3Wp`/`AxLock3Wp2` (the four lock3s flow
equations at `axGA2`), `AxLock3Wp3` (the `lobp` membership corollaries for the writer row), the
`WPd` machinery (`AxWpD`) and `AxTierA2` (`tierAWpd`).  Worked BACKWARDS from the row end, one row
position per lemma:
  §1  generic helpers: `naSplittingWfSnap` (a single `lobp`-predecessor's deposit from a
      persistent annotation snapshot), `wpdSkipStepOfLater`, `flowEqDynExistsSingleton` (a flow
      equation whose `flowIn` is a singleton holding `∃ a, Pk a` is provable from the per-`a`
      equations, the witness destructed locally inside the flow equation), and
      `wpdRowEndTriv` (the row-end triviality Löb, register- AND program-state-generic: past the
      row only administrative steps exist, `wlWdata` is `none` there, and the postcondition is
      bare `True`).
  §2  W4 — the triviality at the writer's row length.
  §3  shared plumbing: `wpdPosShell` (clauses (a)/(c)/(d) of an interior position, Löb over the
      register file for the wire), store/RMW graph facts, the `gob` bridges.
  §4  W3 — the release store (position 3), consuming the `x`-write's re-tied token via
      `lockRelFlowEq3A` (W3's own deposit is `True`); W2 — the fence (position 2), a skip.
  §5  W1 — the `x`-write (position 1), consuming the acquire's deposit via
      `lockXwriteFlowEq3ATie`, depositing `R1 Hl` for W3.
  §6  W0 — the acquire: the RMW's write half (Löb over the register file for the SC retry
      self-loop and the PLIC wire) depositing `R0`, and its read half (also register-generic).
  §7  the capstones: `wpdWriterHart` (genesis-sourced acquire, `Himg`/`Hrd0`) and
      `wpdWriterHartRel` (release-sourced acquire, via the existential deposits `R0e`/`R1e`).

**Fetches.** None: the writer's programs are hand-built monad terms with no fetch node.  The
step clause's boot-image pin premise (`WeakAxRealize.fetchPin`, owner Q8) is never needed.

## Deviations from Rocq

1. NAMES: camelCase (map below).  `R0`/`R1`/`R1e` are in the duplicated-name table, hence
   `AxLock3Writer.R0`/`AxLock3Writer.R1`/`AxLock3Writer.R1e`.  Lean-only helpers
   (file-qualified): `AxLock3Writer.twpd` (Rocq's local notation `TWPD s`),
   `AxLock3Writer.annotEq` (the detach-then-allocate annotation map in `wpEvStep`'s union form),
   `AxLock3Writer.gconstPure`/`AxLock3Writer.localTriv` (`axGA2`'s graph pin is `⌜GD' = GD⌝`, its
   local interpretation `True` — Rocq's `iDestruct "Hgc" as %->` / `done`).
2. THE INSTANCE: Rocq's `Local Instance AxGA2_lock3W` ↦ the named `axGA2Lock3 L x GD nm`
   (AxLock3Wp) passed explicitly; the policy `lock_axpol` ↦ the named `lockAxpol` (AxProtLock3),
   passed explicitly.  Rocq's `T` is gone (O2 Stage C).  `invGS_gen HasNoLc Σ` ↦
   `[InvGS_gen hlc GF]` for any `hlc` (as AxLock3Wp deviation 3).
3. SECTION CONTEXT: Rocq's `Hxy HLram Hxram HLeq Hxeq Hrow Hcons` (and the case-split contexts
   `Himg Hrd0` / `w_rel Hwrel_wb0 Hgob_rel Hrfe_rel`) are explicit arguments of exactly the
   lemmas whose statements or proofs use them, in that order.
4. STATEMENT SHAPES (as AxLock3Wp deviation 4): `P -∗ Q` ↦ `P ⊢ Q`; `s_pol GD e` ↦
   `lockPolS GD e`; `S k` ↦ `k + 1`; `Interface.Ret tt` ↦ `.pure ()`; a write continuation's
   answer `inl None` ↦ `.Ok (some true)`; `annot_interp` (of the section instance) ↦
   `AxAnnot.annotInterp` in `naSplittingWfSnap` (definitionally `axGA2`'s field); `e ↦ₐ P` ↦
   `AxAnnot.annotOwn e P`.
5. `astep_prog` has no fetch constructor (Stage C): `astepProgRowEndShape`/the inversions have
   three cases, and `astepProgRead0Vacuous` no longer needs `Hrow` (Rocq used it only for the
   fetch arm).  The step clause (b) of `WPd` takes the image pin premise, ignored here.
6. The capstones: Rocq's `init_regstate` ↦ an arbitrary register file `rs` (as AxLock3Prog
   deviation 4): `wpdWriterHart`/`wpdWriterHartRel` are stated at `l3pWP0 Lpa xpa cpu rs v`
   for every `rs`.  `nthByte0Id` is stated at MachCSL's `nthByte` (width `8 * 1`).
7. PROOF ROUTE (not statements): `wpdSkipStepOfLater` is proved directly (Rocq routes through
   `wp_skip_step_mono`); Rocq's `bi.later_intro` wrap of the fresh `annot_interp` before
   `iNext` is unnecessary in Lean.

**Rocq → Lean name map.**  `w_m0..w_m4` `wM0..wM4`, `na_splitting_wf_snap` `naSplittingWfSnap`,
`wpd_skip_step_of_later` `wpdSkipStepOfLater`, `flow_eq_dyn_exists_singleton`
`flowEqDynExistsSingleton`, `astep_prog_row_end_shape` `astepProgRowEndShape`,
`lb_admin_wl_wdata_none` `lbAdminWlWdataNone`, `wpd_row_end_triv` `wpdRowEndTriv`, `wpd_w4`
`wpdW4`, `gwrites_byte_of_store` `gwritesByteOfStore`, `gacq_po_gob_cat` `gacqPoGobCat`,
`gfence_covers_gob_cat` `gfenceCoversGobCat`, `wpd_pos_shell` `wpdPosShell`, `nth_byte0_id`
`nthByte0Id`, `wbytes_one` `wbytesOne`, `R1` `AxLock3Writer.R1`, `astep_prog_plain_write_inv`
`astepProgPlainWriteInv`, `astep_prog_fence_inv` `astepProgFenceInv`, `w0_gmo_lt_w1`
`w0GmoLtW1`, `w_only_xwrite_before_rel` `wOnlyXwriteBeforeRel`, `w3_po_latest` `w3PoLatest`,
`w3_lbl3/wb/single/gd/gob/x_mem` `w3Lbl3/Wb/Single/Gd/Gob/XMem`, `w3_flow_eq` `w3FlowEq`,
`wpd_w3` `wpdW3`, `wpd_w2` `wpdW2`, `R0` `AxLock3Writer.R0`, `w1_lbl1/wb/single/gd`
`w1Lbl1/Wb/Single/Gd`, `w0_mem` `w0Mem`, `w1_flow_eq` `w1FlowEq`, `wpd_w1` `wpdW1`,
`gwrites_byte_of_rmw` `gwritesByteOfRmw`, `w0_lbl0/wb/single/gd` `w0Lbl0/Wb/Single/Gd`, `R1e`
`AxLock3Writer.R1e`, `R0e` `R0e`, `w3_flow_eq_e` `w3FlowEqE`, `wpd_w3_e` `wpdW3E`, `wpd_w2_e`
`wpdW2E`, `w1_flow_eq_e` `w1FlowEqE`, `wpd_w1_e` `wpdW1E`, `w0_read_det` `w0ReadDet`,
`astep_prog_write0_inv` `astepProgWrite0Inv`, `astep_prog_read0_vacuous`
`astepProgRead0Vacuous`, `w0_flow_eq_gen` `w0FlowEqGen`, `wpd_w0_write` `wpdW0Write`,
`wpd_w0_read` `wpdW0Read`, `wpd_writer_hart` `wpdWriterHart`, `w0_flow_eq_rel` `w0FlowEqRel`,
`wpd_w0_write_rel` `wpdW0WriteRel`, `wpd_w0_read_rel` `wpdW0ReadRel`, `wpd_writer_hart_rel`
`wpdWriterHartRel`.

**Dropped:** nothing (Rocq 64 definitions/lemmas; Lean 64 + 4 Lean-only).  **Not ported:** the `Print Assumptions` lines (the lint's axiom check
covers them).
-/
import Weak.AxLock3Wp2
import Weak.AxLock3Wp3
import Weak.AxLockWp

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std Iris.Std.PartialMap MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open Sail.ArchSem (FreeM)
open LeanRV64D
open Wlabel

/-- Lean-only: Rocq's local notation `TWPD s` — `tierAWpd` at the lock3s protocol, stuckness
`MaybeStuck`, hart `i`, the trivial postcondition. -/
def AxLock3Writer.twpd (GF : BundledGFunctors.{0,0,0}) [AxlogG GF Hent] [AxLockG GF]
    (hlc : HasLC) [InvGS_gen hlc GF] [AxannotGS GF] (L x : Int) (GD : Gdexec) (nm : lock3N)
    (i : Agent) (s : Athread) : IProp GF :=
  @tierAWpd GF hlc _ _ lockAxpol GD lock3N lock3ObSt0 (lock3ObStInterp0 L x) nm s .MaybeStuck i
    (fun _ => iprop(True))

/-- Lean-only: the annotation map after detaching at `e` and allocating at `e'`. -/
theorem AxLock3Writer.annotEq {GF : BundledGFunctors} (na : Mea GF) (e e' : Geid)
    (R P : IProp GF) :
    insert (insert na e R) e' P =
      PartialMap.union (PartialMap.union {[e' := P]} {[e := R]}) na := by
  rw [insertUnionSingletonL (M := GMapF Geid), insertUnionSingletonL (M := GMapF Geid)]
  exact mapUnionAssoc (M := GMapF Geid)

section writer

variable {GF : BundledGFunctors.{0,0,0}} [AxlogG GF Hent] [AxLockG GF] (L x : Int)
variable {hlc : HasLC} [InvGS_gen hlc GF] [AxannotGS GF] (GD : Gdexec) (nm : lock3N)
variable (Lpa xpa : PAddr) (cpu : CPU) (i : Agent) (t : Nat) (old v : BitVec 8)

/-- Lean-only: `axGA2`'s graph pin is the pure equation. -/
theorem AxLock3Writer.gconstPure (GD' : Gdexec) :
    AxirisG.gconstInterp (self := axGA2Lock3 (GF := GF) L x GD nm) GD' ⊢ iprop(⌜GD' = GD⌝) :=
  .rfl

/-- Lean-only: `axGA2`'s local interpretation is `True`. -/
theorem AxLock3Writer.localTriv (GD' : Gdexec) (j : Agent) (k : Nat) :
    ⊢ AxirisG.localInterp (self := axGA2Lock3 (GF := GF) L x GD nm) GD' j k () :=
  true_intro

/-! ## 0. The writer's own monad states (register-generic) -/

def wM4 : SailM Unit :=
  .impure (.ok (.memWrite 1 64 (l3pWreq l3pAkP Lpa b0))) (fun _ => .pure ())
def wM3 : SailM Unit :=
  .impure (.ok (.barrier .Barrier_RISCV_rw_w)) (fun _ => wM4 Lpa)
def wM2 : SailM Unit :=
  .impure (.ok (.memWrite 1 64 (l3pWreq l3pAkP xpa v))) (fun _ => wM3 Lpa)
def wM1 : SailM Unit :=
  .impure (.ok (.memWrite 1 64 (l3pWreq l3pAkXpl Lpa b1))) (fun _ => wM2 Lpa xpa v)
def wM0 : SailM Unit :=
  .impure (.ok (.memRead 1 64 (l3pRreq l3pAkXaq Lpa))) (fun _ => wM1 Lpa xpa v)

/-! ## 1. Generic helpers -/

omit [AxlogG GF Hent] [AxLockG GF] in
/-- 1.1 Recovering a single `lobp`-predecessor's deposit from a persistent annotation
snapshot. -/
theorem naSplittingWfSnap (e' : Geid) (P : IProp GF) (sLob : GSet Geid) (na : Mea GF) :
    e' ∈ sLob →
    ⊢ AxAnnot.annotInterp na -∗ AxAnnot.annotOwn e' P -∗
      naSplittingWf sLob na {[e' := P]} {[e' := iprop(emp)]} := by
  intro Hin
  iintro Hannot Hsnap
  icases annotAgree na e' P $$ Hannot Hsnap with ⟨%Hdom, Hw⟩
  obtain ⟨Q, HQ⟩ := Option.isSome_iff_exists.1 (elemOfDom.1 Hdom)
  have hconv : AxWp.fromOption (fun P' => iprop(▷ □ (P' -∗ P))) iprop(emp) (get? na e') ⊢
      iprop(▷ □ (Q -∗ P)) := by
    rw [HQ]
    exact .rfl
  ihave Hw := hconv $$ Hw
  unfold naSplittingWf
  isplitr
  · ipureintro
    rw [domSingleton]
    exact singletonSubseteqL.2 Hin
  · iapply (BigSepM2.bigSepM2_singleton _ e' P iprop(emp)).2
    simp only [HQ, AxWp.fromOption]
    inext
    icases Hw with #Hw
    imodintro
    iintro HQ'
    isplitl [HQ']
    · iapply Hw $$ HQ'
    · iempintro

/-- 1.1b `wpSkipStep` from a later-guarded continuation. -/
theorem wpdSkipStepOfLater (k' : Nat) (Ψ : IProp GF) :
    ⊢ ▷ Ψ -∗ @wpSkipStep GF (axGA2Lock3 L x GD nm) GD i k' Ψ := by
  unfold wpSkipStep
  iintro HΨ %na Hna
  imodintro
  inext
  imodintro
  iexists ()
  isplitl [Hna]
  · iexact Hna
  isplitr
  · iapply AxLock3Writer.localTriv
  · iexact HΨ

/-- 1.1b' A flow equation whose `flowIn` is a singleton holding an EXISTENTIAL resource, from
the per-witness equations; the witness is destructed locally. -/
theorem flowEqDynExistsSingleton {A : Type} (k : Geid) (Pk Q : A → IProp GF) (e : Geid)
    (sOb0 : GSet Geid) :
    (∀ a : A, ⊢ @flowEqDyn hlc GF _ (axGA2Lock3 L x GD nm) GD e sOb0 {[k := Pk a]} (Q a)) →
    ⊢ @flowEqDyn hlc GF _ (axGA2Lock3 L x GD nm) GD e sOb0 {[k := iprop(∃ a, Pk a)]}
        iprop(∃ a, Q a) := by
  intro HQ
  unfold flowEqDyn
  iintro %σ %sOb %Hsub %Hnin Hob Hflow
  ihave Hflow := (BigSepM.bigSepM_singleton (M := GMapF Geid)).1 $$ Hflow
  icases Hflow with ⟨%a, Hpa⟩
  have HQa := HQ a
  unfold flowEqDyn at HQa
  ihave HQa := HQa
  imod HQa $$ %σ %sOb %Hsub %Hnin Hob [Hpa] with H
  · iapply (BigSepM.bigSepM_singleton (M := GMapF Geid)).2
    iexact Hpa
  imodintro
  inext
  imod H with ⟨%σ', Hob', Hpost⟩
  imodintro
  iexists σ'
  iframe Hob'
  iexists a
  iexact Hpost

/-- 1.1c The shape of a program step past the row end: administrative, position kept. -/
theorem astepProgRowEndShape (row : List Lbl) (s : Athread) (l : Wlabel) (s' : Athread)
    (Hnone : row[s.atK]? = none) :
    AxOpsem.astepProg row s l s' →
    AxOpsem.lbAdminAx true l ∧ s'.atK = s.atK ∧ ∃ d d', pstepProg s.atP d l s'.atP d' := by
  intro h
  cases h with
  | AStepAdmin _ _ d _ _ d' hadm hs => exact ⟨hadm, rfl, d, d', hs⟩
  | AStepWrite _ _ _ _ _ _ _ hlk _ _ _ _ =>
    simp only at Hnone
    rw [Hnone] at hlk
    cases hlk
  | AStepFence _ _ _ _ _ _ _ hlk _ _ _ =>
    simp only at Hnone
    rw [Hnone] at hlk
    cases hlk

theorem lbAdminWlWdataNone (l : Wlabel) : AxOpsem.lbAdminAx true l → wlWdata l = none := by
  cases l <;> simp [AxOpsem.lbAdminAx, wlWdata]

/-- 1.2 THE ROW-END TRIVIALITY: past the writer's row, every step is administrative and the
postcondition is `True`; one Löb over the whole program state. -/
theorem wpdRowEndTriv (k0 : Nat) (Hend : (AxOpsem.grow GD i).length ≤ k0) (p : Pexv6) :
    ⊢ AxLock3Writer.twpd GF hlc L x GD nm i ⟨p, k0⟩ := by
  have Hnone : (AxOpsem.grow GD i)[k0]? = none := List.getElem?_eq_none Hend
  have H : ⊢ ∀ p : Pexv6, AxLock3Writer.twpd GF hlc L x GD nm i ⟨p, k0⟩ := by
    iloeb as IH
    iintro %p
    unfold AxLock3Writer.twpd tierAWpd
    iapply (@AxWpD.wpdMUnfoldStep hlc GF _ (axGA2Lock3 L x GD nm) lockAxpol rvwmoCatConsistent
      .MaybeStuck i _ _).2
    isplit
    · iapply (@progressOblMaybestuck GF (axGA2Lock3 L x GD nm) lockAxpol i _).2
      itrivial
    unfold wpdMPreStepDef
    iintro %GD' %ls ⟨%Hc, #Hg, -⟩
    ihave %Hg := AxLock3Writer.gconstPure L x GD nm GD' $$ Hg
    subst GD'
    isplit
    · iintro %id %K %Hst
      obtain ⟨lb, Hlb, -⟩ := Hst
      simp only at Hlb
      rw [Hnone] at Hlb
      cases Hlb
    isplit
    · iintro %l %s' %Hst %-
      obtain ⟨Hadm, Hk', -⟩ := astepProgRowEndShape _ _ l s' Hnone Hst
      rw [lbAdminWlWdataNone l Hadm]
      obtain ⟨p', k1⟩ := s'
      simp only at Hk'
      subst Hk'
      iapply wpdSkipStepOfLater (GF := GF) L x GD nm i
      inext
      iapply IH $$ %p'
    isplit
    · iintro %s' %Hw
      obtain ⟨p', k1⟩ := s'
      obtain ⟨Hk, -⟩ := Hw
      simp only at Hk
      subst Hk
      iapply wpdSkipStepOfLater (GF := GF) L x GD nm i
      inext
      iapply IH $$ %p'
    · iintro %-
      iapply (@postLiftingTrue GF (axGA2Lock3 L x GD nm) lockAxpol _ i _ true_intro)
  iapply H $$ %p

/-! ## 2. W4 — the row end, at the writer's own row length -/

theorem wpdW4 (p : Pexv6) :
    ⊢ AxLock3Writer.twpd GF hlc L x GD nm i ⟨p, (AxOpsem.grow GD i).length⟩ :=
  wpdRowEndTriv L x GD nm i _ (Nat.le_refl _) p

/-! ## 3. Shared plumbing for the interior positions -/

theorem gwritesByteOfStore (e : Geid) (base : Int) (b : BitVec 8) (cls : WmClass) :
    gxLbl GD.gdG e = some (.LStore false base [b] cls) →
    gwritesByte GD.gdG e base b ∧ (∀ a' v', gwritesByte GD.gdG e a' v' → a' = base) := by
  intro Hlbl
  refine ⟨⟨_, base, [b], 0, Hlbl, rfl, rfl, by simp [accAddr]⟩, ?_⟩
  rintro a' v' ⟨l, base', vs', j, Hl, Hwr, Hvs, Hacc⟩
  rw [Hlbl, Option.some.injEq] at Hl
  subst Hl
  simp only [lbWr, Option.some.injEq, Prod.mk.injEq] at Hwr
  obtain ⟨rfl, rfl⟩ := Hwr
  cases j with
  | zero => simp only [accAddr] at Hacc; omega
  | succ j => simp at Hvs

theorem gacqPoGobCat (e1 e2 : Geid) : gacqPo GD.gdG e1 e2 → gobCat GD e1 e2 :=
  fun H => gobCatStep _ _ _ (.inl (.inl (.inr (.inr (.inr (.inr (.inl H)))))))

theorem gfenceCoversGobCat (e1 e2 : Geid) : gfenceCovers GD.gdG e1 e2 → gobCat GD e1 e2 :=
  fun H => gobCatStep _ _ _ (.inl (.inl (.inr (.inr (.inr (.inl H))))))

/-- The shell: clause (a) vacuous (the row item is not read-shaped), clause (c) the wire
self-loop (Löb over the register file), clause (d) trivial; clause (b) supplied as `Hb`. -/
theorem wpdPosShell (P : IProp GF) (k : Nat) (m : SailM Unit)
    (Hrowk_nonread : ∀ lb, (AxOpsem.grow GD i)[k]? = some lb → aidentRd (aident lb) = none)
    (Hb : ∀ (rs : RegFile) (l : Wlabel) (s' : Athread),
      AxOpsem.astepProg (AxOpsem.grow GD i) ⟨.PHart cpu m rs none ibNone, k⟩ l s' →
      P ⊢ match wlWdata l with
        | some data =>
            @wpEvStep hlc GF _ (axGA2Lock3 L x GD nm) lockAxpol Unit GD i k (fun _ => True)
              (fun _ => graphData GD (i, k) = some data) (fun _ => s'.atK)
              (fun _ => AxLock3Writer.twpd GF hlc L x GD nm i s')
        | none => @wpSkipStep GF (axGA2Lock3 L x GD nm) GD i s'.atK
            (AxLock3Writer.twpd GF hlc L x GD nm i s')) :
    P ⊢ ∀ rs : RegFile,
      AxLock3Writer.twpd GF hlc L x GD nm i ⟨.PHart cpu m rs none ibNone, k⟩ := by
  have H : ⊢ ∀ rs : RegFile, P -∗
      AxLock3Writer.twpd GF hlc L x GD nm i ⟨.PHart cpu m rs none ibNone, k⟩ := by
    iloeb as IH
    iintro %rs HP
    unfold AxLock3Writer.twpd tierAWpd
    iapply (@AxWpD.wpdMUnfoldStep hlc GF _ (axGA2Lock3 L x GD nm) lockAxpol rvwmoCatConsistent
      .MaybeStuck i _ _).2
    isplit
    · iapply (@progressOblMaybestuck GF (axGA2Lock3 L x GD nm) lockAxpol i _).2
      itrivial
    unfold wpdMPreStepDef
    iintro %GD' %ls ⟨%Hc, #Hg, -⟩
    ihave %Hg := AxLock3Writer.gconstPure L x GD nm GD' $$ Hg
    subst GD'
    isplit
    · iintro %id %K %Hst
      obtain ⟨lb, Hlk, Hid, Hsome, -⟩ := Hst
      have Hnone : aidentRd id = none := by rw [← Hid]; exact Hrowk_nonread lb Hlk
      rw [Hnone] at Hsome
      cases Hsome
    isplit
    · iintro %l %s' %Hst %-
      have Hb' := Hb rs l s' Hst
      unfold AxLock3Writer.twpd tierAWpd at Hb'
      dsimp only
      iapply Hb' $$ HP
    isplit
    · iintro %s' %Hw
      obtain ⟨rs', rfl⟩ := l3pAwireRsOnly cpu m rs none ibNone k s' Hw
      iapply wpdSkipStepOfLater (GF := GF) L x GD nm i
      inext
      iapply IH $$ %rs' HP
    · iintro %-
      iapply (@postLiftingTrue GF (axGA2Lock3 L x GD nm) lockAxpol _ i _ true_intro)
  iintro HP %rs
  iapply H $$ %rs HP

theorem nthByte0Id (b : BitVec 8) : nthByte (n := 1) b 0 = b := by
  apply BitVec.eq_of_toNat_eq
  simp only [nthByte, BitVec.extractLsb'_toNat, Nat.mul_zero, Nat.shiftRight_zero]
  exact Nat.mod_eq_of_lt b.isLt

theorem wbytesOne (b : BitVec 8) : WeakInterpProj.wbytes 1 b = [b] := l3pWbytes1 b

/-! ## 4. W3 — the release store (position 3), and W2 — the fence (position 2) -/

/-- The `x`-write's deposit, parametric in the `x`-history `Hl` before it. -/
def AxLock3Writer.R1 (Hl : List Hent) : IProp GF :=
  iprop(⌜graphData GD (i, 1) = some [v]⌝ ∗
    tokTie GD nm.1 x (Hl ++ [((i, 1), v)]) {[(i, 1) := (1 : Qp)]} ∗
    ⌜histXWf x GD (Hl ++ [((i, 1), v)])⌝)

theorem astepProgPlainWriteInv (pa : PAddr) (Hdev : devAddr pa = false) (val : BitVec 8)
    (KK : Result (Option Bool) Arch.abort → SailM Unit) (rs : RegFile) (k : Nat) (s : Athread)
    (Heqp : s.atP =
      .PHart cpu (.impure (.ok (.memWrite 1 64 (l3pWreq l3pAkP pa val))) KK) rs none ibNone)
    (Heqk : s.atK = k) (l : Wlabel) (s' : Athread) :
    AxOpsem.astepProg (AxOpsem.grow GD i) s l s' →
    l = LStore false (paZ pa) (WeakInterpProj.wbytes 1 val)
          (depsAsrc (depsOfIb ibNone.ibBits)) (depsVsrc (depsOfIb ibNone.ibBits)) ∧
    s' = ⟨.PHart cpu (KK (.Ok (some true))) rs none ibNone, k + 1⟩ := by
  intro h
  cases h with
  | AStepAdmin p k0 d l0 p' d' hadm hst =>
    simp only at Heqp Heqk
    subst Heqp Heqk
    obtain ⟨rfl, -, -⟩ := l3pWritePlainDet cpu pa Hdev val KK rs ibNone d l p' d' hst
    simp [AxOpsem.lbAdminAx] at hadm
  | AStepWrite p k0 d l0 lb p' d' _ _ _ _ hst =>
    simp only at Heqp Heqk
    subst Heqp Heqk
    obtain ⟨rfl, rfl, -⟩ := l3pWritePlainDet cpu pa Hdev val KK rs ibNone d l p' d' hst
    exact ⟨rfl, rfl⟩
  | AStepFence p k0 d l0 lb p' d' _ hfe _ hst =>
    simp only at Heqp Heqk
    subst Heqp Heqk
    obtain ⟨rfl, -, -⟩ := l3pWritePlainDet cpu pa Hdev val KK rs ibNone d l p' d' hst
    simp [wlFence] at hfe

/-- 4.1 The fence step's inversion. -/
theorem astepProgFenceInv (KK : Unit → SailM Unit) (rs : RegFile) (k : Nat) (s : Athread)
    (Heqp : s.atP = .PHart cpu (.impure (.ok (.barrier .Barrier_RISCV_rw_w)) KK) rs none ibNone)
    (Heqk : s.atK = k) (l : Wlabel) (s' : Athread) :
    AxOpsem.astepProg (AxOpsem.grow GD i) s l s' →
    l = LFence true true false true ∧ s' = ⟨.PHart cpu (KK ()) rs none ibNone, k + 1⟩ := by
  intro h
  cases h with
  | AStepAdmin p k0 d l0 p' d' hadm hst =>
    simp only at Heqp Heqk
    subst Heqp Heqk
    obtain ⟨rfl, -, -⟩ := l3pFenceDet cpu KK rs ibNone d l p' d' hst
    simp [AxOpsem.lbAdminAx] at hadm
  | AStepWrite p k0 d l0 lb p' d' _ hwr _ _ hst =>
    simp only at Heqp Heqk
    subst Heqp Heqk
    obtain ⟨rfl, -, -⟩ := l3pFenceDet cpu KK rs ibNone d l p' d' hst
    simp [wlWr] at hwr
  | AStepFence p k0 d l0 lb p' d' _ _ _ hst =>
    simp only at Heqp Heqk
    subst Heqp Heqk
    obtain ⟨rfl, rfl, -⟩ := l3pFenceDet cpu KK rs ibNone d l p' d' hst
    exact ⟨rfl, rfl⟩

/-- 4.2a The acquire is `gmo`-before the `x`-write (rule 5 under `gppoCatGmo`). -/
theorem w0GmoLtW1 (Hrow : AxOpsem.grow GD i = l3pWRow Lpa xpa t old v)
    (Hcons : rvwmoCatConsistent GD) : gmoLt GD.gdG (i, 0) (i, 1) :=
  Hcons.2.1 _ _ (.inl (.inr (.inr (.inr (.inr (.inl
    (l3pWGacqPoXwrite Lpa xpa GD i t old v Hrow)))))))

/-- 4.2b The only `x`-write `gpo`-before the release is the writer's own. -/
theorem wOnlyXwriteBeforeRel (hxy : x ≠ L) (HLeq : L = l3pLbase Lpa) (Hxeq : x = l3pXbase xpa)
    (Hrow : AxOpsem.grow GD i = l3pWRow Lpa xpa t old v) (w' : Geid) (v' : BitVec 8) :
    gwritesByte GD.gdG w' x v' → WeakRvwmoGraph.gpo GD.gdG w' (i, 3) →
    w' = (i, 1) ∧ v' = v := by
  intro Hwb ⟨Heq1, Hlt, _, _⟩
  obtain ⟨j, k⟩ := w'
  simp only at Heq1 Hlt
  subst Heq1
  match k, Hlt with
  | 0, _ =>
    exfalso
    obtain ⟨l, base, vs, jj, Hl, Hwr, Hvs, Hacc⟩ := Hwb
    rw [l3pWLbl0 Lpa xpa GD j t old v Hrow, Option.some.injEq] at Hl
    subst Hl
    simp only [lbWr, Option.some.injEq, Prod.mk.injEq] at Hwr
    obtain ⟨rfl, rfl⟩ := Hwr
    cases jj with
    | zero =>
      simp only [accAddr] at Hacc
      exact hxy (by rw [HLeq]; omega)
    | succ jj => simp at Hvs
  | 1, _ =>
    refine ⟨rfl, ?_⟩
    have Hwb1 : gwritesByte GD.gdG (j, 1) x v := by
      rw [Hxeq]
      exact (gwritesByteOfStore GD (j, 1) (l3pXbase xpa) v .WCplain
        (l3pWLbl1 Lpa xpa GD j t old v Hrow)).1
    exact gwritesByteDet _ _ _ _ _ Hwb Hwb1
  | 2, _ =>
    exfalso
    obtain ⟨l, base, vs, jj, Hl, Hwr, Hvs, Hacc⟩ := Hwb
    rw [l3pWLbl2 Lpa xpa GD j t old v Hrow, Option.some.injEq] at Hl
    subst Hl
    simp [lbWr] at Hwr
  | k + 3, Hlt => exact absurd Hlt (by omega)

/-- 4.2c The po-latest clause at the release, for any acquired history. -/
theorem w3PoLatest (hxy : x ≠ L) (HLeq : L = l3pLbase Lpa) (Hxeq : x = l3pXbase xpa)
    (Hrow : AxOpsem.grow GD i = l3pWRow Lpa xpa t old v) (Hacq : List Hent) :
    lockHhPoLatest x GD (Hacq ++ [((i, 1), v)]) (i, 3) := by
  intro w' v' Hwb Hpo
  obtain ⟨rfl, rfl⟩ := wOnlyXwriteBeforeRel L x GD Lpa xpa i t old v hxy HLeq Hxeq Hrow w' v'
    Hwb Hpo
  left
  simp

theorem w3Lbl3 (HLeq : L = l3pLbase Lpa) (Hrow : AxOpsem.grow GD i = l3pWRow Lpa xpa t old v) :
    gxLbl GD.gdG (i, 3) = some (.LStore false L [b0] .WCplain) := by
  rw [HLeq]
  exact l3pWLbl3 Lpa xpa GD i t old v Hrow

theorem w3Wb (HLeq : L = l3pLbase Lpa) (Hrow : AxOpsem.grow GD i = l3pWRow Lpa xpa t old v) :
    gwritesByte GD.gdG (i, 3) L b0 :=
  (gwritesByteOfStore GD (i, 3) L b0 .WCplain (w3Lbl3 L GD Lpa xpa i t old v HLeq Hrow)).1

theorem w3Single (HLeq : L = l3pLbase Lpa)
    (Hrow : AxOpsem.grow GD i = l3pWRow Lpa xpa t old v) :
    ∀ a' v', gwritesByte GD.gdG (i, 3) a' v' → a' = L :=
  (gwritesByteOfStore GD (i, 3) L b0 .WCplain (w3Lbl3 L GD Lpa xpa i t old v HLeq Hrow)).2

theorem w3Gd (HLeq : L = l3pLbase Lpa) (Hrow : AxOpsem.grow GD i = l3pWRow Lpa xpa t old v) :
    graphData GD (i, 3) = some [b0] := by
  simp only [graphData, w3Lbl3 L GD Lpa xpa i t old v HLeq Hrow, Option.bind_some, lblData]

theorem w3Gob (Hrow : AxOpsem.grow GD i = l3pWRow Lpa xpa t old v) :
    gobCat GD (i, 1) (i, 3) :=
  gfenceCoversGobCat GD _ _ (l3pWGfenceCoversXwriteRel Lpa xpa GD i t old v Hrow)

theorem w3XMem (Hrow : AxOpsem.grow GD i = l3pWRow Lpa xpa t old v) :
    gmemB GD.gdG (i, 1) = true := by
  simp only [gmemB, l3pWLbl1 Lpa xpa GD i t old v Hrow]
  rfl

/-- 4.3 The release's flow equation at `naUsed := {[(i,1) := R1 Hl]}`. -/
theorem w3FlowEq (hxy : x ≠ L) (HLeq : L = l3pLbase Lpa) (Hxeq : x = l3pXbase xpa)
    (Hrow : AxOpsem.grow GD i = l3pWRow Lpa xpa t old v) (Hcons : rvwmoCatConsistent GD)
    (Hl : List Hent) :
    ⊢ @flowEqDyn hlc GF _ (axGA2Lock3 L x GD nm) GD (i, 3) (lockPolS GD (i, 3))
        {[(i, 1) := AxLock3Writer.R1 (GF := GF) x GD nm i v Hl]}
        iprop(True ∗ ⌜graphData GD (i, 3) = some [b0]⌝) := by
  have Hr := lockRelFlowEq3A (hlc := hlc) L x GD nm GD (i, 3) (i, 1) (Hl ++ [((i, 1), v)])
    {[(i, 1) := AxLock3Writer.R1 (GF := GF) x GD nm i v Hl]} Hcons
    (w3Wb L GD Lpa xpa i t old v HLeq Hrow)
    (w3Single L GD Lpa xpa i t old v HLeq Hrow) (w3Gob GD Lpa xpa i t old v Hrow)
  iapply (@flowEqDynMono hlc GF _ (axGA2Lock3 L x GD nm) lockAxpol GD (i, 3) (lockPolS GD (i, 3))
    _ iprop(True) iprop(True ∗ ⌜graphData GD (i, 3) = some [b0]⌝))
  · inext
    iintro -
    isplitr
    · itrivial
    · ipureintro
      exact w3Gd L GD Lpa xpa i t old v HLeq Hrow
  · iapply Hr
    iintro Hin
    ihave Hin := (BigSepM.bigSepM_singleton (M := GMapF Geid)).1 $$ Hin
    iunfold AxLock3Writer.R1 at Hin
    icases Hin with ⟨-, Htie, %Hxwf1⟩
    isplitl [Htie]
    · iapply tokTieXTok
      iexact Htie
    · ipureintro
      exact ⟨Hxwf1, w3PoLatest L x GD Lpa xpa i t old v hxy HLeq Hxeq Hrow Hl⟩

/-! ## 5. W3 assembled, and W2 -/

theorem wpdW3 (hxy : x ≠ L) (HLram : devAddr Lpa = false) (HLeq : L = l3pLbase Lpa)
    (Hxeq : x = l3pXbase xpa) (Hrow : AxOpsem.grow GD i = l3pWRow Lpa xpa t old v)
    (Hcons : rvwmoCatConsistent GD) (Hl : List Hent) :
    AxAnnot.annotOwn (i, 1) (AxLock3Writer.R1 (GF := GF) x GD nm i v Hl) ⊢
      ∀ rs : RegFile,
        AxLock3Writer.twpd GF hlc L x GD nm i ⟨.PHart cpu (wM4 Lpa) rs none ibNone, 3⟩ := by
  apply wpdPosShell L x GD nm cpu i _ 3 (wM4 Lpa)
  · intro lb Hlk
    rw [Hrow] at Hlk
    simp only [l3pWRow, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq]
      at Hlk
    subst Hlk
    rfl
  · intro rs l s' Hstep
    obtain ⟨rfl, rfl⟩ := astepProgPlainWriteInv GD cpu i Lpa HLram b0 (fun _ => .pure ()) rs 3
      ⟨.PHart cpu (wM4 Lpa) rs none ibNone, 3⟩ rfl rfl l s' Hstep
    simp only [wlWdata, l3pWbytes1]
    unfold wpEvStep naAtProgress
    iintro HP %na ⟨%Hprog, Hannot⟩
    have Hin1 : (i, 1) ∈ (FiniteMap.dom_set na : GSet Geid) := by
      have h : (i, 1) ∈ eidsBefore GD i 3 :=
        (elemOfEidsBefore GD i 3 _).2 ⟨rfl, by simp, w3XMem GD Lpa xpa i t old v Hrow⟩
      rw [← Hprog] at h
      exact (elemOfFilter.1 h).2
    obtain ⟨P', HP'⟩ := Option.isSome_iff_exists.1 (elemOfDom.1 Hin1)
    have Hdet : ⊢ AxAnnot.annotInterp na -∗
        AxAnnot.annotOwn (i, 1) (AxLock3Writer.R1 (GF := GF) x GD nm i v Hl) ==∗
        ∃ R, AxAnnot.annotInterp (insert na (i, 1) R) ∗
          iprop(▷ □ (P' -∗ AxLock3Writer.R1 (GF := GF) x GD nm i v Hl ∗ R)) := by
      have h := annotDetach na (i, 1) (AxLock3Writer.R1 (GF := GF) x GD nm i v Hl)
      rw [HP'] at h
      exact h
    imod Hdet $$ Hannot HP with ⟨%R, Hannot', Hwand⟩
    ihave Hfeq := w3FlowEq (hlc := hlc) L x GD nm Lpa xpa i t old v hxy HLeq Hxeq Hrow Hcons Hl
    have Hnin : (i, 3) ∉ (FiniteMap.dom_set (insert na (i, 1) R) : GSet Geid) := by
      rw [domInsert, elemOfUnion, elemOfSingleton]
      rintro (Heq | Hik)
      · simp at Heq
      · have Hf : (i, 3) ∈ FiniteSet.filter (fun e : Geid => decide (e.1 = i))
            (FiniteMap.dom_set na : GSet Geid) := elemOfFilter.2 ⟨by simp, Hik⟩
        rw [Hprog, elemOfEidsBefore] at Hf
        exact Nat.lt_irrefl _ Hf.2.1
    imod (annotAlloc (insert na (i, 1) R) (i, 3) iprop(True) Hnin) $$ Hannot' with ⟨Hannot'', -⟩
    imodintro
    inext
    imodintro
    iexists (), iprop(True), {[(i, 1) := AxLock3Writer.R1 (GF := GF) x GD nm i v Hl]},
      {[(i, 1) := R]}, ()
    isplitr
    · ipureintro
      trivial
    isplitl [Hwand]
    · unfold naSplittingWf
      isplitr
      · ipureintro
        rw [domSingleton]
        exact singletonSubseteqL.2 (l3pWXwriteInLobpRel Lpa xpa GD i t old v Hrow Hcons.1)
      · iapply (BigSepM2.bigSepM2_singleton _ (i, 1)
          (AxLock3Writer.R1 (GF := GF) x GD nm i v Hl) R).2
        simp only [HP', AxWp.fromOption]
        inext
        iexact Hwand
    isplitl [Hfeq]
    · iexact Hfeq
    isplitl [Hannot'']
    · rw [← AxLock3Writer.annotEq]
      iexact Hannot''
    isplitr
    · iapply AxLock3Writer.localTriv
    · iapply wpdRowEndTriv L x GD nm i (3 + 1) (by rw [Hrow]; simp [l3pWRow])

theorem wpdW2 (hxy : x ≠ L) (HLram : devAddr Lpa = false) (HLeq : L = l3pLbase Lpa)
    (Hxeq : x = l3pXbase xpa) (Hrow : AxOpsem.grow GD i = l3pWRow Lpa xpa t old v)
    (Hcons : rvwmoCatConsistent GD) (Hl : List Hent) :
    AxAnnot.annotOwn (i, 1) (AxLock3Writer.R1 (GF := GF) x GD nm i v Hl) ⊢
      ∀ rs : RegFile,
        AxLock3Writer.twpd GF hlc L x GD nm i ⟨.PHart cpu (wM3 Lpa) rs none ibNone, 2⟩ := by
  apply wpdPosShell L x GD nm cpu i _ 2 (wM3 Lpa)
  · intro lb Hlk
    rw [Hrow] at Hlk
    simp only [l3pWRow, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq]
      at Hlk
    subst Hlk
    rfl
  · intro rs l s' Hstep
    obtain ⟨rfl, rfl⟩ := astepProgFenceInv GD cpu i (fun _ => wM4 Lpa) rs 2
      ⟨.PHart cpu (wM3 Lpa) rs none ibNone, 2⟩ rfl rfl l s' Hstep
    simp only [wlWdata]
    iintro HP
    iapply wpdSkipStepOfLater (GF := GF) L x GD nm i
    inext
    ihave H := (wpdW3 (hlc := hlc) L x GD nm Lpa xpa cpu i t old v hxy HLram HLeq Hxeq Hrow Hcons
      Hl) $$ HP
    iapply H

/-! ## 6. W1 — the `x`-write (position 1) -/

/-- The acquire's deposit: a bare fresh `histAuth` on genesis (tagged `Hl = []`), or a re-tied
`tokTie` on an ordinary acquire; with the history's well-formedness. -/
def AxLock3Writer.R0 (Hl : List Hent) : IProp GF :=
  iprop(((⌜Hl = []⌝ ∗ histAuth nm.1 x 1 Hl) ∨
      tokTie GD nm.1 x Hl {[(i, 0) := (1 : Qp)]}) ∗
    ⌜histXWf x GD Hl⌝)

theorem w1Lbl1 (Hxeq : x = l3pXbase xpa) (Hrow : AxOpsem.grow GD i = l3pWRow Lpa xpa t old v) :
    gxLbl GD.gdG (i, 1) = some (.LStore false x [v] .WCplain) := by
  rw [Hxeq]
  exact l3pWLbl1 Lpa xpa GD i t old v Hrow

theorem w1Wb (Hxeq : x = l3pXbase xpa) (Hrow : AxOpsem.grow GD i = l3pWRow Lpa xpa t old v) :
    gwritesByte GD.gdG (i, 1) x v :=
  (gwritesByteOfStore GD (i, 1) x v .WCplain (w1Lbl1 x GD Lpa xpa i t old v Hxeq Hrow)).1

theorem w1Single (Hxeq : x = l3pXbase xpa)
    (Hrow : AxOpsem.grow GD i = l3pWRow Lpa xpa t old v) :
    ∀ a' v', gwritesByte GD.gdG (i, 1) a' v' → a' = x :=
  (gwritesByteOfStore GD (i, 1) x v .WCplain (w1Lbl1 x GD Lpa xpa i t old v Hxeq Hrow)).2

theorem w1Gd (Hxeq : x = l3pXbase xpa) (Hrow : AxOpsem.grow GD i = l3pWRow Lpa xpa t old v) :
    graphData GD (i, 1) = some [v] := by
  simp only [graphData, w1Lbl1 x GD Lpa xpa i t old v Hxeq Hrow, Option.bind_some, lblData]

theorem w0Mem (Hrow : AxOpsem.grow GD i = l3pWRow Lpa xpa t old v) :
    gmemB GD.gdG (i, 0) = true := by
  simp only [gmemB, l3pWLbl0 Lpa xpa GD i t old v Hrow]
  rfl

/-- 6.2 The `x`-write's flow equation at `naUsed := {[(i,0) := R0 Hl]}`. -/
theorem w1FlowEq (hxy : x ≠ L) (Hxeq : x = l3pXbase xpa)
    (Hrow : AxOpsem.grow GD i = l3pWRow Lpa xpa t old v) (Hcons : rvwmoCatConsistent GD)
    (Hl : List Hent) :
    ⊢ @flowEqDyn hlc GF _ (axGA2Lock3 L x GD nm) GD (i, 1) (lockPolS GD (i, 1))
        {[(i, 0) := AxLock3Writer.R0 (GF := GF) x GD nm i Hl]}
        iprop(AxLock3Writer.R1 (GF := GF) x GD nm i v Hl ∗
          ⌜graphData GD (i, 1) = some [v]⌝) := by
  have Hx := lockXwriteFlowEq3ATie (hlc := hlc) L x GD nm hxy GD (i, 1) v Hl
    {[(i, 0) := AxLock3Writer.R0 (GF := GF) x GD nm i Hl]} [v]
    (w1Wb x GD Lpa xpa i t old v Hxeq Hrow) (w1Single x GD Lpa xpa i t old v Hxeq Hrow)
    (w1Gd x GD Lpa xpa i t old v Hxeq Hrow)
  iapply (@flowEqDynMono hlc GF _ (axGA2Lock3 L x GD nm) lockAxpol GD (i, 1) (lockPolS GD (i, 1))
    _ iprop(⌜graphData GD (i, 1) = some [v]⌝ ∗
      tokTie GD nm.1 x (Hl ++ [((i, 1), v)]) {[(i, 1) := (1 : Qp)]} ∗
      ⌜histXWf x GD (Hl ++ [((i, 1), v)])⌝)
    iprop(AxLock3Writer.R1 (GF := GF) x GD nm i v Hl ∗ ⌜graphData GD (i, 1) = some [v]⌝))
  · inext
    iintro ⟨%Hp, Ht, %Hxwf1⟩
    isplitl [Ht]
    · unfold AxLock3Writer.R1
      isplitr
      · ipureintro
        exact Hp
      isplitl [Ht]
      · iexact Ht
      · ipureintro
        exact Hxwf1
    · ipureintro
      exact Hp
  · iapply Hx
    iintro Hin
    ihave Hin := (BigSepM.bigSepM_singleton (M := GMapF Geid)).1 $$ Hin
    iunfold AxLock3Writer.R0 at Hin
    icases Hin with ⟨Hor, %Hxwf⟩
    icases Hor with (⟨%Heq, Hauth⟩ | Htie)
    · isplitl [Hauth]
      · iexact Hauth
      · ipureintro
        refine ⟨Hxwf, ?_⟩
        intro wlast vlast Hlast
        rw [Heq] at Hlast
        cases Hlast
    · iunfold tokTie at Htie
      icases Htie with ⟨Htok, %Htieb⟩
      isplitl [Htok]
      · iapply (tokSingleton nm.1 x Hl (i, 0) (1 : Qp)).1
        iexact Htok
      · ipureintro
        refine ⟨Hxwf, ?_⟩
        intro wlast vlast Hlast
        have Htb : tieBase GD.gdG (Hl.map Prod.fst) (i, 0) := by
          apply Htieb
          rw [domSingleton]
          exact elemOfSingleton.2 rfl
        have Hfst := hentLastFst Hl wlast vlast Hlast
        rcases Htb with Heq0 | ⟨wl0, Hlast0, Hmo0⟩
        · rw [Hfst, Option.some.injEq] at Heq0
          subst Heq0
          exact w0GmoLtW1 GD Lpa xpa i t old v Hrow Hcons
        · rw [Hfst, Option.some.injEq] at Hlast0
          subst Hlast0
          exact gmoLtTrans _ _ _ _ Hmo0 (w0GmoLtW1 GD Lpa xpa i t old v Hrow Hcons)

/-- 7. W1 assembled: recover the acquire's deposit at `(i,0)`, deposit `R1 Hl` at `(i,1)`. -/
theorem wpdW1 (hxy : x ≠ L) (HLram : devAddr Lpa = false) (Hxram : devAddr xpa = false)
    (HLeq : L = l3pLbase Lpa) (Hxeq : x = l3pXbase xpa)
    (Hrow : AxOpsem.grow GD i = l3pWRow Lpa xpa t old v) (Hcons : rvwmoCatConsistent GD)
    (Hl : List Hent) :
    AxAnnot.annotOwn (i, 0) (AxLock3Writer.R0 (GF := GF) x GD nm i Hl) ⊢
      ∀ rs : RegFile,
        AxLock3Writer.twpd GF hlc L x GD nm i
          ⟨.PHart cpu (wM2 Lpa xpa v) rs none ibNone, 1⟩ := by
  apply wpdPosShell L x GD nm cpu i _ 1 (wM2 Lpa xpa v)
  · intro lb Hlk
    rw [Hrow] at Hlk
    simp only [l3pWRow, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq]
      at Hlk
    subst Hlk
    rfl
  · intro rs l s' Hstep
    obtain ⟨rfl, rfl⟩ := astepProgPlainWriteInv GD cpu i xpa Hxram v (fun _ => wM3 Lpa) rs 1
      ⟨.PHart cpu (wM2 Lpa xpa v) rs none ibNone, 1⟩ rfl rfl l s' Hstep
    simp only [wlWdata, l3pWbytes1]
    unfold wpEvStep naAtProgress
    iintro HP %na ⟨%Hprog, Hannot⟩
    have Hin0 : (i, 0) ∈ (FiniteMap.dom_set na : GSet Geid) := by
      have h : (i, 0) ∈ eidsBefore GD i 1 :=
        (elemOfEidsBefore GD i 1 _).2 ⟨rfl, by simp, w0Mem GD Lpa xpa i t old v Hrow⟩
      rw [← Hprog] at h
      exact (elemOfFilter.1 h).2
    obtain ⟨P0', HP0'⟩ := Option.isSome_iff_exists.1 (elemOfDom.1 Hin0)
    have Hdet : ⊢ AxAnnot.annotInterp na -∗
        AxAnnot.annotOwn (i, 0) (AxLock3Writer.R0 (GF := GF) x GD nm i Hl) ==∗
        ∃ R, AxAnnot.annotInterp (insert na (i, 0) R) ∗
          iprop(▷ □ (P0' -∗ AxLock3Writer.R0 (GF := GF) x GD nm i Hl ∗ R)) := by
      have h := annotDetach na (i, 0) (AxLock3Writer.R0 (GF := GF) x GD nm i Hl)
      rw [HP0'] at h
      exact h
    imod Hdet $$ Hannot HP with ⟨%R, Hannot', Hwand⟩
    ihave Hfeq := w1FlowEq (hlc := hlc) L x GD nm Lpa xpa i t old v hxy Hxeq Hrow Hcons Hl
    have Hnin : (i, 1) ∉ (FiniteMap.dom_set (insert na (i, 0) R) : GSet Geid) := by
      rw [domInsert, elemOfUnion, elemOfSingleton]
      rintro (Heq | Hik)
      · simp at Heq
      · have Hf : (i, 1) ∈ FiniteSet.filter (fun e : Geid => decide (e.1 = i))
            (FiniteMap.dom_set na : GSet Geid) := elemOfFilter.2 ⟨by simp, Hik⟩
        rw [Hprog, elemOfEidsBefore] at Hf
        exact Nat.lt_irrefl _ Hf.2.1
    imod (annotAlloc (insert na (i, 0) R) (i, 1) (AxLock3Writer.R1 (GF := GF) x GD nm i v Hl)
      Hnin) $$ Hannot' with ⟨Hannot'', Hpt1⟩
    imodintro
    inext
    imodintro
    iexists (), AxLock3Writer.R1 (GF := GF) x GD nm i v Hl,
      {[(i, 0) := AxLock3Writer.R0 (GF := GF) x GD nm i Hl]}, {[(i, 0) := R]}, ()
    isplitr
    · ipureintro
      trivial
    isplitl [Hwand]
    · unfold naSplittingWf
      isplitr
      · ipureintro
        rw [domSingleton]
        exact singletonSubseteqL.2 (l3pWAcqInLobpXwrite Lpa xpa GD i t old v Hrow Hcons.1)
      · iapply (BigSepM2.bigSepM2_singleton _ (i, 0)
          (AxLock3Writer.R0 (GF := GF) x GD nm i Hl) R).2
        simp only [HP0', AxWp.fromOption]
        inext
        iexact Hwand
    isplitl [Hfeq]
    · iexact Hfeq
    isplitl [Hannot'']
    · rw [← AxLock3Writer.annotEq]
      iexact Hannot''
    isplitr
    · iapply AxLock3Writer.localTriv
    · ihave H := (wpdW2 (hlc := hlc) L x GD nm Lpa xpa cpu i t old v hxy HLram HLeq Hxeq Hrow
        Hcons Hl) $$ Hpt1
      iapply H

/-! ## 8. W0 — the acquire (position 0): graph facts -/

theorem gwritesByteOfRmw (e : Geid) (base : Int) (ts : List Nat) (rvs : List (BitVec 8))
    (b : BitVec 8) (aq rl : Bool) :
    gxLbl GD.gdG e = some (.LRmw aq rl base ts rvs [b] .WCplain) →
    gwritesByte GD.gdG e base b ∧ (∀ a' v', gwritesByte GD.gdG e a' v' → a' = base) := by
  intro Hlbl
  refine ⟨⟨_, base, [b], 0, Hlbl, rfl, rfl, by simp [accAddr]⟩, ?_⟩
  rintro a' v' ⟨l, base', vs', j, Hl, Hwr, Hvs, Hacc⟩
  rw [Hlbl, Option.some.injEq] at Hl
  subst Hl
  simp only [lbWr, Option.some.injEq, Prod.mk.injEq] at Hwr
  obtain ⟨rfl, rfl⟩ := Hwr
  cases j with
  | zero => simp only [accAddr] at Hacc; omega
  | succ j => simp at Hvs

theorem w0Lbl0 (HLeq : L = l3pLbase Lpa) (Hrow : AxOpsem.grow GD i = l3pWRow Lpa xpa t old v) :
    gxLbl GD.gdG (i, 0) = some (.LRmw true false L [t] [old] [b1] .WCplain) := by
  rw [HLeq]
  exact l3pWLbl0 Lpa xpa GD i t old v Hrow

theorem w0Wb (HLeq : L = l3pLbase Lpa) (Hrow : AxOpsem.grow GD i = l3pWRow Lpa xpa t old v) :
    gwritesByte GD.gdG (i, 0) L b1 :=
  (gwritesByteOfRmw GD (i, 0) L [t] [old] b1 true false
    (w0Lbl0 L GD Lpa xpa i t old v HLeq Hrow)).1

theorem w0Single (HLeq : L = l3pLbase Lpa)
    (Hrow : AxOpsem.grow GD i = l3pWRow Lpa xpa t old v) :
    ∀ a' v', gwritesByte GD.gdG (i, 0) a' v' → a' = L :=
  (gwritesByteOfRmw GD (i, 0) L [t] [old] b1 true false
    (w0Lbl0 L GD Lpa xpa i t old v HLeq Hrow)).2

theorem w0Gd (HLeq : L = l3pLbase Lpa) (Hrow : AxOpsem.grow GD i = l3pWRow Lpa xpa t old v) :
    graphData GD (i, 0) = some [b1] := by
  simp only [graphData, w0Lbl0 L GD Lpa xpa i t old v HLeq Hrow, Option.bind_some, lblData]

/-! ## 10. The release-sourced acquire: the deposits threaded existentially -/

/-- 10.1 The existential closures of `R1`/`R0`. -/
def AxLock3Writer.R1e : IProp GF := iprop(∃ Hl, AxLock3Writer.R1 (GF := GF) x GD nm i v Hl)

def R0e : IProp GF := iprop(∃ Hl, AxLock3Writer.R0 (GF := GF) x GD nm i Hl)

/-- 10.2 W3's flow equation, `flowIn`-existential. -/
theorem w3FlowEqE (hxy : x ≠ L) (HLeq : L = l3pLbase Lpa) (Hxeq : x = l3pXbase xpa)
    (Hrow : AxOpsem.grow GD i = l3pWRow Lpa xpa t old v) (Hcons : rvwmoCatConsistent GD) :
    ⊢ @flowEqDyn hlc GF _ (axGA2Lock3 L x GD nm) GD (i, 3) (lockPolS GD (i, 3))
        {[(i, 1) := AxLock3Writer.R1e (GF := GF) x GD nm i v]}
        iprop(True ∗ ⌜graphData GD (i, 3) = some [b0]⌝) := by
  iapply (@flowEqDynMono hlc GF _ (axGA2Lock3 L x GD nm) lockAxpol GD (i, 3) (lockPolS GD (i, 3))
    _ iprop(∃ _Hl : List Hent, True ∗ ⌜graphData GD (i, 3) = some [b0]⌝)
    iprop(True ∗ ⌜graphData GD (i, 3) = some [b0]⌝))
  · inext
    iintro ⟨%_, H⟩
    iexact H
  · unfold AxLock3Writer.R1e
    iapply (flowEqDynExistsSingleton (hlc := hlc) L x GD nm (i, 1)
      (fun Hl => AxLock3Writer.R1 (GF := GF) x GD nm i v Hl)
      (fun _ => iprop(True ∗ ⌜graphData GD (i, 3) = some [b0]⌝)) (i, 3) (lockPolS GD (i, 3))
      (fun Hl => w3FlowEq L x GD nm Lpa xpa i t old v hxy HLeq Hxeq Hrow Hcons Hl))

/-- 10.3 W3 assembled at `R1e`. -/
theorem wpdW3E (hxy : x ≠ L) (HLram : devAddr Lpa = false) (HLeq : L = l3pLbase Lpa)
    (Hxeq : x = l3pXbase xpa) (Hrow : AxOpsem.grow GD i = l3pWRow Lpa xpa t old v)
    (Hcons : rvwmoCatConsistent GD) :
    AxAnnot.annotOwn (i, 1) (AxLock3Writer.R1e (GF := GF) x GD nm i v) ⊢
      ∀ rs : RegFile,
        AxLock3Writer.twpd GF hlc L x GD nm i ⟨.PHart cpu (wM4 Lpa) rs none ibNone, 3⟩ := by
  apply wpdPosShell L x GD nm cpu i _ 3 (wM4 Lpa)
  · intro lb Hlk
    rw [Hrow] at Hlk
    simp only [l3pWRow, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq]
      at Hlk
    subst Hlk
    rfl
  · intro rs l s' Hstep
    obtain ⟨rfl, rfl⟩ := astepProgPlainWriteInv GD cpu i Lpa HLram b0 (fun _ => .pure ()) rs 3
      ⟨.PHart cpu (wM4 Lpa) rs none ibNone, 3⟩ rfl rfl l s' Hstep
    simp only [wlWdata, l3pWbytes1]
    unfold wpEvStep naAtProgress
    iintro HP %na ⟨%Hprog, Hannot⟩
    have Hin1 : (i, 1) ∈ (FiniteMap.dom_set na : GSet Geid) := by
      have h : (i, 1) ∈ eidsBefore GD i 3 :=
        (elemOfEidsBefore GD i 3 _).2 ⟨rfl, by simp, w3XMem GD Lpa xpa i t old v Hrow⟩
      rw [← Hprog] at h
      exact (elemOfFilter.1 h).2
    obtain ⟨P', HP'⟩ := Option.isSome_iff_exists.1 (elemOfDom.1 Hin1)
    have Hdet : ⊢ AxAnnot.annotInterp na -∗
        AxAnnot.annotOwn (i, 1) (AxLock3Writer.R1e (GF := GF) x GD nm i v) ==∗
        ∃ R, AxAnnot.annotInterp (insert na (i, 1) R) ∗
          iprop(▷ □ (P' -∗ AxLock3Writer.R1e (GF := GF) x GD nm i v ∗ R)) := by
      have h := annotDetach na (i, 1) (AxLock3Writer.R1e (GF := GF) x GD nm i v)
      rw [HP'] at h
      exact h
    imod Hdet $$ Hannot HP with ⟨%R, Hannot', Hwand⟩
    ihave Hfeq := w3FlowEqE (hlc := hlc) L x GD nm Lpa xpa i t old v hxy HLeq Hxeq Hrow Hcons
    have Hnin : (i, 3) ∉ (FiniteMap.dom_set (insert na (i, 1) R) : GSet Geid) := by
      rw [domInsert, elemOfUnion, elemOfSingleton]
      rintro (Heq | Hik)
      · simp at Heq
      · have Hf : (i, 3) ∈ FiniteSet.filter (fun e : Geid => decide (e.1 = i))
            (FiniteMap.dom_set na : GSet Geid) := elemOfFilter.2 ⟨by simp, Hik⟩
        rw [Hprog, elemOfEidsBefore] at Hf
        exact Nat.lt_irrefl _ Hf.2.1
    imod (annotAlloc (insert na (i, 1) R) (i, 3) iprop(True) Hnin) $$ Hannot' with ⟨Hannot'', -⟩
    imodintro
    inext
    imodintro
    iexists (), iprop(True), {[(i, 1) := AxLock3Writer.R1e (GF := GF) x GD nm i v]},
      {[(i, 1) := R]}, ()
    isplitr
    · ipureintro
      trivial
    isplitl [Hwand]
    · unfold naSplittingWf
      isplitr
      · ipureintro
        rw [domSingleton]
        exact singletonSubseteqL.2 (l3pWXwriteInLobpRel Lpa xpa GD i t old v Hrow Hcons.1)
      · iapply (BigSepM2.bigSepM2_singleton _ (i, 1)
          (AxLock3Writer.R1e (GF := GF) x GD nm i v) R).2
        simp only [HP', AxWp.fromOption]
        inext
        iexact Hwand
    isplitl [Hfeq]
    · iexact Hfeq
    isplitl [Hannot'']
    · rw [← AxLock3Writer.annotEq]
      iexact Hannot''
    isplitr
    · iapply AxLock3Writer.localTriv
    · iapply wpdRowEndTriv L x GD nm i (3 + 1) (by rw [Hrow]; simp [l3pWRow])

theorem wpdW2E (hxy : x ≠ L) (HLram : devAddr Lpa = false) (HLeq : L = l3pLbase Lpa)
    (Hxeq : x = l3pXbase xpa) (Hrow : AxOpsem.grow GD i = l3pWRow Lpa xpa t old v)
    (Hcons : rvwmoCatConsistent GD) :
    AxAnnot.annotOwn (i, 1) (AxLock3Writer.R1e (GF := GF) x GD nm i v) ⊢
      ∀ rs : RegFile,
        AxLock3Writer.twpd GF hlc L x GD nm i ⟨.PHart cpu (wM3 Lpa) rs none ibNone, 2⟩ := by
  apply wpdPosShell L x GD nm cpu i _ 2 (wM3 Lpa)
  · intro lb Hlk
    rw [Hrow] at Hlk
    simp only [l3pWRow, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq]
      at Hlk
    subst Hlk
    rfl
  · intro rs l s' Hstep
    obtain ⟨rfl, rfl⟩ := astepProgFenceInv GD cpu i (fun _ => wM4 Lpa) rs 2
      ⟨.PHart cpu (wM3 Lpa) rs none ibNone, 2⟩ rfl rfl l s' Hstep
    simp only [wlWdata]
    iintro HP
    iapply wpdSkipStepOfLater (GF := GF) L x GD nm i
    inext
    ihave H := (wpdW3E (hlc := hlc) L x GD nm Lpa xpa cpu i t old v hxy HLram HLeq Hxeq Hrow
      Hcons) $$ HP
    iapply H


/-- 10.4 W1's flow equation, `flowIn`-existential (the witness carried to `R1e`). -/
theorem w1FlowEqE (hxy : x ≠ L) (Hxeq : x = l3pXbase xpa)
    (Hrow : AxOpsem.grow GD i = l3pWRow Lpa xpa t old v) (Hcons : rvwmoCatConsistent GD) :
    ⊢ @flowEqDyn hlc GF _ (axGA2Lock3 L x GD nm) GD (i, 1) (lockPolS GD (i, 1))
        {[(i, 0) := R0e (GF := GF) x GD nm i]}
        iprop(AxLock3Writer.R1e (GF := GF) x GD nm i v ∗
          ⌜graphData GD (i, 1) = some [v]⌝) := by
  iapply (@flowEqDynMono hlc GF _ (axGA2Lock3 L x GD nm) lockAxpol GD (i, 1) (lockPolS GD (i, 1))
    _ iprop(∃ Hl : List Hent,
      AxLock3Writer.R1 (GF := GF) x GD nm i v Hl ∗ ⌜graphData GD (i, 1) = some [v]⌝)
    iprop(AxLock3Writer.R1e (GF := GF) x GD nm i v ∗ ⌜graphData GD (i, 1) = some [v]⌝))
  · inext
    iintro ⟨%Hl, HR1, Hp⟩
    isplitl [HR1]
    · unfold AxLock3Writer.R1e
      iexists Hl
      iexact HR1
    · iexact Hp
  · unfold R0e
    iapply (flowEqDynExistsSingleton (hlc := hlc) L x GD nm (i, 0)
      (fun Hl => AxLock3Writer.R0 (GF := GF) x GD nm i Hl)
      (fun Hl => iprop(AxLock3Writer.R1 (GF := GF) x GD nm i v Hl ∗
        ⌜graphData GD (i, 1) = some [v]⌝)) (i, 1) (lockPolS GD (i, 1))
      (fun Hl => w1FlowEq L x GD nm Lpa xpa i t old v hxy Hxeq Hrow Hcons Hl))

/-- 10.5 W1 assembled at `R0e`/`R1e`. -/
theorem wpdW1E (hxy : x ≠ L) (HLram : devAddr Lpa = false) (Hxram : devAddr xpa = false)
    (HLeq : L = l3pLbase Lpa) (Hxeq : x = l3pXbase xpa)
    (Hrow : AxOpsem.grow GD i = l3pWRow Lpa xpa t old v) (Hcons : rvwmoCatConsistent GD)
    :
    AxAnnot.annotOwn (i, 0) (R0e (GF := GF) x GD nm i) ⊢
      ∀ rs : RegFile,
        AxLock3Writer.twpd GF hlc L x GD nm i
          ⟨.PHart cpu (wM2 Lpa xpa v) rs none ibNone, 1⟩ := by
  apply wpdPosShell L x GD nm cpu i _ 1 (wM2 Lpa xpa v)
  · intro lb Hlk
    rw [Hrow] at Hlk
    simp only [l3pWRow, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq]
      at Hlk
    subst Hlk
    rfl
  · intro rs l s' Hstep
    obtain ⟨rfl, rfl⟩ := astepProgPlainWriteInv GD cpu i xpa Hxram v (fun _ => wM3 Lpa) rs 1
      ⟨.PHart cpu (wM2 Lpa xpa v) rs none ibNone, 1⟩ rfl rfl l s' Hstep
    simp only [wlWdata, l3pWbytes1]
    unfold wpEvStep naAtProgress
    iintro HP %na ⟨%Hprog, Hannot⟩
    have Hin0 : (i, 0) ∈ (FiniteMap.dom_set na : GSet Geid) := by
      have h : (i, 0) ∈ eidsBefore GD i 1 :=
        (elemOfEidsBefore GD i 1 _).2 ⟨rfl, by simp, w0Mem GD Lpa xpa i t old v Hrow⟩
      rw [← Hprog] at h
      exact (elemOfFilter.1 h).2
    obtain ⟨P0', HP0'⟩ := Option.isSome_iff_exists.1 (elemOfDom.1 Hin0)
    have Hdet : ⊢ AxAnnot.annotInterp na -∗
        AxAnnot.annotOwn (i, 0) (R0e (GF := GF) x GD nm i) ==∗
        ∃ R, AxAnnot.annotInterp (insert na (i, 0) R) ∗
          iprop(▷ □ (P0' -∗ R0e (GF := GF) x GD nm i ∗ R)) := by
      have h := annotDetach na (i, 0) (R0e (GF := GF) x GD nm i)
      rw [HP0'] at h
      exact h
    imod Hdet $$ Hannot HP with ⟨%R, Hannot', Hwand⟩
    ihave Hfeq := w1FlowEqE (hlc := hlc) L x GD nm Lpa xpa i t old v hxy Hxeq Hrow Hcons
    have Hnin : (i, 1) ∉ (FiniteMap.dom_set (insert na (i, 0) R) : GSet Geid) := by
      rw [domInsert, elemOfUnion, elemOfSingleton]
      rintro (Heq | Hik)
      · simp at Heq
      · have Hf : (i, 1) ∈ FiniteSet.filter (fun e : Geid => decide (e.1 = i))
            (FiniteMap.dom_set na : GSet Geid) := elemOfFilter.2 ⟨by simp, Hik⟩
        rw [Hprog, elemOfEidsBefore] at Hf
        exact Nat.lt_irrefl _ Hf.2.1
    imod (annotAlloc (insert na (i, 0) R) (i, 1) (AxLock3Writer.R1e (GF := GF) x GD nm i v)
      Hnin) $$ Hannot' with ⟨Hannot'', Hpt1⟩
    imodintro
    inext
    imodintro
    iexists (), AxLock3Writer.R1e (GF := GF) x GD nm i v,
      {[(i, 0) := R0e (GF := GF) x GD nm i]}, {[(i, 0) := R]}, ()
    isplitr
    · ipureintro
      trivial
    isplitl [Hwand]
    · unfold naSplittingWf
      isplitr
      · ipureintro
        rw [domSingleton]
        exact singletonSubseteqL.2 (l3pWAcqInLobpXwrite Lpa xpa GD i t old v Hrow Hcons.1)
      · iapply (BigSepM2.bigSepM2_singleton _ (i, 0)
          (R0e (GF := GF) x GD nm i) R).2
        simp only [HP0', AxWp.fromOption]
        inext
        iexact Hwand
    isplitl [Hfeq]
    · iexact Hfeq
    isplitl [Hannot'']
    · rw [← AxLock3Writer.annotEq]
      iexact Hannot''
    isplitr
    · iapply AxLock3Writer.localTriv
    · ihave H := (wpdW2E (hlc := hlc) L x GD nm Lpa xpa cpu i t old v hxy HLram HLeq Hxeq Hrow
        Hcons) $$ Hpt1
      iapply H

/-! ## 8.3 Step inversions at position 0 (the fused RMW node) -/

theorem w0ReadDet (HLram : devAddr Lpa = false) (rs : RegFile) (d : Efab) (l : Wlabel)
    (p' : Pexv6) (d' : Efab) :
    pstepProg (.PHart cpu (wM0 Lpa xpa v) rs none ibNone) d l p' d' →
    p' = .PHart cpu (wM1 Lpa xpa v) rs none ibNone ∧ d' = d := by
  intro h
  cases p' with
  | PDisk _ => exact False.elim h
  | PHart cpu' m' rs' fn' ib' =>
    obtain ⟨rfl, ors, oib, obar, rfl, rfl, hn, hd⟩ := h
    have hpa : devAddr (l3pRreq l3pAkXaq Lpa).pa = false := HLram
    have hfe : (classify (l3pRreq l3pAkXaq Lpa).access_kind).akIfetch = false := rfl
    simp only [wM0, pstepNode, pnodeStep, hpa, Bool.false_eq_true, ↓reduceIte] at hn
    rcases hn with ⟨hif, _⟩ | ⟨_, ⟨_, w, tvs, _, _, _, hm, hors, hfn, hdd, hoib, _⟩ |
      ⟨_, w, tvs, _, _, _, hm, hors, hfn, hdd, hoib, _⟩⟩
    · rw [hfe] at hif
      cases hif
    all_goals
      subst hm hors hfn hoib
      exact ⟨rfl, by rw [hd, hdd]⟩

theorem astepProgWrite0Inv (HLram : devAddr Lpa = false) (rs : RegFile) (s : Athread)
    (Heqp : s.atP = .PHart cpu (wM1 Lpa xpa v) rs none ibNone) (Heqk : s.atK = 0)
    (l : Wlabel) (s' : Athread) :
    AxOpsem.astepProg (AxOpsem.grow GD i) s l s' →
    (wlWdata l = some (WeakInterpProj.wbytes 1 b1) ∧
      s' = ⟨.PHart cpu (wM2 Lpa xpa v) rs none ibNone, 1⟩) ∨
    (l = LSilent ∧ s' = ⟨.PHart cpu (wM1 Lpa xpa v) rs none ibNone, 0⟩) := by
  intro h
  cases h with
  | AStepAdmin p k0 d l p' d' hadm hst =>
    simp only at Heqp Heqk
    subst Heqp Heqk
    rcases l3pWriteExclDet cpu Lpa HLram b1 (fun _ => wM2 Lpa xpa v) rs ibNone d l p' d' hst with
      ⟨rfl, -, -⟩ | ⟨rfl, rfl, -⟩
    · simp [AxOpsem.lbAdminAx] at hadm
    · exact .inr ⟨rfl, rfl⟩
  | AStepWrite p k0 d l lb p' d' _ hwr _ _ hst =>
    simp only at Heqp Heqk
    subst Heqp Heqk
    rcases l3pWriteExclDet cpu Lpa HLram b1 (fun _ => wM2 Lpa xpa v) rs ibNone d l p' d' hst with
      ⟨rfl, rfl, -⟩ | ⟨rfl, -, -⟩
    · exact .inl ⟨rfl, rfl⟩
    · simp [wlWr] at hwr
  | AStepFence p k0 d l lb p' d' _ hfe _ hst =>
    simp only at Heqp Heqk
    subst Heqp Heqk
    rcases l3pWriteExclDet cpu Lpa HLram b1 (fun _ => wM2 Lpa xpa v) rs ibNone d l p' d' hst with
      ⟨rfl, -, -⟩ | ⟨rfl, -, -⟩ <;> simp [wlFence] at hfe

theorem astepProgRead0Vacuous (HLram : devAddr Lpa = false) (rs : RegFile) (s : Athread)
    (Heqp : s.atP = .PHart cpu (wM0 Lpa xpa v) rs none ibNone) (_Heqk : s.atK = 0)
    (l : Wlabel) (s' : Athread) :
    AxOpsem.astepProg (AxOpsem.grow GD i) s l s' → False := by
  intro h
  obtain ⟨d, d', hst⟩ := astepProgPstep _ _ _ _ h
  rw [Heqp] at hst
  obtain ⟨hrd, -⟩ := pstepProgMemreadLbl cpu 1 64 (l3pRreq l3pAkXaq Lpa)
    (fun _ => wM1 Lpa xpa v) rs ibNone d l s'.atP d' HLram rfl hst
  rcases l3pAstepProgShape _ s l s' h with hadm | hwr | hfn
  · exact l3pRdExclAdmin l hrd hadm
  · exact l3pRdExclWr l hrd hwr
  · exact l3pRdExclFence l hrd hfn

/-! ## 8.2/8.4/8.5/9. The genesis-sourced acquire and its capstone -/

section WGen

/-- 8.2 The genesis flow equation: `lockAcq0FlowEq3A` widened to `R0 [] ∗ ⌜graphData …⌝`. -/
theorem w0FlowEqGen (HLeq : L = l3pLbase Lpa) (Hrow : AxOpsem.grow GD i = l3pWRow Lpa xpa t old v)
    (Hcons : rvwmoCatConsistent GD) (Himg : GD.gdG.gxImg L = some b0)
    (Hrd0 : greadsByte GD.gdG (i, 0) L 0 b0) :
    ⊢ @flowEqDyn hlc GF _ (axGA2Lock3 L x GD nm) GD (i, 0) (lockPolS GD (i, 0)) (∅ : Mea GF)
        iprop(AxLock3Writer.R0 (GF := GF) x GD nm i [] ∗
          ⌜graphData GD (i, 0) = some [b1]⌝) := by
  iapply (@flowEqDynMono hlc GF _ (axGA2Lock3 L x GD nm) lockAxpol GD (i, 0) (lockPolS GD (i, 0))
    _ iprop(histAuth nm.1 x 1 [])
    iprop(AxLock3Writer.R0 (GF := GF) x GD nm i [] ∗ ⌜graphData GD (i, 0) = some [b1]⌝))
  · inext
    iintro H
    isplitl [H]
    · unfold AxLock3Writer.R0
      isplitl [H]
      · ileft
        isplitr
        · ipureintro
          rfl
        · iexact H
      · ipureintro
        exact histXWfNil x GD
    · ipureintro
      exact w0Gd L GD Lpa xpa i t old v HLeq Hrow
  · iapply (lockAcq0FlowEq3A (hlc := hlc) L x GD nm GD (i, 0) ∅ Hcons Himg Hrd0
      (w0Wb L GD Lpa xpa i t old v HLeq Hrow) (w0Single L GD Lpa xpa i t old v HLeq Hrow))

/-- 8.4 W0's write half: Löb over the register file (the SC retry self-loop and the wire). -/
theorem wpdW0Write (hxy : x ≠ L) (HLram : devAddr Lpa = false) (Hxram : devAddr xpa = false)
    (HLeq : L = l3pLbase Lpa) (Hxeq : x = l3pXbase xpa)
    (Hrow : AxOpsem.grow GD i = l3pWRow Lpa xpa t old v) (Hcons : rvwmoCatConsistent GD)
    (Himg : GD.gdG.gxImg L = some b0) (Hrd0 : greadsByte GD.gdG (i, 0) L 0 b0)
    (s : Athread) (rs : RegFile) (Heqp : s.atP = .PHart cpu (wM1 Lpa xpa v) rs none ibNone)
    (Heqk : s.atK = 0) :
    ⊢ AxLock3Writer.twpd GF hlc L x GD nm i s := by
  obtain ⟨p, k⟩ := s
  simp only at Heqp Heqk
  subst Heqp Heqk
  have H : ⊢ ∀ rs : RegFile,
      AxLock3Writer.twpd GF hlc L x GD nm i ⟨.PHart cpu (wM1 Lpa xpa v) rs none ibNone, 0⟩ := by
    iloeb as IH
    iintro %rs
    unfold AxLock3Writer.twpd tierAWpd
    iapply (@AxWpD.wpdMUnfoldStep hlc GF _ (axGA2Lock3 L x GD nm) lockAxpol rvwmoCatConsistent
      .MaybeStuck i _ _).2
    isplit
    · iapply (@progressOblMaybestuck GF (axGA2Lock3 L x GD nm) lockAxpol i _).2
      itrivial
    unfold wpdMPreStepDef
    iintro %GD' %ls ⟨%Hc, #Hg, -⟩
    ihave %Hg := AxLock3Writer.gconstPure L x GD nm GD' $$ Hg
    subst GD'
    isplit
    · iintro %id %K %Hst
      have hfalse : False := by
        obtain ⟨lb, Hlb, Hid, Hsome, HK⟩ := Hst
        simp only at Hlb
        rw [Hrow] at Hlb
        simp only [l3pWRow, List.getElem?_cons_zero, Option.some.injEq] at Hlb
        subst Hlb Hid
        obtain ⟨l0, d0, d0', Hwlrd, -, Hpst, -⟩ := HK [old] rfl
        rcases l3pWriteExclDet cpu Lpa HLram b1 (fun _ => wM2 Lpa xpa v) rs ibNone d0 l0 _ d0'
          Hpst with ⟨rfl, -, -⟩ | ⟨rfl, -, -⟩ <;> simp [wlRd, aident, aidentRd] at Hwlrd
      exact hfalse.elim
    isplit
    · iintro %l %s' %Hst %-
      rcases astepProgWrite0Inv GD Lpa xpa cpu i v HLram rs _ rfl rfl l s' Hst with
        ⟨Hwd, rfl⟩ | ⟨rfl, rfl⟩
      · rw [Hwd, l3pWbytes1]
        dsimp only
        unfold wpEvStep naAtProgress
        iintro %na ⟨%Hprog, Hannot⟩
        have Hnin0 : (i, 0) ∉ (FiniteMap.dom_set na : GSet Geid) := by
          intro Hin
          have Hf : (i, 0) ∈ FiniteSet.filter (fun e : Geid => decide (e.1 = i))
              (FiniteMap.dom_set na : GSet Geid) := elemOfFilter.2 ⟨by simp, Hin⟩
          rw [Hprog, elemOfEidsBefore] at Hf
          exact Nat.not_lt_zero _ Hf.2.1
        imod (annotAlloc na (i, 0) (AxLock3Writer.R0 (GF := GF) x GD nm i []) Hnin0) $$ Hannot
          with ⟨Hannot', Hpt0⟩
        ihave Hfeq0 := w0FlowEqGen (hlc := hlc) L x GD nm Lpa xpa i t old v HLeq Hrow Hcons Himg
          Hrd0
        imodintro
        inext
        imodintro
        iexists (), AxLock3Writer.R0 (GF := GF) x GD nm i [], (∅ : Mea GF), (∅ : Mea GF), ()
        isplitr
        · ipureintro
          trivial
        isplitr
        · unfold naSplittingWf
          isplitr
          · ipureintro
            rw [domEmpty]
            exact LawfulSet.empty_subset
          · iapply (BigSepM2.bigSepM2_empty _).2
            itrivial
        isplitl [Hfeq0]
        · iexact Hfeq0
        isplitl [Hannot']
        · rw [AxLockWp.annotInsertEq]
          iexact Hannot'
        isplitr
        · iapply AxLock3Writer.localTriv
        · have Hw1 := wpdW1 (GF := GF) (hlc := hlc) L x GD nm Lpa xpa cpu i t old v hxy HLram Hxram
            HLeq Hxeq Hrow Hcons []
          unfold AxLock3Writer.twpd tierAWpd at Hw1
          ihave H := Hw1 $$ Hpt0
          dsimp only
          iapply H
      · simp only [wlWdata]
        iapply wpdSkipStepOfLater (GF := GF) L x GD nm i
        inext
        iapply IH $$ %rs
    isplit
    · iintro %s' %Hw
      obtain ⟨rs', rfl⟩ := l3pAwireRsOnly cpu (wM1 Lpa xpa v) rs none ibNone 0 s' Hw
      iapply wpdSkipStepOfLater (GF := GF) L x GD nm i
      inext
      iapply IH $$ %rs'
    · iintro %-
      iapply (@postLiftingTrue GF (axGA2Lock3 L x GD nm) lockAxpol _ i _ true_intro)
  iapply H $$ %rs

/-- 8.5 W0's read half: the real (demonic) read, pinned to the successor `wM1` by
`w0ReadDet`; no program step. -/
theorem wpdW0Read (hxy : x ≠ L) (HLram : devAddr Lpa = false) (Hxram : devAddr xpa = false)
    (HLeq : L = l3pLbase Lpa) (Hxeq : x = l3pXbase xpa)
    (Hrow : AxOpsem.grow GD i = l3pWRow Lpa xpa t old v) (Hcons : rvwmoCatConsistent GD)
    (Himg : GD.gdG.gxImg L = some b0) (Hrd0 : greadsByte GD.gdG (i, 0) L 0 b0) :
    ⊢ ∀ rs : RegFile,
      AxLock3Writer.twpd GF hlc L x GD nm i ⟨.PHart cpu (wM0 Lpa xpa v) rs none ibNone, 0⟩ := by
  iloeb as IH
  iintro %rs
  unfold AxLock3Writer.twpd tierAWpd
  iapply (@AxWpD.wpdMUnfoldStep hlc GF _ (axGA2Lock3 L x GD nm) lockAxpol rvwmoCatConsistent
    .MaybeStuck i _ _).2
  isplit
  · iapply (@progressOblMaybestuck GF (axGA2Lock3 L x GD nm) lockAxpol i _).2
    itrivial
  unfold wpdMPreStepDef
  iintro %GD' %ls ⟨%Hc, #Hg, -⟩
  ihave %Hg := AxLock3Writer.gconstPure L x GD nm GD' $$ Hg
  subst GD'
  isplit
  · iintro %id %K %Hst
    obtain ⟨lb, Hlb, Hid, -, HK⟩ := Hst
    simp only at Hlb
    rw [Hrow] at Hlb
    simp only [l3pWRow, List.getElem?_cons_zero, Option.some.injEq] at Hlb
    subst Hlb Hid
    simp only [aident, aidentAdvRd, Nat.zero_ne_one, ↓reduceIte]
    iintro %gv %Hgv %Hlen
    obtain ⟨l0, d0, d0', -, -, Hpst, Hatk⟩ := HK gv Hlen
    have Hp := (w0ReadDet Lpa xpa cpu v HLram rs d0 l0 _ d0' Hpst).1
    have Hk0 : (K gv).atK = 0 := by rw [Hatk]; rfl
    iapply wpdSkipStepOfLater (GF := GF) L x GD nm i
    inext
    have Hw0 := wpdW0Write (GF := GF) (hlc := hlc) L x GD nm Lpa xpa cpu i t old v hxy HLram Hxram
      HLeq Hxeq Hrow Hcons Himg Hrd0 (K gv) rs Hp Hk0
    unfold AxLock3Writer.twpd tierAWpd at Hw0
    iapply Hw0
  isplit
  · iintro %l %s' %Hst %-
    exact (astepProgRead0Vacuous GD Lpa xpa cpu i v HLram rs _ rfl rfl l s' Hst).elim
  isplit
  · iintro %s' %Hw
    obtain ⟨rs', rfl⟩ := l3pAwireRsOnly cpu (wM0 Lpa xpa v) rs none ibNone 0 s' Hw
    iapply wpdSkipStepOfLater (GF := GF) L x GD nm i
    inext
    iapply IH $$ %rs'
  · iintro %-
    iapply (@postLiftingTrue GF (axGA2Lock3 L x GD nm) lockAxpol _ i _ true_intro)

/-- 9. THE CAPSTONE (genesis-sourced acquire): from `lock3Init nm i` (`emp`). -/
theorem wpdWriterHart (hxy : x ≠ L) (HLram : devAddr Lpa = false) (Hxram : devAddr xpa = false)
    (HLeq : L = l3pLbase Lpa) (Hxeq : x = l3pXbase xpa)
    (Hrow : AxOpsem.grow GD i = l3pWRow Lpa xpa t old v) (Hcons : rvwmoCatConsistent GD)
    (Himg : GD.gdG.gxImg L = some b0) (Hrd0 : greadsByte GD.gdG (i, 0) L 0 b0) (rs : RegFile) :
    ⊢ lock3Init (GF := GF) nm i -∗
      AxLock3Writer.twpd GF hlc L x GD nm i ⟨l3pWP0 Lpa xpa cpu rs v, 0⟩ := by
  have heq : l3pWP0 Lpa xpa cpu rs v = .PHart cpu (wM0 Lpa xpa v) rs none ibNone := rfl
  rw [heq]
  iintro -
  ihave H := wpdW0Read (hlc := hlc) L x GD nm Lpa xpa cpu i t old v hxy HLram Hxram HLeq Hxeq
    Hrow Hcons Himg Hrd0
  iapply H $$ %rs

end WGen

/-! ## 10.6/10.7/11. The release-sourced acquire and its capstone -/

section WRel

/-- 10.6 The release-sourced acquire's flow equation: `lockAcqFlowEq3A` widened to
`R0e ∗ ⌜graphData …⌝`. -/
theorem w0FlowEqRel (HLeq : L = l3pLbase Lpa) (Hrow : AxOpsem.grow GD i = l3pWRow Lpa xpa t old v)
    (Hcons : rvwmoCatConsistent GD) (w_rel : Geid) (Hwrel_wb0 : gwritesByte GD.gdG w_rel L b0)
    (Hgob_rel : gobCat GD w_rel (i, 0)) (Hrfe_rel : lockExtRmwReader L GD w_rel (i, 0)) :
    ⊢ @flowEqDyn hlc GF _ (axGA2Lock3 L x GD nm) GD (i, 0) (lockPolS GD (i, 0)) (∅ : Mea GF)
        iprop(R0e (GF := GF) x GD nm i ∗ ⌜graphData GD (i, 0) = some [b1]⌝) := by
  iapply (@flowEqDynMono hlc GF _ (axGA2Lock3 L x GD nm) lockAxpol GD (i, 0) (lockPolS GD (i, 0))
    _ iprop(∃ Hh, xTok GD nm.1 x Hh (i, 0) ∗
      ⌜histXWf x GD Hh ∧ lockHhPoLatest x GD Hh w_rel⌝)
    iprop(R0e (GF := GF) x GD nm i ∗ ⌜graphData GD (i, 0) = some [b1]⌝))
  · inext
    iintro ⟨%Hh, Htie, %Hp⟩
    isplitl [Htie]
    · unfold R0e AxLock3Writer.R0
      iexists Hh
      isplitl [Htie]
      · iunfold xTok at Htie
        icases Htie with (Htie | Hraw)
        · iright
          iexact Htie
        · ileft
          iexact Hraw
      · ipureintro
        exact Hp.1
    · ipureintro
      exact w0Gd L GD Lpa xpa i t old v HLeq Hrow
  · iapply (lockAcqFlowEq3A (hlc := hlc) L x GD nm GD w_rel (i, 0) ∅ Hcons Hwrel_wb0
      (w0Wb L GD Lpa xpa i t old v HLeq Hrow) (w0Single L GD Lpa xpa i t old v HLeq Hrow)
      Hgob_rel Hrfe_rel)

/-- 10.7 W0's write half (release-sourced): Löb over the register file (the SC retry self-loop and
the wire). -/
theorem wpdW0WriteRel (hxy : x ≠ L) (HLram : devAddr Lpa = false) (Hxram : devAddr xpa = false)
    (HLeq : L = l3pLbase Lpa) (Hxeq : x = l3pXbase xpa)
    (Hrow : AxOpsem.grow GD i = l3pWRow Lpa xpa t old v) (Hcons : rvwmoCatConsistent GD)
    (w_rel : Geid) (Hwrel_wb0 : gwritesByte GD.gdG w_rel L b0)
    (Hgob_rel : gobCat GD w_rel (i, 0)) (Hrfe_rel : lockExtRmwReader L GD w_rel (i, 0))
    (s : Athread) (rs : RegFile) (Heqp : s.atP = .PHart cpu (wM1 Lpa xpa v) rs none ibNone)
    (Heqk : s.atK = 0) :
    ⊢ AxLock3Writer.twpd GF hlc L x GD nm i s := by
  obtain ⟨p, k⟩ := s
  simp only at Heqp Heqk
  subst Heqp Heqk
  have H : ⊢ ∀ rs : RegFile,
      AxLock3Writer.twpd GF hlc L x GD nm i ⟨.PHart cpu (wM1 Lpa xpa v) rs none ibNone, 0⟩ := by
    iloeb as IH
    iintro %rs
    unfold AxLock3Writer.twpd tierAWpd
    iapply (@AxWpD.wpdMUnfoldStep hlc GF _ (axGA2Lock3 L x GD nm) lockAxpol rvwmoCatConsistent
      .MaybeStuck i _ _).2
    isplit
    · iapply (@progressOblMaybestuck GF (axGA2Lock3 L x GD nm) lockAxpol i _).2
      itrivial
    unfold wpdMPreStepDef
    iintro %GD' %ls ⟨%Hc, #Hg, -⟩
    ihave %Hg := AxLock3Writer.gconstPure L x GD nm GD' $$ Hg
    subst GD'
    isplit
    · iintro %id %K %Hst
      have hfalse : False := by
        obtain ⟨lb, Hlb, Hid, Hsome, HK⟩ := Hst
        simp only at Hlb
        rw [Hrow] at Hlb
        simp only [l3pWRow, List.getElem?_cons_zero, Option.some.injEq] at Hlb
        subst Hlb Hid
        obtain ⟨l0, d0, d0', Hwlrd, -, Hpst, -⟩ := HK [old] rfl
        rcases l3pWriteExclDet cpu Lpa HLram b1 (fun _ => wM2 Lpa xpa v) rs ibNone d0 l0 _ d0'
          Hpst with ⟨rfl, -, -⟩ | ⟨rfl, -, -⟩ <;> simp [wlRd, aident, aidentRd] at Hwlrd
      exact hfalse.elim
    isplit
    · iintro %l %s' %Hst %-
      rcases astepProgWrite0Inv GD Lpa xpa cpu i v HLram rs _ rfl rfl l s' Hst with
        ⟨Hwd, rfl⟩ | ⟨rfl, rfl⟩
      · rw [Hwd, l3pWbytes1]
        dsimp only
        unfold wpEvStep naAtProgress
        iintro %na ⟨%Hprog, Hannot⟩
        have Hnin0 : (i, 0) ∉ (FiniteMap.dom_set na : GSet Geid) := by
          intro Hin
          have Hf : (i, 0) ∈ FiniteSet.filter (fun e : Geid => decide (e.1 = i))
              (FiniteMap.dom_set na : GSet Geid) := elemOfFilter.2 ⟨by simp, Hin⟩
          rw [Hprog, elemOfEidsBefore] at Hf
          exact Nat.not_lt_zero _ Hf.2.1
        imod (annotAlloc na (i, 0) (R0e (GF := GF) x GD nm i) Hnin0) $$ Hannot
          with ⟨Hannot', Hpt0⟩
        ihave Hfeq0 := w0FlowEqRel (hlc := hlc) L x GD nm Lpa xpa i t old v HLeq Hrow Hcons w_rel
          Hwrel_wb0 Hgob_rel Hrfe_rel
        imodintro
        inext
        imodintro
        iexists (), R0e (GF := GF) x GD nm i, (∅ : Mea GF), (∅ : Mea GF), ()
        isplitr
        · ipureintro
          trivial
        isplitr
        · unfold naSplittingWf
          isplitr
          · ipureintro
            rw [domEmpty]
            exact LawfulSet.empty_subset
          · iapply (BigSepM2.bigSepM2_empty _).2
            itrivial
        isplitl [Hfeq0]
        · iexact Hfeq0
        isplitl [Hannot']
        · rw [AxLockWp.annotInsertEq]
          iexact Hannot'
        isplitr
        · iapply AxLock3Writer.localTriv
        · have Hw1 := wpdW1E (GF := GF) (hlc := hlc) L x GD nm Lpa xpa cpu i t old v hxy HLram
            Hxram HLeq Hxeq Hrow Hcons
          unfold AxLock3Writer.twpd tierAWpd at Hw1
          ihave H := Hw1 $$ Hpt0
          dsimp only
          iapply H
      · simp only [wlWdata]
        iapply wpdSkipStepOfLater (GF := GF) L x GD nm i
        inext
        iapply IH $$ %rs
    isplit
    · iintro %s' %Hw
      obtain ⟨rs', rfl⟩ := l3pAwireRsOnly cpu (wM1 Lpa xpa v) rs none ibNone 0 s' Hw
      iapply wpdSkipStepOfLater (GF := GF) L x GD nm i
      inext
      iapply IH $$ %rs'
    · iintro %-
      iapply (@postLiftingTrue GF (axGA2Lock3 L x GD nm) lockAxpol _ i _ true_intro)
  iapply H $$ %rs

/-- 10.7 W0's read half (release-sourced): the real (demonic) read, pinned to the successor `wM1` by
`w0ReadDet`; no program step. -/
theorem wpdW0ReadRel (hxy : x ≠ L) (HLram : devAddr Lpa = false) (Hxram : devAddr xpa = false)
    (HLeq : L = l3pLbase Lpa) (Hxeq : x = l3pXbase xpa)
    (Hrow : AxOpsem.grow GD i = l3pWRow Lpa xpa t old v) (Hcons : rvwmoCatConsistent GD)
    (w_rel : Geid) (Hwrel_wb0 : gwritesByte GD.gdG w_rel L b0)
    (Hgob_rel : gobCat GD w_rel (i, 0)) (Hrfe_rel : lockExtRmwReader L GD w_rel (i, 0)) :
    ⊢ ∀ rs : RegFile,
      AxLock3Writer.twpd GF hlc L x GD nm i ⟨.PHart cpu (wM0 Lpa xpa v) rs none ibNone, 0⟩ := by
  iloeb as IH
  iintro %rs
  unfold AxLock3Writer.twpd tierAWpd
  iapply (@AxWpD.wpdMUnfoldStep hlc GF _ (axGA2Lock3 L x GD nm) lockAxpol rvwmoCatConsistent
    .MaybeStuck i _ _).2
  isplit
  · iapply (@progressOblMaybestuck GF (axGA2Lock3 L x GD nm) lockAxpol i _).2
    itrivial
  unfold wpdMPreStepDef
  iintro %GD' %ls ⟨%Hc, #Hg, -⟩
  ihave %Hg := AxLock3Writer.gconstPure L x GD nm GD' $$ Hg
  subst GD'
  isplit
  · iintro %id %K %Hst
    obtain ⟨lb, Hlb, Hid, -, HK⟩ := Hst
    simp only at Hlb
    rw [Hrow] at Hlb
    simp only [l3pWRow, List.getElem?_cons_zero, Option.some.injEq] at Hlb
    subst Hlb Hid
    simp only [aident, aidentAdvRd, Nat.zero_ne_one, ↓reduceIte]
    iintro %gv %Hgv %Hlen
    obtain ⟨l0, d0, d0', -, -, Hpst, Hatk⟩ := HK gv Hlen
    have Hp := (w0ReadDet Lpa xpa cpu v HLram rs d0 l0 _ d0' Hpst).1
    have Hk0 : (K gv).atK = 0 := by rw [Hatk]; rfl
    iapply wpdSkipStepOfLater (GF := GF) L x GD nm i
    inext
    have Hw0 := wpdW0WriteRel (GF := GF) (hlc := hlc) L x GD nm Lpa xpa cpu i t old v hxy HLram
      Hxram HLeq Hxeq Hrow Hcons w_rel Hwrel_wb0 Hgob_rel Hrfe_rel (K gv) rs Hp Hk0
    unfold AxLock3Writer.twpd tierAWpd at Hw0
    iapply Hw0
  isplit
  · iintro %l %s' %Hst %-
    exact (astepProgRead0Vacuous GD Lpa xpa cpu i v HLram rs _ rfl rfl l s' Hst).elim
  isplit
  · iintro %s' %Hw
    obtain ⟨rs', rfl⟩ := l3pAwireRsOnly cpu (wM0 Lpa xpa v) rs none ibNone 0 s' Hw
    iapply wpdSkipStepOfLater (GF := GF) L x GD nm i
    inext
    iapply IH $$ %rs'
  · iintro %-
    iapply (@postLiftingTrue GF (axGA2Lock3 L x GD nm) lockAxpol _ i _ true_intro)

/-- 11. THE SECOND CAPSTONE (release-sourced acquire). -/
theorem wpdWriterHartRel (hxy : x ≠ L) (HLram : devAddr Lpa = false)
    (Hxram : devAddr xpa = false) (HLeq : L = l3pLbase Lpa) (Hxeq : x = l3pXbase xpa)
    (Hrow : AxOpsem.grow GD i = l3pWRow Lpa xpa t old v) (Hcons : rvwmoCatConsistent GD)
    (w_rel : Geid) (Hwrel_wb0 : gwritesByte GD.gdG w_rel L b0)
    (Hgob_rel : gobCat GD w_rel (i, 0)) (Hrfe_rel : lockExtRmwReader L GD w_rel (i, 0))
    (rs : RegFile) :
    ⊢ lock3Init (GF := GF) nm i -∗
      AxLock3Writer.twpd GF hlc L x GD nm i ⟨l3pWP0 Lpa xpa cpu rs v, 0⟩ := by
  have heq : l3pWP0 Lpa xpa cpu rs v = .PHart cpu (wM0 Lpa xpa v) rs none ibNone := rfl
  rw [heq]
  iintro -
  ihave H := wpdW0ReadRel (hlc := hlc) L x GD nm Lpa xpa cpu i t old v hxy HLram Hxram HLeq Hxeq
    Hrow Hcons w_rel Hwrel_wb0 Hgob_rel Hrfe_rel
  iapply H $$ %rs

end WRel

end writer

end Weak
