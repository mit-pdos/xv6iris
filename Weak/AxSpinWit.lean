/-
Weak: **Phase 3b of the spinlock plan -- a WPd-LEVEL witness of the GATED tier-A route at the
TAGGED port** (`AxSpinGate.tierAAdequacyAnnGateT`): a ctrl-gated owned spill FORWARDED to a later
same-hart reload that `Lcanon` defers past its gate source but keeps BEFORE the spill.

Rocq: `iris/AxSpinWit.v` @ xxvzwolszwmp.

## The Rocq header, in substance

PROGRAMS (hand `Pexv6` nodes, `AxClsStep2` style, HALT = `hlt`; f at `ya`, x at `xa`, RAM):
  hart B (1): `ld f; if f = 1 then (sd x 1; ld x; HALT) else HALT` (`sbM0`; row
              `sbRow tf tx vx` = the branch-taken row).
  hart A (0): ABSTRACT in the capstone (any start state, run and WPd premised); `sd f 1; HALT`
              (`saM0`) in certificate (a); `sd f 1; sd x 2; HALT` (`raM0`) in the race (b)/(c).
PROTOCOL: `AxProt.protInv` (`spOb`); `spInit`: A holds the full history auth of f, B that of x
(x OWNED by B; f RACY for B).  POLICY `spPol GT`: `sPol e` = every WRITE gmo-before `e` ∪
`gsrcT GT e` (gate sources, possibly gmo-LATER); `lobp = ∅`.

WHAT IS PROVED
  §2 `sbRun`/`saRun`/`raRun`: the runs over an ABSTRACT graph with the row pinned.
  §3 concrete tagged graphs `spw` (reload gmo-FIRST, forwarded), `spl` (spill gmo-before
     reload), `AxSpinWit.spr` (race): all `rvwmoCatConsistentT` and `ctrlClosed` by kernel
     computation; `spwLcanon`: `Lcanon = [(A,0), (B,0), (B,2), (B,1)]` -- the reload IS deferred
     past its gate source and processed BEFORE the spill; `spwNotGmo`.
  §4 `spHok`: the policy is admissible for `tierAAdequacyAnnGateT` (writes: `polDS` via
     `gsrcTReal'`, needs `ctrlClosed`; gate sources: the gate arm).  `spwBackwardHandout`.
  §6 WPd shells at `axGA2` (`shPos`, `shRead`, `shHltTrue`, `shHltReadback` -- the row-end post
     read back from an annotation) and `shOwnedStore` (the owned store, history appended in
     PHASE 1, FINDING 1).
  §7 `AxSpinWit.wpdA` (A's positive program) and `AxSpinWit.wpdB` (B's WPd, post `vx = 1`): the
     reload deposits `RB = ⌜∀ t v, greadsByte (B,2) x t v → v = 1⌝` whose flow equation is
     `AxProt.flowEqOwnedReadByte` fed B's OWN token; the case split (ghost case (i) / forwarding
     case (ii)) is INSIDE the flow equation.
  §8 THE CAPSTONE `spinReloadOwned`: from `rvwmoCatConsistentT GT`, `ctrlClosed GT`, harts =
     {A, B}, B's row, A's run and A's WPd at the real protocol, `vx = 1`.
  §9 (a) SATISFIABILITY `spwPremises`, `spwSound`, `spwGateWitness`; the non-deferred twin
     `splSound`, `splSpillGmoBefore`.
  §10 (b) RACE `AxSpinWit.sprWpdUnprovable` (reductio through the capstone).
  §11 (c) SANITY TWIN `AxSpinWit.sprWpdTrivial` at the trivial protocol.

FINDINGS (Rocq, unchanged).  1. The spill must append the history in PHASE 1 (the AxEpiOwned
route is not admissible under `Lcanon` on a deferred graph).  2. On the deferred graph the owned
reload's value is the PURE forwarding case (ii); the ghost case (i) only on `spl`.  3. The gate
handout is taken but IDLE (`protInv` records nothing for reads).  4. `Hok` for this policy uses
`gsrcTReal'`, i.e. `ctrlClosed` enters through the POLICY.

## Deviations from Rocq

1. O2 STAGE C (as `AxSpinGate` deviation 2 / `AxClsStep2` deviation 2): no text oracle -- Rocq's
   `Tf`/`T`/`img` arguments are gone: `spAstepWrite` takes no `T`/`img`, `tierAWpd GD N …` and
   `tierAAstep GD nm i` have no `Tf`; `shReadAstepVacuous` (Rocq: under the empty text `Tf`)
   takes `(classify ak).akIfetch = false` (a fetch is an admin step in Lean) and no `GD`.
2. CONTEXTS: the `shells`/`wpd_real`/`twin` sections' `Context`s are explicit arguments;
   `invGS_gen HasNoLc Σ` ↦ `[InvGS_gen hlc GF]` for any `hlc` (the capstone instantiates
   `.hasNoLC`); `GF : BundledGFunctors.{0,0,0}`.  The policy instance is the NAMED binder
   `[pol : Axpol]` (callers pass `(pol := spPol GT)`); `spPol` is a reducible def, not an
   instance.  Rocq's `Local Instance shG` is the reducible def `shG`; the local instances
   `spR_pol`/`spR_G`/`spT_pol`/`spT_G` are inlined (`spPol GT`, `shG (gtAdGd GT) GName Unit spOb
   γ`, `spPol AxSpinWit.spr`, `shG (gtAdGd AxSpinWit.spr) Unit Unit trivOb nm`).  `Hob` of
   `shOwnedStore` is an explicit argument.  `spΣ` ↦ `spGF`, an explicit slot table (inv/credits
   0–3, the history log `AxlogRF Hent` at 4, annotation cameras 5–7) with Lean-only instances
   `AxSpinWit.spGF*`.
3. lean-sail shapes (as `AxClsStep2` deviation 3): read answers `.Ok (w, none)`; `sbK` uses a
   decidable `if w = b1`; `init_regstate` ↦ `zeroRegs`; `S k` ↦ `k + 1`; `l !! k` ↦ `l[k]?`;
   `vm_compute` ↦ `decide +kernel` (`Lcanon` facts by the `AxSpinGate.twLcanon` recipe, Lean-only
   `AxSpinWit.spwListPerm`/`splListPerm`).  Wand chains `A -∗ B` ↦ `⊢ A -∗ B`.  The Rocq
   notations `hA`/`hB` are `abbrev`s, `B1`/`B2` are `b1`/`b2`.
4. The capstone's `set` locals are the Lean-only defs `AxSpinWit.cS0`/`cSN`/`cN`/`cPost`; the
   capstone's `HwpA` and the certificate statements take `[InvGS_gen .hasNoLC spGF]
   [AxannotGS spGF]` instance binders (as `tierAAdequacyAnnGateT`).
5. PROOF ROUTE (not statements): the shells unfold `AxWpD.wpdMUnfoldStep` (as `AxClsStep2b`);
   `shSkip` is proved from `wpSkipStep`'s definition (Rocq: via `wp_skip_step_mono`).

**Rocq → Lean name map.**  `sb_m2/m1/m0` `sbM2/M1/M0`, `sb_k` `sbK`, `sa_m0` `saM0`,
`ra_m1/m0` `raM1/M0`, `sb_k_B1` `sbKB1`, `sb_row` `sbRow`, `sa_row` `saRow`, `ra_row` `raRow`,
`sp_astep_write` `spAstepWrite`, `sp_run_write` `spRunWrite`, `sp_run_read` `spRunRead`,
`sb_run` `sbRun`, `sa_run` `saRun`, `ra_run` `raRun`, `sp_deps` `spDeps`, `spw` `spw`, `spl`
`spl`, `spr` `AxSpinWit.spr`, `spw/spl_cat_t` `spwCatT`/`splCatT`, `spr_cat_t`
`AxSpinWit.sprCatT`, `spw/spl_ctrl_closed` `spwCtrlClosed`/`splCtrlClosed`, `spr_ctrl_closed`
`AxSpinWit.sprCtrlClosed`, `spw_gsrc_reload` `spwGsrcReload`, `spw_Lcanon` `spwLcanon`,
`spw_not_gmo` `spwNotGmo`, `spl_Lcanon` `splLcanon`, `sp_ob` `spOb`, `sp_init` `spInit`,
`sp_Hob_alloc` `spHobAlloc`, `sp_spol` `spSpol`, `sp_pol` `spPol`, `sp_axpol_wf` `spAxpolWf`,
`sp_spol_cov` `spSpolCov`, `sp_Hok` `spHok`, `spw_backward_handout` `spwBackwardHandout`,
`gwb_store` `gwbStore`, `grb_load` `grbLoad`, `prot_inv_write_snap` `protInvWriteSnap`,
`shG` `shG`, `sh_skip` `shSkip`, `sh_pos` `shPos`, `sh_read_astep_vacuous`
`shReadAstepVacuous`, `sh_read` `shRead`, `sh_hlt_true` `shHltTrue`, `sh_hlt_readback`
`shHltReadback`, `sh_owned_store` `shOwnedStore`, `spR_ob` `spROb`, `wpdA` `AxSpinWit.wpdA`,
`sbB_lbl` `sbBLbl`, `RB` `RB`, `wpdB_2/1/0` `wpdB2/1/0`, `wpdB` `AxSpinWit.wpdB`, `spΣ` `spGF`,
`spin_reload_owned` `spinReloadOwned`, `spw/spl_harts` `spwHarts`/`splHarts`, `spr_harts`
`AxSpinWit.sprHarts`, `sa_wpd` `saWpd`, `sa_run_t` `saRunT`, `spw_premises` `spwPremises`,
`spw_sound` `spwSound`, `spw_gate_witness` `spwGateWitness`, `spl_sound` `splSound`,
`spl_spill_gmo_before` `splSpillGmoBefore`, `ra_run_t` `raRunT`, `spr_reload_reads_race`
`sprReloadReadsRace`, `spr_wpd_unprovable` `AxSpinWit.sprWpdUnprovable`, `triv_ob` `trivOb`,
`triv_store` `trivStore`, `spr_wpd_triv_gen` `sprWpdTrivGen`, `spr_wpd_trivial`
`AxSpinWit.sprWpdTrivial`.  Duplicated Rocq names (file-qualified): `AxSpinWit.spr`,
`AxSpinWit.sprCatT`, `AxSpinWit.sprCtrlClosed`, `AxSpinWit.wpdA`, `AxSpinWit.wpdB`,
`AxSpinWit.sprHarts`, `AxSpinWit.sprWpdUnprovable`, `AxSpinWit.sprWpdTrivial`.  Lean-only
(file-qualified): `AxSpinWit.sbKOk`, `AxSpinWit.spwListPerm`, `AxSpinWit.splListPerm`,
`AxSpinWit.gconstEq`, `AxSpinWit.localTrue`, `AxSpinWit.twUnfold`, `AxSpinWit.naSplittingWfEmpty`,
`AxSpinWit.tierAWpdMono`, `AxSpinWit.spInitA`, `AxSpinWit.spInitB`, `AxSpinWit.spGF*`
instances, `AxSpinWit.cS0`/`cSN`/`cN`/`cPost`, `AxSpinWit.trivObTrue`.

**Dropped:** only the §12 `Check`/`Print Assumptions` lines (the lint's axiom check covers them).
-/
import Weak.AxSpinGate
import Weak.AxClsStep2b
import Weak.AxProt
import Weak.AxLockWp

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std Iris.Std.PartialMap MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D
open Dtag

/-! # 1. THE PROGRAMS (hand `Pexv6` nodes; HALT = `hlt`).  f at `ya`, x at `xa`. -/

abbrev hA : Nat := 0
abbrev hB : Nat := 1

/-- Hart B: `ld f; if f = 1 then (sd x 1; ld x; HALT) else HALT`. -/
abbrev sbM2 : SailM Unit :=
  .impure (.ok (.memRead 1 64 (l3pRreq l3pAkP xpaM))) (fun _ => hlt)
abbrev sbM1 : SailM Unit :=
  .impure (.ok (.memWrite 1 64 (l3pWreq l3pAkP xpaM b1))) (fun _ => sbM2)
def sbK (res : Result (BitVec (8 * 1) × Option Bool) Arch.abort) : SailM Unit :=
  match res with
  | .Ok (w, _) => if w = b1 then sbM1 else hlt
  | .Err _ => hlt
abbrev sbM0 : SailM Unit :=
  .impure (.ok (.memRead 1 64 (l3pRreq l3pAkP ypaM))) sbK

/-- Hart A (the positive program): `sd f 1; HALT`. -/
abbrev saM0 : SailM Unit :=
  .impure (.ok (.memWrite 1 64 (l3pWreq l3pAkP ypaM b1))) (fun _ => hlt)

/-- Hart A (the RACE program): `sd f 1; sd x 2; HALT`. -/
abbrev raM1 : SailM Unit :=
  .impure (.ok (.memWrite 1 64 (l3pWreq l3pAkP xpaM b2))) (fun _ => hlt)
abbrev raM0 : SailM Unit :=
  .impure (.ok (.memWrite 1 64 (l3pWreq l3pAkP ypaM b1))) (fun _ => raM1)

/-- Lean-only: `sbK` at an `Ok` answer. -/
theorem AxSpinWit.sbKOk (b : BitVec (8 * 1)) (o : Option Bool) :
    sbK (.Ok (b, o)) = if b = b1 then sbM1 else hlt := rfl

theorem sbKB1 : sbK (.Ok (wordOfBytes 1 [b1], none)) = sbM1 := by
  rw [AxSpinWit.sbKOk, if_pos wordOfBytesB1]

/-- The rows (the branch-taken row of hart B: f read = 1). -/
def sbRow (tf tx : Nat) (vx : BitVec 8) : List Lbl :=
  [.LLoad false ya [tf] [b1], .LStore false xa [b1] .WCplain, .LLoad false xa [tx] [vx]]
def saRow : List Lbl := [.LStore false ya [b1] .WCplain]
def raRow : List Lbl := [.LStore false ya [b1] .WCplain, .LStore false xa [b2] .WCplain]

/-! # 2. THE RUNS (over an ABSTRACT graph, row pinned) -/

section runs
variable (cpu : CPU)

theorem spAstepWrite (row : List Lbl) (pa : PAddr) (Hdev : devAddr pa = false) (val : BitVec 8)
    (m' : SailM Unit) (rs : RegFile) (k : Nat) (cls : WmClass) :
    row[k]? = some (.LStore false (paZ pa) [val] cls) →
    AxOpsem.astepProg row
      ⟨hp cpu (.impure (.ok (.memWrite 1 64 (l3pWreq l3pAkP pa val))) (fun _ => m')) rs, k⟩
      (.LStore false (paZ pa) (WeakInterpProj.wbytes 1 val) [] [])
      ⟨hp cpu m' rs, k + 1⟩ :=
  hAstepWrite cpu row k pa Hdev val cls m' rs

theorem spRunWrite (GD : Gdexec) (i : Agent) (pa : PAddr) (Hdev : devAddr pa = false)
    (val : BitVec 8) (m' : SailM Unit) (rs : RegFile) (k : Nat) (cls : WmClass) :
    (AxOpsem.grow GD i)[k]? = some (.LStore false (paZ pa) [val] cls) →
    astepAnyNfGv GD i
      ⟨hp cpu (.impure (.ok (.memWrite 1 64 (l3pWreq l3pAkP pa val))) (fun _ => m')) rs, k⟩
      ⟨hp cpu m' rs, k + 1⟩ := by
  intro Hl
  exact .ANFGVProg _ _ ⟨_, spAstepWrite cpu _ pa Hdev val m' rs k cls Hl, trivial⟩

theorem spRunRead (GD : Gdexec) (i : Agent) (pa : PAddr) (Hdev : devAddr pa = false)
    (ts : List Nat) (b : BitVec 8)
    (KK : Result (BitVec (8 * 1) × Option Bool) Arch.abort → SailM Unit) (rs : RegFile) (k : Nat) :
    (AxOpsem.grow GD i)[k]? = some (.LLoad false (paZ pa) ts [b]) →
    astepAnyNfGv GD i
      ⟨hp cpu (.impure (.ok (.memRead 1 64 (l3pRreq l3pAkP pa))) KK) rs, k⟩
      ⟨hp cpu (KK (.Ok (wordOfBytes 1 [b], none))) rs, k + 1⟩ := by
  intro Hl
  have Hrd := hAreadGen cpu (AxOpsem.grow GD i) k false l3pAkP pa Hdev rfl rfl rfl ts b KK rs Hl
  have Hgv : graphValue GD (i, k) = some [b] := by
    unfold graphValue
    rw [gxLblGrow, Hl]
    rfl
  exact .ANFGVRead _ _ _ [b] Hrd Hgv rfl

theorem sbRun (GD : Gdexec) (tf tx : Nat) (vx : BitVec 8)
    (Hrow : AxOpsem.grow GD hB = sbRow tf tx vx) :
    nsteps (astepAnyNfGv GD hB) 3 ⟨hp cpu sbM0 zeroRegs, 0⟩ ⟨hp cpu hlt zeroRegs, 3⟩ := by
  have H0 := spRunRead cpu GD hB ypaM ypaMRam [tf] b1 sbK zeroRegs 0 (by rw [Hrow]; rfl)
  rw [sbKB1] at H0
  refine nsteps_l H0 ?_
  refine nsteps_l (spRunWrite cpu GD hB xpaM xpaMRam b1 sbM2 zeroRegs 1 .WCplain
    (by rw [Hrow]; rfl)) ?_
  refine nsteps_l (spRunRead cpu GD hB xpaM xpaMRam [tx] vx (fun _ => hlt) zeroRegs 2
    (by rw [Hrow]; rfl)) ?_
  exact nsteps_O _

theorem saRun (GD : Gdexec) (Hrow : AxOpsem.grow GD hA = saRow) :
    nsteps (astepAnyNfGv GD hA) 1 ⟨hp cpu saM0 zeroRegs, 0⟩ ⟨hp cpu hlt zeroRegs, 1⟩ := by
  refine nsteps_l (spRunWrite cpu GD hA ypaM ypaMRam b1 hlt zeroRegs 0 .WCplain
    (by rw [Hrow]; rfl)) ?_
  exact nsteps_O _

theorem raRun (GD : Gdexec) (Hrow : AxOpsem.grow GD hA = raRow) :
    nsteps (astepAnyNfGv GD hA) 2 ⟨hp cpu raM0 zeroRegs, 0⟩ ⟨hp cpu hlt zeroRegs, 2⟩ := by
  refine nsteps_l (spRunWrite cpu GD hA ypaM ypaMRam b1 raM1 zeroRegs 0 .WCplain
    (by rw [Hrow]; rfl)) ?_
  refine nsteps_l (spRunWrite cpu GD hA xpaM xpaMRam b2 hlt zeroRegs 1 .WCplain
    (by rw [Hrow]; rfl)) ?_
  exact nsteps_O _

end runs

/-! # 3. THE CONCRETE TAGGED GRAPHS -/

/-- The spill `(B,1)` is ctrl-dependent on the f read `(B,0)`. -/
def spDeps : List Tdep := [(((hB, 0), (hB, 1)), DTctrl)]

/-- `spw`: the DEFERRED witness -- the reload `(B,2)` is gmo-FIRST (forwarded from the spill). -/
def spw : GdexecT :=
  mkgt [saRow, sbRow 1 2 b1] [(hB, 2), (hA, 0), (hB, 0), (hB, 1)] spDeps

/-- `spl`: the NON-deferred twin -- the spill is gmo-before the reload. -/
def spl : GdexecT :=
  mkgt [saRow, sbRow 1 2 b1] [(hA, 0), (hB, 0), (hB, 1), (hB, 2)] spDeps

/-- `spr`: the RACE -- A also writes `x := 2`, gmo-between the spill and the reload. -/
def AxSpinWit.spr : GdexecT :=
  mkgt [raRow, sbRow 1 3 b2] [(hA, 0), (hB, 0), (hB, 1), (hA, 1), (hB, 2)] spDeps

theorem spwCatT : rvwmoCatConsistentT spw := catTConsistentBSound _ (by decide +kernel)
theorem splCatT : rvwmoCatConsistentT spl := catTConsistentBSound _ (by decide +kernel)
theorem AxSpinWit.sprCatT : rvwmoCatConsistentT AxSpinWit.spr :=
  catTConsistentBSound _ (by decide +kernel)

theorem spwCtrlClosed : ctrlClosed spw := ctrlClosedBSound _ spwCatT.1 (by decide +kernel)
theorem splCtrlClosed : ctrlClosed spl := ctrlClosedBSound _ splCatT.1 (by decide +kernel)
theorem AxSpinWit.sprCtrlClosed : ctrlClosed AxSpinWit.spr :=
  ctrlClosedBSound _ AxSpinWit.sprCatT.1 (by decide +kernel)

/-- The gate is non-trivial: the f read gates the reload. -/
theorem spwGsrcReload : ((hB, 0) : Geid) ∈ gsrcT spw (hB, 2) :=
  (gsrcTSpec _ _ _).2 ⟨(hB, 1), by decide +kernel, .inr ((gpoBSpec _ _ _).1 (by decide +kernel))⟩

/-- Lean-only: the target order is a permutation of `spw`'s gmo. -/
theorem AxSpinWit.spwListPerm :
    ([(hA, 0), (hB, 0), (hB, 2), (hB, 1)] : List Geid).Perm (gtAdGd spw).gdG.gxGmo := by
  decide +kernel

/-- `Lcanon` DEFERS the reload past its gate source, still BEFORE the spill it is forwarded
from. -/
theorem spwLcanon :
    Lcanon (gtAdGd spw) (gsrcT spw) = [(hA, 0), (hB, 0), (hB, 2), (hB, 1)] := by
  have Hinj : ∀ a, a ∈ ([(hA, 0), (hB, 0), (hB, 2), (hB, 1)] : List Geid) →
      ∀ b, b ∈ ([(hA, 0), (hB, 0), (hB, 2), (hB, 1)] : List Geid) →
      AxDefer3.grank (gtAdGd spw).gdG (gsrcT spw) a =
        AxDefer3.grank (gtAdGd spw).gdG (gsrcT spw) b → a = b := by
    decide +kernel
  have Hsorted : List.Pairwise
      (fun a b => decide (rankLe (AxDefer3.grank (gtAdGd spw).gdG (gsrcT spw)) a b) = true)
      ([(hA, 0), (hB, 0), (hB, 2), (hB, 1)] : List Geid) := by
    decide +kernel
  refine List.Perm.eq_of_pairwise (fun a b ha hb hab hba => ?_)
    (AxDefer3.rankSortSorted _ _) Hsorted
    ((rankSortPerm _ _).trans AxSpinWit.spwListPerm.symm)
  have ha' := ((rankSortPerm _ _).trans AxSpinWit.spwListPerm.symm).mem_iff.1 ha
  have h1 := of_decide_eq_true hab
  have h2 := of_decide_eq_true hba
  unfold rankLe at h1 h2
  exact Hinj a ha' b hb (by omega)

theorem spwNotGmo : spw.gtG.gxGmo ≠ Lcanon (gtAdGd spw) (gsrcT spw) := by
  rw [spwLcanon]
  decide +kernel

/-- Lean-only: the target order is a permutation of `spl`'s gmo. -/
theorem AxSpinWit.splListPerm :
    ([(hA, 0), (hB, 0), (hB, 1), (hB, 2)] : List Geid).Perm (gtAdGd spl).gdG.gxGmo := by
  decide +kernel

theorem splLcanon :
    Lcanon (gtAdGd spl) (gsrcT spl) = [(hA, 0), (hB, 0), (hB, 1), (hB, 2)] := by
  have Hinj : ∀ a, a ∈ ([(hA, 0), (hB, 0), (hB, 1), (hB, 2)] : List Geid) →
      ∀ b, b ∈ ([(hA, 0), (hB, 0), (hB, 1), (hB, 2)] : List Geid) →
      AxDefer3.grank (gtAdGd spl).gdG (gsrcT spl) a =
        AxDefer3.grank (gtAdGd spl).gdG (gsrcT spl) b → a = b := by
    decide +kernel
  have Hsorted : List.Pairwise
      (fun a b => decide (rankLe (AxDefer3.grank (gtAdGd spl).gdG (gsrcT spl)) a b) = true)
      ([(hA, 0), (hB, 0), (hB, 1), (hB, 2)] : List Geid) := by
    decide +kernel
  refine List.Perm.eq_of_pairwise (fun a b ha hb hab hba => ?_)
    (AxDefer3.rankSortSorted _ _) Hsorted
    ((rankSortPerm _ _).trans AxSpinWit.splListPerm.symm)
  have ha' := ((rankSortPerm _ _).trans AxSpinWit.splListPerm.symm).mem_iff.1 ha
  have h1 := of_decide_eq_true hab
  have h2 := of_decide_eq_true hba
  unfold rankLe at h1 h2
  exact Hinj a ha' b hb (by omega)

/-! # 4. THE PROTOCOL INSTANCE AND THE POLICY -/

/-- Real protocol: `AxProt.protInv` (Own class, per-byte histories). -/
def spOb {GF : BundledGFunctors} [AxlogG GF Hent] (γ : GName) (GD : Gdexec) (_ : Unit)
    (s : GSet Geid) : IProp GF :=
  protInv γ GD s

/-- Hart A owns f, hart B owns x. -/
def spInit {GF : BundledGFunctors} [AxlogG GF Hent] (γ : GName) (i : Agent) : IProp GF :=
  if i = hA then histAuth γ ya 1 [] else if i = hB then histAuth γ xa 1 [] else iprop(emp)

/-- Lean-only: `spInit` at hart A. -/
theorem AxSpinWit.spInitA {GF : BundledGFunctors} [AxlogG GF Hent] (γ : GName) :
    spInit (GF := GF) γ hA = histAuth γ ya 1 [] := if_pos rfl

/-- Lean-only: `spInit` at hart B. -/
theorem AxSpinWit.spInitB {GF : BundledGFunctors} [AxlogG GF Hent] (γ : GName) :
    spInit (GF := GF) γ hB = histAuth γ xa 1 [] := by
  unfold spInit
  rw [if_neg (by decide), if_pos rfl]

theorem spHobAlloc {GF : BundledGFunctors} [AxlogG GF Hent] (GD : Gdexec) :
    ⊢ iprop(|==> ∃ (nm : GName) (σ0 : Unit), spOb (GF := GF) nm GD σ0 ∅ ∗
      [∗list] i ∈ [hA, hB], spInit nm i) := by
  imod histAlloc (GF := GF) (({ya} : GSet Int) ∪ {xa}) ([] : List Hent) with ⟨%γ, Halloc⟩
  have hdisj : ({ya} : GSet Int) ## {xa} := by
    rw [elemOfDisjoint]
    intro y hy hy'
    rw [elemOfSingleton.1 hy] at hy'
    exact xaNeYa (elemOfSingleton.1 hy').symm
  icases (BigSepS.bigSepS_union (Φ := fun a => histAuth (GF := GF) γ a 1 []) hdisj).1 $$ Halloc
    with ⟨Hy, Hx⟩
  ihave Hy := BigSepS.bigSepS_singleton.1 $$ Hy
  ihave Hx := BigSepS.bigSepS_singleton.1 $$ Hx
  imodintro
  iexists γ, ()
  isplitr
  · unfold spOb protInv
    iapply BigSepS.bigSepS_empty.2
    iempintro
  · iapply (AxTokLedgerMp.bigSepLPair hA hB (fun i => spInit (GF := GF) γ i)).2
    rw [AxSpinWit.spInitA, AxSpinWit.spInitB]
    isplitl [Hy]
    · iexact Hy
    · iexact Hx

/-- The handout policy: every WRITE gmo-before `e` plus `e`'s TAGGED GATE SOURCES. -/
def spSpol (GT : GdexecT) (GD : Gdexec) (e : Geid) : GSet Geid :=
  (LawfulSet.ofList (GD.gdG.gxGmo.filter (fun w => gisW GD.gdG w && gmoLtB GD.gdG w e)) :
    GSet Geid) ∪ gsrcT GT e

/-- `lobp` is EMPTY: nothing travels through annotations (FINDING 1). -/
@[reducible] def spPol (GT : GdexecT) : Axpol where
  sPol := spSpol GT
  lobp := fun _ _ => ∅

theorem spAxpolWf (GT : GdexecT) : @axpolWf (spPol GT) := by
  intro GD i k e he
  exact absurd he notElemOfEmpty

theorem spSpolCov (GT : GdexecT) (GD : Gdexec) (e w : Geid) (a : Int) (v : BitVec 8) :
    gwritesByte GD.gdG w a v → gmoLt GD.gdG w e → w ∈ spSpol GT GD e := by
  intro Hwb Hlt
  refine elemOfUnion.2 (.inl (elemOfListToSet.2 (List.mem_filter.2 ⟨Hlt.1, ?_⟩)))
  rw [AxProt.gwritesByteGisW _ _ _ _ Hwb, (gmoLtBSpec _ _ _).2 Hlt]

/-- `Hok` of `tierAAdequacyAnnGateT`: writes are deferral-safe (`gsrcTReal'`, i.e. HconsT +
ctrlClosed); gate sources take the gate arm. -/
theorem spHok (GT : GdexecT) (HconsT : rvwmoCatConsistentT GT) (Hcl : ctrlClosed GT) :
    ∀ e e', e' ∈ @Axpol.sPol (spPol GT) (gtAdGd GT) e ∪ @Axpol.lobp (spPol GT) (gtAdGd GT) e →
      polDS GT.gtG (gsrcT GT) e' e ∨ e' ∈ gsrcT GT e := by
  intro e e' Hin
  rcases elemOfUnion.1 Hin with Hin | Hin
  · rcases elemOfUnion.1 Hin with Hin | Hin
    · left
      obtain ⟨_, Hb⟩ := List.mem_filter.1 (elemOfListToSet.1 Hin)
      simp only [Bool.and_eq_true] at Hb
      obtain ⟨Hw, Hlt⟩ := Hb
      have Hlt := (gmoLtBSpec _ _ _).1 Hlt
      refine ⟨Hlt, fun s Hs => .inl ?_⟩
      obtain ⟨_, _, H3⟩ := gsrcTReal' GT HconsT Hcl e' s Hs
      exact gmoLtTrans _ _ _ _ (H3 (AxDeps.gisWGlbl _ _ Hw)) Hlt
    · exact .inr Hin
  · exact absurd Hin notElemOfEmpty

/-- The backward handout IS taken on `spw`: the reload is handed its gate source, which is
gmo-LATER than it. -/
theorem spwBackwardHandout :
    ((hB, 0) : Geid) ∈ @Axpol.sPol (spPol spw) (gtAdGd spw) (hB, 2) ∧
    ¬ gmoLt spw.gtG (hB, 0) (hB, 2) := by
  refine ⟨elemOfUnion.2 (.inr spwGsrcReload), fun Hlt => ?_⟩
  have h := (gmoLtBSpec _ _ _).2 Hlt
  have hf : gmoLtB spw.gtG (hB, 0) (hB, 2) = false := by decide +kernel
  rw [hf] at h
  cases h

/-! # 5. GRAPH FACTS OF THE ROWS -/

theorem gwbStore (G : Gexec) (e : Geid) (base : Int) (b : BitVec 8) (cls : WmClass) :
    gxLbl G e = some (.LStore false base [b] cls) →
    gwritesByte G e base b ∧ (∀ a' v', gwritesByte G e a' v' → a' = base ∧ v' = b) := by
  intro Hlbl
  refine ⟨⟨_, base, [b], 0, Hlbl, rfl, rfl, by simp [accAddr]⟩, ?_⟩
  rintro a' v' ⟨l, base', vs', j, Hl, Hwr, Hvs, Hacc⟩
  rw [Hlbl] at Hl
  cases Hl
  simp only [lbWr, Option.some.injEq, Prod.mk.injEq] at Hwr
  obtain ⟨rfl, rfl⟩ := Hwr
  cases j with
  | zero =>
    simp only [List.getElem?_cons_zero, Option.some.injEq] at Hvs
    refine ⟨?_, Hvs.symm⟩
    rw [← Hacc]
    simp [accAddr]
  | succ j => simp at Hvs

theorem grbLoad (G : Gexec) (e : Geid) (base : Int) (t : Nat) (b : BitVec 8) :
    gxLbl G e = some (.LLoad false base [t] [b]) → greadsByte G e base t b :=
  fun Hl => ⟨_, base, [t], [b], 0, Hl, rfl, rfl, rfl, by simp [accAddr]⟩

/-- Depositing a write's `ΦOwn` from a snapshot obtained in PHASE 1. -/
theorem protInvWriteSnap {GF : BundledGFunctors} [AxlogG GF Hent] (γ : GName) (GD : Gdexec)
    (s : GSet Geid) (w : Geid) (a : Int) (v : BitVec 8) (H0 : List Hent) :
    w ∉ s → gwritesByte GD.gdG w a v →
    (∀ a' v', gwritesByte GD.gdG w a' v' → a' = a ∧ v' = v) →
    ⊢ protInv (GF := GF) γ GD s -∗ histSnap γ a (H0 ++ [(w, v)]) -∗
      protInv γ GD (({w} : GSet Geid) ∪ s) := by
  intro Hnin Hwb Hsingle
  iintro Hinv #Hsn
  have Hisw := AxProt.gwritesByteGisW _ _ _ _ Hwb
  iapply (protInvInsert γ GD w s Hnin).2
  isplitr [Hinv]
  · rw [AxProt.ΦpOwnW γ GD w Hisw]
    unfold ΦOwn
    iintro %a' %v' %Hwb'
    obtain ⟨rfl, rfl⟩ := Hsingle a' v' Hwb'
    iexists (H0 ++ [(w, v')])
    isplitl []
    · iexact Hsn
    · ipureintro
      simp
  · iexact Hinv

/-- Lean-only (a copy of `AxTokLedgerWp.naSplittingWfEmpty` without its `LedgerG`). -/
theorem AxSpinWit.naSplittingWfEmpty {GF : BundledGFunctors} (sLob : GSet Geid) (na : Mea GF) :
    ⊢ naSplittingWf sLob na (∅ : Mea GF) (∅ : Mea GF) := by
  unfold naSplittingWf
  isplitr
  · ipureintro
    rw [domEmpty]
    exact LawfulSet.empty_subset
  · iapply (BigSepM2.bigSepM2_empty _).2
    itrivial

/-! # 6. WPd SHELLS at an `axGA2` instance -/

/-- Rocq `Local Instance shG` (a named reducible def). -/
@[reducible] def shG {GF : BundledGFunctors.{0,0,0}} [AxannotGS GF] (GD : Gdexec) (N obSt0 : Type)
    (obi : N → Gdexec → obSt0 → GSet Geid → IProp GF) (nm : N) : AxirisG GF :=
  axGA2 GD N obSt0 obi nm

section shells
variable {hlc : HasLC} {GF : BundledGFunctors.{0,0,0}} [InvGS_gen hlc GF] [AxannotGS GF]
  [pol : Axpol]

/-- Lean-only: the graph pin of the instance. -/
theorem AxSpinWit.gconstEq (GD : Gdexec) (N obSt0 : Type)
    (obi : N → Gdexec → obSt0 → GSet Geid → IProp GF) (nm : N) (GD' : Gdexec) :
    @AxirisG.gconstInterp GF (shG GD N obSt0 obi nm) GD' ⊢ ⌜GD' = GD⌝ := .rfl

/-- Lean-only: the local state of the instance is trivial. -/
theorem AxSpinWit.localTrue (GD : Gdexec) (N obSt0 : Type)
    (obi : N → Gdexec → obSt0 → GSet Geid → IProp GF) (nm : N) (GD' : Gdexec) (i : Agent)
    (k : Nat) (ls : Unit) :
    ⊢ @AxirisG.localInterp GF (shG GD N obSt0 obi nm) GD' i k ls := by
  show ⊢ iprop(True)
  itrivial

/-- Lean-only: one unfolding of `tierAWpd` at a hart state. -/
theorem AxSpinWit.twUnfold (GD : Gdexec) (N obSt0 : Type)
    (obi : N → Gdexec → obSt0 → GSet Geid → IProp GF) (nm : N) (s : Athread) (i : Agent)
    (Φ : Athread → IProp GF) :
    tierAWpd (hlc := hlc) GD N obSt0 obi nm s .MaybeStuck i Φ ⊣⊢
      iprop(@progressObl GF (shG GD N obSt0 obi nm) .MaybeStuck i s ∧
        @wpdMPreStepDef hlc GF _ (shG GD N obSt0 obi nm) pol rvwmoCatConsistent i
          (fun s' Φ' => tierAWpd (hlc := hlc) GD N obSt0 obi nm s' .MaybeStuck i Φ') s Φ) :=
  @AxWpD.wpdMUnfoldStep hlc GF _ (shG GD N obSt0 obi nm) pol rvwmoCatConsistent .MaybeStuck i s Φ

/-- Lean-only: `wpdMono` at `tierAWpd`. -/
theorem AxSpinWit.tierAWpdMono (GD : Gdexec) (N obSt0 : Type)
    (obi : N → Gdexec → obSt0 → GSet Geid → IProp GF) (nm : N) (s : Athread) (st : Stuckness)
    (i : Agent) (Φ Ψ : Athread → IProp GF) (H : ∀ k, Φ k ⊢ Ψ k) :
    tierAWpd (hlc := hlc) GD N obSt0 obi nm s st i Φ ⊢ tierAWpd GD N obSt0 obi nm s st i Ψ :=
  @wpdMono hlc GF _ (shG GD N obSt0 obi nm) pol st i s Φ Ψ H

theorem shSkip (GD : Gdexec) (N obSt0 : Type) (obi : N → Gdexec → obSt0 → GSet Geid → IProp GF)
    (nm : N) (i : Agent) (k' : Nat) (Ψ : IProp GF) :
    ⊢ ▷ Ψ -∗ @wpSkipStep GF (shG GD N obSt0 obi nm) GD i k' Ψ := by
  iintro HΨ
  unfold wpSkipStep
  iintro %na Hna
  imodintro
  inext
  imodintro
  iexists ()
  isplitl [Hna]
  · iexact Hna
  isplitr
  · iapply AxSpinWit.localTrue
  · iexact HΨ

/-- A non-read node strictly inside the row. -/
theorem shPos (GD : Gdexec) (N obSt0 : Type) (obi : N → Gdexec → obSt0 → GSet Geid → IProp GF)
    (nm : N) (cpu : CPU) (i : Agent) (Φ : Athread → IProp GF) (P : IProp GF) (k : Nat)
    (m : SailM Unit)
    (Hne : k ≠ (AxOpsem.grow GD i).length)
    (Hnord : ∀ (rs : RegFile) id K, ¬ areadStep (AxOpsem.grow GD i) ⟨hp cpu m rs, k⟩ id K)
    (Hb : ∀ (rs : RegFile) (l : Wlabel) (s' : Athread),
      AxOpsem.astepProg (AxOpsem.grow GD i) ⟨hp cpu m rs, k⟩ l s' →
      ⊢ P -∗ match wlWdata l with
        | some data =>
            @wpEvStep hlc GF _ (shG GD N obSt0 obi nm) pol Unit GD i k (fun _ => True)
              (fun _ => graphData GD (i, k) = some data) (fun _ => s'.atK)
              (fun _ => tierAWpd (hlc := hlc) GD N obSt0 obi nm s' .MaybeStuck i Φ)
        | none =>
            @wpSkipStep GF (shG GD N obSt0 obi nm) GD i s'.atK
              (tierAWpd (hlc := hlc) GD N obSt0 obi nm s' .MaybeStuck i Φ)) :
    ⊢ P -∗ ∀ rs : RegFile, tierAWpd (hlc := hlc) GD N obSt0 obi nm ⟨hp cpu m rs, k⟩ .MaybeStuck i Φ := by
  have H : ⊢ ∀ rs : RegFile, P -∗
      tierAWpd (hlc := hlc) GD N obSt0 obi nm ⟨hp cpu m rs, k⟩ .MaybeStuck i Φ := by
    iloeb as IH
    iintro %rs HP
    iapply (AxSpinWit.twUnfold (hlc := hlc) GD N obSt0 obi nm _ i Φ).2
    isplit
    · simp only [progressObl]
      itrivial
    unfold wpdMPreStepDef
    iintro %GD' %ls ⟨%Hc, #Hg, Hloc⟩
    ihave Hok := AxSpinWit.gconstEq GD N obSt0 obi nm GD' $$ Hg
    icases Hok with %HGD
    subst GD'
    isplit
    · iintro %id %K %Hst
      exact (Hnord rs id K Hst).elim
    isplit
    · iintro %l %s' %Hst %_
      iapply (Hb rs l s' Hst) $$ HP
    isplit
    · iintro %s' %Hw
      obtain ⟨rs', rfl⟩ := awireRsOnly2 cpu m rs k s' Hw
      iapply shSkip
      inext
      iapply IH $$ %rs' HP
    · iintro %Heq
      exact (Hne Heq).elim
  iintro HP %rs
  iapply H $$ %rs HP

/-- No program step at a RAM read node (Stage C: an i-fetch access kind is excluded). -/
theorem shReadAstepVacuous (row : List Lbl) (cpu : CPU) (ak : AK) (pa : PAddr)
    (Hdev : devAddr pa = false) (Hfe : (classify ak).akIfetch = false)
    (KK : Result (BitVec (8 * 1) × Option Bool) Arch.abort → SailM Unit) (rs : RegFile) (k : Nat)
    (l : Wlabel) (s' : Athread) :
    AxOpsem.astepProg row ⟨hp cpu (.impure (.ok (.memRead 1 64 (l3pRreq ak pa))) KK) rs, k⟩ l s' →
    False :=
  readNodeNoAstep cpu row ak pa Hdev Hfe KK rs k l s'

/-- A 1-byte plain read node strictly inside the row, ANY continuation. -/
theorem shRead (GD : Gdexec) (N obSt0 : Type) (obi : N → Gdexec → obSt0 → GSet Geid → IProp GF)
    (nm : N) (cpu : CPU) (i : Agent) (Φ : Athread → IProp GF) (pa : PAddr)
    (Hdev : devAddr pa = false)
    (KK : Result (BitVec (8 * 1) × Option Bool) Arch.abort → SailM Unit) (k : Nat)
    (Hne : k ≠ (AxOpsem.grow GD i).length)
    (Hrow : ∀ lb, (AxOpsem.grow GD i)[k]? = some lb → aidentAdvRd (aident lb) = 1)
    (P : IProp GF)
    (Hcont : ∀ (v : List (BitVec 8)) (b : BitVec 8) (rs : RegFile),
      graphValue GD (i, k) = some v → v = [b] →
      ⊢ P -∗ @wpEvStep hlc GF _ (shG GD N obSt0 obi nm) pol Unit GD i k (fun _ => True)
        (fun _ => graphValue GD (i, k) = some v) (fun _ => k + 1)
        (fun _ => tierAWpd (hlc := hlc) GD N obSt0 obi nm
          ⟨hp cpu (KK (.Ok (b, none))) rs, k + 1⟩ .MaybeStuck i Φ)) :
    ⊢ P -∗ ∀ rs : RegFile, tierAWpd (hlc := hlc) GD N obSt0 obi nm
      ⟨hp cpu (.impure (.ok (.memRead 1 64 (l3pRreq l3pAkP pa))) KK) rs, k⟩ .MaybeStuck i Φ := by
  have H : ⊢ ∀ rs : RegFile, P -∗ tierAWpd (hlc := hlc) GD N obSt0 obi nm
      ⟨hp cpu (.impure (.ok (.memRead 1 64 (l3pRreq l3pAkP pa))) KK) rs, k⟩ .MaybeStuck i Φ := by
    iloeb as IH
    iintro %rs HP
    iapply (AxSpinWit.twUnfold (hlc := hlc) GD N obSt0 obi nm _ i Φ).2
    isplit
    · simp only [progressObl]
      itrivial
    unfold wpdMPreStepDef
    iintro %GD' %ls ⟨%Hc, #Hg, Hloc⟩
    ihave Hok := AxSpinWit.gconstEq GD N obSt0 obi nm GD' $$ Hg
    icases Hok with %HGD
    subst GD'
    isplit
    · iintro %id %K %Hst
      have Hst' := Hst
      obtain ⟨lb, Hlk, Hidlb, _, -⟩ := Hst
      have Hadv1 : aidentAdvRd id = 1 := by rw [← Hidlb]; exact Hrow lb Hlk
      rw [if_pos Hadv1]
      iintro %v %Hgv %Hlen
      obtain ⟨lb', b, -, -, -, rfl, HK⟩ :=
        readInvGen cpu _ l3pAkP pa Hdev rfl KK rs k id K v Hst' Hlen
      rw [HK, Hadv1]
      iapply (Hcont [b] b rs Hgv rfl) $$ HP
    isplit
    · iintro %l %s' %Hst %_
      exact (shReadAstepVacuous _ cpu l3pAkP pa Hdev rfl KK rs k l s' Hst).elim
    isplit
    · iintro %s' %Hw
      obtain ⟨rs', rfl⟩ := awireRsOnly2 cpu _ rs k s' Hw
      iapply shSkip
      inext
      iapply IH $$ %rs' HP
    · iintro %Heq
      exact (Hne Heq).elim
  iintro HP %rs
  iapply H $$ %rs HP

/-- HALT with the trivial post. -/
theorem shHltTrue (GD : Gdexec) (N obSt0 : Type)
    (obi : N → Gdexec → obSt0 → GSet Geid → IProp GF) (nm : N) (cpu : CPU) (i : Agent) (k : Nat) :
    ⊢ ∀ rs : RegFile, tierAWpd (hlc := hlc) GD N obSt0 obi nm ⟨hp cpu hlt rs, k⟩ .MaybeStuck i
      (fun _ => iprop(True)) := by
  iloeb as IH
  iintro %rs
  iapply (AxSpinWit.twUnfold (hlc := hlc) GD N obSt0 obi nm _ i _).2
  isplit
  · simp only [progressObl]
    itrivial
  unfold wpdMPreStepDef
  iintro %GD' %ls ⟨%Hc, #Hg, Hloc⟩
  ihave Hok := AxSpinWit.gconstEq GD N obSt0 obi nm GD' $$ Hg
  icases Hok with %HGD
  subst GD'
  isplit
  · iintro %id %K %Hst
    exact (hltNoRead cpu _ rs k id K Hst).elim
  isplit
  · iintro %l %s' %Hst %_
    exact (hltNoAstep cpu _ rs k l s' Hst).elim
  isplit
  · iintro %s' %Hw
    obtain ⟨rs', rfl⟩ := awireRsOnly2 cpu hlt rs k s' Hw
    iapply shSkip
    inext
    iapply IH $$ %rs'
  · iintro %_
    iapply (@postLiftingTrue GF (shG GD N obSt0 obi nm) pol (fun _ => iprop(True)) i _
      (by iintro _; itrivial))

/-- HALT at the row end, the post READ BACK from the annotation at `e`. -/
theorem shHltReadback (GD : Gdexec) (N obSt0 : Type)
    (obi : N → Gdexec → obSt0 → GSet Geid → IProp GF) (nm : N) (cpu : CPU) (i : Agent) (k : Nat)
    (e : Geid) (He : e.1 = i) (R : IProp GF) (Q : Prop) (HRQ : R ⊢ ⌜Q⌝) :
    ⊢ AxAnnot.annotOwn e R -∗ ∀ rs : RegFile, tierAWpd (hlc := hlc) GD N obSt0 obi nm
      ⟨hp cpu hlt rs, k⟩ .MaybeStuck i (fun _ => iprop(⌜Q⌝)) := by
  have H : ⊢ ∀ rs : RegFile, AxAnnot.annotOwn e R -∗ tierAWpd (hlc := hlc) GD N obSt0 obi nm
      ⟨hp cpu hlt rs, k⟩ .MaybeStuck i (fun _ => iprop(⌜Q⌝)) := by
    iloeb as IH
    iintro %rs Hp
    iapply (AxSpinWit.twUnfold (hlc := hlc) GD N obSt0 obi nm _ i _).2
    isplit
    · simp only [progressObl]
      itrivial
    unfold wpdMPreStepDef
    iintro %GD' %ls ⟨%Hc, #Hg, Hloc⟩
    ihave Hok := AxSpinWit.gconstEq GD N obSt0 obi nm GD' $$ Hg
    icases Hok with %HGD
    subst GD'
    isplit
    · iintro %id %K %Hst
      exact (hltNoRead cpu _ rs k id K Hst).elim
    isplit
    · iintro %l %s' %Hst %_
      exact (hltNoAstep cpu _ rs k l s' Hst).elim
    isplit
    · iintro %s' %Hw
      obtain ⟨rs', rfl⟩ := awireRsOnly2 cpu hlt rs k s' Hw
      iapply shSkip
      inext
      iapply IH $$ %rs' Hp
    · iintro %_
      unfold postLifting
      iintro %na Hna
      ihave ⟨%Hdomi, #Hwand⟩ := annotAgree na e R $$ Hna Hp
      imodintro
      isplitl [Hna]
      · iexact Hna
      iintro Hbig
      obtain ⟨P0, HP0⟩ := Option.isSome_iff_exists.1 (elemOfDom.1 Hdomi)
      have Hlk : ([∗map] e' ↦ R' ∈ na, if e'.1 = i then R' else iprop(True)) ⊢ P0 :=
        (BigSepM.bigSepM_lookup (Φ := fun e R => if e.1 = i then R else iprop(True)) HP0).trans
          (by simp only [He, ↓reduceIte]; exact .rfl)
      have Hw2 : AxWp.fromOption (fun P' => iprop(▷ □ (P' -∗ R))) iprop(emp) (get? na e) ⊢
          iprop(▷ □ (P0 -∗ R)) := by
        rw [HP0]; exact .rfl
      ihave HP := Hlk $$ Hbig
      ihave Hw' := Hw2 $$ Hwand
      inext
      ihave HR := Hw' $$ HP
      imodintro
      iapply HRQ $$ HR
  iintro Hp %rs
  iapply H $$ %rs Hp

/-- An OWNED single-byte store, the history appended in PHASE 1 (the snapshot rides into the flow
equation; the full auth stays with the hart).  `obi` must be `protInv γ` (`Hob`). -/
theorem shOwnedStore [AxlogG GF Hent] (GD : Gdexec) (N obSt0 : Type)
    (obi : N → Gdexec → obSt0 → GSet Geid → IProp GF) (nm : N) (γ : GName)
    (Hob : ∀ (GD' : Gdexec) (σ : @AxirisG.obSt GF (shG GD N obSt0 obi nm)) (s : GSet Geid),
      @AxirisG.obStInterp GF (shG GD N obSt0 obi nm) GD' σ s ⊣⊢ protInv γ GD' s)
    (i : Agent) (k : Nat) (pa : PAddr) (val : BitVec 8) (cls : WmClass) (Hh0 : List Hent)
    (Hl : (AxOpsem.grow GD i)[k]? = some (.LStore false (paZ pa) [val] cls)) (Ψ : IProp GF) :
    ⊢ histAuth γ (paZ pa) 1 Hh0 -∗ (histAuth γ (paZ pa) 1 (Hh0 ++ [((i, k), val)]) -∗ Ψ) -∗
      @wpEvStep hlc GF _ (shG GD N obSt0 obi nm) pol Unit GD i k (fun _ => True)
        (fun _ => graphData GD (i, k) = some (WeakInterpProj.wbytes 1 val)) (fun _ => k + 1)
        (fun _ => Ψ) := by
  iintro Hx HΨ
  unfold wpEvStep
  iintro %na ⟨Hpg, Hannot⟩
  ihave %Hnin := naAtProgressNotElemOf GD i k na $$ Hpg
  imod histAppend γ (paZ pa) Hh0 ((i, k), val) $$ Hx with Hx
  ihave #Hsn := histSnapGet γ (paZ pa) 1 (Hh0 ++ [((i, k), val)]) $$ Hx
  imod annotAlloc na (i, k) iprop(True) Hnin $$ Hannot with ⟨Hannot, -⟩
  imodintro
  inext
  imodintro
  have Hlbl : gxLbl GD.gdG (i, k) = some (.LStore false (paZ pa) [val] cls) := by
    rw [gxLblGrow]; exact Hl
  obtain ⟨Hwb, Hsingle⟩ := gwbStore _ _ _ _ _ Hlbl
  iexists (), iprop(True), (∅ : Mea GF), (∅ : Mea GF), ()
  isplitr
  · ipureintro
    trivial
  isplitr
  · iapply AxSpinWit.naSplittingWfEmpty
  isplitr [Hannot HΨ Hx]
  · unfold flowEqDyn
    iintro %σ %sOb %Hsub %Hnin' Hob' _
    iapply fupd_mask_intro LawfulSet.empty_subset
    iintro Hclose
    inext
    imod Hclose
    imodintro
    iexists σ
    isplitl [Hob']
    · iapply (Hob GD σ _).2
      ihave Hob' := (Hob GD σ sOb).1 $$ Hob'
      iapply (protInvWriteSnap γ GD sOb (i, k) (paZ pa) val Hh0 Hnin' Hwb Hsingle) $$ Hob' Hsn
    · isplitr
      · itrivial
      · ipureintro
        unfold graphData
        rw [Hlbl]
        simp [lblData, l3pWbytes1]
  isplitl [Hannot]
  · rw [AxLockWp.annotInsertEq na (i, k) iprop(True)]
    iexact Hannot
  isplitr
  · iapply AxSpinWit.localTrue
  · iapply HΨ $$ Hx

end shells

/-! # 7. THE PER-HART WPds AT THE REAL PROTOCOL -/

section wpdReal
variable {hlc : HasLC} {GF : BundledGFunctors.{0,0,0}} [InvGS_gen hlc GF] [AxannotGS GF]
  [AxlogG GF Hent]

theorem spROb (GT : GdexecT) (γ : GName) :
    ∀ (GD' : Gdexec) (σ : @AxirisG.obSt GF (shG (gtAdGd GT) GName Unit spOb γ)) (s : GSet Geid),
      @AxirisG.obStInterp GF (shG (gtAdGd GT) GName Unit spOb γ) GD' σ s ⊣⊢ protInv γ GD' s :=
  fun _ _ _ => .rfl

/-- 7.1 Hart A, the positive program `sd f 1; HALT`, owning f. -/
theorem AxSpinWit.wpdA (GT : GdexecT) (γ : GName) (cpu : CPU)
    (HrowA : AxOpsem.grow (gtAdGd GT) hA = saRow) :
    ⊢ histAuth (GF := GF) γ ya 1 [] -∗
      @tierAWpd GF hlc _ _ (spPol GT) (gtAdGd GT) GName Unit spOb γ ⟨hp cpu saM0 zeroRegs, 0⟩
        .MaybeStuck hA (fun _ => iprop(True)) := by
  have Hne : 0 ≠ (AxOpsem.grow (gtAdGd GT) hA).length := by rw [HrowA]; decide
  have Hl0 : (AxOpsem.grow (gtAdGd GT) hA)[0]? = some (.LStore false (paZ ypaM) [b1] .WCplain) := by
    rw [HrowA]; rfl
  have H := shPos (hlc := hlc) (GF := GF) (pol := spPol GT) (gtAdGd GT) GName Unit spOb γ cpu hA
    (fun _ => iprop(True)) (histAuth γ (paZ ypaM) 1 []) 0 saM0 Hne
    (fun rs id K => noReadAtWrite cpu _ ypaM ypaMRam b1 hlt rs 0 id K)
    (fun rs l s' Hst => by
      obtain ⟨rfl, Hs', -⟩ := writeInv2 cpu _ ypaM ypaMRam b1 hlt rs 0 l s' Hst
      simp only [wlWdata]
      subst Hs'
      iintro Hy
      iapply (shOwnedStore (hlc := hlc) (pol := spPol GT) (gtAdGd GT) GName Unit spOb γ γ
        (spROb GT γ) hA 0 ypaM b1 .WCplain [] Hl0 _) $$ Hy
      iintro _
      iapply (shHltTrue (hlc := hlc) (pol := spPol GT) (gtAdGd GT) GName Unit spOb γ cpu hA
        (0 + 1)) $$ %rs)
  rw [show ya = paZ ypaM from rfl]
  iintro Hy
  iapply H $$ Hy %zeroRegs

/-! ## 7.2 Hart B: `ld f; branch; sd x 1 (owned); ld x (reload); HALT` -/

theorem sbBLbl (GT : GdexecT) (tf tx : Nat) (vx : BitVec 8)
    (Hrow : AxOpsem.grow (gtAdGd GT) hB = sbRow tf tx vx) (k : Nat) (lb : Lbl) :
    (sbRow tf tx vx)[k]? = some lb → gxLbl (gtAdGd GT).gdG (hB, k) = some lb := by
  intro Hk
  rw [gxLblGrow, Hrow]
  exact Hk

/-- The reload's annotation: the OWNERSHIP fact (any value the reload reads at x is the
spilled 1). -/
def RB {GF : BundledGFunctors} (GT : GdexecT) : IProp GF :=
  iprop(⌜∀ t v, greadsByte (gtAdGd GT).gdG (hB, 2) xa t v → v = b1⌝)

theorem wpdB2 (GT : GdexecT) (γ : GName) (cpu : CPU) (tf tx : Nat) (vx : BitVec 8)
    (Hrow : AxOpsem.grow (gtAdGd GT) hB = sbRow tf tx vx)
    (Hcons : rvwmoCatConsistent (gtAdGd GT)) :
    ⊢ histAuth (GF := GF) γ xa 1 [((hB, 1), b1)] -∗ ∀ rs : RegFile,
      @tierAWpd GF hlc _ _ (spPol GT) (gtAdGd GT) GName Unit spOb γ ⟨hp cpu sbM2 rs, 2⟩
        .MaybeStuck hB (fun _ => iprop(⌜vx = b1⌝)) := by
  have Hne : 2 ≠ (AxOpsem.grow (gtAdGd GT) hB).length := by rw [Hrow]; simp [sbRow]
  have Hadv : ∀ lb, (AxOpsem.grow (gtAdGd GT) hB)[2]? = some lb → aidentAdvRd (aident lb) = 1 := by
    rw [Hrow]
    intro lb h
    cases h
    rfl
  have Hl1 : gxLbl (gtAdGd GT).gdG (hB, 1) = some (.LStore false xa [b1] .WCplain) :=
    sbBLbl GT tf tx vx Hrow 1 _ rfl
  have Hl2 : gxLbl (gtAdGd GT).gdG (hB, 2) = some (.LLoad false xa [tx] [vx]) :=
    sbBLbl GT tf tx vx Hrow 2 _ rfl
  have Hl0 : gxLbl (gtAdGd GT).gdG (hB, 0) = some (.LLoad false ya [tf] [b1]) :=
    sbBLbl GT tf tx vx Hrow 0 _ rfl
  iapply (shRead (hlc := hlc) (pol := spPol GT) (gtAdGd GT) GName Unit spOb γ cpu hB
    (fun _ => iprop(⌜vx = b1⌝)) xpaM xpaMRam (fun _ => hlt) 2 Hne Hadv
    (histAuth γ xa 1 [((hB, 1), b1)]) ?_)
  intro v b rs Hgv Hv
  subst Hv
  iintro Hx
  unfold wpEvStep
  iintro %na ⟨Hpg, Hannot⟩
  ihave %Hnin := naAtProgressNotElemOf (gtAdGd GT) hB 2 na $$ Hpg
  imod annotAlloc na (hB, 2) (RB (GF := GF) GT) Hnin $$ Hannot with ⟨Hannot, Hfrag⟩
  imodintro
  inext
  imodintro
  iexists (), RB (GF := GF) GT, (∅ : Mea GF), (∅ : Mea GF), ()
  isplitr
  · ipureintro
    trivial
  isplitr
  · iapply AxSpinWit.naSplittingWfEmpty
  isplitl [Hx]
  · -- THE OWNED-READ FLOW EQUATION: drawn on the hart's OWN token (the history appended at the
    -- spill in phase 1), NOT on the spill's annotation.
    have Hmem : ((hB, 2) : Geid) ∈ (gtAdGd GT).gdG.gxGmo :=
      gwfMemGmo _ _ Hcons.1 ⟨_, Hl2, rfl⟩
    have Hnw : gisW (gtAdGd GT).gdG (hB, 2) = false := by unfold gisW; rw [Hl2]; rfl
    have Hwr : ∀ p, p ∈ [(((hB, 1) : Geid), b1)] → gwritesByte (gtAdGd GT).gdG p.1 xa p.2 := by
      intro p hp
      simp only [List.mem_singleton] at hp
      subst hp
      exact (gwbStore _ _ _ _ _ Hl1).1
    have Hch : chainWith (gmoLt (gtAdGd GT).gdG) ([(((hB, 1) : Geid), b1)].map Prod.fst) := by
      intro j w1 w2 _ H2
      simp at H2
    have Hown : ∀ w v, gwritesByte (gtAdGd GT).gdG w xa v →
        WeakRvwmoGraph.gpo (gtAdGd GT).gdG w (hB, 2) →
        w ∈ [(((hB, 1) : Geid), b1)].map Prod.fst := by
      rintro ⟨wi, wk⟩ v' Hwb ⟨Hh, Hlt, -, -⟩
      simp only at Hh Hlt
      subst Hh
      match wk, Hlt with
      | 0, _ =>
        have h := AxProt.gwritesByteGisW _ _ _ _ Hwb
        unfold gisW at h
        rw [Hl0] at h
        cases h
      | 1, _ => simp
      | _ + 2, h => omega
    have Hrd : ∃ t v, greadsByte (gtAdGd GT).gdG (hB, 2) xa t v :=
      ⟨tx, vx, grbLoad _ _ _ _ _ Hl2⟩
    have Hcov : ∀ w v, gwritesByte (gtAdGd GT).gdG w xa v → gmoLt (gtAdGd GT).gdG w (hB, 2) →
        w ∈ @Axpol.sPol (spPol GT) (gtAdGd GT) (hB, 2) :=
      fun w v' Hwb Hlt => spSpolCov GT (gtAdGd GT) (hB, 2) w xa v' Hwb Hlt
    have Hpo12 : WeakRvwmoGraph.gpo (gtAdGd GT).gdG (hB, 1) (hB, 2) :=
      ⟨rfl, by decide, by rw [Hl1]; rfl, by rw [Hl2]; rfl⟩
    have Hdom : (FiniteMap.dom_set ({[((hB, 1) : Geid) := (1 : Qp)]} : GMapF Geid Qp) :
        GSet Geid) = {(hB, 1)} := domSingleton
    have Hcase : (∃ e, e ∈ (FiniteMap.dom_set ({[((hB, 1) : Geid) := (1 : Qp)]} : GMapF Geid Qp) :
          GSet Geid) ∧ gmoLt (gtAdGd GT).gdG e (hB, 2)) ∨
        (((hB, 1) : Geid) ∈ (FiniteMap.dom_set ({[((hB, 1) : Geid) := (1 : Qp)]} :
            GMapF Geid Qp) : GSet Geid) ∧
         (∀ e, e ∈ (FiniteMap.dom_set ({[((hB, 1) : Geid) := (1 : Qp)]} : GMapF Geid Qp) :
            GSet Geid) → ¬ gmoLt (gtAdGd GT).gdG e (hB, 2)) ∧
         WeakRvwmoGraph.gpo (gtAdGd GT).gdG (hB, 1) (hB, 2) ∧
         (∀ w' v', gwritesByte (gtAdGd GT).gdG w' xa v' →
           WeakRvwmoGraph.gpo (gtAdGd GT).gdG (hB, 1) w' →
           WeakRvwmoGraph.gpo (gtAdGd GT).gdG w' (hB, 2) → False)) := by
      rw [Hdom]
      cases Hb : gmoLtB (gtAdGd GT).gdG (hB, 1) (hB, 2) with
      | true =>
        -- the spill is gmo-before: the GHOST route (case (i))
        exact .inl ⟨(hB, 1), elemOfSingleton.2 rfl, (gmoLtBSpec _ _ _).1 Hb⟩
      | false =>
        -- forwarded / deferred: case (ii)
        refine .inr ⟨elemOfSingleton.2 rfl, ?_, Hpo12, ?_⟩
        · intro e He Hlt
          obtain rfl := elemOfSingleton.1 He
          rw [(gmoLtBSpec _ _ _).2 Hlt] at Hb
          cases Hb
        · rintro w' v' - ⟨-, H1, -⟩ ⟨-, H2, -⟩
          simp only at H1 H2
          omega
    iapply (@flowEqDynMono hlc GF _ (shG (gtAdGd GT) GName Unit spOb γ) (spPol GT) (gtAdGd GT)
      (hB, 2) _ (∅ : Mea GF)
      iprop(⌜∀ t v, greadsByte (gtAdGd GT).gdG (hB, 2) xa t v → v = b1⌝) _) $$ [] [Hx]
    · inext
      iintro HR
      isplitl [HR]
      · unfold RB
        iexact HR
      · ipureintro
        exact Hgv
    · iapply (flowEqOwnedReadByte (axG := shG (gtAdGd GT) GName Unit spOb γ) γ (spROb GT γ)
        (gtAdGd GT) (hB, 2) xa [(((hB, 1) : Geid), b1)] {[((hB, 1) : Geid) := (1 : Qp)]} (hB, 1)
        b1 (@Axpol.sPol (spPol GT) (gtAdGd GT) (hB, 2)) ∅ Hcons Hmem Hnw Hwr Hch Hown rfl Hrd
        Hcase Hcov)
      iintro _
      unfold tokTie
      isplitl [Hx]
      · iapply (tokSingleton γ xa [(((hB, 1) : Geid), b1)] (hB, 1) 1).2
        iexact Hx
      · ipureintro
        intro e He
        rw [Hdom, elemOfSingleton] at He
        subst He
        exact tieWrite (gtAdGd GT).gdG [] (hB, 1) b1
  isplitl [Hannot]
  · rw [AxLockWp.annotInsertEq na (hB, 2) (RB GT)]
    iexact Hannot
  isplitr
  · iapply AxSpinWit.localTrue
  · iapply (shHltReadback (hlc := hlc) (pol := spPol GT) (gtAdGd GT) GName Unit spOb γ cpu hB
      (2 + 1) (hB, 2) rfl (RB GT) (vx = b1)
      (by unfold RB; exact pure_mono (fun HR => HR tx vx (grbLoad _ _ _ _ _ Hl2)))) $$ Hfrag %rs

theorem wpdB1 (GT : GdexecT) (γ : GName) (cpu : CPU) (tf tx : Nat) (vx : BitVec 8)
    (Hrow : AxOpsem.grow (gtAdGd GT) hB = sbRow tf tx vx)
    (Hcons : rvwmoCatConsistent (gtAdGd GT)) :
    ⊢ histAuth (GF := GF) γ xa 1 [] -∗ ∀ rs : RegFile,
      @tierAWpd GF hlc _ _ (spPol GT) (gtAdGd GT) GName Unit spOb γ ⟨hp cpu sbM1 rs, 1⟩
        .MaybeStuck hB (fun _ => iprop(⌜vx = b1⌝)) := by
  have Hne : 1 ≠ (AxOpsem.grow (gtAdGd GT) hB).length := by rw [Hrow]; simp [sbRow]
  have Hl1 : (AxOpsem.grow (gtAdGd GT) hB)[1]? = some (.LStore false (paZ xpaM) [b1] .WCplain) := by
    rw [Hrow]; rfl
  have Hbr : histAuth (GF := GF) γ (paZ xpaM) 1 ([] ++ [((hB, 1), b1)]) ⊢
      histAuth γ xa 1 [((hB, 1), b1)] := .rfl
  rw [show xa = paZ xpaM from rfl]
  exact shPos (hlc := hlc) (pol := spPol GT) (gtAdGd GT) GName Unit spOb γ cpu hB
    (fun _ => iprop(⌜vx = b1⌝)) (histAuth γ (paZ xpaM) 1 []) 1 sbM1 Hne
    (fun rs id K => noReadAtWrite cpu _ xpaM xpaMRam b1 sbM2 rs 1 id K)
    (fun rs l s' Hst => by
      obtain ⟨rfl, Hs', -⟩ := writeInv2 cpu _ xpaM xpaMRam b1 sbM2 rs 1 l s' Hst
      simp only [wlWdata]
      subst Hs'
      iintro Hx
      iapply (shOwnedStore (hlc := hlc) (pol := spPol GT) (gtAdGd GT) GName Unit spOb γ γ
        (spROb GT γ) hB 1 xpaM b1 .WCplain [] Hl1 _) $$ Hx
      iintro Hx
      ihave Hx := Hbr $$ Hx
      iapply (wpdB2 GT γ cpu tf tx vx Hrow Hcons) $$ Hx %rs)

theorem wpdB0 (GT : GdexecT) (γ : GName) (cpu : CPU) (tf tx : Nat) (vx : BitVec 8)
    (Hrow : AxOpsem.grow (gtAdGd GT) hB = sbRow tf tx vx)
    (Hcons : rvwmoCatConsistent (gtAdGd GT)) :
    ⊢ histAuth (GF := GF) γ xa 1 [] -∗ ∀ rs : RegFile,
      @tierAWpd GF hlc _ _ (spPol GT) (gtAdGd GT) GName Unit spOb γ ⟨hp cpu sbM0 rs, 0⟩
        .MaybeStuck hB (fun _ => iprop(⌜vx = b1⌝)) := by
  have Hne : 0 ≠ (AxOpsem.grow (gtAdGd GT) hB).length := by rw [Hrow]; simp [sbRow]
  have Hadv : ∀ lb, (AxOpsem.grow (gtAdGd GT) hB)[0]? = some lb → aidentAdvRd (aident lb) = 1 := by
    rw [Hrow]
    intro lb h
    cases h
    rfl
  have Hl0 : gxLbl (gtAdGd GT).gdG (hB, 0) = some (.LLoad false ya [tf] [b1]) :=
    sbBLbl GT tf tx vx Hrow 0 _ rfl
  iapply (shRead (hlc := hlc) (pol := spPol GT) (gtAdGd GT) GName Unit spOb γ cpu hB
    (fun _ => iprop(⌜vx = b1⌝)) ypaM ypaMRam sbK 0 Hne Hadv (histAuth γ xa 1 []) ?_)
  intro v b rs Hgv Hv
  subst Hv
  have Hb : b = b1 := by
    have h : graphValue (gtAdGd GT) (hB, 0) = some [b1] := by
      unfold graphValue
      rw [Hl0]
      rfl
    rw [h] at Hgv
    exact ((List.cons.inj (Option.some.inj Hgv)).1).symm
  subst Hb
  rw [AxSpinWit.sbKOk, if_pos rfl]
  iintro Hx
  unfold wpEvStep
  iintro %na ⟨Hpg, Hannot⟩
  ihave %Hnin := naAtProgressNotElemOf (gtAdGd GT) hB 0 na $$ Hpg
  imod annotAlloc na (hB, 0) iprop(True) Hnin $$ Hannot with ⟨Hannot, -⟩
  imodintro
  inext
  imodintro
  iexists (), iprop(True), (∅ : Mea GF), (∅ : Mea GF), ()
  isplitr
  · ipureintro
    trivial
  isplitr
  · iapply AxSpinWit.naSplittingWfEmpty
  isplitr [Hannot Hx]
  · -- the RACY read of f: validated by nothing, deposits nothing
    have Hnw : gisW (gtAdGd GT).gdG (hB, 0) = false := by unfold gisW; rw [Hl0]; rfl
    unfold flowEqDyn
    iintro %σ %sOb %Hsub %Hnin' Hob _
    iapply fupd_mask_intro LawfulSet.empty_subset
    iintro Hclose
    inext
    imod Hclose
    imodintro
    iexists σ
    isplitl [Hob]
    · iapply (spROb GT γ (gtAdGd GT) σ _).2
      ihave Hob := (spROb GT γ (gtAdGd GT) σ sOb).1 $$ Hob
      iapply (protInvReadStep γ (gtAdGd GT) sOb (hB, 0) Hnin' Hnw)
      iexact Hob
    · isplitr
      · itrivial
      · ipureintro
        exact Hgv
  isplitl [Hannot]
  · rw [AxLockWp.annotInsertEq na (hB, 0) iprop(True)]
    iexact Hannot
  isplitr
  · iapply AxSpinWit.localTrue
  · iapply (wpdB1 GT γ cpu tf tx vx Hrow Hcons) $$ Hx %rs

theorem AxSpinWit.wpdB (GT : GdexecT) (γ : GName) (cpu : CPU) (tf tx : Nat) (vx : BitVec 8)
    (Hrow : AxOpsem.grow (gtAdGd GT) hB = sbRow tf tx vx)
    (Hcons : rvwmoCatConsistent (gtAdGd GT)) :
    ⊢ histAuth (GF := GF) γ xa 1 [] -∗
      @tierAWpd GF hlc _ _ (spPol GT) (gtAdGd GT) GName Unit spOb γ ⟨hp cpu sbM0 zeroRegs, 0⟩
        .MaybeStuck hB (fun _ => iprop(⌜vx = b1⌝)) := by
  iintro Hx
  iapply (wpdB0 GT γ cpu tf tx vx Hrow Hcons) $$ Hx %zeroRegs

end wpdReal

/-! # 8. THE CAPSTONE: `tierAAdequacyAnnGateT` at the tagged port -/

section spGFSec

open Iris.Algebra

/-- Rocq `spΣ := #[invΣ; axlogΣ hent; axannotΣ]`. -/
def spGF : BundledGFunctors :=
  BundledGFunctors.default
  |>.set 0 ⟨InvMapF, inferInstance⟩
  |>.set 1 ⟨constOF CoPsetDisjL, inferInstance⟩
  |>.set 2 ⟨constOF (DisjointLeibnizSet PosSet), inferInstance⟩
  |>.set 3 ⟨Auth.AuthURF (constOF Credit), inferInstance⟩
  |>.set 4 ⟨AxlogRF Hent, inferInstance⟩
  |>.set 5 ⟨DFracAgree.DFracAgreeRF (LaterOF IdOF), inferInstance⟩
  |>.set 6 ⟨constOF (HeapView Geid (Agree (DiscreteO GName)) (GMapF Geid)), inferInstance⟩
  |>.set 7 ⟨constOF AxannotSetR, inferInstance⟩

instance AxSpinWit.spGFInvMap : ElemG spGF InvMapF := ⟨0, rfl⟩
instance AxSpinWit.spGFEnabled : ElemG spGF (constOF CoPsetDisjL) := ⟨1, rfl⟩
instance AxSpinWit.spGFDisabled : ElemG spGF (constOF (DisjointLeibnizSet PosSet)) := ⟨2, rfl⟩
instance AxSpinWit.spGFCredit : ElemG spGF (Auth.AuthURF (constOF Credit)) := ⟨3, rfl⟩
instance AxSpinWit.spGFInvGpreS : InvGpreS spGF :=
  ⟨⟨inferInstance, inferInstance, inferInstance⟩, ⟨inferInstance⟩⟩
instance AxSpinWit.spGFAxlogG : AxlogG spGF Hent := { axlogInG := ⟨4, rfl⟩ }
instance AxSpinWit.spGFAxannotG : AxannotG spGF :=
  { axannotSavedG := { elemG := ⟨5, rfl⟩ }, axannotMapG := ⟨⟨6, rfl⟩⟩, axannotSetG := ⟨7, rfl⟩ }

end spGFSec

/-- Lean-only (Rocq `set s0`). -/
def AxSpinWit.cS0 (sA0 : Athread) (i : Agent) : Athread :=
  if i = hA then sA0 else ⟨hp cpu0 sbM0 zeroRegs, 0⟩
/-- Lean-only (Rocq `set sN`). -/
def AxSpinWit.cSN (sAN : Athread) (i : Agent) : Athread :=
  if i = hA then sAN else ⟨hp cpu0 hlt zeroRegs, 3⟩
/-- Lean-only (Rocq `set nf`). -/
def AxSpinWit.cN (nA : Nat) (i : Agent) : Nat := if i = hA then nA else 3
/-- Lean-only (Rocq `set post`). -/
def AxSpinWit.cPost (vx : BitVec 8) (i : Agent) (_ : Athread) : Prop :=
  if i = hB then vx = b1 else True

theorem spinReloadOwned (GT : GdexecT)
    (HconsT : rvwmoCatConsistentT GT) (Hcl : ctrlClosed GT)
    (Hharts : ∀ e, e ∈ GT.gtG.gxGmo → e.1 = hA ∨ e.1 = hB)
    (tf tx : Nat) (vx : BitVec 8) (HrowB : AxOpsem.grow (gtAdGd GT) hB = sbRow tf tx vx)
    (sA0 sAN : Athread) (nA : Nat)
    (HrunA : ∀ (_ : AxannotGS spGF) (nm : GName),
      nsteps (tierAAstep (gtAdGd GT) nm hA) nA sA0 sAN)
    (HkA : sA0.atK = 0) (HendA : sAN.atK = (AxOpsem.grow (gtAdGd GT) hA).length)
    (HwpA : ∀ [InvGS_gen .hasNoLC spGF] [AxannotGS spGF] (nm : GName),
      ⊢ spInit nm hA -∗
        @tierAWpd spGF .hasNoLC _ _ (spPol GT) (gtAdGd GT) GName Unit spOb nm sA0 .MaybeStuck hA
          (fun _ => iprop(True))) :
    vx = b1 := by
  have Hin01 : ∀ i : Agent, i ∈ [hA, hB] → i = hA ∨ i = hB := by
    intro i Hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at Hi
    exact Hi
  have Hnd : [hA, hB].Nodup := by decide
  have Hharts' : ∀ e, e ∈ GT.gtG.gxGmo → e.1 ∈ [hA, hB] := by
    intro e He
    rcases Hharts e He with H | H <;> rw [H] <;> simp
  have Hcons := catTAd GT HconsT
  have Hrun : ∀ (_ : AxannotGS spGF) (nm : GName) i, i ∈ [hA, hB] →
      nsteps (tierAAstep (gtAdGd GT) nm i) (AxSpinWit.cN nA i) (AxSpinWit.cS0 sA0 i)
        (AxSpinWit.cSN sAN i) := by
    intro Hann nm i Hi
    rcases Hin01 i Hi with rfl | rfl
    · exact HrunA Hann nm
    · exact sbRun cpu0 (gtAdGd GT) tf tx vx HrowB
  have Hk0 : ∀ i, i ∈ [hA, hB] → (AxSpinWit.cS0 sA0 i).atK = 0 := by
    intro i Hi
    rcases Hin01 i Hi with rfl | rfl
    · exact HkA
    · rfl
  have Hend : ∀ i, i ∈ [hA, hB] →
      (AxSpinWit.cSN sAN i).atK = (AxOpsem.grow (gtAdGd GT) i).length := by
    intro i Hi
    rcases Hin01 i Hi with rfl | rfl
    · exact HendA
    · show 3 = (AxOpsem.grow (gtAdGd GT) hB).length
      rw [HrowB]
      rfl
  have Hwp : ∀ [InvGS_gen .hasNoLC spGF] [AxannotGS spGF] (nm : GName),
      ⊢ ([∗list] i ∈ [hA, hB], spInit nm i) -∗
        [∗list] i ∈ [hA, hB],
          @tierAWpd spGF .hasNoLC _ _ (spPol GT) (gtAdGd GT) GName Unit spOb nm
            (AxSpinWit.cS0 sA0 i) .MaybeStuck i (fun s => iprop(⌜AxSpinWit.cPost vx i s⌝)) := by
    intro Hinv Hann nm
    iintro HI
    icases (AxTokLedgerMp.bigSepLPair hA hB (fun i => spInit (GF := spGF) nm i)).1 $$ HI
      with ⟨HA, HB⟩
    iapply (AxTokLedgerMp.bigSepLPair hA hB _).2
    rw [show AxSpinWit.cS0 sA0 hA = sA0 from if_pos rfl,
      show AxSpinWit.cS0 sA0 hB = ⟨hp cpu0 sbM0 zeroRegs, 0⟩ from if_neg (by decide)]
    isplitl [HA]
    · iapply (AxSpinWit.tierAWpdMono (hlc := .hasNoLC) (pol := spPol GT) (gtAdGd GT) GName Unit
        spOb nm sA0 .MaybeStuck hA (fun _ => iprop(True))
        (fun s => iprop(⌜AxSpinWit.cPost vx hA s⌝))
        (fun _ => pure_mono (fun _ => by unfold AxSpinWit.cPost; rw [if_neg (by decide)]; trivial)))
      iapply HwpA nm $$ HA
    · iapply (AxSpinWit.tierAWpdMono (hlc := .hasNoLC) (pol := spPol GT) (gtAdGd GT) GName Unit
        spOb nm ⟨hp cpu0 sbM0 zeroRegs, 0⟩ .MaybeStuck hB (fun _ => iprop(⌜vx = b1⌝))
        (fun s => iprop(⌜AxSpinWit.cPost vx hB s⌝))
        (fun _ => pure_mono (fun Hv => by unfold AxSpinWit.cPost; rw [if_pos rfl]; exact Hv)))
      rw [AxSpinWit.spInitB]
      iapply (AxSpinWit.wpdB (hlc := .hasNoLC) GT nm cpu0 tf tx vx HrowB Hcons) $$ HB
  have Hfin := @tierAAdequacyAnnGateT spGF _ _ (spPol GT) GT GName Unit spOb spInit
    (spAxpolWf GT) HconsT [hA, hB] Hnd Hharts' (AxSpinWit.cS0 sA0) (AxSpinWit.cSN sAN)
    (AxSpinWit.cN nA) Hrun Hk0 Hend (AxSpinWit.cPost vx) Hwp (spHobAlloc (gtAdGd GT))
    (spHok GT HconsT Hcl) hB (by simp)
  exact (if_pos rfl : AxSpinWit.cPost vx hB _ = (vx = b1)) ▸ Hfin

/-! # 9. CERTIFICATE (a): SATISFIABILITY on the DEFERRED graph `spw` (and on `spl`) -/

theorem spwHarts : ∀ e, e ∈ spw.gtG.gxGmo → e.1 = hA ∨ e.1 = hB := by
  intro e He
  have h : spw.gtG.gxGmo.all (fun e : Geid => decide (e.1 = hA ∨ e.1 = hB)) = true := by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.1 h e He)

theorem splHarts : ∀ e, e ∈ spl.gtG.gxGmo → e.1 = hA ∨ e.1 = hB := by
  intro e He
  have h : spl.gtG.gxGmo.all (fun e : Geid => decide (e.1 = hA ∨ e.1 = hB)) = true := by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.1 h e He)

theorem AxSpinWit.sprHarts : ∀ e, e ∈ AxSpinWit.spr.gtG.gxGmo → e.1 = hA ∨ e.1 = hB := by
  intro e He
  have h : AxSpinWit.spr.gtG.gxGmo.all (fun e : Geid => decide (e.1 = hA ∨ e.1 = hB)) = true := by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.1 h e He)

/-- Hart A's WPd at the real protocol, the positive program, ANY graph whose hart-A row is
`saRow`. -/
theorem saWpd (GT : GdexecT) (HrowA : AxOpsem.grow (gtAdGd GT) hA = saRow) :
    ∀ [InvGS_gen .hasNoLC spGF] [AxannotGS spGF] (nm : GName),
      ⊢ spInit nm hA -∗
        @tierAWpd spGF .hasNoLC _ _ (spPol GT) (gtAdGd GT) GName Unit spOb nm
          ⟨hp cpu0 saM0 zeroRegs, 0⟩ .MaybeStuck hA (fun _ => iprop(True)) := by
  intro _ _ nm
  rw [AxSpinWit.spInitA]
  exact AxSpinWit.wpdA GT nm cpu0 HrowA

theorem saRunT (GT : GdexecT) (HrowA : AxOpsem.grow (gtAdGd GT) hA = saRow) :
    ∀ (_ : AxannotGS spGF) (nm : GName),
      nsteps (tierAAstep (gtAdGd GT) nm hA) 1 ⟨hp cpu0 saM0 zeroRegs, 0⟩
        ⟨hp cpu0 hlt zeroRegs, 1⟩ :=
  fun _ _ => saRun cpu0 (gtAdGd GT) HrowA

/-- EVERY premise of `spinReloadOwned` on `spw`, as one conjunction. -/
theorem spwPremises :
    rvwmoCatConsistentT spw ∧ ctrlClosed spw ∧
    (∀ e, e ∈ spw.gtG.gxGmo → e.1 = hA ∨ e.1 = hB) ∧
    AxOpsem.grow (gtAdGd spw) hB = sbRow 1 2 b1 ∧
    (∀ (_ : AxannotGS spGF) (nm : GName),
      nsteps (tierAAstep (gtAdGd spw) nm hA) 1 ⟨hp cpu0 saM0 zeroRegs, 0⟩
        ⟨hp cpu0 hlt zeroRegs, 1⟩) ∧
    (⟨hp cpu0 saM0 zeroRegs, 0⟩ : Athread).atK = 0 ∧
    (⟨hp cpu0 hlt zeroRegs, 1⟩ : Athread).atK = (AxOpsem.grow (gtAdGd spw) hA).length ∧
    (∀ [InvGS_gen .hasNoLC spGF] [AxannotGS spGF] (nm : GName),
      ⊢ spInit nm hA -∗
        @tierAWpd spGF .hasNoLC _ _ (spPol spw) (gtAdGd spw) GName Unit spOb nm
          ⟨hp cpu0 saM0 zeroRegs, 0⟩ .MaybeStuck hA (fun _ => iprop(True))) :=
  ⟨spwCatT, spwCtrlClosed, spwHarts, rfl, saRunT spw rfl, rfl, rfl, saWpd spw rfl⟩

/-- The capstone at `spw`: the route is driven end to end on a graph where the reload IS deferred
(`spwLcanon`) and IS handed its gmo-later gate source (`spwBackwardHandout`). -/
theorem spwSound : b1 = b1 :=
  spinReloadOwned spw spwCatT spwCtrlClosed spwHarts 1 2 b1 rfl _ _ 1 (saRunT spw rfl) rfl rfl
    (saWpd spw rfl)

theorem spwGateWitness :
    ((hB, 0) : Geid) ∈ gsrcT spw (hB, 2) ∧
    Lcanon (gtAdGd spw) (gsrcT spw) = [(hA, 0), (hB, 0), (hB, 2), (hB, 1)] ∧
    spw.gtG.gxGmo ≠ Lcanon (gtAdGd spw) (gsrcT spw) ∧
    ((hB, 0) : Geid) ∈ @Axpol.sPol (spPol spw) (gtAdGd spw) (hB, 2) ∧
    ¬ gmoLt spw.gtG (hB, 0) (hB, 2) ∧
    ¬ gmoLt spw.gtG (hB, 1) (hB, 2) := by
  refine ⟨spwGsrcReload, spwLcanon, spwNotGmo, spwBackwardHandout.1, spwBackwardHandout.2, ?_⟩
  intro Hlt
  have h := (gmoLtBSpec _ _ _).2 Hlt
  have hf : gmoLtB spw.gtG (hB, 1) (hB, 2) = false := by decide +kernel
  rw [hf] at h
  cases h

/-- The non-deferred twin (owned-read case (i), the ghost route). -/
theorem splSound : b1 = b1 :=
  spinReloadOwned spl splCatT splCtrlClosed splHarts 1 2 b1 rfl _ _ 1 (saRunT spl rfl) rfl rfl
    (saWpd spl rfl)

theorem splSpillGmoBefore : gmoLt spl.gtG (hB, 1) (hB, 2) :=
  (gmoLtBSpec _ _ _).1 (by decide +kernel)

/-! # 10. CERTIFICATE (b): THE RACE -- hart A's `sd f 1; sd x 2` has NO WPd at the real
protocol (x is owned by hart B). -/

theorem raRunT : ∀ (_ : AxannotGS spGF) (nm : GName),
    nsteps (tierAAstep (gtAdGd AxSpinWit.spr) nm hA) 2 ⟨hp cpu0 raM0 zeroRegs, 0⟩
      ⟨hp cpu0 hlt zeroRegs, 2⟩ :=
  fun _ _ => raRun cpu0 (gtAdGd AxSpinWit.spr) rfl

theorem sprReloadReadsRace : graphValue (gtAdGd AxSpinWit.spr) (hB, 2) = some [b2] := by
  decide +kernel

theorem AxSpinWit.sprWpdUnprovable :
    ¬ (∀ [InvGS_gen .hasNoLC spGF] [AxannotGS spGF] (nm : GName),
        ⊢ spInit nm hA -∗
          @tierAWpd spGF .hasNoLC _ _ (spPol AxSpinWit.spr) (gtAdGd AxSpinWit.spr) GName Unit spOb
            nm ⟨hp cpu0 raM0 zeroRegs, 0⟩ .MaybeStuck hA (fun _ => iprop(True))) := by
  intro Hwp
  have H := spinReloadOwned AxSpinWit.spr AxSpinWit.sprCatT AxSpinWit.sprCtrlClosed
    AxSpinWit.sprHarts 1 3 b2 rfl _ _ 2 raRunT rfl rfl Hwp
  exact b1NeB2 H.symm

/-! # 11. CERTIFICATE (c): SANITY TWIN -- the SAME racy hart-A program, graph, hart, policy,
stuckness and post IS verifiable at the TRIVIAL protocol. -/

def trivOb {GF : BundledGFunctors} (_ : Unit) (_ : Gdexec) (_ : Unit) (_ : GSet Geid) :
    IProp GF :=
  iprop(True)

section twin
variable {hlc : HasLC} {GF : BundledGFunctors.{0,0,0}} [InvGS_gen hlc GF] [AxannotGS GF]

/-- Lean-only: the trivial protocol state holds. -/
theorem AxSpinWit.trivObTrue (nm : Unit) (GD' : Gdexec)
    (σ : @AxirisG.obSt GF (shG (gtAdGd AxSpinWit.spr) Unit Unit trivOb nm)) (s : GSet Geid) :
    ⊢ @AxirisG.obStInterp GF (shG (gtAdGd AxSpinWit.spr) Unit Unit trivOb nm) GD' σ s := by
  show ⊢ iprop(True)
  itrivial

theorem trivStore (nm : Unit) (i : Agent) (k : Nat) (pa : PAddr) (val : BitVec 8) (cls : WmClass)
    (Hl : (AxOpsem.grow (gtAdGd AxSpinWit.spr) i)[k]? = some (.LStore false (paZ pa) [val] cls))
    (Ψ : IProp GF) :
    ⊢ Ψ -∗ @wpEvStep hlc GF _ (shG (gtAdGd AxSpinWit.spr) Unit Unit trivOb nm)
      (spPol AxSpinWit.spr) Unit (gtAdGd AxSpinWit.spr) i k (fun _ => True)
      (fun _ => graphData (gtAdGd AxSpinWit.spr) (i, k) = some (WeakInterpProj.wbytes 1 val))
      (fun _ => k + 1) (fun _ => Ψ) := by
  iintro HΨ
  unfold wpEvStep
  iintro %na ⟨Hpg, Hannot⟩
  ihave %Hnin := naAtProgressNotElemOf (gtAdGd AxSpinWit.spr) i k na $$ Hpg
  imod annotAlloc na (i, k) iprop(True) Hnin $$ Hannot with ⟨Hannot, -⟩
  imodintro
  inext
  imodintro
  have Hlbl : gxLbl (gtAdGd AxSpinWit.spr).gdG (i, k) = some (.LStore false (paZ pa) [val] cls) := by
    rw [gxLblGrow]; exact Hl
  iexists (), iprop(True), (∅ : Mea GF), (∅ : Mea GF), ()
  isplitr
  · ipureintro
    trivial
  isplitr
  · iapply AxSpinWit.naSplittingWfEmpty
  isplitr [Hannot HΨ]
  · unfold flowEqDyn
    iintro %σ %sOb %Hsub %Hnin' _ _
    iapply fupd_mask_intro LawfulSet.empty_subset
    iintro Hclose
    inext
    imod Hclose
    imodintro
    iexists σ
    isplitr
    · iapply AxSpinWit.trivObTrue
    · isplitr
      · itrivial
      · ipureintro
        unfold graphData
        rw [Hlbl]
        simp [lblData, l3pWbytes1]
  isplitl [Hannot]
  · rw [AxLockWp.annotInsertEq na (i, k) iprop(True)]
    iexact Hannot
  isplitr
  · iapply (AxSpinWit.localTrue (pol := spPol AxSpinWit.spr))
  · iexact HΨ

theorem sprWpdTrivGen (nm : Unit) :
    ⊢ ∀ rs : RegFile, @tierAWpd GF hlc _ _ (spPol AxSpinWit.spr) (gtAdGd AxSpinWit.spr) Unit Unit
      trivOb nm ⟨hp cpu0 raM0 rs, 0⟩ .MaybeStuck hA (fun _ => iprop(True)) := by
  have Hne0 : 0 ≠ (AxOpsem.grow (gtAdGd AxSpinWit.spr) hA).length := by decide +kernel
  have Hne1 : 0 + 1 ≠ (AxOpsem.grow (gtAdGd AxSpinWit.spr) hA).length := by decide +kernel
  have H1 := shPos (hlc := hlc) (GF := GF) (pol := spPol AxSpinWit.spr) (gtAdGd AxSpinWit.spr) Unit Unit
    trivOb nm cpu0 hA (fun _ => iprop(True)) iprop(True) (0 + 1) raM1 Hne1
    (fun rs id K => noReadAtWrite cpu0 _ xpaM xpaMRam b2 hlt rs (0 + 1) id K)
    (fun rs l s' Hst => by
      obtain ⟨rfl, Hs', -⟩ := writeInv2 cpu0 _ xpaM xpaMRam b2 hlt rs (0 + 1) l s' Hst
      simp only [wlWdata]
      subst Hs'
      iintro _
      iapply (trivStore (hlc := hlc) nm hA (0 + 1) xpaM b2 .WCplain rfl _)
      iapply (shHltTrue (hlc := hlc) (pol := spPol AxSpinWit.spr) (gtAdGd AxSpinWit.spr) Unit
        Unit trivOb nm cpu0 hA (0 + 1 + 1)) $$ %rs)
  have H0 := shPos (hlc := hlc) (GF := GF) (pol := spPol AxSpinWit.spr) (gtAdGd AxSpinWit.spr) Unit Unit
    trivOb nm cpu0 hA (fun _ => iprop(True)) iprop(True) 0 raM0 Hne0
    (fun rs id K => noReadAtWrite cpu0 _ ypaM ypaMRam b1 raM1 rs 0 id K)
    (fun rs l s' Hst => by
      obtain ⟨rfl, Hs', -⟩ := writeInv2 cpu0 _ ypaM ypaMRam b1 raM1 rs 0 l s' Hst
      simp only [wlWdata]
      subst Hs'
      iintro _
      iapply (trivStore (hlc := hlc) nm hA 0 ypaM b1 .WCplain rfl _)
      ihave H1' := H1 $$ []
      · itrivial
      iapply H1' $$ %rs)
  iintro %rs
  ihave H0' := H0 $$ []
  · itrivial
  iapply H0' $$ %rs

end twin

theorem AxSpinWit.sprWpdTrivial :
    ∀ [InvGS_gen .hasNoLC spGF] [AxannotGS spGF] (nm : Unit),
      ⊢ (iprop(emp) : IProp spGF) -∗
        @tierAWpd spGF .hasNoLC _ _ (spPol AxSpinWit.spr) (gtAdGd AxSpinWit.spr) Unit Unit trivOb
          nm ⟨hp cpu0 raM0 zeroRegs, 0⟩ .MaybeStuck hA (fun _ => iprop(True)) := by
  intro _ _ nm
  iintro _
  iapply (sprWpdTrivGen (hlc := .hasNoLC) nm) $$ %zeroRegs

end Weak
