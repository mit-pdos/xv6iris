/-
Weak: **CLOSING `AxTokLedgerWp`'s VACUITY GAP — `ledgerVerified` IS SATISFIABLE END TO END, on
message passing** (LB/AxSL).

Rocq: `iris/AxTokLedgerMp.v` @ xxvzwolszwmp.

## The Rocq header, in substance

THE MATCHED PAIR (both halves machine-checked, same graph shape):
  `mprLedgerVerified : ledgerVerified 2 AxTokLedgerMp.mpr`           (§5)
  `mprNoViolation    : ¬ gdviolationHart 2 AxTokLedgerMp.mpr`        (§5, via `adequacyViolFreeLedger`)
  `mprPlainViol      : gdviolationHart 2 mprPlain`                   (§1)
  `mprPlainNotLedgerVerified : ¬ ledgerVerified 2 mprPlain`          (§1)
i.e. mp (`sd x; fence rw,w; sd y [release class] ‖ ld.aq y; ld x`) is ledger-verified and
violation-free; its plain twin (sd y plain class) is a real violation and NOT ledger-verified.

GRAPH DEVIATION (Rocq's own, forced): `AxViol.mp` puts x/y at addresses 0/1, below `devAddr`'s RAM
floor, so no hand-built `memWrite`/`memRead` there emits a RAM label (the MMIO arm fires).
`AxTokLedgerMp.mpr` / `mprPlain` are `AxViol.mp` / `mpPlain` VERBATIM except x = 0x80001000,
y = 0x80002000; cat consistency re-checked by `decide +kernel`; the violation and the negative
twin are re-proved for `mprPlain`.

§1 the graphs; §2 hand-built `Pexv6` programs (no Sail decode, `AxLock3Prog` style): hart 0 =
`memWrite x; barrier rw_w; memWrite y; pure` (plain access kinds); hart 1 = `memRead y` (AV_plain,
AS_rel_or_acq); `memRead x; pure`; runs `h0Run` (3 steps) / `h1Run` (2 steps) in
`astepAnyNfGv mpr i`, reads at graph values.  §3 the phase-2 base protocol `baseMpr`: a
gmo-phase-indexed MAILBOX (hart 0's tokens after sd x; the two `tokPending` after the release;
hart 1's tokens after the ld.aq); `lMpr0` = both bytes held by hart 0; `ocMpr` = {x, y}.  §4 the
per-hart WPds at `axGA2 mpr … (obStInterpL ocMpr 2 baseMpr) (γ, γ)` (`imp γ`): the four joint
obligations `mprJ0..3` (the bodies of `mpFe00/02/10/11`: hold / RELEASE both into the mailbox /
ACQUIRE both along `acqFrom`'s rf arm / hold), one event rule `wpEvStepClosed`
(`wpEvStepLedgerJoint` with `naUsed = ∅`), write/fence/read position shells (Löb over the
wire-perturbed register file), row-end triviality, `wpdH0_0` / `wpdH1_0`.  §5
`mprLedgerVerified` (policy `mpPol`: full gmo-prefix `sPol`, `lobp = ∅`; `HobAlloc` from
`ledgerAlloc lMpr0`) and `mprNoViolation`.

DESIGN NOTES (as Rocq): same-hart token flow goes through the BASE mailbox, not lobp
annotations (`lobp = ∅`, every `naUsed = ∅`); `ledgerVerified`'s `base0` only sees `nm.1` while
the ledger uses `nm.2`, the link being `initMpr`'s pure conjunct `nm.1 = nm.2`; the "release" is
the INERT `WCrel` class on a plain store (`AStepWrite` ignores classes), so hart 0's program is
the same term for `mpr` and `mprPlain`; the acquire is a plain-variety, acquire-strength
`memRead` (a hand node, not realizable by Sail decode).

**Fetches (Stage C).** None: the programs are hand-built monad terms with no fetch node, so
every program label is a non-fetch label and the boot-image pin `WeakAxRealize.fetchPin` of
`astepProgNf` holds trivially (`trivial`); `mpr` has no fetch row (no 4-byte text read).

## Deviations from Rocq

1. NAMES: camelCase (map below).  Duplicated Rocq names are FILE-QUALIFIED:
   `AxTokLedgerMp.mpr`, `AxTokLedgerMp.mprCat`, `AxTokLedgerMp.wpdSkipStepOfLater'`,
   `AxTokLedgerMp.astepProgRowEndShape'`, `AxTokLedgerMp.lbAdminWlWdataNone'`.  Lean-only
   helpers are file-qualified `AxTokLedgerMp.*` (list in the name map).
2. O2 STAGE C: `AxOpsem.astepProg` has no `T`/`img` parameters and `axGA2` no `ax_text`, so the
   `T`/`img` arguments of `h_astep_write`/`h_astep_fence`/`astep_prog_row_end_shape'` are gone;
   `Tf` is still defined (downstream Rocq files name it) but is no argument of anything here.
   Lean's `astepProg` has three arms (Rocq's fetch arm is deleted), so the inversion lemmas
   (`astepWriteInv`, `astepFenceInv`, `readAstepVacuous`, `astepProgRowEndShape'`) case on three
   arms.  WPd clause (b) hands an extra `fetchPin` premise (owner Q8), ignored.
3. ACCESS-KIND PREMISES (as `AxLock3Prog` deviation 2): `h_aread`'s `ak_coh (classify ak) = false`
   ↦ `(classify ak).akIfetch = false`.  `readAstepVacuous` and `wpdReadPos` take the same extra
   premise `(classify ak).akIfetch = false` (an `AK_ifetch` node steps by the ADMIN label
   `LIFetch`, which is an `astepProg` step — the Lean statement is false without it); every use
   here discharges it by `rfl`.
4. `init_regstate` ↦ `zeroRegs` (ExecLib) in `mprS0`/`mprSN`; the runs/WPds are stated for an
   arbitrary register file `rs` (as Rocq's `∀ rs` WPds; Rocq's runs fix `init_regstate`, Lean's
   take it as an argument).  `hp cpu m rs` = `.PHart cpu m rs none ibNone`; `hp` and the
   program terms `h0M*`/`h1M*` are `abbrev`s (reducible, so the proof mode's reducible
   unification sees through them).  lean-sail shapes as
   `AxLock3Prog` deviation 3 (`.impure (.ok (.memRead 1 64 …)) k` etc.).  `cpu0 := (0 : CPU)`.
5. CONTEXTS: the §4 section context (`invGS_gen HasNoLc Σ`, `axannotGS`, `ledgerG`) ↦
   `{hlc} {GF : BundledGFunctors.{0,0,0}} [InvGS_gen hlc GF] [AxannotGS GF] [LedgerG GF]`; the
   section parameters `γ cpu` are explicit leading arguments.  Rocq's `Local Instance Imp` is
   the reducible def `imp γ` (not an instance) and Rocq's `Local Existing Instance mp_pol` is
   passed explicitly as `mpPol` (a global `Axpol` instance `axprotPol` is in scope); the
   instance-carrying constants are written `@wpEvStep hlc GF _ (imp γ) mpPol …`,
   `@wpSkipStep GF (imp γ) …`.  The Rocq `Local Notation`s `TW`/`LJ` are the Lean-only abbrevs
   `AxTokLedgerMp.TW`/`AxTokLedgerMp.LJ`.  Wand chains `A -∗ B` ↦ `⊢ A -∗ B`; `P ⊢ Q` stays;
   the `Hb`/`Hcont` premises of the shells are `⊢ P -∗ …`.
6. `mprΣ := #[invΣ; ledgerΣ; axannotΣ]` ↦ `mprGF`, an explicit slot table over
   `BundledGFunctors.default` (as `AxTokLedgerWp.mpGF`): wsat + credits at slots 0–3, the
   ledger at 4, the annotation cameras (saved prop, ghost map `Geid → GName`, `AxannotSetR`) at
   5–7; instances `AxTokLedgerMp.mprGF*`.
7. `ledgerVerified`'s `post` is `fun _ _ => True` and its `Hwp` binders are instance binders
   (`AxTokLedgerWp` deviation 5).
8. PROOF ROUTE (not statements): `vm_compute` ↦ `decide +kernel`; `mprPlainWritesOC` and
   `mprPlainNoRel` follow `AxTokLedger.mpPlainWritesOC`/`mpPlainNoRel` (one kernel-decided fact
   over the program's labels); the WPd shells unfold `AxWpD.wpdMUnfoldStep` (as `AxWpdLift`);
   `wpdSkipStepOfLater'` is proved directly from `wpSkipStep`'s definition.

**Rocq → Lean name map.**  §1 `xpa_m` `xpaM`, `ypa_m` `ypaM`, `xpa_m_ram` `xpaMRam`, `ypa_m_ram`
`ypaMRam`, `xa` `xa`, `ya` `ya`, `xa_ne_ya` `xaNeYa`, `mpr_row0/1` `mprRow0/1`, `mpr`
`AxTokLedgerMp.mpr`, `mpr_cat` `AxTokLedgerMp.mprCat`, `mpr_wf` `mprWf`, `mpr_gmo` `mprGmo`,
`mpr_grow0/1` `mprGrow0/1`, `mpr_plain_row0` `mprPlainRow0`, `mpr_plain` `mprPlain`,
`mpr_plain_cat` `mprPlainCat`, `mpr_plain_no_rel` `mprPlainNoRel`, `mpr_plain_viol`
`mprPlainViol`, `mpr_plain_not_ledger_verified` `mprPlainNotLedgerVerified`.  §2 `akAq` `akAq`,
`h0_m0/1/2` `h0M0/1/2`, `h1_m0/1` `h1M0/1`, `hp` `hp`, `h_aread` `hAread`, `h_astep_write`
`hAstepWrite`, `h_astep_fence` `hAstepFence`, `h0_run` `h0Run`, `h1_run` `h1Run`.  §3 `OC_mpr`
`ocMpr`, `OC_mpr_in` `ocMprIn`, `NoDup_xy` `noDupXy`, `L_mpr0` `lMpr0`, `mpr_phase` `mprPhase`,
`base_mpr` `baseMpr`, `mpr_phase_take` `mprPhaseTake`, `base_mpr_take` `baseMprTake`, `mpr_rel`
`mprRel`, `mpr_rf_y` `mprRfY`, `mpr_acq` `mprAcq`, `mpr_plain_writes_OC` `mprPlainWritesOC`,
`gmo_prefix_gmo_lt'` `gmoPrefixGmoLt'`, `Tf` `Tf`.  §4 `Imp` `imp`, `Imp_ext` `impExt`,
`mpr_j0..3` `mprJ0..3`, `wp_ev_step_closed` `wpEvStepClosed`, `wpd_skip_step_of_later'`
`AxTokLedgerMp.wpdSkipStepOfLater'`, `astep_prog_row_end_shape'`
`AxTokLedgerMp.astepProgRowEndShape'`, `lb_admin_wl_wdata_none'`
`AxTokLedgerMp.lbAdminWlWdataNone'`, `wpd_row_end_triv'` `wpdRowEndTriv'`, `awire_rs_only'`
`awireRsOnly'`, `wpd_pos_shell'` `wpdPosShell'`, `astep_write_inv` `astepWriteInv`,
`astep_fence_inv` `astepFenceInv`, `read_det` `readDet`, `read_astep_vacuous`
`readAstepVacuous`, `wpd_read_pos` `wpdReadPos`, `wpd_h1_1/0` `wpdH1_1/0`, `wpd_h0_2/1/0`
`wpdH0_2/1/0`.  §5 `init_mpr` `initMpr`, `cpu0` `cpu0`, `mpr_s0` `mprS0`, `mpr_sN` `mprSN`,
`mpr_n` `mprN`, `mprΣ` `mprGF`, `mpr_ledger_verified` `mprLedgerVerified`, `mpr_no_violation`
`mprNoViolation`.  Lean-only: `AxTokLedgerMp.bigSepLPair`, `AxTokLedgerMp.mprIdx`,
`AxTokLedgerMp.TW`, `AxTokLedgerMp.LJ`, `AxTokLedgerMp.gconstEq`, `AxTokLedgerMp.localTrue`,
`AxTokLedgerMp.baseMprEmpty`, `AxTokLedgerMp.twUnfold`, `AxTokLedgerMp.initMpr0/1`,
`AxTokLedgerMp.mprS0At0/1`, `AxTokLedgerMp.mprGF*` instances.

**Not ported:** the §6 `Print Assumptions` audits (the lint's axiom check covers them).
-/
import Weak.AxTokLedgerWp
import Weak.AxLock3Prog
import Weak.ExecLib

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std Iris.Std.PartialMap MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D

/-! # 1. THE RAM-ADDRESS MESSAGE-PASSING GRAPH `mpr` AND ITS PLAIN TWIN -/

def xpaM : PAddr := zPa 0x80001000
def ypaM : PAddr := zPa 0x80002000

theorem xpaMRam : devAddr xpaM = false := by decide +kernel
theorem ypaMRam : devAddr ypaM = false := by decide +kernel

def xa : Int := paZ xpaM
def ya : Int := paZ ypaM

theorem xaNeYa : xa ≠ ya := by decide +kernel

def mprRow0 : List Lbl :=
  [.LStore false xa [b1] .WCplain,
   .LFence true true false true,
   .LStore false ya [b1] .WCrel]

def mprRow1 : List Lbl :=
  [.LLoad true ya [2] [b1],
   .LLoad false xa [1] [b1]]

/-- `AxViol.mp` with x = 0x80001000, y = 0x80002000 (RAM) instead of 0 / 1. -/
def AxTokLedgerMp.mpr : Gdexec :=
  ⟨⟨vimg, [mprRow0, mprRow1], [(0, 0), (0, 2), (1, 0), (1, 1)]⟩, []⟩

theorem AxTokLedgerMp.mprCat : rvwmoCatConsistent AxTokLedgerMp.mpr :=
  catConsistentBSound _ (by decide +kernel)

theorem mprWf : gwf AxTokLedgerMp.mpr.gdG := AxTokLedgerMp.mprCat.1

theorem mprGmo : AxTokLedgerMp.mpr.gdG.gxGmo = [(0, 0), (0, 2), (1, 0), (1, 1)] := rfl
theorem mprGrow0 : AxOpsem.grow AxTokLedgerMp.mpr 0 = mprRow0 := rfl
theorem mprGrow1 : AxOpsem.grow AxTokLedgerMp.mpr 1 = mprRow1 := rfl

/-- The plain twin: the release-class sd y replaced by a plain sd. -/
def mprPlainRow0 : List Lbl :=
  [.LStore false xa [b1] .WCplain,
   .LFence true true false true,
   .LStore false ya [b1] .WCplain]

def mprPlain : Gdexec :=
  ⟨⟨vimg, [mprPlainRow0, mprRow1], [(0, 0), (0, 2), (1, 0), (1, 1)]⟩, []⟩

theorem mprPlainCat : rvwmoCatConsistent mprPlain :=
  catConsistentBSound _ (by decide +kernel)

theorem mprPlainNoRel (h : Geid) : ¬ glblIs mprPlain.gdG h lbRelw := by
  intro hr
  obtain ⟨p, hp, l, hl, hb⟩ := axViolGlblIsProg _ _ _ hr
  have hall : ∀ p ∈ mprPlain.gdG.gxProg, ∀ l ∈ p, lbRelw l = false := by decide +kernel
  rw [hall p hp l hl] at hb
  cases hb

theorem mprPlainViol : gdviolationHart 2 mprPlain := by
  refine ⟨(0, 0), (1, 1), xa, b1, by decide +kernel,
    (gwbBSpec _ _ _ _).1 (by decide +kernel), ⟨_, rfl, by decide +kernel⟩, trivial,
    ⟨0, rfl, by omega⟩, ⟨1, rfl, by omega⟩, by decide, ?_⟩
  refine .inr ⟨1, b1, (grbBSpec _ _ _ _ _).1 (by decide +kernel),
    by decide +kernel, ?_, ?_⟩
  · rintro ⟨h, _, hr, _⟩
    exact mprPlainNoRel h hr
  · rintro ws _ ⟨h, _, hr, _⟩
    exact mprPlainNoRel h hr

/-- THE NEGATIVE TWIN, re-proved for the RAM-address graph. -/
theorem mprPlainNotLedgerVerified : ¬ ledgerVerified 2 mprPlain := fun Hver =>
  adequacyViolFreeLedger 2 mprPlain mprPlainCat Hver mprPlainViol

/-! # 2. HAND-BUILT `Pexv6` PROGRAMS (no Sail decode, `AxLock3Prog` style) -/

/-- The acquire load's access kind: plain variety, acquire strength. -/
def akAq : AK := .AK_explicit ⟨.AV_plain, .AS_rel_or_acq⟩

abbrev h0M2 : SailM Unit :=
  .impure (.ok (.memWrite 1 64 (l3pWreq l3pAkP ypaM b1))) (fun _ => .pure ())
abbrev h0M1 : SailM Unit :=
  .impure (.ok (.barrier .Barrier_RISCV_rw_w)) (fun _ => h0M2)
abbrev h0M0 : SailM Unit :=
  .impure (.ok (.memWrite 1 64 (l3pWreq l3pAkP xpaM b1))) (fun _ => h0M1)
abbrev h1M1 : SailM Unit :=
  .impure (.ok (.memRead 1 64 (l3pRreq l3pAkP xpaM))) (fun _ => .pure ())
abbrev h1M0 : SailM Unit :=
  .impure (.ok (.memRead 1 64 (l3pRreq akAq ypaM))) (fun _ => h1M1)

abbrev hp (cpu : CPU) (m : SailM Unit) (rs : RegFile) : Pexv6 := .PHart cpu m rs none ibNone

/-! ## 2.1 Step facts -/

section steps
variable (cpu : CPU)

theorem hAread (row : List Lbl) (k : Nat) (aq : Bool) (ak : AK) (pa : PAddr)
    (Hdev : devAddr pa = false) (Hcoh : (classify ak).akIfetch = false)
    (Hsync : (classify ak).akSync = aq) (Hlat : (classify ak).akLatest = false)
    (ts : List Nat) (b : BitVec 8) (m' : SailM Unit) (rs : RegFile) :
    row[k]? = some (.LLoad aq (paZ pa) ts [b]) →
    areadStep row ⟨hp cpu (.impure (.ok (.memRead 1 64 (l3pRreq ak pa))) (fun _ => m')) rs, k⟩
      (.IRead aq (paZ pa) 1) (fun _ => ⟨hp cpu m' rs, k + 1⟩) := by
  intro hrow
  refine ⟨_, hrow, rfl, rfl, ?_⟩
  intro vs hvs
  refine ⟨rdLabel false (classify ak).akLatest (classify ak).akSync (paZ pa) (tagVals vs)
      (rdAsrc (classify ak).akLatest ibNone), OpaxWit.wtD0, OpaxWit.wtD0, ?_, ?_,
    l3pReadStep cpu ak pa Hdev Hcoh _ rs ibNone OpaxWit.wtD0 vs hvs, rfl⟩
  · rw [Hlat, Hsync]
    simp only [rdLabel, wlRd, aidentRd, tagValsLength, Bool.false_eq_true, ↓reduceIte]
    rw [hvs]
    rfl
  · rw [rdLabelRvals _ _ _ _ _ _ rfl, tagValsSnd]

theorem hAstepWrite (row : List Lbl) (k : Nat) (pa : PAddr) (Hdev : devAddr pa = false)
    (b : BitVec 8) (cls : WmClass) (m' : SailM Unit) (rs : RegFile) :
    row[k]? = some (.LStore false (paZ pa) [b] cls) →
    AxOpsem.astepProg row
      ⟨hp cpu (.impure (.ok (.memWrite 1 64 (l3pWreq l3pAkP pa b))) (fun _ => m')) rs, k⟩
      (.LStore false (paZ pa) (WeakInterpProj.wbytes 1 b) [] [])
      ⟨hp cpu m' rs, k + 1⟩ := by
  intro hrow
  refine .AStepWrite _ k OpaxWit.wtD0 _ _ _ OpaxWit.wtD0 hrow rfl rfl ?_ ?_
  · simp only [wlWdata, lblData, l3pWbytes1]
  · exact l3pWritePlainStep cpu pa Hdev b (fun _ => m') rs ibNone OpaxWit.wtD0

theorem hAstepFence (row : List Lbl) (k : Nat) (m' : SailM Unit) (rs : RegFile) :
    row[k]? = some (.LFence true true false true) →
    AxOpsem.astepProg row
      ⟨hp cpu (.impure (.ok (.barrier .Barrier_RISCV_rw_w)) (fun _ => m')) rs, k⟩
      (.LFence true true false true) ⟨hp cpu m' rs, k + 1⟩ := by
  intro hrow
  exact .AStepFence _ k OpaxWit.wtD0 _ _ _ OpaxWit.wtD0 hrow rfl rfl
    (l3pFenceStep cpu (fun _ => m') rs ibNone OpaxWit.wtD0)

end steps

/-! ## 2.2 THE RUNS (graph-pinned, `astepAnyNfGv`) -/

section runs
variable (cpu : CPU) (rs : RegFile)

theorem h0Run :
    nsteps (astepAnyNfGv AxTokLedgerMp.mpr 0) 3 ⟨hp cpu h0M0 rs, 0⟩
      ⟨hp cpu (.pure ()) rs, 3⟩ := by
  refine nsteps_l (astepAnyNfGv.ANFGVProg _ _
    ⟨_, hAstepWrite cpu (AxOpsem.grow AxTokLedgerMp.mpr 0) 0 xpaM xpaMRam b1 .WCplain h0M1 rs
      rfl, trivial⟩) ?_
  refine nsteps_l (astepAnyNfGv.ANFGVProg _ _
    ⟨_, hAstepFence cpu (AxOpsem.grow AxTokLedgerMp.mpr 0) 1 h0M2 rs rfl, trivial⟩) ?_
  refine nsteps_l (astepAnyNfGv.ANFGVProg _ _
    ⟨_, hAstepWrite cpu (AxOpsem.grow AxTokLedgerMp.mpr 0) 2 ypaM ypaMRam b1 .WCrel (.pure ())
      rs rfl, trivial⟩) ?_
  exact nsteps_O _

theorem h1Run :
    nsteps (astepAnyNfGv AxTokLedgerMp.mpr 1) 2 ⟨hp cpu h1M0 rs, 0⟩
      ⟨hp cpu (.pure ()) rs, 2⟩ := by
  refine nsteps_l (astepAnyNfGv.ANFGVRead _ _ _ [b1]
    (hAread cpu (AxOpsem.grow AxTokLedgerMp.mpr 1) 0 true akAq ypaM ypaMRam rfl rfl rfl [2] b1
      h1M1 rs rfl) rfl rfl) ?_
  refine nsteps_l (astepAnyNfGv.ANFGVRead _ _ _ [b1]
    (hAread cpu (AxOpsem.grow AxTokLedgerMp.mpr 1) 1 false l3pAkP xpaM xpaMRam rfl rfl rfl [1] b1
      (.pure ()) rs rfl) rfl rfl) ?_
  exact nsteps_O _

end runs

/-! # 3. THE PHASE-2 PROTOCOL: a gmo-indexed base mailbox beside the ledger -/

def ocMpr (a : Int) : Prop := a = xa ∨ a = ya

theorem ocMprIn (a : Int) : ocMpr a → a ∈ ([xa, ya] : List Int) := by
  rintro (rfl | rfl) <;> simp

theorem noDupXy : ([xa, ya] : List Int).Nodup := by decide +kernel

def lMpr0 : Ledger := insert ({[xa := .held 0]} : Ledger) ya (.held 0)

/-- Which phase the validated set is in (only ever evaluated on gmo prefixes). -/
def mprPhase (s : GSet Geid) : Nat :=
  if decide (((1, 1) : Geid) ∈ s) then 0
  else if decide (((1, 0) : Geid) ∈ s) then 3
  else if decide (((0, 2) : Geid) ∈ s) then 2
  else if decide (((0, 0) : Geid) ∈ s) then 1
  else 0

/-- The mailbox: after hart 0's plain sd x it holds hart 0's two tokens; after the
release-class sd y the two PENDING tokens (keyed by the release); after the ld.aq hart 1's two
tokens; afterwards nothing. -/
def baseMpr {GF : BundledGFunctors} [LedgerG GF] (γ : GName) (_GD : Gdexec) (_σ : Unit)
    (s : GSet Geid) : IProp GF :=
  match mprPhase s with
  | 1 => iprop(tokAt γ xa 0 ∗ tokAt γ ya 0)
  | 2 => iprop(tokPending γ xa (0, 2) ∗ tokPending γ ya (0, 2))
  | 3 => iprop(tokAt γ xa 1 ∗ tokAt γ ya 1)
  | _ => iprop(True)

theorem mprPhaseTake (k : Nat) :
    mprPhase (LawfulSet.ofList (AxTokLedgerMp.mpr.gdG.gxGmo.take k)) =
      match k with
      | 1 => 1
      | 2 => 2
      | 3 => 3
      | _ => 0 := by
  rcases k with _ | _ | _ | _ | k
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · rw [List.take_of_length_le (by simp [mprGmo])]
    show _ = 0
    decide +kernel

theorem baseMprTake {GF : BundledGFunctors} [LedgerG GF] (γ : GName) (GD : Gdexec) (σ : Unit)
    (k : Nat) :
    baseMpr (GF := GF) γ GD σ (LawfulSet.ofList (AxTokLedgerMp.mpr.gdG.gxGmo.take k)) =
      match k with
      | 1 => iprop(tokAt γ xa 0 ∗ tokAt γ ya 0)
      | 2 => iprop(tokPending γ xa (0, 2) ∗ tokPending γ ya (0, 2))
      | 3 => iprop(tokAt γ xa 1 ∗ tokAt γ ya 1)
      | _ => iprop(True) := by
  unfold baseMpr
  rw [mprPhaseTake]
  rcases k with _ | _ | _ | _ | k <;> rfl

theorem mprRel : glblIs AxTokLedgerMp.mpr.gdG (0, 2) lbRelw := ⟨_, rfl, by decide +kernel⟩

theorem mprRfY : grfAt AxTokLedgerMp.mpr.gdG ya (0, 2) (1, 0) :=
  ⟨2, b1, (grbBSpec _ _ _ _ _).1 (by decide +kernel), by decide +kernel⟩

theorem mprAcq : acqFrom AxTokLedgerMp.mpr (0, 2) (1, 0) := .inl ⟨ya, mprRfY⟩

theorem mprPlainWritesOC :
    ∀ w a v, w ∈ AxTokLedgerMp.mpr.gdG.gxGmo → tidHart 2 (some w.1) →
      glblIs AxTokLedgerMp.mpr.gdG w lbPlain → gwritesByte AxTokLedgerMp.mpr.gdG w a v →
      ocMpr a := by
  intro w a v _ _ _ ⟨l, base, vs, j, hl, hwr, hj, ha⟩
  have hall : ∀ p ∈ AxTokLedgerMp.mpr.gdG.gxProg, ∀ l ∈ p,
      (match lbWr l with
       | some (base, vs) => decide (vs.length = 1 ∧ (base = xa ∨ base = ya))
       | none => true) = true := by decide +kernel
  obtain ⟨p, hp, hlp⟩ := AxTokLedger.gxLblMem _ _ _ hl
  have h := hall p hp l hlp
  rw [hwr] at h
  obtain ⟨hlen, hb⟩ := of_decide_eq_true h
  have hj0 : j = 0 := by
    have := (List.getElem?_eq_some_iff.1 hj).1
    omega
  subst hj0
  unfold accAddr at ha
  unfold ocMpr
  omega

/-- The full gmo-prefix handout is gmo-earlier. -/
theorem gmoPrefixGmoLt' (G : Gexec) (Hwf : gwf G) (e e' : Geid) :
    e' ∈ gmoPrefix G e → gmoLt G e' e := by
  intro He'
  by_cases He : e ∈ G.gxGmo
  · exact (gmoPrefixSpec G e e' Hwf He).1 He'
  · exfalso
    unfold gmoPrefix gpos at He'
    cases hf : listFind (fun e'' => decide (e'' = e)) G.gxGmo with
    | none =>
      rw [hf] at He'
      simp at He'
    | some q =>
      obtain ⟨i, x⟩ := q
      obtain ⟨hi, hx, _⟩ := list_find_Some.1 hf
      have : x = e := of_decide_eq_true hx
      subst this
      exact He (elem_of_list_lookup_2 hi)

/-- Rocq's text-region oracle (O2 Stage C: no longer an argument of anything; kept). -/
def Tf : Int → Prop := fun _ => False

/-- Lean-only: a two-element big separating conjunction. -/
theorem AxTokLedgerMp.bigSepLPair {GF : BundledGFunctors} {α : Type} (x y : α)
    (Φ : α → IProp GF) : ([∗list] a ∈ [x, y], Φ a) ⊣⊢ Φ x ∗ Φ y :=
  BigSepL.bigSepL_cons.trans (sep_congr .rfl BigSepL.bigSepL_singleton)

/-- Lean-only: a gmo lookup of `mpr` names the event's position. -/
theorem AxTokLedgerMp.mprIdx (n : Nat) (e : Geid) :
    AxTokLedgerMp.mpr.gdG.gxGmo[n]? = some e → n = gpos AxTokLedgerMp.mpr.gdG e :=
  fun h => (gposOfLookup _ n e mprWf.1 h).symm

/-! # 4. PER-HART WPds AT THE LEDGER-EXTENDED `axGA2` INSTANCE -/

section wpd
variable {hlc : HasLC} {GF : BundledGFunctors.{0,0,0}} [InvGS_gen hlc GF] [AxannotGS GF]
  [LedgerG GF]

/-- Rocq `Local Instance Imp` (a named reducible def; header deviation 5). -/
@[reducible] def imp (γ : GName) : AxirisG GF :=
  axGA2 AxTokLedgerMp.mpr (GName × GName) Unit (obStInterpL ocMpr 2 baseMpr) (γ, γ)

theorem impExt (γ : GName) :
    ∀ (GD : Gdexec) (σ : @AxirisG.obSt GF (imp γ)) (s : GSet Geid),
      @AxirisG.obStInterp GF (imp γ) GD σ s ⊣⊢
        baseMpr γ GD σ s ∗ AxTokLedgerWp.ledgerInv ocMpr 2 γ GD s :=
  fun _ _ _ => .rfl

/-- Lean-only (Rocq `Local Notation TW`). -/
abbrev AxTokLedgerMp.TW (γ : GName) (s : Athread) (i : Agent) : IProp GF :=
  @tierAWpd GF hlc _ _ mpPol AxTokLedgerMp.mpr (GName × GName) Unit (obStInterpL ocMpr 2 baseMpr)
    (γ, γ) s .MaybeStuck i (fun _ => iprop(⌜True⌝))

/-- Lean-only (Rocq `Local Notation LJ`). -/
abbrev AxTokLedgerMp.LJ (γ : GName) (e : Geid) (fin : Mea GF) (R : IProp GF) : IProp GF :=
  @ledgerJoint hlc GF _ (imp γ) _ ocMpr 2 γ (baseMpr γ) AxTokLedgerMp.mpr e fin R

/-- Lean-only: the graph pin of the instance. -/
theorem AxTokLedgerMp.gconstEq (γ : GName) (GD : Gdexec) :
    @AxirisG.gconstInterp GF (imp γ) GD ⊢ ⌜GD = AxTokLedgerMp.mpr⌝ := .rfl

/-- Lean-only: the local state of the instance is trivial. -/
theorem AxTokLedgerMp.localTrue (γ : GName) (GD : Gdexec) (i : Agent) (k : Nat) (ls : Unit) :
    ⊢ @AxirisG.localInterp GF (imp γ) GD i k ls := by
  show ⊢ iprop(True)
  itrivial

/-- Lean-only: one unfolding of `TW` at a hart state (harts never terminate). -/
theorem AxTokLedgerMp.twUnfold (γ : GName) (s : Athread) (i : Agent) :
    AxTokLedgerMp.TW (hlc := hlc) (GF := GF) γ s i ⊣⊢
      iprop(@progressObl GF (imp γ) .MaybeStuck i s ∧
        @wpdMPreStepDef hlc GF _ (imp γ) mpPol rvwmoCatConsistent i
          (fun s' Φ' => @tierAWpd GF hlc _ _ mpPol AxTokLedgerMp.mpr (GName × GName) Unit
            (obStInterpL ocMpr 2 baseMpr) (γ, γ) s' .MaybeStuck i Φ') s
          (fun _ => iprop(⌜True⌝))) :=
  @AxWpD.wpdMUnfoldStep hlc GF _ (imp γ) mpPol rvwmoCatConsistent .MaybeStuck i s _

/-! ## 4.1 The four phase-2 obligations -/

theorem mprJ0 (γ : GName) :
    iprop(tokAt (GF := GF) γ xa 0 ∗ tokAt γ ya 0) ⊢
      AxTokLedgerMp.LJ (hlc := hlc) γ (0, 0) ∅
        iprop(True ∗ ⌜graphData AxTokLedgerMp.mpr (0, 0) = some [b1]⌝) := by
  iintro ⟨H0, H1⟩
  unfold AxTokLedgerMp.LJ ledgerJoint
  iintro %σ %n %L %Hn _ Ha _
  have Hn0 : n = 0 := (AxTokLedgerMp.mprIdx n _ Hn).trans (by decide +kernel)
  subst Hn0
  ihave Hh := (AxTokLedgerMp.bigSepLPair xa ya (fun a => tokAt γ a ((0, 0) : Geid).1)).2
    $$ [H0 H1]
  · isplitl [H0]
    · iexact H0
    · iexact H1
  ihave Hr := AxTokLedgerWp.bigSepLNil (fun a => tokAt γ a ((0, 0) : Geid).1)
  ihave Hq := AxTokLedgerWp.bigSepLNil (fun a => tokPending γ a ((fun _ => ((0, 2) : Geid)) a))
  imod ledgerActGen ocMpr 2 AxTokLedgerMp.mpr γ L (0, 0) [xa, ya] [] [] (fun _ => (0, 2))
    List.nodup_nil List.nodup_nil (fun _ h => nomatch h) (fun _ h => nomatch h)
    (fun a Ha _ _ => .inl (ocMprIn a Ha)) $$ Ha Hh Hr Hq with ⟨%L', Ha, %Hst, Hh, -, -⟩
  iapply fupd_mask_intro LawfulSet.empty_subset
  iintro Hclose
  inext
  imod Hclose
  imodintro
  iexists σ, L'
  simp only [baseMprTake]
  isplitl [Hh]
  · icases (AxTokLedgerMp.bigSepLPair _ _ _).1 $$ Hh with ⟨H0, H1⟩
    isplitl [H0]
    · iexact H0
    · iexact H1
  isplitl [Ha]
  · iexact Ha
  isplitr
  · ipureintro
    exact Hst
  isplitr
  · itrivial
  · ipureintro
    decide +kernel

theorem mprJ1 (γ : GName) :
    ⊢ AxTokLedgerMp.LJ (hlc := hlc) (GF := GF) γ (0, 2) ∅
        iprop(True ∗ ⌜graphData AxTokLedgerMp.mpr (0, 2) = some [b1]⌝) := by
  unfold AxTokLedgerMp.LJ ledgerJoint
  iintro %σ %n %L %Hn
  have Hn1 : n = 1 := (AxTokLedgerMp.mprIdx n _ Hn).trans (by decide +kernel)
  subst Hn1
  simp only [baseMprTake]
  iintro ⟨H0, H1⟩ Ha _
  ihave Hr := (AxTokLedgerMp.bigSepLPair xa ya (fun a => tokAt γ a ((0, 2) : Geid).1)).2
    $$ [H0 H1]
  · isplitl [H0]
    · iexact H0
    · iexact H1
  ihave Hh := AxTokLedgerWp.bigSepLNil (fun a => tokAt γ a ((0, 2) : Geid).1)
  ihave Hq := AxTokLedgerWp.bigSepLNil (fun a => tokPending γ a ((fun _ => ((0, 2) : Geid)) a))
  imod ledgerActGen ocMpr 2 AxTokLedgerMp.mpr γ L (0, 2) [] [xa, ya] [] (fun _ => (0, 2))
    noDupXy List.nodup_nil (fun _ _ => mprRel) (fun _ h => nomatch h)
    (fun a Ha _ _ => .inr (.inl (ocMprIn a Ha))) $$ Ha Hh Hr Hq with ⟨%L', Ha, %Hst, -, Hr, -⟩
  iapply fupd_mask_intro LawfulSet.empty_subset
  iintro Hclose
  inext
  imod Hclose
  imodintro
  iexists σ, L'
  isplitl [Hr]
  · icases (AxTokLedgerMp.bigSepLPair _ _ _).1 $$ Hr with ⟨P0, P1⟩
    isplitl [P0]
    · iexact P0
    · iexact P1
  isplitl [Ha]
  · iexact Ha
  isplitr
  · ipureintro
    exact Hst
  isplitr
  · itrivial
  · ipureintro
    decide +kernel

theorem mprJ2 (γ : GName) (v : List (BitVec 8)) :
    graphValue AxTokLedgerMp.mpr (1, 0) = some v →
    ⊢ AxTokLedgerMp.LJ (hlc := hlc) (GF := GF) γ (1, 0) ∅
        iprop(True ∗ ⌜graphValue AxTokLedgerMp.mpr (1, 0) = some v⌝) := by
  intro Hgv
  unfold AxTokLedgerMp.LJ ledgerJoint
  iintro %σ %n %L %Hn
  have Hn2 : n = 2 := (AxTokLedgerMp.mprIdx n _ Hn).trans (by decide +kernel)
  subst Hn2
  simp only [baseMprTake]
  iintro ⟨P0, P1⟩ Ha _
  ihave Hq := (AxTokLedgerMp.bigSepLPair xa ya
    (fun a => tokPending γ a ((fun _ => ((0, 2) : Geid)) a))).2 $$ [P0 P1]
  · isplitl [P0]
    · iexact P0
    · iexact P1
  ihave Hh := AxTokLedgerWp.bigSepLNil (fun a => tokAt γ a ((1, 0) : Geid).1)
  ihave Hr := AxTokLedgerWp.bigSepLNil (fun a => tokAt γ a ((1, 0) : Geid).1)
  imod ledgerActGen ocMpr 2 AxTokLedgerMp.mpr γ L (1, 0) [] [] [xa, ya] (fun _ => (0, 2))
    List.nodup_nil noDupXy (fun _ h => nomatch h) (fun _ _ => mprAcq)
    (fun a Ha _ _ => .inr (.inr (ocMprIn a Ha))) $$ Ha Hh Hr Hq with ⟨%L', Ha, %Hst, -, -, Hq⟩
  iapply fupd_mask_intro LawfulSet.empty_subset
  iintro Hclose
  inext
  imod Hclose
  imodintro
  iexists σ, L'
  isplitl [Hq]
  · icases (AxTokLedgerMp.bigSepLPair _ _ _).1 $$ Hq with ⟨H0, H1⟩
    isplitl [H0]
    · iexact H0
    · iexact H1
  isplitl [Ha]
  · iexact Ha
  isplitr
  · ipureintro
    exact Hst
  isplitr
  · itrivial
  · ipureintro
    exact Hgv

theorem mprJ3 (γ : GName) (v : List (BitVec 8)) :
    graphValue AxTokLedgerMp.mpr (1, 1) = some v →
    ⊢ AxTokLedgerMp.LJ (hlc := hlc) (GF := GF) γ (1, 1) ∅
        iprop(True ∗ ⌜graphValue AxTokLedgerMp.mpr (1, 1) = some v⌝) := by
  intro Hgv
  unfold AxTokLedgerMp.LJ ledgerJoint
  iintro %σ %n %L %Hn
  have Hn3 : n = 3 := (AxTokLedgerMp.mprIdx n _ Hn).trans (by decide +kernel)
  subst Hn3
  simp only [baseMprTake]
  iintro ⟨H0, H1⟩ Ha _
  ihave Hh := (AxTokLedgerMp.bigSepLPair xa ya (fun a => tokAt γ a ((1, 1) : Geid).1)).2
    $$ [H0 H1]
  · isplitl [H0]
    · iexact H0
    · iexact H1
  ihave Hr := AxTokLedgerWp.bigSepLNil (fun a => tokAt γ a ((1, 1) : Geid).1)
  ihave Hq := AxTokLedgerWp.bigSepLNil (fun a => tokPending γ a ((fun _ => ((0, 2) : Geid)) a))
  imod ledgerActGen ocMpr 2 AxTokLedgerMp.mpr γ L (1, 1) [xa, ya] [] [] (fun _ => (0, 2))
    List.nodup_nil List.nodup_nil (fun _ h => nomatch h) (fun _ h => nomatch h)
    (fun a Ha _ _ => .inl (ocMprIn a Ha)) $$ Ha Hh Hr Hq with ⟨%L', Ha, %Hst, -, -, -⟩
  iapply fupd_mask_intro LawfulSet.empty_subset
  iintro Hclose
  inext
  imod Hclose
  imodintro
  iexists σ, L'
  isplitr
  · itrivial
  isplitl [Ha]
  · iexact Ha
  isplitr
  · ipureintro
    exact Hst
  isplitr
  · itrivial
  · ipureintro
    exact Hgv

/-! ## 4.2 The event-step rule used at every memory event: no local flow, a `True` deposit,
the joint obligation -/

theorem wpEvStepClosed (γ : GName) (i k : Nat) (val : Unit → Prop) (k' : Unit → Nat)
    (Ψ : Unit → IProp GF) (He : (i, k) ∈ AxTokLedgerMp.mpr.gdG.gxGmo) :
    ⊢ AxTokLedgerMp.LJ (hlc := hlc) γ (i, k) ∅ iprop(True ∗ ⌜val ()⌝) -∗ Ψ () -∗
      @wpEvStep hlc GF _ (imp γ) mpPol Unit AxTokLedgerMp.mpr i k (fun _ => True) val k' Ψ := by
  iintro Hj HΨ
  iapply (@wpEvStepLedgerJoint hlc GF _ (imp γ) _ mpPol ocMpr 2 γ (baseMpr γ) (impExt γ) Unit
    AxTokLedgerMp.mpr i k (fun _ => True) val k' Ψ () trivial mprWf He (fun _ h => h))
    $$ [Hj] HΨ
  iintro %na ⟨Hpg, Hna⟩
  ihave Hnin := naAtProgressNotElemOf AxTokLedgerMp.mpr i k na $$ Hpg
  icases Hnin with %Hnin
  imod annotAlloc na (i, k) iprop(True) Hnin $$ Hna with ⟨Hna, -⟩
  imodintro
  iexists iprop(True), (∅ : Mea GF), (∅ : Mea GF), ()
  isplitr
  · iapply (@AxTokLedgerWp.naSplittingWfEmpty GF (imp γ) _ mpPol)
  isplitl [Hj]
  · iexact Hj
  rw [@AxTokLedgerWp.annotInsertEq GF (imp γ) _ mpPol na (i, k) iprop(True)]
  isplitl [Hna]
  · iexact Hna
  · iapply AxTokLedgerMp.localTrue

/-! ## 4.3 Generic WPd plumbing -/

theorem AxTokLedgerMp.wpdSkipStepOfLater' (γ : GName) (i : Agent) (k' : Nat) (Ψ : IProp GF) :
    ⊢ ▷ Ψ -∗ @wpSkipStep GF (imp γ) AxTokLedgerMp.mpr i k' Ψ := by
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
  · iapply AxTokLedgerMp.localTrue
  · iexact HΨ

theorem AxTokLedgerMp.astepProgRowEndShape' (row : List Lbl) (s : Athread) (l : Wlabel)
    (s' : Athread) (Hnone : row[s.atK]? = none) :
    AxOpsem.astepProg row s l s' →
    lbAdmin true l ∧ s'.atK = s.atK ∧ ∃ d d', pstepProg s.atP d l s'.atP d' := by
  intro h
  cases h with
  | AStepAdmin p k d l p' d' hadm hst => exact ⟨hadm, rfl, d, d', hst⟩
  | AStepWrite p k d l lb p' d' hlk _ _ _ _ =>
    simp only at Hnone
    rw [hlk] at Hnone
    cases Hnone
  | AStepFence p k d l lb p' d' hlk _ _ _ =>
    simp only at Hnone
    rw [hlk] at Hnone
    cases Hnone

theorem AxTokLedgerMp.lbAdminWlWdataNone' (l : Wlabel) : lbAdmin true l → wlWdata l = none := by
  cases l <;> simp [lbAdmin, wlWdata]

theorem wpdRowEndTriv' (γ : GName) (i : Agent) (k0 : Nat)
    (Hend : (AxOpsem.grow AxTokLedgerMp.mpr i).length ≤ k0) (p : Pexv6) :
    ⊢ AxTokLedgerMp.TW (hlc := hlc) (GF := GF) γ ⟨p, k0⟩ i := by
  have H : ⊢ ∀ p : Pexv6, AxTokLedgerMp.TW (hlc := hlc) (GF := GF) γ ⟨p, k0⟩ i := by
    iloeb as IH
    iintro %p
    iapply (AxTokLedgerMp.twUnfold (hlc := hlc) γ _ i).2
    isplit
    · simp only [progressObl]
      itrivial
    unfold wpdMPreStepDef
    iintro %GD %ls ⟨%Hc, #Hg, Hloc⟩
    ihave Hok := AxTokLedgerMp.gconstEq γ GD $$ Hg
    icases Hok with %HGD
    subst HGD
    isplit
    · iintro %id %K %Hst
      obtain ⟨lb, Hlk, -⟩ := Hst
      simp only at Hlk
      rw [List.getElem?_eq_none Hend] at Hlk
      cases Hlk
    isplit
    · iintro %l %s' %Hst %_
      obtain ⟨Hadm, Hk', -⟩ := AxTokLedgerMp.astepProgRowEndShape' _ _ l s'
        (List.getElem?_eq_none Hend) Hst
      simp only [AxTokLedgerMp.lbAdminWlWdataNone' l Hadm]
      obtain ⟨p', k1⟩ := s'
      simp only at Hk'
      subst Hk'
      iapply AxTokLedgerMp.wpdSkipStepOfLater'
      inext
      iapply IH $$ %p'
    isplit
    · iintro %s' %Hw
      obtain ⟨p', k1⟩ := s'
      obtain ⟨Hk, -⟩ := Hw
      simp only at Hk
      subst Hk
      iapply AxTokLedgerMp.wpdSkipStepOfLater'
      inext
      iapply IH $$ %p'
    · iintro %_
      iapply (@postLiftingTrue GF (imp γ) mpPol (fun _ => iprop(⌜True⌝)) i _
        (by iintro _; ipureintro; trivial))
  istart
  iapply H $$ %p

theorem awireRsOnly' (cpu : CPU) (m : SailM Unit) (rs : RegFile)
    (fn : Option (Bool × Bool × Bool × Bool)) (ib : Ibch) (k : Nat) (s' : Athread) :
    awire ⟨.PHart cpu m rs fn ib, k⟩ s' → ∃ rs', s' = ⟨.PHart cpu m rs' fn ib, k⟩ := by
  rintro ⟨Hk, d, d', Hp⟩
  obtain ⟨p', k'⟩ := s'
  simp only at Hk
  subst Hk
  cases p' with
  | PDisk _ => exact Hp.elim
  | PHart cpu' m' rs' fn' ib' =>
    obtain ⟨rfl, ors, oib, obar, _, hib, mm, b, kk, _, _, hm, hfn, _, hoib, _, _⟩ := Hp
    subst hm hfn hoib
    simp only [Option.getD_none] at hib
    subst hib
    exact ⟨rs', rfl⟩

/-- The shell for a non-read position (write or fence). -/
theorem wpdPosShell' (γ : GName) (cpu : CPU) (i : Agent) (P : IProp GF) (k : Nat)
    (m : SailM Unit)
    (Hrowk_nonread : ∀ lb, (AxOpsem.grow AxTokLedgerMp.mpr i)[k]? = some lb →
      aidentRd (aident lb) = none)
    (Hb : ∀ (rs : RegFile) (l : Wlabel) (s' : Athread),
      AxOpsem.astepProg (AxOpsem.grow AxTokLedgerMp.mpr i) ⟨hp cpu m rs, k⟩ l s' →
      ⊢ P -∗ match wlWdata l with
        | some data =>
            @wpEvStep hlc GF _ (imp γ) mpPol Unit AxTokLedgerMp.mpr i k (fun _ => True)
              (fun _ => graphData AxTokLedgerMp.mpr (i, k) = some data) (fun _ => s'.atK)
              (fun _ => AxTokLedgerMp.TW (hlc := hlc) γ s' i)
        | none =>
            @wpSkipStep GF (imp γ) AxTokLedgerMp.mpr i s'.atK
              (AxTokLedgerMp.TW (hlc := hlc) γ s' i)) :
    ⊢ P -∗ ∀ rs : RegFile, AxTokLedgerMp.TW (hlc := hlc) γ ⟨hp cpu m rs, k⟩ i := by
  have H : ⊢ ∀ rs : RegFile, P -∗ AxTokLedgerMp.TW (hlc := hlc) γ ⟨hp cpu m rs, k⟩ i := by
    iloeb as IH
    iintro %rs HP
    iapply (AxTokLedgerMp.twUnfold (hlc := hlc) γ _ i).2
    isplit
    · simp only [progressObl]
      itrivial
    unfold wpdMPreStepDef
    iintro %GD %ls ⟨%Hc, #Hg, Hloc⟩
    ihave Hok := AxTokLedgerMp.gconstEq γ GD $$ Hg
    icases Hok with %HGD
    subst HGD
    isplit
    · iintro %id %K %Hst
      obtain ⟨lb, Hlk, Hid, Hsome, -⟩ := Hst
      have Hnone : aidentRd id = none := Hid ▸ Hrowk_nonread lb Hlk
      rw [Hnone] at Hsome
      cases Hsome
    isplit
    · iintro %l %s' %Hst %_
      iapply (Hb rs l s' Hst) $$ HP
    isplit
    · iintro %s' %Hw
      obtain ⟨rs', rfl⟩ := awireRsOnly' cpu m rs none ibNone k s' Hw
      iapply AxTokLedgerMp.wpdSkipStepOfLater'
      inext
      iapply IH $$ %rs' HP
    · iintro %_
      iapply (@postLiftingTrue GF (imp γ) mpPol (fun _ => iprop(⌜True⌝)) i _
        (by iintro _; ipureintro; trivial))
  iintro HP %rs
  iapply H $$ %rs HP

theorem astepWriteInv (cpu : CPU) (i : Agent) (pa : PAddr) (Hdev : devAddr pa = false)
    (val : BitVec 8) (m' : SailM Unit) (rs : RegFile) (k : Nat) (s : Athread)
    (Heqp : s.atP = hp cpu (.impure (.ok (.memWrite 1 64 (l3pWreq l3pAkP pa val)))
      (fun _ => m')) rs)
    (Heqk : s.atK = k) (l : Wlabel) (s' : Athread) :
    AxOpsem.astepProg (AxOpsem.grow AxTokLedgerMp.mpr i) s l s' →
    l = .LStore false (paZ pa) (WeakInterpProj.wbytes 1 val)
          (depsAsrc (depsOfIb ibNone.ibBits)) (depsVsrc (depsOfIb ibNone.ibBits)) ∧
    s' = ⟨hp cpu m' rs, k + 1⟩ := by
  intro Hst
  cases Hst with
  | AStepAdmin p k0 d l0 p' d' Hadm Hps =>
    simp only at Heqp
    subst Heqp
    obtain ⟨rfl, -, -⟩ := l3pWritePlainDet cpu pa Hdev val _ rs ibNone d _ _ _ Hps
    simp [lbAdmin] at Hadm
  | AStepWrite p k0 d l0 lb p' d' _ _ _ _ Hps =>
    simp only at Heqp Heqk
    subst Heqp Heqk
    obtain ⟨rfl, rfl, -⟩ := l3pWritePlainDet cpu pa Hdev val _ rs ibNone d _ _ _ Hps
    exact ⟨rfl, rfl⟩
  | AStepFence p k0 d l0 lb p' d' _ Hfe _ Hps =>
    simp only at Heqp
    subst Heqp
    obtain ⟨rfl, -, -⟩ := l3pWritePlainDet cpu pa Hdev val _ rs ibNone d _ _ _ Hps
    simp [wlFence] at Hfe

theorem astepFenceInv (cpu : CPU) (i : Agent) (m' : SailM Unit) (rs : RegFile) (k : Nat)
    (s : Athread)
    (Heqp : s.atP = hp cpu (.impure (.ok (.barrier .Barrier_RISCV_rw_w)) (fun _ => m')) rs)
    (Heqk : s.atK = k) (l : Wlabel) (s' : Athread) :
    AxOpsem.astepProg (AxOpsem.grow AxTokLedgerMp.mpr i) s l s' →
    l = .LFence true true false true ∧ s' = ⟨hp cpu m' rs, k + 1⟩ := by
  intro Hst
  cases Hst with
  | AStepAdmin p k0 d l0 p' d' Hadm Hps =>
    simp only at Heqp
    subst Heqp
    obtain ⟨rfl, -, -⟩ := l3pFenceDet cpu _ rs ibNone d _ _ _ Hps
    simp [lbAdmin] at Hadm
  | AStepWrite p k0 d l0 lb p' d' _ Hwr _ _ Hps =>
    simp only at Heqp
    subst Heqp
    obtain ⟨rfl, -, -⟩ := l3pFenceDet cpu _ rs ibNone d _ _ _ Hps
    simp [wlWr] at Hwr
  | AStepFence p k0 d l0 lb p' d' _ _ _ Hps =>
    simp only at Heqp Heqk
    subst Heqp Heqk
    obtain ⟨rfl, rfl, -⟩ := l3pFenceDet cpu _ rs ibNone d _ _ _ Hps
    exact ⟨rfl, rfl⟩

theorem readDet (cpu : CPU) (ak : AK) (pa : PAddr) (Hdev : devAddr pa = false)
    (m' : SailM Unit) (rs : RegFile) (d : Efab) (l : Wlabel) (p' : Pexv6) (d' : Efab) :
    pstepProg (hp cpu (.impure (.ok (.memRead 1 64 (l3pRreq ak pa))) (fun _ => m')) rs) d l p' d' →
    p' = hp cpu m' rs := by
  intro Hst
  cases p' with
  | PDisk _ => exact Hst.elim
  | PHart cpu' m'' rs' fn' ib' =>
    obtain ⟨rfl, ors, oib, obar, hrs, hib, hn, _⟩ := Hst
    have hpa : devAddr (l3pRreq ak pa).pa = false := Hdev
    simp only [pstepNode, pnodeStep, hpa, Bool.false_eq_true, ↓reduceIte] at hn
    rcases hn with ⟨_, _, _, _, _, _, rfl, rfl, rfl, _, rfl, _⟩ |
      ⟨_, ⟨_, _, _, _, _, _, rfl, rfl, rfl, _, rfl, _⟩ | ⟨_, _, _, _, _, _, rfl, rfl, rfl, _, rfl, _⟩⟩
    all_goals
      simp only [Option.getD_none] at hrs hib
      subst hrs hib
      rfl

theorem readAstepVacuous (cpu : CPU) (ak : AK) (pa : PAddr) (Hdev : devAddr pa = false)
    (Hfe : (classify ak).akIfetch = false)
    (m' : SailM Unit) (rs : RegFile) (k : Nat) (aq : Bool) (base : Int) (ts : List Nat)
    (b : BitVec 8)
    (_Hrowk : (AxOpsem.grow AxTokLedgerMp.mpr 1)[k]? = some (.LLoad aq base ts [b])) (s : Athread)
    (Heqp : s.atP = hp cpu (.impure (.ok (.memRead 1 64 (l3pRreq ak pa))) (fun _ => m')) rs)
    (_Heqk : s.atK = k) (l : Wlabel) (s' : Athread) :
    AxOpsem.astepProg (AxOpsem.grow AxTokLedgerMp.mpr 1) s l s' → False := by
  intro Hst
  obtain ⟨d, d', hps⟩ := astepProgPstep _ s l s' Hst
  rw [Heqp] at hps
  obtain ⟨hrd, _⟩ := pstepProgMemreadLbl cpu 1 64 (l3pRreq ak pa) _ rs ibNone d l s'.atP d' Hdev
    Hfe hps
  rcases l3pAstepProgShape _ s l s' Hst with hadm | hwr | hfn
  · exact l3pRdExclAdmin l hrd hadm
  · exact l3pRdExclWr l hrd hwr
  · exact l3pRdExclFence l hrd hfn

/-- The shell for a read position of hart 1: clause (a) pinned to the graph value, (b) vacuous
at a `memRead` node. -/
theorem wpdReadPos (γ : GName) (cpu : CPU) (ak : AK) (pa : PAddr) (Hdev : devAddr pa = false)
    (Hfe : (classify ak).akIfetch = false)
    (k : Nat) (aq : Bool) (base : Int) (ts : List Nat) (b : BitVec 8)
    (Hrowk : (AxOpsem.grow AxTokLedgerMp.mpr 1)[k]? = some (.LLoad aq base ts [b]))
    (m' : SailM Unit) (P : IProp GF)
    (Hcont : ∀ (v : List (BitVec 8)) (rs : RegFile), graphValue AxTokLedgerMp.mpr (1, k) = some v →
      ⊢ P -∗ @wpEvStep hlc GF _ (imp γ) mpPol Unit AxTokLedgerMp.mpr 1 k (fun _ => True)
        (fun _ => graphValue AxTokLedgerMp.mpr (1, k) = some v) (fun _ => k + 1)
        (fun _ => AxTokLedgerMp.TW (hlc := hlc) γ ⟨hp cpu m' rs, k + 1⟩ 1)) :
    ⊢ P -∗ ∀ rs : RegFile, AxTokLedgerMp.TW (hlc := hlc) γ
      ⟨hp cpu (.impure (.ok (.memRead 1 64 (l3pRreq ak pa))) (fun _ => m')) rs, k⟩ 1 := by
  have H : ⊢ ∀ rs : RegFile, P -∗ AxTokLedgerMp.TW (hlc := hlc) γ
      ⟨hp cpu (.impure (.ok (.memRead 1 64 (l3pRreq ak pa))) (fun _ => m')) rs, k⟩ 1 := by
    iloeb as IH
    iintro %rs HP
    iapply (AxTokLedgerMp.twUnfold (hlc := hlc) γ _ 1).2
    isplit
    · simp only [progressObl]
      itrivial
    unfold wpdMPreStepDef
    iintro %GD %ls ⟨%Hc, #Hg, Hloc⟩
    ihave Hok := AxTokLedgerMp.gconstEq γ GD $$ Hg
    icases Hok with %HGD
    subst HGD
    isplit
    · iintro %id %K %Hst
      obtain ⟨lb, Hlk, Hidlb, _, Hvs⟩ := Hst
      simp only at Hlk
      rw [Hrowk] at Hlk
      obtain rfl := Option.some.inj Hlk
      have Hadv1 : aidentAdvRd id = 1 := by rw [← Hidlb]; rfl
      rw [if_pos Hadv1]
      iintro %v %Hgv %Hlen
      obtain ⟨l0, d0, d0', -, -, Hpst, Hatk⟩ := Hvs v Hlen
      have Hp := readDet cpu ak pa Hdev m' rs d0 l0 (K v).atP d0' Hpst
      have HK : K v = ⟨hp cpu m' rs, k + 1⟩ := by
        rcases e : K v with ⟨p'', k''⟩
        rw [e] at Hp Hatk
        simp only at Hp Hatk
        rw [Hp, Hatk, Hadv1]
      rw [HK]
      iapply (Hcont v rs Hgv) $$ HP
    isplit
    · iintro %l %s' %Hst %_
      exact (readAstepVacuous cpu ak pa Hdev Hfe m' rs k aq base ts b Hrowk _ rfl rfl l s'
        Hst).elim
    isplit
    · iintro %s' %Hw
      obtain ⟨rs', rfl⟩ := awireRsOnly' cpu _ rs none ibNone k s' Hw
      iapply AxTokLedgerMp.wpdSkipStepOfLater'
      inext
      iapply IH $$ %rs' HP
    · iintro %_
      iapply (@postLiftingTrue GF (imp γ) mpPol (fun _ => iprop(⌜True⌝)) 1 _
        (by iintro _; ipureintro; trivial))
  iintro HP %rs
  iapply H $$ %rs HP

/-! ## 4.4 Hart 1 (ld.aq y; ld x), backwards from the row end -/

theorem wpdH1_1 (γ : GName) (cpu : CPU) :
    ⊢ ∀ rs : RegFile, AxTokLedgerMp.TW (hlc := hlc) (GF := GF) γ ⟨hp cpu h1M1 rs, 1⟩ 1 := by
  have H := wpdReadPos (hlc := hlc) (GF := GF) γ cpu l3pAkP xpaM xpaMRam rfl 1 false xa [1] b1
    rfl (.pure ()) iprop(True) (fun v rs Hgv => by
      iintro _
      iapply (wpEvStepClosed (hlc := hlc) γ 1 1 _ _ _ (by decide +kernel)) $$ [] []
      · iapply (mprJ3 (hlc := hlc) γ v Hgv)
      · iapply (wpdRowEndTriv' (hlc := hlc) γ 1 2 (by decide +kernel) _))
  iintro %rs
  ihave H' := H $$ []
  · itrivial
  iapply H' $$ %rs

theorem wpdH1_0 (γ : GName) (cpu : CPU) :
    ⊢ ∀ rs : RegFile, AxTokLedgerMp.TW (hlc := hlc) (GF := GF) γ ⟨hp cpu h1M0 rs, 0⟩ 1 := by
  have H := wpdReadPos (hlc := hlc) (GF := GF) γ cpu akAq ypaM ypaMRam rfl 0 true ya [2] b1
    rfl h1M1 iprop(True) (fun v rs Hgv => by
      iintro _
      iapply (wpEvStepClosed (hlc := hlc) γ 1 0 _ _ _ (by decide +kernel)) $$ [] []
      · iapply (mprJ2 (hlc := hlc) γ v Hgv)
      · iapply (wpdH1_1 (hlc := hlc) γ cpu) $$ %rs)
  iintro %rs
  ihave H' := H $$ []
  · itrivial
  iapply H' $$ %rs

/-! ## 4.5 Hart 0 (sd x; fence rw,w; sd y [release class]) -/

theorem wpdH0_2 (γ : GName) (cpu : CPU) :
    ⊢ ∀ rs : RegFile, AxTokLedgerMp.TW (hlc := hlc) (GF := GF) γ ⟨hp cpu h0M2 rs, 2⟩ 0 := by
  have H := wpdPosShell' (hlc := hlc) (GF := GF) γ cpu 0 iprop(True) 2 h0M2
    (fun lb Hlk => by
      obtain rfl := Option.some.inj
        (Hlk : some (Lbl.LStore false ya [b1] .WCrel) = some lb)
      rfl)
    (fun rs l s' Hst => by
      obtain ⟨rfl, rfl⟩ := astepWriteInv cpu 0 ypaM ypaMRam b1 (.pure ()) rs 2 _ rfl rfl l s' Hst
      simp only [wlWdata, l3pWbytes1]
      iintro _
      iapply (wpEvStepClosed (hlc := hlc) γ 0 2 _ _ _ (by decide +kernel)) $$ [] []
      · iapply (mprJ1 (hlc := hlc) γ)
      · iapply (wpdRowEndTriv' (hlc := hlc) γ 0 3 (by decide +kernel) _))
  iintro %rs
  ihave H' := H $$ []
  · itrivial
  iapply H' $$ %rs

theorem wpdH0_1 (γ : GName) (cpu : CPU) :
    ⊢ ∀ rs : RegFile, AxTokLedgerMp.TW (hlc := hlc) (GF := GF) γ ⟨hp cpu h0M1 rs, 1⟩ 0 := by
  have H := wpdPosShell' (hlc := hlc) (GF := GF) γ cpu 0 iprop(True) 1 h0M1
    (fun lb Hlk => by
      obtain rfl := Option.some.inj
        (Hlk : some (Lbl.LFence true true false true) = some lb)
      rfl)
    (fun rs l s' Hst => by
      obtain ⟨rfl, rfl⟩ := astepFenceInv cpu 0 h0M2 rs 1 _ rfl rfl l s' Hst
      simp only [wlWdata]
      iintro _
      iapply AxTokLedgerMp.wpdSkipStepOfLater'
      inext
      iapply (wpdH0_2 (hlc := hlc) γ cpu) $$ %rs)
  iintro %rs
  ihave H' := H $$ []
  · itrivial
  iapply H' $$ %rs

theorem wpdH0_0 (γ : GName) (cpu : CPU) :
    ⊢ iprop(tokAt (GF := GF) γ xa 0 ∗ tokAt γ ya 0) -∗
      ∀ rs : RegFile, AxTokLedgerMp.TW (hlc := hlc) (GF := GF) γ ⟨hp cpu h0M0 rs, 0⟩ 0 :=
  wpdPosShell' (hlc := hlc) (GF := GF) γ cpu 0 _ 0 h0M0
    (fun lb Hlk => by
      obtain rfl := Option.some.inj
        (Hlk : some (Lbl.LStore false xa [b1] .WCplain) = some lb)
      rfl)
    (fun rs l s' Hst => by
      obtain ⟨rfl, rfl⟩ := astepWriteInv cpu 0 xpaM xpaMRam b1 h0M1 rs 0 _ rfl rfl l s' Hst
      simp only [wlWdata, l3pWbytes1]
      iintro Ht
      iapply (wpEvStepClosed (hlc := hlc) γ 0 0 _ _ _ (by decide +kernel)) $$ [Ht] []
      · iapply (mprJ0 (hlc := hlc) γ)
        iexact Ht
      · iapply (wpdH0_1 (hlc := hlc) γ cpu) $$ %rs)

end wpd

/-! # 5. `ledgerVerified 2 mpr`, END TO END -/

def initMpr {GF : BundledGFunctors} [LedgerG GF] (nm : GName × GName) (i : Agent) : IProp GF :=
  iprop(⌜nm.1 = nm.2⌝ ∗
    (match i with
     | 0 => iprop(tokAt nm.2 xa 0 ∗ tokAt nm.2 ya 0)
     | _ => iprop(True)))

/-- Lean-only: hart 0's initial resources. -/
theorem AxTokLedgerMp.initMpr0 {GF : BundledGFunctors} [LedgerG GF] (nm : GName × GName) :
    initMpr (GF := GF) nm 0 ⊣⊢ iprop(⌜nm.1 = nm.2⌝ ∗ (tokAt nm.2 xa 0 ∗ tokAt nm.2 ya 0)) := .rfl

/-- Lean-only: hart 1's initial resources. -/
theorem AxTokLedgerMp.initMpr1 {GF : BundledGFunctors} [LedgerG GF] (nm : GName × GName) :
    initMpr (GF := GF) nm 1 ⊣⊢ iprop(⌜nm.1 = nm.2⌝ ∗ True) := .rfl

def cpu0 : CPU := ⟨0, by decide⟩

def mprS0 (i : Agent) : Athread :=
  match i with
  | 0 => ⟨hp cpu0 h0M0 zeroRegs, 0⟩
  | _ => ⟨hp cpu0 h1M0 zeroRegs, 0⟩

def mprSN (i : Agent) : Athread :=
  match i with
  | 0 => ⟨hp cpu0 (.pure ()) zeroRegs, 3⟩
  | _ => ⟨hp cpu0 (.pure ()) zeroRegs, 2⟩

/-- Lean-only: the start states, by computation. -/
theorem AxTokLedgerMp.mprS0At0 : mprS0 0 = ⟨hp cpu0 h0M0 zeroRegs, 0⟩ := rfl
theorem AxTokLedgerMp.mprS0At1 : mprS0 1 = ⟨hp cpu0 h1M0 zeroRegs, 0⟩ := rfl

def mprN (i : Agent) : Nat := match i with | 0 => 3 | _ => 2

/-! The concrete functor list (Rocq `mprΣ := #[invΣ; ledgerΣ; axannotΣ]`; header deviation 6). -/

section mprGFSec
open Iris Iris.BI Iris.Std Std MachCSL COFE

def mprGF : BundledGFunctors :=
  BundledGFunctors.default
  |>.set 0 ⟨InvMapF, inferInstance⟩
  |>.set 1 ⟨constOF CoPsetDisjL, inferInstance⟩
  |>.set 2 ⟨constOF (DisjointLeibnizSet PosSet), inferInstance⟩
  |>.set 3 ⟨Auth.AuthURF (constOF Credit), inferInstance⟩
  |>.set 4 ⟨constOF (HeapView Int (Agree (DiscreteO Holder)) (GMapF Int)), inferInstance⟩
  |>.set 5 ⟨DFracAgree.DFracAgreeRF (LaterOF IdOF), inferInstance⟩
  |>.set 6 ⟨constOF (HeapView Geid (Agree (DiscreteO GName)) (GMapF Geid)), inferInstance⟩
  |>.set 7 ⟨constOF AxannotSetR, inferInstance⟩

instance AxTokLedgerMp.mprGFInvMap : ElemG mprGF InvMapF := ⟨0, rfl⟩
instance AxTokLedgerMp.mprGFEnabled : ElemG mprGF (constOF CoPsetDisjL) := ⟨1, rfl⟩
instance AxTokLedgerMp.mprGFDisabled : ElemG mprGF (constOF (DisjointLeibnizSet PosSet)) :=
  ⟨2, rfl⟩
instance AxTokLedgerMp.mprGFCredit : ElemG mprGF (Auth.AuthURF (constOF Credit)) := ⟨3, rfl⟩
instance AxTokLedgerMp.mprGFInvGpreS : InvGpreS mprGF :=
  ⟨⟨inferInstance, inferInstance, inferInstance⟩, ⟨inferInstance⟩⟩
instance AxTokLedgerMp.mprGFLedgerG : LedgerG mprGF := { ledgerMapG := ⟨⟨4, rfl⟩⟩ }
instance AxTokLedgerMp.mprGFAxannotG : AxannotG mprGF :=
  { axannotSavedG := { elemG := ⟨5, rfl⟩ }, axannotMapG := ⟨⟨6, rfl⟩⟩, axannotSetG := ⟨7, rfl⟩ }

end mprGFSec

/-- Lean-only: the mailbox is empty at the empty validated set. -/
theorem AxTokLedgerMp.baseMprEmpty {GF : BundledGFunctors} [LedgerG GF] (γ : GName)
    (GD : Gdexec) (σ : Unit) : baseMpr (GF := GF) γ GD σ ∅ = iprop(True) := by
  unfold baseMpr
  rw [show mprPhase ∅ = 0 by decide +kernel]
  rfl

theorem mprLedgerVerified : ledgerVerified 2 AxTokLedgerMp.mpr := by
  refine @ledgerVerified.mk 2 AxTokLedgerMp.mpr mprGF _ _ _ mpPol ocMpr GName Unit baseMpr initMpr
    [0, 1] mprS0 mprSN mprN (fun _ _ => True) mprPlainWritesOC ?_ (by decide) ?_ ?_ ?_ ?_ ?_ ?_
    ?_ ?_
  · intro GD i k e h
    exact absurd h notElemOfEmpty
  · intro e He
    rw [mprGmo] at He
    simp only [List.mem_cons, List.not_mem_nil, or_false] at He
    rcases He with rfl | rfl | rfl | rfl <;> decide
  · intro _ nm i Hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at Hi
    rcases Hi with rfl | rfl
    · exact h0Run cpu0 zeroRegs
    · exact h1Run cpu0 zeroRegs
  · intro i Hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at Hi
    rcases Hi with rfl | rfl <;> rfl
  · intro i Hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at Hi
    rcases Hi with rfl | rfl <;> rfl
  · intro _ _ nm
    obtain ⟨γ1, γ2⟩ := nm
    iintro H
    icases (AxTokLedgerMp.bigSepLPair 0 1 _).1 $$ H with ⟨H0, -⟩
    icases (AxTokLedgerMp.initMpr0 _).1 $$ H0 with ⟨%Heq, Ht⟩
    simp only at Heq
    subst Heq
    iapply (AxTokLedgerMp.bigSepLPair 0 1 _).2
    rw [AxTokLedgerMp.mprS0At0, AxTokLedgerMp.mprS0At1]
    isplitl [Ht]
    · iapply (wpdH0_0 (hlc := .hasNoLC) γ1 cpu0) $$ Ht %zeroRegs
    · iapply (wpdH1_0 (hlc := .hasNoLC) γ1 cpu0) $$ %zeroRegs
  · istart
    have HA := ledgerAlloc (GF := mprGF) lMpr0
    unfold lMpr0 at HA
    imod HA with ⟨%γ, Ha, Hf⟩
    have Hnone : get? ({[xa := Holder.held 0]} : Ledger) ya = none := by decide +kernel
    icases (BigSepM.bigSepM_insert (Φ := fun a h => tokFrag (GF := mprGF) γ a h)
      (x := Holder.held 0) Hnone).1 $$ Hf with ⟨Hy, Hf⟩
    ihave Hx := BigSepM.bigSepM_singleton.1 $$ Hf
    imodintro
    iexists (γ, γ), ()
    isplitl [Ha]
    · unfold obStInterpL
      rw [AxTokLedgerMp.baseMprEmpty]
      isplitr
      · itrivial
      · iapply ledgerInvInit ocMpr 2 γ AxTokLedgerMp.mpr
        iexact Ha
    · iapply (AxTokLedgerMp.bigSepLPair 0 1 _).2
      isplitl [Hx Hy]
      · iapply (AxTokLedgerMp.initMpr0 _).2
        unfold tokAt
        isplitr
        · ipureintro
          rfl
        · isplitl [Hx]
          · iexact Hx
          · iexact Hy
      · iapply (AxTokLedgerMp.initMpr1 _).2
        isplitr
        · ipureintro
          rfl
        · itrivial
  · intro e e' He'
    exact gmoPrefixGmoLt' _ mprWf e e' ((elemOfListToSet (S := GSet Geid)).1 He')
  · intro e e' He'
    exact absurd He' notElemOfEmpty

/-- … hence violation-free (the POSITIVE half of the matched pair). -/
theorem mprNoViolation : ¬ gdviolationHart 2 AxTokLedgerMp.mpr :=
  adequacyViolFreeLedger 2 AxTokLedgerMp.mpr AxTokLedgerMp.mprCat mprLedgerVerified

end Weak
