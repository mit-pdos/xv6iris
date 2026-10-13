/-
Weak: **W-SCO (A) — the cycle** (plan rev 36 §C W-SCO (A) (1)(c), (2), (3)): the instruction-
independent cycle under the residual invariant, and the theorems it closes.  Lean-only.

`riscvStep tick = try_step 0 false >>= λ _, (if tick then tick_clock () else pure ())`
(`MachCSL/Lang.lean:241-243`), `try_step 0 false = ucPrelude >>= λ hs, ucBody hs >>= ucFinish`
(`MachCSL.uc_tryStep_eq`), `run_hart_active 0 = ucDispatch >>= λ o, match o with | some ip =>
pure _ | none => fetch () >>= ucAfterFetch` (`MachCSL.uc_runHartActive_eq`).  Phase by phase:
* `ucPrelude`, `ucDispatch`, `run_hart_waiting` (a WFI/WRS-parked hart), `ucFinish st` (every arm:
  the interrupt trap `handle_interrupt`, the fetch fault `handle_exception` /
  `ext_handle_fetch_check_error`, the execute trap `exception_handler` / `set_next_pc`, the illegal
  instruction, the wait entry, the retire assertion, the extension hooks, the chained-`ExecuteAs`
  error; then `ucEpilogue`: `tick_pc`, the `minstret` bump), `tick_clock` (`mcycle`/`mtime`,
  `clint_dispatch`): "no cycle event" footprints (`fpPrelude`, `fpDispatch`, `fpWaiting`,
  `fpFinish`, `fpTickClock`) — phase-neutral;
* `fetch ()` returns `F_Base w` only at phase `fetch` (`SailCycleOrderFp.gFetch`, both arms: the
  4-byte read and the TWO halfword reads of a 4-byte instruction at `pc ≡ 2 (mod 4)` — each
  `fetch_bytes` translates and reads on its own, and each instruction-fetch read is a RAM read by
  the boot PMA table and the disabled HTIF window [R32.1][R33.1]);
* `ucAfterFetch fr` (`gAfterFetch`): the announce (an SFENCE.VMA word `sfAnnB 32 w` needs phase
  `fetch` — the cycle's own fetch — and keeps it; any other word moves to `instr`), the pure
  decoders, the landing-pad check, `nextPC`, and `uxaExecAs` = `execute` + ONE `ExecuteAs`
  redirect: at phase `instr` every `execute` arm is fine (`gExecute`: `fence.i`'s ONE
  `Barrier_RISCV_i` by hand, the 121 others by `fpExecNotFI`), at an SFENCE.VMA word the decoder
  answers one of `isS` (`fpDecodeS`), whose `execute` is a footprint with no `ExecuteAs`
  (`fpExecuteS`, `gExecAsS`).
Hence `SailCycleOrderK.cycleOkBoot_holds : cycleOkBoot` — the cycle obligation for EVERY fetched
word under the boot register filter (`pma_regions = bootPMA`, `htif_tohost_base = none`), no
restriction on the word (option (a) of §B(11)); `sailCycleOrder_holds`; the corollaries
`srvwmoXv6M1` / `srvwmoXv6M2` (M1's / M2's statements without `hsco`).

Census: 122 `def execute_*` in `InstsEnd.lean` = the 122 arms of `execute` (`:18769`); no F/D/V.
Platform note [R32.1][R33.1]: TRUE of the model from this platform's reset; FALSE over arbitrary
register files (a fetch from an executable I/O region is an `LDev` read, an HTIF window over RAM
answers a fetch from a register) — hence `wbootFacts σ0` in `sailCycleOrder`.

Every helper is `Weak.SailCycleOrderFp.*`.
-/
import Weak.SailCycleOrderStretch
import Weak.SailCycleOrderExecG
import Weak.PfRunUnpinned

namespace Weak
open MachCSL Sail Sail.ConcurrencyInterfaceV1 LeanRV64D LeanRV64D.Functions
open Sail.ArchSem (FreeM)
namespace SailCycleOrderFp
open SailCycleOrderK SailCycleOrderGW

/-! ## After the fetch, the body, the cycle -/

/-- The announce node: it needs phase `fetch` at an SFENCE.VMA word and then keeps the phase; any
other word moves to `instr`. -/
theorem gAnn {n : Nat} (w : BitVec n) (ph : Ph) (h : sfAnnB n w = true → ph = .fetch) :
    good (fun _ _ => True) Rboot (fun p _ => p = (if sfAnnB n w then ph else .instr)) ph
      (instr_announce w) :=
  ⟨h, rfl⟩

/-- `uxaExecAs` at phase `instr`, filed LAST so that `good_walk` tries it before `gExecAsS` (whose
`isS` premise is unprovable after a non-sfence announce). -/
@[g_reg] theorem gExecAsI (i : instruction) :
    good (fun _ _ => True) Rboot (fun p _ => p = .instr) .instr (uxaExecAs i) :=
  gExecAs i

set_option maxHeartbeats 3000000 in
/-- After a compressed fetch: the announce moves to `instr` (a 16-bit word is never the sfence
marker), then decode, landing pad, the `Zca` gate, `uxaExecAs` at `instr`. -/
theorem gAfterFetchRVC (h : BitVec 16) (ph : Ph) :
    good (fun _ _ => True) Rboot (fun _ _ => True) ph (ucAfterFetch (.F_RVC h)) := by
  simp only [ucAfterFetch, ext_fetch_hook]
  refine gBindQF _ _ _ _ _ _ _ (gAnn h ph (fun hs => absurd hs (by simp [sfAnnB]))) ?_
  intro p _ hp
  have hs : sfAnnB 16 h = false := by simp [sfAnnB]
  rw [hs] at hp
  simp only [Bool.false_eq_true, if_false] at hp
  subst hp
  good_walk

set_option maxHeartbeats 3000000 in
/-- After a 32-bit fetch, from phase `fetch`: the announce (the sfence marker keeps `fetch`, any
other word moves to `instr`), decode, landing pad, `uxaExecAs`. -/
theorem gAfterFetchBase (w : BitVec 32) :
    good (fun _ _ => True) Rboot (fun _ _ => True) .fetch (ucAfterFetch (.F_Base w)) := by
  simp only [ucAfterFetch, ext_fetch_hook]
  refine gBindQF _ _ _ _ _ _ _ (gAnn w .fetch (fun _ => rfl)) ?_
  intro p _ hp
  subst hp
  cases hsf : sfAnnB 32 w
  · simp only [Bool.false_eq_true, if_false]
    good_walk
  · simp only [if_true]
    refine gFpF _ _ _ _ _ _ (fpDecodeS w) ?_
    intro i hi
    have hi := hi hsf
    good_walk

/-- The rest of `run_hart_active` after the fetch, from a phase that is `fetch` whenever the fetch
returned a 32-bit word. -/
@[g_reg] theorem gAfterFetch (fr : FetchResult) (ph : Ph) (h : ∀ w, fr = .F_Base w → ph = .fetch) :
    good (fun _ _ => True) Rboot (fun _ _ => True) ph (ucAfterFetch fr) := by
  cases fr with
  | F_Ext_Error e => exact trivial
  | F_Error p => exact trivial
  | F_RVC hw => exact gAfterFetchRVC hw ph
  | F_Base w =>
    obtain rfl := h w rfl
    exact gAfterFetchBase w

set_option maxHeartbeats 3000000 in
/-- An active hart's step body. -/
@[g_reg] theorem gRunHartActive :
    good (fun _ _ => True) Rboot (fun _ _ => True) .instr (run_hart_active 0) := by
  rw [uc_runHartActive_eq]
  good_walk

set_option maxHeartbeats 3000000 in
/-- The step body (a parked or an active hart). -/
@[g_reg] theorem gBody (hs : HartState) :
    good (fun _ _ => True) Rboot (fun _ _ => True) .instr (ucBody hs) := by
  unfold ucBody
  good_walk

end SailCycleOrderFp

set_option maxHeartbeats 3000000 in
/-- **W-SCO (A) deliverable (1)** [OWN.42][R32.1][R33.1]: every Sail cycle `riscvStep tick`, from
the boundary, satisfies the residual invariant under the boot register filter — for EVERY
fetched word (no candidate restriction). -/
theorem SailCycleOrderK.cycleOkBoot_holds : SailCycleOrderK.cycleOkBoot := by
  intro tick
  unfold riscvStep
  rw [uc_tryStep_eq]
  good_walk

/-- **`sailCycleOrder` is a THEOREM** [OWN.42][OWN.45] (W-SCO (A) deliverable (2)): from this
platform's reset (`wbootFacts σ0`), at an own `fence.i` barrier the latest own cycle label is the
announce, and at an own `sfence.vma` announce it is the instruction's fetch. -/
theorem sailCycleOrder_holds : sailCycleOrder :=
  SailCycleOrderK.sailCycleOrderOfCycle SailCycleOrderK.cycleOkBoot_holds

/-! ## The corollaries: M1 and M2 without the Sail-cycle premise -/

section corollaries
open MachCSL.Stdpp Iris.Std TsoShadow PfStepTsoMem PfStepTsoView Iris.ProgramLogic

/-- **M1 without `hsco`** (W-SCO (A) deliverable (3), plan rev 36 §C W-SCO (A) (3)) — INTERNAL
milestone, NOT published [OWN.2]: `srvwmoXv6M1Core`'s statement with the premise `sailCycleOrder`
discharged by `sailCycleOrder_holds` (direct application). -/
theorem srvwmoXv6M1 (σ0 : WGState) (c : Cand) (pst : Nat → List Pexv6) (dv : Nat → Efab)
    (hP : srvwmoXv6M1Premises σ0 c pst dv)
    (g0 : GState) (hg0 : g0.gen = 0) (hp0 : g0.pow = false) (hgd : σ0.wgdev = g0.m.devs.reset)
    (hfs : diskOf g0.m.devs = Xv6.fsImgDisk) :
    ∃ (cf : Wpcfg Pexv6 Efab) (st : List (Nat × Wlabel)) (r : List MachOfPf.PfRec) (n : Nat)
      (t : List Expr) (g : GState),
      -- the shaped pf run (W5-pre)
      pfRunST pstepEv pclsEv (candKfetch (Xv6.bcRoLo : Int) (Xv6.bcRoHi : Int)) TsoShadow.cohSrc
        (wpInit (imgZ σ0.wgimg) (efInit σ0.wgdev) (epsInit σ0)) st cf ∧
      pairAdjacent st ∧
      cf.pcAgs.map Wpagent.paSt = pst c.cdTr.length ∧ cf.pcDev = dv c.cdTr.length ∧
      cfgMatchd cf (stt (candExec c) c.cdTr.length) ∧
      (∀ i, (tsoShadow TsoShadow.cohSrc st i).mem = shadowOf TsoShadow.cohSrc c.cdTr i) ∧
      -- its run record and the realizing MachCSL run (W4)
      MachOfPf.contR (candKfetch (Xv6.bcRoLo : Int) (Xv6.bcRoHi : Int))
        (wpInit (imgZ σ0.wgimg) (efInit σ0.wgdev) (epsInit σ0)) [] r cf ∧
      MachOfPf.recLabels r = st ∧
      MachOfPf.MRun n ([Expr.power], g0) (Obs.powerOn :: MachOfPf.pfObsOf r) (t, g) ∧
      MachOfPf.SimRel cf st t g ∧
      -- the closed xv6 theorems at that run
      (∀ e, e ∈ t → PrimStep.Reducible (e, g)) ∧
      Xv6.xv6TracePure Xv6.fsimgCov Xv6.fsimgSb.sbLogstart g ∧
      Xv6.xv6NiPhi g (Obs.powerOn :: MachOfPf.pfObsOf r) ∧
      Xv6.unionPhiSync (Obs.powerOn :: MachOfPf.pfObsOf r) ∧
      Xv6.textPristine g ∧
      SrvwmoXv6Adequacy.allocprocAns (Obs.powerOn :: MachOfPf.pfObsOf r) :=
  srvwmoXv6M1Core σ0 c pst dv hP g0 hg0 hp0 hgd hfs sailCycleOrder_holds

/-- **M2 without `hsco`** (W-SCO (A) deliverable (3) [R32.s4]) — INTERNAL milestone, NOT published
[OWN.2]; registered (M2 CLOSE: `roots-weak.txt`, `baseline-weak.json`): `srvwmoXv6M2Core`'s statement
with `sailCycleOrder` discharged by `sailCycleOrder_holds` (direct application). -/
theorem srvwmoXv6M2 (σ0 : WGState) (c : Cand) (pst : Nat → List Pexv6) (dv : Nat → Efab)
    (itvOf : Nat → Nat → Nat) (fiOf : Nat → Nat → Bool)
    (hP : srvwmoXv6M2Premises σ0 c pst dv itvOf fiOf)
    (g0 : GState) (hg0 : g0.gen = 0) (hp0 : g0.pow = false) (hgd : σ0.wgdev = g0.m.devs.reset)
    (hfs : diskOf g0.m.devs = Xv6.fsImgDisk) :
    ∃ (cf : Wpcfg Pexv6 Efab) (st : List (Nat × Wlabel)) (r : List MachOfPf.PfRec) (n : Nat)
      (t : List Expr) (g : GState),
      -- the unpinned, cut-carrying pf run (W5d)
      pfRunSTC pstepEv pclsEv PfRunUnpinned.fokTriv TsoShadow.cohSrc PfRunUnpinned.fcutM2
        (wpInit (imgZ σ0.wgimg) (efInit σ0.wgdev) (epsInit σ0)) st cf ∧
      pairAdjacent st ∧
      cf.pcAgs.map Wpagent.paSt = pst c.cdTr.length ∧ cf.pcDev = dv c.cdTr.length ∧
      cfgMatchd cf (stt (candExec c) c.cdTr.length) ∧
      (∀ i, (tsoShadow TsoShadow.cohSrc st i).mem = shadowOf TsoShadow.cohSrc c.cdTr i) ∧
      (∀ i, (tsoShadow TsoShadow.cohSrc st i).itv = itvOf c.cdTr.length i ∧
        (tsoShadow TsoShadow.cohSrc st i).fiArm = fiOf c.cdTr.length i) ∧
      -- its run record and the realizing MachCSL run (W4)
      MachOfPf.contRC PfRunUnpinned.fokTriv PfRunUnpinned.fcutM2
        (wpInit (imgZ σ0.wgimg) (efInit σ0.wgdev) (epsInit σ0)) [] r cf ∧
      MachOfPf.recLabels r = st ∧
      MachOfPf.MRun n ([Expr.power], g0) (Obs.powerOn :: MachOfPf.pfObsOf r) (t, g) ∧
      MachOfPf.SimRel cf st t g ∧
      -- the closed xv6 theorems at that run
      (∀ e, e ∈ t → PrimStep.Reducible (e, g)) ∧
      Xv6.xv6TracePure Xv6.fsimgCov Xv6.fsimgSb.sbLogstart g ∧
      Xv6.xv6NiPhi g (Obs.powerOn :: MachOfPf.pfObsOf r) ∧
      Xv6.unionPhiSync (Obs.powerOn :: MachOfPf.pfObsOf r) ∧
      Xv6.textPristine g ∧
      SrvwmoXv6Adequacy.allocprocAns (Obs.powerOn :: MachOfPf.pfObsOf r) :=
  srvwmoXv6M2Core σ0 c pst dv itvOf fiOf hP g0 hg0 hp0 hgd hfs sailCycleOrder_holds

end corollaries

end Weak
