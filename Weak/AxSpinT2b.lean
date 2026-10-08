/-
Weak: **THEOREM 2 (`allocpidOpen`) and THEOREM 1 (`allocpid2Distinct`)** — the two-hart
allocpid distinctness capstones on xv6's REAL `allocproc` (inlined allocpid, `allocproc + 0x38 ..
+ 0x9a`) in the Lean weak tier, STAGE 1 of the owner's two-stage landing (Q-T2-1: the panic arms
are PINNED, see "Pins" below).  Theorem 2 design (`notes/weak-lb-thm2-design.md`) §B, §C.4–5,
§D row `AxSpinT2b`.  NEW Lean file (no Rocq source: the Rocq development stopped before the
capstone).

## What this file proves

**`allocpidOpen`** (Theorem 2, OPEN THIRD HART).  Harts A and B run the inlined allocpid
segment from `allocproc + 0x38` (`entryOk`) on rows of the family `allocFull` (AxSpinT2a), with
the Option V / Q18b value pins `AllocPins`; hart C is ARBITRARY — its only constraint is the
iProp premise `HwpC` (C's program is verified against the joint xv6 protocol `protXv6` from its
share `xv6Init` of the initial resources, post `True`).  Conclusion, on every graph and run
satisfying the premises:
  `npSrc G L (A, t2KBd qA) (A, t2KA qA) ∧ npSrc G L (B, t2KBd qB) (B, t2KA qB) ∧
   (t2Complete A → t2Complete B → pidOf A qA ≠ pidOf B qB ∧
      ∃ wA wB, pidOf A qA = some (wbytes 4 wA) ∧ pidOf B qB = some (wbytes 4 wB) ∧ wA ≠ wB)`
— A's and B's nextpid reads take their value from the nextpid write that is gmo-latest before
their own lock claim (`npSrc`, AxSpinU), and the pids they store in `p->pid` (`pidOf` = the data
of the `p->pid` store, AxSpinT2a) are distinct 32-bit words.

**`allocpid2Distinct`** (Theorem 1) — the corollary of Theorem 2 with C's row EMPTY (owner ruling
Q-T2-11): `gmo` has only A's and B's events, C is a phantom agent of the layout with
`grow C = []`, its run is the empty one, and its `HwpC` is discharged here by
`AxSpinApA.wpdEndAnn` (post `True` past the end of an empty row).  Same conclusion.

## How

`tierAAdequacyAnnGateJointT` (AxSpinJ) at `GF := AxSpinX7.xv6GF`, policy `xv6Pol GT`,
`obStInterp0 := protXv6 L`, `init := xv6Init L`, `HobAlloc := xv6HobAlloc L` (from the layout
and image premises), `Hok := xv6Hok GT HconsT Hcl` (class-independent, every hart, C included);
`harts = [A, B, C]`; script template `AxSpinJ2.uAllocOpen`.  `Hwp` = A's and B's
`AxSpinApA.wpdAllocpidSegE` (the whole-segment WPd, post `AxSpinApA.t2PostS`, from the
`AxSpinApA.Hyp` built by `AxSpinApA.hypXv6`) and `HwpC`, each lifted to the per-hart post
`AxSpinApA.t2PhiS` by `AxSpinWit.tierAWpdMono`.  `Hjoint` = `AxSpinApA.t2JointS` (issued-
fragment exclusivity `AxSpinT2a.fragNe` — POSITION-INDEPENDENT, so it works for an arbitrary C;
NOT the graph dichotomy), whose `t2ConclS` is the conclusion.  The post is PROVISIONAL ruling
Q-T2-14's `a3`-free `t2PostS` (AxSpinApA header, "The `a3` conjunct": the register conjunct of
`AxSpinT2a.t2Post` cannot be closed past the row end), so the conclusion is about `pidOf`, the
stored pid words, not about `a3`.

## HONESTY: why ownership is load-bearing here

C is constrained ONLY by `HwpC`.  No premise of either theorem mentions C's row, C's values or
C's control flow (`Hharts` merely says no fourth agent emits events; `HkC`, `Hrun`, `Hend` say C's
run is a run of the model).  Every value premise below is about A's or B's OWN events.  So the
DATA facts of the conclusion — `npSrc` (the nextpid read is not served by a racing write) and
`wA ≠ wB` — hold BECAUSE every write C can perform is a protocol step licensed by `protXv6`:
nextpid and `lk->cpu` are written only under the lock (`RPid`'s histories), the issued set and the
exclusive fragments `FRAG` are minted only at the locked nextpid increment, and A's / B's private
bytes (stack windows, `p->pid`, `p->state`, cpu fields) are not C's.  Drop `HwpC` and the
conclusion is false: a C that stores to nextpid gmo-after B's claim makes `npSrc` fail
(certificate (b-np), AxSpinT2d), a C that zeroes the lock word lets A and B both enter
(certificate (b-lk)).  Theorem 1 is the degenerate case where C does nothing.

What the theorems do NOT say.  `allocFull` + the pins fix A's and B's control flow and addresses
on the NORMAL path; the theorems prove nothing about a hart whose control flow or addresses are
diverted, whose nextpid read is 1000 / wraps / collides with a scanned pid, or whose pinned
values differ.  The pins restrict WHICH executions are covered (C may legitimately drive nextpid
to 1000 — such executions are not covered); they do not constrain C.  Allocproc's own scan /
`p->lock` and the caller context are outside (`p_A`, `p_B` are premises via `T2LayHyp`, not
derived).  `t2Complete A → t2Complete B →` is VACUOUS at stage 1 (`HfullA`/`HfullB` are
premises); it is stated for the stage-2 upgrade.  The TLB is warm at entry and the PTE pages are
read-only (`entryOk`, `MapOk`; HAD, design §A.5).  `HfinA`/`HfinB`: the runs stop at instruction
boundaries (the post is guarded by `¬ midState`; a run cut mid-instruction is not covered).
IMAGE NOTE: `textFixed G i (imgS σi)` pins EVERY read of hart `i` at an address in `σi`'s memory
domain to `σi`'s byte; `σi` must therefore be a text + page-table image (as
`AxSpinTextCerts.σK`), NOT a full memory image — if `σi` also held nextpid, both harts' nextpid
reads would be pinned to `n0` and the premises would be contradictory for two complete rows
(the data image is `GT.gtG.gxImg`, constrained only by `Himgc`/`Himgn`).

## Pins (owner ruling 2026-10-08: NAMED scope premises, listed VERBATIM)

All are hypotheses of both theorems, one copy per hart `i ∈ {A, B}` (`HpinsA`, `HpinsB`,
`HfullA`, `HfullB`), with `GD = gtAdGd GT`.  `AllocPins GD i q` (AxSpinT2a §3), field by field:
```
  poMy1 : graphValue GD (i, t2KPo + 5) = some (stBytes 8 (AxSpinPO.ppo 0x14))
  poArm : ∀ vn, graphValue GD (i, t2KPo + 7) = some vn → (ldRes false 4 vn == zero_reg) = q.b
  poMy2 : q.b = true → graphValue GD (i, t2KPo + 10) = some (stBytes 8 (AxSpinPO.ppo 0x30))
  poMy3 : graphValue GD (i, t2KPoT q + 2) = some (stBytes 8 (AxSpinPO.ppo 0x1c))
  poRet : graphValue GD (i, t2KPoT q + 6) = some (stBytes 8 (AxSpinHdB.pac 0x10))
  hdRets : q.hb = true →
    graphValue GD (i, t2KHd q + 7) = some (stBytes 8 (pch 0x1a)) ∧
    graphValue GD (i, t2KHd q + 9) = some (stBytes 8 (AxSpinHdB.pac 0x16))
  hdArm : q.hb = true → ∀ vcpu, graphValue GD (i, t2KHd q + 4) = some vcpu →
    ldRes false 8 vcpu ≠ cpuAddr (cpuOf i)
  aqMy : graphValue GD (i, t2KMy q + 2) = some (stBytes 8 (AxSpinHdB.pac 0x28))
  aqRet : graphValue GD (i, t2KMy q + 5) = some (stBytes 8 (pca 0x44))
  npNowrap : ∀ vs, graphValue GD (i, t2KBd q) = some vs →
    (wordOfBytes 4 vs : BitVec 32) ≠ 1000#32 ∧ (wordOfBytes 4 vs : BitVec 32).toNat + 1 < 2 ^ 32
  npNcoll : ∀ vs, graphValue GD (i, t2KBd q) = some vs → ∀ j, j < 64 → ∀ v,
    graphValue GD (i, t2KBd q + 1 + j) = some v → (wordOfBytes 4 v : BitVec 32) ≠ wordOfBytes 4 vs
  rhRets : graphValue GD (i, t2KRh q + 7) = some (stBytes 8 (pch 0x1a)) ∧
    graphValue GD (i, t2KRh q + 9) = some (stBytes 8 (AxSpinHdB.prl 0x10))
  rhArm : ∀ vcpu, graphValue GD (i, t2KRh q + 4) = some vcpu → ldRes false 8 vcpu = cpuAddr (cpuOf i)
  ppMy : graphValue GD (i, t2KPp q + 4) = some (stBytes 8 (ppp 0x0c))
  ppGe : ∀ vn, graphValue GD (i, t2KPp q + 6) = some vn →
    zopz0zKzJ_s zero_reg (ldRes false 4 vn) = false
  ppArm : ∀ vn, graphValue GD (i, t2KPp q + 6) = some vn → (addiwm1 (ldRes false 4 vn) != zero_reg) = q.c
  ppInt : q.c = false → ∀ vi, graphValue GD (i, t2KPp q + 8) = some vi →
    (ldRes false 4 vi == zero_reg) = true
  ppRet : graphValue GD (i, t2KPp q + 8 + (if q.c then 0 else 1)) =
    some (stBytes 8 (AxSpinHdB.prl 0x22))
  rlRet : graphValue GD (i, t2KRr q) = some (stBytes 8 (pca 0x98))
  poS1 : graphValue GD (i, t2KPoT q + 8) =
    some (stBytes 8 (BitVec.ofNat 64 KernelSyms.«pid_lock»))
  hdS1 : q.hb = true → graphValue GD (i, t2KHd q + 11) =
    some (stBytes 8 (BitVec.ofNat 64 KernelSyms.«pid_lock»))
  aqS1 : graphValue GD (i, t2KMy q + 7) = graphData GD (i, 2)
  rhCpu : graphValue GD (i, t2KRh q + 4) = some (stBytes 8 (cpuAddr (cpuOf i)))
  rhS1 : graphValue GD (i, t2KRh q + 11) =
    some (stBytes 8 (BitVec.ofNat 64 KernelSyms.«pid_lock»))
  rlS1 : graphValue GD (i, t2KRr q + 2) = graphData GD (i, t2KRl q + 2)
```
Classification: Q18b (scope; a verified C may falsify them, then the execution is not covered):
`npNowrap`, `npNcoll`.  Option V return-address reloads (`ra`): `poMy1 poMy2 poMy3 poRet hdRets
aqMy aqRet rhRets ppMy ppRet rlRet`.  Option V `s1` reloads: `poS1 hdS1 aqS1 rhS1 rlS1`.
Option V arms (the PANIC ARMS pinned not taken — stage 1): `hdArm rhArm rhCpu ppGe`; the control
arms (choose `q`, not restrictive): `poArm ppArm ppInt`.

The STORE-VALUE conditions and the label / value conditions inside `allocFull row q i S p`
(AxSpinT2a §2), verbatim:
```
  t2CpuVals row i := ∀ (k : Nat) (lb : Lbl) (rl : Bool) (m : Nat), row[k]? = some lb →
    aidentWr (aident lb) = some (rl, AxSpinT2a.zLk + 16, m) →
    ∃ vw cls, lb = .LStore false (AxSpinT2a.zLk + 16) vw cls ∧
      (vw = cvx i ∨ vw = List.replicate 8 b0)
  t2RelVals row q := ∀ vw cls,
    row[relKw (t2KRl q)]? = some (.LStore false AxSpinT2a.zLk vw cls) → vw = AxSpinX4.z4
  AxSpinAq1.spinRmw row (t2KSp q) q.n AxSpinT2a.zLk := ∀ j, j ≤ q.n → ∃ (t : Nat) (rvs : List (BitVec 8)),
    row[t2KSp q + j]? = some (.LRmw true false AxSpinT2a.zLk [t, t, t, t] rvs AxSpinX4.o4 .WCexcl) ∧
    (rvs = AxSpinX4.z4 ∨ ∃ b0', rvs[0]? = some b0' ∧ b0' ≠ b0)
  lkBranch row k hb := ∃ lb vs, row[k]? = some lb ∧ lblValue lb = some vs ∧
    hb = (ldRes false 4 vs != 0#64)                  -- at k = t2KHd q (hb = q.hb), t2KRh q (true)
  spinVals row (t2KSp q) q.n := ∀ j, j ≤ q.n → ∃ lb vs, row[t2KSp q + j]? = some lb ∧
    lblValue lb = some vs ∧ aqFail vs = decide (j < q.n)
```
(`t2CpuVals`, `t2RelVals`, `spinRmw`'s written data: store values fixed by the code, true on
real rows, NOT consequences of the shape.  `lkBranch (t2KRh q) true` is release's
holding-lock-bit: a further panic-arm pin.  `lkBranch (t2KHd q) q.hb` and `spinVals` choose
`q`.)  The remaining conjuncts of `allocFull` (`RowShX`, the length, `RowAllocpidBody`) are
shape: addresses, widths and classes of A's / B's own row.

## Stage 2 (not here)

Stage T2-cuts (ID-8: `RowShP`/`Des`/P-twins, ≈ 5 files) will DISCHARGE the panic-arm pins
(`hdArm`, `rhArm`/`rhCpu`/`lkBranch (t2KRh q) true`, `ppGe`) and the s1/ra reload pins by D4
readback of the owned annotations (the reloads read the hart's own private spills; holding's
`lk->cpu` read on release's call reads the holder's own store; pop_off's `noff` reads its own
cpu field), turning Rocq's "no panic" conjunct into a theorem, and will drop
`t2Complete A → t2Complete B →`'s vacuity by covering cut rows.  The Q18b pins stay scope
premises (owner Q-T2-5) unless the collision-retry row family is added (Q-T2-3 alt).

## Deviations from the design

1. Post `t2PostS` (Q-T2-14, provisional): no `a3 = sext32 w` conjunct in the conclusion.
2. The conclusion's distinctness is `pidOf A ≠ pidOf B` plus the word form (`∃ wA wB …`);
   `pidOf` takes the hart's `T2Prm` (AxSpinT2a deviation 3).
3. Extra premises the design's sketch leaves implicit: `HalA`/`HalB` (`S % 16 = 0`, AxSpinApA
   `Lay`), `HmapA`/`HmapB` (`AxSpinApA.MapOk`), `Htxt` (`AxSpinApA.tailText`, + 0x98 / + 0x9a),
   `HfinA`/`HfinB` (`¬ midState` final states, AxSpinT2a `t2Joint`'s premises), `HkC`.
4. `Hk0` for A, B is derived from `entryOk` (`entryK0`); C's is `HkC`.
5. Theorem 1 keeps the phantom C in the layout (`T2LayHyp A B C …`: `xlayXv6` is a three-hart
   layout); C's start state is A's program at position 0 (any state works: C never steps).
6. Audit roots: registered in the Weak audit target (`tools/ci/roots-weak.txt`, `tools/audit/baseline-weak.json`; run `tools/ci/audit.sh --weak`, see `Weak/AxSpinT2d.lean`).

**Reused** (by name): `tierAAdequacyAnnGateJointT` (AxSpinJ), `xv6Init`/`xv6HobAlloc`/`xv6Hok`/
`xv6AxpolWf`/`protXv6`/`clb`/`npb` (AxSpinX), `AxSpinX7.xv6GF`, `xlayXv6`/`xlayXv6Ok`/`T2LayHyp`/
`allocFull`/`AllocPins`/`entryOk`/`entryK0`/`t2Complete`/`pidOf` (AxSpinT2a),
`AxSpinApA.hypXv6`/`wpdAllocpidSegE`/`t2PostS`/`t2PhiS`/`t2ConclS`/`t2JointS`/`wpdEndAnn`,
`AxSpinJ2.bigSepLTriple`, `AxSpinWit.tierAWpdMono`, `catTAd`, `wordOfBytesWbytes`, `nsteps_O`.

**Lean-only declarations**: `allocpidOpen`, `allocpid2Distinct` (grepped absent from the tree);
helpers `AxSpinT2b.*`.
-/
import Weak.AxSpinApA
import Weak.AxSpinJ

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D LeanRV64D.Functions

/-! # 1. Helpers -/

/-- The CS resources of `xv6Init`: the lock invariant and `notheld`. -/
theorem AxSpinT2b.initCs {GF : BundledGFunctors} [AxSpinX.Xv6G GF] (L : Xlay) (GD : Gdexec)
    (nm : Xv6N) (i : Agent) :
    xv6Init (GF := GF) L GD nm i ⊢
      isLock nm.xnReg L.xlLk (RPid L nm.xnH nm.xnM nm.xnI GD) ∗ notheld nm.xnReg L.xlLk i := by
  unfold xv6Init
  iintro ⟨-, -, -, Hil, Hnh⟩
  isplitl [Hil]
  · iexact Hil
  · iexact Hnh

theorem AxSpinT2b.phiSA (GD : Gdexec) (L : Xlay) (A B : Agent) (qA qB : T2Prm)
    (Hinv : InvGS_gen .hasNoLC AxSpinX7.xv6GF) (Hann : AxannotGS AxSpinX7.xv6GF) (nm : Xv6N)
    (s : Athread) :
    AxSpinApA.t2PhiS GD L A B qA qB Hinv Hann nm A s = AxSpinApA.t2PostS GD L nm A qA s := by
  simp [AxSpinApA.t2PhiS]

theorem AxSpinT2b.phiSB (GD : Gdexec) (L : Xlay) (A B : Agent) (qA qB : T2Prm) (hAB : A ≠ B)
    (Hinv : InvGS_gen .hasNoLC AxSpinX7.xv6GF) (Hann : AxannotGS AxSpinX7.xv6GF) (nm : Xv6N)
    (s : Athread) :
    AxSpinApA.t2PhiS GD L A B qA qB Hinv Hann nm B s = AxSpinApA.t2PostS GD L nm B qB s := by
  simp [AxSpinApA.t2PhiS, Ne.symm hAB]

theorem AxSpinT2b.phiSC (GD : Gdexec) (L : Xlay) (A B C : Agent) (qA qB : T2Prm) (hCA : C ≠ A)
    (hCB : C ≠ B) (Hinv : InvGS_gen .hasNoLC AxSpinX7.xv6GF) (Hann : AxannotGS AxSpinX7.xv6GF)
    (nm : Xv6N) (s : Athread) :
    AxSpinApA.t2PhiS GD L A B qA qB Hinv Hann nm C s = iprop(True) := by
  simp [AxSpinApA.t2PhiS, hCA, hCB]

/-- The three harts of the layout are distinct. -/
theorem AxSpinT2b.distinct {A B C : Agent} {Sf pf : Agent → Int} {ptp : Int → Prop}
    (H : T2LayHyp A B C Sf pf ptp) : A ≠ B ∧ A ≠ C ∧ B ≠ C := by
  have h := H.nd
  refine ⟨fun e => ?_, fun e => ?_, fun e => ?_⟩
  · rw [e] at h; simp at h
  · rw [e] at h; simp at h
  · rw [e] at h; simp at h

theorem AxSpinT2b.mem3 {A B C i : Agent} (Hi : i ∈ [A, B, C]) : i = A ∨ i = B ∨ i = C := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at Hi
  exact Hi

/-- Two pids in word form are equal iff the words are. -/
theorem AxSpinT2b.pidNe (x y : Option (List (BitVec 8))) (wA wB : BitVec 32)
    (hx : x = some (WeakInterpProj.wbytes 4 wA)) (hy : y = some (WeakInterpProj.wbytes 4 wB))
    (hne : wA ≠ wB) : x ≠ y := by
  intro h
  rw [hx, hy, Option.some.injEq] at h
  apply hne
  have h' := congrArg (wordOfBytes 4) h
  rw [wordOfBytesWbytes, wordOfBytesWbytes] at h'
  exact h'

/-! # 2. THEOREM 2 -/

set_option maxHeartbeats 1600000 in
/-- **THEOREM 2 (`allocpidOpen`, stage 1: panic arms pinned).**  Harts A, B run the inlined
allocpid of xv6's `allocproc` (+ 0x38 .. + 0x9a) on rows of the family, hart C is an ARBITRARY
program verified against the joint protocol (`HwpC`, the only iProp premise).  Then A's and B's
nextpid reads are sourced by the gmo-latest nextpid write before their claim, and (for complete
rows) the pids they store are distinct.  Every premise is listed with a one-line gloss; the
value pins are listed verbatim in the file header. -/
theorem allocpidOpen (GT : GdexecT) (A B C : Agent) (Sf pf : Agent → Int) (ptp : Int → Prop)
    (qA qB : T2Prm) (σi : ExecSt) (T : PTree) (satp0 : BitVec 64) (n0 : Int)
    (s0 sN : Agent → Athread) (n : Agent → Nat)
    -- MODEL: the tagged graph is riscv.cat-consistent
    (HconsT : rvwmoCatConsistentT GT)
    -- MODEL: control dependencies are closed (`AxSpinGate`)
    (Hcl : ctrlClosed GT)
    -- SCOPE: only A, B, C emit memory events
    (Hharts : ∀ e, e ∈ GT.gtG.gxGmo → e.1 ∈ [A, B, C])
    -- LAYOUT: distinct harts < NCPU, distinct `proc[]` slots, disjoint stack windows in `stack0`
    (HLay : T2LayHyp A B C Sf pf ptp)
    -- LAYOUT: allocproc's frames of A and B are 16-aligned
    (HalA : Sf A % 16 = 0) (HalB : Sf B % 16 = 0)
    -- IMAGE: `lk->cpu` is 0 initially (initlock)
    (Himgc : ∀ a, a ∈ clb (xlayXv6 A B C Sf pf ptp) → GT.gtG.gxImg a = some b0)
    -- IMAGE: nextpid's initial value `n0` is a 32-bit word
    (Hn0 : 0 ≤ n0 ∧ n0 < 2 ^ 32)
    -- IMAGE: nextpid's bytes initially hold `n0`
    (Himgn : ∀ (j : Nat) a v, (npb (xlayXv6 A B C Sf pf ptp))[j]? = some a →
      (WeakInterpProj.wbytes 4 (BitVec.ofInt 32 n0))[j]? = some v → GT.gtG.gxImg a = some v)
    -- TEXT: the kernel text of acquire, mycpu, push_off, holding, pop_off, release, allocpid's
    -- inlined copy and allocproc's + 0x98 / + 0x9a (`σi` = text + page-table image)
    (Htxa : acquireText σi T) (Htxm : mycpuText σi T) (Htxp : pushOffText σi T)
    (Htxh : holdingText σi T) (Htxq : popOffText σi T) (Htxr : releaseText σi T)
    (Htxc : allocpidText σi T) (Htxt : AxSpinApA.tailText σi T)
    -- TEXT: A's / B's reads of `σi`'s domain return `σi`'s bytes, which are in the graph image
    (HfixA : textFixed (gtAdGd GT) A (imgS σi)) (HfixB : textFixed (gtAdGd GT) B (imgS σi))
    -- TRANSLATION: Sv39 satp, ASID 0, root = `T`
    (hmode : _get_Satp64_Mode (Mk_Satp64 satp0) = 8#4)
    (hasid : zero_extend (m := 16) (satp_to_asid satp0) = 0#16)
    (hppn : BitVec.setWidth 44 (satp_to_ppn satp0) = T.base)
    -- TRANSLATION: `T` maps A's / B's data ranges VA = PA (load / store / AMO)
    (HmapA : AxSpinApA.MapOk σi T A (Sf A) (pf A)) (HmapB : AxSpinApA.MapOk σi T B (Sf B) (pf B))
    -- ROWS: A's / B's rows are in the allocpid family (shape + the value conditions in the header)
    (HfullA : allocFull (AxOpsem.grow (gtAdGd GT) A) qA A (Sf A) (pf A))
    (HfullB : allocFull (AxOpsem.grow (gtAdGd GT) B) qB B (Sf B) (pf B))
    -- PINS: Option V + Q18b value pins of A and B (verbatim in the header)
    (HpinsA : AllocPins (gtAdGd GT) A qA) (HpinsB : AllocPins (gtAdGd GT) B qB)
    -- ENTRY: A / B start at allocproc + 0x38, S-mode, SIE = 0, sp / s1 / tp set, warm TLB
    (HentA : entryOk T satp0 A (Sf A) (pf A) (s0 A))
    (HentB : entryOk T satp0 B (Sf B) (pf B) (s0 B))
    -- ENTRY: C starts at row position 0
    (HkC : (s0 C).atK = 0)
    -- RUN: each hart's run is `n i` model steps from `s0 i` to `sN i`
    (Hrun : ∀ (_ : AxannotGS AxSpinX7.xv6GF) (nm : Xv6N) i, i ∈ [A, B, C] →
      nsteps (tierAAstep (gtAdGd GT) nm i) (n i) (s0 i) (sN i))
    -- RUN: each hart's run consumes its whole row
    (Hend : ∀ i, i ∈ [A, B, C] → (sN i).atK = (AxOpsem.grow (gtAdGd GT) i).length)
    -- RUN: A's / B's runs stop at an instruction boundary
    (HfinA : ¬ midState (sN A)) (HfinB : ¬ midState (sN B))
    -- C: an arbitrary program verified against the joint protocol (the ONLY iProp premise)
    (HwpC : ∀ [InvGS_gen .hasNoLC AxSpinX7.xv6GF] [AxannotGS AxSpinX7.xv6GF] (nm : Xv6N),
      ⊢ xv6Init (xlayXv6 A B C Sf pf ptp) (gtAdGd GT) nm C -∗
        @tierAWpd AxSpinX7.xv6GF .hasNoLC _ _ (xv6Pol GT) (gtAdGd GT) Xv6N Unit
          (protXv6 (xlayXv6 A B C Sf pf ptp)) nm (s0 C) .MaybeStuck C (fun _ => iprop(True))) :
    npSrc (gtAdGd GT).gdG (xlayXv6 A B C Sf pf ptp) (A, t2KBd qA) (A, t2KA qA) ∧
    npSrc (gtAdGd GT).gdG (xlayXv6 A B C Sf pf ptp) (B, t2KBd qB) (B, t2KA qB) ∧
    (t2Complete (gtAdGd GT) A (Sf A) (pf A) → t2Complete (gtAdGd GT) B (Sf B) (pf B) →
      pidOf (gtAdGd GT) A qA ≠ pidOf (gtAdGd GT) B qB ∧
      ∃ wA wB : BitVec 32,
        pidOf (gtAdGd GT) A qA = some (WeakInterpProj.wbytes 4 wA) ∧
        pidOf (gtAdGd GT) B qB = some (WeakInterpProj.wbytes 4 wB) ∧ wA ≠ wB) := by
  obtain ⟨hAB, hAC, hBC⟩ := AxSpinT2b.distinct HLay
  have Hcons := catTAd GT HconsT
  have HL := xlayXv6Ok A B C Sf pf ptp HLay
  have HyA := AxSpinApA.hypXv6 A B C Sf pf ptp HLay GT σi T A qA (.inl rfl) HalA HfullA HpinsA
    HmapA Htxa Htxm Htxp Htxh Htxq Htxr Htxc Htxt HfixA
  have HyB := AxSpinApA.hypXv6 A B C Sf pf ptp HLay GT σi T B qB (.inr (.inl rfl)) HalB HfullB
    HpinsB HmapB Htxa Htxm Htxp Htxh Htxq Htxr Htxc Htxt HfixB
  have Hk0 : ∀ i, i ∈ [A, B, C] → (s0 i).atK = 0 := by
    intro i Hi
    rcases AxSpinT2b.mem3 Hi with rfl | rfl | rfl
    · exact entryK0 T satp0 _ _ _ _ HentA
    · exact entryK0 T satp0 _ _ _ _ HentB
    · exact HkC
  have Hwp : ∀ [Hinv : InvGS_gen .hasNoLC AxSpinX7.xv6GF] [Hann : AxannotGS AxSpinX7.xv6GF]
      (nm : Xv6N),
      ⊢ ([∗list] i ∈ [A, B, C], xv6Init (xlayXv6 A B C Sf pf ptp) (gtAdGd GT) nm i) -∗
        [∗list] i ∈ [A, B, C],
          @tierAWpd AxSpinX7.xv6GF .hasNoLC _ _ (xv6Pol GT) (gtAdGd GT) Xv6N Unit
            (protXv6 (xlayXv6 A B C Sf pf ptp)) nm (s0 i) .MaybeStuck i
            (AxSpinApA.t2PhiS (gtAdGd GT) (xlayXv6 A B C Sf pf ptp) A B qA qB Hinv Hann nm i) := by
    intro Hinv Hann nm
    have WA := (AxSpinApA.wpdAllocpidSegE (hlc := .hasNoLC) (GF := AxSpinX7.xv6GF)
      (xlayXv6 A B C Sf pf ptp) GT nm HL Hcons σi T satp0 hmode hasid hppn A qA (Sf A) (pf A)
      HyA (s0 A) HentA).trans (wand_mono .rfl (wand_mono .rfl
        (AxSpinWit.tierAWpdMono (hlc := .hasNoLC) (pol := xv6Pol GT) (gtAdGd GT) Xv6N Unit
          (protXv6 (xlayXv6 A B C Sf pf ptp)) nm (s0 A) .MaybeStuck A _
          (AxSpinApA.t2PhiS (gtAdGd GT) (xlayXv6 A B C Sf pf ptp) A B qA qB Hinv Hann nm A)
          (fun s => by rw [AxSpinT2b.phiSA]))))
    have WB := (AxSpinApA.wpdAllocpidSegE (hlc := .hasNoLC) (GF := AxSpinX7.xv6GF)
      (xlayXv6 A B C Sf pf ptp) GT nm HL Hcons σi T satp0 hmode hasid hppn B qB (Sf B) (pf B)
      HyB (s0 B) HentB).trans (wand_mono .rfl (wand_mono .rfl
        (AxSpinWit.tierAWpdMono (hlc := .hasNoLC) (pol := xv6Pol GT) (gtAdGd GT) Xv6N Unit
          (protXv6 (xlayXv6 A B C Sf pf ptp)) nm (s0 B) .MaybeStuck B _
          (AxSpinApA.t2PhiS (gtAdGd GT) (xlayXv6 A B C Sf pf ptp) A B qA qB Hinv Hann nm B)
          (fun s => by rw [AxSpinT2b.phiSB _ _ _ _ _ _ hAB]))))
    iintro HI
    icases (AxSpinJ2.bigSepLTriple A B C
      (fun i => xv6Init (GF := AxSpinX7.xv6GF) (xlayXv6 A B C Sf pf ptp) (gtAdGd GT) nm i)).1
      $$ HI with ⟨HA, HB, HC⟩
    iapply (AxSpinJ2.bigSepLTriple A B C _).2
    isplitl [HA]
    · ihave HA := AxSpinT2b.initCs (xlayXv6 A B C Sf pf ptp) (gtAdGd GT) nm A $$ HA
      icases HA with ⟨Hil, Hnh⟩
      ihave W := WA $$ []
      · iempintro
      iapply W $$ Hil Hnh
    isplitl [HB]
    · ihave HB := AxSpinT2b.initCs (xlayXv6 A B C Sf pf ptp) (gtAdGd GT) nm B $$ HB
      icases HB with ⟨Hil, Hnh⟩
      ihave W := WB $$ []
      · iempintro
      iapply W $$ Hil Hnh
    · iapply (AxSpinWit.tierAWpdMono (hlc := .hasNoLC) (pol := xv6Pol GT) (gtAdGd GT) Xv6N Unit
        (protXv6 (xlayXv6 A B C Sf pf ptp)) nm (s0 C) .MaybeStuck C (fun _ => iprop(True))
        (AxSpinApA.t2PhiS (gtAdGd GT) (xlayXv6 A B C Sf pf ptp) A B qA qB Hinv Hann nm C)
        (fun s => by rw [AxSpinT2b.phiSC _ _ _ _ _ _ _ (Ne.symm hAC) (Ne.symm hBC)]))
      iapply HwpC nm $$ HC
  have Hjoint : ∀ [Hinv : InvGS_gen .hasNoLC AxSpinX7.xv6GF] [Hann : AxannotGS AxSpinX7.xv6GF]
      (nm : Xv6N),
      ⊢ ([∗list] i ∈ [A, B, C], AxSpinApA.t2PhiS (gtAdGd GT) (xlayXv6 A B C Sf pf ptp) A B qA qB
          Hinv Hann nm i (sN i)) ==∗
        ⌜AxSpinApA.t2ConclS (gtAdGd GT) (xlayXv6 A B C Sf pf ptp) A B qA qB⌝ := by
    intro Hinv Hann nm
    exact AxSpinApA.t2JointS (gtAdGd GT) (xlayXv6 A B C Sf pf ptp) A B C qA qB sN hAB HfinA HfinB
      Hinv Hann nm
  have HP := @tierAAdequacyAnnGateJointT AxSpinX7.xv6GF _ _ (xv6Pol GT) GT Xv6N Unit
    (protXv6 (xlayXv6 A B C Sf pf ptp)) (xv6Init (xlayXv6 A B C Sf pf ptp) (gtAdGd GT))
    (xv6AxpolWf GT) HconsT [A, B, C] HLay.nd Hharts s0 sN n Hrun Hk0 Hend
    (AxSpinApA.t2PhiS (gtAdGd GT) (xlayXv6 A B C Sf pf ptp) A B qA qB) Hwp _ Hjoint
    (xv6HobAlloc (GF := AxSpinX7.xv6GF) (xlayXv6 A B C Sf pf ptp) (gtAdGd GT) n0 HL Himgc Hn0
      Himgn)
    (xv6Hok GT HconsT Hcl)
  obtain ⟨wA, wB, HpA, HpB, HsA, HsB, Hne⟩ := HP
  exact ⟨HsA, HsB, fun _ _ =>
    ⟨AxSpinT2b.pidNe _ _ wA wB HpA HpB Hne, wA, wB, HpA, HpB, Hne⟩⟩

/-! # 3. THEOREM 1, the corollary with an empty-row C -/

/-- (Lean-only) `f` with its value at `C` overridden. -/
def AxSpinT2b.over {α : Type} (C : Agent) (a : α) (f : Agent → α) : Agent → α :=
  fun i => if i = C then a else f i

theorem AxSpinT2b.overSelf {α : Type} (C : Agent) (a : α) (f : Agent → α) :
    AxSpinT2b.over C a f C = a := if_pos rfl

theorem AxSpinT2b.overNe {α : Type} (C : Agent) (a : α) (f : Agent → α) (i : Agent) (h : i ≠ C) :
    AxSpinT2b.over C a f i = f i := if_neg h

section thm1
open Iris.Std.PartialMap

/-- C's WPd for an EMPTY row: post `True` from any program state at position 0
(`AxSpinApA.wpdEndAnn` with no annotations). -/
theorem AxSpinT2b.wpdEmpty [Hinv : InvGS_gen .hasNoLC AxSpinX7.xv6GF]
    [Hann : AxannotGS AxSpinX7.xv6GF] (L : Xlay) (GT : GdexecT) (nm : Xv6N) (C : Agent)
    (HrowC : AxOpsem.grow (gtAdGd GT) C = []) (pr : Pexv6) (P : IProp AxSpinX7.xv6GF) :
    ⊢ P -∗ @tierAWpd AxSpinX7.xv6GF .hasNoLC _ _ (xv6Pol GT) (gtAdGd GT) Xv6N Unit
      (protXv6 L) nm ⟨pr, 0⟩ .MaybeStuck C (fun _ => iprop(True)) := by
  have Hm : ∀ e, e ∈ (FiniteMap.dom_set (∅ : Mea AxSpinX7.xv6GF) : GSet Geid) → e.1 = C := by
    intro e he
    rw [domEmpty] at he
    exact absurd he (fun h' => (elemOfEmpty (S := GSet Geid)).1 h')
  have W := AxSpinApA.wpdEndAnn (hlc := .hasNoLC) (GF := AxSpinX7.xv6GF) L GT nm C 0
    (by rw [HrowC]; exact Nat.le_refl _) ∅ Hm (fun _ => iprop(True))
    (fun _ => by iintro -; itrivial)
  unfold tierAWpd
  iintro -
  ihave W := W $$ []
  · iapply BigSepM.bigSepM_empty.2
    itrivial
  iapply W

end thm1

set_option maxHeartbeats 800000 in
/-- **THEOREM 1 (`allocpid2Distinct`)** — two harts A, B run the inlined allocpid; nobody else
emits events.  The corollary of `allocpidOpen` with a phantom third hart C whose row is empty
(its run is empty, its `HwpC` is `AxSpinT2b.wpdEmpty`).  Same premises as Theorem 2 minus C's,
same conclusion. -/
theorem allocpid2Distinct (GT : GdexecT) (A B C : Agent) (Sf pf : Agent → Int)
    (ptp : Int → Prop) (qA qB : T2Prm) (σi : ExecSt) (T : PTree) (satp0 : BitVec 64) (n0 : Int)
    (s0 sN : Agent → Athread) (n : Agent → Nat)
    -- MODEL: the tagged graph is riscv.cat-consistent
    (HconsT : rvwmoCatConsistentT GT)
    -- MODEL: control dependencies are closed
    (Hcl : ctrlClosed GT)
    -- SCOPE: only A and B emit memory events
    (Hharts : ∀ e, e ∈ GT.gtG.gxGmo → e.1 ∈ [A, B])
    -- SCOPE: the phantom third hart C of the layout has an empty row
    (HrowC : AxOpsem.grow (gtAdGd GT) C = [])
    -- LAYOUT: as Theorem 2 (C's slot / stack window are reserved, never used)
    (HLay : T2LayHyp A B C Sf pf ptp)
    (HalA : Sf A % 16 = 0) (HalB : Sf B % 16 = 0)
    -- IMAGE: `lk->cpu` = 0, nextpid = `n0`
    (Himgc : ∀ a, a ∈ clb (xlayXv6 A B C Sf pf ptp) → GT.gtG.gxImg a = some b0)
    (Hn0 : 0 ≤ n0 ∧ n0 < 2 ^ 32)
    (Himgn : ∀ (j : Nat) a v, (npb (xlayXv6 A B C Sf pf ptp))[j]? = some a →
      (WeakInterpProj.wbytes 4 (BitVec.ofInt 32 n0))[j]? = some v → GT.gtG.gxImg a = some v)
    -- TEXT: as Theorem 2
    (Htxa : acquireText σi T) (Htxm : mycpuText σi T) (Htxp : pushOffText σi T)
    (Htxh : holdingText σi T) (Htxq : popOffText σi T) (Htxr : releaseText σi T)
    (Htxc : allocpidText σi T) (Htxt : AxSpinApA.tailText σi T)
    (HfixA : textFixed (gtAdGd GT) A (imgS σi)) (HfixB : textFixed (gtAdGd GT) B (imgS σi))
    -- TRANSLATION: as Theorem 2
    (hmode : _get_Satp64_Mode (Mk_Satp64 satp0) = 8#4)
    (hasid : zero_extend (m := 16) (satp_to_asid satp0) = 0#16)
    (hppn : BitVec.setWidth 44 (satp_to_ppn satp0) = T.base)
    (HmapA : AxSpinApA.MapOk σi T A (Sf A) (pf A)) (HmapB : AxSpinApA.MapOk σi T B (Sf B) (pf B))
    -- ROWS and PINS: as Theorem 2 (verbatim in the header)
    (HfullA : allocFull (AxOpsem.grow (gtAdGd GT) A) qA A (Sf A) (pf A))
    (HfullB : allocFull (AxOpsem.grow (gtAdGd GT) B) qB B (Sf B) (pf B))
    (HpinsA : AllocPins (gtAdGd GT) A qA) (HpinsB : AllocPins (gtAdGd GT) B qB)
    -- ENTRY: as Theorem 2
    (HentA : entryOk T satp0 A (Sf A) (pf A) (s0 A))
    (HentB : entryOk T satp0 B (Sf B) (pf B) (s0 B))
    -- RUN: A's and B's runs, whole rows, stopped at instruction boundaries
    (Hrun : ∀ (_ : AxannotGS AxSpinX7.xv6GF) (nm : Xv6N) i, i ∈ [A, B] →
      nsteps (tierAAstep (gtAdGd GT) nm i) (n i) (s0 i) (sN i))
    (Hend : ∀ i, i ∈ [A, B] → (sN i).atK = (AxOpsem.grow (gtAdGd GT) i).length)
    (HfinA : ¬ midState (sN A)) (HfinB : ¬ midState (sN B)) :
    npSrc (gtAdGd GT).gdG (xlayXv6 A B C Sf pf ptp) (A, t2KBd qA) (A, t2KA qA) ∧
    npSrc (gtAdGd GT).gdG (xlayXv6 A B C Sf pf ptp) (B, t2KBd qB) (B, t2KA qB) ∧
    (t2Complete (gtAdGd GT) A (Sf A) (pf A) → t2Complete (gtAdGd GT) B (Sf B) (pf B) →
      pidOf (gtAdGd GT) A qA ≠ pidOf (gtAdGd GT) B qB ∧
      ∃ wA wB : BitVec 32,
        pidOf (gtAdGd GT) A qA = some (WeakInterpProj.wbytes 4 wA) ∧
        pidOf (gtAdGd GT) B qB = some (WeakInterpProj.wbytes 4 wB) ∧ wA ≠ wB) := by
  obtain ⟨hAB, hAC, hBC⟩ := AxSpinT2b.distinct HLay
  -- C's (empty) run: it starts and ends at position 0 and takes no step
  let sC : Athread := ⟨(s0 A).atP, 0⟩
  have Hharts3 : ∀ e, e ∈ GT.gtG.gxGmo → e.1 ∈ [A, B, C] := by
    intro e He
    have h := Hharts e He
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢
    rcases h with h | h
    · exact .inl h
    · exact .inr (.inl h)
  have Hrun3 : ∀ (_ : AxannotGS AxSpinX7.xv6GF) (nm : Xv6N) i, i ∈ [A, B, C] →
      nsteps (tierAAstep (gtAdGd GT) nm i) (AxSpinT2b.over C 0 n i) (AxSpinT2b.over C sC s0 i)
        (AxSpinT2b.over C sC sN i) := by
    intro Hann nm i Hi
    rcases AxSpinT2b.mem3 Hi with rfl | rfl | rfl
    · rw [AxSpinT2b.overNe _ _ _ _ hAC, AxSpinT2b.overNe _ _ _ _ hAC,
        AxSpinT2b.overNe _ _ _ _ hAC]
      exact Hrun Hann nm _ (by simp)
    · rw [AxSpinT2b.overNe _ _ _ _ hBC, AxSpinT2b.overNe _ _ _ _ hBC,
        AxSpinT2b.overNe _ _ _ _ hBC]
      exact Hrun Hann nm _ (by simp)
    · rw [AxSpinT2b.overSelf, AxSpinT2b.overSelf, AxSpinT2b.overSelf]
      exact nsteps_O _
  have Hend3 : ∀ i, i ∈ [A, B, C] →
      (AxSpinT2b.over C sC sN i).atK = (AxOpsem.grow (gtAdGd GT) i).length := by
    intro i Hi
    rcases AxSpinT2b.mem3 Hi with rfl | rfl | rfl
    · rw [AxSpinT2b.overNe _ _ _ _ hAC]
      exact Hend _ (by simp)
    · rw [AxSpinT2b.overNe _ _ _ _ hBC]
      exact Hend _ (by simp)
    · rw [AxSpinT2b.overSelf, HrowC]
      rfl
  have HwpC : ∀ [InvGS_gen .hasNoLC AxSpinX7.xv6GF] [AxannotGS AxSpinX7.xv6GF] (nm : Xv6N),
      ⊢ xv6Init (xlayXv6 A B C Sf pf ptp) (gtAdGd GT) nm C -∗
        @tierAWpd AxSpinX7.xv6GF .hasNoLC _ _ (xv6Pol GT) (gtAdGd GT) Xv6N Unit
          (protXv6 (xlayXv6 A B C Sf pf ptp)) nm (AxSpinT2b.over C sC s0 C) .MaybeStuck C
          (fun _ => iprop(True)) := by
    intro Hinv Hann nm
    rw [AxSpinT2b.overSelf]
    exact AxSpinT2b.wpdEmpty (xlayXv6 A B C Sf pf ptp) GT nm C HrowC (s0 A).atP _
  exact allocpidOpen GT A B C Sf pf ptp qA qB σi T satp0 n0 (AxSpinT2b.over C sC s0)
    (AxSpinT2b.over C sC sN) (AxSpinT2b.over C 0 n) HconsT Hcl Hharts3 HLay HalA HalB Himgc Hn0
    Himgn Htxa Htxm Htxp Htxh Htxq Htxr Htxc Htxt HfixA HfixB hmode hasid hppn HmapA HmapB
    HfullA HfullB HpinsA HpinsB
    (by rw [AxSpinT2b.overNe _ _ _ _ hAC]; exact HentA)
    (by rw [AxSpinT2b.overNe _ _ _ _ hBC]; exact HentB)
    (by rw [AxSpinT2b.overSelf])
    Hrun3 Hend3
    (by rw [AxSpinT2b.overNe _ _ _ _ hAC]; exact HfinA)
    (by rw [AxSpinT2b.overNe _ _ _ _ hBC]; exact HfinB)
    HwpC

end Weak
