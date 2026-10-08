/-
Weak: THEOREM 2's NEGATIVE CERTIFICATES — the protocol, not the framework, refuses an unlocked
nextpid racer (`allocpidRaceUnprovable`, certificate (b-np)) while the same racer IS verifiable at
the trivial protocol (`allocpidRaceTrivial`, the sanity twin (c′)).  Theorem 2 design
(`notes/weak-lb-thm2-design.md`) §A.4, §C.6, §D row `AxSpinT2d`; owner ruling Q-T2-3 (b-np is
certificate (b); the bogus-release racer (b-lk) is a stretch).  NEW Lean file (no Rocq source).
Templates: `AxSpinJ2.ur3WpdUnprovable` / `ur3WpdTrivial`, `AxSpinU4.urNotSrc` /
`urWpdUnprovable` / `wpdRNTriv`.

## What this file proves

THE RACER (hart C).  `AxSpinT2d.rcM0` = a hand-node program (`Pexv6` `hp`, as every racer of the
templates) `ldk 4 nextpid (fun v => stv 4 nextpid (v + 1) hlt)` — the memory skeleton of
`lw a5, nextpid; addiw a5, a5, 1; sw a5, nextpid` with NO lock acquire (the `addiw` is the
register-only `v + one32` between the two memory events; a hand node has no fetch/decode, which
under Stage C are not graph events anyway).  Its row `AxSpinT2d.rcRow ts w` = the nextpid load
(per-byte sources `ts`, value `w`) then the plain store of `w + 1`.  `AxSpinT2d.rcRun`: its run
(2 steps, row consumed).

**(b-np) `allocpidRaceUnprovable`.**  On EVERY graph satisfying all of `allocpidOpen`'s premises
for A and B (verbatim, minus C's) with C's row the racer's (`HrowC`) and the RACE SHAPE
  `HrfB : grfAt G (paZ nextpid) (C, 1) (B, t2KBd qB)`   — B's nextpid read sources C's store
  `HltB : gmoLt G (B, t2KA qB) (C, 1)`                — C's store is gmo-AFTER B's lock claim
C's WPd at `Ixv6` is NOT provable:
  `¬ (∀ Hinv Hann nm, ⊢ xv6Init L GD nm C -∗ WPd_{protXv6 L} ⟨hp cpu0 rcM0 zeroRegs, 0⟩ {{True}})`.
Proof: reductio THROUGH `allocpidOpen` (C's `Hk0`/`Hrun`/`Hend` are DERIVED from `HrowC` by
`rcRun`, not assumed); its first-B conjunct `npSrc G L (B, t2KBd qB) (B, t2KA qB)` contradicts the
race shape (`AxSpinT2d.raceNotSrc`: the read's source is neither the image, nor the anchor, nor
gmo-before it — gmo is asymmetric).

**(c′) `allocpidRaceTrivial`.**  For every graph with C's row the racer's, the SAME program at the
SAME start state, policy `xv6Pol GT`, functors `xv6GF`, post `True` IS provable at the trivial
protocol `trivOb` (`AxSpinT2d.wpdRcTriv`: `nshRead` + `nshWrite` + `evPlain`/`feTrivu` +
`shHltTrue`).  So what refuses C in (b-np) is `protXv6`'s ownership of nextpid (writes only under
the lock), not the WPd framework or the racer's run.

## HONESTY: what (b-np) does and does not establish

`allocpidRaceUnprovable` is a REDUCTIO OVER AN ABSTRACT GRAPH: its premises are `allocpidOpen`'s
for A and B plus `HrowC`/`HrfB`/`HltB`.  It is NON-VACUOUS only once a concrete `GT` satisfying
them all is exhibited; that concrete full-segment 3-hart run is built by the parallel certificate
worker (`AxSpinT2c*`, design §C.6 (a′)) — this file does NOT build it (A's and B's rows are the
≈ 150-item `allocFull` rows of real S-mode xv6 code, which need the warm-started tracer).  WHAT
THE CERTIFICATE MUST SUPPLY (= the (a′) run with C replaced by the racer):
  1. a `GT` with `rvwmoCatConsistentT`, `ctrlClosed`, `gmo` harts ⊆ [A, B, C], the layout
     (`T2LayHyp`, 16-aligned frames), the image (`lk->cpu` = 0, nextpid = `n0`), the text /
     translation / `MapOk` / `textFixed` premises, A's and B's `allocFull` rows + `AllocPins`,
     `entryOk` starts, runs `Hrun`/`Hend`/`¬ midState` for A and B — exactly as (a′);
  2. C's row `= AxSpinT2d.rcRow ts w` (C runs `rcM0` from `⟨hp cpu0 rcM0 zeroRegs, 0⟩`; its run is
     supplied here);
  3. the race: in `gmo`, C's store `(C, 1)` after B's claim `(B, t2KA qB)` and B's nextpid load
     `(B, t2KBd qB)` reads byte `paZ nextpid` from it.  A consistent schedule: A runs its segment
     (nextpid `n0 → n0 + 1`), B claims A's release, C reads A's `n0 + 1` and stores `n0 + 2`, B
     reads `n0 + 2`, scans (no collision: the slots hold image pids and A's `n0 + 1`), stores
     `n0 + 3`.  B's pins `npNowrap`/`npNcoll` then hold for `n0 + 2` (n0 + 3 < 1000, image pids
     ≠ n0 + 2), so the race is INSIDE the theorem's scope (design §A.4, (b-np)), and `pidOf A =
     n0 + 1 ≠ n0 + 2 = pidOf B` — distinctness survives this racer (the collision scan defends
     it, §A.4); only `npSrc` is refuted.
(b-lk) — the bogus-release racer that falsifies `pidOf A ≠ pidOf B` itself — is NOT done (owner
stretch; it needs the concrete concurrent-entry graph, which is the same T2c machinery).

## The audit (design §C.6 (d))

`allocpidOpen`/`allocpid2Distinct` are registered with the assumption audit as a SEPARATE Weak
target: `tools/ci/roots-weak.txt` + `tools/audit/baseline-weak.json` (lint checks the two lists
agree), run by `tools/ci/audit.sh --weak` (`Audit.lean` imports `$XV6_AUDIT_MODULES`, here
`Weak.AxSpinT2b`).  Baseline (PASSING, 2026-10-08): axioms exactly `propext`,
`Classical.choice`, `Quot.sound` + 18 `bv_decide` certificates; opaques `xv6_resv_is_valid`,
`xv6_resv_matches` (the LR/SC reservation parameters, as the Xv6 roots); cone ≈ 29.4k constants;
the run takes ≈ 1.5 s on the VM (the default Xv6/MachCSL audit: ≈ 17 s, unchanged).  NOT in
`tools/ci/roots.txt`/`baseline.json`: those are also read by `tools/ci/envfacts` (the Xv6+MachCSL
coverage / dead-code cone, which fails on a root it cannot find) and by CI, which builds only
`Xv6 MachCSL` — a Weak root there would need CI to build Weak's cone, the expensive part.
GREP ACCEPTANCE (design §D (iii)): in `allocpidOpen`'s binder list (AxSpinT2b) the only binder
mentioning `⊢`/`IProp`/`iprop`/`tierAWpd` is `HwpC` (checked by `grep` over the signature, lines
251–312 of AxSpinT2b at the time of writing); `allocpid2Distinct` has none.

**Reused** (by name): `allocpidOpen`, `AxSpinT2b.over`/`overSelf`/`overNe`/`mem3`/`distinct`
(AxSpinT2b), `t2KBd`/`t2KA`/`xlayXv6`/`T2LayHyp` (AxSpinT2a), `npSrc`/`npb` (AxSpinU/AxSpinX),
`AxSpinX4.ldkRun`, `nrunWrite`, `nshRead`, `nshWrite`, `advLoad`, `evPlain`,
`feTrivu`, `shHltTrue`, `inClr`, `wordOfBytesWbytes`, `gxLblGrow`, `nsteps_l`/`nsteps_O`.

**Lean-only declarations**: `allocpidRaceUnprovable`, `allocpidRaceTrivial` (grepped absent);
helpers `AxSpinT2d.*`.
-/
import Weak.AxSpinT2b
import Weak.AxSpinJ2

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D LeanRV64D.Functions

/-! # 1. The racer: `lw; addiw; sw nextpid`, no lock -/

/-- xv6's `nextpid` (0x8000a384) as a physical address. -/
def AxSpinT2d.nppaX : PAddr := zPa 0x8000a384

theorem AxSpinT2d.nppaXRam : devAddr AxSpinT2d.nppaX = false := by decide +kernel

theorem AxSpinT2d.nppaXZ : paZ AxSpinT2d.nppaX = AxSpinT2a.zNp := by decide +kernel

/-- The racer's continuation after its load: `addiw` then `sw`. -/
abbrev AxSpinT2d.rcInc (v : BitVec 32) : SailM Unit := stv 4 AxSpinT2d.nppaX (v + one32) hlt

/-- The racer: `lw a5, nextpid; addiw a5, a5, 1; sw a5, nextpid` — no acquire. -/
abbrev AxSpinT2d.rcM0 : SailM Unit := ldk 4 AxSpinT2d.nppaX AxSpinT2d.rcInc

/-- The racer's row: the nextpid load (sources `ts`, value `w`), the plain store of `w + 1`. -/
def AxSpinT2d.rcRow (ts : List Nat) (w : BitVec 32) : List Lbl :=
  [.LLoad false (paZ AxSpinT2d.nppaX) ts (WeakInterpProj.wbytes 4 w),
   .LStore false (paZ AxSpinT2d.nppaX) (WeakInterpProj.wbytes 4 (w + one32)) .WCplain]

/-- The racer's run on its row. -/
theorem AxSpinT2d.rcRun (cpu : CPU) (GD : Gdexec) (i : Agent) (ts : List Nat) (w : BitVec 32)
    (Hrow : AxOpsem.grow GD i = AxSpinT2d.rcRow ts w) :
    nsteps (astepAnyNfGv GD i) 2 ⟨hp cpu AxSpinT2d.rcM0 zeroRegs, 0⟩ ⟨hp cpu hlt zeroRegs, 2⟩ := by
  refine nsteps_l (AxSpinX4.ldkRun cpu GD i 4 AxSpinT2d.nppaX AxSpinT2d.nppaXRam ts w
    AxSpinT2d.rcInc zeroRegs 0 (by rw [Hrow]; rfl)) ?_
  refine nsteps_l (nrunWrite cpu GD i 4 (by decide) AxSpinT2d.nppaX AxSpinT2d.nppaXRam
    (w + one32) hlt zeroRegs 1 .WCplain (by rw [Hrow]; rfl)) ?_
  exact nsteps_O _

/-! # 2. The race refutes `npSrc` -/

/-- A read of a nextpid byte sourced by a write `w` that is not the anchor `e` and is gmo-AFTER
it violates `npSrc`. -/
theorem AxSpinT2d.raceNotSrc (G : Gexec) (L : Xlay) (r e w : Geid) (a : Int) (Ha : a ∈ npb L)
    (Hrf : grfAt G a w r) (Hne : w ≠ e) (Hlt : gmoLt G e w) : ¬ npSrc G L r e := by
  intro Hs
  obtain ⟨t, v, Hrd, Hwa⟩ := Hrf
  rcases Hs a Ha t v Hrd with H0 | ⟨w', Hga, Hw | Hlt'⟩
  · subst H0
    simp [gwriteAt] at Hwa
  · rw [Hwa] at Hga
    obtain rfl := Option.some.inj Hga
    exact Hne Hw
  · rw [Hwa] at Hga
    obtain rfl := Option.some.inj Hga
    obtain ⟨-, -, h1⟩ := Hlt
    obtain ⟨-, -, h2⟩ := Hlt'
    omega

/-- nextpid's first byte is a nextpid byte of the real layout. -/
theorem AxSpinT2d.npMem (A B C : Agent) (Sf pf : Agent → Int) (ptp : Int → Prop) :
    paZ AxSpinT2d.nppaX ∈ npb (xlayXv6 A B C Sf pf ptp) := by
  unfold npb
  rw [inClr, AxSpinT2d.nppaXZ]
  show AxSpinT2a.zNp ≤ AxSpinT2a.zNp ∧ AxSpinT2a.zNp < AxSpinT2a.zNp + ((4 : Nat) : Int)
  omega

/-! # 3. (b-np): C's WPd is unprovable at `Ixv6` -/

set_option maxHeartbeats 800000 in
/-- **CERTIFICATE (b-np), `allocpidRaceUnprovable`.**  On any graph satisfying every premise of
`allocpidOpen` for A and B, where C's row is the unlocked racer's and C's nextpid store lands
gmo-after B's claim and sources B's nextpid read, the racer's WPd at the joint xv6 protocol is
NOT provable.  (Reductio over an abstract graph: see the header for what a concrete witness must
supply.) -/
theorem allocpidRaceUnprovable (GT : GdexecT) (A B C : Agent) (Sf pf : Agent → Int)
    (ptp : Int → Prop) (qA qB : T2Prm) (σi : ExecSt) (T : PTree) (satp0 : BitVec 64) (n0 : Int)
    (s0 sN : Agent → Athread) (n : Agent → Nat) (tsC : List Nat) (wC : BitVec 32)
    -- `allocpidOpen`'s premises, verbatim (AxSpinT2b), minus C's `HkC`/`Hrun`/`Hend`/`HwpC`
    (HconsT : rvwmoCatConsistentT GT) (Hcl : ctrlClosed GT)
    (Hharts : ∀ e, e ∈ GT.gtG.gxGmo → e.1 ∈ [A, B, C])
    (HLay : T2LayHyp A B C Sf pf ptp) (HalA : Sf A % 16 = 0) (HalB : Sf B % 16 = 0)
    (Himgc : ∀ a, a ∈ clb (xlayXv6 A B C Sf pf ptp) → GT.gtG.gxImg a = some b0)
    (Hn0 : 0 ≤ n0 ∧ n0 < 2 ^ 32)
    (Himgn : ∀ (j : Nat) a v, (npb (xlayXv6 A B C Sf pf ptp))[j]? = some a →
      (WeakInterpProj.wbytes 4 (BitVec.ofInt 32 n0))[j]? = some v → GT.gtG.gxImg a = some v)
    (Htxa : acquireText σi T) (Htxm : mycpuText σi T) (Htxp : pushOffText σi T)
    (Htxh : holdingText σi T) (Htxq : popOffText σi T) (Htxr : releaseText σi T)
    (Htxc : allocpidText σi T) (Htxt : AxSpinApA.tailText σi T)
    (HfixA : textFixed (gtAdGd GT) A (imgS σi)) (HfixB : textFixed (gtAdGd GT) B (imgS σi))
    (hmode : _get_Satp64_Mode (Mk_Satp64 satp0) = 8#4)
    (hasid : zero_extend (m := 16) (satp_to_asid satp0) = 0#16)
    (hppn : BitVec.setWidth 44 (satp_to_ppn satp0) = T.base)
    (HmapA : AxSpinApA.MapOk σi T A (Sf A) (pf A)) (HmapB : AxSpinApA.MapOk σi T B (Sf B) (pf B))
    (HfullA : allocFull (AxOpsem.grow (gtAdGd GT) A) qA A (Sf A) (pf A))
    (HfullB : allocFull (AxOpsem.grow (gtAdGd GT) B) qB B (Sf B) (pf B))
    (HpinsA : AllocPins (gtAdGd GT) A qA) (HpinsB : AllocPins (gtAdGd GT) B qB)
    (HentA : entryOk T satp0 A (Sf A) (pf A) (s0 A))
    (HentB : entryOk T satp0 B (Sf B) (pf B) (s0 B))
    (Hrun : ∀ (_ : AxannotGS AxSpinX7.xv6GF) (nm : Xv6N) i, i ∈ [A, B] →
      nsteps (tierAAstep (gtAdGd GT) nm i) (n i) (s0 i) (sN i))
    (Hend : ∀ i, i ∈ [A, B] → (sN i).atK = (AxOpsem.grow (gtAdGd GT) i).length)
    (HfinA : ¬ midState (sN A)) (HfinB : ¬ midState (sN B))
    -- C IS THE RACER: its row is `lw nextpid; sw nextpid ← +1`
    (HrowC : AxOpsem.grow (gtAdGd GT) C = AxSpinT2d.rcRow tsC wC)
    -- THE RACE: B's nextpid read sources C's store, which is gmo-after B's claim
    (HrfB : grfAt (gtAdGd GT).gdG (paZ AxSpinT2d.nppaX) (C, 1) (B, t2KBd qB))
    (HltB : gmoLt (gtAdGd GT).gdG (B, t2KA qB) (C, 1)) :
    ¬ (∀ [InvGS_gen .hasNoLC AxSpinX7.xv6GF] [AxannotGS AxSpinX7.xv6GF] (nm : Xv6N),
        ⊢ xv6Init (xlayXv6 A B C Sf pf ptp) (gtAdGd GT) nm C -∗
          @tierAWpd AxSpinX7.xv6GF .hasNoLC _ _ (xv6Pol GT) (gtAdGd GT) Xv6N Unit
            (protXv6 (xlayXv6 A B C Sf pf ptp)) nm ⟨hp cpu0 AxSpinT2d.rcM0 zeroRegs, 0⟩
            .MaybeStuck C (fun _ => iprop(True))) := by
  intro HwpC
  obtain ⟨hAB, hAC, hBC⟩ := AxSpinT2b.distinct HLay
  let sC0 : Athread := ⟨hp cpu0 AxSpinT2d.rcM0 zeroRegs, 0⟩
  let sCN : Athread := ⟨hp cpu0 hlt zeroRegs, 2⟩
  have Hrun3 : ∀ (_ : AxannotGS AxSpinX7.xv6GF) (nm : Xv6N) i, i ∈ [A, B, C] →
      nsteps (tierAAstep (gtAdGd GT) nm i) (AxSpinT2b.over C 2 n i) (AxSpinT2b.over C sC0 s0 i)
        (AxSpinT2b.over C sCN sN i) := by
    intro Hann nm i Hi
    rcases AxSpinT2b.mem3 Hi with rfl | rfl | rfl
    · rw [AxSpinT2b.overNe _ _ _ _ hAC, AxSpinT2b.overNe _ _ _ _ hAC,
        AxSpinT2b.overNe _ _ _ _ hAC]
      exact Hrun Hann nm _ (by simp)
    · rw [AxSpinT2b.overNe _ _ _ _ hBC, AxSpinT2b.overNe _ _ _ _ hBC,
        AxSpinT2b.overNe _ _ _ _ hBC]
      exact Hrun Hann nm _ (by simp)
    · rw [AxSpinT2b.overSelf, AxSpinT2b.overSelf, AxSpinT2b.overSelf]
      exact AxSpinT2d.rcRun cpu0 (gtAdGd GT) _ tsC wC HrowC
  have Hend3 : ∀ i, i ∈ [A, B, C] →
      (AxSpinT2b.over C sCN sN i).atK = (AxOpsem.grow (gtAdGd GT) i).length := by
    intro i Hi
    rcases AxSpinT2b.mem3 Hi with rfl | rfl | rfl
    · rw [AxSpinT2b.overNe _ _ _ _ hAC]
      exact Hend _ (by simp)
    · rw [AxSpinT2b.overNe _ _ _ _ hBC]
      exact Hend _ (by simp)
    · rw [AxSpinT2b.overSelf, HrowC]
      rfl
  have HwpC' : ∀ [InvGS_gen .hasNoLC AxSpinX7.xv6GF] [AxannotGS AxSpinX7.xv6GF] (nm : Xv6N),
      ⊢ xv6Init (xlayXv6 A B C Sf pf ptp) (gtAdGd GT) nm C -∗
        @tierAWpd AxSpinX7.xv6GF .hasNoLC _ _ (xv6Pol GT) (gtAdGd GT) Xv6N Unit
          (protXv6 (xlayXv6 A B C Sf pf ptp)) nm (AxSpinT2b.over C sC0 s0 C) .MaybeStuck C
          (fun _ => iprop(True)) := by
    intro Hinv Hann nm
    rw [AxSpinT2b.overSelf]
    exact HwpC nm
  obtain ⟨-, HsB, -⟩ := allocpidOpen GT A B C Sf pf ptp qA qB σi T satp0 n0
    (AxSpinT2b.over C sC0 s0) (AxSpinT2b.over C sCN sN) (AxSpinT2b.over C 2 n) HconsT Hcl Hharts
    HLay HalA HalB Himgc Hn0 Himgn Htxa Htxm Htxp Htxh Htxq Htxr Htxc Htxt HfixA HfixB hmode
    hasid hppn HmapA HmapB HfullA HfullB HpinsA HpinsB
    (by rw [AxSpinT2b.overNe _ _ _ _ hAC]; exact HentA)
    (by rw [AxSpinT2b.overNe _ _ _ _ hBC]; exact HentB)
    (by rw [AxSpinT2b.overSelf])
    Hrun3 Hend3
    (by rw [AxSpinT2b.overNe _ _ _ _ hAC]; exact HfinA)
    (by rw [AxSpinT2b.overNe _ _ _ _ hBC]; exact HfinB)
    HwpC'
  exact AxSpinT2d.raceNotSrc (gtAdGd GT).gdG (xlayXv6 A B C Sf pf ptp) (B, t2KBd qB) (B, t2KA qB)
    (C, 1) (paZ AxSpinT2d.nppaX) (AxSpinT2d.npMem A B C Sf pf ptp) HrfB
    (fun h => hBC (congrArg Prod.fst h).symm) HltB HsB

/-! # 4. (c′): the SAME racer at the trivial protocol -/

section rcTriv
variable {hlc : HasLC} {GF : BundledGFunctors.{0,0,0}} [InvGS_gen hlc GF] [AxannotGS GF]

/-- The racer's store and halt, from any loaded value `x` whose increment is the row's store. -/
theorem AxSpinT2d.wpdRcStore (GT : GdexecT) (cpu : CPU) (i : Agent) (ts : List Nat)
    (w : BitVec 32) (Hrow : AxOpsem.grow (gtAdGd GT) i = AxSpinT2d.rcRow ts w) (x : BitVec 32)
    (Hx : x = w) :
    ⊢ (iprop(True) : IProp GF) -∗ ∀ rs : RegFile,
      @tierAWpd GF hlc _ _ (xv6Pol GT) (gtAdGd GT) Unit Unit trivOb ()
        ⟨hp cpu (AxSpinT2d.rcInc x) rs, 1⟩ .MaybeStuck i (fun _ => iprop(True)) := by
  subst Hx
  have Hne : 1 ≠ (AxOpsem.grow (gtAdGd GT) i).length := by rw [Hrow]; simp [AxSpinT2d.rcRow]
  have Hl1 : gxLbl (gtAdGd GT).gdG (i, 1) = some (.LStore false (paZ AxSpinT2d.nppaX)
      (WeakInterpProj.wbytes 4 (x + one32)) .WCplain) := by
    rw [gxLblGrow, Hrow]; rfl
  exact nshWrite (hlc := hlc) (GF := GF) (pol := xv6Pol GT) (gtAdGd GT) Unit Unit trivOb ()
    cpu i (fun _ => iprop(True)) 4 AxSpinT2d.nppaX AxSpinT2d.nppaXRam (x + one32) hlt 1 Hne
    iprop(True)
    (fun rs => by
      have Hval : graphData (gtAdGd GT) (i, 1) =
          some (WeakInterpProj.wbytes 4 (x + one32)) := by
        unfold graphData; rw [Hl1]; rfl
      iintro _
      iapply (evPlain (hlc := hlc) (pol := xv6Pol GT) (gtAdGd GT) Unit Unit trivOb () i 1
        iprop(True) iprop(True) _ _ Hval) $$ []
      · iapply feTrivu
      iintro _ _
      iapply (shHltTrue (hlc := hlc) (pol := xv6Pol GT) (gtAdGd GT) Unit Unit trivOb () cpu i
        (1 + 1)) $$ %rs)

/-- The racer's WPd at the trivial protocol. -/
theorem AxSpinT2d.wpdRcTriv (GT : GdexecT) (cpu : CPU) (i : Agent) (ts : List Nat)
    (w : BitVec 32) (Hrow : AxOpsem.grow (gtAdGd GT) i = AxSpinT2d.rcRow ts w) :
    ⊢ @tierAWpd GF hlc _ _ (xv6Pol GT) (gtAdGd GT) Unit Unit trivOb ()
      ⟨hp cpu AxSpinT2d.rcM0 zeroRegs, 0⟩ .MaybeStuck i (fun _ => iprop(True)) := by
  have Hne : 0 ≠ (AxOpsem.grow (gtAdGd GT) i).length := by rw [Hrow]; simp [AxSpinT2d.rcRow]
  have Hl0 : (AxOpsem.grow (gtAdGd GT) i)[0]? = some (.LLoad false (paZ AxSpinT2d.nppaX) ts
      (WeakInterpProj.wbytes 4 w)) := by
    rw [Hrow]; rfl
  have H := nshRead (hlc := hlc) (GF := GF) (pol := xv6Pol GT) (gtAdGd GT) Unit Unit trivOb ()
    cpu i (fun _ => iprop(True)) 4 (by decide) AxSpinT2d.nppaX AxSpinT2d.nppaXRam
    (AxSpinX4.ldkK 4 AxSpinT2d.rcInc) 0 Hne
    (advLoad (gtAdGd GT) i 0 false _ ts _ Hl0) iprop(True)
    (fun v rs Hgv => by
      have Hv : v = WeakInterpProj.wbytes 4 w := by
        have Hgv' := Hgv
        unfold graphValue at Hgv'
        rw [gxLblGrow, Hl0] at Hgv'
        simp only [Option.bind_some, lblValue, Option.some.injEq] at Hgv'
        exact Hgv'.symm
      have HS := AxSpinT2d.wpdRcStore (hlc := hlc) (GF := GF) GT cpu i ts w Hrow
        (wordOfBytes 4 v) (by rw [Hv, wordOfBytesWbytes])
      iintro _
      iapply (evPlain (hlc := hlc) (pol := xv6Pol GT) (gtAdGd GT) Unit Unit trivOb () i 0
        iprop(True) iprop(True) _ _ Hgv) $$ []
      · iapply feTrivu
      iintro _ _
      iapply HS $$ [] %rs
      itrivial)
  iapply H $$ [] %zeroRegs
  itrivial

end rcTriv

/-- **SANITY TWIN (c′), `allocpidRaceTrivial`.**  The racer of (b-np) — same program, same start
state, same row, same policy and functors, post `True` — IS verifiable at the trivial protocol. -/
theorem allocpidRaceTrivial (GT : GdexecT) (C : Agent) (tsC : List Nat) (wC : BitVec 32)
    (HrowC : AxOpsem.grow (gtAdGd GT) C = AxSpinT2d.rcRow tsC wC) :
    ∀ [InvGS_gen .hasNoLC AxSpinX7.xv6GF] [AxannotGS AxSpinX7.xv6GF] (nm : Unit),
      ⊢ (iprop(emp) : IProp AxSpinX7.xv6GF) -∗
        @tierAWpd AxSpinX7.xv6GF .hasNoLC _ _ (xv6Pol GT) (gtAdGd GT) Unit Unit trivOb nm
          ⟨hp cpu0 AxSpinT2d.rcM0 zeroRegs, 0⟩ .MaybeStuck C (fun _ => iprop(True)) := by
  intro _ _ nm
  cases nm
  iintro _
  iapply (AxSpinT2d.wpdRcTriv (hlc := .hasNoLC) (GF := AxSpinX7.xv6GF) GT cpu0 C tsC wC HrowC)

end Weak
