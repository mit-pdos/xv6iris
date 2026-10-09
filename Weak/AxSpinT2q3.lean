/-
Weak: **THEOREM 2, STAGE 2 / certificate pair (p-lk) / (p-triv): CONJUNCT 1 (NO PANIC) IS
LOAD-BEARING ON OWNERSHIP** — the lock-forging racer C of `AxSpinT2p2` (`sw 1, lk->locked; sd
cvx A, lk->cpu`, no acquire) has NO WPd against the joint xv6 protocol (`allocpidLkRaceUnprovable`,
reductio over an abstract graph; `allocpidLkRaceCert`, the concrete graph `AxSpinT2p2a.gLk`, NO
hypotheses), while the same racer IS verifiable at the trivial protocol (`allocpidLkRaceTrivial`,
`allocpidLkRaceTrivialLk`).

Lean-only (no Rocq source).  Stage-2 design `notes/weak-lb-thm2-stage2.md` §C rows (p-lk) /
(p-triv) (there named `AxSpinT2e2`/`AxSpinT2e3`, names taken by stage-1 modules), §D Q-S2-6 /
Q-S2-7, acceptance (iii), (vi).  Templates: `AxSpinT2d.allocpidRaceUnprovable` /
`allocpidRaceTrivial` (reductio + trivial twin), `AxSpinT2e3.allocpidRaceCert` (discharge).

## What this file proves

**(p-lk), abstract: `allocpidLkRaceUnprovable`.**  On EVERY graph satisfying all of
`allocpidOpen2`'s premises for A and B (verbatim, minus C's `HkC`/C's part of `Hrun`/`Hend` and
`HwpC`), with C's row the forging racer's (`HrowC : grow C = AxSpinT2p2.rcRow`) and A's row
CUT (`HcutA : t2Cut (gtAdGd GT) A (Sf A) (pf A)`):
  `¬ (∀ Hinv Hann nm, ⊢ xv6Init L GD nm C -∗ WPd_{protXv6 L} ⟨hp cpu0 rcM0 zeroRegs, 0⟩ {{True}})`.
Proof: C's run / row end / start position are DERIVED from `HrowC` (`AxSpinT2p2.rcRun`); apply
`allocpidOpen2`; its conjunct 1 gives `¬ t2Cut A`, contradicting `HcutA`.

**(p-lk), concrete: `allocpidLkRaceCert`** (NO hypotheses).  On `gLk` (AxSpinT2p2a: C forges the
lock word and `lk->cpu`, then A runs push_off + acquire's `holding`, takes the LONG arm, reads its
own cpu from C's `sd`, and its row ends at `c.bnez a0, panic` = `cutPos .aq qA2`; B is a phantom
with an empty row), every premise of `allocpidLkRaceUnprovable` is discharged: the bundle
`AxSpinT2p2a.cutCert` (`allocPre`/`AllocPins2` for A and B, `t2Cut A`, `HimgNoff`, A's `HsrcAl`
by `srcAl2`, `HrowC`), `catLk`/`ctrlLk`/`hartsLk`, `runLkA`/`runLkB`, image (`imgClb2`, nextpid
= 1 by `AxSpinT2c5.imgNp`), text (`AxSpinT2c5.*TextX`, `textFixed2`), translation
(`AxSpinT2pt.satpXFacts`, `AxSpinT2c5.mapOk3`), layout (`AxSpinT2c1.layHyp3`/`sZAl`), entry
(`AxSpinT2e3.entryR`), boundary (`AxSpinT2c1.finNotMid`); B's `HsrcAl` is vacuous (empty row,
`AxSpinT2q3.srcAlNil`).  So conjunct 1 of `allocpidOpen2` is NON-VACUOUS: a protocol-violating C
makes A enter the panic branch, and it is `HwpC` that rules this out.

**(p-triv): `allocpidLkRaceTrivial`.**  For every graph with C's row the racer's, the SAME
program at the SAME start state (policy `xv6Pol GT`, functors `xv6GF`, post `True`) IS provable
at `trivOb` (`AxSpinT2q3.wpdLkTriv`: two `nshWrite`s with `evPlain`/`feTrivu`, then
`shHltTrue`); `allocpidLkRaceTrivialLk` instantiates it at `gLk`, C = 2.  So what refuses C is
`protXv6`'s ownership of the lock word / `lk->cpu` (writes only by the claim holder), not the WPd
framework or the racer's run.

## Pins / honesty
* C is AxSpinT2p2's TWO-store racer (`AxSpinT2p2` header: the design's single `sd` cannot reach
  the `aq` cut, since holding's long arm needs a non-zero lock word).  C's start state
  `⟨hp cpu0 AxSpinT2p2.rcM0 zeroRegs, 0⟩` is verbatim in both halves of the pair.
* Inherited scope of the concrete graph: `AxSpinT2p2`/`AxSpinT2p2a`/`AxSpinT2pt`/`AxSpinT2c1`
  headers (kvmmake-shaped `tX`, warm TLB, image models text / page tables / nextpid).  Prefix
  closure stays informal (Q-S2-6, `AxSpinT2b2` header): the cut row is a covered execution.
* `allocpidOpen2`'s Q-S2-B premises `HsrcAlA`/`HsrcAlB` hold on `gLk` (proved, not assumed).
* No drive is re-run here: A's run comes from `AxSpinT2p2a.runLkA` (read-back of `chkA`).

Reused (by name): `allocpidOpen2` (AxSpinT2b2), `AxSpinT2b.over`/`overSelf`/`overNe`/`mem3`/
`distinct`, `AxSpinT2p2.rcM0`/`rcCpu`/`rcRow`/`rcRun`/`lkpaX`/`cpupaX`/`*Ram`/`imgClb2`/
`textFixed2`/`growB2`/`growC2`, `AxSpinT2p2a.*`, `AxSpinT2e3.entryR`, `AxSpinT2c5.*`,
`AxSpinT2c1.*`, `nshWrite`, `evPlain`, `feTrivu`, `shHltTrue`, `gxLblGrow`.
Names: Lean-only; `allocpidLkRaceUnprovable`, `allocpidLkRaceCert`, `allocpidLkRaceTrivial`,
`allocpidLkRaceTrivialLk` (grepped absent); helpers `Weak.AxSpinT2q3.*`.
-/
import Weak.AxSpinT2b2
import Weak.AxSpinT2p2a
import Weak.AxSpinT2e3

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D LeanRV64D.Functions
open AxSpinT2pt

/-! # 1. Helpers -/

/-- `clSrcAligned` at any position of an EMPTY row is vacuous (no read there). -/
theorem AxSpinT2q3.srcAlNil (GD : Gdexec) (Cl : List Int) (i k : Nat)
    (h : AxOpsem.grow GD i = []) : AxSpinT2g.clSrcAligned Cl GD.gdG (i, k) := by
  intro a t v w _ Hr
  obtain ⟨l, base, ts, vs, j, hl, -⟩ := Hr
  rw [gxLblGrow, h] at hl
  simp at hl

/-! # 2. (p-lk), abstract: the reductio through `allocpidOpen2` -/

set_option maxHeartbeats 800000 in
/-- **CERTIFICATE (p-lk), `allocpidLkRaceUnprovable`.**  On any graph satisfying every premise of
`allocpidOpen2` for A and B, where C's row is the lock-forging racer's and A's row is CUT (A enters
the panic / `intr_on` branch), the racer's WPd at the joint xv6 protocol is NOT provable. -/
theorem allocpidLkRaceUnprovable (GT : GdexecT) (A B C : Agent) (Sf pf : Agent → Int)
    (ptp : Int → Prop) (qA qB : T2Prm) (σi : ExecSt) (T : PTree) (satp0 : BitVec 64) (n0 : Int)
    (s0 sN : Agent → Athread) (n : Agent → Nat)
    -- `allocpidOpen2`'s premises, verbatim (AxSpinT2b2), minus C's `HkC`/`Hrun`/`Hend`/`HwpC`
    (HconsT : rvwmoCatConsistentT GT) (Hcl : ctrlClosed GT)
    (Hharts : ∀ e, e ∈ GT.gtG.gxGmo → e.1 ∈ [A, B, C])
    (HLay : T2LayHyp A B C Sf pf ptp) (HalA : Sf A % 16 = 0) (HalB : Sf B % 16 = 0)
    (Himgc : ∀ a, a ∈ clb (xlayXv6 A B C Sf pf ptp) → GT.gtG.gxImg a = some b0)
    (Hn0 : 0 ≤ n0 ∧ n0 < 2 ^ 32)
    (Himgn : ∀ (j : Nat) a v, (npb (xlayXv6 A B C Sf pf ptp))[j]? = some a →
      (WeakInterpProj.wbytes 4 (BitVec.ofInt 32 n0))[j]? = some v → GT.gtG.gxImg a = some v)
    (HimgN : HimgNoff (gtAdGd GT).gdG.gxImg A B)
    (Htxa : acquireText σi T) (Htxm : mycpuText σi T) (Htxp : pushOffText σi T)
    (Htxh : holdingText σi T) (Htxq : popOffText σi T) (Htxr : releaseText σi T)
    (Htxc : allocpidText σi T) (Htxt : AxSpinApA.tailText σi T)
    (HfixA : textFixed (gtAdGd GT) A (imgS σi)) (HfixB : textFixed (gtAdGd GT) B (imgS σi))
    (hmode : _get_Satp64_Mode (Mk_Satp64 satp0) = 8#4)
    (hasid : zero_extend (m := 16) (satp_to_asid satp0) = 0#16)
    (hppn : BitVec.setWidth 44 (satp_to_ppn satp0) = T.base)
    (HmapA : AxSpinApA.MapOk σi T A (Sf A) (pf A)) (HmapB : AxSpinApA.MapOk σi T B (Sf B) (pf B))
    (HpreA : allocPre (AxOpsem.grow (gtAdGd GT) A) qA A (Sf A) (pf A))
    (HpreB : allocPre (AxOpsem.grow (gtAdGd GT) B) qB B (Sf B) (pf B))
    (HpinsA : AllocPins2 (gtAdGd GT) A qA) (HpinsB : AllocPins2 (gtAdGd GT) B qB)
    (HsrcAlA : AxSpinT2g.clSrcAligned (clb (xlayXv6 A B C Sf pf ptp)) (gtAdGd GT).gdG
      (A, t2KHd qA + 4))
    (HsrcAlB : AxSpinT2g.clSrcAligned (clb (xlayXv6 A B C Sf pf ptp)) (gtAdGd GT).gdG
      (B, t2KHd qB + 4))
    (HentA : entryOk T satp0 A (Sf A) (pf A) (s0 A))
    (HentB : entryOk T satp0 B (Sf B) (pf B) (s0 B))
    (Hrun : ∀ (_ : AxannotGS AxSpinX7.xv6GF) (nm : Xv6N) i, i ∈ [A, B] →
      nsteps (tierAAstep (gtAdGd GT) nm i) (n i) (s0 i) (sN i))
    (Hend : ∀ i, i ∈ [A, B] → (sN i).atK = (AxOpsem.grow (gtAdGd GT) i).length)
    (HfinA : ¬ midState (sN A)) (HfinB : ¬ midState (sN B))
    -- C IS THE LOCK-FORGING RACER: `sw 1, lk->locked; sd cvx A, lk->cpu`, no acquire
    (HrowC : AxOpsem.grow (gtAdGd GT) C = AxSpinT2p2.rcRow)
    -- A IS CUT: its row ends at a designated cut on the gate's off (panic) arm
    (HcutA : t2Cut (gtAdGd GT) A (Sf A) (pf A)) :
    ¬ (∀ [InvGS_gen .hasNoLC AxSpinX7.xv6GF] [AxannotGS AxSpinX7.xv6GF] (nm : Xv6N),
        ⊢ xv6Init (xlayXv6 A B C Sf pf ptp) (gtAdGd GT) nm C -∗
          @tierAWpd AxSpinX7.xv6GF .hasNoLC _ _ (xv6Pol GT) (gtAdGd GT) Xv6N Unit
            (protXv6 (xlayXv6 A B C Sf pf ptp)) nm ⟨hp cpu0 AxSpinT2p2.rcM0 zeroRegs, 0⟩
            .MaybeStuck C (fun _ => iprop(True))) := by
  intro HwpC
  obtain ⟨hAB, hAC, hBC⟩ := AxSpinT2b.distinct HLay
  let sC0 : Athread := ⟨hp cpu0 AxSpinT2p2.rcM0 zeroRegs, 0⟩
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
      exact AxSpinT2p2.rcRun cpu0 (gtAdGd GT) _ HrowC
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
  obtain ⟨Hnc, -⟩ := allocpidOpen2 GT A B C Sf pf ptp qA qB σi T satp0 n0
    (AxSpinT2b.over C sC0 s0) (AxSpinT2b.over C sCN sN) (AxSpinT2b.over C 2 n) HconsT Hcl Hharts
    HLay HalA HalB Himgc Hn0 Himgn HimgN Htxa Htxm Htxp Htxh Htxq Htxr Htxc Htxt HfixA HfixB
    hmode hasid hppn HmapA HmapB HpreA HpreB HpinsA HpinsB HsrcAlA HsrcAlB
    (by rw [AxSpinT2b.overNe _ _ _ _ hAC]; exact HentA)
    (by rw [AxSpinT2b.overNe _ _ _ _ hBC]; exact HentB)
    (by rw [AxSpinT2b.overSelf])
    Hrun3 Hend3
    (by rw [AxSpinT2b.overNe _ _ _ _ hAC]; exact HfinA)
    (by rw [AxSpinT2b.overNe _ _ _ _ hBC]; exact HfinB)
    HwpC'
  exact Hnc A (by simp) HcutA

/-! # 3. (p-lk), concrete: every premise discharged on `gLk` -/

namespace AxSpinT2q3

/-- The layout of the (p-lk) graph. -/
def lay : Xlay := xlayXv6 0 1 2 AxSpinT2c1.sZ AxSpinT2a.pEx AxSpinT2c1.ptpX

/-- The (p-lk) graph's emissions. -/
noncomputable abbrev emsLk : List (List Eitem) := [AxSpinT2p2a.emsA, [], AxSpinT2p2.emsC2]

/-- AxSpinT2b2 `Himgn` (n0 = 1) on the (p-lk) graph. -/
theorem imgNpLk (L : Xlay) (hL : L.xlNp = AxSpinT2a.zNp) :
    ∀ (j : Nat) a v, (npb L)[j]? = some a →
      (WeakInterpProj.wbytes 4 (BitVec.ofInt 32 1))[j]? = some v →
        AxSpinT2p2a.gLk.gtG.gxImg a = some v := by
  intro j a v h1 h2
  have H := AxSpinT2c5.imgNp [] L hL j a v h1 h2
  rw [show (AxSpinT2c1.gT3 []).gtG.gxImg = fun a => some (AxSpinT2c1.img a) from rfl] at H
  rw [show AxSpinT2p2a.gLk.gtG.gxImg = fun a => some (AxSpinT2c1.img a) from rfl]
  exact H

/-- The warm entry state of harts 0 / 1. -/
def s0Lk (i : Agent) : Athread := AxEpiRun.st (cpuOf i) (.pure ()) (regsE i) ibNone 0

end AxSpinT2q3

set_option maxHeartbeats 800000 in
/-- **CERTIFICATE (p-lk), NON-VACUOUS: `allocpidLkRaceCert`.**  On the concrete (p-lk) graph (C
forges "A holds pid_lock" without the lock; A's acquire-time `holding` takes the long arm and A is
at `c.bnez a0, panic`; B is a phantom), the racer's WPd at the joint xv6 protocol is NOT provable.
No hypotheses. -/
theorem allocpidLkRaceCert :
    ¬ (∀ [InvGS_gen .hasNoLC AxSpinX7.xv6GF] [AxannotGS AxSpinX7.xv6GF] (nm : Xv6N),
        ⊢ xv6Init AxSpinT2q3.lay (gtAdGd AxSpinT2p2a.gLk) nm 2 -∗
          @tierAWpd AxSpinX7.xv6GF .hasNoLC _ _ (xv6Pol AxSpinT2p2a.gLk)
            (gtAdGd AxSpinT2p2a.gLk) Xv6N Unit (protXv6 AxSpinT2q3.lay) nm
            ⟨hp cpu0 AxSpinT2p2.rcM0 zeroRegs, 0⟩ .MaybeStuck 2 (fun _ => iprop(True))) := by
  obtain ⟨uA, rsA, ibA, nA, HnA, HfA⟩ := AxSpinT2p2a.runLkA
  have hL : AxSpinT2q3.lay.xlLk = AxSpinT2a.zLk := rfl
  have hN : AxSpinT2q3.lay.xlNp = AxSpinT2a.zNp := rfl
  obtain ⟨HpreA, HpinsA, -, -, HcutA, -, -, HpreB, HpinsB, -, HimgN, HsrcAlA, HrowC⟩ :=
    AxSpinT2p2a.cutCert AxSpinT2q3.lay hL
  have HlenB : (AxOpsem.grow (gtAdGd AxSpinT2p2a.gLk) 1) = [] := AxSpinT2p2.growB2 _
  exact allocpidLkRaceUnprovable AxSpinT2p2a.gLk 0 1 2 AxSpinT2c1.sZ AxSpinT2a.pEx
    AxSpinT2c1.ptpX AxSpinT2p2.qA2 AxSpinT2c1.q0 AxSpinT2c5.σX tX (BitVec.ofNat 64 satpX) 1
    AxSpinT2q3.s0Lk
    (fun i => if i = 0 then
        AxEpiRun.st (cpuOf 0) (.pure uA) rsA ibA (AxOpsem.grow (gtAdGd AxSpinT2p2a.gLk) 0).length
      else AxSpinT2q3.s0Lk 1)
    (fun i => if i = 0 then nA else 0)
    AxSpinT2p2a.catLk AxSpinT2p2a.ctrlLk AxSpinT2p2a.hartsLk AxSpinT2c1.layHyp3
    (AxSpinT2c1.sZAl 0) (AxSpinT2c1.sZAl 1)
    (AxSpinT2p2.imgClb2 AxSpinT2q3.emsLk AxSpinT2q3.lay hL) (by decide)
    (AxSpinT2q3.imgNpLk AxSpinT2q3.lay hN) HimgN
    AxSpinT2c5.acquireTextX AxSpinT2c5.mycpuTextX AxSpinT2c5.pushOffTextX
    AxSpinT2c5.holdingTextX AxSpinT2c5.popOffTextX AxSpinT2c5.releaseTextX
    AxSpinT2c5.allocpidTextX AxSpinT2c5.tailTextX
    (AxSpinT2p2.textFixed2 AxSpinT2q3.emsLk 0 (by decide))
    (AxSpinT2p2.textFixed2 AxSpinT2q3.emsLk 1 (by decide))
    satpXFacts.1 satpXFacts.2.1 satpXFacts.2.2
    (AxSpinT2c5.mapOk3 0 (by decide)) (AxSpinT2c5.mapOk3 1 (by decide))
    HpreA HpreB HpinsA HpinsB HsrcAlA
    (AxSpinT2q3.srcAlNil _ _ 1 _ HlenB)
    (AxSpinT2e3.entryR 0 (by decide)) (AxSpinT2e3.entryR 1 (by decide))
    (fun _ nm i hi => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl
      · exact HnA Xv6N nm
      · exact nsteps_O _)
    (fun i hi => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl
      · rfl
      · show 0 = _
        rw [HlenB]; rfl)
    HfA (AxSpinT2c1.finNotMid _ _ _ _ _) HrowC HcutA

/-! # 4. (p-triv): the SAME racer at the trivial protocol -/

section lkTriv
variable {hlc : HasLC} {GF : BundledGFunctors.{0,0,0}} [InvGS_gen hlc GF] [AxannotGS GF]

/-- The racer's `lk->cpu` store and halt. -/
theorem AxSpinT2q3.wpdLkCpu (GT : GdexecT) (cpu : CPU) (i : Agent)
    (Hrow : AxOpsem.grow (gtAdGd GT) i = AxSpinT2p2.rcRow) :
    ⊢ (iprop(True) : IProp GF) -∗ ∀ rs : RegFile,
      @tierAWpd GF hlc _ _ (xv6Pol GT) (gtAdGd GT) Unit Unit trivOb ()
        ⟨hp cpu AxSpinT2p2.rcCpu rs, 1⟩ .MaybeStuck i (fun _ => iprop(True)) := by
  have Hne : 1 ≠ (AxOpsem.grow (gtAdGd GT) i).length := by
    rw [Hrow]; simp [AxSpinT2p2.rcRow]
  have Hl1 : gxLbl (gtAdGd GT).gdG (i, 1) = some (.LStore false (paZ AxSpinT2p2.cpupaX)
      (WeakInterpProj.wbytes 8 (cpuAddr (cpuOf 0))) .WCplain) := by
    rw [gxLblGrow, Hrow]; rfl
  exact nshWrite (hlc := hlc) (GF := GF) (pol := xv6Pol GT) (gtAdGd GT) Unit Unit trivOb ()
    cpu i (fun _ => iprop(True)) 8 AxSpinT2p2.cpupaX AxSpinT2p2.cpupaXRam (cpuAddr (cpuOf 0))
    hlt 1 Hne iprop(True)
    (fun rs => by
      have Hval : graphData (gtAdGd GT) (i, 1) =
          some (WeakInterpProj.wbytes 8 (cpuAddr (cpuOf 0))) := by
        unfold graphData; rw [Hl1]; rfl
      iintro _
      iapply (evPlain (hlc := hlc) (pol := xv6Pol GT) (gtAdGd GT) Unit Unit trivOb () i 1
        iprop(True) iprop(True) _ _ Hval) $$ []
      · iapply feTrivu
      iintro _ _
      iapply (shHltTrue (hlc := hlc) (pol := xv6Pol GT) (gtAdGd GT) Unit Unit trivOb () cpu i
        (1 + 1)) $$ %rs)

/-- The racer's WPd at the trivial protocol. -/
theorem AxSpinT2q3.wpdLkTriv (GT : GdexecT) (cpu : CPU) (i : Agent)
    (Hrow : AxOpsem.grow (gtAdGd GT) i = AxSpinT2p2.rcRow) :
    ⊢ @tierAWpd GF hlc _ _ (xv6Pol GT) (gtAdGd GT) Unit Unit trivOb ()
      ⟨hp cpu AxSpinT2p2.rcM0 zeroRegs, 0⟩ .MaybeStuck i (fun _ => iprop(True)) := by
  have Hne : 0 ≠ (AxOpsem.grow (gtAdGd GT) i).length := by
    rw [Hrow]; simp [AxSpinT2p2.rcRow]
  have Hl0 : gxLbl (gtAdGd GT).gdG (i, 0) = some (.LStore false (paZ AxSpinT2p2.lkpaX)
      (WeakInterpProj.wbytes 4 (BitVec.ofNat (8 * 4) 1)) .WCplain) := by
    rw [gxLblGrow, Hrow]; rfl
  have HS := AxSpinT2q3.wpdLkCpu (hlc := hlc) (GF := GF) GT cpu i Hrow
  have H := nshWrite (hlc := hlc) (GF := GF) (pol := xv6Pol GT) (gtAdGd GT) Unit Unit trivOb ()
    cpu i (fun _ => iprop(True)) 4 AxSpinT2p2.lkpaX AxSpinT2p2.lkpaXRam
    (BitVec.ofNat (8 * 4) 1) AxSpinT2p2.rcCpu 0 Hne iprop(True)
    (fun rs => by
      have Hval : graphData (gtAdGd GT) (i, 0) =
          some (WeakInterpProj.wbytes 4 (BitVec.ofNat (8 * 4) 1)) := by
        unfold graphData; rw [Hl0]; rfl
      iintro _
      iapply (evPlain (hlc := hlc) (pol := xv6Pol GT) (gtAdGd GT) Unit Unit trivOb () i 0
        iprop(True) iprop(True) _ _ Hval) $$ []
      · iapply feTrivu
      iintro _ _
      iapply HS $$ [] %rs
      itrivial)
  iapply H $$ [] %zeroRegs
  itrivial

end lkTriv

/-- **SANITY TWIN (p-triv), `allocpidLkRaceTrivial`.**  The racer of (p-lk) — same program, same
start state, same row, same policy and functors, post `True` — IS verifiable at the trivial
protocol. -/
theorem allocpidLkRaceTrivial (GT : GdexecT) (C : Agent)
    (HrowC : AxOpsem.grow (gtAdGd GT) C = AxSpinT2p2.rcRow) :
    ∀ [InvGS_gen .hasNoLC AxSpinX7.xv6GF] [AxannotGS AxSpinX7.xv6GF] (nm : Unit),
      ⊢ (iprop(emp) : IProp AxSpinX7.xv6GF) -∗
        @tierAWpd AxSpinX7.xv6GF .hasNoLC _ _ (xv6Pol GT) (gtAdGd GT) Unit Unit trivOb nm
          ⟨hp cpu0 AxSpinT2p2.rcM0 zeroRegs, 0⟩ .MaybeStuck C (fun _ => iprop(True)) := by
  intro _ _ nm
  cases nm
  iintro _
  iapply (AxSpinT2q3.wpdLkTriv (hlc := .hasNoLC) (GF := AxSpinX7.xv6GF) GT cpu0 C HrowC)

/-- (p-triv) on the concrete (p-lk) graph, C = 2 (no hypotheses). -/
theorem allocpidLkRaceTrivialLk :
    ∀ [InvGS_gen .hasNoLC AxSpinX7.xv6GF] [AxannotGS AxSpinX7.xv6GF] (nm : Unit),
      ⊢ (iprop(emp) : IProp AxSpinX7.xv6GF) -∗
        @tierAWpd AxSpinX7.xv6GF .hasNoLC _ _ (xv6Pol AxSpinT2p2a.gLk) (gtAdGd AxSpinT2p2a.gLk)
          Unit Unit trivOb nm ⟨hp cpu0 AxSpinT2p2.rcM0 zeroRegs, 0⟩ .MaybeStuck 2
          (fun _ => iprop(True)) :=
  allocpidLkRaceTrivial AxSpinT2p2a.gLk 2 (AxSpinT2p2.growC2 _)

end Weak
