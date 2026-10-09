/-
Weak: **THEOREM 2, STAGE 2 / certificate pair (p-stk) / (p-triv): THE RELOAD READING OF
CONJUNCT 1 (NO RELOAD MISREAD) IS LOAD-BEARING ON STACK OWNERSHIP** — the stack-overwriting racer
C of `AxSpinT2p3` (`sd push_off + 0x30, A's mycpu ra spill slot`, a store into A's PRIVATE stack)
has NO WPd against the joint xv6 protocol (`allocpidStkRaceUnprovable`, reductio over an abstract
graph; `allocpidStkRaceCert`, the concrete graph `AxSpinT2p3a.gStk`, NO hypotheses), while the
same racer IS verifiable at the trivial protocol (`allocpidStkRaceTrivial`,
`allocpidStkRaceTrivialStk`).

Lean-only (no Rocq source).  Design `notes/weak-lb-thm2-pins.md` §P1 ("(p-stk)", Q-P1-4), the
row-integrity analogue of (p-lk) (`AxSpinT2q3`, whose template this file follows).  Possible only
since the P1 finish (2026-10-09): `AllocPins2` lost its interim row-end premise `rlEnd`, which
EXCLUDED every reload-cut row (`PROGRESS-AxSpinT2p3.md`), and `allocpidOpen2`'s `¬ t2Cut` now
PROVES the reload reading (`¬ reloadMis`).

## What this file proves

**(p-stk), abstract: `allocpidStkRaceUnprovable`.**  On EVERY graph satisfying all of
`allocpidOpen2`'s premises for A and B (verbatim, minus C's `HkC`/C's part of `Hrun`/`Hend` and
`HwpC`), with C's row the stack-overwriting racer's (`HrowC : grow C = AxSpinT2p3.rcRowS`) and A's
row a RELOAD CUT (`HmisA : reloadMis (gtAdGd GT) A (Sf A) (pf A)` — A's row ends right after a
reload that read a value other than its spill's):
  `¬ (∀ Hinv Hann nm, ⊢ xv6Init L GD nm C -∗ WPd_{protXv6 L} ⟨hp cpu0 rcMS zeroRegs, 0⟩ {{True}})`.
Proof: C's run / row end / start position are DERIVED from `HrowC` (`AxSpinT2p3.rcRunS`, 1 step);
apply `allocpidOpen2`; its conjunct 1 gives `¬ t2Cut A`, contradicting `t2Cut A`
(`AxSpinT2f.reloadCut HmisA`).

**(p-stk), concrete: `allocpidStkRaceCert`** (NO hypotheses).  On `gStk` (AxSpinT2p3a: A runs
from `allocproc + 0x38` into push_off's first `mycpu()`, spills `ra = push_off + 0x14` to `S − 72`;
C stores `push_off + 0x30` there; mycpu's `ld ra, 8(sp)` reads C's value and A's row ends right
after it, `LEN = 9 = rlPos .poMy1 q0`; B is a phantom with an empty row), every premise of
`allocpidStkRaceUnprovable` is discharged: the bundle `AxSpinT2p3a.stkCert` (`allocPre` /
`AllocPins2` for A and B — A's is now `⟨npNowrapAS, npNcollAS, ppArmAS⟩` —, `reloadMis A`,
`HimgNoff`, `HrowC`), `catStk`/`ctrlStk`/`hartsStk`, `runStkA` (A's run, the REAL `riscvStep`
loading C's value into `ra`) / B's 0-step run, image (`AxSpinT2p3.imgClbS`, nextpid = 1 by
`imgNpS`), text (`AxSpinT2c5.*TextX`, `textFixedS`), translation (`AxSpinT2pt.satpXFacts`,
`AxSpinT2c5.mapOk3`), layout (`AxSpinT2c1.layHyp3`/`sZAl`), entry (`AxSpinT2e3.entryR`), boundary
(`AxSpinT2c1.finNotMid`).  So the reload reading of conjunct 1 is NON-VACUOUS: a C that writes
A's stack makes A's control flow leave the row (a diverted `c.ret` is next), and it is `HwpC`
(`protXv6` keeps `[S − 80, S)` private to its hart) that rules this out.

**(p-triv): `allocpidStkRaceTrivial`.**  For every graph with C's row the racer's, the SAME program
at the SAME start state (policy `xv6Pol GT`, functors `xv6GF`, post `True`) IS provable at
`trivOb` (`AxSpinT2q4.wpdStkTriv`: one `nshWrite` with `evPlain`/`feTrivu`, then `shHltTrue`);
`allocpidStkRaceTrivialStk` instantiates it at `gStk`, C = 2.  So what refuses C is `protXv6`'s
ownership of A's stack window, not the WPd framework or the racer's run.

## Pins / honesty
* C is `AxSpinT2p3`'s one-store racer (`rcMS = stv 8 rapaX wX hlt`, a plain 8-byte `sd`, a
  licensed SHAPE of write); its start state `⟨hp cpu0 AxSpinT2p3.rcMS zeroRegs, 0⟩` is verbatim
  in both halves of the pair.
* Inherited scope of the concrete graph: `AxSpinT2p3`/`AxSpinT2p3a`/`AxSpinT2pt`/`AxSpinT2c1`
  headers (kvmmake-shaped `tX`, warm TLB, image models text / page tables / nextpid).  Prefix
  closure stays informal (Q-S2-6, `AxSpinT2b2` header): the cut row is a covered execution (the
  row stops right after the misread reload, before mycpu's diverted `ret`).
* No drive is re-run here: A's run comes from `AxSpinT2p3a.runStkA` (read-back of `chkA`).

Reused (by name): `allocpidOpen2` (AxSpinT2b2), `AxSpinT2f.reloadCut`, `AxSpinT2b.over`/
`overSelf`/`overNe`/`mem3`/`distinct`, `AxSpinT2p3.rcMS`/`rcRowS`/`rcRunS`/`rapaX`/`rapaXRam`/
`wX`/`imgClbS`/`imgNpS`/`textFixedS`/`growBS`/`growCS`, `AxSpinT2p3a.*`, `AxSpinT2q3.lay`/`s0Lk`,
`AxSpinT2e3.entryR`, `AxSpinT2c5.*`, `AxSpinT2c1.*`, `nshWrite`, `evPlain`, `feTrivu`,
`shHltTrue`, `gxLblGrow`.
Names: Lean-only; `allocpidStkRaceUnprovable`, `allocpidStkRaceCert`, `allocpidStkRaceTrivial`,
`allocpidStkRaceTrivialStk` (grepped absent); helpers `Weak.AxSpinT2q4.*`.
-/
import Weak.AxSpinT2q3
import Weak.AxSpinT2p3a

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D LeanRV64D.Functions
open AxSpinT2pt

/-! # 1. (p-stk), abstract: the reductio through `allocpidOpen2` -/

set_option maxHeartbeats 800000 in
/-- **CERTIFICATE (p-stk), `allocpidStkRaceUnprovable`.**  On any graph satisfying every premise
of `allocpidOpen2` for A and B, where C's row is the stack-overwriting racer's and A's row is a
RELOAD CUT (A's row ends right after a reload that misread), the racer's WPd at the joint xv6
protocol is NOT provable. -/
theorem allocpidStkRaceUnprovable (GT : GdexecT) (A B C : Agent) (Sf pf : Agent → Int)
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
    (HentA : entryOk T satp0 A (Sf A) (pf A) (s0 A))
    (HentB : entryOk T satp0 B (Sf B) (pf B) (s0 B))
    (Hrun : ∀ (_ : AxannotGS AxSpinX7.xv6GF) (nm : Xv6N) i, i ∈ [A, B] →
      nsteps (tierAAstep (gtAdGd GT) nm i) (n i) (s0 i) (sN i))
    (Hend : ∀ i, i ∈ [A, B] → (sN i).atK = (AxOpsem.grow (gtAdGd GT) i).length)
    (HfinA : ¬ midState (sN A)) (HfinB : ¬ midState (sN B))
    -- C IS THE STACK-OVERWRITING RACER: one `sd` into A's private stack, no ownership
    (HrowC : AxOpsem.grow (gtAdGd GT) C = AxSpinT2p3.rcRowS)
    -- A IS A RELOAD CUT: its row ends right after a reload that read a wrong value
    (HmisA : reloadMis (gtAdGd GT) A (Sf A) (pf A)) :
    ¬ (∀ [InvGS_gen .hasNoLC AxSpinX7.xv6GF] [AxannotGS AxSpinX7.xv6GF] (nm : Xv6N),
        ⊢ xv6Init (xlayXv6 A B C Sf pf ptp) (gtAdGd GT) nm C -∗
          @tierAWpd AxSpinX7.xv6GF .hasNoLC _ _ (xv6Pol GT) (gtAdGd GT) Xv6N Unit
            (protXv6 (xlayXv6 A B C Sf pf ptp)) nm ⟨hp cpu0 AxSpinT2p3.rcMS zeroRegs, 0⟩
            .MaybeStuck C (fun _ => iprop(True))) := by
  intro HwpC
  obtain ⟨hAB, hAC, hBC⟩ := AxSpinT2b.distinct HLay
  let sC0 : Athread := ⟨hp cpu0 AxSpinT2p3.rcMS zeroRegs, 0⟩
  let sCN : Athread := ⟨hp cpu0 hlt zeroRegs, 1⟩
  have Hrun3 : ∀ (_ : AxannotGS AxSpinX7.xv6GF) (nm : Xv6N) i, i ∈ [A, B, C] →
      nsteps (tierAAstep (gtAdGd GT) nm i) (AxSpinT2b.over C 1 n i) (AxSpinT2b.over C sC0 s0 i)
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
      exact AxSpinT2p3.rcRunS cpu0 (gtAdGd GT) _ HrowC
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
    (AxSpinT2b.over C sC0 s0) (AxSpinT2b.over C sCN sN) (AxSpinT2b.over C 1 n) HconsT Hcl Hharts
    HLay HalA HalB Himgc Hn0 Himgn HimgN Htxa Htxm Htxp Htxh Htxq Htxr Htxc Htxt HfixA HfixB
    hmode hasid hppn HmapA HmapB HpreA HpreB HpinsA HpinsB
    (by rw [AxSpinT2b.overNe _ _ _ _ hAC]; exact HentA)
    (by rw [AxSpinT2b.overNe _ _ _ _ hBC]; exact HentB)
    (by rw [AxSpinT2b.overSelf])
    Hrun3 Hend3
    (by rw [AxSpinT2b.overNe _ _ _ _ hAC]; exact HfinA)
    (by rw [AxSpinT2b.overNe _ _ _ _ hBC]; exact HfinB)
    HwpC'
  exact Hnc A (by simp) (AxSpinT2f.reloadCut HmisA)

/-! # 2. (p-stk), concrete: every premise discharged on `gStk` -/

namespace AxSpinT2q4

/-- The (p-stk) graph's emissions. -/
noncomputable abbrev emsStk : List (List Eitem) :=
  [AxSpinT2p3a.emsA, [], AxSpinT2p3.emsCS]

end AxSpinT2q4

set_option maxHeartbeats 800000 in
/-- **CERTIFICATE (p-stk), NON-VACUOUS: `allocpidStkRaceCert`.**  On the concrete (p-stk) graph
(C overwrites A's mycpu `ra` spill with push_off's other return site; A's mycpu `ra` reload reads
it and A's row ends right after the reload, a `.poMy1` reload cut; B is a phantom), the racer's
WPd at the joint xv6 protocol is NOT provable.  No hypotheses. -/
theorem allocpidStkRaceCert :
    ¬ (∀ [InvGS_gen .hasNoLC AxSpinX7.xv6GF] [AxannotGS AxSpinX7.xv6GF] (nm : Xv6N),
        ⊢ xv6Init AxSpinT2q3.lay (gtAdGd AxSpinT2p3a.gStk) nm 2 -∗
          @tierAWpd AxSpinX7.xv6GF .hasNoLC _ _ (xv6Pol AxSpinT2p3a.gStk)
            (gtAdGd AxSpinT2p3a.gStk) Xv6N Unit (protXv6 AxSpinT2q3.lay) nm
            ⟨hp cpu0 AxSpinT2p3.rcMS zeroRegs, 0⟩ .MaybeStuck 2 (fun _ => iprop(True))) := by
  obtain ⟨uA, rsA, ibA, nA, HnA, HfA⟩ := AxSpinT2p3a.runStkA
  have hL : AxSpinT2q3.lay.xlLk = AxSpinT2a.zLk := rfl
  have hN : AxSpinT2q3.lay.xlNp = AxSpinT2a.zNp := rfl
  obtain ⟨HpreA, HpinsA, -, -, HmisA, -, -, -, -, HpreB, HpinsB, -, HimgN, HrowC⟩ :=
    AxSpinT2p3a.stkCert
  have HlenB : (AxOpsem.grow (gtAdGd AxSpinT2p3a.gStk) 1) = [] := AxSpinT2p3.growBS _
  exact allocpidStkRaceUnprovable AxSpinT2p3a.gStk 0 1 2 AxSpinT2c1.sZ AxSpinT2a.pEx
    AxSpinT2c1.ptpX AxSpinT2c1.q0 AxSpinT2c1.q0 AxSpinT2c5.σX tX (BitVec.ofNat 64 satpX) 1
    AxSpinT2q3.s0Lk
    (fun i => if i = 0 then
        AxEpiRun.st (cpuOf 0) (.pure uA) rsA ibA (AxOpsem.grow (gtAdGd AxSpinT2p3a.gStk) 0).length
      else AxSpinT2q3.s0Lk 1)
    (fun i => if i = 0 then nA else 0)
    AxSpinT2p3a.catStk AxSpinT2p3a.ctrlStk AxSpinT2p3a.hartsStk AxSpinT2c1.layHyp3
    (AxSpinT2c1.sZAl 0) (AxSpinT2c1.sZAl 1)
    (AxSpinT2p3.imgClbS AxSpinT2q4.emsStk AxSpinT2q3.lay hL) (by decide)
    (AxSpinT2p3.imgNpS AxSpinT2q4.emsStk AxSpinT2q3.lay hN) HimgN
    AxSpinT2c5.acquireTextX AxSpinT2c5.mycpuTextX AxSpinT2c5.pushOffTextX
    AxSpinT2c5.holdingTextX AxSpinT2c5.popOffTextX AxSpinT2c5.releaseTextX
    AxSpinT2c5.allocpidTextX AxSpinT2c5.tailTextX
    (AxSpinT2p3.textFixedS AxSpinT2q4.emsStk 0 (by decide))
    (AxSpinT2p3.textFixedS AxSpinT2q4.emsStk 1 (by decide))
    satpXFacts.1 satpXFacts.2.1 satpXFacts.2.2
    (AxSpinT2c5.mapOk3 0 (by decide)) (AxSpinT2c5.mapOk3 1 (by decide))
    HpreA HpreB HpinsA HpinsB
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
    HfA (AxSpinT2c1.finNotMid _ _ _ _ _) HrowC HmisA

/-! # 3. (p-triv): the SAME racer at the trivial protocol -/

section stkTriv
variable {hlc : HasLC} {GF : BundledGFunctors.{0,0,0}} [InvGS_gen hlc GF] [AxannotGS GF]

/-- The racer's WPd at the trivial protocol: its one store, then halt. -/
theorem AxSpinT2q4.wpdStkTriv (GT : GdexecT) (cpu : CPU) (i : Agent)
    (Hrow : AxOpsem.grow (gtAdGd GT) i = AxSpinT2p3.rcRowS) :
    ⊢ @tierAWpd GF hlc _ _ (xv6Pol GT) (gtAdGd GT) Unit Unit trivOb ()
      ⟨hp cpu AxSpinT2p3.rcMS zeroRegs, 0⟩ .MaybeStuck i (fun _ => iprop(True)) := by
  have Hne : 0 ≠ (AxOpsem.grow (gtAdGd GT) i).length := by
    rw [Hrow]; simp [AxSpinT2p3.rcRowS]
  have Hl0 : gxLbl (gtAdGd GT).gdG (i, 0) = some (.LStore false (paZ AxSpinT2p3.rapaX)
      (WeakInterpProj.wbytes 8 AxSpinT2p3.wX) .WCplain) := by
    rw [gxLblGrow, Hrow]; rfl
  have H := nshWrite (hlc := hlc) (GF := GF) (pol := xv6Pol GT) (gtAdGd GT) Unit Unit trivOb ()
    cpu i (fun _ => iprop(True)) 8 AxSpinT2p3.rapaX AxSpinT2p3.rapaXRam AxSpinT2p3.wX hlt 0 Hne
    iprop(True)
    (fun rs => by
      have Hval : graphData (gtAdGd GT) (i, 0) =
          some (WeakInterpProj.wbytes 8 AxSpinT2p3.wX) := by
        unfold graphData; rw [Hl0]; rfl
      iintro _
      iapply (evPlain (hlc := hlc) (pol := xv6Pol GT) (gtAdGd GT) Unit Unit trivOb () i 0
        iprop(True) iprop(True) _ _ Hval) $$ []
      · iapply feTrivu
      iintro _ _
      iapply (shHltTrue (hlc := hlc) (pol := xv6Pol GT) (gtAdGd GT) Unit Unit trivOb () cpu i
        (0 + 1)) $$ %rs)
  iapply H $$ [] %zeroRegs
  itrivial

end stkTriv

/-- **SANITY TWIN (p-triv), `allocpidStkRaceTrivial`.**  The racer of (p-stk) — same program,
same start state, same row, same policy and functors, post `True` — IS verifiable at the trivial
protocol. -/
theorem allocpidStkRaceTrivial (GT : GdexecT) (C : Agent)
    (HrowC : AxOpsem.grow (gtAdGd GT) C = AxSpinT2p3.rcRowS) :
    ∀ [InvGS_gen .hasNoLC AxSpinX7.xv6GF] [AxannotGS AxSpinX7.xv6GF] (nm : Unit),
      ⊢ (iprop(emp) : IProp AxSpinX7.xv6GF) -∗
        @tierAWpd AxSpinX7.xv6GF .hasNoLC _ _ (xv6Pol GT) (gtAdGd GT) Unit Unit trivOb nm
          ⟨hp cpu0 AxSpinT2p3.rcMS zeroRegs, 0⟩ .MaybeStuck C (fun _ => iprop(True)) := by
  intro _ _ nm
  cases nm
  iintro _
  iapply (AxSpinT2q4.wpdStkTriv (hlc := .hasNoLC) (GF := AxSpinX7.xv6GF) GT cpu0 C HrowC)

/-- (p-triv) on the concrete (p-stk) graph, C = 2 (no hypotheses). -/
theorem allocpidStkRaceTrivialStk :
    ∀ [InvGS_gen .hasNoLC AxSpinX7.xv6GF] [AxannotGS AxSpinX7.xv6GF] (nm : Unit),
      ⊢ (iprop(emp) : IProp AxSpinX7.xv6GF) -∗
        @tierAWpd AxSpinX7.xv6GF .hasNoLC _ _ (xv6Pol AxSpinT2p3a.gStk)
          (gtAdGd AxSpinT2p3a.gStk) Unit Unit trivOb nm ⟨hp cpu0 AxSpinT2p3.rcMS zeroRegs, 0⟩
          .MaybeStuck 2 (fun _ => iprop(True)) :=
  allocpidStkRaceTrivial AxSpinT2p3a.gStk 2 (AxSpinT2p3.growCS _)

end Weak
