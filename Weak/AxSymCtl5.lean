/-
Weak: CLOSED WPd's through the counting engine at the REAL S-mode regime, and the concrete probe
`AxSmodeProbe` / `gpT`.

Rocq: `iris/AxSymCtl5.v` @ xxvzwolszwmp.

## The Rocq header, in substance

§1 `wpdCmvClosed` (generic over `SpineCnt`): ONE `c.mv a0, ra` as a closed
`wpd s0 (ΦRet cpu (POne pc rs0))`: the row is exactly the instruction's reads (`k0 + cnt rs0 pc`);
then the tail at pc + 2.  §2 the S-mode corollaries: `XGprWriteCS`, `wpdBlockClosedS`
(`wpdBlockClosed` at `spineCntS`), and the `axGA2` forms `wpdBlockClosedGa2` / `wpdCmvClosedGa2`
(real `protInv`; premises: the graph fact `textFixed GD0 i (imgS σi)` and the row length).
§3 the probe: `pTTextOkC`, `pH1`, `pTVpn2`, `pTTextAt2`, `pTFcntCold`, and Rocq's capstone
`wpd_cmv_probe_closed` (closed WPd at `gpT`, no premise) — Lean §4 (`wpdCmvProbeClosed`).

## Deviations from Rocq

1. Stage C counts (`AxSymCtlb` deviation 1, `AxSymCtl4` deviation 1): the row lengths are
   `k0 + fcntS rs0 pc` for the block too (Rocq `+ 1`: the second, same-page fetch reads no graph
   item); `pTFcntCold` is `= 3` (Rocq 4; the fetch is an admin step).  Section premise `Hloc`
   DROPPED (as `XGprWriteC`).  Spelling as `AxSymCtl3` deviation 1 / `AxSymCtl4` deviation 4
   (`Hm/Ha/Hp` ↦ `hmode/hasid/hppn`); `vm_compute` ↦ `decide +kernel`; `nseip` ↦
   `AxSymEngine2.notPin`; the local instances `cl_ga2` / `gpT_inst5` are not declared (`blkGa2`
   passed with `@`, `TX` dropped, `AxSymCtl3` deviation 5).
2. THE TAIL — Q14 (provisional) applied.  Every closed corollary carrying a Rocq name is stated
   in the `Htail` form (premise: a budget-0 stop certificate at the tail pc, at every regime state
   with the page of pc warm and the post's GPR values; proofs go through
   `AxSymCtl.wpdTailOfStop`): `wpdCmvClosed`, `wpdBlockClosedS`, `wpdBlockClosedGa2`,
   `wpdCmvClosedGa2` (their instances are SYMBOLIC — the tail page is not known to be cold).
   Each has a Lean-only `wpdBlockClosedCold`-style twin in Rocq's premise shape (`textAt` at the
   tail pc plus `∀ rs, warm cnt rs pc → 1 ≤ cnt rs tail`): `AxSymCtl5.wpdCmvClosedCold`,
   `AxSymCtl5.wpdBlockClosedSCold`, `AxSymCtl5.wpdBlockClosedGa2Cold`,
   `AxSymCtl5.wpdCmvClosedGa2Cold`.  `XGprWriteCS` is a theorem (Rocq `Definition`, a partial
   application), stated in full.
3. THE CAPSTONE `wpd_cmv_probe_closed` ↦ `wpdCmvProbeClosed` — Q16 (owner ruling).  Statement
   as Rocq's (the local instance `gpT_inst5` ↦ `blkGa2 gpT γ` passed with `@`; `TX` dropped).
   The PROOF differs: in Rocq the tail fetch at sPc + 2 was a graph read, stuck at the row end.
   In Lean (Stage C) neither Q14 tail form applies (the tail page is warm after the c.mv, and the
   instructions at sPc + 2 (0x0081, `c.addi ra, 0`, a HINT), sPc + 4 and sPc + 6 (`c.nop`) make
   no graph read; kernel-checked evidence `AxSymCtl5.probeTailTrace`), so the run is followed
   PAST the row end: `wpdCmvProbeRowEnd` (the c.mv, ending exactly at `gpT`'s row end), then
   `XGprWriteC` for the hint and `AxSymCtl.XNopC` twice (each at the row end, 0 graph reads on
   the warm page), then THE IMAGELESS FETCH at sPc + 8: `AxSymCtl.wpdTailOfStopStuck` with the
   stop certificate `AxSymCtl5.stopCert8` (`AxSymCtl.spineStopFetch` over
   `AxSymCtl5.fetchStop8`, which meets two `scFetchS` certificates over the hole-filled images
   `AxSymCtl5.holeSt 0x1` / `holeSt 0x5` by `AxSymCtl.EvBMeet0`: every path ends at
   `EvB.ebNf`).  Graph facts at `blkGa2 gpT γ`: `G GD := GD = gpT` (row length 3 =
   `gpTRowLen`; `gpT`'s boot image IS `imgS nvST`, so `HGimg` is `rfl`-level).  Lean-only
   vocabulary: `AxSymCtl5.pc2/pc4/pc6/pc8/pa8`, `pTVpn4/6/8`, `pWChk`, `textAtPage`, `pI1`,
   `pIns1`, `pHN`, `pIN`, `rfFDecodePH1`, `rfFDecodePHN`, `execDecodePH1`, `execDecodePHN`,
   `rfFExecutePI1`, `rfFExecutePIN`, `pTTextOkC1`, `certAddi0`, `pTTextAt4`, `pTTextAt6`,
   `pTTextOkNop`, `holeSt`, `holeSub`, `imgSub`, `slotSub`, `holeTextAt`, `holeBytes1/2`,
   `fetchStop8`, `stopCert8`, `offBoundary`.

**Rocq → Lean name map.**  `P_one` `POne`, `wpd_cmv_closed` `wpdCmvClosed`, `X_gpr_writeC_S`
`XGprWriteCS`, `wpd_block_closed_S` `wpdBlockClosedS`, `wpd_block_closed_ga2`
`wpdBlockClosedGa2`, `wpd_cmv_closed_ga2` `wpdCmvClosedGa2`, `pT_text_ok_c` `pTTextOkC`, `pH1`
`pH1`, `pT_vpn2` `pTVpn2`, `pT_text_at2` `pTTextAt2`, `pT_fcnt_cold` `pTFcntCold`,
`wpd_cmv_probe_closed` `wpdCmvProbeClosed`.  None is in the duplicated-name table.  Lean-only (file-qualified `AxSymCtl5.*`): `wpdCmvClosedCold`,
`wpdBlockClosedSCold`, `wpdBlockClosedGa2Cold`, `wpdCmvClosedGa2Cold`, `hlenGa2` (the row-length
premise at `blkGa2`), `runTrace`, `probeTailTrace`, `wpdCmvProbeRowEnd`.

**Dropped:** the local instances `cl_ga2`/`gpT_inst5` and the Ltac `nseip` (deviation 1); the
`Print Assumptions`/`Check` lines.  Rocq 12 definitions/lemmas + 2 local instances + 1 Ltac;
Lean 12 + 8 Lean-only (§1–§3) + 35 Lean-only (§4, deviation 3).
-/
import Weak.AxSymCtl4
import Weak.AxSymCtl3
import Weak.AxRelease6

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std MachCSL
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D LeanRV64D.Functions

/-! # 1. One instruction, closed -/

/-- Rocq `P_one`: at the boundary after `c.mv a0, ra` (pc + 2), a0 holds ra's start value, every
other GPR its start value. -/
def POne (pc : BitVec 64) (rs0 : RegFile) (rs : RegFile) : Prop :=
  rs .PC = BitVec.addInt pc 2 →
  ∀ r : BitVec 5, r.toNat ≠ 0 →
    AxSymEngine3.gpr r rs = if r = a05 then blkW1 rs0 else AxSymEngine3.gpr r rs0

section oneClosed
variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [AxirisG GF] [Axpol]
variable (img : Image) (i : Agent) (cpu : CPU)
variable (ctrlOk : RegFile → Prop) (textAt : BitVec 64 → BitVec 16 → Prop)
  (cnt : RegFile → BitVec 64 → Nat)
variable (Hsc : SpineCnt img ctrlOk textAt cnt)
variable (Htext : ∀ GD, rvwmoCatConsistent GD →
  AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜textFixed GD i img⌝)
variable (Hflow : ∀ GD ls k, rvwmoCatConsistent GD →
  (∃ lb aq base n vs, (AxOpsem.grow GD i)[k]? = some lb ∧ aident lb = .IRead aq base n ∧
     imgBytes img base n = some vs) →
  AxirisG.gconstInterp (GF := GF) GD ∗ AxirisG.localInterp GD i k ls ⊢ fetchFlow GD i k)

include Hsc Htext Hflow in
/-- ONE `c.mv a0, ra` as a CLOSED `wpd s0 (ΦRet cpu (POne pc rs0))` (deviation 2): the row is
exactly the instruction's graph reads (`k0 + cnt rs0 pc`); the tail is a budget-0 stop
certificate at `pc + 2` (`Htail`, discharged through `AxSymCtl.wpdTailOfStop`). -/
theorem wpdCmvClosed (pc : BitVec 64) (s0 : Athread) (rs0 : RegFile) (k0 : Nat) :
    RetX cpu rs0 k0 s0 → ctrlOk rs0 → rs0 .PC = pc →
    textOkC img ctrlOk textAt pc ICmv →
    (∀ rs, ctrlOk rs → rs .PC = BitVec.addInt pc 2 → warm cnt rs pc →
      (∀ r : BitVec 5, r.toNat ≠ 0 →
        AxSymEngine3.gpr r rs = if r = a05 then blkW1 rs0 else AxSymEngine3.gpr r rs0) →
      ∀ (tick : Bool) (t : ExecSt), regsAgree AxRunClose.pinReg t.regs rs →
        EvB img (fun _ _ => False) (fun _ _ _ => False) (riscvStep tick) t 0) →
    (∀ GD, rvwmoCatConsistent GD →
      AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜(AxOpsem.grow GD i).length = k0 + cnt rs0 pc⌝) →
    ⊢ wpd .MaybeStuck i s0 (ΦRet (GF := GF) cpu (POne pc rs0)) := by
  intro HR0 Hc0 HPC0 Htx1 Htail Hlen
  have HGl : ∀ GD, (fun GD : Gdexec => (AxOpsem.grow GD i).length = k0 + cnt rs0 pc) GD →
      (AxOpsem.grow GD i).length = k0 + cnt rs0 pc := fun _ h => h
  have HX := XGprWriteC img i cpu ctrlOk textAt cnt Hsc Htext Hflow _ Hlen _ HGl
    (ΦRet (GF := GF) cpu (POne pc rs0)) (ΦRetMid i cpu _ _)
  iapply (HX s0 rs0 k0 pc ICmv a05 (blkW1 rs0) HR0 Hc0 HPC0 Htx1 (by decide)
    (fun s_pc _ Hag => certCmv rs0 s_pc Hag) (by omega)
    (fun _ s1 _ HR _ => ΦRetBoundary i cpu _ rs0 k0 s1
      (fun rs' Hag Hpc => ((addVecIntNe pc 2 ⟨by decide, by decide⟩)
        (Hpc.symm.trans ((Hag .PC (AxSymEngine2.notPin _ (by decide) (by decide))).trans
          HPC0))).elim) HR))
  iintro %s1 %rs1 %k1 %HR1 %Hk1 %Hc1 %HPC1 %Hg1 %Hw1
  subst Hk1
  iapply (AxSymCtl.wpdTailOfStop img i cpu Htext Hflow _ Hlen _ HGl
    (ΦRet (GF := GF) cpu (POne pc rs0)) (ΦRetMid i cpu _ _) s1 rs1 HR1 ?_
    (Htail rs1 Hc1 HPC1 Hw1 Hg1))
  intro GD s3 _ HR3 _
  refine ΦRetBoundary i cpu _ rs1 _ s3 ?_ HR3
  intro rs' Hag _ r Hr
  have e : AxSymEngine3.gpr r rs' = AxSymEngine3.gpr r rs1 :=
    AxSymEngine2.uxaXgetAgree _ _ Hag r
  rw [e]
  exact Hg1 r Hr

include Hsc Htext Hflow in
/-- (Lean-only, deviation 2) `wpdCmvClosed` with Rocq's tail premise `textAt (pc + 2) h1`,
plus: the tail fetch reads the graph after the page of `pc` is warm (a cold tail page). -/
theorem AxSymCtl5.wpdCmvClosedCold (pc : BitVec 64) (s0 : Athread) (rs0 : RegFile) (k0 : Nat)
    (h1 : BitVec 16) :
    RetX cpu rs0 k0 s0 → ctrlOk rs0 → rs0 .PC = pc →
    textOkC img ctrlOk textAt pc ICmv →
    textAt (BitVec.addInt pc 2) h1 →
    (∀ rs, warm cnt rs pc → 1 ≤ cnt rs (BitVec.addInt pc 2)) →
    (∀ GD, rvwmoCatConsistent GD →
      AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜(AxOpsem.grow GD i).length = k0 + cnt rs0 pc⌝) →
    ⊢ wpd .MaybeStuck i s0 (ΦRet (GF := GF) cpu (POne pc rs0)) := by
  intro HR0 Hc0 HPC0 Htx1 Hat2 Hcold Hlen
  exact wpdCmvClosed img i cpu ctrlOk textAt cnt Hsc Htext Hflow pc s0 rs0 k0 HR0 Hc0 HPC0 Htx1
    (fun rs Hc HPC Hw _ tick t Hag =>
      spineStop img ctrlOk textAt cnt Hsc rs (BitVec.addInt pc 2) h1 _ Hc HPC Hat2 (Hcold rs Hw)
        tick t Hag)
    Hlen

end oneClosed

/-! # 2. The S-mode corollaries (the REAL kernel regime, symbolic state) -/

section closedS
variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [AxirisG GF] [Axpol]
variable (σi : ExecSt) (T : PTree) (satp0 : BitVec 64) (i : Agent) (cpu : CPU)
variable (hmode : _get_Satp64_Mode (Mk_Satp64 satp0) = 8#4)
  (hasid : zero_extend (m := 16) (satp_to_asid satp0) = 0#16)
  (hppn : BitVec.setWidth 44 (satp_to_ppn satp0) = T.base)
variable (Htext : ∀ GD, rvwmoCatConsistent GD →
  AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜textFixed GD i (imgS σi)⌝)
variable (Hflow : ∀ GD ls k, rvwmoCatConsistent GD →
  (∃ lb aq base n vs, (AxOpsem.grow GD i)[k]? = some lb ∧ aident lb = .IRead aq base n ∧
     imgBytes (imgS σi) base n = some vs) →
  AxirisG.gconstInterp (GF := GF) GD ∗ AxirisG.localInterp GD i k ls ⊢ fetchFlow GD i k)

include hmode hasid hppn Htext Hflow in
/-- Rocq `X_gpr_writeC_S` (a `Definition` there: `XGprWriteC` at `spineCntS`): X at the S-mode
kernel regime, REPORTING THE ROW POSITION `k' = k + fcntS rs pc` (0 on a TLB hit, 3 on a miss;
Rocq 1 / 4). -/
theorem XGprWriteCS (G : Gdexec → Prop)
    (HG : ∀ GD, rvwmoCatConsistent GD → AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜G GD⌝)
    (kend : Nat) (HGl : ∀ GD, G GD → (AxOpsem.grow GD i).length = kend)
    (Φ : Athread → IProp GF)
    (Hmid : ∀ GD s, G GD → midState s → s.atK = (AxOpsem.grow GD i).length → ⊢ postLifting Φ i s)
    (s : Athread) (rs : RegFile) (k : Nat) (pc : BitVec 64) (ins : instruction)
    (rd : BitVec 5) (wval : BitVec 64) :
    RetX cpu rs k s → ctrlOkS T satp0 rs → rs .PC = pc →
    textOkC (imgS σi) (ctrlOkS T satp0) (textAtS σi T) pc ins →
    rd.toNat ≠ 0 →
    (∀ s_pc : ExecSt,
       s_pc.regs .nextPC = BitVec.addInt pc 2 →
       gprAgree s_pc.regs rs →
       exec (execute ins) s_pc = some (RETIRE_SUCCESS, s_pc.setGpr rd wval)) →
    k ≤ kend →
    (∀ GD s1, G GD → RetX cpu rs k s1 → s1.atK = (AxOpsem.grow GD i).length →
      ⊢ postLifting Φ i s1) →
    ⊢ (∀ s' rs' k',
         ⌜RetX cpu rs' k' s'⌝ -∗ ⌜k' = k + fcntS rs pc⌝ -∗ ⌜ctrlOkS T satp0 rs'⌝ -∗
         ⌜rs' .PC = BitVec.addInt pc 2⌝ -∗
         ⌜∀ r : BitVec 5, r.toNat ≠ 0 →
            uxaXget rs' r = if r = rd then wval else uxaXget rs r⌝ -∗
         ⌜warm fcntS rs' pc⌝ -∗
         wpd .MaybeStuck i s' Φ) -∗
       wpd .MaybeStuck i s Φ :=
  XGprWriteC (imgS σi) i cpu (ctrlOkS T satp0) (textAtS σi T) fcntS
    (spineCntS σi T satp0 hmode hasid hppn) Htext Hflow G HG kend HGl Φ Hmid s rs k pc ins rd wval

include hmode hasid hppn Htext Hflow in
/-- Rocq `wpd_block_closed_S`: `wpdBlockClosed` at `spineCntS` (deviation 2: the `Htail` form;
the row length is `k0 + fcntS rs0 pc`, Rocq `+ 1`). -/
theorem wpdBlockClosedS (pc : BitVec 64) (imm : BitVec 6) (s0 : Athread) (rs0 : RegFile)
    (k0 : Nat) :
    RetX cpu rs0 k0 s0 → ctrlOkS T satp0 rs0 → rs0 .PC = pc →
    textOkC (imgS σi) (ctrlOkS T satp0) (textAtS σi T) pc ICmv →
    textOkC (imgS σi) (ctrlOkS T satp0) (textAtS σi T) (BitVec.addInt pc 2) (ICaddiw imm) →
    WeakKpt.svpnOf (BitVec.addInt pc 2) = WeakKpt.svpnOf pc →
    (∀ rs, ctrlOkS T satp0 rs → rs .PC = blkEnd pc → warm fcntS rs pc →
      (∀ r : BitVec 5, r.toNat ≠ 0 →
        AxSymEngine3.gpr r rs = if r = a05 then blkW2 rs0 imm else AxSymEngine3.gpr r rs0) →
      ∀ (tick : Bool) (t : ExecSt), regsAgree AxRunClose.pinReg t.regs rs →
        EvB (imgS σi) (fun _ _ => False) (fun _ _ _ => False) (riscvStep tick) t 0) →
    (∀ GD, rvwmoCatConsistent GD →
      AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜(AxOpsem.grow GD i).length = k0 + fcntS rs0 pc⌝) →
    ⊢ wpd .MaybeStuck i s0 (ΦRet (GF := GF) cpu (PBlk pc rs0 imm)) :=
  wpdBlockClosed (imgS σi) i cpu _ _ fcntS (spineCntS σi T satp0 hmode hasid hppn) Htext Hflow
    pc imm s0 rs0 k0

include hmode hasid hppn Htext Hflow in
/-- (Lean-only, deviation 2) `wpdBlockClosedS` in Rocq's premise shape
`textAtS σi T (blkEnd pc) h3`, plus a cold tail page (`AxSymCtl.wpdBlockClosedCold`). -/
theorem AxSymCtl5.wpdBlockClosedSCold (pc : BitVec 64) (imm : BitVec 6) (s0 : Athread)
    (rs0 : RegFile) (k0 : Nat) (h3 : BitVec 16) :
    RetX cpu rs0 k0 s0 → ctrlOkS T satp0 rs0 → rs0 .PC = pc →
    textOkC (imgS σi) (ctrlOkS T satp0) (textAtS σi T) pc ICmv →
    textOkC (imgS σi) (ctrlOkS T satp0) (textAtS σi T) (BitVec.addInt pc 2) (ICaddiw imm) →
    WeakKpt.svpnOf (BitVec.addInt pc 2) = WeakKpt.svpnOf pc →
    textAtS σi T (blkEnd pc) h3 →
    (∀ rs, warm fcntS rs pc → 1 ≤ fcntS rs (blkEnd pc)) →
    (∀ GD, rvwmoCatConsistent GD →
      AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜(AxOpsem.grow GD i).length = k0 + fcntS rs0 pc⌝) →
    ⊢ wpd .MaybeStuck i s0 (ΦRet (GF := GF) cpu (PBlk pc rs0 imm)) :=
  AxSymCtl.wpdBlockClosedCold (imgS σi) i cpu _ _ fcntS (spineCntS σi T satp0 hmode hasid hppn)
    Htext Hflow pc imm s0 rs0 k0 h3

end closedS

/-! ### At `axGA2` with the real protocol `protInv` (`blkGa2`): only graph facts remain -/

section closedGa2
variable {hlc : HasLC} {GF : BundledGFunctors.{0,0,0}} [InvGS_gen hlc GF] [AxannotGS GF]
  [pol : Axpol] [AxlogG GF Hent]
variable (GD0 : Gdexec) (γ : GName)
variable (σi : ExecSt) (T : PTree) (satp0 : BitVec 64) (i : Agent) (cpu : CPU)
variable (hmode : _get_Satp64_Mode (Mk_Satp64 satp0) = 8#4)
  (hasid : zero_extend (m := 16) (satp_to_asid satp0) = 0#16)
  (hppn : BitVec.setWidth 44 (satp_to_ppn satp0) = T.base)
variable (Hfix : textFixed GD0 i (imgS σi))

/-- (Lean-only) the row-length premise at `blkGa2 GD0 γ` from the one graph fact. -/
theorem AxSymCtl5.hlenGa2 (n : Nat) (Hlen : (AxOpsem.grow GD0 i).length = n) :
    ∀ GD, rvwmoCatConsistent GD →
      AxirisG.gconstInterp (GF := GF) (self := blkGa2 GD0 γ) GD ⊢
        ⌜(AxOpsem.grow GD i).length = n⌝ := by
  intro GD _
  show iprop(⌜GD = GD0⌝) ⊢ _
  iintro %h
  subst h
  ipureintro
  exact Hlen

include hmode hasid hppn Hfix in
/-- Rocq `wpd_block_closed_ga2` (deviation 2: `Htail` form, row length `k0 + fcntS rs0 pc`). -/
theorem wpdBlockClosedGa2 (pc : BitVec 64) (imm : BitVec 6) (s0 : Athread) (rs0 : RegFile)
    (k0 : Nat) :
    RetX cpu rs0 k0 s0 → ctrlOkS T satp0 rs0 → rs0 .PC = pc →
    textOkC (imgS σi) (ctrlOkS T satp0) (textAtS σi T) pc ICmv →
    textOkC (imgS σi) (ctrlOkS T satp0) (textAtS σi T) (BitVec.addInt pc 2) (ICaddiw imm) →
    WeakKpt.svpnOf (BitVec.addInt pc 2) = WeakKpt.svpnOf pc →
    (∀ rs, ctrlOkS T satp0 rs → rs .PC = blkEnd pc → warm fcntS rs pc →
      (∀ r : BitVec 5, r.toNat ≠ 0 →
        AxSymEngine3.gpr r rs = if r = a05 then blkW2 rs0 imm else AxSymEngine3.gpr r rs0) →
      ∀ (tick : Bool) (t : ExecSt), regsAgree AxRunClose.pinReg t.regs rs →
        EvB (imgS σi) (fun _ _ => False) (fun _ _ _ => False) (riscvStep tick) t 0) →
    (AxOpsem.grow GD0 i).length = k0 + fcntS rs0 pc →
    ⊢ @wpd hlc GF _ (blkGa2 GD0 γ) pol .MaybeStuck i s0 (ΦRet (GF := GF) cpu (PBlk pc rs0 imm)) := by
  intro HR0 Hc0 HPC0 Htx1 Htx2 Hpg Htail Hlen
  exact @wpdBlockClosedS hlc GF _ (blkGa2 GD0 γ) pol σi T satp0 i cpu hmode hasid hppn
    (HtextGa2 GD0 GName Unit _ γ (imgS σi) i Hfix)
    (fun GD ls k hc hx => HflowGa2 GD0 GName Unit _ γ (imgS σi) i
      (fun GD σ s e Hnin Hnw => protInvReadStep γ GD s e Hnin Hnw) GD ls k hc hx)
    pc imm s0 rs0 k0 HR0 Hc0 HPC0 Htx1 Htx2 Hpg Htail
    (AxSymCtl5.hlenGa2 GD0 γ i _ Hlen)

include hmode hasid hppn Hfix in
/-- (Lean-only, deviation 2) `wpdBlockClosedGa2` in Rocq's premise shape (cold tail page). -/
theorem AxSymCtl5.wpdBlockClosedGa2Cold (pc : BitVec 64) (imm : BitVec 6) (s0 : Athread)
    (rs0 : RegFile) (k0 : Nat) (h3 : BitVec 16) :
    RetX cpu rs0 k0 s0 → ctrlOkS T satp0 rs0 → rs0 .PC = pc →
    textOkC (imgS σi) (ctrlOkS T satp0) (textAtS σi T) pc ICmv →
    textOkC (imgS σi) (ctrlOkS T satp0) (textAtS σi T) (BitVec.addInt pc 2) (ICaddiw imm) →
    WeakKpt.svpnOf (BitVec.addInt pc 2) = WeakKpt.svpnOf pc →
    textAtS σi T (blkEnd pc) h3 →
    (∀ rs, warm fcntS rs pc → 1 ≤ fcntS rs (blkEnd pc)) →
    (AxOpsem.grow GD0 i).length = k0 + fcntS rs0 pc →
    ⊢ @wpd hlc GF _ (blkGa2 GD0 γ) pol .MaybeStuck i s0 (ΦRet (GF := GF) cpu (PBlk pc rs0 imm)) := by
  intro HR0 Hc0 HPC0 Htx1 Htx2 Hpg Hat3 Hcold Hlen
  exact @AxSymCtl5.wpdBlockClosedSCold hlc GF _ (blkGa2 GD0 γ) pol σi T satp0 i cpu hmode hasid
    hppn (HtextGa2 GD0 GName Unit _ γ (imgS σi) i Hfix)
    (fun GD ls k hc hx => HflowGa2 GD0 GName Unit _ γ (imgS σi) i
      (fun GD σ s e Hnin Hnw => protInvReadStep γ GD s e Hnin Hnw) GD ls k hc hx)
    pc imm s0 rs0 k0 h3 HR0 Hc0 HPC0 Htx1 Htx2 Hpg Hat3 Hcold
    (AxSymCtl5.hlenGa2 GD0 γ i _ Hlen)

include hmode hasid hppn Hfix in
/-- Rocq `wpd_cmv_closed_ga2` (deviation 2: `Htail` form). -/
theorem wpdCmvClosedGa2 (pc : BitVec 64) (s0 : Athread) (rs0 : RegFile) (k0 : Nat) :
    RetX cpu rs0 k0 s0 → ctrlOkS T satp0 rs0 → rs0 .PC = pc →
    textOkC (imgS σi) (ctrlOkS T satp0) (textAtS σi T) pc ICmv →
    (∀ rs, ctrlOkS T satp0 rs → rs .PC = BitVec.addInt pc 2 → warm fcntS rs pc →
      (∀ r : BitVec 5, r.toNat ≠ 0 →
        AxSymEngine3.gpr r rs = if r = a05 then blkW1 rs0 else AxSymEngine3.gpr r rs0) →
      ∀ (tick : Bool) (t : ExecSt), regsAgree AxRunClose.pinReg t.regs rs →
        EvB (imgS σi) (fun _ _ => False) (fun _ _ _ => False) (riscvStep tick) t 0) →
    (AxOpsem.grow GD0 i).length = k0 + fcntS rs0 pc →
    ⊢ @wpd hlc GF _ (blkGa2 GD0 γ) pol .MaybeStuck i s0 (ΦRet (GF := GF) cpu (POne pc rs0)) := by
  intro HR0 Hc0 HPC0 Htx1 Htail Hlen
  exact @wpdCmvClosed hlc GF _ (blkGa2 GD0 γ) pol (imgS σi) i cpu _ _ fcntS
    (spineCntS σi T satp0 hmode hasid hppn)
    (HtextGa2 GD0 GName Unit _ γ (imgS σi) i Hfix)
    (fun GD ls k hc hx => HflowGa2 GD0 GName Unit _ γ (imgS σi) i
      (fun GD σ s e Hnin Hnw => protInvReadStep γ GD s e Hnin Hnw) GD ls k hc hx)
    pc s0 rs0 k0 HR0 Hc0 HPC0 Htx1 Htail (AxSymCtl5.hlenGa2 GD0 γ i _ Hlen)

include hmode hasid hppn Hfix in
/-- (Lean-only, deviation 2) `wpdCmvClosedGa2` in Rocq's premise shape (cold tail page). -/
theorem AxSymCtl5.wpdCmvClosedGa2Cold (pc : BitVec 64) (s0 : Athread) (rs0 : RegFile) (k0 : Nat)
    (h1 : BitVec 16) :
    RetX cpu rs0 k0 s0 → ctrlOkS T satp0 rs0 → rs0 .PC = pc →
    textOkC (imgS σi) (ctrlOkS T satp0) (textAtS σi T) pc ICmv →
    textAtS σi T (BitVec.addInt pc 2) h1 →
    (∀ rs, warm fcntS rs pc → 1 ≤ fcntS rs (BitVec.addInt pc 2)) →
    (AxOpsem.grow GD0 i).length = k0 + fcntS rs0 pc →
    ⊢ @wpd hlc GF _ (blkGa2 GD0 γ) pol .MaybeStuck i s0 (ΦRet (GF := GF) cpu (POne pc rs0)) := by
  intro HR0 Hc0 HPC0 Htx1 Hat2 Hcold Hlen
  exact @AxSymCtl5.wpdCmvClosedCold hlc GF _ (blkGa2 GD0 γ) pol (imgS σi) i cpu _ _ fcntS
    (spineCntS σi T satp0 hmode hasid hppn)
    (HtextGa2 GD0 GName Unit _ γ (imgS σi) i Hfix)
    (fun GD ls k hc hx => HflowGa2 GD0 GName Unit _ γ (imgS σi) i
      (fun GD σ s e Hnin Hnw => protInvReadStep γ GD s e Hnin Hnw) GD ls k hc hx)
    pc s0 rs0 k0 h1 HR0 Hc0 HPC0 Htx1 Hat2 Hcold (AxSymCtl5.hlenGa2 GD0 γ i _ Hlen)

end closedGa2

/-! # 3. The concrete probe (`AxSmodeProbe` / `gpT`) -/

/-- Rocq `pT_text_ok_c`: `textOkC` for `c.mv a0, ra` at the probe's pc (∀ regime states). -/
theorem pTTextOkC :
    textOkC (imgS nvST) (ctrlOkS pT nvSSatp) (textAtS nvST pT) (AxEpiProbe.w64 sPc) ICmv :=
  ⟨pH, pI0, pTTextAt,
    fun t Hc => EvAOfRfF _ _ rfFDecodePH t pI0 t (execDecodePH t Hc.2.2.1),
    nrdOfRfF _ rfFDecodePH,
    fun t => EvAOfRfF _ _ rfFExecutePI0 t _ t (execExecuteCMV (.Regidx a05) (.Regidx ra5) t),
    nrdOfRfF _ rfFExecutePI0,
    rf0ExecuteRTYPEADD ra5 0#5 a05⟩

/-- Rocq `pH1`: the probe's NEXT halfword (0x0081 at sPc + 2, 2 mod 4). -/
def pH1 : BitVec 16 := 0x0081#16

/-- Rocq `pT_vpn2`. -/
theorem pTVpn2 : WeakKpt.svpnOf (BitVec.addInt (AxEpiProbe.w64 sPc) 2) = pvpn := by
  decide +kernel

/-- Rocq `pT_text_at2`: the next halfword is text too. -/
theorem pTTextAt2 : textAtS nvST pT (BitVec.addInt (AxEpiProbe.w64 sPc) 2) pH1 := by
  unfold textAtS
  rw [pTVpn2]
  refine ⟨pP2, pP1, pW, AxEpiProbe.w64 (sPc + 2), pTMaps, pTSlot2, pTSlot1, pTSlot0, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_⟩
  · intro mxr dosum s
    cases mxr <;> cases dosum <;> ax_epi_ledger_krfl
  · decide +kernel
  · unfold ptePbmt0; decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · rw [if_neg (show ¬ is_aligned_vaddr (.Virtaddr (BitVec.addInt (AxEpiProbe.w64 sPc) 2)) 4 = true
      by decide +kernel)]
    refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
    unfold BytesAt
    decide +kernel

/-- Rocq `pT_fcnt_cold` (Stage C: 3 walk reads; Rocq 4 = 3 + the fetch). -/
theorem pTFcntCold : fcntS nvSRs (AxEpiProbe.w64 sPc) = 3 := by decide +kernel

/-! ### (Lean-only) WHY THE CAPSTONE'S TAIL RUNS PAST THE ROW END (deviation 3)

The probe run from `nvST`, five `riscvStep false` steps, traced by `AxSmodeProbe`'s `mtr`
(events `(0 = read, akTag, size, pa)`; `akTag` 1 = i-fetch, 2 = walk): the `c.mv` at `sPc` makes
the three cold walk reads (`gpT`'s row) and its fetch; the next three instructions (0x0081 at
sPc + 2, c.nop at sPc + 4 and sPc + 6) make NO graph read (warm page; the fetch is an admin
step); the fetch at sPc + 8 has no bytes (stuck, code 2).  So no budget-0 stop certificate
exists at sPc + 2, and the tail page is warm: neither tail form of `wpdCmvClosed` applies; §4
follows the three register-only steps and stops at the imageless fetch (Q16). -/

/-- (Lean-only) the first `n` steps' memory traces, with each step's start pc. -/
noncomputable def AxSymCtl5.runTrace : Nat → ExecSt →
    List (((List AxSmodeProbe.mev × Nat) ⊕ (Nat × List AxSmodeProbe.mev)) × Nat)
  | 0, _ => []
  | n + 1, t => (mtr (riscvStep false) t [] 0, (t.regs .PC).toNat) ::
      (match mfin (riscvStep false) t with
       | some t' => AxSymCtl5.runTrace n t'
       | none => [])

/-- (Lean-only, deviation 3) the probe's run past the `c.mv`: no graph read before a stuck,
imageless fetch. -/
theorem AxSymCtl5.probeTailTrace :
    AxSymCtl5.runTrace 5 nvST =
      [ (.inl ([(0, 2, 8, 0x80010010), (0, 2, 8, 0x80011000), (0, 2, 8, 0x80012000),
                (0, 1, 4, 0x80000000)], 1), 0x80000000),
        (.inl ([(0, 1, 2, 0x80000002)], 0), 0x80000002),
        (.inl ([(0, 1, 4, 0x80000004)], 0), 0x80000004),
        (.inl ([(0, 1, 2, 0x80000006)], 0), 0x80000006),
        (.inr (2, [(0, 1, 4, 0x80000008)]), 0x80000008) ] := by
  ax_epi_ledger_krfl

/-- (Lean-only, deviation 3) THE CAPSTONE'S FIRST STEP: `c.mv a0, ra` at the probe's S-mode
state (cold TLB), hart 0 of `gpT` at `blkGa2 gpT γ` (real `protInv`), every premise discharged;
the run ends EXACTLY at `gpT`'s row end (`fcntS nvSRs pc = 3 = gpTRowLen`), with a0 = ra, the
regime, pc + 2 and the warm page handed to the continuation (the tail, deviation 3). -/
theorem AxSymCtl5.wpdCmvProbeRowEnd {hlc : HasLC} {GF : BundledGFunctors.{0,0,0}}
    [InvGS_gen hlc GF] [AxannotGS GF] [pol : Axpol] [AxlogG GF Hent] (γ : GName) (cpu : CPU)
    (s : Athread) :
    RetX cpu nvSRs 0 s →
    ⊢ (∀ s' rs', ⌜RetX cpu rs' (AxOpsem.grow gpT 0).length s'⌝ -∗ ⌜ctrlOkS pT nvSSatp rs'⌝ -∗
         ⌜rs' .PC = BitVec.addInt (AxEpiProbe.w64 sPc) 2⌝ -∗
         ⌜∀ r : BitVec 5, r.toNat ≠ 0 →
            AxSymEngine3.gpr r rs' = if r = a05 then blkW1 nvSRs else AxSymEngine3.gpr r nvSRs⌝ -∗
         ⌜warm fcntS rs' (AxEpiProbe.w64 sPc)⌝ -∗
         @wpd hlc GF _ (blkGa2 gpT γ) pol .MaybeStuck 0 s'
           (ΦRet (GF := GF) cpu (POne (AxEpiProbe.w64 sPc) nvSRs))) -∗
       @wpd hlc GF _ (blkGa2 gpT γ) pol .MaybeStuck 0 s
         (ΦRet (GF := GF) cpu (POne (AxEpiProbe.w64 sPc) nvSRs)) := by
  intro HR
  have HX := @XGprWriteCS hlc GF _ (blkGa2 gpT γ) pol nvST pT nvSSatp 0 cpu nvSSatpMode
    nvSSatpAsid pTBase (HtextGa2 gpT GName Unit _ γ (imgS nvST) 0 gpTTextFixed)
    (fun GD ls k hc hx => HflowGa2 gpT GName Unit _ γ (imgS nvST) 0
      (fun GD σ s e Hnin Hnw => protInvReadStep γ GD s e Hnin Hnw) GD ls k hc hx)
    (fun GD => (AxOpsem.grow GD 0).length = 3) (AxSymCtl5.hlenGa2 gpT γ 0 3 gpTRowLen)
    3 (fun _ h => h) (ΦRet (GF := GF) cpu (POne (AxEpiProbe.w64 sPc) nvSRs))
    (@ΦRetMid hlc GF _ (blkGa2 gpT γ) 0 cpu _ _) s nvSRs 0 (AxEpiProbe.w64 sPc) ICmv a05 (blkW1 nvSRs) HR (nvSCtrlOk pT)
    nvSPc pTTextOkC (by decide) (fun s_pc _ Hag => certCmv nvSRs s_pc Hag) (by omega)
    (fun _ s1 _ HR1 _ => @ΦRetBoundary hlc GF _ (blkGa2 gpT γ) 0 cpu _ nvSRs 0 s1
      (fun rs' Hag Hpc => ((addVecIntNe (AxEpiProbe.w64 sPc) 2 ⟨by decide, by decide⟩)
        (Hpc.symm.trans ((Hag .PC (AxSymEngine2.notPin _ (by decide) (by decide))).trans
          nvSPc))).elim) HR1)
  iintro C
  iapply HX
  iintro %s' %rs' %k' %HR' %Hk' %Hc' %HPC' %Hg' %Hw'
  rw [pTFcntCold] at Hk'
  have HR'' : RetX cpu rs' (AxOpsem.grow gpT 0).length s' := by
    rw [gpTRowLen]; rw [Hk'] at HR'; exact HR'
  iapply C $$ %s' %rs' %HR'' %Hc' %HPC' %Hg' %Hw'

/-! # 4. (Q16) THE CONCRETE CAPSTONE: the tail ends at the imageless fetch

After the `c.mv` (row end, `wpdCmvProbeRowEnd`) the probe runs `c.addi ra, 0` (0x0081, a HINT
writing ra := ra) at pc2, `c.nop` (0x0001) at pc4 (a 4-byte fetch) and pc6, all on the warm page
(no graph read, the row stays at its end); the fetch at pc8 has no image bytes: `EvB.ebNf`.  The
stop certificate there comes from two EXTENSIONS of the image filling the hole with different
compressed words (`AxSymCtl5.holeSt`): `scFetchS` certifies each fetch, `AxSymCtl.EvBMeet0`
meets them over `imgS nvST` — their results disagree, so every path ends at the hole. -/

/-- (Lean-only) the probe's tail pcs. -/
abbrev AxSymCtl5.pc2 : BitVec 64 := BitVec.addInt (AxEpiProbe.w64 sPc) 2
abbrev AxSymCtl5.pc4 : BitVec 64 := BitVec.addInt AxSymCtl5.pc2 2
abbrev AxSymCtl5.pc6 : BitVec 64 := BitVec.addInt AxSymCtl5.pc4 2
abbrev AxSymCtl5.pc8 : BitVec 64 := BitVec.addInt AxSymCtl5.pc6 2
/-- (Lean-only) the physical address of the imageless fetch. -/
abbrev AxSymCtl5.pa8 : BitVec 64 := AxEpiProbe.w64 (sPc + 8)

theorem AxSymCtl5.pTVpn4 : WeakKpt.svpnOf AxSymCtl5.pc4 = pvpn := by decide +kernel
theorem AxSymCtl5.pTVpn6 : WeakKpt.svpnOf AxSymCtl5.pc6 = pvpn := by decide +kernel
theorem AxSymCtl5.pTVpn8 : WeakKpt.svpnOf AxSymCtl5.pc8 = pvpn := by decide +kernel

/-- (Lean-only) the leaf PTE's fetch checks. -/
theorem AxSymCtl5.pWChk : ∀ mxr dosum : Bool,
    pteCheckOk (.InstructionFetch ()) .Supervisor mxr dosum pW := by
  intro mxr dosum s
  cases mxr <;> cases dosum <;> ax_epi_ledger_krfl

/-- (Lean-only) `textAtS` on the probe's page (the walk of `pTMaps`), any state with the slots. -/
theorem AxSymCtl5.textAtPage (σ : ExecSt) (pc pa : BitVec 64) (h : BitVec 16)
    (hv : WeakKpt.svpnOf pc = pvpn)
    (hs2 : WeakWalkEff.ptSlotMem σ (AxPtProt.ptAddr2 pT pvpn) pP2)
    (hs1 : WeakWalkEff.ptSlotMem σ (AxPtProt.ptAddr1 pP2 pvpn) pP1)
    (hs0 : WeakWalkEff.ptSlotMem σ (AxPtProt.ptAddr0 pP1 pvpn) pW)
    (hcanon : (pc != sign_extend (m := 64) (Sail.BitVec.extractLsb pc 38 0)) = false)
    (hout : zero_extend (m := 64) (ppn0 pW +++ Sail.BitVec.extractLsb pc
      (Functions.pagesize_bits - 1) 0) = pa)
    (hb0 : (Sail.BitVec.access pc 0 != 0#1) = false) (hrvc : isRVC h = true)
    (hal : if is_aligned_vaddr (.Virtaddr pc) 4 then
       ∃ w32 : BitVec 32, Sail.BitVec.extractLsb w32 15 0 = h ∧
         inRam pa 4 ∧ is_aligned_paddr (.Physaddr pa) 4 = true ∧ BytesAt σ pa 4 w32
     else
       (Sail.BitVec.access pc 1 != 0#1) = true ∧
         inRam pa 2 ∧ is_aligned_paddr (.Physaddr pa) 2 = true ∧ BytesAt σ pa 2 h) :
    textAtS σ pT pc h := by
  unfold textAtS
  rw [hv]
  exact ⟨pP2, pP1, pW, pa, pTMaps, hs2, hs1, hs0, AxSymCtl5.pWChk, by decide +kernel,
    by unfold ptePbmt0; decide +kernel, hcanon, hout, hb0, hrvc, hal⟩

/-! ### The decodes: `c.addi ra, 0` (0x0081) and `c.nop` (0x0001) -/

/-- (Lean-only) `c.addi ra, 0`, decoded, and its expansion. -/
def AxSymCtl5.pI1 : instruction := .C_ADDI (0#6, .Regidx ra5)
def AxSymCtl5.pIns1 : instruction :=
  .ITYPE (sign_extend (m := 12) (0#6 : BitVec 6), .Regidx ra5, .Regidx ra5, .ADDI)
/-- (Lean-only) `c.nop` (at pc4 and pc6), decoded. -/
def AxSymCtl5.pHN : BitVec 16 := 0x0001#16
def AxSymCtl5.pIN : instruction := .C_NOP 0#6

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
theorem AxSymCtl5.rfFDecodePH1 : rfF (ext_decode_compressed pH1) := by
  unfold pH1 ext_decode_compressed encdec_compressed_backwards
  simp (config := { decide := true }) only [↓reduceIte]
  rff_auto

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
theorem AxSymCtl5.rfFDecodePHN : rfF (ext_decode_compressed AxSymCtl5.pHN) := by
  unfold AxSymCtl5.pHN ext_decode_compressed encdec_compressed_backwards
  simp (config := { decide := true }) only [↓reduceIte]
  rff_auto

theorem AxSymCtl5.execDecodePH1 (s : ExecSt) : s.regs .misa = misaC →
    exec (ext_decode_compressed pH1) s = some (AxSymCtl5.pI1, s) := by
  intro H
  have hw : runRead drefMisa (ext_decode_compressed pH1) = some (AxSymCtl5.pI1, true) := by
    ax_epi_ledger_krfl
  refine execOfRunRead drefMisa _ s _ true ?_ hw
  intro r v hv
  unfold drefMisa at hv
  split at hv <;> simp only [Option.some.injEq, reduceCtorEq] at hv
  subst hv
  exact H

theorem AxSymCtl5.execDecodePHN (s : ExecSt) : s.regs .misa = misaC →
    exec (ext_decode_compressed AxSymCtl5.pHN) s = some (AxSymCtl5.pIN, s) := by
  intro H
  have hw : runRead drefMisa (ext_decode_compressed AxSymCtl5.pHN) = some (AxSymCtl5.pIN, true) := by
    ax_epi_ledger_krfl
  refine execOfRunRead drefMisa _ s _ true ?_ hw
  intro r v hv
  unfold drefMisa at hv
  split at hv <;> simp only [Option.some.injEq, reduceCtorEq] at hv
  subst hv
  exact H

theorem AxSymCtl5.rfFExecutePI1 : rfF (execute AxSymCtl5.pI1) := by
  show rfF (pure (execute_C_ADDI 0#6 (.Regidx ra5)))
  exact True.intro

theorem AxSymCtl5.rfFExecutePIN : rfF (execute AxSymCtl5.pIN) := by
  show rfF (pure (execute_C_NOP 0#6))
  exact True.intro

/-- (Lean-only) `textOkC` for `c.addi ra, 0` at pc2 (∀ regime states). -/
theorem AxSymCtl5.pTTextOkC1 :
    textOkC (imgS nvST) (ctrlOkS pT nvSSatp) (textAtS nvST pT) AxSymCtl5.pc2 AxSymCtl5.pIns1 :=
  ⟨pH1, AxSymCtl5.pI1, pTTextAt2,
    fun t Hc => EvAOfRfF _ _ AxSymCtl5.rfFDecodePH1 t _ t (AxSymCtl5.execDecodePH1 t Hc.2.2.1),
    nrdOfRfF _ AxSymCtl5.rfFDecodePH1,
    fun t => EvAOfRfF _ _ AxSymCtl5.rfFExecutePI1 t _ t rfl,
    nrdOfRfF _ AxSymCtl5.rfFExecutePI1,
    rf0ExecuteITYPEADDI ra5 ra5 _⟩

/-- (Lean-only) the SC certificate of the expansion: ra := ra + 0. -/
theorem AxSymCtl5.certAddi0 (rs1 : RegFile) (s_pc : ExecSt) :
    gprAgree s_pc.regs rs1 →
    exec (execute AxSymCtl5.pIns1) s_pc = some (RETIRE_SUCCESS, s_pc.setGpr ra5
      (AxSymEngine3.gpr ra5 rs1 + sign_extend (m := 64) (sign_extend (m := 12) (0#6 : BitVec 6)))) := by
  intro Hag
  unfold AxSymCtl5.pIns1
  rw [execExecuteITYPEADDIGpr ra5 ra5 _ s_pc]
  unfold gprAddiVal
  have h : s_pc.gpr ra5 = AxSymEngine3.gpr ra5 rs1 := Hag ra5 (by decide)
  rw [h]

theorem AxSymCtl5.pTTextAt4 : textAtS nvST pT AxSymCtl5.pc4 AxSymCtl5.pHN :=
  AxSymCtl5.textAtPage nvST _ (AxEpiProbe.w64 (sPc + 4)) _ AxSymCtl5.pTVpn4 pTSlot2 pTSlot1 pTSlot0
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by
      rw [if_pos (show is_aligned_vaddr (.Virtaddr AxSymCtl5.pc4) 4 = true by decide +kernel)]
      refine ⟨0x00010001#32, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
      unfold BytesAt
      decide +kernel)

theorem AxSymCtl5.pTTextAt6 : textAtS nvST pT AxSymCtl5.pc6 AxSymCtl5.pHN :=
  AxSymCtl5.textAtPage nvST _ (AxEpiProbe.w64 (sPc + 6)) _ AxSymCtl5.pTVpn6 pTSlot2 pTSlot1 pTSlot0
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by
      rw [if_neg (show ¬ is_aligned_vaddr (.Virtaddr AxSymCtl5.pc6) 4 = true by decide +kernel)]
      refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
      unfold BytesAt
      decide +kernel)

/-- (Lean-only) `AxSymCtl.textOkNop` for `c.nop` at any probe pc holding it. -/
theorem AxSymCtl5.pTTextOkNop (pc : BitVec 64) (Hat : textAtS nvST pT pc AxSymCtl5.pHN) :
    AxSymCtl.textOkNop (imgS nvST) (ctrlOkS pT nvSSatp) (textAtS nvST pT) pc :=
  ⟨AxSymCtl5.pHN, AxSymCtl5.pIN, Hat,
    fun t Hc => EvAOfRfF _ _ AxSymCtl5.rfFDecodePHN t _ t (AxSymCtl5.execDecodePHN t Hc.2.2.1),
    nrdOfRfF _ AxSymCtl5.rfFDecodePHN,
    fun t => EvAOfRfF _ _ AxSymCtl5.rfFExecutePIN t _ t rfl,
    nrdOfRfF _ AxSymCtl5.rfFExecutePIN⟩

/-! ### The imageless fetch at pc8: two hole fillings, met -/

/-- (Lean-only) the probe's state with the hole at `pa8` (4 bytes) filled by `w`. -/
def AxSymCtl5.holeSt (w : BitVec 32) : ExecSt :=
  ⟨nvST.regs,
   fun a => (nvST.mem a).or
     (if (a - AxSymCtl5.pa8).toNat < 4 then some (nthByte (n := 4) w (a - AxSymCtl5.pa8).toNat)
      else none),
   nvST.dev⟩

theorem AxSymCtl5.holeSub (w : BitVec 32) :
    ∀ a v, nvST.mem a = some v → (AxSymCtl5.holeSt w).mem a = some v := by
  intro a v h
  show (nvST.mem a).or _ = some v
  rw [h]
  rfl

theorem AxSymCtl5.imgSub (w : BitVec 32) :
    ∀ a v, imgS nvST a = some v → imgS (AxSymCtl5.holeSt w) a = some v := by
  intro a v h
  unfold imgS imgOf at h ⊢
  by_cases hr : 0 ≤ a ∧ a < 2 ^ 64
  · rw [if_pos hr] at h ⊢
    exact AxSymCtl5.holeSub w _ _ h
  · rw [if_neg hr] at h
    cases h

theorem AxSymCtl5.slotSub {σ σ' : ExecSt} (H : ∀ a v, σ.mem a = some v → σ'.mem a = some v)
    {a p : BitVec 64} : WeakWalkEff.ptSlotMem σ a p → WeakWalkEff.ptSlotMem σ' a p :=
  fun ⟨hb, h1, h2⟩ => ⟨fun j hj => H _ _ (hb j hj), h1, h2⟩

theorem AxSymCtl5.holeTextAt (w : BitVec 32) (h : BitVec 16)
    (hw : BytesAt (AxSymCtl5.holeSt w) AxSymCtl5.pa8 4 w)
    (hl : Sail.BitVec.extractLsb w 15 0 = h) (hr : isRVC h = true) :
    textAtS (AxSymCtl5.holeSt w) pT AxSymCtl5.pc8 h :=
  AxSymCtl5.textAtPage _ _ AxSymCtl5.pa8 h AxSymCtl5.pTVpn8
    (AxSymCtl5.slotSub (AxSymCtl5.holeSub w) pTSlot2)
    (AxSymCtl5.slotSub (AxSymCtl5.holeSub w) pTSlot1)
    (AxSymCtl5.slotSub (AxSymCtl5.holeSub w) pTSlot0)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) hr
    (by
      rw [if_pos (show is_aligned_vaddr (.Virtaddr AxSymCtl5.pc8) 4 = true by decide +kernel)]
      exact ⟨w, hl, by decide +kernel, by decide +kernel, hw⟩)

theorem AxSymCtl5.holeBytes1 : BytesAt (AxSymCtl5.holeSt 0x00000001#32) AxSymCtl5.pa8 4
    0x00000001#32 := by
  unfold BytesAt
  decide +kernel

theorem AxSymCtl5.holeBytes2 : BytesAt (AxSymCtl5.holeSt 0x00000005#32) AxSymCtl5.pa8 4
    0x00000005#32 := by
  unfold BytesAt
  decide +kernel

/-- (Lean-only) THE IMAGELESS FETCH: at budget 0, the fetch at pc8 (any regime state) never
returns over `imgS nvST` (stuck ends accepted). -/
theorem AxSymCtl5.fetchStop8 (t : ExecSt) (Hc : ctrlOkS pT nvSSatp t.regs)
    (HPC : t.regs .PC = AxSymCtl5.pc8) :
    EvB (imgS nvST) (fun _ _ => True) (fun _ _ _ => False) (fetch ()) t 0 := by
  obtain ⟨_, -, -, -, Hf1⟩ := scFetchS (AxSymCtl5.holeSt 0x00000001#32) pT nvSSatp nvSSatpMode
    nvSSatpAsid pTBase t _ _ Hc HPC
    (AxSymCtl5.holeTextAt _ 0x0001#16 AxSymCtl5.holeBytes1 (by decide +kernel) (by decide +kernel))
  obtain ⟨_, -, -, -, Hf2⟩ := scFetchS (AxSymCtl5.holeSt 0x00000005#32) pT nvSSatp nvSSatpMode
    nvSSatpAsid pTBase t _ _ Hc HPC
    (AxSymCtl5.holeTextAt _ 0x0005#16 AxSymCtl5.holeBytes2 (by decide +kernel) (by decide +kernel))
  have d1 := EvBMono _ _ (fun _ _ => True) _ _ (fetch ()) t 0 (fun _ _ _ => trivial)
    (fun _ _ _ h => h) (Hf1 0)
  have d2 := EvBMono _ _ (fun _ _ => True) _ _ (fetch ()) t 0 (fun _ _ _ => trivial)
    (fun _ _ _ h => h) (Hf2 0)
  have Hm := AxSymCtl.EvBMeet0 (imgS nvST) _ _ (fun _ _ => True) (AxSymCtl5.imgSub _)
    (AxSymCtl5.imgSub _) (fun _ _ => trivial) _ _ (fetch ()) t 0 d1 rfl d2
  refine EvBMono _ _ _ _ _ (fetch ()) t 0 (fun _ _ h => h) ?_ Hm
  rintro _ r _ ⟨⟨-, h1, -⟩, ⟨-, h2, -⟩⟩
  rw [h1] at h2
  injection h2 with h3
  exact absurd h3 (by decide)

/-- (Lean-only) THE STOP CERTIFICATE at pc8 (any regime state there, both ticks). -/
theorem AxSymCtl5.stopCert8 (rs : RegFile) (Hc : ctrlOkS pT nvSSatp rs)
    (HPC : rs .PC = AxSymCtl5.pc8) :
    ∀ (tick : Bool) (t : ExecSt), regsAgree AxRunClose.pinReg t.regs rs →
      EvB (imgS nvST) (fun _ _ => True) (fun _ _ _ => False) (riscvStep tick) t 0 :=
  AxSymCtl.spineStopFetch (imgS nvST) _ _ (spineOkTS nvST pT nvSSatp nvSSatpMode nvSSatpAsid pTBase)
    _ rs _ (fun t Hct Hpc => AxSymCtl5.fetchStop8 t Hct (Hpc.trans HPC)) Hc

/-- (Lean-only) at a boundary off pc2 the post `POne` is vacuous. -/
theorem AxSymCtl5.offBoundary {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF]
    [AxirisG GF] (i : Agent) (cpu : CPU) (G : Gdexec → Prop) (rs : RegFile) (pc : BitVec 64)
    (k : Nat) (HPC : rs .PC = pc) (Hne : pc ≠ AxSymCtl5.pc2) :
    ∀ GD s1, G GD → RetX cpu rs k s1 → s1.atK = (AxOpsem.grow GD i).length →
      ⊢ postLifting (ΦRet (GF := GF) cpu (POne (AxEpiProbe.w64 sPc) nvSRs)) i s1 :=
  fun _ s1 _ HR1 _ => ΦRetBoundary i cpu _ rs k s1
    (fun rs' Hag Hpc => (Hne ((HPC.symm.trans
      (Hag .PC (AxSymEngine2.notPin _ (by decide) (by decide))).symm).trans Hpc)).elim) HR1

/-- Rocq `wpd_cmv_probe_closed` — THE CLOSED CONCRETE WPd (deviation 3, Q16): `c.mv a0, ra` at
the probe's S-mode state (cold TLB), hart 0 of `gpT` at `blkGa2 gpT γ` (real `protInv`); the
c.mv's three walk reads are exactly `gpT`'s row; the tail (`c.addi ra, 0`; `c.nop`; `c.nop`)
reads no graph item and the run ends stuck at the imageless fetch at pc8.  No premise. -/
theorem wpdCmvProbeClosed {hlc : HasLC} {GF : BundledGFunctors.{0,0,0}}
    [InvGS_gen hlc GF] [AxannotGS GF] [pol : Axpol] [AxlogG GF Hent] (γ : GName) (cpu : CPU)
    (s : Athread) :
    RetX cpu nvSRs 0 s →
    ⊢ @wpd hlc GF _ (blkGa2 gpT γ) pol .MaybeStuck 0 s
        (ΦRet (GF := GF) cpu (POne (AxEpiProbe.w64 sPc) nvSRs)) := by
  intro HR
  have Hsc := spineCntS nvST pT nvSSatp nvSSatpMode nvSSatpAsid pTBase
  have Htx := HtextGa2 (GF := GF) gpT GName Unit
    (fun (γ : GName) (GD : Gdexec) (_ : Unit) (s : GSet Geid) => protInv γ GD s) γ (imgS nvST) 0
    gpTTextFixed
  have Hfl := fun GD ls k hc hx => HflowGa2 (GF := GF) (hlc := hlc) (pol := pol) gpT GName Unit
    (fun (γ : GName) (GD : Gdexec) (_ : Unit) (s : GSet Geid) => protInv γ GD s) γ (imgS nvST) 0
    (fun GD σ s e Hnin Hnw => protInvReadStep γ GD s e Hnin Hnw) GD ls k hc hx
  have HG : ∀ GD, rvwmoCatConsistent GD →
      AxirisG.gconstInterp (GF := GF) (self := blkGa2 gpT γ) GD ⊢ ⌜GD = gpT⌝ := by
    intro GD _
    show iprop(⌜GD = gpT⌝) ⊢ _
    iintro %h
    ipureintro
    exact h
  have HGl : ∀ GD, GD = gpT → (AxOpsem.grow GD 0).length = 3 := by
    rintro _ rfl
    exact gpTRowLen
  have HGimg : ∀ GD, GD = gpT → ∀ a, imgS nvST a = none → GD.gdG.gxImg a = none := by
    rintro _ rfl a h
    exact h
  have Hmid := @ΦRetMid hlc GF _ (blkGa2 gpT γ) 0 cpu (POne (AxEpiProbe.w64 sPc) nvSRs)
    (fun GD => GD = gpT)
  have Herr := @AxSymCtl.ΦRetErr hlc GF _ (blkGa2 gpT γ) 0 cpu (POne (AxEpiProbe.w64 sPc) nvSRs)
    (fun GD => GD = gpT)
  iapply (AxSymCtl5.wpdCmvProbeRowEnd γ cpu s HR)
  iintro %s1 %rs1 %HR1 %Hc1 %HPC1 %Hg1 %Hw1
  rw [gpTRowLen] at HR1
  -- pc2: c.addi ra, 0 (warm page: no graph read)
  iapply (@XGprWriteC hlc GF _ (blkGa2 gpT γ) pol (imgS nvST) 0 cpu _ _ fcntS Hsc Htx Hfl
    (fun GD => GD = gpT) HG 3 HGl _ Hmid s1 rs1 3 AxSymCtl5.pc2 AxSymCtl5.pIns1 ra5
    (AxSymEngine3.gpr ra5 rs1 + sign_extend (m := 64) (sign_extend (m := 12) (0#6 : BitVec 6)))
    HR1 Hc1 HPC1 AxSymCtl5.pTTextOkC1 (by decide)
    (fun s_pc _ Hag => AxSymCtl5.certAddi0 rs1 s_pc Hag) (Nat.le_refl _)
    (fun _ s' _ HR' _ => @ΦRetBoundary hlc GF _ (blkGa2 gpT γ) 0 cpu _ rs1 3 s'
      (fun rs' Hag _ r Hr => (AxSymEngine2.uxaXgetAgree _ _ Hag r).trans (Hg1 r Hr)) HR'))
  iintro %s2 %rs2 %k2 %HR2 %Hk2 %Hc2 %HPC2 %-
  iintro %Hw2
  rw [Hw1 _ pTVpn2] at Hk2
  subst Hk2
  -- pc4: c.nop
  iapply (@AxSymCtl.XNopC hlc GF _ (blkGa2 gpT γ) pol (imgS nvST) 0 cpu _ _ fcntS Hsc Htx Hfl
    (fun GD => GD = gpT) HG 3 HGl _ Hmid s2 rs2 3 AxSymCtl5.pc4 HR2 Hc2 HPC2
    (AxSymCtl5.pTTextOkNop _ AxSymCtl5.pTTextAt4) (Nat.le_refl _)
    (@AxSymCtl5.offBoundary hlc GF _ (blkGa2 gpT γ) 0 cpu (fun GD => GD = gpT) rs2 _ 3 HPC2
      (by decide +kernel)))
  iintro %s3 %rs3 %k3 %HR3 %Hk3 %Hc3 %HPC3 %-
  iintro %Hw3
  rw [Hw2 _ (AxSymCtl5.pTVpn4.trans pTVpn2.symm)] at Hk3
  subst Hk3
  -- pc6: c.nop
  iapply (@AxSymCtl.XNopC hlc GF _ (blkGa2 gpT γ) pol (imgS nvST) 0 cpu _ _ fcntS Hsc Htx Hfl
    (fun GD => GD = gpT) HG 3 HGl _ Hmid s3 rs3 3 AxSymCtl5.pc6 HR3 Hc3 HPC3
    (AxSymCtl5.pTTextOkNop _ AxSymCtl5.pTTextAt6) (Nat.le_refl _)
    (@AxSymCtl5.offBoundary hlc GF _ (blkGa2 gpT γ) 0 cpu (fun GD => GD = gpT) rs3 _ 3 HPC3
      (by decide +kernel)))
  iintro %s4 %rs4 %k4 %HR4 %Hk4 %Hc4 %HPC4 %- %-
  rw [Hw3 _ (AxSymCtl5.pTVpn6.trans AxSymCtl5.pTVpn4.symm)] at Hk4
  subst Hk4
  -- pc8: the imageless fetch, stuck
  iapply (@AxSymCtl.wpdTailOfStopStuck hlc GF _ (blkGa2 gpT γ) pol (imgS nvST) 0 cpu Htx Hfl
    (fun GD => GD = gpT) HG 3 HGl _ Hmid HGimg Herr s4 rs4 HR4
    (@AxSymCtl5.offBoundary hlc GF _ (blkGa2 gpT γ) 0 cpu (fun GD => GD = gpT) rs4 _ 3 HPC4
      (by decide +kernel)) (AxSymCtl5.stopCert8 rs4 Hc4 HPC4))

end Weak
