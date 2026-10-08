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
`wpd_cmv_probe_closed` (closed WPd at `gpT`, no premise).

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
3. THE CAPSTONE `wpd_cmv_probe_closed` IS NOT PORTED (OPEN, reported): at the probe neither Q14
   form applies.  The tail pc sPc + 2 is on the c.mv's page (`pTVpn2`), warm after the c.mv, so
   the Cold form's premise fails; and NO budget-0 stop certificate exists there: in Lean the
   instructions at sPc + 2 (0x0081, a C.ADDI hint), sPc + 4 and sPc + 6 (c.nop) make no graph
   read, and the run ends at an IMAGELESS fetch at sPc + 8, which `EvB` cannot express (no
   constructor; cf. Q13's `ENf` for AxSpinVA chains).  Kernel-checked evidence:
   `AxSymCtl5.probeTailTrace` (over the Lean-only `AxSymCtl5.runTrace`).  In Rocq the tail
   fetch itself was a graph read, hence stuck at the row end.  What survives, proved with no
   premise: `AxSymCtl5.wpdCmvProbeRowEnd` — the c.mv at the probe at `blkGa2 gpT γ`, all
   premises discharged, its run ending EXACTLY at `gpT`'s row end (`pTFcntCold`, `gpTRowLen`)
   with a0 = ra, the regime, pc + 2 and the warm page handed to the continuation (the tail).
   Closing it needs an owner decision (e.g. an `EvB` arm ending at an imageless fetch plus
   register-only boundary steps, or a probe whose tail stops at a graph read).

**Rocq → Lean name map.**  `P_one` `POne`, `wpd_cmv_closed` `wpdCmvClosed`, `X_gpr_writeC_S`
`XGprWriteCS`, `wpd_block_closed_S` `wpdBlockClosedS`, `wpd_block_closed_ga2`
`wpdBlockClosedGa2`, `wpd_cmv_closed_ga2` `wpdCmvClosedGa2`, `pT_text_ok_c` `pTTextOkC`, `pH1`
`pH1`, `pT_vpn2` `pTVpn2`, `pT_text_at2` `pTTextAt2`, `pT_fcnt_cold` `pTFcntCold`.  None is in
the duplicated-name table.  Lean-only (file-qualified `AxSymCtl5.*`): `wpdCmvClosedCold`,
`wpdBlockClosedSCold`, `wpdBlockClosedGa2Cold`, `wpdCmvClosedGa2Cold`, `hlenGa2` (the row-length
premise at `blkGa2`), `runTrace`, `probeTailTrace`, `wpdCmvProbeRowEnd`.

**Dropped:** `wpd_cmv_probe_closed` (deviation 3; no downstream Rocq user); the local instances
`cl_ga2`/`gpT_inst5` and the Ltac `nseip` (deviation 1); the `Print Assumptions`/`Check` lines.
Rocq 12 definitions/lemmas + 2 local instances + 1 Ltac; Lean 11 + 8 Lean-only.
-/
import Weak.AxSymCtl4
import Weak.AxSymCtl3

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

/-! ### (Lean-only) WHY THE CONCRETE CAPSTONE IS NOT PORTED (deviation 3)

The probe run from `nvST`, five `riscvStep false` steps, traced by `AxSmodeProbe`'s `mtr`
(events `(0 = read, akTag, size, pa)`; `akTag` 1 = i-fetch, 2 = walk): the `c.mv` at `sPc` makes
the three cold walk reads (`gpT`'s row) and its fetch; the next three instructions (0x0081 at
sPc + 2, c.nop at sPc + 4 and sPc + 6) make NO graph read (warm page; the fetch is an admin
step); the fetch at sPc + 8 has no bytes (stuck, code 2).  So no budget-0 stop certificate
exists at sPc + 2, and the tail page is warm: neither tail form of `wpdCmvClosed` applies. -/

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

/-- (Lean-only, deviation 3) WHAT SURVIVES OF THE CAPSTONE: `c.mv a0, ra` at the probe's S-mode
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

end Weak
