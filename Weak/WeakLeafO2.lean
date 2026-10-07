/-
Weak: **leaves with the `wstate` HIDDEN, part 2** -- `Weak/WeakLeafO.lean`'s §§9-11: the `c.ld`
TOR load (objective frame `cobj ξ (wpt8 …)` / `cobj ξ (wpt8Own …)` converted at the leaf via
`ctxRunToHold`/`ctxRunOfHold`), the `c.sd` RELEASE store (the post-state coherence bound
`∀ j < 8, T ≤ flr (wsView ws') (accAddr ea j)` becomes the objective floor token
`ctxViewLb ξ (viewAddrs (accAddr ea) 8 T)`, `WeakCtx` §8), and the `start()` families (c.and,
c.srli, auipc, the PMP-off c.sdsp release store, csrr sie, csrw mepc/satp/medeleg/mideleg/sie/
pmpaddr0, and the three cell-based `_o`-only ones: csrr/csrw mstatus, csrw pmpcfg0).

Rocq: `iris/WeakLeafO.v` @ xxvzwolszwmp, §9 onwards (split for elaboration time).

**Deviations from Rocq.**  Those of `Weak/WeakLeafO.lean` (its header): statements are their
`Weak/WeakLeafM.lean` twins' with the ws threading hidden; the CSR-in-mConf write wrappers (csrw
mepc, satp, medeleg, mideleg, sie, pmpaddr0) are at `DFrac.own 1` / `whartRun cpu ξ 1 c` (Rocq:
any `q`); `wwpCsrwSatpO/Run` carry the leaf's `_get_Mstatus_SXL c.mstatus = 2#2`; the TOR
`pmpaddr_n` cell is `c.pmpaddr`; csrr sie drops Rocq's CSR cells.

**Rocq → Lean name map.**  `wwp_<x>_o` ↦ `wwp<X>O`, `wwp_<x>_run` ↦ `wwp<X>Run` for `ld8_tor_rvc
sd8_tor_rvc and_rvc srli_rvc auipc sd8_off_rvc csrr_sie csrw_mepc csrw_satp csrw_medeleg
csrw_mideleg csrw_sie csrw_pmpaddr0` (and `_o` only for `csrr_mstatus csrw_mstatus
csrw_pmpcfg0`); `wwp_ld8_tor_rvc_o_own` `wwpLd8TorRvcOOwn`, `wwp_ld8_tor_rvc_run_own`
`wwpLd8TorRvcRunOwn`.

**Dropped:** nothing (31 Rocq declarations here).
-/
import Weak.WeakLeafO

namespace Weak

open Iris Iris.BI Iris.BI.MonPred Iris.ProofMode Iris.Std
open MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D LeanRV64D.Functions

section leafo2
variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [WeakGS GF]

/-- Rocq `wwp_ld8_tor_rvc_o`. -/
theorem wwpLd8TorRvcO (gen : Nat) (cpu : CPU) (ξ : CtxId) (pc : BitVec 64) (rs1 rd : BitVec 5)
    (imm : BitVec 12) (ea : PAddr) (v : BitVec 64) (dqv : DFrac) (q : Qp) (c : MConf)
    (rs1v rd0 : BitVec 64) :
    gen = 0 →
    MConf.mok c →
    pmpAllowsAll c.pmpcfg →
    pmpTor0Grants c.pmpcfg c.pmpaddr ea 8 →
    rs1.toNat ≠ 0 →
    rd.toNat ≠ 0 →
    rs1v + sign_extend (m := 64) imm = ea →
    inRam ea 8 →
    mConf (GF := GF) cpu (DFrac.own q) c ⊢
      clockCells cpu -∗
      pcIs cpu pc -∗
      gpr cpu rs1 (DFrac.own 1) rs1v -∗
      gpr cpu rd (DFrac.own 1) rd0 -∗
      winstrM (GF := GF) pc true (.LOAD (imm, .Regidx rs1, .Regidx rd, false, 8)) -∗
      wrunning (GF := GF) cpu ξ -∗
      cobj ξ (wpt8 (GF := GF) ea dqv v) -∗
      (mConf cpu (DFrac.own q) c -∗
        clockCells cpu -∗
        pcIs cpu (BitVec.addInt pc 2) -∗
        gpr cpu rs1 (DFrac.own 1) rs1v -∗
        gpr cpu rd (DFrac.own 1) v -∗
        wrunning cpu ξ -∗
        cobj ξ (wpt8 (GF := GF) ea dqv v) -∗
        wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu)) -∗
      wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu) := by
  intro h1 h2 h3 h4 h5 h6 h7 h8
  iintro Hm Ha1 Ha2 Ha3 Ha4 #Hi Hrun Hp1 Hcont
  icases wrunningOpen (GF := GF) cpu ξ $$ Hrun with ⟨%ws, Hws, Hauth⟩
  icases WeakLeafO.toHold (GF := GF) cpu ξ ws (wpt8 (GF := GF) ea dqv v) $$ Hauth Hp1
    with ⟨Hauth, Hp1⟩
  iapply wwpLd8TorRvc gen cpu pc rs1 rd imm ea v dqv q c rs1v rd0 ws h1 h2 h3 h4 h5 h6 h7 h8
    $$ Hm Ha1 Ha2 Ha3 Ha4 Hi Hws Hp1
  iintro %ws' %hle Hc1 Hc2 Hc3 Hc4 Hc5 Hws Hp1
  iapply WeakLeafO.wwpBupd
  imod ctxRunUpdate (GF := GF) cpu ξ ws ws' hle $$ Hauth with Hauth
  icases WeakLeafO.ofHold (GF := GF) cpu ξ ws' (wpt8 (GF := GF) ea dqv v) $$ Hauth Hp1
    with ⟨Hauth, Hp1⟩
  ihave Hrun := WeakLeafO.closeRun (GF := GF) cpu ξ ws' $$ Hws Hauth
  imodintro
  iapply Hcont $$ Hc1 Hc2 Hc3 Hc4 Hc5 Hrun Hp1

/-- Rocq `wwp_ld8_tor_rvc_o_own`. -/
theorem wwpLd8TorRvcOOwn (gen : Nat) (cpu : CPU) (ξ : CtxId) (pc : BitVec 64) (rs1 rd : BitVec 5)
    (imm : BitVec 12) (ea : PAddr) (v : BitVec 64) (q : Qp) (c : MConf) (rs1v rd0 : BitVec 64) :
    gen = 0 →
    MConf.mok c →
    pmpAllowsAll c.pmpcfg →
    pmpTor0Grants c.pmpcfg c.pmpaddr ea 8 →
    rs1.toNat ≠ 0 →
    rd.toNat ≠ 0 →
    rs1v + sign_extend (m := 64) imm = ea →
    inRam ea 8 →
    mConf (GF := GF) cpu (DFrac.own q) c ⊢
      clockCells cpu -∗
      pcIs cpu pc -∗
      gpr cpu rs1 (DFrac.own 1) rs1v -∗
      gpr cpu rd (DFrac.own 1) rd0 -∗
      winstrM (GF := GF) pc true (.LOAD (imm, .Regidx rs1, .Regidx rd, false, 8)) -∗
      wrunning (GF := GF) cpu ξ -∗
      cobj ξ (wpt8Own (GF := GF) cpu ea v) -∗
      (mConf cpu (DFrac.own q) c -∗
        clockCells cpu -∗
        pcIs cpu (BitVec.addInt pc 2) -∗
        gpr cpu rs1 (DFrac.own 1) rs1v -∗
        gpr cpu rd (DFrac.own 1) v -∗
        wrunning cpu ξ -∗
        cobj ξ (wpt8Own (GF := GF) cpu ea v) -∗
        wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu)) -∗
      wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu) := by
  intro h1 h2 h3 h4 h5 h6 h7 h8
  iintro Hm Ha1 Ha2 Ha3 Ha4 #Hi Hrun Hp1 Hcont
  icases wrunningOpen (GF := GF) cpu ξ $$ Hrun with ⟨%ws, Hws, Hauth⟩
  icases WeakLeafO.toHold (GF := GF) cpu ξ ws (wpt8Own (GF := GF) cpu ea v) $$ Hauth Hp1
    with ⟨Hauth, Hp1⟩
  iapply wwpLd8TorRvcOwn gen cpu pc rs1 rd imm ea v q c rs1v rd0 ws h1 h2 h3 h4 h5 h6 h7 h8
    $$ Hm Ha1 Ha2 Ha3 Ha4 Hi Hws Hp1
  iintro %ws' %hle Hc1 Hc2 Hc3 Hc4 Hc5 Hws Hp1
  iapply WeakLeafO.wwpBupd
  imod ctxRunUpdate (GF := GF) cpu ξ ws ws' hle $$ Hauth with Hauth
  icases WeakLeafO.ofHold (GF := GF) cpu ξ ws' (wpt8Own (GF := GF) cpu ea v) $$ Hauth Hp1
    with ⟨Hauth, Hp1⟩
  ihave Hrun := WeakLeafO.closeRun (GF := GF) cpu ξ ws' $$ Hws Hauth
  imodintro
  iapply Hcont $$ Hc1 Hc2 Hc3 Hc4 Hc5 Hrun Hp1

/-- Rocq `wwp_ld8_tor_rvc_run`. -/
theorem wwpLd8TorRvcRun (gen : Nat) (cpu : CPU) (ξ : CtxId) (pc : BitVec 64) (rs1 rd : BitVec 5)
    (imm : BitVec 12) (ea : PAddr) (v : BitVec 64) (dqv : DFrac) (q : Qp) (c : MConf)
    (rs1v rd0 : BitVec 64) :
    gen = 0 →
    MConf.mok c →
    pmpAllowsAll c.pmpcfg →
    pmpTor0Grants c.pmpcfg c.pmpaddr ea 8 →
    rs1.toNat ≠ 0 →
    rd.toNat ≠ 0 →
    rs1v + sign_extend (m := 64) imm = ea →
    inRam ea 8 →
    whartRun (GF := GF) cpu ξ q c ⊢
      clockCells cpu -∗
      pcIs cpu pc -∗
      gpr cpu rs1 (DFrac.own 1) rs1v -∗
      gpr cpu rd (DFrac.own 1) rd0 -∗
      winstrM (GF := GF) pc true (.LOAD (imm, .Regidx rs1, .Regidx rd, false, 8)) -∗
      cobj ξ (wpt8 (GF := GF) ea dqv v) -∗
      (whartRun cpu ξ q c -∗
        clockCells cpu -∗
        pcIs cpu (BitVec.addInt pc 2) -∗
        gpr cpu rs1 (DFrac.own 1) rs1v -∗
        gpr cpu rd (DFrac.own 1) v -∗
        cobj ξ (wpt8 (GF := GF) ea dqv v) -∗
        wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu)) -∗
      wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu) := by
  intro h1 h2 h3 h4 h5 h6 h7 h8
  iintro Hrun Ha1 Ha2 Ha3 Ha4 #Hi Hp1 Hcont
  icases whartRunOpen (GF := GF) cpu ξ q c $$ Hrun with ⟨Hm, Hview⟩
  iapply wwpLd8TorRvcO gen cpu ξ pc rs1 rd imm ea v dqv q c rs1v rd0 h1 h2 h3 h4 h5 h6 h7 h8
    $$ Hm Ha1 Ha2 Ha3 Ha4 Hi Hview Hp1
  iintro Hc1 Hc2 Hc3 Hc4 Hc5 Hview Hp1
  iapply Hcont $$ [Hc1 Hview] Hc2 Hc3 Hc4 Hc5 Hp1
  iapply whartRunClose (GF := GF) cpu ξ _ _ $$ Hc1 Hview

/-- Rocq `wwp_ld8_tor_rvc_run_own`. -/
theorem wwpLd8TorRvcRunOwn (gen : Nat) (cpu : CPU) (ξ : CtxId) (pc : BitVec 64) (rs1 rd : BitVec 5)
    (imm : BitVec 12) (ea : PAddr) (v : BitVec 64) (q : Qp) (c : MConf) (rs1v rd0 : BitVec 64) :
    gen = 0 →
    MConf.mok c →
    pmpAllowsAll c.pmpcfg →
    pmpTor0Grants c.pmpcfg c.pmpaddr ea 8 →
    rs1.toNat ≠ 0 →
    rd.toNat ≠ 0 →
    rs1v + sign_extend (m := 64) imm = ea →
    inRam ea 8 →
    whartRun (GF := GF) cpu ξ q c ⊢
      clockCells cpu -∗
      pcIs cpu pc -∗
      gpr cpu rs1 (DFrac.own 1) rs1v -∗
      gpr cpu rd (DFrac.own 1) rd0 -∗
      winstrM (GF := GF) pc true (.LOAD (imm, .Regidx rs1, .Regidx rd, false, 8)) -∗
      cobj ξ (wpt8Own (GF := GF) cpu ea v) -∗
      (whartRun cpu ξ q c -∗
        clockCells cpu -∗
        pcIs cpu (BitVec.addInt pc 2) -∗
        gpr cpu rs1 (DFrac.own 1) rs1v -∗
        gpr cpu rd (DFrac.own 1) v -∗
        cobj ξ (wpt8Own (GF := GF) cpu ea v) -∗
        wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu)) -∗
      wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu) := by
  intro h1 h2 h3 h4 h5 h6 h7 h8
  iintro Hrun Ha1 Ha2 Ha3 Ha4 #Hi Hp1 Hcont
  icases whartRunOpen (GF := GF) cpu ξ q c $$ Hrun with ⟨Hm, Hview⟩
  iapply wwpLd8TorRvcOOwn gen cpu ξ pc rs1 rd imm ea v q c rs1v rd0 h1 h2 h3 h4 h5 h6 h7 h8
    $$ Hm Ha1 Ha2 Ha3 Ha4 Hi Hview Hp1
  iintro Hc1 Hc2 Hc3 Hc4 Hc5 Hview Hp1
  iapply Hcont $$ [Hc1 Hview] Hc2 Hc3 Hc4 Hc5 Hp1
  iapply whartRunClose (GF := GF) cpu ξ _ _ $$ Hc1 Hview

/-- Rocq `wwp_sd8_tor_rvc_o`. -/
theorem wwpSd8TorRvcO (gen : Nat) (cpu : CPU) (ξ : CtxId) (pc : BitVec 64) (rs1 rs2 : BitVec 5)
    (imm : BitVec 12) (ea : PAddr) (vold : BitVec 64) (R : VProp GF) (q : Qp) (c : MConf)
    (rs1v rs2v : BitVec 64) :
    gen = 0 →
    MConf.mok c →
    pmpAllowsAll c.pmpcfg →
    pmpTor0Grants c.pmpcfg c.pmpaddr ea 8 →
    rs1.toNat ≠ 0 →
    rs2.toNat ≠ 0 →
    rs1v + sign_extend (m := 64) imm = ea →
    inRam ea 8 →
    mConf (GF := GF) cpu (DFrac.own q) c ⊢
      clockCells cpu -∗
      pcIs cpu pc -∗
      gpr cpu rs1 (DFrac.own 1) rs1v -∗
      gpr cpu rs2 (DFrac.own 1) rs2v -∗
      winstrM (GF := GF) pc true (.STORE (imm, .Regidx rs2, .Regidx rs1, 8)) -∗
      wrunning (GF := GF) cpu ξ -∗
      cobj ξ (wpt8Own (GF := GF) cpu ea vold) -∗
      cobj ξ R -∗
      (∀ T : Nat,
        ctxViewLb ξ (viewAddrs (WeakInterp.accAddr ea) 8 T) -∗
        mConf cpu (DFrac.own q) c -∗
        clockCells cpu -∗
        pcIs cpu (BitVec.addInt pc 2) -∗
        gpr cpu rs1 (DFrac.own 1) rs1v -∗
        gpr cpu rs2 (DFrac.own 1) rs2v -∗
        wrunning cpu ξ -∗
        cobj ξ (wpt8Own (GF := GF) cpu ea rs2v) -∗
        R.monPred_at (viewScl T) -∗
        wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu)) -∗
      wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu) := by
  intro h1 h2 h3 h4 h5 h6 h7 h8
  iintro Hm Ha1 Ha2 Ha3 Ha4 #Hi Hrun Hp1 Hp2 Hcont
  icases wrunningOpen (GF := GF) cpu ξ $$ Hrun with ⟨%ws, Hws, Hauth⟩
  icases WeakLeafO.toHold (GF := GF) cpu ξ ws (wpt8Own (GF := GF) cpu ea vold) $$ Hauth Hp1
    with ⟨Hauth, Hp1⟩
  icases WeakLeafO.toHold (GF := GF) cpu ξ ws R $$ Hauth Hp2
    with ⟨Hauth, Hp2⟩
  iapply wwpSd8TorRvc gen cpu pc rs1 rs2 imm ea vold R q c rs1v rs2v ws h1 h2 h3 h4 h5 h6 h7 h8
    $$ Hm Ha1 Ha2 Ha3 Ha4 Hi Hws Hp1 Hp2
  iintro %ws' %T %hle %hT Hc1 Hc2 Hc3 Hc4 Hc5 Hws Hp1 Hc6
  iapply WeakLeafO.wwpBupd
  imod ctxRunUpdate (GF := GF) cpu ξ ws ws' hle $$ Hauth with Hauth
  icases WeakLeafO.ofHold (GF := GF) cpu ξ ws' (wpt8Own (GF := GF) cpu ea rs2v) $$ Hauth Hp1
    with ⟨Hauth, Hp1⟩
  icases WeakLeafO.addrsKeep (GF := GF) cpu ξ ws' (WeakInterp.accAddr ea) 8 T hT $$ Hauth
    with ⟨Hauth, #Hlb⟩
  ihave Hrun := WeakLeafO.closeRun (GF := GF) cpu ξ ws' $$ Hws Hauth
  imodintro
  iapply Hcont $$ %T Hlb Hc1 Hc2 Hc3 Hc4 Hc5 Hrun Hp1 Hc6

/-- Rocq `wwp_sd8_tor_rvc_run`. -/
theorem wwpSd8TorRvcRun (gen : Nat) (cpu : CPU) (ξ : CtxId) (pc : BitVec 64) (rs1 rs2 : BitVec 5)
    (imm : BitVec 12) (ea : PAddr) (vold : BitVec 64) (R : VProp GF) (q : Qp) (c : MConf)
    (rs1v rs2v : BitVec 64) :
    gen = 0 →
    MConf.mok c →
    pmpAllowsAll c.pmpcfg →
    pmpTor0Grants c.pmpcfg c.pmpaddr ea 8 →
    rs1.toNat ≠ 0 →
    rs2.toNat ≠ 0 →
    rs1v + sign_extend (m := 64) imm = ea →
    inRam ea 8 →
    whartRun (GF := GF) cpu ξ q c ⊢
      clockCells cpu -∗
      pcIs cpu pc -∗
      gpr cpu rs1 (DFrac.own 1) rs1v -∗
      gpr cpu rs2 (DFrac.own 1) rs2v -∗
      winstrM (GF := GF) pc true (.STORE (imm, .Regidx rs2, .Regidx rs1, 8)) -∗
      cobj ξ (wpt8Own (GF := GF) cpu ea vold) -∗
      cobj ξ R -∗
      (∀ T : Nat,
        ctxViewLb ξ (viewAddrs (WeakInterp.accAddr ea) 8 T) -∗
        whartRun cpu ξ q c -∗
        clockCells cpu -∗
        pcIs cpu (BitVec.addInt pc 2) -∗
        gpr cpu rs1 (DFrac.own 1) rs1v -∗
        gpr cpu rs2 (DFrac.own 1) rs2v -∗
        cobj ξ (wpt8Own (GF := GF) cpu ea rs2v) -∗
        R.monPred_at (viewScl T) -∗
        wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu)) -∗
      wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu) := by
  intro h1 h2 h3 h4 h5 h6 h7 h8
  iintro Hrun Ha1 Ha2 Ha3 Ha4 #Hi Hp1 Hp2 Hcont
  icases whartRunOpen (GF := GF) cpu ξ q c $$ Hrun with ⟨Hm, Hview⟩
  iapply wwpSd8TorRvcO gen cpu ξ pc rs1 rs2 imm ea vold R q c rs1v rs2v h1 h2 h3 h4 h5 h6 h7 h8
    $$ Hm Ha1 Ha2 Ha3 Ha4 Hi Hview Hp1 Hp2
  iintro %T #Hlb Hc1 Hc2 Hc3 Hc4 Hc5 Hview Hp1 Hc6
  iapply Hcont $$ %T Hlb [Hc1 Hview] Hc2 Hc3 Hc4 Hc5 Hp1 Hc6
  iapply whartRunClose (GF := GF) cpu ξ _ _ $$ Hc1 Hview

/-- Rocq `wwp_and_rvc_o`. -/
theorem wwpAndRvcO (gen : Nat) (cpu : CPU) (ξ : CtxId) (pc : BitVec 64) (rs2 rs1 rd : BitVec 5)
    (m : RegMap) (c : MConf) (q : Qp) :
    gen = 0 →
    MConf.mok c →
    pmpAllowsAll c.pmpcfg →
    rd.toNat ≠ 0 →
    mConf (GF := GF) cpu (DFrac.own q) c ⊢
      clockCells cpu -∗
      pcIs cpu pc -∗
      gprFile cpu m -∗
      winstrM (GF := GF) pc true (.RTYPE (.Regidx rs2, .Regidx rs1, .Regidx rd, .AND)) -∗
      wrunning (GF := GF) cpu ξ -∗
      (mConf cpu (DFrac.own q) c -∗
        clockCells cpu -∗
        pcIs cpu (BitVec.addInt pc 2) -∗
        gprFile cpu (m.set rd (m.get rs1 &&& m.get rs2)) -∗
        wrunning cpu ξ -∗
        wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu)) -∗
      wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu) := by
  intro h1 h2 h3 h4
  iintro Hm Ha1 Ha2 Ha3 #Hi Hrun Hcont
  icases wrunningOpen (GF := GF) cpu ξ $$ Hrun with ⟨%ws, Hws, Hauth⟩
  ihave HF := WeakLeafO.holdTrue (GF := GF) ws
  iapply wwpAndRvc gen cpu pc rs2 rs1 rd m c q ws (iprop(⌜True⌝) : VProp GF) h1 h2 h3 h4
    $$ Hm Ha1 Ha2 Ha3 Hi Hws HF
  iintro %ws' %hle Hc1 Hc2 Hc3 Hc4 Hws -
  iapply WeakLeafO.wwpBupd
  imod ctxRunUpdate (GF := GF) cpu ξ ws ws' hle $$ Hauth with Hauth
  ihave Hrun := WeakLeafO.closeRun (GF := GF) cpu ξ ws' $$ Hws Hauth
  imodintro
  iapply Hcont $$ Hc1 Hc2 Hc3 Hc4 Hrun

/-- Rocq `wwp_and_rvc_run`. -/
theorem wwpAndRvcRun (gen : Nat) (cpu : CPU) (ξ : CtxId) (pc : BitVec 64) (rs2 rs1 rd : BitVec 5)
    (m : RegMap) (c : MConf) (q : Qp) :
    gen = 0 →
    MConf.mok c →
    pmpAllowsAll c.pmpcfg →
    rd.toNat ≠ 0 →
    whartRun (GF := GF) cpu ξ q c ⊢
      clockCells cpu -∗
      pcIs cpu pc -∗
      gprFile cpu m -∗
      winstrM (GF := GF) pc true (.RTYPE (.Regidx rs2, .Regidx rs1, .Regidx rd, .AND)) -∗
      (whartRun cpu ξ q c -∗
        clockCells cpu -∗
        pcIs cpu (BitVec.addInt pc 2) -∗
        gprFile cpu (m.set rd (m.get rs1 &&& m.get rs2)) -∗
        wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu)) -∗
      wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu) := by
  intro h1 h2 h3 h4
  iintro Hrun Ha1 Ha2 Ha3 #Hi Hcont
  icases whartRunOpen (GF := GF) cpu ξ q c $$ Hrun with ⟨Hm, Hview⟩
  iapply wwpAndRvcO gen cpu ξ pc rs2 rs1 rd m c q h1 h2 h3 h4
    $$ Hm Ha1 Ha2 Ha3 Hi Hview
  iintro Hc1 Hc2 Hc3 Hc4 Hview
  iapply Hcont $$ [Hc1 Hview] Hc2 Hc3 Hc4
  iapply whartRunClose (GF := GF) cpu ξ _ _ $$ Hc1 Hview

/-- Rocq `wwp_srli_rvc_o`. -/
theorem wwpSrliRvcO (gen : Nat) (cpu : CPU) (ξ : CtxId) (pc : BitVec 64) (rs1 rd : BitVec 5)
    (shamt : BitVec 6) (m : RegMap) (c : MConf) (q : Qp) :
    gen = 0 →
    MConf.mok c →
    pmpAllowsAll c.pmpcfg →
    rd.toNat ≠ 0 →
    mConf (GF := GF) cpu (DFrac.own q) c ⊢
      clockCells cpu -∗
      pcIs cpu pc -∗
      gprFile cpu m -∗
      winstrM (GF := GF) pc true (.SHIFTIOP (shamt, .Regidx rs1, .Regidx rd, .SRLI)) -∗
      wrunning (GF := GF) cpu ξ -∗
      (mConf cpu (DFrac.own q) c -∗
        clockCells cpu -∗
        pcIs cpu (BitVec.addInt pc 2) -∗
        gprFile cpu (m.set rd (shift_bits_right (m.get rs1)
          (Sail.BitVec.extractLsb shamt (Functions.log2_xlen -i 1) 0))) -∗
        wrunning cpu ξ -∗
        wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu)) -∗
      wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu) := by
  intro h1 h2 h3 h4
  iintro Hm Ha1 Ha2 Ha3 #Hi Hrun Hcont
  icases wrunningOpen (GF := GF) cpu ξ $$ Hrun with ⟨%ws, Hws, Hauth⟩
  ihave HF := WeakLeafO.holdTrue (GF := GF) ws
  iapply wwpSrliRvc gen cpu pc rs1 rd shamt m c q ws (iprop(⌜True⌝) : VProp GF) h1 h2 h3 h4
    $$ Hm Ha1 Ha2 Ha3 Hi Hws HF
  iintro %ws' %hle Hc1 Hc2 Hc3 Hc4 Hws -
  iapply WeakLeafO.wwpBupd
  imod ctxRunUpdate (GF := GF) cpu ξ ws ws' hle $$ Hauth with Hauth
  ihave Hrun := WeakLeafO.closeRun (GF := GF) cpu ξ ws' $$ Hws Hauth
  imodintro
  iapply Hcont $$ Hc1 Hc2 Hc3 Hc4 Hrun

/-- Rocq `wwp_srli_rvc_run`. -/
theorem wwpSrliRvcRun (gen : Nat) (cpu : CPU) (ξ : CtxId) (pc : BitVec 64) (rs1 rd : BitVec 5)
    (shamt : BitVec 6) (m : RegMap) (c : MConf) (q : Qp) :
    gen = 0 →
    MConf.mok c →
    pmpAllowsAll c.pmpcfg →
    rd.toNat ≠ 0 →
    whartRun (GF := GF) cpu ξ q c ⊢
      clockCells cpu -∗
      pcIs cpu pc -∗
      gprFile cpu m -∗
      winstrM (GF := GF) pc true (.SHIFTIOP (shamt, .Regidx rs1, .Regidx rd, .SRLI)) -∗
      (whartRun cpu ξ q c -∗
        clockCells cpu -∗
        pcIs cpu (BitVec.addInt pc 2) -∗
        gprFile cpu (m.set rd (shift_bits_right (m.get rs1)
          (Sail.BitVec.extractLsb shamt (Functions.log2_xlen -i 1) 0))) -∗
        wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu)) -∗
      wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu) := by
  intro h1 h2 h3 h4
  iintro Hrun Ha1 Ha2 Ha3 #Hi Hcont
  icases whartRunOpen (GF := GF) cpu ξ q c $$ Hrun with ⟨Hm, Hview⟩
  iapply wwpSrliRvcO gen cpu ξ pc rs1 rd shamt m c q h1 h2 h3 h4
    $$ Hm Ha1 Ha2 Ha3 Hi Hview
  iintro Hc1 Hc2 Hc3 Hc4 Hview
  iapply Hcont $$ [Hc1 Hview] Hc2 Hc3 Hc4
  iapply whartRunClose (GF := GF) cpu ξ _ _ $$ Hc1 Hview

/-- Rocq `wwp_auipc_o`. -/
theorem wwpAuipcO (gen : Nat) (cpu : CPU) (ξ : CtxId) (pc : BitVec 64) (rd : BitVec 5)
    (imm : BitVec 20) (m : RegMap) (c : MConf) (q : Qp) :
    gen = 0 →
    MConf.mok c →
    pmpAllowsAll c.pmpcfg →
    rd.toNat ≠ 0 →
    mConf (GF := GF) cpu (DFrac.own q) c ⊢
      clockCells cpu -∗
      pcIs cpu pc -∗
      gprFile cpu m -∗
      winstrM (GF := GF) pc false (.UTYPE (imm, .Regidx rd, .AUIPC)) -∗
      wrunning (GF := GF) cpu ξ -∗
      (mConf cpu (DFrac.own q) c -∗
        clockCells cpu -∗
        pcIs cpu (BitVec.addInt pc 4) -∗
        gprFile cpu (m.set rd (pc + auipcOff imm)) -∗
        wrunning cpu ξ -∗
        wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu)) -∗
      wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu) := by
  intro h1 h2 h3 h4
  iintro Hm Ha1 Ha2 Ha3 #Hi Hrun Hcont
  icases wrunningOpen (GF := GF) cpu ξ $$ Hrun with ⟨%ws, Hws, Hauth⟩
  ihave HF := WeakLeafO.holdTrue (GF := GF) ws
  iapply wwpAuipc gen cpu pc rd imm m c q ws (iprop(⌜True⌝) : VProp GF) h1 h2 h3 h4
    $$ Hm Ha1 Ha2 Ha3 Hi Hws HF
  iintro %ws' %hle Hc1 Hc2 Hc3 Hc4 Hws -
  iapply WeakLeafO.wwpBupd
  imod ctxRunUpdate (GF := GF) cpu ξ ws ws' hle $$ Hauth with Hauth
  ihave Hrun := WeakLeafO.closeRun (GF := GF) cpu ξ ws' $$ Hws Hauth
  imodintro
  iapply Hcont $$ Hc1 Hc2 Hc3 Hc4 Hrun

/-- Rocq `wwp_auipc_run`. -/
theorem wwpAuipcRun (gen : Nat) (cpu : CPU) (ξ : CtxId) (pc : BitVec 64) (rd : BitVec 5)
    (imm : BitVec 20) (m : RegMap) (c : MConf) (q : Qp) :
    gen = 0 →
    MConf.mok c →
    pmpAllowsAll c.pmpcfg →
    rd.toNat ≠ 0 →
    whartRun (GF := GF) cpu ξ q c ⊢
      clockCells cpu -∗
      pcIs cpu pc -∗
      gprFile cpu m -∗
      winstrM (GF := GF) pc false (.UTYPE (imm, .Regidx rd, .AUIPC)) -∗
      (whartRun cpu ξ q c -∗
        clockCells cpu -∗
        pcIs cpu (BitVec.addInt pc 4) -∗
        gprFile cpu (m.set rd (pc + auipcOff imm)) -∗
        wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu)) -∗
      wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu) := by
  intro h1 h2 h3 h4
  iintro Hrun Ha1 Ha2 Ha3 #Hi Hcont
  icases whartRunOpen (GF := GF) cpu ξ q c $$ Hrun with ⟨Hm, Hview⟩
  iapply wwpAuipcO gen cpu ξ pc rd imm m c q h1 h2 h3 h4
    $$ Hm Ha1 Ha2 Ha3 Hi Hview
  iintro Hc1 Hc2 Hc3 Hc4 Hview
  iapply Hcont $$ [Hc1 Hview] Hc2 Hc3 Hc4
  iapply whartRunClose (GF := GF) cpu ξ _ _ $$ Hc1 Hview

/-- Rocq `wwp_sd8_off_rvc_o`. -/
theorem wwpSd8OffRvcO (gen : Nat) (cpu : CPU) (ξ : CtxId) (pc : BitVec 64) (rs1 rs2 : BitVec 5)
    (imm : BitVec 12) (ea : PAddr) (vold : BitVec 64) (R : VProp GF) (q : Qp) (c : MConf)
    (rs1v rs2v : BitVec 64) :
    gen = 0 →
    MConf.mok c →
    pmpAllOff c.pmpcfg →
    rs1.toNat ≠ 0 →
    rs2.toNat ≠ 0 →
    rs1v + sign_extend (m := 64) imm = ea →
    inRam ea 8 →
    mConf (GF := GF) cpu (DFrac.own q) c ⊢
      clockCells cpu -∗
      pcIs cpu pc -∗
      gpr cpu rs1 (DFrac.own 1) rs1v -∗
      gpr cpu rs2 (DFrac.own 1) rs2v -∗
      winstrM (GF := GF) pc true (.STORE (imm, .Regidx rs2, .Regidx rs1, 8)) -∗
      wrunning (GF := GF) cpu ξ -∗
      cobj ξ (wpt8Own (GF := GF) cpu ea vold) -∗
      cobj ξ R -∗
      (∀ T : Nat,
        ctxViewLb ξ (viewAddrs (WeakInterp.accAddr ea) 8 T) -∗
        mConf cpu (DFrac.own q) c -∗
        clockCells cpu -∗
        pcIs cpu (BitVec.addInt pc 2) -∗
        gpr cpu rs1 (DFrac.own 1) rs1v -∗
        gpr cpu rs2 (DFrac.own 1) rs2v -∗
        wrunning cpu ξ -∗
        cobj ξ (wpt8Own (GF := GF) cpu ea rs2v) -∗
        R.monPred_at (viewScl T) -∗
        wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu)) -∗
      wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu) := by
  intro h1 h2 h3 h4 h5 h6 h7
  iintro Hm Ha1 Ha2 Ha3 Ha4 #Hi Hrun Hp1 Hp2 Hcont
  icases wrunningOpen (GF := GF) cpu ξ $$ Hrun with ⟨%ws, Hws, Hauth⟩
  icases WeakLeafO.toHold (GF := GF) cpu ξ ws (wpt8Own (GF := GF) cpu ea vold) $$ Hauth Hp1
    with ⟨Hauth, Hp1⟩
  icases WeakLeafO.toHold (GF := GF) cpu ξ ws R $$ Hauth Hp2
    with ⟨Hauth, Hp2⟩
  iapply wwpSd8OffRvc gen cpu pc rs1 rs2 imm ea vold R q c rs1v rs2v ws h1 h2 h3 h4 h5 h6 h7
    $$ Hm Ha1 Ha2 Ha3 Ha4 Hi Hws Hp1 Hp2
  iintro %ws' %T %hle %hT Hc1 Hc2 Hc3 Hc4 Hc5 Hws Hp1 Hc6
  iapply WeakLeafO.wwpBupd
  imod ctxRunUpdate (GF := GF) cpu ξ ws ws' hle $$ Hauth with Hauth
  icases WeakLeafO.ofHold (GF := GF) cpu ξ ws' (wpt8Own (GF := GF) cpu ea rs2v) $$ Hauth Hp1
    with ⟨Hauth, Hp1⟩
  icases WeakLeafO.addrsKeep (GF := GF) cpu ξ ws' (WeakInterp.accAddr ea) 8 T hT $$ Hauth
    with ⟨Hauth, #Hlb⟩
  ihave Hrun := WeakLeafO.closeRun (GF := GF) cpu ξ ws' $$ Hws Hauth
  imodintro
  iapply Hcont $$ %T Hlb Hc1 Hc2 Hc3 Hc4 Hc5 Hrun Hp1 Hc6

/-- Rocq `wwp_sd8_off_rvc_run`. -/
theorem wwpSd8OffRvcRun (gen : Nat) (cpu : CPU) (ξ : CtxId) (pc : BitVec 64) (rs1 rs2 : BitVec 5)
    (imm : BitVec 12) (ea : PAddr) (vold : BitVec 64) (R : VProp GF) (q : Qp) (c : MConf)
    (rs1v rs2v : BitVec 64) :
    gen = 0 →
    MConf.mok c →
    pmpAllOff c.pmpcfg →
    rs1.toNat ≠ 0 →
    rs2.toNat ≠ 0 →
    rs1v + sign_extend (m := 64) imm = ea →
    inRam ea 8 →
    whartRun (GF := GF) cpu ξ q c ⊢
      clockCells cpu -∗
      pcIs cpu pc -∗
      gpr cpu rs1 (DFrac.own 1) rs1v -∗
      gpr cpu rs2 (DFrac.own 1) rs2v -∗
      winstrM (GF := GF) pc true (.STORE (imm, .Regidx rs2, .Regidx rs1, 8)) -∗
      cobj ξ (wpt8Own (GF := GF) cpu ea vold) -∗
      cobj ξ R -∗
      (∀ T : Nat,
        ctxViewLb ξ (viewAddrs (WeakInterp.accAddr ea) 8 T) -∗
        whartRun cpu ξ q c -∗
        clockCells cpu -∗
        pcIs cpu (BitVec.addInt pc 2) -∗
        gpr cpu rs1 (DFrac.own 1) rs1v -∗
        gpr cpu rs2 (DFrac.own 1) rs2v -∗
        cobj ξ (wpt8Own (GF := GF) cpu ea rs2v) -∗
        R.monPred_at (viewScl T) -∗
        wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu)) -∗
      wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu) := by
  intro h1 h2 h3 h4 h5 h6 h7
  iintro Hrun Ha1 Ha2 Ha3 Ha4 #Hi Hp1 Hp2 Hcont
  icases whartRunOpen (GF := GF) cpu ξ q c $$ Hrun with ⟨Hm, Hview⟩
  iapply wwpSd8OffRvcO gen cpu ξ pc rs1 rs2 imm ea vold R q c rs1v rs2v h1 h2 h3 h4 h5 h6 h7
    $$ Hm Ha1 Ha2 Ha3 Ha4 Hi Hview Hp1 Hp2
  iintro %T #Hlb Hc1 Hc2 Hc3 Hc4 Hc5 Hview Hp1 Hc6
  iapply Hcont $$ %T Hlb [Hc1 Hview] Hc2 Hc3 Hc4 Hc5 Hp1 Hc6
  iapply whartRunClose (GF := GF) cpu ξ _ _ $$ Hc1 Hview

/-- Rocq `wwp_csrr_sie_o`. -/
theorem wwpCsrrSieO (gen : Nat) (cpu : CPU) (ξ : CtxId) (pc : BitVec 64) (rd : BitVec 5)
    (rd0 : BitVec 64) (c : MConf) (q : Qp) :
    gen = 0 →
    MConf.mok c →
    pmpAllowsAll c.pmpcfg →
    rd.toNat ≠ 0 →
    mConf (GF := GF) cpu (DFrac.own q) c ⊢
      clockCells cpu -∗
      pcIs cpu pc -∗
      gpr cpu rd (DFrac.own 1) rd0 -∗
      winstrM (GF := GF) pc false (.CSRReg (0x104#12, zreg, .Regidx rd, .CSRRS)) -∗
      wrunning (GF := GF) cpu ξ -∗
      (mConf cpu (DFrac.own q) c -∗
        clockCells cpu -∗
        pcIs cpu (BitVec.addInt pc 4) -∗
        gpr cpu rd (DFrac.own 1) (lower_mie c.mie c.mideleg) -∗
        wrunning cpu ξ -∗
        wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu)) -∗
      wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu) := by
  intro h1 h2 h3 h4
  iintro Hm Ha1 Ha2 Ha3 #Hi Hrun Hcont
  icases wrunningOpen (GF := GF) cpu ξ $$ Hrun with ⟨%ws, Hws, Hauth⟩
  ihave HF := WeakLeafO.holdTrue (GF := GF) ws
  iapply wwpCsrrSie gen cpu pc rd rd0 c q ws (iprop(⌜True⌝) : VProp GF) h1 h2 h3 h4
    $$ Hm Ha1 Ha2 Ha3 Hi Hws HF
  iintro %ws' %hle Hc1 Hc2 Hc3 Hc4 Hws -
  iapply WeakLeafO.wwpBupd
  imod ctxRunUpdate (GF := GF) cpu ξ ws ws' hle $$ Hauth with Hauth
  ihave Hrun := WeakLeafO.closeRun (GF := GF) cpu ξ ws' $$ Hws Hauth
  imodintro
  iapply Hcont $$ Hc1 Hc2 Hc3 Hc4 Hrun

/-- Rocq `wwp_csrr_sie_run`. -/
theorem wwpCsrrSieRun (gen : Nat) (cpu : CPU) (ξ : CtxId) (pc : BitVec 64) (rd : BitVec 5)
    (rd0 : BitVec 64) (c : MConf) (q : Qp) :
    gen = 0 →
    MConf.mok c →
    pmpAllowsAll c.pmpcfg →
    rd.toNat ≠ 0 →
    whartRun (GF := GF) cpu ξ q c ⊢
      clockCells cpu -∗
      pcIs cpu pc -∗
      gpr cpu rd (DFrac.own 1) rd0 -∗
      winstrM (GF := GF) pc false (.CSRReg (0x104#12, zreg, .Regidx rd, .CSRRS)) -∗
      (whartRun cpu ξ q c -∗
        clockCells cpu -∗
        pcIs cpu (BitVec.addInt pc 4) -∗
        gpr cpu rd (DFrac.own 1) (lower_mie c.mie c.mideleg) -∗
        wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu)) -∗
      wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu) := by
  intro h1 h2 h3 h4
  iintro Hrun Ha1 Ha2 Ha3 #Hi Hcont
  icases whartRunOpen (GF := GF) cpu ξ q c $$ Hrun with ⟨Hm, Hview⟩
  iapply wwpCsrrSieO gen cpu ξ pc rd rd0 c q h1 h2 h3 h4
    $$ Hm Ha1 Ha2 Ha3 Hi Hview
  iintro Hc1 Hc2 Hc3 Hc4 Hview
  iapply Hcont $$ [Hc1 Hview] Hc2 Hc3 Hc4
  iapply whartRunClose (GF := GF) cpu ξ _ _ $$ Hc1 Hview

/-- Rocq `wwp_csrw_mepc_o`. -/
theorem wwpCsrwMepcO (gen : Nat) (cpu : CPU) (ξ : CtxId) (pc : BitVec 64) (rs1 : BitVec 5)
    (rs1v : BitVec 64) (c : MConf) :
    gen = 0 →
    MConf.mok c →
    pmpAllowsAll c.pmpcfg →
    rs1.toNat ≠ 0 →
    mConf (GF := GF) cpu (DFrac.own 1) c ⊢
      clockCells cpu -∗
      pcIs cpu pc -∗
      gpr cpu rs1 (DFrac.own 1) rs1v -∗
      winstrM (GF := GF) pc false (.CSRReg (0x341#12, .Regidx rs1, zreg, .CSRRW)) -∗
      wrunning (GF := GF) cpu ξ -∗
      (mConf cpu (DFrac.own 1) { c with mepc := WeakLeafCsrw2.mepcVal rs1v } -∗
        clockCells cpu -∗
        pcIs cpu (BitVec.addInt pc 4) -∗
        gpr cpu rs1 (DFrac.own 1) rs1v -∗
        wrunning cpu ξ -∗
        wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu)) -∗
      wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu) := by
  intro h1 h2 h3 h4
  iintro Hm Ha1 Ha2 Ha3 #Hi Hrun Hcont
  icases wrunningOpen (GF := GF) cpu ξ $$ Hrun with ⟨%ws, Hws, Hauth⟩
  ihave HF := WeakLeafO.holdTrue (GF := GF) ws
  iapply wwpCsrwMepc gen cpu pc rs1 rs1v c ws (iprop(⌜True⌝) : VProp GF) h1 h2 h3 h4
    $$ Hm Ha1 Ha2 Ha3 Hi Hws HF
  iintro %ws' %hle Hc1 Hc2 Hc3 Hc4 Hws -
  iapply WeakLeafO.wwpBupd
  imod ctxRunUpdate (GF := GF) cpu ξ ws ws' hle $$ Hauth with Hauth
  ihave Hrun := WeakLeafO.closeRun (GF := GF) cpu ξ ws' $$ Hws Hauth
  imodintro
  iapply Hcont $$ Hc1 Hc2 Hc3 Hc4 Hrun

/-- Rocq `wwp_csrw_mepc_run`. -/
theorem wwpCsrwMepcRun (gen : Nat) (cpu : CPU) (ξ : CtxId) (pc : BitVec 64) (rs1 : BitVec 5)
    (rs1v : BitVec 64) (c : MConf) :
    gen = 0 →
    MConf.mok c →
    pmpAllowsAll c.pmpcfg →
    rs1.toNat ≠ 0 →
    whartRun (GF := GF) cpu ξ 1 c ⊢
      clockCells cpu -∗
      pcIs cpu pc -∗
      gpr cpu rs1 (DFrac.own 1) rs1v -∗
      winstrM (GF := GF) pc false (.CSRReg (0x341#12, .Regidx rs1, zreg, .CSRRW)) -∗
      (whartRun cpu ξ 1 { c with mepc := WeakLeafCsrw2.mepcVal rs1v } -∗
        clockCells cpu -∗
        pcIs cpu (BitVec.addInt pc 4) -∗
        gpr cpu rs1 (DFrac.own 1) rs1v -∗
        wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu)) -∗
      wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu) := by
  intro h1 h2 h3 h4
  iintro Hrun Ha1 Ha2 Ha3 #Hi Hcont
  icases whartRunOpen (GF := GF) cpu ξ 1 c $$ Hrun with ⟨Hm, Hview⟩
  iapply wwpCsrwMepcO gen cpu ξ pc rs1 rs1v c h1 h2 h3 h4
    $$ Hm Ha1 Ha2 Ha3 Hi Hview
  iintro Hc1 Hc2 Hc3 Hc4 Hview
  iapply Hcont $$ [Hc1 Hview] Hc2 Hc3 Hc4
  iapply whartRunClose (GF := GF) cpu ξ _ _ $$ Hc1 Hview

/-- Rocq `wwp_csrw_satp_o`. -/
theorem wwpCsrwSatpO (gen : Nat) (cpu : CPU) (ξ : CtxId) (pc : BitVec 64) (rs1 : BitVec 5)
    (rs1v : BitVec 64) (c : MConf) :
    gen = 0 →
    MConf.mok c →
    pmpAllowsAll c.pmpcfg →
    rs1.toNat ≠ 0 →
    _get_Mstatus_SXL c.mstatus = 2#2 →
    mConf (GF := GF) cpu (DFrac.own 1) c ⊢
      clockCells cpu -∗
      pcIs cpu pc -∗
      gpr cpu rs1 (DFrac.own 1) rs1v -∗
      winstrM (GF := GF) pc false (.CSRReg (0x180#12, .Regidx rs1, zreg, .CSRRW)) -∗
      wrunning (GF := GF) cpu ξ -∗
      (mConf cpu (DFrac.own 1) { c with satp := WeakLeafCsrw3.satpLegalized c.satp rs1v } -∗
        clockCells cpu -∗
        pcIs cpu (BitVec.addInt pc 4) -∗
        gpr cpu rs1 (DFrac.own 1) rs1v -∗
        wrunning cpu ξ -∗
        wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu)) -∗
      wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu) := by
  intro h1 h2 h3 h4 h5
  iintro Hm Ha1 Ha2 Ha3 #Hi Hrun Hcont
  icases wrunningOpen (GF := GF) cpu ξ $$ Hrun with ⟨%ws, Hws, Hauth⟩
  ihave HF := WeakLeafO.holdTrue (GF := GF) ws
  iapply wwpCsrwSatp gen cpu pc rs1 rs1v c ws (iprop(⌜True⌝) : VProp GF) h1 h2 h3 h4 h5
    $$ Hm Ha1 Ha2 Ha3 Hi Hws HF
  iintro %ws' %hle Hc1 Hc2 Hc3 Hc4 Hws -
  iapply WeakLeafO.wwpBupd
  imod ctxRunUpdate (GF := GF) cpu ξ ws ws' hle $$ Hauth with Hauth
  ihave Hrun := WeakLeafO.closeRun (GF := GF) cpu ξ ws' $$ Hws Hauth
  imodintro
  iapply Hcont $$ Hc1 Hc2 Hc3 Hc4 Hrun

/-- Rocq `wwp_csrw_satp_run`. -/
theorem wwpCsrwSatpRun (gen : Nat) (cpu : CPU) (ξ : CtxId) (pc : BitVec 64) (rs1 : BitVec 5)
    (rs1v : BitVec 64) (c : MConf) :
    gen = 0 →
    MConf.mok c →
    pmpAllowsAll c.pmpcfg →
    rs1.toNat ≠ 0 →
    _get_Mstatus_SXL c.mstatus = 2#2 →
    whartRun (GF := GF) cpu ξ 1 c ⊢
      clockCells cpu -∗
      pcIs cpu pc -∗
      gpr cpu rs1 (DFrac.own 1) rs1v -∗
      winstrM (GF := GF) pc false (.CSRReg (0x180#12, .Regidx rs1, zreg, .CSRRW)) -∗
      (whartRun cpu ξ 1 { c with satp := WeakLeafCsrw3.satpLegalized c.satp rs1v } -∗
        clockCells cpu -∗
        pcIs cpu (BitVec.addInt pc 4) -∗
        gpr cpu rs1 (DFrac.own 1) rs1v -∗
        wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu)) -∗
      wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu) := by
  intro h1 h2 h3 h4 h5
  iintro Hrun Ha1 Ha2 Ha3 #Hi Hcont
  icases whartRunOpen (GF := GF) cpu ξ 1 c $$ Hrun with ⟨Hm, Hview⟩
  iapply wwpCsrwSatpO gen cpu ξ pc rs1 rs1v c h1 h2 h3 h4 h5
    $$ Hm Ha1 Ha2 Ha3 Hi Hview
  iintro Hc1 Hc2 Hc3 Hc4 Hview
  iapply Hcont $$ [Hc1 Hview] Hc2 Hc3 Hc4
  iapply whartRunClose (GF := GF) cpu ξ _ _ $$ Hc1 Hview

/-- Rocq `wwp_csrw_medeleg_o`. -/
theorem wwpCsrwMedelegO (gen : Nat) (cpu : CPU) (ξ : CtxId) (pc : BitVec 64) (rs1 : BitVec 5)
    (rs1v : BitVec 64) (c : MConf) :
    gen = 0 →
    MConf.mok c →
    pmpAllowsAll c.pmpcfg →
    rs1.toNat ≠ 0 →
    mConf (GF := GF) cpu (DFrac.own 1) c ⊢
      clockCells cpu -∗
      pcIs cpu pc -∗
      gpr cpu rs1 (DFrac.own 1) rs1v -∗
      winstrM (GF := GF) pc false (.CSRReg (0x302#12, .Regidx rs1, zreg, .CSRRW)) -∗
      wrunning (GF := GF) cpu ξ -∗
      (mConf cpu (DFrac.own 1) { c with medeleg := legalize_medeleg c.medeleg rs1v } -∗
        clockCells cpu -∗
        pcIs cpu (BitVec.addInt pc 4) -∗
        gpr cpu rs1 (DFrac.own 1) rs1v -∗
        wrunning cpu ξ -∗
        wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu)) -∗
      wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu) := by
  intro h1 h2 h3 h4
  iintro Hm Ha1 Ha2 Ha3 #Hi Hrun Hcont
  icases wrunningOpen (GF := GF) cpu ξ $$ Hrun with ⟨%ws, Hws, Hauth⟩
  ihave HF := WeakLeafO.holdTrue (GF := GF) ws
  iapply wwpCsrwMedeleg gen cpu pc rs1 rs1v c ws (iprop(⌜True⌝) : VProp GF) h1 h2 h3 h4
    $$ Hm Ha1 Ha2 Ha3 Hi Hws HF
  iintro %ws' %hle Hc1 Hc2 Hc3 Hc4 Hws -
  iapply WeakLeafO.wwpBupd
  imod ctxRunUpdate (GF := GF) cpu ξ ws ws' hle $$ Hauth with Hauth
  ihave Hrun := WeakLeafO.closeRun (GF := GF) cpu ξ ws' $$ Hws Hauth
  imodintro
  iapply Hcont $$ Hc1 Hc2 Hc3 Hc4 Hrun

/-- Rocq `wwp_csrw_medeleg_run`. -/
theorem wwpCsrwMedelegRun (gen : Nat) (cpu : CPU) (ξ : CtxId) (pc : BitVec 64) (rs1 : BitVec 5)
    (rs1v : BitVec 64) (c : MConf) :
    gen = 0 →
    MConf.mok c →
    pmpAllowsAll c.pmpcfg →
    rs1.toNat ≠ 0 →
    whartRun (GF := GF) cpu ξ 1 c ⊢
      clockCells cpu -∗
      pcIs cpu pc -∗
      gpr cpu rs1 (DFrac.own 1) rs1v -∗
      winstrM (GF := GF) pc false (.CSRReg (0x302#12, .Regidx rs1, zreg, .CSRRW)) -∗
      (whartRun cpu ξ 1 { c with medeleg := legalize_medeleg c.medeleg rs1v } -∗
        clockCells cpu -∗
        pcIs cpu (BitVec.addInt pc 4) -∗
        gpr cpu rs1 (DFrac.own 1) rs1v -∗
        wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu)) -∗
      wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu) := by
  intro h1 h2 h3 h4
  iintro Hrun Ha1 Ha2 Ha3 #Hi Hcont
  icases whartRunOpen (GF := GF) cpu ξ 1 c $$ Hrun with ⟨Hm, Hview⟩
  iapply wwpCsrwMedelegO gen cpu ξ pc rs1 rs1v c h1 h2 h3 h4
    $$ Hm Ha1 Ha2 Ha3 Hi Hview
  iintro Hc1 Hc2 Hc3 Hc4 Hview
  iapply Hcont $$ [Hc1 Hview] Hc2 Hc3 Hc4
  iapply whartRunClose (GF := GF) cpu ξ _ _ $$ Hc1 Hview

/-- Rocq `wwp_csrw_mideleg_o`. -/
theorem wwpCsrwMidelegO (gen : Nat) (cpu : CPU) (ξ : CtxId) (pc : BitVec 64) (rs1 : BitVec 5)
    (rs1v : BitVec 64) (c : MConf) :
    gen = 0 →
    MConf.mok c →
    pmpAllowsAll c.pmpcfg →
    rs1.toNat ≠ 0 →
    mConf (GF := GF) cpu (DFrac.own 1) c ⊢
      clockCells cpu -∗
      pcIs cpu pc -∗
      gpr cpu rs1 (DFrac.own 1) rs1v -∗
      winstrM (GF := GF) pc false (.CSRReg (0x303#12, .Regidx rs1, zreg, .CSRRW)) -∗
      wrunning (GF := GF) cpu ξ -∗
      (mConf cpu (DFrac.own 1) { c with mideleg := WeakLeafCsrw2.midelegLegalized c.mideleg rs1v } -∗
        clockCells cpu -∗
        pcIs cpu (BitVec.addInt pc 4) -∗
        gpr cpu rs1 (DFrac.own 1) rs1v -∗
        wrunning cpu ξ -∗
        wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu)) -∗
      wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu) := by
  intro h1 h2 h3 h4
  iintro Hm Ha1 Ha2 Ha3 #Hi Hrun Hcont
  icases wrunningOpen (GF := GF) cpu ξ $$ Hrun with ⟨%ws, Hws, Hauth⟩
  ihave HF := WeakLeafO.holdTrue (GF := GF) ws
  iapply wwpCsrwMideleg gen cpu pc rs1 rs1v c ws (iprop(⌜True⌝) : VProp GF) h1 h2 h3 h4
    $$ Hm Ha1 Ha2 Ha3 Hi Hws HF
  iintro %ws' %hle Hc1 Hc2 Hc3 Hc4 Hws -
  iapply WeakLeafO.wwpBupd
  imod ctxRunUpdate (GF := GF) cpu ξ ws ws' hle $$ Hauth with Hauth
  ihave Hrun := WeakLeafO.closeRun (GF := GF) cpu ξ ws' $$ Hws Hauth
  imodintro
  iapply Hcont $$ Hc1 Hc2 Hc3 Hc4 Hrun

/-- Rocq `wwp_csrw_mideleg_run`. -/
theorem wwpCsrwMidelegRun (gen : Nat) (cpu : CPU) (ξ : CtxId) (pc : BitVec 64) (rs1 : BitVec 5)
    (rs1v : BitVec 64) (c : MConf) :
    gen = 0 →
    MConf.mok c →
    pmpAllowsAll c.pmpcfg →
    rs1.toNat ≠ 0 →
    whartRun (GF := GF) cpu ξ 1 c ⊢
      clockCells cpu -∗
      pcIs cpu pc -∗
      gpr cpu rs1 (DFrac.own 1) rs1v -∗
      winstrM (GF := GF) pc false (.CSRReg (0x303#12, .Regidx rs1, zreg, .CSRRW)) -∗
      (whartRun cpu ξ 1 { c with mideleg := WeakLeafCsrw2.midelegLegalized c.mideleg rs1v } -∗
        clockCells cpu -∗
        pcIs cpu (BitVec.addInt pc 4) -∗
        gpr cpu rs1 (DFrac.own 1) rs1v -∗
        wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu)) -∗
      wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu) := by
  intro h1 h2 h3 h4
  iintro Hrun Ha1 Ha2 Ha3 #Hi Hcont
  icases whartRunOpen (GF := GF) cpu ξ 1 c $$ Hrun with ⟨Hm, Hview⟩
  iapply wwpCsrwMidelegO gen cpu ξ pc rs1 rs1v c h1 h2 h3 h4
    $$ Hm Ha1 Ha2 Ha3 Hi Hview
  iintro Hc1 Hc2 Hc3 Hc4 Hview
  iapply Hcont $$ [Hc1 Hview] Hc2 Hc3 Hc4
  iapply whartRunClose (GF := GF) cpu ξ _ _ $$ Hc1 Hview

/-- Rocq `wwp_csrw_sie_o`. -/
theorem wwpCsrwSieO (gen : Nat) (cpu : CPU) (ξ : CtxId) (pc : BitVec 64) (rs1 : BitVec 5)
    (rs1v : BitVec 64) (c : MConf) :
    gen = 0 →
    MConf.mok c →
    pmpAllowsAll c.pmpcfg →
    rs1.toNat ≠ 0 →
    mConf (GF := GF) cpu (DFrac.own 1) c ⊢
      clockCells cpu -∗
      pcIs cpu pc -∗
      gpr cpu rs1 (DFrac.own 1) rs1v -∗
      winstrM (GF := GF) pc false (.CSRReg (0x104#12, .Regidx rs1, zreg, .CSRRW)) -∗
      wrunning (GF := GF) cpu ξ -∗
      (mConf cpu (DFrac.own 1) { c with mie := WeakLeafCsrw3.sieNewMie c.mie c.mideleg rs1v } -∗
        clockCells cpu -∗
        pcIs cpu (BitVec.addInt pc 4) -∗
        gpr cpu rs1 (DFrac.own 1) rs1v -∗
        wrunning cpu ξ -∗
        wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu)) -∗
      wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu) := by
  intro h1 h2 h3 h4
  iintro Hm Ha1 Ha2 Ha3 #Hi Hrun Hcont
  icases wrunningOpen (GF := GF) cpu ξ $$ Hrun with ⟨%ws, Hws, Hauth⟩
  ihave HF := WeakLeafO.holdTrue (GF := GF) ws
  iapply wwpCsrwSie gen cpu pc rs1 rs1v c ws (iprop(⌜True⌝) : VProp GF) h1 h2 h3 h4
    $$ Hm Ha1 Ha2 Ha3 Hi Hws HF
  iintro %ws' %hle Hc1 Hc2 Hc3 Hc4 Hws -
  iapply WeakLeafO.wwpBupd
  imod ctxRunUpdate (GF := GF) cpu ξ ws ws' hle $$ Hauth with Hauth
  ihave Hrun := WeakLeafO.closeRun (GF := GF) cpu ξ ws' $$ Hws Hauth
  imodintro
  iapply Hcont $$ Hc1 Hc2 Hc3 Hc4 Hrun

/-- Rocq `wwp_csrw_sie_run`. -/
theorem wwpCsrwSieRun (gen : Nat) (cpu : CPU) (ξ : CtxId) (pc : BitVec 64) (rs1 : BitVec 5)
    (rs1v : BitVec 64) (c : MConf) :
    gen = 0 →
    MConf.mok c →
    pmpAllowsAll c.pmpcfg →
    rs1.toNat ≠ 0 →
    whartRun (GF := GF) cpu ξ 1 c ⊢
      clockCells cpu -∗
      pcIs cpu pc -∗
      gpr cpu rs1 (DFrac.own 1) rs1v -∗
      winstrM (GF := GF) pc false (.CSRReg (0x104#12, .Regidx rs1, zreg, .CSRRW)) -∗
      (whartRun cpu ξ 1 { c with mie := WeakLeafCsrw3.sieNewMie c.mie c.mideleg rs1v } -∗
        clockCells cpu -∗
        pcIs cpu (BitVec.addInt pc 4) -∗
        gpr cpu rs1 (DFrac.own 1) rs1v -∗
        wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu)) -∗
      wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu) := by
  intro h1 h2 h3 h4
  iintro Hrun Ha1 Ha2 Ha3 #Hi Hcont
  icases whartRunOpen (GF := GF) cpu ξ 1 c $$ Hrun with ⟨Hm, Hview⟩
  iapply wwpCsrwSieO gen cpu ξ pc rs1 rs1v c h1 h2 h3 h4
    $$ Hm Ha1 Ha2 Ha3 Hi Hview
  iintro Hc1 Hc2 Hc3 Hc4 Hview
  iapply Hcont $$ [Hc1 Hview] Hc2 Hc3 Hc4
  iapply whartRunClose (GF := GF) cpu ξ _ _ $$ Hc1 Hview

/-- Rocq `wwp_csrw_pmpaddr0_o`. -/
theorem wwpCsrwPmpaddr0O (gen : Nat) (cpu : CPU) (ξ : CtxId) (pc : BitVec 64) (rs1 : BitVec 5)
    (rs1v : BitVec 64) (c : MConf) :
    gen = 0 →
    MConf.mok c →
    pmpAllowsAll c.pmpcfg →
    rs1.toNat ≠ 0 →
    mConf (GF := GF) cpu (DFrac.own 1) c ⊢
      clockCells cpu -∗
      pcIs cpu pc -∗
      gpr cpu rs1 (DFrac.own 1) rs1v -∗
      winstrM (GF := GF) pc false (.CSRReg (0x3B0#12, .Regidx rs1, zreg, .CSRRW)) -∗
      wrunning (GF := GF) cpu ξ -∗
      (mConf cpu (DFrac.own 1)
          { c with pmpaddr := WeakLeafCsrw3.pmp0Newaddr c.pmpcfg c.pmpaddr rs1v } -∗
        clockCells cpu -∗
        pcIs cpu (BitVec.addInt pc 4) -∗
        gpr cpu rs1 (DFrac.own 1) rs1v -∗
        wrunning cpu ξ -∗
        wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu)) -∗
      wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu) := by
  intro h1 h2 h3 h4
  iintro Hm Ha1 Ha2 Ha3 #Hi Hrun Hcont
  icases wrunningOpen (GF := GF) cpu ξ $$ Hrun with ⟨%ws, Hws, Hauth⟩
  ihave HF := WeakLeafO.holdTrue (GF := GF) ws
  iapply wwpCsrwPmpaddr0 gen cpu pc rs1 rs1v c ws (iprop(⌜True⌝) : VProp GF) h1 h2 h3 h4
    $$ Hm Ha1 Ha2 Ha3 Hi Hws HF
  iintro %ws' %hle Hc1 Hc2 Hc3 Hc4 Hws -
  iapply WeakLeafO.wwpBupd
  imod ctxRunUpdate (GF := GF) cpu ξ ws ws' hle $$ Hauth with Hauth
  ihave Hrun := WeakLeafO.closeRun (GF := GF) cpu ξ ws' $$ Hws Hauth
  imodintro
  iapply Hcont $$ Hc1 Hc2 Hc3 Hc4 Hrun

/-- Rocq `wwp_csrw_pmpaddr0_run`. -/
theorem wwpCsrwPmpaddr0Run (gen : Nat) (cpu : CPU) (ξ : CtxId) (pc : BitVec 64) (rs1 : BitVec 5)
    (rs1v : BitVec 64) (c : MConf) :
    gen = 0 →
    MConf.mok c →
    pmpAllowsAll c.pmpcfg →
    rs1.toNat ≠ 0 →
    whartRun (GF := GF) cpu ξ 1 c ⊢
      clockCells cpu -∗
      pcIs cpu pc -∗
      gpr cpu rs1 (DFrac.own 1) rs1v -∗
      winstrM (GF := GF) pc false (.CSRReg (0x3B0#12, .Regidx rs1, zreg, .CSRRW)) -∗
      (whartRun cpu ξ 1
          { c with pmpaddr := WeakLeafCsrw3.pmp0Newaddr c.pmpcfg c.pmpaddr rs1v } -∗
        clockCells cpu -∗
        pcIs cpu (BitVec.addInt pc 4) -∗
        gpr cpu rs1 (DFrac.own 1) rs1v -∗
        wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu)) -∗
      wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu) := by
  intro h1 h2 h3 h4
  iintro Hrun Ha1 Ha2 Ha3 #Hi Hcont
  icases whartRunOpen (GF := GF) cpu ξ 1 c $$ Hrun with ⟨Hm, Hview⟩
  iapply wwpCsrwPmpaddr0O gen cpu ξ pc rs1 rs1v c h1 h2 h3 h4
    $$ Hm Ha1 Ha2 Ha3 Hi Hview
  iintro Hc1 Hc2 Hc3 Hc4 Hview
  iapply Hcont $$ [Hc1 Hview] Hc2 Hc3 Hc4
  iapply whartRunClose (GF := GF) cpu ξ _ _ $$ Hc1 Hview

/-- Rocq `wwp_csrr_mstatus_o`. -/
theorem wwpCsrrMstatusO (gen : Nat) (cpu : CPU) (ξ : CtxId) (pc : BitVec 64) (rd : BitVec 5)
    (ms0 rd0 : BitVec 64) (pmpcfg0 : RegisterType .pmpcfg_n) :
    gen = 0 →
    pmpAllowsAll pmpcfg0 →
    rd.toNat ≠ 0 →
    (_get_Mstatus_MIE ms0 == 1#1) = false →
    (_get_Mstatus_MPRV ms0 == 1#1) = false →
    hwConfig (GF := GF) cpu ⊢
      clockCells cpu -∗
      Register.hart_state ↦ᵣ[cpu] HartState.HART_ACTIVE () -∗
      Register.cur_privilege ↦ᵣ[cpu] Privilege.Machine -∗
      Register.mstatus ↦ᵣ[cpu] ms0 -∗
      Register.pmpcfg_n ↦ᵣ[cpu] pmpcfg0 -∗
      pcIs cpu pc -∗
      gpr cpu rd (DFrac.own 1) rd0 -∗
      winstrM (GF := GF) pc false (.CSRReg (0x300#12, zreg, .Regidx rd, .CSRRS)) -∗
      wrunning (GF := GF) cpu ξ -∗
      (Register.hart_state ↦ᵣ[cpu] HartState.HART_ACTIVE () -∗
        Register.cur_privilege ↦ᵣ[cpu] Privilege.Machine -∗
        Register.mstatus ↦ᵣ[cpu] ms0 -∗
        Register.pmpcfg_n ↦ᵣ[cpu] pmpcfg0 -∗
        clockCells cpu -∗
        pcIs cpu (BitVec.addInt pc 4) -∗
        gpr cpu rd (DFrac.own 1) ms0 -∗
        wrunning cpu ξ -∗
        wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu)) -∗
      wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu) := by
  intro h1 h2 h3 h4 h5
  iintro Hm Ha1 Ha2 Ha3 Ha4 Ha5 Ha6 Ha7 #Hi Hrun Hcont
  icases wrunningOpen (GF := GF) cpu ξ $$ Hrun with ⟨%ws, Hws, Hauth⟩
  ihave HF := WeakLeafO.holdTrue (GF := GF) ws
  iapply wwpCsrrMstatus gen cpu pc rd ms0 rd0 pmpcfg0 ws (iprop(⌜True⌝) : VProp GF) h1 h2 h3 h4 h5
    $$ Hm Ha1 Ha2 Ha3 Ha4 Ha5 Ha6 Ha7 Hi Hws HF
  iintro %ws' %hle Hc1 Hc2 Hc3 Hc4 Hc5 Hc6 Hc7 Hws -
  iapply WeakLeafO.wwpBupd
  imod ctxRunUpdate (GF := GF) cpu ξ ws ws' hle $$ Hauth with Hauth
  ihave Hrun := WeakLeafO.closeRun (GF := GF) cpu ξ ws' $$ Hws Hauth
  imodintro
  iapply Hcont $$ Hc1 Hc2 Hc3 Hc4 Hc5 Hc6 Hc7 Hrun

/-- Rocq `wwp_csrw_mstatus_o`. -/
theorem wwpCsrwMstatusO (gen : Nat) (cpu : CPU) (ξ : CtxId) (pc : BitVec 64) (rs1 : BitVec 5)
    (ms0 rs1v : BitVec 64) (pmpcfg0 : RegisterType .pmpcfg_n) :
    gen = 0 →
    pmpAllowsAll pmpcfg0 →
    is_aligned_vaddr (.Virtaddr pc) 4 = true →
    rs1.toNat ≠ 0 →
    (_get_Mstatus_MIE ms0 == 1#1) = false →
    (_get_Mstatus_MPRV ms0 == 1#1) = false →
    hwConfig (GF := GF) cpu ⊢
      clockCells cpu -∗
      Register.hart_state ↦ᵣ[cpu] HartState.HART_ACTIVE () -∗
      Register.cur_privilege ↦ᵣ[cpu] Privilege.Machine -∗
      Register.mstatus ↦ᵣ[cpu] ms0 -∗
      Register.pmpcfg_n ↦ᵣ[cpu] pmpcfg0 -∗
      pcIs cpu pc -∗
      gpr cpu rs1 (DFrac.own 1) rs1v -∗
      winstrM (GF := GF) pc false (.CSRReg (0x300#12, .Regidx rs1, zreg, .CSRRW)) -∗
      wrunning (GF := GF) cpu ξ -∗
      (Register.hart_state ↦ᵣ[cpu] HartState.HART_ACTIVE () -∗
        Register.cur_privilege ↦ᵣ[cpu] Privilege.Machine -∗
        Register.mstatus ↦ᵣ[cpu] WeakLeafCsrw.mstatusLegalized ms0 rs1v -∗
        Register.pmpcfg_n ↦ᵣ[cpu] pmpcfg0 -∗
        clockCells cpu -∗
        pcIs cpu (BitVec.addInt pc 4) -∗
        gpr cpu rs1 (DFrac.own 1) rs1v -∗
        wrunning cpu ξ -∗
        wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu)) -∗
      wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu) := by
  intro h1 h2 h3 h4 h5 h6
  iintro Hm Ha1 Ha2 Ha3 Ha4 Ha5 Ha6 Ha7 #Hi Hrun Hcont
  icases wrunningOpen (GF := GF) cpu ξ $$ Hrun with ⟨%ws, Hws, Hauth⟩
  ihave HF := WeakLeafO.holdTrue (GF := GF) ws
  iapply wwpCsrwMstatus gen cpu pc rs1 ms0 rs1v pmpcfg0 ws (iprop(⌜True⌝) : VProp GF) h1 h2 h3 h4 h5
    h6
    $$ Hm Ha1 Ha2 Ha3 Ha4 Ha5 Ha6 Ha7 Hi Hws HF
  iintro %ws' %hle Hc1 Hc2 Hc3 Hc4 Hc5 Hc6 Hc7 Hws -
  iapply WeakLeafO.wwpBupd
  imod ctxRunUpdate (GF := GF) cpu ξ ws ws' hle $$ Hauth with Hauth
  ihave Hrun := WeakLeafO.closeRun (GF := GF) cpu ξ ws' $$ Hws Hauth
  imodintro
  iapply Hcont $$ Hc1 Hc2 Hc3 Hc4 Hc5 Hc6 Hc7 Hrun

/-- Rocq `wwp_csrw_pmpcfg0_o`. -/
theorem wwpCsrwPmpcfg0O (gen : Nat) (cpu : CPU) (ξ : CtxId) (pc : BitVec 64) (rs1 : BitVec 5)
    (ms0 rs1v : BitVec 64) (pmpcfg0 : RegisterType .pmpcfg_n) :
    gen = 0 →
    pmpAllowsAll pmpcfg0 →
    rs1.toNat ≠ 0 →
    (_get_Mstatus_MIE ms0 == 1#1) = false →
    (_get_Mstatus_MPRV ms0 == 1#1) = false →
    hwConfig (GF := GF) cpu ⊢
      clockCells cpu -∗
      Register.hart_state ↦ᵣ[cpu] HartState.HART_ACTIVE () -∗
      Register.cur_privilege ↦ᵣ[cpu] Privilege.Machine -∗
      Register.mstatus ↦ᵣ[cpu] ms0 -∗
      Register.pmpcfg_n ↦ᵣ[cpu] pmpcfg0 -∗
      pcIs cpu pc -∗
      gpr cpu rs1 (DFrac.own 1) rs1v -∗
      winstrM (GF := GF) pc false (.CSRReg (0x3A0#12, .Regidx rs1, zreg, .CSRRW)) -∗
      wrunning (GF := GF) cpu ξ -∗
      (Register.hart_state ↦ᵣ[cpu] HartState.HART_ACTIVE () -∗
        Register.cur_privilege ↦ᵣ[cpu] Privilege.Machine -∗
        Register.mstatus ↦ᵣ[cpu] ms0 -∗
        Register.pmpcfg_n ↦ᵣ[cpu] WeakLeafPmpcfg0.pmpcfgWritten rs1v pmpcfg0 -∗
        clockCells cpu -∗
        pcIs cpu (BitVec.addInt pc 4) -∗
        gpr cpu rs1 (DFrac.own 1) rs1v -∗
        wrunning cpu ξ -∗
        wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu)) -∗
      wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu) := by
  intro h1 h2 h3 h4 h5
  iintro Hm Ha1 Ha2 Ha3 Ha4 Ha5 Ha6 Ha7 #Hi Hrun Hcont
  icases wrunningOpen (GF := GF) cpu ξ $$ Hrun with ⟨%ws, Hws, Hauth⟩
  ihave HF := WeakLeafO.holdTrue (GF := GF) ws
  iapply wwpCsrwPmpcfg0 gen cpu pc rs1 ms0 rs1v pmpcfg0 ws (iprop(⌜True⌝) : VProp GF) h1 h2 h3 h4 h5
    $$ Hm Ha1 Ha2 Ha3 Ha4 Ha5 Ha6 Ha7 Hi Hws HF
  iintro %ws' %hle Hc1 Hc2 Hc3 Hc4 Hc5 Hc6 Hc7 Hws -
  iapply WeakLeafO.wwpBupd
  imod ctxRunUpdate (GF := GF) cpu ξ ws ws' hle $$ Hauth with Hauth
  ihave Hrun := WeakLeafO.closeRun (GF := GF) cpu ξ ws' $$ Hws Hauth
  imodintro
  iapply Hcont $$ Hc1 Hc2 Hc3 Hc4 Hc5 Hc6 Hc7 Hrun

end leafo2

end Weak
