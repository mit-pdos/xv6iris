/-
Weak: **leaves with the `wstate` HIDDEN** -- the M-mode wrappers of `Weak/WeakLeafM.lean` with the
hart's `wstate` behind the context token `wrunning cpu ξ` (`_o`), and again behind the ambient
bundle `whartRun cpu ξ q c` (`_run`); §§0-8 (bundle, generic conversion, the register-only ALU
family, csrr, csrw, control flow, mret).  §§9-11 are `Weak/WeakLeafO2.lean`.

Rocq: `iris/WeakLeafO.v` @ xxvzwolszwmp.

The Rocq header, in substance.  `hartWs cpu ws` is an EXACT-valued ghost variable, so a leaf can
only step it by naming both states -- which is why every caller above a leaf carried a `ws`
binder, a `⌜wsLe ws ws'⌝` and a `hartWs` in and out.  Hiding the value under an existential
(`wrunning` = `∃ ws, hartWs cpu ws ∗ ctxRun cpu ξ ws`, `Weak/WeakCtx.lean`) removes that residue:
the `wsLe` the leaf hands back is consumed at the seam (`ctxRunUpdate`) and never reaches the
caller.  The frame is gone too: an objective frame (`cobj ξ R`) stays in the Iris context across
the leaf, so the wrappers instantiate `F := ⌜True⌝` and take no frame argument.  The view token
rides in the ambient bundle `whartRun` (non-fractional on purpose: `mConf` is fractional and
`hartWs` exclusive), so a `_run` step site is SC's, name for name.  `mret` has `_o` only: it
DISSOLVES the M-mode bundle (it sets `cur_privilege` to Supervisor).

**Deviations from Rocq.**
1. VOCABULARY: `Weak/WeakLeafM.lean`'s (its deviation 1), plus `wrunning ξ` ↦ `wrunning cpu ξ`,
   `ctx_view_lb` ↦ `ctxViewLb`, `view_addrs` ↦ `viewAddrs`, `acc_addr` ↦ `WeakInterp.accAddr`,
   `monPred_at R (view_scl T)` ↦ `R.monPred_at (viewScl T)`, `CtxId` explicit after `cpu`.
2. THE BUNDLE (owner decision Q3): Rocq `whart_run ξ q := mmode_config (DfracOwn q) ∗ wrunning ξ`
   ↦ `whartRun cpu ξ q c := mConf cpu (DFrac.own q) c ∗ wrunning cpu ξ` (the config `c` is a
   parameter, as `mConf`'s); Rocq's `pmpcfg_n ↦ᵣ{q}` slot is `clockCells cpu`, as in WeakLeafM.
3. EVERY STATEMENT IS ITS WeakLeafM TWIN'S with `hartWs`/`vwpHold F`/`∀ ws'`/`wsLe` replaced by
   `wrunning`, so WeakLeafM's deviations 2-6 carry over verbatim: no separate cells for CSRs
   inside `mConf` (csrr/csrw menvcfg, mcounteren, sie, TOR `pmpaddr`), `minstret_inv` ↦
   `clockCells` (mret, csrr/csrw mstatus, csrw pmpcfg0, in their leaves' resource order),
   `inRam ea 8`, and the CSR-in-mConf WRITE wrappers (csrw menvcfg, mcounteren, stimecmp; in
   WeakLeafO2 mepc, satp, medeleg, mideleg, sie, pmpaddr0) at `DFrac.own 1` -- `whartRun cpu ξ 1
   c` for `_run` (Rocq: any `q`; the orchestrator's full-fraction check: Rocq's top level
   instantiates `whart_run ξ 1`), with the written CSR returned inside the config.
4. `leafHide` takes the generation `gen` explicitly (Rocq `GenId` class, `WWP Loop`).
5. Lean-only helpers (file-qualified): `WeakLeafO.wwpBupd` (a basic update before `wwpTriv`),
   `WeakLeafO.holdTrue` (Rocq's `vwp_hold_pure` iAssert), `WeakLeafO.toHold`/`ofHold` (curried
   `ctxRunToHold`/`ctxRunOfHold`), `WeakLeafO.addrsKeep` (`ctxRunAddrsGet` keeping the bundle --
   Rocq's `iDestruct … as "#Hlb"`), `WeakLeafO.closeRun` (curried `wrunningClose`).

**Rocq → Lean name map.**  `whart_run` `whartRun`, `whart_run_open` `whartRunOpen`,
`whart_run_close` `whartRunClose`, `leaf_hide` `leafHide`, `wwp_<x>_o` ↦ `wwp<X>O`,
`wwp_<x>_run` ↦ `wwp<X>Run`, `wwp_ld8_tor_rvc_o_own` ↦ `wwpLd8TorRvcOOwn`,
`wwp_ld8_tor_rvc_run_own` ↦ `wwpLd8TorRvcRunOwn` (x as in WeakLeafM's map).  None is in the
duplicated-name table.

**Dropped:** nothing (Rocq 68 declarations; Lean 68 + 6 Lean-only, split 37 + 31 over
WeakLeafO / WeakLeafO2).
-/
import Weak.WeakLeafM
import Weak.WeakCtx

namespace Weak

open Iris Iris.BI Iris.BI.MonPred Iris.ProofMode Iris.Std
open MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D LeanRV64D.Functions

section leafo
variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [WeakGS GF]

/-! ## 0. The ambient bundle -/

/-- Rocq `whart_run` (deviation 2). -/
def whartRun (cpu : CPU) (ξ : CtxId) (q : Qp) (c : MConf) : IProp GF :=
  iprop(mConf cpu (DFrac.own q) c ∗ wrunning cpu ξ)

/-- Rocq `whart_run_open`. -/
theorem whartRunOpen (cpu : CPU) (ξ : CtxId) (q : Qp) (c : MConf) :
    whartRun (GF := GF) cpu ξ q c ⊢ mConf cpu (DFrac.own q) c ∗ wrunning cpu ξ := .rfl

/-- Rocq `whart_run_close`. -/
theorem whartRunClose (cpu : CPU) (ξ : CtxId) (q : Qp) (c : MConf) :
    mConf (GF := GF) cpu (DFrac.own q) c ⊢ wrunning cpu ξ -∗ whartRun cpu ξ q c := by
  unfold whartRun
  iintro H1 H2
  isplitl [H1]
  · iexact H1
  · iexact H2

/-! ### Lean-only helpers (deviation 5) -/

/-- A basic update before the weak loop WP is absorbed. -/
theorem WeakLeafO.wwpBupd (E : CoPset) (e : WExpr) :
    (|==> wwpTriv (hlc := hlc) (GF := GF) E e) ⊢ wwpTriv (hlc := hlc) (GF := GF) E e := by
  unfold wwpTriv
  iintro H
  imod H
  iexact H

/-- The trivial frame. -/
theorem WeakLeafO.holdTrue (ws : Wstate) : ⊢ vwpHold (iprop(⌜True⌝) : VProp GF) ws := by
  iapply (vwpHold_pure (GF := GF) True ws).2
  ipureintro
  trivial

/-- `ctxRunToHold`, curried. -/
theorem WeakLeafO.toHold (cpu : CPU) (ξ : CtxId) (ws : Wstate) (R : VProp GF) :
    ctxRun (GF := GF) cpu ξ ws ⊢ cobj ξ R -∗ ctxRun cpu ξ ws ∗ vwpHold R ws := by
  iintro Ha HR
  iapply ctxRunToHold cpu ξ ws R
  isplitl [Ha]
  · iexact Ha
  · iexact HR

/-- `ctxRunOfHold`, curried. -/
theorem WeakLeafO.ofHold (cpu : CPU) (ξ : CtxId) (ws : Wstate) (R : VProp GF) :
    ctxRun (GF := GF) cpu ξ ws ⊢ vwpHold R ws -∗ ctxRun cpu ξ ws ∗ cobj ξ R := by
  iintro Ha HR
  iapply ctxRunOfHold cpu ξ ws R
  isplitl [Ha]
  · iexact Ha
  · iexact HR

/-- `ctxRunAddrsGet`, keeping the bundle (the floor token is persistent). -/
theorem WeakLeafO.addrsKeep (cpu : CPU) (ξ : CtxId) (ws : Wstate) (f : Nat → Int) (n T : Nat)
    (hj : ∀ j : Nat, j < n → T ≤ flr (wsView ws) (f j)) :
    ctxRun (GF := GF) cpu ξ ws ⊢ ctxRun cpu ξ ws ∗ ctxViewLb ξ (viewAddrs f n T) :=
  persistent_entails_left (ctxRunAddrsGet cpu ξ ws f n T hj)

/-- `wrunningClose`, curried. -/
theorem WeakLeafO.closeRun (cpu : CPU) (ξ : CtxId) (ws : Wstate) :
    hartWs (GF := GF) cpu ws ⊢ ctxRun cpu ξ ws -∗ wrunning cpu ξ := by
  iintro Hw Ha
  iapply wrunningClose cpu ξ ws
  isplitl [Hw]
  · iexact Hw
  · iexact Ha

/-! ## 1. The generic conversion -/

/-- Rocq `leaf_hide` (deviation 4): every ws-threading leaf, once its resources are bundled into
`Pre`/`Post`, is a `wrunning` leaf. -/
theorem leafHide (gen : Nat) (cpu : CPU) (ξ : CtxId) (Pre Post : IProp GF) :
    (∀ ws : Wstate,
      ⊢ Pre -∗ hartWs cpu ws -∗
        (∀ ws' : Wstate, ⌜wsLe ws ws'⌝ -∗ Post -∗ hartWs cpu ws' -∗
          wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu)) -∗
        wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu)) →
    Pre ⊢ wrunning cpu ξ -∗
      (Post -∗ wrunning cpu ξ -∗ wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu)) -∗
      wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu) := by
  intro Hleaf
  iintro HPre Hrun Hcont
  icases wrunningOpen (GF := GF) cpu ξ $$ Hrun with ⟨%ws, Hws, Hauth⟩
  iapply (Hleaf ws) $$ HPre Hws
  iintro %ws' %hle HPost Hws
  iapply WeakLeafO.wwpBupd
  imod ctxRunUpdate (GF := GF) cpu ξ ws ws' hle $$ Hauth with Hauth
  ihave Hrun := WeakLeafO.closeRun (GF := GF) cpu ξ ws' $$ Hws Hauth
  imodintro
  iapply Hcont $$ HPost Hrun

/-! ## 2-8. The wrappers: `_o` (context token) and `_run` (the bundle), per instruction

`lui`/`addi` (is_rvc-generic), the register-only ALU family (one encoding each), csrr
menvcfg/mcounteren/mhartid/time, csrw menvcfg/mcounteren/stimecmp (deviation 3: full fraction),
`jal`, `c.jr`, and `mret` (`_o` only: it dissolves the bundle). -/

/-- Rocq `wwp_lui_o`. -/
theorem wwpLuiO (gen : Nat) (cpu : CPU) (ξ : CtxId) (pc : BitVec 64) (is_rvc : Bool) (rd : BitVec 5)
    (imm : BitVec 20) (m : RegMap) (c : MConf) (q : Qp) :
    gen = 0 →
    MConf.mok c →
    pmpAllowsAll c.pmpcfg →
    rd.toNat ≠ 0 →
    mConf (GF := GF) cpu (DFrac.own q) c ⊢
      clockCells cpu -∗
      pcIs cpu pc -∗
      gprFile cpu m -∗
      winstrM (GF := GF) pc is_rvc (.UTYPE (imm, .Regidx rd, .LUI)) -∗
      wrunning (GF := GF) cpu ξ -∗
      (mConf cpu (DFrac.own q) c -∗
        clockCells cpu -∗
        pcIs cpu (BitVec.addInt pc (if is_rvc then 2 else 4)) -∗
        gprFile cpu (m.set rd (WkEntryEff.luival imm)) -∗
        wrunning cpu ξ -∗
        wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu)) -∗
      wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu) := by
  intro h1 h2 h3 h4
  iintro Hm Ha1 Ha2 Ha3 #Hi Hrun Hcont
  icases wrunningOpen (GF := GF) cpu ξ $$ Hrun with ⟨%ws, Hws, Hauth⟩
  ihave HF := WeakLeafO.holdTrue (GF := GF) ws
  iapply wwpLui gen cpu pc is_rvc rd imm m c q ws (iprop(⌜True⌝) : VProp GF) h1 h2 h3 h4
    $$ Hm Ha1 Ha2 Ha3 Hi Hws HF
  iintro %ws' %hle Hc1 Hc2 Hc3 Hc4 Hws -
  iapply WeakLeafO.wwpBupd
  imod ctxRunUpdate (GF := GF) cpu ξ ws ws' hle $$ Hauth with Hauth
  ihave Hrun := WeakLeafO.closeRun (GF := GF) cpu ξ ws' $$ Hws Hauth
  imodintro
  iapply Hcont $$ Hc1 Hc2 Hc3 Hc4 Hrun

/-- Rocq `wwp_lui_run`. -/
theorem wwpLuiRun (gen : Nat) (cpu : CPU) (ξ : CtxId) (pc : BitVec 64) (is_rvc : Bool) (rd : BitVec 5)
    (imm : BitVec 20) (m : RegMap) (c : MConf) (q : Qp) :
    gen = 0 →
    MConf.mok c →
    pmpAllowsAll c.pmpcfg →
    rd.toNat ≠ 0 →
    whartRun (GF := GF) cpu ξ q c ⊢
      clockCells cpu -∗
      pcIs cpu pc -∗
      gprFile cpu m -∗
      winstrM (GF := GF) pc is_rvc (.UTYPE (imm, .Regidx rd, .LUI)) -∗
      (whartRun cpu ξ q c -∗
        clockCells cpu -∗
        pcIs cpu (BitVec.addInt pc (if is_rvc then 2 else 4)) -∗
        gprFile cpu (m.set rd (WkEntryEff.luival imm)) -∗
        wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu)) -∗
      wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu) := by
  intro h1 h2 h3 h4
  iintro Hrun Ha1 Ha2 Ha3 #Hi Hcont
  icases whartRunOpen (GF := GF) cpu ξ q c $$ Hrun with ⟨Hm, Hview⟩
  iapply wwpLuiO gen cpu ξ pc is_rvc rd imm m c q h1 h2 h3 h4
    $$ Hm Ha1 Ha2 Ha3 Hi Hview
  iintro Hc1 Hc2 Hc3 Hc4 Hview
  iapply Hcont $$ [Hc1 Hview] Hc2 Hc3 Hc4
  iapply whartRunClose (GF := GF) cpu ξ _ _ $$ Hc1 Hview

/-- Rocq `wwp_addi_o`. -/
theorem wwpAddiO (gen : Nat) (cpu : CPU) (ξ : CtxId) (pc : BitVec 64) (is_rvc : Bool)
    (rs1 rd : BitVec 5) (imm : BitVec 12) (m : RegMap) (c : MConf) (q : Qp) :
    gen = 0 →
    MConf.mok c →
    pmpAllowsAll c.pmpcfg →
    rd.toNat ≠ 0 →
    mConf (GF := GF) cpu (DFrac.own q) c ⊢
      clockCells cpu -∗
      pcIs cpu pc -∗
      gprFile cpu m -∗
      winstrM (GF := GF) pc is_rvc (.ITYPE (imm, .Regidx rs1, .Regidx rd, .ADDI)) -∗
      wrunning (GF := GF) cpu ξ -∗
      (mConf cpu (DFrac.own q) c -∗
        clockCells cpu -∗
        pcIs cpu (BitVec.addInt pc (if is_rvc then 2 else 4)) -∗
        gprFile cpu (m.set rd (m.get rs1 + sign_extend (m := 64) imm)) -∗
        wrunning cpu ξ -∗
        wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu)) -∗
      wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu) := by
  intro h1 h2 h3 h4
  iintro Hm Ha1 Ha2 Ha3 #Hi Hrun Hcont
  icases wrunningOpen (GF := GF) cpu ξ $$ Hrun with ⟨%ws, Hws, Hauth⟩
  ihave HF := WeakLeafO.holdTrue (GF := GF) ws
  iapply wwpAddi gen cpu pc is_rvc rs1 rd imm m c q ws (iprop(⌜True⌝) : VProp GF) h1 h2 h3 h4
    $$ Hm Ha1 Ha2 Ha3 Hi Hws HF
  iintro %ws' %hle Hc1 Hc2 Hc3 Hc4 Hws -
  iapply WeakLeafO.wwpBupd
  imod ctxRunUpdate (GF := GF) cpu ξ ws ws' hle $$ Hauth with Hauth
  ihave Hrun := WeakLeafO.closeRun (GF := GF) cpu ξ ws' $$ Hws Hauth
  imodintro
  iapply Hcont $$ Hc1 Hc2 Hc3 Hc4 Hrun

/-- Rocq `wwp_addi_run`. -/
theorem wwpAddiRun (gen : Nat) (cpu : CPU) (ξ : CtxId) (pc : BitVec 64) (is_rvc : Bool)
    (rs1 rd : BitVec 5) (imm : BitVec 12) (m : RegMap) (c : MConf) (q : Qp) :
    gen = 0 →
    MConf.mok c →
    pmpAllowsAll c.pmpcfg →
    rd.toNat ≠ 0 →
    whartRun (GF := GF) cpu ξ q c ⊢
      clockCells cpu -∗
      pcIs cpu pc -∗
      gprFile cpu m -∗
      winstrM (GF := GF) pc is_rvc (.ITYPE (imm, .Regidx rs1, .Regidx rd, .ADDI)) -∗
      (whartRun cpu ξ q c -∗
        clockCells cpu -∗
        pcIs cpu (BitVec.addInt pc (if is_rvc then 2 else 4)) -∗
        gprFile cpu (m.set rd (m.get rs1 + sign_extend (m := 64) imm)) -∗
        wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu)) -∗
      wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu) := by
  intro h1 h2 h3 h4
  iintro Hrun Ha1 Ha2 Ha3 #Hi Hcont
  icases whartRunOpen (GF := GF) cpu ξ q c $$ Hrun with ⟨Hm, Hview⟩
  iapply wwpAddiO gen cpu ξ pc is_rvc rs1 rd imm m c q h1 h2 h3 h4
    $$ Hm Ha1 Ha2 Ha3 Hi Hview
  iintro Hc1 Hc2 Hc3 Hc4 Hview
  iapply Hcont $$ [Hc1 Hview] Hc2 Hc3 Hc4
  iapply whartRunClose (GF := GF) cpu ξ _ _ $$ Hc1 Hview

/-- Rocq `wwp_or_rvc_o`. -/
theorem wwpOrRvcO (gen : Nat) (cpu : CPU) (ξ : CtxId) (pc : BitVec 64) (rs2 rs1 rd : BitVec 5)
    (m : RegMap) (c : MConf) (q : Qp) :
    gen = 0 →
    MConf.mok c →
    pmpAllowsAll c.pmpcfg →
    rd.toNat ≠ 0 →
    mConf (GF := GF) cpu (DFrac.own q) c ⊢
      clockCells cpu -∗
      pcIs cpu pc -∗
      gprFile cpu m -∗
      winstrM (GF := GF) pc true (.RTYPE (.Regidx rs2, .Regidx rs1, .Regidx rd, .OR)) -∗
      wrunning (GF := GF) cpu ξ -∗
      (mConf cpu (DFrac.own q) c -∗
        clockCells cpu -∗
        pcIs cpu (BitVec.addInt pc 2) -∗
        gprFile cpu (m.set rd (m.get rs1 ||| m.get rs2)) -∗
        wrunning cpu ξ -∗
        wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu)) -∗
      wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu) := by
  intro h1 h2 h3 h4
  iintro Hm Ha1 Ha2 Ha3 #Hi Hrun Hcont
  icases wrunningOpen (GF := GF) cpu ξ $$ Hrun with ⟨%ws, Hws, Hauth⟩
  ihave HF := WeakLeafO.holdTrue (GF := GF) ws
  iapply wwpOrRvc gen cpu pc rs2 rs1 rd m c q ws (iprop(⌜True⌝) : VProp GF) h1 h2 h3 h4
    $$ Hm Ha1 Ha2 Ha3 Hi Hws HF
  iintro %ws' %hle Hc1 Hc2 Hc3 Hc4 Hws -
  iapply WeakLeafO.wwpBupd
  imod ctxRunUpdate (GF := GF) cpu ξ ws ws' hle $$ Hauth with Hauth
  ihave Hrun := WeakLeafO.closeRun (GF := GF) cpu ξ ws' $$ Hws Hauth
  imodintro
  iapply Hcont $$ Hc1 Hc2 Hc3 Hc4 Hrun

/-- Rocq `wwp_or_rvc_run`. -/
theorem wwpOrRvcRun (gen : Nat) (cpu : CPU) (ξ : CtxId) (pc : BitVec 64) (rs2 rs1 rd : BitVec 5)
    (m : RegMap) (c : MConf) (q : Qp) :
    gen = 0 →
    MConf.mok c →
    pmpAllowsAll c.pmpcfg →
    rd.toNat ≠ 0 →
    whartRun (GF := GF) cpu ξ q c ⊢
      clockCells cpu -∗
      pcIs cpu pc -∗
      gprFile cpu m -∗
      winstrM (GF := GF) pc true (.RTYPE (.Regidx rs2, .Regidx rs1, .Regidx rd, .OR)) -∗
      (whartRun cpu ξ q c -∗
        clockCells cpu -∗
        pcIs cpu (BitVec.addInt pc 2) -∗
        gprFile cpu (m.set rd (m.get rs1 ||| m.get rs2)) -∗
        wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu)) -∗
      wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu) := by
  intro h1 h2 h3 h4
  iintro Hrun Ha1 Ha2 Ha3 #Hi Hcont
  icases whartRunOpen (GF := GF) cpu ξ q c $$ Hrun with ⟨Hm, Hview⟩
  iapply wwpOrRvcO gen cpu ξ pc rs2 rs1 rd m c q h1 h2 h3 h4
    $$ Hm Ha1 Ha2 Ha3 Hi Hview
  iintro Hc1 Hc2 Hc3 Hc4 Hview
  iapply Hcont $$ [Hc1 Hview] Hc2 Hc3 Hc4
  iapply whartRunClose (GF := GF) cpu ξ _ _ $$ Hc1 Hview

/-- Rocq `wwp_add_rvc_o`. -/
theorem wwpAddRvcO (gen : Nat) (cpu : CPU) (ξ : CtxId) (pc : BitVec 64) (rs2 rs1 rd : BitVec 5)
    (m : RegMap) (c : MConf) (q : Qp) :
    gen = 0 →
    MConf.mok c →
    pmpAllowsAll c.pmpcfg →
    rd.toNat ≠ 0 →
    mConf (GF := GF) cpu (DFrac.own q) c ⊢
      clockCells cpu -∗
      pcIs cpu pc -∗
      gprFile cpu m -∗
      winstrM (GF := GF) pc true (.RTYPE (.Regidx rs2, .Regidx rs1, .Regidx rd, .ADD)) -∗
      wrunning (GF := GF) cpu ξ -∗
      (mConf cpu (DFrac.own q) c -∗
        clockCells cpu -∗
        pcIs cpu (BitVec.addInt pc 2) -∗
        gprFile cpu (m.set rd (m.get rs1 + m.get rs2)) -∗
        wrunning cpu ξ -∗
        wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu)) -∗
      wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu) := by
  intro h1 h2 h3 h4
  iintro Hm Ha1 Ha2 Ha3 #Hi Hrun Hcont
  icases wrunningOpen (GF := GF) cpu ξ $$ Hrun with ⟨%ws, Hws, Hauth⟩
  ihave HF := WeakLeafO.holdTrue (GF := GF) ws
  iapply wwpAddRvc gen cpu pc rs2 rs1 rd m c q ws (iprop(⌜True⌝) : VProp GF) h1 h2 h3 h4
    $$ Hm Ha1 Ha2 Ha3 Hi Hws HF
  iintro %ws' %hle Hc1 Hc2 Hc3 Hc4 Hws -
  iapply WeakLeafO.wwpBupd
  imod ctxRunUpdate (GF := GF) cpu ξ ws ws' hle $$ Hauth with Hauth
  ihave Hrun := WeakLeafO.closeRun (GF := GF) cpu ξ ws' $$ Hws Hauth
  imodintro
  iapply Hcont $$ Hc1 Hc2 Hc3 Hc4 Hrun

/-- Rocq `wwp_add_rvc_run`. -/
theorem wwpAddRvcRun (gen : Nat) (cpu : CPU) (ξ : CtxId) (pc : BitVec 64) (rs2 rs1 rd : BitVec 5)
    (m : RegMap) (c : MConf) (q : Qp) :
    gen = 0 →
    MConf.mok c →
    pmpAllowsAll c.pmpcfg →
    rd.toNat ≠ 0 →
    whartRun (GF := GF) cpu ξ q c ⊢
      clockCells cpu -∗
      pcIs cpu pc -∗
      gprFile cpu m -∗
      winstrM (GF := GF) pc true (.RTYPE (.Regidx rs2, .Regidx rs1, .Regidx rd, .ADD)) -∗
      (whartRun cpu ξ q c -∗
        clockCells cpu -∗
        pcIs cpu (BitVec.addInt pc 2) -∗
        gprFile cpu (m.set rd (m.get rs1 + m.get rs2)) -∗
        wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu)) -∗
      wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu) := by
  intro h1 h2 h3 h4
  iintro Hrun Ha1 Ha2 Ha3 #Hi Hcont
  icases whartRunOpen (GF := GF) cpu ξ q c $$ Hrun with ⟨Hm, Hview⟩
  iapply wwpAddRvcO gen cpu ξ pc rs2 rs1 rd m c q h1 h2 h3 h4
    $$ Hm Ha1 Ha2 Ha3 Hi Hview
  iintro Hc1 Hc2 Hc3 Hc4 Hview
  iapply Hcont $$ [Hc1 Hview] Hc2 Hc3 Hc4
  iapply whartRunClose (GF := GF) cpu ξ _ _ $$ Hc1 Hview

/-- Rocq `wwp_slli_rvc_o`. -/
theorem wwpSlliRvcO (gen : Nat) (cpu : CPU) (ξ : CtxId) (pc : BitVec 64) (rs1 rd : BitVec 5)
    (shamt : BitVec 6) (m : RegMap) (c : MConf) (q : Qp) :
    gen = 0 →
    MConf.mok c →
    pmpAllowsAll c.pmpcfg →
    rd.toNat ≠ 0 →
    mConf (GF := GF) cpu (DFrac.own q) c ⊢
      clockCells cpu -∗
      pcIs cpu pc -∗
      gprFile cpu m -∗
      winstrM (GF := GF) pc true (.SHIFTIOP (shamt, .Regidx rs1, .Regidx rd, .SLLI)) -∗
      wrunning (GF := GF) cpu ξ -∗
      (mConf cpu (DFrac.own q) c -∗
        clockCells cpu -∗
        pcIs cpu (BitVec.addInt pc 2) -∗
        gprFile cpu (m.set rd (shift_bits_left (m.get rs1)
          (Sail.BitVec.extractLsb shamt (Functions.log2_xlen -i 1) 0))) -∗
        wrunning cpu ξ -∗
        wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu)) -∗
      wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu) := by
  intro h1 h2 h3 h4
  iintro Hm Ha1 Ha2 Ha3 #Hi Hrun Hcont
  icases wrunningOpen (GF := GF) cpu ξ $$ Hrun with ⟨%ws, Hws, Hauth⟩
  ihave HF := WeakLeafO.holdTrue (GF := GF) ws
  iapply wwpSlliRvc gen cpu pc rs1 rd shamt m c q ws (iprop(⌜True⌝) : VProp GF) h1 h2 h3 h4
    $$ Hm Ha1 Ha2 Ha3 Hi Hws HF
  iintro %ws' %hle Hc1 Hc2 Hc3 Hc4 Hws -
  iapply WeakLeafO.wwpBupd
  imod ctxRunUpdate (GF := GF) cpu ξ ws ws' hle $$ Hauth with Hauth
  ihave Hrun := WeakLeafO.closeRun (GF := GF) cpu ξ ws' $$ Hws Hauth
  imodintro
  iapply Hcont $$ Hc1 Hc2 Hc3 Hc4 Hrun

/-- Rocq `wwp_slli_rvc_run`. -/
theorem wwpSlliRvcRun (gen : Nat) (cpu : CPU) (ξ : CtxId) (pc : BitVec 64) (rs1 rd : BitVec 5)
    (shamt : BitVec 6) (m : RegMap) (c : MConf) (q : Qp) :
    gen = 0 →
    MConf.mok c →
    pmpAllowsAll c.pmpcfg →
    rd.toNat ≠ 0 →
    whartRun (GF := GF) cpu ξ q c ⊢
      clockCells cpu -∗
      pcIs cpu pc -∗
      gprFile cpu m -∗
      winstrM (GF := GF) pc true (.SHIFTIOP (shamt, .Regidx rs1, .Regidx rd, .SLLI)) -∗
      (whartRun cpu ξ q c -∗
        clockCells cpu -∗
        pcIs cpu (BitVec.addInt pc 2) -∗
        gprFile cpu (m.set rd (shift_bits_left (m.get rs1)
          (Sail.BitVec.extractLsb shamt (Functions.log2_xlen -i 1) 0))) -∗
        wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu)) -∗
      wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu) := by
  intro h1 h2 h3 h4
  iintro Hrun Ha1 Ha2 Ha3 #Hi Hcont
  icases whartRunOpen (GF := GF) cpu ξ q c $$ Hrun with ⟨Hm, Hview⟩
  iapply wwpSlliRvcO gen cpu ξ pc rs1 rd shamt m c q h1 h2 h3 h4
    $$ Hm Ha1 Ha2 Ha3 Hi Hview
  iintro Hc1 Hc2 Hc3 Hc4 Hview
  iapply Hcont $$ [Hc1 Hview] Hc2 Hc3 Hc4
  iapply whartRunClose (GF := GF) cpu ξ _ _ $$ Hc1 Hview

/-- Rocq `wwp_addiw_rvc_o`. -/
theorem wwpAddiwRvcO (gen : Nat) (cpu : CPU) (ξ : CtxId) (pc : BitVec 64) (rs1 rd : BitVec 5)
    (immv : BitVec 12) (m : RegMap) (c : MConf) (q : Qp) :
    gen = 0 →
    MConf.mok c →
    pmpAllowsAll c.pmpcfg →
    rd.toNat ≠ 0 →
    mConf (GF := GF) cpu (DFrac.own q) c ⊢
      clockCells cpu -∗
      pcIs cpu pc -∗
      gprFile cpu m -∗
      winstrM (GF := GF) pc true (.ADDIW (immv, .Regidx rs1, .Regidx rd)) -∗
      wrunning (GF := GF) cpu ξ -∗
      (mConf cpu (DFrac.own q) c -∗
        clockCells cpu -∗
        pcIs cpu (BitVec.addInt pc 2) -∗
        gprFile cpu (m.set rd (sign_extend (m := 64)
          (Sail.BitVec.extractLsb (m.get rs1 + sign_extend (m := 64) immv) 31 0))) -∗
        wrunning cpu ξ -∗
        wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu)) -∗
      wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu) := by
  intro h1 h2 h3 h4
  iintro Hm Ha1 Ha2 Ha3 #Hi Hrun Hcont
  icases wrunningOpen (GF := GF) cpu ξ $$ Hrun with ⟨%ws, Hws, Hauth⟩
  ihave HF := WeakLeafO.holdTrue (GF := GF) ws
  iapply wwpAddiwRvc gen cpu pc rs1 rd immv m c q ws (iprop(⌜True⌝) : VProp GF) h1 h2 h3 h4
    $$ Hm Ha1 Ha2 Ha3 Hi Hws HF
  iintro %ws' %hle Hc1 Hc2 Hc3 Hc4 Hws -
  iapply WeakLeafO.wwpBupd
  imod ctxRunUpdate (GF := GF) cpu ξ ws ws' hle $$ Hauth with Hauth
  ihave Hrun := WeakLeafO.closeRun (GF := GF) cpu ξ ws' $$ Hws Hauth
  imodintro
  iapply Hcont $$ Hc1 Hc2 Hc3 Hc4 Hrun

/-- Rocq `wwp_addiw_rvc_run`. -/
theorem wwpAddiwRvcRun (gen : Nat) (cpu : CPU) (ξ : CtxId) (pc : BitVec 64) (rs1 rd : BitVec 5)
    (immv : BitVec 12) (m : RegMap) (c : MConf) (q : Qp) :
    gen = 0 →
    MConf.mok c →
    pmpAllowsAll c.pmpcfg →
    rd.toNat ≠ 0 →
    whartRun (GF := GF) cpu ξ q c ⊢
      clockCells cpu -∗
      pcIs cpu pc -∗
      gprFile cpu m -∗
      winstrM (GF := GF) pc true (.ADDIW (immv, .Regidx rs1, .Regidx rd)) -∗
      (whartRun cpu ξ q c -∗
        clockCells cpu -∗
        pcIs cpu (BitVec.addInt pc 2) -∗
        gprFile cpu (m.set rd (sign_extend (m := 64)
          (Sail.BitVec.extractLsb (m.get rs1 + sign_extend (m := 64) immv) 31 0))) -∗
        wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu)) -∗
      wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu) := by
  intro h1 h2 h3 h4
  iintro Hrun Ha1 Ha2 Ha3 #Hi Hcont
  icases whartRunOpen (GF := GF) cpu ξ q c $$ Hrun with ⟨Hm, Hview⟩
  iapply wwpAddiwRvcO gen cpu ξ pc rs1 rd immv m c q h1 h2 h3 h4
    $$ Hm Ha1 Ha2 Ha3 Hi Hview
  iintro Hc1 Hc2 Hc3 Hc4 Hview
  iapply Hcont $$ [Hc1 Hview] Hc2 Hc3 Hc4
  iapply whartRunClose (GF := GF) cpu ξ _ _ $$ Hc1 Hview

/-- Rocq `wwp_ori_o`. -/
theorem wwpOriO (gen : Nat) (cpu : CPU) (ξ : CtxId) (pc : BitVec 64) (rs1 rd : BitVec 5)
    (imm : BitVec 12) (m : RegMap) (c : MConf) (q : Qp) :
    gen = 0 →
    MConf.mok c →
    pmpAllowsAll c.pmpcfg →
    rd.toNat ≠ 0 →
    mConf (GF := GF) cpu (DFrac.own q) c ⊢
      clockCells cpu -∗
      pcIs cpu pc -∗
      gprFile cpu m -∗
      winstrM (GF := GF) pc false (.ITYPE (imm, .Regidx rs1, .Regidx rd, .ORI)) -∗
      wrunning (GF := GF) cpu ξ -∗
      (mConf cpu (DFrac.own q) c -∗
        clockCells cpu -∗
        pcIs cpu (BitVec.addInt pc 4) -∗
        gprFile cpu (m.set rd (m.get rs1 ||| sign_extend (m := 64) imm)) -∗
        wrunning cpu ξ -∗
        wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu)) -∗
      wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu) := by
  intro h1 h2 h3 h4
  iintro Hm Ha1 Ha2 Ha3 #Hi Hrun Hcont
  icases wrunningOpen (GF := GF) cpu ξ $$ Hrun with ⟨%ws, Hws, Hauth⟩
  ihave HF := WeakLeafO.holdTrue (GF := GF) ws
  iapply wwpOri gen cpu pc rs1 rd imm m c q ws (iprop(⌜True⌝) : VProp GF) h1 h2 h3 h4
    $$ Hm Ha1 Ha2 Ha3 Hi Hws HF
  iintro %ws' %hle Hc1 Hc2 Hc3 Hc4 Hws -
  iapply WeakLeafO.wwpBupd
  imod ctxRunUpdate (GF := GF) cpu ξ ws ws' hle $$ Hauth with Hauth
  ihave Hrun := WeakLeafO.closeRun (GF := GF) cpu ξ ws' $$ Hws Hauth
  imodintro
  iapply Hcont $$ Hc1 Hc2 Hc3 Hc4 Hrun

/-- Rocq `wwp_ori_run`. -/
theorem wwpOriRun (gen : Nat) (cpu : CPU) (ξ : CtxId) (pc : BitVec 64) (rs1 rd : BitVec 5)
    (imm : BitVec 12) (m : RegMap) (c : MConf) (q : Qp) :
    gen = 0 →
    MConf.mok c →
    pmpAllowsAll c.pmpcfg →
    rd.toNat ≠ 0 →
    whartRun (GF := GF) cpu ξ q c ⊢
      clockCells cpu -∗
      pcIs cpu pc -∗
      gprFile cpu m -∗
      winstrM (GF := GF) pc false (.ITYPE (imm, .Regidx rs1, .Regidx rd, .ORI)) -∗
      (whartRun cpu ξ q c -∗
        clockCells cpu -∗
        pcIs cpu (BitVec.addInt pc 4) -∗
        gprFile cpu (m.set rd (m.get rs1 ||| sign_extend (m := 64) imm)) -∗
        wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu)) -∗
      wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu) := by
  intro h1 h2 h3 h4
  iintro Hrun Ha1 Ha2 Ha3 #Hi Hcont
  icases whartRunOpen (GF := GF) cpu ξ q c $$ Hrun with ⟨Hm, Hview⟩
  iapply wwpOriO gen cpu ξ pc rs1 rd imm m c q h1 h2 h3 h4
    $$ Hm Ha1 Ha2 Ha3 Hi Hview
  iintro Hc1 Hc2 Hc3 Hc4 Hview
  iapply Hcont $$ [Hc1 Hview] Hc2 Hc3 Hc4
  iapply whartRunClose (GF := GF) cpu ξ _ _ $$ Hc1 Hview

/-- Rocq `wwp_csrr_menvcfg_o`. -/
theorem wwpCsrrMenvcfgO (gen : Nat) (cpu : CPU) (ξ : CtxId) (pc : BitVec 64) (rd : BitVec 5)
    (rd0 : BitVec 64) (c : MConf) (q : Qp) :
    gen = 0 →
    MConf.mok c →
    pmpAllowsAll c.pmpcfg →
    rd.toNat ≠ 0 →
    mConf (GF := GF) cpu (DFrac.own q) c ⊢
      clockCells cpu -∗
      pcIs cpu pc -∗
      gpr cpu rd (DFrac.own 1) rd0 -∗
      winstrM (GF := GF) pc false (.CSRReg (0x30A#12, zreg, .Regidx rd, .CSRRS)) -∗
      wrunning (GF := GF) cpu ξ -∗
      (mConf cpu (DFrac.own q) c -∗
        clockCells cpu -∗
        pcIs cpu (BitVec.addInt pc 4) -∗
        gpr cpu rd (DFrac.own 1) c.menvcfg -∗
        wrunning cpu ξ -∗
        wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu)) -∗
      wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu) := by
  intro h1 h2 h3 h4
  iintro Hm Ha1 Ha2 Ha3 #Hi Hrun Hcont
  icases wrunningOpen (GF := GF) cpu ξ $$ Hrun with ⟨%ws, Hws, Hauth⟩
  ihave HF := WeakLeafO.holdTrue (GF := GF) ws
  iapply wwpCsrrMenvcfg gen cpu pc rd rd0 c q ws (iprop(⌜True⌝) : VProp GF) h1 h2 h3 h4
    $$ Hm Ha1 Ha2 Ha3 Hi Hws HF
  iintro %ws' %hle Hc1 Hc2 Hc3 Hc4 Hws -
  iapply WeakLeafO.wwpBupd
  imod ctxRunUpdate (GF := GF) cpu ξ ws ws' hle $$ Hauth with Hauth
  ihave Hrun := WeakLeafO.closeRun (GF := GF) cpu ξ ws' $$ Hws Hauth
  imodintro
  iapply Hcont $$ Hc1 Hc2 Hc3 Hc4 Hrun

/-- Rocq `wwp_csrr_menvcfg_run`. -/
theorem wwpCsrrMenvcfgRun (gen : Nat) (cpu : CPU) (ξ : CtxId) (pc : BitVec 64) (rd : BitVec 5)
    (rd0 : BitVec 64) (c : MConf) (q : Qp) :
    gen = 0 →
    MConf.mok c →
    pmpAllowsAll c.pmpcfg →
    rd.toNat ≠ 0 →
    whartRun (GF := GF) cpu ξ q c ⊢
      clockCells cpu -∗
      pcIs cpu pc -∗
      gpr cpu rd (DFrac.own 1) rd0 -∗
      winstrM (GF := GF) pc false (.CSRReg (0x30A#12, zreg, .Regidx rd, .CSRRS)) -∗
      (whartRun cpu ξ q c -∗
        clockCells cpu -∗
        pcIs cpu (BitVec.addInt pc 4) -∗
        gpr cpu rd (DFrac.own 1) c.menvcfg -∗
        wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu)) -∗
      wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu) := by
  intro h1 h2 h3 h4
  iintro Hrun Ha1 Ha2 Ha3 #Hi Hcont
  icases whartRunOpen (GF := GF) cpu ξ q c $$ Hrun with ⟨Hm, Hview⟩
  iapply wwpCsrrMenvcfgO gen cpu ξ pc rd rd0 c q h1 h2 h3 h4
    $$ Hm Ha1 Ha2 Ha3 Hi Hview
  iintro Hc1 Hc2 Hc3 Hc4 Hview
  iapply Hcont $$ [Hc1 Hview] Hc2 Hc3 Hc4
  iapply whartRunClose (GF := GF) cpu ξ _ _ $$ Hc1 Hview

/-- Rocq `wwp_csrr_mcounteren_o`. -/
theorem wwpCsrrMcounterenO (gen : Nat) (cpu : CPU) (ξ : CtxId) (pc : BitVec 64) (rd : BitVec 5)
    (rd0 : BitVec 64) (c : MConf) (q : Qp) :
    gen = 0 →
    MConf.mok c →
    pmpAllowsAll c.pmpcfg →
    rd.toNat ≠ 0 →
    mConf (GF := GF) cpu (DFrac.own q) c ⊢
      clockCells cpu -∗
      pcIs cpu pc -∗
      gpr cpu rd (DFrac.own 1) rd0 -∗
      winstrM (GF := GF) pc false (.CSRReg (0x306#12, zreg, .Regidx rd, .CSRRS)) -∗
      wrunning (GF := GF) cpu ξ -∗
      (mConf cpu (DFrac.own q) c -∗
        clockCells cpu -∗
        pcIs cpu (BitVec.addInt pc 4) -∗
        gpr cpu rd (DFrac.own 1) (zero_extend (m := 64) c.mcounteren) -∗
        wrunning cpu ξ -∗
        wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu)) -∗
      wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu) := by
  intro h1 h2 h3 h4
  iintro Hm Ha1 Ha2 Ha3 #Hi Hrun Hcont
  icases wrunningOpen (GF := GF) cpu ξ $$ Hrun with ⟨%ws, Hws, Hauth⟩
  ihave HF := WeakLeafO.holdTrue (GF := GF) ws
  iapply wwpCsrrMcounteren gen cpu pc rd rd0 c q ws (iprop(⌜True⌝) : VProp GF) h1 h2 h3 h4
    $$ Hm Ha1 Ha2 Ha3 Hi Hws HF
  iintro %ws' %hle Hc1 Hc2 Hc3 Hc4 Hws -
  iapply WeakLeafO.wwpBupd
  imod ctxRunUpdate (GF := GF) cpu ξ ws ws' hle $$ Hauth with Hauth
  ihave Hrun := WeakLeafO.closeRun (GF := GF) cpu ξ ws' $$ Hws Hauth
  imodintro
  iapply Hcont $$ Hc1 Hc2 Hc3 Hc4 Hrun

/-- Rocq `wwp_csrr_mcounteren_run`. -/
theorem wwpCsrrMcounterenRun (gen : Nat) (cpu : CPU) (ξ : CtxId) (pc : BitVec 64) (rd : BitVec 5)
    (rd0 : BitVec 64) (c : MConf) (q : Qp) :
    gen = 0 →
    MConf.mok c →
    pmpAllowsAll c.pmpcfg →
    rd.toNat ≠ 0 →
    whartRun (GF := GF) cpu ξ q c ⊢
      clockCells cpu -∗
      pcIs cpu pc -∗
      gpr cpu rd (DFrac.own 1) rd0 -∗
      winstrM (GF := GF) pc false (.CSRReg (0x306#12, zreg, .Regidx rd, .CSRRS)) -∗
      (whartRun cpu ξ q c -∗
        clockCells cpu -∗
        pcIs cpu (BitVec.addInt pc 4) -∗
        gpr cpu rd (DFrac.own 1) (zero_extend (m := 64) c.mcounteren) -∗
        wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu)) -∗
      wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu) := by
  intro h1 h2 h3 h4
  iintro Hrun Ha1 Ha2 Ha3 #Hi Hcont
  icases whartRunOpen (GF := GF) cpu ξ q c $$ Hrun with ⟨Hm, Hview⟩
  iapply wwpCsrrMcounterenO gen cpu ξ pc rd rd0 c q h1 h2 h3 h4
    $$ Hm Ha1 Ha2 Ha3 Hi Hview
  iintro Hc1 Hc2 Hc3 Hc4 Hview
  iapply Hcont $$ [Hc1 Hview] Hc2 Hc3 Hc4
  iapply whartRunClose (GF := GF) cpu ξ _ _ $$ Hc1 Hview

/-- Rocq `wwp_csrr_mhartid_o`. -/
theorem wwpCsrrMhartidO (gen : Nat) (cpu : CPU) (ξ : CtxId) (pc : BitVec 64) (rd : BitVec 5)
    (mhartid_in rd0 : BitVec 64) (c : MConf) (q : Qp) :
    gen = 0 →
    MConf.mok c →
    pmpAllowsAll c.pmpcfg →
    rd.toNat ≠ 0 →
    mConf (GF := GF) cpu (DFrac.own q) c ⊢
      clockCells cpu -∗
      pcIs cpu pc -∗
      Register.mhartid ↦ᵣ[cpu] mhartid_in -∗
      gpr cpu rd (DFrac.own 1) rd0 -∗
      winstrM (GF := GF) pc false (.CSRReg (0xF14#12, zreg, .Regidx rd, .CSRRS)) -∗
      wrunning (GF := GF) cpu ξ -∗
      (mConf cpu (DFrac.own q) c -∗
        clockCells cpu -∗
        pcIs cpu (BitVec.addInt pc 4) -∗
        gpr cpu rd (DFrac.own 1) mhartid_in -∗
        Register.mhartid ↦ᵣ[cpu] mhartid_in -∗
        wrunning cpu ξ -∗
        wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu)) -∗
      wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu) := by
  intro h1 h2 h3 h4
  iintro Hm Ha1 Ha2 Ha3 Ha4 #Hi Hrun Hcont
  icases wrunningOpen (GF := GF) cpu ξ $$ Hrun with ⟨%ws, Hws, Hauth⟩
  ihave HF := WeakLeafO.holdTrue (GF := GF) ws
  iapply wwpCsrrMhartid gen cpu pc rd mhartid_in rd0 c q ws (iprop(⌜True⌝) : VProp GF) h1 h2 h3 h4
    $$ Hm Ha1 Ha2 Ha3 Ha4 Hi Hws HF
  iintro %ws' %hle Hc1 Hc2 Hc3 Hc4 Hc5 Hws -
  iapply WeakLeafO.wwpBupd
  imod ctxRunUpdate (GF := GF) cpu ξ ws ws' hle $$ Hauth with Hauth
  ihave Hrun := WeakLeafO.closeRun (GF := GF) cpu ξ ws' $$ Hws Hauth
  imodintro
  iapply Hcont $$ Hc1 Hc2 Hc3 Hc4 Hc5 Hrun

/-- Rocq `wwp_csrr_mhartid_run`. -/
theorem wwpCsrrMhartidRun (gen : Nat) (cpu : CPU) (ξ : CtxId) (pc : BitVec 64) (rd : BitVec 5)
    (mhartid_in rd0 : BitVec 64) (c : MConf) (q : Qp) :
    gen = 0 →
    MConf.mok c →
    pmpAllowsAll c.pmpcfg →
    rd.toNat ≠ 0 →
    whartRun (GF := GF) cpu ξ q c ⊢
      clockCells cpu -∗
      pcIs cpu pc -∗
      Register.mhartid ↦ᵣ[cpu] mhartid_in -∗
      gpr cpu rd (DFrac.own 1) rd0 -∗
      winstrM (GF := GF) pc false (.CSRReg (0xF14#12, zreg, .Regidx rd, .CSRRS)) -∗
      (whartRun cpu ξ q c -∗
        clockCells cpu -∗
        pcIs cpu (BitVec.addInt pc 4) -∗
        gpr cpu rd (DFrac.own 1) mhartid_in -∗
        Register.mhartid ↦ᵣ[cpu] mhartid_in -∗
        wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu)) -∗
      wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu) := by
  intro h1 h2 h3 h4
  iintro Hrun Ha1 Ha2 Ha3 Ha4 #Hi Hcont
  icases whartRunOpen (GF := GF) cpu ξ q c $$ Hrun with ⟨Hm, Hview⟩
  iapply wwpCsrrMhartidO gen cpu ξ pc rd mhartid_in rd0 c q h1 h2 h3 h4
    $$ Hm Ha1 Ha2 Ha3 Ha4 Hi Hview
  iintro Hc1 Hc2 Hc3 Hc4 Hc5 Hview
  iapply Hcont $$ [Hc1 Hview] Hc2 Hc3 Hc4 Hc5
  iapply whartRunClose (GF := GF) cpu ξ _ _ $$ Hc1 Hview

/-- Rocq `wwp_csrr_time_o`. -/
theorem wwpCsrrTimeO (gen : Nat) (cpu : CPU) (ξ : CtxId) (pc : BitVec 64) (rd : BitVec 5)
    (rd0 : BitVec 64) (c : MConf) (q : Qp) :
    gen = 0 →
    MConf.mok c →
    pmpAllowsAll c.pmpcfg →
    rd.toNat ≠ 0 →
    mConf (GF := GF) cpu (DFrac.own q) c ⊢
      clockCells cpu -∗
      pcIs cpu pc -∗
      gpr cpu rd (DFrac.own 1) rd0 -∗
      winstrM (GF := GF) pc false (.CSRReg (0xC01#12, zreg, .Regidx rd, .CSRRS)) -∗
      wrunning (GF := GF) cpu ξ -∗
      (∀ tv : BitVec 64,
        mConf cpu (DFrac.own q) c -∗
        clockCells cpu -∗
        pcIs cpu (BitVec.addInt pc 4) -∗
        gpr cpu rd (DFrac.own 1) tv -∗
        wrunning cpu ξ -∗
        wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu)) -∗
      wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu) := by
  intro h1 h2 h3 h4
  iintro Hm Ha1 Ha2 Ha3 #Hi Hrun Hcont
  icases wrunningOpen (GF := GF) cpu ξ $$ Hrun with ⟨%ws, Hws, Hauth⟩
  ihave HF := WeakLeafO.holdTrue (GF := GF) ws
  iapply wwpCsrrTime gen cpu pc rd rd0 c q ws (iprop(⌜True⌝) : VProp GF) h1 h2 h3 h4
    $$ Hm Ha1 Ha2 Ha3 Hi Hws HF
  iintro %tv %ws' %hle Hc1 Hc2 Hc3 Hc4 Hws -
  iapply WeakLeafO.wwpBupd
  imod ctxRunUpdate (GF := GF) cpu ξ ws ws' hle $$ Hauth with Hauth
  ihave Hrun := WeakLeafO.closeRun (GF := GF) cpu ξ ws' $$ Hws Hauth
  imodintro
  iapply Hcont $$ %tv Hc1 Hc2 Hc3 Hc4 Hrun

/-- Rocq `wwp_csrr_time_run`. -/
theorem wwpCsrrTimeRun (gen : Nat) (cpu : CPU) (ξ : CtxId) (pc : BitVec 64) (rd : BitVec 5)
    (rd0 : BitVec 64) (c : MConf) (q : Qp) :
    gen = 0 →
    MConf.mok c →
    pmpAllowsAll c.pmpcfg →
    rd.toNat ≠ 0 →
    whartRun (GF := GF) cpu ξ q c ⊢
      clockCells cpu -∗
      pcIs cpu pc -∗
      gpr cpu rd (DFrac.own 1) rd0 -∗
      winstrM (GF := GF) pc false (.CSRReg (0xC01#12, zreg, .Regidx rd, .CSRRS)) -∗
      (∀ tv : BitVec 64,
        whartRun cpu ξ q c -∗
        clockCells cpu -∗
        pcIs cpu (BitVec.addInt pc 4) -∗
        gpr cpu rd (DFrac.own 1) tv -∗
        wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu)) -∗
      wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu) := by
  intro h1 h2 h3 h4
  iintro Hrun Ha1 Ha2 Ha3 #Hi Hcont
  icases whartRunOpen (GF := GF) cpu ξ q c $$ Hrun with ⟨Hm, Hview⟩
  iapply wwpCsrrTimeO gen cpu ξ pc rd rd0 c q h1 h2 h3 h4
    $$ Hm Ha1 Ha2 Ha3 Hi Hview
  iintro %tv Hc1 Hc2 Hc3 Hc4 Hview
  iapply Hcont $$ %tv [Hc1 Hview] Hc2 Hc3 Hc4
  iapply whartRunClose (GF := GF) cpu ξ _ _ $$ Hc1 Hview

/-- Rocq `wwp_csrw_menvcfg_o`. -/
theorem wwpCsrwMenvcfgO (gen : Nat) (cpu : CPU) (ξ : CtxId) (pc : BitVec 64) (rs1 : BitVec 5)
    (rs1v : BitVec 64) (c : MConf) :
    gen = 0 →
    MConf.mok c →
    pmpAllowsAll c.pmpcfg →
    rs1.toNat ≠ 0 →
    mConf (GF := GF) cpu (DFrac.own 1) c ⊢
      clockCells cpu -∗
      pcIs cpu pc -∗
      gpr cpu rs1 (DFrac.own 1) rs1v -∗
      winstrM (GF := GF) pc false (.CSRReg (0x30A#12, .Regidx rs1, zreg, .CSRRW)) -∗
      wrunning (GF := GF) cpu ξ -∗
      (mConf cpu (DFrac.own 1) { c with menvcfg := WeakLeafCsrw2.menvcfgLegalized c.menvcfg rs1v } -∗
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
  iapply wwpCsrwMenvcfg gen cpu pc rs1 rs1v c ws (iprop(⌜True⌝) : VProp GF) h1 h2 h3 h4
    $$ Hm Ha1 Ha2 Ha3 Hi Hws HF
  iintro %ws' %hle Hc1 Hc2 Hc3 Hc4 Hws -
  iapply WeakLeafO.wwpBupd
  imod ctxRunUpdate (GF := GF) cpu ξ ws ws' hle $$ Hauth with Hauth
  ihave Hrun := WeakLeafO.closeRun (GF := GF) cpu ξ ws' $$ Hws Hauth
  imodintro
  iapply Hcont $$ Hc1 Hc2 Hc3 Hc4 Hrun

/-- Rocq `wwp_csrw_menvcfg_run`. -/
theorem wwpCsrwMenvcfgRun (gen : Nat) (cpu : CPU) (ξ : CtxId) (pc : BitVec 64) (rs1 : BitVec 5)
    (rs1v : BitVec 64) (c : MConf) :
    gen = 0 →
    MConf.mok c →
    pmpAllowsAll c.pmpcfg →
    rs1.toNat ≠ 0 →
    whartRun (GF := GF) cpu ξ 1 c ⊢
      clockCells cpu -∗
      pcIs cpu pc -∗
      gpr cpu rs1 (DFrac.own 1) rs1v -∗
      winstrM (GF := GF) pc false (.CSRReg (0x30A#12, .Regidx rs1, zreg, .CSRRW)) -∗
      (whartRun cpu ξ 1 { c with menvcfg := WeakLeafCsrw2.menvcfgLegalized c.menvcfg rs1v } -∗
        clockCells cpu -∗
        pcIs cpu (BitVec.addInt pc 4) -∗
        gpr cpu rs1 (DFrac.own 1) rs1v -∗
        wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu)) -∗
      wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu) := by
  intro h1 h2 h3 h4
  iintro Hrun Ha1 Ha2 Ha3 #Hi Hcont
  icases whartRunOpen (GF := GF) cpu ξ 1 c $$ Hrun with ⟨Hm, Hview⟩
  iapply wwpCsrwMenvcfgO gen cpu ξ pc rs1 rs1v c h1 h2 h3 h4
    $$ Hm Ha1 Ha2 Ha3 Hi Hview
  iintro Hc1 Hc2 Hc3 Hc4 Hview
  iapply Hcont $$ [Hc1 Hview] Hc2 Hc3 Hc4
  iapply whartRunClose (GF := GF) cpu ξ _ _ $$ Hc1 Hview

/-- Rocq `wwp_csrw_mcounteren_o`. -/
theorem wwpCsrwMcounterenO (gen : Nat) (cpu : CPU) (ξ : CtxId) (pc : BitVec 64) (rs1 : BitVec 5)
    (rs1v : BitVec 64) (c : MConf) :
    gen = 0 →
    MConf.mok c →
    pmpAllowsAll c.pmpcfg →
    rs1.toNat ≠ 0 →
    mConf (GF := GF) cpu (DFrac.own 1) c ⊢
      clockCells cpu -∗
      pcIs cpu pc -∗
      gpr cpu rs1 (DFrac.own 1) rs1v -∗
      winstrM (GF := GF) pc false (.CSRReg (0x306#12, .Regidx rs1, zreg, .CSRRW)) -∗
      wrunning (GF := GF) cpu ξ -∗
      (mConf cpu (DFrac.own 1) { c with mcounteren := legalize_mcounteren c.mcounteren rs1v } -∗
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
  iapply wwpCsrwMcounteren gen cpu pc rs1 rs1v c ws (iprop(⌜True⌝) : VProp GF) h1 h2 h3 h4
    $$ Hm Ha1 Ha2 Ha3 Hi Hws HF
  iintro %ws' %hle Hc1 Hc2 Hc3 Hc4 Hws -
  iapply WeakLeafO.wwpBupd
  imod ctxRunUpdate (GF := GF) cpu ξ ws ws' hle $$ Hauth with Hauth
  ihave Hrun := WeakLeafO.closeRun (GF := GF) cpu ξ ws' $$ Hws Hauth
  imodintro
  iapply Hcont $$ Hc1 Hc2 Hc3 Hc4 Hrun

/-- Rocq `wwp_csrw_mcounteren_run`. -/
theorem wwpCsrwMcounterenRun (gen : Nat) (cpu : CPU) (ξ : CtxId) (pc : BitVec 64) (rs1 : BitVec 5)
    (rs1v : BitVec 64) (c : MConf) :
    gen = 0 →
    MConf.mok c →
    pmpAllowsAll c.pmpcfg →
    rs1.toNat ≠ 0 →
    whartRun (GF := GF) cpu ξ 1 c ⊢
      clockCells cpu -∗
      pcIs cpu pc -∗
      gpr cpu rs1 (DFrac.own 1) rs1v -∗
      winstrM (GF := GF) pc false (.CSRReg (0x306#12, .Regidx rs1, zreg, .CSRRW)) -∗
      (whartRun cpu ξ 1 { c with mcounteren := legalize_mcounteren c.mcounteren rs1v } -∗
        clockCells cpu -∗
        pcIs cpu (BitVec.addInt pc 4) -∗
        gpr cpu rs1 (DFrac.own 1) rs1v -∗
        wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu)) -∗
      wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu) := by
  intro h1 h2 h3 h4
  iintro Hrun Ha1 Ha2 Ha3 #Hi Hcont
  icases whartRunOpen (GF := GF) cpu ξ 1 c $$ Hrun with ⟨Hm, Hview⟩
  iapply wwpCsrwMcounterenO gen cpu ξ pc rs1 rs1v c h1 h2 h3 h4
    $$ Hm Ha1 Ha2 Ha3 Hi Hview
  iintro Hc1 Hc2 Hc3 Hc4 Hview
  iapply Hcont $$ [Hc1 Hview] Hc2 Hc3 Hc4
  iapply whartRunClose (GF := GF) cpu ξ _ _ $$ Hc1 Hview

/-- Rocq `wwp_csrw_stimecmp_o`. -/
theorem wwpCsrwStimecmpO (gen : Nat) (cpu : CPU) (ξ : CtxId) (pc : BitVec 64) (rs1 : BitVec 5)
    (rs1v : BitVec 64) (c : MConf) :
    gen = 0 →
    MConf.mok c →
    pmpAllowsAll c.pmpcfg →
    rs1.toNat ≠ 0 →
    mConf (GF := GF) cpu (DFrac.own 1) c ⊢
      clockCells cpu -∗
      pcIs cpu pc -∗
      gpr cpu rs1 (DFrac.own 1) rs1v -∗
      winstrM (GF := GF) pc false (.CSRReg (0x14D#12, .Regidx rs1, zreg, .CSRRW)) -∗
      wrunning (GF := GF) cpu ξ -∗
      (mConf cpu (DFrac.own 1) { c with stimecmp := stimecmpLegalized c.stimecmp rs1v } -∗
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
  iapply wwpCsrwStimecmp gen cpu pc rs1 rs1v c ws (iprop(⌜True⌝) : VProp GF) h1 h2 h3 h4
    $$ Hm Ha1 Ha2 Ha3 Hi Hws HF
  iintro %ws' %hle Hc1 Hc2 Hc3 Hc4 Hws -
  iapply WeakLeafO.wwpBupd
  imod ctxRunUpdate (GF := GF) cpu ξ ws ws' hle $$ Hauth with Hauth
  ihave Hrun := WeakLeafO.closeRun (GF := GF) cpu ξ ws' $$ Hws Hauth
  imodintro
  iapply Hcont $$ Hc1 Hc2 Hc3 Hc4 Hrun

/-- Rocq `wwp_csrw_stimecmp_run`. -/
theorem wwpCsrwStimecmpRun (gen : Nat) (cpu : CPU) (ξ : CtxId) (pc : BitVec 64) (rs1 : BitVec 5)
    (rs1v : BitVec 64) (c : MConf) :
    gen = 0 →
    MConf.mok c →
    pmpAllowsAll c.pmpcfg →
    rs1.toNat ≠ 0 →
    whartRun (GF := GF) cpu ξ 1 c ⊢
      clockCells cpu -∗
      pcIs cpu pc -∗
      gpr cpu rs1 (DFrac.own 1) rs1v -∗
      winstrM (GF := GF) pc false (.CSRReg (0x14D#12, .Regidx rs1, zreg, .CSRRW)) -∗
      (whartRun cpu ξ 1 { c with stimecmp := stimecmpLegalized c.stimecmp rs1v } -∗
        clockCells cpu -∗
        pcIs cpu (BitVec.addInt pc 4) -∗
        gpr cpu rs1 (DFrac.own 1) rs1v -∗
        wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu)) -∗
      wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu) := by
  intro h1 h2 h3 h4
  iintro Hrun Ha1 Ha2 Ha3 #Hi Hcont
  icases whartRunOpen (GF := GF) cpu ξ 1 c $$ Hrun with ⟨Hm, Hview⟩
  iapply wwpCsrwStimecmpO gen cpu ξ pc rs1 rs1v c h1 h2 h3 h4
    $$ Hm Ha1 Ha2 Ha3 Hi Hview
  iintro Hc1 Hc2 Hc3 Hc4 Hview
  iapply Hcont $$ [Hc1 Hview] Hc2 Hc3 Hc4
  iapply whartRunClose (GF := GF) cpu ξ _ _ $$ Hc1 Hview

/-- Rocq `wwp_jal_o`. -/
theorem wwpJalO (gen : Nat) (cpu : CPU) (ξ : CtxId) (pc : BitVec 64) (rd : BitVec 5)
    (imm : BitVec 21) (rdv0 : BitVec 64) (c : MConf) (q : Qp) :
    gen = 0 →
    MConf.mok c →
    pmpAllowsAll c.pmpcfg →
    rd.toNat ≠ 0 →
    is_aligned_paddr (.Physaddr (pc + sign_extend (m := 64) imm)) 4 = true →
    mConf (GF := GF) cpu (DFrac.own q) c ⊢
      clockCells cpu -∗
      pcIs cpu pc -∗
      gpr cpu rd (DFrac.own 1) rdv0 -∗
      winstrM (GF := GF) pc false (.JAL (imm, .Regidx rd)) -∗
      wrunning (GF := GF) cpu ξ -∗
      (mConf cpu (DFrac.own q) c -∗
        clockCells cpu -∗
        pcIs cpu (pc + sign_extend (m := 64) imm) -∗
        gpr cpu rd (DFrac.own 1) (BitVec.addInt pc 4) -∗
        wrunning cpu ξ -∗
        wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu)) -∗
      wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu) := by
  intro h1 h2 h3 h4 h5
  iintro Hm Ha1 Ha2 Ha3 #Hi Hrun Hcont
  icases wrunningOpen (GF := GF) cpu ξ $$ Hrun with ⟨%ws, Hws, Hauth⟩
  ihave HF := WeakLeafO.holdTrue (GF := GF) ws
  iapply wwpJal gen cpu pc rd imm rdv0 c q ws (iprop(⌜True⌝) : VProp GF) h1 h2 h3 h4 h5
    $$ Hm Ha1 Ha2 Ha3 Hi Hws HF
  iintro %ws' %hle Hc1 Hc2 Hc3 Hc4 Hws -
  iapply WeakLeafO.wwpBupd
  imod ctxRunUpdate (GF := GF) cpu ξ ws ws' hle $$ Hauth with Hauth
  ihave Hrun := WeakLeafO.closeRun (GF := GF) cpu ξ ws' $$ Hws Hauth
  imodintro
  iapply Hcont $$ Hc1 Hc2 Hc3 Hc4 Hrun

/-- Rocq `wwp_jal_run`. -/
theorem wwpJalRun (gen : Nat) (cpu : CPU) (ξ : CtxId) (pc : BitVec 64) (rd : BitVec 5)
    (imm : BitVec 21) (rdv0 : BitVec 64) (c : MConf) (q : Qp) :
    gen = 0 →
    MConf.mok c →
    pmpAllowsAll c.pmpcfg →
    rd.toNat ≠ 0 →
    is_aligned_paddr (.Physaddr (pc + sign_extend (m := 64) imm)) 4 = true →
    whartRun (GF := GF) cpu ξ q c ⊢
      clockCells cpu -∗
      pcIs cpu pc -∗
      gpr cpu rd (DFrac.own 1) rdv0 -∗
      winstrM (GF := GF) pc false (.JAL (imm, .Regidx rd)) -∗
      (whartRun cpu ξ q c -∗
        clockCells cpu -∗
        pcIs cpu (pc + sign_extend (m := 64) imm) -∗
        gpr cpu rd (DFrac.own 1) (BitVec.addInt pc 4) -∗
        wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu)) -∗
      wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu) := by
  intro h1 h2 h3 h4 h5
  iintro Hrun Ha1 Ha2 Ha3 #Hi Hcont
  icases whartRunOpen (GF := GF) cpu ξ q c $$ Hrun with ⟨Hm, Hview⟩
  iapply wwpJalO gen cpu ξ pc rd imm rdv0 c q h1 h2 h3 h4 h5
    $$ Hm Ha1 Ha2 Ha3 Hi Hview
  iintro Hc1 Hc2 Hc3 Hc4 Hview
  iapply Hcont $$ [Hc1 Hview] Hc2 Hc3 Hc4
  iapply whartRunClose (GF := GF) cpu ξ _ _ $$ Hc1 Hview

/-- Rocq `wwp_cjr_rvc_o`. -/
theorem wwpCjrRvcO (gen : Nat) (cpu : CPU) (ξ : CtxId) (pc : BitVec 64) (ra : BitVec 5)
    (rav : BitVec 64) (c : MConf) (q : Qp) :
    gen = 0 →
    MConf.mok c →
    pmpAllowsAll c.pmpcfg →
    ra.toNat ≠ 0 →
    mConf (GF := GF) cpu (DFrac.own q) c ⊢
      clockCells cpu -∗
      pcIs cpu pc -∗
      gpr cpu ra (DFrac.own 1) rav -∗
      winstrM (GF := GF) pc true (.JALR (zeros (n := 12), .Regidx ra, zreg)) -∗
      wrunning (GF := GF) cpu ξ -∗
      (mConf cpu (DFrac.own q) c -∗
        clockCells cpu -∗
        pcIs cpu (WeakLeafMret.retPc rav) -∗
        gpr cpu ra (DFrac.own 1) rav -∗
        wrunning cpu ξ -∗
        wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu)) -∗
      wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu) := by
  intro h1 h2 h3 h4
  iintro Hm Ha1 Ha2 Ha3 #Hi Hrun Hcont
  icases wrunningOpen (GF := GF) cpu ξ $$ Hrun with ⟨%ws, Hws, Hauth⟩
  ihave HF := WeakLeafO.holdTrue (GF := GF) ws
  iapply wwpCjrRvc gen cpu pc ra rav c q ws (iprop(⌜True⌝) : VProp GF) h1 h2 h3 h4
    $$ Hm Ha1 Ha2 Ha3 Hi Hws HF
  iintro %ws' %hle Hc1 Hc2 Hc3 Hc4 Hws -
  iapply WeakLeafO.wwpBupd
  imod ctxRunUpdate (GF := GF) cpu ξ ws ws' hle $$ Hauth with Hauth
  ihave Hrun := WeakLeafO.closeRun (GF := GF) cpu ξ ws' $$ Hws Hauth
  imodintro
  iapply Hcont $$ Hc1 Hc2 Hc3 Hc4 Hrun

/-- Rocq `wwp_cjr_rvc_run`. -/
theorem wwpCjrRvcRun (gen : Nat) (cpu : CPU) (ξ : CtxId) (pc : BitVec 64) (ra : BitVec 5)
    (rav : BitVec 64) (c : MConf) (q : Qp) :
    gen = 0 →
    MConf.mok c →
    pmpAllowsAll c.pmpcfg →
    ra.toNat ≠ 0 →
    whartRun (GF := GF) cpu ξ q c ⊢
      clockCells cpu -∗
      pcIs cpu pc -∗
      gpr cpu ra (DFrac.own 1) rav -∗
      winstrM (GF := GF) pc true (.JALR (zeros (n := 12), .Regidx ra, zreg)) -∗
      (whartRun cpu ξ q c -∗
        clockCells cpu -∗
        pcIs cpu (WeakLeafMret.retPc rav) -∗
        gpr cpu ra (DFrac.own 1) rav -∗
        wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu)) -∗
      wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu) := by
  intro h1 h2 h3 h4
  iintro Hrun Ha1 Ha2 Ha3 #Hi Hcont
  icases whartRunOpen (GF := GF) cpu ξ q c $$ Hrun with ⟨Hm, Hview⟩
  iapply wwpCjrRvcO gen cpu ξ pc ra rav c q h1 h2 h3 h4
    $$ Hm Ha1 Ha2 Ha3 Hi Hview
  iintro Hc1 Hc2 Hc3 Hc4 Hview
  iapply Hcont $$ [Hc1 Hview] Hc2 Hc3 Hc4
  iapply whartRunClose (GF := GF) cpu ξ _ _ $$ Hc1 Hview

/-- Rocq `wwp_mret_o`. -/
theorem wwpMretO (gen : Nat) (cpu : CPU) (ξ : CtxId) (pc : BitVec 64) (newpriv : Privilege)
    (ms_cur mepc0 menvcfg1 : BitVec 64) (pmpcfg0 : RegisterType .pmpcfg_n) :
    gen = 0 →
    pmpAllowsAll pmpcfg0 →
    (_get_Mstatus_MIE ms_cur == 1#1) = false →
    (_get_Mstatus_MPRV ms_cur == 1#1) = false →
    privLevel_bits_forwards (_get_Mstatus_MPP (WeakLeafMret.cms2 ms_cur), 0#1) = pure newpriv →
    newpriv = .Supervisor →
    _get_MEnvcfg_LPE menvcfg1 = 0#1 →
    hwConfig (GF := GF) cpu ⊢
      clockCells cpu -∗
      Register.hart_state ↦ᵣ[cpu] HartState.HART_ACTIVE () -∗
      Register.cur_privilege ↦ᵣ[cpu] Privilege.Machine -∗
      Register.mstatus ↦ᵣ[cpu] ms_cur -∗
      Register.pmpcfg_n ↦ᵣ[cpu] pmpcfg0 -∗
      pcIs cpu pc -∗
      Register.menvcfg ↦ᵣ[cpu] menvcfg1 -∗
      Register.mepc ↦ᵣ[cpu] mepc0 -∗
      winstrM (GF := GF) pc false (.MRET ()) -∗
      wrunning (GF := GF) cpu ξ -∗
      (Register.hart_state ↦ᵣ[cpu] HartState.HART_ACTIVE () -∗
        clockCells cpu -∗
        Register.cur_privilege ↦ᵣ[cpu] newpriv -∗
        Register.mstatus ↦ᵣ[cpu] WeakLeafMret.cms5 ms_cur -∗
        Register.pmpcfg_n ↦ᵣ[cpu] pmpcfg0 -∗
        Register.menvcfg ↦ᵣ[cpu] menvcfg1 -∗
        Register.mepc ↦ᵣ[cpu] mepc0 -∗
        pcIs cpu (WeakLeafMret.retPc mepc0) -∗
        wrunning cpu ξ -∗
        wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu)) -∗
      wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu) := by
  intro h1 h2 h3 h4 h5 h6 h7
  iintro Hm Ha1 Ha2 Ha3 Ha4 Ha5 Ha6 Ha7 Ha8 #Hi Hrun Hcont
  icases wrunningOpen (GF := GF) cpu ξ $$ Hrun with ⟨%ws, Hws, Hauth⟩
  ihave HF := WeakLeafO.holdTrue (GF := GF) ws
  iapply wwpMret gen cpu pc newpriv ms_cur mepc0 menvcfg1 pmpcfg0 ws (iprop(⌜True⌝) : VProp GF) h1
    h2 h3 h4 h5 h6 h7
    $$ Hm Ha1 Ha2 Ha3 Ha4 Ha5 Ha6 Ha7 Ha8 Hi Hws HF
  iintro %ws' %hle Hc1 Hc2 Hc3 Hc4 Hc5 Hc6 Hc7 Hc8 Hws -
  iapply WeakLeafO.wwpBupd
  imod ctxRunUpdate (GF := GF) cpu ξ ws ws' hle $$ Hauth with Hauth
  ihave Hrun := WeakLeafO.closeRun (GF := GF) cpu ξ ws' $$ Hws Hauth
  imodintro
  iapply Hcont $$ Hc1 Hc2 Hc3 Hc4 Hc5 Hc6 Hc7 Hc8 Hrun

end leafo

end Weak
