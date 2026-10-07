/-
Weak: **the SC-shaped leaf interface for the M-mode tier** (M4 packaging layer) --
`winstrM pc is_rvc i`, the weak twin of `InstrBytes.instr`, and one wrapper per
M-mode leaf that consumes it.

Rocq: `iris/WeakLeafM.v` @ xxvzwolszwmp.

The Rocq header, in substance.  The batch-2 leaves take `winstrBytes` plus four
to six loose decode/alignment premises; the SC side packages "the text at `pc`
decodes to `i`" into one persistent token.  This file is that missing packaging
layer: `winstrM pc is_rvc i` is `winstr` PLUS the reference-state decode facts
the certificate half needs (`wdecRef`).  Every call site in `WkTimerinit` /
`WkStartNew` uses the SAME bridge instance (`WkEntryEff.dM` / `dNone` /
`WkEntryEff.dstateM`), so those are fixed here and `agreeMRegs` / `dMMi` leave
the interface.  The 4-alignment premise disappears: a wrapper instantiates the
leaf's `al4` at `is_aligned_vaddr (.Virtaddr pc) 4` itself and passes `rfl`.
RESULT: a wrapper's statement is its SC twin's, plus `hartWs cpu ws` and a
`vwpHold F ws` frame carried to a `wsLe`-bound `ws'` (`vwpHold_mono`).
§1 the two decode shapes; §2 the token; §3 its introduction; §4 the two
eliminators; §5-§6 the register-only ALU family; §7 csrr; §8 csrw; §9 control
flow; §10 mret; §11 the TOR load/store; §12 the `start()` families.

**Deviations from Rocq.**
1. VOCABULARY: the tree's leaf conventions (`Weak/WeakLeafItype.lean` deviation
   1): `mword n` ↦ `BitVec n`, `uint x <> 0` ↦ `x.toNat ≠ 0`, `add_vec_int` ↦
   `BitVec.addInt`, `regval_into_reg v` ↦ `v`, `pc_is` ↦ `pcIs cpu`, `hart_ws
   cpu_id` ↦ `hartWs cpu`, `vwp_hold` ↦ `vwpHold`, `ws_le` ↦ `wsLe`, `WWP Loop`
   ↦ `wwpTriv ⊤ (WExpr.loop gen cpu)`, `GenId`/`CpuId` ↦ explicit `gen`/`cpu`,
   `R_bitvector_64 (gpr_of_Z (uint r)) ↦ᵣ v` ↦ `gpr cpu r (DFrac.own 1) v`,
   `gpr_file m` ↦ `MachCSL.gprFile cpu m` (`m !!! Regidx r` ↦ `m.get r`,
   `<[Regidx rd := v]> m` ↦ `m.set rd v`); the CSR numbers are literals (as the
   leaves); `D_m`/`D_none`/`dstateM` ↦ `WkEntryEff.dM`/`dNone`/`WkEntryEff.dstateM`.
2. THE CONFIG INTERFACE (owner decision Q3, `Weak/WeakFunnel.lean` deviation 7):
   Rocq `mmode_config (DfracOwn q) -∗ pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0` ↦
   `mConf cpu (DFrac.own q) c ∗ clockCells cpu`, `pmp_allows_all pmpcfg0` ↦
   `pmpAllowsAll c.pmpcfg`, plus the premise `MConf.mok c`.  CSRs bundled in
   `mConf` take NO separate cell (`Weak/WeakLeafCsrrM.lean`): the csrr wrappers
   for menvcfg/mcounteren/sie drop Rocq's CSR cell(s) and value binders and read
   `c.menvcfg` / `c.mcounteren` / `lower_mie c.mie c.mideleg`; the TOR wrappers'
   `pmpaddr_n ↦ᵣ{q} pmpaddrs` is `c.pmpaddr` (`pmpTor0Grants c.pmpcfg c.pmpaddr`).
3. CSR-IN-mConf WRITES at the FULL fraction (orchestrator full-fraction check,
   2026-10-06; Rocq's top level instantiates `mmode_config (DfracOwn 1)`): the
   csrw wrappers for menvcfg, mcounteren, stimecmp, mepc, satp, medeleg,
   mideleg, sie and pmpaddr0 are stated at `mConf cpu (DFrac.own 1) c` (Rocq:
   any `q`), and the written CSR comes back inside the config
   (`{ c with menvcfg := WeakLeafCsrw2.menvcfgLegalized c.menvcfg rs1v }`, …)
   instead of as a separate cell.  `wwpCsrwSatp` carries its leaf's extra
   premise `_get_Mstatus_SXL c.mstatus = 2#2` (`Weak/WeakLeafCsrw3.lean`).
   Every other wrapper keeps `q` generic.
4. `minstret_inv` ↦ `clockCells cpu` in the cell-based wrappers (mret, csrr /
   csrw mstatus, csrw pmpcfg0), as their leaves (Q3, no MinstretInv); the
   resource order of those wrappers is their leaves'.
5. `winstrMOfText`: the RAM premise is `inRam pc 4` and the fetch-word match is
   `fetchWordOk r w`, as `WeakFunnel.winstrBytesOfText`; the byte lookup is
   `get? bs (pc + BitVec.ofNat 64 j) = some (nthByte (n := 4) w j)`.
6. `ld8`/`sd8` RAM premises: `(∀ j < 8, addr_is_ram (pa_add ea j))` ↦
   `inRam ea 8`, as the leaves.
7. Lean-only helpers (file-qualified): `WeakLeafM.wdecAllBase` /
   `WeakLeafM.wdecAllRvc` turn `wdecAll` at a known constructor into the leaf's
   decode premise (Rocq does it by conversion).

**Rocq → Lean name map.**  `wdec_all` `wdecAll`, `wdec_ref` `wdecRef`,
`winstr_m` `winstrM`, `winstr_m_persistent` `winstrM_persistent`,
`winstr_bytes_aligned2` `winstrBytesAligned2`, `winstr_m_winstr`
`winstrMWinstr`, `winstr_m_of_text` `winstrMOfText`, `winstr_m_rvc`
`winstrMRvc`, `winstr_m_base` `winstrMBase`, and `wwp_<x>` ↦ `wwp<X>` for
`lui addi or_rvc add_rvc slli_rvc addiw_rvc ori csrr_menvcfg csrr_mcounteren
csrr_mhartid csrr_time csrw_menvcfg csrw_mcounteren csrw_stimecmp jal cjr_rvc
mret ld8_tor_rvc ld8_tor_rvc_own sd8_tor_rvc and_rvc srli_rvc auipc sd8_off_rvc
csrr_sie csrw_mepc csrw_satp csrw_medeleg csrw_mideleg csrw_sie csrw_pmpaddr0
csrr_mstatus csrw_mstatus csrw_pmpcfg0` (`wwpOrRvc`, `wwpLd8TorRvcOwn`,
`wwpCsrwPmpaddr0`, …).  None is in the duplicated-name table.

**Dropped:** nothing (Rocq 43 declarations; Lean 43 + 2 Lean-only).
-/
import Weak.WeakLeafUtypeShift
import Weak.WeakLeafItype
import Weak.WeakLeafRtypeW
import Weak.WeakLeafCsrrM
import Weak.WeakLeafCsrrTime
import Weak.WeakLeafCsrw
import Weak.WeakLeafCsrw2
import Weak.WeakLeafCsrw3
import Weak.WeakLeafStimecmp
import Weak.WeakLeafPmpcfg0
import Weak.WeakLeafSdspOff
import Weak.WeakLeafJump
import Weak.WeakLeafMret
import Weak.WeakLeafTor

namespace Weak

open Iris Iris.BI Iris.BI.MonPred Iris.ProofMode Iris.Std
open MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D LeanRV64D.Functions

/-! ## 1. The two decode shapes, as plain `Prop`s over a `FetchResult` -/

/-- Rocq `wdec_all`: verbatim `winstr`'s own decode field (the ∀-state shape). -/
def wdecAll (r : FetchResult) (i : instruction) : Prop :=
  ∀ t : ExecSt,
    privMSU (t.regs .cur_privilege) = true →
    (_get_Misa_C (t.regs .misa) == 1#1) = true →
    (_get_Misa_A (t.regs .misa) == 1#1) = true →
    t.regs .misa = misaC →
    cfgOk t →
    if fetchIsRvc r then
      ∃ i0 : instruction,
        exec (decodeFetch r) t = some (i0, t) ∧
        is_lpad_instruction i0 = false ∧
        (∀ s : ExecSt, exec (execute i0) s = some (.ExecuteAs i, s))
    else exec (decodeFetch r) t = some (i, t)

/-- Rocq `wdec_ref`: the reference-state shape at the FIXED bridge instance. -/
def wdecRef (r : FetchResult) (i : instruction) : Prop :=
  goodb0 WkEntryEff.dM (decodeFetch r) WkEntryEff.dstateM = true ∧
  match r with
  | .F_Base _ => exec (decodeFetch r) WkEntryEff.dstateM = some (i, WkEntryEff.dstateM)
  | .F_RVC _ =>
      ∃ i0 : instruction,
        exec (decodeFetch r) WkEntryEff.dstateM = some (i0, WkEntryEff.dstateM) ∧
        is_lpad_instruction i0 = false ∧
        (∀ s : ExecSt, goodb0 dNone (execute i0) s = true) ∧
        (∀ s : ExecSt, exec (execute i0) s = some (.ExecuteAs i, s))
  | _ => False

/-- Lean-only (deviation 7): `wdecAll` at an `F_Base` fetch is the leaves' decode premise. -/
theorem WeakLeafM.wdecAllBase {w : BitVec 32} {i : instruction} (H : wdecAll (.F_Base w) i) :
    ∀ t : ExecSt,
      privMSU (t.regs .cur_privilege) = true →
      (_get_Misa_C (t.regs .misa) == 1#1) = true →
      (_get_Misa_A (t.regs .misa) == 1#1) = true →
      t.regs .misa = misaC →
      cfgOk t →
      exec (decodeFetch (.F_Base w)) t = some (i, t) := by
  intro t a b c d e
  have H' := H t a b c d e
  simp only [fetchIsRvc, Bool.false_eq_true, ↓reduceIte] at H'
  exact H'

/-- Lean-only (deviation 7): `wdecAll` at an `F_RVC` fetch is the leaves' decode premise. -/
theorem WeakLeafM.wdecAllRvc {h : BitVec 16} {i : instruction} (H : wdecAll (.F_RVC h) i) :
    ∀ t : ExecSt,
      privMSU (t.regs .cur_privilege) = true →
      (_get_Misa_C (t.regs .misa) == 1#1) = true →
      (_get_Misa_A (t.regs .misa) == 1#1) = true →
      t.regs .misa = misaC →
      cfgOk t →
      ∃ i0 : instruction,
        exec (decodeFetch (.F_RVC h)) t = some (i0, t) ∧
        is_lpad_instruction i0 = false ∧
        (∀ s : ExecSt, exec (execute i0) s = some (.ExecuteAs i, s)) := by
  intro t a b c d e
  have H' := H t a b c d e
  simp only [fetchIsRvc, ↓reduceIte] at H'
  exact H'

/-! ## 2. The token: `InstrBytes.instr`'s weak twin, at leaf altitude -/

section token
variable {GF : BundledGFunctors} [WeakGS GF]

/-- Rocq `winstr_m`. -/
def winstrM (pc : BitVec 64) (is_rvc : Bool) (i : instruction) : IProp GF :=
  iprop(⌜is_lpad_instruction i = false⌝ ∗
    ∃ r : FetchResult, ⌜fetchIsRvc r = is_rvc⌝ ∗ winstrBytes (GF := GF) pc r ∗
      ⌜wdecAll r i⌝ ∗ ⌜wdecRef r i⌝)

/-- Rocq `winstr_m_persistent`. -/
instance winstrM_persistent (pc : BitVec 64) (is_rvc : Bool) (i : instruction) :
    Persistent (winstrM (GF := GF) pc is_rvc i) := by
  unfold winstrM; infer_instance

/-- Rocq `winstr_bytes_aligned2`: the 2-alignment projection of `winstrBytes`. -/
theorem winstrBytesAligned2 (pc : BitVec 64) (r : FetchResult) :
    winstrBytes (GF := GF) pc r ⊢ ⌜is_aligned_vaddr (.Virtaddr pc) 2 = true⌝ := by
  unfold winstrBytes
  iintro ⟨%h, -⟩
  ipureintro; exact h

/-- Rocq `winstr_m_winstr`: it IS a `winstr`. -/
theorem winstrMWinstr (pc : BitVec 64) (is_rvc : Bool) (i : instruction) :
    winstrM (GF := GF) pc is_rvc i ⊢ winstr (GF := GF) pc is_rvc i := by
  unfold winstrM
  iintro ⟨%hlpad, %r, %hrvc, #Hb, %hall, -⟩
  iapply winstrIntro (GF := GF) pc is_rvc i r hlpad hrvc hall
  iexact Hb

/-! ## 3. The introduction a decode file uses -- one per instruction -/

/-- Rocq `winstr_m_of_text` (deviation 5). -/
theorem winstrMOfText (bs : GMapF PAddr (BitVec 8)) (pc : BitVec 64) (r : FetchResult)
    (w : BitVec 32) (i : instruction) :
    is_aligned_vaddr (.Virtaddr pc) 2 = true →
    accWf pc 4 →
    inRam pc 4 →
    fetchWordOk r w →
    is_lpad_instruction i = false →
    wdecAll r i →
    wdecRef r i →
    wkernelText (GF := GF) bs ⊢
      ⌜∀ j : Nat, j < 4 → get? bs (pc + BitVec.ofNat 64 j) = some (nthByte (n := 4) w j)⌝ -∗
        winstrM (GF := GF) pc (fetchIsRvc r) i := by
  intro h2 hacc hram hr hlpad hall href
  iintro #Ht %hlk
  ihave #Hb := winstrBytesOfText (GF := GF) bs pc r w h2 hacc hram hr $$ Ht %hlk
  unfold winstrM
  isplitr
  · ipureintro; exact hlpad
  iexists r
  isplitr
  · ipureintro; rfl
  isplitr
  · iexact Hb
  isplitr
  · ipureintro; exact hall
  ipureintro; exact href

/-! ## 4. The eliminators a wrapper uses -/

/-- Rocq `winstr_m_rvc`. -/
theorem winstrMRvc (pc : BitVec 64) (i : instruction) :
    winstrM (GF := GF) pc true i ⊢
      ∃ (h : BitVec 16) (i0 : instruction),
        ⌜is_lpad_instruction i = false⌝ ∗
        winstrBytes (GF := GF) pc (.F_RVC h) ∗
        ⌜is_aligned_vaddr (.Virtaddr pc) 2 = true⌝ ∗
        ⌜wdecAll (.F_RVC h) i⌝ ∗
        ⌜goodb0 WkEntryEff.dM (ext_decode_compressed h) WkEntryEff.dstateM = true⌝ ∗
        ⌜exec (ext_decode_compressed h) WkEntryEff.dstateM = some (i0, WkEntryEff.dstateM)⌝ ∗
        ⌜is_lpad_instruction i0 = false⌝ ∗
        ⌜∀ s : ExecSt, goodb0 dNone (execute i0) s = true⌝ ∗
        ⌜∀ s : ExecSt, exec (execute i0) s = some (.ExecuteAs i, s)⌝ := by
  unfold winstrM
  iintro ⟨%hlpad, %r, %hrvc, #Hb, %hall, %href⟩
  cases r with
  | F_RVC h =>
    ihave %hal2 := winstrBytesAligned2 (GF := GF) pc _ $$ Hb
    obtain ⟨hgood, i0, hdec, hlp0, hg0, hexp⟩ := href
    iexists h
    iexists i0
    isplitr
    · ipureintro; exact hlpad
    isplitr
    · iexact Hb
    isplitr
    · ipureintro; exact hal2
    isplitr
    · ipureintro; exact hall
    isplitr
    · ipureintro; exact hgood
    isplitr
    · ipureintro; exact hdec
    isplitr
    · ipureintro; exact hlp0
    isplitr
    · ipureintro; exact hg0
    ipureintro; exact hexp
  | F_Base w => simp [fetchIsRvc] at hrvc
  | F_Ext_Error e => simp [fetchIsRvc] at hrvc
  | F_Error e => simp [fetchIsRvc] at hrvc

/-- Rocq `winstr_m_base`. -/
theorem winstrMBase (pc : BitVec 64) (i : instruction) :
    winstrM (GF := GF) pc false i ⊢
      ∃ w : BitVec 32,
        winstrBytes (GF := GF) pc (.F_Base w) ∗
        ⌜is_aligned_vaddr (.Virtaddr pc) 2 = true⌝ ∗
        ⌜wdecAll (.F_Base w) i⌝ ∗
        ⌜goodb0 WkEntryEff.dM (ext_decode w) WkEntryEff.dstateM = true⌝ ∗
        ⌜exec (ext_decode w) WkEntryEff.dstateM = some (i, WkEntryEff.dstateM)⌝ := by
  unfold winstrM
  iintro ⟨%hlpad, %r, %hrvc, #Hb, %hall, %href⟩
  cases r with
  | F_Base w =>
    ihave %hal2 := winstrBytesAligned2 (GF := GF) pc _ $$ Hb
    obtain ⟨hgood, hdec⟩ := href
    iexists w
    isplitr
    · iexact Hb
    isplitr
    · ipureintro; exact hal2
    isplitr
    · ipureintro; exact hall
    isplitr
    · ipureintro; exact hgood
    ipureintro; exact hdec
  | F_RVC h => simp [fetchIsRvc] at hrvc
  | F_Ext_Error e => exact href.2.elim
  | F_Error e => exact href.2.elim

end token

section wrappers
variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [WeakGS GF]

/-! ## 5. The worked wrappers: `lui` and `addi`, is_rvc-generic -/

/-- Rocq `wwp_lui`. -/
theorem wwpLui (gen : Nat) (cpu : CPU) (pc : BitVec 64) (is_rvc : Bool) (rd : BitVec 5)
    (imm : BitVec 20) (m : RegMap) (c : MConf) (q : Qp) (ws : Wstate) (F : VProp GF) :
    gen = 0 →
    MConf.mok c →
    pmpAllowsAll c.pmpcfg →
    rd.toNat ≠ 0 →
    mConf (GF := GF) cpu (DFrac.own q) c ⊢
      clockCells cpu -∗
      pcIs cpu pc -∗
      gprFile cpu m -∗
      winstrM (GF := GF) pc is_rvc (.UTYPE (imm, .Regidx rd, .LUI)) -∗
      hartWs (GF := GF) cpu ws -∗
      vwpHold F ws -∗
      (∀ ws' : Wstate,
        ⌜wsLe ws ws'⌝ -∗
        mConf cpu (DFrac.own q) c -∗
        clockCells cpu -∗
        pcIs cpu (BitVec.addInt pc (if is_rvc then 2 else 4)) -∗
        gprFile cpu (m.set rd (WkEntryEff.luival imm)) -∗
        hartWs cpu ws' -∗
        vwpHold F ws' -∗
        wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu)) -∗
      wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu) := by
  intro hgen hmok hpmp hnz
  iintro Hm Hclk Hpc Hfile #Hi Hhws HF Hcont
  icases WkEntryNew.pcIsSplit (GF := GF) cpu pc $$ Hpc with ⟨Hpc, Hnpc⟩
  cases is_rvc with
  | true =>
    simp only [↓reduceIte]
    icases winstrMRvc (GF := GF) pc _ $$ Hi with
      ⟨%h, %i0, -, #Hb, %hal2, %hall, %hgood, %hdec, %hlp0, %hg0, %hexp⟩
    iapply wwpLuiRvcLeaf gen cpu (is_aligned_vaddr (.Virtaddr pc) 4) pc h rd imm i0 m pc c q
      WkEntryEff.dM dNone WkEntryEff.dstateM ws hgen hmok hpmp hal2 rfl hnz
      (WeakLeafM.wdecAllRvc hall) (fun rs hp hmi hs => agreeMRegs rs hp hs hmi) dMMi hgood hdec
      hg0 hexp
      $$ Hm Hclk Hpc Hnpc Hfile Hb Hhws
    iintro %ws' %hle Hm Hclk Hpc Hfile Hhws
    ihave HF := vwpHold_mono F hle $$ HF
    iapply Hcont $$ %ws' %hle Hm Hclk Hpc Hfile Hhws HF
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    icases winstrMBase (GF := GF) pc _ $$ Hi with ⟨%w, #Hb, %hal2, %hall, %hgood, %hdec⟩
    iapply wwpLuiLeaf gen cpu (is_aligned_vaddr (.Virtaddr pc) 4) pc w rd imm m pc c q
      WkEntryEff.dM WkEntryEff.dstateM ws hgen hmok hpmp hal2 rfl hnz
      (WeakLeafM.wdecAllBase hall) (fun rs hp hmi hs => agreeMRegs rs hp hs hmi) dMMi hgood hdec
      $$ Hm Hclk Hpc Hnpc Hfile Hb Hhws
    iintro %ws' %hle Hm Hclk Hpc Hfile Hhws
    ihave HF := vwpHold_mono F hle $$ HF
    iapply Hcont $$ %ws' %hle Hm Hclk Hpc Hfile Hhws HF

/-- Rocq `wwp_addi`. -/
theorem wwpAddi (gen : Nat) (cpu : CPU) (pc : BitVec 64) (is_rvc : Bool) (rs1 rd : BitVec 5)
    (imm : BitVec 12) (m : RegMap) (c : MConf) (q : Qp) (ws : Wstate) (F : VProp GF) :
    gen = 0 →
    MConf.mok c →
    pmpAllowsAll c.pmpcfg →
    rd.toNat ≠ 0 →
    mConf (GF := GF) cpu (DFrac.own q) c ⊢
      clockCells cpu -∗
      pcIs cpu pc -∗
      gprFile cpu m -∗
      winstrM (GF := GF) pc is_rvc (.ITYPE (imm, .Regidx rs1, .Regidx rd, .ADDI)) -∗
      hartWs (GF := GF) cpu ws -∗
      vwpHold F ws -∗
      (∀ ws' : Wstate,
        ⌜wsLe ws ws'⌝ -∗
        mConf cpu (DFrac.own q) c -∗
        clockCells cpu -∗
        pcIs cpu (BitVec.addInt pc (if is_rvc then 2 else 4)) -∗
        gprFile cpu (m.set rd (m.get rs1 + sign_extend (m := 64) imm)) -∗
        hartWs cpu ws' -∗
        vwpHold F ws' -∗
        wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu)) -∗
      wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu) := by
  intro hgen hmok hpmp hnz
  iintro Hm Hclk Hpc Hfile #Hi Hhws HF Hcont
  icases WkEntryNew.pcIsSplit (GF := GF) cpu pc $$ Hpc with ⟨Hpc, Hnpc⟩
  cases is_rvc with
  | true =>
    simp only [↓reduceIte]
    icases winstrMRvc (GF := GF) pc _ $$ Hi with
      ⟨%h, %i0, -, #Hb, %hal2, %hall, %hgood, %hdec, %hlp0, %hg0, %hexp⟩
    iapply wwpAddiRvcLeaf gen cpu (is_aligned_vaddr (.Virtaddr pc) 4) pc h rs1 rd imm i0 m pc c q
      WkEntryEff.dM dNone WkEntryEff.dstateM ws hgen hmok hpmp hal2 rfl hnz
      (WeakLeafM.wdecAllRvc hall) (fun rs hp hmi hs => agreeMRegs rs hp hs hmi) dMMi hgood hdec
      hg0 hexp
      $$ Hm Hclk Hpc Hnpc Hfile Hb Hhws
    iintro %ws' %hle Hm Hclk Hpc Hfile Hhws
    ihave HF := vwpHold_mono F hle $$ HF
    iapply Hcont $$ %ws' %hle Hm Hclk Hpc Hfile Hhws HF
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    icases winstrMBase (GF := GF) pc _ $$ Hi with ⟨%w, #Hb, %hal2, %hall, %hgood, %hdec⟩
    iapply wwpAddiLeaf gen cpu (is_aligned_vaddr (.Virtaddr pc) 4) pc w rs1 rd imm m pc c q
      WkEntryEff.dM WkEntryEff.dstateM ws hgen hmok hpmp hal2 rfl hnz
      (WeakLeafM.wdecAllBase hall) (fun rs hp hmi hs => agreeMRegs rs hp hs hmi) dMMi hgood hdec
      $$ Hm Hclk Hpc Hnpc Hfile Hb Hhws
    iintro %ws' %hle Hm Hclk Hpc Hfile Hhws
    ihave HF := vwpHold_mono F hle $$ HF
    iapply Hcont $$ %ws' %hle Hm Hclk Hpc Hfile Hhws HF

/-! ## 6. The rest of the register-only ALU family (one encoding each, as their leaves) -/

/-- Rocq `wwp_or_rvc`. -/
theorem wwpOrRvc (gen : Nat) (cpu : CPU) (pc : BitVec 64) (rs2 rs1 rd : BitVec 5) (m : RegMap)
    (c : MConf) (q : Qp) (ws : Wstate) (F : VProp GF) :
    gen = 0 →
    MConf.mok c →
    pmpAllowsAll c.pmpcfg →
    rd.toNat ≠ 0 →
    mConf (GF := GF) cpu (DFrac.own q) c ⊢
      clockCells cpu -∗
      pcIs cpu pc -∗
      gprFile cpu m -∗
      winstrM (GF := GF) pc true (.RTYPE (.Regidx rs2, .Regidx rs1, .Regidx rd, .OR)) -∗
      hartWs (GF := GF) cpu ws -∗
      vwpHold F ws -∗
      (∀ ws' : Wstate,
        ⌜wsLe ws ws'⌝ -∗
        mConf cpu (DFrac.own q) c -∗
        clockCells cpu -∗
        pcIs cpu (BitVec.addInt pc 2) -∗
        gprFile cpu (m.set rd (m.get rs1 ||| m.get rs2)) -∗
        hartWs cpu ws' -∗
        vwpHold F ws' -∗
        wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu)) -∗
      wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu) := by
  intro hgen hmok hpmp hnz
  iintro Hm Hclk Hpc Hfile #Hi Hhws HF Hcont
  icases WkEntryNew.pcIsSplit (GF := GF) cpu pc $$ Hpc with ⟨Hpc, Hnpc⟩
  icases winstrMRvc (GF := GF) pc _ $$ Hi with
    ⟨%h, %i0, -, #Hb, %hal2, %hall, %hgood, %hdec, %hlp0, %hg0, %hexp⟩
  iapply wwpOrRvcLeaf (is_aligned_vaddr (.Virtaddr pc) 4) gen cpu pc h rs2 rs1 rd i0 m pc q c
    WkEntryEff.dM dNone WkEntryEff.dstateM ws hgen hmok hpmp hal2 rfl hnz
    (WeakLeafM.wdecAllRvc hall) (fun rs hp hmi hs => agreeMRegs rs hp hs hmi) dMMi hgood hdec
    hg0 hexp
    $$ Hm Hclk Hpc Hnpc Hfile Hb Hhws
  iintro %ws' %hle Hm Hclk Hpc Hfile Hhws
  ihave HF := vwpHold_mono F hle $$ HF
  iapply Hcont $$ %ws' %hle Hm Hclk Hpc Hfile Hhws HF

/-- Rocq `wwp_add_rvc`. -/
theorem wwpAddRvc (gen : Nat) (cpu : CPU) (pc : BitVec 64) (rs2 rs1 rd : BitVec 5) (m : RegMap)
    (c : MConf) (q : Qp) (ws : Wstate) (F : VProp GF) :
    gen = 0 →
    MConf.mok c →
    pmpAllowsAll c.pmpcfg →
    rd.toNat ≠ 0 →
    mConf (GF := GF) cpu (DFrac.own q) c ⊢
      clockCells cpu -∗
      pcIs cpu pc -∗
      gprFile cpu m -∗
      winstrM (GF := GF) pc true (.RTYPE (.Regidx rs2, .Regidx rs1, .Regidx rd, .ADD)) -∗
      hartWs (GF := GF) cpu ws -∗
      vwpHold F ws -∗
      (∀ ws' : Wstate,
        ⌜wsLe ws ws'⌝ -∗
        mConf cpu (DFrac.own q) c -∗
        clockCells cpu -∗
        pcIs cpu (BitVec.addInt pc 2) -∗
        gprFile cpu (m.set rd (m.get rs1 + m.get rs2)) -∗
        hartWs cpu ws' -∗
        vwpHold F ws' -∗
        wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu)) -∗
      wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu) := by
  intro hgen hmok hpmp hnz
  iintro Hm Hclk Hpc Hfile #Hi Hhws HF Hcont
  icases WkEntryNew.pcIsSplit (GF := GF) cpu pc $$ Hpc with ⟨Hpc, Hnpc⟩
  icases winstrMRvc (GF := GF) pc _ $$ Hi with
    ⟨%h, %i0, -, #Hb, %hal2, %hall, %hgood, %hdec, %hlp0, %hg0, %hexp⟩
  iapply wwpAddRvcLeaf (is_aligned_vaddr (.Virtaddr pc) 4) gen cpu pc h rs2 rs1 rd i0 m pc q c
    WkEntryEff.dM dNone WkEntryEff.dstateM ws hgen hmok hpmp hal2 rfl hnz
    (WeakLeafM.wdecAllRvc hall) (fun rs hp hmi hs => agreeMRegs rs hp hs hmi) dMMi hgood hdec
    hg0 hexp
    $$ Hm Hclk Hpc Hnpc Hfile Hb Hhws
  iintro %ws' %hle Hm Hclk Hpc Hfile Hhws
  ihave HF := vwpHold_mono F hle $$ HF
  iapply Hcont $$ %ws' %hle Hm Hclk Hpc Hfile Hhws HF

/-- Rocq `wwp_slli_rvc`. -/
theorem wwpSlliRvc (gen : Nat) (cpu : CPU) (pc : BitVec 64) (rs1 rd : BitVec 5) (shamt : BitVec 6)
    (m : RegMap) (c : MConf) (q : Qp) (ws : Wstate) (F : VProp GF) :
    gen = 0 →
    MConf.mok c →
    pmpAllowsAll c.pmpcfg →
    rd.toNat ≠ 0 →
    mConf (GF := GF) cpu (DFrac.own q) c ⊢
      clockCells cpu -∗
      pcIs cpu pc -∗
      gprFile cpu m -∗
      winstrM (GF := GF) pc true (.SHIFTIOP (shamt, .Regidx rs1, .Regidx rd, .SLLI)) -∗
      hartWs (GF := GF) cpu ws -∗
      vwpHold F ws -∗
      (∀ ws' : Wstate,
        ⌜wsLe ws ws'⌝ -∗
        mConf cpu (DFrac.own q) c -∗
        clockCells cpu -∗
        pcIs cpu (BitVec.addInt pc 2) -∗
        gprFile cpu (m.set rd (shift_bits_left (m.get rs1)
          (Sail.BitVec.extractLsb shamt (Functions.log2_xlen -i 1) 0))) -∗
        hartWs cpu ws' -∗
        vwpHold F ws' -∗
        wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu)) -∗
      wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu) := by
  intro hgen hmok hpmp hnz
  iintro Hm Hclk Hpc Hfile #Hi Hhws HF Hcont
  icases WkEntryNew.pcIsSplit (GF := GF) cpu pc $$ Hpc with ⟨Hpc, Hnpc⟩
  icases winstrMRvc (GF := GF) pc _ $$ Hi with
    ⟨%h, %i0, -, #Hb, %hal2, %hall, %hgood, %hdec, %hlp0, %hg0, %hexp⟩
  iapply wwpSlliRvcLeaf gen cpu (is_aligned_vaddr (.Virtaddr pc) 4) pc h rs1 rd shamt i0 m pc c q
    WkEntryEff.dM dNone WkEntryEff.dstateM ws hgen hmok hpmp hal2 rfl hnz
    (WeakLeafM.wdecAllRvc hall) (fun rs hp hmi hs => agreeMRegs rs hp hs hmi) dMMi hgood hdec
    hg0 hexp
    $$ Hm Hclk Hpc Hnpc Hfile Hb Hhws
  iintro %ws' %hle Hm Hclk Hpc Hfile Hhws
  ihave HF := vwpHold_mono F hle $$ HF
  iapply Hcont $$ %ws' %hle Hm Hclk Hpc Hfile Hhws HF

/-- Rocq `wwp_addiw_rvc`. -/
theorem wwpAddiwRvc (gen : Nat) (cpu : CPU) (pc : BitVec 64) (rs1 rd : BitVec 5) (immv : BitVec 12)
    (m : RegMap) (c : MConf) (q : Qp) (ws : Wstate) (F : VProp GF) :
    gen = 0 →
    MConf.mok c →
    pmpAllowsAll c.pmpcfg →
    rd.toNat ≠ 0 →
    mConf (GF := GF) cpu (DFrac.own q) c ⊢
      clockCells cpu -∗
      pcIs cpu pc -∗
      gprFile cpu m -∗
      winstrM (GF := GF) pc true (.ADDIW (immv, .Regidx rs1, .Regidx rd)) -∗
      hartWs (GF := GF) cpu ws -∗
      vwpHold F ws -∗
      (∀ ws' : Wstate,
        ⌜wsLe ws ws'⌝ -∗
        mConf cpu (DFrac.own q) c -∗
        clockCells cpu -∗
        pcIs cpu (BitVec.addInt pc 2) -∗
        gprFile cpu (m.set rd (sign_extend (m := 64)
          (Sail.BitVec.extractLsb (m.get rs1 + sign_extend (m := 64) immv) 31 0))) -∗
        hartWs cpu ws' -∗
        vwpHold F ws' -∗
        wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu)) -∗
      wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu) := by
  intro hgen hmok hpmp hnz
  iintro Hm Hclk Hpc Hfile #Hi Hhws HF Hcont
  icases WkEntryNew.pcIsSplit (GF := GF) cpu pc $$ Hpc with ⟨Hpc, Hnpc⟩
  icases winstrMRvc (GF := GF) pc _ $$ Hi with
    ⟨%h, %i0, -, #Hb, %hal2, %hall, %hgood, %hdec, %hlp0, %hg0, %hexp⟩
  iapply wwpAddiwRvcLeaf (is_aligned_vaddr (.Virtaddr pc) 4) gen cpu pc h rs1 rd immv i0 m pc q c
    WkEntryEff.dM dNone WkEntryEff.dstateM ws hgen hmok hpmp hal2 rfl hnz
    (WeakLeafM.wdecAllRvc hall) (fun rs hp hmi hs => agreeMRegs rs hp hs hmi) dMMi hgood hdec
    hg0 hexp
    $$ Hm Hclk Hpc Hnpc Hfile Hb Hhws
  iintro %ws' %hle Hm Hclk Hpc Hfile Hhws
  ihave HF := vwpHold_mono F hle $$ HF
  iapply Hcont $$ %ws' %hle Hm Hclk Hpc Hfile Hhws HF

/-- Rocq `wwp_ori`. -/
theorem wwpOri (gen : Nat) (cpu : CPU) (pc : BitVec 64) (rs1 rd : BitVec 5) (imm : BitVec 12)
    (m : RegMap) (c : MConf) (q : Qp) (ws : Wstate) (F : VProp GF) :
    gen = 0 →
    MConf.mok c →
    pmpAllowsAll c.pmpcfg →
    rd.toNat ≠ 0 →
    mConf (GF := GF) cpu (DFrac.own q) c ⊢
      clockCells cpu -∗
      pcIs cpu pc -∗
      gprFile cpu m -∗
      winstrM (GF := GF) pc false (.ITYPE (imm, .Regidx rs1, .Regidx rd, .ORI)) -∗
      hartWs (GF := GF) cpu ws -∗
      vwpHold F ws -∗
      (∀ ws' : Wstate,
        ⌜wsLe ws ws'⌝ -∗
        mConf cpu (DFrac.own q) c -∗
        clockCells cpu -∗
        pcIs cpu (BitVec.addInt pc 4) -∗
        gprFile cpu (m.set rd (m.get rs1 ||| sign_extend (m := 64) imm)) -∗
        hartWs cpu ws' -∗
        vwpHold F ws' -∗
        wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu)) -∗
      wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu) := by
  intro hgen hmok hpmp hnz
  iintro Hm Hclk Hpc Hfile #Hi Hhws HF Hcont
  icases WkEntryNew.pcIsSplit (GF := GF) cpu pc $$ Hpc with ⟨Hpc, Hnpc⟩
  icases winstrMBase (GF := GF) pc _ $$ Hi with ⟨%w, #Hb, %hal2, %hall, %hgood, %hdec⟩
  iapply wwpOriLeaf gen cpu (is_aligned_vaddr (.Virtaddr pc) 4) pc w rs1 rd imm m pc c q
    WkEntryEff.dM WkEntryEff.dstateM ws hgen hmok hpmp hal2 rfl hnz
    (WeakLeafM.wdecAllBase hall) (fun rs hp hmi hs => agreeMRegs rs hp hs hmi) dMMi hgood hdec
    $$ Hm Hclk Hpc Hnpc Hfile Hb Hhws
  iintro %ws' %hle Hm Hclk Hpc Hfile Hhws
  ihave HF := vwpHold_mono F hle $$ HF
  iapply Hcont $$ %ws' %hle Hm Hclk Hpc Hfile Hhws HF

/-! ## 7. The CSR-read family (deviation 2: no separate cell for CSRs inside `mConf`) -/

/-- Rocq `wwp_csrr_menvcfg` (deviation 2). -/
theorem wwpCsrrMenvcfg (gen : Nat) (cpu : CPU) (pc : BitVec 64) (rd : BitVec 5) (rd0 : BitVec 64)
    (c : MConf) (q : Qp) (ws : Wstate) (F : VProp GF) :
    gen = 0 →
    MConf.mok c →
    pmpAllowsAll c.pmpcfg →
    rd.toNat ≠ 0 →
    mConf (GF := GF) cpu (DFrac.own q) c ⊢
      clockCells cpu -∗
      pcIs cpu pc -∗
      gpr cpu rd (DFrac.own 1) rd0 -∗
      winstrM (GF := GF) pc false (.CSRReg (0x30A#12, zreg, .Regidx rd, .CSRRS)) -∗
      hartWs (GF := GF) cpu ws -∗
      vwpHold F ws -∗
      (∀ ws' : Wstate,
        ⌜wsLe ws ws'⌝ -∗
        mConf cpu (DFrac.own q) c -∗
        clockCells cpu -∗
        pcIs cpu (BitVec.addInt pc 4) -∗
        gpr cpu rd (DFrac.own 1) c.menvcfg -∗
        hartWs cpu ws' -∗
        vwpHold F ws' -∗
        wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu)) -∗
      wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu) := by
  intro hgen hmok hpmp hnz
  iintro Hm Hclk Hpc Hrd #Hi Hhws HF Hcont
  icases WkEntryNew.pcIsSplit (GF := GF) cpu pc $$ Hpc with ⟨Hpc, Hnpc⟩
  icases winstrMBase (GF := GF) pc _ $$ Hi with ⟨%w, #Hb, %hal2, %hall, %hgood, %hdec⟩
  iapply wwpCsrrMenvcfgLeaf gen cpu (is_aligned_vaddr (.Virtaddr pc) 4) pc w rd rd0 pc c q
    WkEntryEff.dM WkEntryEff.dstateM ws hgen hmok hpmp hal2 rfl hnz
    (WeakLeafM.wdecAllBase hall) (fun rs hp hmi hs => agreeMRegs rs hp hs hmi) dMMi hgood hdec
    $$ Hm Hclk Hpc Hnpc Hrd Hb Hhws
  iintro %ws' %hle Hm Hclk Hpc Hrd Hhws
  ihave HF := vwpHold_mono F hle $$ HF
  iapply Hcont $$ %ws' %hle Hm Hclk Hpc Hrd Hhws HF

/-- Rocq `wwp_csrr_mcounteren` (deviation 2). -/
theorem wwpCsrrMcounteren (gen : Nat) (cpu : CPU) (pc : BitVec 64) (rd : BitVec 5)
    (rd0 : BitVec 64) (c : MConf) (q : Qp) (ws : Wstate) (F : VProp GF) :
    gen = 0 →
    MConf.mok c →
    pmpAllowsAll c.pmpcfg →
    rd.toNat ≠ 0 →
    mConf (GF := GF) cpu (DFrac.own q) c ⊢
      clockCells cpu -∗
      pcIs cpu pc -∗
      gpr cpu rd (DFrac.own 1) rd0 -∗
      winstrM (GF := GF) pc false (.CSRReg (0x306#12, zreg, .Regidx rd, .CSRRS)) -∗
      hartWs (GF := GF) cpu ws -∗
      vwpHold F ws -∗
      (∀ ws' : Wstate,
        ⌜wsLe ws ws'⌝ -∗
        mConf cpu (DFrac.own q) c -∗
        clockCells cpu -∗
        pcIs cpu (BitVec.addInt pc 4) -∗
        gpr cpu rd (DFrac.own 1) (zero_extend (m := 64) c.mcounteren) -∗
        hartWs cpu ws' -∗
        vwpHold F ws' -∗
        wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu)) -∗
      wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu) := by
  intro hgen hmok hpmp hnz
  iintro Hm Hclk Hpc Hrd #Hi Hhws HF Hcont
  icases WkEntryNew.pcIsSplit (GF := GF) cpu pc $$ Hpc with ⟨Hpc, Hnpc⟩
  icases winstrMBase (GF := GF) pc _ $$ Hi with ⟨%w, #Hb, %hal2, %hall, %hgood, %hdec⟩
  iapply wwpCsrrMcounterenLeaf gen cpu (is_aligned_vaddr (.Virtaddr pc) 4) pc w rd rd0 pc c q
    WkEntryEff.dM WkEntryEff.dstateM ws hgen hmok hpmp hal2 rfl hnz
    (WeakLeafM.wdecAllBase hall) (fun rs hp hmi hs => agreeMRegs rs hp hs hmi) dMMi hgood hdec
    $$ Hm Hclk Hpc Hnpc Hrd Hb Hhws
  iintro %ws' %hle Hm Hclk Hpc Hrd Hhws
  ihave HF := vwpHold_mono F hle $$ HF
  iapply Hcont $$ %ws' %hle Hm Hclk Hpc Hrd Hhws HF

/-- Rocq `wwp_csrr_mhartid`. -/
theorem wwpCsrrMhartid (gen : Nat) (cpu : CPU) (pc : BitVec 64) (rd : BitVec 5)
    (mhartid_in rd0 : BitVec 64) (c : MConf) (q : Qp) (ws : Wstate) (F : VProp GF) :
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
      hartWs (GF := GF) cpu ws -∗
      vwpHold F ws -∗
      (∀ ws' : Wstate,
        ⌜wsLe ws ws'⌝ -∗
        mConf cpu (DFrac.own q) c -∗
        clockCells cpu -∗
        pcIs cpu (BitVec.addInt pc 4) -∗
        gpr cpu rd (DFrac.own 1) mhartid_in -∗
        Register.mhartid ↦ᵣ[cpu] mhartid_in -∗
        hartWs cpu ws' -∗
        vwpHold F ws' -∗
        wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu)) -∗
      wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu) := by
  intro hgen hmok hpmp hnz
  iintro Hm Hclk Hpc Hcsr Hrd #Hi Hhws HF Hcont
  icases WkEntryNew.pcIsSplit (GF := GF) cpu pc $$ Hpc with ⟨Hpc, Hnpc⟩
  icases winstrMBase (GF := GF) pc _ $$ Hi with ⟨%w, #Hb, %hal2, %hall, %hgood, %hdec⟩
  iapply wwpCsrrMhartidLeaf gen cpu (is_aligned_vaddr (.Virtaddr pc) 4) pc w rd mhartid_in rd0 pc
    c q WkEntryEff.dM WkEntryEff.dstateM ws hgen hmok hpmp hal2 rfl hnz
    (WeakLeafM.wdecAllBase hall) (fun rs hp hmi hs => agreeMRegs rs hp hs hmi) dMMi hgood hdec
    $$ Hm Hclk Hpc Hnpc Hcsr Hrd Hb Hhws
  iintro %ws' %hle Hm Hclk Hpc Hrd Hcsr Hhws
  ihave HF := vwpHold_mono F hle $$ HF
  iapply Hcont $$ %ws' %hle Hm Hclk Hpc Hrd Hcsr Hhws HF

/-- Rocq `wwp_csrr_time`: the continuation quantifies over the value read. -/
theorem wwpCsrrTime (gen : Nat) (cpu : CPU) (pc : BitVec 64) (rd : BitVec 5) (rd0 : BitVec 64)
    (c : MConf) (q : Qp) (ws : Wstate) (F : VProp GF) :
    gen = 0 →
    MConf.mok c →
    pmpAllowsAll c.pmpcfg →
    rd.toNat ≠ 0 →
    mConf (GF := GF) cpu (DFrac.own q) c ⊢
      clockCells cpu -∗
      pcIs cpu pc -∗
      gpr cpu rd (DFrac.own 1) rd0 -∗
      winstrM (GF := GF) pc false (.CSRReg (0xC01#12, zreg, .Regidx rd, .CSRRS)) -∗
      hartWs (GF := GF) cpu ws -∗
      vwpHold F ws -∗
      (∀ (tv : BitVec 64) (ws' : Wstate),
        ⌜wsLe ws ws'⌝ -∗
        mConf cpu (DFrac.own q) c -∗
        clockCells cpu -∗
        pcIs cpu (BitVec.addInt pc 4) -∗
        gpr cpu rd (DFrac.own 1) tv -∗
        hartWs cpu ws' -∗
        vwpHold F ws' -∗
        wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu)) -∗
      wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu) := by
  intro hgen hmok hpmp hnz
  iintro Hm Hclk Hpc Hrd #Hi Hhws HF Hcont
  icases WkEntryNew.pcIsSplit (GF := GF) cpu pc $$ Hpc with ⟨Hpc, Hnpc⟩
  icases winstrMBase (GF := GF) pc _ $$ Hi with ⟨%w, #Hb, %hal2, %hall, %hgood, %hdec⟩
  iapply wwpCsrrTimeLeaf gen cpu (is_aligned_vaddr (.Virtaddr pc) 4) pc w rd rd0 pc c (DFrac.own q)
    WkEntryEff.dM WkEntryEff.dstateM ws hgen hmok hpmp hal2 rfl hnz
    (WeakLeafM.wdecAllBase hall) (fun rs hp hmi hs => agreeMRegs rs hp hs hmi) dMMi hgood hdec
    $$ Hm Hclk Hpc Hnpc Hrd Hb Hhws
  iintro %tv %ws' %hle Hm Hclk Hpc Hrd Hhws
  ihave HF := vwpHold_mono F hle $$ HF
  iapply Hcont $$ %tv %ws' %hle Hm Hclk Hpc Hrd Hhws HF

/-! ## 8. The CSR-write family (deviation 3: full fraction, the CSR inside `mConf`) -/

/-- Rocq `wwp_csrw_menvcfg` (deviation 3). -/
theorem wwpCsrwMenvcfg (gen : Nat) (cpu : CPU) (pc : BitVec 64) (rs1 : BitVec 5) (rs1v : BitVec 64)
    (c : MConf) (ws : Wstate) (F : VProp GF) :
    gen = 0 →
    MConf.mok c →
    pmpAllowsAll c.pmpcfg →
    rs1.toNat ≠ 0 →
    mConf (GF := GF) cpu (DFrac.own 1) c ⊢
      clockCells cpu -∗
      pcIs cpu pc -∗
      gpr cpu rs1 (DFrac.own 1) rs1v -∗
      winstrM (GF := GF) pc false (.CSRReg (0x30A#12, .Regidx rs1, zreg, .CSRRW)) -∗
      hartWs (GF := GF) cpu ws -∗
      vwpHold F ws -∗
      (∀ ws' : Wstate,
        ⌜wsLe ws ws'⌝ -∗
        mConf cpu (DFrac.own 1) { c with menvcfg := WeakLeafCsrw2.menvcfgLegalized c.menvcfg rs1v } -∗
        clockCells cpu -∗
        pcIs cpu (BitVec.addInt pc 4) -∗
        gpr cpu rs1 (DFrac.own 1) rs1v -∗
        hartWs cpu ws' -∗
        vwpHold F ws' -∗
        wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu)) -∗
      wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu) := by
  intro hgen hmok hpmp hnz
  iintro Hm Hclk Hpc Hrs #Hi Hhws HF Hcont
  icases WkEntryNew.pcIsSplit (GF := GF) cpu pc $$ Hpc with ⟨Hpc, Hnpc⟩
  icases winstrMBase (GF := GF) pc _ $$ Hi with ⟨%w, #Hb, %hal2, %hall, %hgood, %hdec⟩
  iapply wwpCsrwMenvcfgLeaf (is_aligned_vaddr (.Virtaddr pc) 4) gen cpu pc w rs1 c rs1v pc
    WkEntryEff.dM WkEntryEff.dstateM ws hgen hmok hpmp hal2 rfl hnz
    (WeakLeafM.wdecAllBase hall) (fun rs hp hmi hs => agreeMRegs rs hp hs hmi) dMMi hgood hdec
    $$ Hm Hclk Hpc Hnpc Hrs Hb Hhws
  iintro %ws' %hle Hm Hclk Hpc Hrs Hhws
  ihave HF := vwpHold_mono F hle $$ HF
  iapply Hcont $$ %ws' %hle Hm Hclk Hpc Hrs Hhws HF

/-- Rocq `wwp_csrw_mcounteren` (deviation 3). -/
theorem wwpCsrwMcounteren (gen : Nat) (cpu : CPU) (pc : BitVec 64) (rs1 : BitVec 5)
    (rs1v : BitVec 64) (c : MConf) (ws : Wstate) (F : VProp GF) :
    gen = 0 →
    MConf.mok c →
    pmpAllowsAll c.pmpcfg →
    rs1.toNat ≠ 0 →
    mConf (GF := GF) cpu (DFrac.own 1) c ⊢
      clockCells cpu -∗
      pcIs cpu pc -∗
      gpr cpu rs1 (DFrac.own 1) rs1v -∗
      winstrM (GF := GF) pc false (.CSRReg (0x306#12, .Regidx rs1, zreg, .CSRRW)) -∗
      hartWs (GF := GF) cpu ws -∗
      vwpHold F ws -∗
      (∀ ws' : Wstate,
        ⌜wsLe ws ws'⌝ -∗
        mConf cpu (DFrac.own 1) { c with mcounteren := legalize_mcounteren c.mcounteren rs1v } -∗
        clockCells cpu -∗
        pcIs cpu (BitVec.addInt pc 4) -∗
        gpr cpu rs1 (DFrac.own 1) rs1v -∗
        hartWs cpu ws' -∗
        vwpHold F ws' -∗
        wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu)) -∗
      wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu) := by
  intro hgen hmok hpmp hnz
  iintro Hm Hclk Hpc Hrs #Hi Hhws HF Hcont
  icases WkEntryNew.pcIsSplit (GF := GF) cpu pc $$ Hpc with ⟨Hpc, Hnpc⟩
  icases winstrMBase (GF := GF) pc _ $$ Hi with ⟨%w, #Hb, %hal2, %hall, %hgood, %hdec⟩
  iapply wwpCsrwMcounterenLeaf (is_aligned_vaddr (.Virtaddr pc) 4) gen cpu pc w rs1 c rs1v pc
    WkEntryEff.dM WkEntryEff.dstateM ws hgen hmok hpmp hal2 rfl hnz
    (WeakLeafM.wdecAllBase hall) (fun rs hp hmi hs => agreeMRegs rs hp hs hmi) dMMi hgood hdec
    $$ Hm Hclk Hpc Hnpc Hrs Hb Hhws
  iintro %ws' %hle Hm Hclk Hpc Hrs Hhws
  ihave HF := vwpHold_mono F hle $$ HF
  iapply Hcont $$ %ws' %hle Hm Hclk Hpc Hrs Hhws HF

/-- Rocq `wwp_csrw_stimecmp` (deviation 3). -/
theorem wwpCsrwStimecmp (gen : Nat) (cpu : CPU) (pc : BitVec 64) (rs1 : BitVec 5)
    (rs1v : BitVec 64) (c : MConf) (ws : Wstate) (F : VProp GF) :
    gen = 0 →
    MConf.mok c →
    pmpAllowsAll c.pmpcfg →
    rs1.toNat ≠ 0 →
    mConf (GF := GF) cpu (DFrac.own 1) c ⊢
      clockCells cpu -∗
      pcIs cpu pc -∗
      gpr cpu rs1 (DFrac.own 1) rs1v -∗
      winstrM (GF := GF) pc false (.CSRReg (0x14D#12, .Regidx rs1, zreg, .CSRRW)) -∗
      hartWs (GF := GF) cpu ws -∗
      vwpHold F ws -∗
      (∀ ws' : Wstate,
        ⌜wsLe ws ws'⌝ -∗
        mConf cpu (DFrac.own 1) { c with stimecmp := stimecmpLegalized c.stimecmp rs1v } -∗
        clockCells cpu -∗
        pcIs cpu (BitVec.addInt pc 4) -∗
        gpr cpu rs1 (DFrac.own 1) rs1v -∗
        hartWs cpu ws' -∗
        vwpHold F ws' -∗
        wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu)) -∗
      wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu) := by
  intro hgen hmok hpmp hnz
  iintro Hm Hclk Hpc Hrs #Hi Hhws HF Hcont
  icases WkEntryNew.pcIsSplit (GF := GF) cpu pc $$ Hpc with ⟨Hpc, Hnpc⟩
  icases winstrMBase (GF := GF) pc _ $$ Hi with ⟨%w, #Hb, %hal2, %hall, %hgood, %hdec⟩
  iapply wwpCsrwStimecmpLeaf gen cpu (is_aligned_vaddr (.Virtaddr pc) 4) pc w rs1 rs1v pc c
    WkEntryEff.dM WkEntryEff.dstateM ws hgen hmok hpmp hal2 rfl hnz
    (WeakLeafM.wdecAllBase hall) (fun rs hp hmi hs => agreeMRegs rs hp hs hmi) dMMi hgood hdec
    $$ Hm Hclk Hpc Hnpc Hrs Hb Hhws
  iintro %ws' %hle Hm Hclk Hpc Hrs Hhws
  ihave HF := vwpHold_mono F hle $$ HF
  iapply Hcont $$ %ws' %hle Hm Hclk Hpc Hrs Hhws HF

/-! ## 9. Control flow -/

/-- Rocq `wwp_jal`. -/
theorem wwpJal (gen : Nat) (cpu : CPU) (pc : BitVec 64) (rd : BitVec 5) (imm : BitVec 21)
    (rdv0 : BitVec 64) (c : MConf) (q : Qp) (ws : Wstate) (F : VProp GF) :
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
      hartWs (GF := GF) cpu ws -∗
      vwpHold F ws -∗
      (∀ ws' : Wstate,
        ⌜wsLe ws ws'⌝ -∗
        mConf cpu (DFrac.own q) c -∗
        clockCells cpu -∗
        pcIs cpu (pc + sign_extend (m := 64) imm) -∗
        gpr cpu rd (DFrac.own 1) (BitVec.addInt pc 4) -∗
        hartWs cpu ws' -∗
        vwpHold F ws' -∗
        wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu)) -∗
      wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu) := by
  intro hgen hmok hpmp hnz htgt
  iintro Hm Hclk Hpc Hrd #Hi Hhws HF Hcont
  icases WkEntryNew.pcIsSplit (GF := GF) cpu pc $$ Hpc with ⟨Hpc, Hnpc⟩
  icases winstrMBase (GF := GF) pc _ $$ Hi with ⟨%w, #Hb, %hal2, %hall, %hgood, %hdec⟩
  iapply wwpJalLeaf gen cpu (is_aligned_vaddr (.Virtaddr pc) 4) pc w rd imm rdv0 pc c q
    WkEntryEff.dM WkEntryEff.dstateM ws hgen hmok hpmp hal2 rfl hnz htgt
    (WeakLeafM.wdecAllBase hall) (fun rs hp hmi hs => agreeMRegs rs hp hs hmi) dMMi hgood hdec
    $$ Hm Hclk Hpc Hnpc Hrd Hb Hhws
  iintro %ws' %hle Hm Hclk Hpc Hrd Hhws
  ihave HF := vwpHold_mono F hle $$ HF
  iapply Hcont $$ %ws' %hle Hm Hclk Hpc Hrd Hhws HF

/-- Rocq `wwp_cjr_rvc`. -/
theorem wwpCjrRvc (gen : Nat) (cpu : CPU) (pc : BitVec 64) (ra : BitVec 5) (rav : BitVec 64)
    (c : MConf) (q : Qp) (ws : Wstate) (F : VProp GF) :
    gen = 0 →
    MConf.mok c →
    pmpAllowsAll c.pmpcfg →
    ra.toNat ≠ 0 →
    mConf (GF := GF) cpu (DFrac.own q) c ⊢
      clockCells cpu -∗
      pcIs cpu pc -∗
      gpr cpu ra (DFrac.own 1) rav -∗
      winstrM (GF := GF) pc true (.JALR (zeros (n := 12), .Regidx ra, zreg)) -∗
      hartWs (GF := GF) cpu ws -∗
      vwpHold F ws -∗
      (∀ ws' : Wstate,
        ⌜wsLe ws ws'⌝ -∗
        mConf cpu (DFrac.own q) c -∗
        clockCells cpu -∗
        pcIs cpu (WeakLeafMret.retPc rav) -∗
        gpr cpu ra (DFrac.own 1) rav -∗
        hartWs cpu ws' -∗
        vwpHold F ws' -∗
        wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu)) -∗
      wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu) := by
  intro hgen hmok hpmp hnz
  iintro Hm Hclk Hpc Hra #Hi Hhws HF Hcont
  icases WkEntryNew.pcIsSplit (GF := GF) cpu pc $$ Hpc with ⟨Hpc, Hnpc⟩
  icases winstrMRvc (GF := GF) pc _ $$ Hi with
    ⟨%h, %i0, -, #Hb, %hal2, %hall, %hgood, %hdec, %hlp0, %hg0, %hexp⟩
  iapply wwpCjrRvcLeaf gen cpu (is_aligned_vaddr (.Virtaddr pc) 4) pc h ra i0 rav pc c q
    WkEntryEff.dM dNone WkEntryEff.dstateM ws hgen hmok hpmp hal2 rfl hnz
    (WeakLeafM.wdecAllRvc hall) (fun rs hp hmi hs => agreeMRegs rs hp hs hmi) dMMi hgood hdec
    hg0 hexp
    $$ Hm Hclk Hpc Hnpc Hra Hb Hhws
  iintro %ws' %hle Hm Hclk Hpc Hra Hhws
  ihave HF := vwpHold_mono F hle $$ HF
  iapply Hcont $$ %ws' %hle Hm Hclk Hpc Hra Hhws HF

/-! ## 10. `mret` -- the packaging only (it takes the cells, not the bundle) -/

/-- Rocq `wwp_mret` (deviation 4). -/
theorem wwpMret (gen : Nat) (cpu : CPU) (pc : BitVec 64) (newpriv : Privilege)
    (ms_cur mepc0 menvcfg1 : BitVec 64) (pmpcfg0 : RegisterType .pmpcfg_n) (ws : Wstate)
    (F : VProp GF) :
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
      hartWs (GF := GF) cpu ws -∗
      vwpHold F ws -∗
      (∀ ws' : Wstate,
        ⌜wsLe ws ws'⌝ -∗
        Register.hart_state ↦ᵣ[cpu] HartState.HART_ACTIVE () -∗
        clockCells cpu -∗
        Register.cur_privilege ↦ᵣ[cpu] newpriv -∗
        Register.mstatus ↦ᵣ[cpu] WeakLeafMret.cms5 ms_cur -∗
        Register.pmpcfg_n ↦ᵣ[cpu] pmpcfg0 -∗
        Register.menvcfg ↦ᵣ[cpu] menvcfg1 -∗
        Register.mepc ↦ᵣ[cpu] mepc0 -∗
        pcIs cpu (WeakLeafMret.retPc mepc0) -∗
        hartWs cpu ws' -∗
        vwpHold F ws' -∗
        wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu)) -∗
      wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu) := by
  intro hgen hpmp hmie hmprv hfwd hnew hlpe
  iintro Hhw Hclk Hhs Hpriv Hms Hpcf Hpc Hmenv Hmepc #Hi Hhws HF Hcont
  icases WkEntryNew.pcIsSplit (GF := GF) cpu pc $$ Hpc with ⟨Hpc, Hnpc⟩
  icases winstrMBase (GF := GF) pc _ $$ Hi with ⟨%w, #Hb, %hal2, %hall, %hgood, %hdec⟩
  iapply wwpMretLeaf gen cpu (is_aligned_vaddr (.Virtaddr pc) 4) pc w newpriv ms_cur mepc0 menvcfg1
    pc pmpcfg0 WkEntryEff.dM WkEntryEff.dstateM ws hgen hpmp hal2 rfl hmie hmprv hfwd hnew hlpe
    (WeakLeafM.wdecAllBase hall) (fun rs hp hmi hs => agreeMRegs rs hp hs hmi) dMMi hgood hdec
    $$ Hhw Hclk Hhs Hpriv Hms Hpcf Hpc Hnpc Hmenv Hmepc Hb Hhws
  iintro %ws' %hle Hhs Hclk Hpriv Hms Hpcf Hmenv Hmepc Hpc Hhws
  ihave HF := vwpHold_mono F hle $$ HF
  iapply Hcont $$ %ws' %hle Hhs Hclk Hpriv Hms Hpcf Hmenv Hmepc Hpc Hhws HF

/-! ## 11. The two memory instructions (the memory interface passed through unchanged) -/

/-- Rocq `wwp_ld8_tor_rvc` (deviations 2, 6). -/
theorem wwpLd8TorRvc (gen : Nat) (cpu : CPU) (pc : BitVec 64) (rs1 rd : BitVec 5) (imm : BitVec 12)
    (ea : PAddr) (v : BitVec 64) (dqv : DFrac) (q : Qp) (c : MConf) (rs1v rd0 : BitVec 64)
    (ws : Wstate) :
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
      hartWs (GF := GF) cpu ws -∗
      vwpHold (wpt8 (GF := GF) ea dqv v) ws -∗
      (∀ ws' : Wstate,
        ⌜wsLe ws ws'⌝ -∗
        mConf cpu (DFrac.own q) c -∗
        clockCells cpu -∗
        pcIs cpu (BitVec.addInt pc 2) -∗
        gpr cpu rs1 (DFrac.own 1) rs1v -∗
        gpr cpu rd (DFrac.own 1) v -∗
        hartWs cpu ws' -∗
        vwpHold (wpt8 (GF := GF) ea dqv v) ws' -∗
        wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu)) -∗
      wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu) := by
  intro hgen hmok hpmp htor hnz1 hnzd hea hram
  iintro Hm Hclk Hpc Hrs Hrd #Hi Hhws Hpt Hcont
  icases WkEntryNew.pcIsSplit (GF := GF) cpu pc $$ Hpc with ⟨Hpc, Hnpc⟩
  icases winstrMRvc (GF := GF) pc _ $$ Hi with
    ⟨%h, %i0, -, #Hb, %hal2, %hall, %hgood, %hdec, %hlp0, %hg0, %hexp⟩
  iapply wwpLd8TorRvcLeaf (is_aligned_vaddr (.Virtaddr pc) 4) gen cpu pc h rs1 rd imm i0 ea v dqv q
    c rs1v rd0 pc WkEntryEff.dM dNone WkEntryEff.dstateM ws hgen hmok hpmp htor hal2 rfl hnz1 hnzd
    hea hram (WeakLeafM.wdecAllRvc hall) (fun rs hp hmi hs => agreeMRegs rs hp hs hmi) dMMi hgood
    hdec hg0 hexp
    $$ Hm Hclk Hpc Hnpc Hrs Hrd Hb Hhws Hpt
  iintro %ws' %hle Hm Hclk Hpc Hrs Hrd Hhws Hpt
  iapply Hcont $$ %ws' %hle Hm Hclk Hpc Hrs Hrd Hhws Hpt

/-- Rocq `wwp_ld8_tor_rvc_own` (deviations 2, 6). -/
theorem wwpLd8TorRvcOwn (gen : Nat) (cpu : CPU) (pc : BitVec 64) (rs1 rd : BitVec 5)
    (imm : BitVec 12) (ea : PAddr) (v : BitVec 64) (q : Qp) (c : MConf) (rs1v rd0 : BitVec 64)
    (ws : Wstate) :
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
      hartWs (GF := GF) cpu ws -∗
      vwpHold (wpt8Own (GF := GF) cpu ea v) ws -∗
      (∀ ws' : Wstate,
        ⌜wsLe ws ws'⌝ -∗
        mConf cpu (DFrac.own q) c -∗
        clockCells cpu -∗
        pcIs cpu (BitVec.addInt pc 2) -∗
        gpr cpu rs1 (DFrac.own 1) rs1v -∗
        gpr cpu rd (DFrac.own 1) v -∗
        hartWs cpu ws' -∗
        vwpHold (wpt8Own (GF := GF) cpu ea v) ws' -∗
        wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu)) -∗
      wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu) := by
  intro hgen hmok hpmp htor hnz1 hnzd hea hram
  iintro Hm Hclk Hpc Hrs Hrd #Hi Hhws Hpt Hcont
  icases WkEntryNew.pcIsSplit (GF := GF) cpu pc $$ Hpc with ⟨Hpc, Hnpc⟩
  icases winstrMRvc (GF := GF) pc _ $$ Hi with
    ⟨%h, %i0, -, #Hb, %hal2, %hall, %hgood, %hdec, %hlp0, %hg0, %hexp⟩
  iapply wwpLd8TorRvcLeafOwn (is_aligned_vaddr (.Virtaddr pc) 4) gen cpu pc h rs1 rd imm i0 ea v q
    c rs1v rd0 pc WkEntryEff.dM dNone WkEntryEff.dstateM ws hgen hmok hpmp htor hal2 rfl hnz1 hnzd
    hea hram (WeakLeafM.wdecAllRvc hall) (fun rs hp hmi hs => agreeMRegs rs hp hs hmi) dMMi hgood
    hdec hg0 hexp
    $$ Hm Hclk Hpc Hnpc Hrs Hrd Hb Hhws Hpt
  iintro %ws' %hle Hm Hclk Hpc Hrs Hrd Hhws Hpt
  iapply Hcont $$ %ws' %hle Hm Hclk Hpc Hrs Hrd Hhws Hpt

/-- Rocq `wwp_sd8_tor_rvc`: the RELEASE store; `T` and its coherence bound kept verbatim. -/
theorem wwpSd8TorRvc (gen : Nat) (cpu : CPU) (pc : BitVec 64) (rs1 rs2 : BitVec 5)
    (imm : BitVec 12) (ea : PAddr) (vold : BitVec 64) (R : VProp GF) (q : Qp) (c : MConf)
    (rs1v rs2v : BitVec 64) (ws : Wstate) :
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
      hartWs (GF := GF) cpu ws -∗
      vwpHold (wpt8Own (GF := GF) cpu ea vold) ws -∗
      vwpHold R ws -∗
      (∀ (ws' : Wstate) (T : Nat),
        ⌜wsLe ws ws'⌝ -∗
        ⌜∀ j : Nat, j < 8 → T ≤ flr (wsView ws') (WeakInterp.accAddr ea j)⌝ -∗
        mConf cpu (DFrac.own q) c -∗
        clockCells cpu -∗
        pcIs cpu (BitVec.addInt pc 2) -∗
        gpr cpu rs1 (DFrac.own 1) rs1v -∗
        gpr cpu rs2 (DFrac.own 1) rs2v -∗
        hartWs cpu ws' -∗
        vwpHold (wpt8Own (GF := GF) cpu ea rs2v) ws' -∗
        R.monPred_at (viewScl T) -∗
        wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu)) -∗
      wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu) := by
  intro hgen hmok hpmp htor hnz1 hnz2 hea hram
  iintro Hm Hclk Hpc Hrs1 Hrs2 #Hi Hhws Hpt HR Hcont
  icases WkEntryNew.pcIsSplit (GF := GF) cpu pc $$ Hpc with ⟨Hpc, Hnpc⟩
  icases winstrMRvc (GF := GF) pc _ $$ Hi with
    ⟨%h, %i0, -, #Hb, %hal2, %hall, %hgood, %hdec, %hlp0, %hg0, %hexp⟩
  iapply wwpSd8TorRvcLeaf (is_aligned_vaddr (.Virtaddr pc) 4) gen cpu pc h rs1 rs2 imm i0 ea vold R
    q c rs1v rs2v pc WkEntryEff.dM dNone WkEntryEff.dstateM ws hgen hmok hpmp htor hal2 rfl hnz1
    hnz2 hea hram (WeakLeafM.wdecAllRvc hall) (fun rs hp hmi hs => agreeMRegs rs hp hs hmi) dMMi
    hgood hdec hg0 hexp
    $$ Hm Hclk Hpc Hnpc Hrs1 Hrs2 Hb Hhws Hpt HR
  iintro %ws' %T %hle %hT Hm Hclk Hpc Hrs1 Hrs2 Hhws Hpt HR
  iapply Hcont $$ %ws' %T %hle %hT Hm Hclk Hpc Hrs1 Hrs2 Hhws Hpt HR

/-! ## 12. The `start()` families -/

/-- Rocq `wwp_and_rvc` (§12a). -/
theorem wwpAndRvc (gen : Nat) (cpu : CPU) (pc : BitVec 64) (rs2 rs1 rd : BitVec 5) (m : RegMap)
    (c : MConf) (q : Qp) (ws : Wstate) (F : VProp GF) :
    gen = 0 →
    MConf.mok c →
    pmpAllowsAll c.pmpcfg →
    rd.toNat ≠ 0 →
    mConf (GF := GF) cpu (DFrac.own q) c ⊢
      clockCells cpu -∗
      pcIs cpu pc -∗
      gprFile cpu m -∗
      winstrM (GF := GF) pc true (.RTYPE (.Regidx rs2, .Regidx rs1, .Regidx rd, .AND)) -∗
      hartWs (GF := GF) cpu ws -∗
      vwpHold F ws -∗
      (∀ ws' : Wstate,
        ⌜wsLe ws ws'⌝ -∗
        mConf cpu (DFrac.own q) c -∗
        clockCells cpu -∗
        pcIs cpu (BitVec.addInt pc 2) -∗
        gprFile cpu (m.set rd (m.get rs1 &&& m.get rs2)) -∗
        hartWs cpu ws' -∗
        vwpHold F ws' -∗
        wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu)) -∗
      wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu) := by
  intro hgen hmok hpmp hnz
  iintro Hm Hclk Hpc Hfile #Hi Hhws HF Hcont
  icases WkEntryNew.pcIsSplit (GF := GF) cpu pc $$ Hpc with ⟨Hpc, Hnpc⟩
  icases winstrMRvc (GF := GF) pc _ $$ Hi with
    ⟨%h, %i0, -, #Hb, %hal2, %hall, %hgood, %hdec, %hlp0, %hg0, %hexp⟩
  iapply wwpAndRvcLeaf (is_aligned_vaddr (.Virtaddr pc) 4) gen cpu pc h rs2 rs1 rd i0 m pc q c
    WkEntryEff.dM dNone WkEntryEff.dstateM ws hgen hmok hpmp hal2 rfl hnz
    (WeakLeafM.wdecAllRvc hall) (fun rs hp hmi hs => agreeMRegs rs hp hs hmi) dMMi hgood hdec
    hg0 hexp
    $$ Hm Hclk Hpc Hnpc Hfile Hb Hhws
  iintro %ws' %hle Hm Hclk Hpc Hfile Hhws
  ihave HF := vwpHold_mono F hle $$ HF
  iapply Hcont $$ %ws' %hle Hm Hclk Hpc Hfile Hhws HF

/-- Rocq `wwp_srli_rvc` (§12b). -/
theorem wwpSrliRvc (gen : Nat) (cpu : CPU) (pc : BitVec 64) (rs1 rd : BitVec 5) (shamt : BitVec 6)
    (m : RegMap) (c : MConf) (q : Qp) (ws : Wstate) (F : VProp GF) :
    gen = 0 →
    MConf.mok c →
    pmpAllowsAll c.pmpcfg →
    rd.toNat ≠ 0 →
    mConf (GF := GF) cpu (DFrac.own q) c ⊢
      clockCells cpu -∗
      pcIs cpu pc -∗
      gprFile cpu m -∗
      winstrM (GF := GF) pc true (.SHIFTIOP (shamt, .Regidx rs1, .Regidx rd, .SRLI)) -∗
      hartWs (GF := GF) cpu ws -∗
      vwpHold F ws -∗
      (∀ ws' : Wstate,
        ⌜wsLe ws ws'⌝ -∗
        mConf cpu (DFrac.own q) c -∗
        clockCells cpu -∗
        pcIs cpu (BitVec.addInt pc 2) -∗
        gprFile cpu (m.set rd (shift_bits_right (m.get rs1)
          (Sail.BitVec.extractLsb shamt (Functions.log2_xlen -i 1) 0))) -∗
        hartWs cpu ws' -∗
        vwpHold F ws' -∗
        wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu)) -∗
      wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu) := by
  intro hgen hmok hpmp hnz
  iintro Hm Hclk Hpc Hfile #Hi Hhws HF Hcont
  icases WkEntryNew.pcIsSplit (GF := GF) cpu pc $$ Hpc with ⟨Hpc, Hnpc⟩
  icases winstrMRvc (GF := GF) pc _ $$ Hi with
    ⟨%h, %i0, -, #Hb, %hal2, %hall, %hgood, %hdec, %hlp0, %hg0, %hexp⟩
  iapply wwpSrliRvcLeaf gen cpu (is_aligned_vaddr (.Virtaddr pc) 4) pc h rs1 rd shamt i0 m pc c q
    WkEntryEff.dM dNone WkEntryEff.dstateM ws hgen hmok hpmp hal2 rfl hnz
    (WeakLeafM.wdecAllRvc hall) (fun rs hp hmi hs => agreeMRegs rs hp hs hmi) dMMi hgood hdec
    hg0 hexp
    $$ Hm Hclk Hpc Hnpc Hfile Hb Hhws
  iintro %ws' %hle Hm Hclk Hpc Hfile Hhws
  ihave HF := vwpHold_mono F hle $$ HF
  iapply Hcont $$ %ws' %hle Hm Hclk Hpc Hfile Hhws HF

/-- Rocq `wwp_auipc` (§12c). -/
theorem wwpAuipc (gen : Nat) (cpu : CPU) (pc : BitVec 64) (rd : BitVec 5) (imm : BitVec 20)
    (m : RegMap) (c : MConf) (q : Qp) (ws : Wstate) (F : VProp GF) :
    gen = 0 →
    MConf.mok c →
    pmpAllowsAll c.pmpcfg →
    rd.toNat ≠ 0 →
    mConf (GF := GF) cpu (DFrac.own q) c ⊢
      clockCells cpu -∗
      pcIs cpu pc -∗
      gprFile cpu m -∗
      winstrM (GF := GF) pc false (.UTYPE (imm, .Regidx rd, .AUIPC)) -∗
      hartWs (GF := GF) cpu ws -∗
      vwpHold F ws -∗
      (∀ ws' : Wstate,
        ⌜wsLe ws ws'⌝ -∗
        mConf cpu (DFrac.own q) c -∗
        clockCells cpu -∗
        pcIs cpu (BitVec.addInt pc 4) -∗
        gprFile cpu (m.set rd (pc + auipcOff imm)) -∗
        hartWs cpu ws' -∗
        vwpHold F ws' -∗
        wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu)) -∗
      wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu) := by
  intro hgen hmok hpmp hnz
  iintro Hm Hclk Hpc Hfile #Hi Hhws HF Hcont
  icases WkEntryNew.pcIsSplit (GF := GF) cpu pc $$ Hpc with ⟨Hpc, Hnpc⟩
  icases winstrMBase (GF := GF) pc _ $$ Hi with ⟨%w, #Hb, %hal2, %hall, %hgood, %hdec⟩
  iapply wwpAuipcLeaf gen cpu (is_aligned_vaddr (.Virtaddr pc) 4) pc w rd imm m pc c q
    WkEntryEff.dM WkEntryEff.dstateM ws hgen hmok hpmp hal2 rfl hnz
    (WeakLeafM.wdecAllBase hall) (fun rs hp hmi hs => agreeMRegs rs hp hs hmi) dMMi hgood hdec
    $$ Hm Hclk Hpc Hnpc Hfile Hb Hhws
  iintro %ws' %hle Hm Hclk Hpc Hfile Hhws
  ihave HF := vwpHold_mono F hle $$ HF
  iapply Hcont $$ %ws' %hle Hm Hclk Hpc Hfile Hhws HF

/-- Rocq `wwp_sd8_off_rvc` (§12d; deviation 6). -/
theorem wwpSd8OffRvc (gen : Nat) (cpu : CPU) (pc : BitVec 64) (rs1 rs2 : BitVec 5)
    (imm : BitVec 12) (ea : PAddr) (vold : BitVec 64) (R : VProp GF) (q : Qp) (c : MConf)
    (rs1v rs2v : BitVec 64) (ws : Wstate) :
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
      hartWs (GF := GF) cpu ws -∗
      vwpHold (wpt8Own (GF := GF) cpu ea vold) ws -∗
      vwpHold R ws -∗
      (∀ (ws' : Wstate) (T : Nat),
        ⌜wsLe ws ws'⌝ -∗
        ⌜∀ j : Nat, j < 8 → T ≤ flr (wsView ws') (WeakInterp.accAddr ea j)⌝ -∗
        mConf cpu (DFrac.own q) c -∗
        clockCells cpu -∗
        pcIs cpu (BitVec.addInt pc 2) -∗
        gpr cpu rs1 (DFrac.own 1) rs1v -∗
        gpr cpu rs2 (DFrac.own 1) rs2v -∗
        hartWs cpu ws' -∗
        vwpHold (wpt8Own (GF := GF) cpu ea rs2v) ws' -∗
        R.monPred_at (viewScl T) -∗
        wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu)) -∗
      wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu) := by
  intro hgen hmok hpmp hnz1 hnz2 hea hram
  iintro Hm Hclk Hpc Hrs1 Hrs2 #Hi Hhws Hpt HR Hcont
  icases WkEntryNew.pcIsSplit (GF := GF) cpu pc $$ Hpc with ⟨Hpc, Hnpc⟩
  icases winstrMRvc (GF := GF) pc _ $$ Hi with
    ⟨%h, %i0, -, #Hb, %hal2, %hall, %hgood, %hdec, %hlp0, %hg0, %hexp⟩
  iapply wwpSd8OffRvcLeaf (is_aligned_vaddr (.Virtaddr pc) 4) gen cpu pc h rs1 rs2 imm i0 ea vold R
    q c rs1v rs2v pc WkEntryEff.dM dNone WkEntryEff.dstateM ws hgen hmok hpmp hal2 rfl hnz1 hnz2
    hea hram (WeakLeafM.wdecAllRvc hall) (fun rs hp hmi hs => agreeMRegs rs hp hs hmi) dMMi hgood
    hdec hg0 hexp
    $$ Hm Hclk Hpc Hnpc Hrs1 Hrs2 Hb Hhws Hpt HR
  iintro %ws' %T %hle %hT Hm Hclk Hpc Hrs1 Hrs2 Hhws Hpt HR
  iapply Hcont $$ %ws' %T %hle %hT Hm Hclk Hpc Hrs1 Hrs2 Hhws Hpt HR

/-- Rocq `wwp_csrr_sie` (§12e; deviation 2). -/
theorem wwpCsrrSie (gen : Nat) (cpu : CPU) (pc : BitVec 64) (rd : BitVec 5) (rd0 : BitVec 64)
    (c : MConf) (q : Qp) (ws : Wstate) (F : VProp GF) :
    gen = 0 →
    MConf.mok c →
    pmpAllowsAll c.pmpcfg →
    rd.toNat ≠ 0 →
    mConf (GF := GF) cpu (DFrac.own q) c ⊢
      clockCells cpu -∗
      pcIs cpu pc -∗
      gpr cpu rd (DFrac.own 1) rd0 -∗
      winstrM (GF := GF) pc false (.CSRReg (0x104#12, zreg, .Regidx rd, .CSRRS)) -∗
      hartWs (GF := GF) cpu ws -∗
      vwpHold F ws -∗
      (∀ ws' : Wstate,
        ⌜wsLe ws ws'⌝ -∗
        mConf cpu (DFrac.own q) c -∗
        clockCells cpu -∗
        pcIs cpu (BitVec.addInt pc 4) -∗
        gpr cpu rd (DFrac.own 1) (lower_mie c.mie c.mideleg) -∗
        hartWs cpu ws' -∗
        vwpHold F ws' -∗
        wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu)) -∗
      wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu) := by
  intro hgen hmok hpmp hnz
  iintro Hm Hclk Hpc Hrd #Hi Hhws HF Hcont
  icases WkEntryNew.pcIsSplit (GF := GF) cpu pc $$ Hpc with ⟨Hpc, Hnpc⟩
  icases winstrMBase (GF := GF) pc _ $$ Hi with ⟨%w, #Hb, %hal2, %hall, %hgood, %hdec⟩
  iapply wwpCsrrSieLeaf gen cpu (is_aligned_vaddr (.Virtaddr pc) 4) pc w rd rd0 pc c q
    WkEntryEff.dM WkEntryEff.dstateM ws hgen hmok hpmp hal2 rfl hnz
    (WeakLeafM.wdecAllBase hall) (fun rs hp hmi hs => agreeMRegs rs hp hs hmi) dMMi hgood hdec
    $$ Hm Hclk Hpc Hnpc Hrd Hb Hhws
  iintro %ws' %hle Hm Hclk Hpc Hrd Hhws
  ihave HF := vwpHold_mono F hle $$ HF
  iapply Hcont $$ %ws' %hle Hm Hclk Hpc Hrd Hhws HF

/-- Rocq `wwp_csrw_mepc` (§12f; deviation 3). -/
theorem wwpCsrwMepc (gen : Nat) (cpu : CPU) (pc : BitVec 64) (rs1 : BitVec 5) (rs1v : BitVec 64)
    (c : MConf) (ws : Wstate) (F : VProp GF) :
    gen = 0 →
    MConf.mok c →
    pmpAllowsAll c.pmpcfg →
    rs1.toNat ≠ 0 →
    mConf (GF := GF) cpu (DFrac.own 1) c ⊢
      clockCells cpu -∗
      pcIs cpu pc -∗
      gpr cpu rs1 (DFrac.own 1) rs1v -∗
      winstrM (GF := GF) pc false (.CSRReg (0x341#12, .Regidx rs1, zreg, .CSRRW)) -∗
      hartWs (GF := GF) cpu ws -∗
      vwpHold F ws -∗
      (∀ ws' : Wstate,
        ⌜wsLe ws ws'⌝ -∗
        mConf cpu (DFrac.own 1) { c with mepc := WeakLeafCsrw2.mepcVal rs1v } -∗
        clockCells cpu -∗
        pcIs cpu (BitVec.addInt pc 4) -∗
        gpr cpu rs1 (DFrac.own 1) rs1v -∗
        hartWs cpu ws' -∗
        vwpHold F ws' -∗
        wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu)) -∗
      wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu) := by
  intro hgen hmok hpmp hnz
  iintro Hm Hclk Hpc Hrs #Hi Hhws HF Hcont
  icases WkEntryNew.pcIsSplit (GF := GF) cpu pc $$ Hpc with ⟨Hpc, Hnpc⟩
  icases winstrMBase (GF := GF) pc _ $$ Hi with ⟨%w, #Hb, %hal2, %hall, %hgood, %hdec⟩
  iapply wwpCsrwMepcLeaf (is_aligned_vaddr (.Virtaddr pc) 4) gen cpu pc w rs1 c rs1v pc
    WkEntryEff.dM WkEntryEff.dstateM ws hgen hmok hpmp hal2 rfl hnz
    (WeakLeafM.wdecAllBase hall) (fun rs hp hmi hs => agreeMRegs rs hp hs hmi) dMMi hgood hdec
    $$ Hm Hclk Hpc Hnpc Hrs Hb Hhws
  iintro %ws' %hle Hm Hclk Hpc Hrs Hhws
  ihave HF := vwpHold_mono F hle $$ HF
  iapply Hcont $$ %ws' %hle Hm Hclk Hpc Hrs Hhws HF

/-- Rocq `wwp_csrw_satp` (§12g; deviation 3, the leaf's SXL premise). -/
theorem wwpCsrwSatp (gen : Nat) (cpu : CPU) (pc : BitVec 64) (rs1 : BitVec 5) (rs1v : BitVec 64)
    (c : MConf) (ws : Wstate) (F : VProp GF) :
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
      hartWs (GF := GF) cpu ws -∗
      vwpHold F ws -∗
      (∀ ws' : Wstate,
        ⌜wsLe ws ws'⌝ -∗
        mConf cpu (DFrac.own 1) { c with satp := WeakLeafCsrw3.satpLegalized c.satp rs1v } -∗
        clockCells cpu -∗
        pcIs cpu (BitVec.addInt pc 4) -∗
        gpr cpu rs1 (DFrac.own 1) rs1v -∗
        hartWs cpu ws' -∗
        vwpHold F ws' -∗
        wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu)) -∗
      wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu) := by
  intro hgen hmok hpmp hnz hsxl
  iintro Hm Hclk Hpc Hrs #Hi Hhws HF Hcont
  icases WkEntryNew.pcIsSplit (GF := GF) cpu pc $$ Hpc with ⟨Hpc, Hnpc⟩
  icases winstrMBase (GF := GF) pc _ $$ Hi with ⟨%w, #Hb, %hal2, %hall, %hgood, %hdec⟩
  iapply wwpCsrwSatpLeaf gen cpu (is_aligned_vaddr (.Virtaddr pc) 4) pc w rs1 rs1v pc c
    WkEntryEff.dM WkEntryEff.dstateM ws hgen hmok hpmp hal2 rfl hnz hsxl
    (WeakLeafM.wdecAllBase hall) (fun rs hp hmi hs => agreeMRegs rs hp hs hmi) dMMi hgood hdec
    $$ Hm Hclk Hpc Hnpc Hrs Hb Hhws
  iintro %ws' %hle Hm Hclk Hpc Hrs Hhws
  ihave HF := vwpHold_mono F hle $$ HF
  iapply Hcont $$ %ws' %hle Hm Hclk Hpc Hrs Hhws HF

/-- Rocq `wwp_csrw_medeleg` (§12h; deviation 3). -/
theorem wwpCsrwMedeleg (gen : Nat) (cpu : CPU) (pc : BitVec 64) (rs1 : BitVec 5) (rs1v : BitVec 64)
    (c : MConf) (ws : Wstate) (F : VProp GF) :
    gen = 0 →
    MConf.mok c →
    pmpAllowsAll c.pmpcfg →
    rs1.toNat ≠ 0 →
    mConf (GF := GF) cpu (DFrac.own 1) c ⊢
      clockCells cpu -∗
      pcIs cpu pc -∗
      gpr cpu rs1 (DFrac.own 1) rs1v -∗
      winstrM (GF := GF) pc false (.CSRReg (0x302#12, .Regidx rs1, zreg, .CSRRW)) -∗
      hartWs (GF := GF) cpu ws -∗
      vwpHold F ws -∗
      (∀ ws' : Wstate,
        ⌜wsLe ws ws'⌝ -∗
        mConf cpu (DFrac.own 1) { c with medeleg := legalize_medeleg c.medeleg rs1v } -∗
        clockCells cpu -∗
        pcIs cpu (BitVec.addInt pc 4) -∗
        gpr cpu rs1 (DFrac.own 1) rs1v -∗
        hartWs cpu ws' -∗
        vwpHold F ws' -∗
        wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu)) -∗
      wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu) := by
  intro hgen hmok hpmp hnz
  iintro Hm Hclk Hpc Hrs #Hi Hhws HF Hcont
  icases WkEntryNew.pcIsSplit (GF := GF) cpu pc $$ Hpc with ⟨Hpc, Hnpc⟩
  icases winstrMBase (GF := GF) pc _ $$ Hi with ⟨%w, #Hb, %hal2, %hall, %hgood, %hdec⟩
  iapply wwpCsrwMedelegLeaf (is_aligned_vaddr (.Virtaddr pc) 4) gen cpu pc w rs1 c rs1v pc
    WkEntryEff.dM WkEntryEff.dstateM ws hgen hmok hpmp hal2 rfl hnz
    (WeakLeafM.wdecAllBase hall) (fun rs hp hmi hs => agreeMRegs rs hp hs hmi) dMMi hgood hdec
    $$ Hm Hclk Hpc Hnpc Hrs Hb Hhws
  iintro %ws' %hle Hm Hclk Hpc Hrs Hhws
  ihave HF := vwpHold_mono F hle $$ HF
  iapply Hcont $$ %ws' %hle Hm Hclk Hpc Hrs Hhws HF

/-- Rocq `wwp_csrw_mideleg` (§12i; deviation 3). -/
theorem wwpCsrwMideleg (gen : Nat) (cpu : CPU) (pc : BitVec 64) (rs1 : BitVec 5) (rs1v : BitVec 64)
    (c : MConf) (ws : Wstate) (F : VProp GF) :
    gen = 0 →
    MConf.mok c →
    pmpAllowsAll c.pmpcfg →
    rs1.toNat ≠ 0 →
    mConf (GF := GF) cpu (DFrac.own 1) c ⊢
      clockCells cpu -∗
      pcIs cpu pc -∗
      gpr cpu rs1 (DFrac.own 1) rs1v -∗
      winstrM (GF := GF) pc false (.CSRReg (0x303#12, .Regidx rs1, zreg, .CSRRW)) -∗
      hartWs (GF := GF) cpu ws -∗
      vwpHold F ws -∗
      (∀ ws' : Wstate,
        ⌜wsLe ws ws'⌝ -∗
        mConf cpu (DFrac.own 1) { c with mideleg := WeakLeafCsrw2.midelegLegalized c.mideleg rs1v } -∗
        clockCells cpu -∗
        pcIs cpu (BitVec.addInt pc 4) -∗
        gpr cpu rs1 (DFrac.own 1) rs1v -∗
        hartWs cpu ws' -∗
        vwpHold F ws' -∗
        wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu)) -∗
      wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu) := by
  intro hgen hmok hpmp hnz
  iintro Hm Hclk Hpc Hrs #Hi Hhws HF Hcont
  icases WkEntryNew.pcIsSplit (GF := GF) cpu pc $$ Hpc with ⟨Hpc, Hnpc⟩
  icases winstrMBase (GF := GF) pc _ $$ Hi with ⟨%w, #Hb, %hal2, %hall, %hgood, %hdec⟩
  iapply wwpCsrwMidelegLeaf (is_aligned_vaddr (.Virtaddr pc) 4) gen cpu pc w rs1 c rs1v pc
    WkEntryEff.dM WkEntryEff.dstateM ws hgen hmok hpmp hal2 rfl hnz
    (WeakLeafM.wdecAllBase hall) (fun rs hp hmi hs => agreeMRegs rs hp hs hmi) dMMi hgood hdec
    $$ Hm Hclk Hpc Hnpc Hrs Hb Hhws
  iintro %ws' %hle Hm Hclk Hpc Hrs Hhws
  ihave HF := vwpHold_mono F hle $$ HF
  iapply Hcont $$ %ws' %hle Hm Hclk Hpc Hrs Hhws HF

/-- Rocq `wwp_csrw_sie` (§12j; deviation 3: `mie`/`mideleg` inside `mConf`). -/
theorem wwpCsrwSie (gen : Nat) (cpu : CPU) (pc : BitVec 64) (rs1 : BitVec 5) (rs1v : BitVec 64)
    (c : MConf) (ws : Wstate) (F : VProp GF) :
    gen = 0 →
    MConf.mok c →
    pmpAllowsAll c.pmpcfg →
    rs1.toNat ≠ 0 →
    mConf (GF := GF) cpu (DFrac.own 1) c ⊢
      clockCells cpu -∗
      pcIs cpu pc -∗
      gpr cpu rs1 (DFrac.own 1) rs1v -∗
      winstrM (GF := GF) pc false (.CSRReg (0x104#12, .Regidx rs1, zreg, .CSRRW)) -∗
      hartWs (GF := GF) cpu ws -∗
      vwpHold F ws -∗
      (∀ ws' : Wstate,
        ⌜wsLe ws ws'⌝ -∗
        mConf cpu (DFrac.own 1) { c with mie := WeakLeafCsrw3.sieNewMie c.mie c.mideleg rs1v } -∗
        clockCells cpu -∗
        pcIs cpu (BitVec.addInt pc 4) -∗
        gpr cpu rs1 (DFrac.own 1) rs1v -∗
        hartWs cpu ws' -∗
        vwpHold F ws' -∗
        wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu)) -∗
      wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu) := by
  intro hgen hmok hpmp hnz
  iintro Hm Hclk Hpc Hrs #Hi Hhws HF Hcont
  icases WkEntryNew.pcIsSplit (GF := GF) cpu pc $$ Hpc with ⟨Hpc, Hnpc⟩
  icases winstrMBase (GF := GF) pc _ $$ Hi with ⟨%w, #Hb, %hal2, %hall, %hgood, %hdec⟩
  iapply wwpCsrwSieLeaf gen cpu (is_aligned_vaddr (.Virtaddr pc) 4) pc w rs1 rs1v pc c
    WkEntryEff.dM WkEntryEff.dstateM ws hgen hmok hpmp hal2 rfl hnz
    (WeakLeafM.wdecAllBase hall) (fun rs hp hmi hs => agreeMRegs rs hp hs hmi) dMMi hgood hdec
    $$ Hm Hclk Hpc Hnpc Hrs Hb Hhws
  iintro %ws' %hle Hm Hclk Hpc Hrs Hhws
  ihave HF := vwpHold_mono F hle $$ HF
  iapply Hcont $$ %ws' %hle Hm Hclk Hpc Hrs Hhws HF

/-- Rocq `wwp_csrw_pmpaddr0` (§12k; deviation 3: `pmpaddr_n` inside `mConf`). -/
theorem wwpCsrwPmpaddr0 (gen : Nat) (cpu : CPU) (pc : BitVec 64) (rs1 : BitVec 5) (rs1v : BitVec 64)
    (c : MConf) (ws : Wstate) (F : VProp GF) :
    gen = 0 →
    MConf.mok c →
    pmpAllowsAll c.pmpcfg →
    rs1.toNat ≠ 0 →
    mConf (GF := GF) cpu (DFrac.own 1) c ⊢
      clockCells cpu -∗
      pcIs cpu pc -∗
      gpr cpu rs1 (DFrac.own 1) rs1v -∗
      winstrM (GF := GF) pc false (.CSRReg (0x3B0#12, .Regidx rs1, zreg, .CSRRW)) -∗
      hartWs (GF := GF) cpu ws -∗
      vwpHold F ws -∗
      (∀ ws' : Wstate,
        ⌜wsLe ws ws'⌝ -∗
        mConf cpu (DFrac.own 1)
          { c with pmpaddr := WeakLeafCsrw3.pmp0Newaddr c.pmpcfg c.pmpaddr rs1v } -∗
        clockCells cpu -∗
        pcIs cpu (BitVec.addInt pc 4) -∗
        gpr cpu rs1 (DFrac.own 1) rs1v -∗
        hartWs cpu ws' -∗
        vwpHold F ws' -∗
        wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu)) -∗
      wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu) := by
  intro hgen hmok hpmp hnz
  iintro Hm Hclk Hpc Hrs #Hi Hhws HF Hcont
  icases WkEntryNew.pcIsSplit (GF := GF) cpu pc $$ Hpc with ⟨Hpc, Hnpc⟩
  icases winstrMBase (GF := GF) pc _ $$ Hi with ⟨%w, #Hb, %hal2, %hall, %hgood, %hdec⟩
  iapply wwpCsrwPmpaddr0Leaf gen cpu (is_aligned_vaddr (.Virtaddr pc) 4) pc w rs1 rs1v pc c
    WkEntryEff.dM WkEntryEff.dstateM ws hgen hmok hpmp hal2 rfl hnz
    (WeakLeafM.wdecAllBase hall) (fun rs hp hmi hs => agreeMRegs rs hp hs hmi) dMMi hgood hdec
    $$ Hm Hclk Hpc Hnpc Hrs Hb Hhws
  iintro %ws' %hle Hm Hclk Hpc Hrs Hhws
  ihave HF := vwpHold_mono F hle $$ HF
  iapply Hcont $$ %ws' %hle Hm Hclk Hpc Hrs Hhws HF

/-- Rocq `wwp_csrr_mstatus` (§12l; deviation 4). -/
theorem wwpCsrrMstatus (gen : Nat) (cpu : CPU) (pc : BitVec 64) (rd : BitVec 5) (ms0 rd0 : BitVec 64)
    (pmpcfg0 : RegisterType .pmpcfg_n) (ws : Wstate) (F : VProp GF) :
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
      hartWs (GF := GF) cpu ws -∗
      vwpHold F ws -∗
      (∀ ws' : Wstate,
        ⌜wsLe ws ws'⌝ -∗
        Register.hart_state ↦ᵣ[cpu] HartState.HART_ACTIVE () -∗
        Register.cur_privilege ↦ᵣ[cpu] Privilege.Machine -∗
        Register.mstatus ↦ᵣ[cpu] ms0 -∗
        Register.pmpcfg_n ↦ᵣ[cpu] pmpcfg0 -∗
        clockCells cpu -∗
        pcIs cpu (BitVec.addInt pc 4) -∗
        gpr cpu rd (DFrac.own 1) ms0 -∗
        hartWs cpu ws' -∗
        vwpHold F ws' -∗
        wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu)) -∗
      wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu) := by
  intro hgen hpmp hnz hmie hmprv
  iintro Hhw Hclk Hhs Hpriv Hms Hpcf Hpc Hrd #Hi Hhws HF Hcont
  icases WkEntryNew.pcIsSplit (GF := GF) cpu pc $$ Hpc with ⟨Hpc, Hnpc⟩
  icases winstrMBase (GF := GF) pc _ $$ Hi with ⟨%w, #Hb, %hal2, %hall, %hgood, %hdec⟩
  iapply wwpCsrrMstatusLeaf gen cpu (is_aligned_vaddr (.Virtaddr pc) 4) pc w rd ms0 rd0 pc pmpcfg0
    WkEntryEff.dM WkEntryEff.dstateM ws hgen hpmp hal2 rfl hnz hmie hmprv
    (WeakLeafM.wdecAllBase hall) (fun rs hp hmi hs => agreeMRegs rs hp hs hmi) dMMi hgood hdec
    $$ Hhw Hclk Hhs Hpriv Hms Hpcf Hpc Hnpc Hrd Hb Hhws
  iintro %ws' %hle Hhs Hpriv Hms Hpcf Hclk Hpc Hrd Hhws
  ihave HF := vwpHold_mono F hle $$ HF
  iapply Hcont $$ %ws' %hle Hhs Hpriv Hms Hpcf Hclk Hpc Hrd Hhws HF

/-- Rocq `wwp_csrw_mstatus` (§12m; deviation 4): its leaf is 4-aligned only, so the
alignment is a premise. -/
theorem wwpCsrwMstatus (gen : Nat) (cpu : CPU) (pc : BitVec 64) (rs1 : BitVec 5)
    (ms0 rs1v : BitVec 64) (pmpcfg0 : RegisterType .pmpcfg_n) (ws : Wstate) (F : VProp GF) :
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
      hartWs (GF := GF) cpu ws -∗
      vwpHold F ws -∗
      (∀ ws' : Wstate,
        ⌜wsLe ws ws'⌝ -∗
        Register.hart_state ↦ᵣ[cpu] HartState.HART_ACTIVE () -∗
        Register.cur_privilege ↦ᵣ[cpu] Privilege.Machine -∗
        Register.mstatus ↦ᵣ[cpu] WeakLeafCsrw.mstatusLegalized ms0 rs1v -∗
        Register.pmpcfg_n ↦ᵣ[cpu] pmpcfg0 -∗
        clockCells cpu -∗
        pcIs cpu (BitVec.addInt pc 4) -∗
        gpr cpu rs1 (DFrac.own 1) rs1v -∗
        hartWs cpu ws' -∗
        vwpHold F ws' -∗
        wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu)) -∗
      wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu) := by
  intro hgen hpmp hal4 hnz hmie hmprv
  iintro Hhw Hclk Hhs Hpriv Hms Hpcf Hpc Hrs #Hi Hhws HF Hcont
  icases WkEntryNew.pcIsSplit (GF := GF) cpu pc $$ Hpc with ⟨Hpc, Hnpc⟩
  icases winstrMBase (GF := GF) pc _ $$ Hi with ⟨%w, #Hb, %_hal2, %hall, %hgood, %hdec⟩
  iapply wwpCsrwMstatusLeaf gen cpu pc w rs1 ms0 rs1v pc pmpcfg0
    WkEntryEff.dM WkEntryEff.dstateM ws hgen hpmp hal4 hnz hmie hmprv
    (WeakLeafM.wdecAllBase hall) (fun rs hp hmi hs => agreeMRegs rs hp hs hmi) dMMi hgood hdec
    $$ Hhw Hclk Hhs Hpriv Hms Hpcf Hpc Hnpc Hrs Hb Hhws
  iintro %ws' %hle Hhs Hpriv Hms Hpcf Hclk Hpc Hrs Hhws
  ihave HF := vwpHold_mono F hle $$ HF
  iapply Hcont $$ %ws' %hle Hhs Hpriv Hms Hpcf Hclk Hpc Hrs Hhws HF

/-- Rocq `wwp_csrw_pmpcfg0` (§12n; deviation 4). -/
theorem wwpCsrwPmpcfg0 (gen : Nat) (cpu : CPU) (pc : BitVec 64) (rs1 : BitVec 5)
    (ms0 rs1v : BitVec 64) (pmpcfg0 : RegisterType .pmpcfg_n) (ws : Wstate) (F : VProp GF) :
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
      hartWs (GF := GF) cpu ws -∗
      vwpHold F ws -∗
      (∀ ws' : Wstate,
        ⌜wsLe ws ws'⌝ -∗
        Register.hart_state ↦ᵣ[cpu] HartState.HART_ACTIVE () -∗
        Register.cur_privilege ↦ᵣ[cpu] Privilege.Machine -∗
        Register.mstatus ↦ᵣ[cpu] ms0 -∗
        Register.pmpcfg_n ↦ᵣ[cpu] WeakLeafPmpcfg0.pmpcfgWritten rs1v pmpcfg0 -∗
        clockCells cpu -∗
        pcIs cpu (BitVec.addInt pc 4) -∗
        gpr cpu rs1 (DFrac.own 1) rs1v -∗
        hartWs cpu ws' -∗
        vwpHold F ws' -∗
        wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu)) -∗
      wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu) := by
  intro hgen hpmp hnz hmie hmprv
  iintro Hhw Hclk Hhs Hpriv Hms Hpcf Hpc Hrs #Hi Hhws HF Hcont
  icases WkEntryNew.pcIsSplit (GF := GF) cpu pc $$ Hpc with ⟨Hpc, Hnpc⟩
  icases winstrMBase (GF := GF) pc _ $$ Hi with ⟨%w, #Hb, %hal2, %hall, %hgood, %hdec⟩
  iapply wwpCsrwPmpcfg0Leaf (is_aligned_vaddr (.Virtaddr pc) 4) gen cpu pc w rs1 ms0 rs1v pc
    pmpcfg0 WkEntryEff.dM WkEntryEff.dstateM ws hgen hpmp hal2 rfl hnz hmie hmprv
    (WeakLeafM.wdecAllBase hall) (fun rs hp hmi hs => agreeMRegs rs hp hs hmi) dMMi hgood hdec
    $$ Hhw Hclk Hhs Hpriv Hms Hpcf Hpc Hnpc Hrs Hb Hhws
  iintro %ws' %hle Hhs Hpriv Hms Hpcf Hclk Hpc Hrs Hhws
  ihave HF := vwpHold_mono F hle $$ HF
  iapply Hcont $$ %ws' %hle Hhs Hpriv Hms Hpcf Hclk Hpc Hrs Hhws HF

end wrappers

end Weak
