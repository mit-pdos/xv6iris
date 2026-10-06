/-
Weak: **the MRET leaf on `WeakFunnelCfg.wwpInstrConfig`** (M4) -- the weak twin
of the SC `mret` rule: from the hardware config, the clock cells, the unbundled
config cells (`hart_state`, `cur_privilege`, `mstatus`, `pmpcfg_n`), the PC /
nextPC / `menvcfg` / `mepc` cells and the weak instruction bytes to `WWP Loop`.

Rocq: `iris/WeakLeafMret.v` @ xxvzwolszwmp.

The Rocq header, in substance.  MRET is the third and last CONFIG-WRITING
M-mode instruction (csrw mstatus / csrw pmpcfg0 / MRET), so it goes through the
config-variant funnel `wwpInstrConfig`.  It is REGISTER-ONLY: its `execute`
mirror is the trace-`[]` one and the certificate is `wcertNowrite` at the
fetch-only trace, in the ALIGNMENT-GENERIC form of `WeakLeafRegOnly`
(`regonlyEs al4 pc` / `wcertRegonly`) -- the kernel's `mret` sits at a
2-not-4-aligned pc.
* §1 the `execEff` mirrors, trace `[]`: the long-CSR write callback for
  mstatus, `set_next_pc`, `get_xLPE` at Supervisor and the whole
  `execute (.MRET ())`.
* §2 the successor register frame `mretSexecFacts` (TEN `setReg`s deep).
* §3 the leaf `wwpMretLeaf`.

**Deviations from Rocq.**
1. NAMES / VOCABULARY: the tree's camelCase (map below), as
   `Weak/WeakLeafLw4.lean` deviation 1 (`register_lookup r s.(sregs)` ↦
   `s.regs r`, `eq_vec x 'b"1" = b` ↦ `(x == 1#1) = b`, `set_reg` ↦
   `ExecSt.setReg`, `add_vec_int` ↦ `BitVec.addInt`, `mword n` ↦ `BitVec n`,
   `ws_le` ↦ `wsLe`, `hart_ws` ↦ `hartWs`, `MState (wm_regs σ) (wmem_restrict
   σ W) (wm_dev σ)` ↦ `⟨σ.wmRegs, wmemRestrict σ W, σ.wmDev⟩`, `dom (mem s) ⊆ W`
   ↦ `bmDomSub s.mem W`, `RETIRE_SUCCESS` ↦ `RETIRE_SUCCESS`/`.Retire_Success ()`,
   `pmp_allows_all` ↦ `pmpAllowsAll`, `returnM` ↦ `pure`,
   `SailStdpp.Instances.generic_neq` ↦ `bne`).
2. THE MSTATUS TOWER: Rocq's section `Let`s `ms0 … ms5` of `exec_eff_execute_MRET`
   are the SC file `WpGprMretWp`'s `cms1 … cms5` applied to `s.regs .mstatus`
   (the same expressions); `WpGprMretWp` has no Lean counterpart (its Lean analog
   `MachCSL.WpMmodeMret` uses `mretMstatus`), so `cms1 … cms5` and RiscvExtras'
   `ret_pc` are defined here, file-qualified (`WeakLeafMret.cms1` …,
   `WeakLeafMret.retPc`), with their fold equations (`WeakLeafMret.cms1Fold` …,
   Lean-only).  The `Let`s `elpv`/`tgt`/`sF`/`sLPE` are inlined.
   `WpMmodeLeafBase.mword1_not_lp` likewise is `WeakLeafMret.mword1NotLp`.
3. THE LEAN MODEL's `execute_MRET` differs syntactically from Rocq's (the
   `currentlyEnabled Ext_U` choice is an `if` inside `privLevel_to_bits`, the
   Zicfilp restore is guarded by the pure `hartSupports .Ext_Zicfilp`, there is
   no fuel in `get_xLPE`); the statements are the same, the proofs are by the
   `execEff` normaliser instead of the token-for-token replay.
4. THE CONFIG INTERFACE (owner decision Q3, `Weak/WeakFunnelCfg.lean`
   deviation 2): Rocq `hw_config -∗ minstret_inv -∗` ↦ `hwConfig cpu ⊢
   clockCells cpu -∗`; the cells are `↦ᵣ[cpu]` at full ownership; the
   continuation additionally receives `clockCells cpu` (after `hart_state`), as
   the funnel's own continuation does.  `GenId`/`CpuId` are the explicit
   `gen`/`cpu`; `WWP Loop` ↦ `wwpTriv ⊤ (WExpr.loop gen cpu)`; `pc_is` ↦
   `MachCSL.pcIs`.
5. Rocq's `reg_interp_set_same` (the value-preserving `elp` write) is a
   rewrite of the exhibited successor by the Lean-only
   `WeakLeafMret.setRegSameVal`; Rocq's in-proof `assert (Hc …)` and the flat
   run are one Lean-only helper `WeakLeafMret.execEffMretAt` (the run at ANY
   state with the funnel's two pre-writes), used at both states.  The O2 fetch
   pin `fetchPin σ (regonlyEs al4 pc)` that `wPEffOfLeafRegonly` takes (its
   deviation 3) is discharged from the text bytes.  The isRVC fact is
   `WeakLeafLw4.winstrBytesNotRVC`; `mret_peel` is not needed (the frame is by
   `setLookupNe`).
6. Rocq §4's `Print Assumptions` commands are not declarations.

**Rocq → Lean name map.**  `exec_eff_long_csr_write_mstatus`
`execEffLongCsrWriteMstatus`, `exec_eff_set_next_pc`
`WeakLeafMret.execEffSetNextPc` (duplicated name), `exec_eff_get_xLPE_S`
`execEffGetXLPES`, `exec_eff_execute_MRET` `execEffExecuteMRET`,
`mret_sexec_facts` `mretSexecFacts`, `wwp_mret_leaf` `wwpMretLeaf`.
Lean-only (file-qualified): `WeakLeafMret.cms1` … `cms5`, `WeakLeafMret.retPc`,
`WeakLeafMret.cms1Fold` … `cms5Fold`, `WeakLeafMret.retPcFold`,
`WeakLeafMret.mword1NotLp`, `WeakLeafMret.setRegSameVal`,
`WeakLeafMret.execEffMretAt`.

**Dropped:** the Ltac `mret_peel` (deviation 5).  Rocq 6 `Lemma`s; Lean 6
theorems + 15 Lean-only.
-/
import Weak.WeakLeafRegOnly
import Weak.WeakFunnelCfg
import Weak.WeakLeafLw4

namespace Weak

open Iris Iris.BI Iris.BI.MonPred Iris.ProofMode Iris.Std
open MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D LeanRV64D.Functions

/-! ## 0. The MRET mstatus tower (Lean-only, deviation 2) -/

/-- `WpGprMretWp.cms1`: `MIE := MPIE`. -/
def WeakLeafMret.cms1 (m : BitVec 64) : BitVec 64 :=
  Sail.BitVec.updateSubrange m 3 3 (_get_Mstatus_MPIE m)
/-- `WpGprMretWp.cms2`: `MPIE := 1`. -/
def WeakLeafMret.cms2 (m : BitVec 64) : BitVec 64 :=
  Sail.BitVec.updateSubrange (WeakLeafMret.cms1 m) 7 7 1#1
/-- `WpGprMretWp.cms3`: `MPP := U`. -/
def WeakLeafMret.cms3 (m : BitVec 64) : BitVec 64 :=
  Sail.BitVec.updateSubrange (WeakLeafMret.cms2 m) 12 11 (privLevel_to_bits .User)
/-- `WpGprMretWp.cms4`: `MPRV := 0`. -/
def WeakLeafMret.cms4 (m : BitVec 64) : BitVec 64 :=
  Sail.BitVec.updateSubrange (WeakLeafMret.cms3 m) 17 17 0#1
/-- `WpGprMretWp.cms5`: `MPELP := NO_LP_EXPECTED`. -/
def WeakLeafMret.cms5 (m : BitVec 64) : BitVec 64 :=
  Sail.BitVec.updateSubrange (WeakLeafMret.cms4 m) 41 41 (landing_pad_bits_backwards .NO_LP_EXPECTED)
/-- `RiscvExtras.ret_pc`: bit 0 cleared. -/
def WeakLeafMret.retPc (v : BitVec 64) : BitVec 64 := BitVec.update v 0 0#1

theorem WeakLeafMret.cms1Fold (m : BitVec 64) :
    Sail.BitVec.updateSubrange m 3 3 (_get_Mstatus_MPIE m) = WeakLeafMret.cms1 m := rfl
theorem WeakLeafMret.cms2Fold (m : BitVec 64) :
    Sail.BitVec.updateSubrange (WeakLeafMret.cms1 m) 7 7 1#1 = WeakLeafMret.cms2 m := rfl
theorem WeakLeafMret.cms3Fold (m : BitVec 64) :
    Sail.BitVec.updateSubrange (WeakLeafMret.cms2 m) 12 11 (privLevel_to_bits .User) =
      WeakLeafMret.cms3 m := rfl
theorem WeakLeafMret.cms4Fold (m : BitVec 64) :
    Sail.BitVec.updateSubrange (WeakLeafMret.cms3 m) 17 17 0#1 = WeakLeafMret.cms4 m := rfl
theorem WeakLeafMret.cms5Fold (m : BitVec 64) :
    Sail.BitVec.updateSubrange (WeakLeafMret.cms4 m) 41 41 (landing_pad_bits_backwards .NO_LP_EXPECTED) =
      WeakLeafMret.cms5 m := rfl
theorem WeakLeafMret.retPcFold (v : BitVec 64) : BitVec.update v 0 0#1 = WeakLeafMret.retPc v := rfl

/-- `WpMmodeLeafBase.mword1_not_lp`. -/
theorem WeakLeafMret.mword1NotLp (x : BitVec 1) :
    (x == landing_pad_bits_backwards .LP_EXPECTED) = false →
    x = landing_pad_bits_backwards .NO_LP_EXPECTED := by
  intro h
  have hx : x = 0#1 ∨ x = 1#1 := by bv_omega
  rcases hx with rfl | rfl
  · rfl
  · exact absurd h (by decide)

/-- A same-value register write is the identity on the state (Lean-only; Rocq
`reg_interp_set_same`'s pure core). -/
theorem WeakLeafMret.setRegSameVal (s : ExecSt) (r : Register) (v : RegisterType r) :
    s.regs r = v → s.setReg r v = s := by
  intro h
  obtain ⟨regs, mem, dev⟩ := s
  show ExecSt.mk (regs.set r v) mem dev = ExecSt.mk regs mem dev
  congr 1
  exact RegFile.set_eq_self regs r v h

/-! ## 1. THE `execEff` MIRRORS OF THE MRET CONE (trace `[]`) -/

/-- Rocq `exec_eff_long_csr_write_mstatus`. -/
theorem execEffLongCsrWriteMstatus (V : BitVec 64) (s : ExecSt) :
    execEff (long_csr_write_callback "mstatus" "mstatush" V) s = some ((), s, []) := by
  unfold long_csr_write_callback csr_name_write_callback
  exec_eff_run
  rfl

/-- Rocq `exec_eff_set_next_pc` (duplicated name). -/
theorem WeakLeafMret.execEffSetNextPc (target : BitVec 64) (s : ExecSt) :
    execEff (set_next_pc target) s = some ((), s.setReg .nextPC target, []) := by
  unfold set_next_pc
  exec_eff_run [execEffBranchAnnounce]

/-- Rocq `exec_eff_get_xLPE_S`: one `menvcfg` read. -/
theorem execEffGetXLPES (sz : ExecSt) :
    _get_MEnvcfg_LPE (sz.regs .menvcfg) = 0#1 →
    execEff (get_xLPE .Supervisor) sz = some (false, sz, []) := by
  intro hL
  unfold get_xLPE
  exec_eff_run [hL]
  rfl

/-- Rocq `exec_eff_execute_MRET` (section `ExecEffMRET`; deviations 2, 3). -/
theorem execEffExecuteMRET (s : ExecSt) (newpriv : Privilege) (lpe : Bool)
    (Hpriv : s.regs .cur_privilege = .Machine)
    (Hmu : (_get_Misa_U (s.regs .misa) == 1#1) = true)
    (Hmc : (_get_Misa_C (s.regs .misa) == 1#1) = true)
    (Hnp : privLevel_bits_forwards (_get_Mstatus_MPP (WeakLeafMret.cms2 (s.regs .mstatus)), 0#1) =
      pure newpriv)
    (Hnpm : bne newpriv .Machine = true)
    (Hlpe : execEff (get_xLPE newpriv)
      ((((((s.setReg .mstatus (WeakLeafMret.cms1 (s.regs .mstatus))).setReg .mstatus
        (WeakLeafMret.cms2 (s.regs .mstatus))).setReg .cur_privilege newpriv).setReg .mstatus
        (WeakLeafMret.cms3 (s.regs .mstatus))).setReg .mstatus
        (WeakLeafMret.cms4 (s.regs .mstatus))).setReg .mstatus (WeakLeafMret.cms5 (s.regs .mstatus))) =
      some (lpe,
        ((((((s.setReg .mstatus (WeakLeafMret.cms1 (s.regs .mstatus))).setReg .mstatus
          (WeakLeafMret.cms2 (s.regs .mstatus))).setReg .cur_privilege newpriv).setReg .mstatus
          (WeakLeafMret.cms3 (s.regs .mstatus))).setReg .mstatus
          (WeakLeafMret.cms4 (s.regs .mstatus))).setReg .mstatus (WeakLeafMret.cms5 (s.regs .mstatus))),
        [])) :
    execEff (execute (.MRET ())) s =
      some (RETIRE_SUCCESS,
        (((((((s.setReg .mstatus (WeakLeafMret.cms1 (s.regs .mstatus))).setReg .mstatus
          (WeakLeafMret.cms2 (s.regs .mstatus))).setReg .cur_privilege newpriv).setReg .mstatus
          (WeakLeafMret.cms3 (s.regs .mstatus))).setReg .mstatus
          (WeakLeafMret.cms4 (s.regs .mstatus))).setReg .mstatus
          (WeakLeafMret.cms5 (s.regs .mstatus))).setReg .elp
          (if lpe then _get_Mstatus_MPELP (WeakLeafMret.cms4 (s.regs .mstatus))
           else landing_pad_bits_backwards .NO_LP_EXPECTED)).setReg .nextPC
          (WeakLeafMret.retPc (s.regs .mepc)),
        []) := by
  show execEff (execute_MRET ()) s = _
  unfold execute_MRET
  cases lpe <;>
  · simp (config := { decide := true })
      (disch := first
        | decide
        | (simp (disch := decide) only [ExecSt.setReg_regs, RegFile.set_same, RegFile.set_other, Hmu,
            Hmc]; done))
      only [execEffBindEq, readReg, writeReg, PreSail.readReg, PreSail.writeReg, PreSail.emit, execEff,
        effThen, execEffReturnm, ↓reduceIte, ExecSt.setReg_regs, RegFile.set_same, RegFile.set_other,
        Hpriv, Hnp, Hnpm, Hlpe, execEffCurrentlyEnabledU, execEffCurrentlyEnabledZca,
        execEffHartSupportsZicfilp, execEffLongCsrWriteMstatus, WeakLeafMret.execEffSetNextPc,
        prepare_xret_target, get_xepc, align_pc, zicfilp_restore_elp_on_xret, WeakLeafMret.cms1Fold,
        WeakLeafMret.cms2Fold, WeakLeafMret.cms3Fold, WeakLeafMret.cms4Fold, WeakLeafMret.cms5Fold,
        WeakLeafMret.retPcFold, List.append_nil]

/-! ## 2. The successor register frame for MRET -/

/-- Rocq `mret_sexec_facts`: TEN `setReg`s deep; none of the written registers
is `hart_state` or `minstret_increment`. -/
theorem mretSexecFacts (s0 : ExecSt) (b : Bool) (npc npc2 : BitVec 64) (v1 v2 v3 v4 v5 : BitVec 64)
    (p : Privilege) (ev : RegisterType .elp) :
    let sExec := (((((((((s0.setReg .minstret_increment b).setReg .nextPC npc).setReg .mstatus v1).setReg
      .mstatus v2).setReg .cur_privilege p).setReg .mstatus v3).setReg .mstatus v4).setReg .mstatus
      v5).setReg .elp ev).setReg .nextPC npc2
    sExec.regs .hart_state = s0.regs .hart_state ∧
    sExec.regs .minstret_increment = b ∧
    sExec.mem = s0.mem ∧
    sExec.dev = s0.dev ∧
    sExec.regs .nextPC = npc2 := by
  intro sExec
  refine ⟨?_, ?_, rfl, rfl, ?_⟩
  · simp (disch := decide) only [sExec, ExecSt.setReg_regs, RegFile.set_other]
  · simp (disch := decide) only [sExec, ExecSt.setReg_regs, RegFile.set_other, RegFile.set_same]
  · simp only [sExec, ExecSt.setReg_regs, RegFile.set_same]

/-- The MRET run at ANY state carrying the funnel's two pre-writes (Lean-only;
Rocq's in-proof `Hc` and flat-run blocks, deviation 5). -/
theorem WeakLeafMret.execEffMretAt (s0 : ExecSt) (b : Bool) (pc : BitVec 64) (newpriv : Privilege)
    (ms_cur mepc0 menvcfg1 : BitVec 64) :
    s0.regs .cur_privilege = .Machine →
    s0.regs .misa = misaC →
    s0.regs .mstatus = ms_cur →
    s0.regs .mepc = mepc0 →
    s0.regs .menvcfg = menvcfg1 →
    privLevel_bits_forwards (_get_Mstatus_MPP (WeakLeafMret.cms2 ms_cur), 0#1) = pure newpriv →
    newpriv = .Supervisor →
    _get_MEnvcfg_LPE menvcfg1 = 0#1 →
    execEff (execute (.MRET ())) ((s0.setReg .minstret_increment b).setReg .nextPC (BitVec.addInt pc 4)) =
      some (RETIRE_SUCCESS,
        (((((((((s0.setReg .minstret_increment b).setReg .nextPC (BitVec.addInt pc 4)).setReg .mstatus
          (WeakLeafMret.cms1 ms_cur)).setReg .mstatus (WeakLeafMret.cms2 ms_cur)).setReg .cur_privilege
          newpriv).setReg .mstatus (WeakLeafMret.cms3 ms_cur)).setReg .mstatus
          (WeakLeafMret.cms4 ms_cur)).setReg .mstatus (WeakLeafMret.cms5 ms_cur)).setReg .elp
          (landing_pad_bits_backwards .NO_LP_EXPECTED)).setReg .nextPC (WeakLeafMret.retPc mepc0),
        []) := by
  intro hpriv hmisa hms hmepc hmenv hnp hsup hlpe0
  subst hsup
  have hprivB : ((s0.setReg .minstret_increment b).setReg .nextPC (BitVec.addInt pc 4)).regs
      .cur_privilege = .Machine := by
    leaf_peel .cur_privilege; exact hpriv
  have hmisaB : ((s0.setReg .minstret_increment b).setReg .nextPC (BitVec.addInt pc 4)).regs
      .misa = misaC := by
    leaf_peel .misa; exact hmisa
  have hmsB : ((s0.setReg .minstret_increment b).setReg .nextPC (BitVec.addInt pc 4)).regs
      .mstatus = ms_cur := by
    leaf_peel .mstatus; exact hms
  have hmepcB : ((s0.setReg .minstret_increment b).setReg .nextPC (BitVec.addInt pc 4)).regs
      .mepc = mepc0 := by
    leaf_peel .mepc; exact hmepc
  have hmu : (_get_Misa_U (((s0.setReg .minstret_increment b).setReg .nextPC (BitVec.addInt pc 4)).regs
      .misa) == 1#1) = true := by
    rw [hmisaB]; decide
  have hmc : (_get_Misa_C (((s0.setReg .minstret_increment b).setReg .nextPC (BitVec.addInt pc 4)).regs
      .misa) == 1#1) = true := by
    rw [hmisaB]; decide
  have hnpB : privLevel_bits_forwards (_get_Mstatus_MPP (WeakLeafMret.cms2
      (((s0.setReg .minstret_increment b).setReg .nextPC (BitVec.addInt pc 4)).regs .mstatus)), 0#1) =
      pure Privilege.Supervisor := by
    rw [hmsB]; exact hnp
  have h := execEffExecuteMRET ((s0.setReg .minstret_increment b).setReg .nextPC (BitVec.addInt pc 4))
    .Supervisor false hprivB hmu hmc hnpB (by decide) (execEffGetXLPES _ (by
      simp (disch := decide) only [ExecSt.setReg_regs, RegFile.set_other]
      rw [hmenv]; exact hlpe0))
  rw [hmsB, hmepcB] at h
  exact h

/-! ## 3. THE LEAF -/

section leaf
variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [WeakGS GF]

/-- Rocq `wwp_mret_leaf` (deviations 1, 4, 5). -/
theorem wwpMretLeaf (gen : Nat) (cpu : CPU) (al4 : Bool) (pc : BitVec 64) (w : BitVec 32)
    (newpriv : Privilege) (ms_cur mepc0 menvcfg1 npc0 : BitVec 64)
    (pmpcfg0 : RegisterType .pmpcfg_n) (D : Register → Bool) (dst : ExecSt) (ws : Wstate) :
    gen = 0 →
    pmpAllowsAll pmpcfg0 →
    is_aligned_vaddr (.Virtaddr pc) 2 = true →
    is_aligned_vaddr (.Virtaddr pc) 4 = al4 →
    (_get_Mstatus_MIE ms_cur == 1#1) = false →
    (_get_Mstatus_MPRV ms_cur == 1#1) = false →
    privLevel_bits_forwards (_get_Mstatus_MPP (WeakLeafMret.cms2 ms_cur), 0#1) = pure newpriv →
    newpriv = .Supervisor →
    _get_MEnvcfg_LPE menvcfg1 = 0#1 →
    -- the decode, in the two shapes its two consumers ask for
    (∀ t : ExecSt,
      privMSU (t.regs .cur_privilege) = true →
      (_get_Misa_C (t.regs .misa) == 1#1) = true →
      (_get_Misa_A (t.regs .misa) == 1#1) = true →
      t.regs .misa = misaC →
      cfgOk t →
      exec (decodeFetch (.F_Base w)) t = some (.MRET (), t)) →
    (∀ rs : RegFile,
      rs .cur_privilege = .Machine →
      rs .misa = misaC →
      rs .mseccfg = 0#64 →
      ∀ r, D r = true → rs r = dst.regs r) →
    D .minstret_increment = false →
    goodb0 D (ext_decode w) dst = true →
    exec (ext_decode w) dst = some (.MRET (), dst) →
    hwConfig (GF := GF) cpu ⊢
      clockCells cpu -∗
      Register.hart_state ↦ᵣ[cpu] HartState.HART_ACTIVE () -∗
      Register.cur_privilege ↦ᵣ[cpu] Privilege.Machine -∗
      Register.mstatus ↦ᵣ[cpu] ms_cur -∗
      Register.pmpcfg_n ↦ᵣ[cpu] pmpcfg0 -∗
      Register.PC ↦ᵣ[cpu] pc -∗
      Register.nextPC ↦ᵣ[cpu] npc0 -∗
      Register.menvcfg ↦ᵣ[cpu] menvcfg1 -∗
      Register.mepc ↦ᵣ[cpu] mepc0 -∗
      winstrBytes (GF := GF) pc (.F_Base w) -∗
      hartWs (GF := GF) cpu ws -∗
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
        wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu)) -∗
      wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu) := by
  intro hgid hpmp hal2 hal4 hmIE hmprv hnp hsup hlpe0 hdecf hagree hDmi hgood hdec
  iintro #Hhw Hclk Hhs Hpriv Hms0 Hpmpc Hpc Hnpc Hmenv Hmepc #Hbs Hhws Hcont
  ihave %haccpc := winstrBytesAccWf pc (.F_Base w) $$ Hbs
  have hacc0 : accWf pc 0 := by unfold accWf at haccpc ⊢; omega
  ihave %hnotRVC := WeakLeafLw4.winstrBytesNotRVC pc w $$ Hbs
  have hdecW : winstrDec (.F_Base w) (.MRET ()) := by
    intro t h1 h2 h3 h4 h5
    simp only [fetchIsRvc, Bool.false_eq_true, ↓reduceIte]
    exact hdecf t h1 h2 h3 h4 h5
  ihave #Hwi := winstrIntro (GF := GF) pc false (.MRET ()) (.F_Base w)
    (by first | rfl | decide) rfl hdecW $$ Hbs
  -- the funnel: certificate = nowrite at the fetch-only trace
  iapply wwpInstrConfig gen cpu pc false (.MRET ()) pmpcfg0 ms_cur
    (wPEff (some cpu.val) (regonlyEs al4 pc)) (wQFr wQPure (some cpu.val) (regonlyEs al4 pc))
    hgid haccpc hpmp hmIE hmprv (wstepCertFr _ _ _ _ (wcertRegonly al4 cpu.val pc))
    $$ Hhw Hclk Hhs Hpriv Hms0 Hpmpc Hpc Hwi
  unfold wwpCbConfig
  iintro %σ %b %mt %ip %Lpc0 %hcfg %Lms0 Hpriv Hms Hpmpc Hlat Hreg Hnorg Hti Hip
  unfold wmstateNorg
  icases Hnorg with ⟨%hbnd, %hnv, %hwf, Hdev, Hlogauth, Hwsauth⟩
  ihave ⟨%hws, Hwsauth, Hhws⟩ := persistent_entails_right (hartWsAgree cpu σ.wmWs ws) $$ [Hwsauth Hhws]
  · iframe Hwsauth Hhws
  subst hws
  obtain ⟨Lpriv, Lhart, Lmisa, Lsec, Lpmpc, Lpma, Lhtif, LmisaS, LmIE, Lmprv, Lpmm, Lelp⟩ := hcfg
  icases keepPure (winstrFlat σ pc (.F_Base w) hwf) $$ Hlat Hbs with ⟨%hfok, Hlat, -⟩
  icases keepPure (winstrTextPinned σ pc (.F_Base w) hwf) $$ Hlat Hbs with ⟨%htp, Hlat, -⟩
  icases keepPure (winstrUnwritten σ pc (.F_Base w) hwf) $$ Hlat Hbs with ⟨%hunw, Hlat, -⟩
  obtain ⟨-, hrampc, w', ⟨hww, -⟩, htext⟩ := hfok
  subst hww
  have LmisaC : (_get_Misa_C (σ.wmRegs .misa) == 1#1) = true := by rw [Lmisa]; decide
  -- the elp value MRET restores is the value elp ALREADY holds
  have Lelp0 := WeakLeafMret.mword1NotLp _ Lelp
  -- the two cells the funnel does not read: menvcfg and mepc
  icases keepPure (wand_intro (reg_valid cpu _ .menvcfg _ menvcfg1)) $$ Hreg Hmenv
    with ⟨%Lmenv_a, Hreg, Hmenv⟩
  have Lmenv : σ.wmRegs .menvcfg = menvcfg1 := (regAtFlat .menvcfg σ b (by decide)).symm.trans Lmenv_a
  icases keepPure (wand_intro (reg_valid cpu _ .mepc _ mepc0)) $$ Hreg Hmepc
    with ⟨%Lmepc_a, Hreg, Hmepc⟩
  have Lmepc : σ.wmRegs .mepc = mepc0 := (regAtFlat .mepc σ b (by decide)).symm.trans Lmepc_a
  -- ---- premise (c): the execute mirror, at the CONFINED state ----
  have hc : ∀ b' : Bool, ∃ sExec : ExecSt,
      execEff (execute (.MRET ()))
        (((⟨σ.wmRegs, wmemRestrict σ (wwin pc pc 0), σ.wmDev⟩ : ExecSt).setReg .minstret_increment
          b').setReg .nextPC (BitVec.addInt pc 4)) = some (.Retire_Success (), sExec, []) ∧
      sExec.regs .hart_state = .HART_ACTIVE () ∧
      sExec.regs .minstret_increment = b' ∧
      bmDomSub sExec.mem (wwin pc pc 0) := by
    intro b'
    have hrun := WeakLeafMret.execEffMretAt ⟨σ.wmRegs, wmemRestrict σ (wwin pc pc 0), σ.wmDev⟩ b' pc
      newpriv ms_cur mepc0 menvcfg1 Lpriv Lmisa Lms0 Lmepc Lmenv hnp hsup hlpe0
    have hF := mretSexecFacts ⟨σ.wmRegs, wmemRestrict σ (wwin pc pc 0), σ.wmDev⟩ b'
      (BitVec.addInt pc 4) (WeakLeafMret.retPc mepc0) (WeakLeafMret.cms1 ms_cur)
      (WeakLeafMret.cms2 ms_cur) (WeakLeafMret.cms3 ms_cur) (WeakLeafMret.cms4 ms_cur)
      (WeakLeafMret.cms5 ms_cur) newpriv (landing_pad_bits_backwards .NO_LP_EXPECTED)
    refine ⟨_, hrun, ?_, hF.2.1, ?_⟩
    · rw [hF.1]; exact Lhart
    · rw [hF.2.2.1]; exact wmemRestrictDom σ _
  -- ---- the O2 fetch pin ----
  have hfp : fetchPin σ (regonlyEs al4 pc) := by
    refine ⟨fun ak pa n hin _ j hj => ?_, ?_⟩
    · obtain ⟨j', hj', heq⟩ := weffsTouchRegonly al4 pc (WeakInterp.accAddr pa j) haccpc
        ⟨_, hin, j, hj, rfl⟩
      rw [heq]; exact (htp j' hj').2
    · cases al4 <;> simp [regonlyEs, fetchFresh, weffWrites]
  -- ---- the certificate's precondition ----
  have HP : wPEff (some cpu.val) (regonlyEs al4 pc) σ :=
    wPEffOfLeafRegonly al4 cpu.val σ (wwin pc pc 0) pc w (.MRET ()) D dst hwf
      (wwinNonzero pc pc 0 (fun j hj => WeakLeafWin.inRamByte pc 4 j hrampc hj) (win0Absurd _))
      (wwinPinned σ pc pc 0 haccpc hacc0 (fun j hj => (htp j hj).1) (win0Absurd _))
      hfp Lpc0 Lpriv (by rw [Lpmpc]; exact hpmp) Lpma Lhtif Lhart LmisaS LmisaC LmIE Lelp hal2 hal4
      hrampc (wwinConfText σ pc pc 0 w htext) hnotRVC (hagree _ Lpriv Lmisa Lsec) hDmi hgood hdec
      (by first | rfl | decide) hc
  -- ---- the run at the FLAT state ----
  have hexf := WeakLeafMret.execEffMretAt (wflatSt σ) b pc newpriv ms_cur mepc0 menvcfg1 Lpriv Lmisa
    Lms0 Lmepc Lmenv hnp hsup hlpe0
  have hG := mretSexecFacts (wflatSt σ) b (BitVec.addInt pc 4) (WeakLeafMret.retPc mepc0)
    (WeakLeafMret.cms1 ms_cur) (WeakLeafMret.cms2 ms_cur) (WeakLeafMret.cms3 ms_cur)
    (WeakLeafMret.cms4 ms_cur) (WeakLeafMret.cms5 ms_cur) newpriv
    (landing_pad_bits_backwards .NO_LP_EXPECTED)
  -- ---- the ghost writes mirroring the physical tower ----
  imod (wand_intro (reg_update cpu _ .nextPC npc0 (BitVec.addInt pc 4))) $$ Hreg Hnpc with ⟨Hreg, Hnpc⟩
  imod (wand_intro (reg_update cpu _ .mstatus ms_cur (WeakLeafMret.cms1 ms_cur))) $$ Hreg Hms
    with ⟨Hreg, Hms⟩
  imod (wand_intro (reg_update cpu _ .mstatus (WeakLeafMret.cms1 ms_cur) (WeakLeafMret.cms2 ms_cur)))
    $$ Hreg Hms with ⟨Hreg, Hms⟩
  imod (wand_intro (reg_update cpu _ .cur_privilege Privilege.Machine newpriv)) $$ Hreg Hpriv
    with ⟨Hreg, Hpriv⟩
  imod (wand_intro (reg_update cpu _ .mstatus (WeakLeafMret.cms2 ms_cur) (WeakLeafMret.cms3 ms_cur)))
    $$ Hreg Hms with ⟨Hreg, Hms⟩
  imod (wand_intro (reg_update cpu _ .mstatus (WeakLeafMret.cms3 ms_cur) (WeakLeafMret.cms4 ms_cur)))
    $$ Hreg Hms with ⟨Hreg, Hms⟩
  imod (wand_intro (reg_update cpu _ .mstatus (WeakLeafMret.cms4 ms_cur) (WeakLeafMret.cms5 ms_cur)))
    $$ Hreg Hms with ⟨Hreg, Hms⟩
  -- elp: a VALUE-PRESERVING physical write, so no ghost update (deviation 5)
  imod (wand_intro (reg_update cpu _ .nextPC (BitVec.addInt pc 4) (WeakLeafMret.retPc mepc0)))
    $$ Hreg Hnpc with ⟨Hreg, Hnpc⟩
  iapply fupd_mask_intro LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro; exact HP
  iexists (((((((((((wflatSt σ).setReg .minstret_increment b).setReg .nextPC (BitVec.addInt pc 4)).setReg
    .mstatus (WeakLeafMret.cms1 ms_cur)).setReg .mstatus (WeakLeafMret.cms2 ms_cur)).setReg
    .cur_privilege newpriv).setReg .mstatus (WeakLeafMret.cms3 ms_cur)).setReg .mstatus
    (WeakLeafMret.cms4 ms_cur)).setReg .mstatus (WeakLeafMret.cms5 ms_cur)).setReg .elp
    (landing_pad_bits_backwards .NO_LP_EXPECTED)).setReg .nextPC (WeakLeafMret.retPc mepc0))
  isplitr
  · ipureintro; exact execEffExec _ _ _ _ _ hexf
  isplitl [Hreg]
  · rw [WeakLeafMret.setRegSameVal _ .elp (landing_pad_bits_backwards .NO_LP_EXPECTED) (by
      simp (disch := decide) only [ExecSt.setReg_regs, RegFile.set_other]
      exact Lelp0)]
    simp only [ExecSt.setReg_regs]
    iexact Hreg
  isplitl [Hti Hip]
  · iexists mt, ip
    iframe Hti Hip
  inext
  iintro %tick %σ' %t %hstep %hdevt0 %hpost %hQ Hhs Hclk' Hpc'
  obtain ⟨hregs, hdevs, hmems, himgs, hlogs, hwsle, hwf', hbnd'⟩ := hpost
  obtain ⟨⟨hQi, hQl, -⟩, hQeff⟩ := hQ
  have hdevt : t.dev = σ.wmDev := by rw [hdevt0, hG.2.2.2.1]; rfl
  imod hartWsUpdate cpu σ.wmWs σ.wmWs σ'.wmWs $$ [$Hwsauth $Hhws] with ⟨Hwsauth, Hhws⟩
  imod Hclose
  rw [hG.2.2.2.2]
  imodintro
  isplitl [Hlat]
  · rw [hQi, hQl]; iexact Hlat
  isplitl [Hdev Hlogauth Hwsauth]
  · isplitr
    · ipureintro; exact hbnd'
    isplitr
    · ipureintro
      apply nvHartOfWQEffUnwritten cpu σ σ' _ hQeff hnv
      intro a ha
      obtain ⟨j, hj, rfl⟩ := weffsTouchRegonly al4 pc a haccpc ha
      rw [hQl]
      exact hunw j hj
    isplitr
    · ipureintro; exact hwf'
    rw [hdevs, hdevt, hQl]
    iframe Hdev Hlogauth Hwsauth
  iapply Hcont $$ %σ'.wmWs %hwsle Hhs Hclk' Hpriv Hms Hpmpc Hmenv Hmepc [Hpc' Hnpc] Hhws
  unfold pcIs
  iframe Hpc' Hnpc

end leaf

end Weak
