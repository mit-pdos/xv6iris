/-
Weak: **the weak `csrr a5, time` leaf** (M4, start/timerinit) -- the CSR-READ
counterpart of the register-only csrw leaves.

Rocq: `iris/WeakLeafCsrrTime.v` @ xxvzwolszwmp.

The Rocq header, in substance.  The weak twin of `WpGprCsrrB.wp_csrr_time_gpr`.
The leaf owns NO `mtime` cell in Rocq (it lives in `clock_inv`) and opens no
invariant: the `execEff` witness reads `mtime` straight off the step state σ,
and the read value `tv` is ∀-quantified in the continuation, instantiated with
`wtimeVal σ` -- the `mtime` lookup at the callback's own σ, peeled past the
funnel's two pre-writes so that the CONFINED-state and the FLAT-state
`execute` instantiations produce the SAME value.
* §1 the `execEff` mirror of the csrr-time `execute` cone, at trace `[]`: the
  Zicntr enablement chain, the counter gate at Machine, the `read_CSR`
  dispatch, the CSR-READ check kit (csr-generic), time's accessibility /
  check / callback, the x0 source read, the csrr SPINE
  `execEffCsrrReadStepP` (csr-generic, privilege-generic) and the end-to-end
  `execEffExecuteCsrrTimeGpr`.
* §1b `wtimeVal` / `timeRdvalPrewrite`: the `mtime` peel past the funnel's
  `minstret_increment` and `nextPC` pre-writes.
* §2 the leaf `wwpCsrrTimeLeaf`, alignment-generic (`WeakLeafRegOnly`'s
  `regonlyEs al4 pc` / `wcertRegonly` / `wPEffOfLeafRegonly`), with the single
  DESTINATION GPR cell and the successor frame `WeakLeafWin.loadSexecFacts`.

**Deviations from Rocq.**
1. VOCABULARY: the `Weak/ExecSC*.lean` conventions (`register_lookup r
   s.(sregs)` ↦ `s.regs r`, `mword n` ↦ `BitVec n`, `set_reg` ↦
   `ExecSt.setReg`, `subrange_vec_dec x 63 0` ↦ `Sail.BitVec.extractLsb x 63 0`,
   `add_vec_int` ↦ `BitVec.addInt`, `uint x` ↦ `x.toNat`, `M X` ↦ `SailM X`,
   `CSR_Check_OK tt` ↦ `.CSR_Check_OK ()`); `csr_time` is the literal
   `0xC01#12`; the GPR write `set_reg s (R_bitvector_64 (gpr_of_Z (uint rd)))
   (regval_into_reg x)` is `s.setGpr rd x` (equal under the kept premise
   `rd.toNat ≠ 0`); `time_rdval` (Rocq `WpGprCsrrB`, no Lean twin) is the
   Lean-only `WeakLeafCsrrTime.timeRdval`.
2. §1a: `hartSupports` is pure in Lean (`WeakLeafEffCommon` deviation 9), so
   `exec_eff_hartSupports_Zicntr` is `hartSupports .Ext_Zicntr = true`; Lean's
   `currentlyEnabled` has no fuel/measure, so the `Zwf_guarded` unfolding is
   gone.
3. §1b: Lean's `read_CSR` is a `match` on the CSR number, not an `if` chain:
   the Ltac `drive_csr_eff` is a macro that rewrites with MachCSL's
   `read_CSR` arm equations (`read_CSR_time`, …, the `sail_facts` set) and
   steps the result with `exec_eff_steps`.
4. §1c/§1e: Lean's `check_CSR` has no `and_boolM`/`returnM` binds
   (`WeakLeafRegOnly` deviation 4); the `0x344`/`0x144` tests are
   `(csr == 0x344#12) = false` (as `WeakLeafCsrw` deviation 4); Lean's
   `doCSR` has no `generic_neq`/`generic_eq` wrappers.  The Rocq statement's
   `zreg` source is kept.
5. §1d: `is_CSR_accessible csr_time Machine CSRRead` is MachCSL's
   `is_CSR_accessible_time` (Lean: `if (← currentlyEnabled Ext_Zicntr) then
   counter_enabled 1 p else pure false`, Rocq's `and_boolM`).
6. `exec_eff_execute_csrr_time_gpr`: the `uint rd <> 0` premise is kept but not
   used (Lean's `execEffWXBitsGpr` is unconditional).
7. THE LEAF (owner decision Q3, `Weak/WeakFunnel.lean` deviation 7): Rocq
   `mmode_config (DfracOwn q) -∗ pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0` ↦ `mConf cpu
   dq c ∗ clockCells cpu` (any `dq`; `pmpcfg0 := c.pmpcfg`, the premise
   `pmp_allows_all pmpcfg0` ↦ `pmpAllowsAll c.pmpcfg`, plus `MConf.mok c`); the
   continuation gets the same back.  In Lean `mtime` IS owned (inside
   `clockCells`); the funnel lends the leaf the `mtime`/`mip` cells and the leaf
   hands them straight back -- the read value is still `wtimeVal σ`, read off
   σ, so the continuation stays ∀-quantified over `tv` as in Rocq.
   `GenId`/`CpuId` are the explicit `gen`/`cpu`; `WWP Loop` ↦ `wwpTriv ⊤
   (WExpr.loop gen cpu)`; `pc_is` ↦ `MachCSL.pcIs`; `hart_ws cpu_id` ↦
   `hartWs cpu`; the destination cell `R_bitvector_64 (gpr_of_Z (uint rd)) ↦ᵣ x`
   is `MachCSL.gpr cpu rd (DFrac.own 1) x` (via `WeakLeafLw4.gprUpdate`); the
   decode premises are over the funnel's vocabulary (`privMSU`, `misaC`,
   `cfgOk`, `decodeFetch`; the agreement premise quantifies over `RegFile`,
   `mword_of_int 0` ↦ `0#64`).  O2: the fetch pin `fetchPin σ (regonlyEs al4
   pc)` is discharged from `winstrTextPinned` (`fetchPinOfText`, with the
   Lean-only `WeakLeafCsrrTime.fetchInWindowRegonly`/`fetchFreshRegonly`).
8. Rocq §3's `Print Assumptions` commands are not declarations.

**Rocq → Lean name map.**  `exec_eff_hartSupports_Zicntr`
`execEffHartSupportsZicntr`, `exec_eff_currentlyEnabled_Zicntr`
`execEffCurrentlyEnabledZicntr`, `exec_eff_counter_enabled_machine`
`execEffCounterEnabledMachine`, `drive_csr_eff` (Ltac) `drive_csr_eff` (macro),
`exec_eff_read_CSR_time` `execEffReadCSRTime`, `exec_eff_check_CSR_read_p`
`execEffCheckCSRReadP`, `exec_eff_check_CSR_result_read_p`
`execEffCheckCSRResultReadP`, `exec_eff_is_CSR_accessible_time`
`execEffIsCSRAccessibleTime`, `exec_eff_check_CSR_result_time`
`execEffCheckCSRResultTime`, `exec_eff_csr_id_read_callback_time`
`execEffCsrIdReadCallbackTime`, `exec_eff_rX_bits_x0`
`WeakLeafCsrrTime.execEffRXBitsX0` (duplicated name), `exec_eff_csrr_read_step_p`
`execEffCsrrReadStepP`, `exec_eff_execute_csrr_time_gpr`
`execEffExecuteCsrrTimeGpr`, `wtime_val` `wtimeVal`, `time_rdval_prewrite`
`timeRdvalPrewrite`, `wwp_csrr_time_leaf` `wwpCsrrTimeLeaf`.  Lean-only
(file-qualified): `WeakLeafCsrrTime.timeRdval` (deviation 1),
`WeakLeafCsrrTime.execEffCsrrTimeAt` (the leaf's confined/flat run, one lemma),
`WeakLeafCsrrTime.fetchInWindowRegonly`, `WeakLeafCsrrTime.fetchFreshRegonly`.

**Dropped:** nothing (Rocq 1 definition + 14 lemmas + 1 Ltac; Lean 1 + 14 + the
macro, plus 4 Lean-only).
-/
import Weak.WeakLeafRegOnly
import Weak.WeakLeafLw4
import Weak.WeakLeafWin
import MachCSL.WpCsrFacts
import MachCSL.Gpr
import MachCSL.Boot

namespace Weak

open Iris Iris.BI Iris.BI.MonPred Iris.ProofMode Iris.Std
open MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D LeanRV64D.Functions

/-! ## 1. THE `execEff` MIRROR OF THE csrr-time CONE (trace `[]`) -/

/-! ### 1a. The Zicntr enablement chain -/

/-- Rocq `exec_eff_hartSupports_Zicntr` (deviation 2). -/
theorem execEffHartSupportsZicntr : hartSupports .Ext_Zicntr = true := by decide +kernel

/-- Rocq `exec_eff_currentlyEnabled_Zicntr`. -/
theorem execEffCurrentlyEnabledZicntr (s : ExecSt) :
    execEff (currentlyEnabled .Ext_Zicntr) s = some (true, s, []) := by
  rw [currentlyEnabled]
  simp only [execEffHartSupportsZicntr, ↓reduceIte, execEffRecCEZicsrAny]

/-- Rocq `exec_eff_counter_enabled_machine`: at Machine the counter gate is
open (both counter-enable registers are read, register-only). -/
theorem execEffCounterEnabledMachine (index : Nat) (s : ExecSt) :
    execEff (counter_enabled index .Machine) s = some (true, s, []) := by
  unfold counter_enabled feature_enabled_for_priv_bool feature_enabled_for_priv
  exec_eff_steps
  try rfl

/-! ### 1b. The `read_CSR` dispatch, at `execEff` (deviation 3) -/

/-- Rocq's Ltac `drive_csr_eff` (deviation 3). -/
macro "drive_csr_eff" : tactic =>
  `(tactic| (simp only [sail_facts]; exec_eff_steps))

/-- Rocq `exec_eff_read_CSR_time`. -/
theorem execEffReadCSRTime (s : ExecSt) :
    execEff (read_CSR 0xC01#12) s = some (Sail.BitVec.extractLsb (s.regs .mtime) 63 0, s, []) := by
  drive_csr_eff

/-! ### 1c. The CSR-READ check kit, csr-generic -/

/-- Rocq `exec_eff_check_CSR_read_p` (deviation 4). -/
theorem execEffCheckCSRReadP (p : Privilege) (csr : BitVec 12) (s : ExecSt) :
    execEff (check_CSR_priv csr p) s = some (true, s, []) →
    check_CSR_access csr .CSRRead = true →
    execEff (is_CSR_accessible csr p .CSRRead) s = some (true, s, []) →
    execEff (stateen_allows_CSR_access csr p .CSRRead) s = some (true, s, []) →
    execEff (check_CSR csr p .CSRRead) s = some (true, s, []) := by
  intro hpriv hca hacc hst
  unfold check_CSR
  rw [execEffBindNil _ _ _ _ _ hpriv]
  simp only [↓reduceIte, hca]
  rw [execEffBindNil _ _ _ _ _ hacc]
  simpa only [↓reduceIte] using hst

/-- Rocq `exec_eff_check_CSR_result_read_p`. -/
theorem execEffCheckCSRResultReadP (p : Privilege) (csr : BitVec 12) (s : ExecSt) :
    execEff (check_CSR csr p .CSRRead) s = some (true, s, []) →
    execEff (check_CSR_result csr p .CSRRead) s = some (.CSR_Check_OK (), s, []) := by
  intro hcc
  unfold check_CSR_result
  rw [execEffBindNil _ _ _ _ _ hcc]
  rfl

/-! ### 1d. time's accessibility / check / callback -/

/-- Rocq `exec_eff_is_CSR_accessible_time` (deviation 5). -/
theorem execEffIsCSRAccessibleTime (s : ExecSt) :
    execEff (is_CSR_accessible 0xC01#12 .Machine .CSRRead) s = some (true, s, []) := by
  rw [is_CSR_accessible_time]
  rw [execEffBindNil _ _ _ _ _ (execEffCurrentlyEnabledZicntr s)]
  simp only [↓reduceIte]
  exact execEffCounterEnabledMachine 1 s

/-- Rocq `exec_eff_check_CSR_result_time`. -/
theorem execEffCheckCSRResultTime (s : ExecSt) :
    execEff (check_CSR_result 0xC01#12 .Machine .CSRRead) s = some (.CSR_Check_OK (), s, []) := by
  apply execEffCheckCSRResultReadP
  apply execEffCheckCSRReadP
  · have h : check_CSR_priv 0xC01#12 .Machine = (pure true : SailM Bool) := by csr_dispatch_eq
    rw [h]
    rfl
  · first | rfl | decide
  · exact execEffIsCSRAccessibleTime s
  · rw [stateen_time]
    rfl

/-- Rocq `exec_eff_csr_id_read_callback_time`. -/
theorem execEffCsrIdReadCallbackTime (s : ExecSt) (d : BitVec 64) :
    execEff (csr_id_read_callback 0xC01#12 d) s = some ((), s, []) := rfl

/-- Rocq `exec_eff_rX_bits_x0`: the x0 source read, derived from
`execEffRXBitsGpr`. -/
theorem WeakLeafCsrrTime.execEffRXBitsX0 (i : BitVec 5) (s : ExecSt) :
    i.toNat = 0 → execEff (rX_bits (.Regidx i)) s = some (zero_reg, s, []) := by
  intro h
  have hi : i = 0#5 := BitVec.eq_of_toNat_eq (by simpa using h)
  subst hi
  rw [execEffRXBitsGpr]
  rfl

/-! ### 1e. The csrr SPINE (csr-generic, privilege-generic) -/

/-- Rocq `exec_eff_csrr_read_step_p` (deviation 4). -/
theorem execEffCsrrReadStepP (p : Privilege) (csr : BitVec 12) (rd : BitVec 5) (readval : BitVec 64)
    (s sW : ExecSt) :
    s.regs .cur_privilege = p →
    execEff (check_CSR_result csr p .CSRRead) s = some (.CSR_Check_OK (), s, []) →
    ext_check_CSR csr p .CSRRead = true →
    execEff (read_CSR csr) s = some (readval, s, []) →
    (csr == 0x344#12) = false →
    (csr == 0x144#12) = false →
    execEff (csr_id_read_callback csr readval) s = some ((), s, []) →
    execEff (wX_bits (.Regidx rd) readval) s = some ((), sW, []) →
    execEff (execute_CSRReg csr zreg (.Regidx rd) .CSRRS) s = some (RETIRE_SUCCESS, sW, []) := by
  intro hpriv hchk hext hread h344 h144 hcb hwx
  have h344' : csr ≠ 0x344#12 := by simpa using h344
  have h144' : csr ≠ 0x144#12 := by simpa using h144
  have hacc : ∀ x : Bool, csr_access_type .CSRRS x true = .CSRRead := by
    intro x; cases x <;> rfl
  have hz : (zreg == zreg) = true := rfl
  have hx0 : execEff (rX_bits zreg) s = some (zero_reg, s, []) :=
    WeakLeafCsrrTime.execEffRXBitsX0 0#5 s rfl
  unfold execute_CSRReg
  simp only [hz, hacc]
  rw [execEffBindNil _ _ _ _ _ hx0]
  unfold doCSR
  exec_eff_steps [hpriv, hchk, hext, Functions.not, hread, h344', h144', hcb, hwx]

/-! ### 1f. The end-to-end csrr-time `execute`, trace `[]` -/

/-- Lean-only (deviation 1): Rocq `WpGprCsrrB.time_rdval`. -/
def WeakLeafCsrrTime.timeRdval (s : ExecSt) : BitVec 64 :=
  Sail.BitVec.extractLsb (s.regs .mtime) 63 0

/-- Rocq `exec_eff_execute_csrr_time_gpr` (deviations 1, 6). -/
theorem execEffExecuteCsrrTimeGpr (rd : BitVec 5) (s : ExecSt) :
    rd.toNat ≠ 0 →
    s.regs .cur_privilege = .Machine →
    execEff (execute (.CSRReg (0xC01#12, zreg, .Regidx rd, .CSRRS))) s =
      some (RETIRE_SUCCESS, s.setGpr rd (WeakLeafCsrrTime.timeRdval s), []) := by
  intro _ hpriv
  show execEff (execute_CSRReg 0xC01#12 zreg (.Regidx rd) .CSRRS) s = _
  exact execEffCsrrReadStepP .Machine 0xC01#12 rd (WeakLeafCsrrTime.timeRdval s) s _ hpriv
    (execEffCheckCSRResultTime s) (by first | rfl | decide) (execEffReadCSRTime s)
    (by decide) (by decide) (execEffCsrIdReadCallbackTime s _) (execEffWXBitsGpr rd _ s)

/-! ## 1b. THE mtime PEEL -/

/-- Rocq `wtime_val`. -/
def wtimeVal (σ : Wmstate) : BitVec 64 := Sail.BitVec.extractLsb (σ.wmRegs .mtime) 63 0

/-- Rocq `time_rdval_prewrite`. -/
theorem timeRdvalPrewrite (σ : Wmstate) (s0 : ExecSt) (b : Bool) (npc : BitVec 64) :
    s0.regs = σ.wmRegs →
    WeakLeafCsrrTime.timeRdval ((s0.setReg .minstret_increment b).setReg .nextPC npc) = wtimeVal σ := by
  intro hs
  unfold WeakLeafCsrrTime.timeRdval wtimeVal
  rw [setLookupNe .mtime .nextPC _ _ (by decide), setLookupNe .mtime .minstret_increment _ _ (by decide),
    hs]

/-! ## 2. THE LEAF -/

/-- The csrr-time `execute` at a pre-written state (Lean-only; the shared core of
the leaf's confined and flat runs). -/
theorem WeakLeafCsrrTime.execEffCsrrTimeAt (σ : Wmstate) (s0 : ExecSt) (b : Bool) (x : BitVec 64)
    (rd : BitVec 5) (hrd : rd.toNat ≠ 0) (hpriv : s0.regs .cur_privilege = .Machine)
    (hs : s0.regs = σ.wmRegs) :
    execEff (execute (.CSRReg (0xC01#12, zreg, .Regidx rd, .CSRRS)))
        ((s0.setReg .minstret_increment b).setReg .nextPC x) =
      some (RETIRE_SUCCESS, ((s0.setReg .minstret_increment b).setReg .nextPC x).setGpr rd (wtimeVal σ),
        []) := by
  have hpriv' : ((s0.setReg .minstret_increment b).setReg .nextPC x).regs .cur_privilege = .Machine := by
    leaf_peel .cur_privilege; exact hpriv
  have h := execEffExecuteCsrrTimeGpr rd _ hrd hpriv'
  rw [timeRdvalPrewrite σ s0 b x hs] at h
  exact h

/-- The register-only fetch trace stays in the text window (Lean-only). -/
theorem WeakLeafCsrrTime.fetchInWindowRegonly (al4 : Bool) (pc : BitVec 64) (hacc : accWf pc 4) :
    fetchInWindow pc (regonlyEs al4 pc) := by
  intro ak pa n hin _ j hj
  exact weffsTouchRegonly al4 pc _ hacc ⟨_, hin, j, hj, rfl⟩

/-- The register-only fetch trace is fetch-fresh (Lean-only). -/
theorem WeakLeafCsrrTime.fetchFreshRegonly (al4 : Bool) (pc : BitVec 64) :
    fetchFresh (regonlyEs al4 pc) := by
  cases al4 <;> simp [regonlyEs, fetchFresh, weffWrites]

section leaf
variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [WeakGS GF]

/-- Rocq `wwp_csrr_time_leaf` (deviation 7). -/
theorem wwpCsrrTimeLeaf (gen : Nat) (cpu : CPU) (al4 : Bool) (pc : BitVec 64) (w : BitVec 32)
    (rd : BitVec 5) (rd0 npc0 : BitVec 64) (c : MConf) (dq : DFrac) (D : Register → Bool)
    (dst : ExecSt) (ws : Wstate) :
    gen = 0 →
    MConf.mok c →
    pmpAllowsAll c.pmpcfg →
    is_aligned_vaddr (.Virtaddr pc) 2 = true →
    is_aligned_vaddr (.Virtaddr pc) 4 = al4 →
    rd.toNat ≠ 0 →
    -- the decode, in the two shapes its two consumers ask for
    (∀ t : ExecSt,
      privMSU (t.regs .cur_privilege) = true →
      (_get_Misa_C (t.regs .misa) == 1#1) = true →
      (_get_Misa_A (t.regs .misa) == 1#1) = true →
      t.regs .misa = misaC →
      cfgOk t →
      exec (decodeFetch (.F_Base w)) t = some (.CSRReg (0xC01#12, zreg, .Regidx rd, .CSRRS), t)) →
    (∀ rs : RegFile,
      rs .cur_privilege = .Machine →
      rs .misa = misaC →
      rs .mseccfg = 0#64 →
      ∀ r, D r = true → rs r = dst.regs r) →
    D .minstret_increment = false →
    goodb0 D (ext_decode w) dst = true →
    exec (ext_decode w) dst = some (.CSRReg (0xC01#12, zreg, .Regidx rd, .CSRRS), dst) →
    mConf (GF := GF) cpu dq c ⊢
      clockCells cpu -∗
      Register.PC ↦ᵣ[cpu] pc -∗
      Register.nextPC ↦ᵣ[cpu] npc0 -∗
      gpr cpu rd (DFrac.own 1) rd0 -∗
      winstrBytes (GF := GF) pc (.F_Base w) -∗
      hartWs (GF := GF) cpu ws -∗
      (∀ (tv : BitVec 64) (ws' : Wstate),
        ⌜wsLe ws ws'⌝ -∗
        mConf cpu dq c -∗
        clockCells cpu -∗
        pcIs cpu (BitVec.addInt pc 4) -∗
        gpr cpu rd (DFrac.own 1) tv -∗
        hartWs cpu ws' -∗
        wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu)) -∗
      wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu) := by
  intro hgid hmok hpmp hal2 hal4 hrd hdecf hagree hDmi hgood hdec
  iintro Hm Hclk Hpc Hnpc Hrdc #Hbs Hhws Hcont
  ihave %haccpc := winstrBytesAccWf pc (.F_Base w) $$ Hbs
  have hacc0 : accWf pc 0 := by unfold accWf at haccpc ⊢; omega
  ihave %hnotRVC := WeakLeafLw4.winstrBytesNotRVC pc w $$ Hbs
  have hdecW : winstrDec (.F_Base w) (.CSRReg (0xC01#12, zreg, .Regidx rd, .CSRRS)) := by
    intro t h1 h2 h3 h4 h5
    simp only [fetchIsRvc, Bool.false_eq_true, ↓reduceIte]
    exact hdecf t h1 h2 h3 h4 h5
  ihave #Hwi := winstrIntro (GF := GF) pc false (.CSRReg (0xC01#12, zreg, .Regidx rd, .CSRRS)) (.F_Base w)
    (by first | rfl | decide) rfl hdecW $$ Hbs
  -- the funnel: certificate = nowrite at the fetch-only trace
  iapply wwpInstr gen cpu pc false (.CSRReg (0xC01#12, zreg, .Regidx rd, .CSRRS)) c dq
    (wPEff (some cpu.val) (regonlyEs al4 pc))
    (wQFr wQPure (some cpu.val) (regonlyEs al4 pc))
    hgid haccpc hmok hpmp
    (wstepCertFr _ _ _ _ (wcertRegonly al4 cpu.val pc)) $$ Hm Hclk Hpc Hwi
  unfold wwpCb
  iintro %σ %b %mt %ip %Lpc0 %hcfg Hlat Hreg Hnorg Hti Hip
  unfold wmstateNorg
  icases Hnorg with ⟨%hbnd, %hnv, %hwf, Hdev, Hlogauth, Hwsauth⟩
  ihave ⟨%hws, Hwsauth, Hhws⟩ := persistent_entails_right (hartWsAgree cpu σ.wmWs ws) $$ [Hwsauth Hhws]
  · iframe Hwsauth Hhws
  subst hws
  obtain ⟨Lpriv, Lhart, Lmisa, Lsec, Lpmpc, Lpma, Lhtif, LmisaS, LmIE, -, -, Lelp⟩ := hcfg
  icases keepPure (winstrFlat σ pc _ hwf) $$ Hlat Hbs with ⟨%hfok, Hlat, -⟩
  icases keepPure (winstrTextPinned σ pc _ hwf) $$ Hlat Hbs with ⟨%htp, Hlat, -⟩
  icases keepPure (winstrUnwritten σ pc _ hwf) $$ Hlat Hbs with ⟨%hunw, Hlat, -⟩
  obtain ⟨-, hram, w', hwok, htext0⟩ := hfok
  obtain ⟨hww, -⟩ := hwok
  subst hww
  -- premise (c): the execute mirror, at the CONFINED state
  have hc : ∀ b' : Bool, ∃ sExec : ExecSt,
      execEff (execute (.CSRReg (0xC01#12, zreg, .Regidx rd, .CSRRS)))
        (((⟨σ.wmRegs, wmemRestrict σ (wwin pc pc 0), σ.wmDev⟩ : ExecSt).setReg
          .minstret_increment b').setReg .nextPC (BitVec.addInt pc 4)) =
        some (.Retire_Success (), sExec, []) ∧
      sExec.regs .hart_state = .HART_ACTIVE () ∧
      sExec.regs .minstret_increment = b' ∧
      bmDomSub sExec.mem (wwin pc pc 0) := by
    intro b'
    obtain ⟨F1, F2, F3, -, -⟩ := loadSexecFacts
      (⟨σ.wmRegs, wmemRestrict σ (wwin pc pc 0), σ.wmDev⟩ : ExecSt) b' (BitVec.addInt pc 4) rd
      (wtimeVal σ)
    refine ⟨_, WeakLeafCsrrTime.execEffCsrrTimeAt σ
      (⟨σ.wmRegs, wmemRestrict σ (wwin pc pc 0), σ.wmDev⟩ : ExecSt) b' _ rd hrd Lpriv rfl, ?_, F2, ?_⟩
    · rw [F1]; exact Lhart
    · rw [F3]; exact wmemRestrictDom σ _
  -- the certificate's precondition
  have HP : wPEff (some cpu.val) (regonlyEs al4 pc) σ :=
    wPEffOfLeafRegonly al4 cpu.val σ (wwin pc pc 0) pc w (.CSRReg (0xC01#12, zreg, .Regidx rd, .CSRRS))
      D dst hwf
      (wwinNonzero pc pc 0 (fun j hj => WeakLeafWin.inRamByte pc 4 j hram hj) (win0Absurd _))
      (wwinPinned σ pc pc 0 haccpc hacc0 (fun j hj => (htp j hj).1) (win0Absurd _))
      (fetchPinOfText σ pc _ (WeakLeafCsrrTime.fetchInWindowRegonly al4 pc haccpc)
        (WeakLeafCsrrTime.fetchFreshRegonly al4 pc) (fun j hj => (htp j hj).2))
      Lpc0 Lpriv (by rw [Lpmpc]; exact hpmp) Lpma Lhtif Lhart LmisaS (by rw [Lmisa]; decide) LmIE Lelp
      hal2 hal4 hram (wwinConfText σ pc pc 0 w htext0) hnotRVC (hagree σ.wmRegs Lpriv Lmisa Lsec) hDmi
      hgood hdec (by first | rfl | decide) hc
  -- the run at the FLAT state
  have hexf := WeakLeafCsrrTime.execEffCsrrTimeAt σ (wflatSt σ) b (BitVec.addInt pc 4) rd hrd Lpriv rfl
  have hfacts := loadSexecFacts (wflatSt σ) b (BitVec.addInt pc 4) rd (wtimeVal σ)
  -- the two register writes the `execute` performs
  imod (wand_intro (reg_update cpu _ .nextPC npc0 (BitVec.addInt pc 4))) $$ Hreg Hnpc with ⟨Hreg, Hnpc⟩
  rw [show (((wflatSt σ).setReg .minstret_increment b).regs.set .nextPC (BitVec.addInt pc 4)) =
      (((wflatSt σ).setReg .minstret_increment b).setReg .nextPC (BitVec.addInt pc 4)).regs from rfl]
  imod WeakLeafLw4.gprUpdate cpu (((wflatSt σ).setReg .minstret_increment b).setReg .nextPC
      (BitVec.addInt pc 4)) rd rd0 (wtimeVal σ) hrd $$ Hreg Hrdc with ⟨Hreg, Hrdc⟩
  iapply fupd_mask_intro LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro; exact HP
  iexists ((((wflatSt σ).setReg .minstret_increment b).setReg .nextPC (BitVec.addInt pc 4)).setGpr rd
    (wtimeVal σ))
  isplitr
  · ipureintro; exact execEffExec _ _ _ _ _ hexf
  isplitl [Hreg]
  · iexact Hreg
  isplitl [Hti Hip]
  · iexists mt, ip
    iframe Hti Hip
  inext
  iintro %tick %σ' %t %_hstep %hdevt0 %hpost %hQ Hm' Hclk' Hpc'
  have hdevt : t.dev = σ.wmDev := by rw [hdevt0, hfacts.2.2.2.1]; rfl
  obtain ⟨-, hdevs, -, -, -, hwsle, hwf', hbnd'⟩ := hpost
  obtain ⟨⟨hQi, hQl, -⟩, hQeff⟩ := hQ
  imod hartWsUpdate cpu σ.wmWs σ.wmWs σ'.wmWs $$ [$Hwsauth $Hhws] with ⟨Hwsauth, Hhws⟩
  imod Hclose
  rw [hfacts.2.2.2.2]
  imodintro
  isplitl [Hlat]
  · rw [hQi, hQl]; iexact Hlat
  isplitl [Hdev Hlogauth Hwsauth]
  · isplitr
    · ipureintro; exact hbnd'
    isplitr
    · ipureintro
      refine nvHartOfWQEffUnwritten cpu σ σ' _ hQeff hnv (fun a ha => ?_)
      obtain ⟨j, hj, rfl⟩ := weffsTouchRegonly al4 pc a haccpc ha
      rw [hQl]
      exact hunw j hj
    isplitr
    · ipureintro; exact hwf'
    rw [hdevs, hdevt, hQl]
    iframe Hdev Hlogauth Hwsauth
  · iapply Hcont $$ %(wtimeVal σ) %σ'.wmWs %hwsle Hm' Hclk' [Hpc' Hnpc] Hrdc Hhws
    unfold pcIs
    iframe Hpc' Hnpc

end leaf

end Weak
