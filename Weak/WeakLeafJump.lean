/-
Weak: **the weak JUMP leaves** (M4, start()/timerinit() port) -- the two
control-flow shapes the `start()` / `timerinit()` port needs.

Rocq: `iris/WeakLeafJump.v` @ xxvzwolszwmp.

The Rocq header, in substance.
* §1 the `execEff` cone of the COMPRESSED return jump (`c.jr rs1` / `c.ret`,
  i.e. the expanded `jalr x0, 0(rs1)`) -- the mirrors of
  `WpMmodeLeafBase.exec_cE_zicfilp_false`, `ExecCommon.exec_jump_to_zca` and
  `WpMmodeLeafBase.exec_execute_JALR_ret_zca`, plus the successor register
  frame `cjrSexecFacts` (a jump writes `nextPC` TWICE and, for `rd = x0`,
  writes no GPR at all -- so neither `loadSexecFacts` nor `jalSexecFacts`
  fits);
* §2 `wwpJalLeaf` -- the `F_Base` JAL leaf (`WpMmodeJal.wp_jal_gpr` under the
  porting-table swaps, the link register held as ONE destination CELL); the
  proof is `WkEntryNew`'s JAL funnel block made generic in the pc / immediate
  / link register / fetch alignment;
* §3 `wwpCjrRvcLeaf` -- the `F_RVC` `c.jr`/`c.ret` leaf
  (`WpMmodeJalr.wp_cret_gpr_zca`, cell-based).
Both leaves ride the PLAIN funnel (`WeakFunnel.wwpInstr`) with a fetch-only,
no-write certificate, and both are ALIGNMENT-GENERIC (`al4`).  The JAL leaf
takes the 4-alignment of the TARGET as a premise (split by
`WeakLeafJump.aligned4JumpBits`); the compressed return jump needs none: under
misa.C (from `wcfgRegs`) `jump_to` accepts a 2-aligned target and `retPc`
clears bit 0 by construction.

**Deviations from Rocq.**
1. VOCABULARY: the `Weak/WkEntryEff.lean` / `Weak/WeakLeafItype.lean`
   conventions (`register_lookup r s.(sregs)` ↦ `s.regs r`, `set_reg` ↦
   `ExecSt.setReg`, `add_vec_int` ↦ `BitVec.addInt`, `add_vec` ↦ `+`,
   `sign_extend' 64` ↦ `sign_extend (m := 64)`, `mword n` ↦ `BitVec n`,
   `uint r <> 0` ↦ `r.toNat ≠ 0`, `eq_vec (access_vec_dec t 0) 'b"0"` ↦
   `(Sail.BitVec.access t 0 == 0#1) = true`, `update_vec_dec v 0 'b"0"` ↦
   `BitVec.update v 0 0#1`, `zeros' 12` ↦ `zeros (n := 12)`,
   `RETIRE_SUCCESS` ↦ `RETIRE_SUCCESS`/`.Retire_Success ()`,
   `mword_of_int 0` ↦ `0#64`, `bool_bit_backwards` kept).  The GPR read
   `register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s` is `s.gpr rs1`
   (equal under the kept `rs1.toNat ≠ 0`); `RiscvExtras.ret_pc` ↦
   `WeakLeafMret.retPc`.
2. `execute_JALR`'s `rd = x0` write: Rocq `uint rdz = 0` kept as
   `rdz.toNat = 0`; the x0 write is the Lean-only
   `WeakLeafJump.execEffWXBitsX0` (silent).
3. THE CELLS: Rocq `R_bitvector_64 (gpr_of_Z (uint r)) ↦ᵣ v` ↦
   `MachCSL.gpr cpu r (DFrac.own 1) v`; `regval_into_reg v` ↦ `v`.
4. THE CONFIG INTERFACE (owner decision Q3, as `Weak/WeakLeafItype.lean`
   deviation 3): `mmode_config (DfracOwn q) -∗ pmpcfg_n ↦ᵣ{DfracOwn q}
   pmpcfg0` ↦ `mConf cpu (DFrac.own q) c ∗ clockCells cpu` (`pmpcfg0 :=
   c.pmpcfg`, `pmp_allows_all pmpcfg0` ↦ `pmpAllowsAll c.pmpcfg`, plus
   `MConf.mok c`); `GenId`/`CpuId` ↦ explicit `gen`/`cpu`; `WWP Loop` ↦
   `wwpTriv ⊤ (WExpr.loop gen cpu)`; `pc_is` ↦ `pcIs`; `hart_ws cpu_id` ↦
   `hartWs cpu`; the decode premises in the funnel's vocabulary (`privMSU`,
   `misaC`, `cfgOk`, `decodeFetch`, the agreement over a `RegFile`).  The
   `al4` parameter comes after `gen cpu` (tree convention).
5. O2 (owner decision): the fetch elements are `.WEread WeakFetchEff.wakIfetch …`
   (Rocq `wak_plain`); the recipes' fetch pin is discharged from
   `winstrTextPinned` (`WeakLeafCsrrTime.fetchInWindowRegonly`/
   `fetchFreshRegonly` for `F_Base`, `WeakLeafItype.fetchPinRvc0` for the
   compressed read).
6. `RiscvExtras.aligned4_jump_bits` / `ret_pc_jalr` / `ret_pc_aligned` have no
   Lean twin: Lean-only `WeakLeafJump.aligned4JumpBits`, `retPcJalr`,
   `retPcAligned`.
7. `exec_eff_execute_cret_zca` states the target as `retPc (s.gpr ra)`
   (deviation 1); `cjr_sexec_facts`' `let s_exec` is kept.
8. Rocq §4's `Print Assumptions` commands are not declarations.

**Rocq → Lean name map.**  `exec_eff_cE_zicfilp_false` `execEffCEZicfilpFalse`,
`exec_eff_jump_to_zca` `execEffJumpToZca`, `exec_eff_execute_JALR_ret_zca`
`execEffExecuteJALRRetZca`, `exec_eff_execute_cret_zca` `execEffExecuteCretZca`,
`cjr_sexec_facts` `cjrSexecFacts`, `wwp_jal_leaf` `wwpJalLeaf`,
`wwp_cjr_rvc_leaf` `wwpCjrRvcLeaf` (none in the duplicated-name table).
Lean-only (file-qualified): `WeakLeafJump.execEffWXBitsX0`,
`WeakLeafJump.aligned4JumpBits`, `WeakLeafJump.retPcJalr`,
`WeakLeafJump.retPcAligned`.

**Dropped:** nothing (Rocq 7 lemmas; Lean 7 theorems + 4 Lean-only).
-/
import Weak.WkEntryNew
import Weak.WeakLeafItype
import Weak.WeakLeafMret

namespace Weak

open Iris Iris.BI Iris.BI.MonPred Iris.ProofMode Iris.Std
open MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D LeanRV64D.Functions

/-! ## 1. THE `execEff` CONE OF THE COMPRESSED RETURN JUMP (trace `[]`) -/

/-- Rocq `exec_eff_cE_zicfilp_false`: `currentlyEnabled Ext_Zicfilp = false` in
M-mode with `mseccfg.MLPE` clear. -/
theorem execEffCEZicfilpFalse (s : ExecSt) (hcp : s.regs .cur_privilege = .Machine)
    (hm : bool_bit_backwards (_get_Seccfg_MLPE (s.regs .mseccfg)) = false) :
    execEff (currentlyEnabled .Ext_Zicfilp) s = some (false, s, []) := by
  rw [currentlyEnabled]
  -- (since 2026-11-04 the gate is `false` without reads; `hcp`/`hm` no longer needed)
  simp only [execEffBindEq, execEffRecCEZicsrAny, execEffHartSupportsZicfilp, ↓reduceIte,
    Bool.false_eq_true]
  try unfold get_xLPE
  try exec_eff_steps [hcp, hm]

/-- Rocq `exec_eff_jump_to_zca`: `jump_to` under the C extension (a 2-aligned
target jumps). -/
theorem execEffJumpToZca (target : BitVec 64) (s : ExecSt)
    (halign : (BitVec.access target 0 == 0#1) = true)
    (hzca : execEff (currentlyEnabled .Ext_Zca) s = some (true, s, [])) :
    execEff (jump_to target) s = some (RETIRE_SUCCESS, s.setReg .nextPC target, []) := by
  unfold jump_to
  rw [execEffCatchEarlyReturn]
  cases hb : bit_to_bool (BitVec.access target 1)
  · simp only [ext_control_check_pc, execREffBindEq, execREffReturnR, execREffLiftR, assert,
      PreSail.assert, halign, ↓reduceIte, execEffReturnm, Bool.false_eq_true,
      WkEntryEff.execEffSetNextPc, List.append_nil]
  · simp only [ext_control_check_pc, execREffBindEq, execREffReturnR, execREffLiftR, assert,
      PreSail.assert, halign, ↓reduceIte, execEffReturnm, hzca, Functions.not, Bool.not_true,
      Bool.false_eq_true, WkEntryEff.execEffSetNextPc, List.append_nil]

/-- Lean-only (deviation 2): the x0 write is silent. -/
theorem WeakLeafJump.execEffWXBitsX0 (v : BitVec 64) (s : ExecSt) :
    execEff (wX_bits (.Regidx 0#5) v) s = some ((), s, []) := rfl

/-- Rocq `exec_eff_execute_JALR_ret_zca`: the return-shaped JALR (`rd = x0`,
no link write). -/
theorem execEffExecuteJALRRetZca (imm : BitVec 12) (rs1 rdz : BitVec 5) (s : ExecSt)
    (_hrs1 : rs1.toNat ≠ 0) (hrdz : rdz.toNat = 0)
    (hzic : execEff (currentlyEnabled .Ext_Zicfilp) s = some (false, s, []))
    (hzca : execEff (currentlyEnabled .Ext_Zca) s = some (true, s, []))
    (halign : (BitVec.access (BitVec.update (s.gpr rs1 + sign_extend (m := 64) imm) 0 0#1) 0 == 0#1)
      = true) :
    execEff (execute_JALR imm (.Regidx rs1) (.Regidx rdz)) s =
      some (RETIRE_SUCCESS, s.setReg .nextPC (BitVec.update (s.gpr rs1 + sign_extend (m := 64) imm) 0 0#1),
        []) := by
  have h0 : rdz = 0#5 := BitVec.eq_of_toNat_eq hrdz
  subst h0
  unfold execute_JALR update_elp_state get_next_pc
  exec_eff_steps [hzic, execEffRXBitsGpr, execEffJumpToZca _ s halign hzca, RETIRE_SUCCESS,
    WeakLeafJump.execEffWXBitsX0]

/-- Lean-only (Rocq `RiscvExtras.ret_pc_jalr`): the zero offset collapses. -/
theorem WeakLeafJump.retPcJalr (v : BitVec 64) :
    BitVec.update (v + sign_extend (m := 64) (zeros (n := 12))) 0 0#1 = WeakLeafMret.retPc v := by
  rw [show sign_extend (m := 64) (zeros (n := 12)) = 0#64 from by decide +kernel, BitVec.add_zero]
  rfl

/-- Lean-only (Rocq `RiscvExtras.ret_pc_aligned`): `retPc` clears bit 0. -/
theorem WeakLeafJump.retPcAligned (v : BitVec 64) :
    (BitVec.access (WeakLeafMret.retPc v) 0 == 0#1) = true := by
  unfold WeakLeafMret.retPc Sail.BitVec.update Sail.BitVec.updateSubrange' Sail.BitVec.access
  have h : (18446744073709551614#64 &&& v)[0] = false := by
    rw [BitVec.getElem_and]
    simp
  simp [h]

/-- Rocq `exec_eff_execute_cret_zca` (deviation 7): the end-to-end `c.jr rs1` /
`c.ret` execute mirror, at the config facts `wcfgRegs` hands a leaf. -/
theorem execEffExecuteCretZca (ra : BitVec 5) (s : ExecSt) (hra : ra.toNat ≠ 0)
    (hpriv : s.regs .cur_privilege = .Machine) (hsec : s.regs .mseccfg = 0#64)
    (hC : (_get_Misa_C (s.regs .misa) == 1#1) = true) :
    execEff (execute (.JALR (zeros (n := 12), .Regidx ra, zreg))) s =
      some (RETIRE_SUCCESS, s.setReg .nextPC (WeakLeafMret.retPc (s.gpr ra)), []) := by
  have hzic := execEffCEZicfilpFalse s hpriv (by rw [hsec]; decide)
  have hzca := execEffCurrentlyEnabledZca s hC
  have htgt := WeakLeafJump.retPcJalr (s.gpr ra)
  show execEff (execute_JALR (zeros (n := 12)) (.Regidx ra) (.Regidx 0#5)) s = _
  rw [execEffExecuteJALRRetZca _ ra 0#5 s hra rfl hzic hzca
    (by rw [htgt]; exact WeakLeafJump.retPcAligned _), htgt]

/-! ## 1e. The successor register frame for a no-link jump -/

/-- Rocq `cjr_sexec_facts`: `jalSexecFacts` without the link write. -/
theorem cjrSexecFacts (s0 : ExecSt) (b : Bool) (npc target : BitVec 64) :
    let sExec := ((s0.setReg .minstret_increment b).setReg .nextPC npc).setReg .nextPC target
    sExec.regs .hart_state = s0.regs .hart_state ∧
    sExec.regs .minstret_increment = b ∧
    sExec.mem = s0.mem ∧
    sExec.dev = s0.dev ∧
    sExec.regs .nextPC = target := by
  intro sExec
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [setLookupNe .hart_state .nextPC _ _ (by decide)]
    leaf_peel .hart_state
  · rw [setLookupNe .minstret_increment .nextPC _ _ (by decide),
      setLookupNe .minstret_increment .nextPC _ _ (by decide)]
    simp only [ExecSt.setReg_regs, RegFile.set_same]
  · rfl
  · rfl
  · simp only [sExec, ExecSt.setReg_regs, RegFile.set_same]

/-- Lean-only (Rocq `RiscvExtras.aligned4_jump_bits`): a 4-aligned target passes
both of `jump_to`'s bit tests. -/
theorem WeakLeafJump.aligned4JumpBits (t : BitVec 64) (h : is_aligned_paddr (.Physaddr t) 4 = true) :
    (BitVec.access t 0 == 0#1) = true ∧ bit_to_bool (BitVec.access t 1) = false := by
  have hm : t.toNat % 4 = 0 := isAlignedVaddrMod t 4 (by decide) h
  have h0 := bit0_clear_of_even t (by omega)
  have h1 := bit1_clear_of_mod4 t hm
  refine ⟨?_, ?_⟩
  · show (BitVec.ofBool t[0]! == 0#1) = true
    revert h0
    cases t[0]! <;> decide
  · show bit_to_bool (BitVec.ofBool t[1]!) = false
    revert h1
    cases t[1]! <;> decide

/-! ## 2. THE JAL LEAF (`F_Base`, alignment-generic) -/

section leafJal
variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [WeakGS GF]

/-- Rocq `wwp_jal_leaf` (deviations 1, 3-5). -/
theorem wwpJalLeaf (gen : Nat) (cpu : CPU) (al4 : Bool) (pc : BitVec 64) (w : BitVec 32)
    (rd : BitVec 5) (imm : BitVec 21) (rdv0 npc0 : BitVec 64) (c : MConf) (q : Qp)
    (D : Register → Bool) (dst : ExecSt) (ws : Wstate) :
    gen = 0 →
    MConf.mok c →
    pmpAllowsAll c.pmpcfg →
    is_aligned_vaddr (.Virtaddr pc) 2 = true →
    is_aligned_vaddr (.Virtaddr pc) 4 = al4 →
    rd.toNat ≠ 0 →
    is_aligned_paddr (.Physaddr (pc + sign_extend (m := 64) imm)) 4 = true →
    -- the decode, in the two shapes its two consumers ask for
    (∀ t : ExecSt,
      privMSU (t.regs .cur_privilege) = true →
      (_get_Misa_C (t.regs .misa) == 1#1) = true →
      (_get_Misa_A (t.regs .misa) == 1#1) = true →
      t.regs .misa = misaC →
      cfgOk t →
      exec (decodeFetch (.F_Base w)) t = some (.JAL (imm, .Regidx rd), t)) →
    (∀ rs : RegFile,
      rs .cur_privilege = .Machine →
      rs .misa = misaC →
      rs .mseccfg = 0#64 →
      ∀ r, D r = true → rs r = dst.regs r) →
    D .minstret_increment = false →
    goodb0 D (ext_decode w) dst = true →
    exec (ext_decode w) dst = some (.JAL (imm, .Regidx rd), dst) →
    mConf (GF := GF) cpu (DFrac.own q) c ⊢
      clockCells cpu -∗
      Register.PC ↦ᵣ[cpu] pc -∗
      Register.nextPC ↦ᵣ[cpu] npc0 -∗
      gpr cpu rd (DFrac.own 1) rdv0 -∗
      winstrBytes (GF := GF) pc (.F_Base w) -∗
      hartWs (GF := GF) cpu ws -∗
      (∀ ws' : Wstate,
        ⌜wsLe ws ws'⌝ -∗
        mConf cpu (DFrac.own q) c -∗
        clockCells cpu -∗
        pcIs cpu (pc + sign_extend (m := 64) imm) -∗
        gpr cpu rd (DFrac.own 1) (BitVec.addInt pc 4) -∗
        hartWs cpu ws' -∗
        wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu)) -∗
      wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu) := by
  intro hgid hmok hpmp hal2 hal4 hrd halign hdecf hagree hDmi hgood hdec
  obtain ⟨hj0, hj1⟩ := WeakLeafJump.aligned4JumpBits _ halign
  have hlpad : is_lpad_instruction (.JAL (imm, .Regidx rd)) = false := rfl
  iintro Hm Hclk Hpc Hnpc Hrdc #Hbs Hhws Hcont
  ihave %haccpc := winstrBytesAccWf pc (.F_Base w) $$ Hbs
  have hacc0 : accWf pc 0 := by unfold accWf at haccpc ⊢; omega
  ihave %hnotRVC := WeakLeafLw4.winstrBytesNotRVC pc w $$ Hbs
  have hdecW : winstrDec (.F_Base w) (.JAL (imm, .Regidx rd)) := by
    intro t h1 h2 h3 h4 h5
    simp only [fetchIsRvc, Bool.false_eq_true, ↓reduceIte]
    exact hdecf t h1 h2 h3 h4 h5
  ihave #Hwi := winstrIntro (GF := GF) pc false (.JAL (imm, .Regidx rd)) (.F_Base w) hlpad rfl hdecW
    $$ Hbs
  -- the funnel: certificate = nowrite at the fetch-only trace
  iapply wwpInstr gen cpu pc false (.JAL (imm, .Regidx rd)) c (DFrac.own q)
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
      execEff (execute (.JAL (imm, .Regidx rd)))
        (((⟨σ.wmRegs, wmemRestrict σ (wwin pc pc 0), σ.wmDev⟩ : ExecSt).setReg
          .minstret_increment b').setReg .nextPC (BitVec.addInt pc 4)) =
        some (.Retire_Success (), sExec, []) ∧
      sExec.regs .hart_state = .HART_ACTIVE () ∧
      sExec.regs .minstret_increment = b' ∧
      bmDomSub sExec.mem (wwin pc pc 0) := by
    intro b'
    have hp : (((⟨σ.wmRegs, wmemRestrict σ (wwin pc pc 0), σ.wmDev⟩ : ExecSt).setReg
        .minstret_increment b').setReg .nextPC (BitVec.addInt pc 4)).regs .PC = pc := by
      leaf_peel .PC; exact Lpc0
    have he := execEffExecuteJALGpr imm rd (((⟨σ.wmRegs, wmemRestrict σ (wwin pc pc 0), σ.wmDev⟩ :
        ExecSt).setReg .minstret_increment b').setReg .nextPC (BitVec.addInt pc 4)) hrd
      (by rw [hp]; exact hj0) (by rw [hp]; exact hj1)
    obtain ⟨F1, F2, F3, -, -⟩ := jalSexecFacts
      (⟨σ.wmRegs, wmemRestrict σ (wwin pc pc 0), σ.wmDev⟩ : ExecSt) b' (BitVec.addInt pc 4)
      ((((⟨σ.wmRegs, wmemRestrict σ (wwin pc pc 0), σ.wmDev⟩ : ExecSt).setReg
        .minstret_increment b').setReg .nextPC (BitVec.addInt pc 4)).regs .PC + sign_extend (m := 64) imm)
      rd ((((⟨σ.wmRegs, wmemRestrict σ (wwin pc pc 0), σ.wmDev⟩ : ExecSt).setReg
        .minstret_increment b').setReg .nextPC (BitVec.addInt pc 4)).regs .nextPC)
    exact ⟨_, he, by rw [F1]; exact Lhart, F2, by rw [F3]; exact wmemRestrictDom σ _⟩
  -- the certificate's precondition
  have HP : wPEff (some cpu.val) (regonlyEs al4 pc) σ :=
    wPEffOfLeafRegonly al4 cpu.val σ (wwin pc pc 0) pc w _ D dst hwf
      (wwinNonzero pc pc 0 (fun j hj => WeakLeafWin.inRamByte pc 4 j hram hj) (win0Absurd _))
      (wwinPinned σ pc pc 0 haccpc hacc0 (fun j hj => (htp j hj).1) (win0Absurd _))
      (fetchPinOfText σ pc _ (WeakLeafCsrrTime.fetchInWindowRegonly al4 pc haccpc)
        (WeakLeafCsrrTime.fetchFreshRegonly al4 pc) (fun j hj => (htp j hj).2))
      Lpc0 Lpriv (by rw [Lpmpc]; exact hpmp) Lpma Lhtif Lhart LmisaS (by rw [Lmisa]; decide) LmIE Lelp
      hal2 hal4 hram (wwinConfText σ pc pc 0 w htext0) hnotRVC (hagree σ.wmRegs Lpriv Lmisa Lsec) hDmi
      hgood hdec hlpad hc
  -- the run at the FLAT state
  have hpf : (((wflatSt σ).setReg .minstret_increment b).setReg .nextPC (BitVec.addInt pc 4)).regs .PC
      = pc := by
    leaf_peel .PC; exact Lpc0
  have hnf : (((wflatSt σ).setReg .minstret_increment b).setReg .nextPC (BitVec.addInt pc 4)).regs
      .nextPC = BitVec.addInt pc 4 := by
    simp only [ExecSt.setReg_regs, RegFile.set_same]
  have hexf := execEffExecuteJALGpr imm rd (((wflatSt σ).setReg .minstret_increment b).setReg .nextPC
    (BitVec.addInt pc 4)) hrd (by rw [hpf]; exact hj0) (by rw [hpf]; exact hj1)
  rw [hpf, hnf] at hexf
  have hfacts := jalSexecFacts (wflatSt σ) b (BitVec.addInt pc 4) (pc + sign_extend (m := 64) imm) rd
    (BitVec.addInt pc 4)
  -- the three register writes the `execute` performs
  imod (wand_intro (reg_update cpu _ .nextPC npc0 (BitVec.addInt pc 4))) $$ Hreg Hnpc with ⟨Hreg, Hnpc⟩
  imod (wand_intro (reg_update cpu _ .nextPC (BitVec.addInt pc 4) (pc + sign_extend (m := 64) imm)))
    $$ Hreg Hnpc with ⟨Hreg, Hnpc⟩
  rw [show ((((wflatSt σ).setReg .minstret_increment b).regs.set .nextPC (BitVec.addInt pc 4)).set
      .nextPC (pc + sign_extend (m := 64) imm)) =
      ((((wflatSt σ).setReg .minstret_increment b).setReg .nextPC (BitVec.addInt pc 4)).setReg .nextPC
        (pc + sign_extend (m := 64) imm)).regs from rfl]
  imod WeakLeafLw4.gprUpdate cpu ((((wflatSt σ).setReg .minstret_increment b).setReg .nextPC
      (BitVec.addInt pc 4)).setReg .nextPC (pc + sign_extend (m := 64) imm)) rd rdv0
      (BitVec.addInt pc 4) hrd $$ Hreg Hrdc with ⟨Hreg, Hrdc⟩
  iapply fupd_mask_intro LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro; exact HP
  iexists (((((wflatSt σ).setReg .minstret_increment b).setReg .nextPC (BitVec.addInt pc 4)).setReg
    .nextPC (pc + sign_extend (m := 64) imm)).setGpr rd (BitVec.addInt pc 4))
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
  · iapply Hcont $$ %σ'.wmWs %hwsle Hm' Hclk' [Hpc' Hnpc] Hrdc Hhws
    unfold pcIs
    iframe Hpc' Hnpc

end leafJal

/-! ## 3. THE c.jr / c.ret LEAF (`F_RVC`, alignment-generic) -/

section leafCjr
variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [WeakGS GF]

/-- Rocq `wwp_cjr_rvc_leaf` (deviations 1, 3-5). -/
theorem wwpCjrRvcLeaf (gen : Nat) (cpu : CPU) (al4 : Bool) (pc : BitVec 64) (h : BitVec 16)
    (ra : BitVec 5) (i0 : instruction) (rav npc0 : BitVec 64) (c : MConf) (q : Qp)
    (D D0 : Register → Bool) (dst : ExecSt) (ws : Wstate) :
    gen = 0 →
    MConf.mok c →
    pmpAllowsAll c.pmpcfg →
    is_aligned_vaddr (.Virtaddr pc) 2 = true →
    is_aligned_vaddr (.Virtaddr pc) 4 = al4 →
    ra.toNat ≠ 0 →
    -- the decode, in the two shapes its two consumers ask for
    (∀ t : ExecSt,
      privMSU (t.regs .cur_privilege) = true →
      (_get_Misa_C (t.regs .misa) == 1#1) = true →
      (_get_Misa_A (t.regs .misa) == 1#1) = true →
      t.regs .misa = misaC →
      cfgOk t →
      ∃ i0' : instruction,
        exec (decodeFetch (.F_RVC h)) t = some (i0', t) ∧
        is_lpad_instruction i0' = false ∧
        (∀ s : ExecSt, exec (execute i0') s =
          some (.ExecuteAs (.JALR (zeros (n := 12), .Regidx ra, zreg)), s))) →
    (∀ rs : RegFile,
      rs .cur_privilege = .Machine →
      rs .misa = misaC →
      rs .mseccfg = 0#64 →
      ∀ r, D r = true → rs r = dst.regs r) →
    D .minstret_increment = false →
    goodb0 D (ext_decode_compressed h) dst = true →
    exec (ext_decode_compressed h) dst = some (i0, dst) →
    (∀ s : ExecSt, goodb0 D0 (execute i0) s = true) →
    (∀ s : ExecSt, exec (execute i0) s =
      some (.ExecuteAs (.JALR (zeros (n := 12), .Regidx ra, zreg)), s)) →
    mConf (GF := GF) cpu (DFrac.own q) c ⊢
      clockCells cpu -∗
      Register.PC ↦ᵣ[cpu] pc -∗
      Register.nextPC ↦ᵣ[cpu] npc0 -∗
      gpr cpu ra (DFrac.own 1) rav -∗
      winstrBytes (GF := GF) pc (.F_RVC h) -∗
      hartWs (GF := GF) cpu ws -∗
      (∀ ws' : Wstate,
        ⌜wsLe ws ws'⌝ -∗
        mConf cpu (DFrac.own q) c -∗
        clockCells cpu -∗
        pcIs cpu (WeakLeafMret.retPc rav) -∗
        gpr cpu ra (DFrac.own 1) rav -∗
        hartWs cpu ws' -∗
        wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu)) -∗
      wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu) := by
  intro hgid hmok hpmp hal2 hal4 hranz hdecf hagree hDmi hgood hdec hgood0 hexp
  have hlpad : is_lpad_instruction (.JALR (zeros (n := 12), .Regidx ra, zreg)) = false := rfl
  iintro Hm Hclk Hpc Hnpc Hrac #Hbs Hhws Hcont
  ihave %haccpc := winstrBytesAccWf pc (.F_RVC h) $$ Hbs
  have hacc0 : accWf pc 0 := by unfold accWf at haccpc ⊢; omega
  have hdecW : winstrDec (.F_RVC h) (.JALR (zeros (n := 12), .Regidx ra, zreg)) := by
    intro t h1 h2 h3 h4 h5
    simp only [fetchIsRvc, ↓reduceIte]
    exact hdecf t h1 h2 h3 h4 h5
  ihave #Hwi := winstrIntro (GF := GF) pc true (.JALR (zeros (n := 12), .Regidx ra, zreg)) (.F_RVC h)
    hlpad rfl hdecW $$ Hbs
  -- the funnel: certificate = nowrite at the single fetch read
  iapply wwpInstr gen cpu pc true (.JALR (zeros (n := 12), .Regidx ra, zreg)) c (DFrac.own q)
    (wPEff (some cpu.val) [.WEread WeakFetchEff.wakIfetch pc (if al4 then 4 else 2)])
    (wQFr wQPure (some cpu.val) [.WEread WeakFetchEff.wakIfetch pc (if al4 then 4 else 2)])
    hgid haccpc hmok hpmp
    (wstepCertFr _ _ _ _ (wcertNowrite cpu.val pc _
      (nowriteRead1 WeakFetchEff.wakIfetch pc (if al4 then 4 else 2)))) $$ Hm Hclk Hpc Hwi
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
  obtain ⟨-, hram, w, hwok, htext0⟩ := hfok
  obtain ⟨hsub, hisRVC⟩ := hwok
  have LmisaC : (_get_Misa_C (σ.wmRegs .misa) == 1#1) = true := by rw [Lmisa]; decide
  -- the ONE register the funnel does not read: this instruction's source
  icases keepPure (WeakLeafLw4.gprValid cpu _ ra _ rav hranz) $$ Hreg Hrac with ⟨%Lraa, Hreg, Hrac⟩
  have Lra : (wflatSt σ).gpr ra = rav := by
    rw [← WeakLeafLw4.gprSetNe (wflatSt σ) .minstret_increment b ra (by decide)]
    exact Lraa
  -- premise (c): the execute mirror, at the CONFINED state
  have hc : ∀ b' : Bool, ∃ sExec : ExecSt,
      execEff (execute (.JALR (zeros (n := 12), .Regidx ra, zreg)))
        (((⟨σ.wmRegs, wmemRestrict σ (wwin pc pc 0), σ.wmDev⟩ : ExecSt).setReg
          .minstret_increment b').setReg .nextPC (BitVec.addInt pc 2)) =
        some (.Retire_Success (), sExec, []) ∧
      sExec.regs .hart_state = .HART_ACTIVE () ∧
      sExec.regs .minstret_increment = b' ∧
      bmDomSub sExec.mem (wwin pc pc 0) := by
    intro b'
    have hprivc : (((⟨σ.wmRegs, wmemRestrict σ (wwin pc pc 0), σ.wmDev⟩ : ExecSt).setReg
        .minstret_increment b').setReg .nextPC (BitVec.addInt pc 2)).regs .cur_privilege = .Machine := by
      leaf_peel .cur_privilege; exact Lpriv
    have hsecc : (((⟨σ.wmRegs, wmemRestrict σ (wwin pc pc 0), σ.wmDev⟩ : ExecSt).setReg
        .minstret_increment b').setReg .nextPC (BitVec.addInt pc 2)).regs .mseccfg = 0#64 := by
      leaf_peel .mseccfg; exact Lsec
    have hCc : (_get_Misa_C ((((⟨σ.wmRegs, wmemRestrict σ (wwin pc pc 0), σ.wmDev⟩ : ExecSt).setReg
        .minstret_increment b').setReg .nextPC (BitVec.addInt pc 2)).regs .misa) == 1#1) = true := by
      leaf_peel .misa; exact LmisaC
    have he := execEffExecuteCretZca ra (((⟨σ.wmRegs, wmemRestrict σ (wwin pc pc 0), σ.wmDev⟩ :
        ExecSt).setReg .minstret_increment b').setReg .nextPC (BitVec.addInt pc 2)) hranz hprivc hsecc hCc
    obtain ⟨F1, F2, F3, -, -⟩ := cjrSexecFacts
      (⟨σ.wmRegs, wmemRestrict σ (wwin pc pc 0), σ.wmDev⟩ : ExecSt) b' (BitVec.addInt pc 2)
      (WeakLeafMret.retPc ((((⟨σ.wmRegs, wmemRestrict σ (wwin pc pc 0), σ.wmDev⟩ : ExecSt).setReg
        .minstret_increment b').setReg .nextPC (BitVec.addInt pc 2)).gpr ra))
    exact ⟨_, he, by rw [F1]; exact Lhart, F2, by rw [F3]; exact wmemRestrictDom σ _⟩
  -- the certificate's precondition
  have HP : wPEff (some cpu.val) [.WEread WeakFetchEff.wakIfetch pc (if al4 then 4 else 2)] σ :=
    wPEffOfLeafRvc al4 cpu.val σ (wwin pc pc 0) pc h w i0 _ [] D D0 dst hwf
      (wwinNonzero pc pc 0 (fun j hj => WeakLeafWin.inRamByte pc 4 j hram hj) (win0Absurd _))
      (wwinPinned σ pc pc 0 haccpc hacc0 (fun j hj => (htp j hj).1) (win0Absurd _))
      (WeakLeafItype.fetchPinRvc0 al4 σ pc (fun j hj => (htp j hj).2))
      Lpc0 Lpriv (by rw [Lpmpc]; exact hpmp) Lpma Lhtif Lhart LmisaS LmisaC LmIE Lelp
      hal2 hal4 hram (wwinConfText σ pc pc 0 w htext0) hsub hisRVC (hagree σ.wmRegs Lpriv Lmisa Lsec)
      hDmi hgood hdec hgood0 hexp hc
  -- the run at the FLAT state
  have hprivf : (((wflatSt σ).setReg .minstret_increment b).setReg .nextPC (BitVec.addInt pc 2)).regs
      .cur_privilege = .Machine := by
    leaf_peel .cur_privilege; exact Lpriv
  have hsecf : (((wflatSt σ).setReg .minstret_increment b).setReg .nextPC (BitVec.addInt pc 2)).regs
      .mseccfg = 0#64 := by
    leaf_peel .mseccfg; exact Lsec
  have hCf : (_get_Misa_C ((((wflatSt σ).setReg .minstret_increment b).setReg .nextPC
      (BitVec.addInt pc 2)).regs .misa) == 1#1) = true := by
    leaf_peel .misa; exact LmisaC
  have hraf : (((wflatSt σ).setReg .minstret_increment b).setReg .nextPC (BitVec.addInt pc 2)).gpr ra
      = rav := by
    rw [WeakLeafLw4.gprSetNe _ _ _ _ (by decide), WeakLeafLw4.gprSetNe _ _ _ _ (by decide)]
    exact Lra
  have hexf := execEffExecuteCretZca ra (((wflatSt σ).setReg .minstret_increment b).setReg .nextPC
    (BitVec.addInt pc 2)) hranz hprivf hsecf hCf
  rw [hraf] at hexf
  have hfacts := cjrSexecFacts (wflatSt σ) b (BitVec.addInt pc 2) (WeakLeafMret.retPc rav)
  -- the two `nextPC` writes
  imod (wand_intro (reg_update cpu _ .nextPC npc0 (BitVec.addInt pc 2))) $$ Hreg Hnpc with ⟨Hreg, Hnpc⟩
  imod (wand_intro (reg_update cpu _ .nextPC (BitVec.addInt pc 2) (WeakLeafMret.retPc rav)))
    $$ Hreg Hnpc with ⟨Hreg, Hnpc⟩
  rw [show ((((wflatSt σ).setReg .minstret_increment b).regs.set .nextPC (BitVec.addInt pc 2)).set
      .nextPC (WeakLeafMret.retPc rav)) =
      ((((wflatSt σ).setReg .minstret_increment b).setReg .nextPC (BitVec.addInt pc 2)).setReg .nextPC
        (WeakLeafMret.retPc rav)).regs from rfl]
  iapply fupd_mask_intro LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro; exact HP
  iexists ((((wflatSt σ).setReg .minstret_increment b).setReg .nextPC (BitVec.addInt pc 2)).setReg
    .nextPC (WeakLeafMret.retPc rav))
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
      obtain ⟨j, hj, rfl⟩ := weffsTouchRead1 _ pc _ a ha
      rw [hQl]
      exact hunw j (WeakLeafTor.ltFetchW al4 j hj)
    isplitr
    · ipureintro; exact hwf'
    rw [hdevs, hdevt, hQl]
    iframe Hdev Hlogauth Hwsauth
  · iapply Hcont $$ %σ'.wmWs %hwsle Hm' Hclk' [Hpc' Hnpc] Hrac Hhws
    unfold pcIs
    iframe Hpc' Hnpc

end leafCjr

end Weak
