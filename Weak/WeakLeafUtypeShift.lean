/-
Weak: **the weak UTYPE and shift-immediate GPR-FILE leaves** (M4, the
`start()`/`timerinit()` port).

Rocq: `iris/WeakLeafUtypeShift.v` @ xxvzwolszwmp.

The Rocq header, in substance.  Five register-only leaves on the PLAIN funnel
(`WeakFunnel.wwpInstr`), all stated over the WHOLE register file `gprFile`
rather than per-register cells, because nearly every call site in
`start()`/`timerinit()` has `rd = rs1` (the shift-immediates always do -- they
come from `c.slli`/`c.srli`) or `rs1 = x0`, and separate cells cannot express
that:
* §2 `wwpLuiLeaf` -- `F_Base` LUI;
* §3 `wwpLuiRvcLeaf` -- the SAME AST reached by a COMPRESSED decode (`c.lui`);
* §4 `wwpAuipcLeaf` -- `F_Base` AUIPC;
* §5 `wwpSlliRvcLeaf` -- `c.slli`;
* §6 `wwpSrliRvcLeaf` -- `c.srli`.
Every leaf takes the fetch alignment `al4 : Bool` and so covers both the
4-aligned and the 2-not-4-aligned call sites with ONE statement: the `F_Base`
pair goes through `WeakLeafRegOnly.wPEffOfLeafRegonly` (+ `wcertRegonly`), the
compressed three through `WeakLeafTor.wPEffOfLeafRvc` at `es_x := []`
(+ `WeakEff.wcertNowrite` at the one-element fetch trace, whose width is the
only thing `al4` decides).  §1 holds the two missing `execute` mirrors
(SHIFTIOP SLLI/SRLI, trace `[]`); the LUI/AUIPC mirrors are `WkEntryEff`'s.

**Deviations from Rocq.**
1. VOCABULARY: the `Weak/ExecSC*.lean` conventions (`register_lookup r
   s.(sregs)` ↦ `s.regs r`, `mword n` ↦ `BitVec n`, `set_reg` ↦
   `ExecSt.setReg`, `add_vec_int` ↦ `BitVec.addInt`, `uint x` ↦ `x.toNat`,
   `subrange_vec_dec shamt (log2_xlen - 1) 0` ↦
   `Sail.BitVec.extractLsb shamt (Functions.log2_xlen -i 1) 0`).  The §1
   mirrors state the GPR write as `s.setGpr rd v` (`WkEntryEff` deviation 5:
   Rocq's `if uint rd =? 0 then s else set_reg …` IS `setGpr`); `luival` is
   `WkEntryEff.luival`, `auipc_off` `ExecSC.auipcOff`, `gpr_slli_val` /
   `gpr_srli_val` `ExecSC.gprSlliVal` / `gprSrliVal`.
2. THE REGISTER FILE: Rocq `WpGpr.gpr_file m` over `m : regfile` ↦
   `MachCSL.gprFile cpu m` over `m : RegMap` (`Weak/WkGprAcc.lean`
   deviation 1); `<[Regidx rd := regval_into_reg v]> m` ↦ `m.set rd v`; the
   x0-safe source value `m !!! Regidx rs1` ↦ `m.get rs1` (`RegMap.get`: `x0`
   reads 0; Lean's file does not own `x0`).  The x0-safe read
   (`gpr_file_lookup_acc` + `gpr_pt_value`) and the write
   (`gpr_file_insert_acc` + `gpr_pt_nz` + `reg_update`) are the Lean-only
   `WeakLeafUtypeShift.gprFileValid` / `gprFileUpdate` (over
   `gprFile_lookup_acc`/`gprFile_acc` and `WeakLeafLw4.gprValid`/`gprUpdate`).
3. THE CONFIG INTERFACE (owner decision Q3, `Weak/WeakFunnel.lean`
   deviation 7): Rocq `mmode_config (DfracOwn q) -∗ pmpcfg_n ↦ᵣ{DfracOwn q}
   pmpcfg0` ↦ `mConf cpu (DFrac.own q) c ∗ clockCells cpu` (`pmpcfg0 :=
   c.pmpcfg`, `pmp_allows_all pmpcfg0` ↦ `pmpAllowsAll c.pmpcfg`, plus
   `MConf.mok c`); the continuation gets the same back.  `GenId`/`CpuId` are
   the explicit `gen`/`cpu`; `WWP Loop` ↦ `wwpTriv ⊤ (WExpr.loop gen cpu)`;
   `pc_is` ↦ `pcIs`; `hart_ws cpu_id` ↦ `hartWs cpu`; `A -∗ B -∗ …` ↦
   `A ⊢ B -∗ …`; the decode premises are over the funnel's vocabulary
   (`privMSU`, `misaC`, `cfgOk`, `decodeFetch`; the agreement premise
   quantifies over `RegFile`, `mword_of_int 0` ↦ `0#64`).  O2: the fetch
   elements are `.WEread WeakFetchEff.wakIfetch …` (Rocq `wak_plain`); the
   fetch pin is discharged from `winstrTextPinned` (`fetchPinOfText` with
   `WeakLeafCsrrTime.fetchInWindowRegonly`/`fetchFreshRegonly` for `F_Base`,
   the Lean-only `WeakLeafUtypeShift.fetchPinRvc0` for the compressed fetch).
4. PROOF FACTORING (statements unchanged): Rocq proves the five leaves by five
   copies of one script.  Lean proves two Lean-only cores,
   `WeakLeafUtypeShift.wwpGprFileBaseLeaf` (F_Base) and
   `WeakLeafUtypeShift.wwpGprFileRvcLeaf` (compressed), parameterised by the
   instruction, the written value and the `execEff` run (premise: at any state
   whose `PC` is `pc` and whose source register `rs` holds `m.get rs`, the
   `execute` retires at trace `[]` writing `v` to `rd`); the five Rocq
   leaves are their instances.
5. Rocq §7's `Print Assumptions` commands are not declarations.

**Rocq → Lean name map.**  `exec_eff_execute_SHIFTIOP_SLLI_gpr`
`execEffExecuteSHIFTIOPSLLIGpr`, `exec_eff_execute_SHIFTIOP_SRLI_gpr`
`execEffExecuteSHIFTIOPSRLIGpr`, `wwp_lui_leaf` `wwpLuiLeaf`,
`wwp_lui_rvc_leaf` `wwpLuiRvcLeaf`, `wwp_auipc_leaf` `wwpAuipcLeaf`,
`wwp_slli_rvc_leaf` `wwpSlliRvcLeaf`, `wwp_srli_rvc_leaf` `wwpSrliRvcLeaf`
(none in the duplicated-name table).  Lean-only (file-qualified):
`WeakLeafUtypeShift.prewritePC`, `prewriteGpr`, `fetchPinRvc0`,
`gprFileValid`, `gprFileUpdate`, `wwpGprFileBaseLeaf`, `wwpGprFileRvcLeaf`.

**Dropped:** nothing (Rocq 7 lemmas; Lean 7 theorems + 7 Lean-only).
-/
import Weak.WeakLeafRegOnly
import Weak.WeakLeafCsrrTime
import Weak.WeakLeafTor
import Weak.WeakLeafLw4
import Weak.WkEntryEff
import Weak.ExecSC
import MachCSL.KCtx

namespace Weak

open Iris Iris.BI Iris.BI.MonPred Iris.ProofMode Iris.Std
open MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D LeanRV64D.Functions

/-! ## 1. THE TWO MISSING `execute` MIRRORS: SHIFTIOP SLLI / SRLI (trace `[]`) -/

/-- Rocq `exec_eff_execute_SHIFTIOP_SLLI_gpr` (deviation 1). -/
theorem execEffExecuteSHIFTIOPSLLIGpr (rs1 rd : BitVec 5) (shamt : BitVec 6) (s : ExecSt) :
    execEff (execute (.SHIFTIOP (shamt, .Regidx rs1, .Regidx rd, .SLLI))) s =
      some (RETIRE_SUCCESS, s.setGpr rd (gprSlliVal rs1 shamt s), []) := by
  show execEff (execute_SHIFTIOP shamt (.Regidx rs1) (.Regidx rd) .SLLI) s = _
  unfold execute_SHIFTIOP gprSlliVal gprSrc
  exec_eff_steps [execEffRXBitsGpr, execEffWXBitsGpr]

/-- Rocq `exec_eff_execute_SHIFTIOP_SRLI_gpr` (deviation 1). -/
theorem execEffExecuteSHIFTIOPSRLIGpr (rs1 rd : BitVec 5) (shamt : BitVec 6) (s : ExecSt) :
    execEff (execute (.SHIFTIOP (shamt, .Regidx rs1, .Regidx rd, .SRLI))) s =
      some (RETIRE_SUCCESS, s.setGpr rd (gprSrliVal rs1 shamt s), []) := by
  show execEff (execute_SHIFTIOP shamt (.Regidx rs1) (.Regidx rd) .SRLI) s = _
  unfold execute_SHIFTIOP gprSrliVal gprSrc
  exec_eff_steps [execEffRXBitsGpr, execEffWXBitsGpr]

/-! ## 1b. Lean-only pure helpers -/

/-- The funnel's two pre-writes leave `PC` alone (Lean-only). -/
theorem WeakLeafUtypeShift.prewritePC (s0 : ExecSt) (b : Bool) (x : BitVec 64) :
    ((s0.setReg .minstret_increment b).setReg .nextPC x).regs .PC = s0.regs .PC := by
  rw [setLookupNe .PC .nextPC _ _ (by decide), setLookupNe .PC .minstret_increment _ _ (by decide)]

/-- The funnel's two pre-writes leave every GPR alone (Lean-only). -/
theorem WeakLeafUtypeShift.prewriteGpr (s0 : ExecSt) (b : Bool) (x : BitVec 64) (j : BitVec 5) :
    ((s0.setReg .minstret_increment b).setReg .nextPC x).gpr j = uxaXget s0.regs j := by
  rw [WeakLeafLw4.gprSetNe _ _ _ _ (by decide), WeakLeafLw4.gprSetNe _ _ _ _ (by decide)]
  rfl

/-- The O2 fetch obligation of a lone compressed-path fetch (Lean-only;
deviation 3). -/
theorem WeakLeafUtypeShift.fetchPinRvc0 (al4 : Bool) (σ : Wmstate) (pc : BitVec 64) :
    (∀ j : Nat, j < 4 → fetchPinned σ (WeakInterp.accAddr pc j)) →
    fetchPin σ [.WEread WeakFetchEff.wakIfetch pc (if al4 then 4 else 2)] := by
  intro h
  refine ⟨fun ak pa n hin _ j hj => ?_, by simp [fetchFresh]⟩
  simp only [List.mem_singleton] at hin
  cases hin
  exact h j (WeakLeafTor.ltFetchW al4 j hj)

/-! ## 1c. Lean-only register-file moves (deviation 2) -/

section gprFileMoves
variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF]

/-- The x0-safe source read off the whole file (Rocq `gpr_file_lookup_acc` +
`gpr_pt_value`, the accessor closed again). -/
theorem WeakLeafUtypeShift.gprFileValid (cpu : CPU) (f : RegFile) (m : RegMap) (i : BitVec 5) :
    regInterp (hlc := hlc) (GF := GF) cpu f ⊢ gprFile cpu m -∗ ⌜uxaXget f i = m.get i⌝ := by
  by_cases hi : i = 0#5
  · subst hi
    iintro - -
    ipureintro
    rw [RegMap.get_zero]
    rfl
  · have hi' : i.toNat ≠ 0 := fun h => hi (BitVec.eq_of_toNat_eq (by simpa using h))
    iintro Hr Hf
    icases gprFile_lookup_acc (GF := GF) cpu m i hi $$ Hf with ⟨Hc, -⟩
    ihave %h := WeakLeafLw4.gprValid cpu f i _ _ hi' $$ Hr Hc
    ipureintro
    rw [RegMap.get_ne _ _ hi]
    exact h

/-- The destination write into the whole file (Rocq `gpr_file_insert_acc` +
`gpr_pt_nz` + `reg_update`). -/
theorem WeakLeafUtypeShift.gprFileUpdate (cpu : CPU) (s : ExecSt) (m : RegMap) (i : BitVec 5)
    (v : BitVec 64) (hi : i.toNat ≠ 0) :
    regInterp (hlc := hlc) (GF := GF) cpu s.regs ⊢ gprFile cpu m -∗
      |==> (regInterp cpu (s.setGpr i v).regs ∗ gprFile cpu (m.set i v)) := by
  have hi0 : i ≠ 0#5 := fun h => hi (by rw [h]; rfl)
  iintro Hr Hf
  icases gprFile_acc (GF := GF) cpu m i hi0 $$ Hf with ⟨Hc, Hclose⟩
  imod WeakLeafLw4.gprUpdate cpu s i (m i) v hi $$ Hr Hc with ⟨Hr, Hc⟩
  imodintro
  isplitl [Hr]
  · iexact Hr
  · iapply Hclose $$ %v Hc

end gprFileMoves

/-! ## 2-6. THE LEAVES -/

section leaves
variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [WeakGS GF]

/-- Lean-only core of §2/§4 (deviation 4): an `F_Base` register-only
instruction writing `v` to `rd`, reading at most `PC` and the source `rs`. -/
theorem WeakLeafUtypeShift.wwpGprFileBaseLeaf (gen : Nat) (cpu : CPU) (al4 : Bool) (pc : BitVec 64)
    (w : BitVec 32) (i : instruction) (rd rs : BitVec 5) (v : BitVec 64) (m : RegMap)
    (npc0 : BitVec 64) (c : MConf) (q : Qp) (D : Register → Bool) (dst : ExecSt) (ws : Wstate) :
    gen = 0 →
    MConf.mok c →
    pmpAllowsAll c.pmpcfg →
    is_aligned_vaddr (.Virtaddr pc) 2 = true →
    is_aligned_vaddr (.Virtaddr pc) 4 = al4 →
    rd.toNat ≠ 0 →
    is_lpad_instruction i = false →
    (∀ s : ExecSt, s.regs .PC = pc → s.gpr rs = m.get rs →
      execEff (execute i) s = some (RETIRE_SUCCESS, s.setGpr rd v, [])) →
    (∀ t : ExecSt,
      privMSU (t.regs .cur_privilege) = true →
      (_get_Misa_C (t.regs .misa) == 1#1) = true →
      (_get_Misa_A (t.regs .misa) == 1#1) = true →
      t.regs .misa = misaC →
      cfgOk t →
      exec (decodeFetch (.F_Base w)) t = some (i, t)) →
    (∀ rs : RegFile,
      rs .cur_privilege = .Machine →
      rs .misa = misaC →
      rs .mseccfg = 0#64 →
      ∀ r, D r = true → rs r = dst.regs r) →
    D .minstret_increment = false →
    goodb0 D (ext_decode w) dst = true →
    exec (ext_decode w) dst = some (i, dst) →
    mConf (GF := GF) cpu (DFrac.own q) c ⊢
      clockCells cpu -∗
      Register.PC ↦ᵣ[cpu] pc -∗
      Register.nextPC ↦ᵣ[cpu] npc0 -∗
      gprFile cpu m -∗
      winstrBytes (GF := GF) pc (.F_Base w) -∗
      hartWs (GF := GF) cpu ws -∗
      (∀ ws' : Wstate,
        ⌜wsLe ws ws'⌝ -∗
        mConf cpu (DFrac.own q) c -∗
        clockCells cpu -∗
        pcIs cpu (BitVec.addInt pc 4) -∗
        gprFile cpu (m.set rd v) -∗
        hartWs cpu ws' -∗
        wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu)) -∗
      wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu) := by
  intro hgid hmok hpmp hal2 hal4 hrd hnlpad hrun hdecf hagree hDmi hgood hdec
  iintro Hm Hclk Hpc Hnpc Hfile #Hbs Hhws Hcont
  ihave %haccpc := winstrBytesAccWf pc (.F_Base w) $$ Hbs
  have hacc0 : accWf pc 0 := by unfold accWf at haccpc ⊢; omega
  ihave %hnotRVC := WeakLeafLw4.winstrBytesNotRVC pc w $$ Hbs
  have hdecW : winstrDec (.F_Base w) i := by
    intro t h1 h2 h3 h4 h5
    simp only [fetchIsRvc, Bool.false_eq_true, ↓reduceIte]
    exact hdecf t h1 h2 h3 h4 h5
  ihave #Hwi := winstrIntro (GF := GF) pc false i (.F_Base w) hnlpad rfl hdecW $$ Hbs
  iapply wwpInstr gen cpu pc false i c (DFrac.own q)
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
  -- the source read (x0-safe; nothing is taken out of the file)
  icases keepPure (WeakLeafUtypeShift.gprFileValid cpu _ m rs) $$ Hreg Hfile with ⟨%Lrsa, Hreg, Hfile⟩
  have Lrs : uxaXget σ.wmRegs rs = m.get rs := by
    have h := WeakLeafLw4.gprSetNe (wflatSt σ) .minstret_increment b rs (by decide)
    unfold ExecSt.gpr at h
    rw [← Lrsa, h]
    rfl
  -- the `execute` at any pre-written state over σ's registers
  have hrunAt : ∀ (s0 : ExecSt) (b' : Bool) (x : BitVec 64), s0.regs = σ.wmRegs →
      execEff (execute i) ((s0.setReg .minstret_increment b').setReg .nextPC x) =
        some (RETIRE_SUCCESS, ((s0.setReg .minstret_increment b').setReg .nextPC x).setGpr rd v,
          []) := by
    intro s0 b' x hs
    apply hrun
    · rw [WeakLeafUtypeShift.prewritePC, hs]; exact Lpc0
    · rw [WeakLeafUtypeShift.prewriteGpr, hs]; exact Lrs
  -- premise (c): the execute mirror, at the CONFINED state
  have hc : ∀ b' : Bool, ∃ sExec : ExecSt,
      execEff (execute i)
        (((⟨σ.wmRegs, wmemRestrict σ (wwin pc pc 0), σ.wmDev⟩ : ExecSt).setReg
          .minstret_increment b').setReg .nextPC (BitVec.addInt pc 4)) =
        some (.Retire_Success (), sExec, []) ∧
      sExec.regs .hart_state = .HART_ACTIVE () ∧
      sExec.regs .minstret_increment = b' ∧
      bmDomSub sExec.mem (wwin pc pc 0) := by
    intro b'
    obtain ⟨F1, F2, F3, -, -⟩ := loadSexecFacts
      (⟨σ.wmRegs, wmemRestrict σ (wwin pc pc 0), σ.wmDev⟩ : ExecSt) b' (BitVec.addInt pc 4) rd v
    refine ⟨_, hrunAt (⟨σ.wmRegs, wmemRestrict σ (wwin pc pc 0), σ.wmDev⟩ : ExecSt) b' _ rfl, ?_, F2,
      ?_⟩
    · rw [F1]; exact Lhart
    · rw [F3]; exact wmemRestrictDom σ _
  -- the certificate's precondition
  have HP : wPEff (some cpu.val) (regonlyEs al4 pc) σ :=
    wPEffOfLeafRegonly al4 cpu.val σ (wwin pc pc 0) pc w i D dst hwf
      (wwinNonzero pc pc 0 (fun j hj => WeakLeafWin.inRamByte pc 4 j hram hj) (win0Absurd _))
      (wwinPinned σ pc pc 0 haccpc hacc0 (fun j hj => (htp j hj).1) (win0Absurd _))
      (fetchPinOfText σ pc _ (WeakLeafCsrrTime.fetchInWindowRegonly al4 pc haccpc)
        (WeakLeafCsrrTime.fetchFreshRegonly al4 pc) (fun j hj => (htp j hj).2))
      Lpc0 Lpriv (by rw [Lpmpc]; exact hpmp) Lpma Lhtif Lhart LmisaS (by rw [Lmisa]; decide) LmIE Lelp
      hal2 hal4 hram (wwinConfText σ pc pc 0 w htext0) hnotRVC (hagree σ.wmRegs Lpriv Lmisa Lsec) hDmi
      hgood hdec hnlpad hc
  -- the run at the FLAT state
  have hexf := hrunAt (wflatSt σ) b (BitVec.addInt pc 4) rfl
  have hfacts := loadSexecFacts (wflatSt σ) b (BitVec.addInt pc 4) rd v
  -- the two register writes the `execute` performs
  imod (wand_intro (reg_update cpu _ .nextPC npc0 (BitVec.addInt pc 4))) $$ Hreg Hnpc with ⟨Hreg, Hnpc⟩
  rw [show (((wflatSt σ).setReg .minstret_increment b).regs.set .nextPC (BitVec.addInt pc 4)) =
      (((wflatSt σ).setReg .minstret_increment b).setReg .nextPC (BitVec.addInt pc 4)).regs from rfl]
  imod WeakLeafUtypeShift.gprFileUpdate cpu (((wflatSt σ).setReg .minstret_increment b).setReg .nextPC
      (BitVec.addInt pc 4)) m rd v hrd $$ Hreg Hfile with ⟨Hreg, Hfile⟩
  iapply fupd_mask_intro LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro; exact HP
  iexists ((((wflatSt σ).setReg .minstret_increment b).setReg .nextPC (BitVec.addInt pc 4)).setGpr rd v)
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
  · iapply Hcont $$ %σ'.wmWs %hwsle Hm' Hclk' [Hpc' Hnpc] Hfile Hhws
    unfold pcIs
    iframe Hpc' Hnpc

/-- Lean-only core of §3/§5/§6 (deviation 4): a COMPRESSED register-only
instruction (expanding to `i`) writing `v` to `rd`, reading at most `PC` and
the source `rs`. -/
theorem WeakLeafUtypeShift.wwpGprFileRvcLeaf (gen : Nat) (cpu : CPU) (al4 : Bool) (pc : BitVec 64)
    (h : BitVec 16) (i0 i : instruction) (rd rs : BitVec 5) (v : BitVec 64) (m : RegMap)
    (npc0 : BitVec 64) (c : MConf) (q : Qp) (D D0 : Register → Bool) (dst : ExecSt) (ws : Wstate) :
    gen = 0 →
    MConf.mok c →
    pmpAllowsAll c.pmpcfg →
    is_aligned_vaddr (.Virtaddr pc) 2 = true →
    is_aligned_vaddr (.Virtaddr pc) 4 = al4 →
    rd.toNat ≠ 0 →
    is_lpad_instruction i = false →
    (∀ s : ExecSt, s.regs .PC = pc → s.gpr rs = m.get rs →
      execEff (execute i) s = some (RETIRE_SUCCESS, s.setGpr rd v, [])) →
    (∀ t : ExecSt,
      privMSU (t.regs .cur_privilege) = true →
      (_get_Misa_C (t.regs .misa) == 1#1) = true →
      (_get_Misa_A (t.regs .misa) == 1#1) = true →
      t.regs .misa = misaC →
      cfgOk t →
      ∃ i0' : instruction,
        exec (decodeFetch (.F_RVC h)) t = some (i0', t) ∧
        is_lpad_instruction i0' = false ∧
        (∀ s : ExecSt, exec (execute i0') s = some (.ExecuteAs i, s))) →
    (∀ rs : RegFile,
      rs .cur_privilege = .Machine →
      rs .misa = misaC →
      rs .mseccfg = 0#64 →
      ∀ r, D r = true → rs r = dst.regs r) →
    D .minstret_increment = false →
    goodb0 D (ext_decode_compressed h) dst = true →
    exec (ext_decode_compressed h) dst = some (i0, dst) →
    (∀ s : ExecSt, goodb0 D0 (execute i0) s = true) →
    (∀ s : ExecSt, exec (execute i0) s = some (.ExecuteAs i, s)) →
    mConf (GF := GF) cpu (DFrac.own q) c ⊢
      clockCells cpu -∗
      Register.PC ↦ᵣ[cpu] pc -∗
      Register.nextPC ↦ᵣ[cpu] npc0 -∗
      gprFile cpu m -∗
      winstrBytes (GF := GF) pc (.F_RVC h) -∗
      hartWs (GF := GF) cpu ws -∗
      (∀ ws' : Wstate,
        ⌜wsLe ws ws'⌝ -∗
        mConf cpu (DFrac.own q) c -∗
        clockCells cpu -∗
        pcIs cpu (BitVec.addInt pc 2) -∗
        gprFile cpu (m.set rd v) -∗
        hartWs cpu ws' -∗
        wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu)) -∗
      wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu) := by
  intro hgid hmok hpmp hal2 hal4 hrd hnlpad hrun hdecf hagree hDmi hgood hdec hgood0 hexp
  iintro Hm Hclk Hpc Hnpc Hfile #Hbs Hhws Hcont
  ihave %haccpc := winstrBytesAccWf pc (.F_RVC h) $$ Hbs
  have hacc0 : accWf pc 0 := by unfold accWf at haccpc ⊢; omega
  have hdecW : winstrDec (.F_RVC h) i := by
    intro t h1 h2 h3 h4 h5
    simp only [fetchIsRvc, ↓reduceIte]
    exact hdecf t h1 h2 h3 h4 h5
  ihave #Hwi := winstrIntro (GF := GF) pc true i (.F_RVC h) hnlpad rfl hdecW $$ Hbs
  iapply wwpInstr gen cpu pc true i c (DFrac.own q)
    (wPEff (some cpu.val) [.WEread WeakFetchEff.wakIfetch pc (if al4 then 4 else 2)])
    (wQFr wQPure (some cpu.val) [.WEread WeakFetchEff.wakIfetch pc (if al4 then 4 else 2)])
    hgid haccpc hmok hpmp
    (wstepCertFr _ _ _ _ (wcertNowrite cpu.val pc
      [.WEread WeakFetchEff.wakIfetch pc (if al4 then 4 else 2)]
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
  -- the source read (x0-safe; nothing is taken out of the file)
  icases keepPure (WeakLeafUtypeShift.gprFileValid cpu _ m rs) $$ Hreg Hfile with ⟨%Lrsa, Hreg, Hfile⟩
  have Lrs : uxaXget σ.wmRegs rs = m.get rs := by
    have h := WeakLeafLw4.gprSetNe (wflatSt σ) .minstret_increment b rs (by decide)
    unfold ExecSt.gpr at h
    rw [← Lrsa, h]
    rfl
  have hrunAt : ∀ (s0 : ExecSt) (b' : Bool) (x : BitVec 64), s0.regs = σ.wmRegs →
      execEff (execute i) ((s0.setReg .minstret_increment b').setReg .nextPC x) =
        some (RETIRE_SUCCESS, ((s0.setReg .minstret_increment b').setReg .nextPC x).setGpr rd v,
          []) := by
    intro s0 b' x hs
    apply hrun
    · rw [WeakLeafUtypeShift.prewritePC, hs]; exact Lpc0
    · rw [WeakLeafUtypeShift.prewriteGpr, hs]; exact Lrs
  have hc : ∀ b' : Bool, ∃ sExec : ExecSt,
      execEff (execute i)
        (((⟨σ.wmRegs, wmemRestrict σ (wwin pc pc 0), σ.wmDev⟩ : ExecSt).setReg
          .minstret_increment b').setReg .nextPC (BitVec.addInt pc 2)) =
        some (.Retire_Success (), sExec, []) ∧
      sExec.regs .hart_state = .HART_ACTIVE () ∧
      sExec.regs .minstret_increment = b' ∧
      bmDomSub sExec.mem (wwin pc pc 0) := by
    intro b'
    obtain ⟨F1, F2, F3, -, -⟩ := loadSexecFacts
      (⟨σ.wmRegs, wmemRestrict σ (wwin pc pc 0), σ.wmDev⟩ : ExecSt) b' (BitVec.addInt pc 2) rd v
    refine ⟨_, hrunAt (⟨σ.wmRegs, wmemRestrict σ (wwin pc pc 0), σ.wmDev⟩ : ExecSt) b' _ rfl, ?_, F2,
      ?_⟩
    · rw [F1]; exact Lhart
    · rw [F3]; exact wmemRestrictDom σ _
  -- the certificate's precondition
  have HP : wPEff (some cpu.val) [.WEread WeakFetchEff.wakIfetch pc (if al4 then 4 else 2)] σ := by
    have := wPEffOfLeafRvc al4 cpu.val σ (wwin pc pc 0) pc h w i0 i [] D D0 dst hwf
      (wwinNonzero pc pc 0 (fun j hj => WeakLeafWin.inRamByte pc 4 j hram hj) (win0Absurd _))
      (wwinPinned σ pc pc 0 haccpc hacc0 (fun j hj => (htp j hj).1) (win0Absurd _))
      (by simpa only [List.append_nil] using
        WeakLeafUtypeShift.fetchPinRvc0 al4 σ pc (fun j hj => (htp j hj).2))
      Lpc0 Lpriv (by rw [Lpmpc]; exact hpmp) Lpma Lhtif Lhart LmisaS (by rw [Lmisa]; decide) LmIE Lelp
      hal2 hal4 hram (wwinConfText σ pc pc 0 w htext0) hsub hisRVC (hagree σ.wmRegs Lpriv Lmisa Lsec)
      hDmi hgood hdec hgood0 hexp hc
    simpa only [List.append_nil] using this
  -- the run at the FLAT state
  have hexf := hrunAt (wflatSt σ) b (BitVec.addInt pc 2) rfl
  have hfacts := loadSexecFacts (wflatSt σ) b (BitVec.addInt pc 2) rd v
  imod (wand_intro (reg_update cpu _ .nextPC npc0 (BitVec.addInt pc 2))) $$ Hreg Hnpc with ⟨Hreg, Hnpc⟩
  rw [show (((wflatSt σ).setReg .minstret_increment b).regs.set .nextPC (BitVec.addInt pc 2)) =
      (((wflatSt σ).setReg .minstret_increment b).setReg .nextPC (BitVec.addInt pc 2)).regs from rfl]
  imod WeakLeafUtypeShift.gprFileUpdate cpu (((wflatSt σ).setReg .minstret_increment b).setReg .nextPC
      (BitVec.addInt pc 2)) m rd v hrd $$ Hreg Hfile with ⟨Hreg, Hfile⟩
  iapply fupd_mask_intro LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro; exact HP
  iexists ((((wflatSt σ).setReg .minstret_increment b).setReg .nextPC (BitVec.addInt pc 2)).setGpr rd v)
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
  · iapply Hcont $$ %σ'.wmWs %hwsle Hm' Hclk' [Hpc' Hnpc] Hfile Hhws
    unfold pcIs
    iframe Hpc' Hnpc

/-! ## 2. `lui` -- `F_Base` fetch, alignment-generic -/

/-- Rocq `wwp_lui_leaf` (deviations 2-4). -/
theorem wwpLuiLeaf (gen : Nat) (cpu : CPU) (al4 : Bool) (pc : BitVec 64) (w : BitVec 32)
    (rd : BitVec 5) (imm : BitVec 20) (m : RegMap) (npc0 : BitVec 64) (c : MConf) (q : Qp)
    (D : Register → Bool) (dst : ExecSt) (ws : Wstate) :
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
      exec (decodeFetch (.F_Base w)) t = some (.UTYPE (imm, .Regidx rd, .LUI), t)) →
    (∀ rs : RegFile,
      rs .cur_privilege = .Machine →
      rs .misa = misaC →
      rs .mseccfg = 0#64 →
      ∀ r, D r = true → rs r = dst.regs r) →
    D .minstret_increment = false →
    goodb0 D (ext_decode w) dst = true →
    exec (ext_decode w) dst = some (.UTYPE (imm, .Regidx rd, .LUI), dst) →
    mConf (GF := GF) cpu (DFrac.own q) c ⊢
      clockCells cpu -∗
      Register.PC ↦ᵣ[cpu] pc -∗
      Register.nextPC ↦ᵣ[cpu] npc0 -∗
      gprFile cpu m -∗
      winstrBytes (GF := GF) pc (.F_Base w) -∗
      hartWs (GF := GF) cpu ws -∗
      (∀ ws' : Wstate,
        ⌜wsLe ws ws'⌝ -∗
        mConf cpu (DFrac.own q) c -∗
        clockCells cpu -∗
        pcIs cpu (BitVec.addInt pc 4) -∗
        gprFile cpu (m.set rd (WkEntryEff.luival imm)) -∗
        hartWs cpu ws' -∗
        wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu)) -∗
      wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu) := by
  intro hgid hmok hpmp hal2 hal4 hrd hdecf hagree hDmi hgood hdec
  exact WeakLeafUtypeShift.wwpGprFileBaseLeaf gen cpu al4 pc w _ rd rd _ m npc0 c q D dst ws hgid hmok
    hpmp hal2 hal4 hrd rfl (fun s _ _ => execEffExecuteUTYPELUIGpr rd imm s) hdecf hagree hDmi hgood
    hdec

/-! ## 3. `c.lui` -- the SAME UTYPE LUI ast through a COMPRESSED decode -/

/-- Rocq `wwp_lui_rvc_leaf` (deviations 2-4). -/
theorem wwpLuiRvcLeaf (gen : Nat) (cpu : CPU) (al4 : Bool) (pc : BitVec 64) (h : BitVec 16)
    (rd : BitVec 5) (imm : BitVec 20) (i0 : instruction) (m : RegMap) (npc0 : BitVec 64) (c : MConf)
    (q : Qp) (D D0 : Register → Bool) (dst : ExecSt) (ws : Wstate) :
    gen = 0 →
    MConf.mok c →
    pmpAllowsAll c.pmpcfg →
    is_aligned_vaddr (.Virtaddr pc) 2 = true →
    is_aligned_vaddr (.Virtaddr pc) 4 = al4 →
    rd.toNat ≠ 0 →
    (∀ t : ExecSt,
      privMSU (t.regs .cur_privilege) = true →
      (_get_Misa_C (t.regs .misa) == 1#1) = true →
      (_get_Misa_A (t.regs .misa) == 1#1) = true →
      t.regs .misa = misaC →
      cfgOk t →
      ∃ i0' : instruction,
        exec (decodeFetch (.F_RVC h)) t = some (i0', t) ∧
        is_lpad_instruction i0' = false ∧
        (∀ s : ExecSt, exec (execute i0') s = some (.ExecuteAs (.UTYPE (imm, .Regidx rd, .LUI)), s))) →
    (∀ rs : RegFile,
      rs .cur_privilege = .Machine →
      rs .misa = misaC →
      rs .mseccfg = 0#64 →
      ∀ r, D r = true → rs r = dst.regs r) →
    D .minstret_increment = false →
    goodb0 D (ext_decode_compressed h) dst = true →
    exec (ext_decode_compressed h) dst = some (i0, dst) →
    (∀ s : ExecSt, goodb0 D0 (execute i0) s = true) →
    (∀ s : ExecSt, exec (execute i0) s = some (.ExecuteAs (.UTYPE (imm, .Regidx rd, .LUI)), s)) →
    mConf (GF := GF) cpu (DFrac.own q) c ⊢
      clockCells cpu -∗
      Register.PC ↦ᵣ[cpu] pc -∗
      Register.nextPC ↦ᵣ[cpu] npc0 -∗
      gprFile cpu m -∗
      winstrBytes (GF := GF) pc (.F_RVC h) -∗
      hartWs (GF := GF) cpu ws -∗
      (∀ ws' : Wstate,
        ⌜wsLe ws ws'⌝ -∗
        mConf cpu (DFrac.own q) c -∗
        clockCells cpu -∗
        pcIs cpu (BitVec.addInt pc 2) -∗
        gprFile cpu (m.set rd (WkEntryEff.luival imm)) -∗
        hartWs cpu ws' -∗
        wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu)) -∗
      wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu) := by
  intro hgid hmok hpmp hal2 hal4 hrd hdecf hagree hDmi hgood hdec hgood0 hexp
  exact WeakLeafUtypeShift.wwpGprFileRvcLeaf gen cpu al4 pc h i0 _ rd rd _ m npc0 c q D D0 dst ws hgid
    hmok hpmp hal2 hal4 hrd rfl (fun s _ _ => execEffExecuteUTYPELUIGpr rd imm s) hdecf hagree hDmi
    hgood hdec hgood0 hexp

/-! ## 4. `auipc` -- `F_Base` fetch, alignment-generic -/

/-- Rocq `wwp_auipc_leaf` (deviations 2-4). -/
theorem wwpAuipcLeaf (gen : Nat) (cpu : CPU) (al4 : Bool) (pc : BitVec 64) (w : BitVec 32)
    (rd : BitVec 5) (imm : BitVec 20) (m : RegMap) (npc0 : BitVec 64) (c : MConf) (q : Qp)
    (D : Register → Bool) (dst : ExecSt) (ws : Wstate) :
    gen = 0 →
    MConf.mok c →
    pmpAllowsAll c.pmpcfg →
    is_aligned_vaddr (.Virtaddr pc) 2 = true →
    is_aligned_vaddr (.Virtaddr pc) 4 = al4 →
    rd.toNat ≠ 0 →
    (∀ t : ExecSt,
      privMSU (t.regs .cur_privilege) = true →
      (_get_Misa_C (t.regs .misa) == 1#1) = true →
      (_get_Misa_A (t.regs .misa) == 1#1) = true →
      t.regs .misa = misaC →
      cfgOk t →
      exec (decodeFetch (.F_Base w)) t = some (.UTYPE (imm, .Regidx rd, .AUIPC), t)) →
    (∀ rs : RegFile,
      rs .cur_privilege = .Machine →
      rs .misa = misaC →
      rs .mseccfg = 0#64 →
      ∀ r, D r = true → rs r = dst.regs r) →
    D .minstret_increment = false →
    goodb0 D (ext_decode w) dst = true →
    exec (ext_decode w) dst = some (.UTYPE (imm, .Regidx rd, .AUIPC), dst) →
    mConf (GF := GF) cpu (DFrac.own q) c ⊢
      clockCells cpu -∗
      Register.PC ↦ᵣ[cpu] pc -∗
      Register.nextPC ↦ᵣ[cpu] npc0 -∗
      gprFile cpu m -∗
      winstrBytes (GF := GF) pc (.F_Base w) -∗
      hartWs (GF := GF) cpu ws -∗
      (∀ ws' : Wstate,
        ⌜wsLe ws ws'⌝ -∗
        mConf cpu (DFrac.own q) c -∗
        clockCells cpu -∗
        pcIs cpu (BitVec.addInt pc 4) -∗
        gprFile cpu (m.set rd (pc + auipcOff imm)) -∗
        hartWs cpu ws' -∗
        wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu)) -∗
      wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu) := by
  intro hgid hmok hpmp hal2 hal4 hrd hdecf hagree hDmi hgood hdec
  refine WeakLeafUtypeShift.wwpGprFileBaseLeaf gen cpu al4 pc w _ rd rd _ m npc0 c q D dst ws hgid hmok
    hpmp hal2 hal4 hrd rfl (fun s hpc _ => ?_) hdecf hagree hDmi hgood hdec
  rw [execEffExecuteUTYPEAUIPCGpr, hpc]

/-! ## 5. `c.slli` -- SHIFTIOP SLLI through a COMPRESSED decode -/

/-- Rocq `wwp_slli_rvc_leaf` (deviations 1-4). -/
theorem wwpSlliRvcLeaf (gen : Nat) (cpu : CPU) (al4 : Bool) (pc : BitVec 64) (h : BitVec 16)
    (rs1 rd : BitVec 5) (shamt : BitVec 6) (i0 : instruction) (m : RegMap) (npc0 : BitVec 64)
    (c : MConf) (q : Qp) (D D0 : Register → Bool) (dst : ExecSt) (ws : Wstate) :
    gen = 0 →
    MConf.mok c →
    pmpAllowsAll c.pmpcfg →
    is_aligned_vaddr (.Virtaddr pc) 2 = true →
    is_aligned_vaddr (.Virtaddr pc) 4 = al4 →
    rd.toNat ≠ 0 →
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
          some (.ExecuteAs (.SHIFTIOP (shamt, .Regidx rs1, .Regidx rd, .SLLI)), s))) →
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
      some (.ExecuteAs (.SHIFTIOP (shamt, .Regidx rs1, .Regidx rd, .SLLI)), s)) →
    mConf (GF := GF) cpu (DFrac.own q) c ⊢
      clockCells cpu -∗
      Register.PC ↦ᵣ[cpu] pc -∗
      Register.nextPC ↦ᵣ[cpu] npc0 -∗
      gprFile cpu m -∗
      winstrBytes (GF := GF) pc (.F_RVC h) -∗
      hartWs (GF := GF) cpu ws -∗
      (∀ ws' : Wstate,
        ⌜wsLe ws ws'⌝ -∗
        mConf cpu (DFrac.own q) c -∗
        clockCells cpu -∗
        pcIs cpu (BitVec.addInt pc 2) -∗
        gprFile cpu (m.set rd (shift_bits_left (m.get rs1)
          (Sail.BitVec.extractLsb shamt (Functions.log2_xlen -i 1) 0))) -∗
        hartWs cpu ws' -∗
        wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu)) -∗
      wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu) := by
  intro hgid hmok hpmp hal2 hal4 hrd hdecf hagree hDmi hgood hdec hgood0 hexp
  refine WeakLeafUtypeShift.wwpGprFileRvcLeaf gen cpu al4 pc h i0 _ rd rs1 _ m npc0 c q D D0 dst ws
    hgid hmok hpmp hal2 hal4 hrd rfl (fun s _ hrs => ?_) hdecf hagree hDmi hgood hdec hgood0 hexp
  rw [execEffExecuteSHIFTIOPSLLIGpr]
  unfold gprSlliVal gprSrc
  rw [hrs]

/-! ## 6. `c.srli` -- SHIFTIOP SRLI through a COMPRESSED decode -/

/-- Rocq `wwp_srli_rvc_leaf` (deviations 1-4). -/
theorem wwpSrliRvcLeaf (gen : Nat) (cpu : CPU) (al4 : Bool) (pc : BitVec 64) (h : BitVec 16)
    (rs1 rd : BitVec 5) (shamt : BitVec 6) (i0 : instruction) (m : RegMap) (npc0 : BitVec 64)
    (c : MConf) (q : Qp) (D D0 : Register → Bool) (dst : ExecSt) (ws : Wstate) :
    gen = 0 →
    MConf.mok c →
    pmpAllowsAll c.pmpcfg →
    is_aligned_vaddr (.Virtaddr pc) 2 = true →
    is_aligned_vaddr (.Virtaddr pc) 4 = al4 →
    rd.toNat ≠ 0 →
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
          some (.ExecuteAs (.SHIFTIOP (shamt, .Regidx rs1, .Regidx rd, .SRLI)), s))) →
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
      some (.ExecuteAs (.SHIFTIOP (shamt, .Regidx rs1, .Regidx rd, .SRLI)), s)) →
    mConf (GF := GF) cpu (DFrac.own q) c ⊢
      clockCells cpu -∗
      Register.PC ↦ᵣ[cpu] pc -∗
      Register.nextPC ↦ᵣ[cpu] npc0 -∗
      gprFile cpu m -∗
      winstrBytes (GF := GF) pc (.F_RVC h) -∗
      hartWs (GF := GF) cpu ws -∗
      (∀ ws' : Wstate,
        ⌜wsLe ws ws'⌝ -∗
        mConf cpu (DFrac.own q) c -∗
        clockCells cpu -∗
        pcIs cpu (BitVec.addInt pc 2) -∗
        gprFile cpu (m.set rd (shift_bits_right (m.get rs1)
          (Sail.BitVec.extractLsb shamt (Functions.log2_xlen -i 1) 0))) -∗
        hartWs cpu ws' -∗
        wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu)) -∗
      wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu) := by
  intro hgid hmok hpmp hal2 hal4 hrd hdecf hagree hDmi hgood hdec hgood0 hexp
  refine WeakLeafUtypeShift.wwpGprFileRvcLeaf gen cpu al4 pc h i0 _ rd rs1 _ m npc0 c q D D0 dst ws
    hgid hmok hpmp hal2 hal4 hrd rfl (fun s _ hrs => ?_) hdecf hagree hDmi hgood hdec hgood0 hexp
  rw [execEffExecuteSHIFTIOPSRLIGpr]
  unfold gprSrliVal gprSrc
  rw [hrs]

end leaves

end Weak
