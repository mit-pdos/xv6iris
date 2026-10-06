/-
Weak: **the weak REGISTER-ONLY ITYPE leaves** (M4, start/timerinit) -- the
weak twins of `WpMmodeItype`'s two register-generic I-type leaves
(`wp_addi_gpr` / `wp_ori_gpr`), stated over the WHOLE GPR file.

Rocq: `iris/WeakLeafItype.v` @ xxvzwolszwmp.

The Rocq header, in substance.  The `start()` / `timerinit()` call sites have
`rd = rs1` and `rs1 = x0` all over, and separate per-register cells cannot
express either, so the leaves take the whole register file.  Three leaves:
* §2 `wwpAddiLeaf`    -- `addi rd, rs1, imm` at an `F_Base` fetch;
* §3 `wwpAddiRvcLeaf` -- the SAME `ITYPE … ADDI` reached through a COMPRESSED
  decode (what `c.addi` / `c.li` / `c.addi4spn` expand to), at an `F_RVC` fetch;
* §4 `wwpOriLeaf`     -- `ori rd, rs1, imm` at an `F_Base` fetch.
Every leaf takes the fetch alignment `al4` as a PARAMETER: the `F_Base` pair
goes through `WeakLeafRegOnly.wPEffOfLeafRegonly` + `wcertRegonly`, the
compressed one through `WeakLeafTor.wPEffOfLeafRvc` at `es_x := []` (whose
conclusion is the single fetch element, certified by `WeakEff.wcertNowrite`).
Nothing touches memory: the window is the text-only `wwin pc pc 0` and the
certificate's `Q` is `wQPure`.  ADDI's `execute` mirror is
`WkEntryEff.execEffExecuteITYPEADDIGpr`, reused; ORI's (§1) is that script at
the ORI arm.

**Deviations from Rocq.**
1. VOCABULARY: the `Weak/ExecSC*.lean` / `Weak/WeakLeafLw4.lean` conventions
   (`register_lookup r s.(sregs)` ↦ `s.regs r`, `set_reg` ↦ `ExecSt.setReg`,
   `add_vec_int` ↦ `BitVec.addInt`, `mword n` ↦ `BitVec n`, `uint x <> 0` ↦
   `x.toNat ≠ 0`, `sign_extend' 64 imm` ↦ `sign_extend (m := 64) imm`,
   `add_vec`/`or_vec` ↦ `+`/`|||`, `regval_into_reg v` ↦ `v`).  The x0-safe
   source read `if uint rs1 =? 0 then zero_reg else register_lookup
   (R_bitvector_64 (gpr_of_Z (uint rs1))) …` is `s.gpr rs1` (`uxaXget` at a
   bare register file); the destination write is `setGpr rd x` (equal under
   the kept premise `rd.toNat ≠ 0`).  The ORI mirror is stated over
   `ExecSC.gprOriVal` and `s.setGpr` (`Weak/WkEntryEff.lean` deviation 5).
2. THE REGISTER FILE: Rocq `gpr_file m` (`m : regidx → mword 64`, the x0 entry
   asserting `m x0 = zero_reg`) ↦ `MachCSL.gprFile cpu m` (`m : RegMap`, the
   x0 slot meaningless); the operand `m !!! Regidx rs1` ↦ `m.get rs1` (reads 0
   at x0, as Rocq's pinned x0 entry); `<[Regidx rd := v]> m` ↦ `m.set rd v`.
   Rocq's `gpr_file_lookup_acc` + `gpr_pt_value` (the read) and
   `gpr_file_insert_acc` + `gpr_pt_nz` + `reg_update` (the write) are the
   Lean-only `WeakLeafItype.gprFileValue` / `WeakLeafItype.gprFileWrite`
   (over `MachCSL.gprFile_lookup_acc`/`gprFile_acc` and
   `WeakLeafLw4.gprValid`/`gprUpdate`).
3. THE CONFIG INTERFACE (owner decision Q3, `Weak/WeakFunnel.lean`
   deviation 7, as `Weak/WeakLeafCsrrTime.lean` deviation 7): Rocq
   `mmode_config (DfracOwn q) -∗ pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0` ↦
   `mConf cpu (DFrac.own q) c ∗ clockCells cpu` (`pmpcfg0 := c.pmpcfg`, the
   premise `pmp_allows_all pmpcfg0` ↦ `pmpAllowsAll c.pmpcfg`, plus
   `MConf.mok c`); the continuation gets the same back.  `GenId`/`CpuId` are
   the explicit `gen`/`cpu`; `WWP Loop` ↦ `wwpTriv ⊤ (WExpr.loop gen cpu)`;
   `pc_is` ↦ `pcIs`; `hart_ws cpu_id` ↦ `hartWs cpu`; the decode premises are
   over the funnel's vocabulary (`privMSU`, `misaC`, `cfgOk`, `decodeFetch`;
   the agreement premise quantifies over a `RegFile`, `mword_of_int 0` ↦
   `0#64`).
4. O2 (owner decision): the fetch elements are `.WEread WeakFetchEff.wakIfetch …`
   (Rocq `WEread wak_plain …`); the recipes' fetch pin is discharged from
   `winstrTextPinned` (`WeakLeafCsrrTime.fetchInWindowRegonly` /
   `fetchFreshRegonly` for `F_Base`; the Lean-only `WeakLeafItype.fetchPinRvc0`
   for the single compressed read).
5. PROOF SHARING: Rocq's three leaf scripts are one script copied thrice.
   Here the `F_Base` pair is one Lean-only theorem
   `WeakLeafItype.wwpGprBaseLeaf`, generic in the instruction `i` and the
   operand map `op` (any `execute i` with mirror `s.setGpr rd (op (s.gpr rs1))`
   at the empty trace); the compressed leaf likewise rests on
   `WeakLeafItype.wwpGprRvcLeaf`.  The three Rocq statements are kept as
   instantiations.
6. `gpr_src_peel_npc` / `gpr_src_at_flat` state the read as `s.gpr rs1`
   (deviation 1); `gpr_src_at_flat`'s right side is `uxaXget σ.wmRegs rs1`.
7. Rocq §5's `Print Assumptions` commands are not declarations.

**Rocq → Lean name map.**  `exec_eff_execute_ITYPE_ORI_gpr`
`execEffExecuteITYPEORIGpr`, `gpr_src_peel_npc` `gprSrcPeelNpc`,
`gpr_src_at_flat` `gprSrcAtFlat`, `wwp_addi_leaf` `wwpAddiLeaf`,
`wwp_addi_rvc_leaf` `wwpAddiRvcLeaf`, `wwp_ori_leaf` `wwpOriLeaf` (none in the
duplicated-name table).  Lean-only (file-qualified): `WeakLeafItype.gprFileValue`,
`WeakLeafItype.gprFileWrite`, `WeakLeafItype.fetchPinRvc0`,
`WeakLeafItype.wwpGprBaseLeaf`, `WeakLeafItype.wwpGprRvcLeaf`.

**Dropped:** nothing (Rocq 6 lemmas; Lean 6 theorems + 5 Lean-only).
-/
import Weak.WeakLeafCsrrTime
import Weak.WeakLeafTor
import Weak.WkEntryEff
import MachCSL.KCtx

namespace Weak

open Iris Iris.BI Iris.BI.MonPred Iris.ProofMode Iris.Std
open MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D LeanRV64D.Functions

/-! ## 1. The ORI `execute` mirror, and the source-register peel -/

/-- Rocq `exec_eff_execute_ITYPE_ORI_gpr` (deviation 1). -/
theorem execEffExecuteITYPEORIGpr (rs1 rd : BitVec 5) (imm : BitVec 12) (s : ExecSt) :
    execEff (execute (.ITYPE (imm, .Regidx rs1, .Regidx rd, .ORI))) s =
      some (RETIRE_SUCCESS, s.setGpr rd (gprOriVal rs1 imm s), []) := by
  show execEff (execute_ITYPE imm (.Regidx rs1) (.Regidx rd) .ORI) s = _
  unfold execute_ITYPE gprOriVal
  exec_eff_steps [execEffRXBitsGpr, execEffWXBitsGpr]

/-- Rocq `gpr_src_peel_npc` (deviation 6): the x0-safe source read, moved past
the funnel's `nextPC` pre-write. -/
theorem gprSrcPeelNpc (rs1 : BitVec 5) (s : ExecSt) (npc : BitVec 64) :
    (s.setReg .nextPC npc).gpr rs1 = s.gpr rs1 :=
  WeakLeafLw4.gprSetNe s .nextPC npc rs1 (by decide)

/-- Rocq `gpr_src_at_flat` (deviation 6): the same read, moved from the
funnel's flat state to σ's own register file. -/
theorem gprSrcAtFlat (rs1 : BitVec 5) (σ : Wmstate) (b : Bool) :
    ((wflatSt σ).setReg .minstret_increment b).gpr rs1 = uxaXget σ.wmRegs rs1 :=
  WeakLeafLw4.gprSetNe (wflatSt σ) .minstret_increment b rs1 (by decide)

/-- The single compressed fetch read is fetch-pinned (Lean-only, deviation 4). -/
theorem WeakLeafItype.fetchPinRvc0 (al4 : Bool) (σ : Wmstate) (pc : BitVec 64) :
    (∀ j : Nat, j < 4 → fetchPinned σ (WeakInterp.accAddr pc j)) →
    fetchPin σ ([.WEread WeakFetchEff.wakIfetch pc (if al4 then 4 else 2)] ++ []) := by
  intro h
  refine ⟨fun ak pa n hin _ j hj => ?_, by simp [fetchFresh]⟩
  simp only [List.append_nil, List.mem_singleton, Weff.WEread.injEq] at hin
  obtain ⟨rfl, rfl, rfl⟩ := hin
  exact h j (WeakLeafTor.ltFetchW al4 j hj)

section gprFileHelpers
variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF]

/-- The x0-safe source read off the whole file (Lean-only, deviation 2; Rocq
`gpr_file_lookup_acc` + `gpr_pt_value`). -/
theorem WeakLeafItype.gprFileValue (cpu : CPU) (f : RegFile) (m : RegMap) (rs1 : BitVec 5) :
    regInterp (hlc := hlc) (GF := GF) cpu f ⊢ gprFile cpu m -∗ ⌜uxaXget f rs1 = m.get rs1⌝ := by
  by_cases h0 : rs1 = 0#5
  · subst h0
    iintro _Hreg _HF
    ipureintro
    rw [RegMap.get_zero]
    rfl
  · have hnz : rs1.toNat ≠ 0 := fun h => h0 (BitVec.eq_of_toNat_eq (by simpa using h))
    iintro Hreg HF
    icases gprFile_lookup_acc cpu m rs1 h0 $$ HF with ⟨Hc, -⟩
    ihave %hv := WeakLeafLw4.gprValid cpu f rs1 _ (m rs1) hnz $$ Hreg Hc
    ipureintro
    rw [RegMap.get_ne _ _ h0]
    exact hv

/-- The destination write into the whole file (Lean-only, deviation 2; Rocq
`gpr_file_insert_acc` + `gpr_pt_nz` + `reg_update`). -/
theorem WeakLeafItype.gprFileWrite (cpu : CPU) (s : ExecSt) (m : RegMap) (rd : BitVec 5)
    (v : BitVec 64) (hrd : rd.toNat ≠ 0) :
    regInterp (hlc := hlc) (GF := GF) cpu s.regs ⊢ gprFile cpu m -∗
      |==> (regInterp cpu (s.setGpr rd v).regs ∗ gprFile cpu (m.set rd v)) := by
  have h0 : rd ≠ 0#5 := fun h => hrd (by rw [h]; rfl)
  iintro Hreg HF
  icases gprFile_acc cpu m rd h0 $$ HF with ⟨Hc, Hclose⟩
  imod WeakLeafLw4.gprUpdate cpu s rd (m rd) v hrd $$ Hreg Hc with ⟨Hreg, Hc⟩
  ihave HF := Hclose $$ %v Hc
  imodintro
  iframe Hreg HF

end gprFileHelpers

/-! ## 2. The generic `F_Base` leaf (Lean-only, deviation 5), and `addi` -/

section leaf
variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [WeakGS GF]

/-- Lean-only (deviation 5): Rocq `wwp_addi_leaf`'s script, generic in the
register-only instruction `i` and its operand map `op`. -/
theorem WeakLeafItype.wwpGprBaseLeaf (gen : Nat) (cpu : CPU) (al4 : Bool) (pc : BitVec 64)
    (w : BitVec 32) (rs1 rd : BitVec 5) (i : instruction) (op : BitVec 64 → BitVec 64) (m : RegMap)
    (npc0 : BitVec 64) (c : MConf) (q : Qp) (D : Register → Bool) (dst : ExecSt) (ws : Wstate) :
    (∀ s : ExecSt, execEff (execute i) s = some (RETIRE_SUCCESS, s.setGpr rd (op (s.gpr rs1)), [])) →
    is_lpad_instruction i = false →
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
        gprFile cpu (m.set rd (op (m.get rs1))) -∗
        hartWs cpu ws' -∗
        wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu)) -∗
      wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu) := by
  intro hexe hlpad hgid hmok hpmp hal2 hal4 hrd hdecf hagree hDmi hgood hdec
  iintro Hm Hclk Hpc Hnpc Hgf #Hbs Hhws Hcont
  ihave %haccpc := winstrBytesAccWf pc (.F_Base w) $$ Hbs
  have hacc0 : accWf pc 0 := by unfold accWf at haccpc ⊢; omega
  ihave %hnotRVC := WeakLeafLw4.winstrBytesNotRVC pc w $$ Hbs
  have hdecW : winstrDec (.F_Base w) i := by
    intro t h1 h2 h3 h4 h5
    simp only [fetchIsRvc, Bool.false_eq_true, ↓reduceIte]
    exact hdecf t h1 h2 h3 h4 h5
  ihave #Hwi := winstrIntro (GF := GF) pc false i (.F_Base w) hlpad rfl hdecW $$ Hbs
  -- the funnel: certificate = nowrite at the fetch-only trace
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
  -- the SOURCE register, read off the file (x0-safe)
  icases keepPure (WeakLeafItype.gprFileValue cpu _ m rs1) $$ Hreg Hgf with ⟨%Lrs1a, Hreg, Hgf⟩
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
      (⟨σ.wmRegs, wmemRestrict σ (wwin pc pc 0), σ.wmDev⟩ : ExecSt) b' (BitVec.addInt pc 4) rd
      (op ((((⟨σ.wmRegs, wmemRestrict σ (wwin pc pc 0), σ.wmDev⟩ : ExecSt).setReg
          .minstret_increment b').setReg .nextPC (BitVec.addInt pc 4)).gpr rs1))
    refine ⟨_, hexe _, ?_, F2, ?_⟩
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
      hgood hdec hlpad hc
  -- the run at the FLAT state
  have hval : (((wflatSt σ).setReg .minstret_increment b).setReg .nextPC (BitVec.addInt pc 4)).gpr rs1 =
      m.get rs1 := by
    rw [gprSrcPeelNpc]; exact Lrs1a
  have hexf := hexe (((wflatSt σ).setReg .minstret_increment b).setReg .nextPC (BitVec.addInt pc 4))
  rw [hval] at hexf
  have hfacts := loadSexecFacts (wflatSt σ) b (BitVec.addInt pc 4) rd (op (m.get rs1))
  -- the two register writes the `execute` performs
  imod (wand_intro (reg_update cpu _ .nextPC npc0 (BitVec.addInt pc 4))) $$ Hreg Hnpc with ⟨Hreg, Hnpc⟩
  rw [show (((wflatSt σ).setReg .minstret_increment b).regs.set .nextPC (BitVec.addInt pc 4)) =
      (((wflatSt σ).setReg .minstret_increment b).setReg .nextPC (BitVec.addInt pc 4)).regs from rfl]
  imod WeakLeafItype.gprFileWrite cpu (((wflatSt σ).setReg .minstret_increment b).setReg .nextPC
      (BitVec.addInt pc 4)) m rd (op (m.get rs1)) hrd $$ Hreg Hgf with ⟨Hreg, Hgf⟩
  iapply fupd_mask_intro LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro; exact HP
  iexists ((((wflatSt σ).setReg .minstret_increment b).setReg .nextPC (BitVec.addInt pc 4)).setGpr rd
    (op (m.get rs1)))
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
  · iapply Hcont $$ %σ'.wmWs %hwsle Hm' Hclk' [Hpc' Hnpc] Hgf Hhws
    unfold pcIs
    iframe Hpc' Hnpc

/-- Rocq `wwp_addi_leaf` (deviations 1-5): `addi rd, rs1, imm` at an `F_Base`
fetch, either alignment. -/
theorem wwpAddiLeaf (gen : Nat) (cpu : CPU) (al4 : Bool) (pc : BitVec 64) (w : BitVec 32)
    (rs1 rd : BitVec 5) (imm : BitVec 12) (m : RegMap) (npc0 : BitVec 64) (c : MConf) (q : Qp)
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
      exec (decodeFetch (.F_Base w)) t = some (.ITYPE (imm, .Regidx rs1, .Regidx rd, .ADDI), t)) →
    (∀ rs : RegFile,
      rs .cur_privilege = .Machine →
      rs .misa = misaC →
      rs .mseccfg = 0#64 →
      ∀ r, D r = true → rs r = dst.regs r) →
    D .minstret_increment = false →
    goodb0 D (ext_decode w) dst = true →
    exec (ext_decode w) dst = some (.ITYPE (imm, .Regidx rs1, .Regidx rd, .ADDI), dst) →
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
        gprFile cpu (m.set rd (m.get rs1 + sign_extend (m := 64) imm)) -∗
        hartWs cpu ws' -∗
        wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu)) -∗
      wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu) :=
  WeakLeafItype.wwpGprBaseLeaf gen cpu al4 pc w rs1 rd (.ITYPE (imm, .Regidx rs1, .Regidx rd, .ADDI))
    (fun x => x + sign_extend (m := 64) imm) m npc0 c q D dst ws
    (fun s => execEffExecuteITYPEADDIGpr rs1 rd imm s) (by first | rfl | decide)

/-! ## 3. The SAME `ITYPE … ADDI`, through a COMPRESSED decode -/

/-- Lean-only (deviation 5): Rocq `wwp_addi_rvc_leaf`'s script, generic in the
expanded register-only instruction `i` and its operand map `op`. -/
theorem WeakLeafItype.wwpGprRvcLeaf (gen : Nat) (cpu : CPU) (al4 : Bool) (pc : BitVec 64)
    (h : BitVec 16) (rs1 rd : BitVec 5) (i0 i : instruction) (op : BitVec 64 → BitVec 64) (m : RegMap)
    (npc0 : BitVec 64) (c : MConf) (q : Qp) (D D0 : Register → Bool) (dst : ExecSt) (ws : Wstate) :
    (∀ s : ExecSt, execEff (execute i) s = some (RETIRE_SUCCESS, s.setGpr rd (op (s.gpr rs1)), [])) →
    is_lpad_instruction i = false →
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
        gprFile cpu (m.set rd (op (m.get rs1))) -∗
        hartWs cpu ws' -∗
        wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu)) -∗
      wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu) := by
  intro hexe hlpad hgid hmok hpmp hal2 hal4 hrd hdecf hagree hDmi hgood hdec hgood0 hexp
  iintro Hm Hclk Hpc Hnpc Hgf #Hbs Hhws Hcont
  ihave %haccpc := winstrBytesAccWf pc (.F_RVC h) $$ Hbs
  have hacc0 : accWf pc 0 := by unfold accWf at haccpc ⊢; omega
  have hdecW : winstrDec (.F_RVC h) i := by
    intro t h1 h2 h3 h4 h5
    simp only [fetchIsRvc, ↓reduceIte]
    exact hdecf t h1 h2 h3 h4 h5
  ihave #Hwi := winstrIntro (GF := GF) pc true i (.F_RVC h) hlpad rfl hdecW $$ Hbs
  -- the funnel: certificate = nowrite at the single fetch read
  iapply wwpInstr gen cpu pc true i c (DFrac.own q)
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
  -- the SOURCE register, read off the file (x0-safe)
  icases keepPure (WeakLeafItype.gprFileValue cpu _ m rs1) $$ Hreg Hgf with ⟨%Lrs1a, Hreg, Hgf⟩
  -- premise (c): the execute mirror, at the CONFINED state
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
      (⟨σ.wmRegs, wmemRestrict σ (wwin pc pc 0), σ.wmDev⟩ : ExecSt) b' (BitVec.addInt pc 2) rd
      (op ((((⟨σ.wmRegs, wmemRestrict σ (wwin pc pc 0), σ.wmDev⟩ : ExecSt).setReg
          .minstret_increment b').setReg .nextPC (BitVec.addInt pc 2)).gpr rs1))
    refine ⟨_, hexe _, ?_, F2, ?_⟩
    · rw [F1]; exact Lhart
    · rw [F3]; exact wmemRestrictDom σ _
  -- the certificate's precondition
  have HP : wPEff (some cpu.val) [.WEread WeakFetchEff.wakIfetch pc (if al4 then 4 else 2)] σ :=
    wPEffOfLeafRvc al4 cpu.val σ (wwin pc pc 0) pc h w i0 i [] D D0 dst hwf
      (wwinNonzero pc pc 0 (fun j hj => WeakLeafWin.inRamByte pc 4 j hram hj) (win0Absurd _))
      (wwinPinned σ pc pc 0 haccpc hacc0 (fun j hj => (htp j hj).1) (win0Absurd _))
      (WeakLeafItype.fetchPinRvc0 al4 σ pc (fun j hj => (htp j hj).2))
      Lpc0 Lpriv (by rw [Lpmpc]; exact hpmp) Lpma Lhtif Lhart LmisaS (by rw [Lmisa]; decide) LmIE Lelp
      hal2 hal4 hram (wwinConfText σ pc pc 0 w htext0) hsub hisRVC (hagree σ.wmRegs Lpriv Lmisa Lsec)
      hDmi hgood hdec hgood0 hexp hc
  -- the run at the FLAT state
  have hval : (((wflatSt σ).setReg .minstret_increment b).setReg .nextPC (BitVec.addInt pc 2)).gpr rs1 =
      m.get rs1 := by
    rw [gprSrcPeelNpc]; exact Lrs1a
  have hexf := hexe (((wflatSt σ).setReg .minstret_increment b).setReg .nextPC (BitVec.addInt pc 2))
  rw [hval] at hexf
  have hfacts := loadSexecFacts (wflatSt σ) b (BitVec.addInt pc 2) rd (op (m.get rs1))
  -- the two register writes the `execute` performs
  imod (wand_intro (reg_update cpu _ .nextPC npc0 (BitVec.addInt pc 2))) $$ Hreg Hnpc with ⟨Hreg, Hnpc⟩
  rw [show (((wflatSt σ).setReg .minstret_increment b).regs.set .nextPC (BitVec.addInt pc 2)) =
      (((wflatSt σ).setReg .minstret_increment b).setReg .nextPC (BitVec.addInt pc 2)).regs from rfl]
  imod WeakLeafItype.gprFileWrite cpu (((wflatSt σ).setReg .minstret_increment b).setReg .nextPC
      (BitVec.addInt pc 2)) m rd (op (m.get rs1)) hrd $$ Hreg Hgf with ⟨Hreg, Hgf⟩
  iapply fupd_mask_intro LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro; exact HP
  iexists ((((wflatSt σ).setReg .minstret_increment b).setReg .nextPC (BitVec.addInt pc 2)).setGpr rd
    (op (m.get rs1)))
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
  · iapply Hcont $$ %σ'.wmWs %hwsle Hm' Hclk' [Hpc' Hnpc] Hgf Hhws
    unfold pcIs
    iframe Hpc' Hnpc

/-- Rocq `wwp_addi_rvc_leaf` (deviations 1-5): the compressed `ITYPE … ADDI`
(`c.addi` / `c.li` / `c.addi4spn`), either alignment, pc bump 2. -/
theorem wwpAddiRvcLeaf (gen : Nat) (cpu : CPU) (al4 : Bool) (pc : BitVec 64) (h : BitVec 16)
    (rs1 rd : BitVec 5) (imm : BitVec 12) (i0 : instruction) (m : RegMap) (npc0 : BitVec 64)
    (c : MConf) (q : Qp) (D D0 : Register → Bool) (dst : ExecSt) (ws : Wstate) :
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
      ∃ i0' : instruction,
        exec (decodeFetch (.F_RVC h)) t = some (i0', t) ∧
        is_lpad_instruction i0' = false ∧
        (∀ s : ExecSt, exec (execute i0') s =
          some (.ExecuteAs (.ITYPE (imm, .Regidx rs1, .Regidx rd, .ADDI)), s))) →
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
      some (.ExecuteAs (.ITYPE (imm, .Regidx rs1, .Regidx rd, .ADDI)), s)) →
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
        gprFile cpu (m.set rd (m.get rs1 + sign_extend (m := 64) imm)) -∗
        hartWs cpu ws' -∗
        wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu)) -∗
      wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu) :=
  WeakLeafItype.wwpGprRvcLeaf gen cpu al4 pc h rs1 rd i0 (.ITYPE (imm, .Regidx rs1, .Regidx rd, .ADDI))
    (fun x => x + sign_extend (m := 64) imm) m npc0 c q D D0 dst ws
    (fun s => execEffExecuteITYPEADDIGpr rs1 rd imm s) (by first | rfl | decide)

/-! ## 4. `ori rd, rs1, imm` -- §2 with §1's mirror -/

/-- Rocq `wwp_ori_leaf` (deviations 1-5). -/
theorem wwpOriLeaf (gen : Nat) (cpu : CPU) (al4 : Bool) (pc : BitVec 64) (w : BitVec 32)
    (rs1 rd : BitVec 5) (imm : BitVec 12) (m : RegMap) (npc0 : BitVec 64) (c : MConf) (q : Qp)
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
      exec (decodeFetch (.F_Base w)) t = some (.ITYPE (imm, .Regidx rs1, .Regidx rd, .ORI), t)) →
    (∀ rs : RegFile,
      rs .cur_privilege = .Machine →
      rs .misa = misaC →
      rs .mseccfg = 0#64 →
      ∀ r, D r = true → rs r = dst.regs r) →
    D .minstret_increment = false →
    goodb0 D (ext_decode w) dst = true →
    exec (ext_decode w) dst = some (.ITYPE (imm, .Regidx rs1, .Regidx rd, .ORI), dst) →
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
        gprFile cpu (m.set rd (m.get rs1 ||| sign_extend (m := 64) imm)) -∗
        hartWs cpu ws' -∗
        wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu)) -∗
      wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu) :=
  WeakLeafItype.wwpGprBaseLeaf gen cpu al4 pc w rs1 rd (.ITYPE (imm, .Regidx rs1, .Regidx rd, .ORI))
    (fun x => x ||| sign_extend (m := 64) imm) m npc0 c q D dst ws
    (fun s => execEffExecuteITYPEORIGpr rs1 rd imm s) (by first | rfl | decide)

end leaf

end Weak
