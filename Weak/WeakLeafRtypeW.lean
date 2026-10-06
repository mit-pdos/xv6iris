/-
Weak: **the COMPRESSED register-only ALU leaves** (M4, start()/timerinit()
port) -- four weak-tier leaves, all RVC-fetch and all GPR-FILE-based.

Rocq: `iris/WeakLeafRtypeW.v` @ xxvzwolszwmp.

The Rocq header, in substance.
* `wwpAddRvcLeaf` -- the RTYPE ADD reached through a compressed decode.  ONE
  lemma covers BOTH `c.add rd,rs2` (rd = rs1) and `c.mv rd,rs2` (rs1 = x0): the
  leaf takes the whole register file (so rd = rs1 is expressible, which
  separate cells cannot do) and reads its two sources x0-safely.
* `wwpOrRvcLeaf` / `wwpAndRvcLeaf` -- the same for `c.or` / `c.and`.
* `wwpAddiwRvcLeaf` -- `c.addiw` (rd = rs1 at the call site; the leaf is
  generic, like its SC twin).
Each statement is its SC twin under the porting table's swaps (`instr` ↦
`winstrBytes pc (.F_RVC h)` plus the compressed decode premise pack, gen id /
alignment / `hartWs` added, pc bump 2), and each proof is the plain funnel
recipe with `WeakLeafTor`'s F_RVC fetch machinery (`wPEffOfLeafRvc` at
`es_x := []`).  §1 is the three missing `execute` mirrors (RTYPE OR, RTYPE AND,
ADDIW) at trace `[]`; the ADD mirror is `WkEntryEff.execEffExecuteRTYPEADDGpr`.
Every window is `WeakLeafWin.wwin pc pc 0`, the text-only window.

**Deviations from Rocq.**
1. VOCABULARY: as `Weak/WeakLeafTor.lean` deviation 1 (`register_lookup r
   s.(sregs)` ↦ `s.regs r`, `set_reg` ↦ `ExecSt.setReg`, `add_vec_int` ↦
   `BitVec.addInt`, `mword n` ↦ `BitVec n`, `add_vec`/`or_vec`/`and_vec` ↦
   `+`/`|||`/`&&&`, `sign_extend' 64` ↦ `sign_extend (m := 64)`,
   `subrange_vec_dec x 31 0` ↦ `Sail.BitVec.extractLsb x 31 0`,
   `regval_into_reg v` ↦ `v`, `fin_to_nat cpu_id` ↦ `cpu.val`).
2. §1 mirrors follow the `Weak/ExecSC.lean` / `Weak/WkEntryEff.lean`
   (deviation 5) GPR convention: Rocq's `if uint rd =? 0 then s else set_reg s
   (R_bitvector_64 (gpr_of_Z (uint rd))) v` is `s.setGpr rd v` (no premise,
   as Rocq); `gpr_or_val` / `gpr_addiw_val` are `ExecSC.gprOrVal` /
   `ExecSC.gprAddiwVal`; `gpr_and_val` (Rocq `WpMmodeLeafBase`, no Lean twin)
   is the Lean-only `WeakLeafRtypeW.gprAndVal`.
3. THE REGISTER FILE: Rocq `gpr_file m` (over `regfile`, with an x0 entry that
   asserts the value is zero) ↦ `MachCSL.gprFile cpu m` (over `RegMap`; x0 is
   not owned).  So Rocq's x0-safe source read `m !!! Regidx r` (= 0 at x0 by
   the file's x0 entry) is `m.get r` (`RegMap.get`, x0 reads 0), and the
   update `<[Regidx rd := v]> m` is `m.set rd v`.  Rocq's
   `gpr_pt_value`-through-`gpr_file_lookup_acc` read is the Lean-only
   `WeakLeafRtypeW.gprFileRead`.
4. THE CONFIG INTERFACE (owner decision Q3; `Weak/WeakFunnel.lean`
   deviation 7): Rocq `mmode_config (DfracOwn q) -∗ pmpcfg_n ↦ᵣ{DfracOwn q}
   pmpcfg0` ↦ `mConf cpu (DFrac.own q) c ∗ clockCells cpu` (`pmpcfg0 :=
   c.pmpcfg`, `pmp_allows_all pmpcfg0` ↦ `pmpAllowsAll c.pmpcfg`, plus the
   premise `MConf.mok c`); the continuation gets the same back.
   `GenId`/`CpuId` are the explicit `gen`/`cpu`; `WWP Loop` ↦ `wwpTriv ⊤
   (WExpr.loop gen cpu)`; `pc_is` ↦ `pcIs`; `hart_ws` ↦ `hartWs`; the decode
   premises are over the funnel's vocabulary (`privMSU`, `misaC`, `cfgOk`,
   `decodeFetch`; the agreement premise quantifies over `RegFile`,
   `mword_of_int 0` ↦ `0#64`).
5. O2 (owner decision): the fetch element is `.WEread WeakFetchEff.wakIfetch pc
   (if al4 then 4 else 2)` (Rocq `WEread wak_plain …`); the recipe's
   `fetchPin` premise is discharged from `winstrTextPinned`.
6. PROOF SHARING: the four Rocq proofs are one script with the operator
   swapped; Lean proves it once, as the Lean-only generic leaf
   `WeakLeafRtypeW.wwpGprRvcLeaf` (instruction, binary operator and value
   function abstract, with the mirror and landing-pad facts as premises), and
   the four leaves are its instances (ADDIW at `rs2 := rs1`).
7. Rocq §3's `Print Assumptions` commands are not declarations.

**Rocq → Lean name map.**  `exec_eff_execute_RTYPE_OR_gpr`
`execEffExecuteRTYPEORGpr`, `exec_eff_execute_RTYPE_AND_gpr`
`execEffExecuteRTYPEANDGpr`, `exec_eff_execute_ADDIW_gpr`
`execEffExecuteADDIWGpr`, `wwp_add_rvc_leaf` `wwpAddRvcLeaf`,
`wwp_or_rvc_leaf` `wwpOrRvcLeaf`, `wwp_and_rvc_leaf` `wwpAndRvcLeaf`,
`wwp_addiw_rvc_leaf` `wwpAddiwRvcLeaf` (none in the duplicated-name table).
Lean-only (file-qualified): `WeakLeafRtypeW.gprAndVal` (deviation 2),
`WeakLeafRtypeW.gprFileRead` (deviation 3), `WeakLeafRtypeW.wwpGprRvcLeaf`
(deviation 6).

**Dropped:** nothing (Rocq 7 lemmas; Lean 7 theorems + 3 Lean-only).
-/
import Weak.WeakLeafTor
import Weak.WeakLeafLw4
import Weak.WeakLeafWin
import Weak.WkEntryEff
import Weak.ExecSC
import MachCSL.KCtx
import MachCSL.Gpr
import MachCSL.Boot

namespace Weak

open Iris Iris.BI Iris.BI.MonPred Iris.ProofMode Iris.Std
open MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D LeanRV64D.Functions

/-! ## 1. THE THREE MISSING `execute` MIRRORS (trace `[]`) -/

/-- Rocq `exec_eff_execute_RTYPE_OR_gpr` (deviation 2). -/
theorem execEffExecuteRTYPEORGpr (rs2 rs1 rd : BitVec 5) (s : ExecSt) :
    execEff (execute (.RTYPE (.Regidx rs2, .Regidx rs1, .Regidx rd, .OR))) s =
      some (RETIRE_SUCCESS, s.setGpr rd (gprOrVal rs2 rs1 s), []) := by
  show execEff (execute_RTYPE (.Regidx rs2) (.Regidx rs1) (.Regidx rd) .OR) s = _
  unfold execute_RTYPE gprOrVal
  exec_eff_steps [execEffRXBitsGpr, execEffWXBitsGpr]

/-- Rocq `WpMmodeLeafBase.gpr_and_val` (Lean-only stand-in, deviation 2). -/
def WeakLeafRtypeW.gprAndVal (rs2 rs1 : BitVec 5) (s : ExecSt) : BitVec 64 :=
  s.gpr rs1 &&& s.gpr rs2

/-- Rocq `exec_eff_execute_RTYPE_AND_gpr` (deviation 2). -/
theorem execEffExecuteRTYPEANDGpr (rs2 rs1 rd : BitVec 5) (s : ExecSt) :
    execEff (execute (.RTYPE (.Regidx rs2, .Regidx rs1, .Regidx rd, .AND))) s =
      some (RETIRE_SUCCESS, s.setGpr rd (WeakLeafRtypeW.gprAndVal rs2 rs1 s), []) := by
  show execEff (execute_RTYPE (.Regidx rs2) (.Regidx rs1) (.Regidx rd) .AND) s = _
  unfold execute_RTYPE WeakLeafRtypeW.gprAndVal
  exec_eff_steps [execEffRXBitsGpr, execEffWXBitsGpr]

/-- Rocq `exec_eff_execute_ADDIW_gpr` (deviation 2). -/
theorem execEffExecuteADDIWGpr (rs1 rd : BitVec 5) (imm : BitVec 12) (s : ExecSt) :
    execEff (execute (.ADDIW (imm, .Regidx rs1, .Regidx rd))) s =
      some (RETIRE_SUCCESS, s.setGpr rd (gprAddiwVal rs1 imm s), []) := by
  show execEff (execute_ADDIW imm (.Regidx rs1) (.Regidx rd)) s = _
  unfold execute_ADDIW gprAddiwVal
  exec_eff_steps [execEffRXBitsGpr, execEffWXBitsGpr]

/-! ## 2. THE FOUR LEAVES -/

section leaves
variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [WeakGS GF]

/-- Lean-only (deviation 3): reading register `i` off the whole file, x0-safely. -/
theorem WeakLeafRtypeW.gprFileRead (cpu : CPU) (f : RegFile) (m : RegMap) (i : BitVec 5) :
    regInterp (hlc := hlc) (GF := GF) cpu f ⊢ gprFile cpu m -∗ ⌜uxaXget f i = m.get i⌝ := by
  by_cases hi : i = 0#5
  · subst hi
    iintro - -
    ipureintro
    rw [RegMap.get_zero]
    rfl
  · have hi' : i.toNat ≠ 0 := fun h => hi (BitVec.eq_of_toNat_eq h)
    iintro Hreg Hf
    icases gprFile_lookup_acc cpu m i hi $$ Hf with ⟨Hc, -⟩
    ihave %h := WeakLeafLw4.gprValid cpu f i _ (m i) hi' $$ Hreg Hc
    ipureintro
    rw [RegMap.get_ne m i hi]
    exact h

/-- Lean-only (deviation 6): THE generic compressed one-destination ALU leaf. -/
theorem WeakLeafRtypeW.wwpGprRvcLeaf (al4 : Bool) (gen : Nat) (cpu : CPU) (pc : BitVec 64)
    (h : BitVec 16) (i i0 : instruction) (rs2 rs1 rd : BitVec 5)
    (op : BitVec 64 → BitVec 64 → BitVec 64) (val : ExecSt → BitVec 64) (m : RegMap)
    (npc0 : BitVec 64) (q : Qp) (c : MConf) (D D0 : Register → Bool) (dst : ExecSt)
    (ws : Wstate)
    (hrun : ∀ s : ExecSt, execEff (execute i) s = some (RETIRE_SUCCESS, s.setGpr rd (val s), []))
    (hval : ∀ s : ExecSt, val s = op (s.gpr rs1) (s.gpr rs2))
    (hlpad : is_lpad_instruction i = false) :
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
        gprFile cpu (m.set rd (op (m.get rs1) (m.get rs2))) -∗
        hartWs cpu ws' -∗
        wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu)) -∗
      wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu) := by
  intro hgid hmok hpmp hal2 hal4 hrd hdecf hagree hDmi hgood hdec hgood0 hexp
  have hrd0 : rd ≠ 0#5 := fun e => hrd (by rw [e]; rfl)
  iintro Hm Hclk Hpc Hnpc Hfile #Hbs Hhws Hcont
  ihave %haccpc := winstrBytesAccWf pc (.F_RVC h) $$ Hbs
  have hacc0 : accWf pc 0 := by unfold accWf at haccpc ⊢; omega
  have hdecW : winstrDec (.F_RVC h) i := by
    intro t h1 h2 h3 h4 h5
    simp only [fetchIsRvc, ↓reduceIte]
    exact hdecf t h1 h2 h3 h4 h5
  ihave #Hwi := winstrIntro (GF := GF) pc true i (.F_RVC h) hlpad rfl hdecW $$ Hbs
  -- the funnel: certificate = nowrite at the fetch-only trace
  iapply wwpInstr gen cpu pc true i c (DFrac.own q)
    (wPEff (some cpu.val) [.WEread WeakFetchEff.wakIfetch pc (if al4 then 4 else 2)])
    (wQFr wQPure (some cpu.val) [.WEread WeakFetchEff.wakIfetch pc (if al4 then 4 else 2)])
    hgid haccpc hmok hpmp
    (wstepCertFr _ _ _ _ (wcertNowrite cpu.val pc _ (nowriteRead1 _ _ _))) $$ Hm Hclk Hpc Hwi
  unfold wwpCb
  iintro %σ %b %mt %ip %Lpc0 %hcfg Hlat Hreg Hnorg Hti Hip
  unfold wmstateNorg
  icases Hnorg with ⟨%hbnd, %hnv, %hwf, Hdev, Hlogauth, Hwsauth⟩
  ihave ⟨%hws, Hwsauth, Hhws⟩ := persistent_entails_right (hartWsAgree cpu σ.wmWs ws) $$ [Hwsauth Hhws]
  · iframe Hwsauth Hhws
  subst hws
  obtain ⟨Lpriv, Lhart, Lmisa, Lsec, Lpmpc, Lpma, Lhtif, LmisaS, LmIE, -, -, Lelp⟩ := hcfg
  have LmisaC : (_get_Misa_C (σ.wmRegs .misa) == 1#1) = true := by rw [Lmisa]; decide
  icases keepPure (winstrFlat σ pc _ hwf) $$ Hlat Hbs with ⟨%hfok, Hlat, -⟩
  icases keepPure (winstrTextPinned σ pc _ hwf) $$ Hlat Hbs with ⟨%htp, Hlat, -⟩
  icases keepPure (winstrUnwritten σ pc _ hwf) $$ Hlat Hbs with ⟨%hunw, Hlat, -⟩
  obtain ⟨-, hram, w, ⟨hsub, hisRVC⟩, htext0⟩ := hfok
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
      (val (((⟨σ.wmRegs, wmemRestrict σ (wwin pc pc 0), σ.wmDev⟩ : ExecSt).setReg
          .minstret_increment b').setReg .nextPC (BitVec.addInt pc 2)))
    refine ⟨_, hrun _, ?_, F2, ?_⟩
    · rw [F1]; exact Lhart
    · rw [F3]; exact wmemRestrictDom σ _
  -- the O2 fetch pin
  have hfp : fetchPin σ ([.WEread WeakFetchEff.wakIfetch pc (if al4 then 4 else 2)] ++ []) := by
    refine ⟨fun ak pa n hin _ j hj => ?_, by simp [fetchFresh, weffWrites]⟩
    simp only [List.append_nil, List.mem_singleton] at hin
    cases hin
    exact (htp j (WeakLeafTor.ltFetchW al4 j hj)).2
  -- the certificate's precondition
  have HP : wPEff (some cpu.val) [.WEread WeakFetchEff.wakIfetch pc (if al4 then 4 else 2)] σ :=
    wPEffOfLeafRvc al4 cpu.val σ (wwin pc pc 0) pc h w i0 i [] D D0 dst hwf
      (wwinNonzero pc pc 0 (fun j hj => WeakLeafWin.inRamByte pc 4 j hram hj) (win0Absurd _))
      (wwinPinned σ pc pc 0 haccpc hacc0 (fun j hj => (htp j hj).1) (win0Absurd _))
      hfp Lpc0 Lpriv (by rw [Lpmpc]; exact hpmp) Lpma Lhtif Lhart LmisaS LmisaC LmIE Lelp
      hal2 hal4 hram (wwinConfText σ pc pc 0 w htext0) hsub hisRVC
      (hagree σ.wmRegs Lpriv Lmisa Lsec) hDmi hgood hdec hgood0 hexp hc
  -- the TWO source reads, off the file
  icases keepPure (WeakLeafRtypeW.gprFileRead cpu _ m rs1) $$ Hreg Hfile with ⟨%L1, Hreg, Hfile⟩
  icases keepPure (WeakLeafRtypeW.gprFileRead cpu _ m rs2) $$ Hreg Hfile with ⟨%L2, Hreg, Hfile⟩
  have hv : val (((wflatSt σ).setReg .minstret_increment b).setReg .nextPC (BitVec.addInt pc 2)) =
      op (m.get rs1) (m.get rs2) := by
    rw [hval, WeakLeafLw4.gprSetNe _ .nextPC _ rs1 (by decide),
      WeakLeafLw4.gprSetNe _ .nextPC _ rs2 (by decide)]
    unfold ExecSt.gpr
    rw [L1, L2]
  -- the run at the FLAT state
  have hexf := hrun (((wflatSt σ).setReg .minstret_increment b).setReg .nextPC (BitVec.addInt pc 2))
  rw [hv] at hexf
  have hfacts := loadSexecFacts (wflatSt σ) b (BitVec.addInt pc 2) rd (op (m.get rs1) (m.get rs2))
  -- the two register writes the `execute` performs
  imod (wand_intro (reg_update cpu _ .nextPC npc0 (BitVec.addInt pc 2))) $$ Hreg Hnpc with ⟨Hreg, Hnpc⟩
  rw [show (((wflatSt σ).setReg .minstret_increment b).regs.set .nextPC (BitVec.addInt pc 2)) =
      (((wflatSt σ).setReg .minstret_increment b).setReg .nextPC (BitVec.addInt pc 2)).regs from rfl]
  icases gprFile_acc cpu m rd hrd0 $$ Hfile with ⟨Hrdc, Hfback⟩
  imod WeakLeafLw4.gprUpdate cpu (((wflatSt σ).setReg .minstret_increment b).setReg .nextPC
      (BitVec.addInt pc 2)) rd (m rd) (op (m.get rs1) (m.get rs2)) hrd $$ Hreg Hrdc with ⟨Hreg, Hrdc⟩
  ihave Hfile := Hfback $$ %(op (m.get rs1) (m.get rs2)) Hrdc
  iapply fupd_mask_intro LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro; exact HP
  iexists ((((wflatSt σ).setReg .minstret_increment b).setReg .nextPC (BitVec.addInt pc 2)).setGpr rd
    (op (m.get rs1) (m.get rs2)))
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

/-- Rocq `wwp_add_rvc_leaf` (deviations 1, 3-5): `c.add` / `c.mv`. -/
theorem wwpAddRvcLeaf (al4 : Bool) (gen : Nat) (cpu : CPU) (pc : BitVec 64) (h : BitVec 16)
    (rs2 rs1 rd : BitVec 5) (i0 : instruction) (m : RegMap) (npc0 : BitVec 64) (q : Qp)
    (c : MConf) (D D0 : Register → Bool) (dst : ExecSt) (ws : Wstate) :
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
          some (.ExecuteAs (.RTYPE (.Regidx rs2, .Regidx rs1, .Regidx rd, .ADD)), s))) →
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
      some (.ExecuteAs (.RTYPE (.Regidx rs2, .Regidx rs1, .Regidx rd, .ADD)), s)) →
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
        gprFile cpu (m.set rd (m.get rs1 + m.get rs2)) -∗
        hartWs cpu ws' -∗
        wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu)) -∗
      wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu) :=
  WeakLeafRtypeW.wwpGprRvcLeaf al4 gen cpu pc h _ i0 rs2 rs1 rd (fun a b => a + b) (gprRdVal rs2 rs1)
    m npc0 q c D D0 dst ws (execEffExecuteRTYPEADDGpr rs2 rs1 rd) (fun _ => rfl)
    (by first | rfl | decide)

/-- Rocq `wwp_or_rvc_leaf` (deviations 1, 3-5): `c.or`. -/
theorem wwpOrRvcLeaf (al4 : Bool) (gen : Nat) (cpu : CPU) (pc : BitVec 64) (h : BitVec 16)
    (rs2 rs1 rd : BitVec 5) (i0 : instruction) (m : RegMap) (npc0 : BitVec 64) (q : Qp)
    (c : MConf) (D D0 : Register → Bool) (dst : ExecSt) (ws : Wstate) :
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
          some (.ExecuteAs (.RTYPE (.Regidx rs2, .Regidx rs1, .Regidx rd, .OR)), s))) →
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
      some (.ExecuteAs (.RTYPE (.Regidx rs2, .Regidx rs1, .Regidx rd, .OR)), s)) →
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
        gprFile cpu (m.set rd (m.get rs1 ||| m.get rs2)) -∗
        hartWs cpu ws' -∗
        wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu)) -∗
      wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu) :=
  WeakLeafRtypeW.wwpGprRvcLeaf al4 gen cpu pc h _ i0 rs2 rs1 rd (fun a b => a ||| b)
    (gprOrVal rs2 rs1) m npc0 q c D D0 dst ws (execEffExecuteRTYPEORGpr rs2 rs1 rd) (fun _ => rfl)
    (by first | rfl | decide)

/-- Rocq `wwp_and_rvc_leaf` (deviations 1, 3-5): `c.and`. -/
theorem wwpAndRvcLeaf (al4 : Bool) (gen : Nat) (cpu : CPU) (pc : BitVec 64) (h : BitVec 16)
    (rs2 rs1 rd : BitVec 5) (i0 : instruction) (m : RegMap) (npc0 : BitVec 64) (q : Qp)
    (c : MConf) (D D0 : Register → Bool) (dst : ExecSt) (ws : Wstate) :
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
          some (.ExecuteAs (.RTYPE (.Regidx rs2, .Regidx rs1, .Regidx rd, .AND)), s))) →
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
      some (.ExecuteAs (.RTYPE (.Regidx rs2, .Regidx rs1, .Regidx rd, .AND)), s)) →
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
        gprFile cpu (m.set rd (m.get rs1 &&& m.get rs2)) -∗
        hartWs cpu ws' -∗
        wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu)) -∗
      wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu) :=
  WeakLeafRtypeW.wwpGprRvcLeaf al4 gen cpu pc h _ i0 rs2 rs1 rd (fun a b => a &&& b)
    (WeakLeafRtypeW.gprAndVal rs2 rs1) m npc0 q c D D0 dst ws
    (execEffExecuteRTYPEANDGpr rs2 rs1 rd) (fun _ => rfl) (by first | rfl | decide)

/-- Rocq `wwp_addiw_rvc_leaf` (deviations 1, 3-5): `c.addiw` (one source). -/
theorem wwpAddiwRvcLeaf (al4 : Bool) (gen : Nat) (cpu : CPU) (pc : BitVec 64) (h : BitVec 16)
    (rs1 rd : BitVec 5) (immv : BitVec 12) (i0 : instruction) (m : RegMap) (npc0 : BitVec 64)
    (q : Qp) (c : MConf) (D D0 : Register → Bool) (dst : ExecSt) (ws : Wstate) :
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
          some (.ExecuteAs (.ADDIW (immv, .Regidx rs1, .Regidx rd)), s))) →
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
      some (.ExecuteAs (.ADDIW (immv, .Regidx rs1, .Regidx rd)), s)) →
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
        gprFile cpu (m.set rd (sign_extend (m := 64)
          (Sail.BitVec.extractLsb (m.get rs1 + sign_extend (m := 64) immv) 31 0))) -∗
        hartWs cpu ws' -∗
        wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu)) -∗
      wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu) :=
  WeakLeafRtypeW.wwpGprRvcLeaf al4 gen cpu pc h _ i0 rs1 rs1 rd
    (fun a _ => sign_extend (m := 64) (Sail.BitVec.extractLsb (a + sign_extend (m := 64) immv) 31 0))
    (gprAddiwVal rs1 immv) m npc0 q c D D0 dst ws (execEffExecuteADDIWGpr rs1 rd immv)
    (fun _ => rfl) (by first | rfl | decide)

end leaves

end Weak
