/-
Weak: **the symbolic WPd engine X for CONTROL TRANSFERS** (branches / jumps), over the
TLB-filling spine `SpineOkT` (builds on `AxSymEngine*` / `AxSpineOk5`..`AxSpineOk7`; nothing
existing is edited; independent of `AxSymCtl` / `AxSymCtl3`).  Continuation form (no row-position
report: that is `AxSymCtl`'s counting job).

Rocq: `iris/AxSymCtl2.v` @ xxvzwolszwmp.

## The Rocq header, in substance

§1 `SpineFetch4T` (the 4-byte fetch field in TLB-filling form — the `F_Base` twin of `sptFetch`)
and `EvAHartActiveBaseT`.
§2 THE GENERIC CONTROL CERTIFICATE `AxSymCtl2.spineCertC`: an instruction whose `execute` is register-only
up to failure (`rfF`, so the misaligned-target / assert arms of `jump_to` are allowed) and whose
SC exec post is `wrOpt ow (npcOpt ot s)` — an OPTIONAL nextPC write `ot` (the jump / taken-branch
target) then an OPTIONAL GPR write `ow` (the link).  Final boundary: PC = `tgtOf ot pc is_rvc`
(the target, or pc+2/4), GPRs by `gprPost ow`, control state in the regime.  The SC exec premise
`CertC` may use the regime and PC = pc, nextPC = pc + incr.  BOTH widths.
§3 `XPost` / `XCtlΦ` / `XCtlΦHolds`: X for control transfers, any post Φ, fine row-end premises
(`Hmid` for the theorem, `Hb` per call) as in `AxSymEngine3.XGprWriteΦ`.
§4 The per-instruction certificates (SC `exec` facts, symbolic register values): `certJALR`
(register target, bit 0 cleared by `jalrTgt`; link iff rd ≠ 0), `certJAL` (pc-relative, link iff
rd ≠ 0), `certBTYPE` (all six ops, REGISTER sources: ONE certificate covers BOTH outcomes, the
condition on the symbolic register values), under `ctlRegime` (Zca on, Zicfilp off).
X corollaries `XJalr`, `XJal`, `XBtype`, and the compressed forms `XCj`, `XCjr`, `XCjalr`,
`XCret`, `XCbeqz`/`XCbnez`.
§5 THE S-MODE KERNEL REGIME: `ctlRegimeS`; `XCtlSRvc`: X at `spineOkTS` for every COMPRESSED
control transfer; `wpdCretGa2` / `wpdCbeqzGa2`: c.ret and c.beqz at the REAL Tier-A instance
(`axGA2` with the real `protInv`) with the boundary post `ΦRet cpu P`.
§6 NON-VACUITY on the REAL model (`evb` + `evbSound`, both ticks, every pin answer) at
`AxEpiProbe.tAt` (M-mode): c.jr ra (0x8082) lands at ra's value with bit 0 clear; beq ra,ra,+8
(0x00108463) is TAKEN, bne ra,ra,+8 (0x00109463) FALLS THROUGH; c.beqz a0,+8 (0xC501) with a0 ≠ 0
falls through — each exactly `tgtOf` of the symbolic certificate's `ot`; plus decode facts.

FINDING / RESIDUALS (as Rocq): the S-mode spine has only the COMPRESSED fetch arm, so the 4-byte
transfers are proved over an ABSTRACT `SpineFetch4T` (the S-mode instance is not done; the
compressed forms discharge it vacuously by `no4`).  JAL / BTYPE targets need bit 0 = 0 (a
premise); JALR clears it.  JALR with rs1 = x0 excluded.  SIE = 1 arm not covered.

## Deviations from Rocq

1. O2 STAGE C (as `AxSymEngine3` deviation 1): the section premise `Hloc` is DROPPED (§3–§5);
   premises are `Htext Hflow` (then `G HG Φ Hmid`).  Rocq's `HlocG` (§5 `Let`) is not built.
2. Q7 (as `AxSymEngine3` deviation 2): the 4-byte arm announces the 32-bit word, so
   `EvAHartActiveBaseT` takes `sfAnnB 32 w = false` and `textOkCtl`'s base arm carries it (after
   `textAt4 pc w`).  LEAN-SAIL: the base arm's landing-pad test is a pure `&&` (no
   `is_lpad_instruction` premise needed with the lpad answer `false`).
3. Types / registers as `AxSymEngine3` deviation 4: `regs_agree seip_reg` ↦
   `regsAgree AxRunClose.pinReg`; Rocq `gpr r rs` ↦ `uxaXget rs r` (= `AxSymEngine3.gpr`);
   `Z.eqb (uint r) (uint rd)` ↦ `r = rd`; `add_vec_int` ↦ `BitVec.addInt`; `incr` is
   `AxSymEngine3.incr` (Int).  `wrOpt`'s GPR write is `ExecSt.setGpr` (Rocq a raw `set_reg` of
   `R_bitvector_64 (gpr_of_Z (uint rd))`; equal under `owOk`, ExecSC convention).
   `wrNpcOther`'s premise `∀ w, r ≠ R_bitvector_64 w` (r not a 64-bit register) ↦
   `r ∉ uxaGprs` and `r ≠ .nextPC`.  `zeros' 12` ↦ `zeros (n := 12)`; `concat_vec x 'b"0"` ↦
   `x ++ 0#1`; `zero_extend' 5 'b"00"` ↦ `zero_extend (m := 5) 0b00#2`; `Regidx`/`zreg`/`ra` are
   the model's.  `eq_vec (access_vec_dec v 0) 'b"0" = true` ↦ `(BitVec.access v 0 == 0#1) = true`.
4. `certJALR` is proved from ExecSC7's `execExecuteJALRZca` (both arms at once; Rocq splits
   ret/link); bit 0 by the Lean-only `AxSymCtl2.bit0Update0` (Rocq `bit0_update0_64`).
5. `bcond` is file-qualified `AxSymCtl2.bcond` (`MachCSL.bcond` exists, a different spelling).
6. §5 `ctl_ga2` (Rocq `Local Instance`, with an `axGA2` `T` parameter Lean lacks) is not declared:
   the statements pass `AxSymEngine3b.blkGa2 GD0 γ` explicitly (the same instance).  The satp
   facts take `AxSpineOk7.spineOkTS`'s shapes.
7. `cE_zicfilp_false_S` is stated over Lean's `exec` (no fuel; `hartSupports` pure).
8. §6: `vm_compute` ↦ `decide +kernel`; `bool_decide (x = I)` ↦ match projections (the model's
   `instruction` has no `DecidableEq`); `nvb_img w` takes `w : Nat` and splits bytes by
   `BitVec.ofNat 8 (w >>> 8k)` (Rocq `Z.land (Z.shiftr w 8k) 255`).

**Rocq → Lean name map.**  `SpineFetch4T` `SpineFetch4T`, `no4` `no4`, `SpineFetch4T_no4`
`SpineFetch4TNo4`, `EvA_hart_active_base_T` `EvAHartActiveBaseT`, `npc_opt` `npcOpt`, `wr_opt`
`wrOpt`, `tgt_of` `tgtOf`, `ow_ok` `owOk`, `gpr_post` `gprPost`, `GoodC` `GoodC`, `text_ok_ctl`
`textOkCtl`, `CertC` `CertC`, `wr_npc_other` `wrNpcOther`, `wr_npc_nextPC` `wrNpcNextPC`,
`wr_npc_gpr` `wrNpcGpr`, `gpr_post_agree` `gprPostAgree`, `tfinal_PC` `tfinalPC`, `tfinal_gpr`
`tfinalGpr`, `wr_npc_ctrl` `wrNpcCtrl`, `spine_certC` `AxSymCtl2.spineCertC`, `XPost` `XPost`, `X_ctlΦ`
`XCtlΦ`, `X_ctlΦ_holds` `XCtlΦHolds`, `ctl_regime` `ctlRegime`, `gval` `gval`, `gval_agree`
`gvalAgree`, `jalr_tgt` `jalrTgt`, `link_ow` `linkOw`, `ow_ok_link` `owOkLink`, `link_ow_zero`
`linkOwZero`, `bcond` `AxSymCtl2.bcond`, `br_ot` `brOt`, `cert_JALR` `certJALR`, `cert_JAL`
`certJAL`, `cert_BTYPE` `certBTYPE`, `exp_EvA` `expEvA`, `X_jalr` `XJalr`, `X_jal` `XJal`,
`X_btype` `XBtype`, `cj_imm` `cjImm`, `X_cj` `XCj`, `X_cjr` `XCjr`, `ra5c` `ra5c`, `X_cjalr`
`XCjalr`, `X_cret` `XCret`, `cb_imm` `cbImm`, `creg5` `creg5`, `X_cbeqz` `XCbeqz`, `X_cbnez`
`XCbnez`, `cE_zicfilp_false_S` `cEZicfilpFalseS`, `ctl_regime_S` `ctlRegimeS`, `X_ctl_S_rvc`
`XCtlSRvc`, `wpd_cret_ga2` `wpdCretGa2`, `wpd_cbeqz_ga2` `wpdCbeqzGa2`, `nvc_img` `nvcImg`,
`nvc_post` `nvcPost`, `nvc_step_false/true` `nvcStepFalse/True`, `nvc_cert` `nvcCert`,
`nvc_decode_expand` `nvcDecodeExpand`, `nvb_pc` `nvbPc`, `nvb_t` `nvbT`, `nvb_img` `nvbImg`,
`nvb_imm` `nvbImm`, `nvb_post` `nvbPost`, `nvb_beq_false/true` `nvbBeqFalse/True`,
`nvb_bne_false/true` `nvbBneFalse/True`, `nvb_outcomes` `nvbOutcomes`, `nvb_decode` `nvbDecode`,
`nvz_img` `nvzImg`, `nvz_rsc` `nvzRsc`, `nvz_post` `nvzPost`, `nvz_step_false/true`
`nvzStepFalse/True`, `nvz_decode_expand` `nvzDecodeExpand`.  None is in the duplicated-name
table.  Lean-only (file-qualified): `AxSymCtl2.bit0Update0`, `AxSymCtl2.setGprZero`,
`AxSymCtl2.wrOptLink`, `AxSymCtl2.gvalEq`.

**Dropped:** the Ltacs `nseipC`, `ev_stepC`/`ev_goC`/`ev_useC`, `lk` (AxSymEngine2's kit
`ax_sym2_ev_go`/`evRUse` and `RegFile` rewrites instead); the section `Let`s `TX`/`XH`/`TXS`/
`HtextG`/`HflowG`/`HlocG` (inlined); `ctl_ga2` (deviation 6).  Rocq 77 definitions/lemmas
+ 1 local instance + 6 section `Let`s; Lean 77 + 4 Lean-only.
**Not ported:** the `Print Assumptions` lines (the lint's axiom check covers them).
-/
import Weak.AxSymEngine3b
import Weak.AxSpineOk7

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std MachCSL
open Sail Sail.ConcurrencyInterfaceV1
open Sail.ArchSem (FreeM)
open LeanRV64D LeanRV64D.Functions

/-! # 1. The 4-byte arm in TLB-filling form -/

def SpineFetch4T (img : Image) (ctrlOk : RegFile → Prop) (textAt4 : BitVec 64 → BitVec 32 → Prop) :
    Prop :=
  ∀ (t : ExecSt) pc w, ctrlOk t.regs → t.regs .PC = pc → textAt4 pc w →
    ∃ t1, tlbFrame t t1 ∧ ctrlOk t1.regs ∧
      EvA img (fun _ _ => False) (fun r t' => r = .F_Base w ∧ t' = t1) (fetch ()) t

/-- No 4-byte text at all: the fetch field holds vacuously. -/
def no4 : BitVec 64 → BitVec 32 → Prop := fun _ _ => False

theorem SpineFetch4TNo4 (img : Image) (ctrlOk : RegFile → Prop) : SpineFetch4T img ctrlOk no4 :=
  fun _ _ _ _ _ h => h.elim

section baseArmT
variable (img : Image)

/-- `EvAHartActiveBase` with the fetch landing in a (TLB-filled) state `t1`. -/
theorem EvAHartActiveBaseT (t t1 : ExecSt) (w : BitVec 32) (ins : instruction) (pc : BitVec 64)
    (Qx : ExecSt → Prop) (hw : sfAnnB 32 w = false) :
    EvA img (fun _ _ => False) (fun r t' => r = none ∧ t' = t)
      (dispatchInterrupt (t.regs .cur_privilege)) t →
    EvA img (fun _ _ => False) (fun r t' => r = .F_Base w ∧ t' = t1) (fetch ()) t →
    EvA img (fun _ _ => False) (fun x t' => x = ins ∧ t' = t1) (ext_decode w) t1 →
    EvA img (fun _ _ => False) (fun x t' => x = false ∧ t' = t1) (is_landing_pad_expected ()) t1 →
    t1.regs .PC = pc →
    EvA img (fun _ _ => False) (fun x t' => x = RETIRE_SUCCESS ∧ Qx t') (execute ins)
      (t1.setReg .nextPC (BitVec.addInt pc 4)) →
    EvA img (fun _ _ => False)
      (fun x t' => x = .Step_Execute (RETIRE_SUCCESS, zero_extend (m := 32) w) ∧ Qx t')
      (run_hart_active 0) t := by
  intro Hdisp Hfetch Hdec Hlpad HPC Hexec
  subst HPC
  unfold run_hart_active
  apply EvACatchEarlyReturn
  ax_sym2_ev_go
  refine AxSymEngine2.evRUse Hdisp ?_
  ax_sym2_ev_go
  refine AxSymEngine2.evRUse Hfetch ?_
  ax_sym2_ev_go
  refine AxSymEngine3.evRAnn32 hw ?_
  ax_sym2_ev_go
  refine AxSymEngine2.evRUse Hdec ?_
  ax_sym2_ev_go
  refine AxSymEngine2.evRUse Hlpad ?_
  ax_sym2_ev_go
  simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  ax_sym2_ev_go
  refine EvAFactLift img _ _ _ _ _ _ Hexec ?_
  rintro _ t' ⟨rfl, hq⟩
  ax_sym2_ev_go
  exact .evRet _ _ ⟨rfl, hq⟩

end baseArmT

/-! # 2. THE GENERIC CONTROL CERTIFICATE -/

def npcOpt (ot : Option (BitVec 64)) (s : ExecSt) : ExecSt :=
  match ot with
  | some tg => s.setReg .nextPC tg
  | none => s

def wrOpt (ow : Option (BitVec 5 × BitVec 64)) (s : ExecSt) : ExecSt :=
  match ow with
  | some (rd, v) => s.setGpr rd v
  | none => s

def tgtOf (ot : Option (BitVec 64)) (pc : BitVec 64) (is_rvc : Bool) : BitVec 64 :=
  match ot with
  | some tg => tg
  | none => BitVec.addInt pc (incr is_rvc)

def owOk (ow : Option (BitVec 5 × BitVec 64)) : Prop :=
  match ow with
  | some (rd, _) => rd.toNat ≠ 0
  | none => True

def gprPost (ow : Option (BitVec 5 × BitVec 64)) (rs : RegFile) (r : BitVec 5) : BitVec 64 :=
  match ow with
  | some (rd, v) => if r = rd then v else uxaXget rs r
  | none => uxaXget rs r

def GoodC (ctrlOk : RegFile → Prop) (is_rvc : Bool) (rs : RegFile) (pc : BitVec 64)
    (ot : Option (BitVec 64)) (ow : Option (BitVec 5 × BitVec 64)) (rs' : RegFile) : Prop :=
  ctrlOk rs' ∧ rs' .PC = tgtOf ot pc is_rvc ∧
    ∀ r : BitVec 5, r.toNat ≠ 0 → uxaXget rs' r = gprPost ow rs r

/-- The text fact, both widths, with the fail-tolerant footprint `rfF` of `execute ins`
(deviation 2: the base arm's word is not an sfence word). -/
def textOkCtl (img : Image) (ctrlOk : RegFile → Prop) (textAt : BitVec 64 → BitVec 16 → Prop)
    (textAt4 : BitVec 64 → BitVec 32 → Prop) (pc : BitVec 64) (is_rvc : Bool)
    (ins : instruction) : Prop :=
  rfF (execute ins) ∧
  if is_rvc then ∃ h i0, textAt pc h ∧
      (∀ t : ExecSt, ctrlOk t.regs →
        EvA img (fun _ _ => False) (fun x t' => x = i0 ∧ t' = t) (ext_decode_compressed h) t) ∧
      (∀ t : ExecSt, EvA img (fun _ _ => False) (fun x t' => x = .ExecuteAs ins ∧ t' = t)
        (execute i0) t)
  else ∃ w, textAt4 pc w ∧ sfAnnB 32 w = false ∧
      (∀ t : ExecSt, ctrlOk t.regs →
        EvA img (fun _ _ => False) (fun x t' => x = ins ∧ t' = t) (ext_decode w) t)

/-- The SC exec premise: at every state of the regime at this pc (nextPC already ticked, GPRs
of `rs`), `execute ins` retires with `ot` / `ow`. -/
def CertC (ctrlOk : RegFile → Prop) (rs : RegFile) (pc : BitVec 64) (is_rvc : Bool)
    (ins : instruction) (ot : Option (BitVec 64)) (ow : Option (BitVec 5 × BitVec 64)) : Prop :=
  ∀ s_pc : ExecSt, ctrlOk s_pc.regs → s_pc.regs .PC = pc →
    s_pc.regs .nextPC = BitVec.addInt pc (incr is_rvc) → gprAgree s_pc.regs rs →
    exec (execute ins) s_pc = some (RETIRE_SUCCESS, wrOpt ow (npcOpt ot s_pc))

theorem wrNpcOther (ow : Option (BitVec 5 × BitVec 64)) (ot : Option (BitVec 64)) (s : ExecSt)
    (r : Register) (hg : r ∉ uxaGprs) (hn : r ≠ .nextPC) :
    (wrOpt ow (npcOpt ot s)).regs r = s.regs r := by
  have Hn : (npcOpt ot s).regs r = s.regs r := by
    cases ot with
    | none => rfl
    | some tg => exact RegFile.set_other _ _ _ _ hn
  cases ow with
  | none => exact Hn
  | some p =>
    obtain ⟨rd, v⟩ := p
    exact (AxSymEngine2.setGprRegsNe _ rd v r hg).trans Hn


theorem wrNpcNextPC (ow : Option (BitVec 5 × BitVec 64)) (ot : Option (BitVec 64)) (s : ExecSt) :
    (wrOpt ow (npcOpt ot s)).regs .nextPC =
      match ot with
      | some tg => tg
      | none => s.regs .nextPC := by
  have Hn : (npcOpt ot s).regs .nextPC =
      match ot with
      | some tg => tg
      | none => s.regs .nextPC := by
    cases ot with
    | none => rfl
    | some tg => simp only [npcOpt, ExecSt.setReg_regs, RegFile.set_same]
  cases ow with
  | none => exact Hn
  | some p =>
    obtain ⟨rd, v⟩ := p
    exact (AxSymEngine2.setGprRegsNe _ rd v .nextPC (by decide)).trans Hn

theorem wrNpcGpr (ow : Option (BitVec 5 × BitVec 64)) (ot : Option (BitVec 64)) (s : ExecSt)
    (r : BitVec 5) : r.toNat ≠ 0 → owOk ow →
    uxaXget (wrOpt ow (npcOpt ot s)).regs r = gprPost ow s.regs r := by
  intro Hr How
  have Hn : uxaXget (npcOpt ot s).regs r = uxaXget s.regs r := by
    cases ot with
    | none => rfl
    | some tg => exact AxSymEngine2.uxaXgetSetNe _ _ _ (by decide) r
  cases ow with
  | none => exact Hn
  | some p =>
    obtain ⟨rd, v⟩ := p
    simp only [wrOpt, gprPost]
    by_cases E : r = rd
    · subst E
      rw [if_pos rfl]
      exact AxFetch3c.gprSetGprSame _ r v How
    · rw [if_neg E]
      exact (AxFetch3c.gprSetGprNe _ rd r v E).trans Hn

theorem gprPostAgree (ow : Option (BitVec 5 × BitVec 64)) (a b : RegFile) (r : BitVec 5) :
    gprAgree a b → r.toNat ≠ 0 → gprPost ow a r = gprPost ow b r := by
  intro Hag Hr
  cases ow with
  | none => exact Hag r Hr
  | some p =>
    obtain ⟨rd, v⟩ := p
    simp only [gprPost]
    split
    · rfl
    · exact Hag r Hr

theorem tfinalPC (b : Bool) (tx : ExecSt) : (tfinal b tx).regs .PC = tx.regs .nextPC := by
  unfold tfinal
  cases b <;> simp only [ExecSt.setReg_regs, Bool.false_eq_true, ↓reduceIte] <;>
    (try rw [RegFile.set_other _ _ _ _ (by decide)]) <;> rw [RegFile.set_same]

theorem tfinalGpr (b : Bool) (tx : ExecSt) (r : BitVec 5) :
    uxaXget (tfinal b tx).regs r = uxaXget tx.regs r := by
  unfold tfinal
  cases b <;> simp only [ExecSt.setReg_regs, Bool.false_eq_true, ↓reduceIte] <;>
    (try rw [AxSymEngine2.uxaXgetSetNe _ _ _ (by decide)]) <;>
    rw [AxSymEngine2.uxaXgetSetNe _ _ _ (by decide)]

section certC
variable (img : Image)

theorem wrNpcCtrl (ctrlOk : RegFile → Prop) (textAt : BitVec 64 → BitVec 16 → Prop)
    (Hsp : SpineOkT img ctrlOk textAt) (ow : Option (BitVec 5 × BitVec 64))
    (ot : Option (BitVec 64)) (s : ExecSt) :
    ctrlOk s.regs → ctrlOk (wrOpt ow (npcOpt ot s)).regs := by
  intro Hc
  have Hn : ctrlOk (npcOpt ot s).regs := by
    cases ot with
    | none => exact Hc
    | some tg => exact Hsp.sptFrame _ _ _ (Or.inr (Or.inl rfl)) Hc
  cases ow with
  | none => exact Hn
  | some p =>
    obtain ⟨rd, v⟩ := p
    exact AxSymEngine2.ctrlOkSetGpr ctrlOk Hsp.sptFrame _ rd v Hn

theorem AxSymCtl2.spineCertC (ctrlOk : RegFile → Prop) (textAt : BitVec 64 → BitVec 16 → Prop)
    (textAt4 : BitVec 64 → BitVec 32 → Prop)
    (Hsp : SpineOkT img ctrlOk textAt) (Hf4 : SpineFetch4T img ctrlOk textAt4)
    (rs : RegFile) (pc : BitVec 64) (is_rvc : Bool) (ins : instruction)
    (ot : Option (BitVec 64)) (ow : Option (BitVec 5 × BitVec 64)) :
    ctrlOk rs → rs .PC = pc → textOkCtl img ctrlOk textAt textAt4 pc is_rvc ins →
    owOk ow → CertC ctrlOk rs pc is_rvc ins ot ow →
    ∀ (tick : Bool) (t : ExecSt), regsAgree AxRunClose.pinReg t.regs rs →
      EvA img (fun _ _ => False) (fun _ t' => GoodC ctrlOk is_rvc rs pc ot ow t'.regs)
        (riscvStep tick) t := by
  intro Hct HPC ⟨Hrf, Htx⟩ How Hcert tick t Hag
  have Hct_t : ctrlOk t.regs := Hsp.sptSeip _ _ Hct Hag
  have HPC_t : t.regs .PC = pc := by
    rw [Hag .PC (AxSymEngine2.notPin _ (by decide) (by decide))]; exact HPC
  obtain ⟨b, Hb⟩ := Hsp.sptInc t Hct_t
  have Hct_a : ctrlOk (t.setReg .minstret_increment b).regs :=
    Hsp.sptFrame _ _ _ (Or.inr (Or.inr (Or.inl rfl))) Hct_t
  have HPC_a : (t.setReg .minstret_increment b).regs .PC = pc := by
    rw [ExecSt.setReg_regs, RegFile.set_other _ _ _ _ (by decide)]; exact HPC_t
  have Hmain : ∃ t1 bits, tlbFrame (t.setReg .minstret_increment b) t1 ∧ ctrlOk t1.regs ∧
      ∀ Qx : ExecSt → Prop,
        EvA img (fun _ _ => False) (fun x t' => x = RETIRE_SUCCESS ∧ Qx t') (execute ins)
          (t1.setReg .nextPC (BitVec.addInt pc (incr is_rvc))) →
        EvA img (fun _ _ => False) (fun x t' => x = .Step_Execute (RETIRE_SUCCESS, bits) ∧ Qx t')
          (run_hart_active 0) (t.setReg .minstret_increment b) := by
    cases is_rvc with
    | true =>
      rw [if_pos rfl] at Htx
      obtain ⟨h, i0, Hat, Hdec, Hexp⟩ := Htx
      obtain ⟨t1, Hfr, Hct1, Hfetch⟩ := Hsp.sptFetch _ pc h Hct_a HPC_a Hat
      have HPC_1 : t1.regs .PC = pc := (tlbFrameLookup _ _ _ Hfr (by decide)).trans HPC_a
      exact ⟨t1, zero_extend (m := 32) h, Hfr, Hct1, fun Qx Hex =>
        EvAHartActiveRvcT img _ t1 h i0 ins pc Qx (Hsp.sptDisp _ Hct_a) Hfetch (Hdec _ Hct1)
          (Hsp.sptLpad _ Hct1) (Hsp.sptZca _ Hct1) HPC_1 (Hexp _) Hex⟩
    | false =>
      rw [if_neg Bool.false_ne_true] at Htx
      obtain ⟨w, Hat, Hsf, Hdec⟩ := Htx
      obtain ⟨t1, Hfr, Hct1, Hfetch⟩ := Hf4 _ pc w Hct_a HPC_a Hat
      have HPC_1 : t1.regs .PC = pc := (tlbFrameLookup _ _ _ Hfr (by decide)).trans HPC_a
      exact ⟨t1, zero_extend (m := 32) w, Hfr, Hct1, fun Qx Hex =>
        EvAHartActiveBaseT img _ t1 w ins pc Qx Hsf (Hsp.sptDisp _ Hct_a) Hfetch (Hdec _ Hct1)
          (Hsp.sptLpad _ Hct1) HPC_1 Hex⟩
  obtain ⟨t1, bits, Hfr, Hct1, Hrun⟩ := Hmain
  have HPC_1 : t1.regs .PC = pc := (tlbFrameLookup _ _ _ Hfr (by decide)).trans HPC_a
  have Hgag : gprAgree (t1.setReg .nextPC (BitVec.addInt pc (incr is_rvc))).regs rs := by
    intro r _
    simp only [ExecSt.setReg_regs]
    rw [AxSymEngine2.uxaXgetSetNe _ _ _ (by decide), AxSpineOk5.tlbFrameXget _ _ Hfr,
      ExecSt.setReg_regs, AxSymEngine2.uxaXgetSetNe _ _ _ (by decide)]
    exact AxSymEngine2.uxaXgetAgree _ _ Hag r
  have Hct_pc : ctrlOk (t1.setReg .nextPC (BitVec.addInt pc (incr is_rvc))).regs :=
    Hsp.sptFrame _ _ _ (Or.inr (Or.inl rfl)) Hct1
  have HPC_pc : (t1.setReg .nextPC (BitVec.addInt pc (incr is_rvc))).regs .PC = pc := by
    rw [ExecSt.setReg_regs, RegFile.set_other _ _ _ _ (by decide)]; exact HPC_1
  have Hnpc_pc : (t1.setReg .nextPC (BitVec.addInt pc (incr is_rvc))).regs .nextPC =
      BitVec.addInt pc (incr is_rvc) := by
    simp only [ExecSt.setReg_regs, RegFile.set_same]
  have Hexec := EvAOfRfF img _ Hrf _ _ _ (Hcert _ Hct_pc HPC_pc Hnpc_pc Hgag)
  have Hrun' := Hrun (fun t' => t' = wrOpt ow (npcOpt ot
    (t1.setReg .nextPC (BitVec.addInt pc (incr is_rvc))))) Hexec
  have Hmi1 : t1.regs .minstret_increment = b := by
    rw [tlbFrameLookup _ _ _ Hfr (by decide)]
    simp only [ExecSt.setReg_regs, RegFile.set_same]
  have Hct_x := wrNpcCtrl img ctrlOk textAt Hsp ow ot _ Hct_pc
  refine EvARiscvStep img tick t (fun t' => GoodC ctrlOk is_rvc rs pc ot ow t'.regs) _ ?_ ?_
  · have HT := EvATryStepActive img t b bits
      (fun t' => t' = wrOpt ow (npcOpt ot (t1.setReg .nextPC (BitVec.addInt pc (incr is_rvc)))))
      (fun t' => GoodC ctrlOk is_rvc rs pc ot ow t'.regs) Hb (Hsp.sptHart _ Hct_a) Hrun' ?_
    · exact EvAMono img _ _ _ _ _ t (fun _ _ h => h) (fun _ _ h => h.2) HT
    · rintro _ rfl
      refine ⟨?_, ?_, ?_⟩
      · rw [wrNpcOther _ _ _ _ (by decide) (by decide)]
        simp only [ExecSt.setReg_regs]
        rw [RegFile.set_other _ _ _ _ (by decide)]
        exact Hsp.sptHart _ Hct1
      · rw [wrNpcOther _ _ _ _ (by decide) (by decide)]
        simp only [ExecSt.setReg_regs]
        rw [RegFile.set_other _ _ _ _ (by decide)]
        exact Hmi1
      · refine ⟨?_, ?_, ?_⟩
        · unfold tfinal
          cases b
          · exact Hsp.sptFrame _ _ _ (Or.inl rfl) Hct_x
          · exact Hsp.sptFrame _ _ _ (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
              (Hsp.sptFrame _ _ _ (Or.inl rfl) Hct_x)
        · rw [tfinalPC, wrNpcNextPC]
          cases ot with
          | none => exact Hnpc_pc
          | some tg => rfl
        · intro r Hr
          rw [tfinalGpr, wrNpcGpr _ _ _ _ Hr How]
          exact gprPostAgree _ _ _ _ Hgag Hr
  · intro t' HG
    cases tick with
    | false => exact HG
    | true =>
      refine EvAMono img _ _ _ _ _ t' (fun _ _ h => h) ?_ (Hsp.sptTick t' HG.1)
      rintro _ t'' ⟨Hc, Hk1, Hk2⟩
      obtain ⟨-, HG2, HG3⟩ := HG
      exact ⟨Hc, Hk1.trans HG2, fun r Hr => (Hk2 r).trans (HG3 r Hr)⟩

end certC

/-! # 3. X for control transfers -/

section xctlDef
variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [AxirisG GF] [Axpol]

def XPost (i : Agent) (cpu : CPU) (ctrlOk : RegFile → Prop) (Φ : Athread → IProp GF)
    (rs : RegFile) (tgt : BitVec 64) (ow : Option (BitVec 5 × BitVec 64)) : IProp GF :=
  iprop(∀ (s' : Athread) (rs' : RegFile) (k' : Nat),
    ⌜RetX cpu rs' k' s'⌝ -∗ ⌜ctrlOk rs'⌝ -∗ ⌜rs' .PC = tgt⌝ -∗
    ⌜∀ r : BitVec 5, r.toNat ≠ 0 → uxaXget rs' r = gprPost ow rs r⌝ -∗
    wpd .MaybeStuck i s' Φ)

def XCtlΦ (i : Agent) (cpu : CPU) (ctrlOk : RegFile → Prop)
    (textOk : BitVec 64 → Bool → instruction → Prop) (G : Gdexec → Prop)
    (Φ : Athread → IProp GF) : Prop :=
  ∀ (s : Athread) (rs : RegFile) (k : Nat) (pc : BitVec 64) (is_rvc : Bool)
    (ins : instruction) (ot : Option (BitVec 64)) (ow : Option (BitVec 5 × BitVec 64)),
    RetX cpu rs k s → ctrlOk rs → rs .PC = pc →
    textOk pc is_rvc ins → owOk ow → CertC ctrlOk rs pc is_rvc ins ot ow →
    (∀ GD s1, G GD → RetX cpu rs k s1 → s1.atK = (AxOpsem.grow GD i).length →
      ⊢ postLifting Φ i s1) →
    ⊢ XPost i cpu ctrlOk Φ rs (tgtOf ot pc is_rvc) ow -∗ wpd .MaybeStuck i s Φ

end xctlDef

section xctl
variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [AxirisG GF] [Axpol]
variable (img : Image) (i : Agent) (cpu : CPU)
variable (ctrlOk : RegFile → Prop) (textAt : BitVec 64 → BitVec 16 → Prop)
  (textAt4 : BitVec 64 → BitVec 32 → Prop)
variable (Hsp : SpineOkT img ctrlOk textAt) (Hf4 : SpineFetch4T img ctrlOk textAt4)
variable (Htext : ∀ GD, rvwmoCatConsistent GD →
  AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜textFixed GD i img⌝)
variable (Hflow : ∀ GD ls k, rvwmoCatConsistent GD →
  (∃ lb aq base n vs, (AxOpsem.grow GD i)[k]? = some lb ∧ aident lb = .IRead aq base n ∧
     imgBytes img base n = some vs) →
  AxirisG.gconstInterp (GF := GF) GD ∗ AxirisG.localInterp GD i k ls ⊢ fetchFlow GD i k)

include Hsp Hf4 Htext Hflow in
theorem XCtlΦHolds (G : Gdexec → Prop)
    (HG : ∀ GD, rvwmoCatConsistent GD → AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜G GD⌝)
    (Φ : Athread → IProp GF)
    (Hmid : ∀ GD s, G GD → midState s → s.atK = (AxOpsem.grow GD i).length →
      ⊢ postLifting Φ i s) :
    XCtlΦ i cpu ctrlOk (textOkCtl img ctrlOk textAt textAt4) G Φ := by
  unfold XCtlΦ
  intro s rs k pc is_rvc ins ot ow HRet Hctrl HPC Htx How Hcert Hb
  unfold XPost
  iintro C
  iapply (wpdInstrOfEvA3 img i Φ cpu G HG Hmid Htext Hflow
    (fun _ t' => GoodC ctrlOk is_rvc rs pc ot ow t'.regs) rs k s HRet Hb
    (AxSymCtl2.spineCertC img ctrlOk textAt textAt4 Hsp Hf4 rs pc is_rvc ins ot ow Hctrl HPC Htx How
      Hcert))
  iintro %t' %rs' %ib' %k' %HGc %Hag
  obtain ⟨Hc, Hpc, Hg⟩ := HGc
  have HRet' : RetX cpu rs' k' ⟨.PHart cpu (.pure ()) rs' none ib', k'⟩ :=
    ⟨ib', rfl, rfl, rfl, rfl, rfl, regsAgreeRefl _ _⟩
  have Hc' : ctrlOk rs' := Hsp.sptSeip _ _ Hc Hag
  have Hpc' : rs' .PC = tgtOf ot pc is_rvc :=
    (Hag .PC (AxSymEngine2.notPin _ (by decide) (by decide))).trans Hpc
  have Hg' : ∀ r : BitVec 5, r.toNat ≠ 0 → uxaXget rs' r = gprPost ow rs r :=
    fun r Hr => (AxSymEngine2.uxaXgetAgree _ _ Hag r).trans (Hg r Hr)
  iapply C $$ %_ %rs' %k' %HRet' %Hc' %Hpc' %Hg'

end xctl

/-! # 4. The per-instruction certificates and X corollaries -/

/-- Zca on, Zicfilp off, at every state of the regime. -/
def ctlRegime (ctrlOk : RegFile → Prop) : Prop :=
  ∀ s : ExecSt, ctrlOk s.regs →
    exec (currentlyEnabled .Ext_Zca) s = some (true, s) ∧
    exec (currentlyEnabled .Ext_Zicfilp) s = some (false, s)

/-- GPR value as `rX` reads it (x0 = 0). -/
def gval (r : BitVec 5) (rs : RegFile) : BitVec 64 :=
  if r.toNat = 0 then zero_reg else uxaXget rs r

/-- (Lean-only) `gval` is the model's GPR read. -/
theorem AxSymCtl2.gvalEq (r : BitVec 5) (rs : RegFile) : gval r rs = uxaXget rs r := by
  unfold gval
  split
  · rename_i h
    exact (AxReuseProbe2.uxaXgetZero rs r h).symm
  · rfl

theorem gvalAgree (a b : RegFile) (r : BitVec 5) : gprAgree a b → gval r a = gval r b := by
  intro Hag
  unfold gval
  split
  · rfl
  · rename_i h
    exact Hag r h

def jalrTgt (imm : BitVec 12) (base : BitVec 64) : BitVec 64 :=
  BitVec.update (base + sign_extend (m := 64) imm) 0 0#1

def linkOw (rd : BitVec 5) (v : BitVec 64) : Option (BitVec 5 × BitVec 64) :=
  if rd.toNat = 0 then none else some (rd, v)

theorem owOkLink (rd : BitVec 5) (v : BitVec 64) : owOk (linkOw rd v) := by
  unfold linkOw
  split
  · trivial
  · rename_i h
    exact h

theorem linkOwZero (rd : BitVec 5) (v : BitVec 64) : rd.toNat = 0 → linkOw rd v = none := by
  intro E
  unfold linkOw
  rw [if_pos E]

/-- Rocq `bcond` (file-qualified: `MachCSL.bcond` exists). -/
def AxSymCtl2.bcond (op : bop) (a b : BitVec 64) : Bool :=
  match op with
  | .BEQ => a == b
  | .BNE => a != b
  | .BLT => zopz0zI_s a b
  | .BGE => zopz0zKzJ_s a b
  | .BLTU => zopz0zI_u a b
  | .BGEU => zopz0zKzJ_u a b

def brOt (op : bop) (rs1 rs2 : BitVec 5) (rs : RegFile) (tg : BitVec 64) : Option (BitVec 64) :=
  if AxSymCtl2.bcond op (gval rs1 rs) (gval rs2 rs) then some tg else none

/-- (Lean-only, Rocq `UserBits.bit0_update0_64`) bit 0 of a cleared target is 0. -/
theorem AxSymCtl2.bit0Update0 (x : BitVec 64) :
    (BitVec.access (BitVec.update x 0 0#1) 0 == 0#1) = true := by
  have e : BitVec.update x 0 0#1 = 18446744073709551614#64 &&& x := by
    unfold Sail.BitVec.update Sail.BitVec.updateSubrange'
    bv_decide
  rw [e]
  unfold Sail.BitVec.access
  have h : (18446744073709551614#64 &&& x)[0] = false := by
    rw [BitVec.getElem_and]
    simp
  simp [h]

/-- (Lean-only) a write of `x0` is discarded. -/
theorem AxSymCtl2.setGprZero (s : ExecSt) (rd : BitVec 5) (v : BitVec 64) (E : rd.toNat = 0) :
    s.setGpr rd v = s := by
  have : rd = 0#5 := BitVec.eq_of_toNat_eq E
  subst this
  rfl

/-- (Lean-only) the optional link write is the model's GPR write. -/
theorem AxSymCtl2.wrOptLink (rd : BitVec 5) (v : BitVec 64) (s : ExecSt) :
    wrOpt (linkOw rd v) s = s.setGpr rd v := by
  unfold linkOw
  split
  · rename_i E
    exact (AxSymCtl2.setGprZero s rd v E).symm
  · rfl

section certs
variable (ctrlOk : RegFile → Prop) (HR : ctlRegime ctrlOk)

include HR in
theorem certJALR (rs : RegFile) (pc : BitVec 64) (is_rvc : Bool) (imm : BitVec 12)
    (rs1 rd : BitVec 5) :
    rs1.toNat ≠ 0 →
    CertC ctrlOk rs pc is_rvc (.JALR (imm, .Regidx rs1, .Regidx rd))
      (some (jalrTgt imm (uxaXget rs rs1))) (linkOw rd (BitVec.addInt pc (incr is_rvc))) := by
  intro Hrs1 s_pc Hc _ Hnpc Hag
  obtain ⟨Hzca, Hzic⟩ := HR s_pc Hc
  have Hg : s_pc.gpr rs1 = uxaXget rs rs1 := Hag rs1 Hrs1
  show exec (execute_JALR imm (.Regidx rs1) (.Regidx rd)) s_pc = _
  rw [execExecuteJALRZca imm rs1 rd s_pc Hzic Hzca (AxSymCtl2.bit0Update0 _), AxSymCtl2.wrOptLink,
    Hnpc, Hg]
  rfl

include HR in
theorem certJAL (rs : RegFile) (pc : BitVec 64) (is_rvc : Bool) (imm : BitVec 21) (rd : BitVec 5) :
    (BitVec.access (pc + sign_extend (m := 64) imm) 0 == 0#1) = true →
    CertC ctrlOk rs pc is_rvc (.JAL (imm, .Regidx rd))
      (some (pc + sign_extend (m := 64) imm)) (linkOw rd (BitVec.addInt pc (incr is_rvc))) := by
  intro Hal s_pc Hc HPC Hnpc _
  obtain ⟨Hzca, -⟩ := HR s_pc Hc
  have Hal' : (BitVec.access (s_pc.regs .PC + sign_extend (m := 64) imm) 0 == 0#1) = true := by
    rw [HPC]; exact Hal
  show exec (execute_JAL imm (.Regidx rd)) s_pc = _
  unfold execute_JAL get_next_pc
  exec_run [execJumpToZca _ s_pc Hal' Hzca, RETIRE_SUCCESS, execWXBitsGpr]
  rw [AxSymCtl2.wrOptLink, Hnpc, HPC]
  rfl

include HR in
theorem certBTYPE (rs : RegFile) (pc : BitVec 64) (is_rvc : Bool) (imm : BitVec 13)
    (rs2 rs1 : BitVec 5) (op : bop) :
    (BitVec.access (pc + sign_extend (m := 64) imm) 0 == 0#1) = true →
    CertC ctrlOk rs pc is_rvc (.BTYPE (imm, .Regidx rs2, .Regidx rs1, op))
      (brOt op rs1 rs2 rs (pc + sign_extend (m := 64) imm)) none := by
  intro Hal s_pc Hc HPC _ Hag
  obtain ⟨Hzca, -⟩ := HR s_pc Hc
  have Hal' : (BitVec.access (s_pc.regs .PC + sign_extend (m := 64) imm) 0 == 0#1) = true := by
    rw [HPC]; exact Hal
  have g1 : gval rs1 rs = s_pc.gpr rs1 :=
    (gvalAgree _ _ rs1 Hag).symm.trans (AxSymCtl2.gvalEq rs1 s_pc.regs)
  have g2 : gval rs2 rs = s_pc.gpr rs2 :=
    (gvalAgree _ _ rs2 Hag).symm.trans (AxSymCtl2.gvalEq rs2 s_pc.regs)
  show exec (execute_BTYPE imm (.Regidx rs2) (.Regidx rs1) op) s_pc = _
  unfold brOt
  rw [g1, g2]
  unfold execute_BTYPE
  cases op <;> exec_run [execRXBitsGpr, execIte, execJumpToZca _ s_pc Hal' Hzca] <;>
    simp only [AxSymCtl2.bcond] <;> split <;> simp only [npcOpt, wrOpt, HPC]

end certs

/-- The compressed expansions (execute of the compressed form = `ExecuteAs` the base form, at
every state). -/
theorem expEvA (img : Image) (i0 ins : instruction) :
    rfF (execute i0) → (∀ s, exec (execute i0) s = some (.ExecuteAs ins, s)) →
    ∀ t, EvA img (fun _ _ => False) (fun x t' => x = .ExecuteAs ins ∧ t' = t) (execute i0) t :=
  fun Hrf He t => EvAOfRfF img _ Hrf t _ _ (He t)

def cjImm (imm : BitVec 11) : BitVec 21 := sign_extend (m := 21) (imm ++ 0#1)

def ra5c : BitVec 5 := zero_extend (m := 5) 0b01#2

def cbImm (imm : BitVec 8) : BitVec 13 := sign_extend (m := 13) (imm ++ 0#1)

def creg5 (rsc : cregidx) : BitVec 5 :=
  match creg2reg_idx rsc with
  | .Regidx r => r

section xins
variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [AxirisG GF] [Axpol]
variable (img : Image) (i : Agent) (cpu : CPU)
variable (ctrlOk : RegFile → Prop) (textAt : BitVec 64 → BitVec 16 → Prop)
  (textAt4 : BitVec 64 → BitVec 32 → Prop)
variable (Hsp : SpineOkT img ctrlOk textAt) (Hf4 : SpineFetch4T img ctrlOk textAt4)
  (HR : ctlRegime ctrlOk)
variable (Htext : ∀ GD, rvwmoCatConsistent GD →
  AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜textFixed GD i img⌝)
variable (Hflow : ∀ GD ls k, rvwmoCatConsistent GD →
  (∃ lb aq base n vs, (AxOpsem.grow GD i)[k]? = some lb ∧ aident lb = .IRead aq base n ∧
     imgBytes img base n = some vs) →
  AxirisG.gconstInterp (GF := GF) GD ∗ AxirisG.localInterp GD i k ls ⊢ fetchFlow GD i k)
variable (G : Gdexec → Prop)
  (HG : ∀ GD, rvwmoCatConsistent GD → AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜G GD⌝)
  (Φ : Athread → IProp GF)
  (Hmid : ∀ GD s, G GD → midState s → s.atK = (AxOpsem.grow GD i).length →
    ⊢ postLifting Φ i s)

include Hsp Hf4 HR Htext Hflow HG Hmid in
/-- jalr rd, imm(rs1): PC := (rs1 + imm) with bit 0 cleared; rd := pc + incr. -/
theorem XJalr (s : Athread) (rs : RegFile) (k : Nat) (pc : BitVec 64) (is_rvc : Bool)
    (imm : BitVec 12) (rs1 rd : BitVec 5) :
    RetX cpu rs k s → ctrlOk rs → rs .PC = pc →
    textOkCtl img ctrlOk textAt textAt4 pc is_rvc (.JALR (imm, .Regidx rs1, .Regidx rd)) →
    rs1.toNat ≠ 0 →
    (∀ GD s1, G GD → RetX cpu rs k s1 → s1.atK = (AxOpsem.grow GD i).length →
      ⊢ postLifting Φ i s1) →
    ⊢ XPost i cpu ctrlOk Φ rs (jalrTgt imm (uxaXget rs rs1))
        (linkOw rd (BitVec.addInt pc (incr is_rvc))) -∗
      wpd .MaybeStuck i s Φ := by
  intro HRet Hc HPC Htx Hrs1 Hb
  exact XCtlΦHolds img i cpu ctrlOk textAt textAt4 Hsp Hf4 Htext Hflow G HG Φ Hmid
    s rs k pc is_rvc _ (some _) _ HRet Hc HPC Htx (owOkLink _ _)
    (certJALR ctrlOk HR rs pc is_rvc imm rs1 rd Hrs1) Hb

include Hsp Hf4 HR Htext Hflow HG Hmid in
/-- jal rd, imm: PC := pc + imm; rd := pc + incr. -/
theorem XJal (s : Athread) (rs : RegFile) (k : Nat) (pc : BitVec 64) (is_rvc : Bool)
    (imm : BitVec 21) (rd : BitVec 5) :
    RetX cpu rs k s → ctrlOk rs → rs .PC = pc →
    textOkCtl img ctrlOk textAt textAt4 pc is_rvc (.JAL (imm, .Regidx rd)) →
    (BitVec.access (pc + sign_extend (m := 64) imm) 0 == 0#1) = true →
    (∀ GD s1, G GD → RetX cpu rs k s1 → s1.atK = (AxOpsem.grow GD i).length →
      ⊢ postLifting Φ i s1) →
    ⊢ XPost i cpu ctrlOk Φ rs (pc + sign_extend (m := 64) imm)
        (linkOw rd (BitVec.addInt pc (incr is_rvc))) -∗
      wpd .MaybeStuck i s Φ := by
  intro HRet Hc HPC Htx Hal Hb
  exact XCtlΦHolds img i cpu ctrlOk textAt textAt4 Hsp Hf4 Htext Hflow G HG Φ Hmid
    s rs k pc is_rvc _ (some _) _ HRet Hc HPC Htx (owOkLink _ _)
    (certJAL ctrlOk HR rs pc is_rvc imm rd Hal) Hb

include Hsp Hf4 HR Htext Hflow HG Hmid in
/-- beq/bne/blt/bge/bltu/bgeu rs1, rs2, imm: BOTH outcomes in one post. -/
theorem XBtype (s : Athread) (rs : RegFile) (k : Nat) (pc : BitVec 64) (is_rvc : Bool)
    (imm : BitVec 13) (rs2 rs1 : BitVec 5) (op : bop) :
    RetX cpu rs k s → ctrlOk rs → rs .PC = pc →
    textOkCtl img ctrlOk textAt textAt4 pc is_rvc (.BTYPE (imm, .Regidx rs2, .Regidx rs1, op)) →
    (BitVec.access (pc + sign_extend (m := 64) imm) 0 == 0#1) = true →
    (∀ GD s1, G GD → RetX cpu rs k s1 → s1.atK = (AxOpsem.grow GD i).length →
      ⊢ postLifting Φ i s1) →
    ⊢ XPost i cpu ctrlOk Φ rs
        (if AxSymCtl2.bcond op (gval rs1 rs) (gval rs2 rs) then pc + sign_extend (m := 64) imm
         else BitVec.addInt pc (incr is_rvc)) none -∗
      wpd .MaybeStuck i s Φ := by
  intro HRet Hc HPC Htx Hal Hb
  have HX := XCtlΦHolds img i cpu ctrlOk textAt textAt4 Hsp Hf4 Htext Hflow G HG Φ Hmid
    s rs k pc is_rvc _ _ none HRet Hc HPC Htx trivial
    (certBTYPE ctrlOk HR rs pc is_rvc imm rs2 rs1 op Hal) Hb
  have e : tgtOf (brOt op rs1 rs2 rs (pc + sign_extend (m := 64) imm)) pc is_rvc =
      (if AxSymCtl2.bcond op (gval rs1 rs) (gval rs2 rs) then pc + sign_extend (m := 64) imm
       else BitVec.addInt pc (incr is_rvc)) := by
    unfold tgtOf brOt
    cases AxSymCtl2.bcond op (gval rs1 rs) (gval rs2 rs) <;> rfl
  rw [e] at HX
  exact HX

include Hsp Hf4 HR Htext Hflow HG Hmid in
theorem XCj (s : Athread) (rs : RegFile) (k : Nat) (pc : BitVec 64) (imm : BitVec 11) :
    RetX cpu rs k s → ctrlOk rs → rs .PC = pc →
    textOkCtl img ctrlOk textAt textAt4 pc true (.JAL (cjImm imm, zreg)) →
    (BitVec.access (pc + sign_extend (m := 64) (cjImm imm)) 0 == 0#1) = true →
    (∀ GD s1, G GD → RetX cpu rs k s1 → s1.atK = (AxOpsem.grow GD i).length →
      ⊢ postLifting Φ i s1) →
    ⊢ XPost i cpu ctrlOk Φ rs (pc + sign_extend (m := 64) (cjImm imm)) none -∗
      wpd .MaybeStuck i s Φ := by
  intro HRet Hc HPC Htx Hal Hb
  have HX := XJal img i cpu ctrlOk textAt textAt4 Hsp Hf4 HR Htext Hflow G HG Φ Hmid
    s rs k pc true (cjImm imm) (zero_extend (m := 5) 0b00#2) HRet Hc HPC Htx Hal Hb
  rw [linkOwZero _ _ (by decide)] at HX
  exact HX

include Hsp Hf4 HR Htext Hflow HG Hmid in
theorem XCjr (s : Athread) (rs : RegFile) (k : Nat) (pc : BitVec 64) (rs1 : BitVec 5) :
    RetX cpu rs k s → ctrlOk rs → rs .PC = pc →
    textOkCtl img ctrlOk textAt textAt4 pc true (.JALR (zeros (n := 12), .Regidx rs1, zreg)) →
    rs1.toNat ≠ 0 →
    (∀ GD s1, G GD → RetX cpu rs k s1 → s1.atK = (AxOpsem.grow GD i).length →
      ⊢ postLifting Φ i s1) →
    ⊢ XPost i cpu ctrlOk Φ rs (jalrTgt (zeros (n := 12)) (uxaXget rs rs1)) none -∗
      wpd .MaybeStuck i s Φ := by
  intro HRet Hc HPC Htx Hrs1 Hb
  have HX := XJalr img i cpu ctrlOk textAt textAt4 Hsp Hf4 HR Htext Hflow G HG Φ Hmid
    s rs k pc true (zeros (n := 12)) rs1 (zero_extend (m := 5) 0b00#2) HRet Hc HPC Htx Hrs1 Hb
  rw [linkOwZero _ _ (by decide)] at HX
  exact HX

include Hsp Hf4 HR Htext Hflow HG Hmid in
theorem XCjalr (s : Athread) (rs : RegFile) (k : Nat) (pc : BitVec 64) (rs1 : BitVec 5) :
    RetX cpu rs k s → ctrlOk rs → rs .PC = pc →
    textOkCtl img ctrlOk textAt textAt4 pc true (.JALR (zeros (n := 12), .Regidx rs1, ra)) →
    rs1.toNat ≠ 0 →
    (∀ GD s1, G GD → RetX cpu rs k s1 → s1.atK = (AxOpsem.grow GD i).length →
      ⊢ postLifting Φ i s1) →
    ⊢ XPost i cpu ctrlOk Φ rs (jalrTgt (zeros (n := 12)) (uxaXget rs rs1))
        (some (ra5c, BitVec.addInt pc 2)) -∗
      wpd .MaybeStuck i s Φ := by
  intro HRet Hc HPC Htx Hrs1 Hb
  have HX := XJalr img i cpu ctrlOk textAt textAt4 Hsp Hf4 HR Htext Hflow G HG Φ Hmid
    s rs k pc true (zeros (n := 12)) rs1 ra5c HRet Hc HPC Htx Hrs1 Hb
  have e : linkOw ra5c (BitVec.addInt pc (incr true)) = some (ra5c, BitVec.addInt pc 2) := by
    unfold linkOw
    rw [if_neg (by decide)]
    rfl
  rw [e] at HX
  exact HX

include Hsp Hf4 HR Htext Hflow HG Hmid in
/-- c.ret = c.jr ra. -/
theorem XCret (s : Athread) (rs : RegFile) (k : Nat) (pc : BitVec 64) :
    RetX cpu rs k s → ctrlOk rs → rs .PC = pc →
    textOkCtl img ctrlOk textAt textAt4 pc true (.JALR (zeros (n := 12), ra, zreg)) →
    (∀ GD s1, G GD → RetX cpu rs k s1 → s1.atK = (AxOpsem.grow GD i).length →
      ⊢ postLifting Φ i s1) →
    ⊢ XPost i cpu ctrlOk Φ rs (jalrTgt (zeros (n := 12)) (uxaXget rs ra5c)) none -∗
      wpd .MaybeStuck i s Φ := by
  intro HRet Hc HPC Htx Hb
  exact XCjr img i cpu ctrlOk textAt textAt4 Hsp Hf4 HR Htext Hflow G HG Φ Hmid
    s rs k pc ra5c HRet Hc HPC Htx (by decide) Hb

include Hsp Hf4 HR Htext Hflow HG Hmid in
/-- c.beqz rs', imm = beq rs', x0. -/
theorem XCbeqz (s : Athread) (rs : RegFile) (k : Nat) (pc : BitVec 64) (imm : BitVec 8)
    (rsc : cregidx) :
    RetX cpu rs k s → ctrlOk rs → rs .PC = pc →
    textOkCtl img ctrlOk textAt textAt4 pc true (.BTYPE (cbImm imm, zreg, .Regidx (creg5 rsc), .BEQ)) →
    (BitVec.access (pc + sign_extend (m := 64) (cbImm imm)) 0 == 0#1) = true →
    (∀ GD s1, G GD → RetX cpu rs k s1 → s1.atK = (AxOpsem.grow GD i).length →
      ⊢ postLifting Φ i s1) →
    ⊢ XPost i cpu ctrlOk Φ rs
        (if (gval (creg5 rsc) rs == zero_reg) then pc + sign_extend (m := 64) (cbImm imm)
         else BitVec.addInt pc 2) none -∗
      wpd .MaybeStuck i s Φ := by
  intro HRet Hc HPC Htx Hal Hb
  exact XBtype img i cpu ctrlOk textAt textAt4 Hsp Hf4 HR Htext Hflow G HG Φ Hmid
    s rs k pc true (cbImm imm) (zero_extend (m := 5) 0b00#2) (creg5 rsc) .BEQ HRet Hc HPC Htx Hal Hb

include Hsp Hf4 HR Htext Hflow HG Hmid in
/-- c.bnez rs', imm = bne rs', x0. -/
theorem XCbnez (s : Athread) (rs : RegFile) (k : Nat) (pc : BitVec 64) (imm : BitVec 8)
    (rsc : cregidx) :
    RetX cpu rs k s → ctrlOk rs → rs .PC = pc →
    textOkCtl img ctrlOk textAt textAt4 pc true (.BTYPE (cbImm imm, zreg, .Regidx (creg5 rsc), .BNE)) →
    (BitVec.access (pc + sign_extend (m := 64) (cbImm imm)) 0 == 0#1) = true →
    (∀ GD s1, G GD → RetX cpu rs k s1 → s1.atK = (AxOpsem.grow GD i).length →
      ⊢ postLifting Φ i s1) →
    ⊢ XPost i cpu ctrlOk Φ rs
        (if (gval (creg5 rsc) rs != zero_reg) then pc + sign_extend (m := 64) (cbImm imm)
         else BitVec.addInt pc 2) none -∗
      wpd .MaybeStuck i s Φ := by
  intro HRet Hc HPC Htx Hal Hb
  exact XBtype img i cpu ctrlOk textAt textAt4 Hsp Hf4 HR Htext Hflow G HG Φ Hmid
    s rs k pc true (cbImm imm) (zero_extend (m := 5) 0b00#2) (creg5 rsc) .BNE HRet Hc HPC Htx Hal Hb

end xins

/-! # 5. At the S-mode kernel regime -/

/-- Rocq `cE_zicfilp_false_S` (deviation 7). -/
theorem cEZicfilpFalseS (s : ExecSt) :
    s.regs .cur_privilege = .Supervisor →
    bool_bit_backwards (_get_MEnvcfg_LPE (s.regs .menvcfg)) = false →
    exec (currentlyEnabled .Ext_Zicfilp) s = some (false, s) := by
  intro Hpriv Hlpe
  rw [currentlyEnabled]
  have h1 : hartSupports .Ext_Zicfilp = true := by decide +kernel
  simp only [h1, ↓reduceIte]
  unfold get_xLPE
  exec_run [execCurrentlyEnabledZicsr, Hpriv, Hlpe]

theorem ctlRegimeS (T : PTree) (satp0 : BitVec 64) : ctlRegime (ctrlOkS T satp0) := by
  intro s hc
  refine ⟨execCurrentlyEnabledZca s (by rw [hc.2.2.1]; decide), cEZicfilpFalseS s hc.1 ?_⟩
  rw [hc.2.2.2.1]
  decide

section xS
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
/-- X for control transfers AT THE S-MODE KERNEL REGIME (compressed text: the 4-byte text
predicate is empty). -/
theorem XCtlSRvc (G : Gdexec → Prop)
    (HG : ∀ GD, rvwmoCatConsistent GD → AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜G GD⌝)
    (Φ : Athread → IProp GF)
    (Hmid : ∀ GD s, G GD → midState s → s.atK = (AxOpsem.grow GD i).length →
      ⊢ postLifting Φ i s) :
    XCtlΦ i cpu (ctrlOkS T satp0) (textOkCtl (imgS σi) (ctrlOkS T satp0) (textAtS σi T) no4) G Φ :=
  XCtlΦHolds (imgS σi) i cpu _ _ no4 (spineOkTS σi T satp0 hmode hasid hppn)
    (SpineFetch4TNo4 _ _) Htext Hflow G HG Φ Hmid

end xS

/-! ### c.ret and c.beqz at the REAL Tier-A instance (`axGA2` with the real `protInv`) -/

section realGa2
variable {hlc : HasLC} {GF : BundledGFunctors.{0,0,0}} [InvGS_gen hlc GF] [AxannotGS GF]
  [pol : Axpol] [AxlogG GF Hent]
variable (GD0 : Gdexec) (γ : GName)
variable (σi : ExecSt) (T : PTree) (satp0 : BitVec 64) (i : Agent) (cpu : CPU)
variable (hmode : _get_Satp64_Mode (Mk_Satp64 satp0) = 8#4)
  (hasid : zero_extend (m := 16) (satp_to_asid satp0) = 0#16)
  (hppn : BitVec.setWidth 44 (satp_to_ppn satp0) = T.base)
variable (Hfix : textFixed GD0 i (imgS σi))

include hmode hasid hppn Hfix in
/-- c.ret: the continuation gets PC = ra (bit 0 cleared), GPRs unchanged. -/
theorem wpdCretGa2 (P : RegFile → Prop) (s0 : Athread) (rs0 : RegFile) (k0 : Nat)
    (pc : BitVec 64) :
    RetX cpu rs0 k0 s0 → ctrlOkS T satp0 rs0 → rs0 .PC = pc →
    textOkCtl (imgS σi) (ctrlOkS T satp0) (textAtS σi T) no4 pc true
      (.JALR (zeros (n := 12), ra, zreg)) →
    (∀ rs', regsAgree AxRunClose.pinReg rs' rs0 → P rs') →
    ⊢ @XPost hlc GF _ (blkGa2 GD0 γ) pol i cpu (ctrlOkS T satp0) (ΦRet (GF := GF) cpu P) rs0
        (jalrTgt (zeros (n := 12)) (uxaXget rs0 ra5c)) none -∗
      @wpd hlc GF _ (blkGa2 GD0 γ) pol .MaybeStuck i s0 (ΦRet (GF := GF) cpu P) := by
  intro HR0 Hc0 HPC0 Htx HP0
  exact @XCret hlc GF _ (blkGa2 GD0 γ) pol (imgS σi) i cpu _ _ no4
    (spineOkTS σi T satp0 hmode hasid hppn) (SpineFetch4TNo4 _ _) (ctlRegimeS T satp0)
    (HtextGa2 GD0 GName Unit _ γ (imgS σi) i Hfix)
    (fun GD ls k hc hx => HflowGa2 GD0 GName Unit _ γ (imgS σi) i
      (fun GD σ s e Hnin Hnw => protInvReadStep γ GD s e Hnin Hnw) GD ls k hc hx)
    (fun _ => True) (fun _ _ => BI.pure_intro trivial) (ΦRet (GF := GF) cpu P)
    (@ΦRetMid hlc GF _ (blkGa2 GD0 γ) i cpu P _) s0 rs0 k0 pc HR0 Hc0 HPC0 Htx
    (fun _ s1 _ HR _ => @ΦRetBoundary hlc GF _ (blkGa2 GD0 γ) i cpu P rs0 k0 s1 HP0 HR)

include hmode hasid hppn Hfix in
/-- c.beqz: both outcomes, the condition on the symbolic register value. -/
theorem wpdCbeqzGa2 (P : RegFile → Prop) (s0 : Athread) (rs0 : RegFile) (k0 : Nat)
    (pc : BitVec 64) (imm : BitVec 8) (rsc : cregidx) :
    RetX cpu rs0 k0 s0 → ctrlOkS T satp0 rs0 → rs0 .PC = pc →
    textOkCtl (imgS σi) (ctrlOkS T satp0) (textAtS σi T) no4 pc true
      (.BTYPE (cbImm imm, zreg, .Regidx (creg5 rsc), .BEQ)) →
    (BitVec.access (pc + sign_extend (m := 64) (cbImm imm)) 0 == 0#1) = true →
    (∀ rs', regsAgree AxRunClose.pinReg rs' rs0 → P rs') →
    ⊢ @XPost hlc GF _ (blkGa2 GD0 γ) pol i cpu (ctrlOkS T satp0) (ΦRet (GF := GF) cpu P) rs0
        (if (gval (creg5 rsc) rs0 == zero_reg) then pc + sign_extend (m := 64) (cbImm imm)
         else BitVec.addInt pc 2) none -∗
      @wpd hlc GF _ (blkGa2 GD0 γ) pol .MaybeStuck i s0 (ΦRet (GF := GF) cpu P) := by
  intro HR0 Hc0 HPC0 Htx Hal HP0
  exact @XCbeqz hlc GF _ (blkGa2 GD0 γ) pol (imgS σi) i cpu _ _ no4
    (spineOkTS σi T satp0 hmode hasid hppn) (SpineFetch4TNo4 _ _) (ctlRegimeS T satp0)
    (HtextGa2 GD0 GName Unit _ γ (imgS σi) i Hfix)
    (fun GD ls k hc hx => HflowGa2 GD0 GName Unit _ γ (imgS σi) i
      (fun GD σ s e Hnin Hnw => protInvReadStep γ GD s e Hnin Hnw) GD ls k hc hx)
    (fun _ => True) (fun _ _ => BI.pure_intro trivial) (ΦRet (GF := GF) cpu P)
    (@ΦRetMid hlc GF _ (blkGa2 GD0 γ) i cpu P _) s0 rs0 k0 pc imm rsc HR0 Hc0 HPC0 Htx Hal
    (fun _ s1 _ HR _ => @ΦRetBoundary hlc GF _ (blkGa2 GD0 γ) i cpu P rs0 k0 s1 HP0 HR)

end realGa2

/-! # 6. NON-VACUITY on the real model -/

/-- c.jr ra (0x8082) at `nvPc` = 0x80000002. -/
def nvcImg (a : Int) : Option (BitVec 8) :=
  if a = nvPc then some 0x82#8 else if a = nvPc + 1 then some 0x80#8 else none

def nvcPost (_ : Unit) (t' : ExecSt) : Bool :=
  (t'.regs .PC == jalrTgt (zeros (n := 12)) (uxaXget nvT.regs ra5c)) &&
  (t'.regs .PC == AxEpiProbe.w64 raVal) &&
  (uxaXget t'.regs ra5c == uxaXget nvT.regs ra5c)

theorem nvcStepFalse : evb nvcImg nvcPost (riscvStep false) nvT = true := by decide +kernel

theorem nvcStepTrue : evb nvcImg nvcPost (riscvStep true) nvT = true := by decide +kernel

theorem nvcCert (tick : Bool) :
    EvA nvcImg (fun _ _ => False) (fun x t' => nvcPost x t' = true) (riscvStep tick) nvT := by
  apply evbSound
  cases tick
  · exact nvcStepFalse
  · exact nvcStepTrue

/-- Decode + expansion of 0x8082 = `JALR (zeros 12, ra, zreg)` (c.ret). -/
theorem nvcDecodeExpand :
    evb nvcImg (fun r _ => match r with
      | .ExecuteAs (.JALR (imm, .Regidx a, .Regidx b)) =>
        imm == zeros (n := 12) && a == ra5c && b == 0#5
      | _ => false)
      (ext_decode_compressed 0x8082#16 >>= execute) nvT = true := by decide +kernel

/-- beq ra, ra, +8 (0x00108463, TAKEN) / bne ra, ra, +8 (0x00109463, falls through) at the
4-aligned 0x80000000. -/
def nvbPc : Nat := 0x80000000

def nvbT : ExecSt := tAt nvbPc

def nvbImg (w : Nat) (a : Int) : Option (BitVec 8) :=
  if a = nvbPc then some (BitVec.ofNat 8 w)
  else if a = nvbPc + 1 then some (BitVec.ofNat 8 (w >>> 8))
  else if a = nvbPc + 2 then some (BitVec.ofNat 8 (w >>> 16))
  else if a = nvbPc + 3 then some (BitVec.ofNat 8 (w >>> 24)) else none

def nvbImm : BitVec 13 := 8#13

def nvbPost (op : bop) (_ : Unit) (t' : ExecSt) : Bool :=
  t'.regs .PC == tgtOf (brOt op ra5c ra5c nvbT.regs
      (AxEpiProbe.w64 nvbPc + sign_extend (m := 64) nvbImm)) (AxEpiProbe.w64 nvbPc) false

theorem nvbBeqFalse : evb (nvbImg 0x00108463) (nvbPost .BEQ) (riscvStep false) nvbT = true := by
  decide +kernel

theorem nvbBeqTrue : evb (nvbImg 0x00108463) (nvbPost .BEQ) (riscvStep true) nvbT = true := by
  decide +kernel

theorem nvbBneFalse : evb (nvbImg 0x00109463) (nvbPost .BNE) (riscvStep false) nvbT = true := by
  decide +kernel

theorem nvbBneTrue : evb (nvbImg 0x00109463) (nvbPost .BNE) (riscvStep true) nvbT = true := by
  decide +kernel

/-- The two outcomes really differ: beq taken to pc+8, bne falls to pc+4. -/
theorem nvbOutcomes :
    tgtOf (brOt .BEQ ra5c ra5c nvbT.regs (AxEpiProbe.w64 nvbPc + sign_extend (m := 64) nvbImm))
        (AxEpiProbe.w64 nvbPc) false = AxEpiProbe.w64 (nvbPc + 8) ∧
    tgtOf (brOt .BNE ra5c ra5c nvbT.regs (AxEpiProbe.w64 nvbPc + sign_extend (m := 64) nvbImm))
        (AxEpiProbe.w64 nvbPc) false = AxEpiProbe.w64 (nvbPc + 4) :=
  ⟨by decide +kernel, by decide +kernel⟩

theorem nvbDecode :
    evb (nvbImg 0x00108463) (fun x _ => match x with
      | .BTYPE (imm, .Regidx a, .Regidx b, .BEQ) => imm == nvbImm && a == ra5c && b == ra5c
      | _ => false)
      (ext_decode 0x00108463#32) nvbT = true := by decide +kernel

/-- c.beqz a0, +8 (0xC501) at `nvPc`: a0 ≠ 0 at the probe state ⇒ falls through to pc + 2, as
the symbolic `brOt` says. -/
def nvzImg (a : Int) : Option (BitVec 8) :=
  if a = nvPc then some 0x01#8 else if a = nvPc + 1 then some 0xC5#8 else none

def nvzRsc : cregidx := .Cregidx 2#3

def nvzPost (_ : Unit) (t' : ExecSt) : Bool :=
  t'.regs .PC == tgtOf (brOt .BEQ (creg5 nvzRsc) (zero_extend (m := 5) 0b00#2) nvT.regs
      (AxEpiProbe.w64 nvPc + sign_extend (m := 64) (cbImm 4#8))) (AxEpiProbe.w64 nvPc) true

theorem nvzStepFalse : evb nvzImg nvzPost (riscvStep false) nvT = true := by decide +kernel

theorem nvzStepTrue : evb nvzImg nvzPost (riscvStep true) nvT = true := by decide +kernel

theorem nvzDecodeExpand :
    evb nvzImg (fun r _ => match r with
      | .ExecuteAs (.BTYPE (imm, .Regidx a, .Regidx b, .BEQ)) =>
        imm == cbImm 4#8 && a == 0#5 && b == creg5 nvzRsc
      | _ => false)
      (ext_decode_compressed 0xC501#16 >>= execute) nvT = true := by decide +kernel

end Weak
