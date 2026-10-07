/-
Weak: **the SpineOk interface with a TLB-FILLING fetch.**

Rocq: `iris/AxSpineOk5.v` @ xxvzwolszwmp.

## The Rocq header, in substance

FINDING (interface).  `AxSymEngine2.SpineOk.spFetch` demands that the fetch leave the state
UNCHANGED (`t' = t`).  Under Sv39 that is false on every TLB MISS: `translate_TLB_miss` ends in
`add_to_TLB`, a write of the `tlb` register (the only state change).  A regime whose TLB always
hits the text page cannot be the real kernel's (loads/stores evict the direct-mapped slots).  So
`SpineOkT` replaces `spFetch` by `sptFetch`: the fetch ends in SOME state `t1` that is `t` up to
the `tlb` register and is again in the regime; everything else is `SpineOk`'s.  `spineOkT`:
every `SpineOk` is a `SpineOkT` (strict generalization).  `spineCertT` / `XGprWriteHoldsT` /
`wpCmvDRealT` / `wpCaddiwDRealT` are the slice-1 theorems of `AxSymEngine2` re-derived over it
(same scripts, the post-fetch state threaded through).

## Deviations from Rocq

All of `AxSymEngine2`'s deviations apply (the pins `seip_reg` ↦ `AxRunClose.pinReg`; types
`mstate` ↦ `ExecSt`, `register_lookup r rs` ↦ `rs r`, `set_reg` ↦ `ExecSt.setReg`; registers an
enum, `R_bitvector_64 (gpr_of_Z (uint rd))` writes ↦ `ExecSt.setGpr rd`, `gpr_agree` ↦
`gprAgree`; Stage C: the section premise `Hloc` is DROPPED from §3, as in `AxSymEngine2` §5;
`invGS_gen HasNoLc Σ` ↦ `[InvGS_gen hlc GF]`, `GenId` dropped).  In particular:
1. Rocq's `ev_step`/`ev_go`/`ev_use` Ltacs (redeclared in Rocq's `regimeT` section) are not
   redeclared: the proofs use `AxSymEngine2`'s kit and tactic `ax_sym2_ev_go`; `nseip` ↦
   `AxSymEngine2.notPin`; `lk` ↦ `RegFile.set_same`/`set_other` rewrites.
2. `wp_cmv_d_real_T`/`wp_caddiw_d_real_T` (Rocq `Definition`s naming the instantiated leaves)
   ↦ theorems restating `AxReuseProbe2.wpCmvD`/`wpCaddiwD` at `textOkD img ctrlOk textAt`
   (as `AxSymEngine2` deviation 7).
3. `tlbFrame`'s second disjunct: `∃ v : RegisterType .tlb, t1 = t.setReg .tlb v`.

**Rocq → Lean name map.**  `tlb_frame` `tlbFrame`, `SpineOkT` `SpineOkT` (fields `spt_seip`
`sptSeip`, `spt_hart` `sptHart`, `spt_frame` `sptFrame`, `spt_inc` `sptInc`, `spt_disp`
`sptDisp`, `spt_fetch` `sptFetch`, `spt_lpad` `sptLpad`, `spt_zca` `sptZca`, `spt_tick`
`sptTick`), `SpineOk_T` `spineOkT`, `EvA_hart_active_rvc_T` `EvAHartActiveRvcT`,
`tlb_frame_lookup` `tlbFrameLookup`, `spine_cert_T` `spineCertT`, `X_gpr_write_holds_T`
`XGprWriteHoldsT`, `wp_cmv_d_real_T` `wpCmvDRealT`, `wp_caddiw_d_real_T` `wpCaddiwDRealT`.
None is in the duplicated-name table.  Lean-only (file-qualified): `AxSpineOk5.tlbFrameXget`
(GPR values survive a TLB frame).

**Dropped:** nothing (Rocq 9 definitions/lemmas + 4 Ltacs; Lean 9 + 1 Lean-only).
**Not ported:** the `Print Assumptions` lines (the lint's axiom check covers them).
-/
import Weak.AxSymEngine2

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std MachCSL
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D LeanRV64D.Functions

/-- `t1` is `t` up to the `tlb` register. -/
def tlbFrame (t t1 : ExecSt) : Prop :=
  t1 = t ∨ ∃ v : RegisterType .tlb, t1 = t.setReg .tlb v

/-! # 1. The regime with a TLB-filling fetch -/

section regimeT
variable (img : Image)

structure SpineOkT (ctrlOk : RegFile → Prop) (textAt : BitVec 64 → BitVec 16 → Prop) : Prop where
  sptSeip : ∀ rs rs', ctrlOk rs → regsAgree AxRunClose.pinReg rs' rs → ctrlOk rs'
  sptHart : ∀ rs, ctrlOk rs → rs .hart_state = .HART_ACTIVE ()
  sptFrame : ∀ rs (r : Register) (v : RegisterType r), ctrlFree r → ctrlOk rs → ctrlOk (rs.set r v)
  sptInc : ∀ t : ExecSt, ctrlOk t.regs → ∃ b, EvA img (fun _ _ => False) (fun x t' => x = b ∧ t' = t)
    (should_inc_minstret (t.regs .cur_privilege)) t
  sptDisp : ∀ t : ExecSt, ctrlOk t.regs → EvA img (fun _ _ => False) (fun r t' => r = none ∧ t' = t)
    (dispatchInterrupt (t.regs .cur_privilege)) t
  sptFetch : ∀ (t : ExecSt) pc h, ctrlOk t.regs → t.regs .PC = pc → textAt pc h →
    ∃ t1, tlbFrame t t1 ∧ ctrlOk t1.regs ∧
      EvA img (fun _ _ => False) (fun r t' => r = .F_RVC h ∧ t' = t1) (fetch ()) t
  sptLpad : ∀ t : ExecSt, ctrlOk t.regs →
    EvA img (fun _ _ => False) (fun x t' => x = false ∧ t' = t) (is_landing_pad_expected ()) t
  sptZca : ∀ t : ExecSt, ctrlOk t.regs →
    EvA img (fun _ _ => False) (fun x t' => x = true ∧ t' = t) (currentlyEnabled .Ext_Zca) t
  sptTick : ∀ t : ExecSt, ctrlOk t.regs →
    EvA img (fun _ _ => False) (fun _ t' => ctrlOk t'.regs ∧ keepRegs t.regs t'.regs) (tick_clock ()) t

theorem spineOkT (ctrlOk : RegFile → Prop) (textAt : BitVec 64 → BitVec 16 → Prop) :
    SpineOk img ctrlOk textAt → SpineOkT img ctrlOk textAt := by
  intro H
  exact ⟨H.spSeip, H.spHart, H.spFrame, H.spInc, H.spDisp,
    fun t pc h Hc Hpc Ht => ⟨t, Or.inl rfl, Hc, H.spFetch t pc h Hc Hpc Ht⟩,
    H.spLpad, H.spZca, H.spTick⟩

theorem EvAHartActiveRvcT (t t1 : ExecSt) (h : BitVec 16) (i0 ins : instruction) (pc : BitVec 64)
    (Qx : ExecSt → Prop) :
    EvA img (fun _ _ => False) (fun r t' => r = none ∧ t' = t)
      (dispatchInterrupt (t.regs .cur_privilege)) t →
    EvA img (fun _ _ => False) (fun r t' => r = .F_RVC h ∧ t' = t1) (fetch ()) t →
    EvA img (fun _ _ => False) (fun x t' => x = i0 ∧ t' = t1) (ext_decode_compressed h) t1 →
    EvA img (fun _ _ => False) (fun x t' => x = false ∧ t' = t1) (is_landing_pad_expected ()) t1 →
    EvA img (fun _ _ => False) (fun x t' => x = true ∧ t' = t1) (currentlyEnabled .Ext_Zca) t1 →
    t1.regs .PC = pc →
    EvA img (fun _ _ => False)
      (fun x t' => x = .ExecuteAs ins ∧ t' = t1.setReg .nextPC (BitVec.addInt pc 2))
      (execute i0) (t1.setReg .nextPC (BitVec.addInt pc 2)) →
    EvA img (fun _ _ => False) (fun x t' => x = RETIRE_SUCCESS ∧ Qx t') (execute ins)
      (t1.setReg .nextPC (BitVec.addInt pc 2)) →
    EvA img (fun _ _ => False)
      (fun x t' => x = .Step_Execute (RETIRE_SUCCESS, zero_extend (m := 32) h) ∧ Qx t')
      (run_hart_active 0) t := by
  intro Hdisp Hfetch Hdec Hlpad Hzca HPC Hexp Hexec
  subst HPC
  unfold run_hart_active
  apply EvACatchEarlyReturn
  ax_sym2_ev_go
  refine AxSymEngine2.evRUse Hdisp ?_
  ax_sym2_ev_go
  refine AxSymEngine2.evRUse Hfetch ?_
  ax_sym2_ev_go
  refine AxSymEngine2.evRUse Hdec ?_
  ax_sym2_ev_go
  refine AxSymEngine2.evRUse Hlpad ?_
  ax_sym2_ev_go
  refine AxSymEngine2.evRUse Hzca ?_
  ax_sym2_ev_go
  refine AxSymEngine2.evRUse Hexp ?_
  ax_sym2_ev_go
  refine EvAFactLift img _ _ _ _ _ _ Hexec ?_
  rintro _ t' ⟨rfl, hq⟩
  exact .evRet _ _ ⟨rfl, hq⟩

end regimeT

theorem tlbFrameLookup (t t1 : ExecSt) (r : Register) :
    tlbFrame t t1 → r ≠ .tlb → t1.regs r = t.regs r := by
  rintro (rfl | ⟨v, rfl⟩) Hr
  · rfl
  · rw [ExecSt.setReg_regs]
    exact RegFile.set_other _ _ _ _ (fun e => Hr e)

/-- (Lean-only) GPR values survive a TLB frame. -/
theorem AxSpineOk5.tlbFrameXget (t t1 : ExecSt) (Hfr : tlbFrame t t1) (z : BitVec 5) :
    uxaXget t1.regs z = uxaXget t.regs z := by
  rcases Hfr with rfl | ⟨v, rfl⟩
  · rfl
  · rw [ExecSt.setReg_regs]
    exact AxSymEngine2.uxaXgetSetNe _ _ _ (by decide) z

/-! # 2. The whole-instruction certificate over `SpineOkT` -/

section certT
variable (img : Image)

theorem spineCertT (ctrlOk : RegFile → Prop) (textAt : BitVec 64 → BitVec 16 → Prop)
    (Hsp : SpineOkT img ctrlOk textAt) (rs : RegFile) (pc : BitVec 64) (ins : instruction)
    (rd : BitVec 5) (wval : BitVec 64) :
    ctrlOk rs → rs .PC = pc → textOkD img ctrlOk textAt pc true ins → rd.toNat ≠ 0 →
    (∀ s_pc : ExecSt,
       s_pc.regs .nextPC = BitVec.addInt pc 2 →
       gprAgree s_pc.regs rs →
       exec (execute ins) s_pc = some (RETIRE_SUCCESS, s_pc.setGpr rd wval)) →
    ∀ (tick : Bool) (t : ExecSt), regsAgree AxRunClose.pinReg t.regs rs →
      EvA img (fun _ _ => False) (fun _ t' => Good ctrlOk rs pc rd wval t'.regs) (riscvStep tick) t := by
  intro Hct HPC ⟨_, h, i0, Hat, Hdec, Hexp, Hrf⟩ Hrd Hcert tick t Hag
  have Hct_t : ctrlOk t.regs := Hsp.sptSeip _ _ Hct Hag
  have HPC_t : t.regs .PC = pc := by
    rw [Hag .PC (AxSymEngine2.notPin _ (by decide) (by decide))]; exact HPC
  obtain ⟨b, Hb⟩ := Hsp.sptInc t Hct_t
  have Hct_a : ctrlOk (t.setReg .minstret_increment b).regs :=
    Hsp.sptFrame _ _ _ (Or.inr (Or.inr (Or.inl rfl))) Hct_t
  have HPC_a : (t.setReg .minstret_increment b).regs .PC = pc := by
    rw [ExecSt.setReg_regs, RegFile.set_other _ _ _ _ (by decide)]; exact HPC_t
  obtain ⟨t1, Hfr, Hct_1, Hfetch⟩ := Hsp.sptFetch _ pc h Hct_a HPC_a Hat
  have HPC_1 : t1.regs .PC = pc := (tlbFrameLookup _ _ _ Hfr (by decide)).trans HPC_a
  have Hgag : gprAgree (t1.setReg .nextPC (BitVec.addInt pc 2)).regs rs := by
    intro r _
    simp only [ExecSt.setReg_regs]
    rw [AxSymEngine2.uxaXgetSetNe _ _ _ (by decide), AxSpineOk5.tlbFrameXget _ _ Hfr,
      ExecSt.setReg_regs, AxSymEngine2.uxaXgetSetNe _ _ _ (by decide)]
    exact AxSymEngine2.uxaXgetAgree _ _ Hag r
  have Hexec : EvA img (fun _ _ => False)
      (fun x t' => x = RETIRE_SUCCESS ∧
        t' = (t1.setReg .nextPC (BitVec.addInt pc 2)).setGpr rd wval)
      (execute ins) (t1.setReg .nextPC (BitVec.addInt pc 2)) :=
    rf0EvA img _ _ Hrf _ _ _ (Hcert _ (by simp only [ExecSt.setReg_regs, RegFile.set_same]) Hgag)
  have Hrun := EvAHartActiveRvcT img (t.setReg .minstret_increment b) t1 h i0 ins pc
    (fun t' => t' = (t1.setReg .nextPC (BitVec.addInt pc 2)).setGpr rd wval)
    (Hsp.sptDisp _ Hct_a) Hfetch (Hdec _ Hct_1) (Hsp.sptLpad _ Hct_1)
    (Hsp.sptZca _ Hct_1) HPC_1 (Hexp _) Hexec
  have Hmi1 : t1.regs .minstret_increment = b := by
    rw [tlbFrameLookup _ _ _ Hfr (by decide)]
    simp only [ExecSt.setReg_regs, RegFile.set_same]
  refine EvARiscvStep img tick t (fun t' => Good ctrlOk rs pc rd wval t'.regs) _ ?_ ?_
  · have HT := EvATryStepActive img t b (zero_extend (m := 32) h)
      (fun t' => t' = (t1.setReg .nextPC (BitVec.addInt pc 2)).setGpr rd wval)
      (fun t' => Good ctrlOk rs pc rd wval t'.regs) Hb (Hsp.sptHart _ Hct_a) Hrun ?_
    · exact EvAMono img _ _ _ _ _ t (fun _ _ h => h) (fun _ _ h => h.2) HT
    · rintro _ rfl
      have Hx := AxSymEngine2.setGprRegsNe (t1.setReg .nextPC (BitVec.addInt pc 2)) rd wval
      refine ⟨?_, ?_, ?_⟩
      · rw [Hx _ (by decide)]
        simp only [ExecSt.setReg_regs]
        rw [RegFile.set_other _ _ _ _ (by decide)]
        exact Hsp.sptHart _ Hct_1
      · rw [Hx _ (by decide)]
        simp only [ExecSt.setReg_regs]
        rw [RegFile.set_other _ _ _ _ (by decide)]
        exact Hmi1
      · have Hct_x := AxSymEngine2.ctrlOkSetGpr ctrlOk Hsp.sptFrame
          (t1.setReg .nextPC (BitVec.addInt pc 2)) rd wval
          (Hsp.sptFrame _ _ _ (Or.inr (Or.inl rfl)) Hct_1)
        refine ⟨?_, ?_, ?_⟩
        · unfold tfinal
          cases b
          · exact Hsp.sptFrame _ _ _ (Or.inl rfl) Hct_x
          · exact Hsp.sptFrame _ _ _ (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
              (Hsp.sptFrame _ _ _ (Or.inl rfl) Hct_x)
        · unfold tfinal
          cases b <;> simp only [ExecSt.setReg_regs, Bool.false_eq_true, ↓reduceIte] <;>
            (try rw [RegFile.set_other _ _ _ _ (by decide)]) <;>
            rw [RegFile.set_same, Hx _ (by decide)] <;>
            simp only [ExecSt.setReg_regs, RegFile.set_same]
        · intro r Hr
          have e : uxaXget (tfinal b ((t1.setReg .nextPC
              (BitVec.addInt pc 2)).setGpr rd wval)).regs r =
              ((t1.setReg .nextPC (BitVec.addInt pc 2)).setGpr rd wval).gpr r := by
            unfold tfinal ExecSt.gpr
            cases b <;> simp only [ExecSt.setReg_regs, Bool.false_eq_true, ↓reduceIte] <;>
              (try rw [AxSymEngine2.uxaXgetSetNe _ _ _ (by decide)]) <;>
              rw [AxSymEngine2.uxaXgetSetNe _ _ _ (by decide)]
          rw [e]
          by_cases E : r = rd
          · subst E
            simp only [if_true]
            exact AxFetch3c.gprSetGprSame _ r wval Hrd
          · simp only [E, if_false]
            rw [AxFetch3c.gprSetGprNe _ rd r wval E]
            exact Hgag r Hr
  · intro t' HG
    cases tick with
    | false => exact HG
    | true =>
      refine EvAMono img _ _ _ _ _ t' (fun _ _ h => h) ?_ (Hsp.sptTick t' HG.1)
      rintro _ t'' ⟨Hc, Hk1, Hk2⟩
      obtain ⟨-, HG2, HG3⟩ := HG
      exact ⟨Hc, Hk1.trans HG2, fun r Hr => (Hk2 r).trans (HG3 r Hr)⟩

end certT

/-! # 3. X over `SpineOkT`, and the real leaves -/

section xproofT
variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [AxirisG GF] [Axpol]
variable (img : Image) (i : Agent) (cpu : CPU)
variable (ctrlOk : RegFile → Prop) (textAt : BitVec 64 → BitVec 16 → Prop)
variable (Hsp : SpineOkT img ctrlOk textAt)
variable (Htext : ∀ GD, rvwmoCatConsistent GD →
  AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜textFixed GD i img⌝)
variable (Hflow : ∀ GD ls k, rvwmoCatConsistent GD →
  (∃ lb aq base n vs, (AxOpsem.grow GD i)[k]? = some lb ∧ aident lb = .IRead aq base n ∧
     imgBytes img base n = some vs) →
  AxirisG.gconstInterp (GF := GF) GD ∗ AxirisG.localInterp GD i k ls ⊢ fetchFlow GD i k)

include Hsp Htext Hflow in
theorem XGprWriteHoldsT : XGprWrite (GF := GF) i cpu ctrlOk (textOkD img ctrlOk textAt) := by
  unfold XGprWrite
  intro s rs k pc is_rvc ins rd wval HRet Hctrl HPC Htx Hrd Hcert
  have e : is_rvc = true := Htx.1
  subst e
  iintro C
  iapply (wpdInstrOfEvA img i Φ0 cpu (postLiftingΦ0 i) Htext Hflow
    (fun _ t' => Good ctrlOk rs pc rd wval t'.regs) rs k s HRet
    (spineCertT img ctrlOk textAt Hsp rs pc ins rd wval Hctrl HPC Htx Hrd
      (fun s_pc h1 h2 => Hcert s_pc h1 h2)))
  iintro %t' %rs' %ib' %k' %HG %Hag
  obtain ⟨Hc, Hpc, Hg⟩ := HG
  have HRet' : RetX cpu rs' k' ⟨.PHart cpu (.pure ()) rs' none ib', k'⟩ :=
    ⟨ib', rfl, rfl, rfl, rfl, rfl, regsAgreeRefl _ _⟩
  have Hc' : ctrlOk rs' := Hsp.sptSeip _ _ Hc Hag
  have Hpc' : rs' .PC = pc + instrLen true :=
    (Hag .PC (AxSymEngine2.notPin _ (by decide) (by decide))).trans Hpc
  have Hg' : ∀ r : BitVec 5, r.toNat ≠ 0 →
      uxaXget rs' r = if r = rd then wval else uxaXget rs r :=
    fun r Hr => (AxSymEngine2.uxaXgetAgree _ _ Hag r).trans (Hg r Hr)
  iapply C $$ %_ %rs' %k' %HRet' %Hc' %Hpc' %Hg'

variable [GhostVarG GF RegMap] [GhostVarG GF (BitVec 64)] (cid : CPU) (γm γp : GName)

include Hsp Htext Hflow in
/-- `AxReuseProbe2.wpCmvD` with its X premise discharged over `SpineOkT`. -/
theorem wpCmvDRealT (pc : BitVec 64) (rd rs2 : BitVec 5)
    (m : RegMap) (n : Nat) (b : Bool) (p : BitVec 64) :
    rd.toNat ≠ 0 →
    MachCSL.rdOk rd →
    ⊢ sieCapD (GF := GF) γm cid m n b p -∗
      pcIsD (GF := GF) γp pc -∗
      instrD (GF := GF) (textOkD img ctrlOk textAt) pc true
        (.RTYPE (.Regidx rs2, zreg, .Regidx rd, .ADD)) -∗
      wpNext b p cid (fun cpu' => iprop(
        sieCapD γm cpu' (m.set rd (0#64 + rget cid m rs2)) n b p -∗
        pcIsD γp (pc + 2#64) -∗
        goalD i cid cpu γm γp ctrlOk)) -∗
      goalD i cid cpu γm γp ctrlOk :=
  wpCmvD i cid cpu γm γp ctrlOk (textOkD img ctrlOk textAt)
    (XGprWriteHoldsT img i cpu ctrlOk textAt Hsp Htext Hflow) pc rd rs2 m n b p

include Hsp Htext Hflow in
/-- `AxReuseProbe2.wpCaddiwD` with its X premise discharged over `SpineOkT`. -/
theorem wpCaddiwDRealT (pc : BitVec 64) (rd : BitVec 5) (imm : BitVec 6)
    (m : RegMap) (n : Nat) (b : Bool) (p : BitVec 64) :
    rd.toNat ≠ 0 →
    MachCSL.rdOk rd →
    ⊢ sieCapD (GF := GF) γm cid m n b p -∗
      pcIsD (GF := GF) γp pc -∗
      instrD (GF := GF) (textOkD img ctrlOk textAt) pc true
        (.ADDIW (sign_extend (m := 12) imm, .Regidx rd, .Regidx rd)) -∗
      wpNext b p cid (fun cpu' => iprop(
        sieCapD γm cpu' (m.set rd (sign_extend (m := 64) (Sail.BitVec.extractLsb
          (rget cid m rd + sign_extend (m := 64) (sign_extend (m := 12) imm)) 31 0))) n b p -∗
        pcIsD γp (pc + 2#64) -∗
        goalD i cid cpu γm γp ctrlOk)) -∗
      goalD i cid cpu γm γp ctrlOk :=
  wpCaddiwD i cid cpu γm γp ctrlOk (textOkD img ctrlOk textAt)
    (XGprWriteHoldsT img i cpu ctrlOk textAt Hsp Htext Hflow) pc rd imm m n b p

end xproofT

end Weak
