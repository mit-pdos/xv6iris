/-
Weak: **the positional engine for instructions whose written value depends on MSTATUS** (the two
sstatus CSR reads of `push_off` / `pop_off`), and their leaf at the joint instance Ixv6.

Rocq: `iris/AxSpinPOm.v` @ xxvzwolszwmp.

## The Rocq header, in substance

WHY.  `CertB` (and `AxSymCtl2`'s `CertC`) quantify over every regime state `tpc` that agrees with
the boundary registers `rs` on the GPRs (and the TLB) only, and fix the written GPR value `ow` up
front — so a value read from mstatus (`sstatusRead (tpc.regs .mstatus)`) is not expressible:
`ctrlOkSW` pins SIE = 0 and a few mstatus fields, not mstatus.  In `AxSpinE.spineCertB` the
certificate is applied at `tpc = rs` modulo the pins / `minstret_increment` / `nextPC`, so mstatus
DOES agree; `CertBm` adds that agreement as a hypothesis, and `spineCertBm` / `XBkm` / `XxRegm`
are `AxSpinE.spineCertB` / `XBk` / `XxReg` replayed over it (same scripts, one extra fact).
§3 the `CertBm` facts of `csrrci a5,sstatus,2` (`q0a`) and `csrr a5,sstatus` (`p0c`):
   a5 := `sstatusRead (rs .mstatus)`, nothing else changes, `e = 0`.

## Deviations from Rocq

1. O2 STAGE C COUNT SHIFT (`AxSpinE` deviation 1, `AxSpinE4` deviation 1, `AxSpinE6`
   deviation 3): the instruction's fetch consumes NO row item.
   * `spineCertBm` starts at `BFin (e + b)` (Rocq `BFin (e + b + 1)`);
   * `XBkm`: continuation at `k + e` (Rocq `k + e + 1`); the premise `k + e + 1 ≤ L` becomes the
     two premises `k < L` and `k + e ≤ L` (as `XBk`);
   * `XxRegm` (`e = 0`): continuation at `k` (Rocq `k + 1`); premise `k < LEN` (Rocq
     `k + 1 ≤ LEN`).
2. `XBkm` / `XxRegm` drop Rocq's section premise `Hntext` (`XBk` does not take it, `AxSpinE4`
   deviation 1 / `AxCert2` deviation 1).
3. THE PINS: `regs_agree seip_reg` ↦ `regsAgree AxRunClose.pinReg` (the mstatus agreement is the
   pin-agreement at `.mstatus`, a non-pin register).  The Ltac `lk` is replaced by
   `RegFile.set_*` rewrites (as `AxSpinE` deviation 4).
4. SECTIONS / INSTANCES (as `AxSpinE4` deviation 3 and `AxSpinE6` deviation 2): section variables
   are explicit arguments; `CertBm` takes `σi T satp0 dok kind` first; `XBkm` takes `XBk`'s
   section arguments (`σi T satp0 hmode hasid hppn i cpu G HG L HL HGex Φ Hmid Htext Hflow Hloc
   dok kind HnoRmw HnoSplit Out`); `XxRegm` takes `XxReg`'s (`L GT nm HL Hcons σi T satp0 hmode
   hasid hppn i cpu Hfix Ψ HΨmid`).  The local instances `xm_pol` / `xm_G` are inlined as
   `xv6Pol GT` / `AxSpinX2.xG L GT nm`, passed with `@`.  `invGS_gen HasNoLc Σ` ↦
   `[InvGS_gen hlc GF]` (any `hlc`).  `Interface.Ret tt` ↦ `.pure ()`.  Spellings:
   `mword_of_int 15 : mword 5` ↦ `15#5`, `sstatus_read` ↦ `sstatusRead`,
   `register_lookup mstatus rs` ↦ `rs .mstatus`.
5. The `Print Assumptions` lines are not ported (the lint's axiom check covers them).

**Rocq → Lean name map.**  `CertBm` `CertBm`, `spine_certBm` `spineCertBm`, `CertBm_q0a`
`CertBmQ0a`, `CertBm_p0c` `CertBmP0c`, `XBkm` `XBkm`, `HL0m` `HL0m`, `HGex0m` `HGex0m`, `Hmid0m`
`Hmid0m`, `Xx_regm` `XxRegm` (none in the duplicated-name table; no Lean-only declarations).

**Dropped:** nothing (Rocq 9 definitions/lemmas + 1 Ltac; Lean 9).
**Not ported:** the Ltac `lk` (deviation 3).
-/
import Weak.AxSpinPOc
import Weak.AxSpinE6

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D LeanRV64D.Functions

/-! # 1. The mstatus-indexed certificate and its spine (pure) -/

section spineBm
variable (σi : ExecSt) (T : PTree) (satp0 : BitVec 64)

/-- Rocq `CertBm`: `CertB` + the mstatus of `tpc` is the mstatus of `rs`. -/
def CertBm (dok : Int → Nat → Prop) (kind : Dkind) (rs : RegFile) (pc : BitVec 64)
    (is_rvc : Bool) (ins : instruction) (e : Nat) (ot : Option (BitVec 64))
    (ow : Cdata → Option (BitVec 5 × BitVec 64)) (d0 : Cdata) (r0 : Bool)
    (PX : Cdata → Bool → Prop) : Prop :=
  ∀ tpc : ExecSt, ctrlOkSW T satp0 tpc.regs → tpc.regs .PC = pc →
    tpc.regs .nextPC = BitVec.addInt pc (incr is_rvc) →
    gprAgree tpc.regs rs → tpc.regs .tlb = rs .tlb → tpc.regs .mstatus = rs .mstatus → ∀ b,
    AxCert.Cert (imgS σi) dok kind (fun _ _ _ => False)
      (fun s x t' => x = RETIRE_SUCCESS ∧ ∃ d r, s = ⟨d, .BFin b, r⟩ ∧ PX d r ∧
        t' = wrOpt (ow d) (npcOpt ot tpc))
      ⟨d0, .BFin (e + b), r0⟩ (execute ins) tpc

/-- Rocq `spine_certBm`: `AxSpinE.spineCertB` over `CertBm` (deviation 1: `BFin (e + b)`,
Rocq `e + b + 1`). -/
theorem spineCertBm (hmode : _get_Satp64_Mode (Mk_Satp64 satp0) = 8#4)
    (hasid : zero_extend (m := 16) (satp_to_asid satp0) = 0#16)
    (hppn : BitVec.setWidth 44 (satp_to_ppn satp0) = T.base)
    (dok : Int → Nat → Prop) (kind : Dkind)
    (rs : RegFile) (pc : BitVec 64) (is_rvc : Bool) (ins : instruction) (e : Nat)
    (ot : Option (BitVec 64)) (ow : Cdata → Option (BitVec 5 × BitVec 64)) (d0 : Cdata) (r0 : Bool)
    (PX : Cdata → Bool → Prop) :
    ctrlOkSW T satp0 rs → rs .PC = pc → hitW rs pc → textOkB σi T satp0 pc is_rvc ins →
    (∀ d r, PX d r → owOk (ow d)) → CertBm σi T satp0 dok kind rs pc is_rvc ins e ot ow d0 r0 PX →
    ∀ (tick : Bool) (t : ExecSt), regsAgree AxRunClose.pinReg t.regs rs → ∀ b,
      AxCert.Cert (imgS σi) dok kind (fun _ _ _ => False)
        (fun s _ t' => ∃ d r, s = ⟨d, .BFin b, r⟩ ∧ PX d r ∧
          GoodB T satp0 rs pc is_rvc ot (ow d) t'.regs)
        ⟨d0, .BFin (e + b), r0⟩ (riscvStep tick) t := by
  intro Hct HPC Hhit Htx How Hcert tick t Hag b
  have Hsp := SpineOkTSW σi T satp0 hmode hasid hppn
  have Hct_t : ctrlOkSW T satp0 t.regs := Hsp.sptSeip _ _ Hct Hag
  have HPC_t : t.regs .PC = pc := by
    rw [Hag .PC (AxSymEngine2.notPin _ (by decide) (by decide))]; exact HPC
  have Htlb_t : t.regs .tlb = rs .tlb := Hag .tlb (AxSymEngine2.notPin _ (by decide) (by decide))
  have Hms_t : t.regs .mstatus = rs .mstatus :=
    Hag .mstatus (AxSymEngine2.notPin _ (by decide) (by decide))
  obtain ⟨bb, Hb⟩ := Hsp.sptInc t Hct_t
  have Hct_a : ctrlOkSW T satp0 (t.setReg .minstret_increment bb).regs :=
    Hsp.sptFrame _ _ _ (Or.inr (Or.inr (Or.inl rfl))) Hct_t
  have HPC_a : (t.setReg .minstret_increment bb).regs .PC = pc := by
    rw [ExecSt.setReg_regs, RegFile.set_other _ _ _ _ (by decide)]; exact HPC_t
  have Htlb_a : (t.setReg .minstret_increment bb).regs .tlb = rs .tlb := by
    rw [ExecSt.setReg_regs, RegFile.set_other _ _ _ _ (by decide)]; exact Htlb_t
  have Hms_a : (t.setReg .minstret_increment bb).regs .mstatus = rs .mstatus := by
    rw [ExecSt.setReg_regs, RegFile.set_other _ _ _ _ (by decide)]; exact Hms_t
  have Hhit_a : hitW (t.setReg .minstret_increment bb).regs pc := hitWAgree _ _ _ Htlb_a Hhit
  have Hgag : gprAgree
      ((t.setReg .minstret_increment bb).setReg .nextPC (BitVec.addInt pc (incr is_rvc))).regs rs := by
    intro r _
    simp only [ExecSt.setReg_regs]
    rw [AxSymEngine2.uxaXgetSetNe _ _ _ (by decide), AxSymEngine2.uxaXgetSetNe _ _ _ (by decide)]
    exact AxSymEngine2.uxaXgetAgree _ _ Hag r
  have Hct_pc : ctrlOkSW T satp0
      ((t.setReg .minstret_increment bb).setReg .nextPC (BitVec.addInt pc (incr is_rvc))).regs :=
    Hsp.sptFrame _ _ _ (Or.inr (Or.inl rfl)) Hct_a
  have HPC_pc : ((t.setReg .minstret_increment bb).setReg .nextPC
      (BitVec.addInt pc (incr is_rvc))).regs .PC = pc := by
    rw [ExecSt.setReg_regs, RegFile.set_other _ _ _ _ (by decide)]; exact HPC_a
  have Hnpc_pc : ((t.setReg .minstret_increment bb).setReg .nextPC
      (BitVec.addInt pc (incr is_rvc))).regs .nextPC = BitVec.addInt pc (incr is_rvc) := by
    simp only [ExecSt.setReg_regs, RegFile.set_same]
  have Htlb_pc : ((t.setReg .minstret_increment bb).setReg .nextPC
      (BitVec.addInt pc (incr is_rvc))).regs .tlb = rs .tlb := by
    rw [ExecSt.setReg_regs, RegFile.set_other _ _ _ _ (by decide)]; exact Htlb_a
  have Hms_pc : ((t.setReg .minstret_increment bb).setReg .nextPC
      (BitVec.addInt pc (incr is_rvc))).regs .mstatus = rs .mstatus := by
    rw [ExecSt.setReg_regs, RegFile.set_other _ _ _ _ (by decide)]; exact Hms_a
  have Hexec := Hcert _ Hct_pc HPC_pc Hnpc_pc Hgag Htlb_pc Hms_pc b
  have Hrun : ∃ bits, AxCert.Cert (imgS σi) dok kind (fun _ _ _ => False)
      (fun s x t' => x = .Step_Execute (RETIRE_SUCCESS, bits) ∧
        ∃ d r, s = ⟨d, .BFin b, r⟩ ∧ PX d r ∧ t' = wrOpt (ow d) (npcOpt ot
          ((t.setReg .minstret_increment bb).setReg .nextPC (BitVec.addInt pc (incr is_rvc)))))
      ⟨d0, .BFin (e + b), r0⟩ (run_hart_active 0) (t.setReg .minstret_increment bb) := by
    cases is_rvc with
    | true =>
      rw [textOkB, if_pos rfl] at Htx
      obtain ⟨h, i0, Hat, Hdec, Hden, Hexp, Hexn⟩ := Htx
      exact ⟨zero_extend (m := 32) h,
        CertHartActiveRvcB (imgS σi) dok kind _ h i0 ins pc d0 r0 (e + b) _
          (Hsp.sptDisp _ Hct_a)
          (fetchHitS σi T satp0 hmode hasid hppn _ pc h Hct_a.1 HPC_a Hat Hhit_a)
          (Hdec _ Hct_a) Hden (Hsp.sptLpad _ Hct_a) (Hsp.sptZca _ Hct_a) HPC_a (Hexp _) Hexn
          Hexec⟩
    | false =>
      rw [textOkB, if_neg Bool.false_ne_true] at Htx
      obtain ⟨w, Hat, Hsf, Hdec, Hden⟩ := Htx
      exact ⟨zero_extend (m := 32) w,
        CertHartActiveBaseB (imgS σi) dok kind _ w ins pc d0 r0 (e + b) _ Hsf
          (Hsp.sptDisp _ Hct_a)
          (fetch4HitS σi T satp0 hmode hasid hppn _ pc w Hct_a.1 HPC_a Hat Hhit_a)
          (Hdec _ Hct_a) Hden (Hsp.sptLpad _ Hct_a) HPC_a Hexec⟩
  obtain ⟨bits, Hrun⟩ := Hrun
  refine CertRiscvStep (imgS σi) dok kind tick ⟨d0, .BFin (e + b), r0⟩ t
    (fun s t' => ∃ d r, s = ⟨d, .BFin b, r⟩ ∧ PX d r ∧ GoodB T satp0 rs pc is_rvc ot (ow d) t'.regs)
    _ ?_ ?_
  · have HT := CertTryStepActiveB (imgS σi) dok kind t bb bits d0 r0 (e + b) _
      (fun s t' => ∃ d r, s = ⟨d, .BFin b, r⟩ ∧ PX d r ∧ GoodB T satp0 rs pc is_rvc ot (ow d) t'.regs)
      Hb (Hsp.sptHart _ Hct_a) Hrun ?_
    · exact CertMono (imgS σi) dok kind _ _ _ _ _ _ t (fun _ _ _ h => h) (fun _ _ _ h => h.2) HT
    · rintro s _ ⟨d, r, rfl, HP, rfl⟩
      have Hct_x := wrNpcCtrl (imgS σi) (ctrlOkSW T satp0) (textAtS σi T) Hsp (ow d) ot _ Hct_pc
      have How' := How d r HP
      refine ⟨?_, ?_, d, r, rfl, HP, ⟨?_, ?_, ?_⟩, ?_⟩
      · rw [wrNpcOther _ _ _ _ (by decide) (by decide)]
        simp only [ExecSt.setReg_regs]
        rw [RegFile.set_other _ _ _ _ (by decide)]
        exact Hsp.sptHart _ Hct_a
      · rw [wrNpcOther _ _ _ _ (by decide) (by decide)]
        simp only [ExecSt.setReg_regs]
        rw [RegFile.set_other _ _ _ _ (by decide), RegFile.set_same]
      · unfold tfinal
        cases bb
        · exact Hsp.sptFrame _ _ _ (Or.inl rfl) Hct_x
        · exact Hsp.sptFrame _ _ _ (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
            (Hsp.sptFrame _ _ _ (Or.inl rfl) Hct_x)
      · rw [tfinalPC, wrNpcNextPC]
        cases ot with
        | none => exact Hnpc_pc
        | some tg => rfl
      · intro r1 Hr
        rw [tfinalGpr, wrNpcGpr _ _ _ _ Hr How']
        exact gprPostAgree _ _ _ _ Hgag Hr
      · have Hx : (wrOpt (ow d) (npcOpt ot ((t.setReg .minstret_increment bb).setReg .nextPC
            (BitVec.addInt pc (incr is_rvc))))).regs .tlb = rs .tlb := by
          rw [wrNpcOther _ _ _ _ (by decide) (by decide)]; exact Htlb_pc
        unfold tfinal
        cases bb
        · simp only [ExecSt.setReg_regs, Bool.false_eq_true, ↓reduceIte]
          rw [RegFile.set_other _ _ _ _ (by decide)]
          exact Hx
        · simp only [ExecSt.setReg_regs, ↓reduceIte]
          rw [RegFile.set_other _ _ _ _ (by decide), RegFile.set_other _ _ _ _ (by decide)]
          exact Hx
  · rintro s' t' ⟨d, r, rfl, HP, HG⟩
    cases tick with
    | false => exact ⟨d, r, rfl, HP, HG⟩
    | true =>
      refine CertMono (imgS σi) dok kind _ _ _ _ _ _ t' (fun _ _ _ h => h) ?_
        (CertNrd (imgS σi) dok kind _ _ d b r t' (sptTickFrame (imgS σi) t') nrdTickClock)
      rintro _ _ t'' ⟨rfl, Hf⟩
      obtain ⟨⟨Hc, HG2, HG3⟩, Htl⟩ := HG
      obtain ⟨Hk1, Hk2⟩ := tickFrameKeep t' t'' Hf
      refine ⟨d, r, rfl, HP, ⟨tickFrameCtrlSW T satp0 t' t'' Hf Hc, Hk1.trans HG2,
        fun r1 Hr => (Hk2 r1).trans (HG3 r1 Hr)⟩, ?_⟩
      rw [Hf .tlb (by decide) (by decide) (by decide)]
      exact Htl

/-- Rocq `CertBm_q0a`: `csrrci a5,sstatus,2` writes a5 := the S-view of the boundary's mstatus. -/
theorem CertBmQ0a (dok : Int → Nat → Prop) (kind : Dkind) (rs : RegFile) (pc : BitVec 64)
    (d0 : Cdata) (r0 : Bool) :
    CertBm σi T satp0 dok kind rs pc false q0a 0 none
      (fun _ => some (15#5, sstatusRead (rs .mstatus))) d0 r0 (fun d r => d = d0 ∧ r = r0) := by
  intro tpc Hct _ _ _ _ Hms b
  have HE := EvAOfRfF (imgS σi) _ rfFQ0a tpc _ _ (execQ0a T satp0 tpc Hct.1)
  rw [Nat.zero_add]
  refine CertMono (imgS σi) dok kind _ _ _ _ _ _ tpc (fun _ _ _ h => h) ?_
    (CertNrd (imgS σi) dok kind _ _ d0 b r0 tpc HE (nrdOfRfF _ rfFQ0a))
  rintro s x t' ⟨rfl, rfl, rfl⟩
  refine ⟨rfl, d0, r0, rfl, ⟨rfl, rfl⟩, ?_⟩
  rw [Hms]
  rfl

/-- Rocq `CertBm_p0c`: `csrr a5,sstatus` writes a5 := the S-view of the boundary's mstatus. -/
theorem CertBmP0c (dok : Int → Nat → Prop) (kind : Dkind) (rs : RegFile) (pc : BitVec 64)
    (d0 : Cdata) (r0 : Bool) :
    CertBm σi T satp0 dok kind rs pc false p0c 0 none
      (fun _ => some (15#5, sstatusRead (rs .mstatus))) d0 r0 (fun d r => d = d0 ∧ r = r0) := by
  intro tpc Hct _ _ _ _ Hms b
  have HE := EvAOfRfF (imgS σi) _ rfFP0c tpc _ _ (execP0c T satp0 tpc Hct.1)
  rw [Nat.zero_add]
  refine CertMono (imgS σi) dok kind _ _ _ _ _ _ tpc (fun _ _ _ h => h) ?_
    (CertNrd (imgS σi) dok kind _ _ d0 b r0 tpc HE (nrdOfRfF _ rfFP0c))
  rintro s x t' ⟨rfl, rfl, rfl⟩
  refine ⟨rfl, d0, r0, rfl, ⟨rfl, rfl⟩, ?_⟩
  rw [Hms]
  rfl

end spineBm

/-! # 2. `XBk` over `CertBm` -/

section xBkm
variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [AxirisG GF] [Axpol]
variable (σi : ExecSt) (T : PTree) (satp0 : BitVec 64)
variable (hmode : _get_Satp64_Mode (Mk_Satp64 satp0) = 8#4)
variable (hasid : zero_extend (m := 16) (satp_to_asid satp0) = 0#16)
variable (hppn : BitVec.setWidth 44 (satp_to_ppn satp0) = T.base)
variable (i : Agent) (cpu : CPU)
variable (G : Gdexec → Prop)
variable (HG : ∀ GD, rvwmoCatConsistent GD → AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜G GD⌝)
variable (L : Nat) (HL : ∀ GD, G GD → (AxOpsem.grow GD i).length = L) (HGex : ∃ GD, G GD)
variable (Φ : Athread → IProp GF)
variable (Hmid : ∀ GD s, G GD → midState s → s.atK = (AxOpsem.grow GD i).length →
  ⊢ postLifting Φ i s)
variable (Htext : ∀ GD, rvwmoCatConsistent GD →
  AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜textFixed GD i (imgS σi)⌝)
variable (Hflow : ∀ GD ls k, rvwmoCatConsistent GD →
  (∃ lb aq base n vs, (AxOpsem.grow GD i)[k]? = some lb ∧ aident lb = .IRead aq base n ∧
     imgBytes (imgS σi) base n = some vs) →
  AxirisG.gconstInterp (GF := GF) GD ∗ AxirisG.localInterp GD i k ls ⊢ fetchFlow GD i k)
variable (Hloc : ∀ GD ls k, rvwmoCatConsistent GD →
  AxirisG.gconstInterp (GF := GF) GD ∗ AxirisG.localInterp GD i k ls ⊢
    |==> ∃ ls', AxirisG.localInterp GD i (k + 1) ls')
variable (dok : Int → Nat → Prop) (kind : Dkind)
variable (HnoRmw : kind = .DKLd → ∀ GD, rvwmoCatConsistent GD →
  AxirisG.gconstInterp (GF := GF) GD ⊢
  ⌜∀ (k : Nat) (lb : Lbl) (aq rl : Bool) (base : Int) (n : Nat),
    (AxOpsem.grow GD i)[k]? = some lb → aident lb = .IRmw aq rl base n → ¬ dok base n⌝)
variable (HnoSplit : kind = .DKRmw → ∀ GD, rvwmoCatConsistent GD →
  AxirisG.gconstInterp (GF := GF) GD ⊢
  ⌜∀ (k : Nat) (lb : Lbl) (aq : Bool) (base : Int) (n : Nat),
    (AxOpsem.grow GD i)[k]? = some lb → aident lb = .IRead aq base n → ¬ dok base n⌝)
variable (Out : Nat → List (BitVec 8) → IProp GF)

include hmode hasid hppn HG HL HGex Hmid Htext Hflow Hloc HnoRmw HnoSplit in
/-- Rocq `XBkm`: `XBk` over `CertBm` (deviation 1: continuation at `k + e`, premises `k < L`,
`k + e ≤ L`; Rocq `k + e + 1`, `k + e + 1 ≤ L`). -/
theorem XBkm (s : Athread) (rs : RegFile) (k : Nat) (pc : BitVec 64) (is_rvc : Bool)
    (ins : instruction) (e : Nat) (ot : Option (BitVec 64))
    (ow : Cdata → Option (BitVec 5 × BitVec 64)) (d0 : Cdata) (r0 : Bool)
    (PX : Cdata → Bool → Prop) :
    RetX cpu rs k s → ctrlOkSW T satp0 rs → rs .PC = pc → hitW rs pc →
    textOkB σi T satp0 pc is_rvc ins → (∀ d r, PX d r → owOk (ow d)) →
    CertBm σi T satp0 dok kind rs pc is_rvc ins e ot ow d0 r0 PX →
    k < L → k + e ≤ L →
    ⊢ CResK dok kind i Out k d0 k -∗
      (∀ d r rs' ib', ⌜PX d r⌝ -∗ ⌜GoodB T satp0 rs pc is_rvc ot (ow d) rs'⌝ -∗
          CResK dok kind i Out k d (k + e) -∗
          wpdM rvwmoCatConsistent .MaybeStuck i ⟨.PHart cpu (.pure ()) rs' none ib', k + e⟩ Φ) -∗
      wpdM rvwmoCatConsistent .MaybeStuck i s Φ := by
  intro HRet Hc HPC Hhit Htx How Hcert Hk Hle
  have Hbp : AxCert2.bpos G i k (Cst.csB ⟨d0, .BFin (e + (L - (k + e))), r0⟩) := by
    intro GD HGD
    rw [HL GD HGD]
    omega
  have Hb : ∀ GD s1, G GD → RetX cpu rs k s1 → s1.atK = (AxOpsem.grow GD i).length →
      ⊢ postLifting Φ i s1 := by
    intro GD s1 HGD HR1 Hat
    exfalso
    obtain ⟨_, _, rfl, -⟩ := retxShape _ _ _ _ HR1
    rw [HL GD HGD] at Hat
    dsimp only at Hat
    omega
  have H := wpdInstrOfCertK (hlc := hlc) (GF := GF) (imgS σi) dok kind i Φ cpu G HG Hmid Htext
    Hflow Hloc HnoRmw HnoSplit Out k
    (fun s' _ t' => ∃ d r, s' = ⟨d, .BFin (L - (k + e)), r⟩ ∧ PX d r ∧
      GoodB T satp0 rs pc is_rvc ot (ow d) t'.regs)
    ⟨d0, .BFin (e + (L - (k + e))), r0⟩ rs s HRet Hbp Hb
    (fun tick t Hag => spineCertBm σi T satp0 hmode hasid hppn dok kind rs pc is_rvc ins e
      ot ow d0 r0 PX Hc HPC Hhit Htx How Hcert tick t Hag (L - (k + e)))
  iintro D C
  iapply H $$ D
  iintro %s' %t' %rs' %ib' %k' %HQ %Hag' %Hbp' D
  obtain ⟨d, r, rfl, HPX, HGB⟩ := HQ
  obtain ⟨GD, HGD⟩ := HGex
  have E : (AxOpsem.grow GD i).length = k' + (L - (k + e)) := Hbp' GD HGD
  rw [HL GD HGD] at E
  obtain rfl : k' = k + e := by omega
  iapply C $$ %d %r %rs' %ib' %HPX %(GoodBAgree σi T satp0 hmode hasid hppn rs pc is_rvc ot (ow d)
    _ rs' HGB Hag') D

end xBkm

/-! # 3. The Ixv6 leaf -/

/-- Rocq `HL0m`. -/
theorem HL0m (GT : GdexecT) (i : Agent) :
    ∀ GD, GD = gtAdGd GT → (AxOpsem.grow GD i).length = (AxOpsem.grow (gtAdGd GT) i).length := by
  intro GD h
  rw [h]

/-- Rocq `HGex0m`. -/
theorem HGex0m (GT : GdexecT) : ∃ GD, GD = gtAdGd GT := ⟨_, rfl⟩

section ixm
variable {hlc : HasLC} {GF : BundledGFunctors.{0,0,0}} [InvGS_gen hlc GF] [AxannotGS GF]
  [AxSpinX.Xv6G GF]
variable (L : Xlay) (GT : GdexecT) (nm : Xv6N)
variable (HL : xlayOk L) (Hcons : rvwmoCatConsistent (gtAdGd GT))
variable (σi : ExecSt) (T : PTree) (satp0 : BitVec 64)
variable (hmode : _get_Satp64_Mode (Mk_Satp64 satp0) = 8#4)
variable (hasid : zero_extend (m := 16) (satp_to_asid satp0) = 0#16)
variable (hppn : BitVec.setWidth 44 (satp_to_ppn satp0) = T.base)
variable (i : Agent) (cpu : CPU)
variable (Hfix : textFixed (gtAdGd GT) i (imgS σi))
variable (Ψ : Athread → IProp GF)
variable (HΨmid : ∀ s, midState s → s.atK = (AxOpsem.grow (gtAdGd GT) i).length →
  ⊢ @postLifting GF (AxSpinX2.xG L GT nm) Ψ i s)

include HΨmid in
/-- Rocq `Hmid0m`. -/
theorem Hmid0m :
    ∀ GD s, GD = gtAdGd GT → midState s → s.atK = (AxOpsem.grow GD i).length →
      ⊢ @postLifting GF (AxSpinX2.xG L GT nm) Ψ i s := by
  rintro GD s rfl Hm Hk
  exact HΨmid s Hm Hk

include HL Hcons hmode hasid hppn Hfix HΨmid in
/-- Rocq `Xx_regm`: a register-only instruction whose written value may read mstatus
(deviation 1: continuation at `k`, premise `k < LEN`; Rocq `k + 1`, `k + 1 ≤ LEN`). -/
theorem XxRegm (s : Athread) (rs : RegFile) (k : Nat) (pc : BitVec 64) (is_rvc : Bool)
    (ins : instruction) (ot : Option (BitVec 64)) (ow : Option (BitVec 5 × BitVec 64)) :
    RetX cpu rs k s → ctrlOkSW T satp0 rs → rs .PC = pc → hitW rs pc →
    textOkB σi T satp0 pc is_rvc ins → owOk ow →
    CertBm σi T satp0 dok0 .DKSt rs pc is_rvc ins 0 ot (fun _ => ow) .CPend false
      (fun d r => d = .CPend ∧ r = false) →
    k < (AxOpsem.grow (gtAdGd GT) i).length →
    ⊢ (∀ (rs' : RegFile) (ib' : Ibch), ⌜GoodB T satp0 rs pc is_rvc ot ow rs'⌝ -∗
        @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
          ⟨.PHart cpu (.pure ()) rs' none ib', k⟩ Ψ) -∗
      @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i s Ψ := by
  intro HRet Hc HPC Hhit Htx How Hcert Hle
  have H := @XBkm hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) σi T satp0 hmode hasid hppn i cpu
    (fun GD => GD = gtAdGd GT) (HGX L GT nm) (AxOpsem.grow (gtAdGd GT) i).length (HL0m GT i)
    (HGex0m GT) Ψ (Hmid0m L GT nm i Ψ HΨmid) (HtextX L GT nm (imgS σi) i Hfix)
    (HflowX L GT nm HL Hcons (imgS σi) i) (HlocX L GT nm i)
    dok0 .DKSt (by intro h; cases h) (by intro h; cases h) (fun _ _ => iprop(True))
    s rs k pc is_rvc ins 0 ot (fun _ => ow) .CPend false (fun d r => d = .CPend ∧ r = false)
    HRet Hc HPC Hhit Htx (fun _ _ _ => How) Hcert Hle (by omega)
  iintro C
  iapply H $$ [] [C]
  · simp only [CResK, CFkM]
    letI : AxirisG GF := AxSpinX2.xG L GT nm
    letI : Axpol := xv6Pol GT
    iapply (FstDok0M (GF := GF) rvwmoCatConsistent i)
  · iintro %d %r %rs' %ib' %_ %HGB -
    iapply C $$ %rs' %ib' %HGB

end ixm

end Weak
