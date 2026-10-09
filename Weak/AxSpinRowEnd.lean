/-
Weak: **PHASE 5 POSITIONAL ENGINE: the ROW-END leaves** — a register-only instruction
AT the row end keeps the post (`AxSpinRowEnd.XxRegEnd`), a store AT the row end is stuck
(`AxSpinRowEnd.XxStEnd`).  Theorem 2 / P4, step 1 (`notes/weak-lb-thm2-p4.md` §A.3–A.5, §C F4).

Lean-only (no Rocq source).

## What this file proves

WHY.  `XxReg` / `XxSt` (AxSpinE6) need `k < LEN` resp. `k + 1 ≤ LEN`: `XBk` (AxSpinE4) refutes the
boundary's row-end obligation (`wpdRetNode3M`'s `Hb`) by `omega`.  At `k = LEN` that obligation
is REAL — the boundary state is a row-end state, so `wpdMPreStepDef` (d) owes the post there —
and it is pure in `wpdRetNode3M`, whereas a post that talks about owned annotations
(`postLifting` hands it the annotation map) can only be proved from a RESOURCE.

§1 `AxSpinRowEnd.wpdRetNode3MR` — `wpdRetNode3M` with the row-end obligation from a resource `R`
(`R ⊢ postLifting Φ i s1`), kept for the continuation: `R -∗ (R -∗ cont) -∗ WPd`.  Same proof
(`wpdOfClosedRunGM` takes the post clause as a resource under `∧` with the continuation).
§2 `AxSpinRowEnd.CertBAt` — `CertB` (AxSpinE) at ONE budget `b` (CertB quantifies `∀ b`);
`AxSpinRowEnd.certBAtOf` (CertB ⇒ every `CertBAt`); `AxSpinRowEnd.spineCertBAt` — `AxSpinE.spineCertB`
from a `CertBAt` (same proof; the spine uses its certificate at one budget only).
§3 THE STUCK STORE CHAIN at `BFin 0`, ending in the write-end arm `AxCert.Cert.cWrEnd` (AxCert
deviation 11): `xbWriteRamEnd`, `xbCheckedMemWriteEnd`, `xbMemWriteValueEnd`,
`xbVmemWriteAddrEnd`, `xbVmemWriteEnd`, `xbExecuteStoreEnd` (copies of AxSpinE2's `XBWriteRam` …
`XBExecuteSTORE` with the data write replaced by `cWrEnd`: ANY post, no `dok`, no kind, nothing
after the write), and `certBStoreEnd` — the store leaf's `CertBAt` at `e = 0`, `b = 0`, final
predicate `False` (as `CertBStoreS`, AxSpinE2).
§4 `AxSpinRowEnd.XBkR` — `XBk` (AxSpinE4) over a `CertBAt` at the exact remaining budget, with the
boundary obligation from a resource `R` instead of `k < L`.
§5 THE LEAVES at Ixv6 (AxSpinE6's section): `XxRegEnd` (`XxReg` at `k = LEN`: continuation at
`k`, `GoodB`), `XxStEnd` (a plain store at `k = LEN`: no continuation at all — the write node
is stuck, `AxCert2.wpdStuckWriteM`, its post `HΨmid`'s since the node is mid-instruction).
In both, the boundary's post comes from `R` (`HRb : ∀ s1, RetX cpu rs k s1 → R ⊢ postLifting Ψ i s1`)
and every mid-instruction row-end state is `HΨmid`'s, as in AxSpinE6.

## Pins / honesty

* No new pins and no new premises beyond AxSpinE6's section (`Hfix`, `HΨmid`, the satp facts).
* `XxStEnd` takes no `priv` / `dok` slot premise (there is no data event); it keeps the TLB-hit
  and `dataAtS` premises because the instruction's translation runs before the write node.
* The write-end chain (§3) is a COPY of AxSpinE2's write chain up to the write node (same
  stepping lemmas, same order); after `cWrEnd` nothing is certified.

Reused: `wpdOfClosedRunGM` (AxEpiChainSdLd), `retxShape`/`retPstepInv`/`astepProgRetShape`
(AxSymEngine3), `wpdOfCertK` (AxSpinE4), `AxSpinE.spineCertB`'s ingredients (AxSpinE),
`XBMemWriteEa` (AxSpinE2), `AxCert2.wpdStuckWriteM` (via `wpdOfCertK`'s `cWrEnd` arm),
`CertBOfCertC`, `GoodBAgree`, `HGX`/`HtextX`/`HflowX`/`HlocX`, `FstDok0M`, `AxSpinE6.Hmid0`.
Names: all Lean-only and file-qualified `AxSpinRowEnd.*`.  (The design note calls this file
`AxSpinE9`; that name is taken by the merged `frb` checker, so it is `AxSpinRowEnd`.)
-/
import Weak.AxSpinE6

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open Sail.ArchSem (FreeM)
open LeanRV64D LeanRV64D.Functions

/-! # 1. The instruction boundary with a resource-borne row-end obligation -/

section retR
variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [AxirisG GF] [Axpol]

/-- `wpdRetNode3M` with the boundary's row-end obligation proved from a resource `R`, which is
handed back to the continuation. -/
theorem AxSpinRowEnd.wpdRetNode3MR (M : Gdexec → Prop) (i : Agent) (Φ : Athread → IProp GF)
    (cpu : CPU) (G : Gdexec → Prop)
    (HG : ∀ GD, M GD → AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜G GD⌝)
    (R : IProp GF) (rs : RegFile) (k : Nat) (s : Athread) (Hs : RetX cpu rs k s)
    (Hb : ∀ GD s1, G GD → RetX cpu rs k s1 → s1.atK = (AxOpsem.grow GD i).length →
      R ⊢ postLifting Φ i s1) :
    ⊢ R -∗ (R -∗ ∀ s2, ⌜RetNext cpu rs k s2⌝ -∗ wpdM M .MaybeStuck i s2 Φ) -∗
      wpdM M .MaybeStuck i s Φ := by
  have Hnord : ∀ GD s1 id K, G GD → RetX cpu rs k s1 → ¬ areadStep (AxOpsem.grow GD i) s1 id K := by
    rintro GD s1 id K - HP ⟨lb, -, -, Hrd, HK⟩
    obtain ⟨rs1, ib1, rfl, -⟩ := retxShape cpu rs k s1 HP
    obtain ⟨l, d, d', Hl, -, Hps, -⟩ := HK (List.replicate (aidentN id) 0) List.length_replicate
    obtain ⟨rfl, -⟩ := retPstepInv _ _ _ _ _ _ _ Hps
    rw [← Hl] at Hrd
    simp [wlRd] at Hrd
  have Hclos : ∀ GD s1 l s2, G GD → RetX cpu rs k s1 →
      AxOpsem.astepProg (AxOpsem.grow GD i) s1 l s2 → WeakAxRealize.fetchPin GD.gdG.gxImg l →
      wlWdata l = none ∧ s2.atK = s1.atK ∧ (RetX cpu rs k s2 ∨ RetNext cpu rs k s2) := by
    rintro GD s1 l s2 - HP Hst -
    obtain ⟨rs1, ib1, rfl, Hag⟩ := retxShape cpu rs k s1 HP
    obtain ⟨d, d', Hps⟩ := astepProgPstep _ _ _ _ Hst
    obtain ⟨tick, rfl⟩ := astepProgRetShape _ cpu rs1 ib1 k l s2 Hst
    obtain ⟨rfl, -⟩ := retPstepInv _ _ _ _ _ _ _ Hps
    exact ⟨rfl, rfl, .inr ⟨tick, rs1, regsAgreeSym _ _ _ Hag, rfl⟩⟩
  have Hwire : ∀ s1 s2, RetX cpu rs k s1 → awire s1 s2 →
      RetX cpu rs k s2 ∨ RetNext cpu rs k s2 := by
    rintro s1 s2 ⟨ib', Hq⟩ Hw
    exact .inl ⟨ib', aeqvTrans _ _ _ (awireAeqv _ _ Hw) Hq⟩
  iintro HR Hcont
  iapply (wpdOfClosedRunGM M i G (RetX cpu rs k) (RetNext cpu rs k) Φ HG Hnord Hclos Hwire) $$
    %s %Hs
  isplit
  · iapply Hcont $$ HR
  · iintro %GD %s1 %HGD %HP %Heq
    ihave Hp := (Hb GD s1 HGD HP Heq) $$ HR
    iexact Hp

end retR

/-! # 2. `CertB` at one budget, and the spine from it -/

section spineAt
variable (σi : ExecSt) (T : PTree) (satp0 : BitVec 64)

/-- `CertB` (AxSpinE) at ONE remaining budget `b`. -/
def AxSpinRowEnd.CertBAt (dok : Int → Nat → Prop) (kind : Dkind) (rs : RegFile) (pc : BitVec 64)
    (is_rvc : Bool) (ins : instruction) (e : Nat) (ot : Option (BitVec 64))
    (ow : Cdata → Option (BitVec 5 × BitVec 64)) (d0 : Cdata) (r0 : Bool)
    (PX : Cdata → Bool → Prop) (b : Nat) : Prop :=
  ∀ tpc : ExecSt, ctrlOkSW T satp0 tpc.regs → tpc.regs .PC = pc →
    tpc.regs .nextPC = BitVec.addInt pc (incr is_rvc) →
    gprAgree tpc.regs rs → tpc.regs .tlb = rs .tlb →
    AxCert.Cert (imgS σi) dok kind (fun _ _ _ => False)
      (fun s x t' => x = RETIRE_SUCCESS ∧ ∃ d r, s = ⟨d, .BFin b, r⟩ ∧ PX d r ∧
        t' = wrOpt (ow d) (npcOpt ot tpc))
      ⟨d0, .BFin (e + b), r0⟩ (execute ins) tpc

theorem AxSpinRowEnd.certBAtOf (dok : Int → Nat → Prop) (kind : Dkind) (rs : RegFile)
    (pc : BitVec 64) (is_rvc : Bool) (ins : instruction) (e : Nat) (ot : Option (BitVec 64))
    (ow : Cdata → Option (BitVec 5 × BitVec 64)) (d0 : Cdata) (r0 : Bool)
    (PX : Cdata → Bool → Prop) :
    CertB σi T satp0 dok kind rs pc is_rvc ins e ot ow d0 r0 PX →
    ∀ b, AxSpinRowEnd.CertBAt σi T satp0 dok kind rs pc is_rvc ins e ot ow d0 r0 PX b :=
  fun H b tpc h1 h2 h3 h4 h5 => H tpc h1 h2 h3 h4 h5 b

/-- `AxSpinE.spineCertB` from a `CertBAt` (same proof). -/
theorem AxSpinRowEnd.spineCertBAt (hmode : _get_Satp64_Mode (Mk_Satp64 satp0) = 8#4)
    (hasid : zero_extend (m := 16) (satp_to_asid satp0) = 0#16)
    (hppn : BitVec.setWidth 44 (satp_to_ppn satp0) = T.base)
    (dok : Int → Nat → Prop) (kind : Dkind)
    (rs : RegFile) (pc : BitVec 64) (is_rvc : Bool) (ins : instruction) (e : Nat)
    (ot : Option (BitVec 64)) (ow : Cdata → Option (BitVec 5 × BitVec 64)) (d0 : Cdata) (r0 : Bool)
    (PX : Cdata → Bool → Prop) (b : Nat) :
    ctrlOkSW T satp0 rs → rs .PC = pc → hitW rs pc → textOkB σi T satp0 pc is_rvc ins →
    (∀ d r, PX d r → owOk (ow d)) →
    AxSpinRowEnd.CertBAt σi T satp0 dok kind rs pc is_rvc ins e ot ow d0 r0 PX b →
    ∀ (tick : Bool) (t : ExecSt), regsAgree AxRunClose.pinReg t.regs rs →
      AxCert.Cert (imgS σi) dok kind (fun _ _ _ => False)
        (fun s _ t' => ∃ d r, s = ⟨d, .BFin b, r⟩ ∧ PX d r ∧
          GoodB T satp0 rs pc is_rvc ot (ow d) t'.regs)
        ⟨d0, .BFin (e + b), r0⟩ (riscvStep tick) t := by
  intro Hct HPC Hhit Htx How Hcert tick t Hag
  have Hsp := SpineOkTSW σi T satp0 hmode hasid hppn
  have Hct_t : ctrlOkSW T satp0 t.regs := Hsp.sptSeip _ _ Hct Hag
  have HPC_t : t.regs .PC = pc := by
    rw [Hag .PC (AxSymEngine2.notPin _ (by decide) (by decide))]; exact HPC
  have Htlb_t : t.regs .tlb = rs .tlb := Hag .tlb (AxSymEngine2.notPin _ (by decide) (by decide))
  obtain ⟨bb, Hb⟩ := Hsp.sptInc t Hct_t
  have Hct_a : ctrlOkSW T satp0 (t.setReg .minstret_increment bb).regs :=
    Hsp.sptFrame _ _ _ (Or.inr (Or.inr (Or.inl rfl))) Hct_t
  have HPC_a : (t.setReg .minstret_increment bb).regs .PC = pc := by
    rw [ExecSt.setReg_regs, RegFile.set_other _ _ _ _ (by decide)]; exact HPC_t
  have Htlb_a : (t.setReg .minstret_increment bb).regs .tlb = rs .tlb := by
    rw [ExecSt.setReg_regs, RegFile.set_other _ _ _ _ (by decide)]; exact Htlb_t
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
  have Hexec := Hcert _ Hct_pc HPC_pc Hnpc_pc Hgag Htlb_pc
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

end spineAt

/-! # 3. The stuck store chain at `BFin 0` (ends in `cWrEnd`) -/

section wrEnd
variable (img : Image) (dok : Int → Nat → Prop) (kind : Dkind)

/-- `XBWriteRam` at the row end: the data write is STUCK (`cWrEnd`), any post. -/
theorem AxSpinRowEnd.xbWriteRamEnd (w : Nat) (QE : Cst → Sail.Error exception → ExecSt → Prop)
    (Q : Cst → Bool → ExecSt → Prop) (pa : BitVec 64) (data : BitVec (8 * w)) (d : Cdata)
    (r : Bool) (t : ExecSt) :
    devAddr pa = false →
    AxCert.Cert img dok kind QE Q ⟨d, .BFin 0, r⟩
      (write_ram .Write_plain (.Physaddr pa) w data ()) t := by
  intro hdev
  simp only [write_ram, PreSail.sail_mem_write, PreSail.emit]
  exact .cWrEnd d r w 64 _ _ t hdev rfl

section cmwEnd
variable (σ : ExecSt) (himg : img = imgOf σ) (acc : MemoryAccessType mem_payload)
  (pbmt : page_based_mem_type) (w : Nat) (pa : BitVec 64)
include himg

/-- `XBCheckedMemWrite` at the row end. -/
theorem AxSpinRowEnd.xbCheckedMemWriteEnd (data : BitVec (8 * w))
    (Q : Cst → Result Bool (physaddr × ExceptionType) → ExecSt → Prop) (d : Cdata) (r : Bool)
    (t : ExecSt) :
    execA (check_pma_with_pmp_priority acc pbmt .Supervisor (.Physaddr pa) w false) (tσ σ t)
      = some (.Ok pmaOkAligned, tσ σ t) →
    execA (pmpCheck (.Physaddr pa) w acc .Supervisor) (tσ σ t) = some (none, tσ σ t) →
    execA (within_mmio_writable (.Physaddr pa) w) (tσ σ t) = some (false, tσ σ t) →
    devAddr pa = false →
    AxCert.Cert img dok kind (fun _ _ _ => False) Q ⟨d, .BFin 0, r⟩
      (checked_mem_write (.Physaddr pa) w data acc pbmt .Supervisor () false false false) t := by
  intro hcp hpmp hmm hdev
  unfold checked_mem_write
  apply CertCatchEarlyReturn
  refine AxCert4.cRAssoc ?_
  refine AxSpinE2.cRUse himg hcp (by ax_spin_e2_rfs) ?_
  refine AxCert4.cRPureBind ?_
  refine AxSpinE2.cRUse himg (a := ((1 : Int), (w : Int))) rfl (by ax_spin_e2_rfs) ?_
  simp only [misaligned_order, sys_misaligned_order_decreasing, ↓reduceIte, Bool.false_eq_true,
    Int.reduceSub, Int.toNat_zero, write_kind_of_flags]
  refine AxSpinE2.cRUse himg rfl (by ax_spin_e2_rfs) ?_
  refine AxCert4.cRBind ?_
  refine CertUntilMT1 img dok kind _ _ _ _ _ _ t ?_
  refine AxSpinE2.cRUse himg rfl (by ax_spin_e2_rfs) ?_
  simp only [bits_of_physaddr, Int.cast_ofNat_Int, Int.zero_mul, addIntZero, Int.toNat_natCast]
  refine AxSpinE2.cRUse himg hpmp (by ax_spin_e2_rfs) ?_
  dsimp only
  refine AxCert4.cRAssoc ?_
  refine AxSpinE2.cRUse himg hmm (by ax_spin_e2_rfs) ?_
  simp only [Bool.false_eq_true, ↓reduceIte]
  refine AxCert4.cRAssoc ?_
  refine AxCert4.cFactLift (P := fun _ _ _ => False)
    (AxSpinRowEnd.xbWriteRamEnd img dok kind w _ _ pa _ d r t hdev) ?_
  intro _ _ _ h
  exact h.elim

/-- `XBMemWriteValue` at the row end. -/
theorem AxSpinRowEnd.xbMemWriteValueEnd (data : BitVec (8 * w))
    (Q : Cst → Result Bool (physaddr × ExceptionType) → ExecSt → Prop) (d : Cdata) (r : Bool)
    (t : ExecSt) :
    wrFacts σ acc pbmt w pa t → devAddr pa = false →
    AxCert.Cert img dok kind (fun _ _ _ => False) Q ⟨d, .BFin 0, r⟩
      (mem_write_value (.Physaddr pa) w data acc pbmt false false false) t := by
  rintro ⟨heff, hcp, hpmp, hmm⟩ hdev
  unfold mem_write_value mem_write_value_meta
  ax_cert4_go
  refine AxSpinE2.cFactUse himg heff (by ax_spin_e2_rfs) ?_
  unfold mem_write_value_priv_meta
  ax_cert4_go
  refine AxCert4.cFactQ (AxSpinRowEnd.xbCheckedMemWriteEnd img dok kind σ himg acc pbmt w pa data
    (fun _ _ _ => False) d r t hcp hpmp hmm hdev) ?_
  intro _ _ _ h
  exact h.elim

end cmwEnd

/-- `XBVmemWriteAddr` at the row end. -/
theorem AxSpinRowEnd.xbVmemWriteAddrEnd (σ : ExecSt) (himg : img = imgOf σ) (va pa : BitVec 64)
    (w : Nat) (data : BitVec (8 * w)) (md : SATPMode)
    (Q : Cst → Result Bool ExecutionResult → ExecSt → Prop) (d : Cdata) (r : Bool)
    (t s1 : ExecSt) :
    vmemWidth w →
    is_aligned_vaddr (.Virtaddr va) w = true →
    execA (effectivePrivilege (.Store .Data) (t.regs .mstatus) (t.regs .cur_privilege)) (tσ σ t)
      = some (.Supervisor, tσ σ t) →
    execA (translationMode .Supervisor) (tσ σ t) = some (md, tσ σ t) →
    execA (translateAddr (.Virtaddr va) (.Store .Data)) (tσ σ t)
      = some (.Ok (.Physaddr pa, .PBMT_PMA, ()), s1) →
    cntA (translateAddr (.Virtaddr va) (.Store .Data)) (tσ σ t) = 0 →
    wrFacts σ (.Store .Data) .PBMT_PMA w pa ⟨s1.regs, t.mem, t.dev⟩ → devAddr pa = false →
    AxCert.Cert img dok kind (fun _ _ _ => False) Q ⟨d, .BFin 0, r⟩
      (vmem_write_addr (.Virtaddr va) w data (.Store .Data) false false false) t := by
  intro hw hal heff htm htr htrc hwf hdev
  have hsp := splitOnPageBoundaryAlignedEq va w hw hal
  unfold vmem_write_addr
  simp only [bits_of_virtaddr, hsp, pure_bind, hal, Functions.not, Bool.not_true, Bool.false_eq_true,
    ↓reduceIte]
  apply CertCatchEarlyReturn
  ax_cert4_go
  refine AxSpinE2.cRUse himg rfl (by ax_spin_e2_rfs) ?_
  ax_cert4_go
  refine AxSpinE2.cRUse himg heff (by ax_spin_e2_rfs) ?_
  refine AxSpinE2.cRUse himg htm (by ax_spin_e2_rfs) ?_
  cases md <;>
  · dsimp only [iteNoSplitBare, iteNoSplitSv32, iteNoSplitSv39, iteNoSplitSv48, iteNoSplitSv57,
      Int.toNat_natCast, sys_misaligned_order_decreasing, Bool.false_and]
    refine AxCert4.cRPureBind ?_
    refine AxCert4.cRAssoc ?_
    refine AxSpinE2.cRUseT himg htr htrc ?_
    dsimp only
    refine AxCert4.cRAssoc ?_
    refine AxSpinE2.cRUse himg rfl (by ax_spin_e2_rfs) ?_
    simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte]
    refine AxCert4.cRAssoc ?_
    refine AxCert4.cFactLift (XBMemWriteEa img dok kind σ himg (.Store .Data) .PBMT_PMA w pa
      (fun s' r' t' => s' = ⟨d, .BFin 0, r⟩ ∧ r' = .Ok () ∧
        t' = ⟨s1.regs, t.mem, t.dev⟩) _ _ hwf ⟨rfl, rfl, rfl⟩) ?_
    rintro s' x t' ⟨hs, rfl, rfl⟩
    subst s'
    dsimp only
    refine AxCert4.cRAssoc ?_
    refine AxCert4.cFactLift (AxSpinRowEnd.xbMemWriteValueEnd img dok kind σ himg (.Store .Data)
      .PBMT_PMA w pa _ (fun _ _ _ => False) d r _ hwf hdev) ?_
    intro _ _ _ h
    exact h.elim

/-- `XBVmemWrite` at the row end. -/
theorem AxSpinRowEnd.xbVmemWriteEnd (σ : ExecSt) (himg : img = imgOf σ) (rs1 : BitVec 5)
    (offset va pa : BitVec 64) (w : Nat) (data : BitVec (8 * w)) (md : SATPMode)
    (Q : Cst → Result Bool ExecutionResult → ExecSt → Prop) (d : Cdata) (r : Bool)
    (t s1 : ExecSt) :
    execA (get_transformed_data_addr (.Regidx rs1) offset (.Store .Data) w) (tσ σ t)
      = some (.Ext_DataAddr_OK (.Virtaddr va), tσ σ t) →
    vmemWidth w →
    is_aligned_vaddr (.Virtaddr va) w = true →
    execA (effectivePrivilege (.Store .Data) (t.regs .mstatus) (t.regs .cur_privilege)) (tσ σ t)
      = some (.Supervisor, tσ σ t) →
    execA (translationMode .Supervisor) (tσ σ t) = some (md, tσ σ t) →
    execA (translateAddr (.Virtaddr va) (.Store .Data)) (tσ σ t)
      = some (.Ok (.Physaddr pa, .PBMT_PMA, ()), s1) →
    cntA (translateAddr (.Virtaddr va) (.Store .Data)) (tσ σ t) = 0 →
    wrFacts σ (.Store .Data) .PBMT_PMA w pa ⟨s1.regs, t.mem, t.dev⟩ → devAddr pa = false →
    AxCert.Cert img dok kind (fun _ _ _ => False) Q ⟨d, .BFin 0, r⟩
      (vmem_write (.Regidx rs1) offset w data (.Store .Data) false false false) t := by
  intro hgta hw hal heff htm htr htrc hwf hdev
  unfold vmem_write
  apply CertCatchEarlyReturn
  ax_cert4_go
  refine AxSpinE2.cRUse himg hgta (by ax_spin_e2_rfs) ?_
  dsimp only
  ax_cert4_go
  exact AxSpinE2.cRLiftLast (AxSpinRowEnd.xbVmemWriteAddrEnd img dok kind σ himg va pa w data md Q d r
    t s1 hw hal heff htm htr htrc hwf hdev)

/-- `XBExecuteSTORE` at the row end: the store instruction runs to its data write, which is
stuck. -/
theorem AxSpinRowEnd.xbExecuteStoreEnd (σ : ExecSt) (himg : img = imgOf σ) (imm : BitVec 12)
    (rs2 rs1 : BitVec 5) (w : Nat) (va pa : BitVec 64) (md : SATPMode)
    (Q : Cst → ExecutionResult → ExecSt → Prop) (d : Cdata) (r : Bool) (t s1 : ExecSt) :
    w ≤ 8 →
    execA (get_transformed_data_addr (.Regidx rs1) (sign_extend (m := 64) imm) (.Store .Data) w)
      (tσ σ t) = some (.Ext_DataAddr_OK (.Virtaddr va), tσ σ t) →
    vmemWidth w →
    is_aligned_vaddr (.Virtaddr va) w = true →
    execA (effectivePrivilege (.Store .Data) (t.regs .mstatus) (t.regs .cur_privilege)) (tσ σ t)
      = some (.Supervisor, tσ σ t) →
    execA (translationMode .Supervisor) (tσ σ t) = some (md, tσ σ t) →
    execA (translateAddr (.Virtaddr va) (.Store .Data)) (tσ σ t)
      = some (.Ok (.Physaddr pa, .PBMT_PMA, ()), s1) →
    cntA (translateAddr (.Virtaddr va) (.Store .Data)) (tσ σ t) = 0 →
    wrFacts σ (.Store .Data) .PBMT_PMA w pa ⟨s1.regs, t.mem, t.dev⟩ → devAddr pa = false →
    AxCert.Cert img dok kind (fun _ _ _ => False) Q ⟨d, .BFin 0, r⟩
      (execute (.STORE (imm, .Regidx rs2, .Regidx rs1, w))) t := by
  intro hw8 hgta hw hal heff htm htr htrc hwf hdev
  show AxCert.Cert img dok kind _ Q _ (execute_STORE imm (.Regidx rs2) (.Regidx rs1) w) t
  unfold execute_STORE
  have h8 : (w ≤b Functions.xlen_bytes) = true := by
    simp only [Functions.xlen_bytes, decide_eq_true_eq]; omega
  simp only [h8]
  refine AxSpinE2.cFactUse himg (execAAssertExpTrue _ _) (by ax_spin_e2_rfs) ?_
  refine AxSpinE2.cFactEvA (rf0EvA img _ _ (rf0RXBits rs2) _ _ _ (execRXBitsGpr rs2 t))
    (nrdOfRf0 _ (rf0RXBits rs2)) ?_
  refine AxCert4.cFactPure ?_
  refine AxCert4.cFactQ (AxSpinRowEnd.xbVmemWriteEnd img dok kind σ himg rs1 _ va pa w
    (AxDataX.stData w (t.gpr rs2)) md (fun _ _ _ => False) d r t s1 hgta hw hal heff htm htr
    htrc hwf hdev) ?_
  intro _ _ _ h
  exact h.elim

end wrEnd

section storeEnd
variable (σi : ExecSt) (T : PTree) (satp0 : BitVec 64)

/-- THE STUCK STORE LEAF'S CERTIFICATE (as `CertBStoreS`): at the row end (`e = 0`, `b = 0`) a
plain store's `execute` reaches its data write, which is stuck; final predicate `False`. -/
theorem AxSpinRowEnd.certBStoreEnd (hmode : _get_Satp64_Mode (Mk_Satp64 satp0) = 8#4)
    (hasid : zero_extend (m := 16) (satp_to_asid satp0) = 0#16)
    (hppn : BitVec.setWidth 44 (satp_to_ppn satp0) = T.base)
    (dok : Int → Nat → Prop) (kind : Dkind) (rs : RegFile) (pc : BitVec 64) (is_rvc : Bool)
    (imm : BitVec 12) (rs2 rs1 : BitVec 5) (w : Nat) (va pa : BitVec 64) (d0 : Cdata) (r0 : Bool)
    (ow : Cdata → Option (BitVec 5 × BitVec 64)) :
    vmemWidth w → 1 ≤ w → w ≤ 8 →
    va = gprVal rs rs1 + sign_extend (m := 64) imm →
    dataAtS σi T (.Store .Data) va w pa → hitW rs va →
    AxSpinRowEnd.CertBAt σi T satp0 dok kind rs pc is_rvc (.STORE (imm, .Regidx rs2, .Regidx rs1, w))
      0 none ow d0 r0 (fun _ _ => False) 0 := by
  intro hvw hw1 hw8 hva hda hhit t ⟨hc, hW⟩ _ _ hag htl
  have hva' : va = gprVal t.regs rs1 + sign_extend (m := 64) imm := by
    rw [gprValAgree _ _ _ hag]; exact hva
  have hhitT : hitW t.regs va := hitWAgree _ _ _ htl hhit
  have hc0 := hc
  obtain ⟨hpriv, -, -, hmenv, -, -, -, hms, -, -, hsatp, -⟩ := hc0
  obtain ⟨hMPRV, hSXL, hMXR, -⟩ := hms
  let σ : ExecSt := tσ σi t
  have heff : exec (effectivePrivilege (.Store .Data) (t.regs .mstatus) .Supervisor) σ
      = some (.Supervisor, σ) := execEffectivePrivilegeStoreS _ σ hMPRV
  have hss : exec (is_shadow_stack_access (.Store .Data)) σ = some (false, σ) := rfl
  obtain ⟨htr, htrc⟩ :=
    dataTranslateHitS σi T satp0 hmode hasid hppn (.Store .Data) t va w pa hc hda hhitT heff hss
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hram, hal, hpal⟩ := hda
  obtain ⟨hwf, hdev⟩ := wrFactsS σi T satp0 ⟨σ.regs, t.mem, t.dev⟩ pa w hc hW hw1 hw8 hram hpal
  have hpmm : pmm_mode_backwards (_get_MEnvcfg_PMM (σ.regs .menvcfg)) = .PMM_Disabled := by
    show pmm_mode_backwards (_get_MEnvcfg_PMM (t.regs .menvcfg)) = .PMM_Disabled
    rw [hmenv]
    first
    | rfl
    | decide +kernel
  have hg : exec (get_transformed_data_addr (.Regidx rs1) (sign_extend (m := 64) imm) (.Store .Data) w)
      σ = some (.Ext_DataAddr_OK (.Virtaddr va), σ) := by
    unfold get_transformed_data_addr
    rw [execBindSome _ _ _ _ _ (execExtDataGetAddrGpr rs1 _ (.Store .Data) w σ)]
    dsimp only
    rw [execBindSome _ _ _ _ _ (execTransformEffectiveAddressStoreS _ satp0 σ hpriv hSXL hsatp hmode
      hMPRV hMXR hpmm)]
    rw [hva']
    rfl
  to_a hg
  have heffA : execA (effectivePrivilege (.Store .Data) (t.regs .mstatus) (t.regs .cur_privilege))
      σ = some (.Supervisor, σ) := by
    rw [hpriv]
    to_a heff
    exact heff
  have htm := execTranslationModeSSv39 satp0 σ hSXL hsatp hmode
  to_a htm
  exact AxSpinRowEnd.xbExecuteStoreEnd (imgS σi) dok kind σi rfl imm rs2 rs1 w va pa .Sv39 _ d0 r0 t σ
    hw8 hg hvw hal heffA htm htr htrc hwf hdev

end storeEnd

/-! # 4. `XBk` over a `CertBAt`, the boundary obligation from a resource -/

section xBkR
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
/-- `XBk` with the boundary's row-end obligation from a resource `R` (no `k < L`) and the
certificate at the exact remaining budget `L - (k + e)` (`CertBAt`). -/
theorem AxSpinRowEnd.XBkR (s : Athread) (rs : RegFile) (k : Nat) (pc : BitVec 64) (is_rvc : Bool)
    (ins : instruction) (e : Nat) (ot : Option (BitVec 64))
    (ow : Cdata → Option (BitVec 5 × BitVec 64)) (d0 : Cdata) (r0 : Bool)
    (PX : Cdata → Bool → Prop) (R : IProp GF) :
    RetX cpu rs k s → ctrlOkSW T satp0 rs → rs .PC = pc → hitW rs pc →
    textOkB σi T satp0 pc is_rvc ins → (∀ d r, PX d r → owOk (ow d)) →
    AxSpinRowEnd.CertBAt σi T satp0 dok kind rs pc is_rvc ins e ot ow d0 r0 PX (L - (k + e)) →
    k + e ≤ L →
    (∀ s1, RetX cpu rs k s1 → s1.atK = L → R ⊢ postLifting Φ i s1) →
    ⊢ R -∗
      (R -∗ CResK dok kind i Out k d0 k ∗
        (∀ d r rs' ib', ⌜PX d r⌝ -∗ ⌜GoodB T satp0 rs pc is_rvc ot (ow d) rs'⌝ -∗
          CResK dok kind i Out k d (k + e) -∗
          wpdM rvwmoCatConsistent .MaybeStuck i ⟨.PHart cpu (.pure ()) rs' none ib', k + e⟩ Φ)) -∗
      wpdM rvwmoCatConsistent .MaybeStuck i s Φ := by
  intro HRet Hc HPC Hhit Htx How Hcert Hle HRb
  have Hbp : AxCert2.bpos G i k (Cst.csB ⟨d0, .BFin (e + (L - (k + e))), r0⟩) := by
    intro GD HGD
    rw [HL GD HGD]
    omega
  have Hb : ∀ GD s1, G GD → RetX cpu rs k s1 → s1.atK = (AxOpsem.grow GD i).length →
      R ⊢ postLifting Φ i s1 := by
    intro GD s1 HGD HR1 Hat
    rw [HL GD HGD] at Hat
    exact HRb s1 HR1 Hat
  iintro HR Hk
  iapply (AxSpinRowEnd.wpdRetNode3MR rvwmoCatConsistent i Φ cpu G HG R rs k s HRet Hb) $$ HR
  iintro HR %s2 %HN
  obtain ⟨tick, rs', Hag, rfl⟩ := HN
  ihave ⟨D, C⟩ := Hk $$ HR
  iapply (wpdOfCertK (imgS σi) dok kind i Φ cpu G HG Hmid Htext Hflow Hloc HnoRmw HnoSplit Out k
    (fun s' _ t' => ∃ d r, s' = ⟨d, .BFin (L - (k + e)), r⟩ ∧ PX d r ∧
      GoodB T satp0 rs pc is_rvc ot (ow d) t'.regs) _
    ⟨d0, .BFin (e + (L - (k + e))), r0⟩ ⟨rs', fun _ => none, testDevs⟩
    (AxSpinRowEnd.spineCertBAt σi T satp0 hmode hasid hppn dok kind rs pc is_rvc ins e ot ow d0 r0 PX
      (L - (k + e)) Hc HPC Hhit Htx How Hcert tick ⟨rs', fun _ => none, testDevs⟩
      (regsAgreeSym _ _ _ Hag))
    rs' ibNone k (regsAgreeRefl _ _) Hbp (Nat.le_refl _)) $$ D
  iintro %s' %t' %rs1 %ib' %k' %HQ %Hag' %Hbp' %_ D
  obtain ⟨d, r, rfl, HPX, HGB⟩ := HQ
  obtain ⟨GD, HGD⟩ := HGex
  have E : (AxOpsem.grow GD i).length = k' + (L - (k + e)) := Hbp' GD HGD
  rw [HL GD HGD] at E
  obtain rfl : k' = k + e := by omega
  iapply C $$ %d %r %rs1 %ib' %HPX %(GoodBAgree σi T satp0 hmode hasid hppn rs pc is_rvc ot (ow d)
    _ rs1 HGB Hag') D

end xBkR

/-! # 5. The row-end leaves at Ixv6 -/

section ixEnd
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

include HL Hcons hmode hasid hppn Hfix HΨmid in
/-- `XxReg` AT THE ROW END (`k = LEN`): a register-only / control instruction; the boundary's
post comes from the resource `R` (`HRb`), which the continuation (at `k`) gets back. -/
theorem AxSpinRowEnd.XxRegEnd (s : Athread) (rs : RegFile) (k : Nat) (pc : BitVec 64)
    (is_rvc : Bool) (ins : instruction) (ot : Option (BitVec 64))
    (ow : Option (BitVec 5 × BitVec 64)) (R : IProp GF) :
    RetX cpu rs k s → ctrlOkSW T satp0 rs → rs .PC = pc → hitW rs pc →
    textOkB σi T satp0 pc is_rvc ins → owOk ow → rfF (execute ins) →
    CertC (ctrlOkSW T satp0) rs pc is_rvc ins ot ow → k = (AxOpsem.grow (gtAdGd GT) i).length →
    (∀ s1, RetX cpu rs k s1 → R ⊢ @postLifting GF (AxSpinX2.xG L GT nm) Ψ i s1) →
    ⊢ R -∗
      (R -∗ ∀ (rs' : RegFile) (ib' : Ibch), ⌜GoodB T satp0 rs pc is_rvc ot ow rs'⌝ -∗
        @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
          ⟨.PHart cpu (.pure ()) rs' none ib', k⟩ Ψ) -∗
      @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i s Ψ := by
  intro HRet Hc HPC Hhit Htx How Hrf Hcert Hk HRb
  have H := @AxSpinRowEnd.XBkR hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) σi T satp0 hmode hasid hppn
    i cpu (fun GD => GD = gtAdGd GT) (HGX L GT nm) (AxOpsem.grow (gtAdGd GT) i).length (HL0 GT i)
    (HGex0 GT) Ψ (AxSpinE6.Hmid0 L GT nm i Ψ HΨmid) (HtextX L GT nm (imgS σi) i Hfix)
    (HflowX L GT nm HL Hcons (imgS σi) i) (HlocX L GT nm i)
    dok0 .DKSt (by intro h; cases h) (by intro h; cases h) (fun _ _ => iprop(True))
    s rs k pc is_rvc ins 0 ot (fun _ => ow) .CPend false (fun d r => d = .CPend ∧ r = false) R
    HRet Hc HPC Hhit Htx (fun _ _ _ => How)
    (AxSpinRowEnd.certBAtOf σi T satp0 dok0 .DKSt rs pc is_rvc ins 0 ot (fun _ => ow) .CPend false _
      (CertBOfCertC σi T satp0 dok0 .DKSt rs pc is_rvc ins ot ow .CPend false Hrf Hcert) _)
    (by omega) (fun s1 H1 _ => HRb s1 H1)
  iintro HR C
  iapply H $$ HR
  iintro HR
  isplitl []
  · simp only [CResK, CFkM]
    letI : AxirisG GF := AxSpinX2.xG L GT nm
    letI : Axpol := xv6Pol GT
    iapply (FstDok0M (GF := GF) rvwmoCatConsistent i)
  · iintro %d %r %rs' %ib' %_ %HGB -
    iapply C $$ HR %rs' %ib' %HGB

include HL Hcons hmode hasid hppn Hfix HΨmid in
/-- A plain STORE AT THE ROW END (`k = LEN`) is STUCK: its data write has no row item
(`AxCert.Cert.cWrEnd`, `AxCert2.wpdStuckWriteM`); every state of the run is the boundary
(post from `R`) or mid-instruction (`HΨmid`).  No continuation. -/
theorem AxSpinRowEnd.XxStEnd (s : Athread) (rs : RegFile) (k : Nat) (pc : BitVec 64) (is_rvc : Bool)
    (imm : BitVec 12) (rs2 rs1 : BitVec 5) (w : Nat) (va pa : BitVec 64) (R : IProp GF) :
    RetX cpu rs k s → ctrlOkSW T satp0 rs → rs .PC = pc → hitW rs pc →
    textOkB σi T satp0 pc is_rvc (.STORE (imm, .Regidx rs2, .Regidx rs1, w)) →
    vmemWidth w → 1 ≤ w → w ≤ 8 →
    va = gprVal rs rs1 + sign_extend (m := 64) imm →
    dataAtS σi T (.Store .Data) va w pa → hitW rs va →
    k = (AxOpsem.grow (gtAdGd GT) i).length →
    (∀ s1, RetX cpu rs k s1 → R ⊢ @postLifting GF (AxSpinX2.xG L GT nm) Ψ i s1) →
    ⊢ R -∗
      @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i s Ψ := by
  intro HRet Hc HPC Hhit Htx hvw hw1 hw8 Hva Hda Hhv Hk HRb
  have Hcert : AxSpinRowEnd.CertBAt σi T satp0 dok0 .DKSt rs pc is_rvc
      (.STORE (imm, .Regidx rs2, .Regidx rs1, w)) 0 none (fun _ => none) .CPend false
      (fun _ _ => False) ((AxOpsem.grow (gtAdGd GT) i).length - (k + 0)) := by
    rw [show (AxOpsem.grow (gtAdGd GT) i).length - (k + 0) = 0 by omega]
    exact AxSpinRowEnd.certBStoreEnd σi T satp0 hmode hasid hppn dok0 .DKSt rs pc is_rvc imm rs2 rs1 w
      va pa .CPend false (fun _ => none) hvw hw1 hw8 Hva Hda Hhv
  have H := @AxSpinRowEnd.XBkR hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) σi T satp0 hmode hasid hppn
    i cpu (fun GD => GD = gtAdGd GT) (HGX L GT nm) (AxOpsem.grow (gtAdGd GT) i).length (HL0 GT i)
    (HGex0 GT) Ψ (AxSpinE6.Hmid0 L GT nm i Ψ HΨmid) (HtextX L GT nm (imgS σi) i Hfix)
    (HflowX L GT nm HL Hcons (imgS σi) i) (HlocX L GT nm i)
    dok0 .DKSt (by intro h; cases h) (by intro h; cases h) (fun _ _ => iprop(True))
    s rs k pc is_rvc _ 0 none (fun _ => none) .CPend false (fun _ _ => False) R
    HRet Hc HPC Hhit Htx (fun _ _ h => h.elim) Hcert (by omega) (fun s1 H1 _ => HRb s1 H1)
  iintro HR
  iapply H $$ HR
  iintro -
  isplitl []
  · simp only [CResK, CFkM]
    letI : AxirisG GF := AxSpinX2.xG L GT nm
    letI : Axpol := xv6Pol GT
    iapply (FstDok0M (GF := GF) rvwmoCatConsistent i)
  · iintro %d %r %rs' %ib' %HPX
    exact HPX.elim

end ixEnd

end Weak
