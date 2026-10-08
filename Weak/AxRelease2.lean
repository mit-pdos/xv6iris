/-
Weak: **the COMPRESSED (2-byte) TLB-framed X bridge at the S-mode data regime**, for the
compressed stack leaves of `release` (c.sdsp / c.ldsp).

Rocq: `iris/AxRelease2.v` @ xxvzwolszwmp.

## The Rocq header, in substance

`CertXT2` — `AxDataX4.CertXT` at nextPC = pc + 2; `CertXT2StoreS` / `CertXT2LoadS` — the S-mode
store / load certificates at nextPC = pc + 2 (the proofs of `CertXTStoreS` / `CertXTLoadS`: they
never use the nextPC hypothesis); `CertHartActiveRvcT` — `AxCert4.CertHartActiveBaseT` for a
compressed fetch (`F_RVC h`, decompress, `ExecuteAs`); `spineCertXT2` — `AxDataX5.spineCertXT`
for a 2-byte word (the fetch from `SpineOkT`'s own `sptFetch`, no `SpineFetch4T`); `XCertT2` —
`AxLeafS2.XCertT` for a 2-byte word; `XStoreS2` / `XLoadS2` — the c.sdsp / c.ldsp X leaves at
`ctrlOkSW`.

## Deviations from Rocq

1. O2 STAGE C (as `AxLeafS2` deviation 1 / `AxCert2` deviation 1): the section premise `Hntext`
   (generic `XCertT2`; the `loads` section of `XLoadS2`) is DROPPED — `wpdInstrOfCertM` no
   longer takes it.  No `sfAnnB` premise is needed: the compressed arm announces nothing the
   certificate must exclude (`AxCert4.cRAnn16` is unconditional).
2. SPELLING as AxLeafS2 deviation 3 / AxDataX4 deviations 1–2: `register_lookup r rs` ↦ `rs r`,
   `regs_agree seip_reg` ↦ `regsAgree AxRunClose.pinReg`, `uint rd ≠ 0` ↦ `rd.toNat ≠ 0`,
   `add_vec_int` ↦ `BitVec.addInt`, `dok (uint pa) (Z.to_nat w)` ↦ `dok (paZ pa) w` with
   `w : Nat` (the certificates take `1 ≤ w → w ≤ 8 →` as AxDataX4, the leaves
   `1 ≤ wd ∧ wd ≤ 8` as AxLeafS2), `add_vec x (sign_extend' 64 imm)` ↦
   `x + sign_extend (m := 64) imm`, `CS d b r` ↦ `⟨d, b, r⟩`, `WPd … @ MaybeStuck; i {{ Φ }}` ↦
   `wpdM rvwmoCatConsistent .MaybeStuck i … Φ`, `Interface.Ret tt` ↦ `.pure ()`; the failure
   predicate's `exception` ↦ `Sail.Error exception`; `iProp` statements are `⊢ … -∗ …`.
3. Section variables / hypotheses are explicit arguments (each declaration takes those it uses,
   as Rocq's section discharge).  The Rocq section notations (`CM`, `EvM`, `decodesC`,
   `expands`, `Hb_at`, `WPK`, `img`, `ctrl_ok`, `Hsp`) are written out; the Ltac `lk` is replaced
   by `RegFile` rewrites, `c_go`/`c_use` by `AxCert4`'s kit and `ax_cert4_go`.

**Rocq → Lean name map.**  `CertXT2` `CertXT2`, `CertXT2_and` `CertXT2And`, `CertXT2_load_S`
`CertXT2LoadS`, `CertXT2_store_S` `CertXT2StoreS`, `Cert_hart_active_rvc_T`
`CertHartActiveRvcT`, `spine_certXT2` `spineCertXT2`, `X_certT2` `XCertT2`, `X_store_S2`
`XStoreS2`, `X_load_S2` `XLoadS2`.  None is in the duplicated-name table.  No Lean-only
declarations.

**Dropped:** nothing (Rocq 9 definitions/lemmas; Lean 9).  **Not ported:** the `Print
Assumptions` lines (the lint's axiom check covers them).
-/
import Weak.AxLeafS2

namespace Weak

open Iris Iris.BI Iris.ProofMode MachCSL
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D LeanRV64D.Functions

/-- Rocq `CertXT2`: `CertXT` at nextPC = pc + 2. -/
def CertXT2 (img : Image) (dok : Int → Nat → Prop) (kind : Dkind)
    (ctrlOk : RegFile → Prop) (rs : RegFile) (pc : BitVec 64) (ins : instruction)
    (ow : Cst → Option (BitVec 5 × BitVec 64)) (s0 : Cst) (PX : Cst → Prop) : Prop :=
  ∀ tpc : ExecSt, ctrlOk tpc.regs →
    tpc.regs .PC = pc →
    tpc.regs .nextPC = BitVec.addInt pc 2 →
    gprAgree tpc.regs rs →
    AxCert.Cert img dok kind (fun (_ : Cst) (_ : Sail.Error exception) (_ : ExecSt) => False)
      (fun s x t' => x = RETIRE_SUCCESS ∧ PX s ∧
        ∃ t0, tlbFrame tpc t0 ∧ ctrlOk t0.regs ∧ t' = wrOpt (ow s) t0) s0 (execute ins) tpc

/-- Rocq `CertXT2_and`. -/
theorem CertXT2And (img : Image) (dok : Int → Nat → Prop) (kind : Dkind) (C P : RegFile → Prop)
    (HP : pDep P) (rs : RegFile) (pc : BitVec 64) (ins : instruction)
    (ow : Cst → Option (BitVec 5 × BitVec 64)) (s0 : Cst) (PX : Cst → Prop) :
    CertXT2 img dok kind C rs pc ins ow s0 PX →
    CertXT2 img dok kind (fun rs => C rs ∧ P rs) rs pc ins ow s0 PX := by
  intro H tpc ⟨hc, hp⟩ HPC Hnpc Hag
  refine CertMono img dok kind _ _ _ _ _ _ tpc (fun _ _ _ h => h) ?_ (H tpc hc HPC Hnpc Hag)
  rintro s x t' ⟨rfl, HPX, t0, Hfr, Hc0, rfl⟩
  exact ⟨rfl, HPX, t0, Hfr, ⟨Hc0, pTlbFrame P HP _ _ Hfr hp⟩, rfl⟩

/-! # 1. The S-mode load / store certificates at nextPC = pc + 2 -/

/-- Rocq `CertXT2_load_S`. -/
theorem CertXT2LoadS (σi : ExecSt) (T : PTree) (satp0 : BitVec 64)
    (hmode : _get_Satp64_Mode (Mk_Satp64 satp0) = 8#4)
    (hasid : zero_extend (m := 16) (satp_to_asid satp0) = 0#16)
    (hppn : BitVec.setWidth 44 (satp_to_ppn satp0) = T.base)
    (dok : Int → Nat → Prop)
    (rs : RegFile) (pc : BitVec 64) (imm : BitVec 12) (rs1 rd : BitVec 5) (u : Bool)
    (w : Nat) (va pa : BitVec 64) (r : Bool) :
    rd.toNat ≠ 0 → vmemWidth w → 1 ≤ w → w ≤ 8 →
    va = gprVal rs rs1 + sign_extend (m := 64) imm →
    dataAtS σi T (.Load .Data) va w pa → dok (paZ pa) w →
    CertXT2 (imgS σi) dok .DKLd (ctrlOkS T satp0) rs pc
      (.LOAD (imm, .Regidx rs1, .Regidx rd, u, w))
      (owLd rd u w) ⟨.CPend, .BInf, r⟩
      (fun s => ∃ vs, s = ⟨.CLd vs, .BInf, r⟩ ∧ vs.length = w) := by
  intro hrd hvw hw1 hw8 hva hda hdok t hc _ _ hag
  have hva' : va = gprVal t.regs rs1 + sign_extend (m := 64) imm := by
    rw [gprValAgree _ _ _ hag]; exact hva
  obtain ⟨s1, hpre, hfr, hc1⟩ :=
    rdPreS σi T satp0 hmode hasid hppn dok imm rs1 w va pa t hc hda hvw hw1 hw8 hva' hdok
  refine CertExecuteLOAD (imgS σi) dok σi rfl imm rs1 rd u w va pa .Sv39 _ r t s1 hrd hpre ?_
  intro vs hvs
  exact ⟨rfl, ⟨vs, rfl, hvs⟩, ⟨s1.regs, t.mem, t.dev⟩, hfr, hc1, rfl⟩

/-- Rocq `CertXT2_store_S`. -/
theorem CertXT2StoreS (σi : ExecSt) (T : PTree) (satp0 : BitVec 64)
    (hmode : _get_Satp64_Mode (Mk_Satp64 satp0) = 8#4)
    (hasid : zero_extend (m := 16) (satp_to_asid satp0) = 0#16)
    (hppn : BitVec.setWidth 44 (satp_to_ppn satp0) = T.base)
    (dok : Int → Nat → Prop)
    (rs : RegFile) (pc : BitVec 64) (imm : BitVec 12) (rs2 rs1 : BitVec 5)
    (w : Nat) (va pa : BitVec 64) (r : Bool) :
    vmemWidth w → 1 ≤ w → w ≤ 8 →
    va = gprVal rs rs1 + sign_extend (m := 64) imm →
    dataAtS σi T (.Store .Data) va w pa → dok (paZ pa) w →
    CertXT2 (imgS σi) dok .DKSt (ctrlOkSW T satp0) rs pc
      (.STORE (imm, .Regidx rs2, .Regidx rs1, w))
      (fun _ => none) ⟨.CPend, .BInf, r⟩
      (fun s => s = ⟨.CSt (stBytes w (gprVal rs rs2)) (wcls AxDataX.akPlain r), .BInf, false⟩) := by
  intro hvw hw1 hw8 hva hda hdok t ⟨hc, hW⟩ _ _ hag
  have hva' : va = gprVal t.regs rs1 + sign_extend (m := 64) imm := by
    rw [gprValAgree _ _ _ hag]; exact hva
  obtain ⟨s1, hpre, hfr, hc1⟩ :=
    wrPreS σi T satp0 hmode hasid hppn dok imm rs1 w va pa t hc hW hda hvw hw1 hw8 hva' hdok
  refine CertExecuteSTORE (imgS σi) dok σi rfl imm rs2 rs1 w va pa .Sv39 _ r t s1 hpre ?_
  refine ⟨rfl, ?_, ⟨s1.regs, t.mem, t.dev⟩, hfr,
    ⟨hc1, AxDataX4.pmpWTlbFrame t s1.regs t.mem t.dev hW hfr⟩, rfl⟩
  rw [gprValAgree _ _ _ hag]

/-! # 2. The compressed spine -/

section spineXT2
variable (img : Image) (dok : Int → Nat → Prop) (kind : Dkind)

/-- Rocq `Cert_hart_active_rvc_T`. -/
theorem CertHartActiveRvcT (t t1 : ExecSt) (h : BitVec 16) (i0 ins : instruction)
    (pc : BitVec 64) (d : Cdata) (r : Bool) (Qx : Cst → ExecSt → Prop) :
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
    AxCert.Cert img dok kind (fun _ _ _ => False) (fun s x t' => x = RETIRE_SUCCESS ∧ Qx s t')
      ⟨d, .BInf, r⟩ (execute ins) (t1.setReg .nextPC (BitVec.addInt pc 2)) →
    AxCert.Cert img dok kind (fun _ _ _ => False)
      (fun s x t' => x = .Step_Execute (RETIRE_SUCCESS, zero_extend (m := 32) h) ∧ Qx s t')
      ⟨d, .BInf, r⟩ (run_hart_active 0) t := by
  intro Hdisp Hfetch Hdec Hlpad Hzca HPC Hexp Hexec
  subst HPC
  unfold run_hart_active
  apply CertCatchEarlyReturn
  ax_cert4_go
  refine AxCert4.cRUse Hdisp ?_
  ax_cert4_go
  refine AxCert4.cRUse Hfetch ?_
  ax_cert4_go
  refine AxCert4.cRUse Hdec ?_
  ax_cert4_go
  refine AxCert4.cRUse Hlpad ?_
  ax_cert4_go
  refine AxCert4.cRUse Hzca ?_
  ax_cert4_go
  refine AxCert4.cRUse Hexp ?_
  ax_cert4_go
  refine AxCert4.cFactLift Hexec ?_
  rintro _ _ t' ⟨rfl, hq⟩
  ax_cert4_go
  exact .cRet _ _ _ ⟨rfl, hq⟩

/-- Rocq `spine_certXT2`. -/
theorem spineCertXT2 (ctrlOk : RegFile → Prop) (textAt : BitVec 64 → BitVec 16 → Prop)
    (Hsp : SpineOkT img ctrlOk textAt)
    (rs : RegFile) (pc : BitVec 64) (h : BitVec 16) (i0 ins : instruction)
    (ow : Cst → Option (BitVec 5 × BitVec 64)) (d : Cdata) (r : Bool) (PX : Cst → Prop) :
    ctrlOk rs → rs .PC = pc → textAt pc h →
    (∀ t : ExecSt, ctrlOk t.regs →
      EvA img (fun _ _ => False) (fun x t' => x = i0 ∧ t' = t) (ext_decode_compressed h) t) →
    (∀ t : ExecSt, EvA img (fun _ _ => False) (fun x t' => x = .ExecuteAs ins ∧ t' = t)
      (execute i0) t) →
    (∀ s, PX s → owOk (ow s)) → (∀ s, PX s → s.csB = .BInf) →
    CertXT2 img dok kind ctrlOk rs pc ins ow ⟨d, .BInf, r⟩ PX →
    ∀ (tick : Bool) (t : ExecSt), regsAgree AxRunClose.pinReg t.regs rs →
      AxCert.Cert img dok kind (fun _ _ _ => False)
        (fun s _ t' => PX s ∧ GoodC ctrlOk true rs pc none (ow s) t'.regs)
        ⟨d, .BInf, r⟩ (riscvStep tick) t := by
  intro Hct HPC Htx Hdec Hexp How HPX Hcert tick t Hag
  have Hct_t : ctrlOk t.regs := Hsp.sptSeip _ _ Hct Hag
  have HPC_t : t.regs .PC = pc := by
    rw [Hag .PC (AxSymEngine2.notPin _ (by decide) (by decide))]; exact HPC
  obtain ⟨b, Hb⟩ := Hsp.sptInc t Hct_t
  have Hct_a : ctrlOk (t.setReg .minstret_increment b).regs :=
    Hsp.sptFrame _ _ _ (Or.inr (Or.inr (Or.inl rfl))) Hct_t
  have HPC_a : (t.setReg .minstret_increment b).regs .PC = pc := by
    rw [ExecSt.setReg_regs, RegFile.set_other _ _ _ _ (by decide)]; exact HPC_t
  obtain ⟨t1, Hfr, Hct1, Hfetch⟩ := Hsp.sptFetch _ pc h Hct_a HPC_a Htx
  have HPC_1 : t1.regs .PC = pc := (tlbFrameLookup _ _ _ Hfr (by decide)).trans HPC_a
  have Hgag : gprAgree (t1.setReg .nextPC (BitVec.addInt pc 2)).regs rs := by
    intro r _
    simp only [ExecSt.setReg_regs]
    rw [AxSymEngine2.uxaXgetSetNe _ _ _ (by decide), AxSpineOk5.tlbFrameXget _ _ Hfr,
      ExecSt.setReg_regs, AxSymEngine2.uxaXgetSetNe _ _ _ (by decide)]
    exact AxSymEngine2.uxaXgetAgree _ _ Hag r
  have Hct_pc : ctrlOk (t1.setReg .nextPC (BitVec.addInt pc 2)).regs :=
    Hsp.sptFrame _ _ _ (Or.inr (Or.inl rfl)) Hct1
  have HPC_pc : (t1.setReg .nextPC (BitVec.addInt pc 2)).regs .PC = pc := by
    rw [ExecSt.setReg_regs, RegFile.set_other _ _ _ _ (by decide)]; exact HPC_1
  have Hnpc_pc : (t1.setReg .nextPC (BitVec.addInt pc 2)).regs .nextPC =
      BitVec.addInt pc 2 := by
    simp only [ExecSt.setReg_regs, RegFile.set_same]
  have Hexec := Hcert _ Hct_pc HPC_pc Hnpc_pc Hgag
  have Hrun := CertHartActiveRvcT img dok kind _ t1 h i0 ins pc d r
    (fun s t' => PX s ∧ ∃ t0, tlbFrame (t1.setReg .nextPC (BitVec.addInt pc 2)) t0 ∧
      ctrlOk t0.regs ∧ t' = wrOpt (ow s) t0)
    (Hsp.sptDisp _ Hct_a) Hfetch (Hdec _ Hct1) (Hsp.sptLpad _ Hct1) (Hsp.sptZca _ Hct1) HPC_1
    (Hexp _) Hexec
  have Hmi1 : t1.regs .minstret_increment = b := by
    rw [tlbFrameLookup _ _ _ Hfr (by decide)]
    simp only [ExecSt.setReg_regs, RegFile.set_same]
  refine CertRiscvStep img dok kind tick ⟨d, .BInf, r⟩ t
    (fun s t' => PX s ∧ GoodC ctrlOk true rs pc none (ow s) t'.regs) _ ?_ ?_
  · have HT := CertTryStepActive img dok kind t b (zero_extend (m := 32) h) d r
      (fun s t' => PX s ∧ ∃ t0, tlbFrame (t1.setReg .nextPC (BitVec.addInt pc 2)) t0 ∧
        ctrlOk t0.regs ∧ t' = wrOpt (ow s) t0)
      (fun s t' => PX s ∧ GoodC ctrlOk true rs pc none (ow s) t'.regs) Hb
      (Hsp.sptHart _ Hct_a) Hrun ?_
    · exact CertMono img dok kind _ _ _ _ _ _ t (fun _ _ _ h => h) (fun _ _ _ h => h.2) HT
    · rintro s _ ⟨HP, t0, Hfr0, Hc0, rfl⟩
      have Hct_x := wrNpcCtrl img ctrlOk textAt Hsp (ow s) none _ Hc0
      have How' := How s HP
      rw [show wrOpt (ow s) t0 = wrOpt (ow s) (npcOpt none t0) from rfl]
      refine ⟨?_, ?_, HP, ?_, ?_, ?_⟩
      · rw [wrNpcOther _ _ _ _ (by decide) (by decide), tlbFrameLookup _ _ _ Hfr0 (by decide)]
        simp only [ExecSt.setReg_regs]
        rw [RegFile.set_other _ _ _ _ (by decide)]
        exact Hsp.sptHart _ Hct1
      · rw [wrNpcOther _ _ _ _ (by decide) (by decide), tlbFrameLookup _ _ _ Hfr0 (by decide)]
        simp only [ExecSt.setReg_regs]
        rw [RegFile.set_other _ _ _ _ (by decide)]
        exact Hmi1
      · unfold tfinal
        cases b
        · exact Hsp.sptFrame _ _ _ (Or.inl rfl) Hct_x
        · exact Hsp.sptFrame _ _ _ (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
            (Hsp.sptFrame _ _ _ (Or.inl rfl) Hct_x)
      · rw [tfinalPC, wrNpcNextPC, tlbFrameLookup _ _ _ Hfr0 (by decide)]
        exact Hnpc_pc
      · intro r Hr
        rw [tfinalGpr, wrNpcGpr _ _ _ _ Hr How']
        refine gprPostAgree _ _ _ _ ?_ Hr
        intro r1 Hr1
        rw [AxSpineOk5.tlbFrameXget _ _ Hfr0]
        exact Hgag r1 Hr1
  · rintro s' t' ⟨HP, HG⟩
    cases tick with
    | false => exact ⟨HP, HG⟩
    | true =>
      obtain ⟨d', b', r'⟩ := s'
      have Hb' : b' = .BInf := HPX _ HP
      subst Hb'
      refine CertMono img dok kind _ _ _ _ _ _ t' (fun _ _ _ h => h) ?_
        (CertEvA img dok kind _ _ d' r' t' (Hsp.sptTick t' HG.1))
      rintro _ _ t'' ⟨rfl, Hc, Hk1, Hk2⟩
      obtain ⟨-, HG2, HG3⟩ := HG
      exact ⟨HP, Hc, Hk1.trans HG2, fun r Hr => (Hk2 r).trans (HG3 r Hr)⟩

end spineXT2

/-! # 3. The generic 2-byte TLB-framed X leaf -/

section xT2
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
variable (Hloc : ∀ GD ls k, rvwmoCatConsistent GD →
  AxirisG.gconstInterp (GF := GF) GD ∗ AxirisG.localInterp GD i k ls ⊢
    |==> ∃ ls', AxirisG.localInterp GD i (k + 1) ls')
variable (G : Gdexec → Prop)
  (HG : ∀ GD, rvwmoCatConsistent GD → AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜G GD⌝)
variable (Φ : Athread → IProp GF)
variable (Hmid : ∀ GD s, G GD → midState s → s.atK = (AxOpsem.grow GD i).length →
  ⊢ postLifting Φ i s)
variable (dok : Int → Nat → Prop) (kind : Dkind) (Out : Nat → List (BitVec 8) → IProp GF)
variable (HnoRmw : kind = .DKLd → ∀ GD, rvwmoCatConsistent GD →
  AxirisG.gconstInterp (GF := GF) GD ⊢
  ⌜∀ (k : Nat) (lb : Lbl) (aq rl : Bool) (base : Int) (n : Nat),
    (AxOpsem.grow GD i)[k]? = some lb → aident lb = .IRmw aq rl base n → ¬ dok base n⌝)
variable (HnoSplit : kind = .DKRmw → ∀ GD, rvwmoCatConsistent GD →
  AxirisG.gconstInterp (GF := GF) GD ⊢
  ⌜∀ (k : Nat) (lb : Lbl) (aq : Bool) (base : Int) (n : Nat),
    (AxOpsem.grow GD i)[k]? = some lb → aident lb = .IRead aq base n → ¬ dok base n⌝)

include Hsp Htext Hflow Hloc HG Hmid HnoRmw HnoSplit in
/-- Rocq `X_certT2`: the generic 2-byte TLB-framed X leaf. -/
theorem XCertT2 (s : Athread) (rs : RegFile) (k : Nat) (pc : BitVec 64) (h : BitVec 16)
    (i0 ins : instruction) (ow : Cst → Option (BitVec 5 × BitVec 64)) (d0 : Cdata) (r0 : Bool)
    (PX : Cst → Prop)
    (HRet : RetX cpu rs k s) (Hctrl : ctrlOk rs) (HPC : rs .PC = pc) (Htx : textAt pc h)
    (Hdec : ∀ t : ExecSt, ctrlOk t.regs →
      EvA img (fun _ _ => False) (fun x t' => x = i0 ∧ t' = t) (ext_decode_compressed h) t)
    (Hexp : ∀ t : ExecSt, EvA img (fun _ _ => False)
      (fun x t' => x = .ExecuteAs ins ∧ t' = t) (execute i0) t)
    (How : ∀ s', PX s' → owOk (ow s')) (HPXb : ∀ s', PX s' → s'.csB = .BInf)
    (Hcert : CertXT2 img dok kind ctrlOk rs pc ins ow ⟨d0, .BInf, r0⟩ PX)
    (Hb : ∀ GD s1, G GD → RetX cpu rs k s1 → s1.atK = (AxOpsem.grow GD i).length →
      ⊢ postLifting Φ i s1) :
    ⊢ CRes dok kind i Out d0 -∗
      (∀ (s' : Cst) (t' : ExecSt) (rs' : RegFile) (ib' : Ibch) (k' : Nat), ⌜PX s'⌝ -∗
        ⌜GoodC ctrlOk true rs pc none (ow s') t'.regs⌝ -∗
        ⌜regsAgree AxRunClose.pinReg rs' t'.regs⌝ -∗ CRes dok kind i Out s'.csD -∗
        wpdM rvwmoCatConsistent .MaybeStuck i ⟨.PHart cpu (.pure ()) rs' none ib', k'⟩ Φ) -∗
      wpdM rvwmoCatConsistent .MaybeStuck i s Φ := by
  have Hc : ∀ (tick : Bool) (t : ExecSt), regsAgree AxRunClose.pinReg t.regs rs →
      AxCert.Cert img dok kind (fun _ _ _ => False)
        (fun s' _ t' => PX s' ∧ GoodC ctrlOk true rs pc none (ow s') t'.regs)
        ⟨d0, .BInf, r0⟩ (riscvStep tick) t :=
    fun tick t Hag => spineCertXT2 img dok kind ctrlOk textAt Hsp rs pc h i0 ins ow d0
      r0 PX Hctrl HPC Htx Hdec Hexp How HPXb Hcert tick t Hag
  have Hbr : CRes dok kind i Out d0 ⊢
      CResM rvwmoCatConsistent dok kind i Out (⟨d0, .BInf, r0⟩ : Cst).csD := .rfl
  iintro D C
  ihave D := Hbr $$ D
  iapply (wpdInstrOfCertM rvwmoCatConsistent img dok kind i Φ cpu G HG Hmid Htext Hflow Hloc
    HnoRmw HnoSplit Out _ ⟨d0, .BInf, r0⟩ rs k s HRet trivial Hb Hc) $$ D
  iintro %s' %t' %rs' %ib' %k' %HQ %Hag %_ HD
  obtain ⟨HP, HG'⟩ := HQ
  iapply C $$ %s' %t' %rs' %ib' %k' %HP %HG' %Hag HD

end xT2

/-! # 4. The S-mode compressed store / load at `ctrlOkSW` -/

section xS2
variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [AxirisG GF] [Axpol]
variable (σi : ExecSt) (T : PTree) (satp0 : BitVec 64)
variable (hmode : _get_Satp64_Mode (Mk_Satp64 satp0) = 8#4)
  (hasid : zero_extend (m := 16) (satp_to_asid satp0) = 0#16)
  (hppn : BitVec.setWidth 44 (satp_to_ppn satp0) = T.base)
variable (i : Agent) (cpu : CPU)
variable (Htext : ∀ GD, rvwmoCatConsistent GD →
  AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜textFixed GD i (imgS σi)⌝)
variable (Hflow : ∀ GD ls k, rvwmoCatConsistent GD →
  (∃ lb aq base n vs, (AxOpsem.grow GD i)[k]? = some lb ∧ aident lb = .IRead aq base n ∧
     imgBytes (imgS σi) base n = some vs) →
  AxirisG.gconstInterp (GF := GF) GD ∗ AxirisG.localInterp GD i k ls ⊢ fetchFlow GD i k)
variable (Hloc : ∀ GD ls k, rvwmoCatConsistent GD →
  AxirisG.gconstInterp (GF := GF) GD ∗ AxirisG.localInterp GD i k ls ⊢
    |==> ∃ ls', AxirisG.localInterp GD i (k + 1) ls')
variable (G : Gdexec → Prop)
  (HG : ∀ GD, rvwmoCatConsistent GD → AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜G GD⌝)
variable (Φ : Athread → IProp GF)
variable (Hmid : ∀ GD s, G GD → midState s → s.atK = (AxOpsem.grow GD i).length →
  ⊢ postLifting Φ i s)
variable (dok : Int → Nat → Prop) (Out : Nat → List (BitVec 8) → IProp GF)

include hmode hasid hppn Htext Hflow Hloc HG Hmid in
/-- Rocq `X_store_S2`: the compressed store (c.sdsp) leaf. -/
theorem XStoreS2 (s : Athread) (rs : RegFile) (k : Nat) (pc : BitVec 64) (h : BitVec 16)
    (i0 : instruction) (imm : BitVec 12) (rs2 rs1 : BitVec 5) (wd : Nat) (va pa : BitVec 64)
    (r : Bool)
    (HRet : RetX cpu rs k s) (Hctrl : ctrlOkSW T satp0 rs) (HPC : rs .PC = pc)
    (Htx : textAtS σi T pc h)
    (Hdec : ∀ t : ExecSt, ctrlOkSW T satp0 t.regs →
      EvA (imgS σi) (fun _ _ => False) (fun x t' => x = i0 ∧ t' = t) (ext_decode_compressed h) t)
    (Hexp : ∀ t : ExecSt, EvA (imgS σi) (fun _ _ => False)
      (fun x t' => x = .ExecuteAs (.STORE (imm, .Regidx rs2, .Regidx rs1, wd)) ∧ t' = t)
      (execute i0) t)
    (Hvw : vmemWidth wd) (Hw : 1 ≤ wd ∧ wd ≤ 8)
    (Hva : va = gprVal rs rs1 + sign_extend (m := 64) imm)
    (Hda : dataAtS σi T (.Store .Data) va wd pa) (Hdok : dok (paZ pa) wd)
    (Hb : ∀ GD s1, G GD → RetX cpu rs k s1 → s1.atK = (AxOpsem.grow GD i).length →
      ⊢ postLifting Φ i s1) :
    ⊢ Fst dok i Out -∗
      (∀ (t' : ExecSt) (rs' : RegFile) (ib' : Ibch) (k' : Nat),
        ⌜GoodC (ctrlOkSW T satp0) true rs pc none none t'.regs⌝ -∗
        ⌜regsAgree AxRunClose.pinReg rs' t'.regs⌝ -∗
        (∃ kd, Out kd (stBytes wd (gprVal rs rs2))) -∗
        wpdM rvwmoCatConsistent .MaybeStuck i ⟨.PHart cpu (.pure ()) rs' none ib', k'⟩ Φ) -∗
      wpdM rvwmoCatConsistent .MaybeStuck i s Φ := by
  have Hcert := CertXT2StoreS σi T satp0 hmode hasid hppn dok rs pc imm rs2 rs1 wd va pa r
    Hvw Hw.1 Hw.2 Hva Hda Hdok
  have Hbr : Fst dok i Out ⊢ CRes dok .DKSt i Out .CPend := .rfl
  iintro F C
  ihave F := Hbr $$ F
  iapply (XCertT2 (imgS σi) i cpu (ctrlOkSW T satp0) (textAtS σi T)
    (SpineOkTSW σi T satp0 hmode hasid hppn)
    Htext Hflow Hloc G HG Φ Hmid dok .DKSt Out (fun h => nomatch h) (fun h => nomatch h)
    s rs k pc h i0 _ (fun _ => none) .CPend r _ HRet Hctrl HPC Htx Hdec Hexp
    (fun _ _ => trivial) (fun _ h => by subst h; rfl) Hcert Hb) $$ F
  iintro %s' %t' %rs' %ib' %k' %HP %HG' %Hag HD
  subst HP
  have Hbr2 : CRes dok .DKSt i Out
      (⟨.CSt (stBytes wd (gprVal rs rs2)) (wcls AxDataX.akPlain r), .BInf, false⟩ : Cst).csD ⊢
      iprop(∃ kd, Out kd (stBytes wd (gprVal rs rs2))) := .rfl
  ihave HD := Hbr2 $$ HD
  iapply C $$ %t' %rs' %ib' %k' %HG' %Hag HD

section loads
variable (HnoRmw : ∀ GD, rvwmoCatConsistent GD → AxirisG.gconstInterp (GF := GF) GD ⊢
  ⌜∀ (k : Nat) (lb : Lbl) (aq rl : Bool) (base : Int) (n : Nat),
    (AxOpsem.grow GD i)[k]? = some lb → aident lb = .IRmw aq rl base n → ¬ dok base n⌝)

include hmode hasid hppn Htext Hflow Hloc HG Hmid HnoRmw in
/-- Rocq `X_load_S2`: the compressed load (c.ldsp) leaf. -/
theorem XLoadS2 (s : Athread) (rs : RegFile) (k : Nat) (pc : BitVec 64) (h : BitVec 16)
    (i0 : instruction) (imm : BitVec 12) (rs1 rd : BitVec 5) (u : Bool) (wd : Nat)
    (va pa : BitVec 64)
    (HRet : RetX cpu rs k s) (Hctrl : ctrlOkSW T satp0 rs) (HPC : rs .PC = pc)
    (Htx : textAtS σi T pc h)
    (Hdec : ∀ t : ExecSt, ctrlOkSW T satp0 t.regs →
      EvA (imgS σi) (fun _ _ => False) (fun x t' => x = i0 ∧ t' = t) (ext_decode_compressed h) t)
    (Hexp : ∀ t : ExecSt, EvA (imgS σi) (fun _ _ => False)
      (fun x t' => x = .ExecuteAs (.LOAD (imm, .Regidx rs1, .Regidx rd, u, wd)) ∧ t' = t)
      (execute i0) t)
    (Hrd : rd.toNat ≠ 0) (Hvw : vmemWidth wd) (Hw : 1 ≤ wd ∧ wd ≤ 8)
    (Hva : va = gprVal rs rs1 + sign_extend (m := 64) imm)
    (Hda : dataAtS σi T (.Load .Data) va wd pa) (Hdok : dok (paZ pa) wd)
    (Hb : ∀ GD s1, G GD → RetX cpu rs k s1 → s1.atK = (AxOpsem.grow GD i).length →
      ⊢ postLifting Φ i s1) :
    ⊢ Fld dok i Out -∗
      (∀ (vs : List (BitVec 8)) (t' : ExecSt) (rs' : RegFile) (ib' : Ibch) (k' : Nat),
        ⌜vs.length = wd⌝ -∗
        ⌜GoodC (ctrlOkSW T satp0) true rs pc none (some (rd, ldRes u wd vs)) t'.regs⌝ -∗
        ⌜regsAgree AxRunClose.pinReg rs' t'.regs⌝ -∗ (∃ kd, Out kd vs) -∗
        wpdM rvwmoCatConsistent .MaybeStuck i ⟨.PHart cpu (.pure ()) rs' none ib', k'⟩ Φ) -∗
      wpdM rvwmoCatConsistent .MaybeStuck i s Φ := by
  have Hcert : CertXT2 (imgS σi) dok .DKLd (ctrlOkSW T satp0) rs pc
      (.LOAD (imm, .Regidx rs1, .Regidx rd, u, wd)) (owLd rd u wd) ⟨.CPend, .BInf, false⟩
      (fun s' => ∃ vs, s' = ⟨.CLd vs, .BInf, false⟩ ∧ vs.length = wd) :=
    CertXT2And (imgS σi) dok .DKLd (ctrlOkS T satp0) pmpW pmpWDep _ _ _ _ _ _
      (CertXT2LoadS σi T satp0 hmode hasid hppn dok rs pc imm rs1 rd u wd va pa false
        Hrd Hvw Hw.1 Hw.2 Hva Hda Hdok)
  have How : ∀ s', (∃ vs, s' = (⟨.CLd vs, .BInf, false⟩ : Cst) ∧ vs.length = wd) →
      owOk (owLd rd u wd s') := by
    rintro _ ⟨_, rfl, _⟩
    exact Hrd
  have HPXb : ∀ s', (∃ vs, s' = (⟨.CLd vs, .BInf, false⟩ : Cst) ∧ vs.length = wd) →
      s'.csB = .BInf := by
    rintro _ ⟨_, rfl, _⟩
    rfl
  have Hbr : Fld dok i Out ⊢ CRes dok .DKLd i Out .CPend := .rfl
  iintro F C
  ihave F := Hbr $$ F
  iapply (XCertT2 (imgS σi) i cpu (ctrlOkSW T satp0) (textAtS σi T)
    (SpineOkTSW σi T satp0 hmode hasid hppn)
    Htext Hflow Hloc G HG Φ Hmid dok .DKLd Out (fun _ => HnoRmw) (fun h => nomatch h)
    s rs k pc h i0 _ (owLd rd u wd) .CPend false _ HRet Hctrl HPC Htx Hdec Hexp How HPXb Hcert
    Hb) $$ F
  iintro %s' %t' %rs' %ib' %k' %HP %HG' %Hag HD
  obtain ⟨vs, rfl, Hlen⟩ := HP
  have Hbr2 : CRes dok .DKLd i Out (⟨.CLd vs, .BInf, false⟩ : Cst).csD ⊢
      iprop(∃ kd, Out kd vs) := .rfl
  ihave HD := Hbr2 $$ HD
  iapply C $$ %vs %t' %rs' %ib' %k' %Hlen %HG' %Hag HD

end loads

end xS2

end Weak
