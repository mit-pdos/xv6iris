/-
Weak: **`AxSymMem2.ExecD` PROVED SYMBOLICALLY in the S-mode regime** for every LOAD / STORE of
width `1 ≤ w ≤ 8` (so c.ldsp / c.sdsp / ld / sd — the decode to `LOAD` / `STORE` is the
per-instruction `textOkM` fact), and the `AxCert.Cert` twins.

Rocq: `iris/AxDataX4.v` @ xxvzwolszwmp.

## The Rocq header, in substance

`ExecDLoadS`: at `ctrlOkS` (any state of the S-mode kernel regime), for a data address
`va = rs1 + imm` (of the BOUNDARY register file) whose page is mapped by the image tree
(`AxDataX3.dataAtS`), the data read is DEMONIC, `rd := ldRes u w vs`, the walk may fill the TLB
(`tlbFrame`).  `ExecDStoreS`: the same at `ctrlOkSW` = `ctrlOkS ∧ pmpW` (stores need the PMP W
bit, which the fetch regime does not record); the data event's bytes are rs2's low `w` bytes
(`dpSt`).  FINDING (Cert side): `AxCert4.CertX` / `CertAmo` demand the final state be EXACTLY
`wrOpt ow tpc` — a data-side TLB MISS fills the TLB, so they are FALSE for any data access on a
cold TLB (the AxSpineOk5 fetch finding, again).  `CertXT` (§2) is the tlb-framed version; the
4-byte spine over it is `AxDataX5.spineCertXT`.

## Deviations from Rocq

1. SPELLING as `AxDataX3` deviation 1 (`mword n` ↦ `BitVec n`, `register_lookup r rs` ↦ `rs r`,
   `uint` ↦ `toNat` / `paZ`, `add_vec (gpr_val rs rs1) (sign_extend' 64 imm)` ↦
   `gprVal rs rs1 + sign_extend (m := 64) imm`, `add_vec_int pc 4` ↦ `BitVec.addInt pc 4`,
   `img_S` ↦ `imgS`, `ak_plain` ↦ `AxDataX.akPlain`, `Cert` ↦ `AxCert.Cert`); the `satp0`
   hypotheses take `AxSpineOk6.sptFetchS`'s shapes (as `AxDataX3.rdPreS`).
2. Widths are `Nat` (`AxDataX` deviation 4): `1 ≤ w ≤ 8` is `1 ≤ w → w ≤ 8 →`, `Z.to_nat w` ↦ `w`.
3. Section variables `σi T satp0 dok` and hypotheses `Hmode Hasid Hppn` are explicit arguments
   (each declaration takes those it uses, in the section order).
4. The `pmpW` frame across the TLB fill (inline in Rocq's two store proofs) is the Lean-only
   `AxDataX4.pmpWTlbFrame`.

**Rocq → Lean name map.**  `gpr_val_agree` `gprValAgree`, `ctrl_ok_SW` `ctrlOkSW`, `dp_ld` `dpLd`,
`ExecD_load_S` `ExecDLoadS`, `dp_st` `dpSt`, `ExecD_store_S` `ExecDStoreS`, `CertXT` `CertXT`,
`ow_ld` `owLd`, `CertXT_load_S` `CertXTLoadS`, `CertXT_store_S` `CertXTStoreS`.  None is in the
duplicated-name table.  Lean-only (file-qualified): `AxDataX4.pmpWTlbFrame`.

**Dropped:** nothing (the `Print Assumptions` lines).  Rocq 10 definitions/lemmas, Lean 10 + 1
Lean-only.
-/
import Weak.AxDataX3
import Weak.AxSymMem2
import Weak.AxSymCtl2
import Weak.AxReuseProbe2

namespace Weak

open MachCSL
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D LeanRV64D.Functions

/-- Rocq `gpr_val_agree`. -/
theorem gprValAgree (a b : RegFile) (r : BitVec 5) : gprAgree a b → gprVal a r = gprVal b r := by
  intro H
  unfold gprVal
  by_cases h : r.toNat = 0
  · rw [AxReuseProbe2.uxaXgetZero a r h, AxReuseProbe2.uxaXgetZero b r h]
  · exact H r h

/-- Rocq `ctrl_ok_SW`: the S-mode regime plus the PMP W bit. -/
def ctrlOkSW (T : PTree) (satp0 : BitVec 64) (rs : RegFile) : Prop :=
  ctrlOkS T satp0 rs ∧ pmpW rs

/-- (Lean-only, deviation 4) the PMP W bit survives a TLB fill. -/
theorem AxDataX4.pmpWTlbFrame (t : ExecSt) (r : RegFile) (m : BMap) (d : DevStates) :
    pmpW t.regs → tlbFrame t ⟨r, m, d⟩ → pmpW r := by
  intro hW hfr
  rcases hfr with h | ⟨v, h⟩
  · have hr := congrArg ExecSt.regs h
    dsimp only at hr
    rw [hr]
    exact hW
  · have hr := congrArg ExecSt.regs h
    dsimp only at hr
    rw [hr, ExecSt.setReg_regs]
    unfold pmpW
    rw [RegFile.set_other _ _ _ _ (by decide)]
    exact hW

/-- Rocq `dp_ld`: the data event of a load is any `w` bytes. -/
def dpLd (w : Nat) (d : AxSymMem.Dstate) : Prop := ∃ vs, d = .DDone vs ∧ vs.length = w

/-- Rocq `ExecD_load_S`. -/
theorem ExecDLoadS (σi : ExecSt) (T : PTree) (satp0 : BitVec 64)
    (hmode : _get_Satp64_Mode (Mk_Satp64 satp0) = 8#4)
    (hasid : zero_extend (m := 16) (satp_to_asid satp0) = 0#16)
    (hppn : BitVec.setWidth 44 (satp_to_ppn satp0) = T.base)
    (dok : Int → Nat → Prop)
    (rs : RegFile) (pc : BitVec 64) (imm : BitVec 12) (rs1 rd : BitVec 5) (u : Bool)
    (w : Nat) (va pa : BitVec 64) :
    rd.toNat ≠ 0 → vmemWidth w → 1 ≤ w → w ≤ 8 →
    va = gprVal rs rs1 + sign_extend (m := 64) imm →
    dataAtS σi T (.Load .Data) va w pa → dok (paZ pa) w →
    ExecD (imgS σi) dok true (ctrlOkS T satp0) rs pc (wrLoad rd (ldRes u w)) (dpLd w)
      (.LOAD (imm, .Regidx rs1, .Regidx rd, u, w)) := by
  intro hrd hvw hw1 hw8 hva hda hdok t hc _ hag
  have hva' : va = gprVal t.regs rs1 + sign_extend (m := 64) imm := by
    rw [gprValAgree _ _ _ hag]; exact hva
  obtain ⟨s1, hpre, hfr, hc1⟩ :=
    rdPreS σi T satp0 hmode hasid hppn dok imm rs1 w va pa t hc hda hvw hw1 hw8 hva' hdok
  refine EvDExecuteLOAD (imgS σi) dok σi rfl imm rs1 rd u w va pa .Sv39 _ t s1 hrd hpre ?_
  intro vs hvs
  refine ⟨rfl, fun h => AxSymMem.Dstate.noConfusion h, ⟨vs, rfl, hvs⟩, ?_⟩
  exact ⟨⟨s1.regs, t.mem, t.dev⟩, hfr, hc1, rfl⟩

/-- Rocq `dp_st`: the data event of a store is rs2's low `w` bytes. -/
def dpSt (rs : RegFile) (rs2 : BitVec 5) (w : Nat) (d : AxSymMem.Dstate) : Prop :=
  d = .DDone (stBytes w (gprVal rs rs2))

/-- Rocq `ExecD_store_S`. -/
theorem ExecDStoreS (σi : ExecSt) (T : PTree) (satp0 : BitVec 64)
    (hmode : _get_Satp64_Mode (Mk_Satp64 satp0) = 8#4)
    (hasid : zero_extend (m := 16) (satp_to_asid satp0) = 0#16)
    (hppn : BitVec.setWidth 44 (satp_to_ppn satp0) = T.base)
    (dok : Int → Nat → Prop)
    (rs : RegFile) (pc : BitVec 64) (imm : BitVec 12) (rs2 rs1 : BitVec 5)
    (w : Nat) (va pa : BitVec 64) :
    vmemWidth w → 1 ≤ w → w ≤ 8 →
    va = gprVal rs rs1 + sign_extend (m := 64) imm →
    dataAtS σi T (.Store .Data) va w pa → dok (paZ pa) w →
    ExecD (imgS σi) dok false (ctrlOkSW T satp0) rs pc wrStore (dpSt rs rs2 w)
      (.STORE (imm, .Regidx rs2, .Regidx rs1, w)) := by
  intro hvw hw1 hw8 hva hda hdok t ⟨hc, hW⟩ _ hag
  have hva' : va = gprVal t.regs rs1 + sign_extend (m := 64) imm := by
    rw [gprValAgree _ _ _ hag]; exact hva
  obtain ⟨s1, hpre, hfr, hc1⟩ :=
    wrPreS σi T satp0 hmode hasid hppn dok imm rs1 w va pa t hc hW hda hvw hw1 hw8 hva' hdok
  refine EvDExecuteSTORE (imgS σi) dok σi rfl imm rs2 rs1 w va pa .Sv39 _ t s1 hpre ?_
  refine ⟨rfl, fun h => AxSymMem.Dstate.noConfusion h, ?_, ?_⟩
  · unfold dpSt
    rw [gprValAgree _ _ _ hag]
  · exact ⟨⟨s1.regs, t.mem, t.dev⟩, hfr,
      ⟨hc1, AxDataX4.pmpWTlbFrame t s1.regs t.mem t.dev hW hfr⟩, rfl⟩

/-! # 2. `CertXT`: the tlb-framed `AxCert4.CertX` -/

/-- Rocq `CertXT`. -/
def CertXT (img : Image) (dok : Int → Nat → Prop) (kind : Dkind)
    (ctrlOk : RegFile → Prop) (rs : RegFile) (pc : BitVec 64) (ins : instruction)
    (ow : Cst → Option (BitVec 5 × BitVec 64)) (s0 : Cst) (PX : Cst → Prop) : Prop :=
  ∀ tpc : ExecSt, ctrlOk tpc.regs →
    tpc.regs .PC = pc →
    tpc.regs .nextPC = BitVec.addInt pc 4 →
    gprAgree tpc.regs rs →
    AxCert.Cert img dok kind (fun (_ : Cst) (_ : Sail.Error exception) (_ : ExecSt) => False)
      (fun s x t' => x = RETIRE_SUCCESS ∧ PX s ∧
        ∃ t0, tlbFrame tpc t0 ∧ ctrlOk t0.regs ∧ t' = wrOpt (ow s) t0) s0 (execute ins) tpc

/-- Rocq `ow_ld`. -/
def owLd (rd : BitVec 5) (u : Bool) (w : Nat) (s : Cst) : Option (BitVec 5 × BitVec 64) :=
  match s.csD with
  | .CLd vs => some (rd, ldRes u w vs)
  | _ => none

/-- Rocq `CertXT_load_S`. -/
theorem CertXTLoadS (σi : ExecSt) (T : PTree) (satp0 : BitVec 64)
    (hmode : _get_Satp64_Mode (Mk_Satp64 satp0) = 8#4)
    (hasid : zero_extend (m := 16) (satp_to_asid satp0) = 0#16)
    (hppn : BitVec.setWidth 44 (satp_to_ppn satp0) = T.base)
    (dok : Int → Nat → Prop)
    (rs : RegFile) (pc : BitVec 64) (imm : BitVec 12) (rs1 rd : BitVec 5) (u : Bool)
    (w : Nat) (va pa : BitVec 64) (r : Bool) :
    rd.toNat ≠ 0 → vmemWidth w → 1 ≤ w → w ≤ 8 →
    va = gprVal rs rs1 + sign_extend (m := 64) imm →
    dataAtS σi T (.Load .Data) va w pa → dok (paZ pa) w →
    CertXT (imgS σi) dok .DKLd (ctrlOkS T satp0) rs pc (.LOAD (imm, .Regidx rs1, .Regidx rd, u, w))
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

/-- Rocq `CertXT_store_S`: the certificate records the bytes AND the class
`wcls AxDataX.akPlain r` (= `WCrel` after an armed fence). -/
theorem CertXTStoreS (σi : ExecSt) (T : PTree) (satp0 : BitVec 64)
    (hmode : _get_Satp64_Mode (Mk_Satp64 satp0) = 8#4)
    (hasid : zero_extend (m := 16) (satp_to_asid satp0) = 0#16)
    (hppn : BitVec.setWidth 44 (satp_to_ppn satp0) = T.base)
    (dok : Int → Nat → Prop)
    (rs : RegFile) (pc : BitVec 64) (imm : BitVec 12) (rs2 rs1 : BitVec 5)
    (w : Nat) (va pa : BitVec 64) (r : Bool) :
    vmemWidth w → 1 ≤ w → w ≤ 8 →
    va = gprVal rs rs1 + sign_extend (m := 64) imm →
    dataAtS σi T (.Store .Data) va w pa → dok (paZ pa) w →
    CertXT (imgS σi) dok .DKSt (ctrlOkSW T satp0) rs pc (.STORE (imm, .Regidx rs2, .Regidx rs1, w))
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

end Weak
