/-
MachCSL: the access information and the effective-address transform of a
kernel access in supervisor mode at either tier (`swp_default_access_info_S`,
`swp_transform_effective_address_S`; sail-riscv 0.16 splits the old
transform in two: `default_access_info` computes the effective privilege and
the pointer-masking length once, `transform_effective_address` takes them).
The translation itself is `MachCSL.TranslateAddr` (whose header describes
it).
-/
import MachCSL.TranslateAddr
import MachCSL.WpStagesM

namespace MachCSL

open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode Std
open Sail Sail.ArchSem
open LeanRV64D LeanRV64D.Functions

variable {GF : BundledGFunctors.{0}} [MachGS GF]

/-! ## Pointer masking: none -/

set_option maxHeartbeats 4000000 in
/-- The access information of a kernel access in supervisor mode (at either
tier; only the physical facts matter): `MPRV = 0`, so the effective privilege
is the current one, `Supervisor`; no pointer masking (`menvcfg.PMM = 0`;
`mstatus.MXR = 0`, so masking applies to data accesses and reads that mode);
not a guest access.  (Since sail-riscv 0.16 the effective privilege and the
pointer-masking length are computed once, by `default_access_info`, and handed
to `transform_effective_address` and `translateAddr`.) -/
theorem swp_default_access_info_S (cpu : CPU) (dq : DFrac) (c : MConf) (sie : Bool)
    (hok : SConfPhys (GF := GF) c sie)
    (acc : MemoryAccessType mem_payload) (hacc : kernelAccess acc)
    (Φ : AccessInfo → IProp GF) :
    confCells cpu dq Privilege.Supervisor c ∗
    ▷ (confCells cpu dq Privilege.Supervisor c -∗
        Φ { eff_privilege := Privilege.Supervisor, pmlen := 0, as_guest := false })
    ⊢ swp cpu (default_access_info acc) Φ := by
  iintro ⟨HmConf, HΦ⟩
  obtain ⟨hpmp, hms, hpmm, hlpe⟩ := hok
  obtain ⟨hSIE, hMPRV, hSXL, hMXR, hTSR, hTVM, hFS, hXS, hVS, hSD, hMPP⟩ := hms
  conf_cases HmConf
  unfold default_access_info
  rcases hacc with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    swp_run 120
    conf_intro HmConf
    iapply HΦ $$ HmConf

set_option maxHeartbeats 4000000 in
/-- The effective-address transform of a kernel access at either tier (the
access information `default_access_info` computes there,
`swp_default_access_info_S`): pointer masking is off, the address is
untouched. -/
theorem swp_transform_effective_address_S (cpu : CPU) (dq : DFrac) (c : MConf) (sie : Bool)
    (tier : KTier) (root : BitVec 44) (hok : SConfAt (GF := GF) tier c root sie)
    (va : BitVec 64) (Φ : virtaddr → IProp GF) :
    confCells cpu dq Privilege.Supervisor c ∗
    ▷ (confCells cpu dq Privilege.Supervisor c -∗ Φ (virtaddr.Virtaddr va))
    ⊢ swp cpu (transform_effective_address (virtaddr.Virtaddr va)
        { eff_privilege := Privilege.Supervisor, pmlen := 0, as_guest := false }) Φ := by
  iintro ⟨HmConf, HΦ⟩
  unfold transform_effective_address
  swp_run 20
  iapply swp_bind
  iapply (swp_translationMode_tier cpu dq c sie tier root hok)
  iframe HmConf
  inext
  iintro HmConf
  cases tier
  all_goals
    simp only [satpModeOf]
    swp_run 20
    reduce_closed_widths
    simp only [pm_transform_PA, pm_transform_VA, zero_extend, sign_extend, Sail.BitVec.zeroExtend,
      Sail.BitVec.signExtend, Sail.BitVec.extractLsb, BitVec.extractLsb, Functions.xlen, Int.reduceSub,
      Int.reduceToNat, Nat.reduceAdd, Nat.sub_zero, Int.cast_ofNat_Int]
    reduce_closed_widths
    try simp only [BitVec.zeroExtend, MachCSL.setWidth_extract64', MachCSL.signExtend_extract64']
    iapply HΦ $$ HmConf

end MachCSL
