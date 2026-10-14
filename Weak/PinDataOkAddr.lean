/-
Weak: **`dataOkR` (3i) — `translateAddr` of a kernel data access under `dkB`**: supervisor mode, no
`MPRV`, an RV64 supervisor, the kernel `satp` (Sv39) and a canonical address give
`Ok (Physaddr (ppn ++ offset), PBMT_PMA, _)` — no page fault (`PROGRESS-dataOk.md`).  Mirrors
`Weak/PinFetchPaAddr.lean`.  Lean-only.  Every helper is `Weak.PinDataOk.*`.
-/
import Weak.PinDataOkTlb
import Weak.PinFetchPaAddr

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open Sail Sail.ConcurrencyInterfaceV1 LeanRV64D LeanRV64D.Functions
open Sail.ArchSem (FreeM)

namespace PinDataOk
open SailCycleOrderK PinFetchPaFp

variable {c : DCfg}

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 100000 in
/-- `translationMode` in supervisor mode under the filter: Sv39. -/
theorem dkTranslationModeS : dkB c (fun m => m = .Sv39) (translationMode .Supervisor) := by
  unfold translationMode architecture
  simp only [bind_assoc, pure_bind]
  have hne : (Privilege.Supervisor == Privilege.Machine) = false := rfl
  simp only [hne, Bool.false_eq_true, ↓reduceIte]
  refine dkReadReg _ _ (fun v hv => ?_)
  have hm := dGMstatus hv
  rw [hm.2]
  have harch : architecture_bits_backwards 2#2 = pure .RV64 := rfl
  simp only [harch, pure_bind, bind_assoc]
  refine dkXfT _ _ (by xf_walk) (fun _ => ?_)
  refine dkReadReg _ _ (fun s hs => ?_)
  have hs' := dGSatp hs
  subst hs'
  simp only [pure_bind, PinFetchPa.kSatpMode64]
  rfl

/-- The physical address the leaf's page gives `va`. -/
def dPa (c : DCfg) (va : BitVec 64) : BitVec 64 :=
  zero_extend (m := 64) (c.ppn +++ Sail.BitVec.extractLsb va 11 0)

/-- `translate` with its ASID, root and vpn given up to equality. -/
theorem dkTranslateEq (c : DCfg) (hr : c.ram) (asid : BitVec 16) (base : BitVec 44) (vpn : BitVec 27)
    (ha : asid = 0#16) (hb : base = c.b) (hv : vpn = c.vpn) (acc : MemoryAccessType mem_payload)
    (hk : dAccKind acc c.perm) (mxr sum : Bool) (u : Unit) :
    dkB c (trPostD c) (translate 39 asid base vpn acc .Supervisor mxr sum u) := by
  subst ha hb hv
  exact dkTranslate c hr acc hk mxr sum u

/-- No `MPRV`: a data access's effective privilege is the current one. -/
theorem effPrivData (acc : MemoryAccessType mem_payload) (perm : KPerm) (hk : dAccKind acc perm)
    (m : BitVec 64) (hm : dMstatusOk m) (p : Privilege) : effectivePrivilege acc m p = pure p := by
  unfold effectivePrivilege
  rw [hm.1]
  rcases hk with rfl | ⟨rfl, -⟩ <;> rfl

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 100000 in
/-- **(3) THE DATA TRANSLATION: NO PAGE FAULT.** -/
theorem dkTranslateAddrData (c : DCfg) (hr : c.ram) (va : BitVec 64) (hva : va.toNat < 2 ^ 38)
    (hv : c.vpn = vpnOf va) (acc : MemoryAccessType mem_payload) (hk : dAccKind acc c.perm) :
    dkB c (fun r => ∃ e, r = .Ok (.Physaddr (dPa c va), .PBMT_PMA, e))
      (translateAddr (.Virtaddr va) acc) := by
  unfold translateAddr
  simp only [SailME.run, PreSail.PreSailME.run, ExceptT.run_bind, run_liftM, bind_assoc, pure_bind]
  refine dkReadReg _ _ (fun m hm => ?_)
  refine dkReadReg _ _ (fun p hp => ?_)
  have hp' := dGPriv hp
  subst hp'
  rw [effPrivData acc c.perm hk m (dGMstatus hm), pure_bind]
  refine dkBind _ _ _ _ dkTranslationModeS (fun mode hmode => ?_)
  subst hmode
  have hss : is_shadow_stack_access acc = pure false := by rcases hk with rfl | ⟨rfl, -⟩ <;> rfl
  simp (config := { decide := true }) only [hss, pure_bind, Bool.false_eq_true, ↓reduceIte,
    ExceptT.run_bind, run_liftM, bind_assoc, satp_mode_width_forwards, get_satp]
  reduce_closed_widths
  refine dkXfT _ _ (by xf_walk) (fun _ => ?_)
  refine dkReadReg _ _ (fun v hsv => ?_)
  have hsv' := dGSatp hsv
  subst hsv'
  refine dkXfT _ _ (by xf_walk) (fun _ => ?_)
  have hva' : va < 0x4000000000#64 := by rw [BitVec.lt_def]; simpa using hva
  have hcan : (bits_of_virtaddr (virtaddr.Virtaddr va) !=
      sign_extend (m := 64) (Sail.BitVec.extractLsb (bits_of_virtaddr (virtaddr.Virtaddr va)) 38 0)) = false := by
    simp only [bits_of_virtaddr, sign_extend, Sail.BitVec.signExtend, Sail.BitVec.extractLsb]
    revert hva'
    generalize va = x
    bv_decide
  simp only [hcan, Bool.false_eq_true, ↓reduceIte, ExceptT.run_bind, run_liftM, bind_assoc, pure_bind]
  refine dkReadReg _ _ (fun _ _ => ?_)
  refine dkReadReg _ _ (fun _ _ => ?_)
  have hasid : zero_extend (m := 16) (satp_to_asid (BitVec.setWidth 64 (PinFetchPa.kSatp c.b))) = 0#16 := by
    simp only [satp_to_asid, _get_Satp64_Asid, Mk_Satp64, PinFetchPa.kSatp, Sail.BitVec.extractLsb,
      Sail.BitVec.length, zero_extend, Sail.BitVec.zeroExtend]
    generalize c.b = x
    bv_decide
  have hbase : BitVec.setWidth 44 (satp_to_ppn (BitVec.setWidth 64 (PinFetchPa.kSatp c.b))) = c.b := by
    simp only [satp_to_ppn, _get_Satp64_PPN, Mk_Satp64, PinFetchPa.kSatp, Sail.BitVec.extractLsb,
      Sail.BitVec.length]
    generalize c.b = x
    bv_decide
  have hvpn : BitVec.setWidth 27 (Sail.BitVec.extractLsb (Sail.BitVec.extractLsb
      (bits_of_virtaddr (virtaddr.Virtaddr va)) 38 0) 38 Functions.pagesize_bits) = c.vpn := by
    rw [hv]
    simp only [vpnOf, bits_of_virtaddr, Sail.BitVec.extractLsb, Functions.pagesize_bits]
    generalize va = x
    bv_decide
  refine dkBind _ _ _ _ (dkTranslateEq c hr _ _ _ hasid hbase hvpn acc hk _ _ _) (fun r ht => ?_)
  obtain ⟨e, rfl⟩ := ht
  exact ⟨e, rfl⟩

end PinDataOk
end Weak
