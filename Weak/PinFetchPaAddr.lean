/-
Weak: **W9a (B) B5 r2 part (B) — HEADLINE: Sail's `translateAddr` of a kernel-text fetch returns
PA = VA under `tvB`** (plan rev 52 §D Q-B5-FETCH (r2-a), `PROGRESS-r2.md`).  Lean-only.

`tvTranslateAddrFetch`: for a fetch at `pc < 2^38` whose vpn is the configuration's, with the walk's
pages in RAM and the root below 2^31, every path of `translateAddr (Virtaddr pc) InstructionFetch`
along which `satp` reads `kSatp b`, the TLB reads `tlbIdOk`, and the walk's PTE reads answer the
`kptTextAt` slot values (`tvB`) ends, if `Ok (pa, _, _)`, with `pa = Physaddr pc`: under Machine
or a Bare mode by the Bare arm, under Sv39 by the TLB hit (the filter) or the miss (the walk's
identity leaf, `PinFetchPaWalk`).  Only the PA claim (`fetchOkR2` (i)); "no fault" (ii) is not here.
Spec: Sail `Vmem.lean:437-590`, `VmemTlb.lean:309-345`; the privileged spec's Sv39 (PA = PPN ++
offset).  FAITHFUL.  Every helper is `Weak.PinFetchPa.*`.
-/
import Weak.PinFetchPaTlb

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open Sail Sail.ConcurrencyInterfaceV1 LeanRV64D LeanRV64D.Functions
open Sail.ArchSem (FreeM)

namespace PinFetchPa
open SailCycleOrderK PinFetchPaFp

/-- `translate` with its ASID, root and vpn given up to equality. -/
theorem tvTranslateEq (c : TCfg) (hr : c.ram) (asid : BitVec 16) (base : BitVec 44) (vpn : BitVec 27)
    (ha : asid = 0#16) (hb : base = c.b) (hv : vpn = c.vpn) (acc : MemoryAccessType mem_payload)
    (priv : Privilege) (mxr sum : Bool) (u : Unit) :
    tvB c (trPost c) (translate 39 asid base vpn acc priv mxr sum u) := by
  subst ha hb hv
  exact tvTranslate c hr acc priv mxr sum u

/-- The kernel `satp`'s Sv39 mode field. -/
theorem kSatpMode64 (b : BitVec 44) : _get_Satp64_Mode (Mk_Satp64 (kSatp b)) = 8#4 := by
  simp only [_get_Satp64_Mode, Mk_Satp64, kSatp, Sail.BitVec.extractLsb]
  generalize b = x
  bv_decide

/-- Read as an RV32 `satp`, the kernel `satp` of a root below 2^31 is Bare. -/
theorem kSatpMode32 (b : BitVec 44) (hb : b.toNat < 2 ^ 31) :
    (0#3 +++ _get_Satp32_Mode (Mk_Satp32 (Sail.BitVec.extractLsb (kSatp b) 31 0))) = 0#4 := by
  have hb' : b < 0x80000000#44 := by rw [BitVec.lt_def]; simpa using hb
  simp only [_get_Satp32_Mode, Mk_Satp32, kSatp, Sail.BitVec.extractLsb]
  revert hb'
  generalize b = x
  bv_decide

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 100000 in
/-- `translationMode` under the kernel `satp`: Bare or Sv39. -/
theorem tvTranslationMode (c : TCfg) (hb : c.b.toNat < 2 ^ 31) (priv : Privilege) :
    tvB c (fun m => m = .Bare ∨ m = .Sv39) (translationMode priv) := by
  unfold translationMode
  split
  · exact Or.inl rfl
  · refine tvXfT _ _ (by xf_walk) (fun arch => ?_)
    cases arch with
    | RV64 =>
      simp only [bind_assoc]
      refine tvXfT _ _ (by xf_walk) (fun _ => ?_)
      refine tvReadReg _ _ (fun v hv => ?_)
      have hv' := tvRkSatp hv
      subst hv'
      simp only [pure_bind, kSatpMode64]
      exact Or.inr rfl
    | RV32 =>
      simp only [bind_assoc]
      refine tvReadReg _ _ (fun v hv => ?_)
      have hv' := tvRkSatp hv
      subst hv'
      simp only [pure_bind, kSatpMode32 c.b hb]
      exact Or.inl rfl
    | RV128 =>
      exact tvXfBind (fun _ => False) _ _ _ (by xf_walk) (fun _ h => h.elim)

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 100000 in
/-- **r2 (B), THE HEADLINE: A KERNEL-TEXT FETCH TRANSLATES TO ITS OWN ADDRESS.** -/
theorem tvTranslateAddrFetch (c : TCfg) (hr : c.ram) (hb : c.b.toNat < 2 ^ 31) (pc : BitVec 64)
    (hpc : pc.toNat < 2 ^ 38) (hv : c.vpn = vpnOf pc) :
    tvB c (fun r => ∀ pa pb e, r = .Ok (pa, pb, e) → pa = .Physaddr pc)
      (translateAddr (.Virtaddr pc) (.InstructionFetch ())) := by
  unfold translateAddr
  simp only [SailME.run, PreSail.PreSailME.run, ExceptT.run_bind, run_liftM, bind_assoc, pure_bind]
  refine tvReadReg _ _ (fun _ _ => ?_)
  refine tvReadReg _ _ (fun _ _ => ?_)
  refine tvXfT _ _ (xfEffectivePrivilege _ _ _) (fun priv => ?_)
  refine tvBind _ _ _ _ (tvTranslationMode c hb priv) (fun mode hm => ?_)
  simp only [is_shadow_stack_access, pure_bind, Bool.false_eq_true, ↓reduceIte]
  rcases hm with rfl | rfl
  · simp (config := { decide := true }) only [↓reduceIte, ExceptT.run_pure, pure_bind]
    intro pa pb e h
    injection h with h
    injection h with h
    subst h
    simp only [bits_of_virtaddr, zext64_self]
  · simp (config := { decide := true }) only [↓reduceIte, ExceptT.run_bind, run_liftM, bind_assoc,
      pure_bind, satp_mode_width_forwards, get_satp]
    reduce_closed_widths
    refine tvXfT _ _ (by xf_walk) (fun _ => ?_)
    refine tvReadReg _ _ (fun v hsv => ?_)
    have hsv' := tvRkSatp hsv
    subst hsv'
    refine tvXfT _ _ (by xf_walk) (fun _ => ?_)
    have hpc' : pc < 0x4000000000#64 := by rw [BitVec.lt_def]; simpa using hpc
    have hcan : (bits_of_virtaddr (virtaddr.Virtaddr pc) !=
        sign_extend (m := 64) (Sail.BitVec.extractLsb (bits_of_virtaddr (virtaddr.Virtaddr pc)) 38 0)) = false := by
      simp only [bits_of_virtaddr, sign_extend, Sail.BitVec.signExtend, Sail.BitVec.extractLsb]
      revert hpc'
      generalize pc = x
      bv_decide
    simp only [hcan, Bool.false_eq_true, ↓reduceIte, ExceptT.run_bind, run_liftM, bind_assoc, pure_bind]
    refine tvReadReg _ _ (fun _ _ => ?_)
    refine tvReadReg _ _ (fun _ _ => ?_)
    have hasid : zero_extend (m := 16) (satp_to_asid (BitVec.setWidth 64 (kSatp c.b))) = 0#16 := by
      simp only [satp_to_asid, _get_Satp64_Asid, Mk_Satp64, kSatp, Sail.BitVec.extractLsb,
        Sail.BitVec.length, zero_extend, Sail.BitVec.zeroExtend]
      generalize c.b = x
      bv_decide
    have hbase : BitVec.setWidth 44 (satp_to_ppn (BitVec.setWidth 64 (kSatp c.b))) = c.b := by
      simp only [satp_to_ppn, _get_Satp64_PPN, Mk_Satp64, kSatp, Sail.BitVec.extractLsb, Sail.BitVec.length]
      generalize c.b = x
      bv_decide
    have hvpn : BitVec.setWidth 27 (Sail.BitVec.extractLsb (Sail.BitVec.extractLsb
        (bits_of_virtaddr (virtaddr.Virtaddr pc)) 38 0) 38 Functions.pagesize_bits) = c.vpn := by
      rw [hv]
      simp only [vpnOf, bits_of_virtaddr, Sail.BitVec.extractLsb, Functions.pagesize_bits]
      generalize pc = x
      bv_decide
    refine tvBind _ _ _ _ (tvTranslateEq c hr _ _ _ hasid hbase hvpn _ priv _ _ _) (fun r ht => ?_)
    match r with
    | .Err _ =>
      simp only [ExceptT.run_bind, run_liftM, bind_assoc, pure_bind]
      refine tvXfT _ _ (xfTranslationException _ _) (fun _ => ?_)
      intro pa pb e h; cases h
    | .Ok (ppn, pbmt, ex) =>
      have hp := ht _ _ _ rfl
      subst hp
      intro pa pb e h
      injection h with h
      injection h with h
      subst h
      congr 1
      rw [hv]
      simp only [idPpn, vpnOf, bits_of_virtaddr, Sail.BitVec.extractLsb, zero_extend,
        Sail.BitVec.zeroExtend]
      revert hpc'
      generalize pc = x
      bv_decide

end PinFetchPa
end Weak
