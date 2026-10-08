/-
Weak: **the S-mode TRANSLATION FRONT at `CertWP`** (`translateAddr` → `translate` → TLB miss →
the demonic walk of `AxWalk3`), and its NON-VACUITY at the probe: the cold-TLB translation of the
probe's data VA (`nvVa`, a `Load Data`) with the three PTE reads demonic, pinned, reported at row
positions 0, 1, 2 (`nvTranslatePreset`), and the A/D-clear variant where the fused Svadu RMW
occurs at position 3 (`nvTranslateAd`).  Port of `AxSpineOk4.execATranslateAddrPtFront`.

Rocq: `iris/AxWalk6.v` @ xxvzwolszwmp.

## Deviations from Rocq

1. SPELLING as `AxWalk4` deviation 1; the front premises take `AxSpineOk4.
   execATranslateAddrPtFront`'s shapes (`BitVec.setWidth 44 (satp_to_ppn satp0) = root`,
   `zero_extend (m := 16) (satp_to_asid satp0) = 0#16`, `(va != sign_extend (m := 64)
   (extractLsb va 38 0)) = false`, the vpn `BitVec.setWidth 27 (extractLsb (extractLsb va 38 0)
   38 pagesize_bits)`); the TLB miss is `(t.regs .tlb)[tlb_hash 39 vpn]! = none`; the walk's
   `mxr`/`do_sum` are `(_get_Mstatus_MXR (t.regs .mstatus) == 1#1)` / `…SUM…` (Rocq `eq_vec … 'b"1"`).
2. TACTICS: Rocq's section Ltacs `p_step`/`p_go`/`rff`/`p_use` and the top-level `nseip6` are
   not ported; the proof uses `AxWalk3`'s kit (`AxWalk3.pRUse`, `pRLift`, `pRPure`, `pFactUse`,
   `ax_walk3_go`) plus the Lean-only `AxWalk6.pRAssertTrue` (lean-sail `assert` in the early-return
   monad).  `vm_compute` / `vr8` ↦ `decide +kernel`.
3. The Rocq `replace (eq_vec (_get_Mstatus_MXR …) 'b"1") with false` steps are the Lean-only
   `AxWalk6.nvMxrSum`; the identity-mapping fact of both posts is the Lean-only
   `AxWalk6.nvPaOfLeaf` (any leaf with the probe's PPN translates `nvVa` to itself).

**Rocq → Lean name map.**  `P_translateAddr_miss` `PTranslateAddrMiss`, `Qf_preset` `QfPreset`,
`nv_translate_preset` `nvTranslatePreset`, `Qf_ad` `QfAd`, `nv_translate_ad` `nvTranslateAd`.
None is in the duplicated-name table.  Lean-only (file-qualified): `AxWalk6.pRAssertTrue`,
`AxWalk6.nvMxrSum`, `AxWalk6.nvPaOfLeaf`.

**Dropped:** the Ltacs (deviation 2) and the `Print Assumptions` lines.  Rocq 5 definitions/
lemmas, Lean 5 (+ 3 Lean-only helpers).
-/
import Weak.AxWalk4

namespace Weak

open MachCSL
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D LeanRV64D.Functions

section front
variable (img : Image) (dok wok : Int → Nat → Prop) (kind : Dkind)
variable (pR pX : (Int → Nat → Prop) → Nat → Prop) (wpin xpin : Nat → Int → List (BitVec 8) → Prop)

local notation "CW" => CertWP img dok wok kind pR pX wpin xpin

/-- (Lean-only) `assert true` in the early-return monad. -/
theorem AxWalk6.pRAssertTrue {R X : Type}
    {QE : List (Nat × Wev) → Cst → Nat → Sail.Error exception → ExecSt → Prop}
    {Q : List (Nat × Wev) → Cst → Nat → Except (Sail.Error exception ⊕ R) X → ExecSt → Prop}
    {b0 : Bool} {msg : String} {f : Unit → SailME R X} {ws : List (Nat × Wev)} {s : Cst}
    {k : Nat} {t : ExecSt} (Hb0 : b0 = true) (H : CW QE Q ws s k (ExceptT.run (f ())) t) :
    CW QE Q ws s k (ExceptT.run (liftM (assert b0 msg) >>= f)) t := by
  subst Hb0
  exact H

/-- Rocq `P_translateAddr_miss`: the S-mode translation front over a TLB miss — the
`translate_TLB_miss` certificate `HTR` lifts to `translateAddr`. -/
theorem PTranslateAddrMiss (μ : ExecSt) (acc : MemoryAccessType mem_payload) (p : Privilege)
    (vpn : BitVec 27) (root : BitVec 44) (satp0 va : BitVec 64)
    (Qf : List (Nat × Wev) → Cst → Nat →
      Result (physaddr × page_based_mem_type × Unit) (ExceptionType × Unit) → ExecSt → Prop)
    (ws : List (Nat × Wev)) (s : Cst) (k : Nat) (t : ExecSt) :
    exec (effectivePrivilege acc (t.regs .mstatus) p) (tm μ t) = some (p, tm μ t) →
    exec (is_shadow_stack_access acc) (tm μ t) = some (false, tm μ t) →
    t.regs .cur_privilege = p →
    exec (translationMode p) (tm μ t) = some (.Sv39, tm μ t) →
    t.regs .satp = satp0 →
    BitVec.setWidth 44 (satp_to_ppn satp0) = root →
    zero_extend (m := 16) (satp_to_asid satp0) = 0#16 →
    (va != sign_extend (m := 64) (Sail.BitVec.extractLsb va 38 0)) = false →
    BitVec.setWidth 27 (Sail.BitVec.extractLsb (Sail.BitVec.extractLsb va 38 0) 38
      Functions.pagesize_bits) = vpn →
    (t.regs .tlb)[tlb_hash 39 vpn]! = none →
    CW (fun _ _ _ _ _ => False)
      (fun ws' s' k' r t' => match r with
        | .Ok (ppn, pbmt, ext) =>
            Qf ws' s' k' (.Ok (.Physaddr (zero_extend (m := 64) (ppn +++
              Sail.BitVec.extractLsb va (Functions.pagesize_bits - 1) 0)), pbmt, ext)) t'
        | .Err _ => False)
      ws s k
      (translate_TLB_miss 39 0#16 root vpn acc p ((_get_Mstatus_MXR (t.regs .mstatus)) == 1#1)
        ((_get_Mstatus_SUM (t.regs .mstatus)) == 1#1) ()) t →
    CW (fun _ _ _ _ _ => False) Qf ws s k (translateAddr (.Virtaddr va) acc) t := by
  intro heff hss hcp htm hsatp hppn hasid hcanon hvpn hmiss HTR
  have heffA := execAOfRfF _ (rfFEffectivePrivilege _ _ _) _ _ heff
  have hssA := execAOfRfF _ (rfFIsShadowStackAccess _) _ _ hss
  have htmA := execAOfRfF _ (rfFTranslationMode _) _ _ htm
  unfold translateAddr
  apply CertWPCatchEarlyReturn
  ax_walk3_go
  rw [hcp]
  refine AxWalk3.pRUse (μ := μ) (rfFEffectivePrivilege _ _ _) heffA ?_
  refine AxWalk3.pRUse (μ := μ) (rfFTranslationMode _) htmA ?_
  refine AxWalk3.pRUse (μ := μ) (rfFIsShadowStackAccess _) hssA ?_
  simp (config := { decide := true }) only [↓reduceIte]
  have hw : execA (satp_mode_width_forwards .Sv39) (tm μ t) = some (39, tm μ t) := rfl
  refine AxWalk3.pRUse (μ := μ) (rfFSatpModeWidthForwards _) hw ?_
  have hgs : execA (get_satp 39) (tm μ t) = some (satp0, tm μ t) := by
    unfold get_satp
    ax_spine4_run [hsatp]
    show some (BitVec.setWidth 64 satp0, _) = _
    rw [BitVec.setWidth_eq]
  refine AxWalk3.pRUse (μ := μ) (rfFGetSatp _) hgs ?_
  refine AxWalk6.pRAssertTrue _ _ _ _ _ _ _ _ (by decide) ?_
  simp only [bits_of_virtaddr, Int.reduceSub, Int.reduceToNat]
  rw [hcanon, if_neg Bool.false_ne_true]
  ax_walk3_go
  refine AxWalk3.pRLift (P := fun ws' s' k' r t' => match r with
    | .Ok (ppn, pbmt, ext) =>
        Qf ws' s' k' (.Ok (.Physaddr (zero_extend (m := 64) (ppn +++
          Sail.BitVec.extractLsb va (Functions.pagesize_bits - 1) 0)), pbmt, ext)) t'
    | .Err _ => False) ?_ ?_
  · have hlk := execLookupTLBMiss vpn 0#16 _ (tm μ t) rfl hmiss
    have hlkA := execAOfRfF _ (rfFLookupTLB _ _ _) _ _ hlk
    erw [hasid, hppn, hvpn]
    unfold translate
    refine AxWalk3.pFactUse (μ := μ) (rfFLookupTLB _ _ _) hlkA ?_
    exact HTR
  · intro ws' s' k' x t' h
    cases x with
    | Err e => exact h.elim
    | Ok v =>
      obtain ⟨ppn, pbmt, ext⟩ := v
      exact AxWalk3.pRPure h

end front

/-! # 2. NON-VACUITY: the cold-TLB translation of the probe's data VA -/

/-- Rocq `Qf_preset`. -/
def QfPreset (ws : List (Nat × Wev)) (_s : Cst) (k : Nat)
    (x : Result (physaddr × page_based_mem_type × Unit) (ExceptionType × Unit)) (t : ExecSt) :
    Prop :=
  ∃ vs2 vs1 vs0 : List (BitVec 8),
    ws = [(0, .WRd (paZ wa2) vs2), (1, .WRd (paZ wa1) vs1), (2, .WRd (paZ wa0) vs0)] ∧
    rrv 8 vs2 = pP2 ∧ rrv 8 vs1 = pP1 ∧ rrv 8 vs0 = dW ∧ k = 3 ∧
    x = .Ok (.Physaddr nvVa, .PBMT_PMA, init_ext_ptw) ∧
    t = AxWalk3.tlbFill dvpn pP2 pP1 nvST 0 dW

/-- (Lean-only) the probe's MXR / SUM bits are clear. -/
theorem AxWalk6.nvMxrSum : (_get_Mstatus_MXR (nvST.regs .mstatus) == 1#1) = false ∧
    (_get_Mstatus_SUM (nvST.regs .mstatus) == 1#1) = false := ⟨by decide +kernel, by decide +kernel⟩

/-- (Lean-only) the translated address of a leaf with the probe's PPN is the probe's VA. -/
theorem AxWalk6.nvPaOfLeaf (q : BitVec 64) (hq : ppn0 q = ppn0 dW) :
    (.Ok (.Physaddr (zero_extend (m := 64) (ppn0 q +++
      Sail.BitVec.extractLsb nvVa (Functions.pagesize_bits - 1) 0)), .PBMT_PMA, ()) :
      Result (physaddr × page_based_mem_type × Unit) (ExceptionType × Unit)) =
      .Ok (.Physaddr nvVa, .PBMT_PMA, init_ext_ptw) := by
  have hpa : zero_extend (m := 64) (ppn0 dW +++
      Sail.BitVec.extractLsb nvVa (Functions.pagesize_bits - 1) 0) = nvVa := by decide +kernel
  rw [hq, hpa]

/-- Rocq `nv_translate_preset`. -/
theorem nvTranslatePreset :
    CertWP (imgOf nvST) (fun _ _ => False) nvWok .DKLd (posR Gnr 0) (posX Gnr 0) (nvPin (Eq dW))
      (fun _ _ _ => True) (fun _ _ _ _ _ => False) QfPreset [] ⟨.CPend, .BInf, false⟩ 0
      (translateAddr (.Virtaddr nvVa) (.Load .Data)) nvST := by
  obtain ⟨Hpriv, -, -, -, -, -, -, Hms, -, -, Hsatp, -⟩ := nvCtrl
  obtain ⟨HMPRV, HSXL, -⟩ := Hms
  refine PTranslateAddrMiss _ _ _ _ _ _ _ _ nvST (.Load .Data) .Supervisor dvpn nvSRoot nvSSatp nvVa
    _ _ _ _ nvST (execEffectivePrivilegeLoadS _ _ HMPRV) (execIsShadowStackLoad _) Hpriv
    (execTranslationModeSSv39 nvSSatp (tm nvST nvST) HSXL Hsatp nvSSatpMode) Hsatp rfl nvSSatpAsid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  rw [AxWalk6.nvMxrSum.1, AxWalk6.nvMxrSum.2]
  refine CertWPMono _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (fun _ _ _ _ _ h => h) ?_ nvWalkPreset
  rintro ws s k x t ⟨vs2, vs1, vs0, rfl, h2, h1, h0, rfl, rfl, rfl⟩
  exact ⟨vs2, vs1, vs0, rfl, h2, h1, h0, rfl, AxWalk6.nvPaOfLeaf _ rfl, rfl⟩

/-- Rocq `Qf_ad`: the A/D-clear variant — the fused Svadu RMW at row position 3 on the `dWc`
branch; the translation is the probe's identity mapping either way. -/
def QfAd (ws : List (Nat × Wev)) (_s : Cst) (k : Nat)
    (x : Result (physaddr × page_based_mem_type × Unit) (ExceptionType × Unit)) (_t : ExecSt) :
    Prop :=
  x = .Ok (.Physaddr nvVa, .PBMT_PMA, init_ext_ptw) ∧
  ((k = 3 ∧ ws.map Prod.fst = [0, 1, 2]) ∨
   (k = 4 ∧ ws.map Prod.fst = [0, 1, 2, 3, 3] ∧
     ∃ rvs wvs, ws[4]? = some (3, .WRmw (paZ wa0) rvs wvs) ∧ nvP0 (rrv 8 rvs)))

/-- Rocq `nv_translate_ad`. -/
theorem nvTranslateAd :
    CertWP (imgOf nvST) (fun _ _ => False) nvWok .DKLd (posR Gad 0) (posX Gad 0) (nvPin nvP0)
      (fun _ _ vs => rrv 8 vs = dWc)
      (fun _ _ _ _ _ => False) QfAd [] ⟨.CPend, .BInf, false⟩ 0
      (translateAddr (.Virtaddr nvVa) (.Load .Data)) nvST := by
  obtain ⟨Hpriv, -, -, -, -, -, -, Hms, -, -, Hsatp, -⟩ := nvCtrl
  obtain ⟨HMPRV, HSXL, -⟩ := Hms
  refine PTranslateAddrMiss _ _ _ _ _ _ _ _ nvST (.Load .Data) .Supervisor dvpn nvSRoot nvSSatp nvVa
    _ _ _ _ nvST (execEffectivePrivilegeLoadS _ _ HMPRV) (execIsShadowStackLoad _) Hpriv
    (execTranslationModeSSv39 nvSSatp (tm nvST nvST) HSXL Hsatp nvSSatpMode) Hsatp rfl nvSSatpAsid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  rw [AxWalk6.nvMxrSum.1, AxWalk6.nvMxrSum.2]
  refine CertWPMono _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (fun _ _ _ _ _ h => h) ?_ nvWalkAd
  rintro ws s k x t ⟨⟨q0, Hq0, rfl⟩, Hrest⟩
  refine ⟨AxWalk6.nvPaOfLeaf _ ?_, Hrest⟩
  rcases Hq0 with rfl | rfl <;> decide +kernel

end Weak

