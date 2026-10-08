/-
Weak: **the spinlock plan, PHASE 5 item (4), part 8** — THE UNMAPPED ARM of the arbitrary-VA
chain, symbolically: the Sv39 walk meets an INVALID PTE at level 2, 1 or 0.

Rocq: `iris/AxSpinVA8.v` @ xxvzwolszwmp.

## What this file proves

`chainFaultUnmapped2/1/0`: at every state `t` of the S-mode regime `ctrlOkS` with PC = a
canonical, 4-aligned VA `va` whose TLB slot does not hit, whose walk in the image tree reads valid
pointer words down to an INVALID word at level ℓ (all slots image bytes of `σi`), with
fetch-page-fault delegated to S and stvec direct at a fetchable 4-aligned kernel VA `sv`, the
label chain from the boundary is (both ticks, every pin answer)
    `[slot2]               ++ stvec chain`   (ℓ = 2)
    `[slot2, slot1]        ++ stvec chain`   (ℓ = 1)
    `[slot2, slot1, slot0] ++ stvec chain`   (ℓ = 0)
where the stvec chain is `AxSpinVA4`'s `walkKeys T tlb (svpnOf sv) p2 p1 ++ [.ENf (paZ pa(sv), 4)]`
— the walker reads up to the invalid slot, then NOTHING (page fault, register-only trap; the
TLB is not filled), then the stvec fetch.
PIECES: `invFalse` (the valid-non-leaf test fails on an invalid word), `FCheckLeafInv`,
`FRecWalkInv0/1/2`, `FRecWalkDown1/2`, `FTranslateTLBMissErr`, `FTranslateAddrFrontInv`
(translation `Err` ⇒ `E_Fetch_Page_Fault`), `unmappedFront` (the shared prefix up to the walk).
Premise kept explicit (as Rocq): the TLB does not hit `svpnOf va` (`tlbHitb … = false`).

## Deviations from Rocq

1. O2 STAGE C (`AxSpinVA4` deviation 1, `AxSpinVA7` deviation 1).  The stvec fetch is no chain
   key; the Rocq-named theorems end at `.ENf (paZ spa, 4)` and take
   `imgBytes (imgOf σi) (paZ spa) 4 = none` (the form `chainFetchMapped4` proves).  The IN-IMAGE
   case (stvec in kernel text, the usual one, where Rocq's fetch-address verdict
   `ERd (false, uint spa, 4)` has no Lean counterpart: the fetch is the pinned admin step
   `FEC.fcIf` that continues into the handler's first instruction) is served by the Lean-only
   step theorems `AxSpinVA8.faultUnmapped0Step/1Step/2Step`: the faulting step emits exactly the
   slot keys up to the invalid word, and every post-trap boundary is a regime state with PC =
   `stvecBase stvec` and the TLB unchanged, so ANY nonempty chain fact `Ks` for the next `n`
   steps there (e.g. via `AxSpinVA4.fetchMappedImg4`) lifts to `slots ++ Ks` for `n + 1` steps
   from `t`.  The Rocq-named theorems are corollaries (n = 1, `chainFetchMapped4`).
2. `inv_false` is about Rocq's `and_boolM` (no Lean combinator: the Lean walk's test is
   `(not (← pte_is_invalid …)) && (pte_is_non_leaf … && level >b 0)` in a `do` block).
   `invFalse` states the same fact for the Lean shape: the bind of `pte_is_invalid` into the
   pure test answers `false`, unchanged state.  The proofs use the `pte_is_invalid` fact
   directly (as `AxSpinVA3`'s walk).
3. THE WALK is Lean's self-recursive `pt_walk` (no `_rec_pt_walk`, no `Acc` argument;
   `AxSpinVA3` deviation 4): `FRecWalkInvℓ` / `FRecWalkDownℓ` are about
   `pt_walk 39 vpn acc p mxr do_sum base ℓ g ()`, and the `FRecWalkDownℓ` continuations are
   `∀ g'` (Rocq `∀ g' wf'`).  The slot address `u_pte_addr base (subrange vpn hi lo)` ↦
   `uPteAddr base (Sail.BitVec.extractLsb vpn hi lo)`.  `FCheckLeafInv` does not take the
   section's `μ` (Lean includes a section variable only when the statement mentions it; the
   register-only fact is used at `tm t t`).
4. SPELLING (as `AxSpinVA7` deviation 2): `mstate` ↦ `ExecSt`, `register_lookup r t.(sregs)` ↦
   `t.regs .r`, `set_reg t (R_bool minstret_increment) b` ↦ `t.setReg .minstret_increment b`,
   `img_of` ↦ `imgOf`, `pt_base T` ↦ `T.base`, `svpn_of` ↦ `WeakKpt.svpnOf`, `pt_slot_mem` ↦
   `WeakWalkEff.ptSlotMem`, `pt_addr2/1/0` ↦ `AxPtProt.ptAddr2/1/0`, `pte_valid` / `pte_ptr` /
   `pte_invalid` ↦ `pteValid` / `ptePtr` / `pteInvalid`, `pte_rd_ok` ↦ `pteRdOk`, `tt` ↦ `()`,
   `mword_of_int 0 : mword 16` ↦ `0#16`, `addr_is_ram spa ∧ addr_is_ram (pa_add spa 3)` ↦
   `inRam spa 4`, `uint` ↦ `paZ`, `WpIntrCore.stvec_base` ↦ `stvecBase`, `stvec_direct` ↦
   `AxIntr.stvecDirect`, the canonical test ↦
   `(va != sign_extend (m := 64) (Sail.BitVec.extractLsb va 38 0))`; the theorems' `let vpn` /
   `let sv` are inlined; Rocq `l1 ++ l2 ++ l3` (right-nested) is written
   `l1 ++ (l2 ++ l3)`.  The satp hypotheses `Hmode Hasid Hppn` take `AxSpineOk4` deviation 7's
   shapes and are explicit arguments (after `σi T satp0`).
5. `FTranslateAddrFrontInv` takes the front premises at `tm μ t` as `FTranslateAddrFront`
   (SC `exec` facts; `get_satp` / width / assert steps inlined); `unmappedFront` goes through
   `AxSpinVA7.FFetch4Err` (the Lean `fetch`'s alignment tests, `AxSpinVA4` deviation 5).
6. TACTICS: Rocq `nseip8` / `k_step` / `k_go` / `post_step` ↦ the `AxSpinVA3` / `AxSpinVA4`
   kit (`ax_spin_va3_go`) and `AxSpinVA7.faultPostFacts` inline.

**Rocq → Lean name map.**  `inv_false` `invFalse`, `F_check_leaf_inv` `FCheckLeafInv`,
`F_rec_walk_inv0/1/2` `FRecWalkInv0/1/2`, `F_rec_walk_down1/2` `FRecWalkDown1/2`,
`F_translate_TLB_miss_err` `FTranslateTLBMissErr`, `F_translateAddr_front_inv`
`FTranslateAddrFrontInv`, `app_snoc_neq` `appSnocNeq`, `unmapped_front` `unmappedFront`,
`chain_fault_unmapped0/1/2` `chainFaultUnmapped0/1/2`.  None is in the duplicated-name table.
Lean-only (file-qualified): `AxSpinVA8.faultUnmapped0Step`, `AxSpinVA8.faultUnmapped1Step`,
`AxSpinVA8.faultUnmapped2Step`.

**Dropped:** none (Rocq 14 lemmas/theorems; Lean the same 14, + 3 Lean-only).  **Not ported:**
the Ltacs (deviation 6) and the `Print Assumptions` lines (the lint's axiom check covers them).
-/
import Weak.AxSpinVA7

namespace Weak

open MachCSL
open Sail Sail.ConcurrencyInterfaceV1
open Sail.ArchSem (FreeM)
open LeanRV64D LeanRV64D.Functions

/-! # 1. The walk stops at an invalid word -/

/-- Rocq `inv_false` (deviation 2): the walk's valid-non-leaf test fails on an invalid word. -/
theorem invFalse (w : BitVec 64) (lv : Nat) (s0 : ExecSt) :
    pteInvalid w →
    execA (pte_is_invalid (Mk_PTE_Flags (Sail.BitVec.extractLsb w 7 0)) (ext_bits_of_PTE w) >>=
      fun b => (pure (!b && (pte_is_non_leaf (Mk_PTE_Flags (Sail.BitVec.extractLsb w 7 0)) &&
        decide (lv > 0))) : SailM Bool)) s0 = some (false, s0) := by
  intro Hi
  rw [execABindSome _ _ _ _ _ (execAOfRfF _ (rfFPteIsInvalid _ _) s0 _ (Hi s0))]
  rfl

section walkInv
variable (img : Image) (μ : ExecSt) (vpn : BitVec 27) (acc : MemoryAccessType mem_payload)
  (p : Privilege) (mxr do_sum : Bool)

local notation "FC" => FEC img

/-- Rocq `F_check_leaf_inv`: the invalid word's leaf check is register-only and fails. -/
theorem FCheckLeafInv (q : BitVec 64) (pa : physaddr) (lvl : Nat)
    (Q : List ekey → Result (BitVec 44 × page_based_mem_type × Unit) (PTW_Error × Unit) →
      ExecSt → Prop)
    (Ks : List ekey) (t : ExecSt) :
    pteInvalid q → Q Ks (.Err (.PTW_Invalid_PTE (), ())) t →
    FC (fun _ _ _ => False) Q Ks (check_leaf_pte 39 vpn acc p mxr do_sum q pa lvl ()) t := by
  intro Hinv HQ
  have Hc := execCheckLeafPteInvalid vpn acc p mxr do_sum q pa lvl (tm t t) Hinv
  replace Hc := execAOfRfF _ (rfFCheckLeafPte _ _ _ _ _ _ _ _ _ _) _ _ Hc
  exact FECExecASame img _ Q _ t _ Ks t (rfFCheckLeafPte _ _ _ _ _ _ _ _ _ _) Hc HQ

/-- Rocq `F_rec_walk_inv0`: an invalid word at level 0. -/
theorem FRecWalkInv0 (base : BitVec 44) (q : BitVec 64) (g : Bool)
    (Q : List ekey → Result (PTW_Output 39 × Unit) (PTW_Error × Unit) → ExecSt → Prop)
    (Ks : List ekey) (t : ExecSt) :
    pteRdOk (fun _ _ => True) μ t (uPteAddr base (Sail.BitVec.extractLsb vpn 8 0)) →
    islot img (uPteAddr base (Sail.BitVec.extractLsb vpn 8 0)) q → Ks ≠ [] → pteInvalid q →
    Q Ks (.Err (.PTW_Invalid_PTE (), ())) t →
    FC (fun _ _ _ => False) Q (wkey (uPteAddr base (Sail.BitVec.extractLsb vpn 8 0)) :: Ks)
      (pt_walk 39 vpn acc p mxr do_sum base 0 g ()) t := by
  intro hok hsl hKs Hinv hq
  rw [pt_walk]
  refine FAssertTrue img _ _ _ rfl _ _ _ _ ?_
  refine AxSpinVA3.fFact (FReadPte img μ (uPteAddr base (Sail.BitVec.extractLsb vpn 8 0)) q
    (fun Ks' x t' => Ks' = Ks ∧ x = .Ok q ∧ t' = t) Ks t hok hsl hKs ⟨rfl, rfl, rfl⟩) ?_
  rintro Ks' x t' ⟨rfl, rfl, rfl⟩
  refine AxSpinVA3.fFactUse (μ := μ) (rfFPteIsInvalid _ _)
    (execAOfRfF _ (rfFPteIsInvalid _ _) _ _ (Hinv _)) ?_
  rw [if_neg (by simp [Functions.not])]
  refine AxSpinVA3.fFact (FCheckLeafInv img vpn acc p mxr do_sum q _ 0
    (fun K x s => x = .Err (.PTW_Invalid_PTE (), ()) ∧ Q K (.Err (.PTW_Invalid_PTE (), ())) s)
    _ _ Hinv ⟨rfl, hq⟩) ?_
  rintro _ _ _ ⟨rfl, hq'⟩
  exact .fcRet _ _ _ hq'

/-- Rocq `F_rec_walk_inv1`: an invalid word at level 1. -/
theorem FRecWalkInv1 (base : BitVec 44) (q : BitVec 64) (g : Bool)
    (Q : List ekey → Result (PTW_Output 39 × Unit) (PTW_Error × Unit) → ExecSt → Prop)
    (Ks : List ekey) (t : ExecSt) :
    pteRdOk (fun _ _ => True) μ t (uPteAddr base (Sail.BitVec.extractLsb vpn 17 9)) →
    islot img (uPteAddr base (Sail.BitVec.extractLsb vpn 17 9)) q → Ks ≠ [] → pteInvalid q →
    Q Ks (.Err (.PTW_Invalid_PTE (), ())) t →
    FC (fun _ _ _ => False) Q (wkey (uPteAddr base (Sail.BitVec.extractLsb vpn 17 9)) :: Ks)
      (pt_walk 39 vpn acc p mxr do_sum base 1 g ()) t := by
  intro hok hsl hKs Hinv hq
  rw [pt_walk]
  refine FAssertTrue img _ _ _ rfl _ _ _ _ ?_
  refine AxSpinVA3.fFact (FReadPte img μ (uPteAddr base (Sail.BitVec.extractLsb vpn 17 9)) q
    (fun Ks' x t' => Ks' = Ks ∧ x = .Ok q ∧ t' = t) Ks t hok hsl hKs ⟨rfl, rfl, rfl⟩) ?_
  rintro Ks' x t' ⟨rfl, rfl, rfl⟩
  refine AxSpinVA3.fFactUse (μ := μ) (rfFPteIsInvalid _ _)
    (execAOfRfF _ (rfFPteIsInvalid _ _) _ _ (Hinv _)) ?_
  rw [if_neg (by simp [Functions.not])]
  refine AxSpinVA3.fFact (FCheckLeafInv img vpn acc p mxr do_sum q _ 1
    (fun K x s => x = .Err (.PTW_Invalid_PTE (), ()) ∧ Q K (.Err (.PTW_Invalid_PTE (), ())) s)
    _ _ Hinv ⟨rfl, hq⟩) ?_
  rintro _ _ _ ⟨rfl, hq'⟩
  exact .fcRet _ _ _ hq'

/-- Rocq `F_rec_walk_inv2`: an invalid word at level 2 (the root slot). -/
theorem FRecWalkInv2 (base : BitVec 44) (q : BitVec 64) (g : Bool)
    (Q : List ekey → Result (PTW_Output 39 × Unit) (PTW_Error × Unit) → ExecSt → Prop)
    (Ks : List ekey) (t : ExecSt) :
    pteRdOk (fun _ _ => True) μ t (uPteAddr base (Sail.BitVec.extractLsb vpn 26 18)) →
    islot img (uPteAddr base (Sail.BitVec.extractLsb vpn 26 18)) q → Ks ≠ [] → pteInvalid q →
    Q Ks (.Err (.PTW_Invalid_PTE (), ())) t →
    FC (fun _ _ _ => False) Q (wkey (uPteAddr base (Sail.BitVec.extractLsb vpn 26 18)) :: Ks)
      (pt_walk 39 vpn acc p mxr do_sum base 2 g ()) t := by
  intro hok hsl hKs Hinv hq
  rw [pt_walk]
  refine FAssertTrue img _ _ _ rfl _ _ _ _ ?_
  refine AxSpinVA3.fFact (FReadPte img μ (uPteAddr base (Sail.BitVec.extractLsb vpn 26 18)) q
    (fun Ks' x t' => Ks' = Ks ∧ x = .Ok q ∧ t' = t) Ks t hok hsl hKs ⟨rfl, rfl, rfl⟩) ?_
  rintro Ks' x t' ⟨rfl, rfl, rfl⟩
  refine AxSpinVA3.fFactUse (μ := μ) (rfFPteIsInvalid _ _)
    (execAOfRfF _ (rfFPteIsInvalid _ _) _ _ (Hinv _)) ?_
  rw [if_neg (by simp [Functions.not])]
  refine AxSpinVA3.fFact (FCheckLeafInv img vpn acc p mxr do_sum q _ 2
    (fun K x s => x = .Err (.PTW_Invalid_PTE (), ()) ∧ Q K (.Err (.PTW_Invalid_PTE (), ())) s)
    _ _ Hinv ⟨rfl, hq⟩) ?_
  rintro _ _ _ ⟨rfl, hq'⟩
  exact .fcRet _ _ _ hq'

/-- Rocq `F_rec_walk_down1`: descend one valid pointer word at level 1, image-fed. -/
theorem FRecWalkDown1 (base : BitVec 44) (p1 : BitVec 64) (g : Bool)
    (Q : List ekey → Result (PTW_Output 39 × Unit) (PTW_Error × Unit) → ExecSt → Prop)
    (Ks : List ekey) (t : ExecSt) :
    pteRdOk (fun _ _ => True) μ t (uPteAddr base (Sail.BitVec.extractLsb vpn 17 9)) →
    islot img (uPteAddr base (Sail.BitVec.extractLsb vpn 17 9)) p1 → Ks ≠ [] →
    pteValid p1 → ptePtr p1 →
    (∀ g' : Bool, FC (fun _ _ _ => False) Q Ks
      (pt_walk 39 vpn acc p mxr do_sum (uNextBase p1) 0 g' ()) t) →
    FC (fun _ _ _ => False) Q (wkey (uPteAddr base (Sail.BitVec.extractLsb vpn 17 9)) :: Ks)
      (pt_walk 39 vpn acc p mxr do_sum base 1 g ()) t := by
  intro hok hsl hKs Hv Hp Hk
  rw [pt_walk]
  refine FAssertTrue img _ _ _ rfl _ _ _ _ ?_
  refine AxSpinVA3.fFact (FReadPte img μ (uPteAddr base (Sail.BitVec.extractLsb vpn 17 9)) p1
    (fun Ks' x t' => Ks' = Ks ∧ x = .Ok p1 ∧ t' = t) Ks t hok hsl hKs ⟨rfl, rfl, rfl⟩) ?_
  rintro Ks' x t' ⟨rfl, rfl, rfl⟩
  refine AxSpinVA3.fFactUse (μ := μ) (rfFPteIsInvalid _ _) (h1iA p1 Hv _) ?_
  rw [if_pos (by simp only [Functions.not, Bool.not_false, Bool.true_and, Bool.and_eq_true]; exact ⟨Hp, by decide⟩)]
  exact Hk _

/-- Rocq `F_rec_walk_down2`: descend one valid pointer word at level 2, image-fed. -/
theorem FRecWalkDown2 (base : BitVec 44) (p2 : BitVec 64) (g : Bool)
    (Q : List ekey → Result (PTW_Output 39 × Unit) (PTW_Error × Unit) → ExecSt → Prop)
    (Ks : List ekey) (t : ExecSt) :
    pteRdOk (fun _ _ => True) μ t (uPteAddr base (Sail.BitVec.extractLsb vpn 26 18)) →
    islot img (uPteAddr base (Sail.BitVec.extractLsb vpn 26 18)) p2 → Ks ≠ [] →
    pteValid p2 → ptePtr p2 →
    (∀ g' : Bool, FC (fun _ _ _ => False) Q Ks
      (pt_walk 39 vpn acc p mxr do_sum (uNextBase p2) 1 g' ()) t) →
    FC (fun _ _ _ => False) Q (wkey (uPteAddr base (Sail.BitVec.extractLsb vpn 26 18)) :: Ks)
      (pt_walk 39 vpn acc p mxr do_sum base 2 g ()) t := by
  intro hok hsl hKs Hv Hp Hk
  rw [pt_walk]
  refine FAssertTrue img _ _ _ rfl _ _ _ _ ?_
  refine AxSpinVA3.fFact (FReadPte img μ (uPteAddr base (Sail.BitVec.extractLsb vpn 26 18)) p2
    (fun Ks' x t' => Ks' = Ks ∧ x = .Ok p2 ∧ t' = t) Ks t hok hsl hKs ⟨rfl, rfl, rfl⟩) ?_
  rintro Ks' x t' ⟨rfl, rfl, rfl⟩
  refine AxSpinVA3.fFactUse (μ := μ) (rfFPteIsInvalid _ _) (h2iA p2 Hv _) ?_
  rw [if_pos (by simp only [Functions.not, Bool.not_false, Bool.true_and, Bool.and_eq_true]; exact ⟨Hp, by decide⟩)]
  exact Hk _

/-- Rocq `F_translate_TLB_miss_err`: `translate_TLB_miss` forwards the walk's `Err`. -/
theorem FTranslateTLBMissErr (asid : BitVec 16) (root : BitVec 44)
    (Q : List ekey → Result (BitVec 44 × page_based_mem_type × Unit) (PTW_Error × Unit) →
      ExecSt → Prop)
    (K : List ekey) (t : ExecSt) :
    FC (fun _ _ _ => False)
      (fun Ks' r t' => match r with
        | .Err (f, ext) => Q Ks' (.Err (f, ext)) t'
        | .Ok _ => False) K
      (pt_walk 39 vpn acc p mxr do_sum root 2 false ()) t →
    FC (fun _ _ _ => False) Q K (translate_TLB_miss 39 asid root vpn acc p mxr do_sum ()) t := by
  intro Hw
  unfold translate_TLB_miss
  refine AxSpinVA3.fFact Hw ?_
  intro Ks' r t' HQ
  cases r with
  | Ok x => exact HQ.elim
  | Err e =>
    obtain ⟨f, ext⟩ := e
    exact .fcRet _ _ _ HQ
end walkInv

/-! # 2. The translation front with the Err arm -/

/-- Rocq `F_translateAddr_front_inv` (deviation 5): the walk's `PTW_Invalid_PTE` becomes the
fetch page fault. -/
theorem FTranslateAddrFrontInv (img : Image) (μ : ExecSt) (p : Privilege) (vpn : BitVec 27)
    (root : BitVec 44) (satp0 va : BitVec 64)
    (Qf : List ekey → Result (physaddr × page_based_mem_type × Unit) (ExceptionType × Unit) →
      ExecSt → Prop)
    (Ks : List ekey) (t : ExecSt) :
    exec (effectivePrivilege (.InstructionFetch ()) (t.regs .mstatus) p) (tm μ t)
      = some (p, tm μ t) →
    exec (is_shadow_stack_access (.InstructionFetch ())) (tm μ t) = some (false, tm μ t) →
    t.regs .cur_privilege = p →
    exec (translationMode p) (tm μ t) = some (.Sv39, tm μ t) →
    t.regs .satp = satp0 →
    BitVec.setWidth 44 (satp_to_ppn satp0) = root →
    zero_extend (m := 16) (satp_to_asid satp0) = 0#16 →
    (va != sign_extend (m := 64) (Sail.BitVec.extractLsb va 38 0)) = false →
    BitVec.setWidth 27 (Sail.BitVec.extractLsb (Sail.BitVec.extractLsb va 38 0) 38
      Functions.pagesize_bits) = vpn →
    FEC img (fun _ _ _ => False)
      (fun Ks' r t' => match r with
        | .Ok _ => False
        | .Err (f, ext) => f = .PTW_Invalid_PTE () ∧ Qf Ks' (.Err (.E_Fetch_Page_Fault (), ext)) t')
      Ks
      (translate 39 0#16 root vpn (.InstructionFetch ()) p
        ((_get_Mstatus_MXR (t.regs .mstatus)) == 1#1)
        ((_get_Mstatus_SUM (t.regs .mstatus)) == 1#1) init_ext_ptw) t →
    FEC img (fun _ _ _ => False) Qf Ks (translateAddr (.Virtaddr va) (.InstructionFetch ())) t := by
  intro heff hss hcp htm hsatp hppn hasid hcanon hvpn HTR
  have heffA := execAOfRfF _ (rfFEffectivePrivilege _ _ _) _ _ heff
  have hssA := execAOfRfF _ (rfFIsShadowStackAccess _) _ _ hss
  have htmA := execAOfRfF _ (rfFTranslationMode _) _ _ htm
  unfold translateAddr
  apply FECCatchEarlyReturn
  ax_spin_va3_go
  rw [hcp]
  refine AxSpinVA3.fRUse (μ := μ) (rfFEffectivePrivilege _ _ _) heffA ?_
  refine AxSpinVA3.fRUse (μ := μ) (rfFTranslationMode _) htmA ?_
  refine AxSpinVA3.fRUse (μ := μ) (rfFIsShadowStackAccess _) hssA ?_
  simp only [Bool.false_eq_true, ↓reduceIte]
  simp (config := { decide := true }) only [↓reduceIte]
  refine AxSpinVA3.fRUse (μ := μ) (rfFSatpModeWidthForwards _) (a := (39 : Int)) rfl ?_
  have hgs : execA (get_satp 39) (tm μ t) = some (satp0, tm μ t) := by
    unfold get_satp
    ax_spine4_run [hsatp]
    show some (BitVec.setWidth 64 satp0, _) = _
    rw [BitVec.setWidth_eq]
  simp (config := { decide := true }) only [Int.reduceToNat, Int.reduceSub, bits_of_virtaddr,
    hcanon, Bool.false_eq_true, ↓reduceIte, Nat.reduceSub]
  refine AxSpinVA3.fRUse (μ := μ) (rfFGetSatp _) hgs ?_
  refine AxSpinVA3.fRUse (μ := μ) (by trivial) rfl ?_
  ax_spin_va3_go
  erw [hasid, hppn, hvpn]
  refine AxSpinVA3.fRLift HTR ?_
  intro Ks' x t' hx
  cases x with
  | Ok a => exact hx.elim
  | Err e =>
    obtain ⟨f, ext⟩ := e
    obtain ⟨rfl, HQ⟩ := hx
    dsimp only
    ax_spin_va3_go
    rw [show translationException (.InstructionFetch ()) (.PTW_Invalid_PTE ()) =
      pure (.E_Fetch_Page_Fault ()) from rfl]
    ax_spin_va3_go
    exact .fcRet _ _ _ HQ

/-! # 3. The theorems -/

/-- Rocq `app_snoc_neq`. -/
theorem appSnocNeq {A : Type} (l : List A) (x : A) : l ++ [x] ≠ [] := by simp

section thm8
variable (σi : ExecSt) (T : PTree) (satp0 : BitVec 64)
  (Hmode : _get_Satp64_Mode (Mk_Satp64 satp0) = 8#4)
  (Hasid : zero_extend (m := 16) (satp_to_asid satp0) = 0#16)
  (Hppn : BitVec.setWidth 44 (satp_to_ppn satp0) = T.base)

include Hmode Hasid Hppn in
/-- Rocq `unmapped_front`: the shared prefix, from the minstret-written boundary state to the
walk. -/
theorem unmappedFront (t : ExecSt) (b : Bool) (va : BitVec 64) (K0 Ks : List ekey)
    (Hwalk : ∀ (mxr do_sum : Bool)
      (Q : List ekey → Result (PTW_Output 39 × Unit) (PTW_Error × Unit) → ExecSt → Prop),
      Q Ks (.Err (.PTW_Invalid_PTE (), ())) (t.setReg .minstret_increment b) →
      FEC (imgOf σi) (fun _ _ _ => False) Q K0
        (pt_walk 39 (WeakKpt.svpnOf va) (.InstructionFetch ()) .Supervisor mxr do_sum T.base 2
          false ())
        (t.setReg .minstret_increment b)) :
    ctrlOkS T satp0 t.regs → t.regs .PC = va →
    is_aligned_vaddr (.Virtaddr va) 4 = true →
    (va != sign_extend (m := 64) (Sail.BitVec.extractLsb va 38 0)) = false →
    tlbHitb (t.regs .tlb) (WeakKpt.svpnOf va) = false →
    FEC (imgOf σi) (fun _ _ _ => False)
      (fun Ks' r t' => Ks' = Ks ∧ r = .F_Error (.E_Fetch_Page_Fault (), va) ∧
        t' = t.setReg .minstret_increment b)
      K0 (fetch ()) (t.setReg .minstret_increment b) := by
  intro Hc HPC Hal Hcanon Hmiss
  have Hc1 := ctrlOkSMinstretInc T satp0 t b Hc
  have Hc0 := Hc1
  obtain ⟨Hpriv, -, -, -, -, -, -, Hms, -, -, Hsatp, -⟩ := Hc0
  obtain ⟨-, HSXL, -⟩ := Hms
  have HPC1 : (t.setReg .minstret_increment b).regs .PC = va := by
    rw [ExecSt.setReg_regs, RegFile.set_other _ _ _ _ (by decide)]; exact HPC
  have Htlb1 : (t.setReg .minstret_increment b).regs .tlb = t.regs .tlb := by
    rw [ExecSt.setReg_regs, RegFile.set_other _ _ _ _ (by decide)]
  refine FFetch4Err (imgOf σi) va (.E_Fetch_Page_Fault ()) K0 _ _ HPC1 Hal ?_
  refine FTranslateAddrFrontInv (imgOf σi) σi .Supervisor (WeakKpt.svpnOf va) T.base satp0 va _
    K0 _ (execEffectivePrivilegeFetch _ .Supervisor _) (execIsShadowStackFetch _) Hpriv
    (execTranslationModeSSv39 satp0 (tm σi (t.setReg .minstret_increment b)) HSXL Hsatp Hmode)
    Hsatp Hppn Hasid Hcanon rfl ?_
  unfold translate
  have Hlk : execA (lookup_TLB 39 0#16 (WeakKpt.svpnOf va))
      (tm σi (t.setReg .minstret_increment b)) =
      some (none, tm σi (t.setReg .minstret_increment b)) := by
    rw [← Htlb1] at Hmiss
    unfold tlbHitb at Hmiss
    cases hslot : ((t.setReg .minstret_increment b).regs .tlb)[tlb_hash 39
        (WeakKpt.svpnOf va)]! with
    | none =>
      have h := execLookupTLBMiss (WeakKpt.svpnOf va) 0#16 _
        (tm σi (t.setReg .minstret_increment b)) rfl hslot
      to_a h
      exact h
    | some ent =>
      rw [hslot] at Hmiss
      have h := execLookupTLBNomatchS (WeakKpt.svpnOf va) 0#16 ent _
        (tm σi (t.setReg .minstret_increment b)) rfl hslot Hmiss
      to_a h
      exact h
  refine AxSpinVA3.fFactUse (μ := σi) (rfFLookupTLB _ _ _) Hlk ?_
  refine FTranslateTLBMissErr (imgOf σi) (WeakKpt.svpnOf va) _ _ _ _ 0#16 T.base _ K0 _ ?_
  refine Hwalk _ _ _ ?_
  exact ⟨rfl, rfl, HPC1, rfl, rfl, rfl⟩

include Hmode Hasid Hppn in
/-- (Lean-only, deviation 1) THE LEVEL-0 UNMAPPED FAULT STEP: the three slot keys, and the next
boundary is a regime state at PC = stvec base with the TLB unchanged. -/
theorem AxSpinVA8.faultUnmapped0Step (t : ExecSt) (va q2 q1 q0 : BitVec 64) (n : Nat)
    (Ks : List ekey) :
    ctrlOkS T satp0 t.regs → t.regs .PC = va →
    is_aligned_vaddr (.Virtaddr va) 4 = true →
    (va != sign_extend (m := 64) (Sail.BitVec.extractLsb va 38 0)) = false →
    tlbHitb (t.regs .tlb) (WeakKpt.svpnOf va) = false →
    WeakWalkEff.ptSlotMem σi (AxPtProt.ptAddr2 T (WeakKpt.svpnOf va)) q2 → pteValid q2 →
    ptePtr q2 →
    WeakWalkEff.ptSlotMem σi (AxPtProt.ptAddr1 q2 (WeakKpt.svpnOf va)) q1 → pteValid q1 →
    ptePtr q1 →
    WeakWalkEff.ptSlotMem σi (AxPtProt.ptAddr0 q1 (WeakKpt.svpnOf va)) q0 → pteInvalid q0 →
    AxIntr.stvecDirect t.regs →
    bit_to_bool (BitVec.access (t.regs .medeleg)
      (BitVec.toNatInt (exceptionType_bits_forwards (.E_Fetch_Page_Fault ())))) = true →
    Ks ≠ [] →
    (∀ t' : ExecSt, ctrlOkS T satp0 t'.regs → t'.regs .PC = stvecBase (t.regs .stvec) →
      t'.regs .tlb = t.regs .tlb → BFEC (imgOf σi) n Ks t') →
    BFEC (imgOf σi) (n + 1)
      ([wkey (AxPtProt.ptAddr2 T (WeakKpt.svpnOf va)), wkey (AxPtProt.ptAddr1 q2 (WeakKpt.svpnOf va)),
        wkey (AxPtProt.ptAddr0 q1 (WeakKpt.svpnOf va))] ++ Ks) t := by
  intro Hc HPC Hal Hcanon Hmiss Hs2 Hv2 Hp2 Hs1 Hv1 Hp1 Hs0 Hi0 Hd Hdel HKs Hk tick
  refine FRiscvStepFault (imgOf σi) T satp0 tick _ Ks (.E_Fetch_Page_Fault ()) va _ t Hc Hd Hdel
    ?_ ?_
  · intro b
    refine unmappedFront σi T satp0 Hmode Hasid Hppn t b va _ Ks ?_ Hc HPC Hal Hcanon Hmiss
    intro mxr do_sum Q HQ
    have Hc1 := ctrlOkSMinstretInc T satp0 t b Hc
    obtain ⟨-, -, -, -, Hhtif, -, Hpma, -, -, -, -, -, Hpmp⟩ := Hc1
    refine FRecWalkDown2 (imgOf σi) σi (WeakKpt.svpnOf va) _ _ mxr do_sum T.base q2 false Q _ _
      (pteRdOkOfRegs (fun _ _ => True) σi _ _ _ σi Hs2 Hpmp Hpma Hhtif trivial)
      (slotImg σi _ _ Hs2) (by simp) Hv2 Hp2 ?_
    intro g
    refine FRecWalkDown1 (imgOf σi) σi (WeakKpt.svpnOf va) _ _ mxr do_sum (uNextBase q2) q1 g Q
      _ _ (pteRdOkOfRegs (fun _ _ => True) σi _ _ _ σi Hs1 Hpmp Hpma Hhtif trivial)
      (slotImg σi _ _ Hs1) (by simp) Hv1 Hp1 ?_
    intro g'
    exact FRecWalkInv0 (imgOf σi) σi (WeakKpt.svpnOf va) _ _ mxr do_sum (uNextBase q1) q0 g' Q
      Ks _ (pteRdOkOfRegs (fun _ _ => True) σi _ _ _ σi Hs0 Hpmp Hpma Hhtif trivial)
      (slotImg σi _ _ Hs0) HKs Hi0 HQ
  · intro b t' Hfr
    obtain ⟨Hc', HPC', Htlb'⟩ := faultPostFacts T satp0 t b _ va t' Hc Hfr
    exact Hk t' Hc' HPC' Htlb'

include Hmode Hasid Hppn in
/-- (Lean-only, deviation 1) THE LEVEL-1 UNMAPPED FAULT STEP. -/
theorem AxSpinVA8.faultUnmapped1Step (t : ExecSt) (va q2 q1 : BitVec 64) (n : Nat)
    (Ks : List ekey) :
    ctrlOkS T satp0 t.regs → t.regs .PC = va →
    is_aligned_vaddr (.Virtaddr va) 4 = true →
    (va != sign_extend (m := 64) (Sail.BitVec.extractLsb va 38 0)) = false →
    tlbHitb (t.regs .tlb) (WeakKpt.svpnOf va) = false →
    WeakWalkEff.ptSlotMem σi (AxPtProt.ptAddr2 T (WeakKpt.svpnOf va)) q2 → pteValid q2 →
    ptePtr q2 →
    WeakWalkEff.ptSlotMem σi (AxPtProt.ptAddr1 q2 (WeakKpt.svpnOf va)) q1 → pteInvalid q1 →
    AxIntr.stvecDirect t.regs →
    bit_to_bool (BitVec.access (t.regs .medeleg)
      (BitVec.toNatInt (exceptionType_bits_forwards (.E_Fetch_Page_Fault ())))) = true →
    Ks ≠ [] →
    (∀ t' : ExecSt, ctrlOkS T satp0 t'.regs → t'.regs .PC = stvecBase (t.regs .stvec) →
      t'.regs .tlb = t.regs .tlb → BFEC (imgOf σi) n Ks t') →
    BFEC (imgOf σi) (n + 1)
      ([wkey (AxPtProt.ptAddr2 T (WeakKpt.svpnOf va)),
        wkey (AxPtProt.ptAddr1 q2 (WeakKpt.svpnOf va))] ++ Ks) t := by
  intro Hc HPC Hal Hcanon Hmiss Hs2 Hv2 Hp2 Hs1 Hi1 Hd Hdel HKs Hk tick
  refine FRiscvStepFault (imgOf σi) T satp0 tick _ Ks (.E_Fetch_Page_Fault ()) va _ t Hc Hd Hdel
    ?_ ?_
  · intro b
    refine unmappedFront σi T satp0 Hmode Hasid Hppn t b va _ Ks ?_ Hc HPC Hal Hcanon Hmiss
    intro mxr do_sum Q HQ
    have Hc1 := ctrlOkSMinstretInc T satp0 t b Hc
    obtain ⟨-, -, -, -, Hhtif, -, Hpma, -, -, -, -, -, Hpmp⟩ := Hc1
    refine FRecWalkDown2 (imgOf σi) σi (WeakKpt.svpnOf va) _ _ mxr do_sum T.base q2 false Q _ _
      (pteRdOkOfRegs (fun _ _ => True) σi _ _ _ σi Hs2 Hpmp Hpma Hhtif trivial)
      (slotImg σi _ _ Hs2) (by simp) Hv2 Hp2 ?_
    intro g
    exact FRecWalkInv1 (imgOf σi) σi (WeakKpt.svpnOf va) _ _ mxr do_sum (uNextBase q2) q1 g Q
      Ks _ (pteRdOkOfRegs (fun _ _ => True) σi _ _ _ σi Hs1 Hpmp Hpma Hhtif trivial)
      (slotImg σi _ _ Hs1) HKs Hi1 HQ
  · intro b t' Hfr
    obtain ⟨Hc', HPC', Htlb'⟩ := faultPostFacts T satp0 t b _ va t' Hc Hfr
    exact Hk t' Hc' HPC' Htlb'

include Hmode Hasid Hppn in
/-- (Lean-only, deviation 1) THE LEVEL-2 (root slot) UNMAPPED FAULT STEP. -/
theorem AxSpinVA8.faultUnmapped2Step (t : ExecSt) (va q2 : BitVec 64) (n : Nat)
    (Ks : List ekey) :
    ctrlOkS T satp0 t.regs → t.regs .PC = va →
    is_aligned_vaddr (.Virtaddr va) 4 = true →
    (va != sign_extend (m := 64) (Sail.BitVec.extractLsb va 38 0)) = false →
    tlbHitb (t.regs .tlb) (WeakKpt.svpnOf va) = false →
    WeakWalkEff.ptSlotMem σi (AxPtProt.ptAddr2 T (WeakKpt.svpnOf va)) q2 → pteInvalid q2 →
    AxIntr.stvecDirect t.regs →
    bit_to_bool (BitVec.access (t.regs .medeleg)
      (BitVec.toNatInt (exceptionType_bits_forwards (.E_Fetch_Page_Fault ())))) = true →
    Ks ≠ [] →
    (∀ t' : ExecSt, ctrlOkS T satp0 t'.regs → t'.regs .PC = stvecBase (t.regs .stvec) →
      t'.regs .tlb = t.regs .tlb → BFEC (imgOf σi) n Ks t') →
    BFEC (imgOf σi) (n + 1) ([wkey (AxPtProt.ptAddr2 T (WeakKpt.svpnOf va))] ++ Ks) t := by
  intro Hc HPC Hal Hcanon Hmiss Hs2 Hi2 Hd Hdel HKs Hk tick
  refine FRiscvStepFault (imgOf σi) T satp0 tick _ Ks (.E_Fetch_Page_Fault ()) va _ t Hc Hd Hdel
    ?_ ?_
  · intro b
    refine unmappedFront σi T satp0 Hmode Hasid Hppn t b va _ Ks ?_ Hc HPC Hal Hcanon Hmiss
    intro mxr do_sum Q HQ
    have Hc1 := ctrlOkSMinstretInc T satp0 t b Hc
    obtain ⟨-, -, -, -, Hhtif, -, Hpma, -, -, -, -, -, Hpmp⟩ := Hc1
    exact FRecWalkInv2 (imgOf σi) σi (WeakKpt.svpnOf va) _ _ mxr do_sum T.base q2 false Q
      Ks _ (pteRdOkOfRegs (fun _ _ => True) σi _ _ _ σi Hs2 Hpmp Hpma Hhtif trivial)
      (slotImg σi _ _ Hs2) HKs Hi2 HQ
  · intro b t' Hfr
    obtain ⟨Hc', HPC', Htlb'⟩ := faultPostFacts T satp0 t b _ va t' Hc Hfr
    exact Hk t' Hc' HPC' Htlb'

include Hmode Hasid Hppn in
/-- Rocq `chain_fault_unmapped0`: invalid at LEVEL 0 (deviation 1: the end key is `ENf`). -/
theorem chainFaultUnmapped0 (t : ExecSt) (va w spa sp2 sp1 q2 q1 q0 : BitVec 64) :
    ctrlOkS T satp0 t.regs → t.regs .PC = va →
    is_aligned_vaddr (.Virtaddr va) 4 = true →
    (va != sign_extend (m := 64) (Sail.BitVec.extractLsb va 38 0)) = false →
    tlbHitb (t.regs .tlb) (WeakKpt.svpnOf va) = false →
    WeakWalkEff.ptSlotMem σi (AxPtProt.ptAddr2 T (WeakKpt.svpnOf va)) q2 → pteValid q2 →
    ptePtr q2 →
    WeakWalkEff.ptSlotMem σi (AxPtProt.ptAddr1 q2 (WeakKpt.svpnOf va)) q1 → pteValid q1 →
    ptePtr q1 →
    WeakWalkEff.ptSlotMem σi (AxPtProt.ptAddr0 q1 (WeakKpt.svpnOf va)) q0 → pteInvalid q0 →
    AxIntr.stvecDirect t.regs →
    bit_to_bool (BitVec.access (t.regs .medeleg)
      (BitVec.toNatInt (exceptionType_bits_forwards (.E_Fetch_Page_Fault ())))) = true →
    is_aligned_vaddr (.Virtaddr (stvecBase (t.regs .stvec))) 4 = true →
    fetchable σi T (stvecBase (t.regs .stvec)) w spa sp2 sp1 →
    inRam spa 4 → is_aligned_paddr (.Physaddr spa) 4 = true →
    imgBytes (imgOf σi) (paZ spa) 4 = none →
    BFEC (imgOf σi) 2
      ([wkey (AxPtProt.ptAddr2 T (WeakKpt.svpnOf va)), wkey (AxPtProt.ptAddr1 q2 (WeakKpt.svpnOf va)),
        wkey (AxPtProt.ptAddr0 q1 (WeakKpt.svpnOf va))] ++
       (walkKeys T (t.regs .tlb) (WeakKpt.svpnOf (stvecBase (t.regs .stvec))) sp2 sp1 ++
        [.ENf (paZ spa, 4)])) t := by
  intro Hc HPC Hal Hcanon Hmiss Hs2 Hv2 Hp2 Hs1 Hv1 Hp1 Hs0 Hi0 Hd Hdel Hals Hfa Hram Halp Hv
  refine AxSpinVA8.faultUnmapped0Step σi T satp0 Hmode Hasid Hppn t va q2 q1 q0 1 _ Hc HPC Hal
    Hcanon Hmiss Hs2 Hv2 Hp2 Hs1 Hv1 Hp1 Hs0 Hi0 Hd Hdel (appSnocNeq _ _) ?_
  intro t' Hc' HPC' Htlb'
  rw [← Htlb']
  exact chainFetchMapped4 σi T satp0 Hmode Hasid Hppn t' _ w spa sp2 sp1 Hc' HPC' Hals Hfa Hram
    Halp Hv

include Hmode Hasid Hppn in
/-- Rocq `chain_fault_unmapped1`: invalid at LEVEL 1 (deviation 1). -/
theorem chainFaultUnmapped1 (t : ExecSt) (va w spa sp2 sp1 q2 q1 : BitVec 64) :
    ctrlOkS T satp0 t.regs → t.regs .PC = va →
    is_aligned_vaddr (.Virtaddr va) 4 = true →
    (va != sign_extend (m := 64) (Sail.BitVec.extractLsb va 38 0)) = false →
    tlbHitb (t.regs .tlb) (WeakKpt.svpnOf va) = false →
    WeakWalkEff.ptSlotMem σi (AxPtProt.ptAddr2 T (WeakKpt.svpnOf va)) q2 → pteValid q2 →
    ptePtr q2 →
    WeakWalkEff.ptSlotMem σi (AxPtProt.ptAddr1 q2 (WeakKpt.svpnOf va)) q1 → pteInvalid q1 →
    AxIntr.stvecDirect t.regs →
    bit_to_bool (BitVec.access (t.regs .medeleg)
      (BitVec.toNatInt (exceptionType_bits_forwards (.E_Fetch_Page_Fault ())))) = true →
    is_aligned_vaddr (.Virtaddr (stvecBase (t.regs .stvec))) 4 = true →
    fetchable σi T (stvecBase (t.regs .stvec)) w spa sp2 sp1 →
    inRam spa 4 → is_aligned_paddr (.Physaddr spa) 4 = true →
    imgBytes (imgOf σi) (paZ spa) 4 = none →
    BFEC (imgOf σi) 2
      ([wkey (AxPtProt.ptAddr2 T (WeakKpt.svpnOf va)),
        wkey (AxPtProt.ptAddr1 q2 (WeakKpt.svpnOf va))] ++
       (walkKeys T (t.regs .tlb) (WeakKpt.svpnOf (stvecBase (t.regs .stvec))) sp2 sp1 ++
        [.ENf (paZ spa, 4)])) t := by
  intro Hc HPC Hal Hcanon Hmiss Hs2 Hv2 Hp2 Hs1 Hi1 Hd Hdel Hals Hfa Hram Halp Hv
  refine AxSpinVA8.faultUnmapped1Step σi T satp0 Hmode Hasid Hppn t va q2 q1 1 _ Hc HPC Hal
    Hcanon Hmiss Hs2 Hv2 Hp2 Hs1 Hi1 Hd Hdel (appSnocNeq _ _) ?_
  intro t' Hc' HPC' Htlb'
  rw [← Htlb']
  exact chainFetchMapped4 σi T satp0 Hmode Hasid Hppn t' _ w spa sp2 sp1 Hc' HPC' Hals Hfa Hram
    Halp Hv

include Hmode Hasid Hppn in
/-- Rocq `chain_fault_unmapped2`: invalid at LEVEL 2, the root slot (deviation 1). -/
theorem chainFaultUnmapped2 (t : ExecSt) (va w spa sp2 sp1 q2 : BitVec 64) :
    ctrlOkS T satp0 t.regs → t.regs .PC = va →
    is_aligned_vaddr (.Virtaddr va) 4 = true →
    (va != sign_extend (m := 64) (Sail.BitVec.extractLsb va 38 0)) = false →
    tlbHitb (t.regs .tlb) (WeakKpt.svpnOf va) = false →
    WeakWalkEff.ptSlotMem σi (AxPtProt.ptAddr2 T (WeakKpt.svpnOf va)) q2 → pteInvalid q2 →
    AxIntr.stvecDirect t.regs →
    bit_to_bool (BitVec.access (t.regs .medeleg)
      (BitVec.toNatInt (exceptionType_bits_forwards (.E_Fetch_Page_Fault ())))) = true →
    is_aligned_vaddr (.Virtaddr (stvecBase (t.regs .stvec))) 4 = true →
    fetchable σi T (stvecBase (t.regs .stvec)) w spa sp2 sp1 →
    inRam spa 4 → is_aligned_paddr (.Physaddr spa) 4 = true →
    imgBytes (imgOf σi) (paZ spa) 4 = none →
    BFEC (imgOf σi) 2
      ([wkey (AxPtProt.ptAddr2 T (WeakKpt.svpnOf va))] ++
       (walkKeys T (t.regs .tlb) (WeakKpt.svpnOf (stvecBase (t.regs .stvec))) sp2 sp1 ++
        [.ENf (paZ spa, 4)])) t := by
  intro Hc HPC Hal Hcanon Hmiss Hs2 Hi2 Hd Hdel Hals Hfa Hram Halp Hv
  refine AxSpinVA8.faultUnmapped2Step σi T satp0 Hmode Hasid Hppn t va q2 1 _ Hc HPC Hal
    Hcanon Hmiss Hs2 Hi2 Hd Hdel (appSnocNeq _ _) ?_
  intro t' Hc' HPC' Htlb'
  rw [← Htlb']
  exact chainFetchMapped4 σi T satp0 Hmode Hasid Hppn t' _ w spa sp2 sp1 Hc' HPC' Hals Hfa Hram
    Halp Hv

end thm8

end Weak
