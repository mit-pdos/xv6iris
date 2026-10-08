/-
Weak: **the spinlock plan, PHASE 5 item (4), part 7** — THE FAULT ARMS of the arbitrary-VA
chain, symbolically: MISALIGNED and NON-CANONICAL PCs (register-only until PC := stvec, then the
stvec fetch chain).

Rocq: `iris/AxSpinVA7.v` @ xxvzwolszwmp.

## What this file proves

`chainFaultMisal` / `chainFaultNoncanon`: at every state `t` of the S-mode regime `ctrlOkS` with
PC = `va` misaligned (PC[0] = 1), resp. non-canonical and 4-aligned, with the matching medeleg
bit set (fetch-misaligned, resp. fetch-page-fault, delegated to S) and stvec in direct mode
pointing at a fetchable, 4-aligned kernel VA `sv` — the label chain from the boundary is, for
BOTH ticks of BOTH steps and EVERY pin answer,
    `walkKeys T tlb (svpnOf sv) p2 p1 ++ [.ENf (paZ pa(sv), 4)]`
i.e. the faulting step emits NO label (`handle_exception` is register-only), and the first label
is that of the stvec fetch at the post-trap boundary (`xtrapSt`, regime kept, TLB untouched;
`AxSpinVA4.chainFetchMapped4` there).
PIECES: `FTickFrame`, `FHandleException`, `FFetchMisal`, `FTranslateAddrNoncanon`,
`FFetch4Err` / `FFetch2Err` (translation `Err` ⇒ `F_Error`), `FRiscvStepFault` (`try_step`'s
fault arm: handle_exception, tick_pc, no retire; then the tick, frame form), `faultPostFacts`.
EXCLUDED (as Rocq): the walk faults (`AxSpinVA8`), denied / A-clear leaves, PMA/PMP-denied
fetch, an unmapped stvec.

## Deviations from Rocq

1. O2 STAGE C (`AxSpinVA4` deviation 1).  The stvec fetch is no chain key; the theorems end at
   `.ENf (paZ spa, 4)` and take `imgBytes (imgOf σi) (paZ spa) 4 = none` (the form
   `AxSpinVA4.chainFetchMapped4` proves).  The in-image case (stvec in kernel text, the usual
   one) is served by the Lean-only step theorems `AxSpinVA7.faultMisalStep` /
   `AxSpinVA7.faultNoncanonStep`: the faulting step leaves the chain untouched and every
   post-trap boundary is a regime state with PC = `stvecBase stvec` and the TLB unchanged, so ANY
   chain fact for the next `n` steps there (e.g. via `AxSpinVA4.fetchMappedImg4`) lifts to
   `n + 1` steps from `t`.  The Rocq-named theorems are corollaries.
2. SPELLING (as `AxSpinVA4` deviation 3 / `AxSpinVA6` deviation 1): `mstate` ↦ `ExecSt`,
   `register_lookup r t.(sregs)` ↦ `t.regs .r`, `set_reg t (R_bool minstret_increment) b` ↦
   `t.setReg .minstret_increment b`, `WpIntrCore.stvec_base` ↦ `stvecBase`, `stvec_direct` ↦
   `AxIntr.stvecDirect`, `tick_frame` ↦ `tickFrame`, `neq_vec (access_vec_dec va i) 'b"0"` ↦
   `Sail.BitVec.access va i != 0#1`, `access_vec_dec v (uint i)` ↦
   `BitVec.access v (BitVec.toNatInt i)`, `addr_is_ram spa ∧ addr_is_ram (pa_add spa 3)` ↦
   `inRam spa 4`, `uint` ↦ `paZ`, the canonical test `neq_vec (bits_of_virtaddr …) (sign_extend'
   64 (subrange …))` ↦ `(va != sign_extend (m := 64) (Sail.BitVec.extractLsb va 38 0))`,
   `returnM exc` ↦ `pure exc`; the theorems' `let sv := …` is inlined as `stvecBase (t.regs
   .stvec)`; the satp hypotheses `Hmode Hasid Hppn` take `AxSpineOk4` deviation 7's shapes and
   are explicit arguments (after `σi T satp0`).
3. The Lean `fetch` tests `PC[0]`, then `PC[1]` with `Ext_Zca`, then the 4-alignment with
   `Ext_Ziccif` (`AxSpinVA4` deviation 5); `fetch_bytes` catches its own early return, so the
   translation `Err` reaches `fetch` as `FetchBytes_Exception`.  `FFetch2Err`'s bit facts are
   premises (as `AxSpinVA4.FFetch2`).
4. `FTranslateAddrNoncanon` takes the front premises at `tm μ t` as `AxSpinVA3.FTranslateAddrFront`
   (SC `exec` facts; the `get_satp` / width / assert steps are inlined in the proof).
5. TACTICS: Rocq `nseip7` / `h_step` / `h_go` / `f_useY` ↦ the `AxSpinVA3` / `AxSpinVA4` kit and
   the local tactic `va7_go`.

**Rocq → Lean name map.**  `F_tick_frame` `FTickFrame`, `F_handle_exception` `FHandleException`,
`F_fetch_misal` `FFetchMisal`, `F_translateAddr_noncanon` `FTranslateAddrNoncanon`,
`F_fetch_4_err` `FFetch4Err`, `F_fetch_2_err` `FFetch2Err`, `fault_post` `faultPost`,
`F_riscv_step_fault` `FRiscvStepFault`, `fault_post_facts` `faultPostFacts`,
`chain_fault_misal` `chainFaultMisal`, `chain_fault_noncanon` `chainFaultNoncanon`.  None is in
the duplicated-name table.  Lean-only (file-qualified): `AxSpinVA7.faultMisalStep`,
`AxSpinVA7.faultNoncanonStep`, `AxSpinVA7.fBranchAnnounce`; local tactic `va7_go`.

**Dropped:** none (Rocq 1 definition + 10 lemmas/theorems; Lean the same 11, + 3 Lean-only).
**Not ported:** the Ltacs (deviation 5) and the `Print Assumptions` lines (the lint's axiom check
covers them).
-/
import Weak.AxSpinVA6
import Weak.AxSpinVA6r
import Weak.AxSpinVA4
import Weak.AxLeafS

namespace Weak

open MachCSL
open Sail Sail.ConcurrencyInterfaceV1
open Sail.ArchSem (FreeM)
open LeanRV64D LeanRV64D.Functions

/-- (deviation 5) `ax_spin_va4_go` plus the print constants and the branch announce. -/
local macro "va7_go" : tactic => `(tactic| (ax_spin_va4_go; try (simp (config := { decide := true }) only [↓reduceIte, Bool.false_eq_true, get_config_print_exception]); ax_spin_va4_go))

/-! # 1. The tick (frame form) and the exception handler -/

/-- Rocq `F_tick_frame`. -/
theorem FTickFrame (img : Image) (t : ExecSt) (Ks : List ekey)
    (QE : List ekey → Sail.Error exception → ExecSt → Prop)
    (Q : List ekey → Unit → ExecSt → Prop) :
    (∀ t', tickFrame t t' → Q Ks () t') → FEC img QE Q Ks (tick_clock ()) t := by
  intro HQ
  refine FECMono img _ _ _ _ Ks _ t ?_ ?_
    (FECOfEvARfS img img _ _ _ t Ks rfSTick (sptTickFrame img t))
  · rintro _ _ _ ⟨_, ⟨⟩⟩
  · rintro Ks' ⟨⟩ t' ⟨rfl, hf⟩
    exact HQ t' hf

/-- (Lean-only) The branch announce: no label. -/
theorem AxSpinVA7.fBranchAnnounce {Y : Type} {img : Image}
    {QE : List ekey → Sail.Error exception → ExecSt → Prop} {Q : List ekey → Y → ExecSt → Prop}
    {n : Nat} {a : BitVec n} {f : Unit → SailM Y} {Ks : List ekey} {t : ExecSt}
    (H : FEC img QE Q Ks (f ()) t) : FEC img QE Q Ks (branch_announce n a >>= f) t :=
  .fcBa Ks n a _ t H

/-- Rocq `F_handle_exception`. -/
theorem FHandleException (img : Image) (t : ExecSt) (e : ExceptionType) (xv : BitVec 64)
    (Ks : List ekey) (QE : List ekey → Sail.Error exception → ExecSt → Prop)
    (Q : List ekey → Unit → ExecSt → Prop) :
    t.regs .cur_privilege = .Supervisor →
    (_get_Misa_S (t.regs .misa) == 1#1) = true →
    AxIntr.stvecDirect t.regs →
    bit_to_bool (BitVec.access (t.regs .medeleg)
      (BitVec.toNatInt (exceptionType_bits_forwards e))) = true →
    Q Ks () (xtrapSt t e xv) →
    FEC img QE Q Ks (handle_exception xv e) t := by
  intro Hp Hm Hd Hdel HQ
  have hES : exec (currentlyEnabled .Ext_S) (tm t t) = some (true, tm t t) := by
    rw [execCurrentlyEnabledS]; rw [show (tm t t).regs .misa = t.regs .misa from rfl, Hm]
  have Hdg := execExceptionDelegateeS e _ (tm t t) rfl hES Hdel
  replace Hdg := execAOfRfF _ (rfFExceptionDelegatee _ _) _ _ Hdg
  have Htr := execTrapHandlerSGen (tm t t) (.Exception e) (xtval_exception_value e xv)
    (t.regs .PC) (t.regs .mstatus) (t.regs .scause) (t.regs .stvec) (t.regs .elp)
    Hp rfl rfl rfl rfl Hm Hd
  replace Htr := execAOfRfF _ (rfFTrapHandlerS _ _ _ _) _ _ Htr
  unfold handle_exception
  va7_go
  rw [Hp]
  unfold exception_handler
  simp only [make_sync_exception]
  va7_go
  refine AxSpinVA3.fFactUse (μ := t) (rfFExceptionDelegatee _ _) Hdg ?_
  va7_go
  refine AxSpinVA3.fFact (P := fun Ks' x t' => Ks' = Ks ∧ x = stvecBase (t.regs .stvec) ∧
      t' = ⟨(AxSpinVA6.trapS9 (tm t t) (.Exception e) (xtval_exception_value e xv) (t.regs .PC)
        (t.regs .mstatus) (t.regs .scause) (t.regs .elp)).regs, t.mem, t.dev⟩)
    (FECExecARfFPost img _ _ _ (tm t t) _ _ t Ks (rfFTrapHandlerS _ _ _ _) Htr rfl
      ⟨rfl, rfl, rfl⟩) ?_
  rintro Ks' x t' ⟨rfl, rfl, rfl⟩
  unfold set_next_pc
  refine AxSpinVA7.fBranchAnnounce ?_
  va7_go
  exact .fcRet _ _ _ HQ

/-! # 2. The faulting fetches -/

/-- Rocq `F_fetch_misal`. -/
theorem FFetchMisal (img : Image) (va : BitVec 64) (Ks : List ekey)
    (Q : List ekey → FetchResult → ExecSt → Prop) (t : ExecSt) :
    t.regs .PC = va → (Sail.BitVec.access va 0 != 0#1) = true →
    Q Ks (.F_Error (.E_Fetch_Addr_Align (), va)) t →
    FEC img (fun _ _ _ => False) Q Ks (fetch ()) t := by
  intro HPC Hb0 HQ
  subst HPC
  unfold fetch
  apply FECCatchEarlyReturn
  va7_go
  simp only [Hb0, ↓reduceIte]
  va7_go
  exact .fcRet _ _ _ HQ

/-- Rocq `F_translateAddr_noncanon` (deviation 4): a NON-CANONICAL VA — the translation returns
`Err` after the register-only front. -/
theorem FTranslateAddrNoncanon (img : Image) (μ : ExecSt) (acc : MemoryAccessType mem_payload)
    (p : Privilege) (satp0 va : BitVec 64) (exc : ExceptionType)
    (Qf : List ekey → Result (physaddr × page_based_mem_type × Unit) (ExceptionType × Unit) →
      ExecSt → Prop)
    (Ks : List ekey) (t : ExecSt) :
    exec (effectivePrivilege acc (t.regs .mstatus) p) (tm μ t) = some (p, tm μ t) →
    exec (is_shadow_stack_access acc) (tm μ t) = some (false, tm μ t) →
    t.regs .cur_privilege = p →
    exec (translationMode p) (tm μ t) = some (.Sv39, tm μ t) →
    t.regs .satp = satp0 →
    (va != sign_extend (m := 64) (Sail.BitVec.extractLsb va 38 0)) = true →
    translationException acc (.PTW_Invalid_Addr ()) = pure exc →
    Qf Ks (.Err (exc, init_ext_ptw)) t →
    FEC img (fun _ _ _ => False) Qf Ks (translateAddr (.Virtaddr va) acc) t := by
  intro heff hss hcp htm hsatp hnc hte HQ
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
    hnc, ↓reduceIte, Nat.reduceSub]
  refine AxSpinVA3.fRUse (μ := μ) (rfFGetSatp _) hgs ?_
  refine AxSpinVA3.fRUse (μ := μ) (by trivial) rfl ?_
  ax_spin_va3_go
  rw [hte]
  ax_spin_va3_go
  exact .fcRet _ _ _ HQ

/-- Rocq `F_fetch_4_err`. -/
theorem FFetch4Err (img : Image) (va : BitVec 64) (exc : ExceptionType) (Ktr : List ekey)
    (Q : List ekey → FetchResult → ExecSt → Prop) (t : ExecSt) :
    t.regs .PC = va →
    is_aligned_vaddr (.Virtaddr va) 4 = true →
    FEC img (fun _ _ _ => False)
      (fun Ks' r t' => r = .Err (exc, init_ext_ptw) ∧ t'.regs .PC = va ∧
        Q Ks' (.F_Error (exc, va)) t')
      Ktr (translateAddr (.Virtaddr va) (.InstructionFetch ())) t →
    FEC img (fun _ _ _ => False) Q Ktr (fetch ()) t := by
  intro HPC Hal Htr
  have Hb0 := bit0ClearOfAligned4 _ Hal
  have Hb1 := bit1ClearOfAligned4 _ Hal
  have Hzi := execACurrentlyEnabledZiccif (tm t t)
  subst HPC
  unfold fetch
  apply FECCatchEarlyReturn
  va7_go
  simp only [Hb0, Bool.false_eq_true, ↓reduceIte]
  va7_go
  simp only [Hb1, Bool.false_eq_true, ↓reduceIte]
  va7_go
  simp only [Hal, ↓reduceIte]
  va7_go
  refine AxSpinVA3.fRUse (μ := t) rfFCurrentlyEnabledZiccif Hzi ?_
  va7_go
  refine AxSpinVA3.fRLift (P := fun Ks' x t' => x = .FetchBytes_Exception exc ∧
      t'.regs .PC = t.regs .PC ∧ Q Ks' (.F_Error (exc, t.regs .PC)) t') ?_ ?_
  · unfold fetch_bytes
    apply FECCatchEarlyReturn
    va7_go
    refine AxSpinVA3.fRLift Htr ?_
    rintro Ks' r t' ⟨rfl, HPC', HQ⟩
    va7_go
    exact .fcRet _ _ _ ⟨rfl, HPC', HQ⟩
  · rintro Ks' x t' ⟨rfl, HPC', HQ⟩
    va7_go
    rw [HPC']
    exact .fcRet _ _ _ HQ

/-- Rocq `F_fetch_2_err` (bit facts as premises, deviation 3). -/
theorem FFetch2Err (img : Image) (va : BitVec 64) (exc : ExceptionType) (Ktr : List ekey)
    (Q : List ekey → FetchResult → ExecSt → Prop) (t : ExecSt) :
    t.regs .PC = va →
    (_get_Misa_C (t.regs .misa) == 1#1) = true →
    (Sail.BitVec.access va 0 != 0#1) = false →
    (Sail.BitVec.access va 1 != 0#1) = true →
    is_aligned_vaddr (.Virtaddr va) 4 = false →
    FEC img (fun _ _ _ => False)
      (fun Ks' r t' => r = .Err (exc, init_ext_ptw) ∧ t'.regs .PC = va ∧
        Q Ks' (.F_Error (exc, va)) t')
      Ktr (translateAddr (.Virtaddr va) (.InstructionFetch ())) t →
    FEC img (fun _ _ _ => False) Q Ktr (fetch ()) t := by
  intro HPC HmisaC Hb0 Hb1 Hal4 Htr
  have Hzca := execACurrentlyEnabledZca (tm t t) HmisaC
  subst HPC
  unfold fetch
  apply FECCatchEarlyReturn
  va7_go
  simp only [Hb0, Bool.false_eq_true, ↓reduceIte]
  va7_go
  simp only [Hb1, ↓reduceIte]
  va7_go
  refine AxSpinVA3.fRUse (μ := t) rfFCurrentlyEnabledZca Hzca ?_
  va7_go
  simp only [Hal4, Bool.false_eq_true, ↓reduceIte]
  va7_go
  refine AxSpinVA3.fRLift (P := fun Ks' x t' => x = .FetchBytes_Exception exc ∧
      t'.regs .PC = t.regs .PC ∧ Q Ks' (.F_Error (exc, t.regs .PC)) t') ?_ ?_
  · unfold fetch_bytes
    apply FECCatchEarlyReturn
    va7_go
    refine AxSpinVA3.fRLift Htr ?_
    rintro Ks' r t' ⟨rfl, HPC', HQ⟩
    va7_go
    exact .fcRet _ _ _ ⟨rfl, HPC', HQ⟩
  · rintro Ks' x t' ⟨rfl, HPC', HQ⟩
    va7_go
    rw [HPC']
    exact .fcRet _ _ _ HQ

/-! # 3. The faulting step -/

/-- Rocq `fault_post`: the boundary after the fault — trap state, PC := nextPC (= stvec base). -/
def faultPost (t : ExecSt) (b : Bool) (e : ExceptionType) (va : BitVec 64) : ExecSt :=
  let t2 := xtrapSt (t.setReg .minstret_increment b) e va
  t2.setReg .PC (t2.regs .nextPC)

/-- Rocq `F_riscv_step_fault`. -/
theorem FRiscvStepFault (img : Image) (T : PTree) (satp0 : BitVec 64) (tick : Bool)
    (K0 Ks : List ekey) (e : ExceptionType) (va : BitVec 64)
    (Qf : List ekey → Unit → ExecSt → Prop) (t : ExecSt) :
    ctrlOkS T satp0 t.regs → AxIntr.stvecDirect t.regs →
    bit_to_bool (BitVec.access (t.regs .medeleg)
      (BitVec.toNatInt (exceptionType_bits_forwards e))) = true →
    (∀ b : Bool, FEC img (fun _ _ _ => False)
      (fun Ks' r t' => Ks' = Ks ∧ r = .F_Error (e, va) ∧ t' = t.setReg .minstret_increment b)
      K0 (fetch ()) (t.setReg .minstret_increment b)) →
    (∀ (b : Bool) (t' : ExecSt), tickFrame (faultPost t b e va) t' → Qf Ks () t') →
    FEC img QT Qf K0 (riscvStep tick) t := by
  intro Hc Hd Hdel Hf HQ
  unfold riscvStep
  refine AxSpinVA3.fFact (P := fun Ks' _ t' => Ks' = Ks ∧ ∃ b, t' = faultPost t b e va) ?_ ?_
  · unfold try_step
    dsimp only
    va7_go
    obtain ⟨b, Hb⟩ := execShouldIncMinstretSome (t.regs .cur_privilege) (tm t t)
    to_a Hb
    refine AxSpinVA3.fFactUse (μ := t) (rfFShouldIncMinstret _) Hb ?_
    va7_go
    have Hc1 := ctrlOkSMinstretInc T satp0 t b Hc
    have Hha : (t.setReg .minstret_increment b).regs .hart_state = .HART_ACTIVE () := Hc1.2.1
    refine AxSpinVA3.fFact (P := fun Ks' r t' => Ks' = Ks ∧
        r = .Step_Fetch_Failure (.Virtaddr va, e) ∧ t' = t.setReg .minstret_increment b) ?_ ?_
    · va7_go
      rw [Hha]
      dsimp only
      unfold run_hart_active
      apply FECCatchEarlyReturn
      va7_go
      refine AxSpinVA3.fRLift (P := fun Ks' r t' => Ks' = K0 ∧ r = none ∧
          t' = t.setReg .minstret_increment b)
        (FDisp img T satp0 _ K0 _ Hc1 ⟨rfl, rfl, rfl⟩) ?_
      rintro Ks' r t' ⟨rfl, rfl, rfl⟩
      va7_go
      refine AxSpinVA3.fRLift (Hf b) ?_
      rintro Ks' r t' ⟨rfl, rfl, rfl⟩
      va7_go
      exact .fcRet _ _ _ ⟨rfl, rfl, rfl⟩
    · rintro Ks' r t' ⟨hK, rfl, rfl⟩
      subst Ks'
      dsimp only
      have Hm1 : (_get_Misa_S ((t.setReg .minstret_increment b).regs .misa) == 1#1) = true := by
        rw [Hc1.2.2.1]; decide
      have Hd1 : AxIntr.stvecDirect (t.setReg .minstret_increment b).regs := by
        unfold AxIntr.stvecDirect at Hd ⊢
        rw [ExecSt.setReg_regs, RegFile.set_other _ _ _ _ (by decide)]
        exact Hd
      have Hdel1 : bit_to_bool (BitVec.access ((t.setReg .minstret_increment b).regs .medeleg)
          (BitVec.toNatInt (exceptionType_bits_forwards e))) = true := by
        rw [ExecSt.setReg_regs, RegFile.set_other _ _ _ _ (by decide)]
        exact Hdel
      refine AxSpinVA3.fFact (P := fun Ks' _ t' => Ks' = Ks ∧
          t' = xtrapSt (t.setReg .minstret_increment b) e va)
        (FHandleException img _ e (bits_of_virtaddr (.Virtaddr va)) Ks _ _ Hc1.1 Hm1 Hd1 Hdel1
          ⟨rfl, rfl⟩) ?_
      rintro Ks' _ t' ⟨rfl, rfl⟩
      have Hha2 : (xtrapSt (t.setReg .minstret_increment b) e va).regs .hart_state =
          .HART_ACTIVE () := by
        rw [xtrapStOther _ _ _ _ (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide)]
        exact Hha
      va7_go
      rw [Hha2]
      dsimp only
      unfold tick_pc
      va7_go
      exact .fcRet _ _ _ ⟨rfl, b, rfl⟩
  · rintro Ks' _ t' ⟨rfl, b, rfl⟩
    cases tick
    · exact .fcRet _ _ _ (HQ b _ (fun _ _ _ _ => rfl))
    · exact FTickFrame img _ _ _ _ (HQ b)

section thm7
variable (σi : ExecSt) (T : PTree) (satp0 : BitVec 64)
  (Hmode : _get_Satp64_Mode (Mk_Satp64 satp0) = 8#4)
  (Hasid : zero_extend (m := 16) (satp_to_asid satp0) = 0#16)
  (Hppn : BitVec.setWidth 44 (satp_to_ppn satp0) = T.base)

/-- Rocq `fault_post_facts`. -/
theorem faultPostFacts (t : ExecSt) (b : Bool) (e : ExceptionType) (va : BitVec 64)
    (t' : ExecSt) :
    ctrlOkS T satp0 t.regs → tickFrame (faultPost t b e va) t' →
    ctrlOkS T satp0 t'.regs ∧ t'.regs .PC = stvecBase (t.regs .stvec) ∧
    t'.regs .tlb = t.regs .tlb := by
  intro Hc Hfr
  have Hc1 := ctrlOkSMinstretInc T satp0 t b Hc
  have Hc2 := xtrapOkS T satp0 _ e va Hc1
  have Hc3 : ctrlOkS T satp0 (faultPost t b e va).regs := by
    refine ctrlOkSAgree T satp0 _ _ (fun r Hin => ?_) Hc2
    unfold faultPost
    dsimp only
    rw [ExecSt.setReg_regs]
    refine RegFile.set_other _ _ _ _ ?_
    intro He
    subst He
    exact absurd Hin (by decide)
  refine ⟨tickFrameCtrlS T satp0 _ _ Hfr Hc3, ?_, ?_⟩
  · rw [Hfr .PC (by decide) (by decide) (by decide)]
    unfold faultPost
    dsimp only
    rw [ExecSt.setReg_regs, RegFile.set_same, xtrapStNextPC, ExecSt.setReg_regs,
      RegFile.set_other _ _ _ _ (by decide)]
  · rw [Hfr .tlb (by decide) (by decide) (by decide)]
    unfold faultPost
    dsimp only
    rw [ExecSt.setReg_regs, RegFile.set_other _ _ _ _ (by decide),
      xtrapStOther _ _ _ _ (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide),
      ExecSt.setReg_regs, RegFile.set_other _ _ _ _ (by decide)]

/-- (Lean-only, deviation 1) THE MISALIGNED FAULT STEP: no label, and the next boundary is a
regime state at PC = stvec base with the TLB unchanged. -/
theorem AxSpinVA7.faultMisalStep (img : Image) (t : ExecSt) (va : BitVec 64) (n : Nat)
    (Ks : List ekey) :
    ctrlOkS T satp0 t.regs → t.regs .PC = va →
    (Sail.BitVec.access va 0 != 0#1) = true →
    AxIntr.stvecDirect t.regs →
    bit_to_bool (BitVec.access (t.regs .medeleg)
      (BitVec.toNatInt (exceptionType_bits_forwards (.E_Fetch_Addr_Align ())))) = true →
    (∀ t' : ExecSt, ctrlOkS T satp0 t'.regs → t'.regs .PC = stvecBase (t.regs .stvec) →
      t'.regs .tlb = t.regs .tlb → BFEC img n Ks t') →
    BFEC img (n + 1) Ks t := by
  intro Hc HPC Hb0 Hd Hdel Hk tick
  refine FRiscvStepFault img T satp0 tick Ks Ks (.E_Fetch_Addr_Align ()) va _ t Hc Hd Hdel ?_ ?_
  · intro b
    refine FFetchMisal img va Ks _ _ ?_ Hb0 ⟨rfl, rfl, rfl⟩
    rw [ExecSt.setReg_regs, RegFile.set_other _ _ _ _ (by decide)]
    exact HPC
  · intro b t' Hfr
    obtain ⟨Hc', HPC', Htlb'⟩ := faultPostFacts T satp0 t b _ va t' Hc Hfr
    exact Hk t' Hc' HPC' Htlb'

include Hmode in
/-- (Lean-only, deviation 1) THE NON-CANONICAL FAULT STEP (4-aligned PC). -/
theorem AxSpinVA7.faultNoncanonStep (img : Image) (t : ExecSt) (va : BitVec 64) (n : Nat)
    (Ks : List ekey) :
    ctrlOkS T satp0 t.regs → t.regs .PC = va →
    is_aligned_vaddr (.Virtaddr va) 4 = true →
    (va != sign_extend (m := 64) (Sail.BitVec.extractLsb va 38 0)) = true →
    AxIntr.stvecDirect t.regs →
    bit_to_bool (BitVec.access (t.regs .medeleg)
      (BitVec.toNatInt (exceptionType_bits_forwards (.E_Fetch_Page_Fault ())))) = true →
    (∀ t' : ExecSt, ctrlOkS T satp0 t'.regs → t'.regs .PC = stvecBase (t.regs .stvec) →
      t'.regs .tlb = t.regs .tlb → BFEC img n Ks t') →
    BFEC img (n + 1) Ks t := by
  intro Hc HPC Hal Hnc Hd Hdel Hk tick
  refine FRiscvStepFault img T satp0 tick Ks Ks (.E_Fetch_Page_Fault ()) va _ t Hc Hd Hdel ?_ ?_
  · intro b
    have Hc1 := ctrlOkSMinstretInc T satp0 t b Hc
    have Hc0 := Hc1
    obtain ⟨Hpriv, -, -, -, -, -, -, Hms, -, -, Hsatp, -⟩ := Hc0
    obtain ⟨-, HSXL, -⟩ := Hms
    have HPC1 : (t.setReg .minstret_increment b).regs .PC = va := by
      rw [ExecSt.setReg_regs, RegFile.set_other _ _ _ _ (by decide)]; exact HPC
    refine FFetch4Err img va (.E_Fetch_Page_Fault ()) Ks _ _ HPC1 Hal ?_
    refine FTranslateAddrNoncanon img t (.InstructionFetch ()) .Supervisor satp0 va
      (.E_Fetch_Page_Fault ()) _ Ks _
      (execEffectivePrivilegeFetch _ .Supervisor _) (execIsShadowStackFetch _) Hpriv
      (execTranslationModeSSv39 satp0 (tm t (t.setReg .minstret_increment b)) HSXL Hsatp Hmode)
      Hsatp Hnc rfl ?_
    exact ⟨rfl, HPC1, rfl, rfl, rfl⟩
  · intro b t' Hfr
    obtain ⟨Hc', HPC', Htlb'⟩ := faultPostFacts T satp0 t b _ va t' Hc Hfr
    exact Hk t' Hc' HPC' Htlb'

include Hmode Hasid Hppn in
/-- Rocq `chain_fault_misal`: THE MISALIGNED-PC ARM (deviation 1: the end key is `ENf`). -/
theorem chainFaultMisal (t : ExecSt) (va w spa p2 p1 : BitVec 64) :
    ctrlOkS T satp0 t.regs → t.regs .PC = va →
    (Sail.BitVec.access va 0 != 0#1) = true →
    AxIntr.stvecDirect t.regs →
    bit_to_bool (BitVec.access (t.regs .medeleg)
      (BitVec.toNatInt (exceptionType_bits_forwards (.E_Fetch_Addr_Align ())))) = true →
    is_aligned_vaddr (.Virtaddr (stvecBase (t.regs .stvec))) 4 = true →
    fetchable σi T (stvecBase (t.regs .stvec)) w spa p2 p1 →
    inRam spa 4 → is_aligned_paddr (.Physaddr spa) 4 = true →
    imgBytes (imgOf σi) (paZ spa) 4 = none →
    BFEC (imgOf σi) 2
      (walkKeys T (t.regs .tlb) (WeakKpt.svpnOf (stvecBase (t.regs .stvec))) p2 p1 ++
        [.ENf (paZ spa, 4)]) t := by
  intro Hc HPC Hb0 Hd Hdel Hal Hfa Hram Halp Hv
  refine AxSpinVA7.faultMisalStep T satp0 _ t va 1 _ Hc HPC Hb0 Hd Hdel ?_
  intro t' Hc' HPC' Htlb'
  rw [← Htlb']
  exact chainFetchMapped4 σi T satp0 Hmode Hasid Hppn t' _ w spa p2 p1 Hc' HPC' Hal Hfa Hram
    Halp Hv

include Hmode Hasid Hppn in
/-- Rocq `chain_fault_noncanon`: THE NON-CANONICAL-PC ARM, 4-aligned PC (deviation 1). -/
theorem chainFaultNoncanon (t : ExecSt) (va w spa p2 p1 : BitVec 64) :
    ctrlOkS T satp0 t.regs → t.regs .PC = va →
    is_aligned_vaddr (.Virtaddr va) 4 = true →
    (va != sign_extend (m := 64) (Sail.BitVec.extractLsb va 38 0)) = true →
    AxIntr.stvecDirect t.regs →
    bit_to_bool (BitVec.access (t.regs .medeleg)
      (BitVec.toNatInt (exceptionType_bits_forwards (.E_Fetch_Page_Fault ())))) = true →
    is_aligned_vaddr (.Virtaddr (stvecBase (t.regs .stvec))) 4 = true →
    fetchable σi T (stvecBase (t.regs .stvec)) w spa p2 p1 →
    inRam spa 4 → is_aligned_paddr (.Physaddr spa) 4 = true →
    imgBytes (imgOf σi) (paZ spa) 4 = none →
    BFEC (imgOf σi) 2
      (walkKeys T (t.regs .tlb) (WeakKpt.svpnOf (stvecBase (t.regs .stvec))) p2 p1 ++
        [.ENf (paZ spa, 4)]) t := by
  intro Hc HPC Hal Hnc Hd Hdel Hals Hfa Hram Halp Hv
  refine AxSpinVA7.faultNoncanonStep T satp0 Hmode _ t va 1 _ Hc HPC Hal Hnc Hd Hdel ?_
  intro t' Hc' HPC' Htlb'
  rw [← Htlb']
  exact chainFetchMapped4 σi T satp0 Hmode Hasid Hppn t' _ w spa p2 p1 Hc' HPC' Hals Hfa Hram
    Halp Hv

end thm7

end Weak
