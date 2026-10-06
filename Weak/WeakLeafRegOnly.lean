/-
Weak: **the ALIGNMENT-GENERIC register-only leaf kit** (M4): the fetch-only
trace `regonlyEs al4 pc` as a function of the alignment bit, its no-write and
footprint facts and certificate; the UNION recipe `wPEffOfLeafRegonly`
(`WeakFetchEff.wPEffOfLeafBase` and `WeakFetch2.wPEffOfLeafBase2` merged);
the csr-generic CSR-write check kit at `execEff`; and the successor register
frame of a one-cell-writing instruction.

Rocq: `iris/WeakLeafRegOnly.v` @ xxvzwolszwmp.

The Rocq header, in substance.  Every register-only M-mode instruction (the
csrw family, the csrr family, MRET) is fetched either at a 4-aligned pc (ONE
4-byte read, `wPEffOfLeafBase`) or at a 2-not-4-aligned pc (TWO 2-byte reads,
`wPEffOfLeafBase2`), and `start()` / `timerinit()` use BOTH alignments for the
SAME instruction shapes.  This file kills that axis once:
* §1 `regonlyEs al4 pc` with `nowriteRegonly`, the footprint
  `weffsTouchRegonly` and the certificate `wcertRegonly`.
* §2 `wPEffOfLeafRegonly`: the premise lists of `_base` and `_base2` merged
  (alignment premises `2-aligned = true` + `4-aligned = al4`; the misa.C
  premise required unconditionally), concluding at `regonlyEs al4 pc`.
* §3 the CSR-WRITE CHECK KIT: the `execEff` mirrors of
  `ExecSC7.execCheckCSRCsrwP` and the four `check_CSR_result` dispatchers.
* §3b `csrwSexecFactsR`, the successor register frame for
  `((s0.setReg mi b).setReg nextPC npc).setReg r v`.
No Iris here.

**Deviations from Rocq.**
1. NAMES / VOCABULARY: the tree's camelCase (map below) and
   `Weak/WeakFetchEff.lean` / `Weak/WeakFetch2.lean` deviation 1
   (`register_lookup r s.(sregs)` ↦ `s.regs r`, `eq_vec x 'b"1" = b` ↦
   `(x == 1#1) = b`, `add_vec_int` ↦ `BitVec.addInt`, `set_reg` ↦
   `ExecSt.setReg`, `mem`/`mdev` ↦ `.mem`/`.dev`, `pa_add pc j` ↦
   `pc + BitVec.ofNat 64 j`, `acc_addr` ↦ `WeakInterp.accAddr`,
   `∀ j < 4, addr_is_ram (pa_add pc j)` ↦ `inRam pc 4`, `dom (mem s) ⊆ W` ↦
   `bmDomSub s.mem W`, `RETIRE_SUCCESS` ↦ `.Retire_Success ()`,
   `pma_allows_all` ↦ `pma_regions = bootPMA`, `pmp_allows_all` ↦
   `pmpAllowsAll`, `W : _` ↦ `W : GSet PAddr`).
2. O2 (owner decision): the fetch trace elements are
   `.WEread WeakFetchEff.wakIfetch …` (Rocq `WEread wak_plain …`), as in
   WeakFetchEff/WeakFetch2.
3. `wPEffOfLeafRegonly` takes the O2 premise `fetchPin σ (regonlyEs al4 pc)`
   (as `wPEffOfLeafBase`/`wPEffOfLeafBase2`, their deviations 9/5); its
   premise order follows the Lean recipes (the pc/priv/pmp/pma/htif/hart
   tower, then misa.S, misa.C, MIE, elp).
4. §3: Lean's `check_CSR` tests the pure `check_CSR_access` directly (no
   `returnM` bind) and has no `and_boolM` (`WeakLeafEffCommon` deviation 2):
   `exec_eff_check_CSR_result_csrw_U_and`'s premise
   `is_CSR_accessible … = and_boolM (currentlyEnabled Ext_U) (returnM b)` is
   stated in the Lean model's own shape for menvcfg,
   `(do let x ← currentlyEnabled .Ext_U; pure (x && b))`.  `CSR_Check_OK tt` ↦
   `.CSR_Check_OK ()`; `mword 12` ↦ `BitVec 12`.
5. `csrw_sexec_facts_r`: `register_beq r r' = false` ↦ `r ≠ r'` (as
   `WeakLeafWin` deviation 4); `type_of_register r` ↦ `RegisterType r`; the
   `let s_exec := …` is inlined.
6. Rocq §4's `Print Assumptions` commands are not declarations.

**Rocq → Lean name map.**  `regonly_es` `regonlyEs`, `nowrite_regonly`
`nowriteRegonly`, `weffs_touch_regonly` `weffsTouchRegonly`, `wcert_regonly`
`wcertRegonly`, `wP_eff_of_leaf_regonly` `wPEffOfLeafRegonly`,
`exec_eff_check_CSR_csrw_p` `execEffCheckCSRCsrwP`,
`exec_eff_check_CSR_result_csrw_p` `execEffCheckCSRResultCsrwP`,
`exec_eff_check_CSR_result_csrw_pure` `execEffCheckCSRResultCsrwPure`,
`exec_eff_check_CSR_result_csrw_S` `execEffCheckCSRResultCsrwS`,
`exec_eff_check_CSR_result_csrw_U_and` `execEffCheckCSRResultCsrwUAnd`,
`exec_eff_check_CSR_result_csrw_U` `execEffCheckCSRResultCsrwU`,
`csrw_sexec_facts_r` `csrwSexecFactsR`.

**Dropped:** nothing (Rocq 1 definition + 11 lemmas; Lean 1 + 11).
-/
import Weak.WeakFetch2
import Weak.WeakLeafWin
import Weak.WeakLeafEffCommon

namespace Weak

open MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D LeanRV64D.Functions

/-! ## 1. The fetch-only trace, as a function of the alignment bit -/

/-- Rocq `regonly_es` (deviation 2). -/
def regonlyEs (al4 : Bool) (pc : BitVec 64) : List Weff :=
  if al4 then [.WEread WeakFetchEff.wakIfetch pc 4]
  else [.WEread WeakFetchEff.wakIfetch pc 2, .WEread WeakFetchEff.wakIfetch (BitVec.addInt pc 2) 2]

/-- Rocq `nowrite_regonly`. -/
theorem nowriteRegonly (al4 : Bool) (pc : BitVec 64) : nowriteTrace (regonlyEs al4 pc) := by
  cases al4
  · exact nowriteFetch2 pc
  · exact nowriteRead1 WeakFetchEff.wakIfetch pc 4

/-- Rocq `weffs_touch_regonly`: THE FETCH FOOTPRINT -- whatever the alignment,
the trace touches exactly the four text bytes of `pc`. -/
theorem weffsTouchRegonly (al4 : Bool) (pc : BitVec 64) (a : Int) :
    accWf pc 4 → weffsTouch (regonlyEs al4 pc) a →
    ∃ j : Nat, j < 4 ∧ a = WeakInterp.accAddr pc j := by
  intro hacc ⟨e, he, ht⟩
  have hhi : paZ (BitVec.addInt pc 2) = paZ pc + 2 := by
    have h := accWfByte pc 4 2 hacc (by omega)
    show paZ (pc + BitVec.ofNat 64 2) = paZ pc + 2
    rw [h]; unfold WeakInterp.accAddr; omega
  cases al4 with
  | true =>
    simp only [regonlyEs, if_true, List.mem_singleton] at he
    subst he
    obtain ⟨j, hj, rfl⟩ := ht
    exact ⟨j, hj, rfl⟩
  | false =>
    simp only [regonlyEs, Bool.false_eq_true, if_false, List.mem_cons, List.not_mem_nil,
      or_false] at he
    rcases he with rfl | rfl
    · obtain ⟨j, hj, rfl⟩ := ht
      exact ⟨j, by omega, rfl⟩
    · obtain ⟨j, hj, rfl⟩ := ht
      refine ⟨2 + j, by omega, ?_⟩
      unfold WeakInterp.accAddr
      rw [hhi]; omega

/-- Rocq `wcert_regonly`: the certificate every register-only leaf hands to the
funnel. -/
theorem wcertRegonly (al4 : Bool) (cid : Nat) (pc : BitVec 64) :
    wstepCert cid pc (wPEff (some cid) (regonlyEs al4 pc)) wQPure :=
  wcertNowrite cid pc (regonlyEs al4 pc) (nowriteRegonly al4 pc)

/-! ## 2. THE UNION RECIPE -/

/-- Rocq `wP_eff_of_leaf_regonly` (deviation 3): `wPEffOfLeafBase` and
`wPEffOfLeafBase2` at the EMPTY execute trace, the alignment as a parameter. -/
theorem wPEffOfLeafRegonly (al4 : Bool) (cid : Nat) (σ : Wmstate) (W : GSet PAddr)
    (pc : BitVec 64) (w : BitVec 32) (i : instruction)
    (D : Register → Bool) (dst : ExecSt) :
    -- the window
    wlogWf σ.wmLog →
    (∀ a, a ∈ W → paZ a ≠ 0) →
    (∀ a, a ∈ W → pinnedRead σ (paZ a)) →
    fetchPin σ (regonlyEs al4 pc) →
    -- the M-mode config tower
    σ.wmRegs .PC = pc →
    σ.wmRegs .cur_privilege = .Machine →
    pmpAllowsAll (σ.wmRegs .pmpcfg_n) →
    σ.wmRegs .pma_regions = bootPMA →
    σ.wmRegs .htif_tohost_base = none →
    σ.wmRegs .hart_state = .HART_ACTIVE () →
    (_get_Misa_S (σ.wmRegs .misa) == 1#1) = true →
    (_get_Misa_C (σ.wmRegs .misa) == 1#1) = true →
    (_get_Mstatus_MIE (σ.wmRegs .mstatus) == 1#1) = false →
    (σ.wmRegs .elp == landing_pad_bits_backwards .LP_EXPECTED) = false →
    -- (a) the text word, in the confined memory, at either alignment
    is_aligned_vaddr (.Virtaddr pc) 2 = true →
    is_aligned_vaddr (.Virtaddr pc) 4 = al4 →
    inRam pc 4 →
    (∀ j : Nat, j < 4 → wmemRestrict σ W (pc + BitVec.ofNat 64 j) = some (nthByte (n := 4) w j)) →
    isRVC (Sail.BitVec.extractLsb w 15 0) = false →
    -- (b) the decode
    (∀ r, D r = true → σ.wmRegs r = dst.regs r) →
    D .minstret_increment = false →
    goodb0 D (ext_decode w) dst = true →
    exec (ext_decode w) dst = some (i, dst) →
    is_lpad_instruction i = false →
    -- (c) the `execute`'s own `execEff` fact, at the EMPTY trace
    (∀ b : Bool, ∃ sExec : ExecSt,
      execEff (execute i)
        (((⟨σ.wmRegs, wmemRestrict σ W, σ.wmDev⟩ : ExecSt).setReg .minstret_increment b).setReg .nextPC
          (BitVec.addInt pc 4)) = some (.Retire_Success (), sExec, []) ∧
      sExec.regs .hart_state = .HART_ACTIVE () ∧
      sExec.regs .minstret_increment = b ∧
      bmDomSub sExec.mem W) →
    wPEff (some cid) (regonlyEs al4 pc) σ := by
  intro hwf hW0 hWp hfp lpc lpriv lpmp lpma lhtif lhart lmisaS lmisaC lmIE lelp hal2 hal4 hram htext
    hnotRVC hagree hDmi hgood hdec hnlpad hexec
  cases al4 with
  | true =>
    exact wPEffOfLeafBase cid σ W pc w i [] D dst hwf hW0 hWp hfp lpc lpriv lpmp lpma lhtif lhart
      lmisaS lmIE lelp hal4 hram htext hnotRVC hagree hDmi hgood hdec hnlpad hexec
  | false =>
    exact wPEffOfLeafBase2 cid σ W pc w i [] D dst hwf hW0 hWp hfp lpc lpriv lpmp lpma lhtif lhart
      lmisaS lmisaC lmIE lelp hal2 hal4 hram htext hnotRVC hagree hDmi hgood hdec hnlpad hexec

/-! ## 3. THE CSR-WRITE CHECK KIT, csr-generic -/

/-- Rocq `exec_eff_check_CSR_csrw_p` (deviation 4). -/
theorem execEffCheckCSRCsrwP (p : Privilege) (csr : BitVec 12) (s : ExecSt) :
    execEff (check_CSR_priv csr p) s = some (true, s, []) →
    check_CSR_access csr .CSRWrite = true →
    execEff (is_CSR_accessible csr p .CSRWrite) s = some (true, s, []) →
    execEff (stateen_allows_CSR_access csr p .CSRWrite) s = some (true, s, []) →
    execEff (check_CSR csr p .CSRWrite) s = some (true, s, []) := by
  intro hpriv hca hacc hst
  unfold check_CSR
  rw [execEffBindNil _ _ _ _ _ hpriv]
  simp only [↓reduceIte, hca]
  rw [execEffBindNil _ _ _ _ _ hacc]
  simpa only [↓reduceIte] using hst

/-- Rocq `exec_eff_check_CSR_result_csrw_p`. -/
theorem execEffCheckCSRResultCsrwP (p : Privilege) (csr : BitVec 12) (s : ExecSt) :
    execEff (check_CSR csr p .CSRWrite) s = some (true, s, []) →
    execEff (check_CSR_result csr p .CSRWrite) s = some (.CSR_Check_OK (), s, []) := by
  intro hcc
  unfold check_CSR_result
  rw [execEffBindNil _ _ _ _ _ hcc]
  rfl

/-- Rocq `exec_eff_check_CSR_result_csrw_pure`: pure-CSR (`is_CSR_accessible`
= `pure true`): mepc 0x341, … -/
theorem execEffCheckCSRResultCsrwPure (csr : BitVec 12) (s : ExecSt) :
    execEff (check_CSR_priv csr .Machine) s = some (true, s, []) →
    check_CSR_access csr .CSRWrite = true →
    execEff (is_CSR_accessible csr .Machine .CSRWrite) s = some (true, s, []) →
    execEff (stateen_allows_CSR_access csr .Machine .CSRWrite) s = some (true, s, []) →
    execEff (check_CSR_result csr .Machine .CSRWrite) s = some (.CSR_Check_OK (), s, []) := by
  intro h1 h2 h3 h4
  exact execEffCheckCSRResultCsrwP _ _ _ (execEffCheckCSRCsrwP _ _ _ h1 h2 h3 h4)

/-- Rocq `exec_eff_check_CSR_result_csrw_S`: Ext_S-gated CSRs (medeleg 0x302,
mideleg 0x303, sie 0x104, satp 0x180). -/
theorem execEffCheckCSRResultCsrwS (csr : BitVec 12) (s : ExecSt) :
    (_get_Misa_S (s.regs .misa) == 1#1) = true →
    execEff (check_CSR_priv csr .Machine) s = some (true, s, []) →
    check_CSR_access csr .CSRWrite = true →
    is_CSR_accessible csr .Machine .CSRWrite = currentlyEnabled .Ext_S →
    execEff (stateen_allows_CSR_access csr .Machine .CSRWrite) s = some (true, s, []) →
    execEff (check_CSR_result csr .Machine .CSRWrite) s = some (.CSR_Check_OK (), s, []) := by
  intro hS hpriv hca hacceq hst
  apply execEffCheckCSRResultCsrwP
  apply execEffCheckCSRCsrwP _ _ _ hpriv hca _ hst
  rw [hacceq, WeakFetchEff.execEffCurrentlyEnabledS, hS]

/-- Rocq `exec_eff_check_CSR_result_csrw_U_and` (deviation 4): U-gated CSRs
whose accessibility conjoins a config predicate -- menvcfg (0x30A). -/
theorem execEffCheckCSRResultCsrwUAnd (csr : BitVec 12) (b : Bool) (s : ExecSt) :
    (_get_Misa_U (s.regs .misa) == 1#1) = true →
    execEff (check_CSR_priv csr .Machine) s = some (true, s, []) →
    check_CSR_access csr .CSRWrite = true →
    is_CSR_accessible csr .Machine .CSRWrite = (do let x ← currentlyEnabled .Ext_U; pure (x && b)) →
    b = true →
    execEff (stateen_allows_CSR_access csr .Machine .CSRWrite) s = some (true, s, []) →
    execEff (check_CSR_result csr .Machine .CSRWrite) s = some (.CSR_Check_OK (), s, []) := by
  intro hU hpriv hca hacceq hb hst
  apply execEffCheckCSRResultCsrwP
  apply execEffCheckCSRCsrwP _ _ _ hpriv hca _ hst
  rw [hacceq, execEffBindNil _ _ _ _ _ (execEffCurrentlyEnabledU s hU), hb]
  rfl

/-- Rocq `exec_eff_check_CSR_result_csrw_U`. -/
theorem execEffCheckCSRResultCsrwU (csr : BitVec 12) (s : ExecSt) :
    (_get_Misa_U (s.regs .misa) == 1#1) = true →
    execEff (check_CSR_priv csr .Machine) s = some (true, s, []) →
    check_CSR_access csr .CSRWrite = true →
    is_CSR_accessible csr .Machine .CSRWrite = currentlyEnabled .Ext_U →
    execEff (stateen_allows_CSR_access csr .Machine .CSRWrite) s = some (true, s, []) →
    execEff (check_CSR_result csr .Machine .CSRWrite) s = some (.CSR_Check_OK (), s, []) := by
  intro hU hpriv hca hacceq hst
  apply execEffCheckCSRResultCsrwP
  apply execEffCheckCSRCsrwP _ _ _ hpriv hca _ hst
  rw [hacceq]
  exact execEffCurrentlyEnabledU s hU

/-! ## 3b. The successor register frame for a ONE-CELL-writing instruction -/

/-- Rocq `csrw_sexec_facts_r` (deviation 5). -/
theorem csrwSexecFactsR (r : Register) (s0 : ExecSt) (b : Bool) (npc : BitVec 64) (v : RegisterType r) :
    Register.hart_state ≠ r →
    Register.minstret_increment ≠ r →
    Register.nextPC ≠ r →
    (((s0.setReg .minstret_increment b).setReg .nextPC npc).setReg r v).regs .hart_state
        = s0.regs .hart_state ∧
      (((s0.setReg .minstret_increment b).setReg .nextPC npc).setReg r v).regs .minstret_increment = b ∧
      (((s0.setReg .minstret_increment b).setReg .nextPC npc).setReg r v).mem = s0.mem ∧
      (((s0.setReg .minstret_increment b).setReg .nextPC npc).setReg r v).dev = s0.dev ∧
      (((s0.setReg .minstret_increment b).setReg .nextPC npc).setReg r v).regs .nextPC = npc := by
  intro hhs hmi hnpc
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [setLookupNe _ _ _ _ hhs, setLookupNe _ _ _ _ (by decide), setLookupNe _ _ _ _ (by decide)]
  · rw [setLookupNe _ _ _ _ hmi, setLookupNe _ _ _ _ (by decide)]
    simp only [ExecSt.setReg_regs, RegFile.set_same]
  · simp only [ExecSt.setReg_mem]
  · simp only [ExecSt.setReg_dev]
  · rw [setLookupNe _ _ _ _ hnpc]
    simp only [ExecSt.setReg_regs, RegFile.set_same]

end Weak
