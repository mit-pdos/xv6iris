/-
Weak: **the M-mode `amoswap.w.aq` leaf, end to end -- THE lock instruction**
(M4 batch 2): the trace-pin fact, the `execute` at an arbitrary state, the
`wPEffPin` half, the leaf concluding `WeakAcquire.wacqCb`, and the slot-in check
against `WeakBranch.wwpAcquireLoopReal`.

Rocq: `iris/WeakLeafAmo4Leaf.v` @ xxvzwolszwmp.

The Rocq header, in substance.  The last batch-2 shape and the most novel one:
TWO ADJACENT memory effects (`WEread aka ea 4; WEwrite akw ea 4 v` -- the
acquire-flavoured read of the OLD lock word immediately followed by the
exclusive write of the NEW one), and a read half that fires in INVARIANT FORM:
the leaf owns NOTHING at the lock word and carries no view hypothesis about the
acquirer, because the read's access kind is latest (`akPins`).
THE ALTITUDE IS `WeakAcquire.wacqCb`, NOT THE FUNNEL: the lock library
(`wwpAcquireSwap`, `wwpAcquireLoopReal`) opens the lock invariant itself, hands
the leaf the lock word `v` the swap will return and runs `wacquireCore` on the
way back; so this leaf's deliverable is the ATTEMPT premise those lemmas
consume, a lemma concluding `wacqCb`, from SC-style resources.  Because
`wacqCb` sits directly on `WeakInstr.wpWinstr`, the `riscvStep` wrapper and the
register bookkeeping that `WeakFunnel.wwpInstr` does for an owned-memory leaf
are done HERE (§5 reuses the funnel's own pieces `wwpStepExec`,
`wwpRetireRegs`, `wwpTickRegs`, `mConfRegFacts`).  The certificate chain is
`WeakCert`'s pin form: the confinement premise is trace-keyed (`tracePin`), and
for this instruction it collapses to "the four TEXT bytes are fetch-pinned"
(free from `WeakFunnel.winstrTextPinned`) because the AMO's read pins itself
and a write is not a read (`amo4TracePin`, §2).
LAYOUT: §2 the trace-pin fact (the window is the shared kit's
`WeakLeafWin.wwin pc ea 4`); §3 the `execute` at an arbitrary `s0`
(`execEffAmo4At`, wrapping `WeakLeafAmo4.execEffExecuteAMOSWAP4Gpr`; FOUR MMIO
gates, both HTIF windows) and the successor's register facts
(`amo4SexecFacts`); §4 the `wPEffPin` half (`wPEffPinAmo4`, one application of
`WeakFetchEff.wPEffPinOfLeafBase`); §5 the leaf `wwpAmo4AcqLeaf` and the
slot-in check `wwpAmo4AcquireLoop`.  Every pure/geometry side condition is a
premise.

**Deviations from Rocq.**
1. NAMES / VOCABULARY: the tree's camelCase (map below); none of this file's
   Rocq names is in the duplicated-name table.  As `Weak/WeakLeafWin.lean`
   deviation 1, `Weak/WeakLeafAmo4.lean` deviation 1 and `Weak/WeakFunnel.lean`
   deviation 1: `register_lookup r s.(sregs)` ↦ `s.regs r`; `eq_vec x 'b"1" = b`
   ↦ `(x == 1#1) = b`; `if uint rs =? 0 then zero_reg else register_lookup
   (R_bitvector_64 (gpr_of_Z (uint rs))) f` ↦ `uxaXget f rs` (`s.gpr rs` at an
   `ExecSt`); `uint rd <> 0` ↦ `rd.toNat ≠ 0`; `add_vec x (zeros' 64)` ↦
   `x + zeros (n := 64)`; Rocq's `sign_extend' (8 * __id 4) (trunc …)` ↦
   `sign_extend (m := 32) (trunc (m := 32) …)` (WeakLeafAmo4's `amoM4Store`);
   the loaded value `regval_into_reg (sign_extend' 64 (autocast v))` ↦
   `sign_extend (m := 64) v`; the byte window ↦ `BytesAt`; `pa_add a j` ↦
   `a + BitVec.ofNat 64 j`; `AkInfo false true true` ↦ `⟨false, true, true⟩`;
   `add_vec_int` ↦ `BitVec.addInt`; `fin_to_nat cpu_id` ↦ `cpu.val`; `WWP
   Loop` ↦ `wwpTriv ⊤ (WExpr.loop gen cpu)`; `locked γ cpu_id` ↦
   `lockedEx γ cpu`; `hart_ws` ↦ `hartWs`; `ws_le` ↦ `wsLe`; `pc_is` ↦ `pcIs`.
2. RAM, PMA, PMP: Rocq's per-byte `addr_is_ram (pa_add ea j)` ↦ `inRam ea 4`
   (WeakFunnel deviation 2); `pma_allows_all` ↦ `pma_regions = bootPMA`; Rocq's
   `pmp_all_off` (every entry OFF) is WEAKENED to the funnel's
   `pmpAllowsAll` (no entry locked): the M-mode AMO's PMP check is discharged
   by `WeakPmpEff.execEffPmpCheckMachineUnlocked` (the access is one aligned
   4-byte cell), so the leaf takes exactly the funnel's PMP premise.
3. O2 (owner decision; `Weak/WeakCert.lean` deviation 4): the fetch's trace
   element is `.WEread WeakFetchEff.wakIfetch pc 4` (Rocq `WEread wak_plain pc
   4`), so `amo4TracePin`'s premise is the FETCH pin `fetchPinned` of the text
   bytes (Rocq `pinned_read`), and Lean's `tracePin` also carries
   `fetchFresh`, proved here by computation.
4. §3: `exec_eff_amo4_at`'s successor `set_reg (MState (sregs s) (write_bytes
   (mem s0) ea 4 sv) (mdev s0)) (R_bitvector_64 …) x` ↦
   `(s.setMem (bmWrite s0.mem ea 4 sv)).setGpr rd x` (WeakLeafAmo4 deviation
   1); `amo4_sexec_facts`'s `let` and its arbitrary `M D` are stated on that
   shape (`M : BMap`; the device is `s0.dev`, which the shape fixes).
5. §5, THE CONFIG INTERFACE (owner decision Q3, option A; WeakFunnel deviation
   7): Rocq `mmode_config (DfracOwn q)` ∗ `pmpcfg_n ↦ᵣ{q} pmpcfg0` ↦
   `mConf cpu dq c ∗ clockCells cpu` (the PMP cell is `mConf`'s own, the
   premise `pmp_all_off pmpcfg0` is `pmpAllowsAll c.pmpcfg`, the mstatus facts
   are `MConf.mok c`); no `MinstretInv` is opened (the clock cells are owned and
   held across the step), so Rocq's masks `⊤ ∖ ↑wlockN ∖ ↑minstretN` are
   `⊤ ∖ ↑wlockN`.  The continuation receives `mConf cpu dq c` and
   `clockCells cpu` back.  The GPR cells `R_bitvector_64 (gpr_of_Z (uint r)) ↦ᵣ
   x` ↦ `gpr cpu r (DFrac.own 1) x`.  Rocq's decode-agreement premise over
   `register_lookup mseccfg rs = mword_of_int 0` ↦ `rs .mseccfg = 0#64`;
   `MISA_C` ↦ `misaC`; `decode_fetch` ↦ `decodeFetch`.
6. Lean-only helpers (file-qualified): `WeakLeafAmo4Leaf.preLookup`,
   `WeakLeafAmo4Leaf.preGpr` (the two funnel pre-writes are invisible to every
   other register / every GPR), `WeakLeafAmo4Leaf.amoM4PaEq` (the AMO's
   physical address is its effective address).  Rocq's `reg_valid` /
   `reg_update` at `R_bitvector_64 (gpr_of_Z (uint r))` are the shared
   `WeakLeafLw4.gprValid` / `WeakLeafLw4.gprUpdate` (the `gpr` cell against
   `regInterp`).
7. Rocq §6's `Print Assumptions` commands are not declarations.

**Rocq → Lean name map.**  `amo4_trace_pin` `amo4TracePin`, `exec_eff_amo4_at`
`execEffAmo4At`, `amo4_sexec_facts` `amo4SexecFacts`, `wP_eff_pin_amo4`
`wPEffPinAmo4`, `wwp_amo4_acq_leaf` `wwpAmo4AcqLeaf`, `wwp_amo4_acquire_loop`
`wwpAmo4AcquireLoop`.

**Dropped:** nothing (6 Rocq `Lemma`s; Lean 6 theorems + 3 Lean-only).
-/
import Weak.WeakBranch
import Weak.WeakFetchEff
import Weak.WeakLeafWin
import Weak.WeakLeafAmo4
import Weak.ExecSC8
import Weak.WeakLeafLw4

namespace Weak

open Iris Iris.BI Iris.BI.MonPred Iris.ProofMode Iris.Std
open MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D LeanRV64D.Functions

/-! ## 2. THE TRACE-PIN FACT (the window is `WeakLeafWin.wwin pc ea 4`) -/

/-- Rocq `amo4_trace_pin` (deviation 3): the fetch is the only non-pinning
read (its footprint is the TEXT, fetch-pinned for free), the AMO's read pins
itself, and a write is not a read. -/
theorem amo4TracePin (σ : Wmstate) (pc lk : PAddr) (v : BitVec 32) :
    (∀ j : Nat, j < 4 → fetchPinned σ (WeakInterp.accAddr pc j)) →
    tracePin σ [.WEread WeakFetchEff.wakIfetch pc 4, .WEread ⟨false, true, true⟩ lk 4,
      .WEwrite ⟨false, true, false⟩ lk 4 v] := by
  intro hpc
  unfold tracePin
  refine ⟨?_, ?_⟩
  · intro ak pa n hin hnp j hj
    simp only [List.mem_cons, List.not_mem_nil, _root_.or_false] at hin
    rcases hin with h | h | h
    · injection h with h1 h2 h3
      subst h1 h2 h3
      unfold readPinned
      exact hpc j hj
    · injection h with h1 h2 h3
      subst h1
      exact absurd hnp (by decide)
    · cases h
  · simp only [fetchFresh]
    refine ⟨?_, ?_, ?_, trivial⟩
    · intro ak pa n hin hif
      simp only [List.mem_cons, List.not_mem_nil, _root_.or_false] at hin
      rcases hin with h | h
      · injection h with h1
        subst h1
        exact absurd hif (by decide)
      · cases h
    · intro ak pa n hin
      simp only [List.mem_cons, List.not_mem_nil, _root_.or_false] at hin
      cases hin
    · intro ak pa n hin
      cases hin

/-! ## 3. THE `execute` AT AN ARBITRARY `s0` -/

/-- Lean-only: the funnel's two pre-writes are invisible to any other register. -/
theorem WeakLeafAmo4Leaf.preLookup (s0 : ExecSt) (b : Bool) (npc : BitVec 64) (r : Register)
    (h1 : r ≠ .nextPC) (h2 : r ≠ .minstret_increment) :
    ((s0.setReg .minstret_increment b).setReg .nextPC npc).regs r = s0.regs r := by
  rw [setLookupNe r .nextPC _ _ h1, setLookupNe r .minstret_increment _ _ h2]

/-- Lean-only: ... in particular to every GPR. -/
theorem WeakLeafAmo4Leaf.preGpr (s0 : ExecSt) (b : Bool) (npc : BitVec 64) (i : BitVec 5) :
    ((s0.setReg .minstret_increment b).setReg .nextPC npc).gpr i = s0.gpr i := by
  unfold ExecSt.gpr
  apply uxaXget_congr
  intro r hr
  apply WeakLeafAmo4Leaf.preLookup
  · rintro rfl; revert hr; decide
  · rintro rfl; revert hr; decide

/-- Lean-only: the AMO's physical address is its effective address (identity
translation, no pointer masking). -/
theorem WeakLeafAmo4Leaf.amoM4PaEq (rs1 : BitVec 5) (s : ExecSt) :
    amoM4Pa rs1 s = amoM4Ea rs1 s := by
  unfold amoM4Pa amoM4A8
  rw [pmTransformPA0]
  simp only [bits_of_virtaddr, zero_extend, Sail.BitVec.zeroExtend, BitVec.setWidth_eq]

/-- Rocq `exec_eff_amo4_at` (deviations 2, 4): `execEffExecuteAMOSWAP4Gpr` with
the funnel-shaped two pre-writes on top, at an arbitrary state. -/
theorem execEffAmo4At (s0 : ExecSt) (b : Bool) (pc : BitVec 64) (rs1 rs2 rd : BitVec 5)
    (ea : PAddr) (w sv : BitVec 32) :
    rd.toNat ≠ 0 →
    s0.regs .cur_privilege = .Machine →
    (_get_Mstatus_MPRV (s0.regs .mstatus) == 1#1) = false →
    pmm_mode_backwards (_get_Seccfg_PMM (s0.regs .mseccfg)) = .PMM_Disabled →
    pmpAllowsAll (s0.regs .pmpcfg_n) →
    s0.regs .pma_regions = bootPMA →
    s0.regs .htif_tohost_base = none →
    s0.gpr rs1 + zeros (n := 64) = ea →
    sign_extend (m := 32) (trunc (m := 32) (s0.gpr rs2)) = sv →
    is_aligned_paddr (.Physaddr ea) 4 = true →
    inRam ea 4 →
    BytesAt s0 ea 4 w →
    execEff (execute (.AMO (.AMOSWAP, true, false, .Regidx rs2, .Regidx rs1, 4, .Regidx rd)))
        ((s0.setReg .minstret_increment b).setReg .nextPC (BitVec.addInt pc 4)) =
      some (RETIRE_SUCCESS,
        (((s0.setReg .minstret_increment b).setReg .nextPC (BitVec.addInt pc 4)).setMem
          (bmWrite s0.mem ea 4 sv)).setGpr rd (sign_extend (m := 64) w),
        [.WEread ⟨false, true, true⟩ ea 4, .WEwrite ⟨false, true, false⟩ ea 4 sv]) := by
  intro hrd lpriv lmprv lpmm lpmp lpma lhtif hea hsv hal hram hbytes
  have L : ∀ r : Register, r ≠ .nextPC → r ≠ .minstret_increment →
      ((s0.setReg .minstret_increment b).setReg .nextPC (BitVec.addInt pc 4)).regs r = s0.regs r :=
    fun r h1 h2 => WeakLeafAmo4Leaf.preLookup s0 b _ r h1 h2
  have hpa : amoM4Pa rs1 ((s0.setReg .minstret_increment b).setReg .nextPC (BitVec.addInt pc 4)) = ea := by
    rw [WeakLeafAmo4Leaf.amoM4PaEq]
    unfold amoM4Ea
    rw [WeakLeafAmo4Leaf.preGpr]
    exact hea
  have ha8 : amoM4A8 rs1 ((s0.setReg .minstret_increment b).setReg .nextPC (BitVec.addInt pc 4)) = ea := by
    have e : amoM4A8 rs1 ((s0.setReg .minstret_increment b).setReg .nextPC (BitVec.addInt pc 4)) =
        amoM4Pa rs1 ((s0.setReg .minstret_increment b).setReg .nextPC (BitVec.addInt pc 4)) := by
      unfold amoM4Pa
      simp only [zero_extend, Sail.BitVec.zeroExtend, BitVec.setWidth_eq]
    rw [e, hpa]
  have hst : amoM4Store rs2 ((s0.setReg .minstret_increment b).setReg .nextPC (BitVec.addInt pc 4)) = sv := by
    unfold amoM4Store
    rw [WeakLeafAmo4Leaf.preGpr]
    exact hsv
  have h4 := isAlignedVaddrMod ea 4 (by decide) hal
  have h := execEffExecuteAMOSWAP4Gpr rs2 rs1 rd ramRegion w
    ((s0.setReg .minstret_increment b).setReg .nextPC (BitVec.addInt pc 4)) hrd
    (by rw [L _ (by decide) (by decide)]; exact lpriv)
    (by rw [L _ (by decide) (by decide)]; exact lmprv)
    (by rw [L _ (by decide) (by decide)]; exact lpmm)
    (by rw [ha8]; exact hal)
    (by
      rw [hpa]
      exact execEffPmpCheckMachineUnlocked _ 4 _ _
        (by rw [L _ (by decide) (by decide)]; exact lpmp) (fun _ => ⟨_, rfl⟩)
        (by show ea.toNat % 4 + (to_bits (l := 64) 4).toNat ≤ 4
            rw [show (to_bits (l := 64) 4).toNat = 4 from rfl]; omega))
    (by rw [L _ (by decide) (by decide), lpma, hpa]
        exact matching_pma_ram ea 4 hram (by decide) (by decide))
    (by rw [hpa]; exact hal)
    (by first | rfl | decide +kernel)
    (by first | rfl | decide +kernel)
    (by first | rfl | decide +kernel)
    (by rw [hpa, within_clint_ram ea 4 hram]; rfl)
    (by
      first
      | rfl
      | (simp only [within_sig, plat_have_sig, Functions.not]; rfl))
    (execEffWithinHtifFalse _ 4 _ (by rw [L _ (by decide) (by decide)]; exact lhtif))
    (execEffWithinHtifWFalse _ 4 _ (by rw [L _ (by decide) (by decide)]; exact lhtif))
    (by rw [hpa]; exact devAddrRam ea 4 hram)
    (by rw [hpa]; exact hbytes)
  rw [hpa, hst] at h
  exact h

/-- Rocq `amo4_sexec_facts` (deviation 4): the successor's bookkeeping facts,
at the AMO-class shape (one memory replacement under one GPR write over the
pre-write tower). -/
theorem amo4SexecFacts (s0 : ExecSt) (b : Bool) (npc : BitVec 64) (rd : BitVec 5) (M : BMap)
    (x : BitVec 64) :
    ((((s0.setReg .minstret_increment b).setReg .nextPC npc).setMem M).setGpr rd x).regs .hart_state =
        s0.regs .hart_state ∧
    ((((s0.setReg .minstret_increment b).setReg .nextPC npc).setMem M).setGpr rd x).regs
        .minstret_increment = b ∧
    ((((s0.setReg .minstret_increment b).setReg .nextPC npc).setMem M).setGpr rd x).regs .nextPC = npc ∧
    ((((s0.setReg .minstret_increment b).setReg .nextPC npc).setMem M).setGpr rd x).mem = M ∧
    ((((s0.setReg .minstret_increment b).setReg .nextPC npc).setMem M).setGpr rd x).dev = s0.dev := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [WeakLeafWin.setGprRegsNe _ _ _ _ (by decide)]
    exact WeakLeafAmo4Leaf.preLookup s0 b npc .hart_state (by decide) (by decide)
  · rw [WeakLeafWin.setGprRegsNe _ _ _ _ (by decide)]
    exact (storeRegsFacts s0 b npc).2.1
  · rw [WeakLeafWin.setGprRegsNe _ _ _ _ (by decide)]
    exact (storeRegsFacts s0 b npc).2.2
  · rw [WeakLeafWin.setGprMem]; rfl
  · rw [WeakLeafWin.setGprDev]; rfl


/-! ## 4. THE `wPEffPin` HALF, over the resources

The lock word's flat bytes arrive as a PURE premise (handed by
`WeakAcquire.wacqCb`, off the invariant's elements): no ownership, no view
hypothesis. -/

section wPEffHalf
variable {GF : BundledGFunctors} [WeakGS GF]

/-- Rocq `wP_eff_pin_amo4`. -/
theorem wPEffPinAmo4 (cid : Nat) (σ : Wmstate) (pc : BitVec 64) (w : BitVec 32)
    (rs1 rs2 rd : BitVec 5) (lk : PAddr) (v sv : BitVec 32) (D : Register → Bool) (dst : ExecSt) :
    wlogWf σ.wmLog →
    -- the M-mode config tower, at σ's own registers
    σ.wmRegs .PC = pc →
    σ.wmRegs .cur_privilege = .Machine →
    pmpAllowsAll (σ.wmRegs .pmpcfg_n) →
    σ.wmRegs .pma_regions = bootPMA →
    σ.wmRegs .htif_tohost_base = none →
    σ.wmRegs .hart_state = .HART_ACTIVE () →
    (_get_Misa_S (σ.wmRegs .misa) == 1#1) = true →
    (_get_Mstatus_MIE (σ.wmRegs .mstatus) == 1#1) = false →
    (_get_Mstatus_MPRV (σ.wmRegs .mstatus) == 1#1) = false →
    pmm_mode_backwards (_get_Seccfg_PMM (σ.wmRegs .mseccfg)) = .PMM_Disabled →
    (σ.wmRegs .elp == landing_pad_bits_backwards .LP_EXPECTED) = false →
    -- the instruction's pure geometry
    is_aligned_vaddr (.Virtaddr pc) 4 = true →
    isRVC (Sail.BitVec.extractLsb w 15 0) = false →
    rd.toNat ≠ 0 →
    uxaXget σ.wmRegs rs1 + zeros (n := 64) = lk →
    sign_extend (m := 32) (trunc (m := 32) (uxaXget σ.wmRegs rs2)) = sv →
    is_aligned_paddr (.Physaddr lk) 4 = true →
    inRam lk 4 →
    -- the lock word's flat bytes: the INVARIANT-FORM premise
    (∀ j : Nat, j < 4 →
      wflatMem σ.wmImg σ.wmLog (lk + BitVec.ofNat 64 j) = some (nthByte (n := 4) v j)) →
    -- the decode, exactly as the decode library states it
    (∀ r, D r = true → σ.wmRegs r = dst.regs r) →
    D .minstret_increment = false →
    goodb0 D (ext_decode w) dst = true →
    exec (ext_decode w) dst =
      some (.AMO (.AMOSWAP, true, false, .Regidx rs2, .Regidx rs1, 4, .Regidx rd), dst) →
    -- the resources
    wlatInterp (GF := GF) σ.wmImg σ.wmLog ⊢
      winstrBytes (GF := GF) pc (.F_Base w) -∗
        ⌜wPEffPin (some cid) ([.WEread WeakFetchEff.wakIfetch pc 4] ++
          [.WEread ⟨false, true, true⟩ lk 4, .WEwrite ⟨false, true, false⟩ lk 4 sv]) σ⌝ := by
  intro hwf lpc lpriv lpmp lpma lhtif lhart lmisaS lmIE lmprv lpmm lelp hal4 hnotRVC hrd hea hsv halk hram
    hflat hagree hDmi hgood hdec
  iintro Hlat #Hbs
  icases keepPure (winstrFlat σ pc _ hwf) $$ Hlat Hbs with ⟨%hfok, Hlat, -⟩
  ihave %hpin := winstrTextPinned σ pc _ hwf $$ Hlat Hbs
  ipureintro
  obtain ⟨_, hrampc, w', ⟨hww, _⟩, htext⟩ := hfok
  subst hww
  apply wPEffPinOfLeafBase cid σ (wwin pc lk 4) pc w _ _ D dst hwf
    (wwinNonzero pc lk 4 (fun j hj => WeakLeafWin.inRamByte pc 4 j hrampc hj)
      (fun j hj => WeakLeafWin.inRamByte lk 4 j hram hj))
    (amo4TracePin σ pc lk sv (fun j hj => (hpin j hj).2))
    lpc lpriv lpmp lpma lhtif lhart lmisaS lmIE lelp hal4 hrampc (wwinConfText σ pc lk 4 _ htext) hnotRVC
    hagree hDmi hgood hdec rfl
  intro b
  refine ⟨_, execEffAmo4At ⟨σ.wmRegs, wmemRestrict σ (wwin pc lk 4), σ.wmDev⟩ b pc rs1 rs2 rd lk v sv hrd
    lpriv lmprv lpmm lpmp lpma lhtif hea hsv halk hram (wwinConfData σ pc lk 4 (k := 4) v hflat), ?_, ?_, ?_⟩
  · exact (amo4SexecFacts _ b _ rd _ _).1.trans lhart
  · exact (amo4SexecFacts _ b _ rd _ _).2.1
  · rw [(amo4SexecFacts ⟨σ.wmRegs, wmemRestrict σ (wwin pc lk 4), σ.wmDev⟩ b (BitVec.addInt pc 4) rd
      (bmWrite (wmemRestrict σ (wwin pc lk 4)) lk 4 sv) (sign_extend (m := 64) v)).2.2.2.1]
    exact wwinWdom σ pc lk 4 sv

end wPEffHalf

/-! ## 5. THE LEAF -- the attempt premise of the lock library

`wwpAmo4AcqLeaf` concludes `WeakAcquire.wacqCb … pc P` with `P := wPEffPin …
[fetch; read; write]`, so a caller instantiates `WeakBranch.wwpAcquireLoopReal`'s
attempt premise with it directly (certificate: `wcertAmoAqPinBase4`).  The
`riscvStep` wrapper is assembled here from the funnel's own pieces; the
continuation is taken under `▷` so the failure arm can be built from the loop's
`▷ (Kb -∗ WP)` retry edge. -/

section leaf
variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [WeakGS GF] [LockExG GF]

/-- Rocq `wwp_amo4_acq_leaf` (deviation 5). -/
theorem wwpAmo4AcqLeaf (gen : Nat) (cpu : CPU) (γ : GName) (lk : PAddr) (R : VProp GF)
    (pc : BitVec 64) (w : BitVec 32) (rs1 rs2 rd : BitVec 5) (c : MConf) (dq : DFrac)
    (rs1v rs2v rd0 npc0 : BitVec 64) (D : Register → Bool) (dst : ExecSt) (ws : Wstate) :
    MConf.mok c →
    pmpAllowsAll c.pmpcfg →
    is_aligned_vaddr (.Virtaddr pc) 4 = true →
    rs1.toNat ≠ 0 →
    rs2.toNat ≠ 0 →
    rd.toNat ≠ 0 →
    rs1v + zeros (n := 64) = lk →
    -- the stored value IS the lock constant: `rs2` holds 1
    sign_extend (m := 32) (trunc (m := 32) rs2v) = lockOne →
    is_aligned_paddr (.Physaddr lk) 4 = true →
    inRam lk 4 →
    -- the decode, in the two shapes its two consumers ask for
    (∀ t : ExecSt,
      privMSU (t.regs .cur_privilege) = true →
      (_get_Misa_C (t.regs .misa) == 1#1) = true →
      (_get_Misa_A (t.regs .misa) == 1#1) = true →
      t.regs .misa = misaC →
      cfgOk t →
      exec (decodeFetch (.F_Base w)) t =
        some (.AMO (.AMOSWAP, true, false, .Regidx rs2, .Regidx rs1, 4, .Regidx rd), t)) →
    (∀ rs : RegFile,
      rs .cur_privilege = .Machine →
      rs .misa = misaC →
      rs .mseccfg = 0#64 →
      ∀ r, D r = true → rs r = dst.regs r) →
    D .minstret_increment = false →
    goodb0 D (ext_decode w) dst = true →
    exec (ext_decode w) dst =
      some (.AMO (.AMOSWAP, true, false, .Regidx rs2, .Regidx rs1, 4, .Regidx rd), dst) →
    mConf (GF := GF) cpu dq c ⊢
      clockCells cpu -∗
      Register.PC ↦ᵣ[cpu] pc -∗
      Register.nextPC ↦ᵣ[cpu] npc0 -∗
      gpr cpu rs1 (DFrac.own 1) rs1v -∗
      gpr cpu rs2 (DFrac.own 1) rs2v -∗
      gpr cpu rd (DFrac.own 1) rd0 -∗
      winstrBytes (GF := GF) pc (.F_Base w) -∗
      hartWs (GF := GF) cpu ws -∗
      ▷ (∀ (v : BitVec 32) (ws' : Wstate),
          ⌜wsLe ws ws'⌝ -∗
          mConf cpu dq c -∗
          clockCells cpu -∗
          pcIs cpu (BitVec.addInt pc 4) -∗
          gpr cpu rs1 (DFrac.own 1) rs1v -∗
          gpr cpu rs2 (DFrac.own 1) rs2v -∗
          gpr cpu rd (DFrac.own 1) (sign_extend (m := 64) v) -∗
          hartWs (GF := GF) cpu ws' -∗
          ((⌜v = lockZero⌝ ∗ vwpHold R ws' ∗ lockedEx (GF := GF) γ cpu) ∨ ⌜v ≠ lockZero⌝) -∗
          wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu)) -∗
      wacqCb (hlc := hlc) gen cpu γ lk R pc
        (wPEffPin (some cpu.val) ([.WEread WeakFetchEff.wakIfetch pc 4] ++
          [.WEread ⟨false, true, true⟩ lk 4, .WEwrite ⟨false, true, false⟩ lk 4 lockOne])) := by
  intro hmok hpmp hal4 hrs1 hrs2 hrd hea hsv halk hram hdecf hagree hDmi hgood hdec
  iintro Hm Hclk Hpc Hnpc Hrs1 Hrs2 Hrd #Hbs Hhws Hcont
  unfold wacqCb wmstateRest wmstateRestNonv
  iintro %σ %v %hflat Hlat ⟨%hbnd, %hnv, %hwf, Hreg, Hdev, Hlog, Hwsa⟩
  -- this hart's view cell
  icases keepPure (wand_intro (hartWsAgree cpu σ.wmWs ws)) $$ Hwsa Hhws with ⟨%hws, Hwsa, Hhws⟩
  subst hws
  -- the config bundle and every register the wrapper / fetch / decode reads
  icases keepPure (mConfRegFacts cpu dq c σ.wmRegs) $$ Hreg Hm with ⟨%hregs, Hreg, Hm⟩
  have hcfg : wcfgRegs σ c.pmpcfg := wcfgRegsOf σ c hmok hregs
  have hcfg' := hcfg
  obtain ⟨Lpriv, Lhs, Lmisa, Lmsec, Lpmpc, Lpma, Lhtif, LmisaS, LmIE, Lmprv, Lpmm, Lelp⟩ := hcfg'
  have Lpmp : pmpAllowsAll (σ.wmRegs .pmpcfg_n) := by rw [Lpmpc]; exact hpmp
  icases keepPure (wand_intro (reg_valid cpu σ.wmRegs .PC _ pc)) $$ Hreg Hpc with ⟨%Lpc, Hreg, Hpc⟩
  icases keepPure (WeakLeafLw4.gprValid cpu σ.wmRegs rs1 _ rs1v hrs1) $$ Hreg Hrs1
    with ⟨%Lrs1, Hreg, Hrs1⟩
  icases keepPure (WeakLeafLw4.gprValid cpu σ.wmRegs rs2 _ rs2v hrs2) $$ Hreg Hrs2
    with ⟨%Lrs2, Hreg, Hrs2⟩
  -- the effective address, the stored value and the agreement, at σ's registers
  have hea_σ : uxaXget σ.wmRegs rs1 + zeros (n := 64) = lk := by rw [Lrs1]; exact hea
  have hsv_σ : sign_extend (m := 32) (trunc (m := 32) (uxaXget σ.wmRegs rs2)) = lockOne := by
    rw [Lrs2]; exact hsv
  have hag_σ : ∀ r, D r = true → σ.wmRegs r = dst.regs r := hagree σ.wmRegs Lpriv Lmisa Lmsec
  -- the text facts
  icases keepPure (winstrFlat σ pc _ hwf) $$ Hlat Hbs with ⟨%hfok, Hlat, -⟩
  icases keepPure (winstrTextPinned σ pc _ hwf) $$ Hlat Hbs with ⟨%htext, Hlat, -⟩
  icases keepPure (winstrNv cpu σ.wmImg σ.wmLog pc _) $$ Hlat Hbs with ⟨%hnvpc, Hlat, -⟩
  have hnotRVC : isRVC (Sail.BitVec.extractLsb w 15 0) = false := by
    obtain ⟨_, _, w', ⟨hww, hn⟩, _⟩ := hfok
    subst hww
    exact hn
  -- the certificate's precondition (§4)
  icases keepPure (wPEffPinAmo4 cpu.val σ pc w rs1 rs2 rd lk v lockOne D dst hwf Lpc Lpriv Lpmp Lpma Lhtif
      Lhs LmisaS LmIE Lmprv Lpmm Lelp hal4 hnotRVC hrd hea_σ hsv_σ halk hram hflat hag_σ hDmi hgood hdec)
    $$ Hlat Hbs with ⟨%hP, Hlat, -⟩
  -- the clock cells, held across the step (deviation 5)
  icases clockCells_cases cpu $$ Hclk with ⟨%mi0, %mst0, %cy0, %ti0, %ip0, Hmi, Hmst, Hcy, Hti, Hip⟩
  -- the `minstret_increment` flag, funnel-chosen
  obtain ⟨b, hsi⟩ := execShouldIncMinstretSome (σ.wmRegs .cur_privilege) (wflatSt σ)
  imod (wand_intro (reg_update cpu σ.wmRegs .minstret_increment mi0 b)) $$ Hreg Hmi with ⟨Hreg, Hmi⟩
  -- the `execute` fact at the FLAT state (nextPC written inside)
  have hexE := execEffAmo4At (wflatSt σ) b pc rs1 rs2 rd lk v lockOne hrd Lpriv Lmprv Lpmm Lpmp Lpma
    Lhtif hea_σ hsv_σ halk hram hflat
  have hexec := execEffExec _ _ _ _ _ hexE
  obtain ⟨Fhs, Fmi, Fnpc, -, Fdev⟩ := amo4SexecFacts (wflatSt σ) b (BitVec.addInt pc 4) rd
    (bmWrite (wflatSt σ).mem lk 4 lockOne) (sign_extend (m := 64) v)
  -- the two register writes the `execute` performs
  imod (wand_intro (reg_update cpu (σ.wmRegs.set .minstret_increment b) .nextPC npc0 (BitVec.addInt pc 4)))
    $$ Hreg Hnpc with ⟨Hreg, Hnpc⟩
  rw [show ((σ.wmRegs.set .minstret_increment b).set .nextPC (BitVec.addInt pc 4)) =
      ((((wflatSt σ).setReg .minstret_increment b).setReg .nextPC (BitVec.addInt pc 4)).setMem
        (bmWrite (wflatSt σ).mem lk 4 lockOne)).regs from rfl]
  imod WeakLeafLw4.gprUpdate cpu
      ((((wflatSt σ).setReg .minstret_increment b).setReg .nextPC (BitVec.addInt pc 4)).setMem
        (bmWrite (wflatSt σ).mem lk 4 lockOne)) rd rd0 (sign_extend (m := 64) v) hrd
    $$ Hreg Hrd with ⟨Hreg, Hrd⟩
  -- the whole step: the funnel's exec chain
  have hdecW : winstrDec (.F_Base w)
      (.AMO (.AMOSWAP, true, false, .Regidx rs2, .Regidx rs1, 4, .Regidx rd)) :=
    fun t h1 h2 h3 h4 h5 => hdecf t h1 h2 h3 h4 h5
  obtain ⟨hst0, cc, tt, pp, hst1⟩ := wwpStepExec σ pc false
    (.AMO (.AMOSWAP, true, false, .Regidx rs2, .Regidx rs1, 4, .Regidx rd)) c.pmpcfg (.F_Base w) b
    ((((((wflatSt σ).setReg .minstret_increment b).setReg .nextPC (BitVec.addInt pc 4)).setMem
        (bmWrite (wflatSt σ).mem lk 4 lockOne)).setGpr rd (sign_extend (m := 64) v)))
    hcfg hpmp Lpc hfok rfl rfl hdecW hsi hexec (Fhs.trans Lhs) Fmi
  -- the wrapper's own register writes: tick PC, maybe bump minstret
  imod wwpRetireRegs cpu
      ((((((wflatSt σ).setReg .minstret_increment b).setReg .nextPC (BitVec.addInt pc 4)).setMem
        (bmWrite (wflatSt σ).mem lk 4 lockOne)).setGpr rd (sign_extend (m := 64) v))) b pc mst0
    $$ Hreg Hpc Hmst with ⟨Hreg, Hpc, %mst1, Hmst⟩
  rw [Fnpc]
  -- hand everything to `wacqCb`'s shape
  iapply fupd_mask_intro LawfulSet.empty_subset
  iintro Hmask
  isplitr
  · ipureintro; exact Lpc
  isplitr
  · ipureintro; exact htext
  isplitr
  · ipureintro; exact hP
  isplitr
  · ipureintro; exact hnvpc
  isplitl [Hlat]
  · iexact Hlat
  iexists (hartActiveSFinal
      ((((((wflatSt σ).setReg .minstret_increment b).setReg .nextPC (BitVec.addInt pc 4)).setMem
        (bmWrite (wflatSt σ).mem lk 4 lockOne)).setGpr rd (sign_extend (m := 64) v))) b),
    ((((hartActiveSFinal
      ((((((wflatSt σ).setReg .minstret_increment b).setReg .nextPC (BitVec.addInt pc 4)).setMem
        (bmWrite (wflatSt σ).mem lk 4 lockOne)).setGpr rd (sign_extend (m := 64) v))) b).setReg
          .mcycle cc).setReg .mtime tt).setReg .mip pp)
  isplitr
  · ipureintro; exact hst0
  isplitr
  · ipureintro; exact hst1
  inext
  iintro %tick %σ' %hpost Harm
  have hdev0 := hartActiveSFinalDev
    ((((((wflatSt σ).setReg .minstret_increment b).setReg .nextPC (BitVec.addInt pc 4)).setMem
      (bmWrite (wflatSt σ).mem lk 4 lockOne)).setGpr rd (sign_extend (m := 64) v))) b
  cases tick
  · -- NO TICK
    simp only [Bool.false_eq_true, ↓reduceIte] at hpost
    obtain ⟨hregs', hdev', -, -, ⟨l, hlog⟩, hwsle, hwf', hbnd'⟩ := hpost
    have hdevσ : σ'.wmDev = σ.wmDev := hdev'.trans (hdev0.trans Fdev)
    imod Hmask
    imod wlogUpdate σ.wmLog l $$ Hlog with Hlog
    imod hartWsUpdate cpu σ.wmWs σ.wmWs σ'.wmWs $$ [$Hwsa $Hhws] with ⟨Hwsa, Hhws⟩
    ihave Hclk := clockCells_introW cpu b mst1 cy0 ti0 ip0 $$ Hmi Hmst Hcy Hti Hip
    imodintro
    isplitl [Hreg Hdev Hlog Hwsa]
    · isplitr
      · ipureintro; exact hbnd'
      isplitr
      · ipureintro; exact hwf'
      rw [hregs', hdevσ, hlog]
      iframe Hreg Hdev Hlog Hwsa
    · iapply Hcont $$ %v %σ'.wmWs %hwsle Hm Hclk [Hpc Hnpc] Hrs1 Hrs2 Hrd Hhws Harm
      unfold pcIs
      iframe Hpc Hnpc
  · -- TICK: `tick_clock` wrote mcycle / mtime / mip
    simp only [↓reduceIte] at hpost
    obtain ⟨hregs', hdev', -, -, ⟨l, hlog⟩, hwsle, hwf', hbnd'⟩ := hpost
    have hdevσ : σ'.wmDev = σ.wmDev := hdev'.trans (hdev0.trans Fdev)
    imod Hmask
    imod wlogUpdate σ.wmLog l $$ Hlog with Hlog
    imod hartWsUpdate cpu σ.wmWs σ.wmWs σ'.wmWs $$ [$Hwsa $Hhws] with ⟨Hwsa, Hhws⟩
    imod wwpTickRegs cpu _ cc tt pp cy0 ti0 ip0 $$ Hreg Hcy Hti Hip with ⟨Hreg, Hcy, Hti, Hip⟩
    ihave Hclk := clockCells_introW cpu b mst1 cc tt pp $$ Hmi Hmst Hcy Hti Hip
    imodintro
    isplitl [Hreg Hdev Hlog Hwsa]
    · isplitr
      · ipureintro; exact hbnd'
      isplitr
      · ipureintro; exact hwf'
      rw [hregs', hdevσ, hlog]
      iframe Hreg Hdev Hlog Hwsa
    · iapply Hcont $$ %v %σ'.wmWs %hwsle Hm Hclk [Hpc Hnpc] Hrs1 Hrs2 Hrd Hhws Harm
      unfold pcIs
      iframe Hpc Hnpc

/-- Rocq `wwp_amo4_acquire_loop`: THE SLOT-IN CHECK -- `wwpAcquireLoopReal` at
this leaf's `P` and certificate (the AMO's access kinds pinned to what the model
emits); the branch is at Lean's `wPEff` (`WeakBranch` deviation 4). -/
theorem wwpAmo4AcquireLoop (gen : Nat) (cpu : CPU) (γ : GName) (lk : PAddr) (R : VProp GF)
    (pca pcb : BitVec 64) (akf2 : AkInfo) (pf2 : PAddr) (nf2 : Nat) (K Kb : IProp GF) :
    gen = 0 →
    accWf pca 4 →
    accWf pcb 4 →
    accWf lk 4 →
    inv wlockN (wlockInv (GF := GF) γ lk R) ⊢
      □ (K -∗ ▷ (Kb -∗ wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu)) -∗
          wacqCb (hlc := hlc) gen cpu γ lk R pca
            (wPEffPin (some cpu.val) ([.WEread WeakFetchEff.wakIfetch pca 4] ++
              [.WEread ⟨false, true, true⟩ lk 4, .WEwrite ⟨false, true, false⟩ lk 4 lockOne]))) -∗
        □ (Kb -∗ (K -∗ wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu)) -∗
            wbrCb (hlc := hlc) (GF := GF) gen cpu pcb
              (wPEff (some cpu.val) [.WEread akf2 pf2 nf2]) wQPure) -∗
          K -∗ wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu) := by
  intro hgen hacca haccb hacclk
  -- the footprint: the four text bytes of `pca` and the four bytes of the lock word
  have hfoot : ∀ a : Int,
      weffsTouch ([.WEread WeakFetchEff.wakIfetch pca 4] ++
        [.WEread ⟨false, true, true⟩ lk 4, .WEwrite ⟨false, true, false⟩ lk 4 lockOne]) a →
      (∃ j, j < 4 ∧ a = WeakInterp.accAddr pca j) ∨ (∃ j, j < 4 ∧ a = WeakInterp.accAddr lk j) := by
    intro a ha
    rcases weffsTouchCons _ _ a ha with ha | ha
    · exact .inl ha
    · rcases weffsTouchCons _ _ a ha with ha | ha
      · exact .inr ha
      · exact .inr (weffsTouchWrite1 _ lk 4 lockOne a ha)
  exact wwpAcquireLoopReal gen cpu γ lk R pca pcb _ _ _ K Kb _ hgen hacca haccb hacclk hfoot
    (wstepCertFrPin _ _ _ _
      (wcertAmoAqPinBase4 cpu.val pca ⟨false, true, true⟩ ⟨false, true, false⟩ lk lockOne rfl rfl rfl))
    (wcertNowrite cpu.val pcb [.WEread akf2 pf2 nf2] (nowriteTraceRead akf2 pf2 nf2))

end leaf

end Weak
