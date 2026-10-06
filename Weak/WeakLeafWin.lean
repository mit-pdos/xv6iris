/-
Weak: **the shared LEAF WINDOW KIT** (M4 batch-2 consolidation): the window
`wwin pc ea n` (the instruction's 4 text bytes at the pc plus an `n`-byte data
word at the effective address) with its membership / inversion / nonzero /
pinned / conf-text / conf-data / write-domain lemmas; the register-side
helpers every leaf shares; the data-word alignment extractors.

Rocq: `iris/WeakLeafWin.v` @ xxvzwolszwmp.

The Rocq header, in substance.  Every batch-2 leaf certifies its step over the
same confined window.  The kit is WIDTH-shaped, not access-shaped; this file
is the ONE width-parameterized copy, plus the small register-bookkeeping
helpers every leaf shares:
* §1 `wwin pc ea n` with its lemmas; every membership fact is discharged
  algebraically (no `set_solver`).
* §2 the register-side helpers: `setLookupNe`, the shared peel tactic
  `leaf_peel`, the funnel-read bridge `regAtFlat`, and the two
  width-independent successor register frames (`loadSexecFacts` for the load
  shape, `storeRegsFacts` for the store/AMO pre-write tower).
* §3 the data-word alignment extractors.
Rocq's LAYOUT CONSTRAINT (the two `Countable Arch.pa` instances around
`Import SailStdpp.Values`) has no Lean counterpart: there is one `GSet PAddr`.

**Deviations from Rocq.**
1. NAMES / VOCABULARY: the tree's camelCase (map below); as
   `Weak/WeakCert.lean` deviations 1–2 and `Weak/WeakFetchEff.lean`
   deviation 1: `pa_add a j` ↦ `a + BitVec.ofNat 64 j`, `n : N` ↦ `n : Nat`,
   `gset Arch.pa` ↦ `GSet PAddr`, `list_to_set` ↦ `LawfulSet.ofList`,
   `seq 0 n` ↦ `List.range n`, `pa_z` ↦ `paZ`, `acc_addr` ↦
   `WeakInterp.accAddr`, `wflat (wm_img σ) (wm_log σ) !! a` ↦
   `wflatMem σ.wmImg σ.wmLog a`, `wmem_restrict σ W !! a` ↦
   `wmemRestrict σ W a`, `dom mm ⊆ W` ↦ `bmDomSub mm W`, `write_bytes` ↦
   `bmWrite`, `register_lookup r (sregs s)` ↦ `s.regs r`, `set_reg` ↦
   `ExecSt.setReg`, `mem`/`mdev` ↦ `.mem`/`.dev`, `mword n` ↦ `BitVec n`.
2. `addr_is_ram a` (one byte) ↦ `inRam a 1`.  The Lean-only
   `WeakLeafWin.inRamByte` turns the leaves' `inRam pa n` into the per-byte
   form.
3. `wwin_conf_data` / `wwin_wdom`: Rocq's `{wd : N} (v : bv wd)` is
   `{k : Nat} (v : BitVec (8 * k))` (`nthByte` and `bmWrite` are stated at
   width `8 * k`); `wwinWdom` writes at the window's own width
   (`v : BitVec (8 * n)`), the only instance the leaves use.
4. `set_lookup_ne` / `reg_at_flat`: Rocq's `register_beq r r' = false` is
   `r ≠ r'` (as `WeakFunnel.setMiLookup`).
5. `load_sexec_facts`: Rocq's GPR write `set_reg … (R_bitvector_64
   (gpr_of_Z (uint rd))) x` is the tree's `setGpr rd x` (the ExecSC
   convention; equal for `rd ≠ 0`, and `x0` discards).
6. `leaf_peel` is a Lean macro; its `ltac:(reg_ne)` side conditions are
   `by decide`.

**Rocq → Lean name map.**  `wwin` `wwin`, `wwin_text` `wwinText`, `wwin_data`
`wwinData`, `wwin_inv` `wwinInv`, `addr_is_ram_pa_z_nz` `addrIsRamPaZNz`,
`wwin_nonzero` `wwinNonzero`, `wwin_pinned` `wwinPinned`, `wwin_conf_text`
`wwinConfText`, `wwin_conf_data` `wwinConfData`, `wwin_wdom` `wwinWdom`,
`set_lookup_ne` `setLookupNe`, `leaf_peel` (Ltac) `leaf_peel` (macro),
`reg_at_flat` `regAtFlat`, `load_sexec_facts` `loadSexecFacts`,
`store_regs_facts` `storeRegsFacts`, `wpt8_align` `wpt8Align`, `wpt4_align`
`wpt4Align`, `wpt8_own_align` `wpt8OwnAlign`, `wpt4_own_align`
`wpt4OwnAlign`.  Lean-only (file-qualified): `WeakLeafWin.inRamByte`,
`WeakLeafWin.setGprRegsNe`, `WeakLeafWin.setGprMem`, `WeakLeafWin.setGprDev`.

**Dropped:** nothing (1 definition, 17 lemmas and 1 Ltac in Rocq; all ported).
-/
import Weak.WeakFetchEff
import Weak.WeakWord8
import Weak.WeakCert

namespace Weak

open Iris Iris.BI Iris.BI.MonPred Iris.ProofMode Iris.Std
open MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D LeanRV64D.Functions

/-! ## 1. THE WINDOW: 4 text bytes + an `n`-byte data word -/

/-- Rocq `wwin`. -/
def wwin (pc ea : PAddr) (n : Nat) : GSet PAddr :=
  LawfulSet.ofList (((List.range 4).map (fun j => pc + BitVec.ofNat 64 j)) ++
    ((List.range n).map (fun j => ea + BitVec.ofNat 64 j)))

theorem wwinText (pc ea : PAddr) (n : Nat) (j : Nat) :
    j < 4 → pc + BitVec.ofNat 64 j ∈ wwin pc ea n := by
  intro hj
  unfold wwin
  rw [elemOfListToSet]
  simp only [List.mem_append, List.mem_map, List.mem_range]
  exact .inl ⟨j, hj, rfl⟩

theorem wwinData (pc ea : PAddr) (n : Nat) (j : Nat) :
    j < n → ea + BitVec.ofNat 64 j ∈ wwin pc ea n := by
  intro hj
  unfold wwin
  rw [elemOfListToSet]
  simp only [List.mem_append, List.mem_map, List.mem_range]
  exact .inr ⟨j, hj, rfl⟩

theorem wwinInv (pc ea : PAddr) (n : Nat) (a : PAddr) :
    a ∈ wwin pc ea n →
    (∃ j : Nat, j < 4 ∧ a = pc + BitVec.ofNat 64 j) ∨
    (∃ j : Nat, j < n ∧ a = ea + BitVec.ofNat 64 j) := by
  intro h
  unfold wwin at h
  rw [elemOfListToSet] at h
  simp only [List.mem_append, List.mem_map, List.mem_range] at h
  rcases h with ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩
  · exact .inl ⟨j, hj, rfl⟩
  · exact .inr ⟨j, hj, rfl⟩

/-- (i) NONZERO: RAM starts at `ramBase = 0x80000000`. -/
theorem addrIsRamPaZNz (a : PAddr) : inRam a 1 → paZ a ≠ 0 := by
  intro h
  unfold inRam ramBase at h
  unfold paZ
  omega

/-- Lean-only (deviation 2): the per-byte RAM fact of a RAM window. -/
theorem WeakLeafWin.inRamByte (pa : PAddr) (n j : Nat) :
    inRam pa n → j < n → inRam (pa + BitVec.ofNat 64 j) 1 := by
  intro h hj
  have hlt := pa.isLt
  unfold inRam ramBase ramEnd at *
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]
  have : j % 2 ^ 64 = j := Nat.mod_eq_of_lt (by omega)
  rw [this, Nat.mod_eq_of_lt (by omega)]
  omega

theorem wwinNonzero (pc ea : PAddr) (n : Nat) :
    (∀ j : Nat, j < 4 → inRam (pc + BitVec.ofNat 64 j) 1) →
    (∀ j : Nat, j < n → inRam (ea + BitVec.ofNat 64 j) 1) →
    ∀ a, a ∈ wwin pc ea n → paZ a ≠ 0 := by
  intro hpc hea a ha
  rcases wwinInv pc ea n a ha with ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩
  · exact addrIsRamPaZNz _ (hpc j hj)
  · exact addrIsRamPaZNz _ (hea j hj)

/-- (ii) PINNEDNESS (the WHOLE-WINDOW form). -/
theorem wwinPinned (σ : Wmstate) (pc ea : PAddr) (n : Nat) :
    accWf pc 4 → accWf ea n →
    (∀ j : Nat, j < 4 → pinnedRead σ (WeakInterp.accAddr pc j)) →
    (∀ j : Nat, j < n → pinnedRead σ (WeakInterp.accAddr ea j)) →
    ∀ a, a ∈ wwin pc ea n → pinnedRead σ (paZ a) := by
  intro hwpc hwea hpc hea a ha
  rcases wwinInv pc ea n a ha with ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩
  · rw [accWfByte pc 4 j hwpc hj]; exact hpc j hj
  · rw [accWfByte ea n j hwea hj]; exact hea j hj

/-- (iii) the text bytes are in the confined map. -/
theorem wwinConfText (σ : Wmstate) (pc ea : PAddr) (n : Nat) (w : BitVec 32) :
    (∀ j : Nat, j < 4 →
      wflatMem σ.wmImg σ.wmLog (pc + BitVec.ofNat 64 j) = some (nthByte (n := 4) w j)) →
    ∀ j : Nat, j < 4 →
      wmemRestrict σ (wwin pc ea n) (pc + BitVec.ofNat 64 j) = some (nthByte (n := 4) w j) :=
  fun h j hj => wmemRestrictLookup σ _ _ _ (wwinText pc ea n j hj) (h j hj)

/-- (iii) the data bytes are in the confined map (deviation 3). -/
theorem wwinConfData (σ : Wmstate) (pc ea : PAddr) (n : Nat) {k : Nat} (v : BitVec (8 * k)) :
    (∀ j : Nat, j < n →
      wflatMem σ.wmImg σ.wmLog (ea + BitVec.ofNat 64 j) = some (nthByte v j)) →
    ∀ j : Nat, j < n →
      wmemRestrict σ (wwin pc ea n) (ea + BitVec.ofNat 64 j) = some (nthByte v j) :=
  fun h j hj => wmemRestrictLookup σ _ _ _ (wwinData pc ea n j hj) (h j hj)

/-- (iv) THE WRITE-DOMAIN CONFINEMENT (deviation 3). -/
theorem wwinWdom (σ : Wmstate) (pc ea : PAddr) (n : Nat) (v : BitVec (8 * n)) :
    bmDomSub (bmWrite (wmemRestrict σ (wwin pc ea n)) ea n v) (wwin pc ea n) :=
  writeBytesDomSub _ ea n v _ (wmemRestrictDom σ _) (fun j hj => wwinData pc ea n j hj)

/-! ## 2. The register-side helpers every leaf shares -/

/-- Rocq `set_lookup_ne` (deviation 4). -/
theorem setLookupNe (r r' : Register) (s : ExecSt) (x : RegisterType r') :
    r ≠ r' → (s.setReg r' x).regs r = s.regs r :=
  fun h => RegFile.set_other _ _ _ _ h

/-- Rocq `leaf_peel r`: peel the `nextPC` and `minstret_increment` writes off a
lookup of `r`.  The register is passed explicitly. -/
macro "leaf_peel " r:term : tactic =>
  `(tactic| rw [setLookupNe $r .nextPC _ _ (by decide),
    setLookupNe $r .minstret_increment _ _ (by decide)])

/-- Rocq `reg_at_flat`: a register read at `σ`, through the funnel's
`minstret_increment` pre-write. -/
theorem regAtFlat (r : Register) (σ : Wmstate) (b : Bool) :
    r ≠ .minstret_increment →
    ((wflatSt σ).setReg .minstret_increment b).regs r = σ.wmRegs r :=
  fun h => setMiLookup r (wflatSt σ) b h

/-- Lean-only: a GPR write leaves every non-GPR register alone. -/
theorem WeakLeafWin.setGprRegsNe (s : ExecSt) (i : BitVec 5) (v : BitVec 64) (r : Register)
    (h : r ∉ [.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15,
      .x16, .x17, .x18, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28, .x29, .x30,
      .x31]) :
    (s.setGpr i v).regs r = s.regs r := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
    h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31⟩ := h
  unfold ExecSt.setGpr
  split <;> first | rfl | exact RegFile.set_other _ _ _ _ ‹_›

/-- Lean-only: a GPR write leaves the memory alone. -/
theorem WeakLeafWin.setGprMem (s : ExecSt) (i : BitVec 5) (v : BitVec 64) :
    (s.setGpr i v).mem = s.mem := by
  unfold ExecSt.setGpr; split <;> rfl

/-- Lean-only: a GPR write leaves the devices alone. -/
theorem WeakLeafWin.setGprDev (s : ExecSt) (i : BitVec 5) (v : BitVec 64) :
    (s.setGpr i v).dev = s.dev := by
  unfold ExecSt.setGpr; split <;> rfl

/-- Rocq `load_sexec_facts` (deviation 5): THE LOAD-SHAPE SUCCESSOR REGISTER
FRAME. -/
theorem loadSexecFacts (s0 : ExecSt) (b : Bool) (npc : BitVec 64) (rd : BitVec 5) (x : BitVec 64) :
    let sExec := ((s0.setReg .minstret_increment b).setReg .nextPC npc).setGpr rd x
    sExec.regs .hart_state = s0.regs .hart_state ∧
    sExec.regs .minstret_increment = b ∧
    sExec.mem = s0.mem ∧
    sExec.dev = s0.dev ∧
    sExec.regs .nextPC = npc := by
  intro sExec
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [WeakLeafWin.setGprRegsNe _ _ _ _ (by decide)]
    leaf_peel .hart_state
  · rw [WeakLeafWin.setGprRegsNe _ _ _ _ (by decide),
      setLookupNe .minstret_increment .nextPC _ _ (by decide)]
    simp only [ExecSt.setReg_regs, RegFile.set_same]
  · exact WeakLeafWin.setGprMem _ _ _
  · exact WeakLeafWin.setGprDev _ _ _
  · rw [WeakLeafWin.setGprRegsNe _ _ _ _ (by decide)]
    simp only [ExecSt.setReg_regs, RegFile.set_same]

/-- Rocq `store_regs_facts`: THE STORE-SHAPE PRE-WRITE TOWER. -/
theorem storeRegsFacts (s0 : ExecSt) (b : Bool) (npc : BitVec 64) :
    ((s0.setReg .minstret_increment b).setReg .nextPC npc).regs .hart_state = s0.regs .hart_state ∧
    ((s0.setReg .minstret_increment b).setReg .nextPC npc).regs .minstret_increment = b ∧
    ((s0.setReg .minstret_increment b).setReg .nextPC npc).regs .nextPC = npc := by
  refine ⟨?_, ?_, ?_⟩
  · leaf_peel .hart_state
  · rw [setLookupNe .minstret_increment .nextPC _ _ (by decide)]
    simp only [ExecSt.setReg_regs, RegFile.set_same]
  · simp only [ExecSt.setReg_regs, RegFile.set_same]

/-! ## 3. The data-word alignment extractors -/

section align
variable {GF : BundledGFunctors} [WeakGS GF]

theorem wpt8Align (ea : PAddr) (dq : DFrac) (v : BitVec 64) (ws : Wstate) :
    vwpHold (wpt8 (GF := GF) ea dq v) ws ⊢ ⌜is_aligned_paddr (.Physaddr ea) 8 = true⌝ := by
  refine (wpt8_at ea dq v ws).1.trans ?_
  iintro ⟨%h, -⟩
  ipureintro; exact h

theorem wpt4Align (ea : PAddr) (dq : DFrac) (v : BitVec 32) (ws : Wstate) :
    vwpHold (wpt4 (GF := GF) ea dq v) ws ⊢ ⌜is_aligned_paddr (.Physaddr ea) 4 = true⌝ := by
  refine (wpt4_at ea dq v ws).1.trans ?_
  iintro ⟨%h, -⟩
  ipureintro; exact h

theorem wpt8OwnAlign (c : CPU) (ea : PAddr) (v : BitVec 64) (ws : Wstate) :
    vwpHold (wpt8Own (GF := GF) c ea v) ws ⊢ ⌜is_aligned_paddr (.Physaddr ea) 8 = true⌝ := by
  refine (wpt8Own_at c ea v ws).1.trans ?_
  iintro ⟨%h, -⟩
  ipureintro; exact h

theorem wpt4OwnAlign (c : CPU) (ea : PAddr) (v : BitVec 32) (ws : Wstate) :
    vwpHold (wpt4Own (GF := GF) c ea v) ws ⊢ ⌜is_aligned_paddr (.Physaddr ea) 4 = true⌝ := by
  refine (wpt4Own_at c ea v ws).1.trans ?_
  iintro ⟨%h, -⟩
  ipureintro; exact h

end align

end Weak
