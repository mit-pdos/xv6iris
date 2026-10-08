/-
Weak: **Q22 ACCEPTANCE — non-vacuity of the push_off / pop_off / acquire / allocpid text
premises** (Lean only; no Rocq source: Rocq's kernel had these 4-byte words 4-aligned, so its
`text_at4_S` premises were satisfiable without a certificate).

Q22 (`notes/weak-port-q22-align.md` §C steps 6–7, acceptance (c)/(d)): before the rework,
`textAt4S` demanded a 4-aligned pc, and this tree's kernel has 4-byte words at pc ≡ 2 (mod 4)
inside `pushOffText` (`Wq10 Wq18 Wq2c Wq30`), `popOffText` (`Wp16`), `acquireText` (`Wa12`) and
`allocpidText` (14 of its 21 `textAt4S` conjuncts), so every theorem taking one of those
premises was vacuous.  With `textAt4S` generalised to the 2-aligned arm (`AxDataX6`
deviation 6), this file proves each premise HOLDS on one concrete instance.

THE INSTANCE.  Image `AxSpinTextCerts.σK` = `AxSpinE8f.σ8` (registers, devices, the Sv39 table
pages 0x80010 / 0x80011 / 0x80012, mycpu's bytes) with the REAL kernel text bytes overlaid on
`[0x80000c1e, 0x80000cc8)` (push_off, acquire, holding's neighbour gap, pop_off) and
`[0x80001baa, 0x80001c0c)` (allocproc + 0x38 .. + 0x9a, the inlined allocpid copy).  The bytes
are read off `Xv6.Kernel.textTree` itself (`AxSpinTextCerts.kByte`: the instruction covering
the address, little-endian), so no encoding is restated here.  Page map `AxSpinE8f.tT`
(VA = PA pages 0x80000 = `vpnD` / `L0leaf`, used by push_off / pop_off / acquire, and 0x80001 =
`vpnT` / `L1leaf`, used by allocpid).

COUNTS.  `pushOffText`: 24 conjuncts (19 compressed, 5 four-byte of which 4 at 2 mod 4);
`popOffText`: 19 (16 compressed, 3 four-byte, 1 at 2 mod 4); `acquireText`: 22 (18 compressed,
4 four-byte, 1 at 2 mod 4); `allocpidText`: 27 (6 compressed, 21 four-byte, 14 at 2 mod 4 —
the q22-align note's "20" overcounts: +0x52/+0x56/+0x76..+0x86 are 4-aligned).
Each conjunct is closed by one of four constructors (`textAtA`/`textAtU`/`text4A`/`text4U`:
compressed / 4-byte at a 4-aligned / 2-mod-4 pc) whose residual premise is decided by
`decide +kernel` over the literal image.

Lean-only names (all file-qualified `AxSpinTextCerts.*`): `kByte`, `inText`, `memK`, `σK`,
`rd32`, `pageOk`, `chkD`, `pageD`, `pageT`, `textAtA`, `textAtU`, `text4A`, `text4U`,
`pushOffTextOf`, `popOffTextOf`, `acquireTextOf`, `allocpidTextOf` (+ macro
`ax_spin_tc_txt`).
-/
import Weak.AxSpinE8f
import Weak.AxSpinPO
import Weak.AxSpinAq
import Weak.AxSpinAp
import Xv6.KernelTree

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D LeanRV64D.Functions

/-! # 1. The image -/

/-- (Lean-only) the byte at `a` of this tree's kernel text: byte `k` of the instruction at
`a - k` (`k < 4`, the first that exists and covers `a`). -/
def AxSpinTextCerts.kByte (a : Nat) : Option (BitVec 8) :=
  let look := fun k : Nat =>
    if k ≤ a then
      match Xv6.Kernel.textTree.find? (a - k) with
      | some i => if k < i.width then some (BitVec.ofNat 8 (i.enc >>> (8 * k))) else none
      | none => none
    else none
  match look 0 with
  | some b => some b
  | none => match look 1 with
    | some b => some b
    | none => match look 2 with
      | some b => some b
      | none => look 3

/-- (Lean-only) the overlaid text ranges: push_off .. pop_off, and allocproc + 0x38 .. + 0x9a. -/
def AxSpinTextCerts.inText (n : Nat) : Bool :=
  (decide (0x80000c1e ≤ n) && decide (n < 0x80000cc8)) ||
  (decide (0x80001baa ≤ n) && decide (n < 0x80001c0c))

/-- (Lean-only) the image memory: kernel text on `inText`, else `AxSpinE8f.σ8`'s. -/
def AxSpinTextCerts.memK (a : BitVec 64) : Option (BitVec 8) :=
  if AxSpinTextCerts.inText a.toNat then AxSpinTextCerts.kByte a.toNat else AxSpinE8f.σ8.mem a

/-- (Lean-only) THE IMAGE. -/
def AxSpinTextCerts.σK : ExecSt :=
  ⟨AxSpinE8f.σ8.regs, AxSpinTextCerts.memK, AxSpinE8f.σ8.dev⟩

/-- (Lean-only) the little-endian 4-byte word at `a` of a memory. -/
def AxSpinTextCerts.rd32 (m : BitVec 64 → Option (BitVec 8)) (a : BitVec 64) : BitVec 32 :=
  let b := fun j : Nat => (m (a + BitVec.ofNat 64 j)).getD 0#8
  b 3 ++ b 2 ++ b 1 ++ b 0

/-! # 2. The two pages -/

/-- (Lean-only) the page-only part of `textAtS` / `textAt4S` at a vpn. -/
def AxSpinTextCerts.pageOk (σ : ExecSt) (T : PTree) (vpn : BitVec 27) (p2 p1 w : BitVec 64) :
    Prop :=
  AxPtProt.ptreeMaps T vpn p2 p1 w ∧
  WeakWalkEff.ptSlotMem σ (AxPtProt.ptAddr2 T vpn) p2 ∧
  WeakWalkEff.ptSlotMem σ (AxPtProt.ptAddr1 p2 vpn) p1 ∧
  WeakWalkEff.ptSlotMem σ (AxPtProt.ptAddr0 p1 vpn) w ∧
  (∀ mxr dosum : Bool, pteCheckOk (.InstructionFetch ()) .Supervisor mxr dosum w) ∧
  update_PTE_Bits w (.InstructionFetch ()) = none ∧
  ptePbmt0 w

/-- (Lean-only) the fetch checks of the page-0x80000 leaf. -/
theorem AxSpinTextCerts.chkD : ∀ mxr dosum : Bool,
    pteCheckOk (.InstructionFetch ()) .Supervisor mxr dosum AxSpinE8f.L0leaf := by
  intro mxr dosum s
  cases mxr <;> cases dosum <;> ax_epi_ledger_krfl

/-- (Lean-only) page 0x80000 (push_off, acquire, pop_off) in `σK`. -/
theorem AxSpinTextCerts.pageD :
    AxSpinTextCerts.pageOk AxSpinTextCerts.σK AxSpinE8f.tT AxSpinE8f.vpnD
      AxSpinE8f.P2 AxSpinE8f.P1 AxSpinE8f.L0leaf :=
  ⟨AxSpinE8f.mapsD,
    ⟨by unfold BytesAt; decide +kernel, by decide +kernel, by decide +kernel⟩,
    ⟨by unfold BytesAt; decide +kernel, by decide +kernel, by decide +kernel⟩,
    ⟨by unfold BytesAt; decide +kernel, by decide +kernel, by decide +kernel⟩,
    AxSpinTextCerts.chkD, by decide +kernel, by unfold ptePbmt0; decide +kernel⟩

/-- (Lean-only) page 0x80001 (allocproc) in `σK`. -/
theorem AxSpinTextCerts.pageT :
    AxSpinTextCerts.pageOk AxSpinTextCerts.σK AxSpinE8f.tT AxSpinE8f.vpnT
      AxSpinE8f.P2 AxSpinE8f.P1 AxSpinE8f.L1leaf :=
  ⟨AxSpinE8f.mapsT,
    ⟨by unfold BytesAt; decide +kernel, by decide +kernel, by decide +kernel⟩,
    ⟨by unfold BytesAt; decide +kernel, by decide +kernel, by decide +kernel⟩,
    ⟨by unfold BytesAt; decide +kernel, by decide +kernel, by decide +kernel⟩,
    AxSpinE8f.chkT, by decide +kernel, by unfold ptePbmt0; decide +kernel⟩

/-! # 3. The four constructors -/

/-- (Lean-only) `textAtS`, 4-aligned arm. -/
theorem AxSpinTextCerts.textAtA {σ : ExecSt} {T : PTree} {vpn : BitVec 27} {p2 p1 w : BitVec 64}
    (hp : AxSpinTextCerts.pageOk σ T vpn p2 p1 w) (pc : BitVec 64) (h : BitVec 16)
    (H : WeakKpt.svpnOf pc = vpn ∧
      (pc != sign_extend (m := 64) (Sail.BitVec.extractLsb pc 38 0)) = false ∧
      (Sail.BitVec.access pc 0 != 0#1) = false ∧ isRVC h = true ∧
      is_aligned_vaddr (.Virtaddr pc) 4 = true ∧
      Sail.BitVec.extractLsb (AxSpinTextCerts.rd32 σ.mem (AxSpinE6.fetchPa w pc)) 15 0 = h ∧
      inRam (AxSpinE6.fetchPa w pc) 4 ∧
      is_aligned_paddr (.Physaddr (AxSpinE6.fetchPa w pc)) 4 = true ∧
      (∀ j, j < 4 → σ.mem (AxSpinE6.fetchPa w pc + BitVec.ofNat 64 j) =
        some (nthByte (n := 4) (AxSpinTextCerts.rd32 σ.mem (AxSpinE6.fetchPa w pc)) j))) :
    textAtS σ T pc h := by
  obtain ⟨hm, h2, h1, h0, hc, hu, hb⟩ := hp
  obtain ⟨hv, hcn, hb0, hrvc, hal, hlo, hr, ha, hby⟩ := H
  unfold textAtS
  rw [hv]
  exact ⟨p2, p1, w, AxSpinE6.fetchPa w pc, hm, h2, h1, h0, hc, hu, hb, hcn, rfl, hb0, hrvc,
    by rw [if_pos hal]; exact ⟨_, hlo, hr, ha, hby⟩⟩

/-- (Lean-only) `textAtS`, 2-mod-4 arm. -/
theorem AxSpinTextCerts.textAtU {σ : ExecSt} {T : PTree} {vpn : BitVec 27} {p2 p1 w : BitVec 64}
    (hp : AxSpinTextCerts.pageOk σ T vpn p2 p1 w) (pc : BitVec 64) (h : BitVec 16)
    (H : WeakKpt.svpnOf pc = vpn ∧
      (pc != sign_extend (m := 64) (Sail.BitVec.extractLsb pc 38 0)) = false ∧
      (Sail.BitVec.access pc 0 != 0#1) = false ∧ isRVC h = true ∧
      is_aligned_vaddr (.Virtaddr pc) 4 = false ∧
      (Sail.BitVec.access pc 1 != 0#1) = true ∧
      inRam (AxSpinE6.fetchPa w pc) 2 ∧
      is_aligned_paddr (.Physaddr (AxSpinE6.fetchPa w pc)) 2 = true ∧
      (∀ j, j < 2 → σ.mem (AxSpinE6.fetchPa w pc + BitVec.ofNat 64 j) =
        some (nthByte (n := 2) h j))) :
    textAtS σ T pc h := by
  obtain ⟨hm, h2, h1, h0, hc, hu, hb⟩ := hp
  obtain ⟨hv, hcn, hb0, hrvc, hal, hb1, hr, ha, hby⟩ := H
  unfold textAtS
  rw [hv]
  exact ⟨p2, p1, w, AxSpinE6.fetchPa w pc, hm, h2, h1, h0, hc, hu, hb, hcn, rfl, hb0, hrvc,
    by rw [if_neg (by rw [hal]; decide)]; exact ⟨hb1, hr, ha, hby⟩⟩

/-- (Lean-only) `textAt4S`, 4-aligned arm. -/
theorem AxSpinTextCerts.text4A {σ : ExecSt} {T : PTree} {vpn : BitVec 27} {p2 p1 w : BitVec 64}
    (hp : AxSpinTextCerts.pageOk σ T vpn p2 p1 w) (pc : BitVec 64) (w32 : BitVec 32)
    (H : WeakKpt.svpnOf pc = vpn ∧
      (pc != sign_extend (m := 64) (Sail.BitVec.extractLsb pc 38 0)) = false ∧
      (Sail.BitVec.access pc 0 != 0#1) = false ∧
      isRVC (Sail.BitVec.extractLsb w32 15 0) = false ∧
      is_aligned_vaddr (.Virtaddr pc) 4 = true ∧
      inRam (AxSpinE6.fetchPa w pc) 4 ∧
      is_aligned_paddr (.Physaddr (AxSpinE6.fetchPa w pc)) 4 = true ∧
      (∀ j, j < 4 → σ.mem (AxSpinE6.fetchPa w pc + BitVec.ofNat 64 j) =
        some (nthByte (n := 4) w32 j))) :
    textAt4S σ T pc w32 := by
  obtain ⟨hm, h2, h1, h0, hc, hu, hb⟩ := hp
  obtain ⟨hv, hcn, hb0, hrvc, hal, hr, ha, hby⟩ := H
  unfold textAt4S
  rw [hv]
  exact ⟨p2, p1, w, AxSpinE6.fetchPa w pc, hm, h2, h1, h0, hc, hu, hb, hcn, rfl, hb0, hrvc, hr,
    by rw [if_pos hal]; exact ha, hby⟩

/-- (Lean-only, Q22) `textAt4S`, 2-mod-4 arm (two halfwords on one page). -/
theorem AxSpinTextCerts.text4U {σ : ExecSt} {T : PTree} {vpn : BitVec 27} {p2 p1 w : BitVec 64}
    (hp : AxSpinTextCerts.pageOk σ T vpn p2 p1 w) (pc : BitVec 64) (w32 : BitVec 32)
    (H : WeakKpt.svpnOf pc = vpn ∧
      (pc != sign_extend (m := 64) (Sail.BitVec.extractLsb pc 38 0)) = false ∧
      (Sail.BitVec.access pc 0 != 0#1) = false ∧
      isRVC (Sail.BitVec.extractLsb w32 15 0) = false ∧
      is_aligned_vaddr (.Virtaddr pc) 4 = false ∧
      (Sail.BitVec.access pc 1 != 0#1) = true ∧
      (Sail.BitVec.extractLsb pc 11 1 != 0x7ff#11) = true ∧
      inRam (AxSpinE6.fetchPa w pc) 4 ∧
      is_aligned_paddr (.Physaddr (AxSpinE6.fetchPa w pc)) 2 = true ∧
      (∀ j, j < 4 → σ.mem (AxSpinE6.fetchPa w pc + BitVec.ofNat 64 j) =
        some (nthByte (n := 4) w32 j))) :
    textAt4S σ T pc w32 := by
  obtain ⟨hm, h2, h1, h0, hc, hu, hb⟩ := hp
  obtain ⟨hv, hcn, hb0, hrvc, hal, hb1, hns, hr, ha, hby⟩ := H
  unfold textAt4S
  rw [hv]
  exact ⟨p2, p1, w, AxSpinE6.fetchPa w pc, hm, h2, h1, h0, hc, hu, hb, hcn, rfl, hb0, hrvc, hr,
    by rw [if_neg (by rw [hal]; decide)]; exact ⟨hb1, ha, hns⟩, hby⟩

/-- (Lean-only) one text conjunct on page `pg`: the fitting constructor, residual by kernel. -/
local macro "ax_spin_tc_txt " pg:term : tactic => `(tactic|
  first
  | exact AxSpinTextCerts.textAtA $pg _ _ (by decide +kernel)
  | exact AxSpinTextCerts.textAtU $pg _ _ (by decide +kernel)
  | exact AxSpinTextCerts.text4U $pg _ _ (by decide +kernel)
  | exact AxSpinTextCerts.text4A $pg _ _ (by decide +kernel))

/-! # 4. The certificates -/

/-- (Lean-only, Q22 acceptance) `pushOffText` HOLDS at the instance (24 conjuncts; the
2-mod-4 words `Wq10 Wq18 Wq2c Wq30` by `text4U`). -/
theorem AxSpinTextCerts.pushOffTextOf : pushOffText AxSpinTextCerts.σK AxSpinE8f.tT := by
  unfold pushOffText
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_⟩ <;> ax_spin_tc_txt AxSpinTextCerts.pageD

/-- (Lean-only, Q22 acceptance) `popOffText` HOLDS at the instance (19 conjuncts; `Wp16` by
`text4U`). -/
theorem AxSpinTextCerts.popOffTextOf : popOffText AxSpinTextCerts.σK AxSpinE8f.tT := by
  unfold popOffText
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    ax_spin_tc_txt AxSpinTextCerts.pageD

/-- (Lean-only, Q22 acceptance) `acquireText` HOLDS at the instance (22 conjuncts; `Wa12` by
`text4U`). -/
theorem AxSpinTextCerts.acquireTextOf : acquireText AxSpinTextCerts.σK AxSpinE8f.tT := by
  unfold acquireText
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_⟩ <;> ax_spin_tc_txt AxSpinTextCerts.pageD

/-- (Lean-only, Q22 acceptance) `allocpidText` HOLDS at the instance (27 conjuncts; 14 by
`text4U`). -/
theorem AxSpinTextCerts.allocpidTextOf : allocpidText AxSpinTextCerts.σK AxSpinE8f.tT := by
  unfold allocpidText
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> ax_spin_tc_txt AxSpinTextCerts.pageT

end Weak
