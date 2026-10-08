/-
Weak: **THEOREM 2 / certificate (a′): THE PAGE TABLE AND THE WARM ENTRY STATE** — a
kvmmake-shaped, A/D-preset identity page table `AxSpinT2pt.tX` for this tree's kernel image, its
walk / `ptreeMaps` facts, the preset warm TLB `AxSpinT2pt.tlbW` with its MachCSL invariant, the
64-entry TLB's slot facts for the mapped pages, and the per-hart entry register files
`AxSpinT2pt.regsE h` at allocproc + 0x38.

Lean-only (no Rocq source).  Design `notes/weak-lb-thm2-design.md` §C.6, §D row `AxSpinT2c`,
§E Q-T2-8 (in ../xv6iris-lbthm2).  MOVED here from the (deleted) de-risking spike
`AxSpinT2Spike` (proofs kept); measurements `PROGRESS-AxSpinT2Spike.md`.  The light half of
certificate (a′): the computation modules `AxSpinT2c1` (rows, graph, row premises),
`AxSpinT2c2/3/4` (one drive per hart) and `AxSpinT2c5` (the text / page-table image) import it.

## What this file proves

§1 THE TABLE.  `tX : PTree` — the identity map of KERNBASE..`end` (pages 0x80000 .. 0x80023, ONE
L0 table) with kvmmake's permissions (text pages below `etext` `KPerm.rx`, the rest `KPerm.rw`),
leaves `kLeaf ppn perm 1 1` (A = D = 1 PRESET, so no walker write-back), pointers `kPtr`, table
pages 0x87fff / 0x87ffe / 0x87ffd (the first pages `kalloc` hands out: top of RAM).
`layoutFacts` (the kernel symbols the table is built for), `tXWalk` (the MachCSL walk of every
mapped page and its TLB slot), `tXMaps` (`AxPtProt.ptreeMaps` — the shape the `dataAtS`/`hitW`
leaves consume — for EVERY mapped page: text, nextpid, stack0, pid_lock, cpus, all of proc[]).
§2 THE WARM TLB.  `tlbW` (every mapped page cached at its hash slot), `tlbWOk` (MachCSL
`tlbOk tX tlbW`: warming the TLB outside the graph is sound for `tX`), `tlbWHit` (the TLB hits
every mapped page: `tlbHitv tlbW (vpnOf j)` for `j < nPages`), `tlbSlotInj` (THE NON-COLLISION
FACT: the mapped pages occupy pairwise different slots of the 64-entry direct-mapped TLB — the
36 pages are consecutive, `tlbHash` is VPN[5:0]).
§3 THE ENTRY REGISTERS.  `regsE h`: S-mode at allocproc + 0x38 (`auipc a0,0x11`, the inlined
allocpid's first instruction), `satp` → `tX` (Sv39, ASID 0), `s1 = &proc[h]`, `sp = stack0 +
4096 (h + 1) − 64` (`spOf h`, allocproc's frame base in `stack0`'s page h + 1), `s0 = sp + 32`,
`tp = h`, SIE = 0, `tlb := tlbW` (WARM); `regsEFacts`, `satpXFacts` (the mode / ASID / root
premises of the S-mode leaves).

## Pins / honesty
* `tX` is kvmmake-SHAPED (permissions, identity, A/D preset), not kvmmake's literal output: no
  UART/VIRTIO/PLIC/trampoline/kstack mappings, the data map stops at `end` (kvmmake: PHYSTOP),
  and kvmmake leaves A = D = 0 (Svadu would write them back; the preset is the design's HAD
  scope, §A.5).  The non-collision fact is a property of THIS map: all of Theorem 2's touched
  pages lie in KERNBASE .. `end` (36 < 64 consecutive pages, `AxSpinT2c1.touchPage`).
* `regsE` is `AxSpinSpikeRun`'s S-mode register file (`rRegs`) re-pointed; nothing here proves
  the S-mode control invariant (`ctrlOkSW`) of it.

Reused: MachCSL `PTree`/`kLeaf`/`kPtr`/`tlbEntryOf`/`tlbOk`/`tlbHash`/`pteAddr`/`pteValid`/
`ptePtr`/`uNextBase`, `AxPtProt.ptreeMaps`/`vpnIdx`, `tlbHitv` (AxSymCtl4), `rRegs`
(AxSpinSpikeRun), tactic `ax_epi_ledger_krfl` (AxEpiLedger).
Names: all Lean-only, in the namespace `Weak.AxSpinT2pt` (file-qualified).
-/
import Weak.AxPtProt
import Weak.AxSpinSpikeRun
import Weak.AxEpiLedger
import Weak.AxSymCtl4

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D LeanRV64D.Functions

namespace AxSpinT2pt

/-! # 1. The table -/

/-- The table pages (root, L1, L0): the first three pages `kalloc` hands out (top of RAM). -/
def ptRoot : Nat := 0x87fff
def ptL1 : Nat := 0x87ffe
def ptL0 : Nat := 0x87ffd
/-- KERNBASE's page. -/
def kbase : Nat := 0x80000
/-- Pages mapped: KERNBASE .. `end` (0x80023b10), one L0 table. -/
def nPages : Nat := 0x24
/-- Text pages: KERNBASE .. `etext` (0x80007000). -/
def textPages : Nat := 7

/-- The layout the table is built for (this tree's kernel image). -/
theorem layoutFacts :
    KernelSyms.«etext» = (kbase + textPages) * 4096 ∧ KernelSyms.«end» ≤ (kbase + nPages) * 4096 ∧
    nPages ≤ 64 ∧ (kbase + nPages) * 4096 ≤ ptL0 * 4096 ∧
    KernelSyms.«pid_lock» / 4096 = kbase + 0x12 ∧ KernelSyms.«nextpid» / 4096 = kbase + 0xa ∧
    KernelSyms.«cpus» / 4096 = kbase + 0x12 ∧ KernelSyms.«proc» / 4096 = kbase + 0x12 ∧
    (KernelSyms.«proc» + 64 * 376) / 4096 = kbase + 0x18 ∧
    KernelSyms.«stack0» / 4096 = kbase + 0xa ∧ (KernelSyms.«stack0» + 0x8000) / 4096 = kbase + 0x12 := by
  decide

/-- kvmmake's permission for page `kbase + j`: text R X, data R W. -/
def permAt (j : Nat) : KPerm := if j < textPages then .rx else .rw
/-- The leaf of page `kbase + j` (MachCSL `kLeaf`, A = D = 1 preset). -/
def leafAt (j : Nat) : BitVec 64 := kLeaf (BitVec.ofNat 44 (kbase + j)) (permAt j) 1#1 1#1

def tX0 : PTree :=
  .node (BitVec.ofNat 44 ptL0) (fun i => if i.toNat < nPages then leafAt i.toNat else 0#64)
    (fun _ => none)
def tX1 : PTree :=
  .node (BitVec.ofNat 44 ptL1) (fun i => if i.toNat = 0 then kPtr (BitVec.ofNat 44 ptL0) else 0#64)
    (fun i => if i.toNat = 0 then some tX0 else none)
/-- THE TABLE. -/
def tX : PTree :=
  .node (BitVec.ofNat 44 ptRoot)
    (fun i => if i.toNat = 2 then kPtr (BitVec.ofNat 44 ptL1) else 0#64)
    (fun i => if i.toNat = 2 then some tX1 else none)

/-- The pointer words on the way down. -/
def p2X : BitVec 64 := kPtr (BitVec.ofNat 44 ptL1)
def p1X : BitVec 64 := kPtr (BitVec.ofNat 44 ptL0)

/-- The Sv39 VPN of page `kbase + j` (VA = PA). -/
def vpnOf (j : Nat) : BitVec 27 := BitVec.ofNat 27 (kbase + j)
/-- The PA of page `kbase + j`'s leaf slot. -/
def addrOf (j : Nat) : BitVec 64 := pteAddr (BitVec.ofNat 44 ptL0) (BitVec.ofNat 9 j)

/-- The MachCSL walk of every mapped page, and its TLB slot. -/
theorem tXWalk : ∀ j, j < nPages →
    tlbHash (vpnOf j) = j ∧
    tX.walk 2 (vpnOf j) = some (addrOf j, kLeaf (BitVec.ofNat 44 (kbase + j)) (permAt j) 1#1 1#1) := by
  decide +kernel

/-- The index / flag facts behind `tXMaps`, for every mapped page. -/
theorem tXBits : ∀ j, j < nPages →
    AxPtProt.vpnIdx 2 (vpnOf j) = 2#9 ∧ AxPtProt.vpnIdx 1 (vpnOf j) = 0#9 ∧
    AxPtProt.vpnIdx 0 (vpnOf j) = BitVec.ofNat 9 j ∧ (BitVec.ofNat 9 j).toNat = j ∧
    Sail.BitVec.extractLsb (leafAt j) 7 0 = (if j < textPages then 0xCB#8 else 0xC7#8) ∧
    ext_bits_of_PTE (leafAt j) = 0#10 ∧
    pte_is_non_leaf (Mk_PTE_Flags (Sail.BitVec.extractLsb (leafAt j) 7 0)) = false ∧
    (_get_PTE_Ext_N (ext_bits_of_PTE (leafAt j)) == 1#1) = false ∧
    _get_PTE_Ext_PBMT (ext_bits_of_PTE (leafAt j)) = 0#2 := by
  decide +kernel

theorem pteValidRX (w : BitVec 64) (h1 : Sail.BitVec.extractLsb w 7 0 = 0xCB#8)
    (h2 : ext_bits_of_PTE w = 0#10) : pteValid w := by
  unfold pteValid; rw [h1, h2]; intro s; ax_epi_ledger_krfl

theorem pteValidRW (w : BitVec 64) (h1 : Sail.BitVec.extractLsb w 7 0 = 0xC7#8)
    (h2 : ext_bits_of_PTE w = 0#10) : pteValid w := by
  unfold pteValid; rw [h1, h2]; intro s; ax_epi_ledger_krfl

theorem p2XFacts : uNextBase p2X = tX1.base ∧ pteValid p2X ∧ ptePtr p2X := by
  refine ⟨by decide +kernel, ?_, ?_⟩
  · unfold pteValid; intro s; ax_epi_ledger_krfl
  · unfold ptePtr; decide +kernel

theorem p1XFacts : uNextBase p1X = tX0.base ∧ pteValid p1X ∧ ptePtr p1X := by
  refine ⟨by decide +kernel, ?_, ?_⟩
  · unfold pteValid; intro s; ax_epi_ledger_krfl
  · unfold ptePtr; decide +kernel

/-- **Q-T2-8.**  `tX` 4K-maps EVERY page of KERNBASE..`end` (text, nextpid, stack0, pid_lock,
cpus, all of proc[]) in the `AxPtProt.ptreeMaps` shape the data/text leaves consume. -/
theorem tXMaps (j : Nat) (hj : j < nPages) :
    AxPtProt.ptreeMaps tX (vpnOf j) p2X p1X (leafAt j) := by
  obtain ⟨h2, h1, h0, hn, hfl, hext, hleaf, hnap, hpb⟩ := tXBits j hj
  obtain ⟨hb2, hv2, hp2⟩ := p2XFacts
  obtain ⟨hb1, hv1, hp1⟩ := p1XFacts
  refine ⟨tX1, tX0, ?_, ?_, ?_, ?_, ?_, hb2, hb1, hv2, hp2, hv1, hp1, ?_, hleaf, hnap, hpb⟩
  · rw [h2]; rfl
  · rw [h1]; rfl
  · rw [h2]; rfl
  · rw [h1]; rfl
  · rw [h0]; show (if (BitVec.ofNat 9 j).toNat < nPages then leafAt (BitVec.ofNat 9 j).toNat else 0#64) = _
    rw [hn, if_pos hj]
  · by_cases ht : j < textPages
    · rw [if_pos ht] at hfl; exact pteValidRX _ hfl hext
    · rw [if_neg ht] at hfl; exact pteValidRW _ hfl hext

/-! # 2. The warm TLB -/

/-- The preset TLB entry of page `kbase + j` (what `add_to_TLB` installs after a level-0 walk). -/
def tlbEnt (j : Nat) : TLB_Entry :=
  tlbEntryOf 0#16 (vpnOf j) (BitVec.ofNat 44 (kbase + j)) (leafAt j) (addrOf j)

/-- THE WARM TLB: every mapped page cached (36 distinct slots). -/
def tlbW : Tlb :=
  Vector.ofFn fun i : Fin (2 ^ 6) => if i.val < nPages then some (tlbEnt i.val) else none

/-- **Warm start, justified.**  The MachCSL TLB invariant: `tlbW` caches only leaves `tX`'s walk
reaches, each at its hash slot (so warming the TLB OUTSIDE the graph is sound for `tX`). -/
theorem tlbWOk : tlbOk tX tlbW := by
  intro i hi ent h
  simp only [tlbW, Vector.getElem_ofFn] at h
  by_cases hn : i < nPages
  · rw [if_pos hn] at h
    obtain rfl := Option.some.inj h
    obtain ⟨hh, hw⟩ := tXWalk i hn
    exact ⟨vpnOf i, addrOf i, BitVec.ofNat 44 (kbase + i), permAt i, 1#1, 1#1, 1#1, 1#1, hh, hw, rfl⟩
  · rw [if_neg hn] at h; cases h

/-- The warm TLB HITS every mapped page (the predicate under `hitW`). -/
theorem tlbWHit : ∀ j, j < nPages → tlbHitv tlbW (vpnOf j) = true := by
  decide +kernel

/-- **TLB NON-COLLISION.**  The mapped pages occupy pairwise different slots of the 64-entry
direct-mapped TLB (`tlbHash` = VPN[5:0]; the 36 pages are consecutive). -/
theorem tlbSlotInj (j1 j2 : Nat) (h1 : j1 < nPages) (h2 : j2 < nPages) :
    tlbHash (vpnOf j1) = tlbHash (vpnOf j2) → j1 = j2 := by
  rw [(tXWalk j1 h1).1, (tXWalk j2 h2).1]
  exact id

/-! # 3. The entry registers -/

/-- Sv39, root `ptRoot`, ASID 0. -/
def satpX : Nat := (8 <<< 60) ||| ptRoot

/-- Entry: `auipc a0,0x11` at allocproc+0x38 (the inlined allocpid's first instruction). -/
def entryPc : Nat := KernelSyms.«allocproc» + 0x38
/-- After the segment: allocproc+0x9c (the terminal `sw a5,24(s1)` is at +0x9a). -/
def exitPc : Nat := KernelSyms.«allocproc» + 0x9c
/-- `&proc[j]`. -/
def procAt (j : Nat) : Nat := KernelSyms.«proc» + 376 * j
/-- Hart `h`'s allocproc frame base (sp at allocproc + 0x38, in `stack0`'s page h+1). -/
def spOf (h : Nat) : Nat := KernelSyms.«stack0» + 4096 * (h + 1) - 64

/-- Entry registers of hart `h` (slot `proc[h]`), WARM TLB. -/
def regsE (h : Nat) : RegFile :=
  let rs := (rRegs entryPc).set .satp (BitVec.ofNat 64 satpX)
  let rs := rs.set .x9 (BitVec.ofNat 64 (procAt h))
  let rs := rs.set .x2 (BitVec.ofNat 64 (spOf h))
  let rs := rs.set .x8 (BitVec.ofNat 64 (spOf h + 32))
  let rs := rs.set .x4 (BitVec.ofNat 64 h)
  rs.set .tlb tlbW

theorem regsEFacts (h : Nat) :
    (regsE h) .tlb = tlbW ∧ (regsE h) .satp = BitVec.ofNat 64 satpX ∧
    (regsE h) .PC = BitVec.ofNat 64 entryPc := ⟨rfl, rfl, rfl⟩

theorem satpXFacts : _get_Satp64_Mode (Mk_Satp64 (BitVec.ofNat 64 satpX)) = 8#4 ∧
    zero_extend (m := 16) (satp_to_asid (BitVec.ofNat 64 satpX)) = 0#16 ∧
    BitVec.setWidth 44 (satp_to_ppn (BitVec.ofNat 64 satpX)) = tX.base := by
  decide +kernel

end AxSpinT2pt

end Weak
