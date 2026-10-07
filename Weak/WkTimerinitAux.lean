/-
Weak: **the per-instruction scaffolding of the weak `timerinit()` chain** -- the decode facts
at the reference state `WkEntryEff.dstateM` and the 21 `winstrM` tokens built from them.

Rocq: `iris/WkTimerinitAux.v` @ xxvzwolszwmp.

The Rocq header, in substance.  Split out of `WkTimerinit` for the reason `WkStartAux` was
split out of `WkStartNew`: the decode layer is STABLE while the proof script above it is
iterated.  Nothing here is weak-memory-specific; it is `CodeTimerinitAux`'s vocabulary
re-derived in the `winstrM` shape the SC-shaped leaves consume.  ONE LEMMA PER INSTRUCTION:
`wstiNN kbs hcov` is the whole token `wkernelText kbs ⊢ winstrM tiPcNN is_rvc i`, and a call
site never mentions a decode fact again.  §0 the vocabulary; §1 the image windows; §2 the
decode facts at `dstateM`; §3 the tokens.

**Deviations from Rocq.**
1. VOCABULARY: `Weak/WeakLeafM.lean` deviation 1 and `Weak/WkEntryEff.lean` deviations 1/3/4
   (`KernelInstrs.kernel_bytes !! A` ↦ `WkEntryEff.kernelBytes A`, `kb_word_at` ↦
   `WkEntryEff.kbWordAt`, `nth_byte` ↦ `nthByte (n := 4)`, `mword_of_int A : mword 64` ↦
   `BitVec.ofInt 64 A`, `D_m`/`D_none`/`dstateM` ↦ `WkEntryEff.dM`/`dNone`/`WkEntryEff.dstateM`,
   `wkb_covers`/`wkernel_text` ↦ `wkbCovers`/`wkernelText`, `sign_extend' n` ↦
   `sign_extend (m := n)`, `zero_extend' n` ↦ `zero_extend (m := n)`, `concat_vec` ↦ `+++`,
   `zeros' 12` ↦ `zeros (n := 12)`, `Cregidx (mword_of_int k)` ↦ `.Cregidx k#3`).  The CSR
   numbers are literals, as in `WeakLeafM` (`WpGprCsrrB.csr_menvcfg` / `WpGprCsrwA.csr_menvcfg`
   ↦ `0x30A#12`, `csr_mcounteren` ↦ `0x306#12`, `csr_time` ↦ `0xC01#12`,
   `WpGprCsrwB.csr_stimecmp` ↦ `0x14D#12`).
2. THE SC VOCABULARY.  Rocq `CodeTimerinitAux` (no Lean twin, by design: `notes/weak-port-map.md`)
   and `WpMmodeLeafBase`'s `csp_rs1`/`cli_rs1` are restated here, file-qualified
   (`WkTimerinitAux.*`, §0): `tiRa tiS0 tiA4 tiA5 tiCs0 tiCa4 tiCa5 i9 u10 u11 nz12 i14 sh15
   i19 i22 i23 i28 cspRs1 cliRs1 tiPc9 … tiPc29`.  `tiPc9` is `BitVec.ofInt 64 (timerinit +
   0x0)` (Rocq: without the `+ 0x0`), so that every `tiPcNN` is literally the window address of
   its `tikbNN`.  `caddi4spn_imm` is `ExecSC.caddi4spnImm`.
3. THE KERNEL IMAGE: the Lean image (`Xv6/KernelImage.lean`, `timerinit = 0x8000001c`) has the
   same 21 instructions at the same offsets with the same encodings as the Rocq image, so
   there is no drift; the `tikbNN` facts are checked against `KernelSitesDef.kbyte`.
4. THE DECODE FACTS: Rocq's generated catalogue `KernelDecode*.kd_*` (the ∀-state shape that
   `winstr_m_of_text` takes as a term) ↦ the `WkEntryNew` recipe: two read-only walks per
   instruction, `WkTimerinitAux.walkNNM` on `MachCSL.drefM` and `WkTimerinitAux.walkNNS` on
   `WkEntryNew.drefS0`, closed by `kernel_rfl` and fed to `WkEntryNew.decBase`/`decRvc`.
   Rocq's `vm_refl` Ltac (`vm_compute` plus `bv_eq`) ↦ `decide +kernel` (the `goodb0` and
   landing-pad facts) and `kernel_rfl` (the `exec … dstateM` decodes; `ExecSt` has no
   `DecidableEq`).  The compressed expansions `tigoodexpNN`/`tiexpNN` are `rfl` (Lean's
   `execute (.C_* …)` is `pure (.ExecuteAs …)`; Rocq cites `exec_execute_C_*`).
5. THE TOKENS: Rocq's 21 inlined `winstr_m_of_text` applications are factored through the
   Lean-only builders `WkTimerinitAux.tokBase` / `WkTimerinitAux.tokRvc` (the application
   together with `wkbWindow`); each `wstiNN` is one application of a builder.  The statements
   of `wstiNN` are Rocq's (`kbs`, `wkbCovers kbs`, `wkernelText kbs ⊢ winstrM …`).

**Rocq → Lean name map.**  `tikb_NN` `tikbNN`, `tigood_NN` `tigoodNN`, `tidec_NN` `tidecNN`,
`tilpad_NN` `tilpadNN`, `tigoodexp_NN` `tigoodexpNN`, `tiexp_NN` `tiexpNN`, `wsti_NN` `wstiNN`
(NN = 9 … 29; none in the duplicated-name table).  `vm_refl` (Ltac): not ported (deviation 4).
Lean-only stand-ins (file-qualified, deviation 2): `WkTimerinitAux.tiRa` … `tiPc29`.  Lean-only
helpers (file-qualified): `WkTimerinitAux.walkNNM`/`walkNNS` (42 walks), `tokBase`, `tokRvc`.

**Dropped:** nothing but the `vm_refl` Ltac (Rocq 120 lemmas + 1 Ltac; Lean the 120 theorems +
84 Lean-only declarations: 19 vocabulary definitions, the 21 `tiPcNN`, the 42 walks, the 2
builders).
-/
import Weak.WeakLeafM

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std
open MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D LeanRV64D.Functions
open WkEntryEff

/-! ## 0. The `timerinit()` vocabulary (Lean-only stand-ins, deviation 2) -/

/-- Rocq `ti_ra` (x1). -/
def WkTimerinitAux.tiRa : BitVec 5 := 1#5
/-- Rocq `ti_s0` (x8). -/
def WkTimerinitAux.tiS0 : BitVec 5 := 8#5
/-- Rocq `ti_a4` (x14). -/
def WkTimerinitAux.tiA4 : BitVec 5 := 14#5
/-- Rocq `ti_a5` (x15). -/
def WkTimerinitAux.tiA5 : BitVec 5 := 15#5
/-- Rocq `ti_cs0` (x8 as a creg). -/
def WkTimerinitAux.tiCs0 : cregidx := .Cregidx 0#3
/-- Rocq `ti_ca4` (x14 as a creg). -/
def WkTimerinitAux.tiCa4 : cregidx := .Cregidx 6#3
/-- Rocq `ti_ca5` (x15 as a creg). -/
def WkTimerinitAux.tiCa5 : cregidx := .Cregidx 7#3
/-- Rocq `i9`: c.addi imm = -16 (6-bit). -/
def WkTimerinitAux.i9 : BitVec 6 := 48#6
/-- Rocq `u10`: c.sdsp/c.ldsp ra offset 8. -/
def WkTimerinitAux.u10 : BitVec 6 := 1#6
/-- Rocq `u11`: c.sdsp/c.ldsp s0 offset 0. -/
def WkTimerinitAux.u11 : BitVec 6 := 0#6
/-- Rocq `nz12`: c.addi4spn nzimm (16/4). -/
def WkTimerinitAux.nz12 : BitVec 8 := 4#8
/-- Rocq `i14`: c.li imm = -1 (6-bit). -/
def WkTimerinitAux.i14 : BitVec 6 := 63#6
/-- Rocq `sh15`: c.slli shamt. -/
def WkTimerinitAux.sh15 : BitVec 6 := 63#6
/-- Rocq `i19`: ori imm. -/
def WkTimerinitAux.i19 : BitVec 12 := 2#12
/-- Rocq `i22`: lui imm. -/
def WkTimerinitAux.i22 : BitVec 20 := 0xf4#20
/-- Rocq `i23`: addi imm. -/
def WkTimerinitAux.i23 : BitVec 12 := 576#12
/-- Rocq `i28`: c.addi imm = +16. -/
def WkTimerinitAux.i28 : BitVec 6 := 16#6
/-- Rocq `WpMmodeLeafBase.csp_rs1` (the stack pointer, as the model's `sp`). -/
def WkTimerinitAux.cspRs1 : BitVec 5 := zero_extend (m := 5) 0b10#2
/-- Rocq `WpMmodeLeafBase.cli_rs1` (x0, as the model's `zreg`). -/
def WkTimerinitAux.cliRs1 : BitVec 5 := zero_extend (m := 5) 0b00#2


section pcs
/-- Rocq `ti_pc9` (c.addi sp, -16). -/
def WkTimerinitAux.tiPc9 : BitVec 64 := BitVec.ofInt 64 ((KernelSyms.«timerinit» : Int) + 0x0)

/-- Rocq `ti_pc10` (c.sdsp ra, 8(sp)). -/
def WkTimerinitAux.tiPc10 : BitVec 64 := BitVec.ofInt 64 ((KernelSyms.«timerinit» : Int) + 0x2)

/-- Rocq `ti_pc11` (c.sdsp s0, 0(sp)). -/
def WkTimerinitAux.tiPc11 : BitVec 64 := BitVec.ofInt 64 ((KernelSyms.«timerinit» : Int) + 0x4)

/-- Rocq `ti_pc12` (c.addi4spn s0, sp, 16). -/
def WkTimerinitAux.tiPc12 : BitVec 64 := BitVec.ofInt 64 ((KernelSyms.«timerinit» : Int) + 0x6)

/-- Rocq `ti_pc13` (csrr a5, menvcfg). -/
def WkTimerinitAux.tiPc13 : BitVec 64 := BitVec.ofInt 64 ((KernelSyms.«timerinit» : Int) + 0x8)

/-- Rocq `ti_pc14` (c.li a4, -1). -/
def WkTimerinitAux.tiPc14 : BitVec 64 := BitVec.ofInt 64 ((KernelSyms.«timerinit» : Int) + 0xc)

/-- Rocq `ti_pc15` (c.slli a4, 63). -/
def WkTimerinitAux.tiPc15 : BitVec 64 := BitVec.ofInt 64 ((KernelSyms.«timerinit» : Int) + 0xe)

/-- Rocq `ti_pc16` (c.or a5, a4). -/
def WkTimerinitAux.tiPc16 : BitVec 64 := BitVec.ofInt 64 ((KernelSyms.«timerinit» : Int) + 0x10)

/-- Rocq `ti_pc17` (csrw menvcfg, a5). -/
def WkTimerinitAux.tiPc17 : BitVec 64 := BitVec.ofInt 64 ((KernelSyms.«timerinit» : Int) + 0x12)

/-- Rocq `ti_pc18` (csrr a5, mcounteren). -/
def WkTimerinitAux.tiPc18 : BitVec 64 := BitVec.ofInt 64 ((KernelSyms.«timerinit» : Int) + 0x16)

/-- Rocq `ti_pc19` (ori a5, a5, 2). -/
def WkTimerinitAux.tiPc19 : BitVec 64 := BitVec.ofInt 64 ((KernelSyms.«timerinit» : Int) + 0x1a)

/-- Rocq `ti_pc20` (csrw mcounteren, a5). -/
def WkTimerinitAux.tiPc20 : BitVec 64 := BitVec.ofInt 64 ((KernelSyms.«timerinit» : Int) + 0x1e)

/-- Rocq `ti_pc21` (csrr a5, time). -/
def WkTimerinitAux.tiPc21 : BitVec 64 := BitVec.ofInt 64 ((KernelSyms.«timerinit» : Int) + 0x22)

/-- Rocq `ti_pc22` (lui a4, 0xf4). -/
def WkTimerinitAux.tiPc22 : BitVec 64 := BitVec.ofInt 64 ((KernelSyms.«timerinit» : Int) + 0x26)

/-- Rocq `ti_pc23` (addi a4, a4, 576). -/
def WkTimerinitAux.tiPc23 : BitVec 64 := BitVec.ofInt 64 ((KernelSyms.«timerinit» : Int) + 0x2a)

/-- Rocq `ti_pc24` (c.add a5, a4). -/
def WkTimerinitAux.tiPc24 : BitVec 64 := BitVec.ofInt 64 ((KernelSyms.«timerinit» : Int) + 0x2e)

/-- Rocq `ti_pc25` (csrw stimecmp, a5). -/
def WkTimerinitAux.tiPc25 : BitVec 64 := BitVec.ofInt 64 ((KernelSyms.«timerinit» : Int) + 0x30)

/-- Rocq `ti_pc26` (c.ldsp ra, 8(sp)). -/
def WkTimerinitAux.tiPc26 : BitVec 64 := BitVec.ofInt 64 ((KernelSyms.«timerinit» : Int) + 0x34)

/-- Rocq `ti_pc27` (c.ldsp s0, 0(sp)). -/
def WkTimerinitAux.tiPc27 : BitVec 64 := BitVec.ofInt 64 ((KernelSyms.«timerinit» : Int) + 0x36)

/-- Rocq `ti_pc28` (c.addi sp, 16). -/
def WkTimerinitAux.tiPc28 : BitVec 64 := BitVec.ofInt 64 ((KernelSyms.«timerinit» : Int) + 0x38)

/-- Rocq `ti_pc29` (c.ret). -/
def WkTimerinitAux.tiPc29 : BitVec 64 := BitVec.ofInt 64 ((KernelSyms.«timerinit» : Int) + 0x3a)

end pcs

/-! ## 1. Kernel-image byte windows (`WkEntryEff.wkbWindow`'s input)

The window word is `kbWordAt A` -- literally the four bytes at `A..A+3` -- at the RVC sites,
and the instruction word itself at the base sites (Rocq's split). -/

section kb

/-- Rocq `tikb_9`. -/
theorem tikb9 : ∀ j : Nat, j < 4 →
    kernelBytes (((KernelSyms.«timerinit» : Int) + 0x0) + (j : Int)) = some (nthByte (n := 4) (kbWordAt ((KernelSyms.«timerinit» : Int) + 0x0)) j) := by
  wk_entry_kb_win

/-- Rocq `tikb_10`. -/
theorem tikb10 : ∀ j : Nat, j < 4 →
    kernelBytes (((KernelSyms.«timerinit» : Int) + 0x2) + (j : Int)) = some (nthByte (n := 4) (kbWordAt ((KernelSyms.«timerinit» : Int) + 0x2)) j) := by
  wk_entry_kb_win

/-- Rocq `tikb_11`. -/
theorem tikb11 : ∀ j : Nat, j < 4 →
    kernelBytes (((KernelSyms.«timerinit» : Int) + 0x4) + (j : Int)) = some (nthByte (n := 4) (kbWordAt ((KernelSyms.«timerinit» : Int) + 0x4)) j) := by
  wk_entry_kb_win

/-- Rocq `tikb_12`. -/
theorem tikb12 : ∀ j : Nat, j < 4 →
    kernelBytes (((KernelSyms.«timerinit» : Int) + 0x6) + (j : Int)) = some (nthByte (n := 4) (kbWordAt ((KernelSyms.«timerinit» : Int) + 0x6)) j) := by
  wk_entry_kb_win

/-- Rocq `tikb_13`. -/
theorem tikb13 : ∀ j : Nat, j < 4 →
    kernelBytes (((KernelSyms.«timerinit» : Int) + 0x8) + (j : Int)) = some (nthByte (n := 4) 0x30a027f3#32 j) := by
  wk_entry_kb_win

/-- Rocq `tikb_14`. -/
theorem tikb14 : ∀ j : Nat, j < 4 →
    kernelBytes (((KernelSyms.«timerinit» : Int) + 0xc) + (j : Int)) = some (nthByte (n := 4) (kbWordAt ((KernelSyms.«timerinit» : Int) + 0xc)) j) := by
  wk_entry_kb_win

/-- Rocq `tikb_15`. -/
theorem tikb15 : ∀ j : Nat, j < 4 →
    kernelBytes (((KernelSyms.«timerinit» : Int) + 0xe) + (j : Int)) = some (nthByte (n := 4) (kbWordAt ((KernelSyms.«timerinit» : Int) + 0xe)) j) := by
  wk_entry_kb_win

/-- Rocq `tikb_16`. -/
theorem tikb16 : ∀ j : Nat, j < 4 →
    kernelBytes (((KernelSyms.«timerinit» : Int) + 0x10) + (j : Int)) = some (nthByte (n := 4) (kbWordAt ((KernelSyms.«timerinit» : Int) + 0x10)) j) := by
  wk_entry_kb_win

/-- Rocq `tikb_17`. -/
theorem tikb17 : ∀ j : Nat, j < 4 →
    kernelBytes (((KernelSyms.«timerinit» : Int) + 0x12) + (j : Int)) = some (nthByte (n := 4) 0x30a79073#32 j) := by
  wk_entry_kb_win

/-- Rocq `tikb_18`. -/
theorem tikb18 : ∀ j : Nat, j < 4 →
    kernelBytes (((KernelSyms.«timerinit» : Int) + 0x16) + (j : Int)) = some (nthByte (n := 4) 0x306027f3#32 j) := by
  wk_entry_kb_win

/-- Rocq `tikb_19`. -/
theorem tikb19 : ∀ j : Nat, j < 4 →
    kernelBytes (((KernelSyms.«timerinit» : Int) + 0x1a) + (j : Int)) = some (nthByte (n := 4) 0x0027e793#32 j) := by
  wk_entry_kb_win

/-- Rocq `tikb_20`. -/
theorem tikb20 : ∀ j : Nat, j < 4 →
    kernelBytes (((KernelSyms.«timerinit» : Int) + 0x1e) + (j : Int)) = some (nthByte (n := 4) 0x30679073#32 j) := by
  wk_entry_kb_win

/-- Rocq `tikb_21`. -/
theorem tikb21 : ∀ j : Nat, j < 4 →
    kernelBytes (((KernelSyms.«timerinit» : Int) + 0x22) + (j : Int)) = some (nthByte (n := 4) 0xc01027f3#32 j) := by
  wk_entry_kb_win

/-- Rocq `tikb_22`. -/
theorem tikb22 : ∀ j : Nat, j < 4 →
    kernelBytes (((KernelSyms.«timerinit» : Int) + 0x26) + (j : Int)) = some (nthByte (n := 4) 0x000f4737#32 j) := by
  wk_entry_kb_win

/-- Rocq `tikb_23`. -/
theorem tikb23 : ∀ j : Nat, j < 4 →
    kernelBytes (((KernelSyms.«timerinit» : Int) + 0x2a) + (j : Int)) = some (nthByte (n := 4) 0x24070713#32 j) := by
  wk_entry_kb_win

/-- Rocq `tikb_24`. -/
theorem tikb24 : ∀ j : Nat, j < 4 →
    kernelBytes (((KernelSyms.«timerinit» : Int) + 0x2e) + (j : Int)) = some (nthByte (n := 4) (kbWordAt ((KernelSyms.«timerinit» : Int) + 0x2e)) j) := by
  wk_entry_kb_win

/-- Rocq `tikb_25`. -/
theorem tikb25 : ∀ j : Nat, j < 4 →
    kernelBytes (((KernelSyms.«timerinit» : Int) + 0x30) + (j : Int)) = some (nthByte (n := 4) 0x14d79073#32 j) := by
  wk_entry_kb_win

/-- Rocq `tikb_26`. -/
theorem tikb26 : ∀ j : Nat, j < 4 →
    kernelBytes (((KernelSyms.«timerinit» : Int) + 0x34) + (j : Int)) = some (nthByte (n := 4) (kbWordAt ((KernelSyms.«timerinit» : Int) + 0x34)) j) := by
  wk_entry_kb_win

/-- Rocq `tikb_27`. -/
theorem tikb27 : ∀ j : Nat, j < 4 →
    kernelBytes (((KernelSyms.«timerinit» : Int) + 0x36) + (j : Int)) = some (nthByte (n := 4) (kbWordAt ((KernelSyms.«timerinit» : Int) + 0x36)) j) := by
  wk_entry_kb_win

/-- Rocq `tikb_28`. -/
theorem tikb28 : ∀ j : Nat, j < 4 →
    kernelBytes (((KernelSyms.«timerinit» : Int) + 0x38) + (j : Int)) = some (nthByte (n := 4) (kbWordAt ((KernelSyms.«timerinit» : Int) + 0x38)) j) := by
  wk_entry_kb_win

/-- Rocq `tikb_29`. -/
theorem tikb29 : ∀ j : Nat, j < 4 →
    kernelBytes (((KernelSyms.«timerinit» : Int) + 0x3a) + (j : Int)) = some (nthByte (n := 4) (kbWordAt ((KernelSyms.«timerinit» : Int) + 0x3a)) j) := by
  wk_entry_kb_win

end kb

/-! ## 2. Decode facts

The Lean-only read-only walks on both reference maps (deviation 4; Rocq `KernelDecode*.kd_*`),
then Rocq's facts at the concrete reference state `dstateM`.  A BASE instruction needs
`tigoodNN` / `tidecNN`; an RVC one needs those two about the compressed encoding plus
`tilpadNN` (the compressed AST is not a landing pad), `tigoodexpNN` (its expansion reads no
register) and `tiexpNN` (what it expands to). -/

section walks
attribute [local semireducible] LeanRV64D.Functions.hartSupports
  LeanRV64D.Functions.currentlyEnabled
open WkTimerinitAux

theorem WkTimerinitAux.walk9M : runRead drefM (ext_decode_compressed 0x1141#16) =
    some (.C_ADDI (i9, .Regidx cspRs1), true) := by kernel_rfl

theorem WkTimerinitAux.walk9S : runRead WkEntryNew.drefS0 (ext_decode_compressed 0x1141#16) =
    some (.C_ADDI (i9, .Regidx cspRs1), true) := by kernel_rfl

theorem WkTimerinitAux.walk10M : runRead drefM (ext_decode_compressed 0xe406#16) =
    some (.C_SDSP (u10, .Regidx tiRa), true) := by kernel_rfl

theorem WkTimerinitAux.walk10S : runRead WkEntryNew.drefS0 (ext_decode_compressed 0xe406#16) =
    some (.C_SDSP (u10, .Regidx tiRa), true) := by kernel_rfl

theorem WkTimerinitAux.walk11M : runRead drefM (ext_decode_compressed 0xe022#16) =
    some (.C_SDSP (u11, .Regidx tiS0), true) := by kernel_rfl

theorem WkTimerinitAux.walk11S : runRead WkEntryNew.drefS0 (ext_decode_compressed 0xe022#16) =
    some (.C_SDSP (u11, .Regidx tiS0), true) := by kernel_rfl

theorem WkTimerinitAux.walk12M : runRead drefM (ext_decode_compressed 0x0800#16) =
    some (.C_ADDI4SPN (.Cregidx 0#3, nz12), true) := by kernel_rfl

theorem WkTimerinitAux.walk12S : runRead WkEntryNew.drefS0 (ext_decode_compressed 0x0800#16) =
    some (.C_ADDI4SPN (.Cregidx 0#3, nz12), true) := by kernel_rfl

theorem WkTimerinitAux.walk13M : runRead drefM (ext_decode 0x30a027f3#32) =
    some (.CSRReg (0x30A#12, zreg, .Regidx tiA5, .CSRRS), true) := by kernel_rfl

theorem WkTimerinitAux.walk13S : runRead WkEntryNew.drefS0 (ext_decode 0x30a027f3#32) =
    some (.CSRReg (0x30A#12, zreg, .Regidx tiA5, .CSRRS), true) := by kernel_rfl

theorem WkTimerinitAux.walk14M : runRead drefM (ext_decode_compressed 0x577d#16) =
    some (.C_LI (i14, .Regidx tiA4), true) := by kernel_rfl

theorem WkTimerinitAux.walk14S : runRead WkEntryNew.drefS0 (ext_decode_compressed 0x577d#16) =
    some (.C_LI (i14, .Regidx tiA4), true) := by kernel_rfl

theorem WkTimerinitAux.walk15M : runRead drefM (ext_decode_compressed 0x177e#16) =
    some (.C_SLLI (sh15, .Regidx tiA4), true) := by kernel_rfl

theorem WkTimerinitAux.walk15S : runRead WkEntryNew.drefS0 (ext_decode_compressed 0x177e#16) =
    some (.C_SLLI (sh15, .Regidx tiA4), true) := by kernel_rfl

theorem WkTimerinitAux.walk16M : runRead drefM (ext_decode_compressed 0x8fd9#16) =
    some (.C_OR (.Cregidx 7#3, .Cregidx 6#3), true) := by kernel_rfl

theorem WkTimerinitAux.walk16S : runRead WkEntryNew.drefS0 (ext_decode_compressed 0x8fd9#16) =
    some (.C_OR (.Cregidx 7#3, .Cregidx 6#3), true) := by kernel_rfl

theorem WkTimerinitAux.walk17M : runRead drefM (ext_decode 0x30a79073#32) =
    some (.CSRReg (0x30A#12, .Regidx tiA5, zreg, .CSRRW), true) := by kernel_rfl

theorem WkTimerinitAux.walk17S : runRead WkEntryNew.drefS0 (ext_decode 0x30a79073#32) =
    some (.CSRReg (0x30A#12, .Regidx tiA5, zreg, .CSRRW), true) := by kernel_rfl

theorem WkTimerinitAux.walk18M : runRead drefM (ext_decode 0x306027f3#32) =
    some (.CSRReg (0x306#12, zreg, .Regidx tiA5, .CSRRS), true) := by kernel_rfl

theorem WkTimerinitAux.walk18S : runRead WkEntryNew.drefS0 (ext_decode 0x306027f3#32) =
    some (.CSRReg (0x306#12, zreg, .Regidx tiA5, .CSRRS), true) := by kernel_rfl

theorem WkTimerinitAux.walk19M : runRead drefM (ext_decode 0x0027e793#32) =
    some (.ITYPE (i19, .Regidx tiA5, .Regidx tiA5, .ORI), true) := by kernel_rfl

theorem WkTimerinitAux.walk19S : runRead WkEntryNew.drefS0 (ext_decode 0x0027e793#32) =
    some (.ITYPE (i19, .Regidx tiA5, .Regidx tiA5, .ORI), true) := by kernel_rfl

theorem WkTimerinitAux.walk20M : runRead drefM (ext_decode 0x30679073#32) =
    some (.CSRReg (0x306#12, .Regidx tiA5, zreg, .CSRRW), true) := by kernel_rfl

theorem WkTimerinitAux.walk20S : runRead WkEntryNew.drefS0 (ext_decode 0x30679073#32) =
    some (.CSRReg (0x306#12, .Regidx tiA5, zreg, .CSRRW), true) := by kernel_rfl

theorem WkTimerinitAux.walk21M : runRead drefM (ext_decode 0xc01027f3#32) =
    some (.CSRReg (0xC01#12, zreg, .Regidx tiA5, .CSRRS), true) := by kernel_rfl

theorem WkTimerinitAux.walk21S : runRead WkEntryNew.drefS0 (ext_decode 0xc01027f3#32) =
    some (.CSRReg (0xC01#12, zreg, .Regidx tiA5, .CSRRS), true) := by kernel_rfl

theorem WkTimerinitAux.walk22M : runRead drefM (ext_decode 0x000f4737#32) =
    some (.UTYPE (i22, .Regidx tiA4, .LUI), true) := by kernel_rfl

theorem WkTimerinitAux.walk22S : runRead WkEntryNew.drefS0 (ext_decode 0x000f4737#32) =
    some (.UTYPE (i22, .Regidx tiA4, .LUI), true) := by kernel_rfl

theorem WkTimerinitAux.walk23M : runRead drefM (ext_decode 0x24070713#32) =
    some (.ITYPE (i23, .Regidx tiA4, .Regidx tiA4, .ADDI), true) := by kernel_rfl

theorem WkTimerinitAux.walk23S : runRead WkEntryNew.drefS0 (ext_decode 0x24070713#32) =
    some (.ITYPE (i23, .Regidx tiA4, .Regidx tiA4, .ADDI), true) := by kernel_rfl

theorem WkTimerinitAux.walk24M : runRead drefM (ext_decode_compressed 0x97ba#16) =
    some (.C_ADD (.Regidx tiA5, .Regidx tiA4), true) := by kernel_rfl

theorem WkTimerinitAux.walk24S : runRead WkEntryNew.drefS0 (ext_decode_compressed 0x97ba#16) =
    some (.C_ADD (.Regidx tiA5, .Regidx tiA4), true) := by kernel_rfl

theorem WkTimerinitAux.walk25M : runRead drefM (ext_decode 0x14d79073#32) =
    some (.CSRReg (0x14D#12, .Regidx tiA5, zreg, .CSRRW), true) := by kernel_rfl

theorem WkTimerinitAux.walk25S : runRead WkEntryNew.drefS0 (ext_decode 0x14d79073#32) =
    some (.CSRReg (0x14D#12, .Regidx tiA5, zreg, .CSRRW), true) := by kernel_rfl

theorem WkTimerinitAux.walk26M : runRead drefM (ext_decode_compressed 0x60a2#16) =
    some (.C_LDSP (u10, .Regidx tiRa), true) := by kernel_rfl

theorem WkTimerinitAux.walk26S : runRead WkEntryNew.drefS0 (ext_decode_compressed 0x60a2#16) =
    some (.C_LDSP (u10, .Regidx tiRa), true) := by kernel_rfl

theorem WkTimerinitAux.walk27M : runRead drefM (ext_decode_compressed 0x6402#16) =
    some (.C_LDSP (u11, .Regidx tiS0), true) := by kernel_rfl

theorem WkTimerinitAux.walk27S : runRead WkEntryNew.drefS0 (ext_decode_compressed 0x6402#16) =
    some (.C_LDSP (u11, .Regidx tiS0), true) := by kernel_rfl

theorem WkTimerinitAux.walk28M : runRead drefM (ext_decode_compressed 0x0141#16) =
    some (.C_ADDI (i28, .Regidx cspRs1), true) := by kernel_rfl

theorem WkTimerinitAux.walk28S : runRead WkEntryNew.drefS0 (ext_decode_compressed 0x0141#16) =
    some (.C_ADDI (i28, .Regidx cspRs1), true) := by kernel_rfl

theorem WkTimerinitAux.walk29M : runRead drefM (ext_decode_compressed 0x8082#16) =
    some (.C_JR (.Regidx tiRa), true) := by kernel_rfl

theorem WkTimerinitAux.walk29S : runRead WkEntryNew.drefS0 (ext_decode_compressed 0x8082#16) =
    some (.C_JR (.Regidx tiRa), true) := by kernel_rfl

end walks

section dec
open WkTimerinitAux

/-! #### 9. c.addi sp, -16 -/
/-- Rocq `tigood_9`. -/
theorem tigood9 : goodb0 dM (ext_decode_compressed 0x1141#16) dstateM = true := by decide +kernel
/-- Rocq `tidec_9`. -/
theorem tidec9 : exec (ext_decode_compressed 0x1141#16) dstateM =
    some (.C_ADDI (i9, .Regidx cspRs1), dstateM) := by kernel_rfl
/-- Rocq `tilpad_9`. -/
theorem tilpad9 : is_lpad_instruction (.C_ADDI (i9, .Regidx cspRs1)) = false := by decide +kernel
/-- Rocq `tigoodexp_9`. -/
theorem tigoodexp9 : ∀ s : ExecSt, goodb0 dNone (execute (.C_ADDI (i9, .Regidx cspRs1))) s = true :=
  fun _ => rfl
/-- Rocq `tiexp_9`. -/
theorem tiexp9 : ∀ s : ExecSt,
    exec (execute (.C_ADDI (i9, .Regidx cspRs1))) s =
      some (.ExecuteAs (.ITYPE (sign_extend (m := 12) i9, .Regidx cspRs1, .Regidx cspRs1, .ADDI)), s) :=
  fun _ => rfl

/-! #### 10. c.sdsp ra, 8(sp) -/
/-- Rocq `tigood_10`. -/
theorem tigood10 : goodb0 dM (ext_decode_compressed 0xe406#16) dstateM = true := by decide +kernel
/-- Rocq `tidec_10`. -/
theorem tidec10 : exec (ext_decode_compressed 0xe406#16) dstateM =
    some (.C_SDSP (u10, .Regidx tiRa), dstateM) := by kernel_rfl
/-- Rocq `tilpad_10`. -/
theorem tilpad10 : is_lpad_instruction (.C_SDSP (u10, .Regidx tiRa)) = false := by decide +kernel
/-- Rocq `tigoodexp_10`. -/
theorem tigoodexp10 : ∀ s : ExecSt, goodb0 dNone (execute (.C_SDSP (u10, .Regidx tiRa))) s = true :=
  fun _ => rfl
/-- Rocq `tiexp_10`. -/
theorem tiexp10 : ∀ s : ExecSt,
    exec (execute (.C_SDSP (u10, .Regidx tiRa))) s =
      some (.ExecuteAs (.STORE (zero_extend (m := 12) (u10 +++ 0b000#3), .Regidx tiRa, .Regidx cspRs1, 8)), s) :=
  fun _ => rfl

/-! #### 11. c.sdsp s0, 0(sp) -/
/-- Rocq `tigood_11`. -/
theorem tigood11 : goodb0 dM (ext_decode_compressed 0xe022#16) dstateM = true := by decide +kernel
/-- Rocq `tidec_11`. -/
theorem tidec11 : exec (ext_decode_compressed 0xe022#16) dstateM =
    some (.C_SDSP (u11, .Regidx tiS0), dstateM) := by kernel_rfl
/-- Rocq `tilpad_11`. -/
theorem tilpad11 : is_lpad_instruction (.C_SDSP (u11, .Regidx tiS0)) = false := by decide +kernel
/-- Rocq `tigoodexp_11`. -/
theorem tigoodexp11 : ∀ s : ExecSt, goodb0 dNone (execute (.C_SDSP (u11, .Regidx tiS0))) s = true :=
  fun _ => rfl
/-- Rocq `tiexp_11`. -/
theorem tiexp11 : ∀ s : ExecSt,
    exec (execute (.C_SDSP (u11, .Regidx tiS0))) s =
      some (.ExecuteAs (.STORE (zero_extend (m := 12) (u11 +++ 0b000#3), .Regidx tiS0, .Regidx cspRs1, 8)), s) :=
  fun _ => rfl

/-! #### 12. c.addi4spn s0, sp, 16 -/
/-- Rocq `tigood_12`. -/
theorem tigood12 : goodb0 dM (ext_decode_compressed 0x0800#16) dstateM = true := by decide +kernel
/-- Rocq `tidec_12`. -/
theorem tidec12 : exec (ext_decode_compressed 0x0800#16) dstateM =
    some (.C_ADDI4SPN (.Cregidx 0#3, nz12), dstateM) := by kernel_rfl
/-- Rocq `tilpad_12`. -/
theorem tilpad12 : is_lpad_instruction (.C_ADDI4SPN (.Cregidx 0#3, nz12)) = false := by decide +kernel
/-- Rocq `tigoodexp_12`. -/
theorem tigoodexp12 : ∀ s : ExecSt, goodb0 dNone (execute (.C_ADDI4SPN (.Cregidx 0#3, nz12))) s = true :=
  fun _ => rfl
/-- Rocq `tiexp_12`. -/
theorem tiexp12 : ∀ s : ExecSt,
    exec (execute (.C_ADDI4SPN (.Cregidx 0#3, nz12))) s =
      some (.ExecuteAs (.ITYPE (caddi4spnImm nz12, .Regidx cspRs1, .Regidx tiS0, .ADDI)), s) :=
  fun _ => rfl

/-! #### 13. csrr a5, menvcfg -/
/-- Rocq `tigood_13`. -/
theorem tigood13 : goodb0 dM (ext_decode 0x30a027f3#32) dstateM = true := by decide +kernel
/-- Rocq `tidec_13`. -/
theorem tidec13 : exec (ext_decode 0x30a027f3#32) dstateM =
    some (.CSRReg (0x30A#12, zreg, .Regidx tiA5, .CSRRS), dstateM) := by kernel_rfl

/-! #### 14. c.li a4, -1 -/
/-- Rocq `tigood_14`. -/
theorem tigood14 : goodb0 dM (ext_decode_compressed 0x577d#16) dstateM = true := by decide +kernel
/-- Rocq `tidec_14`. -/
theorem tidec14 : exec (ext_decode_compressed 0x577d#16) dstateM =
    some (.C_LI (i14, .Regidx tiA4), dstateM) := by kernel_rfl
/-- Rocq `tilpad_14`. -/
theorem tilpad14 : is_lpad_instruction (.C_LI (i14, .Regidx tiA4)) = false := by decide +kernel
/-- Rocq `tigoodexp_14`. -/
theorem tigoodexp14 : ∀ s : ExecSt, goodb0 dNone (execute (.C_LI (i14, .Regidx tiA4))) s = true :=
  fun _ => rfl
/-- Rocq `tiexp_14`. -/
theorem tiexp14 : ∀ s : ExecSt,
    exec (execute (.C_LI (i14, .Regidx tiA4))) s =
      some (.ExecuteAs (.ITYPE (sign_extend (m := 12) i14, .Regidx cliRs1, .Regidx tiA4, .ADDI)), s) :=
  fun _ => rfl

/-! #### 15. c.slli a4, 63 -/
/-- Rocq `tigood_15`. -/
theorem tigood15 : goodb0 dM (ext_decode_compressed 0x177e#16) dstateM = true := by decide +kernel
/-- Rocq `tidec_15`. -/
theorem tidec15 : exec (ext_decode_compressed 0x177e#16) dstateM =
    some (.C_SLLI (sh15, .Regidx tiA4), dstateM) := by kernel_rfl
/-- Rocq `tilpad_15`. -/
theorem tilpad15 : is_lpad_instruction (.C_SLLI (sh15, .Regidx tiA4)) = false := by decide +kernel
/-- Rocq `tigoodexp_15`. -/
theorem tigoodexp15 : ∀ s : ExecSt, goodb0 dNone (execute (.C_SLLI (sh15, .Regidx tiA4))) s = true :=
  fun _ => rfl
/-- Rocq `tiexp_15`. -/
theorem tiexp15 : ∀ s : ExecSt,
    exec (execute (.C_SLLI (sh15, .Regidx tiA4))) s =
      some (.ExecuteAs (.SHIFTIOP (sh15, .Regidx tiA4, .Regidx tiA4, .SLLI)), s) :=
  fun _ => rfl

/-! #### 16. c.or a5, a4 -/
/-- Rocq `tigood_16`. -/
theorem tigood16 : goodb0 dM (ext_decode_compressed 0x8fd9#16) dstateM = true := by decide +kernel
/-- Rocq `tidec_16`. -/
theorem tidec16 : exec (ext_decode_compressed 0x8fd9#16) dstateM =
    some (.C_OR (.Cregidx 7#3, .Cregidx 6#3), dstateM) := by kernel_rfl
/-- Rocq `tilpad_16`. -/
theorem tilpad16 : is_lpad_instruction (.C_OR (.Cregidx 7#3, .Cregidx 6#3)) = false := by decide +kernel
/-- Rocq `tigoodexp_16`. -/
theorem tigoodexp16 : ∀ s : ExecSt, goodb0 dNone (execute (.C_OR (.Cregidx 7#3, .Cregidx 6#3))) s = true :=
  fun _ => rfl
/-- Rocq `tiexp_16`. -/
theorem tiexp16 : ∀ s : ExecSt,
    exec (execute (.C_OR (.Cregidx 7#3, .Cregidx 6#3))) s =
      some (.ExecuteAs (.RTYPE (.Regidx tiA4, .Regidx tiA5, .Regidx tiA5, .OR)), s) :=
  fun _ => rfl

/-! #### 17. csrw menvcfg, a5 -/
/-- Rocq `tigood_17`. -/
theorem tigood17 : goodb0 dM (ext_decode 0x30a79073#32) dstateM = true := by decide +kernel
/-- Rocq `tidec_17`. -/
theorem tidec17 : exec (ext_decode 0x30a79073#32) dstateM =
    some (.CSRReg (0x30A#12, .Regidx tiA5, zreg, .CSRRW), dstateM) := by kernel_rfl

/-! #### 18. csrr a5, mcounteren -/
/-- Rocq `tigood_18`. -/
theorem tigood18 : goodb0 dM (ext_decode 0x306027f3#32) dstateM = true := by decide +kernel
/-- Rocq `tidec_18`. -/
theorem tidec18 : exec (ext_decode 0x306027f3#32) dstateM =
    some (.CSRReg (0x306#12, zreg, .Regidx tiA5, .CSRRS), dstateM) := by kernel_rfl

/-! #### 19. ori a5, a5, 2 -/
/-- Rocq `tigood_19`. -/
theorem tigood19 : goodb0 dM (ext_decode 0x0027e793#32) dstateM = true := by decide +kernel
/-- Rocq `tidec_19`. -/
theorem tidec19 : exec (ext_decode 0x0027e793#32) dstateM =
    some (.ITYPE (i19, .Regidx tiA5, .Regidx tiA5, .ORI), dstateM) := by kernel_rfl

/-! #### 20. csrw mcounteren, a5 -/
/-- Rocq `tigood_20`. -/
theorem tigood20 : goodb0 dM (ext_decode 0x30679073#32) dstateM = true := by decide +kernel
/-- Rocq `tidec_20`. -/
theorem tidec20 : exec (ext_decode 0x30679073#32) dstateM =
    some (.CSRReg (0x306#12, .Regidx tiA5, zreg, .CSRRW), dstateM) := by kernel_rfl

/-! #### 21. csrr a5, time -/
/-- Rocq `tigood_21`. -/
theorem tigood21 : goodb0 dM (ext_decode 0xc01027f3#32) dstateM = true := by decide +kernel
/-- Rocq `tidec_21`. -/
theorem tidec21 : exec (ext_decode 0xc01027f3#32) dstateM =
    some (.CSRReg (0xC01#12, zreg, .Regidx tiA5, .CSRRS), dstateM) := by kernel_rfl

/-! #### 22. lui a4, 0xf4 -/
/-- Rocq `tigood_22`. -/
theorem tigood22 : goodb0 dM (ext_decode 0x000f4737#32) dstateM = true := by decide +kernel
/-- Rocq `tidec_22`. -/
theorem tidec22 : exec (ext_decode 0x000f4737#32) dstateM =
    some (.UTYPE (i22, .Regidx tiA4, .LUI), dstateM) := by kernel_rfl

/-! #### 23. addi a4, a4, 576 -/
/-- Rocq `tigood_23`. -/
theorem tigood23 : goodb0 dM (ext_decode 0x24070713#32) dstateM = true := by decide +kernel
/-- Rocq `tidec_23`. -/
theorem tidec23 : exec (ext_decode 0x24070713#32) dstateM =
    some (.ITYPE (i23, .Regidx tiA4, .Regidx tiA4, .ADDI), dstateM) := by kernel_rfl

/-! #### 24. c.add a5, a4 -/
/-- Rocq `tigood_24`. -/
theorem tigood24 : goodb0 dM (ext_decode_compressed 0x97ba#16) dstateM = true := by decide +kernel
/-- Rocq `tidec_24`. -/
theorem tidec24 : exec (ext_decode_compressed 0x97ba#16) dstateM =
    some (.C_ADD (.Regidx tiA5, .Regidx tiA4), dstateM) := by kernel_rfl
/-- Rocq `tilpad_24`. -/
theorem tilpad24 : is_lpad_instruction (.C_ADD (.Regidx tiA5, .Regidx tiA4)) = false := by decide +kernel
/-- Rocq `tigoodexp_24`. -/
theorem tigoodexp24 : ∀ s : ExecSt, goodb0 dNone (execute (.C_ADD (.Regidx tiA5, .Regidx tiA4))) s = true :=
  fun _ => rfl
/-- Rocq `tiexp_24`. -/
theorem tiexp24 : ∀ s : ExecSt,
    exec (execute (.C_ADD (.Regidx tiA5, .Regidx tiA4))) s =
      some (.ExecuteAs (.RTYPE (.Regidx tiA4, .Regidx tiA5, .Regidx tiA5, .ADD)), s) :=
  fun _ => rfl

/-! #### 25. csrw stimecmp, a5 -/
/-- Rocq `tigood_25`. -/
theorem tigood25 : goodb0 dM (ext_decode 0x14d79073#32) dstateM = true := by decide +kernel
/-- Rocq `tidec_25`. -/
theorem tidec25 : exec (ext_decode 0x14d79073#32) dstateM =
    some (.CSRReg (0x14D#12, .Regidx tiA5, zreg, .CSRRW), dstateM) := by kernel_rfl

/-! #### 26. c.ldsp ra, 8(sp) -/
/-- Rocq `tigood_26`. -/
theorem tigood26 : goodb0 dM (ext_decode_compressed 0x60a2#16) dstateM = true := by decide +kernel
/-- Rocq `tidec_26`. -/
theorem tidec26 : exec (ext_decode_compressed 0x60a2#16) dstateM =
    some (.C_LDSP (u10, .Regidx tiRa), dstateM) := by kernel_rfl
/-- Rocq `tilpad_26`. -/
theorem tilpad26 : is_lpad_instruction (.C_LDSP (u10, .Regidx tiRa)) = false := by decide +kernel
/-- Rocq `tigoodexp_26`. -/
theorem tigoodexp26 : ∀ s : ExecSt, goodb0 dNone (execute (.C_LDSP (u10, .Regidx tiRa))) s = true :=
  fun _ => rfl
/-- Rocq `tiexp_26`. -/
theorem tiexp26 : ∀ s : ExecSt,
    exec (execute (.C_LDSP (u10, .Regidx tiRa))) s =
      some (.ExecuteAs (.LOAD (zero_extend (m := 12) (u10 +++ 0b000#3), .Regidx cspRs1, .Regidx tiRa, false, 8)), s) :=
  fun _ => rfl

/-! #### 27. c.ldsp s0, 0(sp) -/
/-- Rocq `tigood_27`. -/
theorem tigood27 : goodb0 dM (ext_decode_compressed 0x6402#16) dstateM = true := by decide +kernel
/-- Rocq `tidec_27`. -/
theorem tidec27 : exec (ext_decode_compressed 0x6402#16) dstateM =
    some (.C_LDSP (u11, .Regidx tiS0), dstateM) := by kernel_rfl
/-- Rocq `tilpad_27`. -/
theorem tilpad27 : is_lpad_instruction (.C_LDSP (u11, .Regidx tiS0)) = false := by decide +kernel
/-- Rocq `tigoodexp_27`. -/
theorem tigoodexp27 : ∀ s : ExecSt, goodb0 dNone (execute (.C_LDSP (u11, .Regidx tiS0))) s = true :=
  fun _ => rfl
/-- Rocq `tiexp_27`. -/
theorem tiexp27 : ∀ s : ExecSt,
    exec (execute (.C_LDSP (u11, .Regidx tiS0))) s =
      some (.ExecuteAs (.LOAD (zero_extend (m := 12) (u11 +++ 0b000#3), .Regidx cspRs1, .Regidx tiS0, false, 8)), s) :=
  fun _ => rfl

/-! #### 28. c.addi sp, 16 -/
/-- Rocq `tigood_28`. -/
theorem tigood28 : goodb0 dM (ext_decode_compressed 0x0141#16) dstateM = true := by decide +kernel
/-- Rocq `tidec_28`. -/
theorem tidec28 : exec (ext_decode_compressed 0x0141#16) dstateM =
    some (.C_ADDI (i28, .Regidx cspRs1), dstateM) := by kernel_rfl
/-- Rocq `tilpad_28`. -/
theorem tilpad28 : is_lpad_instruction (.C_ADDI (i28, .Regidx cspRs1)) = false := by decide +kernel
/-- Rocq `tigoodexp_28`. -/
theorem tigoodexp28 : ∀ s : ExecSt, goodb0 dNone (execute (.C_ADDI (i28, .Regidx cspRs1))) s = true :=
  fun _ => rfl
/-- Rocq `tiexp_28`. -/
theorem tiexp28 : ∀ s : ExecSt,
    exec (execute (.C_ADDI (i28, .Regidx cspRs1))) s =
      some (.ExecuteAs (.ITYPE (sign_extend (m := 12) i28, .Regidx cspRs1, .Regidx cspRs1, .ADDI)), s) :=
  fun _ => rfl

/-! #### 29. c.ret -/
/-- Rocq `tigood_29`. -/
theorem tigood29 : goodb0 dM (ext_decode_compressed 0x8082#16) dstateM = true := by decide +kernel
/-- Rocq `tidec_29`. -/
theorem tidec29 : exec (ext_decode_compressed 0x8082#16) dstateM =
    some (.C_JR (.Regidx tiRa), dstateM) := by kernel_rfl
/-- Rocq `tilpad_29`. -/
theorem tilpad29 : is_lpad_instruction (.C_JR (.Regidx tiRa)) = false := by decide +kernel
/-- Rocq `tigoodexp_29`. -/
theorem tigoodexp29 : ∀ s : ExecSt, goodb0 dNone (execute (.C_JR (.Regidx tiRa))) s = true :=
  fun _ => rfl
/-- Rocq `tiexp_29`. -/
theorem tiexp29 : ∀ s : ExecSt,
    exec (execute (.C_JR (.Regidx tiRa))) s =
      some (.ExecuteAs (.JALR (zeros (n := 12), .Regidx tiRa, zreg)), s) :=
  fun _ => rfl

end dec

/-! ## 3. The per-instruction tokens (`winstrM`) -/

section tokens
variable {GF : BundledGFunctors} [WeakGS GF]

/-- Lean-only (deviation 5): the token of a BASE instruction from its image window, its two
walks and its two reference-state facts. -/
theorem WkTimerinitAux.tokBase (kbs : GMapF PAddr (BitVec 8)) (A : Int) (w : BitVec 32)
    (i : instruction) (hcov : wkbCovers kbs)
    (h2 : is_aligned_vaddr (.Virtaddr (BitVec.ofInt 64 A)) 2 = true)
    (hacc : accWf (BitVec.ofInt 64 A) 4) (hram : inRam (BitVec.ofInt 64 A) 4)
    (hnrvc : isRVC (Sail.BitVec.extractLsb w 15 0) = false)
    (hlpad : is_lpad_instruction i = false)
    (hM : runRead drefM (ext_decode w) = some (i, true))
    (hS : runRead WkEntryNew.drefS0 (ext_decode w) = some (i, true))
    (hgood : goodb0 dM (ext_decode w) dstateM = true)
    (hdec : exec (ext_decode w) dstateM = some (i, dstateM))
    (hkb : ∀ j : Nat, j < 4 → kernelBytes (A + (j : Int)) = some (nthByte (n := 4) w j)) :
    wkernelText (GF := GF) kbs ⊢ winstrM (GF := GF) (BitVec.ofInt 64 A) false i := by
  have href : wdecRef (.F_Base w) i := by unfold wdecRef; exact ⟨hgood, hdec⟩
  have H0 := winstrMOfText (GF := GF) kbs (BitVec.ofInt 64 A) (.F_Base w) w i h2 hacc hram
    ⟨rfl, hnrvc⟩ hlpad (WkEntryNew.decBase w i hM hS) href
  simp only [fetchIsRvc] at H0
  iintro #Ht
  ihave #H := H0 $$ Ht %(wkbWindow kbs A w hcov hkb)
  iexact H

/-- Lean-only (deviation 5): the token of an RVC instruction from its image window, the two
walks of its compressed encoding, its expansion and its four reference-state facts. -/
theorem WkTimerinitAux.tokRvc (kbs : GMapF PAddr (BitVec 8)) (A : Int) (h : BitVec 16)
    (i0 i : instruction) (hcov : wkbCovers kbs)
    (h2 : is_aligned_vaddr (.Virtaddr (BitVec.ofInt 64 A)) 2 = true)
    (hacc : accWf (BitVec.ofInt 64 A) 4) (hram : inRam (BitVec.ofInt 64 A) 4)
    (hsub : Sail.BitVec.extractLsb (kbWordAt A) 15 0 = h) (hrvc : isRVC h = true)
    (hlpad : is_lpad_instruction i = false)
    (hM : runRead drefM (ext_decode_compressed h) = some (i0, true))
    (hS : runRead WkEntryNew.drefS0 (ext_decode_compressed h) = some (i0, true))
    (hl0 : is_lpad_instruction i0 = false)
    (hexp : ∀ s : ExecSt, exec (execute i0) s = some (.ExecuteAs i, s))
    (hgood : goodb0 dM (ext_decode_compressed h) dstateM = true)
    (hdec : exec (ext_decode_compressed h) dstateM = some (i0, dstateM))
    (hgexp : ∀ s : ExecSt, goodb0 dNone (execute i0) s = true)
    (hkb : ∀ j : Nat, j < 4 →
      kernelBytes (A + (j : Int)) = some (nthByte (n := 4) (kbWordAt A) j)) :
    wkernelText (GF := GF) kbs ⊢ winstrM (GF := GF) (BitVec.ofInt 64 A) true i := by
  have href : wdecRef (.F_RVC h) i := by
    unfold wdecRef; exact ⟨hgood, i0, hdec, hl0, hgexp, hexp⟩
  have H0 := winstrMOfText (GF := GF) kbs (BitVec.ofInt 64 A) (.F_RVC h) (kbWordAt A) i h2 hacc
    hram ⟨hsub, hrvc⟩ hlpad (WkEntryNew.decRvc h i0 i hM hS hl0 hexp) href
  simp only [fetchIsRvc] at H0
  iintro #Ht
  ihave #H := H0 $$ Ht %(wkbWindow kbs A (kbWordAt A) hcov hkb)
  iexact H

open WkTimerinitAux

/-- Rocq `wsti_9` (c.addi sp, -16, `timerinit + 0x0`). -/
theorem wsti9 (kbs : GMapF PAddr (BitVec 8)) (hcov : wkbCovers kbs) :
    wkernelText (GF := GF) kbs ⊢
      winstrM (GF := GF) tiPc9 true
        (.ITYPE (sign_extend (m := 12) i9, .Regidx cspRs1, .Regidx cspRs1, .ADDI)) :=
  WkTimerinitAux.tokRvc kbs ((KernelSyms.«timerinit» : Int) + 0x0) 0x1141#16 (.C_ADDI (i9, .Regidx cspRs1)) _ hcov
    (by decide +kernel) (accWfOfLeb _ _ (by decide +kernel)) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    WkTimerinitAux.walk9M WkTimerinitAux.walk9S tilpad9 tiexp9 tigood9 tidec9 tigoodexp9
    tikb9

/-- Rocq `wsti_10` (c.sdsp ra, 8(sp), `timerinit + 0x2`). -/
theorem wsti10 (kbs : GMapF PAddr (BitVec 8)) (hcov : wkbCovers kbs) :
    wkernelText (GF := GF) kbs ⊢
      winstrM (GF := GF) tiPc10 true
        (.STORE (zero_extend (m := 12) (u10 +++ 0b000#3), .Regidx tiRa, .Regidx cspRs1, 8)) :=
  WkTimerinitAux.tokRvc kbs ((KernelSyms.«timerinit» : Int) + 0x2) 0xe406#16 (.C_SDSP (u10, .Regidx tiRa)) _ hcov
    (by decide +kernel) (accWfOfLeb _ _ (by decide +kernel)) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    WkTimerinitAux.walk10M WkTimerinitAux.walk10S tilpad10 tiexp10 tigood10 tidec10 tigoodexp10
    tikb10

/-- Rocq `wsti_11` (c.sdsp s0, 0(sp), `timerinit + 0x4`). -/
theorem wsti11 (kbs : GMapF PAddr (BitVec 8)) (hcov : wkbCovers kbs) :
    wkernelText (GF := GF) kbs ⊢
      winstrM (GF := GF) tiPc11 true
        (.STORE (zero_extend (m := 12) (u11 +++ 0b000#3), .Regidx tiS0, .Regidx cspRs1, 8)) :=
  WkTimerinitAux.tokRvc kbs ((KernelSyms.«timerinit» : Int) + 0x4) 0xe022#16 (.C_SDSP (u11, .Regidx tiS0)) _ hcov
    (by decide +kernel) (accWfOfLeb _ _ (by decide +kernel)) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    WkTimerinitAux.walk11M WkTimerinitAux.walk11S tilpad11 tiexp11 tigood11 tidec11 tigoodexp11
    tikb11

/-- Rocq `wsti_12` (c.addi4spn s0, sp, 16, `timerinit + 0x6`). -/
theorem wsti12 (kbs : GMapF PAddr (BitVec 8)) (hcov : wkbCovers kbs) :
    wkernelText (GF := GF) kbs ⊢
      winstrM (GF := GF) tiPc12 true
        (.ITYPE (caddi4spnImm nz12, .Regidx cspRs1, .Regidx tiS0, .ADDI)) :=
  WkTimerinitAux.tokRvc kbs ((KernelSyms.«timerinit» : Int) + 0x6) 0x0800#16 (.C_ADDI4SPN (.Cregidx 0#3, nz12)) _ hcov
    (by decide +kernel) (accWfOfLeb _ _ (by decide +kernel)) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    WkTimerinitAux.walk12M WkTimerinitAux.walk12S tilpad12 tiexp12 tigood12 tidec12 tigoodexp12
    tikb12

/-- Rocq `wsti_13` (csrr a5, menvcfg, `timerinit + 0x8`). -/
theorem wsti13 (kbs : GMapF PAddr (BitVec 8)) (hcov : wkbCovers kbs) :
    wkernelText (GF := GF) kbs ⊢
      winstrM (GF := GF) tiPc13 false (.CSRReg (0x30A#12, zreg, .Regidx tiA5, .CSRRS)) :=
  WkTimerinitAux.tokBase kbs ((KernelSyms.«timerinit» : Int) + 0x8) 0x30a027f3#32 _ hcov
    (by decide +kernel) (accWfOfLeb _ _ (by decide +kernel)) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    WkTimerinitAux.walk13M WkTimerinitAux.walk13S tigood13 tidec13 tikb13

/-- Rocq `wsti_14` (c.li a4, -1, `timerinit + 0xc`). -/
theorem wsti14 (kbs : GMapF PAddr (BitVec 8)) (hcov : wkbCovers kbs) :
    wkernelText (GF := GF) kbs ⊢
      winstrM (GF := GF) tiPc14 true
        (.ITYPE (sign_extend (m := 12) i14, .Regidx cliRs1, .Regidx tiA4, .ADDI)) :=
  WkTimerinitAux.tokRvc kbs ((KernelSyms.«timerinit» : Int) + 0xc) 0x577d#16 (.C_LI (i14, .Regidx tiA4)) _ hcov
    (by decide +kernel) (accWfOfLeb _ _ (by decide +kernel)) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    WkTimerinitAux.walk14M WkTimerinitAux.walk14S tilpad14 tiexp14 tigood14 tidec14 tigoodexp14
    tikb14

/-- Rocq `wsti_15` (c.slli a4, 63, `timerinit + 0xe`). -/
theorem wsti15 (kbs : GMapF PAddr (BitVec 8)) (hcov : wkbCovers kbs) :
    wkernelText (GF := GF) kbs ⊢
      winstrM (GF := GF) tiPc15 true
        (.SHIFTIOP (sh15, .Regidx tiA4, .Regidx tiA4, .SLLI)) :=
  WkTimerinitAux.tokRvc kbs ((KernelSyms.«timerinit» : Int) + 0xe) 0x177e#16 (.C_SLLI (sh15, .Regidx tiA4)) _ hcov
    (by decide +kernel) (accWfOfLeb _ _ (by decide +kernel)) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    WkTimerinitAux.walk15M WkTimerinitAux.walk15S tilpad15 tiexp15 tigood15 tidec15 tigoodexp15
    tikb15

/-- Rocq `wsti_16` (c.or a5, a4, `timerinit + 0x10`). -/
theorem wsti16 (kbs : GMapF PAddr (BitVec 8)) (hcov : wkbCovers kbs) :
    wkernelText (GF := GF) kbs ⊢
      winstrM (GF := GF) tiPc16 true
        (.RTYPE (.Regidx tiA4, .Regidx tiA5, .Regidx tiA5, .OR)) :=
  WkTimerinitAux.tokRvc kbs ((KernelSyms.«timerinit» : Int) + 0x10) 0x8fd9#16 (.C_OR (.Cregidx 7#3, .Cregidx 6#3)) _ hcov
    (by decide +kernel) (accWfOfLeb _ _ (by decide +kernel)) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    WkTimerinitAux.walk16M WkTimerinitAux.walk16S tilpad16 tiexp16 tigood16 tidec16 tigoodexp16
    tikb16

/-- Rocq `wsti_17` (csrw menvcfg, a5, `timerinit + 0x12`). -/
theorem wsti17 (kbs : GMapF PAddr (BitVec 8)) (hcov : wkbCovers kbs) :
    wkernelText (GF := GF) kbs ⊢
      winstrM (GF := GF) tiPc17 false (.CSRReg (0x30A#12, .Regidx tiA5, zreg, .CSRRW)) :=
  WkTimerinitAux.tokBase kbs ((KernelSyms.«timerinit» : Int) + 0x12) 0x30a79073#32 _ hcov
    (by decide +kernel) (accWfOfLeb _ _ (by decide +kernel)) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    WkTimerinitAux.walk17M WkTimerinitAux.walk17S tigood17 tidec17 tikb17

/-- Rocq `wsti_18` (csrr a5, mcounteren, `timerinit + 0x16`). -/
theorem wsti18 (kbs : GMapF PAddr (BitVec 8)) (hcov : wkbCovers kbs) :
    wkernelText (GF := GF) kbs ⊢
      winstrM (GF := GF) tiPc18 false (.CSRReg (0x306#12, zreg, .Regidx tiA5, .CSRRS)) :=
  WkTimerinitAux.tokBase kbs ((KernelSyms.«timerinit» : Int) + 0x16) 0x306027f3#32 _ hcov
    (by decide +kernel) (accWfOfLeb _ _ (by decide +kernel)) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    WkTimerinitAux.walk18M WkTimerinitAux.walk18S tigood18 tidec18 tikb18

/-- Rocq `wsti_19` (ori a5, a5, 2, `timerinit + 0x1a`). -/
theorem wsti19 (kbs : GMapF PAddr (BitVec 8)) (hcov : wkbCovers kbs) :
    wkernelText (GF := GF) kbs ⊢
      winstrM (GF := GF) tiPc19 false (.ITYPE (i19, .Regidx tiA5, .Regidx tiA5, .ORI)) :=
  WkTimerinitAux.tokBase kbs ((KernelSyms.«timerinit» : Int) + 0x1a) 0x0027e793#32 _ hcov
    (by decide +kernel) (accWfOfLeb _ _ (by decide +kernel)) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    WkTimerinitAux.walk19M WkTimerinitAux.walk19S tigood19 tidec19 tikb19

/-- Rocq `wsti_20` (csrw mcounteren, a5, `timerinit + 0x1e`). -/
theorem wsti20 (kbs : GMapF PAddr (BitVec 8)) (hcov : wkbCovers kbs) :
    wkernelText (GF := GF) kbs ⊢
      winstrM (GF := GF) tiPc20 false (.CSRReg (0x306#12, .Regidx tiA5, zreg, .CSRRW)) :=
  WkTimerinitAux.tokBase kbs ((KernelSyms.«timerinit» : Int) + 0x1e) 0x30679073#32 _ hcov
    (by decide +kernel) (accWfOfLeb _ _ (by decide +kernel)) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    WkTimerinitAux.walk20M WkTimerinitAux.walk20S tigood20 tidec20 tikb20

/-- Rocq `wsti_21` (csrr a5, time, `timerinit + 0x22`). -/
theorem wsti21 (kbs : GMapF PAddr (BitVec 8)) (hcov : wkbCovers kbs) :
    wkernelText (GF := GF) kbs ⊢
      winstrM (GF := GF) tiPc21 false (.CSRReg (0xC01#12, zreg, .Regidx tiA5, .CSRRS)) :=
  WkTimerinitAux.tokBase kbs ((KernelSyms.«timerinit» : Int) + 0x22) 0xc01027f3#32 _ hcov
    (by decide +kernel) (accWfOfLeb _ _ (by decide +kernel)) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    WkTimerinitAux.walk21M WkTimerinitAux.walk21S tigood21 tidec21 tikb21

/-- Rocq `wsti_22` (lui a4, 0xf4, `timerinit + 0x26`). -/
theorem wsti22 (kbs : GMapF PAddr (BitVec 8)) (hcov : wkbCovers kbs) :
    wkernelText (GF := GF) kbs ⊢
      winstrM (GF := GF) tiPc22 false (.UTYPE (i22, .Regidx tiA4, .LUI)) :=
  WkTimerinitAux.tokBase kbs ((KernelSyms.«timerinit» : Int) + 0x26) 0x000f4737#32 _ hcov
    (by decide +kernel) (accWfOfLeb _ _ (by decide +kernel)) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    WkTimerinitAux.walk22M WkTimerinitAux.walk22S tigood22 tidec22 tikb22

/-- Rocq `wsti_23` (addi a4, a4, 576, `timerinit + 0x2a`). -/
theorem wsti23 (kbs : GMapF PAddr (BitVec 8)) (hcov : wkbCovers kbs) :
    wkernelText (GF := GF) kbs ⊢
      winstrM (GF := GF) tiPc23 false (.ITYPE (i23, .Regidx tiA4, .Regidx tiA4, .ADDI)) :=
  WkTimerinitAux.tokBase kbs ((KernelSyms.«timerinit» : Int) + 0x2a) 0x24070713#32 _ hcov
    (by decide +kernel) (accWfOfLeb _ _ (by decide +kernel)) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    WkTimerinitAux.walk23M WkTimerinitAux.walk23S tigood23 tidec23 tikb23

/-- Rocq `wsti_24` (c.add a5, a4, `timerinit + 0x2e`). -/
theorem wsti24 (kbs : GMapF PAddr (BitVec 8)) (hcov : wkbCovers kbs) :
    wkernelText (GF := GF) kbs ⊢
      winstrM (GF := GF) tiPc24 true
        (.RTYPE (.Regidx tiA4, .Regidx tiA5, .Regidx tiA5, .ADD)) :=
  WkTimerinitAux.tokRvc kbs ((KernelSyms.«timerinit» : Int) + 0x2e) 0x97ba#16 (.C_ADD (.Regidx tiA5, .Regidx tiA4)) _ hcov
    (by decide +kernel) (accWfOfLeb _ _ (by decide +kernel)) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    WkTimerinitAux.walk24M WkTimerinitAux.walk24S tilpad24 tiexp24 tigood24 tidec24 tigoodexp24
    tikb24

/-- Rocq `wsti_25` (csrw stimecmp, a5, `timerinit + 0x30`). -/
theorem wsti25 (kbs : GMapF PAddr (BitVec 8)) (hcov : wkbCovers kbs) :
    wkernelText (GF := GF) kbs ⊢
      winstrM (GF := GF) tiPc25 false (.CSRReg (0x14D#12, .Regidx tiA5, zreg, .CSRRW)) :=
  WkTimerinitAux.tokBase kbs ((KernelSyms.«timerinit» : Int) + 0x30) 0x14d79073#32 _ hcov
    (by decide +kernel) (accWfOfLeb _ _ (by decide +kernel)) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    WkTimerinitAux.walk25M WkTimerinitAux.walk25S tigood25 tidec25 tikb25

/-- Rocq `wsti_26` (c.ldsp ra, 8(sp), `timerinit + 0x34`). -/
theorem wsti26 (kbs : GMapF PAddr (BitVec 8)) (hcov : wkbCovers kbs) :
    wkernelText (GF := GF) kbs ⊢
      winstrM (GF := GF) tiPc26 true
        (.LOAD (zero_extend (m := 12) (u10 +++ 0b000#3), .Regidx cspRs1, .Regidx tiRa, false, 8)) :=
  WkTimerinitAux.tokRvc kbs ((KernelSyms.«timerinit» : Int) + 0x34) 0x60a2#16 (.C_LDSP (u10, .Regidx tiRa)) _ hcov
    (by decide +kernel) (accWfOfLeb _ _ (by decide +kernel)) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    WkTimerinitAux.walk26M WkTimerinitAux.walk26S tilpad26 tiexp26 tigood26 tidec26 tigoodexp26
    tikb26

/-- Rocq `wsti_27` (c.ldsp s0, 0(sp), `timerinit + 0x36`). -/
theorem wsti27 (kbs : GMapF PAddr (BitVec 8)) (hcov : wkbCovers kbs) :
    wkernelText (GF := GF) kbs ⊢
      winstrM (GF := GF) tiPc27 true
        (.LOAD (zero_extend (m := 12) (u11 +++ 0b000#3), .Regidx cspRs1, .Regidx tiS0, false, 8)) :=
  WkTimerinitAux.tokRvc kbs ((KernelSyms.«timerinit» : Int) + 0x36) 0x6402#16 (.C_LDSP (u11, .Regidx tiS0)) _ hcov
    (by decide +kernel) (accWfOfLeb _ _ (by decide +kernel)) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    WkTimerinitAux.walk27M WkTimerinitAux.walk27S tilpad27 tiexp27 tigood27 tidec27 tigoodexp27
    tikb27

/-- Rocq `wsti_28` (c.addi sp, 16, `timerinit + 0x38`). -/
theorem wsti28 (kbs : GMapF PAddr (BitVec 8)) (hcov : wkbCovers kbs) :
    wkernelText (GF := GF) kbs ⊢
      winstrM (GF := GF) tiPc28 true
        (.ITYPE (sign_extend (m := 12) i28, .Regidx cspRs1, .Regidx cspRs1, .ADDI)) :=
  WkTimerinitAux.tokRvc kbs ((KernelSyms.«timerinit» : Int) + 0x38) 0x0141#16 (.C_ADDI (i28, .Regidx cspRs1)) _ hcov
    (by decide +kernel) (accWfOfLeb _ _ (by decide +kernel)) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    WkTimerinitAux.walk28M WkTimerinitAux.walk28S tilpad28 tiexp28 tigood28 tidec28 tigoodexp28
    tikb28

/-- Rocq `wsti_29` (c.ret, `timerinit + 0x3a`). -/
theorem wsti29 (kbs : GMapF PAddr (BitVec 8)) (hcov : wkbCovers kbs) :
    wkernelText (GF := GF) kbs ⊢
      winstrM (GF := GF) tiPc29 true
        (.JALR (zeros (n := 12), .Regidx tiRa, zreg)) :=
  WkTimerinitAux.tokRvc kbs ((KernelSyms.«timerinit» : Int) + 0x3a) 0x8082#16 (.C_JR (.Regidx tiRa)) _ hcov
    (by decide +kernel) (accWfOfLeb _ _ (by decide +kernel)) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    WkTimerinitAux.walk29M WkTimerinitAux.walk29S tilpad29 tiexp29 tigood29 tidec29 tigoodexp29
    tikb29

end tokens

end Weak
