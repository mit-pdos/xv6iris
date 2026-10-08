/-
Weak: **PHASE 5, allocpid's OWN code: the INSTRUCTION FACTS of the `allocpid` copy that this
tree's kernel INLINES into `allocproc`** (27 instructions, 96 bytes, `allocproc + 0x38 ..
+ 0x98`) for the positional engine — template `AxSpinE7` (mycpu).

Rocq: `iris/AxSpinAp.v` @ xxvzwolszwmp (owner ruling Q18: RETARGETED to the inlined code).

## Design: Rocq's `allocpid` vs the inlined copy (owner ruling Q18)

This tree's kernel (`Xv6/KernelImage.lean`, xv6-riscv b72cbac1, branch verified) has NO
`allocpid` symbol: gcc inlines it into `allocproc` (0x80001b72), at `allocproc + 0x38 .. + 0x94`
(0x80001baa .. 0x80001c06), and the verified branch's `allocpid` also SCANS `proc[0..NPROC)`
for a pid collision and wraps at 1000.  The disassembly (`textChunk*`; `R` = 2-byte RVC):

```
+0x38  00011517    auipc a0,0x11            a0 = &pid_lock ...
+0x3c  95650513    addi  a0,a0,-1706        ... 0x80012500
+0x40  8a6ff0ef    jal   acquire            (0x80000c58)          ---- critical section ----
+0x44  00008697    auipc a3,0x8
+0x48  7ce6a683    lw    a3,1998(a3)        pid = nextpid  (0x8000a384; THE nextpid READ)
+0x4c  3e800813    li    a6,1000
+0x50  4505      R c.li  a0,1
+0x52  00017617    auipc a2,0x17
+0x56  b6c60613    addi  a2,a2,-1172        a2 = &proc[NPROC] (= &tickslock, 0x80018730)
+0x5a  a021      R c.j   +0x62
+0x5c  02c78363    beq   a5,a2,+0x82        (collision path; a5 < a2 here: never taken)
+0x60  86ae      R c.mv  a3,a1              pid = next
+0x62  85aa      R c.mv  a1,a0              next = 1
+0x64  01068463    beq   a3,a6,+0x6c        pid == 1000 ? keep next = 1
+0x68  0016859b    addiw a1,a3,1            next = pid + 1
+0x6c  00011797    auipc a5,0x11
+0x70  d5278793    addi  a5,a5,-686         q = proc (0x80012930)
+0x74  5b98      R c.lw  a4,48(a5)          q->pid            -- the scan: NPROC = 64 slots,
+0x76  fed703e3    beq   a4,a3,+0x5c        collision -> retry   376 bytes each
+0x7a  17878793    addi  a5,a5,376
+0x7e  fec79be3    bne   a5,a2,+0x74
+0x82  00008797    auipc a5,0x8
+0x86  78b7a823    sw    a1,1936(a5)        nextpid = next (THE nextpid WRITE)
+0x8a  d894      R c.sw  a3,48(s1)          p->pid = pid   (INSIDE the critical section)
+0x8c  00011517    auipc a0,0x11
+0x90  90250513    addi  a0,a0,-1790        a0 = &pid_lock
+0x94  8daff0ef    jal   release            (0x80000ce0)          ---- end ----
```

Rocq's `allocpid` (0x800019de, 22 instructions) ↦ the inlined copy:

| Rocq `allocpid`                                   | inlined (`allocproc +`)                 |
|---------------------------------------------------|-----------------------------------------|
| +0x00..+0x08 prologue (`c.addi sp,-32`, 3 `c.sdsp`, `c.addi4spn s0`) | NONE (allocproc's own frame `sp - 32` serves acquire/release) |
| +0x0a/+0x0e `auipc/addi a0 = &pid_lock`           | +0x38/+0x3c (+0x38 is `W0e`, as Rocq +0x0a) |
| +0x12 `jal acquire`                               | +0x40                                    |
| +0x16/+0x1a `auipc/addi a5 = &nextpid`, +0x1e `c.lw s1,0(a5)` (THE READ) | +0x44 `auipc a3` / +0x48 `lw a3,1998(a3)` (THE READ, address folded into the load) |
| (none: no wrap)                                   | +0x4c `li a6,1000`, +0x50 `c.li a0,1`, +0x62/+0x64 wrap at 1000 |
| +0x20 `addiw a4,s1,1`                             | +0x68 `addiw a1,a3,1` (skipped when pid = 1000) |
| (none: no collision scan)                         | +0x52/+0x56 `a2 = &proc[NPROC]`, +0x5a `c.j`, +0x6c..+0x7e the scan over `proc[i].pid` (64 × `c.lw; beq; addi; bne`), +0x5c/+0x60 the retry |
| +0x24 `c.sw a4,0(a5)` (THE WRITE)                 | +0x82 `auipc a5` / +0x86 `sw a1,1936(a5)` (THE WRITE) |
| (in the caller, after release: `p->pid = allocpid()`) | +0x8a `c.sw a3,48(s1)` — `p->pid`, a store to the caller's slot, INSIDE the critical section |
| +0x26/+0x2a `auipc/addi a0 = &pid_lock`           | +0x8c/+0x90 (+0x8c is `W0e`, as Rocq +0x26) |
| +0x2e `jal release`                               | +0x94                                    |
| +0x32 `c.mv a0,s1` (return pid), +0x34..+0x3c epilogue + `c.ret` | NONE (pid stays in `a3`; allocproc continues at +0x98) |

So the critical section is still ONE nextpid read and ONE nextpid write between the acquire and
the release, but in between it now runs the collision scan (64·k reads of `proc[i].pid`, k ≥ 1
rounds, each a plain 4-byte load) and, before the release, the `p->pid` store.  On the
normal path (pid ≠ 1000, no collision) the copy executes +0x38 .. +0x5a, +0x62 .. +0x7e
(64 times the scan body), +0x82 .. +0x94 (`AxSpinSpike.allocpidTr`).

## This file

§1 `allocpidText σi T`: the 27 words are text at their pcs `pca off = allocproc + off`
   (`textAtS` for the six compressed ones, `textAt4S` for the 21 4-byte ones) — a fact about the
   IMAGE and the page table, like `mycpuText`.  Lean-only `AxSpinAp.apCode` lists the copy as
   (offset, width, encoding) over the very constants `allocpidText` uses, and
   `AxSpinAp.apCodeImg`/`apCodeContig` check it against THIS tree's kernel text
   (`Xv6.Kernel.textTree`, from `Xv6/KernelImage.lean`) and that it is contiguous from +0x38 to
   +0x98.
§2 the expanded instructions `ap38` … `ap94` (named by their `allocproc` offset).  The two
   `auipc a0,0x11` (+0x38, +0x8c) have the SAME word as mycpu's +0x0e (`W0e`); their decode is
   `dec0e` (`ap38Ins0e`, `ap8cIns0e`).
§3 `TokC h ins`: the pc-INDEPENDENT half of a compressed instruction's `textOkB` (decode +
   expansion footprints, `tokR`'s last four premises) and `tokC` (text + `TokC` ⇒ `textOkB`);
   the `TokC` facts of the six halfwords are in AxSpinAp3/Ap4/Ap5, nine 4-byte decodes here
   (+0x3c .. +0x64), ten in AxSpinAp2 (+0x68 .. +0x94).

## Deviations from Rocq

1. KERNEL INLINING (owner ruling Q18, above): the file states the facts of the inlined copy
   `allocproc + 0x38 .. + 0x94`, not of Rocq's 22-instruction `allocpid`.  `pca off` is
   `allocproc + off` (Rocq `allocpid + off`); the words, instructions and decodes are the
   copy's (27 instructions: 21 4-byte, 6 compressed; Rocq 9 + 13).  Rocq's `WA0e` … `WA2e`,
   `ap00` … `ap3c`, `ap0a_ins0e`, `ap26_ins0e`, `decA0e`/`A16`/`A1a` (and their `rfF`) have no
   counterpart (different code) and are REPLACED by `WA3c` … `WA56`/`WA5c`/`WA64`, `ap38` …
   `ap94`, `ap38Ins0e`, `ap8cIns0e`, `decA3c` … `decA64` (+ `rfFDecA*`).  Lean-only
   `AxSpinAp.apCode`/`apCodeImg`/`apCodeContig` tie the words to the Lean kernel image.
2. TYPES / SPELLING as `AxSpinE7` deviation 2 (`mword_of_int k : mword n` ↦ `k#n`, `text_at_S`
   ↦ `textAtS`, `sign_extend' 12` ↦ `sign_extend (m := 12)`, `hw` ↦ `AxSpinE7.hw`).  The `WA*`
   constants are `BitVec 32` (Rocq `Z`, used only as `mword_of_int W : mword 32`).
3. `TokC`'s decode premise is at the states with `misa = misaC` (Rocq: misa C bit set), as
   `AxSpinE7.tokR` (its deviation 3); `tokC` is then `tokR`.
4. DECODE PROOFS (as `AxSpinE7` deviation 5): no KernelDecode* lemmas; `decA*` are kernel walks
   of the decoder on the machine and supervisor reference maps (`AxSpinAp.walkA*M/S`) combined
   by `WkEntryNew.execAnyCfg` — they also CONFIRM each instruction AST against its word; the
   `rfF` facts are `rff_auto` after pruning the decoder's pattern tests on the literal.
5. Section variables (`σi T satp0`) are explicit arguments.

**Rocq → Lean name map.**  `pca` `pca`, `allocpid_text` `allocpidText`, `tokC` `tokC`, `TokC`
`TokC` (same role, retargeted); words / instructions / decodes: see deviation 1 (none in the
duplicated-name table).  Lean-only (file-qualified): `AxSpinAp.apCode`, `AxSpinAp.apCodeImg`,
`AxSpinAp.apCodeContig`, `AxSpinAp.walkA*M/S` (9 × 2).

**Dropped:** Rocq's allocpid-specific words/instructions/decodes (deviation 1: the code does
not exist in this kernel).  **Not ported:** the `Print Assumptions` lines (the lint's axiom
check covers them).
-/
import Weak.AxSpinE7
import Xv6.KernelTree

namespace Weak

open MachCSL
open Sail Sail.ConcurrencyInterfaceV1
open Sail.ArchSem (FreeM)
open LeanRV64D LeanRV64D.Functions

/-- Rocq `pca` (deviation 1): the address `allocproc + off` (the inlined allocpid copy is
`allocproc + 0x38 .. + 0x98`). -/
def pca (off : Int) : BitVec 64 := BitVec.ofInt 64 ((KernelSyms.«allocproc» : Int) + off)

/-! The 4-byte words other than `auipc a0,0x11` (`W0e`, at + 0x38 and + 0x8c). -/

/-- + 0x3c: `addi a0,a0,-1706` (a0 = &pid_lock). -/
def WA3c : BitVec 32 := 0x95650513#32
/-- + 0x40: `jal acquire`. -/
def WA40 : BitVec 32 := 0x8a6ff0ef#32
/-- + 0x44: `auipc a3,0x8`. -/
def WA44 : BitVec 32 := 0x00008697#32
/-- + 0x48: `lw a3,1998(a3)` (the nextpid read). -/
def WA48 : BitVec 32 := 0x7ce6a683#32
/-- + 0x4c: `li a6,1000`. -/
def WA4c : BitVec 32 := 0x3e800813#32
/-- + 0x52: `auipc a2,0x17`. -/
def WA52 : BitVec 32 := 0x00017617#32
/-- + 0x56: `addi a2,a2,-1172` (a2 = &proc[NPROC]). -/
def WA56 : BitVec 32 := 0xb6c60613#32
/-- + 0x5c: `beq a5,a2,+0x26` (to + 0x82). -/
def WA5c : BitVec 32 := 0x02c78363#32
/-- + 0x64: `beq a3,a6,+8` (to + 0x6c). -/
def WA64 : BitVec 32 := 0x01068463#32
/-- + 0x68: `addiw a1,a3,1`. -/
def WA68 : BitVec 32 := 0x0016859b#32
/-- + 0x6c: `auipc a5,0x11`. -/
def WA6c : BitVec 32 := 0x00011797#32
/-- + 0x70: `addi a5,a5,-686` (a5 = proc). -/
def WA70 : BitVec 32 := 0xd5278793#32
/-- + 0x76: `beq a4,a3,-0x1a` (to + 0x5c). -/
def WA76 : BitVec 32 := 0xfed703e3#32
/-- + 0x7a: `addi a5,a5,376`. -/
def WA7a : BitVec 32 := 0x17878793#32
/-- + 0x7e: `bne a5,a2,-0xa` (to + 0x74). -/
def WA7e : BitVec 32 := 0xfec79be3#32
/-- + 0x82: `auipc a5,0x8`. -/
def WA82 : BitVec 32 := 0x00008797#32
/-- + 0x86: `sw a1,1936(a5)` (the nextpid write). -/
def WA86 : BitVec 32 := 0x78b7a823#32
/-- + 0x90: `addi a0,a0,-1790` (a0 = &pid_lock). -/
def WA90 : BitVec 32 := 0x90250513#32
/-- + 0x94: `jal release`. -/
def WA94 : BitVec 32 := 0x8daff0ef#32

/-! # 2. The expanded instructions (named by their `allocproc` offset) -/

/-- + 0x38: `auipc a0,0x11`. -/
def ap38 : instruction := .UTYPE (17#20, .Regidx 10#5, .AUIPC)
/-- + 0x3c: `addi a0,a0,-1706`. -/
def ap3c : instruction := .ITYPE (0x956#12, .Regidx 10#5, .Regidx 10#5, .ADDI)
/-- + 0x40: `jal acquire` (offset -3930). -/
def ap40 : instruction := .JAL (2093222#21, .Regidx 1#5)
/-- + 0x44: `auipc a3,0x8`. -/
def ap44 : instruction := .UTYPE (8#20, .Regidx 13#5, .AUIPC)
/-- + 0x48: `lw a3,1998(a3)`. -/
def ap48 : instruction := .LOAD (1998#12, .Regidx 13#5, .Regidx 13#5, false, 4)
/-- + 0x4c: `li a6,1000` (`addi a6,zero,1000`). -/
def ap4c : instruction := .ITYPE (1000#12, .Regidx 0#5, .Regidx 16#5, .ADDI)
/-- + 0x50: `c.li a0,1`. -/
def ap50 : instruction := .ITYPE (sign_extend (m := 12) (1#6), zreg, .Regidx 10#5, .ADDI)
/-- + 0x52: `auipc a2,0x17`. -/
def ap52 : instruction := .UTYPE (0x17#20, .Regidx 12#5, .AUIPC)
/-- + 0x56: `addi a2,a2,-1172`. -/
def ap56 : instruction := .ITYPE (0xb6c#12, .Regidx 12#5, .Regidx 12#5, .ADDI)
/-- + 0x5a: `c.j +8` (to + 0x62). -/
def ap5a : instruction := .JAL (sign_extend (m := 21) (4#11 +++ 0#1), zreg)
/-- + 0x5c: `beq a5,a2,+0x26`. -/
def ap5c : instruction := .BTYPE (0x26#13, .Regidx 12#5, .Regidx 15#5, .BEQ)
/-- + 0x60: `c.mv a3,a1`. -/
def ap60 : instruction := .RTYPE (.Regidx 11#5, zreg, .Regidx 13#5, .ADD)
/-- + 0x62: `c.mv a1,a0`. -/
def ap62 : instruction := .RTYPE (.Regidx 10#5, zreg, .Regidx 11#5, .ADD)
/-- + 0x64: `beq a3,a6,+8`. -/
def ap64 : instruction := .BTYPE (8#13, .Regidx 16#5, .Regidx 13#5, .BEQ)
/-- + 0x68: `addiw a1,a3,1`. -/
def ap68 : instruction := .ADDIW (1#12, .Regidx 13#5, .Regidx 11#5)
/-- + 0x6c: `auipc a5,0x11`. -/
def ap6c : instruction := .UTYPE (17#20, .Regidx 15#5, .AUIPC)
/-- + 0x70: `addi a5,a5,-686`. -/
def ap70 : instruction := .ITYPE (0xd52#12, .Regidx 15#5, .Regidx 15#5, .ADDI)
/-- + 0x74: `c.lw a4,48(a5)`. -/
def ap74 : instruction := .LOAD (48#12, .Regidx 15#5, .Regidx 14#5, false, 4)
/-- + 0x76: `beq a4,a3,-0x1a`. -/
def ap76 : instruction := .BTYPE (8166#13, .Regidx 13#5, .Regidx 14#5, .BEQ)
/-- + 0x7a: `addi a5,a5,376`. -/
def ap7a : instruction := .ITYPE (376#12, .Regidx 15#5, .Regidx 15#5, .ADDI)
/-- + 0x7e: `bne a5,a2,-0xa`. -/
def ap7e : instruction := .BTYPE (8182#13, .Regidx 12#5, .Regidx 15#5, .BNE)
/-- + 0x82: `auipc a5,0x8`. -/
def ap82 : instruction := .UTYPE (8#20, .Regidx 15#5, .AUIPC)
/-- + 0x86: `sw a1,1936(a5)`. -/
def ap86 : instruction := .STORE (1936#12, .Regidx 11#5, .Regidx 15#5, 4)
/-- + 0x8a: `c.sw a3,48(s1)` (`p->pid = pid`). -/
def ap8a : instruction := .STORE (48#12, .Regidx 13#5, .Regidx 9#5, 4)
/-- + 0x8c: `auipc a0,0x11`. -/
def ap8c : instruction := .UTYPE (17#20, .Regidx 10#5, .AUIPC)
/-- + 0x90: `addi a0,a0,-1790`. -/
def ap90 : instruction := .ITYPE (0x902#12, .Regidx 10#5, .Regidx 10#5, .ADDI)
/-- + 0x94: `jal release` (offset -3878). -/
def ap94 : instruction := .JAL (2093274#21, .Regidx 1#5)

/-- Rocq `ap0a_ins0e` (deviation 1: + 0x38). -/
theorem ap38Ins0e : ap38 = ins0e := rfl
/-- Rocq `ap26_ins0e` (deviation 1: + 0x8c). -/
theorem ap8cIns0e : ap8c = ins0e := rfl

/-! # 1. The text -/

/-- (Lean-only, deviation 1) the inlined allocpid copy as (offset from `allocproc`, width,
encoding), over the constants `allocpidText` states. -/
def AxSpinAp.apCode : List (Nat × Nat × Nat) :=
  [(0x38, 4, W0e.toNat), (0x3c, 4, WA3c.toNat), (0x40, 4, WA40.toNat), (0x44, 4, WA44.toNat),
   (0x48, 4, WA48.toNat), (0x4c, 4, WA4c.toNat), (0x50, 2, (AxSpinE7.hw 0x4505).toNat),
   (0x52, 4, WA52.toNat), (0x56, 4, WA56.toNat), (0x5a, 2, (AxSpinE7.hw 0xa021).toNat),
   (0x5c, 4, WA5c.toNat), (0x60, 2, (AxSpinE7.hw 0x86ae).toNat),
   (0x62, 2, (AxSpinE7.hw 0x85aa).toNat), (0x64, 4, WA64.toNat), (0x68, 4, WA68.toNat),
   (0x6c, 4, WA6c.toNat), (0x70, 4, WA70.toNat), (0x74, 2, (AxSpinE7.hw 0x5b98).toNat),
   (0x76, 4, WA76.toNat), (0x7a, 4, WA7a.toNat), (0x7e, 4, WA7e.toNat), (0x82, 4, WA82.toNat),
   (0x86, 4, WA86.toNat), (0x8a, 2, (AxSpinE7.hw 0xd894).toNat), (0x8c, 4, W0e.toNat),
   (0x90, 4, WA90.toNat), (0x94, 4, WA94.toNat)]

/-- (Lean-only, deviation 1) THE IMAGE CHECK: every entry of `AxSpinAp.apCode` is the
instruction of this tree's kernel text (`Xv6/KernelImage.lean`) at `allocproc + off`, with that
width and encoding. -/
theorem AxSpinAp.apCodeImg :
    AxSpinAp.apCode.all (fun c =>
      match Xv6.Kernel.textTree.find? (KernelSyms.«allocproc» + c.1) with
      | some k => Nat.beq k.width c.2.1 && Nat.beq k.enc c.2.2
      | none => false) = true := by
  decide +kernel

/-- (Lean-only, deviation 1) the copy is contiguous from `allocproc + 0x38` to `+ 0x98`
(27 instructions, no gap). -/
theorem AxSpinAp.apCodeContig :
    AxSpinAp.apCode.length = 27 ∧ AxSpinAp.apCode.head?.map (·.1) = some 0x38 ∧
    ((AxSpinAp.apCode.zip AxSpinAp.apCode.tail).all fun p => Nat.beq (p.1.1 + p.1.2.1) p.2.1) = true ∧
    AxSpinAp.apCode.getLast?.map (fun c => c.1 + c.2.1) = some 0x98 := by
  decide +kernel

section afacts
variable (σi : ExecSt) (T : PTree) (satp0 : BitVec 64)

/-- Rocq `allocpid_text` (deviation 1: the inlined copy at `allocproc + 0x38 .. + 0x98`). -/
def allocpidText : Prop :=
  textAt4S σi T (pca 0x38) W0e ∧ textAt4S σi T (pca 0x3c) WA3c ∧
  textAt4S σi T (pca 0x40) WA40 ∧ textAt4S σi T (pca 0x44) WA44 ∧
  textAt4S σi T (pca 0x48) WA48 ∧ textAt4S σi T (pca 0x4c) WA4c ∧
  textAtS σi T (pca 0x50) (AxSpinE7.hw 0x4505) ∧
  textAt4S σi T (pca 0x52) WA52 ∧ textAt4S σi T (pca 0x56) WA56 ∧
  textAtS σi T (pca 0x5a) (AxSpinE7.hw 0xa021) ∧
  textAt4S σi T (pca 0x5c) WA5c ∧
  textAtS σi T (pca 0x60) (AxSpinE7.hw 0x86ae) ∧ textAtS σi T (pca 0x62) (AxSpinE7.hw 0x85aa) ∧
  textAt4S σi T (pca 0x64) WA64 ∧ textAt4S σi T (pca 0x68) WA68 ∧
  textAt4S σi T (pca 0x6c) WA6c ∧ textAt4S σi T (pca 0x70) WA70 ∧
  textAtS σi T (pca 0x74) (AxSpinE7.hw 0x5b98) ∧
  textAt4S σi T (pca 0x76) WA76 ∧ textAt4S σi T (pca 0x7a) WA7a ∧
  textAt4S σi T (pca 0x7e) WA7e ∧ textAt4S σi T (pca 0x82) WA82 ∧
  textAt4S σi T (pca 0x86) WA86 ∧
  textAtS σi T (pca 0x8a) (AxSpinE7.hw 0xd894) ∧
  textAt4S σi T (pca 0x8c) W0e ∧ textAt4S σi T (pca 0x90) WA90 ∧
  textAt4S σi T (pca 0x94) WA94

/-! # 3. The pc-independent half of a compressed `textOkB` -/

/-- Rocq `tokC` (deviation 3: the decode premise at the `misa = misaC` states). -/
theorem tokC (pc : BitVec 64) (h : BitVec 16) (ins : instruction) :
    textAtS σi T pc h →
    (∃ i0, rfF (ext_decode_compressed h) ∧
      (∀ s : ExecSt, s.regs .misa = misaC → exec (ext_decode_compressed h) s = some (i0, s)) ∧
      rfF (execute i0) ∧ (∀ s : ExecSt, exec (execute i0) s = some (.ExecuteAs ins, s))) →
    textOkB σi T satp0 pc true ins := by
  intro Hat ⟨i0, H1, H2, H3, H4⟩
  exact tokR σi T satp0 pc h i0 ins Hat H1 H2 H3 H4

end afacts

/-- Rocq `TokC` (deviation 3). -/
def TokC (h : BitVec 16) (ins : instruction) : Prop :=
  ∃ i0, rfF (ext_decode_compressed h) ∧
    (∀ s : ExecSt, s.regs .misa = misaC → exec (ext_decode_compressed h) s = some (i0, s)) ∧
    rfF (execute i0) ∧ (∀ s : ExecSt, exec (execute i0) s = some (.ExecuteAs ins, s))

/-! # 3'. Nine of the 4-byte decodes (+ 0x3c .. + 0x64) -/

/-- `rfF` of a 4-byte decode at a word constant (file-local). -/
local macro "ax_spin_ap_rffdec" w:ident : tactic =>
  `(tactic| (
    unfold $w ext_decode encdec_backwards
    simp (config := { decide := true }) only [↓reduceIte]
    rff_auto))

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- `rfF` of the decode of `WA3c`. -/
theorem rfFDecA3c : rfF (ext_decode WA3c) := by ax_spin_ap_rffdec WA3c
set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- `rfF` of the decode of `WA40`. -/
theorem rfFDecA40 : rfF (ext_decode WA40) := by ax_spin_ap_rffdec WA40
set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- `rfF` of the decode of `WA44`. -/
theorem rfFDecA44 : rfF (ext_decode WA44) := by ax_spin_ap_rffdec WA44
set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- `rfF` of the decode of `WA48`. -/
theorem rfFDecA48 : rfF (ext_decode WA48) := by ax_spin_ap_rffdec WA48
set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- `rfF` of the decode of `WA4c`. -/
theorem rfFDecA4c : rfF (ext_decode WA4c) := by ax_spin_ap_rffdec WA4c
set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- `rfF` of the decode of `WA52`. -/
theorem rfFDecA52 : rfF (ext_decode WA52) := by ax_spin_ap_rffdec WA52
set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- `rfF` of the decode of `WA56`. -/
theorem rfFDecA56 : rfF (ext_decode WA56) := by ax_spin_ap_rffdec WA56
set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- `rfF` of the decode of `WA5c`. -/
theorem rfFDecA5c : rfF (ext_decode WA5c) := by ax_spin_ap_rffdec WA5c
set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- `rfF` of the decode of `WA64`. -/
theorem rfFDecA64 : rfF (ext_decode WA64) := by ax_spin_ap_rffdec WA64

section walks
attribute [local semireducible] LeanRV64D.Functions.hartSupports
  LeanRV64D.Functions.currentlyEnabled

/-- (Lean-only, deviation 4) decode walk of `WA3c`, machine reference map. -/
theorem AxSpinAp.walkA3cM : runRead drefM (ext_decode WA3c) = some (ap3c, true) := by kernel_rfl
/-- (Lean-only, deviation 4) decode walk of `WA3c`, supervisor reference map. -/
theorem AxSpinAp.walkA3cS : runRead WkEntryNew.drefS0 (ext_decode WA3c) = some (ap3c, true) := by
  kernel_rfl
/-- (Lean-only, deviation 4) decode walk of `WA40`, machine reference map. -/
theorem AxSpinAp.walkA40M : runRead drefM (ext_decode WA40) = some (ap40, true) := by kernel_rfl
/-- (Lean-only, deviation 4) decode walk of `WA40`, supervisor reference map. -/
theorem AxSpinAp.walkA40S : runRead WkEntryNew.drefS0 (ext_decode WA40) = some (ap40, true) := by
  kernel_rfl
/-- (Lean-only, deviation 4) decode walk of `WA44`, machine reference map. -/
theorem AxSpinAp.walkA44M : runRead drefM (ext_decode WA44) = some (ap44, true) := by kernel_rfl
/-- (Lean-only, deviation 4) decode walk of `WA44`, supervisor reference map. -/
theorem AxSpinAp.walkA44S : runRead WkEntryNew.drefS0 (ext_decode WA44) = some (ap44, true) := by
  kernel_rfl
/-- (Lean-only, deviation 4) decode walk of `WA48`, machine reference map. -/
theorem AxSpinAp.walkA48M : runRead drefM (ext_decode WA48) = some (ap48, true) := by kernel_rfl
/-- (Lean-only, deviation 4) decode walk of `WA48`, supervisor reference map. -/
theorem AxSpinAp.walkA48S : runRead WkEntryNew.drefS0 (ext_decode WA48) = some (ap48, true) := by
  kernel_rfl
/-- (Lean-only, deviation 4) decode walk of `WA4c`, machine reference map. -/
theorem AxSpinAp.walkA4cM : runRead drefM (ext_decode WA4c) = some (ap4c, true) := by kernel_rfl
/-- (Lean-only, deviation 4) decode walk of `WA4c`, supervisor reference map. -/
theorem AxSpinAp.walkA4cS : runRead WkEntryNew.drefS0 (ext_decode WA4c) = some (ap4c, true) := by
  kernel_rfl
/-- (Lean-only, deviation 4) decode walk of `WA52`, machine reference map. -/
theorem AxSpinAp.walkA52M : runRead drefM (ext_decode WA52) = some (ap52, true) := by kernel_rfl
/-- (Lean-only, deviation 4) decode walk of `WA52`, supervisor reference map. -/
theorem AxSpinAp.walkA52S : runRead WkEntryNew.drefS0 (ext_decode WA52) = some (ap52, true) := by
  kernel_rfl
/-- (Lean-only, deviation 4) decode walk of `WA56`, machine reference map. -/
theorem AxSpinAp.walkA56M : runRead drefM (ext_decode WA56) = some (ap56, true) := by kernel_rfl
/-- (Lean-only, deviation 4) decode walk of `WA56`, supervisor reference map. -/
theorem AxSpinAp.walkA56S : runRead WkEntryNew.drefS0 (ext_decode WA56) = some (ap56, true) := by
  kernel_rfl
/-- (Lean-only, deviation 4) decode walk of `WA5c`, machine reference map. -/
theorem AxSpinAp.walkA5cM : runRead drefM (ext_decode WA5c) = some (ap5c, true) := by kernel_rfl
/-- (Lean-only, deviation 4) decode walk of `WA5c`, supervisor reference map. -/
theorem AxSpinAp.walkA5cS : runRead WkEntryNew.drefS0 (ext_decode WA5c) = some (ap5c, true) := by
  kernel_rfl
/-- (Lean-only, deviation 4) decode walk of `WA64`, machine reference map. -/
theorem AxSpinAp.walkA64M : runRead drefM (ext_decode WA64) = some (ap64, true) := by kernel_rfl
/-- (Lean-only, deviation 4) decode walk of `WA64`, supervisor reference map. -/
theorem AxSpinAp.walkA64S : runRead WkEntryNew.drefS0 (ext_decode WA64) = some (ap64, true) := by
  kernel_rfl

end walks

/-- The decode of `WA3c` (deviation 4). -/
theorem decA3c (s : ExecSt) : s.regs .misa = misaC → cfgOk s →
    exec (ext_decode WA3c) s = some (ap3c, s) :=
  WkEntryNew.execAnyCfg _ _ AxSpinAp.walkA3cM AxSpinAp.walkA3cS s
/-- The decode of `WA40` (deviation 4). -/
theorem decA40 (s : ExecSt) : s.regs .misa = misaC → cfgOk s →
    exec (ext_decode WA40) s = some (ap40, s) :=
  WkEntryNew.execAnyCfg _ _ AxSpinAp.walkA40M AxSpinAp.walkA40S s
/-- The decode of `WA44` (deviation 4). -/
theorem decA44 (s : ExecSt) : s.regs .misa = misaC → cfgOk s →
    exec (ext_decode WA44) s = some (ap44, s) :=
  WkEntryNew.execAnyCfg _ _ AxSpinAp.walkA44M AxSpinAp.walkA44S s
/-- The decode of `WA48` (deviation 4). -/
theorem decA48 (s : ExecSt) : s.regs .misa = misaC → cfgOk s →
    exec (ext_decode WA48) s = some (ap48, s) :=
  WkEntryNew.execAnyCfg _ _ AxSpinAp.walkA48M AxSpinAp.walkA48S s
/-- The decode of `WA4c` (deviation 4). -/
theorem decA4c (s : ExecSt) : s.regs .misa = misaC → cfgOk s →
    exec (ext_decode WA4c) s = some (ap4c, s) :=
  WkEntryNew.execAnyCfg _ _ AxSpinAp.walkA4cM AxSpinAp.walkA4cS s
/-- The decode of `WA52` (deviation 4). -/
theorem decA52 (s : ExecSt) : s.regs .misa = misaC → cfgOk s →
    exec (ext_decode WA52) s = some (ap52, s) :=
  WkEntryNew.execAnyCfg _ _ AxSpinAp.walkA52M AxSpinAp.walkA52S s
/-- The decode of `WA56` (deviation 4). -/
theorem decA56 (s : ExecSt) : s.regs .misa = misaC → cfgOk s →
    exec (ext_decode WA56) s = some (ap56, s) :=
  WkEntryNew.execAnyCfg _ _ AxSpinAp.walkA56M AxSpinAp.walkA56S s
/-- The decode of `WA5c` (deviation 4). -/
theorem decA5c (s : ExecSt) : s.regs .misa = misaC → cfgOk s →
    exec (ext_decode WA5c) s = some (ap5c, s) :=
  WkEntryNew.execAnyCfg _ _ AxSpinAp.walkA5cM AxSpinAp.walkA5cS s
/-- The decode of `WA64` (deviation 4). -/
theorem decA64 (s : ExecSt) : s.regs .misa = misaC → cfgOk s →
    exec (ext_decode WA64) s = some (ap64, s) :=
  WkEntryNew.execAnyCfg _ _ AxSpinAp.walkA64M AxSpinAp.walkA64S s

end Weak
