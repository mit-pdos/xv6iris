/-
Weak: **the `textOkB` facts of all 27 instructions of the `allocpid` copy that this tree's
kernel INLINES into `allocproc` (`allocproc + 0x38 .. + 0x94`) at their pcs (`pca off`)**, from
`allocpidText` (compressed: `tokC` + the `TokC` facts of AxSpinAp3/Ap4/Ap5; 4-byte:
`AxSpinE7.tokB` + the decodes of AxSpinAp/Ap2/AxSpinE7), and the `rfF` (read-footprint) facts
of the expanded register-only / control instructions (ADDI, AUIPC, ADDIW, ADD via `rf0`; the
three JALs via `AxSpinAp6.rfFJal`, generic in the offset and the link register; the four
branches via `AxSpinAp6.rfFBtype`).

Rocq: `iris/AxSpinAp6.v` @ xxvzwolszwmp (owner ruling Q18: RETARGETED to the inlined code; the
code and the Rocq ↦ inlined mapping are in `Weak/AxSpinAp.lean`'s header, "Design").

## Deviations from Rocq

1. KERNEL INLINING (`AxSpinAp` deviation 1, Q18): the facts are about the 27 instructions
   `ap38` … `ap94` (21 four-byte, 6 compressed) at `pca off = allocproc + off`, not Rocq
   allocpid's 22 (`ap00` … `ap3c`).  Mapping of the declarations:

   | Rocq (allocpid)                                   | Lean (inlined copy)                        |
   |---------------------------------------------------|--------------------------------------------|
   | `atok00/02/04/06/08` (prologue, `tokC`)           | none (no prologue)                         |
   | `atok0a` (`auipc a0`, `dec0e`), `atok0e`, `atok12` (`jal acquire`) | `atok38` (`dec0e`), `atok3c`, `atok40` |
   | `atok16/1a/1e` (`&nextpid`, `c.lw` READ)          | `atok44`, `atok48` (`lw`, READ)            |
   | (no wrap / no scan)                               | `atok4c` `atok50` `atok52` `atok56` `atok5a` `atok5c` `atok60` `atok62` `atok64`, scan `atok6c` `atok70` `atok74` `atok76` `atok7a` `atok7e` |
   | `atok20` (`addiw a4,s1,1`)                        | `atok68` (`addiw a1,a3,1`)                 |
   | `atok24` (`c.sw`, WRITE)                          | `atok82`, `atok86` (`sw`, WRITE)           |
   | (in the caller)                                   | `atok8a` (`c.sw a3,48(s1)`, `p->pid`)      |
   | `atok26` (`dec0e`), `atok2a`, `atok2e` (`jal release`) | `atok8c` (`dec0e`), `atok90`, `atok94` |
   | `atok32/34/36/38/3a/3c` (`c.mv a0,s1`, epilogue, `c.ret`) | none                               |
   | `rfF_ap0a/16/26` (AUIPC)                          | `rfFAp38/44/52/6c/82/8c`                   |
   | `rfF_ap00/08/0e/1a/2a/3a` (ADDI)                  | `rfFAp3c/4c/50/56/70/7a/90`                |
   | `rfF_ap20` (ADDIW)                                | `rfFAp68`                                  |
   | `rfF_ap32` (ADD, `c.mv`)                          | `rfFAp60/62`                               |
   | `rfF_ap12/2e` (JAL via `rfF_jal`)                 | `rfFAp40/94`, NEW `rfFAp5a` (`c.j`)         |
   | (no branches)                                     | NEW `rfFAp5c/64/76/7e` (BTYPE)             |
   | `rfF_ap3c` (`c.ret` = `rfF_ins1e`)                | none                                       |

   The loads/stores (+0x48, +0x74, +0x86, +0x8a) get no execute `rfF`, as Rocq's `c.lw`/`c.sw`
   (data leaves).
2. `rfF_jal` (duplicated name: AxSpinAp6, AxSpinPOx) is `AxSpinAp6.rfFJal` and GENERALISED to
   any link register `rd` (Rocq AxSpinAp6: `rd = ra`; it is AxSpinPOx's statement) because
   `c.j` (+0x5a) is a JAL with `rd = zero`.  The proof is AxSpinHd6c's (`rfFH16`) with
   `cases rd`.
3. NEW (Lean-only, Q18): `AxSpinAp6.rfFBtype` — `rfF` of every BTYPE (two GPR reads, then on
   the taken branch the PC read and `jump_to`), the AxSpinHd6b (`rfFH02`) proof made generic
   in the immediate, the registers and the comparison.
4. 4-byte `tokB` calls take `sfAnnB 32 w = false` (`AxSpinE7` deviation 4; `decide` at the
   literal word); decodes are the kernel-walk `dec*` facts (`AxSpinAp` deviation 4).
   `TokC` facts are passed to `tokC` as its existential premise (`TokC` unfolds to it).
5. Section variables (`σi T satp0`) are explicit arguments; `Htxt` is an explicit hypothesis of
   each `atok*` (Rocq section `Context`); the Rocq `Ltac tkr`/`tkb` are inlined (`tokC`/`tokB`
   applied to the `allocpidText` projection).

**Rocq → Lean name map.**  `atokXX` ↦ `atokXX`, `rfF_apXX` ↦ `rfFApXX` (offsets per deviation
1); `rfF_jal` ↦ `AxSpinAp6.rfFJal` (duplicated name).  Lean-only (file-qualified):
`AxSpinAp6.rfFBtype`.

**Dropped:** Rocq allocpid's `atok00/02/04/06/08/32/34/36/38/3a/3c`, `rfF_ap3c` (code absent
from this kernel, deviation 1).  **Not ported:** the two `Print Assumptions` lines (the lint's
axiom check covers them).
-/
import Weak.AxSpinAp2
import Weak.AxSpinAp3
import Weak.AxSpinAp4
import Weak.AxSpinAp5
import Weak.AxSpinE7c
import Weak.AxSymCtl4

namespace Weak

open MachCSL
open Sail Sail.ConcurrencyInterfaceV1
open Sail.ArchSem (FreeM)
open LeanRV64D LeanRV64D.Functions

/-! # 1. The `textOkB` facts -/

section toks
variable (σi : ExecSt) (T : PTree) (satp0 : BitVec 64)

/-- `allocproc + 0x38`: `auipc a0,0x11`. -/
theorem atok38 (Htxt : allocpidText σi T) : textOkB σi T satp0 (pca 0x38) false ap38 :=
  tokB σi T satp0 _ _ _ Htxt.1 (by decide) rfFDec0e dec0e

/-- `allocproc + 0x3c`: `addi a0,a0,-1706`. -/
theorem atok3c (Htxt : allocpidText σi T) : textOkB σi T satp0 (pca 0x3c) false ap3c :=
  tokB σi T satp0 _ _ _ Htxt.2.1 (by decide) rfFDecA3c decA3c

/-- `allocproc + 0x40`: `jal acquire`. -/
theorem atok40 (Htxt : allocpidText σi T) : textOkB σi T satp0 (pca 0x40) false ap40 :=
  tokB σi T satp0 _ _ _ Htxt.2.2.1 (by decide) rfFDecA40 decA40

/-- `allocproc + 0x44`: `auipc a3,0x8`. -/
theorem atok44 (Htxt : allocpidText σi T) : textOkB σi T satp0 (pca 0x44) false ap44 :=
  tokB σi T satp0 _ _ _ Htxt.2.2.2.1 (by decide) rfFDecA44 decA44

/-- `allocproc + 0x48`: `lw a3,1998(a3) (the nextpid read)`. -/
theorem atok48 (Htxt : allocpidText σi T) : textOkB σi T satp0 (pca 0x48) false ap48 :=
  tokB σi T satp0 _ _ _ Htxt.2.2.2.2.1 (by decide) rfFDecA48 decA48

/-- `allocproc + 0x4c`: `li a6,1000`. -/
theorem atok4c (Htxt : allocpidText σi T) : textOkB σi T satp0 (pca 0x4c) false ap4c :=
  tokB σi T satp0 _ _ _ Htxt.2.2.2.2.2.1 (by decide) rfFDecA4c decA4c

/-- `allocproc + 0x50`: `c.li a0,1` (0x4505). -/
theorem atok50 (Htxt : allocpidText σi T) : textOkB σi T satp0 (pca 0x50) true ap50 :=
  tokC σi T satp0 _ _ _ Htxt.2.2.2.2.2.2.1 tkc50

/-- `allocproc + 0x52`: `auipc a2,0x17`. -/
theorem atok52 (Htxt : allocpidText σi T) : textOkB σi T satp0 (pca 0x52) false ap52 :=
  tokB σi T satp0 _ _ _ Htxt.2.2.2.2.2.2.2.1 (by decide) rfFDecA52 decA52

/-- `allocproc + 0x56`: `addi a2,a2,-1172`. -/
theorem atok56 (Htxt : allocpidText σi T) : textOkB σi T satp0 (pca 0x56) false ap56 :=
  tokB σi T satp0 _ _ _ Htxt.2.2.2.2.2.2.2.2.1 (by decide) rfFDecA56 decA56

/-- `allocproc + 0x5a`: `c.j +8` (0xa021). -/
theorem atok5a (Htxt : allocpidText σi T) : textOkB σi T satp0 (pca 0x5a) true ap5a :=
  tokC σi T satp0 _ _ _ Htxt.2.2.2.2.2.2.2.2.2.1 tkc5a

/-- `allocproc + 0x5c`: `beq a5,a2,+0x26`. -/
theorem atok5c (Htxt : allocpidText σi T) : textOkB σi T satp0 (pca 0x5c) false ap5c :=
  tokB σi T satp0 _ _ _ Htxt.2.2.2.2.2.2.2.2.2.2.1 (by decide) rfFDecA5c decA5c

/-- `allocproc + 0x60`: `c.mv a3,a1` (0x86ae). -/
theorem atok60 (Htxt : allocpidText σi T) : textOkB σi T satp0 (pca 0x60) true ap60 :=
  tokC σi T satp0 _ _ _ Htxt.2.2.2.2.2.2.2.2.2.2.2.1 tkc60

/-- `allocproc + 0x62`: `c.mv a1,a0` (0x85aa). -/
theorem atok62 (Htxt : allocpidText σi T) : textOkB σi T satp0 (pca 0x62) true ap62 :=
  tokC σi T satp0 _ _ _ Htxt.2.2.2.2.2.2.2.2.2.2.2.2.1 tkc62

/-- `allocproc + 0x64`: `beq a3,a6,+8`. -/
theorem atok64 (Htxt : allocpidText σi T) : textOkB σi T satp0 (pca 0x64) false ap64 :=
  tokB σi T satp0 _ _ _ Htxt.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (by decide) rfFDecA64 decA64

/-- `allocproc + 0x68`: `addiw a1,a3,1`. -/
theorem atok68 (Htxt : allocpidText σi T) : textOkB σi T satp0 (pca 0x68) false ap68 :=
  tokB σi T satp0 _ _ _ Htxt.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (by decide) rfFDecA68 decA68

/-- `allocproc + 0x6c`: `auipc a5,0x11`. -/
theorem atok6c (Htxt : allocpidText σi T) : textOkB σi T satp0 (pca 0x6c) false ap6c :=
  tokB σi T satp0 _ _ _ Htxt.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (by decide) rfFDecA6c decA6c

/-- `allocproc + 0x70`: `addi a5,a5,-686`. -/
theorem atok70 (Htxt : allocpidText σi T) : textOkB σi T satp0 (pca 0x70) false ap70 :=
  tokB σi T satp0 _ _ _ Htxt.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (by decide) rfFDecA70 decA70

/-- `allocproc + 0x74`: `c.lw a4,48(a5) (the scan read)` (0x5b98). -/
theorem atok74 (Htxt : allocpidText σi T) : textOkB σi T satp0 (pca 0x74) true ap74 :=
  tokC σi T satp0 _ _ _ Htxt.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 tkc74

/-- `allocproc + 0x76`: `beq a4,a3,-0x1a`. -/
theorem atok76 (Htxt : allocpidText σi T) : textOkB σi T satp0 (pca 0x76) false ap76 :=
  tokB σi T satp0 _ _ _ Htxt.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (by decide) rfFDecA76 decA76

/-- `allocproc + 0x7a`: `addi a5,a5,376`. -/
theorem atok7a (Htxt : allocpidText σi T) : textOkB σi T satp0 (pca 0x7a) false ap7a :=
  tokB σi T satp0 _ _ _ Htxt.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (by decide) rfFDecA7a decA7a

/-- `allocproc + 0x7e`: `bne a5,a2,-0xa`. -/
theorem atok7e (Htxt : allocpidText σi T) : textOkB σi T satp0 (pca 0x7e) false ap7e :=
  tokB σi T satp0 _ _ _ Htxt.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (by decide) rfFDecA7e decA7e

/-- `allocproc + 0x82`: `auipc a5,0x8`. -/
theorem atok82 (Htxt : allocpidText σi T) : textOkB σi T satp0 (pca 0x82) false ap82 :=
  tokB σi T satp0 _ _ _ Htxt.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (by decide) rfFDecA82 decA82

/-- `allocproc + 0x86`: `sw a1,1936(a5) (the nextpid write)`. -/
theorem atok86 (Htxt : allocpidText σi T) : textOkB σi T satp0 (pca 0x86) false ap86 :=
  tokB σi T satp0 _ _ _ Htxt.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (by decide) rfFDecA86 decA86

/-- `allocproc + 0x8a`: `c.sw a3,48(s1) (p->pid)` (0xd894). -/
theorem atok8a (Htxt : allocpidText σi T) : textOkB σi T satp0 (pca 0x8a) true ap8a :=
  tokC σi T satp0 _ _ _ Htxt.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 tkc8a

/-- `allocproc + 0x8c`: `auipc a0,0x11`. -/
theorem atok8c (Htxt : allocpidText σi T) : textOkB σi T satp0 (pca 0x8c) false ap8c :=
  tokB σi T satp0 _ _ _ Htxt.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (by decide) rfFDec0e dec0e

/-- `allocproc + 0x90`: `addi a0,a0,-1790`. -/
theorem atok90 (Htxt : allocpidText σi T) : textOkB σi T satp0 (pca 0x90) false ap90 :=
  tokB σi T satp0 _ _ _ Htxt.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (by decide) rfFDecA90 decA90

/-- `allocproc + 0x94`: `jal release`. -/
theorem atok94 (Htxt : allocpidText σi T) : textOkB σi T satp0 (pca 0x94) false ap94 :=
  tokB σi T satp0 _ _ _ Htxt.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 (by decide) rfFDecA94 decA94

end toks

/-! # 2. The execute footprints -/

/-- Rocq `rfF_jal` (deviation 2: any link register `rd`). -/
theorem AxSpinAp6.rfFJal (imm : BitVec 21) (rd : regidx) : rfF (execute (.JAL (imm, rd))) := by
  cases rd
  show rfF (execute_JAL imm (.Regidx _))
  unfold execute_JAL get_next_pc
  refine rfFBind _ _ (rfFReadReg _ (AxSymEngine2.notPin _ (by decide) (by decide))) (fun _ => ?_)
  refine rfFBind _ _ (rfFReadReg _ (AxSymEngine2.notPin _ (by decide) (by decide))) (fun _ => ?_)
  refine rfFBind _ _ (rfFJumpTo _) (fun r => ?_)
  cases r
  · exact rfFBind0 _ _ (rfFOfRf0 _ (rf0WXBits _ _)) trivial
  all_goals exact trivial

/-- (Lean-only, deviation 3) `rfF` of every BTYPE branch. -/
theorem AxSpinAp6.rfFBtype (imm : BitVec 13) (rs2 rs1 : regidx) (op : bop) :
    rfF (execute (.BTYPE (imm, rs2, rs1, op))) := by
  cases rs1; cases rs2
  show rfF (execute_BTYPE imm (.Regidx _) (.Regidx _) op)
  unfold execute_BTYPE
  refine rfFBind _ _ ?_ (fun taken => ?_)
  · cases op <;>
      exact rfFBind _ _ (rfFOfRf0 _ (rf0RXBits _)) (fun _ =>
        rfFBind _ _ (rfFOfRf0 _ (rf0RXBits _)) (fun _ => trivial))
  · cases taken
    · exact trivial
    · exact rfFBind _ _ (rfFReadReg _ (AxSymEngine2.notPin _ (by decide) (by decide)))
        (fun _ => rfFJumpTo _)

/-- `allocproc + 0x38`: `auipc a0,0x11`. -/
theorem rfFAp38 : rfF (execute ap38) := rfFOfRf0 _ (rf0Auipc _ _)
/-- `allocproc + 0x3c`: `addi a0,a0,-1706`. -/
theorem rfFAp3c : rfF (execute ap3c) := rfFOfRf0 _ (rf0Addi _ _ _)
/-- `allocproc + 0x40`: `jal acquire`. -/
theorem rfFAp40 : rfF (execute ap40) := AxSpinAp6.rfFJal _ _
/-- `allocproc + 0x44`: `auipc a3,0x8`. -/
theorem rfFAp44 : rfF (execute ap44) := rfFOfRf0 _ (rf0Auipc _ _)
/-- `allocproc + 0x4c`: `li a6,1000`. -/
theorem rfFAp4c : rfF (execute ap4c) := rfFOfRf0 _ (rf0Addi _ _ _)
/-- `allocproc + 0x50`: `c.li a0,1`. -/
theorem rfFAp50 : rfF (execute ap50) := rfFOfRf0 _ (rf0Addi _ _ _)
/-- `allocproc + 0x52`: `auipc a2,0x17`. -/
theorem rfFAp52 : rfF (execute ap52) := rfFOfRf0 _ (rf0Auipc _ _)
/-- `allocproc + 0x56`: `addi a2,a2,-1172`. -/
theorem rfFAp56 : rfF (execute ap56) := rfFOfRf0 _ (rf0Addi _ _ _)
/-- `allocproc + 0x5a`: `c.j +8`. -/
theorem rfFAp5a : rfF (execute ap5a) := AxSpinAp6.rfFJal _ _
/-- `allocproc + 0x5c`: `beq a5,a2,+0x26`. -/
theorem rfFAp5c : rfF (execute ap5c) := AxSpinAp6.rfFBtype _ _ _ _
/-- `allocproc + 0x60`: `c.mv a3,a1`. -/
theorem rfFAp60 : rfF (execute ap60) := rfFOfRf0 _ (rf0Add _ _ _)
/-- `allocproc + 0x62`: `c.mv a1,a0`. -/
theorem rfFAp62 : rfF (execute ap62) := rfFOfRf0 _ (rf0Add _ _ _)
/-- `allocproc + 0x64`: `beq a3,a6,+8`. -/
theorem rfFAp64 : rfF (execute ap64) := AxSpinAp6.rfFBtype _ _ _ _
/-- `allocproc + 0x68`: `addiw a1,a3,1`. -/
theorem rfFAp68 : rfF (execute ap68) := rfFOfRf0 _ (rf0Addiw _ _ _)
/-- `allocproc + 0x6c`: `auipc a5,0x11`. -/
theorem rfFAp6c : rfF (execute ap6c) := rfFOfRf0 _ (rf0Auipc _ _)
/-- `allocproc + 0x70`: `addi a5,a5,-686`. -/
theorem rfFAp70 : rfF (execute ap70) := rfFOfRf0 _ (rf0Addi _ _ _)
/-- `allocproc + 0x76`: `beq a4,a3,-0x1a`. -/
theorem rfFAp76 : rfF (execute ap76) := AxSpinAp6.rfFBtype _ _ _ _
/-- `allocproc + 0x7a`: `addi a5,a5,376`. -/
theorem rfFAp7a : rfF (execute ap7a) := rfFOfRf0 _ (rf0Addi _ _ _)
/-- `allocproc + 0x7e`: `bne a5,a2,-0xa`. -/
theorem rfFAp7e : rfF (execute ap7e) := AxSpinAp6.rfFBtype _ _ _ _
/-- `allocproc + 0x82`: `auipc a5,0x8`. -/
theorem rfFAp82 : rfF (execute ap82) := rfFOfRf0 _ (rf0Auipc _ _)
/-- `allocproc + 0x8c`: `auipc a0,0x11`. -/
theorem rfFAp8c : rfF (execute ap8c) := rfFOfRf0 _ (rf0Auipc _ _)
/-- `allocproc + 0x90`: `addi a0,a0,-1790`. -/
theorem rfFAp90 : rfF (execute ap90) := rfFOfRf0 _ (rf0Addi _ _ _)
/-- `allocproc + 0x94`: `jal release`. -/
theorem rfFAp94 : rfF (execute ap94) := AxSpinAp6.rfFJal _ _

end Weak
