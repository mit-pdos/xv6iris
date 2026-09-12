/-
Specification of `mycpu` (kernel/proc.c): `&cpus[cpuid()]`.

INTERRUPTS MUST BE DISABLED (see `SpecCpuid`): the contract is stated at
`sie = false` and needs no `wpNext`.  The result is the `KernelGeom`
address of this hart's `struct cpu` (Rocq `mycpu_ret (rget m tp)`, the
code's `auipc/addi/add` chain spelled as the address it denotes).
(Rocq `SpecMycpu.wp_mycpu_sconf_body`.)

Imports only definitional files (never a `Code*` or `Proof*` file).
-/
import MachCSL.CallConv
import Xv6.Image
import Xv6.Geom

namespace Xv6

open Iris Iris.ProgramLogic Iris.BI Std MachCSL
open LeanRV64D

/-- Address of `mycpu`. -/
def mycpuAddr : BitVec 64 := BitVec.ofNat 64 KernelSyms.«mycpu»

/-- **WP of `mycpu`.**  Two stack slots; returns `&cpus[hartid]` in `a0`. -/
def wp_mycpu_body {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [CurCtx]
    (cpu : CPU) (k : KCtx) (hsie : k.sie = false) (htier : k.tier = KTier.bare) (hK : 2 ≤ k.avail) : Prop :=
  kctx cpu k ∗ pcIs cpu mycpuAddr ∗
  (∀ R' : RegMap, kctx cpu (k.withRegs R') -∗ pcIs cpu (retPc (k.regs 1#5)) -∗
    ⌜calleeSaved k.regs R' ∧ R' 10#5 = cpuAddr cpu⌝ -∗ wpLoop cpu)
  ⊢ wpLoop (GF := GF) cpu

/-- The interface of `mycpu`. -/
structure MYCPU : Prop where
  wp_mycpu : ∀ {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [CurCtx] (cpu : CPU) (k : KCtx) hsie htier hK,
    wp_mycpu_body (hlc := hlc) (GF := GF) cpu k hsie htier hK

end Xv6
