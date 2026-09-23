/-
Specifications of `setkilled`, `killed` and `kkill` (kernel/proc.c): the
`killed` field under `p->lock`; `kkill(pid)` scans for the pid, sets the
flag and wakes a sleeper (`0`), or `-1`.  Generic in SIE and depth
(`"proc"` not held).  setkilled/killed need 14 slots, kkill 16.

Imports only definitional files (never a `Code*` or `Proof*` file).
-/
import MachCSL.WpSmodeFrame
import MachCSL.Lock
import Xv6.SchedCtx
import Xv6.PidLock
import Xv6.Image
import Xv6.Geom

namespace Xv6

open Iris Iris.ProgramLogic Iris.BI Std MachCSL
open LeanRV64D

def setkilledAddr : BitVec 64 := KA.«setkilled»
def killedAddr : BitVec 64 := KA.«killed»
def kkillAddr : BitVec 64 := KA.«kkill»

def wp_setkilled_body {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF] [CurCtx]
    (Γ : SchedNames) (cpu : CPU) (k : KCtx) (j : Nat)
    (hj : j < NPROC) (hp : k.regs 10#5 = procAddr j)
    (hnoff : k.noff + 1 < 2 ^ 31) (hK : 14 ≤ k.avail) (hlk : "proc" ∉ k.locks) (htier : k.tier = KTier.kpt) : Prop :=
  kctx cpu k ∗ pcIs cpu setkilledAddr ∗ procsInv Γ ∗
  wpNext k.sie k.proc cpu (fun cpu' => iprop(∀ spie : Bool, ∀ spp : Bool, ∀ R' : RegMap,
    ⌜k.sie = false → spie = k.spie ∧ spp = k.spp⌝ -∗
    kctx cpu' ((k.withSpie spie spp).withRegs R') -∗ pcIs cpu' (jumpPc (k.regs 1#5)) -∗
    ⌜calleeSaved k.regs R'⌝ -∗ wpLoop cpu'))
  ⊢ wpLoop (GF := GF) cpu

structure SETKILLED : Prop where
  wp_setkilled : ∀ {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF] [CurCtx] (Γ : SchedNames) (cpu : CPU) (k : KCtx)
    (j : Nat) hj hp hnoff hK hlk htier,
    wp_setkilled_body (hlc := hlc) (GF := GF) Γ cpu k j hj hp hnoff hK hlk htier

def wp_killed_body {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF] [CurCtx]
    (Γ : SchedNames) (cpu : CPU) (k : KCtx) (j : Nat)
    (hj : j < NPROC) (hp : k.regs 10#5 = procAddr j)
    (hnoff : k.noff + 1 < 2 ^ 31) (hK : 14 ≤ k.avail) (hlk : "proc" ∉ k.locks) (htier : k.tier = KTier.kpt) : Prop :=
  kctx cpu k ∗ pcIs cpu killedAddr ∗ procsInv Γ ∗
  wpNext k.sie k.proc cpu (fun cpu' => iprop(∀ spie : Bool, ∀ spp : Bool, ∀ R' : RegMap,
    ⌜k.sie = false → spie = k.spie ∧ spp = k.spp⌝ -∗
    kctx cpu' ((k.withSpie spie spp).withRegs R') -∗ pcIs cpu' (jumpPc (k.regs 1#5)) -∗
    ⌜calleeSaved k.regs R' ∧ ∃ kl : BitVec 32, R' 10#5 = BitVec.signExtend 64 kl⌝ -∗ wpLoop cpu'))
  ⊢ wpLoop (GF := GF) cpu

structure KILLED : Prop where
  wp_killed : ∀ {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF] [CurCtx] (Γ : SchedNames) (cpu : CPU) (k : KCtx)
    (j : Nat) hj hp hnoff hK hlk htier,
    wp_killed_body (hlc := hlc) (GF := GF) Γ cpu k j hj hp hnoff hK hlk htier

def wp_kkill_body {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF] [CurCtx]
    (Γ : SchedNames) (cpu : CPU) (k : KCtx)
    (hnoff : k.noff + 1 < 2 ^ 31) (hK : 16 ≤ k.avail) (hlk : "proc" ∉ k.locks) (htier : k.tier = KTier.kpt) : Prop :=
  kctx cpu k ∗ pcIs cpu kkillAddr ∗ procsInv Γ ∗
  wpNext k.sie k.proc cpu (fun cpu' => iprop(∀ spie : Bool, ∀ spp : Bool, ∀ R' : RegMap,
    ⌜k.sie = false → spie = k.spie ∧ spp = k.spp⌝ -∗
    kctx cpu' ((k.withSpie spie spp).withRegs R') -∗ pcIs cpu' (jumpPc (k.regs 1#5)) -∗
    ⌜calleeSaved k.regs R' ∧ (R' 10#5 = 0#64 ∨ R' 10#5 = -1#64)⌝ -∗ wpLoop cpu'))
  ⊢ wpLoop (GF := GF) cpu

structure KKILL : Prop where
  wp_kkill : ∀ {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF] [CurCtx] (Γ : SchedNames) (cpu : CPU) (k : KCtx)
    hnoff hK hlk htier,
    wp_kkill_body (hlc := hlc) (GF := GF) Γ cpu k hnoff hK hlk htier

end Xv6
