/-
Specification of `copyout` (kernel/vm.c): the kernel writing `len` bytes
INTO a process's memory at `dstva` (through its page table, size `psz`)
FROM the kernel buffer `src`, faulting in lazily allocated pages on the way
(`vmfault`, the uncounted mode).  Returns `0`, or `-1` after writing a
strict prefix (a failed fault, or a page without `PTE_W`).
copyout needs 52 slots.

THE IMAGE is Rocq's equation (`umem_wr M dstva len src_bytes`, SpecCopyout.v)
in the Lean view: `umemWrite (viewFaulted P P' M) dst bs` -- the Lean view
zeroes the pages the lazy faults added, where Rocq's `us_M` already holds
them as zeros -- AND `umMapped P' dst d` on both arms: every page the
written prefix touches is mapped in `P'`.  Rocq needs no such conjunct (its
view never re-zeroes a page); here it is what lets a caller that copies in
chunks (readi, piperead, consoleread, sys_pipe) chain the chunks'
equations: a later chunk's fault zeroes only pages new to it, never one an
earlier chunk wrote (`UMemL.umemWrite_chain` / `UMemL.umemWrite_step`).

Imports only definitional files (never a `Code*` or `Proof*` file).
-/
import MachCSL.WpSmodeFrame
import MachCSL.Lock
import Xv6.UMem
import Xv6.Image
import Xv6.Geom

namespace Xv6

open Iris Iris.ProgramLogic Iris.BI Std MachCSL
open LeanRV64D

def copyoutAddr : BitVec 64 := KA.«copyout»

/-- `copyout(pt a0, psz a1, dstva a2, src a3, len a4)`. -/
def wp_copyout_body {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF] [CurCtx]
    (cpu : CPU) (k : KCtx) (γl : GName) (γk : KmemNames) (P : UPtd) (M : Nat → List (BitVec 8))
    (dqs : DFrac) (bs : List (BitVec 8))
    (hnoff : k.noff + 1 < 2 ^ 31) (hK : 52 ≤ k.avail) (hlk : "kmem" ∉ k.locks)
    (hroot : k.regs 10#5 = pageAddr P.root) (hsz : (k.regs 11#5).toNat ≤ 2 ^ 38)
    (hlen : k.regs 14#5 = BitVec.ofNat 64 bs.length) (hlen' : bs.length < 2 ^ 63) : Prop :=
  kctx cpu k ∗ pcIs cpu copyoutAddr ∗ isLock γl kmemLockAddr "kmem" (kmemRes γk) ∗ kallocAvail γk none ∗
  procPtAt P M ∗ byteBuf (k.regs 13#5) dqs bs ∗
  wpNext k.sie k.proc cpu (fun cpu' => iprop(∀ spie : Bool, ∀ spp : Bool, ∀ R' : RegMap,
    ⌜k.sie = false → spie = k.spie ∧ spp = k.spp⌝ -∗
    kctx cpu' ((k.withSpie spie spp).withRegs R') -∗ pcIs cpu' (jumpPc (k.regs 1#5)) -∗
    byteBuf (k.regs 13#5) dqs bs -∗
    (∃ (P' : UPtd) (M' : Nat → List (BitVec 8)),
      ⌜P.extSz (k.regs 11#5) P' ∧
        ((R' 10#5 = 0#64 ∧ M' = umemWrite (viewFaulted P P' M) (k.regs 12#5).toNat bs ∧
            umMapped P' (k.regs 12#5).toNat bs.length) ∨
         (R' 10#5 = -1#64 ∧ ∃ d, d < bs.length ∧
            M' = umemWrite (viewFaulted P P' M) (k.regs 12#5).toNat (bs.take d) ∧
            umMapped P' (k.regs 12#5).toNat d))⌝ ∗
      procPtAt P' M') -∗
    ⌜calleeSaved k.regs R'⌝ -∗ wpLoop cpu'))
  ⊢ wpLoop (GF := GF) cpu

structure COPYOUT : Prop where
  wp_copyout : ∀ {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF] [CurCtx] (cpu : CPU) (k : KCtx)
    (γl : GName) (γk : KmemNames) (P : UPtd) (M : Nat → List (BitVec 8)) (dqs : DFrac) (bs : List (BitVec 8))
    hnoff hK hlk hroot hsz hlen hlen',
    wp_copyout_body (hlc := hlc) (GF := GF) cpu k γl γk P M dqs bs hnoff hK hlk hroot hsz hlen hlen'


end Xv6
