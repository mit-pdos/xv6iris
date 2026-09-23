/-
Specification of `uartwrite` (kernel/uart.c): write `n` bytes of a kernel
buffer to port `uid`, one byte per acquisition of the transmit lock,
sleeping on `&uarts[uid]` while the transmitter is busy (woken by
`uartintr`).

```
void uartwrite(int uid, char buf[], int n) {
  struct uart *u = &uarts[uid];
  int i = 0;
  while (i < n) {
    sleep_prepare(u);
    acquire(&u->tx_lock);
    if (ReadReg(u, LSR) & LSR_TX_IDLE) { WriteReg(u, THR, buf[i]); release(&u->tx_lock); i += 1; }
    else { release(&u->tx_lock); sleep(); }
  }
}
```

The running thread is proc `j` (sleep's linkage: `procsInv`, the trap
CSRs, the hart's claim, the interrupt resource; interrupts off, depth 0, no
lock held, at the kernel page table).  The caller holds the port's bundle
and a sublist witness of the trace; the buffer is read-only at any
fraction; the witness comes back extended by the buffer (the Rocq
`SpecUartwrite`'s `out_chain` is replaced by the sublist witness the Lean
port uses throughout).  Stack: the 8-slot frame over `sleep`'s 20.

Imports only definitional files.
-/
import MachCSL.CallConv
import Xv6.Image
import Xv6.UartInv
import Xv6.SchedCtx
import Xv6.SpecSleep

namespace Xv6

open Iris Iris.ProgramLogic Iris.BI Std MachCSL
open LeanRV64D

/-- Address of `uartwrite`. -/
def uartwriteAddr : BitVec 64 := KA.«uartwrite»

/-- The stack `uartwrite`'s cone needs: its 8-slot frame over `sleep`'s. -/
def uartwriteSlots : Nat := 8 + sleepSlots

/-- **WP of `uartwrite`.**  `a0` the port index, `a1` the buffer, `a2` the count. -/
def wp_uartwrite_body {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF] [CurCtx]
    (Γ : SchedNames) [ClaimIs (hlc := hlc) GF Γ]
    (cpu : CPU) (k : KCtx) (i : UartId) (γl : GName) (γ : UartNames) (j : Nat)
    (bs cs : List (BitVec 8)) (dq : DFrac) (n : Nat)
    (hj : j < NPROC) (hproc : k.proc = procAddr j) (hK : uartwriteSlots ≤ k.avail)
    (hsie : k.sie = false) (hnoff : k.noff = 0) (hlocks : k.locks = [])
    (htier : k.tier = KTier.kpt)
    (hid : k.regs 10#5 = BitVec.ofNat 64 i.idx)
    (hn : k.regs 12#5 = BitVec.ofNat 64 n) (hn' : n < 2 ^ 31) (hcs : cs.length = n) : Prop :=
  kctx cpu k ∗ pcIs cpu uartwriteAddr ∗ procsInv Γ ∗
  trapCsrs cpu ∗ cpuClaim cpu k.proc ∗ intrRes cpu ∗
  uartPort i γl γ ∗ uartSentSub γ bs ∗ byteBuf (k.regs 11#5) dq cs ∗
  wpNext true k.proc cpu (fun cpu' => iprop(∀ (spie spp : Bool) (R' : RegMap),
    ⌜calleeSaved k.regs R'⌝ -∗
    kctx cpu' ((k.withSpie spie spp).withRegs R') -∗ pcIs cpu' (jumpPc (k.regs 1#5)) -∗
    trapCsrs cpu' -∗ cpuClaim cpu' k.proc -∗ intrRes cpu' -∗
    byteBuf (k.regs 11#5) dq cs -∗ uartSentSub γ (bs ++ cs) -∗ wpLoop cpu'))
  ⊢ wpLoop (GF := GF) cpu

/-- The interface of `uartwrite`. -/
structure UARTWRITE : Prop where
  wp_uartwrite : ∀ {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF] [CurCtx]
    (Γ : SchedNames) [ClaimIs (hlc := hlc) GF Γ]
    (cpu : CPU) (k : KCtx) (i : UartId) (γl : GName) (γ : UartNames) (j : Nat)
    (bs cs : List (BitVec 8)) (dq : DFrac) (n : Nat) hj hproc hK hsie hnoff hlocks htier hid hn hn' hcs,
    wp_uartwrite_body (hlc := hlc) (GF := GF) Γ cpu k i γl γ j bs cs dq n hj hproc hK hsie hnoff hlocks htier hid hn hn' hcs

end Xv6
