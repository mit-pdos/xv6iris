/-
The console (kernel/console.c): the `cons` object -- a spinlock, the
128-byte input ring and its three indices -- and the payload of `cons.lock`.

```
struct { struct spinlock lock; char buf[128]; uint r, w, e; } cons;
```
at `KA.«cons»`: the lock at +0 (24 bytes), the ring at +24, `r` at +152,
`w` at +156, `e` at +160 (168 bytes with padding).

The payload is the raw ring: every index the code uses goes through
`% INPUT_BUF_SIZE` (`andi 127`), so no arithmetic fact about `r`, `w`, `e`
is needed for memory safety, and the port keeps none (the Rocq
`ConsoleInv` couples the ring to the receive column of the UART; that is
future work here).
-/
import MachCSL.CallConv
import MachCSL.Lock
import MachCSL.KCtxMove
import Xv6.Image
import Xv6.UartInv

namespace Xv6

open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode Std MachCSL

variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF]

/-- `&cons` (= `&cons.lock`). -/
def consAddr : BitVec 64 := KA.«cons»
/-- `cons.buf`. -/
def consBufAddr : BitVec 64 := KA.«cons» + 24#64
/-- `&cons.r` (sleep/wakeup channel of the readers). -/
def consRAddr : BitVec 64 := KA.«cons» + 152#64
/-- `&cons.w`. -/
def consWAddr : BitVec 64 := KA.«cons» + 156#64
/-- `&cons.e`. -/
def consEAddr : BitVec 64 := KA.«cons» + 160#64

/-- What `cons.lock` protects: the ring and the three indices, raw. -/
def consBody [CurCtx] : IProp GF := iprop%
  ∃ (buf : List (BitVec 8)) (r w e : BitVec 32),
    ⌜buf.length = 128⌝ ∗ byteBuf consBufAddr (DFrac.own 1) buf ∗
    wordPointsTo consRAddr 4 (DFrac.own 1) r ∗
    wordPointsTo consWAddr 4 (DFrac.own 1) w ∗
    wordPointsTo consEAddr 4 (DFrac.own 1) e

/-- The payload as a function of the context that owns the cells: the
lock's own until a winner takes it at its own (`lockPay`/`lock_pay_take`).
It must NOT close over the ambient context, or the handle would not
transport -- the shape `Xv6.ticksResAt`, `Xv6.diskRes` and
`Xv6.procLockPay` have.  At the ambient context it IS the raw body
(`consRes_cur`, `rfl`), so a holder still sees `consBody`. -/
def consRes [CurCtx] : CtxId → IProp GF := fun ξ => @consBody hlc GF _ ⟨ξ, curTier⟩

/-- The payload a holder takes is the raw body. -/
theorem consRes_cur [CurCtx] : consRes (GF := GF) curCtx = consBody := rfl

local instance ctxMorph_byteBufT (t : KTier) (a : BitVec 64) (dq : DFrac) (bs : List (BitVec 8)) :
    CtxMorph (GF := GF) (fun ξ => @byteBuf hlc GF _ ⟨ξ, t⟩ a dq bs) :=
  ctxMorph_bigSepL bs
    (fun j b ξ => @wordPointsTo hlc GF _ ⟨ξ, t⟩ (a + BitVec.ofNat 64 j) 1 dq b)
    (fun _ _ => instCtxMorphWordAt _ _ _ _ _)

instance consRes_morph [CurCtx] : CtxMorph (GF := GF) consRes := by
  unfold consRes consBody; infer_instance

/-- The credential of `cons.lock`. -/
def isConsLock [CurCtx] (γc : GName) : IProp GF := isLock γc consAddr "cons" consRes

instance isConsLock_persistent [CurCtx] (γc : GName) : Persistent (isConsLock (GF := GF) γc) := by
  unfold isConsLock; infer_instance

/-- What `uarts[i].rx` needs when `uartintr` calls it: at port 0 the hook is
`consoleintr` (the console lock, port 0's transmit bundle for the echo, and
a sublist witness of its trace); at port 1 there is no hook. -/
def uartRxCaps [CurCtx] [Xv6G GF] (i : UartId) (γc γl : GName) (γ : UartNames) (bs : List (BitVec 8)) : IProp GF :=
  match i with
  | .uart0 => iprop(isConsLock γc ∗ uartPort .uart0 γl γ ∗ uartSentSub γ bs)
  | .uart1 => iprop(emp)

instance uartRxCaps_persistent [CurCtx] [Xv6G GF] (i : UartId) (γc γl : GName) (γ : UartNames) (bs : List (BitVec 8)) :
    Persistent (uartRxCaps (GF := GF) i γc γl γ bs) := by
  cases i <;> unfold uartRxCaps <;> infer_instance

end Xv6
