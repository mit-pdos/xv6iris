/-
The console's transmit trace and its lock, as the printing cone sees them
(the Rocq `WpUart.uart_sent` / `UartTxInv.uart_sent_sub` / `is_txlock`).

The UART device itself (registers, the transmitter's state, the interrupt
path) is not modelled yet; what `consputc`/`printint`/`printk` need of it
is the transmit TRACE: a monotone list of the bytes accepted by the
transmitter, of which a caller holds a persistent sublist witness
(`uartSentSub`), and the transmit lock (`tx_lock`), whose resource is the
transmitter's half of the trace.
-/
import MachCSL.Lock
import Xv6.Geom
import Iris.BI.Lib.MonoList

namespace Xv6

open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode Std MachCSL

/-- The ghost state the console cone needs beyond `MachGS`. -/
class Xv6G (GF : BundledGFunctors) where
  [monoListG : MonoListG GF (BitVec 8)]
  [gvListG : GhostVarG GF (List (BitVec 8))]

attribute [instance] Xv6G.monoListG Xv6G.gvListG

/-- The names of the console's ghosts: the accepted trace and the
transmitter's half. -/
structure UartNames where
  acc : GName
  tx : GName

section
variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF]

/-- The trace so far has `tr` as a prefix (persistent). -/
def uartSent (γ : UartNames) (tr : List (BitVec 8)) : IProp GF := MonoList.lb_own γ.acc tr

instance uartSent_persistent (γ : UartNames) (tr : List (BitVec 8)) : Persistent (uartSent (GF := GF) γ tr) := by
  unfold uartSent; infer_instance

/-- `bs` is a sublist of what has been sent: what a caller threads through
the printing cone (other harts may interleave their bytes). -/
def uartSentSub (γ : UartNames) (bs : List (BitVec 8)) : IProp GF := iprop%
  ∃ tr : List (BitVec 8), uartSent γ tr ∗ ⌜bs.Sublist tr⌝

instance uartSentSub_persistent (γ : UartNames) (bs : List (BitVec 8)) :
    Persistent (uartSentSub (GF := GF) γ bs) := by
  unfold uartSentSub; infer_instance

theorem uartSentSub_of_sent (γ : UartNames) (tr : List (BitVec 8)) :
    uartSent (GF := GF) γ tr ⊢ uartSentSub γ tr := by
  unfold uartSentSub
  iintro H
  iexists tr
  iframe H
  ipureintro; exact List.Sublist.refl tr

theorem uartSentSub_nil (γ : UartNames) (bs : List (BitVec 8)) :
    uartSentSub (GF := GF) γ bs ⊢ uartSentSub γ [] := by
  unfold uartSentSub
  iintro ⟨%tr, H, %_⟩
  iexists tr
  iframe H
  ipureintro; exact List.nil_sublist tr

/-- The transmitter's half of the trace: the `tx_lock`'s resource. -/
def txRes (γ : UartNames) : IProp GF := iprop% ∃ l : List (BitVec 8), γ.tx ↪VAR{.own (1 : Qp).half} l

/-- `tx_lock` (`kernel/uart.c`). -/
def txLockAddr : BitVec 64 := 0x80012380#64

/-- The transmit lock, as the printing cone holds it (persistent). -/
def isTxLock [CurCtx] (γl : GName) (γ : UartNames) : IProp GF :=
  isLock γl txLockAddr "uart" (fun _ => txRes γ)

instance isTxLock_persistent [CurCtx] (γl : GName) (γ : UartNames) : Persistent (isTxLock (GF := GF) γl γ) := by
  unfold isTxLock; infer_instance

end

end Xv6
