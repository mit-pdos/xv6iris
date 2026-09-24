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
import MachCSL.Dev.DevIds
import Xv6.Geom
import Iris.BI.Lib.MonoList
import Iris.Algebra.Auth
import Iris.Algebra.UFrac

namespace Xv6

open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode Std MachCSL

/-- The ghost state the xv6 client needs beyond `MachGS` -- and the ONE home
of every camera two xv6 subsystems share (one instance per camera type, as
Rocq's `inG`; the subsystems' ghost NAMES keep their resources apart).  The
`MonoNatG` camera is `MachGS`'s own (`MachFixedGS.mono`). -/
class Xv6G (GF : BundledGFunctors) where
  [monoListG : MonoListG GF (BitVec 8)]
  [gvListG : GhostVarG GF (List (BitVec 8))]
  [gvNatG : GhostVarG GF Nat]
  [gvUnitG : GhostVarG GF Unit]
  /-- the per-proc hart tag (`SchedCtx.hartOwn`) -/
  [gvCpuG : GhostVarG GF CPU]
  /-- the per-proc state mirror (`SchedCtx.pstateOwn`) -/
  [gvW32G : GhostVarG GF (BitVec 32)]
  /-- the UART's divisor-latch flag (`UartInv.dlabAuth`) -/
  [gvBoolG : GhostVarG GF Bool]
  /-- THE ONE `Nat ↦ ()` ghost-map camera: the log's open transactions
  (`LogNames.tx`), the buffer cache's slot tokens (`BcacheNames.slot`) and
  the file table's fd-slot tokens (`FileNames.fd`) all live here, told
  apart by their ghost NAMES (Rocq: one `ghost_mapG Σ nat unit`) -/
  [gmUnitG : GhostMapG GF Nat Unit RegMapF]
  /-- THE ONE `Nat ↦ block bytes` ghost-map camera: the disk image
  (`DiskNames.img`) and the log's logged view (`FsNames.cache`) -/
  [gmBlkG : GhostMapG GF Nat (List (BitVec 8)) RegMapF]
  /-- THE ONE `Auth (Option UFrac)` camera (Rocq's `authUR (optionUR
  ufracR)`): a tracked sleeplock's "may hold" counter (`Xv6.SlhRF`,
  per-lock names) and the iref-slot supply (`Xv6.IrefslotRF`,
  `IrefslotG.irefslotName`) -/
  [authUfracG : ElemG GF (constOF (Auth (Option UFrac)))]

attribute [instance] Xv6G.monoListG Xv6G.gvListG
attribute [reducible, instance] Xv6G.gvNatG Xv6G.gvUnitG Xv6G.gvCpuG Xv6G.gvW32G Xv6G.gvBoolG
attribute [reducible, instance] Xv6G.gmUnitG Xv6G.gmBlkG Xv6G.authUfracG

/-- The names of one port's ghosts (the Rocq `UartNames.uart_names`, the
subset the Lean port carries): the accepted trace (`mono_list` over
`Uart.acc`), the transmitted prefix (`mono_list` over `u.out`), the
transmit token (`ghost_var` halves over the accepted trace), the divisor
latch (`ghost_var` over `Uart.dlab`, frozen once `uartinit` is done), and
the receive column: the bytes that ever entered the FIFO (`mono_list`) and
the popped count (`ghost_var` halves -- the popper's token), and the
one-shot that says whether `uartinit` has run (`ghost_var` over `Bool`). -/
structure UartNames where
  acc : GName
  out : GName
  tx : GName
  dlab : GName
  rxin : GName
  rxpop : GName
  /-- the port's ONE-SHOT: `false` while the port is still pre-`uartinit`
  (`UartInv.uartPreinit`, an exclusive whole), persistently `true` once
  `uartinit` has run and the receive token exists
  (`UartInv.uartInited`).  It lets the PLIC's invariant be allocated at
  power-on, before there is any `rxTok` to put in its slots. -/
  init : GName

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

/-- The index of a port in `uarts[]` (`kernel/uart.c`). -/
def _root_.MachCSL.UartId.idx : UartId → Nat
  | .uart0 => 0
  | .uart1 => 1

/-- `&uarts[i].tx_lock` (`kernel/uart.c`: `struct uart` is 40 bytes, the
lock at offset 16). -/
def txLockAddr (i : UartId) : BitVec 64 :=
  KA.«uarts» + BitVec.ofNat 64 (40 * i.idx + 16)

/-- The name `uartinit` gives port `i`'s transmit lock. -/
def txLockName : UartId → String
  | .uart0 => "uart0"
  | .uart1 => "uart1"

/-- Port `i`'s transmit lock, as a printing cone holds it (persistent). -/
def isTxLockAt [CurCtx] (i : UartId) (γl : GName) (γ : UartNames) : IProp GF :=
  isLock γl (txLockAddr i) (txLockName i) (fun _ => txRes γ)

instance isTxLockAt_persistent [CurCtx] (i : UartId) (γl : GName) (γ : UartNames) :
    Persistent (isTxLockAt (GF := GF) i γl γ) := by
  unfold isTxLockAt; infer_instance

end

end Xv6
