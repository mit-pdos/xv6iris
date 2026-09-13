/-
Specification of `kernelvec` (kernel/kernelvec.S), xv6's supervisor trap
vector.  Nothing calls it: the hardware traps to it.  Its contract is
therefore not a function spec but the trap engine's handler contract
`ihs ⟨cpu, kernelvec⟩` (`MachCSL.KCtx`): from the context a supervisor
interrupt leaves, the handler runs and resumes the interrupted context at
the trapped pc, on whichever hart the thread lands on.
Imports only definitional files.
-/
import Xv6.Image
import Xv6.UartTrace
import MachCSL.WpSmodeIntr

namespace Xv6

open Iris Iris.ProgramLogic Iris.BI Std MachCSL
open LeanRV64D

/-- Address of `kernelvec`. -/
def kernelvecAddr : BitVec 64 := BitVec.ofNat 64 KernelSyms.«kernelvec»

/-- `stvec := kernelvec` is a direct-mode vector. -/
theorem kernelvecAddr_direct : stvecDirect kernelvecAddr := by
  unfold stvecDirect kernelvecAddr KernelSyms.«kernelvec»; decide

/-- The interface of `kernelvec`: the handler contract, at every hart. -/
structure KERNELVEC : Prop where
  handler : ∀ {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF] (cpu : CPU),
    ⊢@{IProp GF} ihs ⟨cpu, kernelvecAddr⟩

end Xv6
