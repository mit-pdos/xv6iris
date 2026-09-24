/-
The two `KCtx` facts the proofs of `uvmalloc` and `uvmdealloc`
(kernel/vm.c) share: the frame context of a call, at either interrupt
index.

Imports only definitional files (never a `Code*`, `Proof*` or `Link*` file).
-/
import MachCSL.WpSmodeFrame

namespace Xv6

open Iris Iris.ProgramLogic Iris.BI Std MachCSL
open LeanRV64D

/-- The frame context of a call. -/
theorem ua_pushed_withSpie (k : KCtx) (m : Nat) (a b : Bool) :
    (k.pushed m).withSpie a b = (k.withSpie a b).pushed m := rfl

theorem ua_pushed_spie_self (k : KCtx) (m : Nat) :
    k.pushed m = (k.pushed m).withSpie k.spie k.spp :=
  (KCtx.withSpie_self' (k.pushed m) k.spie k.spp rfl rfl).symm

end Xv6
