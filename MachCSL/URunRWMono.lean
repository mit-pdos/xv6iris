/-
MachCSL: what a walk of `runRW` cannot change (lane U1-F): any state
property every node preserves (`runRW_preserves`) and the owned map's domain
(`runRW_dom`; Rocq `HartMemRun`'s `dom mm' = dom mm` obligation, the
`u_mem_step_dom` of `UserBytes`).  These are what a closer of the user
tier needs to carry the loop-constant configuration pins
(`Xv6.UserFrame.UfCfg`) and the byte map's shape (`Xv6.UbMemStep.dom`)
across a stretch.
-/
import MachCSL.UByteFrame

namespace MachCSL

open Sail Sail.ConcurrencyInterfaceV1
open Sail.ArchSem (FreeM)
open LeanRV64D LeanRV64D.Functions

/-- **A walk keeps the owned map's domain.** -/
theorem runRW_dom (D : UFoot) {X : Type} (m : SailM X) (orc : UOrc) (s : UWSt) (x : X) (s' : UWSt)
    (orc' : UOrc) (h : runRW D orc s m = some (x, s', orc')) (a : PAddr) :
    (s'.mm a).isSome = (s.mm a).isSome := by
  refine runRW_preserves D (fun s s' => (s'.mm a).isSome = (s.mm a).isSome) (fun _ => rfl)
    (fun _ _ _ h1 h2 => h2.trans h1) (fun _ _ _ _ => rfl) (fun _ => rfl) ?_ m orc s x s' orc' h
  intro s pa n w hn ho
  exact bmWrite_isSome s.mm pa n w (by omega) ho a

end MachCSL
