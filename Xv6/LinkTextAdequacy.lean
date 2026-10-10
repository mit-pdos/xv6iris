/-
**THE KERNEL'S READ-ONLY WINDOW IS PRISTINE, CLOSED** (weak-allocproc plan
§C Stage 0, item W3; the SIBLING root [OWN.9]): `xv6TextAdequacy_xv6GF` at
`userProof`, with `xv6FsAdequacy_closed`'s three boot hypotheses.  A `Link`
file because it consumes `ProofUser` (tools/check_layering.sh: only Link
files import Proof files).

Whenever the power is on, every byte of `[bcRoLo, bcRoHi)` (`.text`,
`.rodata`, `.eh_frame`, `Xv6/BootCarve.lean`) has exactly the fresh era's
history, the boot image's byte at timestamp 0 (`Xv6.textPristine`); so every
agent, the instruction-cache agent included, reads the image there at every
view (`textPristine_read`, `textPristine_readBytes`).
-/
import Xv6.SystemAdequacyText
import Xv6.ProofUser

namespace Xv6

open Iris Iris.BI Iris.ProofMode Iris.Std Std MachCSL
open Iris.ProgramLogic Language.Notation PrimStep

/-- **THE READ-ONLY WINDOW IS PRISTINE, `USER` discharged**: from the machine
off, never booted, with `fs.img` on its disk, every reachable thread is
reducible and, whenever the power is on, the kernel's read-only window holds
the boot image's bytes, never written. -/
theorem xv6TextAdequacy_closed {hlc : HasLC}
    (g : GState) (Hgen0 : g.gen = 0) (Hpow : g.pow = false) (Hdisk : diskOf g.m.devs = fsImgDisk)
    (n : Nat) (κs : List Obs) (t2 : List Expr) (g2 : GState)
    (hsteps : ([Expr.power], g) -<κs>->ₜₚ^[n] (t2, g2)) :
    (∀ e2, e2 ∈ t2 → Reducible (e2, g2)) ∧ (g2.pow = true → textPristine g2) :=
  xv6TextAdequacy_xv6GF (hlc := hlc) userProof g Hgen0 Hpow Hdisk n κs t2 g2 hsteps

end Xv6

#print axioms Xv6.xv6TextAdequacy_closed
