/-
**THE SYSTEM THEOREM, THE ACCESS DISCIPLINE RECORDED** (weak-allocproc plan
rev 30 §C top [R25.2] (iii), review R27.s4; the (r2) sibling root's
generic part [OWN.37]): `xv6PowerAdequacy` at the final reading
`phi g := g.pow = true → AccessDiscipline.xv6AccessDisc g.m`, its hook
discharged by `AccessDiscipline.powerInterp_accessDisc` (the record
literal's static list is xv6's, `rfl`).

* `xv6DiscAdequacy` (the unit application, as `xv6FsAdequacy`),
  `xv6DiscAdequacyImg` (at the literal mkfs image) and
  `xv6DiscAdequacy_xv6GF` (at the concrete functor list); the closed root is
  `LinkDiscAdequacy.xv6DiscAdequacy_closed`.

Every existing statement is unchanged; the machine semantics and the
trusted assumptions are `xv6FsAdequacy_xv6GF`'s.
-/
import Xv6.SystemAdequacy
import Xv6.AccessDiscipline

namespace Xv6

open Iris Iris.BI Iris.ProofMode Iris.Std Std MachCSL
open Iris.ProgramLogic Language.Notation PrimStep

section unit
variable {hlc : HasLC} {GF : BundledGFunctors} [MachGpreS hlc GF] [Xv6G GF] [WchGpre GF]
  [CtokG GF] [DiskG GF] [IcacheG GF] [LogG GF] [FsBlocksG GF] [IregG GF] [FsTopG GF] [FsLinkG GF]
  [IcboxG GF] [SleepLockG GF] [BcacheG GF] [OffboxG GF] [OffboxBoxG GF] [FileG GF]

include hlc GF in
/-- **THE ACCESS DISCIPLINE HOLDS ON EVERY REACHABLE POWERED STATE** (the
unit application, `xv6PowerAdequacy`'s arbitrary-`phi` slot): every
reachable thread is reducible and, whenever the power is on, the machine's
memory obeys `xv6AccessDisc` (`chainOkAt ∧ lockWordDiscAt ∧ cpuStaticAt ∧
lkCpuReadAt ∧ pteDiscAt`: W8 (f2-ctx), (f3-hold) [OWN.64], (f3-ptek)
[OWN.66]; `chainOkAt`'s `ip->ref` value clause W8 (f3-racy) [OWN.63]). -/
theorem xv6DiscAdequacy (US : USER) (g : GState) (sb : FsSb) (nib : Nat)
    (cov : ExtTreeSet Nat compare)
    (Hgen0 : g.gen = 0) (Hpow : g.pow = false)
    (Himg : fsBootImageWf (diskOf g.m.devs) XV6_DISK_BYTES sb nib cov)
    (n : Nat) (κs : List Obs) (t2 : List Expr) (g2 : GState)
    (hsteps : ([Expr.power], g) -<κs>->ₜₚ^[n] (t2, g2)) :
    (∀ e2, e2 ∈ t2 → Reducible (e2, g2)) ∧ (g2.pow = true → AccessDiscipline.xv6AccessDisc g2.m) :=
  xv6PowerAdequacy (hlc := hlc) (GF := GF) US g sb nib cov
    (fun g' => g'.pow = true → AccessDiscipline.xv6AccessDisc g'.m)
    (fun Hinv γgen γstart γreg γd γsw γobs γhist c T g' => by
      letI : MachFixedGS hlc GF := xv6FixedGS Unit (fun _ _ _ => iprop(True)) appTrivOkc cov sb.sbLogstart
        (appIfaceTriv GF) Hinv γgen γstart γreg γd γsw γobs γhist c T (obsPredAt γobs)
        (appTrivTk c) (appTrivHk c)
      iintro ⟨H, -⟩
      ihave %h := AccessDiscipline.powerInterp_accessDisc (hlc := hlc) (GF := GF) rfl g' $$ H
      imodintro
      ipureintro
      exact h)
    Hgen0 Hpow Himg n κs t2 g2 hsteps

include hlc GF in
/-- **AT THE LITERAL MKFS IMAGE** (`xv6FsAdequacyImg`'s twin). -/
theorem xv6DiscAdequacyImg (US : USER) (g : GState)
    (Hgen0 : g.gen = 0) (Hpow : g.pow = false) (Hdisk : diskOf g.m.devs = fsImgDisk)
    (n : Nat) (κs : List Obs) (t2 : List Expr) (g2 : GState)
    (hsteps : ([Expr.power], g) -<κs>->ₜₚ^[n] (t2, g2)) :
    (∀ e2, e2 ∈ t2 → Reducible (e2, g2)) ∧ (g2.pow = true → AccessDiscipline.xv6AccessDisc g2.m) :=
  xv6DiscAdequacy (hlc := hlc) (GF := GF) US g fsimgSb fsimgNib fsimgCov Hgen0 Hpow
    (fsimgHimg g Hdisk) n κs t2 g2 hsteps

end unit

/-- **AT THE CONCRETE FUNCTOR LIST** (`xv6FsAdequacy_xv6GF`'s twin): no
ghost-state class assumed, the literal mkfs image.  Premises: `USER`, the
machine off and never booted, `fs.img` on its disk. -/
theorem xv6DiscAdequacy_xv6GF {hlc : HasLC} (US : USER) (g : GState)
    (Hgen0 : g.gen = 0) (Hpow : g.pow = false) (Hdisk : diskOf g.m.devs = fsImgDisk)
    (n : Nat) (κs : List Obs) (t2 : List Expr) (g2 : GState)
    (hsteps : ([Expr.power], g) -<κs>->ₜₚ^[n] (t2, g2)) :
    (∀ e2, e2 ∈ t2 → Reducible (e2, g2)) ∧ (g2.pow = true → AccessDiscipline.xv6AccessDisc g2.m) :=
  letI : MachGpreS hlc xv6GF := xv6GF_machGpreS hlc 0
  xv6DiscAdequacyImg (hlc := hlc) (GF := xv6GF) US g Hgen0 Hpow Hdisk n κs t2 g2 hsteps

end Xv6
