/-
**THE TRACE-LEVEL NONINTERFERENCE THEOREM, CLOSED** (NI M2-W4): the NI
application theorem (`NiAdequacy.xv6NiAppAdequacy`) at the generic
application (`appTriv`, `USER` discharged by `ProofUser.userProof`), the
concrete functor list `xv6GF` and the literal mkfs image -- the hypotheses
of `LinkSystemAdequacyClosed.xv6FsAdequacy_closed` (the machine off, never
booted, `fs.img` on its disk) -- and its two pure corollaries over runs.

* **`xv6NiAdequacy`**: every reachable thread is reducible and the run's
  trace satisfies `xv6NiPhi` (a ledger filing of it, ONE-SHOT -- W2d's
  `niOneShot`, which closes the origin loophole --, every incarnation's
  trace obeying the class law).
* **`xv6NiTwoRun`**: two runs, each from such a machine; per incarnation,
  equal inputs (first key, later origins' keys, per-round masks and exit
  contents) and equal uptime readings (`events`), the incarnation's ecalls
  in the class, give equal enters (getpid's answer is the incarnation's
  pid, part of `q`).
* **`xv6NiStrongInstance`**: in one run, every incarnation's enters before
  its first ecall replay its exits (T's `utRoundQuiet` at the trace).

A `Link` file because it consumes `ProofUser` (tools/check_layering.sh).

## Honest scope

The class is {exit, getpid, uptime}; every filing spent a distinct claim
minted before its enter (`niOneShot`, W2d); the mask is carried per filing;
uptime's tick is a reading, getpid's answer the incarnation's pid (`NiTrace`
header).  The filings `F` are existential (O6): the corollaries hold at the
one-shot filings the run's ledger witnesses.
-/
import Xv6.NiAdequacy
import Xv6.ProofUser

namespace Xv6

open Iris Iris.BI Iris.ProofMode Iris.Std Std MachCSL
open Iris.ProgramLogic Language.Notation PrimStep

/-- **THE NI THEOREM, `USER` discharged**: from the machine off, never
booted, with `fs.img` on its disk, every reachable thread is reducible and
the run's boundary trace is filed by the NI ledger, every incarnation's
trace obeying the class law. -/
theorem xv6NiAdequacy {hlc : HasLC}
    (g : GState) (Hgen0 : g.gen = 0) (Hpow : g.pow = false) (Hdisk : diskOf g.m.devs = fsImgDisk)
    (n : Nat) (κs : List Obs) (t2 : List Expr) (g2 : GState)
    (hsteps : ([Expr.power], g) -<κs>->ₜₚ^[n] (t2, g2)) :
    (∀ e2, e2 ∈ t2 → Reducible (e2, g2)) ∧ xv6NiPhi g2 κs :=
  letI : MachGpreS hlc xv6GF := xv6GF_machGpreS hlc 0
  haveI : Xv6AppLaws (hlc := hlc) (appTriv xv6GF) := appTriv_laws userProof
  xv6NiAppAdequacy (hlc := hlc) (GF := xv6GF) g fsimgSb fsimgNib fsimgCov (appTriv xv6GF)
    (fun c => appTriv_init c _) Hgen0 Hpow (fsimgHimg g Hdisk) n κs t2 g2 hsteps

/-- **THE TWO-RUN COROLLARY**: two runs from booting machines; at the
filings their ledgers witness, an incarnation `q` whose ecalls (in run 1)
are in the class, with equal inputs and equal readings in the two runs, has
equal enters. -/
theorem xv6NiTwoRun {hlc : HasLC}
    (g₁ g₂ : GState) (Hgen₁ : g₁.gen = 0) (Hpow₁ : g₁.pow = false) (Hdisk₁ : diskOf g₁.m.devs = fsImgDisk)
    (Hgen₂ : g₂.gen = 0) (Hpow₂ : g₂.pow = false) (Hdisk₂ : diskOf g₂.m.devs = fsImgDisk)
    (n₁ n₂ : Nat) (κs₁ κs₂ : List Obs) (t₁ t₂ : List Expr) (g₁' g₂' : GState)
    (hsteps₁ : ([Expr.power], g₁) -<κs₁>->ₜₚ^[n₁] (t₁, g₁'))
    (hsteps₂ : ([Expr.power], g₂) -<κs₂>->ₜₚ^[n₂] (t₂, g₂')) :
    ∃ F₁ F₂, niOk κs₁ F₁ ∧ niOneShot κs₁ F₁ ∧ niOk κs₂ F₂ ∧ niOneShot κs₂ F₂ ∧ ∀ q : NiInc,
      NiInClass (utrace q κs₁ F₁) →
      (utrace q κs₁ F₁).map NiStep.input = (utrace q κs₂ F₂).map NiStep.input →
      events q κs₁ F₁ = events q κs₂ F₂ →
      (utrace q κs₁ F₁).map NiStep.output = (utrace q κs₂ F₂).map NiStep.output := by
  obtain ⟨-, F₁, hF₁, h1₁, -⟩ := xv6NiAdequacy (hlc := hlc) g₁ Hgen₁ Hpow₁ Hdisk₁ n₁ κs₁ t₁ g₁' hsteps₁
  obtain ⟨-, F₂, hF₂, h1₂, -⟩ := xv6NiAdequacy (hlc := hlc) g₂ Hgen₂ Hpow₂ Hdisk₂ n₂ κs₂ t₂ g₂' hsteps₂
  exact ⟨F₁, F₂, hF₁, h1₁, hF₂, h1₂, fun q hc hin hev => niTwoRun hF₁ hF₂ q hc hin hev⟩

/-- **THE STRONG INSTANCE**: in a run from a booting machine, at the filing
its ledger witnesses, every incarnation's steps before its first ecall
replay their exits (`NiTrace.niStrongInstance`; T's
`UtRoundQuiet.utRoundQuiet` lifted to the trace). -/
theorem xv6NiStrongInstance {hlc : HasLC}
    (g : GState) (Hgen0 : g.gen = 0) (Hpow : g.pow = false) (Hdisk : diskOf g.m.devs = fsImgDisk)
    (n : Nat) (κs : List Obs) (t2 : List Expr) (g2 : GState)
    (hsteps : ([Expr.power], g) -<κs>->ₜₚ^[n] (t2, g2)) :
    ∃ F, niOk κs F ∧ niOneShot κs F ∧ ∀ q : NiInc, ∀ s ∈ (utrace q κs F).takeWhile (fun s => !s.ecall), s.replays := by
  obtain ⟨-, F, hF, h1, -⟩ := xv6NiAdequacy (hlc := hlc) g Hgen0 Hpow Hdisk n κs t2 g2 hsteps
  exact ⟨F, hF, h1, niStrongInstance hF⟩

end Xv6

#print axioms Xv6.xv6NiAdequacy
#print axioms Xv6.xv6NiTwoRun
#print axioms Xv6.xv6NiStrongInstance
