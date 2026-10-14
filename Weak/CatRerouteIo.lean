/-
Weak: **W11-B — (K-cat′)'s NON-CLOSING I/O-window steps, certified through the re-route**
(plan `notes/weak-allocproc-plan.md` rev 52, §C top "W11 — PART LIST (rev 51)" part B and
"W11 — LAUNCH PLAN [rev 50]" part W11-B = W11 obligation (1); rulings [OWN.61], [OWN.75]).
Lean-only, no Rocq twin.

**The gap (`WeakRvwmoKillIOC.lean` §§3–5).**  `ioSegCertC` certifies a segment through an I/O
event `x` only under the NAMED per-step condition `ioStepCloses` (every step after `x`) and the
NAMED exit condition `ioExitCloses`.  A step outside them — the same-source R→R `gpoloc` off the
forwarded byte or out of a gmo-after-`x` read (riscv.cat's ppo rule 2 exempts it, `\ rsw`;
`kcatCex`, `kcatCexNotCloses`) — or a forwarded exit reached by a forwarding arm may leave the
exit gmo-BEFORE the entry, so the window segment has no `CertC` at all (`rrIoNoCert`).

**The re-route (W11-A, `CatReroute.lean`).**  The I/O window is closed by the device lock's
`release` (`fence rw,w; sw` of the disk/UART lock word), a RAM write `REL` po-after the window's
exit; the window's next reader enters through the lock's `ACQ` (`amoswap.w.aq`).  Re-routing the
window's exit to `REL` needs only `entry <gmo REL`, and that holds with NO condition on the
window's steps: the entry is gmo-before `x` ((R1) for a RAM entry, (R3) for an I/O entry, or the
entry IS `x`) and `x` is gmo-before every po-later RAM write ((R2) of `ioResidueGmo`).  So the
non-closing steps and exits never need certifying one by one: the whole window `(entry, REL)` is
`CertC.Pinned`, and the reader's segment `(ACQ, exit')` is certified by `.aq` (rule 5) from the hop
`REL ⇝ ACQ` (`rrIn`).

  §1  `ioWinRelGmo` (entry `<gmo` REL for ANY same-row run through `x`, no step condition),
      `ioWinRrOut` (the annotation's OUT obligation `rrOutOk` for the window re-routed to `REL`),
      **`ioSegCertRrC`** — `ioSegCertC` RESTATED with the re-routed chain: the window, exit
      re-routed to `REL`, is `CertC.Pinned` at its predecessor; **`ioSegRerouteC`** — the whole
      re-routed chain (`chainCReroute` with the window as the hole); `ioSegRerouteKill` — a cyclic
      annotated raw chain whose re-routed segments are I/O windows dies (`cycleKillReroute`).
  §2  NON-VACUITY on `rrIo` (`CatReroute.lean` §4.2, the `kcatCex` shape): the window
      `x →gpow w →rfi u →gpoloc v` has the step `u → v` OUTSIDE `ioStepCloses` (`rrIoNotCloses`)
      and NO `CertC` at `ioCross` (`rrIoNoCert`), yet `ioSegCertRrC` certifies it re-routed
      (`rrIoWinCert`) and `ioSegRerouteC` builds the re-routed chain (`rrIoWinChain`).

**The hop.**  `REL ⇝ ACQ` enters as `rrIn`'s premise (one cross edge, or any gmo path).  From the
export it is W11-D's `rrInOfHopChain` (`RvwmoXv6Adequacy.lean` §6.3): the lock's hand-off
(`chainOkAt`'s `syncPath`) through `R`'s log identification.

**Spec standing.**  FAITHFUL.  Orders used: rule 5 (`.aq`, via `certRerouteIn`), the trusted
residue `ioResidueGmo` arms (R1)/(R2)/(R3) only (riscv.cat's fence bits are r/w only, so a
`fence rw,w` does NOT order an I/O event — (R2) does, as in `rrExitIo`), and `CatLin.rvwmoCatAD`
(implied by the published tagged model).  No trap-entry ordering, no RVWMO⁻ same-address R→R order.
`ioStepCloses`/`ioExitCloses` are NOT assumed here — the window is certified whatever its steps.

**Deviations from the plan text.**  (1) The release's fence is NOT used: (R2) already orders `x`
before every po-later RAM write, so `REL` need only be a RAM write po-after the exit (the release
`sw` of `fence rw,w; sw` is one); the lemma is stated for any such write — it only widens.  (2) The
entry may be gmo-before `x` (any run `entry →* x`) — `rrExitIo` needed an I/O entry.

**Name map (all new).**  `ioWinRelGmo`, `ioWinRrOut`, `ioSegCertRrC`, `ioSegRerouteC`,
`ioSegRerouteKill`, `rrIoWinCert`, `rrIoWinChain`.
-/
import Weak.CatReroute

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open Lbl

namespace CatLin

/-! # 1. The window re-routed to the device lock's release -/

/-- **The window's entry is gmo-before every RAM write po-after its exit**, for ANY same-row run
through the I/O event `x` (no condition on the steps after `x`): entry `≤gmo x` ((R1)/(R3)),
`x <gmo REL` ((R2)). -/
theorem ioWinRelGmo (GF : Gfexec) (ad : List (Geid × Geid)) (x entry exit rel : Geid) :
    rvwmoCatAD GF.gfGd ad → ioResidueGmo GF →
    gisIo GF.gfGd.gdG x = true → gmem GF.gfGd.gdG entry →
    rtc (rsameC GF.gfGd) entry x → rtc (rsameC GF.gfGd) x exit →
    WeakRvwmoGraph.gpo GF.gfGd.gdG exit rel → gisW GF.gfGd.gdG rel = true →
    gmoLt GF.gfGd.gdG entry rel := by
  intro hc hres hio hm hex hxe hpo hw
  have hxr : WeakRvwmoGraph.gpo GF.gfGd.gdG x rel := by
    rcases CatReroute.runPo GF.gfGd ad _ _ hc hxe with heq | hp
    · rw [heq]; exact hpo
    · exact gpoTrans _ _ _ _ hp hpo
  have hxrel : gmoLt GF.gfGd.gdG x rel := hres x rel (Or.inr (Or.inl ⟨hxr, hio, hw⟩))
  rcases CatReroute.runPo GF.gfGd ad _ _ hc hex with heq | hpe
  · rw [heq]; exact hxrel
  · have hen : gmoLt GF.gfGd.gdG entry x := by
      cases he : gisIo GF.gfGd.gdG entry with
      | false => exact hres entry x (Or.inl ⟨hpe, hm, he, hio⟩)
      | true => exact hres entry x (Or.inr (Or.inr (Or.inr (Or.inl ⟨he, hio, hpe⟩))))
    exact gmoLtTrans _ _ _ _ hen hxrel

/-- **The window's OUT obligation** for the re-route `(REL, ACQ)`: `REL` a RAM write po-after the
exit, the hop `REL ⇝ ACQ` (one cross edge or a gmo path). -/
theorem ioWinRrOut (GF : Gfexec) (ad : List (Geid × Geid)) (X : Geid → Geid → Prop) (x : Geid)
    (s : Seg) (r : Reroute) :
    rvwmoCatAD GF.gfGd ad → ioResidueGmo GF →
    gisIo GF.gfGd.gdG x = true → gmem GF.gfGd.gdG s.sgEntry →
    rtc (rsameC GF.gfGd) s.sgEntry x → rtc (rsameC GF.gfGd) x s.sgExit →
    WeakRvwmoGraph.gpo GF.gfGd.gdG s.sgExit r.rrRel → gisW GF.gfGd.gdG r.rrRel = true →
    (X r.rrRel r.rrAcq ∨ gmoLt GF.gfGd.gdG r.rrRel r.rrAcq) →
    rrOutOk GF.gfGd.gdG X s (some r) := by
  intro hc hres hio hm hex hxe hpo hw hhop
  exact ⟨hpo, WeakRvwmoGraph.glblIsWGmem _ _ (WeakRvwmoKillIOC.gisWGlbl _ _ hw),
    ioWinRelGmo GF ad x s.sgEntry s.sgExit r.rrRel hc hres hio hm hex hxe hpo hw, hhop⟩

/-- **`ioSegCertC` RESTATED with the re-routed chain** ([OWN.61]): the I/O window through `x`,
its exit re-routed to the device lock's release `REL` (a RAM write po-after the exit), is
`CertC.Pinned` at its predecessor — for ANY steps after `x` (the non-closing ones included) and
ANY exit (`ioExitCloses` not assumed). -/
theorem ioSegCertRrC (GF : Gfexec) (ad : List (Geid × Geid)) (X : Geid → Geid → Prop)
    (prev x rel : Geid) (s : Seg) :
    rvwmoCatAD GF.gfGd ad → ioResidueGmo GF →
    gisIo GF.gfGd.gdG x = true → gmem GF.gfGd.gdG s.sgEntry →
    rtc (rsameC GF.gfGd) s.sgEntry x → rtc (rsameC GF.gfGd) x s.sgExit →
    WeakRvwmoGraph.gpo GF.gfGd.gdG s.sgExit rel → gisW GF.gfGd.gdG rel = true →
    X prev s.sgEntry → CertC GF.gfGd.gdG X prev ⟨s.sgHart, s.sgEntry, rel⟩ :=
  fun hc hres hio hm hex hxe hpo hw hX =>
    certRerouteExit GF.gfGd.gdG X prev rel s hX
      (ioWinRelGmo GF ad x s.sgEntry s.sgExit rel hc hres hio hm hex hxe hpo hw)

/-- **THE RE-ROUTED CHAIN through an I/O window** (`chainCReroute` with the window `s` as the
hole): certified up to `p`, the window `s` entered from `p`, the reader's segment `s'` entered
through the hop `REL ⇝ ACQ` (`rrIn`), certified after `s'.exit`. -/
theorem ioSegRerouteC (GF : Gfexec) (ad : List (Geid × Geid)) (X : Geid → Geid → Prop)
    (x0 p y x rel acq : Geid) (pre post : List Seg) (s s' : Seg) :
    rvwmoCatAD GF.gfGd ad → ioResidueGmo GF → (∀ a b, X a b → gmoLt GF.gfGd.gdG a b) →
    chainC GF.gfGd.gdG X x0 p pre → X p s.sgEntry →
    gisIo GF.gfGd.gdG x = true → gmem GF.gfGd.gdG s.sgEntry →
    rtc (rsameC GF.gfGd) s.sgEntry x → rtc (rsameC GF.gfGd) x s.sgExit →
    WeakRvwmoGraph.gpo GF.gfGd.gdG s.sgExit rel → gisW GF.gfGd.gdG rel = true →
    rrIn GF.gfGd.gdG X rel acq s'.sgExit → chainC GF.gfGd.gdG X s'.sgExit y post →
    chainC GF.gfGd.gdG X x0 y
      (pre ++ ⟨s.sgHart, s.sgEntry, rel⟩ :: ⟨s'.sgHart, acq, s'.sgExit⟩ :: post) :=
  fun hc hres hX hpre hx hio hm hex hxe hpo hw hin hpost =>
    chainCReroute GF.gfGd.gdG X x0 p y rel acq pre post s s' hc.2.1 hX hpre hx
      (ioWinRelGmo GF ad x s.sgEntry s.sgExit rel hc hres hio hm hex hxe hpo hw) hin hpost

/-- **THE KILL with I/O windows re-routed**: a cyclic annotated raw chain is impossible — its
re-routed I/O windows meet `rrOutOk` by `ioWinRrOut` (any steps after `x`). -/
theorem ioSegRerouteKill (GF : Gfexec) (ad : List (Geid × Geid)) (X : Geid → Geid → Prop)
    (z : Geid) (ι : Option Reroute) (l : List (Seg × Option Reroute)) :
    rvwmoCatAD GF.gfGd ad → (∀ a b, X a b → gmoLt GF.gfGd.gdG a b) →
    l ≠ [] → rrRawChain GF.gfGd X z ι z ι l → False :=
  cycleKillReroute GF.gfGd ad X z ι l

/-! # 2. Non-vacuity: the `kcatCex`-shaped window, its step outside `ioStepCloses` -/

/-- **The window `(x, v)` of `rrIo` — its step `u → v` OUTSIDE `ioStepCloses`
(`rrIoNotCloses`), NO `CertC` at `ioCross` (`rrIoNoCert`) — is certified re-routed to the
release `(0,5)`**, by `ioSegCertRrC` (no step condition). -/
theorem rrIoWinCert :
    CertC rrIo.gfGd.gdG (ioCross rrIo) (2, 0) ⟨0, (0, 0), (0, 5)⟩ := by
  obtain ⟨hx0, hr0, -⟩ := rrIoRaw
  exact ioSegCertRrC rrIo _ (ioCross rrIo) (2, 0) (0, 0) (0, 5) ⟨0, (0, 0), (0, 3)⟩ rrIoCatAD
    rrIoResidue (by decide +kernel) (GraphFabResidue.gisIoGmem _ _ (by decide +kernel))
    (rtc_refl _) hr0 ((gpoBSpec _ _ _).1 (by decide +kernel)) (by decide +kernel) hx0

/-- **…and the whole re-routed chain** `[(x, REL); (ACQ, w2)]` at `ioCross`, by `ioSegRerouteC`
(the hop `REL →rfe ACQ`). -/
theorem rrIoWinChain :
    chainC rrIo.gfGd.gdG (ioCross rrIo) (2, 0) (1, 1)
      ([] ++ ⟨0, (0, 0), (0, 5)⟩ :: ⟨1, (1, 0), (1, 1)⟩ :: []) := by
  obtain ⟨hx0, hr0, -⟩ := rrIoRaw
  refine ioSegRerouteC rrIo _ (ioCross rrIo) (2, 0) (2, 0) (1, 1) (0, 0) (0, 5) (1, 0) [] []
    ⟨0, (0, 0), (0, 3)⟩ ⟨1, (1, 1), (1, 1)⟩ rrIoCatAD rrIoResidue
    (ioCrossGmo rrIo rrIoCatAD.1 rrIoCatAD.2.2.1 rrIoResidue rrIoDiskRead14) rfl hx0
    (by decide +kernel) (GraphFabResidue.gisIoGmem _ _ (by decide +kernel)) (rtc_refl _) hr0
    ((gpoBSpec _ _ _).1 (by decide +kernel)) (by decide +kernel) ?_ rfl
  refine ⟨.inl (.inl (.inl ((grfeBSpec _ _ _).1 (by decide +kernel)))),
    (glblBSpec _ _ _).1 (by decide +kernel), (glblBSpec _ _ _).1 (by decide +kernel),
    .inr ⟨(gpoBSpec _ _ _).1 (by decide +kernel), ⟨LStore false 0 [b1] .WCplain, by decide +kernel, rfl⟩⟩⟩

end CatLin

end Weak
