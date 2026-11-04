/-
Weak/Prom: **track (b)'s machine-side conditions for litmus programs** (stage S4b part 2; plan rev 7 §4 "For the
G4 litmus targets they are dischargeable … every fetch reads the image (PA-0), there are no walks and there are no
A/D messages"; NF_R premise `invalFree`, R-b5).

For EVERY valid machine-v2 run of a litmus test (program half `litStep`, every hart starting with an empty label
queue): the run is FETCH-BOUNDED (`lit_fetchBounded`: `litStep` emits no `LIFetch`, so PO-fetch holds per program,
NfrRun.lean `fetchBounded_ofImg`) and `invalFree` (`lit_invalFree`: `litStep` emits no `LCmo`, so no message of the
final memory is a cache-block operation — every message is fulfilled by its author's write label,
MachSolo.lean `validRun_solo` + CoreRun.lean `solo_fulfils`).  Program-agnostic over litmus tests.
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Prom.OwnKit
import Weak.Prom.MachNota
import Weak.Prom.MachForbid
import Weak.Prom.LitNoCmo   -- MachFix-R-b5: `nfL` … `lit_noInval` moved there

namespace Weak.Prom.Own

open MachCSL MachCSL.Stdpp Iris.Std
open Weak (Image Dsrc)
open Weak.Prom Weak.Prom.Nfr Weak.Prom.Mach Weak.Prom.Mach.Cert
open Weak.Prom.Ref (Instr)
open PLabel

/-- Along a solo run of a litmus hart from a well-formed queue, no label is a fetch or a CMO. -/
theorem solo_nf {img : Image} {M : List PMsg} {h : Nat} :
    ∀ {x y : LP × PState × GSet Nat} {τ : List (PLabel × Option Nat)},
      soloSteps litStep img M h x τ y → qOk x.1.q →
      ∀ e ∈ τ, (∀ b tvs, e.1 ≠ LIFetch b tvs) ∧ (∀ k b len asrc, e.1 ≠ LCmo k b len asrc) := by
  intro x y τ hs
  induction hs with
  | refl => intro _ e he; cases he
  | step x l ots p' ws' prom' tr y hp _ _ ih =>
    intro hq e he
    rcases List.mem_cons.1 he with rfl | he
    · exact litNext_nf hq hp
    · exact ih (litNext_q hq hp) e he

/-- **PO-fetch for every litmus test** (plan §4: dischargeable per program; here for all litmus programs at once). -/
theorem lit_fetchBounded {img : Image} {ps : List LP} {evs : List PEvt} {cfg : PCfg LP Unit}
    (hv : validRun litStep img () ps evs cfg) (hps : ∀ p ∈ ps, p.q = []) :
    fetchBounded litStep img ps cfg.pcLog evs := by
  apply fetchBounded_ofImg
  intro hh e he base tvs hl
  rcases Nat.lt_or_ge hh ps.length with hlt | hge
  · obtain ⟨ag, _, P0, _, hs⟩ := validRun_solo hv hh _ (List.getElem?_eq_getElem hlt)
    have hq : qOk ps[hh].q := by rw [hps _ (List.getElem_mem hlt)]; exact qOk_nil
    exact absurd hl ((solo_nf hs hq e he).1 base tvs)
  · rw [PF.validRun_traceNone hv (List.getElem?_eq_none hge)] at he
    cases he

/-- **`invalFree` for every litmus test**: no message of the final memory is a cache-block operation
(MachFix-R-b5: now `lit_noInval`, LitNoCmo.lean). -/
theorem lit_invalFree {img : Image} {ps : List LP} {evs : List PEvt} {cfg : PCfg LP Unit}
    (hv : validRun litStep img () ps evs cfg) (hps : ∀ p ∈ ps, p.q = []) : invalFree cfg.pcLog :=
  lit_noInval hv hps

end Weak.Prom.Own
