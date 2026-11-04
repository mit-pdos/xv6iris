/-
Weak/Prom: **A0 under havoc — the logic has no rule for an error node** (FIX MachFix-havoc, 2026-11-04;
[OWN.P8]/[OWN.P9]; MachHavoc.lean; plan rev 7 §0 A0).

A remaining Sail error site is HAVOC: a valid run reaching it makes every observation possible
(MachHavoc.lean `allowedH`).  So a program proof must show that no error node is reachable.  The logic does this
by giving an error node NO RULE except "finish with the impossible value":

* `pdoneE perr pdone` — the value map of the hart language with error nodes: an error node is DONE with the value
  `none`; any other state is done with `some v` exactly when `pdone` says `v`.
* `ΦE Φ` — the postcondition: `ΦE Φ h none = False`, `ΦE Φ h (some v) = Φ h v`.
  So the hart wp at an error node is `wpPF … (fun v => ⌜∃ V, ⟦V⟧ ΦE Φ h v⌝)` at a value step whose postcondition is
  `⟦V⟧ False`: it holds only if the protocol is already invalid at `V` (A0 (iv) removes that), i.e. the client must
  show the node is unreachable; MaybeStuck does not help (`wpH_stuck` needs `pdone = none`, false here).
* `adequacyH` — A0 for that world: every conclusion of A0, and NO VALID RUN REACHES AN ERROR NODE
  (`¬ errCfg perr run.cfg`).  With `noHavoc_of_adequacyH` this gives MachHavoc.lean's `¬ havocs`, the half of a
  FORBIDDEN verdict that havoc adds (`forbiddenH_iff`).
How A0 itself reports a havoc run: it does not — `PF.adequacy` is stated over valid runs and says nothing about
error nodes; a "forbidden" claim from A0 alone is a claim about valid runs only, and under havoc it stands only
together with `¬ havocs` (from `adequacyH`, or `noErr_noHavoc` for program halves with no error node — every litmus
front end, so every existing litmus theorem keeps its meaning).
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Prom.CoreAdeq
import Weak.Prom.MachHavoc

namespace Weak.Prom.PF

open MachCSL MachCSL.Stdpp Iris.Std
open Weak (Image Dsrc)
open Weak.Prom
open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode

variable {P D V : Type}

/-- The value map with error nodes: an error node is done with the impossible value `none`. -/
noncomputable def pdoneE (perr : P → Prop) (pdone : P → Option V) : P → Option (Option V) := by
  classical
  exact fun s => if perr s then some none else (pdone s).map some

/-- The postcondition with error nodes: `False` at the impossible value. -/
def ΦE (Φ : Nat → V → Prop) : Nat → Option V → Prop
  | h, some v => Φ h v
  | _, none => False

theorem pdoneE_err {perr : P → Prop} {pdone : P → Option V} {s : P} (h : perr s) : pdoneE perr pdone s = some none := by
  unfold pdoneE; simp [h]

theorem pdoneE_ok {perr : P → Prop} {pdone : P → Option V} {s : P} (h : ¬ perr s) :
    pdoneE perr pdone s = (pdone s).map some := by
  unfold pdoneE; simp [h]

/-- **A0 UNDER HAVOC**: from per-hart wps in the world with error nodes (`pdoneE`, `ΦE`), every conclusion of A0,
and no valid run reaches an error node. -/
theorem adequacyH {hlc : HasLC} {GF : BundledGFunctors} [InvGpreS GF] [GhostVarG GF HSt]
    {pstep : P → D → PLabel → P → D → Prop} {perr : P → Prop} {pdone : P → Option V} {img : Image} {d0 : D}
    {ps : List P} {M : List PMsg} {run : PFRun P D}
    (π : Proto) (Φ : Nat → V → Prop) (Ψ : Nat → Trace → Prop) :
    PO_img π img →
    PO_ad π img M →
    (∀ h, Ψ h []) →
    devFreeProg pstep ps →
    (∀ h p, ps[h]? = some p → ∀ [InvGS_gen hlc GF],
      ⊢@{IProp GF} wpPF π ⟨pstep, pdoneE perr pdone, img, M, h⟩ (Ψ h) p
        (fun v => iprop(⌜∃ V, grd π img M V (ΦE Φ h v)⌝))) →
    validRun pstep img d0 ps M run →
      ¬ errCfg perr run.cfg
    ∧ (∀ h v, run.done pdone h v → Φ h v)
    ∧ (∀ h k, Ψ h ((run.trace h).take k))
    ∧ (∀ t, 1 ≤ t → t ≤ M.length → exU (fun h => t ∈ run.fulfils h ∧ tidAt M t = some h))
    ∧ (∀ h, (run.fulfils h).Nodup)
    ∧ Valid π img M M.length
    ∧ run.traceWf M
    ∧ adExact img M := by
  intro himg had hΨ0 hdf hwp hrun
  obtain ⟨hi, hii, hiii, hiii', hiv, hv, hvi⟩ :=
    adequacy (hlc := hlc) (GF := GF) (pdone := pdoneE perr pdone) π (ΦE Φ) Ψ himg had hΨ0 hdf hwp hrun
  have hno : ¬ errCfg perr run.cfg := by
    rintro ⟨h, ag, hag, he⟩
    exact hi h none ⟨ag, hag, pdoneE_err he⟩
  refine ⟨hno, fun h v ⟨ag, hag, hd⟩ => ?_, hii, hiii, hiii', hiv, hv, hvi⟩
  have hne : ¬ perr ag.paSt := fun he => hno ⟨h, ag, hag, he⟩
  exact hi h (some v) ⟨ag, hag, by simp [pdoneE_ok hne, hd]⟩

/-- The havoc half of a FORBIDDEN verdict from the logic: if every valid run's final memory admits the per-hart
wps (with error nodes), no valid run reaches an error node. -/
theorem noHavoc_of_adequacyH {hlc : HasLC} {GF : BundledGFunctors} [InvGpreS GF] [GhostVarG GF HSt]
    {pstep : P → D → PLabel → P → D → Prop} {perr : P → Prop} {pdone : P → Option V} {img : Image} {d0 : D}
    {ps : List P} (π : Proto) (Φ : Nat → V → Prop) (Ψ : Nat → Trace → Prop)
    (himg : PO_img π img) (had : ∀ M, PO_ad π img M) (hΨ0 : ∀ h, Ψ h []) (hdf : devFreeProg pstep ps)
    (hwp : ∀ M, ∀ h p, ps[h]? = some p → ∀ [InvGS_gen hlc GF],
      ⊢@{IProp GF} wpPF π ⟨pstep, pdoneE perr pdone, img, M, h⟩ (Ψ h) p
        (fun v => iprop(⌜∃ V, grd π img M V (ΦE Φ h v)⌝))) :
    ¬ havocs pstep perr img d0 ps := by
  rintro ⟨evs, cfg, hv, he⟩
  exact (adequacyH (hlc := hlc) (GF := GF) (run := ⟨evs, cfg⟩) π Φ Ψ himg (had cfg.pcLog) hΨ0 hdf
    (hwp cfg.pcLog) ⟨hv, rfl⟩).1 he

end Weak.Prom.PF
