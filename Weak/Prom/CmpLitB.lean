/-
Weak/Prom: **completeness S3b — the AMO and LR/SC FORBIDDEN rows of plan §5 re-derived as ref ⇒ mach ⇒ lit**
(acceptance of plan rev 7 §8 "S3a+b re-derive every §5 FORBIDDEN verdict as `ref ⇒ mach ⇒ lit`").

For each FORBIDDEN row in S3b's scope with a `lit_` theorem (rows 5, 10, 11, 11b, 23, 28, 28c, 37):
* `refFromLit_<row>` — the REFERENCE-LEVEL VERDICT derived from the logic: no execution the reference allows has the
  `lit_` theorem's outcome, over the reference's own observations (`refObsLoad`, `refFinalMem`, `finalReg`).
  Proof: `rvwmo_complete` (through `refFromLit`, or `refFromLitReg` for a final-register outcome) + the `lit_`
  theorem.  The scope premises (`progS3bB`, uniform size for NA-6) are discharged by `decide`.
* `refLit_<row> : forbiddenRef <row>` — the verdict in the reference's vocabulary (the statement of `Ref*.lean`'s
  `ref_<row>`, the reference checker's verdict), and `refLit_<row>_agrees : refLit_<row> = Lit.ref_<row> := rfl`
  (it typechecks only if the two statements coincide).
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Prom.CmpLitT
import Weak.Prom.CoreLitM
import Weak.Prom.RefLitmus2

namespace Weak.Prom.Cmp

open Weak.Prom Weak.Prom.Mach Weak.Prom.Mach.Cert
open Weak.Prom.Ref
open Weak.Prom.Ref.Lit (X Y Z)

/-! ## The generic corollary for final registers -/

/-- **REF ⇒ MACH ⇒ LIT, final registers**: a property of the final registers that every valid run of machine v2
(every hart finished) has, every reference execution has, of its own final registers (`finalReg`). -/
theorem refFromLitReg (T : Test) (hT : progS3bB T = true) {s : Nat} (hu : uniformB T s = true) (hs : 0 < s)
    (Q : (Nat → Nat → Nat) → Prop)
    (hlit : ∀ (M : List PMsg) (run : PF.PFRun LP Unit), PF.validRun litStep (testImg T) () (progs T) M run →
      run.cfg.pcAgs.length = T.harts.length → allDone run.cfg → Q (regOf run.cfg)) :
    ∀ chs ν g, progExec T chs ν g → ∀ trs, T.runAll chs = some trs → Q (finalReg trs ν) := by
  intro chs ν g hE trs hr
  have hE' := hE
  unfold progExec at hE'
  rw [hr] at hE'
  obtain ⟨hc, hX⟩ := hE'
  obtain ⟨run, hv, _, hlen, hdone, _, hreg, _⟩ :=
    rvwmo_complete T hT hr hc hX (singleSize_of_uniform hT hu hs g hr hc) trivial
  have : regOf run.cfg = finalReg trs ν := funext fun h => funext fun r => hreg h r
  rw [← this]
  exact hlit _ run hv hlen hdone

/-! ## Row 10, MP+amo.rl+amo.aq (rules 5, 6; M0) -/

theorem refFromLit_mpAmoRlAq : ∀ chs ν g, progExec Lit.mpAmoRlAq chs ν g → ∀ trs, Lit.mpAmoRlAq.runAll chs = some trs →
    ¬ (refObsLoad (conc Lit.mpAmoRlAq trs ν g) 1 0 = some 1 ∧ refObsLoad (conc Lit.mpAmoRlAq trs ν g) 1 1 = some 0) :=
  refFromLit Lit.mpAmoRlAq (by decide +kernel) (s := 4) (by decide +kernel) (by decide)
    (fun ob _ => ¬ (ob 1 0 = some 1 ∧ ob 1 1 = some 0)) (fun M run hv _ => PF.lit_mpAmoRlAq M run hv)

theorem refLit_mpAmoRlAq : forbiddenRef Lit.mpAmoRlAq :=
  forbid_of_lit Lit.mpAmoRlAq (by decide +kernel) (s := 4) (by decide +kernel) (by decide)
    (fun ob _ => ¬ (ob 1 0 = some 1 ∧ ob 1 1 = some 0)) (fun M run hv _ => PF.lit_mpAmoRlAq M run hv)
    (fun chs ν g trs hE hr hout hQ => by
      have H : (OC.and (.reg 1 10 1) (.reg 1 11 0)).eval (finalReg trs ν)
        (finalByte (conc Lit.mpAmoRlAq trs ν g)) = true := hout
      simp only [oc_and_iff] at H
      obtain ⟨e0, e1⟩ := H
      exact hQ ⟨(obsReg4 (by decide +kernel) (by decide +kernel) hE hr (r := 10) (by decide +kernel) (by decide) _).2 e0,
        (obsReg4 (by decide +kernel) (by decide +kernel) hE hr (r := 11) (by decide +kernel) (by decide) _).2 e1⟩)

theorem refLit_mpAmoRlAq_agrees : refLit_mpAmoRlAq = Lit.ref_mpAmoRlAq := rfl

/-! ## Row 11, MP+fence.rw.w-amo+amo-fence.r.rw (rule 4 both sides, the AMO a load and a store) -/

theorem refFromLit_mpFAmo : ∀ chs ν g, progExec Lit.mpFAmo chs ν g → ∀ trs, Lit.mpFAmo.runAll chs = some trs →
    ¬ (refObsLoad (conc Lit.mpFAmo trs ν g) 1 0 = some 1 ∧ refObsLoad (conc Lit.mpFAmo trs ν g) 1 1 = some 0) :=
  refFromLit Lit.mpFAmo (by decide +kernel) (s := 4) (by decide +kernel) (by decide)
    (fun ob _ => ¬ (ob 1 0 = some 1 ∧ ob 1 1 = some 0)) (fun M run hv _ => PF.lit_mpFAmo M run hv)

theorem refLit_mpFAmo : forbiddenRef Lit.mpFAmo :=
  forbid_of_lit Lit.mpFAmo (by decide +kernel) (s := 4) (by decide +kernel) (by decide)
    (fun ob _ => ¬ (ob 1 0 = some 1 ∧ ob 1 1 = some 0)) (fun M run hv _ => PF.lit_mpFAmo M run hv)
    (fun chs ν g trs hE hr hout hQ => by
      have H : (OC.and (.reg 1 10 1) (.reg 1 11 0)).eval (finalReg trs ν)
        (finalByte (conc Lit.mpFAmo trs ν g)) = true := hout
      simp only [oc_and_iff] at H
      obtain ⟨e0, e1⟩ := H
      exact hQ ⟨(obsReg4 (by decide +kernel) (by decide +kernel) hE hr (r := 10) (by decide +kernel) (by decide) _).2 e0,
        (obsReg4 (by decide +kernel) (by decide +kernel) hE hr (r := 11) (by decide +kernel) (by decide) _).2 e1⟩)

theorem refLit_mpFAmo_agrees : refLit_mpFAmo = Lit.ref_mpFAmo := rfl

/-! ## Row 11b, AMO-store-part+fence.r.rw (M0 (iv)) -/

theorem refFromLit_amoStorePart : ∀ chs ν g, progExec Lit.amoStorePart chs ν g → ∀ trs,
    Lit.amoStorePart.runAll chs = some trs →
    ¬ (refObsLoad (conc Lit.amoStorePart trs ν g) 1 0 = some 2 ∧
      refObsLoad (conc Lit.amoStorePart trs ν g) 1 1 = some 0) :=
  refFromLit Lit.amoStorePart (by decide +kernel) (s := 4) (by decide +kernel) (by decide)
    (fun ob _ => ¬ (ob 1 0 = some 2 ∧ ob 1 1 = some 0)) (fun M run hv _ => PF.lit_amoStorePart M run hv)

theorem refLit_amoStorePart : forbiddenRef Lit.amoStorePart :=
  forbid_of_lit Lit.amoStorePart (by decide +kernel) (s := 4) (by decide +kernel) (by decide)
    (fun ob _ => ¬ (ob 1 0 = some 2 ∧ ob 1 1 = some 0)) (fun M run hv _ => PF.lit_amoStorePart M run hv)
    (fun chs ν g trs hE hr hout hQ => by
      have H : (OC.and (.reg 1 10 2) (.reg 1 11 0)).eval (finalReg trs ν)
        (finalByte (conc Lit.amoStorePart trs ν g)) = true := hout
      simp only [oc_and_iff] at H
      obtain ⟨e0, e1⟩ := H
      exact hQ ⟨(obsReg4 (by decide +kernel) (by decide +kernel) hE hr (r := 10) (by decide +kernel) (by decide) _).2 e0,
        (obsReg4 (by decide +kernel) (by decide +kernel) hE hr (r := 11) (by decide +kernel) (by decide) _).2 e1⟩)

theorem refLit_amoStorePart_agrees : refLit_amoStorePart = Lit.ref_amoStorePart := rfl

/-! ## Row 28, MP+amo-data+fence.r.r (rule 10 from the AMO's single op, M0 (v)) -/

theorem refFromLit_mpAmoData : ∀ chs ν g, progExec Lit.mpAmoData chs ν g → ∀ trs, Lit.mpAmoData.runAll chs = some trs →
    ¬ (refObsLoad (conc Lit.mpAmoData trs ν g) 1 0 = some 5 ∧ refObsLoad (conc Lit.mpAmoData trs ν g) 1 1 = some 0) :=
  refFromLit Lit.mpAmoData (by decide +kernel) (s := 4) (by decide +kernel) (by decide)
    (fun ob _ => ¬ (ob 1 0 = some 5 ∧ ob 1 1 = some 0)) (fun M run hv _ => PF.lit_mpAmoData M run hv)

theorem refLit_mpAmoData : forbiddenRef Lit.mpAmoData :=
  forbid_of_lit Lit.mpAmoData (by decide +kernel) (s := 4) (by decide +kernel) (by decide)
    (fun ob _ => ¬ (ob 1 0 = some 5 ∧ ob 1 1 = some 0)) (fun M run hv _ => PF.lit_mpAmoData M run hv)
    (fun chs ν g trs hE hr hout hQ => by
      have H : (OC.and (.reg 1 11 5) (.reg 1 12 0)).eval (finalReg trs ν)
        (finalByte (conc Lit.mpAmoData trs ν g)) = true := hout
      simp only [oc_and_iff] at H
      obtain ⟨e0, e1⟩ := H
      exact hQ ⟨(obsReg4 (by decide +kernel) (by decide +kernel) hE hr (r := 11) (by decide +kernel) (by decide) _).2 e0,
        (obsReg4 (by decide +kernel) (by decide +kernel) hE hr (r := 12) (by decide +kernel) (by decide) _).2 e1⟩)

theorem refLit_mpAmoData_agrees : refLit_mpAmoData = Lit.ref_mpAmoData := rfl

/-! ## Row 28c, MP+amo-ctrl+fence.r.r (rule 11 from the AMO through `LCtrl`, M0 (v)) -/

theorem refFromLit_mpAmoCtrl : ∀ chs ν g, progExec Lit.mpAmoCtrl chs ν g → ∀ trs, Lit.mpAmoCtrl.runAll chs = some trs →
    ¬ (refObsLoad (conc Lit.mpAmoCtrl trs ν g) 1 0 = some 1 ∧ refObsLoad (conc Lit.mpAmoCtrl trs ν g) 1 1 = some 0) :=
  refFromLit Lit.mpAmoCtrl (by decide +kernel) (s := 4) (by decide +kernel) (by decide)
    (fun ob _ => ¬ (ob 1 0 = some 1 ∧ ob 1 1 = some 0)) (fun M run hv _ => PF.lit_mpAmoCtrl M run hv)

theorem refLit_mpAmoCtrl : forbiddenRef Lit.mpAmoCtrl :=
  forbid_of_lit Lit.mpAmoCtrl (by decide +kernel) (s := 4) (by decide +kernel) (by decide)
    (fun ob _ => ¬ (ob 1 0 = some 1 ∧ ob 1 1 = some 0)) (fun M run hv _ => PF.lit_mpAmoCtrl M run hv)
    (fun chs ν g trs hE hr hout hQ => by
      have H : (OC.and (.reg 1 11 1) (.reg 1 12 0)).eval (finalReg trs ν)
        (finalByte (conc Lit.mpAmoCtrl trs ν g)) = true := hout
      simp only [oc_and_iff] at H
      obtain ⟨e0, e1⟩ := H
      exact hQ ⟨(obsReg4 (by decide +kernel) (by decide +kernel) hE hr (r := 11) (by decide +kernel) (by decide) _).2 e0,
        (obsReg4 (by decide +kernel) (by decide +kernel) hE hr (r := 12) (by decide +kernel) (by decide) _).2 e1⟩)

theorem refLit_mpAmoCtrl_agrees : refLit_mpAmoCtrl = Lit.ref_mpAmoCtrl := rfl

/-! ## Row 23, Par-Inc (atomicity) -/

theorem refFromLit_parInc : ∀ chs ν g, progExec Lit.parInc chs ν g → ∀ trs, Lit.parInc.runAll chs = some trs →
    refFinalMem (conc Lit.parInc trs ν g) X 4 ≠ 1 :=
  refFromLit Lit.parInc (by decide +kernel) (s := 4) (by decide +kernel) (by decide)
    (fun _ fm => fm X 4 ≠ 1) (fun M run hv hd => PF.lit_parInc M run hv (hd 0 (by decide)) (hd 1 (by decide)))

theorem refLit_parInc : forbiddenRef Lit.parInc :=
  forbid_of_lit Lit.parInc (by decide +kernel) (s := 4) (by decide +kernel) (by decide)
    (fun _ fm => fm X 4 ≠ 1) (fun M run hv hd => PF.lit_parInc M run hv (hd 0 (by decide)) (hd 1 (by decide)))
    (fun chs ν g trs hE hr hout hQ => by
      have H : (OC.mem X 4 1).eval (finalReg trs ν) (finalByte (conc Lit.parInc trs ν g)) = true := hout
      exact hQ ((oc_mem_iff (by decide)).1 H))

theorem refLit_parInc_agrees : refLit_parInc = Lit.ref_parInc := rfl

/-! ## Row 5, LB+lrsc (manual `litmus_lb_lrsc`; deps from a successful SC, M4) -/

theorem refFromLit_lbLrsc : ∀ chs ν g, progExec Lit.lbLrsc chs ν g → ∀ trs, Lit.lbLrsc.runAll chs = some trs →
    ¬ (refObsLoad (conc Lit.lbLrsc trs ν g) 0 0 = some 0 ∧ refObsLoad (conc Lit.lbLrsc trs ν g) 1 0 = some 0) :=
  refFromLit Lit.lbLrsc (by decide +kernel) (s := 8) (by decide +kernel) (by decide)
    (fun ob _ => ¬ (ob 0 0 = some 0 ∧ ob 1 0 = some 0)) (fun M run hv _ => PF.lit_lbLrsc M run hv)

theorem refLit_lbLrsc : forbiddenRef Lit.lbLrsc :=
  forbid_of_lit Lit.lbLrsc (by decide +kernel) (s := 8) (by decide +kernel) (by decide)
    (fun ob _ => ¬ (ob 0 0 = some 0 ∧ ob 1 0 = some 0)) (fun M run hv _ => PF.lit_lbLrsc M run hv)
    (fun chs ν g trs hE hr hout hQ => by
      have H : (OC.and (.reg 0 10 0) (.reg 1 13 0)).eval (finalReg trs ν)
        (finalByte (conc Lit.lbLrsc trs ν g)) = true := hout
      simp only [oc_and_iff] at H
      obtain ⟨e0, e1⟩ := H
      exact hQ ⟨(obsReg8 (by decide +kernel) (by decide +kernel) hE hr (r := 10) (by decide +kernel) (by decide) _).2 e0,
        (obsReg8 (by decide +kernel) (by decide +kernel) hE hr (r := 13) (by decide +kernel) (by decide) _).2 e1⟩)

theorem refLit_lbLrsc_agrees : refLit_lbLrsc = Lit.ref_lbLrsc := rfl

/-! ## Row 37, LR;SC-fail;SC (M16: `LExFail` clears the reservation) -/

theorem refFromLit_lrScSc : ∀ chs ν g, progExec Lit.lrScSc chs ν g → ∀ trs, Lit.lrScSc.runAll chs = some trs →
    ¬ (finalReg trs ν 0 11 = 1 ∧ finalReg trs ν 0 13 = 0) :=
  refFromLitReg Lit.lrScSc (by decide +kernel) (s := 4) (by decide +kernel) (by decide)
    (fun fr => ¬ (fr 0 11 = 1 ∧ fr 0 13 = 0)) (fun M run hv hlen hd => by
      have hl : 0 < run.cfg.pcAgs.length := by rw [hlen]; decide
      have hag : run.cfg.pcAgs[0]? = some run.cfg.pcAgs[0] := List.getElem?_eq_getElem hl
      obtain ⟨h1, h2⟩ := hd 0 _ hag
      have hfin : PF.PFRun.done PF.litFin run 0 run.cfg.pcAgs[0].paSt :=
        ⟨_, hag, by simp [PF.litFin, h1, h2]⟩
      have := PF.lit_lrScSc M run hv _ hfin
      simpa [regOf, hag] using this)

theorem refLit_lrScSc : forbiddenRef Lit.lrScSc := by
  intro chs ν g hE hout
  unfold outcome at hout
  cases hr : Lit.lrScSc.runAll chs with
  | none => rw [hr] at hout; cases hout
  | some trs =>
    rw [hr] at hout
    have H : (OC.and (.reg 0 11 1) (.reg 0 13 0)).eval (finalReg trs ν)
      (finalByte (conc Lit.lrScSc trs ν g)) = true := hout
    simp only [oc_and_iff] at H
    exact refFromLit_lrScSc chs ν g hE trs hr ⟨oc_reg (by decide) H.1, oc_reg (by decide) H.2⟩

theorem refLit_lrScSc_agrees : refLit_lrScSc = Lit.ref_lrScSc := rfl

end Weak.Prom.Cmp

#print axioms Weak.Prom.Cmp.rvwmo_complete
#print axioms Weak.Prom.Cmp.rvwmo_complete_exec
#print axioms Weak.Prom.Cmp.refLit_mpAmoRlAq
#print axioms Weak.Prom.Cmp.refLit_mpFAmo
#print axioms Weak.Prom.Cmp.refLit_amoStorePart
#print axioms Weak.Prom.Cmp.refLit_mpAmoData
#print axioms Weak.Prom.Cmp.refLit_mpAmoCtrl
#print axioms Weak.Prom.Cmp.refLit_parInc
#print axioms Weak.Prom.Cmp.refLit_lbLrsc
#print axioms Weak.Prom.Cmp.refLit_lrScSc
