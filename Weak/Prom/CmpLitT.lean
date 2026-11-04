/-
Weak/Prom: **completeness S3a — the FORBIDDEN rows of plan §5 re-derived as ref ⇒ mach ⇒ lit** (acceptance of
plan rev 7 §8 S3a+b, for the rows in S3a's scope).

For every FORBIDDEN row in S3a's scope with a `lit_` theorem (Weak/Prom/CoreLit*.lean):
* `refFromLit_<row>` — the REFERENCE-LEVEL VERDICT derived from the logic: no execution the reference allows has
  the `lit_` theorem's outcome, stated over the reference's own observations (`refObsLoad`, `refFinalMem`).
  Proof: `refFromLit` (rvwmo_complete + the `lit_` theorem).  The scope premises are discharged by `decide`.
* where the `lit_` outcome IS the repository condition, `refLit_<row> : forbiddenRef <row>` — the verdict in the
  reference's vocabulary, the statement of `Ref*.lean`'s `ref_<row>`; `refLit_<row>_agrees` checks the statements
  coincide (`rfl` between the two proofs typechecks only if their types are equal).
* for CoWR0, CoRW1, CoRW2, CoRR, whose `lit_` theorems state the coherence-violating SUB-outcome of the
  repository condition (CoreLitCo.lean header), `refChk_<row>`: the same statement as `refFromLit_<row>`, derived
  instead from the reference checker's `ref_<row>`; `refFromLit_<row>_agrees` checks the statements coincide.
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Prom.CmpLit

namespace Weak.Prom.Cmp

open Weak.Prom Weak.Prom.Mach Weak.Prom.Mach.Cert
open Weak.Prom.Ref
open Weak.Prom.Ref.Lit (X Y Z)

/-! ## Row 2, LB+data+data -/

theorem refFromLit_lbdd : ∀ chs ν g, progExec Lit.lbdd chs ν g → ∀ trs, Lit.lbdd.runAll chs = some trs →
    ¬ (refObsLoad (conc Lit.lbdd trs ν g) 0 0 = some 1 ∧ refObsLoad (conc Lit.lbdd trs ν g) 1 0 = some 1) :=
  refFromLit Lit.lbdd (by decide +kernel) (s := 4) (by decide +kernel) (by decide)
    (fun ob _ => ¬ (ob 0 0 = some 1 ∧ ob 1 0 = some 1)) (fun M run hv _ => PF.lit_lbdd M run hv)

theorem refLit_lbdd : forbiddenRef Lit.lbdd :=
  forbid_of_lit Lit.lbdd (by decide +kernel) (s := 4) (by decide +kernel) (by decide)
    (fun ob _ => ¬ (ob 0 0 = some 1 ∧ ob 1 0 = some 1)) (fun M run hv _ => PF.lit_lbdd M run hv)
    (fun chs ν g trs hE hr hout hQ => by
      have H : (OC.and (.reg 0 5 1) (.reg 1 5 1)).eval (finalReg trs ν) (finalByte (conc Lit.lbdd trs ν g)) = true :=
        hout
      obtain ⟨h1, h2⟩ := oc_and_iff.1 H
      exact hQ ⟨(obsReg4 (by decide +kernel) (by decide +kernel) hE hr (by decide +kernel) (by decide) _).2 h1,
        (obsReg4 (by decide +kernel) (by decide +kernel) hE hr (by decide +kernel) (by decide) _).2 h2⟩)

theorem refLit_lbdd_agrees : refLit_lbdd = Lit.ref_lbdd := rfl

/-! ## `lbDatas` -/

theorem refFromLit_lbDatas : ∀ chs ν g, progExec Lit.lbDatas chs ν g → ∀ trs, Lit.lbDatas.runAll chs = some trs →
    ¬ (refObsLoad (conc Lit.lbDatas trs ν g) 0 0 = some 1 ∧ refObsLoad (conc Lit.lbDatas trs ν g) 1 0 = some 1) :=
  refFromLit Lit.lbDatas (by decide +kernel) (s := 4) (by decide +kernel) (by decide)
    (fun ob _ => ¬ (ob 0 0 = some 1 ∧ ob 1 0 = some 1)) (fun M run hv _ => PF.lit_lbfd M run hv)

theorem refLit_lbDatas : forbiddenRef Lit.lbDatas :=
  forbid_of_lit Lit.lbDatas (by decide +kernel) (s := 4) (by decide +kernel) (by decide)
    (fun ob _ => ¬ (ob 0 0 = some 1 ∧ ob 1 0 = some 1)) (fun M run hv _ => PF.lit_lbfd M run hv)
    (fun chs ν g trs hE hr hout hQ => by
      have H : (OC.and (.reg 0 5 1) (.reg 1 5 1)).eval (finalReg trs ν) (finalByte (conc Lit.lbDatas trs ν g)) = true := hout
      simp only [oc_and_iff] at H
      obtain ⟨e0, e1⟩ := H
      exact hQ ⟨(obsReg4 (by decide +kernel) (by decide +kernel) hE hr (r := 5) (by decide +kernel) (by decide) _).2 e0,
        (obsReg4 (by decide +kernel) (by decide +kernel) hE hr (r := 5) (by decide +kernel) (by decide) _).2 e1⟩)

theorem refLit_lbDatas_agrees : refLit_lbDatas = Lit.ref_lbDatas := rfl

/-! ## `lbCtrls` -/

theorem refFromLit_lbCtrls : ∀ chs ν g, progExec Lit.lbCtrls chs ν g → ∀ trs, Lit.lbCtrls.runAll chs = some trs →
    ¬ (refObsLoad (conc Lit.lbCtrls trs ν g) 0 0 = some 1 ∧ refObsLoad (conc Lit.lbCtrls trs ν g) 1 0 = some 1) :=
  refFromLit Lit.lbCtrls (by decide +kernel) (s := 4) (by decide +kernel) (by decide)
    (fun ob _ => ¬ (ob 0 0 = some 1 ∧ ob 1 0 = some 1)) (fun M run hv _ => PF.lit_lbctrl M run hv)

theorem refLit_lbCtrls : forbiddenRef Lit.lbCtrls :=
  forbid_of_lit Lit.lbCtrls (by decide +kernel) (s := 4) (by decide +kernel) (by decide)
    (fun ob _ => ¬ (ob 0 0 = some 1 ∧ ob 1 0 = some 1)) (fun M run hv _ => PF.lit_lbctrl M run hv)
    (fun chs ν g trs hE hr hout hQ => by
      have H : (OC.and (.reg 0 5 1) (.reg 1 5 1)).eval (finalReg trs ν) (finalByte (conc Lit.lbCtrls trs ν g)) = true := hout
      simp only [oc_and_iff] at H
      obtain ⟨e0, e1⟩ := H
      exact hQ ⟨(obsReg4 (by decide +kernel) (by decide +kernel) hE hr (r := 5) (by decide +kernel) (by decide) _).2 e0,
        (obsReg4 (by decide +kernel) (by decide +kernel) hE hr (r := 5) (by decide +kernel) (by decide) _).2 e1⟩)

theorem refLit_lbCtrls_agrees : refLit_lbCtrls = Lit.ref_lbCtrls := rfl

/-! ## `oota42` -/

theorem refFromLit_oota42 : ∀ chs ν g, progExec Lit.oota42 chs ν g → ∀ trs, Lit.oota42.runAll chs = some trs →
    ¬ (refObsLoad (conc Lit.oota42 trs ν g) 0 0 = some 42 ∧ refObsLoad (conc Lit.oota42 trs ν g) 1 0 = some 42) :=
  refFromLit Lit.oota42 (by decide +kernel) (s := 4) (by decide +kernel) (by decide)
    (fun ob _ => ¬ (ob 0 0 = some 42 ∧ ob 1 0 = some 42)) (fun M run hv _ => PF.lit_oota42 M run hv)

theorem refLit_oota42 : forbiddenRef Lit.oota42 :=
  forbid_of_lit Lit.oota42 (by decide +kernel) (s := 4) (by decide +kernel) (by decide)
    (fun ob _ => ¬ (ob 0 0 = some 42 ∧ ob 1 0 = some 42)) (fun M run hv _ => PF.lit_oota42 M run hv)
    (fun chs ν g trs hE hr hout hQ => by
      have H : (OC.and (.reg 0 5 42) (.reg 1 5 42)).eval (finalReg trs ν) (finalByte (conc Lit.oota42 trs ν g)) = true := hout
      simp only [oc_and_iff] at H
      obtain ⟨e0, e1⟩ := H
      exact hQ ⟨(obsReg4 (by decide +kernel) (by decide +kernel) hE hr (r := 5) (by decide +kernel) (by decide) _).2 e0,
        (obsReg4 (by decide +kernel) (by decide +kernel) hE hr (r := 5) (by decide +kernel) (by decide) _).2 e1⟩)

theorem refLit_oota42_agrees : refLit_oota42 = Lit.ref_oota42 := rfl

/-! ## `mpFF` -/

theorem refFromLit_mpFF : ∀ chs ν g, progExec Lit.mpFF chs ν g → ∀ trs, Lit.mpFF.runAll chs = some trs →
    ¬ (refObsLoad (conc Lit.mpFF trs ν g) 1 0 = some 1 ∧ refObsLoad (conc Lit.mpFF trs ν g) 1 1 = some 0) :=
  refFromLit Lit.mpFF (by decide +kernel) (s := 4) (by decide +kernel) (by decide)
    (fun ob _ => ¬ (ob 1 0 = some 1 ∧ ob 1 1 = some 0)) (fun M run hv _ => PF.lit_mpFF M run hv)

theorem refLit_mpFF : forbiddenRef Lit.mpFF :=
  forbid_of_lit Lit.mpFF (by decide +kernel) (s := 4) (by decide +kernel) (by decide)
    (fun ob _ => ¬ (ob 1 0 = some 1 ∧ ob 1 1 = some 0)) (fun M run hv _ => PF.lit_mpFF M run hv)
    (fun chs ν g trs hE hr hout hQ => by
      have H : (OC.and (.reg 1 5 1) (.reg 1 7 0)).eval (finalReg trs ν) (finalByte (conc Lit.mpFF trs ν g)) = true := hout
      simp only [oc_and_iff] at H
      obtain ⟨e0, e1⟩ := H
      exact hQ ⟨(obsReg4 (by decide +kernel) (by decide +kernel) hE hr (r := 5) (by decide +kernel) (by decide) _).2 e0,
        (obsReg4 (by decide +kernel) (by decide +kernel) hE hr (r := 7) (by decide +kernel) (by decide) _).2 e1⟩)

theorem refLit_mpFF_agrees : refLit_mpFF = Lit.ref_mpFF := rfl

/-! ## `mpFFrr` -/

theorem refFromLit_mpFFrr : ∀ chs ν g, progExec Lit.mpFFrr chs ν g → ∀ trs, Lit.mpFFrr.runAll chs = some trs →
    ¬ (refObsLoad (conc Lit.mpFFrr trs ν g) 1 0 = some 1 ∧ refObsLoad (conc Lit.mpFFrr trs ν g) 1 1 = some 0) :=
  refFromLit Lit.mpFFrr (by decide +kernel) (s := 4) (by decide +kernel) (by decide)
    (fun ob _ => ¬ (ob 1 0 = some 1 ∧ ob 1 1 = some 0)) (fun M run hv _ => PF.lit_mpFFrr M run hv)

theorem refLit_mpFFrr : forbiddenRef Lit.mpFFrr :=
  forbid_of_lit Lit.mpFFrr (by decide +kernel) (s := 4) (by decide +kernel) (by decide)
    (fun ob _ => ¬ (ob 1 0 = some 1 ∧ ob 1 1 = some 0)) (fun M run hv _ => PF.lit_mpFFrr M run hv)
    (fun chs ν g trs hE hr hout hQ => by
      have H : (OC.and (.reg 1 5 1) (.reg 1 7 0)).eval (finalReg trs ν) (finalByte (conc Lit.mpFFrr trs ν g)) = true := hout
      simp only [oc_and_iff] at H
      obtain ⟨e0, e1⟩ := H
      exact hQ ⟨(obsReg4 (by decide +kernel) (by decide +kernel) hE hr (r := 5) (by decide +kernel) (by decide) _).2 e0,
        (obsReg4 (by decide +kernel) (by decide +kernel) hE hr (r := 7) (by decide +kernel) (by decide) _).2 e1⟩)

theorem refLit_mpFFrr_agrees : refLit_mpFFrr = Lit.ref_mpFFrr := rfl

/-! ## `mpFAddr` -/

theorem refFromLit_mpFAddr : ∀ chs ν g, progExec Lit.mpFAddr chs ν g → ∀ trs, Lit.mpFAddr.runAll chs = some trs →
    ¬ (refObsLoad (conc Lit.mpFAddr trs ν g) 1 0 = some 1 ∧ refObsLoad (conc Lit.mpFAddr trs ν g) 1 1 = some 0) :=
  refFromLit Lit.mpFAddr (by decide +kernel) (s := 4) (by decide +kernel) (by decide)
    (fun ob _ => ¬ (ob 1 0 = some 1 ∧ ob 1 1 = some 0)) (fun M run hv _ => PF.lit_mpFAddr M run hv)

theorem refLit_mpFAddr : forbiddenRef Lit.mpFAddr :=
  forbid_of_lit Lit.mpFAddr (by decide +kernel) (s := 4) (by decide +kernel) (by decide)
    (fun ob _ => ¬ (ob 1 0 = some 1 ∧ ob 1 1 = some 0)) (fun M run hv _ => PF.lit_mpFAddr M run hv)
    (fun chs ν g trs hE hr hout hQ => by
      have H : (OC.and (.reg 1 5 1) (.reg 1 8 0)).eval (finalReg trs ν) (finalByte (conc Lit.mpFAddr trs ν g)) = true := hout
      simp only [oc_and_iff] at H
      obtain ⟨e0, e1⟩ := H
      exact hQ ⟨(obsReg4 (by decide +kernel) (by decide +kernel) hE hr (r := 5) (by decide +kernel) (by decide) _).2 e0,
        (obsReg4 (by decide +kernel) (by decide +kernel) hE hr (r := 8) (by decide +kernel) (by decide) _).2 e1⟩)

theorem refLit_mpFAddr_agrees : refLit_mpFAddr = Lit.ref_mpFAddr := rfl

/-! ## `sbFF` -/

theorem refFromLit_sbFF : ∀ chs ν g, progExec Lit.sbFF chs ν g → ∀ trs, Lit.sbFF.runAll chs = some trs →
    ¬ (refObsLoad (conc Lit.sbFF trs ν g) 0 0 = some 0 ∧ refObsLoad (conc Lit.sbFF trs ν g) 1 0 = some 0) :=
  refFromLit Lit.sbFF (by decide +kernel) (s := 4) (by decide +kernel) (by decide)
    (fun ob _ => ¬ (ob 0 0 = some 0 ∧ ob 1 0 = some 0)) (fun M run hv _ => PF.lit_sbFF M run hv)

theorem refLit_sbFF : forbiddenRef Lit.sbFF :=
  forbid_of_lit Lit.sbFF (by decide +kernel) (s := 4) (by decide +kernel) (by decide)
    (fun ob _ => ¬ (ob 0 0 = some 0 ∧ ob 1 0 = some 0)) (fun M run hv _ => PF.lit_sbFF M run hv)
    (fun chs ν g trs hE hr hout hQ => by
      have H : (OC.and (.reg 0 7 0) (.reg 1 7 0)).eval (finalReg trs ν) (finalByte (conc Lit.sbFF trs ν g)) = true := hout
      simp only [oc_and_iff] at H
      obtain ⟨e0, e1⟩ := H
      exact hQ ⟨(obsReg4 (by decide +kernel) (by decide +kernel) hE hr (r := 7) (by decide +kernel) (by decide) _).2 e0,
        (obsReg4 (by decide +kernel) (by decide +kernel) hE hr (r := 7) (by decide +kernel) (by decide) _).2 e1⟩)

theorem refLit_sbFF_agrees : refLit_sbFF = Lit.ref_sbFF := rfl

/-! ## `isa2F` -/

theorem refFromLit_isa2F : ∀ chs ν g, progExec Lit.isa2F chs ν g → ∀ trs, Lit.isa2F.runAll chs = some trs →
    ¬ (refObsLoad (conc Lit.isa2F trs ν g) 1 0 = some 1 ∧ refObsLoad (conc Lit.isa2F trs ν g) 2 0 = some 1 ∧ refObsLoad (conc Lit.isa2F trs ν g) 2 1 = some 0) :=
  refFromLit Lit.isa2F (by decide +kernel) (s := 4) (by decide +kernel) (by decide)
    (fun ob _ => ¬ (ob 1 0 = some 1 ∧ ob 2 0 = some 1 ∧ ob 2 1 = some 0)) (fun M run hv _ => PF.lit_isa2F M run hv)

theorem refLit_isa2F : forbiddenRef Lit.isa2F :=
  forbid_of_lit Lit.isa2F (by decide +kernel) (s := 4) (by decide +kernel) (by decide)
    (fun ob _ => ¬ (ob 1 0 = some 1 ∧ ob 2 0 = some 1 ∧ ob 2 1 = some 0)) (fun M run hv _ => PF.lit_isa2F M run hv)
    (fun chs ν g trs hE hr hout hQ => by
      have H : (OC.and (.reg 1 5 1) (.and (.reg 2 5 1) (.reg 2 7 0))).eval (finalReg trs ν) (finalByte (conc Lit.isa2F trs ν g)) = true := hout
      simp only [oc_and_iff] at H
      obtain ⟨e0, e1, e2⟩ := H
      exact hQ ⟨(obsReg4 (by decide +kernel) (by decide +kernel) hE hr (r := 5) (by decide +kernel) (by decide) _).2 e0,
        (obsReg4 (by decide +kernel) (by decide +kernel) hE hr (r := 5) (by decide +kernel) (by decide) _).2 e1,
        (obsReg4 (by decide +kernel) (by decide +kernel) hE hr (r := 7) (by decide +kernel) (by decide) _).2 e2⟩)

theorem refLit_isa2F_agrees : refLit_isa2F = Lit.ref_isa2F := rfl

/-! ## `wrcF` -/

theorem refFromLit_wrcF : ∀ chs ν g, progExec Lit.wrcF chs ν g → ∀ trs, Lit.wrcF.runAll chs = some trs →
    ¬ (refObsLoad (conc Lit.wrcF trs ν g) 1 0 = some 1 ∧ refObsLoad (conc Lit.wrcF trs ν g) 2 0 = some 1 ∧ refObsLoad (conc Lit.wrcF trs ν g) 2 1 = some 0) :=
  refFromLit Lit.wrcF (by decide +kernel) (s := 4) (by decide +kernel) (by decide)
    (fun ob _ => ¬ (ob 1 0 = some 1 ∧ ob 2 0 = some 1 ∧ ob 2 1 = some 0)) (fun M run hv _ => PF.lit_wrcF M run hv)

theorem refLit_wrcF : forbiddenRef Lit.wrcF :=
  forbid_of_lit Lit.wrcF (by decide +kernel) (s := 4) (by decide +kernel) (by decide)
    (fun ob _ => ¬ (ob 1 0 = some 1 ∧ ob 2 0 = some 1 ∧ ob 2 1 = some 0)) (fun M run hv _ => PF.lit_wrcF M run hv)
    (fun chs ν g trs hE hr hout hQ => by
      have H : (OC.and (.reg 1 5 1) (.and (.reg 2 5 1) (.reg 2 7 0))).eval (finalReg trs ν) (finalByte (conc Lit.wrcF trs ν g)) = true := hout
      simp only [oc_and_iff] at H
      obtain ⟨e0, e1, e2⟩ := H
      exact hQ ⟨(obsReg4 (by decide +kernel) (by decide +kernel) hE hr (r := 5) (by decide +kernel) (by decide) _).2 e0,
        (obsReg4 (by decide +kernel) (by decide +kernel) hE hr (r := 5) (by decide +kernel) (by decide) _).2 e1,
        (obsReg4 (by decide +kernel) (by decide +kernel) hE hr (r := 7) (by decide +kernel) (by decide) _).2 e2⟩)

theorem refLit_wrcF_agrees : refLit_wrcF = Lit.ref_wrcF := rfl

/-! ## `iriwF` -/

theorem refFromLit_iriwF : ∀ chs ν g, progExec Lit.iriwF chs ν g → ∀ trs, Lit.iriwF.runAll chs = some trs →
    ¬ (refObsLoad (conc Lit.iriwF trs ν g) 1 0 = some 1 ∧ refObsLoad (conc Lit.iriwF trs ν g) 1 1 = some 0 ∧ refObsLoad (conc Lit.iriwF trs ν g) 3 0 = some 1 ∧ refObsLoad (conc Lit.iriwF trs ν g) 3 1 = some 0) :=
  refFromLit Lit.iriwF (by decide +kernel) (s := 4) (by decide +kernel) (by decide)
    (fun ob _ => ¬ (ob 1 0 = some 1 ∧ ob 1 1 = some 0 ∧ ob 3 0 = some 1 ∧ ob 3 1 = some 0)) (fun M run hv _ => PF.lit_iriwF M run hv)

theorem refLit_iriwF : forbiddenRef Lit.iriwF :=
  forbid_of_lit Lit.iriwF (by decide +kernel) (s := 4) (by decide +kernel) (by decide)
    (fun ob _ => ¬ (ob 1 0 = some 1 ∧ ob 1 1 = some 0 ∧ ob 3 0 = some 1 ∧ ob 3 1 = some 0)) (fun M run hv _ => PF.lit_iriwF M run hv)
    (fun chs ν g trs hE hr hout hQ => by
      have H : (OC.and (.reg 1 5 1) (.and (.reg 1 7 0) (.and (.reg 3 5 1) (.reg 3 7 0)))).eval (finalReg trs ν) (finalByte (conc Lit.iriwF trs ν g)) = true := hout
      simp only [oc_and_iff] at H
      obtain ⟨e0, e1, e2, e3⟩ := H
      exact hQ ⟨(obsReg4 (by decide +kernel) (by decide +kernel) hE hr (r := 5) (by decide +kernel) (by decide) _).2 e0,
        (obsReg4 (by decide +kernel) (by decide +kernel) hE hr (r := 7) (by decide +kernel) (by decide) _).2 e1,
        (obsReg4 (by decide +kernel) (by decide +kernel) hE hr (r := 5) (by decide +kernel) (by decide) _).2 e2,
        (obsReg4 (by decide +kernel) (by decide +kernel) hE hr (r := 7) (by decide +kernel) (by decide) _).2 e3⟩)

theorem refLit_iriwF_agrees : refLit_iriwF = Lit.ref_iriwF := rfl

/-! ## `datarfi` -/

theorem refFromLit_datarfi : ∀ chs ν g, progExec Lit.datarfi chs ν g → ∀ trs, Lit.datarfi.runAll chs = some trs →
    ¬ (refObsLoad (conc Lit.datarfi trs ν g) 1 0 = some 1 ∧ refObsLoad (conc Lit.datarfi trs ν g) 1 2 = some 0) :=
  refFromLit Lit.datarfi (by decide +kernel) (s := 4) (by decide +kernel) (by decide)
    (fun ob _ => ¬ (ob 1 0 = some 1 ∧ ob 1 2 = some 0)) (fun M run hv _ => PF.lit_datarfi M run hv)

theorem refLit_datarfi : forbiddenRef Lit.datarfi :=
  forbid_of_lit Lit.datarfi (by decide +kernel) (s := 4) (by decide +kernel) (by decide)
    (fun ob _ => ¬ (ob 1 0 = some 1 ∧ ob 1 2 = some 0)) (fun M run hv _ => PF.lit_datarfi M run hv)
    (fun chs ν g trs hE hr hout hQ => by
      have H : (OC.and (.reg 1 10 1) (.reg 1 13 0)).eval (finalReg trs ν) (finalByte (conc Lit.datarfi trs ν g)) = true := hout
      simp only [oc_and_iff] at H
      obtain ⟨e0, e1⟩ := H
      exact hQ ⟨(obsReg4 (by decide +kernel) (by decide +kernel) hE hr (r := 10) (by decide +kernel) (by decide) _).2 e0,
        (obsReg4 (by decide +kernel) (by decide +kernel) hE hr (r := 13) (by decide +kernel) (by decide) _).2 e1⟩)

theorem refLit_datarfi_agrees : refLit_datarfi = Lit.ref_datarfi := rfl

/-! ## `addrpo` -/

theorem refFromLit_addrpo : ∀ chs ν g, progExec Lit.addrpo chs ν g → ∀ trs, Lit.addrpo.runAll chs = some trs →
    ¬ (refObsLoad (conc Lit.addrpo trs ν g) 0 0 = some 1 ∧ refObsLoad (conc Lit.addrpo trs ν g) 1 0 = some Z) :=
  refFromLit Lit.addrpo (by decide +kernel) (s := 4) (by decide +kernel) (by decide)
    (fun ob _ => ¬ (ob 0 0 = some 1 ∧ ob 1 0 = some Z)) (fun M run hv _ => PF.lit_addrpo M run hv)

theorem refLit_addrpo : forbiddenRef Lit.addrpo :=
  forbid_of_lit Lit.addrpo (by decide +kernel) (s := 4) (by decide +kernel) (by decide)
    (fun ob _ => ¬ (ob 0 0 = some 1 ∧ ob 1 0 = some Z)) (fun M run hv _ => PF.lit_addrpo M run hv)
    (fun chs ν g trs hE hr hout hQ => by
      have H : (OC.and (.reg 0 10 1) (.reg 1 11 Z)).eval (finalReg trs ν) (finalByte (conc Lit.addrpo trs ν g)) = true := hout
      simp only [oc_and_iff] at H
      obtain ⟨e0, e1⟩ := H
      exact hQ ⟨(obsReg4 (by decide +kernel) (by decide +kernel) hE hr (r := 10) (by decide +kernel) (by decide) _).2 e0,
        (obsReg4 (by decide +kernel) (by decide +kernel) hE hr (r := 11) (by decide +kernel) (by decide) _).2 e1⟩)

theorem refLit_addrpo_agrees : refLit_addrpo = Lit.ref_addrpo := rfl

/-! ## `coRR2` -/

theorem refFromLit_coRR2 : ∀ chs ν g, progExec Lit.coRR2 chs ν g → ∀ trs, Lit.coRR2.runAll chs = some trs →
    ¬ (refObsLoad (conc Lit.coRR2 trs ν g) 2 0 = some 1 ∧ refObsLoad (conc Lit.coRR2 trs ν g) 2 1 = some 2 ∧ refObsLoad (conc Lit.coRR2 trs ν g) 3 0 = some 2 ∧ refObsLoad (conc Lit.coRR2 trs ν g) 3 1 = some 1) :=
  refFromLit Lit.coRR2 (by decide +kernel) (s := 4) (by decide +kernel) (by decide)
    (fun ob _ => ¬ (ob 2 0 = some 1 ∧ ob 2 1 = some 2 ∧ ob 3 0 = some 2 ∧ ob 3 1 = some 1)) (fun M run hv _ => PF.lit_coRR2 M run hv)

theorem refLit_coRR2 : forbiddenRef Lit.coRR2 :=
  forbid_of_lit Lit.coRR2 (by decide +kernel) (s := 4) (by decide +kernel) (by decide)
    (fun ob _ => ¬ (ob 2 0 = some 1 ∧ ob 2 1 = some 2 ∧ ob 3 0 = some 2 ∧ ob 3 1 = some 1)) (fun M run hv _ => PF.lit_coRR2 M run hv)
    (fun chs ν g trs hE hr hout hQ => by
      have H : (OC.and (.reg 2 10 1) (.and (.reg 2 11 2) (.and (.reg 3 10 2) (.reg 3 11 1)))).eval (finalReg trs ν) (finalByte (conc Lit.coRR2 trs ν g)) = true := hout
      simp only [oc_and_iff] at H
      obtain ⟨e0, e1, e2, e3⟩ := H
      exact hQ ⟨(obsReg4 (by decide +kernel) (by decide +kernel) hE hr (r := 10) (by decide +kernel) (by decide) _).2 e0,
        (obsReg4 (by decide +kernel) (by decide +kernel) hE hr (r := 11) (by decide +kernel) (by decide) _).2 e1,
        (obsReg4 (by decide +kernel) (by decide +kernel) hE hr (r := 10) (by decide +kernel) (by decide) _).2 e2,
        (obsReg4 (by decide +kernel) (by decide +kernel) hE hr (r := 11) (by decide +kernel) (by decide) _).2 e3⟩)

theorem refLit_coRR2_agrees : refLit_coRR2 = Lit.ref_coRR2 := rfl

/-! ## `w22F` (2+2W+fence.w.ws): final memory, both storing harts finished -/

theorem refFromLit_w22F : ∀ chs ν g, progExec Lit.w22F chs ν g → ∀ trs, Lit.w22F.runAll chs = some trs →
    ¬ (refFinalMem (conc Lit.w22F trs ν g) X 4 = 2 ∧ refFinalMem (conc Lit.w22F trs ν g) Y 4 = 2) :=
  refFromLit Lit.w22F (by decide +kernel) (s := 4) (by decide +kernel) (by decide)
    (fun _ fm => ¬ (fm X 4 = 2 ∧ fm Y 4 = 2))
    (fun M run hv hd => PF.lit_w22F M run hv (hd 0 (by decide)) (hd 1 (by decide)))

theorem refLit_w22F : forbiddenRef Lit.w22F :=
  forbid_of_lit Lit.w22F (by decide +kernel) (s := 4) (by decide +kernel) (by decide)
    (fun _ fm => ¬ (fm X 4 = 2 ∧ fm Y 4 = 2))
    (fun M run hv hd => PF.lit_w22F M run hv (hd 0 (by decide)) (hd 1 (by decide)))
    (fun chs ν g trs hE hr hout hQ => by
      have H : (OC.and (.mem X 4 2) (.mem Y 4 2)).eval (finalReg trs ν) (finalByte (conc Lit.w22F trs ν g)) =
        true := hout
      obtain ⟨e0, e1⟩ := oc_and_iff.1 H
      exact hQ ⟨(oc_mem_iff (by decide)).1 e0, (oc_mem_iff (by decide)).1 e1⟩)

theorem refLit_w22F_agrees : refLit_w22F = Lit.ref_w22F := rfl

/-! ## `coWW` (CoWW): the final value, the storing hart finished -/

theorem refFromLit_coWW : ∀ chs ν g, progExec Lit.coWW chs ν g → ∀ trs, Lit.coWW.runAll chs = some trs →
    refFinalMem (conc Lit.coWW trs ν g) X 4 = 2 :=
  refFromLit Lit.coWW (by decide +kernel) (s := 4) (by decide +kernel) (by decide)
    (fun _ fm => fm X 4 = 2) (fun M run hv hd => PF.lit_coWW M run hv (hd 0 (by decide)))

theorem refLit_coWW : forbiddenRef Lit.coWW :=
  forbid_of_lit Lit.coWW (by decide +kernel) (s := 4) (by decide +kernel) (by decide)
    (fun _ fm => fm X 4 = 2) (fun M run hv hd => PF.lit_coWW M run hv (hd 0 (by decide)))
    (fun chs ν g trs hE hr hout hQ => by
      have H : (OC.not (.mem X 4 2)).eval (finalReg trs ν) (finalByte (conc Lit.coWW trs ν g)) = true := hout
      exact oc_not_iff.1 H ((oc_mem_iff (by decide)).2 hQ))

theorem refLit_coWW_agrees : refLit_coWW = Lit.ref_coWW := rfl

/-! ## `coWR` (HAND/CoWR, doublewords) -/

theorem refFromLit_coWR : ∀ chs ν g, progExec Lit.coWR chs ν g → ∀ trs, Lit.coWR.runAll chs = some trs →
    ¬ (refFinalMem (conc Lit.coWR trs ν g) X 8 = 1 ∧ refObsLoad (conc Lit.coWR trs ν g) 0 0 = some 2) :=
  refFromLit Lit.coWR (by decide +kernel) (s := 8) (by decide +kernel) (by decide)
    (fun ob fm => ¬ (fm X 8 = 1 ∧ ob 0 0 = some 2)) (fun M run hv _ => PF.lit_coWR M run hv)

theorem refLit_coWR : forbiddenRef Lit.coWR :=
  forbid_of_lit Lit.coWR (by decide +kernel) (s := 8) (by decide +kernel) (by decide)
    (fun ob fm => ¬ (fm X 8 = 1 ∧ ob 0 0 = some 2)) (fun M run hv _ => PF.lit_coWR M run hv)
    (fun chs ν g trs hE hr hout hQ => by
      have H : (OC.and (.mem X 8 1) (.reg 0 7 2)).eval (finalReg trs ν) (finalByte (conc Lit.coWR trs ν g)) =
        true := hout
      obtain ⟨e0, e1⟩ := oc_and_iff.1 H
      exact hQ ⟨(oc_mem_iff (by decide)).1 e0,
        (obsReg8 (by decide +kernel) (by decide +kernel) hE hr (r := 7) (by decide +kernel) (by decide) _).2 e1⟩)

theorem refLit_coWR_agrees : refLit_coWR = Lit.ref_coWR := rfl

/-! ## `coWR0` (CO/CoWR0): the load never returns the image's 0 -/

theorem refFromLit_coWR0 : ∀ chs ν g, progExec Lit.coWR0 chs ν g → ∀ trs, Lit.coWR0.runAll chs = some trs →
    ¬ refObsLoad (conc Lit.coWR0 trs ν g) 0 0 = some 0 :=
  refFromLit Lit.coWR0 (by decide +kernel) (s := 4) (by decide +kernel) (by decide)
    (fun ob _ => ¬ ob 0 0 = some 0) (fun M run hv _ => PF.lit_coWR0 M run hv)

theorem refChk_coWR0 : ∀ chs ν g, progExec Lit.coWR0 chs ν g → ∀ trs, Lit.coWR0.runAll chs = some trs →
    ¬ refObsLoad (conc Lit.coWR0 trs ν g) 0 0 = some 0 :=
  refChk Lit.coWR0 Lit.ref_coWR0 (fun ob _ => ob 0 0 = some 0) (fun chs ν g trs hE hr hR => by
    have e0 : finalReg trs ν 0 7 = 0 := oc_reg (by decide) ((obsReg4 (by decide +kernel) (by decide +kernel) hE hr
      (r := 7) (by decide +kernel) (by decide) (finalByte (conc Lit.coWR0 trs ν g))).1 hR)
    show (OC.not (.and (.reg 0 7 1) (.mem X 4 1))).eval (finalReg trs ν) (finalByte (conc Lit.coWR0 trs ν g)) = true
    exact oc_not_iff.2 (fun H => by have := oc_reg (by decide) (oc_and_iff.1 H).1; omega))

theorem refFromLit_coWR0_agrees : refFromLit_coWR0 = refChk_coWR0 := rfl

/-! ## `coRW1` (CO/CoRW1): the load never returns its own po-later store -/

theorem refFromLit_coRW1 : ∀ chs ν g, progExec Lit.coRW1 chs ν g → ∀ trs, Lit.coRW1.runAll chs = some trs →
    ¬ refObsLoad (conc Lit.coRW1 trs ν g) 0 0 = some 1 :=
  refFromLit Lit.coRW1 (by decide +kernel) (s := 4) (by decide +kernel) (by decide)
    (fun ob _ => ¬ ob 0 0 = some 1) (fun M run hv _ => PF.lit_coRW1 M run hv)

theorem refChk_coRW1 : ∀ chs ν g, progExec Lit.coRW1 chs ν g → ∀ trs, Lit.coRW1.runAll chs = some trs →
    ¬ refObsLoad (conc Lit.coRW1 trs ν g) 0 0 = some 1 :=
  refChk Lit.coRW1 Lit.ref_coRW1 (fun ob _ => ob 0 0 = some 1) (fun chs ν g trs hE hr hR => by
    have e0 : finalReg trs ν 0 5 = 1 := oc_reg (by decide) ((obsReg4 (by decide +kernel) (by decide +kernel) hE hr
      (r := 5) (by decide +kernel) (by decide) (finalByte (conc Lit.coRW1 trs ν g))).1 hR)
    show (OC.not (.and (.reg 0 5 0) (.mem X 4 1))).eval (finalReg trs ν) (finalByte (conc Lit.coRW1 trs ν g)) = true
    exact oc_not_iff.2 (fun H => by have := oc_reg (by decide) (oc_and_iff.1 H).1; omega))

theorem refFromLit_coRW1_agrees : refFromLit_coRW1 = refChk_coRW1 := rfl

/-! ## `coRW2` (CO/CoRW2): H1 read H0's store, yet its own store is not co-after it -/

theorem refFromLit_coRW2 : ∀ chs ν g, progExec Lit.coRW2 chs ν g → ∀ trs, Lit.coRW2.runAll chs = some trs →
    ¬ (refObsLoad (conc Lit.coRW2 trs ν g) 1 0 = some 1 ∧ refFinalMem (conc Lit.coRW2 trs ν g) X 4 = 1) :=
  refFromLit Lit.coRW2 (by decide +kernel) (s := 4) (by decide +kernel) (by decide)
    (fun ob fm => ¬ (ob 1 0 = some 1 ∧ fm X 4 = 1)) (fun M run hv hd => PF.lit_coRW2 M run hv (hd 1 (by decide)))

theorem refChk_coRW2 : ∀ chs ν g, progExec Lit.coRW2 chs ν g → ∀ trs, Lit.coRW2.runAll chs = some trs →
    ¬ (refObsLoad (conc Lit.coRW2 trs ν g) 1 0 = some 1 ∧ refFinalMem (conc Lit.coRW2 trs ν g) X 4 = 1) :=
  refChk Lit.coRW2 Lit.ref_coRW2 (fun ob fm => ob 1 0 = some 1 ∧ fm X 4 = 1) (fun chs ν g trs hE hr hR => by
    have e0 : finalReg trs ν 1 5 = 1 := oc_reg (by decide) ((obsReg4 (by decide +kernel) (by decide +kernel) hE hr
      (r := 5) (by decide +kernel) (by decide) (finalByte (conc Lit.coRW2 trs ν g))).1 hR.1)
    have e1 := hR.2
    show (OC.not (.or (.and (.reg 1 5 0) (.or (.mem X 4 2) (.mem X 4 1))) (.and (.reg 1 5 1) (.mem X 4 2)))).eval
      (finalReg trs ν) (finalByte (conc Lit.coRW2 trs ν g)) = true
    refine oc_not_iff.2 (fun H => ?_)
    rcases oc_or_iff.1 H with H1 | H2
    · have := oc_reg (by decide) (oc_and_iff.1 H1).1; omega
    · have := (oc_mem_iff (by decide)).1 (oc_and_iff.1 H2).2; omega)

theorem refFromLit_coRW2_agrees : refFromLit_coRW2 = refChk_coRW2 := rfl

/-! ## `coRR` (CO/CoRR): two po-ordered loads of x see the store, then the image -/

theorem refFromLit_coRR : ∀ chs ν g, progExec Lit.coRR chs ν g → ∀ trs, Lit.coRR.runAll chs = some trs →
    ¬ (refObsLoad (conc Lit.coRR trs ν g) 1 0 = some 1 ∧ refObsLoad (conc Lit.coRR trs ν g) 1 1 = some 0) :=
  refFromLit Lit.coRR (by decide +kernel) (s := 4) (by decide +kernel) (by decide)
    (fun ob _ => ¬ (ob 1 0 = some 1 ∧ ob 1 1 = some 0)) (fun M run hv _ => PF.lit_coRR M run hv)

theorem refChk_coRR : ∀ chs ν g, progExec Lit.coRR chs ν g → ∀ trs, Lit.coRR.runAll chs = some trs →
    ¬ (refObsLoad (conc Lit.coRR trs ν g) 1 0 = some 1 ∧ refObsLoad (conc Lit.coRR trs ν g) 1 1 = some 0) :=
  refChk Lit.coRR Lit.ref_coRR (fun ob _ => ob 1 0 = some 1 ∧ ob 1 1 = some 0) (fun chs ν g trs hE hr hR => by
    have e0 : finalReg trs ν 1 5 = 1 := oc_reg (by decide) ((obsReg4 (by decide +kernel) (by decide +kernel) hE hr
      (r := 5) (by decide +kernel) (by decide) (finalByte (conc Lit.coRR trs ν g))).1 hR.1)
    have e1 : finalReg trs ν 1 7 = 0 := oc_reg (by decide) ((obsReg4 (by decide +kernel) (by decide +kernel) hE hr
      (r := 7) (by decide +kernel) (by decide) (finalByte (conc Lit.coRR trs ν g))).1 hR.2)
    show (OC.not (.and (.mem X 4 1) (.or (.and (.reg 1 5 0) (.or (.reg 1 7 0) (.reg 1 7 1)))
      (.and (.reg 1 5 1) (.reg 1 7 1))))).eval (finalReg trs ν) (finalByte (conc Lit.coRR trs ν g)) = true
    refine oc_not_iff.2 (fun H => ?_)
    rcases oc_or_iff.1 (oc_and_iff.1 H).2 with H1 | H2
    · have := oc_reg (by decide) (oc_and_iff.1 H1).1; omega
    · have := oc_reg (by decide) (oc_and_iff.1 H2).2; omega)

theorem refFromLit_coRR_agrees : refFromLit_coRR = refChk_coRR := rfl

end Weak.Prom.Cmp
