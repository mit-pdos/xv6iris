/-
Weak/Prom: **SchedAD — what carries over to the A/D variant: `own_mp` through `adequacyAV`, and row 50's negative
test** (owner ruling [OWN.P14]; brief "Show at least one existing track (a) verdict … still goes through over the
A/D variant (A/D steps possible but unused by the program), and the row-50 negative check"; plan rev 7 §3 "Test"
[R4.4(d), R5.s11], row 50 D-OOTA).

* `liftV pstep` — a machine-v2 program half on the variant's label alphabet: it emits no A/D label (A/D steps are
  in the machine, `memStepV.ad`, `cstepV.ad`, `wpAV_lift`'s A/D arm, but this program does not use them).
  `adEmit_liftV`: the adequacy's emission side condition holds vacuously.
* `noAdL_of_run`: a valid run of such a program has no A/D message (only the A/D arm fulfils one: a v2 fulfil of
  a `.cmo .clean 0` message writes no data, which `msgOk` forbids for a length-0 block).  Hence `PO_adV`/`adExactV`
  hold, `fOkV ↔ fOk`, `ownDoneV = ownDone` (the variant's fetch arm IS v2's) and `memStepV (.v l) ↔ memStep l`.
* `validRunV_toV2`: such a run IS a valid machine-v2 run with the same final configuration and projected traces.
* `wpA_wpAV`: THE HART PROOFS CARRY OVER — every v2 wp `wpA` (OwnAWp.lean) of an A/D-free program entails the
  variant's `wpAV` (Löb induction over the two languages' steps; the state interpretations agree when `M` has no
  A/D message).  `premiseV_of`: a v2 adequacy premise (`wpPremise`) gives the variant's (`wpPremiseV`).
* `own_mpAD`: G4 (2)'s verdict over EVERY valid run of the A/D variant, proved by `adequacyAV` from the unchanged
  `mp_premise` (OwnAMP.lean).  `own_mpAD_run` is the same verdict through `validRunV_toV2` and `own_mp` (a check).
* `row50_neg`: `¬ PO_adV proto₅₀ img₅₀ M₅₀` (plan §3 "Test": "for proto_p := 'D clear' and row 50's M (message 1
  is `WCad`, `Valid(0)` holds, `val M[1] = adUpd (memAt 0 p) = P|D`, which is not D-clear)").  With the variant's
  `isAdV` the lemma carries over; with machine v2's constantly-false `PMsg.isAd` it would not (`row50_v2_vacuous`:
  v2's `PO_ad` holds of the same data).
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Prom.OwnAAdAdeq
import Weak.Prom.OwnAMP

namespace Weak.Prom.OAd

open MachCSL MachCSL.Stdpp Iris.Std
open Weak (Image Dsrc)
open Weak.Prom Weak.Prom.PF Weak.Prom.OA Weak.Prom.Mach Weak.Prom.Mach.Cert
open PLabel
open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode

variable {P D V : Type} {hlc : HasLC}

/-! ## 1. A/D-free program halves and their runs -/

/-- A machine-v2 program half over the variant's labels: it emits no A/D label. -/
def liftV (pstep : P → D → PLabel → P → D → Prop) : P → D → Ad.VLabel → P → D → Prop
  | s, d, .v l, s', d' => pstep s d l s' d'
  | _, _, .ad _ _ _, _, _ => False

theorem adEmit_liftV (pstep : P → Unit → PLabel → P → Unit → Prop) : adEmit (liftV pstep) :=
  fun _ _ _ _ _ h => h.elim

/-- No A/D message in `M`. -/
abbrev noAdL (M : List PMsg) : Prop := ∀ (k : Nat) (m : PMsg), M[k]? = some m → m.cls ≠ PClass.ad

theorem noAdL_adAt {M : List PMsg} (h : noAdL M) (t : Nat) : ¬ Ad.adAt M t := fun ⟨m, hm, hc⟩ => h _ m hm hc

theorem noAdL_msg {M : List PMsg} (h : noAdL M) {t : Nat} {m : PMsg} (hm : msgAt M t = some m) : ¬ isAdV m := by
  cases t with
  | zero => cases hm
  | succ k => exact h k m hm

theorem noAdL_PO {π : Proto} {img : Image} {M : List PMsg} (h : noAdL M) : PO_adV π img M :=
  fun _ _ _ _ hm hc => (noAdL_msg h hm hc).elim

theorem noAdL_ex {img : Image} {M : List PMsg} (h : noAdL M) : adExactV img M :=
  fun _ _ _ _ hm hc => (noAdL_msg h hm hc).elim

theorem fOkV_iff {M : List PMsg} {σ : CSt} {h : Nat} (hna : noAdL M) : fOkV M σ h ↔ fOk M σ h := by
  unfold fOkV fOk stageGeV stageGe
  exact ⟨fun H t a b c => H t a b c (noAdL_adAt hna t), fun H t a b c _ => H t a b c⟩

/-- Without A/D messages the variant's fetch exemption is v2's. -/
theorem ownDoneV_eq {log : List PMsg} (hna : noAdL log) (i : Nat) (prom : GSet Nat) (t : Nat) :
    Ad.ownDoneV log i prom t = ownDone log i prom t := by
  unfold Ad.ownDoneV
  cases h : log[t - 1]? with
  | none => simp [ownDone, h]
  | some m => simp [hna _ _ h]

/-- Without A/D messages a v2-label step of the variant is a machine-v2 step. -/
theorem memStepV_toV2 {img : Image} {log : List PMsg} {i : Nat} {prom : GSet Nat} {ws : PState} {l : PLabel}
    {ots : Option Nat} {ws' : PState} {prom' : GSet Nat} (hna : noAdL log)
    (h : Ad.memStepV img log i prom ws (.v l) ots ws' prom') : memStep img log i prom ws l ots ws' prom' := by
  by_cases hf : Nfr.F.isFetch l
  · obtain ⟨b, tvs, rfl⟩ := hf
    obtain ⟨hok, hots, hws, hpr⟩ := Ad.memStepV_fetch_inv h
    rw [hots, hws, hpr]
    have e : Ad.fetchPostV log i prom ws b tvs = { ws with
        wIfr := max ws.wIfr (bytesMax (fun _ t => t) b tvs)
        wIfv := max ws.wIfv (fetchView log i prom b tvs) } := by
      simp only [Ad.fetchPostV, Ad.fetchViewV, fetchView, ownDoneV_eq hna]
    rw [e]; exact .fetch prom ws b tvs hok
  · exact Ad.memStepV_v_inv h hf

section run

variable {pstep : P → Unit → PLabel → P → Unit → Prop} {img : Image} {ps : List P} {evs : List Ad.VEvt}
  {cfg : PCfg P Unit}

/-- A valid run of an A/D-free program half has no A/D message. -/
theorem noAdL_of_run (hv : Ad.validRunV (liftV pstep) img () ps evs cfg) : noAdL cfg.pcLog := by
  intro k m hm hc
  have hk := (List.getElem?_eq_some_iff.1 hm).1
  obtain ⟨i, _, z, l, p', ws', prom', hp, hmem, -⟩ := validRunV_fulfil hv (k + 1) (by omega) (by omega)
  cases l with
  | ad => exact hp
  | v l0 =>
    have hm2 := (Mach.memStep_msg (memStepV_v_some hmem)).1 (k + 1) rfl
    simp only [Nat.add_sub_cancel] at hm2
    rw [hm] at hm2
    have hd := labelMsg_ad hm2.symm hc
    have hwf := Ad.pmStepsV_wf hv.1 (pmInit_wf img () ps)
    rcases (hwf.2 m (List.mem_of_getElem? hm)).1 with hne | ⟨k', len, hcl, hlen⟩
    · exact hne hd
    · unfold PClass.ad at hc; rw [hc] at hcl; cases hcl; omega

/-- The machine-v2 event of a variant event (an A/D event never occurs in an A/D-free run). -/
def evV : Ad.VEvt → PEvt
  | .prom i m => .prom i m
  | .st i (.v l) o => .st i l o
  | .st i (.ad ..) o => .st i LInstr o

theorem prefix_get {L M : List PMsg} (h : L <+: M) {k : Nat} {m : PMsg} (hk : L[k]? = some m) : M[k]? = some m := by
  obtain ⟨u, rfl⟩ := h
  rw [List.getElem?_append_left (List.getElem?_eq_some_iff.1 hk).1]; exact hk

theorem runV_toV2 : ∀ {c c' : PCfg P Unit} {es : List Ad.VEvt}, Ad.pmStepsV (liftV pstep) c es c' →
    noAdL c'.pcLog → pmSteps pstep c (es.map evV) c' ∧ ∀ h, traceOf h (es.map evV) = prjT (Ad.traceOfV h es) := by
  intro c c' es hrun
  induction hrun with
  | refl => intro _; exact ⟨.refl _, fun _ => rfl⟩
  | step c0 c1 c2 e es hst hrest ih =>
    intro hna
    obtain ⟨ih1, ih2⟩ := ih hna
    have hpre : c0.pcLog <+: c2.pcLog := (Ad.pmStepV_inv hst).2.1.trans (Ad.pmStepsV_inv hrest).2.1
    have hna0 : noAdL c0.pcLog := fun k m hk => hna k m (prefix_get hpre hk)
    cases hst with
    | promise i ag m hag hnt htid =>
      exact ⟨.step _ _ _ _ _ (.promise c0 i ag m hag hnt htid) ih1, fun h => by
        simp only [List.map_cons, evV, traceOf, Ad.traceOfV]; exact ih2 h⟩
    | state i ag l ots st' d' ws' prom' hag hp hm =>
      cases l with
      | ad => exact hp.elim
      | v l0 =>
        refine ⟨.step _ _ _ _ _ (.state c0 i ag l0 ots st' d' ws' prom' hag hp (memStepV_toV2 hna0 hm)) ih1,
          fun h => ?_⟩
        simp only [List.map_cons, evV, traceOf, Ad.traceOfV]
        by_cases hih : i = h
        · simp [hih, prjT, ih2 h]
        · simp [hih, ih2 h]

/-- **AN A/D-FREE VALID RUN OF THE VARIANT IS A VALID MACHINE-v2 RUN** with the same final configuration and the
projected traces. -/
theorem validRunV_toV2 (hv : Ad.validRunV (liftV pstep) img () ps evs cfg) :
    PF.validRun pstep img () ps cfg.pcLog ⟨evs.map evV, cfg⟩ ∧
      ∀ h, traceOf h (evs.map evV) = prjT (Ad.traceOfV h evs) := by
  obtain ⟨h1, h2⟩ := runV_toV2 hv.1 (noAdL_of_run hv)
  exact ⟨⟨⟨h1, hv.2⟩, rfl⟩, h2⟩

end run

/-! ## 2. The hart proofs carry over: `wpA ⊢ wpAV` for an A/D-free program -/

section transfer

variable {GF : BundledGFunctors} [GhostVarG GF HSt] [GhostVarG GF Bool] [InvGS_gen hlc GF]

theorem si_siV {g : AGN} {π : Proto} {img img' : Image} {M M' : List PMsg} {Ψ : Nat → Trace → Prop}
    (e1 : img = img') (e2 : M = M') (hna : noAdL M) (σ : CSt) (ns : Nat) (obs : List Unit) (nt : Nat) :
    @stateInterp CSt Unit GF (aIrisGS (P := P) (D := Unit) (V := V) g π img M Ψ).toStateInterp σ ns obs nt ⊢
      @stateInterp CSt Unit GF (aIrisGSV (P := P) (D := Unit) (V := V) g π img' M' Ψ).toStateInterp σ ns obs nt := by
  subst e1 e2
  rw [aStateI_eq, aStateIV_eq]
  unfold stA stAV
  iintro ⟨Hb, %Hout, %Hok, #Hsh, Hf⟩
  iframe Hb Hf
  isplitr
  · ipureintro; exact Hout
  isplitr
  · ipureintro; exact fun k => (fOkV_iff hna).2 (Hok k)
  isplitr
  · imodintro; iintro %t %ht; iapply Hsh; ipureintro
    exact ⟨ht.1, ht.2.1, ht.2.2.resolve_right (noAdL_adAt hna t)⟩
  · ipureintro; exact ⟨noAdL_PO hna, noAdL_ex hna⟩

theorem siV_si {g : AGN} {π : Proto} {img img' : Image} {M M' : List PMsg} {Ψ : Nat → Trace → Prop}
    (e1 : img = img') (e2 : M = M') (hna : noAdL M) (σ : CSt) (ns : Nat) (obs : List Unit) (nt : Nat) :
    @stateInterp CSt Unit GF (aIrisGSV (P := P) (D := Unit) (V := V) g π img M Ψ).toStateInterp σ ns obs nt ⊢
      @stateInterp CSt Unit GF (aIrisGS (P := P) (D := Unit) (V := V) g π img' M' Ψ).toStateInterp σ ns obs nt := by
  subst e1 e2
  rw [aStateI_eq, aStateIV_eq]
  unfold stA stAV
  iintro ⟨Hb, %Hout, %Hok, #Hsh, -, Hf⟩
  iframe Hb Hf
  isplitr
  · ipureintro; exact Hout
  isplitr
  · ipureintro; exact fun k => (fOkV_iff hna).1 (Hok k)
  · imodintro; iintro %t %ht; iapply Hsh; ipureintro; exact ⟨ht.1, ht.2.1, .inl ht.2.2⟩

/-- **THE HART PROOFS CARRY OVER** (Löb induction): for an A/D-free program half, v2's `wpA` entails the variant's
`wpAV`.  Every variant step of the hart is a v2 step of it (`memStepV_toV2`, `fOkV_iff`; the A/D arm is not
emitted), and the two state interpretations agree (`si_siV`, `siV_si`). -/
theorem wpA_wpAV {g : AGN} {π : Proto} {pstep : P → Unit → PLabel → P → Unit → Prop} {pdone : P → Option V}
    {img : Image} {M : List PMsg} {h : Nat} {Ψ : Nat → Trace → Prop} {Φ : V → IProp GF} (hna : noAdL M) :
    ⊢ ∀ s, wpA g π (hw pstep pdone img M h) Ψ s Φ -∗ wpAV g π (hwV (liftV pstep) pdone img M h) Ψ s Φ := by
  iloeb as IH
  iintro %s H
  unfold wpA wpAV
  rw [(wp_unfold (ι := aIrisGS (P := P) (D := Unit) (V := V) g π (hw pstep pdone img M h).img
      (hw pstep pdone img M h).M Ψ)).to_eq,
    (wp_unfold (ι := aIrisGSV (P := P) (D := Unit) (V := V) g π (hwV (liftV pstep) pdone img M h).img
      (hwV (liftV pstep) pdone img M h).M Ψ)).to_eq]
  dsimp only [wp.pre, ToVal.toVal, CExpr.toV, CExprV.toV]
  iintro %σ₁ %ns %obs %obs' %nt Hσ
  ihave Hσ := siV_si (img := (hwV (liftV pstep) pdone img M h).img) (M := (hwV (liftV pstep) pdone img M h).M)
    (img' := (hw pstep pdone img M h).img) (M' := (hw pstep pdone img M h).M) rfl rfl hna σ₁ ns (obs ++ obs') nt $$ Hσ
  imod H $$ %σ₁ %ns %obs %obs' %nt Hσ with ⟨-, H⟩
  imodintro
  isplitr
  · ipureintro; trivial
  iintro %e₂ %σ₂ %eₜ %Hstep Hc
  change cstepV _ _ _ at Hstep
  cases Hstep with
  | lab _ _ _ l ots s' ws' pr' d d' hp hm hfok =>
    have hs : cstep (CExpr.run (hw pstep pdone img M h) s, σ₁) []
        (CExpr.run (hw pstep pdone img M h) s', updS σ₁ (hwV (liftV pstep) pdone img M h).h
          (ws', pr', (σ₁ (hwV (liftV pstep) pdone img M h).h).2.2 ++ [(l, ots)]), []) :=
      .lab _ _ _ l ots s' ws' pr' d d' hp (memStepV_toV2 hna hm) ((fOkV_iff hna).1 hfok)
    dsimp only [Nat.repeat]
    imod H $$ %_ %_ %_ %hs Hc with H
    iintro !> !>
    imod H
    iintro !>
    iapply step_fupdN_wand $$ H
    iintro >⟨Hσ2, Hw, -⟩
    imodintro
    isplitl [Hσ2]
    · iapply si_siV (img := (hw pstep pdone img M h).img) (M := (hw pstep pdone img M h).M)
        (img' := (hwV (liftV pstep) pdone img M h).img) (M' := (hwV (liftV pstep) pdone img M h).M) rfl rfl hna
      iexact Hσ2
    isplitl [Hw]
    · iapply IH $$ %s' Hw
    · exact BigSepL.bigSepL_nil_intro
  | ad _ _ _ b tvs data ots s' pr' d d' hp hm => exact hp.elim
  | fin _ _ _ v hv =>
    have hs : cstep (CExpr.run (hw pstep pdone img M h) s, σ₁) [] (CExpr.ret v, σ₁, []) := .fin _ _ _ v hv
    dsimp only [Nat.repeat]
    imod H $$ %_ %_ %_ %hs Hc with H
    iintro !> !>
    imod H
    iintro !>
    iapply step_fupdN_wand $$ H
    iintro >⟨Hσ2, Hw, -⟩
    imodintro
    isplitl [Hσ2]
    · iapply si_siV (img := (hw pstep pdone img M h).img) (M := (hw pstep pdone img M h).M)
        (img' := (hwV (liftV pstep) pdone img M h).img) (M' := (hwV (liftV pstep) pdone img M h).M) rfl rfl hna
      iexact Hσ2
    isplitl [Hw]
    · ihave Hv := (wp_value_fupd' (ι := aIrisGS (P := P) (D := Unit) (V := V) g π (hw pstep pdone img M h).img
        (hw pstep pdone img M h).M Ψ) (v := v)).1 $$ Hw
      iapply (wp_value_fupd' (ι := aIrisGSV (P := P) (D := Unit) (V := V) g π (hwV (liftV pstep) pdone img M h).img
        (hwV (liftV pstep) pdone img M h).M Ψ) (v := v)).2
      iexact Hv
    · exact BigSepL.bigSepL_nil_intro

end transfer

section premise

variable {GF : BundledGFunctors} [InvGpreS GF] [GhostVarG GF HSt] [GhostVarG GF Bool]

/-- A machine-v2 adequacy premise of an A/D-free program gives the variant's. -/
theorem premiseV_of {pstep : P → Unit → PLabel → P → Unit → Prop} {pdone : P → Option V} {img : Image}
    {M : List PMsg} {ps : List P} {π : Proto} {Φ : Nat → V → Prop} {Ψ : Nat → Trace → Prop} {Dd : Nat → Prop}
    (hna : noAdL M) (hp : wpPremise hlc GF pstep pdone img M ps π Φ Ψ Dd) :
    wpPremiseV hlc GF (liftV pstep) pdone img M ps π Φ Ψ Dd := by
  intro Hinv g P0 h1 h2 h3 h4
  iintro #Hd Hh Hp
  imod (@hp Hinv g P0 h1 h2 h3 h4) $$ Hd Hh [Hp] with Hw
  · iapply BigSepL.bigSepL_mono ?_ $$ Hp
    intro k _ _
    iintro H
    iapply H
    ipureintro; exact noAdL_adAt hna _
  imodintro
  iapply BigSepL.bigSepL_mono ?_ $$ Hw
  intro k p _
  iintro H
  iapply (wpA_wpAV (pdone := pdone) (img := img) (h := k) hna) $$ %p H

end premise

/-! ## 3. G4 (2) over the A/D variant -/

/-- The value of hart `h`'s `k`-th load-like entry in a variant run (PF `obsLoad` over the projected trace). -/
def obsLoadV (evs : List Ad.VEvt) (h k : Nat) : Option Nat := ((loadsOf (prjT (Ad.traceOfV h evs)))[k]?).map obsOf

/-- **G4 TARGET (2) OVER THE A/D VARIANT, THROUGH `adequacyAV`**: in every valid run of the variant of `mpOwnT`
(program half `liftV litStep`: A/D updates are machine steps the program does not emit), if H1's flag load
returned 1, its x load returned 42.  The hart proofs are OwnAMP.lean's, unchanged (`mp_premise`), carried by
`premiseV_of`; the concurrent adequacy is the variant's. -/
theorem own_mpAD (evs : List Ad.VEvt) (cfg : PCfg LP Unit)
    (hv : Ad.validRunV (liftV litStep) imgMP () (progs mpOwnT) evs cfg) :
    ∀ b, obsLoadV evs 1 0 = some 1 → obsLoadV evs 1 1 = some b → b = 42 := by
  have hnoinv := Own.lit_noInvalT (validRunV_toV2 hv).1
  have hna := noAdL_of_run hv
  obtain ⟨_, hΨ, _⟩ := adequacyAV (hlc := .hasLC) (GF := ownGF) Proto.triv (fun _ _ => True)
    (fun h => ΨK cfg.pcLog (qsMP h)) (fun t => isD cfg.pcLog t = true) trivial (noAdL_PO hna) (adEmit_liftV _)
    (fun h => ⟨qsMP_nil h, wrOk_nil cfg.pcLog⟩) (premiseV_of hna (mp_premise cfg.pcLog hnoinv)) hv rfl
  intro b h0 h1
  have hq := (hΨ 1 (prjT (Ad.traceOfV 1 evs)).length).1
  rw [List.take_length] at hq
  unfold obsLoadV at h0 h1
  rw [← loadsOf_memEv] at h0 h1
  obtain ⟨a, ha, ha1⟩ := Option.map_eq_some_iff.1 h0
  obtain ⟨b', hb, hb1⟩ := Option.map_eq_some_iff.1 h1
  rw [← hb1]
  exact hq a b' ha hb ha1

/-- The same verdict through the run transfer and v2's `own_mp` (a cross-check of `own_mpAD`). -/
theorem own_mpAD_run (evs : List Ad.VEvt) (cfg : PCfg LP Unit)
    (hv : Ad.validRunV (liftV litStep) imgMP () (progs mpOwnT) evs cfg) :
    ∀ b, obsLoadV evs 1 0 = some 1 → obsLoadV evs 1 1 = some b → b = 42 := by
  obtain ⟨hr, htr⟩ := validRunV_toV2 hv
  have := own_mp cfg.pcLog ⟨evs.map evV, cfg⟩ hr
  unfold PFRun.obsLoad PFRun.trace at this
  unfold obsLoadV
  rw [← htr 1]
  exact this

/-! ## 4. Row 50 (D-OOTA): the negative test -/

/-- Row 50's leaf PTE `p` (any address; translation is off in the variant, the test is about `M` only). -/
def p50 : Int := 8

/-- `proto_p := "D clear"` (bit 7 of `p`'s low byte); every other location unconstrained. -/
def proto50 : Proto :=
  ⟨fun m => m.pa = p50 → ∀ b, m.data[0]? = some b → b &&& 0x80 = 0,
   fun img => ∀ b, img p50 = some b → b &&& 0x80 = 0⟩

/-- The image: `p` holds `P|A` (valid, accessed), D clear; everything else 0. -/
def img50 : Image := fun a => if a = p50 then some 0x41 else some 0

/-- Row 50's `M = [1: (p, P|D, H0, WCad), 2: (x, 1, H1), 3: (z, _, H0)]`. -/
def M50 : List PMsg := [⟨p50, [0xC1], some 0, PClass.ad⟩, ⟨16, [1], some 1, .plain⟩, ⟨24, [1], some 0, .plain⟩]

/-- **THE ROW-50 NEGATIVE TEST** (plan §3 "Test"): `PO_adV` FAILS for "D clear", so `adequacyAV` has no PO-ad
premise from which the derivation of the false outcome could start. -/
theorem row50_neg : ¬ PO_adV proto50 img50 M50 := by
  intro h
  have hv0 : Valid proto50 img50 M50 (1 - 1) :=
    ⟨fun b hb => by simp [img50] at hb; subst hb; decide,
     fun t h1 h2 => by simp at h2; omega⟩
  have hd : adData img50 M50 1 p50 [0xC1] := ⟨true, fun j b hj => by
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hj; subst hj
      exact ⟨0x41, by simp [memAt, img50], by decide⟩
    | succ j => simp at hj⟩
  have := h 1 ⟨p50, [0xC1], some 0, PClass.ad⟩ (Nat.le_refl _) (by decide) rfl rfl hv0 hd rfl 0xC1 rfl
  revert this; decide

/-- With machine v2's vocabulary (`PMsg.isAd` constantly false) the same test is vacuous: v2's `PO_ad` holds. -/
theorem row50_v2_vacuous : PO_ad proto50 img50 M50 := PO_ad_all _ _ _

end Weak.Prom.OAd

#print axioms Weak.Prom.OAd.own_mpAD
#print axioms Weak.Prom.OAd.own_mpAD_run
#print axioms Weak.Prom.OAd.row50_neg
#print axioms Weak.Prom.OAd.wpA_wpAV
