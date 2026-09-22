/-
MachCSL: weakest preconditions for DEVICE threads.

A device task `Expr.dev gen d tid m` is a thread of the language exactly as a
hart is, and its rules follow the hart's (`MachCSL.Wp`):

* `devWP gen d tid m` -- the bare WP of a device expression; `wpDev d tid m`
  the same at the ambient generation, under the generation's certificate;
* `wp_dev_dead` -- a dead generation's device task self-loops forever from
  the death certificate alone (the corpse rule);
* `wpDev_lift` -- the single lifting lemma: it hands the caller the ambient
  era's `machInterp` and asks for the step's reducibility and, per possible
  step (`devStep`: possibly observed, possibly forking), the interpretation
  back, the WP of the continuation and the WPs of the forked tasks.  Above
  it no rule sees a generation.
* `devStep_total` -- the pure fact that a device program can always take a
  step (every primitive either answers or is blocked, and a blocked primitive
  is retried), which is what makes a device loop's safety a matter of
  re-establishing the state interpretation only.
-/
import MachCSL.Wp

namespace MachCSL

open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode Std

/-! ## Totality of the device steps -/

theorem devOpStep_or_blocked (gen : Nat) (d : DevId) (o : DevOp (DevSt d) (DevTask d)) (σ : MState) :
    (∃ v σ' obs efs, devOpStep gen d o σ v σ' obs efs) ∨ devBlocked d o σ := by
  cases o with
  | step g =>
    cases h : g (σ.devs.st d) with
    | none => exact Or.inr h
    | some p => exact Or.inl ⟨(), _, _, _, p.1, p.2, h, rfl, rfl, rfl⟩
  | get => exact Or.inl ⟨_, _, _, _, rfl, rfl, rfl, rfl⟩
  | choose => exact Or.inl ⟨0, _, _, _, rfl, rfl, rfl⟩
  | dmaRead pa n =>
    obtain ⟨w, hw⟩ := exists_bv_of_bytes n (fun j =>
      ((σ.mem[pa + BitVec.ofNat 64 j]?).bind Hist.top).getD 0#8)
    refine Or.inl ⟨w, _, _, _, ?_, rfl, rfl, rfl⟩
    intro j hj b hb
    rw [hw j hj, hb]
    rfl
  | dmaWrite g pa n w =>
    cases hg : g (σ.devs.st d)
    · exact Or.inl ⟨(), _, _, _, rfl, rfl, Or.inr ⟨Or.inl hg, rfl⟩⟩
    · by_cases hram : ramBytes pa n
      · by_cases hr : anyReserve σ.resv pa n
        · exact Or.inr ⟨hg, hr⟩
        · exact Or.inl ⟨(), _, _, _, rfl, rfl, Or.inl ⟨hg, hram, hr, rfl⟩⟩
      · exact Or.inl ⟨(), _, _, _, rfl, rfl, Or.inr ⟨Or.inr hram, rfl⟩⟩
  | sample src => exact Or.inl ⟨_, _, _, _, rfl, rfl, rfl, rfl⟩
  | setPin cpu mm b => exact Or.inl ⟨(), _, _, _, rfl, rfl, rfl⟩
  | fork t => exact Or.inl ⟨_, _, _, _, rfl, rfl, rfl, rfl⟩
  | join tid =>
    by_cases h : tid ∈ (σ.devrt d).done
    · exact Or.inl ⟨(), _, _, _, h, rfl, rfl, rfl⟩
    · exact Or.inr h

/-- A device program can always take a step. -/
theorem devStep_total (gen : Nat) (d : DevId) (tid : TaskId) (m : DevProg d) (σ : MState) :
    ∃ obs m' σ' efs, devStep gen d tid m σ obs m' σ' efs := by
  cases m with
  | pure _ =>
    by_cases h : tid = rootTask
    · exact ⟨[], _, σ, [], rfl, rfl, Or.inl ⟨h, rfl, rfl⟩⟩
    · exact ⟨[], .pure (), _, [], rfl, rfl, Or.inr ⟨h, rfl, rfl⟩⟩
  | op o k =>
    rcases devOpStep_or_blocked gen d o σ with ⟨v, σ', obs, efs, hs⟩ | hb
    · exact ⟨obs, k v, σ', efs, Or.inl ⟨v, rfl, hs⟩⟩
    · exact ⟨[], .op o k, σ, [], Or.inr ⟨hb, rfl, rfl, rfl, rfl⟩⟩

/-! ## The corpse rule -/

section dead
variable {hlc : HasLC} {GF : BundledGFunctors} [MachFixedGS hlc GF]

/-- The bare WP of a device expression. -/
def devWP (gen : Nat) (d : DevId) (tid : TaskId) (m : DevProg d) : IProp GF :=
  WP (Expr.dev gen d tid m) @ Stuckness.NotStuck; ⊤ {{ _v, True }}

/-- A dead generation's device task self-loops forever. -/
theorem wp_dev_dead (gen : Nat) (d : DevId) (tid : TaskId) (m : DevProg d) :
    genDead gen ⊢@{IProp GF} devWP gen d tid m := by
  unfold devWP
  iintro #Hdead
  iloeb as IH
  iapply wp_lift_step rfl
  iintro %g %ns %obs %obs' %nt Hσ
  rw [stateInterp_eq]
  unfold powerInterp
  icases Hσ with ⟨Hgen, Hrest⟩
  ihave %Hlt := genAuth_dead _ _ $$ Hgen Hdead
  have hnl : ¬ threadLive g gen := by
    intro h
    unfold threadLive at h
    omega
  iapply fupd_mask_intro LawfulSet.empty_subset
  iintro Hclose
  isplit
  · ipureintro
    exact ⟨[], .dev gen d tid m, g, [], primStep_dev_dead hnl⟩
  inext
  iintro %e₂ %g₂ %eₜ %Hstep _
  rcases primStep_dev_inv Hstep with ⟨hl, _⟩ | ⟨_, rfl, rfl, rfl, rfl⟩
  · exact absurd hl hnl
  imod Hclose
  imodintro
  rw [stateInterp_eq]
  unfold powerInterp
  iframe Hgen Hrest
  isplit
  · iexact IH
  · exact BigSepL.bigSepL_nil_intro

/-- The corpse rule, with the WP spelled out. -/
theorem wp_dev_dead' (gen : Nat) (d : DevId) (tid : TaskId) (m : DevProg d) :
    genDead gen ⊢@{IProp GF} WP (Expr.dev gen d tid m) @ Stuckness.NotStuck; ⊤ {{ _v, True }} :=
  wp_dev_dead gen d tid m

/-- A device root at its loop boundary, as the power thread forks it. -/
theorem devWP_loop (gen : Nat) (d : DevId) :
    devWP (GF := GF) gen d rootTask (pure ()) =
      WP (DevLoop gen d) @ Stuckness.NotStuck; ⊤ {{ IrisGS_gen.forkPost Expr GState Obs }} := rfl

end dead

variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF]

/-- Safety of the ambient generation's device `d`'s task `tid` with `m` left
to run, given the generation's certificate. -/
def wpDev (d : DevId) (tid : TaskId) (m : DevProg d) : IProp GF := iprop%
  genCert -∗ devWP (genId (hlc := hlc) (GF := GF)) d tid m

/-- The lifting lemma for device tasks. -/
theorem wpDev_lift (d : DevId) (tid : TaskId) (m : DevProg d) :
    (∀ σ, machInterp σ ={⊤,∅}=∗
      ⌜∃ obs m' σ' efs, devStep (genId (hlc := hlc) (GF := GF)) d tid m σ obs m' σ' efs⌝ ∗
      ▷ ∀ obs m' σ' efs, ⌜devStep (genId (hlc := hlc) (GF := GF)) d tid m σ obs m' σ' efs⌝ -∗
        £ 1 ={∅,⊤}=∗ machInterp σ' ∗ wpDev d tid m' ∗
          [∗list] ef ∈ efs, WP ef @ Stuckness.NotStuck; ⊤ {{ _v, True }})
    ⊢@{IProp GF} wpDev d tid m := by
  unfold wpDev devWP
  iintro H #Hcert
  ihave #Hparts := genCert_parts $$ Hcert
  icases Hparts with ⟨Hborn, Hstarted, Hreg⟩
  iapply wp_lift_step rfl
  iintro %g %ns %obs %obs' %nt Hσ
  rw [stateInterp_eq]
  unfold powerInterp
  icases Hσ with ⟨Hgen, Hstart, %R, HR, %Hok, Hcur⟩
  ihave %Hb' := genAuth_born _ _ $$ Hgen Hborn
  ihave %Hs' := startAuth_started _ _ $$ Hstart Hstarted
  by_cases hge : g.gen = genId (hlc := hlc) (GF := GF)
  · have hpow : g.pow = true := by
      cases h : g.pow
      · simp [startCount, h] at Hs'; omega
      · rfl
    have hl : threadLive g (genId (hlc := hlc) (GF := GF)) := ⟨hpow, hge⟩
    rw [eraCur_true hpow]
    icases Hcur with ⟨%E, %HE, Hera⟩
    ihave %HRg := eraRegistered_lookup _ _ _ $$ HR Hreg
    have HRg' : get? R g.gen = some (MachGS.era (hlc := hlc) (GF := GF)) := by
      rw [hge]; exact HRg
    have hEq : E = MachGS.era (hlc := hlc) (GF := GF) := by
      rw [HE] at HRg'
      exact Option.some.inj HRg'
    subst hEq
    rw [eraInterp_ambient]
    imod H $$ %g.m Hera with ⟨%Hred, H⟩
    imodintro
    isplit
    · ipureintro
      obtain ⟨obs₀, m', σ', efs, hs⟩ := Hred
      exact ⟨obs₀, .dev _ d tid m', { g with m := σ' }, efs, primStep_dev_live hl hs⟩
    inext
    iintro %e₂ %g₂ %eₜ %Hstep Hcred
    rcases primStep_dev_inv Hstep with ⟨_, m', σ', rfl, hs, rfl⟩ | ⟨hnl, _⟩
    · imod H $$ %obs %m' %σ' %eₜ %hs Hcred with ⟨Hσ', Hwp, Hefs⟩
      imodintro
      rw [stateInterp_eq]
      unfold powerInterp
      rw [show startCount { g with m := σ' } = startCount g from rfl]
      iframe Hgen Hstart
      isplitl [HR Hσ']
      · iexists R
        iframe HR
        isplit
        · ipureintro
          exact Hok
        rw [eraCur_true (g := { g with m := σ' }) hpow]
        iexists (MachGS.era (hlc := hlc) (GF := GF))
        isplit
        · ipureintro
          exact HRg'
        rw [eraInterp_ambient]
        iexact Hσ'
      isplitl [Hwp]
      · iapply Hwp
        iexact Hcert
      · iexact Hefs
    · exact absurd hl hnl
  · have hlt : genId (hlc := hlc) (GF := GF) < g.gen := by omega
    ihave #Hdead := genAuth_get_dead _ _ hlt $$ Hgen
    have hnl : ¬ threadLive g (genId (hlc := hlc) (GF := GF)) := fun h => hge h.2
    iapply fupd_mask_intro LawfulSet.empty_subset
    iintro Hclose
    isplit
    · ipureintro
      exact ⟨[], .dev _ d tid m, g, [], primStep_dev_dead hnl⟩
    inext
    iintro %e₂ %g₂ %eₜ %Hstep _
    rcases primStep_dev_inv Hstep with ⟨hl, _⟩ | ⟨_, rfl, rfl, rfl, rfl⟩
    · exact absurd hl hnl
    imod Hclose
    imodintro
    rw [stateInterp_eq]
    unfold powerInterp
    iframe Hgen Hstart
    isplitl [HR Hcur]
    · iexists R
      iframe HR Hcur
      ipureintro
      exact Hok
    isplit
    · iapply wp_dev_dead' (genId (hlc := hlc) (GF := GF)) d tid m
      iexact Hdead
    · exact BigSepL.bigSepL_nil_intro

end MachCSL
