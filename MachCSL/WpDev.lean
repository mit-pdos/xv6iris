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
import Iris.Instances.Lib.Invariants

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

theorem wpDev_elim (d : DevId) (tid : TaskId) (m : DevProg d) :
    wpDev d tid m ∗ genCert ⊢@{IProp GF} devWP (genId (hlc := hlc) (GF := GF)) d tid m := by
  unfold wpDev
  iintro ⟨H, Hc⟩
  iapply H $$ Hc

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

/-! ## The device mirrors in the interpretation -/

/-- The index of a device in `DevId.all`. -/
def DevId.idx : DevId → Nat
  | .uart .uart0 => 0
  | .uart .uart1 => 1
  | .plic => 2
  | .virtio => 3

theorem DevId.all_get? (d : DevId) : DevId.all[d.idx]? = some d := by
  cases d with
  | uart i => cases i <;> rfl
  | plic => rfl
  | virtio => rfl

theorem DevId.all_get?_ne {k : Nat} {y : DevId} (hk : DevId.all[k]? = some y) (d : DevId)
    (hne : k ≠ d.idx) : y ≠ d := by
  rintro rfl
  apply hne
  rcases k with _ | _ | _ | _ | k
  · simp [DevId.all] at hk; subst hk; rfl
  · simp [DevId.all] at hk; subst hk; rfl
  · simp [DevId.all] at hk; subst hk; rfl
  · simp [DevId.all] at hk; subst hk; rfl
  · simp [DevId.all] at hk

/-- The ambient era's mirror halves of device `d`. -/
abbrev devAuth (d : DevId) (s : DevSt d) : IProp GF := devAuthAt (MachGS.era (hlc := hlc) (GF := GF)) d s
abbrev devFrag (d : DevId) (s : DevSt d) : IProp GF := devFragAt (MachGS.era (hlc := hlc) (GF := GF)) d s

/-- The interpretation does not mention the task bookkeeping. -/
theorem machInterp_devrt (σ : MState) (f : DevId → DevRt) :
    machInterp (GF := GF) { σ with devrt := f } = machInterp σ := rfl

theorem machInterp_setRt (σ : MState) (d : DevId) (rt : DevRt) :
    machInterp (GF := GF) (σ.setRt d rt) = machInterp σ := rfl

/-- Re-assemble the interpretation after a device update. -/
theorem machInterp_of_devs (σ : MState) (ds : DevStates) :
    ([∗list] cpu ∈ cpus, regInterp cpu (σ.regs cpu)) ∗ genHeapInterp σ.mem ∗ memModel σ ∗
      devInterp ds ⊢@{IProp GF} machInterp { σ with devs := ds } := by
  have e : machInterp (GF := GF) { σ with devs := ds } =
      iprop(([∗list] cpu ∈ cpus, regInterp cpu (σ.regs cpu)) ∗ genHeapInterp σ.mem ∗ memModel σ ∗
        devInterp ds) := rfl
  rw [e]

/-- Extract device `d`'s mirror from the interpretation, with a closing wand
that accepts the mirror at a new state. -/
theorem machInterp_acc_dev (σ : MState) (d : DevId) :
    machInterp (GF := GF) σ ⊢
      devAuth d (σ.devs.st d) ∗
      ∀ (s' : DevSt d), devAuth d s' -∗ machInterp { σ with devs := σ.devs.set d s' } := by
  have hget := DevId.all_get? d
  have e : machInterp (GF := GF) σ =
      iprop(([∗list] cpu ∈ cpus, regInterp cpu (σ.regs cpu)) ∗ genHeapInterp σ.mem ∗ memModel σ ∗
        devInterp σ.devs) := rfl
  rw [e]
  unfold devInterp devInterpAt
  iintro ⟨Hregs, Hmem, Hmm, Hdev⟩
  icases BigSepL.bigSepL_lookup_acc_impl (Φ := fun _ d' => devAuthAt (MachGS.era (hlc := hlc) (GF := GF)) d' (σ.devs.st d')) hget $$ Hdev
    with ⟨Hd, Hclose⟩
  iframe Hd
  iintro %s' Hs'
  iapply machInterp_of_devs σ (σ.devs.set d s')
  iframe Hregs Hmem Hmm
  unfold devInterp devInterpAt
  iapply Hclose $$ %(fun _ d' => devAuthAt (MachGS.era (hlc := hlc) (GF := GF)) d' ((σ.devs.set d s').st d'))
  · imodintro
    iintro %k %y %hk %hne Hy
    have hy : y ≠ d := DevId.all_get?_ne hk d hne
    show iprop(devAuthAt (MachGS.era (hlc := hlc) (GF := GF)) y (σ.devs.st y) ⊢
      devAuthAt MachGS.era y ((σ.devs.set d s').st y))
    rw [DevStates.set_other σ.devs d y s' hy]
  · show iprop(devAuth d s' ⊢ devAuthAt MachGS.era d ((σ.devs.set d s').st d))
    rw [DevStates.set_same]

theorem DevStates.set_self (ds : DevStates) (d : DevId) : ds.set d (ds.st d) = ds := by
  cases ds
  simp only [DevStates.set, DevStates.mk.injEq]
  funext d'
  by_cases h : d' = d
  · subst h; simp
  · simp [h]

/-- Closing the accessor at the unchanged state gives the interpretation back. -/
theorem machInterp_acc_dev_self (σ : MState) (d : DevId) :
    (∀ (s' : DevSt d), devAuth d s' -∗ machInterp { σ with devs := σ.devs.set d s' }) ∗
      devAuth d (σ.devs.st d) ⊢@{IProp GF} machInterp σ := by
  have e : machInterp (GF := GF) { σ with devs := σ.devs.set d (σ.devs.st d) } = machInterp σ := by
    rw [DevStates.set_self]
  iintro ⟨Hcl, Ha⟩
  rw [← e]
  iapply Hcl $$ %(σ.devs.st d) Ha

/-! ## Local device programs are safe under the mirror invariant

A program that never writes the bus and never drives a pin touches nothing
the interpretation ties to a hart: its only ghost is the device's own
mirror.  Under an invariant holding the mirror's other half at some state,
every such task is safe, and so is every task it forks -- which is the
UARTs' whole safety proof (the PLIC's wire arm and the disk's DMA need the
wire invariant and the driver's DMA lease respectively). -/

/-- A program using only the local primitives. -/
inductive DevM.Local {S T : Type} : DevM S T Unit → Prop
  | pure (a : Unit) : Local (.pure a)
  | op (o : DevOp S T) (k : o.ret → DevM S T Unit)
      (hw : ∀ g pa n w, o ≠ .dmaWrite g pa n w) (hp : ∀ c mm b, o ≠ .setPin c mm b)
      (hk : ∀ r, Local (k r)) : Local (.op o k)

/-- A device all of whose programs are local. -/
def DevSig.Local (d : DevId) : Prop :=
  DevM.Local (devSig d).body ∧ ∀ t, DevM.Local ((devSig d).task t)

/-- The mirror invariant: the device's half at some state. -/
def devInv (N : Namespace) (d : DevId) : IProp GF := inv N (∃ s : DevSt d, devFrag d s)

instance devInv_persistent (N : Namespace) (d : DevId) : Persistent (devInv (GF := GF) N d) := by
  unfold devInv; infer_instance

/-- What a local primitive does: moves the device's own state, or nothing,
or forks one named task. -/
theorem devOpStep_local (gen : Nat) (d : DevId) (o : DevOp (DevSt d) (DevTask d)) (σ : MState)
    (v : o.ret) (σ' : MState) (obs : List Obs) (efs : List Expr)
    (hw : ∀ g pa n w, o ≠ .dmaWrite g pa n w) (hp : ∀ c mm b, o ≠ .setPin c mm b)
    (hop : devOpStep gen d o σ v σ' obs efs) :
    (∃ s' : DevSt d, σ' = σ.setDev d s' ∧ efs = []) ∨
    (σ' = σ ∧ efs = []) ∨
    (∃ (rt : DevRt) (t : DevTask d) (tid' : TaskId),
      σ' = σ.setRt d rt ∧ efs = [.dev gen d tid' ((devSig d).task t)]) := by
  cases o with
  | step g =>
    obtain ⟨s', os, _, rfl, _, rfl⟩ := hop
    exact Or.inl ⟨s', rfl, rfl⟩
  | get => obtain ⟨_, rfl, _, rfl⟩ := hop; exact Or.inr (Or.inl ⟨rfl, rfl⟩)
  | choose => obtain ⟨rfl, _, rfl⟩ := hop; exact Or.inr (Or.inl ⟨rfl, rfl⟩)
  | dmaRead pa n => obtain ⟨_, rfl, _, rfl⟩ := hop; exact Or.inr (Or.inl ⟨rfl, rfl⟩)
  | dmaWrite g pa n w => exact absurd rfl (hw g pa n w)
  | sample src => obtain ⟨_, rfl, _, rfl⟩ := hop; exact Or.inr (Or.inl ⟨rfl, rfl⟩)
  | setPin c mm b => exact absurd rfl (hp c mm b)
  | fork t =>
    obtain ⟨_, _, rfl, rfl⟩ := hop
    exact Or.inr (Or.inr ⟨_, t, _, rfl, rfl⟩)
  | join tid => obtain ⟨_, rfl, _, rfl⟩ := hop; exact Or.inr (Or.inl ⟨rfl, rfl⟩)

set_option maxHeartbeats 4000000 in
/-- Every task of a local device is safe under its mirror invariant. -/
theorem wpDev_local (N : Namespace) (d : DevId) (hloc : DevSig.Local d) :
    devInv N d ∗ genCert ⊢@{IProp GF} ∀ (tid : TaskId) (m : DevProg d), ⌜DevM.Local m⌝ →
      devWP (genId (hlc := hlc) (GF := GF)) d tid m := by
  unfold devInv
  iintro ⟨#Hinv, #Hcert⟩
  iloeb as IH
  iintro %tid %m %hm
  iapply wpDev_elim d tid m
  iframe Hcert
  iapply wpDev_lift d tid m
  iintro %σ Hσ
  iinv Hinv with Hbody Hclose
  icases Hbody with ⟨%s, >Hfrag⟩
  icases machInterp_acc_dev σ d $$ Hσ with ⟨Hauth, Hσclose⟩
  ihave %hs := devAgreeAt _ d (σ.devs.st d) s $$ [Hauth Hfrag]
  case' _ => iframe
  subst hs
  iapply fupd_mask_intro LawfulSet.empty_subset
  iintro Hmask
  isplit
  · ipureintro
    exact devStep_total _ d tid m σ
  inext
  iintro %obs %m' %σ' %efs %hstep Hcred
  imod Hmask
  -- the continuation, once the interpretation is back at `σ'`
  have hmk : ∀ (m'' : DevProg d), DevM.Local m'' →
      ⊢@{IProp GF} (∀ (tid : TaskId) (m : DevProg d), ⌜DevM.Local m⌝ →
        devWP (genId (hlc := hlc) (GF := GF)) d tid m) -∗ wpDev d tid m'' := by
    intro m'' hm''
    iintro IH
    unfold wpDev
    iintro _
    iapply IH $$ %tid %m'' %hm'' 
  cases m with
  | pure a =>
    obtain ⟨rfl, rfl, h⟩ := hstep
    ihave Hcl := Hclose $$ [Hfrag]
    case' _ => inext; iexists (σ.devs.st d); iexact Hfrag
    imod Hcl
    imodintro
    ihave Hσ := machInterp_acc_dev_self σ d $$ [Hσclose Hauth]
    case' _ => iframe
    rcases h with ⟨_, rfl, rfl⟩ | ⟨_, rfl, hσ'⟩
    · iframe Hσ
      isplitl []
      · iapply hmk _ hloc.1 $$ IH
      · exact BigSepL.bigSepL_nil_intro
    · rw [hσ']
      isplitl [Hσ]
      · split
        · iexact Hσ
        · rw [machInterp_setRt]; iexact Hσ
      isplitl []
      · iapply hmk _ (DevM.Local.pure ()) $$ IH
      · exact BigSepL.bigSepL_nil_intro
  | op o k =>
    have hm' := hm
    cases hm with
    | op _ _ hw hp hk =>
    rcases hstep with ⟨v, rfl, hop⟩ | ⟨hb, rfl, hσ, rfl, rfl⟩
    · rcases devOpStep_local _ d o σ v σ' obs efs hw hp hop with
        ⟨s', rfl, rfl⟩ | ⟨hσ, rfl⟩ | ⟨rt, t, tid', rfl, rfl⟩
      · -- the device's own state moved: both halves follow
        imod (devUpdateAt _ d (σ.devs.st d) (σ.devs.st d) s') $$ [Hauth Hfrag] with ⟨Hauth, Hfrag⟩
        · iframe
        ihave Hcl := Hclose $$ [Hfrag]
        case' _ => inext; iexists s'; iexact Hfrag
        imod Hcl
        imodintro
        isplitl [Hauth Hσclose]
        · iapply Hσclose $$ %s' Hauth
        isplitl []
        · iapply hmk _ (hk v) $$ IH
        · exact BigSepL.bigSepL_nil_intro
      · -- nothing moved
        rw [hσ]
        ihave Hcl := Hclose $$ [Hfrag]
        case' _ => inext; iexists (σ.devs.st d); iexact Hfrag
        imod Hcl
        imodintro
        ihave Hσ := machInterp_acc_dev_self σ d $$ [Hσclose Hauth]
        case' _ => iframe
        iframe Hσ
        isplitl []
        · iapply hmk _ (hk v) $$ IH
        · exact BigSepL.bigSepL_nil_intro
      · -- a task forked: its program is one of the device's own
        ihave Hcl := Hclose $$ [Hfrag]
        case' _ => inext; iexists (σ.devs.st d); iexact Hfrag
        imod Hcl
        imodintro
        ihave Hσ := machInterp_acc_dev_self σ d $$ [Hσclose Hauth]
        case' _ => iframe
        isplitl [Hσ]
        · rw [machInterp_setRt]; iexact Hσ
        isplitl []
        · iapply hmk _ (hk v) $$ IH
        · iapply BigSepL.bigSepL_singleton.2
          unfold devWP
          iapply IH $$ %tid' %((devSig d).task t) %(hloc.2 t)
    · -- blocked: retried
      rw [hσ]
      ihave Hcl := Hclose $$ [Hfrag]
      case' _ => inext; iexists (σ.devs.st d); iexact Hfrag
      imod Hcl
      imodintro
      ihave Hσ := machInterp_acc_dev_self σ d $$ [Hσclose Hauth]
      case' _ => iframe
      iframe Hσ
      isplitl []
      · iapply hmk _ hm' $$ IH
      · exact BigSepL.bigSepL_nil_intro

/-- The UARTs are local devices. -/
theorem uart_local (i : UartId) : DevSig.Local (.uart i) := by
  refine ⟨?_, fun t => nomatch t⟩
  show DevM.Local (Uart.body i)
  unfold Uart.body DevM.chooseLt DevM.chooseByte DevM.choose DevM.step DevM.lift
  simp only [bind, DevM.bind, Pure.pure]
  refine DevM.Local.op _ _ (fun _ _ _ _ => nofun) (fun _ _ _ => nofun) fun r => ?_
  split
  · exact DevM.Local.op _ _ (fun _ _ _ _ => nofun) (fun _ _ _ => nofun) fun _ => DevM.Local.pure ()
  split
  · refine DevM.Local.op _ _ (fun _ _ _ _ => nofun) (fun _ _ _ => nofun) fun _ => ?_
    exact DevM.Local.op _ _ (fun _ _ _ _ => nofun) (fun _ _ _ => nofun) fun _ => DevM.Local.pure ()
  · exact DevM.Local.pure ()

/-- **The UART threads are safe** under their mirror invariants: the root
loop of port `i`, and every task it could fork (none). -/
theorem wpDev_uart (N : Namespace) (i : UartId) :
    devInv N (.uart i) ∗ genCert ⊢@{IProp GF}
      devWP (genId (hlc := hlc) (GF := GF)) (.uart i) rootTask (DevM.pure ()) := by
  iintro H
  iapply wpDev_local N (.uart i) (uart_local i) $$ H %rootTask %(DevM.pure ()) %(DevM.Local.pure ())

end MachCSL
