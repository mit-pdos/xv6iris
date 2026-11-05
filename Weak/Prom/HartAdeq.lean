/-
Weak/Prom: **S5a — the adequacy link of the hart lift** (plan rev 7 §7, §3; track (a)'s concurrent adequacy
`OA.adequacyA`, OwnAAdeq.lean).

`adequacyS`: for the REAL Sail emission (`pstepV2`, every hart `cpu` starting at the boundary `hartInit cpu (rs0
cpu)`), if in every environment the adequacy builds the client proves every hart's loop wp `wpLoopP cpu` from the
doom box, the message one-shots, each hart's initial core and its whole register file's cells, then every valid run
of machine v2 meets A0's exports (ii)–(v): the trace invariant at every prefix of every hart, the partition, `Valid`
at `|M|`, `traceWf`.  (Export (i), termination, is vacuous: a hart never stops, as MachCSL's.)

The link allocates what the hart lift adds on top of track (a) (plan R-a5: once, at adequacy start): one register
ghost map per hart at its initial file (`regAuthAt` for the wp, `regCellsAt` for the client) and one channel ghost
per hart (both halves at `(none, ixNone)`), builds the `PromEnv`, and turns each `wpLoopP cpu` into track (a)'s
`wpA` of hart `cpu.val` at `hartInit cpu (rs0 cpu)`.  No named assumption.  No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Prom.HartSwp
import MachCSL.Power

namespace Weak.Prom.HL

open MachCSL MachCSL.Stdpp Iris.Std
open Weak (Image Dsrc)
open Weak.Prom Weak.Prom.PF Weak.Prom.OA
open PLabel
open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D

/-! ## 1. Pure plumbing -/

/-- The initial harts: hart `cpu` at the instruction boundary with register file `rs0 cpu`. -/
def psOf (rs0 : CPU → RegFile) : List HState := cpus.map (fun cpu => hartInit cpu (rs0 cpu))

theorem psOf_length (rs0 : CPU → RegFile) : (psOf rs0).length = NCPU := by
  simp [psOf, cpus]

/-- `cpus` lists hart `k` at index `k`. -/
theorem cpus_idx {k : Nat} {x : CPU} (hk : cpus[k]? = some x) : x.val = k := by
  have hlt : k < cpus.length := (List.getElem?_eq_some_iff.1 hk).1
  have hk' : k < NCPU := by simpa [cpus] using hlt
  have := cpus_get? (⟨k, hk'⟩ : CPU)
  rw [hk] at this
  cases this
  rfl

section adeq

variable {hlc : HasLC} {GF : BundledGFunctors} [InvGpreS GF] [GhostVarG GF HSt] [GhostVarG GF Bool]
  [GhostMapG GF Nat RegVal RegMapF] [GhostVarG GF Chan]

/-! ## 2. Allocation -/

/-- The fully owned cells of a whole register file at map `γ` (MachCSL `regCells`, Power.lean). -/
def regCellsAt (γ : GName) (f : RegFile) : IProp GF :=
  iprop([∗map] k ↦ v ∈ regMapOf f, γ ↪◯MAP[k] v)

/-- Allocate one hart's register map at file `f` (MachCSL `regs_alloc_one`). -/
theorem regsP_alloc_one (f : RegFile) :
    ⊢@{IProp GF} |==> ∃ γ, regAuthAt γ f ∗ regCellsAt γ f := by
  imod (ghost_map_alloc (regMapOf f)) with ⟨%γ, Hauth, Hcells⟩
  imodintro
  iexists γ
  unfold regCellsAt
  iframe Hcells
  unfold regAuthAt
  iexists (regMapOf f)
  iframe Hauth
  ipureintro
  exact regAgree_regMapOf f

/-- One channel ghost, both halves, at the initial channel. -/
theorem chan_alloc_one :
    ⊢@{IProp GF} |==> ∃ γ, ghost_var γ (.own (1 : Qp).half) ((none, ixNone) : Chan) ∗
      ghost_var γ (.own (1 : Qp).half) ((none, ixNone) : Chan) := by
  iintro
  imod ghost_var_alloc ((none, ixNone) : Chan) with ⟨%γ, H⟩
  have hs := ghost_var_split (GF := GF) γ ((none, ixNone) : Chan) (1 : Qp).half (1 : Qp).half
  rw [Qp.half_add_half] at hs
  ihave ⟨H1, H2⟩ := hs $$ H
  imodintro
  iexists γ
  iframe H1 H2

/-- One ghost name per (distinct) hart of `l`, each with `P` (MachCSL `names_alloc_list`). -/
theorem namesP_alloc_list (P : GName → CPU → IProp GF)
    (halloc : ∀ c, ⊢@{IProp GF} |==> ∃ γ, P γ c) (l : List CPU) (hl : l.Nodup) :
    ⊢@{IProp GF} |==> ∃ names : CPU → GName, [∗list] cpu ∈ l, P (names cpu) cpu := by
  induction l with
  | nil =>
    imodintro
    iexists (fun _ => 0)
    exact BigSepL.bigSepL_nil_intro
  | cons c l ih =>
    have hc : c ∉ l := (List.nodup_cons.mp hl).1
    imod (ih (List.nodup_cons.mp hl).2) with ⟨%names, Hl⟩
    imod (halloc c) with ⟨%γ, Hc⟩
    imodintro
    iexists (fun c' => if c' = c then γ else names c')
    have e : (([∗list] cpu ∈ l, P (if cpu = c then γ else names cpu) cpu) : IProp GF) =
        [∗list] cpu ∈ l, P (names cpu) cpu :=
      BigSepL.bigSepL_eq fun {k x} hk => by
        rw [if_neg (fun (h : x = c) => hc (h ▸ List.mem_of_getElem? hk))]
    iapply BigSepL.bigSepL_cons.2
    simp only [if_true]
    rw [e]
    iframe Hc Hl

/-! ## 3. The client premise and the adequacy -/

/-- **THE CLIENT PREMISE** of the hart lift's adequacy: in every environment the adequacy builds (track (a)'s names
for the `NCPU` harts with the initial promise sets `P0`, the given `π`, image, final memory, trace invariant), from
the doom box, every message one-shot, and each hart's initial core and whole register file, the client (after its
own allocations, `={⊤}=∗`) proves every hart's loop wp. -/
def wpPremiseS (hlc : HasLC) (GF : BundledGFunctors) [GhostVarG GF HSt] [GhostVarG GF Bool]
    [GhostMapG GF Nat RegVal RegMapF] [GhostVarG GF Chan] (π : Proto) (img : Image) (M : List PMsg)
    (Ψ : Nat → Trace → Prop) (Dd : Nat → Prop) (rs0 : CPU → RegFile) : Prop :=
  ∀ [InvGS_gen hlc GF] [E : PromEnv], E.π = π → E.img = img → E.M = M → E.Ψ = Ψ → E.g.dd = Dd →
    E.g.hn.length = NCPU → E.g.mn.length = M.length →
    ∀ P0 : Nat → GSet Nat, (∀ h, h < NCPU → ∀ t, t ∈ P0 h ↔ 0 < t ∧ ownTs M h t) →
    ⊢@{IProp GF} doomInv E.g M -∗ ([∗list] k ↦ _x ∈ E.g.mn, pend E.g (k + 1)) -∗
      ([∗list] cpu ∈ cpus, coreP cpu ⟨none, ixNone, psInit, P0 cpu.val, []⟩ ∗ regCellsAt (E.rn cpu) (rs0 cpu))
      ={⊤}=∗ [∗list] cpu ∈ cpus, wpLoopP (hlc := hlc) cpu

/-- **THE ADEQUACY OF THE HART LIFT** (plan §7; A0's exports (ii)–(v) through track (a)'s `adequacyA`): every valid
run of machine v2 over the REAL Sail emission, from the boundary states `psOf rs0`, meets the trace invariant at
every prefix of every hart, the partition, `Valid π img M |M|` and `traceWf`. -/
theorem adequacyS (π : Proto) (img : Image) (M : List PMsg) (Ψ : Nat → Trace → Prop)
    (ψq : ∀ h τ l, quietLab l = true → Ψ h τ → Ψ h (τ ++ [(l, none)])) (Dd : Nat → Prop) (rs0 : CPU → RegFile)
    (d0 : DevStates) (run : PFRun HState DevStates) :
    PO_img π img → (∀ h, Ψ h []) → wpPremiseS hlc GF π img M Ψ Dd rs0 →
    PF.validRun pstepV2 img d0 (psOf rs0) M run →
      (∀ h k, Ψ h ((run.trace h).take k))
    ∧ (∀ t, 1 ≤ t → t ≤ M.length → exU (fun h => t ∈ run.fulfils h ∧ tidAt M t = some h))
    ∧ (∀ h, (run.fulfils h).Nodup)
    ∧ Valid π img M M.length
    ∧ run.traceWf M := by
  intro himg hΨ0 hcl hrun
  haveI : Inhabited HState := ⟨hartInit (⟨0, by decide⟩ : CPU) (rs0 ⟨0, by decide⟩)⟩
  have hprem : wpPremise hlc GF pstepV2 (fun _ => (none : Option Empty)) img M (psOf rs0) π
      (fun _ _ => False) Ψ Dd := by
    intro inst g P0 hn hm hd hP0
    rw [psOf_length] at hn hP0
    iintro #Hdoom Hharts Hpends
    imod (namesP_alloc_list (fun γ cpu => iprop(regAuthAt γ (rs0 cpu) ∗ regCellsAt γ (rs0 cpu)))
      (fun cpu => regsP_alloc_one (rs0 cpu)) cpus (List.nodup_finRange NCPU)) with ⟨%rn, Hregs⟩
    imod (namesP_alloc_list (fun γ _ => iprop(ghost_var γ (.own (1 : Qp).half) ((none, ixNone) : Chan) ∗
        ghost_var γ (.own (1 : Qp).half) ((none, ixNone) : Chan)))
      (fun _ => chan_alloc_one) cpus (List.nodup_finRange NCPU)) with ⟨%cn, Hchans⟩
    letI E : PromEnv := ⟨g, π, img, M, Ψ, ψq, rn, cn⟩
    -- the client's premise, at the allocated names (definitional unfolding of `E`)
    have hW : ⊢@{IProp GF} doomInv g M -∗ ([∗list] k ↦ _x ∈ g.mn, pend g (k + 1)) -∗
        ([∗list] cpu ∈ cpus, (ghost_var (cn cpu) (.own (1 : Qp).half) ((none, ixNone) : Chan) ∗
          hartA g cpu.val psInit (P0 cpu.val) []) ∗ regCellsAt (rn cpu) (rs0 cpu))
        ={⊤}=∗ [∗list] cpu ∈ cpus, wpLoopP (hlc := hlc) (E := E) cpu :=
      hcl (E := E) rfl rfl rfl rfl hd hn hm P0 hP0
    -- each hart's loop wp, at its initial register file and channel, is track (a)'s wp of its thread
    have hper : ∀ (Φ' : Empty → IProp GF) {k : Nat} {x : CPU}, cpus[k]? = some x →
        ((wpLoopP (hlc := hlc) (E := E) x ∗ regAuthAt (GF := GF) (rn x) (rs0 x)) ∗
          ghost_var (cn x) (.own (1 : Qp).half) ((none, ixNone) : Chan)) ⊢
        wpA (hlc := hlc) g π (hw pstepV2 (fun _ => (none : Option Empty)) img M k) Ψ (hartInit x (rs0 x)) Φ' := by
      intro Φ' k x hk
      have hkx := cpus_idx hk
      subst hkx
      have cr : regAuthAt (GF := GF) (rn x) (rs0 x) ⊢ regAuth (E := E) x (rs0 x) := .rfl
      have cc : ghost_var (GF := GF) (cn x) (.own (1 : Qp).half) ((none, ixNone) : Chan) ⊢
          chanAuth (E := E) x (none, ixNone) := .rfl
      have conv : wpA (hlc := hlc) (GF := GF) E.g E.π (hwS x) E.Ψ (⟨x, .pure (), rs0 x, none, ixNone⟩ : HState)
          (fun _ => iprop(True)) ⊢
          wpA (hlc := hlc) g π (hw pstepV2 (fun _ => (none : Option Empty)) img M x.val) Ψ
            (hartInit x (rs0 x)) Φ' := by
        have : (fun _ : Empty => iprop(True : IProp GF)) = Φ' := funext (fun v => v.elim)
        subst this
        exact .rfl
      iintro ⟨⟨Hw, Hr⟩, Hc⟩
      ihave Hr := cr $$ Hr
      ihave Hc := cc $$ Hc
      unfold wpLoopP wpHP
      ihave H := Hw $$ %(rs0 x) %none %ixNone Hr Hc
      iapply conv $$ H
    -- the harts' track (a) ghosts, per hart
    have hharts : ([∗list] k ↦ _x ∈ g.hn, hartA (GF := GF) g k psInit (P0 k) []) ⊢
        [∗list] cpu ∈ cpus, hartA g cpu.val psInit (P0 cpu.val) [] := by
      refine (bsl_len g.hn cpus (fun k => hartA (GF := GF) g k psInit (P0 k) [])
        (by rw [hn]; simp [cpus])).trans ?_
      exact BigSepL.bigSepL_mono fun {k x} hk => by rw [cpus_idx hk]
    ihave Hharts := hharts $$ Hharts
    icases BigSepL.bigSepL_sep_eqv.1 $$ Hregs with ⟨Hauths, Hcells⟩
    icases BigSepL.bigSepL_sep_eqv.1 $$ Hchans with ⟨Hca, Hcc⟩
    ihave Hcores := BigSepL.bigSepL_sep_eqv.2 $$ [Hcc Hharts]
    · iframe Hcc Hharts
    ihave Hin := BigSepL.bigSepL_sep_eqv.2 $$ [Hcores Hcells]
    · iframe Hcores Hcells
    imod hW $$ Hdoom Hpends Hin with Hw
    imodintro
    ihave Hall := BigSepL.bigSepL_sep_eqv.2 $$ [Hw Hauths]
    · iframe Hw Hauths
    ihave Hall := BigSepL.bigSepL_sep_eqv.2 $$ [Hall Hca]
    · iframe Hall Hca
    unfold psOf
    rw [BigSepL.bigSepL_map]
    iapply (BigSepL.bigSepL_mono (fun hk => hper _ hk)) $$ Hall
  obtain ⟨_, h2, h3, h4, h5, h6⟩ := adequacyA π (fun _ _ => False) Ψ Dd himg hΨ0 hprem hrun
  exact ⟨h2, h3, h4, h5, h6⟩

end adeq

end Weak.Prom.HL

#print axioms Weak.Prom.HL.adequacyS
#print axioms Weak.Prom.HL.wpHP_lift
#print axioms Weak.Prom.HL.swpP_readReg
#print axioms Weak.Prom.HL.swpP_writeReg
#print axioms Weak.Prom.HL.wpLoopP_restart
