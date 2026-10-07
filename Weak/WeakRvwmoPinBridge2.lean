/-
Weak: **the induction that discharges `checkerTaintSubProv`** (R-1(B) slice 2, deliverable 3).

Rocq: `iris/WeakRvwmoPinBridge2.v` @ xxvzwolszwmp.

## The Rocq header, in substance

`WeakRvwmoPinBridge` §3 states ONE hypothesis, `checkerTaintSubProv` (the static checker's taint
walk is a SUB-approximation of the emission's provenance), and proves the three witness classes
from it.  This file proves that hypothesis.  Nothing is admitted or axiomatised; what it costs
is a SITE ORACLE that is no longer a bare parameter but a DEFINED relation (`psites`), and the two
structural facts about the emission that relation packages.

* THE ALIGNMENT `reaches own stop s g s'`: from walk state `s` the emission emits the item groups
  of `g`, one group per instruction, following the checker's own fall-through successor
  `WeakRvwmoPinBridge2.wstep`, and arrives at `s'` whose pc is `stop`.  Each step carries two
  decidable obligations: (a) `grpOkb pc g1 g2 = true` -- the group's register writes are the
  DECODED ones (`depsRd`/`depsRd2` at `pc`) with emitted sources a SUPERSET of the decoded ones
  (DEC-7's `erw_srcs_covers` as a boolean); everything else in the group is provenance-neutral;
  (b) `taintSub (s'.psT) (taintStep s.psT s.psPc)` -- discharged by `wstepTaintSub` at every pc
  whose role names no destination (`c.j`, `jal x0`, `ret`), the identity elsewhere.
* THE INVARIANT `invOk j s t`: every register the checker calls tainted has `j` in the
  emission's `dprov`.  The checker's tainting of `rd` is matched by `dstep` overwriting
  `dprov rd` with the sources' positions; its untainting only weakens the antecedent.
* THE BASE CASE `ldCarrierSound`/`baseOk`: the load emits its own destination-register write
  with `DLdRes` among the sources after the row item that put `j` into `dsLd`.
* PROVED: `checkerTaintSubProvProof` for `psites`; `pinSegPin'` restates
  `WeakRvwmoPinBridge.pinSegPin` with the hypothesis discharged.  NOT PROVED (the honest
  residual R-3): that a `pstepEv` run's items ARE so grouped.  §8 exhibits both halves on
  `WeakRvwmoAdm`'s spin-load stretch, by kernel computation on real image bytes.
* The path is the fall-through one (`fwalk`); the all-paths `pdfs` conjunct is not needed.

## Deviations from Rocq

1. NAMES / VOCABULARY: camelCase (map below); Rocq `Z` pcs ↦ `Int`, `wreg` ↦ `Nat`,
   `Nat.eqb` ↦ `Nat.beq` (KernelPinsDef's), `forallb`/`existsb` ↦ `List.all`/`List.any`,
   `bool_decide` ↦ `decide`, `bv_unsigned w` ↦ `w.toNat`, `(_ =? _)%Z` ↦ `(_ == _)` (as in
   `fwalk`).  The Rocq section variables of `Discharge` (`pcL j own base`) are explicit leading
   arguments in that order; `psites` takes only the ones it uses (`pcL own base`, as in Rocq's
   generalised form).
2. `wstepTaint` follows the Lean `pstep`, whose `kflowOf` match lists `FLnone` last (Rocq
   first); the arms are the same.
3. §8's pcs are `KernelSyms.«main» + 0x16/0x18` at the LEAN kernel image (`KernelPinsDef`
   deviation 1); closed facts are `decide +kernel`, facts uniform in the word read `w` are
   `weak_adm_krfl` (Rocq: `vm_cast_no_check (eq_refl _)`).
4. §9's `Print Assumptions` are dropped (the lint's axiom/sorry ban is the audit).

No Glue premises are carried: the file uses none of `hullRun`/`cycleKillOfL2`/`t2linOfL2`.

**Rocq → Lean name map.**  `taint_del_mem` `taintDelMem`, `taint_upd1_inv` `taintUpd1Inv`,
`taint_step_unfold` `taintStepUnfold`, `taint_step_id` `taintStepId`, `taint_sub` `taintSub`,
`taint_sub_refl` `taintSubRefl`, `inv_ok` `invOk`, `dprov_regw_eq` `dprovRegwEq`,
`dprov_regw_ne` `dprovRegwNe`, `prov_neutralb` `provNeutralb`, `dstep_prov_neutral`
`dstepProvNeutral`, `dprov_neutral_item` `dprovNeutralItem`, `inv_neutral` `invNeutral`,
`inv_neutral_run` `invNeutralRun`, `dsubb` `dsubb`, `existsb_dsrc_elem` `existsbDsrcElem`,
`dsubb_elem` `dsubbElem`, `dsrcs_pos_of_tainted` `dsrcsPosOfTainted`, `regw_step` `regwStep`,
`regw_seg` `regwSeg`, `realizesb` `realizesb`, `regw_seg_sound` `regwSegSound`,
`realizesb_sound` `realizesbSound`, `grp_okb` `grpOkb`, `grp_sound` `grpSound`, `wstep`
`WeakRvwmoPinBridge2.wstep` (duplicated name), `reaches` `reaches` (`RC_stop`/`RC_step`
`reaches.rcStop`/`reaches.rcStep`), `wstep_pstep` `wstepPstep`, `fwalk_S` `fwalkS`,
`reaches_fwalk` `reachesFwalk`, `reaches_inv` `reachesInv`, `wstep_taint` `wstepTaint`,
`wstep_taint_sub` `wstepTaintSub`, `has_ldres_elem` `hasLdresElem`, `dsrcs_pos_ldres`
`dsrcsPosLdres`, `keeps_ldb` `keepsLdb`, `dstep_ld_mono` `dstepLdMono`, `no_regw_of`
`noRegwOf`, `dprov_stable` `dprovStable`, `ld_carrier` `ldCarrier`, `ld_carrier_sound`
`ldCarrierSound`, `ld_item` `ldItem`, `ld_item_load/exload/rmw` `ldItemLoad/Exload/Rmw`,
`base_ok` `baseOk`, `psites` `psites`, `checker_taint_sub_prov_proof`
`checkerTaintSubProvProof`, `pin_seg_pin'` `pinSegPin'`, `la_deps_rd` `laDepsRd`,
`la_deps_rd2` `laDepsRd2`, `la_load_size` `laLoadSize`, `la_grp_ok` `laGrpOk`,
`la_ld_carrier` `laLdCarrier`, `la_base_ok` `laBaseOk`, `la_reaches0` `laReaches0`,
`la_psites` `laPsites`, `la_checker_taint_sub_prov` `laCheckerTaintSubProv`.

**Dropped:** nothing (Rocq 58 declarations; Lean 58).
-/
import Weak.WeakRvwmoPinBridge

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open KernelPinsDef
open WeakRvwmoConf (Dstate dstep)

/-! ## 1. The taint set, as a predicate -/

theorem taintDelMem (r rd : Nat) (t : List Nat) :
    taintMem r (taintDel rd t) = true → r ≠ rd ∧ taintMem r t = true := by
  induction t with
  | nil => intro h; exact absurd h Bool.false_ne_true
  | cons x t ih =>
    intro h
    cases hx : Nat.beq x rd
    · simp only [taintDel, hx, Bool.false_eq_true, ↓reduceIte, taintMem, Bool.or_eq_true] at h
      rcases h with hxr | h
      · have e : x = r := Nat.eq_of_beq_eq_true hxr
        subst e
        refine ⟨fun e => ?_, ?_⟩
        · subst e; exact absurd (Nat.beq_refl x) (by rw [hx]; decide)
        · simp only [taintMem, hxr, Bool.true_or]
      · obtain ⟨h1, h2⟩ := ih h
        exact ⟨h1, by simp only [taintMem, h2, Bool.or_true]⟩
    · simp only [taintDel, hx, ↓reduceIte] at h
      obtain ⟨h1, h2⟩ := ih h
      exact ⟨h1, by simp only [taintMem, h2, Bool.or_true]⟩

/-- THE ONE INVERSION: a register tainted AFTER a destination update is either THE destination,
updated from a tainted source, or a register the update did not touch and which was tainted
BEFORE. -/
theorem taintUpd1Inv (t : List Nat) (rd : Nat) (dec : List Dsrc) (r : Nat) :
    taintMem r (taintUpd1 t (some (rd, dec))) = true →
    (r = rd ∧ srcsTainted t dec = true) ∨ (r ≠ rd ∧ taintMem r t = true) := by
  simp only [taintUpd1]
  cases hs : srcsTainted t dec <;> simp only [Bool.false_eq_true, ↓reduceIte]
  · intro h; exact Or.inr (taintDelMem _ _ _ h)
  · cases hrd : taintMem rd t <;> simp only [Bool.false_eq_true, ↓reduceIte]
    · intro h
      simp only [taintMem, Bool.or_eq_true] at h
      rcases h with h | h
      · exact Or.inl ⟨(Nat.eq_of_beq_eq_true h).symm, trivial⟩
      · by_cases e : r = rd
        · exact Or.inl ⟨e, trivial⟩
        · exact Or.inr ⟨e, h⟩
    · intro h
      by_cases e : r = rd
      · exact Or.inl ⟨e, trivial⟩
      · exact Or.inr ⟨e, h⟩

/-- THE UNFOLDING EQUATION, stated rather than reached by `simp`: never unfold `krole pc` at a
variable `pc` (it bottoms out in the image literal). -/
theorem taintStepUnfold (t : List Nat) (pc : Int) :
    taintStep t pc = taintUpd1 (taintUpd1 t (depsRd (krole pc))) (depsRd2 (krole pc)) := rfl

/-- ... and the update is the IDENTITY when the decoder names no destination. -/
theorem taintStepId (t : List Nat) (pc : Int) :
    depsRd (krole pc) = none → depsRd2 (krole pc) = none → taintStep t pc = t := by
  intro h1 h2
  rw [taintStepUnfold, h1, h2]
  rfl

def taintSub (t t' : List Nat) : Prop :=
  ∀ r, taintMem r t = true → taintMem r t' = true

theorem taintSubRefl (t : List Nat) : taintSub t t := fun _ h => h

/-! ## 2. The invariant, and what one item does to it -/

/-- THE INVARIANT: every register the checker calls tainted carries the row position `j` in
the emission's provenance. -/
def invOk (j : Nat) (s : Dstate) (t : List Nat) : Prop :=
  ∀ r : Nat, taintMem r t = true → j ∈ dprov s r

theorem dprovRegwEq (s : Dstate) (rd : Nat) (srcs : List Dsrc) (k : Option Nat) :
    dprov (dstep s (Wlabel.LRegW rd srcs, k)).1 rd = dsrcsPos s srcs := by
  show dprovSet s.dsProv rd (dsrcsPos s srcs) rd = dsrcsPos s srcs
  simp only [dprovSet, ↓reduceIte]

theorem dprovRegwNe (s : Dstate) (rd : Nat) (srcs : List Dsrc) (k : Option Nat) (r : Nat) :
    r ≠ rd → dprov (dstep s (Wlabel.LRegW rd srcs, k)).1 r = dprov s r := by
  intro hne
  show dprovSet s.dsProv rd (dsrcsPos s srcs) r = s.dsProv r
  simp only [dprovSet, hne, ↓reduceIte]

/-- EVERY OTHER LABEL ARM LEAVES `dsProv` ALONE. -/
def provNeutralb (it : Eitem) : Bool :=
  match it.1 with
  | .LRegW _ _ => false
  | _ => true

theorem dstepProvNeutral (s : Dstate) (it : Eitem) :
    provNeutralb it = true → (dstep s it).1.dsProv = s.dsProv := by
  obtain ⟨l, k⟩ := it
  cases l <;> cases k <;> intro h <;> first | rfl | exact absurd h Bool.false_ne_true

theorem dprovNeutralItem (s : Dstate) (it : Eitem) (r : Nat) :
    provNeutralb it = true → dprov (dstep s it).1 r = dprov s r := by
  intro h
  unfold dprov
  rw [dstepProvNeutral s it h]

theorem invNeutral (j : Nat) (s : Dstate) (t : List Nat) (it : Eitem) :
    provNeutralb it = true → invOk j s t → invOk j (dstep s it).1 t := by
  intro hn hinv r hr
  rw [dprovNeutralItem s it r hn]
  exact hinv r hr

theorem invNeutralRun (j : Nat) (s : Dstate) (t : List Nat) (g : List Eitem) :
    g.all provNeutralb = true → invOk j s t → invOk j (dsRun s g) t := by
  induction g generalizing s with
  | nil => intro _ h; exact h
  | cons it g ih =>
    intro hg hinv
    rw [List.all_cons, Bool.and_eq_true] at hg
    rw [dsRunCons]
    exact ih _ hg.2 (invNeutral _ _ _ _ hg.1 hinv)

/-! ## 3. DEC-7 as a boolean: the emitted sources COVER the decoded ones -/

def dsubb (dec srcs : List Dsrc) : Bool :=
  dec.all (fun x => srcs.any (fun y => decide (x = y)))

theorem existsbDsrcElem (x : Dsrc) (l : List Dsrc) :
    l.any (fun y => decide (x = y)) = true → x ∈ l := by
  intro h
  obtain ⟨y, hy, he⟩ := List.any_eq_true.mp h
  rw [of_decide_eq_true he]
  exact hy

theorem dsubbElem (dec srcs : List Dsrc) (x : Dsrc) :
    dsubb dec srcs = true → x ∈ dec → x ∈ srcs := by
  intro h hx
  exact existsbDsrcElem _ _ (List.all_eq_true.mp h x hx)

/-- A TAINTED DECODED SOURCE IS A POSITION OF THE EMITTED SOURCE LIST. -/
theorem dsrcsPosOfTainted (j : Nat) (s : Dstate) (t : List Nat) (dec srcs : List Dsrc) :
    invOk j s t → dsubb dec srcs = true → srcsTainted t dec = true →
    j ∈ dsrcsPos s srcs := by
  intro hinv hsub ht
  obtain ⟨r, hr, htr⟩ := srcsTaintedReg t dec ht
  exact dsrcsPosReg _ _ _ _ (dsubbElem _ _ _ hsub hr) (hinv r htr)

/-- ONE INSTRUCTION'S REGISTER WRITE, both sides at once. -/
theorem regwStep (j : Nat) (s : Dstate) (t : List Nat) (rd : Nat) (dec srcs : List Dsrc)
    (k : Option Nat) :
    invOk j s t → dsubb dec srcs = true →
    invOk j (dstep s (Wlabel.LRegW rd srcs, k)).1 (taintUpd1 t (some (rd, dec))) := by
  intro hinv hsub r hr
  rcases taintUpd1Inv _ _ _ _ hr with ⟨rfl, hs⟩ | ⟨hne, hr⟩
  · rw [dprovRegwEq]
    exact dsrcsPosOfTainted _ _ _ _ _ hinv hsub hs
  · rw [dprovRegwNe _ _ _ _ _ hne]
    exact hinv r hr

/-! ## 4. One instruction's item group -/

def regwSeg (rd : Nat) (dec : List Dsrc) : List Eitem → Bool
  | [] => false
  | it :: g' =>
    match it.1 with
    | .LRegW rd' srcs => Nat.beq rd' rd && dsubb dec srcs && g'.all provNeutralb
    | _ => regwSeg rd dec g'

def realizesb (d : Option (Nat × List Dsrc)) (g : List Eitem) : Bool :=
  match d with
  | none => g.all provNeutralb
  | some (rd, dec) => regwSeg rd dec g

theorem regwSegSound (j : Nat) (rd : Nat) (dec : List Dsrc) (g : List Eitem) (s : Dstate)
    (t : List Nat) :
    regwSeg rd dec g = true → invOk j s t →
    invOk j (dsRun s g) (taintUpd1 t (some (rd, dec))) := by
  induction g generalizing s with
  | nil => intro h; exact absurd h Bool.false_ne_true
  | cons it g ih =>
    intro hg hinv
    rw [dsRunCons]
    obtain ⟨l, k⟩ := it
    cases l
    case LRegW rd' srcs =>
      simp only [regwSeg, Bool.and_eq_true] at hg
      obtain ⟨⟨hrd, hsub⟩, hn⟩ := hg
      have e : rd' = rd := Nat.eq_of_beq_eq_true hrd
      subst e
      exact invNeutralRun _ _ _ _ hn (regwStep _ _ _ _ _ _ _ hinv hsub)
    all_goals
      simp only [regwSeg] at hg
      exact ih _ hg (invNeutral _ _ _ _ rfl hinv)

theorem realizesbSound (j : Nat) (d : Option (Nat × List Dsrc)) (g : List Eitem) (s : Dstate)
    (t : List Nat) :
    realizesb d g = true → invOk j s t → invOk j (dsRun s g) (taintUpd1 t d) := by
  cases d with
  | none => exact invNeutralRun j s t g
  | some p =>
    obtain ⟨rd, dec⟩ := p
    exact regwSegSound j rd dec g s t

/-- THE GROUP TEST AT A PC: the two decoded destinations, in the order `taintStep` applies
them. -/
def grpOkb (pc : Int) (g1 g2 : List Eitem) : Bool :=
  realizesb (depsRd (krole pc)) g1 && realizesb (depsRd2 (krole pc)) g2

theorem grpSound (j : Nat) (pc : Int) (g1 g2 : List Eitem) (s : Dstate) (t : List Nat) :
    grpOkb pc g1 g2 = true → invOk j s t → invOk j (dsRun s (g1 ++ g2)) (taintStep t pc) := by
  intro h hinv
  unfold grpOkb at h
  rw [Bool.and_eq_true] at h
  rw [dsRunApp, taintStepUnfold]
  exact realizesbSound _ _ _ _ _ h.2 (realizesbSound _ _ _ _ _ h.1 hinv)

/-! ## 5. The walk, with the emission alongside -/

/-- The checker's FALL-THROUGH successor -- `fwalk`'s own step. -/
def WeakRvwmoPinBridge2.wstep (own : Bool) (s : PState) : Option PState :=
  match pstep own s with
  | some (s' :: _) => some s'
  | _ => none

open WeakRvwmoPinBridge2 (wstep)

/-- THE ALIGNMENT. -/
inductive reaches (own : Bool) (stop : Int) : PState → List Eitem → PState → Prop where
  | rcStop (s : PState) : (s.psPc == stop) = true → reaches own stop s [] s
  | rcStep (s : PState) (g1 g2 : List Eitem) (s' : PState) (mid : List Eitem) (s'' : PState) :
      (s.psPc == stop) = false →
      grpOkb s.psPc g1 g2 = true →
      wstep own s = some s' →
      taintSub s'.psT (taintStep s.psT s.psPc) →
      reaches own stop s' mid s'' →
      reaches own stop s (g1 ++ (g2 ++ mid)) s''

theorem wstepPstep (own : Bool) (s s' : PState) :
    wstep own s = some s' → ∃ l, pstep own s = some (s' :: l) := by
  unfold wstep
  cases pstep own s with
  | none => intro h; cases h
  | some l =>
    cases l with
    | nil => intro h; cases h
    | cons s0 l => intro h; cases h; exact ⟨l, rfl⟩

theorem fwalkS (fuel : Nat) (own : Bool) (stop : Int) (s : PState) :
    fwalk (fuel + 1) own stop s
      = if s.psPc == stop then some s.psT
        else match pstep own s with
          | some (s' :: _) => fwalk fuel own stop s'
          | _ => none := rfl

/-- (i) THE WALK IS `fwalk`'S, for every fuel. -/
theorem reachesFwalk (own : Bool) (stop : Int) (s : PState) (g : List Eitem) (s'' : PState) :
    reaches own stop s g s'' →
    ∀ (fuel : Nat) (t : List Nat), fwalk fuel own stop s = some t → t = s''.psT := by
  intro hr
  induction hr with
  | rcStop s hs =>
    intro fuel t hf
    cases fuel with
    | zero => rw [show fwalk 0 own stop s = none from rfl] at hf; cases hf
    | succ fuel =>
      rw [fwalkS, hs, if_pos rfl] at hf
      cases hf; rfl
  | rcStep s g1 g2 s' mid s'' hne _ hw _ _ ih =>
    intro fuel t hf
    cases fuel with
    | zero => rw [show fwalk 0 own stop s = none from rfl] at hf; cases hf
    | succ fuel =>
      obtain ⟨l, hp⟩ := wstepPstep own s s' hw
      rw [fwalkS, hne, hp] at hf
      exact ih fuel t hf

/-- (ii) THE INVARIANT TRAVELS. -/
theorem reachesInv (j : Nat) (own : Bool) (stop : Int) (s : PState) (g : List Eitem)
    (s'' : PState) :
    reaches own stop s g s'' →
    ∀ d0, invOk j d0 s.psT → invOk j (dsRun d0 g) s''.psT := by
  intro hr
  induction hr with
  | rcStop s _ => intro d0 h; exact h
  | rcStep s g1 g2 s' mid s'' _ hg _ hsub _ ih =>
    intro d0 hinv
    rw [← List.append_assoc, dsRunApp]
    apply ih
    intro r hr'
    exact grpSound _ _ _ _ _ _ hg hinv r (hsub r hr')

/-- (iii) THE SUCCESSOR'S TAINT: `pstep` takes the decoded update on every arm but the two that
carry the taint through unchanged. -/
theorem wstepTaint (own : Bool) (s s' : PState) :
    wstep own s = some s' → s'.psT = taintStep s.psT s.psPc ∨ s'.psT = s.psT := by
  intro hw
  obtain ⟨l, hp⟩ := wstepPstep own s s' hw
  obtain ⟨pc, t, rs⟩ := s
  revert hp
  unfold pstep
  dsimp only
  repeat' split
  all_goals intro h
  all_goals first
    | (cases h; done)
    | (cases h; first | exact Or.inl rfl | exact Or.inr rfl)

/-- ... so the alignment's taint obligation is DISCHARGED at every pc whose decoded role names
no destination, and is the identity elsewhere. -/
theorem wstepTaintSub (own : Bool) (s s' : PState) :
    wstep own s = some s' →
    (depsRd (krole s.psPc) = none ∧ depsRd2 (krole s.psPc) = none)
      ∨ s'.psT = taintStep s.psT s.psPc →
    taintSub s'.psT (taintStep s.psT s.psPc) := by
  intro hw h
  rcases h with ⟨h1, h2⟩ | heq
  · rw [taintStepId _ _ h1 h2]
    rcases wstepTaint own s s' hw with he | he
    · rw [he, taintStepId _ _ h1 h2]; exact taintSubRefl _
    · rw [he]; exact taintSubRefl _
  · rw [heq]; exact taintSubRefl _

/-! ## 6. The base case: the load's own destination register -/

theorem hasLdresElem (l : List Dsrc) : hasLdres l = true → Dsrc.DLdRes ∈ l := by
  induction l with
  | nil => intro h; exact absurd h Bool.false_ne_true
  | cons x l ih =>
    cases x with
    | DReg r => intro h; exact List.mem_cons_of_mem _ (ih h)
    | DLdRes => intro _; exact List.mem_cons_self ..

theorem dsrcsPosLdres (s : Dstate) (xs : List Dsrc) (j : Nat) :
    Dsrc.DLdRes ∈ xs → j ∈ s.dsLd → j ∈ dsrcsPos s xs := by
  intro hx hj
  unfold dsrcsPos
  exact List.mem_flatten.mpr ⟨dsrcPos s .DLdRes, List.mem_map_of_mem hx, hj⟩

/-- `dsLd` only grows -- except at `LInstr`. -/
def keepsLdb (it : Eitem) : Bool :=
  match it.1 with
  | .LInstr => false
  | _ => true

theorem dstepLdMono (s : Dstate) (it : Eitem) (i : Nat) :
    keepsLdb it = true → i ∈ s.dsLd → i ∈ (dstep s it).1.dsLd := by
  obtain ⟨l, k⟩ := it
  cases l <;> cases k <;> intro h hi <;>
    first | exact hi | exact List.mem_cons_of_mem _ hi | exact absurd h Bool.false_ne_true

/-- No later item of the group overwrites the carrier. -/
def noRegwOf (rd : Nat) (g : List Eitem) : Bool :=
  g.all (fun it =>
    match it.1 with
    | .LRegW r _ => !(Nat.beq r rd)
    | _ => true)

theorem dprovStable (rd : Nat) (g : List Eitem) (s : Dstate) :
    noRegwOf rd g = true → dprov (dsRun s g) rd = dprov s rd := by
  induction g generalizing s with
  | nil => intro _; rfl
  | cons it g ih =>
    intro hg
    unfold noRegwOf at hg
    rw [List.all_cons, Bool.and_eq_true] at hg
    obtain ⟨h1, h2⟩ := hg
    rw [dsRunCons, ih _ h2]
    obtain ⟨l, k⟩ := it
    cases l
    case LRegW r srcs =>
      cases hb : Nat.beq r rd
      · exact dprovRegwNe _ _ _ _ _ (fun e => Nat.ne_of_beq_eq_false hb e.symm)
      · simp only [hb, Bool.not_true, Bool.false_eq_true] at h1
    all_goals exact dprovNeutralItem _ _ _ rfl

/-- THE LOAD'S GROUP, as a boolean test. -/
def ldCarrier (rd : Nat) : List Eitem → Bool
  | [] => false
  | it :: g' =>
    match it.1 with
    | .LRegW rd' srcs => Nat.beq rd' rd && hasLdres srcs && noRegwOf rd g'
    | .LInstr => false
    | _ => ldCarrier rd g'

theorem ldCarrierSound (j : Nat) (rd : Nat) (g : List Eitem) (s : Dstate) :
    ldCarrier rd g = true → j ∈ s.dsLd → j ∈ dprov (dsRun s g) rd := by
  induction g generalizing s with
  | nil => intro h; exact absurd h Bool.false_ne_true
  | cons it g ih =>
    intro hg hj
    rw [dsRunCons]
    obtain ⟨l, k⟩ := it
    cases l
    case LRegW rd' srcs =>
      simp only [ldCarrier, Bool.and_eq_true] at hg
      obtain ⟨⟨hrd, hld⟩, hn⟩ := hg
      have e : rd' = rd := Nat.eq_of_beq_eq_true hrd
      subst e
      rw [dprovStable _ _ _ hn, dprovRegwEq]
      exact dsrcsPosLdres _ _ _ (hasLdresElem _ hld) hj
    case LInstr => simp only [ldCarrier] at hg; exact absurd hg Bool.false_ne_true
    all_goals
      simp only [ldCarrier] at hg
      exact ih _ hg (dstepLdMono _ _ _ rfl hj)

/-- THE ITEM THAT PUTS THE LOAD'S OWN ROW POSITION INTO `dsLd`. -/
def ldItem (j : Nat) (it : Eitem) : Prop :=
  ∀ s : Dstate, j ∈ (dstep s it).1.dsLd

theorem ldItemLoad (j : Nat) (aq lat : Bool) (b : Int) (tvs : List (Nat × BitVec 8))
    (asrc : List Dsrc) : ldItem j (Wlabel.LLoad aq lat b tvs asrc, some j) :=
  fun _ => List.mem_cons_self ..

theorem ldItemExload (j : Nat) (aq : Bool) (b : Int) (tvs : List (Nat × BitVec 8))
    (asrc : List Dsrc) : ldItem j (Wlabel.LExLoad aq b tvs asrc, some j) :=
  fun _ => List.mem_cons_self ..

theorem ldItemRmw (j : Nat) (aq rl : Bool) (b : Int) (tvs : List (Nat × BitVec 8))
    (dat : List (BitVec 8)) (asrc vsrc : List Dsrc) :
    ldItem j (Wlabel.LRmw aq rl b tvs dat asrc vsrc, some j) :=
  fun _ => List.mem_cons_self ..

/-- THE BASE FACT the top-level theorem consumes. -/
theorem baseOk (j : Nat) (pcL : Int) (pre0 g : List Eitem) (rd : Nat) (lit : Eitem) :
    loadRd pcL = some rd →
    ldItem j lit →
    ldCarrier rd g = true →
    invOk j (dsRun dsInit (pre0 ++ lit :: g)) (pinT0 pcL) := by
  intro hrd hlit hg r hr
  have hr' : taintMem r [rd] = true := by
    unfold pinT0 at hr
    rw [hrd] at hr
    exact hr
  simp only [taintMem, Bool.or_false] at hr'
  have e : rd = r := Nat.eq_of_beq_eq_true hr'
  subst e
  rw [dsRunApp, dsRunCons]
  exact ldCarrierSound _ _ _ _ hg (hlit _)

/-! ## 7. The hypothesis, discharged -/

/-- THE SITE ORACLE, no longer a parameter. -/
def psites (pcL : Int) (own : Bool) (base : List Eitem) (pre : List Eitem) (_ : Eitem)
    (pc' : Int) : Prop :=
  ∃ (mid : List Eitem) (s : PState), pre = base ++ mid ∧ reaches own pc' (pinStart pcL) mid s

theorem checkerTaintSubProvProof (pcL : Int) (j : Nat) (own : Bool) (base : List Eitem)
    (es : List Eitem) :
    invOk j (dsRun dsInit base) (pinT0 pcL) →
    checkerTaintSubProv es (psites pcL own base) pcL j own := by
  intro hbase pre it post pc' t r _ hsite hfw ht
  obtain ⟨mid, s, rfl, hre⟩ := hsite
  rw [dsRunApp]
  apply reachesInv j own pc' _ _ _ hre _ hbase
  rw [← reachesFwalk own pc' _ _ _ hre pinFuel t hfw]
  exact ht

/-- `pinSegPin`, WITH THE HYPOTHESIS GONE. -/
theorem pinSegPin' (GD : Gdexec) (i : Nat) (em : Hemission) (sg : Seg) (pcL pc' : Int)
    (j k : Nat) (own : Bool) (base pre post : List Eitem) (rl : Bool) (a : Int)
    (v : List (BitVec 8)) :
    (∀ jk, jk ∈ rowDeps em.emItems → ((i, jk.1), (i, jk.2)) ∈ GD.gdDeps) →
    sg.sgEntry = (i, j) → sg.sgExit = (i, k) →
    invOk j (dsRun dsInit base) (pinT0 pcL) →
    em.emItems
      = pre ++ (Wlabel.LStore rl a v (depsAddr (krole pc')) (depsVsrc (krole pc')), some k)
        :: post →
    psites pcL own base pre
      (Wlabel.LStore rl a v (depsAddr (krole pc')) (depsVsrc (krole pc')), some k) pc' →
    j < k →
    pinnedb pinFuel pcL (.PDep pc' own) = true →
    segPin GD sg := by
  intro hconf he hx hbase hes hsite hlt hpin
  exact pinSegPin GD i em sg (psites pcL own base) pcL pc' j k own pre post rl a v hconf he hx
    (checkerTaintSubProvProof pcL j own base _ hbase) hes hsite hlt hpin

/-! ## 8. Non-vacuity, on the one stretch computed from real image bytes -/

/-- (i) THE CHECKER'S SIDE: the spin load's decoded destination. -/
theorem laDepsRd :
    depsRd (krole ((KernelSyms.«main» : Int) + 0x16)) = some (15, [.DLdRes, .DReg 14]) := by
  decide +kernel

theorem laDepsRd2 : depsRd2 (krole ((KernelSyms.«main» : Int) + 0x16)) = none := by
  decide +kernel

theorem laLoadSize : wSize (kw ((KernelSyms.«main» : Int) + 0x16)) = 2 := by
  decide +kernel

/-- (ii) THE INSTANCE'S SIDE, COMPUTED: `grpOkb` passes on real bytes. -/
theorem laGrpOk (w : BitVec 32) :
    grpOkb ((KernelSyms.«main» : Int) + 0x16)
      (eadm (admLbls false 200 (ahRead w.toNat laX2))) [] = true := by
  weak_adm_krfl

/-- ... and the same stretch is the LOAD'S CARRIER group. -/
theorem laLdCarrier (w : BitVec 32) :
    ldCarrier 15 (eadm (admLbls false 200 (ahRead w.toNat laX2))) = true := by
  weak_adm_krfl

/-- (iii) THE BASE FACT, on that stretch. -/
theorem laBaseOk (w : BitVec 32) (jj : Nat) (pre0 : List Eitem) (lit : Eitem) :
    ldItem jj lit →
    invOk jj
      (dsRun dsInit (pre0 ++ lit :: eadm (admLbls false 200 (ahRead w.toNat laX2))))
      (pinT0 ((KernelSyms.«main» : Int) + 0x16)) :=
  fun hlit => baseOk _ _ _ _ _ _ laLoadRd hlit (laLdCarrier w)

/-- (iv) THE SITE ORACLE IS INHABITED. -/
theorem laReaches0 (own : Bool) :
    reaches own ((KernelSyms.«main» : Int) + 0x18) (pinStart ((KernelSyms.«main» : Int) + 0x16))
      [] (pinStart ((KernelSyms.«main» : Int) + 0x16)) :=
  .rcStop _ (by decide +kernel)

theorem laPsites (own : Bool) (base : List Eitem) (it : Eitem) :
    psites ((KernelSyms.«main» : Int) + 0x16) own base base it
      ((KernelSyms.«main» : Int) + 0x18) :=
  ⟨[], _, (List.append_nil _).symm, laReaches0 own⟩

/-- (v) AND THE HYPOTHESIS ITSELF, DISCHARGED at that site for the instance's own emission. -/
theorem laCheckerTaintSubProv (w : BitVec 32) (own : Bool) (jj : Nat) (pre0 : List Eitem)
    (lit : Eitem) (es : List Eitem) :
    ldItem jj lit →
    checkerTaintSubProv es
      (psites ((KernelSyms.«main» : Int) + 0x16) own
        (pre0 ++ lit :: eadm (admLbls false 200 (ahRead w.toNat laX2))))
      ((KernelSyms.«main» : Int) + 0x16) jj own :=
  fun hlit => checkerTaintSubProvProof _ _ _ _ _ (laBaseOk w jj pre0 lit hlit)

end Weak
