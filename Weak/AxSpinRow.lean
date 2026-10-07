/-
Weak: **the spinlock plan, ROW-PINNED leaves, part 1** — the generic STUCK lemma for `WPd`
and its Sail / row split.

Rocq: `iris/AxSpinRow.v` @ xxvzwolszwmp.

## What this file proves

ROW PINNING is already the semantics: `AxOpsem.astepProg` / `areadStep` check every label's
identity against `row[k]?`, so a hart whose diverted ra / base register makes it emit a label
the row does not have is STUCK, and `wpdM M .MaybeStuck` of a stuck hart is trivial.

* §1 `rowStuckR pin row s`: every PINNED run of `s` in `row` (`AxSpinRow.astepPin pin row`:
  program steps whose label satisfies `pin`, wires, reads) stays at `s`'s position, never
  reaches the row end, never has a read step, and every pinned program step is administrative.
  `wpdMStuck`: if every graph allowed by `G` makes `s` row-stuck (for a `pin` that every
  allowed graph's boot-image pin implies, `Hpin`), then `⊢ wpdM M .MaybeStuck i s Φ` for EVERY
  `Φ` — via `wpdOfClosedRunGM` at `P := ∀ GD, G GD → rowStuck pin GD i s`, `Q := False`;
  administrative steps are row-independent (`adminAnyRow`), so `P` is closed without a
  graph-uniqueness premise.  `wpdStuck` = the `rvwmoCatConsistent` instance.
* §2 THE SAIL / ROW SPLIT: `firstEv pin F s` (row-free: from `s`, along pinned administrative
  steps and wires, the next non-administrative label is in `F`), `rowRejects row k F`
  (row-only: no label of `F` fits the item at `k`); `rowStuckOfFirst`: both, plus
  `s.atK < row.length`, give `rowStuckR pin row s`.

## Deviations from Rocq

1. O2 STAGE C (`AxOpsem` deviation 2): `astep_prog`/`astep_any` have no `T`/`img` parameters
   and no fetch constructor; `adminAnyRow` quantifies only the new row; the `AStep_fetch` cases
   of `adminAnyRow` and `rowStuckOfFirst` are gone (a fetch is an `AStepAdmin` step).
2. Q12 (owner, THE FETCH PIN): a fetch is an administrative step that may return ANY bytes
   unless pinned, so past a fetch no first-event fact can be certified.  The `WPd` step clause
   supplies the pin `WeakAxRealize.fetchPin GD.gdG.gxImg l` (Q8, `wpdOfClosedRunGM`'s `Hclos`).
   Hence `rowStuckR`, `kstep0`, `firstEv`, `rowStuckOfFirst` take a label predicate
   `pin : Wlabel → Prop` (Rocq `T img`): `rowStuckR`'s runs are over the Lean-only
   `AxSpinRow.astepPin pin row` (Rocq `astep_any row T img`; program steps carry `pin l`) and
   its last conjunct only covers `pin`ned steps; `kstep0`'s administrative arm carries `pin l`.
   `rowStuck pin GD i s := rowStuckR pin (grow GD i) s` (Rocq `row_stuck GD i s`, image
   `gx_img (gd_g GD)`); `wpdMStuck` / `wpdStuck` take `pin` and
   `Hpin : ∀ GD l, G GD → fetchPin GD.gdG.gxImg l → pin l` (Rocq: none — its fetches were row
   reads).  A uniform `pin` is needed because `wpdM` re-chooses `GD` at every step; chains
   (`AxSpinVA.rowStuckOfChain`) use `pin := fetchPin img` with all allowed images `= img`;
   fetch-free nodes may use `pin := fun _ => True`.
3. `invGS_gen HasNoLc Σ` ↦ `[InvGS_gen hlc GF]` (any `hlc`, as `wpdOfClosedRunGM`).
   `wpd_stuck` (a Rocq `Definition` alias) is a theorem.
4. TYPES: `is_Some o` ↦ `o.isSome = true`; `row !! k` ↦ `row[k]?`; `@inhabitant (bv 8)` ↦
   `0#8`; `WPd s @ MaybeStuck; i {{ Φ }}` ↦ `wpdM M .MaybeStuck i s Φ`.

**Rocq → Lean name map.**  `row_stuck_r` `rowStuckR`, `lb_admin_wdata` `AxSpinRow.lbAdminWdata`
(duplicated name), `rd_not_admin` `rdNotAdmin`, `wr_not_admin` `wrNotAdmin`, `fence_not_admin`
`fenceNotAdmin`, `admin_any_row` `adminAnyRow`, `row_stuck` `rowStuck`, `wpdM_stuck`
`wpdMStuck`, `wpd_stuck` `wpdStuck`, `fits` `fits`, `kstep0` `kstep0`, `first_ev` `firstEv`,
`row_rejects` `rowRejects`, `kstep0_k` `kstep0K`, `row_stuck_of_first` `rowStuckOfFirst`.
Lean-only (deviation 2): `AxSpinRow.astepPin`.

**Dropped:** nothing (Rocq 15 definitions/lemmas; Lean 15 + 1 Lean-only).  **Not ported:** the
`Print Assumptions` block (the lint's axiom check covers it).
-/
import Weak.AxEpiChainSdLd

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std MachCSL MachCSL.Stdpp
open Wlabel

/-! # 1. Row-stuck states and `wpdStuck` -/

/-- (Lean-only, deviation 2) `astepAny` with every program step's label `pin`ned. -/
def AxSpinRow.astepPin (pin : Wlabel → Prop) (row : List Lbl) (s s' : Athread) : Prop :=
  (∃ l, AxOpsem.astepProg row s l s' ∧ pin l) ∨ awire s s' ∨
  ∃ id K vs, areadStep row s id K ∧ vs.length = aidentN id ∧ s' = K vs

/-- Every pinned run of `s` in `row` is stuck at `s`'s position, before the row end. -/
def rowStuckR (pin : Wlabel → Prop) (row : List Lbl) (s : Athread) : Prop :=
  ∀ s2, rtc (AxSpinRow.astepPin pin row) s s2 →
    s2.atK = s.atK ∧ s.atK < row.length ∧
    (∀ id K, ¬ areadStep row s2 id K) ∧
    (∀ l s3, AxOpsem.astepProg row s2 l s3 → pin l → lbAdmin true l)

theorem AxSpinRow.lbAdminWdata (l : Wlabel) : lbAdmin true l → wlWdata l = none := by
  cases l <;> simp [lbAdmin, wlWdata]

theorem rdNotAdmin (l : Wlabel) (x : Bool × Int × Nat) : wlRd l = some x → ¬ lbAdmin true l := by
  cases l <;> simp [wlRd, lbAdmin]

theorem wrNotAdmin (l : Wlabel) (x : Bool × Int × Nat) : wlWr l = some x → ¬ lbAdmin true l := by
  cases l <;> simp [wlWr, lbAdmin]

theorem fenceNotAdmin (l : Wlabel) (x : Bool × Bool × Bool × Bool) :
    wlFence l = some x → ¬ lbAdmin true l := by
  cases l <;> simp [wlFence, lbAdmin]

/-- An administrative step does not look at the row. -/
theorem adminAnyRow (row : List Lbl) (s : Athread) (l : Wlabel) (s' : Athread) :
    AxOpsem.astepProg row s l s' → lbAdmin true l →
    ∀ row', AxOpsem.astepProg row' s l s' := by
  intro H Hadm row'
  cases H with
  | AStepAdmin p k d l p' d' Ha Hp => exact .AStepAdmin p k d l p' d' Ha Hp
  | AStepWrite p k d l lb p' d' _ Hws _ _ _ =>
    obtain ⟨x, Hx⟩ := Option.isSome_iff_exists.mp Hws
    exact (wrNotAdmin l x Hx Hadm).elim
  | AStepFence p k d l lb p' d' _ Hfs _ _ =>
    obtain ⟨x, Hx⟩ := Option.isSome_iff_exists.mp Hfs
    exact (fenceNotAdmin l x Hx Hadm).elim

section stuck
variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [AxirisG GF] [Axpol]

def rowStuck (pin : Wlabel → Prop) (GD : Gdexec) (i : Agent) (s : Athread) : Prop :=
  rowStuckR pin (AxOpsem.grow GD i) s

/-- THE STUCK LEMMA: a hart that is row-stuck in every allowed graph has `wpdM` for every
postcondition. -/
theorem wpdMStuck (M : Gdexec → Prop) (i : Agent) (G : Gdexec → Prop)
    (HG : ∀ GD, M GD → AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜G GD⌝)
    (pin : Wlabel → Prop)
    (Hpin : ∀ GD l, G GD → WeakAxRealize.fetchPin GD.gdG.gxImg l → pin l)
    (Φ : Athread → IProp GF) (s : Athread) :
    (∀ GD, G GD → rowStuck pin GD i s) → ⊢ wpdM M .MaybeStuck i s Φ := by
  intro Hst
  have Hnord : ∀ GD s1 id K, G GD → (fun s0 => ∀ GD, G GD → rowStuck pin GD i s0) s1 →
      ¬ areadStep (AxOpsem.grow GD i) s1 id K := by
    intro GD s1 id K HGD HP Hrd
    exact (HP GD HGD s1 (rtc_refl _)).2.2.1 id K Hrd
  have Hclos : ∀ GD s1 l s2, G GD → (fun s0 => ∀ GD, G GD → rowStuck pin GD i s0) s1 →
      AxOpsem.astepProg (AxOpsem.grow GD i) s1 l s2 →
      WeakAxRealize.fetchPin GD.gdG.gxImg l →
      wlWdata l = none ∧ s2.atK = s1.atK ∧
        ((fun s0 => ∀ GD, G GD → rowStuck pin GD i s0) s2 ∨ (fun _ => False) s2) := by
    intro GD s1 l s2 HGD HP Hst1 Hfp
    have Hpl := Hpin GD l HGD Hfp
    have Ha := (HP GD HGD s1 (rtc_refl _)).2.2.2 l s2 Hst1 Hpl
    have Hr : ∀ GD', AxSpinRow.astepPin pin (AxOpsem.grow GD' i) s1 s2 := fun GD' =>
      .inl ⟨l, adminAnyRow _ _ _ _ Hst1 Ha _, Hpl⟩
    have Hk := (HP GD HGD s2 (rtc_once (Hr GD))).1
    refine ⟨AxSpinRow.lbAdminWdata l Ha, Hk, .inl ?_⟩
    intro GD' HGD' s3 Hr3
    obtain ⟨Hk3, Hlt, Hn, Ha3⟩ := HP GD' HGD' s3 (rtc_l (Hr GD') Hr3)
    have Hk2 := (HP GD' HGD' s2 (rtc_once (Hr GD'))).1
    exact ⟨by omega, by omega, Hn, Ha3⟩
  have Hwire : ∀ s1 s2, (fun s0 => ∀ GD, G GD → rowStuck pin GD i s0) s1 → awire s1 s2 →
      (fun s0 => ∀ GD, G GD → rowStuck pin GD i s0) s2 ∨ (fun _ => False) s2 := by
    intro s1 s2 HP Hw
    refine .inl ?_
    intro GD HGD s3 Hr3
    have Hr : AxSpinRow.astepPin pin (AxOpsem.grow GD i) s1 s2 := .inr (.inl Hw)
    obtain ⟨Hk3, Hlt, Hn, Ha3⟩ := HP GD HGD s3 (rtc_l Hr Hr3)
    have Hk2 := (HP GD HGD s2 (rtc_once Hr)).1
    exact ⟨by omega, by omega, Hn, Ha3⟩
  have H := wpdOfClosedRunGM (GF := GF) M i G (fun s0 => ∀ GD, G GD → rowStuck pin GD i s0)
    (fun _ => False) Φ HG Hnord Hclos Hwire
  iapply H $$ %s %Hst
  isplit
  · iintro %s2 %Hf
    exact Hf.elim
  · iintro %GD %s1 %HGD %HP %Heq
    have Hlt := (HP GD HGD s1 (rtc_refl _)).2.1
    exact absurd Heq (by omega)

end stuck

/-- The `rvwmoCatConsistent` instance of `wpdMStuck`. -/
theorem wpdStuck {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [AxirisG GF] [Axpol]
    (i : Agent) (G : Gdexec → Prop)
    (HG : ∀ GD, rvwmoCatConsistent GD → AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜G GD⌝)
    (pin : Wlabel → Prop)
    (Hpin : ∀ GD l, G GD → WeakAxRealize.fetchPin GD.gdG.gxImg l → pin l)
    (Φ : Athread → IProp GF) (s : Athread) :
    (∀ GD, G GD → rowStuck pin GD i s) → ⊢ wpdM rvwmoCatConsistent .MaybeStuck i s Φ :=
  wpdMStuck rvwmoCatConsistent i G HG pin Hpin Φ s

/-! # 2. The Sail / row split -/

/-- `l` passes `astepProg` / `areadStep`'s identity check against `lb`. -/
def fits (l : Wlabel) (lb : Lbl) : Prop :=
  ((wlRd l).isSome = true ∧ wlRd l = aidentRd (aident lb)) ∨
  ((wlWr l).isSome = true ∧ wlWr l = aidentWr (aident lb)) ∨
  ((wlFence l).isSome = true ∧ wlFence l = aidentFence (aident lb))

/-- A `pin`ned administrative program step or a wire (both keep the position; row-free). -/
def kstep0 (pin : Wlabel → Prop) (a b : Athread) : Prop :=
  (b.atK = a.atK ∧ ∃ d l d', lbAdmin true l ∧ pin l ∧ pstepProg a.atP d l b.atP d') ∨
  awire a b

/-- ROW-FREE: from `s` (along pinned administrative steps and wires), the next
non-administrative label is in `F`. -/
def firstEv (pin : Wlabel → Prop) (F : Wlabel → Prop) (s : Athread) : Prop :=
  ∀ s2, rtc (kstep0 pin) s s2 →
    ∀ d l p' d', pstepProg s2.atP d l p' d' → ¬ lbAdmin true l → F l

/-- ROW-ONLY: no label of `F` fits the row item at `k`. -/
def rowRejects (row : List Lbl) (k : Nat) (F : Wlabel → Prop) : Prop :=
  ∀ lb, row[k]? = some lb → ∀ l, F l → ¬ fits l lb

theorem kstep0K (pin : Wlabel → Prop) (s s2 : Athread) :
    rtc (kstep0 pin) s s2 → s2.atK = s.atK := by
  intro h
  induction h with
  | refl => rfl
  | tail _ hst ih =>
    rcases hst with ⟨hk, _⟩ | ⟨hk, _⟩ <;> exact hk.trans ih

theorem rowStuckOfFirst (pin : Wlabel → Prop) (row : List Lbl) (s : Athread)
    (F : Wlabel → Prop) :
    firstEv pin F s → rowRejects row s.atK F → s.atK < row.length → rowStuckR pin row s := by
  intro Hfe Hrej Hlt
  have Hkey : ∀ s2, rtc (kstep0 pin) s s2 →
      (∀ id K, ¬ areadStep row s2 id K) ∧
      (∀ l s3, AxOpsem.astepProg row s2 l s3 → pin l → lbAdmin true l ∧ kstep0 pin s2 s3) := by
    intro s2 Hr
    have Hk2 := kstep0K pin _ _ Hr
    refine ⟨?_, ?_⟩
    · rintro id K ⟨lb, Hlb, rfl, Hx, HK⟩
      obtain ⟨l, d, d', Hl, -, Hps, -⟩ :=
        HK (List.replicate (aidentN (aident lb)) 0#8) List.length_replicate
      obtain ⟨x, Hxe⟩ := Option.isSome_iff_exists.mp Hx
      refine Hrej lb (by rw [← Hk2]; exact Hlb) l ?_ ?_
      · exact Hfe s2 Hr d l _ d' Hps (rdNotAdmin l x (by rw [Hl]; exact Hxe))
      · exact .inl ⟨by rw [Hl]; exact Hx, Hl⟩
    · intro l s3 Hst Hpl
      cases Hst with
      | AStepAdmin p k d l p' d' Hadm Hps =>
        exact ⟨Hadm, .inl ⟨rfl, d, l, d', Hadm, Hpl, Hps⟩⟩
      | AStepWrite p k d l lb p' d' Hlb Hws Hwe Hwd Hps =>
        exfalso
        obtain ⟨x, Hx⟩ := Option.isSome_iff_exists.mp Hws
        refine Hrej lb (by rw [← Hk2]; exact Hlb) l ?_ ?_
        · exact Hfe _ Hr d l p' d' Hps (wrNotAdmin l x Hx)
        · exact .inr (.inl ⟨Hws, Hwe⟩)
      | AStepFence p k d l lb p' d' Hlb Hfs Hfe' Hps =>
        exfalso
        obtain ⟨x, Hx⟩ := Option.isSome_iff_exists.mp Hfs
        refine Hrej lb (by rw [← Hk2]; exact Hlb) l ?_ ?_
        · exact Hfe _ Hr d l p' d' Hps (fenceNotAdmin l x Hx)
        · exact .inr (.inr ⟨Hfs, Hfe'⟩)
  have Hreach : ∀ s1 s2, rtc (kstep0 pin) s s1 → rtc (AxSpinRow.astepPin pin row) s1 s2 →
      rtc (kstep0 pin) s s2 := by
    intro s1 s2 H1 H12
    induction H12 with
    | refl => exact H1
    | tail _ Hyz IH =>
      refine rtc_r IH ?_
      rcases Hyz with ⟨l, Hst, Hpl⟩ | Hw | ⟨id, K, vs, Hrd, -, -⟩
      · exact ((Hkey _ IH).2 l _ Hst Hpl).2
      · exact .inr Hw
      · exact ((Hkey _ IH).1 id K Hrd).elim
  intro s2 Hr2
  have Hk := Hreach s s2 (rtc_refl _) Hr2
  exact ⟨kstep0K pin _ _ Hk, Hlt, (Hkey s2 Hk).1,
    fun l s3 Hst Hpl => ((Hkey s2 Hk).2 l s3 Hst Hpl).1⟩

end Weak
