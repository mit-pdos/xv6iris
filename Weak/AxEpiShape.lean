/-
Weak: **discharging `epilogueRetTargetSpillReload`'s EMISSION SHAPE residuals**
(`HwriteShape`/`HreadShape`/`HpoSdLd`/`HmidNoW`, plus the length facts `Hlen8`/`HtsLen`/`HvsLen`)
from the row/graph machinery.

Rocq: `iris/AxEpiShape.v` @ xxvzwolszwmp.

## What this file proves

THE BRIDGE is definitional: `gxLbl G e := (G.gxProg[e.1]?).bind (·[e.2]?)`, so given
`GD.gdG.gxProg[i]? = some row`, `gxLbl GD.gdG (i, k) = row[k]?` (`gxLblOfProg`/`gxLblToProg`).
`AxFetch3b.afCsdspRowShape row kSd a` / `afCldspRowShape row kLd a` pin the DATA node's identity
(`aident`-equal to `IWrite false a 8` / `IRead false a 8`); inverting `aident`
(`aidentInvStore`/`aidentInvLoad`) gives the labels up to the write's class/bytes and the read's
timestamps/bytes, which ride through as the row projections `epiWriteVal`/`epiWriteCls`/
`epiReadTs`/`epiReadVal`.  `epilogueShapeOfRow` packages the four target facts (and the three
length facts — `HtsLen` from `gwf`'s label-shape clause) for `rSd := (i, kSd)`,
`rLd := (i, kLd)`; `HmidNoW` comes from the "register-only middle" `epiMidRegOnly` (no WRITE
label strictly between the two data nodes).  `epilogueRetTargetSpillReloadOfRow` is the
capstone corollary: `epilogueRetTargetSpillReload` with those residuals replaced by the row
premises (`Hwelldef`, never consumed, fed by `rtc` reflexivity at a thread `t0`).

## Deviations from Rocq

1. O2 STAGE C (rows have no fetch items; re-indexed): Rocq's shapes put the FETCH at `k` and the
   DATA at `S k`, and carry the fetch pc; Lean's `afCsdspRowShape row k a`/`afCldspRowShape row k
   a` (`AxFetch3b` deviation 2) put the DATA at `k` and have no pc.  Hence: the `pc_sd`/`pc_ld`
   binders are dropped; every `S k_sd`/`S k_ld` becomes `kSd`/`kLd` (the events are
   `(i, kSd)`/`(i, kLd)`; `epiWriteVal row k` etc. look at `row[k]?`); `epiMidRegOnly row kSd kLd`
   quantifies over `kSd < p < kLd` (Rocq `S k_sd < p ≤ k_ld`: the window strictly between the two
   data nodes in both cases — Rocq's upper end `k_ld` was the reload's fetch, which no longer
   exists).
2. NAMES / VOCABULARY: camelCase; none in `notes/weak-port-dupnames.json`.  `row !! k` ↦
   `row[k]?`, `lb_is_w` ↦ `lbIsW`, `gx_prog (gd_g GD) !! i` ↦ `GD.gdG.gxProg[i]?`, agents are
   `Nat`; the Sail/graph/ownership vocabulary of the corollary is `AxEpilogue`'s (its deviations
   3-5).  `hent` ↦ the auto-bound `Hent` of `[AxlogG GF Hent]`.
3. CONTEXT: the section's `invGS_gen`/`axirisG` instances are used by nothing and dropped (as
   `AxEpilogue` deviation 5); `γ`, `GD`, `Hcons` are explicit arguments.
4. The capstone is stated `⊢ A -∗ B -∗ ⌜φ⌝` (as `AxEpilogue` deviation 6).

**Rocq → Lean name map.**  `aident_inv_store` `aidentInvStore`, `aident_inv_load`
`aidentInvLoad`, `gx_lbl_of_prog` `gxLblOfProg`, `gx_lbl_to_prog` `gxLblToProg`,
`epi_mid_reg_only` `epiMidRegOnly`, `epi_write_val` `epiWriteVal`, `epi_write_cls`
`epiWriteCls`, `epi_read_ts` `epiReadTs`, `epi_read_val` `epiReadVal`, `epilogue_shape_of_row`
`epilogueShapeOfRow`, `epilogue_ret_target_spill_reload_of_row`
`epilogueRetTargetSpillReloadOfRow`.

**Dropped:** nothing (Rocq 11 declarations; Lean 11).
-/
import Weak.AxEpilogue
import Weak.AxFetch3b

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std Iris.Std.PartialMap MachCSL MachCSL.Stdpp
open Sail LeanRV64D LeanRV64D.Functions

/-! # 1. Inverting `aident` against a fixed identity -/

/-- The only label whose `aident` is `IWrite rl0 a0 n0` is an `LStore`. -/
theorem aidentInvStore (lb : Lbl) (rl0 : Bool) (a0 : Int) (n0 : Nat) :
    aident lb = .IWrite rl0 a0 n0 →
    ∃ (Vs : List (BitVec 8)) (kCls : WmClass), lb = .LStore rl0 a0 Vs kCls ∧ Vs.length = n0 := by
  cases lb with
  | LStore rl base vs k =>
    intro H
    simp only [aident, AidentT.IWrite.injEq] at H
    obtain ⟨h1, h2, h3⟩ := H
    subst h1 h2 h3
    exact ⟨vs, k, rfl, rfl⟩
  | _ => intro H; simp [aident] at H

/-- The only label whose `aident` is `IRead aq0 a0 n0` is an `LLoad`. -/
theorem aidentInvLoad (lb : Lbl) (aq0 : Bool) (a0 : Int) (n0 : Nat) :
    aident lb = .IRead aq0 a0 n0 →
    ∃ (ts : List Nat) (vs : List (BitVec 8)), lb = .LLoad aq0 a0 ts vs ∧ vs.length = n0 := by
  cases lb with
  | LLoad aq base ts vs =>
    intro H
    simp only [aident, AidentT.IRead.injEq] at H
    obtain ⟨h1, h2, h3⟩ := H
    subst h1 h2 h3
    exact ⟨ts, vs, rfl, rfl⟩
  | _ => intro H; simp [aident] at H

/-! # 2. The graph's embedding of a hart's row -/

theorem gxLblOfProg (G : Gexec) (i : Nat) (row : List Lbl) (k : Nat) (lb : Lbl) :
    G.gxProg[i]? = some row → row[k]? = some lb → gxLbl G (i, k) = some lb := by
  intro Hp Hr
  simp only [gxLbl, Hp, Option.bind_some]
  exact Hr

theorem gxLblToProg (G : Gexec) (i : Nat) (row : List Lbl) (k : Nat) (lb : Lbl) :
    G.gxProg[i]? = some row → gxLbl G (i, k) = some lb → row[k]? = some lb := by
  intro Hp Hl
  simp only [gxLbl, Hp, Option.bind_some] at Hl
  exact Hl

/-! # 3. The register-only middle and the row projections -/

/-- No row item strictly between the spill's data node `kSd` and the reload's data node `kLd`
is a WRITE (deviation 1). -/
def epiMidRegOnly (row : List Lbl) (kSd kLd : Nat) : Prop :=
  ∀ p lb, kSd < p → p < kLd → row[p]? = some lb → lbIsW lb = false

def epiWriteVal (row : List Lbl) (k : Nat) : List (BitVec 8) :=
  match row[k]? with
  | some (.LStore _ _ vs _) => vs
  | _ => []

def epiWriteCls (row : List Lbl) (k : Nat) : WmClass :=
  match row[k]? with
  | some (.LStore _ _ _ kc) => kc
  | _ => .WCplain

def epiReadTs (row : List Lbl) (k : Nat) : List Nat :=
  match row[k]? with
  | some (.LLoad _ _ ts _) => ts
  | _ => []

def epiReadVal (row : List Lbl) (k : Nat) : List (BitVec 8) :=
  match row[k]? with
  | some (.LLoad _ _ _ vs) => vs
  | _ => []

/-! # 4. The packaging lemma and the capstone corollary -/

theorem epilogueShapeOfRow (GD : Gdexec) (Hcons : rvwmoCatConsistent GD)
    (i : Nat) (row : List Lbl) (kSd kLd : Nat) (a : Int)
    (Hprog : GD.gdG.gxProg[i]? = some row)
    (HshapeSd : afCsdspRowShape row kSd a)
    (HshapeLd : afCldspRowShape row kLd a)
    (HkLt : kSd < kLd)
    (Hmid : epiMidRegOnly row kSd kLd) :
    (epiWriteVal row kSd).length = 8 ∧
    (epiReadTs row kLd).length = 8 ∧
    (epiReadVal row kLd).length = 8 ∧
    gxLbl GD.gdG (i, kSd) = some (.LStore false a (epiWriteVal row kSd) (epiWriteCls row kSd)) ∧
    gxLbl GD.gdG (i, kLd) = some (.LLoad false a (epiReadTs row kLd) (epiReadVal row kLd)) ∧
    WeakRvwmoGraph.gpo GD.gdG (i, kSd) (i, kLd) ∧
    (∀ (j : Nat) w v, j < 8 → gwritesByte GD.gdG w (a + (j : Int)) v →
      WeakRvwmoGraph.gpo GD.gdG (i, kSd) w → WeakRvwmoGraph.gpo GD.gdG w (i, kLd) → False) := by
  obtain ⟨lbdSd, HrowdSd, HiddSd⟩ := HshapeSd
  obtain ⟨lbdLd, HrowdLd, HiddLd⟩ := HshapeLd
  obtain ⟨Vs, kCls, HlbdSd, HlenVs⟩ := aidentInvStore lbdSd false a 8 HiddSd
  obtain ⟨ts0, vs0, HlbdLd, Hlenvs0⟩ := aidentInvLoad lbdLd false a 8 HiddLd
  subst HlbdSd HlbdLd
  have Hev : epiWriteVal row kSd = Vs := by simp only [epiWriteVal, HrowdSd]
  have Hec : epiWriteCls row kSd = kCls := by simp only [epiWriteCls, HrowdSd]
  have Het : epiReadTs row kLd = ts0 := by simp only [epiReadTs, HrowdLd]
  have Hevr : epiReadVal row kLd = vs0 := by simp only [epiReadVal, HrowdLd]
  have HglSd := gxLblOfProg GD.gdG i row kSd _ Hprog HrowdSd
  have HglLd := gxLblOfProg GD.gdG i row kLd _ Hprog HrowdLd
  have Hlents0 : ts0.length = 8 := by
    have Hlw := Hcons.1.2.2 i row kLd _ Hprog HrowdLd
    simp only [] at Hlw
    omega
  rw [Hev, Hec, Het, Hevr]
  refine ⟨HlenVs, Hlents0, Hlenvs0, HglSd, HglLd, ?_, ?_⟩
  · exact ⟨rfl, HkLt, by rw [HglSd]; rfl, by rw [HglLd]; rfl⟩
  · intro j w v _ Hwb Hpo1 Hpo2
    obtain ⟨wi, wk⟩ := w
    obtain ⟨Hw1eq, Hlt1, _, _⟩ := Hpo1
    obtain ⟨Hw2eq, Hlt2, _, _⟩ := Hpo2
    simp only [] at Hw1eq Hlt1 Hw2eq Hlt2
    subst Hw1eq
    obtain ⟨l, base, vsw, j', Hgl, Hwr, _, _⟩ := Hwb
    have HrowW := gxLblToProg GD.gdG _ row wk l Hprog Hgl
    have Hnw := Hmid wk l Hlt1 Hlt2 HrowW
    have Hwtrue := lbWrIsW l (base, vsw) Hwr
    rw [Hnw] at Hwtrue
    exact Bool.false_ne_true Hwtrue

section epiShape

variable {GF : BundledGFunctors} [AxlogG GF Hent]

/-- THE CAPSTONE COROLLARY: `epilogueRetTargetSpillReload` with its emission-shape residuals
(and the three length facts) replaced by the row premises; `Hwelldef` fed by reflexivity at
`t0`. -/
theorem epilogueRetTargetSpillReloadOfRow (γ : GName) (GD : Gdexec)
    (Hcons : rvwmoCatConsistent GD)
    (i : Nat) (row : List Lbl) (kSd kLd : Nat) (a : Int)
    (Hprog : GD.gdG.gxProg[i]? = some row)
    (HshapeSd : afCsdspRowShape row kSd a)
    (HshapeLd : afCldspRowShape row kLd a)
    (HkLt : kSd < kLd)
    (Hmid : epiMidRegOnly row kSd kLd)
    (t0 : Athread)
    (HsBefore : List (List Hent)) (HlensBefore : HsBefore.length = 8)
    (HwrBefore : ∀ (j : Nat) (H : List Hent), HsBefore[j]? = some H →
      ∀ p, p ∈ H → gwritesByte GD.gdG p.1 (a + (j : Int)) p.2)
    (HchBefore : ∀ (j : Nat) (H : List Hent), HsBefore[j]? = some H →
      chainWith (gmoLt GD.gdG) (H.map Prod.fst))
    (HownBefore : ∀ (j : Nat) (H : List Hent), HsBefore[j]? = some H →
      ∀ w v, gwritesByte GD.gdG w (a + (j : Int)) v → WeakRvwmoGraph.gpo GD.gdG w (i, kSd) →
        w ∈ H.map Prod.fst)
    (HlinkBefore : ∀ (j : Nat) (H : List Hent) wlast vlast, HsBefore[j]? = some H →
      H.getLast? = some (wlast, vlast) → WeakRvwmoGraph.gpo GD.gdG wlast (i, kSd))
    (ra : BitVec 5) (Hra : ra.toNat ≠ 0) (sM : ExecSt)
    (Hpriv : sM.regs .cur_privilege = .Machine) (Hsec : sM.regs .mseccfg = 0#64)
    (HC : (_get_Misa_C (sM.regs .misa) == 1#1) = true)
    (Hbridge : sM.gpr ra = wordOfBytes 8 (epiWriteVal row kSd)) :
    ⊢ (∀ (j : Nat) (w : Geid) (v : BitVec 8), ⌜gwritesByte GD.gdG w (a + (j : Int)) v⌝ -∗
        ⌜gmoLt GD.gdG w (i, kLd)⌝ -∗
        ∃ H' : List Hent, ⌜w ∈ H'.map Prod.fst⌝ ∗ histSnap (GF := GF) γ (a + (j : Int)) H') -∗
      tokn γ GD a (writenHist (i, kSd) (epiWriteVal row kSd) HsBefore)
        ({[(i, kSd) := (1 : Qp)]} : GMapF Geid Qp) -∗
      ⌜graphValue GD (i, kLd) = some (epiWriteVal row kSd) ∧
        execEff (execute (.JALR (zeros (n := 12), .Regidx ra, zreg))) sM =
          some (RETIRE_SUCCESS,
            sM.setReg .nextPC (WeakLeafMret.retPc (wordOfBytes 8 (epiWriteVal row kSd))), []) ∧
        (sM.setReg .nextPC (WeakLeafMret.retPc (wordOfBytes 8 (epiWriteVal row kSd)))).regs
            .nextPC =
          WeakLeafMret.retPc (wordOfBytes 8 (epiWriteVal row kSd))⌝ := by
  obtain ⟨HlenVs, Hlents0, Hlenvs0, HglSd, HglLd, Hpo, Hnow⟩ :=
    epilogueShapeOfRow GD Hcons i row kSd kLd a Hprog HshapeSd HshapeLd HkLt Hmid
  exact epilogueRetTargetSpillReload γ GD Hcons row t0 t0 (FromMathlib.Relation.ReflTransGen.refl)
    (i, kSd) (i, kLd) a false (epiWriteCls row kSd) (epiWriteVal row kSd) HlenVs HglSd
    false (epiReadTs row kLd) (epiReadVal row kLd) HglLd Hlents0 Hlenvs0 Hpo
    HsBefore HlensBefore HwrBefore HchBefore HownBefore HlinkBefore Hnow
    ra Hra sM Hpriv Hsec HC Hbridge

end epiShape

end Weak
