/-
Weak: **the spinlock plan, ROW-PINNED leaves, part 4** — the NON-VACUITY certificate of the
off-row branch, and the CURSOR finding in formal (toy) form.

Rocq: `iris/AxSpinRow4.v` @ xxvzwolszwmp.

## What this file proves

* §1 CERTIFICATE (concrete; `AxOpsem.OpaxWit`'s hart at `wtP0 cpu rs`, a RAM `memRead` of 4
  bytes at `wtPa`).
  - ON-ROW twin `wtRow`: its item 0 is the read of `wtBase`; the hart is NOT row-stuck
    (`cretOnNotStuck`: `OpaxWit.wtAread` is a read step).
  - OFF-ROW twin `offRow`: identical except item 0 reads `wtBase + 16`.
    `cretOffFirst` (row-free Sail half: the node's first non-administrative label is the read of
    `wtBase`, through every wire), `cretOffRejects` (row half), hence `cretOffStuck`
    (`rowStuckOfFirst`) and `cretOffWpd`: at ANY `AxirisG` / `Axpol` instance and ANY
    postcondition — even `fun _ => False` (`cretOffWpdFalse`) — the hart's `wpdM` holds once the
    graph fact `G` pins hart `i`'s row to `offRow` (`wpdStuck`).  So the premise of `wpdStuck`
    is satisfiable, and not for the matching twin.
* §2 CURSOR FINDING (toy): `twoSitePin` — a row fetching the same c.ret twice with two different
  return sites is position-free return-pinned to NO single landing label.

## Deviations from Rocq

1. O2 STAGE C (`AxSpinRow` deviation 1) and Q12 (`AxSpinRow` deviation 2): `row_stuck_r`'s
   `T img` is a label predicate `pin`; `cretOffKreach` / `cretOffFirst` / `cretOffStuck` /
   `cretOnNotStuck` take any `pin` (the node has no administrative program step, so the pin is
   unused), and `cretOffWpd` calls `wpdStuck` at `pin := fun _ => True` (statement unchanged).  The Lean `OpaxWit` node is a PLAIN data read
   (`wtAk = AK_explicit plain`, as Rocq's `wt_ak`), so its label is a graph `LLoad`; the
   certificate is unchanged.  `fetchNodePstep` concludes `l = rdLabel akIfetch false akSync …`,
   which is Rocq's `LLoad` at `wtAk` (`akIfetch = false` by `rfl`).
2. `init_regstate` ↦ an arbitrary register file `rs` (`AxOpsem` deviation 6): every §1 lemma
   takes `rs`; `cretOffKreach` concludes `∃ rs'` for the reached state.
3. The wire changes the register file (`pinSet`) and the PLIC program (`AxOpsem` deviation 3);
   `cretOffKreach`'s closure is over `∃ rs'`, as Rocq.
4. `invGS_gen HasNoLc Σ` ↦ `[InvGS_gen hlc GF]` (any `hlc`, as `wpdStuck`);
   `WPd s @ MaybeStuck; i {{ Φ }}` ↦ `wpdM rvwmoCatConsistent .MaybeStuck i s Φ`.
5. `Z_to_bv 8 0` ↦ `0#8`; `row !! j` ↦ `row[j]?`.

**Rocq → Lean name map.**  `off_row` `offRow`, `F0` `AxSpinRow4.F0` (a one-letter global,
file-qualified to avoid clashes), `wt_lat` `wtLat`, `cret_off_kreach` `cretOffKreach`,
`cret_off_first` `cretOffFirst`, `wt_base_eq` `wtBaseEq`, `cret_off_rejects` `cretOffRejects`,
`cret_off_stuck` `cretOffStuck`, `cret_on_not_stuck` `cretOnNotStuck`, `cret_off_wpd`
`cretOffWpd`, `cret_off_wpd_False` `cretOffWpdFalse`, `ret_pinned_pf` `retPinnedPf`,
`fetch_at` `fetchAt`, `two_site_row` `twoSiteRow`, `fetch_at_inj` `fetchAtInj`, `two_site_pin`
`twoSitePin`.

**Dropped:** nothing (Rocq 16 definitions/lemmas; Lean 16).  **Not ported:** the
`Print Assumptions` block (the lint's axiom check covers it).
-/
import Weak.AxSpinRow
import Weak.AxCjrWpd

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std MachCSL MachCSL.Stdpp
open Wlabel
open OpaxWit

/-! # 1. The certificate -/

/-- The twin row: the first item reads a DIFFERENT address. -/
def offRow (w0 w1 : BitVec (8 * 4)) : List Lbl :=
  [.LLoad false (wtBase + 16) [0, 0, 0, 0] (WeakInterpProj.wbytes 4 w0),
   .LStore false wtBase (WeakInterpProj.wbytes 4 w1) .WCplain]

/-- The labels the node can emit first. -/
def AxSpinRow4.F0 (l : Wlabel) : Prop :=
  ∃ tvs, l = LLoad (classify wtAk).akSync false (paZ wtPa) tvs []

theorem wtLat : (classify wtAk).akLatest = false := rfl

/-- The closure, by induction on the run. -/
theorem cretOffKreach (pin : Wlabel → Prop) (cpu : CPU) (rs : RegFile) (s2 : Athread) :
    rtc (kstep0 pin) ⟨wtP0 cpu rs, 0⟩ s2 →
    ∃ rs', s2 = ⟨.PHart cpu wtM rs' none ibNone, 0⟩ := by
  have Hcls : ∀ x y : Athread, (∃ rs', x = ⟨.PHart cpu wtM rs' none ibNone, 0⟩) →
      kstep0 pin x y →
      ∃ rs', y = ⟨.PHart cpu wtM rs' none ibNone, 0⟩ := by
    rintro x ⟨py, ky⟩ ⟨rs', rfl⟩ (⟨Hk, d, l, d', Hadm, -, Hps⟩ | ⟨Hk, d, d', Hw⟩)
    · exfalso
      obtain ⟨tvs, -, hl, -⟩ := fetchNodePstep cpu 4 64 wtRreq (fun ans => wtM2 (wtVal ans)) rs'
        ibNone d l _ d' wtPaRam wtLat Hps
      have hc : classify wtRreq.access_kind = ⟨false, false, false⟩ := wtAkPlain
      subst hl
      simp [rdLabel, AxOpsem.lbAdminAx, hc] at Hadm
    · obtain ⟨-, cpu', m', rs'', fn', ib', mm, b, k, Hp, -, -, Hp'⟩ :=
        pstepWireInv _ _ _ _ _ Hw
      simp only at Hp Hk Hp'
      injection Hp with h1 h2 h3 h4 h5
      subst h1 h2 h3 h4 h5 Hk Hp'
      exact ⟨_, rfl⟩
  intro Hr
  induction Hr with
  | refl => exact ⟨rs, rfl⟩
  | tail _ Hyz IH => exact Hcls _ _ IH Hyz

/-- THE ROW-FREE (Sail) HALF: the node's first non-administrative label is the read of
`wtBase`, whatever the wire did. -/
theorem cretOffFirst (pin : Wlabel → Prop) (cpu : CPU) (rs : RegFile) :
    firstEv pin AxSpinRow4.F0 ⟨wtP0 cpu rs, 0⟩ := by
  intro s2 Hr d l p' d' Hps _
  obtain ⟨rs', rfl⟩ := cretOffKreach pin cpu rs s2 Hr
  obtain ⟨tvs, -, hl, -⟩ := fetchNodePstep cpu 4 64 wtRreq (fun ans => wtM2 (wtVal ans)) rs'
    ibNone d l p' d' wtPaRam wtLat Hps
  exact ⟨tvs, by rw [hl]; rfl⟩

theorem wtBaseEq : paZ wtPa = wtBase := rfl

/-- THE ROW HALF: the twin row's item 0 rejects every such label. -/
theorem cretOffRejects (w0 w1 : BitVec (8 * 4)) :
    rowRejects (offRow w0 w1) 0 AxSpinRow4.F0 := by
  rintro lb Hlb l ⟨tvs, rfl⟩ Hfit
  simp only [offRow, List.getElem?_cons_zero, Option.some.injEq] at Hlb
  subst Hlb
  rcases Hfit with ⟨-, Hrd⟩ | ⟨Hx, -⟩ | ⟨Hx, -⟩
  · simp only [wlRd, aident, aidentRd, Option.some.injEq, Prod.mk.injEq, wtBaseEq] at Hrd
    omega
  · simp [wlWr] at Hx
  · simp [wlFence] at Hx

theorem cretOffStuck (pin : Wlabel → Prop) (cpu : CPU) (rs : RegFile)
    (w0 w1 : BitVec (8 * 4)) :
    rowStuckR pin (offRow w0 w1) ⟨wtP0 cpu rs, 0⟩ :=
  rowStuckOfFirst pin _ _ AxSpinRow4.F0 (cretOffFirst pin cpu rs) (cretOffRejects w0 w1)
    (by simp [offRow])

/-- … and the ON-ROW twin is NOT stuck. -/
theorem cretOnNotStuck (pin : Wlabel → Prop) (cpu : CPU) (rs : RegFile)
    (w0 w1 : BitVec (8 * 4)) :
    ¬ rowStuckR pin (wtRow w0 w1) ⟨wtP0 cpu rs, 0⟩ := by
  intro H
  exact (H _ (rtc_refl _)).2.2.1 _ _ (wtAread cpu rs w0 w1)

section certWpd
variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [AxirisG GF] [Axpol]

/-- The off-row WPd at ANY instance, for ANY postcondition, once the graph fact pins hart `i`'s
row to the twin. -/
theorem cretOffWpd (i : Agent) (cpu : CPU) (rs : RegFile) (w0 w1 : BitVec (8 * 4))
    (G : Gdexec → Prop)
    (HG : ∀ GD, rvwmoCatConsistent GD → AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜G GD⌝)
    (Hrow : ∀ GD, G GD → AxOpsem.grow GD i = offRow w0 w1) (Φ : Athread → IProp GF) :
    ⊢ wpdM rvwmoCatConsistent .MaybeStuck i ⟨wtP0 cpu rs, 0⟩ Φ := by
  apply wpdStuck i G HG (fun _ => True) (fun _ _ _ _ => trivial) Φ
  intro GD HGD
  unfold rowStuck
  rw [Hrow GD HGD]
  exact cretOffStuck _ cpu rs w0 w1

theorem cretOffWpdFalse (i : Agent) (cpu : CPU) (rs : RegFile) (w0 w1 : BitVec (8 * 4))
    (G : Gdexec → Prop)
    (HG : ∀ GD, rvwmoCatConsistent GD → AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜G GD⌝)
    (Hrow : ∀ GD, G GD → AxOpsem.grow GD i = offRow w0 w1) :
    ⊢ wpdM rvwmoCatConsistent .MaybeStuck i ⟨wtP0 cpu rs, 0⟩
      (fun _ => (iprop(False) : IProp GF)) :=
  cretOffWpd (GF := GF) i cpu rs w0 w1 G HG Hrow (fun _ => iprop(False))

end certWpd

/-! # 2. The cursor finding (toy form) -/

/-- A position-free return pin: every fetch of the c.ret (`fr`) is followed by the fetch of the
landing site `fl`. -/
def retPinnedPf (row : List Lbl) (fr fl : Lbl) : Prop :=
  ∀ j, row[j]? = some fr → row[j + 1]? = some fl

/-- Fetch-shaped labels at three distinct addresses: the c.ret of holding, acquire's and
release's return sites. -/
def fetchAt (a : Int) : Lbl := .LLoad false a [0, 0] [0#8, 0#8]

def twoSiteRow (h a r : Int) : List Lbl := [fetchAt h, fetchAt a, fetchAt h, fetchAt r]

theorem fetchAtInj (a b : Int) : fetchAt a = fetchAt b → a = b := by
  intro h
  injection h

theorem twoSitePin (h a r : Int) : a ≠ r →
    ¬ ∃ L, retPinnedPf (twoSiteRow h a r) (fetchAt h) (fetchAt L) := by
  rintro Har ⟨L, HL⟩
  have H0 := HL 0 rfl
  have H2 := HL 2 rfl
  simp only [twoSiteRow, List.getElem?_cons_succ, List.getElem?_cons_zero,
    Option.some.injEq] at H0 H2
  exact Har ((fetchAtInj _ _ H0).trans (fetchAtInj _ _ H2).symm)

end Weak
