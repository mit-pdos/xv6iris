/-
Weak: **making the lock slice's ownership load-bearing** (AxSL tier) — a racing write to the
protected byte is excluded by token ownership, not by any graph fact.

Rocq: `iris/AxLockRace.v` @ xxvzwolszwmp.

## The Rocq header, in substance

`AxLockAdeq.lock_slice_sound''` is non-vacuous but trivial: its graph is exactly the four events
`[w_x; w_rel; acq; r_x]`, so `w_x` is syntactically the only write to `x` and the load-value
axiom alone gives `r_x`'s value.  This file adds a fifth event, a hart C's write `w_c` to `x`,
and shows the ownership discipline is what excludes it.

  §1  THE KEY LEMMA `ownedWriteExcluded`: a putative write discharging its own flow obligation
      through the owned-write rule (precondition `histAuth γ a 1 Hl_c`) cannot proceed while the
      SAME `(γ, a)` token is tied (`tokTie GD γ a Hl {[e := 1]}`) elsewhere in the chain: the two
      full-fraction `histAuth` pieces clash (`histAuthFullExcl`, `histAgree`'s `1 + 1 ≤ 1` side
      condition, refuted by `Qp.not_add_le_l`).  No graph hypothesis about `w_c` at all.
  §1b THE THIRD RESTING POINT `protInvLockWrelSlotExcl`: between `w_rel` and `acq` the token sits
      inside `protInvLock'` (left disjunct of `ΦLock'` at `w_rel`, `w_rel ∉ D` refuting the
      claimed arm via `claimedDom`); it reduces to the same collision.
  §2  THE SMELL TEST: a machine-checked 3-hart witness `race` (A: W x; fence rw,w; W L=0.
      B: RMW.aq L 0→1; R x.  C: W x=2, gmo-between `w_x` and `w_rel`) that IS
      `rvwmoCatConsistent`, where `r_x` reads `w_c`'s value `b2 ≠ b1`
      (`raceConclusionWouldBeFalse`): without §1 nothing rules this graph out.
  §2b `raceWcExcludedAtWxWrelSlot`: on `race` itself, the excluding premise is
      `ownedWriteExcluded`'s second antecedent `histAuth γ xr 1 Hl_c`.

The remaining assembly (generalising AxLockAdeq §5 to 5 events) is, as in Rocq, not built here.

**Fetches.** Nothing here relies on instruction fetches: `race` has only store/fence/rmw/load
labels (`Lbl` has no fetch constructor); §1/§1b are pure ghost-state facts.

## Deviations from Rocq

1. NAMES: camelCase (map below).  Duplicated Rocq name, file-qualified: `AxLockRace.xr` (also in
   AxSpinU4).  Rocq's `Local Notation B0/B1/B2` ↦ `b0`/`b1`/`b2` directly.
2. VOCABULARY (as AxProtLock deviation 2): `gd_g GD` ↦ `GD.gdG`; `hm !! w` ↦ `get? hm w`;
   `Z` ↦ `Int`; `axlogG Σ hent` ↦ `[AxlogG GF Hent]`; `ax_lockG Σ` ↦ `[AxLockG GF]`; `vmr`
   (`vm_compute; reflexivity`) ↦ `decide +kernel`; `WeakLitmus.b1_ne_b2` ↦ `b1NeB2`.
3. STATEMENT SHAPES (as AxProt deviation 4): `P -∗ Q -∗ False` ↦ `P ∗ Q ⊢ False`; pure
   premises stay `→`.  Section variables `(L x : Z)` of §1b are explicit leading arguments.

**Rocq → Lean name map.**  `hist_auth_full_excl` `histAuthFullExcl`, `owned_write_excluded`
`ownedWriteExcluded`, `prot_inv_lock_wrel_slot_excl` `protInvLockWrelSlotExcl`, `xr`
`AxLockRace.xr`, `Lr` `lr`, `race` `race`, `w_x_r` `wXR`, `w_rel_r` `wRelR`, `acq_r` `acqR`,
`r_x_r` `rXR`, `w_c_r` `wCR`, `race_cat` `raceCat`, `race_rx_reads_wc` `raceRxReadsWc`,
`race_rf_is_wc` `raceRfIsWc`, `race_conclusion_would_be_false` `raceConclusionWouldBeFalse`,
`race_wc_excluded_at_wx_wrel_slot` `raceWcExcludedAtWxWrelSlot`.

**Not ported:** the `Print Assumptions` audits (the lint's axiom check covers them).
-/
import Weak.AxProtLock
import Weak.AxToken
import Weak.AxGhost
import Weak.AxGraphWit
import Weak.AxGraphDec
import Weak.WeakLitmus
import MachCSL.QpLemmas
import Iris.ProofMode

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std Iris.Std.PartialMap MachCSL MachCSL.Stdpp
open Lbl

/-! # 1. THE KEY LEMMA: token exclusivity excludes a racing owned write -/

section KeyLemma

variable {GF : BundledGFunctors} [AxlogG GF Hent]

/-- Two full-fraction tokens on the SAME `(γ, a)` cell never coexist. -/
theorem histAuthFullExcl (γ : GName) (a : Int) (H1 H2 : List Hent) :
    histAuth (GF := GF) γ a 1 H1 ∗ histAuth γ a 1 H2 ⊢ False := by
  refine (histAgree γ a 1 1 H1 H2).trans ?_
  iintro %h
  exact (Qp.not_add_le_l 1 1 h.2).elim

/-- THE KEY LEMMA: a tied `(γ, a)` token refutes any other full `histAuth γ a 1 _`. -/
theorem ownedWriteExcluded (GD : Gdexec) (γ : GName) (a : Int) (Hl : List Hent) (e : Geid)
    (Hl_c : List Hent) :
    tokTie (GF := GF) GD γ a Hl {[e := (1 : Qp)]} ∗ histAuth γ a 1 Hl_c ⊢ False := by
  unfold tokTie
  iintro ⟨⟨Htok, -⟩, Hauth⟩
  ihave Hauth' := (tokSingleton γ a Hl e 1).1 $$ Htok
  iapply histAuthFullExcl γ a Hl Hl_c
  isplitl [Hauth']
  · iexact Hauth'
  · iexact Hauth

end KeyLemma

/-! # 1b. THE THIRD RESTING POINT: the token folded into `ΦLock'` -/

section ThirdRestingPoint

variable {GF : BundledGFunctors} [AxlogG GF Hent] [AxLockG GF]

theorem protInvLockWrelSlotExcl (L x : Int) (γ γc : GName) (GD : Gdexec) (s D : GSet Geid)
    (hm : GMapF Geid (List Hent)) (w_rel : Geid) (Hh Hl_c : List Hent) :
    w_rel ∈ s → w_rel ∉ D → get? hm w_rel = some Hh →
    gwritesByte GD.gdG w_rel L b0 →
    protInvLock' (GF := GF) L x γ γc GD s D hm ∗ histAuth γ x 1 Hl_c ⊢ False := by
  intro hin hninD hhm hwb
  have hHh : (get? hm w_rel).getD [] = Hh := by rw [hhm]; rfl
  iintro ⟨Hinv, Hauth⟩
  icases (protInvLockUnfold' L x γ γc GD s D hm).1 $$ Hinv with ⟨Hc, -, Hlocks⟩
  icases (BigSepS.bigSepS_delete
    (Φ := fun e => ΦLock' L x γ γc GD e ((get? hm e).getD [])) hin).1 $$ Hlocks
    with ⟨Hw, -⟩
  icases AxProtLock.ΦLock'Open L x γ γc GD w_rel _ Hh hHh hwb $$ Hw
    with ((Htie | ⟨-, Hauth'⟩) | Hcl)
  · iapply ownedWriteExcluded GD γ x Hh w_rel Hl_c
    isplitl [Htie]
    · iexact Htie
    · iexact Hauth
  · iapply histAuthFullExcl γ x Hh Hl_c
    isplitl [Hauth']
    · iexact Hauth'
    · iexact Hauth
  · ihave %hinD := claimedDom γc D w_rel $$ [$Hc $Hcl]
    exact (hninD hinD).elim

end ThirdRestingPoint

/-! # 2. THE SMELL TEST: a consistent 5-event race witness

H0 (A): W x=b1 (0,0); fence rw,w (0,1); W L=b0 (0,2).
H1 (B): RMW.aq L: b0→b1 (1,0); R x (1,1).
H2 (C): W x=b2 (2,0) — the independent racing write.
gmo = [w_x; w_c; w_rel; acq; r_x] — writes: w_x=1, w_c=2, w_rel=3, acq=4.  `r_x` reads write
index 2 = `w_c`. -/

def AxLockRace.xr : Int := 0
def lr : Int := 1

def race : Gdexec :=
  AxGraphWit.mkgd
    [[LStore false AxLockRace.xr [b1] .WCplain,
      LFence true true false true,
      LStore false lr [b0] .WCplain],
     [LRmw true false lr [3] [b0] [b1] .WCplain,
      LLoad false AxLockRace.xr [2] [b2]],
     [LStore false AxLockRace.xr [b2] .WCplain]]
    [(0, 0), (2, 0), (0, 2), (1, 0), (1, 1)]
    []

def wXR : Geid := (0, 0)
def wRelR : Geid := (0, 2)
def acqR : Geid := (1, 0)
def rXR : Geid := (1, 1)
def wCR : Geid := (2, 0)

theorem raceCat : rvwmoCatConsistent race :=
  catConsistentBSound _ (by decide +kernel)

/-- `r_x` reads b2 (write index 2, `w_c`'s value). -/
theorem raceRxReadsWc : greadsByte race.gdG rXR AxLockRace.xr 2 b2 :=
  (grbBSpec _ _ _ _ _).1 (by decide +kernel)

/-- `w_c` IS the rf-source. -/
theorem raceRfIsWc : grfAt race.gdG AxLockRace.xr wCR rXR :=
  (grfAtBSpec _ _ _ _).1 (by decide +kernel)

/-- THE SMELL TEST: `lock_slice_sound''`'s conclusion shape is FALSE on `race`. -/
theorem raceConclusionWouldBeFalse :
    ¬ (∀ t v, greadsByte race.gdG rXR AxLockRace.xr t v → v = b1) := by
  intro hall
  exact b1NeB2 (hall 2 b2 raceRxReadsWc).symm

/-! # 2b. The smell test made precise: the excluding premise on `race` itself -/

theorem raceWcExcludedAtWxWrelSlot {GF : BundledGFunctors} [AxlogG GF Hent] (γ : GName)
    (Hl_c : List Hent) :
    tokTie (GF := GF) race γ AxLockRace.xr [(wXR, b1)] {[wXR := (1 : Qp)]} ∗
      histAuth γ AxLockRace.xr 1 Hl_c ⊢ False :=
  ownedWriteExcluded race γ AxLockRace.xr [(wXR, b1)] wXR Hl_c

end Weak
