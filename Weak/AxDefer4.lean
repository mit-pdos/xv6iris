/-
Weak: **constraint F, ledger (item E)** — a ledger indexed by the PROCESSING order is UNSOUND
for K1 (`procLedgerUnsound`); instance side: what a processed set under `Lcanon` contains
(`LcanonWriteBefore`), and the gate-free phase-1 output as a gated todo list (`ordEaTodoLG`)
(AxSL tier).

Rocq: `iris/AxDefer4.v` @ xxvzwolszwmp.

## The Rocq header, in substance

`AxDefer2` showed processing-order and gmo-order ledgers disagree on the stale MP+ctrl graph
`gdefer` (not itself a K1 violation).  Here the FRESH twin `gdefv`:
  hart 1:  (1,0) sd x 1 ; (1,1) fence rw,w ; (1,2) sd.rl-class f 1
  hart 0:  (0,0) r := ld f → 1 ; [bnez r] ; (0,1) d := ld x → 1 (from (1,0)) ;
           (0,2) sd y 1 (ctrl-dependent)
  gmo = [Wx; d; Wf; r; w]
d is again deferred (gmo-before its gate's source r) and it OBSERVES hart 1's plain write of x
BEFORE hart 1 publishes it (`Wf` is gmo-after d): `gdefvViol : gdviolationHart 2 gdefv` — a
genuine K1 violation (the MP+ctrl race).  Yet in the canonical deferring order
(`AxDefer3.Lcanon`, here `Lproc`, d after r) the in-flight ledger has a LEGAL history
(`gdefvLedgerL`: x is released at Wf, ACQUIRED by r along rf, so d's access passes).  Hence
`procLedgerUnsound`: "a legal ledger history in some processing order ⇒ no K1 violation" is
FALSE — the ledger must stay gmo-slot-indexed; under deferral a deferred read's access check
must be made against the ledger AT ITS OWN GMO SLOT.

`LcanonWriteBefore`: every gmo-earlier WRITE is processed earlier under `Lcanon`, for any event
(writes are never deferred: rule 11).  `ordEaTodoLG`: the gate-free phase-1 output is a gated
todo list for any gate structure.

**Fetches (Stage C).** `gdefv` has no fetch row (only 1-byte data loads/stores).

## Deviations from Rocq

1. Vocabulary as `AxDefer2`/`AxDefer3` deviation 1 (`vm_compute` ↦ `decide +kernel`, `≡ₚ` ↦
   `List.Perm`, `!!` ↦ `get?`/`[k]?`, `{[0:=hx; 1:=hf; 2:=hy]}` ↦ nested `insert` over a
   singleton).
2. Rocq's Ltac `acc_list` (enumerate `gacc_addrs` by `vm_compute`) ↦ the Lean-only lemma
   `AxDefer4.accOnly` (an access by `e` whose address list is computed to `[k]` is at `k`).
3. `LcanonGdefv` is proved like `AxDefer3.LcanonGdefer` (deviation 6 there: `List.mergeSort`
   does not reduce in the kernel; uniqueness of sorted permutations).  Same statement.
4. Section `bridge` binds `[InvGS_gen hlc GF]` for any `hlc` (Rocq: `HasNoLc`), as
   `AxDefer.ordEaTodoG`.
5. Lean-only helpers (file-qualified): `AxDefer4.lvGet0/1/2`, `AxDefer4.lvMoves` (per-byte
   moves of `lv` ledgers), `AxDefer4.accOnly`, `AxDefer4.noPub` (no publication of `(1,0)` is
   gmo-before an event gmo-before or at `Wf`).

**Rocq → Lean name map.**  `gdefv` `gdefv`, `gdefv_cat` `gdefvCat`, `gdefv_deferred`
`gdefvDeferred`, `gdefv_gate_real` `gdefvGateReal`, `Lcanon_gdefv` `LcanonGdefv`,
`Lproc_perm_v` `LprocPermV`, `gdefv_viol` `gdefvViol`, `lv` `AxDefer4.lv` (dup), `LHv` `LHv`,
`lv_lookup` `lvLookup`, `acc_list` (Ltac) `AxDefer4.accOnly`, `gdefv_ledger_L` `gdefvLedgerL`,
`proc_ledger_unsound` `procLedgerUnsound`, `Lcanon_write_before` `LcanonWriteBefore`,
`ord_ea_todo_L_G` `ordEaTodoLG`.

**Dropped:** only the `Print Assumptions` blocks (the lint's axiom check covers them).
-/
import Weak.AxDefer3
import Weak.AxViol

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std Iris.Std.PartialMap MachCSL MachCSL.Stdpp
open Lbl AxDefer2

/-! # 1. THE FRESH MP+CTRL GRAPH -/

def gdefv : Gdexec :=
  ⟨⟨vimg, [[LLoad false 1 [2] [b1],
            LLoad false 0 [1] [b1],
            LStore false 2 [b1] .WCplain],
           [LStore false 0 [b1] .WCplain,
            LFence true true false true,
            LStore false 1 [b1] .WCrel]],
    [(1, 0), (0, 1), (1, 2), (0, 0), (0, 2)]⟩,
   [((0, 0), (0, 2))]⟩

theorem gdefvCat : rvwmoCatConsistent gdefv :=
  catConsistentBSound _ (by decide +kernel)

theorem gdefvDeferred : gmoLt gdefv.gdG (0, 1) (0, 0) :=
  (gmoLtBSpec _ _ _).1 (by decide +kernel)

theorem gdefvGateReal : gateReal gdefv gsrcD := by
  intro e r hr
  obtain ⟨He, rfl⟩ := (gsrcDSpec e r).1 hr
  rcases He with rfl | rfl
  · refine ⟨⟨rfl, by decide, rfl, rfl⟩, ⟨_, rfl, rfl⟩, ?_⟩
    rintro ⟨l, hl, hw⟩
    cases hl
    exact absurd hw (by decide)
  · refine ⟨⟨rfl, by decide, rfl, rfl⟩, ⟨_, rfl, rfl⟩, fun _ => ?_⟩
    unfold gdepsRel
    decide

theorem LprocPermV : Lproc.Perm gdefv.gdG.gxGmo := by
  show Lproc.Perm [(1, 0), (0, 1), (1, 2), (0, 0), (0, 2)]
  decide

/-- The canonical deferring order is `Lproc` here too (d after r). -/
theorem LcanonGdefv : Lcanon gdefv gsrcD = Lproc := by
  have Hinj : ∀ a, a ∈ Lproc → ∀ b, b ∈ Lproc →
      AxDefer3.grank gdefv.gdG gsrcD a = AxDefer3.grank gdefv.gdG gsrcD b → a = b := by
    decide +kernel
  have Hsorted : List.Pairwise
      (fun a b => decide (rankLe (AxDefer3.grank gdefv.gdG gsrcD) a b) = true) Lproc := by
    decide +kernel
  refine List.Perm.eq_of_pairwise (fun a b ha hb hab hba => ?_)
    (AxDefer3.rankSortSorted _ _) Hsorted ((rankSortPerm _ _).trans LprocPermV.symm)
  have ha' : a ∈ Lproc := ((rankSortPerm _ _).trans LprocPermV.symm).mem_iff.1 ha
  have h1 := of_decide_eq_true hab
  have h2 := of_decide_eq_true hba
  unfold rankLe at h1 h2
  exact Hinj a ha' b hb (by omega)

/-- Lean-only: no publication of hart 1's `(1,0)` precedes an event that `Wf` does not
gmo-precede. -/
theorem AxDefer4.noPub (e : Geid) (he : gmoLtB gdefv.gdG (1, 2) e = false) :
    ¬ gpubBefore gdefv.gdG (1, 0) e := by
  rintro ⟨⟨i, k⟩, hi, ⟨l, hl, hb⟩, _, hlt⟩
  simp only at hi
  subst hi
  rcases k with _ | _ | _ | k
  · cases hl; exact absurd hb (by decide)
  · cases hl; exact absurd hb (by decide)
  · rw [(gmoLtBSpec _ _ _).2 hlt] at he
    cases he
  · cases hl

/-- THE MP+CTRL RACE: d observes x before hart 1 publishes it. -/
theorem gdefvViol : gdviolationHart 2 gdefv := by
  refine ⟨(1, 0), (0, 1), 0, b1, by decide +kernel,
    (gwbBSpec _ _ _ _).1 (by decide +kernel), ⟨_, rfl, by decide +kernel⟩, trivial,
    ⟨1, rfl, by omega⟩, ⟨0, rfl, by omega⟩, by decide, ?_⟩
  refine .inr ⟨1, b1, (grbBSpec _ _ _ _ _).1 (by decide +kernel),
    by decide +kernel, AxDefer4.noPub _ (by decide +kernel), ?_⟩
  intro ws hws
  have hw1 : gwriteAt gdefv.gdG 1 = some (1, 0) := by decide +kernel
  rw [hw1] at hws
  cases hws
  exact AxDefer4.noPub _ (by decide +kernel)

/-! # 2. A LEGAL LEDGER IN THE PROCESSING ORDER -/

/-- All three bytes tracked (OC = everything, as in `gviolationHart`). -/
def AxDefer4.lv (hx hf hy : Holder) : Ledger :=
  insert (insert ({[2 := hy]} : Ledger) 1 hf) 0 hx

open AxDefer4 in
def LHv : List Ledger :=
  [lv (.held 1) (.held 1) (.held 0), lv (.held 1) (.held 1) (.held 0),
   lv (.pending (1, 2)) (.pending (1, 2)) (.held 0),
   lv (.held 0) (.held 0) (.held 0), lv (.held 0) (.held 0) (.held 0),
   lv (.held 0) (.held 0) (.held 0)]

open AxDefer4

theorem lvLookup (hx hf hy : Holder) (a : Int) :
    get? (lv hx hf hy) a = if a = 0 then some hx else if a = 1 then some hf
                           else if a = 2 then some hy else none := by
  unfold lv
  by_cases h0 : a = 0
  · rw [if_pos h0]; subst h0; exact lookupInsert
  rw [if_neg h0, lookupInsertNe (Ne.symm h0)]
  by_cases h1 : a = 1
  · rw [if_pos h1]; subst h1; exact lookupInsert
  rw [if_neg h1, lookupInsertNe (Ne.symm h1)]
  by_cases h2 : a = 2
  · rw [if_pos h2]; subst h2; exact lookupSingleton
  rw [if_neg h2]
  exact lookupSingletonNe (Ne.symm h2)

theorem AxDefer4.lvGet0 (hx hf hy : Holder) : get? (lv hx hf hy) 0 = some hx := by
  rw [lvLookup]; rfl

theorem AxDefer4.lvGet1 (hx hf hy : Holder) : get? (lv hx hf hy) 1 = some hf := by
  rw [lvLookup]; rfl

theorem AxDefer4.lvGet2 (hx hf hy : Holder) : get? (lv hx hf hy) 2 = some hy := by
  rw [lvLookup]; rfl

theorem AxDefer4.lvMoves (GD : Gdexec) (e : Geid) (hx hf hy hx' hf' hy' : Holder) :
    ledgerMove GD e (some hx) (some hx') → ledgerMove GD e (some hf) (some hf') →
    ledgerMove GD e (some hy) (some hy') →
    ledgerMoves GD e (lv hx hf hy) (lv hx' hf' hy') := by
  intro m0 m1 m2 a
  rw [lvLookup, lvLookup]
  by_cases h0 : a = 0
  · rw [if_pos h0, if_pos h0]; exact m0
  rw [if_neg h0, if_neg h0]
  by_cases h1 : a = 1
  · rw [if_pos h1, if_pos h1]; exact m1
  rw [if_neg h1, if_neg h1]
  by_cases h2 : a = 2
  · rw [if_pos h2, if_pos h2]; exact m2
  rw [if_neg h2, if_neg h2]
  exact .lmSame _

/-- Lean-only (Rocq's `acc_list`): an access by `e` whose address list is `[k]` is at `k`. -/
theorem AxDefer4.accOnly (e : Geid) (k a : Int) (hL : gaccAddrs gdefv.gdG e = [k]) :
    gaccesses gdefv.gdG e a → a = k := by
  intro h
  have h' := (gaccessesAddrs _ _ _).1 h
  rw [hL] at h'
  exact List.mem_singleton.1 h'

theorem gdefvLedgerL : ledgerHistOkL (fun _ => True) 2 gdefv Lproc LHv := by
  refine ⟨rfl, ?_⟩
  intro k e L0 L1 hk h0 h1
  rcases k with _ | _ | _ | _ | _ | k
  · -- Wx (1,0): hart 1 holds x
    cases hk; cases h0; cases h1
    refine ledgerStepOfMoves _ _ _ _ _ _ (ledgerMovesRefl _ _ _) ?_
    intro a _ _ hacc
    rw [accOnly _ 0 a (by decide +kernel) hacc]
    exact .inl (lvGet0 _ _ _)
  · -- Wf (1,2): release x and f
    cases hk; cases h0; cases h1
    have hrel : glblIs gdefv.gdG (1, 2) lbRelw := ⟨_, rfl, by decide +kernel⟩
    refine ledgerStepOfMoves _ _ _ _ _ _
      (lvMoves _ _ _ _ _ _ _ _ (.lmRelease hrel) (.lmRelease hrel) (.lmSame _)) ?_
    intro a _ _ hacc
    rw [accOnly _ 1 a (by decide +kernel) hacc]
    exact .inl (lvGet1 _ _ _)
  · -- r (0,0): acquire x and f along rf from Wf
    cases hk; cases h0; cases h1
    have hacq : acqFrom gdefv (1, 2) (0, 0) :=
      .inl ⟨1, (grfAtBSpec _ _ _ _).1 (by decide +kernel)⟩
    refine ledgerStepOfMoves _ _ _ _ _ _
      (lvMoves _ _ _ _ _ _ _ _ (.lmAcquire _ hacq) (.lmAcquire _ hacq) (.lmSame _)) ?_
    intro a _ _ hacc
    rw [accOnly _ 1 a (by decide +kernel) hacc]
    exact .inr ⟨(1, 2), lvGet1 _ _ _, lvGet1 _ _ _⟩
  · -- d (0,1): reads x, held by hart 0 in THIS order
    cases hk; cases h0; cases h1
    refine ledgerStepOfMoves _ _ _ _ _ _ (ledgerMovesRefl _ _ _) ?_
    intro a _ _ hacc
    rw [accOnly _ 0 a (by decide +kernel) hacc]
    exact .inl (lvGet0 _ _ _)
  · -- w (0,2): y held by hart 0
    cases hk; cases h0; cases h1
    refine ledgerStepOfMoves _ _ _ _ _ _ (ledgerMovesRefl _ _ _) ?_
    intro a _ _ hacc
    rw [accOnly _ 2 a (by decide +kernel) hacc]
    exact .inl (lvGet2 _ _ _)
  · cases hk

/-- THE RE-SORTING CLAIM IS FALSE: a legal ledger in a (canonical, deferring) processing order
does not exclude K1 violations. -/
theorem procLedgerUnsound :
    ¬ (∀ (GD : Gdexec) (L : List Geid) (LH : List Ledger),
        rvwmoCatConsistent GD → L.Perm GD.gdG.gxGmo →
        ledgerHistOkL (fun _ => True) 2 GD L LH → ¬ gdviolationHart 2 GD) := by
  intro H
  exact H gdefv Lproc LHv gdefvCat LprocPermV gdefvLedgerL gdefvViol

/-! # 3. INSTANCE SIDE: what a processed set under `Lcanon` contains -/

/-- Every gmo-EARLIER WRITE is processed earlier, for ANY event (deferred or not). -/
theorem LcanonWriteBefore (GD : Gdexec) (Hcons : rvwmoCatConsistent GD)
    (gsrc : Geid → GSet Geid) (Hreal : gateReal GD gsrc) (n : Nat) (e w : Geid) :
    (Lcanon GD gsrc)[n]? = some e → gisW GD.gdG w = true → gmoLt GD.gdG w e →
    w ∈ takeL (Lcanon GD gsrc) n := by
  intro Hn Hw Hlt
  have Hnd := Hcons.1.1
  obtain ⟨Hwg, _, Hpos⟩ := Hlt
  apply rankSortBefore _ _ n e w Hnd Hn Hwg
  apply grankLt _ _ _ _ Hwg
  left
  have Hkw : gkey GD.gdG gsrc w = gpos GD.gdG w := by
    have h1 := gkeyGeSelf GD.gdG gsrc w
    have h2 : gkey GD.gdG gsrc w ≤ gpos GD.gdG w := by
      apply gkeyLe _ _ _ _ (Nat.le_refl _)
      intro s Hs
      obtain ⟨_, _, h⟩ := gateW GD Hcons gsrc Hreal w s Hs Hw
      omega
    omega
  have := gkeyGeSelf GD.gdG gsrc e
  omega

section bridge
variable [Axpol] {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [AxirisG GF]

/-- The EXISTING (gate-free) phase-1 output is a gated todo list for any gate structure. -/
theorem ordEaTodoLG (GD : Gdexec) (gsrc : Geid → GSet Geid) (φ : Geid → Prop)
    (ea : Sra GF) (na : Mea GF) (L : List Geid) (n : Nat) :
    ordEaTodoL GD ea na L n ⊢ ordEaTodoG GD gsrc φ ea na L n := by
  unfold ordEaTodoL ordEaTodoG
  refine BigSepL.bigSepL_mono_of_forall fun {_ e0} => ?_
  cases get? na e0 with
  | none => exact .rfl
  | some R0 =>
    cases get? ea e0 with
    | none => exact .rfl
    | some flowIn => exact wand_intro sep_elim_left

end bridge

end Weak
