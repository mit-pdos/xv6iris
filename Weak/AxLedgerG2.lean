/-
Weak: **soundness checks of the frozen-slot ledger** (`AxLedgerG`) against `AxDefer`'s
counterexamples, and a POSITIVE deferred-read certificate (AxSL tier, pure).

Rocq: `iris/AxLedgerG2.v` @ xxvzwolszwmp.

## The Rocq header, in substance

§1 `gdefv` (AxDefer4: d = ld x reads hart 1's plain `sd x` BEFORE its publication; d is
   deferred past its gate source r = ld f; a genuine K1 violation, yet the PROCESSING-order
   ledger accepts it): `gdefvFrozenCatches` — in EVERY state of `lfzOk` (any OC ∋ x, any
   history, any validated set) in which d's slot is committed, d's FROZEN-slot check FAILS:
   slot 1 holds x for hart 1 (its plain write at slot 0 is validated whenever anything is).  So
   d's deferred flow equation (`AxLedgerG.ledgerDeferG`) is unprovable, and `gdefvNoLedger` /
   `gdefvNoFull`: no gmo ledger history, hence no completed walk, for any OC covering the plain
   writes.
§2 `gdefer` (AxDefer2: same program, d reads the STALE init value; no violation):
   `gdeferNoFull` — the new invariant rejects it too (d reads x while hart 1 owns it:
   `AxDefer2.ledgerGmoNoneGdefer`).  This is CORRECT, not a completeness bug: `gdefer` and
   `gdefv` are two executions of ONE program, and `gdefv` is a violation — the plain-load gate
   does not order the data load (MP+ctrl).
§3 POSITIVE `gdefo`: the same shape with the deferred read on a byte hart 0 OWNS (z, private):
   consistent (`gdefoCat`), d deferred past its gate source (`gdefoDeferred`), and the WHOLE
   frozen-slot walk in the canonical order `Lcanon = [Wx; Wf; r; d; w]` built from
   `AxLedgerG`'s step lemmas — Wx commits slots 0 (d, frozen) and 1; Wf releases x; r ACQUIRES x
   along rf from the release; d's frozen check at slot 0 (z held by hart 0 since the initial
   ledger); w commits — ending in `lfzOk` at the full set (`gdefoWalk`) and hence
   `gdefoLedger : ledgerHistOkList` (gmo-indexed).  A SATISFIABILITY CERTIFICATE of `lfzOk` with
   a genuinely deferred read.

**Fetches (Stage C).** None of the three graphs has a fetch row (1-byte data accesses only).

## Deviations from Rocq

1. Vocabulary as `AxLedgerG`/`AxDefer2` (`vm_compute` ↦ `decide +kernel`/`rfl`, `list_to_set`
   ↦ `LawfulSet.ofList`, `!!` ↦ `get?`/`[k]?`, `{[0:=hx; 2:=..; 3:=..]}` ↦ nested `insert`
   over a singleton, as `AxDefer4.lv`).  Rocq's notations `r_e d_e …` are `AxDefer2.rE …`.
2. LIST ASSOCIATIVITY (as `AxLedgerG` deviation 2): `lhCurExt` is stated on Lean's left
   parse `(LH ++ replicate m c) ++ [L']` (the same list); it is `lhCurApp`.
3. Rocq's Ltacs `acc_o` (= `acc_list`), `feed`, `oc_vac` ↦ the Lean-only lemma
   `AxLedgerG2.accOnly` (an access by `e` whose address list is computed to `[k]` is at `k`)
   and two file-local tactics `axlg2_mem` / `axlg2_nmem` (membership / non-membership in a
   concrete union of singletons); `feed` is not needed (premises are given in place).
4. `gdefoLcanon` is proved like `AxDefer3.LcanonGdefer` (`List.mergeSort` does not reduce in
   the kernel; uniqueness of sorted permutations).  Same statement.
5. Lean-only helpers (file-qualified): `AxLedgerG2.accOnly`, `AxLedgerG2.accOnlyV` (the same
   on `gdefv`), `AxLedgerG2.polSafeGdefo` (the safe prefix on `gdefo` with the gate sources
   computed), `AxLedgerG2.ofListSub`, `AxLedgerG2.gsrcDEmpty`.

**Rocq → Lean name map.**  `gdefv_gmo` `gdefvGmo`, `gdefv_frozen_catches`
`gdefvFrozenCatches`, `gdefv_no_ledger` `gdefvNoLedger`, `gdefv_no_full` `gdefvNoFull`,
`gdefer_no_full` `gdeferNoFull`, `gdefo` `gdefo`, `gdefo_cat` `gdefoCat`, `gdefo_gmo`
`gdefoGmo`, `gdefo_gate_real` `gdefoGateReal`, `gdefo_deferred` `gdefoDeferred`, `gdefo_gs`
`gdefoGs`, `gdefo_Lcanon` `gdefoLcanon`, `OC_o` `OCO`, `lo` `lo`, `lo_lookup` `loLookup`,
`lh_cur_ext` `lhCurExt`, `not_def_of_empty` `notDefOfEmpty`, `gdefo_walk` `gdefoWalk`,
`gdefo_ledger` `gdefoLedger`.  No name of this file is in `notes/weak-port-dupnames.json`.

**Dropped:** only the `Print Assumptions` lines (the lint's axiom check covers them).
-/
import Weak.AxLedgerG
import Weak.AxDefer4

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std Iris.Std.PartialMap MachCSL MachCSL.Stdpp
open Lbl AxDefer2

/-- Lean-only: an access by `e` on `gdefv` whose address list is `[k]` is at `k`. -/
theorem AxLedgerG2.accOnlyV (e : Geid) (k a : Int) (hL : gaccAddrs gdefv.gdG e = [k]) :
    gaccesses gdefv.gdG e a → a = k := by
  intro h
  have h' := (gaccessesAddrs _ _ _).1 h
  rw [hL] at h'
  exact List.mem_singleton.1 h'

/-! # 1. `gdefv`: THE FROZEN-SLOT CHECK CATCHES THE EARLY READ -/

theorem gdefvGmo : gdefv.gdG.gxGmo = [wxE, dE, wfE, rE, wE] := rfl

theorem gdefvFrozenCatches (OC : Int → Prop) (K : Nat) (LH : List Ledger) (s : GSet Geid) :
    OC 0 → lfzOk OC 2 gdefv gsrcD K LH s →
    gpos gdefv.gdG dE < K →
    ¬ frozenOk OC 2 gdefv dE (lhFun LH (gpos gdefv.gdG dE)) := by
  intro HOC Hok HK Hfz
  have Hpd : gpos gdefv.gdG dE = 1 := rfl
  rw [Hpd] at HK Hfz
  have Hwx : wxE ∈ s := by
    by_cases Hn : wxE ∈ s
    · exact Hn
    exfalso
    obtain ⟨x, Hx, _⟩ := Hok.lfzCov 0 wxE (by omega) rfl Hn
    have Hnd : ¬ gdeferred gdefv.gdG gsrcD wxE := by
      rintro ⟨r, Hr, _⟩
      obtain ⟨Hc, _⟩ := (gsrcDSpec _ _).1 Hr
      rcases Hc with h | h <;> exact absurd h (by decide)
    obtain ⟨_, _, Hlt⟩ := Hok.lfzPin wxE x (by rw [gdefvGmo]; decide) Hnd Hn Hx
    have Hp0 : gpos gdefv.gdG wxE = 0 := rfl
    omega
  have Hlen := Hok.lfzLen
  obtain ⟨L0, H0⟩ : ∃ L0, LH[0]? = some L0 := ⟨_, List.getElem?_eq_getElem (by omega)⟩
  obtain ⟨L1, H1⟩ : ∃ L1, LH[1]? = some L1 := ⟨_, List.getElem?_eq_getElem (by omega)⟩
  have Hst := (Hok.lfzSlot 0 wxE L0 L1 rfl H0 H1).1 Hwx
  have Hacc : gaccesses gdefv.gdG wxE 0 := (gaccBSpec _ _ _).1 (by decide +kernel)
  have Hx1 : get? L1 0 = some (.held 1) := by
    rcases Hst.2 0 HOC ⟨1, rfl, by omega⟩ Hacc with HL | ⟨w, HL, HL'⟩
    · have Hnrel : ¬ glblIs gdefv.gdG wxE lbRelw := by
        rintro ⟨l, hl, hb⟩
        cases hl
        exact absurd hb (by decide)
      exact ledgerStepPlainKeeps _ _ _ _ _ _ _ _ Hnrel Hst HL
    · exact HL'
  have Hd : gaccesses gdefv.gdG dE 0 := (gaccBSpec _ _ _).1 (by decide +kernel)
  have Hx0 := Hfz 0 HOC ⟨0, rfl, by omega⟩ Hd
  rw [lhFunLookup _ _ _ H1, Hx1] at Hx0
  exact absurd Hx0 (by decide)

/-- No gmo ledger history at all, for any OC covering the plain writes. -/
theorem gdefvNoLedger (OC : Int → Prop) :
    (∀ w a v, w ∈ gdefv.gdG.gxGmo → tidHart 2 (some w.1) →
       glblIs gdefv.gdG w lbPlain → gwritesByte gdefv.gdG w a v → OC a) →
    ¬ ∃ LH, ledgerHistOkList OC 2 gdefv LH := by
  rintro Hplain ⟨LH, HLH⟩
  exact ownedNoViolationCat OC 2 gdefv _ gdefvCat
    (ledgerTimelineList OC 2 gdefv LH gdefvCat.1 HLH) Hplain gdefvViol

theorem gdefvNoFull (OC : Int → Prop) (gs : Geid → GSet Geid) (K : Nat) (LH : List Ledger) :
    (∀ w a v, w ∈ gdefv.gdG.gxGmo → tidHart 2 (some w.1) →
       glblIs gdefv.gdG w lbPlain → gwritesByte gdefv.gdG w a v → OC a) →
    ¬ lfzOk OC 2 gdefv gs K LH (LawfulSet.ofList gdefv.gdG.gxGmo) := by
  intro Hplain Hok
  exact gdefvNoLedger OC Hplain ⟨LH, lfzFull _ _ _ _ _ _ gdefvCat.1.1 Hok⟩

/-! # 2. `gdefer`: rejected too (the program is racy) -/

theorem gdeferNoFull (gs : Geid → GSet Geid) (K : Nat) (LH : List Ledger) :
    ¬ lfzOk AxDefer2.OCX 2 gdefer gs K LH (LawfulSet.ofList gdefer.gdG.gxGmo) := by
  intro Hok
  exact ledgerGmoNoneGdefer ⟨LH, lfzFull _ _ _ _ _ _ gdeferCat.1.1 Hok⟩

/-! # 3. POSITIVE: a deferred read of an OWNED byte -/

/-- x=0, f=1, y=2, z=3 (z: hart 0's private byte, never written). -/
def gdefo : Gdexec :=
  ⟨⟨vimg, [[LLoad false 1 [2] [b1],
            LLoad false 3 [0] [b0],
            LStore false 2 [b1] .WCplain],
           [LStore false 0 [b1] .WCplain,
            LFence true true false true,
            LStore false 1 [b1] .WCrel]],
    [(0, 1), (1, 0), (1, 2), (0, 0), (0, 2)]⟩,
   [((0, 0), (0, 2))]⟩

theorem gdefoCat : rvwmoCatConsistent gdefo :=
  catConsistentBSound _ (by decide +kernel)

theorem gdefoGmo : gdefo.gdG.gxGmo = [dE, wxE, wfE, rE, wE] := rfl

theorem gdefoGateReal : gateReal gdefo gsrcD := by
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

theorem gdefoDeferred : gdeferred gdefo.gdG gsrcD dE :=
  ⟨rE, (gsrcDSpec _ _).2 ⟨.inl rfl, rfl⟩, (gmoLtBSpec _ _ _).1 (by decide +kernel)⟩

theorem gdefoGs : gsrcOk gdefo.gdG gsrcD :=
  gsrcOkOfReal gdefo gsrcD gdefoCat gdefoGateReal

theorem gdefoLcanon : Lcanon gdefo gsrcD = [wxE, wfE, rE, dE, wE] := by
  have Hperm : List.Perm [wxE, wfE, rE, dE, wE] gdefo.gdG.gxGmo := by
    rw [gdefoGmo]
    decide
  have Hinj : ∀ a, a ∈ [wxE, wfE, rE, dE, wE] → ∀ b, b ∈ [wxE, wfE, rE, dE, wE] →
      AxDefer3.grank gdefo.gdG gsrcD a = AxDefer3.grank gdefo.gdG gsrcD b → a = b := by
    decide +kernel
  have Hsorted : List.Pairwise
      (fun a b => decide (rankLe (AxDefer3.grank gdefo.gdG gsrcD) a b) = true)
      [wxE, wfE, rE, dE, wE] := by
    decide +kernel
  refine List.Perm.eq_of_pairwise (fun a b ha hb hab hba => ?_)
    (AxDefer3.rankSortSorted _ _) Hsorted ((rankSortPerm _ _).trans Hperm.symm)
  have ha' : a ∈ [wxE, wfE, rE, dE, wE] := ((rankSortPerm _ _).trans Hperm.symm).mem_iff.1 ha
  have h1 := of_decide_eq_true hab
  have h2 := of_decide_eq_true hba
  unfold rankLe at h1 h2
  exact Hinj a ha' b hb (by omega)

def OCO (a : Int) : Prop := a = 0 ∨ a = 2 ∨ a = 3

def lo (hx : Holder) : Ledger :=
  insert (insert ({[3 := .held 0]} : Ledger) 2 (.held 0)) 0 hx

theorem loLookup (hx : Holder) (a : Int) :
    get? (lo hx) a = if a = 0 then some hx else if a = 2 then some (.held 0)
                     else if a = 3 then some (.held 0) else none := by
  unfold lo
  by_cases h0 : a = 0
  · rw [if_pos h0]; subst h0; exact lookupInsert
  rw [if_neg h0, lookupInsertNe (Ne.symm h0)]
  by_cases h2 : a = 2
  · rw [if_pos h2]; subst h2; exact lookupInsert
  rw [if_neg h2, lookupInsertNe (Ne.symm h2)]
  by_cases h3 : a = 3
  · rw [if_pos h3]; subst h3; exact lookupSingleton
  rw [if_neg h3]
  exact lookupSingletonNe (Ne.symm h3)

theorem lhCurExt (LH : List Ledger) (m : Nat) (c L' : Ledger) :
    lhCur (LH ++ List.replicate m c ++ [L']) = L' :=
  lhCurApp _ _

theorem notDefOfEmpty (e : Geid) : gsrcD e = ∅ → ¬ gdeferred gdefo.gdG gsrcD e := by
  rintro He ⟨r, Hr, _⟩
  rw [He] at Hr
  exact notElemOfEmpty Hr

/-- Lean-only (Rocq's `acc_list`): an access by `e` whose address list is `[k]` is at `k`. -/
theorem AxLedgerG2.accOnly (e : Geid) (k a : Int) (hL : gaccAddrs gdefo.gdG e = [k]) :
    gaccesses gdefo.gdG e a → a = k := by
  intro h
  have h' := (gaccessesAddrs _ _ _).1 h
  rw [hL] at h'
  exact List.mem_singleton.1 h'

/-- Lean-only: the safe prefix on `gdefo`, the gate sources computed. -/
theorem AxLedgerG2.polSafeGdefo (e : Geid) :
    polSafeS gsrcD gdefo e = LawfulSet.ofList ((gmoPrefix gdefo.gdG e).filter fun e' =>
      !(decide (e' = dE ∨ e' = wE)) || gmoLtB gdefo.gdG rE e) := by
  unfold polSafeS
  congr 1
  apply List.filter_congr
  intro e' _
  rw [Bool.eq_iff_iff, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true',
    decide_eq_false_iff_not]
  constructor
  · intro h
    by_cases hc : e' = dE ∨ e' = wE
    · exact .inr (h rE (elemOfElements.2 ((gsrcDSpec _ _).2 ⟨hc, rfl⟩)))
    · exact .inl hc
  · intro h r hr
    obtain ⟨hc, rfl⟩ := (gsrcDSpec _ _).1 (elemOfElements.1 hr)
    rcases h with h | h
    · exact absurd hc h
    · exact h

theorem AxLedgerG2.ofListSub (l : List Geid) (s : GSet Geid) :
    (∀ x, x ∈ l → x ∈ s) → (LawfulSet.ofList l : GSet Geid) ⊆ s :=
  fun h x hx => h x (elemOfListToSet.1 hx)

theorem AxLedgerG2.gsrcDEmpty (e : Geid) : ¬ (e = dE ∨ e = wE) → gsrcD e = ∅ := by
  intro h
  unfold gsrcD
  rw [if_neg h]

/-- Membership in a concrete union of singletons. -/
local macro "axlg2_mem" : tactic =>
  `(tactic| repeat (first
      | exact elemOfUnionL (elemOfSingleton.2 rfl)
      | apply elemOfUnionR))

/-- Non-membership in a concrete union of singletons. -/
local macro "axlg2_nmem" : tactic =>
  `(tactic| (intro h; repeat (first | exact notElemOfEmpty h |
      exact absurd (elemOfSingleton.1 h) (by decide) | (rcases elemOfUnion.1 h with h | h))))

theorem gdefoWalk :
    ∃ K LH, lfzOk OCO 2 gdefo gsrcD K LH (LawfulSet.ofList gdefo.gdG.gxGmo) ∧
      LH[0]? = some (lo (.held 1)) := by
  have Hwf := gdefoCat.1
  have S0 := lfzInit OCO 2 gdefo gsrcD (lo (.held 1))
  -- Wx commits slots 0 (d frozen) and 1
  have S1 := lfzCommit OCO 2 gdefo gsrcD 0 [lo (.held 1)] ∅ wxE (lo (.held 1)) Hwf gdefoGs S0
    (by rw [gdefoGmo]; decide) (notDefOfEmpty wxE (AxLedgerG2.gsrcDEmpty _ (by decide)))
    notElemOfEmpty
    (by
      rw [AxLedgerG2.polSafeGdefo]; apply AxLedgerG2.ofListSub; intro x hx
      have hl : ((gmoPrefix gdefo.gdG wxE).filter fun e' =>
          !(decide (e' = dE ∨ e' = wE)) || gmoLtB gdefo.gdG rE wxE) = [] := by
        decide +kernel
      rw [hl] at hx
      exact absurd hx List.not_mem_nil)
    ⟨ledgerMovesRefl _ _ _, by
      intro a _ _ Hacc
      rw [AxLedgerG2.accOnly _ 0 a (by decide +kernel) Hacc]
      exact .inl (by show get? (lo (.held 1)) 0 = _; rw [loLookup]; rfl)⟩
  -- Wf releases x
  have S2 := lfzCommit OCO 2 gdefo gsrcD _ _ _ wfE (lo (.pending wfE)) Hwf gdefoGs S1
    (by rw [gdefoGmo]; decide) (notDefOfEmpty wfE (AxLedgerG2.gsrcDEmpty _ (by decide)))
    (by axlg2_nmem)
    (by
      rw [AxLedgerG2.polSafeGdefo]; apply AxLedgerG2.ofListSub; intro x hx
      have hl : ((gmoPrefix gdefo.gdG wfE).filter fun e' =>
          !(decide (e' = dE ∨ e' = wE)) || gmoLtB gdefo.gdG rE wfE) = [wxE] := by
        decide +kernel
      rw [hl, List.mem_singleton] at hx
      subst hx
      axlg2_mem)
    (by
      rw [lhCurExt]
      refine ⟨?_, ?_⟩
      · intro a
        rw [loLookup, loLookup]
        by_cases h0 : a = 0
        · rw [if_pos h0, if_pos h0]
          exact .lmRelease ⟨_, rfl, by decide +kernel⟩
        · rw [if_neg h0, if_neg h0]
          exact .lmSame _
      · intro a HOC _ Hacc
        rw [AxLedgerG2.accOnly _ 1 a (by decide +kernel) Hacc] at HOC
        unfold OCO at HOC
        omega)
  -- r acquires x along rf from the release
  have S3 := lfzCommit OCO 2 gdefo gsrcD _ _ _ rE (lo (.held 0)) Hwf gdefoGs S2
    (by rw [gdefoGmo]; decide) (notDefOfEmpty rE (AxLedgerG2.gsrcDEmpty _ (by decide)))
    (by axlg2_nmem)
    (by
      rw [AxLedgerG2.polSafeGdefo]; apply AxLedgerG2.ofListSub; intro x hx
      have hl : ((gmoPrefix gdefo.gdG rE).filter fun e' =>
          !(decide (e' = dE ∨ e' = wE)) || gmoLtB gdefo.gdG rE rE) = [wxE, wfE] := by
        decide +kernel
      rw [hl] at hx
      rcases List.mem_cons.1 hx with rfl | hx
      · axlg2_mem
      rw [List.mem_singleton] at hx
      subst hx
      axlg2_mem)
    (by
      rw [lhCurExt]
      refine ⟨?_, ?_⟩
      · intro a
        rw [loLookup, loLookup]
        by_cases h0 : a = 0
        · rw [if_pos h0, if_pos h0]
          exact .lmAcquire wfE (.inl ⟨1, (grfAtBSpec _ _ _ _).1 (by decide +kernel)⟩)
        · rw [if_neg h0, if_neg h0]
          exact .lmSame _
      · intro a HOC _ Hacc
        rw [AxLedgerG2.accOnly _ 1 a (by decide +kernel) Hacc] at HOC
        unfold OCO at HOC
        omega)
  -- d: deferred; frozen check at slot 0 (z is hart 0's from the start)
  have S4 := lfzDefer OCO 2 gdefo gsrcD _ _ _ dE Hwf.1 S3
    (by rw [gdefoGmo]; decide) gdefoDeferred
    (by
      intro x Hx
      obtain ⟨_, rfl⟩ := (gsrcDSpec _ _).1 Hx
      axlg2_mem)
    (by axlg2_nmem)
    (by
      rw [show gpos gdefo.gdG dE = 0 from rfl, lhFunLookup _ 0 (lo (.held 1)) rfl]
      intro a _ _ Hacc
      rw [AxLedgerG2.accOnly _ 3 a (by decide +kernel) Hacc, loLookup]
      rfl)
  -- w commits slot 4
  have S5 := lfzCommit OCO 2 gdefo gsrcD _ _ _ wE (lo (.held 0)) Hwf gdefoGs S4
    (by rw [gdefoGmo]; decide)
    (by
      rintro ⟨r, Hr, Hlt⟩
      obtain ⟨_, rfl⟩ := (gsrcDSpec _ _).1 Hr
      exact absurd ((gmoLtBSpec _ _ _).2 Hlt) (by decide +kernel))
    (by axlg2_nmem)
    (by
      rw [AxLedgerG2.polSafeGdefo]; apply AxLedgerG2.ofListSub; intro x hx
      have hl : ((gmoPrefix gdefo.gdG wE).filter fun e' =>
          !(decide (e' = dE ∨ e' = wE)) || gmoLtB gdefo.gdG rE wE) = [dE, wxE, wfE, rE] := by
        decide +kernel
      rw [hl] at hx
      rcases List.mem_cons.1 hx with rfl | hx
      · axlg2_mem
      rcases List.mem_cons.1 hx with rfl | hx
      · axlg2_mem
      rcases List.mem_cons.1 hx with rfl | hx
      · axlg2_mem
      rw [List.mem_singleton] at hx
      subst hx
      axlg2_mem)
    (by
      rw [lhCurExt]
      refine ⟨ledgerMovesRefl _ _ _, ?_⟩
      intro a _ _ Hacc
      rw [AxLedgerG2.accOnly _ 2 a (by decide +kernel) Hacc]
      exact .inl (by rw [loLookup]; rfl))
  have Hset : (({wE} : GSet Geid) ∪ (({dE} : GSet Geid) ∪ (({rE} : GSet Geid) ∪
      (({wfE} : GSet Geid) ∪ (({wxE} : GSet Geid) ∪ ∅))))) =
      LawfulSet.ofList gdefo.gdG.gxGmo := by
    rw [setEq]
    intro x
    rw [elemOfListToSet, gdefoGmo]
    constructor
    · intro h
      repeat (first
        | exact absurd h notElemOfEmpty
        | (rw [elemOfSingleton.1 h]; decide)
        | rcases elemOfUnion.1 h with h | h)
    · intro h
      simp only [List.mem_cons, List.not_mem_nil, _root_.or_false] at h
      rcases h with rfl | rfl | rfl | rfl | rfl <;> axlg2_mem
  clear S0 S1 S2 S3 S4
  exact ⟨_, _, by rw [← Hset]; exact S5, rfl⟩

/-- … hence the GMO-INDEXED ledger history exists (and with it, by `ledgerTimeline`, an
ownership timeline). -/
theorem gdefoLedger : ∃ LH, ledgerHistOkList OCO 2 gdefo LH := by
  obtain ⟨K, LH, Hok, _⟩ := gdefoWalk
  exact ⟨LH, lfzFull _ _ _ _ _ _ gdefoCat.1.1 Hok⟩

end Weak
