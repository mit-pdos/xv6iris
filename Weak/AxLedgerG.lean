/-
Weak: **the K1 ledger REDESIGNED for deferred reads** — a GMO-SLOT-INDEXED ledger walked in ANY
processing order (in particular `AxDefer3.Lcanon`), FROZEN slots for deferred reads, the joint
flow equations at the gated tier-A instance, adequacy, program-level K1.

Rocq: `iris/AxLedgerG.v` @ xxvzwolszwmp.

## The Rocq header, in substance

WHY.  `AxTokLedgerWp.ledgerInv` requires the validated set to BE a gmo prefix, so its flow
equations need `gmoPrefix e ⊆ sPol e` — the full prefix, which with ctrl gates on PLAIN loads is
UNSOUND (`AxDefer2.naiveGatedRefuted`); a processing-order ledger is UNSOUND
(`AxDefer4.procLedgerUnsound`); re-sorting is FALSE (`AxDefer2.ledgerGmoNoneGdefer`).

THE DESIGN.  The ledger history `LH` stays indexed by GMO SLOT; `K` slots are committed.
Invariant `lfzOk OC nh GD gs K LH s` over the validated set `s` (any set):
- slot `k < K` holding event `e`: if `e ∈ s` the slot is a legal `ledgerStep`; if `e ∉ s` the
  slot is an IDENTITY (FROZEN: committed by the walk, checked later);
- every validated event sits below `K`; every frozen slot is below some validated event
  (`lfzCov`);
- `pinInv`: a validated event is gmo-before every NON-deferred unvalidated event (deferred :=
  gmo-before one of its gate sources, `gdeferred`).
A flow equation of a NON-deferred `e` COMMITS: `K ≤ gpos e` (`lfzCommitLe`); the slots
`[K, gpos e)` become frozen identities, slot `gpos e` gets `e`'s real ledger step
(`lfzCommit`).  A flow equation of a DEFERRED `e` does not touch the ledger: its slot is already
committed (`lfzDeferLt`) and it discharges its access check AGAINST THE FROZEN SLOT
(`frozenOk`, `lfzDefer`) — a deferred read can neither acquire nor release.  At the full set
every slot is a legal step: `lfzFull` ⇒ `ledgerHistOkList` ⇒ `ledgerTimeline` ⇒ `gtlOk`.
THE REFINEMENT: `pinInv` is preserved iff each flow equation's handout contains its
deferral-safe prefix and (deferred) its gate sources: `polSafeS gs GD e ⊆ sPol e` (commit) /
`gs e ⊆ sPol e` (defer) — the `AxDefer5.PGate` shape.

§1 pure: `gdeferred`, `gsrcOk` (`gsrcOkOfReal`), `pinInv`, `frozenOk`, `lfzOk`; `lfzInit`,
`lfzCommitLe`, `lfzCommit`, `lfzDeferLt`, `lfzDefer`, `lfzFull`; `lfzHeldForward`,
`frozenOfInit`; gate-free `lfzGatefreeSet`.
§2 `ledgerInvG` (ghost: the auth of the CURRENT ledger; the frozen history is pure).
§3 `ledgerJointG` (commit) / `ledgerDeferG` (frozen check); `flowEqLedgerG` / `flowEqDeferG`;
`wpEvStepLedgerG` / `wpEvStepDeferG`; `ledgerJointGOfJoint` (gate-free WPd proofs re-run).
§4 `tierAFinalCoreL` / `tierAAdequacyFinalL` / `tierAAdequacyFinalGate`: AxDefer5's adequacy
over an order `L` KEEPING the final phase-2 state.
§5 `obStInterpLG`; `tierAAdequacyLedgerG` (`_Tl`, `_Dev2`); the policy `polGate`.
§6 PROGRAM LEVEL: `progLedgerVerifiedG`, `progTlG`, `progViolFreeG`, `progNotVerifiedGOfViol`.

## Deviations from Rocq

1. NAMES / VOCABULARY as AxTokLedgerWp (deviation 2): `list_to_set` ↦ `LawfulSet.ofList`,
   `{[e]} ∪ s` ↦ `({e} : GSet Geid) ∪ s`, `S n` ↦ `n + 1`, `L !! a` ↦ `get? L a`, `l !! k` ↦
   `l[k]?`, `NoDup` ↦ `List.Nodup`, `Held i` ↦ `.held i`, `(k ≤ j < k + d)` ↦
   `k ≤ j ∧ j < k + d`.  Rocq's record `lfz_ok` (constructor `LfzOk`) is the structure `lfzOk`
   (constructor `lfzOk.mk`, fields `lfzLen`…`lfzPin`); the inductive
   `prog_ledger_verified_G` has constructor `progLedgerVerifiedG.mk` (as AxClsStep).
2. LIST ASSOCIATIVITY: Rocq's `LH ++ replicate m c ++ [L']` is right-nested; Lean's `++` is
   left-associative, so the same text denotes `(LH ++ replicate m c) ++ [L']` (equal lists;
   `extLookup` and `lfzCommit` are stated on the Lean parse).
3. O2 STAGE C (as AxTokLedgerWp/AxDefer5/AxClsStep): no text oracle — the section parameter `T`
   and `ap_T P` are gone (`tierAAstep GD nm i`, `tierAWpd GD N …`).
4. CONTEXTS (as AxTokLedgerWp deviation 4): section `Context`s are explicit leading arguments;
   `invGS_gen HasNoLc Σ` ↦ `[InvGS_gen hlc GF]` for any `hlc` in §3/§4 cores (soundness at
   `.hasNoLC`); `GF : BundledGFunctors.{0,0,0}` where adequacy is involved.  Rocq's `Local
   Instance AxGAF` is `letI … := axGA3 …` (AxTierA3's reducible `axGA2`).  `pol_gate` is a
   `@[reducible] def` (not an instance), its lemmas name it (`@Axpol.sPol (polGate gsF) …`).
5. PROOF ROUTE: §4's phase 2 is `adequacyOrdLWf` (as AxDefer5); Rocq's `adequacy_ord_L`.

**Rocq → Lean name map.**  `gdeferred` `gdeferred`, `gsrc_ok` `gsrcOk`, `gsrc_ok_of_real`
`gsrcOkOfReal`, `pin_inv` `pinInv`, `frozen_ok` `frozenOk`, `lfz_ok` `lfzOk` (`LfzOk`
`lfzOk.mk`; `lfz_len/le/slot/in/cov/pin` `lfzLen/lfzLe/lfzSlot/lfzIn/lfzCov/lfzPin`), `lfz_init`
`lfzInit`, `lh_cur_lookup` `lhCurLookup`, `lfz_commit_le` `lfzCommitLe`, `ext_lookup`
`extLookup`, `pol_safe_s_nondeferred` `polSafeSNondeferred`, `lfz_commit` `lfzCommit`,
`lfz_defer_lt` `lfzDeferLt`, `lh_fun_lookup` `lhFunLookup`, `lfz_defer` `lfzDefer`, `lfz_full`
`lfzFull`, `lfz_held_forward` `lfzHeldForward`, `frozen_of_init` `frozenOfInit`,
`pol_safe_s_empty` `polSafeSEmpty`, `lfz_gatefree_set` `lfzGatefreeSet`, `ledger_inv_G`
`ledgerInvG`, `ledger_inv_G_init` `ledgerInvGInit`, `ledger_inv_G_full` `ledgerInvGFull`,
`ledger_joint_G` `ledgerJointG`, `ledger_defer_G` `ledgerDeferG`, `flow_eq_ledger_G`
`flowEqLedgerG`, `flow_eq_defer_G` `flowEqDeferG`, `wp_ev_step_ledger_G` `wpEvStepLedgerG`,
`wp_ev_step_defer_G` `wpEvStepDeferG`, `ledger_joint_G_of_joint` `ledgerJointGOfJoint`,
`tierA_final_core_L` `tierAFinalCoreL`, `tierA_adequacy_final_L` `tierAAdequacyFinalL`,
`tierA_adequacy_final_gate` `tierAAdequacyFinalGate`, `ob_st_interpLG` `obStInterpLG`,
`AxGA2_ledgerG_ob_ext` `axGA2LedgerGObExt`, `tierA_adequacy_ledger_G` `tierAAdequacyLedgerG`,
`tierA_adequacy_ledger_G_tl` `tierAAdequacyLedgerGTl`, `tierA_adequacy_ledger_G_dev2`
`tierAAdequacyLedgerGDev2`, `pol_gate` `polGate`, `pol_gate_ok` `polGateOk`, `pol_gate_wf`
`polGateWf`, `pol_gate_pin` `polGatePin`, `prog_ledger_verified_G` `progLedgerVerifiedG`
(`ProgLedgerVerifiedG` `progLedgerVerifiedG.mk`), `prog_tl_G` `progTlG`, `prog_viol_free_G`
`progViolFreeG`, `prog_not_verified_G_of_viol` `progNotVerifiedGOfViol`.  No name of this file
is in `notes/weak-port-dupnames.json`; no Lean-only helpers.

**Dropped:** only the `Print Assumptions` lines (the lint's axiom check covers them).
-/
import Weak.AxClsStep
import Weak.AxDefer5

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std Iris.Std.PartialMap MachCSL MachCSL.Stdpp

/-! # 1. THE PURE FROZEN-SLOT INVARIANT -/

/-- `e` is DEFERRED: gmo-before one of its gate sources. -/
def gdeferred (G : Gexec) (gs : Geid → GSet Geid) (e : Geid) : Prop :=
  ∃ r, r ∈ gs e ∧ gmoLt G e r

/-- The two facts of a gate structure the invariant uses. -/
def gsrcOk (G : Gexec) (gs : Geid → GSet Geid) : Prop :=
  ∀ e r, r ∈ gs e → r ∈ G.gxGmo ∧ r ≠ e

theorem gsrcOkOfReal (GD : Gdexec) (gs : Geid → GSet Geid) :
    rvwmoCatConsistent GD → gateReal GD gs → gsrcOk GD.gdG gs := by
  intro Hcons Hreal e r Hr
  refine ⟨gateRealSrcGmo GD gs Hcons Hreal e r Hr, ?_⟩
  intro Heq
  rw [Heq] at Hr
  obtain ⟨⟨_, Hlt, _⟩, _⟩ := Hreal e e Hr
  exact Nat.lt_irrefl _ Hlt

/-- A validated event is gmo-before every unvalidated NON-deferred event. -/
def pinInv (G : Gexec) (gs : Geid → GSet Geid) (s : GSet Geid) : Prop :=
  ∀ e x, e ∈ G.gxGmo → ¬ gdeferred G gs e → e ∉ s → x ∈ s → gmoLt G x e

/-- The access check of `e` against a (frozen) ledger: every Own-class byte a hart event
accesses is HELD by its hart (no acquisition). -/
def frozenOk (OC : Int → Prop) (nh : Nat) (GD : Gdexec) (e : Geid) (L : Ledger) : Prop :=
  ∀ a, OC a → tidHart nh (some e.1) → gaccesses GD.gdG e a → get? L a = some (.held e.1)

/-- THE FROZEN-SLOT INVARIANT. -/
structure lfzOk (OC : Int → Prop) (nh : Nat) (GD : Gdexec) (gs : Geid → GSet Geid)
    (K : Nat) (LH : List Ledger) (s : GSet Geid) : Prop where
  lfzLen : LH.length = K + 1
  lfzLe : K ≤ GD.gdG.gxGmo.length
  lfzSlot : ∀ k e L L', GD.gdG.gxGmo[k]? = some e → LH[k]? = some L → LH[k + 1]? = some L' →
    (e ∈ s → AxTokLedger.ledgerStep OC nh GD e L L') ∧ (e ∉ s → L' = L)
  lfzIn : ∀ x, x ∈ s → x ∈ GD.gdG.gxGmo ∧ gpos GD.gdG x < K
  lfzCov : ∀ k e, k < K → GD.gdG.gxGmo[k]? = some e → e ∉ s →
    ∃ x, x ∈ s ∧ k < gpos GD.gdG x
  lfzPin : pinInv GD.gdG gs s

theorem lfzInit (OC : Int → Prop) (nh : Nat) (GD : Gdexec) (gs : Geid → GSet Geid)
    (L0 : Ledger) : lfzOk OC nh GD gs 0 [L0] ∅ where
  lfzLen := rfl
  lfzLe := Nat.zero_le _
  lfzSlot := by
    intro k e L L' _ _ HL'
    cases k with
    | zero => cases HL'
    | succ k => cases HL'
  lfzIn := fun _ hx => absurd hx notElemOfEmpty
  lfzCov := fun _ _ hk => absurd hk (Nat.not_lt_zero _)
  lfzPin := fun _ _ _ _ _ hx => absurd hx notElemOfEmpty

theorem lhCurLookup (LH : List Ledger) (K : Nat) :
    LH.length = K + 1 → LH[K]? = some (lhCur LH) := by
  intro Hlen
  unfold lhCur
  rw [List.getLast?_eq_getElem?, Hlen, Nat.add_sub_cancel]
  rw [List.getElem?_eq_getElem (by omega)]
  rfl

/-- A NON-deferred unvalidated event is at or above the committed frontier. -/
theorem lfzCommitLe (OC : Int → Prop) (nh : Nat) (GD : Gdexec) (gs : Geid → GSet Geid)
    (K : Nat) (LH : List Ledger) (s : GSet Geid) (e : Geid) :
    GD.gdG.gxGmo.Nodup → lfzOk OC nh GD gs K LH s →
    e ∈ GD.gdG.gxGmo → ¬ gdeferred GD.gdG gs e → e ∉ s →
    K ≤ gpos GD.gdG e := by
  intro _ Hok He Hnd' Hnin
  refine Nat.not_lt.1 fun Hlt => ?_
  obtain ⟨x, Hx, Hpx⟩ := Hok.lfzCov _ e Hlt (gposElemLookup _ _ He) Hnin
  obtain ⟨_, _, Hp⟩ := Hok.lfzPin e x He Hnd' Hnin Hx
  omega

theorem extLookup (LH : List Ledger) (c L' : Ledger) (m k : Nat) :
    (LH ++ List.replicate m c ++ [L'])[k]? =
      if k < LH.length then LH[k]?
      else if k < LH.length + m then some c
      else if k = LH.length + m then some L' else none := by
  rw [List.append_assoc]
  by_cases h1 : k < LH.length
  · rw [if_pos h1, List.getElem?_append_left h1]
  · rw [if_neg h1, List.getElem?_append_right (by omega)]
    by_cases h2 : k < LH.length + m
    · rw [if_pos h2, List.getElem?_append_left (by simp; omega), List.getElem?_replicate,
        if_pos (by omega)]
    · rw [if_neg h2, List.getElem?_append_right (by simp; omega), List.length_replicate]
      by_cases h3 : k = LH.length + m
      · rw [if_pos h3, h3, show LH.length + m - LH.length - m = 0 by omega]
        rfl
      · rw [if_neg h3]
        apply List.getElem?_eq_none
        simp only [List.length_singleton]
        omega

theorem polSafeSNondeferred (GD : Gdexec) (gs : Geid → GSet Geid) (e0 e : Geid) :
    gwf GD.gdG → gsrcOk GD.gdG gs → e ∈ GD.gdG.gxGmo →
    ¬ gdeferred GD.gdG gs e0 → gmoLt GD.gdG e0 e → e0 ∈ polSafeS gs GD e := by
  intro Hwf Hgs He Hnd0 Hlt
  unfold polSafeS
  rw [elemOfListToSet, List.mem_filter]
  refine ⟨(gmoPrefixSpec _ _ _ Hwf He).2 Hlt, ?_⟩
  rw [List.all_eq_true]
  intro r Hr
  have Hr' := elemOfElements.1 Hr
  apply (gmoLtBSpec _ _ _).2
  obtain ⟨Hrg, Hne⟩ := Hgs e0 r Hr'
  rcases gmoLtTotal _ r e0 Hwf.1 Hrg Hlt.1 Hne with H | H
  · exact gmoLtTrans _ _ _ _ H Hlt
  · exact absurd ⟨r, Hr', H⟩ Hnd0

/-- THE COMMIT of a non-deferred event: frozen identities up to its slot, its real step at its
slot. -/
theorem lfzCommit (OC : Int → Prop) (nh : Nat) (GD : Gdexec) (gs : Geid → GSet Geid)
    (K : Nat) (LH : List Ledger) (s : GSet Geid) (e : Geid) (L' : Ledger) :
    gwf GD.gdG → gsrcOk GD.gdG gs →
    lfzOk OC nh GD gs K LH s →
    e ∈ GD.gdG.gxGmo → ¬ gdeferred GD.gdG gs e → e ∉ s →
    polSafeS gs GD e ⊆ s →
    AxTokLedger.ledgerStep OC nh GD e (lhCur LH) L' →
    lfzOk OC nh GD gs (gpos GD.gdG e + 1)
      (LH ++ List.replicate (gpos GD.gdG e - K) (lhCur LH) ++ [L']) (({e} : GSet Geid) ∪ s) := by
  intro Hwf Hgs Hok He Hnde Hnin Hpol Hst
  have Hnd := Hwf.1
  have Hle := lfzCommitLe OC nh GD gs K LH s e Hnd Hok He Hnde Hnin
  have Hlen := Hok.lfzLen
  have Hcur := lhCurLookup LH K Hlen
  have Hp := gposElemLookup _ _ He
  have Hplen := gposLtLen _ _ He
  have HeIn : e ∈ (({e} : GSet Geid) ∪ s) := elemOfUnionL (elemOfSingleton.2 rfl)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [List.length_append, List.length_replicate, List.length_singleton]
    omega
  · omega
  · intro k ev La Lb Hk Ha Hb
    rw [extLookup, Hlen] at Ha Hb
    have Hkev : gpos GD.gdG ev = k := gposOfLookup _ _ _ Hnd Hk
    by_cases HkK : k < K
    · rw [if_pos (by omega : k < K + 1)] at Ha
      rw [if_pos (by omega : k + 1 < K + 1)] at Hb
      have Hne : ev ≠ e := by
        intro h
        rw [h] at Hkev
        omega
      obtain ⟨H1, H2⟩ := Hok.lfzSlot k ev La Lb Hk Ha Hb
      refine ⟨fun Hin => H1 ?_, fun Hin => H2 fun h => Hin (elemOfUnionR h)⟩
      rcases elemOfUnion.1 Hin with h | h
      · exact absurd (elemOfSingleton.1 h) Hne
      · exact h
    · by_cases Hkp : k < gpos GD.gdG e
      · have HLa : La = lhCur LH := by
          by_cases HkK' : k = K
          · rw [HkK', if_pos (Nat.lt_succ_self K), Hcur] at Ha
            exact (Option.some.inj Ha).symm
          · rw [if_neg (by omega), if_pos (by omega)] at Ha
            exact (Option.some.inj Ha).symm
        rw [if_neg (by omega), if_pos (by omega)] at Hb
        have HLb : Lb = lhCur LH := (Option.some.inj Hb).symm
        have Hne : ev ≠ e := by
          intro h
          rw [h] at Hkev
          omega
        have Hnin' : ev ∉ s := by
          intro Hev
          have := (Hok.lfzIn ev Hev).2
          omega
        refine ⟨fun Hin => ?_, fun _ => by rw [HLa, HLb]⟩
        exfalso
        rcases elemOfUnion.1 Hin with h | h
        · exact Hne (elemOfSingleton.1 h)
        · exact Hnin' h
      · by_cases Hkp' : k = gpos GD.gdG e
        · rw [Hkp', Hp] at Hk
          have Hev : ev = e := (Option.some.inj Hk).symm
          have HLa : La = lhCur LH := by
            by_cases HpK : gpos GD.gdG e = K
            · rw [Hkp', HpK, if_pos (Nat.lt_succ_self K), Hcur] at Ha
              exact (Option.some.inj Ha).symm
            · rw [if_neg (by omega), if_pos (by omega)] at Ha
              exact (Option.some.inj Ha).symm
          rw [if_neg (by omega), if_neg (by omega), if_pos (by omega)] at Hb
          have HLb : Lb = L' := (Option.some.inj Hb).symm
          rw [Hev, HLa, HLb]
          exact ⟨fun _ => Hst, fun Hn => absurd HeIn Hn⟩
        · exfalso
          rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)] at Hb
          cases Hb
  · intro x Hx
    rcases elemOfUnion.1 Hx with h | h
    · rw [elemOfSingleton.1 h]
      exact ⟨He, by omega⟩
    · obtain ⟨h1, h2⟩ := Hok.lfzIn x h
      exact ⟨h1, by omega⟩
  · intro k ev Hk Hev Hnin'
    refine ⟨e, HeIn, ?_⟩
    by_cases hkp : k = gpos GD.gdG e
    · exfalso
      rw [hkp, Hp] at Hev
      rw [← Option.some.inj Hev] at Hnin'
      exact Hnin' HeIn
    · omega
  · intro e0 x He0 Hnd0 Hnin0 Hx
    rcases elemOfUnion.1 Hx with h | h
    · rw [elemOfSingleton.1 h]
      have Hne : e0 ≠ e := fun h' => Hnin0 (elemOfUnionL (elemOfSingleton.2 h'))
      rcases gmoLtTotal _ e e0 Hnd He He0 (Ne.symm Hne) with H | H
      · exact H
      · exact absurd (elemOfUnionR (Hpol _ (polSafeSNondeferred GD gs e0 e Hwf Hgs He Hnd0 H)))
          Hnin0
    · exact Hok.lfzPin e0 x He0 Hnd0 (fun h' => Hnin0 (elemOfUnionR h')) h

/-- A deferred event's slot is already committed (its source is validated and gmo-later). -/
theorem lfzDeferLt (OC : Int → Prop) (nh : Nat) (GD : Gdexec) (gs : Geid → GSet Geid)
    (K : Nat) (LH : List Ledger) (s : GSet Geid) (e : Geid) :
    lfzOk OC nh GD gs K LH s → gdeferred GD.gdG gs e → gs e ⊆ s →
    gpos GD.gdG e < K := by
  rintro Hok ⟨r, Hr, _, _, Hlt⟩ Hsub
  have := (Hok.lfzIn r (Hsub r Hr)).2
  omega

theorem lhFunLookup (LH : List Ledger) (k : Nat) (L : Ledger) :
    LH[k]? = some L → lhFun LH k = L := by
  intro H
  simp only [lhFun, H]

/-- THE DEFERRED STEP: no ledger change; the access check is made against the FROZEN slot. -/
theorem lfzDefer (OC : Int → Prop) (nh : Nat) (GD : Gdexec) (gs : Geid → GSet Geid)
    (K : Nat) (LH : List Ledger) (s : GSet Geid) (e : Geid) :
    GD.gdG.gxGmo.Nodup →
    lfzOk OC nh GD gs K LH s → e ∈ GD.gdG.gxGmo →
    gdeferred GD.gdG gs e → gs e ⊆ s → e ∉ s →
    frozenOk OC nh GD e (lhFun LH (gpos GD.gdG e)) →
    lfzOk OC nh GD gs K LH (({e} : GSet Geid) ∪ s) := by
  intro Hnd Hok He Hdef Hsub Hnin Hfz
  have HeK := lfzDeferLt OC nh GD gs K LH s e Hok Hdef Hsub
  refine ⟨Hok.lfzLen, Hok.lfzLe, ?_, ?_, ?_, ?_⟩
  · intro k ev La Lb Hk Ha Hb
    obtain ⟨H1, H2⟩ := Hok.lfzSlot k ev La Lb Hk Ha Hb
    by_cases Hev : ev = e
    · have HLb : Lb = La := H2 (by rw [Hev]; exact Hnin)
      rw [Hev] at Hk ⊢
      have Hkp : gpos GD.gdG e = k := gposOfLookup _ _ _ Hnd Hk
      rw [HLb]
      refine ⟨fun _ => ⟨ledgerMovesRefl GD e La, ?_⟩,
        fun Hn => absurd (elemOfUnionL (elemOfSingleton.2 rfl)) Hn⟩
      intro a HOC Hh Hacc
      left
      rw [Hkp, lhFunLookup _ _ _ Ha] at Hfz
      exact Hfz a HOC Hh Hacc
    · refine ⟨fun Hin => H1 ?_, fun Hin => H2 fun h => Hin (elemOfUnionR h)⟩
      rcases elemOfUnion.1 Hin with h | h
      · exact absurd (elemOfSingleton.1 h) Hev
      · exact h
  · intro x Hx
    rcases elemOfUnion.1 Hx with h | h
    · rw [elemOfSingleton.1 h]
      exact ⟨He, HeK⟩
    · exact Hok.lfzIn x h
  · intro k ev Hk Hev Hnin'
    obtain ⟨x, Hx, Hlt⟩ := Hok.lfzCov k ev Hk Hev (fun h => Hnin' (elemOfUnionR h))
    exact ⟨x, elemOfUnionR Hx, Hlt⟩
  · intro e0 x He0 Hnd0 Hnin0 Hx
    rcases elemOfUnion.1 Hx with h | h
    · rw [elemOfSingleton.1 h]
      obtain ⟨r, Hr, Hlt⟩ := Hdef
      exact gmoLtTrans _ _ _ _ Hlt
        (Hok.lfzPin e0 r He0 Hnd0 (fun h' => Hnin0 (elemOfUnionR h')) (Hsub r Hr))
    · exact Hok.lfzPin e0 x He0 Hnd0 (fun h' => Hnin0 (elemOfUnionR h')) h

/-- READ-BACK at the full validated set: the GMO-indexed history of `AxTokLedger`. -/
theorem lfzFull (OC : Int → Prop) (nh : Nat) (GD : Gdexec) (gs : Geid → GSet Geid)
    (K : Nat) (LH : List Ledger) :
    GD.gdG.gxGmo.Nodup →
    lfzOk OC nh GD gs K LH (LawfulSet.ofList GD.gdG.gxGmo) →
    ledgerHistOkList OC nh GD LH := by
  intro Hnd Hok
  have HK : K = GD.gdG.gxGmo.length := by
    refine Nat.le_antisymm Hok.lfzLe (Nat.not_lt.1 fun Hlt => ?_)
    have Hx : GD.gdG.gxGmo[K]? = some (GD.gdG.gxGmo[K]'Hlt) := List.getElem?_eq_getElem Hlt
    have Hin : GD.gdG.gxGmo[K]'Hlt ∈ (LawfulSet.ofList GD.gdG.gxGmo : GSet Geid) :=
      (elemOfListToSet (S := GSet Geid)).2 (elem_of_list_lookup_2 Hx)
    have Hlt2 := (Hok.lfzIn _ Hin).2
    rw [gposOfLookup _ _ _ Hnd Hx] at Hlt2
    exact Nat.lt_irrefl _ Hlt2
  refine ⟨by rw [Hok.lfzLen, HK], ?_⟩
  intro k e L L' Hk HL HL'
  exact (Hok.lfzSlot k e L L' Hk HL HL').1
    ((elemOfListToSet (S := GSet Geid)).2 (elem_of_list_lookup_2 Hk))

/-! ## 1.1 Frozen-check helpers -/

/-- A Held entry survives every committed slot that is not a release-class event of its
holder. -/
theorem lfzHeldForward (OC : Int → Prop) (nh : Nat) (GD : Gdexec) (gs : Geid → GSet Geid)
    (K : Nat) (LH : List Ledger) (s : GSet Geid) (k d : Nat) (L1 : Ledger) (a : Int)
    (i : Agent) :
    lfzOk OC nh GD gs K LH s → LH[k]? = some L1 → get? L1 a = some (.held i) →
    k + d ≤ K →
    (∀ j ev, k ≤ j ∧ j < k + d → GD.gdG.gxGmo[j]? = some ev →
      ¬ (ev.1 = i ∧ glblIs GD.gdG ev lbRelw)) →
    ∃ L2, LH[k + d]? = some L2 ∧ get? L2 a = some (.held i) := by
  intro Hok Hk Ha
  induction d with
  | zero => exact fun _ _ => ⟨L1, Hk, Ha⟩
  | succ d IH =>
    intro Hle Hno
    obtain ⟨L2, HL2, Ha2⟩ := IH (by omega) (fun j ev Hj => Hno j ev ⟨Hj.1, by omega⟩)
    have Hlen := Hok.lfzLen
    have HKle := Hok.lfzLe
    obtain ⟨L3, HL3⟩ : ∃ L3, LH[k + d + 1]? = some L3 :=
      ⟨_, List.getElem?_eq_getElem (by omega)⟩
    obtain ⟨ev, Hev⟩ : ∃ ev, GD.gdG.gxGmo[k + d]? = some ev :=
      ⟨_, List.getElem?_eq_getElem (by omega)⟩
    refine ⟨L3, by rw [show k + (d + 1) = k + d + 1 by omega]; exact HL3, ?_⟩
    obtain ⟨H1, H2⟩ := Hok.lfzSlot _ ev L2 L3 Hev HL2 HL3
    by_cases Hin : ev ∈ s
    · have Hmv := (H1 Hin).1 a
      rw [Ha2] at Hmv
      rcases ledgerMoveHeldInv GD ev i _ Hmv with Hsame | ⟨_, He1, Hrel⟩
      · exact Hsame
      · exact absurd ⟨He1, Hrel⟩ (Hno (k + d) ev ⟨by omega, by omega⟩ Hev)
    · rw [H2 Hin]
      exact Ha2

/-- The typical deferred read: every Own-class byte it accesses is its hart's in the INITIAL
ledger and the hart has no release-class event gmo-before the read. -/
theorem frozenOfInit (OC : Int → Prop) (nh : Nat) (GD : Gdexec) (gs : Geid → GSet Geid)
    (K : Nat) (LH : List Ledger) (s : GSet Geid) (L0 : Ledger) (e : Geid) :
    lfzOk OC nh GD gs K LH s → LH[0]? = some L0 →
    gpos GD.gdG e ≤ K →
    (∀ a, OC a → tidHart nh (some e.1) → gaccesses GD.gdG e a →
      get? L0 a = some (.held e.1)) →
    (∀ j ev, j < gpos GD.gdG e → GD.gdG.gxGmo[j]? = some ev →
      ¬ (ev.1 = e.1 ∧ glblIs GD.gdG ev lbRelw)) →
    frozenOk OC nh GD e (lhFun LH (gpos GD.gdG e)) := by
  intro Hok H0 Hle Hown Hno a HOC Hh Hacc
  obtain ⟨L2, HL2, Ha2⟩ := lfzHeldForward OC nh GD gs K LH s 0 (gpos GD.gdG e) L0 a e.1 Hok H0
    (Hown a HOC Hh Hacc) (by omega) (fun j ev Hj => Hno j ev (by omega))
  rw [Nat.zero_add] at HL2
  rw [lhFunLookup _ _ _ HL2]
  exact Ha2

/-! ## 1.2 Gate-free specialization: the validated set IS the gmo prefix -/

theorem polSafeSEmpty (GD : Gdexec) (e : Geid) :
    polSafeS (fun _ => ∅) GD e = LawfulSet.ofList (gmoPrefix GD.gdG e) := by
  unfold polSafeS
  congr 1
  apply List.filter_eq_self.2
  intro r _
  rw [List.all_eq_true]
  intro x hx
  exact absurd (elemOfElements.1 hx) notElemOfEmpty

theorem lfzGatefreeSet (OC : Int → Prop) (nh : Nat) (GD : Gdexec) (K : Nat) (LH : List Ledger)
    (s : GSet Geid) (e : Geid) :
    gwf GD.gdG → lfzOk OC nh GD (fun _ => ∅) K LH s →
    e ∈ GD.gdG.gxGmo → e ∉ s → (LawfulSet.ofList (gmoPrefix GD.gdG e) : GSet Geid) ⊆ s →
    s = LawfulSet.ofList (GD.gdG.gxGmo.take (gpos GD.gdG e)) := by
  intro Hwf Hok He Hnin Hsub
  rw [setEq]
  intro x
  constructor
  · intro Hx
    rw [elemOfListToSet]
    show x ∈ gmoPrefix GD.gdG e
    apply (gmoPrefixSpec _ _ _ Hwf He).2
    refine Hok.lfzPin e x He ?_ Hnin Hx
    rintro ⟨r, Hr, _⟩
    exact notElemOfEmpty Hr
  · intro Hx
    exact Hsub x Hx

/-! # 2. THE LEDGER PIECE OF THE STATE INTERPRETATION -/

section ledgerInvGSec
variable {GF : BundledGFunctors} [LedgerG GF]

/-- The frozen-slot invariant beside the auth of the CURRENT ledger. -/
def ledgerInvG (OC : Int → Prop) (nh : Nat) (L0 : Ledger) (gsF : Gdexec → Geid → GSet Geid)
    (γ : GName) (GD : Gdexec) (s : GSet Geid) : IProp GF :=
  iprop(∃ (K : Nat) (LH : List Ledger),
    ⌜lfzOk OC nh GD (gsF GD) K LH s ∧ LH[0]? = some L0⌝ ∗ ledgerInterp γ LH)

theorem ledgerInvGInit (OC : Int → Prop) (nh : Nat) (L0 : Ledger)
    (gsF : Gdexec → Geid → GSet Geid) (γ : GName) (GD : Gdexec) :
    ledgerAuth (GF := GF) γ L0 ⊢ ledgerInvG OC nh L0 gsF γ GD ∅ := by
  unfold ledgerInvG
  iintro Ha
  iexists 0, [L0]
  rw [show ledgerInterp (GF := GF) γ [L0] = ledgerAuth γ L0 from rfl]
  isplitr
  · ipureintro
    exact ⟨lfzInit OC nh GD (gsF GD) L0, rfl⟩
  · iexact Ha

theorem ledgerInvGFull (OC : Int → Prop) (nh : Nat) (L0 : Ledger)
    (gsF : Gdexec → Geid → GSet Geid) (γ : GName) (GD : Gdexec) :
    gwf GD.gdG →
    ledgerInvG (GF := GF) OC nh L0 gsF γ GD (LawfulSet.ofList GD.gdG.gxGmo) ⊢
      ⌜∃ LH, ledgerHistOkList OC nh GD LH⌝ := by
  intro Hwf
  unfold ledgerInvG
  iintro ⟨%K, %LH, %Hp, -⟩
  ipureintro
  exact ⟨LH, lfzFull OC nh GD (gsF GD) K LH Hwf.1 Hp.1⟩

end ledgerInvGSec

/-! # 3. JOINT FLOW EQUATIONS at any instance `base ∗ ledgerInvG` -/

section flowLedgerG
variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [AxirisG GF] [LedgerG GF]

/-- COMMIT (non-deferred `e`): the base step and ONE legal ledger step at `e`'s gmo slot, knowing
the validated set, the frozen history and that `e`'s slot is not yet committed. -/
def ledgerJointG (OC : Int → Prop) (nh : Nat) (L0 : Ledger) (gsF : Gdexec → Geid → GSet Geid)
    (γL : GName) (base : Gdexec → AxirisG.obSt GF → GSet Geid → IProp GF)
    (GD : Gdexec) (e : Geid) (s0 : GSet Geid) (fin : Mea GF) (R : IProp GF) : IProp GF :=
  iprop(∀ (σ : AxirisG.obSt GF) (s : GSet Geid) (K : Nat) (LH : List Ledger),
    ⌜lfzOk OC nh GD (gsF GD) K LH s⌝ -∗ ⌜LH[0]? = some L0⌝ -∗
    ⌜s0 ⊆ s⌝ -∗ ⌜e ∉ s⌝ -∗ ⌜K ≤ gpos GD.gdG e⌝ -∗
    base GD σ s -∗ ledgerAuth γL (lhCur LH) -∗
    ([∗map] Rin ∈ fin, Rin) ={⊤,∅}=∗ ▷ |={∅,⊤}=>
    ∃ (σ' : AxirisG.obSt GF) (L' : Ledger),
      base GD σ' (({e} : GSet Geid) ∪ s) ∗ ledgerAuth γL L' ∗
      ⌜AxTokLedger.ledgerStep OC nh GD e (lhCur LH) L'⌝ ∗ R)

/-- DEFER (deferred `e`): the base step and the access check AGAINST THE FROZEN SLOT; the current
ledger is handed back UNCHANGED. -/
def ledgerDeferG (OC : Int → Prop) (nh : Nat) (L0 : Ledger) (gsF : Gdexec → Geid → GSet Geid)
    (γL : GName) (base : Gdexec → AxirisG.obSt GF → GSet Geid → IProp GF)
    (GD : Gdexec) (e : Geid) (s0 : GSet Geid) (fin : Mea GF) (R : IProp GF) : IProp GF :=
  iprop(∀ (σ : AxirisG.obSt GF) (s : GSet Geid) (K : Nat) (LH : List Ledger),
    ⌜lfzOk OC nh GD (gsF GD) K LH s⌝ -∗ ⌜LH[0]? = some L0⌝ -∗
    ⌜s0 ⊆ s⌝ -∗ ⌜e ∉ s⌝ -∗ ⌜gpos GD.gdG e < K⌝ -∗
    base GD σ s -∗ ledgerAuth γL (lhCur LH) -∗
    ([∗map] Rin ∈ fin, Rin) ={⊤,∅}=∗ ▷ |={∅,⊤}=>
    ∃ (σ' : AxirisG.obSt GF),
      base GD σ' (({e} : GSet Geid) ∪ s) ∗ ledgerAuth γL (lhCur LH) ∗
      ⌜frozenOk OC nh GD e (lhFun LH (gpos GD.gdG e))⌝ ∗ R)

variable [Axpol]

theorem flowEqLedgerG (OC : Int → Prop) (nh : Nat) (L0 : Ledger)
    (gsF : Gdexec → Geid → GSet Geid) (γL : GName)
    (base : Gdexec → AxirisG.obSt GF → GSet Geid → IProp GF)
    (HobExt : ∀ (GD : Gdexec) (σ : AxirisG.obSt GF) (s : GSet Geid),
      AxirisG.obStInterp GD σ s ⊣⊢ base GD σ s ∗ ledgerInvG OC nh L0 gsF γL GD s)
    (GD : Gdexec) (e : Geid) (s0 : GSet Geid) (fin : Mea GF) (R : IProp GF)
    (Hwf : gwf GD.gdG) (Hgs : gsrcOk GD.gdG (gsF GD)) (He : e ∈ GD.gdG.gxGmo)
    (Hnde : ¬ gdeferred GD.gdG (gsF GD) e) (Hpol : polSafeS (gsF GD) GD e ⊆ s0) :
    ⊢ ledgerJointG OC nh L0 gsF γL base GD e s0 fin R -∗ flowEqDyn GD e s0 fin R := by
  unfold flowEqDyn ledgerJointG
  iintro Hj %σ %s %Hsub %Hnin Hob Hin
  ihave Hob := (HobExt GD σ s).1 $$ Hob
  icases Hob with ⟨Hb, Hl⟩
  iunfold ledgerInvG at Hl
  icases Hl with ⟨%K, %LH, %Hp, Ha⟩
  obtain ⟨Hok, H0⟩ := Hp
  have Hle := lfzCommitLe OC nh GD (gsF GD) K LH s e Hwf.1 Hok He Hnde Hnin
  have Hlen := Hok.lfzLen
  iunfold ledgerInterp at Ha
  imod Hj $$ %σ %s %K %LH %Hok %H0 %Hsub %Hnin %Hle Hb Ha Hin with Hj
  imodintro
  inext
  imod Hj with ⟨%σ', %L', Hb, Ha, %Hst, HR⟩
  imodintro
  iexists σ'
  isplitl [Hb Ha]
  · iapply (HobExt GD σ' (({e} : GSet Geid) ∪ s)).2
    isplitl [Hb]
    · iexact Hb
    · iunfold ledgerInvG
      iexists (gpos GD.gdG e + 1), (LH ++ List.replicate (gpos GD.gdG e - K) (lhCur LH) ++ [L'])
      isplitr
      · ipureintro
        refine ⟨lfzCommit OC nh GD (gsF GD) K LH s e L' Hwf Hgs Hok He Hnde Hnin
          (fun x hx => Hsub x (Hpol x hx)) Hst, ?_⟩
        rw [List.append_assoc, List.getElem?_append_left (by omega)]
        exact H0
      · iapply ledgerInterpAppend γL _ L'
        iexact Ha
  · iexact HR

theorem flowEqDeferG (OC : Int → Prop) (nh : Nat) (L0 : Ledger)
    (gsF : Gdexec → Geid → GSet Geid) (γL : GName)
    (base : Gdexec → AxirisG.obSt GF → GSet Geid → IProp GF)
    (HobExt : ∀ (GD : Gdexec) (σ : AxirisG.obSt GF) (s : GSet Geid),
      AxirisG.obStInterp GD σ s ⊣⊢ base GD σ s ∗ ledgerInvG OC nh L0 gsF γL GD s)
    (GD : Gdexec) (e : Geid) (s0 : GSet Geid) (fin : Mea GF) (R : IProp GF)
    (Hwf : gwf GD.gdG) (He : e ∈ GD.gdG.gxGmo)
    (Hdef : gdeferred GD.gdG (gsF GD) e) (Hsrc : gsF GD e ⊆ s0) :
    ⊢ ledgerDeferG OC nh L0 gsF γL base GD e s0 fin R -∗ flowEqDyn GD e s0 fin R := by
  unfold flowEqDyn ledgerDeferG
  iintro Hj %σ %s %Hsub %Hnin Hob Hin
  ihave Hob := (HobExt GD σ s).1 $$ Hob
  icases Hob with ⟨Hb, Hl⟩
  iunfold ledgerInvG at Hl
  icases Hl with ⟨%K, %LH, %Hp, Ha⟩
  obtain ⟨Hok, H0⟩ := Hp
  have Hsrc' : gsF GD e ⊆ s := fun x hx => Hsub x (Hsrc x hx)
  have Hlt := lfzDeferLt OC nh GD (gsF GD) K LH s e Hok Hdef Hsrc'
  iunfold ledgerInterp at Ha
  imod Hj $$ %σ %s %K %LH %Hok %H0 %Hsub %Hnin %Hlt Hb Ha Hin with Hj
  imodintro
  inext
  imod Hj with ⟨%σ', Hb, Ha, %Hfz, HR⟩
  imodintro
  iexists σ'
  isplitl [Hb Ha]
  · iapply (HobExt GD σ' (({e} : GSet Geid) ∪ s)).2
    isplitl [Hb]
    · iexact Hb
    · iunfold ledgerInvG
      iexists K, LH
      isplitr
      · ipureintro
        exact ⟨lfzDefer OC nh GD (gsF GD) K LH s e Hwf.1 Hok He Hdef Hsrc' Hnin Hfz, H0⟩
      · iunfold ledgerInterp
        iexact Ha
  · iexact HR

/-- WP level (as `AxTokLedgerWp.wpEvStepLedgerJoint`). -/
theorem wpEvStepLedgerG (OC : Int → Prop) (nh : Nat) (L0 : Ledger)
    (gsF : Gdexec → Geid → GSet Geid) (γL : GName)
    (base : Gdexec → AxirisG.obSt GF → GSet Geid → IProp GF)
    (HobExt : ∀ (GD : Gdexec) (σ : AxirisG.obSt GF) (s : GSet Geid),
      AxirisG.obStInterp GD σ s ⊣⊢ base GD σ s ∗ ledgerInvG OC nh L0 gsF γL GD s)
    {A : Type} (GD : Gdexec) (i : Agent) (k : Nat) (ok val : A → Prop) (k' : A → Nat)
    (Ψ : A → IProp GF) (x : A) (Hokx : ok x)
    (Hwf : gwf GD.gdG) (Hgs : gsrcOk GD.gdG (gsF GD)) (He : (i, k) ∈ GD.gdG.gxGmo)
    (Hnde : ¬ gdeferred GD.gdG (gsF GD) (i, k))
    (Hpol : polSafeS (gsF GD) GD (i, k) ⊆ Axpol.sPol GD (i, k)) :
    ⊢ (∀ na : Mea GF, naAtProgress GD i k na ∗ AxirisG.annotInterp na ==∗
        ∃ (R : IProp GF) (naUsed : Mea GF) (naUnused : Mea GF) (ls' : AxirisG.logTsT GF),
          naSplittingWf (Axpol.lobp GD (i, k)) na naUsed naUnused ∗
          ledgerJointG OC nh L0 gsF γL base GD (i, k) (Axpol.sPol GD (i, k)) naUsed
            iprop(R ∗ ⌜val x⌝) ∗
          AxirisG.annotInterp (PartialMap.union (PartialMap.union {[(i, k) := R]} naUnused) na) ∗
          AxirisG.localInterp GD i (k' x) ls') -∗
      Ψ x -∗
      wpEvStep GD i k ok val k' Ψ := by
  unfold wpEvStep
  iintro Hflow HΨ %na Hpg
  imodintro
  inext
  imod Hflow $$ %na Hpg with ⟨%R, %nu, %nuu, %ls', Hsplit, Hj, Hna, Hloc⟩
  imodintro
  iexists x, R, nu, nuu, ls'
  isplitr
  · ipureintro
    exact Hokx
  isplitl [Hsplit]
  · iexact Hsplit
  isplitl [Hj]
  · iapply flowEqLedgerG OC nh L0 gsF γL base HobExt GD (i, k) (Axpol.sPol GD (i, k)) nu
      iprop(R ∗ ⌜val x⌝) Hwf Hgs He Hnde Hpol $$ Hj
  iframe Hna Hloc HΨ

theorem wpEvStepDeferG (OC : Int → Prop) (nh : Nat) (L0 : Ledger)
    (gsF : Gdexec → Geid → GSet Geid) (γL : GName)
    (base : Gdexec → AxirisG.obSt GF → GSet Geid → IProp GF)
    (HobExt : ∀ (GD : Gdexec) (σ : AxirisG.obSt GF) (s : GSet Geid),
      AxirisG.obStInterp GD σ s ⊣⊢ base GD σ s ∗ ledgerInvG OC nh L0 gsF γL GD s)
    {A : Type} (GD : Gdexec) (i : Agent) (k : Nat) (ok val : A → Prop) (k' : A → Nat)
    (Ψ : A → IProp GF) (x : A) (Hokx : ok x)
    (Hwf : gwf GD.gdG) (He : (i, k) ∈ GD.gdG.gxGmo)
    (Hdef : gdeferred GD.gdG (gsF GD) (i, k))
    (Hsrc : gsF GD (i, k) ⊆ Axpol.sPol GD (i, k)) :
    ⊢ (∀ na : Mea GF, naAtProgress GD i k na ∗ AxirisG.annotInterp na ==∗
        ∃ (R : IProp GF) (naUsed : Mea GF) (naUnused : Mea GF) (ls' : AxirisG.logTsT GF),
          naSplittingWf (Axpol.lobp GD (i, k)) na naUsed naUnused ∗
          ledgerDeferG OC nh L0 gsF γL base GD (i, k) (Axpol.sPol GD (i, k)) naUsed
            iprop(R ∗ ⌜val x⌝) ∗
          AxirisG.annotInterp (PartialMap.union (PartialMap.union {[(i, k) := R]} naUnused) na) ∗
          AxirisG.localInterp GD i (k' x) ls') -∗
      Ψ x -∗
      wpEvStep GD i k ok val k' Ψ := by
  unfold wpEvStep
  iintro Hflow HΨ %na Hpg
  imodintro
  inext
  imod Hflow $$ %na Hpg with ⟨%R, %nu, %nuu, %ls', Hsplit, Hj, Hna, Hloc⟩
  imodintro
  iexists x, R, nu, nuu, ls'
  isplitr
  · ipureintro
    exact Hokx
  isplitl [Hsplit]
  · iexact Hsplit
  isplitl [Hj]
  · iapply flowEqDeferG OC nh L0 gsF γL base HobExt GD (i, k) (Axpol.sPol GD (i, k)) nu
      iprop(R ∗ ⌜val x⌝) Hwf He Hdef Hsrc $$ Hj
  iframe Hna Hloc HΨ

end flowLedgerG

section jointBridge
variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [AxirisG GF] [LedgerG GF]

/-- GATE-FREE SPECIALIZATION: an `AxTokLedgerWp.ledgerJoint` obligation (base at the exact gmo
prefix) IS a commit obligation when the graph's gate structure is empty. -/
theorem ledgerJointGOfJoint (OC : Int → Prop) (nh : Nat) (L0 : Ledger)
    (gsF : Gdexec → Geid → GSet Geid) (γL : GName)
    (base : Gdexec → AxirisG.obSt GF → GSet Geid → IProp GF)
    (GD : Gdexec) (e : Geid) (s0 : GSet Geid) (fin : Mea GF) (R : IProp GF)
    (Hwf : gwf GD.gdG) (Hgs : gsF GD = fun _ => ∅) (He : e ∈ GD.gdG.gxGmo)
    (Hpref : (LawfulSet.ofList (gmoPrefix GD.gdG e) : GSet Geid) ⊆ s0) :
    ⊢ ledgerJoint OC nh γL base GD e fin R -∗
      ledgerJointG OC nh L0 gsF γL base GD e s0 fin R := by
  unfold ledgerJoint ledgerJointG
  iintro Hj %σ %s %K %LH %Hok %_H0 %Hsub %Hnin %_Hle Hb Ha Hin
  rw [Hgs] at Hok
  have Hs := lfzGatefreeSet OC nh GD K LH s e Hwf Hok He Hnin (fun x hx => Hsub x (Hpref x hx))
  subst Hs
  have Hp := gposElemLookup _ _ He
  imod Hj $$ %σ %(gpos GD.gdG e) %(lhCur LH) %Hp Hb Ha Hin with Hj
  imodintro
  inext
  imod Hj with ⟨%σ', %L', Hb, Ha, %Hst, HR⟩
  imodintro
  iexists σ', L'
  rw [← takeSSet _ _ _ Hp]
  isplitl [Hb]
  · iexact Hb
  isplitl [Ha]
  · iexact Ha
  isplitr
  · ipureintro
    exact Hst
  · iexact HR

end jointBridge

/-! # 4. ADEQUACY OVER AN ARBITRARY ORDER, KEEPING THE FINAL STATE

`AxDefer5.tierAAdequacyAnnCoreL`'s proof, but reading a pure `Q` back from the FINAL phase-2
state (as `AxTokLedgerWp.tierAFinalCore` does for the gmo route). -/

section finalL
variable {GF : BundledGFunctors.{0,0,0}}

theorem tierAFinalCoreL {hlc : HasLC} [InvGS_gen hlc GF] [AxannotGS GF] [Axpol]
    (GD : Gdexec) (N obSt0 : Type) (obStInterp0 : N → Gdexec → obSt0 → GSet Geid → IProp GF)
    (init : N → Agent → IProp GF) (nm : N)
    (Hwf : axpolWf) (Hcons : rvwmoCatConsistent GD)
    (harts : List Agent) (Hnd : harts.Nodup)
    (s0 sN : Agent → Athread) (n : Agent → Nat)
    (Hrun : ∀ i, i ∈ harts → nsteps (astepAnyNfGv GD i) (n i) (s0 i) (sN i))
    (Hk0 : ∀ i, i ∈ harts → (s0 i).atK = 0)
    (Hend : ∀ i, i ∈ harts → (sN i).atK = (AxOpsem.grow GD i).length)
    (post : Agent → Athread → Prop)
    (Hwp : ⊢ ([∗list] i ∈ harts, init nm i) -∗
      [∗list] i ∈ harts,
        tierAWpd GD N obSt0 obStInterp0 nm (s0 i) .MaybeStuck i (fun s => iprop(⌜post i s⌝)))
    (L : List Geid) (Hperm : L.Perm GD.gdG.gxGmo) (Hpol : axpolWfL GD L)
    (Hcov : (unionList (harts.map fun i => eidsBefore GD i (AxOpsem.grow GD i).length) :
        GSet Geid) = LawfulSet.ofList L)
    (Q : Prop)
    (Hread : ∀ σ, obStInterp0 nm GD σ (LawfulSet.ofList L) ⊢ ⌜Q⌝)
    (σ0 : obSt0) :
    ⊢ AxAnnot.annotInterp (∅ : Mea GF) -∗ obStInterp0 nm GD σ0 ∅ -∗
      ([∗list] i ∈ harts, init nm i) -∗
      |={⊤}[∅]▷=>^[(harts.map n).sum + (1 + L.length)] ⌜Q⌝ := by
  letI axG : AxirisG GF := axGA3 GD N obSt0 obStInterp0 nm
  have Hgc : ⊢ AxirisG.gconstInterp GD := axGA2Gconst GD N obSt0 obStInterp0 nm
  have Hloc : ∀ j : Agent, ⊢ ∃ ls, AxirisG.localInterp (GF := GF) GD j 0 ls := fun _ => by
    iexists ()
    show ⊢ iprop(True)
    itrivial
  have Hbig0 : ([∗list] j ∈ harts,
        tierAWpd GD N obSt0 obStInterp0 nm (s0 j) .MaybeStuck j (fun s => iprop(⌜post j s⌝))) ⊢
      [∗list] j ∈ harts, (∃ ls, AxirisG.localInterp (GF := GF) GD j 0 ls) ∗
        wpd .MaybeStuck j (s0 j) (fun s => iprop(⌜post j s⌝)) :=
    BigSepL.bigSepL_mono_of_forall fun {_ j} => AxTierA2.wpdWithLocal GD j _ (Hloc j)
  have Hphase1 := wpdHartsNsteps (GF := GF) GD Hwf Hcons .MaybeStuck harts Hnd s0 sN n Hrun Hk0
    (fun j s => (iprop(⌜post j s⌝) : IProp GF))
  have Hndp : L.Nodup := Hperm.nodup_iff.2 (schedHGwf GD Hcons).1
  have Hfmap : (harts.map fun j => eidsBefore GD j (sN j).atK) =
      harts.map fun j => eidsBefore GD j (AxOpsem.grow GD j).length :=
    List.map_congr_left fun j Hj => by rw [Hend j Hj]
  iintro Hannot0 Hob0 Hinit
  ihave HWPall := Hwp $$ Hinit
  ihave Hbig := Hbig0 $$ HWPall
  ihave #Hg := Hgc
  ihave Hp1 := Hphase1 $$ Hannot0 Hg Hbig
  ihave Hp1 := wpdStepsNStepFupdN _ _ $$ Hp1
  iapply step_fupdN_add.2
  iapply step_fupdN_wand $$ Hp1
  iintro H
  rw [show 1 + L.length = L.length + 1 by omega, AxTierA2.stepFupdNSucc]
  imod H with ⟨%na, %ea, %Hdomna, -, Hea, -⟩
  iapply (step_fupd_intro LawfulSet.empty_subset)
  inext
  have Hdomeq : (FiniteMap.dom_set na : GSet Geid) = LawfulSet.ofList L := by
    rw [Hdomna, Hfmap]
    exact Hcov
  ihave Hconn := (ordEaTodoLOfEaLocalWf GD ea na L Hndp Hdomeq.symm) $$ Hea
  icases Hconn with ⟨%Hdom_eq2, %Hea_lob2, Htodo⟩
  have Hdom_sub : (LawfulSet.ofList L : GSet Geid) ⊆ FiniteMap.dom_set na := by
    rw [Hdomeq]
  ihave Hphase2 := (adequacyOrdLWf GD (schedHGwf GD Hcons) L Hperm Hpol na ea
    Hdom_eq2 Hdom_sub Hea_lob2 σ0) $$ Htodo Hob0
  iapply step_fupdN_wand $$ Hphase2
  iintro ⟨%σ, Hob, -⟩
  ihave HQ := (Hread σ) $$ Hob
  iexact HQ

end finalL

section finalLWrapper
variable {GF : BundledGFunctors.{0,0,0}}

theorem tierAAdequacyFinalL [InvGpreS GF] [AxannotG GF] [Axpol]
    (GD : Gdexec) (N obSt0 : Type) (obStInterp0 : N → Gdexec → obSt0 → GSet Geid → IProp GF)
    (init : N → Agent → IProp GF)
    (Hwf : axpolWf) (Hcons : rvwmoCatConsistent GD)
    (harts : List Agent) (Hnd : harts.Nodup)
    (Hharts : ∀ e, e ∈ GD.gdG.gxGmo → e.1 ∈ harts)
    (s0 sN : Agent → Athread) (n : Agent → Nat)
    (Hrun : ∀ (_ : AxannotGS GF) (nm : N) i, i ∈ harts →
      nsteps (tierAAstep GD nm i) (n i) (s0 i) (sN i))
    (Hk0 : ∀ i, i ∈ harts → (s0 i).atK = 0)
    (Hend : ∀ i, i ∈ harts → (sN i).atK = (AxOpsem.grow GD i).length)
    (post : Agent → Athread → Prop)
    (Hwp : ∀ [InvGS_gen .hasNoLC GF] [AxannotGS GF] (nm : N),
      ⊢ ([∗list] i ∈ harts, init nm i) -∗
        [∗list] i ∈ harts,
          tierAWpd GD N obSt0 obStInterp0 nm (s0 i) .MaybeStuck i (fun s => iprop(⌜post i s⌝)))
    (HobAlloc : ⊢ |==> ∃ (nm : N) (σ0 : obSt0),
      obStInterp0 nm GD σ0 ∅ ∗ [∗list] i ∈ harts, init nm i)
    (L : List Geid) (Hperm : L.Perm GD.gdG.gxGmo) (Hpol : axpolWfL GD L)
    (Q : Prop)
    (Hread : ∀ nm σ, obStInterp0 nm GD σ (LawfulSet.ofList GD.gdG.gxGmo) ⊢ ⌜Q⌝) :
    Q := by
  have HLset : (LawfulSet.ofList L : GSet Geid) = LawfulSet.ofList GD.gdG.gxGmo := by
    rw [setEq]
    intro x
    rw [elemOfListToSet, elemOfListToSet]
    exact Hperm.mem_iff
  have Hcov : (unionList (harts.map fun i => eidsBefore GD i (AxOpsem.grow GD i).length) :
      GSet Geid) = LawfulSet.ofList L := by
    rw [eidsBeforeCov GD harts (schedHGwf GD Hcons) Hharts, HLset]
  have Hread' : ∀ nm σ, obStInterp0 nm GD σ (LawfulSet.ofList L) ⊢ ⌜Q⌝ := by
    intro nm σ
    rw [HLset]
    exact Hread nm σ
  apply Iris.pure_soundness (PROP := IProp GF)
  refine step_fupdN_soundness_close (hlc := .hasNoLC)
    (1 + ((harts.map n).sum + (1 + L.length))) 0 (fun Hinv => ?_)
  rw [show 1 + ((harts.map n).sum + (1 + L.length)) =
      ((harts.map n).sum + (1 + L.length)) + 1 by omega,
    AxTierA2.stepFupdNSucc]
  iintro _
  imod (annotInterpAlloc (GF := GF)) with ⟨%γ, Hannot0⟩
  imod HobAlloc with ⟨%nm, %σ0, Hob0, Hinit⟩
  ihave Hcore := (@tierAFinalCoreL GF .hasNoLC Hinv { axannotName := γ } _ GD N obSt0
    obStInterp0 init nm Hwf Hcons harts Hnd s0 sN n
    (fun j Hj => Hrun { axannotName := γ } nm j Hj) Hk0 Hend post
    (@Hwp Hinv { axannotName := γ } nm)
    L Hperm Hpol Hcov Q (Hread' nm) σ0)
    $$ Hannot0 Hob0 Hinit
  iapply (step_fupd_intro LawfulSet.empty_subset)
  inext
  iexact Hcore

/-- At the canonical deferring order: deferral-safe or gate-source handouts. -/
theorem tierAAdequacyFinalGate [InvGpreS GF] [AxannotG GF] [Axpol]
    (GD : Gdexec) (N obSt0 : Type) (obStInterp0 : N → Gdexec → obSt0 → GSet Geid → IProp GF)
    (init : N → Agent → IProp GF)
    (Hwf : axpolWf) (Hcons : rvwmoCatConsistent GD)
    (harts : List Agent) (Hnd : harts.Nodup)
    (Hharts : ∀ e, e ∈ GD.gdG.gxGmo → e.1 ∈ harts)
    (s0 sN : Agent → Athread) (n : Agent → Nat)
    (Hrun : ∀ (_ : AxannotGS GF) (nm : N) i, i ∈ harts →
      nsteps (tierAAstep GD nm i) (n i) (s0 i) (sN i))
    (Hk0 : ∀ i, i ∈ harts → (s0 i).atK = 0)
    (Hend : ∀ i, i ∈ harts → (sN i).atK = (AxOpsem.grow GD i).length)
    (post : Agent → Athread → Prop)
    (Hwp : ∀ [InvGS_gen .hasNoLC GF] [AxannotGS GF] (nm : N),
      ⊢ ([∗list] i ∈ harts, init nm i) -∗
        [∗list] i ∈ harts,
          tierAWpd GD N obSt0 obStInterp0 nm (s0 i) .MaybeStuck i (fun s => iprop(⌜post i s⌝)))
    (HobAlloc : ⊢ |==> ∃ (nm : N) (σ0 : obSt0),
      obStInterp0 nm GD σ0 ∅ ∗ [∗list] i ∈ harts, init nm i)
    (gsrc : Geid → GSet Geid) (Hreal : gateReal GD gsrc) (Hmono : gateMono GD gsrc)
    (Hok : ∀ e e', e' ∈ Axpol.sPol GD e ∪ Axpol.lobp GD e →
      polDS GD.gdG gsrc e' e ∨ e' ∈ gsrc e)
    (Q : Prop)
    (Hread : ∀ nm σ, obStInterp0 nm GD σ (LawfulSet.ofList GD.gdG.gxGmo) ⊢ ⌜Q⌝) :
    Q :=
  have H := LcanonOkGate GD Hcons gsrc Hreal Hmono Hok
  tierAAdequacyFinalL GD N obSt0 obStInterp0 init Hwf Hcons harts Hnd Hharts s0 sN n Hrun Hk0
    Hend post Hwp HobAlloc (Lcanon GD gsrc) H.1 H.2.2 Q Hread

end finalLWrapper

/-! # 5. THE GATED LEDGER INSTANCE AND ITS ADEQUACY -/

/-- The gated ledger instance: any base protocol beside `ledgerInvG`. -/
def obStInterpLG {GF : BundledGFunctors} [LedgerG GF] (OC : Int → Prop) (nh : Nat)
    (L0 : Ledger) (gsF : Gdexec → Geid → GSet Geid) {N0 obSt0 : Type}
    (base0 : N0 → Gdexec → obSt0 → GSet Geid → IProp GF)
    (nm : N0 × GName) (GD : Gdexec) (σ : obSt0) (s : GSet Geid) : IProp GF :=
  iprop(base0 nm.1 GD σ s ∗ ledgerInvG OC nh L0 gsF nm.2 GD s)

section ledgerAdeqG
variable {GF : BundledGFunctors.{0,0,0}}

/-- §3's combinators apply at the extended `axGA2` instance. -/
theorem axGA2LedgerGObExt [AxannotGS GF] [LedgerG GF] (GD : Gdexec) (OC : Int → Prop)
    (nh : Nat) (L0 : Ledger) (gsF : Gdexec → Geid → GSet Geid)
    (N0 obSt0 : Type) (base0 : N0 → Gdexec → obSt0 → GSet Geid → IProp GF) (nm : N0 × GName) :
    ∀ (GD' : Gdexec) (σ : obSt0) (s : GSet Geid),
      @AxirisG.obStInterp GF (axGA2 GD (N0 × GName) obSt0 (obStInterpLG OC nh L0 gsF base0) nm)
          GD' σ s ⊣⊢
        base0 nm.1 GD' σ s ∗ ledgerInvG OC nh L0 gsF nm.2 GD' s :=
  fun _ _ _ => .rfl

/-- THE GATED J2 ADEQUACY: completed runs of per-hart WPds at the gated ledger instance,
deferral-safe / gate-source handouts, processing in `Lcanon` ⇒ a legal GMO-INDEXED ledger
history. -/
theorem tierAAdequacyLedgerG [InvGpreS GF] [AxannotG GF] [LedgerG GF] [Axpol]
    (GD : Gdexec) (OC : Int → Prop) (nh : Nat) (L0 : Ledger) (gsF : Gdexec → Geid → GSet Geid)
    (N0 obSt0 : Type) (base0 : N0 → Gdexec → obSt0 → GSet Geid → IProp GF)
    (init : N0 × GName → Agent → IProp GF)
    (Hwf : axpolWf) (Hcons : rvwmoCatConsistent GD)
    (harts : List Agent) (Hnd : harts.Nodup)
    (Hharts : ∀ e, e ∈ GD.gdG.gxGmo → e.1 ∈ harts)
    (s0 sN : Agent → Athread) (n : Agent → Nat)
    (Hrun : ∀ (_ : AxannotGS GF) (nm : N0 × GName) i, i ∈ harts →
      nsteps (tierAAstep GD nm i) (n i) (s0 i) (sN i))
    (Hk0 : ∀ i, i ∈ harts → (s0 i).atK = 0)
    (Hend : ∀ i, i ∈ harts → (sN i).atK = (AxOpsem.grow GD i).length)
    (post : Agent → Athread → Prop)
    (Hwp : ∀ [InvGS_gen .hasNoLC GF] [AxannotGS GF] (nm : N0 × GName),
      ⊢ ([∗list] i ∈ harts, init nm i) -∗
        [∗list] i ∈ harts,
          tierAWpd GD (N0 × GName) obSt0 (obStInterpLG OC nh L0 gsF base0) nm (s0 i)
            .MaybeStuck i (fun s => iprop(⌜post i s⌝)))
    (HobAlloc : ⊢ |==> ∃ (nm : N0 × GName) (σ0 : obSt0),
      obStInterpLG OC nh L0 gsF base0 nm GD σ0 ∅ ∗ [∗list] i ∈ harts, init nm i)
    (Hreal : gateReal GD (gsF GD)) (Hmono : gateMono GD (gsF GD))
    (Hok : ∀ e e', e' ∈ Axpol.sPol GD e ∪ Axpol.lobp GD e →
      polDS GD.gdG (gsF GD) e' e ∨ e' ∈ gsF GD e) :
    ∃ LH, ledgerHistOkList OC nh GD LH :=
  tierAAdequacyFinalGate GD (N0 × GName) obSt0 (obStInterpLG OC nh L0 gsF base0) init Hwf Hcons
    harts Hnd Hharts s0 sN n Hrun Hk0 Hend post Hwp HobAlloc (gsF GD) Hreal Hmono Hok _
    (fun nm _σ => by
      unfold obStInterpLG
      iintro ⟨-, Hl⟩
      ihave H := (ledgerInvGFull OC nh L0 gsF nm.2 GD (schedHGwf GD Hcons)) $$ Hl
      iexact H)

theorem tierAAdequacyLedgerGTl [InvGpreS GF] [AxannotG GF] [LedgerG GF] [Axpol]
    (GD : Gdexec) (OC : Int → Prop) (nh : Nat) (L0 : Ledger) (gsF : Gdexec → Geid → GSet Geid)
    (N0 obSt0 : Type) (base0 : N0 → Gdexec → obSt0 → GSet Geid → IProp GF)
    (init : N0 × GName → Agent → IProp GF)
    (Hwf : axpolWf) (Hcons : rvwmoCatConsistent GD)
    (harts : List Agent) (Hnd : harts.Nodup)
    (Hharts : ∀ e, e ∈ GD.gdG.gxGmo → e.1 ∈ harts)
    (s0 sN : Agent → Athread) (n : Agent → Nat)
    (Hrun : ∀ (_ : AxannotGS GF) (nm : N0 × GName) i, i ∈ harts →
      nsteps (tierAAstep GD nm i) (n i) (s0 i) (sN i))
    (Hk0 : ∀ i, i ∈ harts → (s0 i).atK = 0)
    (Hend : ∀ i, i ∈ harts → (sN i).atK = (AxOpsem.grow GD i).length)
    (post : Agent → Athread → Prop)
    (Hwp : ∀ [InvGS_gen .hasNoLC GF] [AxannotGS GF] (nm : N0 × GName),
      ⊢ ([∗list] i ∈ harts, init nm i) -∗
        [∗list] i ∈ harts,
          tierAWpd GD (N0 × GName) obSt0 (obStInterpLG OC nh L0 gsF base0) nm (s0 i)
            .MaybeStuck i (fun s => iprop(⌜post i s⌝)))
    (HobAlloc : ⊢ |==> ∃ (nm : N0 × GName) (σ0 : obSt0),
      obStInterpLG OC nh L0 gsF base0 nm GD σ0 ∅ ∗ [∗list] i ∈ harts, init nm i)
    (Hreal : gateReal GD (gsF GD)) (Hmono : gateMono GD (gsF GD))
    (Hok : ∀ e e', e' ∈ Axpol.sPol GD e ∪ Axpol.lobp GD e →
      polDS GD.gdG (gsF GD) e' e ∨ e' ∈ gsF GD e) :
    ∃ own, gtlOk OC nh GD.gdG own := by
  obtain ⟨LH, HLH⟩ := tierAAdequacyLedgerG GD OC nh L0 gsF N0 obSt0 base0 init Hwf Hcons harts
    Hnd Hharts s0 sN n Hrun Hk0 Hend post Hwp HobAlloc Hreal Hmono Hok
  exact ⟨_, ledgerTimelineList OC nh GD LH (schedHGwf GD Hcons) HLH⟩

/-- The dev-2 form: dev-2 handouts plus gate-source handouts. -/
theorem tierAAdequacyLedgerGDev2 [InvGpreS GF] [AxannotG GF] [LedgerG GF] [Axpol]
    (GD : Gdexec) (OC : Int → Prop) (nh : Nat) (L0 : Ledger) (gsF : Gdexec → Geid → GSet Geid)
    (N0 obSt0 : Type) (base0 : N0 → Gdexec → obSt0 → GSet Geid → IProp GF)
    (init : N0 × GName → Agent → IProp GF)
    (Hwf : axpolWf) (Hcons : rvwmoCatConsistent GD)
    (harts : List Agent) (Hnd : harts.Nodup)
    (Hharts : ∀ e, e ∈ GD.gdG.gxGmo → e.1 ∈ harts)
    (s0 sN : Agent → Athread) (n : Agent → Nat)
    (Hrun : ∀ (_ : AxannotGS GF) (nm : N0 × GName) i, i ∈ harts →
      nsteps (tierAAstep GD nm i) (n i) (s0 i) (sN i))
    (Hk0 : ∀ i, i ∈ harts → (s0 i).atK = 0)
    (Hend : ∀ i, i ∈ harts → (sN i).atK = (AxOpsem.grow GD i).length)
    (post : Agent → Athread → Prop)
    (Hwp : ∀ [InvGS_gen .hasNoLC GF] [AxannotGS GF] (nm : N0 × GName),
      ⊢ ([∗list] i ∈ harts, init nm i) -∗
        [∗list] i ∈ harts,
          tierAWpd GD (N0 × GName) obSt0 (obStInterpLG OC nh L0 gsF base0) nm (s0 i)
            .MaybeStuck i (fun s => iprop(⌜post i s⌝)))
    (HobAlloc : ⊢ |==> ∃ (nm : N0 × GName) (σ0 : obSt0),
      obStInterpLG OC nh L0 gsF base0 nm GD σ0 ∅ ∗ [∗list] i ∈ harts, init nm i)
    (Hreal : gateReal GD (gsF GD)) (Hmono : gateMono GD (gsF GD))
    (HsPol : ∀ e e', e' ∈ Axpol.sPol GD e → flowDev2 GD e' e ∨ e' ∈ gsF GD e)
    (Hlobp : ∀ e e', e' ∈ Axpol.lobp GD e → flowDev2 GD e' e) :
    ∃ LH, ledgerHistOkList OC nh GD LH := by
  apply tierAAdequacyLedgerG GD OC nh L0 gsF N0 obSt0 base0 init Hwf Hcons harts Hnd Hharts
    s0 sN n Hrun Hk0 Hend post Hwp HobAlloc Hreal Hmono
  intro e e' Hin
  rcases elemOfUnion.1 Hin with Hin | Hin
  · rcases HsPol e e' Hin with Hf | Hg
    · exact .inl (dev2DS GD Hcons (gsF GD) Hreal Hmono e' e Hf)
    · exact .inr Hg
  · exact .inl (dev2DS GD Hcons (gsF GD) Hreal Hmono e' e (Hlobp e e' Hin))

end ledgerAdeqG

/-- The policy the gated combinators want — the deferral-safe prefix plus the gate sources
(`AxDefer5.PGate`, for any graph). -/
@[reducible] def polGate (gsF : Gdexec → Geid → GSet Geid) : Axpol where
  sPol := fun GD e => polSafeS (gsF GD) GD e ∪ gsF GD e
  lobp := fun _ _ => ∅

theorem polGateOk (gsF : Gdexec → Geid → GSet Geid) (GD : Gdexec) :
    rvwmoCatConsistent GD →
    ∀ e e', e' ∈ @Axpol.sPol (polGate gsF) GD e ∪ @Axpol.lobp (polGate gsF) GD e →
      polDS GD.gdG (gsF GD) e' e ∨ e' ∈ gsF GD e := by
  intro Hcons e e' Hin
  rcases elemOfUnion.1 Hin with Hin | Hin
  · rcases elemOfUnion.1 Hin with Hin | Hin
    · exact .inl (polSafeDS GD Hcons (gsF GD) e e' Hin)
    · exact .inr Hin
  · exact absurd Hin notElemOfEmpty

theorem polGateWf (gsF : Gdexec → Geid → GSet Geid) : @axpolWf (polGate gsF) :=
  fun _ _ _ _ hx => absurd hx notElemOfEmpty

/-- … and it is exactly what the combinators' handout premises ask. -/
theorem polGatePin (gsF : Gdexec → Geid → GSet Geid) (GD : Gdexec) (e : Geid) :
    polSafeS (gsF GD) GD e ⊆ @Axpol.sPol (polGate gsF) GD e ∧
      gsF GD e ⊆ @Axpol.sPol (polGate gsF) GD e :=
  ⟨fun _ hx => elemOfUnionL hx, fun _ hx => elemOfUnionR hx⟩

/-! # 6. PROGRAM-LEVEL K1, GATED -/

/-- `progLedgerVerifiedG nh P`: `AxClsStep.progLedgerVerified` with a gate structure `gsF` fixed
for the program, handouts admissible for the canonical deferring order (deferral-safe or a gate
source), and the WPds at the FROZEN-SLOT ledger instance `obStInterpLG`. -/
inductive progLedgerVerifiedG (nh : Nat) (P : Aprog) : Prop where
  | mk (GF : BundledGFunctors.{0,0,0}) [HannG : AxannotG GF] [HlG : LedgerG GF]
      [Hpre : InvGpreS GF] [pol : Axpol] (OC : Int → Prop) (L0 : Ledger)
      (gsF : Gdexec → Geid → GSet Geid)
      (N0 obSt0 : Type) (base0 : N0 → Gdexec → obSt0 → GSet Geid → IProp GF)
      (init : N0 × GName → Agent → IProp GF)
      (post : Agent → Athread → Prop)
      (Hwf : axpolWf)
      (Hver : ∀ GD, progRealizes P GD → rvwmoCatConsistent GD →
        (∀ w a v, w ∈ GD.gdG.gxGmo → tidHart nh (some w.1) →
          glblIs GD.gdG w lbPlain → gwritesByte GD.gdG w a v → OC a) ∧
        (∀ [InvGS_gen .hasNoLC GF] [AxannotGS GF] (nm : N0 × GName),
          ⊢ ([∗list] i ∈ P.apHarts, init nm i) -∗
            [∗list] i ∈ P.apHarts,
              tierAWpd GD (N0 × GName) obSt0 (obStInterpLG OC nh L0 gsF base0) nm (P.apS0 i)
                .MaybeStuck i (fun s => iprop(⌜post i s⌝))) ∧
        (⊢ |==> ∃ (nm : N0 × GName) (σ0 : obSt0),
          obStInterpLG OC nh L0 gsF base0 nm GD σ0 ∅ ∗ [∗list] i ∈ P.apHarts, init nm i) ∧
        gateReal GD (gsF GD) ∧ gateMono GD (gsF GD) ∧
        (∀ e e', e' ∈ Axpol.sPol GD e ∪ Axpol.lobp GD e →
          polDS GD.gdG (gsF GD) e' e ∨ e' ∈ gsF GD e))

/-- Timeline extraction at every realized consistent graph. -/
theorem progTlG (nh : Nat) (P : Aprog) :
    progLedgerVerifiedG nh P →
    ∀ GD, progRealizes P GD → rvwmoCatConsistent GD →
      ∃ (OC : Int → Prop) (own : Int → Nat → Option Nat), gtlOk OC nh GD.gdG own ∧
        (∀ w a v, w ∈ GD.gdG.gxGmo → tidHart nh (some w.1) →
          glblIs GD.gdG w lbPlain → gwritesByte GD.gdG w a v → OC a) := by
  intro Hv GD Hreal Hcons
  refine progLedgerVerifiedG.casesOn (motive := fun _ => _) Hv ?_
  intro GF HannG HlG Hpre pol OC L0 gsF N0 obSt0 base0 init post Hwf Hver
  obtain ⟨Hplain, Hwp, Hob, Hgr, Hgm, Hok⟩ := Hver GD Hreal Hcons
  obtain ⟨Hnd, _, Hharts, Hk0, n, sN, rN, Hr⟩ := Hreal
  obtain ⟨own, Htl⟩ := tierAAdequacyLedgerGTl GD OC nh L0 gsF N0 obSt0 base0 init Hwf Hcons
    P.apHarts Hnd Hharts P.apS0 sN n
    (fun _ nm i Hi => clsNstepsTierA GD nm i (n i) (P.apS0 i, false) (sN i, rN i) (Hr i Hi).1)
    Hk0 (fun i Hi => (Hr i Hi).2) post Hwp Hob Hgr Hgm Hok
  exact ⟨OC, own, Htl, Hplain⟩

/-- PROGRAM-LEVEL K1 (gated). -/
theorem progViolFreeG (nh : Nat) (P : Aprog) :
    progLedgerVerifiedG nh P →
    ∀ GD, progRealizes P GD → rvwmoCatConsistent GD → ¬ gdviolationHart nh GD := by
  intro Hv GD Hreal Hcons
  obtain ⟨OC, own, Htl, Hplain⟩ := progTlG nh P Hv GD Hreal Hcons
  exact ownedNoViolationCat OC nh GD own Hcons Htl Hplain

theorem progNotVerifiedGOfViol (nh : Nat) (P : Aprog) (GD : Gdexec) :
    progRealizes P GD → rvwmoCatConsistent GD → gdviolationHart nh GD →
    ¬ progLedgerVerifiedG nh P :=
  fun Hr Hc Hv Hver => progViolFreeG nh P Hver GD Hr Hc Hv

end Weak
