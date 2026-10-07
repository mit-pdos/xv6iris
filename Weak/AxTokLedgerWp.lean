/-
Weak: **K1 jobs J2 + J3 — THE IN-FLIGHT LEDGER THREADED THROUGH PHASE 2** (LB/AxSL): the ledger
of `AxTokLedger` carried in the phase-2 state interpretation beside any base protocol; the
prefix invariant `AxTokLedgerWp.ledgerInv`; the ledger-aware flow-equation combinators
(`flowEqLedger`, `flowEqLedgerJoint`, `wpEvStepLedger(Joint)`); `AxTierA3`'s gmo adequacy
KEEPING the final phase-2 state (`tierAAdequacyFinalGmo`); J2 `tierAAdequacyLedger(Tl)` (a legal
ledger history / an ownership timeline); J3 `tlExtractionLedger` and `adequacyViolFreeLedger`
for `ledgerVerified` programs; the non-vacuity certificates (`mpPlainNotLedgerVerified`; the
four flow equations of `AxViol.mp`, their composition `mpPhase2` and the closed `mpPhase2Closed`).

Rocq: `iris/AxTokLedgerWp.v` @ xxvzwolszwmp.

## The Rocq header, in substance

DESIGN (option (i) of the K1 plan).  The ledger lives in the PHASE-2 state interpretation:
`obStInterpL nm GD σ s := base0 nm.1 GD σ s ∗ ledgerInv OC nh nm.2 GD s` (an `axGA2` instance at
`nm : N0 × GName`; no new record, no edit of `AxWp`).  `ledgerInv γ GD s` := ∃ n LH, `s` is the
first `n` gmo events ∗ `LH` is a legal history for them (`ledgerPrefixOk`) ∗ `ledgerInterp γ LH`.
Consequences: nothing in `wpd`/`wpEvStep` changes — every flow equation of the instance must
perform ONE legal `ledgerStep` at `e`, so the per-step access check is enforced by the INSTANCE.
INDEXING: the ledger is indexed by gmo position; with the FULL gmo-prefix handout
(`gmoPrefix e ⊆ sPol e`, the premise of every rule) and `sOb` a gmo prefix, `e` IS the next gmo
event (`gmoNextOfPrefix`), hence the gate-free `_gmo` adequacy of `AxTierA3`.  CROSS-HART
TRANSFER: lobp/flowIn is same-hart only, so a release parks its pending tokens in the BASE state
and the acquire takes them there — the general combinator is JOINT (`ledgerJoint`).

§1 pure prefix invariant; §2 `ledgerInv` (init / open / full read-back); §3 one event's ledger
action (`toksAgree`, `toksUpdate`, `ledgerActGen`); §4 flow-equation combinators at any instance
with `HobExt : obStInterp ⊣⊢ base ∗ ledgerInv`; §5 `tierAFinalCore` / `tierAAdequacyFinalGmo`;
§6 J2; §7 J3 (`ledgerVerified`); §8 non-vacuity.  HONESTY (as Rocq): the positive certificate is
PHASE 2 only (`ledgerVerified 2 mp` is not proved); gate-free runs only; existing `protInv`
rules are reusable only through their flow-equation lemmas (`flowEqBaseOfDyn`).

**Fetches (Stage C).** `AxViol.mp` has no fetch row; the ledger is indexed by gmo position over
memory events only, so nothing is re-indexed.  `gmoPrefix`/position facts of `mp` are recomputed
by `decide +kernel`.

## Deviations from Rocq

1. NAMES: camelCase (map below).  The duplicated Rocq name `ledger_inv` (also in `AxEpiLedger`) is
   FILE-QUALIFIED `AxTokLedgerWp.ledgerInv`; Lean-only helpers are file-qualified
   `AxTokLedgerWp.*`.  `AxTokLedger.ledger_step` is `AxTokLedger.ledgerStep`.
2. VOCABULARY (as `AxTokLedger`/`AxTierA2`): `list_to_set` ↦ `LawfulSet.ofList`, `{[e]} ∪ s` ↦
   `({e} : GSet Geid) ∪ s`, `S n` ↦ `n + 1`, `NoDup` ↦ `List.Nodup`, `gx_gmo (gd_g GD)` ↦
   `GD.gdG.gxGmo`, `sum_list (n <$> harts)` ↦ `(harts.map n).sum`, `<[(i,k) := R]> na` ↦
   `insert na (i, k) R`, `|={⊤}[∅]▷=>^n` ↦ `|={⊤}[∅]▷=>^[n]`, `vm_compute` ↦ `decide +kernel`.
3. O2 STAGE C (as AxTierA2/AxTierA3): `AxirisG` has no `ax_text`, so the section parameter `T`
   is gone from §5–§7 (and from `ledgerVerified`'s fields) and `mpAxirisG` has no `ax_text`.
4. CONTEXTS: Rocq's section contexts (`OC nh γL base Hob_ext`) are explicit leading arguments;
   `invGS_gen HasNoLc Σ` ↦ `[InvGS_gen hlc GF]` for any `hlc` (soundness at `.hasNoLC`);
   `[Axpol]`/`[AxirisG GF]`/`[LedgerG GF]` are instance binders.  Wand chains are
   `⊢ A -∗ B -∗ …`; `mp_fe_00`'s `toks 0 ⊢ …` is `⊢ toks 0 -∗ …`.
5. `ledger_verified` is an inductive Prop `ledgerVerified` with constructor `ledgerVerified.mk`;
   its `Σ` is `GF : BundledGFunctors.{0,0,0}` and the classes are instance binders.
6. `mpΣ := #[invΣ; ledgerΣ]` ↦ `mpGF`, an explicit slot table over `BundledGFunctors.default`
   (as `Xv6.Xv6GF`; iris-lean has no `gFunctors` lists): wsat + credits at slots 0–3, the ledger's
   ghost map at slot 4; the `ElemG`/`InvGpreS`/`LedgerG` instances are `AxTokLedgerWp.mpGF*`.
7. The Ltac `mp_cond_eval` is replaced by the Lean-only rewrite lemmas `AxTokLedgerWp.baseMpOff`
   / `baseMpOn` (fed with `mpCond0..4`); Rocq `Local Notation`s `w_rl`/`r_aq`/`toks`/`Spre` are
   written out (`toks` is the Lean-only abbrev `AxTokLedgerWp.toks`).
8. PROOF ROUTE (not statements): `toksAgree`/`ledgerActGen` read the auth without consuming it
   via the Lean-only `AxTokLedgerWp.ledgerAgreeKeep`/`toksAgreeKeep`; the pure part of
   `ledgerActGen` is `AxTokLedgerWp.ledgerActGenPure`; `ledgerPrefixOkFull` gets `n = length`
   from `NoDup` lookups instead of set sizes; `wpEvStepLedger` uses the Lean-only
   `AxTokLedgerWp.naSplittingWfEmpty`/`annotInsertEq` (copies of AxLockWp's, not imported);
   `mpPhase2` discharges its set side conditions with `AxTokLedgerWp.ofListSub`/`ofListPerm`.

**Rocq → Lean name map.**  `ledger_prefix_ok` `ledgerPrefixOk`, `ledger_prefix_ok_init`
`ledgerPrefixOkInit`, `gmo_next_of_prefix` `gmoNextOfPrefix`, `ledger_prefix_ok_step`
`ledgerPrefixOkStep`, `take_S_set` `takeSSet`, `ledger_prefix_ok_full` `ledgerPrefixOkFull`,
`ledger_inv` `AxTokLedgerWp.ledgerInv`, `ledger_inv_init` `ledgerInvInit`, `ledger_inv_open`
`ledgerInvOpen`, `ledger_inv_full` `ledgerInvFull`, `ledger_set` `ledgerSet`,
`ledger_set_lookup_in` `ledgerSetLookupIn`, `ledger_set_lookup_nin` `ledgerSetLookupNin`,
`toks_agree` `toksAgree`, `toks_update` `toksUpdate`, `ledger_act_gen` `ledgerActGen`,
`flow_eq_base` `flowEqBase`, `flow_eq_base_of_dyn` `flowEqBaseOfDyn`, `flow_eq_base_pol_mono`
`flowEqBasePolMono`, `ledger_act` `ledgerAct`, `flow_eq_ledger` `flowEqLedger`, `ledger_joint`
`ledgerJoint`, `flow_eq_ledger_joint` `flowEqLedgerJoint`, `ledger_act_of_gen` `ledgerActOfGen`,
`ledger_act_neutral` `ledgerActNeutral`, `wp_ev_step_ledger` `wpEvStepLedger`,
`wp_ev_step_ledger_joint` `wpEvStepLedgerJoint`, `tierA_final_core` `tierAFinalCore`,
`tierA_adequacy_final_gmo` `tierAAdequacyFinalGmo`, `ob_st_interpL` `obStInterpL`,
`AxGA2_ledger_ob_ext` `axGA2LedgerObExt`, `tierA_adequacy_ledger` `tierAAdequacyLedger`,
`tierA_adequacy_ledger_tl` `tierAAdequacyLedgerTl`, `ledger_verified` `ledgerVerified`
(`LedgerVerified` `ledgerVerified.mk`), `tl_extraction_ledger` `tlExtractionLedger`,
`adequacy_viol_free_ledger` `adequacyViolFreeLedger`, `mp_plain_not_ledger_verified`
`mpPlainNotLedgerVerified`, `mp_cond` `mpCond`, `base_mp` `baseMp`, `mp_gmo` `mpGmo`,
`mp_cond_0..4` `mpCond0..4`, `OC_mp_in` `ocMpIn`, `mp_wf` `mpWf`, `mp_fe_00/02/10/11`
`mpFe00/02/10/11`, `mp_phase2` `mpPhase2`, `mp_axirisG` `mpAxirisG`, `mp_axirisG_ext`
`mpAxirisGExt`, `mp_pol` `mpPol`, `mp_phase2_sound` `mpPhase2Sound`, `mpΣ` `mpGF`,
`mp_phase2_closed` `mpPhase2Closed`.

**Not ported:** the Ltac `mp_cond_eval` (deviation 7); the `Print Assumptions` audits (the lint's
axiom check covers them).
-/
import Weak.AxTierA3
import Weak.AxTokLedger
import Weak.AxBridge

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std Iris.Std.PartialMap MachCSL MachCSL.Stdpp

/-! # 1. THE PURE PREFIX INVARIANT -/

/-- After validating the first `n` gmo events, the ledger history `LH` has `n + 1` entries,
adjacent entries related by the event at that gmo position. -/
def ledgerPrefixOk (OC : Int → Prop) (nh : Nat) (GD : Gdexec) (n : Nat) (LH : List Ledger) :
    Prop :=
  LH.length = n + 1 ∧ n ≤ GD.gdG.gxGmo.length ∧
  ∀ k e L L', GD.gdG.gxGmo[k]? = some e → LH[k]? = some L → LH[k + 1]? = some L' →
    AxTokLedger.ledgerStep OC nh GD e L L'

theorem ledgerPrefixOkInit (OC : Int → Prop) (nh : Nat) (GD : Gdexec) (L0 : Ledger) :
    ledgerPrefixOk OC nh GD 0 [L0] := by
  refine ⟨rfl, Nat.zero_le _, ?_⟩
  intro k e L L' _ _ HL'
  cases k with
  | zero => cases HL'
  | succ k => cases HL'

/-- With the FULL gmo-prefix handout, the only facts a flow equation knows pin `e` as the next
gmo event. -/
theorem gmoNextOfPrefix (G : Gexec) (n : Nat) (e : Geid) :
    G.gxGmo.Nodup → e ∈ G.gxGmo →
    (LawfulSet.ofList (gmoPrefix G e) : GSet Geid) ⊆ LawfulSet.ofList (G.gxGmo.take n) →
    e ∉ (LawfulSet.ofList (G.gxGmo.take n) : GSet Geid) →
    G.gxGmo[n]? = some e := by
  intro Hnd He Hsub Hnin
  have Hp := gposElemLookup G e He
  rcases Nat.lt_trichotomy (gpos G e) n with Hlt | Heq | Hgt
  · exact absurd ((elemOfListToSet (S := GSet Geid)).2 (elem_of_take.2 ⟨_, Hp, Hlt⟩)) Hnin
  · rw [← Heq]
    exact Hp
  · exfalso
    have Hlen : n < G.gxGmo.length := Nat.lt_trans Hgt (lookup_lt_Some Hp)
    have Hx : G.gxGmo[n]? = some (G.gxGmo[n]'Hlen) := List.getElem?_eq_getElem Hlen
    have Hxin : G.gxGmo[n]'Hlen ∈ gmoPrefix G e := elem_of_take.2 ⟨n, Hx, Hgt⟩
    have Hx2 := Hsub _ ((elemOfListToSet (S := GSet Geid)).2 Hxin)
    obtain ⟨j, Hj, Hjlt⟩ := elem_of_take.1 ((elemOfListToSet (S := GSet Geid)).1 Hx2)
    have := NoDup_lookup Hnd Hj Hx
    omega

/-- Lean-only: the last entry of a history of length `k + 1` is its `k`-th. -/
theorem AxTokLedgerWp.lhCurOfLookup (LH : List Ledger) (k : Nat) (L : Ledger) :
    LH.length = k + 1 → LH[k]? = some L → lhCur LH = L := by
  intro Hlen HL
  unfold lhCur
  rw [List.getLast?_eq_getElem?, Hlen, Nat.add_sub_cancel, HL]
  rfl

theorem ledgerPrefixOkStep (OC : Int → Prop) (nh : Nat) (GD : Gdexec) (n : Nat)
    (LH : List Ledger) (e : Geid) (L' : Ledger) :
    ledgerPrefixOk OC nh GD n LH → GD.gdG.gxGmo[n]? = some e →
    AxTokLedger.ledgerStep OC nh GD e (lhCur LH) L' →
    ledgerPrefixOk OC nh GD (n + 1) (LH ++ [L']) := by
  rintro ⟨Hlen, _, Hst⟩ Hn Hstep
  refine ⟨by simp [Hlen], lookup_lt_Some Hn, ?_⟩
  intro k e' L L2 Hk HL HL2
  by_cases Hkn : k = n
  · subst Hkn
    rw [Hn] at Hk
    obtain rfl := Option.some.inj Hk
    rw [List.getElem?_append_left (by omega)] at HL
    rw [List.getElem?_append_right (by omega), Hlen, Nat.sub_self] at HL2
    obtain rfl : L' = L2 := Option.some.inj HL2
    rw [← AxTokLedgerWp.lhCurOfLookup LH k L Hlen HL]
    exact Hstep
  · have Hk' : k + 1 < LH.length := by
      have := lookup_lt_Some HL2
      simp at this
      omega
    rw [List.getElem?_append_left (by omega)] at HL HL2
    exact Hst k e' L L2 Hk HL HL2

theorem takeSSet (l : List Geid) (n : Nat) (e : Geid) :
    l[n]? = some e →
    (LawfulSet.ofList (l.take (n + 1)) : GSet Geid) = ({e} : GSet Geid) ∪ LawfulSet.ofList (l.take n) := by
  intro Hn
  have Htake : l.take (n + 1) = l.take n ++ [e] := by
    rw [List.take_add_one, Hn]
    rfl
  rw [Htake, listToSetApp, listToSetCons, listToSetNil, setEq]
  intro x
  rw [elemOfUnion, elemOfUnion, elemOfUnion]
  constructor
  · rintro (h | h | h)
    · exact .inr h
    · exact .inl h
    · exact absurd h notElemOfEmpty
  · rintro (h | h)
    · exact .inr (.inl h)
    · exact .inl h

/-- At the FULL validated set, the prefix invariant IS `ledgerHistOkList`. -/
theorem ledgerPrefixOkFull (OC : Int → Prop) (nh : Nat) (GD : Gdexec) (n : Nat)
    (LH : List Ledger) :
    GD.gdG.gxGmo.Nodup → ledgerPrefixOk OC nh GD n LH →
    (LawfulSet.ofList GD.gdG.gxGmo : GSet Geid) = LawfulSet.ofList (GD.gdG.gxGmo.take n) →
    ledgerHistOkList OC nh GD LH := by
  rintro Hnd ⟨Hlen, Hle, Hst⟩ Hset
  have Hn : n = GD.gdG.gxGmo.length := by
    refine Nat.le_antisymm Hle (Nat.not_lt.1 fun Hlt => ?_)
    have Hx : GD.gdG.gxGmo[n]? = some (GD.gdG.gxGmo[n]'Hlt) := List.getElem?_eq_getElem Hlt
    have Hx1 : GD.gdG.gxGmo[n]'Hlt ∈ (LawfulSet.ofList GD.gdG.gxGmo : GSet Geid) :=
      (elemOfListToSet (S := GSet Geid)).2 (elem_of_list_lookup_2 Hx)
    rw [Hset] at Hx1
    obtain ⟨j, Hj, Hjlt⟩ := elem_of_take.1 ((elemOfListToSet (S := GSet Geid)).1 Hx1)
    have := NoDup_lookup Hnd Hj Hx
    omega
  exact ⟨by rw [Hlen, Hn], Hst⟩

/-! # 2. THE LEDGER PIECE OF THE STATE INTERPRETATION -/

section ledgerInv
variable {GF : BundledGFunctors} [LedgerG GF]

/-- `ledgerInv γ GD s`: the validated set `s` is the first `n` gmo events and the ledger history
for them is legal. -/
def AxTokLedgerWp.ledgerInv (OC : Int → Prop) (nh : Nat) (γ : GName) (GD : Gdexec)
    (s : GSet Geid) : IProp GF :=
  iprop(∃ (n : Nat) (LH : List Ledger),
    ⌜ledgerPrefixOk OC nh GD n LH ∧ s = LawfulSet.ofList (GD.gdG.gxGmo.take n)⌝ ∗
    ledgerInterp γ LH)

theorem ledgerInvInit (OC : Int → Prop) (nh : Nat) (γ : GName) (GD : Gdexec) (L0 : Ledger) :
    ledgerAuth (GF := GF) γ L0 ⊢ AxTokLedgerWp.ledgerInv OC nh γ GD ∅ := by
  unfold AxTokLedgerWp.ledgerInv
  iintro Ha
  iexists 0, [L0]
  rw [show ledgerInterp (GF := GF) γ [L0] = ledgerAuth γ L0 from rfl]
  isplitr
  · ipureintro
    exact ⟨ledgerPrefixOkInit OC nh GD L0, listToSetNil.symm⟩
  · iexact Ha

/-- Opening at a flow equation for `e`: the current ledger, and the way back given one legal
`ledgerStep` at `e`. -/
theorem ledgerInvOpen (OC : Int → Prop) (nh : Nat) (γ : GName) (GD : Gdexec) (s : GSet Geid)
    (e : Geid) (Hwf : gwf GD.gdG) (He : e ∈ GD.gdG.gxGmo)
    (Hpref : (LawfulSet.ofList (gmoPrefix GD.gdG e) : GSet Geid) ⊆ s) (Hnin : e ∉ s) :
    ⊢ AxTokLedgerWp.ledgerInv (GF := GF) OC nh γ GD s -∗
      ∃ L, ledgerAuth γ L ∗
        (∀ L', ⌜AxTokLedger.ledgerStep OC nh GD e L L'⌝ -∗ ledgerAuth γ L' -∗
          AxTokLedgerWp.ledgerInv OC nh γ GD (({e} : GSet Geid) ∪ s)) := by
  unfold AxTokLedgerWp.ledgerInv
  iintro ⟨%n, %LH, %Hp, Ha⟩
  obtain ⟨Hok, Hs⟩ := Hp
  subst Hs
  have Hn := gmoNextOfPrefix GD.gdG n e Hwf.1 He Hpref Hnin
  iunfold ledgerInterp at Ha
  iexists (lhCur LH)
  isplitl [Ha]
  · iexact Ha
  · iintro %L' %Hst Ha
    iexists (n + 1), (LH ++ [L'])
    isplitr
    · ipureintro
      exact ⟨ledgerPrefixOkStep OC nh GD n LH e L' Hok Hn Hst, (takeSSet _ _ _ Hn).symm⟩
    · iapply ledgerInterpAppend γ LH L'
      iexact Ha

/-- READ-BACK at the full validated set. -/
theorem ledgerInvFull (OC : Int → Prop) (nh : Nat) (γ : GName) (GD : Gdexec) :
    gwf GD.gdG →
    AxTokLedgerWp.ledgerInv (GF := GF) OC nh γ GD (LawfulSet.ofList GD.gdG.gxGmo) ⊢
      ⌜∃ LH, ledgerHistOkList OC nh GD LH⌝ := by
  intro Hwf
  unfold AxTokLedgerWp.ledgerInv
  iintro ⟨%n, %LH, %Hp, -⟩
  ipureintro
  exact ⟨LH, ledgerPrefixOkFull OC nh GD n LH Hwf.1 Hp.1 Hp.2⟩

end ledgerInv

/-! # 3. ONE EVENT'S LEDGER ACTION, assembled from §3.1 of `AxTokLedger` -/

def ledgerSet (As : List Int) (h : Holder) (L : Ledger) : Ledger :=
  match As with
  | [] => L
  | a :: As' => ledgerSet As' h (insert L a h)

theorem ledgerSetLookupNin (As : List Int) (h : Holder) (L : Ledger) (a : Int) :
    a ∉ As → get? (ledgerSet As h L) a = get? L a := by
  induction As generalizing L with
  | nil => intro _; rfl
  | cons b As IH =>
    intro Ha
    have Hab : a ≠ b := fun Heq => Ha (Heq ▸ List.mem_cons_self)
    have Has : a ∉ As := fun Hin => Ha (List.mem_cons_of_mem _ Hin)
    show get? (ledgerSet As h (insert L b h)) a = _
    rw [IH _ Has, get?_insert_ne (Ne.symm Hab)]

theorem ledgerSetLookupIn (As : List Int) (h : Holder) (L : Ledger) (a : Int) :
    a ∈ As → get? (ledgerSet As h L) a = some h := by
  induction As generalizing L with
  | nil => intro Ha; cases Ha
  | cons b As IH =>
    intro Ha
    show get? (ledgerSet As h (insert L b h)) a = _
    by_cases Hin : a ∈ As
    · exact IH _ Hin
    · have Hab : a = b := by
        rcases List.mem_cons.1 Ha with h' | h'
        · exact h'
        · exact absurd h' Hin
      rw [ledgerSetLookupNin As h _ a Hin, get?_insert_eq Hab.symm]

section act
variable {GF : BundledGFunctors} [LedgerG GF]

/-- Lean-only: agreement of one fragment with the auth, both kept. -/
theorem AxTokLedgerWp.ledgerAgreeKeep (γ : GName) (L : Ledger) (a : Int) (h : Holder) :
    ⊢ ledgerAuth (GF := GF) γ L -∗ tokFrag γ a h -∗
      ⌜get? L a = some h⌝ ∗ ledgerAuth γ L ∗ tokFrag γ a h := by
  unfold ledgerAuth tokFrag
  iintro Ha Hf
  icombine Ha Hf gives %hL
  isplitr
  · ipureintro
    exact hL
  isplitl [Ha]
  · iexact Ha
  · iexact Hf

/-- Lean-only: `toksAgree`, keeping the auth and the fragments. -/
theorem AxTokLedgerWp.toksAgreeKeep (γ : GName) (L : Ledger) (As : List Int)
    (old : Int → Holder) :
    ⊢ ledgerAuth (GF := GF) γ L -∗ ([∗list] a ∈ As, tokFrag γ a (old a)) -∗
      ⌜∀ a, a ∈ As → get? L a = some (old a)⌝ ∗ ledgerAuth γ L ∗
        [∗list] a ∈ As, tokFrag γ a (old a) := by
  induction As with
  | nil =>
    iintro Ha Hf
    isplitr
    · ipureintro
      intro a Ha
      cases Ha
    isplitl [Ha]
    · iexact Ha
    · iexact Hf
  | cons b As IH =>
    iintro Ha Hf
    icases BigSepL.bigSepL_cons.1 $$ Hf with ⟨Hb, Hf⟩
    icases AxTokLedgerWp.ledgerAgreeKeep γ L b (old b) $$ Ha Hb with ⟨%h1, Ha, Hb⟩
    icases IH $$ Ha Hf with ⟨%h2, Ha, Hf⟩
    isplitr
    · ipureintro
      intro a Ha'
      rcases List.mem_cons.1 Ha' with rfl | Ha'
      · exact h1
      · exact h2 a Ha'
    isplitl [Ha]
    · iexact Ha
    · iapply BigSepL.bigSepL_cons.2
      isplitl [Hb]
      · iexact Hb
      · iexact Hf

/-- A family of fragments agrees with the auth (nothing changes). -/
theorem toksAgree (γ : GName) (L : Ledger) (As : List Int) (old : Int → Holder) :
    ⊢ ledgerAuth (GF := GF) γ L -∗ ([∗list] a ∈ As, tokFrag γ a (old a)) -∗
      ⌜∀ a, a ∈ As → get? L a = some (old a)⌝ := by
  iintro Ha Hf
  icases AxTokLedgerWp.toksAgreeKeep γ L As old $$ Ha Hf with ⟨%h, -, -⟩
  ipureintro
  exact h

/-- A family of fragments rewritten to one holder `hnew`. -/
theorem toksUpdate (γ : GName) (L : Ledger) (As : List Int) (old : Int → Holder) (hnew : Holder) :
    As.Nodup →
    ⊢ ledgerAuth (GF := GF) γ L -∗ ([∗list] a ∈ As, tokFrag γ a (old a)) ==∗
      ledgerAuth γ (ledgerSet As hnew L) ∗ ([∗list] a ∈ As, tokFrag γ a hnew) ∗
      ⌜∀ a, a ∈ As → get? L a = some (old a)⌝ := by
  induction As generalizing L with
  | nil =>
    intro _
    rw [show ledgerSet [] hnew L = L from rfl]
    iintro Ha -
    imodintro
    isplitl [Ha]
    · iexact Ha
    isplitr
    · iapply (BigSepL.bigSepL_nil (Φ := fun _ (a : Int) => tokFrag (GF := GF) γ a hnew)).2
      iempintro
    · ipureintro
      intro a Ha
      cases Ha
  | cons b As IH =>
    intro Hnd
    obtain ⟨Hb, Hnd'⟩ := List.nodup_cons.1 Hnd
    rw [show ledgerSet (b :: As) hnew L = ledgerSet As hnew (insert L b hnew) from rfl]
    iintro Ha Hf
    icases BigSepL.bigSepL_cons.1 $$ Hf with ⟨Hfb, Hf⟩
    icases AxTokLedgerWp.ledgerAgreeKeep γ L b (old b) $$ Ha Hfb with ⟨%Hlb, Ha, Hfb⟩
    imod ledgerUpdate γ L b (old b) hnew $$ Ha Hfb with ⟨Ha, Hfb⟩
    imod IH (insert L b hnew) Hnd' $$ Ha Hf with ⟨Ha, Hf, %Hrest⟩
    imodintro
    isplitl [Ha]
    · iexact Ha
    isplitl [Hfb Hf]
    · iapply BigSepL.bigSepL_cons.2
      isplitl [Hfb]
      · iexact Hfb
      · iexact Hf
    · ipureintro
      intro a Ha'
      rcases List.mem_cons.1 Ha' with rfl | Ha'
      · exact Hlb
      · have hne : b ≠ a := by
          rintro rfl
          exact Hb Ha'
        exact (get?_insert_ne hne).symm.trans (Hrest a Ha')

/-- Lean-only: the pure content of `ledgerActGen`. -/
theorem AxTokLedgerWp.ledgerActGenPure (OC : Int → Prop) (nh : Nat) (GD : Gdexec) (e : Geid)
    (L : Ledger) (Ah Ar Aq : List Int) (wq : Int → Geid)
    (Hrel : ∀ a, a ∈ Ar → glblIs GD.gdG e lbRelw)
    (Hacq : ∀ a, a ∈ Aq → acqFrom GD (wq a) e)
    (Hcov : ∀ a, OC a → tidHart nh (some e.1) → gaccesses GD.gdG e a →
      a ∈ Ah ∨ a ∈ Ar ∨ a ∈ Aq)
    (HAh : ∀ a, a ∈ Ah → get? L a = some (.held e.1))
    (HAr : ∀ a, a ∈ Ar → get? L a = some (.held e.1))
    (HAq : ∀ a, a ∈ Aq → get? (ledgerSet Ar (.pending e) L) a = some (.pending (wq a))) :
    AxTokLedger.ledgerStep OC nh GD e L
      (ledgerSet Aq (.held e.1) (ledgerSet Ar (.pending e) L)) := by
  have HL1 : ∀ a, a ∉ Ar → get? (ledgerSet Ar (.pending e) L) a = get? L a :=
    fun a Ha => ledgerSetLookupNin Ar _ L a Ha
  refine ⟨fun a => ?_, fun a HOC Hh Hacc => ?_⟩
  · by_cases Hq : a ∈ Aq
    · rw [ledgerSetLookupIn Aq _ _ a Hq]
      by_cases Hr : a ∈ Ar
      · rw [HAr a Hr]
        exact .lmSame _
      · rw [← HL1 a Hr, HAq a Hq]
        exact .lmAcquire _ (Hacq a Hq)
    · rw [ledgerSetLookupNin Aq _ _ a Hq]
      by_cases Hr : a ∈ Ar
      · rw [ledgerSetLookupIn Ar _ _ a Hr, HAr a Hr]
        exact .lmRelease (Hrel a Hr)
      · rw [HL1 a Hr]
        exact .lmSame _
  · rcases Hcov a HOC Hh Hacc with Hin | Hin | Hin
    · exact .inl (HAh a Hin)
    · exact .inl (HAr a Hin)
    · by_cases Hr : a ∈ Ar
      · exact .inl (HAr a Hr)
      · refine .inr ⟨wq a, ?_, ledgerSetLookupIn Aq _ _ a Hin⟩
        rw [← HL1 a Hr]
        exact HAq a Hin

/-- THE GENERAL ONE-EVENT ACTION at `e`: bytes `Ah` held and kept, bytes `Ar` released (only at
an `lbRelw` write), bytes `Aq` acquired from pending writes `wq a` (along `acqFrom`); every
Own-class byte `e` accesses is among them. -/
theorem ledgerActGen (OC : Int → Prop) (nh : Nat) (GD : Gdexec) (γ : GName) (L : Ledger)
    (e : Geid) (Ah Ar Aq : List Int) (wq : Int → Geid)
    (HndR : Ar.Nodup) (HndQ : Aq.Nodup)
    (Hrel : ∀ a, a ∈ Ar → glblIs GD.gdG e lbRelw)
    (Hacq : ∀ a, a ∈ Aq → acqFrom GD (wq a) e)
    (Hcov : ∀ a, OC a → tidHart nh (some e.1) → gaccesses GD.gdG e a →
      a ∈ Ah ∨ a ∈ Ar ∨ a ∈ Aq) :
    ⊢ ledgerAuth (GF := GF) γ L -∗
      ([∗list] a ∈ Ah, tokAt γ a e.1) -∗
      ([∗list] a ∈ Ar, tokAt γ a e.1) -∗
      ([∗list] a ∈ Aq, tokPending γ a (wq a)) ==∗
      ∃ L', ledgerAuth γ L' ∗ ⌜AxTokLedger.ledgerStep OC nh GD e L L'⌝ ∗
        ([∗list] a ∈ Ah, tokAt γ a e.1) ∗
        ([∗list] a ∈ Ar, tokPending γ a e) ∗
        ([∗list] a ∈ Aq, tokAt γ a e.1) := by
  unfold tokAt tokPending
  iintro Ha Hh Hr Hq
  icases AxTokLedgerWp.toksAgreeKeep γ L Ah (fun _ => .held e.1) $$ Ha Hh with ⟨%HAh, Ha, Hh⟩
  imod toksUpdate γ L Ar (fun _ => .held e.1) (.pending e) HndR $$ Ha Hr with ⟨Ha, Hr, %HAr⟩
  imod toksUpdate γ (ledgerSet Ar (.pending e) L) Aq (fun a => .pending (wq a)) (.held e.1) HndQ
    $$ Ha Hq with ⟨Ha, Hq, %HAq⟩
  imodintro
  iexists (ledgerSet Aq (.held e.1) (ledgerSet Ar (.pending e) L))
  isplitl [Ha]
  · iexact Ha
  isplitr
  · ipureintro
    exact AxTokLedgerWp.ledgerActGenPure OC nh GD e L Ah Ar Aq wq Hrel Hacq Hcov HAh HAr HAq
  isplitl [Hh]
  · iexact Hh
  isplitl [Hr]
  · iexact Hr
  · iexact Hq

end act

/-! # 4. LEDGER-AWARE FLOW EQUATIONS, at any instance whose state interpretation is
`base ∗ ledgerInv` -/

section flowBase
variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF]

/-- The flow equation of `flowEqDyn`, parametric in the state interpretation. -/
def flowEqBase {S : Type} (base : Gdexec → S → GSet Geid → IProp GF) (GD : Gdexec) (e : Geid)
    (sOb0 : GSet Geid) (flowIn : Mea GF) (R : IProp GF) : IProp GF :=
  iprop(∀ (σ : S) (sOb : GSet Geid),
    ⌜sOb0 ⊆ sOb⌝ -∗ ⌜e ∉ sOb⌝ -∗
    base GD σ sOb -∗ ([∗map] Rin ∈ flowIn, Rin) ={⊤,∅}=∗ ▷ |={∅,⊤}=>
    ∃ σ', base GD σ' (({e} : GSet Geid) ∪ sOb) ∗ R)

/-- Every flow equation of an instance IS a `flowEqBase` of its own state interpretation. -/
theorem flowEqBaseOfDyn [AxirisG GF] [Axpol] (GD : Gdexec) (e : Geid) (s0 : GSet Geid)
    (fin : Mea GF) (R : IProp GF) :
    flowEqDyn GD e s0 fin R ⊢ flowEqBase AxirisG.obStInterp GD e s0 fin R := .rfl

/-- A larger handout is a weaker requirement. -/
theorem flowEqBasePolMono {S : Type} (base : Gdexec → S → GSet Geid → IProp GF) (GD : Gdexec)
    (e : Geid) (s1 s2 : GSet Geid) (fin : Mea GF) (R : IProp GF) :
    s1 ⊆ s2 → flowEqBase base GD e s1 fin R ⊢ flowEqBase base GD e s2 fin R := by
  intro Hs
  unfold flowEqBase
  iintro H %σ %sOb %Hsub %Hnin Hb Hin
  have Hsub' : s1 ⊆ sOb := fun x hx => Hsub x (Hs x hx)
  iapply H $$ %σ %sOb %Hsub' %Hnin Hb Hin

end flowBase

section ledgerActDef
variable {GF : BundledGFunctors} [LedgerG GF]

/-- What one event does to the ledger: from the current ledger and the event's base output `R`,
a legal `ledgerStep` and the new output. -/
def ledgerAct (OC : Int → Prop) (nh : Nat) (γL : GName) (GD : Gdexec) (e : Geid)
    (R R' : IProp GF) : IProp GF :=
  iprop(∀ L, ledgerAuth γL L -∗ R ==∗
    ∃ L', ledgerAuth γL L' ∗ ⌜AxTokLedger.ledgerStep OC nh GD e L L'⌝ ∗ R')

/-- The general action of `ledgerActGen`, as a `ledgerAct`. -/
theorem ledgerActOfGen (OC : Int → Prop) (nh : Nat) (γL : GName) (GD : Gdexec) (e : Geid)
    (Ah Ar Aq : List Int) (wq : Int → Geid) (R : IProp GF)
    (HndR : Ar.Nodup) (HndQ : Aq.Nodup)
    (Hrel : ∀ a, a ∈ Ar → glblIs GD.gdG e lbRelw)
    (Hacq : ∀ a, a ∈ Aq → acqFrom GD (wq a) e)
    (Hcov : ∀ a, OC a → tidHart nh (some e.1) → gaccesses GD.gdG e a →
      a ∈ Ah ∨ a ∈ Ar ∨ a ∈ Aq) :
    ⊢ ledgerAct OC nh γL GD e
        iprop(([∗list] a ∈ Ah, tokAt γL a e.1) ∗ ([∗list] a ∈ Ar, tokAt γL a e.1) ∗
          ([∗list] a ∈ Aq, tokPending γL a (wq a)) ∗ R)
        iprop(([∗list] a ∈ Ah, tokAt γL a e.1) ∗ ([∗list] a ∈ Ar, tokPending γL a e) ∗
          ([∗list] a ∈ Aq, tokAt γL a e.1) ∗ R) := by
  unfold ledgerAct
  iintro %L Ha ⟨Hh, Hr, Hq, HR⟩
  imod ledgerActGen OC nh GD γL L e Ah Ar Aq wq HndR HndQ Hrel Hacq Hcov $$ Ha Hh Hr Hq
    with ⟨%L', Ha, %Hst, Hh, Hr, Hq⟩
  imodintro
  iexists L'
  isplitl [Ha]
  · iexact Ha
  isplitr
  · ipureintro
    exact Hst
  isplitl [Hh]
  · iexact Hh
  isplitl [Hr]
  · iexact Hr
  isplitl [Hq]
  · iexact Hq
  · iexact HR

/-- A LEDGER-NEUTRAL event: no Own-class byte accessed by a hart. -/
theorem ledgerActNeutral (OC : Int → Prop) (nh : Nat) (γL : GName) (GD : Gdexec) (e : Geid)
    (R : IProp GF)
    (Hno : ∀ a, OC a → tidHart nh (some e.1) → gaccesses GD.gdG e a → False) :
    ⊢ ledgerAct OC nh γL GD e R R := by
  unfold ledgerAct
  iintro %L Ha HR
  imodintro
  iexists L
  isplitl [Ha]
  · iexact Ha
  isplitr
  · ipureintro
    exact ⟨ledgerMovesRefl GD e L, fun a HOC Hh Hacc => (Hno a HOC Hh Hacc).elim⟩
  · iexact HR

end ledgerActDef

section flowLedger
variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [AxirisG GF] [LedgerG GF]

/-- THE JOINT FORM: the base protocol and the ledger step together, knowing the EXACT validated
set (the first `n` gmo events, `e` the `n`-th). -/
def ledgerJoint (OC : Int → Prop) (nh : Nat) (γL : GName)
    (base : Gdexec → AxirisG.obSt GF → GSet Geid → IProp GF) (GD : Gdexec) (e : Geid)
    (fin : Mea GF) (R : IProp GF) : IProp GF :=
  iprop(∀ (σ : AxirisG.obSt GF) (n : Nat) (L : Ledger),
    ⌜GD.gdG.gxGmo[n]? = some e⌝ -∗
    base GD σ (LawfulSet.ofList (GD.gdG.gxGmo.take n)) -∗ ledgerAuth γL L -∗
    ([∗map] Rin ∈ fin, Rin) ={⊤,∅}=∗ ▷ |={∅,⊤}=>
    ∃ (σ' : AxirisG.obSt GF) (L' : Ledger),
      base GD σ' (LawfulSet.ofList (GD.gdG.gxGmo.take (n + 1))) ∗
      ledgerAuth γL L' ∗ ⌜AxTokLedger.ledgerStep OC nh GD e L L'⌝ ∗ R)

variable [Axpol]

/-- THE COMBINATOR: a base flow equation plus a ledger action is a flow equation of the
ledger-extended instance; the only side condition is the full gmo-prefix handout. -/
theorem flowEqLedger (OC : Int → Prop) (nh : Nat) (γL : GName)
    (base : Gdexec → AxirisG.obSt GF → GSet Geid → IProp GF)
    (HobExt : ∀ (GD : Gdexec) (σ : AxirisG.obSt GF) (s : GSet Geid),
      AxirisG.obStInterp GD σ s ⊣⊢ base GD σ s ∗ AxTokLedgerWp.ledgerInv OC nh γL GD s)
    (GD : Gdexec) (e : Geid) (s0 : GSet Geid) (fin : Mea GF) (R Q R' : IProp GF)
    (Hwf : gwf GD.gdG) (He : e ∈ GD.gdG.gxGmo)
    (Hpref : (LawfulSet.ofList (gmoPrefix GD.gdG e) : GSet Geid) ⊆ s0) :
    ⊢ flowEqBase base GD e s0 fin iprop(R ∗ Q) -∗ ledgerAct OC nh γL GD e R R' -∗
      flowEqDyn GD e s0 fin iprop(R' ∗ Q) := by
  unfold flowEqDyn flowEqBase ledgerAct
  iintro Hf Hact %σ %sOb %Hsub %Hnin Hob Hin
  ihave Hob := (HobExt GD σ sOb).1 $$ Hob
  icases Hob with ⟨Hb, Hl⟩
  have Hpref' : (LawfulSet.ofList (gmoPrefix GD.gdG e) : GSet Geid) ⊆ sOb :=
    fun x hx => Hsub x (Hpref x hx)
  icases ledgerInvOpen OC nh γL GD sOb e Hwf He Hpref' Hnin $$ Hl with ⟨%L, Ha, Hclose⟩
  imod Hf $$ %σ %sOb %Hsub %Hnin Hb Hin with Hf
  imodintro
  inext
  imod Hf with ⟨%σ', Hb, HR, HQ⟩
  imod Hact $$ %L Ha HR with ⟨%L', Ha, %Hst, HR'⟩
  imodintro
  iexists σ'
  isplitl [Hb Ha Hclose]
  · iapply (HobExt GD σ' (({e} : GSet Geid) ∪ sOb)).2
    isplitl [Hb]
    · iexact Hb
    · iapply Hclose $$ %L' %Hst Ha
  · isplitl [HR']
    · iexact HR'
    · iexact HQ

theorem flowEqLedgerJoint (OC : Int → Prop) (nh : Nat) (γL : GName)
    (base : Gdexec → AxirisG.obSt GF → GSet Geid → IProp GF)
    (HobExt : ∀ (GD : Gdexec) (σ : AxirisG.obSt GF) (s : GSet Geid),
      AxirisG.obStInterp GD σ s ⊣⊢ base GD σ s ∗ AxTokLedgerWp.ledgerInv OC nh γL GD s)
    (GD : Gdexec) (e : Geid) (s0 : GSet Geid) (fin : Mea GF) (R : IProp GF)
    (Hwf : gwf GD.gdG) (He : e ∈ GD.gdG.gxGmo)
    (Hpref : (LawfulSet.ofList (gmoPrefix GD.gdG e) : GSet Geid) ⊆ s0) :
    ⊢ ledgerJoint OC nh γL base GD e fin R -∗ flowEqDyn GD e s0 fin R := by
  unfold flowEqDyn ledgerJoint
  iintro Hj %σ %sOb %Hsub %Hnin Hob Hin
  ihave Hob := (HobExt GD σ sOb).1 $$ Hob
  icases Hob with ⟨Hb, Hl⟩
  iunfold AxTokLedgerWp.ledgerInv at Hl
  icases Hl with ⟨%n, %LH, %Hp, Ha⟩
  obtain ⟨Hok, Hs⟩ := Hp
  subst Hs
  have Hn := gmoNextOfPrefix GD.gdG n e Hwf.1 He (fun x hx => Hsub x (Hpref x hx)) Hnin
  iunfold ledgerInterp at Ha
  imod Hj $$ %σ %n %(lhCur LH) %Hn Hb Ha Hin with Hj
  imodintro
  inext
  imod Hj with ⟨%σ', %L', Hb, Ha, %Hst, HR⟩
  imodintro
  iexists σ'
  isplitl [Hb Ha]
  · iapply (HobExt GD σ' (({e} : GSet Geid) ∪ LawfulSet.ofList (GD.gdG.gxGmo.take n))).2
    rw [← takeSSet _ _ _ Hn]
    isplitl [Hb]
    · iexact Hb
    · iunfold AxTokLedgerWp.ledgerInv
      iexists (n + 1), (LH ++ [L'])
      isplitr
      · ipureintro
        exact ⟨ledgerPrefixOkStep OC nh GD n LH e L' Hok Hn Hst, rfl⟩
      · iapply ledgerInterpAppend γL LH L'
        iexact Ha
  · iexact HR

/-- Lean-only (copy of `AxLockWp.naSplittingWfEmpty`): the empty splitting is well formed. -/
theorem AxTokLedgerWp.naSplittingWfEmpty (sLob : GSet Geid) (na : Mea GF) :
    ⊢ naSplittingWf sLob na (∅ : Mea GF) (∅ : Mea GF) := by
  unfold naSplittingWf
  isplitr
  · ipureintro
    rw [domEmpty]
    exact LawfulSet.empty_subset
  · iapply (BigSepM2.bigSepM2_empty _).2
    itrivial

/-- Lean-only (copy of `AxLockWp.annotInsertEq`). -/
theorem AxTokLedgerWp.annotInsertEq (na : Mea GF) (e : Geid) (R : IProp GF) :
    PartialMap.union (PartialMap.union {[e := R]} (∅ : Mea GF)) na = insert na e R := by
  have h1 : PartialMap.union ({[e := R]} : Mea GF) (∅ : Mea GF) = {[e := R]} :=
    mapUnionEmptyR (M := GMapF Geid)
  rw [h1]
  exact (insertUnionSingletonL (M := GMapF Geid)).symm

/-- THE WP-LEVEL RULE: a `wpEvStep` of the extended instance from a base flow equation (no local
flow) and a ledger action; `R'` is what lands in the event's annotation. -/
theorem wpEvStepLedger (OC : Int → Prop) (nh : Nat) (γL : GName)
    (base : Gdexec → AxirisG.obSt GF → GSet Geid → IProp GF)
    (HobExt : ∀ (GD : Gdexec) (σ : AxirisG.obSt GF) (s : GSet Geid),
      AxirisG.obStInterp GD σ s ⊣⊢ base GD σ s ∗ AxTokLedgerWp.ledgerInv OC nh γL GD s)
    {A : Type} (GD : Gdexec) (i : Agent) (k : Nat) (ok val : A → Prop) (k' : A → Nat)
    (Ψ : A → IProp GF) (x : A) (Hokx : ok x) (R R' : IProp GF) (ls' : AxirisG.logTsT GF)
    (Hwf : gwf GD.gdG) (He : (i, k) ∈ GD.gdG.gxGmo)
    (Hpref : (LawfulSet.ofList (gmoPrefix GD.gdG (i, k)) : GSet Geid) ⊆ Axpol.sPol GD (i, k))
    (Hnalloc : ⊢ ∀ na : Mea GF, naAtProgress GD i k na ∗ AxirisG.annotInterp na ==∗
      AxirisG.annotInterp (insert na (i, k) R')) :
    ⊢ flowEqBase base GD (i, k) (Axpol.sPol GD (i, k)) (∅ : Mea GF) iprop(R ∗ ⌜val x⌝) -∗
      ledgerAct OC nh γL GD (i, k) R R' -∗
      AxirisG.localInterp GD i (k' x) ls' -∗ Ψ x -∗
      wpEvStep GD i k ok val k' Ψ := by
  have Hn' : ⊢ ∀ na : Mea GF, naAtProgress GD i k na ∗ AxirisG.annotInterp na ==∗
      AxirisG.annotInterp (PartialMap.union (PartialMap.union {[(i, k) := R']} (∅ : Mea GF)) na) := by
    simp only [AxTokLedgerWp.annotInsertEq]
    exact Hnalloc
  iintro Hf Hact Hloc HΨ
  ihave Hfe := flowEqLedger OC nh γL base HobExt GD (i, k) (Axpol.sPol GD (i, k)) ∅ R
    iprop(⌜val x⌝) R' Hwf He Hpref $$ Hf Hact
  unfold wpEvStep
  iintro %na Hpg
  ihave Hn := Hn'
  imod Hn $$ %na Hpg with Hna
  imodintro
  inext
  imodintro
  iexists x, R', (∅ : Mea GF), (∅ : Mea GF), ls'
  isplitr
  · ipureintro
    exact Hokx
  isplitr
  · iapply AxTokLedgerWp.naSplittingWfEmpty
  iframe Hfe Hna Hloc HΨ

/-- THE WP-LEVEL JOINT RULE, with a local flow. -/
theorem wpEvStepLedgerJoint (OC : Int → Prop) (nh : Nat) (γL : GName)
    (base : Gdexec → AxirisG.obSt GF → GSet Geid → IProp GF)
    (HobExt : ∀ (GD : Gdexec) (σ : AxirisG.obSt GF) (s : GSet Geid),
      AxirisG.obStInterp GD σ s ⊣⊢ base GD σ s ∗ AxTokLedgerWp.ledgerInv OC nh γL GD s)
    {A : Type} (GD : Gdexec) (i : Agent) (k : Nat) (ok val : A → Prop) (k' : A → Nat)
    (Ψ : A → IProp GF) (x : A) (Hokx : ok x)
    (Hwf : gwf GD.gdG) (He : (i, k) ∈ GD.gdG.gxGmo)
    (Hpref : (LawfulSet.ofList (gmoPrefix GD.gdG (i, k)) : GSet Geid) ⊆ Axpol.sPol GD (i, k)) :
    ⊢ (∀ na : Mea GF, naAtProgress GD i k na ∗ AxirisG.annotInterp na ==∗
        ∃ (R : IProp GF) (naUsed : Mea GF) (naUnused : Mea GF) (ls' : AxirisG.logTsT GF),
          naSplittingWf (Axpol.lobp GD (i, k)) na naUsed naUnused ∗
          ledgerJoint OC nh γL base GD (i, k) naUsed iprop(R ∗ ⌜val x⌝) ∗
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
  · iapply flowEqLedgerJoint OC nh γL base HobExt GD (i, k) (Axpol.sPol GD (i, k)) nu
      iprop(R ∗ ⌜val x⌝) Hwf He Hpref $$ Hj
  iframe Hna Hloc HΨ

end flowLedger

/-! # 5. ADEQUACY WITH A READ-BACK OF THE FINAL PHASE-2 STATE

`AxTierA3.tierAAdequacyAnnCoreGmo` computes the final `∃ σ, obStInterp GD σ (ofList sProc)` and
discards it; the copy below keeps it: any pure consequence `Q` of the final state holds. -/

section finalFixed
variable {GF : BundledGFunctors.{0,0,0}}

theorem tierAFinalCore {hlc : HasLC} [InvGS_gen hlc GF] [AxannotGS GF] [Axpol]
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
    (sst : Sstate) (HrunSched : rtc (schedStep GD.gdG) sst0 sst)
    (Hfull : sst.sN = GD.gdG.gxGmo.length) (Hdone : sst.sD = ∅)
    (Hgatefree : sst.sEverD = ∅)
    (HsPolGmo : ∀ e e', e' ∈ Axpol.sPol GD e → gmoLt GD.gdG e' e)
    (HlobpGmo : ∀ e e', e' ∈ Axpol.lobp GD e → gmoLt GD.gdG e' e)
    (Hcov : (unionList (harts.map fun i => eidsBefore GD i (AxOpsem.grow GD i).length) :
        GSet Geid) = LawfulSet.ofList sst.sProc)
    (Q : Prop)
    (Hread : ∀ σ, obStInterp0 nm GD σ (LawfulSet.ofList sst.sProc) ⊢ ⌜Q⌝)
    (σ0 : obSt0) :
    ⊢ AxAnnot.annotInterp (∅ : Mea GF) -∗ obStInterp0 nm GD σ0 ∅ -∗
      ([∗list] i ∈ harts, init nm i) -∗
      |={⊤}[∅]▷=>^[(harts.map n).sum + (1 + sst.sProc.length)] ⌜Q⌝ := by
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
  have HI := invRtc GD.gdG (schedHGwf GD Hcons) (schedHCat6gmo GD Hcons) sst HrunSched
  have Hndp := HI.invNodup
  have Hfmap : (harts.map fun j => eidsBefore GD j (sN j).atK) =
      harts.map fun j => eidsBefore GD j (AxOpsem.grow GD j).length :=
    List.map_congr_left fun j Hj => by rw [Hend j Hj]
  have Hpol := gatefreeAxpolWfProc GD Hcons sst HrunSched Hfull Hdone Hgatefree HsPolGmo HlobpGmo
  iintro Hannot0 Hob0 Hinit
  ihave HWPall := Hwp $$ Hinit
  ihave Hbig := Hbig0 $$ HWPall
  ihave #Hg := Hgc
  ihave Hp1 := Hphase1 $$ Hannot0 Hg Hbig
  ihave Hp1 := wpdStepsNStepFupdN _ _ $$ Hp1
  iapply step_fupdN_add.2
  iapply step_fupdN_wand $$ Hp1
  iintro H
  rw [show 1 + sst.sProc.length = sst.sProc.length + 1 by omega, AxTierA2.stepFupdNSucc]
  imod H with ⟨%na, %ea, %Hdomna, -, Hea, -⟩
  iapply (step_fupd_intro LawfulSet.empty_subset)
  inext
  have Hdomeq : (FiniteMap.dom_set na : GSet Geid) = LawfulSet.ofList sst.sProc := by
    rw [Hdomna, Hfmap]
    exact Hcov
  ihave Hconn := (ordEaTodoLOfEaLocalWf GD ea na sst.sProc Hndp Hdomeq.symm) $$ Hea
  icases Hconn with ⟨%Hdom_eq2, %Hea_lob2, Htodo⟩
  have Hdom_sub : (LawfulSet.ofList sst.sProc : GSet Geid) ⊆ FiniteMap.dom_set na := by
    rw [Hdomeq]
  ihave Hphase2 := (schedProcAdequatePol GD Hcons sst HrunSched Hfull Hdone Hpol na ea
    Hdom_eq2 Hdom_sub Hea_lob2 σ0) $$ Htodo Hob0
  iapply step_fupdN_wand $$ Hphase2
  iintro ⟨%σ, Hob, -⟩
  ihave HQ := (Hread σ) $$ Hob
  iexact HQ

end finalFixed

section finalWrapper
variable {GF : BundledGFunctors.{0,0,0}}

/-- The Prop-level wrapper: a pure consequence of the FINAL phase-2 state. -/
theorem tierAAdequacyFinalGmo [InvGpreS GF] [AxannotG GF] [Axpol]
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
    (HsPolGmo : ∀ e e', e' ∈ Axpol.sPol GD e → gmoLt GD.gdG e' e)
    (HlobpGmo : ∀ e e', e' ∈ Axpol.lobp GD e → gmoLt GD.gdG e' e)
    (Q : Prop)
    (Hread : ∀ nm σ, obStInterp0 nm GD σ (LawfulSet.ofList GD.gdG.gxGmo) ⊢ ⌜Q⌝) :
    Q := by
  obtain ⟨sst, HrunSched, Hproc, Hfull, Hdone, Hgatefree⟩ := schedGatefreeRun GD
  have Hcov : (unionList (harts.map fun i => eidsBefore GD i (AxOpsem.grow GD i).length) :
      GSet Geid) = LawfulSet.ofList sst.sProc := by
    rw [Hproc]
    exact eidsBeforeCov GD harts (schedHGwf GD Hcons) Hharts
  have Hread' : ∀ nm σ, obStInterp0 nm GD σ (LawfulSet.ofList sst.sProc) ⊢ ⌜Q⌝ := by
    intro nm σ
    rw [Hproc]
    exact Hread nm σ
  apply Iris.pure_soundness (PROP := IProp GF)
  refine step_fupdN_soundness_close (hlc := .hasNoLC)
    (1 + ((harts.map n).sum + (1 + sst.sProc.length))) 0 (fun Hinv => ?_)
  rw [show 1 + ((harts.map n).sum + (1 + sst.sProc.length)) =
      ((harts.map n).sum + (1 + sst.sProc.length)) + 1 by omega,
    AxTierA2.stepFupdNSucc]
  iintro _
  imod (annotInterpAlloc (GF := GF)) with ⟨%γ, Hannot0⟩
  imod HobAlloc with ⟨%nm, %σ0, Hob0, Hinit⟩
  ihave Hcore := (@tierAFinalCore GF .hasNoLC Hinv { axannotName := γ } _ GD N obSt0
    obStInterp0 init nm Hwf Hcons harts Hnd s0 sN n
    (fun j Hj => Hrun { axannotName := γ } nm j Hj) Hk0 Hend post
    (@Hwp Hinv { axannotName := γ } nm)
    sst HrunSched Hfull Hdone Hgatefree HsPolGmo HlobpGmo Hcov Q (Hread' nm) σ0)
    $$ Hannot0 Hob0 Hinit
  iapply (step_fupd_intro LawfulSet.empty_subset)
  inext
  iexact Hcore

end finalWrapper

/-! # 6. J2: THE LEDGER-EXTENDED INSTANCE AND ITS ADEQUACY -/

/-- The extended state interpretation: any base protocol beside the ledger; the ghost-name type
is a pair (the base names, the ledger's name). -/
def obStInterpL {GF : BundledGFunctors} [LedgerG GF] (OC : Int → Prop) (nh : Nat)
    {N0 obSt0 : Type} (base0 : N0 → Gdexec → obSt0 → GSet Geid → IProp GF)
    (nm : N0 × GName) (GD : Gdexec) (σ : obSt0) (s : GSet Geid) : IProp GF :=
  iprop(base0 nm.1 GD σ s ∗ AxTokLedgerWp.ledgerInv OC nh nm.2 GD s)

section ledgerAdeq
variable {GF : BundledGFunctors.{0,0,0}}

/-- §4's rules apply at the extended `axGA2` instance: its state interpretation IS
`base ∗ ledgerInv` (by conversion). -/
theorem axGA2LedgerObExt [AxannotGS GF] [LedgerG GF] (GD : Gdexec) (OC : Int → Prop) (nh : Nat)
    (N0 obSt0 : Type) (base0 : N0 → Gdexec → obSt0 → GSet Geid → IProp GF) (nm : N0 × GName) :
    ∀ (GD' : Gdexec) (σ : obSt0) (s : GSet Geid),
      @AxirisG.obStInterp GF (axGA2 GD (N0 × GName) obSt0 (obStInterpL OC nh base0) nm) GD' σ s ⊣⊢
        base0 nm.1 GD' σ s ∗ AxTokLedgerWp.ledgerInv OC nh nm.2 GD' s :=
  fun _ _ _ => .rfl

/-- THE J2 ADEQUACY: a completed run of per-hart WPds at the extended instance yields a LEGAL
LEDGER HISTORY over gmo. -/
theorem tierAAdequacyLedger [InvGpreS GF] [AxannotG GF] [LedgerG GF] [Axpol]
    (GD : Gdexec) (OC : Int → Prop) (nh : Nat)
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
          tierAWpd GD (N0 × GName) obSt0 (obStInterpL OC nh base0) nm (s0 i) .MaybeStuck i
            (fun s => iprop(⌜post i s⌝)))
    (HobAlloc : ⊢ |==> ∃ (nm : N0 × GName) (σ0 : obSt0),
      obStInterpL OC nh base0 nm GD σ0 ∅ ∗ [∗list] i ∈ harts, init nm i)
    (HsPolGmo : ∀ e e', e' ∈ Axpol.sPol GD e → gmoLt GD.gdG e' e)
    (HlobpGmo : ∀ e e', e' ∈ Axpol.lobp GD e → gmoLt GD.gdG e' e) :
    ∃ LH, ledgerHistOkList OC nh GD LH :=
  tierAAdequacyFinalGmo GD (N0 × GName) obSt0 (obStInterpL OC nh base0) init Hwf Hcons harts Hnd
    Hharts s0 sN n Hrun Hk0 Hend post Hwp HobAlloc HsPolGmo HlobpGmo _ (fun nm _σ => by
      unfold obStInterpL
      iintro ⟨-, Hl⟩
      ihave H := (ledgerInvFull OC nh nm.2 GD (schedHGwf GD Hcons)) $$ Hl
      iexact H)

/-- … hence an ownership timeline (`AxTokLedger.ledgerTimeline`). -/
theorem tierAAdequacyLedgerTl [InvGpreS GF] [AxannotG GF] [LedgerG GF] [Axpol]
    (GD : Gdexec) (OC : Int → Prop) (nh : Nat)
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
          tierAWpd GD (N0 × GName) obSt0 (obStInterpL OC nh base0) nm (s0 i) .MaybeStuck i
            (fun s => iprop(⌜post i s⌝)))
    (HobAlloc : ⊢ |==> ∃ (nm : N0 × GName) (σ0 : obSt0),
      obStInterpL OC nh base0 nm GD σ0 ∅ ∗ [∗list] i ∈ harts, init nm i)
    (HsPolGmo : ∀ e e', e' ∈ Axpol.sPol GD e → gmoLt GD.gdG e' e)
    (HlobpGmo : ∀ e e', e' ∈ Axpol.lobp GD e → gmoLt GD.gdG e' e) :
    ∃ own, gtlOk OC nh GD.gdG own := by
  obtain ⟨LH, HLH⟩ := tierAAdequacyLedger GD OC nh N0 obSt0 base0 init Hwf Hcons harts Hnd Hharts
    s0 sN n Hrun Hk0 Hend post Hwp HobAlloc HsPolGmo HlobpGmo
  exact ⟨_, ledgerTimelineList OC nh GD LH (schedHGwf GD Hcons) HLH⟩

end ledgerAdeq

/-! # 7. J3: `tlExtraction` and the violation-freedom theorem -/

/-- `ledgerVerified nh GD`: SOME choice of resources, policy, Own class `OC` (covering every plain
hart write), base protocol and initial resources, and per-hart runs + WPds AT THE
LEDGER-EXTENDED INSTANCE, satisfying `tierAAdequacyLedger`'s premises. -/
inductive ledgerVerified (nh : Nat) (GD : Gdexec) : Prop where
  | mk (GF : BundledGFunctors.{0,0,0}) [HannG : AxannotG GF] [HlG : LedgerG GF]
      [Hpre : InvGpreS GF] [pol : Axpol] (OC : Int → Prop)
      (N0 obSt0 : Type) (base0 : N0 → Gdexec → obSt0 → GSet Geid → IProp GF)
      (init : N0 × GName → Agent → IProp GF)
      (harts : List Agent) (s0 sN : Agent → Athread) (n : Agent → Nat)
      (post : Agent → Athread → Prop)
      (Hplain : ∀ w a v, w ∈ GD.gdG.gxGmo → tidHart nh (some w.1) →
        glblIs GD.gdG w lbPlain → gwritesByte GD.gdG w a v → OC a)
      (Hwf : axpolWf) (Hnd : harts.Nodup)
      (Hharts : ∀ e, e ∈ GD.gdG.gxGmo → e.1 ∈ harts)
      (Hrun : ∀ (_ : AxannotGS GF) (nm : N0 × GName) i, i ∈ harts →
        nsteps (tierAAstep GD nm i) (n i) (s0 i) (sN i))
      (Hk0 : ∀ i, i ∈ harts → (s0 i).atK = 0)
      (Hend : ∀ i, i ∈ harts → (sN i).atK = (AxOpsem.grow GD i).length)
      (Hwp : ∀ [InvGS_gen .hasNoLC GF] [AxannotGS GF] (nm : N0 × GName),
        ⊢ ([∗list] i ∈ harts, init nm i) -∗
          [∗list] i ∈ harts,
            tierAWpd GD (N0 × GName) obSt0 (obStInterpL OC nh base0) nm (s0 i) .MaybeStuck i
              (fun s => iprop(⌜post i s⌝)))
      (HobAlloc : ⊢ |==> ∃ (nm : N0 × GName) (σ0 : obSt0),
        obStInterpL OC nh base0 nm GD σ0 ∅ ∗ [∗list] i ∈ harts, init nm i)
      (HsPolGmo : ∀ e e', e' ∈ Axpol.sPol GD e → gmoLt GD.gdG e' e)
      (HlobpGmo : ∀ e e', e' ∈ Axpol.lobp GD e → gmoLt GD.gdG e' e)

/-- J3: AxViol's missing premise, for ledger-verified programs. -/
theorem tlExtractionLedger (nh : Nat) : tlExtraction nh (ledgerVerified nh) := by
  intro GD Hcons Hver
  refine ledgerVerified.casesOn (motive := fun _ => _) Hver ?_
  intro GF HannG HlG Hpre pol OC N0 obSt0 base0 init harts s0 sN n post Hplain Hwf Hnd Hharts
    Hrun Hk0 Hend Hwp HobAlloc Hs Hl
  obtain ⟨own, Htl⟩ := tierAAdequacyLedgerTl GD OC nh N0 obSt0 base0 init Hwf Hcons harts Hnd
    Hharts s0 sN n Hrun Hk0 Hend post Hwp HobAlloc Hs Hl
  exact ⟨OC, own, Htl, Hplain⟩

/-- J3: THE VIOLATION-FREEDOM THEOREM for ledger-verified programs. -/
theorem adequacyViolFreeLedger (nh : Nat) : adequacyViolFreeStmt nh (ledgerVerified nh) :=
  adequacyViolFreeOfTl nh _ (tlExtractionLedger nh)

/-! # 8. NON-VACUITY -/

/-- 8.1 THE NEGATIVE TWIN: no ledger-verified program has the plain-sd graph `mpPlain`. -/
theorem mpPlainNotLedgerVerified : ¬ ledgerVerified 2 mpPlain := fun Hver =>
  adequacyViolFreeLedger 2 mpPlain mpPlainCat Hver mpPlainViol

/-! ## 8.2 THE POSITIVE CERTIFICATE on `AxViol.mp` (phase 2) -/

/-- The mailbox condition: the release `(0,2)` validated, the acquire `(1,0)` not yet. -/
def mpCond (s : GSet Geid) : Bool :=
  decide (((0, 2) : Geid) ∈ s) && !decide (((1, 0) : Geid) ∈ s)

/-- The mailbox: between the release's and the acquire's validation, the two pending tokens
live in the state. -/
def baseMp {GF : BundledGFunctors} [LedgerG GF] {S : Type} (γL : GName) (_GD : Gdexec) (_σ : S)
    (s : GSet Geid) : IProp GF :=
  if mpCond s then iprop(tokPending γL 0 (0, 2) ∗ tokPending γL 1 (0, 2)) else iprop(True)

theorem mpGmo : AxViol.mp.gdG.gxGmo = [(0, 0), (0, 2), (1, 0), (1, 1)] := rfl

theorem mpCond0 : mpCond (LawfulSet.ofList (AxViol.mp.gdG.gxGmo.take 0)) = false := by
  decide +kernel
theorem mpCond1 : mpCond (LawfulSet.ofList (AxViol.mp.gdG.gxGmo.take 1)) = false := by
  decide +kernel
theorem mpCond2 : mpCond (LawfulSet.ofList (AxViol.mp.gdG.gxGmo.take 2)) = true := by
  decide +kernel
theorem mpCond3 : mpCond (LawfulSet.ofList (AxViol.mp.gdG.gxGmo.take 3)) = false := by
  decide +kernel
theorem mpCond4 : mpCond (LawfulSet.ofList (AxViol.mp.gdG.gxGmo.take 4)) = false := by
  decide +kernel

theorem ocMpIn (a : Int) : ocMp a → a ∈ ([0, 1] : List Int) := by
  rintro (rfl | rfl) <;> decide

theorem mpWf : gwf AxViol.mp.gdG := mpCat.1

section mpHelpers
variable {GF : BundledGFunctors} [LedgerG GF]

/-- Lean-only (Rocq `mp_cond_eval false`). -/
theorem AxTokLedgerWp.baseMpOff {S : Type} (γL : GName) (GD : Gdexec) (σ : S) (s : GSet Geid)
    (h : mpCond s = false) : baseMp (GF := GF) γL GD σ s = iprop(True) := by
  unfold baseMp
  rw [h]
  rfl

/-- Lean-only (Rocq `mp_cond_eval true`). -/
theorem AxTokLedgerWp.baseMpOn {S : Type} (γL : GName) (GD : Gdexec) (σ : S) (s : GSet Geid)
    (h : mpCond s = true) :
    baseMp (GF := GF) γL GD σ s = iprop(tokPending γL 0 (0, 2) ∗ tokPending γL 1 (0, 2)) := by
  unfold baseMp
  rw [h]
  rfl

/-- Lean-only (Rocq `Local Notation toks`). -/
abbrev AxTokLedgerWp.toks (γL : GName) (i : Agent) : IProp GF :=
  iprop(tokAt γL 0 i ∗ tokAt γL 1 i)

/-- Lean-only: the two-byte list `[0; 1]`. -/
theorem AxTokLedgerWp.bigSepLTwo (Φ : Int → IProp GF) :
    ([∗list] a ∈ ([0, 1] : List Int), Φ a) ⊣⊢ Φ 0 ∗ Φ 1 :=
  BigSepL.bigSepL_cons.trans (sep_congr .rfl BigSepL.bigSepL_singleton)

/-- Lean-only: the empty byte list. -/
theorem AxTokLedgerWp.bigSepLNil (Φ : Int → IProp GF) :
    ⊢ [∗list] a ∈ ([] : List Int), Φ a :=
  BigSepL.bigSepL_nil.2

end mpHelpers

/-- Lean-only: a gmo lookup of `mp` names the event's position. -/
theorem AxTokLedgerWp.mpIdx (n : Nat) (e : Geid) :
    AxViol.mp.gdG.gxGmo[n]? = some e → n = gpos AxViol.mp.gdG e :=
  fun h => (gposOfLookup _ n e mpWf.1 h).symm

/-- Lean-only: a list's set is below `Y` when each element is. -/
theorem AxTokLedgerWp.ofListSub (l : List Geid) (Y : GSet Geid) :
    (∀ x, x ∈ l → x ∈ Y) → (LawfulSet.ofList l : GSet Geid) ⊆ Y :=
  fun h x hx => h x ((elemOfListToSet (S := GSet Geid)).1 hx)

/-- Lean-only: permuted lists have the same set. -/
theorem AxTokLedgerWp.ofListPerm (l1 l2 : List Geid) :
    l1.Perm l2 → (LawfulSet.ofList l1 : GSet Geid) = LawfulSet.ofList l2 := by
  intro h
  rw [setEq]
  intro x
  rw [elemOfListToSet, elemOfListToSet]
  exact h.mem_iff

section mpCert
variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [axG : AxirisG GF] [Axpol]
  [LedgerG GF]

/-- (0,0) plain sd x: hart 0 holds both tokens; nothing moves. -/
theorem mpFe00 (γL : GName)
    (HobExt : ∀ (GD : Gdexec) (σ : AxirisG.obSt GF) (s : GSet Geid),
      AxirisG.obStInterp GD σ s ⊣⊢ baseMp γL GD σ s ∗ AxTokLedgerWp.ledgerInv ocMp 2 γL GD s) :
    ⊢ AxTokLedgerWp.toks (GF := GF) γL 0 -∗
      flowEqDyn AxViol.mp (0, 0) (LawfulSet.ofList (gmoPrefix AxViol.mp.gdG (0, 0))) ∅
        (AxTokLedgerWp.toks γL 0) := by
  iintro ⟨H0, H1⟩
  iapply flowEqLedgerJoint ocMp 2 γL (baseMp γL) HobExt AxViol.mp (0, 0) _ ∅ _ mpWf
    (by decide +kernel) (fun _ h => h)
  unfold ledgerJoint
  iintro %σ %n %L %Hn _ Ha _
  have Hn0 : n = 0 := (AxTokLedgerWp.mpIdx n _ Hn).trans (by decide +kernel)
  subst Hn0
  ihave Hh := (AxTokLedgerWp.bigSepLTwo (fun a => tokAt γL a ((0, 0) : Geid).1)).2 $$ [H0 H1]
  · isplitl [H0]
    · iexact H0
    · iexact H1
  ihave Hr := AxTokLedgerWp.bigSepLNil (fun a => tokAt γL a ((0, 0) : Geid).1)
  ihave Hq := AxTokLedgerWp.bigSepLNil (fun a => tokPending γL a ((fun _ => ((0, 2) : Geid)) a))
  imod ledgerActGen ocMp 2 AxViol.mp γL L (0, 0) [0, 1] [] [] (fun _ => (0, 2)) List.nodup_nil
    List.nodup_nil (fun _ h => nomatch h) (fun _ h => nomatch h)
    (fun a Ha _ _ => .inl (ocMpIn a Ha)) $$ Ha Hh Hr Hq with ⟨%L', Ha, %Hst, Hh, -, -⟩
  iapply fupd_mask_intro LawfulSet.empty_subset
  iintro Hclose
  inext
  imod Hclose
  imodintro
  iexists σ, L'
  rw [AxTokLedgerWp.baseMpOff γL AxViol.mp σ _ mpCond1]
  isplitr
  · itrivial
  isplitl [Ha]
  · iexact Ha
  isplitr
  · ipureintro
    exact Hst
  icases (AxTokLedgerWp.bigSepLTwo _).1 $$ Hh with ⟨H0, H1⟩
  isplitl [H0]
  · iexact H0
  · iexact H1

/-- (0,2) sd.rl y: RELEASE both tokens (the only `lbRelw` event); they are parked in the
mailbox. -/
theorem mpFe02 (γL : GName)
    (HobExt : ∀ (GD : Gdexec) (σ : AxirisG.obSt GF) (s : GSet Geid),
      AxirisG.obStInterp GD σ s ⊣⊢ baseMp γL GD σ s ∗ AxTokLedgerWp.ledgerInv ocMp 2 γL GD s) :
    ⊢ flowEqDyn AxViol.mp (0, 2) (LawfulSet.ofList (gmoPrefix AxViol.mp.gdG (0, 2)))
        ({[((0, 0) : Geid) := AxTokLedgerWp.toks (GF := GF) γL 0]} : Mea GF) iprop(True) := by
  iapply flowEqLedgerJoint ocMp 2 γL (baseMp γL) HobExt AxViol.mp (0, 2) _ _ _ mpWf
    (by decide +kernel) (fun _ h => h)
  unfold ledgerJoint
  iintro %σ %n %L %Hn _ Ha Hin
  have Hn1 : n = 1 := (AxTokLedgerWp.mpIdx n _ Hn).trans (by decide +kernel)
  subst Hn1
  ihave Hin := BigSepM.bigSepM_singleton.1 $$ Hin
  icases Hin with ⟨H0, H1⟩
  ihave Hr := (AxTokLedgerWp.bigSepLTwo (fun a => tokAt γL a ((0, 2) : Geid).1)).2 $$ [H0 H1]
  · isplitl [H0]
    · iexact H0
    · iexact H1
  ihave Hh := AxTokLedgerWp.bigSepLNil (fun a => tokAt γL a ((0, 2) : Geid).1)
  ihave Hq := AxTokLedgerWp.bigSepLNil (fun a => tokPending γL a ((fun _ => ((0, 2) : Geid)) a))
  imod ledgerActGen ocMp 2 AxViol.mp γL L (0, 2) [] [0, 1] [] (fun _ => (0, 2))
    (by decide) List.nodup_nil (fun _ _ => mpRel) (fun _ h => nomatch h)
    (fun a Ha _ _ => .inr (.inl (ocMpIn a Ha))) $$ Ha Hh Hr Hq with ⟨%L', Ha, %Hst, -, Hr, -⟩
  iapply fupd_mask_intro LawfulSet.empty_subset
  iintro Hclose
  inext
  imod Hclose
  imodintro
  iexists σ, L'
  rw [AxTokLedgerWp.baseMpOn γL AxViol.mp σ _ mpCond2]
  isplitl [Hr]
  · icases (AxTokLedgerWp.bigSepLTwo _).1 $$ Hr with ⟨P0, P1⟩
    isplitl [P0]
    · iexact P0
    · iexact P1
  isplitl [Ha]
  · iexact Ha
  isplitr
  · ipureintro
    exact Hst
  · itrivial

/-- (1,0) ld.aq y: ACQUIRE both tokens from the mailbox (`acqFrom`'s rf arm). -/
theorem mpFe10 (γL : GName)
    (HobExt : ∀ (GD : Gdexec) (σ : AxirisG.obSt GF) (s : GSet Geid),
      AxirisG.obStInterp GD σ s ⊣⊢ baseMp γL GD σ s ∗ AxTokLedgerWp.ledgerInv ocMp 2 γL GD s) :
    ⊢ flowEqDyn AxViol.mp (1, 0) (LawfulSet.ofList (gmoPrefix AxViol.mp.gdG (1, 0))) ∅
        (AxTokLedgerWp.toks (GF := GF) γL 1) := by
  iapply flowEqLedgerJoint ocMp 2 γL (baseMp γL) HobExt AxViol.mp (1, 0) _ ∅ _ mpWf
    (by decide +kernel) (fun _ h => h)
  unfold ledgerJoint
  iintro %σ %n %L %Hn
  have Hn2 : n = 2 := (AxTokLedgerWp.mpIdx n _ Hn).trans (by decide +kernel)
  subst Hn2
  rw [AxTokLedgerWp.baseMpOn γL AxViol.mp σ _ mpCond2]
  iintro ⟨P0, P1⟩ Ha _
  ihave Hq := (AxTokLedgerWp.bigSepLTwo
    (fun a => tokPending γL a ((fun _ => ((0, 2) : Geid)) a))).2 $$ [P0 P1]
  · isplitl [P0]
    · iexact P0
    · iexact P1
  ihave Hh := AxTokLedgerWp.bigSepLNil (fun a => tokAt γL a ((1, 0) : Geid).1)
  ihave Hr := AxTokLedgerWp.bigSepLNil (fun a => tokAt γL a ((1, 0) : Geid).1)
  imod ledgerActGen ocMp 2 AxViol.mp γL L (1, 0) [] [] [0, 1] (fun _ => (0, 2))
    List.nodup_nil (by decide) (fun _ h => nomatch h) (fun _ _ => mpAcq)
    (fun a Ha _ _ => .inr (.inr (ocMpIn a Ha))) $$ Ha Hh Hr Hq with ⟨%L', Ha, %Hst, -, -, Hq⟩
  iapply fupd_mask_intro LawfulSet.empty_subset
  iintro Hclose
  inext
  imod Hclose
  imodintro
  iexists σ, L'
  rw [AxTokLedgerWp.baseMpOff γL AxViol.mp σ _ mpCond3]
  isplitr
  · itrivial
  isplitl [Ha]
  · iexact Ha
  isplitr
  · ipureintro
    exact Hst
  icases (AxTokLedgerWp.bigSepLTwo _).1 $$ Hq with ⟨H0, H1⟩
  isplitl [H0]
  · iexact H0
  · iexact H1

/-- (1,1) ld x: hart 1 now holds x's token (the access check passes). -/
theorem mpFe11 (γL : GName)
    (HobExt : ∀ (GD : Gdexec) (σ : AxirisG.obSt GF) (s : GSet Geid),
      AxirisG.obStInterp GD σ s ⊣⊢ baseMp γL GD σ s ∗ AxTokLedgerWp.ledgerInv ocMp 2 γL GD s) :
    ⊢ flowEqDyn AxViol.mp (1, 1) (LawfulSet.ofList (gmoPrefix AxViol.mp.gdG (1, 1)))
        ({[((1, 0) : Geid) := AxTokLedgerWp.toks (GF := GF) γL 1]} : Mea GF)
        (AxTokLedgerWp.toks γL 1) := by
  iapply flowEqLedgerJoint ocMp 2 γL (baseMp γL) HobExt AxViol.mp (1, 1) _ _ _ mpWf
    (by decide +kernel) (fun _ h => h)
  unfold ledgerJoint
  iintro %σ %n %L %Hn _ Ha Hin
  have Hn3 : n = 3 := (AxTokLedgerWp.mpIdx n _ Hn).trans (by decide +kernel)
  subst Hn3
  ihave Hin := BigSepM.bigSepM_singleton.1 $$ Hin
  icases Hin with ⟨H0, H1⟩
  ihave Hh := (AxTokLedgerWp.bigSepLTwo (fun a => tokAt γL a ((1, 1) : Geid).1)).2 $$ [H0 H1]
  · isplitl [H0]
    · iexact H0
    · iexact H1
  ihave Hr := AxTokLedgerWp.bigSepLNil (fun a => tokAt γL a ((1, 1) : Geid).1)
  ihave Hq := AxTokLedgerWp.bigSepLNil (fun a => tokPending γL a ((fun _ => ((0, 2) : Geid)) a))
  imod ledgerActGen ocMp 2 AxViol.mp γL L (1, 1) [0, 1] [] [] (fun _ => (0, 2)) List.nodup_nil
    List.nodup_nil (fun _ h => nomatch h) (fun _ h => nomatch h)
    (fun a Ha _ _ => .inl (ocMpIn a Ha)) $$ Ha Hh Hr Hq with ⟨%L', Ha, %Hst, Hh, -, -⟩
  iapply fupd_mask_intro LawfulSet.empty_subset
  iintro Hclose
  inext
  imod Hclose
  imodintro
  iexists σ, L'
  rw [AxTokLedgerWp.baseMpOff γL AxViol.mp σ _ mpCond4]
  isplitr
  · itrivial
  isplitl [Ha]
  · iexact Ha
  isplitr
  · ipureintro
    exact Hst
  icases (AxTokLedgerWp.bigSepLTwo _).1 $$ Hh with ⟨H0, H1⟩
  isplitl [H0]
  · iexact H0
  · iexact H1

/-- THE COMPOSITION: phase 2 in gmo order, from the initial state to the full one; the read-back
gives the legal ledger history. -/
theorem mpPhase2 (γL : GName)
    (HobExt : ∀ (GD : Gdexec) (σ : AxirisG.obSt GF) (s : GSet Geid),
      AxirisG.obStInterp GD σ s ⊣⊢ baseMp γL GD σ s ∗ AxTokLedgerWp.ledgerInv ocMp 2 γL GD s)
    (σ0 : AxirisG.obSt GF) :
    ⊢ AxirisG.obStInterp AxViol.mp σ0 ∅ -∗ AxTokLedgerWp.toks (GF := GF) γL 0 -∗
      |={⊤}[∅]▷=>^[4] ⌜∃ LH, ledgerHistOkList ocMp 2 AxViol.mp LH⌝ := by
  have F0 := mpFe00 γL HobExt
  have F1 := mpFe02 γL HobExt
  have F2 := mpFe10 γL HobExt
  have F3 := mpFe11 γL HobExt
  unfold flowEqDyn at F0 F1 F2 F3
  have h0s : (LawfulSet.ofList (gmoPrefix AxViol.mp.gdG (0, 0)) : GSet Geid) ⊆ ∅ :=
    AxTokLedgerWp.ofListSub _ _ (by decide +kernel)
  have h0n : ((0, 0) : Geid) ∉ (∅ : GSet Geid) := notElemOfEmpty
  have h1s : (LawfulSet.ofList (gmoPrefix AxViol.mp.gdG (0, 2)) : GSet Geid) ⊆
      ({((0, 0) : Geid)} : GSet Geid) ∪ ∅ :=
    AxTokLedgerWp.ofListSub _ _ (by decide +kernel)
  have h1n : ((0, 2) : Geid) ∉ ({((0, 0) : Geid)} : GSet Geid) ∪ ∅ := by decide +kernel
  have h2s : (LawfulSet.ofList (gmoPrefix AxViol.mp.gdG (1, 0)) : GSet Geid) ⊆
      ({((0, 2) : Geid)} : GSet Geid) ∪ (({((0, 0) : Geid)} : GSet Geid) ∪ ∅) :=
    AxTokLedgerWp.ofListSub _ _ (by decide +kernel)
  have h2n : ((1, 0) : Geid) ∉
      ({((0, 2) : Geid)} : GSet Geid) ∪ (({((0, 0) : Geid)} : GSet Geid) ∪ ∅) := by
    decide +kernel
  have h3s : (LawfulSet.ofList (gmoPrefix AxViol.mp.gdG (1, 1)) : GSet Geid) ⊆
      ({((1, 0) : Geid)} : GSet Geid) ∪
        (({((0, 2) : Geid)} : GSet Geid) ∪ (({((0, 0) : Geid)} : GSet Geid) ∪ ∅)) :=
    AxTokLedgerWp.ofListSub _ _ (by decide +kernel)
  have h3n : ((1, 1) : Geid) ∉ ({((1, 0) : Geid)} : GSet Geid) ∪
      (({((0, 2) : Geid)} : GSet Geid) ∪ (({((0, 0) : Geid)} : GSet Geid) ∪ ∅)) := by
    decide +kernel
  have Hs4 : ({((1, 1) : Geid)} : GSet Geid) ∪ (({((1, 0) : Geid)} : GSet Geid) ∪
      (({((0, 2) : Geid)} : GSet Geid) ∪ (({((0, 0) : Geid)} : GSet Geid) ∪ ∅))) =
      LawfulSet.ofList AxViol.mp.gdG.gxGmo := by
    rw [← AxTokLedgerWp.ofListPerm [(1, 1), (1, 0), (0, 2), (0, 0)] _ (by decide +kernel),
      listToSetCons, listToSetCons, listToSetCons, listToSetCons, listToSetNil]
  have HF := ledgerInvFull (GF := GF) ocMp 2 γL AxViol.mp mpWf
  rw [← Hs4] at HF
  rw [AxTierA2.stepFupdNSucc, AxTierA2.stepFupdNSucc, AxTierA2.stepFupdNSucc,
    AxTierA2.stepFupdNSucc, AxTierA2.stepFupdNZero]
  iintro Hob Ht
  ihave G := F0 $$ Ht
  ihave Hemp : ([∗map] Rin ∈ (∅ : Mea GF), Rin) $$ []
  · iapply BigSepM.bigSepM_empty.2
    iempintro
  imod G $$ %σ0 %(∅ : GSet Geid) %h0s %h0n Hob Hemp with G0
  imodintro
  inext
  imod G0 with ⟨%σ1, Hob, R0⟩
  imodintro
  ihave R0m : ([∗map] Rin ∈ ({[((0, 0) : Geid) := AxTokLedgerWp.toks (GF := GF) γL 0]} : Mea GF),
    Rin) $$ [R0]
  · iapply BigSepM.bigSepM_singleton.2
    iexact R0
  ihave G := F1
  imod G $$ %σ1 %(({((0, 0) : Geid)} : GSet Geid) ∪ ∅) %h1s %h1n Hob R0m with G1
  imodintro
  inext
  imod G1 with ⟨%σ2, Hob, -⟩
  imodintro
  ihave Hemp : ([∗map] Rin ∈ (∅ : Mea GF), Rin) $$ []
  · iapply BigSepM.bigSepM_empty.2
    iempintro
  ihave G := F2
  imod G $$ %σ2 %(({((0, 2) : Geid)} : GSet Geid) ∪ (({((0, 0) : Geid)} : GSet Geid) ∪ ∅))
    %h2s %h2n Hob Hemp with G2
  imodintro
  inext
  imod G2 with ⟨%σ3, Hob, R2⟩
  imodintro
  ihave R2m : ([∗map] Rin ∈ ({[((1, 0) : Geid) := AxTokLedgerWp.toks (GF := GF) γL 1]} : Mea GF),
    Rin) $$ [R2]
  · iapply BigSepM.bigSepM_singleton.2
    iexact R2
  ihave G := F3
  imod G $$ %σ3 %(({((1, 0) : Geid)} : GSet Geid) ∪
      (({((0, 2) : Geid)} : GSet Geid) ∪ (({((0, 0) : Geid)} : GSet Geid) ∪ ∅)))
    %h3s %h3n Hob R2m with G3
  imodintro
  inext
  imod G3 with ⟨%σ4, Hob, -⟩
  imodintro
  ihave Hob := (HobExt _ _ _).1 $$ Hob
  icases Hob with ⟨-, Hl⟩
  ihave H := HF $$ Hl
  iexact H

end mpCert

/-! ## 8.3 The certificate at Prop level, through a concrete instance -/

/-- The concrete instance: trivial annotations/graph pin/local state, the mailbox beside the
ledger as the phase-2 state. -/
@[reducible] def mpAxirisG {GF : BundledGFunctors} [LedgerG GF] (γL : GName) : AxirisG GF where
  annotInterp := fun _ => iprop(True)
  gconstInterp := fun _ => iprop(True)
  obSt := Unit
  obStInterp := fun GD σ s => iprop(baseMp γL GD σ s ∗ AxTokLedgerWp.ledgerInv ocMp 2 γL GD s)
  logTsT := Unit
  localInterp := fun _ _ _ _ => iprop(True)

theorem mpAxirisGExt {GF : BundledGFunctors} [LedgerG GF] (γL : GName) :
    ∀ (GD : Gdexec) (σ : @AxirisG.obSt GF (mpAxirisG γL)) (s : GSet Geid),
      @AxirisG.obStInterp GF (mpAxirisG γL) GD σ s ⊣⊢
        baseMp γL GD σ s ∗ AxTokLedgerWp.ledgerInv ocMp 2 γL GD s :=
  fun _ _ _ => .rfl

/-- The full gmo-prefix handout (what the ledger-aware rules require). -/
@[reducible] def mpPol : Axpol where
  sPol := fun GD e => LawfulSet.ofList (gmoPrefix GD.gdG e)
  lobp := fun _ _ => ∅

theorem mpPhase2Sound {GF : BundledGFunctors} [InvGpreS GF] [LedgerG GF] :
    ∃ LH, ledgerHistOkList ocMp 2 AxViol.mp LH := by
  apply Iris.pure_soundness (PROP := IProp GF)
  refine step_fupdN_soundness_close (hlc := .hasNoLC) 4 0 (fun Hinv => ?_)
  rw [AxTierA2.stepFupdNSucc]
  iintro _
  have HA := ledgerAlloc (GF := GF) lMp0
  unfold lMp0 at HA
  imod HA with ⟨%γL, Ha, Hf⟩
  have Hnone : get? ({[0 := Holder.held 0]} : Ledger) 1 = none := by decide +kernel
  icases (BigSepM.bigSepM_insert (Φ := fun a h => tokFrag (GF := GF) γL a h)
    (x := Holder.held 0) Hnone).1 $$ Hf
    with ⟨H1, Hf⟩
  ihave H0 := BigSepM.bigSepM_singleton.1 $$ Hf
  letI : Axpol := mpPol
  have Hph := mpPhase2 (hlc := .hasNoLC) (GF := GF) (axG := mpAxirisG γL) γL
    (mpAxirisGExt γL) ()
  rw [← AxTierA2.stepFupdNSucc]
  iapply Hph $$ [Ha] [H0 H1]
  · iapply (mpAxirisGExt γL AxViol.mp () ∅).2
    rw [AxTokLedgerWp.baseMpOff γL AxViol.mp () ∅ (by decide +kernel)]
    isplitr
    · itrivial
    · iapply ledgerInvInit ocMp 2 γL AxViol.mp
      iexact Ha
  · rw [show AxTokLedgerWp.toks (GF := GF) γL 0 =
        iprop(tokFrag γL 0 (.held 0) ∗ tokFrag γL 1 (.held 0)) from rfl]
    isplitl [H0]
    · iexact H0
    · iexact H1

/-! The concrete functor list (Rocq `mpΣ := #[invΣ; ledgerΣ]`; header deviation 6). -/

section mpGFSec
open Iris Iris.BI Iris.Std Std MachCSL COFE

def mpGF : BundledGFunctors :=
  BundledGFunctors.default
  |>.set 0 ⟨InvMapF, inferInstance⟩
  |>.set 1 ⟨constOF CoPsetDisjL, inferInstance⟩
  |>.set 2 ⟨constOF (DisjointLeibnizSet PosSet), inferInstance⟩
  |>.set 3 ⟨Auth.AuthURF (constOF Credit), inferInstance⟩
  |>.set 4 ⟨constOF (HeapView Int (Agree (DiscreteO Holder)) (GMapF Int)), inferInstance⟩

instance AxTokLedgerWp.mpGFInvMap : ElemG mpGF InvMapF := ⟨0, rfl⟩
instance AxTokLedgerWp.mpGFEnabled : ElemG mpGF (constOF CoPsetDisjL) := ⟨1, rfl⟩
instance AxTokLedgerWp.mpGFDisabled : ElemG mpGF (constOF (DisjointLeibnizSet PosSet)) := ⟨2, rfl⟩
instance AxTokLedgerWp.mpGFCredit : ElemG mpGF (Auth.AuthURF (constOF Credit)) := ⟨3, rfl⟩
instance AxTokLedgerWp.mpGFInvGpreS : InvGpreS mpGF :=
  ⟨⟨inferInstance, inferInstance, inferInstance⟩, ⟨inferInstance⟩⟩
instance AxTokLedgerWp.mpGFLedgerG : LedgerG mpGF := { ledgerMapG := ⟨⟨4, rfl⟩⟩ }

end mpGFSec

theorem mpPhase2Closed : ∃ LH, ledgerHistOkList ocMp 2 AxViol.mp LH :=
  mpPhase2Sound (GF := mpGF)

end Weak
