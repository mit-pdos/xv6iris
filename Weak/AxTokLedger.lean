/-
Weak: **K1 job J1 — HART-INDEXED TOKENS + THE IN-FLIGHT LEDGER** (LB/AxSL): the pure ledger
(`Holder`, `ledgerMove`, `AxTokLedger.ledgerStep`, `ledgerHistOk(List)`), its composition and
inversion lemmas; THE TIMELINE THEOREM `ledgerTimeline` (a legal ledger history resolves into an
`AxViol.gtlOk` ownership timeline); the ghost (`LedgerG`: `ledgerAuth`, exclusive fragments
`tokFrag`/`tokAt`/`tokPending`) with its three disciplined rules `tokRelease` (the ONLY rule that
takes a token from a hart; needs a release-class write) / `tokAcquire` / `tokPullback`; the
hart-indexed read/write wrappers over `AxToken.ownedReadRule` and `AxProtBytes.wp*OwnedTokn`; and
the vacuity certificates on `AxViol.mp` and its plain twin `mpPlain`.

Rocq: `iris/AxTokLedger.v` @ xxvzwolszwmp.

## The Rocq header, in substance

`AxViol.ownedNoViolationCat` refutes the SC-robustness violation from an ownership timeline
(`gtlOk`): (access) a hart access to an Own-class byte at gmo position `k` happens while
`own a k = some hart`; (drop) a hart loses a token only at one of ITS OWN `WCrel` writes.  The
existing protocol never inspects a store's class, so this file adds the ghost layer that makes the
timeline extractable: tokens indexed by the HART holding them, and the only rule that takes a token
away from a hart is `tokRelease`, whose side condition is `glblIs G w lbRelw`.  §1 the pure ledger
(`Holder := held i | pending w`, a ledger a map `Int → Holder`), §2 the timeline (`ledgerOwn`
resolves a pending entry to the first later holder, or to the releasing hart), §3 the ghost, §4 the
hart-indexed read/write rules (thin wrappers handing the tokens back), §5 the certificates on `mp`
(`sd x; fence rw,w; sd.rl y ‖ ld.aq y; ld x`): a concrete ledger history, the timeline and the
non-violation FROM THE LEDGER, the ghost hand-off of `x` from hart 0 to hart 1; and the negative
twin (plain `sd` instead of `sd.rl`): cat-consistent, a genuine violation, and NO ledger history
at all.  Nothing threads the ledger through `wpd`/adequacy (J2).

**Fetches (Stage C).** The ledger is indexed by gmo position, and gmo holds memory events only.
Neither `AxViol.mp` nor `mpPlain` has a fetch row (no 4-byte text read; checked), so the Stage C §D
"drop the fetch row items and re-index" step is vacuous here: the Rocq ledger history `LH_mp`
(5 ledgers for a 4-event gmo) is kept verbatim, and every concrete ledger fact is recomputed by
`decide +kernel`.

## Deviations from Rocq

1. NAMES: camelCase (map below).  The duplicated Rocq name `ledger_step` (also in `AxEpiLedger`) is
   FILE-QUALIFIED `AxTokLedger.ledgerStep`; Lean-only helpers are file-qualified `AxTokLedger.*`.
   Constructors are lowercase (`Holder.held`/`Holder.pending`; `ledgerMove.lmSame`/`lmRelease`/
   `lmAcquire`).
2. VOCABULARY: `gmap Z holder` ↦ `Ledger := GMapF Int Holder`; `L !! a` ↦ `get? L a`;
   `<[a := h]> L` ↦ `insert L a h`; `LH !! k` (lists) ↦ `LH[k]?`; `S k` ↦ `k + 1`;
   `default ∅ (last LH)` ↦ `LH.getLast?.getD ∅`; `agent` ↦ `Agent` (= `Nat`); `gd_g` ↦ `.gdG`;
   `gx_gmo` ↦ `.gxGmo`; `gpo` ↦ `WeakRvwmoGraph.gpo`; `.*1` ↦ `List.map Prod.fst`; `dom S` ↦
   `FiniteMap.dom_set S`; `Z.of_nat j` ↦ `(j : Int)`; `WeakLitmus.b1` ↦ `b1`; `vm_compute` ↦
   `decide +kernel`.
3. THE CAMERA: Rocq's `gmap_viewR Z (agreeR (leibnizO holder))` is exactly iris-lean's
   `ghost_map` camera (`HeapView` over `Agree (DiscreteO Holder)`), so `LedgerG GF` bundles
   `GhostMapG GF Int Holder (GMapF Int)` and the ghost lemmas are the `ghost_map_*` lemmas
   (`ledgerAlloc` = `ghost_map_alloc`, `ledgerAgree` = `ghost_map_lookup`, `tokFragExcl` via
   `ghost_map_elem_ne`, `ledgerUpdate` = `ghost_map_update`).  Consequently the camera-internal
   `to_ledgerR` / `to_agree_holder_valid` have no Lean counterpart (not used by any downstream
   Rocq file), and `ledgerΣ`/`subG_ledgerG` are subsumed by `BundledGFunctors` synthesis.
   An adequacy file using the ledger must ALLOCATE it (`ledgerAlloc`).
4. STATEMENT SHAPES (as `AxProtBytes` deviation 4): Iris lemmas are wand chains `⊢ A -∗ B -∗ C`.
5. CONTEXTS (as `AxProtBytes` deviation 2): §4 `rules_i`'s section context (`γ γl Hob_eq GD Hcons
   rdatn HrdatnSpec`) becomes explicit arguments in that order, each lemma taking the ones it uses
   (`wpWriteOwnedToknI`: `Proof using Hob_eq Hpol`, no `Hcons`/`rdatn`); `[Axpol]` is an instance
   binder; `invGS_gen HasNoLc Σ` ↦ `[InvGS_gen hlc GF]` for any `hlc`.
6. `mpPlainWritesOC` (Rocq `mp_plain_writes_OC`, about `mp`): instead of the Rocq per-event
   `vm_compute` enumeration, one kernel-decided fact over all store labels of `mp`'s program plus
   the Lean-only `AxTokLedger.gxLblMem` (a label of an event sits in a program row).
   `mpPlainNoRel` follows `AxViol.viol2NoRel` (via `axViolGlblIsProg`).

**Rocq → Lean name map.**  `holder` `Holder` (`Held` `.held`, `Pending` `.pending`),
`holder_eq_dec` (derived `DecidableEq`), `holder_inhabited` `instInhabitedHolder`, `ledger`
`Ledger`, `acq_from` `acqFrom`, `ledger_move` `ledgerMove` (`lm_same` `lmSame`, `lm_release`
`lmRelease`, `lm_acquire` `lmAcquire`), `ledger_moves` `ledgerMoves`, `ledger_access_ok`
`ledgerAccessOk`, `ledger_step` `AxTokLedger.ledgerStep`, `ledger_hist_ok` `ledgerHistOk`,
`ledger_hist_ok_list` `ledgerHistOkList`, `lh_fun` `lhFun`, `ledger_hist_ok_of_list`
`ledgerHistOkOfList`, `ledger_moves_refl` `ledgerMovesRefl`, `ledger_moves_release`
`ledgerMovesRelease`, `ledger_moves_acquire` `ledgerMovesAcquire`, `ledger_step_of_moves`
`ledgerStepOfMoves`, `ledger_move_held_inv` `ledgerMoveHeldInv`, `ledger_move_pending_inv`
`ledgerMovePendingInv`, `ledger_move_none` `ledgerMoveNone`, `ledger_move_held_held`
`ledgerMoveHeldHeld`, `ledger_move_held_pending` `ledgerMoveHeldPending`, `ledger_move_plain_held`
`ledgerMovePlainHeld`, `ledger_step_plain_keeps` `ledgerStepPlainKeeps`, `first_held` `firstHeld`,
`ledger_own` `ledgerOwn`, `ledger_own_held` `ledgerOwnHeld`, `ledger_own_none` `ledgerOwnNone`,
`ledger_own_pending_step` `ledgerOwnPendingStep`, `ledger_own_pending_end` `ledgerOwnPendingEnd`,
`ledger_own_pending_acq` `ledgerOwnPendingAcq`, `ledger_timeline` `ledgerTimeline`,
`ledger_timeline_list` `ledgerTimelineList`, `ledgerG` `LedgerG`, `ledger_auth` `ledgerAuth`,
`tok_frag` `tokFrag`, `tok_at` `tokAt`, `tok_pending` `tokPending`, `ledger_auth_timeless`
`ledgerAuthTimeless`, `tok_frag_timeless` `tokFragTimeless`, `tok_at_timeless` `tokAtTimeless`,
`tok_pending_timeless` `tokPendingTimeless`, `ledger_alloc` `ledgerAlloc`, `ledger_agree`
`ledgerAgree`, `tok_at_agree` `tokAtAgree`, `tok_pending_agree` `tokPendingAgree`, `tok_frag_excl`
`tokFragExcl`, `tok_at_excl` `tokAtExcl`, `ledger_update` `ledgerUpdate`, `tok_release`
`tokRelease`, `tok_acquire` `tokAcquire`, `tok_pullback` `tokPullback`, `lh_cur` `lhCur`,
`ledger_interp` `ledgerInterp`, `lh_cur_app` `lhCurApp`, `ledger_interp_append`
`ledgerInterpAppend`, `ledger_interp_cur` `ledgerInterpCur`, `owned_read_rule_i`
`ownedReadRuleI`, `owned_read_rule_acq` `ownedReadRuleAcq`, `wp_write_owned_tokn_i`
`wpWriteOwnedToknI`, `wp_read_owned_tokn_i` `wpReadOwnedToknI`, `OC_mp` `ocMp`, `L_mp0/1/2`
`lMp0/1/2`, `LH_mp` `lhMp`, `mp_rel` `mpRel`, `mp_rf_y` `mpRfY`, `mp_acq` `mpAcq`,
`mp_ledger_hist` `mpLedgerHist`, `mp_tl_ledger` `mpTlLedger`, `mp_plain_writes_OC`
`mpPlainWritesOC`, `mp_no_violation_ledger` `mpNoViolationLedger`, `mp_ghost_handoff`
`mpGhostHandoff`, `mp_plain` `mpPlain`, `mp_plain_cat` `mpPlainCat`, `mp_plain_no_rel`
`mpPlainNoRel`, `mp_plain_viol` `mpPlainViol`, `mp_plain_step_keeps` `mpPlainStepKeeps`,
`mp_plain_no_ledger_hist` `mpPlainNoLedgerHist`, `mp_plain_no_ledger_hist_list`
`mpPlainNoLedgerHistList`.

**Not ported:** `to_ledgerR`, `to_agree_holder_valid`, `ledgerΣ`, `subG_ledgerG` (deviation 3);
the `Print Assumptions` audits.
-/
import Weak.AxProtBytes
import Weak.AxViol

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std Iris.Std.PartialMap MachCSL MachCSL.Stdpp
open Lbl

/-! # 1. THE PURE LEDGER -/

/-- Who holds byte `a`'s token: a hart, or nobody yet — the token is IN FLIGHT since the
release-class write `w`. -/
inductive Holder where
  | held (i : Agent)
  | pending (w : Geid)
  deriving DecidableEq, Repr

instance instInhabitedHolder : Inhabited Holder := ⟨.held 0⟩

abbrev Ledger : Type := GMapF Int Holder

/-- The edges along which a pending token may be acquired: rf (on any byte) from the releasing
write, ob from it, or the releasing hart pulling its own token back. -/
def acqFrom (GD : Gdexec) (w r : Geid) : Prop :=
  (∃ b, grfAt GD.gdG b w r) ∨ gobCat GD w r ∨ r.1 = w.1

/-- THE THREE PER-BYTE TRANSITIONS event `e` may perform.  Release is the ONLY place the store
class enters. -/
inductive ledgerMove (GD : Gdexec) (e : Geid) : Option Holder → Option Holder → Prop where
  | lmSame (h : Option Holder) : ledgerMove GD e h h
  | lmRelease :
      glblIs GD.gdG e lbRelw →
      ledgerMove GD e (some (.held e.1)) (some (.pending e))
  | lmAcquire (w : Geid) :
      acqFrom GD w e →
      ledgerMove GD e (some (.pending w)) (some (.held e.1))

def ledgerMoves (GD : Gdexec) (e : Geid) (L L' : Ledger) : Prop :=
  ∀ a, ledgerMove GD e (get? L a) (get? L' a)

/-- An access by `e` to a byte is legal when `e`'s hart holds the token, or the token is pending
and `e` acquires it at this very step. -/
def ledgerAccessOk (e : Geid) (h h' : Option Holder) : Prop :=
  h = some (.held e.1) ∨ ∃ w, h = some (.pending w) ∧ h' = some (.held e.1)

def AxTokLedger.ledgerStep (OC : Int → Prop) (nh : Nat) (GD : Gdexec) (e : Geid)
    (L L' : Ledger) : Prop :=
  ledgerMoves GD e L L' ∧
  (∀ a, OC a → tidHart nh (some e.1) → gaccesses GD.gdG e a →
     ledgerAccessOk e (get? L a) (get? L' a))

/-- A ledger per gmo position: `LH k` is the ledger just BEFORE the gmo-`k`th event is validated;
constant past the end. -/
def ledgerHistOk (OC : Int → Prop) (nh : Nat) (GD : Gdexec) (LH : Nat → Ledger) : Prop :=
  ∀ k, match GD.gdG.gxGmo[k]? with
       | some e => AxTokLedger.ledgerStep OC nh GD e (LH k) (LH (k + 1))
       | none => LH (k + 1) = LH k

/-- The list form J2 maintains: one ledger appended per phase-2 step. -/
def ledgerHistOkList (OC : Int → Prop) (nh : Nat) (GD : Gdexec) (LH : List Ledger) : Prop :=
  LH.length = GD.gdG.gxGmo.length + 1 ∧
  ∀ k e L L', GD.gdG.gxGmo[k]? = some e → LH[k]? = some L → LH[k + 1]? = some L' →
    AxTokLedger.ledgerStep OC nh GD e L L'

def lhFun (LH : List Ledger) (k : Nat) : Ledger :=
  match LH[k]? with
  | some L => L
  | none => LH.getLast?.getD ∅

theorem ledgerHistOkOfList (OC : Int → Prop) (nh : Nat) (GD : Gdexec) (LH : List Ledger) :
    ledgerHistOkList OC nh GD LH → ledgerHistOk OC nh GD (lhFun LH) := by
  rintro ⟨hlen, hstep⟩ k
  cases hgk : GD.gdG.gxGmo[k]? with
  | some e =>
    have hlt : k < GD.gdG.gxGmo.length := (List.getElem?_eq_some_iff.1 hgk).1
    have hL : LH[k]? = some LH[k] := List.getElem?_eq_getElem (by omega)
    have hL' : LH[k + 1]? = some LH[k + 1] := List.getElem?_eq_getElem (by omega)
    show AxTokLedger.ledgerStep OC nh GD e (lhFun LH k) (lhFun LH (k + 1))
    simp only [lhFun, hL, hL']
    exact hstep k e _ _ hgk hL hL'
  | none =>
    have hge : GD.gdG.gxGmo.length ≤ k := List.getElem?_eq_none_iff.1 hgk
    have hSk : LH[k + 1]? = none := List.getElem?_eq_none_iff.2 (by omega)
    show lhFun LH (k + 1) = lhFun LH k
    simp only [lhFun, hSk]
    by_cases hk : k = GD.gdG.gxGmo.length
    · subst hk
      rw [List.getLast?_eq_getElem?, show LH.length - 1 = GD.gdG.gxGmo.length by omega]
      rcases LH[GD.gdG.gxGmo.length]? with _ | L <;> rfl
    · have hk' : LH[k]? = none := List.getElem?_eq_none_iff.2 (by omega)
      rw [hk']

/-! ## 1.1 Composition -/

theorem ledgerMovesRefl (GD : Gdexec) (e : Geid) (L : Ledger) : ledgerMoves GD e L L :=
  fun a => .lmSame _

theorem ledgerMovesRelease (GD : Gdexec) (e : Geid) (L L' : Ledger) (a : Int) :
    ledgerMoves GD e L L' → get? L a = some (.held e.1) → get? L' a = some (.held e.1) →
    glblIs GD.gdG e lbRelw →
    ledgerMoves GD e L (insert L' a (.pending e)) := by
  intro hm ha _ hrel b
  by_cases hb : a = b
  · subst hb
    rw [get?_insert_eq rfl, ha]
    exact .lmRelease hrel
  · rw [get?_insert_ne hb]
    exact hm b

theorem ledgerMovesAcquire (GD : Gdexec) (e : Geid) (L L' : Ledger) (a : Int) (w : Geid) :
    ledgerMoves GD e L L' → get? L a = some (.pending w) → get? L' a = some (.pending w) →
    acqFrom GD w e →
    ledgerMoves GD e L (insert L' a (.held e.1)) := by
  intro hm ha _ hacq b
  by_cases hb : a = b
  · subst hb
    rw [get?_insert_eq rfl, ha]
    exact .lmAcquire w hacq
  · rw [get?_insert_ne hb]
    exact hm b

theorem ledgerStepOfMoves (OC : Int → Prop) (nh : Nat) (GD : Gdexec) (e : Geid) (L L' : Ledger) :
    ledgerMoves GD e L L' →
    (∀ a, OC a → tidHart nh (some e.1) → gaccesses GD.gdG e a →
       ledgerAccessOk e (get? L a) (get? L' a)) →
    AxTokLedger.ledgerStep OC nh GD e L L' :=
  fun h1 h2 => ⟨h1, h2⟩

/-! ## 1.2 Inversion -/

theorem ledgerMoveHeldInv (GD : Gdexec) (e : Geid) (i : Agent) (h' : Option Holder) :
    ledgerMove GD e (some (.held i)) h' →
    h' = some (.held i) ∨ (h' = some (.pending e) ∧ e.1 = i ∧ glblIs GD.gdG e lbRelw) := by
  intro hm
  cases hm with
  | lmSame => exact .inl rfl
  | lmRelease hrel => exact .inr ⟨rfl, rfl, hrel⟩

theorem ledgerMovePendingInv (GD : Gdexec) (e w : Geid) (h' : Option Holder) :
    ledgerMove GD e (some (.pending w)) h' →
    h' = some (.pending w) ∨ (h' = some (.held e.1) ∧ acqFrom GD w e) := by
  intro hm
  cases hm with
  | lmSame => exact .inl rfl
  | lmAcquire _ hacq => exact .inr ⟨rfl, hacq⟩

theorem ledgerMoveNone (GD : Gdexec) (e : Geid) (h' : Option Holder) :
    ledgerMove GD e none h' → h' = none := by
  intro hm
  cases hm
  rfl

/-- A Held → Held CHANGE is impossible at any event. -/
theorem ledgerMoveHeldHeld (GD : Gdexec) (e : Geid) (i j : Agent) :
    ledgerMove GD e (some (.held i)) (some (.held j)) → i = j := by
  intro hm
  cases hm
  rfl

/-- Held → Pending forces: the pending write IS this event, the holder's own, release-class. -/
theorem ledgerMoveHeldPending (GD : Gdexec) (e : Geid) (i : Agent) (w : Geid) :
    ledgerMove GD e (some (.held i)) (some (.pending w)) →
    w = e ∧ e.1 = i ∧ glblIs GD.gdG e lbRelw := by
  intro hm
  cases hm with
  | lmRelease hrel => exact ⟨rfl, rfl, hrel⟩

/-- At a NON-release-class event a Held entry cannot change at all. -/
theorem ledgerMovePlainHeld (GD : Gdexec) (e : Geid) (i : Agent) (h' : Option Holder) :
    ¬ glblIs GD.gdG e lbRelw →
    ledgerMove GD e (some (.held i)) h' → h' = some (.held i) := by
  intro hnrel hm
  rcases ledgerMoveHeldInv GD e i h' hm with h | ⟨_, _, hrel⟩
  · exact h
  · exact absurd hrel hnrel

theorem ledgerStepPlainKeeps (OC : Int → Prop) (nh : Nat) (GD : Gdexec) (e : Geid)
    (L L' : Ledger) (a : Int) (i : Agent) :
    ¬ glblIs GD.gdG e lbRelw →
    AxTokLedger.ledgerStep OC nh GD e L L' → get? L a = some (.held i) →
    get? L' a = some (.held i) := by
  intro hnrel ⟨hm, _⟩ ha
  have h := hm a
  rw [ha] at h
  exact ledgerMovePlainHeld GD e i _ hnrel h

/-! # 2. THE TIMELINE -/

/-- The first hart holding `a` at a position in `[m, m + fuel)`. -/
def firstHeld (LH : Nat → Ledger) (a : Int) (m fuel : Nat) : Option Agent :=
  match fuel with
  | 0 => none
  | f + 1 =>
    match get? (LH m) a with
    | some (.held i) => some i
    | _ => firstHeld LH a (m + 1) f

/-- The holder of `a` just before gmo position `k`, a pending entry resolved to its EVENTUAL
holder (searched up to position `n`), or to the releasing hart if never acquired. -/
def ledgerOwn (LH : Nat → Ledger) (n : Nat) (a : Int) (k : Nat) : Option Agent :=
  match get? (LH k) a with
  | some (.held i) => some i
  | some (.pending w) =>
    match firstHeld LH a (k + 1) (n - k) with
    | some i => some i
    | none => some w.1
  | none => none

theorem ledgerOwnHeld (LH : Nat → Ledger) (n : Nat) (a : Int) (k : Nat) (i : Agent) :
    get? (LH k) a = some (.held i) → ledgerOwn LH n a k = some i := by
  intro h
  simp only [ledgerOwn, h]

theorem ledgerOwnNone (LH : Nat → Ledger) (n : Nat) (a : Int) (k : Nat) :
    get? (LH k) a = none → ledgerOwn LH n a k = none := by
  intro h
  simp only [ledgerOwn, h]

/-- Two consecutive Pending entries resolve alike. -/
theorem ledgerOwnPendingStep (LH : Nat → Ledger) (n : Nat) (a : Int) (k : Nat) (w : Geid) :
    get? (LH k) a = some (.pending w) → get? (LH (k + 1)) a = some (.pending w) → k < n →
    ledgerOwn LH n a (k + 1) = ledgerOwn LH n a k := by
  intro hk hSk hlt
  have hn : n - k = (n - (k + 1)) + 1 := by omega
  simp only [ledgerOwn, hk, hSk, hn, firstHeld]

/-- A Pending entry at or past the end resolves to the releasing hart. -/
theorem ledgerOwnPendingEnd (LH : Nat → Ledger) (n : Nat) (a : Int) (k : Nat) (w : Geid) :
    get? (LH k) a = some (.pending w) → n ≤ k → ledgerOwn LH n a k = some w.1 := by
  intro hk hle
  have hn : n - k = 0 := by omega
  simp only [ledgerOwn, hk, hn, firstHeld]

/-- A Pending entry acquired at the very next position resolves to the acquirer. -/
theorem ledgerOwnPendingAcq (LH : Nat → Ledger) (n : Nat) (a : Int) (k : Nat) (w : Geid)
    (j : Agent) :
    get? (LH k) a = some (.pending w) → get? (LH (k + 1)) a = some (.held j) → k < n →
    ledgerOwn LH n a k = some j := by
  intro hk hSk hlt
  have hn : n - k = (n - (k + 1)) + 1 := by omega
  simp only [ledgerOwn, hk, hSk, hn, firstHeld]

/-- THE TIMELINE THEOREM. -/
theorem ledgerTimeline (OC : Int → Prop) (nh : Nat) (GD : Gdexec) (LH : Nat → Ledger) :
    gwf GD.gdG → ledgerHistOk OC nh GD LH →
    gtlOk OC nh GD.gdG (ledgerOwn LH GD.gdG.gxGmo.length) := by
  rintro ⟨hnd, -⟩ hok
  refine ⟨?_, ?_⟩
  · -- (access)
    intro e a hhart he hoc hacc
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.1 he
    rw [gposOfLookup _ _ _ hnd hk]
    have hok' := hok k
    simp only [hk] at hok'
    obtain ⟨-, hacok⟩ := hok'
    rcases hacok a hoc hhart hacc with hh | ⟨w, hh, hh'⟩
    · exact ledgerOwnHeld _ _ _ _ _ hh
    · exact ledgerOwnPendingAcq _ _ _ _ w _ hh hh' (List.getElem?_eq_some_iff.1 hk).1
  · -- (drop)
    intro a k i _ hk hSk
    cases hka : get? (LH k) a with
    | none =>
      rw [ledgerOwnNone _ _ _ _ hka] at hk
      cases hk
    | some h =>
      cases h with
      | held j =>
        rw [ledgerOwnHeld _ _ _ _ _ hka] at hk
        cases hk
        cases hgk : GD.gdG.gxGmo[k]? with
        | some e =>
          have hok' := hok k
          simp only [hgk] at hok'
          have hm := hok'.1 a
          rw [hka] at hm
          rcases ledgerMoveHeldInv _ _ _ _ hm with hsame | ⟨_, he1, hrel⟩
          · exact absurd (ledgerOwnHeld _ _ _ _ _ hsame) hSk
          · exact ⟨e, rfl, he1, hrel⟩
        | none =>
          have hok' := hok k
          simp only [hgk] at hok'
          exact absurd (ledgerOwnHeld _ _ _ _ _ (by rw [hok']; exact hka)) hSk
      | pending w =>
        cases hgk : GD.gdG.gxGmo[k]? with
        | some e =>
          have hlt : k < GD.gdG.gxGmo.length := (List.getElem?_eq_some_iff.1 hgk).1
          have hok' := hok k
          simp only [hgk] at hok'
          have hm := hok'.1 a
          rw [hka] at hm
          rcases ledgerMovePendingInv _ _ _ _ hm with hsame | ⟨hheld, -⟩
          · exact absurd ((ledgerOwnPendingStep _ _ _ _ w hka hsame hlt).trans hk) hSk
          · rw [ledgerOwnPendingAcq _ _ _ _ _ _ hka hheld hlt] at hk
            exfalso
            apply hSk
            rw [← hk]
            exact ledgerOwnHeld _ _ _ _ _ hheld
        | none =>
          have hge : GD.gdG.gxGmo.length ≤ k := List.getElem?_eq_none_iff.1 hgk
          have hok' := hok k
          simp only [hgk] at hok'
          exfalso
          apply hSk
          rw [← hk, ledgerOwnPendingEnd _ _ _ _ _ hka hge]
          exact ledgerOwnPendingEnd _ _ _ _ _ (by rw [hok']; exact hka) (by omega)

/-- The list form, ready for J3. -/
theorem ledgerTimelineList (OC : Int → Prop) (nh : Nat) (GD : Gdexec) (LH : List Ledger) :
    gwf GD.gdG → ledgerHistOkList OC nh GD LH →
    gtlOk OC nh GD.gdG (ledgerOwn (lhFun LH) GD.gdG.gxGmo.length) :=
  fun hwf hok => ledgerTimeline OC nh GD _ hwf (ledgerHistOkOfList OC nh GD LH hok)

/-! # 3. THE GHOST -/

/-- The ledger camera: Rocq's `gmap_viewR Z (agreeR (leibnizO holder))` = iris-lean's ghost map
(header deviation 3). -/
class LedgerG (GF : BundledGFunctors) where
  [ledgerMapG : GhostMapG GF Int Holder (GMapF Int)]

attribute [reducible, instance] LedgerG.ledgerMapG

/-- The current ledger of a list history. -/
def lhCur (LH : List Ledger) : Ledger := LH.getLast?.getD ∅

theorem lhCurApp (LH : List Ledger) (L : Ledger) : lhCur (LH ++ [L]) = L := by
  simp [lhCur]

section ghost

variable {GF : BundledGFunctors} [LedgerG GF]

/-- The authoritative ledger (J2: beside `annotInterp`). -/
def ledgerAuth (γ : GName) (L : Ledger) : IProp GF :=
  ghost_map_auth γ (DFrac.own 1) L

/-- The EXCLUSIVE per-byte fragment: byte `a`'s entry is `h`. -/
def tokFrag (γ : GName) (a : Int) (h : Holder) : IProp GF :=
  ghost_map_elem γ (DFrac.own 1) a h

/-- Hart `i` holds byte `a`'s token. -/
def tokAt (γ : GName) (a : Int) (i : Agent) : IProp GF := tokFrag γ a (.held i)

/-- Byte `a`'s token is in flight since the release-class write `w`. -/
def tokPending (γ : GName) (a : Int) (w : Geid) : IProp GF := tokFrag γ a (.pending w)

instance ledgerAuthTimeless (γ : GName) (L : Ledger) : Timeless (ledgerAuth (GF := GF) γ L) := by
  unfold ledgerAuth; infer_instance

instance tokFragTimeless (γ : GName) (a : Int) (h : Holder) :
    Timeless (tokFrag (GF := GF) γ a h) := by
  unfold tokFrag; infer_instance

instance tokAtTimeless (γ : GName) (a : Int) (i : Agent) : Timeless (tokAt (GF := GF) γ a i) := by
  unfold tokAt; infer_instance

instance tokPendingTimeless (γ : GName) (a : Int) (w : Geid) :
    Timeless (tokPending (GF := GF) γ a w) := by
  unfold tokPending; infer_instance

/-- ALLOCATION: the initial ledger, one fragment per entry. -/
theorem ledgerAlloc (L : Ledger) :
    ⊢@{IProp GF} |==> ∃ γ, ledgerAuth γ L ∗ [∗map] a ↦ h ∈ L, tokFrag γ a h := by
  unfold ledgerAuth tokFrag
  exact ghost_map_alloc L

/-- AGREEMENT: a fragment reads the authoritative entry. -/
theorem ledgerAgree (γ : GName) (L : Ledger) (a : Int) (h : Holder) :
    ⊢ ledgerAuth (GF := GF) γ L -∗ tokFrag γ a h -∗ ⌜get? L a = some h⌝ := by
  unfold ledgerAuth tokFrag
  exact ghost_map_lookup

theorem tokAtAgree (γ : GName) (L : Ledger) (a : Int) (i : Agent) :
    ⊢ ledgerAuth (GF := GF) γ L -∗ tokAt γ a i -∗ ⌜get? L a = some (.held i)⌝ :=
  ledgerAgree γ L a _

theorem tokPendingAgree (γ : GName) (L : Ledger) (a : Int) (w : Geid) :
    ⊢ ledgerAuth (GF := GF) γ L -∗ tokPending γ a w -∗ ⌜get? L a = some (.pending w)⌝ :=
  ledgerAgree γ L a _

/-- EXCLUSIVITY: a byte has ONE fragment. -/
theorem tokFragExcl (γ : GName) (a : Int) (h h' : Holder) :
    ⊢ tokFrag (GF := GF) γ a h -∗ tokFrag γ a h' -∗ False := by
  unfold tokFrag
  iintro H1 H2
  ihave %hne := ghost_map_elem_ne γ a a (DFrac.own 1) h h' $$ H1 H2
  exact (hne rfl).elim

theorem tokAtExcl (γ : GName) (a : Int) (i j : Agent) :
    ⊢ tokAt (GF := GF) γ a i -∗ tokAt γ a j -∗ False :=
  tokFragExcl γ a _ _

/-- THE RAW UPDATE (the three rules below are its disciplined uses). -/
theorem ledgerUpdate (γ : GName) (L : Ledger) (a : Int) (h h' : Holder) :
    ⊢ ledgerAuth (GF := GF) γ L -∗ tokFrag γ a h ==∗
      ledgerAuth γ (insert L a h') ∗ tokFrag γ a h' := by
  unfold ledgerAuth tokFrag
  exact ghost_map_update h'

/-! ## 3.1 THE THREE RULES -/

/-- RELEASE: at a release-class write `w` of hart `w.1`, its token becomes pending.  THE ONLY
RULE THAT TAKES A TOKEN FROM A HART. -/
theorem tokRelease (GD : Gdexec) (γ : GName) (L : Ledger) (a : Int) (w : Geid) :
    glblIs GD.gdG w lbRelw →
    ⊢ ledgerAuth (GF := GF) γ L -∗ tokAt γ a w.1 ==∗
      ledgerAuth γ (insert L a (.pending w)) ∗ tokPending γ a w ∗
      ⌜get? L a = some (.held w.1) ∧ ledgerMove GD w (get? L a) (some (.pending w))⌝ := by
  intro hrel
  unfold ledgerAuth tokAt tokPending tokFrag
  iintro Ha Ht
  icombine Ha Ht gives %hL
  imod ghost_map_update (.pending w) $$ Ha Ht with ⟨Ha, Ht⟩
  imodintro
  isplitl [Ha]
  · iexact Ha
  isplitl [Ht]
  · iexact Ht
  ipureintro
  exact ⟨hL, by rw [hL]; exact .lmRelease hrel⟩

/-- ACQUIRE: at an event `r` reached from the releasing write `w` by an `acqFrom` edge, the
pending token lands at `r`'s hart. -/
theorem tokAcquire (GD : Gdexec) (γ : GName) (L : Ledger) (a : Int) (w r : Geid) :
    acqFrom GD w r →
    ⊢ ledgerAuth (GF := GF) γ L -∗ tokPending γ a w ==∗
      ledgerAuth γ (insert L a (.held r.1)) ∗ tokAt γ a r.1 ∗
      ⌜get? L a = some (.pending w) ∧ ledgerMove GD r (get? L a) (some (.held r.1))⌝ := by
  intro hacq
  unfold ledgerAuth tokAt tokPending tokFrag
  iintro Ha Ht
  icombine Ha Ht gives %hL
  imod ghost_map_update (.held r.1) $$ Ha Ht with ⟨Ha, Ht⟩
  imodintro
  isplitl [Ha]
  · iexact Ha
  isplitl [Ht]
  · iexact Ht
  ipureintro
  exact ⟨hL, by rw [hL]; exact .lmAcquire w hacq⟩

/-- PULL-BACK: the releasing hart takes its own token back, for free, at any of its events. -/
theorem tokPullback (GD : Gdexec) (γ : GName) (L : Ledger) (a : Int) (w e : Geid) :
    e.1 = w.1 →
    ⊢ ledgerAuth (GF := GF) γ L -∗ tokPending γ a w ==∗
      ledgerAuth γ (insert L a (.held w.1)) ∗ tokAt γ a w.1 ∗
      ⌜get? L a = some (.pending w) ∧ ledgerMove GD e (get? L a) (some (.held w.1))⌝ := by
  intro he
  rw [← he]
  exact tokAcquire GD γ L a w e (.inr (.inr he))

/-! ## 3.2 The list-history form of the state-interpretation piece -/

def ledgerInterp (γ : GName) (LH : List Ledger) : IProp GF := ledgerAuth γ (lhCur LH)

/-- One phase-2 step: the current ledger was rewritten to `L'`; append it. -/
theorem ledgerInterpAppend (γ : GName) (LH : List Ledger) (L' : Ledger) :
    ⊢ ledgerAuth (GF := GF) γ L' -∗ ledgerInterp γ (LH ++ [L']) := by
  unfold ledgerInterp
  rw [lhCurApp]
  iintro H
  iexact H

theorem ledgerInterpCur (γ : GName) (LH : List Ledger) :
    ledgerInterp (GF := GF) γ LH ⊣⊢ ledgerAuth γ (lhCur LH) := .rfl

end ghost

/-! # 4. THE HART-INDEXED READ/WRITE RULES (thin wrappers) -/

section readI

variable {GF : BundledGFunctors} [AxlogG GF Hent] [LedgerG GF]

/-- `AxToken.ownedReadRule` for a reader HOLDING the token: required and returned. -/
theorem ownedReadRuleI (GD : Gdexec) (a : Int) (r : Geid) (γ γl : GName) (H : List Hent)
    (S : GMapF Geid Qp) (wl : Geid) (vl : BitVec 8) :
    rvwmoCatConsistent GD →
    (∀ p, p ∈ H → gwritesByte GD.gdG p.1 a p.2) →
    chainWith (gmoLt GD.gdG) (H.map Prod.fst) →
    (∀ w v, gwritesByte GD.gdG w a v → WeakRvwmoGraph.gpo GD.gdG w r → w ∈ H.map Prod.fst) →
    H.getLast? = some (wl, vl) →
    (∃ t v, greadsByte GD.gdG r a t v) →
    ((∃ e, e ∈ (FiniteMap.dom_set S : GSet Geid) ∧ gmoLt GD.gdG e r)
     ∨
     (wl ∈ (FiniteMap.dom_set S : GSet Geid) ∧
      (∀ e, e ∈ (FiniteMap.dom_set S : GSet Geid) → ¬ gmoLt GD.gdG e r) ∧
      WeakRvwmoGraph.gpo GD.gdG wl r ∧
      (∀ w' v', gwritesByte GD.gdG w' a v' →
        WeakRvwmoGraph.gpo GD.gdG wl w' → WeakRvwmoGraph.gpo GD.gdG w' r → False))) →
    ⊢ tokAt (GF := GF) γl a r.1 -∗
      tokTie GD γ a H S -∗
      (∀ w v, ⌜gwritesByte GD.gdG w a v⌝ -∗ ⌜gmoLt GD.gdG w r⌝ -∗
        ∃ H', ⌜w ∈ H'.map Prod.fst⌝ ∗ histSnap γ a H') -∗
      tokAt γl a r.1 ∗
      ⌜grfAt GD.gdG a wl r ∧ ∀ t v, greadsByte GD.gdG r a t v → v = vl⌝ := by
  intro hcons hwr hch hown hlast hrd hcase
  iintro Ht Htie Hsn
  ihave %h := ownedReadRule GD a r γ H S wl vl hcons hwr hch hown hlast hrd hcase $$ [$Htie $Hsn]
  isplitl [Ht]
  · iexact Ht
  ipureintro
  exact h

/-- THE ACQUIRING READ: the reader holds the token PENDING at the last writer `wl`; the read rule
proves `grfAt a wl r` — `acqFrom`'s rf arm — so `tokAcquire` fires with no further hypothesis. -/
theorem ownedReadRuleAcq (GD : Gdexec) (a : Int) (r : Geid) (γ γl : GName) (L : Ledger)
    (H : List Hent) (S : GMapF Geid Qp) (wl : Geid) (vl : BitVec 8) :
    rvwmoCatConsistent GD →
    (∀ p, p ∈ H → gwritesByte GD.gdG p.1 a p.2) →
    chainWith (gmoLt GD.gdG) (H.map Prod.fst) →
    (∀ w v, gwritesByte GD.gdG w a v → WeakRvwmoGraph.gpo GD.gdG w r → w ∈ H.map Prod.fst) →
    H.getLast? = some (wl, vl) →
    (∃ t v, greadsByte GD.gdG r a t v) →
    ((∃ e, e ∈ (FiniteMap.dom_set S : GSet Geid) ∧ gmoLt GD.gdG e r)
     ∨
     (wl ∈ (FiniteMap.dom_set S : GSet Geid) ∧
      (∀ e, e ∈ (FiniteMap.dom_set S : GSet Geid) → ¬ gmoLt GD.gdG e r) ∧
      WeakRvwmoGraph.gpo GD.gdG wl r ∧
      (∀ w' v', gwritesByte GD.gdG w' a v' →
        WeakRvwmoGraph.gpo GD.gdG wl w' → WeakRvwmoGraph.gpo GD.gdG w' r → False))) →
    ⊢ ledgerAuth (GF := GF) γl L -∗
      tokPending γl a wl -∗
      tokTie GD γ a H S -∗
      (∀ w v, ⌜gwritesByte GD.gdG w a v⌝ -∗ ⌜gmoLt GD.gdG w r⌝ -∗
        ∃ H', ⌜w ∈ H'.map Prod.fst⌝ ∗ histSnap γ a H') ==∗
      ledgerAuth γl (insert L a (.held r.1)) ∗ tokAt γl a r.1 ∗
      ⌜get? L a = some (.pending wl) ∧ ledgerMove GD r (get? L a) (some (.held r.1)) ∧
        grfAt GD.gdG a wl r ∧ ∀ t v, greadsByte GD.gdG r a t v → v = vl⌝ := by
  intro hcons hwr hch hown hlast hrd hcase
  iintro Ha Hp Htie Hsn
  ihave %h := ownedReadRule GD a r γ H S wl vl hcons hwr hch hown hlast hrd hcase $$ [$Htie $Hsn]
  imod tokAcquire GD γl L a wl r (.inl ⟨a, h.1⟩) $$ Ha Hp with ⟨Ha, Ht, %hp⟩
  imodintro
  isplitl [Ha]
  · iexact Ha
  isplitl [Ht]
  · iexact Ht
  ipureintro
  exact ⟨hp.1, hp.2, h.1, h.2⟩

end readI

section rulesI

variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [axG : AxirisG GF]
  [AxlogG GF Hent] [LedgerG GF]

/-- THE HART-INDEXED n-BYTE WRITE RULE, ANY store class: per byte the token `tokAt (a+j) i` and
the full history auth; the tokens are handed back to the continuation unchanged. -/
theorem wpWriteOwnedToknI [Axpol] (γ γl : GName)
    (Hob_eq : ∀ (GD : Gdexec) (σ : AxirisG.obSt GF) (s : GSet Geid),
      AxirisG.obStInterp GD σ s ⊣⊢ protInv γ GD s)
    (GD : Gdexec) (i : Agent) (k k'0 : Nat) (ls' : AxirisG.logTsT GF) (a : Int)
    (Hs : List (List Hent)) (Vs : List (BitVec 8)) (data : List (BitVec 8))
    (Ψ : Unit → IProp GF)
    (Hlen : Hs.length = Vs.length)
    (Hisw : gisW GD.gdG (i, k) = true)
    (Hcompl : ∀ a' v', gwritesByte GD.gdG (i, k) a' v' →
      ∃ j : Nat, Vs[j]? = some v' ∧ a' = a + (j : Int))
    (Hgd : graphData GD (i, k) = some data)
    (Hnalloc : ⊢ ∀ na : Mea GF, naAtProgress GD i k na ∗ AxirisG.annotInterp na ==∗
       AxirisG.annotInterp (insert na (i, k)
         iprop(tokn γ GD a (writenHist (i, k) Vs Hs) {[(i, k) := (1 : Qp)]} ∗
           ([∗list] j ↦ H' ∈ writenHist (i, k) Vs Hs, histSnap γ (a + (j : Int)) H')))) :
    ⊢ ([∗list] j ↦ H ∈ Hs, tokAt γl (a + (j : Int)) i ∗ histAuth γ (a + (j : Int)) 1 H) -∗
      AxirisG.localInterp GD i k'0 ls' -∗
      (([∗list] j ↦ _H ∈ Hs, tokAt γl (a + (j : Int)) i) -∗ Ψ ()) -∗
      wpEvStep GD i k (fun _ : Unit => True) (fun _ : Unit => graphData GD (i, k) = some data)
        (fun _ => k'0) Ψ := by
  iintro Htoks Hloc HΨ
  icases BigSepL.bigSepL_sep_eqv.1 $$ Htoks with ⟨Htok, Hauths⟩
  have W := wpWriteOwnedTokn γ Hob_eq GD i k k'0 ls' a Hs Vs data Ψ Hlen Hisw Hcompl Hgd Hnalloc
  ihave W := W $$ Hauths Hloc
  iapply W
  iapply HΨ
  iexact Htok

/-- THE HART-INDEXED n-BYTE READ RULE (`wpReadOwnedTokn` with the reader's tokens required and
returned). -/
theorem wpReadOwnedToknI [Axpol] (γ γl : GName)
    (Hob_eq : ∀ (GD : Gdexec) (σ : AxirisG.obSt GF) (s : GSet Geid),
      AxirisG.obStInterp GD σ s ⊣⊢ protInv γ GD s)
    (GD : Gdexec) (Hcons : rvwmoCatConsistent GD)
    (rdatn : Geid → Int × List (Nat × BitVec 8))
    (HrdatnSpec : ∀ r, gisW GD.gdG r = false →
      graphValue GD r = some ((rdatn r).2.map Prod.snd) ∧
      ∀ (j : Nat) t v, (rdatn r).2[j]? = some (t, v) →
        greadsByte GD.gdG r ((rdatn r).1 + (j : Int)) t v)
    (i : Agent) (k k'0 : Nat) (ls' : AxirisG.logTsT GF)
    (Hs : List (List Hent)) (Vs : List (BitVec 8)) (S : GMapF Geid Qp)
    (Ψ : List (BitVec 8) → IProp GF)
    (Hrgmo : (i, k) ∈ GD.gdG.gxGmo) (Hnw : gisW GD.gdG (i, k) = false)
    (Hlen : (rdatn (i, k)).2.length = Hs.length)
    (Hvals : List.Forall₂ (fun H v => ∃ wl, H.getLast? = some (wl, v)) Hs Vs)
    (Hwr : ∀ (j : Nat) (H : List Hent), Hs[j]? = some H →
      ∀ p, p ∈ H → gwritesByte GD.gdG p.1 ((rdatn (i, k)).1 + (j : Int)) p.2)
    (Hch : ∀ (j : Nat) (H : List Hent), Hs[j]? = some H → chainWith (gmoLt GD.gdG) (H.map Prod.fst))
    (Hown : ∀ (j : Nat) (H : List Hent), Hs[j]? = some H →
      ∀ w v, gwritesByte GD.gdG w ((rdatn (i, k)).1 + (j : Int)) v →
        WeakRvwmoGraph.gpo GD.gdG w (i, k) → w ∈ H.map Prod.fst)
    (Hrd : ∀ (j : Nat) (H : List Hent), Hs[j]? = some H →
      ∃ t v, greadsByte GD.gdG (i, k) ((rdatn (i, k)).1 + (j : Int)) t v)
    (Hcase : ∀ (j : Nat) (H : List Hent) wl vl, Hs[j]? = some H → H.getLast? = some (wl, vl) →
      (∃ e, e ∈ (FiniteMap.dom_set S : GSet Geid) ∧ gmoLt GD.gdG e (i, k))
      ∨
      (wl ∈ (FiniteMap.dom_set S : GSet Geid) ∧
       (∀ e, e ∈ (FiniteMap.dom_set S : GSet Geid) → ¬ gmoLt GD.gdG e (i, k)) ∧
       WeakRvwmoGraph.gpo GD.gdG wl (i, k) ∧
       (∀ w' v', gwritesByte GD.gdG w' ((rdatn (i, k)).1 + (j : Int)) v' →
         WeakRvwmoGraph.gpo GD.gdG wl w' → WeakRvwmoGraph.gpo GD.gdG w' (i, k) → False)))
    (Hpref : (LawfulSet.ofList (gmoPrefix GD.gdG (i, k)) : GSet Geid) ⊆ Axpol.sPol GD (i, k))
    (Hnalloc : ⊢ ∀ na : Mea GF, naAtProgress GD i k na ∗ AxirisG.annotInterp na ==∗
       AxirisG.annotInterp (insert na (i, k)
         iprop(⌜∀ (j : Nat) (H : List Hent), Hs[j]? = some H → ∀ wl vl, H.getLast? = some (wl, vl) →
           ownedExpectedWriteb GD ((rdatn (i, k)).1 + (j : Int)) (i, k) wl vl ∧
           ∃ t, greadsByte GD.gdG (i, k) ((rdatn (i, k)).1 + (j : Int)) t vl⌝))) :
    ⊢ ([∗list] j ↦ _H ∈ Hs, tokAt γl ((rdatn (i, k)).1 + (j : Int)) i) -∗
      tokn γ GD (rdatn (i, k)).1 Hs S -∗
      AxirisG.localInterp GD i k'0 ls' -∗
      (([∗list] j ↦ _H ∈ Hs, tokAt γl ((rdatn (i, k)).1 + (j : Int)) i) -∗
        ∀ v : List (BitVec 8), ⌜v.length = Hs.length⌝ -∗ Ψ v) -∗
      wpEvStep GD i k (fun v : List (BitVec 8) => v.length = Hs.length)
        (fun v => graphValue GD (i, k) = some v) (fun _ => k'0) Ψ := by
  iintro Htok Htie Hloc Hcont
  have W := wpReadOwnedTokn γ Hob_eq GD Hcons rdatn HrdatnSpec i k k'0 ls' Hs Vs S Ψ
    Hrgmo Hnw Hlen Hvals Hwr Hch Hown Hrd Hcase Hpref Hnalloc
  ihave W := W $$ Htie Hloc
  iapply W
  iapply Hcont
  iexact Htok

end rulesI

/-! # 5. VACUITY CERTIFICATES on `AxViol.mp` and its plain twin -/

/-- The Own-class bytes of `mp`: x = 0, y = 1. -/
def ocMp (a : Int) : Prop := a = 0 ∨ a = 1

def lMp0 : Ledger := insert ({[0 := .held 0]} : Ledger) 1 (.held 0)
def lMp1 : Ledger := insert (insert lMp0 0 (.pending (0, 2))) 1 (.pending (0, 2))
def lMp2 : Ledger := insert (insert lMp1 0 (.held 1)) 1 (.held 1)

/-- gmo = [W0x (0,0); W.rl0y (0,2); R.aq1y (1,0); R1x (1,1)]: hart 0 holds both bytes through
its plain write; releases both at the sd.rl; hart 1 acquires both at the ld.aq; then reads x
holding it. -/
def lhMp : List Ledger := [lMp0, lMp0, lMp1, lMp2, lMp2]

theorem mpRel : glblIs AxViol.mp.gdG (0, 2) lbRelw := ⟨_, rfl, by decide +kernel⟩

theorem mpRfY : grfAt AxViol.mp.gdG 1 (0, 2) (1, 0) :=
  ⟨2, b1, (grbBSpec _ _ _ _ _).1 (by decide +kernel), by decide +kernel⟩

theorem mpAcq : acqFrom AxViol.mp (0, 2) (1, 0) := .inl ⟨1, mpRfY⟩

theorem mpLedgerHist : ledgerHistOkList ocMp 2 AxViol.mp lhMp := by
  refine ⟨rfl, ?_⟩
  intro k e L L' hk hL hL'
  rcases k with _ | _ | _ | _ | k
  · obtain rfl : ((0, 0) : Geid) = e := Option.some.inj (hk : some ((0, 0) : Geid) = some e)
    obtain rfl : lMp0 = L := Option.some.inj (hL : some lMp0 = some L)
    obtain rfl : lMp0 = L' := Option.some.inj (hL' : some lMp0 = some L')
    refine ledgerStepOfMoves _ _ _ _ _ _ (ledgerMovesRefl _ _ _) ?_
    intro a ha _ _
    rcases ha with rfl | rfl <;> exact .inl (by decide +kernel)
  · obtain rfl : ((0, 2) : Geid) = e := Option.some.inj (hk : some ((0, 2) : Geid) = some e)
    obtain rfl : lMp0 = L := Option.some.inj (hL : some lMp0 = some L)
    obtain rfl : lMp1 = L' := Option.some.inj (hL' : some lMp1 = some L')
    refine ledgerStepOfMoves _ _ _ _ _ _ ?_ ?_
    · exact ledgerMovesRelease _ _ _ _ 1
        (ledgerMovesRelease _ _ _ _ 0 (ledgerMovesRefl _ _ _) (by decide +kernel)
          (by decide +kernel) mpRel)
        (by decide +kernel) (by decide +kernel) mpRel
    · intro a ha _ _
      rcases ha with rfl | rfl <;> exact .inl (by decide +kernel)
  · obtain rfl : ((1, 0) : Geid) = e := Option.some.inj (hk : some ((1, 0) : Geid) = some e)
    obtain rfl : lMp1 = L := Option.some.inj (hL : some lMp1 = some L)
    obtain rfl : lMp2 = L' := Option.some.inj (hL' : some lMp2 = some L')
    refine ledgerStepOfMoves _ _ _ _ _ _ ?_ ?_
    · exact ledgerMovesAcquire _ _ _ _ 1 (0, 2)
        (ledgerMovesAcquire _ _ _ _ 0 (0, 2) (ledgerMovesRefl _ _ _) (by decide +kernel)
          (by decide +kernel) mpAcq)
        (by decide +kernel) (by decide +kernel) mpAcq
    · intro a ha _ _
      rcases ha with rfl | rfl <;> exact .inr ⟨(0, 2), by decide +kernel, by decide +kernel⟩
  · obtain rfl : ((1, 1) : Geid) = e := Option.some.inj (hk : some ((1, 1) : Geid) = some e)
    obtain rfl : lMp2 = L := Option.some.inj (hL : some lMp2 = some L)
    obtain rfl : lMp2 = L' := Option.some.inj (hL' : some lMp2 = some L')
    refine ledgerStepOfMoves _ _ _ _ _ _ (ledgerMovesRefl _ _ _) ?_
    intro a ha _ _
    rcases ha with rfl | rfl <;> exact .inl (by decide +kernel)
  · have hk' : (none : Option Geid) = some e := hk
    cases hk'

/-- The ledger yields a timeline … -/
theorem mpTlLedger :
    gtlOk ocMp 2 AxViol.mp.gdG (ledgerOwn (lhFun lhMp) AxViol.mp.gdG.gxGmo.length) :=
  ledgerTimelineList _ _ _ _ mpCat.1 mpLedgerHist

/-- (Lean-only; header deviation 6) a label of an event sits in a program row. -/
theorem AxTokLedger.gxLblMem (G : Gexec) (e : Geid) (l : Lbl) :
    gxLbl G e = some l → ∃ p ∈ G.gxProg, l ∈ p := by
  intro hl
  unfold gxLbl at hl
  cases hp : G.gxProg[e.1]? with
  | none => rw [hp] at hl; cases hl
  | some p =>
    rw [hp] at hl
    exact ⟨p, elem_of_list_lookup_2 hp, elem_of_list_lookup_2 hl⟩

/-- … whose plain hart writes are Own-class … -/
theorem mpPlainWritesOC :
    ∀ w a v, w ∈ AxViol.mp.gdG.gxGmo → tidHart 2 (some w.1) →
      glblIs AxViol.mp.gdG w lbPlain → gwritesByte AxViol.mp.gdG w a v → ocMp a := by
  intro w a v _ _ _ ⟨l, base, vs, j, hl, hwr, hj, ha⟩
  have hall : ∀ p ∈ AxViol.mp.gdG.gxProg, ∀ l ∈ p,
      (match lbWr l with
       | some (base, vs) => decide (vs.length = 1 ∧ (base = 0 ∨ base = 1))
       | none => true) = true := by decide +kernel
  obtain ⟨p, hp, hlp⟩ := AxTokLedger.gxLblMem _ _ _ hl
  have h := hall p hp l hlp
  rw [hwr] at h
  obtain ⟨hlen, hb⟩ := of_decide_eq_true h
  have hj0 : j = 0 := by
    have := (List.getElem?_eq_some_iff.1 hj).1
    omega
  subst hj0
  unfold accAddr at ha
  unfold ocMp
  omega

/-- … so the refutation applies, FROM THE LEDGER. -/
theorem mpNoViolationLedger : ¬ gdviolationHart 2 AxViol.mp :=
  ownedNoViolationCat ocMp 2 AxViol.mp _ mpCat mpTlLedger mpPlainWritesOC

/-- THE GHOST DERIVATION: the token of x moves hart 0 → hart 1 by `tokRelease` at the sd.rl
(0,2) and `tokAcquire` at the ld.aq (1,0). -/
theorem mpGhostHandoff {GF : BundledGFunctors} [LedgerG GF] (γ : GName) :
    ⊢ ledgerAuth (GF := GF) γ lMp0 -∗ tokAt γ 0 0 ==∗
      ∃ L, ledgerAuth γ L ∗ tokAt γ 0 1 ∗ ⌜get? L 0 = some (.held 1)⌝ := by
  iintro Ha Ht
  have R := tokRelease (GF := GF) AxViol.mp γ lMp0 0 (0, 2) mpRel
  imod R $$ Ha Ht with ⟨Ha, Hp, -⟩
  have A := tokAcquire (GF := GF) AxViol.mp γ (insert lMp0 0 (.pending (0, 2))) 0 (0, 2) (1, 0)
    mpAcq
  imod A $$ Ha Hp with ⟨Ha, Ht, -⟩
  imodintro
  iexists (insert (insert lMp0 0 (.pending (0, 2))) 0 (.held 1))
  isplitl [Ha]
  · iexact Ha
  isplitl [Ht]
  · iexact Ht
  ipureintro
  exact get?_insert_eq rfl

/-! ## 5.1 THE NEGATIVE TWIN: the sd.rl replaced by a plain sd -/

def mpPlain : Gdexec :=
  ⟨⟨vimg, [[LStore false 0 [b1] .WCplain,
            LFence true true false true,
            LStore false 1 [b1] .WCplain],
           [LLoad true 1 [2] [b1],
            LLoad false 0 [1] [b1]]],
    [(0, 0), (0, 2), (1, 0), (1, 1)]⟩, [], []⟩

theorem mpPlainCat : rvwmoCatConsistent mpPlain :=
  catConsistentBSound _ (by decide +kernel)

theorem mpPlainNoRel (h : Geid) : ¬ glblIs mpPlain.gdG h lbRelw := by
  intro hr
  obtain ⟨p, hp, l, hl, hb⟩ := axViolGlblIsProg _ _ _ hr
  have hall : ∀ p ∈ mpPlain.gdG.gxProg, ∀ l ∈ p, lbRelw l = false := by decide +kernel
  rw [hall p hp l hl] at hb
  cases hb

/-- It IS a violation: hart 1 reads hart 0's plain write of x with no publication in between. -/
theorem mpPlainViol : gdviolationHart 2 mpPlain := by
  refine ⟨(0, 0), (1, 1), 0, b1, by decide +kernel,
    (gwbBSpec _ _ _ _).1 (by decide +kernel), ⟨_, rfl, by decide +kernel⟩, trivial,
    ⟨0, rfl, by omega⟩, ⟨1, rfl, by omega⟩, by decide, ?_⟩
  refine .inr ⟨1, b1, (grbBSpec _ _ _ _ _).1 (by decide +kernel),
    by decide +kernel, ?_, ?_⟩
  · rintro ⟨h, _, hr, _⟩
    exact mpPlainNoRel h hr
  · rintro ws _ ⟨h, _, hr, _⟩
    exact mpPlainNoRel h hr

/-- At the plain sd (0,2) no ledger step moves a Held entry — hart 0 keeps x. -/
theorem mpPlainStepKeeps (OC : Int → Prop) (L L' : Ledger) (a : Int) (i : Agent) :
    AxTokLedger.ledgerStep OC 2 mpPlain (0, 2) L L' →
    get? L a = some (.held i) → get? L' a = some (.held i) :=
  ledgerStepPlainKeeps OC 2 mpPlain (0, 2) L L' a i (mpPlainNoRel _)

/-- NO ledger history is legal on the twin. -/
theorem mpPlainNoLedgerHist (LH : Nat → Ledger) :
    ¬ ledgerHistOk (fun _ => True) 2 mpPlain LH := fun hok =>
  ownedNoViolationCat (fun _ => True) 2 mpPlain _ mpPlainCat
    (ledgerTimeline _ _ _ _ mpPlainCat.1 hok) (fun _ _ _ _ _ _ _ => trivial) mpPlainViol

theorem mpPlainNoLedgerHistList (LH : List Ledger) :
    ¬ ledgerHistOkList (fun _ => True) 2 mpPlain LH := fun hok =>
  mpPlainNoLedgerHist _ (ledgerHistOkOfList _ _ _ _ hok)

end Weak
