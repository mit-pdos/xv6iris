/-
Weak: **the §7 tie lemmas of `AxGraphCat`, in PROCESSING order** (AxSL tier).

Rocq: `iris/AxTieProc.v` @ xxvzwolszwmp.

The Rocq header, in substance (task: LB/AxSL ctrl-gate scheduler, review-fetch Q4;
design `claude-notes/design/weak-memory-lb-axsl.md` rev 7 and
`weak-memory-lb-axsl-review-fetch.md` Q4).  PURE (no Iris), a leaf below
`AxGraphCat`.

SPLIT VERDICT.  CASE (ii), forwarding (`tieReadIi` = `ownForwardCat'`), HOLDS
unconditionally under deferral: it is a pure graph fact about the fixed candidate.
Likewise `tieCases`, `tieAcqCase`, `identStopLemma` hold verbatim (the `*Proc`
one-liners below).  CASE (i), the tie (`ownedReadEpoch`, `tieInv`, `tieReadI`),
FAILS AS STATED if a deferred read `r` is validated against the LIVE per-byte
history accumulated by `r`'s processing time: the live history's last entry may
be a foreign write gmo-AFTER `r` (the deferral window), hence not `gvisible` to
it — §3 builds the machine-checked two-hart witness `wit`.  It HOLDS under the
extra hypothesis `noFwBetween` (no foreign same-byte write gmo-after `r` yet
processed before it): `procGmoAgree` shows processing order and gmo order then
COINCIDE for cross-hart same-byte writes, `procChainGmoChain` that a
proc-chained history is gmo-chained (unconditionally), and
`ownedReadEpochProc`/`tieReadIProc` discharge the boundary-visibility obligation
from `ltIn proc b r` and hand off to the unchanged originals.  The robust
scheduler fix (a `hist_snap` taken when the gmo walker reaches `r`) is the Rocq
header's recommendation and is outside this file.

  §1  `lpos`/`ltIn` (a list-position strict order over an arbitrary list) and
      `isProcOrder` (the setting's hypotheses on a processing-order permutation
      of `G.gxGmo` deferring a set `D` of plain reads);
  §2  `noFwBetween`, `procGmoAgree`, `procWriteOrderIff`, `procChain`,
      `procChainGmoChain`, the restated case (i) `ownedReadEpochProc` /
      `tieReadIProc`, and the verbatim `tieReadIiProc`, `tieCasesProc`,
      `tieAcqCaseProc`, `identStopLemmaProc`;
  §3  THE COUNTEREXAMPLE `wit` (`witRefutesNoFwBetween`).

**Deviations from Rocq.**

1. NAMES: lowerCamelCase as `Weak/WeakMem.lean` deviation 1.  The duplicated
   Rocq names (`notes/weak-port-dupnames.json`) `lb_wr_is_w` and
   `gwrites_byte_is_w` are FILE-QUALIFIED (`AxTieProc.lbWrIsW`,
   `AxTieProc.gwritesByteIsW`); `WeakRvwmoGraph.gpo` is referred to qualified.
2. VOCABULARY: as `WeakRvwmoGraph` deviation 2 (`l !! i` ↦ `l[i]?`, `NoDup` ↦
   `List.Nodup`, `list_find` ↦ `listFind` with a `decide` predicate, `Z` ↦ `Int`,
   `bv 8` ↦ `BitVec 8`, `agent` ↦ `Nat`, `stdpp.list_basics.last` ↦
   `List.getLast?`, `GExec img prog gmo` ↦ `⟨img, prog, gmo⟩`,
   `WeakLitmus.b0/b1/b2` ↦ `b0`/`b1`/`b2`).
3. The Rocq `Notation`s `wit_h0`/`wit_r`/`wit_wf` are `abbrev`s `witH0`/`witR`/
   `witWf`.
4. The closed `vm_compute` side conditions (gmo/proc positions, `gwriteAt`,
   `gwix`) are `decide`, through the file-local `Decidable` instances
   `gmoLtDecTie`/`ltInDec`; the nine-pair case analysis of `witIsProcOrder`'s
   keep clause closes each pair by `decide` instead of rewriting with the
   `witGpos*` facts (which are still ported).
5. The `Proof using All` annotations have no Lean counterpart.

**Name map** (Rocq → Lean): `lpos`; `lt_in` ↦ `ltIn`; `lt_in_irrefl` ↦
`ltInIrrefl`; `lpos_lookup` ↦ `lposLookup`; `lpos_of_lookup` ↦ `lposOfLookup`;
`is_proc_order` ↦ `isProcOrder`; `lb_wr_is_w` ↦ `AxTieProc.lbWrIsW`;
`gwrites_byte_is_w` ↦ `AxTieProc.gwritesByteIsW`; `no_fw_between` ↦
`noFwBetween`; `proc_gmo_agree` ↦ `procGmoAgree`; `proc_write_order_iff` ↦
`procWriteOrderIff`; `proc_chain` ↦ `procChain`; `proc_chain_gmo_chain` ↦
`procChainGmoChain`; `owned_read_epoch_proc` ↦ `ownedReadEpochProc`;
`tie_read_i_proc` ↦ `tieReadIProc`; `tie_read_ii_proc` ↦ `tieReadIiProc`;
`tie_cases_proc` ↦ `tieCasesProc`; `tie_acq_case_proc` ↦ `tieAcqCaseProc`;
`ident_stop_lemma_proc` ↦ `identStopLemmaProc`; `wit_img` ↦ `witImg`; `wit`;
`wit_h0`/`wit_r`/`wit_wf` ↦ `witH0`/`witR`/`witWf`; `wit_proc` ↦ `witProc`;
`wit_D` ↦ `witD`; `wit_lbl` ↦ `witLbl`; `wit_wr` ↦ `witWr`; `wit_rd` ↦ `witRd`;
`wit_wf_gwf` ↦ `witWfGwf`; `wit_lv` ↦ `witLv`; `wit_gmo_lt_r_wf` ↦
`witGmoLtRWf`; `wit_not_visible_wf_r` ↦ `witNotVisibleWfR`;
`wit_lt_in_proc_wf_r` ↦ `witLtInProcWfR`; `wit_proc_nodup` ↦ `witProcNodup`;
`wit_gpos_h0`/`_r`/`_wf` ↦ `witGposH0`/`witGposR`/`witGposWf`;
`wit_lpos_h0`/`_wf`/`_r` ↦ `witLposH0`/`witLposWf`/`witLposR`;
`wit_is_proc_order` ↦ `witIsProcOrder`; `wit_refutes_no_fw_between` ↦
`witRefutesNoFwBetween`.

**Not ported:** nothing (the §4 `Print Assumptions` block has no Lean twin; the
lint's axiom check covers it).
-/
import Weak.AxGraphCat

namespace Weak

open MachCSL MachCSL.Stdpp
open Lbl

/-! # 1. `proc` and `isProcOrder` -/

/-- The generic list-position order — `gpos`/`gmoLt`'s shape over an ARBITRARY
list (instantiated at `proc` throughout this file). -/
def lpos (L : List Geid) (e : Geid) : Nat :=
  match listFind (fun e' => decide (e' = e)) L with
  | some (i, _) => i
  | none => 0

def ltIn (L : List Geid) (e1 e2 : Geid) : Prop :=
  e1 ∈ L ∧ e2 ∈ L ∧ lpos L e1 < lpos L e2

theorem ltInIrrefl (L : List Geid) (e : Geid) : ¬ ltIn L e e := by
  rintro ⟨_, _, h⟩
  omega

/-- `lpos`'s defining property, off the LOOKUP. -/
theorem lposLookup (L : List Geid) (e : Geid) :
    e ∈ L → ∃ i, L[i]? = some e ∧ lpos L e = i := by
  intro he
  unfold lpos
  cases hf : listFind (fun e' => decide (e' = e)) L with
  | some q =>
    obtain ⟨i, x⟩ := q
    obtain ⟨hi, hx, _⟩ := list_find_Some.1 hf
    have : x = e := of_decide_eq_true hx
    subst this
    exact ⟨i, hi, rfl⟩
  | none =>
    have := list_find_None.1 hf e he
    simp at this

theorem lposOfLookup (L : List Geid) (i : Nat) (e : Geid) :
    L.Nodup → L[i]? = some e → lpos L e = i := by
  intro hnd hi
  obtain ⟨i', hi', h⟩ := lposLookup L e (elem_of_list_lookup_2 hi)
  rw [h]
  exact NoDup_lookup hnd hi' hi

/-- THE SETTING's hypotheses on a processing-order permutation `proc` of
`G.gxGmo` that defers exactly the reads in `D`: same elements, no duplicates;
`D` holds only PLAIN reads; a NON-deferred event keeps every gmo-later event
after it (`proc_keep`); a deferred read never moves past a po-later WRITE of its
own hart (`proc_own_write`). -/
def isProcOrder (G : Gexec) (D : Geid → Prop) (proc : List Geid) : Prop :=
  (∀ e, e ∈ proc ↔ e ∈ G.gxGmo) ∧
  proc.Nodup ∧
  (∀ e, D e → ∃ l, gxLbl G e = some l ∧ lbIsR l = true ∧ lbIsW l = false) ∧
  (∀ e1 e2, ¬ D e1 → gmoLt G e1 e2 → ltIn proc e1 e2) ∧
  (∀ r e, D r → WeakRvwmoGraph.gpo G r e → glblIs G e lbIsW → ltIn proc r e)

/-! # 2. The cross-hart agreement lemma, and the restated §7 lemmas -/

theorem AxTieProc.lbWrIsW (l : Lbl) (base : Int) (vs : List (BitVec 8)) :
    lbWr l = some (base, vs) → lbIsW l = true :=
  Weak.lbWrIsW l (base, vs)

theorem AxTieProc.gwritesByteIsW (G : Gexec) (w : Geid) (a : Int) (v : BitVec 8) :
    gwritesByte G w a v → glblIs G w lbIsW := by
  rintro ⟨l, base, vs, _, hl, hwr, _, _⟩
  exact ⟨l, hl, AxTieProc.lbWrIsW l base vs hwr⟩

/-- A `D`-event is never a write. -/
private theorem notDOfW (G : Gexec) (D : Geid → Prop) (w : Geid) :
    (∀ e, D e → ∃ l, gxLbl G e = some l ∧ lbIsR l = true ∧ lbIsW l = false) →
    glblIs G w lbIsW → ¬ D w := by
  rintro hdread ⟨l', hl', hwt⟩ hD
  obtain ⟨l, hl, _, hw⟩ := hdread w hD
  rw [hl, Option.some.injEq] at hl'
  subst hl'
  rw [hw] at hwt
  cases hwt

/-- NO FOREIGN WRITE BETWEEN: no other hart's write to `a` is gmo-after `r` yet
`proc`-before it.  Not derived here (see the header). -/
def noFwBetween (G : Gexec) (proc : List Geid) (a : Int) (r : Geid) : Prop :=
  ∀ w v, gwritesByte G w a v → w.1 ≠ r.1 → gmoLt G r w → ¬ ltIn proc w r

/-- THE AGREEMENT LEMMA: for a cross-hart same-byte write `w` and a deferred read
`r`, "processed before" and "gmo-before" coincide, given `noFwBetween`. -/
theorem procGmoAgree (G : Gexec) (D : Geid → Prop) (proc : List Geid) (a : Int) (r w : Geid)
    (v : BitVec 8) :
    gwf G → isProcOrder G D proc → D r → noFwBetween G proc a r →
    gwritesByte G w a v → w.1 ≠ r.1 →
    (ltIn proc w r ↔ gmoLt G w r) := by
  rintro hwf ⟨_, _, hdread, hkeep, _⟩ hDr hnf hwb hhart
  obtain ⟨lr, hlr, hrr, _⟩ := hdread r hDr
  have hww := AxTieProc.gwritesByteIsW G w a v hwb
  have hne : w ≠ r := by
    rintro rfl
    exact notDOfW G D w hdread hww hDr
  have hwg : w ∈ G.gxGmo := gwfMemGmo G w hwf (WeakRvwmoGraph.glblIsWGmem G w hww)
  have hrg : r ∈ G.gxGmo := gwfMemGmo G r hwf (WeakRvwmoGraph.glblIsRGmem G r ⟨lr, hlr, hrr⟩)
  constructor
  · intro hlt
    rcases gmoLtTotal G w r hwf.1 hwg hrg hne with h | h
    · exact h
    · exact absurd hlt (hnf w v hwb hhart h)
  · intro hgmo
    exact hkeep w r (notDOfW G D w hdread hww) hgmo

/-- WRITE/WRITE ORDER IS UNCONDITIONAL: two same-byte writes keep their relative
gmo order in `proc`. -/
theorem procWriteOrderIff (G : Gexec) (D : Geid → Prop) (proc : List Geid) (a : Int)
    (w1 w2 : Geid) (v1 v2 : BitVec 8) :
    gwf G → isProcOrder G D proc →
    gwritesByte G w1 a v1 → gwritesByte G w2 a v2 →
    (ltIn proc w1 w2 ↔ gmoLt G w1 w2) := by
  rintro hwf ⟨_, _, hdread, hkeep, _⟩ hwb1 hwb2
  have hw1 := AxTieProc.gwritesByteIsW G w1 a v1 hwb1
  have hw2 := AxTieProc.gwritesByteIsW G w2 a v2 hwb2
  have hnd1 := notDOfW G D w1 hdread hw1
  have hnd2 := notDOfW G D w2 hdread hw2
  by_cases hne : w1 = w2
  · subst hne
    exact ⟨fun h => absurd h (ltInIrrefl proc w1), fun h => absurd h (gmoLtIrrefl G w1)⟩
  have hg1 : w1 ∈ G.gxGmo := gwfMemGmo G w1 hwf (WeakRvwmoGraph.glblIsWGmem G w1 hw1)
  have hg2 : w2 ∈ G.gxGmo := gwfMemGmo G w2 hwf (WeakRvwmoGraph.glblIsWGmem G w2 hw2)
  constructor
  · intro hlt
    rcases gmoLtTotal G w1 w2 hwf.1 hg1 hg2 hne with h | h
    · exact h
    · exfalso
      obtain ⟨_, _, ha⟩ := hlt
      obtain ⟨_, _, hb⟩ := hkeep w2 w1 hnd2 h
      omega
  · intro hgmo
    exact hkeep w1 w2 hnd1 hgmo

/-- A same-byte history that is `proc`-chained is gmo-chained — unconditionally. -/
def procChain (proc : List Geid) (Hl : List Geid) : Prop :=
  chainWith (ltIn proc) Hl

theorem procChainGmoChain (G : Gexec) (D : Geid → Prop) (proc : List Geid) (a : Int)
    (Hl : List Geid) :
    gwf G → isProcOrder G D proc →
    (∀ w, w ∈ Hl → ∃ v, gwritesByte G w a v) →
    procChain proc Hl → gmoChain G Hl := by
  intro hwf hpo hwr hch i w1 w2 hi1 hi2
  obtain ⟨v1, hwb1⟩ := hwr w1 (elem_of_list_lookup_2 hi1)
  obtain ⟨v2, hwb2⟩ := hwr w2 (elem_of_list_lookup_2 hi2)
  exact (procWriteOrderIff G D proc a w1 w2 v1 v2 hwf hpo hwb1 hwb2).1 (hch i w1 w2 hi1 hi2)

/-- THE RESTATED CASE (i), boundary form: `ownedReadEpoch` with the boundary's
visibility ESTABLISHED from `ltIn proc b r` (cross-hart `b`) and the history
`proc`-chained.  Needs exactly `noFwBetween`. -/
theorem ownedReadEpochProc (G : Gexec) (D : Geid → Prop) (proc : List Geid)
    (Hl : List Geid) (a : Int) (r b : Geid) (vb : BitVec 8) :
    gwf G → gloadValue G → isProcOrder G D proc → D r → noFwBetween G proc a r →
    (∀ w, w ∈ Hl → ∃ v, gwritesByte G w a v) →
    procChain proc Hl →
    b ∈ Hl → gwritesByte G b a vb → b.1 ≠ r.1 → ltIn proc b r →
    epochCov G Hl a b r →
    (∃ t v, greadsByte G r a t v) →
    ∃ w, lastVisible G Hl r = some w ∧ grfAt G a w r ∧ (w = b ∨ gco G b w) := by
  intro hwf hlv hpo hDr hnf hwr hpch hb hwbb hhart hltb hcov hrd
  have hvisb : gvisible G b r :=
    Or.inl ((procGmoAgree G D proc a r b vb hwf hpo hDr hnf hwbb hhart).1 hltb)
  exact ownedReadEpoch G Hl a r b hwf hlv hwr (procChainGmoChain G D proc a Hl hwf hpo hwr hpch)
    hb hvisb hcov hrd

/-- ... and the read-rule shape, `tieReadI` restated the same way. -/
theorem tieReadIProc (G : Gexec) (D : Geid → Prop) (proc : List Geid)
    (Hl : List Geid) (a : Int) (tie r wl : Geid) (vl : BitVec 8) :
    gwf G → gloadValue G → isProcOrder G D proc → D r → noFwBetween G proc a r →
    (∀ w, w ∈ Hl → ∃ v, gwritesByte G w a v) →
    procChain proc Hl →
    Hl.getLast? = some wl →
    tieInv G Hl tie → gmoLt G tie r → WeakRvwmoGraph.gpo G tie r →
    gwritesByte G wl a vl → wl.1 ≠ r.1 → ltIn proc wl r →
    epochCov G Hl a wl r →
    (∃ t v, greadsByte G r a t v) →
    grfAt G a wl r := by
  intro hwf hlv hpo hDr hnf hwr hpch hlast _ _ _ hwbl hhart hlt hcov hrd
  obtain ⟨w, hlv', hrf, _⟩ := ownedReadEpochProc G D proc Hl a r wl vl hwf hlv hpo hDr hnf hwr
    hpch (last_Some_elem_of hlast) hwbl hhart hlt hcov hrd
  obtain ⟨Hl0, rfl⟩ := last_Some.1 hlast
  have hsn : lastVisible G (Hl0 ++ [wl]) r = some wl :=
    lastSuchSnoc _ _ _ _
      (Or.inl ((procGmoAgree G D proc a r wl vl hwf hpo hDr hnf hwbl hhart).1 hlt))
  rw [hsn, Option.some.injEq] at hlv'
  subst hlv'
  exact hrf

/-- CASE (ii) is UNCHANGED: `tieReadIi` verbatim. -/
theorem tieReadIiProc (GD : Gdexec) (S : List Geid) (a : Int) (w r : Geid) (v : BitVec 8)
    (t : Nat) (vr : BitVec 8) :
    rvwmoCatConsistent GD →
    w ∈ S → (∀ e, e ∈ S → ¬ gmoLt GD.gdG e r) →
    WeakRvwmoGraph.gpo GD.gdG w r → gwritesByte GD.gdG w a v →
    greadsByte GD.gdG r a t vr →
    (∀ w' v', gwritesByte GD.gdG w' a v' → WeakRvwmoGraph.gpo GD.gdG w w' →
      WeakRvwmoGraph.gpo GD.gdG w' r → False) →
    grfAt GD.gdG a w r ∧ vr = v :=
  tieReadIi GD S a w r v t vr

/-- THE EXHAUSTIVE SPLIT is unchanged. -/
theorem tieCasesProc (G : Gexec) (S : List Geid) (r : Geid) :
    (∃ e, e ∈ S ∧ gmoLt G e r) ∨ (∀ e, e ∈ S → ¬ gmoLt G e r) :=
  tieCases G S r

/-- THE ACQUIRE CASE is unchanged. -/
theorem tieAcqCaseProc (GD : Gdexec) (S : List Geid) (acq r : Geid) :
    gppoCatGmo GD → acq ∈ S → gacqPo GD.gdG acq r →
    ¬ (∀ e, e ∈ S → ¬ gmoLt GD.gdG e r) :=
  tieAcqCase GD S acq r

/-- THE IDENTITY-STOP LEMMA is unchanged. -/
theorem identStopLemmaProc (G : Gexec) (i : Nat) (rowExp rowReal : List Lbl)
    (Dd : Nat → Nat → Prop) (stop : Nat) :
    G.gxProg[i]? = some rowReal →
    identStop rowExp rowReal = some stop →
    dCovers Dd rowReal stop → dGmo G i Dd →
    (∀ j, j < stop → identAgree rowExp rowReal j) ∧
    (∀ k, stop ≤ k → glblIs G (i, k) lbIsW →
      ∃ r, r < stop ∧ glblIs G (i, r) lbIsR ∧ gmoLt G (i, r) (i, k)) :=
  identStopLemma G i rowExp rowReal Dd stop

/-! # 3. THE COUNTEREXAMPLE: `noFwBetween` is NECESSARY

`wit`: byte 0.  Hart 0: `r`, one plain load of byte 0 with `ts = [1]` (source
`h0`).  Hart 1: `h0`, a store of `b1`, then `wf`, a store of `b2`.
`gxGmo = [h0, r, wf]`; `proc := [h0, wf, r]` defers `r` past the foreign `wf`. -/

local instance gmoLtDecTie (G : Gexec) (e1 e2 : Geid) : Decidable (gmoLt G e1 e2) := by
  unfold gmoLt; infer_instance

local instance ltInDec (L : List Geid) (e1 e2 : Geid) : Decidable (ltIn L e1 e2) := by
  unfold ltIn; infer_instance

def witImg : Image := fun _ => some b0

def wit : Gexec :=
  ⟨witImg,
   [[LLoad false 0 [1] [b1]],
    [LStore false 0 [b1] .WCplain, LStore false 0 [b2] .WCplain]],
   [(1, 0), (0, 0), (1, 1)]⟩

abbrev witH0 : Geid := (1, 0)
abbrev witR : Geid := (0, 0)
abbrev witWf : Geid := (1, 1)

def witProc : List Geid := [witH0, witWf, witR]
def witD (e : Geid) : Prop := e = witR

theorem witLbl (e : Geid) (l : Lbl) :
    gxLbl wit e = some l →
    (e = witR ∧ l = LLoad false 0 [1] [b1]) ∨
    (e = witH0 ∧ l = LStore false 0 [b1] .WCplain) ∨
    (e = witWf ∧ l = LStore false 0 [b2] .WCplain) := by
  obtain ⟨i, k⟩ := e
  intro hl
  rcases i with _ | _ | i <;> rcases k with _ | _ | k <;> simp [gxLbl, wit] at hl <;>
    subst hl <;> simp

theorem witWr (e : Geid) (a : Int) (v : BitVec 8) :
    gwritesByte wit e a v →
    (e = witH0 ∧ a = 0 ∧ v = b1) ∨ (e = witWf ∧ a = 0 ∧ v = b2) := by
  rintro ⟨l, base, vs, j, hl, hwr, hv, ha⟩
  rcases witLbl e l hl with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    simp [lbWr] at hwr <;> obtain ⟨rfl, rfl⟩ := hwr <;>
    rcases j with _ | j <;> simp at hv <;> subst hv <;> simp [accAddr] at ha <;> subst ha <;> simp

theorem witRd (e : Geid) (a : Int) (t : Nat) (v : BitVec 8) :
    greadsByte wit e a t v → e = witR ∧ a = 0 ∧ t = 1 ∧ v = b1 := by
  rintro ⟨l, base, ts, vs, j, hl, hrd, ht, hv, ha⟩
  rcases witLbl e l hl with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    simp [lbRd] at hrd <;> obtain ⟨rfl, rfl, rfl⟩ := hrd <;>
    rcases j with _ | j <;> simp at ht hv <;> subst ht hv <;> simp [accAddr] at ha <;>
    subst ha <;> simp

theorem witWfGwf : gwf wit := by
  refine ⟨?_, ?_, ?_⟩
  · decide
  · intro e
    constructor
    · intro he
      simp only [wit, List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl <;> exact ⟨_, rfl, rfl⟩
    · rintro ⟨l, hl, _⟩
      rcases witLbl e l hl with ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> decide
  · intro i p k l hp hk
    rcases i with _ | _ | i <;> simp [wit] at hp <;> subst hp <;>
      rcases k with _ | _ | k <;> simp at hk <;> subst hk <;> simp

/-- `r`'s source is `h0`; `wf` is NOT visible to it. -/
theorem witLv : gloadValue wit := by
  intro e a t v hr
  obtain ⟨rfl, rfl, rfl, rfl⟩ := witRd e a t v hr
  refine ⟨?_, ?_⟩
  · show ∃ w, gwriteAt wit 1 = some w ∧ gwritesByte wit w 0 b1 ∧ gvisible wit w witR
    exact ⟨witH0, by decide,
      ⟨LStore false 0 [b1] .WCplain, 0, [b1], 0, rfl, rfl, rfl, by simp [accAddr]⟩,
      Or.inl (by decide)⟩
  · intro w' v' hw' hvis
    rcases witWr w' _ v' hw' with ⟨rfl, _⟩ | ⟨rfl, _⟩
    · decide
    · exfalso
      rcases hvis with h | ⟨hag, _⟩
      · exact absurd h (by decide)
      · simp at hag

theorem witGmoLtRWf : gmoLt wit witR witWf := by decide

theorem witNotVisibleWfR : ¬ gvisible wit witWf witR := by
  rintro (hmo | ⟨hag, _⟩)
  · exact gmoLtIrrefl wit witR (gmoLtTrans wit _ _ _ witGmoLtRWf hmo)
  · simp at hag

theorem witLtInProcWfR : ltIn witProc witWf witR := by decide

theorem witProcNodup : witProc.Nodup := by decide

/-- Concrete `gpos`/`lpos` facts, pinned off lookups. -/
theorem witGposH0 : gpos wit witH0 = 0 := gposOfLookup _ _ _ witWfGwf.1 rfl
theorem witGposR : gpos wit witR = 1 := gposOfLookup _ _ _ witWfGwf.1 rfl
theorem witGposWf : gpos wit witWf = 2 := gposOfLookup _ _ _ witWfGwf.1 rfl

theorem witLposH0 : lpos witProc witH0 = 0 := lposOfLookup _ _ _ witProcNodup rfl
theorem witLposWf : lpos witProc witWf = 1 := lposOfLookup _ _ _ witProcNodup rfl
theorem witLposR : lpos witProc witR = 2 := lposOfLookup _ _ _ witProcNodup rfl

/-- `proc` is legal per `isProcOrder`: it only reorders `r` (the sole element of
`D`); `r`'s hart has no po-later event, so the own-write clause is vacuous. -/
theorem witIsProcOrder : isProcOrder wit witD witProc := by
  refine ⟨?_, witProcNodup, ?_, ?_, ?_⟩
  · intro e
    simp only [witProc, wit, List.mem_cons, List.not_mem_nil, or_false]
    constructor <;> rintro (h | h | h) <;> simp [h]
  · intro e he
    unfold witD at he
    subst he
    exact ⟨LLoad false 0 [1] [b1], rfl, rfl, rfl⟩
  · intro e1 e2 hD hgmo
    obtain ⟨h1, h2, hlt⟩ := hgmo
    simp only [wit, List.mem_cons, List.not_mem_nil, or_false] at h1 h2
    -- the nine pairs: (h0,r) and (h0,wf) are the real pairs kept by `proc`;
    -- (r,wf) is excluded by `hD`; the rest are refuted by `hlt`
    rcases h1 with rfl | rfl | rfl <;> rcases h2 with rfl | rfl | rfl <;>
      first
        | decide
        | exact absurd hlt (by decide)
        | exact absurd rfl hD
  · intro r e hDr hpo _
    exfalso
    unfold witD at hDr
    subst hDr
    obtain ⟨ie, ke⟩ := e
    obtain ⟨hag, hlt, _, hsome⟩ := hpo
    simp only at hag hlt
    subst hag
    rcases ke with _ | ke
    · omega
    · simp [gxLbl, wit] at hsome

/-- THE REFUTATION: `wf` is processed before `r` yet NOT `gvisible` to it, and
`noFwBetween wit witProc 0 witR` is FALSE. -/
theorem witRefutesNoFwBetween :
    gwritesByte wit witWf 0 b2 ∧ witWf.1 ≠ witR.1 ∧
    gmoLt wit witR witWf ∧ ltIn witProc witWf witR ∧
    ¬ gvisible wit witWf witR ∧
    ¬ noFwBetween wit witProc 0 witR := by
  have hwb : gwritesByte wit witWf 0 b2 :=
    ⟨LStore false 0 [b2] .WCplain, 0, [b2], 0, rfl, rfl, rfl, by simp [accAddr]⟩
  refine ⟨hwb, by decide, witGmoLtRWf, witLtInProcWfR, witNotVisibleWfR, ?_⟩
  intro hnf
  exact hnf witWf b2 hwb (by decide) witGmoLtRWf witLtInProcWfR

end Weak
