/-
Weak: **the litmus suite AGAINST THE sRVWMO DEFINITION**.

Rocq: `iris/WeakSrvwmoLitmus.v` @ xxvzwolszwmp (1cc222280).

The Rocq header, in substance.  `WeakLitmus` runs the litmus programs on the
OPERATIONAL machine and settles each verdict by an invariant over reachable
configurations.  This file settles the SAME verdicts against the MODEL:
`WeakAxiomatic3`'s `srvwmoConsistent`, the named axiomatization whose
realizability theorem is T1 (`srvwmoRealizable`).  A positive verdict here is
a machine-checked sRVWMO-consistent candidate — hence, THROUGH T1, a
promise-free machine run; a negative verdict is a machine-checked refutation
of the whole candidate FAMILY with the outcome pinned.

Contents: §1 per-agent positions in a candidate's trace (`agPos` and its four
index lemmas); §2 THE CONFORMANCE KIT (`instrLbl` / `conforms` / `outc`, the
glue `srvwmoRun` and its contrapositive `srvwmoNoRun`); §3 two acyclicity
lemmas generalising `WeakAxiomatic3` §12 (`cohRelAcycTs`, `obOpAcycW`: no
"no event both reads and writes" hypothesis, and the `ppoOp` RULE-14 arm
admitted); §4 reading a value back to its writer (`candReadWriter`); §5
POSITIVE verdicts (SB, MP-no-fence, MP-writer-fence-only, AMO); §6 NEGATIVE
verdicts (LB — the headline; MP with both fences / writer fence + acquire /
reader fence only; CoRR); §7–§9 prose (precedents not redone, what is not
done, THE VERDICT TABLE with the two DELIBERATE DIVERGENCES from RVWMO).

**Deviations from Rocq.**

1. NAMES: as `Weak/WeakAxiomatic.lean` deviation 1 (lowerCamelCase; digit
   segments are glued: `sb_00_allowed` ↦ `sb00Allowed`, `bs_01` ↦ `bs01`).
   The Rocq `Notation`s `ax`/`ay`/`rg1`/`rg2`/`FENCE_RW_W`/`FENCE_R_RW` are
   `local notation`s with the same spellings (as in `WeakLitmus`); `Notation
   prog` is `abbrev Prog`.  `lb_rd_is_r` is in the duplicated-name table and
   is declared `WeakSrvwmoLitmus.lbRdIsR`.  Rocq's unqualified
   `msg_byte_single` (resolved to `WeakAxiomatic3`'s, the later import) is
   `WeakAxiomatic3.msgByteSingle`; `WeakLitmus.msg_byte_single` is
   `WeakLitmus.msgByteSingle`.
2. VOCABULARY: as `Weak/WeakAxiomatic.lean` deviation 2.  `bool_decide (P)`
   is `if P then 1 else 0`; `P !! i ≫= (λ p, p !! j)` is
   `P[i]?.bind (fun p => p[j]?)`; `EStep i l` is `⟨i, l⟩`, `Cand img tr` is
   `⟨img, tr⟩`, `WMsg a vs tid k` is `⟨a, vs, tid, k⟩`.
3. CLOSED CHECKS: the Rocq `vm_compute` value checks (`*_values`) are
   `decide` on the closed `Option` equality for reads of a log message, and a
   rewrite with `logByte0`/`img0X`/`img0Y` for reads of the era-initial image
   (`img0` is a tree map; the image lookups are `WeakLitmus`'s lemmas).
4. PROOFS: the `*_wmsg_inv` inversions go through the Lean-only helper
   `instrLblWmsg` (which write message a conformant step can carry) and then
   enumerate the closed program by `rcases`, where Rocq destructs the agent
   and position by hand; same statements.
5. Lean-only helper (no Rocq twin): `instrLblWmsg`.

**Name map (Rocq → Lean).** `ag_count` ↦ `agCount`, `ag_pos` ↦ `agPos`,
`ag_count_app` ↦ `agCountApp`, `ag_pos_0`/`_S`/`_S_none`/`_mono`/`_prev`/
`_inj` ↦ `agPos0`/`agPosS`/`agPosSNone`/`agPosMono`/`agPosPrev`/`agPosInj`,
`instr_lbl` ↦ `instrLbl`, `prog` ↦ `Prog`, `conforms` and `outc` kept,
`srvwmo_run` ↦ `srvwmoRun`, `cand_shape_of_wf` ↦ `candShapeOfWf`,
`cand_values_of_wf` ↦ `candValuesOfWf`, `srvwmo_of_wf` ↦ `srvwmoOfWf`,
`srvwmo_no_run` ↦ `srvwmoNoRun`, `cand_shape_rd` ↦ `candShapeRd`,
`cand_lb_rd_ts_reads` ↦ `candLbRdTsReads`, `ets_lt_wr` ↦ `etsLtWr`,
`fr_ets_lt` ↦ `frEtsLt`, `coh_rel_acyc_ts` ↦ `cohRelAcycTs`,
`ob_op_acyc_w` ↦ `obOpAcycW`, `cand_reads_at1` ↦ `candReadsAt1`,
`cand_read_log` ↦ `candReadLog`, `cand_read_writer` ↦ `candReadWriter`,
`cand_no_fence_ord` ↦ `candNoFenceOrd`, `cand_no_aq_acq` ↦ `candNoAqAcq`,
`cand_no_pair_acq` ↦ `candNoPairAcq`, `cand_no_ord` ↦ `candNoOrd`,
`cand_no_rl_rel_acq` ↦ `candNoRlRelAcq`, `cand_no_rl_rel_ord` ↦
`candNoRlRelOrd`, `lb_rd_is_r` ↦ `WeakSrvwmoLitmus.lbRdIsR`,
`cand_rw_disjoint_atomicity` ↦ `candRwDisjointAtomicity`, `cand_wr_b_at` ↦
`candWrBAt`, `cand_rd_b_at` ↦ `candRdBAt`, `cand_plain_ok` ↦ `candPlainOk`;
per shape `X ∈ {sb, mpn, mpw, amo}`: `X_P`/`X_tr`/`X_cd`/`X_tr_inv`/
`X_shape`/`X_values`/`X_no_poloc`/`X_ok`/`X_conf` ↦ `XP`/`XTr`/`XCd`/
`XTrInv`/`XShape`/`XValues`/`XNoPoloc`/`XOk`/`XConf`, `amo_no_po` ↦
`amoNoPo`, `amo_atomicity` ↦ `amoAtomicity`, `sb_out00` ↦ `sbOut00`,
`mpn_out`/`mpw_out`/`amo_out` ↦ `mpnOut`/`mpwOut`/`amoOut`, `sb_00_allowed`
↦ `sb00Allowed`, `mpn_weak_allowed` ↦ `mpnWeakAllowed`, `mpw_weak_allowed` ↦
`mpwWeakAllowed`, `amo_latest_allowed` ↦ `amoLatestAllowed`;
`outc_writer` ↦ `outcWriter`, `outc_initial` ↦ `outcInitial`; per shape
`Y ∈ {lb, mpf, mpa, mpg, corr}`: `Y_P`/`Y_out`/`Y_wmsg_inv`/
`Y_forbidden_model`/`Y_forbidden_machine` ↦ `YP`/`YOut`/`YWmsgInv`/
`YForbiddenModel`/`YForbiddenMachine`, `lb_values_forbidden` ↦
`lbValuesForbidden`; `bs_01`/`bs_02`/`bs_10`/`bs_12`/`bs_21` ↦ `bs01`/`bs02`/
`bs10`/`bs12`/`bs21`, `mbx1_x`/`mby1_x`/`mbx2_x` ↦ `mbx1X`/`mby1X`/`mbx2X`,
`ev_at_ne` ↦ `evAtNe`, `conf_pin`/`conf_store`/`conf_fence`/`conf_load` ↦
`confPin`/`confStore`/`confFence`/`confLoad`.

**Not ported:** nothing.  §7–§9 of the Rocq file are prose, kept as the
comments at the end.

**Statements checked** (by hand, against Rocq): all of them.
-/
import Weak.WeakAxiomatic3
import Weak.WeakLitmus

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open Lbl Ev Instr

/-- The litmus vocabulary, re-declared: `WeakLitmus`'s own are local. -/
local notation "ax" => (0 : Int)
local notation "ay" => (8 : Int)
local notation "rg1" => (1 : Nat)
local notation "rg2" => (2 : Nat)

/-- fence rw,w — the release-side writer fence; fence r,rw — the acquire-side
reader fence. -/
local notation "FENCE_RW_W" => Instr.IFence true true false true
local notation "FENCE_R_RW" => Instr.IFence true false true true

/-! # 1. Per-agent positions in a candidate's trace

`agPos tr i k` is the number of steps of agent `i` strictly before position
`k` — i.e. WHICH instruction of agent `i`'s program the step at `k` is.  Four
facts: monotone, advances by one across a step of the agent, has a
PREDECESSOR (the descent every negative verdict runs on), and is INJECTIVE on
the agent's own steps. -/

def agCount (i : Nat) : List Estep → Nat
  | [] => 0
  | s :: tr' => (if s.esAg = i then 1 else 0) + agCount i tr'

def agPos (tr : List Estep) (i : Nat) (k : Nat) : Nat := agCount i (tr.take k)

theorem agCountApp (i : Nat) (l1 l2 : List Estep) :
    agCount i (l1 ++ l2) = agCount i l1 + agCount i l2 := by
  induction l1 with
  | nil => simp [agCount]
  | cons s l1 ih => simp only [List.cons_append, agCount, ih]; omega

theorem agPos0 (tr : List Estep) (i : Nat) : agPos tr i 0 = 0 := by
  simp [agPos, agCount]

/-- The step at `k`, if it belongs to agent `i`, advances `i`'s position by
one; any other step leaves it alone. -/
theorem agPosS (tr : List Estep) (i k : Nat) (s : Estep) :
    tr[k]? = some s → agPos tr i (k + 1) = (if s.esAg = i then 1 else 0) + agPos tr i k := by
  intro hs
  unfold agPos
  rw [take_S_r hs, agCountApp]
  simp only [agCount, Nat.add_zero]
  exact Nat.add_comm _ _

theorem agPosSNone (tr : List Estep) (i k : Nat) :
    tr[k]? = none → agPos tr i (k + 1) = agPos tr i k := by
  intro hs
  have := lookup_ge_None.1 hs
  unfold agPos
  rw [take_ge (show tr.length ≤ k + 1 by omega), take_ge (show tr.length ≤ k by omega)]

theorem agPosMono (tr : List Estep) (i k k' : Nat) : k ≤ k' → agPos tr i k ≤ agPos tr i k' := by
  induction k' with
  | zero => intro h; have : k = 0 := by omega
            subst this; exact Nat.le_refl _
  | succ m ih =>
    intro h
    rcases Nat.lt_or_ge m k with hlt | hge
    · have : k = m + 1 := by omega
      subst this; exact Nat.le_refl _
    · have := ih hge
      cases hs : tr[m]? with
      | some s => rw [agPosS tr i m s hs]; omega
      | none => rw [agPosSNone tr i m hs]; exact this

/-- THE DESCENT.  A step at agent-position `j + 1` has a predecessor step of the
same agent, strictly earlier, at agent-position `j`. -/
theorem agPosPrev (tr : List Estep) (i k j : Nat) :
    agPos tr i k = j + 1 →
    ∃ k' s', k' < k ∧ tr[k']? = some s' ∧ s'.esAg = i ∧ agPos tr i k' = j := by
  induction k with
  | zero => intro h; rw [agPos0] at h; omega
  | succ k ih =>
    intro hpos
    cases hs : tr[k]? with
    | none =>
      rw [agPosSNone tr i k hs] at hpos
      obtain ⟨k', s', h1, h2, h3, h4⟩ := ih hpos
      exact ⟨k', s', by omega, h2, h3, h4⟩
    | some s =>
      rw [agPosS tr i k s hs] at hpos
      by_cases hb : s.esAg = i
      · rw [if_pos hb] at hpos
        exact ⟨k, s, by omega, hs, hb, by omega⟩
      · rw [if_neg hb] at hpos
        obtain ⟨k', s', h1, h2, h3, h4⟩ := ih (by omega)
        exact ⟨k', s', by omega, h2, h3, h4⟩

/-- ... and the position PINS the step. -/
theorem agPosInj (tr : List Estep) (i k k' : Nat) (s s' : Estep) :
    tr[k]? = some s → s.esAg = i → tr[k']? = some s' → s'.esAg = i →
    agPos tr i k = agPos tr i k' → k = k' := by
  intro hs hag hs' hag' heq
  rcases Nat.lt_trichotomy k k' with hlt | heq' | hgt
  · exfalso
    have hle := agPosMono tr i (k + 1) k' hlt
    rw [agPosS tr i k s hs, if_pos hag] at hle; omega
  · exact heq'
  · exfalso
    have hle := agPosMono tr i (k' + 1) k hgt
    rw [agPosS tr i k' s' hs', if_pos hag'] at hle; omega

/-! # 2. THE CONFORMANCE KIT

`conforms P c`: the step at trace position `k` is the instruction its agent's
program has at that agent's own position — a LOAD free to take ANY timestamp
and ANY value, a STORE, a FENCE and an AMO's write half FIXED by the program.
Nothing forces a program to run to completion, and nothing forces the
interleaving. -/

def instrLbl (ins : Instr) (l : Lbl) : Prop :=
  match ins with
  | ILoad _ a aq => ∃ t v, l = LLoad aq a [t] [v]
  | IStore a v => l = LStore false a [v] .WCplain
  | IFence pr pw sr sw => l = LFence pr pw sr sw
  | IAmoSwapAq _ a v => ∃ t vv, l = LRmw true false a [t] [vv] [v] .WCexcl

abbrev Prog : Type := List (List Instr)

def conforms (P : Prog) (c : Cand) : Prop :=
  ∀ k s, c.cdTr[k]? = some s →
    ∃ p ins, P[s.esAg]? = some p ∧ p[agPos c.cdTr s.esAg k]? = some ins ∧ instrLbl ins s.esLb

/-- THE OUTCOME PREDICATE: "the `j`-th instruction of agent `i` read `v` at byte
`a`" (loads and AMO read halves alike). -/
def outc (c : Cand) (i j : Nat) (a : Int) (v : BitVec 8) : Prop :=
  ∃ k s t, c.cdTr[k]? = some s ∧ s.esAg = i ∧ agPos c.cdTr i k = j ∧
    lbRd s.esLb = some (a, [t], [v])

/-! ### The glue, in both directions -/

/-- A candidate that is sRVWMO-consistent AND conformant is a promise-free
MACHINE RUN OF THE PROGRAM (T1). -/
theorem srvwmoRun (img : Image) (P : Prog) (c : Cand) :
    c.cdImg = img → conforms P c → srvwmoConsistent c →
    execWf (candExec c) ∧ (candExec c).exTr = c.cdTr ∧ exImg (candExec c) = img ∧
      conforms P c := by
  rintro rfl hconf hcons
  obtain ⟨hwf, htr, himg⟩ := srvwmoRealizable c hcons
  exact ⟨hwf, htr, himg, hconf⟩

/-- The converse: a machine run IS an sRVWMO-consistent candidate. -/
theorem candShapeOfWf (c : Cand) : execWf (candExec c) → candShape c := by
  intro hwf k s hs
  have hstep := execStepAt (candExec c) k s hwf hs
  generalize stt (candExec c) (k + 1) = σ' at hstep
  generalize s.esLb = l at hstep ⊢
  cases hstep with
  | MStepLoad _ _ _ _ h => exact h.1
  | MStepStore _ _ _ _ h => exact h
  | MStepFence => trivial
  | MStepRmw _ _ _ _ _ _ _ h1 h2 h3 _ => exact ⟨h1, h2, h3.1⟩

theorem candValuesOfWf (c : Cand) : execWf (candExec c) → candValues c := by
  intro hwf k s base ts vs hs hrd j t v hj hv
  have hk := lookup_lt_Some hs
  have hlb := ((execRdOk (candExec c) k s base ts vs hwf hs hrd).2 j t v hj hv).1
  rwa [candEimg c k (by omega), candElog c k (by omega)] at hlb

theorem srvwmoOfWf (c : Cand) : execWf (candExec c) → srvwmoConsistent c := by
  intro hwf
  exact ⟨candShapeOfWf c hwf, candValuesOfWf c hwf, promiseFreeSound _ hwf, soundRelOrd _ hwf,
    promiseFreeObAcyclic _ hwf⟩

/-- THE CONTRAPOSITIVE, in the shape every negative verdict is stated in. -/
theorem srvwmoNoRun (P : Prog) (Out : Cand → Prop) :
    (∀ c, conforms P c → Out c → ¬ srvwmoConsistent c) →
    ∀ c, conforms P c → Out c → ¬ execWf (candExec c) :=
  fun hno c hconf hout hwf => hno c hconf hout (srvwmoOfWf c hwf)

/-! # 3. Two acyclicity lemmas, generalising `WeakAxiomatic3` §12

Both §12 hypotheses come off: the fused-RMW case is discharged by
`axAtomicity`, and the rule-14 arm by `etsLtWr` (everything an agent has done
sits strictly below the timestamp of a po-later store). -/

theorem candShapeRd (c : Cand) (k : Nat) (s : Estep) (base : Int) (ts : List Nat)
    (vs : List (BitVec 8)) :
    candShape c → c.cdTr[k]? = some s → lbRd s.esLb = some (base, ts, vs) →
    vs.length = ts.length := by
  intro hsh hs hrd
  have h := hsh k s hs
  obtain ⟨ag, l⟩ := s
  cases l with
  | LLoad aq b t v =>
    simp only [lbRd, Option.some.injEq, Prod.mk.injEq] at hrd
    obtain ⟨rfl, rfl, rfl⟩ := hrd; exact h
  | LStore => simp [lbRd] at hrd
  | LFence => simp [lbRd] at hrd
  | LRmw aq rl b t rv wv kc =>
    simp only [lbRd, Option.some.injEq, Prod.mk.injEq] at hrd
    obtain ⟨rfl, rfl, rfl⟩ := hrd; exact h.2.2

/-- `WeakAxiomatic2.lbRdTsReads` without `execWf`. -/
theorem candLbRdTsReads (c : Cand) (k : Nat) (s : Estep) (a : Int) (t : Nat) :
    candShape c → c.cdTr[k]? = some s → lbRdTs s.esLb a = some t →
    ∃ v, readsAt (candExec c) k a t v := by
  intro hsh hs
  unfold lbRdTs
  cases hrd : lbRd s.esLb with
  | none => simp
  | some x =>
    obtain ⟨base, ts, vs⟩ := x
    simp only
    split
    · intro hj
      have hlen := candShapeRd c k s base ts vs hsh hs hrd
      have hjl : (a - base).toNat < vs.length := by rw [hlen]; exact lookup_lt_Some hj
      refine ⟨vs[(a - base).toNat], s, base, ts, vs, (a - base).toNat, hs, hrd, hj,
        List.getElem?_eq_getElem hjl, ?_⟩
      unfold accAddr; omega
    · simp

/-- THE RULE-14 ARITHMETIC.  Everything an agent occupies at any byte before
position `k2` is strictly below the timestamp of a write at `k2`. -/
theorem etsLtWr (c : Cand) (a1 : Int) (e1 : Ev) (a2 : Int) (k2 : Nat) :
    candShape c → candValues c → (∀ k1, e1 = ev_at k1 → k1 < k2) →
    wrB (candExec c) a2 (ev_at k2) →
    ets (candExec c) a1 e1 < ets (candExec c) a2 (ev_at k2) := by
  intro hsh hval hlt hw2
  rcases candWrBInv c a2 (ev_at k2) hw2 with ⟨habs, _⟩ | ⟨k2', s2, m2, heq, hs2, hm2, _⟩
  · cases habs
  injection heq with heq; subst heq
  have hk2 := lookup_lt_Some hs2
  rw [etsWr (candExec c) a2 _ hw2, candEvTs c k2 (by omega)]
  cases e1 with
  | ev_init =>
    have : ets (candExec c) a1 ev_init = 0 := by unfold ets; split <;> rfl
    omega
  | ev_at k1 =>
    have hlt1 := hlt k1 rfl
    rcases wrBDec (candExec c) a1 (ev_at k1) with hw1 | hn1
    · rw [etsWr (candExec c) a1 _ hw1]
      rcases candWrBInv c a1 (ev_at k1) hw1 with ⟨habs, _⟩ | ⟨k1', s1, m1, heq1, hs1, hm1, _⟩
      · cases habs
      injection heq1 with heq1; subst heq1
      have h := candTsMono c k1 k2 s1 m1 hs1 hm1 hlt1 (by omega)
      rw [candEvTs c k2 (by omega)] at h; exact h
    · unfold ets
      rw [writesbFalse _ _ _ hn1]
      simp only [Bool.false_eq_true, ↓reduceIte]
      cases hs1 : (candExec c).exTr[k1]? with
      | none => (try simp only); omega
      | some s1 =>
        (try simp only)
        cases ht : lbRdTs s1.esLb a1 with
        | none => (try simp only [Option.getD_none]); omega
        | some t =>
          simp only [Option.getD_some]
          obtain ⟨v, hr⟩ := candLbRdTsReads c k1 s1 a1 t hsh hs1 ht
          have hle := candReadTsLe c hval k1 a1 t v hr
          have := cdLogLenLe c k1 k2 (by omega)
          omega

/-- An `fr` edge's source sits strictly below its target, EVEN WHEN THE SOURCE
IS A FUSED RMW that writes the byte — that case is exactly `axAtomicity`. -/
theorem frEtsLt (c : Cand) (a : Int) (x y : Ev) :
    candShape c → candValues c → axAtomicity (candExec c) →
    frB (candExec c) a x y → ets (candExec c) a x < ets (candExec c) a y := by
  rintro _ _ hatom ⟨⟨w0, hrf0, hco⟩, hne⟩
  obtain ⟨_, hwy, hlt⟩ := hco
  have hrf0' := hrf0
  obtain ⟨_, k, t0, v0, hkeq, hr, hts0⟩ := hrf0'
  rw [etsWr _ a y hwy]
  subst hkeq
  rcases wrBDec (candExec c) a (ev_at k) with hwx | hnx
  · rw [etsWr _ a _ hwx]
    have hnl := hatom k a w0 y hwx.1 hrf0 hwy hlt
    by_cases heq : evTs (candExec c) (ev_at k) = evTs (candExec c) y
    · exact absurd (candTsInj c (a, ev_at k) (a, y) hwx hwy heq) hne
    · omega
  · rw [etsRd _ a k t0 v0 hnx hr]; omega

theorem cohRelAcycTs (c : Cand) (a : Int) :
    candShape c → candValues c → axAtomicity (candExec c) →
    (∀ e1 e2, poLocB (candExec c) a e1 e2 → ets (candExec c) a e1 ≤ ets (candExec c) a e2) →
    ∀ e, ¬ tc (cohRel (candExec c) a) e e := by
  intro hsh hval hatom hnpl
  apply tcLexlt _ (fun e => (ets (candExec c) a e, evIx e))
  intro x y hxy
  rcases hxy with hpl | hrf | hco | hfr
  · have hle := hnpl x y hpl
    have := poIx (candExec c) x y hpl.1
    unfold lexlt; simp only; omega
  · have hrf' := hrf
    obtain ⟨hw, k, t, v, hkeq, hr, hts⟩ := hrf'
    subst hkeq
    rcases wrBDec (candExec c) a (ev_at k) with hwy | hny
    · unfold lexlt; left
      show ets _ a x < ets _ a (ev_at k)
      apply etsLtWr c a x a k hsh hval _ hwy
      intro k1 hk1; subst hk1
      have := candRfIx c a (ev_at k1) k hval hrf
      simp only [evIx] at this; omega
    · unfold lexlt; simp only
      rw [etsWr _ a x hw, hts, etsRd _ a k t v hny hr]
      right; exact ⟨rfl, candRfIx c a x k hval hrf⟩
  · obtain ⟨hw1, hw2, hlt⟩ := hco
    unfold lexlt; simp only
    rw [etsWr _ a x hw1, etsWr _ a y hw2]; exact .inl hlt
  · unfold lexlt; left
    exact frEtsLt c a x y hsh hval hatom hfr

theorem obOpAcycW (c : Cand) :
    candShape c → candValues c → axAtomicity (candExec c) →
    (∀ o1 o2, ppoOp (candExec c) o1 o2 →
      po (candExec c) o1.2 o2.2 ∧ wrB (candExec c) o2.1 o2.2) →
    ∀ o, ¬ tc (obOp (candExec c)) o o := by
  intro hsh hval hatom hppo
  apply tcKless _ (fun o => (ets (candExec c) o.1 o.2, ophase (candExec c) o.1 o.2, evIx o.2, o.1))
  rintro ⟨a1, e1⟩ ⟨a2, e2⟩ (hp | ⟨ha, hrf⟩ | ⟨ha, hco⟩ | ⟨ha, hfr⟩)
  · obtain ⟨hpo, hw2⟩ := hppo _ _ hp
    obtain ⟨k1, k2, s1, s2, he1, he2, hlt, _⟩ := hpo
    simp only at he1 he2 hw2; subst he1 he2
    unfold kless; left
    show ets _ a1 (ev_at k1) < ets _ a2 (ev_at k2)
    apply etsLtWr c a1 (ev_at k1) a2 k2 hsh hval _ hw2
    intro k' heq; injection heq with heq; subst heq; exact hlt
  · simp only at ha hrf; subst ha
    have hrf' := hrf
    obtain ⟨hw, k, t, v, hkeq, hr, hts⟩ := hrf'
    subst hkeq
    rcases wrBDec (candExec c) a1 (ev_at k) with hwy | hny
    · unfold kless; left
      show ets _ a1 e1 < ets _ a1 (ev_at k)
      apply etsLtWr c a1 e1 a1 k hsh hval _ hwy
      intro k1 hk1; subst hk1
      have := candRfIx c a1 (ev_at k1) k hval hrf
      simp only [evIx] at this; omega
    · unfold kless; simp only
      rw [etsWr _ a1 e1 hw, ophaseWr _ a1 e1 hw, ophaseNwr _ a1 _ hny, hts,
        etsRd _ a1 k t v hny hr]
      omega
  · simp only at ha hco; subst ha
    obtain ⟨hw1, hw2, hlt⟩ := hco
    unfold kless; simp only
    rw [etsWr _ a1 e1 hw1, etsWr _ a1 e2 hw2]
    exact .inl hlt
  · simp only at ha hfr; subst ha
    unfold kless; left
    exact frEtsLt c a1 e1 e2 hsh hval hatom hfr

/-! # 4. Reading a value back to its writer -/

theorem candReadsAt1 (c : Cand) (k : Nat) (s : Estep) (a : Int) (t : Nat) (v : BitVec 8) :
    c.cdTr[k]? = some s → lbRd s.esLb = some (a, [t], [v]) → readsAt (candExec c) k a t v := by
  intro hs hrd
  exact ⟨s, a, [t], [v], 0, hs, hrd, rfl, rfl, by simp [accAddr]⟩

theorem candReadLog (c : Cand) (k : Nat) (s : Estep) (a : Int) (t : Nat) (v : BitVec 8) :
    candValues c → c.cdTr[k]? = some s → lbRd s.esLb = some (a, [t], [v]) →
    logByte c.cdImg (cdLog c k) t a = some v := by
  intro hval hs hrd
  have h := hval k s a [t] [v] hs hrd 0 t v rfl rfl
  have ha : accAddr a 0 = a := by simp [accAddr]
  rw [ha] at h; exact h

/-- THE DESCENT STEP of every negative verdict: a non-initial value read at byte
`a` came from a WRITE STEP of the candidate, strictly earlier, whose message
carries that value at that byte and whose event timestamp is the one read. -/
theorem candReadWriter (c : Cand) (k t : Nat) (a : Int) (v : BitVec 8) :
    k ≤ c.cdTr.length → t ≠ 0 → logByte c.cdImg (cdLog c k) t a = some v →
    ∃ k' s m, k' < k ∧ c.cdTr[k']? = some s ∧ esWmsg s = some m ∧
      msgByte m a = some v ∧ evTs (candExec c) (ev_at k') = t := by
  intro hk ht hlb
  have hb := logByteBounded c.cdImg (cdLog c k) t a (by rw [hlb]; rfl)
  obtain ⟨k', s, m, hlt, hs, hm, hts⟩ := candTsWriter c k t hk (by omega) hb
  refine ⟨k', s, m, hlt, hs, hm, ?_, hts⟩
  rw [← candLogByteWr c k' s m k a hs hm (by omega), hts]; exact hlb

/-! # 5. POSITIVE verdicts

A positive verdict exhibits a CONCRETE candidate over `img0`, proves it
`srvwmoConsistent` by DISCHARGING THE AXIOMS DIRECTLY, and reads the outcome off
the trace.  The discharge is factored through `candPlainOk`: with no
`sr`-covering fence, no acquire-to-po-later edge, no release write and no
same-byte program order, the whole of `candAxiomaticOk` reduces to
`axAtomicity`. -/

/-! ### The vacuity kit -/

theorem candNoFenceOrd (c : Cand) :
    (∀ (k : Nat) (s : Estep), c.cdTr[k]? = some s → ∀ pr pw sw, s.esLb ≠ LFence pr pw true sw) →
    ∀ k1 k2 pr pw sw, ¬ fenceBetween (candExec c) k1 k2 pr pw true sw := by
  rintro hnf k1 k2 pr pw sw ⟨kf, sf, s1, s2, _, _, _, hsf, _, _, _, hlf⟩
  exact hnf kf sf hsf pr pw sw hlf

theorem candNoAqAcq (c : Cand) :
    (∀ (k : Nat) (s : Estep), c.cdTr[k]? = some s → lbIsR s.esLb = true → lbAq s.esLb = false) →
    ∀ e1 e2, ¬ acqPo (candExec c) e1 e2 := by
  rintro hnaq e1 e2 ⟨k1, k2, s1, s2, rfl, rfl, _, hs1, _, _, hr, haq⟩
  rw [hnaq k1 s1 hs1 hr] at haq; cases haq

/-- The AMO's discharger: an acquire whose hart takes no other step is in no
`acqPo` edge. -/
theorem candNoPairAcq (c : Cand) :
    (∀ (k1 k2 : Nat) (s1 s2 : Estep), c.cdTr[k1]? = some s1 → c.cdTr[k2]? = some s2 → k1 < k2 →
      s1.esAg ≠ s2.esAg) →
    ∀ e1 e2, ¬ acqPo (candExec c) e1 e2 := by
  rintro hnp e1 e2 ⟨k1, k2, s1, s2, rfl, rfl, hlt, hs1, hs2, hag, _⟩
  exact hnp k1 k2 s1 s2 hs1 hs2 hlt hag

theorem candNoOrd (c : Cand) :
    (∀ (k : Nat) (s : Estep), c.cdTr[k]? = some s → ∀ pr pw sw, s.esLb ≠ LFence pr pw true sw) →
    (∀ e1 e2, ¬ acqPo (candExec c) e1 e2) →
    ∀ e1 e2, ¬ ordPw (candExec c) e1 e2 ∧ ¬ ordPr (candExec c) e1 e2 := by
  intro hnf hnacq e1 e2
  refine ⟨?_, ?_⟩
  · rintro ⟨k1, k2, pr, sw, _, _, hfb⟩
    exact candNoFenceOrd c hnf _ _ _ _ _ hfb
  · rintro (⟨k1, k2, pw, sw, _, _, hfb⟩ | hacq)
    · exact candNoFenceOrd c hnf _ _ _ _ _ hfb
    · exact hnacq _ _ hacq

theorem candNoRlRelAcq (c : Cand) :
    (∀ (k : Nat) (s : Estep), c.cdTr[k]? = some s → lbRl s.esLb = false) →
    ∀ e1 e2, ¬ relAcqPo (candExec c) e1 e2 := by
  rintro hnrl e1 e2 ⟨k1, k2, s1, s2, rfl, rfl, _, hs1, _, _, _, hrl, _⟩
  rw [hnrl k1 s1 hs1] at hrl; cases hrl

theorem candNoRlRelOrd (c : Cand) :
    (∀ (k : Nat) (s : Estep), c.cdTr[k]? = some s → lbRl s.esLb = false) →
    ∀ e1 e2, ¬ relOrd (candExec c) e1 e2 := by
  rintro hnrl e1 e2 (hr | ⟨em, hr, _, _⟩)
  · exact candNoRlRelAcq c hnrl _ _ hr
  · exact candNoRlRelAcq c hnrl _ _ hr

theorem WeakSrvwmoLitmus.lbRdIsR (l : Lbl) (base : Int) (ts : List Nat) (vs : List (BitVec 8)) :
    lbRd l = some (base, ts, vs) → lbIsR l = true := by
  cases l <;> simp [lbRd, lbIsR]

/-- `axAtomicity` for free when no step both reads and writes. -/
theorem candRwDisjointAtomicity (c : Cand) :
    (∀ (k : Nat) (s : Estep), c.cdTr[k]? = some s → lbIsW s.esLb = false ∨ lbIsR s.esLb = false) →
    axAtomicity (candExec c) := by
  intro hrw kr a w0 w hW hrf0 _ _
  obtain ⟨_, k, t, v, hkeq, hr, _⟩ := hrf0
  injection hkeq with hkeq; subst hkeq
  obtain ⟨s, base, ts, vs, j, hs, hrd, _⟩ := hr
  obtain ⟨s', hs', hw'⟩ := hW
  rw [hs] at hs'; injection hs' with hs'; subst hs'
  rcases hrw kr s hs with hnw | hnr
  · rw [hw'] at hnw; cases hnw
  · rw [WeakSrvwmoLitmus.lbRdIsR _ _ _ _ hrd] at hnr; cases hnr

/-- Single-byte access inversion: which byte a candidate event touches. -/
theorem candWrBAt (c : Cand) (a : Int) (k : Nat) :
    wrB (candExec c) a (ev_at k) →
    ∃ s m, c.cdTr[k]? = some s ∧ esWmsg s = some m ∧ (msgByte m a).isSome := by
  intro hw
  rcases candWrBInv c a (ev_at k) hw with ⟨habs, _⟩ | ⟨k', s, m, heq, hs, hm, hb⟩
  · cases habs
  · injection heq with heq; subst heq; exact ⟨s, m, hs, hm, hb⟩

theorem candRdBAt (c : Cand) (a : Int) (k : Nat) :
    rdB (candExec c) a (ev_at k) →
    ∃ s base ts vs j, c.cdTr[k]? = some s ∧ lbRd s.esLb = some (base, ts, vs) ∧
      j < ts.length ∧ accAddr base j = a := by
  rintro ⟨k', t, v, heq, s, base, ts, vs, j, hs, hrd, hj, _, ha⟩
  injection heq with heq; subst heq
  exact ⟨s, base, ts, vs, j, hs, hrd, lookup_lt_Some hj, ha.symm⟩

/-- THE KIT: everything but `axAtomicity` and the four vacuity facts is free.
`ppoOp` collapses to its rule-14 arm, which is what §3's `obOpAcycW` admits. -/
theorem candPlainOk (c : Cand) :
    candShape c → candValues c →
    (∀ (k : Nat) (s : Estep), c.cdTr[k]? = some s → ∀ pr pw sw, s.esLb ≠ LFence pr pw true sw) →
    (∀ e1 e2, ¬ acqPo (candExec c) e1 e2) →
    (∀ (k : Nat) (s : Estep), c.cdTr[k]? = some s → lbRl s.esLb = false) →
    axAtomicity (candExec c) →
    (∀ a e1 e2, ¬ poLocB (candExec c) a e1 e2) →
    srvwmoConsistent c := by
  intro hsh hval hnf hnacq hnrl hatom hnpl
  have hnppo : ∀ o1 o2, ppoOp (candExec c) o1 o2 →
      po (candExec c) o1.2 o2.2 ∧ wrB (candExec c) o2.1 o2.2 := by
    rintro o1 o2 (⟨hpo, hw2⟩ | ⟨_, hpl⟩ | ⟨hord, _⟩ | ⟨hord, _, _⟩ | ⟨hrel, _⟩)
    · exact ⟨hpo, hw2⟩
    · exact absurd hpl (hnpl _ _ _)
    · exact absurd hord (candNoOrd c hnf hnacq _ _).1
    · exact absurd hord (candNoOrd c hnf hnacq _ _).2
    · exact absurd hrel (candNoRlRelAcq c hnrl _ _)
  refine ⟨hsh, hval, ⟨candRfTotal c hval, candRfFunctional c, candRfValue c hval, ?_, hatom, ?_,
    candNoThinAir c hval, candPoWwGmo c⟩, ?_, obOpAcycW c hsh hval hatom hnppo⟩
  · intro a e
    exact cohRelAcycTs c a hsh hval hatom (fun e1 e2 hpl => absurd hpl (hnpl a e1 e2)) e
  · intro e1 k2 s2 a w t _ hcase _
    obtain ⟨hpw, hpr⟩ := candNoOrd c hnf hnacq e1 (ev_at k2)
    rcases hcase with ⟨hord, _⟩ | ⟨hord, _⟩
    · exact absurd hord hpw
    · exact absurd hord hpr
  · intro e1 k2 s2 a w t _ hro _ _
    exact absurd hro (candNoRlRelOrd c hnrl e1 (ev_at k2))

/-! ### SB: both harts read 0 — ALLOWED (matches RVWMO and the machine)

Interleaving: both stores first, both loads read the era-initial image. -/

def sbP : Prog := [sbProg0, sbProg1]
def sbTr : List Estep :=
  [⟨0, LStore false ax [b1] .WCplain⟩,
   ⟨1, LStore false ay [b1] .WCplain⟩,
   ⟨0, LLoad false ay [0] [b0]⟩,
   ⟨1, LLoad false ax [0] [b0]⟩]
def sbCd : Cand := ⟨img0, sbTr⟩

theorem sbTrInv (k : Nat) (s : Estep) :
    sbCd.cdTr[k]? = some s →
    (k = 0 ∧ s = ⟨0, LStore false ax [b1] .WCplain⟩) ∨
    (k = 1 ∧ s = ⟨1, LStore false ay [b1] .WCplain⟩) ∨
    (k = 2 ∧ s = ⟨0, LLoad false ay [0] [b0]⟩) ∨
    (k = 3 ∧ s = ⟨1, LLoad false ax [0] [b0]⟩) := by
  intro hs
  simp only [sbCd, sbTr] at hs
  match k, hs with
  | 0, hs => simp only [List.getElem?_cons_zero, Option.some.injEq] at hs; exact .inl ⟨rfl, hs.symm⟩
  | 1, hs =>
    simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hs
    exact .inr (.inl ⟨rfl, hs.symm⟩)
  | 2, hs =>
    simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hs
    exact .inr (.inr (.inl ⟨rfl, hs.symm⟩))
  | 3, hs =>
    simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hs
    exact .inr (.inr (.inr ⟨rfl, hs.symm⟩))
  | k + 4, hs => simp at hs

theorem sbShape : candShape sbCd := by
  intro k s hs
  rcases sbTrInv k s hs with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> simp

theorem sbValues : candValues sbCd := by
  intro k s base ts vs hs hrd j t v hj hv
  rcases sbTrInv k s hs with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · simp [lbRd] at hrd
  · simp [lbRd] at hrd
  · simp only [lbRd, Option.some.injEq, Prod.mk.injEq] at hrd
    obtain ⟨rfl, rfl, rfl⟩ := hrd
    match j, hj, hv with
    | 0, hj, hv =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hj hv
      subst hj hv
      rw [logByte0, show accAddr ay 0 = ay by simp [accAddr]]; exact img0Y
    | j + 1, hj, _ => simp at hj
  · simp only [lbRd, Option.some.injEq, Prod.mk.injEq] at hrd
    obtain ⟨rfl, rfl, rfl⟩ := hrd
    match j, hj, hv with
    | 0, hj, hv =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hj hv
      subst hj hv
      rw [logByte0, show accAddr ax 0 = ax by simp [accAddr]]; exact img0X
    | j + 1, hj, _ => simp at hj

theorem sbNoPoloc (a : Int) (e1 e2 : Ev) : ¬ poLocB (candExec sbCd) a e1 e2 := by
  rintro ⟨⟨k1, k2, s1, s2, rfl, rfl, hlt, hs1, hs2, hag⟩, hacc1, hacc2⟩
  -- the byte an SB event accesses: ax at steps 0/3, ay at steps 1/2
  have hbyte : ∀ k a', accB (candExec sbCd) a' (ev_at k) →
      ((k = 0 ∨ k = 3) ∧ a' = ax) ∨ ((k = 1 ∨ k = 2) ∧ a' = ay) := by
    intro k a' hacc
    rcases hacc with hw | hr
    · obtain ⟨s', m, hs', hm, hb⟩ := candWrBAt _ _ _ hw
      rcases sbTrInv k s' hs' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        simp only [esWmsg, lbWr, lbCls, Option.some.injEq, reduceCtorEq] at hm
      · subst hm; exact .inl ⟨.inl rfl, WeakAxiomatic3.msgByteSingle _ _ _ _ _ hb⟩
      · subst hm; exact .inr ⟨.inl rfl, WeakAxiomatic3.msgByteSingle _ _ _ _ _ hb⟩
    · obtain ⟨s', base, ts, vs, j, hs', hrd, hj, ha⟩ := candRdBAt _ _ _ hr
      rcases sbTrInv k s' hs' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        simp only [lbRd, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at hrd
      · obtain ⟨rfl, rfl, rfl⟩ := hrd
        simp only [List.length_singleton, Nat.lt_one_iff] at hj; subst hj
        exact .inr ⟨.inr rfl, by rw [← ha]; simp [accAddr]⟩
      · obtain ⟨rfl, rfl, rfl⟩ := hrd
        simp only [List.length_singleton, Nat.lt_one_iff] at hj; subst hj
        exact .inl ⟨.inr rfl, by rw [← ha]; simp [accAddr]⟩
  rcases hbyte k1 a hacc1 with ⟨hk1 | hk1, ha1⟩ | ⟨hk1 | hk1, ha1⟩ <;>
    rcases hbyte k2 a hacc2 with ⟨hk2 | hk2, ha2⟩ | ⟨hk2 | hk2, ha2⟩ <;>
    subst hk1 hk2 <;> (try omega) <;>
    (rcases sbTrInv _ s1 hs1 with ⟨h1, rfl⟩ | ⟨h1, rfl⟩ | ⟨h1, rfl⟩ | ⟨h1, rfl⟩ <;>
     rcases sbTrInv _ s2 hs2 with ⟨h2, rfl⟩ | ⟨h2, rfl⟩ | ⟨h2, rfl⟩ | ⟨h2, rfl⟩ <;>
     first | omega | simp at hag)

theorem sbOk : srvwmoConsistent sbCd := by
  apply candPlainOk
  · exact sbShape
  · exact sbValues
  · intro k s hs pr pw sw
    rcases sbTrInv k s hs with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> simp
  · apply candNoAqAcq; intro k s hs _
    rcases sbTrInv k s hs with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> rfl
  · intro k s hs
    rcases sbTrInv k s hs with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> rfl
  · apply candRwDisjointAtomicity; intro k s hs
    rcases sbTrInv k s hs with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;>
      first | exact .inl rfl | exact .inr rfl
  · exact sbNoPoloc

theorem sbConf : conforms sbP sbCd := by
  intro k s hs
  rcases sbTrInv k s hs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨sbProg0, IStore ax b1, rfl, rfl, rfl⟩
  · exact ⟨sbProg1, IStore ay b1, rfl, rfl, rfl⟩
  · exact ⟨sbProg0, ILoad rg1 ay false, rfl, rfl, 0, b0, rfl⟩
  · exact ⟨sbProg1, ILoad rg2 ax false, rfl, rfl, 0, b0, rfl⟩

def sbOut00 (c : Cand) : Prop := outc c 0 1 ay b0 ∧ outc c 1 1 ax b0

/-- THE VERDICT: the definition admits the 0/0 outcome. -/
theorem sb00Allowed :
    ∃ c, c.cdImg = img0 ∧ conforms sbP c ∧ sbOut00 c ∧ srvwmoConsistent c :=
  ⟨sbCd, rfl, sbConf,
    ⟨⟨2, ⟨0, LLoad false ay [0] [b0]⟩, 0, rfl, rfl, rfl, rfl⟩,
     ⟨3, ⟨1, LLoad false ax [0] [b0]⟩, 0, rfl, rfl, rfl, rfl⟩⟩, sbOk⟩

/-! ### MP with no fences — the weak outcome is ALLOWED

Hart 0 stores `ax` then `ay`; hart 1 loads `ay` (sees the flag, `b1`) then
loads `ax` (sees the STALE data, `b0`).  Nothing orders hart 1's two relaxed
loads.  RVWMO allows this and so does the operational machine. -/

def mpnP : Prog := [mpWNofence, mpRNofence]
def mpnTr : List Estep :=
  [⟨0, LStore false ax [b1] .WCplain⟩,
   ⟨0, LStore false ay [b1] .WCplain⟩,
   ⟨1, LLoad false ay [2] [b1]⟩,
   ⟨1, LLoad false ax [0] [b0]⟩]
def mpnCd : Cand := ⟨img0, mpnTr⟩

theorem mpnTrInv (k : Nat) (s : Estep) :
    mpnCd.cdTr[k]? = some s →
    (k = 0 ∧ s = ⟨0, LStore false ax [b1] .WCplain⟩) ∨
    (k = 1 ∧ s = ⟨0, LStore false ay [b1] .WCplain⟩) ∨
    (k = 2 ∧ s = ⟨1, LLoad false ay [2] [b1]⟩) ∨
    (k = 3 ∧ s = ⟨1, LLoad false ax [0] [b0]⟩) := by
  intro hs
  simp only [mpnCd, mpnTr] at hs
  match k, hs with
  | 0, hs => simp only [List.getElem?_cons_zero, Option.some.injEq] at hs; exact .inl ⟨rfl, hs.symm⟩
  | 1, hs =>
    simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hs
    exact .inr (.inl ⟨rfl, hs.symm⟩)
  | 2, hs =>
    simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hs
    exact .inr (.inr (.inl ⟨rfl, hs.symm⟩))
  | 3, hs =>
    simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hs
    exact .inr (.inr (.inr ⟨rfl, hs.symm⟩))
  | k + 4, hs => simp at hs

theorem mpnShape : candShape mpnCd := by
  intro k s hs
  rcases mpnTrInv k s hs with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> simp

/-- The flag read takes t = 2 (the `ay` store's own message); the data read
takes t = 0, i.e. the era-initial image. -/
theorem mpnValues : candValues mpnCd := by
  intro k s base ts vs hs hrd j t v hj hv
  rcases mpnTrInv k s hs with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · simp [lbRd] at hrd
  · simp [lbRd] at hrd
  · simp only [lbRd, Option.some.injEq, Prod.mk.injEq] at hrd
    obtain ⟨rfl, rfl, rfl⟩ := hrd
    match j, hj, hv with
    | 0, hj, hv =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hj hv
      subst hj hv
      decide
    | j + 1, hj, _ => simp at hj
  · simp only [lbRd, Option.some.injEq, Prod.mk.injEq] at hrd
    obtain ⟨rfl, rfl, rfl⟩ := hrd
    match j, hj, hv with
    | 0, hj, hv =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hj hv
      subst hj hv
      rw [logByte0, show accAddr ax 0 = ax by simp [accAddr]]; exact img0X
    | j + 1, hj, _ => simp at hj

theorem mpnNoPoloc (a : Int) (e1 e2 : Ev) : ¬ poLocB (candExec mpnCd) a e1 e2 := by
  rintro ⟨⟨k1, k2, s1, s2, rfl, rfl, hlt, hs1, hs2, hag⟩, hacc1, hacc2⟩
  -- ax at steps 0/3, ay at steps 1/2 — the two same-agent po pairs (0,1) and
  -- (2,3) are at DIFFERENT bytes, the two same-byte pairs on different agents
  have hbyte : ∀ k a', accB (candExec mpnCd) a' (ev_at k) →
      ((k = 0 ∨ k = 3) ∧ a' = ax) ∨ ((k = 1 ∨ k = 2) ∧ a' = ay) := by
    intro k a' hacc
    rcases hacc with hw | hr
    · obtain ⟨s', m, hs', hm, hb⟩ := candWrBAt _ _ _ hw
      rcases mpnTrInv k s' hs' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        simp only [esWmsg, lbWr, lbCls, Option.some.injEq, reduceCtorEq] at hm
      · subst hm; exact .inl ⟨.inl rfl, WeakAxiomatic3.msgByteSingle _ _ _ _ _ hb⟩
      · subst hm; exact .inr ⟨.inl rfl, WeakAxiomatic3.msgByteSingle _ _ _ _ _ hb⟩
    · obtain ⟨s', base, ts, vs, j, hs', hrd, hj, ha⟩ := candRdBAt _ _ _ hr
      rcases mpnTrInv k s' hs' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        simp only [lbRd, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at hrd
      · obtain ⟨rfl, rfl, rfl⟩ := hrd
        simp only [List.length_singleton, Nat.lt_one_iff] at hj; subst hj
        exact .inr ⟨.inr rfl, by rw [← ha]; simp [accAddr]⟩
      · obtain ⟨rfl, rfl, rfl⟩ := hrd
        simp only [List.length_singleton, Nat.lt_one_iff] at hj; subst hj
        exact .inl ⟨.inr rfl, by rw [← ha]; simp [accAddr]⟩
  rcases hbyte k1 a hacc1 with ⟨hk1 | hk1, ha1⟩ | ⟨hk1 | hk1, ha1⟩ <;>
    rcases hbyte k2 a hacc2 with ⟨hk2 | hk2, ha2⟩ | ⟨hk2 | hk2, ha2⟩ <;>
    subst hk1 hk2 <;> (try omega) <;>
    (rcases mpnTrInv _ s1 hs1 with ⟨h1, rfl⟩ | ⟨h1, rfl⟩ | ⟨h1, rfl⟩ | ⟨h1, rfl⟩ <;>
     rcases mpnTrInv _ s2 hs2 with ⟨h2, rfl⟩ | ⟨h2, rfl⟩ | ⟨h2, rfl⟩ | ⟨h2, rfl⟩ <;>
     first | omega | simp at hag)

theorem mpnOk : srvwmoConsistent mpnCd := by
  apply candPlainOk
  · exact mpnShape
  · exact mpnValues
  · intro k s hs pr pw sw
    rcases mpnTrInv k s hs with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> simp
  · apply candNoAqAcq; intro k s hs _
    rcases mpnTrInv k s hs with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> rfl
  · intro k s hs
    rcases mpnTrInv k s hs with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> rfl
  · apply candRwDisjointAtomicity; intro k s hs
    rcases mpnTrInv k s hs with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;>
      first | exact .inl rfl | exact .inr rfl
  · exact mpnNoPoloc

theorem mpnConf : conforms mpnP mpnCd := by
  intro k s hs
  rcases mpnTrInv k s hs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨mpWNofence, IStore ax b1, rfl, rfl, rfl⟩
  · exact ⟨mpWNofence, IStore ay b1, rfl, rfl, rfl⟩
  · exact ⟨mpRNofence, ILoad rg1 ay false, rfl, rfl, 2, b1, rfl⟩
  · exact ⟨mpRNofence, ILoad rg2 ax false, rfl, rfl, 0, b0, rfl⟩

def mpnOut (c : Cand) : Prop := outc c 1 0 ay b1 ∧ outc c 1 1 ax b0

/-- THE VERDICT: flag seen, data stale — sRVWMO-consistent. -/
theorem mpnWeakAllowed :
    ∃ c, c.cdImg = img0 ∧ conforms mpnP c ∧ mpnOut c ∧ srvwmoConsistent c :=
  ⟨mpnCd, rfl, mpnConf,
    ⟨⟨2, ⟨1, LLoad false ay [2] [b1]⟩, 2, rfl, rfl, rfl, rfl⟩,
     ⟨3, ⟨1, LLoad false ax [0] [b0]⟩, 0, rfl, rfl, rfl, rfl⟩⟩, mpnOk⟩

/-! ### MP with ONLY the writer fence (fence rw,w) — still ALLOWED

The writer fence fixes nothing on the READER side: hart 1's two loads are
plain and unordered.  RVWMO requires fences on BOTH sides for MP; the model
reproduces that, and the operational machine allows the same run. -/

def mpwP : Prog := [mpWFenced, mpRNofence]
def mpwTr : List Estep :=
  [⟨0, LStore false ax [b1] .WCplain⟩,
   ⟨0, LFence true true false true⟩,
   ⟨0, LStore false ay [b1] .WCplain⟩,
   ⟨1, LLoad false ay [2] [b1]⟩,
   ⟨1, LLoad false ax [0] [b0]⟩]
def mpwCd : Cand := ⟨img0, mpwTr⟩

theorem mpwTrInv (k : Nat) (s : Estep) :
    mpwCd.cdTr[k]? = some s →
    (k = 0 ∧ s = ⟨0, LStore false ax [b1] .WCplain⟩) ∨
    (k = 1 ∧ s = ⟨0, LFence true true false true⟩) ∨
    (k = 2 ∧ s = ⟨0, LStore false ay [b1] .WCplain⟩) ∨
    (k = 3 ∧ s = ⟨1, LLoad false ay [2] [b1]⟩) ∨
    (k = 4 ∧ s = ⟨1, LLoad false ax [0] [b0]⟩) := by
  intro hs
  simp only [mpwCd, mpwTr] at hs
  match k, hs with
  | 0, hs => simp only [List.getElem?_cons_zero, Option.some.injEq] at hs; exact .inl ⟨rfl, hs.symm⟩
  | 1, hs =>
    simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hs
    exact .inr (.inl ⟨rfl, hs.symm⟩)
  | 2, hs =>
    simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hs
    exact .inr (.inr (.inl ⟨rfl, hs.symm⟩))
  | 3, hs =>
    simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hs
    exact .inr (.inr (.inr (.inl ⟨rfl, hs.symm⟩)))
  | 4, hs =>
    simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hs
    exact .inr (.inr (.inr (.inr ⟨rfl, hs.symm⟩)))
  | k + 5, hs => simp at hs

theorem mpwShape : candShape mpwCd := by
  intro k s hs
  rcases mpwTrInv k s hs with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> simp

/-- The fence appends no message, so the `ay` store — agent-0 position 2 —
still has timestamp 2, which is what the flag load reads. -/
theorem mpwValues : candValues mpwCd := by
  intro k s base ts vs hs hrd j t v hj hv
  rcases mpwTrInv k s hs with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · simp [lbRd] at hrd
  · simp [lbRd] at hrd
  · simp [lbRd] at hrd
  · simp only [lbRd, Option.some.injEq, Prod.mk.injEq] at hrd
    obtain ⟨rfl, rfl, rfl⟩ := hrd
    match j, hj, hv with
    | 0, hj, hv =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hj hv
      subst hj hv
      decide
    | j + 1, hj, _ => simp at hj
  · simp only [lbRd, Option.some.injEq, Prod.mk.injEq] at hrd
    obtain ⟨rfl, rfl, rfl⟩ := hrd
    match j, hj, hv with
    | 0, hj, hv =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hj hv
      subst hj hv
      rw [logByte0, show accAddr ax 0 = ax by simp [accAddr]]; exact img0X
    | j + 1, hj, _ => simp at hj

theorem mpwNoPoloc (a : Int) (e1 e2 : Ev) : ¬ poLocB (candExec mpwCd) a e1 e2 := by
  rintro ⟨⟨k1, k2, s1, s2, rfl, rfl, hlt, hs1, hs2, hag⟩, hacc1, hacc2⟩
  -- ax at steps 0/4, ay at steps 2/3; the fence at step 1 accesses no byte
  have hbyte : ∀ k a', accB (candExec mpwCd) a' (ev_at k) →
      ((k = 0 ∨ k = 4) ∧ a' = ax) ∨ ((k = 2 ∨ k = 3) ∧ a' = ay) := by
    intro k a' hacc
    rcases hacc with hw | hr
    · obtain ⟨s', m, hs', hm, hb⟩ := candWrBAt _ _ _ hw
      rcases mpwTrInv k s' hs' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        simp only [esWmsg, lbWr, lbCls, Option.some.injEq, reduceCtorEq] at hm
      · subst hm; exact .inl ⟨.inl rfl, WeakAxiomatic3.msgByteSingle _ _ _ _ _ hb⟩
      · subst hm; exact .inr ⟨.inl rfl, WeakAxiomatic3.msgByteSingle _ _ _ _ _ hb⟩
    · obtain ⟨s', base, ts, vs, j, hs', hrd, hj, ha⟩ := candRdBAt _ _ _ hr
      rcases mpwTrInv k s' hs' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        simp only [lbRd, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at hrd
      · obtain ⟨rfl, rfl, rfl⟩ := hrd
        simp only [List.length_singleton, Nat.lt_one_iff] at hj; subst hj
        exact .inr ⟨.inr rfl, by rw [← ha]; simp [accAddr]⟩
      · obtain ⟨rfl, rfl, rfl⟩ := hrd
        simp only [List.length_singleton, Nat.lt_one_iff] at hj; subst hj
        exact .inl ⟨.inr rfl, by rw [← ha]; simp [accAddr]⟩
  rcases hbyte k1 a hacc1 with ⟨hk1 | hk1, ha1⟩ | ⟨hk1 | hk1, ha1⟩ <;>
    rcases hbyte k2 a hacc2 with ⟨hk2 | hk2, ha2⟩ | ⟨hk2 | hk2, ha2⟩ <;>
    subst hk1 hk2 <;> (try omega) <;>
    (rcases mpwTrInv _ s1 hs1 with ⟨h1, rfl⟩ | ⟨h1, rfl⟩ | ⟨h1, rfl⟩ | ⟨h1, rfl⟩ | ⟨h1, rfl⟩ <;>
     rcases mpwTrInv _ s2 hs2 with ⟨h2, rfl⟩ | ⟨h2, rfl⟩ | ⟨h2, rfl⟩ | ⟨h2, rfl⟩ | ⟨h2, rfl⟩ <;>
     first | omega | simp at hag)

theorem mpwOk : srvwmoConsistent mpwCd := by
  apply candPlainOk
  · exact mpwShape
  · exact mpwValues
  · -- the writer fence is `rw,w`: its successor-READ bit is false, so it is
    -- not an `sr`-covering fence and `ord` stays vacuous
    intro k s hs pr pw sw
    rcases mpwTrInv k s hs with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> simp
  · apply candNoAqAcq; intro k s hs _
    rcases mpwTrInv k s hs with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> rfl
  · intro k s hs
    rcases mpwTrInv k s hs with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> rfl
  · apply candRwDisjointAtomicity; intro k s hs
    rcases mpwTrInv k s hs with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;>
      first | exact .inr rfl | exact .inl rfl
  · exact mpwNoPoloc

theorem mpwConf : conforms mpwP mpwCd := by
  intro k s hs
  rcases mpwTrInv k s hs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨mpWFenced, IStore ax b1, rfl, rfl, rfl⟩
  · exact ⟨mpWFenced, FENCE_RW_W, rfl, rfl, rfl⟩
  · exact ⟨mpWFenced, IStore ay b1, rfl, rfl, rfl⟩
  · exact ⟨mpRNofence, ILoad rg1 ay false, rfl, rfl, 2, b1, rfl⟩
  · exact ⟨mpRNofence, ILoad rg2 ax false, rfl, rfl, 0, b0, rfl⟩

def mpwOut (c : Cand) : Prop := outc c 1 0 ay b1 ∧ outc c 1 1 ax b0

/-- THE VERDICT: the release-side fence alone does NOT forbid the MP outcome. -/
theorem mpwWeakAllowed :
    ∃ c, c.cdImg = img0 ∧ conforms mpwP c ∧ mpwOut c ∧ srvwmoConsistent c :=
  ⟨mpwCd, rfl, mpwConf,
    ⟨⟨3, ⟨1, LLoad false ay [2] [b1]⟩, 2, rfl, rfl, rfl, rfl⟩,
     ⟨4, ⟨1, LLoad false ax [0] [b0]⟩, 0, rfl, rfl, rfl, rfl⟩⟩, mpwOk⟩

/-! ### AMO — amoswap.aq reads the globally-latest value

Hart 0 stores `b1` to `ax`; hart 1 then runs `amoswap.aq` on `ax`, reading
`b1` (timestamp 1) and writing `b2`.  The only candidate in the suite whose
step both READS and WRITES a byte, so `axAtomicity` is discharged directly
from the two timestamps (read half t = 1, own write t = 2). -/

def amoP : Prog := [[IStore ax b1], [IAmoSwapAq rg1 ax b2]]
def amoTr : List Estep :=
  [⟨0, LStore false ax [b1] .WCplain⟩,
   ⟨1, LRmw true false ax [1] [b1] [b2] .WCexcl⟩]
def amoCd : Cand := ⟨img0, amoTr⟩

theorem amoTrInv (k : Nat) (s : Estep) :
    amoCd.cdTr[k]? = some s →
    (k = 0 ∧ s = ⟨0, LStore false ax [b1] .WCplain⟩) ∨
    (k = 1 ∧ s = ⟨1, LRmw true false ax [1] [b1] [b2] .WCexcl⟩) := by
  intro hs
  simp only [amoCd, amoTr] at hs
  match k, hs with
  | 0, hs => simp only [List.getElem?_cons_zero, Option.some.injEq] at hs; exact .inl ⟨rfl, hs.symm⟩
  | 1, hs =>
    simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hs
    exact .inr ⟨rfl, hs.symm⟩
  | k + 2, hs => simp at hs

theorem amoShape : candShape amoCd := by
  intro k s hs
  rcases amoTrInv k s hs with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> simp

theorem amoValues : candValues amoCd := by
  intro k s base ts vs hs hrd j t v hj hv
  rcases amoTrInv k s hs with ⟨_, rfl⟩ | ⟨rfl, rfl⟩
  · simp [lbRd] at hrd
  · simp only [lbRd, Option.some.injEq, Prod.mk.injEq] at hrd
    obtain ⟨rfl, rfl, rfl⟩ := hrd
    match j, hj, hv with
    | 0, hj, hv =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hj hv
      subst hj hv
      decide
    | j + 1, hj, _ => simp at hj

/-- The two steps belong to DIFFERENT agents, so this candidate has no
program order at all. -/
theorem amoNoPo (e1 e2 : Ev) : ¬ po (candExec amoCd) e1 e2 := by
  rintro ⟨k1, k2, s1, s2, rfl, rfl, hlt, hs1, hs2, hag⟩
  rcases amoTrInv k1 s1 hs1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    rcases amoTrInv k2 s2 hs2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    first | omega | simp at hag

theorem amoNoPoloc (a : Int) (e1 e2 : Ev) : ¬ poLocB (candExec amoCd) a e1 e2 :=
  fun h => amoNoPo _ _ h.1

/-- THE one non-templated obligation: no write of `ax` falls between the RMW's
read half (timestamp 1) and its write half (timestamp 2). -/
theorem amoAtomicity : axAtomicity (candExec amoCd) := by
  intro kr a w0 w _ hrf0 _ hgt hlt
  obtain ⟨_, k, t, v, hkeq, hr, hts0⟩ := hrf0
  injection hkeq with hkeq; subst hkeq
  obtain ⟨s, base, ts, vs, j, hs, hrd, hj, _, _⟩ := hr
  rcases amoTrInv kr s hs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · simp [lbRd] at hrd
  · simp only [lbRd, Option.some.injEq, Prod.mk.injEq] at hrd
    obtain ⟨rfl, rfl, rfl⟩ := hrd
    match j, hj with
    | 0, hj =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
      subst hj
      -- the read half took t = 1; the RMW's own event timestamp computes to 2
      have h2 : evTs (candExec amoCd) (ev_at 1) = 2 := by
        rw [candEvTs amoCd 1 (by decide)]; rfl
      omega
    | j + 1, hj => simp at hj

theorem amoOk : srvwmoConsistent amoCd := by
  apply candPlainOk
  · exact amoShape
  · exact amoValues
  · intro k s hs pr pw sw
    rcases amoTrInv k s hs with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> simp
  · apply candNoPairAcq; intro k1 k2 s1 s2 hs1 hs2 hlt
    rcases amoTrInv k1 s1 hs1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases amoTrInv k2 s2 hs2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      first | omega | simp
  · intro k s hs
    rcases amoTrInv k s hs with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> rfl
  · exact amoAtomicity
  · exact amoNoPoloc

theorem amoConf : conforms amoP amoCd := by
  intro k s hs
  rcases amoTrInv k s hs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨[IStore ax b1], IStore ax b1, rfl, rfl, rfl⟩
  · exact ⟨[IAmoSwapAq rg1 ax b2], IAmoSwapAq rg1 ax b2, rfl, rfl, 1, b1, rfl⟩

def amoOut (c : Cand) : Prop := outc c 1 0 ax b1

/-- THE VERDICT: the acquire AMO reads the store's value — allowed, with the
fused-RMW arm of the model (and `axAtomicity`) genuinely exercised. -/
theorem amoLatestAllowed :
    ∃ c, c.cdImg = img0 ∧ conforms amoP c ∧ amoOut c ∧ srvwmoConsistent c :=
  ⟨amoCd, rfl, amoConf, ⟨1, ⟨1, LRmw true false ax [1] [b1] [b2] .WCexcl⟩, 1, rfl, rfl, rfl, rfl⟩,
    amoOk⟩

/-! # 6. NEGATIVE verdicts

A negative verdict quantifies over EVERY candidate: no conformant candidate
over `img0` with the outcome is sRVWMO-consistent; through `srvwmoOfWf` that
covers the machine as well.  The engine is §4's descent: a non-initial value
read names its writer STEP, conformance names the writer's INSTRUCTION, and
§1's `agPos` arithmetic names the po-earlier steps of the same hart. -/

theorem outcWriter (c : Cand) (i j : Nat) (a : Int) (v : BitVec 8) :
    candValues c → outc c i j a v → c.cdImg a ≠ some v →
    ∃ k s t k' s' m,
      c.cdTr[k]? = some s ∧ s.esAg = i ∧ agPos c.cdTr i k = j ∧
      lbRd s.esLb = some (a, [t], [v]) ∧
      k' < k ∧ c.cdTr[k']? = some s' ∧ esWmsg s' = some m ∧
      msgByte m a = some v ∧ evTs (candExec c) (ev_at k') = t := by
  rintro hval ⟨k, s, t, hs, hag, hpos, hrd⟩ hni
  have hlb := candReadLog c k s a t v hval hs hrd
  have ht : t ≠ 0 := by
    rintro rfl; rw [logByte0] at hlb; exact hni hlb
  have hk := lookup_lt_Some hs
  obtain ⟨k', s', m, hlt, hs', hm, hb, hts⟩ := candReadWriter c k t a v (by omega) ht hlb
  exact ⟨k, s, t, k', s', m, hs, hag, hpos, hrd, hlt, hs', hm, hb, hts⟩

theorem outcInitial (c : Cand) (i j : Nat) (a : Int) (v : BitVec 8) :
    candValues c → outc c i j a v →
    (∀ (k' : Nat) (s' : Estep) (m : Wmsg), c.cdTr[k']? = some s' → esWmsg s' = some m →
      msgByte m a ≠ some v) →
    ∃ k s, c.cdTr[k]? = some s ∧ s.esAg = i ∧ agPos c.cdTr i k = j ∧
      lbRd s.esLb = some (a, [0], [v]) ∧ c.cdImg a = some v := by
  rintro hval ⟨k, s, t, hs, hag, hpos, hrd⟩ hno
  have hlb := candReadLog c k s a t v hval hs hrd
  have hk := lookup_lt_Some hs
  by_cases ht : t = 0
  · subst ht; rw [logByte0] at hlb
    exact ⟨k, s, hs, hag, hpos, hrd, hlb⟩
  · exfalso
    obtain ⟨k', s', m, _, hs', hm, hb, _⟩ := candReadWriter c k t a v (by omega) ht hlb
    exact hno k' s' m hs' hm hb

/-- Lean-only: the write message a step conformant to an instruction carries
(a store's or an AMO's; loads and fences carry none). -/
theorem instrLblWmsg (ins : Instr) (s : Estep) (m : Wmsg) :
    instrLbl ins s.esLb → esWmsg s = some m →
    (∃ a v, ins = IStore a v ∧ m = ⟨a, [v], some s.esAg, .WCplain⟩) ∨
    (∃ r a v, ins = IAmoSwapAq r a v ∧ m = ⟨a, [v], some s.esAg, .WCexcl⟩) := by
  obtain ⟨ag, l⟩ := s
  intro hil hm
  cases ins with
  | ILoad r a aq =>
    obtain ⟨t, v, hl⟩ := hil
    simp only at hl; subst hl
    simp [esWmsg, lbWr] at hm
  | IStore a v =>
    simp only [instrLbl] at hil; subst hil
    simp only [esWmsg, lbWr, lbCls, Option.some.injEq] at hm
    exact .inl ⟨a, v, rfl, hm.symm⟩
  | IFence pr pw sr sw =>
    simp only [instrLbl] at hil; subst hil
    simp [esWmsg, lbWr] at hm
  | IAmoSwapAq r a v =>
    obtain ⟨t, vv, hl⟩ := hil
    simp only at hl; subst hl
    simp only [esWmsg, lbWr, lbCls, Option.some.injEq] at hm
    exact .inr ⟨r, a, v, rfl, hm.symm⟩

/-! ### LB — THE HEADLINE: forbidden, and forbidden by the LOAD-VALUE axiom
alone.

RVWMO ALLOWS this outcome; sRVWMO forbids it, and the refutation never consults
an ordering axiom: `candValues` — reads take their value from the log PREFIX —
already makes the four steps' trace positions cyclic.  DIVERGENCE (1) of §9. -/

def lbP : Prog :=
  [[ILoad rg1 ax false, IStore ay b1], [ILoad rg2 ay false, IStore ax b1]]
def lbOut (c : Cand) : Prop := outc c 0 0 ax b1 ∧ outc c 1 0 ay b1

/-- Which steps of an `lbP`-conformant candidate write, and what. -/
theorem lbWmsgInv (c : Cand) (k : Nat) (s : Estep) (m : Wmsg) :
    conforms lbP c → c.cdTr[k]? = some s → esWmsg s = some m →
    (s.esAg = 0 ∧ agPos c.cdTr 0 k = 1 ∧ m = ⟨ay, [b1], some 0, .WCplain⟩) ∨
    (s.esAg = 1 ∧ agPos c.cdTr 1 k = 1 ∧ m = ⟨ax, [b1], some 1, .WCplain⟩) := by
  intro hconf hs hm
  obtain ⟨p, ins, hp, hins, hil⟩ := hconf k s hs
  obtain ⟨ag, l⟩ := s
  rcases instrLblWmsg ins ⟨ag, l⟩ m hil hm with ⟨a, v, rfl, rfl⟩ | ⟨r, a, v, rfl, rfl⟩ <;>
    simp only at hp hins ⊢ <;>
    generalize hpos : agPos c.cdTr ag k = n at hins <;>
    rcases ag with _ | _ | ag <;>
    simp only [lbP, List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil,
      Option.some.injEq, reduceCtorEq] at hp <;> subst hp <;>
    rcases n with _ | _ | _ | n <;>
    simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil,
      Option.some.injEq, reduceCtorEq, Instr.IStore.injEq] at hins <;>
    obtain ⟨rfl, rfl⟩ := hins
  · exact .inl ⟨rfl, hpos, rfl⟩
  · exact .inr ⟨rfl, hpos, rfl⟩

theorem lbValuesForbidden (c : Cand) :
    c.cdImg = img0 → conforms lbP c → lbOut c → ¬ candValues c := by
  rintro himg hconf ⟨hout0, hout1⟩ hval
  -- hart 0's read of x = 1 and its writer
  obtain ⟨krx, srx, tx, kwx, swx, mx, hsrx, hagrx, hposrx, _, hltx, hswx, hmx, hbx, _⟩ :=
    outcWriter c 0 0 ax b1 hval hout0 (by rw [himg, img0X]; intro h; exact b0NeB1 (Option.some.inj h))
  -- hart 1's read of y = 1 and its writer
  obtain ⟨kry, sry, ty, kwy, swy, my, hsry, hagry, hposry, _, hlty, hswy, hmy, hby, _⟩ :=
    outcWriter c 1 0 ay b1 hval hout1 (by rw [himg, img0Y]; intro h; exact b0NeB1 (Option.some.inj h))
  -- the writer of x is hart 1's SECOND instruction
  rcases lbWmsgInv c kwx swx mx hconf hswx hmx with ⟨_, _, rfl⟩ | ⟨hagwx, hposwx, _⟩
  · have := WeakAxiomatic3.msgByteSingle _ _ _ _ _ (by rw [hbx]; rfl :
      (msgByte ⟨ay, [b1], some 0, .WCplain⟩ ax).isSome)
    omega
  -- the writer of y is hart 0's SECOND instruction
  rcases lbWmsgInv c kwy swy my hconf hswy hmy with ⟨hagwy, hposwy, _⟩ | ⟨_, _, rfl⟩
  rotate_left
  · have := WeakAxiomatic3.msgByteSingle _ _ _ _ _ (by rw [hby]; rfl :
      (msgByte ⟨ax, [b1], some 1, .WCplain⟩ ay).isSome)
    omega
  -- descend from each store to its hart's first instruction — the reads
  obtain ⟨k1, s1, hk1, hs1, hag1, hpos1⟩ := agPosPrev c.cdTr 1 kwx 0 hposwx
  obtain ⟨k0, s0, hk0, hs0, hag0, hpos0⟩ := agPosPrev c.cdTr 0 kwy 0 hposwy
  -- ... and identify them with the outcome's read steps
  have e1 := agPosInj c.cdTr 1 k1 kry s1 sry hs1 hag1 hsry hagry (by omega)
  have e0 := agPosInj c.cdTr 0 k0 krx s0 srx hs0 hag0 hsrx hagrx (by omega)
  -- krx < kwy < kry < kwx < krx
  omega

theorem lbForbiddenModel (c : Cand) :
    c.cdImg = img0 → conforms lbP c → lbOut c → ¬ srvwmoConsistent c := by
  rintro himg hconf hout ⟨_, hval, _⟩
  exact lbValuesForbidden c himg hconf hout hval

theorem lbForbiddenMachine (c : Cand) :
    c.cdImg = img0 → conforms lbP c → lbOut c → ¬ execWf (candExec c) := by
  intro himg hconf hout hwf
  exact lbForbiddenModel c himg hconf hout (srvwmoOfWf c hwf)

/-! ### The shared kit for the remaining negatives -/

/-- The three litmus bytes are pairwise distinct, at `Option` level. -/
theorem bs01 : some b0 ≠ some b1 := fun h => b0NeB1 (Option.some.inj h)
theorem bs02 : some b0 ≠ some b2 := fun h => b0NeB2 (Option.some.inj h)
theorem bs10 : some b1 ≠ some b0 := fun h => b0NeB1 (Option.some.inj h).symm
theorem bs12 : some b1 ≠ some b2 := fun h => b1NeB2 (Option.some.inj h)
theorem bs21 : some b2 ≠ some b1 := fun h => b1NeB2 (Option.some.inj h).symm

/-- The single-byte messages this file's programs append. -/
theorem mbx1X : msgByte ⟨ax, [b1], some 0, .WCplain⟩ ax = some b1 := by
  rw [WeakLitmus.msgByteSingle]; decide
theorem mby1X : msgByte ⟨ay, [b1], some 0, .WCplain⟩ ax = none := by
  rw [WeakLitmus.msgByteSingle]; decide
theorem mbx2X : msgByte ⟨ax, [b2], some 0, .WCplain⟩ ax = some b2 := by
  rw [WeakLitmus.msgByteSingle]; decide

/-- Two steps of DIFFERENT agents are different events. -/
theorem evAtNe (c : Cand) (k1 k2 : Nat) (s1 s2 : Estep) (i j : Nat) :
    c.cdTr[k1]? = some s1 → c.cdTr[k2]? = some s2 →
    s1.esAg = i → s2.esAg = j → i ≠ j → ev_at k1 ≠ ev_at k2 := by
  intro hs1 hs2 ha1 ha2 hij heq
  injection heq with hk; subst hk
  rw [hs2] at hs1; injection hs1 with hs1; subst hs1
  exact hij (ha1.symm.trans ha2)

/-! ### Pinning a step's LABEL from conformance

Read in the direction the verdicts need — position and agent KNOWN,
instruction read off the program — `conforms` pins the label. -/

theorem confPin (P : Prog) (c : Cand) (k : Nat) (s : Estep) (i j : Nat) (ins : Instr) :
    conforms P c → c.cdTr[k]? = some s → s.esAg = i → agPos c.cdTr i k = j →
    (P[i]?.bind (fun p => p[j]?)) = some ins → instrLbl ins s.esLb := by
  intro hconf hs hag hpos hpi
  obtain ⟨p, ins', hp, hins, hil⟩ := hconf k s hs
  rw [hag] at hp hins; rw [hpos] at hins
  rw [hp] at hpi
  change p[j]? = some ins at hpi
  rw [hins] at hpi; injection hpi with hpi; subst hpi; exact hil

theorem confStore (P : Prog) (c : Cand) (k : Nat) (s : Estep) (i j : Nat) (a : Int)
    (v : BitVec 8) :
    conforms P c → c.cdTr[k]? = some s → s.esAg = i → agPos c.cdTr i k = j →
    (P[i]?.bind (fun p => p[j]?)) = some (IStore a v) →
    s.esLb = LStore false a [v] .WCplain ∧ esWmsg s = some ⟨a, [v], some i, .WCplain⟩ := by
  intro hconf hs hag hpos hpi
  have hil : s.esLb = LStore false a [v] .WCplain :=
    confPin P c k s i j (IStore a v) hconf hs hag hpos hpi
  refine ⟨hil, ?_⟩
  subst hag
  unfold esWmsg; rw [hil]; rfl

theorem confFence (P : Prog) (c : Cand) (k : Nat) (s : Estep) (i j : Nat) (pr pw sr sw : Bool) :
    conforms P c → c.cdTr[k]? = some s → s.esAg = i → agPos c.cdTr i k = j →
    (P[i]?.bind (fun p => p[j]?)) = some (IFence pr pw sr sw) →
    s.esLb = LFence pr pw sr sw :=
  fun hconf hs hag hpos hpi => confPin P c k s i j (IFence pr pw sr sw) hconf hs hag hpos hpi

theorem confLoad (P : Prog) (c : Cand) (k : Nat) (s : Estep) (i j : Nat) (r : Nat) (a : Int)
    (aq : Bool) :
    conforms P c → c.cdTr[k]? = some s → s.esAg = i → agPos c.cdTr i k = j →
    (P[i]?.bind (fun p => p[j]?)) = some (ILoad r a aq) →
    ∃ t v, s.esLb = LLoad aq a [t] [v] :=
  fun hconf hs hag hpos hpi => confPin P c k s i j (ILoad r a aq) hconf hs hag hpos hpi

/-! ### MP with both fences — forbidden, by `axOrd`

    hart 0                     hart 1
      x := 1                     r1 := y     (reads 1)
      fence rw,w                 fence r,rw
      y := 1                     r2 := x     (reads 0 — FORBIDDEN)

The reader's fence covers `r,rw`, so `ordPr` holds between its two loads and
`axOrd` applies to the `fr` edge out of the stale data read.  MATCHES RVWMO. -/

def mpfP : Prog :=
  [[IStore ax b1, FENCE_RW_W, IStore ay b1],
   [ILoad rg1 ay false, FENCE_R_RW, ILoad rg2 ax false]]
def mpfOut (c : Cand) : Prop := outc c 1 0 ay b1 ∧ outc c 1 2 ax b0

/-- The only writing steps are hart 0's two stores. -/
theorem mpfWmsgInv (c : Cand) (k : Nat) (s : Estep) (m : Wmsg) :
    conforms mpfP c → c.cdTr[k]? = some s → esWmsg s = some m →
    (s.esAg = 0 ∧ agPos c.cdTr 0 k = 0 ∧ m = ⟨ax, [b1], some 0, .WCplain⟩) ∨
    (s.esAg = 0 ∧ agPos c.cdTr 0 k = 2 ∧ m = ⟨ay, [b1], some 0, .WCplain⟩) := by
  intro hconf hs hm
  obtain ⟨p, ins, hp, hins, hil⟩ := hconf k s hs
  obtain ⟨ag, l⟩ := s
  rcases instrLblWmsg ins ⟨ag, l⟩ m hil hm with ⟨a, v, rfl, rfl⟩ | ⟨r, a, v, rfl, rfl⟩ <;>
    simp only at hp hins ⊢ <;>
    generalize hpos : agPos c.cdTr ag k = n at hins <;>
    rcases ag with _ | _ | ag <;>
    simp only [mpfP, List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil,
      Option.some.injEq, reduceCtorEq] at hp <;> subst hp <;>
    rcases n with _ | _ | _ | n <;>
    simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil,
      Option.some.injEq, reduceCtorEq, Instr.IStore.injEq] at hins <;>
    obtain ⟨rfl, rfl⟩ := hins
  · exact .inl ⟨rfl, hpos, rfl⟩
  · exact .inr ⟨rfl, hpos, rfl⟩

theorem mpfForbiddenModel (c : Cand) :
    c.cdImg = img0 → conforms mpfP c → mpfOut c → ¬ srvwmoConsistent c := by
  rintro himg hconf ⟨houty, houtx⟩
    ⟨_, hval, ⟨_, _, _, _, _, hord, _, _⟩, _, _⟩
  -- the reader's flag read, and the step that wrote the flag
  obtain ⟨kry, sry, ty, kwy, swy, my, hsry, hagry, _, hrdy, _, hswy, hmy, hby, htsy⟩ :=
    outcWriter c 1 0 ay b1 hval houty (by rw [himg, img0Y]; exact bs01)
  -- it is hart 0's THIRD instruction — the store to y
  rcases mpfWmsgInv c kwy swy my hconf hswy hmy with ⟨_, _, rfl⟩ | ⟨hagwy, hposwy, _⟩
  · have := WeakAxiomatic3.msgByteSingle _ _ _ _ _ (by rw [hby]; rfl :
      (msgByte ⟨ax, [b1], some 0, .WCplain⟩ ay).isSome)
    omega
  -- the reader's data read is INITIAL: no instruction writes b0 at x
  obtain ⟨krx, srx, hsrx, hagrx, hposrx, hrdx, himgx⟩ :=
    outcInitial c 1 2 ax b0 hval houtx (by
      intro k' s' m' hs' hm' hb'
      rcases mpfWmsgInv c k' s' m' hconf hs' hm' with ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩
      · rw [mbx1X] at hb'; exact bs10 hb'
      · rw [mby1X] at hb'; cases hb')
  -- WRITER SIDE: descend y-store ↦ fence ↦ x-store, then trace-order the two
  -- timestamps
  obtain ⟨kwf, _, hltwf, _, _, hposwf⟩ := agPosPrev c.cdTr 0 kwy 1 hposwy
  obtain ⟨kwx, swx, hltwx, hswx, hagwx, hposwx⟩ := agPosPrev c.cdTr 0 kwf 0 hposwf
  obtain ⟨_, hmwx⟩ := confStore mpfP c kwx swx 0 0 ax b1 hconf hswx hagwx hposwx rfl
  have hlenry := lookup_lt_Some hsry
  have htsx := candTsMono c kwx kwy swx _ hswx hmwx (by omega) (by omega)
  -- READER SIDE: the fence sits between the two loads
  obtain ⟨kf, sf, hltf, hsf, hagf, hposf⟩ := agPosPrev c.cdTr 1 krx 1 hposrx
  have hlf := confFence mpfP c kf sf 1 1 true false true true hconf hsf hagf hposf rfl
  obtain ⟨kr0, sr0, hltr0, hsr0, hagr0, hposr0⟩ := agPosPrev c.cdTr 1 kf 0 hposf
  have hkr0 := agPosInj c.cdTr 1 kr0 kry sr0 sry hsr0 hagr0 hsry hagry (by omega)
  have hfb : fenceBetween (candExec c) kry krx true false true true :=
    ⟨kf, sf, sry, srx, by omega, by omega, hsry, hsf, hsrx, by rw [hagry, hagf],
      by rw [hagf, hagrx], hlf⟩
  have hordpr : ordPr (candExec c) (ev_at kry) (ev_at krx) :=
    .inl ⟨kry, krx, false, true, rfl, rfl, hfb⟩
  -- the flag read publishes ty: its rf edge is EXTERNAL
  have hrfy : rfB (candExec c) ay (ev_at kwy) (ev_at kry) :=
    ⟨candWrB c kwy swy my ay hswy hmy (by rw [hby]; rfl), kry, ty, b1, rfl,
      candReadsAt1 c kry sry ay ty b1 hsry hrdy, htsy⟩
  have hpubr : pubR (candExec c) (ev_at kry) ty :=
    ⟨kry, sry, ay, b1, rfl, hsry, candReadsAt1 c kry sry ay ty b1 hsry hrdy,
      .inr ⟨ev_at kwy, hrfy, swy, hswy, by rw [hagwy, hagry]; omega⟩⟩
  -- the stale data read is fr-before the data store
  have hfr : frB (candExec c) ax (ev_at krx) (ev_at kwx) :=
    ⟨⟨ev_init, ⟨candWrBInit c ax (by rw [himgx]; rfl), krx, 0, b0, rfl,
        candReadsAt1 c krx srx ax 0 b0 hsrx hrdx, rfl⟩,
      candWrBInit c ax (by rw [himgx]; rfl),
      candWrB c kwx swx _ ax hswx hmwx (by rw [mbx1X]; rfl), Nat.succ_pos _⟩,
     evAtNe c krx kwx srx swx 1 0 hsrx hswx hagrx hagwx (by omega)⟩
  have hlt := hord (ev_at kry) krx srx ax (ev_at kwx) ty hsrx (.inr ⟨hordpr, hpubr⟩) hfr
  omega

theorem mpfForbiddenMachine (c : Cand) :
    c.cdImg = img0 → conforms mpfP c → mpfOut c → ¬ execWf (candExec c) := by
  intro himg hconf hout hwf
  exact mpfForbiddenModel c himg hconf hout (srvwmoOfWf c hwf)

/-! ### MP with a writer fence and an ACQUIRE load — forbidden, by `axOrd`

    hart 0                     hart 1
      x := 1                     r1 := y.aq  (reads 1)
      fence rw,w                 r2 := x     (reads 0 — FORBIDDEN)
      y := 1

Same proof, with the reader's ordering edge coming from `acqPo` instead of a
fence.  MATCHES RVWMO. -/

def mpaP : Prog :=
  [[IStore ax b1, FENCE_RW_W, IStore ay b1],
   [ILoad rg1 ay true, ILoad rg2 ax false]]
def mpaOut (c : Cand) : Prop := outc c 1 0 ay b1 ∧ outc c 1 1 ax b0

theorem mpaWmsgInv (c : Cand) (k : Nat) (s : Estep) (m : Wmsg) :
    conforms mpaP c → c.cdTr[k]? = some s → esWmsg s = some m →
    (s.esAg = 0 ∧ agPos c.cdTr 0 k = 0 ∧ m = ⟨ax, [b1], some 0, .WCplain⟩) ∨
    (s.esAg = 0 ∧ agPos c.cdTr 0 k = 2 ∧ m = ⟨ay, [b1], some 0, .WCplain⟩) := by
  intro hconf hs hm
  obtain ⟨p, ins, hp, hins, hil⟩ := hconf k s hs
  obtain ⟨ag, l⟩ := s
  rcases instrLblWmsg ins ⟨ag, l⟩ m hil hm with ⟨a, v, rfl, rfl⟩ | ⟨r, a, v, rfl, rfl⟩ <;>
    simp only at hp hins ⊢ <;>
    generalize hpos : agPos c.cdTr ag k = n at hins <;>
    rcases ag with _ | _ | ag <;>
    simp only [mpaP, List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil,
      Option.some.injEq, reduceCtorEq] at hp <;> subst hp <;>
    rcases n with _ | _ | _ | n <;>
    simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil,
      Option.some.injEq, reduceCtorEq, Instr.IStore.injEq] at hins <;>
    obtain ⟨rfl, rfl⟩ := hins
  · exact .inl ⟨rfl, hpos, rfl⟩
  · exact .inr ⟨rfl, hpos, rfl⟩

theorem mpaForbiddenModel (c : Cand) :
    c.cdImg = img0 → conforms mpaP c → mpaOut c → ¬ srvwmoConsistent c := by
  rintro himg hconf ⟨houty, houtx⟩
    ⟨_, hval, ⟨_, _, _, _, _, hord, _, _⟩, _, _⟩
  obtain ⟨kry, sry, ty, kwy, swy, my, hsry, hagry, hposry, hrdy, _, hswy, hmy, hby, htsy⟩ :=
    outcWriter c 1 0 ay b1 hval houty (by rw [himg, img0Y]; exact bs01)
  rcases mpaWmsgInv c kwy swy my hconf hswy hmy with ⟨_, _, rfl⟩ | ⟨_, hposwy, _⟩
  · have := WeakAxiomatic3.msgByteSingle _ _ _ _ _ (by rw [hby]; rfl :
      (msgByte ⟨ax, [b1], some 0, .WCplain⟩ ay).isSome)
    omega
  obtain ⟨krx, srx, hsrx, hagrx, hposrx, hrdx, himgx⟩ :=
    outcInitial c 1 1 ax b0 hval houtx (by
      intro k' s' m' hs' hm' hb'
      rcases mpaWmsgInv c k' s' m' hconf hs' hm' with ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩
      · rw [mbx1X] at hb'; exact bs10 hb'
      · rw [mby1X] at hb'; cases hb')
  -- WRITER SIDE — as for MP with both fences
  obtain ⟨kwf, _, hltwf, _, _, hposwf⟩ := agPosPrev c.cdTr 0 kwy 1 hposwy
  obtain ⟨kwx, swx, hltwx, hswx, hagwx, hposwx⟩ := agPosPrev c.cdTr 0 kwf 0 hposwf
  obtain ⟨_, hmwx⟩ := confStore mpaP c kwx swx 0 0 ax b1 hconf hswx hagwx hposwx rfl
  have hlenry := lookup_lt_Some hsry
  have htsx := candTsMono c kwx kwy swx _ hswx hmwx (by omega) (by omega)
  -- READER SIDE: the acquire load is po-before the data load
  obtain ⟨kr0, sr0, hltr0, hsr0, hagr0, hposr0⟩ := agPosPrev c.cdTr 1 krx 0 hposrx
  have hkr0 := agPosInj c.cdTr 1 kr0 kry sr0 sry hsr0 hagr0 hsry hagry (by omega)
  obtain ⟨t0, v0, hlry⟩ :=
    confLoad mpaP c kry sry 1 0 rg1 ay true hconf hsry hagry hposry rfl
  have hacq : acqPo (candExec c) (ev_at kry) (ev_at krx) :=
    ⟨kry, krx, sry, srx, rfl, rfl, by omega, hsry, hsrx, by rw [hagry, hagrx],
      by rw [hlry]; rfl, by rw [hlry]; rfl⟩
  have hordpr : ordPr (candExec c) (ev_at kry) (ev_at krx) := .inr hacq
  have hpubr : pubR (candExec c) (ev_at kry) ty :=
    ⟨kry, sry, ay, b1, rfl, hsry, candReadsAt1 c kry sry ay ty b1 hsry hrdy,
      .inl (by rw [hlry]; rfl)⟩
  have hfr : frB (candExec c) ax (ev_at krx) (ev_at kwx) :=
    ⟨⟨ev_init, ⟨candWrBInit c ax (by rw [himgx]; rfl), krx, 0, b0, rfl,
        candReadsAt1 c krx srx ax 0 b0 hsrx hrdx, rfl⟩,
      candWrBInit c ax (by rw [himgx]; rfl),
      candWrB c kwx swx _ ax hswx hmwx (by rw [mbx1X]; rfl), Nat.succ_pos _⟩,
     evAtNe c krx kwx srx swx 1 0 hsrx hswx hagrx hagwx (by omega)⟩
  have hlt := hord (ev_at kry) krx srx ax (ev_at kwx) ty hsrx (.inr ⟨hordpr, hpubr⟩) hfr
  omega

theorem mpaForbiddenMachine (c : Cand) :
    c.cdImg = img0 → conforms mpaP c → mpaOut c → ¬ execWf (candExec c) := by
  intro himg hconf hout hwf
  exact mpaForbiddenModel c himg hconf hout (srvwmoOfWf c hwf)

/-! ### MP with the READER fence only — forbidden, and this DIVERGES

    hart 0                     hart 1
      x := 1                     r1 := y     (reads 1)
      y := 1                     fence r,rw
                                 r2 := x     (reads 0 — FORBIDDEN HERE)

RVWMO ALLOWS this outcome; sRVWMO FORBIDS it — DIVERGENCE (2) of §9.  The
culprit is the promise-free strengthening `axPoWwGmo` (ppo rule 14 in the
candidate presentation): a candidate's trace order IS its global memory order.
Mechanically the proof is MP-with-both-fences' with ONE descent on the writer
side — the writer's fence was never used. -/

def mpgP : Prog :=
  [[IStore ax b1, IStore ay b1],
   [ILoad rg1 ay false, FENCE_R_RW, ILoad rg2 ax false]]
def mpgOut (c : Cand) : Prop := outc c 1 0 ay b1 ∧ outc c 1 2 ax b0

theorem mpgWmsgInv (c : Cand) (k : Nat) (s : Estep) (m : Wmsg) :
    conforms mpgP c → c.cdTr[k]? = some s → esWmsg s = some m →
    (s.esAg = 0 ∧ agPos c.cdTr 0 k = 0 ∧ m = ⟨ax, [b1], some 0, .WCplain⟩) ∨
    (s.esAg = 0 ∧ agPos c.cdTr 0 k = 1 ∧ m = ⟨ay, [b1], some 0, .WCplain⟩) := by
  intro hconf hs hm
  obtain ⟨p, ins, hp, hins, hil⟩ := hconf k s hs
  obtain ⟨ag, l⟩ := s
  rcases instrLblWmsg ins ⟨ag, l⟩ m hil hm with ⟨a, v, rfl, rfl⟩ | ⟨r, a, v, rfl, rfl⟩ <;>
    simp only at hp hins ⊢ <;>
    generalize hpos : agPos c.cdTr ag k = n at hins <;>
    rcases ag with _ | _ | ag <;>
    simp only [mpgP, List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil,
      Option.some.injEq, reduceCtorEq] at hp <;> subst hp <;>
    rcases n with _ | _ | _ | n <;>
    simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil,
      Option.some.injEq, reduceCtorEq, Instr.IStore.injEq] at hins <;>
    obtain ⟨rfl, rfl⟩ := hins
  · exact .inl ⟨rfl, hpos, rfl⟩
  · exact .inr ⟨rfl, hpos, rfl⟩

theorem mpgForbiddenModel (c : Cand) :
    c.cdImg = img0 → conforms mpgP c → mpgOut c → ¬ srvwmoConsistent c := by
  rintro himg hconf ⟨houty, houtx⟩
    ⟨_, hval, ⟨_, _, _, _, _, hord, _, _⟩, _, _⟩
  obtain ⟨kry, sry, ty, kwy, swy, my, hsry, hagry, _, hrdy, _, hswy, hmy, hby, htsy⟩ :=
    outcWriter c 1 0 ay b1 hval houty (by rw [himg, img0Y]; exact bs01)
  rcases mpgWmsgInv c kwy swy my hconf hswy hmy with ⟨_, _, rfl⟩ | ⟨hagwy, hposwy, _⟩
  · have := WeakAxiomatic3.msgByteSingle _ _ _ _ _ (by rw [hby]; rfl :
      (msgByte ⟨ax, [b1], some 0, .WCplain⟩ ay).isSome)
    omega
  obtain ⟨krx, srx, hsrx, hagrx, hposrx, hrdx, himgx⟩ :=
    outcInitial c 1 2 ax b0 hval houtx (by
      intro k' s' m' hs' hm' hb'
      rcases mpgWmsgInv c k' s' m' hconf hs' hm' with ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩
      · rw [mbx1X] at hb'; exact bs10 hb'
      · rw [mby1X] at hb'; cases hb')
  -- WRITER SIDE: ONE descent — no fence to step over
  obtain ⟨kwx, swx, hltwx, hswx, hagwx, hposwx⟩ := agPosPrev c.cdTr 0 kwy 0 hposwy
  obtain ⟨_, hmwx⟩ := confStore mpgP c kwx swx 0 0 ax b1 hconf hswx hagwx hposwx rfl
  have hlenry := lookup_lt_Some hsry
  have htsx := candTsMono c kwx kwy swx _ hswx hmwx (by omega) (by omega)
  -- READER SIDE — as for MP with both fences
  obtain ⟨kf, sf, hltf, hsf, hagf, hposf⟩ := agPosPrev c.cdTr 1 krx 1 hposrx
  have hlf := confFence mpgP c kf sf 1 1 true false true true hconf hsf hagf hposf rfl
  obtain ⟨kr0, sr0, hltr0, hsr0, hagr0, hposr0⟩ := agPosPrev c.cdTr 1 kf 0 hposf
  have hkr0 := agPosInj c.cdTr 1 kr0 kry sr0 sry hsr0 hagr0 hsry hagry (by omega)
  have hfb : fenceBetween (candExec c) kry krx true false true true :=
    ⟨kf, sf, sry, srx, by omega, by omega, hsry, hsf, hsrx, by rw [hagry, hagf],
      by rw [hagf, hagrx], hlf⟩
  have hordpr : ordPr (candExec c) (ev_at kry) (ev_at krx) :=
    .inl ⟨kry, krx, false, true, rfl, rfl, hfb⟩
  have hrfy : rfB (candExec c) ay (ev_at kwy) (ev_at kry) :=
    ⟨candWrB c kwy swy my ay hswy hmy (by rw [hby]; rfl), kry, ty, b1, rfl,
      candReadsAt1 c kry sry ay ty b1 hsry hrdy, htsy⟩
  have hpubr : pubR (candExec c) (ev_at kry) ty :=
    ⟨kry, sry, ay, b1, rfl, hsry, candReadsAt1 c kry sry ay ty b1 hsry hrdy,
      .inr ⟨ev_at kwy, hrfy, swy, hswy, by rw [hagwy, hagry]; omega⟩⟩
  have hfr : frB (candExec c) ax (ev_at krx) (ev_at kwx) :=
    ⟨⟨ev_init, ⟨candWrBInit c ax (by rw [himgx]; rfl), krx, 0, b0, rfl,
        candReadsAt1 c krx srx ax 0 b0 hsrx hrdx, rfl⟩,
      candWrBInit c ax (by rw [himgx]; rfl),
      candWrB c kwx swx _ ax hswx hmwx (by rw [mbx1X]; rfl), Nat.succ_pos _⟩,
     evAtNe c krx kwx srx swx 1 0 hsrx hswx hagrx hagwx (by omega)⟩
  have hlt := hord (ev_at kry) krx srx ax (ev_at kwx) ty hsrx (.inr ⟨hordpr, hpubr⟩) hfr
  omega

theorem mpgForbiddenMachine (c : Cand) :
    c.cdImg = img0 → conforms mpgP c → mpgOut c → ¬ execWf (candExec c) := by
  intro himg hconf hout hwf
  exact mpgForbiddenModel c himg hconf hout (srvwmoOfWf c hwf)

/-! ### CoRR — forbidden, by `axCoherence`

    hart 0                     hart 1
      x := 1                     r1 := x     (reads 2)
      x := 2                     r2 := x     (reads 1 — FORBIDDEN)

No ordering axiom is needed: per-byte coherence forbids the cycle
`r1 --po-loc--> r2 --fr--> (x:=2) --rf--> r1`.  MATCHES RVWMO. -/

def corrP : Prog :=
  [[IStore ax b1, IStore ax b2],
   [ILoad rg1 ax false, ILoad rg2 ax false]]
def corrOut (c : Cand) : Prop := outc c 1 0 ax b2 ∧ outc c 1 1 ax b1

theorem corrWmsgInv (c : Cand) (k : Nat) (s : Estep) (m : Wmsg) :
    conforms corrP c → c.cdTr[k]? = some s → esWmsg s = some m →
    (s.esAg = 0 ∧ agPos c.cdTr 0 k = 0 ∧ m = ⟨ax, [b1], some 0, .WCplain⟩) ∨
    (s.esAg = 0 ∧ agPos c.cdTr 0 k = 1 ∧ m = ⟨ax, [b2], some 0, .WCplain⟩) := by
  intro hconf hs hm
  obtain ⟨p, ins, hp, hins, hil⟩ := hconf k s hs
  obtain ⟨ag, l⟩ := s
  rcases instrLblWmsg ins ⟨ag, l⟩ m hil hm with ⟨a, v, rfl, rfl⟩ | ⟨r, a, v, rfl, rfl⟩ <;>
    simp only at hp hins ⊢ <;>
    generalize hpos : agPos c.cdTr ag k = n at hins <;>
    rcases ag with _ | _ | ag <;>
    simp only [corrP, List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil,
      Option.some.injEq, reduceCtorEq] at hp <;> subst hp <;>
    rcases n with _ | _ | _ | n <;>
    simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil,
      Option.some.injEq, reduceCtorEq, Instr.IStore.injEq] at hins <;>
    obtain ⟨rfl, rfl⟩ := hins
  · exact .inl ⟨rfl, hpos, rfl⟩
  · exact .inr ⟨rfl, hpos, rfl⟩

theorem corrForbiddenModel (c : Cand) :
    c.cdImg = img0 → conforms corrP c → corrOut c → ¬ srvwmoConsistent c := by
  rintro himg hconf ⟨hout2, hout1⟩
    ⟨_, hval, ⟨_, _, _, hcoh, _, _, _, _⟩, _, _⟩
  -- the read of 2 comes from the SECOND store
  obtain ⟨kr2, sr2, t2, kw2, sw2, m2, hsr2, hagr2, _, hrd2, hlt2, hsw2, hmw2, hb2, hts2⟩ :=
    outcWriter c 1 0 ax b2 hval hout2 (by rw [himg, img0X]; exact bs02)
  rcases corrWmsgInv c kw2 sw2 m2 hconf hsw2 hmw2 with ⟨_, _, rfl⟩ | ⟨hagw2, hposw2, rfl⟩
  · rw [mbx1X] at hb2; exact bs12 hb2
  -- the read of 1 comes from the FIRST store
  obtain ⟨kr1, sr1, t1, kw1, sw1, m1, hsr1, hagr1, hposr1, hrd1, _, hsw1, hmw1, hb1, hts1⟩ :=
    outcWriter c 1 1 ax b1 hval hout1 (by rw [himg, img0X]; exact bs01)
  rcases corrWmsgInv c kw1 sw1 m1 hconf hsw1 hmw1 with ⟨hagw1, _, rfl⟩ | ⟨_, _, rfl⟩
  rotate_left
  · rw [mbx2X] at hb1; exact bs21 hb1
  -- the reader's two loads, and the writer's two stores, in trace order
  obtain ⟨kr0, sr0, hltr0, hsr0, hagr0, hposr0⟩ := agPosPrev c.cdTr 1 kr1 0 hposr1
  have hkr0 := agPosInj c.cdTr 1 kr0 kr2 sr0 sr2 hsr0 hagr0 hsr2 hagr2 (by omega)
  obtain ⟨kw0, sw0, hltw0, hsw0, hagw0, hposw0⟩ := agPosPrev c.cdTr 0 kw2 0 hposw2
  have hkw0 := agPosInj c.cdTr 0 kw0 kw1 sw0 sw1 hsw0 hagw0 hsw1 hagw1 (by omega)
  have hlen2 := lookup_lt_Some hsr2
  have htslt := candTsMono c kw1 kw2 sw1 _ hsw1 hmw1 (by omega) (by omega)
  -- the three edges of the coherence cycle
  have hpl : poLocB (candExec c) ax (ev_at kr2) (ev_at kr1) :=
    ⟨⟨kr2, kr1, sr2, sr1, rfl, rfl, by omega, hsr2, hsr1, by rw [hagr2, hagr1]⟩,
     .inr ⟨kr2, t2, b2, rfl, candReadsAt1 c kr2 sr2 ax t2 b2 hsr2 hrd2⟩,
     .inr ⟨kr1, t1, b1, rfl, candReadsAt1 c kr1 sr1 ax t1 b1 hsr1 hrd1⟩⟩
  have hfr : frB (candExec c) ax (ev_at kr1) (ev_at kw2) :=
    ⟨⟨ev_at kw1,
        ⟨candWrB c kw1 sw1 _ ax hsw1 hmw1 (by rw [hb1]; rfl), kr1, t1, b1, rfl,
          candReadsAt1 c kr1 sr1 ax t1 b1 hsr1 hrd1, hts1⟩,
        candWrB c kw1 sw1 _ ax hsw1 hmw1 (by rw [hb1]; rfl),
        candWrB c kw2 sw2 _ ax hsw2 hmw2 (by rw [hb2]; rfl), htslt⟩,
     evAtNe c kr1 kw2 sr1 sw2 1 0 hsr1 hsw2 hagr1 hagw2 (by omega)⟩
  have hrf : rfB (candExec c) ax (ev_at kw2) (ev_at kr2) :=
    ⟨candWrB c kw2 sw2 _ ax hsw2 hmw2 (by rw [hb2]; rfl), kr2, t2, b2, rfl,
      candReadsAt1 c kr2 sr2 ax t2 b2 hsr2 hrd2, hts2⟩
  have e1 : cohRel (candExec c) ax (ev_at kr2) (ev_at kr1) := Or.inl hpl
  have e2 : cohRel (candExec c) ax (ev_at kr1) (ev_at kw2) := Or.inr (Or.inr (Or.inr hfr))
  have e3 : cohRel (candExec c) ax (ev_at kw2) (ev_at kr2) := Or.inr (Or.inl hrf)
  exact hcoh ax (ev_at kr2) (tc_l e1 (tc_l e2 (tc_once e3)))

theorem corrForbiddenMachine (c : Cand) :
    c.cdImg = img0 → conforms corrP c → corrOut c → ¬ execWf (candExec c) := by
  intro himg hconf hout hwf
  exact corrForbiddenModel c himg hconf hout (srvwmoOfWf c hwf)

/-! # 7. The two precedents this file does NOT redo

Two verdict-grade facts about the model were already machine-checked in
`WeakAxiomatic3` §13, as the counterexamples that PINNED the definition; they
are cited rather than restated:

- RELEASE→ACQUIRE (ppo rule 7): `ceRlTrueInconsistent` is the NEGATIVE verdict
  (the stale acquire read is sRVWMO-inconsistent — the `axRelOrd`/`relAcqPo`
  arm is exactly what kills it), and `ceRlStaleReachable` is the POSITIVE twin
  with the `.rl` bit dropped.  Together they are rule 7's non-vacuity witness.

- OWN-STORE FORWARDING: `ceFwd` — a plain load reading the agent's own
  po-earlier store "early" — is machine-reachable (`ceFwdReachable`) and
  refuted the old `cand_pub_clean` premise (`ceFwdNotPubClean`); post-A3(ii)
  it is simply a consistent candidate, i.e. the positive forwarding verdict. -/

/-! # 8. What is NOT done, with prices

- IRIW (operationally forbidden: `WeakLitmus.iriwForbidden`, both readers
  fenced `rw,rw`).  The axiomatic refutation needs comparing the two
  independent writes' positions in the trace (gmo totality on writes, free
  here), then the two readers' `axOrd` instances point in opposite
  directions.  No new machinery.  ~150 lines.

- SB-FENCED, both directions.  Its fences are `rw,rw`, i.e. `sr = true`, so
  `candPlainOk` does NOT apply: the POSITIVE ((0,1) reachable —
  `WeakLitmus.sbFenced01Reachable`) needs a real `axOrd` discharge for a
  concrete candidate (~60 lines); the NEGATIVE ((0,0) forbidden) is the MP
  template symmetrized (~120 lines).

- The ATOMICITY negative: an AMO whose read half takes a NON-latest timestamp
  is inconsistent (`axAtomicity` kills it — the model twin of
  `WeakLitmus.amoLatestUnique`).  The §5 AMO candidate plus one interposed
  store.  ~50 lines.

- SPLIT-EXCLUSIVE shapes (`LExLoad`/`LExStore`, dangling reservations) are not
  in this file's alphabet at all: the axiomatic model keeps exclusives FUSED,
  so the split tier's litmus story belongs to the R-track, not here. -/

/-! # 9. THE VERDICT TABLE

Every verdict below is against `srvwmoConsistent` — the DEFINITION; the last
column is `WeakLitmus`'s operational verdict on the same program, and every
row agrees with it, as T1/T2 say it must.

    shape                   outcome          sRVWMO     RVWMO      here / operational (WeakLitmus)
    -------------------------------------------------------------------------------------------
    SB, no fences           r1=0 ∧ r2=0      allowed    allowed    sb00Allowed / sb00Reachable
    MP, no fences           flag=1 ∧ data=0  allowed    allowed    mpnWeakAllowed / mpNofenceWeakReachable
    MP, writer fence only   flag=1 ∧ data=0  allowed    allowed    mpwWeakAllowed / mpWfenceWeakReachable
    AMO (amoswap.aq)        reads the latest allowed    allowed    amoLatestAllowed / amoSwapReachable
    MP, both fences         flag=1 ∧ data=0  FORBIDDEN  forbidden  mpfForbiddenModel / mpFencedForbidden
    MP, wr fence + acquire  flag=1 ∧ data=0  FORBIDDEN  forbidden  mpaForbiddenModel / mpAcquireForbidden
    MP, READER fence only   flag=1 ∧ data=0  FORBIDDEN  ALLOWED    mpgForbiddenModel / mpReaderFenceOnlyForbidden
    CoRR                    r1=new ∧ r2=old  FORBIDDEN  forbidden  corrForbiddenModel / corrForbidden
    LB                      r1=1 ∧ r2=1      FORBIDDEN  ALLOWED    lbForbiddenModel / lbForbidden

THE TWO DELIBERATE DIVERGENCES from RVWMO, both bought by ppo rule 14 (stores
are never early):

(1) LB is FORBIDDEN — and the refutation (`lbValuesForbidden`) never consults
    an ordering axiom: the LOAD-VALUE axiom alone makes the outcome's four
    trace positions cyclic.  In the candidate presentation no-thin-air is
    definitional (`candNoThinAir` is free for every value-consistent
    candidate).  This is the design doc's "LB must be unobservable",
    mechanized.

(2) MP with ONLY a reader fence is FORBIDDEN — rule 14 puts the writer's two
    stores in gmo order with no fence between them (the candidate's trace
    order IS gmo on writes: `axPoWwGmo`), so the reader-side ordering alone
    completes the forbidden cycle; RVWMO allows the stale read here.  NOTE
    what this does to the design doc §3 corollary (b) slogan ("LB
    unobservable, everything else matches riscv.cat"): rule 14 narrows the
    hardware class by MORE than LB — reader-fence-only MP is a second
    observable difference, exactly the in-order-store-visibility
    strengthening the design's §1 declares.  This suite is the honest record
    of both. -/

end Weak
