/-
Weak: **the completeness residue: VIEW DOMINATION** (W4 SLICE 3 of the M6
robustness effort).

Rocq: `iris/WeakAxiomatic3.v` @ xxvzwolszwmp (1cc222280).

The Rocq header, in substance.  THIS FILE'S RESULTS: (1) THE COMPLETENESS
THEOREM, WITH NO SIDE CONDITION (`promiseFreeCompleteClean`): every candidate
satisfying `candAxiomaticOk` is machine-reachable — every stale read allowed,
a strict generalisation of slice 2's `scCandReachable`; the proof is the
view-domination induction slice 2 §9(1) asked for, one conjunct per view
component.  (2) THE NAMED TOP LEVEL (§14): `srvwmoConsistent` and
`srvwmoRealizable`, with the ppo residue table of the settled axiomatization.

NO PREMISE, AND WHY.  (a) THE RELEASE/ACQUIRE SEAM is CLOSED BY STRENGTHENING
THE MODEL: RVWMO ppo rule 7 (`relAcqPo`) is `ppoOp`'s fifth arm and
`axRelOrd` a conjunct of `candAxiomaticOk`; §13's witness is now
axiomatically INCONSISTENT (`ceRlTrueInconsistent`).  (b) THE FORWARD-BANK
SEAM is CLOSED BY WEAKENING THE MACHINE (D-7, 2026-08-17): the bank holds
PARM's dependency-free view `0`, so a forwarded plain read contributes
nothing; §8's `candReadSplit` turns that into a theorem (every byte a read
takes is EITHER forwarded, contributing `0`, OR contributes its own timestamp,
which is then a `pubR` PUBLICATION).

THE SHAPE OF THE INDUCTION: domination is stated as the CONCLUSION shape
`frdomB E i k a n` ("every future step of agent `i` whose `fr` edge at byte
`a` points at a write `w` has `n < evTs w`"), derived per component from the
LOCAL axioms (`axCoherence` for `coh`, `axOrd`/`axRelOrd` for `wVrNew` via
`ordDom`).  `fenceBetween` and `acqPo` are MONOTONE IN THE TARGET, so a view
delivered through any chain of fences is delivered by a SINGLE `ord` edge —
which is why `ob`-acyclicity is not needed (FINDING:
`promiseFreeCompleteLocal`).

**Deviations from Rocq.**

1. NAMES: as `Weak/WeakAxiomatic.lean` deviation 1; primes kept
   (`load_fold_coh'` ↦ `loadFoldCoh'`); `ce_rl` ↦ `ceRl`, `ce_rl_tr` ↦
   `ceRlTr`, `ce_fwd` ↦ `ceFwd`, `ce_rl_notW2` ↦ `ceRlNotW2`, `ce_fwd_wr0` ↦
   `ceFwdWr0`, `frdom_b` ↦ `frdomB`, `ord_dom` ↦ `ordDom`, `invw`/`inv`/
   `rdom`/`rsrc`/`wsrc`/`relsrc`/`bankdom` kept.
2. SECTION VARIABLES.  Rocq's `Section candidate` (`Context c Hval Hrft
   Hcohax Hordax Hrelax`, later `Hshape Hatom`) and the `ce_rl*`/`ce_fwd`
   sections (`Context rl v`) become explicit leading arguments of each
   declaration, in section order, carrying exactly the hypotheses its Rocq
   proof uses (the Rocq signature after the section closes).  E.g.
   `touchFrdom c hrft hcohax ...`, `candReadSplit c hval hrft hcohax ...`,
   `completeClean c hval hrft hcohax hordax hrelax hshape hatom`.  The Rocq
   `Local Notation E := (cand_exec c)` is the local notation `𝓔`.
3. The fold lemmas of §5 state their membership hypotheses as
   `∀ p ∈ ats, ...` (Rocq `∀ p, p ∈ ats → ...`) and use `List.foldl` with
   Lean's argument order.
4. `vm_compute`-free: the witnesses' machine states are computed by
   rewriting with `candNext`, `updWsEq`/`updWsNe`, `cohStorePostNe` and the
   step definitions, as the Rocq proofs do.
5. Lean-only helper (no Rocq twin): `ceRlWs02` (agent 0's state before the
   acquire load of `ceRl true v`, shared by `ceRlBlocked` and `ceRlFloor`,
   which Rocq computes twice inline).

**Not ported:** nothing.  The closing §15 ("what this slice does not do": the
pre-D-7 seven-step witness, why no premise remains, the owed lifts) is prose,
kept as the comment at the end.

**Statements checked** (by hand, against Rocq): all of them; in particular
`promiseFreeCompleteClean`, `promiseFreeCompleteLocal`, `srvwmoRealizable`,
`ceRlTrueInconsistent`, `ceRlStaleReachable`, `ceRlBlocked`,
`ceFwdNotPubClean`, `ceFwdReachable`.
-/
import Weak.WeakAxiomatic2

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open Lbl Ev

/-! # 1. The candidate's own log calculus -/

theorem trMsgsApp (l1 l2 : List Estep) : trMsgs (l1 ++ l2) = trMsgs l1 ++ trMsgs l2 := by
  induction l1 with
  | nil => rfl
  | cons s l ih => simp only [List.cons_append, trMsgs, ih, List.append_assoc]

theorem cdLogS (c : Cand) (k : Nat) (s : Estep) :
    c.cdTr[k]? = some s → cdLog c (k + 1) = cdLog c k ++ esMsg s := by
  intro hs
  unfold cdLog
  rw [take_S_r hs, trMsgsApp]
  simp [trMsgs]

theorem cdLogSplit (c : Cand) (k k' : Nat) : k ≤ k' → ∃ l, cdLog c k' = cdLog c k ++ l := by
  intro hle
  refine ⟨trMsgs ((c.cdTr.drop k).take (k' - k)), ?_⟩
  unfold cdLog
  rw [← trMsgsApp, take_take_drop, Nat.add_sub_of_le hle]

theorem cdLogLenLe (c : Cand) (k k' : Nat) : k ≤ k' → (cdLog c k).length ≤ (cdLog c k').length := by
  intro hle
  obtain ⟨l, hl⟩ := cdLogSplit c k k' hle
  rw [hl, List.length_append]; omega

/-- The log at the very end of the candidate. -/
theorem cdLogFull (c : Cand) : cdLog c c.cdTr.length = trMsgs c.cdTr := by
  unfold cdLog; rw [take_ge (Nat.le_refl _)]

/-! # 2. Truncation: the replay of a prefix IS the prefix of the replay -/

def ctake (c : Cand) (n : Nat) : Cand := ⟨c.cdImg, c.cdTr.take n⟩

theorem replayTake (σ : Mstate) (tr : List Estep) (n : Nat) :
    replay σ (tr.take n) = (replay σ tr).take (n + 1) := by
  induction tr generalizing σ n with
  | nil => simp [replay]
  | cons s tr ih =>
    cases n with
    | zero => simp [replay]
    | succ n => simp only [List.take_succ_cons, replay, ih]

theorem ctakeInit (c : Cand) (n : Nat) : candInit (ctake c n) = candInit c := rfl

theorem ctakeSt (c : Cand) (n : Nat) :
    (candExec (ctake c n)).exSt = (candExec c).exSt.take (n + 1) :=
  replayTake _ _ _

theorem ctakeStt (c : Cand) (n k : Nat) :
    k ≤ n → stt (candExec (ctake c n)) k = stt (candExec c) k := by
  intro hk; unfold stt; rw [ctakeSt, lookup_take (by omega)]

theorem ctakeEws (c : Cand) (n k i : Nat) :
    k ≤ n → ews (candExec (ctake c n)) k i = ews (candExec c) k i := by
  intro hk; unfold ews; rw [ctakeStt c n k hk]

theorem ctakeElog (c : Cand) (n k : Nat) :
    k ≤ n → elog (candExec (ctake c n)) k = elog (candExec c) k := by
  intro hk; unfold elog; rw [ctakeStt c n k hk]

theorem ctakeEvTs (c : Cand) (n k : Nat) :
    k ≤ n → evTs (candExec (ctake c n)) (ev_at k) = evTs (candExec c) (ev_at k) := by
  intro hk; rw [evTsAt, evTsAt, ctakeElog c n k hk]

theorem ctakeTr (c : Cand) (n k : Nat) :
    k < n → (candExec (ctake c n)).exTr[k]? = c.cdTr[k]? := by
  intro hk; exact lookup_take hk

theorem ctakeTrLen (c : Cand) (n : Nat) :
    n ≤ c.cdTr.length → (candExec (ctake c n)).exTr.length = n := by
  intro hn; show (c.cdTr.take n).length = n; rw [List.length_take]; omega

theorem ctakeImg (c : Cand) (n : Nat) : exImg (candExec (ctake c n)) = exImg (candExec c) := by
  unfold exImg eimg; rw [ctakeStt c n 0 (Nat.zero_le _)]

theorem candExLog (c : Cand) : exLog (candExec c) = cdLog c c.cdTr.length :=
  candElog c _ (Nat.le_refl _)

theorem candExTr (c : Cand) : (candExec c).exTr = c.cdTr := rfl

theorem candExImg (c : Cand) : exImg (candExec c) = c.cdImg := candEimg c 0 (Nat.zero_le _)

theorem ctakeExLog (c : Cand) (n : Nat) :
    n ≤ c.cdTr.length → exLog (candExec (ctake c n)) = cdLog c n := by
  intro _
  rw [candExLog]
  unfold cdLog
  show trMsgs ((c.cdTr.take n).take (c.cdTr.take n).length) = trMsgs (c.cdTr.take n)
  rw [take_ge (Nat.le_refl _)]

/-- The final logs of the two executions are related by an append. -/
theorem ctakeLogSplit (c : Cand) (n : Nat) :
    n ≤ c.cdTr.length → ∃ l, exLog (candExec c) = exLog (candExec (ctake c n)) ++ l := by
  intro hn
  rw [ctakeExLog c n hn, candExLog]
  exact cdLogSplit c n _ hn

/-! # 3. Write events of a candidate, without `execWf` -/

def esWmsg (s : Estep) : Option Wmsg :=
  match lbWr s.esLb with
  | some (base, vs) => some ⟨base, vs, some s.esAg, lbCls s.esLb⟩
  | none => none

theorem esMsgWmsg (s : Estep) :
    esMsg s = match esWmsg s with | some m => [m] | none => [] := by
  unfold esMsg esWmsg
  cases lbWr s.esLb with
  | none => rfl
  | some p => obtain ⟨b, v⟩ := p; rfl

theorem esWmsgIsW (s : Estep) (m : Wmsg) : esWmsg s = some m → lbIsW s.esLb = true := by
  unfold esWmsg
  cases h : lbWr s.esLb with
  | none => simp
  | some p => intro _; exact lbWrIsW _ _ h

theorem esWmsgNone (s : Estep) : esWmsg s = none → lbIsW s.esLb = false := by
  obtain ⟨ag, l⟩ := s
  cases l <;> simp [esWmsg, lbWr, lbIsW]

/-- The timestamp of step `k`, read off the candidate. -/
theorem candEvTs (c : Cand) (k : Nat) :
    k ≤ c.cdTr.length → evTs (candExec c) (ev_at k) = (cdLog c k).length + 1 := by
  intro hk; rw [evTsAt, candElog c k hk]

theorem candTsLen (c : Cand) (k : Nat) (s : Estep) (m : Wmsg) :
    c.cdTr[k]? = some s → esWmsg s = some m →
    evTs (candExec c) (ev_at k) = (cdLog c (k + 1)).length := by
  intro hs hm
  have hk := lookup_lt_Some hs
  rw [candEvTs c k (by omega), cdLogS c k s hs, esMsgWmsg, hm]
  simp

/-- A write step's message sits at its own timestamp in every later log. -/
theorem candLogByteWr (c : Cand) (k : Nat) (s : Estep) (m : Wmsg) (k' : Nat) (a : Int) :
    c.cdTr[k]? = some s → esWmsg s = some m → k + 1 ≤ k' →
    logByte c.cdImg (cdLog c k') (evTs (candExec c) (ev_at k)) a = msgByte m a := by
  intro hs hm hk'
  have hk := lookup_lt_Some hs
  rw [candEvTs c k (by omega), logByteS]
  obtain ⟨l, hl⟩ := cdLogSplit c (k + 1) k' hk'
  rw [hl, cdLogS c k s hs, esMsgWmsg, hm, List.append_assoc, lookup_app_r (Nat.le_refl _),
    Nat.sub_self]
  rfl

theorem candWrB (c : Cand) (k : Nat) (s : Estep) (m : Wmsg) (a : Int) :
    c.cdTr[k]? = some s → esWmsg s = some m → (msgByte m a).isSome →
    wrB (candExec c) a (ev_at k) := by
  intro hs hm hb
  have hk := lookup_lt_Some hs
  refine ⟨⟨s, hs, esWmsgIsW s m hm⟩, ?_⟩
  unfold evWrites
  rw [candExImg, candExLog, candLogByteWr c k s m _ a hs hm (by omega)]
  exact hb

theorem candWrBInv (c : Cand) (a : Int) (e : Ev) :
    wrB (candExec c) a e →
    (e = ev_init ∧ (c.cdImg a).isSome) ∨
    ∃ k s m, e = ev_at k ∧ c.cdTr[k]? = some s ∧ esWmsg s = some m ∧ (msgByte m a).isSome := by
  rintro ⟨hW, hwr⟩
  cases e with
  | ev_init =>
    left; refine ⟨rfl, ?_⟩
    unfold evWrites at hwr
    rw [candExImg] at hwr
    exact hwr
  | ev_at k =>
    obtain ⟨s, hs, hw⟩ := hW
    have hk := lookup_lt_Some hs
    right
    cases hm : esWmsg s with
    | none => rw [esWmsgNone s hm] at hw; cases hw
    | some m =>
      refine ⟨k, s, m, rfl, hs, hm, ?_⟩
      unfold evWrites at hwr
      rw [candExImg, candExLog, candLogByteWr c k s m _ a hs hm (by exact hk)] at hwr
      exact hwr

/-- Timestamps of write steps increase strictly with execution position. -/
theorem candTsLeLog (c : Cand) (k1 k2 : Nat) (s1 : Estep) (m1 : Wmsg) :
    c.cdTr[k1]? = some s1 → esWmsg s1 = some m1 → k1 < k2 →
    evTs (candExec c) (ev_at k1) ≤ (cdLog c k2).length := by
  intro hs hm hlt
  rw [candTsLen c k1 s1 m1 hs hm]
  exact cdLogLenLe c _ _ (by omega)

theorem candTsMono (c : Cand) (k1 k2 : Nat) (s1 : Estep) (m1 : Wmsg) :
    c.cdTr[k1]? = some s1 → esWmsg s1 = some m1 → k1 < k2 → k2 ≤ c.cdTr.length →
    evTs (candExec c) (ev_at k1) < evTs (candExec c) (ev_at k2) := by
  intro hs hm hlt hk2
  rw [candEvTs c k2 hk2]
  have := candTsLeLog c k1 k2 s1 m1 hs hm hlt
  omega

theorem candTsInj (c : Cand) (e1 e2 : Int × Ev) :
    wrB (candExec c) e1.1 e1.2 → wrB (candExec c) e2.1 e2.2 →
    evTs (candExec c) e1.2 = evTs (candExec c) e2.2 → e1.2 = e2.2 := by
  obtain ⟨a1, f1⟩ := e1
  obtain ⟨a2, f2⟩ := e2
  simp only
  intro hw1 hw2 hts
  rcases candWrBInv c a1 f1 hw1 with ⟨rfl, _⟩ | ⟨k1, s1, m1, rfl, hs1, hm1, _⟩ <;>
    rcases candWrBInv c a2 f2 hw2 with ⟨rfl, _⟩ | ⟨k2, s2, m2, rfl, hs2, hm2, _⟩
  · rfl
  · have hk2 := lookup_lt_Some hs2
    rw [candEvTs c k2 (by omega)] at hts; simp [evTs] at hts
  · have hk1 := lookup_lt_Some hs1
    rw [candEvTs c k1 (by omega)] at hts; simp [evTs] at hts
  · have hk1 := lookup_lt_Some hs1
    have hk2 := lookup_lt_Some hs2
    by_cases heq : k1 = k2
    · rw [heq]
    · exfalso
      by_cases hlt : k1 < k2
      · have := candTsMono c k1 k2 s1 m1 hs1 hm1 hlt (by omega); omega
      · have := candTsMono c k2 k1 s2 m2 hs2 hm2 (by omega) (by omega); omega

/-- Every non-zero timestamp present in a prefix log belongs to a write step of
that prefix. -/
theorem candTsWriter (c : Cand) (n t : Nat) :
    n ≤ c.cdTr.length → 0 < t → t ≤ (cdLog c n).length →
    ∃ k s m, k < n ∧ c.cdTr[k]? = some s ∧ esWmsg s = some m ∧ evTs (candExec c) (ev_at k) = t := by
  induction n with
  | zero => intro _ ht hlen; simp [cdLog, trMsgs] at hlen; omega
  | succ n ih =>
    intro hn ht hlen
    obtain ⟨s, hs⟩ := someOfIsSome (lookup_lt_is_Some_2 (l := c.cdTr) (i := n) (by omega))
    rw [cdLogS c n s hs, esMsgWmsg, List.length_append] at hlen
    cases hm : esWmsg s with
    | none =>
      rw [hm] at hlen
      simp only [List.length_nil, Nat.add_zero] at hlen
      obtain ⟨k, s', m', h1, h2, h3, h4⟩ := ih (by omega) ht hlen
      exact ⟨k, s', m', by omega, h2, h3, h4⟩
    | some m =>
      rw [hm] at hlen
      simp only [List.length_singleton] at hlen
      by_cases hle : t ≤ (cdLog c n).length
      · obtain ⟨k, s', m', h1, h2, h3, h4⟩ := ih (by omega) ht hle
        exact ⟨k, s', m', by omega, h2, h3, h4⟩
      · refine ⟨n, s, m, by omega, hs, hm, ?_⟩
        rw [candEvTs c n (by omega)]; omega

/-- ... hence a write inside a `writesIn` window is a genuine write EVENT with
its timestamp in that window. -/
theorem candWritesInWr (c : Cand) (n : Nat) (a : Int) (lo hi : Nat) :
    n ≤ c.cdTr.length → writesIn (cdLog c n) a lo hi →
    ∃ w, wrB (candExec c) a w ∧ lo < evTs (candExec c) w ∧ evTs (candExec c) w ≤ hi := by
  intro hn hw
  obtain ⟨t, hlo, hhi, hs⟩ := (writesInLogByte c.cdImg _ _ _ _).1 hw
  have htlen := logByteBounded c.cdImg (cdLog c n) t a hs
  obtain ⟨k, s, m, hk, hs', hm, hts⟩ := candTsWriter c n t hn (by omega) htlen
  refine ⟨ev_at k, ?_, by omega, by omega⟩
  apply candWrB c k s m a hs' hm
  rw [← candLogByteWr c k s m n a hs' hm (by omega), hts]
  exact hs

/-! # 4. The domination vocabulary -/

def frdomB (E : Exec) (i : Nat) (k : Nat) (a : Int) (n : Nat) : Prop :=
  ∀ k2 s2 w, k ≤ k2 → E.exTr[k2]? = some s2 → s2.esAg = i →
    frB E a (ev_at k2) w → n < evTs E w

def frdom (E : Exec) (i : Nat) (k : Nat) (n : Nat) : Prop := ∀ a, frdomB E i k a n

def ordDom (E : Exec) (i : Nat) (k : Nat) (n : Nat) : Prop :=
  n = 0 ∨
  ∀ k2 s2, k ≤ k2 → E.exTr[k2]? = some s2 → s2.esAg = i →
    ∃ e1 t, n ≤ t ∧
      ((ordPw E e1 (ev_at k2) ∧ pubW E e1 t) ∨
       (ordPr E e1 (ev_at k2) ∧ pubR E e1 t) ∨
       (relOrd E e1 (ev_at k2) ∧ pubW E e1 t))

def rsrc (E : Exec) (i : Nat) (k : Nat) (n : Nat) : Prop :=
  n = 0 ∨
  ∃ k1 s1 t, k1 < k ∧ E.exTr[k1]? = some s1 ∧ s1.esAg = i ∧ pubR E (ev_at k1) t ∧ n ≤ t

def wsrc (E : Exec) (i : Nat) (k : Nat) (n : Nat) : Prop :=
  n = 0 ∨
  ∃ k1 s1 t, k1 < k ∧ E.exTr[k1]? = some s1 ∧ s1.esAg = i ∧ pubW E (ev_at k1) t ∧ n ≤ t

/-- `wVRel`'s invariant: a po-earlier RELEASE write published it. -/
def relsrc (E : Exec) (i : Nat) (k : Nat) (n : Nat) : Prop :=
  n = 0 ∨
  ∃ k1 s1 t, k1 < k ∧ E.exTr[k1]? = some s1 ∧ s1.esAg = i ∧
    lbIsW s1.esLb = true ∧ lbRl s1.esLb = true ∧ pubW E (ev_at k1) t ∧ n ≤ t

/-- `wVrOld`'s invariant: either already delivered, or pending. -/
def rdom (E : Exec) (i : Nat) (k : Nat) (n : Nat) : Prop := ordDom E i k n ∨ rsrc E i k n

/-! ### Closure properties -/

theorem frdomB0 (E : Exec) (i k : Nat) (a : Int) : frdomB E i k a 0 := by
  rintro k2 s2 w _ _ _ ⟨⟨w0, _, _, _, hlt⟩, _⟩; omega

theorem frdom0 (E : Exec) (i k : Nat) : frdom E i k 0 := fun a => frdomB0 E i k a

theorem frdomBLe (E : Exec) (i k : Nat) (a : Int) (n n' : Nat) :
    n' ≤ n → frdomB E i k a n → frdomB E i k a n' := by
  intro hle hd k2 s2 w h1 h2 h3 h4; have := hd k2 s2 w h1 h2 h3 h4; omega

theorem frdomBWk (E : Exec) (i k k' : Nat) (a : Int) (n : Nat) :
    k ≤ k' → frdomB E i k a n → frdomB E i k' a n := by
  intro hle hd k2 s2 w h1 h2 h3 h4; exact hd k2 s2 w (by omega) h2 h3 h4

theorem frdomWk (E : Exec) (i k k' n : Nat) : k ≤ k' → frdom E i k n → frdom E i k' n :=
  fun hle hd a => frdomBWk E i k k' a n hle (hd a)

theorem frdomBMax (E : Exec) (i k : Nat) (a : Int) (n1 n2 : Nat) :
    frdomB E i k a n1 → frdomB E i k a n2 → frdomB E i k a (max n1 n2) := by
  intro h1 h2 k2 s2 w g1 g2 g3 g4
  have := h1 k2 s2 w g1 g2 g3 g4; have := h2 k2 s2 w g1 g2 g3 g4; omega

theorem frdomMax (E : Exec) (i k n1 n2 : Nat) :
    frdom E i k n1 → frdom E i k n2 → frdom E i k (max n1 n2) :=
  fun h1 h2 a => frdomBMax E i k a n1 n2 (h1 a) (h2 a)

theorem ordDomLe (E : Exec) (i k n n' : Nat) : n' ≤ n → ordDom E i k n → ordDom E i k n' := by
  rintro hle (h0 | hd)
  · left; omega
  · by_cases h0 : n' = 0
    · exact .inl h0
    · right
      intro k2 s2 h1 h2 h3
      obtain ⟨e1, t, hle', hc⟩ := hd k2 s2 h1 h2 h3
      exact ⟨e1, t, by omega, hc⟩

theorem ordDomWk (E : Exec) (i k k' n : Nat) : k ≤ k' → ordDom E i k n → ordDom E i k' n := by
  rintro hle (h0 | hd)
  · exact .inl h0
  · right; intro k2 s2 h1 h2 h3; exact hd k2 s2 (by omega) h2 h3

theorem ordDomMax (E : Exec) (i k n1 n2 : Nat) :
    ordDom E i k n1 → ordDom E i k n2 → ordDom E i k (max n1 n2) := by
  intro h1 h2
  by_cases hle : n1 ≤ n2
  · rw [Nat.max_eq_right hle]; exact h2
  · rw [Nat.max_eq_left (by omega)]; exact h1

theorem rsrcLe (E : Exec) (i k n n' : Nat) : n' ≤ n → rsrc E i k n → rsrc E i k n' := by
  rintro hle (h0 | ⟨k1, s1, t, h1, h2, h3, h4, h5⟩)
  · left; omega
  · exact .inr ⟨k1, s1, t, h1, h2, h3, h4, by omega⟩

theorem rsrcWk (E : Exec) (i k k' n : Nat) : k ≤ k' → rsrc E i k n → rsrc E i k' n := by
  rintro hle (h0 | ⟨k1, s1, t, h1, h2, h3, h4, h5⟩)
  · exact .inl h0
  · exact .inr ⟨k1, s1, t, by omega, h2, h3, h4, h5⟩

theorem wsrcLe (E : Exec) (i k n n' : Nat) : n' ≤ n → wsrc E i k n → wsrc E i k n' := by
  rintro hle (h0 | ⟨k1, s1, t, h1, h2, h3, h4, h5⟩)
  · left; omega
  · exact .inr ⟨k1, s1, t, h1, h2, h3, h4, by omega⟩

theorem wsrcWk (E : Exec) (i k k' n : Nat) : k ≤ k' → wsrc E i k n → wsrc E i k' n := by
  rintro hle (h0 | ⟨k1, s1, t, h1, h2, h3, h4, h5⟩)
  · exact .inl h0
  · exact .inr ⟨k1, s1, t, by omega, h2, h3, h4, h5⟩

theorem wsrcMax (E : Exec) (i k n1 n2 : Nat) :
    wsrc E i k n1 → wsrc E i k n2 → wsrc E i k (max n1 n2) := by
  intro h1 h2
  by_cases hle : n1 ≤ n2
  · rw [Nat.max_eq_right hle]; exact h2
  · rw [Nat.max_eq_left (by omega)]; exact h1

theorem relsrcLe (E : Exec) (i k n n' : Nat) : n' ≤ n → relsrc E i k n → relsrc E i k n' := by
  rintro hle (h0 | ⟨k1, s1, t, h1, h2, h3, h4, h5, h6, h7⟩)
  · left; omega
  · exact .inr ⟨k1, s1, t, h1, h2, h3, h4, h5, h6, by omega⟩

theorem relsrcWk (E : Exec) (i k k' n : Nat) : k ≤ k' → relsrc E i k n → relsrc E i k' n := by
  rintro hle (h0 | ⟨k1, s1, t, h1, h2, h3, h4, h5, h6, h7⟩)
  · exact .inl h0
  · exact .inr ⟨k1, s1, t, by omega, h2, h3, h4, h5, h6, h7⟩

theorem relsrcMax (E : Exec) (i k n1 n2 : Nat) :
    relsrc E i k n1 → relsrc E i k n2 → relsrc E i k (max n1 n2) := by
  intro h1 h2
  by_cases hle : n1 ≤ n2
  · rw [Nat.max_eq_right hle]; exact h2
  · rw [Nat.max_eq_left (by omega)]; exact h1

theorem rdomLe (E : Exec) (i k n n' : Nat) : n' ≤ n → rdom E i k n → rdom E i k n' := by
  rintro hle (h | h)
  · exact .inl (ordDomLe E i k n n' hle h)
  · exact .inr (rsrcLe E i k n n' hle h)

theorem rdomWk (E : Exec) (i k k' n : Nat) : k ≤ k' → rdom E i k n → rdom E i k' n := by
  rintro hle (h | h)
  · exact .inl (ordDomWk E i k k' n hle h)
  · exact .inr (rsrcWk E i k k' n hle h)

theorem rdomMax (E : Exec) (i k n1 n2 : Nat) :
    rdom E i k n1 → rdom E i k n2 → rdom E i k (max n1 n2) := by
  intro h1 h2
  by_cases hle : n1 ≤ n2
  · rw [Nat.max_eq_right hle]; exact h2
  · rw [Nat.max_eq_left (by omega)]; exact h1

/-! ### The two derivations: delivery becomes domination, pending becomes delivery -/

/-- `axOrd` (with `axRelOrd`) is exactly the step from "an `ord` edge carries a
publication ≥ n" to "no `fr` successor sits at or below n". -/
theorem ordDomFrdom (E : Exec) (i k n : Nat) :
    axOrd E → axRelOrd E → ordDom E i k n → frdom E i k n := by
  rintro hax hrax (h0 | hd) a
  · subst h0; exact frdomB0 E i k a
  · intro k2 s2 w hk hs2 hag hfr
    obtain ⟨e1, t, hle, hcase⟩ := hd k2 s2 hk hs2 hag
    rcases hcase with hc | hc | ⟨hro, hpub⟩
    · have := hax e1 k2 s2 a w t hs2 (.inl hc) hfr; omega
    · have := hax e1 k2 s2 a w t hs2 (.inr hc) hfr; omega
    · have := hrax e1 k2 s2 a w t hs2 hro hpub hfr; omega

/-- A `pr,sr` fence promotes a pending READ publication to a delivered one. -/
theorem rsrcFence (E : Exec) (i kf : Nat) (sf : Estep) (pw sw : Bool) (n : Nat) :
    E.exTr[kf]? = some sf → sf.esAg = i → sf.esLb = LFence true pw true sw →
    rsrc E i kf n → ordDom E i (kf + 1) n := by
  rintro hsf hag hlf (h0 | ⟨k1, s1, t, hlt, hs1, hag1, hpub, hle⟩)
  · exact .inl h0
  · right
    intro k2 s2 hk2 hs2 hag2
    exact ⟨ev_at k1, t, hle, .inr (.inl ⟨.inl ⟨k1, k2, pw, sw, rfl, rfl,
      kf, sf, s1, s2, hlt, by omega, hs1, hsf, hs2, by rw [hag1, hag], by rw [hag, hag2], hlf⟩,
      hpub⟩)⟩

/-- ... and a `pw,sr` fence does the same for a pending WRITE publication. -/
theorem wsrcFence (E : Exec) (i kf : Nat) (sf : Estep) (pr sw : Bool) (n : Nat) :
    E.exTr[kf]? = some sf → sf.esAg = i → sf.esLb = LFence pr true true sw →
    wsrc E i kf n → ordDom E i (kf + 1) n := by
  rintro hsf hag hlf (h0 | ⟨k1, s1, t, hlt, hs1, hag1, hpub, hle⟩)
  · exact .inl h0
  · right
    intro k2 s2 hk2 hs2 hag2
    exact ⟨ev_at k1, t, hle, .inl ⟨⟨k1, k2, pr, sw, rfl, rfl,
      kf, sf, s1, s2, hlt, by omega, hs1, hsf, hs2, by rw [hag1, hag], by rw [hag, hag2], hlf⟩,
      hpub⟩⟩

/-- An ACQUIRE read delivers its own publication with no fence at all. -/
theorem acqOrdDom (E : Exec) (i k1 : Nat) (s1 : Estep) (t : Nat) :
    E.exTr[k1]? = some s1 → s1.esAg = i → lbIsR s1.esLb = true → lbAq s1.esLb = true →
    pubR E (ev_at k1) t → ordDom E i (k1 + 1) t := by
  intro hs1 hag hisr haq hpub
  right
  intro k2 s2 hk2 hs2 hag2
  exact ⟨ev_at k1, t, Nat.le_refl _, .inr (.inl ⟨.inr ⟨k1, k2, s1, s2, rfl, rfl, by omega, hs1, hs2,
    by rw [hag, hag2], hisr, haq⟩, hpub⟩)⟩

/-- An ACQUIRE READ promotes a pending RELEASE publication to a delivered one
(RVWMO ppo rule 7 then rule 5). -/
theorem relsrcAcq (E : Exec) (i k : Nat) (s : Estep) (n : Nat) :
    E.exTr[k]? = some s → s.esAg = i → lbIsR s.esLb = true → lbAq s.esLb = true →
    (∃ a, rdB E a (ev_at k)) → relsrc E i k n → ordDom E i (k + 1) n := by
  rintro hs hag hisr haq hrd (h0 | ⟨k1, s1, t, hlt, hs1, hag1, hw1, hrl1, hpub, hle⟩)
  · exact .inl h0
  · right
    intro k2 s2 hk2 hs2 hag2
    refine ⟨ev_at k1, t, hle, .inr (.inr ⟨.inr ⟨ev_at k, ?_, hrd, ?_⟩, hpub⟩)⟩
    · exact ⟨k1, k, s1, s, rfl, rfl, hlt, hs1, hs, by rw [hag1, hag], hw1, hrl1, hisr, haq⟩
    · exact ⟨k, k2, s, s2, rfl, rfl, by omega, hs, hs2, by rw [hag, hag2], hisr, haq⟩

/-- The same promotion AT the acquire read itself. -/
theorem relsrcFrdomAt (E : Exec) (i k : Nat) (s : Estep) (n : Nat) :
    axRelOrd E → E.exTr[k]? = some s → s.esAg = i → lbIsR s.esLb = true → lbAq s.esLb = true →
    relsrc E i k n → ∀ a w, frB E a (ev_at k) w → n < evTs E w := by
  rintro hax hs hag hisr haq (h0 | ⟨k1, s1, t, hlt, hs1, hag1, hw1, hrl1, hpub, hle⟩) a w hfr
  · obtain ⟨⟨w0, _, _, _, hlt0⟩, _⟩ := hfr; omega
  · have hra : relAcqPo E (ev_at k1) (ev_at k) :=
      ⟨k1, k, s1, s, rfl, rfl, hlt, hs1, hs, by rw [hag1, hag], hw1, hrl1, hisr, haq⟩
    have := hax (ev_at k1) k s a w t hs (.inl hra) hpub hfr
    omega

/-! # 5. Upper bounds for the step functions — LIFTED

`maxcl` and the upper-bound fold lemmas live in `WeakMem`.  THREE additions owe
the same lift, proved here: (i) the release channel's upper bound; (ii) the
load fold's bounds WITH FORWARDING (the primed copies, stated on the byte's
actual CONTRIBUTION `P (fwdView ws aq p.1 p.2)`); (iii) the forward bank's own
fold facts. -/

theorem storeFoldVRel (P : Nat → Prop) (rl : Bool) (t : Nat) (as_ : List Int) (ws : Wstate) :
    maxcl P → P ws.wVRel → (rl = true → P t) →
    P (as_.foldl (fun w a => storePost w rl a t) ws).wVRel := by
  intro hcl
  induction as_ generalizing ws with
  | nil => intro hc _; exact hc
  | cons a l ih =>
    intro hc ht
    apply ih _ _ ht
    cases rl with
    | false => exact hc
    | true => exact maxclMax P _ _ hcl hc (ht rfl)

theorem loadFoldCoh' (P : Nat → Prop) (aq : Bool) (vpre : Nat) (ats : List (Int × Nat))
    (ws : Wstate) (a : Int) :
    maxcl P →
    (∀ p ∈ ats, p.1 = a → P p.2) →
    (∀ p ∈ ats, p.1 = a → P (fwdView ws aq p.1 p.2)) →
    P (coh ws a) → P vpre →
    P (coh (ats.foldl (fun w at_ => loadPostAt w aq vpre at_.1 at_.2) ws) a) := by
  intro hcl
  induction ats generalizing ws with
  | nil => intro _ _ hc _; exact hc
  | cons p l ih =>
    intro hts hfv hc hv
    apply ih (loadPostAt ws aq vpre p.1 p.2) (fun q hq hqa => hts q (List.mem_cons_of_mem _ hq) hqa)
      (fun q hq hqa => hfv q (List.mem_cons_of_mem _ hq) hqa) _ hv
    by_cases heq : a = p.1
    · have hpa := hts p List.mem_cons_self heq.symm
      have hpf := hfv p List.mem_cons_self heq.symm
      rw [heq, cohLoadPostAtEq]
      rw [heq] at hc
      exact maxclMax P _ _ hcl hc (maxclMax P _ _ hcl (maxclMax P _ _ hcl hv hpf) hpa)
    · rw [cohLoadPostAtNe _ _ _ _ _ _ heq]; exact hc

theorem loadFoldVrOld' (P : Nat → Prop) (aq : Bool) (vpre : Nat) (ats : List (Int × Nat))
    (ws : Wstate) :
    maxcl P → (∀ p ∈ ats, P (fwdView ws aq p.1 p.2)) →
    P ws.wVrOld → P vpre →
    P (ats.foldl (fun w at_ => loadPostAt w aq vpre at_.1 at_.2) ws).wVrOld := by
  intro hcl
  induction ats generalizing ws with
  | nil => intro _ hc _; exact hc
  | cons p l ih =>
    intro hfv hc hv
    apply ih (loadPostAt ws aq vpre p.1 p.2) (fun q hq => hfv q (List.mem_cons_of_mem _ hq)) _ hv
    show P (max ws.wVrOld (max vpre (fwdView ws aq p.1 p.2)))
    exact maxclMax P _ _ hcl hc (maxclMax P _ _ hcl hv (hfv p List.mem_cons_self))

theorem loadFoldVrNew' (P : Nat → Prop) (aq : Bool) (vpre : Nat) (ats : List (Int × Nat))
    (ws : Wstate) :
    maxcl P → (∀ p ∈ ats, P (fwdView ws aq p.1 p.2)) →
    P ws.wVrNew → P vpre →
    P (ats.foldl (fun w at_ => loadPostAt w aq vpre at_.1 at_.2) ws).wVrNew := by
  intro hcl
  induction ats generalizing ws with
  | nil => intro _ hc _; exact hc
  | cons p l ih =>
    intro hfv hc hv
    apply ih (loadPostAt ws aq vpre p.1 p.2) (fun q hq => hfv q (List.mem_cons_of_mem _ hq)) _ hv
    cases aq with
    | false => exact hc
    | true =>
      show P (max ws.wVrNew (max vpre (fwdView ws true p.1 p.2)))
      exact maxclMax P _ _ hcl hc (maxclMax P _ _ hcl hv (hfv p List.mem_cons_self))

/-- The bank after a store fold: `(t, 0)` on every byte written, untouched
elsewhere. -/
theorem storeFoldFwdOut (rl : Bool) (t : Nat) (as_ : List Int) (ws : Wstate) (a : Int) :
    a ∉ as_ → get? (as_.foldl (fun w b => storePost w rl b t) ws).wFwd a = get? ws.wFwd a := by
  induction as_ generalizing ws with
  | nil => intro _; rfl
  | cons b l ih =>
    intro hnin
    rw [List.mem_cons, not_or] at hnin
    rw [List.foldl_cons, ih _ hnin.2]
    exact lookupInsertNe (Ne.symm hnin.1)

theorem storeFoldFwdIn (rl : Bool) (t : Nat) (as_ : List Int) (ws : Wstate) (a : Int) :
    a ∈ as_ → get? (as_.foldl (fun w b => storePost w rl b t) ws).wFwd a = some (t, 0) := by
  induction as_ generalizing ws with
  | nil => intro h; cases h
  | cons b l ih =>
    intro hin
    by_cases hl : a ∈ l
    · exact ih _ hl
    · rcases List.mem_cons.1 hin with rfl | hin'
      · rw [List.foldl_cons, storeFoldFwdOut rl t l _ _ hl]
        exact lookupInsert
      · exact absurd hin' hl

theorem storeRunFwdIn (ws : Wstate) (rl : Bool) (base : Int) (n t : Nat) (a : Int) :
    a ∈ storeRunAs base n → get? (storePostRun ws rl base n t).wFwd a = some (t, 0) :=
  storeFoldFwdIn rl t _ ws a

theorem storeRunFwdOut (ws : Wstate) (rl : Bool) (base : Int) (n t : Nat) (a : Int) :
    a ∉ storeRunAs base n → get? (storePostRun ws rl base n t).wFwd a = get? ws.wFwd a :=
  storeFoldFwdOut rl t _ ws a

/-- `fwdView` post-D-7: EITHER its own timestamp OR nothing at all. -/
theorem fwdViewCases (ws : Wstate) (aq : Bool) (a : Int) (t : Nat) :
    (∀ a' tf vf, get? ws.wFwd a' = some (tf, vf) → vf = 0) →
    fwdView ws aq a t = t ∨ fwdView ws aq a t = 0 := by
  intro hz
  cases aq with
  | true => exact .inl rfl
  | false =>
    cases hf : get? ws.wFwd a with
    | none => exact .inl (fwdViewMiss _ _ _ _ hf)
    | some p =>
      obtain ⟨tf, vf⟩ := p
      simp only [fwdView, hf, Bool.false_eq_true, ↓reduceIte]
      by_cases ht : t = tf
      · right; simp only [ht, ↓reduceIte]; exact hz a tf vf hf
      · left; simp [ht]

/-! # 6. The state calculus -/

theorem candWsNe (c : Cand) (k : Nat) (s : Estep) (i : Nat) :
    c.cdTr[k]? = some s → i ≠ s.esAg → ews (candExec c) (k + 1) i = ews (candExec c) k i := by
  intro hs hne; unfold ews; rw [candNext c k s hs, mnextWsNe _ _ _ i hne]

theorem candWsLoad (c : Cand) (k : Nat) (s : Estep) (aq : Bool) (base : Int) (ts : List Nat)
    (vs : List (BitVec 8)) :
    c.cdTr[k]? = some s → s.esLb = LLoad aq base ts vs →
    ews (candExec c) (k + 1) s.esAg = loadPostRun (ews (candExec c) k s.esAg) aq base ts := by
  intro hs hl; unfold ews; rw [candNext c k s hs, hl]; exact updWsEq _ _ _

theorem candWsStore (c : Cand) (k : Nat) (s : Estep) (rl : Bool) (base : Int)
    (vs : List (BitVec 8)) (kc : WmClass) :
    c.cdTr[k]? = some s → s.esLb = LStore rl base vs kc →
    ews (candExec c) (k + 1) s.esAg
      = storePostRun (ews (candExec c) k s.esAg) rl base vs.length (evTs (candExec c) (ev_at k)) := by
  intro hs hl; unfold ews; rw [candNext c k s hs, hl]; exact updWsEq _ _ _

theorem candWsFence (c : Cand) (k : Nat) (s : Estep) (pr pw sr sw : Bool) :
    c.cdTr[k]? = some s → s.esLb = LFence pr pw sr sw →
    ews (candExec c) (k + 1) s.esAg = fencePost (ews (candExec c) k s.esAg) pr pw sr sw := by
  intro hs hl; unfold ews; rw [candNext c k s hs, hl]; exact updWsEq _ _ _

/-- W13 (E): the replay's `mnext` leaves the state at an I/O-class label. -/
theorem candWsIo (c : Cand) (k : Nat) (s : Estep) (kd : IoKind) (base : Int)
    (vs : List (BitVec 8)) :
    c.cdTr[k]? = some s → s.esLb = LIo kd base vs →
    ews (candExec c) (k + 1) s.esAg = ews (candExec c) k s.esAg := by
  intro hs hl; unfold ews; rw [candNext c k s hs, hl]; rfl

theorem candWsRmw (c : Cand) (k : Nat) (s : Estep) (aq rl : Bool) (base : Int) (ts : List Nat)
    (rvs wvs : List (BitVec 8)) (kc : WmClass) :
    c.cdTr[k]? = some s → s.esLb = LRmw aq rl base ts rvs wvs kc →
    ews (candExec c) (k + 1) s.esAg
      = storePostRun (loadPostRun (ews (candExec c) k s.esAg) aq base ts) rl base wvs.length
          (evTs (candExec c) (ev_at k)) := by
  intro hs hl; unfold ews; rw [candNext c k s hs, hl]; exact updWsEq _ _ _

theorem candSttInit (c : Cand) : stt (candExec c) 0 = candInit c :=
  sttLookup _ _ _ (replay0 (candInit c) c.cdTr)

theorem candWsInit (c : Cand) (i : Nat) : ews (candExec c) 0 i = wsInit := by
  unfold ews; rw [candSttInit]; rfl

/-! ### The byte/timestamp pairs a multi-byte access folds over -/

theorem elemOfZipSeq (base : Int) (ts : List Nat) (p : Int × Nat) :
    p ∈ List.zipWith (fun (j : Nat) (t : Nat) => (base + (j : Int), t)) (List.range' 0 ts.length) ts →
    ∃ j : Nat, ts[j]? = some p.2 ∧ p.1 = accAddr base j := by
  intro hin
  obtain ⟨j, x, y, hp, hx, hy⟩ := elem_of_lookup_zip_with_1 hin
  rw [lookup_seq] at hx
  obtain ⟨rfl, _⟩ := hx
  subst hp
  exact ⟨j, hy, by simp [accAddr]⟩

theorem elemOfMapSeq (base : Int) (n : Nat) (a : Int) :
    a ∈ (List.range' 0 n).map (fun j : Nat => base + (j : Int)) →
    ∃ j : Nat, j < n ∧ a = accAddr base j := by
  intro hin
  obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hin
  rw [List.mem_range'_1] at hj
  exact ⟨j, by omega, rfl⟩

/-! ### `wrB` for the virtual init event, and transfer to a truncation -/

theorem candWrBInit (c : Cand) (a : Int) : (c.cdImg a).isSome → wrB (candExec c) a ev_init := by
  intro hs; refine ⟨trivial, ?_⟩; unfold evWrites; rw [candExImg]; exact hs

theorem ctakeReadsAt (c : Cand) (n k : Nat) (a : Int) (t : Nat) (v : BitVec 8) :
    k < n → readsAt (candExec c) k a t v → readsAt (candExec (ctake c n)) k a t v := by
  rintro hk ⟨s, base, ts, vs, j, hs, hrd, hj, hv, ha⟩
  exact ⟨s, base, ts, vs, j, by rw [ctakeTr c n k hk]; exact hs, hrd, hj, hv, ha⟩

theorem ctakeWrB (c : Cand) (n : Nat) (a : Int) (k : Nat) :
    k < n → wrB (candExec c) a (ev_at k) → wrB (candExec (ctake c n)) a (ev_at k) := by
  intro hk hw
  rcases candWrBInv c a (ev_at k) hw with ⟨habs, _⟩ | ⟨k', s, m, heq, hs, hm, hb⟩
  · cases habs
  · injection heq with heq; subst heq
    apply candWrB (ctake c n) k s m a _ hm hb
    show (c.cdTr.take n)[k]? = some s
    rw [lookup_take hk]; exact hs

theorem ctakeWrBInit (c : Cand) (n : Nat) (a : Int) :
    wrB (candExec c) a ev_init → wrB (candExec (ctake c n)) a ev_init := by
  intro hw
  rcases candWrBInv c a ev_init hw with ⟨_, hs⟩ | ⟨_, _, _, habs, _⟩
  · exact candWrBInit (ctake c n) a hs
  · cases habs

/-! # 7. The coherence conjunct: a touched byte's timestamp dominates -/

set_option hygiene false in
local notation "𝓔" => candExec c

theorem candReadTsLe (c : Cand) (hval : candValues c) (k : Nat) (a : Int) (t : Nat)
    (v : BitVec 8) : readsAt 𝓔 k a t v → t ≤ (cdLog c k).length := by
  rintro ⟨s, base, ts, vs, j, hs, hrd, hj, hv, rfl⟩
  have hlb := hval k s base ts vs hs hrd j t v hj hv
  exact logByteBounded c.cdImg (cdLog c k) t (accAddr base j) (by rw [hlb]; rfl)

/-- A write whose timestamp is already in the log at step `k` is a step strictly
before `k`. -/
theorem candWrLt (c : Cand) (k : Nat) (a : Int) (k' : Nat) :
    wrB 𝓔 a (ev_at k') → evTs 𝓔 (ev_at k') ≤ (cdLog c k).length → k' < k := by
  intro hw hle
  rcases candWrBInv c a (ev_at k') hw with ⟨habs, _⟩ | ⟨k'', s, m, heq, hs, hm, _⟩
  · cases habs
  · injection heq with heq; subst heq
    have hk' := lookup_lt_Some hs
    by_cases hlt : k' < k
    · exact hlt
    · exfalso
      rw [candEvTs c k' (by omega)] at hle
      have := cdLogLenLe c k k' (by omega)
      omega

theorem touchFrdom (c : Cand) (hrft : axRfTotal 𝓔) (hcohax : axCoherence 𝓔) (k1 : Nat)
    (s1 : Estep) (a : Int) (t1 : Nat) :
    c.cdTr[k1]? = some s1 →
    ((∃ v, readsAt 𝓔 k1 a t1 v) ∨ (wrB 𝓔 a (ev_at k1) ∧ t1 = evTs 𝓔 (ev_at k1))) →
    frdomB 𝓔 s1.esAg (k1 + 1) a t1 := by
  intro hs1 htouch k2 s2 w hk hs2 hag hfr
  by_cases hlt : t1 < evTs 𝓔 w
  · exact hlt
  exfalso
  have hfr' := hfr
  obtain ⟨⟨w0, hrf0, hco0⟩, hne⟩ := hfr'
  obtain ⟨hw0, hw, hlt0⟩ := hco0
  have hacc2 : accB 𝓔 a (ev_at k2) := by
    obtain ⟨_, k, t, v, hkeq, hr, _⟩ := hrf0
    exact .inr ⟨k, t, v, hkeq, hr⟩
  have hacc1 : accB 𝓔 a (ev_at k1) := by
    rcases htouch with ⟨v1, hr1⟩ | ⟨hw1, _⟩
    · exact .inr ⟨k1, t1, v1, rfl, hr1⟩
    · exact .inl hw1
  have hpl : poLocB 𝓔 a (ev_at k1) (ev_at k2) :=
    ⟨⟨k1, k2, s1, s2, rfl, rfl, by omega, hs1, hs2, hag.symm⟩, hacc1, hacc2⟩
  apply hcohax a (ev_at k1)
  refine tc_l (y := ev_at k2) (.inl hpl) ?_
  rcases htouch with ⟨v1, hr1⟩ | ⟨hw1, ht1⟩
  · -- the earlier access READ `a` at `t1`
    obtain ⟨w1, hrf1⟩ := hrft k1 a t1 v1 hr1
    have hts1 : evTs 𝓔 w1 = t1 := by
      have hrf1' := hrf1
      obtain ⟨_, k, t, v, hkeq, hr, hts⟩ := hrf1'
      injection hkeq with hkeq; subst hkeq
      exact hts.trans (readsAtDet 𝓔 k1 a t v t1 v1 hr hr1).1
    by_cases heq : evTs 𝓔 w = t1
    · -- `w` IS the source the earlier read took
      refine tc_l (y := w) (.inr (.inr (.inr hfr))) ?_
      exact tc_once (.inr (.inl ⟨hw, k1, t1, v1, rfl, hr1, heq⟩))
    · refine tc_l (y := w) (.inr (.inr (.inr hfr))) ?_
      refine tc_l (y := w1) (.inr (.inr (.inl ⟨hw, hrf1.1, by omega⟩))) ?_
      exact tc_once (.inr (.inl hrf1))
  · -- the earlier access WROTE `a` at its own timestamp
    by_cases heq : evTs 𝓔 w = evTs 𝓔 (ev_at k1)
    · have : w = ev_at k1 := candTsInj c (a, w) (a, ev_at k1) hw hw1 heq
      subst this
      exact tc_once (.inr (.inr (.inr hfr)))
    · refine tc_l (y := w) (.inr (.inr (.inr hfr))) ?_
      exact tc_once (.inr (.inr (.inl ⟨hw, hw1, by omega⟩)))

/-! # 8. THE FORWARD BANK'S CONTENT — what makes a forwarded read harmless -/

theorem msgByteInRange (base : Int) (vs : List (BitVec 8)) (tid : Option Nat) (k : WmClass)
    (j : Nat) : j < vs.length → (msgByte ⟨base, vs, tid, k⟩ (accAddr base j)).isSome := by
  intro hj
  unfold msgByte accAddr
  have h1 : base ≤ base + (j : Int) := by omega
  have h2 : (base + (j : Int) - base).toNat = j := by omega
  simp only [h1, ↓reduceIte, h2]
  exact lookup_lt_is_Some_2 hj

theorem msgByteElem (base : Int) (vs : List (BitVec 8)) (tid : Option Nat) (kc : WmClass)
    (a : Int) : (msgByte ⟨base, vs, tid, kc⟩ a).isSome → a ∈ storeRunAs base vs.length := by
  intro h
  obtain ⟨j, hj, ha⟩ := msgByteRange _ a h
  exact List.mem_map.2 ⟨j, List.mem_range'_1.2 ⟨Nat.zero_le _, by simpa using hj⟩, ha.symm⟩

theorem candWrRun (c : Cand) (k : Nat) (s : Estep) (base : Int) (vs : List (BitVec 8)) (a : Int) :
    c.cdTr[k]? = some s → lbWr s.esLb = some (base, vs) → wrB 𝓔 a (ev_at k) →
    a ∈ storeRunAs base vs.length := by
  intro hs hwr hw
  have hm : esWmsg s = some ⟨base, vs, some s.esAg, lbCls s.esLb⟩ := by
    unfold esWmsg; rw [hwr]
  rcases candWrBInv c a (ev_at k) hw with ⟨habs, _⟩ | ⟨k0, s0, m0, heq, hs0, hm0, hb⟩
  · cases habs
  · injection heq with heq; subst heq
    rw [hs] at hs0; injection hs0 with hs0; subst hs0
    rw [hm] at hm0; injection hm0 with hm0; subst hm0
    exact msgByteElem _ _ _ _ a hb

theorem candRunWr (c : Cand) (k : Nat) (s : Estep) (base : Int) (vs : List (BitVec 8)) (a : Int) :
    c.cdTr[k]? = some s → lbWr s.esLb = some (base, vs) →
    a ∈ storeRunAs base vs.length → wrB 𝓔 a (ev_at k) := by
  intro hs hwr hin
  obtain ⟨j, hj, rfl⟩ := elemOfMapSeq base vs.length a hin
  exact candWrB c k s ⟨base, vs, some s.esAg, lbCls s.esLb⟩ _ hs (by unfold esWmsg; rw [hwr])
    (msgByteInRange _ _ _ _ j hj)

/-- One step's effect on the bank, for both writing labels at once. -/
theorem candWsFwdW (c : Cand) (k : Nat) (s : Estep) (base : Int) (vs : List (BitVec 8)) (a : Int) :
    c.cdTr[k]? = some s → lbWr s.esLb = some (base, vs) →
    (a ∈ storeRunAs base vs.length →
      get? (ews 𝓔 (k + 1) s.esAg).wFwd a = some (evTs 𝓔 (ev_at k), 0)) ∧
    (a ∉ storeRunAs base vs.length →
      get? (ews 𝓔 (k + 1) s.esAg).wFwd a = get? (ews 𝓔 k s.esAg).wFwd a) := by
  intro hs hwr
  cases hl : s.esLb with
  | LLoad => rw [hl] at hwr; simp [lbWr] at hwr
  | LStore rl b0 vs0 kc =>
    rw [hl] at hwr; simp only [lbWr, Option.some.injEq, Prod.mk.injEq] at hwr
    obtain ⟨rfl, rfl⟩ := hwr
    rw [candWsStore c k s rl b0 vs0 kc hs hl]
    exact ⟨fun hin => storeRunFwdIn _ _ _ _ _ _ hin, fun hout => storeRunFwdOut _ _ _ _ _ _ hout⟩
  | LFence => rw [hl] at hwr; simp [lbWr] at hwr
  | LRmw aq rl b0 ts0 rvs0 wvs0 kc =>
    rw [hl] at hwr; simp only [lbWr, Option.some.injEq, Prod.mk.injEq] at hwr
    obtain ⟨rfl, rfl⟩ := hwr
    rw [candWsRmw c k s aq rl b0 ts0 rvs0 wvs0 kc hs hl]
    refine ⟨fun hin => storeRunFwdIn _ _ _ _ _ _ hin, fun hout => ?_⟩
    rw [storeRunFwdOut _ _ _ _ _ _ hout, loadPostRunFwd]
  | LIo => rw [hl] at hwr; simp [lbWr] at hwr

/-- A non-writing step moves neither the bank nor the write set. -/
theorem candWsFwdNw (c : Cand) (k : Nat) (s : Estep) :
    c.cdTr[k]? = some s → esWmsg s = none →
    (ews 𝓔 (k + 1) s.esAg).wFwd = (ews 𝓔 k s.esAg).wFwd := by
  intro hs hm
  cases hl : s.esLb with
  | LLoad aq b0 ts0 vs0 => rw [candWsLoad c k s aq b0 ts0 vs0 hs hl]; exact loadPostRunFwd _ _ _ _
  | LStore => unfold esWmsg at hm; rw [hl] at hm; simp [lbWr] at hm
  | LFence p1 p2 p3 p4 => rw [candWsFence c k s p1 p2 p3 p4 hs hl]; exact fencePostFwd _ _ _ _ _
  | LRmw => unfold esWmsg at hm; rw [hl] at hm; simp [lbWr] at hm
  | LIo kd0 b0 v0 => rw [candWsIo c k s kd0 b0 v0 hs hl]

def bankdom (c : Cand) (k : Nat) (i : Nat) : Prop :=
  (∀ a tf vf, get? (ews 𝓔 k i).wFwd a = some (tf, vf) → vf = 0) ∧
  (∀ k' s' a, k' < k → c.cdTr[k']? = some s' → s'.esAg = i → wrB 𝓔 a (ev_at k') →
    ∃ k'' s'', k'' < k ∧ c.cdTr[k'']? = some s'' ∧ s''.esAg = i ∧ wrB 𝓔 a (ev_at k'') ∧
      evTs 𝓔 (ev_at k') ≤ evTs 𝓔 (ev_at k'') ∧
      get? (ews 𝓔 k i).wFwd a = some (evTs 𝓔 (ev_at k''), 0))

theorem candBankdom (c : Cand) (k : Nat) (i : Nat) : k ≤ c.cdTr.length → bankdom c k i := by
  induction k with
  | zero =>
    intro _
    refine ⟨?_, fun k' _ _ hk' => absurd hk' (Nat.not_lt_zero _)⟩
    intro a tf vf hlk
    rw [candWsInit c i] at hlk
    simp [wsInit, lookupEmpty] at hlk
  | succ k ih =>
    intro hk
    obtain ⟨s, hs⟩ := someOfIsSome (lookup_lt_is_Some_2 (l := c.cdTr) (i := k) (by omega))
    obtain ⟨iha, ihb⟩ := ih (by omega)
    by_cases hi : i = s.esAg
    · subst hi
      cases hm : esWmsg s with
      | none =>
        -- not a write step
        have hws := candWsFwdNw c k s hs hm
        have hnw : ∀ a, ¬ wrB 𝓔 a (ev_at k) := by
          rintro a ⟨⟨s0, hs0, hw0⟩, _⟩
          rw [candExTr, hs] at hs0; injection hs0 with hs0; subst hs0
          rw [esWmsgNone s hm] at hw0; cases hw0
        unfold bankdom; rw [hws]
        refine ⟨iha, ?_⟩
        intro k' s' a hk' hs' hag hw
        have hlt : k' < k := by
          by_cases heq : k' = k
          · subst heq; exact absurd hw (hnw a)
          · omega
        obtain ⟨k'', s'', h1, h2, h3, h4, h5, h6⟩ := ihb k' s' a hlt hs' hag hw
        exact ⟨k'', s'', by omega, h2, h3, h4, h5, h6⟩
      | some m =>
        -- a write step of this very agent
        cases hwr : lbWr s.esLb with
        | none => unfold esWmsg at hm; rw [hwr] at hm; cases hm
        | some p =>
          obtain ⟨base, vs⟩ := p
          refine ⟨?_, ?_⟩
          · intro a tf vf hlk
            obtain ⟨hin, hout⟩ := candWsFwdW c k s base vs a hs hwr
            by_cases h : a ∈ storeRunAs base vs.length
            · rw [hin h] at hlk; injection hlk with hlk; injection hlk with _ hlk; exact hlk.symm
            · rw [hout h] at hlk; exact iha a tf vf hlk
          · intro k' s' a hk' hs' hag hw
            obtain ⟨hin, hout⟩ := candWsFwdW c k s base vs a hs hwr
            by_cases h : a ∈ storeRunAs base vs.length
            · refine ⟨k, s, by omega, hs, rfl, candRunWr c k s base vs a hs hwr h, ?_, hin h⟩
              by_cases heq : k' = k
              · rw [heq]; exact Nat.le_refl _
              · obtain ⟨⟨s0, hs0, hw0⟩, _⟩ := hw
                rw [candExTr, hs'] at hs0; injection hs0 with hs0; subst hs0
                obtain ⟨b1, v1, hwr1⟩ := lbIsWWr s'.esLb hw0
                have := candTsMono c k' k s' ⟨b1, v1, some s'.esAg, lbCls s'.esLb⟩ hs'
                  (by unfold esWmsg; rw [hwr1]) (by omega) (by omega)
                omega
            · have hlt : k' < k := by
                by_cases heq : k' = k
                · subst heq; exact absurd (candWrRun c k' s base vs a hs hwr hw) h
                · omega
              obtain ⟨k'', s'', h1, h2, h3, h4, h5, h6⟩ := ihb k' s' a hlt hs' hag hw
              exact ⟨k'', s'', by omega, h2, h3, h4, h5, by rw [hout h]; exact h6⟩
    · have hws : ews 𝓔 (k + 1) i = ews 𝓔 k i := candWsNe c k s i hs hi
      unfold bankdom; rw [hws]
      refine ⟨iha, ?_⟩
      intro k' s' a hk' hs' hag hw
      have hlt : k' < k := by
        by_cases heq : k' = k
        · subst heq; rw [hs] at hs'; injection hs' with hs'; subst hs'; exact absurd hag.symm hi
        · omega
      obtain ⟨k'', s'', h1, h2, h3, h4, h5, h6⟩ := ihb k' s' a hlt hs' hag hw
      exact ⟨k'', s'', by omega, h2, h3, h4, h5, h6⟩

/-- THE READ CLASSIFICATION: every byte a read takes either contributes
NOTHING (forwarded) or contributes its own timestamp, which is then a
PUBLICATION. -/
theorem candReadSplit (c : Cand) (hval : candValues c) (hrft : axRfTotal 𝓔)
    (hcohax : axCoherence 𝓔) (k : Nat) (s : Estep) (a : Int) (t : Nat) (v : BitVec 8) :
    k < c.cdTr.length → c.cdTr[k]? = some s → readsAt 𝓔 k a t v →
    fwdView (ews 𝓔 k s.esAg) (lbAq s.esLb) a t = 0 ∨
    (fwdView (ews 𝓔 k s.esAg) (lbAq s.esLb) a t = t ∧ pubR 𝓔 (ev_at k) t) := by
  intro hk hs hr
  obtain ⟨hz, hb⟩ := candBankdom c k s.esAg (by omega)
  rcases fwdViewCases (ews 𝓔 k s.esAg) (lbAq s.esLb) a t hz with hfv | hfv
  · right
    refine ⟨hfv, ?_⟩
    cases haq : lbAq s.esLb with
    | true => exact ⟨k, s, a, v, rfl, hs, hr, .inl haq⟩
    | false =>
      rw [haq] at hfv
      obtain ⟨w, hrf⟩ := hrft k a t v hr
      have hts : evTs 𝓔 w = t := by
        have hrf' := hrf
        obtain ⟨_, k0, t0, v0, hkeq, hr0, hts0⟩ := hrf'
        injection hkeq with hkeq; subst hkeq
        exact hts0.trans (readsAtDet 𝓔 k a t0 v0 t v hr0 hr).1
      cases w with
      | ev_init =>
        -- the era-initial image is external to every agent
        exact ⟨k, s, a, v, rfl, hs, hr, .inr ⟨ev_init, hrf, trivial⟩⟩
      | ev_at k' =>
        have htlen : t ≤ (cdLog c k).length := candReadTsLe c hval k a t v hr
        have hk' : k' < k := candWrLt c k a k' hrf.1 (by omega)
        obtain ⟨s', hs'⟩ := someOfIsSome (lookup_lt_is_Some_2 (l := c.cdTr) (i := k') (by omega))
        by_cases hag : s'.esAg = s.esAg
        · -- INTERNAL SOURCE: impossible in this branch
          exfalso
          obtain ⟨k'', s'', hk'', hs'', hag'', hw'', hle, hbk⟩ := hb k' s' a hk' hs' hag hrf.1
          rw [hts] at hle
          by_cases heq : evTs 𝓔 (ev_at k'') = t
          · -- the bank holds `t`: `fwdView` is the banked `0`, not `t`
            rw [heq] at hbk
            rw [fwdViewHit (ews 𝓔 k s.esAg) a t t 0 hbk rfl] at hfv
            rw [← hts] at hfv
            simp [evTs] at hfv
          · -- the bank holds a STRICTLY LATER own write to `a`: a coherence cycle
            have hfrd := touchFrdom c hrft hcohax k'' s'' a (evTs 𝓔 (ev_at k'')) hs''
              (.inr ⟨hw'', rfl⟩)
            rw [hag''] at hfrd
            have hfr : frB 𝓔 a (ev_at k) (ev_at k'') := by
              refine ⟨⟨ev_at k', hrf, hrf.1, hw'', by omega⟩, ?_⟩
              intro habs; injection habs with habs; omega
            have := hfrd k s (ev_at k'') (by omega) hs rfl hfr
            omega
        · exact ⟨k, s, a, v, rfl, hs, hr, .inr ⟨ev_at k', hrf, s', hs', hag⟩⟩
  · exact .inl hfv

/-! # 9. THE VIEW-DOMINATION INVARIANT -/

def invw (c : Cand) (k : Nat) (i : Nat) (ws : Wstate) : Prop :=
  (∀ a, frdomB 𝓔 i k a (coh ws a)) ∧
  ordDom 𝓔 i k ws.wVrNew ∧
  rdom 𝓔 i k ws.wVrOld ∧
  wsrc 𝓔 i k ws.wVwOld ∧
  relsrc 𝓔 i k ws.wVRel

def inv (c : Cand) (k : Nat) (i : Nat) : Prop := invw c k i (ews 𝓔 k i)

theorem invwWk (c : Cand) (k k' i : Nat) (ws : Wstate) : k ≤ k' → invw c k i ws → invw c k' i ws := by
  rintro hle ⟨hc, hrn, hro, hwo, hrel⟩
  exact ⟨fun a => frdomBWk _ _ _ _ _ _ hle (hc a), ordDomWk _ _ _ _ _ hle hrn,
    rdomWk _ _ _ _ _ hle hro, wsrcWk _ _ _ _ _ hle hwo, relsrcWk _ _ _ _ _ hle hrel⟩

/-- The invariant does not constrain `wVcap`, so `ctrlPost` is transparent. -/
theorem invwCtrlPost (c : Cand) (k i : Nat) (ws : Wstate) (v : Nat) :
    invw c k i ws → invw c k i (ctrlPost ws v) := fun h => h

theorem maxclFrdomB (c : Cand) (i k : Nat) (a : Int) : maxcl (frdomB 𝓔 i k a) :=
  ⟨frdomB0 _ _ _ _, fun _ _ => frdomBMax _ _ _ _ _ _⟩
theorem maxclOrdDom (c : Cand) (i k : Nat) : maxcl (ordDom 𝓔 i k) :=
  ⟨.inl rfl, fun _ _ => ordDomMax _ _ _ _ _⟩
theorem maxclRdom (c : Cand) (i k : Nat) : maxcl (rdom 𝓔 i k) :=
  ⟨.inl (.inl rfl), fun _ _ => rdomMax _ _ _ _ _⟩
theorem maxclWsrc (c : Cand) (i k : Nat) : maxcl (wsrc 𝓔 i k) :=
  ⟨.inl rfl, fun _ _ => wsrcMax _ _ _ _ _⟩
theorem maxclRelsrc (c : Cand) (i k : Nat) : maxcl (relsrc 𝓔 i k) :=
  ⟨.inl rfl, fun _ _ => relsrcMax _ _ _ _ _⟩

/-- The value a read of byte `accAddr base j` returns. -/
theorem candReadOf (c : Cand) (k : Nat) (s : Estep) (base : Int) (ts : List Nat)
    (vs : List (BitVec 8)) (j t : Nat) :
    c.cdTr[k]? = some s → lbRd s.esLb = some (base, ts, vs) → vs.length = ts.length →
    ts[j]? = some t → ∃ v, readsAt 𝓔 k (accAddr base j) t v := by
  intro hs hrd hlen hj
  have hjl : j < vs.length := by rw [hlen]; exact lookup_lt_Some hj
  exact ⟨vs[j], s, base, ts, vs, j, hs, hrd, hj, List.getElem?_eq_getElem hjl, rfl⟩

/-- THE LOAD ARM, WITH FORWARDING. -/
theorem invLoadFold (c : Cand) (hrft : axRfTotal 𝓔) (hcohax : axCoherence 𝓔)
    (hordax : axOrd 𝓔) (hrelax : axRelOrd 𝓔) (k : Nat) (s : Estep) (base : Int)
    (ts : List Nat) (vs : List (BitVec 8)) (aq : Bool) (i : Nat) :
    c.cdTr[k]? = some s → s.esAg = i →
    lbRd s.esLb = some (base, ts, vs) → vs.length = ts.length →
    lbAq s.esLb = aq →
    (∀ a t v, readsAt 𝓔 k a t v →
      fwdView (ews 𝓔 k i) aq a t = 0 ∨ (fwdView (ews 𝓔 k i) aq a t = t ∧ pubR 𝓔 (ev_at k) t)) →
    inv c k i →
    invw c (k + 1) i (loadPostRun (ews 𝓔 k i) aq base ts) := by
  intro hs hag hrd hlen haq hnf hinv
  have hinv' := hinv
  obtain ⟨hc, hrn, hro, hwo, hrel⟩ := hinv'
  -- AN EMPTY READ MOVES NOTHING
  by_cases hnil : ts = []
  · subst hnil
    exact invwCtrlPost c (k + 1) i (ews 𝓔 k i) _ (invwWk c k (k + 1) i _ (by omega) hinv)
  -- THE RELEASE CHANNEL
  have hrdb : ∃ a, rdB 𝓔 a (ev_at k) := by
    cases ts with
    | nil => exact absurd rfl hnil
    | cons t0 ts' =>
      obtain ⟨v, hr⟩ := candReadOf c k s base (t0 :: ts') vs 0 t0 hs hrd hlen rfl
      exact ⟨accAddr base 0, k, t0, v, rfl, hr⟩
  have hreldel : ordDom 𝓔 i (k + 1) (if aq then (ews 𝓔 k i).wVRel else 0) := by
    cases aq with
    | false => exact .inl rfl
    | true => exact relsrcAcq 𝓔 i k s _ hs hag (lbRdIsR _ _ hrd) haq hrdb hrel
  -- per-byte facts
  have hread : ∀ p ∈ loadRunAts base ts, ∃ v, readsAt 𝓔 k p.1 p.2 v := by
    intro p hp
    obtain ⟨j, hj, hpa⟩ := elemOfZipSeq base ts p hp
    rw [hpa]
    exact candReadOf c k s base ts vs j p.2 hs hrd hlen hj
  have hsplit : ∀ p ∈ loadRunAts base ts,
      fwdView (ews 𝓔 k i) aq p.1 p.2 = 0 ∨
      (fwdView (ews 𝓔 k i) aq p.1 p.2 = p.2 ∧ pubR 𝓔 (ev_at k) p.2) := by
    intro p hp
    obtain ⟨v, hr⟩ := hread p hp
    exact hnf _ _ v hr
  have hfrd : ∀ p ∈ loadRunAts base ts, frdomB 𝓔 i (k + 1) p.1 p.2 := by
    intro p hp
    obtain ⟨v, hr⟩ := hread p hp
    rw [← hag]
    exact touchFrdom c hrft hcohax k s p.1 p.2 hs (.inl ⟨v, hr⟩)
  have hrs : ∀ p ∈ loadRunAts base ts, pubR 𝓔 (ev_at k) p.2 → rsrc 𝓔 i (k + 1) p.2 := by
    intro p _ hpub
    exact .inr ⟨k, s, p.2, by omega, hs, hag, hpub, Nat.le_refl _⟩
  -- the five conjuncts
  apply invwCtrlPost
  show invw c (k + 1) i ((loadRunAts base ts).foldl
    (fun w at_ => loadPostAt w aq (loadVpre (ews 𝓔 k i) aq) at_.1 at_.2) (ews 𝓔 k i))
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro a
    apply loadFoldCoh' _ aq _ _ _ a (maxclFrdomB c i (k + 1) a)
    · intro p hp heq; rw [← heq]; exact hfrd p hp
    · intro p hp heq
      rcases hsplit p hp with h0 | ⟨ht, _⟩
      · rw [h0]; exact maxcl0 _ (maxclFrdomB c i (k + 1) a)
      · rw [ht, ← heq]; exact hfrd p hp
    · exact frdomBWk _ _ _ _ _ _ (by omega) (hc a)
    · rw [loadVpre]
      exact maxclMax _ _ _ (maxclFrdomB c i (k + 1) a)
        (ordDomFrdom _ _ _ _ hordax hrelax (ordDomWk _ _ _ _ _ (by omega) hrn) a)
        (ordDomFrdom _ _ _ _ hordax hrelax hreldel a)
  · cases aq with
    | false =>
      rw [loadFoldVrNewPlain]; exact ordDomWk _ _ _ _ _ (by omega) hrn
    | true =>
      apply loadFoldVrNew' _ true _ _ _ (maxclOrdDom c i (k + 1))
      · intro p hp
        rcases hsplit p hp with h0 | ⟨ht, hpub⟩
        · rw [h0]; exact maxcl0 _ (maxclOrdDom c i (k + 1))
        · rw [ht, ← hag]
          exact acqOrdDom 𝓔 s.esAg k s p.2 hs rfl (lbRdIsR _ _ hrd) haq hpub
      · exact ordDomWk _ _ _ _ _ (by omega) hrn
      · rw [loadVpre]
        exact maxclMax _ _ _ (maxclOrdDom c i (k + 1)) (ordDomWk _ _ _ _ _ (by omega) hrn) hreldel
  · apply loadFoldVrOld' _ aq _ _ _ (maxclRdom c i (k + 1))
    · intro p hp
      rcases hsplit p hp with h0 | ⟨ht, hpub⟩
      · rw [h0]; exact maxcl0 _ (maxclRdom c i (k + 1))
      · rw [ht]; exact .inr (hrs p hp hpub)
    · exact rdomWk _ _ _ _ _ (by omega) hro
    · rw [loadVpre]
      exact maxclMax _ _ _ (maxclRdom c i (k + 1)) (.inl (ordDomWk _ _ _ _ _ (by omega) hrn))
        (.inl hreldel)
  · rw [loadFoldVwOld]; exact wsrcWk _ _ _ _ _ (by omega) hwo
  · rw [loadFoldVRel]; exact relsrcWk _ _ _ _ _ (by omega) hrel

/-- THE STORE ARM. -/
theorem invStoreFold (c : Cand) (hrft : axRfTotal 𝓔) (hcohax : axCoherence 𝓔) (k : Nat)
    (s : Estep) (base : Int) (vs : List (BitVec 8)) (rl : Bool) (i : Nat) (ws : Wstate) :
    c.cdTr[k]? = some s → s.esAg = i →
    lbWr s.esLb = some (base, vs) → lbRl s.esLb = rl →
    invw c (k + 1) i ws →
    invw c (k + 1) i (storePostRun ws rl base vs.length (evTs 𝓔 (ev_at k))) := by
  rintro hs hag hwr hrlb ⟨hc, hrn, hro, hwo, hrel⟩
  have hm : esWmsg s = some ⟨base, vs, some s.esAg, lbCls s.esLb⟩ := by
    unfold esWmsg; rw [hwr]
  have hW : isW 𝓔 (ev_at k) := ⟨s, hs, lbWrIsW _ _ hwr⟩
  have hpw : pubW 𝓔 (ev_at k) (evTs 𝓔 (ev_at k)) := ⟨hW, ⟨k, rfl⟩, rfl⟩
  have hwsT : wsrc 𝓔 i (k + 1) (evTs 𝓔 (ev_at k)) :=
    .inr ⟨k, s, _, by omega, hs, hag, hpw, Nat.le_refl _⟩
  apply invwCtrlPost
  show invw c (k + 1) i ((storeRunAs base vs.length).foldl
    (fun w a => storePost w rl a (evTs 𝓔 (ev_at k))) ws)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro a
    apply storeFoldCoh _ rl _ _ ws a (maxclFrdomB c i (k + 1) a) (hc a)
    intro hin
    obtain ⟨j, hj, rfl⟩ := elemOfMapSeq base vs.length a hin
    rw [← hag]
    exact touchFrdom c hrft hcohax k s _ _ hs
      (.inr ⟨candWrB c k s _ _ hs hm (msgByteInRange _ _ _ _ j hj), rfl⟩)
  · rw [storeFoldVrNew]; exact hrn
  · rw [storeFoldVrOld]; exact hro
  · exact storeFoldVwOld _ rl _ _ ws (maxclWsrc c i (k + 1)) hwo hwsT
  · apply storeFoldVRel _ rl _ _ ws (maxclRelsrc c i (k + 1)) hrel
    intro hrl
    exact .inr ⟨k, s, _, by omega, hs, hag, lbWrIsW _ _ hwr, by rw [hrlb, hrl], hpw, Nat.le_refl _⟩

/-! ### The fence arm — where PENDING becomes DELIVERED -/

theorem cohFencePost (ws : Wstate) (pr pw sr sw : Bool) (a : Int) :
    coh (fencePost ws pr pw sr sw) a = coh ws a := rfl

theorem invFence (c : Cand) (k : Nat) (s : Estep) (pr pw sr sw : Bool) (i : Nat) :
    c.cdTr[k]? = some s → s.esAg = i → s.esLb = LFence pr pw sr sw →
    inv c k i → invw c (k + 1) i (fencePost (ews 𝓔 k i) pr pw sr sw) := by
  rintro hs hag hl ⟨hc, hrn, hro, hwo, hrel⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro a; rw [cohFencePost]; exact frdomBWk _ _ _ _ _ _ (by omega) (hc a)
  · apply fencePostVrNewPred _ _ pr pw sr sw (maxclOrdDom c i (k + 1))
      (ordDomWk _ _ _ _ _ (by omega) hrn)
    · intro hpr hsr
      subst hpr hsr
      rcases hro with hd | hp
      · exact ordDomWk _ _ _ _ _ (by omega) hd
      · exact rsrcFence 𝓔 i k s pw sw _ hs hag hl hp
    · intro hpw hsr
      subst hpw hsr
      exact wsrcFence 𝓔 i k s pr sw _ hs hag hl hwo
  · exact rdomWk _ _ _ _ _ (by omega) hro
  · exact wsrcWk _ _ _ _ _ (by omega) hwo
  · exact relsrcWk _ _ _ _ _ (by omega) hrel

/-! ### One step of the invariant, all four label arms -/

theorem invStep (c : Cand) (hrft : axRfTotal 𝓔) (hcohax : axCoherence 𝓔) (hordax : axOrd 𝓔)
    (hrelax : axRelOrd 𝓔) (hshape : candShape c) (k : Nat) (s : Estep) (i : Nat) :
    c.cdTr[k]? = some s →
    (∀ a t v, readsAt 𝓔 k a t v →
      fwdView (ews 𝓔 k s.esAg) (lbAq s.esLb) a t = 0 ∨
      (fwdView (ews 𝓔 k s.esAg) (lbAq s.esLb) a t = t ∧ pubR 𝓔 (ev_at k) t)) →
    inv c k i → inv c (k + 1) i := by
  intro hs hnf hinv
  by_cases hi : i = s.esAg
  · subst hi
    have hsh := hshape k s hs
    unfold inv
    cases hl : s.esLb with
    | LLoad aq base ts vs =>
      rw [hl] at hsh
      rw [candWsLoad c k s aq base ts vs hs hl]
      exact invLoadFold c hrft hcohax hordax hrelax k s base ts vs aq s.esAg hs rfl
        (by rw [hl]; rfl) hsh (by rw [hl]; rfl)
        (fun a t v hr => by have := hnf a t v hr; rw [hl] at this; exact this) hinv
    | LStore rl base vs kc =>
      rw [candWsStore c k s rl base vs kc hs hl]
      exact invStoreFold c hrft hcohax k s base vs rl s.esAg _ hs rfl (by rw [hl]; rfl)
        (by rw [hl]; rfl) (invwWk c k (k + 1) _ _ (by omega) hinv)
    | LFence pr pw sr sw =>
      rw [candWsFence c k s pr pw sr sw hs hl]
      exact invFence c k s pr pw sr sw s.esAg hs rfl hl hinv
    | LRmw aq rl base ts rvs wvs kc =>
      rw [hl] at hsh
      obtain ⟨_, _, hlenr⟩ := hsh
      rw [candWsRmw c k s aq rl base ts rvs wvs kc hs hl]
      apply invStoreFold c hrft hcohax k s base wvs rl s.esAg _ hs rfl (by rw [hl]; rfl)
        (by rw [hl]; rfl)
      exact invLoadFold c hrft hcohax hordax hrelax k s base ts rvs aq s.esAg hs rfl
        (by rw [hl]; rfl) hlenr (by rw [hl]; rfl)
        (fun a t v hr => by have := hnf a t v hr; rw [hl] at this; exact this) hinv
    | LIo => rw [hl] at hsh; exact hsh.elim
  · unfold inv; rw [candWsNe c k s i hs hi]
    exact invwWk c k (k + 1) i _ (by omega) hinv

/-! # 10. THE VIEW-DOMINATION LEMMA, and the discharge of `readable` -/

theorem invUpto (c : Cand) (hval : candValues c) (hrft : axRfTotal 𝓔) (hcohax : axCoherence 𝓔)
    (hordax : axOrd 𝓔) (hrelax : axRelOrd 𝓔) (hshape : candShape c) (n : Nat) :
    n ≤ c.cdTr.length → ∀ k i, k ≤ n → inv c k i := by
  intro hn k
  induction k with
  | zero =>
    intro i _
    unfold inv invw
    rw [candWsInit c i]
    exact ⟨fun a => by rw [cohInit]; exact frdomB0 _ _ _ _, .inl rfl, .inl (.inl rfl), .inl rfl,
      .inl rfl⟩
  | succ k ih =>
    intro i hk
    obtain ⟨s, hs⟩ := someOfIsSome (lookup_lt_is_Some_2 (l := c.cdTr) (i := k) (by omega))
    refine invStep c hrft hcohax hordax hrelax hshape k s i hs ?_ (ih i (by omega))
    intro a t v hr
    exact candReadSplit c hval hrft hcohax k s a t v (by omega) hs hr

/-- The read at step `n` is admissible. -/
theorem candRdOk (c : Cand) (hval : candValues c) (hrft : axRfTotal 𝓔) (hcohax : axCoherence 𝓔)
    (hordax : axOrd 𝓔) (hrelax : axRelOrd 𝓔) (hshape : candShape c) (n : Nat) (s : Estep)
    (base : Int) (ts : List Nat) (vs : List (BitVec 8)) :
    n ≤ c.cdTr.length →
    (∀ k s', k < n → c.cdTr[k]? = some s' → mstepOk (stt 𝓔 k) s'.esAg s'.esLb) →
    c.cdTr[n]? = some s → lbRd s.esLb = some (base, ts, vs) →
    vs.length = ts.length →
    rdOk (stt 𝓔 n).msImg (stt 𝓔 n).msLog ((stt 𝓔 n).msWs s.esAg) (lbAq s.esLb) base ts vs := by
  intro hn hok hs hrd hlen
  have hnlt := lookup_lt_Some hs
  have himg : (stt 𝓔 n).msImg = c.cdImg := candEimg c n hn
  have hlog : (stt 𝓔 n).msLog = cdLog c n := candElog c n hn
  have hb := candBoundedUpto c n hn hok
  have hbnd : wsBounded (ews 𝓔 n s.esAg) (cdLog c n).length := by
    have := hb s.esAg; rw [hlog] at this; exact this
  show rdOk _ _ (ews 𝓔 n s.esAg) _ _ _ _
  obtain ⟨hc, hrn, _, _, hrel⟩ :=
    invUpto c hval hrft hcohax hordax hrelax hshape n hn n s.esAg (Nat.le_refl _)
  refine ⟨hlen, fun j t v hj hv => ?_⟩
  have hr : readsAt 𝓔 n (accAddr base j) t v := ⟨s, base, ts, vs, j, hs, hrd, hj, hv, rfl⟩
  have hlb : logByte c.cdImg (cdLog c n) t (accAddr base j) = some v :=
    hval n s base ts vs hs hrd j t v hj hv
  -- the floor is a real timestamp, and it is dominated
  have hfloor : max (loadVpre (ews 𝓔 n s.esAg) (lbAq s.esLb))
      (coh (ews 𝓔 n s.esAg) (accAddr base j)) ≤ (cdLog c n).length := by
    have := loadVpreBounded _ (lbAq s.esLb) _ hbnd
    have := hbnd.2.2.2.2.2.2.1 (accAddr base j)
    omega
  rw [himg, hlog]
  refine ⟨hlb, by rw [hlb]; rfl, fun hw => ?_⟩
  obtain ⟨w, hwb, hgt, hle⟩ := candWritesInWr c n (accAddr base j) t _ hn hw
  -- the `fr` edge from this step to `w`
  obtain ⟨w0, hrf0⟩ := hrft n (accAddr base j) t v hr
  have hts0 : evTs 𝓔 w0 = t := by
    have hrf0' := hrf0
    obtain ⟨_, k0, t0, v0, hkeq, hr0, hts0⟩ := hrf0'
    injection hkeq with hkeq; subst hkeq
    exact hts0.trans (readsAtDet 𝓔 n _ t0 v0 t v hr0 hr).1
  have hne : ev_at n ≠ w := by
    intro heq; subst heq; rw [candEvTs c n hn] at hle; omega
  have hfr : frB 𝓔 (accAddr base j) (ev_at n) w := ⟨⟨w0, hrf0, hrf0.1, hwb, by omega⟩, hne⟩
  -- ... contradicted by the three dominating conjuncts
  have h1 := hc (accAddr base j) n s w (Nat.le_refl _) hs rfl hfr
  have h2 := ordDomFrdom 𝓔 s.esAg n _ hordax hrelax hrn (accAddr base j) n s w
    (Nat.le_refl _) hs rfl hfr
  have hvpre : loadVpre (ews 𝓔 n s.esAg) (lbAq s.esLb) < evTs 𝓔 w := by
    unfold loadVpre
    cases haq : lbAq s.esLb with
    | false => simp only [Bool.false_eq_true, ↓reduceIte]; omega
    | true =>
      have := relsrcFrdomAt 𝓔 s.esAg n s _ hrelax hs rfl (lbRdIsR _ _ hrd) haq hrel
        (accAddr base j) w hfr
      simp only [↓reduceIte]
      omega
  omega

/-- The RMW's atomicity side condition is `axAtomicity`, read at the one place
it bites. -/
theorem candRmwLatest (c : Cand) (hval : candValues c) (hrft : axRfTotal 𝓔)
    (hatom : axAtomicity 𝓔) (n : Nat) (s : Estep) (base : Int) (ts : List Nat)
    (vs : List (BitVec 8)) :
    n ≤ c.cdTr.length →
    (∀ k s', k < n → c.cdTr[k]? = some s' → mstepOk (stt 𝓔 k) s'.esAg s'.esLb) →
    c.cdTr[n]? = some s → lbRd s.esLb = some (base, ts, vs) →
    lbIsW s.esLb = true → vs.length = ts.length →
    rmwLatest (stt 𝓔 n).msImg (stt 𝓔 n).msLog base ts := by
  intro hn _ hs hrd hisw hlen
  have hnlt := lookup_lt_Some hs
  have himg : (stt 𝓔 n).msImg = c.cdImg := candEimg c n hn
  have hlog : (stt 𝓔 n).msLog = cdLog c n := candElog c n hn
  have hW : isW 𝓔 (ev_at n) := ⟨s, hs, hisw⟩
  intro j t hj
  have hjl : j < vs.length := by rw [hlen]; exact lookup_lt_Some hj
  have hr : readsAt 𝓔 n (accAddr base j) t vs[j] :=
    ⟨s, base, ts, vs, j, hs, hrd, hj, List.getElem?_eq_getElem hjl, rfl⟩
  have hlb := hval n s base ts vs hs hrd j t vs[j] hj (List.getElem?_eq_getElem hjl)
  rw [himg, hlog]
  refine ⟨by rw [hlb]; rfl, fun hw => ?_⟩
  obtain ⟨w, hwb, hgt, hle⟩ := candWritesInWr c n (accAddr base j) t _ hn hw
  obtain ⟨w0, hrf0⟩ := hrft n (accAddr base j) t vs[j] hr
  have hts0 : evTs 𝓔 w0 = t := by
    have hrf0' := hrf0
    obtain ⟨_, k0, t0, v0, hkeq, hr0, hts0⟩ := hrf0'
    injection hkeq with hkeq; subst hkeq
    exact hts0.trans (readsAtDet 𝓔 n _ t0 v0 t _ hr0 hr).1
  apply hatom n (accAddr base j) w0 w hW hrf0 hwb (by omega)
  rw [candEvTs c n hn]; omega

/-! ### Every step is admissible -/

theorem candMstepOkAt (c : Cand) (hval : candValues c) (hrft : axRfTotal 𝓔)
    (hcohax : axCoherence 𝓔) (hordax : axOrd 𝓔) (hrelax : axRelOrd 𝓔) (hshape : candShape c)
    (hatom : axAtomicity 𝓔) (n : Nat) (s : Estep) :
    n ≤ c.cdTr.length →
    (∀ k s', k < n → c.cdTr[k]? = some s' → mstepOk (stt 𝓔 k) s'.esAg s'.esLb) →
    c.cdTr[n]? = some s → mstepOk (stt 𝓔 n) s.esAg s.esLb := by
  intro hn hok hs
  have hsh := hshape n s hs
  cases hl : s.esLb with
  | LLoad aq base ts vs =>
    rw [hl] at hsh
    have hh := candRdOk c hval hrft hcohax hordax hrelax hshape n s base ts vs hn hok hs
      (by rw [hl]; rfl) hsh
    rw [hl] at hh
    exact hh
  | LStore rl base vs kc => rw [hl] at hsh; exact hsh
  | LFence => trivial
  | LRmw aq rl base ts rvs wvs kc =>
    rw [hl] at hsh
    obtain ⟨hne0, hlenw, hlenr⟩ := hsh
    have hh := candRdOk c hval hrft hcohax hordax hrelax hshape n s base ts rvs hn hok hs
      (by rw [hl]; rfl) hlenr
    rw [hl] at hh
    exact ⟨hne0, hlenw, hh, candRmwLatest c hval hrft hatom n s base ts rvs hn hok hs
      (by rw [hl]; rfl) (by rw [hl]; rfl) hlenr⟩
  | LIo => rw [hl] at hsh; exact hsh.elim

theorem candMstepOk (c : Cand) (hval : candValues c) (hrft : axRfTotal 𝓔)
    (hcohax : axCoherence 𝓔) (hordax : axOrd 𝓔) (hrelax : axRelOrd 𝓔) (hshape : candShape c)
    (hatom : axAtomicity 𝓔) :
    ∀ n k s, k < n → c.cdTr[k]? = some s → mstepOk (stt 𝓔 k) s.esAg s.esLb := by
  intro n
  induction n with
  | zero => intro k s hk; omega
  | succ n ih =>
    intro k s hk hs
    by_cases hlt : k < n
    · exact ih k s hlt hs
    have : k = n := by omega
    subst this
    have hnlt := lookup_lt_Some hs
    exact candMstepOkAt c hval hrft hcohax hordax hrelax hshape hatom k s (by omega)
      (fun k' s' hk' hs' => ih k' s' hk' hs') hs

/-! ## THE THEOREM (for this section's hypotheses) -/

theorem completeClean (c : Cand) (hval : candValues c) (hrft : axRfTotal 𝓔)
    (hcohax : axCoherence 𝓔) (hordax : axOrd 𝓔) (hrelax : axRelOrd 𝓔) (hshape : candShape c)
    (hatom : axAtomicity 𝓔) :
    execWf 𝓔 ∧ (𝓔).exTr = c.cdTr ∧ exImg 𝓔 = c.cdImg := by
  apply candReachable
  intro k s hs
  exact candMstepOk c hval hrft hcohax hordax hrelax hshape hatom (k + 1) k s (by omega) hs

/-! # 11. Slice 2 §9(1)'s statement, and the theorem this file proves -/

def candAxiomaticOk (c : Cand) : Prop :=
  axiomaticOk (candExec c) ∧ axRelOrd (candExec c) ∧ (∀ o, ¬ tc (obOp (candExec c)) o o)

/-- THE COMPLETENESS THEOREM OF THIS SLICE, PREMISE-FREE. -/
theorem promiseFreeCompleteClean (c : Cand) :
    candShape c → candValues c → candAxiomaticOk c →
    execWf (candExec c) ∧ (candExec c).exTr = c.cdTr ∧ exImg (candExec c) = c.cdImg := by
  rintro hsh hval ⟨⟨hrft, _, _, hcohax, hatom, hordax, _, _⟩, hrelax, _⟩
  exact completeClean c hval hrft hcohax hordax hrelax hsh hatom

/-- ... and with the hypothesis pared down to what the proof uses.  FINDING:
`ob`-acyclicity is NOT needed — five LOCAL axioms are. -/
theorem promiseFreeCompleteLocal (c : Cand) :
    candShape c → candValues c →
    axRfTotal (candExec c) → axCoherence (candExec c) →
    axOrd (candExec c) → axRelOrd (candExec c) → axAtomicity (candExec c) →
    execWf (candExec c) ∧ (candExec c).exTr = c.cdTr ∧ exImg (candExec c) = c.cdImg := by
  intro hsh hval hrft hcohax hordax hrelax hatom
  exact completeClean c hval hrft hcohax hordax hrelax hsh hatom

/-! # 12. Which axioms a candidate satisfies for free -/

theorem candRfTotal (c : Cand) : candValues c → axRfTotal (candExec c) := by
  intro hval k a t v hr
  have hr' := hr
  obtain ⟨s, base, ts, vs, j, hs, hrd, hj, hv, ha⟩ := hr'
  have hlb := hval k s base ts vs hs hrd j t v hj hv
  rw [← ha] at hlb
  have hk : k < c.cdTr.length := lookup_lt_Some hs
  cases t with
  | zero =>
    refine ⟨ev_init, candWrBInit c a ?_, k, 0, v, rfl, hr, rfl⟩
    rw [logByte0] at hlb; rw [hlb]; rfl
  | succ i =>
    have htlen := logByteBounded _ _ _ _ (by rw [hlb]; rfl : (logByte c.cdImg (cdLog c k) (i + 1) a).isSome)
    obtain ⟨k', s', m, hk', hs', hm, hts⟩ := candTsWriter c k (i + 1) (by omega) (by omega) htlen
    refine ⟨ev_at k', candWrB c k' s' m a hs' hm ?_, k, i + 1, v, rfl, hr, hts⟩
    rw [← candLogByteWr c k' s' m k a hs' hm (by omega), hts, hlb]; rfl

theorem candRfFunctional (c : Cand) : axRfFunctional (candExec c) := by
  intro a w1 w2 r h1 h2
  obtain ⟨hw1, k1, t1, v1, rfl, hr1, hts1⟩ := h1
  obtain ⟨hw2, k2, t2, v2, hkeq, hr2, hts2⟩ := h2
  injection hkeq with hkeq; subst hkeq
  have := (readsAtDet (candExec c) k1 a t1 v1 t2 v2 hr1 hr2).1
  exact candTsInj c (a, w1) (a, w2) hw1 hw2 (by simp only; omega)

theorem candRfValue (c : Cand) : candValues c → axRfValue (candExec c) := by
  intro hval k a w t v hr hrf
  obtain ⟨hw, k0, t0, v0, hkeq, hr0, hts⟩ := hrf
  injection hkeq with hkeq; subst hkeq
  obtain ⟨heqt, _⟩ := readsAtDet (candExec c) k a t0 v0 t v hr0 hr
  rw [heqt] at hts
  have hr' := hr
  obtain ⟨s, base, ts, vs, j, hs, hrd, hj, hv, ha⟩ := hr'
  have hk : k < c.cdTr.length := lookup_lt_Some hs
  have hlb := hval k s base ts vs hs hrd j t v hj hv
  rw [← ha] at hlb
  rw [hts, candExImg, candExLog]
  obtain ⟨l, hl⟩ := cdLogSplit c k c.cdTr.length (by omega)
  have htlen := logByteBounded _ _ _ _ (by rw [hlb]; rfl : (logByte c.cdImg (cdLog c k) t a).isSome)
  rw [hl, logByteApp _ _ _ _ _ htlen]
  exact hlb

theorem candRfIx (c : Cand) (a : Int) (w : Ev) (k : Nat) :
    candValues c → rfB (candExec c) a w (ev_at k) → evIx w < evIx (ev_at k) := by
  intro hval hrf
  obtain ⟨hw, k0, t, v, hkeq, hr, hts⟩ := hrf
  injection hkeq with hkeq; subst hkeq
  cases w with
  | ev_init => simp [evIx]
  | ev_at k' =>
    have htlen := candReadTsLe c hval k a t v hr
    have := candWrLt c k a k' hw (by omega)
    simp only [evIx]; omega

theorem candNoThinAir (c : Cand) : candValues c → axNoThinAir (candExec c) := by
  intro hval
  apply tcNatLt _ evIx
  rintro x y (hpo | ⟨a, hrf⟩)
  · exact poIx (candExec c) x y hpo
  · have hrf' := hrf
    obtain ⟨_, k, _, _, rfl, _, _⟩ := hrf'
    exact candRfIx c a x k hval hrf

theorem candPoWwGmo (c : Cand) : axPoWwGmo (candExec c) := by
  rintro e1 e2 ⟨k1, k2, s1, s2, rfl, rfl, hlt, hs1, hs2, _⟩ hW1 hW2
  refine ⟨hW1, hW2, ?_⟩
  obtain ⟨s, hs, hw⟩ := hW1
  rw [hs1] at hs; injection hs with hs; subst hs
  cases hm : esWmsg s1 with
  | none => rw [esWmsgNone s1 hm] at hw; cases hw
  | some m =>
    have : k2 < c.cdTr.length := lookup_lt_Some hs2
    exact candTsMono c k1 k2 s1 m hs1 hm hlt (by omega)

/-- Acyclicity for the SIMPLE shape the counterexamples have (coherence). -/
theorem cohRelAcycSimple (c : Cand) (a : Int) :
    candValues c →
    (∀ e1 e2, poLocB (candExec c) a e1 e2 → ets (candExec c) a e1 ≤ ets (candExec c) a e2) →
    (∀ e, wrB (candExec c) a e → ¬ rdB (candExec c) a e) →
    ∀ e, ¬ tc (cohRel (candExec c) a) e e := by
  intro hval hnpl hnrw
  apply tcLexlt _ (fun e => (ets (candExec c) a e, evIx e))
  intro x y hxy
  rcases hxy with hpl | hrf | hco | hfr
  · have hle := hnpl x y hpl
    have := poIx (candExec c) x y hpl.1
    unfold lexlt; simp only; omega
  · obtain ⟨hw, k, t, v, hkeq, hr, hts⟩ := hrf
    subst hkeq
    have hnw : ¬ wrB (candExec c) a (ev_at k) := fun hwx => hnrw _ hwx ⟨k, t, v, rfl, hr⟩
    unfold lexlt
    simp only
    rw [etsWr (candExec c) a x hw, hts, etsRd (candExec c) a k t v hnw hr]
    right
    exact ⟨rfl, candRfIx c a x k hval ⟨hw, k, t, v, rfl, hr, hts⟩⟩
  · obtain ⟨hw1, hw2, hlt⟩ := hco
    unfold lexlt; simp only
    rw [etsWr (candExec c) a x hw1, etsWr (candExec c) a y hw2]
    exact .inl hlt
  · obtain ⟨⟨w0, hrf0, hw0, hw2, hlt⟩, _⟩ := hfr
    obtain ⟨_, k, t, v, hkeq, hr, hts0⟩ := hrf0
    subst hkeq
    have hnw : ¬ wrB (candExec c) a (ev_at k) := fun hwx => hnrw _ hwx ⟨k, t, v, rfl, hr⟩
    unfold lexlt; simp only
    rw [etsWr (candExec c) a y hw2, etsRd (candExec c) a k t v hnw hr]
    left; omega

/-- Acyclicity for the SIMPLE shape (`ob`, no `ppoOp` edge at all). -/
theorem obOpAcycSimple (c : Cand) :
    candValues c →
    (∀ o1 o2, ¬ ppoOp (candExec c) o1 o2) →
    (∀ a e, wrB (candExec c) a e → ¬ rdB (candExec c) a e) →
    ∀ o, ¬ tc (obOp (candExec c)) o o := by
  intro hval hnppo hnrw
  apply tcKless _ (fun o => (ets (candExec c) o.1 o.2, ophase (candExec c) o.1 o.2, evIx o.2, o.1))
  rintro ⟨a1, e1⟩ ⟨a2, e2⟩ (hppo | ⟨ha, hrf⟩ | ⟨ha, hco⟩ | ⟨ha, hfr⟩)
  · exact absurd hppo (hnppo _ _)
  · simp only at ha hrf; subst ha
    obtain ⟨hw, k, t, v, hkeq, hr, hts⟩ := hrf
    subst hkeq
    have hnw : ¬ wrB (candExec c) a1 (ev_at k) := fun hwx => hnrw _ _ hwx ⟨k, t, v, rfl, hr⟩
    unfold kless; simp only
    rw [etsWr (candExec c) a1 e1 hw, ophaseWr (candExec c) a1 e1 hw,
      ophaseNwr (candExec c) a1 _ hnw, hts, etsRd (candExec c) a1 k t v hnw hr]
    omega
  · simp only at ha hco; subst ha
    obtain ⟨hw1, hw2, hlt⟩ := hco
    unfold kless; simp only
    rw [etsWr (candExec c) a1 e1 hw1, etsWr (candExec c) a1 e2 hw2]
    exact .inl hlt
  · simp only at ha hfr; subst ha
    obtain ⟨⟨w0, hrf0, hw0, hw2, hlt⟩, _⟩ := hfr
    obtain ⟨_, k, t, v, hkeq, hr, hts0⟩ := hrf0
    subst hkeq
    have hnw : ¬ wrB (candExec c) a1 (ev_at k) := fun hwx => hnrw _ _ hwx ⟨k, t, v, rfl, hr⟩
    unfold kless; simp only
    rw [etsWr (candExec c) a1 e2 hw2, etsRd (candExec c) a1 k t v hnw hr]
    omega

/-! # 13. THE RELEASE/ACQUIRE WITNESS, on both sides of the model

Three steps, two bytes, no fence: ts 1 — agent 1 stores byte 0; ts 2 — agent 0
stores byte 1, `rl` iff the section's `rl` is set; then agent 0 ACQUIRE-loads
byte 0 and reads timestamp 0 (the image).  `rl = true`: MACHINE-BLOCKED
(`ceRlBlocked`) AND AXIOMATICALLY INCONSISTENT (`ceRlTrueInconsistent`).
`rl = false`: MACHINE-REACHABLE (`ceRlStaleReachable`) and not an SC
candidate. -/

def ceRlTr (rl : Bool) (v : BitVec 8) : List Estep :=
  [⟨1, LStore false 0 [v] .WCplain⟩,
   ⟨0, LStore rl 1 [v] .WCplain⟩,
   ⟨0, LLoad true 0 [0] [v]⟩]

def ceRl (rl : Bool) (v : BitVec 8) : Cand := ⟨fun _ => some v, ceRlTr rl v⟩

theorem ceRlTrInv (rl : Bool) (v : BitVec 8) (k : Nat) (s : Estep) :
    (ceRl rl v).cdTr[k]? = some s →
    (k = 0 ∧ s = ⟨1, LStore false 0 [v] .WCplain⟩) ∨
    (k = 1 ∧ s = ⟨0, LStore rl 1 [v] .WCplain⟩) ∨
    (k = 2 ∧ s = ⟨0, LLoad true 0 [0] [v]⟩) := by
  intro hs
  simp only [ceRl, ceRlTr] at hs
  match k, hs with
  | 0, hs => simp only [List.getElem?_cons_zero, Option.some.injEq] at hs; exact .inl ⟨rfl, hs.symm⟩
  | 1, hs =>
    simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hs
    exact .inr (.inl ⟨rfl, hs.symm⟩)
  | 2, hs =>
    simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hs
    exact .inr (.inr ⟨rfl, hs.symm⟩)
  | k + 3, hs => simp at hs

theorem ceRlShape (rl : Bool) (v : BitVec 8) : candShape (ceRl rl v) := by
  intro k s hs
  rcases ceRlTrInv rl v k s hs with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> simp

theorem ceRlValues (rl : Bool) (v : BitVec 8) : candValues (ceRl rl v) := by
  intro k s base ts vs hs hrd j t v' hj hv'
  rcases ceRlTrInv rl v k s hs with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨rfl, rfl⟩
  · simp [lbRd] at hrd
  · simp [lbRd] at hrd
  · simp only [lbRd, Option.some.injEq, Prod.mk.injEq] at hrd
    obtain ⟨rfl, rfl, rfl⟩ := hrd
    match j, hj, hv' with
    | 0, hj, hv' =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hj hv'
      subst hj hv'
      rfl
    | j + 1, hj, _ => simp at hj

/-- Lean-only: agent 0's state just before the acquire load of `ceRl true v`. -/
theorem ceRlWs02 (v : BitVec 8) :
    (stt (candExec (ceRl true v)) 2).msWs 0 = storePostRun wsInit true 1 [v].length 2 := by
  have h1 := candNext (ceRl true v) 1 ⟨0, LStore true 1 [v] .WCplain⟩ rfl
  have h0 := candNext (ceRl true v) 0 ⟨1, LStore false 0 [v] .WCplain⟩ rfl
  rw [show stt (candExec (ceRl true v)) 2 = stt (candExec (ceRl true v)) (1 + 1) from rfl, h1,
    show stt (candExec (ceRl true v)) 1 = stt (candExec (ceRl true v)) (0 + 1) from rfl, h0,
    candSttInit]
  rfl

/-- The machine's refusal, computed. -/
theorem ceRlBlocked (v : BitVec 8) : ¬ execWf (candExec (ceRl true v)) := by
  intro hwf
  have hstep := execStepAt (candExec (ceRl true v)) 2 ⟨0, LLoad true 0 [0] [v]⟩ hwf rfl
  obtain ⟨_, hok⟩ := mstepDet _ _ _ _ hstep
  obtain ⟨_, hall⟩ := hok
  obtain ⟨_, _, hnw⟩ := hall 0 0 v rfl rfl
  apply hnw
  -- the state after the first two steps, computed from the replay
  have hlog : (stt (candExec (ceRl true v)) 2).msLog = cdLog (ceRl true v) 2 :=
    candElog _ 2 (by simp [ceRl, ceRlTr])
  rw [hlog]
  show writesIn _ (accAddr 0 0) 0 (max (loadVpre ((stt (candExec (ceRl true v)) 2).msWs 0) true)
    (coh ((stt (candExec (ceRl true v)) 2).msWs 0) (accAddr 0 0)))
  rw [ceRlWs02]
  have hfl : max (loadVpre (storePostRun wsInit true 1 [v].length 2) true)
      (coh (storePostRun wsInit true 1 [v].length 2) (accAddr 0 0)) = 2 := by
    show max (loadVpre (storePostRun wsInit true 1 [v].length 2) true)
      (coh (storePost wsInit true (1 + ((0 : Nat) : Int)) 2) (accAddr 0 0)) = 2
    rw [cohStorePostNe _ _ _ _ _ (by simp [accAddr]), cohInit]
    rfl
  rw [hfl]
  exact ⟨1, by omega, by omega, ⟨0, [v], some 1, .WCplain⟩, rfl, by simp [msgByte, accAddr]⟩

theorem WeakAxiomatic3.msgByteSingle (v : BitVec 8) (b : Int) (tid : Option Nat) (k : WmClass) (a : Int) :
    (msgByte ⟨b, [v], tid, k⟩ a).isSome → a = b := by
  intro h
  obtain ⟨j, hj, ha⟩ := msgByteRange _ a h
  simp only [List.length_singleton] at hj
  have : j = 0 := by omega
  subst this; simpa using ha

theorem ceRlNoFence (rl : Bool) (v : BitVec 8) (e1 e2 : Ev) :
    ¬ ordPw (candExec (ceRl rl v)) e1 e2 ∧ ¬ ordPr (candExec (ceRl rl v)) e1 e2 := by
  have hnf : ∀ k1 k2 pr pw sr sw, ¬ fenceBetween (candExec (ceRl rl v)) k1 k2 pr pw sr sw := by
    rintro k1 k2 pr pw sr sw ⟨kf, sf, _, _, _, _, _, hsf, _, _, _, hlf⟩
    rcases ceRlTrInv rl v kf sf hsf with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> simp at hlf
  refine ⟨?_, ?_⟩
  · rintro ⟨k1, k2, pr, sw, _, _, hfb⟩; exact hnf _ _ _ _ _ _ hfb
  · rintro (⟨k1, k2, pw, sw, _, _, hfb⟩ | ⟨k1, k2, s1, s2, rfl, rfl, hlt, hs1, hs2, hag, hisr, haq⟩)
    · exact hnf _ _ _ _ _ _ hfb
    · rcases ceRlTrInv rl v k1 s1 hs1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        rcases ceRlTrInv rl v k2 s2 hs2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        simp_all [lbIsR, lbAq]

theorem ceRlPo (rl : Bool) (v : BitVec 8) (e1 e2 : Ev) :
    po (candExec (ceRl rl v)) e1 e2 → e1 = ev_at 1 ∧ e2 = ev_at 2 := by
  rintro ⟨k1, k2, s1, s2, rfl, rfl, hlt, hs1, hs2, hag⟩
  rcases ceRlTrInv rl v k1 s1 hs1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    rcases ceRlTrInv rl v k2 s2 hs2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    simp_all

theorem ceRlRdB (rl : Bool) (v : BitVec 8) (a : Int) (e : Ev) :
    rdB (candExec (ceRl rl v)) a e → e = ev_at 2 ∧ a = 0 := by
  rintro ⟨k, t, v', rfl, s, base, ts, vs, j, hs, hrd, hj, hv, ha⟩
  rcases ceRlTrInv rl v k s hs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · simp [lbRd] at hrd
  · simp [lbRd] at hrd
  · simp only [lbRd, Option.some.injEq, Prod.mk.injEq] at hrd
    obtain ⟨rfl, rfl, rfl⟩ := hrd
    match j, hj with
    | 0, _ => exact ⟨rfl, by rw [ha]; simp [accAddr]⟩
    | j + 1, hj => simp at hj

theorem ceRlWr2 (rl : Bool) (v : BitVec 8) (a : Int) : ¬ wrB (candExec (ceRl rl v)) a (ev_at 2) := by
  rintro ⟨⟨s, hs, hw⟩, _⟩
  rcases ceRlTrInv rl v 2 s hs with ⟨habs, _⟩ | ⟨habs, _⟩ | ⟨_, rfl⟩
  · omega
  · omega
  · simp [lbIsW] at hw

theorem ceRlWr1 (rl : Bool) (v : BitVec 8) (a : Int) :
    wrB (candExec (ceRl rl v)) a (ev_at 1) → a = 1 := by
  intro hw
  rcases candWrBInv (ceRl rl v) a (ev_at 1) hw with ⟨habs, _⟩ | ⟨k, s, m, heq, hs, hm, hb⟩
  · cases habs
  · injection heq with heq; subst heq
    rcases ceRlTrInv rl v 1 s hs with ⟨habs, _⟩ | ⟨_, rfl⟩ | ⟨habs, _⟩
    · omega
    · simp only [esWmsg, lbWr, lbCls, Option.some.injEq] at hm
      subst hm
      exact WeakAxiomatic3.msgByteSingle v 1 (some 0) .WCplain a hb
    · omega

/-- No same-byte program order, and no event both reads and writes a byte. -/
theorem ceRlNoPoloc (rl : Bool) (v : BitVec 8) (a : Int) (e1 e2 : Ev) :
    ¬ poLocB (candExec (ceRl rl v)) a e1 e2 := by
  rintro ⟨hpo, hacc1, hacc2⟩
  obtain ⟨rfl, rfl⟩ := ceRlPo rl v e1 e2 hpo
  have ha : a = 0 := by
    rcases hacc2 with hw | hr
    · exact absurd hw (ceRlWr2 rl v a)
    · exact (ceRlRdB rl v a _ hr).2
  subst ha
  rcases hacc1 with hw | hr
  · have := ceRlWr1 rl v 0 hw; omega
  · have := (ceRlRdB rl v 0 _ hr).1; simp at this

theorem ceRlNoRw (rl : Bool) (v : BitVec 8) (a : Int) (e : Ev) :
    wrB (candExec (ceRl rl v)) a e → ¬ rdB (candExec (ceRl rl v)) a e := by
  intro hw hr
  obtain ⟨rfl, _⟩ := ceRlRdB rl v a e hr
  exact ceRlWr2 rl v a hw

/-- With no `.rl` anywhere in the trace there is no rule-7 edge. -/
theorem ceRlNoRelAcq (rl : Bool) (v : BitVec 8) (e1 e2 : Ev) :
    rl = false → ¬ relAcqPo (candExec (ceRl rl v)) e1 e2 := by
  rintro hrl ⟨k1, k2, s1, s2, rfl, rfl, hlt, hs1, hs2, hag, _, hrl1, _⟩
  rcases ceRlTrInv rl v k1 s1 hs1 with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;>
    simp_all [lbRl]

theorem ceRlNoRelOrd (rl : Bool) (v : BitVec 8) (e1 e2 : Ev) :
    rl = false → ¬ relOrd (candExec (ceRl rl v)) e1 e2 := by
  rintro hrl (h | ⟨em, h, _, _⟩)
  · exact ceRlNoRelAcq rl v _ _ hrl h
  · exact ceRlNoRelAcq rl v _ _ hrl h

theorem ceRlNoPpo (rl : Bool) (v : BitVec 8) :
    rl = false → ∀ o1 o2, ¬ ppoOp (candExec (ceRl rl v)) o1 o2 := by
  rintro hrl o1 o2 (⟨hpo, hw2⟩ | ⟨_, hpl⟩ | ⟨hord, _⟩ | ⟨hord, _, _⟩ | ⟨hrel, _⟩)
  · obtain ⟨_, heq⟩ := ceRlPo rl v _ _ hpo
    rw [heq] at hw2
    exact ceRlWr2 rl v _ hw2
  · exact ceRlNoPoloc rl v _ _ _ hpl
  · exact (ceRlNoFence rl v _ _).1 hord
  · exact (ceRlNoFence rl v _ _).2 hord
  · exact ceRlNoRelAcq rl v _ _ hrl hrel

theorem ceRlNotW2 (rl : Bool) (v : BitVec 8) : ¬ isW (candExec (ceRl rl v)) (ev_at 2) := by
  rintro ⟨s, hs, hw⟩
  rcases ceRlTrInv rl v 2 s hs with ⟨habs, _⟩ | ⟨habs, _⟩ | ⟨_, rfl⟩
  · omega
  · omega
  · simp [lbIsW] at hw

theorem ceRlAxCoherence (rl : Bool) (v : BitVec 8) : axCoherence (candExec (ceRl rl v)) := by
  intro a e
  exact cohRelAcycSimple (ceRl rl v) a (ceRlValues rl v)
    (fun e1 e2 hpl => absurd hpl (ceRlNoPoloc rl v a e1 e2)) (ceRlNoRw rl v a) e

theorem ceRlAxAtomicity (rl : Bool) (v : BitVec 8) : axAtomicity (candExec (ceRl rl v)) := by
  intro kr a w0 w hW hrf0 _ _
  obtain ⟨_, k, t, v', hkeq, hr, _⟩ := hrf0
  have := (ceRlRdB rl v a (ev_at kr) ⟨k, t, v', hkeq, hr⟩).1
  injection this with this; subst this
  exact absurd hW (ceRlNotW2 rl v)

theorem ceRlAxOrd (rl : Bool) (v : BitVec 8) : axOrd (candExec (ceRl rl v)) := by
  intro e1 k2 s2 a w t _ hcase _
  obtain ⟨hpw, hpr⟩ := ceRlNoFence rl v e1 (ev_at k2)
  rcases hcase with ⟨hord, _⟩ | ⟨hord, _⟩
  · exact absurd hord hpw
  · exact absurd hord hpr

theorem ceRlAxRelOrd (rl : Bool) (v : BitVec 8) : rl = false → axRelOrd (candExec (ceRl rl v)) := by
  intro hrl e1 k2 s2 a w t _ hro _ _
  exact absurd hro (ceRlNoRelOrd rl v e1 (ev_at k2) hrl)

theorem ceRlAxiomaticOk (rl : Bool) (v : BitVec 8) : rl = false → candAxiomaticOk (ceRl rl v) := by
  intro hrl
  refine ⟨⟨candRfTotal _ (ceRlValues rl v), candRfFunctional _, candRfValue _ (ceRlValues rl v),
    ceRlAxCoherence rl v, ceRlAxAtomicity rl v, ceRlAxOrd rl v, candNoThinAir _ (ceRlValues rl v),
    candPoWwGmo _⟩, ceRlAxRelOrd rl v hrl, ?_⟩
  exact obOpAcycSimple (ceRl rl v) (ceRlValues rl v) (ceRlNoPpo rl v hrl) (ceRlNoRw rl v)

/-- The floor the machine computes at the acquire load: `wVRel` = 2. -/
theorem ceRlFloor (v : BitVec 8) :
    max (loadVpre ((stt (candExec (ceRl true v)) 2).msWs 0) true)
      (coh ((stt (candExec (ceRl true v)) 2).msWs 0) 0) = 2 := by
  rw [ceRlWs02]
  show max (loadVpre (storePostRun wsInit true 1 [v].length 2) true)
    (coh (storePost wsInit true (1 + ((0 : Nat) : Int)) 2) 0) = 2
  rw [cohStorePostNe _ _ _ _ _ (by decide), cohInit]
  rfl

/-- An operation of the virtual init event always sits at position 0. -/
theorem oposInit (E : Exec) (a : Int) : opos E a ev_init = 0 := by
  unfold opos ets evpre
  cases writesb E a ev_init <;> rfl

/-- THE WITNESS, ON THE MODEL SIDE: `ceRl true v` fails `candAxiomaticOk`. -/
theorem ceRlTrueInconsistent (v : BitVec 8) : ¬ candAxiomaticOk (ceRl true v) := by
  rintro ⟨_, hrelax, _⟩
  -- the two writes of byte 0: the image, and agent 1's store at timestamp 1
  have hwi : wrB (candExec (ceRl true v)) 0 ev_init := candWrBInit _ 0 rfl
  have hw0 : wrB (candExec (ceRl true v)) 0 (ev_at 0) :=
    candWrB (ceRl true v) 0 ⟨1, LStore false 0 [v] .WCplain⟩ ⟨0, [v], some 1, .WCplain⟩ 0 rfl rfl
      (by simp [msgByte])
  have hts0 : evTs (candExec (ceRl true v)) (ev_at 0) = 1 := by
    rw [candEvTs (ceRl true v) 0 (by simp [ceRl, ceRlTr])]; rfl
  have hts1 : evTs (candExec (ceRl true v)) (ev_at 1) = 2 := by
    rw [candEvTs (ceRl true v) 1 (by simp [ceRl, ceRlTr])]; rfl
  -- the acquire load reads the image, and so is `fr`-before that store
  have hr : readsAt (candExec (ceRl true v)) 2 0 0 v :=
    ⟨⟨0, LLoad true 0 [0] [v]⟩, 0, [0], [v], 0, rfl, rfl, rfl, rfl, by simp [accAddr]⟩
  have hfr : frB (candExec (ceRl true v)) 0 (ev_at 2) (ev_at 0) := by
    refine ⟨⟨ev_init, ⟨hwi, 2, 0, v, rfl, hr, rfl⟩, hwi, hw0, by rw [hts0]; simp [evTs]⟩, ?_⟩
    simp
  -- the rule-7 edge, and the release store's publication
  have hra : relAcqPo (candExec (ceRl true v)) (ev_at 1) (ev_at 2) :=
    ⟨1, 2, ⟨0, LStore true 1 [v] .WCplain⟩, ⟨0, LLoad true 0 [0] [v]⟩, rfl, rfl, by omega, rfl, rfl,
      rfl, rfl, rfl, rfl, rfl⟩
  have hpub : pubW (candExec (ceRl true v)) (ev_at 1) (evTs (candExec (ceRl true v)) (ev_at 1)) :=
    ⟨⟨⟨0, LStore true 1 [v] .WCplain⟩, rfl, rfl⟩, ⟨1, rfl⟩, rfl⟩
  have := hrelax (ev_at 1) 2 ⟨0, LLoad true 0 [0] [v]⟩ 0 (ev_at 0)
    (evTs (candExec (ceRl true v)) (ev_at 1)) rfl (.inl hra) hpub hfr
  omega

/-- NON-VACUITY: the same trace WITHOUT the release annotation is
machine-reachable BY THE THEOREM OF §11, and it is not an SC candidate. -/
theorem ceRlStaleReachable (v : BitVec 8) :
    execWf (candExec (ceRl false v)) ∧ ¬ candLatest (ceRl false v) := by
  refine ⟨(promiseFreeCompleteClean _ (ceRlShape false v) (ceRlValues false v)
    (ceRlAxiomaticOk false v rfl)).1, ?_⟩
  intro hlat
  obtain ⟨_, hnw⟩ := hlat 2 ⟨0, LLoad true 0 [0] [v]⟩ 0 [0] [v] rfl rfl 0 0 rfl
  apply hnw
  exact ⟨1, by omega, by simp [cdLog, ceRl, ceRlTr, trMsgs, esMsg, lbWr], ⟨0, [v], some 1, .WCplain⟩,
    rfl, by simp [msgByte, accAddr]⟩

/-! # 13b. THE FORWARDED-READ WITNESS: the deleted premise's case, inhabited

Two steps, one byte, one agent: ts 1 — agent 0 stores byte 0; then agent 0
PLAIN-loads byte 0 and reads timestamp 1.  It fails the old `cand_pub_clean`
premise (`ceFwdNotPubClean`) and is machine-reachable by §11's theorem
(`ceFwdReachable`). -/

def ceFwdTr (v : BitVec 8) : List Estep :=
  [⟨0, LStore false 0 [v] .WCplain⟩,
   ⟨0, LLoad false 0 [1] [v]⟩]

def ceFwd (v : BitVec 8) : Cand := ⟨fun _ => some v, ceFwdTr v⟩

theorem ceFwdTrInv (v : BitVec 8) (k : Nat) (s : Estep) :
    (ceFwd v).cdTr[k]? = some s →
    (k = 0 ∧ s = ⟨0, LStore false 0 [v] .WCplain⟩) ∨ (k = 1 ∧ s = ⟨0, LLoad false 0 [1] [v]⟩) := by
  intro hs
  simp only [ceFwd, ceFwdTr] at hs
  match k, hs with
  | 0, hs => simp only [List.getElem?_cons_zero, Option.some.injEq] at hs; exact .inl ⟨rfl, hs.symm⟩
  | 1, hs =>
    simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hs
    exact .inr ⟨rfl, hs.symm⟩
  | k + 2, hs => simp at hs

theorem ceFwdShape (v : BitVec 8) : candShape (ceFwd v) := by
  intro k s hs
  rcases ceFwdTrInv v k s hs with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> simp

theorem ceFwdValues (v : BitVec 8) : candValues (ceFwd v) := by
  intro k s base ts vs hs hrd j t v' hj hv'
  rcases ceFwdTrInv v k s hs with ⟨_, rfl⟩ | ⟨rfl, rfl⟩
  · simp [lbRd] at hrd
  · simp only [lbRd, Option.some.injEq, Prod.mk.injEq] at hrd
    obtain ⟨rfl, rfl, rfl⟩ := hrd
    match j, hj, hv' with
    | 0, hj, hv' =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hj hv'
      subst hj hv'
      simp [cdLog, ceFwd, ceFwdTr, trMsgs, esMsg, lbWr, lbCls, logByte, msgByte, accAddr]
    | j + 1, hj, _ => simp at hj

theorem ceFwdTs0 (v : BitVec 8) : evTs (candExec (ceFwd v)) (ev_at 0) = 1 := by
  rw [candEvTs (ceFwd v) 0 (by simp [ceFwd, ceFwdTr])]; rfl

theorem ceFwdWr0 (v : BitVec 8) : wrB (candExec (ceFwd v)) 0 (ev_at 0) :=
  candWrB (ceFwd v) 0 ⟨0, LStore false 0 [v] .WCplain⟩ ⟨0, [v], some 0, .WCplain⟩ 0 rfl rfl
    (by simp [msgByte])

theorem ceFwdRd1 (v : BitVec 8) : readsAt (candExec (ceFwd v)) 1 0 1 v :=
  ⟨⟨0, LLoad false 0 [1] [v]⟩, 0, [1], [v], 0, rfl, rfl, rfl, rfl, by simp [accAddr]⟩

/-- Only the store (and the era-initial image) writes, only the load reads. -/
theorem ceFwdWrInv (v : BitVec 8) (a : Int) (e : Ev) :
    wrB (candExec (ceFwd v)) a e → e = ev_init ∨ (e = ev_at 0 ∧ a = 0) := by
  intro hw
  rcases candWrBInv (ceFwd v) a e hw with ⟨rfl, _⟩ | ⟨k, s, m, rfl, hs, hm, hb⟩
  · exact .inl rfl
  · rcases ceFwdTrInv v k s hs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · simp only [esWmsg, lbWr, lbCls, Option.some.injEq] at hm
      subst hm
      exact .inr ⟨rfl, WeakAxiomatic3.msgByteSingle v 0 (some 0) .WCplain a hb⟩
    · simp [esWmsg, lbWr] at hm

theorem ceFwdNotWr1 (v : BitVec 8) (a : Int) : ¬ wrB (candExec (ceFwd v)) a (ev_at 1) := by
  intro hw
  rcases ceFwdWrInv v a (ev_at 1) hw with habs | ⟨habs, _⟩ <;> simp at habs

theorem ceFwdRdInv (v : BitVec 8) (a : Int) (e : Ev) :
    rdB (candExec (ceFwd v)) a e → e = ev_at 1 ∧ a = 0 := by
  rintro ⟨k, t, v', rfl, s, base, ts, vs, j, hs, hrd, hj, hv, ha⟩
  rcases ceFwdTrInv v k s hs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · simp [lbRd] at hrd
  · simp only [lbRd, Option.some.injEq, Prod.mk.injEq] at hrd
    obtain ⟨rfl, rfl, rfl⟩ := hrd
    match j, hj with
    | 0, _ => exact ⟨rfl, by rw [ha]; simp [accAddr]⟩
    | j + 1, hj => simp at hj

theorem ceFwdNoRw (v : BitVec 8) (a : Int) (e : Ev) :
    wrB (candExec (ceFwd v)) a e → ¬ rdB (candExec (ceFwd v)) a e := by
  intro hw hr
  obtain ⟨rfl, _⟩ := ceFwdRdInv v a e hr
  exact ceFwdNotWr1 v a hw

/-- The one same-byte program-order pair is `ets`-flat. -/
theorem ceFwdPolocEts (v : BitVec 8) (a : Int) (e1 e2 : Ev) :
    poLocB (candExec (ceFwd v)) a e1 e2 → ets (candExec (ceFwd v)) a e1 ≤ ets (candExec (ceFwd v)) a e2 := by
  rintro ⟨⟨k1, k2, s1, s2, rfl, rfl, hlt, hs1, hs2, _⟩, hacc1, _⟩
  rcases ceFwdTrInv v k1 s1 hs1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    rcases ceFwdTrInv v k2 s2 hs2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · omega
  · have ha : a = 0 := by
      rcases hacc1 with hw | hr
      · rcases ceFwdWrInv v a _ hw with habs | ⟨_, ha⟩
        · cases habs
        · exact ha
      · have := (ceFwdRdInv v a _ hr).1; simp at this
    subst ha
    rw [etsWr _ 0 (ev_at 0) (ceFwdWr0 v), ceFwdTs0, etsRd _ 0 1 1 v (ceFwdNotWr1 v 0) (ceFwdRd1 v)]
    exact Nat.le_refl _
  · omega
  · omega

/-- No fence, no acquire, no release: the three ordering relations are empty. -/
theorem ceFwdNoOrd (v : BitVec 8) (e1 e2 : Ev) :
    ¬ ordPw (candExec (ceFwd v)) e1 e2 ∧ ¬ ordPr (candExec (ceFwd v)) e1 e2 ∧
    ¬ relOrd (candExec (ceFwd v)) e1 e2 := by
  have hnf : ∀ k1 k2 pr pw sr sw, ¬ fenceBetween (candExec (ceFwd v)) k1 k2 pr pw sr sw := by
    rintro k1 k2 pr pw sr sw ⟨kf, sf, _, _, _, _, _, hsf, _, _, _, hlf⟩
    rcases ceFwdTrInv v kf sf hsf with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> simp at hlf
  have hnaq : ∀ e e', ¬ acqPo (candExec (ceFwd v)) e e' := by
    rintro e e' ⟨k1, k2, s1, s2, rfl, rfl, _, hs1, _, _, _, haq⟩
    rcases ceFwdTrInv v k1 s1 hs1 with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> simp [lbAq] at haq
  have hnra : ∀ e e', ¬ relAcqPo (candExec (ceFwd v)) e e' := by
    rintro e e' ⟨k1, k2, s1, s2, rfl, rfl, _, hs1, _, _, _, hrl, _⟩
    rcases ceFwdTrInv v k1 s1 hs1 with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> simp [lbRl] at hrl
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨k1, k2, pr, sw, _, _, hfb⟩; exact hnf _ _ _ _ _ _ hfb
  · rintro (⟨k1, k2, pw, sw, _, _, hfb⟩ | hacq)
    · exact hnf _ _ _ _ _ _ hfb
    · exact hnaq _ _ hacq
  · rintro (h | ⟨em, h, _, _⟩)
    · exact hnra _ _ h
    · exact hnra _ _ h

theorem ceFwdAxOrd (v : BitVec 8) : axOrd (candExec (ceFwd v)) := by
  intro e1 k2 s2 a w t _ hcase _
  obtain ⟨hpw, hpr, _⟩ := ceFwdNoOrd v e1 (ev_at k2)
  rcases hcase with ⟨hord, _⟩ | ⟨hord, _⟩
  · exact absurd hord hpw
  · exact absurd hord hpr

theorem ceFwdAxRelOrd (v : BitVec 8) : axRelOrd (candExec (ceFwd v)) := by
  intro e1 k2 s2 a w t _ hro _ _
  exact absurd hro (ceFwdNoOrd v e1 (ev_at k2)).2.2

theorem ceFwdAxAtomicity (v : BitVec 8) : axAtomicity (candExec (ceFwd v)) := by
  intro kr a w0 w hW hrf0 _ _
  obtain ⟨_, k, t, v', hkeq, hr, _⟩ := hrf0
  have := (ceFwdRdInv v a (ev_at kr) ⟨k, t, v', hkeq, hr⟩).1
  injection this with this; subst this
  obtain ⟨s, hs, hisw⟩ := hW
  rcases ceFwdTrInv v 1 s hs with ⟨habs, _⟩ | ⟨_, rfl⟩
  · omega
  · simp [lbIsW] at hisw

/-- THE TWO HALVES.  The candidate fails the old premise ... -/
theorem ceFwdNotPubClean (v : BitVec 8) :
    ¬ (∀ k s a t v', (ceFwd v).cdTr[k]? = some s → readsAt (candExec (ceFwd v)) k a t v' →
        lbAq s.esLb = true ∨
        ∃ w, rfB (candExec (ceFwd v)) a w (ev_at k) ∧ extW (candExec (ceFwd v)) w s.esAg) := by
  intro hpc
  rcases hpc 1 ⟨0, LLoad false 0 [1] [v]⟩ 0 1 v rfl (ceFwdRd1 v) with habs | ⟨w, hrf, hext⟩
  · simp [lbAq] at habs
  -- the only write at timestamp 1 is agent 0's own store
  have hts : evTs (candExec (ceFwd v)) w = 1 := by
    have hrf' := hrf
    obtain ⟨_, k, t, v', hkeq, hr, hts⟩ := hrf'
    injection hkeq with hkeq; subst hkeq
    exact hts.trans (readsAtDet _ 1 0 t v' 1 v hr (ceFwdRd1 v)).1
  have hw : w = ev_at 0 :=
    candTsInj (ceFwd v) (0, w) (0, ev_at 0) hrf.1 (ceFwdWr0 v) (by simp only; rw [hts, ceFwdTs0])
  subst hw
  obtain ⟨s'', hs'', hne⟩ := hext
  rcases ceFwdTrInv v 0 s'' hs'' with ⟨_, rfl⟩ | ⟨habs, _⟩
  · exact hne rfl
  · omega

/-- ... and is machine-reachable all the same. -/
theorem ceFwdReachable (v : BitVec 8) :
    execWf (candExec (ceFwd v)) ∧ (candExec (ceFwd v)).exTr = (ceFwd v).cdTr := by
  obtain ⟨hwf, htr, _⟩ := promiseFreeCompleteLocal (ceFwd v) (ceFwdShape v) (ceFwdValues v)
    (candRfTotal _ (ceFwdValues v))
    (fun a e => cohRelAcycSimple (ceFwd v) a (ceFwdValues v) (ceFwdPolocEts v a) (ceFwdNoRw v a) e)
    (ceFwdAxOrd v) (ceFwdAxRelOrd v) (ceFwdAxAtomicity v)
  exact ⟨hwf, htr⟩

/-! # 14. THE NAMED TOP LEVEL: sRVWMO

sRVWMO is RVWMO with ONE ordering rule added — "po ∩ (M × W) ⊆ gmo", stores
are never early — and with its ppo fragment restricted to what the
promise-free machine enforces.  THE ppo RESIDUE TABLE (design doc "SETTLED
AXIOMATIZATION", 2026-08-19): sRVWMO's ppo = RVWMO rules 1–5, 7, 14.

    rule                             status here
    1–3  same-address pairs          IN   `poLocB` / `axCoherence`
    4    fence pred/succ             IN   `ordPw` / `ordPr` / `axOrd`
    5    acquire annotation on a     IN   `acqPo` (inside `ordPr`)
    7    RCsc pair (rl before aq)    IN   `relAcqPo` / `axRelOrd`
    14   b is a store (NEW)          IN   `ppoOp`'s first arm, in full
    6    release annotation on b     OMITTED: not enforced by the machine
    8, 10, 11, 13, 9 (store half)    REDUNDANT under 14
    9  (LOAD half)                   OMITTED BECAUSE OF D-8 (the xv6 loads carry
                                     `asrc = []`); IF D-8 IS EVER DROPPED, RULE 9's
                                     LOAD HALF COMES STRAIGHT BACK
    12   forwarding pipeline         OMITTED, and CONSUMED INSIDE THE THEOREM
                                     (`candReadSplit`)

Exclusive pairs stay FUSED in this presentation. -/

def srvwmoConsistent (c : Cand) : Prop := candShape c ∧ candValues c ∧ candAxiomaticOk c

/-- T1 FOR THIS FRAGMENT, IN FINAL FORM: an sRVWMO-consistent candidate is
realized by the promise-free machine, with the same trace and image. -/
theorem srvwmoRealizable (c : Cand) :
    srvwmoConsistent c →
    execWf (candExec c) ∧ (candExec c).exTr = c.cdTr ∧ exImg (candExec c) = c.cdImg := by
  rintro ⟨hsh, hval, hax⟩
  exact promiseFreeCompleteClean c hsh hval hax

/-! # 15. WHAT THIS SLICE DOES NOT DO (prose)

(1) THE PRE-D-7 FORWARD-BANK LEAK is argued and not machine-checked: the
seven-step witness (foreign write of byte 0; own write of byte 1; fence
`pw,sw`; own write of byte 2 banking `(3, 2)` pre-D-7; a FORWARDED load of byte
2; fence `pr,sr`; a load of byte 0 at timestamp 0) separated the two sides
BEFORE D-7 and is dead as of D-7 (the bank holds `(3, 0)`).  What IS
machine-checked is that the leak is gone (§13b).  (2) WHY NO PREMISE REMAINS:
the release/acquire leak is closed by strengthening the model (rule 7); the
forward-bank leak by weakening the machine (D-7), cashed in by §8.  (3) OWED
LIFTS: `maxcl` and the fold lemmas now live in `WeakMem`; §5's
`storeFoldVRel`, the primed fold lemmas, the bank facts and `fwdViewCases`
belong there too; §1–§3's candidate log calculus next to `candExec` in
`WeakAxiomatic2`. -/

end Weak
