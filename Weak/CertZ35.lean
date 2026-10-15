/-
Weak: **(γ) [OWN.100], increment 0 — the CROSS-SPIN shape is NOT realizable by the current realization
target** (`PROGRESS-W10N2p.md`).  Lean-only, no Rocq twin.

The machine every member must be a run of (the promise-free candidate model: each hart's steps in program
order, a store's message APPENDED at its step, an RMW reading the LATEST log bytes) cannot exhibit two
harts that each release one lock word and then fail an acquire on the other's: **`CertZ35.crossSpinNo`**.
RVWMO allows it (a plain release store and a later non-`rl` AMO to another address are unordered), so the
realization target must change (OWN.100, option γ); this file is the formal witness.

Spec: a theorem about the existing candidate model; nothing assumed.  Lean-only helpers `CertZ35.*`.
-/
import Weak.CertZ34

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open TsoShadow

/-- A step's message writes `b`. -/
def CertZ35.wrB (c : Cand) (b : Int) (j : Nat) : Prop :=
  ∃ s m, c.cdTr[j]? = some s ∧ esMsg s = [m] ∧ (msgByte m b).isSome

/-- An RMW step reading a NONZERO byte at `b`. -/
def CertZ35.rmwNz (c : Cand) (b : Int) (j : Nat) : Prop :=
  ∃ s aq rl base ts rvs wvs kc jj t v, c.cdTr[j]? = some s ∧
    s.esLb = .LRmw aq rl base ts rvs wvs kc ∧ ts[jj]? = some t ∧ rvs[jj]? = some v ∧
    accAddr base jj = b ∧ v ≠ 0#8

/-- A step whose message writes ZERO at `b`. -/
def CertZ35.wrZero (c : Cand) (b : Int) (j : Nat) : Prop :=
  ∃ s m, c.cdTr[j]? = some s ∧ esMsg s = [m] ∧ msgByte m b = some 0#8

theorem CertZ35.logAtPfx (c : Cand) (i f : Nat) (s : Estep) (m : Wmsg) :
    c.cdTr[i]? = some s → esMsg s = [m] → i < f →
    (cdLog c f)[(cdLog c i).length]? = some m := by
  intro hs hm hif
  obtain ⟨rest, hrest⟩ := cdLogSplit c (i + 1) f (by omega)
  rw [hrest, cdLogS c i s hs, hm, List.append_assoc, List.getElem?_append_right (Nat.le_refl _),
    Nat.sub_self]
  rfl

/-- **THE RMW CANNOT READ PAST A ZERO STORE**: if the only writes of `b` are at `a < r`, `r` and `f`,
`r` writes zero and the RMW at `f ≠ r` reads nonzero at `b`, then `f < r`. -/
theorem CertZ35.rmwBefore (c : Cand) (b : Int) (a r f : Nat) :
    srvwmoConsistent c → a < r → f ≠ r →
    (∀ j, CertZ35.wrB c b j → j = a ∨ j = r ∨ j = f) →
    CertZ35.wrZero c b r → CertZ35.rmwNz c b f → f < r := by
  intro hcons har hfr honly ⟨sr, mr, hsr, hmr, hzr⟩ ⟨s, aq, rl, base, ts, rvs, wvs, kc, jj, t, v, hs, hl,
    ht, hv, ha, hne⟩
  refine Nat.lt_of_not_le (fun hle => ?_)
  have hrf : r < f := by omega
  have hfl : f < c.cdTr.length := lookup_lt_Some hs
  -- the RMW's read: its value from the log before it, at the latest timestamp
  obtain ⟨hwf, htrE, -⟩ := srvwmoRealizable c hcons
  have hkE : (candExec c).exTr[f]? = some s := by rw [htrE]; exact hs
  have hW : lbIsW s.esLb = true := by rw [hl]; rfl
  have hrd : lbRd s.esLb = some (base, ts, rvs) := by rw [hl]; rfl
  have hstep := execStepAt (candExec c) f s hwf hkE
  have hlat0 := CertZ20.mstepRmwLatest _ _ _ _ base ts rvs hstep hW hrd jj t ht
  have hmI : (stt (candExec c) f).msImg = c.cdImg := candEimg c f (Nat.le_of_lt hfl)
  have hmL : (stt (candExec c) f).msLog = cdLog c f := candElog c f (Nat.le_of_lt hfl)
  rw [hmI, hmL] at hlat0
  have hval := hcons.2.1 f s base ts rvs hs hrd jj t v ht hv
  rw [ha] at hlat0 hval
  -- the zero store's message is in the log before the RMW
  have hatR := CertZ35.logAtPfx c r f sr mr hsr hmr hrf
  generalize hp : (cdLog c r).length = p at hatR
  have htp : p + 1 ≤ t := by
    refine Nat.le_of_not_lt (fun hlt => hlat0.2 ⟨p + 1, hlt, ?_, mr, ?_, by rw [hzr]; rfl⟩)
    · exact lookup_lt_Some hatR
    · simpa using hatR
  rcases Nat.lt_or_eq_of_le htp with hgt | heq
  · -- a later message writes `b`: it is a step strictly between `r` and `f`
    obtain ⟨i, rfl⟩ : ∃ i, t = i + 1 := ⟨t - 1, by omega⟩
    rw [logByteS] at hval
    cases hm : (cdLog c f)[i]? with
    | none => rw [hm] at hval; cases hval
    | some m =>
      rw [hm] at hval
      have hbv : msgByte m b = some v := by simpa using hval
      obtain ⟨j, sj, hjf, hsj, hlj, hemj⟩ := CertZ22.logIdx c f i m hm
      have hwb : CertZ35.wrB c b j := ⟨sj, m, hsj, hemj, by rw [hbv]; rfl⟩
      rcases honly j hwb with rfl | rfl | rfl
      · have h1 := CertZ22.logLenStep c j sj m hsj hemj
        have h2 := cdLogLenLe c (j + 1) r har
        omega
      · omega
      · omega
  · subst heq
    rw [logByteS, hatR] at hval
    have : msgByte mr b = some v := by simpa using hval
    rw [hzr, Option.some.injEq] at this
    exact hne this.symm

/-- **`CertZ35.crossSpinNo` — NO CANDIDATE REALIZES THE CROSS-SPIN**: hart-order positions
`a1 < r1 < f2` (hart 1: acquire, release of `b1`, failed RMW on `b2`) and `a2 < r2 < f1` (hart 2; the
release steps distinct from the RMWs), the
only writes of `b1` at `a1, r1, f1` and of `b2` at `a2, r2, f2`, the releases zero, the failed RMWs
reading nonzero — impossible. -/
theorem CertZ35.crossSpinNo (c : Cand) (b1 b2 : Int) (a1 r1 f1 a2 r2 f2 : Nat) :
    srvwmoConsistent c → a1 < r1 → r1 < f2 → a2 < r2 → r2 < f1 → f1 ≠ r1 → f2 ≠ r2 →
    (∀ j, CertZ35.wrB c b1 j → j = a1 ∨ j = r1 ∨ j = f1) →
    (∀ j, CertZ35.wrB c b2 j → j = a2 ∨ j = r2 ∨ j = f2) →
    CertZ35.wrZero c b1 r1 → CertZ35.wrZero c b2 r2 →
    CertZ35.rmwNz c b1 f1 → CertZ35.rmwNz c b2 f2 → False := by
  intro hcons h1 h2 h3 h4 hd1 hd2 hw1 hw2 hz1 hz2 hn1 hn2
  have hf1 := CertZ35.rmwBefore c b1 a1 r1 f1 hcons h1 hd1 hw1 hz1 hn1
  have hf2 := CertZ35.rmwBefore c b2 a2 r2 f2 hcons h3 hd2 hw2 hz2 hn2
  omega

end Weak
