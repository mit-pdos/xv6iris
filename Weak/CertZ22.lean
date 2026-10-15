/-
Weak: **W10-4 [OWN.94] (N2′), decision (i) — the RACE-FREE READS theorem, walk half (D2)**
(`PROGRESS-W10N2p.md`).  Lean-only, no Rocq twin.

At a walk state that has walked `L.take k` (the candidate's agents are `L`'s, each hart's trace labels
re-index `GF`'s row — the walk invariant `CertZ6.lockInv`/`CertZ8.prefInv`), the walk's log is the
messages of the walked writes in walk order, with `GF`'s write bytes (writes verbatim).  So the latest
byte of `a` in the walk's log is the `L`-last walked write of `a` (or the image) — by `CertZ21.drfRead`
exactly the value `GF`'s protected read returns:

  §1  the candidate log calculus: `CertZ22.logIdx` (a log message is a trace step's), `logAt`,
      `logLenStep`; the trace ↔ order ↔ `GF` correspondence `CertZ22.ceidTake`, `CertZ22.stepLbl`,
      `CertZ22.msgByteIff` (a walked step's message writes `GF`'s bytes);
  §2  **`CertZ22.byteAgree`** (one protected byte) and **`CertZ22.readAgreeDrf`** — at a protected plain
      load, `lrdVs St.cstC base n = vs`: the load arm of `CertZ11.readAgree` (and of `CertZ8.valPol`).

Spec: FAITHFUL (the premises are `CertZ21`'s DRF and order facts and the walk invariant).
-/
import Weak.CertZ21

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open TsoShadow

/-! # 1. The candidate log and the correspondence -/

theorem CertZ22.esMsgCases (s : Estep) : esMsg s = [] ∨ ∃ m, esMsg s = [m] := by
  unfold esMsg
  split
  · exact .inr ⟨_, rfl⟩
  · exact .inl rfl

/-- A message of the candidate's log is a trace step's. -/
theorem CertZ22.logIdx (c : Cand) : ∀ (k p : Nat) (m : Wmsg), (cdLog c k)[p]? = some m →
    ∃ j s, j < k ∧ c.cdTr[j]? = some s ∧ (cdLog c j).length = p ∧ esMsg s = [m] := by
  intro k
  induction k with
  | zero => intro p m h; simp [cdLog, trMsgs] at h
  | succ k ih =>
    intro p m h
    cases hk : c.cdTr[k]? with
    | none =>
      have hle : c.cdTr.length ≤ k := by
        refine Nat.le_of_not_lt (fun hlt => ?_)
        rw [List.getElem?_eq_getElem hlt] at hk
        cases hk
      have heq : cdLog c (k + 1) = cdLog c k := by
        unfold cdLog
        rw [List.take_of_length_le (by omega), List.take_of_length_le hle]
      rw [heq] at h
      obtain ⟨j, s, hj, hs, hl, hm⟩ := ih p m h
      exact ⟨j, s, by omega, hs, hl, hm⟩
    | some s =>
      rw [cdLogS c k s hk] at h
      by_cases hp : p < (cdLog c k).length
      · rw [List.getElem?_append_left hp] at h
        obtain ⟨j, s', hj, hs, hl, hm⟩ := ih p m h
        exact ⟨j, s', by omega, hs, hl, hm⟩
      · rw [List.getElem?_append_right (by omega)] at h
        rcases CertZ22.esMsgCases s with he | ⟨m', he⟩
        · rw [he] at h; simp at h
        · rw [he] at h
          have hp0 : p - (cdLog c k).length = 0 := by
            refine Nat.eq_zero_of_not_pos (fun hpos => ?_)
            rw [List.getElem?_eq_none (by simp; omega)] at h
            cases h
          rw [hp0] at h
          simp only [List.getElem?_cons_zero, Option.some.injEq] at h
          subst h
          exact ⟨k, s, by omega, hk, by omega, he⟩

theorem CertZ22.logAt (c : Cand) (i : Nat) (s : Estep) (m : Wmsg) :
    c.cdTr[i]? = some s → esMsg s = [m] →
    (cdLog c c.cdTr.length)[(cdLog c i).length]? = some m := by
  intro hs hm
  have hil := lookup_lt_Some hs
  obtain ⟨rest, hrest⟩ := cdLogSplit c (i + 1) c.cdTr.length (by omega)
  rw [hrest, cdLogS c i s hs, hm, List.append_assoc, List.getElem?_append_right (Nat.le_refl _),
    Nat.sub_self]
  rfl

theorem CertZ22.logLenStep (c : Cand) (i : Nat) (s : Estep) (m : Wmsg) :
    c.cdTr[i]? = some s → esMsg s = [m] → (cdLog c (i + 1)).length = (cdLog c i).length + 1 := by
  intro hs hm
  rw [cdLogS c i s hs, hm, List.length_append]
  rfl

/-- The trace's `i`-th step is the order's `i`-th event, along a walked prefix. -/
theorem CertZ22.ceidTake (rows : List (List Lbl)) (dev L : List Geid) (c : Cand) (k i : Nat)
    (e : Geid) :
    CertZ8.walkOrd rows dev L → c.cdTr.map Estep.esAg = (L.take k).map Prod.fst → i < k →
    L[i]? = some e → ∃ s, c.cdTr[i]? = some s ∧ ceid (candExec c) i = e := by
  intro hord hags hik hi
  have hi' : (L.take k)[i]? = some e := by rw [lookup_take hik]; exact hi
  have hlen : c.cdTr.length = (L.take k).length := by
    have := congrArg List.length hags; simpa using this
  have hil : i < c.cdTr.length := by rw [hlen]; exact lookup_lt_Some hi'
  obtain ⟨s, hs⟩ : ∃ s, c.cdTr[i]? = some s := ⟨_, List.getElem?_eq_getElem hil⟩
  have hag : s.esAg = e.1 := by
    have h1 : (c.cdTr.map Estep.esAg)[i]? = some s.esAg := by rw [List.getElem?_map, hs]; rfl
    rw [hags, List.getElem?_map, hi'] at h1
    simp only [Option.map_some, Option.some.injEq] at h1
    exact h1.symm
  refine ⟨s, hs, ?_⟩
  rw [ceidCf (candExec c) i s hs]
  obtain ⟨x, a⟩ := e
  show (s.esAg, ((c.cdTr.take i).filter (fun s' => decide (s'.esAg = s.esAg))).length) = (x, a)
  rw [hag, CertZ8.countMapAg, List.map_take, hags, ← List.map_take, ← CertZ8.countMapFst,
    List.take_take, Nat.min_eq_left (Nat.le_of_lt hik), CertZ8.ordCount rows dev L i x a hord hi]

/-- A walked step's label re-indexes `GF`'s label of its event. -/
theorem CertZ22.stepLbl (G : Gexec) (dev L : List Geid) (c : Cand) (cnt : Nat → Nat) (i : Nat)
    (s : Estep) (e : Geid) :
    CertZ8.walkOrd G.gxProg dev L →
    (∀ x, x < G.gxProg.length →
      List.Forall₂ lblReidxW ((G.gxProg.getD x []).take (cnt x)) (CertZ2.hartTr c.cdTr x)) →
    L[i]? = some e → c.cdTr[i]? = some s → ceid (candExec c) i = e →
    ∃ l0, gxLbl G e = some l0 ∧ lblReidxW l0 s.esLb := by
  intro hord hper hi hs hce
  have hev := (hord.2.1 e).1 (List.mem_of_getElem? hi)
  have hh : (CertZ2.hartTr c.cdTr e.1)[e.2]? = some s.esLb := by
    have h1 := (cgLbl (candExec c) i s hs).1
    rw [hce, CertZ3.cgLblHart] at h1
    exact h1
  have hx : e.1 < G.gxProg.length := hev.1
  rcases GraphFetchN2.forall₂Get _ _ _ (hper e.1 hx) e.2 with ⟨-, h2⟩ | ⟨l0, l1, h1, h2, h12⟩
  · rw [hh] at h2; cases h2
  · rw [hh, Option.some.injEq] at h2
    subst h2
    refine ⟨l0, ?_, h12⟩
    unfold gxLbl
    rw [CertZ7.getDSome _ e.1 hx]
    exact (lookup_take_Some.1 h1).1

theorem CertZ22.wrNone (l : Lbl) : lbIsW l = false → lbWr l = none := by
  cases l <;> simp_all [lbIsW, lbWr]

theorem CertZ22.wrEq (l0 l1 : Lbl) : lblReidxW l0 l1 → lbWr l1 = lbWr l0 := by
  intro h
  cases hW : lbIsW l0 with
  | true => exact (GraphFetchWalkZ.lblReidxWWr l0 l1 h hW).1
  | false =>
    rw [CertZ22.wrNone l0 hW, CertZ22.wrNone l1 (by rw [lblReidxWIsw _ _ h, hW])]

/-- A walked step's message writes exactly `GF`'s bytes of its event. -/
theorem CertZ22.msgByteIff (G : Gexec) (e : Geid) (l0 : Lbl) (s : Estep) (a : Int) (v : BitVec 8) :
    gxLbl G e = some l0 → lblReidxW l0 s.esLb →
    (gwritesByte G e a v ↔ ∃ m, esMsg s = [m] ∧ msgByte m a = some v) := by
  intro hl hre
  have hwr := CertZ22.wrEq l0 s.esLb hre
  unfold esMsg
  rw [hwr]
  cases h0 : lbWr l0 with
  | none =>
    constructor
    · rintro ⟨l, base, vs, j, hl', hw, -⟩
      rw [hl, Option.some.injEq] at hl'
      subst hl'
      rw [h0] at hw
      cases hw
    · rintro ⟨m, hm, -⟩
      cases hm
  | some p =>
    obtain ⟨base, vs⟩ := p
    have hg : WeakRvwmoKillArms.gmsg G e = some ⟨base, vs, some e.1, lbCls l0⟩ := by
      unfold WeakRvwmoKillArms.gmsg
      simp only [hl, h0]
    have key := WeakRvwmoKillArms.gmsgByte G e _ a v hg
    constructor
    · intro hw
      exact ⟨_, rfl, key.2 hw⟩
    · rintro ⟨m, hm, hb⟩
      simp only [List.cons.injEq, and_true] at hm
      subst hm
      exact key.1 hb

/-! # 2. The theorem -/

/-- **ONE PROTECTED BYTE**: the walk's latest byte of `a` is the value `GF`'s protected read returns. -/
theorem CertZ22.byteAgree (G : Gexec) (dev L : List Geid) (c : Cand) (cnt : Nat → Nat) (k : Nat)
    (r A : Geid) (oR : Option Geid) (b a : Int) (t : Nat) (v : BitVec 8) :
    gwf G → gppoCat6Gmo G → gloadValue G → CertZ8.walkOrd G.gxProg dev L →
    c.cdImg = G.gxImg →
    c.cdTr.map Estep.esAg = (L.take k).map Prod.fst →
    (∀ x, x < G.gxProg.length →
      List.Forall₂ lblReidxW ((G.gxProg.getD x []).take (cnt x)) (CertZ2.hartTr c.cdTr x)) →
    L[k]? = some r → greadsByte G r a t v → ¬ glblIs G r lbIsW →
    CertZ21.drfFacts G b a → CertZ21.ordFacts G b L → CertZ21.secOf G b r A oR →
    logByte c.cdImg (cdLogEnd c) (latestTs (cdLogEnd c) a) a = some v := by
  intro hwf h6 hlv hord hci hags hper hk hrd hnW hd ho hsr
  have hkL : k < L.length := lookup_lt_Some hk
  have hlen : c.cdTr.length = k := by
    have := congrArg List.length hags
    simp only [List.length_map, List.length_take] at this
    omega
  have hend : cdLogEnd c = cdLog c c.cdTr.length := by rw [cdLogEndFull, cdLogFull]
  obtain ⟨h0, hpos⟩ := CertZ21.drfRead G b a L k r A oR t v hwf h6 hlv hd ho hk hrd hnW hsr
  -- a trace step's message writing `a` is a walked `GF` write of `a`
  have hstepW : ∀ jj s m v', c.cdTr[jj]? = some s → esMsg s = [m] → msgByte m a = some v' →
      ∃ e, L[jj]? = some e ∧ jj < k ∧ gwritesByte G e a v' := by
    intro jj s m v' hs hm hb
    have hjj : jj < k := by rw [← hlen]; exact lookup_lt_Some hs
    obtain ⟨e, he⟩ : ∃ e, L[jj]? = some e := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    obtain ⟨s', hs', hce⟩ := CertZ22.ceidTake G.gxProg dev L c k jj e hord hags hjj he
    rw [hs, Option.some.injEq] at hs'
    subst hs'
    obtain ⟨l0, hl0, hre⟩ := CertZ22.stepLbl G dev L c cnt jj s e hord hper he hs hce
    exact ⟨e, he, hjj, (CertZ22.msgByteIff G e l0 s a v' hl0 hre).2 ⟨m, hm, hb⟩⟩
  by_cases ht : t = 0
  · obtain ⟨himg, hnone⟩ := h0 ht
    have hz : latestTs (cdLogEnd c) a = 0 := by
      rcases latestTsWrites (cdLogEnd c) a with hz | ⟨p, m, -, hm, hs⟩
      · exact hz
      · exfalso
        rw [hend] at hm
        obtain ⟨jj, s, -, hs', -, hem⟩ := CertZ22.logIdx c _ p m hm
        obtain ⟨v', hv'⟩ := Option.isSome_iff_exists.1 hs
        obtain ⟨e, he, hjj, hw⟩ := hstepW jj s m v' hs' hem hv'
        have := hnone e v' jj hw he
        omega
    rw [hz, logByte0, hci]
    exact himg
  · have htpos : 0 < t := Nat.pos_of_ne_zero ht
    obtain ⟨w0, hw0⟩ : ∃ w0, gwriteAt G t = some w0 := by
      obtain ⟨hsrc, -⟩ := hlv r a t v hrd
      obtain ⟨n, rfl⟩ : ∃ n, t = n + 1 := ⟨t - 1, by omega⟩
      obtain ⟨w, hw, -⟩ := hsrc
      exact ⟨w, hw⟩
    obtain ⟨hwv, ⟨i0, hi0k, hi0⟩, hlast⟩ := hpos w0 hw0 htpos
    obtain ⟨s0, hs0, hce0⟩ := CertZ22.ceidTake G.gxProg dev L c k i0 w0 hord hags hi0k hi0
    obtain ⟨l0, hl0, hre0⟩ := CertZ22.stepLbl G dev L c cnt i0 s0 w0 hord hper hi0 hs0 hce0
    obtain ⟨m0, hm0, hb0⟩ := (CertZ22.msgByteIff G w0 l0 s0 a v hl0 hre0).1 hwv
    have hat0 := CertZ22.logAt c i0 s0 m0 hs0 hm0
    have hlat : latest c.cdImg (cdLogEnd c) a ((cdLog c i0).length + 1) := by
      rw [hend]
      refine ⟨by rw [logByteS, hat0]; simp [hb0], ?_⟩
      rintro ⟨q, hq1, hq2, m, hm, hs⟩
      obtain ⟨jj, s, -, hs', hlenj, hem⟩ := CertZ22.logIdx c _ (q - 1) m hm
      obtain ⟨v', hv'⟩ := Option.isSome_iff_exists.1 hs
      obtain ⟨e, he, hjj, hw⟩ := hstepW jj s m v' hs' hem hv'
      have hgt : i0 < jj := by
        refine Nat.lt_of_not_le (fun hle => ?_)
        rcases Nat.eq_or_lt_of_le hle with heq | hlt
        · subst heq
          omega
        · have h1 := CertZ22.logLenStep c jj s m hs' hem
          have h2 := cdLogLenLe c (jj + 1) i0 hlt
          omega
      have hne : e ≠ w0 := by
        intro hew
        subst hew
        have := NoDup_lookup hord.1 he hi0
        omega
      have := hlast e v' jj i0 hw he hjj hi0 hne
      omega
    rw [latestTsEq _ _ _ _ hlat, hend, logByteS, hat0]
    simpa using hb0

/-- **`CertZ22.readAgreeDrf` — RACE-FREE READS AT THE WALK**: at a walk state that has walked
`L.take k`, the next event a plain load of `GF` all of whose bytes are protected (each by a lock byte
whose DRF and order facts hold, the load inside a section of it) gets the walk's latest bytes as its
`GF` values — the load arm of `CertZ11.readAgree`. -/
theorem CertZ22.readAgreeDrf (G : Gexec) (dev L : List Geid) (c : Cand) (cnt : Nat → Nat)
    (k : Nat) (r : Geid) (aq : Bool) (base : Int) (ts : List Nat) (vs : List (BitVec 8)) :
    gwf G → gppoCat6Gmo G → gloadValue G → CertZ8.walkOrd G.gxProg dev L →
    c.cdImg = G.gxImg →
    c.cdTr.map Estep.esAg = (L.take k).map Prod.fst →
    (∀ x, x < G.gxProg.length →
      List.Forall₂ lblReidxW ((G.gxProg.getD x []).take (cnt x)) (CertZ2.hartTr c.cdTr x)) →
    L[k]? = some r → gxLbl G r = some (.LLoad aq base ts vs) → vs.length = ts.length →
    (∀ j, j < ts.length → ∃ (b : Int) (A : Geid) (oR : Option Geid),
      CertZ21.drfFacts G b (accAddr base j) ∧ CertZ21.ordFacts G b L ∧ CertZ21.secOf G b r A oR) →
    lrdVs c base ts.length = vs := by
  intro hwf h6 hlv hord hci hags hper hk hl hvl hprot
  have hnW : ¬ glblIs G r lbIsW := by
    rintro ⟨l, hl', hw⟩
    rw [hl, Option.some.injEq] at hl'
    subst hl'
    simp [lbIsW] at hw
  apply List.ext_getElem?
  intro j
  unfold lrdVs
  by_cases hj : j < ts.length
  · rw [List.getElem?_map, lookup_seq_lt hj, Nat.zero_add]
    obtain ⟨tj, htj⟩ : ∃ tj, ts[j]? = some tj := ⟨_, List.getElem?_eq_getElem hj⟩
    obtain ⟨vj, hvj⟩ : ∃ vj, vs[j]? = some vj := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    rw [hvj]
    obtain ⟨b, A, oR, hd, ho, hs⟩ := hprot j hj
    have hrd : greadsByte G r (accAddr base j) tj vj :=
      ⟨_, base, ts, vs, j, hl, rfl, htj, hvj, rfl⟩
    show some ((logByte c.cdImg (cdLogEnd c) (latestTs (cdLogEnd c) (accAddr base j))
      (accAddr base j)).getD 0#8) = some vj
    rw [CertZ22.byteAgree G dev L c cnt k r A oR b (accAddr base j) tj vj hwf h6 hlv hord hci hags
      hper hk hrd hnW hd ho hs]
    rfl
  · rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by omega)]

end Weak
