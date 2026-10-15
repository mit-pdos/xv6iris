/-
Weak: **W10-4 [OWN.94] (N2′), decision (A), step 4d — RACE-FREE READS at the walk WITH SKIPS**
(`PROGRESS-W10N2p.md`).  Lean-only, no Rocq twin.

`CertZ22.readAgreeDrf` restated at the walk-invariant states of the walk with skips
(`CertZ29.hartStepRI4`'s hypotheses: the trace is the KEPT prefix of `L`, each hart's trace re-indexes its
filtered row prefix): **`CertZ32.readAgreeDrf4`** — a protected plain load `L[k]` gets the walk's latest
bytes as its `GF` values, provided no failed acquire writes the protected bytes (lock words and protected
data are disjoint).  This discharges the read part of `CatLin.stepSupplyCZ4` at protected loads.

  §1  `CertZ32.ceidKeepK` (a kept event of `L.take k` is its trace step), `idxUniq`, `stepLbl4`;
  §2  **`CertZ32.byteAgree4`**, **`CertZ32.readAgreeDrf4`**.

Spec: FAITHFUL (proof organisation).
-/
import Weak.CertZ31

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open TsoShadow

/-! # 1. The kept prefix and the trace -/

theorem CertZ32.ceidKeepK (rows : List (List Lbl)) (Lb : Int → Prop) (dev L : List Geid) (c : Cand)
    (k i0 : Nat) (e : Geid) :
    CertZ8.walkOrd rows dev L →
    c.cdTr.map Estep.esAg = ((L.take k).filter (CertZ29.keepEv rows Lb)).map Prod.fst →
    i0 < k → L[i0]? = some e → CertZ29.keepEv rows Lb e = true →
    ∃ s, c.cdTr[((L.take i0).filter (CertZ29.keepEv rows Lb)).length]? = some s ∧
      s.esAg = e.1 ∧
      ceid (candExec c) ((L.take i0).filter (CertZ29.keepEv rows Lb)).length =
        (e.1, (((rows.getD e.1 []).take e.2).filter (CertZ26.keepB Lb)).length) := by
  intro hord hags hik hi hk
  have htk : (L.take k).take i0 = L.take i0 := by rw [List.take_take, Nat.min_eq_left (by omega)]
  generalize hidx : ((L.take i0).filter (CertZ29.keepEv rows Lb)).length = i
  have hfe := CertZ30.filterAt _ (L.take k) i0 e (by rw [lookup_take hik]; exact hi) hk
  rw [htk, hidx] at hfe
  have hag1 : (c.cdTr.map Estep.esAg)[i]? = some e.1 := by
    rw [hags, List.getElem?_map, hfe]; rfl
  rw [List.getElem?_map] at hag1
  cases hs : c.cdTr[i]? with
  | none => rw [hs] at hag1; cases hag1
  | some s =>
    rw [hs] at hag1
    simp only [Option.map_some, Option.some.injEq] at hag1
    refine ⟨s, rfl, hag1, ?_⟩
    rw [ceidCf (candExec c) i s hs]
    obtain ⟨x, a⟩ := e
    show (s.esAg, ((c.cdTr.take i).filter (fun s' => decide (s'.esAg = s.esAg))).length) = _
    have hpre := CertZ30.filterTakeLeft (CertZ29.keepEv rows Lb) (L.take k) i0
    rw [htk] at hpre
    rw [hag1, CertZ8.countMapAg, List.map_take, hags, ← List.map_take, ← CertZ8.countMapFst, ← hidx,
      hpre, CertZ30.keptCount rows Lb dev L i0 x a hord hi]

theorem CertZ32.idxUniq (p : Geid → Bool) (L : List Geid) (k jj i1 : Nat) (e : Geid) :
    L.Nodup → ((L.take k).filter p)[jj]? = some e → L[i1]? = some e → i1 < k →
    jj = ((L.take i1).filter p).length := by
  intro hnd hj hi hik
  have hpe : p e = true := (List.mem_filter.1 (List.mem_of_getElem? hj)).2
  have hfe := CertZ30.filterAt p (L.take k) i1 e (by rw [lookup_take hik]; exact hi) hpe
  rw [List.take_take, Nat.min_eq_left (by omega)] at hfe
  exact NoDup_lookup ((hnd.sublist (List.take_sublist _ _)).filter _) hj hfe

/-- A kept event of the walked prefix: its trace step re-indexes its `GF` label. -/
theorem CertZ32.stepLbl4 (G : Gexec) (dev L : List Geid) (c : Cand) (Lb : Int → Prop) (k i0 : Nat)
    (e : Geid) :
    CertZ8.walkOrd G.gxProg dev L →
    c.cdTr.map Estep.esAg = ((L.take k).filter (CertZ29.keepEv G.gxProg Lb)).map Prod.fst →
    (∀ y, y < G.gxProg.length →
      List.Forall₂ lblReidxW
        (((G.gxProg.getD y []).take (((L.take k).filter (fun e => decide (e.1 = y))).length)).filter
          (CertZ26.keepB Lb))
        (CertZ2.hartTr c.cdTr y)) →
    i0 < k → L[i0]? = some e → CertZ29.keepEv G.gxProg Lb e = true →
    ∃ s l0, c.cdTr[((L.take i0).filter (CertZ29.keepEv G.gxProg Lb)).length]? = some s ∧
      gxLbl G e = some l0 ∧ lblReidxW l0 s.esLb := by
  intro hord hags hper hik hi hk
  obtain ⟨s, hs, -, hce⟩ := CertZ32.ceidKeepK _ Lb dev L c k i0 e hord hags hik hi hk
  have hev := (hord.2.1 e).1 (List.mem_of_getElem? hi)
  obtain ⟨l0, hl0⟩ : ∃ l0, (G.gxProg.getD e.1 [])[e.2]? = some l0 :=
    ⟨_, List.getElem?_eq_getElem hev.2⟩
  have hk0 : CertZ26.keepB Lb l0 = true := by
    rw [← CertZ29.keepEvAt _ Lb e.1 e.2 l0 hl0]; exact hk
  have hh : (CertZ2.hartTr c.cdTr e.1)[
      (((G.gxProg.getD e.1 []).take e.2).filter (CertZ26.keepB Lb)).length]? = some s.esLb := by
    have h1 := (cgLbl (candExec c) _ s hs).1
    rw [hce, CertZ3.cgLblHart] at h1
    exact h1
  -- the hart's count in the walked prefix passes `e.2`
  have hpe1 := hper e.1 hev.1
  have hcx : e.2 < ((L.take k).filter (fun e' => decide (e'.1 = e.1))).length := by
    obtain ⟨x, a⟩ := e
    have h1 := CertZ8.ordCount _ _ L i0 x a hord hi
    have h2 := CertZ30.filterTakeLt (fun e' => decide (e'.1 = x)) L i0 k (x, a) hik hi (by simp)
    dsimp only at h1 ⊢
    omega
  generalize hcnt : ((L.take k).filter (fun e' => decide (e'.1 = e.1))).length = cx at hpe1 hcx
  have hfe := CertZ30.filterAt (CertZ26.keepB Lb) ((G.gxProg.getD e.1 []).take cx) e.2 l0
    (by rw [lookup_take hcx]; exact hl0) hk0
  rw [List.take_take, Nat.min_eq_left (Nat.le_of_lt hcx)] at hfe
  rcases GraphFetchN2.forall₂Get _ _ _ hpe1
      (((G.gxProg.getD e.1 []).take e.2).filter (CertZ26.keepB Lb)).length with
    ⟨h1, -⟩ | ⟨l1, l2, h1, h2, h12⟩
  · rw [hfe] at h1; cases h1
  · rw [hfe, Option.some.injEq] at h1
    subst h1
    rw [hh, Option.some.injEq] at h2
    subst h2
    refine ⟨s, l0, hs, ?_, h12⟩
    unfold gxLbl; rw [CertZ7.getDSome _ e.1 hev.1]; exact hl0

/-! # 2. The theorem -/

/-- **ONE PROTECTED BYTE, WALK WITH SKIPS.** -/
theorem CertZ32.byteAgree4 (G : Gexec) (dev L : List Geid) (c : Cand) (Lb : Int → Prop) (k : Nat)
    (r A : Geid) (oR : Option Geid) (b a : Int) (t : Nat) (v : BitVec 8) :
    gwf G → gppoCat6Gmo G → gloadValue G → CertZ8.walkOrd G.gxProg dev L →
    c.cdImg = G.gxImg →
    c.cdTr.map Estep.esAg = ((L.take k).filter (CertZ29.keepEv G.gxProg Lb)).map Prod.fst →
    (∀ y, y < G.gxProg.length →
      List.Forall₂ lblReidxW
        (((G.gxProg.getD y []).take (((L.take k).filter (fun e => decide (e.1 = y))).length)).filter
          (CertZ26.keepB Lb))
        (CertZ2.hartTr c.cdTr y)) →
    L[k]? = some r → greadsByte G r a t v → ¬ glblIs G r lbIsW →
    CertZ21.drfFacts G b a → CertZ21.ordFacts G b L → CertZ21.secOf G b r A oR →
    (∀ e v', gwritesByte G e a v' → CertZ29.keepEv G.gxProg Lb e = true) →
    logByte c.cdImg (cdLogEnd c) (latestTs (cdLogEnd c) a) a = some v := by
  intro hwf h6 hlv hord hci hags hper hk hrd hnW hd ho hsr hkeepA
  have hkL : k < L.length := lookup_lt_Some hk
  have hlen : c.cdTr.length = ((L.take k).filter (CertZ29.keepEv G.gxProg Lb)).length := by
    have := congrArg List.length hags
    simpa using this
  have hend : cdLogEnd c = cdLog c c.cdTr.length := by rw [cdLogEndFull, cdLogFull]
  obtain ⟨h0, hpos⟩ := CertZ21.drfRead G b a L k r A oR t v hwf h6 hlv hd ho hk hrd hnW hsr
  have hstepW : ∀ jj s m v', c.cdTr[jj]? = some s → esMsg s = [m] → msgByte m a = some v' →
      ∃ e i1, L[i1]? = some e ∧ i1 < k ∧
        jj = ((L.take i1).filter (CertZ29.keepEv G.gxProg Lb)).length ∧ gwritesByte G e a v' := by
    intro jj s m v' hs hm hb
    have hjj : jj < ((L.take k).filter (CertZ29.keepEv G.gxProg Lb)).length := by
      rw [← hlen]; exact lookup_lt_Some hs
    obtain ⟨e, he⟩ : ∃ e, ((L.take k).filter (CertZ29.keepEv G.gxProg Lb))[jj]? = some e :=
      ⟨_, List.getElem?_eq_getElem hjj⟩
    obtain ⟨hmk, hpe⟩ := List.mem_filter.1 (List.mem_of_getElem? he)
    obtain ⟨i1, hi1k, hi1⟩ := (CertZ8.memTakeIff L k e).1 hmk
    have hjeq := CertZ32.idxUniq _ L k jj i1 e hord.1 he hi1 hi1k
    obtain ⟨s', l0, hs', hl0, hre⟩ := CertZ32.stepLbl4 G dev L c Lb k i1 e hord hags hper hi1k hi1 hpe
    rw [← hjeq, hs, Option.some.injEq] at hs'
    subst hs'
    exact ⟨e, i1, hi1, hi1k, hjeq, (CertZ22.msgByteIff G e l0 s a v' hl0 hre).2 ⟨m, hm, hb⟩⟩
  by_cases ht : t = 0
  · obtain ⟨himg, hnone⟩ := h0 ht
    have hz : latestTs (cdLogEnd c) a = 0 := by
      rcases latestTsWrites (cdLogEnd c) a with hz | ⟨p, m, -, hm, hs⟩
      · exact hz
      · exfalso
        rw [hend] at hm
        obtain ⟨jj, s, -, hs', -, hem⟩ := CertZ22.logIdx c _ p m hm
        obtain ⟨v', hv'⟩ := Option.isSome_iff_exists.1 hs
        obtain ⟨e, i1, he, hi1k, -, hw⟩ := hstepW jj s m v' hs' hem hv'
        have := hnone e v' i1 hw he
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
    have hk0 := hkeepA w0 v hwv
    obtain ⟨s0, l0, hs0, hl0, hre0⟩ := CertZ32.stepLbl4 G dev L c Lb k i0 w0 hord hags hper hi0k hi0 hk0
    generalize hp0 : ((L.take i0).filter (CertZ29.keepEv G.gxProg Lb)).length = p0 at hs0
    obtain ⟨m0, hm0, hb0⟩ := (CertZ22.msgByteIff G w0 l0 s0 a v hl0 hre0).1 hwv
    have hat0 := CertZ22.logAt c p0 s0 m0 hs0 hm0
    have hlat : latest c.cdImg (cdLogEnd c) a ((cdLog c p0).length + 1) := by
      rw [hend]
      refine ⟨by rw [logByteS, hat0]; simp [hb0], ?_⟩
      rintro ⟨q, hq1, hq2, m, hm, hs⟩
      obtain ⟨jj, s, -, hs', hlenj, hem⟩ := CertZ22.logIdx c _ (q - 1) m hm
      obtain ⟨v', hv'⟩ := Option.isSome_iff_exists.1 hs
      obtain ⟨e, i1, he, hi1k, hjeq, hw⟩ := hstepW jj s m v' hs' hem hv'
      have hgt : p0 < jj := by
        refine Nat.lt_of_not_le (fun hle => ?_)
        rcases Nat.eq_or_lt_of_le hle with heq | hlt
        · subst heq
          omega
        · have h1 := CertZ22.logLenStep c jj s m hs' hem
          have h2 := cdLogLenLe c (jj + 1) p0 hlt
          omega
      have hne : e ≠ w0 := by
        intro hew
        subst hew
        have := NoDup_lookup hord.1 he hi0
        subst this
        omega
      have hlt := hlast e v' i1 i0 hw he hi1k hi0 hne
      have := CertZ30.filterTakeLt _ L i1 i0 e hlt he (hkeepA e v' hw)
      omega
    rw [latestTsEq _ _ _ _ hlat, hend, logByteS, hat0]
    simpa using hb0

/-- **`CertZ32.readAgreeDrf4` — RACE-FREE READS AT THE WALK WITH SKIPS** (the load arm of
`CertZ11.readAgree` at walk-invariant states). -/
theorem CertZ32.readAgreeDrf4 (G : Gexec) (dev L : List Geid) (c : Cand) (Lb : Int → Prop)
    (k : Nat) (r : Geid) (aq : Bool) (base : Int) (ts : List Nat) (vs : List (BitVec 8)) :
    gwf G → gppoCat6Gmo G → gloadValue G → CertZ8.walkOrd G.gxProg dev L →
    c.cdImg = G.gxImg →
    c.cdTr.map Estep.esAg = ((L.take k).filter (CertZ29.keepEv G.gxProg Lb)).map Prod.fst →
    (∀ y, y < G.gxProg.length →
      List.Forall₂ lblReidxW
        (((G.gxProg.getD y []).take (((L.take k).filter (fun e => decide (e.1 = y))).length)).filter
          (CertZ26.keepB Lb))
        (CertZ2.hartTr c.cdTr y)) →
    L[k]? = some r → gxLbl G r = some (.LLoad aq base ts vs) → vs.length = ts.length →
    (∀ j, j < ts.length → ∃ (b : Int) (A : Geid) (oR : Option Geid),
      CertZ21.drfFacts G b (accAddr base j) ∧ CertZ21.ordFacts G b L ∧ CertZ21.secOf G b r A oR ∧
      ∀ e v', gwritesByte G e (accAddr base j) v' → CertZ29.keepEv G.gxProg Lb e = true) →
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
    obtain ⟨b, A, oR, hd, ho, hs, hkw⟩ := hprot j hj
    have hrd : greadsByte G r (accAddr base j) tj vj :=
      ⟨_, base, ts, vs, j, hl, rfl, htj, hvj, rfl⟩
    show some ((logByte c.cdImg (cdLogEnd c) (latestTs (cdLogEnd c) (accAddr base j))
      (accAddr base j)).getD 0#8) = some vj
    rw [CertZ32.byteAgree4 G dev L c Lb k r A oR b (accAddr base j) tj vj hwf h6 hlv hord hci hags
      hper hk hrd hnW hd ho hs hkw]
    rfl
  · rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by omega)]

end Weak
