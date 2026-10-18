/-
Weak: **(c) [OWN.100], increment 4c-ii — the silent pair simulation** (`PROGRESS-W10N2p.md`).
Lean-only, no Rocq twin.

**`SilPair.pairSimS`**: the twin of `mstepWpPfStepPairS` for a SILENT AMO.  A candidate silent step
(`SilCand.silentOk` at `σ`) realized by the program pair (`lblRealizesPair`: `LExLoad`, the administrative
star, `LExStore false`) is replayed by a twin pf run — `PFExLoad`, the star, then `exStoreSilent` at `q`
over the reservation the load made — ending `cfgMatchd`-matched to `SilCand.silentNext σ …`.

`SilPair.admRunRtc`: the administrative star, unpinned (fetches at their view-0 check, as M2's
`PfRunUnpinned.admStepPfF`), as a registered pf run.

Spec: FAITHFUL (the same pair the registered rmw replay uses; the write half is the silent one; no pin).
-/
import Weak.SilDep

namespace Weak

open MachCSL MachCSL.Stdpp

/-- The silent raise is a `wsEqr` congruence. -/
theorem SilPair.wsEqrAqRaise (w1 w2 : Wstate) (q : Nat) :
    wsEqr w1 w2 → wsEqr (SilCand.aqRaise w1 q) (SilCand.aqRaise w2 q) := by
  rintro ⟨hc, h1, h2, h3, h4, h5, h6, h7, h8⟩
  refine ⟨fun a => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [SilCand.aqRaise, coh] at * <;> simp_all

section twin

variable {P D : Type}
variable (pstep : P → D → Wlabel → P → D → Prop)
variable (pcls : P → Wlabel → Wstate → WmClass)

/-- The administrative star, UNPINNED, as a pf run: a fetch is admissible at its view-0 check. -/
theorem SilPair.admRunRtc (instr : Bool) (p : P) (d : D) (ls : List Wlabel) (p' : P) (d' : D) :
    admRunG pstep instr p d ls p' d' →
    ∀ (c : Wpcfg P D) (i : Nat) (ag : Wpagent P),
      c.pcAgs[i]? = some ag → ag.paSt = p → c.pcDev = d →
      (∀ (base : Int) (tvs : List (Nat × BitVec 8)), Wlabel.LIFetch base tvs ∈ ls →
        ifetchOk c.pcImg c.pcLog 0 base tvs) →
      ∃ (c' : Wpcfg P D) (ag' : Wpagent P),
        rtc (wpPfRun pstep pcls) c c' ∧ cfgEqr c c' ∧ c'.pcDev = d' ∧
        c'.pcAgs[i]? = some ag' ∧ ag'.paSt = p' ∧
        wsEqr ag.paWs ag'.paWs ∧
        (instr = false → ag'.paWs.wRes = ag.paWs.wRes) ∧
        c'.pcAgs.map Wpagent.paSt = (c.pcAgs.map Wpagent.paSt).set i p' := by
  intro h
  induction h with
  | nil p d =>
    intro c i ag hlk hst hdev _
    refine ⟨c, ag, rtc_refl _, cfgEqrRefl c, hdev, hlk, hst, wsEqrRefl _, fun _ => rfl, ?_⟩
    exact (listSetLookupId (by simp [List.getElem?_map, hlk, hst])).symm
  | cons p d l p1 d1 ls p' d' hadm hps _ ih =>
    intro c i ag hlk hst hdev hf
    obtain ⟨c1, ag1, hstep, he1, hd1, hl1, hs1, hw1, hr1, hf1⟩ :=
      PfRunUnpinned.admStepPfF pstep pcls instr c i ag l p1 d1 hadm
        (fun b t hl => by subst hl; exact hf b t (List.mem_cons.2 (.inl rfl))) hlk
        (by rw [hst, hdev]; exact hps)
    obtain ⟨c2, ag2, hrun, he2, hd2, hl2, hs2, hw2, hr2, hf2⟩ :=
      ih c1 i ag1 hl1 hs1 hd1
        (fun b t hm => by rw [he1.1, he1.2.1]; exact hf b t (List.mem_cons.2 (.inr hm)))
    refine ⟨c2, ag2, rtc_l ⟨i, l, hstep⟩ hrun, cfgEqrTrans _ _ _ he1 he2, hd2, hl2, hs2,
      wsEqrTrans hw1 hw2, fun hi => (hr2 hi).trans (hr1 hi), ?_⟩
    rw [hf2, hf1, list_insert_insert]

/-- **THE SILENT PAIR SIMULATION.** -/
theorem SilPair.pairSimS (σ : Mstate) (i : Nat) (c : Wpcfg P D) (ag : Wpagent P)
    (pm pm2 p' : P) (l1 l2 : Wlabel) (ls2 : List Wlabel) (dm dm2 dn : D)
    (aq : Bool) (base : Int) (ts : List Nat) (rvs wvs : List (BitVec 8)) (k : WmClass) (q : Nat) :
    cfgMatchd c σ → c.pcAgs[i]? = some ag →
    lblRealizesPair pcls ag.paSt pm2 σ i (.LRmw aq false base ts rvs wvs k) l1 l2 →
    pstep ag.paSt c.pcDev l1 pm dm →
    admRunG pstep false pm dm ls2 pm2 dm2 →
    pstep pm2 dm2 l2 p' dn →
    SilCand.silentOk σ i aq base ts rvs wvs q →
    SilDep.depOkL (SilDep.starWs (SilDep.wsStep ag.paWs l1 c.pcLog.length) ls2 c.pcLog.length) l2 q →
    ∃ c', rtc (SilPf.wpPfRunS pstep pcls) c c' ∧
      cfgMatchd c' (SilCand.silentNext σ i aq base ts wvs q) ∧
      c'.pcAgs.map Wpagent.paSt = (c.pcAgs.map Wpagent.paSt).set i p' ∧
      c'.pcDev = dn ∧
      (∃ ag' : Wpagent P, c'.pcAgs[i]? = some ag' ∧
        ag'.paWs = SilDep.silentWsL
          (SilDep.starWs (SilDep.wsStep ag.paWs l1 c.pcLog.length) ls2 c.pcLog.length) l2 q) ∧
      (∀ j, j ≠ i → c'.pcAgs[j]? = c.pcAgs[j]?) := by
  intro hm hlk hre hps1 hstar hps2 hsil hdep
  have hew := cfgMatchdWs c σ i ag hm hlk
  have hlti := lookup_lt_Some hlk
  obtain ⟨aq', rl, base', tvs, wvs, asrc1, asrc2, vsrc2, rfl, rfl, hnn, hlen, hlb⟩ := hre
  injection hlb with e1 e2 e3 e4 e5 e6 _
  subst e1 e2 e3 e4 e5 e6
  obtain ⟨hwr, -, -, hrd, hq, hts, hcoh, -, hown⟩ := hsil
  obtain ⟨img, lg, f⟩ := σ
  obtain ⟨himg, hlg, hf⟩ := hm
  dsimp only at himg hlg hf hew hrd hq hts hcoh hown ⊢
  subst himg hlg
  have hro : readOk c.pcImg c.pcLog ag.paWs aq false base tvs := by
    have h := wsEqrReadOk _ _ _ _ _ _ _ _ hew (rdOkReadOk _ _ _ _ _ _ _ hrd)
    rwa [zip_fst_snd] at h
  have hstep1 : wpPfStep pstep pcls i (.LExLoad aq base tvs asrc1) c
      ⟨c.pcImg, c.pcLog, dm, c.pcAgs.set i
        ⟨pm, exloadPostRunD ag.paWs aq (srcsView ag.paWs asrc1) base (tvs.map Prod.fst),
         ag.paProm⟩⟩ :=
    wpPfStep.PFExLoad c ag aq base tvs asrc1 pm dm hlk hps1 hro
  have hlk1 : (c.pcAgs.set i
        ⟨pm, exloadPostRunD ag.paWs aq (srcsView ag.paWs asrc1) base (tvs.map Prod.fst),
         ag.paProm⟩)[i]?
      = some ⟨pm, exloadPostRunD ag.paWs aq (srcsView ag.paWs asrc1) base (tvs.map Prod.fst),
          ag.paProm⟩ :=
    list_lookup_insert hlti
  obtain ⟨c2, ag2, hrun2, heq2, hd2, hlk2, hs2, hwx2, hoth2, hfm2, hw2, hr2⟩ :=
    SilDep.admRunRtcW pstep pcls false pm dm ls2 pm2 dm2 hstar
      ⟨c.pcImg, c.pcLog, dm, c.pcAgs.set i
        ⟨pm, exloadPostRunD ag.paWs aq (srcsView ag.paWs asrc1) base (tvs.map Prod.fst),
         ag.paProm⟩⟩ i
      ⟨pm, exloadPostRunD ag.paWs aq (srcsView ag.paWs asrc1) base (tvs.map Prod.fst),
       ag.paProm⟩ hlk1 rfl rfl
      (fun b t hm => absurd hm (admRunGFetchFree pstep _ _ _ _ _ hstar b t))
  have hres2 : ag2.paWs.wRes
      = some ⟨base, tvs.map Prod.fst, ldvOf ag.paWs aq 0 base (tvs.map Prod.fst)⟩ :=
    (hr2 rfl).trans (exloadPostRunDRes _ _ _ _ _)
  have himg2 : c2.pcImg = c.pcImg := heq2.1
  have hlog2 : c2.pcLog = c.pcLog := heq2.2.1
  have hoth : ∀ j agj, j ≠ i → c2.pcAgs[j]? = some agj → wsEqr (f j) agj.paWs := by
    intro j agj hne hj
    obtain ⟨agj1, hj1, he1⟩ := heq2.2.2 j agj hj
    rcases lookupSetCases hj1 with ⟨hji, _⟩ | ⟨_, hj1'⟩
    · exact absurd hji hne
    · exact wsEqrTrans (hf j agj1 hj1') he1
  have hwm : wsEqr (loadPostRun (f i) aq base (tvs.map Prod.fst)) ag2.paWs :=
    wsEqrTrans (wsEqrExloadPostRunD _ _ _ _ _ _ hew) hw2
  have hstep2 : SilPf.wpPfStepS pstep pcls i (.LExStore false base wvs asrc2 vsrc2) c2
      ⟨c2.pcImg, c2.pcLog, dn, c2.pcAgs.set i
        ⟨p', storePostRunD (SilCand.aqRaise ag2.paWs q) false (srcsView ag2.paWs asrc2)
              (srcsView ag2.paWs vsrc2) base wvs.length q, ag2.paProm⟩⟩ := by
    refine SilPf.wpPfStepS.exStoreSilent c2 ag2 base wvs asrc2 vsrc2
      ⟨base, tvs.map Prod.fst, ldvOf ag.paWs aq 0 base (tvs.map Prod.fst)⟩ q p' dn hlk2
      (by rw [hs2, hd2]; exact hps2) hnn hres2 rfl
      (by show (tvs.map Prod.fst).length = wvs.length; rw [List.length_map]; exact hlen)
      ?_ ?_ (by rw [hlog2]; exact hq) ?_ (by rw [hwx2]; exact hdep) (by rw [hlog2]; exact hown)
    · intro j t ht
      refine ⟨(hts j t ht).1, ?_⟩
      rw [himg2, hlog2]
      have hjl : j < tvs.length := by
        have := lookup_lt_Some ht; rw [List.length_map] at this; exact this
      have hv : (tvs.map Prod.snd)[j]? = some (tvs[j]'hjl).2 := by
        rw [List.getElem?_map, List.getElem?_eq_getElem hjl]; rfl
      have hb := (hrd.2 j t _ ht hv).1
      unfold accAddr at hb
      rw [hb, hwr, hv]
    · intro j t ht hw
      apply (hts j t ht).2
      have h := writesInByWritesIn _ _ _ _ _ hw
      rw [hlog2, Nat.add_sub_cancel] at h
      exact h
    · intro j hj
      have h := hcoh j (by rw [List.length_map]; omega)
      rw [← hwm.1]; exact h
  have hrunS : rtc (SilPf.wpPfRunS pstep pcls) c c2 :=
    SilPf.rtcOfOld pstep pcls _ _
      (rtc_l ⟨i, _, hstep1⟩ hrun2)
  refine ⟨_, rtc_r hrunS ⟨i, _, hstep2⟩, ?_, ?_, rfl, ⟨_, List.getElem?_set_self
    (lookup_lt_Some hlk2), by rw [hwx2]; rfl⟩, fun j hj => ?_⟩
  rotate_left 2
  · dsimp only
    rw [List.getElem?_set_ne (Ne.symm hj), hoth2 j hj, List.getElem?_set_ne (Ne.symm hj)]
  · dsimp only [SilCand.silentNext, SilCand.silentPost]
    rw [hlog2, himg2]
    refine cfgMatchdUpdGen _ _ _ _ i ag2 p' _ _ (updWs f i ag2.paWs) _ ?_ hlk2 ?_ ?_
    · intro j agj hj
      by_cases hji : j = i
      · subst hji
        rw [hlk2] at hj
        cases hj
        rw [updWsEq]
        exact wsEqrRefl _
      · rw [updWsNe _ _ _ _ hji]
        exact hoth j agj hji hj
    · rw [updWsEq]
      exact wsEqrStorePostRunD _ _ _ _ _ _ _ _ (SilPair.wsEqrAqRaise _ _ q hwm)
    · intro j hne
      rw [updWsNe _ _ _ _ hne, updWsNe _ _ _ _ hne]
  · dsimp only
    rw [list_fmap_insert, hfm2, list_insert_insert]
    dsimp only
    rw [list_fmap_insert, list_insert_insert]

end twin

end Weak
