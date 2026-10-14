/-
Weak: **W10-2 [OWN.94] (N2′), increment 6 — THE LOCKSTEP STEP: the emission's block, re-answered by
the machine, is the walk's step** (`PROGRESS-W10N2p.md`).  Lean-only, no Rocq twin.

The pinned twins are `WeakRvwmoCert2.certBlockRead`/`cblkRetime`/`certBlockPair` (a `hemit` block
at the CONSTANT fabric, re-timed to the candidate's log).  At the Zifencei bundle a hart's block
(`GraphFetchBlocks.blkOne`/`blkPair`, extracted from its `hemitf` emission by
`GraphFetchBlocks.hemitfBlocks`) runs between the emission's fabric endpoints `d → d'` (any `d` when
contact-free), its leading star carries FETCHES, and the walk answers every read and every fetch
with the LATEST bytes (`CertZ4.machLbl`, `CertZ4` header).  When the hart's certified state IS the
emission's (lockstep), its `wRelp` agrees, the fabric is the block's, and the latest VALUES are the
emission's (value agreement: what W10-3's invariant maintains, or W10-4's poison breaks), the block
re-answered is the walk's step:

  §1  re-answering a fetch (`CertZ5.fetchRet`) and the leading star (`CertZ5.admRunGRet`, through
      `pstepEvTsIfetch`); THE WALK-TIME FETCH CUT for a latest fetch (`CertZ5.fetchCutLatest`: the
      cut at the log's end, given the instruction view below it);
  §2  re-answering the realizing step (`CertZ5.oneRet`: a plain load through `pstepEvTsLoad`, any
      other fused label verbatim, its class moved by `wRelp` alone) and the exclusive pair
      (`CertZ5.pairRet`: the exclusive read through `pstepEvTsExload`, the RMW's class through
      `loadPostRunRelpEv`);
  §3  **`CertZ5.lockstepOne`** / **`CertZ5.lockstepPair`** — the step obligation `CertZ2.stepOkZ`
      of the machine label, from the emission's block.

Spec: the Sail step is oblivious to read/fetch TIMESTAMPS (`pstepEvTs*`, merged); the cut form is
M2's trusted clause, met at the log's end; FAITHFUL.  Lean-only helpers file-qualified
(`CertZ5.*`).
-/
import Weak.CertZ4

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open TsoShadow

/-! # 1. Fetches, re-answered -/

/-- A wlabel's FETCH re-answered by the latest bytes of the candidate's log. -/
def CertZ5.fetchRet (c : Cand) (l : Wlabel) : Wlabel :=
  match l with
  | .LIFetch base tvs => .LIFetch base (witTvs c base tvs.length)
  | l => l

theorem CertZ5.fetchRetAdmin (c : Cand) (instr : Bool) (l : Wlabel) :
    lbAdmin instr l → lbAdmin instr (CertZ5.fetchRet c l) := by
  cases l <;> simp [CertZ5.fetchRet, lbAdmin]

/-- Fetch value agreement on a star: every fetch's bytes are the log's latest bytes. -/
def CertZ5.fetchAgree (c : Cand) (ls : List Wlabel) : Prop :=
  ∀ (base : Int) (tvs : List (Nat × BitVec 8)), Wlabel.LIFetch base tvs ∈ ls →
    (witTvs c base tvs.length).map Prod.snd = tvs.map Prod.snd ∧
    latestBytesOk c base tvs.length

/-- **THE LEADING STAR, RE-ANSWERED**: a star whose fetches agree in value with the latest bytes is a
star with them re-answered (`pstepEvTsIfetch`). -/
theorem CertZ5.admRunGRet (c : Cand) (instr : Bool) (p : Pexv6) (d : Efab) (ls : List Wlabel)
    (p' : Pexv6) (d' : Efab) :
    admRunG pstepEv instr p d ls p' d' → CertZ5.fetchAgree c ls →
    admRunG pstepEv instr p d (ls.map (CertZ5.fetchRet c)) p' d' := by
  intro h
  induction h with
  | nil p d => intro _; exact .nil p d
  | cons p d l p1 d1 ls p' d' ha hs _ ih =>
    intro hag
    rw [List.map_cons]
    refine .cons p d _ p1 d1 _ p' d' (CertZ5.fetchRetAdmin c instr l ha) ?_
      (ih (fun base tvs hm => hag base tvs (List.mem_cons_of_mem _ hm)))
    cases l with
    | LIFetch base tvs =>
      exact pstepEvTsIfetch _ _ _ _ _ _ _ hs (hag base tvs (by simp)).1
    | _ => exact hs

/-- **THE WALK-TIME FETCH CUT** for a latest fetch: the cut at the log's end (the instruction view
below it), every byte its latest write. -/
theorem CertZ5.fetchCutLatest (c : Cand) (itv x : Nat) (base : Int) (n : Nat) :
    itv ≤ (cdLogEnd c).length → latestBytesOk c base n →
    PfRunUnpinned.fcutM2 itv (candLastSt c).msImg (candLastSt c).msLog x base
      (witTvs c base n) := by
  intro hitv hb
  rw [candLastImg, candLastLog]
  have hent : ∀ (j t : Nat) (v : BitVec 8), (witTvs c base n)[j]? = some (t, v) →
      j < n ∧ t = latestTs (cdLogEnd c) (accAddr base j) ∧
      logByte c.cdImg (cdLogEnd c) t (accAddr base j) = some v := by
    intro j t v hj
    have h1 : ((witTvs c base n).map Prod.fst)[j]? = some t := by
      rw [List.getElem?_map, hj]; rfl
    have h2 : ((witTvs c base n).map Prod.snd)[j]? = some v := by
      rw [List.getElem?_map, hj]; rfl
    rw [witTvsFst] at h1
    rw [witTvsSnd] at h2
    obtain ⟨hjn, rfl⟩ := lrdTsLookup c base n j t h1
    refine ⟨hjn, rfl, ?_⟩
    have h2' := h2
    unfold lrdVs at h2'
    rw [List.getElem?_map, lookup_seq_lt hjn, Nat.zero_add, Option.map_some,
      Option.some.injEq] at h2'
    obtain ⟨v0, hv0⟩ := Option.isSome_iff_exists.1 (hb j hjn)
    rw [hv0, Option.getD_some] at h2'
    rw [hv0, h2']
  refine ⟨(cdLogEnd c).length, hitv, Nat.le_refl _, fun j t v hj => ?_, fun j t v hj => ?_⟩
  · obtain ⟨-, rfl, hv⟩ := hent j t v hj
    refine ⟨hv, ?_⟩
    have hle := logByteBounded _ _ _ _ (by rw [hv]; rfl)
    rw [show max (latestTs (cdLogEnd c) (accAddr base j)) (cdLogEnd c).length =
      (cdLogEnd c).length by omega]
    exact latestTsTop _ _
  · obtain ⟨-, -, hv⟩ := hent j t v hj
    exact logByteBounded _ _ _ _ (by rw [hv]; rfl)

/-! # 2. The realizing step and the pair, re-answered -/

theorem CertZ5.wlblRenId (l : Wlabel) : wlblRen (fun t => t) l = l := by
  have htv : ∀ (tvs : List (Nat × BitVec 8)), tvs.map (tvRen fun t => t) = tvs := by
    intro tvs
    induction tvs with
    | nil => rfl
    | cons tv tvs ih => simp only [List.map_cons, ih]; rfl
  cases l <;> simp only [wlblRen, htv]

/-- A realizing label's class moves with `wRelp` alone. -/
theorem CertZ5.hlblRealizesRelp (p : Pexv6) (ws ws' : Wstate) (lb : Lbl) (l : Wlabel) :
    ws'.wRelp = ws.wRelp → hlblRealizes p ws lb l → hlblRealizes p ws' lb l := by
  intro hr h
  have := hlblRealizesRen (fun t => t) p ws ws' lb l hr h
  rwa [lblRenId, CertZ5.wlblRenId] at this

/-- The fused realizing step, re-answered: a plain load reads the latest bytes (values agreeing),
any other fused label is verbatim; the realized label is the machine label. -/
theorem CertZ5.oneRet (c : Cand) (pa : Pexv6) (da : Efab) (ws ws' : Wstate) (lb : Lbl)
    (l : Wlabel) (p' : Pexv6) (d' : Efab) :
    ws'.wRelp = ws.wRelp → lbFused l → hlblRealizes pa ws lb l → pstepEv pa da l p' d' →
    (∀ aq base ts vs, lb = .LLoad aq base ts vs → lrdVs c base ts.length = vs) →
    ∃ l', lbFused l' ∧ hlblRealizes pa ws' (CertZ4.machLbl c lb) l' ∧ pstepEv pa da l' p' d' := by
  intro hr hf hre hst hval
  have hre' := CertZ5.hlblRealizesRelp pa ws ws' lb l hr hre
  obtain ⟨hnb, hlat, hrf, hpr⟩ := hre'
  cases l with
  | LLoad aq lat base tvs asrc =>
    simp only [latFree] at hlat
    simp only [lbRfoldfree] at hrf
    subst hlat hrf
    simp only [projLbl, Option.some.injEq] at hpr
    subst hpr
    have hv := hval aq base _ _ rfl
    rw [List.length_map] at hv
    refine ⟨.LLoad aq false base (witTvs c base tvs.length) [], trivial,
      ⟨trivial, rfl, rfl, ?_⟩, ?_⟩
    · simp only [projLbl, CertZ4.machLbl, List.length_map, witTvsFst, witTvsSnd]
    · exact pstepEvTsLoad _ _ _ _ _ _ _ _ hst (by rw [witTvsSnd, hv])
  | LRmw aq rl base tvs data asrc vsrc =>
    exact absurd hst (pstepEvNoRmw _ _ _ _ _ _ _ _ _ _ _)
  | LExLoad => exact absurd hf (by simp [lbFused])
  | LExStore => exact absurd hf (by simp [lbFused])
  | LSilent => simp [projLbl] at hpr
  | LRegW => simp [projLbl] at hpr
  | LCtrl => simp [projLbl] at hpr
  | LInstr => simp [projLbl] at hpr
  | LIFetch => simp [projLbl] at hpr
  | LStore rl base data asrc vsrc =>
    simp only [projLbl, Option.some.injEq] at hpr
    subst hpr
    exact ⟨_, hf, ⟨hnb, trivial, hrf, rfl⟩, hst⟩
  | LFence pr pw sr sw =>
    simp only [projLbl, Option.some.injEq] at hpr
    subst hpr
    exact ⟨_, hf, ⟨hnb, trivial, hrf, rfl⟩, hst⟩
  | LDev kd base vs sa sv =>
    simp only [projLbl, Option.some.injEq] at hpr
    subst hpr
    exact ⟨_, hf, ⟨hnb, trivial, hrf, rfl⟩, hst⟩

/-- The exclusive pair, re-answered: the exclusive read reads the latest bytes (values agreeing);
the realized label is the machine label (its class through `wRelp`). -/
theorem CertZ5.pairRet (c : Cand) (pa pm2 : Pexv6) (ws ws' : Wstate) (lb : Lbl) (l1 l2 : Wlabel) :
    ws'.wRelp = ws.wRelp → hlblRealizesPair pa pm2 ws lb l1 l2 →
    (∀ aq rl base ts rvs wvs kc, lb = .LRmw aq rl base ts rvs wvs kc →
      lrdVs c base ts.length = rvs) →
    ∃ l1', hlblRealizesPair pa pm2 ws' (CertZ4.machLbl c lb) l1' l2 ∧
      ∀ (da : Efab) (pm : Pexv6) (dm : Efab), pstepEv pa da l1 pm dm → pstepEv pa da l1' pm dm := by
  rintro hr ⟨aq, rl, base, tvs, data, asrc1, asrc2, vsrc2, rfl, rfl, hne, hlen, rfl⟩ hval
  have hv := hval aq rl base _ _ _ _ rfl
  rw [List.length_map] at hv
  refine ⟨.LExLoad aq base (witTvs c base tvs.length) asrc1,
    ⟨aq, rl, base, witTvs c base tvs.length, data, asrc1, asrc2, vsrc2, rfl, rfl, hne,
      by rw [witTvsLength]; exact hlen, ?_⟩,
    fun da pm dm h => pstepEvTsExload _ _ _ _ _ _ _ _ _ h (by rw [witTvsSnd, hv])⟩
  simp only [CertZ4.machLbl, List.length_map, witTvsFst, witTvsSnd]
  rw [WeakRvwmoConf.pclsEvRelp pm2 _ (loadPostRun ws aq base (tvs.map Prod.fst))
    (loadPostRun ws' aq base (lrdTs c base tvs.length))
    (by rw [loadPostRunRelpEv, loadPostRunRelpEv, hr])]

/-! # 3. THE LOCKSTEP STEP -/

/-- The fetch cut of a re-answered star. -/
theorem CertZ5.starCut (c : Cand) (itv x : Nat) (ls : List Wlabel) :
    itv ≤ (cdLogEnd c).length → CertZ5.fetchAgree c ls →
    ∀ (base : Int) (tvs : List (Nat × BitVec 8)),
      Wlabel.LIFetch base tvs ∈ ls.map (CertZ5.fetchRet c) →
      PfRunUnpinned.fcutM2 itv (candLastSt c).msImg (candLastSt c).msLog x base tvs := by
  intro hitv hag base tvs hm
  obtain ⟨l0, hl0, he⟩ := List.mem_map.1 hm
  cases l0 with
  | LIFetch base0 tvs0 =>
    simp only [CertZ5.fetchRet, Wlabel.LIFetch.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    exact CertZ5.fetchCutLatest c itv x base0 tvs0.length hitv (hag base0 tvs0 hl0).2
  | _ => simp [CertZ5.fetchRet] at he

/-- **`CertZ5.lockstepOne`** — A FUSED BLOCK OF THE EMISSION IS THE WALK'S STEP: from the hart's
emission state at the candidate's end fabric (its `wRelp` agreeing), the machine label's step
obligation, the leading star and every read re-answered by the latest bytes (values agreeing). -/
theorem CertZ5.lockstepOne (St : CycState) (itvOf : Nat → Nat → Nat) (x : Nat) (lb : Lbl)
    (ws : Wstate) (ls : List Wlabel) (l : Wlabel) (pE pE' : Pexv6) (d' : Efab) :
    srvwmoConsistent St.cstC → CertZ4.lblShape lb → CertZ4.readFoot St.cstC lb →
    ((candLastSt St.cstC).msWs x).wRelp = ws.wRelp →
    lbFused l →
    GraphFetchBlocks.blkOne (St.cstDv (cdEnd St.cstC)) d' ws lb ls l pE pE' →
    CertZ5.fetchAgree St.cstC ls →
    (∀ aq base ts vs, lb = .LLoad aq base ts vs → lrdVs St.cstC base ts.length = vs) →
    itvOf (cdEnd St.cstC) x ≤ (cdLogEnd St.cstC).length →
    ∃ (pa : Pexv6) (da : Efab),
      CertZ2.stepOkZ St itvOf x (CertZ4.machLbl St.cstC lb) pE pa da
        (ls.map (CertZ5.fetchRet St.cstC)) pE' d' := by
  intro hc hsh hft hr hf ⟨pa, da, hrun, hre, hst⟩ hfag hval hitv
  obtain ⟨hmok, hld⟩ := CertZ4.machLblOk St.cstC x lb hc hsh hft
  obtain ⟨l', hf', hre', hst'⟩ :=
    CertZ5.oneRet St.cstC pa da ws ((candLastSt St.cstC).msWs x) lb l pE' d' hr hf hre hst hval
  exact ⟨pa, da, hmok, hld, CertZ5.admRunGRet St.cstC true pE _ ls pa da hrun hfag,
    CertZ5.starCut St.cstC _ x ls hitv hfag, .inl ⟨l', hf', hre', hst'⟩⟩

/-- **`CertZ5.lockstepPair`** — AN EXCLUSIVE-PAIR BLOCK (an AMO) OF THE EMISSION IS THE WALK'S STEP. -/
theorem CertZ5.lockstepPair (St : CycState) (itvOf : Nat → Nat → Nat) (x : Nat) (lb : Lbl)
    (ws : Wstate) (ls : List Wlabel) (l : Wlabel) (pE pE' : Pexv6) (d' : Efab) :
    srvwmoConsistent St.cstC → CertZ4.lblShape lb → CertZ4.readFoot St.cstC lb →
    ((candLastSt St.cstC).msWs x).wRelp = ws.wRelp →
    GraphFetchBlocks.blkPair (St.cstDv (cdEnd St.cstC)) d' ws lb ls l pE pE' →
    CertZ5.fetchAgree St.cstC ls →
    (∀ aq rl base ts rvs wvs kc, lb = .LRmw aq rl base ts rvs wvs kc →
      lrdVs St.cstC base ts.length = rvs) →
    itvOf (cdEnd St.cstC) x ≤ (cdLogEnd St.cstC).length →
    ∃ (pa : Pexv6) (da : Efab),
      CertZ2.stepOkZ St itvOf x (CertZ4.machLbl St.cstC lb) pE pa da
        (ls.map (CertZ5.fetchRet St.cstC)) pE' d' := by
  intro hc hsh hft hr ⟨pa, da, pm, dm, ls2, pm2, dm2, l2, hrun, hpair, hst1, hrun2, hst2⟩ hfag
    hval hitv
  obtain ⟨hmok, hld⟩ := CertZ4.machLblOk St.cstC x lb hc hsh hft
  obtain ⟨l1', hpair', hst1'⟩ :=
    CertZ5.pairRet St.cstC pa pm2 ws ((candLastSt St.cstC).msWs x) lb l l2 hr hpair hval
  exact ⟨pa, da, hmok, hld, CertZ5.admRunGRet St.cstC true pE _ ls pa da hrun hfag,
    CertZ5.starCut St.cstC _ x ls hitv hfag,
    .inr ⟨pm, dm, ls2, pm2, dm2, l1', l2, hpair', hst1' da pm dm hst1, hrun2, hst2⟩⟩

/-! # 4. The instruction view is below the log -/

/-- **THE INSTRUCTION VIEW BOUND**: in a threaded state, every agent's instruction view at index
`k` is at most the log length there (M2's recurrence raises it only to a `fence.i` value of the
trace shadow, which §1 of `CertZ4` bounds). -/
theorem CertZ5.itvBound (d0 : Efab) (St : CycState) (itvOf : Nat → Nat → Nat)
    (fiOf : Nat → Nat → Bool) :
    CertZ.cstOkZW d0 St itvOf fiOf →
    ∀ k, k ≤ cdEnd St.cstC → ∀ ag, itvOf k ag ≤ (cdLog St.cstC k).length := by
  intro ⟨_, hi0, _, ⟨hSC, _, _⟩, _⟩ k
  induction k with
  | zero => intro _ ag; rw [hi0 ag]; exact Nat.zero_le _
  | succ k ih =>
    intro hk ag
    have hk' : k < St.cstC.cdTr.length := hk
    obtain ⟨s, hs⟩ : ∃ s, St.cstC.cdTr[k]? = some s :=
      ⟨St.cstC.cdTr[k], List.getElem?_eq_getElem hk'⟩
    have hle : (cdLog St.cstC k).length ≤ (cdLog St.cstC (k + 1)).length :=
      cdLogLenLe _ _ _ (Nat.le_succ k)
    obtain ⟨-, -, -, -, -, ls, -, -, -, -, ⟨-, -, hitv, hfr⟩, -⟩ := hSC k s hs
    by_cases hag : ag = s.esAg
    · subst hag
      rw [hitv]
      unfold PfRunUnpinned.itvStep
      rw [show (candExec St.cstC).exTr[k]? = some s from hs]
      dsimp only
      have ih' := ih (by omega) s.esAg
      split
      · have hb := CertZ4.shadowRunBnd s.esAg ((candExec St.cstC).exTr.take k)
        rw [CertZ4.shadowAuthorsLen] at hb
        obtain ⟨htv, hrv, -⟩ := hb
        have hpub := MachCSL.ownPubAux_le s.esAg
          (shadowRun cohSrc s.esAg ((candExec St.cstC).exTr.take k)).1 0
        rw [CertZ4.shadowAuthorsLen] at hpub
        have hlog : (trMsgs ((candExec St.cstC).exTr.take k)).length = (cdLog St.cstC k).length :=
          rfl
        unfold MachCSL.fencePost
        unfold MachCSL.ownPub
        simp only [↓reduceIte, Bool.false_eq_true]
        omega
      · omega
    · rw [(hfr ag hag).2]
      have := ih (by omega) ag
      omega

end Weak
