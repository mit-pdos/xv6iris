/-
Weak: **allocproc route P, row P-W6 on the S-R walk — `SimRelP`'s MEMORY HALF and its item steps**
(`PROGRESS-PW6.md` CP-PW6-8 resume step 1).  Lean-only, no Rocq twin.  A PRIMED TWIN: nothing registered imports
this file.

**`RmemR img G c σ ι`** relates a walk candidate `c` (its current state `SbWalk.cur c`) to a MachCSL state `σ`:
the state map `SbRealP.rmemP`, the issue-stamp relation `SbRealPStamp.StampRel` (stamps ↔ walk items), and
`SbRealPRView.RView` at every hart (MachCSL's floors dominated in GF terms).  Each walk item is answered by its
MachCSL move with `RmemR` kept:

  §1  **`landStepR`** — an enabled S-R landing (`SbOrdR.landR`) of hart `cpu`'s `k`-th pending store is MachCSL's
      `landOk` landing of the matching stamp: `ForeignBelowLanded` from the stamp map and `IssueCo`
      (`SbRealPStamp.foreignBelowOfStamp`), the state map (`SbRealP.rmemPLand`), the stamps (`stampLand`), the
      views (`rviewLandOwn` for the hart, `rviewFrame` for the others).
  §2  **`issueStepR`** — a plain store event is MachCSL's issue (`SbRealP.rmemPIssue`, `stampIssue`,
      `rviewIssue`, `rviewFrame`).

Spec: FAITHFUL (proof organisation; the one named input is `SbIssueCo.IssueCo`, discharged by the census
`SbIssueCoR.issueCoOfCustodyR`).  Lean-only helpers `SbRealPSim.*`.
-/
import Weak.SbRealPStamp
import Weak.SbRealPRViewStep
import Weak.SbRealPDma

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open Lbl PfStepTsoMem SbRealP SbRealPView SbRealPRView SbRealPRViewStep SbRealPStamp

namespace SbRealPSim

open SbWalk SbAgree SbReplay SbOrd SpikeSP SbDom SpikeSR

/-! # 0. The memory half of `SimRelP` -/

/-- **`SimRelP`'S MEMORY HALF** at a walk candidate and a MachCSL state. -/
structure RmemR (img : Image) (G : Gexec) (c : CandW) (σ : MState) (ι : Nat → Nat) : Prop where
  mem : rmemP img (SbWalk.cur c).σ σ
  stamp : StampRel c σ ι
  view : ∀ cpu, RView G (SbWalk.cur c) σ cpu

/-- The landing top is the landed write count (`R-log` + S-P). -/
theorem ltopWrW {N : Nat} {img : Image} {G : Gexec} {X : Geid → Prop} {dev : List Geid} {w : WS} {σ : MState}
    (hP : SbOrdR.PInvR N img G X dev w) (hR : rmemP img w.σ σ) : σ.ltop = (wrW w).length := by
  obtain ⟨hlogLen, -⟩ := logAt img G w hP.inv hP.spw
  have h1 := congrArg List.length hR.2.1
  simp only [List.length_map, landAuthors] at h1
  show σ.llog.length = _
  rw [← h1, hlogLen]

theorem curSnoc (c : CandW) (it : Item) : SbWalk.cur (snocC c it) = nextI (SbWalk.cur c) it := by
  unfold SbWalk.cur; rw [snocLen]; exact stAtSnocEnd c _

theorem nextLLog (σ : SbCand.CandS) (i k : Nat) : σ.ms.msLog <+: (SbCand.nextL σ i k).ms.msLog := by
  unfold SbCand.nextL
  split
  · exact ⟨_, rfl⟩
  · exact List.prefix_refl _

theorem nextLSb (σ : SbCand.CandS) (i k j : Nat) (e : SbEnt) (he : e ∈ (SbCand.nextL σ i k).sb j) :
    e ∈ σ.sb j := by
  unfold SbCand.nextL at he
  split at he
  · show e ∈ σ.sb j
    by_cases hj : j = i
    · subst hj
      have he' : e ∈ (σ.sb j).eraseIdx k := by simpa [SbCand.updSb] using he
      exact List.mem_of_mem_eraseIdx he'
    · simpa [SbCand.updSb, hj] using he
  · exact he

theorem nextLSbNe (σ : SbCand.CandS) (i k j : Nat) (hj : j ≠ i) : (SbCand.nextL σ i k).sb j = σ.sb j := by
  unfold SbCand.nextL
  split
  · exact SbCand.updSbNe _ _ _ _ hj
  · rfl

/-! # 1. The landing item -/

/-- **THE LANDING ITEM**: an enabled S-R landing of hart `cpu`'s `k`-th pending store is MachCSL's landing of the
matching stamp, `RmemR` kept. -/
theorem landStepR {N : Nat} {X : Geid → Prop} {dev : List Geid} (img : Image) (G : Gexec) (hc : CatH G)
    (hnd : G.gxGmo.Nodup) (c : CandW) (σ : MState) (ι : Nat → Nat) (hM : RmemR img G c σ ι)
    (hP : SbOrdR.PInvR N img G X dev (SbWalk.cur c)) (hco : SbIssueCo.IssueCo G c) (cpu : CPU) (k : Nat)
    (hg : SbOrdR.landR SbPol.epoch G (SbWalk.cur c) (hartAgent cpu) k) :
    ∃ s, (σ.sb cpu)[k]? = some s ∧ σ.landOk cpu s.1 ∧
      RmemR img G (snocC c (.land (hartAgent cpu) k)) (σ.land cpu s.1) ι := by
  obtain ⟨p, hp, hpol, hS⟩ := id hg
  obtain ⟨s, hs, hland⟩ := rmemPLand img (SbWalk.cur c).σ σ cpu k hM.mem hpol
  have hfbl := foreignBelowOfStamp SbPol.epoch G c σ ι hco hnd hP hM.mem hM.stamp.1 hM.stamp.2.1 cpu k hg s hs
  obtain ⟨hok', hR'⟩ := hland hfbl
  have hok := hM.mem.2.2.2.2.2.2.2.2
  have hcurE := (curSnoc c (.land (hartAgent cpu) k)).trans (landEq (hartAgent cpu) k p hp)
  -- the landed write: GF's next write, realized, a store of the hart
  have hpm : p ∈ (SbWalk.cur c).pend (hartAgent cpu) := List.mem_of_getElem? hp
  obtain ⟨rl, base, vs, kc, hl, -, -⟩ := SbOrdR.pendLblR hP _ p hpm
  have hWg : (hartAgent cpu, p.1) ∈ gwrites G := by
    obtain ⟨T, hT⟩ := hS; rw [← hT]; simp
  have hWgw : gwix G (hartAgent cpu, p.1) = σ.llog.length + 1 := by
    rw [wixOfNext _ _ hnd hS]
    have := ltopWrW hP hM.mem
    simp only [MState.ltop] at this
    omega
  have hWlt := SbOrdR.pendRealizedR hP _ p hpm
  have hsm : s ∈ σ.sb cpu := List.mem_of_getElem? hs
  obtain ⟨-, -, hs3, -⟩ := (hok.2.2.2.2.2.2.1 cpu s.1).1 ⟨s.2, hsm⟩
  have hown : σ.log.getD (s.1 - 1) diskAgent = hartAgent cpu := by
    rw [List.getD_eq_getElem?_getD, hs3]; rfl
  refine ⟨s, hs, hok', ⟨by rw [hcurE]; exact hR', stampLand c σ ι hM.stamp hok cpu k s hs p hp, fun cpu' => ?_⟩⟩
  have hrows : (SbWalk.cur (snocC c (.land (hartAgent cpu) k))).rows = (SbWalk.cur c).rows := by rw [hcurE]
  have hlog : (SbWalk.cur c).σ.ms.msLog <+: (SbWalk.cur (snocC c (.land (hartAgent cpu) k))).σ.ms.msLog := by
    rw [hcurE]; exact nextLLog _ _ _
  have hsb : ∀ j, ∀ e ∈ (SbWalk.cur (snocC c (.land (hartAgent cpu) k))).σ.sb j,
      ∃ e0 ∈ (SbWalk.cur c).σ.sb j, e0.msg = e.msg := by
    intro j e he
    rw [hcurE] at he
    exact ⟨e, nextLSb _ _ _ _ e he, rfl⟩
  by_cases hcc : cpu' = cpu
  · subst hcc
    exact rviewLandOwn G hc _ _ σ cpu' s.1 (hM.view cpu') hown _ hWg hWgw rfl hWlt _ hl rfl
      (by rw [hrows]) hlog (hsb _)
  · have hne : hartAgent cpu ≠ hartAgent cpu' := fun h => hcc (SbRealP.hartAgentInj h).symm
    exact rviewFrame G _ _ σ (σ.land cpu s.1) cpu' (hM.view cpu') rfl rfl
      (pubLandOther σ cpu' s.1 (by rw [hown]; exact hne)) (Nat.le_of_eq (by rw [hrows]))
      (fun W a u _ h1 h2 => by rw [hrows] at h2; omega) hlog (hsb _)

/-! # 2. The plain store's issue -/

theorem paZInj (a b : PAddr) (h : paZ a = paZ b) : a = b :=
  BitVec.eq_of_toNat_eq (by unfold paZ at h; omega)

/-- A byte of the footprint, as an accessed address, is in it. -/
theorem inFpOf (pa : PAddr) (n : Nat) (hnw : pa.toNat + n ≤ 2 ^ 64) (a : PAddr) (j : Nat) (hj : j < n)
    (h : paZ a = accAddr (paZ pa) j) : inFp pa n a = true := by
  have ha : a = pa + BitVec.ofNat 64 j := paZInj _ _ (by rw [h, paZAddJ pa n j hnw hj])
  unfold inFp
  rw [List.any_eq_true]
  exact ⟨j, List.mem_range.2 hj, by rw [ha]; exact beq_self_eq_true _⟩

theorem nextIEv (w : WS) (s : Estep) :
    nextI w (.ev s) = ⟨SbCand.nextE w.σ s.esAg s.esLb, upd w.pend s.esAg (pendE w s.esAg s.esLb),
      upd w.rows s.esAg (w.rows s.esAg ++ [s.esLb]), upd w.fw s.esAg (w.fw s.esAg ++ [fwOf (w.pend s.esAg) s.esLb]),
      if gmoEv s.esLb then w.gmo ++ [(s.esAg, (w.rows s.esAg).length)] else w.gmo⟩ := rfl

theorem rowsEvSelf (w : WS) (s : Estep) : ((nextI w (.ev s)).rows s.esAg).length = (w.rows s.esAg).length + 1 := by
  rw [nextIEv]; simp [updEq]

theorem rowsEvNe (w : WS) (s : Estep) (y : Nat) (hy : y ≠ s.esAg) : (nextI w (.ev s)).rows y = w.rows y := by
  rw [nextIEv]; exact updNe _ _ _ _ hy

/-- **THE ISSUE ITEM**: a plain store event of hart `cpu` (GF's label at its head) is MachCSL's issue,
`RmemR` kept (the new stamp maps to the item). -/
theorem issueStepR {N : Nat} {X : Geid → Prop} {dev : List Geid} (img : Image) (G : Gexec) (hc : CatH G)
    (c : CandW) (σ : MState) (ι : Nat → Nat) (hM : RmemR img G c σ ι)
    (hP : SbOrdR.PInvR N img G X dev (SbWalk.cur c)) (cpu : CPU) (pa : PAddr) (n : Nat) (v : BitVec (8 * n))
    (vs : List (BitVec 8)) (k : WmClass) (hram : ramBytes pa n) (hvl : vs.length = n)
    (hb : ∀ j, j < n → vs[j]? = some (nthByte v j))
    (hgl : gxLbl G (hd (SbWalk.cur c) (hartAgent cpu)) = some (LStore false (paZ pa) vs k)) :
    RmemR img G (snocC c (.ev ⟨hartAgent cpu, LStore false (paZ pa) vs k⟩)) (σ.issue cpu pa n v)
      (ιNew ι σ.top c.its.length) := by
  have hok := hM.mem.2.2.2.2.2.2.2.2
  have hnw := noWrapOfRam pa n hram
  let s : Estep := ⟨hartAgent cpu, LStore false (paZ pa) vs k⟩
  have hcur := curSnoc c (.ev s)
  -- the walk's post-state
  have hpe : ∀ i, (SbWalk.cur (snocC c (.ev s))).pend i =
      if i = hartAgent cpu then (SbWalk.cur c).pend (hartAgent cpu) ++
        [(((SbWalk.cur c).rows (hartAgent cpu)).length,
          SbCand.issueEnt (SbWalk.cur c).σ (hartAgent cpu) false (paZ pa) vs k)]
      else (SbWalk.cur c).pend i := by
    intro i
    rw [hcur, nextIEv]
    show upd _ (hartAgent cpu) _ i = _
    by_cases hi : i = hartAgent cpu
    · subst hi; rw [updEq, if_pos rfl]; rfl
    · rw [updNe _ _ _ _ hi, if_neg hi]
  have hlen : (σ.sb cpu).length = ((SbWalk.cur c).pend (hartAgent cpu)).length := by
    rw [(hM.mem.2.2.2.2.1 cpu).length_eq, hP.inv.sb, List.length_map]
  have hsbE : ∀ i, (SbWalk.cur (snocC c (.ev s))).σ.sb i =
      if i = hartAgent cpu then (SbWalk.cur c).σ.sb (hartAgent cpu) ++
        [SbCand.issueEnt (SbWalk.cur c).σ (hartAgent cpu) false (paZ pa) vs k]
      else (SbWalk.cur c).σ.sb i := by
    intro i
    rw [hcur, nextIEv]
    show SbCand.updSb _ (hartAgent cpu) _ i = _
    by_cases hi : i = hartAgent cpu
    · subst hi; rw [SbCand.updSbEq, if_pos rfl]
    · rw [SbCand.updSbNe _ _ _ _ hi, if_neg hi]
  have hlogE : (SbWalk.cur (snocC c (.ev s))).σ.ms.msLog = (SbWalk.cur c).σ.ms.msLog := by
    rw [hcur, nextIEv]; rfl
  refine ⟨?_, stampIssue c σ ι hM.stamp hok cpu pa n v s rfl hlen _ hpe, fun cpu' => ?_⟩
  · rw [hcur, nextIEv]
    exact rmemPIssue img _ σ cpu pa n v vs k hram hvl hb hM.mem
  · by_cases hcc : cpu' = cpu
    · subst hcc
      refine rviewIssue G hc.wf _ _ σ cpu' pa n v (hM.view cpu') hok (by rw [hcur]; exact rowsEvSelf _ s)
        (fun a u hwb => ?_) (by rw [hlogE]; exact List.prefix_refl _) (fun e he => ?_)
      · obtain ⟨l, b0, vs0, j, hl0, hw0, hv0, ha0⟩ := hwb
        have hl1 : gxLbl G (hd (SbWalk.cur c) (hartAgent cpu')) = some l := hl0
        rw [hgl, Option.some.injEq] at hl1
        subst hl1
        simp only [lbWr, Option.some.injEq, Prod.mk.injEq] at hw0
        obtain ⟨rfl, rfl⟩ := hw0
        exact inFpOf pa n hnw a j (by rw [← hvl]; exact lookup_lt_Some hv0) ha0.symm
      · rw [hsbE, if_pos rfl] at he
        rcases List.mem_append.1 he with he | he
        · exact .inl ⟨e, he, rfl⟩
        · simp only [List.mem_singleton] at he
          subst he
          refine .inr (fun a ha => ?_)
          obtain ⟨j, hj, haj⟩ := msgByteIndex (paZ pa) vs _ _ (paZ a) ha
          exact inFpOf pa n hnw a j (by omega) haj
    · have hne : hartAgent cpu' ≠ hartAgent cpu := fun h => hcc (SbRealP.hartAgentInj h)
      have hrw : (SbWalk.cur (snocC c (.ev s))).rows (hartAgent cpu') = (SbWalk.cur c).rows (hartAgent cpu') := by
        rw [hcur]; exact rowsEvNe _ s _ hne
      refine rviewFrame G _ _ σ (σ.issue cpu pa n v) cpu' (hM.view cpu') rfl ?_ ?_ (Nat.le_of_eq (by rw [hrw]))
        (fun W a u _ h1 h2 => by rw [hrw] at h2; omega) (by rw [hlogE]; exact List.prefix_refl _) (fun e he => ?_)
      · show (if cpu' = cpu then _ else _) = _; rw [if_neg hcc]
      · unfold ownPubL
        show ownPub _ (landAuthors (σ.log ++ [hartAgent cpu]) σ.llog) = _
        rw [landAuthorsSnocLog σ.log σ.llog _ hok.2.2.2.2.1]
      · rw [hsbE, if_neg hne] at he
        exact ⟨e, he, rfl⟩

/-! # 3. Frame facts of a non-store event -/

/-- An event whose label is not a store and not a `pw ∧ sw` fence leaves the pending tags and the twin buffers'
messages; a `pw ∧ sw` fence only bumps the entries. -/
theorem tagsEv (w : WS) (s : Estep) (hst : isSt s.esLb = false) (i : Nat) :
    ((nextI w (.ev s)).pend i).map Prod.fst = (w.pend i).map Prod.fst := by
  rw [nextIEv]
  show ((upd w.pend s.esAg (pendE w s.esAg s.esLb)) i).map Prod.fst = _
  by_cases hi : i = s.esAg
  · subst hi
    rw [updEq]
    obtain ⟨ag, lb⟩ := s
    cases lb with
    | LStore => simp [isSt] at hst
    | LFence pr pw sr sw =>
      show (if pw && sw then (w.pend ag).map (fun p => (p.1, p.2.bump)) else w.pend ag).map Prod.fst = _
      split <;> simp
    | LLoad => rfl
    | LRmw => rfl
    | LIo => rfl
  · rw [updNe _ _ _ _ hi]

theorem sbMsgEv (w : WS) (s : Estep) (hst : isSt s.esLb = false) (i : Nat) :
    ∀ e ∈ (nextI w (.ev s)).σ.sb i, ∃ e0 ∈ w.σ.sb i, e0.msg = e.msg := by
  intro e he
  rw [nextIEv] at he
  obtain ⟨ag, lb⟩ := s
  cases lb with
  | LStore => simp [isSt] at hst
  | LLoad => exact ⟨e, he, rfl⟩
  | LRmw => exact ⟨e, he, rfl⟩
  | LIo => exact ⟨e, he, rfl⟩
  | LFence pr pw sr sw =>
    change e ∈ (if pw && sw then SbCand.updSb _ ag ((w.σ.sb ag).map SbEnt.bump) else w.σ.sb) i at he
    split at he
    · by_cases hi : i = ag
      · subst hi
        rw [SbCand.updSbEq] at he
        obtain ⟨e0, he0, rfl⟩ := List.mem_map.1 he
        exact ⟨e0, he0, rfl⟩
      · rw [SbCand.updSbNe _ _ _ _ hi] at he; exact ⟨e, he, rfl⟩
    · exact ⟨e, he, rfl⟩

/-! # 4. The plain load -/

/-- **THE LOAD ITEM**: a non-exempt plain-load head of hart `cpu` (GF's label, the S-R gate) is MachCSL's plain
read at a view cut `tvn` (`SbRealPView.evLoadViewP` with `ViewCut`), `RmemR` kept. -/
theorem loadStepR {N : Nat} {X : Geid → Prop} {dev : List Geid} (img : Image) (G : Gexec) (hc : CatH G)
    (himg : G.gxImg = img) (hnd : G.gxGmo.Nodup) (c : CandW) (σ : MState) (ι : Nat → Nat)
    (hM : RmemR img G c σ ι) (hP : SbOrdR.PInvR N img G X dev (SbWalk.cur c)) (cpu : CPU)
    (aq : Bool) (base : Int) (ts : List Nat) (vs : List (BitVec 8))
    (hl : gxLbl G (hd (SbWalk.cur c) (hartAgent cpu)) = some (LLoad aq base ts vs))
    (hg : SbOrdR.srGate G (SbWalk.cur c) (hartAgent cpu) aq base ts vs)
    (pa : PAddr) (n : Nat) (hbase : base = paZ pa) (hram : ramBytes pa n) (hlen : ts.length = n)
    (wv : BitVec (8 * n)) (hb : ∀ j, j < n → vs[j]? = some (nthByte wv j)) :
    ∃ tvn, ViewCut img (SbWalk.cur c).σ σ cpu pa n wv tvn ∧
      RmemR img G (snocC c (.ev ⟨hartAgent cpu, LLoad aq base ts vs⟩)) (σ.afterLoad cpu pa n tvn) ι := by
  have hok := hM.mem.2.2.2.2.2.2.2.2
  have hnw := noWrapOfRam pa n hram
  let s : Estep := ⟨hartAgent cpu, LLoad aq base ts vs⟩
  have hcur := curSnoc c (.ev s)
  obtain ⟨T, hT, hcut, hcohT, hTw⟩ :=
    cutBytesOfRView G (SbWalk.cur c) σ cpu hP hc himg hnd hM.mem (hM.view cpu) aq base ts vs hl hg pa n hbase hnw
      hlen
  have himg' : (SbWalk.cur c).σ.ms.msImg = img := hM.mem.1
  have hvc := viewCutOf img (SbWalk.cur c).σ σ hM.mem cpu pa n wv T hT (fun j hj => by
    rw [paZAddJ pa n j hnw hj, ← himg', ← hbase]
    obtain ⟨t, htj⟩ : ∃ t, ts[j]? = some t := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    rcases hcut j t (nthByte wv j) hj htj (hb j hj) with h | ⟨h1, h2, h3, h4⟩
    · exact .inl h
    · exact .inr ⟨h1, t, h2, h3, h4⟩)
  have hltv := hvc.2.1
  have hlogE : (SbWalk.cur (snocC c (.ev s))).σ.ms.msLog = (SbWalk.cur c).σ.ms.msLog := by
    rw [hcur, nextIEv]; rfl
  refine ⟨_, hvc, ⟨?_, stampFrame c (.ev s) σ _ ι hM.stamp rfl rfl
    (fun cpu0 => by rw [hcur]; exact tagsEv _ s rfl _), fun cpu' => ?_⟩⟩
  · rw [hcur, nextIEv]
    exact rmemPLoadAt img _ σ cpu pa n _ aq base ts vs hM.mem hltv
  · by_cases hcc : cpu' = cpu
    · subst hcc
      exact rviewLoad G hc hnd _ _ σ cpu' hP hM.mem (hM.view cpu') aq base ts vs hl pa n hbase hram hlen T
        hcut hcohT hTw (by rw [hcur]; exact rowsEvSelf _ s) (by rw [hlogE]; exact List.prefix_refl _)
        (by rw [hcur]; exact sbMsgEv _ s rfl _)
    · have hne : hartAgent cpu' ≠ hartAgent cpu := fun h => hcc (SbRealP.hartAgentInj h)
      have hrw : (SbWalk.cur (snocC c (.ev s))).rows (hartAgent cpu') = (SbWalk.cur c).rows (hartAgent cpu') := by
        rw [hcur]; exact rowsEvNe _ s _ hne
      refine rviewFrame G _ _ σ _ cpu' (hM.view cpu') rfl ?_ rfl (Nat.le_of_eq (by rw [hrw]))
        (fun W a u _ h1 h2 => by rw [hrw] at h2; omega) (by rw [hlogE]; exact List.prefix_refl _)
        (by rw [hcur]; exact sbMsgEv _ s rfl _)
      show (if cpu' = cpu then _ else _) = _; rw [if_neg hcc]

/-! # 5. The fence -/

/-- **THE FENCE ITEM**: a barrier `b ≠ fence.tso` of hart `cpu` (its twin label GF's), with the twin's drain, is
MachCSL's barrier (the guard under M-S2's non-draining `fence.i`, `SbRealPHart.MS2FenceINoDrain`), `RmemR` kept. -/
theorem fenceStepR (img : Image) (G : Gexec) (hc : CatH G) (c : CandW) (σ : MState) (ι : Nat → Nat)
    (hM : RmemR img G c σ ι) (cpu : CPU) (b : LeanRV64D.barrier_kind) (pr pw sr sw : Bool)
    (htso : b ≠ .Barrier_RISCV_tso) (hl : ebarLabel b = .LFence pr pw sr sw)
    (hgl : gxLbl G (hd (SbWalk.cur c) (hartAgent cpu)) = some (LFence pr pw sr sw))
    (hms2 : SbRealPHart.MS2FenceINoDrain)
    (hdr : SbCand.drains pw sr = true → (SbWalk.cur c).σ.sb (hartAgent cpu) = []) :
    evStep cpu (.barrier b) σ () (σ.fence cpu b) ∧
      RmemR img G (snocC c (.ev ⟨hartAgent cpu, LFence pr pw sr sw⟩)) (σ.fence cpu b) ι := by
  let s : Estep := ⟨hartAgent cpu, LFence pr pw sr sw⟩
  have hcur := curSnoc c (.ev s)
  obtain ⟨hev, hR'⟩ := SbRealPHart.evFenceNdP img (SbWalk.cur c).σ σ cpu b pr pw sr sw hM.mem htso hl hms2 hdr
  have hlogE : (SbWalk.cur (snocC c (.ev s))).σ.ms.msLog = (SbWalk.cur c).σ.ms.msLog := by
    rw [hcur, nextIEv]; rfl
  refine ⟨hev, by rw [hcur, nextIEv]; exact hR', stampFrame c (.ev s) σ _ ι hM.stamp rfl rfl
    (fun cpu0 => by rw [hcur]; exact tagsEv _ s rfl _), fun cpu' => ?_⟩
  by_cases hcc : cpu' = cpu
  · subst hcc
    exact rviewFence G hc.wf _ _ σ cpu' b pr pw sr sw (hM.view cpu') hl hgl (by rw [hcur]; exact rowsEvSelf _ s)
      (by rw [hlogE]; exact List.prefix_refl _) (by rw [hcur]; exact sbMsgEv _ s rfl _)
  · have hne : hartAgent cpu' ≠ hartAgent cpu := fun h => hcc (SbRealP.hartAgentInj h)
    have hrw : (SbWalk.cur (snocC c (.ev s))).rows (hartAgent cpu') = (SbWalk.cur c).rows (hartAgent cpu') := by
      rw [hcur]; exact rowsEvNe _ s _ hne
    refine rviewFrame G _ _ σ _ cpu' (hM.view cpu') ?_ rfl rfl (Nat.le_of_eq (by rw [hrw]))
      (fun W a u _ h1 h2 => by rw [hrw] at h2; omega) (by rw [hlogE]; exact List.prefix_refl _)
      (by rw [hcur]; exact sbMsgEv _ s rfl _)
    show (if cpu' = cpu then _ else _) = _; rw [if_neg hcc]

/-! # 6. The exclusive pair -/

/-- **THE AMO ITEM**: an AMO head of hart `cpu` that is GF's next write (the S-R gate) is MachCSL's exclusive
read at the landed top then its write landing at once, `RmemR` kept (the new stamp maps to the item). -/
theorem exclStepR {N : Nat} {X : Geid → Prop} {dev : List Geid} (img : Image) (G : Gexec) (hc : CatH G)
    (hnd : G.gxGmo.Nodup) (c : CandW) (σ : MState) (ι : Nat → Nat) (hM : RmemR img G c σ ι)
    (hP : SbOrdR.PInvR N img G X dev (SbWalk.cur c)) (cpu : CPU) (pa : PAddr) (n : Nat) (r v : BitVec (8 * n))
    (aq rl : Bool) (ts : List Nat) (rvs wvs : List (BitVec 8)) (k : WmClass) (hram : ramBytes pa n)
    (hwl : wvs.length = n) (hb : ∀ j, j < n → wvs[j]? = some (nthByte v j))
    (htop : σ.mem.topBytesL σ.lp pa n r)
    (hgl : gxLbl G (hd (SbWalk.cur c) (hartAgent cpu)) = some (LRmw aq rl (paZ pa) ts rvs wvs k))
    (hnext : wrW (SbWalk.cur c) ++ [hd (SbWalk.cur c) (hartAgent cpu)] <+: gwrites G) :
    RmemR img G (snocC c (.ev ⟨hartAgent cpu, LRmw aq rl (paZ pa) ts rvs wvs k⟩))
      ((σ.afterExcl cpu pa n r aq).storeL cpu pa n v) (ιNew ι σ.top c.its.length) := by
  have hok := hM.mem.2.2.2.2.2.2.2.2
  have hnw := noWrapOfRam pa n hram
  let s : Estep := ⟨hartAgent cpu, LRmw aq rl (paZ pa) ts rvs wvs k⟩
  have hcur := curSnoc c (.ev s)
  have hlogP : (SbWalk.cur c).σ.ms.msLog <+: (SbWalk.cur (snocC c (.ev s))).σ.ms.msLog := by
    rw [hcur, nextIEv]; exact ⟨_, rfl⟩
  have hltop := ltopWrW hP hM.mem
  have hAw : hd (SbWalk.cur c) (hartAgent cpu) ∈ gwrites G := by
    obtain ⟨T, hT⟩ := hnext; rw [← hT]; simp
  have hAgw : gwix G (hd (SbWalk.cur c) (hartAgent cpu)) = σ.ltop + 1 := by
    rw [wixOfNext _ _ hnd hnext, hltop]
  have hpre : σ.ltop = 0 ∨ ∃ W0, W0 ∈ gwrites G ∧ gwix G W0 = σ.ltop ∧
      gmoLt G W0 (hd (SbWalk.cur c) (hartAgent cpu)) := by
    rcases Nat.eq_zero_or_pos σ.ltop with h0 | hpos
    · exact .inl h0
    · right
      obtain ⟨T, hT⟩ := hnext
      have hlt : σ.ltop - 1 < (wrW (SbWalk.cur c)).length := by omega
      obtain ⟨W0, hW0⟩ : ∃ W0, (wrW (SbWalk.cur c))[σ.ltop - 1]? = some W0 :=
        ⟨_, List.getElem?_eq_getElem hlt⟩
      have hg0 : (gwrites G)[σ.ltop - 1]? = some W0 := by
        rw [← hT, List.append_assoc, List.getElem?_append_left hlt]; exact hW0
      have hW0g : W0 ∈ gwrites G := List.mem_of_getElem? hg0
      have hgw0 : gwix G W0 = σ.ltop := by have := gwixOfLookup G _ W0 hnd hg0; omega
      refine ⟨W0, hW0g, hgw0, (List.mem_filter.1 hW0g).1, (List.mem_filter.1 hAw).1, ?_⟩
      exact (gwixGposLt G W0 _ hnd hW0g hAw).1 (by omega)
  refine ⟨?_, stampNew c (.ev s) σ _ ι hM.stamp rfl (by simp [MState.top]) hok
    (fun cpu0 => by rw [hcur]; exact tagsEv _ s rfl _), fun cpu' => ?_⟩
  · rw [hcur, nextIEv]
    exact rmemPRmw img _ σ cpu pa n r v aq rl ts rvs wvs k hram hwl hb htop hM.mem
  · by_cases hcc : cpu' = cpu
    · subst hcc
      refine rviewExcl G hc hnd _ _ σ (σ.afterExcl cpu' pa n r aq) cpu' pa n r v aq (hM.view cpu') hok _ hgl rfl rfl
        (fun h => by simp [lbAq, h]) hAw hAgw hpre rfl rfl rfl rfl (by rw [hcur]; exact rowsEvSelf _ s)
        (fun a u hwb => ?_) hlogP (by rw [hcur]; exact sbMsgEv _ s rfl _)
      obtain ⟨l, b0, vs0, j, hl0, hw0, hv0, ha0⟩ := hwb
      have hl1 : gxLbl G (hd (SbWalk.cur c) (hartAgent cpu')) = some l := hl0
      rw [hgl, Option.some.injEq] at hl1
      subst hl1
      simp only [lbWr, Option.some.injEq, Prod.mk.injEq] at hw0
      obtain ⟨rfl, rfl⟩ := hw0
      exact inFpOf pa n hnw a j (by rw [← hwl]; exact lookup_lt_Some hv0) ha0.symm
    · have hne : hartAgent cpu' ≠ hartAgent cpu := fun h => hcc (SbRealP.hartAgentInj h)
      have hrw : (SbWalk.cur (snocC c (.ev s))).rows (hartAgent cpu') = (SbWalk.cur c).rows (hartAgent cpu') := by
        rw [hcur]; exact rowsEvNe _ s _ hne
      refine rviewFrame G _ _ σ _ cpu' (hM.view cpu') ?_ ?_ ?_ (Nat.le_of_eq (by rw [hrw]))
        (fun W a u _ h1 h2 => by rw [hrw] at h2; omega) hlogP (by rw [hcur]; exact sbMsgEv _ s rfl _)
      · show (if cpu' = cpu then _ else _) = _
        rw [if_neg hcc]
        show (if cpu' = cpu then _ else _) = _
        rw [if_neg hcc]
      · show (if cpu' = cpu then _ else _) = _
        rw [if_neg hcc]
        show (if cpu' = cpu then _ else _) = _
        rw [if_neg hcc]
      · show ownPubL _ (σ.log ++ [hartAgent cpu]) (σ.llog ++ [σ.top + 1]) = _
        unfold ownPubL
        rw [landAuthorsSnoc]
        have hget : (σ.log ++ [hartAgent cpu]).getD (σ.top + 1 - 1) diskAgent = hartAgent cpu := by
          simp [MState.top]
        rw [hget, landAuthorsSnocLog σ.log σ.llog _ hok.2.2.2.2.1, ownPubSnocNe _ _ (Ne.symm hne)]

/-! # 7. MMIO and the memory-blind steps -/

/-- **A STEP THAT MOVES NO MEMORY SIDE** (a register read or write, the boundary's dropped reservation, a fetch, an
MMIO step: MachCSL's buffers, logs and read sides unchanged) keeps `RmemR`. -/
theorem rmemRSame (img : Image) (G : Gexec) (c : CandW) (σ σ' : MState) (ι : Nat → Nat) (hM : RmemR img G c σ ι)
    (hR' : rmemP img (SbWalk.cur c).σ σ') (hsb : σ'.sb = σ.sb) (hlog : σ'.log = σ.log) (hll : σ'.llog = σ.llog)
    (htv : σ'.tv = σ.tv) (hhr : σ'.hr = σ.hr) : RmemR img G c σ' ι := by
  have htop : σ'.top = σ.top := by show σ'.log.length = σ.log.length; rw [hlog]
  refine ⟨hR', ?_, fun cpu => ?_⟩
  · obtain ⟨hM1, hM2, hM3⟩ := hM.stamp
    exact ⟨fun cpu k s q hs hq => hM1 cpu k s q (by rw [← hsb]; exact hs) hq,
      fun s1 s2 h1 h2 h3 => hM2 s1 s2 h1 h2 (by rw [← htop]; exact h3),
      fun s0 h1 h2 => hM3 s0 h1 (by rw [← htop]; exact h2)⟩
  · have hV := hM.view cpu
    exact ⟨by rw [htv]; exact hV.tvD, by rw [hhr]; exact hV.rvD,
      by unfold ownPubL; rw [hlog, hll]; exact hV.pubD, fun a => by rw [hhr]; exact hV.cohD a,
      fun a h => by rw [hhr] at h ⊢; exact hV.cohSrc a h, fun a h => by rw [hhr]; exact hV.cohFwd a h,
      fun a h => by rw [hhr] at h ⊢; exact hV.cohOwn a h⟩

/-- **THE MMIO ITEM**: an I/O event of hart `cpu` is MachCSL's MMIO access (devices only), `RmemR` kept. -/
theorem ioStepR (img : Image) (G : Gexec) (hc : CatH G) (c : CandW) (σ : MState) (ι : Nat → Nat)
    (hM : RmemR img G c σ ι) (cpu : CPU) (kd : IoKind) (base : Int) (vs : List (BitVec 8)) (ds : DevStates)
    (hgl : gxLbl G (hd (SbWalk.cur c) (hartAgent cpu)) = some (LIo kd base vs)) :
    RmemR img G (snocC c (.ev ⟨hartAgent cpu, LIo kd base vs⟩)) { σ with devs := ds } ι := by
  let s : Estep := ⟨hartAgent cpu, LIo kd base vs⟩
  have hcur := curSnoc c (.ev s)
  have hlogE : (SbWalk.cur (snocC c (.ev s))).σ.ms.msLog = (SbWalk.cur c).σ.ms.msLog := by
    rw [hcur, nextIEv]; rfl
  have hrows' : ∀ y, (SbWalk.cur (snocC c (.ev s))).rows y =
      if y = hartAgent cpu then (SbWalk.cur c).rows (hartAgent cpu) ++ [LIo kd base vs]
      else (SbWalk.cur c).rows y := by
    intro y
    rw [hcur, nextIEv]
    show upd _ (hartAgent cpu) _ y = _
    by_cases hy : y = hartAgent cpu
    · subst hy; rw [updEq, if_pos rfl]
    · rw [updNe _ _ _ _ hy, if_neg hy]
  refine ⟨by rw [hcur, nextIEv]; exact rmemPIo img _ σ (hartAgent cpu) kd base vs ds hM.mem,
    stampFrame c (.ev s) σ _ ι hM.stamp rfl rfl (fun cpu0 => by rw [hcur]; exact tagsEv _ s rfl _), fun cpu' => ?_⟩
  have hrle : ((SbWalk.cur c).rows (hartAgent cpu')).length ≤
      ((SbWalk.cur (snocC c (.ev s))).rows (hartAgent cpu')).length := by
    rw [hrows']
    split
    · rename_i hy; rw [hy]; simp
    · exact Nat.le_refl _
  refine rviewFrame G _ _ σ _ cpu' (hM.view cpu') rfl rfl rfl hrle (fun W a u hx h1 h2 hwb => ?_)
    (by rw [hlogE]; exact List.prefix_refl _) (by rw [hcur]; exact sbMsgEv _ s rfl _)
  -- the only new event is the I/O one, not a write
  rw [hrows'] at h2
  split at h2
  · rename_i hy
    rw [hy] at h1 hx
    simp only [List.length_append, List.length_singleton] at h2
    have hW : W = hd (SbWalk.cur c) (hartAgent cpu) := Prod.ext hx (by unfold hd; omega)
    obtain ⟨l, b0, vs0, j, hl0, hw0, -, -⟩ := hwb
    rw [hW, hgl, Option.some.injEq] at hl0
    subst hl0; cases hw0
  · omega

/-! # 8. The DMA pair -/

/-- **THE DMA PAIR**: the disk agent's store issue followed by the landing of its only entry (the [OWN.151] device
unit) is MachCSL's DMA write landing at once, `RmemR` kept across the pair (the new stamp maps to the landing
item). -/
theorem dmaPairStepR {N : Nat} {X : Geid → Prop} {dev : List Geid} (img : Image) (G : Gexec) (c : CandW)
    (σ : MState) (ι : Nat → Nat) (hM : RmemR img G c σ ι) (hP : SbOrdR.PInvR N img G X dev (SbWalk.cur c))
    (pa : PAddr) (n : Nat) (v : BitVec (8 * n)) (wvs : List (BitVec 8)) (k : WmClass) (hram : ramBytes pa n)
    (hn0 : n ≠ 0) (hwl : wvs.length = n) (hb : ∀ j, j < n → wvs[j]? = some (nthByte v j)) :
    RmemR img G (snocC (snocC c (.ev ⟨NCPU, LStore false (paZ pa) wvs k⟩)) (.land NCPU 0)) (σ.storeDma pa n v)
      (ιNew ι σ.top (c.its.length + 1)) := by
  have hok := hM.mem.2.2.2.2.2.2.2.2
  let s : Estep := ⟨NCPU, LStore false (paZ pa) wvs k⟩
  let c1 := snocC c (.ev s)
  have hcur1 := curSnoc c (.ev s)
  have hcur2 := curSnoc c1 (.land NCPU 0)
  have hnil : (SbWalk.cur c).σ.sb NCPU = [] :=
    hM.mem.2.2.2.2.2.1 NCPU (fun cpu => Nat.ne_of_gt (hartAgent_lt cpu))
  have hpnil : (SbWalk.cur c).pend NCPU = [] := by
    have := hP.inv.sb NCPU
    rw [hnil] at this
    exact List.map_eq_nil_iff.1 this.symm
  -- the device's pending entry after the issue
  have hp1 : ((SbWalk.cur c1).pend NCPU)[0]? =
      some (((SbWalk.cur c).rows NCPU).length, SbCand.issueEnt (SbWalk.cur c).σ NCPU false (paZ pa) wvs k) := by
    rw [hcur1, nextIEv]
    show (upd (SbWalk.cur c).pend NCPU _ NCPU)[0]? = _
    rw [updEq]
    show ((SbWalk.cur c).pend NCPU ++ [_])[0]? = _
    rw [hpnil]; rfl
  have hcurE := hcur2.trans (landEq NCPU 0 _ hp1)
  have hσ : (SbWalk.cur (snocC c1 (.land NCPU 0))).σ =
      SbCand.nextL (SbCand.nextE (SbWalk.cur c).σ NCPU (LStore false (paZ pa) wvs k)) NCPU 0 := by
    rw [hcurE, hcur1, nextIEv]
  have hne : ∀ cpu : CPU, hartAgent cpu ≠ NCPU := fun cpu => Nat.ne_of_lt (hartAgent_lt cpu)
  have hrows : ∀ cpu : CPU, (SbWalk.cur (snocC c1 (.land NCPU 0))).rows (hartAgent cpu) =
      (SbWalk.cur c).rows (hartAgent cpu) := by
    intro cpu
    rw [hcurE]
    show (SbWalk.cur c1).rows (hartAgent cpu) = _
    rw [hcur1]; exact rowsEvNe _ s _ (hne cpu)
  have hpend : ∀ cpu : CPU, (SbWalk.cur (snocC c1 (.land NCPU 0))).pend (hartAgent cpu) =
      (SbWalk.cur c).pend (hartAgent cpu) := by
    intro cpu
    rw [hcurE]
    show upd (SbWalk.cur c1).pend NCPU _ (hartAgent cpu) = _
    rw [updNe _ _ _ _ (hne cpu), hcur1, nextIEv]
    exact updNe _ _ _ _ (hne cpu)
  obtain ⟨-, hlogF, hsbF⟩ := SbRealPDma.pairFields (SbWalk.cur c).σ (paZ pa) wvs k hnil
  have hlogP : (SbWalk.cur c).σ.ms.msLog <+: (SbWalk.cur (snocC c1 (.land NCPU 0))).σ.ms.msLog := by
    rw [hσ, hlogF]; exact ⟨_, rfl⟩
  have hsbE : (SbWalk.cur (snocC c1 (.land NCPU 0))).σ.sb = (SbWalk.cur c).σ.sb := by rw [hσ, hsbF]
  have hS1 : StampRel c1 σ ι :=
    stampFrame c (.ev s) σ σ ι hM.stamp rfl rfl (fun cpu => by
      rw [hcur1, nextIEv]; show ((upd (SbWalk.cur c).pend NCPU _ (hartAgent cpu))).map Prod.fst = _
      rw [updNe _ _ _ _ (hne cpu)])
  have hS2 : StampRel (snocC c1 (.land NCPU 0)) (σ.storeDma pa n v) (ιNew ι σ.top c1.its.length) :=
    stampNew c1 (.land NCPU 0) σ _ ι hS1 rfl (by simp [MState.storeDma, hn0, MState.top]) hok
      (fun cpu => by rw [hpend cpu, hcur1, nextIEv]; show _ = ((upd (SbWalk.cur c).pend NCPU _ (hartAgent cpu))).map Prod.fst
                     rw [updNe _ _ _ _ (hne cpu)])
  have hlen1 : c1.its.length = c.its.length + 1 := snocLen c _
  refine ⟨by rw [hσ]; exact SbRealPDma.rmemPDma img _ σ pa n v wvs k hram hn0 hwl hb hM.mem,
    by rw [← hlen1]; exact hS2, fun cpu => ?_⟩
  refine rviewFrame G _ _ σ _ cpu (hM.view cpu) rfl rfl ?_ (Nat.le_of_eq (by rw [hrows cpu]))
    (fun W a u _ h1 h2 => by rw [hrows cpu] at h2; omega) hlogP
    (fun e he => by rw [hsbE] at he; exact ⟨e, he, rfl⟩)
  show ownPubL _ (if n = 0 then σ.log else σ.log ++ [diskAgent]) (if n = 0 then σ.llog else σ.llog ++ [σ.top + 1]) = _
  rw [if_neg hn0, if_neg hn0]
  unfold ownPubL
  rw [landAuthorsSnoc]
  have hget : (σ.log ++ [diskAgent]).getD (σ.top + 1 - 1) diskAgent = diskAgent := by simp [MState.top]
  rw [hget, landAuthorsSnocLog σ.log σ.llog _ hok.2.2.2.2.1,
    ownPubSnocNe _ diskAgent (by unfold diskAgent; exact Ne.symm (hne cpu))]

/-! # 9. Boot -/

/-- **AT POWER-ON**: the empty walk and a booted machine are related by `RmemR`. -/
theorem bootR (G : Gexec) (hwf : gwf G) (σ : MState) (hb : bootFacts σ) :
    RmemR (imgZ bootImage) G ⟨imgZ bootImage, []⟩ σ (fun _ => 0) := by
  have hb' := hb
  obtain ⟨-, hlog, hcpu, -, -, hll, hsb⟩ := hb'
  have hinit : SbCand.initS (SbWalk.cur ⟨imgZ bootImage, []⟩).σ :=
    ⟨rfl, fun _ => rfl, fun _ => rfl⟩
  refine ⟨rmemPBoot _ σ hb hinit rfl, stampBoot _ σ (fun cpu => (hsb cpu).1) (by simp [MState.top, hlog]),
    fun cpu => rviewBoot G hwf _ σ cpu (hcpu cpu).1 (by rw [(hcpu cpu).2.2.1]; rfl)
      (fun a => by rw [(hcpu cpu).2.2.1]; rfl) hll⟩

#print axioms Weak.SbRealPSim.bootR
#print axioms Weak.SbRealPSim.dmaPairStepR
#print axioms Weak.SbRealPSim.exclStepR
#print axioms Weak.SbRealPSim.ioStepR
#print axioms Weak.SbRealPSim.loadStepR
#print axioms Weak.SbRealPSim.fenceStepR
#print axioms Weak.SbRealPSim.issueStepR
#print axioms Weak.SbRealPSim.landStepR

end SbRealPSim

end Weak
