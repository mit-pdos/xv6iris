/-
Weak: **spike S-P (route P, report-only) — landing the gated walk's stores in GF's CROSS-ADDRESS write
order** (`~/dev/weak-orch/weakmach/proposal-A5.md` §6 item S-P; `PROGRESS-SPSR.md`).  Lean-only, no
Rocq twin.  A leaf: nothing imports this file.

**Spec, stated first.**  riscv.cat orders two writes of a hart to different bytes only by rule 4 (a
fence with `w` predecessor and `w` successor bits), rule 5/6/7 (`.aq`/`.rl`) or rules 9–13; RVWMO's
global memory order (gmo) restricted to writes is a total order chosen by the execution.  The gated walk
(`SbOrd`) lands a buffered store when the landed list of every byte it writes ++ it is a prefix of GF's
co at that byte (`SbOrd.landG`); ACROSS bytes it lands freely.  S-P asks whether the walk can follow GF's
gmo on ALL writes (the member's landed write list a prefix of `gwrites GF`) without losing progress
(`SbOrd.noStuckP`), and whether the walk then realizes GF's gmo CUT (finding F-6h-1,
`parked/PROGRESS-w2-6h-1021.md`).

  §1  the member's landed write list `SpikeSP.wrW`, the strengthened gate `SpikeSP.enbX` (a landing —
      and an AMO head, whose write lands at its event — only as the NEXT GF write), `SpikeSP.enbXSub`
      (every S-P item is an old item: S-P walks are gated walks, so every per-state input discharged for
      gated walks covers them), the prefix invariant along an enabled item (`pfxWLand`, `pfxWEv`) and the
      LOG IS GF's WRITE PREFIX (`logOfWrW`).
  §2  **`SpikeSP.noStuckPX`** — PROGRESS under the strengthened gate with EXACTLY `noStuckP`'s
      hypotheses plus the prefix invariant: a blocked S-P landing / AMO head waits for the next unlanded
      GF write, which is strictly gmo-earlier (`nextW` + `SbOrd.tgtW`); no new named input.
  §3  GF's Litmus members are S-P members: `SpikeSP.l1MemberSP` (Litmus 1, `SBAcqP.ord1P`),
      `SpikeSP.l4xMemberSP` (the F-R45-1 companion, `SBAcqP.ord4X`).
  §4  **`SpikeSP.g0`** (2 harts: `ld a ← s ; sd b = m` ‖ `sd a = s`, gmo `m < s < ld a`):
      RVWMO-consistent (`g0Cat`), has a per-byte member (`g0MemberP`), has NO S-P member
      (`g0NoMemberSP`, any positions with program order, issue-before-landing and the top-read rule) —
      under S-P a po-later write gmo-before a read's foreign source DEADLOCKS, so the write half of row
      H3 (`SbHeadHop.WrHop`-type: the source gmo-before every later write of the row) becomes NECESSARY
      for progress, not just for its proof.
  §5  **F-6h-1 is NOT rescued by S-P**: `SpikeSP.cutPast` (generic — in any S-P member, if hart `i` has
      a write `m2` po-after event `e` and gmo-before `w′`, then `e`'s step precedes `w′`'s landing by
      `m2`'s issue: hart `i` is PAST its slot at every state where `w′` has landed) and the witness
      `SpikeSP.f6` (`uservec`-shaped: slot event, trapframe stores `gnxw` then `m2`, a foreign write `w′`
      to the fetched byte; gmo `m2 < w′ < gnxw`): RVWMO-consistent (`f6Cat`), `w′` inside the fetch's
      cut (`f6InCut`), so `fetchReplayOk`'s U-mode replay state with `w′` landed exists at NO S-P walk
      state (`f6Past`).
  §6  the REPAIRED order (S-K): the kill's relation `racy` contains `gpow` (po into a write), so a
      linear extension `K` of it never puts a row's later write before the row's earlier events.  GF
      re-linearized by `K` (same po / rf / co): `g0K` (consistent, `g0KCat`; an S-P member exists,
      `g0KMemberSP`) and `f6K` (consistent, `f6KCat`; `w′` still inside the cut, `f6KInCut`; an S-P
      member lands `w′` while hart `i` has stepped ONLY its slot event, `f6KHeld`).

Spec: FAITHFUL (proof organisation over riscv.cat rules 1, 4, 5, load value, atomicity, co ⊆ gmo; the
trusted residue as in `SbOrd`); theorems about the existing model; nothing assumed.  Lean-only helpers
`SpikeSP.*`.
-/
import Weak.SbOrdWalk
import Weak.LitmusSBAcqP
import Weak.GraphFetchSpike

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open Lbl

namespace SpikeSP

open SbWalk SbAgree SbReplay SbOrd

/-! # 1. The strengthened gate -/

/-- A walk event is a write (off the rows). -/
def rwW (rows : Nat → List Lbl) (e : Geid) : Bool :=
  match (rows e.1)[e.2]? with
  | some l => lbIsW l
  | none => false

/-- **THE MEMBER'S LANDED WRITES**, in landing order (all bytes). -/
def wrW (w : WS) : List Geid := w.gmo.filter (rwW w.rows)

/-- Row `x`'s next GF event is an AMO (its write lands at its event). -/
def amoHd (G : Gexec) (w : WS) (x : Nat) : Prop :=
  ∃ aq rl base ts rvs wvs kc, gxLbl G (hd w x) = some (LRmw aq rl base ts rvs wvs kc)

/-- **THE S-P LANDING GATE**: `SbOrd.landG`, and the store is the NEXT GF write (all bytes). -/
def landGX (pol : SbPol) (G : Gexec) (w : WS) (i k : Nat) : Prop :=
  landG pol G w i k ∧ ∃ p, (w.pend i)[k]? = some p ∧ wrW w ++ [(i, p.1)] <+: gwrites G

/-- **THE S-P GATE**: `SbOrd.enb`, an AMO head only as the next GF write, a landing by `landGX`. -/
def enbX (pol : SbPol) (G : Gexec) (X : Geid → Prop) (rdG : RdG) (dev : List Geid) (w : WS) :
    Tgt → Prop
  | .hd x => enb pol G X rdG dev w (.hd x) ∧ (amoHd G w x → wrW w ++ [hd w x] <+: gwrites G)
  | .ld i k => (SbOrd.devQuiet w ∨ NCPU ≤ i) ∧ landGX pol G w i k

/-- **EVERY S-P ITEM IS A GATED ITEM** (so S-P walks are gated walks). -/
theorem enbXSub (pol : SbPol) (G : Gexec) (X : Geid → Prop) (rdG : RdG) (dev : List Geid) (w : WS)
    (T : Tgt) : enbX pol G X rdG dev w T → enb pol G X rdG dev w T := by
  cases T with
  | hd x => exact fun h => h.1
  | ld i k => exact fun h => ⟨h.1, h.2.1⟩

/-- A landed write in the old sense (some byte) is a landed write. -/
theorem wrAtWrW (w : WS) (a : Int) (n : Geid) : n ∈ wrAtW w a → n ∈ wrW w := by
  intro h
  obtain ⟨hm, hb⟩ := List.mem_filter.1 h
  refine List.mem_filter.2 ⟨hm, ?_⟩
  unfold rwrB at hb; unfold rwW
  cases hl : (w.rows n.1)[n.2]? with
  | none => rw [hl] at hb; cases hb
  | some l => rw [hl] at hb; exact wrsBOfWr l a hb

/-- The label shapes of `gwf` at an event. -/
theorem lblShape (G : Gexec) (hwf : gwf G) (e : Geid) (l : Lbl) : gxLbl G e = some l →
    match l with
    | LLoad _ _ ts vs => vs.length = ts.length
    | LStore _ _ vs _ => vs ≠ []
    | LFence _ _ _ _ => True
    | LRmw _ _ _ ts rvs wvs _ => wvs ≠ [] ∧ wvs.length = ts.length ∧ rvs.length = ts.length
    | LIo .. => True := by
  intro hl
  unfold gxLbl at hl
  cases hr : G.gxProg[e.1]? with
  | none => rw [hr] at hl; cases hl
  | some row =>
    rw [hr] at hl
    simp only [Option.bind_some] at hl
    exact hwf.2.2 e.1 row e.2 l hr hl

/-- A GF write writes some byte. -/
theorem gwrOfW (G : Gexec) (hwf : gwf G) (n : Geid) : n ∈ gwrites G → ∃ a, gwrB G a n = true := by
  intro hn
  obtain ⟨-, hw⟩ := (gwritesElemOf G n).1 hn
  unfold gisW at hw
  cases hl : gxLbl G n with
  | none => rw [hl] at hw; cases hw
  | some l =>
    rw [hl] at hw
    have hs := lblShape G hwf n l hl
    have hwr : ∀ base (vs : List (BitVec 8)), lbWr l = some (base, vs) → vs ≠ [] →
        gwrB G (accAddr base 0) n = true := by
      intro base vs hlw hne
      obtain ⟨v, vs', rfl⟩ : ∃ v vs', vs = v :: vs' := by
        cases vs with
        | nil => exact absurd rfl hne
        | cons v vs' => exact ⟨v, vs', rfl⟩
      unfold gwrB; rw [hl]
      exact (wrsBIff l _).2 ⟨base, v :: vs', 0, v, hlw, rfl, rfl⟩
    cases l with
    | LStore rl base vs kc => exact ⟨_, hwr base vs rfl hs⟩
    | LRmw aq rl base ts rvs wvs kc => exact ⟨_, hwr base wvs rfl hs.1⟩
    | LLoad _ _ _ _ => simp [lbIsW] at hw
    | LFence _ _ _ _ => simp [lbIsW] at hw
    | LIo _ _ _ => simp [lbIsW] at hw

/-- **THE NEXT UNLANDED GF WRITE**: if the landed write list is a GF prefix and `s` cannot land next,
the GF write after the prefix is unlanded and strictly gmo-before `s`. -/
theorem nextW (G : Gexec) (w : WS) (s : Geid) : wrW w <+: gwrites G → G.gxGmo.Nodup →
    s ∈ gwrites G → s ∉ wrW w → ¬ (wrW w ++ [s] <+: gwrites G) →
    ∃ n, n ∈ gwrites G ∧ n ∉ wrW w ∧ gpos G n < gpos G s := by
  rintro ⟨T, hT⟩ hnd hs hsW hno
  cases T with
  | nil => rw [List.append_nil] at hT; rw [← hT] at hs; exact absurd hs hsW
  | cons n T' =>
    have hnG : n ∈ gwrites G := by rw [← hT]; simp
    have hnd' : (wrW w ++ n :: T').Nodup := by rw [hT]; exact gwritesNodup G hnd
    have hnW : n ∉ wrW w := fun h => (List.nodup_append.1 hnd').2.2 n h n (by simp) rfl
    by_cases hns : n = s
    · subst hns; exact absurd ⟨T', by rw [← hT, List.append_assoc]; rfl⟩ hno
    · refine ⟨n, hnG, hnW, (gwixGposLt G n s hnd hnG hs).1 ?_⟩
      rw [gwixPosOf G n hnd hnG, gwixPosOf G s hnd hs, ← hT, posOfAppNot _ _ n hnW,
        posOfAppNot _ _ s hsW]
      have : posOf (n :: T') n = 0 := by simp [posOf]
      have : posOf (n :: T') s = posOf T' s + 1 := by simp only [posOf, if_neg hns]
      omega

/-! ## 1.1 The prefix invariant along an enabled item -/

/-- An S-P landing keeps the landed write list a GF prefix. -/
theorem pfxWLand (img : Image) (G : Gexec) (w : WS) (i k : Nat) (p : Nat × SbEnt) :
    Inv img w → (w.pend i)[k]? = some p → wrW w ++ [(i, p.1)] <+: gwrites G →
    wrW (nextI w (.land i k)) <+: gwrites G := by
  intro hI hp hg
  obtain ⟨rl, base, vs, kc, hrow, -⟩ := hI.pendSt i p (List.mem_of_getElem? hp)
  rw [SbOrd.landEq i k p hp]
  show (w.gmo ++ [(i, p.1)]).filter (rwW w.rows) <+: _
  rw [List.filter_append]
  have : rwW w.rows (i, p.1) = true := by unfold rwW; rw [hrow]; rfl
  simp only [List.filter_cons, this, if_true, List.filter_nil]
  exact hg

/-- An S-P event keeps the landed write list a GF prefix (an AMO is the next GF write; any other event
lands nothing). -/
theorem pfxWEv (img : Image) (G : Gexec) (w : WS) (s : Estep) : Inv img w →
    wrW w <+: gwrites G →
    ((gmoEv s.esLb && lbIsW s.esLb) = true → wrW w ++ [(s.esAg, (w.rows s.esAg).length)] <+: gwrites G) →
    wrW (nextI w (.ev s)) <+: gwrites G := by
  intro hI h0 h1
  have hcong : ∀ e, e ∈ w.gmo → rwW (nextI w (.ev s)).rows e = rwW w.rows e := by
    intro e he
    obtain ⟨l, hl, -⟩ := hI.gmoMem e he
    unfold rwW
    rw [hl, rowsEvOld w s e.1 e.2 l hl]
  have hold : w.gmo.filter (rwW (nextI w (.ev s)).rows) = wrW w := List.filter_congr hcong
  have hnew : rwW (nextI w (.ev s)).rows (s.esAg, (w.rows s.esAg).length) = lbIsW s.esLb := by
    unfold rwW
    show (match (upd w.rows s.esAg (w.rows s.esAg ++ [s.esLb]) s.esAg)[(w.rows s.esAg).length]? with
      | some l => lbIsW l
      | none => false) = _
    rw [updEq]; simp
  unfold wrW
  change (if gmoEv s.esLb then w.gmo ++ [(s.esAg, (w.rows s.esAg).length)] else w.gmo).filter _ <+: _
  by_cases hg : gmoEv s.esLb = true
  · rw [if_pos hg, List.filter_append, hold]
    by_cases hw : lbIsW s.esLb = true
    · rw [List.filter_cons, hnew, if_pos hw]; exact h1 (by simp [hg, hw])
    · rw [List.filter_cons, hnew, if_neg hw]; simpa using h0
  · rw [if_neg hg, hold]; exact h0

/-- **THE LOG IS THE MEMBER'S LANDED WRITE LIST'S MESSAGES** — with `wrW w <+: gwrites GF`, the member's
log at every S-P state is the messages of a PREFIX of GF's gmo|W (GF's write cut). -/
theorem logOfWrW (img : Image) (w : WS) : Inv img w →
    w.σ.ms.msLog = (wrW w).filterMap (wmsgOf w.rows) := by
  intro hI
  rw [hI.log]
  unfold wrW
  have hnone : ∀ e, rwW w.rows e = false → wmsgOf w.rows e = none := by
    intro e he
    unfold rwW at he; unfold wmsgOf
    cases hl : (w.rows e.1)[e.2]? with
    | none => rfl
    | some l => rw [hl] at he; cases l <;> simp_all [lbIsW, lbWr]
  have key : ∀ l : List Geid, l.filterMap (wmsgOf w.rows) =
      (l.filter (rwW w.rows)).filterMap (wmsgOf w.rows) := by
    intro l
    induction l with
    | nil => rfl
    | cons e l ih =>
      by_cases he : rwW w.rows e = true
      · simp only [List.filter_cons, he, if_true, List.filterMap_cons, ih]
      · have he' : rwW w.rows e = false := by simpa using he
        simp only [List.filter_cons, he', Bool.false_eq_true, if_false, List.filterMap_cons,
          hnone e he', ih]
  exact key w.gmo

/-! # 2. Progress under the S-P gate -/

/-- **`noStuckPX` — PROGRESS UNDER THE S-P GATE**: `SbOrd.noStuckP`'s hypotheses (rows H1–H5, the named
H3 `HeadOrdRd`, `DevStOrd`, the trusted residue) and the S-P prefix invariant give an ENABLED genuine
S-P item at every non-final walk state.  No new named input: a blocked S-P landing or AMO head waits for
the next unlanded GF write, which is strictly gmo-earlier.  [OWN.151] integration (2026-10-22): stated at
DEVICE-QUIET states (`hq`; the spike's S-P gate does not carry the device unit — the S-R walk
`SbOrdR.noStuckR` does) and with `DevStFab` for `SbOrd.blkHead`. -/
theorem noStuckPX (GF : Gfexec) (N : Nat) (img : Image) (X : Geid → Prop) (rdG : RdG) (w : WS)
    (hc : CatH GF.gfGd.gdG) (hio : ioResidueGmo GF) (hwio : gfDevWIo GF) (hI : ImgFacts GF.gfGd.gdG)
    (hN : GF.gfGd.gdG.gxProg.length = N) (hP : PInv N img GF.gfGd.gdG X GF.gfDev w)
    (hmono : ∀ x aq base ts vs, gxLbl GF.gfGd.gdG (hd w x) = some (LLoad aq base ts vs) →
      srcGate GF.gfGd.gdG w x base ts vs → rdG w x base ts vs)
    (hDS : DevStOrd GF.gfGd.gdG GF.gfDev) (hDF : DevStFab GF.gfGd.gdG GF.gfDev)
    (hHart : ∀ e, e ∈ GF.gfDev → e.1 < NCPU → gisIo GF.gfGd.gdG e = true)
    (hR : HeadOrdRd GF.gfGd.gdG X rdG GF.gfDev w)
    (hW : wrW w <+: gwrites GF.gfGd.gdG) (hq : SbOrd.devQuiet w) :
    ((∃ x, x < N ∧ (w.rows x).length < (GF.gfGd.gdG.gxProg.getD x []).length) ∨ (∃ i, w.pend i ≠ [])) →
    ∃ T, validT N GF.gfGd.gdG w T ∧ enbX SbPol.epoch GF.gfGd.gdG X rdG GF.gfDev w T := by
  intro hne
  obtain ⟨A0, hA0⟩ := validOfNonFinal hP hne
  have hwio' : ∀ d, d ∈ GF.gfDev → gmem GF.gfGd.gdG d :=
    fun d hd => WeakRvwmoLin2.wioGmem _ d (hwio d hd)
  have hr1 : ∀ s m, WeakRvwmoGraph.gpo GF.gfGd.gdG s m → gmem GF.gfGd.gdG s →
      gisIo GF.gfGd.gdG s = false → gisIo GF.gfGd.gdG m = true → gmoLt GF.gfGd.gdG s m :=
    fun s m hpo hgm hn hi => hio s m (.inl ⟨hpo, hgm, hn, hi⟩)
  have hr2 : ∀ s m, WeakRvwmoGraph.gpo GF.gfGd.gdG s m → gisIo GF.gfGd.gdG s = true →
      gisW GF.gfGd.gdG m = true → gmoLt GF.gfGd.gdG s m :=
    fun s m hpo hi hw => hio s m (.inr (.inl ⟨hpo, hi, hw⟩))
  have hr2'' : ∀ s m, WeakRvwmoGraph.gpo GF.gfGd.gdG s m → gisIo GF.gfGd.gdG s = true →
      gisR GF.gfGd.gdG m = true → gmoLt GF.gfGd.gdG s m :=
    fun s m hpo hi hr => hio s m (.inr (.inr (.inr (.inr (.inr ⟨hpo, hi, hr⟩)))))
  have hr3a : ∀ s m, gisIo GF.gfGd.gdG s = true → gisIo GF.gfGd.gdG m = true →
      WeakRvwmoGraph.gpo GF.gfGd.gdG s m → gmoLt GF.gfGd.gdG s m :=
    fun s m hi hj hpo => hio s m (.inr (.inr (.inr (.inl ⟨hi, hj, hpo⟩))))
  have hr3 : ∀ d e, gmem GF.gfGd.gdG d → gmem GF.gfGd.gdG e → before GF.gfDev d e →
      gmoLt GF.gfGd.gdG d e :=
    fun d e hd he hb => hio d e (.inr (.inr (.inr (.inr (.inl ⟨hd, he, hb⟩)))))
  -- a write `s` that cannot land next waits for a genuine item gmo-before it
  have hnext : ∀ s, s ∈ gwrites GF.gfGd.gdG → s ∉ wrW w → ¬ (wrW w ++ [s] <+: gwrites GF.gfGd.gdG) →
      ∃ B, validT N GF.gfGd.gdG w B ∧ mu GF.gfGd.gdG GF.gfDev w B < gpos GF.gfGd.gdG s := by
    intro s hs hsW hno
    obtain ⟨n, hnG, hnW, hlt⟩ := nextW _ w s hW hc.wf.1 hs hsW hno
    obtain ⟨a, ha⟩ := gwrOfW _ hc.wf n hnG
    exact tgtW hP hc.wf hN a n _ ha ((gwritesElemOf _ n).1 hnG).1
      (fun h => hnW (wrAtWrW w a n h)) hlt
  refine SbOrd.descent (validT N GF.gfGd.gdG w) (enbX SbPol.epoch GF.gfGd.gdG X rdG GF.gfDev w)
    (mu GF.gfGd.gdG GF.gfDev w) (fun A hv hb => ?_) A0 hA0
  cases A with
  | hd x =>
    by_cases he : enb SbPol.epoch GF.gfGd.gdG X rdG GF.gfDev w (.hd x)
    · -- the AMO head is not the next GF write
      have hno : amoHd GF.gfGd.gdG w x ∧ ¬ (wrW w ++ [hd w x] <+: gwrites GF.gfGd.gdG) :=
        Classical.byContradiction (fun h => hb ⟨he, fun ha => Classical.byContradiction
          (fun h' => h ⟨ha, h'⟩)⟩)
      obtain ⟨⟨aq, rl, base, ts, rvs, wvs, kc, hl⟩, hno⟩ := hno
      have hem : hd w x ∈ GF.gfGd.gdG.gxGmo := lblGmo _ _ _ hc.wf hl rfl
      have hs : hd w x ∈ gwrites GF.gfGd.gdG :=
        (gwritesElemOf _ _).2 ⟨hem, by unfold gisW; rw [hl]; rfl⟩
      have hsW : hd w x ∉ wrW w := by
        intro h
        obtain ⟨l, hl', -⟩ := hP.inv.gmoMem _ (List.mem_filter.1 h).1
        unfold hd at hl'; simp at hl'
      obtain ⟨B, hB, hlt⟩ := hnext _ hs hsW hno
      have haq := hI.amoAq _ aq rl base ts rvs wvs kc hl
      subst haq
      refine ⟨B, hB, .inr (headBound hc.wf x _ _ hl rfl
        (fun m h1 h2 h3 _ => aqOrd hc x _ hl rfl m h1 h2 h3) hlt)⟩
    · obtain ⟨B, hB, hlt⟩ := blkHead SbPol.epoch hP hc hI hN rdG hwio' hwio hr1 hr2 hr2'' hr3a hr3 hR
        hDS hDF hHart x (hmono x) hv hq he
      exact ⟨B, hB, .inr hlt⟩
  | ld i k =>
    obtain ⟨-, p, hp⟩ := hv
    by_cases hl : landG SbPol.epoch GF.gfGd.gdG w i k
    · have hno : ¬ (wrW w ++ [(i, p.1)] <+: gwrites GF.gfGd.gdG) :=
        fun h => hb ⟨.inl hq, hl, p, hp, h⟩
      have hpm := List.mem_of_getElem? hp
      obtain ⟨rl, base, vs, kc, hlb, -, -⟩ := pendLbl hP i p hpm
      have hs : (i, p.1) ∈ gwrites GF.gfGd.gdG :=
        (gwritesElemOf _ _).2 ⟨lblGmo _ _ _ hc.wf hlb rfl, by unfold gisW; rw [hlb]; rfl⟩
      have hsW : (i, p.1) ∉ wrW w := fun h => hP.inv.pendGmo i p hpm (List.mem_filter.1 h).1
      obtain ⟨B, hB, hlt⟩ := hnext _ hs hsW hno
      exact ⟨B, hB, .inr (by rw [muLd _ _ w i k p hp]; exact hlt)⟩
    · obtain ⟨B, hB, hlt⟩ := blkLand hP hc hN i k p hp hl
      exact ⟨B, hB, .inr (by rw [muLd _ _ w i k p hp]; exact hlt)⟩

/-! # 3. GF's Litmus members follow GF's write order -/

/-- **THE S-P CONDITION on issue/landing positions**: every pair of writes lands in GF's gmo order
(across bytes). -/
def CoGmoW (G : Gexec) (p q : Geid → Nat) : Prop :=
  ∀ w1 w2, glblIs G w1 lbIsW → glblIs G w2 lbIsW → gmoLt G w1 w2 →
    SBAcqP.lpos G p q w1 < SBAcqP.lpos G p q w2

def coGmoWB (G : Gexec) (p q : Geid → Nat) : Bool :=
  SBAcqP.all2B G (fun w1 w2 => !(glblB G w1 lbIsW && glblB G w2 lbIsW && gmoLtB G w1 w2) ||
    decide (SBAcqP.lpos G p q w1 < SBAcqP.lpos G p q w2))

theorem coGmoWBSound (G : Gexec) (p q : Geid → Nat) : coGmoWB G p q = true → CoGmoW G p q := by
  intro hb w1 w2 h1 h2 hlt
  have h := SBAcqP.all2Sound G _ hb w1 w2 (SBAcqP.lblEv G w1 _ h1) (SBAcqP.lblEv G w2 _ h2)
  rw [(glblBSpec _ _ _).2 h1, (glblBSpec _ _ _).2 h2, (gmoLtBSpec _ _ _).2 hlt] at h
  simpa using h

/-- **LITMUS 1's route-P member is an S-P member** (the AMOs land at their events in GF's order, the
two releases last, `w′` before `w″`). -/
theorem l1MemberSP : CoGmoW SBAcq.l1.gdG (SBAcqP.pOf SBAcqP.ord1P) (SBAcqP.qOf SBAcqP.ord1P) :=
  coGmoWBSound _ _ _ (by decide +kernel)

/-- **The F-R45-1 companion's member is an S-P member.** -/
theorem l4xMemberSP : CoGmoW SBAcqP.l4x.gdG (SBAcqP.pOf SBAcqP.ord4X) (SBAcqP.qOf SBAcqP.ord4X) :=
  coGmoWBSound _ _ _ (by decide +kernel)

/-! # 4. `g0`: a po-later write gmo-before a read's foreign source

Row 0: `ld a` (byte 0) reading `s` (write #2), then `sd b` (byte 1) `= m` (write #1); row 1: `sd a = s`.
gmo `m < s < ld a`: `m` overtakes the load (no ppo from a load to a store of another byte without a
fence or a dependency) and lands before the load's source. -/

def g0Prog : List (List Lbl) :=
  [[LLoad false 0 [2] [b1], LStore false 1 [b1] .WCplain],
   [LStore false 0 [b1] .WCplain]]

def g0Gmo : List Geid := [(0, 1), (1, 0), (0, 0)]

def g0 : Gdexec := AxLitmus.mkgd g0Prog g0Gmo []

/-- **`g0` IS RVWMO-CONSISTENT** (the faithful cat model). -/
theorem g0Cat : rvwmoCatConsistent g0 := catConsistentBSound _ (by decide +kernel)

/-- The source of `ld a` is `s`, `m` is write #1. -/
theorem g0Rf : gwriteAt g0.gdG 2 = some (1, 0) ∧ gwriteAt g0.gdG 1 = some (0, 1) := by decide +kernel

def g0Ord : List SBAcqP.Item :=
  [(false, (1, 0)), (true, (1, 0)), (false, (0, 0)), (false, (0, 1)), (true, (0, 1))]

/-- **`g0` HAS A ROUTE-P MEMBER** (per-byte landing order: `s` lands first). -/
theorem g0MemberP :
    SBAcqP.OrdOk g0.gdG g0Ord ∧
    SBAcqP.FifoCore g0.gdG (SBAcqP.pOf g0Ord) (SBAcqP.qOf g0Ord) ∧
    SBAcqP.ReadsGF g0.gdG (SBAcqP.pOf g0Ord) (SBAcqP.qOf g0Ord) ∧
    SBAcqP.CoGF g0.gdG (SBAcqP.pOf g0Ord) (SBAcqP.qOf g0Ord) ∧
    SBAcqP.GateWr g0.gdG (SBAcqP.pOf g0Ord) (SBAcqP.qOf g0Ord) :=
  ⟨by unfold SBAcqP.OrdOk; decide +kernel, SBAcqP.memberPBSound _ _ _ (by decide +kernel)⟩

/-- **`g0` HAS NO S-P MEMBER**: for any positions with program order, issue before landing, the read
rule (`ReadsGF`: the source landed before the read, no promises) and GF's write order,
`q s < p (ld a) < p m < q m < q s`. -/
theorem g0NoMemberSP (p q : Geid → Nat)
    (hpo : ∀ e1 e2, WeakRvwmoGraph.gpo g0.gdG e1 e2 → p e1 < p e2)
    (hiss : ∀ w, glblIs g0.gdG w SBAcq.isSt → p w < q w)
    (hr : SBAcqP.ReadsGF g0.gdG p q) (hw : CoGmoW g0.gdG p q) : False := by
  have hls : SBAcqP.lpos g0.gdG p q (1, 0) = q (1, 0) := by
    unfold SBAcqP.lpos; exact if_pos (by decide +kernel)
  have hlm : SBAcqP.lpos g0.gdG p q (0, 1) = q (0, 1) := by
    unfold SBAcqP.lpos; exact if_pos (by decide +kernel)
  have a1 : q (1, 0) < p (0, 0) := by
    rcases hr.1 (0, 0) 0 2 b1 (1, 0) ((grbBSpec _ _ _ _ _).1 (by decide +kernel)) g0Rf.1 with
      ⟨hg, -⟩ | ⟨hl, -⟩
    · exact absurd hg.1 (by decide)
    · rw [hls] at hl; exact hl
  have a2 := hpo (0, 0) (0, 1) ((gpoBSpec _ _ _).1 (by decide +kernel))
  have a3 := hiss (0, 1) ((glblBSpec _ _ _).1 (by decide +kernel))
  have a4 := hw (0, 1) (1, 0) ((glblBSpec _ _ _).1 (by decide +kernel))
    ((glblBSpec _ _ _).1 (by decide +kernel)) ((gmoLtBSpec _ _ _).1 (by decide +kernel))
  rw [hls, hlm] at a4
  omega

/-! # 5. F-6h-1: hart `i` is past its slot whenever `w′` has landed -/

/-- **GENERIC**: in any S-P member (program order; a plain store issues before it lands, an AMO lands
at its step — `lpos ≥ p`), an event `e` of a row that has a write `m2` po-after `e` and gmo-before a
write `w′` steps before `w′` lands — `p e < p m2 ≤ lpos m2 < lpos w′`. -/
theorem cutPast (G : Gexec) (p q : Geid → Nat)
    (hpo : ∀ e1 e2, WeakRvwmoGraph.gpo G e1 e2 → p e1 < p e2)
    (hiss : ∀ w, glblIs G w SBAcq.isSt → p w < q w) (hw : CoGmoW G p q)
    (e m2 w' : Geid) (hm2 : glblIs G m2 lbIsW) (hw' : glblIs G w' lbIsW)
    (hpe : WeakRvwmoGraph.gpo G e m2) (hlt : gmoLt G m2 w') :
    p m2 < SBAcqP.lpos G p q w' ∧ p e < SBAcqP.lpos G p q w' := by
  have h1 := hpo e m2 hpe
  have h2 := hw m2 w' hm2 hw' hlt
  have h3 : p m2 ≤ SBAcqP.lpos G p q m2 := by
    unfold SBAcqP.lpos
    split
    · exact Nat.le_of_lt (hiss m2 ((glblBSpec _ _ _).1 (by assumption)))
    · exact Nat.le_refl _
  omega

/-- The `uservec`-shaped witness.  Row 0 (hart `i`): the slot-`k` event `e` (a user load of byte 4),
then the trap entry's trapframe stores `gnxw` (`sd ra`, byte 1) and `m2` (`sd sp`, byte 2), no fence
between; row 1: a foreign write `w′` to the fetched user-text byte 7 (no graph read of it: the fetch is
not a graph event, Stage C).  gmo `e < m2 < w′ < gnxw`. -/
def f6Prog : List (List Lbl) :=
  [[LLoad false 4 [0] [b0], LStore false 1 [b1] .WCplain, LStore false 2 [b1] .WCplain],
   [LStore false 7 [b1] .WCplain]]

def f6Gmo : List Geid := [(0, 0), (0, 2), (1, 0), (0, 1)]

def f6 : Gdexec := AxLitmus.mkgd f6Prog f6Gmo []

/-- **THE WITNESS IS RVWMO-CONSISTENT** (two stores of a hart to different bytes, no fence: unordered). -/
theorem f6Cat : rvwmoCatConsistent f6 := catConsistentBSound _ (by decide +kernel)

/-- `w′` is INSIDE the fetch's cut (`gwix w′ = 2 ≤ gfcut = gwix gnxw − 1 = 2`), and `m2` is gmo-before
it: exactly `fetchReplayOk`'s early half (a fetched byte written co-after the source — the image,
`t = 0` — at or below the cut). -/
theorem f6InCut : gnxw f6.gdG (0, 0) = some (0, 1) ∧ gwix f6.gdG (1, 0) = 2 ∧
    gfcut f6.gdG 0 0 = 2 ∧ gmoLt f6.gdG (0, 2) (1, 0) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, (gmoLtBSpec _ _ _).1 (by decide +kernel)⟩

/-- **NO S-P WALK STATE HAS HART `i` AT ITS SLOT WITH `w′` LANDED**: in every S-P member, hart `i`
has issued the trap entry's second trapframe store (`m2`, S-mode) before `w′` lands. -/
theorem f6Past (p q : Geid → Nat)
    (hpo : ∀ e1 e2, WeakRvwmoGraph.gpo f6.gdG e1 e2 → p e1 < p e2)
    (hiss : ∀ w, glblIs f6.gdG w SBAcq.isSt → p w < q w) (hw : CoGmoW f6.gdG p q) :
    p (0, 2) < q (1, 0) ∧ p (0, 1) < q (1, 0) := by
  have hl : SBAcqP.lpos f6.gdG p q (1, 0) = q (1, 0) := by
    unfold SBAcqP.lpos; exact if_pos (by decide +kernel)
  obtain ⟨h1, -⟩ := cutPast f6.gdG p q hpo hiss hw (0, 0) (0, 2) (1, 0)
    ((glblBSpec _ _ _).1 (by decide +kernel)) ((glblBSpec _ _ _).1 (by decide +kernel))
    ((gpoBSpec _ _ _).1 (by decide +kernel)) f6InCut.2.2.2
  have h2 := hpo (0, 1) (0, 2) ((gpoBSpec _ _ _).1 (by decide +kernel))
  rw [hl] at h1
  omega

/-! # 6. The repaired order: the kill's linearization (`racyD` includes po-into-write)

`g0` and `f6` fail S-P because GF's gmo may put a po-LATER write before an earlier event's
dependency (`m < s` in `g0`, `m2 < w′ < gnxw` in `f6`).  The kill's relation `racy`
(`WeakRvwmoAcyc.racy`: `gpow ∪ rf ∪ co ∪ fr ∪ ppo`) contains `gpow` (po INTO a write), so any linear
extension `K` of it keeps every row's writes after the row's earlier memory events.  Re-linearizing GF
by such a `K` (same po / rf / co, gmo := `K`) gives a consistent graph the walk can follow exactly. -/

/-- `g0` re-linearized by a linear extension of `racy`: `s < ld a < m` (the load re-timed to `s`'s new
write index 1). -/
def g0KProg : List (List Lbl) :=
  [[LLoad false 0 [1] [b1], LStore false 1 [b1] .WCplain],
   [LStore false 0 [b1] .WCplain]]

def g0KGmo : List Geid := [(1, 0), (0, 0), (0, 1)]

def g0K : Gdexec := AxLitmus.mkgd g0KProg g0KGmo []

theorem g0KCat : rvwmoCatConsistent g0K := catConsistentBSound _ (by decide +kernel)

def g0KOrd : List SBAcqP.Item :=
  [(false, (1, 0)), (true, (1, 0)), (false, (0, 0)), (false, (0, 1)), (true, (0, 1))]

/-- **`g0K` HAS AN S-P MEMBER** (its own gmo order on writes). -/
theorem g0KMemberSP :
    SBAcqP.FifoCore g0K.gdG (SBAcqP.pOf g0KOrd) (SBAcqP.qOf g0KOrd) ∧
    SBAcqP.ReadsGF g0K.gdG (SBAcqP.pOf g0KOrd) (SBAcqP.qOf g0KOrd) ∧
    CoGmoW g0K.gdG (SBAcqP.pOf g0KOrd) (SBAcqP.qOf g0KOrd) :=
  let h := SBAcqP.memberPBSound g0K.gdG (SBAcqP.pOf g0KOrd) (SBAcqP.qOf g0KOrd) (by decide +kernel)
  ⟨h.1, h.2.1, coGmoWBSound _ _ _ (by decide +kernel)⟩

/-- `f6` re-linearized by a linear extension of `racy` that puts `w′` first: `e < w′ < gnxw < m2`
(`gpow` forces `gnxw < m2`). -/
def f6KGmo : List Geid := [(0, 0), (1, 0), (0, 1), (0, 2)]

def f6K : Gdexec := AxLitmus.mkgd f6Prog f6KGmo []

theorem f6KCat : rvwmoCatConsistent f6K := catConsistentBSound _ (by decide +kernel)

/-- In `f6K`, `w′` is still inside the fetch's cut (`gwix w′ = 1 ≤ gfcut = 1`)… -/
theorem f6KInCut : gnxw f6K.gdG (0, 0) = some (0, 1) ∧ gwix f6K.gdG (1, 0) = 1 ∧
    gfcut f6K.gdG 0 0 = 1 := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩

def f6KOrd : List SBAcqP.Item :=
  [(false, (0, 0)), (false, (1, 0)), (true, (1, 0)), (false, (0, 1)), (false, (0, 2)),
   (true, (0, 1)), (true, (0, 2))]

/-- …and an S-P member of `f6K` lands `w′` while hart `i` has stepped ONLY its slot event (`gnxw` not
yet issued): the replay state `fetchReplayOk` asks for exists at `f6K`. -/
theorem f6KHeld :
    SBAcqP.FifoCore f6K.gdG (SBAcqP.pOf f6KOrd) (SBAcqP.qOf f6KOrd) ∧
    SBAcqP.ReadsGF f6K.gdG (SBAcqP.pOf f6KOrd) (SBAcqP.qOf f6KOrd) ∧
    CoGmoW f6K.gdG (SBAcqP.pOf f6KOrd) (SBAcqP.qOf f6KOrd) ∧
    SBAcqP.qOf f6KOrd (1, 0) < SBAcqP.pOf f6KOrd (0, 1) := by
  have h := SBAcqP.memberPBSound f6K.gdG (SBAcqP.pOf f6KOrd) (SBAcqP.qOf f6KOrd) (by decide +kernel)
  exact ⟨h.1, h.2.1, coGmoWBSound _ _ _ (by decide +kernel), by decide +kernel⟩

end SpikeSP

end Weak
