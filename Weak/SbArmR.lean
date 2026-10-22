/-
Weak: **the S-R `DomAt` lift, increment I-2 (2/2) — `SbArmR`, THE S-R ARMS and ONE WALK STEP**
(ruling [OWN.150]; `PROGRESS-DomAt.md` §0.2).  Lean-only, no Rocq twin.  A leaf: nothing registered
imports this file.

**Spec, stated first.**  riscv.cat's load value: a plain load reads its GF source; at an S-P state that
source's timestamp is its GF write index, and the read is admissible (stale or not) because the hart's
view is dominated (`SbDom.domAtOf`) — so the S-R arm uses GF's LABEL VERBATIM (`SpikeSR.staleLoadArm`).
An AMO, GF's next write, reads its source at the landed top (atomicity: no write co-between).  The remaining
exempt read ([OWN.124], `holding+0x12`) reads, PER BYTE, GF's source when it has landed and the landed top
otherwise (finding F-DomAt-2: the top of a landed byte may be co-after a po-later load's source, which would
strand it); its word is the exempt-value interface's (`ExValMin`, NAMED — the `ExValTop` of the min rule).

  §1  the arms: `armLd` (a gated plain load, GF's label, `SrBytes`), `armAmo` (an AMO, GF's label),
      `armX` (the exempt read, the per-byte min rule), and `armHdR` (every enabled head, with everything
      `SbOrdR.pinvEvR` needs).
  §2  **`walkStepR`**: every enabled genuine S-R item extends the walk (valid under the epoch buffer),
      keeps `PInvR` and decreases `SbOrd.work`.

Spec: FAITHFUL (proof organisation).  Lean-only helpers `SbOrdR.*`.
-/
import Weak.SbOrdR

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open Lbl

namespace SbOrdR

open SbWalk SbAgree SbReplay SbOrd SpikeSP SbDom

/-! # 1. The arms -/

/-- The per-byte MIN RULE word of an exempt read: forwarded, or the log at GF's timestamp when the source has
landed and at the landed top otherwise. -/
def minVals (w : WS) (x : Nat) (base : Int) (ts : List Nat) (vs : List (BitVec 8)) : Prop :=
  ∀ j v, vs[j]? = some v →
    SbCand.fwdByte (w.σ.sb x) (accAddr base j) = some v ∨
    (SbCand.fwdByte (w.σ.sb x) (accAddr base j) = none ∧ ∃ t, ts[j]? = some t ∧
      logByte w.σ.ms.msImg w.σ.ms.msLog
        (if t ≤ (wrW w).length then t else latestTs w.σ.ms.msLog (accAddr base j)) (accAddr base j) =
        some v)

/-- **THE EXEMPT-VALUE INTERFACE OF THE MIN RULE (NAMED; [OWN.124]'s member side under S-R)**: at a walk
state, the min-rule word an exempt read of a row's next GF event reads satisfies `exValV` — `ExValTop` with
the landed bytes read at GF's timestamp. -/
def ExValMin (G : Gexec) (X : Geid → Prop) (w : WS) : Prop :=
  ∀ (x : Nat) (base : Int) (ts : List Nat) (vs vs' : List (BitVec 8)), X (x, (w.rows x).length) →
    gxLbl G (x, (w.rows x).length) = some (LLoad false base ts vs) → vs'.length = ts.length →
    minVals w x base ts vs' → exValV x vs'

section Arms

variable {N : Nat} {G : Gexec} {X : Geid → Prop} {dev : List Geid}

/-- A GF write index inside the landed prefix names a landed write. -/
theorem landedOfIx {w : WS} (hW : wrW w <+: gwrites G) (t : Nat) (s : Geid) :
    gwriteAt G t = some s → t ≤ (wrW w).length → s ∈ wrW w := by
  intro hs ht
  cases t with
  | zero => simp [gwriteAt] at hs
  | succ i =>
    obtain ⟨T, hT⟩ := hW
    have hi : i < (wrW w).length := by omega
    have h : (gwrites G)[i]? = some s := hs
    rw [← hT, List.getElem?_append_left hi] at h
    exact List.mem_of_getElem? h

/-- The `SrOk` of a byte whose source has landed (an `.aq` load: its own source gmo-before it). -/
theorem srOkLanded (hc : CatH G) {w : WS} (hW : wrW w <+: gwrites G) (x : Nat) (aq : Bool) (base : Int)
    (ts : List Nat) (vs : List (BitVec 8)) (hl : gxLbl G (hd w x) = some (LLoad aq base ts vs))
    (j t : Nat) (v : BitVec 8) (htj : ts[j]? = some t) (hvj : vs[j]? = some v)
    (hland : t ≤ (wrW w).length)
    (haq : aq = true → ∀ s, gwriteAt G t = some s → s.1 = x → gmoLt G s (hd w x)) :
    SrOk G (wrW w) x (hd w x) aq ts j t := by
  refine ⟨t, htj, Nat.le_refl _, ?_⟩
  by_cases h0 : t = 0
  · exact .inl h0
  · obtain ⟨i, rfl⟩ : ∃ i, t = i + 1 := ⟨t - 1, by omega⟩
    have hrd : greadsByte G (hd w x) (accAddr base j) (i + 1) v := ⟨_, base, ts, vs, j, hl, rfl, htj, hvj, rfl⟩
    obtain ⟨⟨src, hs, -, -⟩, -⟩ := hc.lv _ _ _ _ hrd
    obtain ⟨hsG, hsix⟩ := gwriteAtInv G _ src hc.wf.1 hs
    rcases srcCases hc _ _ _ v src hrd hs with hlt | hpo
    · exact .inr (.inl ⟨src, hsG, hlt, by omega⟩)
    · cases aq with
      | true => exact .inr (.inl ⟨src, hsG, haq rfl src hs hpo.1, by omega⟩)
      | false => exact .inr (.inr ⟨rfl, rfl, src, hs, hpo.1, landedOfIx hW _ src hs hland⟩)

/-- **THE S-R LOAD ARM**: a gated plain load is an `SbCand` step with GF's label VERBATIM. -/
theorem armLd {c : CandW} (hP : PInvR N c.img G X dev (cur c)) (hc : CatH G) (himg : G.gxImg = c.img)
    (x : Nat) (aq : Bool) (base : Int) (ts : List Nat) (vs : List (BitVec 8))
    (hl : gxLbl G (hd (cur c) x) = some (LLoad aq base ts vs))
    (hrl : aq = true → SbCand.noRl ((cur c).σ.sb x)) (hg : srGate G (cur c) x aq base ts vs) :
    SbCand.stepE (cur c).σ x (LLoad aq base ts vs) (SbCand.nextE (cur c).σ x (LLoad aq base ts vs)) ∧
    SrBytes G (cur c) x aq base ts ts := by
  have hlen := lblShapeLd G hc.wf _ _ _ _ _ hl
  refine ⟨.load aq base ts vs (SpikeSR.staleLoadArm c.img G X (cur c) hP.inv hP.pf hP.spw hc.wf hc.lv
    himg x aq base ts vs hl (fun j t v htj hvj => ?_)) hrl, fun j t htj => ?_⟩
  · rcases hg j t v htj hvj with h | ⟨hn, hland, -⟩
    · exact .inl h
    · exact .inr ⟨hn, hland, domAtOf hc (hP.dom x) aq base ts vs hl _ t v
        ⟨_, base, ts, vs, j, hl, rfl, htj, hvj, rfl⟩⟩
  · have hjl : j < vs.length := by rw [hlen]; exact lookup_lt_Some htj
    rcases hg j t vs[j] htj (List.getElem?_eq_getElem hjl) with h | ⟨-, hland, haq⟩
    · left; simp [h]
    · right; exact srOkLanded hc hP.spw x aq base ts vs hl j t vs[j] htj (List.getElem?_eq_getElem hjl)
        hland haq

/-- The view bound of a candidate's state. -/
theorem floorLe {c : CandW} (hv : validW SbPol.epoch c) (x : Nat) (aq : Bool) (a : Int) :
    max (loadVpre ((cur c).σ.ms.msWs x) aq) (coh ((cur c).σ.ms.msWs x) a) ≤ (cur c).σ.ms.msLog.length := by
  have hSI : SbCand.Inv (cur c).σ := sbInvStAt SbPol.epoch c hv _
  exact Nat.max_le.2 ⟨loadVpreBounded _ aq _ (hSI x), (hSI x).2.2.2.2.2.2.1 a⟩

/-- **THE S-R AMO ARM**: an AMO that is GF's next write reads its GF sources at the landed top. -/
theorem armAmo {c : CandW} (hv : validW SbPol.epoch c) (hP : PInvR N c.img G X dev (cur c)) (hc : CatH G)
    (himg : G.gxImg = c.img) (x : Nat) (aq rl : Bool) (base : Int) (ts : List Nat)
    (rvs wvs : List (BitVec 8)) (kc : WmClass)
    (hl : gxLbl G (hd (cur c) x) = some (LRmw aq rl base ts rvs wvs kc))
    (hok : SbCand.amoOk ((cur c).σ.sb x) base ts.length) (hrl : rl = true → (cur c).σ.sb x = [])
    (haq : aq = true → SbCand.noRl ((cur c).σ.sb x)) (hS : wrW (cur c) ++ [hd (cur c) x] <+: gwrites G) :
    SbCand.stepE (cur c).σ x (LRmw aq rl base ts rvs wvs kc)
      (SbCand.nextE (cur c).σ x (LRmw aq rl base ts rvs wvs kc)) := by
  obtain ⟨hwne, hwl, hrl'⟩ := rmwShape hc.wf _ aq rl base ts rvs wvs kc hl
  have hix : gwix G (hd (cur c) x) = (wrW (cur c)).length + 1 := wixOfNext _ _ hc.wf.1 hS
  have hlog : (cur c).σ.ms.msLog.length = (wrW (cur c)).length :=
    (SpikeSR.logAt c.img G (cur c) hP.inv hP.spw).1
  have hkey : ∀ j t v, ts[j]? = some t → rvs[j]? = some v →
      logByte c.img (cur c).σ.ms.msLog t (accAddr base j) = some v ∧
      latest c.img (cur c).σ.ms.msLog (accAddr base j) t := by
    intro j t v htj hvj
    have hrd : greadsByte G (hd (cur c) x) (accAddr base j) t v := ⟨_, base, ts, rvs, j, hl, rfl, htj, hvj, rfl⟩
    have hjw : j < wvs.length := by rw [hwl]; exact lookup_lt_Some htj
    have hwr : gwritesByte G (hd (cur c) x) (accAddr base j) wvs[j] :=
      ⟨_, base, wvs, j, hl, rfl, List.getElem?_eq_getElem hjw, rfl⟩
    have hlt := srcLtWrite hc _ _ t v _ hrd hwr
    obtain ⟨hv1, hnw⟩ := SpikeSR.staleStep c.img G X (cur c) hP.inv hP.pf hP.spw hc.wf.1 hc.lv himg _ _ t v
      hrd (by omega) (cur c).σ.ms.msLog.length (fun n u hn htn => by
        have := hc.atom _ _ t v hrd ⟨_, hl, rfl⟩ n u hn
        omega)
    exact ⟨hv1, ⟨by rw [hv1]; rfl, hnw⟩⟩
  have himg' : (cur c).σ.ms.msImg = c.img := hP.inv.img
  refine .rmw aq rl base ts rvs wvs kc hwne hwl ⟨hrl', fun j t v htj hvj => ?_⟩ (fun j t htj => ?_) hok hrl haq
  · obtain ⟨hv1, hlat⟩ := hkey j t v htj hvj
    rw [himg']
    exact ⟨hv1, latestReadable _ _ _ _ _ _ (floorLe hv x aq _) hlat⟩
  · have hjr : j < rvs.length := by rw [hrl']; exact lookup_lt_Some htj
    rw [himg']
    exact (hkey j t rvs[j] htj (List.getElem?_eq_getElem hjr)).2

/-- An own unlanded write that is realized is pending, so a byte it writes is forwarded. -/
theorem fwdOfOwnUnlanded {img : Image} {w : WS} (hI : Inv img w) (hpf : pfx G X w) (x : Nat) (s : Geid)
    (a : Int) (u : BitVec 8) (hsx : s.1 = x) (hsr : s.2 < (w.rows x).length) (hsw : gwritesByte G s a u)
    (hsW : s ∉ w.gmo) : SbCand.fwdByte (w.σ.sb x) a ≠ none := by
  obtain ⟨l', hl'⟩ : ∃ l', (w.rows s.1)[s.2]? = some l' :=
    ⟨_, List.getElem?_eq_getElem (by rw [hsx]; exact hsr)⟩
  obtain ⟨l, hl, hrel⟩ := hpf.1 s.1 s.2 l' hl'
  have hlw : lbIsW l = true := by
    obtain ⟨l0, b0, vs0, j0, hl0, hw0, -⟩ := hsw
    rw [show gxLbl G (s.1, s.2) = gxLbl G s from rfl, hl0, Option.some.injEq] at hl
    subst hl; cases l0 <;> simp_all [lbWr, lbIsW]
  have hlw' : lbIsW l' = true := by rw [relXIsW _ l l' hrel]; exact hlw
  rcases hI.memIn s.1 s.2 l' hl' (memOfWr _ hlw') with h | h
  · exact absurd h hsW
  · obtain ⟨q, hq, hq1⟩ := List.mem_map.1 h
    rw [hsx] at hq
    obtain ⟨rl, base, vs, kc, hlq, hrowq, hmq⟩ := pendLblI hI hpf x q hq
    have hcov : (msgByte q.2.msg a).isSome = true := by
      have hs' : s = (x, q.1) := Prod.ext hsx hq1.symm
      rw [hs'] at hsw
      obtain ⟨l1, b1, vs1, j1, hl1, hw1, hv1, ha1⟩ := hsw
      rw [hlq, Option.some.injEq] at hl1
      subst hl1
      simp only [lbWr, Option.some.injEq, Prod.mk.injEq] at hw1
      obtain ⟨rfl, rfl⟩ := hw1
      rw [hmq, ← ha1, msgByteVal, hv1]; rfl
    rw [hI.sb x]
    rcases fwdRel (w.pend x) a with ⟨h1, -⟩ | ⟨p, -, -, h2, h3⟩
    · rw [fwdIdFold] at h1
      have := fwdFoldNone a _ none h1 q hq
      rw [hcov] at this; cases this
    · rw [h2]; intro h; rw [h] at h3; cases h3

/-- **THE S-R EXEMPT ARM** ([OWN.124]; finding F-DomAt-2): the per-byte min rule. -/
theorem armX {c : CandW} (hv : validW SbPol.epoch c) (hP : PInvR N c.img G X dev (cur c)) (hc : CatH G)
    (himg : G.gxImg = c.img) (x : Nat) (base : Int) (ts : List Nat) (vs : List (BitVec 8))
    (hl : gxLbl G (hd (cur c) x) = some (LLoad false base ts vs))
    (hdef : ∀ j, j < ts.length → (c.img (accAddr base j)).isSome) :
    ∃ ts' vs', lblReidxSub (LLoad false base ts vs) (LLoad false base ts' vs') ∧ minVals (cur c) x base ts vs' ∧
      SbCand.stepE (cur c).σ x (LLoad false base ts' vs')
        (SbCand.nextE (cur c).σ x (LLoad false base ts' vs')) ∧
      SrBytes G (cur c) x false base ts ts' := by
  classical
  have hlen := lblShapeLd G hc.wf _ _ _ _ _ hl
  have himg' : (cur c).σ.ms.msImg = c.img := hP.inv.img
  have hlog : (cur c).σ.ms.msLog.length = (wrW (cur c)).length :=
    (SpikeSR.logAt c.img G (cur c) hP.inv hP.spw).1
  let L := (wrW (cur c)).length
  let tf : Nat → Nat := fun j => match ts[j]? with
    | some t => if t ≤ L then t else latestTs (cur c).σ.ms.msLog (accAddr base j)
    | none => 0
  let vf : Nat → BitVec 8 := fun j => match SbCand.fwdByte ((cur c).σ.sb x) (accAddr base j) with
    | some v => v
    | none => (logByte c.img (cur c).σ.ms.msLog (tf j) (accAddr base j)).getD 0
  let ts' := (List.range ts.length).map tf
  let vs' := (List.range ts.length).map vf
  have hts' : ∀ j t', ts'[j]? = some t' → j < ts.length ∧ t' = tf j := by
    intro j t' hj
    have hjl : j < ts.length := by have := lookup_lt_Some hj; simpa [ts'] using this
    simp only [ts', List.getElem?_map, List.getElem?_range hjl, Option.map_some, Option.some.injEq] at hj
    exact ⟨hjl, hj.symm⟩
  have hvs' : ∀ j v', vs'[j]? = some v' → j < ts.length ∧ v' = vf j := by
    intro j v' hj
    have hjl : j < ts.length := by have := lookup_lt_Some hj; simpa [vs'] using this
    simp only [vs', List.getElem?_map, List.getElem?_range hjl, Option.map_some, Option.some.injEq] at hj
    exact ⟨hjl, hj.symm⟩
  -- the per-byte facts at a non-forwarded byte
  have hbyte : ∀ j, j < ts.length → SbCand.fwdByte ((cur c).σ.sb x) (accAddr base j) = none →
      logByte c.img (cur c).σ.ms.msLog (tf j) (accAddr base j) = some (vf j) ∧
      readable c.img (cur c).σ.ms.msLog ((cur c).σ.ms.msWs x) (loadVpre ((cur c).σ.ms.msWs x) false)
        (accAddr base j) (tf j) ∧
      SrOk G (wrW (cur c)) x (hd (cur c) x) false ts j (tf j) := by
    intro j hj hf
    obtain ⟨t, htj⟩ : ∃ t, ts[j]? = some t := ⟨_, List.getElem?_eq_getElem hj⟩
    have hjv : j < vs.length := by rw [hlen]; exact hj
    have hrd : greadsByte G (hd (cur c) x) (accAddr base j) t vs[j] :=
      ⟨_, base, ts, vs, j, hl, rfl, htj, List.getElem?_eq_getElem hjv, rfl⟩
    have htf : tf j = if t ≤ L then t else latestTs (cur c).σ.ms.msLog (accAddr base j) := by
      simp only [tf, htj]
    have hvf : vf j = (logByte c.img (cur c).σ.ms.msLog (tf j) (accAddr base j)).getD 0 := by
      simp only [vf, hf]
    by_cases hland : t ≤ L
    · rw [if_pos hland] at htf
      have hdom := domAtOf hc (hP.dom x) false base ts vs hl _ t _ hrd
      obtain ⟨hv1, hnw⟩ := SpikeSR.staleStep c.img G X (cur c) hP.inv hP.pf hP.spw hc.wf.1 hc.lv himg _ _
        t _ hrd hland _ hdom
      rw [htf] at hvf ⊢
      refine ⟨by simp only [hvf, hv1, Option.getD_some], ⟨by simp [hv1], hnw⟩, srOkLanded hc hP.spw x false base ts vs hl j t vs[j] htj
        (List.getElem?_eq_getElem hjv) hland (fun h => by cases h)⟩
    · rw [if_neg hland] at htf
      have hsome : (logByte c.img (cur c).σ.ms.msLog (latestTs (cur c).σ.ms.msLog (accAddr base j))
          (accAddr base j)).isSome :=
        latestTsSome _ _ _ 0 (by rw [logByte0]; exact hdef j hj)
      have hlat := latestTsLatest _ _ _ hsome
      obtain ⟨v1, hv1⟩ := Option.isSome_iff_exists.1 hsome
      rw [htf] at hvf ⊢
      refine ⟨by simp only [hvf, hv1, Option.getD_some], ?_, t, htj, ?_, .inr (.inl ?_)⟩
      · exact latestReadable _ _ _ _ _ _ (floorLe hv x false (accAddr base j)) hlat
      · have := latestTsLe (cur c).σ.ms.msLog (accAddr base j); omega
      · -- the GF source: gmo-before the read (an own source unlanded would be forwarded)
        have ht0 : t ≠ 0 := by omega
        obtain ⟨i, rfl⟩ : ∃ i, t = i + 1 := ⟨t - 1, by omega⟩
        obtain ⟨⟨src, hs, hsw, -⟩, -⟩ := hc.lv _ _ _ _ hrd
        obtain ⟨hsG, hsix⟩ := gwriteAtInv G _ src hc.wf.1 hs
        refine ⟨src, hsG, ?_, by have := latestTsLe (cur c).σ.ms.msLog (accAddr base j); omega⟩
        rcases srcCases hc _ _ _ _ src hrd hs with hlt | hpo
        · exact hlt
        · exfalso
          have hsW : src ∉ (cur c).gmo := by
            intro hm
            have hwW : src ∈ wrW (cur c) := List.mem_filter.2 ⟨hm, by
              obtain ⟨l', hl', -⟩ := hP.inv.gmoMem src hm
              obtain ⟨l, hlg, hrel⟩ := hP.pf.1 src.1 src.2 l' hl'
              unfold rwW; rw [hl']; show lbIsW l' = true; rw [relXIsW _ l l' hrel]
              obtain ⟨l0, b0, vs0, j0, hl0, hw0, -⟩ := hsw
              rw [show gxLbl G (src.1, src.2) = gxLbl G src from rfl, hl0, Option.some.injEq] at hlg
              subst hlg; cases l0 <;> simp_all [lbWr, lbIsW]⟩
            have := wixLeOfPfx _ src hc.wf.1 hP.spw hwW
            omega
          exact fwdOfOwnUnlanded hP.inv hP.pf x src _ _ hpo.1 hpo.2.1 hsw hsW hf
  refine ⟨ts', vs', ⟨rfl, rfl, rfl, by simp [ts'], by simp [ts', vs']⟩, fun j v' hj => ?_, ?_, ?_⟩
  · obtain ⟨hjl, rfl⟩ := hvs' j v' hj
    cases hf : SbCand.fwdByte ((cur c).σ.sb x) (accAddr base j) with
    | some v => left; simp only [vf, hf]
    | none =>
      right
      obtain ⟨t, htj⟩ : ∃ t, ts[j]? = some t := ⟨_, List.getElem?_eq_getElem hjl⟩
      refine ⟨rfl, t, htj, ?_⟩
      have := (hbyte j hjl hf).1
      rw [himg']
      simp only [tf, htj] at this
      exact this
  · refine .load false base ts' vs' ⟨by simp [ts', vs'], fun j t' v' htj hvj => ?_⟩ (fun h => by cases h)
    obtain ⟨hjl, rfl⟩ := hts' j t' htj
    obtain ⟨-, rfl⟩ := hvs' j v' hvj
    cases hf : SbCand.fwdByte ((cur c).σ.sb x) (accAddr base j) with
    | some v => left; simp only [vf, hf]
    | none =>
      right
      obtain ⟨h1, h2, -⟩ := hbyte j hjl hf
      rw [himg']
      exact ⟨rfl, h1, h2⟩
  · intro j t' htj
    obtain ⟨hjl, rfl⟩ := hts' j t' htj
    cases hf : SbCand.fwdByte ((cur c).σ.sb x) (accAddr base j) with
    | some v => left; rfl
    | none => right; exact (hbyte j hjl hf).2.2

/-- **THE S-R HEAD ARMS**: an enabled head's member label — GF's label verbatim (a gated load, an AMO, a
store, a fence, an I/O step), the min-rule read (an exempt load) — with everything `pinvEvR` needs. -/
theorem armHdR {c : CandW} (hv : validW SbPol.epoch c) (hP : PInvR N c.img G X dev (cur c)) (hc : CatH G)
    (hI : ImgFacts G) (himg : G.gxImg = c.img)
    (hX : ∀ e l, X e → gxLbl G e = some l → ∃ base ts vs, l = LLoad false base ts vs)
    (hdef : ∀ e a t v, greadsByte G e a t v → (c.img a).isSome) (hEx : ExValMin G X (cur c))
    (x : Nat) (l : Lbl) (hl : gxLbl G (hd (cur c) x) = some l)
    (he : enbLR G X (cur c) (hd (cur c) x) l) :
    ∃ lb', lblRelX (X (hd (cur c) x)) l lb' ∧
      SbCand.stepE (cur c).σ x lb' (SbCand.nextE (cur c).σ x lb') ∧
      (¬ X (hd (cur c) x) → lb' = l) ∧
      (∀ aq rl base ts rvs wvs kc, l = LRmw aq rl base ts rvs wvs kc →
        lb' = l ∧ wrW (cur c) ++ [hd (cur c) x] <+: gwrites G) ∧
      (∀ aq base ts vs ts' vs', l = LLoad aq base ts vs → lb' = LLoad aq base ts' vs' →
        SrBytes G (cur c) x aq base ts ts') ∧
      (∀ rl base vs kc, lb' = LStore rl base vs kc → rl = false) ∧
      (X (hd (cur c) x) → exValL x lb') ∧
      (∀ rl base vs kc, lb' = LStore rl base vs kc → NCPU ≤ x →
        wrW (cur c) ++ [hd (cur c) x] <+: gwrites G) := by
  have hnX : ∀ l0, gxLbl G (hd (cur c) x) = some l0 → (∀ base ts vs, l0 ≠ LLoad false base ts vs) →
      ¬ X (hd (cur c) x) := by
    intro l0 hl0 hn hx
    obtain ⟨base, ts, vs, h⟩ := hX _ l0 hx hl0
    exact hn base ts vs h
  cases l with
  | LLoad aq base ts vs =>
    rcases he with hx | ⟨hx, hrl, hg⟩
    · obtain ⟨b0', t0', v0', h⟩ := hX _ _ hx hl
      have haq : aq = false := by injection h
      subst haq
      have hlen := lblShapeLd G hc.wf _ _ _ _ _ hl
      obtain ⟨ts', vs', hsub, hmin, hst, hsr⟩ := armX hv hP hc himg x base ts vs hl
        (fun j hj => hdef _ _ _ _ ⟨_, base, ts, vs, j, hl, rfl, List.getElem?_eq_getElem hj,
          List.getElem?_eq_getElem (by rw [hlen]; exact hj), rfl⟩)
      obtain ⟨-, -, -, hl1, hl2⟩ := hsub
      refine ⟨LLoad false base ts' vs', .inr ⟨hx, ⟨rfl, rfl, rfl, hl1, hl2⟩⟩, hst, fun h => absurd hx h,
        (fun _ _ _ _ _ _ _ h => by cases h), fun aq0 base0 ts0 vs0 ts1 vs1 h1 h2 => ?_,
        (fun _ _ _ _ h => by cases h), fun _ => ⟨base, ts', vs', rfl, ?_⟩, (fun _ _ _ _ h => by cases h)⟩
      · simp only [LLoad.injEq] at h1 h2
        obtain ⟨rfl, rfl, rfl, -⟩ := h1
        obtain ⟨-, -, rfl, -⟩ := h2
        exact hsr
      · exact hEx x base ts vs vs' hx hl (by rw [hl2, hl1]) hmin
    · obtain ⟨hst, hsr⟩ := armLd hP hc himg x aq base ts vs hl hrl hg
      refine ⟨LLoad aq base ts vs, .inl ⟨hx, lblReidxRefl _⟩, hst, fun _ => rfl,
        (fun _ _ _ _ _ _ _ h => by cases h), fun aq0 base0 ts0 vs0 ts1 vs1 h1 h2 => ?_,
        (fun _ _ _ _ h => by cases h), fun h => absurd h hx, (fun _ _ _ _ h => by cases h)⟩
      simp only [LLoad.injEq] at h1 h2
      obtain ⟨rfl, rfl, rfl, -⟩ := h1
      obtain ⟨-, -, rfl, -⟩ := h2
      exact hsr
  | LStore rl base vs kc =>
    have hx := hnX _ hl (fun _ _ _ h => by cases h)
    have hne : vs ≠ [] := by
      unfold gxLbl at hl
      cases hr : G.gxProg[(hd (cur c) x).1]? with
      | none => rw [hr] at hl; cases hl
      | some row =>
        rw [hr] at hl; simp only [Option.bind_some] at hl
        exact hc.wf.2.2 _ row _ _ hr hl
    refine ⟨_, .inl ⟨hx, lblReidxRefl _⟩, .issue rl base vs kc hne he.1, fun _ => rfl,
      (fun _ _ _ _ _ _ _ h => by cases h), (fun _ _ _ _ _ _ h => by cases h), fun rl0 _ _ _ h => ?_,
      fun h => absurd h hx, fun _ _ _ _ _ hxd => he.2 hxd⟩
    simp only [LStore.injEq] at h
    obtain ⟨rfl, -⟩ := h
    have := hI.noRl _ _ hl
    simpa [lbRl] using this
  | LFence pr pw sr sw =>
    have hx := hnX _ hl (fun _ _ _ h => by cases h)
    exact ⟨_, .inl ⟨hx, lblReidxRefl _⟩, .fence pr pw sr sw he, fun _ => rfl,
      (fun _ _ _ _ _ _ _ h => by cases h), (fun _ _ _ _ _ _ h => by cases h), (fun _ _ _ _ h => by cases h),
      fun h => absurd h hx, (fun _ _ _ _ h => by cases h)⟩
  | LRmw aq rl base ts rvs wvs kc =>
    have hx := hnX _ hl (fun _ _ _ h => by cases h)
    obtain ⟨hok, hrl, haq, hS⟩ := he
    exact ⟨_, .inl ⟨hx, lblReidxRefl _⟩, armAmo hv hP hc himg x aq rl base ts rvs wvs kc hl hok hrl haq hS,
      fun _ => rfl, fun _ _ _ _ _ _ _ _ => ⟨rfl, hS⟩, (fun _ _ _ _ _ _ h => by cases h),
      (fun _ _ _ _ h => by cases h), fun h => absurd h hx, (fun _ _ _ _ h => by cases h)⟩
  | LIo kd base vs =>
    have hx := hnX _ hl (fun _ _ _ h => by cases h)
    exact ⟨_, .inl ⟨hx, lblReidxRefl _⟩, .io kd base vs, fun _ => rfl,
      (fun _ _ _ _ _ _ _ h => by cases h), (fun _ _ _ _ _ _ h => by cases h), (fun _ _ _ _ h => by cases h),
      fun h => absurd h hx, (fun _ _ _ _ h => by cases h)⟩

end Arms

/-! # 2. One walk step -/

/-- **`walkStepR` — ONE S-R WALK STEP**: an enabled genuine item extends the walk (valid under the epoch
buffer), keeps `PInvR` and strictly decreases the work. -/
theorem walkStepR (GF : Gfexec) (N : Nat) (X : Geid → Prop) (c : CandW)
    (hW : WalkHyp GF N c.img X) (hv : validW SbPol.epoch c)
    (hP : PInvR N c.img GF.gfGd.gdG X GF.gfDev (cur c)) (hEx : ExValMin GF.gfGd.gdG X (cur c))
    (T : Tgt) (hT : validT N GF.gfGd.gdG (cur c) T)
    (he : enbR SbPol.epoch GF.gfGd.gdG X GF.gfDev (cur c) T) :
    ∃ it, validW SbPol.epoch (snocC c it) ∧ PInvR N c.img GF.gfGd.gdG X GF.gfDev (cur (snocC c it)) ∧
      work N GF.gfGd.gdG (cur (snocC c it)) < work N GF.gfGd.gdG (cur c) ∧ itemTgt it = T := by
  cases T with
  | ld i k =>
    obtain ⟨hi, -⟩ := hT
    obtain ⟨hq, p, hp, hok, -⟩ := id he
    refine ⟨.land i k, validSnoc _ c _ hv hok, by rw [curSnoc]; exact pinvLandR hW.cat _ hP i k hq he.2, ?_,
      rfl⟩
    rw [curSnoc]
    refine sumToLt _ _ i N hi ?_ (fun y hy => ?_)
    · rw [landEq i k p hp]
      dsimp only
      rw [updEq, List.length_eraseIdx, if_pos (lookup_lt_Some hp)]
      have := lookup_lt_Some hp
      omega
    · rw [landEq i k p hp]
      dsimp only
      rw [updNe _ _ _ _ hy]
  | hd x =>
    obtain ⟨hx, hcnt⟩ := hT
    obtain ⟨hq, l, hl, hfab, hen⟩ := he
    obtain ⟨lb', hrel, hst, hvb, hamo, hld, hnrl, hex, hdev⟩ := armHdR hv hP hW.cat hW.imgF hW.imgEq hW.ex
      hW.def' hEx x l hl hen
    refine ⟨.ev ⟨x, lb'⟩, validSnoc _ c _ hv hst, by
      rw [curSnoc]; exact pinvEvR hW.cat hP x hx hcnt l lb' hl hrel hst hfab hvb hamo hld hnrl hex hq hdev,
      ?_, rfl⟩
    rw [curSnoc]
    refine sumToLt _ _ x N hx ?_ (fun y hy => ?_)
    · rw [rowsEvEq, if_pos rfl, pendEvEq, if_pos rfl, List.length_append, List.length_singleton]
      dsimp only
      have hpe : (pendE (cur c) x lb').length ≤ ((cur c).pend x).length + 1 := by
        rcases pendECases (cur c) x lb' with ⟨_, _, _, _, -, h⟩ | ⟨_, _, -, h⟩ | h <;> rw [h] <;> simp
      omega
    · rw [rowsEvEq, if_neg hy, pendEvEq, if_neg hy]

end SbOrdR

end Weak
