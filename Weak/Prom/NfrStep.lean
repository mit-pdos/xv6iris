/-
Weak/Prom: **NF_R, the step level** (stage S4b, track (b); plan rev 7 §4 "Run shape NF_R", "NF_R lemma").

The plan's NF_R construction runs a hart's segment against a PREFIX of the final memory `M`.  This file proves the
three step facts that make that possible, for every arm of machine v2 (`memStep`, Machine.lean):

* `memStep_restrict` — RESTRICTION, the converse of `memStep_extend` (MachFactor.lean): a state step against `M`
  whose read timestamps and fulfil timestamp lie in the prefix `L` is a state step against `L`, with the same label,
  timestamp and post-state, from the promise set cut at `|L|`.  Premise `invalFree M` (no invalidate-class CMO in
  `M`): the invalidate clause `invalRead` (Machine.lean) lets a load cite an invalidate ABOVE every view (its post-view
  does not absorb it, D-v2-5), a fourth escape the plan's list (§4: fetches, `lat` loads, sink-free walks, A/D) does
  not name.  It is a premise of NF_R here and is reported (PROGRESS-S4b.md, R-b5).
* `memStep_self` — THE SELF BOUND: with `bnd ws := vrOld ⊔ vwOld ⊔ wIfr`, every timestamp a step reads or fulfils
  is at most `bnd` of its post-state, `bnd` only grows, and `psBounded ws (bnd ws)` is kept.  So every view of a hart
  is bounded by its loads (`vrOld`), its fulfils (`vwOld`) and its fetches (`wIfr`), the plan's "Why the segment
  fits" (§4).
* `relClass` — THE RELEASE CLASS, plan §3 "Release-class, defined precisely" [R1.8]: a write step (the five fulfil
  arms: store, fused AMO, AMO write half, SC, CMO) whose pre-view (`wrPre`, the expression its EXT premise compares
  with `ts`) is at least `vrOld ⊔ vwOld` of the state immediately before the write (`wrState`: for the fused AMO the
  state after its read half).  `relClass_lt`: a release-class write at `ts` has `vrOld ⊔ vwOld < ts` before it.
  Machine v2 has no A/D arm ([OWN.P3]), so the plan's exclusion of `WPAd`/`WPAspec` is vacuous.

No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Prom.MachSolo

namespace Weak.Prom.Nfr

open MachCSL MachCSL.Stdpp Iris.Std
open Weak (Image Dsrc)
open Weak.Prom
open PLabel

/-! ## 1. Definitions -/

/-- The state immediately before the WRITE of a write step (plan §3: "For an AMO, that state already includes the
read half's update"): the post-read state for the fused AMO, the step's own state otherwise. -/
def wrState (ws : PState) : PLabel → PState
  | LRmw aq _ base tvs _ asrc _ => loadRun ws aq false (srcsView ws asrc) base tvs
  | _ => ws

/-- The PRE-VIEW of a write step: exactly the expression its EXT premise compares with the timestamp (Machine.lean
arms `store`, `rmw`, `amoSt`, `sc`, `cmo`); `none` for a label that writes nothing. -/
def wrPre (ws : PState) : PLabel → Option Nat
  | LStore aq rl _ _ asrc vsrc => some (stPreA ws aq rl (srcsView ws asrc) (srcsView ws vsrc))
  | LRmw aq rl base tvs _ asrc vsrc =>
      some (stPre (loadRun ws aq false (srcsView ws asrc) base tvs) rl (srcsView ws asrc) (srcsView ws vsrc))
  | LAmoSt rl _ _ asrc vsrc => some (stPre ws rl (srcsView ws asrc) (srcsView ws vsrc))
  | LExStore aq rl _ _ asrc vsrc =>
      ws.wRes.map (fun R => max (stPreA ws aq rl (srcsView ws asrc) (srcsView ws vsrc)) R.rvView)
  | LCmo _ _ _ asrc => some (stPre ws false (srcsView ws asrc) 0)
  | _ => none

/-- RELEASE-CLASS (plan §3 [R1.8]): the write's pre-view is at least `vrOld ⊔ vwOld` of the state immediately
before the write.  A property of the machine step, decidable from `ws` and the label, never of the program text.
Examples: an `rl` store or AMO (`stPre`'s rule-6 term); `fence rw,w` directly before a plain store (`fencePost`
raises `vwNew` to `vrOld ⊔ vwOld`). -/
def relClass (ws : PState) (l : PLabel) : Prop :=
  ∃ pv, wrPre ws l = some pv ∧ max (wrState ws l).wVrOld (wrState ws l).wVwOld ≤ pv

/-- THE SELF BOUND of a hart state: its load, store and fetch maxima. -/
def bnd (ws : PState) : Nat := max (max ws.wVrOld ws.wVwOld) ws.wIfr

/-- Every timestamp the label reads (load-like entries and fetches, `labelReads`) is at most `n`. -/
def readsLe (l : PLabel) (n : Nat) : Prop :=
  ∀ base tvs, labelReads l = some (base, tvs) → bytesAll (fun _ t _ => t ≤ n) base tvs

/-- No invalidate-class cache-block operation in `M` (premise of the restriction; see the header). -/
def invalFree (M : List PMsg) : Prop := ∀ t a, ¬ cmoAt M isInvalK t a

/-! ## 2. Prefix monotonicity of the negative premises -/

theorem writesIn_pre {L M : List PMsg} (hpre : L <+: M) {a : Int} {lo hi : Nat} (h : writesIn L a lo hi) :
    writesIn M a lo hi := by
  obtain ⟨t, h1, h2, m, hm, hb⟩ := h
  have hlt : t - 1 < L.length := (List.getElem?_eq_some_iff.1 hm).1
  exact ⟨t, h1, h2, m, by rw [prefix_getElem? hpre hlt]; exact hm, hb⟩

theorem writesInBy_pre {L M : List PMsg} (hpre : L <+: M) {Q : Option Nat → Prop} {a : Int} {lo hi : Nat}
    (h : writesInBy L Q a lo hi) : writesInBy M Q a lo hi := by
  obtain ⟨t, h1, h2, m, hm, hb⟩ := h
  have hlt : t - 1 < L.length := (List.getElem?_eq_some_iff.1 hm).1
  exact ⟨t, h1, h2, m, by rw [prefix_getElem? hpre hlt]; exact hm, hb⟩

theorem exclOk_pre {L M : List PMsg} (hpre : L <+: M) {i ts : Nat} :
    ∀ (a : Int) (l : List Nat), exclOk M i a l ts → exclOk L i a l ts
  | _, [], _ => trivial
  | a, _ :: r, ⟨h1, h2⟩ => ⟨fun h => h1 (writesInBy_pre hpre h), exclOk_pre hpre (a + 1) r h2⟩

theorem loadOk_restrict {img : Image} {L M : List PMsg} (hpre : L <+: M) (hinv : invalFree M) {ws : PState}
    {vpre : Nat} : ∀ {base : Int} {tvs : List (Nat × BitVec 8)}, loadOk img M ws vpre base tvs →
      bytesAll (fun _ t _ => t ≤ L.length) base tvs → loadOk img L ws vpre base tvs := by
  intro base tvs hok hts
  unfold loadOk at hok ⊢
  -- the floor expressions mention `base`/`tvs` globally; generalise the run while keeping them
  have key : ∀ (a : Int) (r : List (Nat × BitVec 8)),
      bytesAll (fun a t v => memByte img M t a = some v ∧
        (¬ writesIn M a t (max (if fwdHit ws a t then vpre else max vpre (nonFwdMax ws base tvs)) (coh ws a)) ∨
          invalRead M a t (max vpre (coh ws a)))) a r →
      bytesAll (fun _ t _ => t ≤ L.length) a r →
      bytesAll (fun a t v => memByte img L t a = some v ∧
        (¬ writesIn L a t (max (if fwdHit ws a t then vpre else max vpre (nonFwdMax ws base tvs)) (coh ws a)) ∨
          invalRead L a t (max vpre (coh ws a)))) a r := by
    intro a r
    induction r generalizing a with
    | nil => intro _ _; trivial
    | cons tv r ih =>
      obtain ⟨t, v⟩ := tv
      rintro ⟨⟨hm, hw⟩, h2⟩ ⟨ht, h3⟩
      refine ⟨⟨by rw [← memByte_ext hpre ht]; exact hm, ?_⟩, ih (a + 1) h2 h3⟩
      rcases hw with hw | hw
      · exact .inl (fun h => hw (writesIn_pre hpre h))
      · obtain ⟨ti, hc, _⟩ := hw
        exact absurd hc (hinv ti a)
  exact key base tvs hok hts

/-! ## 3. Restriction -/

theorem promCut_diff {prom Q : GSet Nat} {n ts : Nat} (hQ : ∀ t, t ∈ Q ↔ t ∈ prom ∧ t ≤ n) :
    ∀ t, t ∈ Q \ {ts} ↔ t ∈ prom \ {ts} ∧ t ≤ n := by
  intro t
  rw [elemOfDifference, elemOfDifference, hQ t]
  exact ⟨fun ⟨⟨a, b⟩, c⟩ => ⟨⟨a, c⟩, b⟩, fun ⟨⟨a, c⟩, b⟩ => ⟨⟨a, b⟩, c⟩⟩

/-- THE ARM LEMMA OF RESTRICTION: a state step against `M` whose read and fulfil timestamps lie in the prefix `L` is
a state step against `L` with the same label, timestamp and post-state, from the promise set cut at `|L|`. -/
theorem memStep_restrict {img : Image} {L M : List PMsg} {i : Nat} {prom : GSet Nat} {ws : PState} {l : PLabel}
    {ots : Option Nat} {ws' : PState} {prom' : GSet Nat} (Q : GSet Nat)
    (h : memStep img M i prom ws l ots ws' prom') (hpre : L <+: M) (hinv : invalFree M)
    (hr : readsLe l L.length) (hts : ∀ ts, ots = some ts → ts ≤ L.length)
    (hQ : ∀ t, t ∈ Q ↔ t ∈ prom ∧ t ≤ L.length) :
    ∃ Q', memStep img L i Q ws l ots ws' Q' ∧ ∀ t, t ∈ Q' ↔ t ∈ prom' ∧ t ≤ L.length := by
  have hmsg : ∀ ts (m : PMsg), 0 < ts → ts ≤ L.length → M[ts - 1]? = some m → L[ts - 1]? = some m := by
    intro ts m h0 hts' hm
    rw [← prefix_getElem? hpre (by omega)]
    exact hm
  have hin : ∀ ts, ts ∈ prom → ts ≤ L.length → ts ∈ Q := fun ts h1 h2 => (hQ ts).2 ⟨h1, h2⟩
  cases h with
  | silent => exact ⟨Q, .silent _ _, hQ⟩
  | load aq rl base tvs asrc hok =>
    exact ⟨Q, .load _ _ _ _ _ _ _ (loadOk_restrict hpre hinv hok (hr _ _ rfl)), hQ⟩
  | store aq rl base data asrc vsrc ts hts' hm hc hpv =>
    have h1 := hts ts rfl
    exact ⟨Q \ {ts}, .store _ _ _ _ _ _ _ _ _ (hin ts hts' h1) (hmsg ts _ (by omega) h1 hm) hc hpv,
      promCut_diff hQ⟩
  | rmw aq rl base tvs data asrc vsrc ts hlen hts' hm hok hx hc hpv =>
    have h1 := hts ts rfl
    exact ⟨Q \ {ts}, .rmw _ _ _ _ _ _ _ _ _ _ hlen (hin ts hts' h1) (hmsg ts _ (by omega) h1 hm)
      (loadOk_restrict hpre hinv hok (hr _ _ rfl)) (exclOk_pre hpre _ _ hx) hc hpv, promCut_diff hQ⟩
  | amoLd aq base tvs asrc hok =>
    exact ⟨Q, .amoLd _ _ _ _ _ _ (loadOk_restrict hpre hinv hok (hr _ _ rfl)), hQ⟩
  | amoSt rl base data asrc vsrc ts R hR hb' hlen hts' hm hx hc hpv =>
    have h1 := hts ts rfl
    exact ⟨Q \ {ts}, .amoSt _ _ _ _ _ _ _ _ R hR hb' hlen (hin ts hts' h1) (hmsg ts _ (by omega) h1 hm)
      (exclOk_pre hpre _ _ hx) hc hpv, promCut_diff hQ⟩
  | fence => exact ⟨Q, .fence _ _ _ _ _ _, hQ⟩
  | fenceI => exact ⟨Q, .fenceI _ _, hQ⟩
  | dev => exact ⟨Q, .dev _ _ _ _ _ _ _, hQ⟩
  | regW rd srcs => exact ⟨Q, .regW _ _ _ _, hQ⟩
  | ctrl srcs => exact ⟨Q, .ctrl _ _ _, hQ⟩
  | instr => exact ⟨Q, .instr _ _, hQ⟩
  | lr aq rl base tvs asrc hok =>
    exact ⟨Q, .lr _ _ _ _ _ _ _ (loadOk_restrict hpre hinv hok (hr _ _ rfl)), hQ⟩
  | sc aq rl base data asrc vsrc ts R hR hts' hm hx hlt hc hpv =>
    have h1 := hts ts rfl
    exact ⟨Q \ {ts}, .sc _ _ _ _ _ _ _ _ _ R hR (hin ts hts' h1) (hmsg ts _ (by omega) h1 hm)
      (exclOk_pre hpre _ _ hx) hlt hc hpv, promCut_diff hQ⟩
  | scFail => exact ⟨Q, .scFail _ _, hQ⟩
  | fetch base tvs hok =>
    have hts' : bytesAll (fun _ t _ => t ≤ L.length) base tvs := hr _ _ rfl
    have hok' : bytesAll (fetchByteOk img L ws) base tvs := by
      have key : ∀ (a : Int) (r : List (Nat × BitVec 8)), bytesAll (fetchByteOk img M ws) a r →
          bytesAll (fun _ t _ => t ≤ L.length) a r → bytesAll (fetchByteOk img L ws) a r := by
        intro a r
        induction r generalizing a with
        | nil => intro _ _; trivial
        | cons tv r ih =>
          obtain ⟨t, v⟩ := tv
          rintro ⟨⟨hm, hw⟩, h2⟩ ⟨ht, h3⟩
          exact ⟨⟨by rw [← memByte_ext hpre ht]; exact hm, fun h => hw (writesIn_pre hpre h)⟩, ih (a + 1) h2 h3⟩
      exact key base tvs hok hts'
    have hlow : ∀ t, t ≤ L.length → (t ∈ prom ↔ t ∈ Q) := by
      intro t ht; rw [hQ t]; exact ⟨fun h => ⟨h, ht⟩, fun h => h.1⟩
    have e : fetchView M i prom base tvs = fetchView L i Q base tvs := by
      unfold fetchView
      refine bytesMax_congr base tvs (bytesAll_mono (fun a t _ ht => ?_) base tvs hts')
      rw [ownDone_ext hpre ht hlow]
    refine ⟨Q, ?_, hQ⟩
    rw [e]
    exact .fetch _ _ _ _ hok'
  | cmo k base len asrc ts hts' hm hc hpv =>
    have h1 := hts ts rfl
    exact ⟨Q \ {ts}, .cmo _ _ _ _ _ _ _ (hin ts hts' h1) (hmsg ts _ (by omega) h1 hm) hc hpv,
      promCut_diff hQ⟩

/-! ## 4. Bounds at an arbitrary level `n` (MachWf's `memStep_bnd`, with the log length replaced by `n`) -/

theorem memStep_bndN {img : Image} {log : List PMsg} {i : Nat} {prom : GSet Nat} {ws : PState} {l : PLabel}
    {ots : Option Nat} {ws' : PState} {prom' : GSet Nat} {n : Nat} (h : memStep img log i prom ws l ots ws' prom')
    (hb : psBounded ws n) (hr : readsLe l n) (hts : ∀ ts, ots = some ts → ts ≤ n) : psBounded ws' n := by
  have hsv : ∀ s, srcsView ws s ≤ n := srcsView_le hb.2.2.2.2.2.2.2.1 hb.2.2.2.2.2.2.2.2.2.1
  cases h with
  | silent => exact hb
  | load aq rl base tvs asrc hok => exact loadRun_bnd hb (hsv _) (hr _ _ rfl)
  | store aq rl base data asrc vsrc ts _ _ _ _ =>
    have hts' := hts ts rfl
    refine acqPost_bnd (storeRun_bnd hb (hsv _) ?_ hts') hts'
    have := hsv asrc; have := hsv vsrc; omega
  | rmw aq rl base tvs data asrc vsrc ts _ _ _ hok _ _ _ =>
    have hts' := hts ts rfl
    exact amoPost_bnd (storeRun_bnd (loadRun_bnd hb (hsv _) (hr _ _ rfl)) (hsv _) hts' hts') hts'
  | amoLd aq base tvs asrc hok =>
    have h1 := loadRun_bnd (aq := aq) (rl := false) hb (hsv asrc) (hr _ _ rfl)
    obtain ⟨hc, h1, h2, h3, h4, h5, hf, hr', h6, h7, hR, _, h8, h9, h10⟩ := h1
    refine psB_intro hc h1 h2 h3 h4 h5 hf hr' h6 h7 hR (fun R hR' => ?_) h8 h9 h10
    simp only [Option.some.injEq] at hR'
    subst hR'
    exact tsList_bnd base tvs (hr _ _ rfl)
  | amoSt rl base data asrc vsrc ts R _ _ _ _ _ _ _ _ =>
    have hts' := hts ts rfl
    have h1 := amoPost_bnd (aq := R.rmAq) (storeRun_bnd (rl := rl) (base := base) (len := data.length) hb
      (hsv asrc) hts' hts') hts'
    obtain ⟨hc, h1, h2, h3, h4, h5, hf, hr', h6, h7, hR, _, h8, h9, h10⟩ := h1
    exact psB_intro hc h1 h2 h3 h4 h5 hf hr' h6 h7 hR (fun R hR' => by cases hR') h8 h9 h10
  | fence => exact fencePost_bnd hb
  | fenceI => exact fenceIPost_bnd hb
  | dev => exact hb
  | regW rd srcs =>
    obtain ⟨hc, h1, h2, h3, h4, h5, hf, hr', h6, h7, hR, hM, h8, h9, h10⟩ := hb
    refine psB_intro hc h1 h2 h3 h4 h5 hf (fun r => ?_) h6 h7 hR hM h8 h9 h10
    simp only [regv, getD_insert_nat]
    split
    · exact hsv srcs
    · exact hr' r
  | ctrl srcs =>
    have := hsv srcs
    obtain ⟨hc, h1, h2, h3, h4, h5, hf, hr', h6, h7, hR, hM, h8, h9, h10⟩ := hb
    refine psB_intro hc h1 h2 h3 h4 h5 hf hr' ?_ h7 hR hM h8 h9 h10
    simp only; omega
  | instr =>
    obtain ⟨hc, h1, h2, h3, h4, h5, hf, hr', h6, h7, hR, hM, h8, h9, h10⟩ := hb
    exact psB_intro hc h1 h2 h3 h4 h5 hf hr' h6 (Nat.zero_le _) hR (fun R hR' => by cases hR') h8 h9
      (Nat.zero_le _)
  | lr aq rl base tvs asrc hok =>
    have hrv := readView_le (aq := aq) (rl := rl) hb (hsv asrc) (hr _ _ rfl)
    have h1 := loadRun_bnd (aq := aq) (rl := rl) hb (hsv asrc) (hr _ _ rfl)
    obtain ⟨hc, h1, h2, h3, h4, h5, hf, hr', h6, h7, _, hM, h8, h9, h10⟩ := h1
    refine psB_intro hc h1 h2 h3 h4 h5 hf hr' h6 h7 (fun R hR' => ?_) hM h8 h9 h10
    simp only [Option.some.injEq] at hR'
    subst hR'
    exact ⟨tsList_bnd base tvs (hr _ _ rfl), hrv⟩
  | sc aq rl base data asrc vsrc ts R _ _ _ _ _ _ _ =>
    have hts' := hts ts rfl
    have h1 := acqPost_bnd (aq := aq) (storeRun_bnd (rl := rl) (base := base) (len := data.length) hb
      (hsv asrc) hts' hts') hts'
    obtain ⟨hc, h1, h2, h3, h4, h5, hf, hr', h6, h7, _, hM, h8, h9, h10⟩ := h1
    refine psB_intro hc h1 h2 h3 h4 h5 hf hr' h6 ?_ (fun R hR' => by cases hR') hM h8 h9 h10
    simp only [acqPost] at h7 ⊢
    omega
  | scFail =>
    obtain ⟨hc, h1, h2, h3, h4, h5, hf, hr', h6, h7, hR, hM, h8, h9, h10⟩ := hb
    exact psB_intro hc h1 h2 h3 h4 h5 hf hr' h6 h7 (fun R hR' => by cases hR') hM h8 h9 h10
  | fetch base tvs hok =>
    have hts' : bytesAll (fun _ t _ => t ≤ n) base tvs := hr _ _ rfl
    have e1 : bytesMax (fun _ t => t) base tvs ≤ n := bytesMax_le base tvs hts'
    have e2 : fetchView log i prom base tvs ≤ n := by
      unfold fetchView
      refine bytesMax_le base tvs (bytesAll_mono (fun _ t _ ht => ?_) base tvs hts')
      split <;> omega
    obtain ⟨hc, h1, h2, h3, h4, h5, hf, hr', h6, h7, hR, hM, h8, h9, h10⟩ := hb
    refine psB_intro hc h1 h2 h3 h4 h5 hf hr' h6 h7 hR hM h8 ?_ ?_
    · simp only; omega
    · simp only; omega
  | cmo k base len asrc ts _ _ _ _ =>
    exact cmoPost_bnd hb (hsv _) (hts ts rfl)

/-! ## 5. Field bookkeeping of the post-state functions -/

theorem fwdView_congr {ws ws' : PState} (h : ws'.wFwd = ws.wFwd) (aq : Bool) (a : Int) (t : Nat) :
    fwdView ws' aq a t = fwdView ws aq a t := by
  unfold fwdView; rw [h]

/-- A read byte is below its forwarded view, or is the hart's own latest store to that byte. -/
theorem le_fwdView (ws : PState) (aq : Bool) (a : Int) (t : Nat) :
    t ≤ fwdView ws aq a t ∨ ∃ vf, get? ws.wFwd a = some (t, vf) := by
  unfold fwdView
  cases h : get? ws.wFwd a with
  | none => exact .inl (Nat.le_refl _)
  | some p =>
    obtain ⟨tf, vf⟩ := p
    simp only
    by_cases e : t = tf
    · subst e; exact .inr ⟨vf, rfl⟩
    · rw [if_neg e]; exact .inl (Nat.le_refl _)

theorem loadBytes_keep (aq : Bool) (vpre : Nat) : ∀ (ws : PState) (a : Int) (tvs : List (Nat × BitVec 8)),
    (loadBytes aq vpre ws a tvs).wFwd = ws.wFwd ∧ (loadBytes aq vpre ws a tvs).wVwOld = ws.wVwOld ∧
    (loadBytes aq vpre ws a tvs).wIfr = ws.wIfr ∧ ws.wVrOld ≤ (loadBytes aq vpre ws a tvs).wVrOld ∧
    bytesAll (fun b t _ => fwdView ws aq b t ≤ (loadBytes aq vpre ws a tvs).wVrOld) a tvs
  | ws, _, [] => ⟨rfl, rfl, rfl, Nat.le_refl _, trivial⟩
  | ws, a, (t, _) :: r => by
    obtain ⟨i1, i2, i3, i4, i5⟩ := loadBytes_keep aq vpre (loadByte ws aq vpre a t) (a + 1) r
    have k1 : (loadByte ws aq vpre a t).wFwd = ws.wFwd := rfl
    simp only [loadBytes]
    refine ⟨by rw [i1]; rfl, by rw [i2]; rfl, by rw [i3]; rfl, ?_, ?_, ?_⟩
    · exact Nat.le_trans (by simp only [loadByte]; omega) i4
    · exact Nat.le_trans (by simp only [loadByte]; omega) i4
    · refine bytesAll_mono (fun b u _ hb => ?_) (a + 1) r i5
      rw [fwdView_congr k1] at hb
      exact hb

theorem loadRun_keep (ws : PState) (aq rl : Bool) (va : Nat) (base : Int) (tvs : List (Nat × BitVec 8)) :
    (loadRun ws aq rl va base tvs).wFwd = ws.wFwd ∧ (loadRun ws aq rl va base tvs).wVwOld = ws.wVwOld ∧
    (loadRun ws aq rl va base tvs).wIfr = ws.wIfr ∧ ws.wVrOld ≤ (loadRun ws aq rl va base tvs).wVrOld ∧
    bytesAll (fun a t _ => fwdView ws aq a t ≤ (loadRun ws aq rl va base tvs).wVrOld) base tvs := by
  obtain ⟨i1, i2, i3, i4, i5⟩ := loadBytes_keep aq (ldPre ws aq rl va) ws base tvs
  exact ⟨i1, i2, i3, i4, i5⟩

theorem storeBytes_keep : ∀ (ws : PState) (a : Int) (n ts fv : Nat),
    (storeBytes ws a n ts fv).wVrOld = ws.wVrOld ∧ (storeBytes ws a n ts fv).wVwOld = ws.wVwOld ∧
    (storeBytes ws a n ts fv).wIfr = ws.wIfr
  | ws, _, 0, _, _ => ⟨rfl, rfl, rfl⟩
  | ws, a, n + 1, ts, fv => by
    simp only [storeBytes]
    exact storeBytes_keep _ (a + 1) n ts fv

theorem storeRun_keep (ws : PState) (rl : Bool) (va fv : Nat) (base : Int) (n ts : Nat) :
    (storeRun ws rl va fv base n ts).wVrOld = ws.wVrOld ∧
    (storeRun ws rl va fv base n ts).wVwOld = max ws.wVwOld ts ∧ (storeRun ws rl va fv base n ts).wIfr = ws.wIfr := by
  obtain ⟨i1, i2, i3⟩ := storeBytes_keep ws base n ts fv
  unfold storeRun
  exact ⟨i1, by simp only; rw [i2], i3⟩

theorem cohRaise_keep : ∀ (ws : PState) (a : Int) (n ts : Nat),
    (cohRaise ws a n ts).wVrOld = ws.wVrOld ∧ (cohRaise ws a n ts).wVwOld = ws.wVwOld ∧
    (cohRaise ws a n ts).wIfr = ws.wIfr
  | ws, _, 0, _ => ⟨rfl, rfl, rfl⟩
  | ws, a, n + 1, ts => by
    simp only [cohRaise]
    exact cohRaise_keep _ (a + 1) n ts

/-- The read bytes of a load-like step are at most `vrOld` after it, or are an own fulfilled store (bounded by the
pre-state's self bound). -/
theorem reads_le_of {ws : PState} {B : Nat} (hb : psBounded ws B) {aq : Bool} {V : Nat} {base : Int}
    {tvs : List (Nat × BitVec 8)} (hv : bytesAll (fun a t _ => fwdView ws aq a t ≤ V) base tvs) :
    bytesAll (fun _ t _ => t ≤ max V B) base tvs := by
  refine bytesAll_mono (fun a t _ h => ?_) base tvs hv
  rcases le_fwdView ws aq a t with e | ⟨vf, e⟩
  · omega
  · have := (hb.2.2.2.2.2.2.1 a t vf e).1; omega

/-! ## 6. The self bound -/

/-- THE SELF BOUND (plan §4 "Why the segment fits"): every timestamp a step reads or fulfils is at most `bnd` of its
post-state; `bnd` grows; `psBounded ws (bnd ws)` is an invariant of every arm. -/
theorem memStep_self {img : Image} {M : List PMsg} {i : Nat} {prom : GSet Nat} {ws : PState} {l : PLabel}
    {ots : Option Nat} {ws' : PState} {prom' : GSet Nat} (h : memStep img M i prom ws l ots ws' prom')
    (hb : psBounded ws (bnd ws)) :
    bnd ws ≤ bnd ws' ∧ readsLe l (bnd ws') ∧ (∀ ts, ots = some ts → ts ≤ bnd ws') ∧ psBounded ws' (bnd ws') := by
  suffices H : bnd ws ≤ bnd ws' ∧ readsLe l (bnd ws') ∧ (∀ ts, ots = some ts → ts ≤ bnd ws') by
    exact ⟨H.1, H.2.1, H.2.2, memStep_bndN h (psBounded_mono hb H.1) H.2.1 H.2.2⟩
  have nor : ∀ n, readsLe l n → readsLe l n := fun _ h => h
  cases h with
  | silent => exact ⟨Nat.le_refl _, fun _ _ h => (by cases h), fun _ h => (by cases h)⟩
  | load aq rl base tvs asrc hok =>
    obtain ⟨_, i2, i3, i4, i5⟩ := loadRun_keep ws aq rl (srcsView ws asrc) base tvs
    have e2 : (loadRun ws aq rl (srcsView ws asrc) base tvs).wVwOld = ws.wVwOld := i2
    refine ⟨by unfold bnd; rw [i2, i3]; omega, fun b t hl => ?_, fun _ h => (by cases h)⟩
    simp only [labelReads, Option.some.injEq, Prod.mk.injEq] at hl
    obtain ⟨rfl, rfl⟩ := hl
    refine bytesAll_mono (fun _ _ _ h => ?_) _ _ (reads_le_of hb i5)
    unfold bnd at h ⊢; rw [i2, i3]; omega
  | lr aq rl base tvs asrc hok =>
    obtain ⟨_, i2, i3, i4, i5⟩ := loadRun_keep ws aq rl (srcsView ws asrc) base tvs
    refine ⟨by unfold bnd; simp only; rw [i2, i3]; omega, fun b t hl => ?_, fun _ h => (by cases h)⟩
    simp only [labelReads, Option.some.injEq, Prod.mk.injEq] at hl
    obtain ⟨rfl, rfl⟩ := hl
    refine bytesAll_mono (fun _ _ _ h => ?_) _ _ (reads_le_of hb i5)
    unfold bnd at h ⊢; simp only; rw [i2, i3]; omega
  | amoLd aq base tvs asrc hok =>
    obtain ⟨_, i2, i3, i4, i5⟩ := loadRun_keep ws aq false (srcsView ws asrc) base tvs
    refine ⟨by unfold bnd; simp only; rw [i2, i3]; omega, fun b t hl => ?_, fun _ h => (by cases h)⟩
    simp only [labelReads, Option.some.injEq, Prod.mk.injEq] at hl
    obtain ⟨rfl, rfl⟩ := hl
    refine bytesAll_mono (fun _ _ _ h => ?_) _ _ (reads_le_of hb i5)
    unfold bnd at h ⊢; simp only; rw [i2, i3]; omega
  | rmw aq rl base tvs data asrc vsrc ts _ _ _ hok _ _ _ =>
    obtain ⟨_, i2, i3, i4, i5⟩ := loadRun_keep ws aq false (srcsView ws asrc) base tvs
    obtain ⟨j1, j2, j3⟩ := storeRun_keep (loadRun ws aq false (srcsView ws asrc) base tvs) rl (srcsView ws asrc)
      ts base data.length ts
    refine ⟨?_, ?_, ?_⟩
    · simp only [bnd, amoPost, j1, j2, j3, i2, i3]; omega
    · intro b t hl
      simp only [labelReads, Option.some.injEq, Prod.mk.injEq] at hl
      obtain ⟨rfl, rfl⟩ := hl
      refine bytesAll_mono (fun _ _ _ h => ?_) _ _ (reads_le_of hb i5)
      simp only [bnd, amoPost, j1, j2, j3, i2, i3]
      unfold bnd at h; omega
    · intro t h; cases h; simp only [bnd, amoPost, j1, j2, j3, i2, i3]; omega
  | store aq rl base data asrc vsrc ts _ _ _ _ =>
    obtain ⟨j1, j2, j3⟩ := storeRun_keep ws rl (srcsView ws asrc) (max (srcsView ws asrc) (srcsView ws vsrc))
      base data.length ts
    refine ⟨?_, fun _ _ h => (by cases h), ?_⟩
    · simp only [bnd, acqPost, j1, j2, j3]; omega
    · intro t h; cases h; simp only [bnd, acqPost, j1, j2, j3]; omega
  | amoSt rl base data asrc vsrc ts R _ _ _ _ _ _ _ _ =>
    obtain ⟨j1, j2, j3⟩ := storeRun_keep ws rl (srcsView ws asrc) ts base data.length ts
    refine ⟨?_, fun _ _ h => (by cases h), ?_⟩
    · simp only [bnd, amoPost, j1, j2, j3]; omega
    · intro t h; cases h; simp only [bnd, amoPost, j1, j2, j3]; omega
  | sc aq rl base data asrc vsrc ts R _ _ _ _ _ _ _ =>
    obtain ⟨j1, j2, j3⟩ := storeRun_keep ws rl (srcsView ws asrc) ts base data.length ts
    refine ⟨?_, fun _ _ h => (by cases h), ?_⟩
    · simp only [bnd, acqPost, j1, j2, j3]; omega
    · intro t h; cases h; simp only [bnd, acqPost, j1, j2, j3]; omega
  | cmo k base len asrc ts _ _ _ _ =>
    obtain ⟨j1, j2, j3⟩ := cohRaise_keep ws base len ts
    refine ⟨?_, fun _ _ h => (by cases h), ?_⟩
    · simp only [bnd, cmoPost, j1, j2, j3]; omega
    · intro t h; cases h; simp only [bnd, cmoPost, j1, j2, j3]; omega
  | fence pr pw sr sw => exact ⟨Nat.le_refl _, fun _ _ h => (by cases h), fun _ h => (by cases h)⟩
  | fenceI => exact ⟨Nat.le_refl _, fun _ _ h => (by cases h), fun _ h => (by cases h)⟩
  | dev => exact ⟨Nat.le_refl _, fun _ _ h => (by cases h), fun _ h => (by cases h)⟩
  | regW => exact ⟨Nat.le_refl _, fun _ _ h => (by cases h), fun _ h => (by cases h)⟩
  | ctrl => exact ⟨Nat.le_refl _, fun _ _ h => (by cases h), fun _ h => (by cases h)⟩
  | instr => exact ⟨Nat.le_refl _, fun _ _ h => (by cases h), fun _ h => (by cases h)⟩
  | scFail => exact ⟨Nat.le_refl _, fun _ _ h => (by cases h), fun _ h => (by cases h)⟩
  | fetch base tvs hok =>
    refine ⟨?_, fun b t hl => ?_, fun _ h => (by cases h)⟩
    · simp only [bnd]; omega
    simp only [labelReads, Option.some.injEq, Prod.mk.injEq] at hl
    obtain ⟨rfl, rfl⟩ := hl
    have key : ∀ (a : Int) (r : List (Nat × BitVec 8)), bytesAll (fun _ t _ => t ≤ bytesMax (fun _ t => t) a r) a r := by
      intro a r
      induction r generalizing a with
      | nil => trivial
      | cons tv r ih =>
        obtain ⟨t, v⟩ := tv
        refine ⟨by simp only [bytesMax]; omega, bytesAll_mono (fun _ _ _ h => ?_) (a + 1) r (ih (a + 1))⟩
        simp only [bytesMax]; omega
    exact bytesAll_mono (fun _ _ _ h => by simp only [bnd]; omega) _ _ (key _ _)

/-! ## 7. Write-step facts -/

/-- Every write step's pre-view is below its timestamp (EXT), and its message is the agent's. -/
theorem memStep_write {img : Image} {M : List PMsg} {i : Nat} {prom : GSet Nat} {ws : PState} {l : PLabel}
    {ts : Nat} {ws' : PState} {prom' : GSet Nat} (h : memStep img M i prom ws l (some ts) ws' prom') :
    (∃ pv, wrPre ws l = some pv ∧ pv < ts) ∧ ∃ m, M[ts - 1]? = some m ∧ m.tid = some i := by
  cases h with
  | store aq rl base data asrc vsrc ts _ hm _ hpv => exact ⟨⟨_, rfl, hpv⟩, _, hm, rfl⟩
  | rmw aq rl base tvs data asrc vsrc ts _ _ hm _ _ _ hpv => exact ⟨⟨_, rfl, hpv⟩, _, hm, rfl⟩
  | amoSt rl base data asrc vsrc ts R _ _ _ _ hm _ _ hpv => exact ⟨⟨_, rfl, hpv⟩, _, hm, rfl⟩
  | sc aq rl base data asrc vsrc ts R hR _ hm _ _ _ hpv =>
    exact ⟨⟨_, by simp only [wrPre, hR, Option.map_some], hpv⟩, _, hm, rfl⟩
  | cmo k base len asrc ts _ hm _ hpv => exact ⟨⟨_, rfl, hpv⟩, _, hm, rfl⟩

/-- Only write arms carry a timestamp. -/
theorem memStep_none {img : Image} {M : List PMsg} {i : Nat} {prom : GSet Nat} {ws : PState} {l : PLabel}
    {ws' : PState} {prom' : GSet Nat} (h : memStep img M i prom ws l none ws' prom') : wrPre ws l = none := by
  cases h <;> rfl

theorem wrState_le (ws : PState) (l : PLabel) :
    ws.wVrOld ≤ (wrState ws l).wVrOld ∧ ws.wVwOld ≤ (wrState ws l).wVwOld := by
  cases l with
  | LRmw aq rl base tvs data asrc vsrc =>
    obtain ⟨_, i2, _, i4, _⟩ := loadRun_keep ws aq false (srcsView ws asrc) base tvs
    exact ⟨i4, by simp only [wrState]; rw [i2]; exact Nat.le_refl _⟩
  | _ => exact ⟨Nat.le_refl _, Nat.le_refl _⟩

/-- A RELEASE-CLASS write at `ts` has `vrOld ⊔ vwOld < ts` in the state before it. -/
theorem relClass_lt {img : Image} {M : List PMsg} {i : Nat} {prom : GSet Nat} {ws : PState} {l : PLabel}
    {ts : Nat} {ws' : PState} {prom' : GSet Nat} (h : memStep img M i prom ws l (some ts) ws' prom')
    (hr : relClass ws l) : max ws.wVrOld ws.wVwOld < ts := by
  obtain ⟨⟨pv, hpv, hlt⟩, _⟩ := memStep_write h
  obtain ⟨pv', hpv', hle⟩ := hr
  rw [hpv] at hpv'
  cases hpv'
  have := wrState_le ws l
  omega

/-- A step with no timestamp is not release-class. -/
theorem not_relClass_none {img : Image} {M : List PMsg} {i : Nat} {prom : GSet Nat} {ws : PState} {l : PLabel}
    {ws' : PState} {prom' : GSet Nat} (h : memStep img M i prom ws l none ws' prom') : ¬ relClass ws l := by
  rintro ⟨pv, hpv, _⟩
  rw [memStep_none h] at hpv
  cases hpv

/-- `vwOld` grows, and absorbs a fulfilled timestamp. -/
theorem memStep_vw {img : Image} {M : List PMsg} {i : Nat} {prom : GSet Nat} {ws : PState} {l : PLabel}
    {ots : Option Nat} {ws' : PState} {prom' : GSet Nat} (h : memStep img M i prom ws l ots ws' prom') :
    ws.wVwOld ≤ ws'.wVwOld ∧ ∀ ts, ots = some ts → ts ≤ ws'.wVwOld := by
  cases h with
  | load aq rl base tvs asrc =>
    obtain ⟨_, i2, _⟩ := loadRun_keep ws aq rl (srcsView ws asrc) base tvs
    exact ⟨by rw [show (loadRun ws aq rl (srcsView ws asrc) base tvs).wVwOld = ws.wVwOld from i2]; exact
      Nat.le_refl _, fun _ h => (by cases h)⟩
  | lr aq rl base tvs asrc =>
    obtain ⟨_, i2, _⟩ := loadRun_keep ws aq rl (srcsView ws asrc) base tvs
    exact ⟨by simp only; rw [i2]; exact Nat.le_refl _, fun _ h => (by cases h)⟩
  | amoLd aq base tvs asrc =>
    obtain ⟨_, i2, _⟩ := loadRun_keep ws aq false (srcsView ws asrc) base tvs
    exact ⟨by simp only; rw [i2]; exact Nat.le_refl _, fun _ h => (by cases h)⟩
  | rmw aq rl base tvs data asrc vsrc ts =>
    obtain ⟨_, i2, _⟩ := loadRun_keep ws aq false (srcsView ws asrc) base tvs
    obtain ⟨_, j2, _⟩ := storeRun_keep (loadRun ws aq false (srcsView ws asrc) base tvs) rl (srcsView ws asrc)
      ts base data.length ts
    refine ⟨?_, fun t h => ?_⟩
    · simp only [amoPost]; rw [j2, i2]; omega
    · cases h; simp only [amoPost]; rw [j2]; omega
  | store aq rl base data asrc vsrc ts =>
    obtain ⟨_, j2, _⟩ := storeRun_keep ws rl (srcsView ws asrc) (max (srcsView ws asrc) (srcsView ws vsrc))
      base data.length ts
    refine ⟨?_, fun t h => ?_⟩
    · simp only [acqPost]; rw [j2]; omega
    · cases h; simp only [acqPost]; rw [j2]; omega
  | amoSt rl base data asrc vsrc ts R =>
    obtain ⟨_, j2, _⟩ := storeRun_keep ws rl (srcsView ws asrc) ts base data.length ts
    refine ⟨?_, fun t h => ?_⟩
    · simp only [amoPost]; rw [j2]; omega
    · cases h; simp only [amoPost]; rw [j2]; omega
  | sc aq rl base data asrc vsrc ts R =>
    obtain ⟨_, j2, _⟩ := storeRun_keep ws rl (srcsView ws asrc) ts base data.length ts
    refine ⟨?_, fun t h => ?_⟩
    · simp only [acqPost]; rw [j2]; omega
    · cases h; simp only [acqPost]; rw [j2]; omega
  | cmo k base len asrc ts =>
    obtain ⟨_, j2, _⟩ := cohRaise_keep ws base len ts
    refine ⟨?_, fun t h => ?_⟩
    · simp only [cmoPost]; rw [j2]; omega
    · cases h; simp only [cmoPost]; rw [j2]; omega
  | _ => exact ⟨Nat.le_refl _, fun _ h => (by cases h)⟩

end Weak.Prom.Nfr
