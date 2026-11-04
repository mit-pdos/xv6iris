/-
Weak/Prom: **E-c — track (b)'s NF_R lemma for the A/D variant (AdMachine.lean), fix (i), NO premise** (G4 deciding
experiment E-c, owner ruling [OWN.P13]; G4-review2.md §6 B-1′, §7; plan rev 7 §4 "A fourth kind, a write: A/D
messages").

The difficulty (plan §4, PROGRESS-Eb.md "A/D"): an A/D update is a WRITE with no view effect, so its timestamp `ts`
is not bounded by the hart's next release `r` — `bndF`, the release class and the self bound say nothing about it.
In the NF schedule a hart's release-free segment runs against the prefix `M[..r)`, where `M[ts]` is absent.

* FIX (ii) ("defer the A/D step until the log reaches `ts`") is IMPOSSIBLE under trace equality: the A/D step is in
  the hart's own label stream.  Counterexample (2 messages, one hart): `ad p` fulfilling `ts = 2`, then a release
  store `x` at `r = 1` (valid: the A/D write raises no view, so the release pre-view stays 0 < 1).  An NF run must
  fulfil `r = 1` in place at log length 0, after the hart's `ad` step (trace order), so the `ad` step runs at log
  length 0 < 2: it cannot be deferred without reordering the hart's trace (the plan's "commutation lemma ruled
  out" finding, made concrete).
* FIX (i), taken here: in the NF run shape (`nfStepsV`) an A/D step whose timestamp is ABOVE the prefix is
  admissible against the FINAL memory `M` (constructor `adF`, the A/D analogue of E-b's prophecy-fed fetch `fet`);
  its post (no view effect) leaves the hart's cut promise set unchanged; and when the log reaches `ts` the agent
  appends `M[ts]` WITHOUT a promise owner (constructor `promF`, "appended as already fulfilled").  NO bookkeeping
  is added to the configuration: the NF run's `promF`/`prom` choice is made by the scheduler from the solo runs.
  The schedule invariant changes in ONE clause: an own message above the prefix is still promised OR is an A/D
  message (`hartInvV`, `adAt`).

Checked (the review's claim, G4-review2.md §5.5 "no read in the segment can depend on the deferred write (it would
raise `vrOld` above `r`)"): TRUE for every explicit read and every log window of the segment — `memStep_selfF` bounds
them by `bndF < r` unchanged, since the A/D arm moves no view.  Two reads are NOT so bounded and are replayed against
`M` instead: fetches (E-b's `fet`) and the A/D update's own implicit read (`adF`, its sources are below `ts` only).
The fetch view's own-store exemption must not count a pre-fulfilled A/D write (AdMachine.lean `ownDoneV`), and with
that `fetchViewV_cut` holds.

`nfRAd` / `nfRAd_pre`: EVERY valid run of the variant (`D = Unit`), NO premise, has an NF run with the same final
configuration and per-hart traces.  No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Prom.AdMachine

namespace Weak.Prom.Ad

open MachCSL MachCSL.Stdpp Iris.Std
open Weak (Image Dsrc)
open Weak.Prom Weak.Prom.Nfr Weak.Prom.Nfr.F
open PLabel

/-! ## 1. Step facts -/

section steps

variable {img : Image} {L M : List PMsg} {i : Nat} {prom : GSet Nat} {ws : PState} {l : VLabel}
  {ots : Option Nat} {ws' : PState} {prom' : GSet Nat}

theorem memStepV_prom (h : memStepV img L i prom ws l ots ws' prom') :
    (ots = none ∧ prom' = prom) ∨ (∃ ts, ots = some ts ∧ ts ∈ prom ∧ prom' = prom \ {ts}) := by
  cases h with
  | v2 _ _ _ _ hm _ => exact memStep_prom hm
  | fetch => exact .inl ⟨rfl, rfl⟩
  | ad _ _ _ ts _ _ hts => exact .inr ⟨ts, rfl, hts, rfl⟩

theorem memStepV_vw (h : memStepV img L i prom ws l ots ws' prom') : ws.wVwOld ≤ ws'.wVwOld := by
  cases h with
  | v2 _ _ _ _ hm _ => exact (memStep_vw hm).1
  | fetch => exact Nat.le_refl _
  | ad => exact Nat.le_refl _

/-- `bndF` grows and `fwdB` is kept along every step (the A/D and fetch arms move neither). -/
theorem memStepV_bndF (h : memStepV img L i prom ws l ots ws' prom') (hb : fwdB ws) :
    bndF ws ≤ bndF ws' ∧ fwdB ws' := by
  cases h with
  | v2 _ _ _ _ hm _ => have := memStep_selfF hm hb; exact ⟨this.1, this.2.2.2⟩
  | fetch => exact ⟨Nat.le_refl _, hb⟩
  | ad => exact ⟨Nat.le_refl _, hb⟩

theorem memStepV_v_inv {l0 : PLabel} (h : memStepV img L i prom ws (.v l0) ots ws' prom') (hnf : ¬ isFetch l0) :
    memStep img L i prom ws l0 ots ws' prom' := by
  cases h with
  | v2 _ _ _ _ hm _ => exact hm
  | fetch base tvs _ => exact (‹¬ isFetch (LIFetch base tvs)› ⟨base, tvs, rfl⟩).elim

theorem memStepV_fetch_inv {b : Int} {tvs : List (Nat × BitVec 8)}
    (h : memStepV img L i prom ws (.v (LIFetch b tvs)) ots ws' prom') :
    bytesAll (fetchByteOk img L ws) b tvs ∧ ots = none ∧ ws' = fetchPostV L i prom ws b tvs ∧ prom' = prom := by
  cases h with
  | v2 _ _ _ _ _ hnf => exact (hnf ⟨b, tvs, rfl⟩).elim
  | fetch _ _ hok => exact ⟨hok, rfl, rfl, rfl⟩

theorem memStepV_ad_inv {b : Int} {tvs : List (Nat × BitVec 8)} {d : List (BitVec 8)}
    (h : memStepV img L i prom ws (.ad b tvs d) ots ws' prom') :
    ∃ ts, ots = some ts ∧ ws' = ws ∧ prom' = prom \ {ts} ∧ tvs.length = d.length ∧ 0 < ts ∧ ts ∈ prom ∧
      L[ts - 1]? = some ⟨b, d, some i, PClass.ad⟩ ∧ bytesAll (adReadOk img L ts) b tvs := by
  cases h with
  | ad _ _ _ ts hlen h0 hts hm hrd => exact ⟨ts, rfl, rfl, rfl, hlen, h0, hts, hm, hrd⟩

/-- A v2 write step is a variant step. -/
theorem v2V {l0 : PLabel} {r : Nat} (h : memStep img L i prom ws l0 (some r) ws' prom') :
    memStepV img L i prom ws (.v l0) (some r) ws' prom' :=
  .v2 _ _ _ _ _ _ h (fun ⟨_, _, e⟩ => by subst e; cases h)

/-- The A/D read is append-stable and restriction-stable below `ts`. -/
theorem adReadOk_iff (hpre : L <+: M) {ts : Nat} (hts : ts ≤ L.length) (a : Int) (t : Nat) (v : BitVec 8) :
    adReadOk img M ts a t v ↔ adReadOk img L ts a t v := by
  unfold adReadOk
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨by rw [← memByte_ext hpre (by omega)]; exact h1, h2, fun hw => h3 ((writesIn_ext hpre (by omega)).2 hw)⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨by rw [memByte_ext hpre (by omega)]; exact h1, h2, fun hw => h3 ((writesIn_ext hpre (by omega)).1 hw)⟩

theorem ownDoneV_ext {P : GSet Nat} {t : Nat} (h : L <+: M) (ht : t ≤ L.length)
    (hP : ∀ t, t ≤ L.length → (t ∈ P ↔ t ∈ prom)) : ownDoneV M i P t = ownDoneV L i prom t := by
  unfold ownDoneV
  rw [ownDone_ext h ht hP]
  rcases Nat.eq_zero_or_pos t with h0 | h0
  · subst h0
    have : ownDone L i prom 0 = false := by unfold ownDone; cases L[0 - 1]? <;> simp
    rw [this]; simp
  · rw [prefix_getElem? h (by omega)]

theorem fetchViewV_ext {P : GSet Nat} {base : Int} {tvs : List (Nat × BitVec 8)} (h : L <+: M)
    (hts : bytesAll (fun _ t _ => t ≤ L.length) base tvs) (hP : ∀ t, t ≤ L.length → (t ∈ P ↔ t ∈ prom)) :
    fetchViewV M i P base tvs = fetchViewV L i prom base tvs := by
  unfold fetchViewV
  refine bytesMax_congr base tvs (bytesAll_mono (fun a t _ ht => ?_) base tvs hts)
  rw [ownDoneV_ext h ht hP]

/-- THE FETCH VIEW OF A REPLAYED FETCH (E-b's `fetchView_cut` for `ownDoneV`): an own message above the prefix is
still promised or is an A/D message — neither is exempt. -/
theorem fetchViewV_cut {P Q : GSet Nat} (hpre : L <+: M) (hQ : ∀ t, t ∈ Q ↔ t ∈ P ∧ t ≤ L.length)
    (hfut : ∀ t, L.length < t → ownTs M i t → t ∈ P ∨ adAt M t) (base : Int) (tvs : List (Nat × BitVec 8)) :
    fetchViewV M i P base tvs = fetchViewV L i Q base tvs := by
  unfold fetchViewV
  refine bytesMax_congr base tvs (bytesAll_all (fun a t _ => ?_) base tvs)
  by_cases ht : t ≤ L.length
  · rw [ownDoneV_ext hpre ht (fun t' ht' => by rw [hQ t']; exact ⟨fun h => ⟨h, ht'⟩, fun h => h.1⟩)]
  · have h1 : ownDoneV L i Q t = false := by
      unfold ownDoneV ownDone; rw [List.getElem?_eq_none (by omega)]; rfl
    have h2 : ownDoneV M i P t = false := by
      unfold ownDoneV ownDone
      cases hm : M[t - 1]? with
      | none => rfl
      | some m =>
        by_cases ht' : m.tid = some i
        · rcases hfut t (by omega) ⟨m, hm, ht'⟩ with hp | ⟨m', hm', hc⟩
          · simp [hp]
          · rw [hm] at hm'; cases hm'; simp [hc]
        · simp [ht']
    rw [h1, h2]

theorem fetchPostV_bnd {base : Int} {tvs : List (Nat × BitVec 8)} (hok : bytesAll (fetchByteOk img L ws) base tvs)
    (hb : psBounded ws L.length) : psBounded (fetchPostV L i prom ws base tvs) L.length := by
  have hts : bytesAll (fun _ t _ => t ≤ L.length) base tvs :=
    bytesAll_mono (fun _ _ _ hp => memByte_le hp.1) base tvs hok
  have e1 : bytesMax (fun _ t => t) base tvs ≤ L.length := bytesMax_le base tvs hts
  have e2 : fetchViewV L i prom base tvs ≤ L.length := by
    unfold fetchViewV
    refine bytesMax_le base tvs (bytesAll_mono (fun _ t _ ht => ?_) base tvs hts)
    split <;> omega
  obtain ⟨hc, h1, h2, h3, h4, h5, hf, hr, h6, h7, hR, hM, h8, h9, h10⟩ := hb
  refine psB_intro hc h1 h2 h3 h4 h5 hf hr h6 h7 hR hM h8 ?_ ?_
  · simp only [fetchPostV]; omega
  · simp only [fetchPostV]; omega

/-- Every arm keeps the bounds (MachWf.lean `memStep_bnd`). -/
theorem memStepV_bnd (h : memStepV img L i prom ws l ots ws' prom') (hb : psBounded ws L.length)
    (hw : promWf L i prom) : psBounded ws' L.length ∧ promWf L i prom' := by
  cases h with
  | v2 _ _ _ _ hm _ => exact memStep_bnd hm hb hw
  | fetch _ _ hok => exact ⟨fetchPostV_bnd hok hb, hw⟩
  | ad _ _ _ ts => exact ⟨hb, promWf_diff ts hw⟩

/-- THE ARM LEMMA (MachFactor.lean `memStep_extend`) for the variant. -/
theorem memStepV_extend (P : GSet Nat) (Q : Nat → Prop) (h : memStepV img L i prom ws l ots ws' prom')
    (hpre : L <+: M) (hb : psBounded ws L.length) (hw : promWf L i prom)
    (hP : ∀ t, t ∈ P ↔ t ∈ prom ∨ (L.length < t ∧ Q t)) :
    ∃ P', memStepV img M i P ws l ots ws' P' ∧ ∀ t, t ∈ P' ↔ t ∈ prom' ∨ (L.length < t ∧ Q t) := by
  cases h with
  | v2 _ _ _ _ hm hnf =>
    obtain ⟨P', h1, h2⟩ := memStep_extend P Q hm hpre hb hw hP
    exact ⟨P', .v2 _ _ _ _ _ _ h1 hnf, h2⟩
  | fetch base tvs hok =>
    have hts : bytesAll (fun _ t _ => t ≤ L.length) base tvs :=
      bytesAll_mono (fun _ _ _ hp => memByte_le hp.1) base tvs hok
    have hifl : ws.wIfl ≤ L.length := hb.2.2.2.2.2.2.2.2.2.2.2.2.1
    have hok' : bytesAll (fetchByteOk img M ws) base tvs := by
      refine bytesAll_mono (fun a t v hp => ?_) base tvs hok
      obtain ⟨h1, h2⟩ := hp
      exact ⟨by rw [memByte_ext hpre (memByte_le h1)]; exact h1, by rw [writesIn_ext hpre hifl]; exact h2⟩
    have hlow : ∀ t, t ≤ L.length → (t ∈ P ↔ t ∈ prom) := by
      intro t ht
      rw [hP t]
      constructor
      · rintro (h1 | h1)
        · exact h1
        · omega
      · exact .inl
    refine ⟨P, ?_, hP⟩
    have e : fetchPostV M i P ws base tvs = fetchPostV L i prom ws base tvs := by
      unfold fetchPostV; rw [fetchViewV_ext hpre hts hlow]
    rw [← e]
    exact .fetch _ _ _ _ hok'
  | ad base tvs data ts hlen h0 hts hm hrd =>
    have hts' := (hw ts hts).2.1
    refine ⟨P \ {ts}, .ad _ _ _ _ _ _ hlen h0 ((hP ts).2 (.inl hts))
      (by rw [prefix_getElem? hpre (by omega)]; exact hm)
      (bytesAll_mono (fun a t v hp => (adReadOk_iff hpre hts' a t v).2 hp) base tvs hrd), fun t => ?_⟩
    rw [elemOfDifference, elemOfDifference, hP t, elemOfSingleton]
    constructor
    · rintro ⟨h1 | h1, h2⟩
      · exact .inl ⟨h1, h2⟩
      · exact .inr h1
    · rintro (⟨h1, h2⟩ | h1)
      · exact ⟨.inl h1, h2⟩
      · exact ⟨.inr h1, by have := h1.1; omega⟩

end steps

/-! ## 2. Runs of the variant: bounds and solo projection -/

section runs

variable {P : Type} {pstep : P → Unit → VLabel → P → Unit → Prop}

theorem pmStepV_wf {c c' : PCfg P Unit} {e : VEvt} (h : pmStepV pstep c e c') (hw : runWf c) : runWf c' := by
  obtain ⟨hcfg, hlog⟩ := hw
  cases h with
  | promise i ag m hag hnt htid =>
    have hi : i < c.pcAgs.length := (List.getElem?_eq_some_iff.1 hag).1
    refine ⟨fun j ag' hj => ?_, fun m' hm' => ?_⟩
    · simp only at hj
      rcases getElem?_set_of hj with ⟨hij, hb, _⟩ | ⟨hij, hj'⟩
      · subst hij hb
        obtain ⟨h1, h2⟩ := hcfg i ag hag
        refine ⟨psBounded_mono h1 (by simp), fun t ht => ?_⟩
        simp only at ht
        rcases elemOfUnion.1 ht with ht | ht
        · rw [elemOfSingleton] at ht
          subst ht
          refine ⟨by omega, by simp, m, by simp, htid⟩
        · exact promWf_append m h2 t ht
      · obtain ⟨h1, h2⟩ := hcfg j ag' hj'
        exact ⟨psBounded_mono h1 (by simp), promWf_append m h2⟩
    · simp only [List.length_set]
      simp only [List.mem_append, List.mem_singleton] at hm'
      rcases hm' with hm' | hm'
      · exact hlog m' hm'
      · subst hm'; exact ⟨hnt, i, htid, hi⟩
  | state i ag l ots st' d' ws' prom' hag hp hm =>
    refine ⟨fun j ag' hj => ?_, fun m' hm' => ?_⟩
    · simp only at hj ⊢
      rcases getElem?_set_of hj with ⟨hij, hb, _⟩ | ⟨hij, hj'⟩
      · subst hij hb
        obtain ⟨h1, h2⟩ := hcfg i ag hag
        exact memStepV_bnd hm h1 h2
      · exact hcfg j ag' hj'
    · simp only [List.length_set]
      exact hlog m' hm'

theorem pmStepsV_wf {c c' : PCfg P Unit} {evs : List VEvt} (h : pmStepsV pstep c evs c') (hw : runWf c) :
    runWf c' := by
  induction h with
  | refl => exact hw
  | step _ _ _ _ _ h1 _ ih => exact ih (pmStepV_wf h1 hw)

theorem pmStepV_inv {c c' : PCfg P Unit} {e : VEvt} (h : pmStepV pstep c e c') :
    c'.pcImg = c.pcImg ∧ c.pcLog <+: c'.pcLog ∧ c'.pcAgs.length = c.pcAgs.length ∧
      ∀ j l ots, e = .st j l ots → j < c.pcAgs.length := by
  cases h with
  | promise => exact ⟨rfl, List.prefix_append _ _, by simp, fun _ _ _ e => by cases e⟩
  | state i ag l ots st' d' ws' prom' hag =>
    exact ⟨rfl, List.prefix_refl _, by simp, fun j _ _ e => by
      cases e; exact (List.getElem?_eq_some_iff.1 hag).1⟩

theorem pmStepsV_inv {c c' : PCfg P Unit} {evs : List VEvt} (h : pmStepsV pstep c evs c') :
    c'.pcImg = c.pcImg ∧ c.pcLog <+: c'.pcLog ∧ c'.pcAgs.length = c.pcAgs.length ∧
      ∀ hh, c.pcAgs.length ≤ hh → traceOfV hh evs = [] := by
  induction h with
  | refl => exact ⟨rfl, List.prefix_refl _, rfl, fun _ _ => rfl⟩
  | step c0 c1 c2 e es h1 _ ih =>
    obtain ⟨a1, a2, a3, a4⟩ := pmStepV_inv h1
    obtain ⟨b1, b2, b3, b4⟩ := ih
    refine ⟨b1.trans a1, a2.trans b2, b3.trans a3, fun hh hle => ?_⟩
    cases e with
    | prom => exact b4 hh (by omega)
    | st j l ots =>
      have := a4 j l ots rfl
      simp only [traceOfV, show j ≠ hh by omega, if_false]
      exact b4 hh (by omega)

theorem traceOfV_append (h : Nat) : ∀ (a b : List VEvt), traceOfV h (a ++ b) = traceOfV h a ++ traceOfV h b
  | [], _ => rfl
  | .prom _ _ :: a, b => by simp only [List.cons_append, traceOfV]; exact traceOfV_append h a b
  | .st i l o :: a, b => by
    simp only [List.cons_append, traceOfV]
    split <;> simp [traceOfV_append h a b]

end runs

/-! ## 3. Solo runs of the variant -/

section soloq

variable {P : Type} (pstep : P → Unit → VLabel → P → Unit → Prop) (img : Image) (M : List PMsg) (i : Nat)

/-- A solo run of agent `i` against `M` whose every step satisfies `Q` (NfrRun.lean `soloQ` over `VLabel`). -/
inductive soloQV (Q : PState → VLabel → Option Nat → Prop) :
    P × PState × GSet Nat → List (VLabel × Option Nat) → P × PState × GSet Nat → Prop
  | refl (x : P × PState × GSet Nat) : soloQV Q x [] x
  | step (x : P × PState × GSet Nat) (l : VLabel) (ots : Option Nat) (p' : P) (ws' : PState) (prom' : GSet Nat)
      (tr : List (VLabel × Option Nat)) (y : P × PState × GSet Nat) :
      Q x.2.1 l ots → pstep x.1 () l p' () → memStepV img M i x.2.2 x.2.1 l ots ws' prom' →
      soloQV Q (p', ws', prom') tr y → soloQV Q x ((l, ots) :: tr) y

end soloq

/-- The release class on variant labels: the A/D update is never release-class. -/
def RCV (RC : PState → PLabel → Prop) (ws : PState) : VLabel → Prop
  | .v l => RC ws l
  | .ad .. => False

/-- No side condition. -/
def QTV : PState → VLabel → Option Nat → Prop := fun _ _ _ => True

/-- "Every `RC` write is above `n`". -/
def QGV (RC : PState → PLabel → Prop) (n : Nat) : PState → VLabel → Option Nat → Prop :=
  fun ws l ots => RCV RC ws l → ∀ r, ots = some r → n < r

/-- Not in `RC`. -/
def QNRV (RC : PState → PLabel → Prop) : PState → VLabel → Option Nat → Prop := fun ws l _ => ¬ RCV RC ws l

section soloLemmas

variable {P : Type} {pstep : P → Unit → VLabel → P → Unit → Prop} {img : Image} {M : List PMsg} {i : Nat}
variable {RC : PState → PLabel → Prop}

theorem rcV_inv (hRC : RCOk RC) {prom : GSet Nat} {ws : PState} {l : VLabel} {ots : Option Nat} {ws' : PState}
    {prom' : GSet Nat} (h : memStepV img M i prom ws l ots ws' prom') (hr : RCV RC ws l) :
    ∃ l0, l = .v l0 ∧ memStep img M i prom ws l0 ots ws' prom' := by
  cases h with
  | v2 l0 _ _ _ hm _ => exact ⟨l0, rfl, hm⟩
  | fetch base tvs hok => exact absurd hr (hRC.none_ (memStep.fetch (i := i) prom ws base tvs hok))
  | ad => exact hr.elim

theorem soloQV_mono {Q1 Q2 : PState → VLabel → Option Nat → Prop} (hQ : ∀ ws l ots, Q1 ws l ots → Q2 ws l ots) :
    ∀ {x y τ}, soloQV pstep img M i Q1 x τ y → soloQV pstep img M i Q2 x τ y := by
  intro x y τ h
  induction h with
  | refl => exact .refl _
  | step x l ots p' ws' prom' tr y hq hp hm _ ih => exact .step _ _ _ _ _ _ _ _ (hQ _ _ _ hq) hp hm ih

theorem soloQV_append {Q : PState → VLabel → Option Nat → Prop} :
    ∀ {x z y τ1 τ2}, soloQV pstep img M i Q x τ1 z → soloQV pstep img M i Q z τ2 y →
      soloQV pstep img M i Q x (τ1 ++ τ2) y := by
  intro x z y τ1 τ2 h1 h2
  induction h1 with
  | refl => exact h2
  | step x l ots p' ws' prom' tr y' hq hp hm _ ih => exact .step _ _ _ _ _ _ _ _ hq hp hm (ih h2)

theorem soloQV_raiseF (hRC : RCOk RC) {n : Nat} : ∀ {x y τ}, soloQV pstep img M i QTV x τ y →
    n ≤ x.2.1.wVwOld → soloQV pstep img M i (QGV RC n) x τ y := by
  intro x y τ h
  induction h with
  | refl => intro _; exact .refl _
  | step x l ots p' ws' prom' tr y _ hp hm _ ih =>
    intro hn
    refine .step _ _ _ _ _ _ _ _ (fun hr r hots => ?_) hp hm (ih (Nat.le_trans hn (memStepV_vw hm)))
    subst hots
    obtain ⟨l0, e, hm0⟩ := rcV_inv hRC hm hr
    subst e
    have := hRC.lt_ hm0 hr
    omega

theorem soloQV_QN_QG {n : Nat} {x y τ} (h : soloQV pstep img M i (QNRV RC) x τ y) :
    soloQV pstep img M i (QGV RC n) x τ y :=
  soloQV_mono (fun _ _ _ hq hr => absurd hr hq) h

theorem soloQV_QG_anti {n m : Nat} (hmn : m ≤ n) {x y τ} (h : soloQV pstep img M i (QGV RC n) x τ y) :
    soloQV pstep img M i (QGV RC m) x τ y :=
  soloQV_mono (fun _ _ _ hq hr r hr' => by have := hq hr r hr'; omega) h

theorem soloQV_bndF {Q : PState → VLabel → Option Nat → Prop} :
    ∀ {x y τ}, soloQV pstep img M i Q x τ y → fwdB x.2.1 → bndF x.2.1 ≤ bndF y.2.1 ∧ fwdB y.2.1 := by
  intro x y τ h
  induction h with
  | refl => intro hb; exact ⟨Nat.le_refl _, hb⟩
  | step x l ots p' ws' prom' tr y _ _ hm _ ih =>
    intro hb
    have hs := memStepV_bndF hm hb
    have := ih hs.2
    exact ⟨Nat.le_trans hs.1 this.1, this.2⟩

/-- THE SPLIT AT THE FIRST `RC` WRITE (always a machine-v2 write). -/
theorem soloQV_splitF (hRC : RCOk RC) {n : Nat} : ∀ {x y τ}, soloQV pstep img M i (QGV RC n) x τ y →
    soloQV pstep img M i (QNRV RC) x τ y ∨
    ∃ τ1 z l r p' ws' prom' τ2, soloQV pstep img M i (QNRV RC) x τ1 z ∧ RC z.2.1 l ∧ n < r ∧
      pstep z.1 () (.v l) p' () ∧ memStep img M i z.2.2 z.2.1 l (some r) ws' prom' ∧
      soloQV pstep img M i QTV (p', ws', prom') τ2 y ∧ τ = τ1 ++ (.v l, some r) :: τ2 := by
  intro x y τ h
  induction h with
  | refl => exact .inl (.refl _)
  | step x l ots p' ws' prom' tr y hq hp hm hrest ih =>
    by_cases hr : RCV RC x.2.1 l
    · obtain ⟨l0, e, hm0⟩ := rcV_inv hRC hm hr
      subst e
      cases ots with
      | none => exact absurd hr (hRC.none_ hm0)
      | some r =>
        exact .inr ⟨[], x, l0, r, p', ws', prom', tr, .refl _, hr, hq hr r rfl, hp, hm0,
          soloQV_mono (fun _ _ _ _ => trivial) hrest, rfl⟩
    · rcases ih with ih | ⟨τ1, z, l', r, p'', ws'', prom'', τ2, k1, k2, k3, k4, k5, k6, k7⟩
      · exact .inl (.step _ _ _ _ _ _ _ _ hr hp hm ih)
      · refine .inr ⟨(l, ots) :: τ1, z, l', r, p'', ws'', prom'', τ2, .step _ _ _ _ _ _ _ _ hr hp hm k1, k2, k3,
          k4, k5, k6, ?_⟩
        rw [k7]; rfl

theorem soloQV_prom {Q : PState → VLabel → Option Nat → Prop} :
    ∀ {x y τ}, soloQV pstep img M i Q x τ y → ∀ t, t ∈ y.2.2 → t ∈ x.2.2 := by
  intro x y τ hs
  induction hs with
  | refl => exact fun _ h => h
  | step x l ots p' ws' prom' tr y _ _ hm _ ih =>
    intro t ht
    have := ih t ht
    rcases memStepV_prom hm with ⟨_, e⟩ | ⟨ts, _, _, e2⟩
    · rw [← e]; exact this
    · rw [e2] at this; exact (elemOfDifference.1 this).1

end soloLemmas

/-! ## 4. Every valid run of the variant separates into solo runs against the final memory -/

section solo

variable {P : Type} {pstep : P → Unit → VLabel → P → Unit → Prop} {img : Image} {ps : List P} {M : List PMsg}

/-- Every hart `h` has a solo run against `M` from its initial state, with its trace so far, to its current
state, whose promise set is the current one plus its own messages above the log (MachFactor.lean `FRel`). -/
def SoloAt (pstep : P → Unit → VLabel → P → Unit → Prop) (img : Image) (ps : List P) (M : List PMsg)
    (c : PCfg P Unit) (pre : List VEvt) : Prop :=
  c.pcImg = img ∧ ∀ h p, ps[h]? = some p → ∃ ag, c.pcAgs[h]? = some ag ∧ ∃ P0 Pf : GSet Nat,
    (∀ t, t ∈ P0 ↔ 0 < t ∧ ownTs M h t) ∧ (∀ t, t ∈ Pf ↔ t ∈ ag.paProm ∨ (c.pcLog.length < t ∧ ownTs M h t)) ∧
    soloQV pstep img M h QTV (p, psInit, P0) (traceOfV h pre) (ag.paSt, ag.paWs, Pf)

theorem soloAt_run : ∀ {c cfg : PCfg P Unit} {es : List VEvt}, pmStepsV pstep c es cfg → runWf c →
    cfg.pcLog = M → ∀ pre, SoloAt pstep img ps M c pre → SoloAt pstep img ps M cfg (pre ++ es) := by
  intro c cfg es hrun
  induction hrun with
  | refl => intro _ _ pre hs; simpa using hs
  | step c0 c1 c2 e es hst hrest ih =>
    intro hwf hM pre hs
    have hwf1 := pmStepV_wf hst hwf
    have hpre1 : c1.pcLog <+: M := hM ▸ (pmStepsV_inv hrest).2.1
    have key : SoloAt pstep img ps M c1 (pre ++ [e]) := by
      obtain ⟨himg, hh⟩ := hs
      cases hst with
      | promise i ag m hag hnt htid =>
        have hpre' : c0.pcLog ++ [m] <+: M := hpre1
        refine ⟨himg, fun h p hp => ?_⟩
        obtain ⟨ag0, hag0, P0, Pf, hP0, hPf, hsolo⟩ := hh h p hp
        have etr : traceOfV h (pre ++ [VEvt.prom i m]) = traceOfV h pre := by
          rw [traceOfV_append]; simp [traceOfV]
        rw [etr]
        by_cases hih : h = i
        · subst hih
          rw [hag] at hag0; cases hag0
          refine ⟨_, getElem?_set_eq_of hag, P0, Pf, hP0, fun t => ?_, hsolo⟩
          simp only [List.length_append, List.length_singleton]
          rw [hPf t, ownTs_shift hpre' h t, elemOfUnion, elemOfSingleton]
          constructor
          · rintro (h1 | ⟨h1, _⟩ | h1)
            · exact .inl (.inr h1)
            · exact .inl (.inl h1)
            · exact .inr h1
          · rintro ((h1 | h1) | h1)
            · exact .inr (.inl ⟨h1, htid⟩)
            · exact .inl h1
            · exact .inr (.inr h1)
        · refine ⟨ag0, by simp only; rw [List.getElem?_set_ne (Ne.symm hih)]; exact hag0, P0, Pf, hP0,
            fun t => ?_, hsolo⟩
          simp only [List.length_append, List.length_singleton]
          rw [hPf t, ownTs_shift hpre' h t]
          constructor
          · rintro (h1 | ⟨_, h1⟩ | h1)
            · exact .inl h1
            · rw [htid] at h1; cases h1; exact absurd rfl hih
            · exact .inr h1
          · rintro (h1 | h1)
            · exact .inl h1
            · exact .inr (.inr h1)
      | state i ag l ots st' d' ws' prom' hag hp hm =>
        refine ⟨himg, fun h p hp' => ?_⟩
        obtain ⟨ag0, hag0, P0, Pf, hP0, hPf, hsolo⟩ := hh h p hp'
        by_cases hih : h = i
        · subst hih
          rw [hag] at hag0; cases hag0
          obtain ⟨hb, hw⟩ := hwf.1 h ag hag
          obtain ⟨P', hm', hP'⟩ := memStepV_extend Pf (ownTs M h) hm hpre1 hb hw hPf
          refine ⟨_, getElem?_set_eq_of hag, P0, P', hP0, hP', ?_⟩
          rw [traceOfV_append]
          simp only [traceOfV, if_true]
          rw [himg] at hm'
          cases d'
          exact soloQV_append hsolo (.step _ _ _ _ _ _ _ _ trivial hp hm' (.refl _))
        · refine ⟨ag0, by simp only; rw [List.getElem?_set_ne (Ne.symm hih)]; exact hag0, P0, Pf, hP0, hPf, ?_⟩
          rw [traceOfV_append]
          simp only [traceOfV, show i ≠ h from fun e => hih e.symm, if_false, List.append_nil]
          exact hsolo
    have := ih hwf1 hM (pre ++ [e]) key
    simpa using this

/-- EVERY VALID RUN OF THE VARIANT SEPARATES (MachSolo.lean `validRun_solo`). -/
theorem validRunV_solo {evs : List VEvt} {cfg : PCfg P Unit} (hv : validRunV pstep img () ps evs cfg) :
    ∀ hh p, ps[hh]? = some p → ∃ ag, cfg.pcAgs[hh]? = some ag ∧ ∃ P0 : GSet Nat,
      (∀ t, t ∈ P0 ↔ 0 < t ∧ ownTs cfg.pcLog hh t) ∧
      soloQV pstep img cfg.pcLog hh QTV (p, psInit, P0) (traceOfV hh evs) (ag.paSt, ag.paWs, ag.paProm) := by
  intro hh p hp
  have hwf := pmStepsV_wf hv.1 (pmInit_wf img () ps)
  have hlen := (pmStepsV_inv hv.1).2.2.1
  obtain ⟨c0', _, _, hlog, _, _, hags⟩ := promsRun (pstep := fun (_ : P) (_ : Unit) (_ : PLabel) (_ : P) (_ : Unit) =>
    True) cfg.pcLog (pmInit img () ps) (fun m hm => by rw [← hlen]; exact hwf.2 m hm)
  have h0 : SoloAt pstep img ps cfg.pcLog (pmInit img () ps) [] := by
    refine ⟨rfl, fun h p' hp' => ?_⟩
    have hi : (pmInit img () ps).pcAgs[h]? = some ⟨p', psInit, ∅⟩ := by
      simp only [pmInit, List.getElem?_map, hp', Option.map_some]
    obtain ⟨ag', _, _, _, h4⟩ := hags h _ hi
    have hP : ∀ t, t ∈ ag'.paProm ↔ 0 < t ∧ ownTs cfg.pcLog h t := by
      intro t
      rw [h4 t]
      simp only [pmInit, List.length_nil, List.nil_append]
      exact ⟨fun u => u.elim (fun v => absurd v notElemOfEmpty) id, .inr⟩
    exact ⟨_, hi, ag'.paProm, ag'.paProm, hP, fun t => by
      rw [hP t]; simp only [pmInit, List.length_nil]
      exact ⟨.inr, fun u => u.elim (fun v => absurd v notElemOfEmpty) id⟩, .refl _⟩
  obtain ⟨_, hh'⟩ := soloAt_run hv.1 (pmInit_wf img () ps) rfl [] h0
  obtain ⟨ag, hag, P0, Pf, hP0, hPf, hsolo⟩ := hh' hh p hp
  have e : Pf = ag.paProm := setEq.2 (fun t => by
    rw [hPf t]; exact ⟨fun u => u.elim id (fun v => absurd v.2 (ownTs_gt v.1)), .inl⟩)
  subst e
  exact ⟨ag, hag, P0, hP0, by simpa using hsolo⟩

end solo

/-! ## 5. The NF run shape with prophecy-fed fetches and A/D updates -/

section nf

variable {P D : Type} (RC : PState → PLabel → Prop) (pstep : P → D → VLabel → P → D → Prop) (M : List PMsg)

/-- THE NF RUN SHAPE (NfrFetch.lean `nfStepsF` over `VLabel`) plus FIX (i): `adF` — an A/D update of agent `i` whose
timestamp is ABOVE the current log, admissible against the FINAL memory `M` (no view effect: the agent's state and
promise set are unchanged); `promF` — the agent appends an A/D message WITHOUT a promise owner (it was fulfilled
early).  `promF` and `prom` emit the same event `.prom i m`, so traces are unaffected. -/
inductive nfStepsV : PCfg P D → List VEvt → PCfg P D → Prop
  | refl (c : PCfg P D) : nfStepsV c [] c
  | prom (c c1 : PCfg P D) (i : Nat) (m : PMsg) (es : List VEvt) (c2 : PCfg P D) :
      pmStepV pstep c (.prom i m) c1 → nfStepsV c1 es c2 → nfStepsV c (.prom i m :: es) c2
  | promF (c : PCfg P D) (i : Nat) (ag : PAgent P) (m : PMsg) (es : List VEvt) (c2 : PCfg P D) :
      c.pcAgs[i]? = some ag → m.data ≠ [] → m.tid = some i → m.cls = PClass.ad →
      nfStepsV ⟨c.pcImg, c.pcLog ++ [m], c.pcDev, c.pcAgs⟩ es c2 → nfStepsV c (.prom i m :: es) c2
  | st (c c1 : PCfg P D) (i : Nat) (ag : PAgent P) (l : VLabel) (ots : Option Nat) (es : List VEvt)
      (c2 : PCfg P D) :
      c.pcAgs[i]? = some ag → ¬ RCV RC ag.paWs l → pmStepV pstep c (.st i l ots) c1 → nfStepsV c1 es c2 →
      nfStepsV c (.st i l ots :: es) c2
  | rel (c c1 c2 : PCfg P D) (i : Nat) (m : PMsg) (ag : PAgent P) (l : PLabel) (r : Nat) (es : List VEvt)
      (c3 : PCfg P D) :
      pmStepV pstep c (.prom i m) c1 → c1.pcAgs[i]? = some ag → RC ag.paWs l → r = c1.pcLog.length →
      pmStepV pstep c1 (.st i (.v l) (some r)) c2 → nfStepsV c2 es c3 →
      nfStepsV c (.prom i m :: .st i (.v l) (some r) :: es) c3
  | fet (c : PCfg P D) (i : Nat) (ag : PAgent P) (b : Int) (tvs : List (Nat × BitVec 8)) (st' : P) (d' : D)
      (es : List VEvt) (c2 : PCfg P D) :
      c.pcAgs[i]? = some ag → pstep ag.paSt c.pcDev (.v (LIFetch b tvs)) st' d' →
      bytesAll (fetchByteOk c.pcImg M ag.paWs) b tvs →
      nfStepsV ⟨c.pcImg, c.pcLog, d', c.pcAgs.set i ⟨st', fetchPostV c.pcLog i ag.paProm ag.paWs b tvs, ag.paProm⟩⟩
        es c2 →
      nfStepsV c (.st i (.v (LIFetch b tvs)) none :: es) c2
  | adF (c : PCfg P D) (i : Nat) (ag : PAgent P) (b : Int) (tvs : List (Nat × BitVec 8)) (d : List (BitVec 8))
      (ts : Nat) (st' : P) (d' : D) (es : List VEvt) (c2 : PCfg P D) :
      c.pcAgs[i]? = some ag → pstep ag.paSt c.pcDev (.ad b tvs d) st' d' → c.pcLog.length < ts →
      tvs.length = d.length → M[ts - 1]? = some ⟨b, d, some i, PClass.ad⟩ → bytesAll (adReadOk c.pcImg M ts) b tvs →
      nfStepsV ⟨c.pcImg, c.pcLog, d', c.pcAgs.set i ⟨st', ag.paWs, ag.paProm⟩⟩ es c2 →
      nfStepsV c (.st i (.ad b tvs d) (some ts) :: es) c2

/-- An NF VALID RUN of the variant. -/
def nfRunV (img : Image) (d0 : D) (ps : List P) (evs : List VEvt) (cfg : PCfg P D) : Prop :=
  nfStepsV RC pstep M (pmInit img d0 ps) evs cfg ∧ noPromises cfg

variable {RC pstep M}

theorem nfStepsV_append {c c1 c2 : PCfg P D} {es1 es2 : List VEvt} (h1 : nfStepsV RC pstep M c es1 c1)
    (h2 : nfStepsV RC pstep M c1 es2 c2) : nfStepsV RC pstep M c (es1 ++ es2) c2 := by
  induction h1 with
  | refl => exact h2
  | prom c c1 i m es c2' h _ ih => exact .prom _ _ _ _ _ _ h (ih h2)
  | promF c i ag m es c2' ha hd ht hc _ ih => exact .promF _ _ _ _ _ _ ha hd ht hc (ih h2)
  | st c c1 i ag l ots es c2' ha hn h _ ih => exact .st _ _ _ _ _ _ _ _ ha hn h (ih h2)
  | rel c c1 c2' i m ag l r es c3 h ha hr hl h' _ ih => exact .rel _ _ _ _ _ _ _ _ _ _ h ha hr hl h' (ih h2)
  | fet c i ag b tvs st' d' es c2' ha hp hok _ ih => exact .fet _ _ _ _ _ _ _ _ _ ha hp hok (ih h2)
  | adF c i ag b tvs d ts st' d' es c2' ha hp hlt hlen hm hrd _ ih =>
    exact .adF _ _ _ _ _ _ _ _ _ _ _ ha hp hlt hlen hm hrd (ih h2)

theorem pmStepV_prefix {c c' : PCfg P D} {e : VEvt} (h : pmStepV pstep c e c') : c.pcLog <+: c'.pcLog := by
  cases h with
  | promise => exact List.prefix_append _ _
  | state => exact List.prefix_refl _

/-- The log only grows along an NF run. -/
theorem nfStepsV_prefix {c c' : PCfg P D} {es : List VEvt} (h : nfStepsV RC pstep M c es c') :
    c.pcLog <+: c'.pcLog := by
  induction h with
  | refl => exact List.prefix_refl _
  | prom c c1 i m es c2 h1 _ ih => exact List.IsPrefix.trans (pmStepV_prefix h1) ih
  | promF c i ag m es c2 _ _ _ _ _ ih => exact List.IsPrefix.trans (List.prefix_append _ _) ih
  | st c c1 i ag l ots es c2 _ _ h1 _ ih => exact List.IsPrefix.trans (pmStepV_prefix h1) ih
  | rel c c1 c2 i m ag l r es c3 h1 _ _ _ h2 _ ih =>
    exact List.IsPrefix.trans (pmStepV_prefix h1) (List.IsPrefix.trans (pmStepV_prefix h2) ih)
  | fet c i ag b tvs st' d' es c2 _ _ _ _ ih => exact ih
  | adF c i ag b tvs d ts st' d' es c2 _ _ _ _ _ _ _ ih => exact ih

end nf

/-! ## 6. The schedule (NfrFetch.lean §6 over `VLabel`; the A/D cases are the only new ones) -/

/-- A hart's remaining work over variant labels. -/
structure JobV (P : Type) where
  x : P × PState × GSet Nat
  τ : List (VLabel × Option Nat)
  y : P × PState × GSet Nat

/-- The state events of agent `A` for a trace. -/
def stEvsV (A : Nat) (τ : List (VLabel × Option Nat)) : List VEvt := τ.map (fun e => VEvt.st A e.1 e.2)

theorem traceOfV_stEvsV (h A : Nat) : ∀ τ : List (VLabel × Option Nat),
    traceOfV h (stEvsV A τ) = if h = A then τ else []
  | [] => by simp [stEvsV, traceOfV]
  | e :: τ => by
    have ih := traceOfV_stEvsV h A τ
    simp only [stEvsV, List.map_cons] at ih ⊢
    simp only [traceOfV]
    by_cases hh : A = h
    · subst hh; simp only [if_true] at ih ⊢; rw [ih]
    · have hh' : ¬ h = A := fun e => hh e.symm
      simp only [hh, hh', if_false] at ih ⊢; exact ih

section sched

variable {P : Type} {pstep : P → Unit → VLabel → P → Unit → Prop} {img : Image} {M : List PMsg} {N : Nat}
variable {RC : PState → PLabel → Prop}

/-- One hart's part of the invariant at log length `n`.  THE ONE CHANGE from NfrFetch.lean `hartInvF`: an own
message above the prefix is still promised OR IS AN A/D MESSAGE (fulfilled early by `adF`). -/
def hartInvV (RC : PState → PLabel → Prop) (pstep : P → Unit → VLabel → P → Unit → Prop) (img : Image)
    (M : List PMsg) (c : PCfg P Unit) (n : Nat) (h : Nat) (j : JobV P) : Prop :=
  ∃ Q, c.pcAgs[h]? = some ⟨j.x.1, j.x.2.1, Q⟩ ∧ (∀ t, t ∈ Q ↔ t ∈ j.x.2.2 ∧ t ≤ n) ∧
    soloQV pstep img M h (QGV RC n) j.x j.τ j.y ∧ promWf M h j.x.2.2 ∧
    (∀ t, n < t → ownTs M h t → t ∈ j.x.2.2 ∨ adAt M t) ∧ fwdB j.x.2.1

/-- THE SCHEDULE INVARIANT. -/
def InvV (RC : PState → PLabel → Prop) (pstep : P → Unit → VLabel → P → Unit → Prop) (img : Image)
    (M : List PMsg) (N : Nat) (c : PCfg P Unit) (J : Fin N → JobV P) (n : Nat) : Prop :=
  c.pcImg = img ∧ c.pcLog = M.take n ∧ n ≤ M.length ∧ c.pcAgs.length = N ∧
    ∀ h : Fin N, hartInvV RC pstep img M c n h (J h)

/-- The end of the schedule. -/
def FinalV (img : Image) (M : List PMsg) (N : Nat) (c : PCfg P Unit) (J : Fin N → JobV P) : Prop :=
  c.pcImg = img ∧ c.pcLog = M ∧ c.pcAgs.length = N ∧
    ∀ h : Fin N, ∃ Q, c.pcAgs[(h : Nat)]? = some ⟨(J h).y.1, (J h).y.2.1, Q⟩ ∧ ∀ t, t ∈ Q ↔ t ∈ (J h).y.2.2

/-- ONE APPEND of `M[n]` by its author: as a promise (`prom`), or, if the author already fulfilled it — then it is
an A/D message — with no promise owner (`promF`). -/
theorem promOneV (hmsg : ∀ m ∈ M, msgOk N m) {c : PCfg P Unit} {J : Fin N → JobV P} {n : Nat}
    (hI : InvV RC pstep img M N c J n) (hn : n < M.length)
    (hq : ∀ h : Fin N, soloQV pstep img M h (QGV RC (n + 1)) (J h).x (J h).τ (J h).y) :
    ∃ i m c', M[n]? = some m ∧ m.tid = some i ∧ nfStepsV RC pstep M c [.prom i m] c' ∧
      InvV RC pstep img M N c' J (n + 1) := by
  obtain ⟨himg, hlog, hle, hlen, hh⟩ := hI
  have hmn : M[n]? = some M[n] := List.getElem?_eq_getElem hn
  obtain ⟨hnt, i, htid, hiN⟩ := hmsg M[n] (List.getElem_mem hn)
  obtain ⟨Qi, hagi, hQi, _, _, hfut, _⟩ := hh ⟨i, hiN⟩
  have hclen : c.pcLog.length = n := by rw [hlog]; exact take_length_of hle
  -- the other harts are unaffected by either kind of append
  have hothers : ∀ (h : Fin N), (h : Nat) ≠ i → ∀ Q : GSet Nat, (∀ t, t ∈ Q ↔ t ∈ (J h).x.2.2 ∧ t ≤ n) →
      promWf M h (J h).x.2.2 → ∀ t, t ∈ Q ↔ t ∈ (J h).x.2.2 ∧ t ≤ n + 1 := by
    intro h hih Q hQ hw t
    rw [hQ t]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, by omega⟩
    · rintro ⟨h1, h2⟩
      refine ⟨h1, ?_⟩
      by_cases e : t = n + 1
      · subst e
        obtain ⟨_, _, m', hm', ht'⟩ := hw _ h1
        simp only [Nat.add_sub_cancel] at hm'
        rw [hmn] at hm'
        cases hm'
        rw [htid] at ht'
        cases ht'
        exact absurd rfl hih
      · omega
  by_cases hin : n + 1 ∈ (J ⟨i, hiN⟩).x.2.2
  · -- a promise of its author
    have hst := pmStepV.promise (pstep := pstep) c i _ M[n] hagi hnt htid
    refine ⟨i, M[n], _, hmn, htid, .prom _ _ _ _ _ _ hst (.refl _), himg, ?_, by omega, by simp [hlen], fun h => ?_⟩
    · simp only; rw [hlog, take_succ_of hmn]
    · obtain ⟨Q, hag, hQ, _, hw, hf, hb⟩ := hh h
      by_cases hih : (h : Nat) = i
      · have e : h = ⟨i, hiN⟩ := Fin.ext hih
        subst e
        rw [hagi] at hag
        cases hag
        refine ⟨{c.pcLog.length + 1} ∪ Qi, ?_, fun t => ?_, hq _, hw, fun t ht ho => hf t (by omega) ho, hb⟩
        · simp only; exact getElem?_set_eq_of hagi
        · rw [elemOfUnion, elemOfSingleton, hQi t, hclen]
          constructor
          · rintro (e | ⟨h1, h2⟩)
            · subst e; exact ⟨hin, Nat.le_refl _⟩
            · exact ⟨h1, by omega⟩
          · rintro ⟨h1, h2⟩
            by_cases e : t = n + 1
            · exact .inl e
            · exact .inr ⟨h1, by omega⟩
      · refine ⟨Q, ?_, hothers h hih Q hQ hw, hq h, hw, fun t ht ho => hf t (by omega) ho, hb⟩
        simp only; rw [List.getElem?_set_ne (Ne.symm hih)]; exact hag
  · -- already fulfilled by its author: an A/D message, appended with no promise owner
    have hc : M[n].cls = PClass.ad := by
      rcases hfut (n + 1) (by omega) ⟨M[n], by simp [hmn], htid⟩ with h1 | ⟨m', hm', hc⟩
      · exact absurd h1 hin
      · simp only [Nat.add_sub_cancel] at hm'; rw [hmn] at hm'; cases hm'; exact hc
    have hd : M[n].data ≠ [] := by
      rcases hnt with h1 | ⟨k, len, h1, h2⟩
      · exact h1
      · rw [hc] at h1; simp only [PClass.ad, PClass.cmo.injEq] at h1; omega
    refine ⟨i, M[n], ⟨c.pcImg, c.pcLog ++ [M[n]], c.pcDev, c.pcAgs⟩, hmn, htid,
      .promF _ _ _ _ _ _ hagi hd htid hc (.refl _), himg, ?_, by omega, hlen, fun h => ?_⟩
    · simp only; rw [hlog, take_succ_of hmn]
    · obtain ⟨Q, hag, hQ, _, hw, hf, hb⟩ := hh h
      refine ⟨Q, hag, ?_, hq h, hw, fun t ht ho => hf t (by omega) ho, hb⟩
      by_cases hih : (h : Nat) = i
      · have e : h = ⟨i, hiN⟩ := Fin.ext hih
        subst e
        intro t
        rw [hQ t]
        constructor
        · rintro ⟨h1, h2⟩; exact ⟨h1, by omega⟩
        · rintro ⟨h1, h2⟩
          refine ⟨h1, ?_⟩
          by_cases e : t = n + 1
          · subst e; exact absurd h1 hin
          · omega
      · exact hothers h hih Q hQ hw

/-- APPENDS UP TO `k`. -/
theorem promsUpToV (hmsg : ∀ m ∈ M, msgOk N m) {k : Nat} :
    ∀ (d : Nat) {c : PCfg P Unit} {J : Fin N → JobV P} {n : Nat}, n + d = k → InvV RC pstep img M N c J n →
      k ≤ M.length → (∀ h : Fin N, soloQV pstep img M h (QGV RC k) (J h).x (J h).τ (J h).y) →
      ∃ es c', nfStepsV RC pstep M c es c' ∧ InvV RC pstep img M N c' J k ∧ ∀ h, traceOfV h es = [] := by
  intro d
  induction d with
  | zero =>
    intro c J n hk hI _ _
    rw [Nat.add_zero] at hk; subst hk
    exact ⟨[], c, .refl _, hI, fun _ => rfl⟩
  | succ d ih =>
    intro c J n hk hI hkM hq
    obtain ⟨i, m, c', _, _, hst, hI'⟩ := promOneV hmsg hI (by omega)
      (fun h => soloQV_QG_anti (by omega) (hq h))
    obtain ⟨es, c'', h1, h2, h3⟩ := ih (n := n + 1) (by omega) hI' hkM hq
    exact ⟨.prom i m :: es, c'', nfStepsV_append hst h1, h2, fun h => by simp only [traceOfV]; exact h3 h⟩

/-- RUNNING ONE HART'S `RC`-FREE SEGMENT against the current prefix: v2 non-fetch steps by restriction, fetches by
`fet`, and an A/D update by restriction if its timestamp is in the prefix, else by `adF` against `M`. -/
theorem runSegV {A : Nat} :
    ∀ {x z : P × PState × GSet Nat} {τ1 : List (VLabel × Option Nat)}, soloQV pstep img M A (QNRV RC) x τ1 z →
      ∀ (c : PCfg P Unit) (Q : GSet Nat), c.pcImg = img → c.pcLog <+: M → c.pcAgs[A]? = some ⟨x.1, x.2.1, Q⟩ →
      (∀ t, t ∈ Q ↔ t ∈ x.2.2 ∧ t ≤ c.pcLog.length) → fwdB x.2.1 →
      (∀ t, c.pcLog.length < t → ownTs M A t → t ∈ x.2.2 ∨ adAt M t) →
      (bndF z.2.1 ≤ c.pcLog.length ∨ M.length ≤ c.pcLog.length) →
      ∃ Q', nfStepsV RC pstep M c (stEvsV A τ1) ⟨c.pcImg, c.pcLog, c.pcDev, c.pcAgs.set A ⟨z.1, z.2.1, Q'⟩⟩ ∧
        (∀ t, t ∈ Q' ↔ t ∈ z.2.2 ∧ t ≤ c.pcLog.length) ∧ fwdB z.2.1 ∧
        (∀ t, c.pcLog.length < t → ownTs M A t → t ∈ z.2.2 ∨ adAt M t) ∧ (∀ t, t ∈ z.2.2 → t ∈ x.2.2) := by
  intro x z τ1 h
  induction h with
  | refl x =>
    intro c Q _ _ hag hQ hb hfut _
    refine ⟨Q, ?_, hQ, hb, hfut, fun _ h => h⟩
    rw [set_of_get hag]
    exact .refl _
  | step x l ots p' ws' prom' tr z hq hp hm hrest ih =>
    intro c Q himg hpre hag hQ hb hfut hfit
    have eset : ∀ (ag1 ag2 : PAgent P),
        (⟨c.pcImg, c.pcLog, (), (c.pcAgs.set A ag1).set A ag2⟩ : PCfg P Unit) =
          ⟨c.pcImg, c.pcLog, c.pcDev, c.pcAgs.set A ag2⟩ := by
      intro ag1 ag2; rw [List.set_set]
    have hsub : ∀ t, t ∈ prom' → t ∈ x.2.2 := by
      intro t ht
      rcases memStepV_prom hm with ⟨_, e⟩ | ⟨ts, _, _, e2⟩
      · rw [← e]; exact ht
      · rw [e2] at ht; exact (elemOfDifference.1 ht).1
    have hfin : ∀ (Q' : GSet Nat), (∀ t, t ∈ z.2.2 → t ∈ prom') → ∀ t, t ∈ z.2.2 → t ∈ x.2.2 :=
      fun _ h5 t ht => hsub t (h5 t ht)
    cases l with
    | ad b tvs d =>
      -- THE A/D UPDATE (fix (i))
      obtain ⟨ts, rfl, rfl, rfl, hlen, h0, hts, hmM, hrd⟩ := memStepV_ad_inv hm
      have hfut' : ∀ t, c.pcLog.length < t → ownTs M A t → t ∈ x.2.2 \ {ts} ∨ adAt M t := by
        intro t ht ho
        by_cases e : t = ts
        · subst e; exact .inr ⟨_, hmM, rfl⟩
        · rcases hfut t ht ho with h1 | h1
          · exact .inl (elemOfDifference.2 ⟨h1, by rw [elemOfSingleton]; exact e⟩)
          · exact .inr h1
      by_cases hle : ts ≤ c.pcLog.length
      · -- in the prefix: an ordinary step of the arm, by restriction
        have hmL : memStepV img c.pcLog A Q x.2.1 (.ad b tvs d) (some ts) x.2.1 (Q \ {ts}) :=
          .ad _ _ _ _ _ _ hlen h0 ((hQ ts).2 ⟨hts, hle⟩) (by rw [← prefix_getElem? hpre (by omega)]; exact hmM)
            (bytesAll_mono (fun a t v hp => (adReadOk_iff hpre hle a t v).1 hp) b tvs hrd)
        have hst : pmStepV pstep c (.st A (.ad b tvs d) (some ts))
            ⟨c.pcImg, c.pcLog, (), c.pcAgs.set A ⟨p', x.2.1, Q \ {ts}⟩⟩ :=
          pmStepV.state c A _ _ _ p' () _ _ hag hp (himg ▸ hmL)
        obtain ⟨Q', h1, h2, h3, h4, h5⟩ := ih ⟨c.pcImg, c.pcLog, (), c.pcAgs.set A ⟨p', x.2.1, Q \ {ts}⟩⟩ (Q \ {ts})
          himg hpre (getElem?_set_eq_of hag) (promCut_diff hQ) hb hfut' hfit
        refine ⟨Q', ?_, h2, h3, h4, hfin Q' h5⟩
        rw [← eset ⟨p', x.2.1, Q \ {ts}⟩ ⟨z.1, z.2.1, Q'⟩]
        exact .st _ _ _ _ _ _ _ _ hag (fun h => h) hst h1
      · -- above the prefix: the prophecy-fed `adF`, cut promise set unchanged
        have hQ' : ∀ t, t ∈ Q ↔ t ∈ x.2.2 \ {ts} ∧ t ≤ c.pcLog.length := by
          intro t
          rw [hQ t, elemOfDifference, elemOfSingleton]
          exact ⟨fun ⟨u1, u2⟩ => ⟨⟨u1, by omega⟩, u2⟩, fun ⟨⟨u1, _⟩, u2⟩ => ⟨u1, u2⟩⟩
        obtain ⟨Q', h1, h2, h3, h4, h5⟩ := ih ⟨c.pcImg, c.pcLog, (), c.pcAgs.set A ⟨p', x.2.1, Q⟩⟩ Q
          himg hpre (getElem?_set_eq_of hag) hQ' hb hfut' hfit
        refine ⟨Q', ?_, h2, h3, h4, hfin Q' h5⟩
        rw [← eset ⟨p', x.2.1, Q⟩ ⟨z.1, z.2.1, Q'⟩]
        exact .adF c A ⟨x.1, x.2.1, Q⟩ b tvs d ts p' () _ _ hag hp (by omega) hlen hmM (himg ▸ hrd) h1
    | v l0 =>
      by_cases hfe : isFetch l0
      · -- THE PROPHECY-FED FETCH (E-b)
        obtain ⟨b, tvs, rfl⟩ := hfe
        obtain ⟨hok, rfl, rfl, rfl⟩ := memStepV_fetch_inv hm
        have hws : fetchPostV M A x.2.2 x.2.1 b tvs = fetchPostV c.pcLog A Q x.2.1 b tvs := by
          unfold fetchPostV; rw [fetchViewV_cut hpre hQ hfut b tvs]
        rw [hws] at ih hrest
        have hb' : fwdB (fetchPostV c.pcLog A Q x.2.1 b tvs) := hb
        obtain ⟨Q', h1, h2, h3, h4, h5⟩ := ih ⟨c.pcImg, c.pcLog, (), c.pcAgs.set A
          ⟨p', fetchPostV c.pcLog A Q x.2.1 b tvs, Q⟩⟩ Q himg hpre (getElem?_set_eq_of hag) hQ hb' hfut hfit
        refine ⟨Q', ?_, h2, h3, h4, h5⟩
        rw [← eset ⟨p', fetchPostV c.pcLog A Q x.2.1 b tvs, Q⟩ ⟨z.1, z.2.1, Q'⟩]
        exact .fet c A ⟨x.1, x.2.1, Q⟩ b tvs p' () _ _ hag hp (himg ▸ hok) h1
      · have hm0 := memStepV_v_inv hm hfe
        have hs := memStep_selfF hm0 hb
        have hz : bndF ws' ≤ bndF z.2.1 := (soloQV_bndF hrest hs.2.2.2).1
        have hr : readsLe l0 c.pcLog.length ∧ ∀ ts, ots = some ts → ts ≤ c.pcLog.length := by
          rcases hfit with hf | hf
          · exact ⟨fun b t hl => bytesAll_mono (fun _ _ _ h => by omega) _ _ (hs.2.1 hfe b t hl),
              fun ts e => by have := hs.2.2.1 ts e; omega⟩
          · have hl := memStep_len hm0
            exact ⟨fun b t e => bytesAll_mono (fun _ _ _ h => by omega) _ _ (hl.1 b t e),
              fun ts e => by have := hl.2 ts e; omega⟩
        obtain ⟨Q1, hm1, hQ1⟩ := memStep_restrict Q hm0 hpre
          (fun _ => hfit.elim (fun hf => .inl (by unfold bndF at hz hf; omega)) .inr) hr.1 hr.2 hQ
        have hst : pmStepV pstep c (.st A (.v l0) ots) ⟨c.pcImg, c.pcLog, (), c.pcAgs.set A ⟨p', ws', Q1⟩⟩ :=
          pmStepV.state c A _ (.v l0) ots p' () ws' Q1 hag hp (himg ▸ .v2 _ _ _ _ _ _ hm1 hfe)
        have hfut' : ∀ t, c.pcLog.length < t → ownTs M A t → t ∈ prom' ∨ adAt M t := by
          intro t ht ho
          rcases hfut t ht ho with h1 | h1
          · rcases memStep_prom hm0 with ⟨_, e⟩ | ⟨ts, e1, _, e2⟩
            · rw [e]; exact .inl h1
            · rw [e2, elemOfDifference, elemOfSingleton]
              refine .inl ⟨h1, fun e => ?_⟩
              subst e
              have := hr.2 _ e1
              omega
          · exact .inr h1
        obtain ⟨Q', h1, h2, h3, h4, h5⟩ := ih ⟨c.pcImg, c.pcLog, (), c.pcAgs.set A ⟨p', ws', Q1⟩⟩ Q1 himg hpre
          (getElem?_set_eq_of hag) hQ1 hs.2.2.2 hfut' hfit
        refine ⟨Q', ?_, h2, h3, h4, hfin Q' h5⟩
        rw [← eset ⟨p', ws', Q1⟩ ⟨z.1, z.2.1, Q'⟩]
        exact .st _ _ _ _ _ _ _ _ hag hq hst h1

/-- THE FINAL PHASE: with the whole of `M` in the log and no `RC` write left, run the harts `0, …, k−1`. -/
theorem runAllV {c : PCfg P Unit} {J : Fin N → JobV P}
    (himg : c.pcImg = img) (hlog : c.pcLog = M) (hlen : c.pcAgs.length = N)
    (hh : ∀ h : Fin N, ∃ Q, c.pcAgs[(h : Nat)]? = some ⟨(J h).x.1, (J h).x.2.1, Q⟩ ∧
      (∀ t, t ∈ Q ↔ t ∈ (J h).x.2.2 ∧ t ≤ M.length) ∧ soloQV pstep img M h (QNRV RC) (J h).x (J h).τ (J h).y ∧
      fwdB (J h).x.2.1) :
    ∀ k, k ≤ N → ∃ es c', nfStepsV RC pstep M c es c' ∧ c'.pcImg = img ∧ c'.pcLog = M ∧ c'.pcAgs.length = N ∧
      (∀ h : Fin N, ∃ Q, (h < k → c'.pcAgs[(h : Nat)]? = some ⟨(J h).y.1, (J h).y.2.1, Q⟩ ∧
          ∀ t, t ∈ Q ↔ t ∈ (J h).y.2.2 ∧ t ≤ M.length) ∧
        (k ≤ h → c'.pcAgs[(h : Nat)]? = some ⟨(J h).x.1, (J h).x.2.1, Q⟩ ∧
          ∀ t, t ∈ Q ↔ t ∈ (J h).x.2.2 ∧ t ≤ M.length)) ∧
      ∀ h, traceOfV h es = if hN : h < N then (if h < k then (J ⟨h, hN⟩).τ else []) else [] := by
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨[], c, .refl _, himg, hlog, hlen, fun h => ?_, fun h => ?_⟩
    · obtain ⟨Q, h1, h2, _⟩ := hh h
      exact ⟨Q, fun e => absurd e (Nat.not_lt_zero _), fun _ => ⟨h1, h2⟩⟩
    · simp only [Nat.not_lt_zero, if_false, dite_eq_ite, ite_self]; rfl
  | succ k ih =>
    intro hk
    obtain ⟨es, c', h1, h2, h3, h4, h5, h6⟩ := ih (by omega)
    obtain ⟨A, hAk⟩ : ∃ A : Fin N, (A : Nat) = k := ⟨⟨k, by omega⟩, rfl⟩
    obtain ⟨Q, _, hA⟩ := h5 A
    obtain ⟨hag, hQ⟩ := hA (by omega)
    obtain ⟨_, _, _, hrun, hb⟩ := hh A
    rw [← h3] at hQ
    obtain ⟨Q', g1, g2, _, _, _⟩ := runSegV hrun c' Q h2 (by rw [h3]; exact List.prefix_refl _) hag hQ hb
      (fun t ht ho => absurd ho (ownTs_gt (by rw [h3] at ht; exact ht))) (.inr (by rw [h3]; exact Nat.le_refl _))
    refine ⟨es ++ stEvsV A (J A).τ, _, nfStepsV_append h1 g1, h2, h3, by simp [h4], fun h => ?_, fun h => ?_⟩
    · by_cases e : (h : Nat) = k
      · have e' : h = A := Fin.ext (by omega)
        subst e'
        refine ⟨Q', fun _ => ⟨?_, by rw [← h3]; exact g2⟩, fun hle => absurd hle (by omega)⟩
        simp only; exact getElem?_set_eq_of hag
      · obtain ⟨Q0, k1, k2⟩ := h5 h
        have e2 : (A : Nat) ≠ (h : Nat) := by omega
        refine ⟨Q0, fun hl => ?_, fun hl => ?_⟩
        · obtain ⟨u1, u2⟩ := k1 (by omega)
          refine ⟨?_, u2⟩
          simp only; rw [List.getElem?_set_ne e2]; exact u1
        · obtain ⟨u1, u2⟩ := k2 (by omega)
          refine ⟨?_, u2⟩
          simp only; rw [List.getElem?_set_ne e2]; exact u1
    · rw [traceOfV_append, h6 h, traceOfV_stEvsV]
      by_cases hN : h < N
      · simp only [hN, dif_pos]
        by_cases e : h = k
        · subst e
          have e' : (⟨h, hN⟩ : Fin N) = A := Fin.ext (by show h = (A : Nat); omega)
          rw [e']
          simp [hAk]
        · by_cases hlt : h < k
          · simp [hlt, e, hAk, show h < k + 1 by omega]
          · simp [hlt, e, hAk, show ¬ h < k + 1 by omega]
      · have e : ¬ h = (A : Nat) := by omega
        simp [hN, e]

/-- THE SCHEDULE, by induction on `|M| − n`. -/
theorem scheduleV (hRC : RCOk RC) (hmsg : ∀ m ∈ M, msgOk N m) :
    ∀ (d : Nat) {c : PCfg P Unit} {J : Fin N → JobV P} {n : Nat}, M.length - n ≤ d →
      InvV RC pstep img M N c J n →
      ∃ es c', nfStepsV RC pstep M c es c' ∧ FinalV img M N c' J ∧
        ∀ h, traceOfV h es = if hN : h < N then (J ⟨h, hN⟩).τ else [] := by
  intro d
  induction d using Nat.strongRecOn with
  | _ d ihd =>
  intro c J n hd hI
  classical
  let S : Nat → Prop := fun r => ∃ h : Fin N, ∃ τ1 z l p' ws' prom' τ2,
    soloQV pstep img M h (QNRV RC) (J h).x τ1 z ∧ RC z.2.1 l ∧ n < r ∧
    pstep z.1 () (.v l) p' () ∧ memStep img M h z.2.2 z.2.1 l (some r) ws' prom' ∧
    soloQV pstep img M h QTV (p', ws', prom') τ2 (J h).y ∧ (J h).τ = τ1 ++ (.v l, some r) :: τ2
  obtain ⟨himg, hlog, hle, hlen, hh⟩ := hI
  have hsplit : ∀ h : Fin N, soloQV pstep img M h (QNRV RC) (J h).x (J h).τ (J h).y ∨ ∃ r, S r ∧
      ∃ τ1 z l p' ws' prom' τ2,
      soloQV pstep img M h (QNRV RC) (J h).x τ1 z ∧ RC z.2.1 l ∧ n < r ∧
      pstep z.1 () (.v l) p' () ∧ memStep img M h z.2.2 z.2.1 l (some r) ws' prom' ∧
      soloQV pstep img M h QTV (p', ws', prom') τ2 (J h).y ∧ (J h).τ = τ1 ++ (.v l, some r) :: τ2 := by
    intro h
    obtain ⟨_, _, _, hq, _⟩ := hh h
    rcases soloQV_splitF hRC hq with e | ⟨τ1, z, l, r, p', ws', prom', τ2, k1, k2, k3, k4, k5, k6, k7⟩
    · exact .inl e
    · exact .inr ⟨r, ⟨h, τ1, z, l, p', ws', prom', τ2, k1, k2, k3, k4, k5, k6, k7⟩,
        τ1, z, l, p', ws', prom', τ2, k1, k2, k3, k4, k5, k6, k7⟩
  by_cases hS : ∃ r, S r
  · -- an `RC` write remains: process the least one
    obtain ⟨r, hSr, hmin⟩ := exists_min S hS
    obtain ⟨A, τ1, z, l, p', ws', prom', τ2, k1, k2, k4, k5, k6, k7, k8⟩ := hSr
    obtain ⟨⟨pv, hpv, hpvlt⟩, m, hm, hmt⟩ := memStep_write k6
    have hrM : r ≤ M.length := by have := (List.getElem?_eq_some_iff.1 hm).1; omega
    have hother : ∀ h : Fin N, h ≠ A → soloQV pstep img M h (QGV RC r) (J h).x (J h).τ (J h).y := by
      intro h hne
      rcases hsplit h with e | ⟨rh, hSh, τ1', z', l', p'', ws'', prom'', τ2', j1, j2, j4, j5, j6, j7, j8⟩
      · exact soloQV_QN_QG e
      · have hrh : r ≤ rh := by
          by_cases hc : rh < r
          · exact absurd hSh (hmin rh hc)
          · omega
        have hne' : rh ≠ r := by
          intro e; subst e
          obtain ⟨_, m', hm', hmt'⟩ := memStep_write j6
          rw [hm] at hm'; cases hm'
          exact hne (Fin.ext (Option.some.inj (hmt'.symm.trans hmt)))
        rw [j8]
        refine soloQV_append (soloQV_QN_QG j1) (.step _ _ _ _ _ _ _ _ (fun _ r' e => ?_) j5 (v2V j6)
          (soloQV_raiseF hRC j7 (Nat.le_trans (by omega) ((memStep_vw j6).2 rh rfl))))
        cases e; omega
    have hAq : soloQV pstep img M A (QGV RC (r - 1)) (J A).x (J A).τ (J A).y := by
      rw [k8]
      exact soloQV_append (soloQV_QN_QG k1) (.step _ _ _ _ _ _ _ _ (fun _ r' e => by cases e; omega)
        k5 (v2V k6) (soloQV_raiseF hRC k7 (Nat.le_trans (by omega) ((memStep_vw k6).2 r rfl))))
    have hall : ∀ h : Fin N, soloQV pstep img M h (QGV RC (r - 1)) (J h).x (J h).τ (J h).y := by
      intro h
      by_cases e : h = A
      · subst e; exact hAq
      · exact soloQV_QG_anti (by omega) (hother h e)
    -- 1. appends up to `r − 1`
    obtain ⟨es1, c1, n1, i1, n1tr⟩ := promsUpToV hmsg (r - 1 - n) (k := r - 1) (by omega)
      ⟨himg, hlog, hle, hlen, hh⟩ (by omega) hall
    obtain ⟨g1, g2, g3, g4, g5⟩ := i1
    have hc1len : c1.pcLog.length = r - 1 := by rw [g2]; exact take_length_of (by omega)
    -- 2. hart `A`'s segment up to its `RC` write
    obtain ⟨QA, hagA, hQA, _, hwA, hfA, hbA⟩ := g5 A
    have hbz : bndF z.2.1 < r := hRC.lt_ k6 k2
    obtain ⟨Qz, s1, s2, s3, s4, s5⟩ := runSegV k1 c1 QA g1 (by rw [g2]; exact take_prefix M _) hagA
      (by rw [hc1len]; exact hQA) hbA (fun t ht ho => hfA t (by omega) ho) (.inl (by omega))
    -- 3. the release: promise `M[r − 1]`, then fulfil it in place
    let c2 : PCfg P Unit := ⟨c1.pcImg, c1.pcLog, c1.pcDev, c1.pcAgs.set A ⟨z.1, z.2.1, Qz⟩⟩
    have hag2 : c2.pcAgs[(A : Nat)]? = some ⟨z.1, z.2.1, Qz⟩ := getElem?_set_eq_of hagA
    have hmr : M[r - 1]? = some m := hm
    obtain ⟨hnt, _⟩ := hmsg m (List.mem_of_getElem? hm)
    have hpst := pmStepV.promise (pstep := pstep) c2 A _ m hag2 hnt hmt
    let c3 : PCfg P Unit := ⟨c2.pcImg, c2.pcLog ++ [m], c2.pcDev,
      c2.pcAgs.set A ⟨z.1, z.2.1, {c2.pcLog.length + 1} ∪ Qz⟩⟩
    have hlog3 : c3.pcLog = M.take r := by
      show c1.pcLog ++ [m] = M.take r
      rw [g2]
      have := take_succ_of hmr
      rw [show r - 1 + 1 = r by omega] at this
      exact this.symm
    have hr_in : r ∈ z.2.2 := by
      rcases memStep_prom k6 with ⟨e, _⟩ | ⟨ts, e1, e2, _⟩
      · cases e
      · cases e1; exact e2
    have hQ3 : ∀ t, t ∈ ({c2.pcLog.length + 1} ∪ Qz : GSet Nat) ↔ t ∈ z.2.2 ∧ t ≤ c3.pcLog.length := by
      intro t
      rw [hlog3, take_length_of hrM, elemOfUnion, elemOfSingleton, s2 t, hc1len]
      constructor
      · rintro (e | ⟨u1, u2⟩)
        · subst e; exact ⟨by rw [show r - 1 + 1 = r by omega]; exact hr_in, by omega⟩
        · exact ⟨u1, by omega⟩
      · rintro ⟨u1, u2⟩
        by_cases e : t = r
        · left; omega
        · right; exact ⟨u1, by omega⟩
    have hrd : readsLe l c3.pcLog.length := by
      rw [hlog3, take_length_of hrM]
      exact hRC.reads_ k6 k2 s3
    obtain ⟨Q4, hm4, hQ4⟩ := memStep_restrict _ k6 (by rw [hlog3]; exact take_prefix M r) (fun h => by cases h) hrd
      (fun ts e => by cases e; rw [hlog3, take_length_of hrM]; exact Nat.le_refl _) hQ3
    have hag3 : c3.pcAgs[(A : Nat)]? = some ⟨z.1, z.2.1, {c2.pcLog.length + 1} ∪ Qz⟩ := getElem?_set_eq_of hag2
    let c4 : PCfg P Unit := ⟨c3.pcImg, c3.pcLog, (), c3.pcAgs.set A ⟨p', ws', Q4⟩⟩
    have himg3 : c3.pcImg = img := g1
    have hrst := pmStepV.state (pstep := pstep) c3 A _ (.v l) (some r) p' () ws' Q4 hag3 k5 (himg3 ▸ v2V hm4)
    have hr3 : r = c3.pcLog.length := by rw [hlog3, take_length_of hrM]
    -- the invariant after the release
    let J' : Fin N → JobV P := fun h => if h = A then ⟨(p', ws', prom'), τ2, (J A).y⟩ else J h
    have hself := memStep_selfF k6 s3
    have hI4 : InvV RC pstep img M N c4 J' r := by
      refine ⟨g1, hlog3, hrM, by simp [c4, c3, c2, g4], fun h => ?_⟩
      by_cases e : h = A
      · subst e
        simp only [J', if_true]
        refine ⟨Q4, getElem?_set_eq_of hag3, fun t => by rw [hQ4 t, hlog3, take_length_of hrM],
          soloQV_raiseF hRC k7 ((memStep_vw k6).2 r rfl), ?_, fun t ht ho => ?_, hself.2.2.2⟩
        · intro t ht
          rcases memStep_prom k6 with ⟨e, _⟩ | ⟨ts, _, _, e2⟩
          · cases e
          · rw [e2] at ht; exact hwA t (s5 t (elemOfDifference.1 ht).1)
        · rcases memStep_prom k6 with ⟨e, _⟩ | ⟨ts, e1, _, e2⟩
          · cases e
          · cases e1
            rw [e2, elemOfDifference, elemOfSingleton]
            rcases s4 t (by omega) ho with u | u
            · exact .inl ⟨u, by omega⟩
            · exact .inr u
      · simp only [J', e, if_false]
        obtain ⟨Q, u1, u2, _, u4, u5, u6⟩ := g5 h
        have hne : (h : Nat) ≠ (A : Nat) := fun e' => e (Fin.ext e')
        refine ⟨Q, ?_, fun t => ?_, hother h e, u4, fun t ht ho => u5 t (by omega) ho, u6⟩
        · show (((c1.pcAgs.set A _).set A _).set A _)[(h : Nat)]? = _
          rw [List.getElem?_set_ne (Ne.symm hne), List.getElem?_set_ne (Ne.symm hne),
            List.getElem?_set_ne (Ne.symm hne)]
          exact u1
        · rw [u2 t]
          constructor
          · rintro ⟨v1, v2⟩; exact ⟨v1, by omega⟩
          · rintro ⟨v1, v2⟩
            refine ⟨v1, ?_⟩
            by_cases et : t = r
            · subst et
              obtain ⟨_, _, m', hm', ht'⟩ := u4 _ v1
              rw [hm] at hm'; cases hm'
              exact absurd (Option.some.inj (ht'.symm.trans hmt)) hne
            · omega
    obtain ⟨es4, c5, n4, f4, t4⟩ := ihd (M.length - r) (by omega) (Nat.le_refl _) hI4
    refine ⟨es1 ++ (stEvsV A τ1 ++ (.prom A m :: .st A (.v l) (some r) :: es4)), c5,
      nfStepsV_append n1 (nfStepsV_append s1 (.rel _ _ _ _ _ _ _ _ _ _ hpst hag3 k2 hr3 hrst n4)), ?_, ?_⟩
    · obtain ⟨f1, f2, f3, f4⟩ := f4
      refine ⟨f1, f2, f3, fun h => ?_⟩
      obtain ⟨Q, v1, v2⟩ := f4 h
      by_cases e : h = A
      · subst e; simp only [J', if_true] at v1 v2; exact ⟨Q, v1, v2⟩
      · simp only [J', e, if_false] at v1 v2; exact ⟨Q, v1, v2⟩
    · intro h
      rw [traceOfV_append, traceOfV_append, n1tr h, traceOfV_stEvsV, List.nil_append]
      simp only [traceOfV]
      rw [t4 h]
      by_cases hN : h < N
      · simp only [hN, dif_pos]
        by_cases e : h = (A : Nat)
        · have e' : (⟨h, hN⟩ : Fin N) = A := Fin.ext e
          rw [e']
          simp only [J', if_true, e, if_true, k8]
        · have e' : (⟨h, hN⟩ : Fin N) ≠ A := fun e'' => e (congrArg Fin.val e'')
          have e2 : ¬ (A : Nat) = h := fun e'' => e e''.symm
          simp only [J', e', e, e2, if_false, List.nil_append]
      · have e : ¬ (A : Nat) = h := fun e'' => hN (e'' ▸ A.isLt)
        have e2 : ¬ h = (A : Nat) := fun e'' => e e''.symm
        simp [hN, e, e2]
  · -- no `RC` write remains: the final phase
    have hN : ∀ h : Fin N, soloQV pstep img M h (QNRV RC) (J h).x (J h).τ (J h).y := by
      intro h
      rcases hsplit h with e | ⟨r, hSr, _⟩
      · exact e
      · exact absurd ⟨r, hSr⟩ hS
    obtain ⟨es1, c1, n1, i1, n1tr⟩ := promsUpToV hmsg (M.length - n) (k := M.length) (by omega)
      ⟨himg, hlog, hle, hlen, hh⟩ (Nat.le_refl _) (fun h => soloQV_QN_QG (hN h))
    obtain ⟨g1, g2, _, g4, g5⟩ := i1
    have hlogM : c1.pcLog = M := by rw [g2]; exact List.take_length
    obtain ⟨es2, c2, n2, f1, f2, f3, f5, f6⟩ := runAllV g1 hlogM g4 (fun h => by
      obtain ⟨Q, u1, u2, _, _, _, u6⟩ := g5 h
      exact ⟨Q, u1, u2, hN h, u6⟩) N (Nat.le_refl _)
    refine ⟨es1 ++ es2, c2, nfStepsV_append n1 n2, ⟨f1, f2, f3, fun h => ?_⟩, fun h => ?_⟩
    · obtain ⟨Q, u1, _⟩ := f5 h
      obtain ⟨v1, v2⟩ := u1 h.isLt
      refine ⟨Q, v1, fun t => ?_⟩
      rw [v2 t]
      obtain ⟨_, _, _, _, w4, _, _⟩ := g5 h
      constructor
      · exact fun u => u.1
      · intro u
        exact ⟨u, (w4 t (soloQV_prom (hN h) t u)).2.1⟩
    · rw [traceOfV_append, n1tr h, f6 h, List.nil_append]
      by_cases hN' : h < N
      · simp [hN']
      · simp [hN']

end sched

/-! ## 7. THE NF_R LEMMA FOR THE A/D VARIANT -/

/-- **THE NF_R LEMMA WITH A/D UPDATES** (E-c; program-agnostic; no device fabric), for any release class satisfying
`RCOk`.  Every valid run of the variant — NO premise — can be rescheduled into an NF run (`nfRunV`: releases in
place, fetches and above-prefix A/D updates admissible against the final memory, A/D messages appended without an
owner once fulfilled) with the same final configuration and the same per-hart traces. -/
theorem nfRAd_gen {RC : PState → PLabel → Prop} (hRC : RCOk RC) {P : Type}
    {pstep : P → Unit → VLabel → P → Unit → Prop} {img : Image} {ps : List P} {evs : List VEvt}
    {cfg : PCfg P Unit} (hv : validRunV pstep img () ps evs cfg) :
    ∃ evs', nfRunV RC pstep cfg.pcLog img () ps evs' cfg ∧ ∀ h, traceOfV h evs' = traceOfV h evs := by
  classical
  let M := cfg.pcLog
  let N := ps.length
  have hwf := pmStepsV_wf hv.1 (pmInit_wf img () ps)
  obtain ⟨himg0, _, hlen0, htrN⟩ := pmStepsV_inv hv.1
  have hlenN : cfg.pcAgs.length = N := by rw [hlen0]; simp [pmInit, N]
  have hmsg : ∀ m ∈ M, msgOk N m := fun m hm => by rw [← hlenN]; exact hwf.2 m hm
  have hsolo := validRunV_solo hv
  have hps : ∀ h : Fin N, ps[(h : Nat)]? = some ps[(h : Nat)] := fun h => List.getElem?_eq_getElem h.isLt
  have hjob : ∀ h : Fin N, ∃ ag : PAgent P, cfg.pcAgs[(h : Nat)]? = some ag ∧ ∃ P0 : GSet Nat,
      (∀ t, t ∈ P0 ↔ 0 < t ∧ ownTs M h t) ∧
      soloQV pstep img M h QTV (ps[(h : Nat)], psInit, P0) (traceOfV h evs) (ag.paSt, ag.paWs, ag.paProm) :=
    fun h => hsolo h _ (hps h)
  let ag : Fin N → PAgent P := fun h => Classical.choose (hjob h)
  have hag : ∀ h : Fin N, cfg.pcAgs[(h : Nat)]? = some (ag h) := fun h => (Classical.choose_spec (hjob h)).1
  let P0 : Fin N → GSet Nat := fun h => Classical.choose (Classical.choose_spec (hjob h)).2
  have hP0 : ∀ h : Fin N, (∀ t, t ∈ P0 h ↔ 0 < t ∧ ownTs M h t) ∧
      soloQV pstep img M h QTV (ps[(h : Nat)], psInit, P0 h) (traceOfV h evs)
        ((ag h).paSt, (ag h).paWs, (ag h).paProm) :=
    fun h => Classical.choose_spec (Classical.choose_spec (hjob h)).2
  let J : Fin N → JobV P := fun h =>
    ⟨(ps[(h : Nat)], psInit, P0 h), traceOfV h evs, ((ag h).paSt, (ag h).paWs, (ag h).paProm)⟩
  have hI : InvV RC pstep img M N (pmInit img () ps) J 0 := by
    refine ⟨rfl, by simp [pmInit], Nat.zero_le _, by simp [pmInit, N], fun h => ?_⟩
    obtain ⟨h1, h2⟩ := hP0 h
    refine ⟨∅, by simp [pmInit, hps h, J], fun t => ?_, ?_, fun t ht => ?_, fun t _ ho => ?_, fwdB_psInit⟩
    · constructor
      · intro u; exact absurd u notElemOfEmpty
      · rintro ⟨u1, u2⟩
        have := ((h1 t).1 u1).1
        omega
    · exact soloQV_raiseF hRC h2 (Nat.zero_le _)
    · obtain ⟨u1, m, hm, hmt⟩ := (h1 t).1 ht
      exact ⟨u1, by have := (List.getElem?_eq_some_iff.1 hm).1; omega, m, hm, hmt⟩
    · exact .inl ((h1 t).2 ⟨by omega, ho⟩)
  obtain ⟨es, c', hnf, ⟨f1, f2, f3, f4⟩, htr⟩ := scheduleV hRC hmsg (M.length - 0) (Nat.le_refl _) hI
  have hc : c' = cfg := by
    have hags : c'.pcAgs = cfg.pcAgs := by
      apply List.ext_getElem?
      intro j
      by_cases hj : j < N
      · obtain ⟨Q, u1, u2⟩ := f4 ⟨j, hj⟩
        rw [u1, hag ⟨j, hj⟩]
        have : Q = (ag ⟨j, hj⟩).paProm := setEq.2 u2
        subst this
        rfl
      · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]
    cases c'; cases cfg
    simp only at f1 f2 hags himg0
    subst f1 f2 hags himg0
    rfl
  subst hc
  refine ⟨es, ⟨hnf, hv.2⟩, fun h => ?_⟩
  rw [htr h]
  by_cases hN : h < N
  · simp only [hN, dif_pos]; rfl
  · simp only [hN, dif_neg, not_false_eq_true]
    exact (htrN h (by simp [pmInit]; omega)).symm

/-- **NF_R FOR THE A/D VARIANT, PLAN §3's RELEASE CLASS.** -/
theorem nfRAd {P : Type} {pstep : P → Unit → VLabel → P → Unit → Prop} {img : Image} {ps : List P}
    {evs : List VEvt} {cfg : PCfg P Unit} (hv : validRunV pstep img () ps evs cfg) :
    ∃ evs', nfRunV relClass pstep cfg.pcLog img () ps evs' cfg ∧ ∀ h, traceOfV h evs' = traceOfV h evs :=
  nfRAd_gen rcOk_plan hv

/-- **NF_R FOR THE A/D VARIANT, S4b3's PRE-STATE RELEASE CLASS.** -/
theorem nfRAd_pre {P : Type} {pstep : P → Unit → VLabel → P → Unit → Prop} {img : Image} {ps : List P}
    {evs : List VEvt} {cfg : PCfg P Unit} (hv : validRunV pstep img () ps evs cfg) :
    ∃ evs', nfRunV Pre.relClassPre pstep cfg.pcLog img () ps evs' cfg ∧ ∀ h, traceOfV h evs' = traceOfV h evs :=
  nfRAd_gen rcOk_pre hv

end Weak.Prom.Ad
