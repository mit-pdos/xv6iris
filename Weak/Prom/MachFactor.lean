/-
Weak/Prom: **the promises-first factorization of machine v2** (S0-P part (2), milestone 2b, statement 1; plan §0
`PF.validRun_factorL`, NA-12b; [R7.s1]).

  `validRun_factorL : validRun pstep img d0 ps evs cfg →
      validRun pstep img d0 ps (cfg.pcLog.map promEv ++ evs.filter PEvt.isSt) cfg`

Every message of the final memory is promised first, in log order, by its author; then every state event of the run
follows in its original order, with the same label and fulfil timestamp, and the run reaches the SAME final
configuration.  `validRun_factorL_trace` adds the plan's trace clause (every hart's trace is unchanged).  It holds
for ANY program half `pstep` and any device fabric `D` (promise steps leave `pcDev` alone), with no premise.

Proof: a simulation (`FRel`) between the given run's configuration `c` and the factored run's `c'`: same image,
fabric, program states and `PState`s; `c'`'s log is the final `M` (of which `c`'s log is a prefix); `c'`'s promise
set of agent `i` is `c`'s plus every own message of `M` above `|c.pcLog|`.  A state step of `c` is then a state
step of `c'` (`memStep_extend`): every arm is APPEND-STABLE (each window's upper end is a view or a fulfilled
timestamp, all `≤ |c.pcLog|` by `psBounded`, MachWf.lean) and OWN-PROMISE-MONOTONE (the promises added are above
`|c.pcLog|`; `ownDone`, the only other reader of the promise set, looks at timestamps `≤ |c.pcLog|`).
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Prom.MachWf

namespace Weak.Prom

open MachCSL MachCSL.Stdpp Iris.Std
open Weak (Image Dsrc)
open PLabel

/-! ## 1. Prefix facts -/

theorem prefix_getElem? {L M : List PMsg} (h : L <+: M) {k : Nat} (hk : k < L.length) : M[k]? = L[k]? := by
  obtain ⟨t, rfl⟩ := h
  exact List.getElem?_append_left hk

theorem memByte_ext {img : Image} {L M : List PMsg} {t : Nat} {a : Int} (h : L <+: M) (ht : t ≤ L.length) :
    memByte img M t a = memByte img L t a := by
  cases t with
  | zero => rfl
  | succ k => simp only [memByte]; rw [prefix_getElem? h (by omega)]

theorem writesIn_ext {L M : List PMsg} {a : Int} {lo hi : Nat} (h : L <+: M) (hhi : hi ≤ L.length) :
    writesIn M a lo hi ↔ writesIn L a lo hi := by
  unfold writesIn
  constructor
  · rintro ⟨t, h1, h2, m, hm, hb⟩
    exact ⟨t, h1, h2, m, by rw [← prefix_getElem? h (by omega)]; exact hm, hb⟩
  · rintro ⟨t, h1, h2, m, hm, hb⟩
    exact ⟨t, h1, h2, m, by rw [prefix_getElem? h (by omega)]; exact hm, hb⟩

theorem writesInBy_ext {L M : List PMsg} {Q : Option Nat → Prop} {a : Int} {lo hi : Nat} (h : L <+: M)
    (hhi : hi ≤ L.length) : writesInBy M Q a lo hi ↔ writesInBy L Q a lo hi := by
  unfold writesInBy
  constructor
  · rintro ⟨t, h1, h2, m, hm, hb⟩
    exact ⟨t, h1, h2, m, by rw [← prefix_getElem? h (by omega)]; exact hm, hb⟩
  · rintro ⟨t, h1, h2, m, hm, hb⟩
    exact ⟨t, h1, h2, m, by rw [prefix_getElem? h (by omega)]; exact hm, hb⟩

theorem exclOk_ext {L M : List PMsg} {i ts : Nat} (h : L <+: M) (hts : ts ≤ L.length) :
    ∀ (a : Int) (l : List Nat), exclOk M i a l ts ↔ exclOk L i a l ts
  | _, [] => Iff.rfl
  | a, t :: r => by
    simp only [exclOk]
    rw [writesInBy_ext h (by omega), exclOk_ext h hts (a + 1) r]

theorem cmoAt_ext {L M : List PMsg} {p : CmoKind → Bool} {t : Nat} {a : Int} (h : L <+: M)
    (ht : t - 1 < L.length) : cmoAt M p t a ↔ cmoAt L p t a := by
  unfold cmoAt
  rw [prefix_getElem? h ht]

theorem cmoAt_lt {L : List PMsg} {p : CmoKind → Bool} {t : Nat} {a : Int} (h : cmoAt L p t a) :
    t - 1 < L.length := by
  obtain ⟨m, _, _, hm, _⟩ := h
  exact (List.getElem?_eq_some_iff.1 hm).1

theorem invalRead_ext {L M : List PMsg} {a : Int} {t fl : Nat} (h : L <+: M) (hfl : fl ≤ L.length)
    (hr : invalRead L a t fl) : invalRead M a t fl := by
  obtain ⟨ti, hc, hlt, hnw, hno, hall⟩ := hr
  have hti := cmoAt_lt hc
  refine ⟨ti, (cmoAt_ext h hti).2 hc, hlt, ?_, ?_, ?_⟩
  · rw [writesIn_ext h hfl]; exact hnw
  · rintro ⟨ti', h1, h2, hc'⟩
    exact hno ⟨ti', h1, h2, (cmoAt_ext h (by omega)).1 hc'⟩
  · intro c hc1 hc2
    rw [writesIn_ext h (by omega)]
    exact hall c hc1 ((cmoAt_ext h (by omega)).1 hc2)

theorem nonFwdMax_le {ws : PState} {base : Int} {tvs : List (Nat × BitVec 8)} {n : Nat}
    (hts : bytesAll (fun _ t _ => t ≤ n) base tvs) : nonFwdMax ws base tvs ≤ n :=
  bytesMax_le base tvs (bytesAll_mono (fun a t _ ht => by split <;> omega) base tvs hts)

/-- A READ IS APPEND-STABLE: admissible against `L`, it is admissible against any extension `M`. -/
theorem loadOk_ext {img : Image} {L M : List PMsg} {ws : PState} {vpre : Nat} {base : Int}
    {tvs : List (Nat × BitVec 8)} (h : L <+: M) (hv : vpre ≤ L.length) (hc : ∀ a, coh ws a ≤ L.length)
    (hok : loadOk img L ws vpre base tvs) : loadOk img M ws vpre base tvs := by
  have hN : nonFwdMax ws base tvs ≤ L.length := nonFwdMax_le (loadOk_ts hok)
  unfold loadOk at hok ⊢
  refine bytesAll_mono (fun a t v hp => ?_) base tvs hok
  obtain ⟨hm, hr⟩ := hp
  have ht := memByte_le hm
  refine ⟨by rw [memByte_ext h ht]; exact hm, ?_⟩
  have hca := hc a
  rcases hr with hr | hr
  · left
    rw [writesIn_ext h (by split <;> omega)]
    exact hr
  · right
    exact invalRead_ext h (by omega) hr

theorem ownDone_ext {L M : List PMsg} {i : Nat} {P prom : GSet Nat} {t : Nat} (h : L <+: M)
    (ht : t ≤ L.length) (hP : ∀ t, t ≤ L.length → (t ∈ P ↔ t ∈ prom)) :
    ownDone M i P t = ownDone L i prom t := by
  unfold ownDone
  rcases Nat.eq_zero_or_pos t with h0 | h0
  · subst h0
    cases M[0 - 1]? <;> cases L[0 - 1]? <;> simp
  · rw [prefix_getElem? h (by omega)]
    cases L[t - 1]? with
    | none => rfl
    | some m =>
      simp only
      rw [decide_eq_decide.2 (hP t ht)]

theorem bytesMax_congr {f g : Int → Nat → Nat} :
    ∀ (a : Int) (l : List (Nat × BitVec 8)), bytesAll (fun a t _ => f a t = g a t) a l →
      bytesMax f a l = bytesMax g a l
  | _, [], _ => rfl
  | a, (t, _) :: r, ⟨h1, h2⟩ => by
    simp only [bytesMax]
    rw [h1, bytesMax_congr (a + 1) r h2]

/-! ## 2. Every arm is append-stable and own-promise-monotone -/

/-- THE ARM LEMMA ([R7.s1]): a state step against the log `L` (a prefix of `M`), with the bounds of `cfgWf`, is a
state step against `M` with the same label, fulfil timestamp and post-state, from any promise set `P` that is
`prom` plus timestamps above `|L|`; the post promise set is again `prom'` plus the same timestamps. -/
theorem memStep_extend {img : Image} {L M : List PMsg} {i : Nat} {prom : GSet Nat} {ws : PState} {l : PLabel}
    {ots : Option Nat} {ws' : PState} {prom' : GSet Nat} (P : GSet Nat) (Q : Nat → Prop)
    (h : memStep img L i prom ws l ots ws' prom') (hpre : L <+: M) (hb : psBounded ws L.length)
    (hw : promWf L i prom) (hP : ∀ t, t ∈ P ↔ t ∈ prom ∨ (L.length < t ∧ Q t)) :
    ∃ P', memStep img M i P ws l ots ws' P' ∧ ∀ t, t ∈ P' ↔ t ∈ prom' ∨ (L.length < t ∧ Q t) := by
  have hsv : ∀ s, srcsView ws s ≤ L.length := srcsView_le hb.2.2.2.2.2.2.2.1 hb.2.2.2.2.2.2.2.2.2.1
  have hcoh : ∀ a, coh ws a ≤ L.length := hb.1
  have hPin : ∀ t, t ∈ prom → t ∈ P := fun t ht => (hP t).2 (.inl ht)
  have hPdiff : ∀ ts, ts ≤ L.length → ∀ t, t ∈ P \ {ts} ↔ t ∈ prom \ {ts} ∨ (L.length < t ∧ Q t) := by
    intro ts hts t
    rw [elemOfDifference, elemOfDifference, hP t, elemOfSingleton]
    constructor
    · rintro ⟨h1 | h1, h2⟩
      · exact .inl ⟨h1, h2⟩
      · exact .inr h1
    · rintro (⟨h1, h2⟩ | h1)
      · exact ⟨.inl h1, h2⟩
      · exact ⟨.inr h1, by have := h1.1; omega⟩
  have hmsg : ∀ ts m, ts ∈ prom → L[ts - 1]? = some m → M[ts - 1]? = some m := by
    intro ts m hts hm
    have := (hw ts hts).2.1
    have := (hw ts hts).1
    rw [prefix_getElem? hpre (by omega)]
    exact hm
  cases h with
  | silent => exact ⟨P, .silent _ _, hP⟩
  | load aq rl base tvs asrc hok =>
    exact ⟨P, .load _ _ _ _ _ _ _ (loadOk_ext hpre (ldPre_le hb (hsv _)) hcoh hok), hP⟩
  | store aq rl base data asrc vsrc ts hts hm hc hpv =>
    exact ⟨P \ {ts}, .store _ _ _ _ _ _ _ _ _ (hPin ts hts) (hmsg ts _ hts hm) hc hpv,
      hPdiff ts (hw ts hts).2.1⟩
  | rmw aq rl base tvs data asrc vsrc ts hlen hts hm hok hx hc hpv =>
    have hts' := (hw ts hts).2.1
    exact ⟨P \ {ts}, .rmw _ _ _ _ _ _ _ _ _ _ hlen (hPin ts hts) (hmsg ts _ hts hm)
      (loadOk_ext hpre (ldPre_le hb (hsv _)) hcoh hok) ((exclOk_ext hpre hts' _ _).2 hx) hc hpv,
      hPdiff ts hts'⟩
  | amoLd aq base tvs asrc hok =>
    exact ⟨P, .amoLd _ _ _ _ _ _ (loadOk_ext hpre (ldPre_le hb (hsv _)) hcoh hok), hP⟩
  | amoSt rl base data asrc vsrc ts R hR hb' hlen hts hm hx hc hpv =>
    have hts' := (hw ts hts).2.1
    exact ⟨P \ {ts}, .amoSt _ _ _ _ _ _ _ _ R hR hb' hlen (hPin ts hts) (hmsg ts _ hts hm)
      ((exclOk_ext hpre hts' _ _).2 hx) hc hpv, hPdiff ts hts'⟩
  | fence => exact ⟨P, .fence _ _ _ _ _ _, hP⟩
  | fenceI => exact ⟨P, .fenceI _ _, hP⟩
  | dev => exact ⟨P, .dev _ _ _ _ _ _ _, hP⟩
  | regW rd srcs => exact ⟨P, .regW _ _ _ _, hP⟩
  | ctrl srcs => exact ⟨P, .ctrl _ _ _, hP⟩
  | instr => exact ⟨P, .instr _ _, hP⟩
  | lr aq rl base tvs asrc hok =>
    exact ⟨P, .lr _ _ _ _ _ _ _ (loadOk_ext hpre (ldPre_le hb (hsv _)) hcoh hok), hP⟩
  | sc aq rl base data asrc vsrc ts R hR hts hm hx hlt hc hpv =>
    have hts' := (hw ts hts).2.1
    exact ⟨P \ {ts}, .sc _ _ _ _ _ _ _ _ _ R hR (hPin ts hts) (hmsg ts _ hts hm)
      ((exclOk_ext hpre hts' _ _).2 hx) hlt hc hpv, hPdiff ts hts'⟩
  | scFail => exact ⟨P, .scFail _ _, hP⟩
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
    have e : fetchView M i P base tvs = fetchView L i prom base tvs := by
      unfold fetchView
      refine bytesMax_congr base tvs (bytesAll_mono (fun a t _ ht => ?_) base tvs hts)
      rw [ownDone_ext hpre ht hlow]
    refine ⟨P, ?_, hP⟩
    rw [← e]
    exact .fetch _ _ _ _ hok'
  | cmo k base len asrc ts hts hm hc hpv =>
    exact ⟨P \ {ts}, .cmo _ _ _ _ _ _ _ (hPin ts hts) (hmsg ts _ hts hm) hc hpv, hPdiff ts (hw ts hts).2.1⟩

/-! ## 3. The simulation -/

/-- Is the event a state step? -/
def PEvt.isSt : PEvt → Bool
  | .st .. => true
  | .prom .. => false

/-- The promise event of a message by its author. -/
def promEv (m : PMsg) : PEvt := .prom (m.tid.getD 0) m

/-- `t` is the timestamp of an own message of agent `i` in `M`. -/
def ownTs (M : List PMsg) (i t : Nat) : Prop := ∃ m, M[t - 1]? = some m ∧ m.tid = some i

/-- THE SIMULATION RELATION between the given run's configuration `c` and the factored run's `c'`. -/
structure FRel {P D : Type} (M : List PMsg) (c c' : PCfg P D) : Prop where
  img : c'.pcImg = c.pcImg
  log : c'.pcLog = M
  dev : c'.pcDev = c.pcDev
  pre : c.pcLog <+: M
  len : c'.pcAgs.length = c.pcAgs.length
  ags : ∀ i ag, c.pcAgs[i]? = some ag → ∃ ag', c'.pcAgs[i]? = some ag' ∧ ag'.paSt = ag.paSt ∧
    ag'.paWs = ag.paWs ∧ ∀ t, t ∈ ag'.paProm ↔ t ∈ ag.paProm ∨ (c.pcLog.length < t ∧ ownTs M i t)

theorem ownTs_shift {L M : List PMsg} {m : PMsg} (h : L ++ [m] <+: M) (j t : Nat) :
    (L.length < t ∧ ownTs M j t) ↔
      ((t = L.length + 1 ∧ m.tid = some j) ∨ (L.length + 1 < t ∧ ownTs M j t)) := by
  have hM : M[L.length]? = some m := by
    rw [prefix_getElem? h (by simp)]
    simp
  constructor
  · rintro ⟨h1, m', hm', ht⟩
    by_cases e : t = L.length + 1
    · subst e
      simp only [Nat.add_sub_cancel] at hm'
      rw [hM] at hm'
      cases hm'
      exact .inl ⟨rfl, ht⟩
    · exact .inr ⟨by omega, m', hm', ht⟩
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · subst h1
      exact ⟨by omega, m, by simpa using hM, h2⟩
    · exact ⟨by omega, h2⟩

theorem getElem?_set_eq_of {α : Type} {l : List α} {i : Nat} {a b : α} (h : l[i]? = some a) :
    (l.set i b)[i]? = some b := by
  rw [List.getElem?_set_self]
  exact (List.getElem?_eq_some_iff.1 h).1

theorem sim {P D : Type} {pstep : P → D → PLabel → P → D → Prop} {M : List PMsg} :
    ∀ {c cfg : PCfg P D} {evs : List PEvt}, pmSteps pstep c evs cfg → runWf c → cfg.pcLog = M →
      ∀ {c' : PCfg P D}, FRel M c c' → ∃ c'', pmSteps pstep c' (evs.filter PEvt.isSt) c'' ∧ FRel M cfg c'' := by
  intro c cfg evs hrun
  induction hrun with
  | refl => intro _ _ c' hfr; exact ⟨c', .refl _, hfr⟩
  | step c0 c1 c2 e es hst hrest ih =>
    intro hwf hM c' hfr
    have hwf1 := pmStep_wf hst hwf
    have hpre1 : c1.pcLog <+: M := hM ▸ pmSteps_prefix hrest
    cases hst with
    | promise i ag m hag hnt htid =>
      have hpre' : c0.pcLog ++ [m] <+: M := hpre1
      have hfr1 : FRel M ⟨c0.pcImg, c0.pcLog ++ [m], c0.pcDev,
          c0.pcAgs.set i ⟨ag.paSt, ag.paWs, {c0.pcLog.length + 1} ∪ ag.paProm⟩⟩ c' := by
        refine ⟨hfr.img, hfr.log, hfr.dev, hpre', by simp [hfr.len], fun j ag1 hj => ?_⟩
        simp only at hj
        rcases getElem?_set_of hj with ⟨hij, hb, _⟩ | ⟨hij, hj'⟩
        · subst hij hb
          obtain ⟨ag', h1, h2, h3, h4⟩ := hfr.ags i ag hag
          refine ⟨ag', h1, h2, h3, fun t => ?_⟩
          simp only [List.length_append, List.length_singleton]
          rw [h4 t, ownTs_shift hpre' i t, elemOfUnion, elemOfSingleton]
          constructor
          · rintro (h | ⟨h, _⟩ | h)
            · exact .inl (.inr h)
            · exact .inl (.inl h)
            · exact .inr h
          · rintro ((h | h) | h)
            · exact .inr (.inl ⟨h, htid⟩)
            · exact .inl h
            · exact .inr (.inr h)
        · obtain ⟨ag', h1, h2, h3, h4⟩ := hfr.ags j ag1 hj'
          refine ⟨ag', h1, h2, h3, fun t => ?_⟩
          simp only [List.length_append, List.length_singleton]
          rw [h4 t, ownTs_shift hpre' j t]
          constructor
          · rintro (h | ⟨_, h⟩ | h)
            · exact .inl h
            · rw [htid] at h; cases h; exact absurd rfl hij
            · exact .inr h
          · rintro (h | h)
            · exact .inl h
            · exact .inr (.inr h)
      obtain ⟨c'', hs, hfr''⟩ := ih hwf1 hM hfr1
      exact ⟨c'', by simpa [PEvt.isSt] using hs, hfr''⟩
    | state i ag l ots st' d' ws' prom' hag hp hm =>
      obtain ⟨ag', h1, h2, h3, h4⟩ := hfr.ags i ag hag
      obtain ⟨hb, hw⟩ := hwf.1 i ag hag
      obtain ⟨P', hm', hP'⟩ := memStep_extend ag'.paProm (ownTs M i) hm hfr.pre hb hw h4
      have hstep : pmStep pstep c' (.st i l ots)
          ⟨c'.pcImg, c'.pcLog, d', c'.pcAgs.set i ⟨st', ws', P'⟩⟩ := by
        refine .state c' i ag' l ots st' d' ws' P' h1 ?_ ?_
        · rw [h2, hfr.dev]; exact hp
        · rw [hfr.img, hfr.log, h3]; exact hm'
      have hfr1 : FRel M ⟨c0.pcImg, c0.pcLog, d', c0.pcAgs.set i ⟨st', ws', prom'⟩⟩
          ⟨c'.pcImg, c'.pcLog, d', c'.pcAgs.set i ⟨st', ws', P'⟩⟩ := by
        refine ⟨hfr.img, hfr.log, rfl, hfr.pre, by simp [hfr.len], fun j ag1 hj => ?_⟩
        simp only at hj
        rcases getElem?_set_of hj with ⟨hij, hb, _⟩ | ⟨hij, hj'⟩
        · subst hij hb
          exact ⟨⟨st', ws', P'⟩, getElem?_set_eq_of h1, rfl, rfl, hP'⟩
        · obtain ⟨ag2, k1, k2, k3, k4⟩ := hfr.ags j ag1 hj'
          exact ⟨ag2, by simp only [List.getElem?_set_ne hij]; exact k1, k2, k3, k4⟩
      obtain ⟨c'', hs, hfr''⟩ := ih hwf1 hM hfr1
      exact ⟨c'', by simpa [PEvt.isSt] using pmSteps.step _ _ _ _ _ hstep hs, hfr''⟩

/-! ## 4. The promise phase -/

theorem promsRun {P D : Type} {pstep : P → D → PLabel → P → D → Prop} :
    ∀ (Ms : List PMsg) (c : PCfg P D), (∀ m ∈ Ms, msgOk c.pcAgs.length m) →
      ∃ c', pmSteps pstep c (Ms.map promEv) c' ∧ c'.pcImg = c.pcImg ∧ c'.pcLog = c.pcLog ++ Ms ∧
        c'.pcDev = c.pcDev ∧ c'.pcAgs.length = c.pcAgs.length ∧
        ∀ i ag, c.pcAgs[i]? = some ag → ∃ ag', c'.pcAgs[i]? = some ag' ∧ ag'.paSt = ag.paSt ∧
          ag'.paWs = ag.paWs ∧
          ∀ t, t ∈ ag'.paProm ↔ t ∈ ag.paProm ∨ (c.pcLog.length < t ∧ ownTs (c.pcLog ++ Ms) i t)
  | [], c, _ => by
    refine ⟨c, .refl _, rfl, by simp, rfl, rfl, fun i ag h => ⟨ag, h, rfl, rfl, fun t => ?_⟩⟩
    constructor
    · exact .inl
    · rintro (h | ⟨h1, m, hm, _⟩)
      · exact h
      · simp only [List.append_nil] at hm
        rw [List.getElem?_eq_none (by omega)] at hm
        cases hm
  | m :: Ms, c, hok => by
    obtain ⟨hnt, i, htid, hi⟩ := hok m (by simp)
    have hag : c.pcAgs[i]? = some c.pcAgs[i] := List.getElem?_eq_getElem hi
    let c1 : PCfg P D := ⟨c.pcImg, c.pcLog ++ [m], c.pcDev,
      c.pcAgs.set i ⟨c.pcAgs[i].paSt, c.pcAgs[i].paWs, {c.pcLog.length + 1} ∪ c.pcAgs[i].paProm⟩⟩
    have hst : pmStep pstep c (.prom i m) c1 := pmStep.promise c i c.pcAgs[i] m hag hnt htid
    obtain ⟨c', hs, himg, hlog, hdev, hlen, hags⟩ := promsRun (pstep := pstep) Ms c1 (fun m' hm' => by
      simp only [c1, List.length_set]; exact hok m' (by simp [hm']))
    have hev : promEv m = .prom i m := by simp [promEv, htid]
    have hpre : c.pcLog ++ [m] <+: c.pcLog ++ m :: Ms := ⟨Ms, by simp⟩
    have hlogeq : c.pcLog ++ [m] ++ Ms = c.pcLog ++ m :: Ms := by simp
    refine ⟨c', ?_, himg, by simp [hlog, c1], hdev, by simp [hlen, c1], fun j ag hj => ?_⟩
    · rw [List.map_cons, hev]; exact .step _ _ _ _ _ hst hs
    · by_cases hij : i = j
      · subst hij
        have hj1 : c1.pcAgs[i]? =
            some ⟨c.pcAgs[i].paSt, c.pcAgs[i].paWs, {c.pcLog.length + 1} ∪ c.pcAgs[i].paProm⟩ :=
          getElem?_set_eq_of hag
        obtain ⟨ag', h1, h2, h3, h4⟩ := hags i _ hj1
        rw [hag] at hj
        cases hj
        refine ⟨ag', h1, h2, h3, fun t => ?_⟩
        rw [h4 t]
        simp only [c1, List.length_append, List.length_singleton]
        rw [hlogeq, ownTs_shift hpre i t, elemOfUnion, elemOfSingleton]
        constructor
        · rintro ((h | h) | h)
          · exact .inr (.inl ⟨h, htid⟩)
          · exact .inl h
          · exact .inr (.inr h)
        · rintro (h | ⟨h, _⟩ | h)
          · exact .inl (.inr h)
          · exact .inl (.inl h)
          · exact .inr h
      · have hj1 : c1.pcAgs[j]? = some ag := by
          simp only [c1]; rw [List.getElem?_set_ne hij]; exact hj
        obtain ⟨ag', h1, h2, h3, h4⟩ := hags j _ hj1
        refine ⟨ag', h1, h2, h3, fun t => ?_⟩
        rw [h4 t]
        simp only [c1, List.length_append, List.length_singleton]
        rw [hlogeq, ownTs_shift hpre j t]
        constructor
        · rintro (h | h)
          · exact .inl h
          · exact .inr (.inr h)
        · rintro (h | ⟨_, h⟩ | h)
          · exact .inl h
          · rw [htid] at h; cases h; exact absurd rfl hij
          · exact .inr h

theorem pmSteps_append {P D : Type} {pstep : P → D → PLabel → P → D → Prop} {c c1 c2 : PCfg P D}
    {es1 es2 : List PEvt} (h1 : pmSteps pstep c es1 c1) (h2 : pmSteps pstep c1 es2 c2) :
    pmSteps pstep c (es1 ++ es2) c2 := by
  induction h1 with
  | refl => exact h2
  | step _ _ _ _ _ hs _ ih => exact .step _ _ _ _ _ hs (ih h2)

theorem FRel_final {P D : Type} {M : List PMsg} {cfg c : PCfg P D} (h : FRel M cfg c) (hM : cfg.pcLog = M) :
    c = cfg := by
  have hA : c.pcAgs = cfg.pcAgs := by
    apply List.ext_getElem?
    intro j
    cases hj : cfg.pcAgs[j]? with
    | none =>
      have := List.getElem?_eq_none_iff.1 hj
      exact List.getElem?_eq_none (by rw [h.len]; exact this)
    | some ag =>
      obtain ⟨ag', h1, h2, h3, h4⟩ := h.ags j ag hj
      rw [h1]
      have hp : ag'.paProm = ag.paProm := by
        apply Std.ExtTreeSet.ext_mem
        intro t
        rw [h4 t]
        constructor
        · rintro (h | ⟨h1, m, hm, _⟩)
          · exact h
          · rw [← hM, List.getElem?_eq_none (by omega)] at hm; cases hm
        · exact .inl
      cases ag'; cases ag
      simp only at h2 h3 hp
      subst h2 h3 hp
      rfl
  have hi := h.img
  have hl := h.log
  have hd := h.dev
  cases c; cases cfg
  simp only at hi hl hd hA hM
  subst hi hd hA
  rw [hl, hM]

/-! ## 5. The factorization -/

/-- **`PF.validRun_factorL` (plan §0, NA-12b), machine v2**: every valid run factors as all promises first (each
message of the final memory by its author, in log order), then the run's state events in their order, reaching
the same final configuration. -/
theorem validRun_factorL {P D : Type} {pstep : P → D → PLabel → P → D → Prop} {img : Image} {d0 : D}
    {ps : List P} {evs : List PEvt} {cfg : PCfg P D} (h : validRun pstep img d0 ps evs cfg) :
    validRun pstep img d0 ps (cfg.pcLog.map promEv ++ evs.filter PEvt.isSt) cfg := by
  obtain ⟨hrun, hno⟩ := h
  have hwf := pmSteps_wf hrun (pmInit_wf img d0 ps)
  have hlen := pmSteps_len hrun
  obtain ⟨c0', hp, himg, hlog, hdev, hlen', hags⟩ := promsRun (pstep := pstep) cfg.pcLog
    (pmInit img d0 ps) (fun m hm => by rw [← hlen]; exact hwf.2 m hm)
  have hfr : FRel cfg.pcLog (pmInit img d0 ps) c0' := by
    refine ⟨himg, by rw [hlog]; rfl, hdev, List.nil_prefix, hlen', fun i ag hi => ?_⟩
    obtain ⟨ag', h1, h2, h3, h4⟩ := hags i ag hi
    exact ⟨ag', h1, h2, h3, fun t => by rw [h4 t]; rfl⟩
  obtain ⟨c'', hs, hfr''⟩ := sim hrun (pmInit_wf img d0 ps) rfl hfr
  have he := FRel_final hfr'' rfl
  subst he
  exact ⟨pmSteps_append hp hs, hno⟩

theorem traceOf_append (h : Nat) : ∀ (a b : List PEvt), traceOf h (a ++ b) = traceOf h a ++ traceOf h b
  | [], _ => rfl
  | .prom _ _ :: a, b => by simp only [List.cons_append, traceOf]; exact traceOf_append h a b
  | .st i l o :: a, b => by
    simp only [List.cons_append, traceOf]
    split <;> simp [traceOf_append h a b]

theorem traceOf_proms (h : Nat) : ∀ Ms : List PMsg, traceOf h (Ms.map promEv) = []
  | [] => rfl
  | _ :: Ms => by simp only [List.map_cons, promEv, traceOf]; exact traceOf_proms h Ms

theorem traceOf_filter (h : Nat) : ∀ evs : List PEvt, traceOf h (evs.filter PEvt.isSt) = traceOf h evs
  | [] => rfl
  | .prom _ _ :: es => by simp only [List.filter_cons, PEvt.isSt, traceOf]; exact traceOf_filter h es
  | .st i l o :: es => by
    simp only [List.filter_cons, PEvt.isSt, if_true, traceOf]
    split <;> simp [traceOf_filter h es]

/-- The plan's form (§0): a promises-first run with the same final configuration and the same per-hart traces. -/
theorem validRun_factorL_trace {P D : Type} {pstep : P → D → PLabel → P → D → Prop} {img : Image} {d0 : D}
    {ps : List P} {evs : List PEvt} {cfg : PCfg P D} (h : validRun pstep img d0 ps evs cfg) :
    ∃ evs', validRun pstep img d0 ps evs' cfg ∧ evs' = cfg.pcLog.map promEv ++ evs.filter PEvt.isSt ∧
      ∀ hh, traceOf hh evs' = traceOf hh evs :=
  ⟨_, validRun_factorL h, rfl, fun hh => by rw [traceOf_append, traceOf_proms, traceOf_filter]; rfl⟩

end Weak.Prom
