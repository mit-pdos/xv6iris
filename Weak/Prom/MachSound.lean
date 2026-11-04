/-
Weak/Prom: **soundness of the label-level explorer of machine v2** (S0-P part (2), milestone 2, [R5.s5]).

* `explorerStep_sound` — every successor `Mach.succ` lists is a `memStep` of machine v2 (Machine.lean), with the
  successor's label, fulfil timestamp, post-state and promise set.
* `memStepF` — the memory half of a state step as a FUNCTION of the full label and fulfil timestamp (the run
  certificate checker's step, `Weak/Prom/MachCert.lean`), and `memStepF_sound`: `memStepF … = some (ws', prom')`
  implies `memStep … ws' prom'`.  MachFix-R-b5: a load-like step takes the absorbed invalidate view `vi = 0`;
  `memStepL` (every `vi`, `viOpts`) is the list of every step, `memStepL_sound`.

Both rest on the Bool ↔ Prop lemmas of §1 (one per transcribed premise of MachExplore.lean §1, plus
`ExtTreeSet.contains ↔ ∈`); post-states are Machine.lean's own functions, so they agree by definition.  Nothing here
is trusted beyond Machine.lean's definitions: no `sorry`, no axiom, no `native_decide`.

Completeness of the explorer (milestone 2b) is NOT proved here; the statements are listed in PROGRESS-S0P2.md.
-/
import Weak.Prom.MachExplore

namespace Weak.Prom.Mach

open MachCSL MachCSL.Stdpp Iris.Std
open Weak (Image Dsrc)
open Weak.Prom
open PLabel

/-! ## 1. Bool ↔ Prop -/

theorem writesInB_iff (log : List PMsg) (a : Int) (lo hi : Nat) :
    writesInB log a lo hi = true ↔ writesIn log a lo hi := by
  unfold writesInB writesIn
  simp only [List.any_eq_true, List.mem_range'_1]
  constructor
  · rintro ⟨t, ⟨h1, h2⟩, h3⟩
    refine ⟨t, by omega, by omega, ?_⟩
    cases hm : log[t - 1]? with
    | none => simp only [hm] at h3; cases h3
    | some m => simp only [hm] at h3; exact ⟨m, rfl, h3⟩
  · rintro ⟨t, h1, h2, m, hm, hb⟩
    exact ⟨t, ⟨by omega, by omega⟩, by simp only [hm]; exact hb⟩

theorem writesInOtherB_iff (log : List PMsg) (i : Nat) (a : Int) (lo hi : Nat) :
    writesInOtherB log i a lo hi = true ↔ writesInBy log (fun tid => tid ≠ some i) a lo hi := by
  unfold writesInOtherB writesInBy
  simp only [List.any_eq_true, List.mem_range'_1]
  constructor
  · rintro ⟨t, ⟨h1, h2⟩, h3⟩
    refine ⟨t, by omega, by omega, ?_⟩
    cases hm : log[t - 1]? with
    | none => simp only [hm] at h3; cases h3
    | some m =>
      simp only [hm, Bool.and_eq_true, decide_eq_true_eq] at h3
      exact ⟨m, rfl, h3.1, h3.2⟩
  · rintro ⟨t, h1, h2, m, hm, hb, ht⟩
    refine ⟨t, ⟨by omega, by omega⟩, ?_⟩
    simp only [hm, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨hb, ht⟩

theorem exclOkB_iff (log : List PMsg) (i : Nat) (ts : Nat) :
    ∀ (a : Int) (l : List Nat), exclOkB log i a l ts = true ↔ exclOk log i a l ts := by
  intro a l
  induction l generalizing a with
  | nil => simp [exclOkB, exclOk]
  | cons t r ih =>
    simp only [exclOkB, exclOk, Bool.and_eq_true, Bool.not_eq_true', ih]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨fun h => ?_, h2⟩
      rw [← writesInOtherB_iff] at h
      rw [h] at h1; cases h1
    · rintro ⟨h1, h2⟩
      refine ⟨?_, h2⟩
      cases hb : writesInOtherB log i a t (ts - 1) with
      | false => rfl
      | true => exact absurd ((writesInOtherB_iff ..).1 hb) h1

theorem cmoAtB_iff (log : List PMsg) (p : CmoKind → Bool) (t : Nat) (a : Int) :
    cmoAtB log p t a = true ↔ cmoAt log p t a := by
  unfold cmoAtB cmoAt
  cases hm : log[t - 1]? with
  | none => simp
  | some m =>
    constructor
    · intro h
      simp only at h
      revert h
      cases hc : m.cls <;> intro h <;> simp only [hc, Bool.and_eq_true, decide_eq_true_eq, reduceCtorEq] at h
      case cmo k len => exact ⟨m, k, len, rfl, hc, h.1.1, h.1.2, h.2⟩
    · rintro ⟨m', k', len', hm', hc', h1, h2, h3⟩
      cases hm'
      simp only [hc', Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨⟨h1, h2⟩, h3⟩

theorem not_writesIn_of_B {log : List PMsg} {a : Int} {lo hi : Nat} (h : (!writesInB log a lo hi) = true) :
    ¬ writesIn log a lo hi := by
  intro hw
  rw [← writesInB_iff] at hw
  rw [hw] at h; cases h

theorem invalReadB_sound {log : List PMsg} {a : Int} {t fl : Nat} (h : invalReadB log a t fl = true) :
    invalRead log a t fl := by
  unfold invalReadB at h
  simp only [List.any_eq_true, List.mem_range'_1, Bool.and_eq_true] at h
  obtain ⟨ti, ⟨h1, h2⟩, ⟨⟨hc, hw⟩, hn⟩, hall⟩ := h
  refine ⟨ti, (cmoAtB_iff ..).1 hc, by omega, not_writesIn_of_B hw, ?_, ?_⟩
  · rintro ⟨ti', h3, h4, hc'⟩
    have hb := (cmoAtB_iff ..).2 hc'
    have hany : (List.range' (ti + 1) (max fl ti - ti)).any (fun ti' => cmoAtB log isInvalK ti' a) = true :=
      List.any_eq_true.2 ⟨ti', List.mem_range'_1.2 ⟨by omega, by omega⟩, hb⟩
    rw [hany] at hn; cases hn
  · intro c hc1 hc2
    have := List.all_eq_true.1 hall c (List.mem_range.2 hc1)
    simp only [Bool.or_eq_true] at this
    rcases this with h5 | h5
    · have hb := (cmoAtB_iff ..).2 hc2
      rw [hb] at h5; cases h5
    · exact not_writesIn_of_B h5

theorem bytesAllB_sound {P : Int → Nat → BitVec 8 → Bool} {Q : Int → Nat → BitVec 8 → Prop}
    (hPQ : ∀ a t v, P a t v = true → Q a t v) :
    ∀ (a : Int) (l : List (Nat × BitVec 8)), bytesAllB P a l = true → bytesAll Q a l := by
  intro a l
  induction l generalizing a with
  | nil => intro _; trivial
  | cons tv r ih =>
    obtain ⟨t, v⟩ := tv
    intro h
    simp only [bytesAllB, Bool.and_eq_true] at h
    exact ⟨hPQ a t v h.1, ih (a + 1) h.2⟩

theorem loadOkB_sound {img : Image} {log : List PMsg} {ws : PState} {vpre : Nat} {base : Int}
    {tvs : List (Nat × BitVec 8)} (h : loadOkB img log ws vpre base tvs = true) :
    loadOk img log ws vpre base tvs := by
  unfold loadOkB at h
  unfold loadOk
  refine bytesAllB_sound (fun a t v hp => ?_) base tvs h
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hp
  refine ⟨hp.1, ?_⟩
  rcases hp.2 with h2 | h2
  · exact .inl (not_writesIn_of_B h2)
  · exact .inr (invalReadB_sound h2)

/-- MachFix-R-b5. -/
theorem invalReadAtB_sound {log : List PMsg} {a : Int} {t fl ti : Nat} (h : invalReadAtB log a t fl ti = true) :
    invalReadAt log a t fl ti := by
  unfold invalReadAtB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hc, hlt⟩, hw⟩, hn⟩, hall⟩ := h
  refine ⟨(cmoAtB_iff ..).1 hc, hlt, not_writesIn_of_B hw, ?_, ?_⟩
  · rintro ⟨ti', h3, h4, hc'⟩
    have hb := (cmoAtB_iff ..).2 hc'
    have hany : (List.range' (ti + 1) (max fl ti - ti)).any (fun ti' => cmoAtB log isInvalK ti' a) = true :=
      List.any_eq_true.2 ⟨ti', List.mem_range'_1.2 ⟨by omega, by omega⟩, hb⟩
    rw [hany] at hn; cases hn
  · intro c hc1 hc2
    have := List.all_eq_true.1 hall c (List.mem_range.2 hc1)
    simp only [Bool.or_eq_true] at this
    rcases this with h5 | h5
    · have hb := (cmoAtB_iff ..).2 hc2
      rw [hb] at h5; cases h5
    · exact not_writesIn_of_B h5

/-- MachFix-R-b5. -/
theorem bytesAnyB_sound {P : Int → Nat → BitVec 8 → Bool} {Q : Int → Nat → BitVec 8 → Prop}
    (hPQ : ∀ a t v, P a t v = true → Q a t v) :
    ∀ (a : Int) (l : List (Nat × BitVec 8)), bytesAnyB P a l = true → bytesAny Q a l := by
  intro a l
  induction l generalizing a with
  | nil => intro h; cases h
  | cons tv r ih =>
    obtain ⟨t, v⟩ := tv
    intro h
    simp only [bytesAnyB, Bool.or_eq_true] at h
    rcases h with h | h
    · exact .inl (hPQ a t v h)
    · exact .inr (ih (a + 1) h)

/-- MachFix-R-b5. -/
theorem invalCiteB_sound {log : List PMsg} {ws : PState} {vpre vi : Nat} {base : Int}
    {tvs : List (Nat × BitVec 8)} (h : invalCiteB log ws vpre vi base tvs = true) :
    invalCite log ws vpre vi base tvs := by
  unfold invalCiteB at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨bytesAllB_sound (fun a t v hp => ?_) base tvs h1, ?_⟩
  · simp only [Bool.or_eq_true] at hp
    rcases hp with hp | hp
    · exact .inl (not_writesIn_of_B hp)
    · obtain ⟨ti, hti, hr⟩ := List.any_eq_true.1 hp
      exact .inr ⟨ti, by have := List.mem_range.1 hti; omega, invalReadAtB_sound hr⟩
  · rcases h2 with h2 | h2
    · exact .inl h2
    · exact .inr (bytesAnyB_sound (fun a t v hp => invalReadAtB_sound hp) base tvs h2)

/-- MachFix-R-b5. -/
theorem viOpts_sound {log : List PMsg} {ws : PState} {vpre vi : Nat} {base : Int}
    {tvs : List (Nat × BitVec 8)} (h : vi ∈ viOpts log ws vpre base tvs) : invalCite log ws vpre vi base tvs :=
  invalCiteB_sound (List.mem_filter.1 h).2

theorem cohBelowB_iff (ws : PState) (ts : Nat) :
    ∀ (a : Int) (n : Nat), cohBelowB ws a n ts = true ↔ cohBelow ws a n ts := by
  intro a n
  induction n generalizing a with
  | zero => simp [cohBelowB, cohBelow]
  | succ n ih => simp only [cohBelowB, cohBelow, Bool.and_eq_true, decide_eq_true_eq, ih]

theorem promHas_iff (prom : GSet Nat) (ts : Nat) : promHas prom ts = true ↔ ts ∈ prom :=
  Std.ExtTreeSet.contains_iff_mem

theorem msgEq_of_beq {log : List PMsg} {ts : Nat} {m : PMsg} (h : (log[ts - 1]? == some m) = true) :
    log[ts - 1]? = some m := beq_iff_eq.1 h

/-- The membership facts `writeTs` guarantees. -/
theorem writeTs_mem {log : List PMsg} {i : Nat} {prom : GSet Nat} {ws : PState} {base : Int}
    {data : List (BitVec 8)} {cls : PClass} {pre ts : Nat} (h : ts ∈ writeTs log i prom ws base data cls pre) :
    ts ∈ prom ∧ log[ts - 1]? = some ⟨base, data, some i, cls⟩ ∧ cohBelow ws base data.length ts ∧ pre < ts := by
  unfold writeTs at h
  simp only [List.mem_filter, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨_, ⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  exact ⟨(promHas_iff ..).1 h1, msgEq_of_beq h2, (cohBelowB_iff ..).1 h3, h4⟩

/-! ## 2. `explorerStep_sound` -/

/-- THE EXPLORER STEP IS SOUND ([R5.s5]): every successor of `succ` for any label template is a `memStep` of
machine v2 with that successor's label, fulfil timestamp, post-state and promise set. -/
theorem explorerStep_sound {img : Image} {log : List PMsg} {i : Nat} {prom : GSet Nat} {ws : PState} {t : Tmpl}
    {s : Succ} (h : s ∈ succ img log i prom ws t) : memStep img log i prom ws s.l s.ots s.ws s.prom := by
  cases t with
  | fix l =>
    simp only [succ] at h
    cases hf : fixPost ws l with
    | none => rw [hf] at h; cases h
    | some ws' =>
      rw [hf] at h
      simp only [List.mem_singleton] at h
      subst h
      cases l <;> simp only [fixPost, Option.some.injEq, reduceCtorEq] at hf <;> subst hf
      · exact .silent _ _
      · exact .fence _ _ _ _ _ _
      · exact .fenceI _ _
      · exact .dev _ _ _ _ _ _ _
      · exact .regW _ _ _ _
      · exact .ctrl _ _ _
      · exact .instr _ _
      · exact .scFail _ _
  | ld aq rl base sz asrc =>
    simp only [succ, List.mem_flatMap] at h
    obtain ⟨tvs, _, hs⟩ := h
    split at hs
    · rename_i hok
      obtain ⟨vi, hvi, rfl⟩ := List.mem_map.1 hs
      exact .load _ _ _ _ _ _ _ (loadOkB_sound hok) vi (viOpts_sound hvi)
    · cases hs
  | lr aq rl base sz asrc =>
    simp only [succ, List.mem_flatMap] at h
    obtain ⟨tvs, _, hs⟩ := h
    split at hs
    · rename_i hok
      obtain ⟨vi, hvi, rfl⟩ := List.mem_map.1 hs
      exact .lr _ _ _ _ _ _ _ (loadOkB_sound hok) vi (viOpts_sound hvi)
    · cases hs
  | st aq rl base data asrc vsrc =>
    simp only [succ, List.mem_map] at h
    obtain ⟨ts, hts, hs⟩ := h
    subst hs
    obtain ⟨h1, h2, h3, h4⟩ := writeTs_mem hts
    exact .store _ _ _ _ _ _ _ _ _ h1 h2 h3 h4
  | sc aq rl base data asrc vsrc =>
    simp only [succ] at h
    cases hR : ws.wRes with
    | none => rw [hR] at h; cases h
    | some R =>
      rw [hR] at h
      simp only [List.mem_map, List.mem_filter, Bool.and_eq_true] at h
      obtain ⟨ts, ⟨hts, hx, hall⟩, hs⟩ := h
      subst hs
      obtain ⟨h1, h2, h3, h4⟩ := writeTs_mem hts
      refine .sc _ _ _ _ _ _ _ _ _ R hR h1 h2 ((exclOkB_iff ..).1 hx) ?_ h3 h4
      intro t ht
      exact of_decide_eq_true (List.all_eq_true.1 hall t ht)
  | rmw aq rl base sz f asrc vsrc =>
    simp only [succ, List.mem_flatMap] at h
    obtain ⟨tvs, _, hs⟩ := h
    split at hs
    · cases hs
    · rename_i hok
      simp only [Bool.not_eq_true', Bool.not_eq_false] at hok
      split at hs
      · cases hs
      · rename_i hlen
        simp only [bne_iff_ne, ne_eq, Decidable.not_not] at hlen
        obtain ⟨ts, hts', hs⟩ := List.mem_flatMap.1 hs
        obtain ⟨hts, hx⟩ := List.mem_filter.1 hts'
        obtain ⟨vi, hvi', rfl⟩ := List.mem_map.1 hs
        obtain ⟨hvi, hvt⟩ := List.mem_filter.1 hvi'
        obtain ⟨h1, h2, h3, h4⟩ := writeTs_mem hts
        exact .rmw _ _ _ _ _ _ _ _ _ _ hlen h1 h2 (loadOkB_sound hok) ((exclOkB_iff ..).1 hx) h3 h4 vi
          (viOpts_sound hvi) (of_decide_eq_true hvt)

/-! ## 3. The memory half as a function of the full label (the certificate checker's step) -/

/-- `some x` iff the Bool holds. -/
def okIf {α : Type} (c : Bool) (x : α) : Option α := if c then some x else none

theorem okIf_eq_some {α : Type} {c : Bool} {x y : α} (h : okIf c x = some y) : c = true ∧ x = y := by
  unfold okIf at h
  cases c
  · cases h
  · cases h; exact ⟨rfl, rfl⟩

/-- A promise message is non-trivial (the `promise` arm's side condition) as a Bool. -/
def msgNonTrivB (m : PMsg) : Bool :=
  !m.data.isEmpty || (match m.cls with | .cmo _ len => decide (0 < len) | _ => false)

theorem msgNonTriv_sound {m : PMsg} (h : msgNonTrivB m = true) :
    m.data ≠ [] ∨ ∃ k len, m.cls = .cmo k len ∧ 0 < len := by
  unfold msgNonTrivB at h
  simp only [Bool.or_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff] at h
  rcases h with h | h
  · exact .inl h
  · right
    cases hc : m.cls with
    | cmo k len => rw [hc] at h; exact ⟨k, len, rfl, of_decide_eq_true h⟩
    | plain => rw [hc] at h; cases h
    | rel => rw [hc] at h; cases h
    | excl => rw [hc] at h; cases h

/-- THE MEMORY HALF OF A STATE STEP, as a function of the label and the fulfil timestamp: every premise of the
matching `memStep` arm checked by its Bool transcription, the post-state by Machine.lean's functions. -/
def memStepF (img : Image) (log : List PMsg) (i : Nat) (prom : GSet Nat) (ws : PState) :
    PLabel → Option Nat → Option (PState × GSet Nat)
  | LSilent, none => some (ws, prom)
  | LLoad aq rl base tvs asrc, none =>   -- MachFix-R-b5: the `vi = 0` step (`memStepL`: every `vi`)
    okIf (loadOkB img log ws (ldPre ws aq rl (srcsView ws asrc)) base tvs &&
        invalCiteB log ws (ldPre ws aq rl (srcsView ws asrc)) 0 base tvs)
      (loadRun ws aq rl (srcsView ws asrc) base tvs, prom)
  | LStore aq rl base data asrc vsrc, some ts =>
    okIf (promHas prom ts && log[ts - 1]? == some ⟨base, data, some i, stClass rl⟩ &&
        cohBelowB ws base data.length ts && decide (stPreA ws aq rl (srcsView ws asrc) (srcsView ws vsrc) < ts))
      (acqPost (storeRun ws rl (srcsView ws asrc) (max (srcsView ws asrc) (srcsView ws vsrc)) base
        data.length ts) aq ts, prom \ {ts})
  | LRmw aq rl base tvs data asrc vsrc, some ts =>
    okIf (decide (tvs.length = data.length) && promHas prom ts &&
        log[ts - 1]? == some ⟨base, data, some i, .excl⟩ &&
        loadOkB img log ws (ldPre ws aq false (srcsView ws asrc)) base tvs &&
        exclOkB log i base (tvs.map Prod.fst) ts &&
        cohBelowB (loadRun ws aq false (srcsView ws asrc) base tvs) base data.length ts &&
        decide (stPre (loadRun ws aq false (srcsView ws asrc) base tvs) rl (srcsView ws asrc)
          (srcsView ws vsrc) < ts) &&
        invalCiteB log ws (ldPre ws aq false (srcsView ws asrc)) 0 base tvs)   -- MachFix-R-b5
      (amoPost (storeRun (loadRun ws aq false (srcsView ws asrc) base tvs) rl (srcsView ws asrc) ts base
          data.length ts) aq ts, prom \ {ts})
  | LAmoLd aq base tvs asrc, none =>   -- MachFix-R-b5: `vi = 0`
    okIf (loadOkB img log ws (ldPre ws aq false (srcsView ws asrc)) base tvs &&
        invalCiteB log ws (ldPre ws aq false (srcsView ws asrc)) 0 base tvs)
      ({ loadRun ws aq false (srcsView ws asrc) base tvs with wRmw := some ⟨base, tvs.map Prod.fst, aq⟩ }, prom)
  | LAmoSt rl base data asrc vsrc, some ts =>
    match ws.wRmw with
    | some R =>
      okIf (decide (R.rmBase = base) && decide (R.rmTs.length = data.length) && promHas prom ts &&
          log[ts - 1]? == some ⟨base, data, some i, .excl⟩ && exclOkB log i base R.rmTs ts &&
          cohBelowB ws base data.length ts &&
          decide (stPre ws rl (srcsView ws asrc) (srcsView ws vsrc) < ts))
        ({ amoPost (storeRun ws rl (srcsView ws asrc) ts base data.length ts) R.rmAq ts with wRmw := none },
          prom \ {ts})
    | none => none
  | LFence pr pw sr sw, none => some (fencePost ws pr pw sr sw, prom)
  | LFenceI, none => some (fenceIPost ws, prom)
  | LDev _ _ _ _ _, none => some (ws, prom)
  | LRegW rd srcs, none => some ({ ws with wRegv := insert ws.wRegv rd (srcsView ws srcs) }, prom)
  | LCtrl srcs, none => some ({ ws with wVcap := max (srcsView ws srcs) ws.wVcap }, prom)
  | LInstr, none => some ({ ws with wLdv := 0, wRmw := none, wIfv := 0 }, prom)
  | LExLoad aq rl base tvs asrc, none =>   -- MachFix-R-b5: `vi = 0`
    okIf (loadOkB img log ws (ldPre ws aq rl (srcsView ws asrc)) base tvs &&
        invalCiteB log ws (ldPre ws aq rl (srcsView ws asrc)) 0 base tvs)
      ({ loadRun ws aq rl (srcsView ws asrc) base tvs with
          wRes := some ⟨base, tvs.map Prod.fst, readView ws aq rl (srcsView ws asrc) base tvs⟩ }, prom)
  | LExStore aq rl base data asrc vsrc, some ts =>
    match ws.wRes with
    | some R =>
      okIf (promHas prom ts && log[ts - 1]? == some ⟨base, data, some i, .excl⟩ &&
          exclOkB log i R.rvBase R.rvTs ts && R.rvTs.all (fun t => decide (t < ts)) &&
          cohBelowB ws base data.length ts &&
          decide (max (stPreA ws aq rl (srcsView ws asrc) (srcsView ws vsrc)) R.rvView < ts))
        ({ acqPost (storeRun ws rl (srcsView ws asrc) ts base data.length ts) aq ts with
            wLdv := max (storeRun ws rl (srcsView ws asrc) ts base data.length ts).wLdv ts
            wRes := none }, prom \ {ts})
    | none => none
  | LExFail, none => some ({ ws with wRes := none }, prom)
  | LIFetch base tvs, none =>
    okIf (bytesAllB (fun a t v => memByte img log t a == some v && !writesInB log a t ws.wIfl) base tvs)
      ({ ws with
          wIfr := max ws.wIfr (bytesMax (fun _ t => t) base tvs)
          wIfv := max ws.wIfv (fetchView log i prom base tvs) }, prom)
  | LCmo k base len asrc, some ts =>
    okIf (promHas prom ts && log[ts - 1]? == some ⟨base, [], some i, .cmo k len⟩ &&
        cohBelowB ws base len ts && decide (stPre ws false (srcsView ws asrc) 0 < ts))
      (cmoPost ws (srcsView ws asrc) base len ts, prom \ {ts})
  | _, _ => none

/-- `memStepF` IS SOUND: a computed step is a `memStep` of machine v2. -/
theorem memStepF_sound {img : Image} {log : List PMsg} {i : Nat} {prom : GSet Nat} {ws : PState}
    {l : PLabel} {ots : Option Nat} {ws' : PState} {prom' : GSet Nat}
    (h : memStepF img log i prom ws l ots = some (ws', prom')) : memStep img log i prom ws l ots ws' prom' := by
  cases l <;> cases ots <;> simp only [memStepF, reduceCtorEq] at h
  case LSilent.none => cases h; exact .silent _ _
  case LLoad.none aq rl base tvs asrc =>
    obtain ⟨hc, he⟩ := okIf_eq_some h
    cases he
    simp only [Bool.and_eq_true] at hc
    have := memStep.load (img := img) (log := log) (i := i) prom ws aq rl base tvs asrc (loadOkB_sound hc.1) 0
      (invalCiteB_sound hc.2)
    rwa [loadRunV_zero] at this
  case LStore.some aq rl base data asrc vsrc ts =>
    obtain ⟨hc, he⟩ := okIf_eq_some h
    cases he
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hc
    exact .store _ _ _ _ _ _ _ _ _ ((promHas_iff ..).1 h1) (msgEq_of_beq h2) ((cohBelowB_iff ..).1 h3) h4
  case LRmw.some aq rl base tvs data asrc vsrc ts =>
    obtain ⟨hc, he⟩ := okIf_eq_some h
    cases he
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := hc
    have := memStep.rmw (img := img) (log := log) (i := i) prom ws aq rl base tvs data asrc vsrc ts h0
      ((promHas_iff ..).1 h1) (msgEq_of_beq h2) (loadOkB_sound h3) ((exclOkB_iff ..).1 h4)
      ((cohBelowB_iff ..).1 h5) h6 0 (invalCiteB_sound h7) (by omega)
    rwa [loadRunV_zero] at this
  case LAmoLd.none aq base tvs asrc =>
    obtain ⟨hc, he⟩ := okIf_eq_some h
    cases he
    simp only [Bool.and_eq_true] at hc
    have := memStep.amoLd (img := img) (log := log) (i := i) prom ws aq base tvs asrc (loadOkB_sound hc.1) 0
      (invalCiteB_sound hc.2)
    rwa [loadRunV_zero] at this
  case LAmoSt.some rl base data asrc vsrc ts =>
    cases hR : ws.wRmw with
    | none => rw [hR] at h; cases h
    | some R =>
      rw [hR] at h
      obtain ⟨hc, he⟩ := okIf_eq_some h
      cases he
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      obtain ⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := hc
      exact .amoSt _ _ _ _ _ _ _ _ R hR h0 h1 ((promHas_iff ..).1 h2) (msgEq_of_beq h3)
        ((exclOkB_iff ..).1 h4) ((cohBelowB_iff ..).1 h5) h6
  case LFence.none pr pw sr sw => cases h; exact .fence _ _ _ _ _ _
  case LFenceI.none => cases h; exact .fenceI _ _
  case LDev.none kd ba bs sa sv => cases h; exact .dev _ _ _ _ _ _ _
  case LRegW.none rd srcs => cases h; exact .regW _ _ _ _
  case LCtrl.none srcs => cases h; exact .ctrl _ _ _
  case LInstr.none => cases h; exact .instr _ _
  case LExLoad.none aq rl base tvs asrc =>
    obtain ⟨hc, he⟩ := okIf_eq_some h
    cases he
    simp only [Bool.and_eq_true] at hc
    have := memStep.lr (img := img) (log := log) (i := i) prom ws aq rl base tvs asrc (loadOkB_sound hc.1) 0
      (invalCiteB_sound hc.2)
    rwa [loadRunV_zero, readViewV_zero] at this
  case LExStore.some aq rl base data asrc vsrc ts =>
    cases hR : ws.wRes with
    | none => rw [hR] at h; cases h
    | some R =>
      rw [hR] at h
      obtain ⟨hc, he⟩ := okIf_eq_some h
      cases he
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := hc
      refine .sc _ _ _ _ _ _ _ _ _ R hR ((promHas_iff ..).1 h1) (msgEq_of_beq h2) ((exclOkB_iff ..).1 h3) ?_
        ((cohBelowB_iff ..).1 h5) h6
      intro t ht
      exact of_decide_eq_true (List.all_eq_true.1 h4 t ht)
  case LExFail.none => cases h; exact .scFail _ _
  case LIFetch.none base tvs =>
    obtain ⟨hc, he⟩ := okIf_eq_some h
    cases he
    refine .fetch _ _ _ _ (bytesAllB_sound (fun a t v hp => ?_) base tvs hc)
    simp only [Bool.and_eq_true, beq_iff_eq] at hp
    exact ⟨hp.1, not_writesIn_of_B hp.2⟩
  case LCmo.some k base len asrc ts =>
    obtain ⟨hc, he⟩ := okIf_eq_some h
    cases he
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hc
    exact .cmo _ _ _ _ _ _ _ ((promHas_iff ..).1 h1) (msgEq_of_beq h2) ((cohBelowB_iff ..).1 h3) h4

/-! ## 4. MachFix-R-b5: every step of a full label (`memStepL`, the absorbed views enumerated) -/

/-- THE MEMORY HALF OF A STATE STEP, every successor: as `memStepF`, with every admissible absorbed invalidate view
`vi` of a load-like label (`viOpts`; `memStepF` takes `vi = 0` only). -/
def memStepL (img : Image) (log : List PMsg) (i : Nat) (prom : GSet Nat) (ws : PState) :
    PLabel → Option Nat → List (PState × GSet Nat)
  | LLoad aq rl base tvs asrc, none =>
    if loadOkB img log ws (ldPre ws aq rl (srcsView ws asrc)) base tvs then
      (viOpts log ws (ldPre ws aq rl (srcsView ws asrc)) base tvs).map (fun vi =>
        (loadRunV ws aq rl (srcsView ws asrc) vi base tvs, prom))
    else []
  | LRmw aq rl base tvs data asrc vsrc, some ts =>
    if decide (tvs.length = data.length) && promHas prom ts &&
        log[ts - 1]? == some ⟨base, data, some i, .excl⟩ &&
        loadOkB img log ws (ldPre ws aq false (srcsView ws asrc)) base tvs &&
        exclOkB log i base (tvs.map Prod.fst) ts &&
        cohBelowB (loadRun ws aq false (srcsView ws asrc) base tvs) base data.length ts &&
        decide (stPre (loadRun ws aq false (srcsView ws asrc) base tvs) rl (srcsView ws asrc)
          (srcsView ws vsrc) < ts) then
      ((viOpts log ws (ldPre ws aq false (srcsView ws asrc)) base tvs).filter (fun vi => decide (vi < ts))).map
        (fun vi => (amoPost (storeRun (loadRunV ws aq false (srcsView ws asrc) vi base tvs) rl (srcsView ws asrc) ts
          base data.length ts) aq ts, prom \ {ts}))
    else []
  | LAmoLd aq base tvs asrc, none =>
    if loadOkB img log ws (ldPre ws aq false (srcsView ws asrc)) base tvs then
      (viOpts log ws (ldPre ws aq false (srcsView ws asrc)) base tvs).map (fun vi =>
        ({ loadRunV ws aq false (srcsView ws asrc) vi base tvs with wRmw := some ⟨base, tvs.map Prod.fst, aq⟩ },
          prom))
    else []
  | LExLoad aq rl base tvs asrc, none =>
    if loadOkB img log ws (ldPre ws aq rl (srcsView ws asrc)) base tvs then
      (viOpts log ws (ldPre ws aq rl (srcsView ws asrc)) base tvs).map (fun vi =>
        ({ loadRunV ws aq rl (srcsView ws asrc) vi base tvs with
            wRes := some ⟨base, tvs.map Prod.fst, readViewV ws aq rl (srcsView ws asrc) vi base tvs⟩ }, prom))
    else []
  | l, o => (memStepF img log i prom ws l o).toList

/-- `memStepL` IS SOUND. -/
theorem memStepL_sound {img : Image} {log : List PMsg} {i : Nat} {prom : GSet Nat} {ws : PState}
    {l : PLabel} {ots : Option Nat} {ws' : PState} {prom' : GSet Nat}
    (h : (ws', prom') ∈ memStepL img log i prom ws l ots) : memStep img log i prom ws l ots ws' prom' := by
  have fb : ∀ {l o}, (ws', prom') ∈ (memStepF img log i prom ws l o).toList →
      memStep img log i prom ws l o ws' prom' := fun h => memStepF_sound (by simpa using h)
  cases l <;> cases ots <;> simp only [memStepL] at h <;> try exact fb h
  case LLoad.none aq rl base tvs asrc =>
    split at h
    · rename_i hok
      obtain ⟨vi, hvi, he⟩ := List.mem_map.1 h
      cases he
      exact .load _ _ _ _ _ _ _ (loadOkB_sound hok) vi (viOpts_sound hvi)
    · cases h
  case LRmw.some aq rl base tvs data asrc vsrc ts =>
    split at h
    · rename_i hc
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      obtain ⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := hc
      obtain ⟨vi, hvi', he⟩ := List.mem_map.1 h
      cases he
      obtain ⟨hvi, hvt⟩ := List.mem_filter.1 hvi'
      exact .rmw _ _ _ _ _ _ _ _ _ _ h0 ((promHas_iff ..).1 h1) (msgEq_of_beq h2) (loadOkB_sound h3)
        ((exclOkB_iff ..).1 h4) ((cohBelowB_iff ..).1 h5) h6 vi (viOpts_sound hvi) (of_decide_eq_true hvt)
    · cases h
  case LAmoLd.none aq base tvs asrc =>
    split at h
    · rename_i hok
      obtain ⟨vi, hvi, he⟩ := List.mem_map.1 h
      cases he
      exact .amoLd _ _ _ _ _ _ (loadOkB_sound hok) vi (viOpts_sound hvi)
    · cases h
  case LExLoad.none aq rl base tvs asrc =>
    split at h
    · rename_i hok
      obtain ⟨vi, hvi, he⟩ := List.mem_map.1 h
      cases he
      exact .lr _ _ _ _ _ _ _ (loadOkB_sound hok) vi (viOpts_sound hvi)
    · cases h

end Weak.Prom.Mach
