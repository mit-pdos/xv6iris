/-
Weak/Prom: **the absorbed invalidate view, lemmas** (FIX MachFix-R-b5, 2026-11-04; brief
`~/dev/weak-orch/promising/MachFix_prompt.txt`, PROGRESS-S4b.md R-b5).

Machine.lean's load-like arms (`load`, `rmw`, `amoLd`, `lr`) carry the view `vi` the load absorbs for the
invalidates it cites (`invalCite`): cmo.adoc:259–274 "If an invalidate operation i precedes a load r …" — `i`
precedes `r` in the global memory order, so `r` is ordered after `i` and its post-view is at least `ti`
(`loadRunV`, `readViewV`).  This file proves the facts every client needs:

* `loadRunV_zero`, `readViewV_zero` — with no citation the arms are the old ones;
* `invalCite_vi0` — with no invalidate-class message in the log, `vi = 0` (so CMO-free proofs are unchanged);
* `invalCite_zero` / `invalCite_zero_of_loadOk` — the `vi = 0` citation of a normal read;
* `invalCite_le` — `vi` is a log timestamp (`vi ≤ |log|`);
* `invalCite_restrict` — prefix restriction (NF_R, NfrStep.lean): a citation against `M` whose read timestamps
  and `vi` lie in a prefix `L` is a citation against `L`.
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Prom.Machine

namespace Weak.Prom

open MachCSL MachCSL.Stdpp Iris.Std
open Weak (Image Dsrc)
open PLabel

theorem invalRead_iff_at {log : List PMsg} {a : Int} {t fl : Nat} :
    invalRead log a t fl ↔ ∃ ti, invalReadAt log a t fl ti := Iff.rfl

theorem loadRunV_zero (ws : PState) (aq rl : Bool) (va : Nat) (base : Int) (tvs : List (Nat × BitVec 8)) :
    loadRunV ws aq rl va 0 base tvs = loadRun ws aq rl va base tvs := by
  simp only [loadRunV, loadRun, readViewV, Nat.max_zero]

theorem readViewV_zero (ws : PState) (aq rl : Bool) (va : Nat) (base : Int) (tvs : List (Nat × BitVec 8)) :
    readViewV ws aq rl va 0 base tvs = readView ws aq rl va base tvs := by
  simp only [readViewV, Nat.max_zero]

/-- A cited invalidate is an invalidate-class message of the log. -/
theorem invalReadAt_cmo {log : List PMsg} {a : Int} {t fl ti : Nat} (h : invalReadAt log a t fl ti) :
    cmoAt log isInvalK ti a := h.1

theorem cmoAt_le {log : List PMsg} {p : CmoKind → Bool} {t : Nat} {a : Int} (h : cmoAt log p t a) (h0 : 0 < t) :
    t ≤ log.length := by
  obtain ⟨m, _, _, hm, _⟩ := h
  have := (List.getElem?_eq_some_iff.1 hm).1
  omega

theorem bytesAny_elim {P : Int → Nat → BitVec 8 → Prop} {Q : Prop} (hQ : ∀ a t v, P a t v → Q) :
    ∀ (a : Int) (l : List (Nat × BitVec 8)), bytesAny P a l → Q
  | _, [], h => h.elim
  | a, (t, v) :: r, h => h.elim (hQ a t v) (bytesAny_elim hQ (a + 1) r)

theorem bytesAny_mono {P Q : Int → Nat → BitVec 8 → Prop} (hPQ : ∀ a t v, P a t v → Q a t v) :
    ∀ (a : Int) (l : List (Nat × BitVec 8)), bytesAny P a l → bytesAny Q a l
  | _, [], h => h
  | a, (t, v) :: r, h => h.elim (fun h => .inl (hPQ a t v h)) (fun h => .inr (bytesAny_mono hPQ (a + 1) r h))

/-- `vi` is `0` or a cited invalidate (so `0 < vi` only with an invalidate-class message at `vi`). -/
theorem invalCite_cmo {log : List PMsg} {ws : PState} {vpre vi : Nat} {base : Int} {tvs : List (Nat × BitVec 8)}
    (h : invalCite log ws vpre vi base tvs) : vi = 0 ∨ ∃ a, cmoAt log isInvalK vi a :=
  h.2.elim .inl (fun h => .inr (bytesAny_elim (fun a _ _ hp => ⟨a, hp.1⟩) base tvs h))

/-- With no invalidate-class message, the absorbed view is `0`. -/
theorem invalCite_vi0 {log : List PMsg} (hinv : ∀ t a, ¬ cmoAt log isInvalK t a) {ws : PState} {vpre vi : Nat}
    {base : Int} {tvs : List (Nat × BitVec 8)} (h : invalCite log ws vpre vi base tvs) : vi = 0 :=
  (invalCite_cmo h).elim id (fun ⟨a, ha⟩ => absurd ha (hinv vi a))

/-- `vi` is a log timestamp. -/
theorem invalCite_le {log : List PMsg} {ws : PState} {vpre vi : Nat} {base : Int} {tvs : List (Nat × BitVec 8)}
    (h : invalCite log ws vpre vi base tvs) : vi ≤ log.length := by
  rcases h.2 with h0 | h1
  · omega
  · exact bytesAny_elim (fun _ _ _ hp => cmoAt_le hp.1 (by have := hp.2.1; omega)) base tvs h1

/-- The `vi = 0` citation of a read whose every byte is read normally. -/
theorem invalCite_zero {log : List PMsg} {ws : PState} {vpre : Nat} {base : Int} {tvs : List (Nat × BitVec 8)}
    (h : bytesAll (fun a t _ =>
      ¬ writesIn log a t (max (if fwdHit ws a t then vpre else max vpre (nonFwdMax ws base tvs)) (coh ws a)))
      base tvs) : invalCite log ws vpre 0 base tvs := by
  refine ⟨?_, .inl rfl⟩
  have key : ∀ (a : Int) (r : List (Nat × BitVec 8)), bytesAll (fun a t _ =>
      ¬ writesIn log a t (max (if fwdHit ws a t then vpre else max vpre (nonFwdMax ws base tvs)) (coh ws a))) a r →
      bytesAll (fun a t _ =>
      ¬ writesIn log a t (max (if fwdHit ws a t then vpre else max vpre (nonFwdMax ws base tvs)) (coh ws a)) ∨
      ∃ ti, ti ≤ 0 ∧ invalReadAt log a t (max vpre (coh ws a)) ti) a r := by
    intro a r
    induction r generalizing a with
    | nil => intro _; trivial
    | cons tv r ih => obtain ⟨t, v⟩ := tv; exact fun ⟨h1, h2⟩ => ⟨.inl h1, ih (a + 1) h2⟩
  exact key base tvs h

/-- With no invalidate-class message, every admissible read has the `vi = 0` citation. -/
theorem invalCite_zero_of_loadOk {img : Image} {log : List PMsg} (hinv : ∀ t a, ¬ cmoAt log isInvalK t a)
    {ws : PState} {vpre : Nat} {base : Int} {tvs : List (Nat × BitVec 8)} (h : loadOk img log ws vpre base tvs) :
    invalCite log ws vpre 0 base tvs := by
  refine invalCite_zero ?_
  have key : ∀ (a : Int) (r : List (Nat × BitVec 8)), bytesAll (fun a t v => memByte img log t a = some v ∧
      (¬ writesIn log a t (max (if fwdHit ws a t then vpre else max vpre (nonFwdMax ws base tvs)) (coh ws a)) ∨
        invalRead log a t (max vpre (coh ws a)))) a r →
      bytesAll (fun a t _ =>
      ¬ writesIn log a t (max (if fwdHit ws a t then vpre else max vpre (nonFwdMax ws base tvs)) (coh ws a))) a r := by
    intro a r
    induction r generalizing a with
    | nil => intro _; trivial
    | cons tv r ih =>
      obtain ⟨t, v⟩ := tv
      rintro ⟨⟨_, hw | ⟨ti, hc, _⟩⟩, h2⟩
      · exact ⟨hw, ih (a + 1) h2⟩
      · exact absurd hc (hinv ti a)
  exact key base tvs h

/-! ## The `vi = 0` arms (no invalidate-class message: the arms as before the fix) -/

theorem memStep.load0 {img : Image} {log : List PMsg} {i : Nat} {prom : GSet Nat} {ws : PState} {aq rl : Bool}
    {base : Int} {tvs : List (Nat × BitVec 8)} {asrc : List Dsrc} (hinv : ∀ t a, ¬ cmoAt log isInvalK t a)
    (hl : loadOk img log ws (ldPre ws aq rl (srcsView ws asrc)) base tvs) :
    memStep img log i prom ws (LLoad aq rl base tvs asrc) none (loadRun ws aq rl (srcsView ws asrc) base tvs) prom := by
  have := memStep.load (img := img) (log := log) (i := i) prom ws aq rl base tvs asrc hl 0
    (invalCite_zero_of_loadOk hinv hl)
  rwa [loadRunV_zero] at this

theorem memStep.lr0 {img : Image} {log : List PMsg} {i : Nat} {prom : GSet Nat} {ws : PState} {aq rl : Bool}
    {base : Int} {tvs : List (Nat × BitVec 8)} {asrc : List Dsrc} (hinv : ∀ t a, ¬ cmoAt log isInvalK t a)
    (hl : loadOk img log ws (ldPre ws aq rl (srcsView ws asrc)) base tvs) :
    memStep img log i prom ws (LExLoad aq rl base tvs asrc) none
      { loadRun ws aq rl (srcsView ws asrc) base tvs with
        wRes := some ⟨base, tvs.map Prod.fst, readView ws aq rl (srcsView ws asrc) base tvs⟩ } prom := by
  have := memStep.lr (img := img) (log := log) (i := i) prom ws aq rl base tvs asrc hl 0
    (invalCite_zero_of_loadOk hinv hl)
  rwa [loadRunV_zero, readViewV_zero] at this

theorem memStep.amoLd0 {img : Image} {log : List PMsg} {i : Nat} {prom : GSet Nat} {ws : PState} {aq : Bool}
    {base : Int} {tvs : List (Nat × BitVec 8)} {asrc : List Dsrc} (hinv : ∀ t a, ¬ cmoAt log isInvalK t a)
    (hl : loadOk img log ws (ldPre ws aq false (srcsView ws asrc)) base tvs) :
    memStep img log i prom ws (LAmoLd aq base tvs asrc) none
      { loadRun ws aq false (srcsView ws asrc) base tvs with wRmw := some ⟨base, tvs.map Prod.fst, aq⟩ } prom := by
  have := memStep.amoLd (img := img) (log := log) (i := i) prom ws aq base tvs asrc hl 0
    (invalCite_zero_of_loadOk hinv hl)
  rwa [loadRunV_zero] at this

theorem memStep.rmw0 {img : Image} {log : List PMsg} {i : Nat} (hinv : ∀ t a, ¬ cmoAt log isInvalK t a)
    (prom : GSet Nat) (ws : PState) (aq rl : Bool) (base : Int) (tvs : List (Nat × BitVec 8))
    (data : List (BitVec 8)) (asrc vsrc : List Dsrc) (ts : Nat)
    (hlen : tvs.length = data.length) (hts : ts ∈ prom) (hm : log[ts - 1]? = some ⟨base, data, some i, .excl⟩)
    (hl : loadOk img log ws (ldPre ws aq false (srcsView ws asrc)) base tvs)
    (hx : exclOk log i base (tvs.map Prod.fst) ts)
    (hc : cohBelow (loadRun ws aq false (srcsView ws asrc) base tvs) base data.length ts)
    (hpv : stPre (loadRun ws aq false (srcsView ws asrc) base tvs) rl (srcsView ws asrc) (srcsView ws vsrc) < ts) :
    memStep img log i prom ws (LRmw aq rl base tvs data asrc vsrc) (some ts)
      (amoPost (storeRun (loadRun ws aq false (srcsView ws asrc) base tvs) rl (srcsView ws asrc) ts base
        data.length ts) aq ts) (prom \ {ts}) := by
  have := memStep.rmw (img := img) (log := log) (i := i) prom ws aq rl base tvs data asrc vsrc ts hlen hts hm hl hx
    hc hpv 0 (invalCite_zero_of_loadOk hinv hl) (by omega)
  rwa [loadRunV_zero] at this

/-- Every load-like arm of a log with no invalidate-class message has `vi = 0`: the post-state is `loadRun`'s. -/
theorem invalCite_vi0' {log : List PMsg} (hinv : ∀ t a, ¬ cmoAt log isInvalK t a) {ws : PState} {vpre vi : Nat}
    {base : Int} {tvs : List (Nat × BitVec 8)} (h : invalCite log ws vpre vi base tvs) :
    ∀ (aq rl : Bool) (va : Nat), loadRunV ws aq rl va vi base tvs = loadRun ws aq rl va base tvs ∧
      readViewV ws aq rl va vi base tvs = readView ws aq rl va base tvs := by
  intro aq rl va
  rw [invalCite_vi0 hinv h]
  exact ⟨loadRunV_zero .., readViewV_zero ..⟩

/-! ## The absorbed view is below the post-state's `vrOld` -/

theorem loadBytes_vrOld_mono (aq : Bool) (vpre : Nat) : ∀ (ws : PState) (a : Int) (tvs : List (Nat × BitVec 8)),
    ws.wVrOld ≤ (loadBytes aq vpre ws a tvs).wVrOld
  | _, _, [] => Nat.le_refl _
  | ws, a, (t, _) :: r => by
    have := loadBytes_vrOld_mono aq vpre (loadByte ws aq vpre a t) (a + 1) r
    simp only [loadBytes]
    have e : (loadByte ws aq vpre a t).wVrOld = max ws.wVrOld (max vpre (fwdView ws aq a t)) := rfl
    omega

theorem loadBytes_vrOld_pre (aq : Bool) (vpre : Nat) : ∀ (ws : PState) (a : Int) (tvs : List (Nat × BitVec 8)),
    tvs ≠ [] → vpre ≤ (loadBytes aq vpre ws a tvs).wVrOld
  | _, _, [], h => absurd rfl h
  | ws, a, (t, _) :: r, _ => by
    have := loadBytes_vrOld_mono aq vpre (loadByte ws aq vpre a t) (a + 1) r
    simp only [loadBytes]
    have e : (loadByte ws aq vpre a t).wVrOld = max ws.wVrOld (max vpre (fwdView ws aq a t)) := rfl
    omega

/-- THE ABSORBED VIEW IS ABSORBED: `vi ≤ vrOld` after the read. -/
theorem loadRunV_vi_le {log : List PMsg} {ws : PState} {vpre : Nat} {aq rl : Bool} {va vi : Nat} {base : Int}
    {tvs : List (Nat × BitVec 8)} (h : invalCite log ws vpre vi base tvs) :
    vi ≤ (loadRunV ws aq rl va vi base tvs).wVrOld := by
  rcases h.2 with h0 | h1
  · omega
  · have hne : tvs ≠ [] := by rintro rfl; exact h1
    have := loadBytes_vrOld_pre aq (max (ldPre ws aq rl va) vi) ws base tvs hne
    show vi ≤ (loadBytes aq (max (ldPre ws aq rl va) vi) ws base tvs).wVrOld
    omega

/-! ## `loadRunV` against `loadRun`: every view raised by at most `vi`, the rest unchanged -/

/-- `B` is `A` with its read-side views raised by at most `vi` (everything else equal). -/
structure vRaise (vi : Nat) (A B : PState) : Prop where
  vrOld : A.wVrOld ≤ B.wVrOld ∧ B.wVrOld ≤ max A.wVrOld vi
  vrNew : A.wVrNew ≤ B.wVrNew ∧ B.wVrNew ≤ max A.wVrNew vi
  vwNew : A.wVwNew ≤ B.wVwNew ∧ B.wVwNew ≤ max A.wVwNew vi
  vRel : A.wVRel ≤ B.wVRel ∧ B.wVRel ≤ max A.wVRel vi
  ldv : A.wLdv ≤ B.wLdv ∧ B.wLdv ≤ max A.wLdv vi
  coh : ∀ b, coh A b ≤ coh B b ∧ coh B b ≤ max (coh A b) vi
  fwd : B.wFwd = A.wFwd
  vwOld : B.wVwOld = A.wVwOld
  regv : B.wRegv = A.wRegv
  vcap : B.wVcap = A.wVcap
  res : B.wRes = A.wRes
  rmw : B.wRmw = A.wRmw
  ifl : B.wIfl = A.wIfl
  ifr : B.wIfr = A.wIfr
  ifv : B.wIfv = A.wIfv

theorem vRaise_refl (vi : Nat) (A : PState) : vRaise vi A A :=
  ⟨⟨Nat.le_refl _, by omega⟩, ⟨Nat.le_refl _, by omega⟩, ⟨Nat.le_refl _, by omega⟩, ⟨Nat.le_refl _, by omega⟩,
    ⟨Nat.le_refl _, by omega⟩, fun _ => ⟨Nat.le_refl _, by omega⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem getD_insert_natI {m : GMapF Int Nat} {a b : Int} {x : Nat} :
    (get? (insert m a x) b).getD 0 = if a = b then x else (get? m b).getD 0 := by
  by_cases h : a = b
  · subst h; rw [lookupInsert]; simp
  · rw [lookupInsertNe h]; simp [h]

theorem loadByte_vRaise {vi p : Nat} {A B : PState} (aq : Bool) (a : Int) (t : Nat) (h : vRaise vi A B) :
    vRaise vi (loadByte A aq p a t) (loadByte B aq (max p vi) a t) := by
  have hf : fwdView B aq a t = fwdView A aq a t := by unfold fwdView; rw [h.fwd]
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩ := h
  refine ⟨?_, ?_, ?_, h4, ?_, fun b => ?_, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩
  · simp only [loadByte, hf]; omega
  · simp only [loadByte, hf]; split <;> omega
  · simp only [loadByte, hf]; split <;> omega
  · simp only [loadByte, hf]; omega
  · have := h6 b
    have ha := h6 a
    simp only [loadByte, coh, getD_insert_natI, hf] at this ha ⊢
    split <;> omega

theorem loadBytes_vRaise {vi p : Nat} (aq : Bool) :
    ∀ (A B : PState) (a : Int) (tvs : List (Nat × BitVec 8)), vRaise vi A B →
      vRaise vi (loadBytes aq p A a tvs) (loadBytes aq (max p vi) B a tvs)
  | _, _, _, [], h => h
  | A, B, a, (t, _) :: r, h => by
    simp only [loadBytes]
    exact loadBytes_vRaise aq _ _ (a + 1) r (loadByte_vRaise aq a t h)

/-- THE ABSORBING READ RAISES EVERY READ-SIDE VIEW BY AT MOST `vi`, and changes nothing else. -/
theorem loadRunV_vRaise (ws : PState) (aq rl : Bool) (va vi : Nat) (base : Int) (tvs : List (Nat × BitVec 8)) :
    vRaise vi (loadRun ws aq rl va base tvs) (loadRunV ws aq rl va vi base tvs) := by
  have h := loadBytes_vRaise (vi := vi) (p := ldPre ws aq rl va) aq ws ws base tvs (vRaise_refl vi ws)
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩ := h
  refine ⟨h1, h2, h3, ?_, h5, h6, h7, h8, h9, ?_, h11, h12, h13, h14, h15⟩
  · simp only [loadRun, loadRunV, readViewV]; split <;> omega
  · simp only [loadRun, loadRunV]; omega

/-! ## Prefix restriction (NF_R) -/

theorem cmoAt_pre {L M : List PMsg} (hpre : L <+: M) {p : CmoKind → Bool} {t : Nat} {a : Int}
    (h : cmoAt L p t a) : cmoAt M p t a := by
  obtain ⟨m, k, len, hm, h2⟩ := h
  have hlt : t - 1 < L.length := (List.getElem?_eq_some_iff.1 hm).1
  refine ⟨m, k, len, ?_, h2⟩
  obtain ⟨tl, rfl⟩ := hpre
  rw [List.getElem?_append_left hlt]; exact hm

theorem cmoAt_restrict {L M : List PMsg} (hpre : L <+: M) {p : CmoKind → Bool} {t : Nat} {a : Int}
    (h : cmoAt M p t a) (ht : t - 1 < L.length) : cmoAt L p t a := by
  obtain ⟨m, k, len, hm, h2⟩ := h
  refine ⟨m, k, len, ?_, h2⟩
  obtain ⟨tl, rfl⟩ := hpre
  rw [List.getElem?_append_left ht] at hm; exact hm

theorem writesIn_pre' {L M : List PMsg} (hpre : L <+: M) {a : Int} {lo hi : Nat} (h : writesIn L a lo hi) :
    writesIn M a lo hi := by
  obtain ⟨t, h1, h2, m, hm, hb⟩ := h
  have hlt : t - 1 < L.length := (List.getElem?_eq_some_iff.1 hm).1
  obtain ⟨tl, rfl⟩ := hpre
  exact ⟨t, h1, h2, m, by rw [List.getElem?_append_left hlt]; exact hm, hb⟩

/-- A cited invalidate at `ti ≤ |L|` against `M` is one against the prefix `L`. -/
theorem invalReadAt_restrict {L M : List PMsg} (hpre : L <+: M) {a : Int} {t fl ti : Nat}
    (h : invalReadAt M a t fl ti) (hti : ti ≤ L.length) : invalReadAt L a t fl ti := by
  obtain ⟨hc, hlt, hw, hn, hcl⟩ := h
  refine ⟨cmoAt_restrict hpre hc (by omega), hlt, fun h => hw (writesIn_pre' hpre h), fun ⟨ti', h1, h2, h3⟩ =>
    hn ⟨ti', h1, h2, cmoAt_pre hpre h3⟩, fun c hc' hcc h => hcl c hc' (cmoAt_pre hpre hcc) (writesIn_pre' hpre h)⟩

/-- No invalidate-class message in `M`: none in a prefix. -/
theorem noInval_take {M : List PMsg} (h : ∀ t a, ¬ cmoAt M isInvalK t a) (n : Nat) :
    ∀ t a, ¬ cmoAt (M.take n) isInvalK t a :=
  fun t a hc => h t a (cmoAt_pre (List.take_prefix n M) hc)

/-- PREFIX RESTRICTION OF A CITATION: if `vi ≤ |L|`, a citation against `M` is one against `L`. -/
theorem invalCite_restrict {L M : List PMsg} (hpre : L <+: M) {ws : PState} {vpre vi : Nat} {base : Int}
    {tvs : List (Nat × BitVec 8)} (h : invalCite M ws vpre vi base tvs) (hvi : vi ≤ L.length) :
    invalCite L ws vpre vi base tvs := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, h2.elim .inl (fun h => .inr (bytesAny_mono (fun _ _ _ hp => invalReadAt_restrict hpre hp hvi)
    base tvs h))⟩
  have key : ∀ (a : Int) (r : List (Nat × BitVec 8)), bytesAll (fun a t _ =>
      ¬ writesIn M a t (max (if fwdHit ws a t then vpre else max vpre (nonFwdMax ws base tvs)) (coh ws a)) ∨
      ∃ ti, ti ≤ vi ∧ invalReadAt M a t (max vpre (coh ws a)) ti) a r →
      bytesAll (fun a t _ =>
      ¬ writesIn L a t (max (if fwdHit ws a t then vpre else max vpre (nonFwdMax ws base tvs)) (coh ws a)) ∨
      ∃ ti, ti ≤ vi ∧ invalReadAt L a t (max vpre (coh ws a)) ti) a r := by
    intro a r
    induction r generalizing a with
    | nil => intro _; trivial
    | cons tv r ih =>
      obtain ⟨t, v⟩ := tv
      rintro ⟨hw | ⟨ti, hti, hr⟩, h2⟩
      · exact ⟨.inl (fun h => hw (writesIn_pre' hpre h)), ih (a + 1) h2⟩
      · exact ⟨.inr ⟨ti, hti, invalReadAt_restrict hpre hr (by omega)⟩, ih (a + 1) h2⟩
  exact key base tvs h1

end Weak.Prom
