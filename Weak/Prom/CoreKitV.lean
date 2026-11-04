/-
Weak/Prom: **view facts and the contradiction toolkit of the litmus kit** (stage S2; plan rev 7 §2 "Leaf rules"
(X4)–(X6), "The LB trio, derived step by step from A0's exports", §8 S2).

Part 1 — VIEW FACTS (pure lemmas about machine v2's post-states, used INSIDE each hart's proof, plan §2: "they
hold of the hart's exact ws inside its own proof"):
* `loadRun_b0` / `loadRun_mono` — a load's byte 0 raises `wLdv`, `vrOld` and `coh` to its post-view (X4), an
  acquire also the new-floors (rule 5); every other field is unchanged or grows;
* `storeRun_*`, `amoPost_*`, `ldPre_ge`, `stPre_ge` — the store, AMO, pre-view components (rules 4–7, 9–11, EXT);
* `loadOk_b0`, `loadOk_b0nc` — the load-value / coherence fact a load's byte 0 carries, with the invalidate clause
  removed under `noCmo`.
Part 2 — THE CONTRADICTION TOOLKIT (after A0, from its exports only):
* `kitAdeq` — A0 for a kit program: (i), Ψ = `ΨK` of every final trace (ii), `noCmo` (from (iii) and `wrOk`),
  the partition (iii), `traceWf` (v), `Valid` (iv);
* `kit_writer` — the writer of a message: a timestamped memory entry of some hart (iii) whose label writes the
  message (v); `kit_read` — the bytes a load entry read are the memory's (v);
* `lastByte`, `finalMem_b0`, `lastByte_spec` — the final byte of a location is its last writer's.
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Prom.CoreKit

namespace Weak.Prom.PF

open MachCSL MachCSL.Stdpp Iris.Std
open Weak (Image Dsrc)
open Weak.Prom Weak.Prom.Mach Weak.Prom.Mach.Cert
open Weak.Prom.Ref (Instr Test two64 aluOp brEval amoOp sext byteList bytesVal)
open PLabel
open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode

/-! ## 1. Load posts -/

theorem coh_insert_ge (ws : PState) (a x : Int) (v : Nat) (hv : coh ws a ≤ v) :
    coh ws x ≤ coh { ws with wCoh := insert ws.wCoh a v } x := by
  unfold coh
  by_cases h : a = x
  · subst h; simp only [lookupInsert, Option.getD_some]; exact hv
  · simp only; rw [lookupInsertNe h]; exact Nat.le_refl _

theorem coh_insert_self (ws : PState) (a : Int) (v : Nat) : coh { ws with wCoh := insert ws.wCoh a v } a = v := by
  unfold coh; simp only [lookupInsert, Option.getD_some]

/-- The fields a load's byte fold leaves alone or raises. -/
theorem loadBytes_mono (aq : Bool) (vpre : Nat) : ∀ (ws : PState) (a : Int) (tvs : List (Nat × BitVec 8)),
    (loadBytes aq vpre ws a tvs).wRegv = ws.wRegv ∧ (loadBytes aq vpre ws a tvs).wFwd = ws.wFwd ∧
    (loadBytes aq vpre ws a tvs).wVwOld = ws.wVwOld ∧ (loadBytes aq vpre ws a tvs).wVcap = ws.wVcap ∧
    (loadBytes aq vpre ws a tvs).wVRel = ws.wVRel ∧ (loadBytes aq vpre ws a tvs).wRes = ws.wRes ∧
    ws.wVrOld ≤ (loadBytes aq vpre ws a tvs).wVrOld ∧ ws.wVrNew ≤ (loadBytes aq vpre ws a tvs).wVrNew ∧
    ws.wVwNew ≤ (loadBytes aq vpre ws a tvs).wVwNew ∧ ws.wLdv ≤ (loadBytes aq vpre ws a tvs).wLdv ∧
    (∀ x, coh ws x ≤ coh (loadBytes aq vpre ws a tvs) x) ∧
    (aq = false → (loadBytes aq vpre ws a tvs).wVrNew = ws.wVrNew ∧ (loadBytes aq vpre ws a tvs).wVwNew = ws.wVwNew)
  | ws, _, [] => ⟨rfl, rfl, rfl, rfl, rfl, rfl, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _,
      fun _ => Nat.le_refl _, fun _ => ⟨rfl, rfl⟩⟩
  | ws, a, (t, _) :: r => by
    obtain ⟨i1, i2, i3, i4, i5, i6, i7, i8, i9, i10, i11, i12⟩ := loadBytes_mono aq vpre (loadByte ws aq vpre a t) (a + 1) r
    simp only [loadBytes]
    refine ⟨i1, i2, i3, i4, i5, i6, ?_, ?_, ?_, ?_, fun x => Nat.le_trans ?_ (i11 x), fun haq => ?_⟩
    · exact Nat.le_trans (by simp only [loadByte]; omega) i7
    · exact Nat.le_trans (by simp only [loadByte]; split <;> omega) i8
    · exact Nat.le_trans (by simp only [loadByte]; split <;> omega) i9
    · exact Nat.le_trans (by simp only [loadByte]; omega) i10
    · exact coh_insert_ge ws a x _ (by omega)
    · obtain ⟨j1, j2⟩ := i12 haq
      subst haq
      exact ⟨by rw [j1]; rfl, by rw [j2]; rfl⟩

/-- **(X4) at byte 0**: the post-view `max vpre (fwdView t)` of byte 0 is below `wLdv`, `vrOld` and `coh base` after
the load (and below both new-floors for an acquire, rule 5); the raw timestamp is below `coh base`. -/
theorem loadRun_b0 (ws : PState) (aq rl : Bool) (va : Nat) (base : Int) (t : Nat) (v : BitVec 8)
    (r : List (Nat × BitVec 8)) :
    max (ldPre ws aq rl va) (fwdView ws aq base t) ≤ (loadRun ws aq rl va base ((t, v) :: r)).wLdv ∧
    max (ldPre ws aq rl va) (fwdView ws aq base t) ≤ (loadRun ws aq rl va base ((t, v) :: r)).wVrOld ∧
    max (ldPre ws aq rl va) (fwdView ws aq base t) ≤ coh (loadRun ws aq rl va base ((t, v) :: r)) base ∧
    t ≤ coh (loadRun ws aq rl va base ((t, v) :: r)) base ∧
    (aq = true → max (ldPre ws aq rl va) (fwdView ws aq base t) ≤ (loadRun ws aq rl va base ((t, v) :: r)).wVrNew ∧
      max (ldPre ws aq rl va) (fwdView ws aq base t) ≤ (loadRun ws aq rl va base ((t, v) :: r)).wVwNew) := by
  obtain ⟨_, _, _, _, _, _, i7, i8, i9, i10, i11, _⟩ :=
    loadBytes_mono aq (ldPre ws aq rl va) (loadByte ws aq (ldPre ws aq rl va) base t) (base + 1) r
  have hc := i11 base
  have hcs : coh (loadByte ws aq (ldPre ws aq rl va) base t) base =
      max (coh ws base) (max (max (ldPre ws aq rl va) (fwdView ws aq base t)) t) := coh_insert_self ws base _
  rw [hcs] at hc
  have e1 : (loadRun ws aq rl va base ((t, v) :: r)).wLdv =
      (loadBytes aq (ldPre ws aq rl va) (loadByte ws aq (ldPre ws aq rl va) base t) (base + 1) r).wLdv := rfl
  have e2 : (loadRun ws aq rl va base ((t, v) :: r)).wVrOld =
      (loadBytes aq (ldPre ws aq rl va) (loadByte ws aq (ldPre ws aq rl va) base t) (base + 1) r).wVrOld := rfl
  have e3 : coh (loadRun ws aq rl va base ((t, v) :: r)) base =
      coh (loadBytes aq (ldPre ws aq rl va) (loadByte ws aq (ldPre ws aq rl va) base t) (base + 1) r) base := rfl
  have e4 : (loadRun ws aq rl va base ((t, v) :: r)).wVrNew =
      (loadBytes aq (ldPre ws aq rl va) (loadByte ws aq (ldPre ws aq rl va) base t) (base + 1) r).wVrNew := rfl
  have e5 : (loadRun ws aq rl va base ((t, v) :: r)).wVwNew =
      (loadBytes aq (ldPre ws aq rl va) (loadByte ws aq (ldPre ws aq rl va) base t) (base + 1) r).wVwNew := rfl
  have l7 : (loadByte ws aq (ldPre ws aq rl va) base t).wVrOld =
      max ws.wVrOld (max (ldPre ws aq rl va) (fwdView ws aq base t)) := rfl
  have l10 : (loadByte ws aq (ldPre ws aq rl va) base t).wLdv =
      max ws.wLdv (max (ldPre ws aq rl va) (fwdView ws aq base t)) := rfl
  rw [e1, e2, e3, e4, e5]
  rw [l7] at i7
  rw [l10] at i10
  refine ⟨by omega, by omega, by omega, by omega, fun haq => ?_⟩
  subst haq
  have l8 : (loadByte ws true (ldPre ws true rl va) base t).wVrNew =
      max ws.wVrNew (max (ldPre ws true rl va) (fwdView ws true base t)) := rfl
  have l9 : (loadByte ws true (ldPre ws true rl va) base t).wVwNew =
      max ws.wVwNew (max (ldPre ws true rl va) (fwdView ws true base t)) := rfl
  rw [l8] at i8
  rw [l9] at i9
  exact ⟨by omega, by omega⟩

/-- The fields a run-level load leaves alone or raises. -/
theorem loadRun_mono (ws : PState) (aq rl : Bool) (va : Nat) (base : Int) (tvs : List (Nat × BitVec 8)) :
    (loadRun ws aq rl va base tvs).wRegv = ws.wRegv ∧ (loadRun ws aq rl va base tvs).wFwd = ws.wFwd ∧
    (loadRun ws aq rl va base tvs).wVwOld = ws.wVwOld ∧ (loadRun ws aq rl va base tvs).wVcap = max va ws.wVcap ∧
    (rl = false → (loadRun ws aq rl va base tvs).wVRel = ws.wVRel) ∧ (loadRun ws aq rl va base tvs).wRes = ws.wRes ∧
    ws.wVrOld ≤ (loadRun ws aq rl va base tvs).wVrOld ∧ ws.wVrNew ≤ (loadRun ws aq rl va base tvs).wVrNew ∧
    ws.wVwNew ≤ (loadRun ws aq rl va base tvs).wVwNew ∧ ws.wLdv ≤ (loadRun ws aq rl va base tvs).wLdv ∧
    (∀ x, coh ws x ≤ coh (loadRun ws aq rl va base tvs) x) ∧
    (aq = false → (loadRun ws aq rl va base tvs).wVrNew = ws.wVrNew ∧
      (loadRun ws aq rl va base tvs).wVwNew = ws.wVwNew) := by
  obtain ⟨i1, i2, i3, i4, i5, i6, i7, i8, i9, i10, i11, i12⟩ := loadBytes_mono aq (ldPre ws aq rl va) ws base tvs
  unfold loadRun
  refine ⟨i1, i2, i3, by simp only; rw [i4], fun hrl => by subst hrl; simp only [Bool.false_eq_true, if_false]; exact i5,
    i6, i7, i8, i9, i10, fun x => i11 x, i12⟩

theorem fwdView_empty {ws : PState} {aq : Bool} {a : Int} {t : Nat} (h : ws.wFwd = ∅) : fwdView ws aq a t = t := by
  unfold fwdView; rw [h, lookupEmpty]

/-! ## 2. Pre-views -/

theorem ldPre_ge (ws : PState) (aq rl : Bool) (va : Nat) :
    va ≤ ldPre ws aq rl va ∧ ws.wVrNew ≤ ldPre ws aq rl va ∧ (aq = true → ws.wVRel ≤ ldPre ws aq rl va) := by
  unfold ldPre
  refine ⟨by omega, by omega, fun h => by subst h; simp only [if_true]; omega⟩

theorem stPreA_ge (ws : PState) (aq rl : Bool) (va vd : Nat) :
    va ≤ stPreA ws aq rl va vd ∧ vd ≤ stPreA ws aq rl va vd ∧ ws.wVcap ≤ stPreA ws aq rl va vd ∧
    ws.wVwNew ≤ stPreA ws aq rl va vd ∧
    (rl = true → ws.wVrOld ≤ stPreA ws aq rl va vd ∧ ws.wVwOld ≤ stPreA ws aq rl va vd) := by
  unfold stPreA stPre
  refine ⟨by omega, by omega, by omega, by omega, fun h => by subst h; simp only [if_true]; omega⟩

theorem stPre_ge (ws : PState) (rl : Bool) (va vd : Nat) :
    va ≤ stPre ws rl va vd ∧ vd ≤ stPre ws rl va vd ∧ ws.wVcap ≤ stPre ws rl va vd ∧ ws.wVwNew ≤ stPre ws rl va vd ∧
    (rl = true → ws.wVrOld ≤ stPre ws rl va vd ∧ ws.wVwOld ≤ stPre ws rl va vd) := by
  unfold stPre
  refine ⟨by omega, by omega, by omega, by omega, fun h => by subst h; simp only [if_true]; omega⟩

/-! ## 3. Store and AMO posts -/

theorem storeBytes_mono : ∀ (ws : PState) (a : Int) (n ts fv : Nat),
    (storeBytes ws a n ts fv).wRegv = ws.wRegv ∧ (storeBytes ws a n ts fv).wVrOld = ws.wVrOld ∧
    (storeBytes ws a n ts fv).wVwOld = ws.wVwOld ∧ (storeBytes ws a n ts fv).wVrNew = ws.wVrNew ∧
    (storeBytes ws a n ts fv).wVwNew = ws.wVwNew ∧ (storeBytes ws a n ts fv).wVcap = ws.wVcap ∧
    (storeBytes ws a n ts fv).wVRel = ws.wVRel ∧ (storeBytes ws a n ts fv).wLdv = ws.wLdv ∧
    (storeBytes ws a n ts fv).wRes = ws.wRes ∧
    (∀ x, coh ws x ≤ coh (storeBytes ws a n ts fv) x) ∧
    (∀ j : Nat, j < n → ts ≤ coh (storeBytes ws a n ts fv) (a + j))
  | ws, _, 0, _, _ => ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ => Nat.le_refl _, fun j hj => by omega⟩
  | ws, a, n + 1, ts, fv => by
    obtain ⟨i1, i2, i3, i4, i5, i6, i7, i8, i9, i10, i11⟩ :=
      storeBytes_mono { ws with wCoh := insert ws.wCoh a (max (coh ws a) ts), wFwd := insert ws.wFwd a (ts, fv) }
        (a + 1) n ts fv
    simp only [storeBytes]
    refine ⟨i1, i2, i3, i4, i5, i6, i7, i8, i9, fun x => Nat.le_trans ?_ (i10 x), fun j hj => ?_⟩
    · have := coh_insert_ge ws a x (max (coh ws a) ts) (by omega)
      unfold coh at this ⊢; exact this
    · cases j with
      | zero =>
        rw [show a + ((0 : Nat) : Int) = a by omega]
        refine Nat.le_trans ?_ (i10 a)
        unfold coh; simp only [lookupInsert, Option.getD_some]; omega
      | succ j =>
        have := i11 j (by omega)
        rw [show a + 1 + (j : Int) = a + ((j + 1 : Nat) : Int) by omega] at this
        exact this

theorem storeRun_mono (ws : PState) (rl : Bool) (va fv : Nat) (base : Int) (n ts : Nat) :
    (storeRun ws rl va fv base n ts).wRegv = ws.wRegv ∧ (storeRun ws rl va fv base n ts).wVrOld = ws.wVrOld ∧
    (storeRun ws rl va fv base n ts).wVwOld = max ws.wVwOld ts ∧
    (storeRun ws rl va fv base n ts).wVrNew = ws.wVrNew ∧ (storeRun ws rl va fv base n ts).wVwNew = ws.wVwNew ∧
    (storeRun ws rl va fv base n ts).wVcap = max va ws.wVcap ∧
    (storeRun ws rl va fv base n ts).wVRel = (if rl then max ws.wVRel ts else ws.wVRel) ∧
    (storeRun ws rl va fv base n ts).wLdv = ws.wLdv ∧ (storeRun ws rl va fv base n ts).wRes = ws.wRes ∧
    (∀ x, coh ws x ≤ coh (storeRun ws rl va fv base n ts) x) ∧
    (∀ j : Nat, j < n → ts ≤ coh (storeRun ws rl va fv base n ts) (base + j)) ∧
    (∀ x, get? (storeRun ws rl va fv base n ts).wFwd x =
      if base ≤ x ∧ x < base + n then some (ts, fv) else get? ws.wFwd x) := by
  obtain ⟨i1, i2, i3, i4, i5, i6, i7, i8, i9, i10, i11⟩ := storeBytes_mono ws base n ts fv
  unfold storeRun
  refine ⟨i1, i2, by simp only; rw [i3], i4, i5, by simp only; rw [i6], by simp only; rw [i7], i8, i9,
    fun x => i10 x, fun j hj => i11 j hj, fun x => storeBytes_fwd' ws base n ts fv x⟩

/-- COH of a store's byte 0. -/
theorem cohBelow_b0 {ws : PState} {base : Int} {n ts : Nat} (h : cohBelow ws base n ts) (hn : 0 < n) :
    coh ws base < ts := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  exact h.1

/-- A store raises `coh` of its byte 0 to its timestamp. -/
theorem storeRun_coh0 (ws : PState) (rl : Bool) (va fv : Nat) (base : Int) (n ts : Nat) (hn : 0 < n) :
    ts ≤ coh (storeRun ws rl va fv base n ts) base := by
  have := (storeRun_mono ws rl va fv base n ts).2.2.2.2.2.2.2.2.2.2.1 0 hn
  simpa using this

/-- A load raises `coh` of its byte 0 to the byte's source. -/
theorem loadRun_coh0 (ws : PState) (aq rl : Bool) (va : Nat) (base : Int) (t : Nat) (v : BitVec 8)
    (r : List (Nat × BitVec 8)) : t ≤ coh (loadRun ws aq rl va base ((t, v) :: r)) base :=
  (loadRun_b0 ws aq rl va base t v r).2.2.2.1

theorem acqPost_false (ws : PState) (ts : Nat) : acqPost ws false ts = ws := by
  unfold acqPost; simp

theorem amoPost_spec (ws : PState) (aq : Bool) (ts : Nat) :
    (amoPost ws aq ts).wRegv = ws.wRegv ∧ (amoPost ws aq ts).wVrOld = max ws.wVrOld ts ∧
    (amoPost ws aq ts).wVwOld = ws.wVwOld ∧ (amoPost ws aq ts).wLdv = max ws.wLdv ts ∧
    (amoPost ws aq ts).wVcap = ws.wVcap ∧ (amoPost ws aq ts).wFwd = ws.wFwd ∧ (∀ x, coh (amoPost ws aq ts) x = coh ws x) ∧
    (amoPost ws aq ts).wVrNew = (if aq then max ws.wVrNew ts else ws.wVrNew) ∧
    (amoPost ws aq ts).wVwNew = (if aq then max ws.wVwNew ts else ws.wVwNew) := by
  unfold amoPost; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, fun _ => rfl, rfl, rfl⟩

/-! ## 4. Reads -/

theorem writesIn_mono {log : List PMsg} {a : Int} {lo hi hi' : Nat} (h : writesIn log a lo hi) (hle : hi ≤ hi') :
    writesIn log a lo hi' := by
  obtain ⟨t, h1, h2, m, hm, hb⟩ := h
  exact ⟨t, h1, by omega, m, hm, hb⟩

/-- A message at `k + 1` covering `a`, in `(lo, hi]`, is a write to `a` in the window. -/
theorem writesIn_of {log : List PMsg} {a : Int} {lo hi k : Nat} {m : PMsg} (hm : log[k]? = some m)
    (hb : (m.byteAt a).isSome = true) (h1 : lo < k + 1) (h2 : k + 1 ≤ hi) : writesIn log a lo hi :=
  ⟨k + 1, h1, h2, m, by simpa using hm, hb⟩

/-- **The load-value fact of byte 0** (machine v2's `loadOk`, M9): its value is the memory's at its timestamp, and no
write to the byte lies between its timestamp and `max vpre coh` (or the invalidate clause applies). -/
theorem loadOk_b0 {img : Image} {log : List PMsg} {ws : PState} {vpre : Nat} {base : Int} {t : Nat}
    {v : BitVec 8} {r : List (Nat × BitVec 8)} (h : loadOk img log ws vpre base ((t, v) :: r)) :
    memByte img log t base = some v ∧
    (¬ writesIn log base t (max vpre (coh ws base)) ∨ invalRead log base t (max vpre (coh ws base))) := by
  obtain ⟨⟨hm, hw⟩, _⟩ := h
  refine ⟨hm, ?_⟩
  rcases hw with hw | hw
  · left
    intro hc
    apply hw
    refine writesIn_mono hc ?_
    split <;> omega
  · exact .inr hw

/-- `loadOk_b0` without the invalidate clause (`noCmo`). -/
theorem loadOk_b0nc {img : Image} {log : List PMsg} {ws : PState} {vpre : Nat} {base : Int} {t : Nat}
    {v : BitVec 8} {r : List (Nat × BitVec 8)} (hnc : noCmo log) (h : loadOk img log ws vpre base ((t, v) :: r)) :
    memByte img log t base = some v ∧ ¬ writesIn log base t (max vpre (coh ws base)) := by
  obtain ⟨hm, hw⟩ := loadOk_b0 h
  exact ⟨hm, hw.resolve_right (noInval hnc)⟩

/-- **The single read point (M9) for a 2-byte load whose bytes are not forwarded**: no write to byte 0 lies between
its timestamp and byte 1's. -/
theorem loadOk_sp2 {img : Image} {log : List PMsg} {ws : PState} {vpre : Nat} {base : Int} {t0 t1 : Nat}
    {v0 v1 : BitVec 8} (hnc : noCmo log) (h : loadOk img log ws vpre base [(t0, v0), (t1, v1)])
    (hf0 : fwdHit ws base t0 = false) (hf1 : fwdHit ws (base + 1) t1 = false) : ¬ writesIn log base t0 t1 := by
  obtain ⟨⟨_, hw⟩, _⟩ := h
  have hw := hw.resolve_right (noInval hnc)
  intro hc
  apply hw
  refine writesIn_mono hc ?_
  simp only [hf0, Bool.false_eq_true, if_false, nonFwdMax, bytesMax, hf1]
  omega

/-- (X4) at byte 0, with the state pinned by the load's admissibility. -/
theorem loadRun_ldv_of {img : Image} {log : List PMsg} {ws : PState} {aq rl : Bool} {va : Nat} {base : Int} {t : Nat}
    {v : BitVec 8} {r : List (Nat × BitVec 8)} (_ : loadOk img log ws (ldPre ws aq rl va) base ((t, v) :: r)) :
    max (ldPre ws aq rl va) (fwdView ws aq base t) ≤ (loadRun ws aq rl va base ((t, v) :: r)).wLdv :=
  (loadRun_b0 ws aq rl va base t v r).1

/-- **A FORWARDED-OR-LATER READ (rule 12's view, M2)**: after an own store `tf` with forward view `vf` to `base`
(bank entry, coherence floor, the store's message), a load's byte 0 either forwards (view `vf`) or reads at or
above `tf`, so its view is at least `min vf tf`. -/
theorem fwdView_ge_of {img : Image} {M : List PMsg} {ws : PState} {vpre : Nat} {base : Int} {t : Nat} {v : BitVec 8}
    {r : List (Nat × BitVec 8)} {tf vf : Nat} {m : PMsg} (hnc : noCmo M) (hlo : loadOk img M ws vpre base ((t, v) :: r))
    (hfwd : get? ws.wFwd base = some (tf, vf)) (hcoh : tf ≤ coh ws base) (hm : M[tf - 1]? = some m)
    (hcov : (m.byteAt base).isSome = true) (htf : 0 < tf) : min vf tf ≤ fwdView ws false base t := by
  unfold fwdView
  rw [hfwd]
  show min vf tf ≤ (if t = tf then vf else t)
  split
  · omega
  · have hw := (loadOk_b0nc hnc hlo).2
    rcases Nat.lt_or_ge t tf with h | h
    · exact absurd (writesIn_of (k := tf - 1) hm hcov (by omega) (by omega)) hw
    · omega

/-! ## 5. A0 for kit programs -/

/-- **A0 for a kit program** (`PF.adequacy` with `Ψ h = ΨK M (Qs h)`): the exports (i), (ii) at the final trace,
(iii), (iv), (v), and `noCmo M` (every message is fulfilled by some hart, (iii), whose trace records `wrOk`). -/
theorem kitAdeq {V : Type} {pdone : LP → Option V} {T : Test} {π : Proto} {M : List PMsg} {run : PFRun LP Unit}
    (Qs : Nat → Trace → Prop) (Φ : Nat → V → Prop) (himg : PO_img π (testImg T)) (hQ0 : ∀ h, Qs h [])
    (hwp : ∀ h p, (progs T)[h]? = some p → ∀ [InvGS_gen HasLC.hasLC pfGF],
      ⊢@{IProp pfGF} wpPF π ⟨litStep, pdone, testImg T, M, h⟩ (ΨK M (Qs h)) p
        (fun v => iprop(⌜∃ V, grd π (testImg T) M V (Φ h v)⌝)))
    (hrun : validRun litStep (testImg T) () (progs T) M run) :
    (∀ h v, run.done pdone h v → Φ h v) ∧ (∀ h, Qs h (memEv (run.trace h))) ∧ noCmo M ∧
    (∀ t, 1 ≤ t → t ≤ M.length → exU (fun h => t ∈ run.fulfils h ∧ tidAt M t = some h)) ∧ run.traceWf M ∧
    run.cfg.pcImg = testImg T ∧ Valid π (testImg T) M M.length := by
  have hnoinv := Own.lit_noInvalT hrun   -- MachFix-R-b5
  obtain ⟨hi, hii, hpart, _, hval, hwf, _⟩ := adequacy (hlc := HasLC.hasLC) (GF := pfGF) (pdone := pdone)
    π Φ (fun h => ΨK M (Qs h)) himg (PO_ad_all _ _ _) (fun h => ⟨hQ0 h, wrOk_nil M⟩) (devFree_lit _) hwp hrun
  have hfin : ∀ h, ΨK M (Qs h) (run.trace h) := fun h => by simpa using hii h (run.trace h).length
  refine ⟨hi, fun h => (hfin h).1, fun k m hm => ?_, hpart, hwf, validRun_img hrun.1, hval⟩
  have hkl : k < M.length := (List.getElem?_eq_some_iff.1 hm).1
  obtain ⟨h, ⟨hin, _⟩, _⟩ := hpart (k + 1) (by omega) (by omega)
  unfold PFRun.fulfils fulfilsOf at hin
  obtain ⟨e, he, het⟩ := List.mem_filterMap.1 hin
  exact (hfin h).2 e he (k + 1) het m (by simpa [msgAt] using hm)

/-- **THE WRITER OF A MESSAGE** (A0 (iii) + (v)): a timestamped memory entry of some hart, whose label writes it. -/
theorem kit_writer {P D : Type} {run : PFRun P D} {M : List PMsg}
    (hpart : ∀ t, 1 ≤ t → t ≤ M.length → exU (fun h => t ∈ run.fulfils h ∧ tidAt M t = some h))
    (hwf : run.traceWf M) {k : Nat} {m : PMsg} (hm : M[k]? = some m) :
    ∃ h, ∃ e ∈ memEv (run.trace h), e.2 = some (k + 1) ∧ labelWrite e.1 = some (m.pa, m.data) := by
  obtain ⟨h, e, he, het⟩ := fulfil_entry hm hpart
  refine ⟨h, e, memEv_of_ts he het, het, ?_⟩
  have hx := (hwf h e he).2
  rw [het] at hx
  rcases hlw : labelWrite e.1 with _ | ⟨b, d⟩
  · simp only [hlw] at hx
  · simp only [hlw] at hx
    obtain ⟨m', hm', hpa, hdata, _⟩ := hx
    simp only [Nat.add_sub_cancel] at hm'
    rw [hm] at hm'; cases hm'
    rw [hpa, hdata]

/-- The bytes a load-like memory entry read are the memory's (A0 (v)). -/
theorem kit_read {P D : Type} {run : PFRun P D} {M : List PMsg} (hwf : run.traceWf M) {h : Nat} {e : PEv}
    (he : e ∈ memEv (run.trace h)) {base : Int} {tvs : List (Nat × BitVec 8)} (hr : labelReads e.1 = some (base, tvs)) :
    bytesAll (fun a t v => memByte run.cfg.pcImg M t a = some v) base tvs :=
  (hwf h e (mem_of_memEv he)).1 base tvs hr

/-- The byte a message writes at `a`, from its base and data. -/
theorem byteAt_eq (m : PMsg) (a : Int) : m.byteAt a = if m.pa ≤ a then m.data[(a - m.pa).toNat]? else none := rfl

/-! ## 6. Final memory -/

/-- The final byte at `a`: the latest message writing it, else the image. -/
def lastByte (img : Image) (M : List PMsg) (a : Int) : Nat :=
  match (M.filter (fun m => (m.byteAt a).isSome)).getLast? with
  | some m => ((m.byteAt a).map BitVec.toNat).getD 0
  | none => ((img a).map BitVec.toNat).getD 0

theorem lastByte_lt (img : Image) (M : List PMsg) (a : Int) : lastByte img M a < 256 := by
  unfold lastByte
  split
  · next m _ =>
    cases hb : m.byteAt a with
    | none => simp
    | some b => simp only [Option.map_some, Option.getD_some]; exact b.isLt
  · cases hi : img a with
    | none => simp
    | some b => simp only [Option.map_some, Option.getD_some]; exact b.isLt

/-- The final byte of a location (byte 0 of `finalMem`, MachLitmus.lean) is `lastByte`. -/
theorem finalMem_b0 {img : Image} {M : List PMsg} {a n v : Nat} (h : finalMem img M a n = v) (hn : 0 < n) :
    lastByte img M (a : Int) = v % 256 := by
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  unfold finalMem at h
  rw [List.range_succ_eq_map, List.map_cons] at h
  change lastByte img M ((a : Int) + ((0 : Nat) : Int)) + 256 * bytesVal _ = v at h
  rw [show ((a : Int) + ((0 : Nat) : Int)) = (a : Int) by omega] at h
  have := lastByte_lt img M (a : Int)
  omega

theorem getLast?_filter_spec {α : Type} (p : α → Bool) : ∀ (l : List α) (x : α), (l.filter p).getLast? = some x →
    ∃ k : Nat, l[k]? = some x ∧ p x = true ∧ ∀ (k' : Nat) (y : α), k < k' → l[k']? = some y → p y = false
  | [], x, h => by simp at h
  | a :: l, x, h => by
    by_cases hf : (l.filter p).getLast? = none
    · have hno : ∀ (k' : Nat) (y : α), l[k']? = some y → p y = false := by
        intro k' y hy
        rw [List.getLast?_eq_none_iff, List.filter_eq_nil_iff] at hf
        have := hf y (List.mem_of_getElem? hy); simpa using this
      rw [List.filter_cons] at h
      split at h
      · next hpa =>
        rw [List.getLast?_cons, hf] at h
        simp only [Option.getD_none, Option.some.injEq] at h
        subst h
        refine ⟨0, rfl, hpa, fun k' y hk hy => ?_⟩
        obtain ⟨k'', rfl⟩ : ∃ k'', k' = k'' + 1 := ⟨k' - 1, by omega⟩
        exact hno k'' y (by simpa using hy)
      · rw [hf] at h; cases h
    · obtain ⟨x', hx'⟩ := Option.ne_none_iff_exists'.1 hf
      have hx : x' = x := by
        rw [List.filter_cons] at h
        split at h
        · rw [List.getLast?_cons, hx'] at h; simpa using h
        · rw [hx'] at h; simpa using h
      subst hx
      obtain ⟨k, hk, hp, hlast⟩ := getLast?_filter_spec p l x' hx'
      exact ⟨k + 1, by simpa using hk, hp, fun k' y hk' hy => by
        obtain ⟨k'', rfl⟩ : ∃ k'', k' = k'' + 1 := ⟨k' - 1, by omega⟩
        exact hlast k'' y (by omega) (by simpa using hy)⟩

/-- **The final byte is the last writer's**, or the image's when no message writes the byte. -/
theorem lastByte_cases (img : Image) (M : List PMsg) (a : Int) :
    (∃ (k : Nat) (m : PMsg), M[k]? = some m ∧ (m.byteAt a).isSome = true ∧
      lastByte img M a = ((m.byteAt a).map BitVec.toNat).getD 0 ∧
      ∀ (k' : Nat) (m' : PMsg), k < k' → M[k']? = some m' → (m'.byteAt a).isSome = false) ∨
    ((∀ (k : Nat) (m : PMsg), M[k]? = some m → (m.byteAt a).isSome = false) ∧
      lastByte img M a = ((img a).map BitVec.toNat).getD 0) := by
  cases hl : (M.filter (fun m => (m.byteAt a).isSome)).getLast? with
  | some m =>
    obtain ⟨k, hk, hp, hlast⟩ := getLast?_filter_spec _ M m hl
    refine .inl ⟨k, m, hk, hp, ?_, hlast⟩
    unfold lastByte; rw [hl]
  | none =>
    refine .inr ⟨fun k m hm => ?_, by unfold lastByte; rw [hl]⟩
    rw [List.getLast?_eq_none_iff, List.filter_eq_nil_iff] at hl
    simpa using hl m (List.mem_of_getElem? hm)

/-- **THE LAST WRITER OUTRUNS THE OTHERS**: if the final byte at `a` is `v` (not the image's), and `j` is the only
message holding `v` there, every other message writing `a` is below `j`. -/
theorem last_order {img : Image} {M : List PMsg} {a : Int} {v : Nat} (hl : lastByte img M a = v)
    (hv : ((img a).map BitVec.toNat).getD 0 ≠ v) {i j : Nat} {mi : PMsg} (hmi : M[i]? = some mi)
    (hci : (mi.byteAt a).isSome = true) (hvi : ((mi.byteAt a).map BitVec.toNat).getD 0 ≠ v)
    (huniq : ∀ (k : Nat) (m : PMsg), M[k]? = some m → (m.byteAt a).isSome = true →
      ((m.byteAt a).map BitVec.toNat).getD 0 = v → k = j) : i < j := by
  rcases lastByte_cases img M a with ⟨k, m, hk, hs, hlb, hlast⟩ | ⟨_, hlb⟩
  · have hkj := huniq k m hk hs (by rw [← hlb, hl])
    subst hkj
    rcases Nat.lt_trichotomy i k with h | h | h
    · exact h
    · subst h; rw [hmi] at hk; cases hk; exact absurd (by rw [← hlb, hl]) hvi
    · have := hlast i mi h hmi; rw [this] at hci; cases hci
  · exact absurd (by rw [← hlb, hl]) hv

/-- The final byte is that of the last message writing it. -/
theorem lastByte_eq_of {img : Image} {M : List PMsg} {a : Int} {j : Nat} {m : PMsg} (hm : M[j]? = some m)
    (hb : (m.byteAt a).isSome = true)
    (hlast : ∀ (k : Nat) (m' : PMsg), j < k → M[k]? = some m' → (m'.byteAt a).isSome = false) :
    lastByte img M a = ((m.byteAt a).map BitVec.toNat).getD 0 := by
  rcases lastByte_cases img M a with ⟨k, m', hk, hs, hlb, hl'⟩ | ⟨hno, _⟩
  · rcases Nat.lt_trichotomy k j with h | h | h
    · have := hl' j m h hm; rw [this] at hb; cases hb
    · subst h; rw [hm] at hk; cases hk; exact hlb
    · have := hlast k m' h hk; rw [this] at hs; cases hs
  · have := hno j m hm; rw [this] at hb; cases hb

/-- `finalMem` from the final bytes. -/
theorem finalMem_of_bytes {img : Image} {M : List PMsg} {a n : Nat} {d : List (BitVec 8)} (hl : d.length = n)
    (hb : ∀ k, k < n → lastByte img M ((a : Int) + (k : Int)) = ((d[k]?).map BitVec.toNat).getD 0) :
    finalMem img M a n = bytesVal (d.map BitVec.toNat) := by
  unfold finalMem
  congr 1
  apply List.ext_getElem (by simp [hl])
  intro k h1 h2
  rw [List.getElem_map, List.getElem_map, List.getElem_range]
  simp only [List.length_map, List.length_range] at h1
  have := hb k h1
  rw [List.getElem?_eq_getElem (by omega)] at this
  simp only [Option.map_some, Option.getD_some] at this
  exact this

/-! ## 7. Field equations of the posts (simp set `kitv`) -/

section fields

variable (ws : PState)

@[simp] theorem instrR_vrOld : (instrR ws).wVrOld = ws.wVrOld := rfl
@[simp] theorem instrR_vwOld : (instrR ws).wVwOld = ws.wVwOld := rfl
@[simp] theorem instrR_vrNew : (instrR ws).wVrNew = ws.wVrNew := rfl
@[simp] theorem instrR_vwNew : (instrR ws).wVwNew = ws.wVwNew := rfl
@[simp] theorem instrR_vRel : (instrR ws).wVRel = ws.wVRel := rfl
@[simp] theorem instrR_fwd : (instrR ws).wFwd = ws.wFwd := rfl
@[simp] theorem instrR_regv (r : Nat) : regv (instrR ws) r = regv ws r := rfl
@[simp] theorem instrR_vcap : (instrR ws).wVcap = ws.wVcap := rfl
@[simp] theorem instrR_ldv : (instrR ws).wLdv = 0 := rfl
@[simp] theorem instrR_coh (a : Int) : coh (instrR ws) a = coh ws a := rfl
@[simp] theorem instrR_res : (instrR ws).wRes = ws.wRes := rfl
@[simp] theorem instrR_ifv : (instrR ws).wIfv = 0 := rfl

@[simp] theorem regWP_vrOld (rd : Nat) (srcs : List Dsrc) : (regWP ws rd srcs).wVrOld = ws.wVrOld := rfl
@[simp] theorem regWP_vwOld (rd : Nat) (srcs : List Dsrc) : (regWP ws rd srcs).wVwOld = ws.wVwOld := rfl
@[simp] theorem regWP_vrNew (rd : Nat) (srcs : List Dsrc) : (regWP ws rd srcs).wVrNew = ws.wVrNew := rfl
@[simp] theorem regWP_vwNew (rd : Nat) (srcs : List Dsrc) : (regWP ws rd srcs).wVwNew = ws.wVwNew := rfl
@[simp] theorem regWP_vRel (rd : Nat) (srcs : List Dsrc) : (regWP ws rd srcs).wVRel = ws.wVRel := rfl
@[simp] theorem regWP_fwd (rd : Nat) (srcs : List Dsrc) : (regWP ws rd srcs).wFwd = ws.wFwd := rfl
@[simp] theorem regWP_vcap (rd : Nat) (srcs : List Dsrc) : (regWP ws rd srcs).wVcap = ws.wVcap := rfl
@[simp] theorem regWP_ldv (rd : Nat) (srcs : List Dsrc) : (regWP ws rd srcs).wLdv = ws.wLdv := rfl
@[simp] theorem regWP_coh (rd : Nat) (srcs : List Dsrc) (a : Int) : coh (regWP ws rd srcs) a = coh ws a := rfl
@[simp] theorem regWP_res (rd : Nat) (srcs : List Dsrc) : (regWP ws rd srcs).wRes = ws.wRes := rfl
@[simp] theorem regWP_ifv (rd : Nat) (srcs : List Dsrc) : (regWP ws rd srcs).wIfv = ws.wIfv := rfl
@[simp] theorem regWP_regv (rd : Nat) (srcs : List Dsrc) (r : Nat) :
    regv (regWP ws rd srcs) r = if r = rd then srcsView ws srcs else regv ws r := by
  unfold regWP regv
  by_cases h : r = rd
  · subst h; simp only [lookupInsert, Option.getD_some, if_true]
  · simp only; rw [lookupInsertNe (Ne.symm h), if_neg h]

@[simp] theorem ctrlP_vrOld (srcs : List Dsrc) : (ctrlP ws srcs).wVrOld = ws.wVrOld := rfl
@[simp] theorem ctrlP_vwOld (srcs : List Dsrc) : (ctrlP ws srcs).wVwOld = ws.wVwOld := rfl
@[simp] theorem ctrlP_vrNew (srcs : List Dsrc) : (ctrlP ws srcs).wVrNew = ws.wVrNew := rfl
@[simp] theorem ctrlP_vwNew (srcs : List Dsrc) : (ctrlP ws srcs).wVwNew = ws.wVwNew := rfl
@[simp] theorem ctrlP_vRel (srcs : List Dsrc) : (ctrlP ws srcs).wVRel = ws.wVRel := rfl
@[simp] theorem ctrlP_fwd (srcs : List Dsrc) : (ctrlP ws srcs).wFwd = ws.wFwd := rfl
@[simp] theorem ctrlP_vcap (srcs : List Dsrc) : (ctrlP ws srcs).wVcap = max (srcsView ws srcs) ws.wVcap := rfl
@[simp] theorem ctrlP_ldv (srcs : List Dsrc) : (ctrlP ws srcs).wLdv = ws.wLdv := rfl
@[simp] theorem ctrlP_coh (srcs : List Dsrc) (a : Int) : coh (ctrlP ws srcs) a = coh ws a := rfl
@[simp] theorem ctrlP_regv (srcs : List Dsrc) (r : Nat) : regv (ctrlP ws srcs) r = regv ws r := rfl
@[simp] theorem ctrlP_ifv (srcs : List Dsrc) : (ctrlP ws srcs).wIfv = ws.wIfv := rfl

@[simp] theorem fence_vrOld (pr pw sr sw : Bool) : (fencePost ws pr pw sr sw).wVrOld = ws.wVrOld := rfl
@[simp] theorem fence_vwOld (pr pw sr sw : Bool) : (fencePost ws pr pw sr sw).wVwOld = ws.wVwOld := rfl
@[simp] theorem fence_vrNew (pr pw sr sw : Bool) : (fencePost ws pr pw sr sw).wVrNew =
    if sr then max ws.wVrNew (max (if pr then ws.wVrOld else 0) (if pw then ws.wVwOld else 0)) else ws.wVrNew := rfl
@[simp] theorem fence_vwNew (pr pw sr sw : Bool) : (fencePost ws pr pw sr sw).wVwNew =
    if sw then max ws.wVwNew (max (if pr then ws.wVrOld else 0) (if pw then ws.wVwOld else 0)) else ws.wVwNew := rfl
@[simp] theorem fence_vRel (pr pw sr sw : Bool) : (fencePost ws pr pw sr sw).wVRel = ws.wVRel := rfl
@[simp] theorem fence_fwd (pr pw sr sw : Bool) : (fencePost ws pr pw sr sw).wFwd = ws.wFwd := rfl
@[simp] theorem fence_vcap (pr pw sr sw : Bool) : (fencePost ws pr pw sr sw).wVcap = ws.wVcap := rfl
@[simp] theorem fence_ldv (pr pw sr sw : Bool) : (fencePost ws pr pw sr sw).wLdv = ws.wLdv := rfl
@[simp] theorem fence_coh (pr pw sr sw : Bool) (a : Int) : coh (fencePost ws pr pw sr sw) a = coh ws a := rfl
@[simp] theorem fence_regv (pr pw sr sw : Bool) (r : Nat) : regv (fencePost ws pr pw sr sw) r = regv ws r := rfl
@[simp] theorem fence_ifv (pr pw sr sw : Bool) : (fencePost ws pr pw sr sw).wIfv = ws.wIfv := rfl
@[simp] theorem fence_res (pr pw sr sw : Bool) : (fencePost ws pr pw sr sw).wRes = ws.wRes := rfl

@[simp] theorem storeRun_vrOld (rl : Bool) (va fv : Nat) (base : Int) (n ts : Nat) :
    (storeRun ws rl va fv base n ts).wVrOld = ws.wVrOld := (storeRun_mono ws rl va fv base n ts).2.1
@[simp] theorem storeRun_vwOld (rl : Bool) (va fv : Nat) (base : Int) (n ts : Nat) :
    (storeRun ws rl va fv base n ts).wVwOld = max ws.wVwOld ts := (storeRun_mono ws rl va fv base n ts).2.2.1
@[simp] theorem storeRun_vrNew (rl : Bool) (va fv : Nat) (base : Int) (n ts : Nat) :
    (storeRun ws rl va fv base n ts).wVrNew = ws.wVrNew := (storeRun_mono ws rl va fv base n ts).2.2.2.1
@[simp] theorem storeRun_vwNew (rl : Bool) (va fv : Nat) (base : Int) (n ts : Nat) :
    (storeRun ws rl va fv base n ts).wVwNew = ws.wVwNew := (storeRun_mono ws rl va fv base n ts).2.2.2.2.1
@[simp] theorem storeRun_vcap (rl : Bool) (va fv : Nat) (base : Int) (n ts : Nat) :
    (storeRun ws rl va fv base n ts).wVcap = max va ws.wVcap := (storeRun_mono ws rl va fv base n ts).2.2.2.2.2.1
@[simp] theorem storeRun_vRel (rl : Bool) (va fv : Nat) (base : Int) (n ts : Nat) :
    (storeRun ws rl va fv base n ts).wVRel = (if rl then max ws.wVRel ts else ws.wVRel) :=
  (storeRun_mono ws rl va fv base n ts).2.2.2.2.2.2.1
@[simp] theorem storeRun_ldv (rl : Bool) (va fv : Nat) (base : Int) (n ts : Nat) :
    (storeRun ws rl va fv base n ts).wLdv = ws.wLdv := (storeRun_mono ws rl va fv base n ts).2.2.2.2.2.2.2.1
@[simp] theorem storeRun_res (rl : Bool) (va fv : Nat) (base : Int) (n ts : Nat) :
    (storeRun ws rl va fv base n ts).wRes = ws.wRes := (storeRun_mono ws rl va fv base n ts).2.2.2.2.2.2.2.2.1
@[simp] theorem storeRun_regv (rl : Bool) (va fv : Nat) (base : Int) (n ts : Nat) (r : Nat) :
    regv (storeRun ws rl va fv base n ts) r = regv ws r := by
  unfold regv; rw [(storeRun_mono ws rl va fv base n ts).1]

@[simp] theorem acqPost_false' (ts : Nat) : acqPost ws false ts = ws := acqPost_false ws ts

@[simp] theorem storeRun_fwd_get (rl : Bool) (va fv : Nat) (base : Int) (n ts : Nat) (x : Int) :
    get? (storeRun ws rl va fv base n ts).wFwd x =
      if base ≤ x ∧ x < base + n then some (ts, fv) else get? ws.wFwd x :=
  (storeRun_mono ws rl va fv base n ts).2.2.2.2.2.2.2.2.2.2.2 x

@[simp] theorem loadRun_regv' (aq rl : Bool) (va : Nat) (base : Int) (tvs : List (Nat × BitVec 8)) (r : Nat) :
    regv (loadRun ws aq rl va base tvs) r = regv ws r := by
  unfold regv; rw [(loadRun_mono ws aq rl va base tvs).1]
@[simp] theorem loadRun_fwd (aq rl : Bool) (va : Nat) (base : Int) (tvs : List (Nat × BitVec 8)) :
    (loadRun ws aq rl va base tvs).wFwd = ws.wFwd := (loadRun_mono ws aq rl va base tvs).2.1
@[simp] theorem loadRun_vwOld (aq rl : Bool) (va : Nat) (base : Int) (tvs : List (Nat × BitVec 8)) :
    (loadRun ws aq rl va base tvs).wVwOld = ws.wVwOld := (loadRun_mono ws aq rl va base tvs).2.2.1
@[simp] theorem loadRun_vcap (aq rl : Bool) (va : Nat) (base : Int) (tvs : List (Nat × BitVec 8)) :
    (loadRun ws aq rl va base tvs).wVcap = max va ws.wVcap := (loadRun_mono ws aq rl va base tvs).2.2.2.1
@[simp] theorem loadRun_res (aq rl : Bool) (va : Nat) (base : Int) (tvs : List (Nat × BitVec 8)) :
    (loadRun ws aq rl va base tvs).wRes = ws.wRes := (loadRun_mono ws aq rl va base tvs).2.2.2.2.2.1
@[simp] theorem loadRun_vrNew_pl (rl : Bool) (va : Nat) (base : Int) (tvs : List (Nat × BitVec 8)) :
    (loadRun ws false rl va base tvs).wVrNew = ws.wVrNew := ((loadRun_mono ws false rl va base tvs).2.2.2.2.2.2.2.2.2.2.2 rfl).1
@[simp] theorem loadRun_vwNew_pl (rl : Bool) (va : Nat) (base : Int) (tvs : List (Nat × BitVec 8)) :
    (loadRun ws false rl va base tvs).wVwNew = ws.wVwNew := ((loadRun_mono ws false rl va base tvs).2.2.2.2.2.2.2.2.2.2.2 rfl).2

@[simp] theorem amoPost_vrOld (aq : Bool) (ts : Nat) : (amoPost ws aq ts).wVrOld = max ws.wVrOld ts := rfl
@[simp] theorem amoPost_vwOld (aq : Bool) (ts : Nat) : (amoPost ws aq ts).wVwOld = ws.wVwOld := rfl
@[simp] theorem amoPost_ldv (aq : Bool) (ts : Nat) : (amoPost ws aq ts).wLdv = max ws.wLdv ts := rfl
@[simp] theorem amoPost_vcap (aq : Bool) (ts : Nat) : (amoPost ws aq ts).wVcap = ws.wVcap := rfl
@[simp] theorem amoPost_fwd (aq : Bool) (ts : Nat) : (amoPost ws aq ts).wFwd = ws.wFwd := rfl
@[simp] theorem amoPost_coh (aq : Bool) (ts : Nat) (a : Int) : coh (amoPost ws aq ts) a = coh ws a := rfl
@[simp] theorem amoPost_regv (aq : Bool) (ts : Nat) (r : Nat) : regv (amoPost ws aq ts) r = regv ws r := rfl
@[simp] theorem amoPost_vrNew (aq : Bool) (ts : Nat) :
    (amoPost ws aq ts).wVrNew = (if aq then max ws.wVrNew ts else ws.wVrNew) := rfl
@[simp] theorem amoPost_vwNew (aq : Bool) (ts : Nat) :
    (amoPost ws aq ts).wVwNew = (if aq then max ws.wVwNew ts else ws.wVwNew) := rfl
@[simp] theorem amoPost_vRel (aq : Bool) (ts : Nat) : (amoPost ws aq ts).wVRel = ws.wVRel := rfl
@[simp] theorem amoPost_res (aq : Bool) (ts : Nat) : (amoPost ws aq ts).wRes = ws.wRes := rfl

@[simp] theorem qPosts_nil : qPosts ws [] = ws := rfl
@[simp] theorem qPosts_cons (l : PLabel) (r : List PLabel) : qPosts ws (l :: r) = qPosts (qPost ws l) r := rfl
@[simp] theorem qPost_regw (rd : Nat) (srcs : List Dsrc) : qPost ws (LRegW rd srcs) = regWP ws rd srcs := rfl
@[simp] theorem qPost_instr : qPost ws LInstr = instrR ws := rfl
@[simp] theorem qPost_exfail : qPost ws LExFail = { ws with wRes := none } := rfl

@[simp] theorem psInit_fwd : psInit.wFwd = ∅ := rfl
@[simp] theorem psInit_vrOld : psInit.wVrOld = 0 := rfl
@[simp] theorem psInit_vwOld : psInit.wVwOld = 0 := rfl
@[simp] theorem psInit_vrNew : psInit.wVrNew = 0 := rfl
@[simp] theorem psInit_vwNew : psInit.wVwNew = 0 := rfl
@[simp] theorem psInit_vcap : psInit.wVcap = 0 := rfl
@[simp] theorem psInit_vRel : psInit.wVRel = 0 := rfl
@[simp] theorem psInit_ldv : psInit.wLdv = 0 := rfl
@[simp] theorem psInit_ifv : psInit.wIfv = 0 := rfl
@[simp] theorem psInit_regv (r : Nat) : regv psInit r = 0 := by unfold regv; rw [show psInit.wRegv = ∅ from rfl, lookupEmpty]; rfl
@[simp] theorem psInit_coh (a : Int) : coh psInit a = 0 := by unfold coh; rw [show psInit.wCoh = ∅ from rfl, lookupEmpty]; rfl
@[simp] theorem psInit_res : psInit.wRes = none := rfl

@[simp] theorem srcR_pos {r : Nat} (h : r ≠ 0) : srcR r = [.DReg r] := by unfold srcR; rw [if_neg h]
@[simp] theorem srcR_zero : srcR 0 = [] := rfl
@[simp] theorem srcsView_one (d : Dsrc) : srcsView ws [d] = dsrcView ws d := by simp [srcsView]
@[simp] theorem srcsView_app (a b : List Dsrc) : srcsView ws (a ++ b) = max (srcsView ws a) (srcsView ws b) := by
  induction a with
  | nil => simp [srcsView]
  | cons d r ih => simp only [List.cons_append, srcsView, List.foldr_cons] at ih ⊢; rw [ih]; omega
@[simp] theorem dsrcView_reg (r : Nat) : dsrcView ws (.DReg r) = regv ws r := rfl
@[simp] theorem srcsView_cons_s (d : Dsrc) (l : List Dsrc) :
    srcsView ws (d :: l) = max (dsrcView ws d) (srcsView ws l) := rfl
@[simp] theorem srcsView_nil_s : srcsView ws [] = 0 := rfl
@[simp] theorem dsrcView_ld : dsrcView ws .DLdRes = ws.wLdv := rfl

end fields

end Weak.Prom.PF
