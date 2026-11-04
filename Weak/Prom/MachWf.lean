/-
Weak/Prom: **the well-formedness invariant of machine v2** (S0-P part (2), milestone 2b; plan [R7.s1], [R2.s10]).

* `memStep_bnd` — every arm keeps `psBounded ws |log|` and `promWf log i prom` (every view, bank, reservation,
  AMO slot and fetch view is a timestamp of the log; every promise is an own message).
* `pmStep_wf`, `pmSteps_wf` — `runWf` (= `cfgWf` + every log message is a non-trivial message of an existing
  agent + the agent count) holds along every run from `pmInit`.

These bounds are what makes every arm APPEND-STABLE (Machine.lean header): a premise reads the log only inside
windows whose upper end is a view or a fulfilled timestamp, and `psBounded` puts every such end below `|log|`.
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Prom.MachInval   -- MachFix-R-b5 (was: Weak.Prom.Machine)

namespace Weak.Prom

open MachCSL MachCSL.Stdpp Iris.Std
open Weak (Image Dsrc)
open PLabel

/-! ## 1. Generic facts -/

theorem getD_insert_nat {K : Type} [Ord K] [DecidableEq K] [Std.TransCmp (compare : K → K → Ordering)]
    [Std.LawfulEqCmp (compare : K → K → Ordering)] (m : GMapF K Nat) (a b : K) (x : Nat) :
    (get? (insert m a x) b).getD 0 = if a = b then x else (get? m b).getD 0 := by
  by_cases h : a = b
  · subst h; rw [lookupInsert]; simp
  · rw [lookupInsertNe h]; simp [h]

theorem memByte_le {img : Image} {log : List PMsg} {t : Nat} {a : Int} {v : BitVec 8}
    (h : memByte img log t a = some v) : t ≤ log.length := by
  cases t with
  | zero => omega
  | succ k =>
    simp only [memByte] at h
    rcases Nat.lt_or_ge k log.length with hk | hk
    · omega
    · rw [List.getElem?_eq_none hk] at h
      cases h

theorem bytesAll_mono {P Q : Int → Nat → BitVec 8 → Prop} (hPQ : ∀ a t v, P a t v → Q a t v) :
    ∀ (a : Int) (l : List (Nat × BitVec 8)), bytesAll P a l → bytesAll Q a l
  | _, [], _ => trivial
  | a, (t, v) :: r, ⟨h1, h2⟩ => ⟨hPQ a t v h1, bytesAll_mono hPQ (a + 1) r h2⟩

theorem bytesMax_le {f : Int → Nat → Nat} {n : Nat} :
    ∀ (a : Int) (l : List (Nat × BitVec 8)), bytesAll (fun a t _ => f a t ≤ n) a l → bytesMax f a l ≤ n
  | _, [], _ => Nat.zero_le _
  | a, (t, _) :: r, ⟨h1, h2⟩ => by
    simp only [bytesMax]
    have := bytesMax_le (a + 1) r h2
    omega

/-- Every answered timestamp of an admissible read is a log timestamp. -/
theorem loadOk_ts {img : Image} {log : List PMsg} {ws : PState} {vpre : Nat} {base : Int}
    {tvs : List (Nat × BitVec 8)} (h : loadOk img log ws vpre base tvs) :
    bytesAll (fun _ t _ => t ≤ log.length) base tvs :=
  bytesAll_mono (fun _ _ _ hp => memByte_le hp.1) base tvs h

theorem tsList_bnd {n : Nat} : ∀ (a : Int) (l : List (Nat × BitVec 8)),
    bytesAll (fun _ t _ => t ≤ n) a l → tsBounded (l.map Prod.fst) n
  | _, [], _ => fun _ h => by cases h
  | a, (t, _) :: r, ⟨h1, h2⟩ => by
    intro x hx
    simp only [List.map_cons, List.mem_cons] at hx
    rcases hx with hx | hx
    · subst hx; exact h1
    · exact tsList_bnd (a + 1) r h2 x hx

/-! ## 2. Bounds of the post-state functions -/

/-- Introduction form of `psBounded`. -/
theorem psB_intro {ws : PState} {n : Nat}
    (hc : ∀ a, coh ws a ≤ n) (h1 : ws.wVrOld ≤ n) (h2 : ws.wVwOld ≤ n) (h3 : ws.wVrNew ≤ n)
    (h4 : ws.wVwNew ≤ n) (h5 : ws.wVRel ≤ n)
    (hf : ∀ a tf vf, get? ws.wFwd a = some (tf, vf) → tf ≤ n ∧ vf ≤ n) (hr : ∀ r, regv ws r ≤ n)
    (h6 : ws.wVcap ≤ n) (h7 : ws.wLdv ≤ n)
    (hR : ∀ R, ws.wRes = some R → tsBounded R.rvTs n ∧ R.rvView ≤ n)
    (hM : ∀ R, ws.wRmw = some R → tsBounded R.rmTs n)
    (h8 : ws.wIfl ≤ n) (h9 : ws.wIfr ≤ n) (h10 : ws.wIfv ≤ n) : psBounded ws n :=
  ⟨hc, h1, h2, h3, h4, h5, hf, hr, h6, h7, hR, hM, h8, h9, h10⟩

theorem psBounded_mono {ws : PState} {n n' : Nat} (h : psBounded ws n) (hn : n ≤ n') : psBounded ws n' := by
  obtain ⟨hc, h1, h2, h3, h4, h5, hf, hr, h6, h7, hR, hM, h8, h9, h10⟩ := h
  refine psB_intro (fun a => Nat.le_trans (hc a) hn) (by omega) (by omega) (by omega) (by omega) (by omega)
    (fun a tf vf h => ⟨Nat.le_trans (hf a tf vf h).1 hn, Nat.le_trans (hf a tf vf h).2 hn⟩)
    (fun r => Nat.le_trans (hr r) hn) (by omega) (by omega)
    (fun R h => ⟨fun t ht => Nat.le_trans ((hR R h).1 t ht) hn, Nat.le_trans (hR R h).2 hn⟩)
    (fun R h => fun t ht => Nat.le_trans (hM R h t ht) hn) (by omega) (by omega) (by omega)

theorem psInit_bnd (n : Nat) : psBounded psInit n := by
  refine psB_intro (fun a => ?_) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
    (Nat.zero_le _) (fun a tf vf h => ?_) (fun r => ?_) (Nat.zero_le _) (Nat.zero_le _)
    (fun R h => by cases h) (fun R h => by cases h) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
  · simp [coh, psInit, lookupEmpty]
  · simp [psInit, lookupEmpty] at h
  · simp [regv, psInit, lookupEmpty]

theorem srcsView_le {ws : PState} {n : Nat} (hr : ∀ r, regv ws r ≤ n) (hl : ws.wLdv ≤ n) :
    ∀ srcs : List Dsrc, srcsView ws srcs ≤ n
  | [] => Nat.zero_le _
  | s :: r => by
    have e : srcsView ws (s :: r) = max (dsrcView ws s) (srcsView ws r) := rfl
    rw [e]
    have ih := srcsView_le hr hl r
    cases s with
    | DReg x => have e2 : dsrcView ws (.DReg x) = regv ws x := rfl; have := hr x; omega
    | DLdRes => have e2 : dsrcView ws .DLdRes = ws.wLdv := rfl; omega

theorem fwdView_le {ws : PState} {n : Nat} {aq : Bool} {a : Int} {t : Nat}
    (hf : ∀ a tf vf, get? ws.wFwd a = some (tf, vf) → tf ≤ n ∧ vf ≤ n) (ht : t ≤ n) :
    fwdView ws aq a t ≤ n := by
  unfold fwdView
  cases h : get? ws.wFwd a with
  | none => exact ht
  | some p =>
    obtain ⟨tf, vf⟩ := p
    simp only
    split
    · exact (hf a tf vf h).2
    · exact ht

theorem ldPre_le {ws : PState} {n : Nat} {aq rl : Bool} {va : Nat} (h : psBounded ws n) (hva : va ≤ n) :
    ldPre ws aq rl va ≤ n := by
  obtain ⟨_, h1, h2, h3, _, h5, _, _, _, _, _, _, _, _, h10⟩ := h
  unfold ldPre
  split <;> split <;> omega

theorem loadByte_bnd {ws : PState} {n vpre : Nat} {aq : Bool} {a : Int} {t : Nat}
    (h : psBounded ws n) (hv : vpre ≤ n) (ht : t ≤ n) : psBounded (loadByte ws aq vpre a t) n := by
  obtain ⟨hc, h1, h2, h3, h4, h5, hf, hr, h6, h7, hR, hM, h8, h9, h10⟩ := h
  have hfv : fwdView ws aq a t ≤ n := fwdView_le hf ht
  refine psB_intro (fun b => ?_) ?_ h2 ?_ ?_ h5 hf hr h6 ?_ hR hM h8 h9 h10
  · simp only [loadByte, coh, getD_insert_nat]
    split
    · have := hc a; simp only [coh] at this; omega
    · exact hc b
  · simp only [loadByte]; omega
  · simp only [loadByte]; split <;> omega
  · simp only [loadByte]; split <;> omega
  · simp only [loadByte]; omega

theorem loadBytes_bnd {n vpre : Nat} {aq : Bool} (hv : vpre ≤ n) :
    ∀ (ws : PState) (a : Int) (tvs : List (Nat × BitVec 8)),
      psBounded ws n → bytesAll (fun _ t _ => t ≤ n) a tvs → psBounded (loadBytes aq vpre ws a tvs) n
  | _, _, [], h, _ => h
  | ws, a, (_, _) :: r, h, ⟨ht, hr⟩ => loadBytes_bnd hv _ _ r (loadByte_bnd h hv ht) hr

theorem readView_le {ws : PState} {n : Nat} {aq rl : Bool} {va : Nat} {base : Int}
    {tvs : List (Nat × BitVec 8)} (h : psBounded ws n) (hva : va ≤ n)
    (hts : bytesAll (fun _ t _ => t ≤ n) base tvs) : readView ws aq rl va base tvs ≤ n := by
  unfold readView
  have h1 := ldPre_le (aq := aq) (rl := rl) h hva
  have h2 : bytesMax (fun a t => fwdView ws aq a t) base tvs ≤ n :=
    bytesMax_le base tvs (bytesAll_mono (fun a t _ ht => fwdView_le h.2.2.2.2.2.2.1 ht) base tvs hts)
  omega

theorem loadRun_bnd {ws : PState} {n : Nat} {aq rl : Bool} {va : Nat} {base : Int}
    {tvs : List (Nat × BitVec 8)} (h : psBounded ws n) (hva : va ≤ n)
    (hts : bytesAll (fun _ t _ => t ≤ n) base tvs) : psBounded (loadRun ws aq rl va base tvs) n := by
  have h1 := loadBytes_bnd (aq := aq) (ldPre_le (aq := aq) (rl := rl) h hva) ws base tvs h hts
  have hrv := readView_le (aq := aq) (rl := rl) h hva hts
  obtain ⟨hc, h1, h2, h3, h4, h5, hf, hr, h6, h7, hR, hM, h8, h9, h10⟩ := h1
  refine psB_intro hc h1 h2 h3 h4 ?_ hf hr ?_ h7 hR hM h8 h9 h10
  · simp only [loadRun]; split <;> omega
  · simp only [loadRun]; omega

/-- MachFix-R-b5: `loadRunV` keeps the bounds when the absorbed view is in range. -/
theorem loadRunV_bnd {ws : PState} {n : Nat} {aq rl : Bool} {va vi : Nat} {base : Int}
    {tvs : List (Nat × BitVec 8)} (h : psBounded ws n) (hva : va ≤ n) (hvi : vi ≤ n)
    (hts : bytesAll (fun _ t _ => t ≤ n) base tvs) : psBounded (loadRunV ws aq rl va vi base tvs) n := by
  have hp := ldPre_le (aq := aq) (rl := rl) h hva
  have h1 := loadBytes_bnd (aq := aq) (vpre := max (ldPre ws aq rl va) vi) (by omega) ws base tvs h hts
  have hrv := readView_le (aq := aq) (rl := rl) h hva hts
  obtain ⟨hc, h1, h2, h3, h4, h5, hf, hr, h6, h7, hR, hM, h8, h9, h10⟩ := h1
  refine psB_intro hc h1 h2 h3 h4 ?_ hf hr ?_ h7 hR hM h8 h9 h10
  · simp only [loadRunV, readViewV]; split <;> omega
  · simp only [loadRunV]; omega

theorem readViewV_le {ws : PState} {n : Nat} {aq rl : Bool} {va vi : Nat} {base : Int}
    {tvs : List (Nat × BitVec 8)} (h : psBounded ws n) (hva : va ≤ n) (hvi : vi ≤ n)
    (hts : bytesAll (fun _ t _ => t ≤ n) base tvs) : readViewV ws aq rl va vi base tvs ≤ n := by
  have := readView_le (aq := aq) (rl := rl) h hva hts
  simp only [readViewV]; omega

theorem cohRaise_bnd {n ts : Nat} (hts : ts ≤ n) :
    ∀ (ws : PState) (a : Int) (len : Nat), psBounded ws n → psBounded (cohRaise ws a len ts) n
  | _, _, 0, h => h
  | ws, a, k + 1, h => by
    simp only [cohRaise]
    apply cohRaise_bnd hts
    obtain ⟨hc, h1, h2, h3, h4, h5, hf, hr, h6, h7, hR, hM, h8, h9, h10⟩ := h
    refine psB_intro (fun b => ?_) h1 h2 h3 h4 h5 hf hr h6 h7 hR hM h8 h9 h10
    simp only [coh, getD_insert_nat]
    split
    · have := hc a; simp only [coh] at this; omega
    · exact hc b

theorem storeBytes_bnd {n ts fv : Nat} (hts : ts ≤ n) (hfv : fv ≤ n) :
    ∀ (ws : PState) (a : Int) (len : Nat), psBounded ws n → psBounded (storeBytes ws a len ts fv) n
  | _, _, 0, h => h
  | ws, a, k + 1, h => by
    simp only [storeBytes]
    apply storeBytes_bnd hts hfv
    obtain ⟨hc, h1, h2, h3, h4, h5, hf, hr, h6, h7, hR, hM, h8, h9, h10⟩ := h
    refine psB_intro (fun b => ?_) h1 h2 h3 h4 h5 (fun b tf vf hb => ?_) hr h6 h7 hR hM h8 h9 h10
    · simp only [coh, getD_insert_nat]
      split
      · have := hc a; simp only [coh] at this; omega
      · exact hc b
    · by_cases hab : a = b
      · subst hab
        simp only [lookupInsert, Option.some.injEq, Prod.mk.injEq] at hb
        omega
      · simp only [lookupInsertNe hab] at hb
        exact hf b tf vf hb

theorem storeRun_bnd {ws : PState} {n : Nat} {rl : Bool} {va fv : Nat} {base : Int} {len ts : Nat}
    (h : psBounded ws n) (hva : va ≤ n) (hfv : fv ≤ n) (hts : ts ≤ n) :
    psBounded (storeRun ws rl va fv base len ts) n := by
  have h1 := storeBytes_bnd hts hfv ws base len h
  obtain ⟨hc, h1, h2, h3, h4, h5, hf, hr, h6, h7, hR, hM, h8, h9, h10⟩ := h1
  refine psB_intro hc h1 ?_ h3 h4 ?_ hf hr ?_ h7 hR hM h8 h9 h10
  · simp only [storeRun]; omega
  · simp only [storeRun]; split <;> omega
  · simp only [storeRun]; omega

theorem amoPost_bnd {ws : PState} {n : Nat} {aq : Bool} {ts : Nat} (h : psBounded ws n) (hts : ts ≤ n) :
    psBounded (amoPost ws aq ts) n := by
  obtain ⟨hc, h1, h2, h3, h4, h5, hf, hr, h6, h7, hR, hM, h8, h9, h10⟩ := h
  refine psB_intro hc ?_ h2 ?_ ?_ h5 hf hr h6 ?_ hR hM h8 h9 h10
  · simp only [amoPost]; omega
  · simp only [amoPost]; split <;> omega
  · simp only [amoPost]; split <;> omega
  · simp only [amoPost]; omega

theorem acqPost_bnd {ws : PState} {n : Nat} {aq : Bool} {ts : Nat} (h : psBounded ws n) (hts : ts ≤ n) :
    psBounded (acqPost ws aq ts) n := by
  obtain ⟨hc, h1, h2, h3, h4, h5, hf, hr, h6, h7, hR, hM, h8, h9, h10⟩ := h
  refine psB_intro hc h1 h2 ?_ ?_ h5 hf hr h6 h7 hR hM h8 h9 h10
  · simp only [acqPost]; split <;> omega
  · simp only [acqPost]; split <;> omega

theorem cmoPost_bnd {ws : PState} {n : Nat} {va : Nat} {base : Int} {len ts : Nat} (h : psBounded ws n)
    (hva : va ≤ n) (hts : ts ≤ n) : psBounded (cmoPost ws va base len ts) n := by
  have h1 := cohRaise_bnd hts ws base len h
  obtain ⟨hc, h1, h2, h3, h4, h5, hf, hr, h6, h7, hR, hM, h8, h9, h10⟩ := h1
  refine psB_intro hc h1 ?_ h3 h4 h5 hf hr ?_ h7 hR hM h8 h9 h10
  · simp only [cmoPost]; omega
  · simp only [cmoPost]; omega

theorem fencePost_bnd {ws : PState} {n : Nat} {pr pw sr sw : Bool} (h : psBounded ws n) :
    psBounded (fencePost ws pr pw sr sw) n := by
  obtain ⟨hc, h1, h2, h3, h4, h5, hf, hr, h6, h7, hR, hM, h8, h9, h10⟩ := h
  refine psB_intro hc h1 h2 ?_ ?_ h5 hf hr h6 h7 hR hM h8 h9 h10
  · simp only [fencePost]; (repeat' split) <;> omega
  · simp only [fencePost]; (repeat' split) <;> omega

theorem fenceIPost_bnd {ws : PState} {n : Nat} (h : psBounded ws n) : psBounded (fenceIPost ws) n := by
  obtain ⟨hc, h1, h2, h3, h4, h5, hf, hr, h6, h7, hR, hM, h8, h9, h10⟩ := h
  refine psB_intro hc h1 h2 h3 h4 h5 hf hr h6 h7 hR hM ?_ h9 h10
  simp only [fenceIPost]; omega

/-! ## 3. Every arm keeps the bounds -/

theorem promWf_diff {log : List PMsg} {i : Nat} {prom : GSet Nat} (ts : Nat) (h : promWf log i prom) :
    promWf log i (prom \ {ts}) := fun t ht => h t (elemOfDifference.1 ht).1

/-- EVERY ARM KEEPS THE BOUNDS ([R7.s1]): `psBounded` and `promWf` against the (unchanged) log. -/
theorem memStep_bnd {img : Image} {log : List PMsg} {i : Nat} {prom : GSet Nat} {ws : PState} {l : PLabel}
    {ots : Option Nat} {ws' : PState} {prom' : GSet Nat} (h : memStep img log i prom ws l ots ws' prom')
    (hb : psBounded ws log.length) (hw : promWf log i prom) :
    psBounded ws' log.length ∧ promWf log i prom' := by
  have hsv : ∀ s, srcsView ws s ≤ log.length := srcsView_le hb.2.2.2.2.2.2.2.1 hb.2.2.2.2.2.2.2.2.2.1
  cases h with
  | silent => exact ⟨hb, hw⟩
  | load aq rl base tvs asrc hok vi hvi =>
    exact ⟨loadRunV_bnd hb (hsv _) (invalCite_le hvi) (loadOk_ts hok), hw⟩
  | store aq rl base data asrc vsrc ts hts hm hcoh hpre =>
    have hts' := (hw ts hts).2.1
    refine ⟨acqPost_bnd (storeRun_bnd hb (hsv _) ?_ hts') hts', promWf_diff ts hw⟩
    have := hsv asrc; have := hsv vsrc; omega
  | rmw aq rl base tvs data asrc vsrc ts hlen hts hm hok hx hcoh hpre vi hvi _ =>
    have hts' := (hw ts hts).2.1
    exact ⟨amoPost_bnd (storeRun_bnd (loadRunV_bnd hb (hsv _) (invalCite_le hvi) (loadOk_ts hok)) (hsv _) hts'
      hts') hts',
      promWf_diff ts hw⟩
  | amoLd aq base tvs asrc hok vi hvi =>
    refine ⟨?_, hw⟩
    have h1 := loadRunV_bnd (aq := aq) (rl := false) hb (hsv asrc) (invalCite_le hvi) (loadOk_ts hok)
    obtain ⟨hc, h1, h2, h3, h4, h5, hf, hr, h6, h7, hR, _, h8, h9, h10⟩ := h1
    refine psB_intro hc h1 h2 h3 h4 h5 hf hr h6 h7 hR (fun R hR' => ?_) h8 h9 h10
    simp only [Option.some.injEq] at hR'
    subst hR'
    exact tsList_bnd base tvs (loadOk_ts hok)
  | amoSt rl base data asrc vsrc ts R hR hb' hlen hts hm hx hcoh hpre =>
    have hts' := (hw ts hts).2.1
    refine ⟨?_, promWf_diff ts hw⟩
    have h1 := amoPost_bnd (aq := R.rmAq) (storeRun_bnd (rl := rl) (base := base) (len := data.length) hb (hsv asrc)
      hts' hts') hts'
    obtain ⟨hc, h1, h2, h3, h4, h5, hf, hr, h6, h7, hR, _, h8, h9, h10⟩ := h1
    exact psB_intro hc h1 h2 h3 h4 h5 hf hr h6 h7 hR (fun R hR' => by cases hR') h8 h9 h10
  | fence => exact ⟨fencePost_bnd hb, hw⟩
  | fenceI => exact ⟨fenceIPost_bnd hb, hw⟩
  | dev => exact ⟨hb, hw⟩
  | regW rd srcs =>
    refine ⟨?_, hw⟩
    obtain ⟨hc, h1, h2, h3, h4, h5, hf, hr, h6, h7, hR, hM, h8, h9, h10⟩ := hb
    refine psB_intro hc h1 h2 h3 h4 h5 hf (fun r => ?_) h6 h7 hR hM h8 h9 h10
    simp only [regv, getD_insert_nat]
    split
    · exact hsv srcs
    · exact hr r
  | ctrl srcs =>
    refine ⟨?_, hw⟩
    have := hsv srcs
    obtain ⟨hc, h1, h2, h3, h4, h5, hf, hr, h6, h7, hR, hM, h8, h9, h10⟩ := hb
    refine psB_intro hc h1 h2 h3 h4 h5 hf hr ?_ h7 hR hM h8 h9 h10
    simp only; omega
  | instr =>
    refine ⟨?_, hw⟩
    obtain ⟨hc, h1, h2, h3, h4, h5, hf, hr, h6, h7, hR, hM, h8, h9, h10⟩ := hb
    exact psB_intro hc h1 h2 h3 h4 h5 hf hr h6 (Nat.zero_le _) hR (fun R hR' => by cases hR') h8 h9
      (Nat.zero_le _)
  | lr aq rl base tvs asrc hok vi hvi =>
    refine ⟨?_, hw⟩
    have hrv := readViewV_le (aq := aq) (rl := rl) hb (hsv asrc) (invalCite_le hvi) (loadOk_ts hok)
    have h1 := loadRunV_bnd (aq := aq) (rl := rl) hb (hsv asrc) (invalCite_le hvi) (loadOk_ts hok)
    obtain ⟨hc, h1, h2, h3, h4, h5, hf, hr, h6, h7, _, hM, h8, h9, h10⟩ := h1
    refine psB_intro hc h1 h2 h3 h4 h5 hf hr h6 h7 (fun R hR' => ?_) hM h8 h9 h10
    simp only [Option.some.injEq] at hR'
    subst hR'
    exact ⟨tsList_bnd base tvs (loadOk_ts hok), hrv⟩
  | sc aq rl base data asrc vsrc ts R hR hts hm hx hlt hcoh hpre =>
    have hts' := (hw ts hts).2.1
    refine ⟨?_, promWf_diff ts hw⟩
    have h1 := acqPost_bnd (aq := aq) (storeRun_bnd (rl := rl) (base := base) (len := data.length) hb (hsv asrc)
      hts' hts') hts'
    obtain ⟨hc, h1, h2, h3, h4, h5, hf, hr, h6, h7, _, hM, h8, h9, h10⟩ := h1
    refine psB_intro hc h1 h2 h3 h4 h5 hf hr h6 ?_ (fun R hR' => by cases hR') hM h8 h9 h10
    simp only [acqPost] at h7 ⊢
    omega
  | scFail =>
    refine ⟨?_, hw⟩
    obtain ⟨hc, h1, h2, h3, h4, h5, hf, hr, h6, h7, hR, hM, h8, h9, h10⟩ := hb
    exact psB_intro hc h1 h2 h3 h4 h5 hf hr h6 h7 (fun R hR' => by cases hR') hM h8 h9 h10
  | fetch base tvs hok =>
    refine ⟨?_, hw⟩
    have hts : bytesAll (fun _ t _ => t ≤ log.length) base tvs :=
      bytesAll_mono (fun _ _ _ hp => memByte_le hp.1) base tvs hok
    have e1 : bytesMax (fun _ t => t) base tvs ≤ log.length := bytesMax_le base tvs hts
    have e2 : fetchView log i prom base tvs ≤ log.length := by
      unfold fetchView
      refine bytesMax_le base tvs (bytesAll_mono (fun _ t _ ht => ?_) base tvs hts)
      split <;> omega
    obtain ⟨hc, h1, h2, h3, h4, h5, hf, hr, h6, h7, hR, hM, h8, h9, h10⟩ := hb
    refine psB_intro hc h1 h2 h3 h4 h5 hf hr h6 h7 hR hM h8 ?_ ?_
    · simp only; omega
    · simp only; omega
  | cmo k base len asrc ts hts hm hcoh hpre =>
    have hts' := (hw ts hts).2.1
    exact ⟨cmoPost_bnd hb (hsv _) hts', promWf_diff ts hw⟩

/-! ## 4. The run invariant -/

/-- A message a `promise` step may append. -/
def msgOk (n : Nat) (m : PMsg) : Prop :=
  (m.data ≠ [] ∨ ∃ k len, m.cls = .cmo k len ∧ 0 < len) ∧ ∃ i, m.tid = some i ∧ i < n

/-- THE RUN INVARIANT: `cfgWf`, and every log message is a non-trivial message of an existing agent. -/
def runWf {P D : Type} (cfg : PCfg P D) : Prop :=
  cfgWf cfg ∧ ∀ m ∈ cfg.pcLog, msgOk cfg.pcAgs.length m

theorem promWf_append {log : List PMsg} {i : Nat} {prom : GSet Nat} (m : PMsg) (h : promWf log i prom) :
    promWf (log ++ [m]) i prom := by
  intro t ht
  obtain ⟨h1, h2, m', hm, htid⟩ := h t ht
  refine ⟨h1, by simp only [List.length_append, List.length_singleton]; omega, m', ?_, htid⟩
  rw [List.getElem?_append_left (by omega)]
  exact hm

theorem getElem?_set_of {α : Type} {l : List α} {i j : Nat} {a b : α} (h : (l.set i a)[j]? = some b) :
    (i = j ∧ b = a ∧ j < l.length) ∨ (i ≠ j ∧ l[j]? = some b) := by
  rw [List.getElem?_set] at h
  split at h
  · split at h
    · left; cases h; rename_i h1 h2; exact ⟨h1, rfl, h1 ▸ h2⟩
    · cases h
  · right; rename_i h1; exact ⟨h1, h⟩

theorem pmStep_wf {P D : Type} {pstep : P → D → PLabel → P → D → Prop} {cfg cfg' : PCfg P D} {e : PEvt}
    (h : pmStep pstep cfg e cfg') (hw : runWf cfg) : runWf cfg' := by
  obtain ⟨hcfg, hlog⟩ := hw
  cases h with
  | promise i ag m hag hnt htid =>
    have hi : i < cfg.pcAgs.length := (List.getElem?_eq_some_iff.1 hag).1
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
        exact memStep_bnd hm h1 h2
      · exact hcfg j ag' hj'
    · simp only [List.length_set]
      exact hlog m' hm'

theorem pmInit_wf {P D : Type} (img : Image) (d0 : D) (ps : List P) : runWf (pmInit img d0 ps) := by
  refine ⟨fun i ag h => ?_, fun m hm => by cases hm⟩
  simp only [pmInit, List.getElem?_map, Option.map_eq_some_iff] at h
  obtain ⟨p, _, hp⟩ := h
  subst hp
  exact ⟨psInit_bnd _, fun t ht => absurd ht notElemOfEmpty⟩

theorem pmSteps_wf {P D : Type} {pstep : P → D → PLabel → P → D → Prop} {c c' : PCfg P D} {evs : List PEvt}
    (h : pmSteps pstep c evs c') (hw : runWf c) : runWf c' := by
  induction h with
  | refl => exact hw
  | step _ _ _ _ _ h1 _ ih => exact ih (pmStep_wf h1 hw)

/-- The agent count never changes. -/
theorem pmStep_len {P D : Type} {pstep : P → D → PLabel → P → D → Prop} {cfg cfg' : PCfg P D} {e : PEvt}
    (h : pmStep pstep cfg e cfg') : cfg'.pcAgs.length = cfg.pcAgs.length := by
  cases h <;> simp

theorem pmSteps_len {P D : Type} {pstep : P → D → PLabel → P → D → Prop} {c c' : PCfg P D} {evs : List PEvt}
    (h : pmSteps pstep c evs c') : c'.pcAgs.length = c.pcAgs.length := by
  induction h with
  | refl => rfl
  | step _ _ _ _ _ h1 _ ih => rw [ih, pmStep_len h1]

/-- The log only grows (append-only memory). -/
theorem pmSteps_prefix {P D : Type} {pstep : P → D → PLabel → P → D → Prop} {c c' : PCfg P D}
    {evs : List PEvt} (h : pmSteps pstep c evs c') : c.pcLog <+: c'.pcLog := by
  induction h with
  | refl => exact List.prefix_refl _
  | step c0 c1 _ _ _ h1 _ ih =>
    refine List.IsPrefix.trans ?_ ih
    cases h1 with
    | promise => exact List.prefix_append _ _
    | state => exact List.prefix_refl _

end Weak.Prom
