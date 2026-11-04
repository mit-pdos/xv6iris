/-
Weak/Prom: **the forward-bank knowledge invariant of the core** (stage S2; plan rev 7 §2 "Forwarded reads" [R1.5]).

Machine facts (no logic) that the state interpretation of `CoreWp.lean` keeps, so that a load that FORWARDS a byte
from the hart's own store `t_f` gets the knowledge recorded at that store's fulfil, at the store's own index
`⟦pv_f⟧ proto(M[t_f])` (plan §2), not at the smaller forward view.

* `fulPv ws l` — the pre-view of the fulfil of a write label (the `pv` of EXT, `fulfilVpreD` of the plan) at state
  `ws`; `fulPv_lt`: a state step's fulfil timestamp is above it.  The core's FULFIL obligation is `⟦fulPv⟧ proto`.
* `fwdKnow π img M ws τ` (FK) — for every forward-bank entry `(t_f, v_f)` of byte `a`: some `pv < t_f` with
  `⟦pv⟧ proto(M[t_f])` and either `pv ≤ v_f ⊔ plainFloor ws` (the bound `fwdMono` needs; it holds for every plain
  store and every exclusive write, whose forward view is its own timestamp, M1) or the entry comes from a release /
  acquire store of the trace (whose pre-view also contains `vrOld ⊔ vwOld` / `vRel`, rules 6/7).
* `fetchInv ws` (FI) — `wIfv ≤ wIfr` (a fetch view is bounded by the fetched sources).
* `fwd_step` — every state step keeps FI and FK, given the fulfil's `⟦fulPv⟧` knowledge.
* `stFloor`, `floors_mono` (moved here from CoreRules.lean) — the capture and store floors only grow.
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Prom.CoreRun

namespace Weak.Prom.PF

open MachCSL MachCSL.Stdpp Iris.Std
open Weak (Image Dsrc)
open Weak.Prom
open PLabel

/-! ## 1. The floors (moved from CoreRules.lean) -/

/-- The floors a later fulfil's pre-view contains: capture view and store floor. -/
def stFloor (ws : PState) : Nat := max ws.wVcap ws.wVwNew

theorem loadBytes_floor (aq : Bool) (vpre : Nat) : ∀ (ws : PState) (a : Int) (tvs : List (Nat × BitVec 8)),
    ws.wVcap = (loadBytes aq vpre ws a tvs).wVcap ∧ ws.wVwNew ≤ (loadBytes aq vpre ws a tvs).wVwNew
  | _, _, [] => ⟨rfl, Nat.le_refl _⟩
  | ws, a, (t, _) :: r => by
    simp only [loadBytes]
    have := loadBytes_floor aq vpre (loadByte ws aq vpre a t) (a + 1) r
    refine ⟨this.1, Nat.le_trans ?_ this.2⟩
    simp only [loadByte]; split <;> omega

theorem storeBytes_floor : ∀ (ws : PState) (a : Int) (n ts fv : Nat),
    (storeBytes ws a n ts fv).wVcap = ws.wVcap ∧ (storeBytes ws a n ts fv).wVwNew = ws.wVwNew
  | _, _, 0, _, _ => ⟨rfl, rfl⟩
  | ws, a, n + 1, ts, fv => by simp only [storeBytes]; exact storeBytes_floor _ _ n ts fv

theorem cohRaise_floor : ∀ (ws : PState) (a : Int) (n ts : Nat),
    (cohRaise ws a n ts).wVcap = ws.wVcap ∧ (cohRaise ws a n ts).wVwNew = ws.wVwNew
  | _, _, 0, _ => ⟨rfl, rfl⟩
  | ws, a, n + 1, ts => by simp only [cohRaise]; exact cohRaise_floor _ _ n ts

theorem loadRun_floor (ws : PState) (aq rl : Bool) (va : Nat) (base : Int) (tvs : List (Nat × BitVec 8)) :
    stFloor ws ≤ stFloor (loadRun ws aq rl va base tvs) := by
  have := loadBytes_floor aq (ldPre ws aq rl va) ws base tvs
  unfold stFloor loadRun; simp only; omega

/-- MachFix-R-b5. -/
theorem loadRunV_floor (ws : PState) (aq rl : Bool) (va vi : Nat) (base : Int) (tvs : List (Nat × BitVec 8)) :
    stFloor ws ≤ stFloor (loadRunV ws aq rl va vi base tvs) := by
  have := loadBytes_floor aq (max (ldPre ws aq rl va) vi) ws base tvs
  unfold stFloor loadRunV; simp only; omega

theorem storeRun_floor (ws : PState) (rl : Bool) (va fv : Nat) (base : Int) (n ts : Nat) :
    stFloor ws ≤ stFloor (storeRun ws rl va fv base n ts) := by
  have := storeBytes_floor ws base n ts fv
  unfold stFloor storeRun; simp only; omega

theorem acqPost_floor (ws : PState) (aq : Bool) (ts : Nat) : stFloor ws ≤ stFloor (acqPost ws aq ts) := by
  unfold stFloor acqPost; simp only; split <;> omega

theorem amoPost_floor (ws : PState) (aq : Bool) (ts : Nat) : stFloor ws ≤ stFloor (amoPost ws aq ts) := by
  unfold stFloor amoPost; simp only; split <;> omega

/-- The floors are monotone along every state step (vcap only grows: `ctrl`, loads and stores take maxima;
`vwNew` only grows: fences and acquires take maxima; nothing resets them). -/
theorem floors_mono {img : Image} {log : List PMsg} {i : Nat} {prom : GSet Nat} {ws : PState} {l : PLabel}
    {ots : Option Nat} {ws' : PState} {prom' : GSet Nat} (h : memStep img log i prom ws l ots ws' prom') :
    stFloor ws ≤ stFloor ws' := by
  cases h with
  | silent => exact Nat.le_refl _
  | load => exact loadRunV_floor _ _ _ _ _ _ _   -- MachFix-R-b5
  | store => exact Nat.le_trans (storeRun_floor _ _ _ _ _ _ _) (acqPost_floor _ _ _)
  | rmw =>
    exact Nat.le_trans (loadRunV_floor _ _ _ _ _ _ _) (Nat.le_trans (storeRun_floor _ _ _ _ _ _ _)
      (amoPost_floor _ _ _))
  | amoLd => exact loadRunV_floor _ _ _ _ _ _ _
  | amoSt => exact Nat.le_trans (storeRun_floor _ _ _ _ _ _ _) (amoPost_floor _ _ _)
  | fence => unfold stFloor fencePost; simp only; split <;> omega
  | fenceI => exact Nat.le_refl _
  | dev => exact Nat.le_refl _
  | regW => exact Nat.le_refl _
  | ctrl => unfold stFloor; simp only; omega
  | instr => exact Nat.le_refl _
  | lr => exact loadRunV_floor _ _ _ _ _ _ _
  | sc => exact Nat.le_trans (storeRun_floor _ _ _ _ _ _ _) (acqPost_floor _ _ _)
  | scFail => exact Nat.le_refl _
  | fetch => exact Nat.le_refl _
  | cmo _ base len _ ts =>
    have := cohRaise_floor ws base len ts
    unfold stFloor cmoPost; simp only; omega


/-! ## 2. Field facts -/

theorem loadBytes_keep (aq : Bool) (vpre : Nat) : ∀ (ws : PState) (a : Int) (tvs : List (Nat × BitVec 8)),
    (loadBytes aq vpre ws a tvs).wFwd = ws.wFwd ∧ (loadBytes aq vpre ws a tvs).wIfr = ws.wIfr ∧
      (loadBytes aq vpre ws a tvs).wIfv = ws.wIfv
  | _, _, [] => ⟨rfl, rfl, rfl⟩
  | ws, a, (t, _) :: r => by simp only [loadBytes]; exact loadBytes_keep aq vpre _ _ r

theorem storeBytes_keep : ∀ (ws : PState) (a : Int) (n ts fv : Nat),
    (storeBytes ws a n ts fv).wIfr = ws.wIfr ∧ (storeBytes ws a n ts fv).wIfv = ws.wIfv
  | _, _, 0, _, _ => ⟨rfl, rfl⟩
  | ws, a, n + 1, ts, fv => by simp only [storeBytes]; exact storeBytes_keep _ _ n ts fv

theorem cohRaise_keep : ∀ (ws : PState) (a : Int) (n ts : Nat),
    (cohRaise ws a n ts).wFwd = ws.wFwd ∧ (cohRaise ws a n ts).wIfr = ws.wIfr ∧ (cohRaise ws a n ts).wIfv = ws.wIfv
  | _, _, 0, _ => ⟨rfl, rfl, rfl⟩
  | ws, a, n + 1, ts => by simp only [cohRaise]; exact cohRaise_keep _ _ n ts

theorem storeBytes_fwd' : ∀ (ws : PState) (a : Int) (n ts fv : Nat) (b : Int),
    get? (storeBytes ws a n ts fv).wFwd b = if a ≤ b ∧ b < a + n then some (ts, fv) else get? ws.wFwd b
  | ws, a, 0, ts, fv, b => by simp only [storeBytes]; rw [if_neg (by omega)]
  | ws, a, n + 1, ts, fv, b => by
    simp only [storeBytes]
    rw [storeBytes_fwd' _ (a + 1) n ts fv b]
    by_cases h1 : a + 1 ≤ b ∧ b < a + 1 + n
    · rw [if_pos h1, if_pos (by omega)]
    · rw [if_neg h1]
      by_cases h2 : a = b
      · subst h2; rw [lookupInsert, if_pos (by omega)]
      · rw [lookupInsertNe h2, if_neg (by omega)]

theorem fetchView_le (log : List PMsg) (i : Nat) (prom : GSet Nat) :
    ∀ (base : Int) (tvs : List (Nat × BitVec 8)), fetchView log i prom base tvs ≤ bytesMax (fun _ t => t) base tvs
  | _, [] => Nat.le_refl _
  | a, (t, _) :: r => by
    have ih := fetchView_le log i prom (a + 1) r
    unfold fetchView at ih ⊢
    simp only [bytesMax]
    split <;> omega

/-! ## 3. The invariants -/

/-- The capture, store and fetch floors: what a later plain fulfil's pre-view contains (with the fetch floor
`wIfr ≥ wIfv`). -/
def plainFloor (ws : PState) : Nat := max (stFloor ws) ws.wIfr

/-- A release or acquire store label (Zalasr `s*.rl`/`s*.aqrl`): its pre-view has `vrOld ⊔ vwOld` / `vRel`. -/
def isRelAcq : PLabel → Bool
  | LStore aq rl _ _ _ _ => aq || rl
  | _ => false

/-- THE PRE-VIEW OF A FULFIL (EXT's `pv`, plan §2 `fulfilVpreD`), per write label. -/
def fulPv (ws : PState) : PLabel → Nat
  | LStore aq rl _ _ asrc vsrc => stPreA ws aq rl (srcsView ws asrc) (srcsView ws vsrc)
  | LRmw aq rl base tvs _ asrc vsrc =>
      stPre (loadRun ws aq false (srcsView ws asrc) base tvs) rl (srcsView ws asrc) (srcsView ws vsrc)
  | LAmoSt rl _ _ asrc vsrc => stPre ws rl (srcsView ws asrc) (srcsView ws vsrc)
  | LExStore aq rl _ _ asrc vsrc =>
      max (stPreA ws aq rl (srcsView ws asrc) (srcsView ws vsrc)) (match ws.wRes with | some R => R.rvView | none => 0)
  | LCmo _ _ _ asrc => stPre ws false (srcsView ws asrc) 0
  | _ => 0

/-- (FI) the fetch view is below the fetch sources. -/
def fetchInv (ws : PState) : Prop := ws.wIfv ≤ ws.wIfr

/-- (FK) THE FORWARD-BANK KNOWLEDGE (plan §2 "Forwarded reads"). -/
def fwdKnow (π : Proto) (img : Image) (M : List PMsg) (ws : PState) (τ : Trace) : Prop :=
  ∀ a tf vf, get? ws.wFwd a = some (tf, vf) → ∃ pv, pv < tf ∧
    (∀ m, msgAt M tf = some m → grd π img M pv (π.okMsg m)) ∧
    (pv ≤ max vf (plainFloor ws) ∨ ∃ e ∈ τ, e.2 = some tf ∧ isRelAcq e.1 = true)

/-- A state step's fulfil timestamp is above its pre-view (EXT). -/
theorem fulPv_lt {img : Image} {log : List PMsg} {i : Nat} {prom : GSet Nat} {ws : PState} {l : PLabel}
    {t : Nat} {ws' : PState} {prom' : GSet Nat} (h : memStep img log i prom ws l (some t) ws' prom') :
    fulPv ws l < t := by
  cases h with
  | store _ _ _ _ _ _ _ _ _ _ hext => exact hext
  | rmw _ _ _ _ _ _ _ _ _ _ _ _ _ _ hext => exact hext
  | amoSt _ _ _ _ _ _ _ _ _ _ _ _ _ _ hext => exact hext
  | sc _ _ _ _ _ _ _ R hR _ _ _ _ _ hext => simp only [fulPv, hR]; exact hext
  | cmo _ _ _ _ _ _ _ _ hext => exact hext

theorem fwdKnow_keep {π : Proto} {img : Image} {M : List PMsg} {ws ws' : PState} {τ : Trace} {e : PEv}
    (hf : ws'.wFwd = ws.wFwd) (hfl : plainFloor ws ≤ plainFloor ws') (h : fwdKnow π img M ws τ) :
    fwdKnow π img M ws' (τ ++ [e]) := by
  intro a tf vf hg
  rw [hf] at hg
  obtain ⟨pv, h1, h2, h3⟩ := h a tf vf hg
  refine ⟨pv, h1, h2, ?_⟩
  rcases h3 with h3 | ⟨e', he', h4, h5⟩
  · exact .inl (by omega)
  · exact .inr ⟨e', List.mem_append_left _ he', h4, h5⟩

theorem fwdKnow_store {π : Proto} {img : Image} {M : List PMsg} {ws ws1 ws' : PState} {τ : Trace} {e : PEv}
    {base : Int} {n ts fv : Nat} (hf : ws'.wFwd = (storeBytes ws1 base n ts fv).wFwd) (hw1 : ws1.wFwd = ws.wFwd)
    (hfl : plainFloor ws ≤ plainFloor ws') (h : fwdKnow π img M ws τ)
    (hnew : ∃ pv, pv < ts ∧ (∀ m, msgAt M ts = some m → grd π img M pv (π.okMsg m)) ∧
      (pv ≤ max fv (plainFloor ws') ∨ (e.2 = some ts ∧ isRelAcq e.1 = true))) :
    fwdKnow π img M ws' (τ ++ [e]) := by
  intro a tf vf hg
  rw [hf, storeBytes_fwd', hw1] at hg
  split at hg
  · cases hg
    obtain ⟨pv, h1, h2, h3⟩ := hnew
    refine ⟨pv, h1, h2, ?_⟩
    rcases h3 with h3 | ⟨h4, h5⟩
    · exact .inl h3
    · exact .inr ⟨e, List.mem_append_right _ (List.mem_singleton_self _), h4, h5⟩
  · obtain ⟨pv, h1, h2, h3⟩ := h a tf vf hg
    refine ⟨pv, h1, h2, ?_⟩
    rcases h3 with h3 | ⟨e', he', h4, h5⟩
    · exact .inl (by omega)
    · exact .inr ⟨e', List.mem_append_left _ he', h4, h5⟩

theorem plainFloor_of {ws ws' : PState} (h1 : stFloor ws ≤ stFloor ws') (h2 : ws.wIfr ≤ ws'.wIfr) :
    plainFloor ws ≤ plainFloor ws' := by unfold plainFloor; omega

/-- **Every state step keeps (FI) and (FK)**, given the fulfil's knowledge at its own pre-view. -/
theorem fwd_step {π : Proto} {img : Image} {M : List PMsg} {i : Nat} {prom : GSet Nat} {ws : PState}
    {l : PLabel} {ots : Option Nat} {ws' : PState} {prom' : GSet Nat} {τ : Trace}
    (h : memStep img M i prom ws l ots ws' prom') (hfi : fetchInv ws) (hfk : fwdKnow π img M ws τ)
    (hk : ∀ t, ots = some t → ∀ m, msgAt M t = some m → grd π img M (fulPv ws l) (π.okMsg m)) :
    fetchInv ws' ∧ fwdKnow π img M ws' (τ ++ [(l, ots)]) := by
  have hfm := floors_mono h
  unfold fetchInv at hfi ⊢
  cases h with
  | silent => exact ⟨hfi, fwdKnow_keep (ws := ws) rfl (Nat.le_refl _) hfk⟩
  | load aq rl base tvs asrc _ vi _ =>   -- MachFix-R-b5: `loadRunV`
    have hl := loadBytes_keep aq (max (ldPre ws aq rl (srcsView ws asrc)) vi) ws base tvs
    refine ⟨?_, fwdKnow_keep (ws := ws) ?_ (plainFloor_of hfm ?_) hfk⟩
    · simp only [loadRunV, hl]; omega
    · simp only [loadRunV, hl]
    · simp only [loadRunV, hl]; omega
  | store aq rl base data asrc vsrc ts _ _ _ hext =>
    have hk' := hk ts rfl
    have hsb := storeBytes_keep ws base data.length ts (max (srcsView ws asrc) (srcsView ws vsrc))
    refine ⟨?_, fwdKnow_store (ws1 := ws) (base := base) (n := data.length) (ts := ts)
      (fv := max (srcsView ws asrc) (srcsView ws vsrc)) rfl rfl (plainFloor_of hfm ?_) hfk ⟨_, hext, hk', ?_⟩⟩
    · simp only [acqPost, storeRun, hsb]; omega
    · simp only [acqPost, storeRun, hsb]; omega
    · cases hrq : (aq || rl) with
      | true => exact .inr ⟨rfl, by simp [isRelAcq, hrq]⟩
      | false =>
        refine .inl ?_
        simp only [Bool.or_eq_false_iff] at hrq
        obtain ⟨rfl, rfl⟩ := hrq
        have hsb2 := storeBytes_floor ws base data.length ts (max (srcsView ws asrc) (srcsView ws vsrc))
        simp only [fulPv, stPreA, stPre, plainFloor, stFloor, acqPost, storeRun, hsb, Bool.false_eq_true,
          if_false] at hext ⊢
        omega
  | rmw aq rl base tvs data asrc vsrc ts _ _ _ _ _ _ hext vi _ _ =>   -- MachFix-R-b5: `loadRunV`
    have hk' := hk ts rfl
    have hl := loadBytes_keep aq (max (ldPre ws aq false (srcsView ws asrc)) vi) ws base tvs
    have hsb := storeBytes_keep (loadRunV ws aq false (srcsView ws asrc) vi base tvs) base data.length ts ts
    have hlw : (loadRunV ws aq false (srcsView ws asrc) vi base tvs).wIfr = ws.wIfr ∧
        (loadRunV ws aq false (srcsView ws asrc) vi base tvs).wIfv = ws.wIfv := by simp only [loadRunV, hl]; simp
    refine ⟨?_, fwdKnow_store (ws1 := loadRunV ws aq false (srcsView ws asrc) vi base tvs) (base := base)
      (n := data.length) (ts := ts) (fv := ts) rfl (by simp only [loadRunV, hl])
      (plainFloor_of hfm ?_) hfk ⟨_, hext, hk', .inl (by omega)⟩⟩
    · simp only [amoPost, storeRun, hsb]; omega
    · simp only [amoPost, storeRun, hsb]; omega
  | amoLd aq base tvs asrc _ vi _ =>
    have hl := loadBytes_keep aq (max (ldPre ws aq false (srcsView ws asrc)) vi) ws base tvs
    refine ⟨?_, fwdKnow_keep (ws := ws) ?_ (plainFloor_of hfm ?_) hfk⟩
    · simp only [loadRunV, hl]; omega
    · simp only [loadRunV, hl]
    · simp only [loadRunV, hl]; omega
  | amoSt rl base data asrc vsrc ts R _ _ _ _ _ _ _ hext =>
    have hk' := hk ts rfl
    have hsb := storeBytes_keep ws base data.length ts ts
    refine ⟨?_, fwdKnow_store (ws1 := ws) (base := base) (n := data.length) (ts := ts) (fv := ts) rfl rfl
      (plainFloor_of hfm ?_) hfk ⟨_, hext, hk', .inl (by omega)⟩⟩
    · simp only [amoPost, storeRun, hsb]; omega
    · simp only [amoPost, storeRun, hsb]; omega
  | fence => exact ⟨hfi, fwdKnow_keep (ws := ws) rfl (plainFloor_of hfm (Nat.le_refl _)) hfk⟩
  | fenceI => exact ⟨hfi, fwdKnow_keep (ws := ws) rfl (plainFloor_of hfm (Nat.le_refl _)) hfk⟩
  | dev => exact ⟨hfi, fwdKnow_keep (ws := ws) rfl (Nat.le_refl _) hfk⟩
  | regW => exact ⟨hfi, fwdKnow_keep (ws := ws) rfl (plainFloor_of hfm (Nat.le_refl _)) hfk⟩
  | ctrl => exact ⟨hfi, fwdKnow_keep (ws := ws) rfl (plainFloor_of hfm (Nat.le_refl _)) hfk⟩
  | instr => exact ⟨Nat.zero_le _, fwdKnow_keep (ws := ws) rfl (plainFloor_of hfm (Nat.le_refl _)) hfk⟩
  | lr aq rl base tvs asrc _ vi _ =>
    have hl := loadBytes_keep aq (max (ldPre ws aq rl (srcsView ws asrc)) vi) ws base tvs
    refine ⟨?_, fwdKnow_keep (ws := ws) ?_ (plainFloor_of hfm ?_) hfk⟩
    · simp only [loadRunV, hl]; omega
    · simp only [loadRunV, hl]
    · simp only [loadRunV, hl]; omega
  | sc aq rl base data asrc vsrc ts R hR _ _ _ _ _ hext =>
    have hk' := hk ts rfl
    have hsb := storeBytes_keep ws base data.length ts ts
    have hext' : fulPv ws (LExStore aq rl base data asrc vsrc) < ts := by simp only [fulPv, hR]; exact hext
    refine ⟨?_, fwdKnow_store (ws1 := ws) (base := base) (n := data.length) (ts := ts) (fv := ts) rfl rfl
      (plainFloor_of hfm ?_) hfk ⟨_, hext', hk', .inl (by omega)⟩⟩
    · simp only [acqPost, storeRun, hsb]; omega
    · simp only [acqPost, storeRun, hsb]; omega
  | scFail => exact ⟨hfi, fwdKnow_keep (ws := ws) rfl (plainFloor_of hfm (Nat.le_refl _)) hfk⟩
  | fetch base tvs _ =>
    have := fetchView_le M i prom base tvs
    refine ⟨?_, fwdKnow_keep (ws := ws) rfl (plainFloor_of hfm ?_) hfk⟩
    · simp only; omega
    · simp only; omega
  | cmo k base len asrc ts _ _ _ _ =>
    have hc := cohRaise_keep ws base len ts
    refine ⟨?_, fwdKnow_keep (ws := ws) ?_ (plainFloor_of hfm ?_) hfk⟩
    · simp only [cmoPost, hc]; omega
    · simp only [cmoPost, hc]
    · simp only [cmoPost, hc]; omega

end Weak.Prom.PF
