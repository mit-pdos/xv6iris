/-
Weak/Prom: **`amoSplitFused`, the split AMO is one memory operation** (S1M-proof, plan rev 7 §1 M10 (4), §8 S1M;
NA-5 "Sail's split AMO events = one memory op").  Brief: `~/dev/weak-orch/promising/AmoSplit_prompt.txt`.

The Sail model emits an AMO as TWO events (`execute_AMO`, InstsEnd.lean: `mem_read … aq (aq && rl) true`, then
`mem_write_value … (aq && rl) rl true`); emission v2 (Emit.lean) labels them `LAmoLd aq` / `LAmoSt rl` (M10 (1),
(2)), and machine v2 runs them through the AMO slot `wRmw` (`memStep.amoLd` / `memStep.amoSt`).  The litmus front
end and completeness (`Cmp*.lean`) use ONE fused step `LRmw` (`memStep.rmw`, M0: §rvwmo "An aligned AMO gives rise
to a single memory operation that is both a load operation and a store operation simultaneously").

## 1. The step level (plan M10 (4) literally: "the split pair's combined transition equals `WPRmw` v2's")

`amoSplitFused_mem` : with register-only address/data sources and an empty slot,
  `memStep ws (LRmw aq rl base tvs data asrc vsrc) (some ts) ws' prom'`
    ↔ `∃ ws1, memStep ws (LAmoLd aq base tvs asrc) none ws1 prom ∧ memStep ws1 (LAmoSt rl base data asrc vsrc) (some ts) ws' prom'`.
The atomicity of the pair is the fused step's `exclOk` (the slot carries the read's bytes and timestamps to the
write half), its COH and EXT are the fused step's (`cohBelow`/`stPre` on the absorbing post-read state are
equivalent to the fused step's on the `vi = 0` state plus `vi < ts`, `vRaise`); the slot fixes the write's base and
width; aq comes from the read half (`rmAq`, M10 (2)).

## 2. The run level (`splitToFused`, `fusedToSplit`)

For ANY program half `pstepS` that emits split AMOs and any fused program half `pstepF`:
* `fusedToSplit` (premise `FuseOk`: each fused step is a split step with a non-half label, or an `LRmw` that the
  split program performs as `LAmoLd`, silent steps, `LAmoSt` with the same sources): every valid run of the fused
  machine is a valid run of the split machine with THE SAME FINAL CONFIGURATION, each hart's trace related by
  `TrRel` (each `LRmw` entry ↦ `LAmoLd`, `LSilent`s, `LAmoSt`; everything else kept).
* `splitToFused` (premise `SplitOk`: an invariant `Inv` of the split program; non-half steps are fused steps; the
  silent and read-half steps do not touch the device fabric; TIGHTNESS — after an `LAmoLd` the hart takes only
  `LSilent` steps until an `LAmoSt` with the read's address sources ("no other event of the hart between the
  halves"); a read half, silent steps and a write half form a fused `LRmw` step): every valid run of the split
  machine has a valid fused run with the same image, final memory and fabric, the traces related by `TrRel`, and
  the same final agents except a hart that ends the run BETWEEN its halves (`pendS`: its slot is full), whose
  fused agent is the one before the read (`TrRelP`: the split trace has the dangling read and silent steps).
  If no hart ends between its halves (`closedS`), the final configurations are EQUAL (`splitToFused_closed`).
  Proof: the promises-first factorization (`validRun_factorL`), then a simulation in which a hart's fused copy
  waits at its read half until the write half and then takes the fused step, at the then-current fabric (the read
  half and silent steps are fabric-free); the log is fixed in the state phase, so the read stays admissible.
* `fuseStep pstepS`: the canonical fused program of a split one (Sail: `fuseStep pstepV2`, AmoSplitV2.lean).

## Findings on the slot `wRmw` (M10 (1), (3)) — what the proof needs and gets
* The fused `LRmw` leaves `wRmw` alone and the split write half empties it: the post-states agree exactly when the
  slot is empty at the read half.  It is: `wRmw` starts empty (`psInit`), only `amoLd` fills it, only `amoSt` and
  `LInstr` empty it, every other arm keeps it (`memStep_rmw_none`), so in a tight run it is empty outside an AMO.
* `amoSt` checks the slot's base and width against the write (so a write half at another address is stuck), and
  carries aq (`rmAq`); it does NOT compare the write's address sources with the read's: the fused label has ONE
  `asrc`, so tightness asks for the same sources (Sail: both are `depsAddr` of the same decoded instruction).
* Sources must be register-only (`regOnly`, no `DLdRes`): the write half evaluates its sources after the read has
  raised `wLdv`, the fused step before.  Every AMO source of emission v2 is `dsrcOfNum`, a `DReg` list.
* A read half with NO write half (a failed `amocas` without write-back, or a trap between the halves) leaves a
  dangling read that `LInstr` clears: such a run has no fused counterpart (the instruction is a load, not an AMO);
  `SplitOk.tight` excludes it.
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Prom.MachFactor

namespace Weak.Prom.AS

open MachCSL MachCSL.Stdpp Iris.Std
open Weak (Image Dsrc)
open Weak.Prom
open PLabel

/-! ## 1. Field bookkeeping -/

/-- Register-only sources (no `DLdRes`): their view is the register views' (M19 syntactic sources). -/
def regOnly (s : List Dsrc) : Prop := ∀ x ∈ s, x ≠ Dsrc.DLdRes

theorem loadBytes_regv_rmw (aq : Bool) (vpre : Nat) : ∀ (ws : PState) (a : Int) (tvs : List (Nat × BitVec 8)),
    (loadBytes aq vpre ws a tvs).wRegv = ws.wRegv ∧ (loadBytes aq vpre ws a tvs).wRmw = ws.wRmw
  | _, _, [] => ⟨rfl, rfl⟩
  | ws, a, (t, _) :: r => by
    simp only [loadBytes]
    exact loadBytes_regv_rmw aq vpre (loadByte ws aq vpre a t) (a + 1) r

theorem loadRunV_regv (ws : PState) (aq rl : Bool) (va vi : Nat) (base : Int) (tvs : List (Nat × BitVec 8)) :
    (loadRunV ws aq rl va vi base tvs).wRegv = ws.wRegv :=
  (loadBytes_regv_rmw aq _ ws base tvs).1

theorem loadRunV_rmw (ws : PState) (aq rl : Bool) (va vi : Nat) (base : Int) (tvs : List (Nat × BitVec 8)) :
    (loadRunV ws aq rl va vi base tvs).wRmw = ws.wRmw :=
  (loadBytes_regv_rmw aq _ ws base tvs).2

theorem storeBytes_rmw : ∀ (n : Nat) (ws : PState) (a : Int) (ts fv : Nat), (storeBytes ws a n ts fv).wRmw = ws.wRmw
  | 0, _, _, _, _ => rfl
  | n + 1, ws, a, ts, fv => by
    simp only [storeBytes]
    exact storeBytes_rmw n _ (a + 1) ts fv

theorem storeBytes_setRmw (r : Option PRmw) : ∀ (n : Nat) (ws : PState) (a : Int) (ts fv : Nat),
    storeBytes { ws with wRmw := r } a n ts fv = { storeBytes ws a n ts fv with wRmw := r }
  | 0, _, _, _, _ => rfl
  | n + 1, ws, a, ts, fv => by
    simp only [storeBytes]
    have e := storeBytes_setRmw r n
      { ws with wCoh := insert ws.wCoh a (max (coh ws a) ts), wFwd := insert ws.wFwd a (ts, fv) } (a + 1) ts fv
    exact e

theorem cohRaise_rmw : ∀ (ws : PState) (a : Int) (n ts : Nat), (cohRaise ws a n ts).wRmw = ws.wRmw
  | _, _, 0, _ => rfl
  | ws, a, n + 1, ts => by
    simp only [cohRaise]
    exact cohRaise_rmw _ (a + 1) n ts

theorem storeRun_rmw (ws : PState) (rl : Bool) (va fv : Nat) (base : Int) (n ts : Nat) :
    (storeRun ws rl va fv base n ts).wRmw = ws.wRmw :=
  storeBytes_rmw n ws base ts fv

theorem storeRun_setRmw (r : Option PRmw) (ws : PState) (rl : Bool) (va fv : Nat) (base : Int) (n ts : Nat) :
    storeRun { ws with wRmw := r } rl va fv base n ts = { storeRun ws rl va fv base n ts with wRmw := r } := by
  unfold storeRun
  rw [storeBytes_setRmw]

theorem amoPost_rmw (ws : PState) (aq : Bool) (ts : Nat) : (amoPost ws aq ts).wRmw = ws.wRmw := rfl

theorem acqPost_rmw (ws : PState) (aq : Bool) (ts : Nat) : (acqPost ws aq ts).wRmw = ws.wRmw := rfl

theorem setRmw_self (Y : PState) {r : Option PRmw} (h : Y.wRmw = r) : { Y with wRmw := r } = Y := by
  subst h; rfl

theorem srcsView_regv {ws ws' : PState} (hr : ws'.wRegv = ws.wRegv) :
    ∀ {s : List Dsrc}, regOnly s → srcsView ws' s = srcsView ws s
  | [], _ => rfl
  | x :: s, h => by
    have ih := srcsView_regv hr (s := s) (fun y hy => h y (List.mem_cons_of_mem _ hy))
    have hx := h x (by simp)
    simp only [srcsView, List.foldr_cons] at ih ⊢
    rw [ih]
    cases x with
    | DReg r => simp only [dsrcView, regv, hr]
    | DLdRes => exact absurd rfl hx

/-! ## 2. Coherence and pre-view facts across the absorbed invalidate view -/

theorem cohBelow_mono {A B : PState} (hab : ∀ b, coh A b ≤ coh B b) :
    ∀ (a : Int) (n ts : Nat), cohBelow B a n ts → cohBelow A a n ts
  | _, 0, _, _ => trivial
  | a, n + 1, ts, h => by
    simp only [cohBelow] at h ⊢
    exact ⟨Nat.lt_of_le_of_lt (hab a) h.1, cohBelow_mono hab (a + 1) n ts h.2⟩

theorem cohBelow_raise {A B : PState} {vi ts : Nat} (hab : ∀ b, coh B b ≤ max (coh A b) vi) (hvi : vi < ts) :
    ∀ (a : Int) (n : Nat), cohBelow A a n ts → cohBelow B a n ts
  | _, 0, _ => trivial
  | a, n + 1, h => by
    simp only [cohBelow] at h ⊢
    have := hab a
    exact ⟨by omega, cohBelow_raise hab hvi (a + 1) n h.2⟩

theorem max_le_max2 {a b a' b' : Nat} (h1 : a ≤ a') (h2 : b ≤ b') : max a b ≤ max a' b' := by omega

theorem max_le_vi2 {a b a' b' v : Nat} (h1 : a' ≤ max a v) (h2 : b' ≤ max b v) : max a' b' ≤ max (max a b) v := by
  omega

theorem stPre_raise {vi : Nat} {A B : PState} (h : vRaise vi A B) (rl : Bool) (va vd : Nat) :
    stPre A rl va vd ≤ stPre B rl va vd ∧ stPre B rl va vd ≤ max (stPre A rl va vd) vi := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩ := h
  have hX : (if rl then max A.wVrOld A.wVwOld else 0) ≤ (if rl then max B.wVrOld B.wVwOld else 0) ∧
      (if rl then max B.wVrOld B.wVwOld else 0) ≤ max (if rl then max A.wVrOld A.wVwOld else 0) vi := by
    rw [h8]
    cases rl
    · exact ⟨Nat.le_refl _, Nat.zero_le _⟩
    · exact ⟨max_le_max2 h1.1 (Nat.le_refl _), max_le_vi2 h1.2 (Nat.le_max_left _ _)⟩
  unfold stPre
  rw [h10, h15]
  have hr : ∀ x : Nat, x ≤ max x vi := fun x => Nat.le_max_left _ _
  refine ⟨max_le_max2 (Nat.le_refl _) (max_le_max2 (Nat.le_refl _) (max_le_max2 (Nat.le_refl _)
    (max_le_max2 (Nat.le_refl _) (max_le_max2 h3.1 hX.1)))), ?_⟩
  exact max_le_vi2 (hr _) (max_le_vi2 (hr _) (max_le_vi2 (hr _) (max_le_vi2 (hr _) (max_le_vi2 h3.2 hX.2))))

theorem loadByte_coh (ws : PState) (aq : Bool) (vpre : Nat) (a : Int) (t : Nat) (b : Int) :
    coh (loadByte ws aq vpre a t) b =
      if a = b then max (coh ws a) (max (max vpre (fwdView ws aq a t)) t) else coh ws b := by
  simp only [loadByte, coh]
  exact getD_insert_natI

theorem loadBytes_coh_mono (aq : Bool) (vpre : Nat) :
    ∀ (ws : PState) (a : Int) (tvs : List (Nat × BitVec 8)) (b : Int), coh ws b ≤ coh (loadBytes aq vpre ws a tvs) b
  | _, _, [], _ => Nat.le_refl _
  | ws, a, (t, _) :: r, b => by
    simp only [loadBytes]
    have h1 := loadBytes_coh_mono aq vpre (loadByte ws aq vpre a t) (a + 1) r b
    have h2 : coh ws b ≤ coh (loadByte ws aq vpre a t) b := by
      rw [loadByte_coh]
      split
      · rename_i h; subst h; omega
      · exact Nat.le_refl _
    omega

theorem loadBytes_coh_base (aq : Bool) (vpre : Nat) (ws : PState) (a : Int) (t : Nat) (v : BitVec 8)
    (r : List (Nat × BitVec 8)) : vpre ≤ coh (loadBytes aq vpre ws a ((t, v) :: r)) a := by
  simp only [loadBytes]
  have h1 := loadBytes_coh_mono aq vpre (loadByte ws aq vpre a t) (a + 1) r a
  have h2 : vpre ≤ coh (loadByte ws aq vpre a t) a := by rw [loadByte_coh, if_pos rfl]; omega
  omega

/-- A memory step with an equal post-state. -/
theorem memStep_cast {img : Image} {log : List PMsg} {i : Nat} {prom : GSet Nat} {ws : PState} {l : PLabel}
    {ots : Option Nat} {ws' ws'' : PState} {prom' : GSet Nat} (h : memStep img log i prom ws l ots ws' prom')
    (e : ws' = ws'') : memStep img log i prom ws l ots ws'' prom' := e ▸ h

/-- The split write half's post-state is the fused post-state (empty slot at the read). -/
theorem amo_post_eq (ws : PState) (hn : ws.wRmw = none) (aq rl : Bool) (va vi : Nat) (base : Int)
    (tvs : List (Nat × BitVec 8)) (n ts : Nat) :
    { amoPost (storeRun { loadRunV ws aq false va vi base tvs with wRmw := some ⟨base, tvs.map Prod.fst, aq⟩ }
        rl va ts base n ts) aq ts with wRmw := none } =
      amoPost (storeRun (loadRunV ws aq false va vi base tvs) rl va ts base n ts) aq ts := by
  rw [storeRun_setRmw]
  have h : (amoPost (storeRun (loadRunV ws aq false va vi base tvs) rl va ts base n ts) aq ts).wRmw = none := by
    show (storeRun (loadRunV ws aq false va vi base tvs) rl va ts base n ts).wRmw = none
    rw [storeRun_rmw, loadRunV_rmw, hn]
  exact setRmw_self _ h

/-! ## 3. `amoSplitFused` at the step level (plan M10 (4)) -/

/-- FUSED ⇒ SPLIT: a fused AMO step is a read half followed by a write half, with the same post-state. -/
theorem rmw_split {img : Image} {log : List PMsg} {i : Nat} {prom : GSet Nat} {ws : PState} {aq rl : Bool}
    {base : Int} {tvs : List (Nat × BitVec 8)} {data : List (BitVec 8)} {asrc vsrc : List Dsrc} {ts : Nat}
    {ws' : PState} {prom' : GSet Nat} (hra : regOnly asrc) (hrv : regOnly vsrc) (hn : ws.wRmw = none)
    (h : memStep img log i prom ws (LRmw aq rl base tvs data asrc vsrc) (some ts) ws' prom') :
    ∃ ws1, memStep img log i prom ws (LAmoLd aq base tvs asrc) none ws1 prom ∧
      memStep img log i prom ws1 (LAmoSt rl base data asrc vsrc) (some ts) ws' prom' := by
  cases h with
  | rmw _ _ _ _ _ _ _ _ hlen hts hm hl hx hc hpv vi hcite hvi =>
    refine ⟨_, memStep.amoLd prom ws aq base tvs asrc hl vi hcite, ?_⟩
    have hR := loadRunV_vRaise ws aq false (srcsView ws asrc) vi base tvs
    have hreg : ({ loadRunV ws aq false (srcsView ws asrc) vi base tvs with
        wRmw := some ⟨base, tvs.map Prod.fst, aq⟩ } : PState).wRegv = ws.wRegv := loadRunV_regv ..
    have hva := srcsView_regv hreg hra
    have hvd := srcsView_regv hreg hrv
    have hc' : cohBelow ({ loadRunV ws aq false (srcsView ws asrc) vi base tvs with
        wRmw := some ⟨base, tvs.map Prod.fst, aq⟩ } : PState) base data.length ts :=
      cohBelow_raise (B := ({ loadRunV ws aq false (srcsView ws asrc) vi base tvs with
        wRmw := some ⟨base, tvs.map Prod.fst, aq⟩ } : PState)) (fun b => (hR.coh b).2) hvi base data.length hc
    have hpv' : stPre ({ loadRunV ws aq false (srcsView ws asrc) vi base tvs with
        wRmw := some ⟨base, tvs.map Prod.fst, aq⟩ } : PState) rl
        (srcsView ({ loadRunV ws aq false (srcsView ws asrc) vi base tvs with
          wRmw := some ⟨base, tvs.map Prod.fst, aq⟩ } : PState) asrc)
        (srcsView ({ loadRunV ws aq false (srcsView ws asrc) vi base tvs with
          wRmw := some ⟨base, tvs.map Prod.fst, aq⟩ } : PState) vsrc) < ts := by
      rw [hva, hvd]
      have := (stPre_raise hR rl (srcsView ws asrc) (srcsView ws vsrc)).2
      exact Nat.lt_of_le_of_lt this (by omega)
    have hst := memStep.amoSt (img := img) (log := log) (i := i) prom
      { loadRunV ws aq false (srcsView ws asrc) vi base tvs with wRmw := some ⟨base, tvs.map Prod.fst, aq⟩ }
      rl base data asrc vsrc ts ⟨base, tvs.map Prod.fst, aq⟩ rfl rfl (by simp [hlen]) hts hm hx hc' hpv'
    refine memStep_cast hst ?_
    rw [hva]
    exact amo_post_eq ws hn aq rl (srcsView ws asrc) vi base tvs data.length ts

/-- SPLIT ⇒ FUSED: a read half followed by a write half is one fused AMO step (the slot fixes the base). -/
theorem split_rmw {img : Image} {log : List PMsg} {i : Nat} {prom prom1 : GSet Nat} {ws ws1 : PState}
    {aq rl : Bool} {base base' : Int} {tvs : List (Nat × BitVec 8)} {data : List (BitVec 8)}
    {asrc vsrc : List Dsrc} {ts : Nat} {ws' : PState} {prom' : GSet Nat}
    (hra : regOnly asrc) (hrv : regOnly vsrc) (hn : ws.wRmw = none)
    (h1 : memStep img log i prom ws (LAmoLd aq base tvs asrc) none ws1 prom1)
    (h2 : memStep img log i prom1 ws1 (LAmoSt rl base' data asrc vsrc) (some ts) ws' prom') :
    base' = base ∧ prom1 = prom ∧
      memStep img log i prom ws (LRmw aq rl base tvs data asrc vsrc) (some ts) ws' prom' := by
  cases h1 with
  | amoLd _ _ _ _ hl vi hcite =>
    cases h2 with
    | amoSt _ _ _ _ _ _ R hR hbase hlen hts hm hx hc hpv =>
      injection hR with hR
      subst hR
      simp only at hbase hlen hx
      subst hbase
      refine ⟨rfl, rfl, ?_⟩
      have hR := loadRunV_vRaise ws aq false (srcsView ws asrc) vi base tvs
      have hreg : ({ loadRunV ws aq false (srcsView ws asrc) vi base tvs with
          wRmw := some ⟨base, tvs.map Prod.fst, aq⟩ } : PState).wRegv = ws.wRegv := loadRunV_regv ..
      have hva := srcsView_regv hreg hra
      have hvd := srcsView_regv hreg hrv
      rw [hva, hvd] at hpv
      have hlen' : tvs.length = data.length := by simpa using hlen
      have hvi : vi < ts := by
        cases tvs with
        | nil =>
          rcases hcite.2 with h0 | h0
          · omega
          · exact h0.elim
        | cons tv r =>
          obtain ⟨t, v⟩ := tv
          have hdl : data.length = r.length + 1 := by simp at hlen'; omega
          rw [hdl] at hc
          simp only [cohBelow] at hc
          have hco := loadBytes_coh_base aq (max (ldPre ws aq false (srcsView ws asrc)) vi) ws base t v r
          have hlt : coh (loadBytes aq (max (ldPre ws aq false (srcsView ws asrc)) vi) ws base ((t, v) :: r)) base
              < ts := hc.1
          omega
      have hc0 : cohBelow (loadRun ws aq false (srcsView ws asrc) base tvs) base data.length ts := by
        refine cohBelow_mono ?_ base data.length ts hc
        intro b
        exact (hR.coh b).1
      have hpv0 : stPre (loadRun ws aq false (srcsView ws asrc) base tvs) rl (srcsView ws asrc)
          (srcsView ws vsrc) < ts :=
        Nat.lt_of_le_of_lt (stPre_raise hR rl (srcsView ws asrc) (srcsView ws vsrc)).1 hpv
      have hf := memStep.rmw (img := img) (log := log) (i := i) prom ws aq rl base tvs data asrc vsrc ts hlen' hts hm
        hl hx hc0 hpv0 vi hcite hvi
      refine memStep_cast hf ?_
      rw [hva]
      exact (amo_post_eq ws hn aq rl (srcsView ws asrc) vi base tvs data.length ts).symm

/-- **`amoSplitFused_mem` (plan M10 (4))**: with register-only sources and an empty AMO slot, the fused AMO step
`LRmw` and the Sail pair `LAmoLd ; LAmoSt` have exactly the same transitions. -/
theorem amoSplitFused_mem {img : Image} {log : List PMsg} {i : Nat} {prom : GSet Nat} {ws : PState}
    {aq rl : Bool} {base : Int} {tvs : List (Nat × BitVec 8)} {data : List (BitVec 8)} {asrc vsrc : List Dsrc}
    {ts : Nat} {ws' : PState} {prom' : GSet Nat} (hra : regOnly asrc) (hrv : regOnly vsrc) (hn : ws.wRmw = none) :
    memStep img log i prom ws (LRmw aq rl base tvs data asrc vsrc) (some ts) ws' prom' ↔
      ∃ ws1, memStep img log i prom ws (LAmoLd aq base tvs asrc) none ws1 prom ∧
        memStep img log i prom ws1 (LAmoSt rl base data asrc vsrc) (some ts) ws' prom' :=
  ⟨rmw_split hra hrv hn, fun ⟨_, h1, h2⟩ => (split_rmw hra hrv hn h1 h2).2.2⟩

/-! ## 4. Step inversions and the slot invariant -/

/-- Is the label a split-AMO half? -/
def isHalf : PLabel → Bool
  | LAmoLd .. => true
  | LAmoSt .. => true
  | _ => false

/-- Every arm but the two halves keeps an empty slot empty (`LInstr` empties it). -/
theorem memStep_rmw_none {img : Image} {log : List PMsg} {i : Nat} {prom : GSet Nat} {ws : PState} {l : PLabel}
    {ots : Option Nat} {ws' : PState} {prom' : GSet Nat} (h : memStep img log i prom ws l ots ws' prom')
    (hl : isHalf l = false) (hn : ws.wRmw = none) : ws'.wRmw = none := by
  cases h with
  | silent => exact hn
  | load => exact (loadRunV_rmw ..).trans hn
  | store => simp only [acqPost_rmw, storeRun_rmw]; exact hn
  | rmw => simp only [amoPost_rmw, storeRun_rmw, loadRunV_rmw]; exact hn
  | amoLd => cases hl
  | amoSt => cases hl
  | fence => exact hn
  | fenceI => exact hn
  | dev => exact hn
  | regW => exact hn
  | ctrl => exact hn
  | instr => rfl
  | lr => exact (loadRunV_rmw ..).trans hn
  | sc => simp only [acqPost_rmw, storeRun_rmw]; exact hn
  | scFail => exact hn
  | fetch => exact hn
  | cmo => simp only [cmoPost, cohRaise_rmw]; exact hn

theorem memStep_amoLd_inv {img : Image} {log : List PMsg} {i : Nat} {prom : GSet Nat} {ws : PState} {aq : Bool}
    {base : Int} {tvs : List (Nat × BitVec 8)} {asrc : List Dsrc} {ots : Option Nat} {ws' : PState}
    {prom' : GSet Nat} (h : memStep img log i prom ws (LAmoLd aq base tvs asrc) ots ws' prom') :
    ots = none ∧ prom' = prom ∧ ws'.wRmw ≠ none := by
  cases h with
  | amoLd => exact ⟨rfl, rfl, by simp⟩

theorem memStep_amoSt_inv {img : Image} {log : List PMsg} {i : Nat} {prom : GSet Nat} {ws : PState} {rl : Bool}
    {base : Int} {data : List (BitVec 8)} {asrc vsrc : List Dsrc} {ots : Option Nat} {ws' : PState}
    {prom' : GSet Nat} (h : memStep img log i prom ws (LAmoSt rl base data asrc vsrc) ots ws' prom') :
    ws.wRmw ≠ none ∧ ∃ ts, ots = some ts := by
  cases h with
  | amoSt _ _ _ _ _ ts R hR => exact ⟨by rw [hR]; simp, ts, rfl⟩

theorem memStep_rmw_inv {img : Image} {log : List PMsg} {i : Nat} {prom : GSet Nat} {ws : PState} {aq rl : Bool}
    {base : Int} {tvs : List (Nat × BitVec 8)} {data : List (BitVec 8)} {asrc vsrc : List Dsrc}
    {ots : Option Nat} {ws' : PState} {prom' : GSet Nat}
    (h : memStep img log i prom ws (LRmw aq rl base tvs data asrc vsrc) ots ws' prom') : ∃ ts, ots = some ts := by
  cases h with
  | rmw _ _ _ _ _ _ _ ts => exact ⟨ts, rfl⟩

theorem memStep_silent_inv {img : Image} {log : List PMsg} {i : Nat} {prom : GSet Nat} {ws : PState}
    {ots : Option Nat} {ws' : PState} {prom' : GSet Nat} (h : memStep img log i prom ws LSilent ots ws' prom') :
    ots = none ∧ ws' = ws ∧ prom' = prom := by
  cases h with
  | silent => exact ⟨rfl, rfl, rfl⟩

/-! ## 5. Program-side vocabulary -/

section prog

variable {P D : Type}

/-- A FABRIC-FREE SILENT CHAIN of the program: every step is an `LSilent` step at every fabric value, which it
leaves alone. -/
inductive silentRun (pstep : P → D → PLabel → P → D → Prop) : P → P → Prop
  | refl (h : P) : silentRun pstep h h
  | step (h h1 h2 : P) : (∀ d, pstep h d LSilent h1 d) → silentRun pstep h1 h2 → silentRun pstep h h2

/-- A silent chain with the fabric threaded through. -/
inductive silentRunD (pstep : P → D → PLabel → P → D → Prop) : P → D → P → D → Prop
  | refl (h : P) (d : D) : silentRunD pstep h d h d
  | step (h : P) (d : D) (h1 : P) (d1 : D) (h2 : P) (d2 : D) :
      pstep h d LSilent h1 d1 → silentRunD pstep h1 d1 h2 d2 → silentRunD pstep h d h2 d2

theorem silentRun_snoc {pstep : P → D → PLabel → P → D → Prop} {h1 h2 h3 : P} (h : silentRun pstep h1 h2)
    (hs : ∀ d, pstep h2 d LSilent h3 d) : silentRun pstep h1 h3 := by
  induction h with
  | refl => exact .step _ _ _ hs (.refl _)
  | step _ _ _ h0 _ ih => exact .step _ _ _ h0 (ih hs)

theorem silentRunD_of {pstep : P → D → PLabel → P → D → Prop} {h1 h2 : P} (h : silentRun pstep h1 h2) (d : D) :
    silentRunD pstep h1 d h2 d := by
  induction h with
  | refl => exact .refl _ _
  | step _ _ _ h0 _ ih => exact .step _ _ _ _ _ _ (h0 d) ih

/-- THE FUSED PROGRAM of a split one: every non-half step, and every read half, silent chain and write half with
the same base and sources as ONE `LRmw` step. -/
inductive fuseStep (pstep : P → D → PLabel → P → D → Prop) : P → D → PLabel → P → D → Prop
  | plain (h : P) (d : D) (l : PLabel) (h' : P) (d' : D) :
      pstep h d l h' d' → isHalf l = false → fuseStep pstep h d l h' d'
  | amo (h : P) (d : D) (aq rl : Bool) (base : Int) (tvs : List (Nat × BitVec 8)) (data : List (BitVec 8))
      (asrc vsrc : List Dsrc) (h1 : P) (d1 : D) (hk : P) (dk : D) (h' : P) (d' : D) :
      regOnly asrc → regOnly vsrc →
      pstep h d (LAmoLd aq base tvs asrc) h1 d1 → silentRunD pstep h1 d1 hk dk →
      pstep hk dk (LAmoSt rl base data asrc vsrc) h' d' →
      fuseStep pstep h d (LRmw aq rl base tvs data asrc vsrc) h' d'

/-- THE SPLIT ⇒ FUSED PREMISES on a split program `pstepS`, a fused program `pstepF` and an invariant `Inv` of the
split program's states. -/
structure SplitOk (pstepS pstepF : P → D → PLabel → P → D → Prop) (Inv : P → Prop) : Prop where
  inv : ∀ h d l h' d', Inv h → pstepS h d l h' d' → Inv h'
  plain : ∀ h d l h' d', Inv h → pstepS h d l h' d' → isHalf l = false → pstepF h d l h' d'
  /-- the silent and read-half steps are fabric-free -/
  fab : ∀ h d l h' d', Inv h → pstepS h d l h' d' → (l = LSilent ∨ ∃ aq base tvs asrc, l = LAmoLd aq base tvs asrc) →
    d' = d ∧ ∀ d2, pstepS h d2 l h' d2
  /-- TIGHTNESS: after a read half, only silent steps until a write half with the read's address sources -/
  tight : ∀ h d aq base tvs asrc h1 d1, Inv h → pstepS h d (LAmoLd aq base tvs asrc) h1 d1 →
    regOnly asrc ∧ ∀ hk, silentRun pstepS h1 hk → ∀ d l h' d', pstepS hk d l h' d' →
      l = LSilent ∨ ∃ rl b data vsrc, l = LAmoSt rl b data asrc vsrc ∧ regOnly vsrc
  fuse : ∀ h aq base tvs asrc h1 hk d rl data vsrc h' d', Inv h →
    (∀ d0, pstepS h d0 (LAmoLd aq base tvs asrc) h1 d0) → silentRun pstepS h1 hk →
    pstepS hk d (LAmoSt rl base data asrc vsrc) h' d' → regOnly asrc → regOnly vsrc →
    pstepF h d (LRmw aq rl base tvs data asrc vsrc) h' d'

/-- THE FUSED ⇒ SPLIT PREMISES. -/
structure FuseOk (pstepF pstepS : P → D → PLabel → P → D → Prop) (Inv : P → Prop) : Prop where
  inv : ∀ h d l h' d', Inv h → pstepF h d l h' d' → Inv h'
  step : ∀ h d l h' d', Inv h → pstepF h d l h' d' →
    (isHalf l = false ∧ pstepS h d l h' d') ∨
    (∃ aq rl base tvs data asrc vsrc h1 d1 hk dk, l = LRmw aq rl base tvs data asrc vsrc ∧ regOnly asrc ∧
      regOnly vsrc ∧ pstepS h d (LAmoLd aq base tvs asrc) h1 d1 ∧ silentRunD pstepS h1 d1 hk dk ∧
      pstepS hk dk (LAmoSt rl base data asrc vsrc) h' d')

/-- `fuseStep` satisfies `SplitOk` for every tight, fabric-free-on-halves split program. -/
theorem splitOk_fuse {pstepS : P → D → PLabel → P → D → Prop} {Inv : P → Prop}
    (hinv : ∀ h d l h' d', Inv h → pstepS h d l h' d' → Inv h')
    (hfab : ∀ h d l h' d', Inv h → pstepS h d l h' d' → (l = LSilent ∨ ∃ aq base tvs asrc, l = LAmoLd aq base tvs asrc) →
      d' = d ∧ ∀ d2, pstepS h d2 l h' d2)
    (htight : ∀ h d aq base tvs asrc h1 d1, Inv h → pstepS h d (LAmoLd aq base tvs asrc) h1 d1 →
      regOnly asrc ∧ ∀ hk, silentRun pstepS h1 hk → ∀ d l h' d', pstepS hk d l h' d' →
        l = LSilent ∨ ∃ rl b data vsrc, l = LAmoSt rl b data asrc vsrc ∧ regOnly vsrc) :
    SplitOk pstepS (fuseStep pstepS) Inv :=
  ⟨hinv, fun h d l h' d' _ hs hl => .plain _ _ _ _ _ hs hl, hfab, htight,
    fun h aq base tvs asrc h1 hk d rl data vsrc h' d' _ hld hsr hst hra hrv =>
      .amo _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hra hrv (hld d) (silentRunD_of hsr d) hst⟩

/-- `fuseStep` satisfies `FuseOk` (no premise). -/
theorem fuseOk_fuse (pstepS : P → D → PLabel → P → D → Prop) : FuseOk (fuseStep pstepS) pstepS (fun _ => True) := by
  refine ⟨fun _ _ _ _ _ _ _ => trivial, fun h d l h' d' _ hs => ?_⟩
  cases hs with
  | plain _ _ _ hs hl => exact .inl ⟨hl, hs⟩
  | amo aq rl base tvs data asrc vsrc h1 d1 hk dk _ _ hra hrv hld hsr hst =>
    exact .inr ⟨aq, rl, base, tvs, data, asrc, vsrc, h1, d1, hk, dk, rfl, hra, hrv, hld, hsr, hst⟩

end prog

/-! ## 6. Trace relation -/

/-- A list of silent trace entries. -/
def allSil (sil : List (PLabel × Option Nat)) : Prop := ∀ x ∈ sil, x = (LSilent, none)

/-- `TrRel fused split`: the split trace is the fused one with each `LRmw` entry replaced by the read half, silent
entries and the write half (same fulfil timestamp); every other entry kept. -/
inductive TrRel : List (PLabel × Option Nat) → List (PLabel × Option Nat) → Prop
  | nil : TrRel [] []
  | keep (f s : List (PLabel × Option Nat)) (l : PLabel) (o : Option Nat) :
      isHalf l = false → TrRel f s → TrRel (f ++ [(l, o)]) (s ++ [(l, o)])
  | amo (f s : List (PLabel × Option Nat)) (aq rl : Bool) (base : Int) (tvs : List (Nat × BitVec 8))
      (data : List (BitVec 8)) (asrc vsrc : List Dsrc) (ts : Nat) (sil : List (PLabel × Option Nat)) :
      TrRel f s → allSil sil →
      TrRel (f ++ [(LRmw aq rl base tvs data asrc vsrc, some ts)])
        (s ++ ((LAmoLd aq base tvs asrc, none) :: (sil ++ [(LAmoSt rl base data asrc vsrc, some ts)])))

/-- `TrRel`, or `TrRel` followed by a dangling read half and silent entries (a hart that ends between its halves). -/
def TrRelP (f s : List (PLabel × Option Nat)) : Prop :=
  TrRel f s ∨ ∃ (s0 : List (PLabel × Option Nat)) (aq : Bool) (base : Int) (tvs : List (Nat × BitVec 8))
    (asrc : List Dsrc) (sil : List (PLabel × Option Nat)), TrRel f s0 ∧ allSil sil ∧
      s = s0 ++ (LAmoLd aq base tvs asrc, none) :: sil

theorem TrRel_append {f1 s1 : List (PLabel × Option Nat)} (h1 : TrRel f1 s1) :
    ∀ {f2 s2}, TrRel f2 s2 → TrRel (f1 ++ f2) (s1 ++ s2) := by
  intro f2 s2 h2
  induction h2 with
  | nil => simpa using h1
  | keep f s l o hl _ ih =>
    have := TrRel.keep _ _ l o hl ih
    simpa [List.append_assoc] using this
  | amo f s aq rl base tvs data asrc vsrc ts sil _ hsil ih =>
    have := TrRel.amo _ _ aq rl base tvs data asrc vsrc ts sil ih hsil
    simpa [List.append_assoc] using this

theorem TrRel_single {l : PLabel} {o : Option Nat} (hl : isHalf l = false) : TrRel [(l, o)] [(l, o)] := by
  simpa using TrRel.keep [] [] l o hl .nil

/-! ## 7. Run plumbing -/

section runs

variable {P D : Type}

/-- Runs built from the end (for the forward simulation of a split run). -/
inductive pmStepsR (pstep : P → D → PLabel → P → D → Prop) : PCfg P D → List PEvt → PCfg P D → Prop
  | refl (c : PCfg P D) : pmStepsR pstep c [] c
  | snoc (c c1 c2 : PCfg P D) (es : List PEvt) (e : PEvt) :
      pmStepsR pstep c es c1 → pmStep pstep c1 e c2 → pmStepsR pstep c (es ++ [e]) c2

theorem pmStepsR_cons {pstep : P → D → PLabel → P → D → Prop} {c0 c1 c2 : PCfg P D} {e : PEvt} {es : List PEvt}
    (hs : pmStep pstep c0 e c1) (hr : pmStepsR pstep c1 es c2) : pmStepsR pstep c0 (e :: es) c2 := by
  induction hr with
  | refl => simpa using pmStepsR.snoc _ _ _ [] e (.refl c0) hs
  | snoc c3 c4 es' e' _ h4 ih =>
    have := pmStepsR.snoc _ _ _ _ e' ih h4
    simpa using this

theorem pmStepsR_of {pstep : P → D → PLabel → P → D → Prop} {c c' : PCfg P D} {es : List PEvt}
    (h : pmSteps pstep c es c') : pmStepsR pstep c es c' := by
  induction h with
  | refl => exact .refl _
  | step _ _ _ _ _ hs _ ih => exact pmStepsR_cons hs ih

theorem pmSteps_app_inv {pstep : P → D → PLabel → P → D → Prop} :
    ∀ {c c2 : PCfg P D} {a b : List PEvt}, pmSteps pstep c (a ++ b) c2 →
      ∃ c1, pmSteps pstep c a c1 ∧ pmSteps pstep c1 b c2
  | c, _, [], _, h => ⟨c, .refl _, h⟩
  | c, c2, e :: a, b, h => by
    cases h with
    | step _ c1 _ _ _ hs hr =>
      obtain ⟨c3, h3, h4⟩ := pmSteps_app_inv hr
      exact ⟨c3, .step _ _ _ _ _ hs h3, h4⟩

theorem pmSteps_single {pstep : P → D → PLabel → P → D → Prop} {c c' : PCfg P D} {e : PEvt}
    (h : pmStep pstep c e c') : pmSteps pstep c [e] c' := .step _ _ _ _ _ h (.refl _)

/-- A promise-only run is a run of any program half. -/
theorem promsTransfer {pstep pstep' : P → D → PLabel → P → D → Prop} {c c' : PCfg P D} {es : List PEvt}
    (h : pmSteps pstep c es c') (hp : ∀ e ∈ es, e.isSt = false) : pmSteps pstep' c es c' := by
  induction h with
  | refl => exact .refl _
  | step c0 c1 c2 e es hs _ ih =>
    have ih' := ih (fun e he => hp e (List.mem_cons_of_mem _ he))
    cases hs with
    | promise i ag m h1 h2 h3 => exact .step _ _ _ _ _ (.promise _ i ag m h1 h2 h3) ih'
    | state => exact absurd (hp _ (List.mem_cons_self ..)) (by simp [PEvt.isSt])

/-- A promise-only run keeps every agent's program state and `PState`. -/
theorem promsKeep {pstep : P → D → PLabel → P → D → Prop} {c c' : PCfg P D} {es : List PEvt}
    (h : pmSteps pstep c es c') (hp : ∀ e ∈ es, e.isSt = false) :
    ∀ (k : Nat) (ag : PAgent P), c'.pcAgs[k]? = some ag → ∃ ag0, c.pcAgs[k]? = some ag0 ∧ ag.paSt = ag0.paSt ∧ ag.paWs = ag0.paWs := by
  induction h with
  | refl => intro k ag hk; exact ⟨ag, hk, rfl, rfl⟩
  | step c0 c1 c2 e es hs _ ih =>
    intro k ag hk
    obtain ⟨ag1, h1, h2, h3⟩ := ih (fun e he => hp e (List.mem_cons_of_mem _ he)) k ag hk
    cases hs with
    | promise i ag0 m hag _ _ =>
      simp only at h1
      rcases getElem?_set_of h1 with ⟨hij, hb, _⟩ | ⟨_, hj⟩
      · subst hij hb
        exact ⟨ag0, hag, h2, h3⟩
      · exact ⟨ag1, hj, h2, h3⟩
    | state => exact absurd (hp _ (List.mem_cons_self ..)) (by simp [PEvt.isSt])

theorem traceOf_snoc (k j : Nat) (es : List PEvt) (l : PLabel) (o : Option Nat) :
    traceOf k (es ++ [.st j l o]) = if j = k then traceOf k es ++ [(l, o)] else traceOf k es := by
  rw [traceOf_append]
  simp only [traceOf]
  split <;> simp

theorem traceOf_cons_st (k j : Nat) (es : List PEvt) (l : PLabel) (o : Option Nat) :
    traceOf k (.st j l o :: es) = if j = k then (l, o) :: traceOf k es else traceOf k es := rfl

theorem set_self_of {α : Type} {l : List α} {j : Nat} {a : α} (h : l[j]? = some a) : l.set j a = l := by
  apply List.ext_getElem?
  intro k
  rw [List.getElem?_set]
  split
  · rename_i hk
    subst hk
    rw [h]
    simp [(List.getElem?_eq_some_iff.1 h).1]
  · rfl

end runs

/-! ## 8. Split ⇒ fused -/

section sf

variable {P D : Type} {pstepS pstepF : P → D → PLabel → P → D → Prop} {Inv : P → Prop}

/-- A hart BETWEEN ITS HALVES: reached from an `Inv` state by a read half and a silent chain. -/
def pendS (pstepS : P → D → PLabel → P → D → Prop) (Inv : P → Prop) (hk : P) : Prop :=
  ∃ (h0 : P) (aq : Bool) (base : Int) (tvs : List (Nat × BitVec 8)) (asrc : List Dsrc) (h1 : P),
    Inv h0 ∧ (∀ d, pstepS h0 d (LAmoLd aq base tvs asrc) h1 d) ∧ silentRun pstepS h1 hk

/-- The per-agent simulation relation: SYNCED (equal agents, empty slot) or PENDING (the fused agent waits before
the read half the split agent has taken). -/
def AgRel (pstepS : P → D → PLabel → P → D → Prop) (Inv : P → Prop) (img : Image) (log : List PMsg) (j : Nat)
    (agS agF : PAgent P) (trS trF : List (PLabel × Option Nat)) : Prop :=
  (agF = agS ∧ Inv agS.paSt ∧ agS.paWs.wRmw = none ∧ TrRel trF trS) ∨
  (∃ (aq : Bool) (base : Int) (tvs : List (Nat × BitVec 8)) (asrc : List Dsrc) (h1 : P)
      (s0 sil : List (PLabel × Option Nat)),
    Inv agF.paSt ∧ agF.paWs.wRmw = none ∧ agF.paProm = agS.paProm ∧ regOnly asrc ∧
    (∀ d, pstepS agF.paSt d (LAmoLd aq base tvs asrc) h1 d) ∧ silentRun pstepS h1 agS.paSt ∧ Inv agS.paSt ∧
    memStep img log j agF.paProm agF.paWs (LAmoLd aq base tvs asrc) none agS.paWs agS.paProm ∧
    TrRel trF s0 ∧ allSil sil ∧ trS = s0 ++ (LAmoLd aq base tvs asrc, none) :: sil)

structure SRel (pstepS : P → D → PLabel → P → D → Prop) (Inv : P → Prop) (cS cF : PCfg P D)
    (esS esF : List PEvt) : Prop where
  img : cF.pcImg = cS.pcImg
  log : cF.pcLog = cS.pcLog
  dev : cF.pcDev = cS.pcDev
  len : cF.pcAgs.length = cS.pcAgs.length
  ags : ∀ (k : Nat) (agS : PAgent P), cS.pcAgs[k]? = some agS → ∃ agF, cF.pcAgs[k]? = some agF ∧
    AgRel pstepS Inv cS.pcImg cS.pcLog k agS agF (traceOf k esS) (traceOf k esF)
  out : ∀ k, cS.pcAgs.length ≤ k → traceOf k esS = [] ∧ traceOf k esF = []

theorem traceOf_out {k : Nat} : ∀ {es : List PEvt} (j : Nat) (l : PLabel) (o : Option Nat), j ≠ k →
    traceOf k (es ++ [.st j l o]) = traceOf k es := by
  intro es j l o h
  rw [traceOf_snoc, if_neg h]

/-- THE SIMULATION of a split state phase by a fused one. -/
theorem simSF (H : SplitOk pstepS pstepF Inv) {c : PCfg P D}
    (hc : ∀ (k : Nat) (ag : PAgent P), c.pcAgs[k]? = some ag → Inv ag.paSt ∧ ag.paWs.wRmw = none) :
    ∀ {es : List PEvt} {c' : PCfg P D}, pmStepsR pstepS c es c' → (∀ e ∈ es, e.isSt = true) →
      ∃ esF cF, pmSteps pstepF c esF cF ∧ SRel pstepS Inv c' cF es esF := by
  intro es c' hr
  induction hr with
  | refl =>
    intro _
    refine ⟨[], c, .refl _, ⟨rfl, rfl, rfl, rfl, fun k agS hk => ⟨agS, hk, .inl ⟨rfl, (hc k agS hk).1,
      (hc k agS hk).2, .nil⟩⟩, fun _ _ => ⟨rfl, rfl⟩⟩⟩
  | snoc c1 c2 es e _ hs ih =>
    intro hst
    obtain ⟨esF, cF1, hF, sr⟩ := ih (fun e he => hst e (List.mem_append_left _ he))
    cases hs with
    | promise => exact absurd (hst _ (List.mem_append_right _ (List.mem_singleton_self _))) (by simp [PEvt.isSt])
    | state j agS l ots st' d' ws' prom' hag hp hm =>
      have hj : j < c1.pcAgs.length := (List.getElem?_eq_some_iff.1 hag).1
      obtain ⟨agF, hagF, hrel⟩ := sr.ags j agS hag
      -- the other agents and the outside traces, when the fused side takes `esF'` with no `j`-free event
      have hout : ∀ (esF' : List PEvt), (∀ k, k ≠ j → traceOf k esF' = traceOf k esF) →
          ∀ k, (c1.pcAgs.set j ⟨st', ws', prom'⟩).length ≤ k →
            traceOf k (es ++ [.st j l ots]) = [] ∧ traceOf k esF' = [] := by
        intro esF' hF' k hk
        simp only [List.length_set] at hk
        have hkj : j ≠ k := by omega
        rw [traceOf_out j l ots hkj, hF' k (Ne.symm hkj)]
        exact sr.out k hk
      rcases hrel with ⟨rfl, hI, hn, htr⟩ | ⟨aq, base, tvs, asrc, h1, s0, sil, hI0, hn0, hpr, hra, hld, hsr, hI, hml,
          htr, hsil, hS⟩
      · -- SYNCED
        cases hhalf : isHalf l with
        | false =>
          have hpF : pstepF agF.paSt cF1.pcDev l st' d' := by rw [sr.dev]; exact H.plain _ _ _ _ _ hI hp hhalf
          have hmF : memStep cF1.pcImg cF1.pcLog j agF.paProm agF.paWs l ots ws' prom' := by
            rw [sr.img, sr.log]; exact hm
          refine ⟨esF ++ [.st j l ots], ⟨cF1.pcImg, cF1.pcLog, d', cF1.pcAgs.set j ⟨st', ws', prom'⟩⟩, pmSteps_append hF (pmSteps_single (.state _ j agF l ots st' d' ws' prom'
            hagF hpF hmF)), ⟨sr.img, sr.log, rfl, by simp [sr.len], fun k agS' hk => ?_,
            hout _ (fun k hk => traceOf_out j l ots (Ne.symm hk))⟩⟩
          simp only at hk ⊢
          rcases getElem?_set_of hk with ⟨hkj, hb, _⟩ | ⟨hkj, hk'⟩
          · subst hkj hb
            refine ⟨_, getElem?_set_eq_of hagF, .inl ⟨rfl, H.inv _ _ _ _ _ hI hp, memStep_rmw_none hm hhalf hn, ?_⟩⟩
            rw [traceOf_snoc, traceOf_snoc, if_pos rfl, if_pos rfl]
            exact TrRel.keep _ _ l ots hhalf htr
          · obtain ⟨agF', h1, h2⟩ := sr.ags k agS' hk'
            refine ⟨agF', by rw [List.getElem?_set_ne hkj]; exact h1, ?_⟩
            rw [traceOf_out j l ots hkj, traceOf_out j l ots hkj]
            exact h2
        | true =>
          cases l with
          | LAmoLd aq base tvs asrc =>
            obtain ⟨hots, hprom, _⟩ := memStep_amoLd_inv hm
            subst hots hprom
            obtain ⟨hd, hall⟩ := H.fab _ _ _ _ _ hI hp (.inr ⟨aq, base, tvs, asrc, rfl⟩)
            have hra := (H.tight _ _ _ _ _ _ _ _ hI hp).1
            refine ⟨esF, cF1, hF, ⟨sr.img, sr.log, by rw [sr.dev, hd], by simp [sr.len], fun k agS' hk => ?_,
              hout _ (fun _ _ => rfl)⟩⟩
            simp only at hk ⊢
            rcases getElem?_set_of hk with ⟨hkj, hb, _⟩ | ⟨hkj, hk'⟩
            · subst hkj hb
              refine ⟨agF, hagF, .inr ⟨aq, base, tvs, asrc, st', traceOf j es, [], hI, hn, rfl, hra, hall,
                .refl _, H.inv _ _ _ _ _ hI hp, hm, htr, fun _ h => (by cases h), ?_⟩⟩
              rw [traceOf_snoc, if_pos rfl]
            · obtain ⟨agF', h1, h2⟩ := sr.ags k agS' hk'
              refine ⟨agF', h1, ?_⟩
              rw [traceOf_out j _ _ hkj]
              exact h2
          | LAmoSt rl b data asrc vsrc => exact absurd hn (memStep_amoSt_inv hm).1
          | _ => cases hhalf
      · -- PENDING
        obtain ⟨_, hT⟩ := H.tight _ c1.pcDev _ _ _ _ _ _ hI0 (hld c1.pcDev)
        rcases hT _ hsr _ _ _ _ hp with rfl | ⟨rl, b, data, vsrc, rfl, hrv⟩
        · -- a silent step between the halves
          obtain ⟨hots, hws, hprom⟩ := memStep_silent_inv hm
          subst hots hws hprom
          obtain ⟨hd, hall⟩ := H.fab _ _ _ _ _ hI hp (.inl rfl)
          refine ⟨esF, cF1, hF, ⟨sr.img, sr.log, by rw [sr.dev, hd], by simp [sr.len], fun k agS' hk => ?_,
            hout _ (fun _ _ => rfl)⟩⟩
          simp only at hk ⊢
          rcases getElem?_set_of hk with ⟨hkj, hb, _⟩ | ⟨hkj, hk'⟩
          · subst hkj hb
            refine ⟨agF, hagF, .inr ⟨aq, base, tvs, asrc, h1, s0, sil ++ [(LSilent, none)], hI0, hn0, hpr, hra, hld,
              silentRun_snoc hsr hall, H.inv _ _ _ _ _ hI hp, hml, htr, ?_, ?_⟩⟩
            · intro x hx
              rcases List.mem_append.1 hx with hx | hx
              · exact hsil x hx
              · simpa using hx
            · rw [traceOf_snoc, if_pos rfl, hS]
              simp
          · obtain ⟨agF', h1', h2⟩ := sr.ags k agS' hk'
            refine ⟨agF', h1', ?_⟩
            rw [traceOf_out j _ _ hkj]
            exact h2
        · -- the write half: the fused copy takes the fused step
          obtain ⟨_, ts, hots⟩ := memStep_amoSt_inv hm
          subst hots
          obtain ⟨hbb, _, hmF⟩ := split_rmw hra hrv hn0 hml hm
          rw [hbb] at hp
          have hpF : pstepF agF.paSt cF1.pcDev (LRmw aq rl base tvs data asrc vsrc) st' d' := by
            rw [sr.dev]; exact H.fuse _ _ _ _ _ _ _ _ _ _ _ _ _ hI0 hld hsr hp hra hrv
          have hmF' : memStep cF1.pcImg cF1.pcLog j agF.paProm agF.paWs (LRmw aq rl base tvs data asrc vsrc)
              (some ts) ws' prom' := by rw [sr.img, sr.log]; exact hmF
          refine ⟨esF ++ [.st j (LRmw aq rl base tvs data asrc vsrc) (some ts)],
            ⟨cF1.pcImg, cF1.pcLog, d', cF1.pcAgs.set j ⟨st', ws', prom'⟩⟩,
            pmSteps_append hF (pmSteps_single (.state _ j agF _ _ st' d' ws' prom' hagF hpF hmF')),
            ⟨sr.img, sr.log, rfl, by simp [sr.len], fun k agS' hk => ?_,
              hout _ (fun k hk => traceOf_out j _ _ (Ne.symm hk))⟩⟩
          simp only at hk ⊢
          rcases getElem?_set_of hk with ⟨hkj, hb, _⟩ | ⟨hkj, hk'⟩
          · subst hkj hb
            refine ⟨_, getElem?_set_eq_of hagF, .inl ⟨rfl, H.inv _ _ _ _ _ hI hp,
              memStep_rmw_none hmF rfl hn0, ?_⟩⟩
            rw [traceOf_snoc, traceOf_snoc, if_pos rfl, if_pos rfl, hS, hbb]
            have := TrRel.amo _ _ aq rl base tvs data asrc vsrc ts sil htr hsil
            simpa [List.append_assoc] using this
          · obtain ⟨agF', h1', h2⟩ := sr.ags k agS' hk'
            refine ⟨agF', by rw [List.getElem?_set_ne hkj]; exact h1', ?_⟩
            rw [traceOf_out j _ _ hkj, traceOf_out j _ _ hkj]
            exact h2

/-- **SPLIT ⇒ FUSED, run level.**  Every valid run of the split machine has a valid run of the fused machine with
the same image, final memory, fabric and agent count; every hart's traces are related (`TrRelP`); every final agent
is the same, or the hart is between its halves (`pendS`, slot full) and its fused agent is the one before the read
(then its trace relation is `TrRelP`'s second form). -/
theorem splitToFused (H : SplitOk pstepS pstepF Inv) {img : Image} {d0 : D} {ps : List P} {evs : List PEvt}
    {cfg : PCfg P D} (hps : ∀ p ∈ ps, Inv p) (hv : validRun pstepS img d0 ps evs cfg) :
    ∃ evsF cfgF, validRun pstepF img d0 ps evsF cfgF ∧ cfgF.pcImg = cfg.pcImg ∧ cfgF.pcLog = cfg.pcLog ∧
      cfgF.pcDev = cfg.pcDev ∧ cfgF.pcAgs.length = cfg.pcAgs.length ∧
      (∀ h, TrRelP (traceOf h evsF) (traceOf h evs)) ∧
      (∀ h, cfg.pcAgs.length ≤ h → traceOf h evsF = [] ∧ traceOf h evs = []) ∧
      (∀ (k : Nat) (agS : PAgent P), cfg.pcAgs[k]? = some agS → ∃ agF, cfgF.pcAgs[k]? = some agF ∧
        ((agF = agS ∧ TrRel (traceOf k evsF) (traceOf k evs)) ∨
         (agS.paWs.wRmw ≠ none ∧ pendS pstepS Inv agS.paSt))) := by
  have hf := validRun_factorL hv
  obtain ⟨c1, hp1, hs1⟩ := pmSteps_app_inv hf.1
  have hpr : ∀ e ∈ cfg.pcLog.map promEv, e.isSt = false := by
    intro e he
    obtain ⟨m, _, rfl⟩ := List.mem_map.1 he
    rfl
  have hc1 : ∀ (k : Nat) (ag : PAgent P), c1.pcAgs[k]? = some ag → Inv ag.paSt ∧ ag.paWs.wRmw = none := by
    intro k ag hk
    obtain ⟨ag0, h0, h2, h3⟩ := promsKeep hp1 hpr k ag hk
    simp only [pmInit, List.getElem?_map, Option.map_eq_some_iff] at h0
    obtain ⟨p, hp, rfl⟩ := h0
    rw [h2, h3]
    exact ⟨hps p (List.mem_of_getElem? hp), rfl⟩
  obtain ⟨esF, cF, hFs, sr⟩ := simSF H hc1 (pmStepsR_of hs1) (fun e he => (List.mem_filter.1 he).2)
  have htrS : ∀ h, traceOf h evs = traceOf h (evs.filter PEvt.isSt) := fun h => (traceOf_filter h evs).symm
  have htrF : ∀ h, traceOf h (cfg.pcLog.map promEv ++ esF) = traceOf h esF := by
    intro h; rw [traceOf_append, traceOf_proms]; rfl
  refine ⟨cfg.pcLog.map promEv ++ esF, cF, ⟨pmSteps_append (promsTransfer hp1 hpr) hFs, ?_⟩, sr.img, sr.log, sr.dev,
    sr.len, fun h => ?_, fun h hh => ?_, fun k agS hk => ?_⟩
  · intro k agF hk
    have hlt : k < cfg.pcAgs.length := by rw [← sr.len]; exact (List.getElem?_eq_some_iff.1 hk).1
    obtain ⟨agS, hS⟩ : ∃ agS, cfg.pcAgs[k]? = some agS := ⟨_, List.getElem?_eq_getElem hlt⟩
    obtain ⟨agF', h1, h2⟩ := sr.ags k agS hS
    rw [hk] at h1
    cases h1
    rcases h2 with ⟨rfl, _⟩ | ⟨_, _, _, _, _, _, _, _, _, hpr', _⟩
    · exact hf.2 k _ hS
    · rw [hpr']; exact hf.2 k agS hS
  · rw [htrS, htrF]
    by_cases hlt : h < cfg.pcAgs.length
    · obtain ⟨agS, hS⟩ : ∃ agS, cfg.pcAgs[h]? = some agS := ⟨_, List.getElem?_eq_getElem hlt⟩
      obtain ⟨agF, _, h2⟩ := sr.ags h agS hS
      rcases h2 with ⟨_, _, _, htr⟩ | ⟨aq, base, tvs, asrc, _, s0, sil, _, _, _, _, _, _, _, _, htr, hsil, hS'⟩
      · exact .inl htr
      · exact .inr ⟨s0, aq, base, tvs, asrc, sil, htr, hsil, hS'⟩
    · obtain ⟨e1, e2⟩ := sr.out h (by omega)
      rw [e1, e2]
      exact .inl .nil
  · obtain ⟨e1, e2⟩ := sr.out h hh
    rw [htrS, htrF]
    exact ⟨e2, e1⟩
  · obtain ⟨agF, h1, h2⟩ := sr.ags k agS hk
    refine ⟨agF, h1, ?_⟩
    rcases h2 with ⟨he, _, _, htr⟩ | ⟨aq, base, tvs, asrc, h1', _, _, hI0, _, _, _, hld, hsr, _, hml, _⟩
    · exact .inl ⟨he, by rw [htrS, htrF]; exact htr⟩
    · exact .inr ⟨(memStep_amoLd_inv hml).2.2, agF.paSt, aq, base, tvs, asrc, h1', hI0, hld, hsr⟩

/-- No hart ends between its halves. -/
def closedS (pstepS : P → D → PLabel → P → D → Prop) (Inv : P → Prop) (cfg : PCfg P D) : Prop :=
  ∀ (k : Nat) (ag : PAgent P), cfg.pcAgs[k]? = some ag → ag.paWs.wRmw = none ∨ ¬ pendS pstepS Inv ag.paSt

theorem cfg_eq_of {cfg cfgF : PCfg P D} (himg : cfgF.pcImg = cfg.pcImg) (hlog : cfgF.pcLog = cfg.pcLog)
    (hdev : cfgF.pcDev = cfg.pcDev) (hlen : cfgF.pcAgs.length = cfg.pcAgs.length)
    (hags : ∀ (k : Nat) (agS : PAgent P), cfg.pcAgs[k]? = some agS → cfgF.pcAgs[k]? = some agS) : cfgF = cfg := by
  have hA : cfgF.pcAgs = cfg.pcAgs := by
    apply List.ext_getElem?
    intro k
    cases hk : cfg.pcAgs[k]? with
    | none => exact List.getElem?_eq_none (by rw [hlen]; exact List.getElem?_eq_none_iff.1 hk)
    | some ag => exact hags k ag hk
  cases cfgF; cases cfg
  simp only at himg hlog hdev hA
  subst himg hlog hdev hA
  rfl

/-- **SPLIT ⇒ FUSED, closed runs**: if no hart ends between its halves, the fused run reaches THE SAME final
configuration and every hart's traces are `TrRel`-related. -/
theorem splitToFused_closed (H : SplitOk pstepS pstepF Inv) {img : Image} {d0 : D} {ps : List P}
    {evs : List PEvt} {cfg : PCfg P D} (hps : ∀ p ∈ ps, Inv p) (hv : validRun pstepS img d0 ps evs cfg)
    (hcl : closedS pstepS Inv cfg) :
    ∃ evsF, validRun pstepF img d0 ps evsF cfg ∧ ∀ h, TrRel (traceOf h evsF) (traceOf h evs) := by
  obtain ⟨evsF, cfgF, hvF, himg, hlog, hdev, hlen, _, hout, hags⟩ := splitToFused H hps hv
  have hsync : ∀ (k : Nat) (agS : PAgent P), cfg.pcAgs[k]? = some agS →
      cfgF.pcAgs[k]? = some agS ∧ TrRel (traceOf k evsF) (traceOf k evs) := by
    intro k agS hk
    obtain ⟨agF, h1, h2⟩ := hags k agS hk
    rcases h2 with ⟨rfl, htr⟩ | ⟨hne, hpd⟩
    · exact ⟨h1, htr⟩
    · rcases hcl k agS hk with h | h
      · exact absurd h hne
      · exact absurd hpd h
  have he := cfg_eq_of himg hlog hdev hlen (fun k agS hk => (hsync k agS hk).1)
  subst he
  refine ⟨evsF, hvF, fun h => ?_⟩
  by_cases hlt : h < cfgF.pcAgs.length
  · obtain ⟨agS, hS⟩ : ∃ agS, cfgF.pcAgs[h]? = some agS := ⟨_, List.getElem?_eq_getElem hlt⟩
    exact (hsync h agS hS).2
  · obtain ⟨e1, e2⟩ := hout h (by omega)
    rw [e1, e2]
    exact .nil

end sf

/-! ## 9. Fused ⇒ split -/

section fs

variable {P D : Type} {pstepS pstepF : P → D → PLabel → P → D → Prop} {Inv : P → Prop}

/-- A silent chain of agent `j` is a run of silent state events of `j` (the fabric threaded through). -/
theorem silentBlock {j : Nat} {ws : PState} {prom : GSet Nat} {img : Image} {log : List PMsg} :
    ∀ {h1 : P} {d1 : D} {hk : P} {dk : D}, silentRunD pstepS h1 d1 hk dk →
      ∀ (ags : List (PAgent P)), j < ags.length →
      ∃ (sevs : List PEvt) (sil : List (PLabel × Option Nat)),
        pmSteps pstepS ⟨img, log, d1, ags.set j ⟨h1, ws, prom⟩⟩ sevs ⟨img, log, dk, ags.set j ⟨hk, ws, prom⟩⟩ ∧
        allSil sil ∧ ∀ k, traceOf k sevs = if j = k then sil else [] := by
  intro h1 d1 hk dk hs
  induction hs with
  | refl h d =>
    intro ags _
    exact ⟨[], [], .refl _, (fun _ h => by cases h), (fun k => by split <;> rfl)⟩
  | step h d h1' d1' h2 d2 hst _ ih =>
    intro ags hj
    obtain ⟨sevs, sil, hr, hsil, htr⟩ := ih ags hj
    have hag : (ags.set j (⟨h, ws, prom⟩ : PAgent P))[j]? = some ⟨h, ws, prom⟩ := by simp [hj]
    have h1st := pmStep.state (pstep := pstepS) ⟨img, log, d, ags.set j ⟨h, ws, prom⟩⟩ j ⟨h, ws, prom⟩ LSilent none
      h1' d1' ws prom hag hst (memStep.silent prom ws)
    simp only [List.set_set] at h1st
    refine ⟨.st j LSilent none :: sevs, (LSilent, none) :: sil, .step _ _ _ _ _ h1st hr, ?_, fun k => ?_⟩
    · intro x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · rfl
      · exact hsil x hx
    · rw [traceOf_cons_st, htr k]
      split <;> rfl

/-- THE SIMULATION of a fused run by a split one (each fused AMO step expands in place). -/
theorem simFS (H : FuseOk pstepF pstepS Inv) :
    ∀ {c c' : PCfg P D} {es : List PEvt}, pmSteps pstepF c es c' →
      (∀ (k : Nat) (ag : PAgent P), c.pcAgs[k]? = some ag → Inv ag.paSt ∧ ag.paWs.wRmw = none) →
      ∃ esS, pmSteps pstepS c esS c' ∧ ∀ h, TrRel (traceOf h es) (traceOf h esS) := by
  intro c c' es hr
  induction hr with
  | refl c => intro _; exact ⟨[], .refl _, fun _ => .nil⟩
  | step c0 c1 c2 e es hs _ ih =>
    intro hc
    cases hs with
    | promise i ag m hag hnt htid =>
      obtain ⟨esS, hS, htr⟩ := ih (fun k ag' hk => by
        simp only at hk
        rcases getElem?_set_of hk with ⟨hkj, hb, _⟩ | ⟨_, hk'⟩
        · subst hkj hb
          exact hc _ ag hag
        · exact hc k ag' hk')
      exact ⟨.prom i m :: esS, .step _ _ _ _ _ (.promise _ i ag m hag hnt htid) hS, fun h => htr h⟩
    | state j ag l ots st' d' ws' prom' hag hp hm =>
      obtain ⟨hI, hn⟩ := hc j ag hag
      have hj : j < c0.pcAgs.length := (List.getElem?_eq_some_iff.1 hag).1
      have hcase := H.step _ _ _ _ _ hI hp
      have hl : isHalf l = false := by
        rcases hcase with ⟨hl, _⟩ | ⟨_, _, _, _, _, _, _, _, _, _, _, rfl, _⟩
        · exact hl
        · rfl
      obtain ⟨esS, hS, htr⟩ := ih (fun k ag' hk => by
        simp only at hk
        rcases getElem?_set_of hk with ⟨hkj, hb, _⟩ | ⟨_, hk'⟩
        · subst hkj hb
          exact ⟨H.inv _ _ _ _ _ hI hp, memStep_rmw_none hm hl hn⟩
        · exact hc k ag' hk')
      rcases hcase with ⟨_, hpS⟩ | ⟨aq, rl, base, tvs, data, asrc, vsrc, h1, d1, hk, dk, rfl, hra, hrv, hld, hsr, hst⟩
      · refine ⟨.st j l ots :: esS, .step _ _ _ _ _ (.state _ j ag l ots st' d' ws' prom' hag hpS hm) hS,
          fun h => ?_⟩
        rw [traceOf_cons_st, traceOf_cons_st]
        split
        · exact TrRel_append (TrRel_single hl) (htr h)
        · exact htr h
      · obtain ⟨ts, rfl⟩ := memStep_rmw_inv hm
        obtain ⟨ws1, hm1, hm2⟩ := rmw_split hra hrv hn hm
        have e1 := pmStep.state (pstep := pstepS) c0 j ag (LAmoLd aq base tvs asrc) none h1 d1 ws1 ag.paProm hag hld
          hm1
        obtain ⟨sevs, sil, hsev, hsil, htrs⟩ := silentBlock (ws := ws1) (prom := ag.paProm) (img := c0.pcImg)
          (log := c0.pcLog) hsr c0.pcAgs hj
        have hagk : (c0.pcAgs.set j (⟨hk, ws1, ag.paProm⟩ : PAgent P))[j]? = some ⟨hk, ws1, ag.paProm⟩ := by
          simp [hj]
        have e3 := pmStep.state (pstep := pstepS) ⟨c0.pcImg, c0.pcLog, dk, c0.pcAgs.set j ⟨hk, ws1, ag.paProm⟩⟩ j
          ⟨hk, ws1, ag.paProm⟩ (LAmoSt rl base data asrc vsrc) (some ts) st' d' ws' prom' hagk hst hm2
        simp only [List.set_set] at e3
        refine ⟨.st j (LAmoLd aq base tvs asrc) none :: (sevs ++
            (.st j (LAmoSt rl base data asrc vsrc) (some ts) :: esS)),
          .step _ _ _ _ _ e1 (pmSteps_append hsev (.step _ _ _ _ _ e3 hS)), fun h => ?_⟩
        rw [traceOf_cons_st, traceOf_cons_st, traceOf_append, traceOf_cons_st, htrs h]
        split
        · have h0 := TrRel.amo [] [] aq rl base tvs data asrc vsrc ts sil .nil hsil
          have := TrRel_append h0 (htr h)
          simpa [List.append_assoc] using this
        · simpa using htr h

/-- **FUSED ⇒ SPLIT, run level.**  Every valid run of the fused machine is a valid run of the split machine with
THE SAME FINAL CONFIGURATION (so the same final memory, registers and fabric), every hart's traces related by
`TrRel` (so the same load-like answers in order). -/
theorem fusedToSplit (H : FuseOk pstepF pstepS Inv) {img : Image} {d0 : D} {ps : List P} {evs : List PEvt}
    {cfg : PCfg P D} (hps : ∀ p ∈ ps, Inv p) (hv : validRun pstepF img d0 ps evs cfg) :
    ∃ evsS, validRun pstepS img d0 ps evsS cfg ∧ ∀ h, TrRel (traceOf h evs) (traceOf h evsS) := by
  obtain ⟨esS, hS, htr⟩ := simFS H hv.1 (fun k ag hk => by
    simp only [pmInit, List.getElem?_map, Option.map_eq_some_iff] at hk
    obtain ⟨p, hp, rfl⟩ := hk
    exact ⟨hps p (List.mem_of_getElem? hp), rfl⟩)
  exact ⟨esS, ⟨hS, hv.2⟩, htr⟩

end fs

end Weak.Prom.AS
