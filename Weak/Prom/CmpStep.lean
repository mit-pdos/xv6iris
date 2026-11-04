/-
Weak/Prom: **completeness S3a — machine v2's post-state functions, byte by byte** (Machine.lean §4–§6).

The simulation (Weak/Prom/CmpSim.lean) needs, for the labels a litmus hart of S3a emits, what each post-state
function does to each field: a load's byte fold `loadBytes` over answers with ONE timestamp (NA-6: every byte of a
single-size load comes from the same store), the store's `storeBytes`, and the answer-free labels' effect `afEff`
(register write, instruction boundary, fence, control, FENCE.I), with `afEff_step` (each is a `memStep`).
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Prom.CmpSym
import Weak.Prom.CoreFwd

namespace Weak.Prom.Cmp

open MachCSL MachCSL.Stdpp Iris.Std
open Weak (Image Dsrc)
open Weak.Prom Weak.Prom.Mach Weak.Prom.Mach.Cert
open Weak.Prom.Ref (Instr)
open PLabel

/-! ## 1. Byte runs with one timestamp -/

/-- The answers of a single-size load: every byte from timestamp `t`. -/
def uniTvs (t : Nat) (vs : List (BitVec 8)) : List (Nat × BitVec 8) := vs.map (fun v => (t, v))

theorem bytesAll_uni (P : Int → Nat → BitVec 8 → Prop) (t : Nat) :
    ∀ (vs : List (BitVec 8)) (a : Int), (∀ (k : Nat) v, vs[k]? = some v → P (a + k) t v) →
      bytesAll P a (uniTvs t vs)
  | [], _, _ => trivial
  | v :: vs, a, h => by
    have h0 := h 0 v rfl
    rw [show a + ((0 : Nat) : Int) = a by omega] at h0
    refine ⟨h0, bytesAll_uni P t vs (a + 1) (fun k v' hk => ?_)⟩
    have := h (k + 1) v' (by simpa using hk)
    rw [show a + 1 + (k : Int) = a + ((k + 1 : Nat) : Int) by push_cast; omega]
    exact this

theorem bytesMax_uni_le (f : Int → Nat → Nat) (t B : Nat) :
    ∀ (vs : List (BitVec 8)) (a : Int), (∀ k, k < vs.length → f (a + k) t ≤ B) →
      bytesMax f a (uniTvs t vs) ≤ B
  | [], _, _ => Nat.zero_le _
  | v :: vs, a, h => by
    simp only [uniTvs, List.map_cons, bytesMax]
    have h0 := h 0 (by simp)
    rw [show a + ((0 : Nat) : Int) = a by omega] at h0
    have ih := bytesMax_uni_le f t B vs (a + 1) (fun k hk => by
      have := h (k + 1) (by simp; omega)
      rwa [show a + ((k + 1 : Nat) : Int) = a + 1 + (k : Int) by push_cast; omega] at this)
    simp only [uniTvs] at ih
    omega

theorem nonFwdMax_uni_le (ws : PState) (t : Nat) (vs : List (BitVec 8)) (a : Int) :
    nonFwdMax ws a (uniTvs t vs) ≤ t :=
  bytesMax_uni_le _ t t vs a (fun k _ => by split <;> omega)

theorem uniTvs_length (t : Nat) (vs : List (BitVec 8)) : (uniTvs t vs).length = vs.length := by simp [uniTvs]

theorem uniTvs_snd (t : Nat) (vs : List (BitVec 8)) : (uniTvs t vs).map Prod.snd = vs := by
  induction vs with
  | nil => rfl
  | cons v vs ih => simp only [uniTvs, List.map_cons] at ih ⊢; rw [ih]

/-! ## 2. The load's byte fold -/

theorem coh_insert (ws : PState) (a b : Int) (v : Nat) :
    coh { ws with wCoh := insert ws.wCoh a v } b = if a = b then v else coh ws b := by
  unfold coh
  by_cases h : a = b
  · subst h; simp only [lookupInsert, Option.getD_some, if_true]
  · simp only; rw [lookupInsertNe h, if_neg h]

/-- WHAT A SINGLE-SIZE LOAD'S BYTE FOLD DOES (`aq = false`). -/
theorem loadBytes_uni (vpre t : Nat) :
    ∀ (vs : List (BitVec 8)) (ws : PState) (a : Int),
      (loadBytes false vpre ws a (uniTvs t vs)).wFwd = ws.wFwd ∧
      (loadBytes false vpre ws a (uniTvs t vs)).wRegv = ws.wRegv ∧
      (loadBytes false vpre ws a (uniTvs t vs)).wVcap = ws.wVcap ∧
      (loadBytes false vpre ws a (uniTvs t vs)).wVRel = ws.wVRel ∧
      (loadBytes false vpre ws a (uniTvs t vs)).wVwOld = ws.wVwOld ∧
      (loadBytes false vpre ws a (uniTvs t vs)).wVrNew = ws.wVrNew ∧
      (loadBytes false vpre ws a (uniTvs t vs)).wVwNew = ws.wVwNew ∧
      (loadBytes false vpre ws a (uniTvs t vs)).wIfv = ws.wIfv ∧
      (∀ B, (∀ k, k < vs.length → max vpre (fwdView ws false (a + k) t) ≤ B) →
        (loadBytes false vpre ws a (uniTvs t vs)).wVrOld ≤ max ws.wVrOld B ∧
        (loadBytes false vpre ws a (uniTvs t vs)).wLdv ≤ max ws.wLdv B) ∧
      (∀ b : Int, coh (loadBytes false vpre ws a (uniTvs t vs)) b = coh ws b ∨
        ∃ k, k < vs.length ∧ b = a + k ∧
          coh (loadBytes false vpre ws a (uniTvs t vs)) b = max (coh ws b) (max (max vpre (fwdView ws false b t)) t))
  | [], ws, a => ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun B _ => ⟨by simp [uniTvs, loadBytes]; omega,
      by simp [uniTvs, loadBytes]; omega⟩, fun b => .inl rfl⟩
  | v :: vs, ws, a => by
    have hcons : loadBytes false vpre ws a (uniTvs t (v :: vs)) =
        loadBytes false vpre (loadByte ws false vpre a t) (a + 1) (uniTvs t vs) := rfl
    obtain ⟨i1, i2, i3, i4, i5, i6, i7, i8, i9, i10⟩ := loadBytes_uni vpre t vs (loadByte ws false vpre a t) (a + 1)
    have hfv : ∀ b, fwdView (loadByte ws false vpre a t) false b t = fwdView ws false b t := fun b => rfl
    rw [hcons]
    refine ⟨i1, i2, i3, i4, i5, i6, i7, i8, fun B hB => ?_, fun b => ?_⟩
    · have h0 := hB 0 (by simp)
      rw [show a + ((0 : Nat) : Int) = a by omega] at h0
      obtain ⟨j1, j2⟩ := i9 B (fun k hk => by
        rw [hfv]
        have := hB (k + 1) (by simp; omega)
        rwa [show a + ((k + 1 : Nat) : Int) = a + 1 + (k : Int) by push_cast; omega] at this)
      have e1 : (loadByte ws false vpre a t).wVrOld = max ws.wVrOld (max vpre (fwdView ws false a t)) := rfl
      have e2 : (loadByte ws false vpre a t).wLdv = max ws.wLdv (max vpre (fwdView ws false a t)) := rfl
      rw [e1] at j1; rw [e2] at j2
      exact ⟨by omega, by omega⟩
    · have hc1 : coh (loadByte ws false vpre a t) b =
          if a = b then max (coh ws a) (max (max vpre (fwdView ws false a t)) t) else coh ws b :=
        coh_insert ws a b _
      rcases i10 b with h | ⟨k, hk, hb, hc⟩
      · rw [h, hc1]
        by_cases hab : a = b
        · subst hab; rw [if_pos rfl]
          exact .inr ⟨0, by simp, by simp, rfl⟩
        · rw [if_neg hab]; exact .inl rfl
      · have hab : a ≠ b := by omega
        rw [hc, hc1, if_neg hab, hfv]
        exact .inr ⟨k + 1, by simp; omega, by rw [hb]; push_cast; omega, rfl⟩

/-! ## 3. The store's byte fold -/

theorem storeBytes_spec : ∀ (n : Nat) (ws : PState) (a : Int) (ts fv : Nat),
    (∀ b : Int, coh (storeBytes ws a n ts fv) b = if a ≤ b ∧ b < a + n then max (coh ws b) ts else coh ws b) ∧
    (∀ b : Int, get? (storeBytes ws a n ts fv).wFwd b = if a ≤ b ∧ b < a + n then some (ts, fv) else get? ws.wFwd b) ∧
    (storeBytes ws a n ts fv).wRegv = ws.wRegv ∧ (storeBytes ws a n ts fv).wVcap = ws.wVcap ∧
    (storeBytes ws a n ts fv).wVrOld = ws.wVrOld ∧ (storeBytes ws a n ts fv).wVwOld = ws.wVwOld ∧
    (storeBytes ws a n ts fv).wVrNew = ws.wVrNew ∧ (storeBytes ws a n ts fv).wVwNew = ws.wVwNew ∧
    (storeBytes ws a n ts fv).wLdv = ws.wLdv ∧ (storeBytes ws a n ts fv).wIfv = ws.wIfv ∧
    (storeBytes ws a n ts fv).wVRel = ws.wVRel
  | 0, ws, a, ts, fv => ⟨fun b => by simp only [storeBytes]; rw [if_neg (by omega)],
      fun b => by simp only [storeBytes]; rw [if_neg (by omega)], rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  | n + 1, ws, a, ts, fv => by
    obtain ⟨i1, i2, i3, i4, i5, i6, i7, i8, i9, i10, i11⟩ := storeBytes_spec n
      { ws with wCoh := insert ws.wCoh a (max (coh ws a) ts), wFwd := insert ws.wFwd a (ts, fv) } (a + 1) ts fv
    simp only [storeBytes]
    refine ⟨fun b => ?_, fun b => ?_, i3, i4, i5, i6, i7, i8, i9, i10, i11⟩
    · rw [i1 b]
      have hc : coh { ws with wCoh := insert ws.wCoh a (max (coh ws a) ts), wFwd := insert ws.wFwd a (ts, fv) } b =
          if a = b then max (coh ws a) ts else coh ws b := coh_insert ws a b _
      rw [hc]
      by_cases h2 : a = b
      · subst h2
        rw [if_neg (by omega : ¬ (a + 1 ≤ a ∧ a < a + 1 + (n : Int))), if_pos rfl, if_pos (by omega)]
      · rw [if_neg h2]
        by_cases h1 : a + 1 ≤ b ∧ b < a + 1 + n
        · rw [if_pos h1, if_pos (by omega)]
        · rw [if_neg h1, if_neg (by omega)]
    · rw [i2 b]
      by_cases h1 : a + 1 ≤ b ∧ b < a + 1 + n
      · rw [if_pos h1, if_pos (by omega)]
      · rw [if_neg h1]
        by_cases h2 : a = b
        · subst h2; simp only; rw [lookupInsert, if_pos (by omega)]
        · simp only; rw [lookupInsertNe h2, if_neg (by omega)]

/-! ## 4. Answer-free labels -/

/-- The labels of S3a that carry no memory answers and fulfil nothing. -/
def afOk : PLabel → Bool
  | LRegW .. | LInstr | LFence .. | LCtrl .. | LFenceI => true
  | _ => false

/-- Their memory half, as a function (Machine.lean `memStep`'s `regW`, `instr`, `fence`, `ctrl`, `fenceI`). -/
def afEff (ws : PState) : PLabel → PState
  | LRegW rd srcs => { ws with wRegv := insert ws.wRegv rd (srcsView ws srcs) }
  | LInstr => { ws with wLdv := 0, wRmw := none, wIfv := 0 }
  | LFence pr pw sr sw => fencePost ws pr pw sr sw
  | LCtrl srcs => { ws with wVcap := max (srcsView ws srcs) ws.wVcap }
  | LFenceI => fenceIPost ws
  | _ => ws

theorem afEff_step (img : Image) (log : List PMsg) (i : Nat) (prom : GSet Nat) (ws : PState) (l : PLabel)
    (h : afOk l = true) : memStep img log i prom ws l none (afEff ws l) prom := by
  cases l <;> simp only [afOk] at h <;> first | cases h | skip
  · exact .fence prom ws _ _ _ _
  · exact .fenceI prom ws
  · exact .regW prom ws _ _
  · exact .ctrl prom ws _
  · exact .instr prom ws

/-- A run of answer-free labels from the queue. -/
theorem solo_af (img : Image) (M : List PMsg) (i : Nat) :
    ∀ (labs : List PLabel) (lp : LP) (ws : PState) (prom : GSet Nat), (∀ l ∈ labs, afOk l = true) →
      lp.q = labs → soloSteps litStep img M i (lp, ws, prom) (labs.map (fun l => (l, none)))
        ({ lp with q := [] }, labs.foldl afEff ws, prom)
  | [], lp, ws, prom, _, hq => by
    have : ({ lp with q := [] } : LP) = lp := by cases lp; simp only at hq; subst hq; rfl
    rw [this]; exact .refl _
  | l :: rest, lp, ws, prom, hok, hq => by
    have hstep : litStep lp () l { lp with q := rest } () := by
      show litNext lp l = some { lp with q := rest }
      simp [litNext, hq]
    have ih := solo_af img M i rest { lp with q := rest } (afEff ws l) prom
      (fun l' hl' => hok l' (List.mem_cons_of_mem _ hl')) rfl
    exact .step _ l none _ _ _ _ _ hstep (afEff_step img M i prom ws l (hok l (List.mem_cons_self ..))) ih

/-- An instruction whose labels are all answer-free (MachCert.lean `go1`). -/
theorem solo_go1 (img : Image) (M : List PMsg) (i : Nat) (lp : LP) (ws : PState) (prom : GSet Nat)
    (ins : Instr) (regs' : List Nat) (pc' : Nat) (l0 : PLabel) (rest : List PLabel)
    (hq : lp.q = []) (hi : lp.prog[lp.pc]? = some ins)
    (hn : instrNext lp.prog.length lp ins l0 = go1 lp regs' pc' (l0 :: rest) l0)
    (hok : ∀ l ∈ l0 :: rest, afOk l = true) :
    soloSteps litStep img M i (lp, ws, prom) ((l0 :: rest).map (fun l => (l, none)))
      ({ lp with regs := regs', pc := pc', q := [] }, (l0 :: rest).foldl afEff ws, prom) := by
  have hstep : litStep lp () l0 { lp with regs := regs', pc := pc', q := rest } () := by
    show litNext lp l0 = some _
    simp only [litNext, hq, hi]
    rw [hn]
    simp [go1]
  have ih := solo_af img M i rest { lp with regs := regs', pc := pc', q := rest } (afEff ws l0) prom
    (fun l' hl' => hok l' (List.mem_cons_of_mem _ hl')) rfl
  exact .step _ l0 none _ _ _ _ _ hstep (afEff_step img M i prom ws l0 (hok l0 (List.mem_cons_self ..))) ih

theorem afOk_noLoad {l : PLabel} (h : afOk l = true) : PF.loadLikeTvs l = none := by
  cases l <;> simp only [afOk] at h <;> first | rfl | cases h

theorem machRow_af (labs : List PLabel) (h : ∀ l ∈ labs, afOk l = true) :
    machRow (labs.map (fun l => (l, (none : Option Nat)))) = [] := by
  induction labs with
  | nil => rfl
  | cons l rest ih =>
    have hl := afOk_noLoad (h l (List.mem_cons_self ..))
    have ih' := ih (fun l' hl' => h l' (List.mem_cons_of_mem _ hl'))
    unfold machRow PF.loadsOf at ih' ⊢
    simp only [List.map_cons, List.filterMap_cons, hl]
    exact ih'

theorem machRow_append (τ τ' : PF.Trace) : machRow (τ ++ τ') = machRow τ ++ machRow τ' := by
  simp [machRow, PF.loadsOf, List.filterMap_append]

end Weak.Prom.Cmp
