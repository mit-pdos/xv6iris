/-
Weak/Mini: **E2 part 3 — the memory halves agree** (mini plan rev 4 §2 L2, E2; THE INERTNESS INVARIANT).

`RelWs P ms ws`: machine v2's agent state `ws` is the mini state `ms` — the six views and the register views equal,
every byte of an aligned word has the word's coherence floor and forward-bank entry, and the fields F never moves
are INERT: `wVRel = 0`, `wRes = none`, `wRmw = none`, `wIfl = wIfr = wIfv = 0` (plan §2 L2; pattern `x_noInvalT`,
OwnAFront.lean:416).  `mem_fwd`/`mem_bwd`: under `RelWs`, an embedded good log and matching promise sets, a mini
memory step and machine v2's `memStep` on the embedded label are interchangeable (the load arm's `vi` is forced to
`0`: an embedded log has no CMO message, `invalCite_vi0`).
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Mini.EqMachFront
import Weak.Prom.CmpStep

namespace MiniEq

open MachCSL MachCSL.Stdpp Iris.Std
open Weak.Prom Weak.Prom.Mach Weak.Prom.Mach.Cert Weak.Prom.Cmp
open Weak (Dsrc)
open Weak.Mini
open PLabel

/-- THE STATE RELATION (with the inertness invariant). -/
structure RelWs (P : MProg) (ms : Mach.MSt) (ws : PState) : Prop where
  vrOld : ws.wVrOld = ms.vrOld
  vwOld : ws.wVwOld = ms.vwOld
  vrNew : ws.wVrNew = ms.vrNew
  vwNew : ws.wVwNew = ms.vwNew
  vcap : ws.wVcap = ms.vcap
  ldv : ws.wLdv = ms.ldv
  regv : ∀ r, regv ws r = ms.regv r
  word : ∀ a, a % P.sz = 0 → ∀ k, k < P.sz →
    coh ws ((a + k : Nat) : Int) = ms.coh a ∧ get? ws.wFwd ((a + k : Nat) : Int) = ms.fwd a
  vrel : ws.wVRel = 0
  res : ws.wRes = none
  rmw : ws.wRmw = none
  ifl : ws.wIfl = 0
  ifr : ws.wIfr = 0
  ifv : ws.wIfv = 0

theorem relWs_init (P : MProg) : RelWs P Mach.msInit psInit := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, fun r => ?_, fun a _ k _ => ⟨?_, ?_⟩, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · simp [Weak.Prom.regv, psInit, lookupEmpty, Mach.msInit]
  · simp [coh, psInit, lookupEmpty, Mach.msInit]
  · simp [psInit, lookupEmpty, Mach.msInit]

/-! ## 1. Views -/

theorem srcsView_emb {P : MProg} {ms : Mach.MSt} {ws : PState} (hR : RelWs P ms ws) :
    ∀ srcs, srcsView ws (embSs srcs) = Mach.srcsView ms srcs
  | [] => rfl
  | s :: r => by
    simp only [embSs, List.map_cons, srcsView, List.foldr_cons, Mach.srcsView] at *
    have := srcsView_emb hR r
    simp only [srcsView, Mach.srcsView, embSs] at this
    rw [this]
    cases s with
    | reg x => simp only [embS, dsrcView, Mach.srcView, hR.regv]
    | ldres => simp only [embS, dsrcView, Mach.srcView, hR.ldv]

theorem ldPre_emb {P : MProg} {ms : Mach.MSt} {ws : PState} (hR : RelWs P ms ws) (va : Nat) :
    ldPre ws false false va = Mach.ldPre ms va := by
  simp only [ldPre, Mach.ldPre, hR.ifv, hR.vrNew, Bool.false_eq_true, if_false]; omega

theorem stPre_emb {P : MProg} {ms : Mach.MSt} {ws : PState} (hR : RelWs P ms ws) (va vd : Nat) :
    stPreA ws false false va vd = Mach.stPre ms va vd := by
  simp only [stPreA, stPre, Mach.stPre, hR.ifv, hR.vcap, hR.vwNew, Bool.false_eq_true, if_false]; omega

/-! ## 2. Byte runs of one timestamp -/

theorem bytesAll_map (Q : Int → Nat → BitVec 8 → Prop) (t : Nat) : ∀ (bs : List (BitVec 8)) (a : Nat),
    bytesAll Q (a : Int) (bs.map (fun x => (t, x))) ↔ ∀ k (hk : k < bs.length), Q ((a + k : Nat) : Int) t bs[k]
  | [], _ => by simp [bytesAll]
  | b :: r, a => by
    simp only [List.map_cons, bytesAll]
    have ih := bytesAll_map Q t r (a + 1)
    rw [show ((a + 1 : Nat) : Int) = (a : Int) + 1 by push_cast; rfl] at ih
    rw [ih]
    constructor
    · rintro ⟨h0, h1⟩ k hk
      cases k with
      | zero => exact h0
      | succ k =>
        have := h1 k (by simpa using hk)
        rw [show a + (k + 1) = a + 1 + k by omega]; simpa using this
    · intro h
      refine ⟨h 0 (by simp), fun k hk => ?_⟩
      have := h (k + 1) (by simp; omega)
      rw [show a + (k + 1) = a + 1 + k by omega] at this; simpa using this

theorem bytesAll_imp {Q R : Int → Nat → BitVec 8 → Prop} (hQR : ∀ a t v, Q a t v → R a t v) :
    ∀ (b : Int) (l : List (Nat × BitVec 8)), bytesAll Q b l → bytesAll R b l
  | _, [], _ => trivial
  | b, (t, v) :: r, h => ⟨hQR b t v h.1, bytesAll_imp hQR (b + 1) r h.2⟩

theorem bytesMax_uni (f : Int → Nat → Nat) (t c : Nat) : ∀ (bs : List (BitVec 8)) (a : Nat), bs ≠ [] →
    (∀ k, k < bs.length → f ((a + k : Nat) : Int) t = c) → bytesMax f (a : Int) (bs.map (fun x => (t, x))) = c
  | [], _, h, _ => absurd rfl h
  | b :: r, a, _, hf => by
    show max (f (a : Int) t) (bytesMax f ((a : Int) + 1) (r.map (fun x => (t, x)))) = c
    have h0 : f (a : Int) t = c := hf 0 (by simp)
    rw [h0]
    cases r with
    | nil => simp [bytesMax]
    | cons b' r' =>
      have ih := bytesMax_uni f t c (b' :: r') (a + 1) (by simp) (fun k hk => by
        have := hf (k + 1) (by simp at hk ⊢; omega); rwa [show a + (k + 1) = a + 1 + k by omega] at this)
      rw [show ((a + 1 : Nat) : Int) = (a : Int) + 1 by push_cast; rfl] at ih
      rw [ih]; omega

theorem cohBelow_iff (ws : PState) (ts : Nat) : ∀ (n a : Nat),
    cohBelow ws (a : Int) n ts ↔ ∀ k, k < n → coh ws ((a + k : Nat) : Int) < ts
  | 0, _ => by simp [cohBelow]
  | n + 1, a => by
    simp only [cohBelow]
    have ih := cohBelow_iff ws ts n (a + 1)
    rw [show ((a + 1 : Nat) : Int) = (a : Int) + 1 by push_cast; rfl] at ih
    rw [ih]
    constructor
    · rintro ⟨h0, h1⟩ k hk
      cases k with
      | zero => simpa using h0
      | succ k => have := h1 k (by omega); rwa [show a + (k + 1) = a + 1 + k by omega]
    · intro h
      refine ⟨by simpa using h 0 (by omega), fun k hk => ?_⟩
      have := h (k + 1) (by omega); rwa [show a + (k + 1) = a + 1 + k by omega] at this

/-! ## 3. The load's byte fold -/

theorem loadBytes_shape (vpre : Nat) : ∀ (tvs : List (Nat × BitVec 8)) (ws : PState) (b : Int),
    ∃ c vr ld, loadBytes false vpre ws b tvs = { ws with wCoh := c, wVrOld := vr, wLdv := ld }
  | [], ws, _ => ⟨ws.wCoh, ws.wVrOld, ws.wLdv, rfl⟩
  | (t, _) :: r, ws, b => by
    obtain ⟨c, vr, ld, h⟩ := loadBytes_shape vpre r (loadByte ws false vpre b t) (b + 1)
    exact ⟨c, vr, ld, by simp only [loadBytes]; rw [h]; rfl⟩

theorem loadBytes_vals (vpre t F : Nat) : ∀ (bs : List (BitVec 8)) (ws : PState) (a : Nat),
    (∀ k, k < bs.length → fwdView ws false ((a + k : Nat) : Int) t = F) →
    (loadBytes false vpre ws a (bs.map (fun x => (t, x)))).wVrOld =
        (if bs = [] then ws.wVrOld else max ws.wVrOld (max vpre F)) ∧
    (loadBytes false vpre ws a (bs.map (fun x => (t, x)))).wLdv =
        (if bs = [] then ws.wLdv else max ws.wLdv (max vpre F)) ∧
    ∀ x : Int, coh (loadBytes false vpre ws a (bs.map (fun x => (t, x)))) x =
      if (a : Int) ≤ x ∧ x < a + bs.length then max (coh ws x) (max (max vpre F) t) else coh ws x
  | [], ws, a, _ => ⟨rfl, rfl, fun x => by
      have : ¬ ((a : Int) ≤ x ∧ x < (a : Int) + (([] : List (BitVec 8)).length : Nat)) := by
        intro ⟨h1, h2⟩; simp at h2; omega
      rw [if_neg this]; rfl⟩
  | b :: r, ws, a, hF => by
    have h0 := hF 0 (by simp); simp only [Nat.add_zero] at h0
    have hcons : loadBytes false vpre ws a ((b :: r).map (fun x => (t, x))) =
        loadBytes false vpre (loadByte ws false vpre a t) ((a + 1 : Nat) : Int) (r.map (fun x => (t, x))) := by
      simp only [List.map_cons, loadBytes]; congr 1
    have hfv : ∀ x, fwdView (loadByte ws false vpre a t) false x t = fwdView ws false x t := fun _ => rfl
    obtain ⟨i1, i2, i3⟩ := loadBytes_vals vpre t F r (loadByte ws false vpre a t) (a + 1) (fun k hk => by
      rw [hfv]; have := hF (k + 1) (by simp; omega); rwa [show a + (k + 1) = a + 1 + k by omega] at this)
    rw [hcons]
    have e1 : (loadByte ws false vpre a t).wVrOld = max ws.wVrOld (max vpre F) := by
      simp only [loadByte]; rw [← h0]
    have e2 : (loadByte ws false vpre a t).wLdv = max ws.wLdv (max vpre F) := by
      simp only [loadByte]; rw [← h0]
    refine ⟨?_, ?_, fun x => ?_⟩
    · rw [i1, e1]; split <;> simp <;> omega
    · rw [i2, e2]; split <;> simp <;> omega
    · rw [i3 x]
      have hc1 : coh (loadByte ws false vpre a t) x =
          if (a : Int) = x then max (coh ws a) (max (max vpre F) t) else coh ws x := by
        rw [← h0]; exact coh_insert ws a x _
      rw [hc1]
      simp only [List.length_cons]
      by_cases hx : (a : Int) = x
      · subst hx
        rw [if_neg (by push_cast; omega), if_pos rfl, if_pos (by omega)]
      · rw [if_neg hx]
        by_cases hr : ((a + 1 : Nat) : Int) ≤ x ∧ x < ((a + 1 : Nat) : Int) + r.length
        · rw [if_pos hr, if_pos (by push_cast at hr; omega)]
        · rw [if_neg hr, if_neg (by push_cast at hr; omega)]

/-! ## 4. Post-states keep the relation -/

theorem word_split {P : MProg} {a a' k : Nat} (ha : a % P.sz = 0) (ha' : a' % P.sz = 0) (hk : k < P.sz) :
    ((a : Int) ≤ ((a' + k : Nat) : Int) ∧ ((a' + k : Nat) : Int) < (a : Int) + (P.sz : Nat)) ↔ a' = a := by
  constructor
  · rintro ⟨h1, h2⟩; exact (aligned_eq ha ha' hk (by omega) (by omega)).symm
  · rintro rfl; omega

theorem relWs_load (P : MProg) (hwf : Mach.progWf P) {ms : Mach.MSt} {ws : PState} (hR : RelWs P ms ws)
    {a t va : Nat} (ha : a % P.sz = 0) (bs : List (BitVec 8)) (hbs : bs.length = P.sz) :
    RelWs P (Mach.loadPost ms va (Mach.ldPre ms va) a t)
      (loadRunV ws false false va 0 (a : Int) (bs.map (fun x => (t, x)))) := by
  have hsz := hwf.1
  rw [loadRunV_zero]
  have hne : bs ≠ [] := by intro h; rw [h] at hbs; simp at hbs; omega
  have hF : ∀ k, k < bs.length → fwdView ws false ((a + k : Nat) : Int) t = Mach.fwdView ms a t := by
    intro k hk
    unfold fwdView Mach.fwdView
    rw [(hR.word a ha k (by omega)).2]
    cases ms.fwd a with
    | none => rfl
    | some p => cases p; rfl
  obtain ⟨c, vr, ld, hsh⟩ := loadBytes_shape (ldPre ws false false va) (bs.map (fun x => (t, x))) ws a
  obtain ⟨i1, i2, i3⟩ := loadBytes_vals (ldPre ws false false va) t (Mach.fwdView ms a t) bs ws a hF
  rw [hsh] at i1 i2 i3
  simp only [loadRun, hsh]
  rw [ldPre_emb hR] at i1 i2 i3
  simp only [hne, if_false] at i1 i2
  refine ⟨?_, hR.vwOld, hR.vrNew, hR.vwNew, ?_, ?_, hR.regv, fun a' ha' k hk => ⟨?_, hR.word a' ha' k hk |>.2⟩,
    ?_, hR.res, hR.rmw, hR.ifl, hR.ifr, hR.ifv⟩
  · simp only [Mach.loadPost]; rw [i1, hR.vrOld]
  · simp only [Mach.loadPost, hR.vcap]
  · simp only [Mach.loadPost]; rw [i2, hR.ldv]
  · have := i3 ((a' + k : Nat) : Int)
    simp only [coh] at this ⊢
    rw [this, hbs]
    simp only [Mach.loadPost]
    have hw := (hR.word a' ha' k hk).1
    simp only [coh] at hw
    by_cases he : a' = a
    · subst he; rw [if_pos ((word_split ha ha hk).2 rfl), if_pos rfl, hw]
    · rw [if_neg (fun h => he ((word_split ha ha' hk).1 h)), if_neg he, hw]
  · simp only [Bool.false_eq_true, if_false]; exact hR.vrel

theorem storeBytes_shape : ∀ (n : Nat) (ws : PState) (b : Int) (ts fv : Nat),
    ∃ c f, storeBytes ws b n ts fv = { ws with wCoh := c, wFwd := f }
  | 0, ws, _, _, _ => ⟨ws.wCoh, ws.wFwd, rfl⟩
  | n + 1, ws, b, ts, fv => by
    obtain ⟨c, f, h⟩ := storeBytes_shape n
      { ws with wCoh := insert ws.wCoh b (max (coh ws b) ts), wFwd := insert ws.wFwd b (ts, fv) } (b + 1) ts fv
    exact ⟨c, f, by simp only [storeBytes]; rw [h]⟩

theorem relWs_store (P : MProg) {ms : Mach.MSt} {ws : PState} (hR : RelWs P ms ws) {a va fv ts : Nat}
    (ha : a % P.sz = 0) :
    RelWs P (Mach.storePost ms va fv a ts) (acqPost (storeRun ws false va fv (a : Int) P.sz ts) false ts) := by
  obtain ⟨j1, j2, -⟩ := storeBytes_spec P.sz ws (a : Int) ts fv
  obtain ⟨c, f, hsh⟩ := storeBytes_shape P.sz ws (a : Int) ts fv
  rw [hsh] at j1 j2
  simp only [acqPost, storeRun, hsh, Bool.false_eq_true, if_false]
  refine ⟨hR.vrOld, ?_, hR.vrNew, hR.vwNew, ?_, hR.ldv, hR.regv, fun a' ha' k hk => ⟨?_, ?_⟩,
    hR.vrel, hR.res, hR.rmw, hR.ifl, hR.ifr, hR.ifv⟩
  · simp only [Mach.storePost, hR.vwOld]
  · simp only [Mach.storePost, hR.vcap]
  · have := j1 ((a' + k : Nat) : Int)
    simp only [coh] at this ⊢
    rw [this]
    have hw := (hR.word a' ha' k hk).1
    simp only [coh] at hw
    simp only [Mach.storePost]
    by_cases he : a' = a
    · subst he; rw [if_pos ((word_split ha ha hk).2 rfl), if_pos rfl, hw]
    · rw [if_neg (fun h => he ((word_split ha ha' hk).1 h)), if_neg he, hw]
  · have := j2 ((a' + k : Nat) : Int)
    simp only at this ⊢
    rw [this]
    simp only [Mach.storePost]
    by_cases he : a' = a
    · subst he; rw [if_pos ((word_split ha ha hk).2 rfl), if_pos rfl]
    · rw [if_neg (fun h => he ((word_split ha ha' hk).1 h)), if_neg he, (hR.word a' ha' k hk).2]

theorem relWs_fence {P : MProg} {ms : Mach.MSt} {ws : PState} (hR : RelWs P ms ws) (pr pw sr sw : Bool) :
    RelWs P (Mach.fencePost ms pr pw sr sw) (fencePost ws pr pw sr sw) := by
  refine ⟨hR.vrOld, hR.vwOld, ?_, ?_, hR.vcap, hR.ldv, hR.regv, hR.word, hR.vrel, hR.res, hR.rmw, hR.ifl, hR.ifr,
    hR.ifv⟩ <;> simp only [fencePost, Mach.fencePost, hR.vrOld, hR.vwOld, hR.vrNew, hR.vwNew]

theorem relWs_regW {P : MProg} {ms : Mach.MSt} {ws : PState} (hR : RelWs P ms ws) (rd : Nat) (srcs : List Mach.MSrc) :
    RelWs P { ms with regv := fun r => if r = rd then Mach.srcsView ms srcs else ms.regv r }
      { ws with wRegv := insert ws.wRegv rd (srcsView ws (embSs srcs)) } := by
  refine ⟨hR.vrOld, hR.vwOld, hR.vrNew, hR.vwNew, hR.vcap, hR.ldv, fun r => ?_, hR.word, hR.vrel, hR.res, hR.rmw,
    hR.ifl, hR.ifr, hR.ifv⟩
  simp only [Weak.Prom.regv]
  by_cases h : r = rd
  · subst h; rw [lookupInsert, if_pos rfl, srcsView_emb hR]; rfl
  · rw [lookupInsertNe (Ne.symm h), if_neg h]; exact hR.regv r

theorem relWs_ctrl {P : MProg} {ms : Mach.MSt} {ws : PState} (hR : RelWs P ms ws) (srcs : List Mach.MSrc) :
    RelWs P { ms with vcap := max (Mach.srcsView ms srcs) ms.vcap }
      { ws with wVcap := max (srcsView ws (embSs srcs)) ws.wVcap } :=
  ⟨hR.vrOld, hR.vwOld, hR.vrNew, hR.vwNew, by simp only [srcsView_emb hR, hR.vcap], hR.ldv, hR.regv, hR.word,
    hR.vrel, hR.res, hR.rmw, hR.ifl, hR.ifr, hR.ifv⟩

theorem relWs_instr {P : MProg} {ms : Mach.MSt} {ws : PState} (hR : RelWs P ms ws) :
    RelWs P { ms with ldv := 0 } { ws with wLdv := 0, wRmw := none, wIfv := 0 } :=
  ⟨hR.vrOld, hR.vwOld, hR.vrNew, hR.vwNew, hR.vcap, rfl, hR.regv, hR.word, hR.vrel, hR.res, rfl, hR.ifl, hR.ifr,
    rfl⟩

/-! ## 5. The read rule -/

/-- Is the answer `t` at word `a` the hart's own latest store (Machine.lean `fwdHit`, :294, on a word)?  Only the
proof of `loadOk_iff` needs it: the mini `loadOk` has no forwarding case (`writesIn_window`). -/
def fwdHitW (ws : Mach.MSt) (a t : Nat) : Bool :=
  match ws.fwd a with
  | some (tf, _) => t == tf
  | none => false

theorem fwdHit_emb {P : MProg} {ms : Mach.MSt} {ws : PState} (hR : RelWs P ms ws) {a k : Nat} (ha : a % P.sz = 0)
    (hk : k < P.sz) (t : Nat) : fwdHit ws ((a + k : Nat) : Int) t = fwdHitW ms a t := by
  unfold fwdHit fwdHitW
  rw [(hR.word a ha k hk).2]
  cases ms.fwd a with
  | none => rfl
  | some p => cases p; rfl

/-- THE SAME WINDOW (P1 gate fix 6): on one word, Machine.lean's forwarded floor `vpre ⊔ coh` and its common floor
`(vpre ⊔ t) ⊔ coh` give the same window `(t, _]`, so the mini `loadOk` writes neither case. -/
theorem writesIn_window (log : List Mach.MMsg) (b : Bool) (a t vpre c : Nat) :
    Mach.writesIn log a t (max (if b then vpre else max vpre t) c) ↔ Mach.writesIn log a t (max vpre c) := by
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte]
    unfold Mach.writesIn
    constructor <;> rintro ⟨u, h1, h2, h3⟩ <;> exact ⟨u, h1, by omega, h3⟩
  · simp only [↓reduceIte]

/-- THE READ RULE ON A WORD: machine v2's `loadOk` of an untorn word answer is the mini `loadOk`. -/
theorem loadOk_iff (P : MProg) (hwf : Mach.progWf P) (cond : Weak.Prom.Ref.OC) {mlog : List Mach.MMsg}
    (hg : ∀ m ∈ mlog, goodM P m) {ms : Mach.MSt} {ws : PState} (hR : RelWs P ms ws) {a v : Nat}
    (ha : a % P.sz = 0) (hv : v < Mach.wordW P) (vpre t : Nat) :
    loadOk (testImg (P.toTest cond)) (mlog.map (embMsg P)) ws vpre (a : Int) ((wordB P v).map (fun x => (t, x))) ↔
      Mach.loadOk P mlog ms vpre a t v := by
  have hsz := hwf.1
  have hlen : (wordB P v).length = P.sz := wordB_len.2 hv
  have hne : wordB P v ≠ [] := wordB_ne_nil hsz v
  have hnf : nonFwdMax ws (a : Int) ((wordB P v).map (fun x => (t, x))) = if fwdHitW ms a t then 0 else t :=
    bytesMax_uni _ t _ (wordB P v) a hne (fun k hk => by rw [fwdHit_emb hR ha (by omega)])
  have hfl : ∀ k, k < P.sz →
      max (if fwdHit ws ((a + k : Nat) : Int) t then vpre
        else max vpre (nonFwdMax ws (a : Int) ((wordB P v).map (fun x => (t, x))))) (coh ws ((a + k : Nat) : Int)) =
      max (if fwdHitW ms a t then vpre else max vpre t) (ms.coh a) := by
    intro k hk
    rw [fwdHit_emb hR ha hk, hnf, (hR.word a ha k hk).1]
    split <;> simp
  unfold loadOk Mach.loadOk
  rw [bytesAll_map]
  constructor
  · intro h
    have hk : ∀ k (hk : k < P.sz), (Mach.memv P mlog t a).bind (fun w => (toBytes w P.sz)[k]?) =
        some ((wordB P v)[k]'(by omega)) ∧
        ¬ Mach.writesIn mlog a t (max vpre (ms.coh a)) := by
      intro k hk
      obtain ⟨h1, h2⟩ := h k (by omega)
      rw [memByte_word P hwf cond hg ha hk] at h1
      refine ⟨h1, ?_⟩
      rcases h2 with h2 | h2
      · rw [hfl k hk, writesIn_word P hg ha hk, writesIn_window] at h2; exact h2
      · obtain ⟨ti, hti, -⟩ := h2; exact absurd hti (noInval_emb P mlog ti _)
    refine ⟨?_, (hk 0 hsz).2⟩
    cases hm : Mach.memv P mlog t a with
    | none => have := (hk 0 hsz).1; rw [hm] at this; cases this
    | some w =>
      congr 1
      have hw := memv_lt hg hm
      apply toBytes_inj hw hv
      rw [← wordB_lt hv]
      apply List.ext_getElem (by rw [tb_len, hlen])
      intro k h1 h2
      have := (hk k (by rw [tb_len] at h1; exact h1)).1
      rw [hm, Option.bind_some, List.getElem?_eq_getElem h1] at this
      exact Option.some.inj this
  · rintro ⟨h1, h2⟩ k hk
    rw [hlen] at hk
    refine ⟨?_, .inl ?_⟩
    · rw [memByte_word P hwf cond hg ha hk, h1, Option.bind_some, ← wordB_lt hv, List.getElem?_eq_getElem]
    · rw [hfl k hk, writesIn_word P hg ha hk, writesIn_window]; exact h2

/-! ## 6. The memory halves -/

theorem prom_diff {prom : GSet Nat} {mprom : List Nat} (hp : ∀ t, t ∈ prom ↔ t ∈ mprom) (ts : Nat) :
    ∀ t, t ∈ prom \ {ts} ↔ t ∈ mprom.filter (fun t => t != ts) := by
  intro t
  rw [elemOfDifference, elemOfSingleton, hp, List.mem_filter]
  simp

/-- A mini memory step is a machine v2 memory step on the embedded label. -/
theorem mem_fwd (P : MProg) (hwf : Mach.progWf P) (cond : Weak.Prom.Ref.OC) {mlog : List Mach.MMsg} {i : Nat}
    {mprom : List Nat} {ms : Mach.MSt} {ml : Mach.MLab} {ots : Option Nat} {ms' : Mach.MSt} {mprom' : List Nat}
    (hm : Mach.mMem P mlog i mprom ms ml ots ms' mprom') (hlab : labOk P ml) (hg : ∀ m ∈ mlog, goodM P m)
    {prom : GSet Nat} {ws : PState} (hR : RelWs P ms ws) (hp : ∀ t, t ∈ prom ↔ t ∈ mprom) :
    ∃ ws' prom', memStep (testImg (P.toTest cond)) (mlog.map (embMsg P)) i prom ws (embL P ml) ots ws' prom' ∧
      RelWs P ms' ws' ∧ ∀ t, t ∈ prom' ↔ t ∈ mprom' := by
  cases hm with
  | load a t v asrc hok =>
    obtain ⟨ha, hv⟩ := hlab
    have hva := srcsView_emb hR asrc
    have hfull : loadOk (testImg (P.toTest cond)) (mlog.map (embMsg P)) ws
        (ldPre ws false false (srcsView ws (embSs asrc))) (a : Int) ((wordB P v).map (fun x => (t, x))) := by
      rw [hva, ldPre_emb hR, loadOk_iff P hwf cond hg hR ha hv]; exact hok
    refine ⟨_, _, .load prom ws false false (a : Int) _ (embSs asrc) hfull 0 ?_, ?_, hp⟩
    · apply invalCite_zero
      unfold loadOk at hfull
      refine bytesAll_imp (fun x t' _ hx => ?_) _ _ hfull
      rcases hx.2 with h | ⟨ti, hti, -⟩
      · exact h
      · exact absurd hti (noInval_emb P mlog ti x)
    · rw [hva]; exact relWs_load P hwf hR ha _ (wordB_len.2 hv)
  | store a v asrc vsrc ts hts hmsg hcoh hpre =>
    obtain ⟨ha, hv⟩ := hlab
    have hlen := wordB_len.2 hv
    refine ⟨_, _, .store prom ws false false (a : Int) (wordB P v) (embSs asrc) (embSs vsrc) ts ((hp ts).2 hts)
      (by rw [List.getElem?_map, hmsg]; rfl) ?_ ?_, ?_, prom_diff hp ts⟩
    · rw [hlen, cohBelow_iff]
      intro k hk; rw [(hR.word a ha k hk).1]; exact hcoh
    · rw [srcsView_emb hR, srcsView_emb hR, stPre_emb hR]; exact hpre
    · rw [hlen, srcsView_emb hR, srcsView_emb hR]; exact relWs_store P hR ha
  | fence pr pw sr sw => exact ⟨_, _, .fence prom ws pr pw sr sw, relWs_fence hR pr pw sr sw, hp⟩
  | regW rd srcs => exact ⟨_, _, .regW prom ws rd (embSs srcs), relWs_regW hR rd srcs, hp⟩
  | ctrl srcs => exact ⟨_, _, .ctrl prom ws (embSs srcs), relWs_ctrl hR srcs, hp⟩
  | instr => exact ⟨_, _, .instr prom ws, relWs_instr hR, hp⟩

/-- A machine v2 memory step on an embedded label is a mini memory step. -/
theorem mem_bwd (P : MProg) (hwf : Mach.progWf P) (cond : Weak.Prom.Ref.OC) {mlog : List Mach.MMsg} {i : Nat}
    {prom : GSet Nat} {ws : PState} {ml : Mach.MLab} {ots : Option Nat} {ws' : PState} {prom' : GSet Nat}
    (hm : memStep (testImg (P.toTest cond)) (mlog.map (embMsg P)) i prom ws (embL P ml) ots ws' prom')
    (hlab : labOk P ml) (hg : ∀ m ∈ mlog, goodM P m) {mprom : List Nat} {ms : Mach.MSt} (hR : RelWs P ms ws)
    (hp : ∀ t, t ∈ prom ↔ t ∈ mprom) :
    ∃ ms' mprom', Mach.mMem P mlog i mprom ms ml ots ms' mprom' ∧ RelWs P ms' ws' ∧ ∀ t, t ∈ prom' ↔ t ∈ mprom' := by
  cases ml with
  | load a t v asrc =>
    obtain ⟨ha, hv⟩ := hlab
    simp only [embL] at hm
    cases hm with
    | load _ _ _ _ _ hok vi hci =>
      obtain rfl := invalCite_vi0 (noInval_emb P mlog) hci
      have hva := srcsView_emb hR asrc
      rw [hva, ldPre_emb hR, loadOk_iff P hwf cond hg hR ha hv] at hok
      refine ⟨_, _, .load mprom ms a t v asrc hok, ?_, hp⟩
      rw [hva]; exact relWs_load P hwf hR ha _ (wordB_len.2 hv)
  | store a v asrc vsrc =>
    obtain ⟨ha, hv⟩ := hlab
    have hlen := wordB_len.2 hv
    simp only [embL] at hm
    cases hm with
    | store _ _ _ _ _ _ ts hts hmsg hcoh hpre =>
      rw [List.getElem?_map] at hmsg
      obtain ⟨mm, hmm, he⟩ := Option.map_eq_some_iff.1 hmsg
      have hmm' : mm = ⟨a, v, i⟩ := embMsg_inj (P := P) he
      subst hmm'
      rw [hlen, cohBelow_iff] at hcoh
      have hc : ms.coh a < ts := by
        have := hcoh 0 hwf.1; rwa [(hR.word a ha 0 hwf.1).1] at this
      rw [srcsView_emb hR, srcsView_emb hR, stPre_emb hR] at hpre
      refine ⟨_, _, .store mprom ms a v asrc vsrc ts ((hp ts).1 hts) hmm hc hpre, ?_, prom_diff hp ts⟩
      rw [hlen, srcsView_emb hR, srcsView_emb hR]; exact relWs_store P hR ha
  | fence pr pw sr sw =>
    simp only [embL] at hm
    cases hm with
    | fence => exact ⟨_, _, .fence mprom ms pr pw sr sw, relWs_fence hR pr pw sr sw, hp⟩
  | regW rd srcs =>
    simp only [embL] at hm
    cases hm with
    | regW => exact ⟨_, _, .regW mprom ms rd srcs, relWs_regW hR rd srcs, hp⟩
  | ctrl srcs =>
    simp only [embL] at hm
    cases hm with
    | ctrl => exact ⟨_, _, .ctrl mprom ms srcs, relWs_ctrl hR srcs, hp⟩
  | instr =>
    simp only [embL] at hm
    cases hm with
    | instr => exact ⟨_, _, .instr mprom ms, relWs_instr hR, hp⟩

end MiniEq
