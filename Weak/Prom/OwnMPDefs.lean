/-
Weak/Prom: **G4 target (2), MP with ownership transfer, on track (b): the program and the pure protocol** (stage
S4b; plan rev 7 §4 "Gate G4" (2): `sd x; fence rw,w; sd flag` / `ld flag; fence r,rw; ld x`, "proving that x's
points-to moves").

* The program half `tpStep`: a LABEL-LEVEL front end (one memory label per access, no register bookkeeping): a hart
  program is a list of templates — a plain 1-byte store `st a v`, a plain 1-byte load `ld a` (its answer is recorded
  in `got`), a fence.  Targets: `H0 = [st x 1; fence rw,w; st flag 1]`, `H1 = [ld flag; fence r,rw; ld x]` with
  x = byte 1, flag = byte 2, every image byte 0.  (Width 1 instead of the plan's `sd`/`ld`; the instruction-level
  front end `litStep` is not used here — see PROGRESS-S4b.md.)
* The protocol state of the proof (`mpOk`), kept by the client state interpretation of OwnWp.lean:
  - the DEAD set `D` (plan §4 (b2-none), "unbacked"): messages that can never be fulfilled — every one is still in
    its author's promise set; at the end of a valid run all promise sets are empty, so `D` is empty;
  - x's OWNERSHIP RECORD `(hold, tstart, tstar, v)`: the holder of x's write permission W(x) (plan §4 "Points-to
    (b)"), when its tenure started, the latest x-message a reader with floor ≥ `tstar` returns, its value; every
    later x-message in the log prefix is dead, BACKED (by the holder, appended during its tenure, still pending:
    plan §4 (b2-own) "data promises need write permission"), or a LEFTOVER of the releasing holder H0;
  - flag's RELEASE CELL `f`: the in-place release message whose deposit is in the state interpretation; every
    other flag message in the prefix is dead (plan §4 "releases in place");
  - `bad`: a dead message was read; the final value of H1 satisfies the MP spec or `bad`.
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Prom.OwnWp

namespace Weak.Prom.Own.MP

open MachCSL MachCSL.Stdpp Iris.Std
open Weak (Image Dsrc)
open Weak.Prom Weak.Prom.Nfr Weak.Prom.Own
open PLabel

/-! ## 1. The label-level program half -/

inductive Tpl where
  | st (a : Int) (v : BitVec 8)
  | ld (a : Int)
  | fence (pr pw sr sw : Bool)

structure TP where
  code : List Tpl
  got : List (BitVec 8)

def tpNext (s : TP) (l : PLabel) : Option TP :=
  match s.code, l with
  | .st a v :: c, LStore aq rl b d asrc vsrc =>
      if aq = false ∧ rl = false ∧ b = a ∧ d = [v] ∧ asrc = [] ∧ vsrc = [] then some ⟨c, s.got⟩ else none
  | .ld a :: c, LLoad aq rl b tvs asrc =>
      if aq = false ∧ rl = false ∧ b = a ∧ tvs.length = 1 ∧ asrc = [] then some ⟨c, s.got ++ tvs.map Prod.snd⟩
      else none
  | .fence pr pw sr sw :: c, LFence pr' pw' sr' sw' =>
      if pr' = pr ∧ pw' = pw ∧ sr' = sr ∧ sw' = sw then some ⟨c, s.got⟩ else none
  | _, _ => none

def tpStep (s : TP) (_ : Unit) (l : PLabel) (s' : TP) (_ : Unit) : Prop := tpNext s l = some s'

def tpDone (s : TP) : Option (List (BitVec 8)) := if s.code = [] then some s.got else none

theorem tp_st {a : Int} {v : BitVec 8} {c : List Tpl} {g : List (BitVec 8)} {l : PLabel} {s' : TP}
    (h : tpNext ⟨.st a v :: c, g⟩ l = some s') : l = LStore false false a [v] [] [] ∧ s' = ⟨c, g⟩ := by
  unfold tpNext at h
  cases l <;> simp at h
  obtain ⟨⟨h1, h2, h3, h4, h5, h6⟩, h7⟩ := h
  subst h1 h2 h3 h4 h5 h6 h7
  exact ⟨rfl, rfl⟩

theorem tp_ld {a : Int} {c : List Tpl} {g : List (BitVec 8)} {l : PLabel} {s' : TP}
    (h : tpNext ⟨.ld a :: c, g⟩ l = some s') :
    ∃ t v, l = LLoad false false a [(t, v)] [] ∧ s' = ⟨c, g ++ [v]⟩ := by
  cases l with
  | LLoad aq rl b tvs asrc =>
    unfold tpNext at h
    simp at h
    obtain ⟨⟨h1, h2, h3, h4, h5⟩, h7⟩ := h
    subst h1 h2 h3 h5 h7
    match tvs, h4 with
    | [(t, v)], _ => exact ⟨t, v, rfl, rfl⟩
  | _ => unfold tpNext at h; simp at h

theorem tp_fence {pr pw sr sw : Bool} {c : List Tpl} {g : List (BitVec 8)} {l : PLabel} {s' : TP}
    (h : tpNext ⟨.fence pr pw sr sw :: c, g⟩ l = some s') : l = LFence pr pw sr sw ∧ s' = ⟨c, g⟩ := by
  unfold tpNext at h
  cases l <;> simp at h
  obtain ⟨⟨h1, h2, h3, h4⟩, h7⟩ := h
  subst h1 h2 h3 h4 h7
  exact ⟨rfl, rfl⟩

theorem tp_nil {g : List (BitVec 8)} {l : PLabel} {s' : TP} (h : tpNext ⟨[], g⟩ l = some s') : False := by
  unfold tpNext at h; cases l <;> simp at h

/-- [E-b] The label-level program half never fetches (for `hstepO.fetch`). -/
theorem tp_fetch {s s' : TP} {b : Int} {tvs : List (Nat × BitVec 8)} (h : tpNext s (LIFetch b tvs) = some s') :
    False := by
  rcases s with ⟨_ | ⟨x, c⟩, g⟩
  · unfold tpNext at h; simp at h
  · cases x <;> (unfold tpNext at h; simp at h)

/-! ## 2. The test -/

def X : Int := 1
def F : Int := 2

def mpImg : Image := fun _ => some 0

def h0Code : List Tpl := [.st X 1, .fence true true false true, .st F 1]
def h1Code : List Tpl := [.ld F, .fence true false true true, .ld X]

def mpProgs : List TP := [⟨h0Code, []⟩, ⟨h1Code, []⟩]

/-- THE MP SPEC: if H1 read flag = 1 then it read x = 1. -/
def mpSpec (g : List (BitVec 8)) : Prop := g[0]? = some 1 → g[1]? = some 1

/-! ## 3. Message vocabulary -/

/-- Message `t` (1-based) writes byte `a`. -/
def wrA (M : List PMsg) (t : Nat) (a : Int) : Prop := ∃ m, M[t - 1]? = some m ∧ (m.byteAt a).isSome = true

/-- The author of message `t` (1-based). -/
def au (M : List PMsg) (t : Nat) : Option Nat := (M[t - 1]?).bind PMsg.tid

/-- x's ownership record: holder, tenure start, latest returned x-message, its value. -/
structure XRec where
  hold : Option Nat
  tstart : Nat
  tstar : Nat
  v : BitVec 8
  deriving DecidableEq

/-- THE PROTOCOL STATE of the MP proof (see the header). -/
def mpOk (img : Image) (M : List PMsg) (σ : OSt (List (BitVec 8))) (D : Nat → Prop) (rec : XRec)
    (f : Option Nat) (bad : Bool) : Prop :=
  (∀ a t, t ∈ σ.pr a → 1 ≤ t ∧ t ≤ σ.n ∧ au M t = some a) ∧
  (∀ t, D t → 1 ≤ t ∧ t ≤ σ.n ∧ ∃ a, au M t = some a ∧ t ∈ σ.pr a) ∧
  (bad = true → ∃ t, D t) ∧
  (rec.tstar ≤ σ.n ∧ memByte img M rec.tstar X = some rec.v ∧ rec.tstart ≤ σ.n ∧
    ∀ t, rec.tstar < t → t ≤ σ.n → wrA M t X →
      D t ∨ (rec.hold = au M t ∧ rec.tstart < t ∧ ∃ a, au M t = some a ∧ t ∈ σ.pr a) ∨
      (au M t = some 0 ∧ (∃ r, f = some r ∧ t ≤ r) ∧ t ∈ σ.pr 0)) ∧
  (∀ t, D t → wrA M t X → rec.hold = au M t → rec.tstart < t → rec.hold = some 1 ∨ wrA M t F) ∧
  (∀ t, 1 ≤ t → t ≤ σ.n → wrA M t F → D t ∨ f = some t) ∧
  (∀ r, f = some r → 1 ≤ r ∧ r ≤ σ.n ∧ M[r - 1]? = some ⟨F, [1], some 0, .plain⟩) ∧
  (∀ g, σ.done 1 = some g → mpSpec g ∨ bad = true)

/-! ## 4. Pure facts -/

theorem au_of_take {M : List PMsg} {n t : Nat} {m : PMsg} (h : (M.take n)[t - 1]? = some m) :
    M[t - 1]? = some m ∧ t - 1 < n := by
  rw [List.getElem?_take] at h
  split at h
  · exact ⟨h, by omega⟩
  · cases h

theorem memByte_take {img : Image} {M : List PMsg} {n t : Nat} {a : Int} {v : BitVec 8}
    (h : memByte img (M.take n) t a = some v) : memByte img M t a = some v ∧ t ≤ n := by
  cases t with
  | zero => exact ⟨h, Nat.zero_le _⟩
  | succ k =>
    simp only [memByte] at h ⊢
    rw [List.getElem?_take] at h
    split at h
    · exact ⟨h, by omega⟩
    · cases h

theorem wrA_of_memByte {img : Image} {M : List PMsg} {t : Nat} {a : Int} {v : BitVec 8} (ht : 1 ≤ t)
    (h : memByte img M t a = some v) : wrA M t a := by
  cases t with
  | zero => omega
  | succ k =>
    simp only [memByte] at h
    cases hm : M[k]? with
    | none => rw [hm] at h; cases h
    | some m =>
      rw [hm] at h
      refine ⟨m, by simpa using hm, ?_⟩
      simp only [Option.bind_some] at h
      rw [h]; rfl

theorem memByte_inj {img : Image} {M : List PMsg} {t : Nat} {a : Int} {v v' : BitVec 8}
    (h1 : memByte img M t a = some v) (h2 : memByte img M t a = some v') : v = v' := by
  rw [h1] at h2; cases h2; rfl

theorem byteAt_one_F : (⟨X, [1], some 0, .plain⟩ : PMsg).byteAt F = none := by
  simp [PMsg.byteAt, X, F]

theorem byteAt_F_X : (⟨F, [1], some 0, .plain⟩ : PMsg).byteAt X = none := by
  simp [PMsg.byteAt, X, F]

theorem upd_pr_self (σ : OSt (List (BitVec 8))) (h : Nat) : ({ σ with pr := upd σ.pr h (σ.pr h) } : OSt _) = σ := by
  cases σ; simp only [OSt.mk.injEq, and_true, true_and]; funext j; by_cases e : j = h <;> simp [upd, e]

/-- THE AGENT OBLIGATION, pure part: appending `M[n]` keeps the protocol (an x-message of the holder is backed; any
other x-message and every flag message is dead). -/
theorem mpOk_agent {img : Image} {M : List PMsg} {σ σ' : OSt (List (BitVec 8))} {D : Nat → Prop} {rec : XRec}
    {f : Option Nat} {bad : Bool} (hok : mpOk img M σ D rec f bad)
    (ha : ∃ i, σ.n < M.length ∧ authorAt M σ.n = some i ∧
      σ' = { σ with n := σ.n + 1, pr := upd σ.pr i ({σ.n + 1} ∪ σ.pr i) }) :
    ∃ D', mpOk img M σ' D' rec f bad := by
  obtain ⟨i, hn, hau, rfl⟩ := ha
  obtain ⟨hpr, hD, hbad, ⟨hx1, hx2, hx3, hx4⟩, hdis, hcell, hf, hdone⟩ := hok
  have hau' : au M (σ.n + 1) = some i := by simpa [au, authorAt] using hau
  let dead : Prop := wrA M (σ.n + 1) F ∨ (wrA M (σ.n + 1) X ∧ rec.hold ≠ some i)
  let D' : Nat → Prop := fun t => D t ∨ (t = σ.n + 1 ∧ dead)
  have hpr' : ∀ a t, t ∈ upd σ.pr i ({σ.n + 1} ∪ σ.pr i) a ↔ (t ∈ σ.pr a ∨ (a = i ∧ t = σ.n + 1)) := by
    intro a t
    by_cases e : a = i
    · subst e; simp only [upd_eq, elemOfUnion, elemOfSingleton]; constructor
      · rintro (h | h); exact .inr ⟨by simp, h⟩; exact .inl h
      · rintro (h | ⟨_, h⟩); exact .inr h; exact .inl h
    · simp only [upd_ne _ _ e]; constructor
      · exact .inl
      · rintro (h | ⟨h, _⟩); exact h; exact absurd h e
  refine ⟨D', ?_, ?_, ?_, ⟨by simp only; omega, hx2, by simp only; omega, ?_⟩, ?_, ?_, ?_, hdone⟩
  · intro a t ht
    rcases (hpr' a t).1 ht with ht | ⟨rfl, rfl⟩
    · obtain ⟨u1, u2, u3⟩ := hpr a t ht; exact ⟨u1, by simp only; omega, u3⟩
    · exact ⟨by omega, by simp only; omega, hau'⟩
  · intro t ht
    rcases ht with ht | ⟨rfl, _⟩
    · obtain ⟨u1, u2, a, u3, u4⟩ := hD t ht
      exact ⟨u1, by simp only; omega, a, u3, (hpr' a t).2 (.inl u4)⟩
    · exact ⟨by omega, by simp only; omega, i, hau', (hpr' i _).2 (.inr ⟨rfl, rfl⟩)⟩
  · intro hb; obtain ⟨t, ht⟩ := hbad hb; exact ⟨t, .inl ht⟩
  · intro t h1 h2 h3
    by_cases e : t = σ.n + 1
    · subst e
      by_cases hh : rec.hold = some i
      · by_cases hF : wrA M (σ.n + 1) F
        · exact .inl (.inr ⟨by simp, .inl hF⟩)
        · exact .inr (.inl ⟨by rw [hh, hau'], by omega, i, hau', (hpr' i _).2 (.inr ⟨rfl, rfl⟩)⟩)
      · exact .inl (.inr ⟨by simp, .inr ⟨h3, hh⟩⟩)
    · rcases hx4 t h1 (by simp only at h2; omega) h3 with u | ⟨u1, u2, a, u3, u4⟩ | ⟨u1, u2, u3⟩
      · exact .inl (.inl u)
      · exact .inr (.inl ⟨u1, u2, a, u3, (hpr' a t).2 (.inl u4)⟩)
      · exact .inr (.inr ⟨u1, u2, (hpr' 0 t).2 (.inl u3)⟩)
  · intro t ht h2 h3 h4
    rcases ht with ht | ⟨rfl, hd⟩
    · exact hdis t ht h2 h3 h4
    · rcases hd with hd | ⟨_, hd⟩
      · exact .inr hd
      · rw [hau'] at h3; exact absurd h3 hd
  · intro t h1 h2 h3
    by_cases e : t = σ.n + 1
    · subst e; exact .inl (.inr ⟨by simp, .inl h3⟩)
    · rcases hcell t h1 (by simp only at h2; omega) h3 with u | u
      · exact .inl (.inl u)
      · exact .inr u
  · intro r hr; obtain ⟨u1, u2, u3⟩ := hf r hr; exact ⟨u1, by simp only; omega, u3⟩

/-- THE FINAL EXTRACTION: at the end of a valid run every promise set is empty, so the dead set is empty, `bad` is
false, and H1's value meets the spec. -/
theorem mpOk_final {img : Image} {M : List PMsg} {σ : OSt (List (BitVec 8))} {D : Nat → Prop} {rec : XRec}
    {f : Option Nat} {bad : Bool} (hok : mpOk img M σ D rec f bad) (hpr : ∀ h, σ.pr h = ∅) :
    ∀ g, σ.done 1 = some g → mpSpec g := by
  intro g hg
  obtain ⟨_, hD, hbad, _, _, _, _, hdone⟩ := hok
  rcases hdone g hg with h | h
  · exact h
  · obtain ⟨t, ht⟩ := hbad h
    obtain ⟨_, _, a, _, ha⟩ := hD t ht
    rw [hpr a] at ha
    exact absurd ha notElemOfEmpty

end Weak.Prom.Own.MP

namespace Weak.Prom.Own.MP

open MachCSL MachCSL.Stdpp Iris.Std
open Weak (Image Dsrc)
open Weak.Prom Weak.Prom.Nfr Weak.Prom.Own
open PLabel

/-! ## 5. The hart steps, pure part -/

/-- The world of the test over the final memory `M`. -/
def mpW (M : List PMsg) : OW TP (List (BitVec 8)) := ⟨tpStep, tpDone, mpImg, M⟩

theorem relPr {σ : OSt (List (BitVec 8))} {h : Nat} (hle : ∀ t, t ∈ σ.pr h → t ≤ σ.n) :
    upd σ.pr h (({σ.n + 1} ∪ σ.pr h) \ {σ.n + 1}) = σ.pr := by
  funext j
  by_cases e : j = h
  · subst e
    rw [upd_eq]
    apply setEq.2
    intro t
    rw [elemOfDifference, elemOfUnion, elemOfSingleton]
    constructor
    · rintro ⟨h1 | h1, h2⟩
      · exact absurd h1 h2
      · exact h1
    · intro h1
      exact ⟨.inr h1, fun e => by have := hle t h1; omega⟩
  · rw [upd_ne _ _ e]

theorem take_get {M : List PMsg} {n k : Nat} {m : PMsg} (h : (M.take n)[k]? = some m) : M[k]? = some m := by
  rw [List.getElem?_take] at h; split at h; exact h; cases h

/-- A store after which nothing has been loaded or stored is release-class (its pre-view is ≥ 0). -/
theorem relClass_store0 {ws : PState} (h1 : ws.wVrOld = 0) (h2 : ws.wVwOld = 0) (aq rl : Bool) (a : Int)
    (d : List (BitVec 8)) (asr vsr : List Dsrc) : relClass ws (LStore aq rl a d asr vsr) :=
  ⟨_, rfl, by simp only [wrState, h1, h2]; omega⟩

/-- A plain store directly after `fence rw,w` is release-class (plan §3). -/
theorem relClass_fenceW (ws : PState) (sr : Bool) (a : Int) (d : List (BitVec 8)) :
    relClass (fencePost ws true true sr true) (LStore false false a d [] []) := by
  refine ⟨_, rfl, ?_⟩
  simp only [wrState, stPreA, stPre, fencePost]
  simp only [if_true, if_false, Bool.false_eq_true]
  omega

/-- A FENCE step: no memory effect. -/
theorem hstep_fence {w : OW TP (List (BitVec 8))} {h : Nat} {σ σ' : OSt (List (BitVec 8))} {pr pw sr sw : Bool}
    {c : List Tpl} {g : List (BitVec 8)} {ws ws' : PState} {l : PLabel} {ots : Option Nat} {s' : TP}
    (hw : w.pstep = tpStep) (hs : hstepO w h σ ⟨.fence pr pw sr sw :: c, g⟩ ws l ots s' ws' σ') :
    s' = ⟨c, g⟩ ∧ ots = none ∧ σ' = σ ∧ ws' = fencePost ws pr pw sr sw := by
  cases hs with
  | plain =>
    rename_i pr' _ hp hm
    rw [hw] at hp
    obtain ⟨rfl, rfl⟩ := tp_fence hp
    cases hm
    exact ⟨rfl, rfl, upd_pr_self σ h, rfl⟩
  | fetch => rename_i _ hp; rw [hw] at hp; exact (tp_fetch hp).elim   -- [E-b]
  | rel =>
    rename_i pr' _ _ _ hp hm
    rw [hw] at hp
    obtain ⟨rfl, rfl⟩ := tp_fence hp
    cases hm

/-- A LOAD step (one byte, plain): the answer's message holds the value, nothing writes the byte between the
answer and the load's pre-view, the post-view is above the forwarded view of the answer. -/
theorem hstep_ld {w : OW TP (List (BitVec 8))} {h : Nat} {σ σ' : OSt (List (BitVec 8))} {a : Int}
    {c : List Tpl} {g : List (BitVec 8)} {ws ws' : PState} {l : PLabel} {ots : Option Nat} {s' : TP}
    (hw : w.pstep = tpStep) (hinv : invalFree w.M) (hs : hstepO w h σ ⟨.ld a :: c, g⟩ ws l ots s' ws' σ') :
    ∃ t v, s' = ⟨c, g ++ [v]⟩ ∧ ots = none ∧ σ' = σ ∧ ws' = loadRun ws false false 0 a [(t, v)] ∧
      memByte w.img w.M t a = some v ∧ t ≤ σ.n ∧
      (∀ t0, t < t0 → t0 ≤ ldPre ws false false 0 → t0 ≤ σ.n → ¬ wrA w.M t0 a) ∧
      fwdView ws false a t ≤ ws'.wVrOld := by
  cases hs with
  | plain =>
    rename_i pr' _ hp hm
    rw [hw] at hp
    obtain ⟨t, v, rfl, rfl⟩ := tp_ld hp
    cases hm with
    | load _ _ _ _ _ hok vi hci =>   -- MachFix-R-b5: `vi = 0` (`invalFree`)
      obtain rfl := invalCite_vi0 (noInval_take hinv _) hci
      rw [loadRunV_zero]
      obtain ⟨⟨hmb, hw'⟩, _⟩ := hok
      obtain ⟨hmb', htn⟩ := memByte_take hmb
      refine ⟨t, v, rfl, rfl, upd_pr_self σ h, rfl, hmb', htn, fun t0 h1 h2 h3 hwr => ?_, ?_⟩
      · rcases hw' with hw' | hw'
        · apply hw'
          obtain ⟨m, hm, hb⟩ := hwr
          refine ⟨t0, h1, ?_, m, ?_, hb⟩
          · have e : srcsView ws [] = 0 := rfl
            rw [e]
            have : ldPre ws false false 0 ≤ max (if fwdHit ws a t = true then ldPre ws false false 0
                else max (ldPre ws false false 0) (nonFwdMax ws a [(t, v)])) (coh ws a) := by
              split <;> omega
            omega
          · rw [List.getElem?_take, if_pos (by omega)]; exact hm
        · obtain ⟨ti, hc, _⟩ := hw'
          obtain ⟨m, k, len, hm, hcl, hk, hle1, hle2⟩ := hc
          exact absurd ⟨m, k, len, take_get hm, hcl, hk, hle1, hle2⟩ (hinv ti a)
      · have := (loadRun_keep ws false false (srcsView ws []) a [(t, v)]).2.2.2.2
        exact this.1
  | fetch => rename_i _ hp; rw [hw] at hp; exact (tp_fetch hp).elim   -- [E-b]
  | rel =>
    rename_i pr' _ _ _ hp hm
    rw [hw] at hp
    obtain ⟨t, v, rfl, rfl⟩ := tp_ld hp
    cases hm

end Weak.Prom.Own.MP

namespace Weak.Prom.Own.MP

open MachCSL MachCSL.Stdpp Iris.Std
open Weak (Image Dsrc)
open Weak.Prom Weak.Prom.Nfr Weak.Prom.Own
open PLabel

/-! ## 6. The protocol steps -/

theorem prWf_le {img : Image} {M : List PMsg} {σ : OSt (List (BitVec 8))} {D : Nat → Prop} {rec : XRec}
    {f : Option Nat} {bad : Bool} (hok : mpOk img M σ D rec f bad) (h : Nat) :
    ∀ t, t ∈ σ.pr h → t ≤ σ.n := fun t ht => (hok.1 h t ht).2.1

/-- H0's `st x 1`: the store is its first write, so release-class; it appends its message in place and becomes
x's latest message (`tstar`). -/
theorem h0_st1 {M : List PMsg} {σ σ' : OSt (List (BitVec 8))} {D : Nat → Prop} {bad : Bool} {l : PLabel}
    {ots : Option Nat} {s' : TP} {ws' : PState}
    (hok : mpOk mpImg M σ D ⟨some 0, 0, 0, 0⟩ none bad)
    (hs : hstepO (mpW M) 0 σ ⟨h0Code, []⟩ psInit l ots s' ws' σ') :
    s' = ⟨[.fence true true false true, .st F 1], []⟩ ∧ ∃ ts, ots = some ts ∧
      mpOk mpImg M σ' D ⟨some 0, 0, ts, 1⟩ none bad := by
  cases hs with
  | plain =>
    rename_i pr' hnr hp _
    obtain ⟨rfl, rfl⟩ := tp_st hp
    exact absurd (relClass_store0 rfl rfl _ _ _ _ _ _) hnr
  | fetch => rename_i _ hp; exact (tp_fetch hp).elim   -- [E-b]
  | rel =>
    rename_i pr' hn _ _ hp hm
    obtain ⟨rfl, rfl⟩ := tp_st hp
    cases hm with
    | store _ _ _ _ _ _ _ _ hmsg _ _ =>
    have hM : M[σ.n]? = some ⟨X, [1], some 0, .plain⟩ := by
      have := take_get hmsg; simpa [stClass, mpW] using this
    refine ⟨rfl, σ.n + 1, rfl, ?_⟩
    obtain ⟨hpr, hD, hbad, ⟨hx1, hx2, hx3, hx4⟩, hdis, hcell, hf, hdone⟩ := hok
    have e : upd σ.pr 0 (({σ.n + 1} ∪ σ.pr 0) \ {σ.n + 1}) = σ.pr := relPr (prWf_le ⟨hpr, hD, hbad, ⟨hx1, hx2, hx3, hx4⟩, hdis, hcell, hf, hdone⟩ 0)
    simp only [e]
    refine ⟨fun a t ht => ?_, fun t ht => ?_, hbad, ⟨Nat.le_refl _, ?_, Nat.zero_le _, fun t h1 h2 _ => by (try dsimp only at *); omega⟩,
      hdis, fun t h1 h2 h3 => ?_, fun r hr => (by cases hr), hdone⟩
    · obtain ⟨u1, u2, u3⟩ := hpr a t ht; exact ⟨u1, by (try dsimp only at *); omega, u3⟩
    · obtain ⟨u1, u2, u3⟩ := hD t ht; exact ⟨u1, by (try dsimp only at *); omega, u3⟩
    · simp [memByte, hM, PMsg.byteAt, X]
    · by_cases e2 : t = σ.n + 1
      · subst e2
        obtain ⟨m, hm', hb⟩ := h3
        simp only [Nat.add_sub_cancel] at hm'
        rw [hM] at hm'; cases hm'
        simp [PMsg.byteAt, X, F] at hb
      · rcases hcell t h1 (by (try dsimp only at *); omega) h3 with u | u
        · exact .inl u
        · cases u

/-- H0's `st flag 1` after `fence rw,w`: release-class, appended in place; the DEPOSIT: x's record goes to "no
holder" (its leftover pending x-messages, if any, stay pending of H0), flag's cell records the release. -/
theorem h0_st2 {M : List PMsg} {σ σ' : OSt (List (BitVec 8))} {D : Nat → Prop} {bad : Bool} {l : PLabel}
    {ots : Option Nat} {s' : TP} {ws1 ws' : PState} {tsx : Nat}
    (hok : mpOk mpImg M σ D ⟨some 0, 0, tsx, 1⟩ none bad)
    (hs : hstepO (mpW M) 0 σ ⟨[.st F 1], []⟩ (fencePost ws1 true true false true) l ots s' ws' σ') :
    s' = ⟨[], []⟩ ∧ ∃ r, ots = some r ∧ tsx < r ∧
      mpOk mpImg M σ' D ⟨none, r, tsx, 1⟩ (some r) bad := by
  cases hs with
  | plain =>
    rename_i pr' hnr hp _
    obtain ⟨rfl, rfl⟩ := tp_st hp
    exact absurd (relClass_fenceW ws1 false F [1]) hnr
  | fetch => rename_i _ hp; exact (tp_fetch hp).elim   -- [E-b]
  | rel =>
    rename_i pr' hn _ _ hp hm
    obtain ⟨rfl, rfl⟩ := tp_st hp
    cases hm with
    | store _ _ _ _ _ _ _ _ hmsg _ _ =>
    have hM : M[σ.n]? = some ⟨F, [1], some 0, .plain⟩ := by
      have := take_get hmsg; simpa [stClass, mpW] using this
    obtain ⟨hpr, hD, hbad, ⟨hx1, hx2, hx3, hx4⟩, hdis, hcell, hf, hdone⟩ := hok
    refine ⟨rfl, σ.n + 1, rfl, by (try dsimp only at *); omega, ?_⟩
    have e : upd σ.pr 0 (({σ.n + 1} ∪ σ.pr 0) \ {σ.n + 1}) = σ.pr :=
      relPr (fun t ht => (hpr 0 t ht).2.1)
    simp only [e]
    have hnotX : ¬ wrA M (σ.n + 1) X := by
      rintro ⟨m, hm', hb⟩
      simp only [Nat.add_sub_cancel] at hm'
      rw [hM] at hm'; cases hm'
      simp [PMsg.byteAt, X, F] at hb
    refine ⟨fun a t ht => ?_, fun t ht => ?_, hbad, ⟨by (try dsimp only at *); omega, hx2, Nat.le_refl _, ?_⟩,
      ?_, fun t h1 h2 h3 => ?_, fun r hr => ?_, hdone⟩
    · obtain ⟨u1, u2, u3⟩ := hpr a t ht; exact ⟨u1, by (try dsimp only at *); omega, u3⟩
    · obtain ⟨u1, u2, u3⟩ := hD t ht; exact ⟨u1, by (try dsimp only at *); omega, u3⟩
    · intro t h1 h2 h3
      by_cases e2 : t = σ.n + 1
      · subst e2; exact absurd h3 hnotX
      · rcases hx4 t h1 (by (try dsimp only at *); omega) h3 with u | ⟨u1, _, a, u3, u4⟩ | ⟨_, ⟨r, hr, _⟩, _⟩
        · exact .inl u
        · simp only at u1
          rw [u3] at u1; cases u1
          exact .inr (.inr ⟨u3, ⟨σ.n + 1, rfl, by (try dsimp only at *); omega⟩, u4⟩)
        · cases hr
    · intro t ht _ h3 _
      obtain ⟨_, _, a, u3, _⟩ := hD t ht
      simp only at h3
      rw [u3] at h3; cases h3
    · by_cases e2 : t = σ.n + 1
      · subst e2; exact .inr rfl
      · rcases hcell t h1 (by (try dsimp only at *); omega) h3 with u | u
        · exact .inl u
        · cases u
    · cases hr
      exact ⟨by (try dsimp only at *); omega, Nat.le_refl _, by simpa using hM⟩

/-- H1's CLAIM (the designated claimant takes x's record out of the cell; plan §4 (b2-pull)'s designated
claimant, here for a read-only receiver): no holder → holder H1 with a tenure starting now. -/
theorem h1_claim {img : Image} {M : List PMsg} {σ : OSt (List (BitVec 8))} {D : Nat → Prop} {bad : Bool}
    {r tsx : Nat} {f : Option Nat} (hok : mpOk img M σ D ⟨none, r, tsx, 1⟩ f bad) :
    mpOk img M σ D ⟨some 1, σ.n, tsx, 1⟩ f bad := by
  obtain ⟨hpr, hD, hbad, ⟨hx1, hx2, hx3, hx4⟩, hdis, hcell, hf, hdone⟩ := hok
  refine ⟨hpr, hD, hbad, ⟨hx1, hx2, Nat.le_refl _, fun t h1 h2 h3 => ?_⟩, fun t _ _ _ h4 => by
    simp only at h4; have := (hD t ‹_›).2.1; omega, hcell, hf, hdone⟩
  rcases hx4 t h1 h2 h3 with u | ⟨u1, _, a, u3, _⟩ | u
  · exact .inl u
  · simp only at u1; rw [u3] at u1; cases u1
  · exact .inr (.inr u)

/-- H1's READ OF x as the holder: the latest message (value 1), or a dead / own-pending / leftover message, which
is then marked dead (`bad`). -/
theorem h1_rdx {img : Image} {M : List PMsg} {σ : OSt (List (BitVec 8))} {D : Nat → Prop} {bad : Bool}
    {nc tsx : Nat} {f : Option Nat} (hok : mpOk img M σ D ⟨some 1, nc, tsx, 1⟩ f bad) (htsx : 1 ≤ tsx)
    {t P : Nat} {v : BitVec 8} (hmb : memByte img M t X = some v) (htn : t ≤ σ.n) (hP : tsx ≤ P)
    (hnw : ∀ t0, t < t0 → t0 ≤ P → t0 ≤ σ.n → ¬ wrA M t0 X) :
    v = 1 ∨ ∃ D', mpOk img M σ D' ⟨some 1, nc, tsx, 1⟩ f true := by
  obtain ⟨hpr, hD, hbad, ⟨hx1, hx2, hx3, hx4⟩, hdis, hcell, hf, hdone⟩ := hok
  simp only at hx1 hx2 hx3 hx4 hdis
  have hwx : wrA M tsx X := wrA_of_memByte htsx hx2
  by_cases hlt : t < tsx
  · exact absurd hwx (hnw tsx hlt hP hx1)
  by_cases heq : t = tsx
  · subst heq; exact .inl (memByte_inj hmb hx2)
  have hgt : tsx < t := by omega
  have hwt : wrA M t X := wrA_of_memByte (by omega) hmb
  right
  have key : ∃ a, au M t = some a ∧ t ∈ σ.pr a ∧ (some 1 = au M t → nc < t → True) ∧
      (au M t = some 1 ∨ au M t = some 0 ∨ D t) := by
    rcases hx4 t hgt htn hwt with u | ⟨u1, _, a, u3, u4⟩ | ⟨u1, _, u3⟩
    · obtain ⟨_, _, a, u3, u4⟩ := hD t u; exact ⟨a, u3, u4, fun _ _ => trivial, .inr (.inr u)⟩
    · exact ⟨a, u3, u4, fun _ _ => trivial, .inl u1.symm⟩
    · exact ⟨0, u1, u3, fun _ _ => trivial, .inr (.inl u1)⟩
  obtain ⟨a, ha, hta, _, hcls⟩ := key
  refine ⟨fun t' => D t' ∨ t' = t, hpr, fun t' ht' => ?_, fun _ => ⟨t, .inr rfl⟩,
    ⟨hx1, hx2, hx3, fun t' h1 h2 h3 => ?_⟩, fun t' ht' h2 h3 h4 => ?_, fun t' h1 h2 h3 => ?_, hf,
    fun g hg => .inr rfl⟩
  · rcases ht' with ht' | rfl
    · exact hD t' ht'
    · exact ⟨by omega, htn, a, ha, hta⟩
  · rcases hx4 t' h1 h2 h3 with u | u | u
    · exact .inl (.inl u)
    · exact .inr (.inl u)
    · exact .inr (.inr u)
  · rcases ht' with ht' | rfl
    · exact .inl rfl
    · exact .inl rfl
  · rcases hcell t' h1 h2 h3 with u | u
    · exact .inl (.inl u)
    · exact .inr u

/-- H1's FINAL VALUE: recorded with the spec or `bad`. -/
theorem h1_fin {img : Image} {M : List PMsg} {σ : OSt (List (BitVec 8))} {D : Nat → Prop} {rec : XRec}
    {f : Option Nat} {bad : Bool} {g : List (BitVec 8)} (hok : mpOk img M σ D rec f bad)
    (hg : mpSpec g ∨ bad = true) : mpOk img M { σ with done := upd σ.done 1 (some g) } D rec f bad := by
  obtain ⟨hpr, hD, hbad, hx, hdis, hcell, hf, hdone⟩ := hok
  refine ⟨hpr, hD, hbad, hx, hdis, hcell, hf, fun g' hg' => ?_⟩
  simp only [upd_eq] at hg'
  cases hg'
  exact hg

/-- H0's FINAL VALUE: nothing to record. -/
theorem h0_fin {img : Image} {M : List PMsg} {σ : OSt (List (BitVec 8))} {D : Nat → Prop} {rec : XRec}
    {f : Option Nat} {bad : Bool} {g : List (BitVec 8)} (hok : mpOk img M σ D rec f bad) :
    mpOk img M { σ with done := upd σ.done 0 (some g) } D rec f bad := by
  obtain ⟨hpr, hD, hbad, hx, hdis, hcell, hf, hdone⟩ := hok
  refine ⟨hpr, hD, hbad, hx, hdis, hcell, hf, fun g' hg' => ?_⟩
  simp only [upd_ne _ _ (show (1 : Nat) ≠ 0 by omega)] at hg'
  exact hdone g' hg'

end Weak.Prom.Own.MP
