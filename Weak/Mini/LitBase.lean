/-
Weak/Mini: **support for the machine-level example lemmas** `mini_lit_*` (mini plan rev 4 §2 L6: "Machine-level
`mini_lit_*` are LEMMAS"; the full stack's template is `Weak/Prom/CoreLitBase.lean`, `CoreKit*.lean`).

* `miniGF` — a concrete functor bundle (invariants, later credits, the hart ghost variable), so the lemmas are
  closed: `mini_adequacy` is applied at `miniGF`.
* `memEv τ` — the memory entries (loads, stores) of a trace; a `Ψ` of the form `Q ∘ memEv` is quiet-stable.
* `adeqMem` — `mini_adequacy` for such `Ψ` over a `miniValidRun`, with its exports in the form the examples use:
  `Q` of every hart's final memory entries, every message is some hart's store entry (partition + wf), every load
  entry reads what it returns (wf).
* View facts of the instruction rules' post-states (`ld_regv`, `st_vwOld`, `fence_*`, …).
Imports: `Weak.Mini.Adeq`, `Weak.Mini.Rules` and iris-lean only.  No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Mini.Adeq
import Weak.Mini.Rules
import Iris.Instances.Lib.WSat
import Iris.Instances.Lib.LaterCredits
import Iris.Algebra.Auth

namespace Weak.Mini.Logic

open Weak.Mini Weak.Mini.Mach
open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode

/-! ## 1. A concrete functor bundle -/

section gf
open Iris COFE Auth HeapView

/-- The functors MiniLogic needs: invariants (0–2), later credits (3), the hart ghost variable (4). -/
noncomputable def miniGF : BundledGFunctors := fun n =>
  match n with
  | 0 => ⟨InvMapF, by infer_instance⟩
  | 1 => ⟨constOF CoPsetDisjL, by infer_instance⟩
  | 2 => ⟨constOF (DisjointLeibnizSet PosSet), by infer_instance⟩
  | 3 => ⟨AuthURF (constOF Credit), by infer_instance⟩
  | 4 => ⟨GhostVarF HSt, by infer_instance⟩
  | _ => ⟨constOF Unit, by infer_instance⟩

instance : WsatGpreS miniGF where
  inv := { τ := 0, transp := by unfold miniGF; rfl }
  enabled := { τ := 1, transp := by unfold miniGF; rfl }
  disabled := { τ := 2, transp := by unfold miniGF; rfl }

instance : LcGpreS miniGF where
  lc_elem := { τ := 3, transp := by unfold miniGF; rfl }

instance : InvGpreS miniGF where
  toWsatGpreS := inferInstance
  toLcGpreS := inferInstance

instance : GhostVarG miniGF HSt where
  elemG := { τ := 4, transp := by unfold miniGF; rfl }

end gf

/-! ## 2. Memory entries -/

/-- The memory entries (loads and stores) of a trace, in order. -/
def memEv (τ : Trace) : Trace := τ.filter (fun e => isMem e.1)

theorem memEv_quiet (τ : Trace) (l : MLab) (o : Option Nat) (hl : isMem l = false) :
    memEv (τ ++ [(l, o)]) = memEv τ := by
  simp [memEv, hl]

theorem memEv_mem (τ : Trace) (l : MLab) (o : Option Nat) (hl : isMem l = true) :
    memEv (τ ++ [(l, o)]) = memEv τ ++ [(l, o)] := by
  simp [memEv, hl]

theorem memEv_qTr (τ : Trace) : ∀ labs : List MLab, (∀ l ∈ labs, isMem l = false) → memEv (qTr τ labs) = memEv τ
  | [], _ => rfl
  | l :: rest, h => by
    rw [qTr_cons, memEv_qTr _ rest (fun l' hl' => h l' (List.mem_cons_of_mem _ hl')),
      memEv_quiet _ _ _ (h l (List.mem_cons_self ..))]

theorem qstable_mem (Q : Trace → Prop) : qstable (fun τ => Q (memEv τ)) :=
  fun τ l hl hq => by simpa [memEv_quiet τ l none hl] using hq

theorem memEv_sub {τ : Trace} {e : MLab × Option Nat} (h : e ∈ memEv τ) : e ∈ τ := (List.mem_filter.1 h).1

theorem mem_memEv {τ : Trace} {e : MLab × Option Nat} (h : e ∈ τ) (hm : isMem e.1 = true) : e ∈ memEv τ :=
  List.mem_filter.2 ⟨h, hm⟩

theorem loadVals_memEv : ∀ τ : Trace, loadVals τ = loadVals (memEv τ)
  | [] => rfl
  | e :: τ => by
    have ih := loadVals_memEv τ
    obtain ⟨l, o⟩ := e
    cases l <;> simp_all [loadVals, memEv, isMem]

/-! ## 3. A0 for memory-entry invariants, over a valid run -/

/-- **`mini_adequacy` for `Ψ h = Q h ∘ memEv`** over a valid run, `Φ = True`.  Exports: `Q h` of every hart's
memory entries; every message of the final log is a store entry of its author (the partition + wf); every load
entry reads the word it returns, every store entry fulfils its own word (wf). -/
theorem adeqMem {P : MProg} {Mm : List MMsg} {r : MRun} (hv : miniValidRun P Mm r) (Qs : Nat → Trace → Prop)
    (hQ0 : ∀ h, Qs h [])
    (hwp : ∀ (h : Nat) (hs : MHart), (mInit P).hs[h]? = some hs → ∀ [InvGS_gen HasLC.hasLC miniGF],
      ⊢@{IProp miniGF} wp P Mm h (fun τ => Qs h (memEv τ)) hs.fr (fun _ => iprop(⌜True⌝))) :
    (∀ h, Qs h (memEv (r.trace h))) ∧
    (∀ k m, Mm[k]? = some m → ∃ asrc vsrc, (.store m.pa m.v asrc vsrc, some (k + 1)) ∈ memEv (r.trace m.tid)) ∧
    (∀ h a t v asrc o, (.load a t v asrc, o) ∈ r.trace h → memv P Mm t a = some v) ∧
    (∀ h a v asrc vsrc o, (.store a v asrc vsrc, o) ∈ r.trace h →
      ∃ ts, o = some ts ∧ 0 < ts ∧ Mm[ts - 1]? = some ⟨a, v, h⟩) := by
  obtain ⟨c, hrun, hnp, rfl⟩ := hv
  obtain ⟨hii, _, hpart, _, hwf⟩ := mini_adequacy (hlc := HasLC.hasLC) (GF := miniGF) hrun hnp
    (fun h τ => Qs h (memEv τ)) (fun _ _ => True) hQ0 hwp
  refine ⟨fun h => ?_, fun k m hm => ?_, fun h a t v asrc o he => ?_, fun h a v asrc vsrc o he => hwf h _ he⟩
  · have := hii h (traceOf h r.evs).length
    rwa [List.take_length] at this
  · have hin := ((hpart m.tid (k + 1)).2 ⟨by omega, m, by simpa using hm, rfl⟩)
    unfold fulfilsOf at hin
    obtain ⟨e, he, het⟩ := List.mem_filterMap.1 hin
    obtain ⟨l, o⟩ := e
    have hw := hwf m.tid _ he
    simp only at het
    subst het
    cases l with
    | store a v asrc vsrc =>
      obtain ⟨ts, hts, _, hM⟩ := hw
      cases hts
      simp only [Nat.add_sub_cancel] at hM
      rw [hm] at hM
      have e := Option.some.inj hM
      have e1 : m.pa = a := by rw [e]
      have e2 : m.v = v := by rw [e]
      rw [e1, e2]
      exact ⟨asrc, vsrc, mem_memEv he rfl⟩
    | load => simp [entryWf] at hw
    | fence => simp [entryWf] at hw
    | regW => simp [entryWf] at hw
    | ctrl => simp [entryWf] at hw
    | instr => simp [entryWf] at hw
  · exact (hwf h _ he).2

theorem obsLoad_mem {r : MRun} {h k : Nat} : r.obsLoad h k = (loadVals (memEv (r.trace h)))[k]? := by
  unfold MRun.obsLoad; rw [loadVals_memEv]

/-! ## 4. Words in the log -/

theorem memv_zero {P : MProg} {M : List MMsg} {a v : Nat} (h : memv P M 0 a = some v) : v = P.img0 a % wordW P := by
  simp only [memv, Option.some.injEq] at h; exact h.symm

theorem memv_succ {P : MProg} {M : List MMsg} {k a v : Nat} (h : memv P M (k + 1) a = some v) :
    ∃ m, M[k]? = some m ∧ m.pa = a ∧ m.v = v := by
  simp only [memv] at h
  split at h
  · next m hm =>
    split at h
    · next he => exact ⟨m, hm, he, Option.some.inj h⟩
    · cases h
  · cases h

theorem writesIn_mono {log : List MMsg} {a lo hi hi' : Nat} (h : writesIn log a lo hi) (hh : hi ≤ hi') :
    writesIn log a lo hi' := by
  obtain ⟨t, h1, h2, m, hm, hpa⟩ := h
  exact ⟨t, h1, by omega, m, hm, hpa⟩

theorem writesIn_of {log : List MMsg} {a lo hi k : Nat} {m : MMsg} (hm : log[k]? = some m) (hpa : m.pa = a)
    (h1 : lo < k + 1) (h2 : k + 1 ≤ hi) : writesIn log a lo hi :=
  ⟨k + 1, h1, h2, m, by simpa using hm, hpa⟩

/-! ## 5. Front-end and view facts -/

theorem rd_wr_ne {f : MFront} {pc : Nat} {q : List MLab} {r r' v : Nat} (h : r ≠ r') :
    (MFront.mk pc (f.wr r' v) q).rd r = f.rd r := by
  unfold MFront.rd MFront.wr
  by_cases h0 : r = 0
  · simp [h0]
  · by_cases h0' : r' = 0
    · simp [h0, h0']
    · simp only [h0, h0', if_false]; rw [List.getElem?_set_ne (Ne.symm h)]

theorem srcR_ne {r : Nat} (h : r ≠ 0) : srcR r = [.reg r] := by simp [srcR, h]

theorem srcsView_reg (ws : MSt) {r : Nat} (h : r ≠ 0) : srcsView ws (srcR r) = ws.regv r := by
  rw [srcR_ne h]; simp [srcsView, srcView]

theorem regWL_ne {r : Nat} (srcs : List MSrc) (h : r ≠ 0) : regWL r srcs = [.regW r srcs] := by simp [regWL, h]

/-- (X4)+(X5): after a NON-FORWARDED load into `rd ≠ x0`, the register's view is at least the answer's timestamp;
the load-floor input `vrOld` too; the forward bank is untouched. -/
theorem ld_post {ws : MSt} {va vpre a t rd : Nat} (hf : ws.fwd a = none) (hrd : rd ≠ 0) :
    t ≤ (qWs (loadPost ws va vpre a t) (regWL rd [.ldres] ++ [.instr])).regv rd ∧
    t ≤ (qWs (loadPost ws va vpre a t) (regWL rd [.ldres] ++ [.instr])).vrOld ∧
    (qWs (loadPost ws va vpre a t) (regWL rd [.ldres] ++ [.instr])).fwd = ws.fwd := by
  rw [regWL_ne _ hrd]
  refine ⟨?_, ?_, rfl⟩ <;> simp [qWs, qpost, loadPost, fwdView, hf, srcsView, srcView] <;> omega

/-- FULFIL: after a store at `ts`, `vwOld ≥ ts`; registers and the load-side views are untouched. -/
theorem st_post (ws : MSt) (va fv a ts : Nat) :
    ts ≤ (qWs (storePost ws va fv a ts) [.instr]).vwOld ∧
    (qWs (storePost ws va fv a ts) [.instr]).regv = ws.regv := by
  refine ⟨?_, rfl⟩
  simp only [qWs, List.foldl_cons, List.foldl_nil, qpost, storePost]
  omega

/-- FENCE `w,w` raises the store floor to `vwOld`; FENCE `r,·` raises the load floor to `vrOld`. -/
theorem fence_post (ws : MSt) (pr pw sr sw : Bool) :
    (pw = true → sw = true → ws.vwOld ≤ (qWs ws [.fence pr pw sr sw, .instr]).vwNew) ∧
    (pr = true → sr = true → ws.vrOld ≤ (qWs ws [.fence pr pw sr sw, .instr]).vrNew) ∧
    (qWs ws [.fence pr pw sr sw, .instr]).regv = ws.regv ∧ (qWs ws [.fence pr pw sr sw, .instr]).fwd = ws.fwd := by
  refine ⟨fun h1 h2 => ?_, fun h1 h2 => ?_, rfl, rfl⟩ <;> subst h1 h2 <;> simp [qWs, qpost, fencePost] <;> omega

theorem qpost_fwd (ws : MSt) (l : MLab) : (qpost ws l).fwd = ws.fwd := by cases l <;> rfl

theorem qWs_fwd (ws : MSt) : ∀ labs : List MLab, (qWs ws labs).fwd = ws.fwd
  | [] => rfl
  | l :: rest => by rw [qWs_cons, qWs_fwd _ rest, qpost_fwd]

/-- A load into `rd ≠ x0` keeps an empty forward bank empty. -/
theorem fwdN_ld {ws : MSt} {va vpre b t rd : Nat} (hf : ∀ a, ws.fwd a = none) (hrd : rd ≠ 0) :
    ∀ a, (qWs (loadPost ws va vpre b t) (regWL rd [.ldres] ++ [.instr])).fwd a = none := by
  intro a; rw [(ld_post (hf b) hrd).2.2]; exact hf a

theorem ldPre_ge (ws : MSt) (va : Nat) : ws.vrNew ≤ ldPre ws va := by unfold ldPre; omega

theorem stPre_ge (ws : MSt) (va vd : Nat) : vd ≤ stPre ws va vd ∧ ws.vwNew ≤ stPre ws va vd := by
  unfold stPre; omega

/-! ## 6. Glue -/

theorem prefix2 {α : Type} {l : List α} {a b : α} (h : l <+: [a, b]) : l = [] ∨ l = [a] ∨ l = [a, b] := by
  obtain ⟨t, ht⟩ := h
  match l, t, ht with
  | [], _, _ => exact .inl rfl
  | [x], _, ht => simp at ht; exact .inr (.inl (by rw [ht.1]))
  | [x, y], _, ht => simp at ht; exact .inr (.inr (by rw [ht.1, ht.2.1]))
  | x :: y :: z :: _, _, ht => simp at ht

/-- A load that returned 1 at a word the image holds 0 read a message: some hart's store entry of 1 at that
word, fulfilling the load's timestamp. -/
theorem read_src {P : MProg} {Mm : List MMsg} {r : MRun} {x t : Nat} {asr : List MSrc} {o : Option Nat}
    (hR : ∀ h a t v asrc o, (.load a t v asrc, o) ∈ r.trace h → memv P Mm t a = some v)
    (hW : ∀ k m, Mm[k]? = some m → ∃ asrc vsrc, (.store m.pa m.v asrc vsrc, some (k + 1)) ∈ memEv (r.trace m.tid))
    (himg : P.img0 x % wordW P = 0) {h v : Nat} (hl : (.load x t v asr, o) ∈ r.trace h) (hv : v ≠ 0) :
    ∃ j asrc vsrc, (.store x v asrc vsrc, some t) ∈ memEv (r.trace j) := by
  have hm := hR h x t v asr o hl
  cases t with
  | zero => exact absurd ((memv_zero hm).trans himg) hv
  | succ k =>
    obtain ⟨m, hk, hpa, hmv⟩ := memv_succ hm
    obtain ⟨asrc, vsrc, he⟩ := hW k m hk
    rw [hpa, hmv] at he
    exact ⟨m.tid, asrc, vsrc, he⟩

end Weak.Mini.Logic
