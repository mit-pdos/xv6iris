/-
Weak/Prom: **support for the `lit_` theorems of the core** (stage S2; plan rev 7 §2 "The LB trio, derived step by
step from A0's exports", §8 S2).

* `pfGF` — a concrete `BundledGFunctors` with the invariant, later-credit and `GhostVarG HSt` functors, so the
  `lit_` theorems are CLOSED (no `GF` parameter): A0 is applied at `pfGF`.
* Program-half lemmas for the litmus front end `Weak.Prom.Mach.Cert.litStep` (MachCert.lean §1, the label table of
  MachLitmus.lean): which label each instruction kind emits first (`litNext_*`).  These are facts about the program
  TEXT's semantics used inside each hart's wp proof (plan §2: "At every step the wp knows the label the step
  emits"); none is used after adequacy.
* `ΨLB x y n` — the trace invariant (P0)–(P4) of plan §2 for an LB-shaped hart that loads `n` bytes at `x` and
  stores `n` bytes at `y`, with its step lemmas (`psiLB_*`).
* `lb_contra` — THE CONTRADICTION of plan §2 steps 1–6, from A0's exports (ii), (iii), (v) ONLY: `ΨLB` of both harts'
  final traces (X1), the partition (X2), `traceWf` (X3), the outcome through `run.obsLoad`.
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Prom.CoreAdeq
import Weak.Prom.CoreRules
import Weak.Prom.MachCert
import Iris.Instances.Lib.WSat
import Iris.Instances.Lib.LaterCredits
import Iris.Algebra.Auth

namespace Weak.Prom.PF

open MachCSL MachCSL.Stdpp Iris.Std
open Weak (Image Dsrc)
open Weak.Prom Weak.Prom.Mach Weak.Prom.Mach.Cert
open Weak.Prom.Ref (Instr Test two64 aluOp brEval amoOp sext byteList bytesVal)
open PLabel

/-! ## 1. A concrete functor bundle -/

section gf
open Iris COFE Auth HeapView

/-- The functors the core needs: invariants (0–2), later credits (3), the hart ghost variable (4). -/
noncomputable def pfGF : BundledGFunctors := fun n =>
  match n with
  | 0 => ⟨InvMapF, by infer_instance⟩
  | 1 => ⟨constOF CoPsetDisjL, by infer_instance⟩
  | 2 => ⟨constOF (DisjointLeibnizSet PosSet), by infer_instance⟩
  | 3 => ⟨AuthURF (constOF Credit), by infer_instance⟩
  | 4 => ⟨GhostVarF HSt, by infer_instance⟩
  | _ => ⟨constOF Unit, by infer_instance⟩

instance : WsatGpreS pfGF where
  inv := { τ := 0, transp := by unfold pfGF; rfl }
  enabled := { τ := 1, transp := by unfold pfGF; rfl }
  disabled := { τ := 2, transp := by unfold pfGF; rfl }

instance : LcGpreS pfGF where
  lc_elem := { τ := 3, transp := by unfold pfGF; rfl }

instance : InvGpreS pfGF where
  toWsatGpreS := inferInstance
  toLcGpreS := inferInstance

instance : GhostVarG pfGF HSt where
  elemG := { τ := 4, transp := by unfold pfGF; rfl }

end gf

/-! ## 2. The litmus program half -/

/-- A litmus hart has reached its value when its program is done (MachCert.lean `allDone`). -/
def litDone (s : LP) : Option Unit := if s.q = [] ∧ s.prog.length ≤ s.pc then some () else none

theorem anyFab_lit {s : LP} {l : PLabel} {s' : LP} : anyFab litStep s () l s' () ↔ litNext s l = some s' :=
  ⟨fun ⟨_, _, h⟩ => h, fun h => ⟨(), (), h⟩⟩

theorem litDone_q {s : LP} (h : s.q ≠ []) : litDone s = none := by
  unfold litDone; simp [h]

theorem litDone_pc {s : LP} (h : s.pc < s.prog.length) : litDone s = none := by
  unfold litDone; split
  · next hh => omega
  · rfl

theorem litNext_q {s : LP} {l0 : PLabel} {rest : List PLabel} (hq : s.q = l0 :: rest) {l : PLabel} {s' : LP}
    (h : litNext s l = some s') : l = l0 ∧ s' = { s with q := rest } := by
  unfold litNext at h
  rw [hq] at h
  simp only at h
  split at h
  · next he => cases h; exact ⟨he, rfl⟩
  · cases h

theorem litNext_end {s : LP} (hq : s.q = []) (hp : s.prog[s.pc]? = none) (l : PLabel) : litNext s l = none := by
  unfold litNext; rw [hq]; simp only; rw [hp]

theorem litNext_load {s : LP} {sz rd rs1 off : Nat} {sgn : Bool} (hq : s.q = [])
    (hp : s.prog[s.pc]? = some (.load sz sgn rd rs1 off)) (ha : aligned ((s.rd rs1 + off) % two64) sz = true)
    {l : PLabel} {s' : LP} (h : litNext s l = some s') :
    ∃ tvs, l = LLoad false false (((s.rd rs1 + off) % two64 : Nat) : Int) tvs (srcR rs1) ∧
      s' = { s with regs := s.wr rd (if sgn then sext sz (ofBytes (tvs.map Prod.snd)) else ofBytes (tvs.map Prod.snd)),
                    pc := s.pc + 1, q := regWL rd [.DLdRes] ++ [LInstr] } ∧ tvs.length = sz := by
  unfold litNext at h
  rw [hq] at h
  simp only [hp, instrNext, ha, Bool.not_true, Bool.false_eq_true, if_false] at h
  split at h
  · next aq rl b tvs asrc =>
    split at h
    · next hc =>
      obtain ⟨h1, h2, h3, h4, h5⟩ := hc
      subst h1 h2 h3 h5
      cases h
      exact ⟨tvs, rfl, rfl, h4⟩
    · cases h
  · cases h

theorem litNext_store {s : LP} {sz rs2 rs1 off : Nat} (hq : s.q = [])
    (hp : s.prog[s.pc]? = some (.store sz rs2 rs1 off)) (ha : aligned ((s.rd rs1 + off) % two64) sz = true)
    {l : PLabel} {s' : LP} (h : litNext s l = some s') :
    l = LStore false false (((s.rd rs1 + off) % two64 : Nat) : Int) (toBytes (s.rd rs2) sz) (srcR rs1) (srcR rs2) ∧
      s' = { s with pc := s.pc + 1, q := [LInstr] } := by
  unfold litNext at h
  rw [hq] at h
  simp only [hp, instrNext, ha, Bool.not_true, Bool.false_eq_true, if_false] at h
  split at h
  · next aq rl b data asrc vsrc =>
    split at h
    · next hc =>
      obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hc
      subst h1 h2 h3 h4 h5 h6
      cases h
      exact ⟨rfl, rfl⟩
    · cases h
  · cases h

theorem litNext_alu {s : LP} {op : Weak.Prom.Ref.Alu} {rd rs1 rs2 : Nat} (hq : s.q = [])
    (hp : s.prog[s.pc]? = some (.alu op rd rs1 rs2)) (hrd : rd ≠ 0) {l : PLabel} {s' : LP}
    (h : litNext s l = some s') :
    l = LRegW rd (srcR rs1 ++ srcR rs2) ∧
      s' = { s with regs := s.wr rd (aluOp op (s.rd rs1) (s.rd rs2)), pc := s.pc + 1, q := [LInstr] } := by
  unfold litNext at h
  rw [hq] at h
  simp only [hp, instrNext, go1, regWL, hrd, if_false, List.singleton_append] at h
  split at h
  · next he => cases h; exact ⟨he, rfl⟩
  · cases h

theorem litNext_alui {s : LP} {op : Weak.Prom.Ref.Alu} {rd rs1 imm : Nat} (hq : s.q = [])
    (hp : s.prog[s.pc]? = some (.alui op rd rs1 imm)) (hrd : rd ≠ 0) {l : PLabel} {s' : LP}
    (h : litNext s l = some s') :
    l = LRegW rd (srcR rs1) ∧
      s' = { s with regs := s.wr rd (aluOp op (s.rd rs1) imm), pc := s.pc + 1, q := [LInstr] } := by
  unfold litNext at h
  rw [hq] at h
  simp only [hp, instrNext, go1, regWL, hrd, if_false, List.singleton_append] at h
  split at h
  · next he => cases h; exact ⟨he, rfl⟩
  · cases h

theorem litNext_br {s : LP} {c : Weak.Prom.Ref.BrC} {rs1 rs2 tgt : Nat} (hq : s.q = [])
    (hp : s.prog[s.pc]? = some (.br c rs1 rs2 tgt)) (ht : ¬ (tgt ≤ s.pc ∨ s.prog.length < tgt)) {l : PLabel}
    {s' : LP} (h : litNext s l = some s') :
    l = LCtrl (srcR rs1 ++ srcR rs2) ∧
      s' = { s with regs := s.regs, pc := if brEval c (s.rd rs1) (s.rd rs2) then tgt else s.pc + 1,
                    q := [LInstr] } := by
  unfold litNext at h
  rw [hq] at h
  simp only [hp, instrNext, go1, ht, if_false] at h
  split at h
  · next he => cases h; exact ⟨he, rfl⟩
  · cases h

theorem litNext_lr {s : LP} {sz rd rs1 : Nat} (hq : s.q = [])
    (hp : s.prog[s.pc]? = some (.lr sz false false rd rs1)) (ha : aligned (s.rd rs1) sz = true)
    {l : PLabel} {s' : LP} (h : litNext s l = some s') :
    ∃ tvs, l = LExLoad false false ((s.rd rs1 : Nat) : Int) tvs (srcR rs1) ∧
      s' = { s with regs := s.wr rd (sext sz (ofBytes (tvs.map Prod.snd))), pc := s.pc + 1,
                    q := regWL rd [.DLdRes] ++ [LInstr] } ∧ tvs.length = sz := by
  unfold litNext at h
  rw [hq] at h
  simp only [hp, instrNext, ha, Bool.not_true, Bool.false_eq_true, if_false] at h
  split at h
  · next aq rl b tvs asrc =>
    split at h
    · next hc =>
      obtain ⟨h1, h2, h3, h4, h5⟩ := hc
      subst h1 h3 h5
      simp only [Bool.and_false] at h2
      subst h2
      cases h
      exact ⟨tvs, rfl, rfl, h4⟩
    · cases h
  · cases h

theorem litNext_sc {s : LP} {sz rd rs2 rs1 : Nat} (hq : s.q = [])
    (hp : s.prog[s.pc]? = some (.sc sz false false rd rs2 rs1)) (ha : aligned (s.rd rs1) sz = true)
    {l : PLabel} {s' : LP} (h : litNext s l = some s') :
    (l = LExStore false false ((s.rd rs1 : Nat) : Int) (toBytes (s.rd rs2) sz) (srcR rs1) (srcR rs2) ∧
      s' = { s with regs := s.wr rd 0, pc := s.pc + 1, q := regWL rd [.DLdRes] ++ [LExFail, LInstr] }) ∨
    (l = LExFail ∧ s' = { s with regs := s.wr rd 1, pc := s.pc + 1, q := regWL rd [] ++ [LExFail, LInstr] }) := by
  unfold litNext at h
  rw [hq] at h
  simp only [hp, instrNext, ha, Bool.not_true, Bool.false_eq_true, if_false] at h
  split at h
  · next aq rl b data asrc vsrc =>
    split at h
    · next hc =>
      obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hc
      simp only [Bool.and_false] at h1
      subst h1 h2 h3 h4 h5 h6
      cases h
      exact .inl ⟨rfl, rfl⟩
    · cases h
  · cases h; exact .inr ⟨rfl, rfl⟩
  · cases h

theorem toBytes_length (v sz : Nat) : (toBytes v sz).length = sz := by
  simp [toBytes, byteList]

/-! ## 3. The trace invariant (P0)–(P4) of plan §2 -/

/-- (P0) of one entry: an entry carrying a timestamp is an `st` (a plain-store label). -/
def P0c (e : PEv) : Prop := ∀ t, e.2 = some t → ∃ aq rl base data asrc vsrc, e.1 = LStore aq rl base data asrc vsrc

/-- (P1) of one entry: every `st` entry's footprint is the `n` bytes at `y`. -/
def P1c (y : Int) (n : Nat) (e : PEv) : Prop :=
  ∀ aq rl base data asrc vsrc, e.1 = LStore aq rl base data asrc vsrc → base = y ∧ data.length = n

/-- (P3) of a pair: an `ld` entry's byte-0 source is below every timestamped entry's timestamp. -/
def P3c (e e' : PEv) : Prop :=
  ∀ aq rl base tv tvs asrc t, e.1 = LLoad aq rl base (tv :: tvs) asrc → e'.2 = some t → tv.1 < t

/-- (P4) of one entry: every load-like entry is an `ld` at `x` of `n` bytes. -/
def P4c (x : Int) (n : Nat) (e : PEv) : Prop :=
  ∀ tvs, loadLikeTvs e.1 = some tvs → (∃ asrc, e.1 = LLoad false false x tvs asrc) ∧ tvs.length = n

/-- **Ψ of plan §2 (LB+data+data / LB+fakedep)**, for a hart loading `n` bytes at `x` and storing `n` at `y`:
(P0) every timestamped entry is an `st`; (P1) every `st` is at `y` with `n` bytes; (P2) at most one `st`;
(P3) every `ld`'s byte-0 source is below every `st`'s timestamp; (P4) every load-like entry is an `ld` at `x`. -/
def ΨLB (x y : Int) (n : Nat) (τ : Trace) : Prop :=
  (∀ e ∈ τ, P0c e) ∧ (∀ e ∈ τ, P1c y n e) ∧ (τ.filter (fun e => e.2.isSome)).length ≤ 1 ∧
  (∀ e ∈ τ, ∀ e' ∈ τ, P3c e e') ∧ (∀ e ∈ τ, P4c x n e)

theorem psiLB_nil (x y : Int) (n : Nat) : ΨLB x y n [] := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp

/-- A "quiet" entry (no answers, no write, no timestamp: `regw`, `instr`, `ctrl`, …) keeps Ψ. -/
theorem psiLB_quiet {x y : Int} {n : Nat} {τ : Trace} (h : ΨLB x y n τ) (l : PLabel)
    (hr : loadLikeTvs l = none) (hs : ∀ aq rl base data asrc vsrc, l ≠ LStore aq rl base data asrc vsrc) :
    ΨLB x y n (τ ++ [(l, none)]) := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := h
  have hq3 : ∀ e : PEv, P3c (l, none) e := by
    intro e aq rl base tv tvs asrc t he; simp only at he; subst he; cases hr
  have hq3' : ∀ e : PEv, P3c e (l, none) := by
    intro e aq rl base tv tvs asrc t _ ht; cases ht
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro e he; rcases List.mem_append.1 he with he | he
    · exact h0 e he
    · rw [List.mem_singleton] at he; subst he; intro t ht; cases ht
  · intro e he; rcases List.mem_append.1 he with he | he
    · exact h1 e he
    · rw [List.mem_singleton] at he; subst he; intro aq rl base data asrc vsrc hl; exact absurd hl (hs _ _ _ _ _ _)
  · simpa using h2
  · intro e he e' he'
    rcases List.mem_append.1 he with he | he
    · rcases List.mem_append.1 he' with he' | he'
      · exact h3 e he e' he'
      · rw [List.mem_singleton] at he'; subst he'; exact hq3' e
    · rw [List.mem_singleton] at he; subst he; exact hq3 e'
  · intro e he; rcases List.mem_append.1 he with he | he
    · exact h4 e he
    · rw [List.mem_singleton] at he; subst he; intro tvs ht; simp only at ht; rw [hr] at ht; cases ht

/-- The hart's load (on a trace with no timestamped entry yet) keeps Ψ. -/
theorem psiLB_load {x y : Int} {n : Nat} {τ : Trace} (h : ΨLB x y n τ) (hnt : ∀ e ∈ τ, e.2 = none)
    (tvs : List (Nat × BitVec 8)) (asrc : List Dsrc) (hn : tvs.length = n) :
    ΨLB x y n (τ ++ [(LLoad false false x tvs asrc, none)]) := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro e he; rcases List.mem_append.1 he with he | he
    · exact h0 e he
    · rw [List.mem_singleton] at he; subst he; intro t ht; cases ht
  · intro e he; rcases List.mem_append.1 he with he | he
    · exact h1 e he
    · rw [List.mem_singleton] at he; subst he; intro aq rl base data asrc vsrc hl; cases hl
  · simpa using h2
  · intro e he e' he' aq rl base tv tvs' asrc' t hl ht
    rcases List.mem_append.1 he' with he' | he'
    · rw [hnt e' he'] at ht; cases ht
    · rw [List.mem_singleton] at he'; subst he'; cases ht
  · intro e he; rcases List.mem_append.1 he with he | he
    · exact h4 e he
    · rw [List.mem_singleton] at he; subst he; intro tvs' ht
      simp only [loadLikeTvs, Option.some.injEq] at ht; subst ht
      exact ⟨⟨asrc, rfl⟩, hn⟩

/-- The hart's one store (on a trace with no timestamped entry yet, above every load's byte-0 source) keeps Ψ. -/
theorem psiLB_store {x y : Int} {n : Nat} {τ : Trace} (h : ΨLB x y n τ) (hnt : ∀ e ∈ τ, e.2 = none)
    (aq rl : Bool) (data : List (BitVec 8)) (asrc vsrc : List Dsrc) (ts : Nat) (hn : data.length = n)
    (hlt : ∀ e ∈ τ, ∀ aq rl base tv tvs asrc, e.1 = LLoad aq rl base (tv :: tvs) asrc → tv.1 < ts) :
    ΨLB x y n (τ ++ [(LStore aq rl y data asrc vsrc, some ts)]) := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro e he; rcases List.mem_append.1 he with he | he
    · exact h0 e he
    · rw [List.mem_singleton] at he; subst he; intro t _; exact ⟨_, _, _, _, _, _, rfl⟩
  · intro e he; rcases List.mem_append.1 he with he | he
    · exact h1 e he
    · rw [List.mem_singleton] at he; subst he; intro aq' rl' base' data' asrc' vsrc' hl
      simp only [LStore.injEq] at hl
      obtain ⟨_, _, rfl, rfl, _, _⟩ := hl
      exact ⟨rfl, hn⟩
  · have : τ.filter (fun e => e.2.isSome) = [] := by
      rw [List.filter_eq_nil_iff]; intro e he; simp [hnt e he]
    simp [this]
  · intro e he e' he' aq' rl' base tv tvs asrc' t hl ht
    rcases List.mem_append.1 he with he | he
    · rcases List.mem_append.1 he' with he' | he'
      · rw [hnt e' he'] at ht; cases ht
      · rw [List.mem_singleton] at he'; subst he'; cases ht; exact hlt e he _ _ _ _ _ _ hl
    · rw [List.mem_singleton] at he; subst he; cases hl
  · intro e he; rcases List.mem_append.1 he with he | he
    · exact h4 e he
    · rw [List.mem_singleton] at he; subst he; intro tvs ht; cases ht

/-! ## 3b. The trace invariant of the LB+lrsc hart (row 5) -/

theorem loadsOf_append (τ τ' : Trace) : loadsOf (τ ++ τ') = loadsOf τ ++ loadsOf τ' := by
  unfold loadsOf; rw [List.filterMap_append]

/-- (Q0) a timestamped entry is an `st` or an `exst`. -/
def Q0c (e : PEv) : Prop := ∀ t, e.2 = some t →
  (∃ aq rl base data asrc vsrc, e.1 = LStore aq rl base data asrc vsrc) ∨
  (∃ aq rl base data asrc vsrc, e.1 = LExStore aq rl base data asrc vsrc)

/-- (Q1) every `st` is the 8 bytes at `z`, every `exst` the 8 bytes at `y`. -/
def Q1c (y z : Int) (e : PEv) : Prop :=
  (∀ aq rl base data asrc vsrc, e.1 = LStore aq rl base data asrc vsrc → base = z ∧ data.length = 8) ∧
  (∀ aq rl base data asrc vsrc, e.1 = LExStore aq rl base data asrc vsrc → base = y ∧ data.length = 8)

/-- (Q3) every `ld`'s byte-0 source is below the timestamp of every `st` whose byte 0 is 0. -/
def Q3c (e e' : PEv) : Prop :=
  ∀ aq rl base tv tvs asrc aq' rl' base' data asrc' vsrc' t, e.1 = LLoad aq rl base (tv :: tvs) asrc →
    e'.1 = LStore aq' rl' base' data asrc' vsrc' → data[0]? = some 0 → e'.2 = some t → tv.1 < t

/-- (Q4) the 0th load-like entry is an 8-byte `ld` at `x`. -/
def Q4 (x : Int) (τ : Trace) : Prop :=
  ∀ tvs, (loadsOf τ).head? = some tvs → (∃ e ∈ τ, ∃ asrc, e.1 = LLoad false false x tvs asrc) ∧ tvs.length = 8

/-- **Ψ of the LB+lrsc hart** (row 5, H0 `ld a0,(x); lr a1,(y); sc a2,a0,(y); sd a2,(z)`). -/
def ΨLS (x y z : Int) (τ : Trace) : Prop :=
  (∀ e ∈ τ, Q0c e) ∧ (∀ e ∈ τ, Q1c y z e) ∧ (∀ e ∈ τ, ∀ e' ∈ τ, Q3c e e') ∧ Q4 x τ

theorem psiLS_nil (x y z : Int) : ΨLS x y z [] := ⟨by simp, by simp, by simp, fun tvs h => by cases h⟩

theorem mem_snoc {τ : Trace} {e e' : PEv} (h : e' ∈ τ ++ [e]) : e' ∈ τ ∨ e' = e := by
  rcases List.mem_append.1 h with h | h
  · exact .inl h
  · exact .inr (List.mem_singleton.1 h)

/-- A quiet entry keeps ΨLS. -/
theorem psiLS_quiet {x y z : Int} {τ : Trace} (h : ΨLS x y z τ) (l : PLabel) (hr : loadLikeTvs l = none)
    (hs : ∀ aq rl base data asrc vsrc, l ≠ LStore aq rl base data asrc vsrc)
    (hx : ∀ aq rl base data asrc vsrc, l ≠ LExStore aq rl base data asrc vsrc) :
    ΨLS x y z (τ ++ [(l, none)]) := by
  obtain ⟨h0, h1, h3, h4⟩ := h
  refine ⟨fun e he => ?_, fun e he => ?_, fun e he e' he' => ?_, fun tvs ht => ?_⟩
  · rcases mem_snoc he with he | rfl
    · exact h0 e he
    · intro t ht; cases ht
  · rcases mem_snoc he with he | rfl
    · exact h1 e he
    · exact ⟨fun _ _ _ _ _ _ hl => absurd hl (hs _ _ _ _ _ _), fun _ _ _ _ _ _ hl => absurd hl (hx _ _ _ _ _ _)⟩
  · intro aq rl base tv tvs asrc aq' rl' base' data asrc' vsrc' t hl hst hd ht
    rcases mem_snoc he with he | rfl
    · rcases mem_snoc he' with he' | rfl
      · exact h3 e he e' he' _ _ _ _ _ _ _ _ _ _ _ _ _ hl hst hd ht
      · cases ht
    · simp only at hl; subst hl; cases hr
  · rw [loadsOf_append] at ht
    have hn : loadsOf [(l, none)] = [] := by simp [loadsOf, hr]
    rw [hn, List.append_nil] at ht
    obtain ⟨⟨e, he, ha⟩, hl⟩ := h4 tvs ht
    exact ⟨⟨e, List.mem_append_left _ he, ha⟩, hl⟩

/-- The first load, an 8-byte `ld` at `x`, on a trace with no load-like entry and no `st`. -/
theorem psiLS_ld {x y z : Int} {τ : Trace} (h : ΨLS x y z τ) (hnl : loadsOf τ = [])
    (hns : ∀ e ∈ τ, ∀ aq rl base data asrc vsrc, e.1 ≠ LStore aq rl base data asrc vsrc)
    (tvs : List (Nat × BitVec 8)) (asrc : List Dsrc) (hn : tvs.length = 8) :
    ΨLS x y z (τ ++ [(LLoad false false x tvs asrc, none)]) := by
  obtain ⟨h0, h1, h3, _⟩ := h
  refine ⟨fun e he => ?_, fun e he => ?_, fun e he e' he' => ?_, fun tvs' ht => ?_⟩
  · rcases mem_snoc he with he | rfl
    · exact h0 e he
    · intro t ht; cases ht
  · rcases mem_snoc he with he | rfl
    · exact h1 e he
    · exact ⟨fun _ _ _ _ _ _ hl => (by cases hl), fun _ _ _ _ _ _ hl => (by cases hl)⟩
  · intro aq rl base tv tvs'' asrc' aq' rl' base' data asrc'' vsrc' t hl hst hd ht
    rcases mem_snoc he' with he' | rfl
    · exact absurd hst (hns e' he' _ _ _ _ _ _)
    · cases hst
  · rw [loadsOf_append, hnl] at ht
    simp only [loadsOf, List.filterMap_cons, List.filterMap_nil, loadLikeTvs, List.nil_append,
      List.head?_cons, Option.some.injEq] at ht
    subst ht
    exact ⟨⟨_, List.mem_append_right _ (List.mem_singleton_self _), asrc, rfl⟩, hn⟩

/-- A load-like entry after the first (here the LR) keeps ΨLS. -/
theorem psiLS_lr {x y z : Int} {τ : Trace} (h : ΨLS x y z τ) (hnl : loadsOf τ ≠ []) (aq rl : Bool) (base : Int)
    (tvs : List (Nat × BitVec 8)) (asrc : List Dsrc) :
    ΨLS x y z (τ ++ [(LExLoad aq rl base tvs asrc, none)]) := by
  obtain ⟨h0, h1, h3, h4⟩ := h
  refine ⟨fun e he => ?_, fun e he => ?_, fun e he e' he' => ?_, fun tvs' ht => ?_⟩
  · rcases mem_snoc he with he | rfl
    · exact h0 e he
    · intro t ht; cases ht
  · rcases mem_snoc he with he | rfl
    · exact h1 e he
    · exact ⟨fun _ _ _ _ _ _ hl => (by cases hl), fun _ _ _ _ _ _ hl => (by cases hl)⟩
  · intro aq₁ rl₁ base₁ tv tvs'' asrc' aq' rl' base' data asrc'' vsrc' t hl hst hd ht
    rcases mem_snoc he with he | rfl
    · rcases mem_snoc he' with he' | rfl
      · exact h3 e he e' he' _ _ _ _ _ _ _ _ _ _ _ _ _ hl hst hd ht
      · cases ht
    · cases hl
  · rw [loadsOf_append] at ht
    obtain ⟨a, rest, has⟩ : ∃ a rest, loadsOf τ = a :: rest := by
      cases hq : loadsOf τ with
      | nil => exact absurd hq hnl
      | cons a rest => exact ⟨a, rest, rfl⟩
    rw [has] at ht
    simp only [List.cons_append, List.head?_cons] at ht
    obtain ⟨⟨e, he, ha⟩, hl⟩ := h4 tvs' (by rw [has]; exact ht)
    exact ⟨⟨e, List.mem_append_left _ he, ha⟩, hl⟩

/-- The successful SC (an 8-byte `exst` at `y`) keeps ΨLS. -/
theorem psiLS_exst {x y z : Int} {τ : Trace} (h : ΨLS x y z τ) (aq rl : Bool) (data : List (BitVec 8))
    (asrc vsrc : List Dsrc) (ts : Nat) (hn : data.length = 8) :
    ΨLS x y z (τ ++ [(LExStore aq rl y data asrc vsrc, some ts)]) := by
  obtain ⟨h0, h1, h3, h4⟩ := h
  refine ⟨fun e he => ?_, fun e he => ?_, fun e he e' he' => ?_, fun tvs' ht => ?_⟩
  · rcases mem_snoc he with he | rfl
    · exact h0 e he
    · intro t _; exact .inr ⟨_, _, _, _, _, _, rfl⟩
  · rcases mem_snoc he with he | rfl
    · exact h1 e he
    · refine ⟨fun _ _ _ _ _ _ hl => (by cases hl), fun aq' rl' base' data' asrc' vsrc' hl => ?_⟩
      simp only [LExStore.injEq] at hl
      obtain ⟨_, _, rfl, rfl, _, _⟩ := hl
      exact ⟨rfl, hn⟩
  · intro aq₁ rl₁ base₁ tv tvs'' asrc' aq' rl' base' data' asrc'' vsrc' t hl hst hd ht
    rcases mem_snoc he with he | rfl
    · rcases mem_snoc he' with he' | rfl
      · exact h3 e he e' he' _ _ _ _ _ _ _ _ _ _ _ _ _ hl hst hd ht
      · cases hst
    · cases hl
  · rw [loadsOf_append] at ht
    have hn' : loadsOf [(LExStore aq rl y data asrc vsrc, some ts)] = [] := rfl
    rw [hn', List.append_nil] at ht
    obtain ⟨⟨e, he, ha⟩, hl⟩ := h4 tvs' ht
    exact ⟨⟨e, List.mem_append_left _ he, ha⟩, hl⟩

/-- The `sd` (8 bytes at `z`) keeps ΨLS when, if its byte 0 is 0, it is above every `ld`'s byte-0 source. -/
theorem psiLS_st {x y z : Int} {τ : Trace} (h : ΨLS x y z τ) (aq rl : Bool) (data : List (BitVec 8))
    (asrc vsrc : List Dsrc) (ts : Nat) (hn : data.length = 8)
    (hlt : data[0]? = some 0 → ∀ e ∈ τ, ∀ aq rl base tv tvs asrc, e.1 = LLoad aq rl base (tv :: tvs) asrc →
      tv.1 < ts) :
    ΨLS x y z (τ ++ [(LStore aq rl z data asrc vsrc, some ts)]) := by
  obtain ⟨h0, h1, h3, h4⟩ := h
  refine ⟨fun e he => ?_, fun e he => ?_, fun e he e' he' => ?_, fun tvs' ht => ?_⟩
  · rcases mem_snoc he with he | rfl
    · exact h0 e he
    · intro t _; exact .inl ⟨_, _, _, _, _, _, rfl⟩
  · rcases mem_snoc he with he | rfl
    · exact h1 e he
    · refine ⟨fun aq' rl' base' data' asrc' vsrc' hl => ?_, fun _ _ _ _ _ _ hl => by cases hl⟩
      simp only [LStore.injEq] at hl
      obtain ⟨_, _, rfl, rfl, _, _⟩ := hl
      exact ⟨rfl, hn⟩
  · intro aq₁ rl₁ base₁ tv tvs'' asrc' aq' rl' base' data' asrc'' vsrc' t hl hst hd ht
    rcases mem_snoc he with he | rfl
    · rcases mem_snoc he' with he' | rfl
      · exact h3 e he e' he' _ _ _ _ _ _ _ _ _ _ _ _ _ hl hst hd ht
      · simp only [LStore.injEq] at hst
        obtain ⟨_, _, _, rfl, _, _⟩ := hst
        cases ht
        exact hlt hd e he _ _ _ _ _ _ hl
    · cases hl
  · rw [loadsOf_append] at ht
    have hn' : loadsOf [(LStore aq rl z data asrc vsrc, some ts)] = [] := rfl
    rw [hn', List.append_nil] at ht
    obtain ⟨⟨e, he, ha⟩, hl⟩ := h4 tvs' ht
    exact ⟨⟨e, List.mem_append_left _ he, ha⟩, hl⟩

/-! ## 4. The contradiction from A0's exports (plan §2 steps 1–6) -/

section contra

variable {P D : Type}

theorem obsOf_one {tv : Nat × BitVec 8} {r : List (Nat × BitVec 8)} (h : obsOf (tv :: r) = 1) : tv.2.toNat = 1 := by
  simp only [obsOf, List.foldr_cons] at h
  have := tv.2.isLt
  omega

/-- One side of the LB contradiction (plan §2 steps 1–3): hart `a`'s 0th load-like entry returned 1, so it is an
`ld x` (P4) whose byte-0 source `s` is a real message (traceWf, the image holds 0 at `x`), fulfilled (partition) by
a hart whose `st` entry has timestamp `s` (P0); not `a` (P1: `a` stores only at `y`, disjoint from `x`), hence `b`. -/
theorem lb_side {run : PFRun P D} {M : List PMsg} {img : Image} {x y : Int} {a b : Nat}
    (himg : run.cfg.pcImg = img) (hx0 : img x = some 0)
    (hyx : ∀ m : PMsg, m.pa = y → m.data.length = 4 → m.byteAt x = none)
    (hΨa : ΨLB x y 4 (run.trace a)) (hother : ∀ h, h ≠ a → h ≠ b → run.trace h = [])
    (hpart : ∀ t, 1 ≤ t → t ≤ M.length → exU (fun h => t ∈ run.fulfils h ∧ tidAt M t = some h))
    (hwf : run.traceWf M) (hobs : run.obsLoad a 0 = some 1) :
    ∃ e ∈ run.trace a, ∃ tv tvs asrc, e.1 = LLoad false false x (tv :: tvs) asrc ∧
      ∃ e' ∈ run.trace b, e'.2 = some tv.1 := by
  obtain ⟨tvs, htvs, hval⟩ := Option.map_eq_some_iff.1 hobs
  obtain ⟨e, he, hel⟩ := List.mem_filterMap.1 (List.mem_of_getElem? htvs)
  obtain ⟨⟨asrc, hl⟩, hlen⟩ := hΨa.2.2.2.2 e he tvs hel
  obtain ⟨tv, rest, rfl⟩ : ∃ tv rest, tvs = tv :: rest := by
    cases tvs with
    | nil => cases hlen
    | cons tv rest => exact ⟨tv, rest, rfl⟩
  have hv1 := obsOf_one hval
  -- (X3): the byte is the memory's
  have hrd := (hwf a e he).1 x (tv :: rest) (by rw [hl]; rfl)
  rw [himg] at hrd
  have hb0 : memByte img M tv.1 x = some tv.2 := hrd.1
  -- the source is not the image
  obtain ⟨k, hk⟩ : ∃ k, tv.1 = k + 1 := by
    cases h0 : tv.1 with
    | zero =>
      rw [h0] at hb0; simp only [memByte] at hb0; rw [hx0] at hb0
      have h00 := Option.some.inj hb0
      rw [← h00] at hv1
      exact absurd hv1 (by decide)
    | succ k => exact ⟨k, rfl⟩
  rw [hk] at hb0
  simp only [memByte] at hb0
  obtain ⟨m, hm, hmb⟩ := Option.bind_eq_some_iff.1 hb0
  have hkl : k < M.length := (List.getElem?_eq_some_iff.1 hm).1
  -- (X2): the partition
  obtain ⟨h, ⟨hin, _⟩, _⟩ := hpart (k + 1) (by omega) (by omega)
  unfold PFRun.fulfils fulfilsOf at hin
  obtain ⟨e', he', het⟩ := List.mem_filterMap.1 hin
  refine ⟨e, he, tv, rest, asrc, hl, ?_⟩
  by_cases hha : h = a
  · -- (P0), (P1) of `a` and traceWf: `a`'s store is at `y`, which does not cover `x`
    subst hha
    exfalso
    obtain ⟨aq, rl, base, data, asrc', vsrc', hst⟩ := hΨa.1 e' he' _ het
    obtain ⟨hby, hdl⟩ := hΨa.2.1 e' he' _ _ _ _ _ _ hst
    have hw := (hwf h e' he').2
    rw [hst, het] at hw
    simp only [labelWrite] at hw
    obtain ⟨m', hm', hpa, hdata, _⟩ := hw
    simp only [Nat.add_sub_cancel] at hm'
    rw [hm] at hm'; cases hm'
    rw [hyx m (by rw [hpa, hby]) (by rw [hdata, hdl])] at hmb
    cases hmb
  · by_cases hhb : h = b
    · subst hhb; exact ⟨e', he', by rw [het, hk]⟩
    · have hnil := hother h hha hhb
      unfold PFRun.trace at hnil
      rw [hnil] at he'; cases he'

/-- **THE LB CONTRADICTION** (plan §2 steps 1–6) from A0's exports (ii), (iii), (v) only: if both harts' final
traces satisfy Ψ (for hart 0 at `x`/`y`, hart 1 at `y`/`x`), no other hart has a trace, and both 0th loads
returned 1, then `s0 < t0 = s1 < t1 = s0`. -/
theorem lb_contra {run : PFRun P D} {M : List PMsg} {img : Image} {x y : Int}
    (himg : run.cfg.pcImg = img) (hx0 : img x = some 0) (hy0 : img y = some 0)
    (hyx : ∀ m : PMsg, m.pa = y → m.data.length = 4 → m.byteAt x = none)
    (hxy : ∀ m : PMsg, m.pa = x → m.data.length = 4 → m.byteAt y = none)
    (hΨ0 : ΨLB x y 4 (run.trace 0)) (hΨ1 : ΨLB y x 4 (run.trace 1)) (hn : ∀ h, 2 ≤ h → run.trace h = [])
    (hpart : ∀ t, 1 ≤ t → t ≤ M.length → exU (fun h => t ∈ run.fulfils h ∧ tidAt M t = some h))
    (hwf : run.traceWf M) : ¬ (run.obsLoad 0 0 = some 1 ∧ run.obsLoad 1 0 = some 1) := by
  rintro ⟨ho0, ho1⟩
  obtain ⟨e0, he0, tv0, r0, a0, hl0, e1', he1', ht1'⟩ := lb_side (b := 1) himg hx0 hyx hΨ0
    (fun h h0 h1 => hn h (by omega)) hpart hwf ho0
  obtain ⟨e1, he1, tv1, r1, a1, hl1, e0', he0', ht0'⟩ := lb_side (b := 0) himg hy0 hxy hΨ1
    (fun h h0 h1 => hn h (by omega)) hpart hwf ho1
  -- (P3) of both harts
  have h01 := hΨ0.2.2.2.1 e0 he0 e0' he0' _ _ _ _ _ _ _ hl0 ht0'
  have h10 := hΨ1.2.2.2.1 e1 he1 e1' he1' _ _ _ _ _ _ _ hl1 ht1'
  omega

theorem obsOf_zero {tv : Nat × BitVec 8} {r : List (Nat × BitVec 8)} (h : obsOf (tv :: r) = 0) :
    tv.2.toNat = 0 := by
  simp only [obsOf, List.foldr_cons] at h
  omega

/-- The 0th load-like entry of a trace, if its value is `v`, is the head of `loadsOf`. -/
theorem obsLoad_head {run : PFRun P D} {h v : Nat} (hobs : run.obsLoad h 0 = some v) :
    ∃ tvs, (loadsOf (run.trace h)).head? = some tvs ∧ obsOf tvs = v := by
  obtain ⟨tvs, htvs, hval⟩ := Option.map_eq_some_iff.1 hobs
  refine ⟨tvs, ?_, hval⟩
  cases hq : loadsOf (run.trace h) with
  | nil => unfold PFRun.obsLoad at hobs; rw [hq] at htvs; cases htvs
  | cons a rest => rw [hq] at htvs; simpa using htvs

/-- A byte the image does not hold is a message's byte: its source is a timestamp `k + 1` of `M`. -/
theorem src_msg {img : Image} {M : List PMsg} {t : Nat} {a : Int} {v b : BitVec 8} (hb : memByte img M t a = some v)
    (hi : img a = some b) (hne : v ≠ b) : ∃ k m, t = k + 1 ∧ M[k]? = some m ∧ m.byteAt a = some v := by
  cases t with
  | zero => simp only [memByte] at hb; rw [hi] at hb; exact absurd (Option.some.inj hb).symm hne
  | succ k =>
    simp only [memByte] at hb
    obtain ⟨m, hm, hmb⟩ := Option.bind_eq_some_iff.1 hb
    exact ⟨k, m, rfl, hm, hmb⟩

/-- The trace entry of the fulfil of `k + 1` (partition + `traceWf`'s write clause): some hart `h` has an entry with
timestamp `k + 1`; if it is a write label, the message is the label's. -/
theorem fulfil_entry {run : PFRun P D} {M : List PMsg} {k : Nat} {m : PMsg} (hm : M[k]? = some m)
    (hpart : ∀ t, 1 ≤ t → t ≤ M.length → exU (fun h => t ∈ run.fulfils h ∧ tidAt M t = some h)) :
    ∃ h, ∃ e ∈ run.trace h, e.2 = some (k + 1) := by
  have hkl : k < M.length := (List.getElem?_eq_some_iff.1 hm).1
  obtain ⟨h, ⟨hin, _⟩, _⟩ := hpart (k + 1) (by omega) (by omega)
  unfold PFRun.fulfils fulfilsOf at hin
  obtain ⟨e', he', het⟩ := List.mem_filterMap.1 hin
  exact ⟨h, e', he', het⟩

theorem write_msg {run : PFRun P D} {M : List PMsg} {h : Nat} {e : PEv} (hwf : run.traceWf M)
    (he : e ∈ run.trace h) {ts : Nat} (het : e.2 = some ts) {base : Int} {data : List (BitVec 8)}
    (hw : labelWrite e.1 = some (base, data)) :
    ∃ m, M[ts - 1]? = some m ∧ m.pa = base ∧ m.data = data := by
  have := (hwf h e he).2
  rw [hw, het] at this
  obtain ⟨m, h1, h2, h3, _⟩ := this
  exact ⟨m, h1, h2, h3⟩

/-- **THE LB+lrsc CONTRADICTION** (row 5): H0 `ld a0,(x); lr a1,(y); sc a2,a0,(y); sd a2,(z)` with ΨLS,
H1 `ld a3,(z); sd a3,(x)` with ΨLB z x 8; the image holds 1 at `x` and `z`.  If H0's 0th load and H1's 0th load
both return 0: H0's load read H1's store (`s0 = t1`), H1's load read H0's `sd z` whose byte 0 is 0 (`s1 = tz`),
(Q3) `s0 < tz`, (P3) `s1 < t1`. -/
theorem lrsc_contra {run : PFRun P D} {M : List PMsg} {img : Image} {x y z : Int}
    (himg : run.cfg.pcImg = img) (hx1 : img x = some 1) (hz1 : img z = some 1)
    (hYX : ∀ m : PMsg, m.pa = y → m.byteAt x = none) (hZX : ∀ m : PMsg, m.pa = z → m.byteAt x = none)
    (hXZ : ∀ m : PMsg, m.pa = x → m.data.length = 8 → m.byteAt z = none)
    (hYZ : ∀ m : PMsg, m.pa = y → m.data.length = 8 → m.byteAt z = none)
    (hZZ : ∀ m : PMsg, m.pa = z → m.byteAt z = m.data[0]?)
    (hΨ0 : ΨLS x y z (run.trace 0)) (hΨ1 : ΨLB z x 8 (run.trace 1)) (hn : ∀ h, 2 ≤ h → run.trace h = [])
    (hpart : ∀ t, 1 ≤ t → t ≤ M.length → exU (fun h => t ∈ run.fulfils h ∧ tidAt M t = some h))
    (hwf : run.traceWf M) : ¬ (run.obsLoad 0 0 = some 0 ∧ run.obsLoad 1 0 = some 0) := by
  rintro ⟨ho0, ho1⟩
  rw [← himg] at hx1 hz1
  have hdom : ∀ h, ∀ e ∈ run.trace h, h = 0 ∨ h = 1 := by
    intro h e he
    by_cases h2 : 2 ≤ h
    · rw [hn h h2] at he; cases he
    · omega
  -- H0's 0th load: an `ld x` whose byte 0 (s0, 0) is H1's store
  obtain ⟨tvs0, hh0, hv0⟩ := obsLoad_head ho0
  obtain ⟨⟨e0, he0, a0, hl0⟩, hlen0⟩ := hΨ0.2.2.2 tvs0 hh0
  obtain ⟨tv0, r0, rfl⟩ : ∃ tv r, tvs0 = tv :: r := by
    cases tvs0 with
    | nil => cases hlen0
    | cons tv r => exact ⟨tv, r, rfl⟩
  have hb0 := ((hwf 0 e0 he0).1 x (tv0 :: r0) (by rw [hl0]; rfl)).1
  obtain ⟨k0, m0, hk0, hm0, hmb0⟩ := src_msg hb0 hx1 (by
    intro he; have := obsOf_zero hv0; rw [he] at this; exact absurd this (by decide))
  obtain ⟨h0, e0', he0', het0⟩ := fulfil_entry hm0 hpart
  have hh01 : h0 = 1 := by
    rcases hdom h0 e0' he0' with rfl | rfl
    · exfalso
      rcases hΨ0.1 e0' he0' _ het0 with ⟨aq, rl, base, data, asrc, vsrc, hst⟩ | ⟨aq, rl, base, data, asrc, vsrc, hst⟩
      · obtain ⟨hb, _⟩ := (hΨ0.2.1 e0' he0').1 _ _ _ _ _ _ hst
        obtain ⟨m, hm, hpa, _⟩ := write_msg hwf he0' het0 (by rw [hst]; rfl)
        simp only [Nat.add_sub_cancel] at hm; rw [hm0] at hm; cases hm
        rw [hZX m0 (by rw [hpa, hb])] at hmb0; cases hmb0
      · obtain ⟨hb, _⟩ := (hΨ0.2.1 e0' he0').2 _ _ _ _ _ _ hst
        obtain ⟨m, hm, hpa, _⟩ := write_msg hwf he0' het0 (by rw [hst]; rfl)
        simp only [Nat.add_sub_cancel] at hm; rw [hm0] at hm; cases hm
        rw [hYX m0 (by rw [hpa, hb])] at hmb0; cases hmb0
    · rfl
  subst hh01
  -- H1's 0th load: an `ld z` whose byte 0 (s1, 0) is H0's `sd z` with byte 0 = 0
  obtain ⟨tvs1, hh1, hv1⟩ := obsLoad_head ho1
  obtain ⟨e1, he1, hl1⟩ : ∃ e ∈ run.trace 1, loadLikeTvs e.1 = some tvs1 := by
    cases hq : loadsOf (run.trace 1) with
    | nil => rw [hq] at hh1; cases hh1
    | cons a rest =>
      rw [hq] at hh1; simp only [List.head?_cons, Option.some.injEq] at hh1; subst hh1
      have hin : a ∈ loadsOf (run.trace 1) := by rw [hq]; exact List.mem_cons_self ..
      exact List.mem_filterMap.1 hin
  obtain ⟨⟨a1, hl1'⟩, hlen1⟩ := hΨ1.2.2.2.2 e1 he1 tvs1 hl1
  obtain ⟨tv1, r1, rfl⟩ : ∃ tv r, tvs1 = tv :: r := by
    cases tvs1 with
    | nil => cases hlen1
    | cons tv r => exact ⟨tv, r, rfl⟩
  have hb1 := ((hwf 1 e1 he1).1 z (tv1 :: r1) (by rw [hl1']; rfl)).1
  have hv1' := obsOf_zero hv1
  obtain ⟨k1, m1, hk1, hm1, hmb1⟩ := src_msg hb1 hz1 (by
    intro he; rw [he] at hv1'; exact absurd hv1' (by decide))
  obtain ⟨h1, e1', he1', het1⟩ := fulfil_entry hm1 hpart
  rcases hdom h1 e1' he1' with rfl | rfl
  · -- H0's entry: an `st` at `z` (an `exst` at `y` does not cover `z`)
    rcases hΨ0.1 e1' he1' _ het1 with ⟨aq, rl, base, data, asrc, vsrc, hst⟩ | ⟨aq, rl, base, data, asrc, vsrc, hst⟩
    · obtain ⟨hb, _⟩ := (hΨ0.2.1 e1' he1').1 _ _ _ _ _ _ hst
      obtain ⟨m, hm, hpa, hdata⟩ := write_msg hwf he1' het1 (by rw [hst]; rfl)
      simp only [Nat.add_sub_cancel] at hm; rw [hm1] at hm; cases hm
      rw [hZZ m1 (by rw [hpa, hb]), hdata] at hmb1
      have hd0 : data[0]? = some 0 := by
        rw [hmb1]; congr 1; apply BitVec.eq_of_toNat_eq; rw [hv1']; rfl
      -- (Q3) of H0: s0 < tz = s1; (P3) of H1: s1 < t1 = s0
      have q3 := hΨ0.2.2.1 e0 he0 e1' he1' _ _ _ _ _ _ _ _ _ _ _ _ _ hl0 hst hd0 het1
      have p3 := hΨ1.2.2.2.1 e1 he1 e0' he0' _ _ _ _ _ _ _ hl1' het0
      omega
    · exfalso
      obtain ⟨hb, hdl⟩ := (hΨ0.2.1 e1' he1').2 _ _ _ _ _ _ hst
      obtain ⟨m, hm, hpa, hdata⟩ := write_msg hwf he1' het1 (by rw [hst]; rfl)
      simp only [Nat.add_sub_cancel] at hm; rw [hm1] at hm; cases hm
      rw [hYZ m1 (by rw [hpa, hb]) (by rw [hdata, hdl])] at hmb1; cases hmb1
  · -- H1's own store is at `x`: it does not cover `z`
    exfalso
    obtain ⟨aq, rl, base, data, asrc, vsrc, hst⟩ := hΨ1.1 e1' he1' _ het1
    obtain ⟨hb, hdl⟩ := hΨ1.2.1 e1' he1' _ _ _ _ _ _ hst
    obtain ⟨m, hm, hpa, hdata⟩ := write_msg hwf he1' het1 (by rw [hst]; rfl)
    simp only [Nat.add_sub_cancel] at hm; rw [hm1] at hm; cases hm
    rw [hXZ m1 (by rw [hpa, hb]) (by rw [hdata, hdl])] at hmb1; cases hmb1

end contra

end Weak.Prom.PF
