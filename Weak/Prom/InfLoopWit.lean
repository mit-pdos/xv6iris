/-
Weak/Prom: **InfWit — the end-to-end theorem `inf_mpLoop` is NOT vacuous** (owner 2026-11-16, verbatim: "Start
with G5"; gap G5 of CutReview.md §2(ii)/§4: "no Lean vacuity witness `infExec tLoop E_SC`").

`inf_mpLoop` (InfLoop.lean) quantifies over every `E` with `infExec tLoop E` (PfxDefs.lean: the harts run `tLoop`
forever under the loop front end `stepL`, the path conditions hold, and `rvwmoRefInf` — rvwmo.adoc's global memory
order, preserved program order, the load value, atomicity and progress axioms over a possibly infinite set of
events).  This file exhibits ONE such execution and shows that the theorem's premises are all met in it.

* `E_SC` — the SEQUENTIALLY CONSISTENT INTERLEAVING (CutReview.md §2(ii)): both harts run their four instructions
  forever (`nxt`: the `stepL` successor; for `beq zero,zero,0`, the taken side of the `.fork`); the global memory
  order is the rank order `rkS`, hart 0's `n`-th memory operation at rank `2n`, hart 1's at `2n + 1`
  (rvwmo.adoc:46–47 "a total ordering of the memory operations produced by all harts"); the load values are the
  ones the load value axiom (rvwmo.adoc:315–324) prescribes for that order: hart 1's first flag load reads the
  initial 0, every other load reads 1.
* `infExec_witness : infExec tLoop E_SC` — every conjunct: `conforms`, `condsOkI`, `gmoOk`, `evWfI`, `ppoAxI`
  (every ppo / I/O edge is a po edge, and po is rank-increasing), `loadValueAxI` (the latest gmo-earlier store,
  explicitly), `atomicityAxI` / `scAxI` (vacuous: `tLoop` has no LR/SC), `progressAxI` (every rank is finite; a
  pigeonhole argument).
* `inf_mpLoop_exercised` — every premise of `inf_mpLoop` is met at once (hart 1, flag load `(1, 3)` of the second
  iteration, which returned `[1,0,0,0]`; data load `(1, 5)`), and the conclusion `(E_SC.ev (1, 5)).rdat =
  [1,0,0,0]` follows both from `inf_mpLoop` (`witness_concl_thm`) and by direct computation (`witness_concl`).
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Prom.InfLoop

noncomputable section

namespace Weak.Prom.InfLoop.Wit

open Classical
open Weak.Prom.Ref
open Weak.Prom.Pfx
open Weak.Prom.PF.Loop (tLoop)
open Weak.Prom.Ref.Lit (X Y)

/-! ## 1. The events of the run, in closed form -/

/-- Hart 0's `fence w,w` (the program literal, InfLoopRef.lean `prog0`). -/
def fW0 : FenceSet := ⟨false, true, false, false, false, true, false, false⟩

/-- Hart 1's `fence r,r` (the program literal, InfLoopRef.lean `prog1`). -/
def fR1 : FenceSet := ⟨true, false, false, false, true, false, false, false⟩

/-- The symbolic event of hart `h`'s iteration `q`, instruction `p` (`p < 3`; the branch emits nothing):
hart 0 `sw t1,0(a2)` / `fence w,w` / `sw t1,0(a3)`, hart 1 `lw a0,0(a3)` / `fence r,r` / `lw a1,0(a2)`
(RefProg.lean `stepI`: untainted registers, no control dependency — `beq zero,zero,0` reads `x0` only). -/
def evP : Nat → Nat → Nat → SEv
  | 0, q, 0 => ⟨{ kind := .st, ii := 4 * q, sz := 4 }, aX, .c 1⟩
  | 0, q, 1 => ⟨{ kind := .fence fW0, ii := 4 * q + 1, sz := 0 }, .c 0, .c 0⟩
  | 0, q, _ => ⟨{ kind := .st, ii := 4 * q + 2, sz := 4 }, aY, .c 1⟩
  | _, q, 0 => ⟨{ kind := .ld, ii := 4 * q, sz := 4 }, aY, .c 0⟩
  | _, q, 1 => ⟨{ kind := .fence fR1, ii := 4 * q + 1, sz := 0 }, .c 0, .c 0⟩
  | _, q, _ => ⟨{ kind := .ld, ii := 4 * q + 2, sz := 4 }, aX, .c 0⟩

/-- Event `i` of hart `h`: iteration `i / 3`, instruction `i % 3`. -/
def evF (h i : Nat) : SEv := evP h (i / 3) (i % 3)

/-- The number of events after `k` steps (three per four-instruction iteration). -/
def cnt (k : Nat) : Nat := 3 * (k / 4) + min (k % 4) 3

theorem evF_eq (h q c : Nat) (hc : c < 3) : evF h (3 * q + c) = evP h q c := by
  unfold evF; rw [show (3 * q + c) / 3 = q by omega, show (3 * q + c) % 3 = c by omega]

theorem cnt_eq (q c : Nat) (hc : c < 3) : cnt (4 * q + c) = 3 * q + c := by unfold cnt; omega

theorem evF_cnt (h q c : Nat) (hc : c < 3) : evF h (cnt (4 * q + c)) = evP h q c := by
  rw [cnt_eq q c hc, evF_eq h q c hc]

theorem range_snoc {α : Type} (f : Nat → α) (n : Nat) :
    (List.range n).map f ++ [f n] = (List.range (n + 1)).map f := by
  rw [List.range_succ, List.map_append]; rfl

/-! ## 2. The run: iterate the loop front end -/

/-- The successor state: `stepL` on the instruction at `pc`, the TAKEN side of a fork (the only fork of `tLoop`
is `beq zero,zero,0`). -/
def nxt (h : Nat) (s : SSt) : SSt :=
  match stepL h 4 s (((tLoop.prog h)[s.pc]?).getD .nop) with
  | .next s' => s'
  | .fork t _ => t
  | .stuck => s

/-- Hart `h`'s state after `k` steps. -/
def stS (h : Nat) : Nat → SSt
  | 0 => tLoop.init h
  | k + 1 => nxt h (stS h k)

/-- The invariant of the run after `k` steps. -/
structure J (h k : Nat) (s : SSt) : Prop where
  pc : s.pc = k % 4
  ii : s.ii = k
  ctl : s.ctl = []
  evs : s.evs = (List.range (cnt k)).map (evF h)
  r12 : s.rd 12 = (.c X, [])
  r13 : s.rd 13 = (.c Y, [])
  r6 : h = 0 → s.rd 6 = (.c 1, [])
  conds : ∀ c ∈ s.conds, c = (.eq, .c 0, .c 0, true)

theorem wr_ii (s : SSt) (r : Nat) (v : Ex × List Nat) : (s.wr r v).ii = s.ii := by
  unfold SSt.wr; split <;> rfl

theorem wr_ctl (s : SSt) (r : Nat) (v : Ex × List Nat) : (s.wr r v).ctl = s.ctl := by
  unfold SSt.wr; split <;> rfl

theorem wr_conds (s : SSt) (r : Nat) (v : Ex × List Nat) : (s.wr r v).conds = s.conds := by
  unfold SSt.wr; split <;> rfl

theorem J_emit {h k : Nat} {s s' : SSt} {se : SEv} (hJ : J h k s) (hk : k % 4 < 3) (hpc : s'.pc = s.pc + 1)
    (hii : s'.ii = s.ii + 1) (hctl : s'.ctl = s.ctl) (hcd : s'.conds = s.conds) (hev : s'.evs = s.evs ++ [se])
    (hse : se = evF h (cnt k)) (h12 : s'.rd 12 = s.rd 12) (h13 : s'.rd 13 = s.rd 13) (h6 : s'.rd 6 = s.rd 6) :
    J h (k + 1) s' :=
  ⟨by rw [hpc, hJ.pc]; omega, by rw [hii, hJ.ii], by rw [hctl, hJ.ctl],
    by rw [hev, hJ.evs, hse, range_snoc, show cnt (k + 1) = cnt k + 1 by unfold cnt; omega],
    by rw [h12, hJ.r12], by rw [h13, hJ.r13], fun h0 => by rw [h6, hJ.r6 h0], by rw [hcd]; exact hJ.conds⟩

/-- A step that appends one event (store, fence). -/
theorem J_plain {h k : Nat} {s : SSt} {se : SEv} (hJ : J h k s) (hk : k % 4 < 3) (hse : se = evF h (cnt k)) :
    J h (k + 1) (s.emit se).adv :=
  J_emit hJ hk rfl rfl rfl rfl rfl hse rfl rfl rfl

/-- A step that appends one event and writes a register other than `x6`, `x12`, `x13` (load). -/
theorem J_load {h k r : Nat} {s : SSt} {se : SEv} {v : Ex × List Nat} (hJ : J h k s) (hk : k % 4 < 3)
    (hse : se = evF h (cnt k)) (h6 : r ≠ 6) (h12 : r ≠ 12) (h13 : r ≠ 13) :
    J h (k + 1) ((s.emit se).wr r v).adv :=
  J_emit hJ hk (by show ((s.emit se).wr r v).pc + 1 = _; rw [wr_pc]; rfl)
    (by show ((s.emit se).wr r v).ii + 1 = _; rw [wr_ii]; rfl) (wr_ctl _ _ _) (wr_conds _ _ _)
    (by show ((s.emit se).wr r v).evs = _; rw [wr_evs]; rfl) hse
    (by show ((s.emit se).wr r v).rd 12 = _; rw [wr_rd _ h12]; rfl)
    (by show ((s.emit se).wr r v).rd 13 = _; rw [wr_rd _ h13]; rfl)
    (by show ((s.emit se).wr r v).rd 6 = _; rw [wr_rd _ h6]; rfl)

/-- The taken `beq zero,zero,0`. -/
theorem J_br {h k : Nat} {s : SSt} (hJ : J h k s) (hk : k % 4 = 3) :
    J h (k + 1)
      { s with ii := s.ii + 1, ctl := s.ctl ++ [] ++ [], pc := 0, conds := s.conds ++ [(.eq, .c 0, .c 0, true)] } :=
  ⟨by show 0 = _; omega, by show s.ii + 1 = _; rw [hJ.ii], by show s.ctl ++ [] ++ [] = []; rw [hJ.ctl]; rfl,
    by show s.evs = _; rw [hJ.evs, show cnt (k + 1) = cnt k by unfold cnt; omega], hJ.r12, hJ.r13, hJ.r6,
    fun c hc => by
      rcases List.mem_append.1 hc with hc | hc
      · exact hJ.conds c hc
      · exact List.mem_singleton.1 hc⟩

theorem nxt_next {h : Nat} {s s' : SSt} {i : Instr} (hl : (tLoop.prog h).length = 4)
    (hget : (tLoop.prog h)[s.pc]? = some i) (hst : stepL h 4 s i = .next s') :
    nxt h s = s' ∧ LStep (tLoop.prog h) h s s' := by
  refine ⟨?_, .inr ⟨i, hget, ?_⟩⟩
  · simp only [nxt, hget, Option.getD_some, hst]
  · rw [hl]; exact .inl hst

theorem nxt_fork {h : Nat} {s t f : SSt} {i : Instr} (hl : (tLoop.prog h).length = 4)
    (hget : (tLoop.prog h)[s.pc]? = some i) (hst : stepL h 4 s i = .fork t f) :
    nxt h s = t ∧ LStep (tLoop.prog h) h s t := by
  refine ⟨?_, .inr ⟨i, hget, ?_⟩⟩
  · simp only [nxt, hget, Option.getD_some, hst]
  · rw [hl]; exact .inr ⟨t, f, hst, .inl rfl⟩

/-- **One step of the run** keeps the invariant and is an `LStep` of `tLoop`'s program. -/
theorem J_step {h k : Nat} {s : SSt} (hh : h < 2) (hJ : J h k s) :
    J h (k + 1) (nxt h s) ∧ LStep (tLoop.prog h) h s (nxt h s) := by
  have hl : (tLoop.prog h).length = 4 := by rcases (by omega : h = 0 ∨ h = 1) with rfl | rfl <;> rfl
  obtain ⟨q, c, hc, rfl⟩ : ∃ q c, c < 4 ∧ k = 4 * q + c := ⟨k / 4, k % 4, Nat.mod_lt _ (by decide), by omega⟩
  have hpc : s.pc = c := by rw [hJ.pc]; omega
  rcases (by omega : h = 0 ∨ h = 1) with rfl | rfl <;>
    rcases (by omega : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3) with rfl | rfl | rfl | rfl
  · obtain ⟨hn, hL⟩ := nxt_next hl (by rw [hpc]; rfl) (stepL_store _ _ _ _ _ _ _ hJ.r12 (hJ.r6 rfl))
    rw [hn]; refine ⟨J_plain hJ (by omega) ?_, hL⟩
    rw [hJ.ii, hJ.ctl]; exact (evF_cnt 0 q 0 (by decide)).symm
  · obtain ⟨hn, hL⟩ := nxt_next hl (by rw [hpc]; rfl) (stepL_fence 0 4 s fW0)
    rw [hn]; refine ⟨J_plain hJ (by omega) ?_, hL⟩
    rw [hJ.ii]; exact (evF_cnt 0 q 1 (by decide)).symm
  · obtain ⟨hn, hL⟩ := nxt_next hl (by rw [hpc]; rfl) (stepL_store _ _ _ _ _ _ _ hJ.r13 (hJ.r6 rfl))
    rw [hn]; refine ⟨J_plain hJ (by omega) ?_, hL⟩
    rw [hJ.ii, hJ.ctl]; exact (evF_cnt 0 q 2 (by decide)).symm
  · obtain ⟨hn, hL⟩ := nxt_fork hl (by rw [hpc]; rfl) (stepL_br 0 s)
    rw [hn]; exact ⟨J_br hJ (by omega), hL⟩
  · obtain ⟨hn, hL⟩ := nxt_next hl (by rw [hpc]; rfl) (stepL_load _ _ _ 10 _ _ hJ.r13)
    rw [hn]; refine ⟨J_load hJ (by omega) ?_ (by decide) (by decide) (by decide), hL⟩
    rw [hJ.ii, hJ.ctl]; exact (evF_cnt 1 q 0 (by decide)).symm
  · obtain ⟨hn, hL⟩ := nxt_next hl (by rw [hpc]; rfl) (stepL_fence 1 4 s fR1)
    rw [hn]; refine ⟨J_plain hJ (by omega) ?_, hL⟩
    rw [hJ.ii]; exact (evF_cnt 1 q 1 (by decide)).symm
  · obtain ⟨hn, hL⟩ := nxt_next hl (by rw [hpc]; rfl) (stepL_load _ _ _ 11 _ _ hJ.r12)
    rw [hn]; refine ⟨J_load hJ (by omega) ?_ (by decide) (by decide) (by decide), hL⟩
    rw [hJ.ii, hJ.ctl]; exact (evF_cnt 1 q 2 (by decide)).symm
  · obtain ⟨hn, hL⟩ := nxt_fork hl (by rw [hpc]; rfl) (stepL_br 1 s)
    rw [hn]; exact ⟨J_br hJ (by omega), hL⟩

theorem J_all {h : Nat} (hh : h < 2) : ∀ k, J h k (stS h k)
  | 0 => by
    rcases (by omega : h = 0 ∨ h = 1) with rfl | rfl
    · exact ⟨rfl, rfl, rfl, rfl, by decide, by decide, fun _ => by decide,
        fun c hc => by simp [stS, Test.init] at hc⟩
    · exact ⟨rfl, rfl, rfl, rfl, by decide, by decide, fun h0 => absurd h0 (by decide),
        fun c hc => by simp [stS, Test.init] at hc⟩
  | k + 1 => (J_step hh (J_all hh k)).1

theorem J_len {h : Nat} (hh : h < 2) (k : Nat) : (stS h k).evs.length = cnt k := by
  rw [(J_all hh k).evs, List.length_map, List.length_range]

/-! ## 3. The execution -/

/-- The rank of an event in the global memory order: hart 0's `n`-th memory operation at `2n`, hart 1's at
`2n + 1` (event `i` is memory operation `2 (i / 3) + (i % 3) / 2` of its hart when `i % 3 ≠ 1`). -/
def rkS (e : EvId) : Nat := 2 * (2 * (e.2 / 3) + e.2 % 3 / 2) + e.1

theorem rkS_mk (h i : Nat) : rkS (h, i) = 2 * (2 * (i / 3) + i % 3 / 2) + h := rfl

/-- THE GLOBAL MEMORY ORDER: rank order on the memory operations (`h < 2`, `i % 3 ≠ 1`). -/
def gmoSC (a b : EvId) : Prop := a.1 < 2 ∧ b.1 < 2 ∧ a.2 % 3 ≠ 1 ∧ b.2 % 3 ≠ 1 ∧ rkS a < rkS b

/-- THE LOAD VALUES: hart 1's first flag load returns the initial 0, every other load 1. -/
def nuSC : Val := fun e => if e = (1, 0) then [0, 0, 0, 0] else [1, 0, 0, 0]

/-- **The SC interleaving of `tLoop`, run forever.** -/
def E_SC : IExec where
  T := tLoop
  st := stS
  ν := nuSC
  gmo := gmoSC

theorem conforms_SC : E_SC.conforms := fun h hh =>
  ⟨rfl, fun k => (J_step (h := h) (show h < 2 from hh) (J_all (show h < 2 from hh) k)).2⟩

theorem frag_SC : FragT E_SC.T := fragT_of tLoop_S3a

theorem has_SC (e : EvId) : E_SC.has e ↔ e.1 < 2 := by
  refine ⟨fun he => he.1, fun hh => ⟨hh, 4 * e.2 + 4, ?_⟩⟩
  show e.2 < (stS e.1 (4 * e.2 + 4)).evs.length
  rw [J_len hh]; unfold cnt; omega

theorem sev_SC {h : Nat} (hh : h < 2) (i : Nat) : E_SC.sev (h, i) = evF h i := by
  have hk : i < (E_SC.st h (4 * i + 4)).evs.length := by
    show i < (stS h _).evs.length; rw [J_len hh]; unfold cnt; omega
  have h1 := Pfx.sev_eq conforms_SC frag_SC (show h < E_SC.T.harts.length from hh) hk
  have h2 : (E_SC.st h (4 * i + 4)).evs[i]? = some (evF h i) := by
    show (stS h (4 * i + 4)).evs[i]? = _
    rw [(J_all hh _).evs, List.getElem?_map, List.getElem?_range (by unfold cnt; omega)]; rfl
  rw [h1] at h2; exact Option.some.inj h2

theorem ev_SC {h : Nat} (hh : h < 2) (i : Nat) : E_SC.ev (h, i) = concEv nuSC h i (evF h i) := by
  show concEv nuSC h i (E_SC.sev (h, i)) = _; rw [sev_SC hh]

theorem sk_SC {h : Nat} (hh : h < 2) (i : Nat) : E_SC.sk (h, i) = (evF h i).sk := by
  show (E_SC.ev (h, i)).sk = _; rw [ev_SC hh]; rfl

/-! ## 4. Event facts (six cases: hart × instruction) -/

/-- The kind of instruction `p` of hart `h`. -/
def kF (h p : Nat) : Kind := if p = 1 then .fence (if h = 0 then fW0 else fR1) else if h = 0 then .st else .ld

/-- The address of instruction `p` of hart `h` (`p ≠ 1`). -/
def paF (h p : Nat) : Nat := if h = 0 then (if p = 0 then X else Y) else (if p = 0 then Y else X)

theorem kindF {h : Nat} (hh : h < 2) (i : Nat) : (evF h i).sk.kind = kF h (i % 3) := by
  have hp : i % 3 < 3 := Nat.mod_lt _ (by decide)
  unfold evF; generalize i / 3 = q; generalize i % 3 = p at hp ⊢
  rcases (by omega : h = 0 ∨ h = 1) with rfl | rfl <;>
    rcases (by omega : p = 0 ∨ p = 1 ∨ p = 2) with rfl | rfl | rfl <;> rfl

theorem iiF {h : Nat} (hh : h < 2) (i : Nat) : (evF h i).sk.ii = 4 * (i / 3) + i % 3 := by
  have hp : i % 3 < 3 := Nat.mod_lt _ (by decide)
  unfold evF; generalize i / 3 = q; generalize i % 3 = p at hp ⊢
  rcases (by omega : h = 0 ∨ h = 1) with rfl | rfl <;>
    rcases (by omega : p = 0 ∨ p = 1 ∨ p = 2) with rfl | rfl | rfl <;> rfl

theorem szF {h : Nat} (hh : h < 2) (i : Nat) (hi : i % 3 ≠ 1) : (evF h i).sk.sz = 4 := by
  have hp : i % 3 < 3 := Nat.mod_lt _ (by decide)
  unfold evF; generalize i / 3 = q; generalize i % 3 = p at hp hi ⊢
  rcases (by omega : h = 0 ∨ h = 1) with rfl | rfl <;>
    rcases (by omega : p = 0 ∨ p = 2) with rfl | rfl <;> rfl

theorem addrF {h : Nat} (hh : h < 2) (i : Nat) (hi : i % 3 ≠ 1) (ν : Val) :
    (evF h i).addr.eval ν = paF h (i % 3) := by
  have hp : i % 3 < 3 := Nat.mod_lt _ (by decide)
  unfold evF; generalize i / 3 = q; generalize i % 3 = p at hp hi ⊢
  rcases (by omega : h = 0 ∨ h = 1) with rfl | rfl <;>
    rcases (by omega : p = 0 ∨ p = 2) with rfl | rfl <;> rfl

theorem wvalF {h : Nat} (hh : h < 2) (i : Nat) (hi : i % 3 ≠ 1) (ν : Val) :
    (evF h i).wval.eval ν = if h = 0 then 1 else 0 := by
  have hp : i % 3 < 3 := Nat.mod_lt _ (by decide)
  unfold evF; generalize i / 3 = q; generalize i % 3 = p at hp hi ⊢
  rcases (by omega : h = 0 ∨ h = 1) with rfl | rfl <;>
    rcases (by omega : p = 0 ∨ p = 2) with rfl | rfl <;> rfl

/-- The two addresses as one arithmetic formula (`X = 0x1000`, `Y = 0x2000`). -/
theorem paF_val {h p : Nat} (hh : h < 2) (hp : p < 3) (hp1 : p ≠ 1) :
    paF h p = 4096 + 4096 * ((h + p / 2) % 2) := by
  rcases (by omega : h = 0 ∨ h = 1) with rfl | rfl <;>
    rcases (by omega : p = 0 ∨ p = 2) with rfl | rfl <;> rfl

theorem mod3 (i : Nat) : i % 3 < 3 := Nat.mod_lt _ (by decide)

theorem z2 : (0 : Nat) < 2 := by decide
theorem o2 : (1 : Nat) < 2 := by decide

/-- Every access is naturally aligned (`condsOk`'s second half). -/
theorem condF {h : Nat} (hh : h < 2) (i : Nat) (ν : Val) :
    (!(evF h i).sk.kind.isAcc || ((evF h i).addr.eval ν % (evF h i).sk.sz == 0)) = true := by
  by_cases hi : i % 3 = 1
  · rw [kindF hh, show kF h (i % 3) = .fence (if h = 0 then fW0 else fR1) by simp [kF, hi]]
    simp [Kind.isAcc, Kind.isMem]
  · rw [addrF hh i hi, szF hh i hi, paF_val hh (mod3 i) hi]
    have : (4096 + 4096 * ((h + i % 3 / 2) % 2)) % 4 = 0 := by omega
    rw [this]; simp

theorem kF_mem {h p : Nat} (hh : h < 2) (hp : p < 3) : (kF h p).isMem = true ↔ p ≠ 1 := by
  rcases (by omega : h = 0 ∨ h = 1) with rfl | rfl <;>
    rcases (by omega : p = 0 ∨ p = 1 ∨ p = 2) with rfl | rfl | rfl <;> decide

theorem kF_load {h p : Nat} (hh : h < 2) (hp : p < 3) : (kF h p).isLoad = true ↔ h = 1 ∧ p ≠ 1 := by
  rcases (by omega : h = 0 ∨ h = 1) with rfl | rfl <;>
    rcases (by omega : p = 0 ∨ p = 1 ∨ p = 2) with rfl | rfl | rfl <;> decide

theorem kF_store {h p : Nat} (hh : h < 2) (hp : p < 3) : (kF h p).isStore = true ↔ h = 0 ∧ p ≠ 1 := by
  rcases (by omega : h = 0 ∨ h = 1) with rfl | rfl <;>
    rcases (by omega : p = 0 ∨ p = 1 ∨ p = 2) with rfl | rfl | rfl <;> decide

theorem kF_lr {h p : Nat} (hh : h < 2) (hp : p < 3) : kF h p ≠ .lr := by
  rcases (by omega : h = 0 ∨ h = 1) with rfl | rfl <;>
    rcases (by omega : p = 0 ∨ p = 1 ∨ p = 2) with rfl | rfl | rfl <;> decide

theorem kF_sc {h p : Nat} (hh : h < 2) (hp : p < 3) : kF h p ≠ .sc := by
  rcases (by omega : h = 0 ∨ h = 1) with rfl | rfl <;>
    rcases (by omega : p = 0 ∨ p = 1 ∨ p = 2) with rfl | rfl | rfl <;> decide

theorem mem_SC (h i : Nat) : E_SC.isMem (h, i) ↔ h < 2 ∧ i % 3 ≠ 1 := by
  constructor
  · rintro ⟨hhas, hm⟩
    have hh : h < 2 := (has_SC _).1 hhas
    rw [sk_SC hh, kindF hh] at hm
    exact ⟨hh, (kF_mem hh (mod3 i)).1 hm⟩
  · rintro ⟨hh, hi⟩
    refine ⟨(has_SC _).2 hh, ?_⟩
    rw [sk_SC hh, kindF hh]; exact (kF_mem hh (mod3 i)).2 hi

theorem load_SC {h i : Nat} (hh : h < 2) : (E_SC.sk (h, i)).kind.isLoad = true ↔ h = 1 ∧ i % 3 ≠ 1 := by
  rw [sk_SC hh, kindF hh]; exact kF_load hh (mod3 i)

theorem store_SC {h i : Nat} (hh : h < 2) : (E_SC.sk (h, i)).kind.isStore = true ↔ h = 0 ∧ i % 3 ≠ 1 := by
  rw [sk_SC hh, kindF hh]; exact kF_store hh (mod3 i)

theorem pa_SC {h i : Nat} (hh : h < 2) (hi : i % 3 ≠ 1) : (E_SC.ev (h, i)).pa = paF h (i % 3) := by
  rw [ev_SC hh]; exact addrF hh i hi nuSC

theorem szE {h i : Nat} (hh : h < 2) (hi : i % 3 ≠ 1) : (E_SC.sk (h, i)).sz = 4 := by
  rw [sk_SC hh]; exact szF hh i hi

theorem iiE {h i : Nat} (hh : h < 2) : (E_SC.sk (h, i)).ii = 4 * (i / 3) + i % 3 := by
  rw [sk_SC hh]; exact iiF hh i

theorem rdat_SC {h i : Nat} (hh : h < 2) (hl : (E_SC.sk (h, i)).kind.isLoad = true) :
    (E_SC.ev (h, i)).rdat = nuSC (h, i) := by
  rw [sk_SC hh] at hl
  rw [ev_SC hh]
  show (if (evF h i).sk.kind.isLoad then nuSC (h, i) else []) = _
  rw [if_pos hl]

theorem wdat_SC {h i : Nat} (hh : h < 2) (hs : (E_SC.sk (h, i)).kind.isStore = true) :
    (E_SC.ev (h, i)).wdat = [1, 0, 0, 0] := by
  obtain ⟨rfl, hi⟩ := (store_SC hh).1 hs
  rw [sk_SC hh] at hs
  rw [ev_SC hh]
  show (if (evF 0 i).sk.kind.isStore then byteList ((evF 0 i).wval.eval nuSC) (evF 0 i).sk.sz else []) = _
  rw [if_pos hs, wvalF hh i hi, szF hh i hi]; rfl

/-! ## 5. The conjuncts -/

theorem condsOk_SC : E_SC.condsOkI := by
  intro h hh k
  have hh' : h < 2 := hh
  have hJ := J_all hh' k
  show condsOk nuSC [stS h k] = true
  unfold condsOk
  rw [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true]
  refine ⟨List.all_eq_true.2 (fun c hc => ?_), List.all_eq_true.2 (fun se hse => ?_)⟩
  · rw [hJ.conds c hc]; rfl
  · rw [hJ.evs] at hse
    obtain ⟨i, _, rfl⟩ := List.mem_map.1 hse
    exact condF hh' i nuSC

theorem rkS_inj {a b : EvId} (ha1 : a.1 < 2) (hb1 : b.1 < 2) (ha : a.2 % 3 ≠ 1) (hb : b.2 % 3 ≠ 1)
    (h : rkS a = rkS b) : a = b := by
  obtain ⟨h1, i⟩ := a
  obtain ⟨h2, j⟩ := b
  simp only [rkS_mk] at h
  simp only at ha1 hb1 ha hb
  have : h1 = h2 ∧ i = j := by omega
  rw [this.1, this.2]

theorem gmoOk_SC : E_SC.gmoOk := by
  refine ⟨fun a b hab => ⟨(mem_SC _ _).2 ⟨hab.1, hab.2.2.1⟩, (mem_SC _ _).2 ⟨hab.2.1, hab.2.2.2.1⟩⟩,
    fun a haa => Nat.lt_irrefl _ haa.2.2.2.2,
    fun a b c hab hbc => ⟨hab.1, hbc.2.1, hab.2.2.1, hbc.2.2.2.1, Nat.lt_trans hab.2.2.2.2 hbc.2.2.2.2⟩,
    fun a b ha hb hne => ?_⟩
  obtain ⟨ha1, ha2⟩ := (mem_SC _ _).1 ha
  obtain ⟨hb1, hb2⟩ := (mem_SC _ _).1 hb
  rcases Nat.lt_trichotomy (rkS a) (rkS b) with h | h | h
  · exact .inl ⟨ha1, hb1, ha2, hb2, h⟩
  · exact absurd (rkS_inj ha1 hb1 ha2 hb2 h) hne
  · exact .inr ⟨hb1, ha1, hb2, ha2, h⟩

theorem evWf_SC : E_SC.evWfI := by
  rintro ⟨h, i⟩ he
  have hh : h < 2 := (has_SC _).1 he
  refine ⟨fun hl => ?_, fun hs => ?_⟩
  · obtain ⟨_, hi⟩ := (load_SC hh).1 hl
    rw [rdat_SC hh hl, szE hh hi]; unfold nuSC; split <;> rfl
  · obtain ⟨_, hi⟩ := (store_SC hh).1 hs
    rw [wdat_SC hh hs, szE hh hi]; rfl

/-- Program order between memory operations is rank order (every ppo edge is a po edge). -/
theorem po_gmo {a b : EvId} (ha : E_SC.isMem a) (hb : E_SC.isMem b) (hpo : poS E_SC.sk a b = true) :
    E_SC.gmo a b := by
  obtain ⟨h, i⟩ := a
  obtain ⟨h', j⟩ := b
  obtain ⟨ha1, ha2⟩ := (mem_SC _ _).1 ha
  obtain ⟨hb1, hb2⟩ := (mem_SC _ _).1 hb
  simp only [poS, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hpo
  obtain ⟨rfl, hlt⟩ := hpo
  rw [iiE ha1, iiE hb1] at hlt
  refine ⟨ha1, hb1, ha2, hb2, ?_⟩
  show rkS (h, i) < rkS (h, j)
  rw [rkS_mk, rkS_mk]; omega

theorem ppo_SC : E_SC.ppoAxI := by
  intro a b hab
  have key : E_SC.isMem a ∧ E_SC.isMem b ∧ poS E_SC.sk a b = true := by
    rcases hab with ⟨h1, h2, h3, _⟩ | ⟨h1, h2, h3, _⟩
    · exact ⟨h1, h2, h3⟩
    · exact ⟨h1, h2, h3⟩
  exact po_gmo key.1 key.2.1 key.2.2

/-! ### The load value axiom -/

/-- A candidate store of byte `k` of hart 1's load `i` is a hart-0 store to the same address, earlier in rank. -/
theorem cand_fwd {i k : Nat} {w : EvId} (hi : i % 3 ≠ 1) (hk : k < 4)
    (hc : E_SC.candI (1, i) (paF 1 (i % 3) + k) w) :
    w.1 = 0 ∧ w.2 % 3 + i % 3 = 2 ∧ rkS w < rkS (1, i) := by
  obtain ⟨a, j⟩ := w
  obtain ⟨hw, hwr, hord⟩ := hc
  have ha : a < 2 := (has_SC _).1 hw
  unfold writesB touches at hwr
  rw [Bool.and_eq_true, decide_eq_true_eq] at hwr
  obtain ⟨hst, hlo, hhi⟩ := hwr
  obtain ⟨rfl, hj⟩ := (store_SC ha).1 hst
  rw [pa_SC ha hj] at hlo hhi
  rw [show (E_SC.ev (0, j)).sk.sz = 4 from szE ha hj] at hhi
  rw [paF_val ha (mod3 j) hj, paF_val (by decide) (mod3 i) hi] at hlo hhi
  refine ⟨rfl, ?_, ?_⟩
  · have := mod3 j; have := mod3 i; simp only; omega
  · rcases hord with hg | hpo
    · exact hg.2.2.2.2
    · simp [poS] at hpo

theorem cand_bwd {i k j : Nat} (hi : i % 3 ≠ 1) (hk : k < 4) (hj : j % 3 + i % 3 = 2)
    (hr : rkS (0, j) < rkS (1, i)) : E_SC.candI (1, i) (paF 1 (i % 3) + k) (0, j) := by
  have hj1 : j % 3 ≠ 1 := by omega
  refine ⟨(has_SC _).2 z2, ?_, .inl ⟨z2, o2, hj1, hi, hr⟩⟩
  unfold writesB touches
  rw [Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨(store_SC (by decide)).2 ⟨rfl, hj1⟩, ?_⟩
  rw [pa_SC (by decide) hj1, show (E_SC.ev (0, j)).sk.sz = 4 from szE (by decide) hj1,
    paF_val (by decide) (mod3 j) hj1, paF_val (by decide) (mod3 i) hi]
  have := mod3 j; have := mod3 i
  omega

theorem lva_some {i j k : Nat} (hi : i % 3 ≠ 1) (hi0 : i ≠ 0) (hk : k < 4) (hj : j % 3 + i % 3 = 2)
    (hr : rkS (0, j) < rkS (1, i))
    (hmax : ∀ j', j' % 3 + i % 3 = 2 → rkS (0, j') < rkS (1, i) → rkS (0, j') ≤ rkS (0, j)) :
    ∃ o, E_SC.rfI (1, i) (paF 1 (i % 3) + k) o ∧
      (nuSC (1, i))[k]? = some (E_SC.valI (paF 1 (i % 3) + k) o) := by
  have hj1 : j % 3 ≠ 1 := by omega
  refine ⟨some (0, j), ⟨cand_bwd hi hk hj hr, fun w' hw' => ?_⟩, ?_⟩
  · obtain ⟨h1, h2, h3⟩ := cand_fwd hi hk hw'
    obtain ⟨a, j'⟩ := w'
    simp only at h1 h2 h3; subst h1
    have hle := hmax j' h2 h3
    have hj1' : j' % 3 ≠ 1 := by omega
    rcases Nat.lt_or_eq_of_le hle with hlt | heq
    · exact .inr ⟨z2, z2, hj1', hj1, hlt⟩
    · exact .inl (rkS_inj z2 z2 hj1' hj1 heq)
  · have hnu : nuSC (1, i) = [1, 0, 0, 0] := by
      unfold nuSC; rw [if_neg (fun he => hi0 (Prod.mk.inj he).2)]
    show _ = some (wbyte (E_SC.ev (0, j)) _)
    unfold wbyte
    have hpa : paF 1 (i % 3) + k - paF 0 (j % 3) = k := by
      rw [paF_val (by decide) (mod3 j) hj1, paF_val (by decide) (mod3 i) hi]
      have := mod3 j; have := mod3 i
      omega
    rw [hnu, wdat_SC (by decide) ((store_SC (by decide)).2 ⟨rfl, hj1⟩), pa_SC (by decide) hj1, hpa]
    rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl <;> rfl

theorem lva_SC : E_SC.loadValueAxI := by
  rintro ⟨h, i⟩ hr hl _ k hk
  have hh : h < 2 := (has_SC _).1 hr
  obtain ⟨rfl, hi⟩ := (load_SC hh).1 hl
  rw [szE hh hi] at hk
  rw [pa_SC hh hi, rdat_SC hh hl]
  by_cases hi0 : i = 0
  · subst hi0
    refine ⟨none, fun w hw => ?_, ?_⟩
    · obtain ⟨h1, h2, h3⟩ := cand_fwd hi hk hw
      obtain ⟨a, j⟩ := w
      simp only at h1 h2 h3; subst h1
      rw [rkS_mk, rkS_mk] at h3
      omega
    · show _ = some (tLoop.imgF _)
      rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl <;> rfl
  · rcases (by have := mod3 i; omega : i % 3 = 0 ∨ i % 3 = 2) with h0 | h2
    · exact lva_some (j := i - 1) hi hi0 hk (by omega) (by rw [rkS_mk, rkS_mk]; omega)
        (fun j' h1 h2 => by rw [rkS_mk, rkS_mk] at *; omega)
    · exact lva_some (j := i - 2) hi hi0 hk (by omega) (by rw [rkS_mk, rkS_mk]; omega)
        (fun j' h1 h2 => by rw [rkS_mk, rkS_mk] at *; omega)

/-! ### Atomicity, SC, progress -/

theorem atom_SC : E_SC.atomicityAxI := by
  rintro ⟨h, i⟩ w hr _ hp
  exfalso
  have hh : h < 2 := (has_SC _).1 hr
  have hk := hp.1
  rw [sk_SC hh, kindF hh] at hk
  exact kF_lr hh (mod3 i) hk

theorem sc_SC : E_SC.scAxI := by
  rintro ⟨h, i⟩ hw hk
  exfalso
  have hh : h < 2 := (has_SC _).1 hw
  rw [sk_SC hh, kindF hh] at hk
  exact kF_sc hh (mod3 i) hk

/-- Pigeonhole: no injection of `Nat` into `[0, N)`. -/
theorem no_inj_bound : ∀ (N : Nat) (g : Nat → Nat), (∀ n, g n < N) → (∀ n m, g n = g m → n = m) → False
  | 0, g, hb, _ => absurd (hb 0) (Nat.not_lt_zero _)
  | N + 1, g, hb, hi => by
    by_cases hex : ∃ n0, g n0 = N
    · obtain ⟨n0, hn0⟩ := hex
      refine no_inj_bound N (fun n => g (if n < n0 then n else n + 1)) (fun n => ?_) (fun n m he => ?_)
      · have h1 := hb (if n < n0 then n else n + 1)
        have h2 : g (if n < n0 then n else n + 1) ≠ N := by
          intro he
          have := hi _ _ (he.trans hn0.symm)
          split at this <;> omega
        omega
      · have := hi _ _ he
        split at this <;> split at this <;> omega
    · exact no_inj_bound N g (fun n => by
        have h1 := hb n
        have h2 : g n ≠ N := fun h => hex ⟨n, h⟩
        omega) hi

theorem progress_SC : E_SC.progressAxI := by
  rintro e _ ⟨f, hinj, hlt⟩
  refine no_inj_bound (6 * rkS e) (fun n => 2 * (f n).2 + (f n).1) (fun n => ?_) (fun n m he => ?_)
  · obtain ⟨h1, _, _, _, h5⟩ := hlt n
    unfold rkS at h5 ⊢
    omega
  · have h1 := (hlt n).1
    have h2 := (hlt m).1
    exact hinj n m (Prod.ext (by omega) (by omega))

/-! ## 6. THE WITNESS -/

/-- **`inf_mpLoop` is not vacuous: `tLoop` has an infinite RVWMO execution** (CutReview.md G5).  Every conjunct
of `infExec` (PfxDefs.lean) holds for the SC interleaving `E_SC`. -/
theorem infExec_witness : infExec tLoop E_SC :=
  ⟨rfl, conforms_SC, condsOk_SC, gmoOk_SC, evWf_SC, ppo_SC, lva_SC, atom_SC, sc_SC, progress_SC⟩

/-- The witness is genuinely infinite: every hart-0/1 event index exists. -/
theorem witness_infinite (h i : Nat) (hh : h < 2) : E_SC.has (h, i) := (has_SC _).2 hh

/-- Hart 1's FIRST flag load (event `(1, 0)`) reads the initial 0 (so the flag premise genuinely selects). -/
theorem witness_first_flag : (E_SC.ev (1, 0)).rdat = [0, 0, 0, 0] := by
  rw [rdat_SC (by decide) ((load_SC (by decide)).2 ⟨rfl, by decide⟩)]; rfl

/-- **Every premise of `inf_mpLoop` is met at once** (hart 1's second iteration: flag load `(1, 3)` returned
`[1,0,0,0]`, its next memory operation `(1, 5)` is the data load). -/
theorem inf_mpLoop_exercised : ∃ E h i j, infExec tLoop E ∧ E.isMem (h, i) ∧ E.isMem (h, j) ∧ i < j ∧
    (∀ k, i < k → k < j → ¬ E.isMem (h, k)) ∧ (E.sk (h, i)).kind.isLoad = true ∧ (E.ev (h, i)).pa = Y ∧
    (E.ev (h, i)).rdat = [1, 0, 0, 0] ∧ (E.sk (h, j)).kind.isLoad = true ∧ (E.ev (h, j)).pa = X := by
  refine ⟨E_SC, 1, 3, 5, infExec_witness, (mem_SC _ _).2 ⟨by decide, by decide⟩,
    (mem_SC _ _).2 ⟨by decide, by decide⟩, by decide, fun k h1 h2 hm => ?_,
    (load_SC (by decide)).2 ⟨rfl, by decide⟩, ?_, ?_, (load_SC (by decide)).2 ⟨rfl, by decide⟩, ?_⟩
  · have : k = 4 := by omega
    subst this
    exact ((mem_SC _ _).1 hm).2 rfl
  · rw [pa_SC (by decide) (by decide)]; rfl
  · rw [rdat_SC (by decide) ((load_SC (by decide)).2 ⟨rfl, by decide⟩)]; rfl
  · rw [pa_SC (by decide) (by decide)]; rfl

/-- The conclusion at the witness, BY DIRECT COMPUTATION (the load value axiom's value). -/
theorem witness_concl : (E_SC.ev (1, 5)).rdat = [1, 0, 0, 0] := by
  rw [rdat_SC (by decide) ((load_SC (by decide)).2 ⟨rfl, by decide⟩)]; rfl

/-- The conclusion at the witness, FROM THE THEOREM `inf_mpLoop`. -/
theorem witness_concl_thm : (E_SC.ev (1, 5)).rdat = [1, 0, 0, 0] := by
  exact inf_mpLoop infExec_witness 1 3 5 ((mem_SC _ _).2 ⟨by decide, by decide⟩)
    ((mem_SC _ _).2 ⟨by decide, by decide⟩) (by decide)
    (fun k h1 h2 hm => by have : k = 4 := by omega
                          subst this; exact ((mem_SC _ _).1 hm).2 rfl)
    ((load_SC (by decide)).2 ⟨rfl, by decide⟩) (by rw [pa_SC (by decide) (by decide)]; rfl)
    (by rw [rdat_SC (by decide) ((load_SC (by decide)).2 ⟨rfl, by decide⟩)]; rfl)
    ((load_SC (by decide)).2 ⟨rfl, by decide⟩) (by rw [pa_SC (by decide) (by decide)]; rfl)

/-- **Premises and conclusion together**: some execution of `tLoop` meets every premise of `inf_mpLoop`, and its
data load returned `[1,0,0,0]`. -/
theorem inf_mpLoop_exercised_concl : ∃ E h i j, infExec tLoop E ∧ E.isMem (h, i) ∧ E.isMem (h, j) ∧ i < j ∧
    (∀ k, i < k → k < j → ¬ E.isMem (h, k)) ∧ (E.sk (h, i)).kind.isLoad = true ∧ (E.ev (h, i)).pa = Y ∧
    (E.ev (h, i)).rdat = [1, 0, 0, 0] ∧ (E.sk (h, j)).kind.isLoad = true ∧ (E.ev (h, j)).pa = X ∧
    (E.ev (h, j)).rdat = [1, 0, 0, 0] := by
  obtain ⟨E, h, i, j, hE, hi, hj, hij, hn, hfl, hfa, hfv, hdl, hda⟩ := inf_mpLoop_exercised
  exact ⟨E, h, i, j, hE, hi, hj, hij, hn, hfl, hfa, hfv, hdl, hda,
    inf_mpLoop hE h i j hi hj hij hn hfl hfa hfv hdl hda⟩

end Weak.Prom.InfLoop.Wit

end

#print axioms Weak.Prom.InfLoop.Wit.infExec_witness
#print axioms Weak.Prom.InfLoop.Wit.inf_mpLoop_exercised
#print axioms Weak.Prom.InfLoop.Wit.inf_mpLoop_exercised_concl
#print axioms Weak.Prom.InfLoop.Wit.witness_concl_thm
