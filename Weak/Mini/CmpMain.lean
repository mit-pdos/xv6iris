/-
Weak/Mini: **L4 MiniCmp — COMPLETENESS of MiniMach for MiniRef's finite executions** (mini plan rev 4 §2 L4:
"every finite MiniRef execution (cut) of an F program is a mini valid run (Pulte AtoP: promises first in gmo order,
replay along the hart's actual path), with equal load observations").

`mini_complete`: for a well-formed F program (its ALU immediates are 64-bit values, `MI.immOk` in `MProg.wf`; CmpStep.lean:
without it the machine's `slti`/`sltiu` and the reference's disagree) and a finite execution `C` (`miniCut`), a
valid run of MiniMach ending with memory `cutMem P C` (the cut's stores in gmo order) in which
* every hart's load values, in order, are the cut's (`cutLoads`), and
* every hart ends at the cut's pc with the cut's register values (it followed the cut's path; the mini front end
  LOOPS, so the run executes the program's own text, no unrolling).
The run: promise every store of `C.g` in order (`promAll`), then replay hart after hart (`run_hart`, one instruction
at a time: CmpStep.lean, CmpStepM.lean).
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Mini.CmpStepM

namespace Weak.Mini

open Weak.Mini.Mach Weak.Mini.Cmp

/-- The load values of hart `h` in the cut, in program order. -/
def cutLoads (P : MProg) (C : MCut) (h : Nat) : List Nat := ldVals (C.st P h).evs

/-- The cut's final memory: its stores in gmo order, as messages. -/
def cutMem (P : MProg) (C : MCut) : List MMsg := memL (C.evs P) C.g

namespace Cmp

variable {P : MProg} {C : MCut}

/-! ## 1. Reference-run facts -/

theorem mrun_out (P : MProg) (V : EvId → Nat) {h : Nat} (hh : P.harts.length ≤ h) : ∀ k, (mrun P V h k).evs = []
  | 0 => rfl
  | k + 1 => by
    show (mstep P V h (mrun P V h k)).evs = []
    have : P.prog h = [] := by simp [MProg.prog, List.getElem?_eq_none hh]
    simp only [mstep, this, List.getElem?_nil]; exact mrun_out P V hh k

/-- The reference facts of one step of the cut. -/
theorem sc_of {h k : Nat} (hk : k < C.ks h) : SC P C h (mrun P C.V h k) (mrun P C.V h (k + 1)) := by
  refine ⟨mrun_wf P C.V h k, fun i hi => ldAt_cut (Nat.le_of_lt hk) hi, fun e he => ?_, fun j hj1 hj2 hkd x hx => ?_⟩
  · have : (mrun P C.V h (k + 1)).evs[(mrun P C.V h k).evs.length]? = some e := by rw [he]; simp
    exact ev_run hk this
  · have hj : (mrun P C.V h (C.ks h)).evs[j]? = some ((C.evs P).ev (h, j)) := by
      rw [ev_eq hj2]; exact List.getElem?_eq_getElem hj2
    exact mrun_cdep P C.V h (k + 1) (C.ks h) hk j _ hj1 hj hkd x hx

/-! ## 2. One step, one hart -/

theorem step_any (hwf : P.wf) (himm : P.immOk) (hC : miniCut P C) {h k : Nat} (hh : h < P.harts.length)
    (hk : k < C.ks h) {H : MHart} (hI : Inv P C h (mrun P C.V h k) H) :
    StepOk P C h (mrun P C.V h k) (mrun P C.V h (k + 1)) H := by
  have hX := sc_of (P := P) hk
  show StepOk P C h _ (mstep P C.V h (mrun P C.V h k)) H
  change SC P C h _ (mstep P C.V h (mrun P C.V h k)) at hX
  generalize mrun P C.V h k = s at hX hI ⊢
  unfold mstep at hX ⊢
  split at hX
  · rename_i ins hi
    have hmem := List.mem_of_getElem? hi
    cases ins with
    | alui op rd rs1 imm =>
      have himm' := himm h _ hmem op rd rs1 imm rfl
      have hreg : rd < 32 ∧ rs1 < 32 := (hwf.2.2 h _ hmem).2.1  -- [MiniP3 (0)]
      rcases h1 : s.rd rs1 with ⟨v1, t1⟩
      simp only [exec, h1]
      have hr1 : H.fr.rd rs1 = v1 := by rw [hI.regs, h1]
      have hv1 : v1 < two64 := by have := hI.regLt rs1; rw [h1] at this; exact this
      refine step_regw hC hh hI hi (fun l => rfl) ?_ (by rw [Nat.mod_eq_of_lt himm']; exact aluOp_lt op hv1 himm') ?_
      · rw [hr1, Nat.mod_eq_of_lt himm', Nat.mod_eq_of_lt (aluOp_lt op hv1 himm')]
      · have := dom_srcR hI.regv hreg.2; rw [h1] at this; exact this
    | alu op rd rs1 rs2 =>
      have hreg := (hwf.2.2 h _ hmem).2.1  -- [MiniP3 (0)]
      rcases h1 : s.rd rs1 with ⟨v1, t1⟩
      rcases h2 : s.rd rs2 with ⟨v2, t2⟩
      simp only [exec, h1, h2]
      have hr1 : H.fr.rd rs1 = v1 := by rw [hI.regs, h1]
      have hr2 : H.fr.rd rs2 = v2 := by rw [hI.regs, h2]
      have hv1 : v1 < two64 := by have := hI.regLt rs1; rw [h1] at this; exact this
      have hv2 : v2 < two64 := by have := hI.regLt rs2; rw [h2] at this; exact this
      refine step_regw hC hh hI hi (fun l => rfl) ?_ (aluOp_lt op hv1 hv2) ?_
      · rw [hr1, hr2, Nat.mod_eq_of_lt (aluOp_lt op hv1 hv2)]
      · rw [srcsView_append]
        have d1 := dom_srcR hI.regv hreg.2.1; rw [h1] at d1
        have d2 := dom_srcR hI.regv hreg.2.2; rw [h2] at d2
        exact dom_max (dom_mono d1 (fun i hi => List.mem_append_left _ hi))
          (dom_mono d2 (fun i hi => List.mem_append_right _ hi))
    | load sgn rd rs1 off => exact step_load hC hh hwf hI hi hX
    | store rs2 rs1 off => exact step_store hC hh hwf hI hi hX
    | fence f => exact step_fence hC hh hI hi hX
    | br c rs1 rs2 tgt => exact step_br hC hh hwf hI hi hX
    | jmp tgt =>
      have htgt : tgt ≤ (P.prog h).length := (hwf.2.2 h _ hmem).1
      exact step_instr hC hh hI hi (pc' := tgt)
        (fun l => by simp only [instrNext, Nat.not_lt.2 htgt, if_false]) rfl rfl rfl
    | nop =>
      exact step_instr hC hh hI hi (pc' := H.fr.pc + 1) (fun l => rfl) rfl rfl
        (by show s.pc + 1 = H.fr.pc + 1; rw [hI.pc])
  · exact ⟨[], H, .refl _, hI, by simp [loadVals]⟩

/-! ## 3. One hart, all its steps -/

theorem inv_init (hC : miniCut P C) {h : Nat} (hh : h < P.harts.length) {prom : List Nat}
    (hp : ∀ t, t ∈ prom ↔ ∃ j, 0 ≤ j ∧ j < NN P C h ∧ kd P C h j = .st ∧ vo P C (h, j) = t) :
    Inv P C h (P.init h) ⟨⟨0, (List.range 32).map (fun r => P.reg0 h r % two64), []⟩, msInit, prom⟩ := by
  have hst : ∀ j, j < NN P C h → kd P C h j = .st → 0 < vo P C (h, j) := fun j hj hs =>
    vo_pos hC (mem_hj hC hh hj (.inr hs)) hs
  refine ⟨rfl, rfl, by simp, ?_, ?_, fun _ _ _ => .inl rfl, .inl rfl, .inl rfl, fun _ _ _ _ => Nat.zero_le _,
    fun j _ hj hs => hst j hj hs, fun j _ hj hs => hst j hj hs, fun j _ hj hs => hst j hj hs, ?_,
    fun _ j hj => absurd hj (by simp [MProg.init]), rfl, hp⟩
  · intro r
    show (if r = 0 then 0 else (((List.range 32).map (fun r => P.reg0 h r % two64))[r]?).getD 0) =
      (if 0 < r ∧ r < 32 then (P.reg0 h r % two64, ([] : List Nat)) else (0, [])).1
    by_cases h0 : r = 0
    · subst h0; simp
    · by_cases h32 : r < 32
      · rw [if_neg h0, if_pos ⟨Nat.pos_of_ne_zero h0, h32⟩]; simp [h32]
      · rw [if_neg h0, if_neg (fun h' => h32 h'.2)]; simp [h32]
  · intro r
    unfold Weak.Mini.MSt.rd MProg.init
    split
    · exact Nat.mod_lt _ (by decide)
    · decide
  · intro j _ hj hld w hwg hws _ hle
    have := vo_pos hC hwg hws
    exact absurd hle (by simp [msInit]; omega)

theorem run_hart (hwf : P.wf) (himm : P.immOk) (hC : miniCut P C) {h : Nat} (hh : h < P.harts.length)
    {H0 : MHart} (hI0 : Inv P C h (mrun P C.V h 0) H0) :
    ∀ k, k ≤ C.ks h → ∃ τ H', hSteps P (memL (C.evs P) C.g) h H0 τ H' ∧ Inv P C h (mrun P C.V h k) H' ∧
      ldVals (mrun P C.V h k).evs = loadVals τ
  | 0, _ => ⟨[], H0, .refl _, hI0, by simp [mrun, MProg.init, ldVals, loadVals]⟩
  | k + 1, hk => by
    obtain ⟨τ, H', hs, hI, hl⟩ := run_hart hwf himm hC hh hI0 k (by omega)
    obtain ⟨τ', H'', hs', hI', hl'⟩ := step_any hwf himm hC hh (by omega) hI
    exact ⟨τ ++ τ', H'', hs.trans hs', hI', by rw [hl', hl, loadVals_append]⟩

/-! ## 4. All harts -/

theorem mem_memL {m : MMsg} (hm : m ∈ memL (C.evs P) C.g) :
    ∃ w ∈ C.g, ((C.evs P).ev w).kind = .st ∧ m = msgOf (C.evs P) w := by
  unfold memL at hm
  obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hm
  exact ⟨w, (List.mem_filter.1 hw).1, by simpa using (List.mem_filter.1 hw).2, rfl⟩

theorem promOk (hC : miniCut P C) :
    ∀ m ∈ memL (C.evs P) C.g, m.tid < (mInit P).hs.length ∧ m.pa % P.sz = 0 ∧ m.v < wordW P := by
  intro m hm
  obtain ⟨w, hwg, hws, rfl⟩ := mem_memL hm
  have hwM := (mem_g hC w).1 hwg
  refine ⟨by simp [mInit, msgOf]; exact hwM.1.1, hC.2.2.1 w hwM, ?_⟩
  show ((C.evs P).ev w).v < 2 ^ (8 * P.sz)
  obtain ⟨h, j⟩ := w
  rw [ev_eq hwM.1.2]
  exact mrun_v P C.V h (C.ks h) _ (List.getElem_mem _)

/-- Hart `h`'s promise set after the promise phase: its stores' timestamps. -/
theorem prom_phase (hC : miniCut P C) {h : Nat} (hh : h < P.harts.length) (prom : List Nat)
    (hp : ∀ t, t ∈ prom ↔ t ∈ ([] : List Nat) ∨
      (([] : List MMsg).length < t ∧ ∃ m, ([] ++ memL (C.evs P) C.g)[t - 1]? = some m ∧ m.tid = h)) :
    ∀ t, t ∈ prom ↔ ∃ j, 0 ≤ j ∧ j < NN P C h ∧ kd P C h j = .st ∧ vo P C (h, j) = t := by
  intro t
  rw [hp t]
  simp only [List.not_mem_nil, false_or, List.length_nil, List.nil_append]
  constructor
  · rintro ⟨ht, m, hm, htid⟩
    obtain ⟨w, hwg, hws, hvo, rfl⟩ := memL_get C.g hC.1 hm
    have hwM := (mem_g hC w).1 hwg
    obtain ⟨h0, j⟩ := w
    simp only [msgOf] at htid; subst htid
    exact ⟨j, Nat.zero_le _, hwM.1.2, hws, by unfold vo; rw [hvo]; omega⟩
  · rintro ⟨j, _, hj, hs, rfl⟩
    have hg := mem_hj hC hh hj (.inr hs)
    obtain ⟨hpos, hget⟩ := voL_mem C.g hg hs
    exact ⟨hpos, _, hget, rfl⟩

end Cmp

/-- The proof of `mini_complete`. -/
theorem Cmp.completeRun (P : MProg) (hwf : P.wf) (himm : P.immOk) (C : MCut) (hC : miniCut P C) :
    ∃ r : MRun, miniValidRun P (cutMem P C) r ∧ (∀ h, loadVals (r.trace h) = cutLoads P C h) ∧
      ∃ c, mSteps P (mInit P) r.evs c ∧ ∀ h < P.harts.length, ∃ H, c.hs[h]? = some H ∧
        H.fr.pc = (C.st P h).pc ∧ ∀ reg, H.fr.rd reg = ((C.st P h).rd reg).1 := by
  obtain ⟨c1, hs1, hlog1, hlen1, hH1⟩ := promAll (memL (C.evs P) C.g) (mInit P) (promOk hC)
  have hlen0 : (mInit P).hs.length = P.harts.length := by simp [mInit]
  -- the state of hart `i` after the promise phase
  have hc1 : ∀ i < P.harts.length, ∃ prom, c1.hs[i]? = some ⟨⟨0, (List.range 32).map (fun r => P.reg0 i r % two64),
      []⟩, msInit, prom⟩ ∧ Inv P C i (mrun P C.V i 0) ⟨⟨0, (List.range 32).map (fun r => P.reg0 i r % two64), []⟩,
        msInit, prom⟩ := by
    intro i hi
    obtain ⟨prom, h1, h2⟩ := hH1 i ⟨⟨0, (List.range 32).map (fun r => P.reg0 i r % two64), []⟩, msInit, []⟩
      (by simp [mInit, hi])
    exact ⟨prom, h1, inv_init hC hi (prom_phase hC hi prom h2)⟩
  -- replay harts `0 … m-1`
  have hrep : ∀ m, m ≤ P.harts.length → ∃ es c, mSteps P c1 es c ∧ c.log = memL (C.evs P) C.g ∧
      c.hs.length = P.harts.length ∧
      (∀ i < m, ∃ H, c.hs[i]? = some H ∧ H.prom = [] ∧ H.fr.pc = (C.st P i).pc ∧
        ∀ reg, H.fr.rd reg = ((C.st P i).rd reg).1) ∧
      (∀ i, m ≤ i → c.hs[i]? = c1.hs[i]?) ∧
      (∀ i, loadVals (traceOf i es) = if i < m then cutLoads P C i else []) := by
    intro m
    induction m with
    | zero => exact fun _ => ⟨[], c1, .refl _, hlog1, by rw [hlen1, hlen0], fun i hi => absurd hi (by omega),
        fun _ _ => rfl, fun i => by simp [traceOf, loadVals]⟩
    | succ m ih =>
      intro hm
      obtain ⟨es, c, hs, hlog, hlen, hdone, hrest, htr⟩ := ih (by omega)
      obtain ⟨prom, hcm, hI0⟩ := hc1 m hm
      obtain ⟨τ, Hf, hsf, hIf, hlf⟩ := run_hart hwf himm hC hm hI0 (C.ks m) (Nat.le_refl _)
      have hcm' : c.hs[m]? = some _ := (hrest m (Nat.le_refl _)).trans hcm
      have hl := hSteps_lift hsf c.hs hcm'
      rw [← hlog] at hl
      refine ⟨es ++ stEvs m τ, _, mSteps_trans hs hl, hlog, by simp [hlen], ?_, ?_, ?_⟩
      · intro i hi
        by_cases him : i = m
        · subst him
          refine ⟨Hf, by simp [show i < c.hs.length by omega], ?_, hIf.pc, hIf.regs⟩
          apply List.eq_nil_iff_forall_not_mem.2
          intro t ht
          obtain ⟨j, hj1, hj2, _⟩ := (hIf.prom t).1 ht
          exact absurd hj2 (by unfold NN; unfold MCut.st; omega)
        · obtain ⟨H, h1, h2⟩ := hdone i (by omega)
          exact ⟨H, by rw [List.getElem?_set_ne (Ne.symm him)]; exact h1, h2⟩
      · intro i hi
        show (c.hs.set m Hf)[i]? = _
        rw [List.getElem?_set_ne (by omega)]; exact hrest i (by omega)
      · intro i
        rw [traceOf_append, loadVals_append, htr i, traceOf_stEvs]
        by_cases him : m = i
        · subst him; simp [hlf, cutLoads, MCut.st]
        · rw [if_neg him, loadVals]
          by_cases hi : i < m
          · simp [hi, show i < m + 1 by omega]
          · simp [hi, show ¬ i < m + 1 by omega]
  obtain ⟨es, c, hs, hlog, hlen, hdone, _, htr⟩ := hrep P.harts.length (Nat.le_refl _)
  refine ⟨⟨(memL (C.evs P) C.g).map (fun m => .prom m.tid m) ++ es⟩, ⟨c, mSteps_trans hs1 hs, ?_, hlog⟩, ?_,
    c, mSteps_trans hs1 hs, fun h hh => (hdone h hh).elim (fun H hH => ⟨H, hH.1, hH.2.2⟩)⟩
  · intro i H hH
    have hi : i < P.harts.length := by rw [← hlen]; exact (List.getElem?_eq_some_iff.1 hH).1
    obtain ⟨H', h1, h2, _⟩ := hdone i hi
    rw [hH] at h1; cases h1; exact h2
  · intro h
    show loadVals (traceOf h (_ ++ es)) = _
    rw [traceOf_append, traceOf_proms, List.nil_append, htr h]
    split
    · rfl
    · rename_i hh
      simp [cutLoads, ldVals, MCut.st, mrun_out P C.V (Nat.le_of_not_lt hh)]

/-- **L4 — COMPLETENESS (mini plan rev 4 §2 L4).**  Every finite execution `C` of a well-formed F program `P` (whose
ALU immediates are 64-bit values: part of `wf`, [MiniP3 (0)]) is a valid run of MiniMach: the run's memory is the cut's stores in gmo order,
every hart's load values are the cut's in program order, and every hart ends at the cut's pc with the cut's
register values (the run follows each hart's path through the program's own text: no unrolling). -/
theorem mini_complete (P : MProg) (hwf : P.wf) (C : MCut) (hC : miniCut P C) :
    ∃ r : MRun, miniValidRun P (cutMem P C) r ∧ (∀ h, loadVals (r.trace h) = cutLoads P C h) ∧
      ∃ c, mSteps P (mInit P) r.evs c ∧ ∀ h < P.harts.length, ∃ H, c.hs[h]? = some H ∧
        H.fr.pc = (C.st P h).pc ∧ ∀ reg, H.fr.rd reg = ((C.st P h).rd reg).1 :=
  Cmp.completeRun P hwf hwf.immOk C hC  -- [MiniP3 (0)]: `immOk` is now part of `wf`

end Weak.Mini
