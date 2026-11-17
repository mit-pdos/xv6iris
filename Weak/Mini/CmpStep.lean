/-
Weak/Mini: **L4 MiniCmp — one instruction simulated** (mini plan rev 4 §2 L4; Pulte AtoP.v `sim_step`).

For each instruction of F, from a state related by `Inv` (CmpInv.lean) the machine hart takes the instruction's
labels (the load answering the timestamp of the store the cut's load reads, the store fulfilling its own promise)
and reaches a state related to the reference's next state; the trace's load values are the new event's.
The context `SC` collects what the reference run says about the step (well-formedness, the new event is the
cut's event, later events' control dependencies).
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Mini.CmpRules

namespace Weak.Mini.Cmp

open Weak.Mini Weak.Mini.Mach

/-- The load values of an event list, in order. -/
def ldVals (l : List MEv) : List Nat := l.filterMap (fun e => if e.kind = .ld then some e.v else none)

/-- EVERY ALU IMMEDIATE IS A 64-BIT VALUE.  Needed: on `slti`/`sltiu` (`alui .slt`/`.sltu`) the reference compares
`imm % 2^64` (Ref.lean `exec`) and the machine compares `imm` (Mach.lean `instrNext`, as machine v2's
MachCert `instrNext`); for `imm ≥ 2^64` they disagree. -/
def _root_.Weak.Mini.MProg.immOk (P : MProg) : Prop :=
  ∀ h, ∀ i ∈ P.prog h, ∀ op rd rs1 imm, i = MI.alui op rd rs1 imm → imm < two64

variable {P : MProg} {C : MCut}

/-- What the reference run says about one step `s → s'` of hart `h` of the cut. -/
structure SC (P : MProg) (C : MCut) (h : Nat) (s s' : Weak.Mini.MSt) : Prop where
  wf : RunWf s
  taint : ∀ i, ldAt s.evs i → i < s.evs.length ∧ kd P C h i = .ld ∧ i < NN P C h
  next : ∀ e, s'.evs = s.evs ++ [e] → (C.evs P).ev (h, s.evs.length) = e ∧ s.evs.length < NN P C h
  cdep : ∀ j, s'.evs.length ≤ j → j < NN P C h → (kd P C h j = .ld ∨ kd P C h j = .st) →
    ∀ x ∈ s'.ctl, x ∈ ((C.evs P).ev (h, j)).cdep

/-- One instruction simulated. -/
def StepOk (P : MProg) (C : MCut) (h : Nat) (s s' : Weak.Mini.MSt) (H : MHart) : Prop :=
  ∃ τ H', hSteps P (memL (C.evs P) C.g) h H τ H' ∧ Inv P C h s' H' ∧ ldVals s'.evs = ldVals s.evs ++ loadVals τ

section steps

variable (hC : miniCut P C) {h : Nat} (hh : h < P.harts.length)
include hC hh

theorem mem_hj {j : Nat} (hj : j < NN P C h) (hk : kd P C h j = .ld ∨ kd P C h j = .st) : (h, j) ∈ C.g :=
  (mem_g hC _).2 (isMem_hj hh hj hk)

omit hh in
theorem le_vo_of {j : Nat} {Q : Nat → Prop} {v : Nat} (hd : dom P C h Q v)
    (hQ : ∀ i, Q i → (C.evs P).gmo (h, i) (h, j)) : v ≤ vo P C (h, j) :=
  dom_le hd (fun i hi => vo_gmo_le hC (hQ i hi))

theorem lt_vo_of {j : Nat} (hj : j < NN P C h) (hst : kd P C h j = .st) {Q : Nat → Prop} {v : Nat}
    (hd : dom P C h Q v) (hQ : ∀ i, Q i → (C.evs P).gmo (h, i) (h, j)) : v < vo P C (h, j) :=
  dom_lt hd (fun i hi => vo_gmo_st hC (hQ i hi) hst) (vo_pos hC (mem_hj hC hh hj (.inr hst)) hst)

/-! ## 1. Steps without memory events -/

/-- A register-writing ALU instruction. -/
theorem step_regw {s : Weak.Mini.MSt} {H : MHart} (hI : Inv P C h s H) {ins : MI}
    (hi : (P.prog h)[s.pc]? = some ins) {rd val : Nat} {srcs : List MSrc} {x : Nat × List Nat}
    (hn : ∀ l, instrNext P (P.prog h).length H.fr ins l =
      go1 H.fr (H.fr.wr rd val) (H.fr.pc + 1) (regWL rd srcs ++ [MLab.instr]) l)
    (hval : val % two64 = x.1) (hx : x.1 < two64) (hdom : dom P C h (· ∈ x.2) (srcsView H.ws srcs)) :
    StepOk P C h s (s.wr rd x).adv H := by
  obtain ⟨l0, rest, hl⟩ := regWL_cons rd srcs
  have haf := regWL_af rd srcs
  rw [hl] at haf hn
  have hs := hSteps_go1 (log := memL (C.evs P) C.g) hI.q (hI.pc ▸ hi) (hn l0) haf
  refine ⟨_, _, hs, ?_, ?_⟩
  · rw [← hl, foldl_regWL]
    obtain ⟨_, he, _, _⟩ := wr_same s rd x
    refine inv_nomem hI (by simp [MSt.adv, he]) (by simp [MSt.adv, (wr_same s rd x).1, hI.pc]) rfl
      (by rw [front_wr_len, hI.len]) (regs_wr2 hI.len hI.regs _ _ rd val x hval)
      (regLt_wr hI.regLt rd x hx) ?_ hI.vcap rfl rfl rfl rfl rfl rfl rfl rfl
    intro r h0 h32
    show dom P C h (· ∈ ((s.wr rd x).rd r).2) (if rd ≠ 0 ∧ r = rd then srcsView H.ws srcs else H.ws.regv r)
    rw [Cmp.rd_wr]
    by_cases hr : r = rd
    · subst hr
      rw [if_pos (show r ≠ 0 ∧ r = r from ⟨by omega, rfl⟩), if_pos (show 0 < r ∧ r < 32 ∧ r = r from ⟨h0, h32, rfl⟩)]
      exact hdom
    · rw [if_neg (show ¬ (rd ≠ 0 ∧ r = rd) from fun h' => hr h'.2),
        if_neg (show ¬ (0 < rd ∧ rd < 32 ∧ r = rd) from fun h' => hr h'.2.2)]
      exact hI.regv r h0 h32
  · rw [loadVals_af _ haf]; simp [MSt.adv, (wr_same s rd x).2.1]

/-- An instruction emitting only the boundary label (`jal x0`, `nop`). -/
theorem step_instr {s s' : Weak.Mini.MSt} {H : MHart} (hI : Inv P C h s H) {ins : MI}
    (hi : (P.prog h)[s.pc]? = some ins) {pc' : Nat}
    (hn : ∀ l, instrNext P (P.prog h).length H.fr ins l = go1 H.fr H.fr.regs pc' [MLab.instr] l)
    (hevs : s'.evs = s.evs) (hregs : s'.regs = s.regs) (hpc : s'.pc = pc') : StepOk P C h s s' H := by
  have haf : ∀ l ∈ [MLab.instr], AF l := by simp [AF]
  have hs := hSteps_go1 (log := memL (C.evs P) C.g) hI.q (hI.pc ▸ hi) (hn .instr) haf
  have hrd : ∀ r, s'.rd r = s.rd r := fun r => by unfold Weak.Mini.MSt.rd; rw [hregs]
  refine ⟨_, _, hs, ?_, ?_⟩
  · refine inv_nomem hI hevs hpc.symm rfl hI.len (fun r => by rw [front_rd_same, hrd]; exact hI.regs r)
      (fun r => by rw [hrd]; exact hI.regLt r) (fun r h0 h32 => by rw [hrd]; exact hI.regv r h0 h32) hI.vcap
      rfl rfl rfl rfl rfl rfl rfl rfl
  · rw [loadVals_af _ haf, hevs]; simp

/-- A branch: the control label raises `vcap` by the sources' views (rule 11). -/
theorem step_br (hwf : P.wf) {s : Weak.Mini.MSt} {H : MHart} (hI : Inv P C h s H) {c : MBrC} {rs1 rs2 tgt : Nat}
    (hi : (P.prog h)[s.pc]? = some (.br c rs1 rs2 tgt)) (hX : SC P C h s (exec P.sz h C.V s (.br c rs1 rs2 tgt))) :
    StepOk P C h s (exec P.sz h C.V s (.br c rs1 rs2 tgt)) H := by
  have hmem := List.mem_of_getElem? hi
  have htgt : tgt ≤ (P.prog h).length := (hwf.2.2 h _ hmem).1
  have hreg : rs1 < 32 ∧ rs2 < 32 := (hwf.2.2 h _ hmem).2
  rcases h1 : s.rd rs1 with ⟨v1, t1⟩
  rcases h2 : s.rd rs2 with ⟨v2, t2⟩
  have hex : exec P.sz h C.V s (.br c rs1 rs2 tgt) =
      { s with pc := if c.eval v1 v2 then tgt else s.pc + 1, ii := s.ii + 1, ctl := s.ctl ++ t1 ++ t2 } := by
    simp [exec, h1, h2]
  rw [hex] at hX ⊢
  have haf : ∀ l ∈ [MLab.ctrl (srcR rs1 ++ srcR rs2), MLab.instr], AF l := by simp [AF]
  have hr1 : H.fr.rd rs1 = v1 := by rw [hI.regs, h1]
  have hr2 : H.fr.rd rs2 = v2 := by rw [hI.regs, h2]
  have hs := hSteps_go1 (log := memL (C.evs P) C.g) (regs' := H.fr.regs)
    (pc' := if c.eval v1 v2 then tgt else H.fr.pc + 1) hI.q (hI.pc ▸ hi)
    (by simp only [instrNext, Nat.not_lt.2 htgt, if_false, hr1, hr2]) haf
  refine ⟨_, _, hs, ?_, ?_⟩
  · refine inv_nomem hI rfl (by simp [hI.pc]) rfl hI.len (fun r => by rw [front_rd_same]; exact hI.regs r)
      hI.regLt hI.regv ?_ rfl rfl rfl rfl rfl rfl rfl rfl
    intro j hj1 hj2 hst
    show max (srcsView H.ws (srcR rs1 ++ srcR rs2)) H.ws.vcap < _
    refine Nat.max_lt.2 ⟨?_, hI.vcap j hj1 hj2 hst⟩
    rw [srcsView_append]
    have d1 := dom_srcR hI.regv hreg.1; rw [h1] at d1
    have d2 := dom_srcR hI.regv hreg.2; rw [h2] at d2
    have hd : dom P C h (· ∈ t1 ++ t2) (max (srcsView H.ws (srcR rs1)) (srcsView H.ws (srcR rs2))) :=
      dom_max (dom_mono d1 (fun i hi => List.mem_append_left _ hi))
        (dom_mono d2 (fun i hi => List.mem_append_right _ hi))
    refine lt_vo_of hC hh hj2 hst hd (fun i hi => ?_)
    have hld : ldAt s.evs i := by
      rcases List.mem_append.1 hi with hi | hi
      · exact hX.wf.rd rs1 i (by rw [h1]; exact hi)
      · exact hX.wf.rd rs2 i (by rw [h2]; exact hi)
    obtain ⟨hin, hik, hiN⟩ := hX.taint i hld
    have hcd := hX.cdep j hj1 hj2 (.inr hst) i (by simp only [List.append_assoc]; exact List.mem_append_right _ hi)
    exact gmo_r11 hC (isMem_hj hh hiN (.inl hik)) (isMem_hj hh hj2 (.inr hst)) (po_hj (by omega) hj2) hst hcd
  · rw [loadVals_af _ haf]; simp

/-! ## 2. FENCE -/

/-- FENCE pred,succ: raises `vrNew`/`vwNew` by the old views of the predecessor kinds (rule 4). -/
theorem step_fence {s : Weak.Mini.MSt} {H : MHart} (hI : Inv P C h s H) {f : MFence}
    (hi : (P.prog h)[s.pc]? = some (.fence f)) (hX : SC P C h s (exec P.sz h C.V s (.fence f))) :
    StepOk P C h s (exec P.sz h C.V s (.fence f)) H := by
  have hex : exec P.sz h C.V s (.fence f) = (s.emit ⟨.fence f, s.ii, 0, 0, [], [], []⟩).adv := rfl
  rw [hex] at hX ⊢
  obtain ⟨hev, hnN⟩ := hX.next _ rfl
  have hkd : kd P C h s.evs.length = .fence f := by unfold kd; rw [hev]
  have haf : ∀ l ∈ [MLab.fence f.pr f.pw f.sr f.sw, MLab.instr], AF l := by simp [AF]
  have hs := hSteps_go1 (log := memL (C.evs P) C.g) (regs' := H.fr.regs) (pc' := H.fr.pc + 1) hI.q (hI.pc ▸ hi)
    (by simp only [instrNext]) haf
  have hlen : ((s.emit ⟨.fence f, s.ii, 0, 0, [], [], []⟩).adv).evs.length = s.evs.length + 1 := by
    simp [MSt.adv, MSt.emit]
  have hm : (C.evs P).has (h, s.evs.length) := ⟨hh, hnN⟩
  -- rule 4 from a past event to a future one
  have hr4 : ∀ i j, i < s.evs.length → s.evs.length + 1 ≤ j → j < NN P C h →
      (kd P C h i = .ld ∧ f.pr = true ∨ kd P C h i = .st ∧ f.pw = true) →
      (kd P C h j = .ld ∧ f.sr = true ∨ kd P C h j = .st ∧ f.sw = true) →
      (C.evs P).gmo (h, i) (h, j) := by
    intro i j hi1 hj1 hj2 hpi hsj
    have hiN : i < NN P C h := by omega
    exact gmo_r4 hC (isMem_hj hh hiN (by rcases hpi with h | h; exact .inl h.1; exact .inr h.1))
      (isMem_hj hh hj2 (by rcases hsj with h | h; exact .inl h.1; exact .inr h.1)) (po_hj (by omega) hj2) hm hkd
      (po_hj hi1 hnN) (po_hj (by omega) hj2) hpi hsj
  refine ⟨_, _, hs, ?_, ?_⟩
  · simp only [List.foldl_cons, List.foldl_nil, eff]
    refine ⟨by simp [MSt.adv, MSt.emit, hI.pc], rfl, hI.len, fun r => by rw [front_rd_same]; exact hI.regs r, hI.regLt,
      hI.regv, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl, ?_⟩
    · rw [hlen]; exact dom_mono hI.vrOld (fun j hj => ⟨by omega, hj.2⟩)
    · rw [hlen]; exact dom_mono hI.vwOld (fun j hj => ⟨by omega, hj.2⟩)
    · rw [hlen]; intro j hj1 hj2 hld
      show (if f.sr then max H.ws.vrNew _ else H.ws.vrNew) ≤ _
      have h0 := hI.vrNew j (by omega) hj2 hld
      split
      · rename_i hsr
        refine Nat.max_le.2 ⟨h0, Nat.max_le.2 ⟨?_, ?_⟩⟩
        · split
          · rename_i hpr
            exact le_vo_of hC hI.vrOld (fun i hi => hr4 i j hi.1 hj1 hj2 (.inl ⟨hi.2, hpr⟩) (.inl ⟨hld, hsr⟩))
          · exact Nat.zero_le _
        · split
          · rename_i hpw
            exact le_vo_of hC hI.vwOld (fun i hi => hr4 i j hi.1 hj1 hj2 (.inr ⟨hi.2, hpw⟩) (.inl ⟨hld, hsr⟩))
          · exact Nat.zero_le _
      · exact h0
    · rw [hlen]; intro j hj1 hj2 hst
      show (if f.sw then max H.ws.vwNew _ else H.ws.vwNew) < _
      have h0 := hI.vwNew j (by omega) hj2 hst
      split
      · rename_i hsw
        refine Nat.max_lt.2 ⟨h0, Nat.max_lt.2 ⟨?_, ?_⟩⟩
        · split
          · rename_i hpr
            exact lt_vo_of hC hh hj2 hst hI.vrOld
              (fun i hi => hr4 i j hi.1 hj1 hj2 (.inl ⟨hi.2, hpr⟩) (.inr ⟨hst, hsw⟩))
          · exact vo_pos hC (mem_hj hC hh hj2 (.inr hst)) hst
        · split
          · rename_i hpw
            exact lt_vo_of hC hh hj2 hst hI.vwOld
              (fun i hi => hr4 i j hi.1 hj1 hj2 (.inr ⟨hi.2, hpw⟩) (.inr ⟨hst, hsw⟩))
          · exact vo_pos hC (mem_hj hC hh hj2 (.inr hst)) hst
      · exact h0
    · rw [hlen]; intro j hj1 hj2 hst; exact hI.vcap j (by omega) hj2 hst
    · rw [hlen]; intro j hj1 hj2 hst; exact hI.coh1 j (by omega) hj2 hst
    · rw [hlen]; intro j hj1 hj2 hld; exact hI.coh2 j (by omega) hj2 hld
    · rw [hlen]; intro a; exact fwdOk_mono (hI.fwd a) (fun h' => by rw [hkd] at h'; cases h'.1)
    · rw [hlen]; exact prom_mono hI.prom (by rw [hkd]; intro h'; cases h')
  · rw [loadVals_af _ haf]; simp [ldVals, MSt.adv, MSt.emit, List.filterMap_append]

end steps

end Weak.Mini.Cmp
