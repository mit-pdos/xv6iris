/-
Weak/Mini: **E1, the program side** (mini plan rev 4 §2 L1 E1): MiniRef's concrete harts (Ref.lean §3) and the full
reference's symbolic loop front end (`stepL`, PfxDefs.lean) take the same steps.

* `replay T h ν` — the full front end REPLAYED along the branch outcomes under `ν` (at a fork, the side whose new
  path condition holds: `chosen`); this is `toFull`'s run (plan §2 L1 "`toFull` REPLAYS `stepL` along X's branch
  outcomes").
* `SimSt` — a mini state and a full symbolic state agree: same pc, instruction index, control taint; every register's
  expression evaluates under `ν` to the mini value, with the same taint; the events agree (`SimEv`: the same skeleton,
  the address evaluates to the mini address, a store's value to the mini value modulo `2^(8 sz)`, a load's mini value
  is `V` modulo `2^(8 sz)`), provided `V` and `ν` agree on every load's value (`Agree`).
* `sim_exec` — one F instruction keeps `SimSt`, and the full side's chosen successor keeps the path conditions.
* `sim_run` — any full run whose steps are the chosen ones is simulated by the mini run; `fstep_of_lstep` — an `LStep`
  run whose path conditions hold takes the chosen steps; `replay_sim` — so does the replay.
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Mini.EqRefBase

namespace Weak.Mini

open Weak.Prom.Ref
open Weak.Prom.Pfx

/-! ## 1. The replay -/

/-- The new path condition of a fork side holds under `ν`. -/
def forkOk (ν : Val) (t : SSt) : Bool :=
  match t.conds.getLast? with
  | some (c, a, b, v) => brEval c (a.eval ν) (b.eval ν) == v
  | none => true

/-- The successor the execution takes (a fork: the side whose condition holds). -/
def chosen (ν : Val) : StepR → Option SSt
  | .next s' => some s'
  | .fork t f => some (if forkOk ν t then t else f)
  | .stuck => none

/-- One replayed step (halted, or stuck: stay). -/
def rstep (p : List Instr) (h : Nat) (ν : Val) (s : SSt) : SSt :=
  match p[s.pc]? with
  | none => s
  | some i => (chosen ν (stepL h p.length s i)).getD s

/-- Hart `h`'s replayed run. -/
def replay (T : Test) (h : Nat) (ν : Val) : Nat → SSt
  | 0 => T.init h
  | k + 1 => rstep (T.prog h) h ν (replay T h ν k)

/-- The path conditions of `s` hold (the first half of RefProg.lean `condsOk`). -/
def condsHold (ν : Val) (s : SSt) : Bool := s.conds.all (fun (c, a, b, t) => brEval c (a.eval ν) (b.eval ν) == t)

/-- Every access of `s` is aligned (the second half of `condsOk`). -/
def evsAligned (ν : Val) (s : SSt) : Bool :=
  s.evs.all (fun se => !se.sk.kind.isAcc || (se.addr.eval ν % se.sk.sz == 0))

theorem condsOk_single (ν : Val) (s : SSt) : condsOk ν [s] = (condsHold ν s && evsAligned ν s) := by
  simp [condsOk, condsHold, evsAligned]

/-- A step that takes the chosen successor (or a halted hart staying). -/
def FStep (p : List Instr) (h : Nat) (ν : Val) (s s' : SSt) : Prop :=
  (s.pc = p.length ∧ s' = s) ∨ ∃ i, p[s.pc]? = some i ∧ chosen ν (stepL h p.length s i) = some s'

/-! ## 2. The simulation relation -/

/-- `V` and `ν` agree on the value of every load (`sz` bytes). -/
def Agree (sz : Nat) (V : EvId → Nat) (ν : Val) : Prop :=
  ∀ e, V e % 2 ^ (8 * sz) = bytesVal ((ν e).take sz) % 2 ^ (8 * sz)

structure SimEv (sz h i : Nat) (V : EvId → Nat) (ν : Val) (se : SEv) (me : MEv) : Prop where
  sk : se.sk = (me.toEv sz).sk
  pa : se.addr.eval ν = me.pa
  wv : me.kind = .st → se.wval.eval ν % 2 ^ (8 * sz) = me.v
  lv : me.kind = .ld → me.v = V (h, i) % 2 ^ (8 * sz)

structure SimSt (sz h : Nat) (V : EvId → Nat) (ν : Val) (m : MSt) (s : SSt) : Prop where
  pc : s.pc = m.pc
  ii : s.ii = m.ii
  ctl : s.ctl = m.ctl
  len : s.regs.length = 32
  rd : ∀ r, ((s.rd r).1.eval ν, (s.rd r).2) = m.rd r
  evl : s.evs.length = m.evs.length
  ev : ∀ i (h1 : i < s.evs.length) (h2 : i < m.evs.length), SimEv sz h i V ν s.evs[i] m.evs[i]

/-! ## 3. Register files -/

theorem sst_rd_wr {s : SSt} (hl : s.regs.length = 32) (r r' : Nat) (x : Ex × List Nat) :
    (s.wr r x).rd r' = if 0 < r ∧ r < 32 ∧ r' = r then x else s.rd r' := by
  by_cases h0 : r = 0
  · subst h0; simp [SSt.wr]
  · unfold SSt.wr SSt.rd
    rw [if_neg h0]
    simp only
    by_cases h1 : r' = 0
    · subst h1; simp only [if_true]; rw [if_neg (by omega)]
    · rw [if_neg h1, if_neg h1, List.getElem?_set]
      by_cases h2 : r = r'
      · subst h2
        by_cases h3 : r < 32
        · simp [hl, h3, h0]
        · simp [hl, h3]
      · simp only [h2, if_false]
        rw [if_neg (by omega)]

theorem sst_wr_len {s : SSt} (hl : s.regs.length = 32) (r : Nat) (x : Ex × List Nat) : (s.wr r x).regs.length = 32 := by
  unfold SSt.wr; split
  · exact hl
  · simp [hl]

theorem mst_rd_wr (m : MSt) (r r' : Nat) (x : Nat × List Nat) :
    (m.wr r x).rd r' = if 0 < r ∧ r < 32 ∧ r' = r then x else m.rd r' := by
  unfold MSt.wr MSt.rd
  by_cases h : 0 < r ∧ r < 32
  · rw [if_pos h]
    by_cases h' : r' = r
    · subst h'; simp [h]
    · simp [h']
  · rw [if_neg h]
    have : ¬ (0 < r ∧ r < 32 ∧ r' = r) := fun ⟨a, b, _⟩ => h ⟨a, b⟩
    rw [if_neg this]

theorem condsHold_wr (ν : Val) (s : SSt) (r : Nat) (x : Ex × List Nat) : condsHold ν (s.wr r x) = condsHold ν s := by
  unfold SSt.wr; split <;> rfl

theorem condsHold_snoc {ν : Val} {s' : SSt} {cs : List PCond} {c : BrC} {a b : Ex} {t : Bool}
    (hs : s'.conds = cs ++ [(c, a, b, t)]) :
    condsHold ν s' = (cs.all (fun (c, a, b, t) => brEval c (a.eval ν) (b.eval ν) == t) &&
      (brEval c (a.eval ν) (b.eval ν) == t)) := by
  unfold condsHold; rw [hs, List.all_append]; simp

theorem condsHold_adv (ν : Val) (s : SSt) : condsHold ν s.adv = condsHold ν s := rfl

theorem condsHold_emit (ν : Val) (s : SSt) (se : SEv) : condsHold ν (s.emit se) = condsHold ν s := rfl

/-! ## 4. Simulation combinators -/

section comb

variable {sz h : Nat} {V : EvId → Nat} {ν : Val} {m : MSt} {s : SSt}

theorem sim_wr (H : SimSt sz h V ν m s) (r : Nat) {x : Ex × List Nat} {y : Nat × List Nat}
    (hxy : (x.1.eval ν, x.2) = y) : SimSt sz h V ν (m.wr r y) (s.wr r x) := by
  have hpc : (s.wr r x).pc = s.pc := by unfold SSt.wr; split <;> rfl
  have hii : (s.wr r x).ii = s.ii := by unfold SSt.wr; split <;> rfl
  have hctl : (s.wr r x).ctl = s.ctl := by unfold SSt.wr; split <;> rfl
  have hev : (s.wr r x).evs = s.evs := by unfold SSt.wr; split <;> rfl
  have mpc : (m.wr r y).pc = m.pc := by unfold MSt.wr; split <;> rfl
  have mii : (m.wr r y).ii = m.ii := by unfold MSt.wr; split <;> rfl
  have mctl : (m.wr r y).ctl = m.ctl := by unfold MSt.wr; split <;> rfl
  have mev : (m.wr r y).evs = m.evs := by unfold MSt.wr; split <;> rfl
  refine ⟨by rw [hpc, mpc, H.pc], by rw [hii, mii, H.ii], by rw [hctl, mctl, H.ctl], sst_wr_len H.len r x,
    fun r' => ?_, by rw [hev, mev, H.evl], fun i h1 h2 => ?_⟩
  · rw [sst_rd_wr H.len, mst_rd_wr]
    split
    · exact hxy
    · exact H.rd r'
  · simp only [hev, mev] at h1 h2 ⊢
    exact H.ev i h1 h2

theorem sim_adv (H : SimSt sz h V ν m s) : SimSt sz h V ν m.adv s.adv :=
  ⟨by simp [SSt.adv, MSt.adv, H.pc], by simp [SSt.adv, MSt.adv, H.ii], H.ctl, H.len, H.rd, H.evl, H.ev⟩

theorem sim_emit (H : SimSt sz h V ν m s) {se : SEv} {me : MEv} (he : SimEv sz h s.evs.length V ν se me) :
    SimSt sz h V ν (m.emit me) (s.emit se) := by
  refine ⟨H.pc, H.ii, H.ctl, H.len, H.rd, by simp [SSt.emit, MSt.emit, H.evl], fun i h1 h2 => ?_⟩
  simp only [SSt.emit, MSt.emit, List.length_append, List.length_singleton] at h1 h2 ⊢
  by_cases hi : i < s.evs.length
  · rw [List.getElem_append_left hi, List.getElem_append_left (by rw [← H.evl]; exact hi)]
    exact H.ev i hi _
  · have hi' : i = s.evs.length := by omega
    subst hi'
    rw [List.getElem_concat_length rfl, List.getElem_concat_length H.evl]
    exact he

end comb

/-! ## 5. One instruction -/

theorem aluOp_eq (op : MAlu) (a b : Nat) : aluOp op.toAlu a b = op.eval a b := by cases op <;> rfl

theorem brEval_eq (c : MBrC) (a b : Nat) : brEval c.toBrC a b = c.eval a b := by cases c <;> rfl

theorem sext_eq (sz v : Nat) : Weak.Prom.Ref.sext sz v = Weak.Mini.sext sz v := rfl

theorem two64_eq : Weak.Prom.Ref.two64 = Weak.Mini.two64 := rfl

theorem getLast_conds (l : List PCond) (x : PCond) : (l ++ [x]).getLast? = some x := List.getLast?_concat

section step

variable {sz h : Nat} {V : EvId → Nat} {ν : Val} {m : MSt} {s : SSt}

/-- **One F instruction**: the full side's chosen successor exists, is simulated by the mini step, and keeps the
path conditions. -/
theorem sim_exec (hA : Agree sz V ν) (H : SimSt sz h V ν m s) (n : Nat) (mi : MI) (hok : mi.tgtOk n) :
    ∃ s', chosen ν (stepL h n s (mi.toInstr sz)) = some s' ∧ SimSt sz h V ν (exec sz h V m mi) s' ∧
      (condsHold ν s = true → condsHold ν s' = true) := by
  cases mi with
  | alui op rd rs1 imm =>
    have e1 : stepL h n s (MI.toInstr sz (.alui op rd rs1 imm)) =
        .next ((s.wr rd (.bin op.toAlu (s.rd rs1).1 (.c imm), (s.rd rs1).2)).adv) := rfl
    have e2 : exec sz h V m (.alui op rd rs1 imm) = (m.wr rd (op.eval (m.rd rs1).1 (imm % two64), (m.rd rs1).2)).adv :=
      rfl
    rw [e1, e2]
    refine ⟨_, rfl, sim_adv (sim_wr H rd ?_), fun hc => by rw [condsHold_adv, condsHold_wr]; exact hc⟩
    have := H.rd rs1
    rw [← this]
    simp only [Ex.eval, aluOp_eq, two64_eq]
  | alu op rd rs1 rs2 =>
    have e1 : stepL h n s (MI.toInstr sz (.alu op rd rs1 rs2)) =
        .next ((s.wr rd (.bin op.toAlu (s.rd rs1).1 (s.rd rs2).1, (s.rd rs1).2 ++ (s.rd rs2).2)).adv) := rfl
    have e2 : exec sz h V m (.alu op rd rs1 rs2) =
        (m.wr rd (op.eval (m.rd rs1).1 (m.rd rs2).1, (m.rd rs1).2 ++ (m.rd rs2).2)).adv := rfl
    rw [e1, e2]
    refine ⟨_, rfl, sim_adv (sim_wr H rd ?_), fun hc => by rw [condsHold_adv, condsHold_wr]; exact hc⟩
    have h1 := H.rd rs1; have h2 := H.rd rs2
    rw [← h1, ← h2]
    simp only [Ex.eval, aluOp_eq]
  | load sgn rd rs1 off =>
    have e1 : stepL h n s (MI.toInstr sz (.load sgn rd rs1 off)) =
        .next (((s.emit ⟨{ kind := .ld, ii := s.ii, sz := sz, adep := (s.rd rs1).2, cdep := s.ctl },
          .bin .add (s.rd rs1).1 (.c off), .c 0⟩).wr rd (.ld (h, s.evs.length) sz sgn, [s.evs.length])).adv) := rfl
    have e2 : exec sz h V m (.load sgn rd rs1 off) =
        ((m.emit ⟨.ld, m.ii, MAlu.add.eval (m.rd rs1).1 (off % two64), V (h, m.evs.length) % 2 ^ (8 * sz),
          (m.rd rs1).2, [], m.ctl⟩).wr rd (ldExt sz sgn (V (h, m.evs.length) % 2 ^ (8 * sz)),
            [m.evs.length])).adv := rfl
    rw [e1, e2]
    refine ⟨_, rfl, sim_adv (sim_wr (sim_emit H ?_) rd ?_),
      fun hc => by rw [condsHold_adv, condsHold_wr, condsHold_emit]; exact hc⟩
    · have h1 := H.rd rs1
      refine ⟨?_, ?_, (fun hk => by cases hk), fun _ => ?_⟩
      · simp only [MEv.toEv, MK.toKind, MK.szOf]; rw [H.ii, H.ctl, ← h1]
      · rw [← h1]; rfl
      · rw [H.evl]
    · simp only [Ex.eval]
      rw [H.evl, ← hA, sext_eq]
      rfl
  | store rs2 rs1 off =>
    have e1 : stepL h n s (MI.toInstr sz (.store rs2 rs1 off)) = .next ((s.emit
        ⟨{ kind := .st, ii := s.ii, sz := sz, adep := (s.rd rs1).2, ddep := (s.rd rs2).2, cdep := s.ctl },
          .bin .add (s.rd rs1).1 (.c off), (s.rd rs2).1⟩).adv) := rfl
    have e2 : exec sz h V m (.store rs2 rs1 off) =
        (m.emit ⟨.st, m.ii, MAlu.add.eval (m.rd rs1).1 (off % two64), (m.rd rs2).1 % 2 ^ (8 * sz),
          (m.rd rs1).2, (m.rd rs2).2, m.ctl⟩).adv := rfl
    rw [e1, e2]
    refine ⟨_, rfl, sim_adv (sim_emit H ?_), fun hc => hc⟩
    have h1 := H.rd rs1; have h2 := H.rd rs2
    refine ⟨?_, ?_, fun _ => ?_, (fun hk => by cases hk)⟩
    · simp only [MEv.toEv, MK.toKind, MK.szOf]; rw [H.ii, H.ctl, ← h1, ← h2]
    · rw [← h1]; rfl
    · rw [← h2]
  | fence f =>
    have e1 : stepL h n s (MI.toInstr sz (.fence f)) =
        .next ((s.emit ⟨{ kind := .fence f.toFenceSet, ii := s.ii, sz := 0 }, .c 0, .c 0⟩).adv) := rfl
    have e2 : exec sz h V m (.fence f) = (m.emit ⟨.fence f, m.ii, 0, 0, [], [], []⟩).adv := rfl
    rw [e1, e2]
    refine ⟨_, rfl, sim_adv (sim_emit H ⟨?_, rfl, (fun hk => by cases hk), (fun hk => by cases hk)⟩), fun hc => hc⟩
    simp only [MEv.toEv, MK.toKind, MK.szOf]; rw [H.ii]
  | br c rs1 rs2 tgt =>
    simp only [MI.tgtOk] at hok
    have h1 := H.rd rs1; have h2 := H.rd rs2
    have hb : brEval c.toBrC ((s.rd rs1).1.eval ν) ((s.rd rs2).1.eval ν) = c.eval (m.rd rs1).1 (m.rd rs2).1 := by
      rw [brEval_eq, ← h1, ← h2]
    have hstep : stepL h n s (MI.toInstr sz (.br c rs1 rs2 tgt)) =
        .fork { s with ii := s.ii + 1, ctl := s.ctl ++ (s.rd rs1).2 ++ (s.rd rs2).2, pc := tgt,
                       conds := s.conds ++ [(c.toBrC, (s.rd rs1).1, (s.rd rs2).1, true)] }
              { s with ii := s.ii + 1, ctl := s.ctl ++ (s.rd rs1).2 ++ (s.rd rs2).2, pc := s.pc + 1,
                       conds := s.conds ++ [(c.toBrC, (s.rd rs1).1, (s.rd rs2).1, false)] } := by
      simp only [MI.toInstr, stepL, if_neg (Nat.not_lt.2 hok)]
    rw [hstep]
    simp only [chosen, forkOk, getLast_conds, hb]
    have hsim : ∀ (p : Nat) (cs : List PCond), p = (if c.eval (m.rd rs1).1 (m.rd rs2).1 then tgt else m.pc + 1) →
        SimSt sz h V ν (exec sz h V m (.br c rs1 rs2 tgt))
          { s with ii := s.ii + 1, ctl := s.ctl ++ (s.rd rs1).2 ++ (s.rd rs2).2, pc := p, conds := cs } := by
      intro p cs hp
      refine ⟨hp, by simp [exec, H.ii], ?_, H.len, H.rd, H.evl, H.ev⟩
      simp only [exec]; rw [H.ctl, ← congrArg Prod.snd h1, ← congrArg Prod.snd h2]
    cases hc : c.eval (m.rd rs1).1 (m.rd rs2).1
    · refine ⟨_, rfl, hsim _ _ (by simp [hc, H.pc]), fun hh => ?_⟩
      rw [condsHold_snoc rfl]; unfold condsHold at hh; rw [hh, hb, hc]; rfl
    · refine ⟨_, rfl, hsim _ _ (by simp [hc]), fun hh => ?_⟩
      rw [condsHold_snoc rfl]; unfold condsHold at hh; rw [hh, hb, hc]; rfl
  | jmp tgt =>
    simp only [MI.tgtOk] at hok
    have e1 : stepL h n s (MI.toInstr sz (.jmp tgt)) = .next { s with pc := tgt, ii := s.ii + 1 } := by
      simp only [MI.toInstr, stepL, if_neg (Nat.not_lt.2 hok)]
    have e2 : exec sz h V m (.jmp tgt) = { m with pc := tgt, ii := m.ii + 1 } := rfl
    rw [e1, e2]
    exact ⟨_, rfl, ⟨rfl, by simp [H.ii], H.ctl, H.len, H.rd, H.evl, H.ev⟩, fun hc => hc⟩
  | nop =>
    have e1 : stepL h n s (MI.toInstr sz .nop) = .next s.adv := rfl
    have e2 : exec sz h V m .nop = m.adv := rfl
    rw [e1, e2]
    exact ⟨_, rfl, sim_adv H, fun hc => hc⟩

/-- An `LStep` successor of an F instruction whose path conditions hold is the chosen one. -/
theorem chosen_of_lstep (n : Nat) (mi : MI) {s' : SSt}
    (hs : stepL h n s (mi.toInstr sz) = .next s' ∨
      ∃ t f, stepL h n s (mi.toInstr sz) = .fork t f ∧ (s' = t ∨ s' = f))
    (hc : condsHold ν s' = true) : chosen ν (stepL h n s (mi.toInstr sz)) = some s' := by
  rcases hs with hs | ⟨t, f, hs, ht⟩
  · rw [hs]; rfl
  · rw [hs]
    cases mi with
    | br c rs1 rs2 tgt =>
      simp only [MI.toInstr, stepL] at hs
      split at hs
      · cases hs
      · simp only [StepR.fork.injEq] at hs
        obtain ⟨rfl, rfl⟩ := hs
        simp only [chosen, forkOk, getLast_conds]
        rcases ht with rfl | rfl
        · rw [condsHold_snoc rfl, Bool.and_eq_true, beq_iff_eq] at hc
          rw [hc.2]; rfl
        · rw [condsHold_snoc rfl, Bool.and_eq_true, beq_iff_eq] at hc
          rw [hc.2]; rfl
    | jmp tgt =>
      simp only [MI.toInstr, stepL] at hs; split at hs <;> cases hs
    | _ => cases hs

end step

/-! ## 6. Runs -/

theorem prog_toTest (P : MProg) (cond : OC) (h : Nat) :
    (P.toTest cond).prog h = (P.prog h).map (MI.toInstr P.sz) := by
  simp only [Test.prog, MProg.toTest, MProg.prog, List.getElem?_map]
  cases P.harts[h]? <;> rfl

theorem sim_init (P : MProg) (cond : OC) (h : Nat) (V : EvId → Nat) (ν : Val) :
    SimSt P.sz h V ν (P.init h) ((P.toTest cond).init h) := by
  refine ⟨rfl, rfl, rfl, by simp [Test.init], fun r => ?_, rfl, fun i h1 => by simp [Test.init] at h1⟩
  simp only [Test.init, SSt.rd, MSt.rd, MProg.init, MProg.reg0, MProg.toTest]
  by_cases h0 : r = 0
  · subst h0; simp; rfl
  · rw [if_neg h0]
    by_cases h32 : r < 32
    · rw [if_pos ⟨Nat.pos_of_ne_zero h0, h32⟩]
      simp [h32, Ex.eval, two64_eq]
    · rw [if_neg (fun h => h32 h.2), List.getElem?_eq_none (by simp; omega)]
      rfl

/-- Every instruction of hart `h` has its targets inside the text. -/
def TgtOk (P : MProg) (h : Nat) : Prop := ∀ i ∈ P.prog h, i.tgtOk (P.prog h).length

theorem sim_fstep {P : MProg} {cond : OC} {h : Nat} {V : EvId → Nat} {ν : Val} (hA : Agree P.sz V ν)
    (ht : TgtOk P h) {m : MSt} {s s' : SSt} (H : SimSt P.sz h V ν m s)
    (hs : FStep ((P.toTest cond).prog h) h ν s s') : SimSt P.sz h V ν (mstep P V h m) s' := by
  rw [prog_toTest] at hs
  rcases hs with ⟨hp, rfl⟩ | ⟨i, hi, hc⟩
  · have : (P.prog h)[m.pc]? = none := by
      rw [List.length_map] at hp; rw [← H.pc, hp]; simp
    unfold mstep; rw [this]; exact H
  · rw [List.getElem?_map] at hi
    cases hmi : (P.prog h)[s.pc]? with
    | none => rw [hmi] at hi; cases hi
    | some mi =>
      rw [hmi] at hi
      simp only [Option.map_some, Option.some.injEq] at hi
      subst hi
      have hmem : mi ∈ P.prog h := List.mem_of_getElem? hmi
      obtain ⟨s'', h1, h2, _⟩ := sim_exec hA H _ mi (ht mi hmem)
      rw [List.length_map, h1] at hc
      cases hc
      unfold mstep; rw [← H.pc, hmi]; exact h2

/-- **The mini run simulates every full run that takes the chosen steps.** -/
theorem sim_run {P : MProg} {cond : OC} {h : Nat} {V : EvId → Nat} {ν : Val} (hA : Agree P.sz V ν)
    (ht : TgtOk P h) (st : Nat → SSt) (h0 : st 0 = (P.toTest cond).init h)
    (hs : ∀ k, SimSt P.sz h V ν (mrun P V h k) (st k) → FStep ((P.toTest cond).prog h) h ν (st k) (st (k + 1))) :
    ∀ k, SimSt P.sz h V ν (mrun P V h k) (st k)
  | 0 => by rw [h0]; exact sim_init P cond h V ν
  | k + 1 => by
    have ih := sim_run hA ht st h0 hs k
    exact sim_fstep hA ht ih (hs k ih)

/-- An `LStep` whose successor's path conditions hold is a chosen step. -/
theorem fstep_of_lstep {P : MProg} {cond : OC} {h : Nat} {ν : Val} {s s' : SSt}
    (hl : LStep ((P.toTest cond).prog h) h s s') (hc : condsHold ν s' = true) :
    FStep ((P.toTest cond).prog h) h ν s s' := by
  rcases hl with h1 | ⟨i, hi, hs⟩
  · exact .inl h1
  · refine .inr ⟨i, hi, ?_⟩
    rw [prog_toTest, List.getElem?_map] at hi
    cases hmi : (P.prog h)[s.pc]? with
    | none => rw [hmi] at hi; cases hi
    | some mi =>
      rw [hmi] at hi
      simp only [Option.map_some, Option.some.injEq] at hi
      subst hi
      exact chosen_of_lstep _ mi hs hc

theorem mstep_pc_le {P : MProg} {V : EvId → Nat} {h : Nat} (ht : TgtOk P h) {m : MSt}
    (hm : m.pc ≤ (P.prog h).length) : (mstep P V h m).pc ≤ (P.prog h).length := by
  unfold mstep
  cases hmi : (P.prog h)[m.pc]? with
  | none => exact hm
  | some mi =>
    have hlt : m.pc < (P.prog h).length := (List.getElem?_eq_some_iff.1 hmi).1
    have hok := ht mi (List.mem_of_getElem? hmi)
    cases mi with
    | br c rs1 rs2 tgt =>
      simp only [MI.tgtOk] at hok
      simp only [exec]; split <;> omega
    | jmp tgt => simp only [MI.tgtOk] at hok; simp only [exec]; omega
    | alui => simp only [exec]; unfold MSt.wr; split <;> simp [MSt.adv] <;> omega
    | alu => simp only [exec]; unfold MSt.wr; split <;> simp [MSt.adv] <;> omega
    | load => simp only [exec]; unfold MSt.wr; split <;> simp [MSt.adv, MSt.emit] <;> omega
    | store => simp only [exec, MSt.adv, MSt.emit]; omega
    | fence => simp only [exec, MSt.adv, MSt.emit]; omega
    | nop => simp only [exec, MSt.adv]; omega

theorem mrun_pc_le {P : MProg} {V : EvId → Nat} {h : Nat} (ht : TgtOk P h) :
    ∀ k, (mrun P V h k).pc ≤ (P.prog h).length
  | 0 => Nat.zero_le _
  | k + 1 => mstep_pc_le ht (mrun_pc_le ht k)

/-- **The replay takes the chosen steps** and is simulated by the mini run; its path conditions hold. -/
theorem replay_sim {P : MProg} {cond : OC} {h : Nat} {V : EvId → Nat} {ν : Val} (hA : Agree P.sz V ν)
    (ht : TgtOk P h) : ∀ k, SimSt P.sz h V ν (mrun P V h k) (replay (P.toTest cond) h ν k) ∧
      FStep ((P.toTest cond).prog h) h ν (replay (P.toTest cond) h ν k) (replay (P.toTest cond) h ν (k + 1)) ∧
      condsHold ν (replay (P.toTest cond) h ν k) = true := by
  have hstep : ∀ k, SimSt P.sz h V ν (mrun P V h k) (replay (P.toTest cond) h ν k) →
      FStep ((P.toTest cond).prog h) h ν (replay (P.toTest cond) h ν k) (replay (P.toTest cond) h ν (k + 1)) ∧
      (condsHold ν (replay (P.toTest cond) h ν k) = true →
        condsHold ν (replay (P.toTest cond) h ν (k + 1)) = true) := by
    intro k H
    have hpc := mrun_pc_le (V := V) ht k
    rw [← H.pc] at hpc
    show FStep _ h ν _ (rstep _ h ν _) ∧ (_ → condsHold ν (rstep _ h ν _) = true)
    unfold rstep
    rw [prog_toTest, List.getElem?_map]
    cases hmi : (P.prog h)[(replay (P.toTest cond) h ν k).pc]? with
    | none =>
      have : (replay (P.toTest cond) h ν k).pc = (P.prog h).length := by
        rcases Nat.lt_or_eq_of_le hpc with hl | hl
        · rw [List.getElem?_eq_some_iff.2 ⟨hl, rfl⟩] at hmi; cases hmi
        · exact hl
      refine ⟨.inl ⟨by rw [List.length_map]; exact this, rfl⟩, id⟩
    | some mi =>
      simp only [Option.map_some, List.length_map]
      obtain ⟨s'', h1, _, h3⟩ := sim_exec hA H (P.prog h).length mi (ht mi (List.mem_of_getElem? hmi))
      rw [h1]
      refine ⟨.inr ⟨mi.toInstr P.sz, by rw [List.getElem?_map, hmi]; rfl, ?_⟩, h3⟩
      rw [List.length_map, h1]; rfl
  have hsim := sim_run hA ht (replay (P.toTest cond) h ν) rfl (fun k H => (hstep k H).1)
  intro k
  refine ⟨hsim k, (hstep k (hsim k)).1, ?_⟩
  induction k with
  | zero => rfl
  | succ k ih => exact (hstep k (hsim k)).2 ih

end Weak.Mini
