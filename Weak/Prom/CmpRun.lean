/-
Weak/Prom: **completeness S3a — the run assembly for `rvwmo_complete`** (plan rev 7 §0 "(T-cmp)", §6, §8 S3a;
the theorem itself is in Weak/Prom/CmpMain.lean).

    rvwmo_complete : progS3bB T = true → T.runAll chs = some trs → condsOk ν trs = true →
      rvwmoRef (conc T trs ν g) → singleSize (conc T trs ν g) → platformOrd (conc T trs ν g) →
      ∃ run, PF.validRun litStep (testImg T) () (progs T) (memOf (conc T trs ν g)) run ∧ promisesFirst run.evs ∧
        run.cfg.pcAgs.length = T.harts.length ∧ allDone run.cfg ∧ (∀ h, machRow (run.trace h) = refRow (conc T trs ν g) h) ∧
        (∀ h r, regOf run.cfg h r = finalReg trs ν h r) ∧
        (∀ a n, finalMem (testImg T) (memOf (conc T trs ν g)) a n = refFinalMem (conc T trs ν g) a n)

Every execution the REFERENCE allows (an execution of the litmus test `T` in RefProg.lean's sense: per-hart paths
`trs`, load values `ν`, a global memory order `g`, path conditions holding, `rvwmoRef`) of an S3b program (S3a's
subset plus Zalasr `l*.aq[rl]`/`s*.[aq]rl`, LR/SC, AMOs with every aq/rl combination; no I/O; NA-6 single-size) is a VALID RUN of machine v2 over the same program (MachCert.lean's
`litStep` on `progs T`) whose final memory is the execution's stores in gmo order, in PROMISES-FIRST form, in which
every hart finishes, with the SAME per-hart observations: the same answered bytes of every load in program order
(`machRow = refRow`; so `run.obsLoad = refObsLoad`, `obsLoad_eq`), the same final registers and the same final
memory.  No program-specific premise (kill criterion K3).

The run (Pulte AtoP.v): promise every message of `memOf X` in order (`promsRun`, MachFactor.lean), then run each
hart's reference path to completion, hart after hart (`sim_hart`, lifted by `solo_lift`).
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Prom.CmpSim

namespace Weak.Prom.Cmp

open MachCSL MachCSL.Stdpp Iris.Std
open Weak (Image Dsrc)
open Weak.Prom Weak.Prom.Mach Weak.Prom.Mach.Cert
open Weak.Prom.Ref
open PLabel

/-! ## 1. Paths -/

theorem runFrom_spec (T : Test) : ∀ (chs : List (List Bool)) (k : Nat) (trs : List SSt),
    T.runFrom k chs = some trs →
      trs.length = chs.length ∧ ∀ i (hi : i < trs.length), ∃ ch, T.runH (k + i) ch = some trs[i]
  | [], k, trs, H => by
    simp only [Test.runFrom, Option.some.injEq] at H
    subst H; exact ⟨rfl, fun i hi => absurd hi (by simp)⟩
  | c :: cs, k, trs, H => by
    unfold Test.runFrom at H
    cases h1 : T.runH k c with
    | none => rw [h1] at H; cases H
    | some s =>
      cases h2 : T.runFrom (k + 1) cs with
      | none => rw [h1, h2] at H; cases H
      | some rs =>
        rw [h1, h2] at H
        simp only [Option.some.injEq] at H
        subst H
        obtain ⟨l1, l2⟩ := runFrom_spec T cs (k + 1) rs h2
        refine ⟨by simp [l1], fun i hi => ?_⟩
        cases i with
        | zero => exact ⟨c, by simpa using h1⟩
        | succ i =>
          obtain ⟨ch, hch⟩ := l2 i (by simpa using hi)
          exact ⟨ch, by rw [show k + (i + 1) = k + 1 + i by omega]; simpa using hch⟩

theorem runAll_spec {T : Test} {chs : List (List Bool)} {trs : List SSt} (H : T.runAll chs = some trs) :
    trs.length = T.harts.length ∧ ∀ i (hi : i < trs.length), ∃ ch, T.runH i ch = some trs[i] := by
  unfold Test.runAll at H
  by_cases hl : chs.length = T.harts.length
  · rw [if_pos hl] at H
    obtain ⟨l1, l2⟩ := runFrom_spec T chs 0 trs H
    exact ⟨l1.trans hl, fun i hi => by simpa using l2 i hi⟩
  · rw [if_neg hl] at H; cases H

/-! ## 2. Stores write at least one byte (scope) -/

theorem stepI_stSz {h n : Nat} {s : SSt} {i : Instr} (hok : instrS3a i = true)
    (hs : ∀ se ∈ s.evs, se.sk.kind.isStore = true → 0 < se.sk.sz) :
    (∀ s', stepI h n s i = .next s' → ∀ se ∈ s'.evs, se.sk.kind.isStore = true → 0 < se.sk.sz) ∧
    (∀ t f, stepI h n s i = .fork t f →
      (∀ se ∈ t.evs, se.sk.kind.isStore = true → 0 < se.sk.sz) ∧
      (∀ se ∈ f.evs, se.sk.kind.isStore = true → 0 < se.sk.sz)) := by
  cases i with
  | alui => refine ⟨fun s' e => ?_, fun t f e => by simp [stepI] at e⟩
            simp only [stepI, Ref.StepR.next.injEq] at e; subst e; simpa using hs
  | alu => refine ⟨fun s' e => ?_, fun t f e => by simp [stepI] at e⟩
           simp only [stepI, Ref.StepR.next.injEq] at e; subst e; simpa using hs
  | csrr => refine ⟨fun s' e => ?_, fun t f e => by simp [stepI] at e⟩
            simp only [stepI, Ref.StepR.next.injEq] at e; subst e; simpa using hs
  | nop => refine ⟨fun s' e => ?_, fun t f e => by simp [stepI] at e⟩
           simp only [stepI, Ref.StepR.next.injEq] at e; subst e; simpa using hs
  | fencei => refine ⟨fun s' e => ?_, fun t f e => by simp [stepI] at e⟩
              simp only [stepI, Ref.StepR.next.injEq] at e; subst e; simpa using hs
  | jmp tgt =>
    refine ⟨fun s' e => ?_, fun t f e => by simp only [stepI] at e; split at e <;> cases e⟩
    simp only [stepI] at e; split at e
    · cases e
    · simp only [Ref.StepR.next.injEq] at e; subst e; simpa using hs
  | br c rs1 rs2 tgt =>
    refine ⟨fun s' e => (by simp only [stepI] at e; split at e <;> cases e), fun t f e => ?_⟩
    simp only [stepI] at e; split at e
    · cases e
    · simp only [Ref.StepR.fork.injEq] at e; obtain ⟨rfl, rfl⟩ := e; exact ⟨hs, hs⟩
  | load sz sgn rd rs1 off =>
    refine ⟨fun s' e => ?_, fun t f e => by simp [stepI] at e⟩
    simp only [stepI, Ref.StepR.next.injEq] at e; subst e
    intro se hse hst
    simp only [SSt.adv_evs, SSt.wr_evs, SSt.emit_evs, List.mem_append, List.mem_singleton] at hse
    rcases hse with hse | rfl
    · exact hs se hse hst
    · cases hst
  | store sz rs2 rs1 off =>
    refine ⟨fun s' e => ?_, fun t f e => by simp [stepI] at e⟩
    simp only [stepI, Ref.StepR.next.injEq] at e; subst e
    intro se hse hst
    simp only [SSt.adv_evs, SSt.emit_evs, List.mem_append, List.mem_singleton] at hse
    rcases hse with hse | rfl
    · exact hs se hse hst
    · simp only [instrS3a, Bool.and_eq_true] at hok
      exact (szOk_le hok.1.1).1
  | fence fs =>
    refine ⟨fun s' e => ?_, fun t f e => by simp [stepI] at e⟩
    simp only [stepI, Ref.StepR.next.injEq] at e; subst e
    intro se hse hst
    simp only [SSt.adv_evs, SSt.emit_evs, List.mem_append, List.mem_singleton] at hse
    rcases hse with hse | rfl
    · exact hs se hse hst
    · cases hst
  | fenceTso =>
    refine ⟨fun s' e => ?_, fun t f e => by simp [stepI] at e⟩
    simp only [stepI, Ref.StepR.next.injEq] at e; subst e
    intro se hse hst
    simp only [SSt.adv_evs, SSt.emit_evs, List.mem_append, List.mem_singleton] at hse
    rcases hse with (hse | rfl) | rfl
    · exact hs se hse hst
    · cases hst
    · cases hst
  | loadAq => simp [instrS3a] at hok
  | storeRl => simp [instrS3a] at hok
  | loadAqPc => simp [instrS3a] at hok
  | storeRlPc => simp [instrS3a] at hok
  | lr => simp [instrS3a] at hok
  | sc => simp [instrS3a] at hok
  | amo => simp [instrS3a] at hok

theorem symRun_stSz (p : List Instr) (hp : ∀ i ∈ p, instrS3a i = true) (h : Nat) :
    ∀ (fuel : Nat) (s : SSt) (ch : List Bool) (sf : SSt), symRun p h fuel s ch = some sf →
      (∀ se ∈ s.evs, se.sk.kind.isStore = true → 0 < se.sk.sz) →
      ∀ se ∈ sf.evs, se.sk.kind.isStore = true → 0 < se.sk.sz
  | 0, s, ch, sf, H, _ => by simp [symRun] at H
  | fuel + 1, s, ch, sf, H, hs => by
    unfold symRun at H
    by_cases hpc : s.pc = p.length
    · rw [if_pos hpc] at H
      split at H
      · cases H; exact hs
      · cases H
    · rw [if_neg hpc] at H
      cases hi : p[s.pc]? with
      | none => rw [hi] at H; cases H
      | some i =>
        rw [hi] at H
        simp only at H
        have hsz := stepI_stSz (h := h) (n := p.length) (hp i (List.mem_of_getElem? hi)) hs
        cases he : stepI h p.length s i with
        | stuck => rw [he] at H; cases H
        | next s' =>
          rw [he] at H
          exact symRun_stSz p hp h fuel s' ch sf H (hsz.1 s' he)
        | fork t f =>
          rw [he] at H
          simp only at H
          cases ch with
          | nil => cases H
          | cons b ch' =>
            cases b
            · exact symRun_stSz p hp h fuel f ch' sf H (hsz.2 t f he).2
            · exact symRun_stSz p hp h fuel t ch' sf H (hsz.2 t f he).1

/-! ## 3. Lifting a solo run into a machine run -/

theorem set_self_of {α : Type} {l : List α} {i : Nat} {a : α} (h : l[i]? = some a) : l.set i a = l := by
  obtain ⟨hi, he⟩ := List.getElem?_eq_some_iff.1 h
  rw [← he, List.set_getElem_self]

theorem solo_lift {img : Image} {M : List PMsg} {i : Nat} :
    ∀ {x y : LP × PState × GSet Nat} {tr : List (PLabel × Option Nat)}, soloSteps litStep img M i x tr y →
    ∀ (cfg : PCfg LP Unit), cfg.pcImg = img → cfg.pcLog = M → cfg.pcAgs[i]? = some ⟨x.1, x.2.1, x.2.2⟩ →
      pmSteps litStep cfg (tr.map (fun e => PEvt.st i e.1 e.2))
        ⟨cfg.pcImg, cfg.pcLog, cfg.pcDev, cfg.pcAgs.set i ⟨y.1, y.2.1, y.2.2⟩⟩ := by
  intro x y tr hs
  induction hs with
  | refl x =>
    intro cfg _ _ hag
    rw [set_self_of hag]
    exact .refl _
  | step x l ots p' ws' prom' tr y hp hm _ ih =>
    intro cfg himg hlog hag
    have hstep : pmStep litStep cfg (.st i l ots) ⟨cfg.pcImg, cfg.pcLog, (), cfg.pcAgs.set i ⟨p', ws', prom'⟩⟩ :=
      .state cfg i ⟨x.1, x.2.1, x.2.2⟩ l ots p' () ws' prom' hag hp (by rw [himg, hlog]; exact hm)
    have ih' := ih ⟨cfg.pcImg, cfg.pcLog, (), cfg.pcAgs.set i ⟨p', ws', prom'⟩⟩ himg hlog
      (getElem?_set_eq_of hag)
    simp only [List.set_set] at ih'
    exact .step _ _ _ _ _ hstep ih'

theorem traceOf_st (h i : Nat) : ∀ tr : List (PLabel × Option Nat),
    traceOf h (tr.map (fun e => PEvt.st i e.1 e.2)) = if i = h then tr else []
  | [] => by split <;> rfl
  | e :: tr => by
    simp only [List.map_cons, traceOf, traceOf_st h i tr]
    split <;> rfl

/-! ## 4. The state phase, hart after hart -/

theorem statePhase {M : List PMsg} {img : Image} {H : Nat} (G : Nat → PF.Trace → LP → PState → Prop)
    (P : Nat → GSet Nat) (L0 : Nat → LP) (c0 : PCfg LP Unit) (himg : c0.pcImg = img) (hlog : c0.pcLog = M)
    (hlen : c0.pcAgs.length = H) (hag : ∀ i, i < H → c0.pcAgs[i]? = some ⟨L0 i, psInit, P i⟩)
    (hsolo : ∀ i, i < H → ∃ tr lp' ws', soloSteps litStep img M i (L0 i, psInit, P i) tr (lp', ws', ∅) ∧
      G i tr lp' ws') :
    ∀ k, k ≤ H → ∃ evs cfg, pmSteps litStep c0 evs cfg ∧ cfg.pcImg = img ∧ cfg.pcLog = M ∧
      cfg.pcAgs.length = H ∧
      (∀ i, i < k → ∃ lp' ws', cfg.pcAgs[i]? = some ⟨lp', ws', ∅⟩ ∧ G i (traceOf i evs) lp' ws') ∧
      (∀ i, k ≤ i → cfg.pcAgs[i]? = c0.pcAgs[i]?) ∧ (∀ i, k ≤ i → traceOf i evs = []) ∧
      (∀ e ∈ evs, e.isSt = true)
  | 0, _ => ⟨[], c0, .refl _, himg, hlog, hlen, fun i hi => absurd hi (Nat.not_lt_zero _), fun _ _ => rfl,
      fun _ _ => rfl, fun e he => absurd he (List.not_mem_nil)⟩
  | k + 1, hk => by
    obtain ⟨evs, cfg, hs, himg', hlog', hlen', hdone, hrest, htr, hst⟩ := statePhase G P L0 c0 himg hlog hlen hag
      hsolo k (by omega)
    obtain ⟨tr, lp', ws', hsol, hG⟩ := hsolo k (by omega)
    have hagk : cfg.pcAgs[k]? = some ⟨(L0 k, psInit, P k).1, (L0 k, psInit, P k).2.1, (L0 k, psInit, P k).2.2⟩ := by
      rw [hrest k (Nat.le_refl _)]; exact hag k (by omega)
    have hlift := solo_lift hsol cfg himg' hlog' hagk
    refine ⟨evs ++ tr.map (fun e => PEvt.st k e.1 e.2), _, pmSteps_append hs hlift, himg', hlog',
      by simp [hlen'], fun i hi => ?_, fun i hi => ?_, fun i hi => ?_, fun e he => ?_⟩
    · rw [traceOf_append, traceOf_st]
      by_cases hik : i = k
      · subst hik
        refine ⟨lp', ws', ?_, ?_⟩
        · simp only; rw [List.getElem?_set_self (by rw [hlen']; omega)]
        · rw [htr i (Nat.le_refl _), if_pos rfl, List.nil_append]; exact hG
      · obtain ⟨lq, wq, h1, h2⟩ := hdone i (by omega)
        refine ⟨lq, wq, ?_, ?_⟩
        · simp only; rw [List.getElem?_set_ne (Ne.symm hik)]; exact h1
        · rw [if_neg (Ne.symm hik), List.append_nil]; exact h2
    · simp only; rw [List.getElem?_set_ne (by omega)]; exact hrest i (by omega)
    · rw [traceOf_append, traceOf_st, htr i (by omega), if_neg (by omega)]; rfl
    · rcases List.mem_append.1 he with he | he
      · exact hst e he
      · obtain ⟨x, _, rfl⟩ := List.mem_map.1 he; rfl

end Weak.Prom.Cmp
