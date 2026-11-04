/-
Weak/Prom: **litmus programs issue no cache-block operation** (FIX MachFix-R-b5, 2026-11-04; moved here from
OwnLitSide.lean so that the S2 litmus proofs can use it).

Machine v2's load-like arms absorb the view of a cited invalidate (Machine.lean `invalCite`); on a final memory with
no invalidate-class message the absorbed view is `0` and the arms are the pre-fix ones (MachInval.lean
`invalCite_vi0`).  For EVERY valid machine-v2 run of a litmus test (program half `litStep`, every hart starting with
an empty label queue) no message of the final memory is a cache-block operation (`lit_noInval`: `litStep` emits no
`LCmo`, and every message is fulfilled by its author's write label).  Program-agnostic over litmus tests.
`nfL`, `instrNext_nfL`, `litNext_nf`, `solo_q` are OwnLitSide.lean's (S4b), verbatim, in their namespace.
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Prom.MachNota
import Weak.Prom.CoreRun

namespace Weak.Prom.Own

open MachCSL MachCSL.Stdpp Iris.Std
open Weak (Image Dsrc)
open Weak.Prom Weak.Prom.Mach Weak.Prom.Mach.Cert
open Weak.Prom.Ref (Instr)
open PLabel

/-- Neither a fetch nor a cache-block operation. -/
def nfL : PLabel → Bool
  | LIFetch _ _ => false
  | LCmo _ _ _ _ => false
  | _ => true

/-- The first label of a litmus instruction is neither a fetch nor a CMO (MachCert.lean `instrNext`). -/
theorem instrNext_nfL {n : Nat} {s s' : LP} {ins : Instr} {l : PLabel} (h : instrNext n s ins l = some s') :
    nfL l = true := by
  cases ins with
  | alui op rd rs1 imm =>
    simp only [instrNext] at h
    obtain ⟨rest, h1, rfl⟩ := go1_eq h
    unfold regWL at h1; split at h1 <;> simp at h1 <;> obtain ⟨rfl, _⟩ := h1 <;> rfl
  | alu op rd rs1 rs2 =>
    simp only [instrNext] at h
    obtain ⟨rest, h1, rfl⟩ := go1_eq h
    unfold regWL at h1; split at h1 <;> simp at h1 <;> obtain ⟨rfl, _⟩ := h1 <;> rfl
  | csrr rd v =>
    simp only [instrNext] at h
    obtain ⟨rest, h1, rfl⟩ := go1_eq h
    unfold regWL at h1; split at h1 <;> simp at h1 <;> obtain ⟨rfl, _⟩ := h1 <;> rfl
  | fence f =>
    simp only [instrNext] at h
    obtain ⟨rest, h1, rfl⟩ := go1_eq h
    simp at h1; obtain ⟨rfl, _⟩ := h1; rfl
  | fenceTso =>
    simp only [instrNext] at h
    obtain ⟨rest, h1, rfl⟩ := go1_eq h
    simp at h1; obtain ⟨rfl, _⟩ := h1; rfl
  | fencei =>
    simp only [instrNext] at h
    obtain ⟨rest, h1, rfl⟩ := go1_eq h
    simp at h1; obtain ⟨rfl, _⟩ := h1; rfl
  | nop =>
    simp only [instrNext] at h
    obtain ⟨rest, h1, rfl⟩ := go1_eq h
    simp at h1; obtain ⟨rfl, _⟩ := h1; rfl
  | br c rs1 rs2 tgt =>
    replace h := ite_none_some h
    obtain ⟨rest, h1, rfl⟩ := go1_eq h
    simp at h1; obtain ⟨rfl, _⟩ := h1; rfl
  | jmp tgt =>
    replace h := ite_none_some h
    obtain ⟨rest, h1, rfl⟩ := go1_eq h
    simp at h1; obtain ⟨rfl, _⟩ := h1; rfl
  | load sz sgn rd rs1 off =>
    replace h := ite_none_some h
    cases l <;> first | rfl | (simp only [reduceCtorEq] at h; done)
  | loadAq sz rl0 rd rs1 =>
    replace h := ite_none_some h
    cases l <;> first | rfl | (simp only [reduceCtorEq] at h; done)
  | lr sz aq0 rl0 rd rs1 =>
    replace h := ite_none_some h
    cases l <;> first | rfl | (simp only [reduceCtorEq] at h; done)
  | amo op sz aq0 rl0 rd rs2 rs1 =>
    replace h := ite_none_some h
    cases l <;> first | rfl | (simp only [reduceCtorEq] at h; done)
  | store sz rs2 rs1 off =>
    replace h := ite_none_some h
    cases l <;> first | rfl | (simp only [reduceCtorEq] at h; done)
  | storeRl sz aq0 rs2 rs1 =>
    replace h := ite_none_some h
    cases l <;> first | rfl | (simp only [reduceCtorEq] at h; done)
  | sc sz aq0 rl0 rd rs2 rs1 =>
    replace h := ite_none_some h
    cases l <;> first | rfl | (simp only [reduceCtorEq] at h; done)
  | loadAqPc => cases h
  | storeRlPc => cases h

/-- `litNext` emits no fetch and no cache-block operation from a well-formed queue (MachNota.lean `qOk`). -/
theorem litNext_nf {s s' : LP} {l : PLabel} (hq : qOk s.q) (h : litNext s l = some s') :
    (∀ b tvs, l ≠ LIFetch b tvs) ∧ (∀ k b len asrc, l ≠ LCmo k b len asrc) := by
  have key : nfL l = true := by
    unfold litNext at h
    split at h
    · rename_i l0 rest hq'
      split at h
      · rename_i he
        subst he
        have := hq.1 l (by rw [hq']; simp)
        cases l <;> simp_all [qLab, nfL]
      · cases h
    · split at h
      · exact instrNext_nfL h
      · cases h
  exact ⟨fun b tvs e => by subst e; simp [nfL] at key, fun k b len asrc e => by subst e; simp [nfL] at key⟩

/-- Solo runs of a litmus hart keep the queue well-formed. -/
theorem solo_q {img : Image} {M : List PMsg} {h : Nat} :
    ∀ {x y : LP × PState × GSet Nat} {τ : List (PLabel × Option Nat)},
      soloSteps litStep img M h x τ y → qOk x.1.q → qOk y.1.q := by
  intro x y τ hs
  induction hs with
  | refl => exact id
  | step x l ots p' ws' prom' tr y hp _ _ ih => exact fun hq => ih (litNext_q hq hp)

/-- Solo runs keep a program-state invariant. -/
theorem solo_inv {P : Type} {pstep : P → Unit → PLabel → P → Unit → Prop} {img : Image} {M : List PMsg} {h : Nat}
    (Inv : P → Prop) (hst : ∀ s l s', Inv s → pstep s () l s' () → Inv s') :
    ∀ {x y : P × PState × GSet Nat} {τ : List (PLabel × Option Nat)},
      soloSteps pstep img M h x τ y → Inv x.1 → Inv y.1 := by
  intro x y τ hs
  induction hs with
  | refl => exact id
  | step x l ots p' ws' prom' tr y hp _ _ ih => exact fun hq => ih (hst _ _ _ hq hp)

/-- **No invalidate-class message, for any program half that never emits `LCmo`** (from states satisfying an
invariant it keeps): every message of the final memory is fulfilled by its author's write label, which is not a
cache-block operation. -/
theorem noInval_of_noCmoLab {P : Type} {pstep : P → Unit → PLabel → P → Unit → Prop} {img : Image} {ps : List P}
    {evs : List PEvt} {cfg : PCfg P Unit} (Inv : P → Prop) (h0 : ∀ p ∈ ps, Inv p)
    (hst : ∀ s l s', Inv s → pstep s () l s' () → Inv s' ∧ ∀ k b len asrc, l ≠ LCmo k b len asrc)
    (hv : validRun pstep img () ps evs cfg) : ∀ t a, ¬ cmoAt cfg.pcLog isInvalK t a := by
  intro t a hc
  obtain ⟨m, k, len, hm, hcls, _⟩ := hc
  have hm1 : cfg.pcLog[(t - 1 + 1) - 1]? = some m := by simpa using hm
  have hwf := pmSteps_wf hv.1 (pmInit_wf img () ps)
  obtain ⟨_, i, hti, hil⟩ := hwf.2 m (List.mem_of_getElem? hm)
  rw [PF.validRun_len hv] at hil
  obtain ⟨ag, hag, P0, hP0, hs⟩ := validRun_solo hv i _ (List.getElem?_eq_getElem hil)
  have hin : t - 1 + 1 ∈ P0 := (hP0 _).2 ⟨by omega, m, hm1, hti⟩
  have hout : t - 1 + 1 ∉ ag.paProm := by rw [hv.2 i ag hag]; exact notElemOfEmpty
  obtain ⟨z, tr1, l, p', ws', prom', hpre, hp, hmm⟩ := solo_fulfil hs hin hout
  have hqz : Inv z.1 := solo_inv Inv (fun s l s' h1 h2 => (hst s l s' h1 h2).1) hpre (h0 _ (List.getElem_mem hil))
  obtain ⟨h1, _⟩ := memStep_msg hmm
  have hmsg := h1 _ rfl
  rw [hm1] at hmsg
  have hnc := (hst _ _ _ hqz hp).2
  cases l <;> simp [labelMsg] at hmsg <;> subst hmsg <;> simp [stClass] at hcls
  · split at hcls <;> cases hcls
  · exact hnc _ _ _ _ rfl

/-- **No invalidate-class message for every litmus test** (MachFix-R-b5; was OwnLitSide.lean `lit_invalFree`): no
message of the final memory is a cache-block operation. -/
theorem lit_noInval {img : Image} {ps : List LP} {evs : List PEvt} {cfg : PCfg LP Unit}
    (hv : validRun litStep img () ps evs cfg) (hps : ∀ p ∈ ps, p.q = []) : ∀ t a, ¬ cmoAt cfg.pcLog isInvalK t a := by
  intro t a hc
  obtain ⟨m, k, len, hm, hcls, _⟩ := hc
  have hm1 : cfg.pcLog[(t - 1 + 1) - 1]? = some m := by simpa using hm
  have hwf := pmSteps_wf hv.1 (pmInit_wf img () ps)
  obtain ⟨_, i, hti, hil⟩ := hwf.2 m (List.mem_of_getElem? hm)
  rw [PF.validRun_len hv] at hil
  obtain ⟨ag, hag, P0, hP0, hs⟩ := validRun_solo hv i _ (List.getElem?_eq_getElem hil)
  have hin : t - 1 + 1 ∈ P0 := (hP0 _).2 ⟨by omega, m, hm1, hti⟩
  have hout : t - 1 + 1 ∉ ag.paProm := by rw [hv.2 i ag hag]; exact notElemOfEmpty
  obtain ⟨z, tr1, l, p', ws', prom', hpre, hp, hmm⟩ := solo_fulfil hs hin hout
  have hq : qOk ps[i].q := by rw [hps _ (List.getElem_mem hil)]; exact qOk_nil
  have hqz : qOk z.1.q := solo_q hpre hq
  obtain ⟨h1, _⟩ := memStep_msg hmm
  have hmsg := h1 _ rfl
  rw [hm1] at hmsg
  have hnc := (litNext_nf hqz hp).2
  cases l <;> simp [labelMsg] at hmsg <;> subst hmsg <;> simp [stClass] at hcls
  · split at hcls <;> cases hcls
  · exact hnc _ _ _ _ rfl

/-- `lit_noInval` for `PF.validRun` (the S2 litmus theorems' form). -/
theorem lit_noInvalPF {img : Image} {ps : List LP} {M : List PMsg} {run : PF.PFRun LP Unit}
    (hv : PF.validRun litStep img () ps M run) (hps : ∀ p ∈ ps, p.q = []) : ∀ t a, ¬ cmoAt M isInvalK t a := by
  rw [← hv.2]; exact lit_noInval hv.1 hps

theorem progs_q (T : Weak.Prom.Ref.Test) : ∀ p ∈ progs T, p.q = [] := by
  intro p hp
  simp only [progs, List.mem_map] at hp
  obtain ⟨_, _, rfl⟩ := hp
  rfl

/-- `lit_noInvalPF` for a litmus test's own initial states. -/
theorem lit_noInvalT {T : Weak.Prom.Ref.Test} {img : Image} {M : List PMsg} {run : PF.PFRun LP Unit}
    (hv : PF.validRun litStep img () (progs T) M run) : ∀ t a, ¬ cmoAt M isInvalK t a :=
  lit_noInvalPF hv (progs_q T)

end Weak.Prom.Own
