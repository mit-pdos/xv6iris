/-
Weak/Prom: **track (b)'s machine-side conditions for litmus programs** (stage S4b part 2; plan rev 7 §4 "For the
G4 litmus targets they are dischargeable … every fetch reads the image (PA-0), there are no walks and there are no
A/D messages"; NF_R premise `invalFree`, R-b5).

For EVERY valid machine-v2 run of a litmus test (program half `litStep`, every hart starting with an empty label
queue): the run is FETCH-BOUNDED (`lit_fetchBounded`: `litStep` emits no `LIFetch`, so PO-fetch holds per program,
NfrRun.lean `fetchBounded_ofImg`) and `invalFree` (`lit_invalFree`: `litStep` emits no `LCmo`, so no message of the
final memory is a cache-block operation — every message is fulfilled by its author's write label,
MachSolo.lean `validRun_solo` + CoreRun.lean `solo_fulfils`).  Program-agnostic over litmus tests.
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Prom.OwnKit
import Weak.Prom.MachNota
import Weak.Prom.MachForbid

namespace Weak.Prom.Own

open MachCSL MachCSL.Stdpp Iris.Std
open Weak (Image Dsrc)
open Weak.Prom Weak.Prom.Nfr Weak.Prom.Mach Weak.Prom.Mach.Cert
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

/-- Along a solo run of a litmus hart from a well-formed queue, no label is a fetch or a CMO. -/
theorem solo_nf {img : Image} {M : List PMsg} {h : Nat} :
    ∀ {x y : LP × PState × GSet Nat} {τ : List (PLabel × Option Nat)},
      soloSteps litStep img M h x τ y → qOk x.1.q →
      ∀ e ∈ τ, (∀ b tvs, e.1 ≠ LIFetch b tvs) ∧ (∀ k b len asrc, e.1 ≠ LCmo k b len asrc) := by
  intro x y τ hs
  induction hs with
  | refl => intro _ e he; cases he
  | step x l ots p' ws' prom' tr y hp _ _ ih =>
    intro hq e he
    rcases List.mem_cons.1 he with rfl | he
    · exact litNext_nf hq hp
    · exact ih (litNext_q hq hp) e he

/-- Solo runs of a litmus hart keep the queue well-formed. -/
theorem solo_q {img : Image} {M : List PMsg} {h : Nat} :
    ∀ {x y : LP × PState × GSet Nat} {τ : List (PLabel × Option Nat)},
      soloSteps litStep img M h x τ y → qOk x.1.q → qOk y.1.q := by
  intro x y τ hs
  induction hs with
  | refl => exact id
  | step x l ots p' ws' prom' tr y hp _ _ ih => exact fun hq => ih (litNext_q hq hp)

/-- **PO-fetch for every litmus test** (plan §4: dischargeable per program; here for all litmus programs at once). -/
theorem lit_fetchBounded {img : Image} {ps : List LP} {evs : List PEvt} {cfg : PCfg LP Unit}
    (hv : validRun litStep img () ps evs cfg) (hps : ∀ p ∈ ps, p.q = []) :
    fetchBounded litStep img ps cfg.pcLog evs := by
  apply fetchBounded_ofImg
  intro hh e he base tvs hl
  rcases Nat.lt_or_ge hh ps.length with hlt | hge
  · obtain ⟨ag, _, P0, _, hs⟩ := validRun_solo hv hh _ (List.getElem?_eq_getElem hlt)
    have hq : qOk ps[hh].q := by rw [hps _ (List.getElem_mem hlt)]; exact qOk_nil
    exact absurd hl ((solo_nf hs hq e he).1 base tvs)
  · rw [PF.validRun_traceNone hv (List.getElem?_eq_none hge)] at he
    cases he

/-- **`invalFree` for every litmus test**: no message of the final memory is a cache-block operation. -/
theorem lit_invalFree {img : Image} {ps : List LP} {evs : List PEvt} {cfg : PCfg LP Unit}
    (hv : validRun litStep img () ps evs cfg) (hps : ∀ p ∈ ps, p.q = []) : invalFree cfg.pcLog := by
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

end Weak.Prom.Own
