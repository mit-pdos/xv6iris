/-
Weak/Prom: **completeness S3a — one hart, the whole program** (plan rev 7 §6: "Step each hart in po with a
simulation").

`sim`: from any symbolic state related by `SimInv` to a machine state, the rest of the reference path is a solo run
of machine v2 against `memOf X` whose loads answer the reference's loads; `sim_hart`: from the initial states (the
machine hart at `psInit` with every own message promised, as after the promise phase), every hart's reference path
is a solo run ending done, with no outstanding promise, the reference's final registers, and the reference row.
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Prom.CmpSimA  -- S3b: the S3b steps (imports CmpSimS)
import Weak.Prom.CmpSymB

namespace Weak.Prom.Cmp

open MachCSL MachCSL.Stdpp Iris.Std
open Weak (Image Dsrc)
open Weak.Prom Weak.Prom.Mach Weak.Prom.Mach.Cert
open Weak.Prom.Ref
open PLabel

variable {T : Test} {trs : List SSt} {ν : Val} {X : Exec} {h : Nat} {sf : SSt}

theorem soloSteps_append {P : Type} {pst : P → Unit → PLabel → P → Unit → Prop} {img : Image} {M : List PMsg}
    {i : Nat} : ∀ {x y z : P × PState × GSet Nat} {t1 t2 : List (PLabel × Option Nat)},
    soloSteps pst img M i x t1 y → soloSteps pst img M i y t2 z → soloSteps pst img M i x (t1 ++ t2) z := by
  intro x y z t1 t2 h1 h2
  induction h1 with
  | refl => exact h2
  | step x l ots p' ws' prom' tr y hp hm _ ih => exact .step _ _ _ _ _ _ _ _ hp hm (ih h2)

theorem instr_scope (hT : progS3bB T = true) {pc : Nat} {ins : Instr} (hi : (T.prog h)[pc]? = some ins) :
    instrS3b ins = true := by  -- S3b: the S3b scope
  simp only [progS3bB, Bool.and_eq_true, List.all_eq_true] at hT
  unfold Test.prog at hi
  cases hh : T.harts[h]? with
  | none => rw [hh] at hi; simp at hi
  | some p =>
    rw [hh] at hi
    simp only [Option.getD_some] at hi
    exact hT.1.2 p (List.mem_of_getElem? hh) ins (List.mem_of_getElem? hi)

/-- THE SIMULATION OF THE REST OF A PATH (S3b: the invariant is `SimInv` and `ExtraInv`; every S3b instruction). -/
theorem sim (c : HCtx T trs ν X h sf) :
    ∀ (fuel : Nat) (s : SSt) (ch : List Bool) (lp : LP) (ws : PState) (prom : GSet Nat),
      symRun (T.prog h) h fuel s ch = some sf → SimInv T X ν h sf s lp ws prom →
      ExtraInv X h s.evs.length ws.wVRel ws.wRes →
      ∃ tr lp' ws' prom', soloSteps litStep (testImg T) (memOf X) h (lp, ws, prom) tr (lp', ws', prom') ∧
        machRow tr = rowSeg X h s.evs.length sf.evs.length ∧ SimInv T X ν h sf sf lp' ws' prom' ∧
        lp'.pc = (T.prog h).length
  | 0, s, ch, lp, ws, prom, H, _, _ => by simp [symRun] at H
  | fuel + 1, s, ch, lp, ws, prom, H, hinv, hx => by
    unfold symRun at H
    by_cases hpc : s.pc = (T.prog h).length
    · rw [if_pos hpc] at H
      split at H
      · cases H
        exact ⟨[], lp, ws, prom, .refl _, by rw [rowSeg_self]; rfl, hinv, by rw [hinv.pc, hpc]⟩
      · cases H
    · rw [if_neg hpc] at H
      cases hi : (T.prog h)[s.pc]? with
      | none => rw [hi] at H; cases H
      | some ins =>
        rw [hi] at H
        simp only at H
        have hok := instr_scope c.scope hi
        -- one instruction, then the rest
        have cont : ∀ s' ch', s.evs.length ≤ s'.evs.length → StepOkB T X ν h sf s lp ws prom s' →
            symRun (T.prog h) h fuel s' ch' = some sf →
            ∃ tr lp' ws' prom', soloSteps litStep (testImg T) (memOf X) h (lp, ws, prom) tr (lp', ws', prom') ∧
              machRow tr = rowSeg X h s.evs.length sf.evs.length ∧ SimInv T X ν h sf sf lp' ws' prom' ∧
              lp'.pc = (T.prog h).length := by
          intro s' ch' hle hst H'
          obtain ⟨tr1, lp1, ws1, prom1, hs1, hr1, hinv1, hx1⟩ := hst
          obtain ⟨tr2, lp2, ws2, prom2, hs2, hr2, hinv2, hpc2⟩ := sim c fuel s' ch' lp1 ws1 prom1 H' hinv1 hx1
          refine ⟨tr1 ++ tr2, lp2, ws2, prom2, soloSteps_append hs1 hs2, ?_, hinv2, hpc2⟩
          rw [machRow_append, hr1, hr2, rowSeg_append _ _ _ _ _ hle hinv1.fut.evs.length_le]
        -- an S3a step keeps `ExtraInv`
        have old : ∀ s', NewOk ins s s' → Future s' sf → notLrScI ins = true →
            StepOk T X ν h sf s lp ws prom s' → StepOkB T X ν h sf s lp ws prom s' := by
          intro s' hn hfut' hnl hst
          have hle : s.evs.length ≤ s'.evs.length := by obtain ⟨new, h1, _⟩ := hn; rw [h1]; simp
          exact stepOkB_of hx hst hle (fun j h1 h2 => by
            obtain ⟨se, hse, hok'⟩ := newOk_get hn hfut'.evs h1 h2
            rw [c.sk hse]; exact newEvOk_noLrSc hnl hok')
        have hnew := stepI_new h (T.prog h).length s ins
        cases hstep : stepI h (T.prog h).length s ins with
        | stuck => rw [hstep] at H; cases H
        | next s' =>
          rw [hstep] at H
          have hfut := symRun_future (T.prog h) h fuel s' ch sf H
          have hn := hnew.1 s' hstep
          have hle : s.evs.length ≤ s'.evs.length := by obtain ⟨new, h1, _⟩ := hn; rw [h1]; simp
          refine cont s' ch hle ?_ H
          cases ins with
          | alui op rd rs1 imm => exact old s' hn hfut rfl (sim_alui c hinv hi hok hstep hfut)
          | alu op rd rs1 rs2 => exact old s' hn hfut rfl (sim_alu c hinv hi hok hstep hfut)
          | load sz sgn rd rs1 off => exact old s' hn hfut rfl (sim_load c hinv hi hok hstep hfut)
          | store sz rs2 rs1 off => exact old s' hn hfut rfl (sim_store c hinv hi hok hstep hfut)
          | fence fs => exact old s' hn hfut rfl (sim_fence c hinv hi hstep hfut)
          | fenceTso => exact old s' hn hfut rfl (sim_fenceTso c hinv hi hstep hfut)
          | br cc rs1 rs2 tgt => simp only [stepI] at hstep; split at hstep <;> cases hstep
          | jmp tgt => exact old s' hn hfut rfl (sim_jmp hinv hi hstep hfut)
          | csrr rd v => exact old s' hn hfut rfl (sim_csrr c hinv hi hstep hfut)
          | fencei => exact old s' hn hfut rfl (sim_fencei hinv hi hstep hfut)
          | nop => exact old s' hn hfut rfl (sim_nop hinv hi hstep hfut)
          | loadAq => exact sim_loadAq c hinv hx hi hok hstep hfut
          | storeRl => exact sim_storeRl c hinv hx hi hok hstep hfut
          | lr => exact sim_lr c hinv hx hi hok hstep hfut
          | amo => exact sim_amo c hinv hx hi hok hstep hfut
          | loadAqPc => simp [instrS3b, instrS3a] at hok
          | storeRlPc => simp [instrS3b, instrS3a] at hok
          | sc => simp [stepI] at hstep
        | fork t f =>
          rw [hstep] at H
          simp only at H
          cases ch with
          | nil => cases H
          | cons b ch' =>
            have H' : symRun (T.prog h) h fuel (if b then t else f) ch' = some sf := by
              cases b <;> simpa using H
            have hfut := symRun_future (T.prog h) h fuel _ ch' sf H'
            have hn : NewOk ins s (if b then t else f) := by
              cases b
              · exact (hnew.2 t f hstep).2
              · exact (hnew.2 t f hstep).1
            have hle : s.evs.length ≤ (if b then t else f).evs.length := by
              obtain ⟨new, h1, _⟩ := hn; rw [h1]; simp
            refine cont _ ch' hle ?_ H'
            cases ins with
            | br cc rs1 rs2 tgt => exact old _ hn hfut rfl (sim_br c hinv hi hok hstep b hfut)
            | sc =>
              cases b
              · exact sim_scFail c hinv hx hi hok hstep hfut
              · exact sim_scOk c hinv hx hi hok hstep hfut
            | jmp tgt => simp only [stepI] at hstep; split at hstep <;> cases hstep
            | _ => simp [stepI] at hstep

/-- An identifier of hart `h` in `X` indexes `sf`'s events. -/
theorem HCtx.idx_lt (c : HCtx T trs ν X h sf) {j : Nat} (hj : (h, j) ∈ X.ids) : j < sf.evs.length := by
  rw [c.xc, conc_ids] at hj
  obtain ⟨l, hl1, hl2⟩ := (mem_idsOf _ _).1 hj
  simp only [List.getElem?_map, c.tr, Option.map_some, Option.some.injEq] at hl1
  subst hl1; exact hl2

/-- `X`'s event list of hart `h`. -/
theorem HCtx.evs_h (c : HCtx T trs ν X h sf) : X.evs[h]? = some (sf.evs.mapIdx (fun i se => concEv ν h i se)) := by
  rw [c.xc]
  simp [conc, List.getElem?_mapIdx, c.tr]

theorem rowSeg_list (X : Exec) (h : Nat) (p : Ev → Bool) (f : Ev → List Nat) :
    ∀ (L : List Ev) (n : Nat), (∀ k (hk : k < L.length), X.ev (h, n + k) = L[k]) →
      ((List.range' n L.length).filter (fun j => p (X.ev (h, j)))).map (fun j => f (X.ev (h, j))) =
        (L.filter p).map f
  | [], _, _ => rfl
  | v :: L, n, hL => by
    have h0 := hL 0 (by simp)
    simp only [Nat.add_zero, List.getElem_cons_zero] at h0
    have ih := rowSeg_list X h p f L (n + 1) (fun k hk => by
      have := hL (k + 1) (by simp; omega)
      rw [show n + (k + 1) = n + 1 + k by omega] at this
      simpa using this)
    simp only [List.length_cons, List.range'_succ, List.filter_cons, h0]
    split <;> simp [ih, h0]

/-- The reference row is the row segment of all events. -/
theorem HCtx.refRow_eq (c : HCtx T trs ν X h sf) : refRow X h = rowSeg X h 0 sf.evs.length := by
  unfold refRow rowSeg
  rw [c.evs_h, Option.getD_some, Nat.sub_zero]
  have := rowSeg_list X h (fun v => v.sk.kind.isLoad) Ev.rdat (sf.evs.mapIdx (fun i se => concEv ν h i se)) 0
    (fun k hk => by
      rw [Nat.zero_add]
      unfold Exec.ev
      rw [c.evs_h]
      have hk' : k < sf.evs.length := by simpa using hk
      simp [List.getElem?_eq_getElem hk'])
  rw [List.length_mapIdx] at this
  exact this.symm

/-- The machine's initial program state of hart `h` (MachCert.lean `progs`). -/
def lpInit (T : Test) (h : Nat) : LP :=
  { prog := T.prog h, pc := 0, q := []
    regs := (List.range 32).map (fun r => ((((T.regs0[h]?).getD []).lookup r).getD 0) % two64) }

theorem progs_get (T : Test) {h : Nat} (hh : h < T.harts.length) : (progs T)[h]? = some (lpInit T h) := by
  simp [progs, lpInit, hh]

theorem progs_len (T : Test) : (progs T).length = T.harts.length := by simp [progs]

theorem getD_map_range {α : Type} (f : Nat → α) (d : α) (n r : Nat) :
    (((List.range n).map f)[r]?).getD d = if r < n then f r else d := by
  by_cases h : r < n
  · rw [if_pos h, List.getElem?_map, List.getElem?_range h]; rfl
  · rw [if_neg h, List.getElem?_eq_none (by simp; omega)]; rfl

/-- THE INITIAL STATES ARE RELATED (the machine hart at `psInit`, every own message promised). -/
theorem simInv_init (c : HCtx T trs ν X h sf) {ch : List Bool} (hrun : T.runH h ch = some sf)
    (P0 : GSet Nat) (hP0 : ∀ t, t ∈ P0 ↔ 0 < t ∧ ownTs (memOf X) h t) :
    SimInv T X ν h sf (T.init h) (lpInit T h) psInit P0 := by
  have hfut := symRun_future _ _ _ _ _ _ hrun
  have hst1 : ∀ j, j < sf.evs.length → (X.sk (h, j)).kind.isStore = true → 1 ≤ vo X (h, j) := by
    intro j hj hs
    exact voG_st_pos X X.gmo _ ((mem_gmo c.ref _).2 ⟨(fut_ev c hj).1, Kind.isMem_of_isStore _ hs⟩) hs
  have hreg : ∀ r, (lpInit T h).rd r = ((T.init h).rd r).1.eval ν ∧ ((T.init h).rd r).1.eval ν < two64 := by
    intro r
    unfold LP.rd SSt.rd lpInit Test.init
    by_cases h0 : r = 0
    · simp only [h0, if_true, Ex.eval]; exact ⟨rfl, by decide⟩
    · simp only [h0, if_false]
      rw [getD_map_range, getD_map_range]
      by_cases h32 : r < 32
      · rw [if_pos h32, if_pos h32]
        exact ⟨rfl, Nat.mod_lt _ (by decide)⟩
      · rw [if_neg h32, if_neg h32]
        exact ⟨rfl, eval_c_lt 0 ν⟩
  have hfwd0 : ∀ x : Int, get? psInit.wFwd x = none := fun x => lookupEmpty
  refine ⟨symWf_init T h, hfut, rfl, rfl, rfl, by simp [lpInit], fun r => (hreg r).1, fun r => (hreg r).2,
    fun r _ _ => ?_, domF_zero _ _, domF_zero _ _,
    fun j _ hj hs => ⟨Nat.zero_le _, fun hst => hst1 j hj hst⟩,  -- S3b: strict part
    fun j _ hj hs => hst1 j hj hs, fun j _ hj hs => hst1 j hj hs, fun x j _ hj hs _ => ?_, ?_, ?_, rfl, rfl, ?_⟩
  · have : regv psInit r = 0 := by unfold regv; rw [show psInit.wRegv = ∅ from rfl, lookupEmpty]; rfl
    rw [this]; exact domF_zero _ _
  · have : coh psInit x = 0 := by unfold coh; rw [show psInit.wCoh = ∅ from rfl, lookupEmpty]; rfl
    rw [this]; exact hst1 j hj hs
  · intro x j _ _ _ _ w hw hww hle
    have : coh psInit x = 0 := by unfold coh; rw [show psInit.wCoh = ∅ from rfl, lookupEmpty]; rfl
    rw [this] at hle
    have := voG_st_pos X X.gmo w hw (writesB_store hww)
    unfold vo at hle; omega
  · intro x
    rw [hfwd0]
    intro j hj; exact absurd hj (by simp [Test.init])
  · intro t
    rw [hP0 t]
    constructor
    · rintro ⟨ht, m, hm, htid⟩
      have hlen : t ≤ (memOf X).length := by have := (List.getElem?_eq_some_iff.1 hm).1; omega
      obtain ⟨w, hw, hws, hv, hm'⟩ := memG_at X X.gmo (gmo_nodup c.ref) t ht hlen
      unfold memOf at hm
      rw [hm'] at hm
      cases hm
      simp only [msgOf, Option.some.injEq] at htid
      obtain ⟨w1, w2⟩ := w
      simp only at htid; subst htid
      exact ⟨w2, Nat.zero_le _, c.idx_lt (ids_of_gmo hw c.ref), hws, hv⟩
    · rintro ⟨j, _, hj, hs, rfl⟩
      have hg : (h, j) ∈ X.gmo := (mem_gmo c.ref _).2 ⟨(fut_ev c hj).1, Kind.isMem_of_isStore _ hs⟩
      refine ⟨hst1 j hj hs, msgOf X (h, j), memG_voG X X.gmo _ hg hs, rfl⟩

/-- **ONE HART, THE WHOLE PATH**: hart `h`'s reference path is a solo run of machine v2 against `memOf X` from
its initial state (every own message promised), ending done with no outstanding promise, the reference's final
registers, and the reference row. -/
theorem sim_hart (c : HCtx T trs ν X h sf) {ch : List Bool} (hrun : T.runH h ch = some sf)
    (P0 : GSet Nat) (hP0 : ∀ t, t ∈ P0 ↔ 0 < t ∧ ownTs (memOf X) h t) :
    ∃ tr lp' ws', soloSteps litStep (testImg T) (memOf X) h (lpInit T h, psInit, P0) tr (lp', ws', ∅) ∧
      machRow tr = refRow X h ∧ lp'.pc = lp'.prog.length ∧ lp'.q = [] ∧
      (∀ r, lp'.rd r = (sf.rd r).1.eval ν) := by
  obtain ⟨tr, lp', ws', prom', hs, hrow, hinv, hpc⟩ :=
    sim c _ (T.init h) ch (lpInit T h) psInit P0 hrun (simInv_init c hrun P0 hP0) (extra_init X h)  -- S3b
  have hempty : prom' = ∅ := by
    apply setEq.2
    intro t
    rw [hinv.prom t]
    constructor
    · rintro ⟨j, h1, h2, _⟩; omega
    · intro ht; exact absurd ht notElemOfEmpty
  subst hempty
  refine ⟨tr, lp', ws', hs, ?_, by rw [hpc, hinv.prog], hinv.q, hinv.regEq⟩
  rw [hrow, c.refRow_eq]
  rfl

end Weak.Prom.Cmp
