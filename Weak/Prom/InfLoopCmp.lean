/-
Weak/Prom: **InfLoop part 1 — PATH-EXPOSING completeness** (owner request 2026-11-13 "write the end-to-end
infinite-execution theorem for tLoop"; plan rev 7 §0 "(T-inf)": "proof = rvwmo_prefix ∘ rvwmo_complete ∘ …").

`rvwmo_inf_completeP` is PfxUnroll.lean's `rvwmo_inf_complete` (its proof re-run from PfxUnroll's exported lemmas;
PfxUnroll.lean is not edited) with ONE more conjunct in the conclusion: the concrete unrolling.  For every hart
`h` there is a cut `K h` such that the unrolled program of `h` IS `unrP E h (K h)` — the `j`-th instruction is
`unr j (iAt E h j)`, the instruction `E`'s hart `h` executes at step `j`, a branch or jump retargeted to `j + 1` —
and hart `h` is not halted at any step `j < K h`.  (`rvwmo_inf_complete` only says that every instruction of the
unrolling is SOME instruction of the program, retargeted.)
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Prom.PfxUnroll

noncomputable section

namespace Weak.Prom.InfLoop

open Classical
open MachCSL MachCSL.Stdpp Iris.Std
open Weak.Prom Weak.Prom.Mach Weak.Prom.Mach.Cert
open Weak.Prom.Ref
open Weak.Prom.Pfx
open Weak.Prom.Cmp (progS3aB progS3bB instrS3a progS3bB_of_S3a singleSize refRow machRow promisesFirst
  rvwmo_complete memOf)
open Weak.Prom.Pfx.Cut

/-- **Hart `h`'s first steps, unrolled, with the unrolling exposed** (PfxUnroll.lean `unroll_run`, whose `U` is
`unrP E h k'` for the non-halted prefix `k'` of `k`). -/
theorem unroll_runP {E : IExec} (hc : E.conforms) (hf : FragT E.T) {h : Nat} (hh : h < E.T.harts.length)
    (k : Nat) :
    ∃ (k' : Nat) (ch : List Bool), (∀ j < k', (E.st h j).pc ≠ (E.T.prog h).length) ∧
      (∀ j (i : Instr), (unrP E h k')[j]? = some i → ∃ (p : Nat) (i0 : Instr), (E.T.prog h)[p]? = some i0 ∧
        i = unr j i0) ∧ (∀ i ∈ unrP E h k', instrS3a i = true) ∧
      symRun (unrP E h k') h ((unrP E h k').length + 1) (E.T.init h) ch =
        some { E.st h k with pc := (unrP E h k').length } := by
  obtain ⟨k', hk1, hk2⟩ := nonhalted_prefix hc hf hh k
  have hlen : (unrP E h k').length = k' := by simp [unrP]
  have hiA : ∀ j < k', ∃ i0, (E.T.prog h)[(E.st h j).pc]? = some i0 ∧ iAt E h j = i0 := by
    intro j hj
    rcases (hc h hh).2 j with ⟨hp, _⟩ | ⟨i, hi, _⟩
    · exact absurd hp (hk2 j hj)
    · exact ⟨i, hi, by unfold iAt; rw [hi]; rfl⟩
  obtain ⟨ch, hch⟩ := unroll_sym hc hf hh k' hk2 k' (Nat.le_refl _)
  refine ⟨k', ch, hk2, fun j i hji => ?_, fun i hi => ?_, ?_⟩
  · simp only [unrP, List.getElem?_map] at hji
    have hj : j < k' := by
      rcases Nat.lt_or_ge j k' with h1 | h1
      · exact h1
      · rw [List.getElem?_eq_none (by simpa using h1)] at hji; cases hji
    rw [List.getElem?_range hj, Option.map_some, Option.some.injEq] at hji
    obtain ⟨i0, hi0, hia⟩ := hiA j hj
    exact ⟨_, i0, hi0, by rw [← hji, hia]⟩
  · simp only [unrP, List.mem_map, List.mem_range] at hi
    obtain ⟨j, hj, rfl⟩ := hi
    obtain ⟨i0, hi0, hia⟩ := hiA j hj
    rw [hia]; exact unr_frag j i0 (hf h i0 (List.mem_of_getElem? hi0))
  · rw [hlen, ← hk1]
    have h0 : ({ E.st h 0 with pc := 0 } : SSt) = E.T.init h := by rw [(hc h hh).1]; rfl
    simpa [h0] using hch

/-- **(T-inf) ∘ (T-cmp), S3a scope, PATH EXPOSED.**  `rvwmo_inf_complete` (PfxUnroll.lean) with the unrolling
exposed: hart `h` of `T'` runs `unrP E h (K h)`, and hart `h` of `E` is not halted before step `K h`. -/
theorem rvwmo_inf_completeP {T : Test} (hT : progS3aB T = true) {E : IExec} (hE : infExec T E)
    (hss : singleSizeI E) (O : List EvId) (hO : ∀ e ∈ O, E.isMem e) :
    ∃ (T' : Test) (K : Nat → Nat) (chs : List (List Bool)) (trs : List SSt) (ν : Val) (g : List EvId),
      unrollOf T T' ∧
      (∀ h < T.harts.length, T'.prog h = unrP E h (K h) ∧ ∀ j < K h, (E.st h j).pc ≠ (T.prog h).length) ∧
      T'.runAll chs = some trs ∧ condsOk ν trs = true ∧ rvwmoRef (conc T' trs ν g) ∧
      (∀ o ∈ O, ∀ i ≤ o.2, (o.1, i) ∈ (conc T' trs ν g).ids ∧ (conc T' trs ν g).ev (o.1, i) = E.ev (o.1, i)) ∧
      ∃ run : PF.PFRun LP Unit,
        PF.validRun litStep (testImg T') () (progs T') (memOf (conc T' trs ν g)) run ∧ promisesFirst run.evs ∧
        allDone run.cfg ∧
        ∀ o ∈ O, (((List.range (o.2 + 1)).map (fun i => E.ev (o.1, i))).filter (fun v => v.sk.kind.isLoad)).map
          Ev.rdat <+: machRow (run.trace o.1) := by
  obtain ⟨hET, hconf, hconds, href⟩ := hE
  subst hET
  have hio : E.T.io = [] := by
    simp only [progS3aB, Bool.and_eq_true, List.isEmpty_iff] at hT; exact hT.1.1
  have H : Hyp E O := ⟨hconf, hconds, href, fragT_of hT, hio, hO⟩
  have hf := fragT_of hT
  -- unroll every hart's cut path (the unrolling exposed)
  have hU : ∀ h, ∃ (k' : Nat) (ch : List Bool), h < E.T.harts.length →
      (∀ j < k', (E.st h j).pc ≠ (E.T.prog h).length) ∧
      (∀ j (i : Instr), (unrP E h k')[j]? = some i → ∃ (p : Nat) (i0 : Instr), (E.T.prog h)[p]? = some i0 ∧
        i = unr j i0) ∧
      (∀ i ∈ unrP E h k', instrS3a i = true) ∧
      symRun (unrP E h k') h ((unrP E h k').length + 1) (E.T.init h) ch =
        some { E.st h (kcut E O h) with pc := (unrP E h k').length } := by
    intro h
    by_cases hh : h < E.T.harts.length
    · obtain ⟨k', ch, h0, h1, h2, h3⟩ := unroll_runP hconf hf hh (kcut E O h)
      exact ⟨k', ch, fun _ => ⟨h0, h1, h2, h3⟩⟩
    · exact ⟨0, [], fun h' => absurd h' hh⟩
  let Kf : Nat → Nat := fun h => Classical.choose (hU h)
  let Uf : Nat → List Instr := fun h => unrP E h (Kf h)
  let Cf : Nat → List Bool := fun h => Classical.choose (Classical.choose_spec (hU h))
  have hUC : ∀ h, h < E.T.harts.length → _ := fun h => Classical.choose_spec (Classical.choose_spec (hU h))
  let n := E.T.harts.length
  let T' : Test := { harts := (List.range n).map Uf, regs0 := E.T.regs0, img := E.T.img, io := E.T.io,
                     cond := E.T.cond }
  let chs : List (List Bool) := (List.range n).map Cf
  let S : Nat → SSt := fun h => { E.st h (kcut E O h) with pc := (Uf h).length }
  let trs : List SSt := (List.range n).map S
  have hprog : ∀ h, h < n → T'.prog h = Uf h := by
    intro h hh; simp [T', Test.prog, List.getElem?_map, List.getElem?_range hh]
  have hinit : ∀ h, T'.init h = E.T.init h := fun h => rfl
  have hrun : T'.runAll chs = some trs := by
    unfold Test.runAll
    rw [if_pos (by simp [chs, T'])]
    have := runFrom_ok T' S chs 0 (fun j hj => by
      have hj' : j < n := by simpa [chs] using hj
      simp only [Nat.zero_add, chs, List.getElem_map, List.getElem_range]
      unfold Test.runH
      rw [hprog j hj', hinit]
      exact (hUC j hj').2.2.2)
    rw [this]
    simp [chs, trs]
  -- the unrolled execution is the cut execution
  have hconc : conc T' trs (νC E O) (gC E O) = XC E O := by
    unfold XC conc
    have : trs.mapIdx (fun h s => s.evs.mapIdx (fun i se => concEv (νC E O) h i se)) =
        (trsC E O).mapIdx (fun h s => s.evs.mapIdx (fun i se => concEv (νC E O) h i se)) := by
      apply List.ext_getElem?
      intro i
      rw [List.getElem?_mapIdx, List.getElem?_mapIdx]
      simp only [trs, trsC, List.getElem?_map]
      by_cases hi : i < n
      · rw [List.getElem?_range hi]; rfl
      · rw [List.getElem?_eq_none (by simp; omega)]; rfl
    rw [this]
    rfl
  have hcond : condsOk (νC E O) trs = condsOk (νC E O) (trsC E O) := by
    unfold condsOk
    simp only [trs, trsC, List.all_map]
    rfl
  have hT' : progS3bB T' = true := by
    apply progS3bB_of_S3a
    simp only [progS3aB, Bool.and_eq_true, List.all_eq_true] at hT ⊢
    refine ⟨⟨hT.1.1, fun p hp i hi => ?_⟩, hT.2⟩
    simp only [T', List.mem_map, List.mem_range] at hp
    obtain ⟨h, hh, rfl⟩ := hp
    exact (hUC h hh).2.2.1 i hi
  have hX : rvwmoRef (conc T' trs (νC E O) (gC E O)) := by rw [hconc]; exact rvwmoRef_XC H
  have hc : condsOk (νC E O) trs = true := by rw [hcond]; exact condsOk_C H
  have hss' : singleSize (conc T' trs (νC E O) (gC E O)) := by rw [hconc]; exact singleSize_XC H hss
  obtain ⟨run, hv, hpf, _, hdone, hrow, _, _⟩ := rvwmo_complete T' hT' hrun hc hX hss' trivial
  have hagree : ∀ o ∈ O, ∀ i ≤ o.2, (o.1, i) ∈ (conc T' trs (νC E O) (gC E O)).ids ∧
      (conc T' trs (νC E O) (gC E O)).ev (o.1, i) = E.ev (o.1, i) := by
    rw [hconc]; exact fun o ho i hi => agree_C H ho hi
  refine ⟨T', Kf, chs, trs, νC E O, gC E O, ⟨rfl, rfl, rfl, by simp [T', n], fun h j i hji => ?_⟩,
    fun h hh => ⟨hprog h hh, (hUC h hh).1⟩, hrun, hc, hX, hagree, run, hv, hpf, hdone, fun o ho => ?_⟩
  · by_cases hh : h < n
    · rw [hprog h hh] at hji; exact (hUC h hh).2.1 j i hji
    · have hp : T'.prog h = [] := by
        unfold Test.prog
        rw [List.getElem?_eq_none (by simp [T']; omega)]
        rfl
      rw [hp] at hji; simp at hji
  · rw [hrow o.1]
    exact row_prefix H (hagree o ho)

end Weak.Prom.InfLoop

end

#print axioms Weak.Prom.InfLoop.rvwmo_inf_completeP
