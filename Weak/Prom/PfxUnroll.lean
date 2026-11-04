/-
Weak/Prom: **S3d — composing the prefix lemma with `rvwmo_complete`** (plan rev 7 §0 "(T-inf)" and "(T-xv6)":
"proof = rvwmo_prefix ∘ rvwmo_complete ∘ …").

`rvwmo_complete` (CmpMain.lean) is stated for RefProg.lean's LOOP-FREE front end (`T.runAll`: forward branches, every
hart runs to its end).  A finite partial execution of a LOOPING program (PfxMain.lean `rvwmo_prefix`) is an
execution of a loop-free test: every hart's finite path, UNROLLED (`unrP`: the j-th executed instruction, a branch or
jump retargeted to j + 1 — both outcomes fall through, the path condition records the outcome).  The unrolled
symbolic run produces the SAME events, path conditions and registers (`unroll_sym`; only `pc` differs), so the cut
execution IS `conc T' trs ν g` of the unrolled test `T'` (same image, registers, I/O).

`rvwmo_inf_complete`: every (possibly infinite) execution of an S3a-scope program that the reference allows, with
NA-6 (`singleSizeI`, as `rvwmo_complete`), and every finite list `O` of its memory operations: there are an
unrolling `T'` of the program (`unrollOf`) and a VALID RUN of machine v2 on `T'` (promises first, every hart done)
whose every hart's load row EXTENDS `E`'s row up to each observed event.

What this does NOT give (recorded in PROGRESS-S3d.md): a run of machine v2 on the LOOPING program itself (the loop
front end `xStep`, OwnAFront.lean); the remaining bridge is machine-level (a litStep run of the unrolled program is
an xStep run of the loop program with the same labels: same instruction texts, branch labels `LCtrl`/`LInstr`
identical, only `pc` differs).
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Prom.PfxMain
import Weak.Prom.CmpMain

noncomputable section

namespace Weak.Prom.Pfx

open Classical
open MachCSL MachCSL.Stdpp Iris.Std
open Weak.Prom Weak.Prom.Mach Weak.Prom.Mach.Cert
open Weak.Prom.Ref
open Weak.Prom.Cmp (progS3aB progS3bB instrS3a progS3bB_of_S3a singleSize refRow machRow promisesFirst
  rvwmo_complete memOf)
open Cut

/-! ## 1. One unrolled step -/

theorem pc_emit (s : SSt) (p : Nat) (se : SEv) : ({ s with pc := p } : SSt).emit se = { s.emit se with pc := p } := rfl
theorem pc_wr (s : SSt) (p rd : Nat) (v : Ex × List Nat) :
    ({ s with pc := p } : SSt).wr rd v = { s.wr rd v with pc := p } := by unfold SSt.wr; split <;> rfl
theorem pc_adv (s : SSt) (p : Nat) : ({ s with pc := p } : SSt).adv = { s.adv with pc := p + 1 } := rfl
theorem pc_rd (s : SSt) (p r : Nat) : ({ s with pc := p } : SSt).rd r = s.rd r := rfl

/-- The `j`-th instruction of an unrolled path: a branch or jump goes to `j + 1` (forward). -/
def unr (j : Nat) : Instr → Instr
  | .br c a b _ => .br c a b (j + 1)
  | .jmp _ => .jmp (j + 1)
  | i => i

theorem unr_frag (j : Nat) (i : Instr) (hi : instrS3a i = true) : instrS3a (unr j i) = true := by
  cases i <;> simp_all [unr, instrS3a]

/-- The unrolled instruction at index `j` does what the loop instruction did, with `pc = j`. -/
theorem unr_step (h n m j : Nat) {s s' : SSt} (i : Instr) (hi : instrS3a i = true) (hj : j < m)
    (hs : stepL h n s i = .next s' ∨ ∃ t f, stepL h n s i = .fork t f ∧ (s' = t ∨ s' = f)) :
    stepI h m { s with pc := j } (unr j i) = .next { s' with pc := j + 1 } ∨
      ∃ t f, stepI h m { s with pc := j } (unr j i) = .fork t f ∧
        ({ s' with pc := j + 1 } = t ∨ { s' with pc := j + 1 } = f) := by
  cases i with
  | br c rs1 rs2 tgt =>
    right
    rcases hs with hs | ⟨t, f, hs, hst⟩
    · simp only [stepL] at hs; split at hs <;> cases hs
    · simp only [stepL] at hs
      split at hs
      · cases hs
      · simp only [Ref.StepR.fork.injEq] at hs
        obtain ⟨rfl, rfl⟩ := hs
        simp only [unr, stepI, pc_rd]
        rw [if_neg (by omega)]
        refine ⟨_, _, rfl, ?_⟩
        rcases hst with rfl | rfl
        · left; rfl
        · right; rfl
  | jmp tgt =>
    left
    rcases hs with hs | ⟨t, f, hs, _⟩
    · simp only [stepL] at hs
      split at hs
      · cases hs
      · simp only [Ref.StepR.next.injEq] at hs; subst hs
        simp only [unr, stepI]
        rw [if_neg (by omega)]
    · simp only [stepL] at hs; split at hs <;> cases hs
  | loadAq _ _ _ _ => simp [instrS3a] at hi
  | storeRl _ _ _ _ => simp [instrS3a] at hi
  | loadAqPc _ _ _ _ => simp [instrS3a] at hi
  | storeRlPc _ _ _ _ => simp [instrS3a] at hi
  | lr _ _ _ _ _ => simp [instrS3a] at hi
  | sc _ _ _ _ _ _ => simp [instrS3a] at hi
  | amo _ _ _ _ _ _ _ => simp [instrS3a] at hi
  | alui op rd rs1 imm =>
    left
    rcases hs with hs | ⟨t, f, hs, _⟩
    · simp only [stepL, stepI, Ref.StepR.next.injEq] at hs; subst hs
      simp only [unr, stepI, pc_rd, pc_wr, pc_adv]
    · simp [stepL, stepI] at hs
  | alu op rd rs1 rs2 =>
    left
    rcases hs with hs | ⟨t, f, hs, _⟩
    · simp only [stepL, stepI, Ref.StepR.next.injEq] at hs; subst hs
      simp only [unr, stepI, pc_rd, pc_wr, pc_adv]
    · simp [stepL, stepI] at hs
  | load sz sgn rd rs1 off =>
    left
    rcases hs with hs | ⟨t, f, hs, _⟩
    · simp only [stepL, stepI, Ref.StepR.next.injEq] at hs; subst hs
      simp only [unr, stepI, pc_rd, pc_wr, pc_adv, pc_emit]
    · simp [stepL, stepI] at hs
  | store sz rs2 rs1 off =>
    left
    rcases hs with hs | ⟨t, f, hs, _⟩
    · simp only [stepL, stepI, Ref.StepR.next.injEq] at hs; subst hs
      simp only [unr, stepI, pc_rd, pc_adv, pc_emit]
    · simp [stepL, stepI] at hs
  | fence fs =>
    left
    rcases hs with hs | ⟨t, f, hs, _⟩
    · simp only [stepL, stepI, Ref.StepR.next.injEq] at hs; subst hs
      rfl
    · simp [stepL, stepI] at hs
  | fenceTso =>
    left
    rcases hs with hs | ⟨t, f, hs, _⟩
    · simp only [stepL, stepI, Ref.StepR.next.injEq] at hs; subst hs
      rfl
    · simp [stepL, stepI] at hs
  | csrr rd v =>
    left
    rcases hs with hs | ⟨t, f, hs, _⟩
    · simp only [stepL, stepI, Ref.StepR.next.injEq] at hs; subst hs
      simp only [unr, stepI, pc_wr, pc_adv]
    · simp [stepL, stepI] at hs
  | fencei =>
    left
    rcases hs with hs | ⟨t, f, hs, _⟩
    · simp only [stepL, stepI, Ref.StepR.next.injEq] at hs; subst hs
      rfl
    · simp [stepL, stepI] at hs
  | nop =>
    left
    rcases hs with hs | ⟨t, f, hs, _⟩
    · simp only [stepL, stepI, Ref.StepR.next.injEq] at hs; subst hs
      rfl
    · simp [stepL, stepI] at hs

/-! ## 2. One hart's unrolled path -/

/-- The instruction hart `h` executes at step `j`. -/
def iAt (E : IExec) (h j : Nat) : Instr := ((E.T.prog h)[(E.st h j).pc]?).getD .nop

/-- The unrolled program of hart `h`'s first `k` steps. -/
def unrP (E : IExec) (h k : Nat) : List Instr := (List.range k).map (fun j => unr j (iAt E h j))

section run

variable {E : IExec} (hc : E.conforms) (hf : FragT E.T) {h : Nat} (hh : h < E.T.harts.length)
include hc hf hh

theorem halted_stay {j : Nat} (hp : (E.st h j).pc = (E.T.prog h).length) : ∀ d, E.st h (j + d) = E.st h j := by
  intro d
  induction d with
  | zero => rfl
  | succ d ih =>
    rcases (hc h hh).2 (j + d) with ⟨_, he⟩ | ⟨i, hi, _⟩
    · rw [← Nat.add_assoc, he, ih]
    · rw [ih, hp] at hi; simp at hi

theorem nonhalted_prefix (k : Nat) :
    ∃ k', E.st h k' = E.st h k ∧ ∀ j < k', (E.st h j).pc ≠ (E.T.prog h).length := by
  induction k with
  | zero => exact ⟨0, rfl, fun j hj => absurd hj (Nat.not_lt_zero _)⟩
  | succ k ih =>
    obtain ⟨k', hk1, hk2⟩ := ih
    by_cases hp : (E.st h k).pc = (E.T.prog h).length
    · refine ⟨k', ?_, hk2⟩
      rw [hk1, show k + 1 = k + 1 from rfl, halted_stay hc hf hh hp 1]
    · refine ⟨k + 1, rfl, fun j hj => ?_⟩
      intro hj'
      apply hp
      rcases Nat.lt_or_ge j k with h1 | h1
      · obtain ⟨d, rfl⟩ : ∃ d, k = j + d := ⟨k - j, by omega⟩
        rw [halted_stay hc hf hh hj' d]; exact hj'
      · have : j = k := by omega
        subst this; exact hj'

theorem unroll_sym (k' : Nat) (hk : ∀ j < k', (E.st h j).pc ≠ (E.T.prog h).length) :
    ∀ d ≤ k', ∃ ch, symRun (unrP E h k') h (d + 1) { E.st h (k' - d) with pc := k' - d } ch =
      some { E.st h k' with pc := k' } := by
  have hlen : (unrP E h k').length = k' := by simp [unrP]
  intro d
  induction d with
  | zero =>
    intro _
    refine ⟨[], ?_⟩
    unfold symRun
    rw [if_pos (by simp [hlen]), if_pos rfl]
    simp
  | succ d ih =>
    intro hd
    obtain ⟨ch', hch'⟩ := ih (by omega)
    have hj : k' - (d + 1) < k' := by omega
    have hj1 : k' - (d + 1) + 1 = k' - d := by omega
    generalize hjj : k' - (d + 1) = j at hj hj1 ⊢
    rw [← hj1] at hch'
    have hnh := hk j hj
    rcases (hc h hh).2 j with ⟨hp, _⟩ | ⟨i, hi, hs⟩
    · exact absurd hp hnh
    have hiA : iAt E h j = i := by unfold iAt; rw [hi]; rfl
    have hfr : instrS3a i = true := hf h i (List.mem_of_getElem? hi)
    have hU : (unrP E h k')[j]? = some (unr j i) := by
      simp only [unrP, List.getElem?_map, List.getElem?_range hj, Option.map_some, hiA]
    rcases unr_step h _ (unrP E h k').length j i hfr (by rw [hlen]; exact hj) hs with hst | ⟨t, f, hst, htf⟩
    · refine ⟨ch', ?_⟩
      unfold symRun
      rw [if_neg (by simp only [hlen]; omega), hU]
      simp only
      rw [hst]
      exact hch'
    · rcases htf with htf | htf
      · refine ⟨true :: ch', ?_⟩
        unfold symRun
        rw [if_neg (by simp only [hlen]; omega), hU]
        simp only
        rw [hst]
        simp only
        rw [← htf]; exact hch'
      · refine ⟨false :: ch', ?_⟩
        unfold symRun
        rw [if_neg (by simp only [hlen]; omega), hU]
        simp only
        rw [hst]
        simp only
        rw [← htf]; exact hch'

/-- **Hart `h`'s first `k` steps, unrolled**: a loop-free program whose symbolic run from the initial state reaches
`E`'s state at step `k` (up to `pc`). -/
theorem unroll_run (k : Nat) :
    ∃ (U : List Instr) (ch : List Bool), (∀ j (i : Instr), U[j]? = some i → ∃ (p : Nat) (i0 : Instr), (E.T.prog h)[p]? = some i0 ∧
        i = unr j i0) ∧ (∀ i ∈ U, instrS3a i = true) ∧
      symRun U h (U.length + 1) (E.T.init h) ch = some { E.st h k with pc := U.length } := by
  obtain ⟨k', hk1, hk2⟩ := nonhalted_prefix hc hf hh k
  have hlen : (unrP E h k').length = k' := by simp [unrP]
  have hiA : ∀ j < k', ∃ i0, (E.T.prog h)[(E.st h j).pc]? = some i0 ∧ iAt E h j = i0 := by
    intro j hj
    rcases (hc h hh).2 j with ⟨hp, _⟩ | ⟨i, hi, _⟩
    · exact absurd hp (hk2 j hj)
    · exact ⟨i, hi, by unfold iAt; rw [hi]; rfl⟩
  obtain ⟨ch, hch⟩ := unroll_sym hc hf hh k' hk2 k' (Nat.le_refl _)
  refine ⟨unrP E h k', ch, fun j i hji => ?_, fun i hi => ?_, ?_⟩
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

end run

/-! ## 3. The unrolled test -/

/-- `T'` is an UNROLLING of `T`: same initial registers, image and I/O, the same number of harts, and every
instruction of a hart is an instruction of `T`'s same hart, a branch or jump retargeted to the next index. -/
def unrollOf (T T' : Test) : Prop :=
  T'.regs0 = T.regs0 ∧ T'.img = T.img ∧ T'.io = T.io ∧ T'.harts.length = T.harts.length ∧
    ∀ h j (i : Instr), (T'.prog h)[j]? = some i → ∃ (p : Nat) (i0 : Instr), (T.prog h)[p]? = some i0 ∧ i = unr j i0

/-- NA-6 over an infinite execution (CmpDefs.lean `singleSize`): two memory operations touching a common byte have
the same address and size. -/
def singleSizeI (E : IExec) : Prop :=
  ∀ a b, E.isMem a → E.isMem b → overlapB (E.ev a) (E.ev b) = true →
    (E.ev a).pa = (E.ev b).pa ∧ (E.sk a).sz = (E.sk b).sz

theorem runFrom_ok (T : Test) (S : Nat → SSt) :
    ∀ (chs : List (List Bool)) (k : Nat), (∀ j (hj : j < chs.length), T.runH (k + j) chs[j] = some (S (k + j))) →
      T.runFrom k chs = some ((List.range chs.length).map (fun j => S (k + j)))
  | [], _, _ => rfl
  | c :: cs, k, H => by
    have h0 := H 0 (by simp)
    have ih := runFrom_ok T S cs (k + 1) (fun j hj => by
      have := H (j + 1) (by simp; omega)
      simp only [List.getElem_cons_succ] at this
      rw [show k + 1 + j = k + (j + 1) by omega]; exact this)
    simp only [Nat.add_zero, List.getElem_cons_zero] at h0
    unfold Test.runFrom
    rw [h0, ih]
    simp only [List.length_cons, Option.some.injEq]
    rw [List.range_succ_eq_map]
    simp only [List.map_cons, List.map_map, Nat.add_zero]
    congr 1
    apply List.map_congr_left
    intro j _
    simp only [Function.comp]
    rw [show k + (j + 1) = k + 1 + j by omega]

section main

variable {E : IExec} {O : List EvId} (H : Hyp E O)
include H

theorem singleSize_XC (hss : singleSizeI E) : singleSize (XC E O) := by
  intro a ha b hb hma hmb hov
  have hai := (XC_ids H a).1 ha
  have hbi := (XC_ids H b).1 hb
  rw [XC_sk H hai] at hma ⊢
  rw [XC_sk H hbi] at hmb ⊢
  have hka : ((XC E O).ev a).sk = (E.ev a).sk := XC_sk H hai
  have hkb : ((XC E O).ev b).sk = (E.ev b).sk := XC_sk H hbi
  unfold overlapB at hov
  rw [XC_pa H hai, XC_pa H hbi, hka, hkb] at hov
  rw [XC_pa H hai, XC_pa H hbi]
  exact hss a b ⟨inD_has H hai, hma⟩ ⟨inD_has H hbi, hmb⟩ hov

/-- The row prefix: the first events of a hart of the cut are `E`'s. -/
theorem row_prefix {X : Exec} {o : EvId} (hids : ∀ i ≤ o.2, (o.1, i) ∈ X.ids ∧ X.ev (o.1, i) = E.ev (o.1, i)) :
    (((List.range (o.2 + 1)).map (fun i => E.ev (o.1, i))).filter (fun v => v.sk.kind.isLoad)).map Ev.rdat <+:
      refRow X o.1 := by
  unfold refRow
  apply List.IsPrefix.map
  apply List.IsPrefix.filter
  have hl : ((X.evs[o.1]?).getD []).take (o.2 + 1) = (List.range (o.2 + 1)).map (fun i => E.ev (o.1, i)) := by
    apply List.ext_getElem?
    intro i
    rw [List.getElem?_take, List.getElem?_map]
    by_cases hi : i < o.2 + 1
    · rw [if_pos hi, List.getElem?_range hi, Option.map_some]
      obtain ⟨hm, he⟩ := hids i (by omega)
      rw [← he]
      obtain ⟨l, hl1, hl2⟩ := (mem_idsOf _ _).1 hm
      simp only at hl1 hl2
      unfold Exec.ev
      rw [hl1]
      simp [List.getElem?_eq_getElem hl2]
    · rw [if_neg hi, List.getElem?_eq_none (by simp; omega)]
      rfl
  rw [← hl]
  exact List.take_prefix _ _

end main

/-- **(T-inf) composed with (T-cmp), S3a scope.**  Every (possibly infinite) execution of an S3a-scope program
that the reference allows (with NA-6), and every finite list `O` of its memory operations: some unrolling `T'` of
the program has an execution `conc T' trs ν g` (RefProg.lean's `runAll`, `condsOk`, Ref.lean's `rvwmoRef`) that
agrees with `E` on every event up to an observed one, and machine v2 has a valid run of `T'` (promises first, every
hart done) whose every hart's load row EXTENDS `E`'s row up to each observed event. -/
theorem rvwmo_inf_complete {T : Test} (hT : progS3aB T = true) {E : IExec} (hE : infExec T E)
    (hss : singleSizeI E) (O : List EvId) (hO : ∀ e ∈ O, E.isMem e) :
    ∃ (T' : Test) (chs : List (List Bool)) (trs : List SSt) (ν : Val) (g : List EvId),
      unrollOf T T' ∧ T'.runAll chs = some trs ∧ condsOk ν trs = true ∧ rvwmoRef (conc T' trs ν g) ∧
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
  -- unroll every hart's cut path
  have hU : ∀ h, ∃ (U : List Instr) (ch : List Bool), h < E.T.harts.length →
      (∀ j (i : Instr), U[j]? = some i → ∃ (p : Nat) (i0 : Instr), (E.T.prog h)[p]? = some i0 ∧ i = unr j i0) ∧
      (∀ i ∈ U, instrS3a i = true) ∧
      symRun U h (U.length + 1) (E.T.init h) ch = some { E.st h (kcut E O h) with pc := U.length } := by
    intro h
    by_cases hh : h < E.T.harts.length
    · obtain ⟨U, ch, h1, h2, h3⟩ := unroll_run hconf hf hh (kcut E O h)
      exact ⟨U, ch, fun _ => ⟨h1, h2, h3⟩⟩
    · exact ⟨[], [], fun h' => absurd h' hh⟩
  let Uf : Nat → List Instr := fun h => Classical.choose (hU h)
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
      exact (hUC j hj').2.2)
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
    exact (hUC h hh).2.1 i hi
  have hX : rvwmoRef (conc T' trs (νC E O) (gC E O)) := by rw [hconc]; exact rvwmoRef_XC H
  have hc : condsOk (νC E O) trs = true := by rw [hcond]; exact condsOk_C H
  have hss' : singleSize (conc T' trs (νC E O) (gC E O)) := by rw [hconc]; exact singleSize_XC H hss
  obtain ⟨run, hv, hpf, _, hdone, hrow, _, _⟩ := rvwmo_complete T' hT' hrun hc hX hss' trivial
  have hagree : ∀ o ∈ O, ∀ i ≤ o.2, (o.1, i) ∈ (conc T' trs (νC E O) (gC E O)).ids ∧
      (conc T' trs (νC E O) (gC E O)).ev (o.1, i) = E.ev (o.1, i) := by
    rw [hconc]; exact fun o ho i hi => agree_C H ho hi
  refine ⟨T', chs, trs, νC E O, gC E O, ⟨rfl, rfl, rfl, by simp [T', n], fun h j i hji => ?_⟩, hrun, hc, hX, hagree,
    run, hv, hpf, hdone, fun o ho => ?_⟩
  · by_cases hh : h < n
    · rw [hprog h hh] at hji; exact (hUC h hh).1 j i hji
    · have hp : T'.prog h = [] := by
        unfold Test.prog
        rw [List.getElem?_eq_none (by simp [T']; omega)]
        rfl
      rw [hp] at hji; simp at hji
  · rw [hrow o.1]
    exact row_prefix H (hagree o ho)

end Weak.Prom.Pfx

end
