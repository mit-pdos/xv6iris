/-
Weak/Prom: **completeness of the per-hart explorer of machine v2** (S0-P part (2), milestone 2b, statements 3–4,
for the checker of `Weak/Prom/MachForbid.lean`).

* `memStepF_complete` — `memStep … l ots ws' prom' → memStepF … l ots = some (ws', prom')`: the memory half as a
  function (MachSound.lean) is EXACT (with `memStepF_sound`).  Rests on the Bool completeness of every transcribed
  premise (`invalReadB_complete`, `loadOkB_complete`, …).
* `labCands` — every label a litmus hart (`litNext`, MachCert.lean) can emit next, with every answer run the memory
  could give (`ansRuns`: per byte every timestamp `0 … |M|` holding it); `labCands_complete`.
* `soloDFS` — the DFS of one hart's solo runs against `M` (labels from `labCands`, fulfil timestamps from
  `tsOpts`, each step by `litNext` and `memStepF`); `soloDFS_complete`: if the DFS did not run out of fuel, every
  solo run's final state is listed.  (The brute-force answer generator replaces `Mach.succ`'s pruned `readCands` of
  milestone 1: same role, a one-line completeness argument.)
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Prom.MachCert
import Weak.Prom.MachSolo

namespace Weak.Prom.Mach

open MachCSL MachCSL.Stdpp Iris.Std
open Weak (Image Dsrc)
open Weak.Prom Weak.Prom.Mach.Cert
open Weak.Prom.Ref (Instr Test two64 aluOp brEval amoOp sext byteList bytesVal)
open PLabel

/-! ## 1. Bool completeness of the transcribed premises -/

theorem notB_of_not {b : Bool} {p : Prop} (hb : b = true ↔ p) (h : ¬ p) : (!b) = true := by
  cases hbb : b
  · rfl
  · exact absurd (hb.1 hbb) h

theorem invalReadB_complete {log : List PMsg} {a : Int} {t fl : Nat} (h : invalRead log a t fl) :
    invalReadB log a t fl = true := by
  obtain ⟨ti, hc, hlt, hnw, hno, hall⟩ := h
  have hti := cmoAt_lt hc
  unfold invalReadB
  refine List.any_eq_true.2 ⟨ti, List.mem_range'_1.2 ⟨by omega, by omega⟩, ?_⟩
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨(cmoAtB_iff ..).2 hc, notB_of_not (writesInB_iff ..) hnw⟩, ?_⟩, ?_⟩
  · apply notB_of_not List.any_eq_true
    rintro ⟨ti', hm, hb⟩
    rw [List.mem_range'_1] at hm
    exact hno ⟨ti', by omega, by omega, (cmoAtB_iff ..).1 hb⟩
  · refine List.all_eq_true.2 (fun c hc' => ?_)
    rw [List.mem_range] at hc'
    simp only [Bool.or_eq_true]
    cases hb : cmoAtB log isCleanK c a
    · left; rfl
    · right; exact notB_of_not (writesInB_iff ..) (hall c hc' ((cmoAtB_iff ..).1 hb))

theorem bytesAllB_complete {P : Int → Nat → BitVec 8 → Bool} {Q : Int → Nat → BitVec 8 → Prop}
    (hQP : ∀ a t v, Q a t v → P a t v = true) :
    ∀ (a : Int) (l : List (Nat × BitVec 8)), bytesAll Q a l → bytesAllB P a l = true
  | _, [], _ => rfl
  | a, (t, v) :: r, ⟨h1, h2⟩ => by
    simp only [bytesAllB, Bool.and_eq_true]
    exact ⟨hQP a t v h1, bytesAllB_complete hQP (a + 1) r h2⟩

theorem loadOkB_complete {img : Image} {log : List PMsg} {ws : PState} {vpre : Nat} {base : Int}
    {tvs : List (Nat × BitVec 8)} (h : loadOk img log ws vpre base tvs) :
    loadOkB img log ws vpre base tvs = true := by
  unfold loadOkB
  unfold loadOk at h
  refine bytesAllB_complete (fun a t v hp => ?_) base tvs h
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq]
  refine ⟨hp.1, ?_⟩
  rcases hp.2 with h2 | h2
  · exact .inl (notB_of_not (writesInB_iff ..) h2)
  · exact .inr (invalReadB_complete h2)

/-- `memStepF` IS COMPLETE: it computes every `memStep`. -/
theorem memStepF_complete {img : Image} {log : List PMsg} {i : Nat} {prom : GSet Nat} {ws : PState}
    {l : PLabel} {ots : Option Nat} {ws' : PState} {prom' : GSet Nat}
    (h : memStep img log i prom ws l ots ws' prom') : memStepF img log i prom ws l ots = some (ws', prom') := by
  cases h with
  | silent => rfl
  | load aq rl base tvs asrc hok => simp [memStepF, okIf, loadOkB_complete hok]
  | store aq rl base data asrc vsrc ts hts hm hc hpv =>
    simp [memStepF, okIf, (promHas_iff ..).2 hts, hm, (cohBelowB_iff ..).2 hc, hpv]
  | rmw aq rl base tvs data asrc vsrc ts hlen hts hm hok hx hc hpv =>
    simp [memStepF, okIf, hlen, (promHas_iff ..).2 hts, hm, loadOkB_complete hok, (exclOkB_iff ..).2 hx,
      (cohBelowB_iff ..).2 hc, hpv]
  | amoLd aq base tvs asrc hok => simp [memStepF, okIf, loadOkB_complete hok]
  | amoSt rl base data asrc vsrc ts R hR hb hlen hts hm hx hc hpv =>
    simp [memStepF, okIf, hR, hb, hlen, (promHas_iff ..).2 hts, hm, (exclOkB_iff ..).2 hx,
      (cohBelowB_iff ..).2 hc, hpv]
  | fence => rfl
  | fenceI => rfl
  | dev => rfl
  | regW => rfl
  | ctrl => rfl
  | instr => rfl
  | lr aq rl base tvs asrc hok => simp [memStepF, okIf, loadOkB_complete hok]
  | sc aq rl base data asrc vsrc ts R hR hts hm hx hlt hc hpv =>
    have hall : R.rvTs.all (fun t => decide (t < ts)) = true :=
      List.all_eq_true.2 (fun t ht => decide_eq_true (hlt t ht))
    simp [memStepF, okIf, hR, (promHas_iff ..).2 hts, hm, (exclOkB_iff ..).2 hx, hall,
      (cohBelowB_iff ..).2 hc, hpv]
  | scFail => rfl
  | fetch base tvs hok =>
    have hb : bytesAllB (fun a t v => memByte img log t a == some v && !writesInB log a t ws.wIfl) base tvs =
        true := by
      refine bytesAllB_complete (fun a t v hp => ?_) base tvs hok
      simp only [Bool.and_eq_true, beq_iff_eq]
      exact ⟨hp.1, notB_of_not (writesInB_iff ..) hp.2⟩
    simp [memStepF, okIf, hb]
  | cmo k base len asrc ts hts hm hc hpv =>
    simp [memStepF, okIf, (promHas_iff ..).2 hts, hm, (cohBelowB_iff ..).2 hc, hpv]

/-! ## 2. Facts about a state step's label -/

/-- Every answer of a read label is a byte the memory holds at its timestamp. -/
theorem memStep_reads {img : Image} {log : List PMsg} {i : Nat} {prom : GSet Nat} {ws : PState}
    {l : PLabel} {ots : Option Nat} {ws' : PState} {prom' : GSet Nat}
    (h : memStep img log i prom ws l ots ws' prom') :
    ∀ base tvs, labelReads l = some (base, tvs) → bytesAll (fun a t v => memByte img log t a = some v) base tvs := by
  intro b tvs hl
  cases h with
  | load aq rl base tvs' asrc hok =>
    simp only [labelReads, Option.some.injEq, Prod.mk.injEq] at hl
    obtain ⟨rfl, rfl⟩ := hl
    exact bytesAll_mono (fun _ _ _ hp => hp.1) _ _ hok
  | rmw aq rl base tvs' data asrc vsrc ts _ _ _ hok =>
    simp only [labelReads, Option.some.injEq, Prod.mk.injEq] at hl
    obtain ⟨rfl, rfl⟩ := hl
    exact bytesAll_mono (fun _ _ _ hp => hp.1) _ _ hok
  | amoLd aq base tvs' asrc hok =>
    simp only [labelReads, Option.some.injEq, Prod.mk.injEq] at hl
    obtain ⟨rfl, rfl⟩ := hl
    exact bytesAll_mono (fun _ _ _ hp => hp.1) _ _ hok
  | lr aq rl base tvs' asrc hok =>
    simp only [labelReads, Option.some.injEq, Prod.mk.injEq] at hl
    obtain ⟨rfl, rfl⟩ := hl
    exact bytesAll_mono (fun _ _ _ hp => hp.1) _ _ hok
  | fetch base tvs' hok =>
    simp only [labelReads, Option.some.injEq, Prod.mk.injEq] at hl
    obtain ⟨rfl, rfl⟩ := hl
    exact bytesAll_mono (fun _ _ _ hp => hp.1) _ _ hok
  | _ => simp [labelReads] at hl

/-- The fulfil-timestamp options of a step against `M`. -/
def tsOpts (M : List PMsg) : List (Option Nat) := none :: (List.range (M.length + 1)).map some

theorem tsOpts_complete {img : Image} {log : List PMsg} {i : Nat} {prom : GSet Nat} {ws : PState}
    {l : PLabel} {ots : Option Nat} {ws' : PState} {prom' : GSet Nat}
    (h : memStep img log i prom ws l ots ws' prom') : ots ∈ tsOpts log := by
  have key : ∀ ts (m : PMsg), log[ts - 1]? = some m → some ts ∈ tsOpts log := by
    intro ts m hm
    have := (List.getElem?_eq_some_iff.1 hm).1
    exact List.mem_cons_of_mem _ (List.mem_map.2 ⟨ts, List.mem_range.2 (by omega), rfl⟩)
  cases h with
  | store _ _ _ _ _ _ ts _ hm => exact key ts _ hm
  | rmw _ _ _ _ _ _ _ ts _ _ hm => exact key ts _ hm
  | amoSt _ _ _ _ _ ts _ _ _ _ _ hm => exact key ts _ hm
  | sc _ _ _ _ _ _ ts _ _ _ hm => exact key ts _ hm
  | cmo _ _ _ _ ts _ hm => exact key ts _ hm
  | _ => exact List.mem_cons_self ..

/-! ## 3. Label candidates -/

/-- The answers a byte at `a` may carry: every timestamp `0 … |M|` holding it, with its value. -/
def ansOpts (img : Image) (M : List PMsg) (a : Int) : List (Nat × BitVec 8) :=
  (List.range (M.length + 1)).filterMap (fun t => (memByte img M t a).map (fun v => (t, v)))

/-- Every answer run of `k` bytes from `a`. -/
def ansRuns (img : Image) (M : List PMsg) : Int → Nat → List (List (Nat × BitVec 8))
  | _, 0 => [[]]
  | a, k + 1 => (ansOpts img M a).flatMap (fun tv => (ansRuns img M (a + 1) k).map (tv :: ·))

theorem ansRuns_complete {img : Image} {M : List PMsg} :
    ∀ (a : Int) (tvs : List (Nat × BitVec 8)), bytesAll (fun a t v => memByte img M t a = some v) a tvs →
      tvs ∈ ansRuns img M a tvs.length
  | _, [], _ => List.mem_singleton.2 rfl
  | a, (t, v) :: r, ⟨h1, h2⟩ => by
    simp only [List.length_cons, ansRuns]
    refine List.mem_flatMap.2 ⟨(t, v), ?_, List.mem_map.2 ⟨r, ansRuns_complete (a + 1) r h2, rfl⟩⟩
    refine List.mem_filterMap.2 ⟨t, List.mem_range.2 (by have := memByte_le h1; omega), ?_⟩
    rw [h1]; rfl

/-- The labels instruction `ins` may emit first, at state `s`, with read answers from `ans base sz`. -/
def insLabs (ans : Int → Nat → List (List (Nat × BitVec 8))) (s : LP) : Instr → List PLabel
  | .alui _ rd rs1 _ => (regWL rd (srcR rs1) ++ [LInstr]).take 1
  | .alu _ rd rs1 rs2 => (regWL rd (srcR rs1 ++ srcR rs2) ++ [LInstr]).take 1
  | .load sz _ _ rs1 off =>
    let a := (s.rd rs1 + off) % two64
    (ans (a : Int) sz).map (fun tvs => LLoad false false a tvs (srcR rs1))
  | .store sz rs2 rs1 off =>
    let a := (s.rd rs1 + off) % two64
    [LStore false false a (toBytes (s.rd rs2) sz) (srcR rs1) (srcR rs2)]
  | .loadAq sz rl _ rs1 =>
    (ans (s.rd rs1 : Int) sz).map (fun tvs => LLoad true rl (s.rd rs1) tvs (srcR rs1))
  | .storeRl sz aq rs2 rs1 => [LStore aq true (s.rd rs1) (toBytes (s.rd rs2) sz) (srcR rs1) (srcR rs2)]
  | .loadAqPc .. => []
  | .storeRlPc .. => []
  | .lr sz aq rl _ rs1 =>
    (ans (s.rd rs1 : Int) sz).map (fun tvs => LExLoad aq (aq && rl) (s.rd rs1) tvs (srcR rs1))
  | .sc sz aq rl _ rs2 rs1 =>
    [LExStore (aq && rl) rl (s.rd rs1) (toBytes (s.rd rs2) sz) (srcR rs1) (srcR rs2), LExFail]
  | .amo op sz aq rl _ rs2 rs1 =>
    (ans (s.rd rs1 : Int) sz).map (fun tvs => LRmw aq rl (s.rd rs1) tvs
      (toBytes (amoOp op sz (ofBytes (tvs.map Prod.snd)) (s.rd rs2 % 2 ^ (8 * sz))) sz) (srcR rs1) (srcR rs2))
  | .fence f => [LFence f.pr f.pw f.sr f.sw]
  | .fenceTso => [LFence true false true true]
  | .br _ rs1 rs2 _ => [LCtrl (srcR rs1 ++ srcR rs2)]
  | .jmp _ => [LInstr]
  | .csrr rd _ => (regWL rd [] ++ [LInstr]).take 1
  | .fencei => [LFenceI]
  | .nop => [LInstr]

/-- Every label the hart may emit next. -/
def labCands (img : Image) (M : List PMsg) (s : LP) : List PLabel :=
  match s.q with
  | l0 :: _ => [l0]
  | [] =>
    match s.prog[s.pc]? with
    | some ins => insLabs (ansRuns img M) s ins
    | none => []

theorem go1_mem {s : LP} {regs' : List Nat} {pc' : Nat} {labs : List PLabel} {l : PLabel} {s' : LP}
    (h : go1 s regs' pc' labs l = some s') : l ∈ labs.take 1 := by
  unfold go1 at h
  cases labs with
  | nil => cases h
  | cons l0 rest =>
    simp only at h
    split at h
    · rename_i he; subst he; simp
    · cases h

theorem ite_none_some {α : Type} {c : Prop} [Decidable c] {x : Option α} {y : α}
    (h : (if c then none else x) = some y) : x = some y := by
  split at h
  · cases h
  · exact h

theorem ite_some_none {α : Type} {c : Prop} [Decidable c] {x y : α} (h : (if c then some x else none) = some y) :
    c ∧ x = y := by
  split at h
  · rename_i hc; cases h; exact ⟨hc, rfl⟩
  · cases h

/-- THE FIRST-LABEL CANDIDATES ARE COMPLETE, for any answer generator that contains the label's answers. -/
theorem insLabs_complete {ans : Int → Nat → List (List (Nat × BitVec 8))} {n : Nat} {s s' : LP} {ins : Instr}
    {l : PLabel} (h : instrNext n s ins l = some s')
    (hr : ∀ base tvs, labelReads l = some (base, tvs) → tvs ∈ ans base tvs.length) :
    l ∈ insLabs ans s ins := by
  cases ins with
  | alui op rd rs1 imm => simp only [instrNext] at h; exact go1_mem h
  | alu op rd rs1 rs2 => simp only [instrNext] at h; exact go1_mem h
  | load sz sgn rd rs1 off =>
    replace h := ite_none_some h
    cases l
    all_goals try (simp only [reduceCtorEq] at h; done)
    rename_i aq rl b tvs asrc
    obtain ⟨⟨h1, h2, h3, h4, h5⟩, _⟩ := ite_some_none h
    subst h1 h2 h3 h5
    simp only [insLabs]
    exact List.mem_map.2 ⟨tvs, h4 ▸ hr _ _ rfl, rfl⟩
  | store sz rs2 rs1 off =>
    replace h := ite_none_some h
    cases l
    all_goals try (simp only [reduceCtorEq] at h; done)
    rename_i aq rl b data asrc vsrc
    obtain ⟨⟨h1, h2, h3, h4, h5, h6⟩, _⟩ := ite_some_none h
    subst h1 h2 h3 h4 h5 h6
    simp [insLabs]
  | loadAq sz rl0 rd rs1 =>
    replace h := ite_none_some h
    cases l
    all_goals try (simp only [reduceCtorEq] at h; done)
    rename_i aq rl b tvs asrc
    obtain ⟨⟨h1, h2, h3, h4, h5⟩, _⟩ := ite_some_none h
    subst h1 h2 h3 h5
    simp only [insLabs]
    exact List.mem_map.2 ⟨tvs, h4 ▸ hr _ _ rfl, rfl⟩
  | storeRl sz aq0 rs2 rs1 =>
    replace h := ite_none_some h
    cases l
    all_goals try (simp only [reduceCtorEq] at h; done)
    rename_i aq rl b data asrc vsrc
    obtain ⟨⟨h1, h2, h3, h4, h5, h6⟩, _⟩ := ite_some_none h
    subst h1 h2 h3 h4 h5 h6
    simp [insLabs]
  | loadAqPc => cases h
  | storeRlPc => cases h
  | lr sz aq0 rl0 rd rs1 =>
    replace h := ite_none_some h
    cases l
    all_goals try (simp only [reduceCtorEq] at h; done)
    rename_i aq rl b tvs asrc
    obtain ⟨⟨h1, h2, h3, h4, h5⟩, _⟩ := ite_some_none h
    subst h1 h2 h3 h5
    simp only [insLabs]
    exact List.mem_map.2 ⟨tvs, h4 ▸ hr _ _ rfl, rfl⟩
  | sc sz aq0 rl0 rd rs2 rs1 =>
    replace h := ite_none_some h
    cases l
    all_goals try (simp only [reduceCtorEq] at h; done)
    · rename_i aq rl b data asrc vsrc
      obtain ⟨⟨h1, h2, h3, h4, h5, h6⟩, _⟩ := ite_some_none h
      subst h1 h2 h3 h4 h5 h6
      simp [insLabs]
    · simp [insLabs]
  | amo op sz aq0 rl0 rd rs2 rs1 =>
    replace h := ite_none_some h
    cases l
    all_goals try (simp only [reduceCtorEq] at h; done)
    rename_i aq rl b tvs data asrc vsrc
    obtain ⟨⟨h1, h2, h3, h4, h5, h6, h7⟩, _⟩ := ite_some_none h
    subst h1 h2 h3 h5 h6 h7
    simp only [insLabs]
    exact List.mem_map.2 ⟨tvs, h4 ▸ hr _ _ rfl, rfl⟩
  | fence f => simp only [instrNext] at h; exact go1_mem h
  | fenceTso => simp only [instrNext] at h; exact go1_mem h
  | br c rs1 rs2 tgt =>
    replace h := ite_none_some h
    exact go1_mem h
  | jmp tgt =>
    replace h := ite_none_some h
    exact go1_mem h
  | csrr rd v => simp only [instrNext] at h; exact go1_mem h
  | fencei => simp only [instrNext] at h; exact go1_mem h
  | nop => simp only [instrNext] at h; exact go1_mem h

/-- THE LABEL CANDIDATES ARE COMPLETE: every label the hart can emit whose answers the memory holds. -/
theorem labCands_complete {img : Image} {M : List PMsg} {s s' : LP} {l : PLabel}
    (h : litNext s l = some s')
    (hr : ∀ base tvs, labelReads l = some (base, tvs) → bytesAll (fun a t v => memByte img M t a = some v) base tvs) :
    l ∈ labCands img M s := by
  unfold litNext at h
  unfold labCands
  cases hq : s.q with
  | cons l0 rest =>
    rw [hq] at h
    simp only at h ⊢
    split at h
    · rename_i he; subst he; exact List.mem_singleton.2 rfl
    · cases h
  | nil =>
    rw [hq] at h
    simp only at h ⊢
    cases hp : s.prog[s.pc]? with
    | none => rw [hp] at h; cases h
    | some ins =>
      rw [hp] at h
      simp only at h ⊢
      exact insLabs_complete h (fun base tvs hl => ansRuns_complete _ _ (hr base tvs hl))

/-! ## 4. The solo DFS -/

/-- Every successor of a solo state against `M`. -/
def soloKids (img : Image) (M : List PMsg) (i : Nat) (x : LP × PState × GSet Nat) :
    List (LP × PState × GSet Nat) :=
  (labCands img M x.1).flatMap (fun l => (tsOpts M).filterMap (fun o =>
    match litNext x.1 l, memStepF img M i x.2.2 x.2.1 l o with
    | some s', some (ws', p') => some (s', ws', p')
    | _, _ => none))

/-- The DFS of hart `i`'s solo runs against `M`: every reachable state, and whether the fuel ran out. -/
def soloDFS (img : Image) (M : List PMsg) (i : Nat) : Nat → LP × PState × GSet Nat →
    List (LP × PState × GSet Nat) × Bool
  | 0, _ => ([], true)
  | f + 1, x =>
    let rs := (soloKids img M i x).map (soloDFS img M i f)
    (x :: rs.flatMap Prod.fst, rs.any Prod.snd)

theorem soloKids_complete {img : Image} {M : List PMsg} {i : Nat} {x : LP × PState × GSet Nat} {l : PLabel}
    {ots : Option Nat} {p' : LP} {ws' : PState} {prom' : GSet Nat} (hp : litStep x.1 () l p' ())
    (hm : memStep img M i x.2.2 x.2.1 l ots ws' prom') : (p', ws', prom') ∈ soloKids img M i x := by
  unfold soloKids
  refine List.mem_flatMap.2 ⟨l, labCands_complete hp (memStep_reads hm),
    List.mem_filterMap.2 ⟨ots, tsOpts_complete hm, ?_⟩⟩
  have hp' : litNext x.1 l = some p' := hp
  rw [hp', memStepF_complete hm]

/-- THE SOLO DFS IS COMPLETE: with enough fuel, every solo run's final state is reached. -/
theorem soloDFS_complete {img : Image} {M : List PMsg} {i : Nat} :
    ∀ {x y : LP × PState × GSet Nat} {tr : List (PLabel × Option Nat)},
      soloSteps litStep img M i x tr y → ∀ f L, soloDFS img M i f x = (L, false) → y ∈ L := by
  intro x y tr h
  induction h with
  | refl x =>
    intro f L hd
    cases f with
    | zero => simp [soloDFS] at hd
    | succ f =>
      simp only [soloDFS, Prod.mk.injEq] at hd
      rw [← hd.1]; exact List.mem_cons_self ..
  | step x l ots p' ws' prom' tr y hp hm hrest ih =>
    intro f L hd
    cases f with
    | zero => simp [soloDFS] at hd
    | succ f =>
      simp only [soloDFS, Prod.mk.injEq] at hd
      obtain ⟨hL, hb⟩ := hd
      have hk := soloKids_complete hp hm
      have hr : soloDFS img M i f (p', ws', prom') ∈ (soloKids img M i x).map (soloDFS img M i f) :=
        List.mem_map.2 ⟨_, hk, rfl⟩
      have hb' : (soloDFS img M i f (p', ws', prom')).2 = false := by
        cases hh : (soloDFS img M i f (p', ws', prom')).2
        · rfl
        · have : ((soloKids img M i x).map (soloDFS img M i f)).any Prod.snd = true :=
            List.any_eq_true.2 ⟨_, hr, hh⟩
          rw [hb] at this; cases this
      have := ih f _ (Prod.ext rfl hb')
      rw [← hL]
      exact List.mem_cons_of_mem _ (List.mem_flatMap.2 ⟨_, hr, this⟩)

end Weak.Prom.Mach
