/-
Weak/Prom: **the free-run explorer and list utilities of the forbidden-outcome checker** (S0-P part (2),
milestone 2b).

* `freeDFS` — the DFS of a hart's FREE runs over a domain `D` (MachNota.lean `freeSteps`; read answers canonical,
  timestamp 0), recording each reachable state with the messages emitted so far; `freeDFS_complete`.
* `perms` (every permutation, `perms_complete`), `choicesG` (every choice of one element per list,
  `choicesG_complete`), `perm_owner` (a nodup list is a permutation of its parts by owner).
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Prom.MachNI

namespace Weak.Prom.Mach

open MachCSL MachCSL.Stdpp Iris.Std
open Weak (Image Dsrc)
open Weak.Prom Weak.Prom.Mach.Cert
open Weak.Prom.Ref (Instr Test two64 aluOp brEval amoOp sext byteList bytesVal)
open PLabel

/-! ## 1. Canonical read answers -/

def canonL : PLabel → PLabel
  | LLoad aq rl b tvs asrc => LLoad aq rl b (tvs.map (fun p => (0, p.2))) asrc
  | LExLoad aq rl b tvs asrc => LExLoad aq rl b (tvs.map (fun p => (0, p.2))) asrc
  | LRmw aq rl b tvs data asrc vsrc => LRmw aq rl b (tvs.map (fun p => (0, p.2))) data asrc vsrc
  | LAmoLd aq b tvs asrc => LAmoLd aq b (tvs.map (fun p => (0, p.2))) asrc
  | LIFetch b tvs => LIFetch b (tvs.map (fun p => (0, p.2)))
  | l => l

theorem canonL_msg (i : Nat) (l : PLabel) : labelMsg i (canonL l) = labelMsg i l := by
  cases l <;> rfl

theorem map_canon_snd (tvs : List (Nat × BitVec 8)) :
    (tvs.map (fun p => ((0 : Nat), p.2))).map Prod.snd = tvs.map Prod.snd := by
  simp [List.map_map, Function.comp_def]

theorem take1_canon_regWL (rd : Nat) (srcs : List Dsrc) : ∀ x ∈ (regWL rd srcs ++ [LInstr]).take 1, canonL x = x := by
  unfold regWL; split <;> simp [canonL]

theorem instrNext_canon {n : Nat} {s s1 : LP} {ins : Instr} {l : PLabel} (h : instrNext n s ins l = some s1) :
    instrNext n s ins (canonL l) = some s1 := by
  have hg : ∀ (r : List Nat) (p : Nat) (labs : List PLabel), go1 s r p labs l = some s1 →
      (∀ x ∈ labs.take 1, canonL x = x) → canonL l = l := fun r p labs hg hl => hl l (go1_mem hg)
  cases ins with
  | alui op rd rs1 imm => have h0 := h; simp only [instrNext] at h0; rw [hg _ _ _ h0 (take1_canon_regWL _ _)]; exact h
  | alu op rd rs1 rs2 => have h0 := h; simp only [instrNext] at h0; rw [hg _ _ _ h0 (take1_canon_regWL _ _)]; exact h
  | csrr rd v => have h0 := h; simp only [instrNext] at h0; rw [hg _ _ _ h0 (take1_canon_regWL _ _)]; exact h
  | fence f => have h0 := h; simp only [instrNext] at h0; rw [hg _ _ _ h0 (by simp [canonL])]; exact h
  | fenceTso => have h0 := h; simp only [instrNext] at h0; rw [hg _ _ _ h0 (by simp [canonL])]; exact h
  | fencei => have h0 := h; simp only [instrNext] at h0; rw [hg _ _ _ h0 (by simp [canonL])]; exact h
  | nop => have h0 := h; simp only [instrNext] at h0; rw [hg _ _ _ h0 (by simp [canonL])]; exact h
  | jmp tgt => rw [hg _ _ _ (ite_none_some h) (by simp [canonL])]; exact h
  | br c rs1 rs2 tgt => rw [hg _ _ _ (ite_none_some h) (by simp [canonL])]; exact h
  | loadAqPc => cases h
  | storeRlPc => cases h
  | store sz rs2 rs1 off =>
    cases l
    all_goals first | exact h | (simp only [instrNext] at h; split at h <;> simp at h)
  | storeRl sz aq0 rs2 rs1 =>
    cases l
    all_goals first | exact h | (simp only [instrNext] at h; split at h <;> simp at h)
  | sc sz aq0 rl0 rd rs2 rs1 =>
    cases l
    all_goals first | exact h | (simp only [instrNext] at h; split at h <;> simp at h)
  | load sz sgn rd rs1 off =>
    cases l
    case LLoad aq rl b tvs asrc =>
      simp only [canonL]; simp only [instrNext] at h ⊢; simp only [List.length_map, map_canon_snd]; exact h
    all_goals first | exact h | (simp only [instrNext] at h; split at h <;> simp at h)
  | loadAq sz rl0 rd rs1 =>
    cases l
    case LLoad aq rl b tvs asrc =>
      simp only [canonL]; simp only [instrNext] at h ⊢; simp only [List.length_map, map_canon_snd]; exact h
    all_goals first | exact h | (simp only [instrNext] at h; split at h <;> simp at h)
  | lr sz aq0 rl0 rd rs1 =>
    cases l
    case LExLoad aq rl b tvs asrc =>
      simp only [canonL]; simp only [instrNext] at h ⊢; simp only [List.length_map, map_canon_snd]; exact h
    all_goals first | exact h | (simp only [instrNext] at h; split at h <;> simp at h)
  | amo op sz aq0 rl0 rd rs2 rs1 =>
    cases l
    case LRmw aq rl b tvs data asrc vsrc =>
      simp only [canonL]; simp only [instrNext] at h ⊢; simp only [List.length_map, map_canon_snd]; exact h
    all_goals first | exact h | (simp only [instrNext] at h; split at h <;> simp at h)

/-! ## 2. The free DFS -/

/-- Every canonical run of `k` bytes from `a`, byte options `D`. -/
def domRunsD (D : Int → List (BitVec 8)) : Int → Nat → List (List (Nat × BitVec 8))
  | _, 0 => [[]]
  | a, k + 1 => (D a).flatMap (fun b => (domRunsD D (a + 1) k).map ((0, b) :: ·))

theorem domRunsD_complete {D : Int → List (BitVec 8)} :
    ∀ (a : Int) (tvs : List (Nat × BitVec 8)), bytesAll (fun a _ v => v ∈ D a) a tvs →
      tvs.map (fun p => ((0 : Nat), p.2)) ∈ domRunsD D a tvs.length
  | _, [], _ => List.mem_singleton.2 rfl
  | a, (t, v) :: r, ⟨h1, h2⟩ => by
    simp only [List.map_cons, List.length_cons, domRunsD]
    exact List.mem_flatMap.2 ⟨v, h1, List.mem_map.2 ⟨_, domRunsD_complete (a + 1) r h2, rfl⟩⟩

/-- The answers a free run may give at `a`: a domain byte, or its own latest byte there. -/
def optsAt (D : Int → List (BitVec 8)) (w : List PMsg) (a : Int) : List (BitVec 8) := D a ++ (lastByte w a).toList

/-- The labels a free run may take next. -/
def freeCands (D : Int → List (BitVec 8)) (w : List PMsg) (s : LP) : List PLabel :=
  match s.q with
  | l0 :: _ => [l0]
  | [] =>
    match s.prog[s.pc]? with
    | some ins => insLabs (domRunsD (optsAt D w)) s ins
    | none => []

theorem canon_reads {D : Int → List (BitVec 8)} {w : List PMsg} {l : PLabel} (hok : freeOk D w l) :
    ∀ base tvs, labelReads (canonL l) = some (base, tvs) → tvs ∈ domRunsD (optsAt D w) base tvs.length := by
  have hok' : ∀ base tvs, labelReads l = some (base, tvs) → bytesAll (fun a _ v => v ∈ optsAt D w a) base tvs :=
    fun base tvs h => bytesAll_mono (fun a _ v hv => by
      unfold optsAt
      rcases hv with hv | hv
      · exact List.mem_append_left _ hv
      · exact List.mem_append_right _ (by rw [hv]; simp)) base tvs (hok base tvs h)
  intro base tvs hr
  cases l <;> simp only [canonL, labelReads, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at hr
  all_goals first
    | (obtain ⟨rfl, rfl⟩ := hr
       rw [List.length_map]
       exact domRunsD_complete _ _ (hok' _ _ rfl))
    | (obtain ⟨rfl, rfl⟩ := hr
       exact absurd rfl (by simp))

theorem freeCands_complete {D : Int → List (BitVec 8)} {w : List PMsg} {s s1 : LP} {l : PLabel}
    (h : litNextF s l = some s1) (hok : freeOk D w l) :
    ∃ l' ∈ freeCands D w s, litNextF s l' = some s1 ∧ ∀ i, labelMsg i l' = labelMsg i l := by
  unfold litNextF at h
  cases hq : s.q with
  | cons l0 rest =>
    rw [hq] at h
    simp only at h
    split at h
    · rename_i he
      subst he
      refine ⟨l, by simp [freeCands, hq], ?_, fun _ => rfl⟩
      unfold litNextF; rw [hq]; simp only [if_true]; exact h
    · cases h
  | nil =>
    rw [hq] at h
    simp only at h
    cases hp : s.prog[s.pc]? with
    | none => rw [hp] at h; cases h
    | some ins =>
      rw [hp] at h
      simp only at h
      have hlit : ∀ l', insNextF s.prog.length s ins l' = some s1 → litNextF s l' = some s1 := by
        intro l' h'; unfold litNextF; rw [hq]; simp only; rw [hp]; exact h'
      cases ins with
      | sc sz aq0 rl0 rd rs2 rs1 =>
        refine ⟨l, ?_, hlit l h, fun _ => rfl⟩
        simp only [freeCands, hq, hp, insLabs]
        simp only [insNextF, scNextF] at h
        cases l <;> simp only [reduceCtorEq] at h
        · obtain ⟨⟨h1, h2, h3, h4, h5, h6⟩, _⟩ := ite_some_none h
          subst h1 h2 h3 h4 h5 h6
          simp
        · simp
      | _ =>
        simp only [insNextF] at h
        have hc := instrNext_canon h
        refine ⟨canonL l, ?_, hlit _ (by simp only [insNextF]; exact hc), fun i => canonL_msg i l⟩
        simp only [freeCands, hq, hp]
        exact insLabs_complete hc (canon_reads hok)

/-- The DFS of a hart's free runs: every reachable state with the messages emitted so far, and whether the fuel ran
out. -/
def freeDFS (D : Int → List (BitVec 8)) (i : Nat) : Nat → LP × List PMsg → List (LP × List PMsg) × Bool
  | 0, _ => ([], true)
  | f + 1, (s, w) =>
    let rs := ((freeCands D w s).filterMap (fun l => (litNextF s l).map (fun s1 => (s1, w ++ (labelMsg i l).toList)))).map
      (freeDFS D i f)
    ((s, w) :: rs.flatMap Prod.fst, rs.any Prod.snd)

/-- THE FREE DFS IS COMPLETE. -/
theorem freeDFS_complete {D : Int → List (BitVec 8)} {i : Nat} :
    ∀ {x y : LP × List PMsg} {ls : List PLabel}, freeSteps D i x ls y → ∀ f L, freeDFS D i f x = (L, false) →
      y ∈ L := by
  intro x y ls h
  induction h with
  | refl x =>
    intro f L hd
    obtain ⟨s, w⟩ := x
    cases f with
    | zero => simp [freeDFS] at hd
    | succ f =>
      simp only [freeDFS, Prod.mk.injEq] at hd
      rw [← hd.1]; exact List.mem_cons_self ..
  | step s w l s1 ls y hl hok hrest ih =>
    intro f L hd
    cases f with
    | zero => simp [freeDFS] at hd
    | succ f =>
      simp only [freeDFS, Prod.mk.injEq] at hd
      obtain ⟨hL, hb⟩ := hd
      obtain ⟨l', hl'mem, hl', hmsg⟩ := freeCands_complete hl hok
      have hk : (s1, w ++ (labelMsg i l').toList) ∈ (freeCands D w s).filterMap
          (fun l => (litNextF s l).map (fun s1 => (s1, w ++ (labelMsg i l).toList))) :=
        List.mem_filterMap.2 ⟨l', hl'mem, by rw [hl']; rfl⟩
      rw [hmsg] at hk
      have hr : freeDFS D i f (s1, w ++ (labelMsg i l).toList) ∈ ((freeCands D w s).filterMap
          (fun l => (litNextF s l).map (fun s1 => (s1, w ++ (labelMsg i l).toList)))).map (freeDFS D i f) :=
        List.mem_map.2 ⟨_, hk, rfl⟩
      have hb' : (freeDFS D i f (s1, w ++ (labelMsg i l).toList)).2 = false := by
        cases hh : (freeDFS D i f (s1, w ++ (labelMsg i l).toList)).2
        · rfl
        · have := List.any_eq_true.2 ⟨_, hr, hh⟩
          rw [hb] at this; cases this
      have := ih f _ (Prod.ext rfl hb')
      rw [← hL]
      exact List.mem_cons_of_mem _ (List.mem_flatMap.2 ⟨_, hr, this⟩)

/-! ## 3. Permutations and choices -/

/-- Every permutation of `l` (fuel `n ≥ |l|`). -/
def perms {α : Type} [DecidableEq α] : Nat → List α → List (List α)
  | 0, l => if l.isEmpty then [[]] else []
  | n + 1, l => if l.isEmpty then [[]] else l.eraseDups.flatMap (fun x => (perms n (l.erase x)).map (x :: ·))

theorem perms_complete {α : Type} [DecidableEq α] :
    ∀ (l' : List α) (n : Nat) (l : List α), List.Perm l' l → l.length ≤ n → l' ∈ perms n l := by
  intro l'
  induction l' with
  | nil =>
    intro n l hp _
    have := hp.nil_eq
    subst this
    cases n <;> simp [perms]
  | cons x r ih =>
    intro n l hp hn
    have hx : x ∈ l := hp.mem_iff.1 (List.mem_cons_self ..)
    have hr : List.Perm r (l.erase x) := (hp.trans (List.perm_cons_erase hx)).cons_inv
    have hne : l.isEmpty = false := by
      cases l with
      | nil => cases hx
      | cons _ _ => rfl
    have hlen := List.length_erase_of_mem hx
    cases n with
    | zero => cases l with
      | nil => cases hx
      | cons _ _ => simp at hn
    | succ n =>
      simp only [perms, hne, Bool.false_eq_true, if_false]
      refine List.mem_flatMap.2 ⟨x, List.mem_eraseDups.2 hx, List.mem_map.2 ⟨r, ih n _ hr (by omega), rfl⟩⟩

/-- Every choice of one element of each list. -/
def choicesG {α : Type} : List (List α) → List (List α)
  | [] => [[]]
  | s :: rest => s.flatMap (fun x => (choicesG rest).map (x :: ·))

theorem choicesG_complete {α : Type} : ∀ (ss : List (List α)) (xs : List α), xs.length = ss.length →
    (∀ (k : Nat) (x : α) (s : List α), xs[k]? = some x → ss[k]? = some s → x ∈ s) → xs ∈ choicesG ss
  | [], [], _, _ => List.mem_singleton.2 rfl
  | [], _ :: _, h, _ => by cases h
  | _ :: _, [], h, _ => by cases h
  | s :: rest, x :: xs, hl, hm => by
    simp only [choicesG]
    refine List.mem_flatMap.2 ⟨x, hm 0 x s rfl rfl, List.mem_map.2 ⟨xs, ?_, rfl⟩⟩
    exact choicesG_complete rest xs (by simpa using hl) (fun k y t h1 h2 => hm (k + 1) y t h1 h2)

theorem sum_range_ind (P : Prop) [Decidable P] (o : Nat) :
    ∀ n, ((List.range n).map (fun h => if P ∧ o = h then 1 else 0)).sum = if P ∧ o < n then 1 else 0
  | 0 => by simp
  | n + 1 => by
    rw [List.range_succ, List.map_append, List.sum_append_nat, sum_range_ind P o n]
    by_cases hP : P <;> by_cases h1 : o < n <;> by_cases h2 : o = n <;> simp [hP, h1, h2] <;> omega

/-- A nodup list is a permutation of the concatenation of its parts by owner. -/
theorem perm_owner (J : List Nat) (hJ : J.Nodup) (n : Nat) (F : Nat → List Nat) (owner : Nat → Nat)
    (hF : ∀ h, h < n → (F h).Nodup) (hin : ∀ h, h < n → ∀ t, t ∈ F h → t ∈ J ∧ owner t = h)
    (hcov : ∀ t ∈ J, owner t < n ∧ t ∈ F (owner t)) :
    J.Perm ((List.range n).map F).flatten := by
  rw [List.perm_iff_count]
  intro t
  rw [List.count_flatten, List.map_map, hJ.count]
  have e : ∀ h, h ∈ List.range n → (List.count t ∘ F) h = if t ∈ J ∧ owner t = h then 1 else 0 := by
    intro h hh
    have hh' := List.mem_range.1 hh
    simp only [Function.comp, (hF h hh').count]
    by_cases hm : t ∈ F h
    · rw [if_pos hm, if_pos (hin h hh' t hm)]
    · rw [if_neg hm, if_neg]
      rintro ⟨h1, h2⟩
      exact hm (h2 ▸ (hcov t h1).2)
  rw [List.map_congr_left e, sum_range_ind]
  by_cases h1 : t ∈ J
  · rw [if_pos h1, if_pos ⟨h1, (hcov t h1).1⟩]
  · rw [if_neg h1, if_neg (fun h => h1 h.1)]

end Weak.Prom.Mach
