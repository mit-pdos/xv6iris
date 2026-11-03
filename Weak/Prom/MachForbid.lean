/-
Weak/Prom: **the machine-v2 FORBIDDEN-outcome checker and its soundness** (S0-P part (2), milestone 2b).

  `forbidMachB_sound : forbidMachB T K = true → ¬ allowedMach T`     (closed value domain)
  `forbidChainB_sound : forbidChainB T = true → ¬ allowedMach T`      (domain chain, any test)

`allowedMach T` (MachCert.lean) is "machine v2 has a valid run of `T` (program half `litStep`) in which every hart
finishes and the condition holds".  The checker:
1. `forbidMachB`: computes a value domain `D` (an untrusted iteration, `domIter`), and checks that `D` is CLOSED:
   the free-run DFS of every hart (`freeDFS`, complete) runs out of no fuel and every message it emits has its bytes
   in `D`.  `forbidChainB` (for domains with no finite closure, e.g. counters): `D_0` = the image, `D_{j+1}` = `D_j`
   plus every byte of every free run over `D_j` (fuel checked at every level), up to `N` = the total program length
   (`valid_msgs_le`: a valid run has at most `N` messages; NOTA in depth form puts the byte at timestamp `t` in
   `D_t`);
2. for every choice of one complete free-run message list per hart and every permutation `M` of their
   concatenation, runs every hart's solo DFS against `M` (`soloDFS`, complete; fuel checked) and checks that no
   combination of final states (all done, no promise left) satisfies the condition.
Soundness: a valid run factors promises-first (MachFactor.lean) and separates into solo runs (MachSolo.lean); NOTA
(MachNI.lean, `nota` / `nota_depth`) puts every byte of the final memory in `D` (resp. `D_N`), so each solo run is a complete free run and its fulfilled
messages are one of the enumerated lists; the final memory is a permutation of their concatenation (every message
is fulfilled exactly once, by its author); each hart's final state is found by the solo DFS.
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Prom.MachFree

namespace Weak.Prom.Mach

open MachCSL MachCSL.Stdpp Iris.Std
open Weak (Image Dsrc)
open Weak.Prom Weak.Prom.Mach.Cert
open Weak.Prom.Ref (Instr Test two64 aluOp brEval amoOp sext byteList bytesVal)
open PLabel

/-! ## 1. The checker -/

/-- A domain: extra bytes per address (the image byte is always in). -/
abbrev DomL := List (Int × BitVec 8)

def domF (img : Image) (d : DomL) (a : Int) : List (BitVec 8) :=
  ((img a).toList ++ d.filterMap (fun p => if p.1 = a then some p.2 else none)).eraseDups

def msgBytes (m : PMsg) : DomL :=
  (List.range m.data.length).filterMap (fun (k : Nat) => (m.data[k]?).map (fun b => (m.pa + (k : Int), b)))

def msgInB (D : Int → List (BitVec 8)) (m : PMsg) : Bool :=
  (List.range m.data.length).all (fun (k : Nat) =>
    match m.data[k]? with
    | some b => decide (b ∈ D (m.pa + (k : Int)))
    | none => true)

def lpOf (T : Test) (h : Nat) : LP := ((progs T)[h]?).getD ⟨[], 0, [], []⟩

def fuelOf (T : Test) (h : Nat) : Nat := 5 * (T.prog h).length + 2

def freeAll (T : Test) (D : Int → List (BitVec 8)) : List (List (LP × List PMsg) × Bool) :=
  (List.range T.harts.length).map (fun h => freeDFS D h (fuelOf T h) (lpOf T h, []))

/-- One step of the (untrusted) domain iteration. -/
def domStep (T : Test) (d : DomL) : DomL :=
  (d ++ ((freeAll T (domF (testImg T) d)).flatMap (fun r => r.1.flatMap (fun st => st.2.flatMap msgBytes)))).eraseDups

def domIter (T : Test) : Nat → DomL → DomL
  | 0, d => d
  | k + 1, d =>
    let d' := domStep T d
    if d'.length = d.length then d else domIter T k d'

def domT (T : Test) (K : Nat) : Int → List (BitVec 8) := domF (testImg T) (domIter T K [])

def doneLP (s : LP) : Bool := s.pc == s.prog.length && s.q.isEmpty

/-- Closedness and fuel of the free DFSs. -/
def freeOkB (D : Int → List (BitVec 8)) (fr : List (List (LP × List PMsg) × Bool)) : Bool :=
  fr.all (fun r => !r.2 && r.1.all (fun st => st.2.all (msgInB D)))

/-- Per hart, the message lists of its complete free runs. -/
def candW (fr : List (List (LP × List PMsg) × Bool)) : List (List (List PMsg)) :=
  fr.map (fun r => ((r.1.filter (fun st => doneLP st.1)).map Prod.snd).eraseDups)

def regOfL (fs : List (LP × PState × GSet Nat)) (h r : Nat) : Nat :=
  match fs[h]? with
  | some x => x.1.rd r
  | none => 0

def soloAll (T : Test) (M : List PMsg) : List (List (LP × PState × GSet Nat) × Bool) :=
  (List.range T.harts.length).map (fun h => soloDFS (testImg T) M h (fuelOf T h) (lpOf T h, psInit, promsOf M h))

/-- No combination of final states against `M` satisfies the condition (and no solo DFS ran out of fuel). -/
def noOutcomeB (T : Test) (M : List PMsg) : Bool :=
  (soloAll T M).all (fun r => !r.2) &&
  (choicesG ((soloAll T M).map (fun r => r.1.filter (fun x => doneLP x.1 && promDone M x.2.2)))).all
    (fun fs => !T.cond.eval (regOfL fs) (fun x => finalMem (testImg T) M x 1))

/-- The candidate check against a domain `D` holding every byte of the final memory: every free DFS over `D`
finished, and no candidate final memory has a combination of finished final states satisfying the condition. -/
def candOkB (T : Test) (D : Int → List (BitVec 8)) : Bool :=
  (freeAll T D).all (fun r => !r.2) &&
  (choicesG (candW (freeAll T D))).all (fun W => (perms W.flatten.length W.flatten).all (noOutcomeB T))

/-- THE CHECKER (closed domain): machine v2 has no valid run of `T` in which every hart finishes and the condition
holds. -/
def forbidMachB (T : Test) (K : Nat) : Bool :=
  freeOkB (domT T K) (freeAll T (domT T K)) && candOkB T (domT T K)

/-- The program length bound on the number of messages. -/
def progSum (T : Test) : Nat := ((List.range T.harts.length).map (fun h => (T.prog h).length)).sum

/-- The domain chain `D_0 = image`, `D_{j+1}` = `D_j` plus every byte of every free run over `D_j`. -/
def iterD (T : Test) : Nat → DomL → DomL
  | 0, d => d
  | k + 1, d => iterD T k (domStep T d)

/-- Every free DFS along the chain finished. -/
def chainB (T : Test) : Nat → DomL → Bool
  | 0, _ => true
  | k + 1, d => (freeAll T (domF (testImg T) d)).all (fun r => !r.2) && chainB T k (domStep T d)

/-- THE CHECKER (domain chain, for value domains with no finite closure such as counters): the candidate check
against `D_N`, `N` = the total program length (a bound on the number of messages, hence on every value chain). -/
def forbidChainB (T : Test) : Bool :=
  chainB T (progSum T) [] && candOkB T (domF (testImg T) (iterD T (progSum T) []))

/-! ## 2. Small facts -/

theorem domF_img {img : Image} {d : DomL} {a : Int} {b : BitVec 8} (h : img a = some b) : b ∈ domF img d a := by
  unfold domF; rw [List.mem_eraseDups, h]; simp

theorem domF_ne {img : Image} {d : DomL} (h : ∀ a, ∃ b, img a = some b) (a : Int) : domF img d a ≠ [] := by
  obtain ⟨b, hb⟩ := h a
  intro he
  have := domF_img (d := d) hb
  rw [he] at this; cases this

theorem msgInB_sound {D : Int → List (BitVec 8)} {m : PMsg} (h : msgInB D m = true) : msgIn D m := by
  intro k b hb
  have hk : k < m.data.length := (List.getElem?_eq_some_iff.1 hb).1
  have := List.all_eq_true.1 h k (List.mem_range.2 hk)
  rw [hb] at this
  exact of_decide_eq_true this

theorem testImg_some (T : Test) (a : Int) : ∃ b, testImg T a = some b := ⟨_, rfl⟩

theorem progs_len (T : Test) : (progs T).length = T.harts.length := by simp [progs]

theorem progs_get {T : Test} {h : Nat} (hh : h < T.harts.length) : (progs T)[h]? = some (lpOf T h) := by
  unfold lpOf
  have : h < (progs T).length := by rw [progs_len]; exact hh
  rw [List.getElem?_eq_getElem this]; rfl

theorem progs_get_inv {T : Test} {h : Nat} {p : LP} (hp : (progs T)[h]? = some p) :
    h < T.harts.length ∧ p = lpOf T h := by
  have hh : h < (progs T).length := (List.getElem?_eq_some_iff.1 hp).1
  rw [progs_len] at hh
  refine ⟨hh, ?_⟩
  rw [progs_get hh] at hp; cases hp; rfl

theorem lpOf_q (T : Test) {h : Nat} (hh : h < T.harts.length) : (lpOf T h).q = [] := by
  unfold lpOf progs
  simp [hh]

theorem foldl_spec (M : List PMsg) (i t : Nat) (f : GSet Nat → Nat → GSet Nat)
    (hf : ∀ acc k, t ∈ f acc k ↔ t ∈ acc ∨ (t = k + 1 ∧ ∃ m, M[k]? = some m ∧ m.tid = some i)) :
    ∀ (ks : List Nat) (acc : GSet Nat),
      t ∈ ks.foldl f acc ↔ t ∈ acc ∨ ∃ k ∈ ks, t = k + 1 ∧ ∃ m, M[k]? = some m ∧ m.tid = some i
  | [], acc => by simp
  | k :: ks, acc => by
    rw [List.foldl_cons, foldl_spec M i t f hf ks, hf]
    constructor
    · rintro ((h | h) | ⟨k', hk', h1⟩)
      · exact .inl h
      · exact .inr ⟨k, List.mem_cons_self .., h⟩
      · exact .inr ⟨k', List.mem_cons_of_mem _ hk', h1⟩
    · rintro (h | ⟨k', hk', h1⟩)
      · exact .inl (.inl h)
      · rcases List.mem_cons.1 hk' with e | e
        · subst e; exact .inl (.inr h1)
        · exact .inr ⟨k', e, h1⟩

theorem promsOf_mem (M : List PMsg) (i t : Nat) : t ∈ promsOf M i ↔ 0 < t ∧ ownTs M i t := by
  unfold promsOf
  rw [foldl_spec M i t _ (fun acc k => by
    split
    · rename_i m hm
      by_cases ht : m.tid = some i
      · simp only [ht, beq_self_eq_true, if_true, elemOfUnion, elemOfSingleton]
        constructor
        · rintro (h | h)
          · exact .inr ⟨h, m, hm, ht⟩
          · exact .inl h
        · rintro (h | ⟨h, m', hm', ht'⟩)
          · exact .inr h
          · exact .inl h
      · have hb : (m.tid == some i) = false := by simp [ht]
        simp only [hb, Bool.false_eq_true, if_false]
        constructor
        · exact .inl
        · rintro (h | ⟨_, m', hm', ht'⟩)
          · exact h
          · rw [hm] at hm'; cases hm'; exact absurd ht' ht
    · rename_i hm
      constructor
      · exact .inl
      · rintro (h | ⟨_, m', hm', _⟩)
        · exact h
        · rw [hm] at hm'; cases hm')]
  constructor
  · rintro (h | ⟨k, _, rfl, m, hm, ht⟩)
    · exact absurd h notElemOfEmpty
    · exact ⟨by omega, m, by simpa using hm, ht⟩
  · rintro ⟨h0, m, hm, ht⟩
    refine .inr ⟨t - 1, List.mem_range.2 (List.getElem?_eq_some_iff.1 hm).1, by omega, m, hm, ht⟩

theorem promDone_empty (M : List PMsg) : promDone M ∅ = true := by
  unfold promDone
  refine List.all_eq_true.2 (fun t _ => ?_)
  simp only [Bool.not_eq_true']
  cases h : promHas ∅ t
  · rfl
  · exact absurd ((promHas_iff _ _).1 h) notElemOfEmpty

theorem range'_filterMap (L : List PMsg) : ∀ (k : Nat) (M : List PMsg), L.drop k = M →
    (List.range' (k + 1) M.length).filterMap (fun t => L[t - 1]?) = M
  | _, [], _ => rfl
  | k, m :: M', h => by
    have h0 : L[k]? = some m := by
      have := congrArg (fun l => l[0]?) h
      simp only [List.getElem?_drop, Nat.add_zero] at this
      simpa using this
    have h1 : L.drop (k + 1) = M' := by
      have := congrArg (List.drop 1) h
      simpa [List.drop_drop, Nat.add_comm] using this
    simp only [List.length_cons, List.range'_succ, List.filterMap_cons, Nat.add_sub_cancel, h0]
    rw [range'_filterMap L (k + 1) M' h1]

/-! ## 3. Solo runs: free runs, messages, fulfilments -/

theorem solo_free {img : Image} {M : List PMsg} {D : Int → List (BitVec 8)} {h : Nat}
    (hD : ∀ t a b, memByte img M t a = some b → b ∈ D a) :
    ∀ {x y : LP × PState × GSet Nat} {tr : List (PLabel × Option Nat)},
      soloSteps litStep img M h x tr y → ∀ w,
        freeSteps D h (x.1, w) (tr.map Prod.fst) (y.1, w ++ (tr.map Prod.fst).filterMap (labelMsg h)) := by
  intro x y tr hs
  induction hs with
  | refl => intro w; simp only [List.map_nil, List.filterMap_nil, List.append_nil]; exact .refl _
  | step x l ots p' ws' prom' tr y hp hm _ ih =>
    intro w
    have hr := ih (w ++ (labelMsg h l).toList)
    refine .step _ _ _ _ _ _ (litNextF_of hp) (fun base tvs hr' => ?_) ?_
    · exact bytesAll_mono (fun a t v hb => .inl (hD t a v hb)) _ _ (memStep_reads hm base tvs hr')
    · have e : (w ++ (labelMsg h l).toList) ++ (tr.map Prod.fst).filterMap (labelMsg h) =
          w ++ (((l, ots) :: tr).map Prod.fst).filterMap (labelMsg h) := by
        simp only [List.map_cons, List.filterMap_cons]; cases labelMsg h l <;> simp
      rw [← e]; exact hr

theorem solo_msgs {img : Image} {M : List PMsg} {h : Nat} :
    ∀ {x y : LP × PState × GSet Nat} {tr : List (PLabel × Option Nat)},
      soloSteps litStep img M h x tr y →
        (tr.map Prod.fst).filterMap (labelMsg h) = (tr.filterMap Prod.snd).filterMap (fun ts => M[ts - 1]?) := by
  intro x y tr hs
  induction hs with
  | refl => rfl
  | step x l ots p' ws' prom' tr y hp hm _ ih =>
    obtain ⟨h1, h2⟩ := memStep_msg hm
    cases ots with
    | none =>
      simp only [List.map_cons, List.filterMap_cons, h2 rfl]
      exact ih
    | some ts =>
      have e := h1 ts rfl
      simp only [List.map_cons, List.filterMap_cons]
      rw [← e]
      cases M[ts - 1]? <;> simp [ih]

theorem solo_fulfils {P : Type} {pstep : P → Unit → PLabel → P → Unit → Prop} {img : Image} {M : List PMsg}
    {h : Nat} : ∀ {x y : P × PState × GSet Nat} {tr : List (PLabel × Option Nat)},
      soloSteps pstep img M h x tr y →
        (tr.filterMap Prod.snd).Nodup ∧ ∀ t, t ∈ x.2.2 ↔ t ∈ y.2.2 ∨ t ∈ tr.filterMap Prod.snd := by
  intro x y tr hs
  induction hs with
  | refl x => exact ⟨List.nodup_nil, fun t => by simp⟩
  | step x l ots p' ws' prom' tr y hp hm _ ih =>
    obtain ⟨hnd, hiff⟩ := ih
    rcases memStep_prom hm with ⟨rfl, he⟩ | ⟨ts, rfl, hts, he⟩
    · subst he
      simp only [List.filterMap_cons]
      exact ⟨hnd, hiff⟩
    · subst he
      simp only [List.filterMap_cons]
      have hnot : ts ∉ tr.filterMap Prod.snd := by
        intro hin
        have := (hiff ts).2 (.inr hin)
        exact (elemOfDifference.1 this).2 (elemOfSingleton.2 rfl)
      refine ⟨List.nodup_cons.2 ⟨hnot, hnd⟩, fun t => ?_⟩
      constructor
      · intro ht
        by_cases e : t = ts
        · exact .inr (List.mem_cons.2 (.inl e))
        · rcases (hiff t).1 (elemOfDifference.2 ⟨ht, by rw [elemOfSingleton]; exact e⟩) with h1 | h1
          · exact .inl h1
          · exact .inr (List.mem_cons_of_mem _ h1)
      · rintro (h1 | h1)
        · exact (elemOfDifference.1 ((hiff t).2 (.inl h1))).1
        · rcases List.mem_cons.1 h1 with e | e
          · subst e; exact hts
          · exact (elemOfDifference.1 ((hiff t).2 (.inr e))).1

/-! ## 4. Soundness -/

theorem freeOkB_closed {T : Test} {D : Int → List (BitVec 8)} (hD : freeOkB D (freeAll T D) = true) {h : Nat}
    (hh : h < T.harts.length) :
    closedFrom D h (lpOf T h) ∧ (freeDFS D h (fuelOf T h) (lpOf T h, [])).2 = false := by
  have hmem : freeDFS D h (fuelOf T h) (lpOf T h, []) ∈ freeAll T D := List.mem_map.2 ⟨h, List.mem_range.2 hh, rfl⟩
  have := List.all_eq_true.1 hD _ hmem
  simp only [Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true] at this
  obtain ⟨hf, hall⟩ := this
  refine ⟨fun ls y hfs m hm => ?_, hf⟩
  have hin := freeDFS_complete hfs (fuelOf T h) _ (Prod.ext rfl hf)
  exact msgInB_sound (hall _ hin m hm)

theorem freeAll_flag {T : Test} {D : Int → List (BitVec 8)} (hD : (freeAll T D).all (fun r => !r.2) = true)
    {h : Nat} (hh : h < T.harts.length) : (freeDFS D h (fuelOf T h) (lpOf T h, [])).2 = false := by
  have := List.all_eq_true.1 hD _ (List.mem_map.2 ⟨h, List.mem_range.2 hh, rfl⟩)
  simpa using this

/-! ## 5. Facts of valid runs -/

theorem valid_len {T : Test} {evs : List PEvt} {cfg : PCfg LP Unit}
    (hv : validRun litStep (testImg T) () (progs T) evs cfg) : cfg.pcAgs.length = T.harts.length := by
  rw [pmSteps_len hv.1]; simp [pmInit, progs_len]

theorem valid_solo {T : Test} {evs : List PEvt} {cfg : PCfg LP Unit}
    (hv : validRun litStep (testImg T) () (progs T) evs cfg) :
    ∀ h, h < T.harts.length → ∃ ag, cfg.pcAgs[h]? = some ag ∧ ag.paProm = ∅ ∧
      soloSteps litStep (testImg T) cfg.pcLog h (lpOf T h, psInit, promsOf cfg.pcLog h) (traceOf h evs)
        (ag.paSt, ag.paWs, ag.paProm) := by
  intro h hh
  obtain ⟨ag, hag, P0, hP0, hrun⟩ := validRun_solo hv h (lpOf T h) (progs_get hh)
  have he : P0 = promsOf cfg.pcLog h := Std.ExtTreeSet.ext_mem (fun t => by rw [hP0, promsOf_mem])
  subst he
  exact ⟨ag, hag, hv.2 h ag hag, hrun⟩

/-- The fulfilled messages of hart `h`, in program order. -/
def fulMsgs (evs : List PEvt) (h : Nat) : List PMsg := ((traceOf h evs).map Prod.fst).filterMap (labelMsg h)

/-- THE FINAL MEMORY IS A PERMUTATION of the concatenation of the harts' fulfilled messages (statement 6). -/
theorem valid_perm {T : Test} {evs : List PEvt} {cfg : PCfg LP Unit}
    (hv : validRun litStep (testImg T) () (progs T) evs cfg) :
    List.Perm cfg.pcLog ((List.range T.harts.length).map (fulMsgs evs)).flatten := by
  have hn := valid_len hv
  have hwf := pmSteps_wf hv.1 (pmInit_wf _ _ _)
  have hsolo := valid_solo hv
  have hJ := perm_owner (List.range' 1 cfg.pcLog.length) List.nodup_range' T.harts.length
    (fun h => (traceOf h evs).filterMap Prod.snd) (fun t => ((cfg.pcLog[t - 1]?).bind PMsg.tid).getD 0)
    (fun h hh => by obtain ⟨ag, _, _, hrun⟩ := hsolo h hh; exact (solo_fulfils hrun).1)
    (fun h hh t ht => by
      obtain ⟨ag, _, hp0, hrun⟩ := hsolo h hh
      have := ((solo_fulfils hrun).2 t).2 (.inr ht)
      obtain ⟨h0, m, hm, htid⟩ := (promsOf_mem _ _ _).1 this
      have hlt := (List.getElem?_eq_some_iff.1 hm).1
      refine ⟨List.mem_range'_1.2 ⟨by omega, by omega⟩, ?_⟩
      simp [hm, htid])
    (fun t ht => by
      have ht' := List.mem_range'_1.1 ht
      have hlt : t - 1 < cfg.pcLog.length := by omega
      have hm : cfg.pcLog[t - 1]? = some cfg.pcLog[t - 1] := List.getElem?_eq_getElem hlt
      obtain ⟨_, o, htid, ho⟩ := hwf.2 _ (List.getElem_mem hlt)
      have hown : ((cfg.pcLog[t - 1]?).bind PMsg.tid).getD 0 = o := by simp [hm, htid]
      rw [hown]
      refine ⟨by rw [← hn]; exact ho, ?_⟩
      obtain ⟨ag, _, hp0, hrun⟩ := hsolo o (by rw [← hn]; exact ho)
      have := ((solo_fulfils hrun).2 t).1 ((promsOf_mem _ _ _).2 ⟨by omega, _, hm, htid⟩)
      rcases this with h1 | h1
      · simp only at h1; rw [hp0] at h1; exact absurd h1 notElemOfEmpty
      · exact h1)
  have hJ' := hJ.filterMap (fun t => cfg.pcLog[t - 1]?)
  rw [range'_filterMap cfg.pcLog 0 cfg.pcLog (List.drop_zero), List.filterMap_flatten, List.map_map] at hJ'
  have e : List.map (List.filterMap (fun t => cfg.pcLog[t - 1]?) ∘ fun h => (traceOf h evs).filterMap Prod.snd)
      (List.range T.harts.length) = (List.range T.harts.length).map (fulMsgs evs) := by
    refine List.map_congr_left (fun h hh => ?_)
    obtain ⟨ag, _, _, hrun⟩ := hsolo h (List.mem_range.1 hh)
    simp only [Function.comp, fulMsgs]
    exact (solo_msgs hrun).symm
  rw [e] at hJ'
  exact hJ'

/-! ## 6. Soundness -/

/-- THE CANDIDATE CHECK IS SOUND, given a domain that holds every byte of the final memory. -/
theorem candOk_sound {T : Test} {D : Int → List (BitVec 8)} (hc : candOkB T D = true) {evs : List PEvt}
    {cfg : PCfg LP Unit} (hv : validRun litStep (testImg T) () (progs T) evs cfg) (hdone : allDone cfg)
    (hbytes : ∀ t a b, memByte (testImg T) cfg.pcLog t a = some b → b ∈ D a) :
    T.cond.eval (regOf cfg) (memOf T cfg) = false := by
  unfold candOkB at hc
  rw [Bool.and_eq_true] at hc
  obtain ⟨hflags, hall⟩ := hc
  have hn := valid_len hv
  have hsolo := valid_solo hv
  let Ws : List (List PMsg) := (List.range T.harts.length).map (fulMsgs evs)
  have hWs : Ws ∈ choicesG (candW (freeAll T D)) := by
    refine choicesG_complete _ _ (by simp [Ws, candW, freeAll]) (fun k x s hx hs => ?_)
    simp only [Ws, List.getElem?_map, Option.map_eq_some_iff] at hx
    obtain ⟨k', hk', rfl⟩ := hx
    have hk : k < T.harts.length := by
      rcases Nat.lt_or_ge k T.harts.length with h1 | h1
      · exact h1
      · rw [List.getElem?_eq_none (by simp; omega)] at hk'; cases hk'
    rw [List.getElem?_range hk] at hk'
    cases hk'
    simp only [candW, freeAll, List.getElem?_map, List.getElem?_range hk, Option.map_some,
      Option.some.injEq] at hs
    subst hs
    obtain ⟨ag, hag, _, hrun⟩ := hsolo k hk
    have hfs := solo_free hbytes hrun []
    have hc := freeDFS_complete hfs (fuelOf T k) _ (Prod.ext rfl (freeAll_flag hflags hk))
    have hd := hdone k ag hag
    rw [List.mem_eraseDups]
    refine List.mem_map.2 ⟨(ag.paSt, fulMsgs evs k), List.mem_filter.2 ⟨?_, ?_⟩, rfl⟩
    · rw [List.nil_append] at hc; exact hc
    · simp [doneLP, hd.1, hd.2]
  have hM : cfg.pcLog ∈ perms Ws.flatten.length Ws.flatten :=
    perms_complete _ _ _ (valid_perm hv) (Nat.le_refl _)
  have hno : noOutcomeB T cfg.pcLog = true := List.all_eq_true.1 (List.all_eq_true.1 hall Ws hWs) _ hM
  unfold noOutcomeB at hno
  rw [Bool.and_eq_true] at hno
  obtain ⟨hfuel, hout⟩ := hno
  let fs : List (LP × PState × GSet Nat) := cfg.pcAgs.map (fun ag => (ag.paSt, ag.paWs, ag.paProm))
  have hfs : fs ∈ choicesG ((soloAll T cfg.pcLog).map
      (fun r => r.1.filter (fun x => doneLP x.1 && promDone cfg.pcLog x.2.2))) := by
    refine choicesG_complete _ _ (by simp [fs, soloAll, hn]) (fun k x s hx hs => ?_)
    simp only [fs, List.getElem?_map, Option.map_eq_some_iff] at hx
    obtain ⟨ag, hag, rfl⟩ := hx
    have hk : k < T.harts.length := by rw [← hn]; exact (List.getElem?_eq_some_iff.1 hag).1
    simp only [soloAll, List.getElem?_map, List.getElem?_range hk, Option.map_some, Option.some.injEq] at hs
    subst hs
    obtain ⟨ag', hag', hp0, hrun⟩ := hsolo k hk
    rw [hag] at hag'; cases hag'
    have hf : (soloDFS (testImg T) cfg.pcLog k (fuelOf T k) (lpOf T k, psInit, promsOf cfg.pcLog k)).2 = false := by
      have := List.all_eq_true.1 hfuel _ (List.mem_map.2 ⟨k, List.mem_range.2 hk, rfl⟩)
      simpa using this
    have hc := soloDFS_complete hrun _ _ (Prod.ext rfl hf)
    have hd := hdone k ag hag
    refine List.mem_filter.2 ⟨hc, ?_⟩
    simp [doneLP, hd.1, hd.2, hp0, promDone_empty]
  have hc := List.all_eq_true.1 hout fs hfs
  have hreg : regOfL fs = regOf cfg := by
    funext h r
    simp only [regOfL, regOf, fs, List.getElem?_map]
    cases cfg.pcAgs[h]? <;> rfl
  rw [hreg] at hc
  have hmem : (fun x => finalMem (testImg T) cfg.pcLog x 1) = memOf T cfg := rfl
  rw [hmem] at hc
  simpa using hc

/-- The hypotheses of NOTA for a valid run. -/
theorem valid_nota_hyps {T : Test} {evs : List PEvt} {cfg : PCfg LP Unit}
    (hv : validRun litStep (testImg T) () (progs T) evs cfg) :
    (∀ (h : Nat) (p : LP), (progs T)[h]? = some p → qOk p.q) ∧
    (∀ (k : Nat) (m : PMsg), cfg.pcLog[k]? = some m → ∃ (h : Nat) (p : LP), m.tid = some h ∧ (progs T)[h]? = some p) ∧
    (∀ (h : Nat) (p : LP), (progs T)[h]? = some p → ∃ (P0 : GSet Nat) (y : LP × PState × GSet Nat)
      (tr : List (PLabel × Option Nat)), (∀ t, t ∈ P0 ↔ 0 < t ∧ ownTs cfg.pcLog h t) ∧
      soloSteps litStep (testImg T) cfg.pcLog h (p, psInit, P0) tr y ∧ ∀ t, t ∉ y.2.2) := by
  have hn := valid_len hv
  have hwf := pmSteps_wf hv.1 (pmInit_wf _ _ _)
  refine ⟨fun h p hp => ?_, fun k m hk => ?_, fun h p hp => ?_⟩
  · obtain ⟨hh, rfl⟩ := progs_get_inv hp
    rw [lpOf_q T hh]; exact qOk_nil
  · obtain ⟨_, h, htid, hlt⟩ := hwf.2 m (List.mem_of_getElem? hk)
    exact ⟨h, lpOf T h, htid, progs_get (by rw [← hn]; exact hlt)⟩
  · obtain ⟨hh, rfl⟩ := progs_get_inv hp
    obtain ⟨ag, _, hp0, hrun⟩ := valid_solo hv h hh
    exact ⟨_, _, _, promsOf_mem _ _, hrun, fun t => by simp only; rw [hp0]; exact notElemOfEmpty⟩

/-- **THE FORBIDDEN-OUTCOME CHECKER IS SOUND** for machine v2 (closed-domain form). -/
theorem forbidMachB_sound (T : Test) (K : Nat) (hB : forbidMachB T K = true) : ¬ allowedMach T := by
  rintro ⟨evs, cfg, hv, hdone, hcond⟩
  unfold forbidMachB at hB
  rw [Bool.and_eq_true] at hB
  obtain ⟨hfree, hcand⟩ := hB
  obtain ⟨hq, hown, hruns⟩ := valid_nota_hyps hv
  have hbytes : ∀ t a b, memByte (testImg T) cfg.pcLog t a = some b → b ∈ domT T K a :=
    nota (ps := progs T) (domF_ne (testImg_some T)) (fun a b h => domF_img h)
      (fun h p hp => by obtain ⟨hh, rfl⟩ := progs_get_inv hp; exact (freeOkB_closed hfree hh).1) hq hown hruns
  rw [candOk_sound hcand hv hdone hbytes] at hcond
  cases hcond

/-! ## 7. The domain-chain checker -/

theorem instrNext_pc {n : Nat} {s s' : LP} {ins : Instr} {l : PLabel} (hn : s.pc < n)
    (h : instrNext n s ins l = some s') : s'.prog = s.prog ∧ s.pc < s'.pc ∧ s'.pc ≤ n := by
  cases ins with
  | alui => simp only [instrNext] at h; obtain ⟨_, _, rfl⟩ := go1_eq h; simp; omega
  | alu => simp only [instrNext] at h; obtain ⟨_, _, rfl⟩ := go1_eq h; simp; omega
  | csrr => simp only [instrNext] at h; obtain ⟨_, _, rfl⟩ := go1_eq h; simp; omega
  | fence => simp only [instrNext] at h; obtain ⟨_, _, rfl⟩ := go1_eq h; simp; omega
  | fenceTso => simp only [instrNext] at h; obtain ⟨_, _, rfl⟩ := go1_eq h; simp; omega
  | fencei => simp only [instrNext] at h; obtain ⟨_, _, rfl⟩ := go1_eq h; simp; omega
  | nop => simp only [instrNext] at h; obtain ⟨_, _, rfl⟩ := go1_eq h; simp; omega
  | jmp tgt =>
    obtain ⟨hg, h⟩ := ite_none_some' h
    obtain ⟨_, _, rfl⟩ := go1_eq h
    simp; omega
  | br c rs1 rs2 tgt =>
    obtain ⟨hg, h⟩ := ite_none_some' h
    obtain ⟨_, _, rfl⟩ := go1_eq h
    split <;> simp <;> omega
  | loadAqPc => cases h
  | storeRlPc => cases h
  | _ =>
    replace h := ite_none_some h
    cases l
    all_goals try (simp only [reduceCtorEq] at h; done)
    all_goals first
      | (obtain ⟨_, rfl⟩ := ite_some_none h; simp; omega)
      | (cases h; simp; omega)

theorem litNext_pc {s s' : LP} {l : PLabel} {i : Nat} (hq : qOk s.q) (h : litNext s l = some s') :
    s'.prog = s.prog ∧ ((s'.pc = s.pc ∧ labelMsg i l = none) ∨ (s.pc < s'.pc ∧ s'.pc ≤ s.prog.length)) := by
  unfold litNext at h
  cases hqs : s.q with
  | cons l0 rest =>
    rw [hqs] at h hq
    simp only at h
    split at h
    · rename_i he
      subst he
      cases h
      have hq0 := hq.1 l (List.mem_cons_self ..)
      refine ⟨rfl, Or.inl ⟨rfl, ?_⟩⟩
      cases l <;> simp only [qLab, Bool.false_eq_true] at hq0 <;> rfl
    · cases h
  | nil =>
    rw [hqs] at h
    simp only at h
    cases hp : s.prog[s.pc]? with
    | none => rw [hp] at h; cases h
    | some ins =>
      rw [hp] at h
      have hn : s.pc < s.prog.length := (List.getElem?_eq_some_iff.1 hp).1
      obtain ⟨h1, h2, h3⟩ := instrNext_pc hn h
      exact ⟨h1, .inr ⟨h2, h3⟩⟩

/-- A hart emits at most one message per instruction it executes. -/
theorem solo_msgcount {img : Image} {M : List PMsg} {h : Nat} :
    ∀ {x y : LP × PState × GSet Nat} {tr : List (PLabel × Option Nat)},
      soloSteps litStep img M h x tr y → qOk x.1.q → x.1.pc ≤ x.1.prog.length →
        ((tr.map Prod.fst).filterMap (labelMsg h)).length + x.1.pc ≤ x.1.prog.length := by
  intro x y tr hs
  induction hs with
  | refl => intro _ hle; simpa using hle
  | step x l ots p' ws' prom' tr y hp hm _ ih =>
    intro hq hle
    obtain ⟨hprog, hc⟩ := litNext_pc (i := h) hq hp
    have hq' := litNext_q hq hp
    simp only [List.map_cons, List.filterMap_cons]
    rcases hc with ⟨hpc, hmsg⟩ | ⟨hlt, hle'⟩
    · rw [hmsg]
      have := ih hq' (by simp only; rw [hpc, hprog]; exact hle)
      simp only at this
      rw [hpc, hprog] at this
      exact this
    · have := ih hq' (by simp only; rw [hprog]; exact hle')
      simp only at this
      rw [hprog] at this
      cases labelMsg h l
      · simp only; omega
      · simp only [List.length_cons]; omega

theorem lpOf_prog (T : Test) {h : Nat} (hh : h < T.harts.length) : (lpOf T h).prog = T.prog h := by
  unfold lpOf progs; simp [hh]

theorem lpOf_pc (T : Test) {h : Nat} (hh : h < T.harts.length) : (lpOf T h).pc = 0 := by
  unfold lpOf progs; simp [hh]

theorem sum_le_range (f g : Nat → Nat) : ∀ n, (∀ h, h < n → f h ≤ g h) →
    ((List.range n).map f).sum ≤ ((List.range n).map g).sum
  | 0, _ => by simp
  | n + 1, hfg => by
    rw [List.range_succ, List.map_append, List.map_append, List.sum_append_nat, List.sum_append_nat]
    have := sum_le_range f g n (fun h hh => hfg h (by omega))
    have := hfg n (by omega)
    simp; omega

/-- THE NUMBER OF MESSAGES of a valid run is at most the total program length. -/
theorem valid_msgs_le {T : Test} {evs : List PEvt} {cfg : PCfg LP Unit}
    (hv : validRun litStep (testImg T) () (progs T) evs cfg) : cfg.pcLog.length ≤ progSum T := by
  rw [(valid_perm hv).length_eq, List.length_flatten, List.map_map]
  unfold progSum
  refine sum_le_range _ _ _ (fun h hh => ?_)
  obtain ⟨ag, _, _, hrun⟩ := valid_solo hv h hh
  have := solo_msgcount hrun (by simp only; rw [lpOf_q T hh]; exact qOk_nil)
    (by simp only; rw [lpOf_pc T hh]; omega)
  simp only [lpOf_pc T hh, lpOf_prog T hh, Nat.add_zero] at this
  simpa [Function.comp, fulMsgs] using this

theorem iterD_succ (T : Test) : ∀ (k : Nat) (d : DomL), iterD T (k + 1) d = domStep T (iterD T k d)
  | 0, _ => rfl
  | k + 1, d => by
    show iterD T (k + 1) (domStep T d) = domStep T (iterD T k (domStep T d))
    exact iterD_succ T k (domStep T d)

theorem chainB_flags (T : Test) : ∀ (k : Nat) (d : DomL), chainB T k d = true →
    ∀ j, j < k → (freeAll T (domF (testImg T) (iterD T j d))).all (fun r => !r.2) = true
  | 0, _, _, j, hj => absurd hj (by omega)
  | k + 1, d, h, j, hj => by
    simp only [chainB, Bool.and_eq_true] at h
    cases j with
    | zero => exact h.1
    | succ j => exact chainB_flags T k (domStep T d) h.2 j (by omega)

theorem domF_mem {img : Image} {d : DomL} {a : Int} {b : BitVec 8} (h : (a, b) ∈ d) : b ∈ domF img d a := by
  unfold domF; rw [List.mem_eraseDups]
  exact List.mem_append_right _ (List.mem_filterMap.2 ⟨(a, b), h, by simp⟩)

theorem domF_sub {img : Image} {d d' : DomL} (hsub : ∀ p ∈ d, p ∈ d') {a : Int} {b : BitVec 8}
    (h : b ∈ domF img d a) : b ∈ domF img d' a := by
  unfold domF at h ⊢
  rw [List.mem_eraseDups] at h ⊢
  rcases List.mem_append.1 h with h1 | h1
  · exact List.mem_append_left _ h1
  · obtain ⟨p, hp, hpb⟩ := List.mem_filterMap.1 h1
    exact List.mem_append_right _ (List.mem_filterMap.2 ⟨p, hsub p hp, hpb⟩)

theorem domStep_sub (T : Test) (d : DomL) : ∀ p ∈ d, p ∈ domStep T d := by
  intro p hp
  unfold domStep; rw [List.mem_eraseDups]; exact List.mem_append_left _ hp

theorem msgBytes_mem {m : PMsg} {k : Nat} {b : BitVec 8} (h : m.data[k]? = some b) :
    (m.pa + (k : Int), b) ∈ msgBytes m := by
  unfold msgBytes
  exact List.mem_filterMap.2 ⟨k, List.mem_range.2 (List.getElem?_eq_some_iff.1 h).1, by rw [h]; rfl⟩

/-- A step of the chain closes the free runs of its level into the next level. -/
theorem chain_closed {T : Test} {d : DomL} (hfl : (freeAll T (domF (testImg T) d)).all (fun r => !r.2) = true)
    {h : Nat} (hh : h < T.harts.length) :
    closedInto (domF (testImg T) d) (domF (testImg T) (domStep T d)) h (lpOf T h) := by
  intro ls y hfs m hm k b hb
  have hc := freeDFS_complete hfs (fuelOf T h) _ (Prod.ext rfl (freeAll_flag hfl hh))
  refine domF_mem ?_
  unfold domStep; rw [List.mem_eraseDups]
  refine List.mem_append_right _ (List.mem_flatMap.2 ⟨_, List.mem_map.2 ⟨h, List.mem_range.2 hh, rfl⟩,
    List.mem_flatMap.2 ⟨y, hc, List.mem_flatMap.2 ⟨m, hm, msgBytes_mem hb⟩⟩⟩)

/-- **THE DOMAIN-CHAIN CHECKER IS SOUND** for machine v2. -/
theorem forbidChainB_sound (T : Test) (hB : forbidChainB T = true) : ¬ allowedMach T := by
  rintro ⟨evs, cfg, hv, hdone, hcond⟩
  unfold forbidChainB at hB
  rw [Bool.and_eq_true] at hB
  obtain ⟨hch, hcand⟩ := hB
  obtain ⟨hq, hown, hruns⟩ := valid_nota_hyps hv
  let Ds : Nat → Int → List (BitVec 8) := fun j => domF (testImg T) (iterD T j [])
  have hmono : ∀ j a b, b ∈ Ds j a → b ∈ Ds (j + 1) a := by
    intro j a b hb
    simp only [Ds] at hb ⊢
    rw [iterD_succ]
    exact domF_sub (domStep_sub T _) hb
  have hle : ∀ j k a b, j ≤ k → b ∈ Ds j a → b ∈ Ds k a := by
    intro j k a b hjk hb
    induction k with
    | zero =>
      have : j = 0 := by omega
      subst this; exact hb
    | succ k ih =>
      rcases Nat.lt_or_ge j (k + 1) with h1 | h1
      · exact hmono k a b (ih (by omega))
      · have : j = k + 1 := by omega
        subst this; exact hb
  have hcl : ∀ (j h : Nat) (p : LP), j < progSum T → (progs T)[h]? = some p →
      closedInto (Ds j) (Ds (j + 1)) h p := by
    intro j h p hj hp
    obtain ⟨hh, rfl⟩ := progs_get_inv hp
    simp only [Ds]
    rw [iterD_succ]
    exact chain_closed (chainB_flags T _ _ hch j hj) hh
  have hdepth := nota_depth (ps := progs T) (N := progSum T) (Ds := Ds) (fun j a => domF_ne (testImg_some T) a)
    (fun a b h => domF_img h) hmono hcl hq hown hruns
  have hbytes : ∀ t a b, memByte (testImg T) cfg.pcLog t a = some b →
      b ∈ domF (testImg T) (iterD T (progSum T) []) a := by
    intro t a b hb
    have ht : t ≤ progSum T := Nat.le_trans (memByte_le hb) (valid_msgs_le hv)
    exact hle t _ a b ht (hdepth t a b ht hb)
  rw [candOk_sound hcand hv hdone hbytes] at hcond
  cases hcond

end Weak.Prom.Mach
