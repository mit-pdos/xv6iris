/-
Weak/Prom: **completeness S3a — reference verdicts from the logic: ref ⇒ mach ⇒ lit** (plan rev 7 §8 S3a+b
"Accept: re-derive every §5 FORBIDDEN verdict as `ref ⇒ mach ⇒ lit`").

* `uniformB T s` (every access has size `s`) gives NA-6 for EVERY execution of `T` (`singleSize_of_uniform`): two
  naturally aligned accesses of one size that overlap have the same address.  So the single-size scope of
  `rvwmo_complete` is discharged per test by `decide`, not assumed.
* `refFromLit` — THE GENERIC COROLLARY: if every valid run of machine v2 over `T` in which every hart finished
  satisfies a property `Q` of its load observations and final memory (what a `lit_` theorem proves in the logic),
  then every reference execution of `T` satisfies `Q` of ITS load observations and final memory
  (`rvwmo_complete` gives the run, `obsLoad_eq`/`finalMem_eq` the equal observations).
* `forbid_of_lit` — the reference verdict in the reference's own vocabulary (`forbiddenRef T`, the statement of
  `Ref*.lean`'s `ref_<test>`), from `refFromLit` and a BRIDGE: the test's outcome condition (final registers,
  final memory) implies the negation of `Q`.  The bridges are program dataflow facts, not consistency facts: they
  hold for every load valuation of every path (`regLoad`: a register's final value is the k-th load's value,
  checked over all paths by `decide`).
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Prom.CmpMain
import Weak.Prom.CoreLit6
import Weak.Prom.CoreLitDR
import Weak.Prom.RefLitmus

namespace Weak.Prom.Cmp

open MachCSL MachCSL.Stdpp Iris.Std
open Weak (Image Dsrc)
open Weak.Prom Weak.Prom.Mach Weak.Prom.Mach.Cert
open Weak.Prom.Ref
open PLabel

/-! ## 1. NA-6 for uniform-size programs -/

/-- Every load and store of the program has size `s`. -/
def instrSz (s : Nat) : Instr → Bool
  | .load sz _ _ _ _ => sz == s
  | .store sz _ _ _ => sz == s
  | _ => true

def uniformB (T : Test) (s : Nat) : Bool := T.harts.all (fun p => p.all (instrSz s))

theorem stepI_memSz {h n s : Nat} {st : SSt} {i : Instr} (hok : instrS3a i = true) (hu : instrSz s i = true)
    (hs : ∀ se ∈ st.evs, se.sk.kind.isMem = true → se.sk.sz = s) :
    (∀ s', stepI h n st i = .next s' → ∀ se ∈ s'.evs, se.sk.kind.isMem = true → se.sk.sz = s) ∧
    (∀ t f, stepI h n st i = .fork t f →
      (∀ se ∈ t.evs, se.sk.kind.isMem = true → se.sk.sz = s) ∧
      (∀ se ∈ f.evs, se.sk.kind.isMem = true → se.sk.sz = s)) := by
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
    intro se hse hm
    simp only [SSt.adv_evs, SSt.wr_evs, SSt.emit_evs, List.mem_append, List.mem_singleton] at hse
    rcases hse with hse | rfl
    · exact hs se hse hm
    · simpa [instrSz] using hu
  | store sz rs2 rs1 off =>
    refine ⟨fun s' e => ?_, fun t f e => by simp [stepI] at e⟩
    simp only [stepI, Ref.StepR.next.injEq] at e; subst e
    intro se hse hm
    simp only [SSt.adv_evs, SSt.emit_evs, List.mem_append, List.mem_singleton] at hse
    rcases hse with hse | rfl
    · exact hs se hse hm
    · simpa [instrSz] using hu
  | fence fs =>
    refine ⟨fun s' e => ?_, fun t f e => by simp [stepI] at e⟩
    simp only [stepI, Ref.StepR.next.injEq] at e; subst e
    intro se hse hm
    simp only [SSt.adv_evs, SSt.emit_evs, List.mem_append, List.mem_singleton] at hse
    rcases hse with hse | rfl
    · exact hs se hse hm
    · cases hm
  | fenceTso =>
    refine ⟨fun s' e => ?_, fun t f e => by simp [stepI] at e⟩
    simp only [stepI, Ref.StepR.next.injEq] at e; subst e
    intro se hse hm
    simp only [SSt.adv_evs, SSt.emit_evs, List.mem_append, List.mem_singleton] at hse
    rcases hse with (hse | rfl) | rfl
    · exact hs se hse hm
    · cases hm
    · cases hm
  | loadAq => simp [instrS3a] at hok
  | storeRl => simp [instrS3a] at hok
  | loadAqPc => simp [instrS3a] at hok
  | storeRlPc => simp [instrS3a] at hok
  | lr => simp [instrS3a] at hok
  | sc => simp [instrS3a] at hok
  | amo => simp [instrS3a] at hok

theorem symRun_memSz (p : List Instr) (hp : ∀ i ∈ p, instrS3a i = true) {s : Nat}
    (hu : ∀ i ∈ p, instrSz s i = true) (h : Nat) :
    ∀ (fuel : Nat) (st : SSt) (ch : List Bool) (sf : SSt), symRun p h fuel st ch = some sf →
      (∀ se ∈ st.evs, se.sk.kind.isMem = true → se.sk.sz = s) →
      ∀ se ∈ sf.evs, se.sk.kind.isMem = true → se.sk.sz = s
  | 0, st, ch, sf, H, _ => by simp [symRun] at H
  | fuel + 1, st, ch, sf, H, hs => by
    unfold symRun at H
    by_cases hpc : st.pc = p.length
    · rw [if_pos hpc] at H
      split at H
      · cases H; exact hs
      · cases H
    · rw [if_neg hpc] at H
      cases hi : p[st.pc]? with
      | none => rw [hi] at H; cases H
      | some i =>
        rw [hi] at H
        simp only at H
        have hsz := stepI_memSz (h := h) (n := p.length) (hp i (List.mem_of_getElem? hi))
          (hu i (List.mem_of_getElem? hi)) hs
        cases he : stepI h p.length st i with
        | stuck => rw [he] at H; cases H
        | next s' =>
          rw [he] at H
          exact symRun_memSz p hp hu h fuel s' ch sf H (hsz.1 s' he)
        | fork t f =>
          rw [he] at H
          simp only at H
          cases ch with
          | nil => cases H
          | cons b ch' =>
            cases b
            · exact symRun_memSz p hp hu h fuel f ch' sf H (hsz.2 t f he).2
            · exact symRun_memSz p hp hu h fuel t ch' sf H (hsz.2 t f he).1

theorem aligned_eq {s a b : Nat} (hs : 0 < s) (ha : a % s = 0) (hb : b % s = 0) (h1 : a < b + s) (h2 : b < a + s) :
    a = b := by
  have ea := Nat.div_add_mod a s
  have eb := Nat.div_add_mod b s
  rw [ha, Nat.add_zero] at ea
  rw [hb, Nat.add_zero] at eb
  have k1 : a / s < b / s + 1 := by
    apply Nat.lt_of_mul_lt_mul_left (a := s)
    rw [Nat.mul_add, Nat.mul_one, ea, eb]; exact h1
  have k2 : b / s < a / s + 1 := by
    apply Nat.lt_of_mul_lt_mul_left (a := s)
    rw [Nat.mul_add, Nat.mul_one, ea, eb]; exact h2
  have : a / s = b / s := by omega
  rw [← ea, ← eb, this]

/-- **NA-6 FOR EVERY EXECUTION of a uniform-size program**: all memory operations have size `s` and are naturally
aligned (`condsOk`), so overlapping ones have the same address. -/
theorem singleSize_of_uniform {T : Test} (hT : progS3aB T = true) {s : Nat} (hu : uniformB T s = true)
    (hs : 0 < s) {chs : List (List Bool)} {trs : List SSt} {ν : Val} (g : List EvId)
    (hrun : T.runAll chs = some trs) (hc : condsOk ν trs = true) : singleSize (conc T trs ν g) := by
  obtain ⟨hlen, hpaths⟩ := runAll_spec hrun
  have hall : ∀ e ∈ (conc T trs ν g).ids, (sskOf trs e).kind.isMem = true →
      (sskOf trs e).sz = s ∧ ((conc T trs ν g).ev e).pa % s = 0 := by
    intro e he hm
    rw [conc_ids] at he
    obtain ⟨l, hl1, hl2⟩ := (mem_idsOf _ _).1 he
    simp only [List.getElem?_map] at hl1
    obtain ⟨st, hst, rfl⟩ := Option.map_eq_some_iff.1 hl1
    have hi : e.1 < trs.length := (List.getElem?_eq_some_iff.1 hst).1
    have hst' : trs[e.1] = st := (List.getElem?_eq_some_iff.1 hst).2
    obtain ⟨ch, hch⟩ := hpaths e.1 hi
    have hse : sevAt trs e = st.evs[e.2] := by simp [sevAt, hst, List.getElem?_eq_getElem hl2]
    have hprog : ∀ i ∈ T.prog e.1, instrS3a i = true := by
      intro i hin
      obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hin
      exact Weak.Prom.Cmp.instr_scope (h := e.1) hT (List.getElem?_eq_getElem hk)
    have hprogu : ∀ i ∈ T.prog e.1, instrSz s i = true := by
      intro i hin
      simp only [uniformB, List.all_eq_true] at hu
      unfold Test.prog at hin
      cases hh : T.harts[e.1]? with
      | none => rw [hh] at hin; simp at hin
      | some p => rw [hh] at hin; exact hu p (List.mem_of_getElem? hh) i hin
    rw [hst'] at hch
    have hmem : st.evs[e.2] ∈ st.evs := List.getElem_mem hl2
    have hsk : sskOf trs e = st.evs[e.2].sk := by simp [sskOf, hse]
    rw [hsk] at hm ⊢
    refine ⟨symRun_memSz _ hprog hprogu e.1 _ _ _ _ hch (fun se hse' => by simp [Test.init] at hse')
      _ hmem hm, ?_⟩
    have hcs := List.all_eq_true.1 hc st (List.mem_of_getElem? hst)
    simp only [Bool.and_eq_true, List.all_eq_true] at hcs
    have := hcs.2 _ hmem
    have hacc : st.evs[e.2].sk.kind.isAcc = true := by simp [Kind.isAcc, hm]
    simp only [hacc, Bool.not_true, Bool.false_or, beq_iff_eq] at this
    rw [conc_ev _ _ _ _ _ he, hse]
    rw [symRun_memSz _ hprog hprogu e.1 _ _ _ _ hch (fun se hse' => by simp [Test.init] at hse') _ hmem hm] at this
    exact this
  intro a ha b hb ham hbm hov
  rw [conc_sk] at ham hbm
  obtain ⟨sa, pa⟩ := hall a ha ham
  obtain ⟨sb, pb⟩ := hall b hb hbm
  have hov' := hov
  simp only [overlapB, decide_eq_true_eq] at hov'
  have esa : ((conc T trs ν g).ev a).sk.sz = s := by rw [← sa, ← conc_sk T trs ν g a]; rfl
  have esb : ((conc T trs ν g).ev b).sk.sz = s := by rw [← sb, ← conc_sk T trs ν g b]; rfl
  rw [esa, esb] at hov'
  exact ⟨aligned_eq hs pa pb hov'.1 hov'.2, by rw [conc_sk, conc_sk, sa, sb]⟩

/-! ## 2. The generic corollary -/

/-- **REF ⇒ MACH ⇒ LIT**: a property `Q` that every valid run of machine v2 (with every hart finished) has, of its
load observations and final memory, every reference execution has, of its own. -/
theorem refFromLit (T : Test) (hT : progS3aB T = true) {s : Nat} (hu : uniformB T s = true) (hs : 0 < s)
    (Q : (Nat → Nat → Option Nat) → (Nat → Nat → Nat) → Prop)
    (hlit : ∀ (M : List PMsg) (run : PF.PFRun LP Unit), PF.validRun litStep (testImg T) () (progs T) M run →
      (∀ h, h < T.harts.length → run.done PF.litDone h ()) → Q run.obsLoad (finalMem (testImg T) M)) :
    ∀ chs ν g, progExec T chs ν g → ∀ trs, T.runAll chs = some trs →
      Q (refObsLoad (conc T trs ν g)) (refFinalMem (conc T trs ν g)) := by
  intro chs ν g hE trs hr
  have hE' := hE
  unfold progExec at hE'
  rw [hr] at hE'
  obtain ⟨hc, hX⟩ := hE'
  obtain ⟨run, hv, _, hlen, hdone, hrow, _, hmem⟩ :=
    rvwmo_complete T hT hr hc hX (singleSize_of_uniform hT hu hs g hr hc) trivial
  have hobs : run.obsLoad = refObsLoad (conc T trs ν g) := funext fun h => funext fun k => obsLoad_eq (hrow h) k
  have hfm : finalMem (testImg T) (memOf (conc T trs ν g)) = refFinalMem (conc T trs ν g) :=
    funext fun a => funext fun n => hmem a n
  rw [← hobs, ← hfm]
  refine hlit _ run hv (fun h hh => ?_)
  have hh' : h < run.cfg.pcAgs.length := by rw [hlen]; exact hh
  refine ⟨run.cfg.pcAgs[h], List.getElem?_eq_getElem hh', ?_⟩
  obtain ⟨h1, h2⟩ := hdone h _ (List.getElem?_eq_getElem hh')
  simp [PF.litDone, h1, h2]

/-- **THE REFERENCE VERDICT, IN THE REFERENCE'S VOCABULARY**: `forbiddenRef T` (the statement of `ref_<test>`)
from the logic's property `Q` and a bridge "the outcome implies ¬ Q". -/
theorem forbid_of_lit (T : Test) (hT : progS3aB T = true) {s : Nat} (hu : uniformB T s = true) (hs : 0 < s)
    (Q : (Nat → Nat → Option Nat) → (Nat → Nat → Nat) → Prop)
    (hlit : ∀ (M : List PMsg) (run : PF.PFRun LP Unit), PF.validRun litStep (testImg T) () (progs T) M run →
      (∀ h, h < T.harts.length → run.done PF.litDone h ()) → Q run.obsLoad (finalMem (testImg T) M))
    (hbr : ∀ chs ν g trs, progExec T chs ν g → T.runAll chs = some trs →
      T.cond.eval (finalReg trs ν) (finalByte (conc T trs ν g)) = true →
      ¬ Q (refObsLoad (conc T trs ν g)) (refFinalMem (conc T trs ν g))) :
    forbiddenRef T := by
  intro chs ν g hE hout
  unfold outcome at hout
  cases hr : T.runAll chs with
  | none => rw [hr] at hout; cases hout
  | some trs =>
    rw [hr] at hout
    exact hbr chs ν g trs hE hr hout (refFromLit T hT hu hs Q hlit chs ν g hE trs hr)

/-! ## 3. Bridges: final registers and memory as observations -/

/-- The indices of a path's load events. -/
def loadIdx (evs : List SEv) : List Nat :=
  (List.range evs.length).filter (fun j => match evs[j]? with | some se => se.sk.kind.isLoad | none => false)

/-- REGISTER `r` OF HART `h` ENDS WITH THE `k`-TH LOAD's VALUE (a `sz`-byte sign-extending load), on every path:
a dataflow fact of the program, checked by `decide`. -/
def regLoadB (T : Test) (h r k sz : Nat) : Bool :=
  T.paths.all (fun p => match p.2[h]? with
    | some st => match (loadIdx st.evs)[k]? with
      | some j => (st.rd r).1 == Ex.ld (h, j) sz true && (match st.evs[j]? with
          | some se => se.sk.sz == sz | none => false)
      | none => false
    | none => false)

theorem rowSeg_loadIdx {T : Test} {trs : List SSt} {ν : Val} {g : List EvId} {h : Nat} {st : SSt}
    (htr : trs[h]? = some st) :
    rowSeg (conc T trs ν g) h 0 st.evs.length = (loadIdx st.evs).map (fun j => ν (h, j)) := by
  unfold rowSeg loadIdx
  rw [Nat.sub_zero, ← List.range_eq_range']
  have hsev : ∀ j (hj : j < st.evs.length), sevAt trs (h, j) = st.evs[j] := by
    intro j hj; simp [sevAt, htr, List.getElem?_eq_getElem hj]
  have hf : (List.range st.evs.length).filter (fun j => ((conc T trs ν g).sk (h, j)).kind.isLoad) =
      (List.range st.evs.length).filter (fun j => match st.evs[j]? with
        | some se => se.sk.kind.isLoad | none => false) := by
    apply List.filter_congr
    intro j hj
    have hj' := List.mem_range.1 hj
    rw [conc_sk, sskOf, hsev j hj', List.getElem?_eq_getElem hj']
  rw [hf]
  apply List.map_congr_left
  intro j hj
  obtain ⟨hj1, hj2⟩ := List.mem_filter.1 hj
  have hj' := List.mem_range.1 hj1
  have hid : (h, j) ∈ sids trs := (mem_idsOf _ _).2 ⟨st.evs, by simp [htr], hj'⟩
  rw [conc_ev _ _ _ _ _ hid, hsev j hj']
  rw [List.getElem?_eq_getElem hj'] at hj2
  simp only [concEv, hj2, if_true]

theorem sext_small {sz u v : Nat} (hsz : 0 < sz ∧ sz ≤ 8) (hu : u < 2 ^ (8 * sz)) (hv : v < 2 ^ (8 * sz - 1))
    (h : sext sz u = v) : u = v := by
  have hp : 2 ^ (8 * sz) ≤ two64 := pow_le_two64 hsz.2
  have h2 : 2 ^ (8 * sz) = 2 * 2 ^ (8 * sz - 1) := by
    rw [← Nat.pow_succ']; congr 1; omega
  unfold sext at h
  split at h
  · omega
  · exact h

/-- **THE REGISTER BRIDGE**: if register `r` of hart `h` ends with the `k`-th load's value (`regLoadB`) and the
outcome asks it to be `v` (small enough not to be sign-extended), the reference's `k`-th load observation is
`v`. -/
theorem bridge_reg {T : Test} (hT : progS3aB T = true) {s : Nat} (hu : uniformB T s = true) (hs : 0 < s)
    {chs : List (List Bool)} {ν : Val} {g : List EvId} {trs : List SSt} (hE : progExec T chs ν g)
    (hr : T.runAll chs = some trs) {h r k sz v : Nat} (hB : regLoadB T h r k sz = true)
    (hsz : 0 < sz ∧ sz ≤ 8) (hv : v < 2 ^ (8 * sz - 1)) (hv64 : v < two64)
    (hreg : finalReg trs ν h r = v) : refObsLoad (conc T trs ν g) h k = some v := by
  have hE' := hE
  unfold progExec at hE'
  rw [hr] at hE'
  obtain ⟨hc, hX⟩ := hE'
  have hpath := List.all_eq_true.1 hB _ (runAll_paths T chs trs hr)
  simp only at hpath
  cases htr : trs[h]? with
  | none => rw [htr] at hpath; cases hpath
  | some st =>
    rw [htr] at hpath
    simp only at hpath
    cases hk : (loadIdx st.evs)[k]? with
    | none => rw [hk] at hpath; cases hpath
    | some j =>
      rw [hk] at hpath
      simp only [Bool.and_eq_true, beq_iff_eq] at hpath
      obtain ⟨hld, hsj⟩ := hpath
      have hjl : j < st.evs.length := by
        have := List.mem_of_getElem? hk
        simp only [loadIdx, List.mem_filter, List.mem_range] at this
        exact this.1
      rw [List.getElem?_eq_getElem hjl] at hsj
      simp only [beq_iff_eq] at hsj
      -- the context
      have hio : T.io = [] := by
        simp only [progS3aB, Bool.and_eq_true, List.isEmpty_iff] at hT; exact hT.1.1
      have c : HCtx T trs ν (conc T trs ν g) h st :=
        ⟨rfl, hX, hio, singleSize_of_uniform hT hu hs g hr hc, hc, hT, htr⟩
      have hjm : st.evs[j]? = some st.evs[j] := List.getElem?_eq_getElem hjl
      have hjload : st.evs[j].sk.kind.isLoad = true := by
        have := List.mem_of_getElem? hk
        simp only [loadIdx, List.mem_filter, hjm] at this
        exact this.2
      have hid := c.id hjm
      have hsk := c.sk hjm
      have hrl : ((conc T trs ν g).sk (h, j)).kind.isLoad = true := by rw [hsk]; exact hjload
      have hrdat : ((conc T trs ν g).ev (h, j)).rdat = ν (h, j) := by
        rw [c.ev hjm]; simp [concEv, hjload]
      have hlen : (ν (h, j)).length = sz := by rw [← hrdat, c.rdat_len hid hrl, hsk, hsj]
      have hbyt : ∀ b ∈ ν (h, j), b < 256 := by rw [← hrdat]; exact c.rdat_lt hid hrl
      -- the observation
      have hrow : refRow (conc T trs ν g) h = (loadIdx st.evs).map (fun j => ν (h, j)) := by
        rw [c.refRow_eq, rowSeg_loadIdx htr]
      unfold refObsLoad
      rw [hrow, List.getElem?_map, hk]
      simp only [Option.map_some, Option.some.injEq]
      -- the value
      unfold finalReg at hreg
      rw [htr] at hreg
      simp only [Option.map_some, Option.getD_some, hld, Ex.eval] at hreg
      rw [List.take_of_length_le (by omega)] at hreg
      have hlt := bytesVal_lt (ν (h, j)) hbyt
      rw [hlen] at hlt
      rw [Nat.mod_eq_of_lt hlt] at hreg
      simp only [if_true] at hreg
      exact sext_small hsz hlt hv hreg

/-- An outcome condition `.reg h r v` holds of the final registers. -/
theorem oc_reg {fr : Nat → Nat → Nat} {fm : Nat → Nat} {h r v : Nat} (hv : v < two64)
    (H : (OC.reg h r v).eval fr fm = true) : fr h r = v := by
  simp only [OC.eval, beq_iff_eq] at H
  rw [H, Nat.mod_eq_of_lt hv]

theorem oc_and {fr : Nat → Nat → Nat} {fm : Nat → Nat} {p q : OC} (H : (OC.and p q).eval fr fm = true) :
    p.eval fr fm = true ∧ q.eval fr fm = true := by
  simpa [OC.eval] using H

/-- An outcome condition `.mem a sz v` is the reference's final memory. -/
theorem oc_mem {X : Exec} {fr : Nat → Nat → Nat} {a sz v : Nat} (hv : v < 2 ^ (8 * sz))
    (H : (OC.mem a sz v).eval fr (finalByte X) = true) : refFinalMem X a sz = v := by
  simp only [OC.eval, beq_iff_eq] at H
  unfold refFinalMem
  rw [H, Nat.mod_eq_of_lt hv]

theorem oc_notMem {X : Exec} {fr : Nat → Nat → Nat} {a sz v : Nat} (hv : v < 2 ^ (8 * sz))
    (H : (OC.not (OC.mem a sz v)).eval fr (finalByte X) = true) : refFinalMem X a sz ≠ v := by
  simp only [OC.eval, Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq] at H
  unfold refFinalMem
  intro he; apply H; rw [he, Nat.mod_eq_of_lt hv]

/-- **THE REGISTER BRIDGE, BOTH WAYS**: the reference's `k`-th load observation is `v` iff the outcome condition
`.reg h r v` holds (for a register that ends with that load's value, `regLoadB`). -/
theorem obsReg {T : Test} (hT : progS3aB T = true) {s : Nat} (hu : uniformB T s = true) (hs : 0 < s)
    {chs : List (List Bool)} {ν : Val} {g : List EvId} {trs : List SSt} (hE : progExec T chs ν g)
    (hr : T.runAll chs = some trs) {h r k sz v : Nat} (hB : regLoadB T h r k sz = true)
    (hsz : 0 < sz ∧ sz ≤ 8) (hv : v < 2 ^ (8 * sz - 1)) (hv64 : v < two64) (fm : Nat → Nat) :
    refObsLoad (conc T trs ν g) h k = some v ↔ (OC.reg h r v).eval (finalReg trs ν) fm = true := by
  constructor
  · intro ho
    -- the converse direction of `bridge_reg`
    have hE' := hE
    unfold progExec at hE'
    rw [hr] at hE'
    obtain ⟨hc, hX⟩ := hE'
    have hpath := List.all_eq_true.1 hB _ (runAll_paths T chs trs hr)
    simp only at hpath
    cases htr : trs[h]? with
    | none => rw [htr] at hpath; cases hpath
    | some st =>
      rw [htr] at hpath
      simp only at hpath
      cases hk : (loadIdx st.evs)[k]? with
      | none => rw [hk] at hpath; cases hpath
      | some j =>
        rw [hk] at hpath
        simp only [Bool.and_eq_true, beq_iff_eq] at hpath
        obtain ⟨hld, hsj⟩ := hpath
        have hjl : j < st.evs.length := by
          have := List.mem_of_getElem? hk
          simp only [loadIdx, List.mem_filter, List.mem_range] at this
          exact this.1
        rw [List.getElem?_eq_getElem hjl] at hsj
        simp only [beq_iff_eq] at hsj
        have hio : T.io = [] := by
          simp only [progS3aB, Bool.and_eq_true, List.isEmpty_iff] at hT; exact hT.1.1
        have c : HCtx T trs ν (conc T trs ν g) h st :=
          ⟨rfl, hX, hio, singleSize_of_uniform hT hu hs g hr hc, hc, hT, htr⟩
        have hjm : st.evs[j]? = some st.evs[j] := List.getElem?_eq_getElem hjl
        have hjload : st.evs[j].sk.kind.isLoad = true := by
          have := List.mem_of_getElem? hk
          simp only [loadIdx, List.mem_filter, hjm] at this
          exact this.2
        have hid := c.id hjm
        have hsk := c.sk hjm
        have hrl : ((conc T trs ν g).sk (h, j)).kind.isLoad = true := by rw [hsk]; exact hjload
        have hrdat : ((conc T trs ν g).ev (h, j)).rdat = ν (h, j) := by
          rw [c.ev hjm]; simp [concEv, hjload]
        have hlen : (ν (h, j)).length = sz := by rw [← hrdat, c.rdat_len hid hrl, hsk, hsj]
        have hbyt : ∀ b ∈ ν (h, j), b < 256 := by rw [← hrdat]; exact c.rdat_lt hid hrl
        have hrow : refRow (conc T trs ν g) h = (loadIdx st.evs).map (fun j => ν (h, j)) := by
          rw [c.refRow_eq, rowSeg_loadIdx htr]
        unfold refObsLoad at ho
        rw [hrow, List.getElem?_map, hk] at ho
        simp only [Option.map_some, Option.some.injEq] at ho
        have hlt := bytesVal_lt (ν (h, j)) hbyt
        rw [hlen] at hlt
        simp only [OC.eval, beq_iff_eq]
        unfold finalReg
        rw [htr]
        simp only [Option.map_some, Option.getD_some, hld, Ex.eval]
        rw [List.take_of_length_le (by omega), Nat.mod_eq_of_lt hlt, ho, Nat.mod_eq_of_lt hv64]
        simp only [if_true]
        unfold sext
        rw [if_neg (by omega)]
  · intro H
    exact bridge_reg hT hu hs hE hr hB hsz hv hv64 (oc_reg hv64 H)

theorem oc_and_iff {fr : Nat → Nat → Nat} {fm : Nat → Nat} {p q : OC} :
    (OC.and p q).eval fr fm = true ↔ p.eval fr fm = true ∧ q.eval fr fm = true := by
  simp [OC.eval]

theorem oc_or_iff {fr : Nat → Nat → Nat} {fm : Nat → Nat} {p q : OC} :
    (OC.or p q).eval fr fm = true ↔ p.eval fr fm = true ∨ q.eval fr fm = true := by
  simp [OC.eval]

theorem oc_not_iff {fr : Nat → Nat → Nat} {fm : Nat → Nat} {p : OC} :
    (OC.not p).eval fr fm = true ↔ ¬ p.eval fr fm = true := by
  simp [OC.eval]

theorem oc_mem_iff {X : Exec} {fr : Nat → Nat → Nat} {a sz v : Nat} (hv : v < 2 ^ (8 * sz)) :
    (OC.mem a sz v).eval fr (finalByte X) = true ↔ refFinalMem X a sz = v := by
  simp only [OC.eval, beq_iff_eq]
  unfold refFinalMem
  rw [Nat.mod_eq_of_lt hv]

/-- The reference checker's verdict, transported to an outcome `R` of the observations that implies the test's
condition: no reference execution has `R` (used to check that `refFromLit` agrees with `ref_<test>` where the
logic states a sub-outcome of the repository condition). -/
theorem refChk (T : Test) (hF : forbiddenRef T) (R : (Nat → Nat → Option Nat) → (Nat → Nat → Nat) → Prop)
    (hbr : ∀ chs ν g trs, progExec T chs ν g → T.runAll chs = some trs →
      R (refObsLoad (conc T trs ν g)) (refFinalMem (conc T trs ν g)) →
      T.cond.eval (finalReg trs ν) (finalByte (conc T trs ν g)) = true) :
    ∀ chs ν g, progExec T chs ν g → ∀ trs, T.runAll chs = some trs →
      ¬ R (refObsLoad (conc T trs ν g)) (refFinalMem (conc T trs ν g)) := by
  intro chs ν g hE trs hr hR
  apply hF chs ν g hE
  unfold outcome
  rw [hr]
  exact hbr chs ν g trs hE hr hR

/-- `obsReg` for word loads (`lw`, size 4). -/
theorem obsReg4 {T : Test} (hT : progS3aB T = true) (hu : uniformB T 4 = true)
    {chs : List (List Bool)} {ν : Val} {g : List EvId} {trs : List SSt} (hE : progExec T chs ν g)
    (hr : T.runAll chs = some trs) {h r k v : Nat} (hB : regLoadB T h r k 4 = true) (hv : v < 2 ^ 31)
    (fm : Nat → Nat) :
    refObsLoad (conc T trs ν g) h k = some v ↔ (OC.reg h r v).eval (finalReg trs ν) fm = true :=
  obsReg hT hu (by decide) hE hr hB ⟨by decide, by decide⟩ hv (Nat.lt_trans hv (by decide)) fm

/-- `obsReg` for doubleword loads (`ld`, size 8). -/
theorem obsReg8 {T : Test} (hT : progS3aB T = true) (hu : uniformB T 8 = true)
    {chs : List (List Bool)} {ν : Val} {g : List EvId} {trs : List SSt} (hE : progExec T chs ν g)
    (hr : T.runAll chs = some trs) {h r k v : Nat} (hB : regLoadB T h r k 8 = true) (hv : v < 2 ^ 63)
    (fm : Nat → Nat) :
    refObsLoad (conc T trs ν g) h k = some v ↔ (OC.reg h r v).eval (finalReg trs ν) fm = true :=
  obsReg hT hu (by decide) hE hr hB ⟨by decide, by decide⟩ hv (Nat.lt_trans hv (by decide)) fm

end Weak.Prom.Cmp
