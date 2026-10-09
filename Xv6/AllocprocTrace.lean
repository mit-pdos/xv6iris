/-
**THE ALLOCPROC SHADOW ON THE TRACE** (weak-allocproc plan §C Stage 0, item
W1, rulings [R3.s1], [R6.5d], [R6.5d-alt]; D23): what the closed NI theorem
(`LinkNiAdequacy.xv6NiAdequacy`) already says about every fork round of a run
from the booting machine, read off at the filings its ledger witnesses, and
the range lemma for `PidEv.pidPick` the plan asks W1 to prove.

* **`pidPick_range`** ([R6.5d-alt]): from `cycAt`'s codomain and the counter
  tie `nextOf pidmax h ≤ pidmax` (the kernel's `PidLock.pidTie` keeps the
  stored counter there), the pick is in `[1, pidmax]`.  The tie is a
  HYPOTHESIS: on an arbitrary history it fails (`pidPick_badHist`: a `PAlloc`
  of an out-of-range pid steps the counter past `PIDMAX`, and with every
  candidate live `pidPick` falls back to the counter -- `UsysDet` deviation 6
  says the same).  `pidPick_range_of_wf` is the form at a history whose
  allocations are all in range.
* **`allocprocTraceAns`**: from the machine off, never booted, with `fs.img`
  on its disk, every run's trace has a one-shot NI filing `F` at which every
  fork round of every incarnation cites a prefix `ι`, answers
  `usysForkAns ι` (the pid `pidPick PIDMAX ι.pev` when `forkOk ι`, else `-1`)
  -- tie β (D11) --, its answer is `-1` or in `[1, PIDMAX]` (the kernel's
  row, `usysMemOk`'s fork entry, carried by the round's `roundOkKeys`), and
  on success the pick is in `[1, PIDMAX]` OR is the counter fallback at the
  one value `2^32 - 1` (whose sign-extended word IS `-1`).

## Deviations from the plan's statement ([R6.5d]) -- see `PROGRESS-W1.md`

1. **The bound conjunct `forkOk ι → 1 ≤ pidPick PIDMAX ι.pev ≤ PIDMAX` is
   NOT derivable from `xv6NiPhi`**: the trace conclusion constrains the cited
   pid prefix only through the answer word, and `pidPick_badHist` exhibits a
   history whose pick is `2^32 - 1`, whose word is `-1`, consistent with every
   row `niEntryOk` carries.  The theorem proves the strongest trace-level
   form (the disjunction above); the plan's form needs the counter tie at the
   citation exported by the NI ledger (an edit to merged files).
2. **`poolEmpty` at every `KNull` is NOT derivable** from `xv6NiPhi` either:
   no filing row mentions the allocator history's shape (the receipts
   `KallocDefs.kNullRcpt`/`kAllocRcpt` carry it in Iris only).  Not stated.
3. `allocprocTraceAns`, not `allocprocTrace`: the plan's name is left for the
   statement as specified, once the owner rules on the exports.

Lean-only (no Rocq source).  Helpers are file-qualified `AllocprocTrace.*`.
-/
import Xv6.LinkNiAdequacy

namespace Xv6

open Iris Iris.BI Iris.ProofMode Iris.Std Std MachCSL
open Iris.ProgramLogic Language.Notation PrimStep

/-! ## §1 The counter's range -/

/-- The counter fold stays in `[1, B]` when every allocation it meets steps it
there. -/
theorem AllocprocTrace.foldNext_bounds (pidmax B : Nat) :
    ∀ (l : List Pev) (n : Nat), 1 ≤ n → n ≤ B →
      (∀ a p, Pev.PAlloc a p ∈ l → p.toNat ≠ pidmax → p.toNat + 1 ≤ B) →
      1 ≤ l.foldl (nextStep pidmax) n ∧ l.foldl (nextStep pidmax) n ≤ B
  | [], n, h1, h2, _ => ⟨h1, h2⟩
  | e :: l, n, h1, h2, hs => by
    rw [List.foldl_cons]
    have hB : 1 ≤ B := Nat.le_trans h1 h2
    refine AllocprocTrace.foldNext_bounds pidmax B l _ ?_ ?_
      (fun a p hm hne => hs a p (List.mem_cons_of_mem _ hm) hne)
    · cases e with
      | PAlloc a p => dsimp only [nextStep]; split <;> omega
      | PFree a p => exact h1
    · cases e with
      | PAlloc a p =>
        dsimp only [nextStep]
        split
        · exact hB
        · rename_i hne; exact hs a p List.mem_cons_self hne
      | PFree a p => exact h2

/-- The counter is in `[1, B]` when every allocation steps it there. -/
theorem AllocprocTrace.nextOf_bounds (pidmax B : Nat) (h : List Pev) (hB : 1 ≤ B)
    (hs : ∀ a p, Pev.PAlloc a p ∈ h → p.toNat ≠ pidmax → p.toNat + 1 ≤ B) :
    1 ≤ nextOf pidmax h ∧ nextOf pidmax h ≤ B :=
  AllocprocTrace.foldNext_bounds pidmax B h 1 (Nat.le_refl 1) hB hs

/-- The counter is at most `2^32` on every history (a pid is a 32-bit word). -/
theorem AllocprocTrace.nextOf_le_two32 (pidmax : Nat) (h : List Pev) : nextOf pidmax h ≤ 2 ^ 32 :=
  (AllocprocTrace.nextOf_bounds pidmax (2 ^ 32) h (by decide)
    (fun _ p _ _ => by have := p.isLt; omega)).2

/-- The counter is at most `pidmax` at a history whose allocations are all at
most `pidmax`. -/
theorem AllocprocTrace.nextOf_le_of_wf (pidmax : Nat) (h : List Pev) (hp : 0 < pidmax)
    (hwf : ∀ a p, Pev.PAlloc a p ∈ h → p.toNat ≤ pidmax) : nextOf pidmax h ≤ pidmax :=
  (AllocprocTrace.nextOf_bounds pidmax pidmax h hp
    (fun a p hm hne => by have := hwf a p hm; omega)).2

/-! ## §2 THE PICK'S RANGE ([R6.5d-alt]) -/

/-- `cycAt`'s codomain: every cyclic candidate is in `[1, pidmax]`. -/
theorem AllocprocTrace.cycAt_range (pidmax n i : Nat) (hp : 0 < pidmax) :
    1 ≤ cycAt pidmax n i ∧ cycAt pidmax n i ≤ pidmax := by
  unfold cycAt
  have := Nat.mod_lt (n - 1 + i) hp
  omega

/-- The pick is a cyclic candidate, hence in range, or the counter fallback. -/
theorem AllocprocTrace.pidPick_cases (pidmax : Nat) (h : List Pev) (hp : 0 < pidmax) :
    (1 ≤ pidPick pidmax h ∧ pidPick pidmax h ≤ pidmax) ∨ pidPick pidmax h = nextOf pidmax h := by
  unfold pidPick
  split
  · exact Or.inl (AllocprocTrace.cycAt_range _ _ _ hp)
  · exact Or.inr rfl

/-- **THE PICK IS A PID** ([R6.5d-alt]): under the counter tie
`nextOf pidmax h ≤ pidmax`, `pidPick pidmax h ∈ [1, pidmax]`. -/
theorem pidPick_range (pidmax : Nat) (h : List Pev) (hp : 0 < pidmax) (hn : nextOf pidmax h ≤ pidmax) :
    1 ≤ pidPick pidmax h ∧ pidPick pidmax h ≤ pidmax := by
  rcases AllocprocTrace.pidPick_cases pidmax h hp with hr | hr
  · exact hr
  · rw [hr]
    exact ⟨(AllocprocTrace.nextOf_bounds pidmax (2 ^ 32) h (by decide)
      (fun _ p _ _ => by have := p.isLt; omega)).1, hn⟩

/-- `pidPick_range` at a history whose allocations are all in range. -/
theorem pidPick_range_of_wf (pidmax : Nat) (h : List Pev) (hp : 0 < pidmax)
    (hwf : ∀ a p, Pev.PAlloc a p ∈ h → p.toNat ≤ pidmax) :
    1 ≤ pidPick pidmax h ∧ pidPick pidmax h ≤ pidmax :=
  pidPick_range pidmax h hp (AllocprocTrace.nextOf_le_of_wf pidmax h hp hwf)

/-- The pick is at most `2^32` on every history. -/
theorem AllocprocTrace.pidPick_le_two32 (h : List Pev) : pidPick PIDMAX h ≤ 2 ^ 32 := by
  rcases AllocprocTrace.pidPick_cases PIDMAX h (by decide) with hr | hr
  · have := hr.2; have h2 : PIDMAX = 1000 := rfl; omega
  · rw [hr]; exact AllocprocTrace.nextOf_le_two32 PIDMAX h

/-! ## §3 The tie is needed: a history whose pick is out of range -/

/-- Every pid `1..PIDMAX` allocated, then the out-of-range `2^32 - 2`: every
candidate is live and the counter is `2^32 - 1`. -/
def AllocprocTrace.badHist : List Pev :=
  (List.range PIDMAX).map (fun i => Pev.PAlloc 0#64 (BitVec.ofNat 32 (i + 1))) ++
    [Pev.PAlloc 0#64 (BitVec.ofNat 32 (2 ^ 32 - 2))]

/-- **The tie is not free** (`UsysDet` deviation 6): on `badHist` the pick is
the counter fallback `2^32 - 1`, out of `[1, PIDMAX]`. -/
theorem pidPick_badHist : pidPick PIDMAX AllocprocTrace.badHist = 2 ^ 32 - 1 := by
  decide +kernel

/-- ... and its sign-extended word is `-1`: a successful fork at such a
prefix answers what a failed one does, so the trace cannot tell. -/
theorem AllocprocTrace.badWord :
    BitVec.signExtend 64 (BitVec.ofNat 32 (pidPick PIDMAX AllocprocTrace.badHist)) = -1#64 := by
  rw [pidPick_badHist]; decide

/-! ## §4 The answer word's arithmetic -/

/-- fork's row in the kernel's table (`usysMemOk`'s fork entry). -/
def AllocprocTrace.forkRet (r : BitVec 64) : Prop := r = -1#64 ∨ (1 ≤ r.toInt ∧ r.toInt ≤ PIDMAX)

/-- A pick at most `2^32` whose sign-extended 32-bit word has fork's row is in
`[1, PIDMAX]` or is `2^32 - 1`. -/
theorem AllocprocTrace.pickOfWord (P : Nat) (hP : P ≤ 2 ^ 32)
    (hr : AllocprocTrace.forkRet (BitVec.signExtend 64 (BitVec.ofNat 32 P))) :
    (1 ≤ P ∧ P ≤ PIDMAX) ∨ P = 2 ^ 32 - 1 := by
  have ht : (BitVec.signExtend 64 (BitVec.ofNat 32 P)).toInt = (BitVec.ofNat 32 P).toInt :=
    BitVec.toInt_signExtend_of_le (by decide)
  rw [BitVec.toInt_eq_toNat_cond (BitVec.ofNat 32 P), BitVec.toNat_ofNat] at ht
  unfold AllocprocTrace.forkRet at hr
  unfold PIDMAX at hr ⊢
  rcases hr with hr | hr
  · have hm := congrArg BitVec.toInt hr
    rw [ht, show (-1#64).toInt = -1 by decide] at hm
    split at hm <;> omega
  · rw [ht] at hr
    split at hr <;> omega

/-! ## §5 Fork rounds on the trace -/

/-- A trace step is a FORK round: an ecall exit whose effective number (at the
step's mask) is fork. -/
def AllocprocTrace.isFork : NiStep → Prop
  | .origin .. => False
  | .round secc _ _ _ _ _ x _ _ =>
    ∃ ep xg, exitView x = some (uecallScause, ep, xg) ∧ gprsNum secc xg = USYS_fork

/-- A step's answer: the `a0` its enter resumes with (`0` at an origin). -/
def AllocprocTrace.ans : NiStep → BitVec 64
  | .origin .. => 0#64
  | .round _ _ _ _ _ _ _ e _ => enterA0 e

/-- **A filed fork round answers `usysForkAns` of its citation, and the answer
has fork's row** (`niDetRow_fork`; the range from the round's `roundOkKeys`). -/
theorem AllocprocTrace.forkStep {h : List Obs} {F : List NiEntry} (hF : niOk h F) {q : NiInc}
    {s : NiStep} (hs : s ∈ utrace q h F) (hfk : AllocprocTrace.isFork s) :
    ∃ k ι, s.cite = some (k, ι) ∧ AllocprocTrace.ans s = usysForkAns ι ∧
      AllocprocTrace.forkRet (usysForkAns ι) := by
  obtain ⟨f, hfF, -, hfs⟩ := mem_utrace hs
  have hf := hF.1 f hfF
  match f, hf, hfs with
  | .origin j W0 .., _, hfs =>
    simp only [niStepOf] at hfs
    obtain ⟨e, -, rfl⟩ := Option.map_eq_some_iff.mp hfs
    exact hfk.elim
  | .round i j sc _ W W' c _ _, hf, hfs =>
    obtain ⟨-, ⟨x, hx, cpu, sa, rfl⟩, ⟨e, he, cpu', sa', ep', rfl, -⟩, hr, -, -, -, hcit, hdet, -⟩ := hf
    simp only [niStepOf, hx, he, Option.some.injEq] at hfs
    subst hfs
    obtain ⟨ep, xg, hxv, hnumf⟩ := hfk
    simp only [exitView, Option.some.injEq, Prod.mk.injEq] at hxv
    obtain ⟨hsc, -, hxg⟩ := hxv
    subst hxg
    have hf' : uvisNum (uvisRun W) = USYS_fork := (uvisNum_run_gprs W).trans hnumf
    obtain ⟨k, ι, rfl⟩ := niCiting_some hcit hsc (Or.inr (Or.inr (Or.inl hf')))
    have hans := niDetRow_fork hdet hsc hf'
    refine ⟨k, ι, rfl, hans, ?_⟩
    have hnum := gprsNum_tfGprs W (retPc (tfW W.tf tfEpcIdx))
    rw [hsc] at hr
    rcases uroundOk_ecall hr with ⟨hexec, -⟩ | ⟨-, r, ⟨hb1, -⟩, hm, -⟩
    · rw [hnum, hnumf] at hexec; exact absurd hexec (by decide)
    · have ha0 : gprsA0 (tfGprs W'.tf) = r := by
        rw [← gprList_tfResumeGpr0, gprsA0_gprList, hb1]; simp
      rw [hnum, hnumf] at hm
      unfold usysMemOk at hm
      rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide),
        if_neg (by decide), if_neg (by decide), if_pos rfl] at hm
      rw [← hans, ha0]
      exact hm.1

/-- **A successful fork's pick, from its answer**: in `[1, PIDMAX]`, or the
counter fallback at `2^32 - 1` answering `-1`. -/
theorem AllocprocTrace.pickOfAns (ι : UIota) (hok : forkOk ι)
    (hr : AllocprocTrace.forkRet (usysForkAns ι)) :
    (1 ≤ pidPick PIDMAX ι.pev ∧ pidPick PIDMAX ι.pev ≤ PIDMAX) ∨
      (pidPick PIDMAX ι.pev = nextOf PIDMAX ι.pev ∧ nextOf PIDMAX ι.pev = 2 ^ 32 - 1 ∧
        usysForkAns ι = -1#64) := by
  have hr' := hr
  unfold usysForkAns usysForkPid at hr'
  rw [if_pos hok] at hr'
  rcases AllocprocTrace.pickOfWord _ (AllocprocTrace.pidPick_le_two32 _) hr' with hw | hw
  · exact Or.inl hw
  · right
    rcases AllocprocTrace.pidPick_cases PIDMAX ι.pev (by decide) with hc | hc
    · exfalso; have := hc.2; rw [hw] at this; have h2 : PIDMAX = 1000 := rfl; omega
    · refine ⟨hc, hc.symm.trans hw, ?_⟩
      unfold usysForkAns usysForkPid
      rw [if_pos hok, hw]
      decide

/-! ## §6 THE THEOREM -/

/-- **THE ALLOCPROC SHADOW ON THE TRACE** (W1, D23, tie β): from the machine
off, never booted, with `fs.img` on its disk, every run's trace has a one-shot
NI filing `F` at which every fork round of every incarnation cites a prefix
`ι`, answers `usysForkAns ι` -- `pidPick PIDMAX ι.pev` (sign-extended) when
`forkOk ι`, `-1` otherwise --, the answer is `-1` or in `[1, PIDMAX]`, and on
success the pick is in `[1, PIDMAX]` or is the counter fallback `2^32 - 1`
(answering `-1`).  The plan's sharper bound needs the counter tie at the
citation (`pidPick_range`); see the header's deviations. -/
theorem allocprocTraceAns {hlc : HasLC}
    (g : GState) (Hgen0 : g.gen = 0) (Hpow : g.pow = false) (Hdisk : diskOf g.m.devs = fsImgDisk)
    (n : Nat) (κs : List Obs) (t2 : List Expr) (g2 : GState)
    (hsteps : ([Expr.power], g) -<κs>->ₜₚ^[n] (t2, g2)) :
    ∃ F, niOk κs F ∧ niOneShot κs F ∧ ∀ q : NiInc, ∀ s ∈ utrace q κs F, AllocprocTrace.isFork s →
      ∃ k ι, s.cite = some (k, ι) ∧ AllocprocTrace.ans s = usysForkAns ι ∧
        AllocprocTrace.forkRet (usysForkAns ι) ∧
        (forkOk ι →
          (1 ≤ pidPick PIDMAX ι.pev ∧ pidPick PIDMAX ι.pev ≤ PIDMAX) ∨
          (pidPick PIDMAX ι.pev = nextOf PIDMAX ι.pev ∧ nextOf PIDMAX ι.pev = 2 ^ 32 - 1 ∧
            usysForkAns ι = -1#64)) := by
  obtain ⟨-, F, hF, h1, -⟩ := xv6NiAdequacy (hlc := hlc) g Hgen0 Hpow Hdisk n κs t2 g2 hsteps
  refine ⟨F, hF, h1, fun q s hs hfk => ?_⟩
  obtain ⟨k, ι, hc, ha, hr⟩ := AllocprocTrace.forkStep hF hs hfk
  exact ⟨k, ι, hc, ha, hr, fun hok => AllocprocTrace.pickOfAns ι hok hr⟩

end Xv6

#print axioms Xv6.pidPick_range
#print axioms Xv6.pidPick_badHist
#print axioms Xv6.allocprocTraceAns
