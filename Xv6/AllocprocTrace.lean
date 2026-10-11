/-
**THE ALLOCPROC SHADOW ON THE TRACE** (weak-allocproc plan §C Stage 0, item
W1, rulings [R3.s1], [R6.5d], [R6.5d-alt]; D23; strengthened by W1b, W1-Q
RULED (c) [OWN.16]): what the closed NI theorem
(`LinkNiAdequacy.xv6NiAdequacy`) says about every fork round of a run from
the booting machine, read off at the filings its ledger witnesses, and the
range lemma for `PidEv.pidPick` the plan asks W1 to prove.

* **`pidPick_range`** ([R6.5d-alt]): from `cycAt`'s codomain and the counter
  tie `nextOf pidmax h ≤ pidmax` (the kernel's `PidLock.pidTie` keeps the
  stored counter there), the pick is in `[1, pidmax]`.  The tie is a
  HYPOTHESIS: on an arbitrary history it fails (`pidPick_badHist`: a `PAlloc`
  of an out-of-range pid steps the counter past `PIDMAX`, and with every
  candidate live `pidPick` falls back to the counter -- `UsysDet` deviation 6
  says the same).  `pidPick_range_of_wf` is the form at a history whose
  allocations are all in range.
* (W1b) **`pidHistWf_nextOf`**: a well-formed pid history (`PidEv.pidHistWf`,
  every allocation lawful at its prefix -- the invariant the pid ledger now
  keeps, `PidLock.pidLedger`) has its counter in range; **`pidHistWf_nodup`**:
  its live pids are pairwise distinct -- the multiset reading `liveList` (one
  entry per allocation not yet freed) has no duplicates and is the live set
  `liveOf`.
* **`allocprocTraceAns`**: from the machine off, never booted, with `fs.img`
  on its disk, every run's trace has a one-shot NI filing `F` at which every
  fork round of every incarnation cites a prefix `ι`, answers
  `usysForkAns ι` (the pid `pidPick PIDMAX ι.pev` when `forkOk ι`, else `-1`)
  -- tie β (D11) --, its answer is `-1` or in `[1, PIDMAX]` (the kernel's
  row, `usysMemOk`'s fork entry, carried by the round's `roundOkKeys`), and
  (W1b, through the filing's `NiLedger.niForkTie`, supplied by the kernel's
  fork arm from the ledgers' receipts) the cited prefix's ledger ties: the
  pick in `[1, PIDMAX]` (the counter tie at the citation), on success not
  live at the cited prefix (distinct from every live pid), the cited pid
  prefix's live pids pairwise distinct, and the decisive allocator event
  the pool's state (`poolEmpty` before a `KNull`, not before a `KAlloc`).
  (W1b follow-up) The filing's CHAIN `niChain F (niHist F)` (the NI
  conclusion's third conjunct, `NiAdequacy.xv6NiPhi`) is exported too, and
  every fork round's citation is below its era's joined history
  `niHist F k` (`niBelow`): the per-round facts are about prefixes of ONE
  pid / allocator history per era, not about independently fabricable
  per-round prefixes.  `AllocprocTrace.forkPev_comparable`: two fork rounds
  of one era cite prefix-comparable pid histories.
* (W1b follow-up, [OWN.28] (A)) **`AllocprocTrace.forkHist_spec`**: era
  `k`'s FORK history `AllocprocTrace.forkHist F k` (the longest pid prefix
  a fork round of era `k` cites) is a prefix of `(niHist F k).pev`, well
  formed (`pidHistWf PIDMAX`), contains every era-`k` fork citation's pid
  prefix, and its live pids are pairwise distinct -- "live pids pairwise
  distinct" ACROSS the era's forks; `allocprocTraceAns` exports it.

## Deviations from the plan's statement ([R6.5d])

1. The interim W1 form's fallback disjunct (`pidPick = nextOf = 2^32 - 1 ∧
   ans = -1`, PROGRESS-W1) is GONE (W1b): the counter tie is exported at the
   citation, so the pick's range holds at every cited fork prefix -- stated
   unconditionally (it implies the plan's `forkOk ι → …`).  Remark, NOT a
   guarantee of this theorem: the kernel's failing fork arms
   (`SyscallArmsFork.syscArmFork_evNeg`'s `KNull` / `SFull` branches) build
   their citation from `UIota.boot`, so in the runs the kernel produces a
   `-1` fork cites the empty pid prefix (pick `1`); the trace-level
   statement only knows what `usysForkTie` and fork's row say of `ι`.
2. `allocprocTraceAns`, not `allocprocTrace`: the landed name is kept
   (plan §A "Names"), strengthened in place.
3. `pidHistWf` takes the bound as an explicit parameter (`PidEv`'s
   convention for `nextOf`/`pidPick`), instantiated at `PIDMAX`.
4. (W1b follow-up, ruled (A) [OWN.28]) "live pids pairwise distinct" is
   stated for the era's FORK history `AllocprocTrace.forkHist F k` (the
   join of the pid prefixes era `k`'s fork rounds cite), not for the era's
   joined history `(niHist F k).pev`: the latter's well-formedness is NOT
   derivable from the NI conclusion -- `niHist` joins ALL citations, and
   only a fork round's filing (`NiLedger.niForkTie`) constrains its cited
   pid prefix (the uptime / wait / sbrk / write rows never read `ι.pev`).
   Not covered: pid-ledger events after the last fork citation of the era.

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

/-- The counter is at most `pidmax` at a history whose allocations are all at
most `pidmax`. -/
theorem AllocprocTrace.nextOf_le_of_wf (pidmax : Nat) (h : List Pev) (hp : 0 < pidmax)
    (hwf : ∀ a p, Pev.PAlloc a p ∈ h → p.toNat ≤ pidmax) : nextOf pidmax h ≤ pidmax :=
  (AllocprocTrace.nextOf_bounds pidmax pidmax h hp
    (fun a p hm hne => by have := hwf a p hm; omega)).2

/-- Every allocation of a well-formed history is at most `pidmax`. -/
theorem AllocprocTrace.pidHistWf_le (pidmax : Nat) (h : List Pev) (hw : pidHistWf pidmax h) :
    ∀ a p, Pev.PAlloc a p ∈ h → p.toNat ≤ pidmax := by
  intro a p hm
  obtain ⟨n, hn⟩ := List.mem_iff_getElem?.mp hm
  exact (hw n a p hn).2.2.1

/-- **THE COUNTER TIE, FROM THE HISTORY** (W1b): a well-formed history's
counter is at most `pidmax`. -/
theorem pidHistWf_nextOf (pidmax : Nat) (h : List Pev) (hp : 0 < pidmax) (hw : pidHistWf pidmax h) :
    nextOf pidmax h ≤ pidmax :=
  AllocprocTrace.nextOf_le_of_wf pidmax h hp (AllocprocTrace.pidHistWf_le pidmax h hw)

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

/-! ## §3 The tie is needed: a history whose pick is out of range

(W1b) Such a history is not well formed (its last allocation is out of
range), so the filing's `pidHistWf` at every cited fork prefix excludes it. -/

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

/-! ## §3b LIVE PIDS PAIRWISE DISTINCT (W1b)

`liveOf` is a SET, so "distinct" is vacuous on it (review [R1.3]); the
meaningful reading counts: one entry per allocation not yet freed, a free
erasing one entry.  On a well-formed history that list has no duplicates
and is the live set. -/

/-- One event's step on the live multiset. -/
def AllocprocTrace.liveListStep (l : List Nat) : Pev → List Nat
  | .PAlloc _ p => l ++ [p.toNat]
  | .PFree _ p => l.erase p.toNat

/-- The live pids, one entry per allocation not yet freed. -/
def AllocprocTrace.liveList (h : List Pev) : List Nat := h.foldl AllocprocTrace.liveListStep []

theorem AllocprocTrace.liveList_snoc (h : List Pev) (e : Pev) :
    AllocprocTrace.liveList (h ++ [e]) = AllocprocTrace.liveListStep (AllocprocTrace.liveList h) e := by
  unfold AllocprocTrace.liveList; rw [List.foldl_append]; rfl

/-- **LIVE PIDS PAIRWISE DISTINCT** (W1b): on a well-formed history the live
multiset has no duplicates, and its members are exactly the live set. -/
theorem pidHistWf_nodup (pidmax : Nat) (h : List Pev) (hw : pidHistWf pidmax h) :
    (AllocprocTrace.liveList h).Nodup ∧ ∀ z : Nat, z ∈ AllocprocTrace.liveList h ↔ liveOf h (z : Int) := by
  obtain ⟨l, rfl⟩ : ∃ l, h = l.reverse := ⟨h.reverse, (List.reverse_reverse h).symm⟩
  induction l with
  | nil =>
    refine ⟨List.nodup_nil, fun z => ?_⟩
    simp [AllocprocTrace.liveList, liveOf]
  | cons e l ih =>
    rw [List.reverse_cons] at hw ⊢
    obtain ⟨hw0, hlaw⟩ := pidHistWf_snoc_inv pidmax _ e hw
    obtain ⟨hnd, hmem⟩ := ih hw0
    rw [AllocprocTrace.liveList_snoc, liveOf_snoc]
    cases e with
    | PAlloc a p =>
      have hnl : ¬ liveOf l.reverse (p.toNat : Int) := (hlaw a p rfl).2.2.2
      refine ⟨List.nodup_append.mpr ⟨hnd, List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩, ?_⟩,
        fun z => ?_⟩
      · intro x hx y hy hxy
        rw [List.mem_singleton] at hy
        subst hy hxy
        exact hnl ((hmem _).mp hx)
      · simp only [AllocprocTrace.liveListStep, liveStep, List.mem_append, List.mem_singleton, hmem,
          Int.ofNat_inj]
        exact Or.comm
    | PFree a p =>
      refine ⟨hnd.erase _, fun z => ?_⟩
      simp only [AllocprocTrace.liveListStep, liveStep, hnd.mem_erase_iff, hmem, ne_eq, Int.ofNat_inj]
      exact And.comm

/-! ## §4 Fork's row -/

/-- fork's row in the kernel's table (`usysMemOk`'s fork entry). -/
def AllocprocTrace.forkRet (r : BitVec 64) : Prop := r = -1#64 ∨ (1 ≤ r.toInt ∧ r.toInt ≤ PIDMAX)

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

/-- (W1b follow-up, [OWN.28] (A)) A filing's FORK citation of era `k`: the
pid prefix a fork ecall round of era `k` cites (`none` for every other
filing). -/
def AllocprocTrace.forkCite (k : Nat) : NiEntry → Option (List Pev)
  | .round _ _ sc _ W _ (some (k', ι)) _ _ =>
    if k' = k ∧ sc = uecallScause ∧ uvisNum (uvisRun W) = USYS_fork then some ι.pev else none
  | _ => none

/-- **A filed fork round answers `usysForkAns` of its citation, the answer
has fork's row** (`niDetRow_fork`; the range from the round's `roundOkKeys`),
**and the citation carries the ledger ties** (W1b: the filing's
`niForkTie`). -/
theorem AllocprocTrace.forkStep {h : List Obs} {F : List NiEntry} (hF : niOk h F) {q : NiInc}
    {s : NiStep} (hs : s ∈ utrace q h F) (hfk : AllocprocTrace.isFork s) :
    ∃ k ι, s.cite = some (k, ι) ∧ AllocprocTrace.ans s = usysForkAns ι ∧
      AllocprocTrace.forkRet (usysForkAns ι) ∧ usysForkTie ι ∧
      ∃ f ∈ F, AllocprocTrace.forkCite k f = some ι.pev := by
  obtain ⟨f, hfF, -, hfs⟩ := mem_utrace hs
  have hf := hF.1 f hfF
  match f, hfF, hf, hfs with
  | .origin j W0 .., _, _, hfs =>
    simp only [niStepOf] at hfs
    obtain ⟨e, -, rfl⟩ := Option.map_eq_some_iff.mp hfs
    exact hfk.elim
  | .round i j sc _ W W' c _ _, hfF, hf, hfs =>
    obtain ⟨-, ⟨x, hx, cpu, sa, rfl⟩, ⟨e, he, cpu', sa', ep', rfl, -⟩, hr, -, -, -, hcit, hdet, -, -, -, -,
      htie⟩ := hf
    simp only [niStepOf, hx, he, Option.some.injEq] at hfs
    subst hfs
    obtain ⟨ep, xg, hxv, hnumf⟩ := hfk
    simp only [exitView, Option.some.injEq, Prod.mk.injEq] at hxv
    obtain ⟨hsc, -, hxg⟩ := hxv
    subst hxg
    have hf' : uvisNum (uvisRun W) = USYS_fork := (uvisNum_run_gprs W).trans hnumf
    obtain ⟨k, ι, rfl⟩ := niCiting_some hcit hsc (Or.inr (Or.inr (Or.inl hf')))
    have hans := niDetRow_fork hdet hsc hf'
    refine ⟨k, ι, rfl, hans, ?_, htie hsc hf', _, hfF, by simp [AllocprocTrace.forkCite, hsc, hf']⟩
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

/-! ## §5b THE ERA'S FORK HISTORY (W1b follow-up, [OWN.28] (A))

`niHist F k` joins ALL of era `k`'s citations, and only fork rounds file
`pidHistWf` at theirs (`NiLedger.niForkTie`), so the joined pid history's
well-formedness is not derivable.  The FORK-joined one is: the longest of
the pid prefixes era `k`'s fork rounds cite.  Under the chain all of them
are prefixes of `(niHist F k).pev`, so they are pairwise comparable, the
fold picks the longest, and every one is a prefix of it. -/

/-- **The era's fork history**: the `niLonger` join of the pid prefixes
era `k`'s fork rounds cite, from `[]`. -/
def AllocprocTrace.forkHist (F : List NiEntry) (k : Nat) : List Pev :=
  (F.filterMap (AllocprocTrace.forkCite k)).foldl niLonger []

/-- The `niLonger` fold of lists that are all prefixes of `B` and satisfy
`P` (closed under the choice `niLonger` makes): the result is a prefix of
`B`, satisfies `P`, extends the start and every folded list. -/
theorem AllocprocTrace.foldLonger_spec {α : Type _} {B : List α} {P : List α → Prop} :
    ∀ (L : List (List α)) (G : List α), G <+: B → P G → (∀ p ∈ L, p <+: B ∧ P p) →
      L.foldl niLonger G <+: B ∧ P (L.foldl niLonger G) ∧ G <+: L.foldl niLonger G ∧
        ∀ p ∈ L, p <+: L.foldl niLonger G
  | [], G, hG, hP, _ => ⟨hG, hP, List.prefix_refl G, fun _ hp => absurd hp List.not_mem_nil⟩
  | p :: L, G, hG, hP, hL => by
    rw [List.foldl_cons]
    obtain ⟨hpB, hpP⟩ := hL p List.mem_cons_self
    have hc := List.prefix_or_prefix_of_prefix hG hpB
    have hP' : P (niLonger G p) := by unfold niLonger; split <;> assumption
    obtain ⟨g1, g2, g3, g4⟩ := AllocprocTrace.foldLonger_spec L (niLonger G p) (niLonger_le hG hpB) hP'
      (fun p' hp' => hL p' (List.mem_cons_of_mem _ hp'))
    refine ⟨g1, g2, (niLonger_left hc).trans g3, fun p' hp' => ?_⟩
    rcases List.mem_cons.mp hp' with rfl | hp'
    · exact (niLonger_right hc).trans g3
    · exact g4 p' hp'

/-- A fork citation of a valid chained filing: below the era's joined pid
history, and well formed (the filing's `niForkTie`). -/
theorem AllocprocTrace.forkCite_facts {h : List Obs} {F : List NiEntry} (hF : niOk h F)
    (hC : niChain F (niHist F)) {k : Nat} {f : NiEntry} (hf : f ∈ F) {p : List Pev}
    (hp : AllocprocTrace.forkCite k f = some p) : p <+: (niHist F k).pev ∧ pidHistWf PIDMAX p := by
  cases f with
  | origin => simp [AllocprocTrace.forkCite] at hp
  | round i j sc Wr W W' c γ kk =>
    cases c with
    | none => simp [AllocprocTrace.forkCite] at hp
    | some c =>
      obtain ⟨k', ι⟩ := c
      simp only [AllocprocTrace.forkCite] at hp
      split at hp
      · rename_i hcond
        obtain ⟨rfl, hsc, hnum⟩ := hcond
        cases hp
        have htie := (hF.1 _ hf).2.2.2.2.2.2.2.2.2.2.2.2.2 hsc hnum
        exact ⟨(hC _ hf k' ι rfl).1, htie.1⟩
      · exact absurd hp (by simp)

/-- **THE ERA'S FORK HISTORY** ([OWN.28] (A)): at a valid chained filing,
era `k`'s fork history is a prefix of its joined pid history, well formed
(`pidHistWf PIDMAX`), contains every pid prefix a fork round of era `k`
cites, and its live pids are pairwise distinct (`liveList` has no
duplicates and is `liveOf`). -/
theorem AllocprocTrace.forkHist_spec {h : List Obs} {F : List NiEntry} (hF : niOk h F)
    (hC : niChain F (niHist F)) (k : Nat) :
    AllocprocTrace.forkHist F k <+: (niHist F k).pev ∧ pidHistWf PIDMAX (AllocprocTrace.forkHist F k) ∧
      (∀ f ∈ F, ∀ p, AllocprocTrace.forkCite k f = some p → p <+: AllocprocTrace.forkHist F k) ∧
      (AllocprocTrace.liveList (AllocprocTrace.forkHist F k)).Nodup ∧
      (∀ z : Nat, z ∈ AllocprocTrace.liveList (AllocprocTrace.forkHist F k) ↔
        liveOf (AllocprocTrace.forkHist F k) (z : Int)) := by
  obtain ⟨g1, g2, -, g4⟩ := AllocprocTrace.foldLonger_spec (B := (niHist F k).pev)
    (P := pidHistWf PIDMAX) (F.filterMap (AllocprocTrace.forkCite k)) [] (List.nil_prefix)
    (pidHistWf_nil PIDMAX) (fun p hp => by
      obtain ⟨f, hf, hfp⟩ := List.mem_filterMap.mp hp
      exact AllocprocTrace.forkCite_facts hF hC hf hfp)
  obtain ⟨hnd, hmem⟩ := pidHistWf_nodup PIDMAX _ g2
  exact ⟨g1, g2, fun f hf p hfp => g4 p (List.mem_filterMap.mpr ⟨f, hf, hfp⟩), hnd, hmem⟩

/-! ## §6 THE THEOREM -/

/-- **THE ALLOCPROC SHADOW ON THE TRACE** (W1, D23, tie β; W1b): from the
machine off, never booted, with `fs.img` on its disk, every run's trace has a
one-shot NI filing `F` at which every fork round of every incarnation cites
a prefix `ι` and
* answers `usysForkAns ι` -- `pidPick PIDMAX ι.pev` (sign-extended) when
  `forkOk ι`, `-1` otherwise --, the answer `-1` or in `[1, PIDMAX]`;
* the pick is in `[1, PIDMAX]`, the cited counter `nextOf PIDMAX ι.pev` too;
* on success the pick is not live at the cited pid prefix (the child's pid
  is distinct from every live pid);
* the cited pid prefix is well formed (`pidHistWf`) and its live pids are
  pairwise distinct (`liveList` has no duplicates and is `liveOf`);
* the cited allocator prefix's decisive event is the pool's state: the
  pool was empty before a `KNull` and non-empty before a `KAlloc`;
* (W1b follow-up) the filing is a chain (`niChain F (niHist F)`) and the
  citation is below its era's joined history `niHist F k`;
* ([OWN.28] (A)) every era's fork history `AllocprocTrace.forkHist F k` is
  a prefix of `(niHist F k).pev`, well formed, with pairwise distinct live
  pids, and the round's cited pid prefix is a prefix of it. -/
theorem allocprocTraceAns {hlc : HasLC}
    (g : GState) (Hgen0 : g.gen = 0) (Hpow : g.pow = false) (Hdisk : diskOf g.m.devs = fsImgDisk)
    (n : Nat) (κs : List Obs) (t2 : List Expr) (g2 : GState)
    (hsteps : ([Expr.power], g) -<κs>->ₜₚ^[n] (t2, g2)) :
    ∃ F, niOk κs F ∧ niOneShot κs F ∧ niChain F (niHist F) ∧
      (∀ k, AllocprocTrace.forkHist F k <+: (niHist F k).pev ∧
        pidHistWf PIDMAX (AllocprocTrace.forkHist F k) ∧
        (AllocprocTrace.liveList (AllocprocTrace.forkHist F k)).Nodup ∧
        (∀ z : Nat, z ∈ AllocprocTrace.liveList (AllocprocTrace.forkHist F k) ↔
          liveOf (AllocprocTrace.forkHist F k) (z : Int))) ∧
      ∀ q : NiInc, ∀ s ∈ utrace q κs F, AllocprocTrace.isFork s →
      ∃ k ι, s.cite = some (k, ι) ∧ niBelow ι (niHist F k) ∧ ι.pev <+: AllocprocTrace.forkHist F k ∧
        AllocprocTrace.ans s = usysForkAns ι ∧
        AllocprocTrace.forkRet (usysForkAns ι) ∧
        (1 ≤ pidPick PIDMAX ι.pev ∧ pidPick PIDMAX ι.pev ≤ PIDMAX) ∧ nextOf PIDMAX ι.pev ≤ PIDMAX ∧
        (forkOk ι → ¬ liveOf ι.pev (pidPick PIDMAX ι.pev : Int)) ∧
        pidHistWf PIDMAX ι.pev ∧ (AllocprocTrace.liveList ι.pev).Nodup ∧
        (∀ z : Nat, z ∈ AllocprocTrace.liveList ι.pev ↔ liveOf ι.pev (z : Int)) ∧
        (ι.kNull → poolEmpty ι.kev.dropLast) ∧ (ι.kOk → ¬ poolEmpty ι.kev.dropLast) := by
  obtain ⟨-, F, hF, h1, hC, -⟩ := xv6NiAdequacy (hlc := hlc) g Hgen0 Hpow Hdisk n κs t2 g2 hsteps
  refine ⟨F, hF, h1, hC, fun k => ?_, fun q s hs hfk => ?_⟩
  · obtain ⟨g1, g2, -, g4, g5⟩ := AllocprocTrace.forkHist_spec hF hC k
    exact ⟨g1, g2, g4, g5⟩
  obtain ⟨k, ι, hc, ha, hr, ⟨hwf, hnl, hkn, hko⟩, f', hf'F, hf'c⟩ := AllocprocTrace.forkStep hF hs hfk
  have hfh := (AllocprocTrace.forkHist_spec hF hC k).2.2.1 f' hf'F _ hf'c
  obtain ⟨f, hfF, -, hfs⟩ := mem_utrace hs
  have hbl : niBelow ι (niHist F k) := hC f hfF k ι ((niStepOf_cite hfs).symm.trans hc)
  have hnx := pidHistWf_nextOf PIDMAX ι.pev (by decide) hwf
  obtain ⟨hnd, hmem⟩ := pidHistWf_nodup PIDMAX ι.pev hwf
  exact ⟨k, ι, hc, hbl, hfh, ha, hr, pidPick_range PIDMAX ι.pev (by decide) hnx, hnx, hnl, hwf, hnd, hmem, hkn,
    hko⟩

/-- (W1b follow-up) Two citations below one era's joined history cite
prefix-comparable pid histories: one fork round's cited pid prefix extends
the other's. -/
theorem AllocprocTrace.forkPev_comparable {F : List NiEntry} {k : Nat} {ι ι' : UIota}
    (h : niBelow ι (niHist F k)) (h' : niBelow ι' (niHist F k)) : ι.pev <+: ι'.pev ∨ ι'.pev <+: ι.pev :=
  List.prefix_or_prefix_of_prefix h.1 h'.1

end Xv6

#print axioms Xv6.pidPick_range
#print axioms Xv6.pidPick_badHist
#print axioms Xv6.pidHistWf_nodup
#print axioms Xv6.AllocprocTrace.forkHist_spec
#print axioms Xv6.allocprocTraceAns
