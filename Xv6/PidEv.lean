/-
The PURE event vocabulary of the pid ledger (the Rocq `PidEv.v`, commit
d66e99d0d, NI-LEDGER-REST W1).

Every pid allocation and release the kernel performs under `pid_lock`
appends one ACTOR-LABELLED event to a ghost history `h : List Pev`:

  `PAlloc a p` -- allocproc's inlined allocpid, run by actor `a` (the
                  hart's current proc word, `KCtx.proc`), handed out pid `p`,
  `PFree a p`  -- freeproc's `p->pid = 0`, run by actor `a`, released pid `p`.

The history is appended at the END (`h ++ [e]`), so its readings are LEFT
FOLDS / counts, and the snoc equations are `List.foldl_append` /
`List.countP_append` one-liners:

  `liveOf h`          -- the live set: allocs insert the pid's value, frees
                         remove it;
  `ownAllocs act h`   -- (NI M4 pids) the allocations actor `act` made: its
                         own fork count, which with its slot fixes the pid
                         the partition hands it (`pidPickS`).

(The pre-M4 kernel's global counter `nextOf` and the cyclic scan's
`pidPick` went with the scan: the pid kernel has neither.)  No Iris, no
ghost state, no gname.

Design: `claude-notes/design/ni-pid-ledger.md` (§2 D1, §3 W1).

## Deviations from Rocq

1. Names: `pev`/`pev_pid`/`live_of` are
   `Pev`/`Pev.pid`/`liveOf` (`pev_actor` is not ported: nothing
   uses it); the constructors keep Rocq's spelling (`Pev.PAlloc`,
   `Pev.PFree`).  `mword 64` / `mword 32` are `BitVec 64` / `BitVec 32`.
2. **The live set is a PREDICATE on `Int`** (`Int → Prop`; Rocq: `gset Z`):
   it is compared with the pid register's domain, which in this tree is
   `PartialMap.dom R : Int → Prop` over `R : IntMapF GName` (the register
   is keyed at `(pid.toNat : Int)`, `SlotGen` deviation 1).  `{[x]} ∪ S`
   is `fun k => k = x ∨ S k`, `S ∖ {[x]}` is `fun k => S k ∧ k ≠ x`, `∅` is
   `fun _ => False`; equalities are of functions (`funext`/`propext`).
3. (NI M4 pids) Rocq's counter `next_of` is gone with the scan; the
   partition's reading is the own count `ownAllocs` (a `Nat`).
4. No `Countable` instance: iris-lean's `MonoList` camera is over
   `DiscreteO Pev` and asks nothing of the element type (as `KallocEv`
   deviation 2).  `DecidableEq` is derived.
-/
import Xv6.ProcGeom

namespace Xv6

/-! ## 1. The events -/

/-- One pid call, labelled by its actor (Rocq `pev`). -/
inductive Pev where
  /-- allocproc's inlined allocpid, run by `act`, handed out `pid` -/
  | PAlloc (act : BitVec 64) (pid : BitVec 32)
  /-- freeproc's `p->pid = 0`, run by `act`, released `pid` -/
  | PFree (act : BitVec 64) (pid : BitVec 32)
  deriving DecidableEq, Repr

/-- The pid the event carries (Rocq `pev_pid`). -/
def Pev.pid : Pev → BitVec 32
  | .PAlloc _ p | .PFree _ p => p

/-! ## 2. The live set, as a left fold over the history -/

/-- One event's step on the live set (Rocq `live_step`). -/
def liveStep (S : Int → Prop) : Pev → Int → Prop
  | .PAlloc _ p => fun k => k = (p.toNat : Int) ∨ S k
  | .PFree _ p => fun k => S k ∧ k ≠ (p.toNat : Int)

/-- The live set after `h` (Rocq `live_of`; deviation 2). -/
def liveOf (h : List Pev) : Int → Prop := h.foldl liveStep (fun _ => False)

/-! ## 3. The snoc equations -/

theorem liveOf_snoc (h : List Pev) (e : Pev) : liveOf (h ++ [e]) = liveStep (liveOf h) e := by
  unfold liveOf; rw [List.foldl_append]; rfl

theorem liveOf_snoc_alloc (h : List Pev) (a : BitVec 64) (p : BitVec 32) :
    liveOf (h ++ [.PAlloc a p]) = fun k => k = (p.toNat : Int) ∨ liveOf h k := by
  rw [liveOf_snoc]; rfl

theorem liveOf_snoc_free (h : List Pev) (a : BitVec 64) (p : BitVec 32) :
    liveOf (h ++ [.PFree a p]) = fun k => liveOf h k ∧ k ≠ (p.toNat : Int) := by
  rw [liveOf_snoc]; rfl

/-! ## 5. The rewrite forms the invariant's tie uses -/

theorem liveOf_snoc_alloc_dom (S : Int → Prop) (h : List Pev) (a : BitVec 64) (p : BitVec 32)
    (hs : liveOf h = S) :
    liveOf (h ++ [.PAlloc a p]) = fun k => k = (p.toNat : Int) ∨ S k := by
  rw [liveOf_snoc_alloc, hs]

theorem liveOf_snoc_free_dom (S : Int → Prop) (h : List Pev) (a : BitVec 64) (p : BitVec 32)
    (hs : liveOf h = S) :
    liveOf (h ++ [.PFree a p]) = fun k => S k ∧ k ≠ (p.toNat : Int) := by
  rw [liveOf_snoc_free, hs]

/-! ## 6. THE PARTITION (NI M4 pids P-0; design noninterference.md "M4 pids design" F4/F7)

The pid kernel (`verified-quota` 975109bc) PARTITIONS pids by the parent's
slot: slot `j` hands its children `j + NPROC`, `j + 2·NPROC`, ... from a
per-slot counter (`p->npid`) that never wraps and never resets; `init`
(allocproc with no current process) is 1; a slot that has created `PIDQ`
children forks no more (allocpid's cap).  So the pid an allocation by actor
`act` hands out after history `h` is a function of the actor and ITS OWN
allocation count (`pidPickS`), and it is FRESH on a well-formed history
(`pidPickS_fresh`: a pure lemma, no scan). -/

/-- A slot's pid quota: the children it may ever create (`PIDMAX = 63 + 64 · PIDQ`). -/
def PIDQ : Nat := 2 ^ 25 - 1

/-- Is `e` an allocation by `act`? -/
def isAllocOf (act : BitVec 64) : Pev → Bool
  | .PAlloc a _ => a == act
  | .PFree _ _ => false

/-- The allocations actor `act` made in `h`: its OWN fork count. -/
def ownAllocs (act : BitVec 64) (h : List Pev) : Nat := h.countP (isAllocOf act)

/-- **THE PARTITION**: the pid the kernel is bound to give actor `act` after `h`. -/
def pidPickS (act : BitVec 64) (h : List Pev) : Nat :=
  if act = 0#64 then 1 else slotOf act + NPROC * (ownAllocs act h + 1)

/-- An actor word the kernel can hold: no process (`0`, the boot hart before
the scheduler) or a slot's address. -/
def pevActOk (a : BitVec 64) : Prop := a = 0#64 ∨ ∃ j, j < NPROC ∧ a = procAddr j

/-- A WELL-FORMED history: every allocation is the partition's at its prefix,
by an actor the kernel can hold. -/
def pevWf (h : List Pev) : Prop :=
  ∀ i a p, h[i]? = some (.PAlloc a p) → p.toNat = pidPickS a (h.take i) ∧ pevActOk a

theorem ownAllocs_nil (act : BitVec 64) : ownAllocs act [] = 0 := rfl

theorem ownAllocs_snoc_alloc_self (act : BitVec 64) (h : List Pev) (p : BitVec 32) :
    ownAllocs act (h ++ [.PAlloc act p]) = ownAllocs act h + 1 := by
  unfold ownAllocs; rw [List.countP_append]; simp [isAllocOf]

theorem ownAllocs_snoc_alloc_other (act a : BitVec 64) (h : List Pev) (p : BitVec 32) (hne : a ≠ act) :
    ownAllocs act (h ++ [.PAlloc a p]) = ownAllocs act h := by
  unfold ownAllocs; rw [List.countP_append]; simp [isAllocOf, hne]

theorem ownAllocs_snoc_free (act a : BitVec 64) (h : List Pev) (p : BitVec 32) :
    ownAllocs act (h ++ [.PFree a p]) = ownAllocs act h := by
  unfold ownAllocs; rw [List.countP_append]; simp [isAllocOf]

theorem ownAllocs_take_le (act : BitVec 64) (h : List Pev) (i : Nat) :
    ownAllocs act (h.take i) ≤ ownAllocs act h := by
  unfold ownAllocs
  exact (List.take_sublist i h).countP_le

/-- An allocation by `act` at index `i` is counted strictly below the whole. -/
theorem ownAllocs_take_lt (act : BitVec 64) (h : List Pev) (i : Nat) (p : BitVec 32)
    (hi : h[i]? = some (.PAlloc act p)) : ownAllocs act (h.take i) < ownAllocs act h := by
  have hlt : i < h.length := (List.getElem?_eq_some_iff.1 hi).1
  have he : h[i] = .PAlloc act p := (List.getElem?_eq_some_iff.1 hi).2
  have hsplit : h = h.take i ++ h[i] :: h.drop (i + 1) := by
    rw [← List.drop_eq_getElem_cons hlt, List.take_append_drop]
  have hc : ownAllocs act h = ownAllocs act (h.take i) + 1 + ownAllocs act (h.drop (i + 1)) := by
    conv => lhs; rw [hsplit]
    unfold ownAllocs
    rw [List.countP_append, List.countP_cons, he]
    simp only [isAllocOf, beq_self_eq_true, if_true]
    omega
  omega

/-- (NI M4 pids P-1) A canonical list of `n` allocations by `act` counts `n`:
the own count is all `UsysDet.UIota.ledP` keeps of the pid prefix. -/
theorem ownAllocs_replicate (act : BitVec 64) (n : Nat) (p : BitVec 32) :
    ownAllocs act (List.replicate n (.PAlloc act p)) = n := by
  unfold ownAllocs; rw [List.countP_replicate]; simp [isAllocOf]

/-- (NI M4 pids P-1) The partition's pick reads the history through the own
count only. -/
theorem pidPickS_congr {act : BitVec 64} {h h' : List Pev} (hc : ownAllocs act h = ownAllocs act h') :
    pidPickS act h = pidPickS act h' := by
  unfold pidPickS; rw [hc]

theorem pevWf_nil : pevWf [] := by
  intro i a p h; simp at h

theorem pevWf_snoc_free (h : List Pev) (a : BitVec 64) (p : BitVec 32) (hw : pevWf h) :
    pevWf (h ++ [.PFree a p]) := by
  intro i b q hi
  by_cases hl : i < h.length
  · rw [List.getElem?_append_left hl] at hi
    rw [List.take_append_of_le_length (Nat.le_of_lt hl)]
    exact hw i b q hi
  · rw [List.getElem?_append_right (by omega)] at hi
    rcases hn : i - h.length with _ | n
    · rw [hn] at hi; simp at hi
    · rw [hn] at hi; simp at hi

theorem pevWf_snoc_alloc (h : List Pev) (a : BitVec 64) (p : BitVec 32) (hw : pevWf h)
    (hp : p.toNat = pidPickS a h) (ha : pevActOk a) : pevWf (h ++ [.PAlloc a p]) := by
  intro i b q hi
  by_cases hl : i < h.length
  · rw [List.getElem?_append_left hl] at hi
    rw [List.take_append_of_le_length (Nat.le_of_lt hl)]
    exact hw i b q hi
  · rw [List.getElem?_append_right (by omega)] at hi
    rcases hn : i - h.length with _ | n
    · rw [hn] at hi
      simp only [List.getElem?_cons_zero, Option.some.injEq, Pev.PAlloc.injEq] at hi
      obtain ⟨rfl, rfl⟩ := hi
      have hi' : i = h.length := by omega
      subst hi'
      rw [List.take_left]
      exact ⟨hp, ha⟩
    · rw [hn] at hi; simp at hi

theorem liveOf_alloc_aux (h : List Pev) : ∀ (S : Int → Prop) (z : Int), h.foldl liveStep S z →
    S z ∨ ∃ (i : Nat) (a : BitVec 64) (p : BitVec 32), h[i]? = some (Pev.PAlloc a p) ∧ z = (p.toNat : Int) := by
  induction h with
  | nil => intro S z hz; exact Or.inl hz
  | cons e t ih =>
    intro S z hz
    rcases ih _ z hz with h1 | ⟨i, a, p, hi, rfl⟩
    · cases e with
      | PAlloc a p =>
        rcases h1 with rfl | h1
        · exact Or.inr ⟨0, a, p, rfl, rfl⟩
        · exact Or.inl h1
      | PFree a p => exact Or.inl h1.1
    · exact Or.inr ⟨i + 1, a, p, by simpa using hi, rfl⟩

/-- A pid is live only if some allocation handed it out. -/
theorem liveOf_alloc (h : List Pev) (z : Int) (hz : liveOf h z) :
    ∃ (i : Nat) (a : BitVec 64) (p : BitVec 32), h[i]? = some (Pev.PAlloc a p) ∧ z = (p.toNat : Int) :=
  (liveOf_alloc_aux h _ z hz).resolve_left id

/-- **FRESHNESS**: on a well-formed history the partition's pick for a slot's
actor was never handed out (every earlier pid of the same slot is smaller,
every other slot's has a different residue mod `NPROC`, init's is `1`), so it
is not live, and it is not init's `1`. -/
theorem pidPickS_fresh {h : List Pev} {act : BitVec 64} {j : Nat} (hw : pevWf h) (hj : j < NPROC)
    (ha : act = procAddr j) :
    ¬ liveOf h (pidPickS act h : Int) ∧ pidPickS act h ≠ 1 := by
  have hne : act ≠ 0#64 := by rw [ha]; exact procAddr_nonzero hj
  have hpk : pidPickS act h = j + NPROC * (ownAllocs act h + 1) := by
    unfold pidPickS; rw [if_neg hne, ha, slotOf_procAddr hj]
  refine ⟨fun hl => ?_, by rw [hpk]; unfold NPROC; omega⟩
  obtain ⟨i, b, q, hi, hz⟩ := liveOf_alloc h _ hl
  obtain ⟨hq, hb⟩ := hw i b q hi
  have hzq : pidPickS act h = q.toNat := by exact_mod_cast hz
  rcases hb with rfl | ⟨j', hj', rfl⟩
  · unfold pidPickS at hq; rw [if_pos rfl] at hq
    rw [hpk] at hzq; unfold NPROC at hzq; omega
  · have hq' : q.toNat = j' + NPROC * (ownAllocs (procAddr j') (h.take i) + 1) := by
      unfold pidPickS at hq; rw [if_neg (procAddr_nonzero hj'), slotOf_procAddr hj'] at hq; exact hq
    rw [hpk, hq'] at hzq
    unfold NPROC at hzq hj hj'
    have hjj : j = j' := by omega
    subst hjj
    have hlt := ownAllocs_take_lt (procAddr j) h i q hi
    rw [← ha] at hzq hlt
    omega

/-- Under the quota the pick is a positive `int`: at most `PIDMAX`. -/
theorem pidPickS_le {h : List Pev} {act : BitVec 64} {j : Nat} (hj : j < NPROC) (ha : act = procAddr j)
    (hc : ownAllocs act h < PIDQ) : pidPickS act h ≤ PIDMAX := by
  unfold pidPickS
  rw [if_neg (by rw [ha]; exact procAddr_nonzero hj), ha, slotOf_procAddr hj]
  rw [ha] at hc
  unfold PIDQ at hc; unfold PIDMAX NPROC; unfold NPROC at hj
  omega

end Xv6
