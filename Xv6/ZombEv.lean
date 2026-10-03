/-
The PURE event vocabulary of the zombie ledger (the Rocq `ZombEv.v`, commit
2107981b4, NI-LEDGER-REST, the last M1 ledger).

Every fork, exit and reap the kernel performs under `wait_lock` appends one
ACTOR-LABELLED event to a ghost history `h : List Zev`:

  `ZExit a p xs ip` -- kexit's ZOMBIE store, run by actor `a` (the hart's
                    current proc word, the exiting process itself), with
                    pid `p` and exit status `xs` (ruling R1: the status
                    rides in the event because the parent reads it),
  `ZReap a j p`  -- kwait's reap, run by actor `a` (the parent), which
                    took the zombie with pid `p` (in slot `j`),
  `ZFork a j p g` -- kfork's parent store (the family ledger, below).

The history is appended at the END (`h ++ [e]`), so both readings of it are
LEFT FOLDS, and the snoc equations are `List.foldl_append` one-liners:

  `zombiesOf h` -- the zombie set: exits insert the pid's value, reaps
                   remove it;
  `statusOf h`  -- the readable status per zombie pid: exits record the
                   status, reaps forget it.

THE FAMILY LEDGER (NI M2-G1a, design of record
`claude-notes/projects/noninterference.md` "M2-G1 design" §1, rulings
G1-R1/R3): the ledger grows a third event and two fields, so that it records
everything `wait`'s choice depends on, all under `wait_lock`:

  `ZFork a j p g`    -- kfork's `np->parent = p` store, run by the parent
                        `a`, placing the child (pid `p`, generation `g`) in
                        slot `j` (THE PLACEMENT EVENT, R1);
  `ZExit a p xs ip`  -- as before, plus `ip`, the `initproc` word
                        `reparent` wrote (the fold needs no global init
                        address);
  `ZReap a j p`      -- as before, plus the reaped slot `j`.

`famOf h` reads, per slot, the parent cell, the generation and the zombie
column (`ZSlot`); `zHasKids` is kwait's `havekids`, `zLowest` the scan's
choice (the least slot holding a zombie child).  `zombiesOf` / `statusOf`
keep their meaning (`ZFork` steps neither; the new fields are ignored).  No
Iris, no ghost state (`GName` is iris-lean's `Nat` abbreviation).

Design: `claude-notes/design/ni-zombie-ledger.md` (§2 D1, §3 W1) and the
G1 design §1.

## Deviations from Rocq

1. Names: `zev`/`zev_pid`/`zombies_of`/`status_of` are
   `Zev`/`Zev.pid`/`zombiesOf`/`statusOf` (`zev_actor` is not ported:
   nothing uses it); the constructors keep Rocq's spelling (`Zev.ZExit`, `Zev.ZReap`).  `mword 64` / `mword 32` are
   `BitVec 64` / `BitVec 32`; the status `Z` is `Int`; `bv_unsigned p` is
   `(p.toNat : Int)` (as `PidEv`).
2. **The zombie set is a PREDICATE on `Int`** (`Int → Prop`; Rocq: `gset Z`),
   as `PidEv.liveOf` (PidEv deviation 2): `{[x]} ∪ S` is `fun k => k = x ∨ S
   k`, `S ∖ {[x]}` is `fun k => S k ∧ k ≠ x`, `∅` is `fun _ => False`.
3. **The status map is a FUNCTION `Int → Option Int`** (Rocq: `gmap Z Z`):
   `<[x := v]> m` is `fun k => if k = x then some v else m k`, `delete x m`
   is `fun k => if k = x then none else m k`, `∅` is `fun _ => none`.
4. No `Countable` / `EqDecision` instance: iris-lean's `MonoList` camera is
   over `DiscreteO Zev` and asks nothing of the element type (as `PidEv`
   deviation 4).  `DecidableEq` is derived.
5. **`ZFork` keeps the zombie column** (G1 design §1 has `⟨act, g, none⟩`):
   kfork's parent store runs under `wait_lock` AFTER `release(&np->lock)`,
   so the child slot's T2 element (in its lock payload) is not in hand
   there and the zombie column at `j` cannot be READ; keeping it makes the
   step's effect on T2's authority the identity.  It is `none` anyway (the
   slot is USED, its element `none`), and T2 ties the column to the
   elements at every moment, so nothing reads the difference.
-/

import Xv6.ProcGeom

namespace Xv6

open Iris (GName)

/-! ## 1. The events -/

/-- One fork, exit or reap, labelled by its actor (Rocq `zev`, grown into
the family ledger by NI M2-G1). -/
inductive Zev where
  /-- kfork's `np->parent = p` store, run by `act` (the parent), placing the
  child with `pid` and generation `g` in slot `j` (G1-R1) -/
  | ZFork (act : BitVec 64) (j : Nat) (pid : BitVec 32) (g : GName)
  /-- kexit's ZOMBIE store, run by `act` (the exiting process), with `pid`,
  exit status `xs`, and `ip` the `initproc` word `reparent` wrote -/
  | ZExit (act : BitVec 64) (pid : BitVec 32) (xs : Int) (ip : BitVec 64)
  /-- kwait's reap, run by `act` (the parent), of the zombie with `pid` in
  slot `j` -/
  | ZReap (act : BitVec 64) (j : Nat) (pid : BitVec 32)
  deriving DecidableEq, Repr

/-- The pid the event carries (Rocq `zev_pid`). -/
def Zev.pid : Zev → BitVec 32
  | .ZFork _ _ p _ | .ZExit _ p _ _ | .ZReap _ _ p => p

/-! ## 2. The zombie set and the status map, as left folds over the history -/

/-- One event's step on the zombie set (Rocq `zomb_step`; a fork steps
nothing). -/
def zombStep (S : Int → Prop) : Zev → Int → Prop
  | .ZFork _ _ _ _ => S
  | .ZExit _ p _ _ => fun k => k = (p.toNat : Int) ∨ S k
  | .ZReap _ _ p => fun k => S k ∧ k ≠ (p.toNat : Int)

/-- The zombie set after `h` (Rocq `zombies_of`; deviation 2). -/
def zombiesOf (h : List Zev) : Int → Prop := h.foldl zombStep (fun _ => False)

/-- One event's step on the status map (Rocq `status_step`; a fork steps
nothing). -/
def statusStep (m : Int → Option Int) : Zev → Int → Option Int
  | .ZFork _ _ _ _ => m
  | .ZExit _ p xs _ => fun k => if k = (p.toNat : Int) then some xs else m k
  | .ZReap _ _ p => fun k => if k = (p.toNat : Int) then none else m k

/-- The readable status per zombie pid after `h` (Rocq `status_of`;
deviation 3). -/
def statusOf (h : List Zev) : Int → Option Int := h.foldl statusStep (fun _ => none)

/-! ## 3. The family ledger's reading, per slot (G1 design §1) -/

/-- What the ledger says of one slot: its parent cell, its child's
generation, and its zombie column (pid and status, or `none`). -/
structure ZSlot where
  par : BitVec 64
  gen : GName
  zomb : Option (BitVec 32 × Int)
  deriving DecidableEq, Repr

/-- The empty slot: no parent, generation 0, not a zombie. -/
def ZSlot.empty : ZSlot := ⟨0, 0, none⟩

/-- One event's step on the 64 slots: a fork places the child (parent and
generation; deviation 5: the zombie column kept); an exit reparents the
exiting process's children to `ip` and makes its own slot a zombie; a reap
empties the slot (`pp->parent = 0`; freeproc). -/
def famStep (m : Nat → ZSlot) : Zev → Nat → ZSlot
  | .ZFork act j _ g => fun k => if k = j then { m k with par := act, gen := g } else m k
  | .ZExit act pid xs ip => fun k =>
      let s := m k
      let s := if s.par = act then { s with par := ip } else s
      if procAddr k = act then { s with zomb := some (pid, xs) } else s
  | .ZReap _ j _ => fun k => if k = j then ZSlot.empty else m k

/-- The slots after `h`. -/
def famOf (h : List Zev) : Nat → ZSlot := h.foldl famStep (fun _ => ZSlot.empty)

theorem famOf_nil : famOf [] = fun _ => ZSlot.empty := rfl

/-- The snoc equation: an append steps the reading once. -/
theorem famOf_snoc (h : List Zev) (e : Zev) : famOf (h ++ [e]) = famStep (famOf h) e := by
  unfold famOf; rw [List.foldl_append]; rfl

/-- THE PREFIX READING: the reading at a prefix of length `n + 1` is the
reading at the prefix of length `n`, stepped by the `n`-th event. -/
theorem famOf_take (h : List Zev) (n : Nat) (hn : n < h.length) :
    famOf (h.take (n + 1)) = famStep (famOf (h.take n)) h[n] := by
  rw [List.take_add_one, List.getElem?_eq_getElem hn, Option.toList_some, famOf_snoc]

/-- kwait's `havekids`: some slot's parent cell is `a`. -/
def zHasKids (h : List Zev) (a : BitVec 64) : Prop := ∃ k < NPROC, (famOf h k).par = a

instance (h : List Zev) (a : BitVec 64) : Decidable (zHasKids h a) := by
  unfold zHasKids; infer_instance

/-- The scan from slot `k` over `n` slots: the first slot whose parent is
`a` and which is a zombie, with its pid, status and generation. -/
def zScan (f : Nat → ZSlot) (a : BitVec 64) : Nat → Nat → Option (Nat × BitVec 32 × Int × GName)
  | _, 0 => none
  | k, n + 1 =>
    match (f k).zomb with
    | some (pid, xs) => if (f k).par = a then some (k, pid, xs, (f k).gen) else zScan f a (k + 1) n
    | none => zScan f a (k + 1) n

/-- kwait's choice: the least slot `k < NPROC` with `(famOf h k).par = a`
and `(famOf h k).zomb = some (pid, xs)` -- the slot, pid, status and
generation. -/
def zLowest (h : List Zev) (a : BitVec 64) : Option (Nat × BitVec 32 × Int × GName) :=
  zScan (famOf h) a 0 NPROC

theorem zScan_spec (f : Nat → ZSlot) (a : BitVec 64) :
    ∀ (n k i : Nat) (pid : BitVec 32) (xs : Int) (g : GName),
    zScan f a k n = some (i, pid, xs, g) ↔
      k ≤ i ∧ i < k + n ∧ (f i).par = a ∧ (f i).zomb = some (pid, xs) ∧ (f i).gen = g ∧
      ∀ i', k ≤ i' → i' < i → (f i').par = a → (f i').zomb = none := by
  intro n
  induction n with
  | zero => intro k i pid xs g; simp [zScan]; omega
  | succ n ih =>
    intro k i pid xs g
    have hrest : (zScan f a (k + 1) n = some (i, pid, xs, g)) →
        ((f k).par = a → (f k).zomb = none) →
        (k ≤ i ∧ i < k + (n + 1) ∧ (f i).par = a ∧ (f i).zomb = some (pid, xs) ∧ (f i).gen = g ∧
          ∀ i', k ≤ i' → i' < i → (f i').par = a → (f i').zomb = none) := by
      intro hs hk
      obtain ⟨h1, h2, h3, h4, h5, h6⟩ := (ih (k + 1) i pid xs g).1 hs
      refine ⟨by omega, by omega, h3, h4, h5, fun i' hi1 hi2 hp => ?_⟩
      by_cases e : i' = k
      · subst e; exact hk hp
      · exact h6 i' (by omega) hi2 hp
    have hback : (k < i) → (k ≤ i ∧ i < k + (n + 1) ∧ (f i).par = a ∧ (f i).zomb = some (pid, xs) ∧
        (f i).gen = g ∧ ∀ i', k ≤ i' → i' < i → (f i').par = a → (f i').zomb = none) →
        zScan f a (k + 1) n = some (i, pid, xs, g) := by
      intro hki ⟨_, h2, h3, h4, h5, h6⟩
      exact (ih (k + 1) i pid xs g).2 ⟨hki, by omega, h3, h4, h5, fun i' hi1 hi2 hp => h6 i' (by omega) hi2 hp⟩
    simp only [zScan]
    cases hz : (f k).zomb with
    | none =>
      simp only
      constructor
      · intro hs; exact hrest hs (fun _ => hz)
      · intro hr
        have hki : k < i := by
          rcases Nat.lt_or_ge k i with h | h
          · exact h
          · have : i = k := by omega
            subst this; rw [hz] at hr; exact absurd hr.2.2.2.1 (by simp)
        exact hback hki hr
    | some p =>
      obtain ⟨pid0, xs0⟩ := p
      simp only
      by_cases hp : (f k).par = a
      · rw [if_pos hp]
        constructor
        · intro he
          simp only [Option.some.injEq, Prod.mk.injEq] at he
          obtain ⟨rfl, rfl, rfl, rfl⟩ := he
          exact ⟨Nat.le_refl _, by omega, hp, hz, rfl, fun i' hi1 hi2 _ => absurd hi2 (by omega)⟩
        · intro ⟨h1, _, _, h4, h5, h6⟩
          have hik : i = k := by
            rcases Nat.lt_or_ge k i with h | h
            · have := h6 k (Nat.le_refl _) h hp; rw [hz] at this; cases this
            · omega
          subst hik
          rw [hz] at h4
          simp only [Option.some.injEq, Prod.mk.injEq] at h4
          obtain ⟨rfl, rfl⟩ := h4
          rw [h5]
      · rw [if_neg hp]
        constructor
        · intro hs; exact hrest hs (fun h => absurd h hp)
        · intro hr
          have hki : k < i := by
            rcases Nat.lt_or_ge k i with h | h
            · exact h
            · have : i = k := by omega
              subst this; exact absurd hr.2.2.1 hp
          exact hback hki hr

/-- **`zLowest`'s specification**: it names the LEAST slot below `NPROC`
whose parent is `a` and which is a zombie (member, parent, zombie, and
first-ness). -/
theorem zLowest_spec (h : List Zev) (a : BitVec 64) (i : Nat) (pid : BitVec 32) (xs : Int) (g : GName) :
    zLowest h a = some (i, pid, xs, g) ↔
      i < NPROC ∧ (famOf h i).par = a ∧ (famOf h i).zomb = some (pid, xs) ∧ (famOf h i).gen = g ∧
      ∀ i' < i, (famOf h i').par = a → (famOf h i').zomb = none := by
  unfold zLowest
  rw [zScan_spec]
  constructor
  · intro ⟨_, h2, h3, h4, h5, h6⟩
    exact ⟨by omega, h3, h4, h5, fun i' hi hp => h6 i' (Nat.zero_le _) hi hp⟩
  · intro ⟨h1, h3, h4, h5, h6⟩
    exact ⟨Nat.zero_le _, by omega, h3, h4, h5, fun i' _ hi hp => h6 i' hi hp⟩

/-- **`havekids` through T1**: when the 64 parent cells `ps` agree with the
ledger's parent column, kwait's `havekids` scan over the cells IS
`zHasKids`. -/
theorem zHasKids_iff (h : List Zev) (a : BitVec 64) (ps : Nat → BitVec 64)
    (hps : ∀ k < NPROC, ps k = (famOf h k).par) :
    zHasKids h a ↔ ∃ k < NPROC, ps k = a := by
  unfold zHasKids
  constructor
  · intro ⟨k, hk, hp⟩; exact ⟨k, hk, (hps k hk).trans hp⟩
  · intro ⟨k, hk, hp⟩; exact ⟨k, hk, (hps k hk).symm.trans hp⟩

end Xv6
