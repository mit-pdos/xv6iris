/-
The PURE event vocabulary of the zombie ledger (the Rocq `ZombEv.v`, commit
2107981b4, NI-LEDGER-REST, the last M1 ledger).

Every exit and every reap the kernel performs under `wait_lock` appends one
ACTOR-LABELLED event to a ghost history `h : List Zev`:

  `ZExit a p xs` -- kexit's ZOMBIE store, run by actor `a` (the hart's
                    current proc word, the exiting process itself), with
                    pid `p` and exit status `xs` (ruling R1: the status
                    rides in the event because the parent reads it),
  `ZReap a p`    -- kwait's reap, run by actor `a` (the parent), which
                    took the zombie with pid `p`.

The history is appended at the END (`h ++ [e]`), so both readings of it are
LEFT FOLDS, and the snoc equations are `List.foldl_append` one-liners:

  `zombiesOf h` -- the zombie set: exits insert the pid's value, reaps
                   remove it;
  `statusOf h`  -- the readable status per zombie pid: exits record the
                   status, reaps forget it.

No fork event (ruling R3: the pid ledger's `PAlloc parent pid` is the
fork).  No Iris, no ghost state, no gname.

Design: `claude-notes/design/ni-zombie-ledger.md` (§2 D1, §3 W1).

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
-/

namespace Xv6

/-! ## 1. The events -/

/-- One exit or reap, labelled by its actor (Rocq `zev`). -/
inductive Zev where
  /-- kexit's ZOMBIE store, run by `act` (the exiting process), with `pid`
  and exit status `xs` -/
  | ZExit (act : BitVec 64) (pid : BitVec 32) (xs : Int)
  /-- kwait's reap, run by `act` (the parent), of the zombie with `pid` -/
  | ZReap (act : BitVec 64) (pid : BitVec 32)
  deriving DecidableEq, Repr

/-- The pid the event carries (Rocq `zev_pid`). -/
def Zev.pid : Zev → BitVec 32
  | .ZExit _ p _ | .ZReap _ p => p

/-! ## 2. The zombie set and the status map, as left folds over the history -/

/-- One event's step on the zombie set (Rocq `zomb_step`). -/
def zombStep (S : Int → Prop) : Zev → Int → Prop
  | .ZExit _ p _ => fun k => k = (p.toNat : Int) ∨ S k
  | .ZReap _ p => fun k => S k ∧ k ≠ (p.toNat : Int)

/-- The zombie set after `h` (Rocq `zombies_of`; deviation 2). -/
def zombiesOf (h : List Zev) : Int → Prop := h.foldl zombStep (fun _ => False)

/-- One event's step on the status map (Rocq `status_step`). -/
def statusStep (m : Int → Option Int) : Zev → Int → Option Int
  | .ZExit _ p xs => fun k => if k = (p.toNat : Int) then some xs else m k
  | .ZReap _ p => fun k => if k = (p.toNat : Int) then none else m k

/-- The readable status per zombie pid after `h` (Rocq `status_of`;
deviation 3). -/
def statusOf (h : List Zev) : Int → Option Int := h.foldl statusStep (fun _ => none)

end Xv6
