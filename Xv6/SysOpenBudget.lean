/-
**THE OP-WIDE LOG LEDGER OF sys_open, ARM BY ARM** (pure).  A port of Rocq
`SysOpenBudget.v` (`/shared/xv6rocq/iris/SysOpenBudget.v`, 268 lines),
stated at the figures the LANDED Lean contracts state: `MAXOPBLOCKS`
(LogDefs), `walkNeed` / `walkSpend` (SpecNamex), `iputUnits` / `ipSpendW`
(SpecIput), `itEntry` / `itBm` / `itIu` / `itSpend` (SpecItrunc).

Rocq's header, kept (the reasons are the content):

> The whole ledger turns on ONE figure: what the two entry arms leave at the
> JOIN.  The namei arm leaves NINE (ten less at most one walk unit); the
> create arm leaves only what `SpecCreate`'s `ok = true` floor promises,
> which is `iput_units` -- THREE.  So the joint invariant past +0x4a is
> `iput_units <= u`, and every one of the four failure arms below the join
> spends exactly `iput_units` on its `iunlockput`.  That is EXACT:
> `so_join_exact`.
>
> * `so_counted_namei_busts` -- the COUNTED namei cannot serve this caller:
>   at `L = 3` its premise alone is twelve of the ten, and even at `L = 2`
>   it hands back one where the join needs three.  The set form prices the
>   walk at `walk_need L <= 4` whatever the depth.
> * `so_create_nofloor_busts` -- without `SpecCreate`'s `ok = true` floor the
>   create arm reaches the join with a bare `u' <= u`, and the very first
>   `iunlockput` past it is unpayable.
>
> And ONE genuine surprise: the O_TRUNC arm is payable off the create arm's
> three with NO credit at all (`so_trunc_closes`): itrunc's uncredited
> entry level is `it_entry false u = S (S u)`, i.e. TWO.  There is no corner
> at which sys_open needs `crb` or `cru`, and it could not supply either.

(Addresses in Rocq's arm map are Rocq's image; the Lean image's `sys_open`
is at `KA.«sys_open»` and its join is the `lh a4,68(s1)` at +0x4a.)

## The create lemmas

`so_create_need`, `so_create_need_exact` and `so_create_arm_closes` read
`SpecCreate.create_units` (= `MAXOPBLOCKS`), which the Lean port hoists to
`CreateDefs.createUnits` (split of SpecCreate.v, D21); this file imports
`CreateDefs` for it (Rocq imports SpecCreate).

## Deviations from Rocq

1. `S u` / `S (S u)` are `u + 1` / `u + 2` (the port's spelling); every
   quantity is `Nat`, as in Rocq.
2. Names: `so_u0` → `soU0`, `so_un` → `soUn`, `so_unf` → `soUnf`, `so_join`
   → `soJoin`; lemma names camel head, Rocq snake tail (`so_namei_need` →
   `soNamei_need`, ...).

## Dropped/simplified vs Rocq

Nothing.
-/
import Xv6.CreateDefs

namespace Xv6

/-! ## 1.  What each of sys_open's logging callees spends -/

/-- begin_op's mint (Rocq's `so_u0`). -/
def soU0 : Nat := MAXOPBLOCKS

theorem soU0_value : soU0 = 10 := rfl

/-! ## 2.  The two entry arms, down to the join -/

/-- create's premise is EXACTLY begin_op's mint, with nothing to spare
(Rocq's `so_create_need`): the O_CREATE arm is only callable because
sys_open does no logging of its own before it. -/
theorem soCreate_need : createUnits ≤ soU0 := by decide

theorem soCreate_need_exact : createUnits = soU0 := rfl

/-- namei's premise, at every path length (Rocq's `so_namei_need`). -/
theorem soNamei_need (L : Nat) : walkNeed L ≤ soU0 := by
  cases L <;> simp only [walkNeed] <;> decide

/-- THE REFUTATION THAT CHOICE ANSWERS (Rocq's `so_counted_namei_busts`): the
counted premise `(L + 1) * iput_units ≤ n` wants twelve of the ten at three
components. -/
theorem soCounted_namei_busts : (3 + 1) * iputUnits > soU0 := by decide

/-- ...and at TWO components the counted SPEND leaves one where the join's
`iunlockput` needs three (Rocq's `so_counted_namei_busts_at_two`). -/
theorem soCounted_namei_busts_at_two : soU0 - (2 + 1) * iputUnits < iputUnits := by decide

/-- the namei arm's count at the join: ten less at most one walk unit
(Rocq's `so_un`). -/
def soUn (w : Bool) : Nat := soU0 - walkSpend w

theorem soUn_values : soUn false = 10 ∧ soUn true = 9 := by decide

/-- the FAILURE-side count, which ARM B-FAIL exits on (Rocq's `so_unf`). -/
def soUnf (w : Bool) : Nat := soU0 - (walkSpend w + 1)

theorem soUnf_ge8 (w : Bool) : 8 ≤ soUnf w := by cases w <;> decide

/-- ARM C-FAIL (Rocq's `so_armC_closes`). -/
theorem soArmC_closes (w : Bool) : iputUnits ≤ soUn w := by cases w <;> decide

/-! ## 3.  The join, and why the floor is the walk -/

/-- THE JOINT INVARIANT past the join (Rocq's `so_join`). -/
def soJoin : Nat := iputUnits

theorem soJoin_value : soJoin = 3 := rfl

theorem soNamei_meets_join (w : Bool) : soJoin ≤ soUn w := by cases w <;> decide

theorem soJoin_exact : soJoin = iputUnits := rfl

/-- WITHOUT THE FLOOR (Rocq's `so_create_nofloor_busts`, stated as the
corner): the ceiling admits `u' = 0`, and three is not at most zero. -/
theorem soCreate_nofloor_busts : 0 ≤ soU0 ∧ iputUnits > 0 := by decide

/-! ## 4.  The four failure arms below the join -/

theorem soArmD_closes : iputUnits ≤ soJoin := by decide
theorem soArmE_closes : iputUnits ≤ soJoin := by decide
theorem soArmF_closes : iputUnits ≤ soJoin := by decide

/-- on the namei side each of them has six to spare (Rocq's
`so_arms_DEF_namei`) -/
theorem soArms_DEF_namei (w : Bool) : iputUnits ≤ soUn w := by cases w <;> decide

/-- THE SPEND IS NOT THE ENTRY BOUND (Rocq's `so_arms_DEF_survivors`) -/
theorem soArms_DEF_survivors (w : Bool) : soJoin - ipSpendW w false false ≤ 2 := by
  cases w <;> decide

/-! ## 5.  The success tail: O_TRUNC -/

/-- itrunc's UNCREDITED entry level at the create corner: two of three
(Rocq's `so_trunc_need`). -/
theorem soTrunc_need : itEntry false (soJoin - 2) ≤ soJoin := by decide

theorem soTrunc_need_exact : itEntry false (soJoin - 2) = soJoin := by decide

theorem soTrunc_need_namei (w : Bool) : itEntry false (soUn w - 2) = soUn w := by
  cases w <;> decide

/-- WHAT SURVIVES IT, at both reported corners of `w` (Rocq's
`so_trunc_closes`). -/
theorem soTrunc_closes (w : Bool) :
    itEntry false (soJoin - 2) - (itBm w + itIu false) ≤ soJoin := by
  cases w <;> decide

/-- THE HONEST BOUND (Rocq's `so_trunc_spend_two`). -/
theorem soTrunc_spend_two : itSpend false false = 2 := by decide

theorem soTrunc_spend_bounds (w : Bool) : itBm w + itIu false ≤ itSpend false false := by
  cases w <;> decide

/-- AND THE CREDITS ARE NOT AVAILABLE: the arithmetic that would have been
gained, one unit (Rocq's `so_trunc_credit_would_gain`). -/
theorem soTrunc_credit_would_gain : itEntry true (soJoin - 2) < itEntry false (soJoin - 2) := by
  decide

/-! ## 6.  The whole ledger, per entry arm -/

/-- THE O_CREATE ARM, end to end (Rocq's `so_create_arm_closes`): create is
callable, its floor meets the join, every failure arm's `iunlockput` is
callable, and the O_TRUNC tail's entry level is met. -/
theorem soCreate_arm_closes :
    createUnits ≤ soU0 ∧ iputUnits ≤ soJoin ∧ itEntry false (soJoin - 2) ≤ soJoin := by decide

/-- THE else ARM, end to end (Rocq's `so_namei_arm_closes`). -/
theorem soNamei_arm_closes (L : Nat) (w : Bool) :
    walkNeed L ≤ soU0 ∧ iputUnits ≤ soUn w ∧ itEntry false (soUn w - 2) ≤ soUn w := by
  exact ⟨soNamei_need L, soArmC_closes w, Nat.le_of_eq (soTrunc_need_namei w)⟩

end Xv6
