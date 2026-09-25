/-
**THE OP-WIDE LOG LEDGER OF create, ARM BY ARM, MACHINE CHECKED** (Rocq
`CreateBudget.v`, 491 lines, WHOLE; fs-icache.md §18 clause 1, fs-sysfile
S5a).  Pure.  Nothing here is a contract: it is the arithmetic create's
contracts are checked against, landed first and on purpose.

CONSUMERS (grep `-w CreateBudget` over `/shared/xv6rocq/iris/*.v`): no `.v`
REQUIRES it; ProofCreate*, SpecCreate, SpecDirlink, SpecWritei, SpecIput,
SpecItrunc, SpecIupdate, SpecSysMkdir/Mknod and SysLinkBudget cite its
theorems in their HEADERS (`cr_budget_fail_late`, `cr_budget_mkdir`, ...).
Ported whole because it is small and it is the record the create proof
stages (7b-3) cite; brief fs7b §4.3 lists it as optional.

Rocq's header, in short (the reasons are the content):

> **xv6 is log-sound at create.**  The op's distinct-block set is at most
> SIX -- IBLOCK(ip), IBLOCK(dp), THE bitmap block, ip's block 0, dp's entry
> block, dp's indirect -- against MAXOPBLOCKS = 10, and every one of
> create's logging calls either introduces one of those six or ABSORBS
> against a block a predecessor already logged.  The walk (nameiparent)
> adds no seventh: a freeing level writes only `bmapstart` and the freed
> inode's own block, already priced (`crz`).
>
> The counted sums are hopeless (`4 * dirlink_units = 28`), and so is the
> set form with the LOOSE per-call constant (`10 - 1 - 1 - 4 - 4 - 4 < 0`).
> What closes it is ABSORPTION CREDITS in the spend bound -- the bitmap
> (`crb`), the DATA block a dirlink writes (`crd`) and the directory's own
> inode block (`cru`).  With those three booleans the ledger closes with
> room, and the TIGHTEST arm -- the late failure, which runs two
> iunlockputs after a dirlink that spent everything it was allowed --
> closes at EXACTLY `iputUnits`.

## Deviations from Rocq

1. Names: `ia_spend` → `crIaSpend`, `iu_spend` → `crIuSpend`, `ip_spend` →
   `crIpSpend`, `ip_need` → `crIpNeed`, `cr_u0` → `crU0`, `cr_uw` → `crUw`
   (prefixed: `iuSpend`/`ipSpend` are generic names a later file may want);
   the theorems camel-headed with Rocq's snake tail (`cr_budget_mkdir` →
   `crBudget_mkdir`, `cr_fail_closes_at_zero` → `crFail_closes_at_zero`,
   `wi16_bmonly_amort_insufficient` → `crWi16_bmonly_amort_insufficient`).
2. `np_spend` IS `SpecNamex.walkSpend` (the same `if w then 1 else 0`; Rocq
   defined it here before the walk's contract exposed the figure), so it is
   reused rather than redefined; `np_spend_le1` is `crNpSpend_le1` over it.
3. `dl_spend` / `dl_need` / `dl0_spend` / `wi16_spend` / `wi_cost_bmonly` /
   `dirlink_units` / `ip_spend_w` / `iput_units` are the landed
   `dlSpend` / `dlNeed` / `dl0Spend` / `wi16Spend` / `wiCostBmonly` /
   `dirlinkUnits` / `ipSpendW` / `iputUnits` (moved to the seams in Rocq
   too).  `vm_compute; lia` is `decide` after `cases` on the booleans.

## Dropped/simplified vs Rocq

Nothing.
-/
import Xv6.SpecIput
import Xv6.SpecWritei
import Xv6.SpecDirlink
import Xv6.SpecNamex

namespace Xv6

/-! ## 1.  What each of create's logging callees spends -/

/-- ialloc: ONE `log_write`, of the claimed inode's home block; the inum is
the scan's, so no caller can credit it (Rocq's `ia_spend`). -/
def crIaSpend : Nat := 1

/-- iupdate: ONE `log_write` of `IBLOCK inum`, ABSORBED when the op already
logged it (`cru`; Rocq's `iu_spend`). -/
def crIuSpend (cru : Bool) : Nat := if cru then 0 else 1

/-- iput (through iunlockput): NOTHING unless it frees, and a free spends only
what it cannot absorb -- itrunc's bfrees all hit THE bitmap block and its
final iupdate hits `IBLOCK inum` (Rocq's `ip_spend`). -/
def crIpSpend (crb cru freed : Bool) : Nat :=
  if freed then (if crb then 0 else 1) + crIuSpend cru else 0

/-- Rocq's `ip_need`. -/
def crIpNeed : Nat := iputUnits

theorem crIpNeed_value : crIpNeed = 3 := rfl

/-- nameiparent: under group absorption the whole walk spends AT MOST ONE
unit, THE bitmap block (Rocq's `np_spend_le1`, at `walkSpend`). -/
theorem crNpSpend_le1 (w : Bool) : walkSpend w ≤ 1 := by cases w <;> decide

/-! ## 2.  The ledger, arm by arm -/

/-- create's caller runs ONE begin_op..end_op around the whole body (Rocq's
`cr_u0`). -/
def crU0 : Nat := MAXOPBLOCKS

theorem crU0_value : crU0 = 10 := rfl

/-- ...and what is left when nameiparent hands the parent back (Rocq's
`cr_uw`).  Every arm is stated at THIS level and quantifies over `w`. -/
def crUw (w : Bool) : Nat := crU0 - walkSpend w

theorem crUw_values : crUw false = 10 ∧ crUw true = 9 := by decide

/-- ARM C-OK-DIR, the mkdir success path: ialloc, iupdate(ip) (absorbs),
dirlink(ip, ".") (allocates block 0), dirlink(ip, "..") (absorbs whole),
dirlink(dp, name) (worst case: grows through the indirect), iupdate(dp)
(absorbs).  Closes at EXACTLY `iputUnits`, at either `w`. -/
theorem crBudget_mkdir (w : Bool) :
    let u1 := crUw w - crIaSpend
    let u2 := u1 - crIuSpend true
    let u3 := u2 - dlSpend w false false true false
    let u4 := u3 - dlSpend true true true false false
    let u5 := u4 - dlSpend true false false true true
    let u6 := u5 - crIuSpend true
    crIaSpend ≤ crUw w ∧ 1 ≤ u1 ∧ dlNeed w false ≤ u2 ∧ dlNeed true false ≤ u3 ∧
      dlNeed true true ≤ u4 ∧ 1 ≤ u5 ∧ crIpNeed ≤ u6 ∧ u6 = 3 := by
  cases w <;> decide

/-- ARM C-OK-FILE: the ONE dirlink pays for the bitmap block itself, which is
why `dlNeed false true` (six) is the largest requirement in create. -/
theorem crBudget_file (w : Bool) :
    let u1 := crUw w - crIaSpend
    let u2 := u1 - crIuSpend true
    let u3 := u2 - dlSpend w false false true true
    crIaSpend ≤ crUw w ∧ 1 ≤ u1 ∧ dlNeed w true ≤ u2 ∧ crIpNeed ≤ u3 := by
  cases w <;> decide

/-- ARM FAIL entered from the LAST dirlink of the mkdir path, the tightest arm:
iupdate(ip) absorbs, iunlockput(ip) FREES (bitmap and IBLOCK(ip) both paid),
iunlockput(dp) frees nothing.  Closes at EXACTLY `iputUnits`. -/
theorem crBudget_fail_late (w : Bool) :
    let u1 := crUw w - crIaSpend
    let u2 := u1 - crIuSpend true
    let u3 := u2 - dlSpend w false false true false
    let u4 := u3 - dlSpend true true true false false
    let u5 := u4 - dlSpend true false false true true
    let u6 := u5 - crIuSpend true
    let u7 := u6 - crIpSpend true true true
    crIpNeed ≤ u6 ∧ crIpNeed ≤ u7 ∧ u7 = 3 := by
  cases w <;> decide

/-- ARM FAIL entered EARLY (the "." link failed): strictly slacker. -/
theorem crBudget_fail_early (w : Bool) :
    let u1 := crUw w - crIaSpend
    let u2 := u1 - crIuSpend true
    let u3 := u2 - dlSpend w false false true false
    let u4 := u3 - crIuSpend true
    let u5 := u4 - crIpSpend true true true
    crIpNeed ≤ u4 ∧ crIpNeed ≤ u5 := by
  cases w <;> decide

/-- ARM FAIL entered from the NON-DIRECTORY dirlink: `crBudget_file`'s chain
with the fail tail spliced on; both tail claims are ZERO. -/
theorem crBudget_fail_file (w : Bool) :
    let u1 := crUw w - crIaSpend
    let u2 := u1 - crIuSpend true
    let u3 := u2 - dlSpend w false false true true
    let u4 := u3 - crIuSpend true
    let u5 := u4 - crIpSpend true true true
    crIaSpend ≤ crUw w ∧ 1 ≤ u1 ∧ dlNeed w true ≤ u2 ∧
      crIpNeed ≤ u3 ∧ crIpNeed ≤ u4 ∧ crIpNeed ≤ u5 := by
  cases w <;> decide

/-- ARMS N / F-OK / F-BAD / A-FAIL: nothing is logged before them. -/
theorem crBudget_found (w : Bool) :
    crIpNeed ≤ crUw w ∧ crIpNeed ≤ crUw w - crIpSpend true true false := by
  cases w <;> decide

/-- ...AND THE SAME ARMS AT THE FIGURE THEY CAN ACTUALLY CLAIM: on these arms
create holds neither absorption credit (nothing is logged yet, and `crz` is
minted from a NONZERO nlink observation, which ARM G negates), so the honest
per-call figure is `ipSpendW w false false`, at most two. -/
theorem crBudget_found_w (w wg wf : Bool) :
    let u1 := crUw w
    let u2 := u1 - ipSpendW wg false false
    crIpNeed ≤ u1 ∧ crIpNeed ≤ u2 ∧ crIpNeed ≤ u2 - ipSpendW wf false false := by
  cases w <;> cases wg <;> cases wf <;> decide

/-! ## 3.  What the uncredited contracts give, and why it is not enough -/

/-- THE RULING'S REFUTATION (GR-3 stage-3): exposing only the bitmap
amortization cannot close the mkdir arm; this is why `SpecWritei`'s
sixteen-byte post exposes the full `wi16Spend`. -/
theorem crWi16_bmonly_amort_insufficient :
    let amort (inS : Bool) : Nat := wiCostBmonly 0 16 - (if inS then 1 else 0)
    crU0 - crIaSpend - crIuSpend true - amort false - amort true - amort true < iputUnits := by
  decide

/-- THE LOOSE SPEND BOUND BUSTS ON THE THIRD dirlink. -/
theorem crBudget_loose_busts :
    let u1 := crU0 - crIaSpend
    let u2 := u1 - 1
    let u3 := u2 - dlNeed false false
    let u4 := u3 - dlNeed false false
    u4 < dlNeed false false := by
  decide

/-- ...AND THE COUNTED FORM IS FURTHER OUT STILL: four dirlinks at
`dirlinkUnits` is 28 against 10. -/
theorem crBudget_counted_busts : crU0 < 4 * dirlinkUnits := by decide

/-- THE CREDIT ON THE DATA BLOCK IS LOAD BEARING: without it the LATE FAIL
arm's second iunlockput runs out. -/
theorem crBudget_needs_data_credit :
    let u1 := crU0 - crIaSpend
    let u2 := u1 - crIuSpend true
    let u3 := u2 - dlSpend false false false true false
    let u4 := u3 - dlSpend true false true false false
    let u5 := u4 - dlSpend true false false true true
    let u6 := u5 - crIuSpend true
    let u7 := u6 - crIpSpend true true true
    u7 < crIpNeed := by
  decide

/-! ## 3b.  The `fail:` tail and the dirlink that enters it -/

/-- THE REFUTATION THE REPAIR ANSWERS: at the counted per-call constant the
tail's first iunlockput cannot run. -/
theorem crFail_counted_busts (w : Bool) :
    let u1 := crUw w - crIaSpend
    let u2 := u1 - crIuSpend true
    let u3 := u2 - dirlinkUnits
    let u4 := u3 - crIuSpend true
    u4 < crIpNeed := by
  cases w <;> decide

/-- ...and it is the SPEND bound and nothing else. -/
theorem crFail_would_fit_at_u0 : crIpNeed ≤ crU0 - dirlinkUnits := by decide

/-- THE REPAIR'S FIRST CLAUSE, at `0 < tot`: the tail closes at every value of
the reported booleans. -/
theorem crFail_closes_with_credit (w crd cru al ind : Bool) :
    crIpNeed ≤ crUw w - crIaSpend - crIuSpend true - dlSpend w crd cru al ind := by
  cases w <;> cases crd <;> cases cru <;> cases al <;> cases ind <;> decide

/-- THE REPAIR'S SECOND CLAUSE, at `tot = 0`, at the figure dirlink can prove
(`dl0Spend`): it closes the two routes whose failing dirlink is create's FIRST
logging dirlink. -/
theorem crFail_closes_at_zero (w : Bool) :
    crIpNeed ≤ crUw w - crIaSpend - crIuSpend true - dl0Spend := by
  cases w <;> decide

/-- ...AND WHAT THE CONSTANT DOES NOT CLOSE: the mkdir path's INTERIOR entries
run with SIX in hand, and four from six leaves two. -/
theorem crFail_mkdir_at_zero_busts (w : Bool) :
    let u1 := crUw w - crIaSpend
    let u2 := u1 - crIuSpend true
    let u3 := u2 - dlSpend w false false true false
    let u4 := u3 - dlSpend true true true false false
    u3 = 6 ∧ u4 = 6 ∧ u3 - dl0Spend < crIpNeed ∧ u4 - dl0Spend < crIpNeed ∧
      crIpNeed ≤ u3 - 3 ∧ crIpNeed ≤ u4 - 3 := by
  cases w <;> decide

/-- THE FLIP, AT THE FIGURE ITSELF: both interior entries close against the
credit-aware spend at every value of the booleans, on a DIRECT window. -/
theorem crFail_mkdir_closes (w crb crd cru al : Bool) :
    let u1 := crUw w - crIaSpend
    let u2 := u1 - crIuSpend true
    let u3 := u2 - dlSpend w false false true false
    let u4 := u3 - dlSpend true true true false false
    crIpNeed ≤ u3 - wi16Spend crb crd cru al false ∧
      crIpNeed ≤ u4 - wi16Spend crb crd cru al false := by
  cases w <;> cases crb <;> cases crd <;> cases cru <;> cases al <;> decide

/-- ...AND ON THE INDIRECT PATH, once the bitmap block is in the op's set. -/
theorem crFail_mkdir_closes_ind (w crd cru al : Bool) :
    let u1 := crUw w - crIaSpend
    let u2 := u1 - crIuSpend true
    let u3 := u2 - dlSpend w false false true false
    let u4 := u3 - dlSpend true true true false false
    crIpNeed ≤ u3 - wi16Spend true crd cru al true ∧
      crIpNeed ≤ u4 - wi16Spend true crd cru al true := by
  cases w <;> cases crd <;> cases cru <;> cases al <;> decide

/-- ...AND THAT CORNER IS ATTAINED: an allocating INDIRECT window at an unpaid
bitmap block spends the full four. -/
theorem crWi16_spend_max : wi16Spend false false false true true = 4 := by decide

/-- THE CREDIT ON THE INODE BLOCK IS LOAD BEARING TOO. -/
theorem crBudget_needs_inode_credit :
    let u1 := crU0 - crIaSpend
    let u2 := u1 - crIuSpend false
    let u3 := u2 - dlSpend false false false true false
    let u4 := u3 - dlSpend true true false false false
    let u5 := u4 - dlSpend true false false true true
    let u6 := u5 - crIuSpend false
    u6 < crIpNeed := by
  decide

end Xv6
