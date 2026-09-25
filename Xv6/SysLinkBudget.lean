/-
**THE OP-WIDE LOG LEDGER OF sys_link, ARM BY ARM, MACHINE CHECKED AT EVERY
CORNER OF THE REPORTED BOOLEANS.**  A port of Rocq `SysLinkBudget.v`
(`/shared/xv6rocq/iris/SysLinkBudget.v`, 228 lines), WHOLE.  Pure.

CONSUMERS (grep, brief fs7b §5.1): Rocq `ProofSysLink.v` (`sl_iu`,
`sl_u0..u3f`, `sl_corr`, the arm theorems), `ProofSysLinkTails.v`
(`sl_orphan_closes`), `LinkSysLink.v` / `SpecDirlink.v` /
`SpecSysUnlink.v` (the refutations and the corner, cited in their headers).
So it is ported whole.

Rocq's header, kept because the reasons are the content:

> sys_link's transaction is
>
>   begin_op                              ten units, empty set
>   namei(old)          success           `wp_namei_gen`
>   ip->nlink++; iupdate(ip)              `wp_iupdate_link`
>   iunlock(ip)                           nothing logged
>   nameiparent(new, name)                `wp_nameiparent_gen`
>   ilock(dp)                             nothing logged
>   dirlink(dp, name, ip->inum)           `wp_dirlink_gen`
>   iunlockput(dp); iput(ip)
>   end_op
>
> with `bad:` -- `ilock(ip); ip->nlink--; iupdate(ip); iunlockput(ip)` --
> reachable from the nameiparent failure and from either dirlink failure.
>
> THE CORRELATION CLAUSE.  Neither walk takes a bitmap credit, so both may
> report `w = true` and spend a unit; but a walk that DID spend it reports
> `bmapstart ∈ Sb'`, so at the one corner where the dirlink runs UNCREDITED
> both `walkSpend`s were zero and the count is two higher.  That is
> `slCorr`, and every arm below is checked at both corners.
>
> THE VERDICT.  Every arm closes, and three of them EXACTLY.  The one that
> decided a contract is dirlink's FOUND arm: it is payable only because
> `SpecDirlink`'s post states the found arm's own spend (`found = true →
> ncount - iputUnits ≤ n'`).  Against the counted `dirlinkUnits` alone it
> is unpayable at every corner -- `slFound_counted_busts(_by_one)` are that
> refutation -- and `slFound_at_four_busts` is why three, not four, is the
> figure the clause had to state.

## Deviations from Rocq

1. As `Xv6/SysUnlinkBudget.lean` deviation 1, plus `dirlink_units`/
   `dl_need` are `SpecDirlink.dirlinkUnits`/`dlNeed`.
2. Names: `sl_iu` → `slIu`, `sl_u0/u1/u2/u3/u3f` → `slU0/U1/U2/U3/U3f`, and
   the theorems camel-headed with Rocq's snake tail (`sl_corr` → `slCorr`,
   `sl_bad1_closes` → `slBad1_closes`, `sl_orphan_closes` →
   `slOrphan_closes`, `sl_found_counted_busts_by_one` →
   `slFound_counted_busts_by_one`, ...).

## Dropped/simplified vs Rocq

Nothing.
-/
import Xv6.SpecIput
import Xv6.SpecWritei
import Xv6.SpecDirlink
import Xv6.SpecNamex

namespace Xv6

/-! ## 1.  What each of sys_link's logging callees spends -/

/-- iupdate: ONE `log_write` of `IBLOCK inum`, free when credited (Rocq's
`sl_iu`). -/
def slIu (cru : Bool) : Nat := if cru then 0 else 1

/-! ## 2.  The ledger down to the dirlink -/

/-- Rocq's `sl_u0`. -/
def slU0 : Nat := MAXOPBLOCKS

theorem slU0_value : slU0 = 10 := rfl

/-- namei(old), success arm (Rocq's `sl_u1`). -/
def slU1 (w1 : Bool) : Nat := slU0 - walkSpend w1

/-- `ip->nlink++; iupdate(ip)` -- UNCREDITED, and that is forced: namei
never locks the inode it returns (Rocq's `sl_u2`). -/
def slU2 (w1 : Bool) : Nat := slU1 w1 - slIu false

/-- nameiparent(new), success arm (Rocq's `sl_u3`). -/
def slU3 (w1 w2 : Bool) : Nat := slU2 w1 - walkSpend w2

/-- nameiparent(new), failure arm (Rocq's `sl_u3f`). -/
def slU3f (w1 w2 : Bool) : Nat := slU2 w1 - (walkSpend w2 + 1)

theorem slU3_values :
    slU3 false false = 9 ∧ slU3 true false = 8 ∧ slU3 false true = 8 ∧ slU3 true true = 7 := by
  decide

theorem slU3_ge7 (w1 w2 : Bool) : 7 ≤ slU3 w1 w2 := by
  revert w1 w2; decide

/-- THE CORRELATION CLAUSE, as arithmetic (Rocq's `sl_corr`): the dirlink
runs uncredited on the bitmap block only where NEITHER walk paid for it, and
there the count is nine. -/
theorem slCorr (w1 w2 : Bool) : (w1 = true ∨ w2 = true) ∨ slU3 w1 w2 = 9 := by
  revert w1 w2; decide

/-! ## 3.  The arms that close -/

/-- ARM E (`bad:` entered from nameiparent returning 0): the flush is
CREDITED -- the `++` put `IBLOCK ip` in the set (Rocq's `sl_bad1_closes`). -/
theorem slBad1_closes (w1 w2 : Bool) :
    1 ≤ slU3f w1 w2 ∧ iputUnits ≤ slU3f w1 w2 - slIu true := by
  revert w1 w2; decide

/-- ARM E2, THE ORPHAN GUARD (Rocq's `sl_orphan_closes`): nothing has been
logged since nameiparent returned, so the free runs UNCREDITED on both
blocks, and the tail's own flush is still credited by the `++`. -/
theorem slOrphan_closes (w1 w2 wd : Bool) :
    let u4 := slU3 w1 w2
    let u5 := u4 - ipSpendW wd false false
    iputUnits ≤ u4 ∧ 1 ≤ u5 ∧ iputUnits ≤ u5 - slIu true := by
  revert w1 w2 wd; decide

/-- dirlink's ENTRY requirement, credited corner (Rocq's
`sl_dl_need_credited`). -/
theorem slDl_need_credited (w1 w2 ind : Bool) : dlNeed true ind ≤ slU3 w1 w2 := by
  revert w1 w2 ind; decide

/-- ...uncredited corner (Rocq's `sl_dl_need_uncredited`). -/
theorem slDl_need_uncredited (ind : Bool) : dlNeed false ind ≤ slU3 false false := by
  revert ind; decide

/-- ARM G, the success append, credited corner (Rocq's
`sl_ok_closes_credited`). -/
theorem slOk_closes_credited (w1 w2 crd al ind wd : Bool) :
    let u4 := slU3 w1 w2 - wi16Spend true crd false al ind
    iputUnits ≤ u4 ∧ iputUnits ≤ u4 - ipSpendW wd true false := by
  revert w1 w2 crd al ind wd; decide

/-- ...uncredited corner (Rocq's `sl_ok_closes_uncredited`). -/
theorem slOk_closes_uncredited (crd al ind wd : Bool) :
    let u4 := slU3 false false - wi16Spend false crd false al ind
    iputUnits ≤ u4 ∧ iputUnits ≤ u4 - ipSpendW wd true false := by
  revert crd al ind wd; decide

/-- ARM F-0, the EMPTY append, credited corner (Rocq's
`sl_fail0_closes_credited`). -/
theorem slFail0_closes_credited (w1 w2 crd al ind : Bool) :
    let u4 := slU3 w1 w2 - wi16Spend true crd false al ind
    let u5 := u4 - ipSpendW false false false
    iputUnits ≤ u4 ∧ 1 ≤ u5 ∧ iputUnits ≤ u5 - slIu true := by
  revert w1 w2 crd al ind; decide

/-- ...uncredited corner (Rocq's `sl_fail0_closes_uncredited`). -/
theorem slFail0_closes_uncredited (crd al ind wd : Bool) :
    let u4 := slU3 false false - wi16Spend false crd false al ind
    let u5 := u4 - ipSpendW wd false false
    iputUnits ≤ u4 ∧ 1 ≤ u5 ∧ iputUnits ≤ u5 - slIu true := by
  revert crd al ind wd; decide

/-! ## 4.  ARM F-FOUND, and the contract it decided

`link(old, new)` with `new` ALREADY PRESENT makes `dirlink`'s `dirlookup`
match, so it `iput`s the child and returns -1 without writing anything.
sys_link cannot refute that arm the way create does, so it has to be PAID
FOR, by SpecDirlink's SEPARATE found-arm clause `found = true → ncount -
iputUnits ≤ n'`. -/

/-- THE REFUTATION THAT CLAUSE ANSWERS (Rocq's `sl_found_counted_busts`):
against the counted `dirlinkUnits = 7` alone the arm is unpayable at every
corner. -/
theorem slFound_counted_busts (w1 w2 : Bool) : slU3 w1 w2 - dirlinkUnits < iputUnits := by
  revert w1 w2; decide

/-- ...and it busts AT THE BEST CORNER BY EXACTLY ONE UNIT (Rocq's
`sl_found_counted_busts_by_one`). -/
theorem slFound_counted_busts_by_one : slU3 false false - dirlinkUnits = 2 ∧ iputUnits = 3 := by
  decide

/-- THE CLAUSE AS LANDED, credited corner (Rocq's
`sl_found_closes_at_iput_units_credited`). -/
theorem slFound_closes_at_iput_units_credited (w1 w2 : Bool) :
    let u4 := slU3 w1 w2 - iputUnits
    let u5 := u4 - ipSpendW false false false
    iputUnits ≤ u4 ∧ 1 ≤ u5 ∧ iputUnits ≤ u5 - slIu true := by
  revert w1 w2; decide

/-- ...uncredited corner (Rocq's
`sl_found_closes_at_iput_units_uncredited`). -/
theorem slFound_closes_at_iput_units_uncredited (wd : Bool) :
    let u4 := slU3 false false - iputUnits
    let u5 := u4 - ipSpendW wd false false
    iputUnits ≤ u4 ∧ 1 ≤ u5 ∧ iputUnits ≤ u5 - slIu true := by
  revert wd; decide

/-- ...and THREE is the largest constant that would have worked: FOUR busts
again (Rocq's `sl_found_at_four_busts`). -/
theorem slFound_at_four_busts :
    let u4 := slU3 true true - 4
    iputUnits ≤ u4 ∧ iputUnits > u4 - ipSpendW false false false := by
  decide

/-- ...and the HONEST figure is at or below it (Rocq's `sl_found_honest`). -/
theorem slFound_honest (wf cruf : Bool) : ipSpendW wf cruf false ≤ iputUnits := by
  revert wf cruf; decide

end Xv6
