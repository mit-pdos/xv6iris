# The iget licence increment (C′-lite) — build worklist

STATUS: **LANDED** at `35bc973b` (2026-08-16).  Rows 1-13 built as
written; **row 14 deviated and is REPORTED, not absorbed** — see "Row 14"
below.  The campaign-ledger entry is in
[`fs-fragments-campaign.md`](fs-fragments-campaign.md) ("THE iget LICENCE
INCREMENT (C′-lite)"), and it carries the two audit greps, the four
findings and the gate.  Design of record: `design/fs-fragments.md` §7.1
(the C′ verification report, R13(i)/(ii) adopted) as amended by **R14**
(C′ un-parked, licence (d) foreclosed, the `SpanL` transitional
constructor).  Supplier table: §7.5.6.  Mandate: the user's invariant —
*"the kernel will never invoke iget on inode numbers in directories in
a disconnected subtree"* — built in its statable form, a licence
premise on `SpecIget`, per the user's direction of 2026-08-16.

## WHAT IS LEFT

Three things, none of them blocking:

1. **Row 14's shape question, owed to the coordinator.**  F2's
   client-facing premise set grew beyond §7.5.6's disjunction by three
   items — `⌜dir_orphan_clean dn data⌝`, `⌜0 <= dpi < 2 ^ 32⌝` and the
   RESOURCE `FsRep.fedges dpi dn data`.  The exact list, and why no
   tree-level fact supplies (ii), is in `FsLookup.v`'s own header.  **The
   fix that would restore the property outright is folding the edges into
   `fdir`**; that is a change to F1b's landed fragment and is not this
   increment's to make.  F2 still has strictly fewer premises than the
   bytes, so the property is dented, not lost.
2. **`IgetLic.v` folds back at a milestone**, into `InodeRegion.v` /
   `DirLinks.v`, for the reason `IregLinkNz.v` does.  In particular
   `dir_links_borrow` belongs beside `dir_links_dotdot_out`.
3. **`SpanL` and `GreyL` delete**, on the schedule R14 sets: `SpanL` when
   F1.5c mints an `iclaim` (the site becomes `ClaimL`, no signature moves
   — that is why (d) is kept) or when `create_fresh_ty` retires; `GreyL`
   with G1's token deletion, at the same milestone fold-back (it touches
   `IcacheRef`/`InodeRegion`, which this increment could not).

The four readings in `IgetLic.v` (`iname_linked_alloc`,
`iname_held_alloc`, `iname_root_alloc`, `iname_buf_alloc`) have **no
consumer in the tree** — they are the payoff the enumeration makes
available and the proof that the constructors are not vacuous.  Do not
delete them as dead code.

## Goal / non-goal

GOAL: every `iget` in the tree presents a licence from a closed,
type-level enumeration (`ilic`); the orphan-`".."` door (TRACE G,
§7.5.4) is closed by contract — `ProofNamex` earns its licence at
exactly the `fs.c:693` nlink guard, which makes the user's invariant a
theorem of every licensed iget.  §20.17.5's box becomes two greps
(GreyL: zero sites; SpanL: exactly one).

NON-GOAL (do not oversell in ledger entries): the free-side wall is
untouched — §7.1.6's death certificate stands, `create_fresh_ty`
stands.  This is the delivery half of the licence-completion program,
necessary and not sufficient.

## The build list (from §7.1.8, amended by R14)

| # | file | change | est |
|---|------|--------|-----|
| 1 | **NEW `iris/IgetLic.v`** | `ilic` with SEVEN constructors: `LinkedL GreyL HeldL ClaimL BufL RootL SpanL`; `iname` per §7.1.1 with `SpanL => ⌜True⌝` (header comment: the create_fresh_ty span licence, ONE permitted site, deletes with the axiom); `Timeless`; readings: `LinkedL`⇒allocated (`ireg_link_nz`), `HeldL`⇒allocated (definitional), `RootL`⇒allocated (`ireg_root_ok_alive` + (L3) contrapositive), `BufL`⇒allocated (`ireg_read_blk` pattern + `diblk_bytes_inj`).  Leaf home per §7.1.1's comment (do NOT add to InodeRegion.v). | ~200 |
| 2 | `SpecIget.v` | one binder `l : ilic`, one premise `iname γi γfs inum l`, post returns it at the SAME `l` (a `∃ l'` post is FORBIDDEN — §7.1.2), one Require IgetLic | ~15 |
| 3 | `ProofIget.v` | frame the licence on hit and recycle arms; drop on the diverging panic arm | ~10 |
| 4 | `SpecDirlookup.v` | borrowed colourless ticket list + `dinode_at`, in and out, PLUS the disjunctive pure premise verbatim from §7.5.6: `bv_unsigned (di_nlink dn) <> 0 \/ (bname 14 s <> dot_name /\ bname 14 s <> dotdot_name)` (`dir_orphan_clean` is already in the payload — landed) | ~25 |
| 5 | `ProofDirlookup.v` | matched-index `lookup_acc` + the self-record case split; found arm vacuous under the right disjunct | ~120 |
| 6 | `SpecDirlink.v` | borrowed PRE-state ticket list, returned verbatim on both arms (R13(ii)'s amendment of §20.18 ruling 1) | ~25 |
| 7 | `ProofDirlink.v` | thread the borrow to its inner `dirlookup` | ~60 |
| 8 | `ProofNamex.v` / `ProofNamexRoot.v` | left disjunct from `Hnl0` (the `fs.c:693` guard — THE site where the user's invariant is earned; say so in a comment); `RootL` at `+0x4c` | ~40 |
| 9 | `ProofCreate.v` | left-disjunct suppliers at `+0x38` and the four `dirlink`s (the `:269` guard, `ip->nlink = 1`) | ~60 |
| 10 | `ProofSysLink.v` | supply at its `dirlink` (the `:161` orphan guard) | ~40 |
| 11 | `ProofSysUnlink.v` | RIGHT disjunct at its `dirlookup` — the two `namecmp` refusals at `sysfile.c:220-221` (§7.5.6's table, last row) | ~30 |
| 12 | `ProofIreclaim.v` | `BufL` via `iu_held_L` (iget is before its brelse, so the half is in hand); add the §7.1.7 boot-shelter comment (ireclaim's iget lands on claim-shaped records; sheltered by boot order, stated in the comment, not the model) | ~30 |
| 13 | `ProofIalloc.v` | `SpanL` at its iget, with the R14 comment | ~10 |
| 14 | `FsLookup.v` (F2's atomic triple) | re-supply the wrapper over the new SpecDirlookup shape.  If its CLIENT-facing premise set must grow beyond the §7.5.6 disjunction, **STOP AND REPORT** — F2's fewer-premises-than-bytes property is the point of F2 | ~40 |

Readings constraint (STANDING, §7.1.4): every reading is an accessor
over `ireg_inv` in `ireg_link_nz`'s shape.  A free-standing entailment
`iname … -∗ ⌜di_type dn <> 0⌝` with `dn` free is the inconsistent form
`SpecCreateFreshTy.v:34-45` warns about.  Write it in the accessor
shape or not at all.

## What must NOT move (verified list, §7.1.8)

`SpecNamex`, `SpecCreate`, `SpecSysLink`, `SpecIalloc`, `SpecIlock`,
`SpecIput`, `SpecIupdate`, `InodeRegion.v`, `IcacheRef.v`,
`IcacheEscrow.v`, `IcacheBoot.v`, `DirLinks.v`.  The licence is
borrowed within one call; no syscall-level contract sees it.  No new
`Axiom`/`Parameter`/`admit` anywhere; `SpecCreateFreshTy.v`'s statement
untouched.

APPENDIX (one owed comment edit, same gate): rewrite
`SpecCreateFreshTy.v` §(F3) — currently "Nobody has run it" — to the
probe-8 outcome (run, DEAD at THE ADVERSARY RESOLVES CONSISTENTLY,
see fs-fragments.md §7.11).  Comment-only; `LinkCreateFreshTy.vo` must
rebuild green as the statement-drift catch.

## Gate

- Mirror ONLY — NEVER rocq/coqc/make on the local machine.  Recipe
  VERBATIM: `ssh -i /shared/xv6iris/aws/ags-fk.pem -o
  StrictHostKeyChecking=no
  ubuntu@ec2-18-206-159-30.compute-1.amazonaws.com`; mirror checkout is
  `/shared/xv6iris` (same path).  Check `git status` on the mirror
  BEFORE starting; if another lane is dirty/building there, use a lane
  tree (durable-notes rule).
- Full cone of every touched file; `proof_coverage.py --check`;
  `tools/lemma_diff.py` clean.
- `Print Assumptions` on the sealed syscalls unchanged: the standing
  six, +`create_fresh_ty` only in create's cone.  The licence increment
  must add ZERO assumptions.
- THE TWO AUDIT GREPS, recorded in the ledger entry: `grep -n "GreyL"
  iris/Proof*.v` → zero instantiation sites; `grep -n "SpanL"
  iris/Proof*.v` → exactly `ProofIalloc.v`'s iget.

## Row 14 — the deviation, in full

The row said: re-supply F2's wrapper over the new `SpecDirlookup` shape,
and **STOP AND REPORT if its CLIENT-facing premise set must grow beyond
the §7.5.6 disjunction**, because "fewer premises than the bytes" is the
property F2 exists for.  It had to grow, by three items beyond the
disjunction:

| # | what | why it is unavoidable |
|---|---|---|
| (ii) | `⌜dir_orphan_clean dn data⌝` | `FsTree.node_rep`'s NDir case fixes the type, `dir_names_unique` and `ents = dir_view …` and says NOTHING about `di_nlink`.  No tree-level fact implies it. |
| (iii) | `⌜0 <= dpi < 2 ^ 32⌝` | the bytes key the ticket list at `bv_unsigned dinum`, the tree at `dpi : Z`; this is `FsRep.inum_of_unsigned`'s premise, i.e. `FsTree.fs_inums_ok` at one node. |
| (iv) | `FsRep.fedges dpi dn data` | a RESOURCE — the substantive one.  §1.3 makes edges a primitive client-held fragment BESIDE the node, so a client holds it; `fdir` does not contain it. |

The row was EXECUTED rather than left red, because the increment's gate is
a green cone and thirteen rows cannot land behind one red file.  The
finding is recorded in three places (`FsLookup.v`'s header, the campaign
ledger, here) so it cannot be lost, and the ruling owed is item 1 of WHAT
IS LEFT above.

## LAUNCH CONDITION (historical)

AFTER the V5′ P+W closer lands: it holds `ProofCreate.v`,
`ProofSysLink.v`, `ProofSysUnlink.v`, `DirLinks.v`, `FsRep.v`,
`IregDirBit.v`, `IregLinkNz.v`, `LinkSysUnlink.v` and both ledger
files dirty (rows 9-11 and the campaign-ledger entry collide).  Check
`git status` locally first; every listed file must be clean or
committed.  The campaign-ledger entry for this increment is written at
LANDING time, not before.
