# Project: the sail-riscv model bump (fork pin + the 2026-08 upstream bump)

**STATUS: IN FLIGHT.** The model is regenerated, installed and compiles; the
`iris/` port is partly done and `make proofs` currently FAILS — see
"Where the build stands". Everything below is the recipe and the worklist.

## What changed and why

`model-xv6iris/{rv64d.v,rv64d_types.v}` are now generated from
**[`zeldovich/sail-riscv`](https://github.com/zeldovich/sail-riscv)**, pinned by
`SAIL_RISCV_REV` in the `Makefile`, instead of `riscv/sail-riscv`. The fork's
delta upstream is the **atomic PTE A/D-bit update**: an A/D update during
translation re-reads the PTE with an exclusive read, re-runs the tablewalk
checks on the freshly read value (`check_leaf_pte`, factored out of `pt_walk`
for exactly this), and writes it back with a conditional write, instead of
writing back a value derived from the copy the walk read. That closes the hole
`MANUAL-NOTES.md` recorded (uvmunmap clears a PTE, another hart writes it back
with A|D — impossible on hardware, permitted by the old model).

**The bump is two changes, not one, and it is worth keeping them apart when
diagnosing a breakage.** The fork's tip sits on `riscv/sail-riscv` @ `61266bd`
(2026-08-03) while the previous model came from `eb31a74` (2026-06-16), so
regenerating brought 58 upstream commits along. Measured on the generated Rocq:

| | changed lines in `rv64d.v` | model defs `iris/` references that changed |
|---|---|---|
| upstream `eb31a74 → 61266bd` | 3345 | 63 of 585 |
| the fork's own delta | 686 | 9 of 585 |

The **fork delta** touches `_rec_pt_walk`, `check_leaf_pte` (new),
`update_and_write_pte`, `translate_TLB_hit`, `translate_TLB_miss`, `pmaCheck`
(the PTE arms lost their `assert(not(res_or_con))`, which is what makes an
exclusive PTE read/conditional PTE write legal at all).

The **upstream bump** rewrote the physical-memory access chain; that is where
almost all the porting work is. To isolate the two again, generate at both revs
and diff (README "Regenerating the Sail model" ends with the recipe).

`tools/apidiff`-style measurement, if you need it again: extract per-definition
text blocks from two `rv64d.v`, intersect the names with the identifiers
appearing in `iris/*.v`, and diff the blocks. Beware `loop` — `iris/` has its
own, so it shows up as a false hit in 162 files.

## The upstream bump's interface changes, in the order the build meets them

1. **`PMA` gained two fields** — `PMA_misaligned_atomicity_granule_size_exp`
   and its `_vector_` twin (Zama16b's Misaligned Atomicity Granule). Every PMA
   literal must supply them. `RiscvLang.v`'s three region literals do (RAM 4,
   i.e. 16 bytes; the two IOMemory regions 0, i.e. absent) — read off the
   config, same as every other field there. **DONE.**
2. **`getPendingSet` no longer opens with a guard/assert** — it reads `mideleg`
   only under `currentlyEnabled(Ext_S)` and substitutes zeros otherwise, and
   reads `mie` twice rather than `mie`/`mideleg` twice.
   `RiscvTryStep.exec_getPendingSet_machine_none` follows the S-enabled branch;
   `exec_guard_true` is gone with the guard it modelled. **DONE.**
3. **`MemoryAccessType`'s constructors gained the instruction's aq/rl
   annotations**: `LoadReserved (aq, rl, p)`, `StoreConditional (aq, rl, p)`,
   `Atomic (op, aq, rl, rp, wp)`. 255 sites in 11 files. **The rule:** nothing
   in the translation, PMP or PMA path inspects those booleans, so
   - a lemma that is generic in them gets fresh `(aq rl : bool)` binders (or a
     section `Variable`), and
   - a predicate over an unknown access quantifies them
     (`SRegime.s_acc_ok`'s AMO arm is `exists aq rl, acc = Atomic (AMOSWAP, aq,
     rl, Data, Data)`; `UserPtTree` already had the idiom for `op`), while
   - a lemma about a CONCRETE instruction uses that instruction's annotations.
     Get them from the model, never by guessing: `LOADRES` builds
     `LoadReserved(aq, rl, Data)` and then calls `vmem_read` with `aq, aq & rl`;
     `STORECON` builds `StoreConditional(aq, rl, Data)` and calls `vmem_write`
     with `aq & rl, rl`; `AMO` builds `Atomic(op, aq, rl, Data, Data)`. So a
     lemma whose mem-level args are already `true false` is about
     `amoswap.w.aq`, i.e. `(AMOSWAP, true, false, Data, Data)` — filling the
     mem-level `aq rl` into the access type instead would state a fact about an
     access the model never builds. **DONE for KptPt/KptTree/SRegime/
     UserPtTree/MemAmo4/WpAmo; NOT for UserMemAccess (37), UserMemArms (37),
     UserMemClassify (142), WpSmodePtLock (4), WpSconfLock (3).**
4. **`pmaCheck` answers a plan, not an absence of exception**: its type is
   `result Phys_Mem_Access_Info ExceptionType`, it is an early-return body
   (`catch_early_return`, so it is peeled at the `execR` level), and its tail
   runs `mag_pma_check`. 20 lemmas. **DONE for 13 (see below); NOT for the
   LR/SC pair in `UserMemAccess`, the AMO one in `WpAmo`, the AMO-generic and
   `CacheAccess` ones in `UserMemClassify`, and the inline one inside
   `SmodePte.exec_read_pte_S`.**
5. **`checked_mem_read`/`checked_mem_write` became split-access loops** —
   `check_pma_with_pmp_priority` (not `phys_access_check`) for the PMA/PMP
   decision, then `split_misaligned` on the PHYSICAL address with the plan's
   granule/splittability (it used to be called on the VIRTUAL address, in
   `vmem_read_addr`), then a `untilMT` loop doing a per-split `pmpCheck`,
   `within_mmio_readable`, `read_ram`/`mmio_read` and a
   `update_subrange_vec_dec` into the accumulator. **DONE for `checked_mem_read`
   at widths 4 and 2 (`RiscvFetchExec`) and 8 (`WpLoad`) — the peel is written
   out below; NOT DONE for the rest, nor for `checked_mem_write` anywhere.**
6. **`MemoryOpResult`'s `Err` carries the address**: `Err (paddr, e)`. Only the
   fault arms care (`UserMemClassify`, `UserMemArms`, the `translationException`
   users). **NOT DONE.**
7. **Misaligned AMOs no longer always fault** — the config's
   `memory.misaligned.exceptions.amo` is `{"None": null}` upstream now, so the
   AMO path has a new no-fault branch, and `plat_misaligned_exception` replaced
   `plat_misaligned_access`. **NOT DONE** (`WpAmo`, `MemAmo4`,
   `UserMemClassify`'s AMO arms).
8. **`legalize_medeleg`/`legalize_mideleg` mask by configurable delegatable
   bits** (`plat_medeleg_delegatable_bits` / `plat_mideleg_delegatable_bits`,
   `0xcb3FF` / `0x2222`). xv6's `start()` writes both, so the readback facts in
   the boot chain move. **NOT DONE — not yet reached by the build.**
9. **`isa_version` became `privileged_isa_version`** (`Privileged_ISA_1_13`);
   `physaddr_bits` is now a config parameter (56 for RV64), which is what
   `legalize_satp`'s PPN mask and `pmpaddr`'s legalization width derive from.
   Nothing in `iris/` names the removed `isa_version*` definitions.
10. **`is_aligned_paddr`/`is_aligned_vaddr` moved out of `mem.sail`** — same
    Rocq names, no effect.

## The recipes that are proven and should be reused

All of these live in `iris/RiscvExtras.v` (opcode-independent shared
reductions), which is below every consumer.

- **`pma_ok_aligned`** — the `Phys_Mem_Access_Info` an aligned access yields
  (`CannotSplit`, granule 0). EVERY access these proofs perform is naturally
  aligned, so the whole splitting axis collapses to this one constant. This is
  the single most useful fact about the bump: **the new machinery is inert for
  this development, it just has to be walked past.**
- **`exec_mag_pma_check_aligned`** + the per-access
  `exec_is_mag_applicable_*` facts — `mag_pma_check` short-circuits on
  `is_aligned_paddr`, so an aligned access answers `Ok (CannotSplit, 0)`
  whatever the PMA and whatever the access type.
- **`Ltac pma_ok_peel Hmatch Hfield Hmag Halign`** — the whole `pmaCheck`
  walk, once: read `pma_regions`, resolve `matching_pma_region` to the
  region's overridden attributes, resolve the access arm to the PMA field that
  licenses it (dispatching on whether that arm has an `assert_exp'`), rewrite
  the field to `true`, run `mag_pma_check`. A ported lemma is now three lines:
  `intros …; destruct region as [rbase rsize rattr rdtree]; pma_ok_peel …`.
  13 of the 20 `pmaCheck` lemmas are already in that form.
- **`exec_assert_exp'_true`** — peel an `assert_exp'` whose condition is `true`
  WITHOUT naming its message. **Do not go back to
  `change (assert_exp' true "sys/mem.sail:106.61-106.62" >>= …) with …`:** the
  message is a `<file>:<line>` position in the Sail source, so such a `change`
  breaks on any model edit that shifts a line, for reasons that have nothing to
  do with the proof. Five sites were broken exactly this way by this bump.
- **`exec_split_misaligned_unsplit`**, `pma_ok_aligned_splittable`,
  `pma_ok_aligned_granule`, `misaligned_order_1` — the four facts that get a
  proof from the plan to "one operation of the full width, offset 0".
- **`execR_untilMT_1`** — moved down from `WpLoad.v` into `RiscvFetchExec.v`
  (right after `execR_bind_Some`/`execR_returnR_fwd`, which it needs), because
  the fetch path's `checked_mem_read` needs the one-iteration unrolling too.

## The `checked_mem_read` peel, DONE at widths 4 and 2 (RiscvFetchExec.v)

`RiscvFetchExec.exec_checked_mem_read_ram{,_2}` are ported and compile; copy
their shape. The walk, with the three traps that cost time:

```coq
(* 1. the PMA/PMP decision.  check_pma_with_pmp_priority runs pmaCheck first and
      pmpCheck only to PRIORITISE the exception on failure, so on the success
      path it IS the ported pmaCheck lemma. *)
assert (Hcp : exec (check_pma_with_pmp_priority acc pbmt priv (Physaddr addr) W res) s
              = Some (Ok pma_ok_aligned, s)).
{ unfold check_pma_with_pmp_priority.
  rewrite (exec_bind_Some _ _ _ _ _ (<the ported pmaCheck lemma>)).
  cbn match. apply exec_returnM. }
unfold checked_mem_read. rewrite exec_catch_early_return.
rewrite (execR_liftR_seq _ _ _ _ _ Hcp). cbn beta. cbn match.
rewrite execR_bind. rewrite execR_returnR. cbn match beta.
rewrite pma_ok_aligned_splittable pma_ok_aligned_granule.
rewrite (execR_liftR_seq _ _ _ _ _ (exec_split_misaligned_unsplit addr W 0 s)). cbn beta.
rewrite misaligned_order_1. cbn zeta.
rewrite (execR_liftR_seq _ _ _ _ _ (_ : exec (read_kind_of_flags _ _ _) s = Some (<rk>, s))).
2:{ unfold read_kind_of_flags. apply exec_returnM. }
cbn beta.
(* 2. one loop iteration, at offset 0 *)
match goal with |- context[Defs.bind (Defs.untilMT ?vs ?m ?c ?b) _] =>
  assert (Hu : execR (Defs.untilMT vs m c b) s = Some (inr (w, true, 0), s)) end.
{ eapply execR_untilMT_1; [ reflexivity | | apply execR_returnR_fwd ].
  rewrite (execR_liftR_seq _ _ _ _ _ (exec_assert_exp'_true _ s)). cbn beta.
  change (bits_of_physaddr (Physaddr addr)) with addr.
  rewrite avi0_mulW.                       (* the split offset 0 * W *)
  rewrite (execR_liftR_seq _ _ _ _ _ (<the pmpCheck lemma>)). cbn beta. cbn match.
  ...
  rewrite autocast_id. rewrite usvd_zeros_full_<8*W>.
  apply execR_returnR_fwd. }
rewrite (execR_bind_Some _ _ _ _ _ Hu). cbn beta zeta.
rewrite autocast_id. rewrite execR_returnR. reflexivity.
```

- **`rewrite (execR_liftR_seq …)` only fires when `execR (bind (liftR m) k)` is
  ITSELF a subterm of the goal.** Both the pmpCheck arm (a `bind0` seq into
  `within_mmio_readable`) and the RAM read (an inner `bind` that drops the meta)
  sit UNDER another `bind`, so the rewrite reports "does not match any subterm"
  on a goal that visibly contains the term. Fix: `assert` the inner
  `execR (…) = Some (inr v, s)` — grabbing the term from the goal with
  `match goal with |- context[…] => assert … end` rather than transcribing it —
  and then `rewrite (execR_bind_Some _ _ _ _ _ H)`. `execR_bind0` + `execR_liftR`
  discharge the `bind0` one.
- **The outer `catch_early_return` wrapper is a `match`, not a `returnR`.** The
  last step is `rewrite execR_returnR; reflexivity`, not
  `apply execR_returnR_fwd` — the latter fails with an unreadable "Unable to
  unify … with match execR (returnR …) s with …".
- **The accumulator identity is `usvd_zeros_full_<n>`** (`RiscvExtras.v`), and
  it needs `rewrite autocast_id` first. There is a width-generic proof TACTIC
  (`usvd_zeros_full_tac`) but the statement cannot be made width-generic as it
  stands — see the comment there.

## The keystone still to build

`checked_mem_read`/`checked_mem_write` are proven per access type in ~17 files.
Do NOT port them one at a time — state ONE generic lemma each and make every
existing lemma an application of it:

```coq
Lemma exec_checked_mem_read_unsplit (acc : MemoryAccessType mem_payload)
    (pbmt : page_based_mem_type) (priv : Privilege) (addr : mword 64)
    (width : Z) (aq rl res meta : bool) (rk : read_kind) (w : mword (8 * width)) s :
  exec (check_pma_with_pmp_priority acc pbmt priv (Physaddr addr) width res) s
    = Some (Ok pma_ok_aligned, s) ->
  exec (read_kind_of_flags aq rl res) s = Some (rk, s) ->
  exec (pmpCheck (Physaddr addr) width acc priv) s = Some (None, s) ->
  exec (within_mmio_readable (Physaddr addr) width) s = Some (false, s) ->
  exec (read_ram rk (Physaddr addr) width meta) s = Some ((w, tt), s) ->
  exec (checked_mem_read acc pbmt priv (Physaddr addr) width aq rl res meta) s
    = Some (Ok (w, default_meta), s).
```

The peel, verified as far as the loop body:

```coq
unfold checked_mem_read. rewrite exec_catch_early_return.
rewrite (execR_liftR_seq _ _ _ _ _ Hpac). cbn beta. cbn match.
rewrite execR_bind. rewrite execR_returnR. cbn match beta.
rewrite pma_ok_aligned_splittable pma_ok_aligned_granule.
rewrite (execR_liftR_seq _ _ _ _ _ (exec_split_misaligned_unsplit addr width 0 s)). cbn beta.
rewrite misaligned_order_1. cbn zeta.
rewrite (execR_liftR_seq _ _ _ _ _ Hrk). cbn beta.
(* then: eapply execR_untilMT_1; [reflexivity | <the body> | apply execR_returnR_fwd] *)
```

What is left inside the body, all of it concrete after the above: the
`assert_exp' true "loop dummy assert"` (use `exec_assert_exp'_true`), the
per-split `pmpCheck` at `add_vec_int (bits_of_physaddr (Physaddr addr)) (0 *
width)` (`change (bits_of_physaddr (Physaddr addr)) with addr`, then `avi0`),
`within_mmio_readable`, `read_ram`, and finally the accumulator
`update_subrange_vec_dec (zeros' (8 * 1 * width)) (8 * 1 * width - 1) 0
(autocast split_data)`. **The tree's convention is to CARRY that subrange term
rather than simplify it** — `ProofPlicClaim.v` / `ProofVirtioDiskInit.v` already
state their post-values that way, from the virtual-side split loop that existed
before. Follow it: a `= split_data` identity would need the `autocast` width
coercion discharged at every width.

`check_pma_with_pmp_priority` is `pmaCheck` first and `pmpCheck` only to
PRIORITISE a PMA failure's exception, so on the success path it is
`pmaCheck`'s answer — one thin lemma over the ported `pmaCheck` ones.

## The fork delta's own worklist (the page-table walk)

Independent of the above, and the reason for the bump:

- **`_rec_pt_walk` restructured.** The non-leaf branch is now guarded by
  `not(pte_is_invalid …) & pte_is_non_leaf … & level > 0` (one `and_boolM`), and
  everything else goes to `check_leaf_pte`. `global` is computed before the
  branch. `CommonWalk.v`'s and `Pt4kWalk.v`'s per-level stepping lemmas
  (`cbn [_rec_pt_walk]` then a hand walk) have to follow that shape.
- **Factor `check_leaf_pte` out in the proofs too, exactly as the model did.**
  One lemma "the leaf checks succeed and yield this ppn/pbmt" serves both
  `pt_walk`'s leaf arm and `update_and_write_pte`'s re-check. Its hypotheses
  are the ones the old inline leaf arm consumed (`pte_valid`, `pte_leaf`,
  `pte_no_napot`, `pte_check_ok`, `PBMTE = 0`).
- **`update_and_write_pte` takes 10 arguments and returns
  `result (option pte * ext_ptw) (PTW_Error * ext_ptw)`.** The no-write case is
  still one step (`update_PTE_Bits = None → Ok (None, tt)`). The WRITE case now
  runs, after the Svadu/ADUE gate: `read_pte_exclusive` → `check_leaf_pte` on
  the freshly read word → `update_PTE_Bits` again → `write_pte_conditional`,
  whose `Ok false` arm is an `internal_error` (unreachable in a sequential
  machine).
- **Generalise the PTE read/write leaves over the `res_or_con` flag.**
  `read_pte_exclusive`/`write_pte_conditional` differ from
  `read_pte`/`write_pte` only in that flag, which selects
  `Read_RISCV_reserved`/`Write_RISCV_conditional`. **The interpreter
  (`RiscvLang.run`) ignores the access kind entirely** — `MemRead`/`MemWrite`
  are handled by address, not by kind — so the memory effect is identical and
  ONE flag-generic lemma should serve all four. That is also why the fork needs
  no interpreter change: a conditional write reduces to the same
  `write_bytes`, and `sail_mem_write`'s `Ok _` makes it answer `true`.
- **`translate_TLB_hit` now calls `tlb_get_level`** (new: recovers a TLB
  entry's level from its `levelMask` by a `foreach` over the levels). For the
  level-0 entries this development builds (`u_walk_entry`, `pt_fill_ent`,
  `kpt_tlb_ent` — all with `levelMask = zeros`) it is 0; one lemma.
- `PtTreeAdue.v` is the file that exercises the live A/D write-back path
  (menvcfg.ADUE = 1), so it is where the new read-check-write shows up in full.
  Its §1 PTE-store stack keeps working: the `Store PageTableEntry` arm of
  `pmaCheck` is exactly the one the fork stopped asserting on.

## Where the build stands

`make model` is green (the regenerated model compiles under the project's
`coq-sail-stdpp` 0.20.1 — the checkout asks for a newer `sail` than the one
installed here, and the regen script passes the version it has and says so).

`make -f CoqMakefile -j32 -k` in `iris/` builds **365 of the 802 files** and
stops on **THREE root failures**; everything else is blocked behind them, not
broken:

| file | what it needs |
|---|---|
| `WpLoad.v` | the vmem level: `split_on_page_boundary` + `translate_and_read_value` (its `checked_mem_read`/`pmaCheck` chain IS ported — copy that) |
| `CommonWalk.v` | the fork delta: `_rec_pt_walk`'s new shape + `check_leaf_pte` |
| `WpGprCsrwB.v` | `stimecmp`'s write now refreshes the timer-pending bits (see below) |

The CSR layer is otherwise done: `is_CSR_accessible` now conjoins a CONFIG
predicate with the extension gate for the `xenvcfg` CSRs (menvcfg 0x30A is
`and_boolM (currentlyEnabled Ext_U) (returnM xenvcfg_csrs_are_defined)`), which
`WpGprCsrwCommon.exec_check_CSR_result_csrw_U_and` absorbs with one extra
premise; `WpGprCsrrB`'s read-side site opens the `and_boolM` by hand.
`mideleg_legalized` is re-stated for the new masking: the written value is masked
by `plat_mideleg_delegatable_bits` (0x2222) BEFORE the per-extension gates, and
the old value plays no part any more (the model's first parameter is `_o`).
`legalize_medeleg` masks by `plat_medeleg_delegatable_bits` and additionally
clears the new Double_Trap bit.

`legalize_satp` is DONE and is the pattern for every configuration-derived
field mask the bump introduces: it re-writes satp's PPN through
`zero_extend' 44 (subrange_vec_dec (PPN s) (min (physaddr_bits - pagesize_bits) 44 - 1) 0)`
before dispatching on the mode, and at `physaddr_bits = 56` that window is the
FULL 44-bit field, so the mask is the IDENTITY. `RiscvExtras.satp_ppn_mask_id`
absorbs it in one rewrite and `satp_legalized` needed no change at all. **Do not
re-state a legalized-value definition around such a mask** — it would bake a
platform constant into a definition that does not depend on it, and every
downstream satp fact would then have to carry the wrapper.

Its proof is the reusable kit for bit-field write-back identities, in
`RiscvExtras.v`: `z_lor_split` and `z_field_writeback` over PLAIN `Z` variables
(mandatory — `lia` answers "Cannot find witness" as soon as a `bv_unsigned` is
merely in scope), then `usvd_get_bottom_44` = the bv-level peel that hands them a
closed `Z` goal, then `subrange_full_44` / `zero_extend'_id44` for the two
wrappers. Two ssreflect traps while writing it: `rewrite lem by tac` does not
parse (use `assert … by tac`, or `rewrite lem; [| tac]`), and ssreflect's
`rewrite` hits ALL copies of a pattern, so a proof that peels the same wrapper
twice wants `rewrite ?autocast_id`, not two `rewrite autocast_id`s.

**`WpGprCsrwB`'s remaining failure is `stimecmp`, and it is a real semantic
change, not a shape change.** Writing `stimecmp` (0x14D) now runs
`clint_dispatch false` between the register write and the read-back, which
REFRESHES the timer-pending bits: it writes `mip[7]` (MTIP) from `mtimecmp <=
mtime` unconditionally, and `mip[5]` (STIP) from `stimecmp <= mtime` when
`Ext_Sstc` is enabled and `menvcfg.STCE = 1`. So `exec_write_CSR_stimecmp`'s
post-state is no longer `set_reg s stimecmp _` — it gains one or two `mip`
writes, and the lemma has to grow hypotheses naming `mtime`/`mtimecmp` (and
`menvcfg.STCE`, which decides whether the STIP arm runs at all). That is a
contract change that ripples to its callers, so plan it rather than patching the
proof: decide first whether the STCE arm is live in the states these proofs are
about.

There are no `Admitted`s: `WpLoad.exec_vmem_read_addr_8` is left in its OLD form
behind a `PORT PENDING` comment, so the build points at it rather than a proof
being silently assumed.

**Work the build, not the greps.** The grep counts overstate the damage badly
(370 `is_aligned_paddr` hits are all unaffected; the 46 `translateAddr` files
mostly just mention it in a statement). What actually decides the work is which
lemmas STEP THROUGH a changed body, and that is what a `make -f CoqMakefile
-j32 -k` tells you. Expect the failing set to stay small and to move DOWN the
tree one layer at a time; a single low file blocks hundreds.
