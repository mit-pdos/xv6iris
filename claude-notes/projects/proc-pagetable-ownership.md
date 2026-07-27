# Project: the process page table — OWNERSHIP (`struct proc`'s `pagetable`)

One predicate for "a valid process page table", and the reconciliation that
keeps it the *only* such definition. `iris/ProcPtOwn.v` holds the design; this
file is the worklist for folding the pre-existing descriptions into it.

**Not to be confused with [`../completed/proc-pagetable.md`](../completed/proc-pagetable.md)**,
which is the *construction* side (proc_pagetable / uvmcreate, `iris/ProcPt.v`'s
`ppt_*` pure layer). The two meet at exactly one lemma:
`ProcPtOwn.proc_pt_intro_ppt` takes `wp_proc_pagetable`'s post through
`ProcPt.ppt_bridge` into `proc_pt` at the empty user map — the caller adding
only the trapframe page, which proc_pagetable deliberately does not own.

## What already existed, and how it was layered

Three existing descriptions, at different altitudes — all keepers, none
duplicating another:

- **`ProcPt.v` (upstream) — construction.** `ppt_m1` / `ppt_map tfp` are the
  maps the two `mappages` runs build; `ppt_bridge` turns `pt_rep0 t (ppt_map
  tfp)` into `upt_tree_spec (pt_base t) tfp ∅ t`. Pure; no ownership, no
  validity beyond the tree.

- **`UptTree.v` — the mapping spec.** `upt_tree_spec uroot tfp um` is *the*
  statement of what a user Sv39 table maps: the trampoline leaf at
  `tramp_vpn`, `pte_tf tfp` at `tf_vpn`, an abstract user map `um : gmap vpn
  leaf` below, every other vpn blocked, every leaf modulo the Svadu A/D bits.
  `upt_map_wf um` is its well-formedness (each user vpn below `tf_vpn`, each
  leaf a proper 4K leaf on every A/D variant). `utlb_inv_pt uroot tfp um` is
  that table **installed** (satp at `uroot`, `tlb_ok_pt`, `ptree_own 2 1 t`,
  `pmp_config`); `pt_frame (upt_tree_spec …)` (PtTree.v) is the same table
  **parked**, which is the form `wp_userret_pt` (UserretAllPt.v) consumes.
- **`UserPtTree.v` — the user-execution bundle.** The descriptor record
  `uptd` and `upt_acc_wf` (each leaf is User-ok or User-denied on every A/D
  variant — decided once when the map is built), plus `user_pt_inv P` =
  `utlb_inv_pt` ∗ `udata_own ud_data` ∗ ⌜`udata_cov`⌝ ∗ ⌜`upt_acc_wf`⌝.
  `UserExec.user_inv` wraps it; `UserKernelBridge.userret_to_user_inv`
  repackages userret's post into it.

So `user_pt_inv` was the closest thing to a "process page table", and three
things were missing from it:

1. **Nothing owned the pages on the parked side.** `pt_frame` owns the root
   and interior nodes only; a parked table's user pages were owned nowhere.
2. **The trapframe page had no owner at all.** `wp_userret_pt` takes its 35
   register slots as loose `↦ₚ₈{dqm}` words and hands them back; nothing
   holds the page.
3. **Nothing said the mapped pages are kalloc pages.** A "valid" user table
   could map kernel text or a device page with `PTE_U` set, and there was no
   way to move between the kernel's `↦ₘ` view of a page and user execution's
   `↦ₚ` view.

Plus one shape defect: `ud_data` + `udata_cov` is a derived quantity carried
as a second field of the same record and re-coupled by a side condition —
exactly the "ad-hoc argument coupling" the durable notes warn off.

## The design (in `iris/ProcPtOwn.v`)

Three decisions, argued in the file header:

1. **The footprint is derived from `um`.** `pte_ppn w` is the ppn a leaf
   names; `um_ppns um` the pages, `page_pas ppn` / `um_pas um` their bytes.
   `udata_cov um (um_pas um)` is then a theorem (`um_pas_cov`, over
   `u_walk_pa_in_page`: a leaf's translate output lies in that leaf's page).
2. **Pages are owned in the PHYSICAL tier** (`phys_page_own ppn`, 4096
   existential `↦ₚ` bytes). A page a user table maps is reachable at two
   virtual addresses — its identity kernel va (kalloc's pointer; how
   copyin/copyout/kfree reach it) and its user va — so neither belongs baked
   into the resource, which VA-based `KallocInv.page_own` (`↦ₘ`) would do.
   `udata_own` is already this tier, so **the satp switch converts nothing**.
   The kernel's `page_own` view is recovered per page by the claim-keyed
   bridge (`KMap.mem_ident_phys` / `phys_ident_mem`).
3. **Validity carries "every mapped page is a kalloc page"**
   (`um_pages_valid`, and the same for `ud_tfp`). Load-bearing twice: it
   keeps the tier bridge of (2) available on every byte
   (`page_in_range_addr_is_kdata` + `kdata_svpn_class` ⇒ `kmap_static … KP_rw`,
   packaged as `um_pages_kmap_static`), and it is what makes the pages
   re-freeable on exit — the role `page_valid` plays in `is_pipe`.

The pieces:

```
proc_pt_wf P  := upt_map_wf ud_um ∧ upt_acc_wf ud_um
               ∧ um_pages_valid ud_um ∧ page_valid (page_base ud_tfp)
proc_pt_own P := proc_tf_own ud_tfp ∗ upt_pages_own ud_um     (* what it OWNS *)
proc_pt P     := ⌜proc_pt_wf P⌝ ∗ pt_frame (upt_tree_spec …) ∗ proc_pt_own P
proc_pt_at pa P := p_pagetable pa ↦₈ page_base ud_root
                 ∗ p_trapframe pa ↦₈ page_base ud_tfp ∗ proc_pt P
```

The trapframe page is its own conjunct (`proc_tf_own`, `phys_page_own ud_tfp`
today) so it can later gain **structure** — the saved user registers,
`kernel_satp`, `kernel_sp`, `epc`, which uservec/usertrapret read back —
without disturbing the rest. Existential contents are all `wp_userret_pt`
needs today; the eventual `stvec_handler_wp` discharge (uservec) is what
will force the structured form.

Parked ⇄ installed differ in **exactly one conjunct** (`pt_frame` vs
`utlb_inv_pt`); `proc_pt_own` and the wf ride across unchanged, and the
conversion is the existing satp-switch window (`TransPt.tlb_inv_pt2_enter` /
`_exit`, already used by `wp_userret_entry_pt`).

## Worklist

**Step 1 — extract `PageOwn.v` out of `KallocInv.v`.** Move the page
geometry and the `page_own` family (`PGSIZE`/`kmem_lo`/`kmem_hi`,
`page_aligned`/`page_in_range`/`page_valid` + `page_valid_ne_null` /
`_aligned8`, `page_in_range_addr_is_kdata` and its two local arithmetic
helpers, `byte_any`/`word_at`/`page_head8`/`page_rest`/`page_own`/`run_page`
+ `page_own_split`/`word_at_head8`) into a new low file requiring only
`RiscvModelBytes`/`RiscvPtsto`; `Require Export` it from `KallocInv.v` so
every existing consumer is untouched. Needed so `UserPtTree.v` can name
`page_valid` without pulling `WpLock` into the user-execution stack. (All of
it currently sits in a section with `!lockG Σ, !kallocG Σ` in context but
uses neither, so the move is transparent.)

**Step 2 — move `ProcPtOwn.v`'s §1–§3 into `UserPtTree.v`.** `pte_ppn`,
`page_base`, `um_ppns`, `page_pas`, `um_pas`, `ud_pas`, `um_pages_valid`,
`proc_pt_wf`, `phys_byte_any`, `phys_page_own`, `upt_pages_own`,
`proc_tf_own`, `proc_pt_own`. `UserPtTree.v` owns `uptd`, so the descriptor
and its footprint belong in one file; `ProcPtOwn.v` keeps only the parked form
and the `struct proc` cells. (`ProcPtOwn.v` is written so this is a cut/paste —
it requires nothing of `UserPtTree` that `UserPtTree` cannot state itself,
except `page_valid` from step 1.)

**Step 3 — drop the `ud_data` field; re-shape `user_pt_inv`.**

```
Definition user_pt_inv (P : uptd) : iProp Σ :=
  ⌜proc_pt_wf P⌝ ∗ utlb_inv_pt ud_root ud_tfp ud_um ∗ proc_pt_own P.
```

Then `user_pt_inv` and `proc_pt` are literally the same definition modulo
the tree conjunct. Churn: `ud_data` appears 22× (UserPtTree, UserKernelBridge,
UserClassifyAsm, UserMemClassify) → `ud_pas P`; `udata_cov` premises stay on
the *lemmas* in UserFetchPt/UserMemAccess/UserMemPt (they take `um` and
`data` separately and should stay general) and are discharged at call sites
by `ud_pas_cov`. `upt_acc_wf` moves out of the bundle into the wf. Also drops
`ProcPtOwn.ppt_desc`'s 4th `UPTD` argument (it passes `um_pas ∅` today only
because the field still exists).

**Step 4 — the two bridge lemmas: DONE** (proven in `ProcPtOwn.v`, axiom-clean).
Both are pure big-op reshuffling; neither has a `kmap_static` side condition:

```
phys_bytes_udata  (S : gset Arch.pa) : ([∗ set] a ∈ S, phys_byte_any a) ⊣⊢ udata_own S
phys_page_own_set (ppn)              : phys_page_own ppn ⊣⊢ [∗ set] a ∈ page_pas ppn, phys_byte_any a
phys_pages_own_set (T)               : ([∗ set] ppn ∈ T, phys_page_own ppn) ⊣⊢ [∗ set] a ∈ pages_pas T, …
upt_pages_udata   (um)               : upt_pages_own um ⊣⊢ udata_own (um_pas um)
proc_pt_own_udata (P)                : proc_pt_own P ⊣⊢ proc_tf_own ud_tfp ∗ udata_own (ud_pas P)
```

Reusable bits: `phys_bytes_udata`'s → direction is a `set_ind_L` induction
accumulating `dm` (`big_sepS_insert` / `big_sepM_insert`, `dm' !! a = None`
from `dom dm' = S'` and `a ∉ S'`); ← is `big_sepM_dom` + `big_sepM_impl`.
All the disjointness comes from one arithmetic lemma
(`pa_add_page_unsigned`) via `page_pa_inj` (offsets inside a page) and
`page_pas_disjoint` / `page_pas_disjoint_pages` (distinct pages); the
`z_*` helpers are stated over plain `Z` so `lia` is never looking at a
`bv_unsigned` goal.

**Step 4b — the trapframe opener.** `wp_userret_pt` already takes its 35
register slots as `↦ₚ₈{dqm}` words at `zero_extend' 64 (concat_vec tfp
(pageoff (TRAPFRAME + k)))` — i.e. already the physical tier, at
`pa_add (page_base tfp) k`. So decision (2) needs no conversion there
either; what is needed is the split/rejoin pair

```
Lemma proc_tf_open (tfp : mword 44) :
  proc_tf_own tfp -∗ (35 slots as ↦ₚ₈ with existential words) ∗ (rejoin wand)
```

i.e. a `phys_page_own` → aligned-8-word-window accessor (the `↦ₚ₈` body is
`[∗ list] j ∈ seq 0 8, ↦ₚ`, so this is `big_sepL` regrouping over
`seq 0 4096` plus the doubleword alignment `page_valid` gives). This is what
turns userret's 35 loose premises into one conjunct.

**Step 5 — the kalloc/kfree boundary: DONE** (`ProcPtOwn.v`, axiom-clean). The
pair that moves a page in and out of a process page table — the ONE place a
process's pages change tier (in at uvmalloc / proc_pagetable, out at
uvmunmap / freewalk):

```
page_own_to_phys / phys_to_page_own (ppn) :
  page_valid (page_base ppn) ->
  kmap_static_claims -∗ page_own (page_base ppn) ∗-∗ phys_page_own ppn
```

Pointwise `mem_ident_phys` / `phys_ident_mem` under `big_sepL_impl`; the
per-byte side conditions come from `page_valid_kmap_static` /
`page_valid_ram` / `page_valid_canon` (all in `ProcPtOwn.v` §3, off
`page_in_range_addr_is_kdata` + `kdata_svpn_class`). These supersede
`KMap.mem_page_to_phys`, which is stated for a *single constant byte value*
across the page and so does not fit `page_own`'s per-byte existential
contents — delete it once its (single) call site moves over, rather than
keeping both.

**Step 6 — the `struct proc` cell addresses: DONE.** `sz_off`/`pagetable_off`/
`trapframe_off` (72/80/88) and `p_sz`/`p_pagetable`/`p_trapframe` are added
to `ProcGeom.v`. The offsets are pinned by two independent anchors already
there: `pid` at +48 and `context_off = 96`, and confirmed by
`proc_size = 360` (96 + context 112 + ofile 128 + cwd 8 + name 16). Touching
`ProcGeom.v` rebuilds ~54 files.

**Step 7 — consumers.** `p->pagetable` / `p->trapframe` are `p->lock`-FREE
in xv6 ("these are private to the process, so p->lock need not be held"), so
`proc_pt_at` does **not** belong inside `proc_lock_res` (SchedCtx.v) — it
belongs with the running process's private state, i.e. alongside the
`cur_proc` resource (`completed/yield-sched.md`). Settle this when the first
`uvm*` / `usertrapret` proof needs it. `p->sz` coherence with `um`'s domain
is a *separate* fact the `uvmalloc`/`uvmdealloc` specs will carry; it is
deliberately not part of table validity.

Two things that correctly stay OUT of the parked form: `satp` (owned by the
installed invariant only) and `pmp_config` — hart-level, and phantom in its
root index anyway (`TransPt.pmp_config_reindex` converts by `iExact`).

## Adjacent, not blocking

- **`PageFields.v`** (added with `pipealloc`) carves a `page_own` into typed
  struct fields — the same page→object boundary this file crosses, but in the
  field direction rather than the tier direction. Nothing overlaps today; if a
  structured trapframe lands (see above), it should be built on `PageFields`'s
  `bwin_split` / `bwin_rebase` / `bytes_word8` rather than on new machinery.
- **The `pa_add`-doesn't-wrap lemma now has four copies**:
  `UserBits.uint_add_vec_int_small`, `Pt4kWalk.pt_add_vec_int_small`,
  `PageFields.pa_add_unsigned`, and `SmodePte.uint_pa_add` (which
  `ProcPtOwn.pa_add_page_unsigned` uses). `PageFields.v`'s header already calls
  for folding them into `RiscvExtras` beside `avi0`; do that once, and point
  `pa_add_page_unsigned` at the survivor.

## Open questions

- **Which pages does the predicate own — all of `um`, or only the `PTE_U`
  ones?** Currently all: ownership is what makes a page unaliased and
  re-freeable, and xv6's `uvmunmap`/`freewalk` free everything in `um`
  regardless of `U`. Owning a non-U page's bytes is strictly stronger than
  user safety needs and avoids a flag case-split.
- **`upt_acc_wf`'s excluded middle.** A leaf with `X=1, R=0` (execute-only
  user page) is neither User-ok nor User-denied at `mxr=0` and is excluded by
  `upt_acc_wf`. xv6 never builds one; if `uvm*` ever needs `PROT_EXEC`-only
  pages this is the conjunct that has to be generalized.
