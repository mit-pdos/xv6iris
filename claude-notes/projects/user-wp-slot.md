# Project: the per-process user-execution WP — handoff state & worklist

**WHAT THIS PROJECT IS.**  Making the WP that userret runs a per-process
resource so that VERIFIED user programs (sync first) can run inside the
whole-system theorem in place of the generic-safety WP.  Everything
landed so far is on `main` and green; the design as built is
[`../design/user-wp-slot.md`](../design/user-wp-slot.md) — read it
first.  This file is what is LEFT, in execution order, plus the
operating rules a successor needs.

**STATE AT HANDOFF** (HEAD `512893e4`, full build EXIT=0, `audit-only`
at the sanctioned 13 assumptions, tracked dumps unchanged):

- The CIRCULATING WP (milestone G + lane H): `uexec_wp` is a guarded
  fixpoint with a paired return channel; userret extracts it, the user
  WP returns its successor at the trap, the trap-entry seam re-deposits;
  a WP is MINTED at exactly two process-creation sites (userinit's
  park, sys_fork's kfork call — `grep uexec_wp_gen` is the proof);
  kfork's contract consumes a WP for the child it parks.
- `proc_priv γf pa pid (U : ustate)` with
  `Record ustate := { us_V : pprivate; us_M : gmap Z (bv 8) }`, memory
  at the LAZY sz-region view (`proc_ptm`; vmfault/copyin are noops on
  `M` by `SpecVmfault`'s `proc_ptm` theorem).  Preservation of the WP's
  precondition BY SIGNATURE for functions that do not touch user
  memory.
- The trapframe-keyed slot `uexec_slot (W : uvis)` (table ∀-bound
  inside) + the conditional-mint probe
  machinery (`UexecCond.v`: decidable `text_region_eq`,
  `cond_entry_slot`/`_gated` choosing generic-vs-sync by
  `destruct (decide …)`) and `USyncKernel.sync_uexec_slot` (sync's
  entry deposit; `uv_cap` is its one assumption) are IN THE TREE with
  no kernel consumer yet.
- The `proc_pt_any` ELIMINATION CAMPAIGN is FINISHED as far as it is
  worth taking (§2).  NO CONTRACT in the tree reads at a named ∃:
  readers into user memory state the `umem_wr` window as an equation,
  writers from user memory are same-`M`, sbrk/growproc are equations
  on the image at every arm, the syscall dispatcher says which user
  bytes each table index can have moved, all five ∃-twins are gone,
  and the nine honestly-existential contracts write their ∃ out.
  `proc_pt_any` itself SURVIVES as a proof-internal spelling, with a
  banner at its definition; §2 has the price of deleting it and why
  the owner shelved that.

## §0 Operating rules (hard-won; violating these cost real time)

- Builds run on the GCP VM (`claude-notes/remote-build-gcp.md`) with
  the dump-guard flags; `run-on-gcp … -k proofs` is ALSO the warm
  edit/check loop (~90 s) — the local `.vo` tree is stale.  ONE build
  per remote tree: never run two lanes' builds concurrently.
- THE GATE before any push: full build with the EXIT sentinel written
  INTO the log and grepped (never trust a pipeline's exit status; a
  `;` before `git push` once pushed a red tree), `audit-only` byte-
  compared against the sanctioned 13, `md5sum kernel-rocq/*.v
  user-rocq/*.v` unchanged.  After any rebase, re-gate before pushing.
- Upstream moves fast (durable-disk + fs-syscall-specs lanes).  Their
  new files now speak `ustate`, but if one arrives on the old
  interface the fix idiom is five substitutions:
  `(V : pprivate)`→`(U : ustate)`, applications at `U`,
  `pv_* V`→`pv_* (us_V U)`, `upd_upt V P'`→`us_upt U P'`,
  `upd_usM (us_upt U P') M'`→`us_upt U P'` where the callee went
  same-M.
- Orchestration per durable-notes: the coordinator owns specs/design;
  subagent lanes do the proofs and MUST stop-and-report on design
  friction rather than force (a hard proof usually means a wrong
  spec).  Nothing commits without a green gate and coordinator review;
  the OWNER rules on design questions — when asking, explain the
  issue, considerations, constraints, not just the question.

## §1 The `uvis` re-key — landed

The slot is keyed on the user-visible `uvis` record (trapframe words +
image), the realizing table ∀-bound inside under `loop_ok`; described
in `../design/user-wp-slot.md` §"The two WP forms".  Nothing remains.

## §2 The `proc_pt_any` elimination campaign (owner-ruled) — landed

`proc_pt_any` is a spec smell — a contract holding it cannot say what
happens to the process state.  Bottom-up conversion (callees first),
then DELETE the definition.  "PRECISE" = post is an equation on the
image (`umem_wr`/`umem_grow`/shrunk view); "same-M" = caller's image
back; "GENUINE ∃" = the function really replaces the address space,
inlined `∃ M, proc_pt P M` at the very end.

**DONE: tiers 0–6.**  Every ∃-twin in the tree is deleted —
copyinstr's, `wp_copyin_sconf`, `wp_vmfault_sconf`,
`wp_uvmunmap_sconf` (+`BarePt.uptg_proc_pt`), `either_copyout_post_any`,
and then `wp_copyout_sconf`, `wp_uvmalloc_sconf`,
`wp_uvmdealloc_sconf`, `wp_uvmclear_sconf`, `wp_uvmcopy_sconf` (with
`ProofUvmcopy`'s ~90-line private `uc_*` bridge, which existed only to
prove one of them).  The caller-less companions are gone too
(`umem_wrote_of`, `cr_win_0`, `ProcPtOwn.proc_pt_page_acc_vmfault`).

Landed shapes to imitate: `either_copyout_post` (window equation,
`nat` prefix existential on failure only), readi's post (NO existential
— the failure arm's count re-instantiated to cover the partial chunk),
device-sourced bytes as a length + byte FUNCTION (`d : nat`,
`bs : nat -> bv 8`), never a gmap.

**The syscall layer, as landed.**  `sys_read`/`sys_fstat` inherit their
callee's WINDOW at the syscall's own buffer argument (which is now a
NAMED parameter of the contract, not merely assumed to exist);
`sys_write` is same-`M`; `sys_pipe` composes its two 4-byte copyouts
into one `d <= 8` window at the fd array (`umem_wr_app`, adjacent runs);
`kwait`/`sys_wait` state a `d <= 4` window at the status pointer, with
`d = 0` on the null-pointer and no-child arms; `growproc_ok` and
`sys_sbrk_ok` gained `(M M' : gmap Z (bv 8))` and pin the image on
EVERY arm (`umem_grow` on a grow, `umem_del` on a shrink, unchanged on
failure and `n = 0`).  The lazy path needed a primitive nothing in the
tree had — grow the lazy view by SIZE ALONE, table standing still —
now `ProcPtOwn.umem_lazy_grow_sz` / `proc_ptm_grow_sz` over
`UserPtTree.pgroundup_mono` / `uva_live_mono`.

**The capstone, as landed.**  `SpecSyscall.sysc_mem_ok V V' M M'` says
WHICH USER BYTES a syscall can have moved, keyed by `sysc_num V` (the
a7 word, trapframe index `tf_arg_idx 7`, read signed at 32 bits exactly
as the C does).  `sysc_window` is the table of the four copyout entries
and the argument each bases its window at (wait→0, pipe→0, read→1,
fstat→1); sbrk gets `sysc_sbrk_img`'s three arms; exec is
unconstrained, its image being `SpecKexec`'s to pin; the other sixteen
read `M' = M`.  It rides `sysc_hcont_ty` / `sysc_epilogue_tail` /
`sysc_ret_tail` as a pure premise, and `sysc_arm_goal` gained
`sysc_num (us_V U) = Z.of_nat k` so an arm can select its own branch.
Three discharge lemmas serve all 22 arms: `sysc_mem_ok_quiet`,
`sysc_mem_ok_window` (over the table, so one lemma covers all four
windows) and `sysc_mem_ok_sbrk`.

**TIER 7 — SHELVED, and priced first.**  Checkpoints ① (the precise
contracts and the ∃-twins) and ② (no contract reads at a named ∃) are
LANDED.  ③, deleting `proc_pt_any` itself, was priced against the
post-② tree and the owner shelved it.  The price:

- ten of the sixteen lemmas around it come back as the SAME STATEMENT
  with `∃ M, proc_pt P M` typed where `proc_pt_any P` stood —
  `proc_pt_any_unfold`, `proc_pt_ptm`, `proc_ptm_pt` (19 call sites,
  the most-used thing in the family), `proc_pt_acc_rep0`,
  `proc_pt_rebuild`, `proc_pt_split`, the `proc_pt_page_acc` accessor
  pair, and the `proc_pt_at_*` restatements;
- ~65 proof-internal call sites in the kexec and uvm cones, the trap
  residue, `BarePt` and `ProofKforkParts` change mechanically and
  prove exactly what they proved before;
- and `Typeclasses Opaque proc_pt_any` is LOAD-BEARING — it is what
  stops `iIntros`/`iDestruct` from silently opening the existential
  under proofs that never mentioned it.  Lane I measured that seam
  precisely: plain wand application goes through conversion and does
  not care whether the predicate is folded, but `iFrame`'s
  witness-then-match and `rewrite`'s syntactic pattern do.

**What was taken instead** — the part of the family that carries no
weight: `proc_pt_any_norm` and `proc_pt_any_root_valid` (no users
left), the whole `proc_pt_at_any` sub-family (nothing outside
`ProcPtOwn` holds it after ②; its one live consumer moved to the
STRONGER `proc_ptm_at_of_pt_at`), `proc_pt_any_ptm` (one direction of
`proc_pt_ptm`, which is an iff), and `proc_pt_any_data_irrel` re-based
on a general `proc_pt_data_irrel`.

`proc_pt_forget` and `proc_pt_any_wf_get` STAY: they are the fold and
the query interface of the predicate that stays, and replacing them
makes call sites longer, not shorter.

**IF ③ IS EVER RE-OPENED**, the thing that would make it worth doing is
not the name — it is milestone J's residue re-key, which turns
`SpecUsertrap`'s parked-table pair from an honest ∃ into a `(V, M)`-keyed
resource.  At that point the survivors shrink for a REASON rather than
by re-spelling, and the tally above should be re-taken.

**Conversion idioms (the campaign's learned rules):**
1. A leaf's `_mem` form is the PRIMITIVE; its `proc_pt_any` form is a
   five-line corollary that DIES with its last caller (the deleted
   `ProofCopyin.wp_copyin_sconf` was the recipe: `proc_pt_ptm` in,
   `proc_ptm_pt` out).
2. Converting a callee's post breaks callers whose specs don't move;
   the repair is SUBSTITUTION, not conversion (drop the `M'` binder,
   replace `upd_usM (us_upt U P') M'` with `us_upt U P'`; the
   caller's own ∃-post closes by unification).  Tell for the hidden
   variant: `iSpecialize: cannot instantiate … (upd_usM U Mx) … with … U`
   — the caller was passing a DIFFERENT image than its statement said.
3. A byte loop's window needs its cursor pinned to the entry address
   (`cur = pa_add dst k`) or the rounds' `umem_wr`s cannot compose;
   `umem_wr_app` needs no no-wrap side condition (runs are keyed by
   `add_vec_int`).
4. When a writer's post already carries a count, spend the failure
   arm's existential by RE-INSTANTIATING that count (readi), not by
   adding a second one.
5. OPEN THE ∃ AT THE CALLEE'S OWN UNREDUCED SIZE TERM.  A `_mem` leaf
   states its index as a `let` over its own register file (copyout's
   `uint szv`, uvmalloc's `uint (mm !!! Ra1)`); opening `proc_pt_any` at
   a size that is only PROPOSITIONALLY equal to it (`pgroundup szv`,
   tied by a hypothesis) fails `iSpecialize` with idiom 2's tell.
   `proc_pt_ptm` holds at EVERY `sz`, so the index is free — pick the
   callee's own term and the unification is definitional.

## §3 The road to a verified process in SystemAdequacy (re-cut 2026-08-28)

The design of record is `../design/user-wp-slot.md` §"The ruled design
for the user/kernel trap contract": `uexec_ret` (A), `ukont` (B), the
U-mode bundle `uvb` (C), and the five-step staging.  Lanes, in order:

1. **[x] `uvis`** — landed (`351f8dbf7`).
2. **[ ] The U-mode lane** (IN FLIGHT): new definitions beside the old
   (`usys_mem_ok` on the word list, `uexec_ret`, `ukont`,
   `trapped_machine`, `uvb`, the `uvb`-keyed `uexec_slot`), every
   U-mode leaf re-stated on `uvb`, `WpUmodeStep`'s trap arms and the
   program-level IH producing `uexec_ret`, sync re-proved,
   `USyncKernel.sync_uexec_slot` assumption-free; `uv_cap`/`uv_cap_gpr`/
   `uv_lin`/`uv_run`/`UmodeKernelTie` retired.  Kernel proofs untouched.
3. **[ ] Milestone J** (§4): the kernel side switches to `ukont`'s
   shape.  Boundary exposure (the round's post names the resume
   trapframe and image: `bump`'d on the ecall arm with `usys_mem_ok`,
   unchanged on interrupt/vmfault) is PART of this lane, not a
   separate item.  Mint sites: userinit (generic), fork's child (the
   parent's `uexec_ret` fork half — kfork's "parking consumes a WP"
   premise takes it; the park channel needs a `pv_tf` equation beside
   its `pv_fdg` one), exec-success (`cond_entry_slot_gated`).  `exit`
   consumes nothing.  `Rut_hole` and the old forms are deleted.
4. **[ ] Exec-site forcing function**: apply sync's constructor at
   exec's success arm; the first obligation will be exec's post
   saying what image/table it built (today `∃ U'` with `kexec_ok`
   pinning only the trapframe and size) — genuinely open until file
   content is tracked (`namei-pinned-lookup.md` / fs-syscall-specs
   lane P are NOT integrated).  Gate `sync_layout`-first so the
   dumped literal is never reduced (a bare `simpl`/`cbn` on goals
   MENTIONING it hangs).

Representation notes still true: `wp_uvmcopy_sconf` returns the
parent's image on the nose; `wp_copyinstr_sconf_mem` exists; the old
"vmfault representation wart" is RESOLVED by the lazy view.

## §4 Milestone J plan (as specced; re-read against §3.3)

`uexec_wp` keeps its fixpoint; its trap premise becomes `ukont`.  The
slot travels only through boundary rows: slotted residue VARIANTS
(`∃ N V av M, ⟨rows⟩ ∗ S V M`, the shape functional `S` chosen by the
boundary); usertrap's pre takes `S := uexec_ret sc_v`; the arms' posts
and the composed round's post carry the PRECISE slot at the final key;
the loop applies the keyed slot from the round's post; the park
channel's closer row goes keyed under the binders it already receives.
`Rut` returns to the plain bare form (the hole trick dies).  The
generic inhabitant remains a Löb proof returning itself; mints stay
creation-only.

## §5 Session-local artifacts (durable parts lifted into this file)

The per-lane sweep log (tooling notes, per-file decisions, the raw
inventory) and the probe's wart report lived in a session scratchpad;
everything load-bearing from them is in this file, in
`design/user-wp-slot.md`, and in the landed code and comments.  The
conversion tooling (`addarg.py`/`mkrec2.py` family) was ephemeral —
§2's idioms are what mattered.  The probe patch equals the in-tree
`UexecCond.v`; the probe's five warts are folded into §3 (items 3, 4,
5, 6).
