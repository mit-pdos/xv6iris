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
2. **[x] The U-mode lane** — LANDED (design: `../design/uk-engine.md`;
   "Stage 3, as landed" in `../design/user-wp-slot.md`).  The owner ruled
   (a) the key carries the per-page permission map as a projection
   (`UserPerm.perm_of`, lazy pages filled RW — the lane's decision, argued
   in `UserPerm.v`'s header), and (b) the existing engine and sh/echo/init
   stay as they are, with a NEW engine beside them (`UkStep.v`, `UkLeaf.v`,
   `UkStore.v`) against `uvb`/`ukont`/`uexec_ret`; `sync` is re-proved on
   it (`UkSync.v`) and `USyncKernel.sync_uexec_slot` has no assumption.
   `sync_entry_tbl` / `sync_entry_tbl_refuted` are gone;
   `UexecCond.cond_entry_slot : □ uexec_wp -∗ uslot W` decides the gate.
   NOT ported (sync needs neither, the rewrite is mechanical):
   `WpUmodeLoad.v` → `UkLoad.v`, `WpUmodeBranch.v` → `UkBranch.v`.
   `usys_mem_ok`'s sbrk row: the image half at an existential size, the
   permission half `usys_sbrk_perm` (unchanged / grown by a page set at
   RW / shrunk by a page set); `UsysMemOkSpec.perm_of_grow` proves the
   grow shape from the kernel's facts, the SHRINK bridge is a premise
   (`sysc_mem_ok_usys_sbrk`) until `growproc_ok`'s shrink arm exposes the
   vpn run `uvmdealloc` drops.  The proc_ptm ruling LANDED (`cf70e89c0`)
   as `user_ptm_inv pt sz M` — see `../design/uk-engine.md` for why the
   literal `proc_ptm` could not back an executing bundle — with the
   store leaf's transparent fault arm built from the generic tier's own
   fault machinery.  NEW J OBLIGATION from the landing: the loop must
   discharge `usz_ok (uint (pv_sz V))` at resume — find or add the
   kernel-side invariant that pins `p->sz` below the trampoline region
   (growproc's own bound check is the likely source).
3. **[ ] Milestone J** (§4): the kernel side switches to `ukont`'s
   shape.  **THE KEY'S IMAGE VIEW IS RULED (owner, 2026-08-28): option
   (A), the `proc_ptm` re-key** — the owner's principle, verbatim: the
   user process cannot tell what is going on under lazy allocation, so
   the abstraction must NOT distinguish lazy vs allocated; the key's
   image is ALWAYS the lazy view.  Accordingly
   `uvb`/`trapped_machine`'s image conjunct becomes `proc_ptm pt sz M`
   (`sz` travels beside `π`).  Found while cutting J's stages; the old
   `UexecSlot.v` §3 header deferred exactly this to J.  The landed `UexecRet.v` is
   two-minded about `uvis_M`: `uexec_ret`'s ecall arm feeds it to
   `usys_mem_ok`, whose rows are LAZY-view facts (`sysc_mem_ok` verbatim;
   vmfault/copyin are noops on it, copyout to a lazy page is a pure
   window), while `trapped_machine`/`uvb` feed the same `uvis_M` to
   `user_pt_inv`, whose `umem_own` pins `dom M = uva_dom pt` — the
   MAPPED view.  On the lazy reading the kernel can NEVER supply
   `uvb`'s `user_pt_inv pt (uvis_M W)` for a genuinely lazy process
   (the GAP-premise trap, one tier up from `sync_entry_tbl`); on the
   mapped reading the vmfault arm is NOT transparent (the mapped image
   gains the zero page vmfault maps) and the window rows are false
   (copyout to a lazy page grows the dom by a page, `umem_wr` says
   only the window moved).  §3.3/§4's own wording — the image
   "unchanged on interrupt/vmfault" — is the lazy reading.  Options
   priced:
   - **(A) RULED: re-key `uvb`/`trapped_machine`'s image conjunct
     to `proc_ptm pt sz M`** (the lazy-view resource; `sz` is already
     `uslot`'s guard binder).  `SpecVmfault`'s theorem is literally
     `proc_ptm P sz M -∗ … proc_ptm (uptd_insert P …) sz M`, so the
     transparent arm is the existing theorem's shape; the residue seam
     becomes trivial (`proc_priv U ⊣⊢ proc_priv_nopt … ∗ proc_ptm …`).
     Engine cost: the leaves convert `proc_ptm` to the walker resources
     for the MAPPED submap via `ProcPtOwn` §5c'; the STORE leaf gains a
     transparent-fault arm (store to a live-unmapped page traps, the
     continuation is the program's own IH at the SAME key — the lazy
     image and the filled `perm_of` don't move; guardedness pays for
     the re-execution), and the same treatment covers loads when they
     port.  No new entry facts owed by sync's constructor.
   - (B) The old §3-header form: `uvb` ∀-binds `Mm ⊆ uvis_M W` with
     `⌜dom Mm = uva_dom pt⌝ -∗ user_pt_inv pt Mm`.  Same semantics as
     (A) spelled through `user_pt_inv`; keeps two image vocabularies
     alive in the bundle and still needs the store fault arm.
   - (C) Mapped key: `uexec_ret` gains an explicit page-fault arm at
     the grown key and `usys_mem_ok`'s window rows get "∪ the zero
     pages copyout mapped".  Transparency dies; contradicts §3.3/§4's
     wording; every row uglier.  Not recommended.
   The re-key runs as its own green-gated lane BEFORE the residue/loop
   stages; the BOUNDARY EXPOSURE is ruling-independent and proceeds
   beside it.  Boundary exposure (the round's post names the resume
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

## §4a J1a — boundary exposure, planned 2026-08-28 (execute in this order)

The trap round's posts must NAME the resume user-visible state.  Planned
against the tree at `1e08893ae`; the full draft (exact statements, all
twelve composition sites with provenance) was a session artifact — the
durable content is here.

- **The enabler is an INDEX on the residue**: `usertrap_res` /
  `_parked` / `_bare` gain one trailing `(U : ustate)` (the ∃ V M
  narrows to the index; `pt` stays).  A ∀-bound datum with only a pure
  premise is contentless — the relation must anchor to a resource, and
  the indexed residue is that resource.  The nine arm sites mention the
  residue only partially applied, so they do not change; ~240
  one-token edits over 14 files.
- **The round relation** `uround_ok sc tf M π tf' M' π'` (new
  `UexecRound.v`), keyed by `decide (sc = uecall_scause)` — the same
  test the dispatch's `c.li a5,8; bne` performs: ecall →
  `usys_num tf = USYS_exec ∨ ∃ r, uround_bump_ok tf tf' r ∧ usys_mem_ok …`;
  everything else → `uround_id_ok tf tf' ∧ M' = M ∧ π' = π`.  The bump
  is stated on the RESUME PROJECTIONS (`tf_resume_gpr0`/`tf_resume_pc`),
  not `tf' = bump_tf tf r`: the actual list differs in the four kernel
  words `prepare_return` re-arms, so the projection form is what is
  provable.  `tf_ueq` (new `TfUser.v`: equality at epc + words 5..35)
  with congruences is the vocabulary that crosses `prepare_return`.
- **Facts that exist NOWHERE today** (each a lower-spec obligation):
  (R2) the dispatcher pins nothing about `pv_tf (us_V U')` — each of
  the 22 arms owes `pv_tf` unchanged (the a0/epc writeback is AFTER the
  dispatcher, in `sysc_ret_tail`), exec escaping; (R3) same for
  `pv_upt`/`pv_sz` on the 20 non-sbrk non-exec arms (`uk-engine.md`
  already owed this); (R4) `perm_of` under `uptd_insert` (vmfault's
  fill-transparency) is argued in `uk-engine.md` but UNPROVED, and
  `SpecVmfault` may not pin the inserted leaf's flags; (R5) sbrk's
  shrink permission bridge still premises on `growproc_ok` exposing the
  dropped vpn run; (R6) one `bv` lemma tying the code's sign-extended
  `+4` to `add_vec_int`; (R7) `ret_pc` and `mepc_val` are the same term
  under two names — `ret_pc_idem` wanted.
- **Stages, each green-gated**: S1 pure vocabulary (`TfUser.v`,
  projection congruences); S2 `UexecRound.v`; S3 `user_trap_frame_at`
  (parameterized frame, additive); S4 the residue index (the long
  pole, pure re-typing); S5 = R2+R3 through `SpecSyscall` /
  `ProofSyscall` / the 22 arms — PRICED 2026-08-28, CHEAP (~120-140
  mechanical lines, proof-side only, NO spec strengthening) with the
  clauses RESTATED to what is true: (i) literal `pv_tf` equality is
  FALSE — `sysc_ret_tail`'s own `sd a0,112(s2)` is the writeback — the
  provable clause is `∃ w, pv_tf (us_V U') = <[tf_arg_idx 0 := w]>
  (pv_tf (us_V U))`, and the a0-tied variant (w = the return value) is
  NOT needed: `uexec_ret`'s ecall arm ∀-binds r, the kernel
  instantiates at the stored word, and only exec's row constrains it
  (kexec's failure arm already pins -1); (ii) literal `pv_upt`
  equality is FALSE on the 11 buffer-touching arms — copyin/copyout
  lazy faults grow `ud_um` — the true clause is `uptd_ext`, and π' = π
  then follows from R4's lemma stated ONCE over RW-leaf extensions
  (serving the vmfault arm and the syscall arms alike); (iii) `pv_sz`
  verbatim, free on all 20.  Every parking arm (wait/pause/pipe)
  already states its post at a syntactic updater of the entry U, so
  the parked reacquisition is pre-pinned; fork's parent returns the
  literal U; exec and sbrk escape by `sysc_num` guards discharged off
  `sysc_arm_goal`'s own `Hnum`; 16 arms are eq_refl one-tokeners, 5
  need ~6-line iAssert widenings, fallback included.
  S6 = R4 (state the lemma over RW-leaf `uptd_ext`, not just one
  `uptd_insert` — see S5's (ii)); S7 the transparent arms with a temporary ecall escape;
  S8 the ecall arm (route the framed `sysc_mem_ok` at
  `ProofUsertrapSys.v` ~:502-528 through `UsysMemOkSpec`); S9 the
  register-file/pc tie in `uservec_post` (the residue's 36 peeled tf
  words ARE `pv_tf (us_V U')` under the index, and `userret_gpr` at
  them is `tf_resume_gpr` DEFINITIONALLY) and the loop's new intros.
  S5/S6 are independent lanes; S4 waits for S5's price.
- The image half of `uround_ok` is stated at the LAZY tier (the
  residue's `us_M`), which the proc_ptm ruling made the key's view —
  the plan neither depends on nor duplicates the re-key lane's work;
  `uservec_post`'s `user_pt_any pt'` conjunct is NOT touched at J1a
  (it re-cuts with `uvb` when the loop switches).

## §5 Session-local artifacts (durable parts lifted into this file)

The per-lane sweep log (tooling notes, per-file decisions, the raw
inventory) and the probe's wart report lived in a session scratchpad;
everything load-bearing from them is in this file, in
`design/user-wp-slot.md`, and in the landed code and comments.  The
conversion tooling (`addarg.py`/`mkrec2.py` family) was ephemeral —
§2's idioms are what mattered.  The probe patch equals the in-tree
`UexecCond.v`; the probe's five warts are folded into §3 (items 3, 4,
5, 6).
