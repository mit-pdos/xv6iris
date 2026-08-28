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
- The trapframe-keyed slot `uexec_slot` + the conditional-mint probe
  machinery (`UexecCond.v`: decidable `text_region_eq`,
  `cond_entry_slot`/`_gated` choosing generic-vs-sync by
  `destruct (decide …)`) and `USyncKernel.sync_uexec_slot` (sync's
  entry deposit; `uv_cap` is its one assumption) are IN THE TREE with
  no kernel consumer yet.
- The `proc_pt_any` ELIMINATION CAMPAIGN is through tier 3 (see the
  DAG in §2): 157 → 129 occurrences; readers-into-user-memory state
  the `umem_wr` window as an EQUATION, writers-from-user-memory are
  same-`M`.

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

## §1 NEXT LANE, fully specced: the `uvis` re-key (owner-ruled)

The slot must be keyed on the ACTUALLY-user-visible state — a process
observes its va-keyed memory and registers, never PPNs.  New record
`uvis := { uvis_tf : list (mword 64); uvis_M : gmap Z (bv 8) }` with
`uvis_of : ustate -> uvis`; `uexec_slot (W : uvis)` UNIVERSALLY
QUANTIFIES the realizing descriptor inside
(`∀ P, ⌜loop_ok C P⌝ -∗ … user_pt_inv P (uvis_M W) … Rut P …`),
exactly parallel to its ∀-dead register-file base — and exactly the
∀-descriptor form the fork clause needs for the child (same `M`, fresh
table).  `tf_resume_*` read `uvis_tf`; `uexec_slot_congr` collapses to
tf/M equality; `sync_uexec_slot`'s table-dependent entry conditions
(`sync_layout P`, stack facts) move inside the `∀ P` as guards.
SMALL BY CONSTRUCTION: no kernel proof consumes `uexec_slot` yet, so
this touches `UexecSlot.v`/`UexecCond.v`/`USyncKernel.v` only.
`ustate`/`proc_priv` keep the descriptor exposed — the trap seams,
phase splits and table-moving specs are keyed on it.  `uvis_tf` keeps
the full 36-word list (kernel words 0/1/2/4 are dead weight in the
key; epc, word 3, is user-visible); a later refinement may restrict.

## §2 The `proc_pt_any` elimination campaign (owner-ruled), tiers 4–7

`proc_pt_any` is a spec smell — a contract holding it cannot say what
happens to the process state.  Bottom-up conversion (callees first),
then DELETE the definition.  "PRECISE" = post is an equation on the
image (`umem_wr`/`umem_grow`/shrunk view); "same-M" = caller's image
back; "GENUINE ∃" = the function really replaces the address space,
inlined `∃ M, proc_pt P M` at the very end.

**DONE: tiers 0–3.**  Deleted so far: copyinstr's ∃-twin,
`wp_copyin_sconf`(+body+proof), `wp_vmfault_sconf`,
`wp_uvmunmap_sconf` (+`BarePt.uptg_proc_pt`),
`either_copyout_post_any`.  Landed shapes to imitate:
`either_copyout_post` (window equation, `nat` prefix existential on
failure only), readi's post (NO existential — the failure arm's count
re-instantiated to cover the partial chunk), device-sourced bytes as a
length + byte FUNCTION (`d : nat`, `bs : nat -> bv 8`), never a gmap.
Remaining `wp_copyout_sconf` (∃-twin) callers: `ProofSysPipe` ×2,
`ProofKwait` ×1 (tier 4), `ProofKexecC` ×2 (tier 5).  Remaining
`_mem`-less leaves: `uvmclear` (tier 5 writes it; same-M — clearing
PTE_U moves neither domain nor PPN, the `uva_*_set_same` algebra is
the recipe), `proc_freepagetable` (tier 7; callers give the table
away, the honest form may stay ∃).

**TIER 4 — syscall dispatch (unblocked, next after §1):**
`SpecSysRead`/`SysFstat` inherit the `∀ d bs` window (their proofs
already re-form the block at `umem_wr (us_M U) (S4 !!! Ra1) dw bsw`);
`SpecSysWrite` drops `∀ M'`; `ProofSysPipe` ×2 + `ProofKwait` ×1 move
to `wp_copyout_sconf_mem`; `SpecSysSbrk`/`SpecGrowproc`+proofs become
PRECISE at `umem_grow` (uvmalloc/uvmdealloc `_mem` forms exist);
`SpecSysWait`/`SpecKwait`; capstone: `wp_syscall_sconf` re-keyed so
the dispatcher's post threads each arm's own effect.
**TIER 5 — exec cone:** first `SpecUvmclear`'s `_mem` form; then
ProofKexecB2/B3/C/D/Seam/Tail re-spell their crossings; kexec's post
is honestly ∃ for now — its PRECISE form (image = the loaded
segments) is also the future exec-deposit prerequisite for
sync-linking, so consider doing it precisely here.
**TIER 6:** `ProofUservec.wp_uservec_pt` (1 occurrence).
**TIER 7 — residue crossings, then the kill:**
`ut_res_pt_open/close` family (7 across
SpecUsertrap/ProofUsertrap/UtResFits/UsertrapRes),
`SpecFreeproc.fp_pt` + dormant ZOMBIE arms,
`ProofKforkParts.kfk_of_priv`, `ProofKforkB6.kfk_prologue`, `BarePt`,
`proc_freepagetable` — each becomes an inline `∃ M, proc_pt P M` at
its own site; FINALLY delete `proc_pt_any`/`proc_pt_at_any` and their
~22-lemma family in `ProcPtOwn` (re-base survivors on `proc_ptm`).
**Loose ends:** `umem_wrote_of`, `cr_win_0` (unused 2-line API
companions), `ProcPtOwn.proc_pt_page_acc_vmfault` (caller-less).

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

## §3 After the campaign: the road to a verified process in SystemAdequacy

All owner-ruled; chronological intent:

1. **Milestone J — boundary-row circulation** (plan in §4): the slot
   becomes STORAGE-FREE (never a conjunct of `proc_priv` or
   `ut_own`); explicit rows on the trap-chain boundaries; usertrap's
   precondition carries the CAUSE-INDEXED shape
   (`uexec_ret sc_v … := if sc = ecall then uexec_slot_sc else
   uexec_slot`, coupled to the `sc_v` the boundary already names);
   `ut_own`'s current slot row and accessors are DELETED then.
2. **The syscall shape**: at an ecall the u-mode side returns
   `uexec_slot_sc := ∀ r, uexec_slot ⟨V[epc := epc+4][a0 := r]⟩ M`
   (universal over the return register, everything else exact, over
   the BUMPED trapframe); buffer syscalls later add region-universals
   over `M` windows.  Transparent traps (device interrupt) return the
   precise slot.  Sync fits entirely (sync = the sc shape; exit's
   return is never consumed).  During the excursion the cause-shaped
   WP travels in usertrap's PROOF CONTEXT (mid-syscall parks capture
   it in the closure); the deposit lands where the shape turns
   precise — immediately on the transparent arm, at
   instantiation-at-ret on the syscall arm.
3. **The fork clause**: fork's spec takes TWO deposited WPs — child
   (`a0 = 0`) and parent (`a0 ∈ {pid, −1}`, the failure arm consumes
   no child WP) — same va-keyed `M`, `V_child` = parent's modulo a0
   plus fresh table (the `uvis`/∀-descriptor keying makes this work);
   kfork's existing "parking consumes a WP" premise takes the child
   half, replacing today's generic mint in `ProofSysFork`.  The park
   channel needs `pv_upt`/`pv_tf` preservation equations beside its
   existing `pv_fdg` one (`uexec_slot_congr` is already in-tree).
4. **Boundary exposure** (blocks keyed-slot runs): the round's post
   (`wp_uservec_pt`/`uservec_post`) must expose BOTH agreement halves
   — userret's RESTORE (`mf = tf_resume_gpr b V'`,
   `ret_pc uepc = tf_resume_pc V'`; already stated at
   `wp_userret_pt`'s own level, existentially hidden in the
   composition) and uservec's SAVE (the post-trap `V'` records the
   trapped registers) — against slotted residue variants whose
   binders name `V'`/`M'`.
5. **Discharge `uv_cap`** (turns `sync_uexec_slot`'s one assumption
   into a theorem): reshape the Umode tier's trap exits onto the
   paired return channel; the tier's frames (`uv_trap_frame`,
   `uv_run`) gain a `Rut` conjunct (the `□`-cap vs linear-residue
   tension); the DEPOSIT-COVERING formulation is deliberately
   undesigned — it cannot be pure (read()'s widening relates
   delivered bytes to FS state) and gets designed against the first
   concrete obligation HERE.  Also owed: the reverse `UmodeKernelTie`
   movers re-supplying `user_pt_inv`'s three pure facts
   (`dom`/`uva_pa_inj`/`upt_acc_wf`) from the table on the way back.
6. **The probe cycle** (owner's method): the userinit conditional
   mint (`UexecCond.cond_entry_slot_gated`, in-tree) is the standing
   forcing function — apply as an uncommitted patch, find the next
   precise obligation, land the fix green, re-apply.  Userinit is
   PLUMBING-ONLY (its process's user map is empty — no uvmfirst in
   this userinit); the semantic sync-branch forcing arrives with
   exec, whose image identification eventually connects to the
   ELF/namei story (`namei-pinned-lookup.md`, gated on the owner).
   Gate `sync_layout`-first so the dumped literal is never reduced
   (a bare `simpl`/`cbn` on goals MENTIONING it hangs — fs-img.md's
   first trap bullet).
7. **Representation notes**: `wp_uvmcopy_sconf` already returns the
   parent's image on the nose; `wp_copyinstr_sconf_mem` exists; the
   old "vmfault representation wart" is RESOLVED by the lazy view.

## §4 Milestone J plan (as specced, unchanged)

`uexec_wp` keeps its fixpoint/return channel.  The slot travels only
through boundary rows: slotted residue VARIANTS
(`∃ N V av M, ⟨rows⟩ ∗ S V M`, the shape functional `S` chosen by the
boundary); usertrap's pre takes `S := uexec_ret sc_v`; the arms'
posts and the composed round's post carry the PRECISE slot at the
final key plus the §3.4 agreement equations; the loop applies the
keyed slot from the round's post; the park channel's closer row goes
keyed under the binders it already receives (`V'` is an argument;
`M'` joins).  `Rut` returns to the plain bare form (the hole trick
dies).  The generic inhabitant remains a Löb proof returning itself;
mints stay creation-only.

## §5 Session-local artifacts (durable parts lifted into this file)

The per-lane sweep log (tooling notes, per-file decisions, the raw
inventory) and the probe's wart report lived in a session scratchpad;
everything load-bearing from them is in this file, in
`design/user-wp-slot.md`, and in the landed code and comments.  The
conversion tooling (`addarg.py`/`mkrec2.py` family) was ephemeral —
§2's idioms are what mattered.  The probe patch equals the in-tree
`UexecCond.v`; the probe's five warts are folded into §3 (items 3, 4,
5, 6).
