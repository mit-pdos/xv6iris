# Coordinator checkpoint — user-wp-slot, 2026-08-28 (resume here if the session was cut off)

Written by the coordinating session while a proof lane was still running.
If you are a successor: READ THIS, then `projects/user-wp-slot.md` (§3 is
the worklist; the lane may have edited it ahead of its gate — trust the
GIT LOG, not the checkboxes), then `design/user-wp-slot.md` §"The ruled
design for the user/kernel trap contract" and (if it exists)
`design/uk-engine.md`.

## What the owner ruled this session (all final)

1. The slot is keyed on the user-visible state `uvis` (trapframe words +
   image) with the page table ∀-bound inside — landed `351f8dbf7`.
2. The user/kernel trap contract is re-typed: `uexec_ret sc W` (what a
   process hands back at a trap: per-cause, per-syscall keyed slots, with
   the pure `usys_mem_ok` table under the ∀; exec-success is a KERNEL
   mint; exit returns nothing), `ukont` (the kernel obligation with a
   CONCRETE trapped machine, the process instantiating), and the U-mode
   bundle `uvb C pt Rut M m pc` keyed on register file / pc / image —
   NEVER on the 36-word trapframe list (no `tf_set_*` algebra in the
   U-mode API; `uvis` conversion only at the trap boundary).  Design
   committed `09b66e352`; parallel-form definitions landed `53583a1b0`
   (`UsysMemOk.v`, `UsysMemOkSpec.v`, `UmodeRegs.v`, `UexecRet.v` with
   the `uslot` fixpoint; x0 pinned via `gpr_file_x0`; generic inhabitant
   `uexec_wp_uslot` proved).
3. Permissions: the lane proved the ∀-bound table made `sync`'s entry
   premise UNSATISFIABLE (`sync_entry_tbl_refuted`).  Ruling: `uvis`
   gains a per-page permission map `{X, W}` as a PROJECTION of the
   kernel's table (`uvis_of` computes it; nothing stores it), page-table
   structure stays hidden; `uslot`'s guard is `perm_of pt = uvis_perm W`.
   The tuple form `M : gmap Z (bv 8 * perm)` was considered and is a
   cheap mechanical switch later (only ~a dozen definitions inspect the
   image; the rest thread it) — revisit at milestone J if the per-arm
   permission equations are noisy.
4. The EXISTING U-mode engine (`WpUmode*`, `UmodeCap`, `UmodeSyscall`,
   `UmodeIo`, `UmodeKernelTie`) and the sh/echo/init proofs STAY AS-IS.
   A NEW engine (`Uk*.v`) is built beside them against `uvb`, and `sync`
   is re-proved on it so `USyncKernel.sync_uexec_slot` has no
   assumption.  Whether to port sh/echo/init or back-port the design is a
   LATER owner decision.
5. Exec's post cannot say what image it loaded until file content is
   tracked (the pinned-lookup port, fs-syscall-specs lane P, is NOT
   integrated) — the exec-site forcing function is worklist item 4,
   after milestone J.

## State at checkpoint

- HEAD `53583a1b0` (green, gated).  A lane was running the permission
  re-key + new engine + sync reconstruction with UNCOMMITTED edits to
  `UexecSlot.v`, `UexecRet.v`, `UexecCond.v`, `USyncKernel.v`,
  `UsysMemOk*.v`, `_CoqProject`, new `Uk*.v`/`UserPerm.v`, and the
  notes.  If those are still uncommitted: they are UNGATED.  Run the §0
  gate on the GCP VM (full build with the EXIT sentinel grepped,
  `audit-only` == the sanctioned 13, `md5sum kernel-rocq/*.v
  user-rocq/*.v` unchanged) before committing anything; if it is red,
  read the lane's notes edits for what it believed was done, and finish
  or revert per file.
- Kernel proofs MUST be unchanged by that lane (`git diff --stat` should
  show only U-mode/slot files and notes).
- Nothing has been pushed this session; the owner pushes.

## Operating incidents (do not repeat)

- The lane ran single-file `coqc` probes LOCALLY and exhausted the
  machine's RAM.  ALL compiles go to the GCP VM (`remote-build-gcp.md`).
- A check that grows past a few hundred MB / minutes on a small file is
  a DEGENERATE PROOF, not something to wait out: known culprits are any
  reduction/unification touching `SyncInstrs.sync_bytes` (`cbn [fst]`,
  `decide` on symbolic `M`, keep the literal behind opaque lemmas) and
  ssr `rewrite`/`iFrame` against the 32-insert `userret_gpr` chain
  (enumerate the 32 indices, peel per case).

## Next after the lane lands

Milestone J (worklist §3.3 / §4): the kernel loop, `usertrap_post`,
`uservec_post` and the mint sites switch to `ukont`'s shape; the
round's post names the resume trapframe (`bump`'d on ecall with
`usys_mem_ok`, unchanged on interrupt/vmfault) and the permission map
per arm; `Rut_hole` and the old forms are deleted.  Then item 4.
