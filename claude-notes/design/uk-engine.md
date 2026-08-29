# Design: the user-mode-on-kernel engine (`Uk*.v`)

The verified-user step engine stated against the KERNEL's trap contract
(`UexecRet.uvb` / `ukont` / `uexec_ret`) instead of the Umode tier's
assumed capability (`UmodeCap.uv_cap`).  It is the design's (C) from
`user-wp-slot.md` ("The ruled design for the user/kernel trap contract")
built as NEW FILES beside the old engine, which is left as-is: the sh/echo/
init proofs still run on `WpUmode*.v`, and `sync` runs on both.

Files, bottom-up: `UserPerm.v` (the per-page permission view; below the
slot), `UkStep.v` (the engine), `UkLeaf.v` (the register-only leaves),
`UkStore.v` (the store leaf), `UkSync.v` (sync on the new engine),
`USyncKernel.v` (the slot constructor), `UexecCond.v` (the decidable gate).

## The permission map is a projection, and the lazy pages are filled RW

`UserPerm.v`.  `Record uperm := { up_X; up_W }` — the two bits a user page
can differ in.  `perm_of um sz : gmap (mword 27) uperm` is

    omap perm_leaf um ∪ gset_to_gmap uperm_rw (live_pages sz ∖ dom um)

— every leaf of the user map with U set, reduced to its X/W bits
(`perm_leaf` is `None` at U = 0: the guard page `uvmclear` strips U from is
mapped, has bytes in `M`, and is NOT in the map, because nothing the
process does reaches it), UNION every page below `PGROUNDUP sz` that is not
mapped yet, at `{X := false; W := true}`.  `uvis_of U` computes
`uvis_perm := perm_of (ud_um (pv_upt V)) (uint (pv_sz V))`.  `uperm_at π va
:= π !! svpn_of va` is the byte-vs-page helper.

**Why the lazy pages are in the map (the decision the owner left to the
lane).**  `vmfault` maps a first-touched page `PTE_R|PTE_W|PTE_U`
(kernel/vm.c), so as the process sees it a live-unmapped page IS a
writable page whose bytes happen to be zero; the lazy image view already
says the zeros, and this projection already says RW.  That is what makes
the page-fault arm of `uexec_ret` TRANSPARENT (the returned slot is at
the same key): neither the image nor the map moves under `vmfault`.  Had
lazy pages been ABSENT, `vmfault` would change the key and the
transparent arm would be false as stated.  The price is `sz` beside the
map in the projection — but `sz` is the kernel's other address-space
datum, so J's discharge of `perm_of pt sz = uvis_perm W` is by
computation — and the leaves never look at it: a FETCH needs X, which no
filled page has, so an X page is a mapped page (`perm_of_X_mapped`); a
STORE needs W and a byte present in the image, and at the tier the
leaves run on (`user_pt_inv`'s `dom M = uva_dom pt`) a present byte is a
mapped page (`image_byte_mapped`).  R is implied for every page in the
map: xv6 never builds a U leaf without R, and `upt_acc_wf` excludes the
execute-only and write-only shapes.

**The leaf-bit transfer** (`perm_of_X` / `perm_of_W` / `perm_of_R`: from
the key's bits to the model's `uleaf_ok acc w`) is proved by ENUMERATING
the six flag bits the permission check reads (`flags6`, 64 cases); the
byte an A/D variant carries is `pte_flags_byte_of_flags6`.  The trick
that keeps it to 64 × 1 `vm_compute`: `upt_acc_wf` gives ok-or-DENIED,
and a denial is a claim at EVERY machine state, so it is refuted by
evaluating at ONE concrete state (`dstate`, with mxr = 1) — no
computation ever runs on a symbolic state (the first attempt did, and it
did not finish).

**How the map moves** (`UsysMemOk.usys_mem_ok n tf r M π M' π'`): `π' = π`
on the sixteen quiet entries, the four windows and exec's failure arm;
sbrk's row is `usys_sbrk_perm π π'` — unchanged, or grown by a page set
at RW, or shrunk by a page set (both sets existential, as the size is).
`UsysMemOkSpec.perm_of_grow` proves the grow disjunct from the kernel's
own facts (same table, larger size); the shrink bridge is a PREMISE
(`sysc_mem_ok_usys_sbrk` takes `usys_sbrk_perm`), because the exact
page set is `uvmdealloc`'s run, which `SpecSyscall.sysc_mem_ok` does not
expose.  The other bridge (`sysc_mem_ok_usys`) takes `π' = π`, which is
each quiet/window arm's `P' = P`, `sz' = sz` to show at J.

## The contract, re-cut on the map

`UexecRet.v`, as landed:

- `ukb C pt Rut π` — the kernel obligation's LATER-FREE body:
  `∀ W' sc stv, ⌜uvis_perm W' = π⌝ -∗ trapped_machine … W' ∗ uexec_ret sc W' -∗ WP`;
  `ukont C pt Rut π := ▷ ukb …` (`ukont_unfold`).  The pure premise pins
  the trapped key's map to the one the kernel resumed the process under
  (user execution never changes it), which is what lets J re-apply the
  returned slot at the same table.
- `uvb C pt Rut π M m pc` carries `ukont C pt Rut π` last.
- `uslot W := ∀ h C pt Rut sz, ⌜loop_ok C pt⌝ -∗ ⌜perm_of (ud_um pt) sz = uvis_perm W⌝ -∗ uvb … -∗ WP`.
- `ukc π M m pc` — THE U-MODE CONTINUATION at a natural state, the same ∀
  over the bundle at `(π, M, m, pc)`; `uslot_ukc` says the slot is the
  continuation at the key's state, `uslot_run` that the slot at the
  trap-out key `uvis_of_run m pc M π` is `ukc π M m pc` (under x0 = 0 and
  a 2-aligned pc), `uslot_bump_run` the same after a returning syscall
  (`a0 := r`, `pc + 4`).
- `uexec_ret`'s ecall arms carry `M'` AND `π'` under `usys_mem_ok`;
  `bump W r M' π'`.

## The engine (`UkStep.v`)

It REUSES `WpUmodeStep.v`'s Sail-facing lemmas by import — landing
shapes, `uv_pre`, the page-table opener/re-former, the fetch/execute
bridges, `uv_land_close`, `uv_psi_trap` — none of which mention the
capability.  New:

- `uk_instr π M pc is_rvc i := ∀ pt sz, proc_pt_wf pt -> perm_of (ud_um pt) sz = π -> uinstr pt M pc is_rvc i`
  — the decode fact at every table realizing the key.  EVERY continuation
  re-binds the table (the resume after an interrupt comes back through
  `uslot`, which ∀-binds it), so the fetch obligation must hold at any
  table too.  A program gets it from its key facts once per instruction
  (`UkSync.uk_instr_of_sync`, through `sync_layout_of_key`).
- `uk_step_obl π Kc M m pc` — the fetch-onward obligation, at ∀ table
  with the guards and `uk_pt_pure pt M` (the three pure facts of
  `user_pt_inv` the Umode page half drops) as premises, taking
  `(R -∗ Rut pt ∗ ukb C pt Rut π ∗ Kc)`.
- `uk_ih π Kc M m pc` — the Löb hypothesis; `wp_uk_step_gen` proves it
  under a 2-aligned pc.  The payload at the cycle's tail is
  `uk_payload := uk_ih ∗ Kc ∗ Rut pt ∗ ukb` (the wrapper strips `ukont`'s
  later with everything else; `uk_psi_active` puts it back with
  `later_intro` when it rebuilds `uvb`).
- `uk_arm_intr` — the interrupt arm: `trapped_of_uv_trap_frame` turns the
  Umode trapped frame into `trapped_machine` at `uvis_of_run m pc M π`;
  `utrap_scause_intr_ne` selects `uexec_ret`'s transparent arm; the slot
  handed back is `uslot_run` of `uk_ih` applied to the obligation and the
  continuation — the program's own induction hypothesis at its current
  bundle, exactly as the design said.
- `wp_uk_retire[_later]` — the leaf funnel, statement-identical to
  `wp_uv_retire` with `uv_cap_gpr ∗ pc_is` read as `uvb` and the
  continuation as `ukc`; the section carries the ambient guard
  (`Hlo`, `Hpm`), which is what lets the retiring arm hand `uvb` at THIS
  table to a continuation that accepts any.
- `wp_uk_ecall` — the ecall driver: `uvb -∗ uexec_ret uecall_scause (uvis_of_run m pc M π) -∗ WP`
  (`utrap_scause_ecall`, via `RiscvExtras.scause_tower`).

`UkLeaf.v` is `WpUmodeLeaf.v` under a mechanical rewrite (39 leaves; the
proofs unchanged).  `UkStore.v` is `WpUmodeStore.v`'s §5–§6 with the
table's leaf premise (`ud_um pt !! svpn_of va = Some w ∧ uleaf_ok (Store Data) w`)
replaced by the key's `uk_store_ok va` (the page is a W page of `π`);
`wp_uk_store_later` derives the table leaf at each bound table from the
byte's presence (`image_byte_mapped`) and `perm_of_W`.  Loads and
branches are NOT ported (sync needs neither): `WpUmodeLoad.v` /
`WpUmodeBranch.v` port by the same rewrite, the load's table premise
becoming "the page is in `π`" (`perm_of_R`).

## sync on the engine (`UkSync.v`, `USyncKernel.v`, `UexecCond.v`)

`uk_xpage π va` / `uk_wpage π va` (decidable) and `uk_stack π M sp n`
(`uv_stack` with its leaf clause on the key; decidable) are the key-level
layout facts; `uk_stack_split` / `uk_stack_slot` are `UmodeAbi`'s
budget lemmas re-read on the key.  A diverging function proves
`⊢ ukc π M m pc`; the returning stub takes `∀ ret, ukc …` as its
continuation.  `USyncKernel.sync_uexec_slot` is `uslot_ukc` plus
`wp_ksync_start`, with NO capability and no table premise.
`UexecCond.cond_entry_slot : □ uexec_wp -∗ uslot W` decides `sync_gate W`
(text, pc, X page, stack) and deposits sync's slot or the generic one.
`sync_entry_tbl` and `sync_entry_tbl_refuted` are gone.

## What milestone J now owes

- Build `ukont C pt Rut π` at `π := perm_of (ud_um pt) (uint (pv_sz V))`
  and meet `uslot`'s guard by `reflexivity` at resume.
- On the transparent arms (interrupt, page fault) re-apply the returned
  `uslot W'` at the same `(pt, sz)`: `uvis_perm W' = π` is `ukont`'s own
  premise.
- On the ecall arm, apply the returned `uslot (bump W' r M' π')` with
  `usys_mem_ok` discharged by `UsysMemOkSpec.sysc_mem_ok_usys` (`π' = π`:
  from each arm's `P' = P`, `sz' = sz`) or `sysc_mem_ok_usys_sbrk`
  (grow: `usys_sbrk_perm_grow`; shrink: the page-set premise, which
  needs `growproc_ok`'s shrink arm to say which vpns `uvmdealloc`
  dropped — today it says `M' = umem_del …` and `uptd`-level facts the
  kernel holds but `sysc_mem_ok` does not carry).
- fork's child: `uslot_congr` — same tf, same image, and the same
  PROJECTION (uvmcopy copies flags leaf for leaf, at a new size equal to
  the old one).
- exec-success: `cond_entry_slot` at the new `uvis_of U'`.
