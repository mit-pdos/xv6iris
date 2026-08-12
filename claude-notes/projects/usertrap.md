# Project: usertrap() — the C half of the user trap

`usertrap()` @ `KernelSyms.usertrap`, **262 bytes / 90 instructions**
(`CodeUsertrap.v`, `uti_*`). It is the function between the two trampoline
halves: uservec jalr's into it with `ra = uva 0x9c` (so it **returns straight
into userret**), and its return value in a0 is the user satp userret installs.

Prerequisites are all in place as of `74f28a7e`:

| callee | contract | status |
|---|---|---|
| `myproc` | `SpecMyproc` | PROVEN |
| `killed` / `setkilled` | `SpecKilled` / `SpecSetkilled` | PROVEN |
| `devintr` | `SpecDevintr` | PROVEN (kerneltrap's) |
| `vmfault` | `SpecVmfault` | PROVEN |
| `yield` | `SpecYield` | PROVEN, eb-generic |
| `prepare_return` | `SpecPrepareReturn` | PROVEN, index-generic |
| `kexit` | `SpecKexit` | PROVEN, index-generic (`74f28a7e`) |
| `syscall` | `SpecSyscall` | **ASSUMED** (`LinkSyscall` axiom), `syscall_env γf pj` |
| `printk` (unexpected-scause arm, 2 calls) | `SpecPrintkGen` | **ASSUMED** (`LinkPrintkGen` axiom) — the general path, not the panic one |
| `panic` (`"usertrap: not from user mode"`) | — | arm is REFUTED, see below |

So nothing about the *cones* blocks the proof any more. What blocks it is the
BOUNDARY, and that is what this note is mostly about.

## CHECKPOINT — where this stands, and how to pick it up

State as of **`f8edc216`** on `main` (pushed; full `iris/` build green; no
`Admitted`, no `Axiom` in anything below).

**The design is done and machine-checked. The WP walk is not written.** That
is the whole of the state: every question about *what usertrap's contract is*
and *what resources it holds* is settled and compiled, and no instruction of
the function has been stepped yet.

### What is on disk

| file | what |
|---|---|
| `iris/SpecUsertrap.v` | the boundary, **restated in the kernel tier** (the old one was unsatisfiable — §"THE BOUNDARY IS STATED IN THE WRONG WORLD"). `USERTRAP` now `Include`s a split-out `USERTRAP_RES`. |
| `iris/UsertrapRes.v` | `usertrap_res` DEFINED (`ut_trap` / `ut_env` / `ut_res`), `K_usertrap = 4 + K_syscall`, and the `<:`-checked module fit `UtResFits (SY : SYSCALL)`. |
| `iris/ProofUsertrapParts.v` | the pure obligations. |

Seven proven lemmas, and it is worth knowing what each buys before touching
anything:

- `ut_sconf_open` — `ut_sconf_closer` really is "the rest of `sconf`". It is
  `IntrDefs.sconf_at`'s idiom plus `cur_privilege` (userret's `sret` writes
  that cell, so the boundary must expose it).
- **`ut_trap_open`** — the boundary's raw machine state + `ut_trap` **is**
  `sie_cap_gpr m av false pj ∗ cpu_own 0 false pj C false`, with the dangling
  SIE quarter, the KPT receipt and the sret mirror falling out loose. *This is
  the lemma that says the restated boundary is right.*
- **`ut_exit_ms_ok`** — `usertrap_ret_ms` is DERIVABLE from what
  prepare_return hands back, not something usertrap arranges.
- **`ut_trap_csrs_fold`** — those three loose members + the written stvec cell
  + the handler contract **are** `trap_csrs`. This is the `csrw stvec,
  kernelvec` at +0x1e, i.e. the C comment, and its ORDER is a theorem.
- `ut_spp_bit` / `ut_spp_clear_eq` / `ut_spp_clear_neq` — the panic arm is
  dead. The last is the `neq_vec` spelling `wp_cbnez_fall_s_sconf` consumes.

### Resume here

Write the walk. §"Phase plan" has the per-instruction table for Phase A with
every leaf and every pure fact named and **checked to exist** — it is a
mechanical `iApply` chain, and `ProofPrepareReturn.v` (whose first four steps
are usertrap's +0x00..+0x06 with a frame two slots smaller) is the template
for the tactic idiom, the `set (M1 := …)` regfile tracking and the `pcw` /
`nz` / `rdok` discharges. Read, in order: this checkpoint, §"The restated
boundary", §"Phase plan", then `ProofPrepareReturn.v:105-235`.

Two process rules from the neighbours apply from the first line: put
`Set Printing Depth 40.` at the top of every proof file (usertrap proves over
`proc_priv`, so a failing tactic otherwise prints `tf_page`'s 4096 conjuncts —
a 40-minute non-answer), and close block seams by naming every conjunct rather
than with `iFrame` (the >19 GB non-termination).

`ProofUsertrap*.v` will be a functor over SYSCALL, PRINTK_GEN, MYPROC,
KILLED, SETKILLED, DEVINTR, VMFAULT, YIELD, PREPARE_RETURN, KEXIT **and
KERNELVEC** — the last because `intr_handler_spec kernelvec` is deliberately
NOT in the bundle (see §"Phase plan"); it is derived where it is needed.

### Settled — do not re-litigate

- **usertrap lives in the SHARED kernel-table tier and does not mention the
  kernel table at all.** Taking `tlb_inv_pt` as well would make the premises
  jointly unsatisfiable and the proof vacuous. §A.
- **The trapframe words and the parked user table are NOT in the contract**;
  `proc_priv` inside `usertrap_res` is their only owner. §B.
- **The post is a `wp_next true pj` crossing.** usertrap parks. §C.
- **`uc_mie C = MIE_S` costs nothing** — `UCfg` is applied nowhere in the
  tree, so no `ucfg` field changes. (Checked; conversion 3 below.)
- The three conversions owed to the trampoline halves are §"What is OWED",
  and the big one is kpt-share's already-predicted rework. **None of them
  gates the walk.**

### Two hoists owed (both deliberate, neither blocking)

- `ut_sconf_closer` + `ut_sconf_open` belong beside `IntrDefs.sconf_at`;
- `ut_spp_bit` / `ut_spp_clear_eq` belong beside `sstatus_read` in
  `WpGprCsrwC.v`, together with `ProofKerneltrapParts`' opposite-polarity
  `kt_spp_bit` / `kt_spp_set_neq`.

Both are where they are because editing the bottom of the tree costs a
near-total rebuild. Do them when something else has to touch those files.

## The CFG, read off the image

Offsets are `usertrap + x`. `s1 = p`, `s2 = which_dev`, `a5/a4` scratch.

```
  +0x00  prologue: 32-byte frame, ra/s0/s1/s2 saved
  +0x0c  csrr a5,sstatus; andi a5,SPP; bnez -> +0x84   (panic arm)
  +0x16  auipc/addi a5 := kernelvec; csrw stvec,a5     <-- INSTALLS THE KERNEL HANDLER
  +0x22  jal myproc; s1 := a0
  +0x28  ld a5,88(a0) (p->trapframe); csrr a4,sepc; sd a4,24(a5)
  +0x30  csrr a4,scause; li a5,8; beq -> +0x90         (syscall arm)
  +0x3a  jal devintr; s2 := a0; bnez -> +0xe8          (device arm)
  +0x42  scause == 15 / 13 ? -> +0xd0                  (vmfault arm)
  +0x56  printk x2; setkilled(p); j +0xa6              (unexpected scause)
  +0x84  panic("usertrap: not from user mode")         (REFUTED)
  +0x90  jal killed; bnez -> +0xc8 (kexit(-1) then falls into +0x96);
         p->trapframe->epc += 4; csrsi sstatus,2 (intr_on); jal syscall
  +0xa6  jal killed; bnez -> +0xf2 (s2 := 0; kexit(-1))
  +0xae  jal prepare_return; a0 := MAKE_SATP(p->pagetable); epilogue; ret
  +0xd0  vmfault(p->pagetable, r_stval(), scause==13); bnez -> +0xa6 else -> +0x56
  +0xe8  jal killed; beqz -> +0xfa; else kexit(-1)
  +0xfa  which_dev == 2 ? jal yield ; -> +0xae
```

Two things worth having in mind before writing any of it:

- **the panic arm is refuted from the contract's premises**, exactly as
  kerneltrap's three are: the trap came from user mode, so
  `trap_mstatus_ok`'s `SPP = User` makes the `andi/bnez` fall through. That is
  what keeps `panic` (and with it printk-on-the-panic-path) out of the cone.
  **DONE** — `ProofUsertrapParts.ut_spp_bit` / `ut_spp_clear_eq`, the
  opposite-polarity mirror of `ProofKerneltrapParts`' `kt_spp_bit` /
  `kt_spp_set_neq` (kerneltrap's `== 0` test needs the mask NONZERO from
  SPP = 1; usertrap's `!= 0` needs it ZERO from SPP = 0). All four belong
  beside `sstatus_read` in `WpGprCsrwC.v` and are split only because neither
  parts file may import the other's — hoist them together.
- **the function changes SIE index twice**: it is entered at `false` (the trap
  cleared SIE), the `csrsi sstatus,2` at +0xa2 flips it to `true` for the
  syscall arm only, and prepare_return is reached at `true` from that arm and
  at `false` from every other. Both prepare_return and kexit are already
  index-generic, which is why this costs nothing.

## THE BOUNDARY IS STATED IN THE WRONG WORLD — the finding of this project

`SpecUsertrap.v` was written ahead of the proof (`10892e92`) as
"uservec's postcondition in, userret's precondition out", with the
kernel-internal resources abstracted as `usertrap_res pt ksp`. That framing is
right; the vocabulary was not. Three separate collisions, all the same shape:
**the trampoline halves and the kernel interior describe the same objects in
two incompatible tiers, and a contract that takes BOTH is not merely awkward,
it is UNSATISFIABLE — so proving it would be vacuous.**

### A. The kernel page table: exclusive `tlb_inv_pt` vs shared `kpt_inv`

The old boundary takes `tlb_inv_pt kroot`, which owns `ptree_own 2 (DfracOwn 1)`
of the KERNEL tree (`PtTree.pt_frame`). Every kernel callee, meanwhile, works
over `IntrDefs.sie_cap`, which contains `strans_inv`, whose KPT arm is
`KptShare.tlb_res_pt root_ppn` — and `tlb_res_pt` carries `kpt_inv root`, the
Iris invariant that holds the tree. Hold both and one `iInv kptN` yields two
exclusive `ptree_own`s of the same tree, i.e. `False`; every leaf's
`sr_absorb` opens `kptN`, so the interior would go through **by absurdity**.

This is not a gap in the sweep — it is the follow-up
`completed/kpt-share.md` §3 already names: *"reworking the [satp-switch]
window to open `kpt_inv` per step is a FOLLOW-UP project, prerequisite only
for user-mode-under-shared-table."* Only four spec files mention
`tlb_inv_pt` (`SpecUservec`, `SpecUserret`, `SpecUsertrap`,
`SpecProcPagetable`); the whole rest of the tree is on the shared tier.

**Resolution: usertrap lives in the SHARED world, and it does not mention the
kernel table at all.** It never writes satp — the only two functions that do
are the trampoline halves — so it has no business owning a tree. The kernel
table reaches it the way it reaches every other kernel function: inside
`sie_cap`'s `strans_inv`, i.e. inside `usertrap_res`. The exclusive/shared
seam then sits entirely in uservec/userret, which is the only place that
needs exclusivity, and it becomes the trampoline rework's problem rather than
a contradiction inside usertrap's premises.

### B. The trapframe page: physical at the trampoline, VA inside `proc_priv`

The old boundary hands over the 36 trapframe words as
`tf_pa tfp off ↦ₚ₈ w` — the PHYSICAL tier, which is what uservec/userret
genuinely see (they reach the page through the user table's TRAMPOLINE
mapping). But `ProcInv.proc_priv` — which every kernel callee below usertrap
takes, and which usertrap needs for `p->trapframe->epc` — owns the same page
as `tf_page (ud_tfp (pv_upt V)) (pv_tf V)` at the **VA tier** (`a_tf_word …
↦₈`, through the kernel's identity map). Taking both is double ownership.

**Resolution: the words are NOT in usertrap's contract.** `proc_priv`, inside
`usertrap_res`, is the only owner, and `p->trapframe->epc = r_sepc()` is an
ordinary VA-tier store through it. The physical↔VA crossing
(`RiscvPtsto.phys_to_mem_claim` / `mem_to_phys_claim`, which need
`kmap_at (svpn_of pa) ppn KP_rw`) belongs on the trampoline side, where the
mapping is in scope — which is what `ProcInv.v`'s own note about the page's
tier already says ("the trampoline side converts back with
`mem_to_phys_claim`"). Same story, one tier up, for `user_cfg C`: its
mie/mideleg/menvcfg cells are `sconf`'s cells, so they ride inside
`usertrap_res` and the boundary keeps only the one cell usertrap WRITES
(`stvec`).

### C. The post is missing the crossing

`usertrap_post` was a plain `∀` at the ambient hart. usertrap PARKS — yield on
the timer arm, and every sleeping syscall through `SpecSyscall`'s own
`wp_next true pj` — so it can return on a different hart, and its post has to
be a `wp_next true pj (fun CID => …)` or it is unprovable (the continuation's
`pc_is` / `gpr_file` / `cpu_own` are hart-indexed). Cost: the trampoline
dovetail must be written hart-generically. Nothing else changes — the guard of
a `true` crossing is vacuous for the callee.

## The restated boundary: the entry payload IS prepare_return's exit payload

This is the pleasing part, and it is what makes the restatement obviously
right rather than merely different. Line up what prepare_return leaves
(`SpecPrepareReturn.v`'s post) against what usertrap is entered with:

| prepare_return leaves | the trap does | usertrap is entered with |
|---|---|---|
| `stvec ↦ᵣ TRAMPOLINE`, NO `intr_res` | — | `stvec ↦ᵣ TRAMPOLINE`, no handler installed |
| the `sie_gname` **1/4 dangling** | — | the same quarter, still dangling |
| `strans_bit strans_bit_kpt` loose | — | the same receipt |
| `sret_bits 'b"0" 'b"1"` (SPP=U, SPIE=1) | `sret` sets SIE:=SPIE=1, then the trap sets SPP:=U, SPIE:=SIE=1 | SPP=U, SPIE=1 — the SAME pair |
| `sepc ↦ᵣ mepc_val epc`, scause/stval ∃ | trap overwrites all three | `sepc/scause/stval` at the trap's values |
| mstatus SIE=0 (its own `intr_off`) | `sret` sets SIE=1 in user mode; the trap clears it | mstatus SIE=0 again |

Every ghost fraction is where prepare_return left it, and the two mstatus bits
the ghost mirror tracks come back to the same values — **so the whole
excursion through userret / user mode / uservec moves no ghost at all**, and
`usertrap_res` can simply carry the mirror halves across it. That is why the
boundary needs no ghost var of its own.

And usertrap's own first act closes the loop: `csrw stvec, kernelvec` at +0x1e
folds the dangling quarter + the `stvec` cell + `intr_handler_spec kernelvec`
into a real `IntrDefs.intr_res`, hence `trap_csrs` — which is precisely the
`intr_res` that prepare_return's `csrci` will unfold again on the way out.
The C comment ("send interrupts and exceptions to kerneltrap(), since we're
now in the kernel") is that fold, and the ORDER is forced: at +0x0c the hart
has no kernel handler, so nothing before +0x1e may enable interrupts.

So the restated contract is:

- **premises**: `usertrap_entry_ms ms_v` (= `trap_mstatus_ok` + `sconf_ms_facts`
  + `SPIE = 1`), `j < NPROC`, `m !!! sp = ksp`, `m !!! tp = cid_word`;
- **in**: `kernel_text`, `pc_is usertrap`, `hart_state`, `cur_privilege`,
  the four CSR cells, `stvec ↦ᵣ TRAMPOLINE`, `gpr_file m`, `R pt ksp`;
- **out**, under `wp_next true (proc_addr j)`: the same shape with `ms'`
  satisfying `usertrap_ret_ms`, a0 = a `satp_rooted` user satp of a possibly
  grown `pt'` (root and tfp stable), `callee_saved m mf`, and `R pt' ksp`.

`usertrap_res` stays the abstract module parameter, keyed on `(pt, ksp)`, and
the proof will define it as

```
  R pt ksp ≜ ∃ γf γs j γl pid V av C <the FS/disk/icache ghost names>,
      ⌜pv_upt V = pt⌝ ∗ ⌜K_usertrap ≤ av⌝ ∗ ⌜γs !! j = Some γl⌝ ∗
      (* sie_cap's three, keyed on sp = ksp — which is what the
         [m !!! sp = ksp] premise licenses *)
      stack_own ksp av ∗ strans_inv ∗ sie_arm false (proc_addr j) ∗
      (* sconf minus the mstatus cell, plus the two ghost mirrors WHOLE *)
      hw_config ∗ minstret_inv ∗ <mie/mideleg/menvcfg cells> ∗
      ghost_var sie_gname (1/2) 'b"0" ∗ ghost_var sie_gname (1/4) _ ∗
      sret_bits _ _ ∗ strans_bit strans_bit_kpt ∗
      cpu_own 0 false (proc_addr j) C false ∗ cpu_claim (proc_addr j) ∗
      □ intr_handler_spec (mword_of_int KernelSyms.kernelvec) ∗
      procs_inv γs ∗ panic_wp_any ∗ kernel_data ∗ is_kstack (proc_addr j) _ ∗
      proc_priv γf (proc_addr j) pid V ∗ syscall_env γf (proc_addr j) ∗
      <kexit's list> ∗ <devintr's> ∗ <vmfault's> ∗ <printk_gen's> ∗
      fd_slots FDSPARE ∗ iref_slots IREFSPARE
```

i.e. the union of the five cones' environments, exactly as `syscall_env` is
the union of the twenty-two table entries'. Most of it is `syscall_env`'s
union already — kexit's list IS `sys_exit`'s — so the real content is the
handful of things syscall does not need: devintr's device bundle, vmfault's,
printk-general's `pr` lock, and the trap-side pieces above.

**LANDED as `UsertrapRes.v`**, split three ways (`ut_trap` / `ut_env` /
`ut_res`) so the phases can open them separately, with `K_usertrap =
4 + K_syscall`. Two things worth knowing about it:

- **The instance list is kexit's, not the boundary's**, because a module
  PARAMETER's type has to be its instantiation's. Nothing would have caught a
  mismatch until `ProofUsertrap` seals `USERTRAP` — the whole proof away — so
  `USERTRAP` now `Include`s a split-out `USERTRAP_RES` and the file ends with
  `Module UtResFits (SY : SYSCALL) <: USERTRAP_RES`, checked against the
  declaration rather than a hand-copied mirror of it (verified to bite:
  dropping one class gives *"Signature components for field usertrap_res do
  not match"*). It has to be a functor because `syscall_env` is the one member
  of the union that is itself still an assumed contract.
- **`ut_sconf_closer` is `IntrDefs.sconf_at`'s idiom with one more cell.**
  `sconf_at` exposes only the mstatus cell; the trampoline needs
  `cur_privilege` too (userret's `sret` writes it). Keeping it as a CLOSER
  rather than re-spelling `sconf`'s internals avoids a second copy of five
  pure side conditions, and `ut_sconf_open` is the proof that the closer
  really is "the rest of `sconf`". It BELONGS beside `sconf_at` in
  `IntrDefs.v` and is in `UsertrapRes.v` only because editing the bottom of
  the tree costs a near-total rebuild — hoist it whenever something else has
  to touch that file.

## What is OWED to the trampoline halves (the dovetail, now explicit)

The restatement moves the seam rather than closing it. `SpecUservec`'s post
and `SpecUserret`'s pre are stated in the trampoline tier; usertrap's contract
is in the kernel tier. Composing them (the whole-trap-loop Löb theorem that
discharges `UserExec.stvec_handler_wp`) now owes exactly three conversions,
and each is a real piece of work with a known shape:

1. **The kernel table, exclusive → shared and back.** Rework the pt2
   satp-switch window (`TransPt.v` / `UserretEntryPt.v` / `UservecExitPt.v` /
   `TrampStepPt.v`) so the KERNEL side is `kpt_inv` + a `kpt_lb` snapshot
   opened per step, the way `KptShare.tlb_res_pt_translateAddr_at` already
   does it, instead of `kpt_frame`'s exclusive `pt_frame`. The user side stays
   exclusive (a per-process table genuinely is). This is
   `completed/kpt-share.md` §3's named follow-up; it is the LARGEST of the
   three and it gates the composition, not usertrap's own proof.
2. **The trapframe page, physical → VA.** 36 words, one
   `phys_to_mem_claim` each, needing `kmap_at (svpn_of pa) ppn KP_rw` for the
   RAM gigapage. Under the shared regime that claim is available by opening
   `kpt_inv` (mask-carrying), which is why doing this conversion in the
   trampoline halves is now cheaper than it was when `ProcInv.v`'s note was
   written.
3. **`user_cfg C` ⟷ `sconf`'s config cells.** Plain cells on both sides;
   needs `uc_mie C = MIE_S`, since `sconf` PINS mie while `ucfg` only
   constrains `mie & ~mideleg = 0`. **Checked, and it is free**: the record
   constructor `UCfg` appears NOWHERE in the tree — no concrete `ucfg` is
   ever built (every user-tier statement carries `C` as a parameter), so the
   composition that eventually builds one just sets `uc_mie := MIE_S`
   (`0x220`), for which `uc_mm` holds at `mideleg = 0xffff`. No field change,
   no ripple; the seam needs only the premise. This was the one item that
   could have forced a `ucfg` change, so it was worth checking first.

## Phase plan for the proof itself

Sized against ProofPrepareReturn (42 instructions, one file) and ProofUservec
(44, four files). usertrap is 90 instructions but eight of the arms are calls,
so the instruction count is not the driver — the resource assembly is.

- **Phase A — the entry assembly and the two straight-line prologues.**
  +0x00..+0x28: the frame, the SPP test (refute the panic arm), the
  `csrw stvec` fold into `trap_csrs`, `jal myproc`, and the
  `p->trapframe->epc = r_sepc()` store. Ends holding `sie_cap_gpr` +
  `cpu_own` + `trap_csrs` + `proc_priv` at index `false` — after which every
  later phase is ordinary kernel-cone work. **This is the phase that proves
  the design; do it before anything else.**
  **The resource half of it is DONE** — `UsertrapRes.ut_trap_open`, and it
  went through on the first attempt: the boundary's raw machine state plus
  `ut_trap` *is* `sie_cap_gpr m av false pj ∗ cpu_own 0 false pj C false`,
  with the dangling SIE quarter, the KPT receipt and the sret mirror falling
  out loose (three of `trap_csrs`' six members). No instruction is involved,
  which is exactly why it is the design check. `ut_trap_csrs_fold` is the
  other half: those three plus the WRITTEN stvec cell and the handler
  contract *are* `trap_csrs`, via `intr_res_intro` at
  `SpecKernelvec.kernelvec_tv_direct` / `_stvec_base`. So the C comment
  ("send interrupts and exceptions to kerneltrap(), since we're now in the
  kernel") is a fold, and its ORDER is a theorem: nothing before +0x1e can
  set SIE = 1, because `sie_ghost_flip` needs all three fractions and the
  quarter is not inside an `intr_res` to be found in.
  The remaining Phase A work is the walk itself, and **every ingredient it
  needs already exists** — checked one by one, so it is a mechanical chain
  rather than an exploration. Per instruction:

  | off | insn | leaf | pure fact |
  |---|---|---|---|
  | +0x00 | `c.addi sp,sp,-32` | `wp_caddi_sp_push_s_sconf` | `KernelRvcDecode.stk_push_32` |
  | +0x02 | `c.sdsp ra,24(sp)` | `wp_csdsp_s_sconf` | `stk_frm` at `d=4,u=3,k=1` |
  | +0x04 | `c.sdsp s0,16(sp)` | `wp_csdsp_s_sconf` | `stk_frm` at `4,2,2` |
  | +0x06 | `c.sdsp s1,8(sp)` | `wp_csdsp_s_sconf` | `stk_frm` at `4,1,3` |
  | +0x08 | `c.sdsp s2,0(sp)` | `wp_csdsp_s_sconf` | `stk_frm` at `4,0,4` |
  | +0x0a | `c.addi4spn s0,sp,32` | `wp_caddi4spn_s_sconf` | `stk_fp_32` |
  | +0x0c | `csrr a5,sstatus` | `WpSconfCsr.wp_csrr_sstatus_s_sconf` | — |
  | +0x10 | `andi a5,a5,256` | `WpSconfAlu.wp_andi_s_sconf` | — |
  | +0x14 | `c.bnez a5` (NOT taken) | `WpSconfBtype.wp_cbnez_fall_s_sconf` | `ut_spp_clear_neq` |
  | +0x16 | `auipc a5,0x3` | `wp_auipc_s_sconf` | — |
  | +0x1a | `addi a5,a5,-374` | `wp_addi4_s_sconf` | — |
  | +0x1e | `csrw stvec,a5` | `wp_csrw_stvec_s_sconf` (takes the **RAW** cell) | then `ut_trap_csrs_fold` |
  | +0x22 | `jal myproc` | `wp_jal_s_sconf` + `MYPROC.wp_myproc_sconf` | — |
  | +0x26 | `c.mv s1,a0` | `WpSconfAlu.wp_cmv_s_sconf` | — |
  | +0x28 | `c.ld a5,88(a0)` | `wp_cld_s_sconf` | — (opens `proc_priv`) |

  The frame words come out of `StackOwn.stack_own_4_elim`, and the epilogue's
  `c.addi16sp sp,32` at +0xfc is `stk_pop_32`. **The prologue needs no new
  pure lemma at all** — `stk_push_32` / `stk_fp_32` / `stk_pop_32` are already
  in `KernelRvcDecode.v` for exactly a 32-byte frame, and `stk_frm` is the
  generic slot-address lemma (its own header gives the call form:
  `apply stk_frm; apply bv_eq; vm_compute; reflexivity`, both indices closed,
  `X` symbolic). `ProofPrepareReturn` is the walk template for all of it —
  its first four steps are +0x00..+0x06 with the frame two slots smaller.

  The one step that is not prologue bookkeeping is **+0x28**, the first read
  of `p->trapframe`: it needs `proc_priv` opened for the `p_trapframe` cell,
  which is where Phase A stops being mechanical and Phase B's resource work
  begins.

  One thing the bundle deliberately does NOT carry:
  `intr_handler_spec kernelvec`. `SpecKernelvec.kernelvec_handler_spec` builds
  it from hw_config + minstret_inv + kernel_text + `devintr_caps`, and
  `ut_env` holds the last while the first two are persistent conjuncts of the
  `sconf` `ut_trap_open` assembles — so asking R's builder for it would be
  asking for something it can compute. The cost is one more functor argument
  on ProofUsertrap (KERNELVEC, a proven module), and the reason the derivation
  is not in `UsertrapRes.v` is that a definitional file may not name a module
  parameter.
- **Phase B — the scause dispatch and the three cheap arms.** devintr,
  vmfault, and the unexpected-scause arm (printk-general ×2 + setkilled).
  Each is a call and a branch; the interesting part is that the arms rejoin at
  +0xa6 carrying different `which_dev`.
- **Phase C — the syscall arm.** The `killed`/`kexit(-1)` pre-check, the
  `epc += 4`, the `csrsi` index flip to `true`, `jal syscall`, and the rejoin.
  The flip is prepare_return's lesson in reverse: the binder AT the flip is
  still at the old index.
- **Phase D — the tail.** The second `killed`/`kexit`, the `which_dev == 2`
  yield, `jal prepare_return`, `MAKE_SATP`, the epilogue, and the exit
  DISASSEMBLY (prepare_return's post back into the boundary's raw pieces plus
  `R pt' ksp`). **Its load-bearing fact is already proven**:
  `UsertrapRes.ut_exit_ms_ok` shows `usertrap_ret_ms` is DERIVABLE from the
  bundle prepare_return hands back, not something usertrap has to arrange —
  SIE = 0 off the dangling quarter's agreement with `sconf`'s half, SPP/SPIE
  off the travelling mirror's agreement with `sconf`'s tie (then
  `sret_ms2_SPP` for `sret_newpriv ms = User`), and the rest verbatim from
  `sconf_ms_facts`. So the two ghost fractions the user-mode excursion parks
  are not bookkeeping: they are what makes the return legal.
- **Phase E — `usertrap_res` defined concretely, `ProofUsertrap` sealed as
  `Module UsertrapProof : USERTRAP`, `LinkUsertrap.v`.**

Two process notes carried over from the neighbours: put
`Set Printing Depth 40.` at the top of every file (usertrap proves over
`proc_priv`, so a failing tactic prints `tf_page`'s 4096 conjuncts —
durable-notes' 40-minute non-answer), and close block seams by naming every
conjunct rather than with `iFrame` (the >19 GB non-termination).
