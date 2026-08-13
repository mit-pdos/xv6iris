# Project: uservec — the user-mode trap handler (E-uservec)

Prove uservec (trampoline.S, offsets 0x00..0x9b of the trampoline page) and
close the last assumed piece of the user-mode story: `stvec_handler_wp`
(UserExec.v), the hypothesis of `wp_user_exec_closed` (SpecUser.v).

## The boundary specs (all landed, all compile)

- **SpecUserret.v / ProofUserret.v / LinkUserret.v** — userret in the
  spec-module shape.  The statement is verbatim the old
  `UserretAllPt.wp_userret_pt` (that file BECAME ProofUserret.v; the proof
  body is unchanged, entered via `cbv beta delta [wp_userret_pt_body];
  unfold tf_pa, userret_gpr`).  New spec vocabulary: `tf_pa tfp off` (the
  trapframe word's physical address) and `userret_gpr m vra … va0f` (the
  restored file), both plain Definitions so the old proof script unifies
  through them.
- **UserretUser.v / LinkUserretUser.v** — THE DOVETAIL, machine-checked: a
  functor over USERRET + USER whose `wp_userret_user` runs userret, feeds
  its postcondition through `userret_to_user_inv` (UserKernelBridge.v) into
  `user_inv`, and concludes with `U.wp_user_exec_closed`.  Type-checking
  this file is the proof that userret's post matches SpecUser's pre.  The
  leftovers in userret's continuation (31 trapframe words + `kpt_frame`)
  are exactly SpecUservec's kernel-side bundle for the NEXT trap.
- **SpecUservec.v** — uservec's interface.  Consumes exactly
  `user_trap_frame C pt` (what `stvec_handler_wp` receives) + the
  kernel-side bundle (`sscratch`, `kpt_frame kroot`, the 31 save slots at
  FULL ownership, the 4 kernel trapframe words at generic dfrac, with
  `satp_rooted`-style premises pinning word 0 to a kroot-rooted satp
  value).  Continuation: ∀ over the frame's existentials (g, ms_v, trap
  CSRs), at `pc_is (ret_pc vktr)` with `gpr_file (uservec_gpr g …)`,
  `tlb_inv_pt kroot` live, the user table parked, the save slots holding
  g's registers.
- **SpecUsertrap.v** — usertrap()'s boundary contract as first stated,
  which is NOT the one that was proven: read `completed/usertrap.md`
  §"THE BOUNDARY IS STATED IN THE WRONG WORLD" before using anything below
  this bullet.  As sketched here, entry = SpecUservec's continuation and
  return = exactly userret's precondition (`usertrap_ret_ms`, `satp_rooted`, the re-armed
  kernel trapframe words with word 16 = KernelSyms.usertrap, callee_saved,
  a0 = user satp of a possibly-grown `pt'` with root/tfp stable).  The
  kernel-internal resources are the ABSTRACT module-type parameter
  `usertrap_res : uptd -> mword 64 -> iProp Σ` (process bundle keyed by
  user table + kernel stack top), so the eventual proof refines the
  definition without churning the boundary; consumers thread it opaquely.
  `satp_rooted` and `usertrap_ret_ms` live here — shared vocabulary for
  the loop composition.

## The mstatus-pin extension (landed)

`user_mstatus_ok` and `trap_mstatus_ok` (UserExec.v) now ALSO pin
`TVM = 0` and `TSR = 0`.  Without them uservec's `sfence.vma`/`csrw satp`
(TVM gates) and userret's `sret` (TSR gate) would be unprovable from the
trap frame — the bits were existentially lost inside `user_inv`.  They are
M-mode bits xv6 never writes and sstatus writes cannot touch.  Ripple was
mechanical: `utrap_ms_TVM/TSR` (UserTrap.v), `user_mstatus_ok_sret_ms5`
gains two premises (UserKernelBridge.v; `userret_to_user_inv` likewise),
destructuring sites got `& _ & _` (UserMemClassify.v, UserTotalU.v).

## The uservec proof (LANDED — trampoline.S 100% proven)

All four files below are built, linked, in `_CoqProject`, and axiom-clean
(the 5 platform stubs + funext only).  `tools/proof_coverage.py` counts
uservec via `MANIFEST_PROVEN` (virtual entry pc, like userret): trampoline.S
is 2/2 functions, 288/288 bytes proven.  What was learned, per file, is
inlined below.

Cleanup candidates left behind (none blocking, all small):
- `exec_execute_C_JALR` now exists in BOTH UservecDefs.v and
  UserExecFacts.v (the latter off this import chain); hoist one copy into
  WpMmodeLeafBase next to `exec_execute_C_SD`/`C_JR` and drop the other.
- `exec_cE_zicfilp_false_S` now has a THIRD `Local` copy
  (UservecExitPt.v, after WpSconfCtl.v:118 and WpSmodePtCtl.v:52) — hoist
  into ExecCommon.v/WpDecode.v.
- `exec_execute_JALR_link_zca` (the rd≠0 linking JALR reduction,
  UservecExitPt.v) is worth promoting next to the rd=0
  `exec_execute_JALR_ret_zca` in WpSmodePtCtl.v (currently `Local`).
- `csr_sscratch := mword_of_int 0x140` is defined in BOTH UservecDefs.v
  and UservecPt.v (identical; import shadowing is benign) — keep one,
  ideally beside `csr_satp` in WpGprCsrwB.v.
- `UptTree.v` lacks `utlb_inv_pt_open` (UservecExitPt destructures the
  definition raw) and `TransPt.v` lacks `kpt_pt2_base` (the `proj1` of
  `kpt_tree_spec_gen`, supplied inline) — add both for symmetry.
- `wp_usd_pt`'s `Hmod8` premise is kept only for signature symmetry with
  `wp_uld_pt` (the `↦ₚ₈` resource already carries 8-alignment).

## The uservec proof plan (as executed)

The 44-instruction catalog (words verified against KernelInstrs.v):
csrw sscratch,a0 @0x00; li a0,TRAPFRAME (lui/c.addiw/c.slli @0x04–0x0a,
same words as userret's); 30 sd's @0x0c–0x72 (7 compressed at 0x28–0x34);
csrr t0,sscratch @0x76; sd t0,112(a0) @0x7a; ld sp/tp/t0/t1 @0x7e–0x8a
(kernel words 8/32/16/0); sfence @0x8e; csrw satp,t1 @0x92; sfence @0x96;
c.jalr t0 @0x9a (ra := uva 0x9c — usertrap rets straight into userret).

Files (mirror the userret split):
1. **UservecDefs.v** — catalog: words/ASTs/decode facts/`instr` lemmas.
2. **UservecPt.v** — leaves: the pa-form width-8 STORE tower +
   `wp_usd_pt` (the store mirror of `wp_uld_pt`; rs2 read at the
   translate-output state), `wp_ucsrw_sscratch_pt`, `wp_ucsrr_sscratch_pt`
   (over `wp_instr_u_pt`).  `wp_ualu_pt`/`wp_uld_pt` are reused as-is
   (offset-generic).
3. **UservecExitPt.v** — `wp_uservec_exit_pt`: sfence under the user
   invariant; csrw satp,t1 ENTERS the pt2 window with roles swapped
   (Sp := upt spec, Sc := kpt spec from `kpt_frame`'s ∃M); sfence EXITS
   into `tlb_inv_pt kroot` re-sealed with kpt_frame's M + kmap_auth, the
   user table parking as `pt_frame`; then c.jalr t0 under the kernel
   invariant (`wp_instr_ktramp_pt`).
4. **ProofUservec.v / LinkUservec.v** — the chain concluding
   `wp_uservec_pt_body`, `Module UservecProof : USERVEC` (1379 lines,
   85 s): opens `user_trap_frame_open` (UserKernelBridge.v),
   stvec_base(TRAMPOLINE) = uva 0 by vm_compute, then csrw sscratch → li
   (3 same-key inserts collapsed to `<[a0 := TRAPFRAME]> g` exactly as
   ProofUserret's li) → 30 stores (`gpr_file` UNCHANGED by `wp_usd_pt`,
   so ONE `Ha0` fact serves all 30 — no map tower; each saved word is
   rewritten `M2!!!rs2 → g!!!rs2` by `upd_ne` as it lands) → csrr →
   store 112 → 4 loads → exit lemma → continuation.

Worth keeping (proof-technique notes from the build):
- The store leaf needed NO new tower: `WpSmodePtLeaves.v`'s
  `exec_execute_STORE_8_gpr_S_walk_pt` is already state- AND pa-generic
  (it takes the effective-address transform as hypothesis `Htea`); only
  `exec_transform_effective_address_store_S` (the `_load_S` twin) was
  missing.  `execute_STORE` reads rs2 BEFORE the translate, so rs2 = x0
  needs no special-casing (unlike the AMO tower).
- The pt2 window is fully direction-symmetric: `tlb_inv_pt2_enter/_exit`
  / `wp_instr_pt2_tramp` / `pmp_config_reindex` all take
  `Sp := upt_tree_spec`, `Sc := kpt_tree_spec_gen kroot M`, `rc := kroot`
  with zero changes — UservecExitPt.v mirrors UserretEntryPt.v line for
  line, plus the c.jalr step (`exec_execute_C_JALR` emits
  `JALR (zeros' 12, rs1, ra)` verbatim; the link value is
  `regval_into_reg (uva 0x9c)`; `regval_into_reg` is rv64d's identity on
  mword 64, so such gaps close by `reflexivity`).
- uservec's offsets 0x36..0x9a are 2-mod-4 aligned: every 32-bit fetch
  there goes through the split 2+2 chunk geometry, and the engine's
  `is_aligned 4 → is_aligned 4` premise is discharged by REFUTING its
  hypothesis (`intro Hf; vm_compute in Hf; discriminate`).
- `trap_mstatus_ok`'s TVM pin + `menvcfg0 = MENVCFG_S` were enough for
  every gate (satp csrw, sfence, Zicfilp LPE) — no extra premises.
- `utlb_inv_pt` internally carries `⌜upt_map_wf um⌝`, so the exit lemma's
  wf premise is extracted (`iDestruct … as %`, keeping the spatial input)
  rather than spec-threaded.

## prepare_return: the resource shape, after `intr_inv` was deleted

`prepare_return`'s 42 instructions (`CodePrepareReturn.v`, `prr_*`) all
have leaves. Two of them were gaps until 2026-08-11:

- `csrr a4,satp` (`prr_32`, `CSRReg (0x180, zreg, a4, CSRRS)`) — satp is
  the one CSR whose accessibility is not a constant (`satp_accessible
  Supervisor` READS mstatus for TVM=0), so it could not use the shared
  `exec_check_CSR_result_read_extS` route. Now
  `WpSconfCsr.wp_csrr_satp_kpt_s_sconf`; the TVM premise costs callers
  nothing because `sconf` already carries `sconf_ms_facts`. **It takes the
  KPT receipt, not a satp points-to** — see design/smode-and-vcgen.md: a
  leaf that asks for the cell *beside* `sie_cap_gpr` is vacuous, because
  `strans_inv` owns satp in both arms and is inside the bundle.
- `csrw stvec,a5` (`prr_2c`) — the trap-destination switch from kerneltrap
  to usertrap. This was **structurally unprovable** while the trap vector
  lived in `intr_inv`: a persistent `inv` whose handler was fixed in its
  type, so the cell could be borrowed but only ever returned at the SAME
  value. `30041d61` deleted it.

**The post-`intr_res` shape, which is what a proof should be written
against.** The vector is now OWNED:

```coq
Definition intr_res : iProp Σ :=
  (∃ h b, ⌜TV_Direct h⌝ ∗ ⌜stvec_base h = h⌝ ∗
          ghost_var sie_gname (1/4) b ∗ stvec ↦ᵣ h ∗ ▷ intr_handler_spec h)%I.
```

and rides as the fifth member of `trap_csrs`, with `trap_csrs_to_raw :
trap_csrs -∗ trap_csrs_raw ∗ intr_res`. So prepare_return gets the cell
from **its own `intr_off()`**: `wp_csrci_sstatus_x0_s_sconf` at `b = true`
hands back `trap_csrs` (plus `intr_count 0 false`, `cpu_cells_pay`, and
the bundle at the disabled index), and `rewrite /intr_res` opens it —
`Typeclasses Opaque` means `iDestruct` cannot, by design.

**The postcondition hands back `trap_csrs_raw`, NOT `trap_csrs`.** After
prepare_return this hart has no *kernel* trap handler installed: traps go
to uservec, whose contract is not `intr_handler_spec` (it never returns to
the interrupted pc — it runs usertrap and sret's to user), so claiming
`intr_res` at TRAMPOLINE would be false. What comes out is
`trap_csrs_raw` + `stvec ↦ᵣ TRAMPOLINE` + the dangling SIE quarter.

**That dangling quarter is the safety argument, and it makes the C comment
a theorem.** `sie_ghost_flip` needs all three fractions; the 1/4 that
lived in `intr_res` is now loose in prepare_return's post, so nothing can
set SIE=1 until it is folded back into a real `intr_res`. That is exactly
"a trap from kernel code to usertrap would be a disaster, turn off
interrupts" — and it is why the write is legal only after `intr_off()`,
which is the order the C code uses.

## prepare_return: PROVEN, 42/42 instructions

`ProofPrepareReturn.v` closes with `Qed` (2026-08-11), sealed as
`PREPARE_RETURN` and linked by `LinkPrepareReturn.v` against
`LinkMyproc`. Pure obligations live in `ProofPrepareReturnParts.v`.

**The one structural idea: the function changes index at +0x0c, and
everything it needs comes out of that flip.** The prologue and the `jal
myproc` run at `b = true`, so each step rebinds the hart; from the `csrci`
onward the index is `false` and every step is `wp_next_off_intro`. Three
consequences that cost real time to find:

- **The binder at the flip itself is still `true`.** The flip leaf's
  continuation is `wp_next b p` at the leaf's *entry* index, and an
  interrupt can be taken on that very instruction — so that one step
  rebinds (`iIntros (CID7 Hk7 ms0)`) and only the ones after it introduce
  at the ambient hart. Writing `wp_next_off_intro` there fails with an
  unhelpful unification error.
- **`c.mv a4,tp` at +0x50 is legal only because the flip already
  happened.** `src_ok b rs` forbids a tp read at `b = true`, so this
  instruction could not be proved anywhere before +0x0c. gcc's ordering is
  the only one that works.
- **A resource minted before the flip carries the *old* hart in its
  `rget`s.** "Hbra" (the ra slot, stored at +0x02) holds `rget (CID :=
  <that step's hart>) M1 ra_idx`, while every fact stated after +0x0c is
  at the rebound hart; the two do not match syntactically. The fix is to
  state the restatement ∀-quantified over `CpuId` and let `rget_ne` —
  which is hart-generic away from tp — rewrite at whichever instance the
  resource carries. This is the only place in the walk where the hart
  annotation matters.

**The sstatus RMW was never the hard part it looked like.** The whole-word
identity `sstatus_read ms0 = (sstatus_read ms &~0x100) | 0x20` is not
needed and cannot be proved cheaply (it would need `lower_mstatus`'s nest
of slice updates reasoned about as a word). `flip_core` already takes the
written word abstractly with five field premises, so generalizing
`wp_csrw_sstatus_val_s_sconf` to an abstract `wval` reduced the obligation
to seven three-line field lemmas: slicing distributes over the bitwise ops
(`bv_extract_and` / `bv_extract_or`, added to `WpGprCsrwC.v`) and each
mask's own slice is a closed `vm_compute`. `prr_sst_spp` lands at `'b"0"`
and `prr_sst_spie` at `'b"1"` — exactly the `sret_bits 'b"0" 'b"1"` the
contract promises.

**Two bugs found by attempting the proof, not by inspection.** The spec's
post promised the per-cpu bundle twice (`cpu_cells` and `intr_count`
standalone *and* inside `cpu_own`); and `wp_csrr_satp_s_sconf` as first
written had a premise set no caller could hold. Both were unprovable-as-
written rather than hard, and both are fixed.

**`callee_saved m mF` over a 25-deep insert tower** is three lines, not
13×25 peels: every write above `A` is to a3/a4/a5/ra — all caller-saved —
so `repeat (apply callee_saved_insert_r; [vm_compute; reflexivity |])`
collapses the tower to `callee_saved A U17`, and only sp and s0 (saved by
the prologue, restored by the epilogue) need their own conjuncts.

## prepare_return: INDEX-GENERIC, at either entry SIE state

`wp_prepare_return_sconf_body` now takes a `b : bool` entry index and a
`trap_csrs_ext b` premise. Both values are reachable and pinning `true`
was what made usertrap unprovable against it:

- `b = true` — forkret, and usertrap's SYSCALL path (its own `csrsi
  sstatus,2` runs just before the `jal syscall`);
- `b = false` — usertrap's devintr / vmfault / unexpected-scause paths,
  which never re-enable interrupts after the trap cleared SIE.

**The missing leaf was an `intr_off()` that is a NO-OP.**
`WpSconfCsr.wp_csrci_sstatus_x0_s_sconf` REFUTES its `b = false` arm (its
`intr_count_pre b 0 true` premise is unsatisfiable there — the count
eighth at '1' contradicts the capability's '0' eighth), so a `csrci`
reached with interrupts already off had no leaf at all. Added:

- `WpSconfCsr.wp_csrci_sstatus_x0_idem_s_sconf` — the exact mirror of the
  existing `wp_csrsi_sstatus_x0_idem_s_sconf`: pre and post are the same
  `sie_cap_gpr m n false p` at an ARBITRARY index, nothing moves;
- `WpIntrOff.v` — `wp_intr_off_lvl0_s_sconf`, the index-generic composite,
  stated over `CpuOwn.cpu_own` and `IntrDefs.trap_csrs_ext` rather than
  over the leaf's raw pieces. **That is what makes its postcondition
  index-free** (`cpu_own 0 false p C false ∗ trap_csrs` on both arms), so
  everything after the `csrci` is proved once — which is why generalizing
  a 42-instruction proof cost three lines in its body rather than a
  second walk. Also `trap_csrs_ext_transport`, the `cpu_own_transport`
  twin: free on both arms (`emp` at `true`, no hart movement at `false`),
  and needed because the caller's own trap CSRs must reach the `csrci`
  across five hart-rebinding steps.

The rule this generalizes: **when a function's contract pins an index
because one leaf on its path only exists there, check whether the leaf's
other arm is a NO-OP before assuming the contract is right.** The
`_idem`/`_disable` pair is the shape; `trap_csrs_ext` is the accounting
(`SpecYield`/`SpecSched` use the same complement one tier up).

## What remains after this project

- **usertrap() is PROVEN and LINKED** — `completed/usertrap.md` is the
  record. Its boundary was RESTATED in the
  kernel tier along the way: the contract sketched below took the
  trampoline's `tlb_inv_pt` / physical trapframe / `user_cfg`, which together
  with the kernel cone's `sie_cap` are UNSATISFIABLE, so proving it would
  have been vacuous. What that moved rather than closed is the dovetail
  below.
- The whole-trap-loop theorem: Löb over trap rounds discharging
  `stvec_handler_wp` from USERVEC + USERTRAP + USERRET + USER. **This is the
  next piece of trampoline work, and it now owes three explicit conversions**
  (`completed/usertrap.md`, §"What is OWED to the trampoline halves"): the
  kernel page table exclusive → shared (`completed/kpt-share.md`'s named
  user-mode-under-shared-table follow-up, the largest of the three and the
  one that gates the composition), the trapframe page physical → VA (36
  words, one `phys_to_mem_claim` each, and it also owns `udata_cov`), and
  `user_cfg C` ⟷ `sconf`'s config cells (free: no concrete `ucfg` is ever
  built, so the composition just sets `uc_mie := MIE_S`). The resource cycle
  is otherwise closed by construction — uservec's leftovers = usertrap's
  entry bundle; usertrap's post = userret's pre; userret's leftovers =
  uservec's bundle for the next round.
