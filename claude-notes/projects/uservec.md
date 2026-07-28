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
- **SpecUsertrap.v** — usertrap()'s boundary contract, stated but NOT
  proven (per plan).  Entry = SpecUservec's continuation; return = exactly
  userret's precondition (`usertrap_ret_ms`, `satp_rooted`, the re-armed
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

## What remains after this project

- Prove usertrap() (huge: syscall/devintr/vmfault/kexit/prepare_return
  cones) and define `usertrap_res` concretely.
- The whole-trap-loop theorem: Löb over trap rounds discharging
  `stvec_handler_wp` from USERVEC + USERTRAP + USERRET + USER — the
  resource cycle is already closed by construction (uservec's leftovers =
  usertrap's entry bundle; usertrap's post = userret's pre; userret's
  leftovers = uservec's bundle for the next round).
