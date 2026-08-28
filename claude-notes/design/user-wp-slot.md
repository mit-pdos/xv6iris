# Design: the per-process user-execution WP slot

The WP that userret runs is a RESOURCE in the kernel-side residue, not a
hardwired theorem.  It rides beside `proc_priv`, through uservec/usertrap
and every park; userret extracts it and runs it; the user-space WP RETURNS
the next one at its trap and the trap-entry seam re-deposits that.  A WP is
MINTED at the two PARKS and nowhere else (userinit's, and sys_fork's kfork
call — a WP is a LINEAR resource the parker owes its child); the loop mints
nothing.  Today the minted one is the generic-safety WP; the machinery
exists so a VERIFIED process can carry its own WP instead.  The in-flight
work (real per-process linkage) is `projects/user-wp-slot.md`.

## The two WP forms

- **`UexecWp.uexec_wp`** — the ∀-STATE form, zero arguments, a GUARDED
  FIXPOINT (`fixpoint uexec_F`; `ParkCap.park_token` is the pattern —
  functional, `Local Instance … Contractive` by `solve_contractive`,
  `fixpoint`, `uexec_wp_unfold`).  `uexec_F X`: for every hart, config `C`
  (with `⌜loop_ok C pt⌝`, which lives here now; `SpecUserretClosed`
  re-exports it), table `pt`, abstract residue predicate `Rut`, image `M`,
  register file, mstatus (up to `user_mstatus_ok`), stale trap CSRs and pc
  — given `hw_config ∗ minstret_inv ∗ wire_inv`, the `u_regs` bundle,
  `user_pt_inv pt M`, `user_cfg C`, `Rut pt` and the PAIRED trap seam
  `▷ (user_trap_frame C pt Rut ∗ X -∗ WP Loop)`, conclude `WP Loop`.
  The pair is the RETURN CHANNEL: the frame goes to the kernel, the next
  round's WP comes back.  `X` occurs only under that `▷`, hence the guard.
  `UserExec.stvec_handler_wp` is the UNPAIRED form and stays what the
  safety tier consumes; the two are bridged inside the generic inhabitant.
  "Happy with any resume state": this is what the generic safety theorem
  proves (`ProofUexecWp.UexecGen (US : USER) : UEXEC_GEN`, providing
  `uexec_wp_gen : ⊢ □ uexec_wp` — no linear hypothesis, hence `□`, hence
  mintable wherever a `UEXEC_GEN` is in scope, which the tree keeps to the
  two mint sites below), and it is the residue's conjunct today.  Its proof
  is now a **Löb** that
  RETURNS ITSELF: `iLöb` gives `▷ □ uexec_wp`, the paired premise gives
  `▷ (frame ∗ uexec_wp -∗ WP Loop)`, and one `iNext` strips both so the
  old-shape `▷ stvec_handler_wp` the safety theorem wants can be built
  from the two.  Everything else in that proof is the unchanged `user_inv`
  repacking.
- **Seeing the body.** `uexec_wp` has no δ-unfolding — `rewrite /uexec_wp`
  is gone tree-wide, replaced by `uexec_wp_unfold`.  And the rewrite is
  always `iEval (rewrite uexec_wp_unfold /uexec_F) in "H"`, never a bare
  `rewrite`: a bare one rewrites the whole proofmode goal and would unfold
  the `uexec_wp` inside the handler premise / the Löb hypothesis, which is
  the type the RETURNED WP is stated at and must stay folded.
- **`UexecSlot.uexec_slot V M`** — the TRAPFRAME-KEYED form ("trapframe"
  always means trapframe + memory-view, the `(V, M)` pair): same shape,
  but the table is `pv_upt V`, the pc is
  `tf_resume_pc V = ret_pc (tf_w V tf_epc_idx)`, and the register file is
  `tf_resume_gpr b V = userret_gpr b ⟨the 31 words of pv_tf V⟩` at a
  ∀-BOUND dead base `b`.  The ∀ on `b` is load-bearing: `userret_gpr`
  overwrites x1..x31, so `b` survives only at the architecturally-zero
  x0, and the loop can only ever supply the base it happens to hold — ∀
  is the only form a discharge can meet.  The slot's precondition is thus
  the state its OWN trapframe and image record; nothing free-standing is
  ever discharged at resume.  `tf_w` is stdpp total lookup on `pv_tf`;
  the word-index map (epc = 3, ra..t6 = 5..35, a0 = `tf_arg_idx 0` = 14,
  sp = `tf_sp_idx` = 6) is `ProcGeom.v`'s, corroborated there.
- **`UexecSlot.uexec_wp_slot : uexec_wp -∗ uexec_slot V M`** — "plug in
  the generic WP", for processes with no exact U-mode WP.
  Its handler premise is PAIRED like `uexec_wp`'s, and the WP it returns is
  typed at the GENERAL `uexec_wp` — a verified process may hand back any
  successor.  So `uexec_slot` stays a plain definition, not a fixpoint of
  its own: its recursion routes through `uexec_wp`.
- `Rut` is ∀-bound in both forms; that is what keeps the RESIDUE out of the
  definitions even though the residue instantiating `Rut` itself contains a
  slot — the instantiation is an ordinary application.  (The guarded
  fixpoint above is about the RETURN CHANNEL, a different recursion.)

**Seal discipline.**  Both forms are `Typeclasses Opaque`, which blocks
`IntoForall`: `iEval (rewrite uexec_wp_unfold /uexec_F) in "H"` (resp.
`rewrite /uexec_slot`) by hand before
`iApply ("H" $! …)`.  The seal does not travel through re-exports — any
file manipulating a slot hypothesis must `Require Import UexecWp`
(resp. `UexecSlot`) DIRECTLY.  `uexec_wp`'s ∀-order is
`h C pt Rut M g ms_v sc_v stval_v sepc_v va` (regfile before the four
mwords).  `UexecWp.v` sits above `IntrDefs` — nothing lower may import it.

## Where the slot lives, and how it travels

- Conjunct of `UsertrapRes.ut_own` / `ut_own_nopt` (LAST), beside
  `proc_priv` — index-free, so the `∀ V'` closers thread it like
  `bslots 3` and the syscall walk carries it opaquely.
- Accessor `usertrap_res_uwp_acc pt ksp : usertrap_res_bare pt ksp -∗
  uexec_wp ∗ (uexec_wp -∗ usertrap_res_bare pt ksp)` — a `USERTRAP_RES`
  Parameter (SpecUsertrap.v), concrete in `UsertrapRes.ut_res_bare_uwp_acc`,
  re-exported through every seal.  The closer accepts a possibly
  different slot: it is the deposit channel.  The loop no longer feeds it
  at extraction time — the un-applied closer IS the parked `Rut` (below).
- Combined opener `usertrap_res_run_open pt ksp` — slot OUT and trapframe
  words BORROWED from ONE opener, the tf-closer landing in the HOLED form
  `… -∗ (uexec_wp -∗ usertrap_res_bare pt ksp)`.  The forkret entry needs
  both at once and each single accessor consumes the whole sealed bundle,
  so they do not compose in either order (same argument as
  `usertrap_res_tf_csrs_open`'s).  Concrete:
  `UsertrapRes.ut_res_bare_run_open`, a re-association of
  `ut_res_bare_tf_open`'s proof with the slot conjunct peeled out.
- **A WP IS A LINEAR RESOURCE, AND NOTHING PERSISTENT CARRIES ONE.**
  `SyscParkEnv.park_world` used to hold `□ uexec_wp` as its last conjunct
  — and `park_world` rides in `UsertrapRes.ut_park_caps`, i.e. inside the
  residue, so that copy made the WP ambiently DUPLICABLE from inside every
  trap round.  The conjunct is GONE (and with it
  `UsertrapRes.park_world_uwp`); `park_world` is back to its pre-slot
  shape.
- **The park channel carries the child's WP, captured AT THE PARK.**  The
  closer's row list gains `uexec_wp -∗` LAST, in three places that mirror
  each other row for row: `UsertrapRes.ut_park_intro_body` (the statement),
  `ParkCap.park_chan` (the token's copy of it), and
  `UsertrapRes.ut_res_bare_park` (the proof, which spends the row on
  `ut_own_nopt`'s slot conjunct).  The route is `fd_frags_any`'s exactly:
  `ParkCap.park_token_park` takes the WP as a premise beside the child's
  `fd_frags_any (pv_fdg V)` and closes over it in the `▷ park_pkg` it
  builds, feeding it to the channel's closer at resume time — so
  `park_pkg` / `forkret_park_pkg` (whose closers do not list `fd_frags_any`
  either) are UNCHANGED, and forkret, the resumer, needs no WP.
  `park_token_F`'s contractiveness is untroubled: the new row is a constant
  in `X`, and `solve_contractive` absorbs it.
  `ProofForkretPark.park_token_intro` needed no change at all — it builds
  `park_chan` from `ut_park_intro_body` by `iExact`.
- **THE TWO MINT SITES**, both `UEXEC_GEN.uexec_wp_gen` applications, both
  eliminating the `□` once into a linear WP that a park consumes:
  - `ProofUserinit`, at its `park_token_park` call (functor argument
    `(UG : UEXEC_GEN)`, tied by `LinkUserinit` to `UexecGen UserProof`) —
    the first process;
  - `ProofSysFork`, at its `kfork` call (`SysForkProof (Kfork : KFORK)
    (UG : UEXEC_GEN)`, tied by `LinkSysFork` to `UexecGen UserProof`) —
    every forked process.
  `grep -rn "uexec_wp_gen" iris/*.v` shows exactly four lines: the theorem
  (`ProofUexecWp`), the `Parameter` (`UexecWp`), and those two.
- **Why kfork's contract takes the premise.**  `SpecKfork`'s
  `wp_kfork_sconf_body` gains `uexec_wp -∗` ("the child's user-execution
  WP, consumed by the park"), threaded `ProofKforkMain.wp_kfork_sconf` →
  `kfork_arm3` → `ProofKforkB5.kfk_b5` → `park_token_park`.  That is the
  shape the verified-fork story needs: the PARENT supplies the CHILD's WP,
  so when the parent is verified the same premise takes its own
  fork-continuation deposit instead of the generic inhabitant.  sys_fork is
  kfork's only caller (userinit does not call kfork), so exactly one payer
  exists and the syscall dispatcher's table is untouched.

## The two run sites, and the circulation

Both extract the slot and run it; NEITHER deposits anything.  The parked
`Rut` is the accessor's un-applied closer,

    ProofUserretClosed.Rut_hole h p := ∃ ksp, (uexec_wp -∗ usertrap_res_bare p ksp)

— the residue MINUS a WP — and it is the trap-ENTRY seam that fills the
hole with the WP user execution just returned.  So the bundle is whole
again BEFORE any kernel excursion, and every syscall park carries a slot.
Neither run site names `USER` any more; `UserretClosed` /
`UserretClosedProof` DROPPED the `(US : USER)` functor argument
(`LinkUserretClosed` follows).  The only mints in the tree are the two
PARKS' — `ProofUserinit`'s and `ProofSysFork`'s applications of
`UEXEC_GEN.uexec_wp_gen` (above).

- **`ProofUserretClosed.stvec_handler_loop`** (each round): its `□` handler
  now takes the PAIR `user_trap_frame C pt (Rut_hole h) ∗ uexec_wp`.  It
  opens the frame, applies the holed `Rut` to the returned WP to get a
  whole `usertrap_res_bare`, and proceeds as before (rebuild the frame at
  `Rut := emp` for uservec, `wp_uservec_pt`, csrs/sstc).  At the round's
  end `usertrap_res_uwp_acc (CID := CID')` takes the slot out and the
  closer is NOT applied: it is supplied as `Rut_hole CID'` (`iExists ksp;
  iExact "Hback"`).  Then `uexec_wp_unfold` on the extracted slot and apply
  it at the round's concrete state, the paired Löb IH as the handler.  The
  `user_inv` construction that used to sit here lives in `ProofUexecWp`.
- **`UserretUser.wp_userret_user`** (the forkret entry): no longer a
  functor over `USER` — it takes `⌜loop_ok C pt⌝` (not derivable from
  userret's own premises) and the slot as premises, bridges with
  `UserKernelBridge.userret_to_user_state` (the UNPACKED bridge: from
  `umem_any pt`, delivers `∃ M`, the `u_regs` bundle at the post-sret
  state, `user_pt_inv pt M`, `user_cfg C`, with
  `⌜user_mstatus_ok (sret_ms5 mstatus0)⌝` riding inside), and applies
  the slot.  Its final premise is the PAIRED seam.  The packed
  `userret_to_user_inv` is GONE — it would have been a near-duplicate with
  no caller.  `wp_userret_closed` gets slot AND trapframe words from the
  one `usertrap_res_run_open`, applies the dovetail at
  `Rut := LP.Rut_hole CID`, and completes the tf-closer into the holed
  form — which is that `Rut`'s body verbatim.

`SpecUser.USER.wp_user_exec_closed` has exactly ONE consumer tree-wide:
`ProofUexecWp.v`.

## The step-2 layer: a verified program as a slot constructor

- **`UmodeKernelTie.v`** — movers from the slot vocabulary into the Umode
  tier's: `user_pt_inv` → `utlb_inv_pt ∗ umem` (definitional up to the
  dom pin), `u_regs` → `uv_regs ∗ gpr_file ∗ pc_is`, `uv_amb`, and the
  composite `uexec_state_uv_cap_gpr` ending in `uv_cap_gpr … ∗ pc_is`.
  ONE-DIRECTIONAL: `user_pt_inv`'s three pure facts (`dom`, `uva_pa_inj`,
  `upt_acc_wf`) are dropped on the way in and must be re-supplied from
  the table on any way back (a step-3 obligation).
- **`USyncKernel.sync_uexec_slot`** — sync's ENTRY DEPOSIT: from
  `tf_resume_pc V0 = start`, `sync_layout (pv_upt V0)`,
  `uimg_sub sync_bytes M0`, `uv_stack … (tf_w V0 tf_sp_idx) 32`, and
  `□ (∀ C, ⌜loop_ok C (pv_upt V0)⌝ -∗ uv_cap C (pv_upt V0) (xv6_sys_protocol …))`,
  conclude `uexec_slot V0 M0`.  `Hsp` is discharged by
  `tf_resume_gpr_sp` — the payoff of trapframe keying.  `Rut` and the
  handler are received and retained unused (affine): with `uv_cap` still
  an assumption, sync's traps are absorbed by the assumed round-trip
  contracts, and `uv_cap` is visibly the one gap.  Establishing the
  entry conditions — arranging the trapframe/image so a program's
  constructor applies, or falling back to `uexec_wp_slot` of the generic
  — is the INITIALIZER's job (exec, forkret's park).
- `UexecSlot.v` deliberately does not import `UmodeAbi`
  (`tf_resume_gpr_sp` is stated at `Regidx (mword_of_int 2)`, convertible
  with `sp_idx`): the verified-program tier stays out of the kernel-side
  type file's cone.

## What is deliberately NOT designed

How a DEPOSITED slot covers the kernel's own writes between deposit and
resume — a syscall's `tf->a0 := ret` / `epc += 4`, read() filling the
`(a1, a2)` buffer window of `M`, a vmfault's zero page.  It cannot be a
pure predicate on `(V, M)` pairs (read()'s widening relates the delivered
bytes to file-system state — an iProp-level fact); it will be an
iProp-based, universally-quantified shape, designed against the first
concrete proof obligation that needs it — inside the `uv_cap` discharge.
The raw material is the process side's protocol arms (`usys_ret`'s
`∀ ret`; `uv_intr_wp`'s resume wand).  See `projects/user-wp-slot.md`.
