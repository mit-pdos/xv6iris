# Project: the per-process user-execution WP slot — step 3 (real linkage)

**STATUS.**  Steps 1 and 2 are LANDED and green (full tree + `audit-only`
at the sanctioned 13 assumptions).  The design as built is
[`../design/user-wp-slot.md`](../design/user-wp-slot.md): the WP userret
runs is a residue-resident resource (`uexec_wp` in `ut_own`, extracted at
userret, re-deposited each round, minted generically at the two parks —
userinit's and sys_fork's), the trapframe-keyed `uexec_slot V M` exists
with the `uexec_wp ⊢ uexec_slot` mover, and `USyncKernel.sync_uexec_slot` is the
`sync` program's entry deposit — type-compatible with the slot, with
`uv_cap` visibly the one gap.  What follows is what is LEFT: making a
verified process actually run IN PLACE of the generic WP.

## MILESTONE G (owner-directed): the WP circulates instead of being re-minted

**LANDED** (full tree + `audit-only` at the sanctioned 13); the design as
built is in `../design/user-wp-slot.md`, and ledger item 6 below is
resolved by it.

Userret extracts the WP from the per-process resource and runs it;
the user-space WP RETURNS the next WP at its trap; usertrap re-deposits
that returned WP.  Initialization (forkret's park; later exec) is the only
place a WP is ever minted; the loop's per-round mints are deleted.  (Lane
H below moved the mint from the park's ambient world to the PARKER, but the
"initialization only" property is unchanged.)

- `uexec_wp` becomes a GUARDED FIXPOINT (`ParkCap.park_token_F` is the
  pattern): the handler premise is
  `▷ (user_trap_frame C pt Rut ∗ uexec_wp -∗ WP Loop)` — the recursive
  occurrence sits under the handler's `▷`, so the functional is
  contractive.  The generic inhabitant `⊢ □ uexec_wp` is a Löb proof that
  returns ITSELF at every trap.
- Across user execution `Rut` is the HOLED residue — the accessor's
  closer, `λ p, ∃ ksp, (uexec_wp -∗ usertrap_res_bare p ksp)`.  No new
  residue forms; `user_inv`/`user_trap_frame` take `Rut` opaquely, so the
  safety tier is untouched.  The trap-entry seam (where the loop opens
  the frame) applies the hole to the returned WP, so the residue is whole
  BEFORE the kernel excursion — syscall parks carry the slot.
- The forkret entry needs ONE combined opener on the bare residue (slot
  out + tf words borrowed + closer landing in the holed form): two
  borrows of a sealed bundle come out of one opener.
- `wp_userret_closed_body`'s public boundary and the safety tower keep
  their shapes; `US : USER` becomes unused in the loop's modules and is
  dropped; `uexec_slot`/`sync_uexec_slot` reshape their handler premise
  mechanically (the returned WP is typed at the general `uexec_wp`).
- **LANE H (follow-up, LANDED).**  The DUPLICABLE copy is gone:
  `SyscParkEnv.park_world`'s `□ uexec_wp` (and `UsertrapRes.park_world_uwp`)
  are deleted, and the child's WP is a LINEAR row the PARKER supplies, on
  the park channel, captured at the park exactly the way `fd_frags_any` is
  (`ut_park_intro_body` / `ParkCap.park_chan` / `park_token_park` /
  `ut_res_bare_park`).  `SpecKfork`'s contract gains the premise ("the
  child's user-execution WP, consumed by the park"), threaded through
  `ProofKforkMain` → `ProofKforkB5`, and sys_fork pays it
  (`SysForkProof (Kfork : KFORK) (UG : UEXEC_GEN)`, `LinkSysFork`).  A WP
  now enters the world at exactly TWO greppable `uexec_wp_gen` sites —
  userinit's park and sys_fork's kfork call — which is the contract shape
  the verified-fork story needs (the parent owes the child a WP).  Details
  in `../design/user-wp-slot.md`.

## The ledger

1. **Re-key the residue's conjunct** from the ∀-state `uexec_wp` to the
   trapframe-keyed slot at `ut_own`'s own `V` (and an `M` per item 2).
   Localized by design to `UsertrapRes.v` plus the dispatcher's deposit
   obligations (the accessor's closer is the deposit channel).  Two
   rulings to get from the owner before starting:
   - PLACEMENT: whether the conjunct stays in `ut_own` or becomes a
     `proc_priv` field proper (deferred, not rejected — it IS a
     per-process WP; the accessor seam localizes the move either way).
   - THE `sp_idx` TIER QUESTION: `UexecSlot.v` deliberately does not
     import `UmodeAbi` (`tf_resume_gpr_sp` is stated at
     `Regidx (mword_of_int 2)`, convertible with `sp_idx`).  If the
     re-key puts `uexec_slot` into `UsertrapRes.v`'s cone and anyone
     wants the `sp_idx` spelling, `UmodeAbi` enters the residue's build
     path — rule first.

2. **Pin the image for a verified process.**  Both run sites today
   receive `M` existentially (`umem_any` at the entry, `user_pt_any` from
   `uservec_post`).  A verified mode of the residue must carry
   `umem_own`-at-a-known-`M` — `M` is the one resume ingredient `V` does
   not determine.  Nothing landed depends on the image being anonymous,
   so this is additive.

3. **Boundary exposure.**  For the loop to apply a trapframe-keyed slot,
   the round's post must EXPOSE that the returned registers are the
   residue's trapframe words and the returned memory its image.
   `SpecUserret.wp_userret_pt` already says the register half at its own
   level (its continuation returns `userret_gpr m vra…` built from the
   tf-word arguments — lane D confirmed the loop's application tuple is
   literally the `tf_resume_gpr b V` / `tf_resume_pc V` pair); the
   composed `wp_uservec_pt` post must stop existentially hiding it.

4. **The deposit-covering formulation** — how a deposited slot covers the
   kernel's own writes between deposit and resume (a syscall's
   `tf->a0 := ret` / `epc += 4`; read() filling the `(a1, a2)` buffer
   window; a vmfault's zero page).  DELIBERATELY UNDESIGNED (owner
   ruling): it cannot be a pure predicate on `(V, M)` pairs — read()'s
   widening relates the delivered bytes to file-system state, an
   iProp-level fact — so it will be an iProp-based,
   universally-quantified shape, designed against the first concrete
   proof obligation inside item 5.  Raw material on the process side:
   `usys_ret`'s `∀ ret` continuation (the syscall case) and
   `uv_intr_wp`'s resume wand (the identity case).

5. **Discharge `uv_cap` from the kernel** (usertrap/userret round trip +
   per-syscall kernel specs) — the step that turns `sync_uexec_slot`'s
   one assumption into a theorem.  Known shape: `uv_cap` is `□` while the
   residue is linear, resolved by the Umode tier's frames
   (`uv_trap_frame`, `uv_run`) gaining a `Rut pt` conjunct — the parked
   residue travels in the frames exactly as the safety tier's do; the
   tier's port history says the `USpec*`/`UProof*` statements tolerate an
   opaque added conjunct, and the engine (`WpUmodeStep`) is where it
   lands.  Also owed here: the reverse direction of
   `UmodeKernelTie`'s movers — `user_pt_inv`'s three pure facts
   (`dom M = uva_dom pt`, `uva_pa_inj`, `upt_acc_wf`) are dropped on the
   way into the Umode tier and must be re-supplied from the table on the
   way back.
