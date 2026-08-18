# THE USER TIER PORT PLAN (`UserExec` + 44 dependents) onto per-node semantics

Branch `hart-node-port`.  Everything below is either **[V]** verified by reading
the tree (file:line given) or **[A]** assumed / to be checked by the agent that
does the work.  Design of record: `claude-notes/design/main-cycle-port.md`;
worklist: `claude-notes/projects/main-cycle-port.md`, "THE USER TIER".

---

## 0. THE SPINE, IN ONE PARAGRAPH

A user hart OWNS every register and every byte its cycle can touch — with
**exactly one exception, the two PLIC wires**.  So the port is NOT a per-node
rewrite of the user tier: it is

> **CHOP THE CYCLE AT THE DISPATCH; EVERYTHING ELSE IS ONE
> `HartMemRun.swp_hmrun_of_exec` PER MODEL CALL, DRIVEN BY THE EXEC FACTS THE
> TIER ALREADY HAS PLUS A `goodmb` CERTIFICATE.**

and the single move that makes the whole thing cheap is the choice of the
reference state:

```coq
s := MState rs mm dev0_state          (* rs = the frames' file, mm = the owned bytes *)
```

because then `swp_hmrun_of_exec`'s two hard-looking premises
(`reg_agree_on (Drw ∪ Dro) rs s.(sregs)` and `mm ⊆ s.(mem)`,
`HartMemRun.v:1177-1178`, statement at 1171) are `reflexivity` and `⊆`-reflexivity **[V]**, and the
landing map is *literally* `s'.(mem)` (dom is preserved by `write_bytes`, and
`hmrun_of_exec_after` returns `mm' ⊆ s'.(mem) ∧ dom mm' = dom mm`,
`HartMemRun.v:1023-1032` **[V]**).  Every `exec` fact in the tier is
∀-quantified over σ with premises that are register lookups and memory
contents, so it applies at that state unchanged.

Consequence: the ~11 k lines of the tier split into
* a **PURE `⟨exec, goodmb⟩` layer** — the existing exec facts verbatim, each
  gaining a `goodmb` twin.  7 of the 33 `User*.v` files are already
  Iris-free and survive byte-identical (4 547 lines: `UserBits` 645,
  `UserCsr` 1303, `UserExecFacts` 1029, `UserFetch` 466, `UserMem` 297,
  `UserMemArms` 731, `UserTranslate` 76) **[V, `grep -c riscvGS`]**;
* a **thin Iris layer** — one `swp_hmrun_of_exec` per model call, one frame
  bridge, one byte-map accessor, and the extended cycle rule.

---

## 1. PRE-CHECKS (the five things a fresh agent would get wrong)

### 1.1 **[V] LR/SC ARE STUCK UNDER PER-NODE SEMANTICS.  THIS IS A SAFETY HOLE, AND IT IS THE FIRST THING TO FIX.**

`load_reservation` and `cancel_reservation` are **opaque monadic axioms** of the
model:

```coq
Axiom load_reservation   : forall (_ : mword (if 64 =? 32 then 34 else 64)) (n : Z), M unit.   (* rv64d.v:21793 *)
Axiom cancel_reservation : forall (_ : unit), M unit.                                          (* rv64d.v:21802 *)
```

Under whole-cycle stepping this was harmless: `RiscvExec.exec` is stuck on them
and `UserMemAccess.v:45,49` simply *axiomatised the interpreter's answer*
(`exec (load_reservation a w) s = Some (tt, s)`).  Under per-node stepping
`mnode_step` matches on the monad's **constructors** (`RiscvLang.mnode_step:594`), so
an opaque constant application has **no arm at all** — the configuration is
irreducible.  Adequacy is `NotStuck`, and arbitrary user code may execute
`lr`/`sc` (the tier proves totality for them: `UserMemArms.exec_execute_LOADRES_u_ok:204`,
`_STORECON_u_ok:246`, `UserMemClassify.arm_LOADRES_u:3456`, `arm_STORECON_u:4460`)
— so the user-tier theorem would become unprovable, not merely inconvenient.

**FIX (do this first, it is 20 lines and it unblocks four files).**  Replace the
two `exec`-level axioms by TERM-level ones, in `UserMemAccess.v` §0 (or better,
hoist to a new `ResvAxioms.v` so `ArchReset`/`ColdBoot` share them):

```coq
Axiom load_reservation_term :
  forall (a : mword (if 64 =? 32 then 34 else 64)) (n : Z),
    load_reservation a n = Defs.returnm tt.
Axiom cancel_reservation_term :
  forall (u : unit), cancel_reservation u = Defs.returnm tt.
```

Both existing `exec_*` axioms become one-line corollaries (`rewrite …; apply
exec_returnm`), `goodb`/`goodmb`/`hmrun` all compute on them, and the machine
steps them as `Ret tt`.  It is strictly a refinement (`load_reservation := λ _ _,
Ret tt` realises both), and it removes two axioms while adding two.
`ArchReset.v:29-38` and `ColdBoot.v:30` already reason about
`cancel_reservation` inside `reset_sys` and will simplify.

**[V]** the only other opaque `M`-valued axioms are `get_16_random_bits`
(Zkr seed CSR — illegal at U) and `plat_term_read/_write` (HTIF, dead under the
tier's `htif_tohost_base = None` premise, `rv64d.v:23255`).  `match_reservation`
and `valid_reservation` are pure `bool` axioms and are destructed both ways
already — no change.

### 1.2 **[V] `bytes_own` AND `user_pt_inv` ALREADY AGREE ON THE DATA PAGES; THE PT PAGES NEED ONE NEW LEMMA.**

* `UserPtTree.udata_own data := ∃ dm, ⌜dom dm = data⌝ ∗ [∗ map] a ↦ b ∈ dm, a ↦ₚ b`
  (`UserPtTree.v:150-153`) is **definitionally** `∃ dm, ⌜dom dm = data⌝ ∗
  HartMemRun.bytes_own dm` (`HartMemRun.v:168`).  Zero work.
* `utlb_inv_pt` holds `ptree_own 2 (DfracOwn 1) t` (`UptTree.v:639`), whose page
  layer is `pt_node_claim (pt_base t) ∗ [∗ list] i ∈ seqZ 0 512, u_pte_addr … ↦ₚ₈{dq} pt_ents t …`
  (`PtTree.v:928-943`), and `↦ₚ₈` is `⌜aligned⌝ ∗ [∗ list] j ∈ seq 0 8, ↦ₚ`
  (`RiscvPtsto.v:1339-1341`).  So the slot bytes ARE `↦ₚ` cells; what is needed
  is a *pure* byte-map view `ptree_bytes : ptree -> gmap pa (bv 8)` and
  `ptree_own_bytes : ptree_own 2 dq t ⊣⊢ pt_claims t ∗ bytes_own (ptree_bytes t)`
  (the `pt_node_claim` ghosts are NOT bytes and stay on the side).  New work,
  ~200 lines in `PtTree.v`/a new `PtBytes.v`.
* `addr_is_ram` (needed to discharge `goodmb`'s `negb (dev_addr pa)`) is a
  RESOURCE fact today (`RiscvPtsto.phys_ram:2248`, used at
  `UserFetchPt.v:80-91`).  It must be extracted **once** into the pure
  side-condition: `bytes_own mm ⊢ ⌜∀ a, a ∈ dom mm -> addr_is_ram a⌝`
  (big_sepM + `phys_ram`), then `RiscvPtsto.addr_is_ram_not_dev:889` **[V]**
  gives `dev_addr = false` for every access inside `dom mm`.
* Disjointness of the tree bytes from the data bytes — which is what makes a
  user store unable to corrupt a PTE — is today implicit in the separating
  conjunction.  It must likewise be extracted once
  (`bytes_own m1 ∗ bytes_own m2 ⊢ ⌜m1 ##ₘ m2⌝`, from `↦ₚ` exclusivity) and
  carried as a pure conjunct of `u_mem_wf`.

### 1.3 **[V] THE "FOOTPRINT CANNOT RUN SYMBOLIC OPERANDS" TRAP DOES NOT APPLY HERE.**

`projects/main-cycle-port.md`'s trap list says a footprint walker "CANNOT run an
instruction with SYMBOLIC operands" because `hfrun` answers a read by
`bool_decide (r ∈ D)`, which does not compute at a symbolic index.  That killed
the M-mode "convert `gpr_file` into `hreg_frame`" plan.  **It does not bind the
user tier**, because nothing here ever *computes* the walker: `hmrun_of_exec`
discharges the very same `bool_decide` by `bool_decide_eq_true_2` from the
certificate's `Dr r = true -> r ∈ D` (`HartMemRun.v:620,628` **[V]**).  So the
user tier MAY and SHOULD put all 31 GPRs in `Drw`, with

```coq
Definition Du_gpr (r : register) : bool :=          (* x1..x31, 31-way *)
  match r with R_bitvector_64 x => is_gpr_reg x | _ => false end.
Lemma Du_gpr_of_Z (i : mword 5) : uint i <> 0 -> Du_gpr (R_bitvector_64 (gpr_of_Z (uint i))) = true.
Lemma u_gpr_in_Drw (i : mword 5) : uint i <> 0 -> (R_bitvector_64 (gpr_of_Z (uint i)) : register) ∈ u_Drw.
```

both by the same 32-way `lia` split `WpGpr.exec_rX_bits_gpr:46` already uses
**[V]**.  Say this loudly in the file header; it is the single most likely
re-discovery.

### 1.4 **[V] THE ONLY OFF-FRAME REGISTERS ARE `sig_meip` / `sig_seip`.**

Enumerated against `UserStep.exec_getPendingSet_U_reduce:56` and the cycle's
reads: cur_privilege, mstatus, misa, mseccfg, elp, senvcfg, mstateen0,
sstateen0, menvcfg, medeleg, stvec, mie, mideleg, satp, tlb, pmpcfg_n,
pmpaddr_n, pma_regions, htif_tohost_base, hart_state, PC, nextPC, minstret,
minstret_increment, mcountinhibit, minstretcfg, mcycle, mtime, mip, scause,
stval, sepc, x1..x31 — **all owned** by `user_regs` / `user_cfg` / `hw_config` /
`pc_is` / `utlb_inv_pt` (`UserExec.v:294-346`, `RiscvFetchExec.hw_config:277`,
`InstrBytes.pc_is:696`, `MinstretInv.clock_res:349`/`minstret_res:359`,
`UptTree.utlb_inv_pt:628`).  The wires live in `WireInv.wire_inv` and are read
∀-bound by `WpMmodeCsrSwp.swp_read_reg_any`, **which needs no ownership at all**
(`WpIntrCore.v:160-171` **[V]**).  `mtimecmp`/`stimecmp` are read only by
`tick_clock`, which is absorbed by `swp_tick_clock_any` inside `wp_loop_cycle`
(design §5 items 7b/7c) — outside the tier's obligation.

**CONSEQUENCE, and it is a simplification worth banking: the user tier no
longer needs `wire_inv` OR `clock_inv` at all.**  `UserExec.clock_mip_acc:251`
and every `iInv "Hwinv"` in `UserStepFull.v:221,228` / `UserStep.v:402` /
`WpUmodeStep.v:258,267` are DELETED: `mip` is now owned through `pc_is`'s
`clock_res`, and the wires are peeled, not borrowed.

### 1.5 **[V] `swp_try_step_any` REFUSES FOUR OF THE SIX ARMS THE USER TIER NEEDS.**

`HartStepAny.swp_try_step_any:106` and `swp_exec_step_any:321` accept only
`Step_Execute (Retire_Success tt, _)` and `Step_Pending_Interrupt`; every other
`Step` is `| _ => False` (`HartStepAny.v:141`, and its header at line 37 says so).
The user tier needs, additionally: `Step_Execute (Trap (…))`,
`Step_Execute (Illegal_Instruction tt)`, `Step_Execute (Enter_Wait wr)`,
`Step_Fetch_Failure`, plus the WAITING-hart entry (`Step_Waiting`).  The exec
shape of each tail is already written and proved:
`UserTrap.exec_riscv_step_fetch_failure:327`, `_execute_illegal:382`,
`_execute_trap:433`, `UserStep.exec_riscv_step_enter_wait` (§7),
`_wait_stay`/`_wait_wake` (§1b) **[V]** — each is the same
`handle_* ; read hart_state ; tick_pc ; retired=false` shape, so each new arm of
the swp rule is a ~40-line branch mirroring one of them.

---

## 2. QUESTION 1 — THE NEW STATEMENTS

### 2.1 `user_regs` — the only definition that really changes

```coq
  (* the per-step mutable register cells + the cells the CYCLE WRAPPER owns.
     mip/mcycle/mtime are OWNED now (MinstretInv.clock_res): there is no
     clock invariant to borrow them from, and no [uc_mip] problem -- their
     values are existential per step, which is what [clock_res] already says. *)
  Definition user_regs (hs : HartState)
      (ms_v sc_v stval_v sepc_v va va' : mword 64) (g : regfile) : iProp Σ :=
    (hart_state ↦ᵣ hs ∗
     cur_privilege ↦ᵣ User ∗
     mstatus ↦ᵣ ms_v ∗ scause ↦ᵣ sc_v ∗ stval ↦ᵣ stval_v ∗ sepc ↦ᵣ sepc_v ∗
     PC ↦ᵣ va ∗ nextPC ↦ᵣ va' ∗
     minstret_res ∗ clock_res ∗ resv_any cpu_id ∗          (* NEW: the three pc_is riders *)
     gpr_file g)%I.
```

* `minstret_res` = `∃ mst mi mc micfg, minstret ↦ᵣ mst ∗ minstret_increment ↦ᵣ mi ∗ mcountinhibit ↦ᵣ□ mc ∗ minstretcfg ↦ᵣ□ micfg` (`MinstretInv.v:359`).
* `clock_res` = `∃ c t p, mcycle ↦ᵣ c ∗ mtime ↦ᵣ t ∗ mip ↦ᵣ p` (`MinstretInv.v:349`).
* `resv_any cpu_id` = `∃ r, resv_frag cpu_id r` (`RiscvPtsto.v:1773`).

**WHY EXACTLY THESE THREE AND NOT `pc_is`:** `pc_is x` bundles
`PC ↦ᵣ x ∗ nextPC ↦ᵣ x ∗ minstret_res ∗ clock_res ∗ resv_any`
(`InstrBytes.v:696-701` **[V]**), i.e. it *forces PC = nextPC*.  The WAITING
state decouples them (`UserExec.v:325-333` — the enter-wait step skips the
tick), so `user_regs` must keep PC/nextPC separate.  Add the bridge both ways so
the two boundaries (userret in, uservec out) still speak `pc_is`:

```coq
  Lemma user_regs_pc_is hs ms sc stv sep va g :
    user_regs hs ms sc stv sep va va g ⊣⊢
      hart_state ↦ᵣ hs ∗ cur_privilege ↦ᵣ User ∗ mstatus ↦ᵣ ms ∗ scause ↦ᵣ sc ∗
      stval ↦ᵣ stv ∗ sepc ↦ᵣ sep ∗ pc_is va ∗ gpr_file g.
```
(`iSplit`+`iFrame`, 8 lines; `pc_is` is a plain `∗`-chain so this is definitional
up to reassociation.)

`user_hart_ok`, `user_mstatus_ok`, the lock-step conjunct, `user_pt_inv`,
`user_cfg`, `Rut pt` — **unchanged**.  `user_inv` therefore keeps its exact
shape (`UserExec.v:348`), and so does `user_trap_frame` (`UserExec.v:367`),
which already carries `pc_is (stvec_base …)` and so already carries the three
new riders **[V]**.

`user_trap_frame_intro` (`UserExec.v:385`) takes `PC ↦ᵣ … -∗ nextPC ↦ᵣ …`; it
gains three arguments (`minstret_res -∗ clock_res -∗ resv_any cpu_id -∗`) or,
better, ONE (`pc_is (stvec_base (uc_stvec C)) -∗`) — prefer the latter, it is
what every producer will have.

### 2.2 `ucfg` — delete the anti-`uc_mip` note, keep the record

`UserExec.v:89-127`'s `ucfg` is unchanged in DATA, but the long comment where
`uc_mip` "cannot be" a field (`UserExec.v:96-113`) is now obsolete and must be
rewritten: mip is owned per hart, the exclusivity clash with `clock_inv` is
gone, and mip's value is still existential per step (the tick writes it) — so
still no field, but for a different reason.  Same for `MipBorrow`/`clock_mip_acc`
(`UserExec.v:236-262`): **delete the whole section**, 30 lines.

### 2.3 The two obligations

`user_step_obligation` (`UserExec.v:413`) and `user_step_obligation_active`
(`UserExec.v:424`) keep their statements **byte-identical** — they mention only
`user_inv` / `user_regs` / `user_pt_inv` / `user_cfg` / `Rut` / `WP Loop`, all of
which keep their spelling.  That is the load-bearing fact for the 44 dependents:
**no consumer of the tier's interface sees the port.**

`stvec_handler_wp` (`UserExec.v:404`) and `wp_user_exec` (`UserExec.v:448`):
unchanged, proof unchanged (pure Löb over the obligation).

### 2.4 Every external consumer, and how it closes

| consumer | uses | what changes |
|---|---|---|
| `UserKernelBridge.userret_to_user_inv:87` | builds `user_inv` from userret's cells; **destructures `pc_is`** at line 156 (`iDestruct "Hpc" as "[Hpcc Hnpc]"`) | ONE line: `iDestruct (pc_is_open …)` → frame `minstret_res`/`clock_res`/`resv_any` into `user_regs`.  This is exactly the "6 files destructure `pc_is`" breakage the worklist predicts **[V]** |
| `UserKernelBridge.user_trap_frame_open:190` | opens `user_trap_frame` | unchanged (it already re-exports `pc_is`) |
| `UserretUser.v:231,247` | `userret_to_user_inv` then `U.wp_user_exec_closed` | unchanged if `SpecUser.wp_user_exec_closed_body` keeps its premise list |
| `SpecUser.wp_user_exec_closed_body:57` | `hw_config -∗ minstret_inv -∗ wire_inv -∗ user_inv -∗ ▷ stvec_handler_wp -∗ WP Loop` | **KEEP `minstret_inv` and `wire_inv` as ignored premises for now.**  Both are dead after the port (`minstret_inv := emp` already, `MinstretInv.v`; `wire_inv` unused per §1.4).  Dropping them is a weakening, but it is a STATEMENT diff at 2 call sites (`UserretUser.v:247`, `ProofUser.v:69`) — do it in one separate premise-removal commit together with the tree-wide `minstret_inv` deletion the worklist already schedules |
| `ProofUser.wp_user_exec_closed:68` | discharges the totalities into the spec | unchanged (it just applies `wp_user_exec_full`) |
| `SpecUservec.v:304`, `ProofUservec.v:118` | consume `user_trap_frame` | unchanged — `user_trap_frame`'s shape is preserved.  uservec's own proof is red for the *kernel*-side port reasons, not the tier's |
| `SpecUsertrap.v:491`, `UsertrapRes.v` | `Rut pt` = `∃ ksp, usertrap_res pt ksp`, opaque to the tier | unchanged |
| `ProofUserretClosed.v:101-148` | builds `user_trap_frame` at another hart and re-enters `wp_user_exec_closed`; uses `user_trap_frame_intro` and rebuilds `user_cfg` | ONE call site of `user_trap_frame_intro` gains the `pc_is` argument |
| `UmodeCap.v:109`, `UmodeFrame.v:66`, `WpUmodeStep.v` (the VERIFIED Umode tier) | reuse `ucfg`, `user_mstatus_ok`, `u_dispatch`, `interrupt_branch`, the trap tower | **out of scope of this plan but ported by the same bricks**; `WpUmodeStep.wp_uv_step_gen:239` is `wp_user_step_active`'s twin, wire/mip borrow included.  Schedule it immediately after, as a separate worklist; it costs the same seam and nothing new |

---

## 3. QUESTION 2 — THE STEP ENGINE: ONE USER CYCLE, PER NODE

### 3.1 The frames

New file **`UserFrame.v`** (mirror of `HartSFrame.v:65-151`, which is 498 lines
for 25 cells **[V]**):

```coq
Definition u_Drw : gset register :=            (* WRITTEN somewhere in a user cycle *)
  {[ PC; nextPC; hart_state; cur_privilege; mstatus; scause; stval; sepc;
     minstret; minstret_increment; mcycle; mtime; mip; tlb ]} ∪ u_Dgpr    (* + x1..x31 *)
Definition u_Dro : gset register :=            (* READ only *)
  {[ misa; mseccfg; pma_regions; htif_tohost_base; elp; senvcfg;
     mcountinhibit; minstretcfg;                       (* minstret_res, discarded *)
     stvec; mie; mideleg; medeleg; menvcfg; mstateen0; sstateen0;   (* user_cfg *)
     satp; pmpcfg_n; pmpaddr_n ]}                                   (* utlb_inv_pt *)
Definition Du_r (r : register) : bool := (* boolean image of u_Drw ∪ u_Dro *)
Definition Du_w (r : register) : bool := (* boolean image of u_Drw *)
Definition Df_u (r : register) : dfrac := (* uc_dqc C on the user_cfg cells, DfracDiscarded on hw_config's *)
```

**cur_privilege and mstatus are in `Drw`, not `Dro`** (unlike S-mode): the trap
tower writes both (`UserTrap.v:104-120` — five mstatus writes and the
cur_privilege write).  `hart_state` is in `Drw`: the enter-wait/wake steps write
it.  `tlb` is in `Drw`: the fill.

**NO REGISTER TOWER.**  `HartSFrame.s_rs:171` builds a `register_set` tower so a
leaf can compute lookups.  The user tier must NOT: it never computes at a
symbolic file, and the durable notes record two measured disasters for towers
("A `Definition` for an intermediate register file is a conversion bomb";
"Never `rewrite` between two register-file towers").  Instead the frame's file
is an ordinary existential `rs : regstate` and every needed value is a pure
side-condition `register_lookup r rs = v` — which is precisely what `user_inv`'s
existentials already are.  Deliver the ~35 membership lemmas as standalone
`u_in_*` / `u_w_*` names (`HartSFrame.v:90-151` is the template) and never call
`set_solver` inside a proof (`optimization.md`).

Two bridges (new file **`UserFrames.v`**, the `WpSFrames.v` analogue but much
smaller because there is no tower):

```coq
  Lemma u_frames_intro (rs : regstate) hs ms sc stv sep va va' g :
    ⌜u_pins rs hs ms sc stv sep va va' g⌝ -∗          (* the 30-odd register_lookup facts *)
    user_regs hs ms sc stv sep va va' g -∗ user_cfg C -∗ hw_config -∗ upt_regs pt -∗
    hreg_frame rs u_Drw ∗ hreg_frame_ro Df_u rs u_Dro ∗ resv_any cpu_id.
  Lemma u_frames_elim (rs : regstate) : (* the converse, at any file agreeing on the pins *)
```

`gpr_file g ⊣⊢ ⌜g (Regidx 0) = zero_reg⌝ ∗ hreg_frame rs u_Dgpr` under
`gpr_agree g rs` (31-way `big_sepM`↔`big_sepS`; `WpGpr.gpr_pt:100` is a
points-to for x1..x31 and a pure fact for x0 **[V]**).  Used TWICE per user
phase (entry and trap exit), not per step.

### 3.2 The cycle rule: `swp_try_step_full`

New file **`HartStepFull.v`** (above `HartStepAny.v`, so the ~1000-file cone of
a bottom-of-tree edit is not paid; fold back at a milestone, as
`HartStepAny.v:52` itself says).  Statement = `swp_try_step_any`
(`HartStepAny.v:106`) with the body's match extended:

```coq
    (resv_frag cpu_id None -∗ hreg_frame rsA Drw -∗ hreg_frame_ro Df rsA Dro -∗
       swp (run_hart_active 0)
         (fun st => ∃ rs2 : regstate, ⌜Q rs2⌝ ∗
            match st with
            | Step_Execute (Retire_Success tt, _)   => frames rs2 ∗ Psi
            | Step_Pending_Interrupt (i, p)         => swp (handle_interrupt i p) (fun _ => frames rs2 ∗ Psi)
            | Step_Execute (Illegal_Instruction tt, ib) =>
                swp (handle_exception (zero_extend' 64 ib) (E_Illegal_Instr tt)) (fun _ => frames rs2 ∗ Psi)
            | Step_Execute (Trap (p, exc, pcx), _)  =>
                swp (bind (exception_handler p exc pcx) set_next_pc)      (fun _ => frames rs2 ∗ Psi)
            | Step_Fetch_Failure (Virtaddr xv, e)   =>
                swp (handle_exception xv e)                              (fun _ => frames rs2 ∗ Psi)
            | Step_Execute (Enter_Wait wr, ib)      =>
                ⌜wait_is_nop wr = false⌝ ∗ frames rs2 ∗ Psi        (* the arm WRITES hart_state itself *)
            | _ => False
            end))
```

and the tails read off the five `exec_riscv_step_*` proofs listed in §1.5: the
four trap-ish arms are `retired = false` (no minstret bump, `and_boolM (returnM
false) _` short-circuits — `UserTrap.v:355-362` **[V]**), the enter-wait arm
writes `hart_state := HART_WAITING (wr, ib)` and takes **no** `tick_pc`, so its
`Q` must be allowed to land on a file with `hart_state ≠ ACTIVE` (relax
`swp_try_step_any`'s `HQhart` premise into a per-arm one).
Then `swp_exec_step_full` = the `wp_loop_cycle`/`swp_tick_wrap` wrapper exactly
as `swp_exec_step_any:321` does it (**re-use that proof verbatim**, only `Q`'s
hart_state obligation moves).

A second rule for the WAITING hart, `swp_try_step_waiting` (same file):
prelude, `read hart_state = HART_WAITING (wr,ib)`, then
`swp (run_hart_waiting 0 wr ib false)` — which is a REGISTER-ONLY stretch over
mip/mie/hart_state, all owned now, so it is ONE `swp_hmrun_of_exec` off
`UserStep.exec_run_hart_waiting_wake:170` / `_wake_resv:191` / `_stay:212`
(three arms, `valid_reservation` is a pure bool axiom — destruct it) plus three
2-line `goodmb` twins.  Its two tails are `Step_Waiting` (nothing, `retired=false`)
and `Step_Execute (Retire_Success tt, ib)` (tick + bump), i.e.
`UserStep.exec_riscv_step_wait_stay` / `_wait_wake` node for node.

**Size: ~600 lines for `HartStepFull.v`.**  It is the single largest new piece
of *generic* machinery and it is privilege-agnostic — state it that way, the
S-mode kernel will want the exception arms when `WpSmodeWfi` lands.

### 3.3 The dispatch at User — **BUILT**, in `HartRunFull.v`

`swp_dispatchInterrupt_U` (and its `swp_getPendingSet_U` half) is in
`HartRunFull.v`, NOT in `WpIntrCore.v`: the file is edited by the S-mode lane,
and the U rule's only need of it is `s_pending` plus the two privilege-free
wire lemmas, which it imports.  The one change against the sketch below is the
spelling of the answer: `HartRunFull.dispatch_of_pending : mword 64 -> option (InterruptType *
Privilege)` is the decision ONCE THE PENDING SET IS KNOWN — the shared core of
`WpIntrCore.s_dispatch` (Supervisor, SIE-gated) and `UserStep.u_dispatch`
(User, ungated).  `u_dispatch a b c d e = dispatch_of_pending (s_pending a b c
d e)` **by `reflexivity` [V, checked]**, so the tier bridges it in one line —
or, better, `UserStep.u_dispatch`'s body becomes that application and the
duplicate goes away.

```coq
  Lemma swp_dispatchInterrupt_U (Drw Dro : gset register) (Df : register -> dfrac)
      (rs : regstate) (dst : mstate) (Db : register -> bool) (mip_v mie_v mdv_v : mword 64) :
    Drw ## Dro ->
    (mip : register) ∈ Drw ∪ Dro -> (mie : register) ∈ Drw ∪ Dro ->
    (mideleg : register) ∈ Drw ∪ Dro ->
    register_lookup mip rs = mip_v -> register_lookup mie rs = mie_v ->
    register_lookup mideleg rs = mdv_v ->
    and_vec mie_v (not_vec mdv_v) = zeros' 64 ->
    (forall r, Db r = true -> r ∈ Drw ∪ Dro) ->
    (forall r, Db r = true -> register_lookup r rs = register_lookup r dst.(sregs)) ->
    exec (currentlyEnabled Ext_S) dst = Some (true, dst) ->
    goodb Db (currentlyEnabled Ext_S) dst = true ->
    gen_cert -∗ hreg_frame rs Drw -∗ hreg_frame_ro Df rs Dro -∗
    swp (dispatchInterrupt User)
      (fun r => ∃ meip seip : mword 1,
                ⌜r = dispatch_of_pending (s_pending mip_v meip seip mie_v mdv_v)⌝ ∗
                hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro).
```

Proof = `swp_dispatchInterrupt_S`'s (`WpIntrCore.v:383-427`) with the two
`or_boolM` enable blocks *deleted*: at User both effective enables
short-circuit **without reading mstatus** (`and_boolM (returnM false) _`,
`UserStep.v:70-100` **[V]**), so the U rule needs **no mstatus premise at all**
and is strictly simpler than the S one.  Reuse `swp_read_mip_S:179` and
`swp_external_interrupts_pending_S:141` verbatim — they are privilege-free.
`u_dispatch` (`UserStep.v:47`) and `exec_dispatchInterrupt_U_reduce:120` are
the map it mirrors; both stay.

### 3.4 `run_hart_active` at User: the fetch/decode/execute peel — **BUILT**

`HartRunFull.v`.  What a caller applies:

* `swp_run_hart_active_full` — the core.  Dispatch obligation identical to
  `HartRunGen.swp_run_hart_active_gen`'s; fetch obligation
  `swp (fetch tt) (run_fetch_post Drw Dro Df Pe Pf Px)`; conclusion
  `fun st => match st with Step_Pending_Interrupt (ii,pr) => Qi ii pr
  | Step_Execute (r,ib) => Pe r ib | Step_Fetch_Failure (Virtaddr xv,e) =>
  Pf xv e | Step_Ext_Fetch_Failure x => Px x | Step_Waiting _ => False end`.
  That IS `swp_try_step_full`'s body postcondition once `st` is destructed
  (the body's `∃ rs2, ⌜Q st rs2⌝ ∗ …` goes INSIDE each `P`), so the two meet
  with one `swp_mono`.
* `swp_run_hart_active_U` — the core with the dispatch discharged by §3.3,
  `Qi` baked (the wire values are not known until the dispatch has run, so the
  existential lives in the payload, as in `swp_run_hart_active_S`).
* the five instances, each pinning the fetch's shape and reading off one exec
  composer: `swp_run_hart_active_base` / `_base_redirect` / `_rvc` /
  `_rvc_direct` / `_fetch_fail`.  Their conclusion is `HartRunGen`'s
  disjunctive one generalised from `RETIRE_SUCCESS` to any `resf`, so
  `swp_run_hart_active_gen` is the `resf := RETIRE_SUCCESS` instance.

The obligations the fetch and execute agents write to:

```coq
  (* run_fetch_post Drw Dro Df Pe Pf Px : FetchResult -> iProp Σ *)
  | F_Base w        => run_fetch_base Drw Dro Df Pe w
  | F_RVC h         => run_fetch_rvc  Drw Dro Df Pe h
  | F_Error (e, xv) => Pf xv e
  | F_Ext_Error x   => Px x

  (* run_fetch_base: rsf is EXISTENTIAL -- a filling walk does not land where
     it started -- so the decode certificate and the lpad refusal are stated
     about rsf HERE rather than as premises of the rule *)
  ∃ (rsf : regstate) (i : instruction) (pc : mword 64) (nl : nat),
    ⌜register_lookup PC rsf = pc⌝ ∗ ⌜hval (Drw ∪ Dro) Drw rsf (ext_decode w) i rsf⌝ ∗
    ⌜hfrun nl (Drw ∪ Dro) Drw rsf (is_landing_pad_expected tt) = Some (false, rsf)⌝ ∗
    hreg_frame rsf Drw ∗ hreg_frame_ro Df rsf Dro ∗
    (frames (register_set nextPC (add_vec_int pc 4) rsf) -∗
       swp (execute i) (run_exec_post Pe (zero_extend' 32 w)))
  (* run_fetch_rvc adds ⌜hfrun nz … (currentlyEnabled Ext_Zca) = Some (true, rsf)⌝
     (hand it HartRunGen.hfrun_cE_Zca) and uses nextPC+2 *)

  (* run_exec_post Pe ib : ExecutionResult -> iProp Σ -- the redirect is a
     SECOND swp inside the FIRST execute's post, not a side condition *)
  | ExecuteAs other => swp (execute other) (fun e' => Pe e' ib)
  | _               => Pe e ib
```

`run_exec_post_direct` (needs `match e with ExecuteAs _ => False | _ => True
end`) and `run_exec_post_redirect` are the two introduction forms.

Why each generalisation is forced, kept because it is the design:

1. **the FETCH obligation becomes match-shaped** — the model's `fetch` can
   answer `F_Base w`, `F_RVC h` or an error that `run_hart_active` early-returns
   as `Step_Fetch_Failure`.  The existing rule hardcodes `⌜r = F_Base w⌝`.
2. **the EXECUTE obligation becomes result-generic** — `⌜e = RETIRE_SUCCESS⌝`
   becomes an arbitrary `r : ExecutionResult` with the postcondition matching,
   because the user tier's four outcomes (`UserClassify.u_result_ok:26` **[V]**)
   include Trap / Illegal / Enter_Wait.
3. **the `ExecuteAs` redirect** — a second execute obligation, as in
   `UserStep.exec_hart_active_progress_base_redirect_gen` (§6) and
   `_RVC_direct_gen` (§6b).

Deliver it as ONE core rule plus four ~50-line instances matching the four exec
composers the tier already has (`SmodeCore.exec_hart_active_progress_base_gen`,
`_RVC_gen`, `UserStep`'s `_base_redirect_gen`, `_RVC_direct_gen`) plus the
fetch-failure instance.  **~500 lines.**

### 3.5 The fetch, the decode, the execute: ONE `swp_hmrun_of_exec` EACH

This is the payoff, and it is why the user tier does NOT need
`CommonWalk.swp_pt_walk_user_ex` / `swp_translate_TLB_miss_user_ex`
(`CommonWalk.v:1508,1604` **[V]** — those exist for the *kernel* table, which is
invariant-held and opened per read node, so its leaf cannot be pinned across the
walk; the *user* table is exclusively owned by the hart, so the whole walk fits
inside one certificate).

```coq
  (* the fetch obligation of HartRunFull, discharged in one application *)
  iApply (swp_hmrun_of_exec Du_r Du_w u_Drw u_Dro Df_u (fetch tt)
            (MState rs mm dev0_state) sf iw rs mm
            u_disj u_Dr_sub u_Dw_sub (reg_agree_refl _ _) (map_subseteq_refl _)
            Hgoodmb_fetch Hexec_fetch with "Hcert Hany Hrw Hro Hown").
```

with `Hexec_fetch` **the existing** `UserFetchPt.user_pt_fetch_instr:160` made
PURE (see §4.2) and `Hgoodmb_fetch` its new certificate.  Same for
`swp (execute i)` (from `base_exec_total_u`'s exec disjunct) and for each trap
tower.  The decode stays on `HartGoodb.hval_of_goodb` exactly as today
(`UserStep.agree_u` §5 + `DecodeTotalU` are unchanged **[V]** — the decode is
read-only, so `goodb` still certifies it and `hval` is what `HartRunFull` wants).

### 3.6 The trap tower: `goodmb` at `mm := ∅` is the register-WRITE engine the tree lacked

`goodb` REFUSES every `RegWrite` (`WpDecodeBridge.v:63` `| _ => false` **[V]**)
and `hval_of_goodb` demands `exec m dst = Some (x, dst)` — the SAME state
(`HartGoodb.v:219` **[V]**).  So the trap tower (which writes mstatus ×3, elp,
scause ×2, stval, sepc, cur_privilege, nextPC — `UserTrap.v:104-120`) **cannot**
go through `goodb`, and the worklist's sketch ("an `hval_of_goodb` engine over
`exec_handle_interrupt_S`", `projects/main-cycle-port.md`, "What `WpIntrInv`
actually needs") is WRONG as written.

`goodmb` is the fix and it is already built: it takes writes
(`andb (Dw r) …`, `HartMemRun.v:459`) and `hmrun_of_exec` takes `exec m s = Some
(x, s')` with `s' ≠ s` (`HartMemRun.v:601`) **[V]**.  With `mm := ∅`,
`bytes_own ∅ = emp`, `∅ ⊆ s.(mem)` and `mm_after m s ∅ = ∅` for an event-free
stretch, so:

> **`swp_hmrun_of_exec … (mm := ∅)` IS the register-writing analogue of
> `hval_of_goodb`.**  Record this in `HartMemRun.v`'s header; three other
> stretches in the tree want it (MRET's walk, the S-mode trap tower,
> `reset_elp`).

The user tower then needs exactly four `goodmb` twins mirroring
`UserTrap.exec_trap_handler_U:104` / `exec_handle_interrupt_U:246` /
`exec_exception_handler_U:258` / `exec_handle_exception_U:272`, assembled with
`goodmb_bind`/`_bind0` along the same chain and the same sub-facts.
**~250 lines** for the four.

### 3.7 What the whole engine looks like, top to bottom

```
wp_user_exec                       (UserExec, UNCHANGED)
  user_step_obligation_holds       (UserStep §3, UNCHANGED shape; WAITING arm re-proved)
    wp_user_step_active            (UserStepFull; wire_inv premise GONE)
      swp_exec_step_full           (HartStepFull, NEW: 6 arms + tick + Loop)
        u_frames_intro/elim        (UserFrames, NEW)
        swp_dispatchInterrupt_U    (WpIntrCore, NEW; wires ∀-peeled)
        swp_run_hart_active_u_*    (HartRunFull, NEW: fetch match-shaped, result-generic)
          swp_fetch_u              = swp_hmrun_of_exec ⟨exec_fetch, goodmb_fetch⟩
          hval_of_goodb (decode)   UNCHANGED
          swp_execute_u            = swp_hmrun_of_exec ⟨base/rvc_exec_total_u, goodmb twin⟩
        swp_trap_tower_u           = swp_hmrun_of_exec ⟨exec_handle_*_U, goodmb twin⟩ at mm := ∅
```

---

## 4. QUESTION 3 — WHICH EXEC FACTS STAY, AND THE `goodmb` DISCIPLINE

### 4.1 The rule that decides every case (the memory analogue of the leaf-sweep rule)

* **event-free and read-only → `goodmb_of_goodb`** (`HartMemRun.v:774` **[V]**),
  i.e. free wherever a `goodb` already exists (`CommonWalk.goodb_check_leaf_pte_leaf0:255`,
  `goodb_currentlyEnabled_Svnapot:90`, the whole decode catalogue).
* **register WRITES, no memory → `goodmb` assembled along the exec proof's own
  chain**, `mm := ∅` (`goodmb_bind`, `_bind0`, `_bindR`, `_bind0R`,
  `_try_catch`, `_liftR`, `_cer`, `_mono`, `HartMemRun.v:854-1005`).  The three
  habits from `projects/main-cycle-port.md` ("THE PAGE-TABLE PROOFS ARE
  BRIDGED") apply verbatim: `set` the left operand OUT of the goal; make its
  value existential; mind the monad level (`bindR`/`execR` inside a
  `catch_early_return`).
* **memory accesses inside owned pages → the same assembly, with the access
  node discharged by `negb (dev_addr pa) && bytes_owned mm pa n`**, both pure
  consequences of `u_mem_wf pt mm` (§4.2).
* **`vm_compute` only where the whole term is data-free** — `goodmb` answers a
  `bool` and never normalises the state, so it computes in ~0.1 s at concrete
  arguments (`HartMemRun.v` §6 **[V]**), but the user tier's arguments carry
  symbolic register and byte values, so ASSEMBLE.  Two recorded traps:
  `dom (mm_after …) = dom mm` does NOT `vm_compute` (state it as
  `bytes_owned … = true`); `exec` at a concrete state does not either.

### 4.2 The one structural change: PURE memory composers over a byte map

Today every memory/fetch composer is an Iris bupd that consumes
`gen_heap_interp σ.(mem)` **only to learn what σ.(mem) holds** — e.g.
`UserFetchPt.udata_fetch_word:50` reads the four instruction bytes out of the
authority, and `UserPtTree`/`KptTree`'s `ptree_own_path_mem` reads the PTEs.
Under the port the hart HOLDS those bytes, so the same facts are PURE.  Define,
in a new **`UserBytes.v`**:

```coq
Definition u_mem_wf (P : uptd) (t : ptree) (mm : gmap Arch.pa (bv 8)) : Prop :=
  (* the tree's slots and the data pages, as ONE map *)
  ptree_bytes t ##ₘ udata_bytes P ∧ mm = ptree_bytes t ∪ udata_bytes P ∧
  (forall a, a ∈ dom mm -> addr_is_ram a) ∧              (* ⇒ dev_addr = false *)
  (forall vpn w va, P.(ud_um) !! vpn = Some w -> u_walk_pa w va ∈ dom mm) ∧   (* udata_cov *)
  (forall path, ptree_maps t … -> read_bytes mm (u_pte_addr …) 8 = Some …) ∧  (* the slot view *)
  upt_tree_spec P.(ud_root) P.(ud_tfp) P.(ud_um) t ∧ upt_map_wf P.(ud_um).

Lemma user_pt_inv_bytes (P : uptd) :
  user_pt_inv P -∗ ∃ t mm, ⌜u_mem_wf P t mm⌝ ∗ upt_regs P ∗ pt_claims t ∗ bytes_own mm ∗
     (∀ mm', ⌜u_mem_step P t mm mm'⌝ -∗ bytes_own mm' -∗ upt_regs P -∗ pt_claims t -∗ user_pt_inv P).
```

`u_mem_step P t mm mm'` = "`dom mm' = dom mm`, the data half is arbitrary, and
the tree half differs only in leaf A/D bits".  The A/D clause is exactly what
`upt_tree_spec` already tolerates — it quantifies leaves as `pte_set_ad w a d`
(`UptTree.v:174-185` **[V]**) — so re-establishment is the pure content of the
existing ADUE absorption, not new reasoning.  The data half is unconstrained
because `udata_own`'s contents are existential.

**Then every memory composer loses its Iris wrapper and returns a pair.**  E.g.

```coq
Lemma u_fetch_pure (P : uptd) t mm rs (w va : mword 64) :
  P.(ud_um) !! svpn_of va = Some w -> uleaf_ok (InstructionFetch tt) w ->
  u_mem_wf P t mm -> <the register pins, on rs> ->
  exists (iw : mword 32) (sf : mstate),
    exec (fetch tt) (MState rs mm dev0_state) = Some (if isRVC … then F_RVC … else F_Base …, sf) /\
    goodmb Du_r Du_w (fetch tt) (MState rs mm dev0_state) mm = true /\
    <sf.(sregs) = rs or one tlb write> /\ u_mem_step P t mm sf.(mem).
```

This is `UserFetchPt.user_pt_fetch_instr:160` with `reg_interp`/`gen_heap_interp`
premises replaced by `u_mem_wf` and a `goodmb` conjunct added.  Its proof is the
SAME proof (the `phys_valid` steps become `u_mem_wf` projections) plus the
certificate assembly.

### 4.3 Per-file cost of the `goodmb` twins

| where | what needs a twin | route | est. lines |
|---|---|---|---|
| `CommonWalk.v` | `check_leaf_pte`, the Svnapot/Svadu probes, `update_and_write_pte` (decline arm) | already have `goodb` ⇒ `goodmb_of_goodb` | ~40 |
| `CommonWalk.v` | `_rec_pt_walk` ×3 levels, `add_to_TLB` | assemble: 3 PTE reads (`bytes_owned` from `u_mem_wf`) + one tlb write | ~250 |
| `PtTreeAdue.v` | `read_pte` / `write_pte_conditional` / `pmpCheck` / `pmaCheck` | assemble; the exclusive read + conditional write are ORDINARY nodes for `goodmb` (it ignores the access kind, `HartMemRun.v:78-96` **[V]**) | ~200 |
| `UserTranslate`/`UserPtTree` | `translateAddr` hit / miss / fault heads | assemble over the above | ~200 |
| `UserFetchPt.v` | `fetch`, `fetch_bytes`, the 2-halfword straddle | assemble | ~250 |
| `UserMemPt.v`, `UserMemAccess.v` | `mem_read`/`mem_write`/`translate_and_read_value`/`vmem_read_addr`/`vmem_write_addr`, aligned + LR/SC | assemble; needs §1.1's term axioms | ~500 |
| `UserMemMis.v` | the per-page misaligned split | assemble (same peel as aligned) | ~250 |
| `UserMemArms.v` (PURE, unchanged) | `execute_LOAD/STORE/LOADRES/STORECON/AMO` | one `goodmb_bind` per arm over the vmem twin | ~300 |
| `UserCsr.v`, `UserExecFacts.v` (PURE, unchanged) | the register-only execute families | `goodmb_of_goodb` off a `goodb` computed at `dstateU` where the term is data-free; ASSEMBLE where the operand index is symbolic (`goodmb_rX_bits_gpr`/`_wX_bits_gpr`, one lemma each, 32-way split) | ~350 |
| `UserTrap.v` | the four tower entry points | assemble, `mm := ∅` | ~250 |
| `UserStep.v` | `run_hart_waiting` ×3 arms, `should_inc_minstret` | assemble, tiny | ~60 |

**Total new certificate code ≈ 2 650 lines**, and it is the most parallelisable
work in the port: every twin sits BESIDE its exec lemma, takes the SAME
hypotheses, and its proof is that lemma's proof with `exec_bind_Some` replaced by
`goodmb_bind`.

**THE REGISTER-ONLY ROWS ARE DONE** (`UserCsr.v` +811, `UserExecFacts.v` +1 095,
`UserTrap.v` +475, `UserCompute.v` nil — it has no `exec_X` fact), and four
things they settled apply to every remaining row:

1. **STATE EVERY REGISTER-ONLY TWIN AT `mm := ∅`, and nothing is lost.**
   `HartMemRun.goodmb_map_mono` lifts an ∅-certificate to ANY map (only
   `dom mm` is consulted and `bytes_owned` is monotone in it), so a caller
   standing on the whole user image can use it unchanged.
2. **SAIL'S `>>`/`>>=` ARE LEFT ASSOCIATIVE, AND AN `erewrite` OF A BIND
   EQUATION WITH AN OPEN LEFT OPERAND DECOMPOSES A CHAIN SYNTACTICALLY** —
   picking `(A >> B) >> C` as the head of `((A >> B) >> C) >> D`, which is not
   what any proof has facts about, and the error is a bare "no applicable
   tactic". GIVE the head (pass the head's certificate and `exec` fact as
   ARGUMENTS, not as side goals): the match then goes through CONVERSION,
   which peels the leftmost node out of one level of nesting.  `HartMemRun`'s
   `gm_peel` / `gm_peel_r` / `gm_peel_w` do this and fall back to
   `goodmb_bind_nest_empty`; deeper than one nest (four consecutive register
   writes, `track_trap`'s callback chain) build the prefixes' facts
   inside-out and peel the top once.  This is habit 1 of
   `projects/main-cycle-port.md` and it costs a day to re-learn.
3. **AN EARLY-RETURN REGION THAT THROWS CANNOT USE `goodmb_cer` AT ALL.**
   `goodmb` refuses an `ExtraOutcome` node, so a body that early-returns has
   no certificate; the wrapper must stay ON while the chain is peeled
   (`goodmb_cer_bind_empty`, and `goodmb_cer_bind_nest_empty` where an
   `and_boolM`/`or_boolM` guard puts the throw one level in).  The walk ends
   at the thrown tail, where `catch_early_return` absorbs the throw and the
   certificate is `reflexivity`.
4. **A TACTIC-DRIVEN EXEC TRAVERSAL MIRRORS FOR FREE.**  `is_CSR_accessible`'s
   200-clause dispatch has PURE guards, so `gm_csr_step` is `csr_step` with
   the `∃ _, exec _ = Some _ ∧ _` pattern replaced by `goodmb _ _ _ _ _ = true`
   and the per-clause RESULT obligations DELETED — a certificate does not
   depend on the outcome.  The dead branches die on the same three facts.
   Expect the same for `UserTotalU`'s dispatch tables.

### 4.4 What CANNOT get a `goodmb` twin, and what to do instead

1. **`load_reservation` / `cancel_reservation`** — opaque `M` axioms; no
   certificate is even statable.  §1.1's term axioms are the answer, and they
   are *required* for soundness anyway.  (Do NOT add
   `Axiom goodmb_load_reservation` — it would paper over the stuckness.)
2. **the interrupt dispatch** (`getPendingSet`/`read_mip`/`external_interrupts_pending`)
   — reads `sig_meip`/`sig_seip`, which no frame may hold, and every certified
   read must be in the footprint.  Hand-peeled `swp` walk, §3.3.  This is the
   same wall `WpIntrCore` hit on the S side and the reason `swp_read_reg_any`
   exists.
3. **`tick_clock`** — reads `mtimecmp`/`stimecmp` and (on one branch) the wires,
   and no caller can name its post-file.  Already solved generically by
   `swp_tick_clock_any` / `swp_tick_wrap` (design §5 7b/7c); the user tier never
   sees it.
4. **anything the machine may execute at a DEVICE address.**  `goodmb` refuses
   MMIO by construction.  Sound for this tier because every user-mapped page is
   RAM — but that is now a PURE side-condition (`u_mem_wf`'s `addr_is_ram`
   clause) that must be *carried*, where today it is re-derived from `phys_ram`
   at each use.  If a future user PT could map a device page, the tier's
   totality would have to grow an MMIO arm; note it, do not build it.

---

## 5. QUESTION 4 — ORDER, PARALLELISATION, RISKS

### 5.1 FREEZE THESE SIX INTERFACES BEFORE ANY PARALLEL WORK

| # | interface | file | why first |
|---|---|---|---|
| I1 | `load_reservation_term` / `cancel_reservation_term` | `ResvAxioms.v` (new) | soundness; four files import it |
| I2 | `u_Drw` / `u_Dro` / `Du_r` / `Du_w` / `Df_u` / `u_pins` + the membership lemmas | `UserFrame.v` (new) | EVERY `goodmb` twin mentions `Du_r`/`Du_w` |
| I3 | `u_mem_wf` / `u_mem_step` / `user_pt_inv_bytes` / `ptree_bytes` | `UserBytes.v` (new) + `PtTree.v` | every memory twin's premise |
| I4 | the `⟨exec, goodmb⟩` PAIR CONVENTION: for every existing `exec_X`, a twin `goodmb_X` with the SAME binders and hypotheses, in the SAME file, immediately after | tree-wide | prevents two agents inventing two shapes |
| I5 | **DONE** — `swp_run_hart_active_full` + `_U` + the five instances (fetch obligation match-shaped, execute result-generic, redirect) | `HartRunFull.v` | the fetch and execute agents write to it; shapes in §3.4 |
| I6 | `swp_try_step_full` / `swp_exec_step_full` (6 arms) + `swp_try_step_waiting` | `HartStepFull.v` (new) | the engine agent and the tier agent meet here |

Write I1–I6 as **statements with `Admitted` bodies in one commit**, then fan out.
(The tree has no admits today; land the bodies before merging anything.)

### 5.2 WORK PACKAGES (parallel after the freeze)

* **P0 (blocking, 1 agent, ~1 day).**  I1 + I2 + I3 + the `gpr_file ⟷ hreg_frame`
  bridge.  Files: `ResvAxioms.v`, `UserFrame.v`, `UserBytes.v`, `PtTree.v`
  (+`ptree_bytes`), `UserPtTree.v` (+accessor).  **~1 200 lines.**
* **P1 (1 agent).**  `HartStepFull.v` (I6) — the six arms + the waiting rule.
  Depends only on `HartStepAny`/`HartMCycle` and the five `exec_riscv_step_*`
  facts, which are PURE and already proved.  **~600 lines.**
* **P2 — DONE.**  `HartRunFull.v` (I5) + `swp_dispatchInterrupt_U`, which
  lives in `HartRunFull.v` too (§3.3).  Closes at the five platform axioms.
* **P3 (1 agent).**  The WALK + FETCH twins: `CommonWalk.v`, `PtTreeAdue.v`,
  `UserTranslate.v`, `UserFetchPt.v`, `UserFetch.v`.  **~740 lines.**
* **P4 (2 agents, split by family).**  The DATA-ACCESS twins: `UserMemPt.v`,
  `UserMemAccess.v`, `UserMemMis.v` / then `UserMemClassify.v`,
  `UserMemClassifyAmo.v`.  **~1 500 lines.**  The second agent cannot start the
  `arm_*` conversions until P4a's `vmem_*` twins exist — sequence them, or have
  one agent do both.
* **P5 (1 agent).**  The REGISTER-ONLY execute twins: `UserCsr.v`,
  `UserExecFacts.v`, `UserCompute.v`, plus `goodmb_rX_bits_gpr`/`_wX_bits_gpr`.
  **~350 lines.**  Fully independent of P3/P4.
* **P6 (1 agent).**  The TRAP tower: `UserTrap.v`.  **~250 lines.**  Independent.
* **P7 (last, 1 agent).**  The tier proper: `UserExec.v`, `UserStep.v`,
  `UserStepFull.v`, `UserClassify.v`, `UserClassifyAsm.v`, `UserActiveClass.v`,
  `UserTotalU.v`, `UserKernelBridge.v`.  **~1 000 changed lines**; the pure case
  trees (`UserActiveClass` §1–§2, `UserTotalU`'s two 250-line `lazymatch`
  dispatch tables at `UserTotalU.v:1514,1760`) survive verbatim provided
  `base_exec_total_u` / `rvc_exec_total_u` keep their NAMES and their
  `⌜exec …⌝` conjuncts.
* **P8 (after green).**  The verified Umode tier (`WpUmodeStep.v` and friends) —
  the same bricks; and the standalone premise-removal commit
  (`minstret_inv`, `wire_inv`).

### 5.3 THE ONE DESIGN DECISION THAT COULD STILL GO EITHER WAY

`base_exec_total_u` / `rvc_exec_total_u` (`UserClassifyAsm.v:40,68`) are today
`iProp` obligations that MOVE `mstate_interp` and `gpr_file`.  After the port
there is nothing left to move — the frames and the bytes stay with the caller —
so they can become **pure `Prop`s** (exec fact + `goodmb` + post-state
characterisation).  That deletes the Iris plumbing from ~4 000 lines of
`UserMemClassify`/`UserTotalU` glue and makes the whole family checkable without
the proofmode.  **Recommended.**  The cost is that the `arm_*` lemmas'
statements change shape (not just body), so `_holds`' dispatch tables need their
`fin`/`arm_*` applications retyped — mechanical, but do it in ONE commit and
diff the tables to prove nothing else moved.  If that proves painful, the
fallback is to keep them `iProp` with `bytes_own`/frames threaded through; the
`goodmb` conjunct is the same either way.

### 5.4 THE FIVE RISKIEST POINTS, PRE-CHECKED

| # | risk | verdict |
|---|---|---|
| R1 | LR/SC opaque axioms make the machine STUCK | **[V] REAL, and it is a soundness hole, not an inconvenience.**  Fixed by §1.1 in 20 lines.  Do it first |
| R2 | Can `swp_hmrun_of_exec` be instantiated at a symbolic frame? | **[V] YES, trivially**, by `s := MState rs mm dev0_state`: `reg_agree_on` is reflexivity, `mm ⊆ s.(mem)` is `⊆`-refl, and the landing map is `s'.(mem)` because `write_bytes` preserves `dom` (`HartMemRun.write_bytes_dom:568`, `goodmb_dom:728`) |
| R3 | Does `bytes_own` match `user_pt_inv`'s ownership shape? | **[V] HALF FREE**: `udata_own` IS `bytes_own` up to the `dom` conjunct (`UserPtTree.v:150` vs `HartMemRun.v:168`); `ptree_own`'s slots are `↦ₚ₈` = 8 `↦ₚ` bytes each (`PtTree.v:931`, `RiscvPtsto.v:1339`) and need ONE new view lemma; the `pt_node_claim` ghost is not a byte and must be kept aside |
| R4 | Does the tier read a register the hart does not own? | **[V] EXACTLY TWO**: `sig_meip`, `sig_seip`, and only inside `dispatchInterrupt`.  Nothing else — no htif (gated `= None`), no device state (`goodmb` refuses MMIO and every user page is RAM), no other hart's cells |
| R5 | Does `swp_try_step_any` cover the user's outcomes? | **[V] NO** — four of six arms are `| _ => False` (`HartStepAny.v:141`).  `HartStepFull.v` is real, unavoidable work (~600 lines), and it is on the critical path |
| R6 | Do the GPRs fit in a footprint at symbolic operands? | **[V] YES via `goodmb`** (§1.3) — the trap in the durable notes is about *computing* `hfrun`, which this route never does |
| R7 | Can a user store corrupt a PTE? | **[A→V by construction**: the tree bytes and the data bytes are separately owned today, so they are disjoint; the port must EXTRACT that disjointness once into `u_mem_wf` (§4.2).  If it is ever violated, `u_mem_step`'s A/D-only clause fails and the port fails loudly rather than silently |

### 5.5 SUCCESS CRITERION

`UserExec.v` … `UserActiveClass.v` compile; `ProofUser.wp_user_exec_closed`
closes at the 5 rv64d platform axioms **plus the two reservation term axioms**
(which REPLACE the two `exec_*` reservation axioms — net axiom count unchanged);
`UserretUser.v` / `ProofUserretClosed.v` re-check with at most the two one-line
`pc_is` fixes; and a `git diff` of `UserTotalU.v`'s two dispatch tables and of
`UserActiveClass.v` §1–§2 is EMPTY.

---

## 6. FILE-BY-FILE LEDGER

| file | now | after | work |
|---|---|---|---|
| `ResvAxioms.v` (NEW) | – | ~40 | I1 term axioms + the two exec corollaries |
| `UserFrame.v` (NEW) | – | ~350 | I2 footprints, ~35 membership lemmas, `Du_gpr` |
| `UserFrames.v` (NEW) | – | ~250 | `u_frames_intro/_elim`, `gpr_file ⟷ hreg_frame` |
| `UserBytes.v` (NEW) | – | ~450 | I3 `u_mem_wf`, `u_mem_step`, the accessor, ram/disjointness extraction |
| `PtTree.v` | 1 000+ | +200 | `ptree_bytes`, `ptree_own_bytes` |
| `HartStepFull.v` (NEW) | – | ~600 | I6, the 6 arms + waiting |
| `HartRunFull.v` (NEW) | – | ~500 | I5, fetch match-shaped + result-generic execute |
| `WpIntrCore.v` | 1 000+ | +120 | `swp_dispatchInterrupt_U` |
| `HartMemRun.v` | 1 295 | +20 | header note: `mm := ∅` is the register-write engine |
| `CommonWalk.v` | 1 690 | +250 | walk twins |
| `PtTreeAdue.v` | 1 400+ | +200 | pte read/write twins |
| `UserPtTree.v` | 588 | ~700 | the accessor, pure heads |
| `UserFetchPt.v` | 647 | ~800 | pure composers + twins |
| `UserMemPt.v` / `UserMemAccess.v` / `UserMemMis.v` | 3 867 | ~4 700 | pure composers + twins |
| `UserMemClassify.v` / `UserMemClassifyAmo.v` | 6 685 | ~7 100 | arms re-shaped, Iris plumbing deleted |
| `UserTrap.v` | 567 | ~800 | tower twins; `utrap_ghost` (§6, Iris) deleted — the walker does the ghost update |
| `UserTotalU.v` | 2 006 | ~2 000 | glue re-shaped, dispatch tables UNTOUCHED |
| `UserClassify.v` / `UserClassifyAsm.v` / `UserActiveClass.v` | 1 070 | ~1 050 | `active_step_branch` becomes the `swp` branch; pure case trees untouched |
| `UserStep.v` | 774 | ~500 | WAITING engine collapses (no clock borrow) |
| `UserStepFull.v` | 308 | ~250 | wire borrow DELETED |
| `UserExec.v` | 463 | ~430 | `user_regs` +3 riders, `MipBorrow` deleted, `ucfg` comment rewritten |
| `UserKernelBridge.v` | 242 | 243 | one `pc_is` line |
| `UserBits/Csr/ExecFacts/Fetch/Mem/MemArms/Translate` | 4 547 | 4 547 + twins | **statements byte-identical** |

**Net: ~2 500 lines of new machinery, ~2 650 lines of certificates, ~1 500 lines
of re-shaped tier glue, and ~4 500 lines that do not move at all.**

---

## 7. TWO THINGS TO WRITE INTO THE NOTES WHEN THIS LANDS

1. `swp_hmrun_of_exec` at `mm := ∅` is the general **register-WRITING** transport
   (`hval_of_goodb`'s missing twin).  The worklist currently tells the next agent
   to use `hval_of_goodb` for the S-mode trap tower; that is impossible
   (`goodb` refuses writes) and the correction belongs in
   `projects/main-cycle-port.md`, "What `WpIntrInv` actually needs".
2. The durable "a footprint CANNOT run symbolic operands" trap must be qualified:
   it is about *computing* `hfrun`, not about `goodmb`, which is assembled and
   discharges `bool_decide (r ∈ D)` by proof.  The user tier puts all 31 GPRs in
   its footprint because of this.
