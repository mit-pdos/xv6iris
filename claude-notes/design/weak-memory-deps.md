# Dependency tracking in the full machine, and a machine-checked Layer 2 — design

**Status (2026-08-17): PROPOSAL by the orchestrator, requested by the user;
nothing built.  Companion to
[`weak-memory-premise-discharge.md`](weak-memory-premise-discharge.md)
(what `main_premises` are and why the current discharge story has a hole)
and [`weak-memory-m6-robustness.md`](weak-memory-m6-robustness.md) (the
Layer-1 architecture this changes).  Decision points for the user: ⚑.**

## 0. The claim, in one paragraph

Today `WeakEvCapstone.xv6_ev_weak_robust` is machine-checked
`WPs ⇒ φ ⇒ robustness` under `main_premises`, a per-bundle package about
FULL-machine traces that (i) is false for xv6 in two clauses (fixable) and
(ii) cannot be derived from the WPs by any state-predicate export, because a
full-machine trace has positions AFTER AN EARLY READ OF A PROMISE that no
promise-free run visits — and, more fundamentally, because our full machine
DROPPED PARM's dependency tracking (D-M6-5, "weaker is free for
containment"), so it admits out-of-thin-air executions in which control
flow itself is steered by promised values and NO code-discipline statement
holds over all of its behaviors.  The proposal: **restore PARM's dependency
tracking (per-register views + `vcap`) in the full machine and the
promise-free fragment**, which (a) makes the full machine literally
Promising-RISC-V per byte (tightening the containment note), (b) removes
OOTA and orders every address-/data-/control-dependent memory access after
the load it depends on BY THE MACHINE, so that the reader-side robustness
obligation shrinks to "an INDEPENDENT store after an uncovered foreign read
is fenced or covered", and (c) makes a Layer-2 transfer theorem — "an
exported promise-free state predicate Ψ implies the (relativized) premises
on every full trace" — provable along the minimal-cycle argument the M6
design sketched (D-M6-8) but never mechanized.  The end state is
`WPs ⇒ Ψ ⇒ main_premises′` machine-checked, with the PARM containment note
as the only remaining seam.

## 1. Why dependencies, precisely

RVWMO orders (ppo 9–11, and 12–13's pipeline rules) a memory access after an
earlier LOAD when its address (9), data (10) or a controlling branch/jump
(11) SYNTACTICALLY depends on that load's destination register.  PARM models
this with a VIEW PER REGISTER (`regs : Reg → Val × View`), a control view
`vcap`, and view components in the read/write pre-views.  Dropping them
made our machine WEAKER (more behaviors) — free for `hardware ⊆ model` — but
it costs Layer 2 twice:

1. **OOTA.**  `A: r=ld x; st y=r` ‖ `B: r'=ld y; st x=r'` with both stores
   promised (`WPPromise` is unconditional) and both fulfilled with the value
   read from the other's promise IS a `wp_behavior` of our machine.  With
   OOTA values a hart can jump anywhere; the code discipline that
   `main_premises` encode is simply false over the model's behaviors, so it
   can only ever be proven for a SUB-CLASS of behaviors — and the only
   honest sub-class is "RVWMO's", i.e. the machine with dependencies.
2. **The reader-side obligation is much larger than it need be.**  With
   `vcap` in every store's `view_pre`, a store control-dependent on an
   uncovered foreign read is ordered after it by EXT — the S1 inequality
   `ts_read < ts_fulfil` that `edges_split` exists to supply.  xv6's racy
   sites are ALL of that shape (`while(started==0)`: the branch depends on
   the load; `holding()`: `if(holding(lk)) panic` before the RMW), so with
   dependencies the residual obligation is only for a store INDEPENDENT of
   an uncovered foreign read — which lock discipline forbids outright.

Polarity check (Decision 1's rule): adding orderings REMOVES behaviors from
the full machine, so it owes an argument that hardware still ⊆ model.  The
argument is PARM's own theorem: with these components the machine IS
Promising-RISC-V (per byte, modulo the message-class tag which is inert),
and Promising-RISC-V ≡ axiomatic RVWMO (Pulte et al.).  The containment
note in `WeakCompose` §6(5) becomes "identical to PARM up to byte
granularity" instead of "weaker than PARM".  ⚑ We must decide how faithful
to be on the fine points (RCpc `.aq/.rl` handling, `vrel`, the exbank view,
`ChooseReal`); the rule is: copy PARM's `Local.read/fulfill/fence` and the
register-assignment rule VERBATIM (Promising.v ~800–910; the m6 worklist's
§0 has the line map), deviating only where our per-byte log forces it, and
record every deviation with its polarity.

## 2. What the machine gains (Layer 1, `WeakMem`/`WeakPromise`)

### 2.1 State
`wstate` gains three MACHINE-OWNED, `ts_oblivious`-safe components (they are
timestamps computed by the machine from labels, exactly like `w_vwNew`):
- `w_regv : gmap register nat` — the view of each register (default 0; only
  GPRs ever become nonzero, by construction of the label vocabulary);
- `w_vcap : nat` — PARM's control/address-capture view;
- `w_ldv : nat` — the post-view of the CURRENT instruction's most recent
  load (the value a later `RegWrite rd` of this instruction inherits).

### 2.2 Labels: dependency SOURCES are names, never views
`wlabel` gains an operand vocabulary
`Inductive dsrc := DReg (r : register) | DLdRes` (a GPR, or "this
instruction's load result") and:
- `LLoad aq lat base tvs (asrc : list dsrc)`,
  `LStore rl base data (asrc dsrc : list dsrc)`,
  `LRmw aq rl base tvs data (asrc dsrc : list dsrc)`;
- `LRegW (rd : register) (srcs : list dsrc)` — the destination write of an
  instruction (ALU result, load result, AMO result, `jal` link…);
- `LCtrl (srcs : list dsrc)` — a branch / indirect jump resolves;
- `LInstr` — instruction start (resets `w_ldv`; carries nothing else).
Everything else (`LSilent`, `LDev`, `LFence`) is unchanged.  `pstep` stays
LOG-BLIND and VIEW-BLIND: it emits NAMES; the machine looks the views up.
`ts_oblivious`, `pcls_obl`, `lat_free_prog`, `pdev_ok` are unaffected in
shape (the names are not timestamps).

### 2.3 Rules (PARM's, in our spelling)
With `V(srcs) := ⊔ { w_regv r | DReg r ∈ srcs } ⊔ (w_ldv if DLdRes ∈ srcs)`:
- **read** (`WPLoad`/`PFLoad`): `vaddr := V(asrc)`;
  `vpre := w_vrNew ⊔ vaddr ⊔ (aq ? …)` (PARM's exact acquire term);
  admissible `t` as today at `vpre`; post `vpost = vpre ⊔ t` (or the forward
  bank's view); updates as today PLUS `w_vcap ⊔= vaddr`, `w_ldv := vpost`.
- **write / fulfil** (`WPFulfil`/`PFStore`, and the RMW arms):
  `fulfil_vpre := w_vwNew ⊔ V(asrc) ⊔ V(dsrc) ⊔ w_vcap ⊔ (rl ? …) ⊔ (rmw ? its
  own read's post-view, as today)`; EXT `fulfil_vpre < ts`, COH as today;
  post as today PLUS `w_vcap ⊔= V(asrc)`, forward bank carries
  `V(asrc) ⊔ V(dsrc)`.
- **`LRegW rd srcs`**: `w_regv[rd] := V(srcs)`.  (Register writes with no
  dependency role — CSRs, PC, `minstret`, `nextPC`, x0 — stay `LSilent`,
  i.e. keep the machine view they had; that UNDER-approximates syntactic
  dependencies through CSRs, which is the safe polarity.)
- **`LCtrl srcs`**: `w_vcap ⊔= V(srcs)`.
- **`LInstr`**: `w_ldv := 0`.
- fences, promise arm, `LDev`: unchanged.
The promise-free fragment (`wp_pf_step`) gets the same arms fused as today.

### 2.3′ THE RULE TABLE — PARM verbatim, with our spellings and the recorded deviations (2026-08-17)

Source: `snu-sf/promising-arm`, `src/promising/Promising.v` `Module Local`
(state `mk coh vrn vwn vro vwo vcap vrel fwdbank exbank promises`, lines
~779–1000 at the tip) and `src/lib/Lang.v` (`sem_expr`: an expression's view
is the JOIN of its registers' views; `step_load` puts the read's `res` (value
+ `view_post`) into `rmap[res]`; `step_if` emits `Event.control (view of the
condition)`).  Our names: `w_coh/w_vrNew/w_vwNew/w_vrOld/w_vwOld/w_vRel/
w_fwd` = `coh/vrn/vwn/vro/vwo/vrel/fwdbank`; NEW `w_regv` = `rmap`'s views,
`w_vcap` = `vcap`, `w_ldv` = the pending `res` view of the current load.

| PARM rule | PARM formula | ours (D2) |
|---|---|---|
| `Local.read` | `view_pre = view(addr) ⊔ vrn ⊔ (ord ≥ acquire ? vrel)`; `COH: latest loc ts coh(loc)`; `LATEST: latest loc ts view_pre`; `view_post = view_pre ⊔ fwd_read_view`; `coh(loc) ⊔= view_post`; `vrn,vwn ⊔= (ord ≥ acquire_pc ? view_post)`; `vro ⊔= view_post`; **`vcap ⊔= view(addr)`**; `exbank := (loc, ts, view_post)` if `ex`; `res := (val, view_post)` | `LLoad aq lat base tvs asrc`: `vaddr := V(asrc)`; `vpre := load_vpre ws aq ⊔ vaddr` (today's `load_vpre` already carries the `vrel` term); `readable`/`read_ok` at `vpre` per byte as today; post = today's `load_post_run` PLUS `w_vcap ⊔= vaddr`, `w_ldv := vpost` (max over the bytes) |
| `Local.fulfill` (`writable`) | `view_pre = view(loc) ⊔ view(val) ⊔ vcap ⊔ vwn ⊔ (ord ≥ release_pc ? vro ⊔ vwo) ⊔ (ex ∧ riscv ? exbank.view)`; `COH: coh(loc) < ts`; `EXT: view_pre < ts`; `EX: exclusive window`; post `coh(loc) := ts`; `vwo ⊔= ts`; **`vcap ⊔= view(loc)`**; `vrel ⊔= (ord ≥ release ? ts)`; `fwd(loc) := (ts, view(loc) ⊔ view(val), ex)`; `res := (0, view ts if ex∧riscv)` | `LStore rl base data asrc dsrc` / `LRmw … asrc dsrc`: `fulfil_vpre := today's (w_vwNew ⊔ (rl ? vrOld ⊔ vwOld)) ⊔ V(asrc) ⊔ V(dsrc) ⊔ w_vcap ⊔ (rmw ? the read half's post-view)`; COH/EXT/`excl_ok` as today; post = today's `store_post_run` PLUS `w_vcap ⊔= V(asrc)`, forward bank view := `V(asrc) ⊔ V(dsrc)` |
| `Local.control` | `vcap ⊔= ctrl` (`step_if`: ctrl = view of the branch condition) | `LCtrl srcs`: `w_vcap ⊔= V(srcs)`; emitted for conditional branches (srcs = rs1, rs2) AND indirect jumps (`jalr`: srcs = rs1) — RVWMO ppo 11 names both; PARM's language has no indirect jump, so this is a strengthening WITHIN RVWMO (deviation D-3) |
| `step_assign` / `sem_expr` | `rmap[lhs] := (val, ⊔ views of the registers read)` | `LRegW rd srcs`: `w_regv[rd] := V(srcs)`, srcs = the instruction's integer source registers (from `deps_of_bits`); the load's `res` = `DLdRes` |
| `Local.dmb rr rw wr ww` | `vrn ⊔= (rr? vro) ⊔ (wr? vwo)`; `vwn ⊔= (rw? vro) ⊔ (ww? vwo)` | today's `fence_post pr pw sr sw` (rr=pr∧sr, wr=pw∧sr, rw=pr∧sw, ww=pw∧sw) — unchanged |
| `Local.isb` | `vrn ⊔= vcap` | n/a on RISC-V (`fence.i` is not `isb`; today's inert `LFence false…` stays) |
| `Local.promise` | append; views untouched | unchanged (`WPPromise` unconditional) |

Recorded deviations (each with polarity; "STRONGER" = removes behaviors and
needs the containment argument, "WEAKER" = adds behaviors, free):
- **D-1 (per byte).** All views per byte as today; a multi-byte access is
  its per-byte events; `w_ldv` = the max post-view over the bytes.
- **D-2 (fused RMW, exbank).** PARM's exclusive write joins `exbank.view`
  (= the exclusive read's `view_post`) into `view_pre`; today's fused
  `fulfil_ok (load_post_run …)` includes it ONLY when `aq`.  D2 adds the
  read half's post-view unconditionally — STRONGER than today, EQUAL to
  PARM.  PARM's SC-result register view (`res = ts` for `ex ∧ riscv`) has no
  counterpart (an AMO's `rd` is the READ's `res`, view = the read's
  `view_post`; xv6 has no `sc`) — WEAKER (free); note it in the ledger.
  **STATUS: the exbank JOIN stands; the exclusive read's own ADDRESS-VIEW
  floor does NOT — see D-2r below before reading anything here as current.**
  In particular the exclusive read is admissible at the PLAIN read floor and
  its byte fold runs there, so `rv_view` is the plain `ldv_of … 0`.
- **D-3 (`jalr` control).** As above: STRONGER than PARM's language, inside
  RVWMO ppo 11.
- **D-4 (CSR / non-GPR registers).** `w_regv` tracks GPRs only; CSR-mediated
  chains and PC are NOT dependencies (RVWMO's syntactic dependency is on
  the integer/FP source registers) — WEAKER or equal, free.  `x0` never
  gets a view.
- **D-5 (`.aq`/`.rl` orders) — AUDIT PERFORMED IN D2; OUTCOME: NO CHANGE,
  the single-bit conflation is EXACT for RISC-V.**
  PARM's `OrdR.t = pln | acquire_pc | acquire` (`src/lib/Lang.v:63`) and
  `OrdW.t = pln | release_pc | release` (`:82`) enter `Local.read` /
  `Local.fulfill` at FOUR points; D2's single `aq`/`rl` bit was checked
  against each:
  1. `read`'s `view_pre = view(addr) ⊔ vrn ⊔ ifc (ord ≥ acquire) vrel`
     (`Promising.v:841`) — the `vrel` join fires only at FULL `acquire`.
     Ours: `load_vpre ws aq = vrNew ⊔ (aq ? vRel)`, fires at `aq`.
  2. `read`'s post `vrn,vwn ⊔= ifc (ord ≥ acquire_pc) view_post`
     (`:851–852`) — fires at `acquire_pc` AND `acquire`.
     Ours: `load_post_at`'s `if aq then …`, fires at `aq`.
  3. `fulfill`'s `view_pre ⊒ ifc (ord ≥ release_pc) (vro ⊔ vwo)`
     (`:874–875`).  Ours: `fulfil_vpre ws rl`'s `(rl ? vrOld ⊔ vwOld)`.
  4. `fulfill`'s post `vrel ⊔= ifc (ord ≥ release) ts` (`:911`) — full
     `release` only.  Ours: `store_post`'s `if rl then …`.

  (1) vs (2), and (4) vs (3), are the only places where PARM's two levels
  could part company with our one bit — and they part company ONLY at
  `acquire_pc` / `release_pc`.  **PARM's language has no decoder**: `ord`
  is a program annotation and the `_pc` levels are ARM's RCpc forms
  (`LDAPR`, and the `STLR` pairing); nothing in `snu-sf/promising-arm`
  produces them for RISC-V, whose `.aq`/`.rl` are RCsc.  At
  `ord ∈ {pln, acquire}`, `OrdR.ge acquire acquire_pc = true`, so (1) and
  (2) fire together and the single bit is EXACTLY PARM-at-RISC-V; likewise
  (3)/(4) at `ord ∈ {pln, release}`.  **No semantics changed in D2, and
  none is proposed.**

  TWO RESIDUES FOUND WHILE AUDITING, both recorded rather than fixed:
  - **(D-5a) `WeakInterp.as_sync` maps `AS_acq_rcpc` to `aq = true`**, i.e.
    Sail's RCpc strength is treated as full `acquire`, which joins `vRel`
    into the pre-view where PARM's rule (1) would not: STRONGER (removes
    behaviors).  The arm is DEAD for `rv64d` (Zalasr is not in the model,
    and finding (3) of `WeakInterp`'s header records that a plain load with
    `.aq` is an `internal_error`), so it is vacuous for every proof here.
    If the model ever grows Zalasr, `load_vpre` needs a three-valued read
    order.
  - **(D-5b) `fwd_view`'s acquire arm is not PARM's.**  `WeakMem.fwd_view`
    disables forwarding when `aq` is set; `FwdItem.read_view`
    (`Promising.v:529`) disables it when
    `fwd.ex ∧ (arch = riscv ∨ ord ≥ acquire_pc)`, which **at
    `arch = riscv` reduces to `fwd.ex` alone** — the ORDER plays no role,
    and what matters is whether the BANKED STORE was the write half of an
    exclusive.  So ours is STRONGER on an acquire load that would have
    forwarded a plain store (`fwd.view < fwd.ts` by that store's own EXT,
    so forcing `t` raises the post-view) and WEAKER on any load forwarding
    an exclusive store (we record no `ex` in the bank).  `WeakMem`'s header
    prose ("PARM does the same: an acquire may not take the weaker
    forwarded view") is therefore wrong for RISC-V and is corrected in
    place.  Both directions are vacuous for xv6 (its only acquires are
    `amoswap.w.aq`, whose read half is exclusive and whose forwarding
    source would have to be its own earlier exclusive store), so D2 leaves
    the rule alone; making it faithful means adding an `ex` flag to
    `w_fwd`'s payload and dropping the `aq` test — a self-contained
    follow-up, noted here so it is not rediscovered.
- **D-7 (THE FORWARD BANK — was a genuine STRENGTHENING; FIXED 2026-08-17,
  found the same day while auditing containment).**
  **STATUS: FIXED, then D2-UPGRADED, then REVERSED — the view column is `0`
  again.  See the D-7r addendum immediately below before touching this.**
  `WeakMem.store_post` records `w_fwd[a] := (t, 0)` —
  PARM's dependency-free `FwdItem` view; D2 replaced the `0` by
  `V(asrc) ⊔ V(dsrc)` and **D-7r (2026-08-21) put it back**.
  `WeakRobustProv.lstore_post` mirrors it (`(t, [])`),
  `WeakCompose` §6(5) and `weak-memory.md` Decision 3 are corrected, and
  `WeakAxiomatic3`'s argued counterexample (b) (the forward-bank leak, §14(1))
  is DEAD as a result — its premise `cand_pub_clean` is now only a proof-side
  premise, not one any known witness forces.  No litmus verdict changed
  (`WeakLitmus`'s forward-bank witnesses run at `w_vwNew = 0`).  The original
  finding follows.
  `WeakMem.store_post` recorded `w_fwd[a] := (t, w_vwNew ws)`, so a forwarded
  read (a load reading the agent's own latest store to `a`) gets post-view
  `vpre ⊔ w_vwNew(at store time)`; PARM's `FwdItem` records
  `view_loc ⊔ view_val` (the store's ADDRESS/DATA dependency views — RVWMO
  ppo 12, "a load reading an intermediate store inherits that store's
  dependencies"), which is `bot` in a dependency-free machine.  Ours was
  LARGER, i.e. STRONGER than PARM/RVWMO: `fence rw,w; st x; ld x (fwd);
  fence r,r; ld y` forces `ld y` above the pre-fence accesses in our machine
  but not in RVWMO (`fence rw,w` orders no later LOAD, and the forwarded
  `ld x` is ordered only through the store's dependencies).  Exotic and
  vacuous for xv6's proofs (owned bytes read deterministically), but a real
  behavior-REDUCING deviation, so `WeakCompose` §6(5)'s "weaker than PARM"
  claim was wrong on this axis.  D2 replaces the recorded view by PARM's
  `V(asrc) ⊔ V(dsrc)`; if D2 is delayed, change it to `0` now (the
  dependency-free PARM value; a one-line change to `store_post` plus the
  `fwd_view` lemma family — check that no leaf DERIVES a view lower bound
  from a forwarded read; none should).
- **D-7r (THE ROUTE-B REVERSAL OF D-7's D2 UPGRADE, 2026-08-21).  The bank's
  VIEW COLUMN IS `0` AGAIN, on purpose, and the machine is deliberately
  WEAKER for it.**  `WeakMem.store_post_d` banks `(t, 0)` — PARM's
  dependency-FREE `FwdItem` — at every operand view; `vf` is a DEAD parameter
  kept only for signature stability, and `store_post_d_vf :
  store_post_d ws rl vf a t = store_post ws rl a t` is the collapse lemma the
  `_d` tower's repairs go through (`store_post_bytes_d_vf` at the byte fold,
  `WeakRobustProv.lstore_post_d_vfL` on the mirror).
  - **Why.**  Under route B the DECLARED model is RVWMO⁻ + store-deps, which
    has **no ppo rule 12**.  A dep-carrying bank therefore made the machine
    STRICTLY STRONGER than its own declared model on exactly this axis — the
    realization-direction bug pattern: a dep-banked forward raises a later
    same-byte read's `coh`/`vrOld` floor, so the machine REFUSES stale reads
    the model admits, and T1's completeness at real (dep-carrying) labels
    would then force the model to GROW rule 12, i.e. dep data in the fused
    alphabet — the big surgery.  This is the T1-D CORRECTION's channel
    (`projects/weak-memory-certification.md`), closed by weakening the machine
    rather than by growing the model.
  - **What survives.**  Every DIRECT dependency floor: the fulfil's
    `vd = srcs_view asrc ⊔ srcs_view vsrc`, the exclusive `rv_view`, and the
    `w_vcap`/`w_regv` chains (including `store_post_run_d`'s `ctrl_post`
    raise at the ADDRESS view).  Only THROUGH-FORWARD dep inheritance dies,
    and no landed kill or capstone consumed it — the audit that landed D-7r
    found the whole tree's repair set to be the mirror plus statement-level
    `(t, vf)` → `(t, 0)`, with several proofs getting SHORTER.
  - **RE-UPGRADE COUPLING — do not "fix" this back casually.**  If rule-12
    enforcement is ever wanted, the bank AND the completeness model move
    TOGETHER: re-bank `vf` in `store_post_d` *and* pay the model growth
    (rule 12 + dep-carrying labels in the conformance alphabet).  One without
    the other reopens the gap D-7r closed.
  - Nothing else moved: `store_post_run_d`'s `vdata` argument is likewise dead
    (it fed only the bank — `vaddr` is still live through the `ctrl_post`
    raise, which is why `store_post_run_d_bounded` keeps `vaddr ≤ n'`; its
    `vdata ≤ n'` premise is now VACUOUS and was deliberately left in place,
    since deleting it would touch eight call sites in `WeakPromise`,
    `WeakEvLift` and `WeakRobustBlocks` for no proof content),
    `WeakErase`'s `fwd_le` arm is now the reflexive
    case, and `WeakAxiomatic3`'s `bankdom`/`fwd_view_cases` "a consulted bank
    contributes `0`" invariants — which the dep-free tier always assumed — are
    now true of the `_d` tier too.
- **D-2r (THE ROUTE-B ALIGNMENT OF THE EXCLUSIVE READ'S ADDRESS VIEW,
  2026-08-21).  The address view LEAVES the exclusive read's admissibility
  and its byte fold; it survives in `w_vcap` and (via the fold) nowhere
  else.**  `WeakMem.exload_post_run_d` folds `load_post_bytes` at the PLAIN
  `load_vpre` and banks `rv_view := ldv_of … 0`, keeping the
  `ctrl_post (vaddr ⊔ w_tbank)` wrapper unchanged; `WPExLoad`/`PFExLoad`
  (and, for uniformity, the fused `WPRmw`/`PFRmw` read halves — they die at
  R6) ask for `read_ok`, the 0 floor, instead of
  `read_ok_d … (srcs_view … asrc)`.  `vaddr` is a parameter kept for
  signature stability, and `exload_post_run_d_ctrl :
  exload_post_run_d ws aq vaddr base ts
  = ctrl_post (exload_post_run_d ws aq 0 base ts) vaddr` is the collapse
  lemma the repairs go through (D-7r's `store_post_d_vf` pattern).
  - **Why.**  D-2 gave the exclusive read PARM's `Local.read` shape, whose
    `view_pre` joins `view(addr)` — RVWMO ppo rule 9 in its exclusive-read
    flavor.  Route B's DECLARED model is RVWMO⁻ + store-deps, which has NO
    read-targeted dependency rule, so the machine was STRICTLY STRONGER than
    its own declared model at exactly this point: the realization-direction
    bug pattern, D-7r's species.  The PAIRED exclusive read is harmless (it
    reads LATEST — `rmw_latest` + `latest_readable` admit at any floor — and
    the write half's fresh-top timestamp absorbs the fold's `coh` raise),
    but a DANGLING exload (the walker's A/D re-read race, an amocas miss;
    both real xv6 shapes, both projecting as plain loads) has no absorbing
    write: its address view leaked into its bytes' `coh` and could refuse a
    later stale re-read the model admits.  Folding at the plain `vpre`
    WEAKENS the machine (more behaviours — the containment-SAFE direction)
    and aligns it with the declared model.
  - **What survives.**  `w_vcap`: the `ctrl_post (vaddr ⊔ w_tbank)` join is
    untouched, so every W-TV consumer (the bank's consumption at the access
    node, `exload_post_run_d_vcap`, L2′'s walker kills) is unaffected — that
    was an explicit veto condition of the slice and it did not fire.  The
    reservation still exists and still banks a view; only its VALUE weakens
    to the plain fold's, which the robustness tower does not relate anyway
    (S4 leaves `rv_view` deliberately unrelated).  D-2's exbank JOIN at the
    conditional write (`fulfil_vpre ⊒ rv_view`) is unchanged.
  - **RE-UPGRADE COUPLING — do not "fix" this back casually** (the twin of
    D-7r's).  Re-admitting the address view into the exclusive read's
    admissibility and fold goes TOGETHER with growing the completeness model
    by rule 9's exclusive flavor (read-targeted dep ordering + dep-carrying
    labels in the conformance alphabet).  One without the other reopens the
    gap this closed.
  - **Where the mirrors are.**  `WeakRobustProv.lexload_post_run_d` (the
    `lstate` twin: plain fold, address leaves in `lctrl_post` only) with
    `lrel_lexload_post_run_d` / `lexload_post_run_d_leaf`;
    `WeakRobustGraph.lb_rasrc` — the READ-FLOOR operand list (a plain load's
    `asrc`, `[]` for the exclusives and the fused rmw), which is what
    `rd_leaves`/`rd_floor`/`WeakRobustSim.read_ok_pf` now use.  `lb_asrc` is
    unchanged: it is still the label's real address operand list, consumed
    by the store side's dependency edges and by `w_vcap`.
  - Premises that DIED with the move (the alignment evidence):
    `WeakErase.exload_post_run_d_er` lost its `vae ≤ vai` premise outright
    (the two sides now erase at unrelated address views), the tower's
    `read_latest_read_ok_d`/`read_ok_d_app` uses at exclusive reads became
    the shorter `read_latest_read_ok`/`read_ok_app`, and the bridge's
    `srcs_view_nil read_ok_d_0` peel at the rmw arm is gone.
- **D-6 (the disk agent).** `virtio_prog`'s events carry empty `srcs`; its
  ordering is aq/fence-based — WEAKER than a hart with the same accesses
  (free), and exact for what the driver relies on.

### 2.3'' D2 LANDED (2026-08-17) — the final definitions

Everything in §2.3'/§2.3 is built.  The shapes that differ from the plan
above, and why:

**State** (`WeakMem.wstate`, three appended fields).
```coq
Notation wreg := nat (only parsing).            (* NOT [register]: [Riscv.rv64d_types]
                                                   exports its own [register] *)
Inductive dsrc := DReg (r : wreg) | DLdRes.
  w_regv  : gmap wreg nat;   w_vcap : nat;   w_ldv : nat;
Definition regv ws r := default 0 (w_regv ws !! r).
Definition dsrc_view ws x := match x with DReg r => regv ws r | DLdRes => w_ldv ws end.
Definition srcs_view ws srcs := foldr (λ x v, Nat.max (dsrc_view ws x) v) 0 srcs.
```
`srcs_view ws [] = 0` HOLDS BY CONVERSION, and every `_d` step function puts
its new argument FIRST inside a `Nat.max`, so `foo_d ws … 0 … ≡ foo ws …`
definitionally.  That is what makes the D2 event language (all operand lists
empty) reuse the dependency-free vocabulary without a single rewrite in the
byte-level lemmas.

**`ws_le` — FINDING, correcting the stage brief.**  Only `w_vcap` joins the
order.  `w_ldv` is reset by `instr_post`, as expected; but `w_regv` is not
monotone either, and not merely unprovably so — it is REFUTED: `regw_post`
is PARM's `step_assign`, an OVERWRITE, so `r1 := ld x; r1 := 0` lowers
`regv _ r1` from the load's post-view to `0`.  A pointwise-`≤` conjunct for
`w_regv` would be false of the machine.  `ws_bounded` takes all three (a
reset or a smaller overwrite still stores real timestamps).
`WeakViewMono`'s monotone-ghost prototype gains a seventh `mono_nat` for
`w_vcap` and nothing for the other two.

**The `_d` layering.**  The address view enters a load ONLY through
`load_vpre_d ws aq vaddr := Nat.max vaddr (load_vpre ws aq)` and through
`w_vcap`, which the RUN-level wrapper raises once:
```coq
load_post_run_d ws aq vaddr base ts := ctrl_post (load_post_bytes_d ws aq vaddr …) vaddr
store_post_run_d ws rl va vd base n t :=
  ctrl_post (store_post_bytes_d ws rl (Nat.max va vd) … t) va
```
Hoisting `ctrl_post` out of the per-byte function is what keeps EVERY
existing per-byte fold lemma (all of which quantify over an arbitrary
`vpre`) usable verbatim; the price is that `foo_run_d … 0 … = foo_run …`
is propositional (`ctrl_post_0`, a record eta) rather than definitional.
`store_post_d` takes ONE banked-view parameter `vf` (= `V(asrc) ⊔ V(dsrc)`,
closing D-7) because the bank entry is written per byte.
`ldv_of ws aq vaddr base ts := w_ldv (load_post_run_d (ws_ldv0 ws) aq vaddr base ts)`
is the RMW's exbank view (D-2): computed from a ZEROED `w_ldv` so that it is
exactly this access's `view_post` and not a join with a previous load's.
The EXCLUSIVE read (`exload_post_run_d`) is the one exception to the first
sentence of this paragraph: since D-2r its address view enters `w_vcap`
ONLY — its byte fold runs at the plain `load_vpre` and its reservation banks
`ldv_of … 0`.

**Labels.**  `LLoad aq lat base tvs asrc`, `LStore rl base data asrc vsrc`,
`LRmw aq rl base tvs data asrc vsrc`, and `LRegW rd srcs | LCtrl srcs |
LInstr` appended AFTER `LDev` (a trailing constructor leaves every existing
bulleted script's arm ORDER intact — the same argument that put `LDev`
last).  The design's `dsrc` operand field is spelled `vsrc` because `dsrc`
is the type of its elements.

**`fulfil_vpre` gains `w_vcap` IN THE DEFINITION** (it is state, not label)
and the label half arrives as `fulfil_vpre_d ws rl vd := Nat.max vd
(fulfil_vpre ws rl)`.  Nothing downstream changed shape: every consumer of
`fulfil_vpre _ _ < ts` goes through `fulfil_vpre_bounded`, which still holds
because `ws_bounded` bounds `w_vcap`.

### 2.3''' D2 LANDED — WHAT THE REPLAY NEEDED, AND THE RESIDUES

**The replay extended with NO new hypothesis.**  `WeakRobustProv`'s leaf
mirror `lstate` gained the three components (`l_regv : gmap wreg (list nat)`,
`l_vcap`, `l_ldv`), `lrel` three appended conjuncts, `lstate_leaf` three
appended disjuncts, and the mirrored step functions `lregw_post`/`lctrl_post`/
`linstr_post` (+ `lstore_post_d`, `lload_post_bytes_d`, the two `_run_d`).
The one genuinely new ingredient is
```coq
Lemma lrel_srcs_view σ S w srcs : lrel σ S w → srcs_view w srcs = lval σ (lsrcs_view S srcs).
```
— a label's operand list is a list of NAMES, so its view on the `wstate` side
is a join of register views and its leaf list on the mirror side is their
concatenation, and `lrel`'s two new pointwise conjuncts identify them one
register at a time.  Everything else is three more folds, exactly as §3
predicted.

**`aev_ts_occurs` is UNCHANGED, and that is a theorem, not luck.**  The new
components add no NEW leaf to the state: `lsrcs_view_leaf` says every leaf of
an operand view is already a leaf of the same `lstate` (register views are
populated only from a load's post-view, which is already a leaf).  So
`laevs_leaves_occur` — "every leaf is a timestamp some event of the trace read
or fulfilled", the well-definedness the E edges need — survives verbatim.

**The read crux gained the operand view on BOTH sides.**
`WeakRobustOrd.rd_leaves` now prefixes `lsrcs_view (pre_lstate TS r) (lb_asrc l)`
to the floor's leaf list, `rd_floor_ws` reads
`Nat.max (load_vpre_d … (srcs_view … (lb_asrc l))) (coh …)`, and
`WeakRobustSim.read_ok_pf` produces `read_ok_d` at the REPLAYED state's own
operand view.  The `lval_lt`/`pi_lt_of_tc` argument is unchanged: the extra
leaves are leaves of the same `pre_lstate`, so `pre_lstate_leaf_occurs` covers
them and the E edges they induce are ordinary E edges (`gE_ts_lt` is proved
from membership in `rd_leaves` plus `lval_ge`, both of which still apply).

**S1 got easier, as predicted.**  `WeakRobustAcyc.fulfil_vext` is now the
DEPENDENCY-CARRYING pre-view (`fulfil_vpre_d` at the label's `V(asrc) ⊔
V(dsrc)`, plus `ldv_of` at an rmw).  `fcov`'s obligation is `ts ≤ v`, so a
BIGGER `v` makes the per-edge premise `edge_ok_f` strictly WEAKER — the
direction §3's "S1 gets EASIER (EXT is bigger)" names, and the reason the
dependency track pays at Layer 2.

**THE ONE RESIDUE: the axiomatic projection is restricted to the
dependency-free fragment.**  `WeakPromise.lb_depfree` (all operand lists `[]`,
no `LRegW`/`LCtrl`/`LInstr`) is a new premise of `WeakPromiseBridge`'s part
(D) — `wp_pf_step_mstep`, `bridge_step`, and (as `pstep_depfree`)
`bridge_run` / `wp_pf_bridge` / `wp_pf_bridge_log`.  The reason is exact:
`WeakAxiomatic.mstep` steps its `mstate` with the DEPENDENCY-FREE
`load_post_run`/`store_post_run`, so a machine step that raises a view through
an operand list has no `mstep` image with an EQUAL post-state, and
`cfg_match` is an equality.  Closing the gap means giving the axiomatic side
RVWMO's ppo 9–11 — §3's "`WeakAxiomatic*` gains ppo 9–11", deliberately not
done in D2.  **The residue is VACUOUS for every instance in this tree**: the
event language and the archived `sail_step` both emit only operand-free
labels (`WeakEvInst.pstep_ev_depfree`, `WeakSailLTS2.sail_step_ni_depfree`),
and no consumer of the projection exists outside `WeakPromiseBridge` itself.
The REVERSE direction (axiomatic ⇒ machine, `mstep_wp_pf_step` /
`exec_wf_pf_run`) is unchanged: `unproj_lbl` emits empty operand lists.

**Two smaller premise additions, both discharged at every use.**
`WeakEvCapstone.wp_pf_step_inv` takes `lb_depfree l` (its `pf_ok` pins the
operand lists so that `pf_ok_hart` stays a conversion); the one call site
discharges it with `WeakEvInst.pstep_ev_depfree`.
`WeakRobustBlocks.lts_enabled`'s `le_load`/`le_rmw` quantify over the operand
lists (the completion re-runs a block with retimed reads, and the operands are
part of the label it must re-emit).

**Capstone statements are BYTE-IDENTICAL to HEAD** — `WeakRobustMain.robust_main`,
`WeakRobustMain.main_premises`, `WeakCompose.xv6_weak_robust`,
`WeakComposeLang.xv6_weak_robust_lifted` / `xv6_weak_robust_adequate`,
`WeakEvCapstone.xv6_ev_weak_robust` — and `Print Assumptions` is unchanged:
`robust_main` and `xv6_weak_robust` closed, the three Sail-facing capstones on
the five `rv64d` axioms.

### 2.4 Where the operand names come from — the ONE model change (LANDED 2026-08-17: `-D SYMBOLIC`)

**LANDED**: the model is regenerated with `-D SYMBOLIC` (the Sail library's
own flag for wiring the announcements to the concurrency interface — no
fork surgery), so `riscv_step` now emits `Interface.InstrAnnounce opcode`
after every fetch and `Interface.BranchAnnounce` at every PC redirect.  Cost
measured: 12 one-line proof fixes (bind-spine walks) + one node count in the
spike + a `mark_register` no-op stub; the whole tree green, capstone still
on the 5 axioms.  Original analysis follows.
RVWMO's syntactic dependency is defined on the ISA ENCODING (which register
fields an instruction reads/writes), not on the Sail node stream.  The
node stream shows `RegRead`/`RegWrite`/`MemRead` but not WHICH register a
memory address was computed from (Sail's pure code between nodes is
opaque), and over-approximating ("all registers read so far") is the WRONG
polarity.  So the program step must see the instruction bits:
- **The generated model's `sail_instr_announce` is a pure stub**
  (`rv64d.v:6798`, `:= tt`), called at both fetch shapes (`:43211` RVC,
  `:43253` base).  Change the FORK's Sail source so it emits the
  concurrency interface's `InstrAnnounce` outcome (which every interpreter
  in this tree already treats as a silent node: `RiscvLang.run:171`,
  `WeakInterp.wrun/wexec`, `WeakCert.exec_eff`, `WeakEvLang.emonad_step:377`,
  `esil_node`), regenerate `rv64d.v`, rebuild.  Cost: a full rebuild plus
  the spike files' hard-coded node counts (`WeakEvStarted.ev_len1` 107 →
  108); the SC tree is unaffected (silent arm).
- The event language's hart expression records the announced bits
  (`Sail gen c m fn (ib : option (mword 32))`), and `pstep_ev` computes the
  labels' `srcs` with a small PURE operand decoder `deps_of_bits :
  mword 32 → op_roles` over the RISC-V formats xv6 uses (R/I/S/B/U/J, the
  AMO/LR/SC forms, the C-extension forms), returning "no dependency" for
  anything else (safe under-approximation).  This is the RVWMO definition
  itself (integer source/destination fields), independent of Sail's decode.
- Fallback if the fork change is refused ⚑: identify the fetch as the RAM
  read whose value the decode consumes — not syntactically available; or
  key the deps on the pc through the image (breaks the language's
  genericity).  Neither is clean; the announce node is the intended
  interface and I recommend it.

### 2.5 The event language and the instance
`WeakEvLang`: `RegWrite` arms emit `LRegW`/stay silent per `deps_of_bits ib`
and the register name; branch/jalr resolution emits `LCtrl` (attach it to
the instruction's `RegWrite nextPC`/`PC` node — decide at build time; the
sources' views are fixed for the whole instruction, so any node after the
announce and before the store is sound); the memory arms carry `asrc`/`dsrc`;
`hart_ws` views extend.  `WeakEvInst`/`WeakEvPf`/`WeakEvCapstone` re-land
mechanically (the factorization is arm-for-arm; the new labels are still
"program × memory").  `weak_state_interp`'s `ws_bounded` gains the new
components; φ is unchanged (its floors are `coh`).  The disk agent's
program (`virtio_prog`) needs no operand info: it is not an ISA program;
its labels carry empty `srcs` (its ordering is aq/fence-based, exactly as
today).

### 2.6 D3-1 LANDED (2026-08-18) — `wgib`, `deps_of_bits`, and the
   machine-checked fact that the ANNOUNCE IS INVISIBLE TO THE WP TIER

D3 is staged in two: **D3-1** (this block) puts the instruction bits where
the instance can decode them and proves that doing so moves NO WP statement;
**D3-2** (§2.7) turns the decoded roles into operand lists on the labels.
D3-1 is the half that is *supposed* to be free, and it is: the acceptance
test passes for every listed lemma with byte-identical statements.

**`WeakDeps.v` — the decoder (NEW FILE, ~560 lines, self-contained).**
`deps_of_bits : mword 32 → op_roles` with
`op_roles = ORnone | ORload rd rs1 | ORstore rs1 rs2 | ORamo rd rs1 rs2 |
ORbranch rs1 rs2 | ORjalr rd rs1 | ORjal rd | ORalu rd srcs` over register
NUMBERS, and four total projections `deps_ctrl` (ppo 11), `deps_asrc`
(ppo 9), `deps_vsrc` (ppo 10), `deps_rd` (PARM's `step_assign`) that turn a
role into `list dsrc` / `option (wreg * list dsrc)`.  `x0` is dropped by
`wreg_of_num` — once, so every projection inherits the rule.  Coverage:
base RV64I (R/I/S/B/U/J), M (they are `OP`/`OP-32`), A (`lr`, `sc`, the
AMOs), Zicsr (→ `ORnone`, D-4), and the C extension quadrants 0/1/2 (the
whole list the stage brief names).  Anything unrecognised → `ORnone`, the
safe under-approximation.  **69 `vm_compute` tests** are recorded as
`Example`s over real `rv64` encodings (including `c.sw a4,0(a5) = 0xc398`,
the `started` publisher's own store, and `amoswap.w.aq`), so a regression in
the bit surgery cannot pass the build.

Decoder deviations recorded in the file header: **DEC-1** `c.jal` is
RV32-only (on `rv64d`, `op=01, funct3=001` is `c.addiw`, and that is what
the decoder returns); **DEC-2** an AMO's `rd` inherits the READ half's view
(`[DLdRes]`) where PARM gives `sc`'s `rd` the exclusive write's timestamp —
smaller, hence WEAKER, free; **DEC-3** `lui`/`auipc`/`jal`/`jalr` have an
EMPTY source list but still emit a destination, because `step_assign`
OVERWRITES `rd`'s view and dropping the write would leave a stale (larger)
view — the write is the point.

**`wgstate` gains ONE field, `wgib : CPU → option (mword 32)`.**  Not the
register file (it is not a register), not the expression (every WP statement
mentions the expression, and the acceptance test is that no WP statement
moves).  The `InstrAnnounce` arm of `WeakEvLang.emonad_step` sets it
(`ewg_ib σ c (Some (ib_of_bvn ob))`, zero-extending the announced `bvn`,
which is lossless because an RVC halfword has `bits[1:0] ≠ 0b11`); the
boundary arm (`Ret tt` → `riscv_step tick`) clears it.  `BranchAnnounce`
stays silent, deliberately: it fires only on the TAKEN arm of a redirect,
whereas RVWMO ppo 11 and PARM's `step_if` order after a branch whether or
not it is taken, so the control view must be raised at the ANNOUNCE (D3-2).

**THE INVISIBILITY, machine-checked.**  `WeakGhost.weak_state_interp` is
UNCHANGED and mentions `wgregs/wgimg/wglog/wgws/wgdev/wggen/wgpow` and
nothing else, so `WeakEvLift.weak_state_interp_ib :
weak_state_interp (ewg_ib σ c v) = weak_state_interp σ` **holds by
`reflexivity`** — a conversion, not a rewrite.  Consequences, all built:

- `WeakEvLift.esil_node` keeps the announce arm SILENT (the reflective
  cursor does not move), so NO `vm_cast` node count moves anywhere;
- the two-way disjunction `esil_node_ecycle`/`_inv` used to return became
  the named three-way `esil_sigma σ c rs' σ' := σ' = ewg_reg σ c rs' ∨
  (rs' = wgregs σ c ∧ ∃ v, σ' = ewg_ib σ c v) ∨ (rs' = wgregs σ c ∧ σ' = σ)`
  — the ONLY statement in the WP tier that D3-1 moves, and it is an internal
  bridge lemma, not a rule;
- `ewp_ecycle`, `ewp_eloop`, `ewp_ev_ret`, `ewp_ev_sil_node`,
  `ewp_ev_sil_rtc`, `ewp_ev_batch`, every `ewp_ev_seq_*`, every RAM-event
  rule, `WeakEvFunnel.ewp_ev_sil_node2`/`ewp_ev_walk`, `WeakEvExecEff`'s
  `epure`/`erun` rules and EVERY leaf: **statements byte-identical**, and the
  announce arm of each proof closes with the same proof term as the
  σ-identity arm.

**The instance.**  `WeakEvPf.pexv6.PHart` gains `ib : oib32`, fed from
`wgib σ c` by `ehart_ag` exactly as `rs` is fed from `wgregs σ c`;
`WeakEvInst.pnode_step`/`pstep_node`/`pstep_plic`/`pstep_hart` gain an `ib`
INPUT and an `oib : option oib32` OUTPUT (the `ors` idiom: `None` = "this
node does not move them", which is what keeps `elab_apply_silent` & co.
record eta-equalities and keeps FUNCTIONAL EXTENSIONALITY out of the
development — a `<[c := wgib σ c]> (wgib σ) = wgib σ` would have needed it).
`elab_apply` gains the `oib` slot and one new shape lemma,
`elab_apply_ib σ c k v : elab_apply σ c LSilent k None (Some v) (wgdev σ) =
ewg_ib σ c v`.  `WeakEvPf.elabel_ok` is UNCHANGED (it constrains `wglog σ'`
and `wgws σ' c`, and the announce moves neither); `EPFBoundary`'s successor
state becomes `ewg_ib σ c None`.

**The capstone's premise ledger is UNCHANGED** — no `wgib σ0 c = None`
fresh-era fact was needed, because `eps_init σ` reads the hart's bits off σ
(`PHart c (Ret tt) (wgregs σ c) None (wgib σ c)`) exactly as it reads the
register file, so `ecfg_of_init` still needs only `wglog σ = []` and
`∀ c, wgws σ c = ws_init`.  `xv6_ev_weak_robust` and `robust_main` are
byte-identical to `e1b67ace`; `Print Assumptions` unchanged (five `rv64d`
axioms / closed); `lemma_diff --ref e1b67ace` CLEAN.

### 2.7 D3-2 LANDED (2026-08-18) — THE OPERAND LISTS, and THE ANSWER TO
   "do per-register views leak into WP-level reasoning?"

**THE ANSWER, in one line: yes, but at exactly ONE altitude — the batched
SILENT-NODE rule — and it does NOT reach the leaf statements.**  Nine of the
ten lemmas the stage brief names re-check BYTE-IDENTICAL; the tenth
(`WeakEvExecEff.ewp_ev_lui_tail`) changes, and the reason is a theorem, not
an accident.

#### What the language emits

| node | label | view effect |
|---|---|---|
| `InstrAnnounce ob` | `LInstr` | `instr_post` (`w_ldv := 0`, PARM's `res` bank) **and** `wgib c := Some (ib_of_bvn ob)` |
| `RegWrite r` with `r` = the instruction's architectural `rd` | `LRegW rd srcs` | `regw_post` — PARM's `step_assign`, an OVERWRITE |
| `RegWrite nextPC` | `LCtrl (deps_ctrl role)` | `ctrl_post` — PARM's `step_if` |
| every other `RegWrite` (CSRs, `PC`, `minstret`, a non-`rd` GPR) | `LSilent` | none (D-4) |
| RAM `MemWrite` | `LStore rl base data (deps_asrc role) (deps_vsrc role)` | `store_post_run_d` |
| fused RMW | `LRmw aq rl base tvs data (deps_asrc) (deps_vsrc)` | `store_post_run_d ∘ load_post_run_d` |
| plain RAM `MemRead` | `LLoad aq false base tvs []` | `load_post_run` — **D-8** |
| `BranchAnnounce`, fences, MMIO, the disk | unchanged | unchanged |

The classification is `WeakEvLang.erw_of : op_roles → register → erw_kind`,
the JOIN of `WeakDeps.deps_rd` (which architectural register the instruction
writes) with `ereg_gpr_num` (which Sail register the node targets:
`x1..x31` are `num_of_register_bitvector_64` `16..46`, and the model has no
`x0` register at all, which is why `x0` can never be a destination).  Six
`vm_compute` `Example`s in `WeakEvLang` pin it down NON-VACUOUSLY —
`lw a5,0(a5)` gives `ERWreg 15 [DLdRes]` at `x15` and `ERWnone` at `x14` and
at `mstatus`; `beq a5,zero` gives `ERWctrl [DReg 15]` at `nextPC` and
`addi` gives `ERWctrl []` there.

**DEVIATION D-9 (new): the control view is raised at `RegWrite nextPC`, not
at the announce.**  The brief asked for `LInstr (ctrl : list dsrc)` — a
Layer-1 label change, which would have re-opened `WeakPromise`, the bridge,
the replay and the whole robustness tower.  It is unnecessary: D2's
`LCtrl srcs` is exactly PARM's `Local.control`, and `riscv_step`'s decode
preamble writes `nextPC` UNCONDITIONALLY and BEFORE `execute` — on the taken
and the not-taken arm of every branch, and before every memory access of the
instruction.  So `LCtrl` at that node is PARM's `step_if` position exactly,
and for a non-branch instruction `deps_ctrl` is `[]`, making the arm a no-op.
**The D2 label vocabulary was already right; nothing in Layer 1 moved.**

**DEVIATION D-8 (as briefed): a plain load carries NO address sources
ON ITS LABEL — but since F5′ (2026-08-22) its RESULT REGISTER names them.**
`WeakDeps.deps_addr` is the one definition of "the address sources of a
memory role"; `deps_asrc` (the ppo-9 operand list on the label) masks the
load arm off, exactly as below, and `deps_rd`'s `ORload` arm uses it raw, so
the emission is `LRegW rd (DLdRes :: deps_addr role)` (decoder deviation
DEC-4).  Rules 9 and 10 composed are RVWMO-honest, the machine's
`read_ok_d` vaddr floor stays untripped, and the only effect downstream is a
HIGHER dependency view / one more `row_deps` edge.  The rest of D-8:  A
load's data read and the page walker's PTE read are indistinguishable at the
node (both `AK_explicit` plain, `va = None`; the model emits no
`TranslationStart`/`TranslationEnd`), so attaching `rs1` to a read would
attach it to a PTE read too — a STRENGTHENING beyond RVWMO's syntactic
dependencies, i.e. the wrong polarity.  ppo 9 is therefore modelled for
STORES and the fused RMW (whose nodes are unambiguous) and not for loads.
Upgrade path: make the fork emit `sail_translation_start/end`, or give the
hart a "walking" phase; either makes the read arms separable and D-8 dies.
`WeakPromise.lb_ldepfree` is the pin that survives, and it is the only
premise the capstone's uniform-shape inversion still needs.

#### THE ACCEPTANCE TEST — the table

| lemma | outcome |
|---|---|
| `WeakEvStarted.ewp_ev_started_set` | **UNCHANGED** (proof only) |
| `WeakEvStarted.ewp_ev_started_load` | **UNCHANGED** (proof only) |
| `WeakEvStarted.ewp_ev_started_fence` | **UNCHANGED** (proof only) |
| `WeakEvStarted.ewp_ev_started_wait_seq` | **UNCHANGED** (not even the proof) |
| `WeakEvStarted.ewp_ev_started_set_at_main` | **UNCHANGED**, and NO `vm_cast` node count moved |
| `WeakEvFunnel.ewp_lui_leaf_ev` | **UNCHANGED** (proof only) |
| `WeakEvWire.ewp_plic` | **UNCHANGED** (not even the proof) |
| `WeakEvDisk.*` | **UNCHANGED** — the file has an EMPTY diff (D-6) |
| `WeakEvExecEff.ewp_ev_lui_tail` | **CHANGED**: gains `hart_ws c ws` in and `∀ ws', ⌜ws_depmove ws ws'⌝ -∗ hart_ws c ws'` out |

**WHY THE LEAVES SURVIVE.**  They already speak in the
`∀ ws', ⌜ws_le ws ws'⌝ -∗ hart_ws c ws'` idiom — the shape the M1c leaf
discipline settled on long before D3 — so a stretch that moves the view
monotonically is invisible to them.  What the batched rule hands back is not
`ws_le` but the stronger `WeakMem.ws_depmove`: **every ordering component
(`coh`, the four frontiers, `w_vRel`, the forward bank, `w_pub`, `w_relp`) is
UNCHANGED and only `w_vcap` rises.**  That is what lets
`ewp_ev_started_set` still read `w_relp = true` off its moved view (a fact
`ws_le` does NOT carry — `w_relp` toggles and is deliberately outside it) and
`ewp_ev_started_load` still read its `coh` payment.  `ws_depmove` is the
D3 contribution to the leaf-facing vocabulary, and it is why the leak is
one level deep instead of all the way down.

**WHY `ewp_ev_lui_tail` CANNOT SURVIVE — the finding.**  `WeakEvExecEff.epure`
means "this stretch has NO MEMORY EFFECT": no RAM access, no MMIO, no
barrier.  Under D3 that is no longer the same as "no effect on the hart's
weak state", because PARM's `step_assign` fires at the architectural
destination register — and `lui` WRITES ITS DESTINATION REGISTER.  A
register-only bridge is therefore a weak-memory event now, and since
`hart_ws` is a `ghost_var` at fraction ½ (`WeakGhost`, §3c), the rule
*cannot* move the authority without the client's half.  The whole
`epure`/`erun` family (`ewp_ev_epure`, `ewp_ev_exec_eff_pure`,
`ewp_ev_exec_eff_cert`, `ewp_ev_lui_tail`) gains the two arguments.  THE M4
BRIDGE'S NOTION OF "PURE" IS WHAT D3 BREAKS, and there is no way to restore
it short of moving `w_regv` out of the leaf-pinned `wstate` — which would
mean changing `WeakGhost.weak_state_interp`, explicitly out of scope.

#### The other WP-tier statements that moved (none is a leaf)

- `WeakEvLift.ewp_ev_sil_node` / `ewp_ev_sil_rtc` / `ewp_ev_batch` and the
  five `ewp_ev_seq_*` combinators — the leak itself: they own `hart_ws` and
  return `ws_depmove`;
- `WeakEvLift.ewp_ev_store` and `ewp_ev_seq_store` — their post-view is
  `store_post_run_d ws rl va vd …` with `va`/`vd` UNIVERSALLY QUANTIFIED,
  because the operand views are computed from `wgib`, which the client
  cannot see.  This is PARM's `FwdItem` view (deviation D-7's fix landing
  for real).  `ewp_ev_rmw` keeps its statement because its views hide inside
  `ermw_ok`/`ermw_ws`, which are already σ-parameterised;
- `WeakEvFunnel.ewp_ev_node2` / `ewp_ev_walk` / `ewp_ev_one_fetch` /
  `ewp_instr_pure` and `WeakEvWire.ewp_ewrun_nil` / `ewp_ewrun_fetch` /
  `ewp_instr` — the same threading, with the fetch-crossing forms weakened
  from a NAMED post-view to `∀ ws', ⌜ws_le ws ws'⌝` (which is all their
  clients ever used).

#### Layer 1 and the machine

`WeakMem` gains `ws_depmove` (+ reflexivity, transitivity, `_coh`, `_relp`,
`_le`, and the three `*_post_depmove` instances) and
`coh_store_post_run_d_moved` / `flr_store_post_run_d` land in `WeakEvLift` /
`WeakStore`.  `WeakEvCapstone.pf_ok`/`pf_ws` drop the store/RMW pins and use
`read_ok_d`/`store_post_run_d`/`load_post_run_d`; `wp_pf_step_inv`'s premise
weakens from `lb_depfree` to `lb_ldepfree`; `elab_apply_elabel_ok` LOSES its
`lb_depfree` premise outright, because the three dependency-only labels now
have real `elabel_ok` images.  `xv6_ev_weak_robust`, `robust_main` and
`xv6_weak_robust` are BYTE-IDENTICAL and `Print Assumptions` is unchanged
(five `rv64d` axioms / closed / closed).

**`lemma_diff --ref e1b67ace` reports exactly five GONE lemmas**, all
intended and all in `WeakEvInst`: `pnode_step_depfree`,
`pstep_node_depfree`, `pstep_plic_depfree`, `pstep_hart_depfree`,
`pstep_ev_depfree`.  They are FALSE now — that is the point of the stage —
and each is replaced by its `_ldepfree` twin (D-8's surviving pin).  The
DISK keeps the full `lb_depfree` (`pstep_disk_depfree`, D-6).

#### What D3-2 does NOT do

`WeakPromiseBridge`'s axiomatic projection (D2's one residue) is still
restricted to `lb_depfree`, and the event instance no longer satisfies it —
so the residue is no longer even vacuously discharged at this instance.  It
was never consumed outside `WeakPromiseBridge`, and closing it is §3's
"`WeakAxiomatic*` gains ppo 9–11".  Nothing else in the tree changes.

## 3. Layer-1 proof impact (what re-lands, what is new)

- **W1 (machine) / front-loading (`WeakPromiseFact`)**: `wp_swap` and the
  factorization commute state steps past promises; the new components are
  computed from labels and the frozen log exactly like `w_vwNew`, so the
  commutation arguments are unchanged in shape.
- **W2 replay (`WeakRobustProv`/`WeakRobustSim`)**: the view-provenance
  theory ("every view component is a join of processed events'
  timestamps, transported by π") extends to `w_regv`/`w_vcap`/`w_ldv` — the
  same lemma family, three more folds.  EXT at a replayed fulfil now has
  MORE conjuncts (`V(asrc) ⊔ V(dsrc) ⊔ vcap`), each a transported join —
  the crux is the same monotonicity argument.  This is the largest
  mechanical item (~the W2 rework of 2026-08-11/12, but with the invariant
  shape known in advance).
- **W2a acyclicity (`WeakRobustAcyc*`)**: S1 gets EASIER (EXT is bigger);
  the milestone measure argument is unchanged.  This is where the
  dependency ordering pays: cross edges into control-/data-dependent
  fulfils need NO premise.
- **W3/W4/W5, retag, capstones**: labels carry no classes → retag
  untouched; `WeakAxiomatic*` (promise-free ⊆ axiomatic) gains ppo 9–11 —
  a strengthening of the machine-checked half of the containment note.
- **Archive** (`WeakSailLTS*`, `WeakCompose*`): their `pstep` never emits
  the new labels; matches gain arms.

## 4. Layer 2: the exported predicate Ψ and the transfer theorem

### 4.1 Ψ — machine-syntactic, adequacy-exportable (D-M6-6 pattern)
Two more INERT per-agent components, read by no rule:
- `w_rdw : nat` — the READ WATERMARK: the max timestamp of a plain (non-aq)
  read of a message NOT covered by the reader's `w_vwNew` at the time
  (`t > w_vwNew`), since the last `pr∧sw` fence (which resets it to 0);
- the per-byte OWNERSHIP MAP `wbo : Z → option agent` in the state
  interpretation (the M6 W3 "ownership reflection", budgeted there and
  never built): owner = the hart holding `↦w{1}`/the lock-derived fragment
  for the byte, transferred by the release/acquire leaves.
`Ψ σ` := (i) every hart at a store node of byte `b` is `b`'s owner, or `b`
is a SYNC byte (lock words, `started`/`first`) and the store is
`WCrel`/`WCexcl`; (ii) every hart at a plain load node of `b` is `b`'s owner
or `b` is a sync byte; (iii) no hart fulfils a store while
`w_rdw > fulfil_vpre` (the watermark violation).  Ψ is a pure predicate over
`(pool, σ)` — the residual monad in the expression names the node — so
adequacy exports it at every reachable state EXACTLY as φ, with a
three-line change; the WP leaves discharge it: CS accesses hold the
resource (i)/(ii); the enumerated racy leaves are aq or fence before their
next store (iii); `holding()`'s read is followed by the RMW whose own aq
read raises `fulfil_vpre` above the watermark (iii holds by the machine).

### 4.2 The transfer theorem (the research core)
Statement: `(∀ pf-reachable ρ, Ψ ρ)` (+ the trace facts Track A already
consumes) ⇒ `main_premises′ TS DS` for every canonical bundle of every
full-machine behavior — where `main_premises′` is the RELATIVIZED package
(Track A0/A0′ of the discharge design: `edges_split` only for the reader's
milestone-source fulfils, coverage at the fulfil's EXT view; `dev_epoch_ok`
over witness gmo positions).
Proof sketch, per clause, along D-M6-8:
1. Take a minimal `gdep3` cycle; its strict ancestry `U` is acyclic and
   pf-replayable (the existing exhibit machinery), so every SEGMENT HEAD `h`
   (first cycle event of an agent's po-segment) has a pf-real PRE-STATE
   — the pool holds the hart's residual monad at `h`, so Ψ at that state
   speaks about `h`'s node.
2. Case on the segment's outgoing fulfil `f` (the milestone source):
   - `f` data-, address- or control-dependent on `h` (or on any cycle-chord
     read): EXT with `V(dsrc)/V(asrc)/vcap` gives `ts_h < ts_f` — machine,
     no premise (THIS is what dependencies buy);
   - otherwise the instructions from `h` to `f` contain no branch depending
     on any unsupported read, so the segment's control path is
     value-independent and identical to a pf continuation from `h`'s
     pre-state; Ψ(iii) on that pf continuation gives "fence before `f` or
     `f`'s EXT view ≥ the watermark", and Ψ(i)/(ii) give the
     ownership/sync case split; the trace facts + Track A1/A2 (coverage
     from the acquire chain of the byte's owner) close `ts_h < ts_f`.
   The gap I flagged in the discharge design — coverage of the EARLY
   message `m` is not a pf fact — is exactly what (i)/(ii) resolve: if `h`
   reads a non-sync byte then `h`'s hart OWNS it (pf-real pre-state), so
   `m`'s author wrote it as owner earlier and released before `h`'s hart
   acquired: a full-trace chain (Track A2) → covered.
3. `ee_ok`: Track A3's arms from the release/ownership site facts (i).
4. `bytes_ok`: `excl_byte` for RMW-only sync bytes, `sw_byte`/`handoff`
   from (i) via A2 chains.
5. `bad_wf`: with (i), a bad edge (foreign read of an owned unpublished
   message) contradicts ownership at a pf-real pre-state, so bad edges
   into segment heads do not exist; the measure for `bad_min` is the
   ownership transfer count — needs a lemma; ⚑ open until built.
6. `dev_epoch_ok′`: from the gmo positions + fence discipline at MMIO
   sites (permissive I/O semantics; a stated model assumption).
This is a real theorem, not plumbing; I believe it but will not claim it
until it is built.  Its shape is fixed enough to stage.

## 5. Staging (each stage green + committed; findings recorded)

- **D0 (design/decisions, this doc):** ⚑ approve the fork change
  (announce node), the label vocabulary, and the PARM-verbatim rule set.
- **D1 model:** monadic `sail_instr_announce` in the fork; regen; rebuild;
  fix the spike node counts.  ½–1 day.
- **D2 machine (LANDED 2026-08-17/18):**
  `WeakMem`/`WeakPromise`/`WeakPromiseFact`/`WeakPromiseBridge` with §2, and
  — because Layer 1 is generic in the labels — the whole robustness tower
  with it: the graph/acyclicity files, THE REPLAY
  (`WeakRobustProv`/`Ord`/`Sim`/`Cone`), the language/instance/capstone and
  the instruction-atomic tier.  See §2.3'' for the final definitions and
  §2.3' D-5 for the audit.
- **D3 language + instance + capstone:** `deps_of_bits`; `WeakEvLang` arms;
  `WeakEvInst`/`WeakEvPf`/`WeakEvCapstone` re-landed; `WeakEvLift`'s rules
  and the disk rules re-landed (`hart_ws` grows).  1–2 sessions.
- **D4 replay:** `WeakRobustProv`/`Sim`/`Cone` with the three new folds;
  `robust_main` re-landed.  2–3 sessions (the big one).
- **D5 premises′:** A0 (relativized `edges_split`) + A0′ (fabric gmo
  positions, re-land G5a) — independent of D2–D4 in content, do in
  parallel.  1–2 sessions.
- **D6 Ψ export:** the two inert components + ownership map in
  `weak_state_interp`; the three-line adequacy export; the leaf-family
  obligations folded into the M4 port's chokepoint rules (so they are
  paid once).  1–2 sessions, on the M4 timeline.
- **D7 transfer theorem** (§4.2).  Unknown; budget 3+ sessions; the first
  milestone is the "dependent `f`" case (should be a page) and the
  "independent `f`, sync byte" case (racy sites).

## 6. Risks and what would make me change the plan

- The Sail announce change turns out to disturb more than node counts
  (e.g. certification data keyed on node offsets) — mitigated by the
  `exec_eff` bridge (M4-S1), which never counts nodes.
- PARM's `vcap`/exbank semantics interact with our fused RMW in a way that
  breaks a replay crux — surface it in D2/D4 with a litmus in
  `WeakLitmus`; the fused RMW is a machine-CHOICE we can revisit.
- The transfer theorem's independent-`f` case may need a stronger Ψ than
  §4.1 (e.g. per-hart "in CS of lock L" ghost) — that is more export
  work, not a dead end.
- If D7 stalls, the fallback is the honest one from the discharge design:
  `main_premises′` stated, Track A + Ψ machine-checked, and a small
  explicit residue named per site — strictly better than today, and every
  D1–D6 artifact is kept.
