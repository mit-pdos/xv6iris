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
- **D-3 (`jalr` control).** As above: STRONGER than PARM's language, inside
  RVWMO ppo 11.
- **D-4 (CSR / non-GPR registers).** `w_regv` tracks GPRs only; CSR-mediated
  chains and PC are NOT dependencies (RVWMO's syntactic dependency is on
  the integer/FP source registers) — WEAKER or equal, free.  `x0` never
  gets a view.
- **D-5 (`.aq`/`.rl` orders).** Keep today's mapping of the access kinds to
  `aq`/`rl` (`WeakInterp.classify`); PARM's `acquire_pc` vs `acquire`
  distinction (RCpc vs RCsc) is today's `aq` for the `vrn/vwn` raise and
  the `vrel` join — re-audit `load_vpre`/`load_post` against the two `ifc`s
  when D2 is written and record the outcome here.
- **D-7 (THE FORWARD BANK — a genuine STRENGTHENING in today's machine, to be
  fixed by D2; found 2026-08-17 while auditing containment).**
  `WeakMem.store_post` records `w_fwd[a] := (t, w_vwNew ws)`, so a forwarded
  read (a load reading the agent's own latest store to `a`) gets post-view
  `vpre ⊔ w_vwNew(at store time)`; PARM's `FwdItem` records
  `view_loc ⊔ view_val` (the store's ADDRESS/DATA dependency views — RVWMO
  ppo 12, "a load reading an intermediate store inherits that store's
  dependencies"), which is `bot` in a dependency-free machine.  Ours is
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
- **D-6 (the disk agent).** `virtio_prog`'s events carry empty `srcs`; its
  ordering is aq/fence-based — WEAKER than a hart with the same accesses
  (free), and exact for what the driver relies on.

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
- **D2 machine:** `WeakMem`/`WeakPromise`/`WeakPromiseFact`/`WeakPromiseBridge`
  with §2 (state, labels, rules; `wp_swap` re-proved).  1–2 sessions.
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
