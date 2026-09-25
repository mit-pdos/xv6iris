# Brief: the I/O-trace track (console ghost, Rocq ConsoleInv) — plan for steps (2)–(5)

User decision (Sept 25 2026): "(a′) first, block fileread" — open the I/O-trace track so the
console ghost (Rocq `ConsoleInv.v`) can be ported Rocq-literally; `fileread`'s FD_DEVICE arm
(D5b in `fs7_file_layer.md`) waits for step (5).

All standing rules of `fs0_common.md` / `fs7_file_layer.md` §0 apply (Rocq-literal, one capacity
instance per camera, eb-generic new contracts, stage files without the Proof prefix, fast proofs,
no `sorry`, report every process-layer deviation).

## 0. Step (1) — LANDED (branch of the step-1 worktree; three commits)

What exists now, and what later steps consume:

| Lean | Rocq | content |
|---|---|---|
| `MachCSL/ObsTrace.lean` (~690) | `ObsTrace.v` (608) | `obsWire`, `isIo`, `obsStep`/`traceShape`, `obsEndsIn` (+`_snoc`, `_inj`), `histExt`/`ohistLe`/`ohistExt` + laws, `obsBoots`, `openSeg`, `obsWf` (+`_init`, `primStep_obsWf`, `step_/nsteps_/run_obsWf`), `cyclesOf` |
| `MachCSL/LogEntryDefs.lean` (60) | `LogEntryDefs.v` (45) | `LogEntry`, `leHist/leByte/leEcho`, `ConsArm`, `ConsHist` (`chAcc chLog chDl chArm`) |
| `MachCSL/Resources.lean` | `RiscvPtsto.v` §obs | `MachFixedGS` fields `obsVarG obsName obsTotal obsPred obsHistG obsHist rxTag killCred consRes` (+ persistent/timeless fields); `obsHistLb/obsHistAuth/obsHalf/obsAuth/obsFrag`, `obsAuth_lb`, `obsHistLb_prefix/_cmp/_mono`, `obsAgree`, `obsUpdate`, `obsN`, `obsInv`, `rxTagTriv killCredTriv consResTriv obsPredTriv obsLedger`, `obsInterp` (+`_silent`, `_close`); `stateInterp = powerInterp g ∗ obsInterp g κs` |
| `MachCSL/WpDev.lean` | `RiscvExec.wp_uart_step`, `WpUart.uart_obs_permit(_triv)` | `wpDev_lift_obs` (callback gets `obsAuth h` + shape / wire tie / era stamp, returns `obsAuth (h ++ obs)`), `wpDev_lift` (silent devices), `devObsPermit N d R` (+`_silent`, `_triv`), `wpDev_localR` (+ permit) |
| `MachCSL/Power.lean` | `RiscvAdequacy.wp_power_loop`'s `Hobs` | `wp_power` takes the trace hook `Hobs` and `obsInv`; `powerYield`, `powerBootRes` carries `consRes (gen+1) [] ⟨[],[],[],none⟩` |
| `Xv6/UartInv.lean` | `WpUart.wp_uart_loop` | `wpDev_uart_inv` takes the port's permit; `wpDev_uart_inv_triv` |

Not ported in step (1), on purpose (to be decided in the step named):
* `riscv_in_res`, `riscv_out_res` — dead after Rocq's redesign R2 (their only consumers
  `WpUart.in_claim_at` / `out_claim_at` have no uses; adequacy instantiates them trivially);
  superseded by `riscv_cons_res`. Flagged, not ported.
* `riscv_win_res` (the echo window token) and the power-on `Tn` (init's turn) — still threaded in
  Rocq (`uart_rx_writer`, `power_boot_res`); port in step (2) with the PLIC payload if the
  console ghost still needs it after R2 (Rocq's own R2 comment says the arm-in-history makes it
  unnecessary — check `ProofConsoleintr.v` before porting).
* `riscv_client_T/riscv_client` — adequacy-only.
* `riscv_crash_pred` / the durable-disk lend of `Hobs` — Lean has no fixed disk conjunct.

## 1. Step (2) — the UART/PLIC invariants to WpUart's shape

Rocq sources: `WpUart.v` (4326; §§ uart_names ghosts 350–1250, column 790–1250, invariants
1590–2045, links 2100–2500, THR store/`store_ob` 2790–3020, permits + thread 3310–3700),
`UartNames.v` (138), `WpUartgetc.v` (331), `WpSconfUartAccess.v` (879).

Lean today: `Xv6/UartTrace.lean` (147: `Xv6G`, `UartNames` = acc out tx dlab rxin rxpop init),
`Xv6/UartInv.lean` (926), `Xv6/UartModel.lean` (197), `Xv6/PlicInv.lean` (747),
`Xv6/PlicPlan*.lean` (758).

Work, in order:
1. `UartNames` gains Rocq's `un_rxpush` (mono_nat — the Lean `rxin` mono-list may stay if
   every consumer only needs the count; decide by grepping `uart_rx_pushed_lb` uses),
   `un_rxhi`, `un_loghi`, `un_log`, `un_deliv`, `un_logm`, `un_arm`. ONE record edit
   (`UartTrace.lean`); cameras: `GhostVarG (Option (List Obs))`, `MonoListG LogEntry`,
   `GhostVarG (List (List Obs × BitVec 8))`, `GhostVarG (List LogEntry)`,
   `GhostVarG (Option ConsArm)` — all NEW types, add each ONCE to `Xv6G`.
2. The receive COLUMN (`uart_col`, `uart_col_ok`): each queued byte carries the history it
   arrived at (`obsEndsIn`), the column's histories chain (`histExt`), and each carries its
   `rxTag` — filed by the port's permit (Lean: into `R s'` = `uartGhosts γ s'`, the generic
   `devObsPermit` has no separate tag output).
3. `cons_claim_at` (the port's ONE claim: `consRes (genId+1) ho H` at Uart0, `emp` at Uart1,
   with `obsHistLb` on its witness, `chAcc H = acc u`, `consHistOk H` — needs ConsLog from
   step 3, so 3a (ConsLog pure) goes FIRST).
4. The PLIC payload (`uart_rx_writer`: rx token, rx-hi / log-hi halves, arm half, [window]).
5. The port permit at the app level (`uart_obs_permit_ledger`) — a `devObsPermit` instance.
6. The links: `cons_link`/`out_link` (THR store, `store_ob`), `echo_link`, `read_link`,
   `cons_read_pay`; the accessors of `WpSconfUartAccess` (THR write re-establishes the claim
   from a caller-supplied view shift) into the Lean accessors (`thr_write_au`, `rhr_read_au`).

Blast radius: 49 Xv6 files mention `uartInv`/`UartNames`/`plicInv` (list:
`grep -rl -E "uartInv|UartNames|plicInv" Xv6`). Most only thread the invariant; the ones whose
PROOFS open it: `UartInv`, `PlicInv`, `PlicPlan*`, `ProofUartputcSync`, `ProofUartwrite`,
`ProofUartintr`, `ProofUartinit(one)`, `ProofPlicClaim/Complete`, `ProofConsputc`,
`ProofConsoleintr`, `ProofConsoleinit`, `ProofConsolewrite`, `ProofPrintk`, `ProofPanic`,
`ProofPrintint`, `ProofPrputc`, `ProofProcdump`, `ProofDevintr`. Worktree agent(s) only.

## 2. Step (3) — ConsLog, LogEntryDefs

* `LogEntryDefs` — DONE in step (1) (the fixed record names its types).
* `Xv6/ConsLog.lean` ← `ConsLog.v` (382): `echo_of`, `cons_erase`, `consputc_bs`,
  `cons_echo`, `log_echoed`, `hist_chain`, `gap_ok`, `read_ok`, `log_ok`, `cons_ev`,
  `cons_step`, `cons_ev_ok`, `arm_ok`, `cons_hist_ok` (+ the step lemma). PURE; main tree; no
  dependency beyond `MachCSL.ObsTrace` + `LogEntryDefs`. ~400 Lean lines, one agent, a few
  hours. Can run in PARALLEL with everything else and must land before (2).3.

## 3. Step (4) — ConsoleInv

`ConsoleInv.v` (2663; 113 lemmas). Split (stage files, no Proof prefix, one owner = consoleread/
consoleintr family):
* `ConsoleRing.lean` — pure ring algebra (`cons_ok`, `cons_slot`, `cons_row`, `cons_xlate`,
  `cons_stored`, `cons_pend`, lines 120–400 and their lemmas, ~900).
* `ConsoleTags.lean` — tags/window/logged/gaps (`cons_tagged`, `cons_chain`, `cons_below`,
  `cons_window`, `cons_gtop`, `cons_logged`, `cons_gaps_ok`, `cons_gp_ok`, `cons_log_ok`,
  `cons_owed`, ~800).
* `ConsoleInvDefs.lean` — the Iris layer (`cons_names` → Lean `ConsNames`, `cons_data`,
  `cons_tags`, `cons_stored_auth/lb`, `cons_cursor`, `cons_rdtok`, `cons_deliv`, `cons_logm`,
  `cons_hi`, the lock body, `devsw` constants, lines 1400–2663, ~1100).
Replaces `Xv6/ConsoleDefs.lean` (86) — grep its 13 users (`HandlerEnv`, `FsCfgDefs`,
`SpecConsole*`, `ProofConsole*`, `ProofUartintr`, `SpecUartintr`, `Icache*`) and keep its
names as abbreviations if they still read naturally.
Camera check: `cons_names` gnames go to existing `Xv6G` cameras where the type matches
(`MonoListG (BitVec 8)`, `GhostVarG Nat`), new types ONCE into `Xv6G`.

## 4. Step (5) — re-prove the console functions

Order (by callee): consputc → uartintr → consoleintr → consolewrite → consoleinit →
consoleread. Rocq Spec/Proof sizes: SpecConsputc 187 / ProofConsputc 646; SpecUartintr 205 /
ProofUartintr 1441; SpecConsoleintr 439 / ProofConsoleintr 4498; SpecConsolewrite 325 /
ProofConsolewrite 2253; SpecConsoleinit 210 / ProofConsoleinit 552; SpecConsoleread 382 /
ProofConsoleread 4302. Lean today: ProofConsputc 264, ProofUartintr 658, ProofConsoleintr 1716,
ProofConsolewrite 1316, ProofConsoleinit 283, ProofConsoleread 2070 (thin posts).
Every new contract eb-generic (`wp_X_eb`), as the landed fs cone.

## 5. Batching

* Batch A (parallel): (3) ConsLog [main tree, new file]; (4a) ConsoleRing + ConsoleTags [main
  tree, pure new files].
* Batch B (one worktree agent, serial): (2) UartNames/Xv6G record edit + UartInv/PlicInv +
  accessors + the step-(2) blast radius. Needs ConsLog.
* Batch C (after B): (4b) ConsoleInvDefs; then (5) in the order above — consputc and uartintr
  can go in parallel worktrees (disjoint files), consoleintr after uartintr, consolewrite /
  consoleinit in parallel, consoleread last; then fileread (D5b) resumes.

## 6. Risks

* The Lean devices are generic programs, so step (1) made the language enforce event
  faithfulness (`devObsOk`, an unfaithful device answer is blocked). Any NEW device program
  must answer faithfully or it will spin; the UART's arms are proven faithful
  (`Uart.txArm_ok`, `Uart.rxArm_ok`).
* The generic permit (`devObsPermit`) has no tag output; step (2) files the rx tag inside the
  client's `R` — check `WpUartgetc`'s consumers read it from the column, as in Rocq.
* `wp_power`'s hook yields only `consRes`; if `win_res`/`Tn` are ported, `powerYield` and
  `powerBootRes` grow (no callers yet: there is no Lean adequacy theorem).
