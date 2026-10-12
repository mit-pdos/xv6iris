VERDICT: NOT SATISFIED

# Review R25 of `notes/weak-allocproc-plan.md` (rev 28)

Reviewer: one-off adversarial advisor (advisory only: no builds, no proofs, no git or jj, no subagents).  Every cite
below was read at the working-copy tip of `../xv6iris-weak` (file mtimes 2026-10-12 00:32 for the W-DISK files).  Scope
per the R25 brief: verify the W-DISK DONE record against the tip (deviations d1–d4), the [OWN.37] restructuring of W8,
the `holding+0x12` correction, the "M1 does NOT wait for W8" claim, the W13 (I) gate, and decide whether each item of
the launch set W4 F9 ∥ W8-β′ ∥ R-ctx ∥ W5 CORE is launchable as written.  Items (a)/(b) of the standing brief were
settled in R1–R24 and are spot-checked only (`tools/ci/roots.txt:6,19`, `tools/audit/baseline.json:11-14`,
`Weak/WeakAxiomatic3.lean:2060-2071`, `Weak/WeakSrvwmoLitmus.lean:1663-1670` — unchanged).

**Sign-off.**  NO — three required changes, all S text, one revision.  The W-DISK record is accurate (every `:N` in the
header and in §C W-DISK's record resolves to the named declaration at the tip; d1–d4 are real and sound), the
`holding+0x12` correction is right, "M1 does NOT wait for W8" holds EXACTLY as stated, W13 (I)'s gate is met, and **W4
F9 and W5 CORE are launchable as written.**  **W8-β′ and R-ctx are NOT**: **[R25.1]** the pinned export `chainOkAt`
(binding text, §C W8 `:2478-2481` = W8-design §1) is FALSE on reachable states — the hardware A/D write-back on the
SHARED kernel page table is an exclusive store by the walking hart that every other hart's walk plain-reads and
`coh`-stamps, with no sync chain (`MachCSL/KptInv.lean:4-8`, `WpPtWalk.lean:3-7,455-462`, `Lang.lean:373-375,400`);
R-ctx's (f2-ctx) invariant ("every foreign-HART entry `t ≤ bound ξ` has a `syncPath`") inherits the hole, so R-ctx
would table its uses against a wrong target; **[R25.2]** W8-β′'s acceptance ("stated in `Xv6/AccessDiscipline.lean` and
PROVED invariant through the reserved-region rules", `:2566-2568`) names no Lean statement a worker can be held to —
`Xv6/` cannot be imported by MachCSL, the registry agreement W8-design puts "inside the twin" (`W8-design.md:452-453`)
has no twin until W8 (f2-ctx), so as written β′'s facts reach NO theorem and W13 (K) is not actually unblocked;
**[R25.3]** R-ctx's file list (19 files, `:1184-1189`, `W8-design.md:369-375`) omits `Xv6/ProofSwtch.lean` — the FIVE
`kctx_move_in/out` applications that ARE the `swtch` handoff door — and `Xv6/PipeBirth.lean` (the only dynamic lock
birth, `lock_pay_born`), and two of its counts are wrong.  No owner question is needed (all three are plan text in the
sound direction; [R25.1] is not a memory-model question — see the last section).

## What was checked and holds

- **The W-DISK record (header `:3-25`, §C `:1528-1566`, §A Names `:432-441`) against the tip.**  `Weak/VirtioProg.lean`
  is 672 lines; `DM` `:257-266` = `DRet`/`DRead`/`DFence`/`DWriteDev pre g pa bs k`/`DPop h k` (no plain `DWrite` — d3 ✓),
  `Dres` `:269-273`, `DmWf :279`, `popState :319` (= `{ setPhase v h .popped with seen := v.seen + 1 }` — exactly
  `body`'s guard, `MachCSL/Dev/Virtio.lean:570-572` ✓), `drainAll :323`, `preCaptureHead :338` (pre-check → `.fetched` →
  `taken` guard with `taken := some h` set IN the guard — exactly `serve :526-529` ✓), `dusedTail :394` (used element →
  `DFence` → `idxNode` with `serve`'s guard verbatim, `:548-554` ✓), `virtioProg :438`, `virtioProgWf :661`; the header
  carries the Spec-first text, THE FOLDING RULE, the (M1)–(M9) table and the "moves the fabric?" column (`:1-130`).
  `WeakEvLang.ediskStep :936`, `ediskStepWf :1360`, `eprimStepDiskReducible :1393`, `setDvirtioSelf :922` ✓.
  `WeakEvInst.pdiskProg :499` has exactly the ten arms (`:499-560`: START, `DRead`, `DFence`, `DWriteDev` STORE / SKIP /
  ABORT, `DPop` refused / moved, `DStall`, `DRet DIdle`), `pdiskProgLabel` five shapes, the STATE-AWARE `pdevEv :604`
  (`LDev` OR `.PDisk (some (DWriteDev ..))`), `pdiskProgDevFree :1759`/`pstepDiskDevFree :1781` with the extra "not at a
  `DWriteDev`" hypothesis, `pdevEvOk :1792` "statement unchanged" ✓.  `WeakEvDisk.lean` (850): `ewpDiskStart :388`,
  `Read :431`, `Fence :488`, `WriteDevStore :524`, `WriteDevSkip :607`, `WriteDevAbort :666`, `Pop :722`, `PopRefused
  :772`, `Idle :816`; deviation 5 at `:52-61` retires `ewp_disk_write`/`ewp_disk_commit` (d4 ✓).  `PfStepTsoMem.
  pfDWriteDevRowMem :698`/`pfDSkipRowMem :806`, `pfDWriteRowMem :672` kept as "(13) … without its fabric move" ✓;
  `PfStepTsoView.rowDiskDevMove :808`, `rowDiskWrite :796`, the (↓) rows `:45-46` ✓.  `WeakRvwmoSupply.devQuiet :177`,
  `devQuietStep :183`, `pdevEvFalse :209`/`pstepEvDevfree :219` restated with `devQuiet p` and proved by cases on `p`
  ✓; `WeakRvwmoFab.hemitfStatesQ :396`/`hartConffStatesQ :556` carry `devQuiet p ∧ (∀ dp, p = .PDisk dp → … LDev ∉ …)`
  ✓; `gfexecConf :620` with the INTERIM clause `:633-634` commented "DELETED BY W13 (I)" ✓; `fconfRowsPin :885`,
  `fconfSupply :928`, `emDev :158` ✓.  The quiet-boot hypothesis is `∀ i, i < N → devQuiet (boot i)` at
  `WeakRvwmoFabInd.lean:425,465,537`, `WeakRvwmoLin2.lean:1007,1024`, discharged by `WeakRvwmoCapstone.epsInitQuiet :232`
  at `:268` (d2 ✓); `xv6RvwmoSafeModuloF :238`; `WeakEvCapstone.lean:1183` unchanged ✓.  `AxOpsem.pstepProgReadCont :622`'s
  `.PDisk` case destructures ten arms (`:647-651`) — d1 ✓ (and sound: the file was not on the brief's list only because
  the brief did not know the shape reached it).  `grep DWild Weak/` = 0 ✓.  `MachCSL/Dev/Virtio.lean` (600 lines) and
  `Xv6/*VirtioDisk*.lean` have mtime 2026-10-05 — UNTOUCHED ✓; `MachCSL/Lang.lean` mtime 2026-10-11 17:09 (W-DMA0) ✓.
  Build/lint/audit cannot be re-run here (no `.lake` artifacts in this checkout; builds live on the VM) — the plan's
  "green" is taken on the worker's word, as every rev before.
- **"M1 does NOT wait for W8 — EXACTLY" (`:1202-1208`).**  `srvwmoXv6M1Premises` (`Weak/SrvwmoXv6Witness.lean:599-607`,
  quoted at `:532-536`) names no access discipline; W5 CORE's inputs are `machRunOfPfRun` (`MachOfPf.lean:1535`),
  `pfStepTso`, `powerInterp_textPristine` (`Xv6/TextPristine.lean:122-123` — a statement about `powerInterp`, which a
  state-interpretation change rebases but does not re-state), HSafe from `xv6FsAdequacy_closed`'s first conjunct, and
  W-DISK; W8-β′/W8 edit `Resources.lean`/`Lock.lean`/`KCtx.lean`/the context layer and not `MState`/`Lang.lean`
  (W8-design §0 item 2).  Logic-independent, build-order-coupled — as the plan says.  ✓
- **The `holding+0x12` correction (header `:40-46`, §C W13 R5 `:2345-2353`, `:2361-2364`, §C W8 `:2445-2447`, §C W11
  `:2589-2592`, §D Q-HOLDING `:2744-2782`, `notes/xv6-holding-race.md`).**  `KernelPins.lean:255` is `(0x80000c04,
  PResidue) -- holding+0x12` ✓; `MachCSL/Lock.lean:18-22` states the cpu word's discipline ("every entry is 0 or the
  writer's own `&cpus[c]`; any hart that is not the recorded holder has 0 as its latest own entry, so a racy read by it
  never returns its own pointer (`lkCpu_read_not_mine`)") ✓; `lockWordAt :53-56` ✓; `lockBody :590-597` holds both
  words as `wordCell`s with `lockWordAt ∧ lkCpuAt` ✓.  The RVWMO argument in Q-HOLDING's Spec line (rules 1–3 / load
  value: a hart cannot read its own older store past its own newer one) is right.  Q-HOLDING meets the 2026-10-10
  format (Spec first, plain language, tiny example, definitions, why it matters, options marked).  ✓
- **W8-design's numbers.**  PStack buckets 82 + 747 + 192 + 13 = 1,034 = the pin table (1,035 occurrences of the word,
  one in the header) ✓; `PPerCpu` 3 at `:476,546,548` ✓; the cpu-cell rules exist (`wp_s_sd_proc`
  `MachCSL/WpSmodeProc.lean:107`; `wp_s_sw_noff_lend :1159`, `wp_s_sw_intena :1076`, `wp_s_lw_noff :966` in
  `WpSmodeRules.lean`) with `Xv6/` uses 3 + 2 + 2 + 4 = 11 (`ProofScheduler`, `ProofPopoff`, `ProofSched`,
  `ProofPushoff`) ✓; `lkFresh` in 30 `Xv6/` files (plan: 29 — [R25.s3]); `KernelGeom` is a MachCSL class
  (`KCtx.lean:510`), `aCpuProc :526`, `cpuCells :556-560` ✓; `BootCarveHart.lean:81,84` ✓; `SpecScheduler.lean:9-15` ✓;
  `kstackVa` `SpecProcinit.lean:66`, `p->kstack = KSTACK` `:11` ✓.  R-ctx's law counts: `ctx_absorb` 6/3,
  `ownCtx_floor_view` 8/4, `ctxStamped_raise` 5/2, `lockHook_llb` 13/10, `ownCtx_key_vis` 3/2, `ctx_unstamp` 1,
  `ctx_park` 3 — all ✓ by grep; `ctx_move` and `lock_pay_*` are off ([R25.3]).
- **W13 (I)'s gate (`:1193-1195`, `:2235-2237`).**  The fused `DWriteDev`, the state-aware `pdevEv :604` and the interim
  clause `Fab.lean:633` are in the tree ✓; (M) landed.  Gate MET.  (Not in the launch set — usage; fine.)
- **W4 F9 as written (`:1406-1527`).**  Every binding cite is the tip's: `preCaptureHead :338` = `pre₁`, `popState :319`,
  the W2 rows, `MachOfPf.lean` 1659 lines unchanged (`SimRel :305`, `Hyps.disk :644`, `simDev :1193`, `simWire
  :1295-1354`), the `Virtio.lean` line numbers (`:522,526,529,533-534,536,539-554,559-580`) — confirmed against the
  600-line file.  The bookkeeping rows (POP 1 → 4: `get :567`, `guard :570-572`, `fork :573`, `serve`'s `get :522`;
  refusal 1 → 2) match the code.  **LAUNCHABLE.**
- **W5 CORE as written (`:1189-1193`, §C W5).**  Inputs present; `Weak/SrvwmoXv6Adequacy.lean` does not exist yet (the
  item creates it — [R25.s2]).  **LAUNCHABLE.**

## REQUIRED changes

- **[R25.1] `chainOkAt` as pinned is FALSE for page-table-entry bytes: the hardware A/D write-back is a foreign-hart
  entry every other hart's walk observes without a sync chain.  The export must class PTE bytes; R-ctx must table the
  walker; the W13 census's "kernel_pagetable non-racy" line must go.**
  *What is wrong (evidence).*  §C W8 `:2478-2481` (= W8-design §1 `:147-151`, "the binding text") pins
  `chainOkAt σ := ∀ j a H e, σ.mem[a]? = some H → e ∈ H → e.t ≠ 0 → e.t = (σ.hr j).coh a → (hA : e.tid < NCPU) → e.tid ≠
  hartAgent j → (∀ b, custAt σ a e.t ≠ .lockw b) → syncPath σ ⟨e.tid, hA⟩ e.t j (σ.top + 1)` — the ONLY exemptions are
  DMA authors and lock-layer bytes.  But (1) the kernel page table is SHARED and the hardware writes its A/D bits back
  from every hart: "Every hart walks the same kernel table, and the hardware writes its A/D bits back concurrently from
  all of them, so under weak memory a reader may see any of the values ever written to an entry" (`MachCSL/KptInv.lean:
  4-8`; `pteVariant :38-41`); (2) the write-back is an EXCLUSIVE STORE BY THE WALKING HART — `read_pte_exclusive`/
  `write_pte_conditional` (`WpPtWalk.lean:3-7`, `swp_write_pte_conditional :156-165` with `exclWriteAU cpu pa 8 …`,
  `swp_update_and_write_pte_kpt :455-470`), i.e. `MState.store σ cpu pa 8 w true`, which appends `HEnt ⟨top+1, hartAgent
  cpu, _⟩` (`Lang.lean:151-156`); Svadu is ON in this image (`start()` sets `menvcfg = ADUE | STCE`, `Xv6/SpecStart.
  lean:29,40`; `Xv6/TransPt.lean:310-319` discharges `hadue`); (3) every OTHER hart's walk reads the entry with the PLAIN
  arm that stamps `coh`: "a **plain read** (explicit non-exclusive, **or a page-table walk**) reads as the hart … the
  watermark and the footprint's coherence floors move" (`Lang.lean:373-375`; the arm `σ' = σ.afterLoad cpu req.pa n tvn`
  `:400`; `swp_read_pte` goes through `swp_sail_mem_read_plain_au`, `WpPtWalk.lean:48-57`; `HRead.afterLoad` stamps the
  FOREIGN source, `TsoMem.lean:354-356`).  So at the post-state of hart `m`'s walk of a kernel PTE whose latest entry is
  hart `k`'s write-back at `t₁`, `(σ.hr m).coh a = t₁`, `e.tid = k ≠ m`, `k < NCPU`, `custAt σ a t₁ ∉ .lockw`, and
  `chainOkAt` demands `syncPath σ k t₁ m _`.  *Concrete reachable counterexample.*  Kernel TEXT pages first executed
  after boot (`sysfile.c`, `exec.c`, `pipe.c`, most of `trap.c`/`proc.c`'s `sched`/`sleep`/`exit` — nothing in `main`'s
  boot path touches them, and `A` is per 4 KiB page): hart `k`, running process P, takes a syscall and first-executes
  the `sys_open` page at `t₁ > bootEnd σ` — its fetch walk writes `A` back; hart `m` has been in user mode since
  before `t₁` on an unrelated process Q (Q's `p->lock` was released to `m` by a hart before `t₁`), traps, and its fetch
  walk of the same page plain-reads `k`'s variant.  Between `k`'s write-back and `m`'s walk `m` performed no acquire
  (`syscall` → `sys_open` fetches happen BEFORE `m` touches `ftable.lock`), so no `syncPath` exists: `chainOkAt` is
  false on a run the SC tree certifies (`KptInv` admits exactly this interleaving).  The same holds for `D` on any
  kernel-data page first written post-boot.  *Why nothing downstream needs the chain.*  The write-back message is pinned
  `.WCexcl` (`Weak/WeakKptStale.lean:26`: "The write-back message class is PINNED at `.WCexcl` (the walk's write-back
  is `ak_latest`)"), so W11's `badSeg` (a `.WCplain` source, `:2585-2586`) is VACUOUS there; the walker's value-
  insensitivity to the variant is `WeakKptStale`'s racy-absorption theorem, already landed.  The hole is in the EXPORT's
  statement, not in the kill.  *Consequences if left.*  W8 (f2-ctx)'s worker builds against a false predicate; R-ctx
  (launching now) checks whether each TSO-leaky use "can be re-justified by a chain or the device-key arm"
  (`:2538-2542`) against an invariant — "every foreign-HART entry `t ≤ bound ξ` has a `syncPath` to ξ's hart"
  (`W8-design.md:343-344`) — that the walker's own rules (`WpPtWalk`, `TransPt`) CANNOT re-establish (the write-back
  needs no key, the walk's read raises `coh` outside any chain); without a named arm R-ctx will either miss the walker
  entirely (it is not in the 19 files) or table it as RESISTS and send a part to (f1) for the wrong reason.  The W13
  census's exclusion list says "Excluded as non-racy (no concurrent writer): … `kernel_pagetable`" (`:2378-2379`) —
  false by `KptInv.lean:4-8`.  And `:492`'s "xv6 boots with `menvcfg = 0` (`BootBoard.lean:30`; `start()` sets only
  STCE)" is wrong about ADUE (FIOM = 0 still holds, so the I/O-fence point stands).
  *Exact change.*  (a) §C W8 skeleton `:2471-2481` and the W8-design §1 pointer: add `| pte` to `Cust` ("page-table
  pages: the kernel table reachable from `KernelSyms.kernel_pagetable`'s root, and `proc[j].pagetable`'s pages"), add
  `(∀ b, custAt σ a e.t ≠ .lockw b) → custAt σ a e.t ≠ .pte →` to `chainOkAt`'s hypotheses, and add the clause
  **`pteDiscAt σ`** := every post-boot entry on a kernel-table PTE byte is an A/D VARIANT of the entry's canonical value
  (`KptInv.pteVariant`, the σ-form of `kptBody`'s pin) authored by a hart; `xv6AccessDisc := chainOkAt ∧ lockWordDiscAt ∧
  pteDiscAt ∧ cpuStaticAt ∧ cpuProcDiscAt ∧ utextDiscAt`; user-table pages may stay `.proc j` (their A/D write-backs are
  by the running hart, chained by the `p->lock` hop like the kstack) — the spike decides, say so.  (b) §C W11 (i)
  `:2589-2592`: beside the lock-layer `badSeg` arm, one line: "PTE bytes need no arm — the write-back is `.WCexcl`
  (`WeakKptStale.lean:26`), never a `badSeg` source; `pteDiscAt` is consumed only by the walker's racy-absorption
  (`WeakKptStale`)".  (c) R-ctx's brief (`:1184-1189`, §C W8 `:2538-2542`): add the walker as a NAMED case — "the A/D
  write-back (`WpPtWalk.lean:455-470`, `Xv6/TransPt.lean`) and the walk's plain PTE read are a `pte-key` arm beside the
  device-key arm: exempt from the chain invariant, covered by `pteDiscAt`; R-ctx tables it as such, not as RESISTS".
  (d) `:2378-2379`: move `kernel_pagetable` out of "non-racy" into the table as "C6 kernel PTE reads by the walker —
  racy against other harts' A/D write-backs (`KptInv.lean:4-8`), `.WCexcl` source, variant-insensitive
  (`WeakKptStale`), covered by `pteDiscAt`".  (e) `:492`: "`menvcfg = ADUE | STCE` after `start()` (`SpecStart.lean:
  29,40`; FIOM = 0 — the i/o bits still never reach `LFence`)"; §A(4) `:312` and §B(2) `:562-564` may cite `pteDiscAt`
  as where the "concurrent hardware A/D write-back" lands in the export.  S text.  Spec, for the record (not an owner
  question): RVWMO orders implicit page-table accesses by SFENCE.VMA, not by FENCE, and the privileged spec makes the
  A/D update atomic with respect to other accesses to the PTE; the Sail model in this tree performs it as
  `read_pte_exclusive`/`write_pte_conditional` (`WpPtWalk.lean:3-7`); Zifencei/PMAs silent.  Every option above is
  FAITHFUL (an internal export's shape; the published quantifier and conclusions are unchanged), so the plan text is
  REQUIRED, not put to the owner.
- **[R25.2] W8-β′'s acceptance names no theorem; as written its facts reach no root and W13 (K) is not unblocked.**
  *What is wrong (evidence).*  §C top `:1179-1184` and §C W8 `:2566-2568` say W8-β′ "yields `cpuStaticAt` +
  `lockWordDiscAt`" and is accepted when they are "stated in `Xv6/AccessDiscipline.lean` and PROVED invariant through
  the reserved-region rules".  But the reserved-region rules are MachCSL (`Resources.lean`'s `memModelAt :951-956`,
  `Lock.lean`, `KCtx.lean`), and `Xv6/` never imports into MachCSL — so "invariant" must be a MachCSL-side predicate
  (e.g. a `reservedOk σ reg` conjunct beside `⌜mmOk σ⌝`, under `[KernelGeom]` + the ghost lock registry), and the step
  "`reservedOk σ reg` + registry agreement ⇒ `lockWordDiscAt σ ∧ cpuStaticAt σ`" is `Xv6/`-side; W8-design puts that
  agreement "inside the twin" (`W8-design.md:452-453`: "The registry agreement (MachCSL ghost registry ⊆ `xv6LockWord σ`)
  is a small `Xv6/` invariant inside the twin") and prices the (r2) twin under W8 (f2-ctx) only (`:460`: "+ root twin
  ≤ 1.8k"; β′'s row `:459` has no twin).  Hence at β′'s landing there is no `powerInterp ⊢ … ⌜g.pow = true → …⌝`
  extraction (the `powerInterp_textPristine` shape, `Xv6/TextPristine.lean:122-123`) and no root; `lockWordDiscAt`
  exists as a definition the audit never sees.  The plan's "unblocks W13 (K)'s `lk->cpu` precondition" (`:1183-1184`,
  `:2629`) is then true only of the STATEMENT; the fact W13 (K) needs at the realizing run arrives only with W8
  (f2-ctx) — L–XL, gated on R-ctx, with an (f1) fallback — which is not what "unblocks" says, and the serial lane's
  "one `Xv6`-cone rebuild each" (`:1946`) hides that β′'s rebuild buys no root-level fact.  A worker reading the brief
  cannot tell which Lean statement closes the item.
  *Exact change (§C top `:1179-1184`; §C W8 (3)/(6)/Acceptance `:2505-2510`, `:2558-2559`, `:2566-2568`; serial lane
  `:1947-1949`; D24 `:3428-3432`).*  Pin W8-β′'s deliverables as three statements: (i) the MachCSL invariant — a
  conjunct of `memModelAt` (`Resources.lean:951-956`) or a sibling of `⌜mmOk σ⌝`, say `⌜reservedOk σ reg⌝`, stating
  per registered region (the `cpus[h]` cells `KCtx.lean:526-528,556-560`; each registered lock's two words
  `Lock.lean:590-597`) that every post-registration entry is by the region's structural author, re-established by the
  dedicated rules ONLY (the half-points-to mechanism of W8-design §4 keeps the generic rules out); (ii) the `Xv6/`
  extraction lemma `powerInterp_accessDiscβ : powerInterp g ⊢ … -∗ ⌜g.pow = true → lockWordDiscAt g.m ∧ cpuStaticAt
  g.m⌝` on `powerInterp_textPristine`'s pattern, with the registry agreement (MachCSL registry ⊆ `xv6LockWord σ`) as
  its `Xv6/` side; (iii) **the (r2) sibling root NOW, at the β′ conjunction** — `xv6DiscAdequacy_closed` with
  `xv6AccessDisc` provisionally `:= lockWordDiscAt ∧ cpuStaticAt` (registered in `roots.txt`/`baseline.json`/
  `tools/tcb/expected.json` per §B(12)), W8 (f2-ctx) then only STRENGTHENS the conjunction — RECOMMENDED, because it
  pays the twin once, settles W8-design §8's "no PowerOn hook" unverified point early (β′'s facts live in the state
  interpretation, so the twin should need only the extraction — the cheap case), and makes "unblocks W13 (K)" true.
  If the owner prefers to keep the twin in W8 (f2-ctx), the plan must instead say at `:1183-1184`/`:2629` "unblocks
  the STATEMENT of W13 (K)'s precondition; the root-level fact arrives with W8 (f2-ctx)" and move the twin's ≤ 1.8k into
  the lane's risk line.  Re-size β′ accordingly (≈ +0.3–0.5k for the twin if (iii), still M–L, still one rebuild).  S
  text.  Not a memory-model question (proof organisation; every option FAITHFUL).
- **[R25.3] R-ctx's file list misses the `swtch` door and the dynamic lock birth; two counts are wrong.**
  *What is wrong (evidence).*  §C top `:1184-1189` and W8-design §3.4 (`:369-375`) send R-ctx to "the 19 `Xv6/` files
  that use the laws directly" and count the transports as "`ctx_unstamp` 1, `ctx_park` 3, `ctx_move` 5, `lock_pay_*`
  3".  At the tip: `ctx_move` proper is applied ONCE (`Xv6/ProofForkretPark.lean:250`); the `swtch` handoff itself is
  `kctx_move_in`/`kctx_move_out` — FIVE applications in `Xv6/ProofSwtch.lean:251,253,268,270,274` (moving `ctxCells`,
  `stackOwn` and the context payload across the hart boundary) plus one in `ProofScheduler.lean:1000`; `ProofSwtch.lean`
  is NOT among the 19.  `lock_pay_*` has ONE `Xv6/` application, `lock_pay_born` in `Xv6/PipeBirth.lean:303` (the
  pipe lock — the only lock born after boot, hence the only "cancellable lock … released at reclaim" case β′'s registry
  must handle, `W8-design.md:424-425`); the other four hits (`IcacheTable.lean:223`, `IcacheBootTable.lean:155`,
  `SpecRelease.lean:14`, `SpecAcquire.lean:17`) are prose, and `PipeBirth.lean` is not among the 19 either.  Under
  (f2-ctx) the `p_j->lock` hop is "supplied at the 3 `wp_swtch` sites" (`:2533-2534`) — but the token transport those
  sites rely on is `ProofSwtch.lean`'s `kctx_move_*`, exactly the place where a chain must be concatenated across the
  handoff; a read-only check that never opens that file cannot say whether the hop is expressible.
  *Exact change.*  `:1184-1189`, §C W8 `:2538-2542`, and W8-design §3.4's pointer: the list is 21 files — add
  `Xv6/ProofSwtch.lean` (`kctx_move_in/out` ×5: the `swtch` payload transport, the (f2-ctx) hop site) and
  `Xv6/PipeBirth.lean` (`lock_pay_born`: the dynamic lock birth / reclaim case of the β′ registry); counts "`ctx_move`
  1 + `kctx_move_in/out` 6 (`ProofSwtch` 5, `ProofScheduler` 1), `lock_pay_born` 1 (`PipeBirth`)"; R-ctx's output
  table gains rows for the handoff (CHAINED via the `p->lock` hop or RESISTS) and for the walker ([R25.1] (c)).  S text.

## SUGGESTIONS

- **[R25.s1] Stale cite in the M1 text.**  `:1201` "START is unguarded from `.PDisk none`, `WeakEvInst.lean:488`" → the
  START arm is now `:502` (`pdiskProg :499`); `:552` already declares `:488` pre-W-DISK, but `:1201` is binding W5 text.
- **[R25.s2] Mark `Weak/SrvwmoXv6Adequacy.lean` NEW** at `:1203` (it does not exist; W5 CORE creates it), and
  `tools/tcb/expected.json` is the file's path (`:1141`, `:2556` say `tcb/expected.json`).
- **[R25.s3] Counts.**  `lkFresh` appears in 30 `Xv6/` files (plan `:1949` "29"); W8-β′'s "≤ 30" bound is right as a
  bound.  The `ctx_move`/`lock_pay_*` figures are in [R25.3].
- **[R25.s4] `utextDiscAt` is credible — say why in one clause.**  The verified branch's `userret` executes `fence.i`
  after the `satp` switch (`Xv6/KernelImage.lean:17614`, `0x8000609c`; `Xv6/SpecUserret.lean:6` "the icache sees the
  process image"), so "entries on proc j's executable user pages precede its owner's last `fence.i`" holds on every
  return to user mode after a migration; upstream xv6 has no such fence — the plan should name this as an image fact of
  the branch (it is the only `fence.i` in the image), since an xv6 expert will ask.
- **[R25.s5] W-DISK record: one wording.**  `:1532` "`Dres` = `DIdle`/`DStall` (`:271-273`)" → `:269-273` (the
  `inductive` opens at `:269`).  Cosmetic.
- **[R25.s6] The holding-race note's C11 remark.**  `notes/xv6-holding-race.md` §"Why it matters" item 1 is right but
  the plan's Q-HOLDING (c) could add that the SAME racy-read pattern exists at `holding+0x0` on `lk->locked` (C1 in the
  census table, `:2358-2360`), covered by `lockWordDiscAt`'s word clause — so the "fix xv6" option would have to touch
  both fields or drop the `holding()` call.

## Owner questions the plan is missing

None.  [R25.1] is the only finding that touches semantics, and per the OWNER RULE it is NOT a memory-model question:
RVWMO's chapter orders implicit page-table accesses only through SFENCE.VMA (FENCE does not order them); the privileged
spec requires the A/D update to be atomic with respect to other accesses to the PTE; the Sail model in this tree performs
the update as the exclusive pair `read_pte_exclusive`/`write_pte_conditional` (`MachCSL/WpPtWalk.lean:3-7,129-165`) and
the walk's read as a plain `Load PageTableEntry` (`:25-57`); Zifencei and the PMAs are silent.  Every form of the
export's PTE clause is FAITHFUL — it changes an INTERNAL predicate's statement and leaves the published quantifier and
conclusions unchanged — so it is plan text in the sound direction, REQUIRED of the plan, not put to the owner.  [R25.2]
and [R25.3] are proof-organisation and brief-completeness fixes (all options FAITHFUL).  The plan's RULED/REPORT
questions (Q-W8-feed `:2695-2743`, Q-HOLDING `:2744-2782`, Q-GFDEV-delta `:2783-2822`) keep their "Spec:" lines and the
2026-10-10 format.
