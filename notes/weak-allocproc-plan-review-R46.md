VERDICT: PROCEED WITH CHANGES

# R46 — the LOAD side of route P: does any reachable xv6 load reordering escape the replay?  ([OWN.121]; F-HH2-1)

Reviewer + design advisor (one-off, advisory: no proofs, no builds, no git/jj, no subagents), 2026-10-19.  Read: the
owner's question and rulings [OWN.106]–[OWN.122] (`~/dev/weak-orch/allocproc_revise3_extra.txt`), the route-P design
(`notes/weak-allocproc-routeP-design.md` §1, §3.2–3.4, §4–§6), plan rev 55 (top paragraph, REMAINING WORK),
`~/dev/weak-orch/parked/PROGRESS-P-hh2-1019.md` (P-W1–P-W4, export clauses 12/13, §DEVSTORD, §HEADHOP, §HEADHOP2,
F-HH2-1), `Weak/SbOrd.lean` (`srcGate :75`, `valGate :81`, `enbL :88`, `landG :105`, `waitedOn :170`, `mu :178`,
`HeadOrdRd :251`, `tgtW :446`, `blkLoad :942`, `noStuckP :1202`), `Weak/SbHeadHop.lean`/`SbHeadHop2.lean` (headers,
`headOrdRdOfTable :450`, `HoldZero :479`, `FrameQuiet :492`), `Weak/LitmusSbStuck2.lean` (l7/l8/l9), `Weak/SbKill.lean`
(§4 named inputs), `MachCSL/Lang.lean:1698-1716` (the four read arms), `MachCSL/TsoMem.lean:290-299` (`HRead`),
`:356-366` (`afterLoad`/`resetCoh`), `:491` (`fencePost`), `Xv6/AccessDiscipline.lean` (`lockWordDiscAt :362`,
`cpuStaticAt :368`, `lkCpuReadAt :384`, `ksFrameAt :1027`, the route-P twins `lkCpuReadAtP :1467`, `ksFrameAtP :1539`,
`xv6AccessDiscP :1547`), `Xv6/KernelImage.lean` (`holding` `0x80000bf2`–`0x80000c1c`, `mycpu` `0x8000195c`–`0x8000197a`,
`acquire` `0x80000c58`–`0x80000c94`, `release` `0x80000ce0`–`0x80000d0a`, `forkret+0x18` `0x800019c6`, `procdump`
`0x80002412`–), `Xv6/KernelRsv.lean` (the one `.racy` region `xv6IrefRacyR :96`), `Weak/SilSiteTab.lean:71-96` (the 18
sites), `notes/W10-6m-census.md`, `notes/W10-P0a-wfence.md` §3–§5, `Xv6/SpecProcdump.lean`, `Xv6/SpecForkret.lean`,
R45 §2.4/§7, `~/dev/weak-orch/allocproc_prog.txt:478-498` (lane positions: P-M4 DONE and HELD; P-W1–P-W4 merged).
Every size is an unverified estimate (ranges; MachCSL 6–10 h/k, Weak 4–8 h/k as in the plan); every spec mark is
w.r.t. riscv.cat / RVWMO / Sail / Zifencei / PMAs.  Note: `~/dev/xv6-riscv/kernel/kernel.asm` is a DIFFERENT build
(`holding` at `0x80000b82`, a `panicking` global); every instruction fact below is from `Xv6/KernelImage.lean`.

## 0. Summary — the answer, the escapes, the verdict

**The owner is right about RVWMO in general and the tree already has that half.**  An operational model of full
RVWMO needs (i) a store side — per-hart buffers with forwarding, landing in same-address + fence order — for W→R and
W→W reordering, and (ii) a load side for R→R reordering — either out-of-order satisfaction (a logical load buffer)
or, equivalently, loads satisfied at STALE per-location views — and (iii) promises for R→W reordering (load
buffering, LB).  MachCSL has had (ii) in the view form since the TSO days and still has it under P: a plain load
reads at ANY view `tvn ∈ [tv, ltop]` and raises only its read watermark `rv` and the FOREIGN-sourced coherence
floors, never the hart view `tv` (`Lang.lean:1708-1711`, `TsoMem.lean:356-361`) — exactly rules 2–3 per byte, with
`fence r,*` raising the floor to `rv` (`fencePost :491`) for rule 4.  Route P adds (i).  MachCSL-P lacks only (iii),
and **no RVWMO-consistent execution of THIS binary has an LB shape** (§2 row 2: every unlocked read is followed by a
branch on its value or a fence before any foreign-readable store — rules 11/4; the only stores that escape are the
hart's own stack frame at `holding+0x12`/`mycpu`).
**THIS proof needs no load buffer at all — not in the machine and not in the twin.**  The replay walks each row in
program order and reads the member's TOP; a load that RVWMO satisfied "early" (gmo-before an earlier-in-po load) is
reproduced by holding the competing store's LANDING back until the later-in-po read is realized (the `land` gate's
`readersDone`).  Same rf, same co, a different gmo witness — FAITHFUL for the quantifier.  Late landing replaces the
load buffer; the only place it can fail is when the EARLIER read of the pair is itself blocked — i.e. a racy read
whose GF source is a pending or unissued foreign store, which in xv6 is a census site (18 kernel pcs + 8 device
reads, `SilSiteTab.kSites`).  That finite table (`HeadOrdRd`, PROGRESS §HEADHOP2) IS the load-side analysis, and it
has exactly ONE open row of the load-buffer kind: **F-HH2-1**, `holding+0x12`.
**Escapes found (§3): F-HH2-1 only; nothing new.**  Checked: the 18 sites, the 8 device reads, user rows (no shared
memory), interrupt/trap/switch paths, `forkret`'s `first` (chained through fork's `release(&np->lock)`), `procdump`
(DEAD TEXT: no `jal <procdump>` in the image — its unlocked `p->state` reads are unreachable), and `panicked`/
`pr.locking` (absent from this image; panic paths end in `unreachable`).
**F-HH2-1 verdict: (a) — exempt `holding+0x12` like `ip->ref` ([OWN.112] pattern), 0.6–1.2k Weak, no new MachCSL
record** (§4): its member-side value fact is already an export twin (`lkCpuReadAtP :1467` quantifies over EVERY view);
(b) (a custody-aware measure) is the structurally nicer fix but needs a NEW per-load MachCSL footprint record for a
clause about other harts' UNREALIZED next loads — more serial-lane work for one site; (c) WEAKER.  Both (a) and (b)
need `HoldZero` (GF side), which this review sizes and routes ([R46.3]).
**Recommendation (§5–§6): (P), no load-side mechanism; the MachCSL lane may proceed past P-M4 with the [OWN.122]
switch NOW** — nothing load-side changes P-M5..P-M8; the two buffer-state records the per-site table needs
(frame-quiet, `lk->cpu`-quiet) are additive interpretation records queued after P-M8 like M12/M13.  (P+L) would push
the problem into W4-P's realization (a commutation of early-satisfied reads, the (R) rescheduling the owner
rejected for δ1), +3–6k; (M+L) would put a promise machine in the red branch for a freedom xv6 never uses, +10–25k.
Required changes [R46.1]–[R46.6] in §7; two owner questions in §8.

## 1. Spec first — the LOAD side of riscv.cat / RVWMO, what MachCSL-P does, what the replay does

Terms.  *gmo*: riscv.cat's global memory order.  *rf/co*: reads-from / coherence.  *Stale view*: a load returning
a write older than the latest landed one at its byte, allowed when no co-later write is visible at the hart's
view.  *Logical load buffer*: an operational device letting a later-in-po load be satisfied before an earlier one.
*LB (load buffering)*: a later-in-po STORE becoming visible before an earlier load is satisfied (needs promises).
*Head*: a row's next GF event in the walk; *blocked head*: one the gate rejects (`srcGate`/`valGate`: the member's
top ≠ GF's value); *late landing*: the walk's `land` gate holding a store back while a GF reader of the byte's
member-latest write is unrealized (`readersDone`).

| # | riscv.cat / RVWMO rule on loads | MachCSL-P as a MACHINE (`Lang.lean:1708`, `TsoMem.lean:356`, `:491`) | the replay (member `SbCand`, gate `SbOrd.enb`) | mark |
|---|---|---|---|---|
| L1 | load value axiom: a read returns a write gmo-before or po-before it, not overwritten before it in gmo (per byte) | `readFwd`: own pending byte, else the history at a view `tvn ∈ [tv, ltop]` | reads the member's TOP (forwarded or latest landed); the GF source is the top by the gate | FAITHFUL (quantifier); the member's gmo differs from GF's where GF had the read earlier |
| L2 | rules 2–3 (`[R];po-loc-no-w;[R]`, rsw/fri): two same-byte reads return co-nondecreasing writes unless an own write intervenes | per-byte `coh` floors raised by FOREIGN sources only, reset at own stores (`afterLoad`/`resetCoh`) | reads in po at the top: automatic | FAITHFUL |
| L3 | rule 4 with `pr` (`fence r,r`/`r,rw`/`rw,*`): earlier loads before later accesses | floor := `rv` (the read watermark) | po-respecting: automatic | FAITHFUL |
| L4 | rule 5: `.aq` read before everything po-later | the exclusive read sets `rv`/floor := top; xv6's only `.aq` is `acquire+0x1c`'s AMO read half | AMO reads `rmwLatest` (landed top, atomicity); H1 `aqOrd` | FAITHFUL (machine STRONGER only at the exclusive read's same-address drain, row 1 of the design) |
| L5 | R→R to DIFFERENT bytes, no fence/dep: UNORDERED (no rule) | stale views (`tv` is NOT raised by a load) | **late landing**: the overwriting landing waits for the earlier-in-po reader; the replay never uses stale views (member loads at `tvn = ltop`) | FAITHFUL; stuck only if the earlier read is a blocked head — the per-site table (§3) |
| L6 | R→W to different bytes, no dep/fence: UNORDERED (LB allowed) | NOT modelled (loads execute in program order, no promises) | the store is issued after the read is realized; harmless unless the store is WAITED ON while the read is blocked (F-HH2-1) | machine STRONGER; FAITHFUL for the quantifier: no reachable LB shape of this binary (§2 row 2) |
| L7 | rules 9–13 (addr/data/ctrl deps, `[M];addr;[M];po;[W]`) | none tracked (more permissive) | the member respects po, hence every dep; the emission's `dsCtl`/`dsLd` edges are used only in the progress hops (`wrHopOfCtl`, `diskWrHop`) | unchanged (theorem unaffected) |
| L8 | mixed size / misalignment: per byte | per byte (`readFwd`, `textAt4S`) | per byte | FAITHFUL (N10 caveat unchanged) |
| L9 | LR/SC reads | LR = exclusive read, drains overlapping own entries | no LR/SC in the image (`LockFacts.amoCensus`) | n/a (machine STRONGER, harmless) |
| L10 | loads vs I/O: ordered only by fence i/o bits (Sail drops them, D48), deps, rule 5, PMAs | MMIO loads at the event | fabric order (R3); **(R2″) [OWN.116]** I/O → later RAM READ | STRONGER (trusted platform text, removable with (R1): A4) |
| L11 | loads of DMA-written RAM: silent in RVWMO | device writes land at once | never pending; an unissued device write ⇒ device-row progress (`diskWrHop`, (R2′), `diskFabPo`) | device-model text (named `diskFabPo`), FAITHFUL to the model |
| L12 | a read whose GF source is a store its hart has NOT YET REACHED (cross-hart R→W freedom) | n/a | `blkLoad`'s unissued-source edge → the source row's head, through `waitedOn` (write) | FAITHFUL; the dual of F-HH2-1 (§4) |

Nothing here changes what riscv.cat/RVWMO/Sail say.  MachCSL-P is STRONGER than RVWMO on the load side in exactly one
way — it forbids LB — and that strength is never exercised by a GF of this binary.  **[R46.1]** puts this block into
the design's §1 and corrects §1's closing sentence ("stronger only where it already was" must add the LB line).

## 2. The owner's question, made concrete — the load-side shapes and how P's replay handles each

The question splits in two.  (A) *Why does a general RVWMO operational machine need load-side weakness?*  Because
with in-order loads from a single memory and only a store buffer you get TSO: message passing without an acquire
(hart 2 reads `flag = 1` then `data = old`) is unproducible, and RVWMO allows it (no rule orders two plain loads of
different bytes).  So a general machine needs either early load satisfaction or stale views (equivalent for R→R),
and promises for LB.  (B) *Does THIS proof need it?*  No: the proof does not run a general machine against unknown
programs — it REPLAYS a given riscv.cat-consistent graph GF of this image on the buffered twin, step by step, with a
gate.  The replay knows GF's rf and co; it only has to produce a member run with the same rf/co.  A load that GF
satisfied early is satisfied in program order in the member, and the member makes the VALUE come out the same by
not landing the competing store yet.  The load buffer is replaced by the landing gate.

| shape (GF) | xv6 instance | what the replay does | where it can fail | status / mark |
|---|---|---|---|---|
| 1 R→R early: `r1 <gmo r0`, `r0 <po r1`, different bytes | `holding+0x0` then `holding+0x12` (`SbStuck.l7`); `ilock+0xe` then `holding+0x0` (F-R45-1 `l4`); `holding+0x0` then `+0x12` reading stale `lk->cpu` (F-P-W3-1 `l5`) | realize `r0` at the top, then `r1` at the top; the write `w1'` co-after `r1`'s source does not land until `r1` is realized (`readersDone`) | only if `r0` is BLOCKED (its source pending/unissued) and the held-back landing is what would unblock it — a cycle through a racy head | `l4`: cured by `rdX` [OWN.112]; `l7`: no cycle (`l7R1Idle`, the waited-on measure); `l5`: cured by the value gate (F-P-W3-1 (a)); FAITHFUL |
| 2 R→W early (LB): `w1 <gmo r0`, `r0 <po w1` | **none foreign-readable**: `holding+0x0 → bnez` (rule 11 orders every later write: `holding0CtrlNext`), `main+0x16 → fence r,rw` (`main16FenceNext`), `ilock+0xe`/`iunlock+0x1c → blez` (next instruction), vdi ×4 → branch (`vdiShape`), PTE ×7 → branch (`ptePctrlAlu`); the ONLY stores a racy read can precede in gmo are the hart's own frame: `holding+0x12`'s `mv s1,a5; jal mycpu` → `mycpu`'s `sd ra,8(sp); sd s0,0(sp)` (`0x8000195e/60`) and `ismapped+0x10`'s return path | the store is issued only after the read is realized | the frame stores are counted as `waitedOn` (every write is, `SbOrd.lean:171`), so a blocked `holding+0x12` cannot show descent — **F-HH2-1** | FAITHFUL for the quantifier (no cross-hart LB: no other hart reads a live frame — stack custody); the member and MachCSL-P are STRONGER (no LB), harmless |
| 3 same-byte coherence (CoRR/CoRW/CoWR/CoWW) | everywhere | member co at each byte is a GF-co PREFIX (`PInv.pfx`), reads at the top | — | PROVED (P-W2/P-W3); FAITHFUL |
| 4 forwarding then early read (W→R own, then R→R) | `release+0x12 sd zero,16(s1)` then `pop_off`'s per-cpu loads; `acquire+0x28` then the caller's loads | `readFwd` for the own byte; late landing for the other | — | FAITHFUL |
| 5 `.aq` AMO read vs later loads (rule 5) | every acquire | AMO at the landed top, lands at once; later reads after it | — | H1 PROVED; FAITHFUL |
| 6 a failed acquire reading a PENDING release (reads 1) | every contended lock (Litmus 1, cross-spin) | the AMO reads the landed top = 1, writes 1; the release lands later | — | PROVED (`l1MemberSb`); FAITHFUL; δ1 unnecessary [OWN.114] |
| 7 a read whose source is a store its row has not yet ISSUED (L12) | `holding+0x0` reading an unissued swap (`l7`); a racy read reading an unissued `release+0x1a` | edge head → source row's head through `waitedOn` (the source is a write) | the same measure limitation as row 2 if the blocked head's row has early waited-on writes | covered by `blkLoad`; FAITHFUL |
| 8 loads of DMA data / device reads of driver data | `virtio_disk_intr` ×4; the 8 `DRead` nodes | device writes land at once; driver stores landed by the `fence iorw,iorw` before NOTIFY → START (`drainLanded`) | device-row heads blocked on pending driver stores — WrHop PROVED (`diskWrHop`), A2 needs "never blocked" (`DiskDesc`) | named, dischargeable (§3) |
| 9 user-mode loads | all user rows | sources are the process's own writes (own hart, or chained through `p->lock` on migration), the kernel's writes on its behalf (`copyout` in its own syscall; `fork`/`exec` by the parent → chained through `np->lock`), or `kfree`'s fill (chained through `kmem.lock`) | never blocked (no shared memory between processes) | FAITHFUL; rests on the user-tier custody at the realized prefix ([R46.4]) |
| 10 trap / context-switch loads | `uservec`→`userret` trapframe, `swtch`'s `p->context`, `scheduler` | written by the previous hart po-before its `release(&p->lock)` (`fence rw,w` ⇒ epoch-before the release store ⇒ landed first); the next hart's acquire reads the landed release | never blocked | FAITHFUL |

So: the load side is absorbed by late landing everywhere except at a blocked head, and a blocked head is a racy
census site.  The complete load-side obligation of route P is `HeadOrdRd` at those sites — a finite table whose
rows are static hops (rules 4/5/11/13 as the emission carries them), "never blocked" (sources landed by custody), or
an exemption.  That is what §HEADHOP2 built; §3 re-derives it.

## 3. Escape hunt — every reachable shape where a load reordering could stall or diverge the replay

Method.  A head is blocked iff the member's top ≠ GF's value at some byte (value gate), i.e. GF's source is a
pending or unissued foreign store (own stores forward; landed sources make the top GF's value because the
co-successor's landing waits).  A chained read's source is landed when the read becomes the head: the chain's hop
AMO is realized only when its source (the release) is member-latest = landed, the release's `fence rw,w` puts every
earlier store of the releaser in an earlier epoch (`landOk`'s oldest-epoch clause), so they landed first; the
`started` hop likewise (`main+0xac` fence); device writes land at once.  So blocked heads are reads of EXEMPT-class
or disk-written bytes — the census set (`SilSiteTab.kSites`, 18 pcs; 8 `DRead` nodes) — **given** that non-census
loads are chained; that completeness claim is today folded into the named transport (T) and is made explicit by
[R46.4].  For each blocked site the walk needs (A1) every later WAITED-ON write gmo-after the head and (A2) every
later waited-on pure read past an ordering point (`headOrdRdOf`), or "never blocked", or an exemption.

| site (image pc) | blocked possible? | load→store before the branch? | (A1) | (A2) | verdict |
|---|---|---|---|---|---|
| `holding+0x0` from `acquire+0x12` (`0x80000bf2`, `lw a5,0(a0)`) | yes: zero arm (GF 0 = a pending release, top 1), nonzero arm (GF 1 = an unissued swap, top 0) | no: `bnez` is next (`0x80000bf4`) | rule 11 via `dsCtl` (`wrHopOfCtl` + `ctlOfPsites`) | zero arm: next event is the `.aq` AMO (`aqNextA2`); nonzero arm: the window to the AMO holds `holding+0x12` (quiet by `LkCpuQuiet`: no pending `lk->cpu` store while the landed byte is 0) and own-frame reloads (quiet by `FrameQuiet`), then `bnez a0` → AMO or panic (excluded by `HoldZero`) | PROVED mod (T), `LkCpuQuiet`, `FrameQuiet`, `HoldZero` — no escape |
| `holding+0x0` from `release+0xc`/`sched+0x14` (caller holds) | no: top = 1 = GF (the holder's AMO landed, spinners write 1, nobody writes 0) | — | — | — | `HeldPin` (named, realized-prefix lock fact) — no escape |
| **`holding+0x12`** (`0x80000c04`, `ld a5,16(a0)`) from `acquire` | **yes**: the holder z's `sd a0,16(s1)` (`acquire+0x28`) pending, GF reads it, top is 0 or an older pointer | **YES**: `mv s1,a5; jal mycpu` → `mycpu+0x2/+0x4` `sd ra`/`sd s0` before `seqz`/`bnez` | **FALSE** for the frame stores (no dep, no fence; pin `PResidue`) | window = `mycpu`'s and `holding`'s frame reloads (quiet) → `bnez a0` → AMO | **F-HH2-1** — the one escape; fix §4 |
| `holding+0x12` from `release`/`sched` | no: the holder's own `sd a0,16` forwards or is landed (own source) | — | — | — | no escape |
| `main+0x16` (`started`) | yes (GF 1, hart 0's `main+0xb0` pending) | no: `fence r,rw` is next | rule 4 (`main16FenceNext`) | rule 4 | PROVED mod (T) |
| `ilock+0xe`, `iunlock+0x1c` (`ip->ref`) | exempt (`rdX`, [OWN.112]) | no: `blez` next | — | — | exempt; value by `IrefTop`/`IrefGF` ([OWN.117] M12-a/b) |
| PTE ×9 (`walk+0x32` … `uvmclear+0x10`) | no: custody — the table's writers are the owning process's hart (or the walker on it); hand-offs through `p->lock`; the reaper reads a ZOMBIE's table after `wait`'s acquire | 7 × ALU only to the branch (`ptePctrlAlu`); `ismapped+0x10` returns the value (its caller branches after `ld ra`/`ld s0` reloads — loads, no stores); `uvmclear+0x10` data-dep into its `sd` (rule 10) | ctrl / data | NOT static — must be never blocked | Q-6M-PTE (a) ⇒ `SrcLanded` ⇒ passes the gate — no escape |
| `virtio_disk_intr+0x36`/`+0x82` (`used->idx`) GF ≠ `used_idx` | yes (waits for the device row's idx write) | no: `beq`/`bne` next | `fenceNextHop` (vdi+0x3e `fence iorw,iorw`) | same | PROVED mod (T) |
| vdi+0x36 taken / vdi+0x82 fall-through (GF = `used_idx`) | no (`VirtioIdx`: device idx writes consecutive, `0 ≤ idx − used_idx ≤ NUM`, realized idx reads monotone ⇒ top = GF) | — | — | NOT static | named `VirtioIdx` — no escape once discharged |
| vdi+0x4e (`ring[i].id`), vdi+0x5a (`info[id].status`) | no (`VirtioDesc`: the source is the device's completion write, `devStOrd`-before the idx the hart already read; landed) | no (`wrHopOfCtlR` through the `lbu`) | ctrl | NOT static | named `VirtioDesc` — no escape |
| the 8 device `DRead` nodes | blocked while the driver's descriptor/avail stores are pending | n/a (device program) | `diskWrHop` PROVED (rule 13 `dsLd`) | NOT static (disk loads carry no deps) | `DiskDesc`: the source is a driver store po-before its REALIZED `fence iorw,iorw` ⇒ landed (`drainLanded`, a new `PInv` clause) — no escape |
| `forkret+0x18` (`lw first.1`, `0x800019c6`) | no: the writer (the first process, `0x800019d6`) is po-before its `fork`'s `release(&np->lock)`; the reader is resumed by a scheduler acquire of that lock | `beqz` next | — | — | chained (not a census site); the Xv6 proof decides the branch by a token (`SpecForkret.lean:33`) — consistent |
| `procdump+0x70` (`lw p->state` unlocked, `0x80002482`) | would be (a foreign `p->state` store under `p->lock` pending) | `beqz` next; then `printk`'s `acquire(&pr.lock)` → `holding+0x0` on `pr.lock` before any ordering point — (A2) would FAIL | — | — | **DEAD TEXT**: no `jal <procdump>` in `Xv6/KernelImage.lean`; its contract is stated unsatisfiable (`SpecProcdump.lean:45`); unreachable — no escape (record it, [R46.s3]) |
| `panicked` / `pr.locking` readers (`uartputc*`, `printf`) | — | — | — | — | absent from this image (panic → `unreachable 0x80000860`); no escape |
| user rows; `uservec`/`userret`/`swtch`; `kfree`'s fill; `log` commit reads; `bio`; `pipe*`; `filewrite`'s `f->type`; `wakeup`/`sleep`; `either_copyout` | no (chained: §2 rows 9–10; `copyout` goes through the PTE sites above) | — | — | — | no escape |

**Finding re-derivation, F-HH2-1 (confirmed, the only one).**  At a reachable walk state: z won the swap on `L`
(landed at issue), z's `sd a0,16(s1)` is pending (no fence until z's release), x's `holding+0x0` realized (top 1 = GF
1), x's head `r12 = holding+0x12` has GF source = z's pending store ⇒ top ≠ GF ⇒ blocked.  `mu (.hd x)` is the least
gmo position of x's unrealized waited-on events; `mycpu`'s `sd ra` is a write, hence waited on (`SbOrd.lean:171`
`gisW`), and RVWMO lets it sit gmo-before z's store (no rule orders `ld` → unrelated `sd`), so `mu (.hd x) ≤ gpos (sd
ra) < gpos (z's store) = mu (.ld z _)` and the (E5) edge does not descend.  Nothing is stuck (z's entry is landable:
its co-predecessor's readers are `holding+0x12` reads, all realized or not waited on); the MEASURE is too coarse.
Classification: the dual of row 2 — a load-side artifact of the proof, FAITHFUL to fix either way.
**Are there more of its kind?**  A blocked racy read followed by a store before the branch on its value: among the 18
only `holding+0x12` (frames) and `ismapped+0x10` (never blocked, and its path to the caller's branch has loads
only); among the device reads none (device programs store only after the fabric point).  The (A2) kind (a blocked
racy read followed by a WAITED-ON read before an ordering point): `holding+0x0`'s nonzero arm (quiet window — handled)
and `procdump+0x70` (dead text).  **No new escape.**

**Where the hunt's completeness rests** (all FAITHFUL program-layer facts, WEAKER only while named): (i) "a blocked
head is a census-site load" = non-census loads' sources are landed — chain at the realized prefix + GF row
structure for unissued sources (the kill's `l2ClaimP`, row 6n) → [R46.4]; (ii) the per-site named inputs:
`HoldZero`, `FrameQuiet`, `LkCpuQuiet`, `HeldPin`, `VirtioIdx`, `VirtioDesc`, `DiskDesc`, PTE custody, (T); (iii) the
device model (`diskFabPo`, `usedElemGateOk`).  None is a load-buffer question; all were already named before R46
except that §HEADHOP2's table lives only in a PROGRESS file → [R46.6].

## 4. F-HH2-1 — the verdict: (a), and why not (b)

Spec first: RVWMO orders a plain load before a po-later store only by rules 4 (fence), 9–11 (addr/data/ctrl into the
write) and 13; `holding+0x12`'s loaded value reaches `mycpu`'s frame stores by no dependency, so GF may put them
gmo-before it.  All three options keep the quantifier; they differ in where the proof pays.

**(a) Exempt `holding+0x12` (RECOMMENDED; w3's recommendation).**  A third `rdX` pc (`ipRefPc`-style predicate →
`exemptPc`): the member reads the top of `[L+16, L+24)` (own forwarded `sd zero` or the latest landed value), GF reads
its source; `valEqX`'s clause at this pc: `memberWord ≠ cpuAddr x ∧ gfWord ≠ cpuAddr x`; the taint arm runs from
`holding+0x12` through `mv s1,a5; jal mycpu` (`mycpu` `0x8000195c`–`0x8000197a` never touches `s1`; its frame stores
and reloads carry untainted registers) to `sub a0,s1,a0; seqz a0,a0` (`holding+0x1a/+0x1e`), where both sides give 0
— the taint dies by the value lemma, as `ilock`'s dies at `blez`.  Needs: the taint walker to cross one call (if
`taintDiesB` stops at `jal`, +0.1–0.3k) and the Sail meaning of a 14-instruction path (O-P-W2-a's open item, larger
here).  Value interfaces: member side — **already an export twin**: `lkCpuReadAtP` (`AccessDiscipline.lean:1467`)
says a non-holder `c` reading `lk->cpu` at ANY view `tvn` from an initial `v0 ≠ cpuAddr c` never obtains `cpuAddr c`;
applied at `tvn = top` via P-W6's state map, with "x is not `st`'s holder" read off the merged lock-word history (x's
last own write to `L` is a release — x's own events are realized); no new MachCSL record.  GF side — `HoldZero`
([R46.3], shared with (b)).  **Cost 0.6–1.2k Weak, 5–10 h** (rdX/valEqX glue 0.2–0.4k, taint arm + Sail meaning
0.3–0.6k, member-side fact 0.1–0.2k).  FAITHFUL.  An xv6 expert reads: "at three unlocked sanity reads (`ip->ref` ×2,
`holding`'s `lk->cpu` compare) the replay may see a different value than the graph did; both values give the same
branch."  Risk: M (the pattern exists; the call-crossing taint is new).
**(b) A custody-aware measure.**  Replace `waitedOn`'s write arm `gisW G m` (`SbOrd.lean:171`) by "a write to a BUSY
byte", `busy w a := (∃ pending entry writing a) ∨ (∃ AMO head writing a) ∨ (∃ load head whose GF source byte is a)`
(the third disjunct is what `blkLoad`'s unissued-source edge needs; `tgtW :446` gains the busy hypothesis, available
at both call sites `blkLand`/`blkAmo`; `tgtEv`, `HeadOrdRd`, `descent` unchanged).  Then `mycpu`'s frame stores are
waited on only if some OTHER row's head load reads x's live frame — and `FrameQuiet` (`SbHeadHop2.lean:492`) must gain
exactly that clause.  Its two existing clauses are realized-level (pending entries) or label-level (an AMO head's
footprint is a lock word); the new one is about another hart's UNREALIZED next load's footprint, which no current
export gives (`ksFrameAtP :1539` constrains landed ENTRIES; `chainOkAtP` constrains observed entries AFTER the load,
and a chained live-frame entry is not excluded by it).  Discharge needs a NEW per-load MachCSL footprint record ("a
load's footprint avoids other harts' live frames", paid at the load leaf from the static regions + the X1
page-provenance record) plus a one-step-lookahead glue in P-W6 (MachCSL-P never blocks a plain load, so the
successor state is reachable).  **Cost 0.3–0.7k Weak (3–7 h) + 0.5–1.0k MachCSL (4–10 h, serial lane) + 0.3–0.5k
P-W6 glue; total 1.1–2.2k.**  FAITHFUL; structurally general (covers any future site of this kind); more named
surface and more serial-lane work for ONE site.  w3's "L–XL" read of the SbOrd edit is, by my reading of
`waitedOn`/`mu`/`tgtW`, an over-estimate — the MachCSL record is the real cost.  Keep as the documented alternative.
**(c) Name `noStuckP`.**  WEAKER (a progress premise in the header); 0.  Rejected by the [OWN.100] standard.

**Shared by (a) and (b): `HoldZero`** (`SbHeadHop2.lean:479`): every `holding+0x12` read inside `acquire(L)` by row x
has GF value `≠ cpuAddr x`.  Why it is true: x's po-last own write to `[L+16)` is its last release's `sd zero`
(no recursive acquire — the MachCSL proof's precondition), every co-later write is another hart u's `sd a0,16(s1)`
with `a0 = mycpu() = cpuAddr u` (u ≠ x) or a 0, and `cpus` pointers are distinct; CoWR puts GF's source co-at-or-after
x's own write.  Why it needs work: for PENDING or UNISSUED writer rows the value is a GF label whose relation to
`cpuAddr u` comes from the emission's register state (`a0 = &cpus[tp]`, `mycpu+0x8` `mv a5,tp`) and the invariant
`tp = row` at kernel pcs (boot `start`; after user mode, `uservec`'s reload of `kernel_hartid` written by the same
hart in `prepare_return` — the [OWN.77]/[OWN.87] trapframe custody; `AxSpinT2a.lean:616` already has the `mycpu`
value lemma at `tp = hartId c`); `kfree`'s 1-fill and recycled pages are excluded by restricting to LIVE published
locks (`Lk`); for REALIZED writes `lockWordDiscAtP`/`lkCpuReadAtP` via P-W6.  **0.6–1.2k Weak, 4–10 h; no MachCSL
record** (the "not holder" fact is x's own realized history).  [R46.3] makes it a sized row.

## 5. Options — (P), (P+L), (M+L)

| option | what an xv6 expert reads in the final theorem | spec mark | lines / worker-hours | risk | interaction with [OWN.122] |
|---|---|---|---|---|---|
| **(P) keep P, no load-side mechanism; per-site fixes** (F-HH2-1 (a); `HoldZero`; the named inputs of §3 discharged as planned) | "The proof machine buffers stores exactly as RVWMO allows and executes loads in program order against the latest value; every RVWMO execution of this kernel is still covered because the proof delays the competing store instead of reordering the load, and at three unlocked sanity reads it shows the value does not matter." | FAITHFUL (quantifier); machine STRONGER only by forbidding LB, unused by xv6 | load-side residue in total ≈ **3.0–6.3k, 22–50 h**: (a) 0.6–1.2k W; `HoldZero` 0.6–1.2k W; `FrameQuiet`/`LkCpuQuiet` MachCSL records 0.5–1.1k M (after P-M8) + 0.2–0.4k W glue; `HeldPin` 0.1–0.3k W; `VirtioIdx`/`VirtioDesc`/`DiskDesc` + `drainLanded` 0.7–1.5k W; PTE custody 0.3–0.6k W (already in P-W3's row); of this ≈ 1.5–3k is already carried by rows P-W3/P-W6/6m → **net new ≈ +1.5–3.3k, +10–25 h** | M (the per-site table is finite and mostly proved mod (T)) | none on P-M5..P-M8; two additive records queued after P-M8; **proceed now** |
| **(P+L) load side in the twin only** (a blocked head is realized EARLY with GF's value — a "satisfied-early" read or a generalized `rdX` with the true value; no MachCSL change) | "The replay lets a load take its value from a store that has not yet reached memory, then shows the machine could have executed the load a little later." | FAITHFUL, but the member is no longer a MachCSL-P run step for step: W4-P (P-W6) must REORDER — a commutation lemma per early read (the (R) rescheduling of [OWN.103], rejected for δ1) | **+3–6k Weak, 25–50 h** on top of (P)'s residue minus `HeadOrdRd` (−0.5–1k) | M−/L (the commutation past intermediate steps — frame stores, CSR ops — is a new design; the value interfaces (`HoldZero`) are NOT saved: lockstep needs GF's branch) | none on the MachCSL lane; P-W6 doubles |
| **(M+L) load side in MachCSL** (loads satisfied from unlanded foreign stores / promises; or an out-of-order load unit in the registered machine) | "The proof machine can execute loads out of order like real hardware." | machine closer to RVWMO (adds LB); theorem UNCHANGED in meaning — LB is never reachable for this binary | **+10–25k, 80–200 h**: the WP load rules return values no history holds (breaks the merged-history ghost, §2.6 of the design); every load lemma re-proved (`memModel_read_*`, `read_cases*`, 1,689 call sites' side conditions), registered roots re-audited again | L (a promise machine under Iris is research, not engineering) | would have to go INTO the red branch — 2–4× its duration — for nothing the quantifier needs |

The replay's one genuine use of load-side freedom is exemption (`rdX`): a value-insensitive read replayed with a
different value.  That is a per-site device, not a buffer; it is what (a) extends by one pc.

## 6. Recommendation; the MachCSL lane

**(P).  F-HH2-1 → (a).  No load buffer, in the twin or in MachCSL.**  The MachCSL lane **may proceed past P-M4 with
the [OWN.122] switch NOW**: nothing in §1–§5 touches P-M5 (contexts/hops), P-M6 (locks), P-M7 (rules), P-M8
(fallout); the two buffer-state records the per-site table needs — (r1) frame-quiet `∀ j a, ksLiveFrameAtP σ j a → ∀
i ≠ j, ∀ e ∈ σ.sb i, ¬ e.hits a`; (r2) `LkCpuQuiet` in MachCSL form (PROGRESS §HEADHOP (a2-lkcpu)) — are
state-interpretation records on the route-P state, additive, queued after P-M8 beside M12-a/b and M13 ([OWN.117]/
[OWN.118]); under (a) NO "not-holder" record and NO per-load footprint record is needed.  Weak lane now: (a) + the
`busy`-free `SbOrd` as is; `HoldZero` next (it unblocks `holding+0x0`'s nonzero arm too); `drainLanded` + `DiskDesc`;
[R46.4]'s boundary lemma.

## 7. REQUIRED changes [R46.n] (to the design note / plan rev 56), then suggestions

* **[R46.1]** Design §1: add the LOAD-SIDE block (§1 table above, rows L1–L12, with marks) and correct the closing
  sentence: "the machine stays STRONGER than RVWMO only where it already was (the exclusive read's drain) **and on
  the load side by forbidding load→store (LB) reordering — harmless for the quantifier: no RVWMO-consistent GF of
  this binary has an LB shape (census [R46.s1])**"; record Q-LOADBUF's answer in the plan's top paragraph and §D:
  no load buffer; the replay's late landing replaces it; MachCSL's stale views are present but unused by the replay
  (member loads at `tvn = ltop`).
* **[R46.2]** F-HH2-1 = **(a)**: a third exempt pc `holding+0x12` (`0x80000c04`) — `rdX` arm, `valEqX` clause
  `memberWord ≠ cpuAddr x ∧ gfWord ≠ cpuAddr x`, taint arm `holding+0x12 → holding+0x1e` across `jal mycpu` (static
  facts by `decide +kernel`: `mycpu` writes no callee-saved register; the frame stores carry `ra`/`s0` only), member
  side from `lkCpuReadAtP` at the top via P-W6 with "x not the holder" from x's realized history; 0.6–1.2k Weak,
  5–10 h; row P-W3's residue.  (b) recorded as the alternative with its MachCSL footprint record; (c) rejected.
* **[R46.3]** `HoldZero` becomes a sized P-W3-residue row (0.6–1.2k Weak, 4–10 h) with the discharge path of §4:
  realized writes via `lockWordDiscAtP`/`lkCpuReadAtP` (P-W6); pending/unissued writes via the emission's `a0 =
  &cpus[tp]` at `acquire+0x28` and the `tp = row` invariant at kernel pcs (boot + trapframe `kernel_hartid` custody
  [OWN.77]/[OWN.87]; reuse `AxSpinT2a`'s `mycpu` value lemma); `Lk` = live published locks; no MachCSL record.
* **[R46.4]** State the completeness boundary as its own item `blockedIsCensus` (P-W3/P-W6, 0.5–1.0k Weak, 4–8 h):
  "a plain-load head that is not a census site passes the value gate" — own source ⇒ forwarded; chained source ⇒
  the hop AMO realized ⇒ release landed ⇒ epoch ⇒ landed (`srcGateOfLanded`/`valGateOfLanded`); device source ⇒
  landed at issue; an unissued foreign source is excluded by rules 4–5 against the row's realized acquire + the
  lock discipline of the GF rows (`l2ClaimP`, row 6n).  Inputs named explicitly (today hidden inside (T)).
* **[R46.5]** Plan: the MachCSL lane proceeds past P-M4 with the switch now; queue (r1) frame-quiet and (r2)
  `LkCpuQuiet` as additive records after P-M8 (0.5–1.1k MachCSL, 4–10 h) next to M12-a/b and M13; no load-side
  item enters the red branch.
* **[R46.6]** Design §3.4 H3 row: replace by §HEADHOP2's per-site table (columns blocked?/A1/A2/named input); correct
  "`virtio_disk_intr`: never blocked" (false on vdi+0x36's fall-through and vdi+0x82's back edge — legitimately
  blocked, covered by `fenceNextHop`); add `drainLanded` as a `PInv` clause (0.1–0.3k) for `DiskDesc` and PTE
  custody; list (T) once as "label↔pc transport (P-W6)".

Suggestions.  **[R46.s1]** a `decide +kernel` leaf "LB-freedom unused": for each of the 18 census pcs the
instruction path to its certified branch contains no store, except `holding+0x12` (own frames) and `ismapped+0x10`
(return path) — `holding0CtrlNext`, `main16FenceNext`, `vdiShape`, `ptePctrlAlu` exist; add `ilock+0xe`/
`iunlock+0x1c` (`blez` next) and the two exceptions as explicit statements; 0.05–0.15k.  **[R46.s2]** note in the
design that `HRead`'s stale-view freedom (`tv` never raised by a load) is RVWMO's rules 2–3 in view form and is left
unused by the replay — it stays for the Xv6 proofs.  **[R46.s3]** census notes: `procdump` has no call site in the
image (dead text; its contract is stated unsatisfiable, `SpecProcdump.lean:45`); `forkret+0x18`'s `first` read is
chained through fork's `release(&np->lock)`; this image has no `panicked`/`pr.locking`.  **[R46.s4]** the 12 named
inputs of §3 get one table in the plan (owner, size, status) so the status reports can tick them.

## 8. Owner questions (owner format; two)

### Q-R46-LOADSIDE — does route P need a load buffer (in the twin or in MachCSL)?

*Plain-language issue.*  RVWMO lets hardware reorder a hart's loads: a later load may be satisfied before an
earlier one (when they touch different addresses and nothing fences them), and a later store may even become
visible before an earlier load is satisfied.  Any general machine model of RVWMO must therefore have a load-side
mechanism besides the store buffer — the owner's intuition.  Our proof does not run a general machine: it replays
one known execution graph of this kernel at a time on the buffered proof machine, step by step.  It handles the
reordered-load case by DELAYING the competing store instead of reordering the load: the two loads run in program
order, and the value the "early" load would have seen is still the latest value because the store that would
have overwritten it has not been let through yet.  The result has the same reads-from and coherence relations as
the hardware execution — the only thing that differs is the bookkeeping order, which the theorem does not speak
of.  This trick fails only when the earlier load is itself waiting for a store that has not arrived — an unlocked
("racy") read — and xv6 has 18 such read instructions (plus 8 device reads); each is handled by a static argument
(the next instruction is a branch on the value or a fence), by showing the read can never be waiting, or by
showing its value does not matter.  One of the 18 (`holding`'s `lk->cpu` read) is the open item Q-R46-HH2.
*Tiny example.*  Hart z takes lock `L` (`amoswap.aq`) and then writes its own cpu pointer into `L->cpu`; the write
sits in z's store buffer.  Hart y, trying to take `L`, runs `holding`: it reads `L->locked` and sees 1 (z's swap),
then reads `L->cpu` and sees the OLD value 0 — on hardware, because the second load was satisfied before z's write
arrived.  The replay: y's first read waits until z's swap is replayed; y's second read then returns 0 simply
because z's write has not landed yet.  Same values, same reads-from, loads in program order.
*Terms.*  *Load buffer*: a modelling device letting a later load be satisfied before an earlier one.  *Store
buffer / landing*: a store waits privately in its hart and LANDS (becomes visible to all) later.  *Replay*: the
proof's step-by-step construction of a run of the proof machine from a given execution graph.  *Blocked read*: a
read the replay cannot take yet because the store it must return has not landed.  *Exempt read*: a read the replay
takes with a different value than the graph, allowed when both values give the same branch.
*Options.*  **(P) No load buffer; keep the replay as designed, with the per-site fixes.**  Reads: "the proof
machine buffers stores exactly as RVWMO allows; loads run in order and read the latest value; every RVWMO execution
of this kernel is still covered, because the proof delays the competing store instead of reordering the load, and
at three unlocked sanity reads it shows the value does not matter."  FAITHFUL (the quantifier is unchanged; the
machine is stronger than RVWMO only by forbidding a reordering xv6 never exhibits).  Cost: the load-side residue
already largely in the plan, ≈ 3.0–6.3k / 22–50 h in total, of which ≈ +1.5–3.3k / +10–25 h is new (F-HH2-1 (a),
`HoldZero`, two small MachCSL records after P-M8).  **(P+L) A load-side mechanism in the twin only** (the replay may
take a blocked read early with the graph's value and later show the machine could have done the load a bit
later).  Reads: "the replay lets a load take its value from a store that has not reached memory yet, then
re-sequences the run."  FAITHFUL, but the re-sequencing is the rescheduling the owner rejected for δ1
([OWN.103]); cost +3–6k Weak / 25–50 h, risk M−/L; nothing saved on the per-site facts.  **(M+L) Out-of-order or
promised loads in the proof machine itself.**  Reads: "the proof machine executes loads out of order like real
hardware."  Machine closer to RVWMO, theorem unchanged in meaning; cost +10–25k / 80–200 h inside the red branch,
risk L (promises under the Iris program logic break the rule that every load returns a value some store already
made).  **Recommendation: (P).**

### Q-R46-HH2 — the one open load-side site: `holding`'s `lk->cpu` read (F-HH2-1)

*Plain-language issue.*  In `acquire`, xv6 first calls `holding(lk)` to detect a double acquire: it reads
`lk->locked` and, if it is 1, reads `lk->cpu` and compares it with `mycpu()`.  That second read is unlocked and
may need a value another hart has written but not yet landed; the replay then waits for that landing.  Nothing
prevents the landing, but the proof's PROGRESS bookkeeping — a count that must strictly decrease at every wait —
treats every upcoming store of the waiting hart as something others might be waiting for, and RVWMO lets the
hart's next stores (two pushes onto its own stack inside `mycpu`) sit before the blocked read in the global order,
so the count cannot be shown to decrease.  A proof artifact, not a real stall.
*Tiny example.*  Hart z holds `L` and its write `L->cpu = &cpus[z]` is still in z's buffer.  Hart x enters
`acquire(L)`: `holding` reads `L->locked` = 1, then must read `L->cpu`; the graph says that read returns z's buffered
pointer, so the replay must wait for z's write to land.  Meanwhile x's next instructions are `mycpu`'s `sd ra,8(sp)`,
`sd s0,0(sp)` — private stack pushes nobody else reads — and the global order may place them before x's blocked
read.
*Terms.*  *Measure*: the decreasing count the progress proof uses.  *Waited-on event*: an event the measure counts
because some other wait could pass through it.  *Exempt read*: see above; *taint*: running the hart with a
register that differs between the two runs until the difference is dead (here: at the `seqz` that makes the
compare 0 on both sides, since neither value is x's own pointer).  *Stack custody*: no hart touches another hart's
live stack frame.
*Options.*  **(a) Exempt the read** (as the two `ip->ref` reads are): the replay reads whatever is there (0 or
another hart's pointer), the graph reads z's pointer; both differ from x's own pointer, so `holding` returns 0 in
both runs.  Reads: "at three unlocked sanity reads the replay may see a different value than the graph; the
outcome of the check is the same."  FAITHFUL.  Cost 0.6–1.2k Weak / 5–10 h; no new MachCSL record (the "a
non-holder never reads its own pointer" fact is already an export twin, `lkCpuReadAtP`); plus the shared `HoldZero`
fact ([R46.3], needed by every option).  **(b) Refine the bookkeeping** so a store counts as waited-on only when
some hart could actually wait on it (another hart's pending write, a lock-taking AMO, or a next load of the same
byte).  Reads: "the proof's progress argument knows that private stack stores are nobody's business."  FAITHFUL
and general, but the clause about other harts' NEXT loads needs a new per-load MachCSL record on the serial lane:
0.3–0.7k Weak + 0.5–1.0k MachCSL + 0.3–0.5k glue, 1.1–2.2k / 9–21 h.  **(c) Assume progress** (name `noStuckP`).
Reads: "the theorem assumes the replay never gets stuck."  WEAKER; 0.  **Recommendation: (a); keep (b) on file for
a second site of this kind, none found.**
