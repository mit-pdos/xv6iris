> **COORDINATOR DECISIONS (Sept 24 2026):** (1) shared buffer lemmas go in a new definitional
> `Xv6/BlkmapBuf.lean`, landed FIRST by its own agent; (2) the SpecBalloc / SpecIget gates are
> satisfied (both committed with wave 1, c19021022); (3) ialloc restates `iu_log_write` as Rocq does;
> (4) the listed cleanups are approved (record each in the file header). NAMING: prefix every helper
> lemma with the function's name (`bmap_…`, `ialloc_…`, `itrunc_…`) — wave 1 hit root-build clashes
> from generic prefixes (`il_*` vs ProofInitlog).

# Brief: wave 2 — bmap (+ bmap_noalloc), ialloc, itrunc

Read notes/briefs/fs0_common.md and notes/briefs/fs1_leaves.md first. Their rules apply
unchanged:
- build only your own modules (`timeout 1800 lake build Xv6.<Module>`) and never run a bare
  `lake build`;
- no edits to existing files (report the exact change instead), no Xv6.lean edits, no git, no
  `sorry`;
- `tools/check_layering.sh` must stay green.

fs1 §1 (templates, vocabulary mapping, the `sie` question, `unreachable`) and §7 (report) apply
word for word. This brief only adds what is new.

## 0. Standing rules (the user's words, verbatim; they bind every agent in this wave)

- "the file system is a tricky piece of spec/proof. It's important to consult the Rocq version
  whenever you might be possibly in doubt about the right way to spec/prove something; it has the
  whole thing fully specified and proven."
- "broadly speaking, don't reinvent the wheel; check the Rocq version instead."
- "some cleanup is helpful, as there is a fair bit of gunk accumulated in the Rocq proofs, but the
  big ideas should be taken from there."
- "it's not a good idea to simplify without having the full picture or plan, because then the risk
  is, the simplification will turn out to be at odds with some later part of the proof/spec."

In practice:
- The Rocq `Spec<F>.v` sets the contract shape. The Rocq `Proof<F>.v` sets the proof route: the
  stage lemmas, the ghost moves, the order of invariant opens, and the loop invariants.
- Before any cleanup, grep `/shared/xv6rocq/iris/*.v` (comments stripped, `.claude/worktrees`
  ignored) for every downstream consumer. That means the later fs functions (readi, writei, iput,
  dirlink) AND the syscall layer (`ProofCreate*`, `ProofSys*`, `ProofFile*`).
- Record every cleanup in the file header as "Dropped/simplified vs Rocq: <item> — uses checked:
  <files> — reason". If you cannot see every consumer, keep the Rocq form.
- **Wave 2's contracts are consumed by the three largest proofs of the port** (writei, readi and
  iput, in wave 3). Their postconditions must stay Rocq-literal, clause for clause, including the
  ones that look redundant:
  - bmap's ledger clauses (a)–(e) and its "never un-allocates" clause;
  - itrunc's `∃ w u' Sb'` report;
  - ialloc's `dn' = ialloc_fresh ty` conjuncts.

**Project rules** (fs1 §0, restated):
- One kernel function per file triple (`Spec<Fn>`, `Proof<Fn>`, `Link<Fn>`).
- A `Spec<Fn>.lean` imports only definitional files and callee `Spec*` files.
- Proofs must be fast: no theorem over a few seconds. Stage every proof as Rocq does, with one
  theorem per code segment, each entered with its continuation as a named hypothesis or `def`.
  Ghost-only moves are separate lemmas.
- Use `set_option maxHeartbeats N in` per theorem only. Split a slow theorem rather than raise a
  limit.

**LAYERING (tools/check_layering.sh):**
- A Proof*/Link* file must NOT import another Proof*/Link* file, and no non-Proof file may import
  a Proof file.
- Multi-file proofs: stage files are named WITHOUT the Proof prefix (`BmapTail.lean`,
  `ItruncArm.lean`). They import only Spec/definitional files and each other, and exactly ONE
  `Proof<Fn>.lean` imports them.
- A stage file belongs to ONE function. **Do not import another function's stage file**
  (`IupdateSteps`, `BfreeParts`, `BallocDefs`, `IlockBlk`, …). Copy the few lines you need, or
  report the lemma as a promotion candidate (§4, W2-P).

## 1. Templates (the wave-1 files are now the templates)

| what | copy from |
|---|---|
| Spec file shape, pinned `sie`/`noff`/`locks`, bread's machine bundle, `V` as a parameter | `Xv6/SpecBfree.lean`, `Xv6/SpecBalloc.lean` |
| ambient `Fscfg`/`Icfg` names (`fscFs`, `fscIreg`, `icfgLog`, `icfgIst`, `fsView fscFs fscDisk icfgDev fscCov`) | `Xv6/SpecIupdate.lean` (deviation 2) |
| a derived set-forgetting form (`logOp_openS` → field at `cr = false` → `logOpS_op`) | `BFREE.wp_bfree_sconf` (SpecBfree.lean:247), `BALLOC.wp_balloc_sconf` |
| two structures from one proof core | `Xv6/SpecWalk.lean` `WALK` / `WALK_NOALLOC` (:64/:85) |
| 6-slot frame with a lazily saved `s4` slot (bmap and itrunc both have bread's exact prologue) | `MachCSL/WpSmodeFrame6c.lean` `wp_prologue6s3_gen`/`wp_epilogue6s3_gen` (:37/:83), `frame6s3rest` |
| fuel-induction scan with a live printk exit | `Xv6/BallocScan.lean`, `Xv6/BallocTail.lean` (`ba_printk`, BallocDefs.lean:453; message via `cstr_intro` + `kctx_kernelData`) |
| credited AU `log_write` (`logOpS_named` → `logCredit_own` → `lwAu_lb0`; after: `logOpSwe_opSw` → `logOpSw_witness`) | `Xv6/BfreeTail.lean`, `Xv6/BallocAlloc.lean` |
| byte-range `log_write` over a dinode slot (`lwAuRec`, `lwRecWindow`, `Efs = ⊤ \ ↑iregN`) | `Xv6/IupdateSteps.lean` `iu_log_write` (:469) |
| dinode block decode after bread (`dsHeld_L` + `iregRead_blk` → `diblkSlot_acc`) | `Xv6/IlockBlk.lean` `il_blk_open` (:98), `Xv6/IupdateMain.lean` |
| buffer byte swap inside a held handle | `dsHold_swap` (DinodeSlot:667), `bufHold0_travel`/`_of_travel` (BufEscrow:282/299), `bioLocked_split` (BcacheInv:1353) |
| slot split/join | `bslots_cons`/`bslots_uncons` (BcacheInv:1747/1775) |
| calling `iupdate` credgen and `bfree` | their Specs; no Lean caller exists yet, so you are the first |

**Addresses.** Use `KA.«f» + 0x..#64` and dump the image with
`riscv64-linux-gnu-objdump -d --section=.text /shared/lean-xv6/xv6-riscv/kernel/kernel | awk '/<f>:$/,/^$/'`.
Never copy absolute addresses from Rocq comments. The offsets below were checked against the Lean
image. All three functions have byte-identical bodies to Rocq's, so Rocq's `+0x..` offsets carry
over; the absolute addresses do not.

**MachCSL.** Every instruction in all three functions already has a rule, so wave 2 needs no
MachCSL work:

| instruction | rule |
|---|---|
| `addi`/`li`/`c.addi16sp`/`c.addi4spn` | `wp_s_addi` (WpSmodeCycle:885) |
| `mv`/`add` | `wp_s_add` (:970) |
| `slli` | `wp_s_slli` (:945) |
| `srli` | `wp_s_srli` (:933) |
| `andi` | `wp_s_andi` (:897) |
| `addiw`/`sext.w` | `wp_s_addiw` (:957) |
| `addw` | `wp_s_addw` (WpSmodeRules:454) |
| `auipc` | `wp_s_auipc` |
| `lw`/`sw` | `wp_s_lw` (:711) / `wp_s_sw` (:729) |
| `ld`/`sd` | `wp_s_ld`/`wp_s_sd`, or `wp_s_pop`/`wp_s_push` |
| `lh` | `wp_s_lh` (MachCSL/WpSmodeLh.lean:48) |
| `sh` | `wp_s_sh` (WpSmodeFrame12b:211) |
| `beq`/`bltu`/`bgeu` | `wp_s_branch` (WpSmodeRules:381) |
| `c.beqz`/`c.bnez` | `wp_s_branch0` (:746) |
| `jal` / `j` / `ret` | `wp_s_jal` / `wp_s_j` / `wp_s_ret` |

## 2. Status of the ground you build on

- **Landed (use, do not duplicate):** wave 0 and wave 1's stati, namecmp, idup, bfree, iunlock,
  iupdate and ilock, plus W1-LW and W1-TX.
  - `LOG_WRITE` has four fields: `wp_log_write_au_range` (the primitive), `wp_log_write_au`,
    `wp_log_write_gen` and `wp_log_write` (SpecLogWrite.lean:483–519).
  - The adapters `lwAu_lb0` (:385), `lwAuWhole` (:412), `lwAuRec` (:447) and `lwRecWindow` (:478)
    are all present.
  - The log ledger is in LogInv.lean: `logOpSe` 185, `logOpS` 199, `logOpSe_opS` 221,
    `logOpS_named` 226, `logOpS_op` 235, `logOp_openS` 251, `logOpSwe_opSw` 279,
    `logOpSw_witness` 296, `logCredit` 316, `logCredit_own` 324, `logCredit_group` 336,
    `logCredit_mono` 350, `logCtx_bytesAny` 570. `logEpochLb_0` is LogDefs:510 and `loggedAt` is
    LogDefs:520.
- **In progress when this brief was written (UNTRACKED): iget and balloc.**
  - `Xv6/SpecIget.lean` + IgetParts/Scan/Hit/Recycle/Tail + ProofIget + LinkIget.
  - `Xv6/SpecBalloc.lean` + BallocParts/Defs/Tail/Bzero/Alloc/Scan/Main + ProofBalloc + LinkBalloc.
  - **Gate G-IGET:** ialloc's Spec and proof are written against `SpecIget.lean`. Do not start
    ialloc's claim stage (§3.2) until SpecIget is committed; its statement may still move.
  - **Gate G-BALLOC:** likewise for bmap against `SpecBalloc.lean`.
  - Link files need the callee's Link committed.
- **The two draft contracts, as read today** (re-read them when their gates open):
  - `BALLOC.wp_balloc_gen`
    - Premises: `ballocSlots = 10 + breadSlots = 72`; pinned sie/noff/locks; `logGeomOk`,
      `bitmapGeomOk`; the PURE credit `cr = true → bmapstart ∈ Sb`.
    - Pre: `sbSizeAddr`/`sbBmapstartAddr` cells, `bitmapInv`, `bslots 2`, `logOpS (2+u) Sb`.
    - Post FAIL: `a0 = 0 ∗ logOpS (2+u) Sb`.
    - Post SUCCESS: `∃ blk`, `a0 = sext blk ∧ blk ≠ 0 ∧ fsHome`,
      `fsblock γfs.bytes blk (replicate BSIZE 0)`,
      `logOpS (if cr then u+1 else u) (blk :: bmapstart :: Sb)`.
    - The printk credentials are `panicEnv`.
  - `IGET.wp_iget`
    - Premises: `igetSlots = 62`, `noff + 3 < 2^31`, `inum < 16·icfgNib`, `0 < inum`, sext args,
      `"itable"`/`"pr"`/`"uart1"` ∉ locks. It is sie-generic.
    - Pre: `isItable2`, `itableInv`, `iregReg`, `panicEnv`, `irefSlot`,
      `iname fscIreg fscFs icfgIst inum l`.
    - Post: `wpNext k.sie`, `∃ kk q`, `kk < NINODE ∧ a0 = ientry kk`,
      `inodeRefb (isClaim l) kk q icfgDev inum`, the licence back at the same `l`.
    - `icEscrows` was DROPPED from its premises (SpecIget header).
- **Callee facts that differ from Rocq's names:**
  - `BFREE`'s field is `wp_bfree`, not `wp_bfree_gen`. Its sconf form is derived.
  - `IUPDATE` has only `wp_iupdate_credgen`, `_link` and `_unlink`.
  - `BREAD`, `BRELSE` and `MEMSET.wp_memset` (the byteBuf form, which is Rocq's `MemsetArray`) are
    unchanged from wave 1.
  - `PRINTK.wp_printk` is Rocq's `PRINTK_GEN`, with credentials by `panicEnv`.
- **The `sie` question: identical to wave 1.**
  - All three functions call `bread`, so every contract here is pinned
    `k.sie = false ∧ k.noff = 0 ∧ k.locks = [] ∧ k.tier = kpt` and crosses with the literal
    `wpNext true`.
  - Rocq's `eb`/`b` genericity, `trap_csrs_ext`/`cpu_claim_ext` and every `locks_below lks "…"`
    ("log", "bcache") collapse to that pin.
  - This is a recorded deviation, not a cleanup. Put it in each Spec header as SpecBfree does.
- **Naming.** Lean lemma names are mixed (`camelHead_snakeTail` and verbatim Rocq snake names).
  Grep both spellings before concluding a name is missing.

## 3. Per-function facts

Rocq line numbers are for `/shared/xv6rocq/iris/<File>.v`. The survey
(notes/fs-rocq-summary.md) has §3.14/§3.5/§3.15 with the specs verbatim, §1d the residuals, §4C
the budgets and §6.2 the pitfalls.

### 3.1 bmap (+ bmap_noalloc) — HARD (~2000–2500 Lean lines, 7–8 stage files); no live panic

**Rocq files.** SpecBmap.v 787, ProofBmap.v 3827, ProofBmapParts.v 467, LinkBmap.v 7,
LinkBmapNoalloc.v 12.

**Image.** `KA.«bmap»` = 0x80003070 (KernelImage.lean:18004). It is 192 B, a standalone local
symbol (not inlined into readi/writei). The frame is 48 B (6 slots): bread's exact `frame6s3`
prologue, with `s4` saved lazily into slot 0.

| offsets | code |
|---|---|
| +00..+0c | prologue |
| +0e..+12 | `mv s2,a0`; `li a5,11`; `bltu a5,a1 → +38` (direct/indirect split) |
| +16..+36 | **DIRECT**: `slli 32`/`srli 30` (fbn·4), `add`, `lw s1,80(s3)`, `bnez → +8a` (hit). Then `lw dev`, **jal balloc**, `beqz → +8a` (fail), `sw a0,80(s3)` (install), `j +8a` |
| +38..+44 | **INDIRECT head**: `addiw -12`, `li 255`, `bltu → +b2` (**DEAD**, refuted from `fbn < MAXFILE`) |
| +48..+56 | `lw s1,128(a0)` (addrs[NDIRECT]), `bnez → +60`. Then **jal balloc** (the indirect block), `beqz → +8a` (fail; s4 never saved on this path) |
| +58..+60 | `sd s4`; `sw a0,128(s2)`; `j +62` (or `+60 sd s4`) |
| +62..+80 | **jal bread**(indirect); `addi 88`; `slli 32`/`srli 30`; `lw s1,0(a5)` (entry); `beqz → +9a` |
| +82..+88 | **jal brelse**; `ld s4` |
| +8a..+98 | epilogue (`mv a0,s1`) |
| +9a..+b0 | **ALLOCATE**: **jal balloc**(data), `beqz → +82` (fail), `sw a0,0(s3)` into the buffer, **jal log_write**, `j +82` |
| +b2..+bc | DEAD: `unreachable("bmap: out of range")` (0x80007430). Refute it before the `jal`, as ProofBwrite does |

**Budget.**
- `bmapSlots := 6 + ballocSlots` (= 78, Rocq `K_bmap` l.132).
- `BMAP_NOALLOC` re-uses 78 (Rocq l.693).
- bslots: 3 for gen, 1 for noalloc.

**Contracts** (fs survey §3.14; all three Rocq forms were checked):

| Rocq form | Spec lines | downstream caller | ship as |
|---|---|---|---|
| `wp_bmap_gen_body` | 444–592 | ProofWritei.v:2291 (`WriteiProof (BM : BMAP)`) | `BMAP.wp_bmap_gen` (field) |
| `wp_bmap_noalloc_sconf_body` | 676–768 | ProofReadi.v:1299 (`ReadiProof (BM : BMAP_NOALLOC)`) | `BMAP_NOALLOC.wp_bmap_noalloc` (field of a SECOND structure) |
| `wp_bmap_sconf_body` | 258–436 | none (Module field and its seal only; comments in ProofIupdate/ProofDirlink/ProofWritei) | derive (`logOp_openS` → gen at `cr = false` → `bmapCost_le3` → `logOpS_op`; Rocq 3590–3675) only if it is under ~60 lines, otherwise drop and record |

**`wp_bmap_gen` (the allocating form).**
- **Premises:**
  - `bmapSlots ≤ k.avail`
  - `bmapNeed cr (bmapInd fbn) ≤ n` (a lower bound on the caller's counter, not a `5 + u` shape;
    writei presents its counter directly)
  - `logGeomOk`, `bitmapGeomOk`, `cr = true → bmapstart ∈ Sb`
  - `fbn < MAXFILE`, `blkmapWf cov logstart bm`
  - `a0 = ip`, `a1 = sext fbn`; the pin
- **Pre:**
  - bread's bundle, `fsBytesAny γfs`, `logCtx`
  - `iDev ip ↦{dqd} dev`, `inodeMap fs ip bm` and `inodeBlocks fs bm data` (FULL)
  - `sbSizeAddr`/`sbBmapstartAddr` cells, `bitmapInv`
  - `bslots 3`, `logOpS γ n Sb`
- **Post:** `∀ bm' n' data' Sb'`, with
  - `blkmapWf bm'`
  - agreement off `fbn`
  - never un-allocates (`get bm i ≠ 0 → get bm' i = get bm i`)
  - the arm disjunction `(a0 = 0 ∧ get bm' fbn = 0) ∨ (a0 = sext (get bm' fbn) ∧ ≠ 0)`
  - `inodeMap … bm'`
  - `data' = data ∨ (get bm fbn = 0 ∧ data' = data[fbn := replicate BSIZE 0])`,
    `inodeBlocks bm' data'`
  - `bslots 3`
  - the ledger clauses (560–589), where "⊆" is `∀ x ∈ Sb, x ∈ Sb'` in the port's list-as-set
    form:
    - (a) `n ≤ n' + bmapCost cr (bmapAlloced bm bm' fbn) (bmapInd fbn) ∧ n' ≤ n`
    - (b) `Sb ⊆ Sb' ⊆ Sb ∪ {bmapstart, bmInd bm', get bm' fbn}`
    - (c) `alloced → bmapstart ∈ Sb'`
    - (d) `ad → get bm' fbn ∈ Sb'`
    - (e) `bmapInd fbn = false → bmInd bm' = bmInd bm`
  - `logOpS γ n' Sb'`
- **FAILURE MAY CHANGE `bm`**: the indirect block can be installed before the data balloc fails
  (survey §1e.1). Do not "tighten" the fail arm to `bm' = bm`.

**`wp_bmap_noalloc`.**
- **Premises:** as gen, minus the log/bitmap ones, plus **`(blkmapGet bm fbn).toNat ≠ 0`**.
- **Pre:** bread's bundle, `fsBytesAny`, `iDev{dqd}`, **`inodeMapQ fs dq ip bm`** and
  **`inodeBlocksQ fs dq bm data` AT A SHARE `dq`** (readi runs on a read-locker's share), and ONE
  `bslot`. No log, no superblock cells, no bitmap.
- **Post:** exact. `a0 = sext (get bm fbn)`, everything handed back, `bslot`.
- **Why the three balloc arms are dead:** the premise gives it, and for the indirect-block test it
  goes through `blkmapWf_ind_nz` (InodeInv:339).

**The cost algebra** (SpecBmap.v 168–256) goes IN SpecBmap.lean, with Rocq's names camelCased:
- `bmapInd`, `bmapAi`, `bmapAd`, `bmapAlloced`, `bmapCost`, `bmapNeed`
- the lemmas `_cost_le3`, `_need_le4`, `_need_ge2`, `_ind_lt/_ge`, `_alloced_none`,
  `_ad_none/_true`, `_alloced_of_ad/_ai`, `_ai_true`

ProofCreateShared, ProofCreateMkdir and WriteiBudget.v use these names directly, and
`Xv6/WriteiBudget.lean`'s deferred sections cite `bmap_cost` by name.

**Proof route** (ProofBmap.v).
- **One core, parameterised by `ak : Option BmAlloc`** (Rocq `bm_gen_stmt` 427–518 in
  `Module BmapCore (BR BL)` 520–3574).
  - `BmAlloc`/`bmAllocRes` already exist (BitmapInv.lean:655/668).
  - The kit (`bm_kit` 210) is `bmAllocRes ∗ logCtx ∗ bslots 2 ∗ logOpS n Sb` at `some`, `emp` at
    `none`.
  - The callee contracts enter as HYPOTHESES gated on `ak` (Rocq `balloc_contract` 392 is
    `wp_balloc_gen_body`; `log_write_contract` 411 is `wp_log_write_gen_body`).
  - In Lean, take `(hba : ak.isSome → BALLOC) (hlw : ak.isSome → LOG_WRITE)`, so that
    `bmap_noalloc_proof (BR : BREAD) (BL : BRELSE) : BMAP_NOALLOC` needs neither. That keeps
    readi/dirlookup/namex free of balloc (survey §4C item 2).
- **`log_write` is the WHOLE-BLOCK HELD `wp_log_write_gen` form**, not AU and not range. It is
  called at 1974 with `bs = indBytes (new)`, `bsl = indBytes (old)` and credit `cri` (the indirect
  block is already in the set). Its `fsblock` comes from `fsblockQ_1_of/_to` (FsBytes:218/222)
  under `ak ≠ None → dq = 1`.
- **Stage lemmas, right to left:**
  - `bm_epilogue` 646–969 (+8a..+98)
  - `bm_release` 981–1162 (+82..+88; brelse at 1089)
  - `bm_indirect_tail` 1174–2178, covering +62..+80 and +9a..+b0:
    - bread at 1389
    - `bm_held_content` 1422 pins the buffer to `indBytes (bmEnt bmI)`
    - the entry read and `beqz` 1585–1620
    - the allocate arm 1620–2114: data balloc 1726, fail 1760, `inodeFreshQ` 1848, the buffer
      store 1906, log_write 1974, `blkmapWf_slot_upd` 2028, `inodeBlocksQ_insert` 2061)
    - the hit arm 2144
  - the core `wp_bmap_gen` 2189–3570:
    - prologue 2240–2323
    - direct arm 2564–2875 (balloc 2631, install 2732–2830)
    - indirect head 2966–3483 (dead `bltu` 3068, `inodeMapQ_ind_acc` 3084, no-alloc via
      `blkmapWf_ind_nz` 3112, balloc 3206, `indBytes_replicate` 3411)
- **Seals.**
  - `BmapProof` 3582–3762: gen at `ak = some`, with `dq = 1` via `inodeMapQ_1_of`.
  - `BmapNoallocProof` 3764–3827: the core at `none`, `n = 0`, `cr = false`, `Sb = []`.
- **Ghost moves** (all landed in InodeInv unless noted):
  - `inodeMapQ_dir_acc`/`_ind_acc` (1343/1372)
  - `inodeFreshQ` (1212)
  - `blkmapWf_slot_upd` (610), `bmSlot_insert_*` (563–596)
  - `inodeBlocksQ_insert` (1105), `inodeBlocksQ_1_of/_to` (818/823)
  - `bmCells_set_dir/_ind` (1328/1334; these ARE ProofBmapParts' `bm_cells_insert_dir/ind`)
  - `indBytes_lookup`/`_insert_*`/`_replicate` (BlockWords:99/128–177)
  - `fsBytes_agree_any_q` (FsBytesMint:279)
  - `dsHold_swap`/`dsHold_k` (DinodeSlot:667/649; these are `bm_held_swap`/`bm_held_k`)

**Missing.**
- The cost algebra (above).
- The ProofBmapParts.v arithmetic/buffer lemmas. **The ones itrunc also uses go in W2-P (§4).**
  The bmap-only ones go in `BmapParts.lean`: `bm_slli32_srli30`, `bm_addiw_m12`, `bm_sext32`,
  `bm_uint_moi`, `bm_sext_zero`, `bm_data_addr`, `bm_slot_addr`, `bm_off0`, `bm_ent_store`.
- The `bm_*` set lemmas become List-membership lemmas. Rocq's `set_solver` cost up to 407 s at
  one site; state small named lemmas and use `simp`/`List.mem_cons`.

**Stale in Rocq.**
- The SpecBmap/ProofBmap headers say `panic(...)`; the code calls `unreachable`.
- SpecBmap 67–68 mentions an "interior acquire"; there is none. `panicEnv` is there only because
  bread needs it.
- The ProofBmap header calls the main lemma `wp_bmap_sconf`; it is `BmapCore.wp_bmap_gen`.
- LinkBmap.v and ProofBmap 142–146 say balloc is ASSUMED/Axiom. It is proven.
- ProofBmap 387 says "sconf" for what are `_gen` bodies.
- The Rocq functors take `PRINTK_GEN`, which bmap never calls. **Drop `Printk` from both Lean
  proofs and Links** and record it (uses checked: ProofBmap.v only).

**Lean shape.**
- `structure BMAP` with field `wp_bmap_gen` (+ a derived `BMAP.wp_bmap_sconf` if cheap).
- `structure BMAP_NOALLOC` with field `wp_bmap_noalloc`.
- `theorem bmap_proof (BA : BALLOC) (BR : BREAD) (BL : BRELSE) (LW : LOG_WRITE) : BMAP`.
- `theorem bmap_noalloc_proof (BR : BREAD) (BL : BRELSE) : BMAP_NOALLOC`.
- `LinkBmap.lean` (`Balloc Bread Brelse LogWrite`) and `LinkBmapNoalloc.lean`
  (`Bread Brelse`).

**Split** (suggested):
1. `BmapParts.lean`: bmap-only arithmetic.
2. `BmapDefs.lean`: kit, core statement, frame, `bmCont`, thr/sp predicates.
3. `BmapTail.lean`: epilogue + release.
4. `BmapIndRead.lean`: +62..+80 and the hit arm.
5. `BmapIndAlloc.lean`: +9a..+b0.
6. `BmapDirect.lean`: +16..+36.
7. `BmapHead.lean`: +38..+60.
8. `BmapMain.lean`: prologue, dispatch, core assembly.
9. `ProofBmap.lean`: the two seals.

**Needs** gate G-BALLOC (Spec and Link) and W2-P. SpecBmap and the pure parts can start at once.

### 3.2 ialloc — HARD (~2000–2400 lines, 5 stage files); LIVE printk ARM

**Rocq files.** SpecIalloc.v 560, ProofIalloc.v 3404, LinkIalloc.v 25
(`IallocProof Bread LogWrite Brelse MemsetArray Iget PrintkGen`).

**Image.** `KA.«ialloc»` = 0x80003188 (KernelImage.lean:18108). It is 188 B with a 64-B frame (8
slots: ra, s0, s1..s6).

| offsets | code |
|---|---|
| +08/+0c | `auipc`+`lw` `sb.ninodes` (`sbNinodes`) |
| +12 | **`bgeu a5,a4` → +72: DEAD**, refuted from `1 < ninodes` (Rocq `wp_bgeu_fall` at 3060) |
| +16..+2c | pushes s1..s6, `s4 = &sb` |
| +30..+64 | **SCAN**: `srli a1,s2,4` (64-bit), `lw sbInodestart`, `addw`, **jal bread**. Then `andi 15`, `slli 6`, `add` (the slot), **`lh a5,0(s3)`** (type), `beqz → +88` (claim). Then **jal brelse**, `addi s2,1`, `lw sb.ninodes`, `sext.w`, `bltu → +30` |
| +66..+7e | **OUT (LIVE)**: pops, then `printk("ialloc: no inodes\n")` (`KStr.«ialloc: no inodes\n»`, KernelImage.lean:18560, 0x80007458), `li a0,0` |
| +80..+86 | join epilogue |
| +88..+ba | **CLAIM**: `memset(dip,0,64)`, **`sh s6,0(s3)`** (type), **jal log_write**, **jal brelse**, `sext.w a1,s2`, **jal iget**, pops, `j +80` |

**Budget.**
- `iallocSlots := 8 + breadSlots` (= 70 = Rocq `K_ialloc` l.149). `igetSlots` is also 62.
- `bslots 2`.

**Contracts:**

| Rocq form | Spec lines | downstream caller | ship as |
|---|---|---|---|
| `wp_ialloc_gen_body` | 366–525 | ProofCreateAlloc.v:404 (via `create_fresh_ty`, ProofCreateFreshTy.v:192–201) | `IALLOC.wp_ialloc_gen` (field) |
| `wp_ialloc_sconf_body` | 173–348 | none (derived in ProofIalloc 3355–3400, ~45 lines) | derive as `IALLOC.wp_ialloc_sconf` (cheap), or drop and record |

Also port **`ialloc_fresh ty`** (154–156: `MkDinode ty 0 0 0 0 (replicate 13 0)`) with
`ialloc_fresh_type`/`_shape` (needs `ty ≠ 0`; gives `freshShape`)/`_wf` (158–170) into
SpecIalloc.lean as `iallocFresh` and its lemmas.

**`wp_ialloc_gen`.**
- **Premises:**
  - `iallocSlots ≤ k.avail`, `logGeomOk`
  - `iregBlocksOk ist nib cov logst` (InodeInv:237)
  - `1 < ninodes`, `ninodes ≤ 16·nib`, `ninodes < 2^31`
  - `ty ≠ 0`, `iregTyOk (iallocFresh ty)` (InodeRegionDefs:654)
  - `a0 = sext icfgDev`, `a1 = sext ty`; the pin
  - (`0 ≤ ist` vanishes at `Nat`.)
- **Pre:**
  - bread's bundle, `panicEnv` (printk credentials), `logCtx`
  - `sbNinodes ↦{dqn}`, `sbInodestart ↦{dqs}`
  - `iregInv` and `iregOpen` (IcacheRefDefs:1157), both persistent
  - `isItable2`, `itableInv`, `irefSlot`
  - the claiming transaction's share `icfgLog.tx ↪◯MAP[t]{own qt} ()` (the raw form
    `iregClaim_au` takes, InodeRegionMovers:54)
  - `bslots 2`, `logOpS (u+1) Sb`
- **There is NO iget licence in the pre.** The licence `.claimL ty t qt` (whose `iname` is
  `iclaim inum ty t qt`, IgetLic:218) is MINTED inside `log_write`'s ghost step and lent to iget.
- **Post** (`wpNext true`):
  - SUCCESS:
    - `a0 = ientry kslot`, `kslot < NINODE`, `0 < inum < ninodes`, `inum < 16·nib`
    - `dn' = iallocFresh ty ∧ diType dn' = ty ∧ freshShape dn'` (keep these conjuncts;
      ProofCreateFreshTy reads them)
    - `inodeClaimed ty kslot q dev inum t qt` (IcacheRef:907, `_intro` :912)
    - `logOpS u (IBLOCK inum ist :: Sb)`. The spend is unconditional: no credit.
  - FAIL: `a0 = 0`, with `irefSlot`, the tx share and `logOpS (u+1) Sb` returned unspent.
- **Drop `icEscrows`** from the premises, following SpecIget's drop. Uses to check:
  ProofCreateAlloc/ProofCreateFreshTy/SpecCreate frame it only. Re-grep and record.

**Proof route** (ProofIalloc.v).
- Pure `ia_*` 136–322. Most are ALREADY in DinodeSlot.lean: `dsSext_small`, `dsSrli4`,
  `dsAddwIbl`, `dsAndi15`, `dsSlli6`, `dsSext64_16_inj`, `dsType_zero/_nonzero`, `dsBgeu/_Bltu`,
  `dsHeld_L` (= `ia_held_L`). Grep before porting.
- Defs 430–544 (`ia_frame` 8 slots, `ia_arms`, `ia_cont`, `ia_thr2/8`, `ia_sp`).
- `ia_epilogue` 550–761 (packs `inodeClaimed_intro`).
- `ia_out` 776–1096 (printk at 1043; copy `ba_printk`).
- **`ia_claim` 1114–1976**, in this order:
  - `dsHold_swap` → `dsBuf_bytes` → the 64-byte window. Use `diblkSlot_acc` + `dislot_bytes` in
    place of Rocq's raw `ia_win_acc`.
  - `memset` 64 at 1329.
  - `sh` at 1384, rebuilt through `dislot`.
  - `logOpS_named` + `logCredit_own false` + `logEpochLb_0`.
  - **`LW.wp_log_write_au_range` at 1506**, window `(64·islot, 64)`, `lwRecWindow`,
    `diblkBytes_splice`, `Efs = ⊤ \ ↑iregN`, **`Φfsb := iclaim inum ty t qt`**. The AU is
    `lwAuRec` ∘ `iregClaim_au ⊤ … (iallocFresh ty) ds t qt` (1532–1536).
  - `brelse` 1625.
  - **iget at 1751** with licence `.claimL ty t qt`, after `iregInv_reg` (InodeRegionInv:751).
  - iget's `inodeRefb (isClaim …)` → `runitClaim` (IcacheRefLink:197) → `inodeClaimed_intro`.
- **`ia_scan` 1990–2854**:
  - Fuel induction on `ninodes − inum`, the continuation reverted BEFORE induction.
  - Each turn: bread 2271, `dsHeld_L` + `iregRead_blk` (InodeRegionMovers:370) → `iregBlkSlot`
    2557, `lh`/`beqz`, then the claim (2565), or brelse 2646 and the `bltu`, then IH or
    `ia_out` 2845.
  - The only region moves are `iregRead_blk`, `iregClaim_au` and `iregInv_reg`. There is NO
    `iregWithdraw` (that is ilock's).
- Main 2863–3353.
- **Reuse iupdate's call wrapper by COPY, not import.** `iu_log_write` (IupdateSteps.lean:469)
  already packages the range-form call with `lwRecWindow`/`iu_shape`/`Efs`. Rocq's ProofIalloc
  does not import ProofIupdate either. Restate it (~50 lines) in `IallocClaim.lean` at
  `dn = iallocFresh ty`, `Pout = iclaim …`, `cr = false`, `vlb = 0`, or ask for W2-P promotion.

**Stale in Rocq.**
- The SpecIalloc header and the `ia_claim` banner say "`wp_log_write_au` … `Φfsb := True`". The
  code uses `_au_range` with `Φfsb = iclaim`.
- ProofIalloc ~l.130 gives the message address as 0x80007428; it is 0x80007458.
- "THREADED printk obligation … pure hypothesis": printk is a functor parameter.
- SpecIalloc says "`itable` is the lowest"; the premise is `locks_below "log"`.
- LinkIalloc says `bgeu a4,a5`; it is `a5,a4`.

**Missing.**
- `iallocFresh` + 3 lemmas.
- `iaDzero` and `dinodeBytes iaDzero = replicate 64 0`.
- `ia_fresh_of_zero`.
- The message/`cstr` fact, the `sb` address facts (auipc+lw), and the branch/return `decide`
  facts.

**Lean shape.**
- `structure IALLOC` with field `wp_ialloc_gen`.
- `ialloc_proof (BR LW BL) (MS : MEMSET) (IG : IGET) (PK : PRINTK) : IALLOC`.
- Link with `Bread LogWrite Brelse Memset Iget Printk`.

**Split** (suggested):
1. `IallocParts.lean`: pure facts, message, targets, sb addresses, call-site wrappers.
2. `IallocDefs.lean`.
3. `IallocTail.lean`: epilogue + out/printk.
4. `IallocClaim.lean`: +88..+ba; cut at log_write's return if slow.
5. `IallocScan.lean`: +30..+64.
6. `ProofIalloc.lean`: prologue, dead `bgeu`, main, sconf.

**Needs** gate G-IGET. Spec, Parts, Tail and Scan can start at once; the Claim stage waits for the
gate.

### 3.3 itrunc — HARD (~1700–2200 lines, 5 stage files); no panic

**Rocq files.** SpecItrunc.v 676, ProofItrunc.v 3062, ProofItruncParts.v 671, LinkItrunc.v 21
(`ItruncProof Bread Bfree Brelse Iupdate`).

**Image.** `KA.«itrunc»` = 0x800033e6 (KernelImage.lean:18136). It is 148 B, 53 instrs, with a
48-B frame. This is exactly `frame6s3` (use `wp_prologue6s3_gen`/`wp_epilogue6s3_gen`); the pad
slot is the conditional `s4`.

| offsets | code |
|---|---|
| +00..+18 | prologue; `s1 = ip+80`, `s2 = ip+128`, `j +20` |
| +1a..+30 | **DIRECT loop** (rotated): `addi s1,4`, `beq s1,s2 → +32`. Then `lw a1,0(s1)`, `beqz → +1a`, `lw dev`, **jal bfree**, `sw zero,0(s1)`, `j +1a` |
| +32/+36 | `lw a1,128(s3)`, `bnez → +50` |
| +38..+4e | **TAIL**: `sw zero,76(s3)` (size = 0), **jal iupdate**, epilogue |
| +50..+64 | **ARM**: `sd s4`, **jal bread**(indirect), `s1 = a0+88`, `s2 = a0+1112`, `j +6c` |
| +66..+78 | **ENTRY loop** (rotated): `addi s1,4`, `beq → +7a`, `lw a1,0(s1)`, `beqz`, `lw dev`, **jal bfree**, `j +66` |
| +7a..+92 | **jal brelse**; `lw a1,128(s3)`; **jal bfree**(indirect); `sw zero,128(s3)`; `ld s4`; `j +38` |

bfree is CALLED (three sites), not inlined.

**Budget.**
- `itruncSlots := 6 + bfreeSlots` (= 72 = Rocq `K_itrunc` l.135).
- `bslots 3`, split as follows:
  - direct loop: 2 + 1 parked;
  - arm: bread takes the third, and each nested bfree takes 2;
  - tail: iupdate 2 + 1 parked.

**Contracts:**

| Rocq form | Spec lines | downstream caller | ship as |
|---|---|---|---|
| `wp_itrunc_gen_body` | 512–640 | ProofIput.v:3095 (`crb`, credit `cru‖crz` via `logCredit_group`), ProofSysOpenStores.v:822 | `ITRUNC.wp_itrunc` (field; name it as BFREE does, or keep `wp_itrunc_gen`; say which in the header) |
| `wp_itrunc_sconf_body` | 308–483 | none (derived in ProofItrunc 3008–3058) | derive as a theorem if cheap (the `BFREE.wp_bfree_sconf` pattern), else drop and record |

**`wp_itrunc_gen`.**
- **Premises:**
  - `itruncSlots ≤ k.avail`, `crb = true → bmapstart ∈ Sb`
  - `logGeomOk`, `bitmapGeomOk`
  - `IBLOCK inum ist ∈ cov`, `∉ logRegion`, `inum < 16·nib`
  - `diType dn ≠ 0`, `diTypeStable dn dn0`, `diNlinkStable dn dn0`
  - `blkmapWf cov logst bm`, `covBelow cov size` (IcacheInvAlg:179)
  - `inodeSized data` (∀ i < MAXFILE, |data i| = BSIZE; InodeInv:457)
  - `diAddrs dn = bmCells bm`
  - `a0 = ip`; the pin
- **Pre:**
  - bread's bundle, `logCtx`
  - `iDev`/`iInum` cells, `inodeMeta ip dn`, `inodeMap fs ip bm`, `inodeBlocks fs bm data`
  - `sbBmapstartAddr`, `sbInodestart` cells
  - `bitmapInv`, `iregInv`, `dinodeAt ireg inum dn0`
  - `bslots 3`
  - **`logCredit icfgLog cru Sb e0 (IBLOCK inum ist)`** (a RESOURCE)
  - **`logOpSe icfgLog (itEntry crb u) Sb e0`**
- **Post:**
  - `inodeMeta ip (diTrunc dn)`, `inodeMap fs ip bmEmpty`,
    `inodeBlocks fs bmEmpty (fun _ => replicate BSIZE 0)`
  - `dinodeAt ireg inum (diTrunc dn)`, `bslots 3`
  - `∃ w u' Sb'`, with:
    - `Sb ⊆ Sb'`, `IBLOCK ∈ Sb'`
    - `w = true → bmapstart ∈ Sb'`
    - `crb = true → w = false`
    - `itEntry crb u − (itBm w + itIu cru) ≤ u' ∧ u' + itIu cru ≤ itEntry crb u`
    - `logOpS u' Sb'` (epoch CLOSED)
- **Port with it:**
  - `diTrunc` (142–144) + `_addrs`/`_wf`
  - `itEntry` (226), `itIu` (231), `itBm` (240)
  - **`bmPaidS crb u Sb e0`** (217–221) with `_intro` (251) and `_elim` (273)
- **Drop the dead ones and record them:** `bm_paid`, `bm_paid_intro`, `bm_paid_elim`,
  `bm_paid_use`, `it_spend` (grep: only SpecItrunc/ProofItrunc*/WriteiBudget.v comments).

**THE BUDGET IS `bmPaidS`, NOT `logAmort`.** Rocq's itrunc never uses `log_amort`/
`one_bitmap_block`. The 269 frees are paid by threading ONE epoch `e0` and re-presenting the
bitmap credit at every bfree:
- **`bmPaidS_use`** (ProofItruncParts 482) gives `∃ cr u' Sq`, `cr → bmapstart ∈ Sq`,
  `(if cr then u'+1 else u') = u+1`, `logOpSe (u'+1) Sq e0`, and a wand back.
- Then `logCredit_own … cr Sq e0 bmapstart`, then `BFREE.wp_bfree`.

This matches Lean bfree's `u+1 → if cr then u+1 else u` exactly. It is why bfree's contract takes
the credit as a resource at a NAMED epoch and returns the SAME `e0`. Do not close the epoch
inside the loops.

**Proof route** (ProofItrunc.v, `ItruncProof` l.74).
- `it_cont` 92–123, `it_thr` 127, `it_thr4` 136 (s4 excluded; used inside the arm), `it_sp` 148.
- **`it_tail` 193–655** (+38..+4e):
  - `sw zero` size, then `logEpochLb_0` (v = 0).
  - **`IU.wp_iupdate_credgen` at 362** with `(diTrunc dn) dn0 bmEmpty u Sb0 cru e0 0`.
  - bslots 3 → 2+1.
  - Drop the `loggedAt` receipt.
  - `iregOut_alloc_inv` (InodeRegion:210) turns `iregOut` back into `dinodeAt` using `diType ≠ 0`.
- **`it_dloop` 694–1223**:
  - Fuel induction on `NDIRECT − k`, continuation reverted before the induction.
  - State `itDirState` = `inodeMap (bmDirZeroed bm k) ∗ inodeBlocks (bmDirZeroed bm k) data ∗ bmPaidS`,
    opened and closed only by lemma so the IH matches.
  - Step:
    - `inodeMap_dir_acc` (InodeInv:1360) read, then `beqz`.
    - Zero entry: skip (`bmDirZeroed_skip`).
    - Otherwise `bmPaidS_use` 1038 → `logCredit_own` 1043 → **bfree 1053** with the block's
      `fsblock` from `inodeBlocks_take` → `sw zero` (`bmDirZeroed_step`).
  - `bitmapInv` rides persistent; there is no free-pool bookkeeping in itrunc.
- **`it_eloop` 1263–1754**:
  - Same shape over `itEntRes` (big-op over `seq q (NINDIRECT − q)` of `blkRes`) + `bmPaidS`.
  - The buffer's `bufOwn … (indBytes (bmEnt bm))` rides unchanged.
  - The word read uses `bm_buf_word_acc`/`bm_ent_read`/`bm_align4`/`bm_buf_restore` (W2-P).
  - bfree at 1605.
- **`it_iarm` 1792–2480**, in this order:
  - `inodeMap_ind_acc` (:1394) → `indRes_nz` → `fsblock (bmInd) (indBytes ent)`.
  - `sd s4`.
  - **bread 1980** on the parked third slot.
  - `bio_locked_kbound`.
  - `logCtx_bytesAny` + `fsblockQ_1_to/of` + **`bm_held_content`** (2003–2012; `dsPay_content`,
    DinodeSlot:756, is the full-fraction form).
  - `dsHold_swap`.
  - `inodeBlocks_toEntRes`.
  - `it_eloop`.
  - Rebuild the handle.
  - **brelse 2213**.
  - `lw` the indirect block again.
  - **bfree(indirect) 2348** with bytes `indBytes (bmEnt bm)`.
  - `sw zero,128`.
  - `bmDirZeroed_full` → `bmEmpty`.
  - `ld s4`, `j` to the tail.
  - Watch Rocq's comment at 2324 on context transports stranded across brelse.
- **Main 2497–2992**:
  - `blkmap_slot_inrange` (IcacheInvAlg:185) + `covBelow` give the range facts.
  - `bmPaidS_intro` 2756.
  - `it_dloop`.
  - Dispatch on `bmInd` (`blkmapWf_no_ind` for the no-indirect exit).
  - Each exit: `bmPaidS_elim` + `logCredit_mono` → `it_tail`, closed by `it_sub_union_l`/
    `it_in_union_sing` and `omega` over `itEntry`/`itBm`/`itIu`.

**`inodeBlocks` is a 268-element big-op**, and an `iframe` over it hangs (its InodeInv docstring
says so). Keep it behind the take/frame/toEntRes lemmas.

**Missing** (ProofItruncParts.v; all go in `ItruncParts.lean` unless W2-P takes them):
- `bmDirZeroed` (73) + 9 lemmas (77–222)
- the cursor/injectivity lemmas `it_dir_cursor`, `i_addr_inj`, `b_data_off_inj`,
  `b_data_cursor`, `it_dir_limit` (224–310)
- `it_frame` 345
- `itDirState` + open/close (374–398)
- `itEntRes`/`itEntState` + open/close/peel/done (420–664)
- `bmPaidS_use` 482
- `inodeBlocks_take` 518 (from `inodeBlocks_acc`/`_frame`, InodeInv:1093/1049)
- `inodeBlocks_emptyAny` 557 (check `bmEmpty_holes`, InodeInv:518, first)
- `blkRes_nz` 569, `bio_locked_kbound` 579, `indRes_nz` 591 (from `indBlk_nz` :739),
  `inodeBlocks_toEntRes` 624

**Callee wrapper.** Write ONE `it_bfree` lemma (`bmPaidS_use` + `logCredit_own` + `BF.wp_bfree` +
reclose) and use it at all three sites.

**Split** (suggested):
1. `ItruncParts.lean`.
2. `ItruncTail.lean`: +38..+4e.
3. `ItruncDirect.lean`: `it_dloop`.
4. `ItruncELoop.lean`: `it_eloop`.
5. `ItruncArm.lean`: `it_iarm`.
6. `ProofItrunc.lean`: prologue, dispatch, exits, the sconf derivation,
   `itrunc_proof (BR BF BL IU) : ITRUNC`.

Parts comes first. Tail and Direct need nothing else; ELoop and Arm need W2-P.

**Needs** nothing unlanded except W2-P. bfree and iupdate are committed.

## 4. Prerequisite

**W2-P: the shared buffer-word lemmas (Rocq ProofBmapParts.v, the part itrunc also uses).**
- Rocq's ProofItrunc.v and ProofItruncParts.v `Require Import ProofBmapParts`, and so do
  ProofReadiParts.v and ProofWriteiParts.v (wave 3).
- In Lean a stage file may not be shared across functions, so the shared lemmas need a DEFINITIONAL
  home. Suggested name: `Xv6/BlkmapBuf.lean` (not `BmapParts`, which stays bmap-only).
- It should contain:
  - `bm_eqz_true`/`_false`
  - `bm_align4` (4-byte alignment of `aBufData (bnode kk) + 4q`)
  - `bm_ent_read` (`bytesToWord4 (((indBytes e).drop (4q)).take 4) = e[q]`, from
    `indBytes_lookup`)
  - `bm_buf_word_acc` (over `byteBuf_word4_acc`, ByteWord4:240)
  - `bm_buf_restore`
  - `bm_held_content` at a SHARE, as `dsPay_contentQ` by copy of `dsPay_content` via
    `fsBytes_agree_any_q`, FsBytesMint:279. bmap's no-alloc read needs the share; itrunc can use
    either.
  - If they are wanted in the shared file, `bm_ent_store` and the address lemmas `bm_data_addr`/
    `bm_slot_addr`.
- Size: ~250–350 lines, about an hour.
- **Coordinator decides** the home: (a) this new definitional file, owned by one small agent and
  landed first; or (b) Rocq's literal structure, where itrunc's stage files import bmap's
  `BmapParts.lean`. Option (b) breaks the one-function-per-stage-file rule and serialises itrunc
  behind the bmap agent. **(a) is recommended.**
- Also a promotion candidate, same decision: `iu_log_write` (IupdateSteps:469). ialloc may
  restate it instead (the default in §3.2).

## 5. Dependency order and batch schedule

The three functions are mutually independent in the call graph:
- bmap needs balloc;
- ialloc needs iget and the log_write range form;
- itrunc needs bfree and iupdate.

One agent owns one function's triple plus its stage files. Nobody edits a file another agent owns.

**Batch W2-A (4 in parallel, start now):**
- **P**: W2-P `BlkmapBuf.lean`. Small; land it first.
- **B bmap**:
  - Start now: SpecBmap (cost algebra and both bodies), `BmapParts`, `BmapDefs`, `BmapTail`
    (none of these call balloc).
  - Wait for G-BALLOC: `BmapDirect`/`BmapHead`/`BmapIndAlloc` (the balloc call sites) and Link.
  - Wait for P: `BmapIndRead`.
- **I ialloc**:
  - Start now: SpecIalloc, `IallocParts`/`Defs`/`Tail`/`Scan`.
  - Wait for G-IGET: `IallocClaim` and Link.
- **T itrunc**:
  - Start now: SpecItrunc, `ItruncParts`, `ItruncTail`, `ItruncDirect`.
  - Wait for P: `ItruncELoop`/`ItruncArm`.

**Critical path.**
- bmap is the largest, and it gates BOTH readi (noalloc) and writei (gen) in wave 3.
- itrunc gates iput in wave 3.
- ialloc gates only the syscall layer (create) in wave 7, so it is off the fs.c critical path.
  Staff it last if agents are short.

**After wave 2:** readi (BMAP_NOALLOC), writei (BMAP, IUPDATE) and iput (ITRUNC, IUPDATE); see
survey §7.4.

## 6. Risks

1. **bmap's postcondition shape is writei's loop invariant.** The ledger (a)–(e), the arm-wise
   `bmapCost`, the `∀ bm' …` binder order and "never un-allocates" are what WriteiBudget's
   deferred sections (`wi_*`, `bm_iter_cost`, `bm_pot`) are stated over. Port them literally.
   Read ProofWritei.v around 2291 before fixing any binder order.
2. **The two bmap contracts must come from ONE core.** Rocq has no second proof. The
   `Option BmAlloc` gating must keep BALLOC/LOG_WRITE out of `bmap_noalloc_proof`'s arguments,
   otherwise readi's cone gains balloc.
3. **The share form of the no-alloc read.** `inodeMapQ`/`inodeBlocksQ` at `dq` everywhere on the
   `none` path; `fsblockQ_1_of/_to` only under `ak = some → dq = 1`. Missing the share form of
   `bm_held_content` (W2-P) is what would push someone to state noalloc at full fraction, which
   readi cannot supply.
4. **Gate drift.** SpecBalloc and SpecIget are untracked drafts. If either statement moves after
   bmap/ialloc build against it, those call sites move too. Start the call-site stages only when
   the gate commits.
5. **itrunc's epoch threading.** Closing `e0` early (an `∃ e0` in a loop invariant, or a
   `logOpSe_opS` before the tail) makes the tail's iupdate credit unstatable. Keep `e0` fixed
   from entry to `it_tail`, as Rocq does.
6. **Live arms stay live.** ialloc's "ialloc: no inodes" printk arm (the region can be full) and
   bmap's three balloc-fail arms are real returns. The dead arms, all refuted before the
   branch/`jal`, are:
   - ialloc +0x12 (`1 < ninodes`);
   - bmap +0x44 → `unreachable` (`fbn < MAXFILE`);
   - bmap-noalloc's balloc arms (`get bm fbn ≠ 0`, `blkmapWf_ind_nz`).
7. **List-as-set arithmetic.** Rocq's `set_solver` took 407 s at one itrunc site. Every ⊆/∪ fact
   goes into a small named lemma, discharged by `simp [List.mem_cons]`/`omega`.
8. **Proof speed.** These are 3.1–3.8k-line Rocq proofs. Follow the stage splits above, and split
   any theorem over a few seconds before reporting done.
9. **Stale Rocq prose** (listed per function above). The CODE is the reference.

## 7. Report (per agent)

As fs1 §7:
- Files with line counts and the last line of each build.
- The slowest theorem's elaboration time.
- Every deviation from Rocq with its reason, and every cleanup as "item — uses checked — reason"
  (in particular each dropped `sconf` form, bmap's dropped `Printk`, and ialloc's dropped
  `icEscrows`).
- Every landed name reused.
- Any edit an existing file needs, as exact old → new.
- Any lemma you copied from another function's stage file, as a promotion candidate.
