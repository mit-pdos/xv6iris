# Weak port: sail-riscv drift c32fbf41 → 070832a1 (drift item zero)

Rocq weak line pin: `c32fbf4111b8` ("Model the PTE A/D-bit update as an atomic read-check-write",
2026-08-06; `xv6iris-spinlock/tools/regen_sail_model.sh`). Lean pin: `070832a1e4b0` ("Expose AK_ifetch /
AK_ttw at the concurrency interface", 2026-08-26). Fork: zeldovich/sail-riscv. I checked this in a scratch
clone.

**History is linear.** `c32fbf41` is the merge base. `c32fbf41..070832a1` holds 3 commits and the reverse
range holds 0. The atomic A/D update is in both pins. The whole diff touches 5 files, +20/−7 lines:

| commit | files | class |
|---|---|---|
| `c7c3dbde` coq: bind the reservation and terminal platform externs | `model/sys/platform.sail`, `model/sys/sys_reservation.sail` | (c) |
| `23dcf8fd` add Axiom definitions to the baseline riscv_extras.v | `handwritten_support/riscv_extras.v` | (c) |
| `070832a1` Expose AK_ifetch / AK_ttw | `model/core/phys_mem_interface.sail`, `model/sys/mem.sail` | **(a) HIGH** |

None of these files is touched: fetch (`postlude/fetch.sail`), step, decode/execute, the walker
(`vmem*.sail`), PMP, CSRs, AMO, LR/SC, fences, trap entry, or the announce sites
(`lib/concurrency_interface`). Store/write kinds are unchanged too.

## (c) `c7c3dbde`, `23dcf8fd`: Rocq extern bindings

These commits add `coq: "<name>"` to the `val` declarations of `load_reservation`, `match_reservation`,
`cancel_reservation`, `valid_reservation`, `plat_term_write` and `plat_term_read`. They also add the matching
`Axiom`s to the *stub* `riscv_extras.v`. Effects:
- **Lean:** none. The Lean backend ignores the `coq:` key, and these externs are realised by hand in
  `model/Xv6Extras.lean`.
- **Rocq:** a regen at the new rev would stop emitting the bare `Axiom`s in `rv64d.v` and would resolve
  the names from `model-xv6iris/riscv_extras.v` instead. That is a link-time change only. The events are
  the same, since these calls are pure or outcome-free externs either way.

## (a) HIGH: `070832a1` changes the access kind on every fetch and every plain PTE read

**Old.** `checked_mem_read` used `let rk = read_kind_of_flags(aq, rl, res)`, which picks the kind from the
flags alone. A fetch `mem_read(InstructionFetch(), …, false,false,false)` got `Read_plain`, and so did a
walker read `mem_read_priv(Load(PageTableEntry), …, false,false,false)`. Both became
`AK_explicit{AV_plain, AS_normal}`. The constructor `Read_ifetch` existed but no code produced it.

**New.**
```sail
let rk : read_kind = match (access, res) {
  (InstructionFetch(), false)   => Read_ifetch,   // -> AK_ifetch()
  (Load(PageTableEntry), false) => Read_ttw,      // -> AK_ttw()   (new enum constructor)
  (_, _)                        => read_kind_of_flags(aq, rl, res),
};
```

**What does not change.**
- The *shape* of every event stream is the same: the number, order, addresses, widths and values of
  MemRead/MemWrite/barrier/announce/register events. The new match is pure, no read is added or
  removed, and MMIO reads (`mmio_read`) do not use `rk`.
- The atomic A/D read-check-write (`vmem.sail:76`, `res = true`) still classifies as
  `AK_explicit{AV_exclusive}`. Data loads, AMOs and LR/SC are also unchanged.

**What changes.**
- The `access_kind` payload of the `MemRead` request is now `AK_ifetch ()` for **every instruction
  fetch**. It is `AK_ttw ()` for every non-atomic page-table-walk read.
- `read_kind` gains a constructor, which renumbers `num_of_read_kind` and `read_kind_of_num`. Nothing in the
  weak tier relies on that numbering. The one numeric table is `AxSmodeProbe.v:128`, and it is keyed on
  `accessKind`.
- The term structure of `checked_mem_read` changes: a new match sits in front of `read_kind_of_flags`.

**Why this is HIGH.** The whole Rocq weak tier is built on the opposite fact, which it states explicitly:
"rv64d NEVER emits `AK_ifetch`/`AK_ttw`" (`WeakInterp.v` §3, finding (1)). Specifically:

1. `WeakInterp.classify` maps `AK_ifetch` and `AK_ttw` to `ak_coh = true`. The arms were written to be
   unreachable.
2. The event language **needs `ak_coh = false` on every RAM read.** In `WeakEvLang.v:887` the MemRead arm
   of the step reads `ak_coh (classify …) = false /\ …`. `WeakSailLTS.v` (d) makes coherent reads a
   *stuck* arm. `sail_shaped` / no-coherent-reads (`WeakCompose.v` (6), `WeakShape*`) is discharged as
   "vacuous for rv64d".
   - On the new model, every fetch is coherent, so every instruction step is stuck in the language as
     ported.
   - Every walk also has coherent reads.
3. Finding F7: the fetch is treated as an *ordinary plain* read. It goes through `ewp_ev_load` /
   `read_ok`, and `WeakEvLift` §5c derives a cheap rule from the immutability of text.
   - This is pinned by closed facts. Examples: `WeakEvStarted.ev_fetch_plain` (`classify … = AkInfo false
     false false` by `vm_cast_no_check`) and `ev_fetch_req` (a concrete request literal).
   - `WeakFetchEff.wak_plain` is "what classify makes of the fetch", and 33 files use it for fetch and walk
     reads.
   - `WeakCert` deliberately quantifies over the fetch's `akinfo`, so its general certificates are robust.
     The concrete ones are not.
4. `WeakShapeMem` (a): `gwalk_read_ram_*` assume `rk ≠ Read_ifetch`, and §3 discharges that from the
   postcondition of `read_kind_of_flags`. On the new model it is false for fetches, and the call site's
   term has changed.

The Lean SC/TSO tier already uses the new kinds. `MachCSL/Lang.lean` and `MachCSL/TsoMem.lean` read
`AK_ifetch` as the hart's i-cache agent (`akIfetch`, `ifetchAgent`) and `AK_ttw` as a plain read (`akPlain`).
So the Lean model is internally consistent, and the weak port has to adapt to it.

## Options (owner decision)

- **O1 (recommended, small): keep the Rocq semantics in `classify`.** Map both `AK_ifetch` and `AK_ttw` to
  `AkInfo false false false`, which is exactly what the old model's `AK_explicit` plain classified to. Then:
  - Every *classified* event stream equals the Rocq one, so the certificates, ledgers and view arguments
    carry over unchanged.
  - Record it as a numbered Deviation in `Weak/WeakInterp.lean`.
  - Cost:
    - Restate the closed request literals (`ev_reqf` and similar) with the new `access_kind`.
    - Re-prove `WeakShapeMem` §1/§3 for the new `checked_mem_read` match. The hypothesis `rk ≠ Read_ifetch`
      disappears or flips.
    - Drop the "dead arm" claims.
  - Limitation: the weak model then keeps one *coherent hart-view* fetch. That disagrees with Lean
    `machInterp`'s separate i-cache agent. The `WeakBridge` and refinement statements must reconcile the
    two, probably by using the immutable-text argument (Rocq Decision 4).
- **O2: use the Lean semantics** (ifetch = i-cache agent that moves no view; ttw = plain or coherent).
  This is faithful to `MachCSL`, but it rewrites WeakEvLang's read arm, `WeakEvLift` §5c and every
  fetch-event leaf. This is the large redesign that §C.4 of the architecture note tries to avoid.
- Not an option: regenerating Lean at `c32fbf41`. The SC tier depends on `AK_ifetch`.

## Rocq weak files likely affected (grep of `xv6iris-spinlock/iris`)

- **Load-bearing for the "never emitted" claim:** `WeakInterp.v` (`classify`, §3), `WeakInterpProj.v`,
  `WeakSailLTS.v` (`no_coh_reads`, stuck arm), `WeakSailLTS2.v`, `WeakEvLang.v` (MemRead arm),
  `WeakCompose.v` (6), `WeakShape.v`, `WeakShapeMem.v` (`gwalk_read_ram_*`, `Read_ifetch` discharge),
  `WeakShapeWin.v`, `WeakShapeGen01–15.v` (generated, `sail_shaped`), `WeakShapeTop.v`,
  `WeakShapeOverrides{,2}.v`, `WeakSailComplete.v`, `WeakSailCone.v`, `WeakComposeLang.v`,
  `WeakEvAdequacy.v`, `WeakEvCapstone.v`, `KernelSitesDef.v`.
- **Fetch read is pinned to plain (F7, `wak_plain`):** `WeakEvStarted.v` (`ev_fetch_plain`, `ev_fetch_req`),
  `WeakEvLift.v` §5c, `WeakFetchEff.v`, `WeakFetch2.v`, `WeakFetchRvc.v`, `WkFetchPeel.v`, `WkStepPeel.v`,
  `WeakEvFunnel.v`, `WeakLeaf{Csrw,Itype,Jump,Ld8,Lw4,RegOnly,RtypeW,Sd8,SdspOff,Sw4,Tor,UtypeShift,Amo4Leaf}.v`,
  `WkEntryNew.v`, `AxFetch.v`, `AxRegOnly.v`, `AxRowConf.v`, `AxEpiChain.v`.
- **Walker reads (now `AK_ttw`):** `WeakWalkEff.v`, `WeakWalkStale.v`, `WeakKpt.v`, `WeakKptStale.v`,
  `WeakStale.v`, `WkWalkRule.v`, `WkWalkTails.v`, `WkWalkCapstone.v`, `WkUnmapMp.v`, `AxWalk*.v`,
  `AxPtProt.v`.
- **Concrete `AK_explicit` request literals or `exec_eff` traces at fetch or walk:** `WeakEvInst.v`,
  `WeakLeafBase4.v`, `WeakLeafEff8{,s}.v`, `WeakUpdEff.v`, `WeakLeafAmo4.v`, `AxDataX{,7,9}.v`, `AxOpsem.v`,
  `AxPair.v`, `AxLock3Prog.v`, `AxTokLedgerMp.v`, `AxSmodeProbe.v`.
- **Mention `read_kind_of_flags` at the `checked_mem_read` site:** 39 files, among them the SC `Wp*`, `UserMem*`
  and `Smode*` files. Lean has already re-proved those, so only their weak twins `WeakLeaf*`, `WeakShape*`,
  `WeakUpdEff` and `AxSpin*` need attention.

Robust under O1: the axiomatic certificate files (`AxCert*`, `AxSym*`, `AxEpi*` beyond the ones above,
`WeakCert.v`) branch on `ak_coh` symbolically. Under O1 they need only renaming.
