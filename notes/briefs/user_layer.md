# Brief: wave 9, proving `USER` (the user-mode machine layer)

Surveyed 2026-09-26 against `lean-v2` @ `f3ac4109f` (the system theorem `Xv6.xv6FsAdequacy_xv6GF
(US : USER) …` is proved) and `/shared/xv6rocq/iris` on `main` @ `1900b8a43`. The standing
rules are `notes/coord/wave7b_prompt.txt`, wave8_top.md §0, and the memory rules (Rocq is the
authority, one capacity instance per camera, root build before push, short Lean runs).
USER RULINGS in force: D24 (USER was a parameter until wave 9; it is to be PROVED now,
2026-09-26 ruling), and BootReset belongs to wave 9 (a sibling lane, §6.6, outside USER's cone).

> **DECISIONS PENDING (user).** Numbering continues from w8_5_final.md's D49. Each one has a
> recommendation.
>
> | # | decision | recommendation |
> |---|---|---|
> | **D50** | **The execution engine for ARBITRARY user instructions.** MachCSL's instruction leaves are `swp` proofs by symbolic execution (`swp_run`) of ONE known instruction. `USER` needs every instruction the decoder can produce, run at symbolic registers, with every outcome (retire, trap, illegal, fetch failure, wait). Rocq's post-port tower does not do this in Iris. Its walker `hmrun` (HartMemRun.v) runs a stretch of the model over the hart's OWNED registers and OWNED byte map. `swp_hmrun_of_exec` is proved ONCE, and every family fact is then a PURE `exec … = Some …` fact paired with a `goodmb` footprint certificate. Rocq's header says this cut about 4k lines of Iris plumbing. | **(a) Port Rocq's engine the Lean way.** Add a walker `runRW`, the write-capable sibling of MachCSL's `runRead`. It walks a register map inside a footprint and the owned byte map, and asks ∀-oracles for the wire pins and for instruction fetches. Prove `swp_runRW` once, by induction on `FreeM`. Rocq's PAIR (the `exec` fact plus its `goodmb` twin) then collapses into ONE equation, `runRW … m = some …`, which is both facts at once. All classification is pure Lean (`simp`/`split`/`bv_decide`). This also matches MachCSL's rule: "a function that only reads gets `swp_runRead` + `rfl`, never `swp_run`". (b) Lean-native `swp` leaves per instruction family (`execSpecF_*` generalised to every `ExecutionResult`). This reuses about 60 privilege-generic ALU leaves. But every fault and translation branch would then be split inside the proof mode, which is the shape Rocq abandoned. |
> | **D51** | **Model patch: the reservation hooks and the experimental-extensions flag.** In `model/Lean_RV64D/LeanRV64D/RiscvExtras.lean`, `load_reservation`/`cancel_reservation : … → SailM Unit` are AXIOMS. An opaque monadic term cannot be stepped, so `LR`/`SC` (and hence `USER`) cannot be proved. `sys_enable_experimental_extensions : Unit → Bool` is an axiom too, so decode gates on it are open. Rocq faced the same problem. Its pinned fork binds the two hooks to `returnM tt`, which is exact: the reservation set is not in the state (ResvAxioms.v, xv6iris_extras.v). Rocq's `riscv_extras.v:28` defines the flag as `false`. `match_reservation`/`valid_reservation` stay opaque (Rocq `Parameter`s) | **Patch in `tools/regen_sail_model.sh`**, as patches 1–5 already are: the two hooks become `pure ()` and the flag becomes `false`. That is Rocq parity. The axiom baseline loses 3 entries (notes/adequacy_axioms_baseline.md). Worktree, first thing merged |
> | **D52** | **The user tier's register footprint vs `userInv`.** Rocq's footprint (UserFrame.v `u_ro_list`) includes `mstateen0`, `sstateen0` (read by `stateen_allows_CSR_access` at every U-mode CSR instruction and by the decoder's gates) and `mhpmcounter` (the hpm-counter read path). Lean's `userInv` lacks all three: `mstateen0`/`sstateen0` sit in the kernel's `hartCsrs` (`KCtx.lean:706`), and `mhpmcounter` has no owner at all (not in `resetVal`, UserExec deviation 4). **As stated, `USER` is unprovable** for any footprint cell the user cycle reads but does not own. | **(a) Extend `userHwCells`** with the missing read-only cells, keeping UserExec deviation 1 (exclusive cells moved in and out by userret/uservec). `hartCsrs` hands `mstateen0`/`sstateen0` over. `mhpmcounter` is carved at boot into `hartCsrs`. This is a statement edit to UserExec/SpecUser. It ripples into `UserKernelBridge` (`userInv_of_sret`/`userTrapFrame_open`), the userret/uservec seams and BootCarveHart, all in one worktree. The FULL list comes from a footprint audit done first (§6, U0-D). (b) Reinstate Rocq's `hw_config`: freeze these cells as persistent `↦ᵣ□` after M-mode boot, and give `USER` its `hw_config -∗` premise back. That is cleaner and Rocq-literal, but it re-fractions `confCells` in every kernel rule |
> | **D53** | **The user-leaf pins in `uptWf`.** The config supports Svnapot, Svpbmt and Svadu (`PlatformConfig.hartSupports`), so a user leaf with `N=1` or `PBMT≠0` walks differently. Rocq's `upt_map_wf` pins every leaf, at every A/D variant, as valid, leaf, no-NAPOT and PBMT=0. Lean's `uptWf` only has `isLeafPte ∧ pageValid`, so those pins are REQUIRED either way. The G bit is a real choice. Lean's `utlbOk` states the entry as `tlbEntryOf …` with `global := false`, and the model fills `global` from the walk's G bits. W8-M's review note asks for G=0 in `uptWf`. Rocq instead carries the walk's G into the entry (`CommonWalk.u_walk_entry`, `u_global`) | **(a) Add `G=0` to `uptWf` in the same edit as the NAPOT/PBMT pins** (W8-M's note). It is one conjunct at every `uptWf` producer (literal perms: `bv_decide`). It also keeps `tlbEntryOf`, and therefore TransPt's `tlbOk2` and the kernel's `tlbOk`, unchanged. Recorded as a deviation from Rocq. (b) Rocq's `u_global` in `utlbOk`. That leaves `uptWf` at the NAPOT/PBMT pins only, but generalises `tlbEntryOf` and touches TransPt |
> | **D54** | **Where the tower lives.** Rocq keeps all ~70k lines in one flat `iris/`. Nearly all of it is generic to the machine, not to xv6: the walker, the six-arm U cycle, U dispatch, the U→S trap tower, Sv39 translation with faults over an owned tree, U fetch, the memory arms, the execute totality, decode totality. The xv6-specific part is the config values (`MEDELEG_S`, `MIE_S`, `MENVCFG_S`, `mcounteren = 2`, `scounteren = 0`, `senvcfg = 0`, `xv6Pmpcfg`), the `UPtd` shape (trampoline and trapframe leaves with U=0), and `userInv`/`userTrapFrame` | **Generic engine in `MachCSL/U*.lean`** (worktree lanes, new files), stated over MachCSL's resources and a pure record of the frozen config values. **The xv6 instantiation goes in `Xv6/User*.lean`** (main tree): the frame bridge, the classification closers, the Löb loop, `ProofUser`. This follows the user's framework/xv6 separation rule. The alternative is everything under `Xv6/` |

## 0. Findings that shape the plan (read first)

1. **`USER` is used in one place and can be discharged in one line.** `SystemAdequacy.lean`
   takes `US : USER` only through `LinkUexecWp.UexecGen`/`ProofUexecWp.uexecWp_gen`. Proving
   `userProof : USER` (Xv6/ProofUser.lean) and instantiating `xv6FsAdequacy_xv6GF userProof …`
   gives the `USER`-free theorem. `#print axioms` should then be Lean core, the Sail platform
   externs minus D51's three, and the `bv_decide` family.
2. **The Rocq cone that is USER-ONLY is about 43k lines in 35 files.** It sits on about 27k more
   lines of machine base that Rocq's kernel also uses, but whose Lean analogues are
   success-path-only or absent (§1.3). `SpecUser.v`/`ProofUser.v` are 81 lines each. The
   `Umode*`/`WpUmode*`/`Uk*` files (≈13.5k + the Uk* forest) are NOT in USER's cone. They verify
   specific user PROGRAMS (sh, cat, grep), which is the application track (D48), not USER.
3. **MachCSL has no failure paths.** Every Lean cycle rule (`wpLoop_s_base/rvc/instr`, `wpLoop_sT_*`,
   `WpCycle`) takes `Step_Execute (Retire_Success …)` only. Every translation rule
   (`swp_translateAddr_own/_via`, `swp_pt_walk_kpt/_own`) takes a successful kernel-shaped leaf
   (`kLeaf`, `kernelAccess`). The only trap is a SUPERVISOR interrupt taken in S
   (`swp_handle_interrupt_S`). The only waiting rule is S-mode `wfi` with interrupts off
   (WpSmodeWait). The only instruction fetch reads never-written image bytes
   (`swp_sail_mem_read_ifetch` over `imgBytes`). `USER` needs every one of those in its general
   form at User privilege.
4. **The KTier question from wave 8 does not come back.** W8-M ran the trampoline over an
   ABSTRACT translation resource (`WpSmodeCycleT`/`WpSmodeSatpU`/`WpPtWalkOwn`), not a new
   `KTier`. The user tier has its own frame (Rocq `UserFrame`: every GPR, PC/nextPC,
   hart_state, cur_privilege, mstatus, the trap CSRs, the clock cells and the TLB writable, the
   config read-only), so `KTier`/`SConfPhys` need no change.
5. **Same model, same config.** Lean's `SAIL_RISCV_REV` is `070832a1…` and the config file is shared
   with Rocq's `model-xv6iris/`. So Rocq's decode image (`DecodeSetU.decodable_u`, about 50
   instruction families) and the misaligned-access structure (UserMemMis: page split in vmem,
   MAG split in checked_mem) carry over as they are. Extensions live at U include A (plus Zacas
   and Zabha), C (plus Zcb), M, Zicond, Zbc/Zbkb/Zbkc/Zbkx, Zicbo{m,z,p}, Zimop/Zcmop, Zawrs
   (`WRS` puts the hart in `HART_WAITING`), Zihint*, Zicntr/Zihpm (illegal under the counter
   enables), and Sstc (the S timer interrupt from `stimecmp`). F/D/V decode to nothing live at
   U (FS = VS = Off), and Zicfilp/Zicfiss are gated off by `senvcfg = 0`.
6. **The icache needs no stamp for USER.** User fetches go through the non-coherent instruction
   view (TsoMem `itv`), so a user fetch of its own freshly written bytes may be stale. For SAFETY
   that does not matter: the fetched bytes are ∀-quantified, and any decode is handled. So
   UserExec deviation 7 (`userPtInvX = userPtInv`, no `UmodeText` stamp) stands for `USER`. The
   stamp matters only for proving specific programs (the application track). MachCSL does need
   ONE new leaf here: an ifetch of context-owned bytes answers some value at some readable view.
7. **The seam is already the right shape.** `SpecUser.wpUserExecClosedBody` is Rocq's body minus
   the `hw_config`/`minstret_inv` wands (see D52), with the `Rut` accessor lending `ctxToken`
   per step. `UserKernelBridge.wpLoop_userret_sret` consumes it. Nothing on the kernel side
   changes, except D52's footprint cells and D53's `uptWf` conjuncts.

## 1. Rocq's proof of USER

### 1.1 The top

`ProofUser.v` (81): `Module UserProof : USER`. It instantiates `UserTotalU`'s two execute
totalities (`base_exec_total_u_holds`, `rvc_exec_total_u_holds`, both PURE `Prop`s) with the 19
proven memory arms: 6 base (LOAD/STORE from UserMemArmsBase, LOADRES/STORECON/AMO from
UserMemArmsA, ZICBOP from UserMemClassifyAmo) and 13 compressed (UserMemArmsC). It then applies
`UserActiveClass.wp_user_exec_full`:

```
wp_user_exec_full : (∀ va mi, base_exec_total_u pt va mi) → (∀ va mi, rvc_exec_total_u pt va mi) →
  hw_config -∗ minstret_inv -∗ wire_inv -∗ user_inv C pt Rut -∗ ▷ stvec_handler_wp C pt Rut -∗ WP Loop
```

`wp_user_exec_full` = `UserStep.wp_user_exec_active` (Löb; `user_step_obligation_holds` does the
WAITING hart, i.e. WRS stay/wake) applied to `UserActiveClass.active_class_intro` (the ACTIVE hart:
a case tree over `va` routing every fetch geometry to a producer, then dispatch → fetch → decode →
execute → the four trap towers, closed through `UserStepFull.wp_user_step_active`, which drives the
ONE six-armed cycle rule `HartStepFull.swp_exec_step_full` at the user footprint).

### 1.2 The cone, by layer (Rocq line counts; `ProofUser`'s import cone is 153 files / 150k lines, most of it the language itself)

| layer | Rocq files (lines) | generic / xv6 | Lean today |
|---|---|---|---|
| **L1 engine**: interpreter, walker, cycle | RiscvExec 1643 (`exec`), RiscvTryStep 1571 (`execR`, `try_step` reductions), HartSpan 810 (`hfrun`), HartSpanChar 302, HartEvents 1136, HartGoodb 237, WpDecodeBridge 288 (`goodb`), **HartMemRun 2004** (`hmrun`, `goodmb`, `swp_hmrun_of_exec`), **HartMemAsm 885** (`gm_*` bind toolkit), HartRunGen 539, **HartRunFull 1116** (fetch-shape-generic `run_hart_active`, U dispatch), HartStepAny 691, **HartStepFull 1072** (six arms + waiting hart), HartLift/Lift2 1195, HartSwp 473, HartRegNode 398. Σ ≈ 14.4k | generic | `Wp.lean` (`swp`, per-event rules, `wpHart_lift`), `DecodeBridge` (`runRead`/`swp_runRead` = goodb), `WpCycle`/`WpSmodeCycle(T)` (success only), `WpSmodeWait` (S `wfi`, SIE off). **Missing: the write-capable walker, the six-arm cycle, the waiting hart at U with dispatch** |
| **L2 decode** | DecodeTotalU 296 (every 32-bit word decodes, read set `D_u` = priv, misa, menvcfg, senvcfg, mstateen0, sstateen0), DecodeSetU 671 (`goodbP`, the set `decodable_u`). Σ ≈ 1k | generic at a U reference config | **missing** (Lean has per-word `decodes32_bridge` only) |
| **L3 walk & translation** | PtTree 2587, CommonWalk 1682 (`u_walk_entry`), PtTreeAdue 2613 (Svadu write-back), SmodePte 528, Pt4kWalk 762, PtAdBits 580, **PtWalkCert 3223** (goodmb twins of the walk), PtBytes 351, MemAccessGen 1013 (the MAG split). Σ ≈ 13.3k | generic | `PtTree`, `Pte`, `WpPtWalk` (kernel, shared table), `WpPtWalkOwn` (owned table, success, kernel-shaped leaves), `Translate`. **Missing: U permission checks, all fault paths, NAPOT/PBMT pins, pure forms, the MAG split** |
| **L4 user address space** | UptTree 921 (`utlb_inv_pt`, `upt_map_wf`), UserPtTree 2187 (`user_pt_inv` + the Iris translate/fault lemmas), UserBits 645, UserTranslate 76, **UserBytes 912** (the byte-map view: `u_mem_wf`, `u_mem_step`), **UserFrame 1154** (the footprint, `u_Df`, the frame bridge), UserExec 665, TrampPt 71. Σ ≈ 6.6k | mixed: the shapes are xv6 (`uptd`, tramp/tf leaves); the rest is generic | `UserExec` (412, the vocabulary), `UPtDefs`, `UptTree` (219, kernel-side subset), `UptWalkTramp`, `TransPt`, `UserKernelBridge`. **Missing: UserBytes, UserFrame, the U-side of UptTree/UserPtTree** |
| **L5 fetch & memory** | UserFetch 466, UserFetchPt 23, **UserFetchCert 1489**, **UserFaultCert 1342**, UserMemPt 1178, **UserMemAccess 2212** (vmem, LR/SC reservation), **UserMemMis 3511** (misaligned: page split and MAG chunks), **UserMemCert 2894**, UserMemArms 1839, UserMemArmsBase 1161, UserMemArmsC 1031, UserMemArmsA 1430 (LR/SC/AMO), UserMemClassify 260, **UserMemClassifyAmo 2086** (AMO + ZICBOP), UserMemTotal 159, ResvAxioms 91. Σ ≈ 21.2k | generic | **missing** |
| **L6 execute totality (register-only)** | UserExecFacts 2133 (ECALL/EBREAK trap; MRET/SRET/WFI/sfence family illegal), UserCsr 2114 (CSRReg/CSRImm at U: a counter read if enabled, else illegal), UserClassify 67, UserClassifyAsm 602 (the pair convention, `u_exec_pins`), **UserTotalU 2702** (the two dispatch tables; pure), ZicondGpr 85. Σ ≈ 7.7k | generic (config-pinned) | **missing** (the ≈60 privilege-generic `execSpecF_*` ALU leaves are Iris, success only) |
| **L7 trap, step, assembly** | UserStep 785 (U dispatch, WAITING arm, Löb), **UserTrap 1577** (cause-generic U→S tower, `utrap_ms`), UserStepFull 305, **UserActiveClass 2610** (the case tree), WpIntrCore 1061 (the S twin). Σ ≈ 6.3k | UserTrap and dispatch are generic; the assembly is xv6-shaped (`user_inv`) | `WpTrap` (S interrupt from S only), `UserKernelBridge` (the sret seam). **Missing: the U trap tower, U dispatch, the assembly, Löb** |
| **L8 seal** | SpecUser 81, ProofUser 81 | xv6 | `SpecUser` (65) landed; `ProofUser` missing |

The USER-ONLY 35 files (what nothing else in the final theorem imports) total 42,940 lines.
UserMemMis, PtWalkCert, UserMemCert, UserTotalU, UserActiveClass, UserMemAccess, UserExecFacts,
UserCsr, UserMemClassifyAmo and UserMemArms are the ten largest.

### 1.3 Rocq's big ideas (to keep; "never reinvent")

1. **Per-node stepping, with the hart owning its whole footprint.** A user hart owns every register
   its cycle touches (the writable set `u_rw_list` plus 31 GPRs, and the read-only set `u_ro_list`)
   and every byte it can reach (the tree and the pages), so no other hart can interfere with a
   cycle. The only shared inputs are the two PLIC wire pins, which are answered by ∀.
2. **One six-armed cycle rule** (HartStepFull), with `Q` indexed by the `Step` so the caller can
   tell retire from trap from wait. Plus the waiting-hart rule. `Enter_Wait` is the arm with a
   different post-file (no tick of the PC).
3. **One cause-generic trap tower** (UserTrap): interrupts and exceptions write the same register
   sequence. Only `scause`/`stval` differ. SPP := U.
4. **Classification is below Iris** (UserClassifyAsm header). The totality facts are pure `Prop`s
   at a reference state `(rs, mm)`: the frame's register file and the owned byte map. The Iris
   side is ONE rule. Their post-state says exactly: registers agree off `{nextPC, GPRs, tlb}`,
   and the byte map moved only by `u_mem_step` (data at the same domain, and a same-shaped tree
   for the A/D write-back).
5. **The fetch geometry is a case tree over `va`**: 4-aligned, 2-aligned, a page straddle, odd, a
   fault. The decode image is an explicit set.
6. **The memory arms go by PAGE, not by chunk.** vmem splits at most two ways at a page
   boundary, and the MAG split is a pure computation under one translation.
7. **The fault walk does not move the state.** No TLB fill and no A/D write-back happen on any
   fault arm, so fault facts are pure and state-preserving.

## 2. What Lean/MachCSL has vs needs

### 2.1 Machine layer (MachCSL): gaps, in dependency order

| # | need | Rocq source | Lean status |
|---|---|---|---|
| G1 | **Model patch** (D51): `load_reservation`/`cancel_reservation := pure ()`, `sys_enable_experimental_extensions := false` | ResvAxioms, xv6iris_extras, riscv_extras:28 | axioms; blocks LR/SC and the decode gates |
| G2 | **`runRW` walker + `swp_runRW`** (D50): register map in a footprint `(Dr, Dw)`, owned byte map (ctx bytes read EXACTLY, stores stamped as `ctx_store`, the exclusive pair as `ctx_store_excl`/`ctxBytes_exclReadAU` in WpPtWalkOwn), silent events, ∀-oracles for the wire pins (`swp_readReg_any`) and the ifetch reads (G5); refuses MMIO; `laterIf`-style laters; bind/seq combinators (Rocq HartMemAsm `gm_*`, the left-nested variants, `catch_early_return`) | HartMemRun, HartMemAsm, HartSpan | `runRead`/`swp_runRead` (read-only) is the template (DecodeBridge.lean) |
| G3 | **The six-arm U cycle** (`try_step` with Retire / Trap / Illegal / Fetch_Failure / Pending_Interrupt / Enter_Wait; `Q` indexed by `Step`), and the **waiting hart at U** (WRS stay/wake with interrupt dispatch) | HartRunFull, HartStepFull, RiscvTryStep, UserStep §2 | success-only cycles; WpSmodeWait is S-only with SIE off |
| G4 | **U dispatch** (unmaskable at U: `mstatus` is not read; M set empty by `uc_mm`; wires ∀) and the **cause-generic U→S trap tower** (`handle_interrupt`/`exception_handler`/`handle_exception` at `del_priv = S` through `medeleg`/`mideleg`; `utrap_ms`) | HartRunFull §1, UserStep, UserTrap, WpIntrCore | `swp_dispatchInterrupt_S`, `swp_handle_interrupt_S` (S→S interrupt only) |
| G5 | **Ifetch of context-owned bytes** answers ∀ a value readable at a view ≥ `itv` (Finding 6) | (TSO icache; Rocq UserFetchCert reads the map) | only `swp_sail_mem_read_ifetch` over `imgBytes` |
| G6 | **Decode totality at U**: `drefU` (Rocq `D_u`: priv, misa, menvcfg, senvcfg, mstateen0, sstateen0), a leaf-predicate walk `runReadP`, and `∀ w, runReadP drefU decodableU (decode w)` for 32- and 16-bit words | DecodeTotalU, DecodeSetU | per-word `decodes32_bridge` |
| G7 | **Sv39 translation at U over an owned tree, pure**: satp mode/ASID pins, non-canonical va fault, TLB hit (U-bit + R/W/X + MXR/SUM check), miss → walk (invalid at any level, leaf at level 0, permission denied), the Svadu A/D write-back, the fill; PMP at U (xv6Pmpcfg TOR entry 0); PMA; `utlbOk`/`ptRep` preservation | CommonWalk, PtTreeAdue, Pt4kWalk, PtAdBits, PtWalkCert, UserFaultCert, UserFetchCert §6, UserMemPt §2–3, UptTree, UserPtTree | WpPtWalkOwn does success for kernel-shaped leaves; `uptTlbOk_after`, `uptPtRep_setLeaf` exist |
| G8 | **U fetch**: the geometry tree (4-aligned; 2-aligned RVC; the 2+2 straddle, possibly across a page; misaligned; fetch faults → `F_Error` → `Step_Fetch_Failure`) | UserFetch, UserFetchCert, UserFaultCert, UserActiveClass | kernel fetch shapes (`fetchSpecS_*`, `…X`) over known words |
| G9 | **U memory arms**: vmem read/write (aligned, page split, MAG chunking), LR/SC (reservation in `ctxTok`, `match_reservation` split both ways; misaligned LR/SC → access fault), AMO (+Zacas, Zabha), CBO (cbo.zero/clean/flush illegal under `senvcfg=0`/`menvcfg`; ZICBOP a no-access hint), the 13 compressed forms | UserMemAccess, UserMemMis, UserMemCert, UserMemArms*, UserMemClassify(Amo), MemAccessGen | kernel `execSpecF_ld/sd/lw/…` at known cells; `WpSmodeAtomic` (amoswap on shared cells) |
| G10 | **U execute totality, register-only**: every `decodableU` family's outcome (ALU/M/Zbc/Zbk/Zicond/shifts; JAL/JALR/BTYPE with the misaligned-target trap; LUI/AUIPC; FENCE/FENCE_TSO/FENCEI/PAUSE/NTL; ECALL/EBREAK → Trap; MRET/SRET/WFI/SFENCE*/SINVAL → Illegal; CSR at U; WRS → Enter_Wait; Zimop/Zcmop; ILLEGAL) | UserExecFacts, UserCsr, UserTotalU, ZicondGpr | ≈60 `execSpecF_*` (Iris, privilege-generic, Retire only). They can serve as cross-checks, but D50(a) restates them as `runRW` facts |

### 2.2 Xv6 layer: gaps

| # | need | Rocq source | Lean status |
|---|---|---|---|
| X1 | **The footprint audit and statement fix** (D52): the full list of registers a U cycle reads, checked against `userInv`/`userCfg`/`clockCells`; add the missing cells; re-close `userInv_of_sret`/`userTrapFrame_open` and the userret/uservec seams | UserFrame `u_rw_list`/`u_ro_list`/`u_Df` | known gaps so far: mstateen0, sstateen0, mhpmcounter |
| X2 | **`uptWf` pins** (D53) and their producers (uvmalloc/uvmcopy/kexec/mappages sites; 48 files mention `uptWf`, but only the producers change) | UptTree `upt_map_wf` | `isLeafPte ∧ pageValid` only |
| X3 | **The byte-map view** of `userPtInv` (the tree's bytes + `umPages` as ONE owned map; `uMemWf`, `uMemStep`; same-shape trees across A/D) | UserBytes | none (`umPages` is a big-sep over pages) |
| X4 | **The frame bridge**: `userInv` ⇄ (reference register map within the footprint, owned byte map, `ctxToken` borrowed from `Rut`), and the closers back to `userInv` / `userTrapFrame` | UserFrame, UserStepFull `u_open`/`u_close_inv` | `uRegs_uvRegs` & co. only |
| X5 | **The classification**: the pure `baseExecTotalU`/`rvcExecTotalU` over the decode set, the memory closers, and the `va` case tree | UserClassifyAsm, UserMemTotal, UserTotalU, UserActiveClass | none |
| X6 | **The loop**: `userStepObligation(Active)`, the waiting arm, Löb → `wpUserExecClosedBody` | UserStep §2–3, UserExec | `SpecUser` statement only |
| X7 | **The seal**: `ProofUser.userProof : USER`; the USER-free final corollary; the axiom re-measure | ProofUser, SystemAssumptions | none |

## 3. Design notes (for D50(a); settled in the U0 spikes)

- **`runRW` signature** (sketch): `runRW (fuel?) (Dr Dw : Register → Bool) (rs : RegFile) (mm : PAddr
  → Option (BitVec 8)) (orc : Oracle) : SailM X → Option (X × RegFile × (PAddr → Option (BitVec 8)) ×
  Bool)`. `FreeM` is inductive, so no fuel is needed (structural, as `runRead`). `Oracle` answers
  `sig_meip`/`sig_seip` reads and ifetch reads. `swp_runRW` quantifies over it:
  `(∀ orc, runRW … orc m = some (x, rs', mm', b) → …Φ x…) ⊢ swp cpu m Φ` under the owned
  footprint cells, the `ctxBytes` of `mm`'s domain, and `ctxToken` (the reservation fragment).
  Rocq's two premises `reg_agree_on` / `mm ⊆ mem` become reflexivity at the reference state, as
  in Rocq.
- **The PAIR collapses.** Rocq states `exec X s = Some (r, s')` and `goodmb Dr Dw X s mm = true`
  separately, because `exec` pre-dated the per-node engine. In Lean the walker's `some` IS the
  certificate, so one equation per fact. Rocq's `gm_*` combinators become `runRW_bind`/`_seq`
  simp lemmas.
- **Performance rules**: unseal `hartSupports`/`currentlyEnabled` as the decode bridge does. One
  family per theorem (the dispatch's 22-way-arm rule from wave 8, risk 6). Use `bv_decide` for
  bit-field side conditions. Never let a `simp` see the whole `execute` match. Budget: no theorem
  over a few seconds.
- **The frozen config** is a pure record (`UConf`: misa, menvcfg, senvcfg, medeleg, mideleg,
  mie, the counter enables, mstateen0/sstateen0, pmpcfg/pmpaddr, pma, …) that MachCSL's U files
  are generic in. Xv6 instantiates it at `sConfOf`/`userHwCells`'s values.

## 4. Sizes (Lean estimates)

Under D50(a) Rocq's pairs collapse, and MachCSL already has the per-event rules, `runRead`, the
owned-walk success leaves and the TLB lemmas. Expect **≈ 28–38k Lean lines** (Rocq's
comparable L1–L8 slice is ≈ 71k). Per lane: G2 ≈ 1.5k, G3+G4 ≈ 3k, G5 ≈ 0.3k, G6 ≈ 1–1.5k,
G7 ≈ 4–5k, G8 ≈ 2k, G9 ≈ 8–10k, G10 ≈ 5k, X1+X2 ≈ 1–2k of edits, X3+X4 ≈ 3k, X5 ≈ 3–4k,
X6+X7 ≈ 1k.

## 5. Risks

1. **Decode totality over a symbolic word (G6).** The Lean decoder is the generated backwards
   `encdec` (and a noncomputable compressed matcher). A linear symbolic walk with the leaf
   predicate may be slow to elaborate. Spike first (U0-C). The fallback is a per-opcode-major split
   (the 7-bit opcode is 128 concrete cases, each walked by `rfl` over the remaining symbolic fields).
2. **`runRW` at symbolic state (G2).** If `simp` over the model's do-blocks is slow, the whole
   D50(a) plan pays for it. Spike on one ALU op, one load and the trap tower before fanning out
   (U0-B). D50(b) is the retreat.
3. **Footprint surprises (X1).** Every missing cell is a SpecUser statement change that ripples
   into already-proved kernel seams. So the audit runs FIRST, before any lane codes against
   `userInv`.
4. **Misaligned accesses (G9).** UserMemMis is Rocq's biggest file. Give it its own lane, and keep
   the MAG chunk plan pure.
5. **Reservations.** LR's reservation must ride `ctxTok` (UserExec deviation 3), and SC splits on
   `match_reservation` both ways. Other harts are blocked by the TSO reservation rule, not by
   the proof.
6. **Build hygiene.** New MachCSL files are cheap, but `Lang`/`Wp`/`Ctx` edits (if G2 needs one)
   re-build everything. Additive leaves go in NEW files (Rocq's own rule, PtWalkCert header).

## 6. Agent split

Conventions: wave7b_prompt.txt. Worktree lanes branch off `origin/lean-v2`, run the full
`lake build Xv6 MachCSL` + `tools/check_layering.sh` + a sorry grep per commit, and commit
unpushed. Main-tree lanes add NEW files only, build their modules, and report imports. GCP VM
builds as in the prompt. Every MachCSL lane is NEW files (`MachCSL/U*.lean`), so the lanes stay
disjoint. Only U0-M and U0-S edit existing files.

### 6.1 Wave U0 (start now, parallel)

| lane | tree | files | size | notes |
|---|---|---|---|---|
| **U0-M** model patch | worktree | `tools/regen_sail_model.sh` (patch 6), `model/Lean_RV64D/LeanRV64D/RiscvExtras.lean`, `notes/adequacy_axioms_baseline.md` | ≈50 + regen | D51. Merge FIRST: G9's LR/SC and G6's gates need it |
| **U0-B** walker spike | main (new) | `MachCSL/URunRW.lean` (`runRW`, `swp_runRW`, bind toolkit), `MachCSL/URunRWDemo.lean` (one RTYPE, one aligned LD over an owned page, one ECALL through the trap tower, timings) | ≈1.5k | D50 go/no-go. Report the timings |
| **U0-C** decode spike | main (new) | `MachCSL/UDecode.lean` (`drefU`, `runReadP`, `decodableU`, `decodeU_total32/16`) | ≈1–1.5k | risk 1 |
| **U0-D** footprint + statement fix | worktree | audit note (in the report); edits to `Xv6/UserExec.lean` (`userHwCells`), `MachCSL/KCtx.lean` (`hartCsrs`), `Xv6/UserKernelBridge.lean`, userret/uservec seams, `Xv6/BootCarveHart.lean` (mhpmcounter); and D53's `Xv6/UPtDefs.lean` `uptWf` pins with its producers | ≈1–2k of edits | D52 + D53. **Serial and invasive.** Merge before U2 lanes code against `userInv` |
| **U0-T** dispatch + trap tower | main (new) | `MachCSL/UDispatch.lean` (U dispatch), `MachCSL/UTrap.lean` (cause-generic U→S tower, `utrapMs`, `trapMstatusOk_utrapMs`) | ≈1.5k | `swp`-native stage lemmas, like WpTrap. Independent of D50 |

### 6.2 Wave U1 (after U0-B's go; U0-M merged)

| lane | tree | files | size |
|---|---|---|---|
| U1-C cycle | main (new) | `MachCSL/UCycle.lean` (six-arm `try_step` at U, `Q` by `Step`), `MachCSL/UWait.lean` (waiting hart at U, WRS stay/wake/trap) | ≈2–2.5k |
| U1-P translation | main (new) | `MachCSL/UWalk.lean` (owned-tree walk, pure: invalid/leaf/perm/Svadu), `MachCSL/UTlb.lean` (hit/miss/fill, `utlbOk` preservation), `MachCSL/UTranslate.lean` (`translateAddr` at U: canonical check, success/fault, PMP/PMA at U), `MachCSL/UFetchMem.lean` (G5 ifetch leaf) | ≈4–5k (two agents: walk+TLB / translate+PMP+ifetch) |
| U1-X1 exec ALU | main (new) | `MachCSL/UExecAlu.lean` (I/M/Zbc/Zbk/Zicond/shifts/LUI/AUIPC + compressed ALU forms) | ≈2k |
| U1-X2 exec control | main (new) | `MachCSL/UExecCtl.lean` (JAL/JALR/BTYPE + misaligned-target trap, fences, ECALL/EBREAK, the privileged-illegal family, WRS, Zimop/Zcmop, ILLEGAL) | ≈1.5k |
| U1-X3 exec CSR | main (new) | `MachCSL/UExecCsr.lean` (CSRReg/CSRImm at U, stateen and counter-enable gates) | ≈2k |
| U1-F frame | main (new) | `Xv6/UserBytes.lean` (X3), `Xv6/UserFrame.lean` (X4) | ≈3k; after U0-D |

### 6.3 Wave U2 (after U1-P)

| lane | files | size |
|---|---|---|
| U2-F fetch | `MachCSL/UFetch.lean` (geometry tree; straddle; faults → `F_Error`) | ≈2k |
| U2-M1 aligned vmem | `MachCSL/UMemAccess.lean` (aligned LOAD/STORE, the width-generic physical access; LR/SC) | ≈3k |
| U2-M2 misaligned | `MachCSL/UMemMis.lean` (page split + MAG chunks, pure) | ≈3k |
| U2-M3 AMO/CBO | `MachCSL/UMemAmo.lean` (AMO incl. Zacas/Zabha, CBO, ZICBOP) | ≈2–3k |
| U2-M4 arms | `MachCSL/UMemArms.lean` (execute-level LOAD/STORE/LR/SC/AMO + the 13 compressed forms, over M1–M3) | ≈1.5k; after M1–M3 |

### 6.4 Wave U3 (the assembly; after U1-C, U1-X*, U1-F, U2-*)

| lane | files | size |
|---|---|---|
| U3-A classification | `Xv6/UserClassify.lean` (the pure totality over `decodableU`: register-only table + memory closers, Rocq UserClassifyAsm/UserMemTotal/UserTotalU), `Xv6/UserActiveClass.lean` (the `va` case tree → `userStepActive`) | ≈4–5k (split the two tables across two agents if they exceed ~2k each) |
| U3-L loop | `Xv6/UserStep.lean` (`userStepObligation(Active)`, the waiting arm, Löb → the body) | ≈1k |

### 6.5 Wave U4 (the seal)

`Xv6/ProofUser.lean` (`userProof : USER`). A USER-free corollary goes in
`Xv6/SystemAdequacyClosed.lean`: `xv6FsAdequacy_xv6GF userProof …`, then `#print axioms`, then an
update to `notes/adequacy_axioms_baseline.md` and STATUS. It needs the full root build before
the push. Size ≈0.2k.

### 6.6 Sibling lane (wave 9, not in USER's cone)

**BootReset** (the user ruling): Rocq's symbolic Sail boot run proving the reset values, which
retires MachCSL's trusted `resetVal`/`bootFacts` table. It is independent of every lane above, so
it can run whenever a slot is free.

### 6.7 Order and the critical path

U0-M ∥ U0-B ∥ U0-C ∥ U0-D ∥ U0-T → (U0-B go) U1-P ∥ U1-X1..3 ∥ U1-C ∥ (U0-D merged) U1-F →
U2-F ∥ U2-M1..3 → U2-M4 → U3-A ∥ U3-L → U4.

The critical path is U0-B → U1-P → U2-M1/M2 → U2-M4 → U3-A → U4, which is the translation and
memory tower, as in Rocq. With the pipeline kept full, that is about 7–9 lane-rounds.

## 7. Report (per agent)

As in wave7b_prompt: files/commits, contract shapes (old → new for edits), the Rocq lemmas
mirrored, deviations, cleanups with checked uses, reused names, and what is left. U0-B and
U0-C also report per-theorem timings and a go/no-go for D50(a).
