> **USER RULINGS (2026-09-26):** DU1 = only union_adequacy_closed's cone, pinned to Rocq 1900b8a43. DU3/DU4 = Lean's approach (per-program text tables decoded in proofs; printf once, load-address-parametric) — user has slight doubts, so SPIKE FIRST (putc/printf) and fall back to Rocq's structure if it fails. DU8 = general parser walk only; per the cone audit (union_cone.md §2) the old walks are still used at the pin, so REPOINT sh's echo arm (rewire via RefParseBridge.ref_parsecmd_nosym) and the N-stage pipeline layer (new N-stage bridge proof) at the general parser, record as a deviation, and DROP the 12 old-walk files (user ruling 2026-09-26). DU9 = classical where possible. DU2/DU5/DU6/DU7/DU10 = coordinator adopts the recommendations.

# Brief: UNION ADEQUACY — the plan (Rocq `UInitUnion.union_adequacy_closed` in Lean)

Surveyed 2026-09-26 against `lean-v2` @ `f3ac4109f` and `/shared/xv6rocq` `main` @ `1900b8a43`
(post-seccomp S5b, with user-once A1–A3 and C1 integrated). Read-only survey: no Lean file was
edited. The standing rules are `notes/coord/wave7b_prompt.txt`, w8_5_final.md's rulings (D46–D49) and
the memory rules (one function per file, one instance per camera, Rocq is the authority but drop its
gunk, keep Lean runs short, root build before push).

Sizes below are Rocq line counts (`wc -l`). The cone comes from a `Require` closure
(scratch script). Rocq's import blocks are copied verbatim ("trimmed imports have OOM'd"), so the cone
is an UPPER bound. Agent U0-X measures the real one.

> **DECISIONS PENDING (user).** These are numbered DU1–DU10 so they do not collide with user_layer.md,
> which is being drafted in parallel. The coordinator assigns global D-numbers when both briefs are
> ruled. Each decision carries a recommendation.
>
> | # | decision | recommendation |
> |---|---|---|
> | **DU1** | **The Rocq reference and the scope.** Rocq is still moving: user-once B1/B2/C2/C3 are open, and the *.txt widening and the grep stage landed this week. | **Pin the port to Rocq `1900b8a43`.** Port only the cone of `union_adequacy_closed`. Do NOT port: the tree application and its theorem (audit "tree 13"), `UexecCond`'s sync/echo generic-entry gate (`UkSync`/`UCodeSync`/`USyncKernel`; the union never uses it), or the deleted file/pipe/echo application theorems. Re-survey Rocq drift only at wave boundaries (§5 W-end). |
> | **DU2** | **Where the Lean union meets the verified-user ENGINE.** The engine is the Sail-facing, value-precise per-instruction leaves (Rocq `WpUmode*`, `Umode{Fetch,FetchX,Mem,Text,Regs,Cap}`, `UkStep`, `UkLeaf`, `UkLoad`, `UkStore`, `UkLoadText`, `UkBranch`; about 21k). It is built on USER's INTERNAL tower (`UserTotalU`, `UserMem*`, `UserStep*`, `UserTrap`, `UserExecFacts`, `DecodeTotalU`, …), not on the `USER` theorem. | **(a) One interface structure `Xv6/SpecUkLeaves.lean` (`structure UK_LEAVES : Prop`).** It states the per-instruction leaves (UkLeaf/UkLoad/UkStore/UkLoadText/UkBranch forms plus `wp_uk_ecall`) against Lean's landed `uvb`/`ukc` (UexecRet). The union lane writes the statements first. **The user_layer lane OWNS the proof** (`LinkUkLeaves`), because it is the same Sail work over the same tower. Until it lands, the union theorem takes `UL : UK_LEAVES` beside `US : USER` (the D24 pattern). Everything from `UkRun` up is the union lane's. (b) The alternative is waiting for the user tower: that serialises about 190k Rocq lines of program proofs behind it. |
> | **DU3** | **The code catalogs.** Rocq's `UCode{Cat,Grep,Init,Seccomp,ShK,ShM,ShP,Echo}` (about 48.4k lines) are GENERATED per-instruction `uinstr` lemmas (`tools/gen_ucode.py`). Lean's kernel proofs have no catalog: they use a text tree (`tools/gen_text_tree.py`, `KernelText`) plus decode-at-proof-time tactics. | **(a) Lean-native.** A generator emits per-program user text trees from the 7b2c1b1b ELFs. One generic lemma gives a text-heap fetch from the tree, and the step tactics decode in the proof, as they do for the kernel. The Rocq catalog is not ported. Record this as a deviation: the big idea, text-heap resources per pc (`utext γt a b`), is kept. (b) Port `gen_ucode.py` literally. |
> | **DU4** | **The printf cone ONCE.** Rocq proves ulib's putc/vprintf/vprintfS/fprintf four times (cat 6.8k, grep 7.9k, seccomp 7.1k, init 3.3k). Its own header says they are "the same C, the same instructions, every pc 0x1d0 further down". | **Prove it once, parametric in the load offset** (and in the stub addresses it calls), then instantiate it per image. Spike it on putc first. If the pc-relative call to the `write` stub makes the relocation lemma awkward, fall back to per-image copies. Saves about 18k Rocq-equivalent lines. |
> | **DU5** | **The pipe byte queue and the close payments are a union PREREQUISITE in the kernel.** Rocq `PipeNames`/`PipeQueue`/`PipeReg` are flagged unported in Lean (SpecPipewrite dev 1, SpecFilewrite dev 11, SyscallArmsFdDefs dev 4, pending_edits "exit's deposit … fileclose close payments"). The union's pipe interface (`PipeProto`, `UkPipeDev`, `UkRead/WritePipe`, `UkPipesIface`, `UShPipe*`) is stated over `pipe_wlink`/`pipe_rlink`/`pipe_cpay`/`pipe_reg`. | **Port the queue Rocq-literally INTO the landed kernel contracts**, in two worktree waves. **PQ-a** (pipe files: defs and pipealloc/pipewrite/piperead/pipeclose/sys_pipe plus the fileread/filewrite pipe arms) runs now, in parallel with the bump, on disjoint files. **PQ-b** (`fileclose_cpay(s)`, the exit deposit, the sys_close deposit, the sys_pipe receipt, the `udepw` suppliers of UexecExecMint dev 2) runs after the bump. About 28 Rocq kernel files move. There is no weaker alternative: the union reads these resources. |
> | **DU6** | **The era turn `Tn`.** D49(a) left it out. The union needs it: `union_turn = fturn`, `<init>` speaks first on the console. | **Reverse D49(a) now.** MachCSL's `Hobs` power-on arm yields `Tn c (obsBoots h + 1)`, and `powerBootRes`/`Hboot` carry `Tn c (gen+1)` (Rocq RiscvAdequacy :714–806). Thread it through `SystemBootEra`, `EraInitBoot` and `xv6PowerAdequacyGen`. The unit instance is `emp`. This is a small MachCSL worktree (K1). |
> | **DU7** | **Who owns the seccomp SPEC layer.** Rocq did the 7b2c1b1b move in two checkpoints. Checkpoint 1 was the code bump plus the mask in the contracts. Checkpoint 2 was the union-driven kernel refinements: S0 `ai_wild`/`ai_wild_lic`/`ai_rdwild` in `app_iface`, `AppInv.app_rdcred`, `WpUart.cons_licence_at`; S2k–S2k3, the console read's marked arm (`cons_placed`, `cons_chain`, `cons_swallow_placed`, `cons_era` in `cons_res`); S5b, `ep_rpos` riding the lease; `UexecSecc`'s universe. | **The bump agent does checkpoint 1 only.** The union lane's worktree K3 ("K-SECC") does checkpoint 2's kernel half after the bump lands. That keeps the bump reviewable and puts the design-heavy part next to its only consumer. |
> | **DU8** | **user-once.** Rocq replaced three copies of sh's parser walk by ONE refinement walk (`RefParse` + `UkShGettoken`/`UkShRedirs`/`UkShArgs`/`UkShParser`/`UkShSeam`). It keeps the per-shape walks (`UkShParse*`, `UkShRedirPr/Gtk`, `UkShPipe{Tok,Pr,Ex,Ex2,Pex,Parse,Cm,Right}`, about 27k) as corollaries "because upstream's full shells import them". B (`fd_stream`) and C2/C3 (the program-generic exec) are NOT landed. | **Port only the general walks, and drop the corollary-only files.** U0-X's reverse-cone audit confirms which files are corollary-only. For B/C2/C3, port Rocq's current copies (`UEchoOut/File/Pipe`, the `USh*Pay` twins), unless Rocq lands them before wave U2 reaches those files. Re-check at the U1→U2 boundary. |
> | **DU9** | **Decidability of the disciplines.** Rocq wrote constructive deciders: `UnionDecU` (2.1k, "the riskiest pure item"), `UnionDiscDec`, `FileDiscDec`, `PipesDiscDec`, `PipesDecE` (about 4.7k in all). Their only purpose is to keep `Classical` out of the audit, because the ledger's taint counter cases on `lm_disc`. Lean's audited baseline ALREADY contains `Classical.choice`. | **Use `Classical.propDecidable` where Rocq's decider exists only to case-split.** Keep a computable decider only where a proof computes, and keep a few `decide` demos as anti-vacuity checks. Record it as a deviation. The axiom list stays the baseline. |
> | **DU10** | **One function per file for USER programs.** The memory rule covers kernel functions. The user programs have about 60 functions: sh ≈ 30 (getcmd, parsecmd, gettoken, peek, parseredirs, parseexec, parsepipe, parseline, nulterminate, runcmd, fork1, malloc/free/morecore, the printf cone…), cat/grep/init/seccomp mains and helpers, and echo. | **Yes: `Spec<Prog><Fn>`/`Proof<Prog><Fn>` per user function** (Rocq's multi-function files are split). The shared layers (run leaves, handlers, claims, rounds) stay grouped as in Rocq. This also gives the program wave its parallelism. |

---

## 0. Findings that shape the plan

1. **The union is large: about 375k Rocq lines that Lean has not ported.**
   - The `Require` cone of `UInitUnion` minus the cone of `SystemAdequacy` is **292 files, 331,464
     lines**.
   - Rocq's SystemAdequacy cone also contains about **43.8k lines Lean never ported**, because Lean's
     system theorem did not need them. They sit in Rocq's system cone only through
     `UexecExecMint → UkRun` and `UexecCond → UEchoKernel`:
     - the verified-user engine: `WpUmode*`, `Umode*`, `Uk{Step,Leaf,Load,Store,LoadText,Branch}`;
     - the run layer: `UserHeap`, `UkRun*`, `UkAbi`;
     - the echo program: `UkEcho`, `UCodeEcho`, `UEchoKernel`;
     - the pipe queue: `PipeQueue`, `PipeReg`, `PipeNames`.
   - At Lean's measured ratio (Lean 518k lines vs about 875k Rocq for the ported system cone, ≈0.6)
     and with the DU3/DU4/DU8/DU9 savings, expect **about 150–170k Lean lines**. That is roughly
     another third of today's tree.
2. **The union depends on `USER` only as a PARAMETER, exactly as `xv6FsAdequacy` does.** Rocq calls
   `LinkUserinit.UG.uexec_wp_gen` in two places:
   - `UInitFileLeaves.file_gen_mint`, the taint fallback slot;
   - `UShURound.usecc_exec_sup`, `seccomp x` exec'ing an arbitrary binary.

   Lean has this as `(LinkUexecWp.UexecGen US).uexec_wp_gen`. So the union theorem takes `US : USER`,
   and nothing waits on USER's proof.
3. **What really waits on the user layer is the ENGINE's proof (DU2), about 21k Rocq.** It sits on
   USER's internal tower. Its STATEMENTS are Iris-level over Lean's landed `uvb`/`ukc`, so with an
   interface everything above it can start now.
4. **Most of the rest is kernel-independent or uses kernel vocabulary Lean has.**
   - 60 files (about 45k) are PURE: line models, disciplines, program trees, the reference parser,
     the lexers.
   - 58 files (about 50k) are the claim/ghost layer over FsAbs/console/uexec vocabulary.
   - The kernel-side GAPS are specific: the pipe queue (DU5), `Tn` (DU6), the seccomp spec layer
     (DU7), and a list of small lemma gaps (§3.3).
5. **The 7b2c1b1b bump blocks less than it seems.**
   - The user binaries (`usys.S` gained the `seccomp` stub, so every user ELF moved) can be dumped
     from `xv6-riscv@7b2c1b1b` independently of the Lean kernel bump.
   - What truly waits for the bump:
     - the `fs.img` literal (inum 23 `/seccomp`, the `Fs*Pin` files);
     - the `uvis` secc key and `secc_all` (every uexec/`UkRunSys` row);
     - `initBootBundle`'s secc argument;
     - K3.
6. **Rocq's compile hazards carry over, so the rule is to time the step and not raise budgets:**
   - lane M's decider demo reduced a unary `nat` code;
   - `UkSeccMain` took 28 min and 135 GB on one argument tactic;
   - two instance hangs at bare `uartGhostG`/`ghost_varG` binders.

---

## 1. (a) Rocq's cone, by layer

### 1.1 The top (L7, 6 files, 2,376)

- `App.v` (669): the record `xv6_app` (**ported: `Xv6/AppIface.lean`**), the class `xv6_app_laws`
  with 11 fields (`al_birth al_Rt al_kill al_sup al_R0 al_pow al_tx al_rx al_xfer al_programs
  al_echo`), `xv6_app_adequacy` (it builds `Hperm` from `al_tx`/`al_rx` through
  `uart_obs_permit_ledger`, then calls `xv6_power_adequacy_gen`), `app_triv_laws`, and
  `xv6_app_adequacy_triv_xv6Σ`.
- `AppUnionRec.v` (410): `union_phi`, and `app_union := MkApp union_gn union_cl_all file_names
  (file_pred ∘ ugn_file) (file_boot …) union_R union_ifc union_turn union_phi`.
  - `union_ifc` fills all 7 `app_iface` components, including seccomp's `usecc_tok`/`union_wild_lic`
    and `urdwild`.
  - The ten discharged laws are `union_al_{birth,Rt,kill,sup,R0,pow,tx,rx,xfer,echo}`, plus
    `union_Happ_init` (the file claim at the literal image) and `union_Hphi_R`.
  - `union_laws` takes `al_programs` as the section hypothesis `Hprog`.
- `UUnionBootAdequacy.v` (191): `union_prog_law` (`al_programs` at `app_union`, NAMED),
  `union_adequacy_at_img`, `unionΣ` (xv6Σ + bioslot, echoOut, unionLine = `mono_list Z`, fileApp,
  fileOut, fifReg, pipeOut, pipeProto, pnsReg, pipesN, cifReg), and `union_adequacy_unionΣ`.
- `UInitUnion.v` (102): `union_Hinit_boot : union_prog_law` (by name, from
  `UInitUnionBoot.union_Hinit_boot_at`) and **`union_adequacy_closed`**: `Hgen0 Hpow0 (Hdisk : v_disk
  … = fsimg_dk) → nsteps … → (∀ reducible) ∧ UnionOutPure.union_phi κs`.
- `UInitUnionBoot.v` (429) and `UInitUnionCC.v` (575): the assembly of `/init`'s bundle at the
  union.

### 1.2 PURE layers: no Iris (60 files, about 44.8k)

| group | files (lines) | total |
|---|---|---|
| line model / disciplines | LineModel 1192, LineModelInst 83, LineModelLinks 1653, LineWords 1762, LineBytes 285, GenOutPure 1002, GenOutHist 659, GenOutWild 515, EchoDisc 2822, EchoOutPure 1854 | 11.8k |
| file model | FileState 245, FileClass 183, FileName 312, UNameBytes 126, UNamePath 165, FileDisc 3337, FileDiscDec 416, FileHooks 528, FileLineWit 99, FileOutPure 703, EchoFsPure 32, FileFsPure 90, FsFPin 154 | 6.4k |
| pipes model | PipeDisc 1931, PipesDisc 2659, PipesDiscDec 668, PipesDecE 794, PipesCut 924, PipesUline 317, PipesView 143, PipesPair 87, PipesLedPure 210, PipesFire 1317, PipeOutPure 493, PipeBothNPure 1123 | 10.7k |
| union model | UnionDisc 871, UnionDiscDec 714, UnionDecU 2092, UnionOutPure 313, UnionView 119 | 4.1k |
| program trees | ProgTree 1584, ProgTreeFile 47, ProgTreePipes 1381, GrepFilt 653, GrepTree 655 | 4.3k |
| reference parser + sh lexing | RefParse 413, RefParseSym 1354, RefParseBridge 729, UkShParseSym 639, UkShPipeLex 812, UkShPipesLex 945, UkShRedirCut 42, UkShRedirLex 70, UkShRedirLine 388, UkShWords 586, UShLexRedir 442 | 6.4k |
| ELF / ABI words | ElfUser 800 (sanity leaf: nothing imports it), ElfLoadable 153, ExecWords 70, UkProgAbi 69 | 1.1k |

### 1.3 The claim / ghost / pin layer: Iris over kernel vocabulary, no `urun` (58 files, about 50.3k)

| group | files | total |
|---|---|---|
| console claim & links | EchoOut 4130, EchoLinks 1226, EchoLinksBan 222, EchoLinksLine 998, EchoLinksPro 439, GenOut 1858, GenLinks 254, GenLinksGl 103, GenLinksLine 1373, LinkRec 902, StageRec 430, ReadRec 297, UserConsole 569, UConsLine 357, UConsOpen 681 | 13.8k |
| file application | AppEcho 1709, AppFile 1589, AppFileCons 447, FileOut 695, FileLinks 102, FileLinkGen 379, FileLinksLine 738, FileDeltas 1383, FileOpen 2481, FileWrite 718, FileWritePart 135, FsAbsWritePart 145, FsDurSyscall 665 | 11.2k |
| tree view, pins, exec entry | AppTree 2676, TreeView 3731, TreeImg 439, TreeObs 215, PinnedExec 575, PinnedObs 1481, PinnedOpen 536, FsCatPin 472, FsConsPin 668, FsEchoPin 471, FsGrepPin 433, FsInitPin 541, FsInitPinBoot 388, FsSeccPin 433, FsShPin 476, ExecBundle 280, ExecEntry 261, UInitFd 452, UStrImg 125, UImgWordDefs 78 | 15.2k |
| pipes & union claim | PipeProto 2446, PipeBothN 957, PipeOut 777, PipeOutN 1572, PipeOutNEv 1012, PipeOutW 975, PipesOut 269, PipesLinksV 402, UnionOut 787, UnionLinks 423, UnionLinkInst 397, UnionLinkInstAt 246, UnionReadInst 290, UnionReadInstAt 313 | 10.9k |
| seccomp universe | UexecSecc 881 | 0.9k |

UConsLine, UConsOpen, UserConsole and PipeProto mention `urun` a few times. Their only dependency on
the run layer is the vocabulary.

### 1.4 The verified-user ENGINE and RUN layer (in Rocq's system cone; NOT ported; about 43.8k)

- **Engine, Sail-facing (DU2, user_layer lane owns the proof), 21.0k:**
  - WpUmodeStep 2467, WpUmodeStore 2182, WpUmodeLoad 1653, WpUmodeFetch 1277, WpUmodeTextLoad 919,
    WpUmodeBranch 593;
  - UmodeFetch 1096, UmodeFetchX 640, UmodeText 508, UmodeMem 384, UmodeCap 218, UmodeRegs 90;
  - UkStep 2154, UkStore 2132, UkLoad 1757, UkLeaf 1608, UkLoadText 922, UkBranch 367.
- **Run layer (union lane), 16.5k:** UserHeap 2187, UkRun 2904, UkRunLeaf 1346, UkRunMem 893,
  UkRunSys 6697, UkAbi 996, UmodeAbi 986, UmodeArith 486.
- **The echo program, old tier (union lane), 5.3k:** UkEcho 2986, UCodeEcho 1815, UEchoKernel 502.
  The union's echo entries still import them (`UEcho*`, `UkEchoTree`, `UkTreeEntry`,
  `UkFileEntries`, `UkUnionEntries`, `USh*`).
- **The pipe queue (kernel, DU5), 1.05k:** PipeQueue 715, PipeReg 260, PipeNames 78.

### 1.5 Code catalogs (generated, 12 files, 47.2k; DU3)

- UCodeCat 5937, UCodeGrep 8906, UCodeInit 5591, UCodeSeccomp 5353, UCodeShK 9024, UCodeShM 2823 and
  UCodeShP 8998 (the three sh files are ONE binary split for build time).
- The literal pins UkCatLit 103, UkInitLit 103 and UkSeccLit 156 (`secc_mask_masked`: the ONE place
  the seccomp binary's mask enters).
- The dumps behind them are `user-rocq/*` (46.5k): raw ELFs, instruction lists, data.

### 1.6 The program tier

**L4, handlers / interfaces / program-tree payment (34 files, 26.5k):**

| group | files | total |
|---|---|---|
| tree payment | UkTree 337, UkTreeEntry 726, UkTreeRead 631, UkHandler 908, UkFreeHandler 368, UkStub 297, UkFork 1471 | 4.7k |
| read / write leaves | UkReadCons 452, UkReadFile 605, UkReadPipe 693, UkReadRows 396, UkWriteClosed 292, UkWriteFile 536, UkWriteLeaf 587, UkWritePipe 499, UkConsOut 1122 | 5.2k |
| devices | UkFileDev 1366, UkFileOpen 1604, UkFileIface 1862, UkFileEntries 219, UkPipeDev 1179, UkPipesIface 2631, UkPipesEntries 548, UkCatFIface 1905, UkCatFEntries 226, UkUnionEntries 715 | 12.3k |
| run extras & exec | UkRunBr 173, UkRunExecRef 395, UkRunSecc 126, ExecArgs 766, ExecRun 1012, ExecBundle/ExecEntry (§1.3) | 2.5k |

UkCatFprintf 1361 belongs to the printf cone (DU4).

**L5, per-program proofs (83 files, 132.5k):**

| program | files | total |
|---|---|---|
| **sh** | 52 files, UkSh* (the largest: UkSh 9734, UkShDiag 9155, UkShMalloc 4845, UkShParser 4373, UkShRun 3896, UkShParse 3634, UkShPipe 3567, UkShParseCmd 3469, UkShPipeCm 3320, UkShParseTok 3183, UkShArgs 3056). About 27k of it is legacy per-shape walks, and DU8 skips those | 85.7k |
| **grep** | UkGrepFprintf 2136, UkGrepLib 1794, UkGrepLoop 2324, UkGrepMain 1997, UkGrepMatch 2138, UkGrepPutc 856, UkGrepTree 267, UkGrepVprintf 2198, UkGrepVprintfS 2715 | 16.4k |
| **cat** | UkCat 1322, UkCatCat 2074, UkCatMain 1965, UkCatPutc 557, UkCatTree 555, UkCatVprintf 2195, UkCatVprintfS 2712 | 11.4k |
| **init** | UkInit 2415, UkInitMain 2967, UkInitPrintf 689, UkInitPutc 542, UkInitVprintf 2065 | 8.7k |
| **seccomp** | UkSeccEntry 203, UkSeccFprintf 1363, UkSeccMain 1229, UkSeccPutc 858, UkSeccVprintf 2198, UkSeccVprintfS 2698 | 8.5k |
| **echo (tree route)** | UEchoFile 317, UEchoOut 991, UEchoPipe 185, UkEchoTree 293 (plus §1.4's UkEcho) | 1.8k |

The printf cone inside those totals is about 25k (DU4).

**L6, the shell's rounds and init's assembly (39 files, 27.7k):**

- **USh\* (20.1k):**
  - UShLine 1595, UShLineHold 102, UShPanic 964, UShPanicHold 187, UShOut 457, UShKernel 1193,
    UShConsK 533, UShGeom 874, UShExecPin 513;
  - UShEcho 1367, UShEchoOut 152, UShEchoPipePay 266, UShCat 877, UShCatPay 461, UShCatFStage 458,
    UShGrep 1080, UShSecc 781, UShFileRedir 458;
  - UShPipeCall 281, UShPipeLeaves 434, UShPipesDefs 743, UShPipesNode 1125, UShPipesStage 805,
    UShUPipes 906;
  - UShURound 1571, UShURoundDefs 927, UShURoundLaws 879, UShURoundShapes 93.
- **UInit\* (7.6k):** UInitArgv 81, UInitBanner 525, UInitBoot 376, UInitCons 1318,
  UInitConsFile 644, UInitConsK 989, UInitDiag 405, UInitFd 452, UInitFileLeaves 350,
  UInitKernel 790, UInitSh 1652.

---

## 2. (b) What depends on USER / the user layer, and what can start NOW

| layer | depends on | can start |
|---|---|---|
| §1.2 pure (44.8k) | nothing; seccomp's `LSecc` is model-only | **NOW** |
| §1.4 engine statements → `UK_LEAVES` | Lean's `uvb`/`ukc`/`ukcq` (UexecRet), `ElfMem`, UserPerm | **NOW** (statements) |
| §1.4 engine PROOF (21k) | USER's internal tower (`UserTotalU`, `UserMem*`, `UserStep*`, `UserTrap`, `UserActiveClass`, `UserExecFacts`, `DecodeTotalU`, `WpDecodeBridge`, `UserPtTree`, `UserFrame`, `UserBytes`, Hart*-level MachCSL) | **after the user_layer's lower tower** (user lane, DU2) |
| §1.4 run layer (16.5k) | `UK_LEAVES` + UexecRet/UexecSG/UexecSlot + UsysMemOk rows | **NOW** for `UserHeap`/`UkRun`/`UkAbi`/`UmodeAbi`/`UmodeArith`/`UkRunLeaf`/`UkRunMem`. `UkRunSys` needs K3 (secc key/rows) and K4 (close/exit deposits) |
| §1.5 code (DU3) | the 7b2c1b1b user ELFs (dumpable now) | **NOW** (generator + images) |
| §1.3 console/file claims | ConsLog/ConsoleInv/UartInv, FsAbs*, AppInv/AppCfg | **NOW**, except the wild arms (`GenOutWild` is pure; `lk_wild`/`riscv_wild` need K3) |
| §1.3 tree/pins | fs.img literal (the pins name inodes and bytes of `/sh`, `/cat`, …, `/seccomp` = inum 23) | **after the BUMP** (the fs.img literal moves). `TreeView`/`TreeObs`/`PinnedObs` can start now |
| §1.3 pipes/union claim | PQ-a/PQ-b (DU5), K3 | after K2, K4, K3 |
| §1.6 L4 handlers | run layer + claims + PQ | after U1 |
| §1.6 L5 programs | run layer + code images + (L4 for entries) | walks after U0-6/U0-7/U1-R; entries after L4 |
| §1.6 L6 rounds / init | L4 + L5 | U3 |
| §1.1 top | everything, plus K1 (Tn) and K3 | U4 |

**USER-parametric, not USER-blocked:** the theorem's `US : USER` feeds `uexecWp_gen` at the two sites
of §0.2.

**The Uk\* program-tree logic** (UkTree/UkHandler/UkStub) is NOT in Lean yet. It is L4, on the run
layer.

---

## 3. (c) What Lean has vs needs

### 3.1 The application record and the generic theorem

| piece | Lean state | needed |
|---|---|---|
| `Xv6/AppIface.lean` (206) | `AppIface` (tag/kill/cons/lic), `appIfaceTriv`, `Xv6App` (all 9 fields, `turn` present but carried by nothing), `appTriv` | **K3:** add `wild`/`wild_persistent`/`wild_timeless`/`wild_lic`/`rdwild`(+instances), `wildNone`/`wildNone_lic`; the `bootFixedGS` slots grow to match (MachCSL gets the new slots, or they ride Xv6's `EraPerm`/console defs — K3 decides against Rocq's `riscvF_app_iface` uses in WpUart/AppInv) |
| App laws + `xv6_app_adequacy` | NOT ported (AppIface header) | **U0-A `Xv6/AppLaws.lean`:** `structure Xv6AppLaws A` (11 fields, Rocq's order). `al_programs` is stated as Lean's `EraInitBoot` (with the turn after K1 and the secc argument after K3). `xv6AppAdequacy` (`Hperm` from `al_tx`/`al_rx` via the landed `uartObsPermit_ledger`, the ledger via `obsLedgerAt_alloc_cl/_step/_phi`, all landed in MachCSL/Adequacy), `appTriv_laws`, `xv6AppAdequacyTriv_xv6GF` |
| `xv6PowerAdequacyGen` hooks | `CT Cl Hbirth`, `N appFs`, `appBoot`, `Ai`, `Happ_boot`, `Happ_init`, `Pt HPt Hobs`, `Hinit_boot = EraInitBoot`, `Happ_echo = EraEcho`, `Hperm = EraPerm`, `phi Hphi`, `Himg`. `Hkill_sup`/`Hout_sup` dropped (unused, dev 2) | **K1:** `Tnn` and `Hobs`'s turn. **K3:** EraInitBoot's secc (`initBootBundle ROOTINO seccAll fdt0`) |
| `EraInitBoot` | `appInv fscFs -∗ appBoot c (gen+1) r ==∗ initBootBundle ROOTINO fdt0` at the era instance | `-∗ Tn c (gen+1)` (K1) and the secc argument (K3), matching Rocq `al_programs` |
| `xv6GF`, `fsimgHimg` | at the old revision | bump re-does them. U4 adds `unionGF` = xv6GF + the union's capacity classes (echoOut, fileApp, fileOut, pipeOut, pipeProto, pnsReg, pipesN, cifReg, fifReg, `mono_list Z`), each mapped onto the ONE instance of its camera (memory rule), reusing Xv6G's where the camera type coincides |
| `USER`, `LinkUexecWp.UexecGen` | landed | used at the taint-fallback slot and the seccomp exec supply (§0.2) |

### 3.2 The kernel-level vocabulary the union reads

| Rocq | Lean | gap |
|---|---|---|
| UexecRet (`uvb`, `ukont`, `ukc`, `uslot`, `uexec_dep_F`, `uexec_ret`), UexecSG, UexecSlot (`uvis`), UexecExecInst, UexecExecMint, InitBoot | landed (UexecRet 1388, UexecSG, UexecSlot, UexecExecInst 1106, UexecExecMint, InitBoot) | `secc_all`/`uvis_secc`/`usys_eff_secc_all` (bump/K3); **`udep`/`udepw`/`udepw_law_of_sup_{read,write,close,exit}` suppliers (UexecExecMint dev 2: "return with the program tier")**, which go to the run layer and K4; `tf_of_arg0/1/2`, `uvis_of_run_fd` |
| SpecSyscall `sysc*` rows, SyscallArms* | landed | **pipe and close receipts are PURE (SyscallArmsFdDefs dev 4); the exit deposit pays nothing.** That is DU5, PQ-b |
| pipe specs | pipealloc/pipewrite/piperead/pipeclose landed WITHOUT the queue (SpecPipewrite dev 1–2; `pipeWpostR` only, write end not pinned) | **DU5, PQ-a:** `pipe_st`, `pipe_qauth`/`pipe_qfrag`, `pipe_wlink`/`pipe_rlink`/`pipe_wolink`/`pipe_rolink`, `pipe_wchain`/`pipe_rchain`, `pipe_rpay`, `pipe_cpay`, `pipe_reg`, `fileclose_cpays_of_regs` |
| fileclose | landed, no close payment | `fileclose_cpay`/`_cpays`/`_cpost_any` (PQ-b) |
| console (ConsLog, ConsoleInv, WpUart) | landed | **K3:** `wild_ev`, `cons_ev_ok`, `cons_licence_at`, `out_link_of_licence_at`, `cons_read_pay_triv_at`, `cons_licence_at_of_wild`, `cons_placed`, `cons_chain`, `cons_swallow_placed`, `cons_era` (in `cons_res`, threaded through BootShared/SpecMain/ProofMain, as Rocq S2k2 did), `flush_lost`, `cons_drop_ok`; AppInv `app_rdcred` (and `_of_sup`, `_of_rdwild`, `_elim`) replacing `app_sup` at the escrow |
| UserFd | landed | the whole-table view `ustd_at`, `ustd_ok`, `ush_view_ok` (seccomp S4 G2) |
| FsAbs / SysOpen | landed | `FsAbsCreateNm` (326: the create commit at a name predicate, `acre_commit_at_nm`), `open_trunc_at`/`trunc_*`/`cre_permit*`/`cur_kept`, `astate_nview`, `delta_*` lookups, `awrite_*_adv`, `aread_commit_adv`, `off_link`/`off_ret_of_link` (OffGv) |
| misc | — | `UserCwd` (`ucwd`, 101), ChildTok `exit_tok_pid`/`child_tok_pid`, UserChildren `uch_any_of`, ObsTrace `obs_wire_app`/`cycles_of_*`/`open_seg_*`, FsImgCheck `fname_{sh,echo,cat,init,grep,seccomp,f}` / `fsimg_*_at`, KexecDefs `kxc_sp_*range`, KexecBuilt `kexec_sz_after_*` |

**The gap estimate is a heuristic.** Every Rocq name defined in a boundary file and used by the
union, with no snake→camel match in Lean, comes to about 709 names. About 560 of them are §1.4's
engine/run layer and UCodeEcho. About 150 are kernel-level, which is the list above. U0-X turns this
into an exact old→new table.

### 3.3 Conventions settled by precedent (no decision needed)

- **User memory keys follow kexec_image_plan §2.** Every Rocq predicate over `M : gmap Z (bv 8)` is
  ported over the view `Mv : Int → Option (BitVec 8)` (`umemView P M`). `UserHeap`'s two ghost maps
  are keyed by the byte VA, as Rocq's are. No gmap lemma is transcribed.
- **Adequacy shape follows D46.** The union theorem is stated at an abstract `GF` first, then at
  `unionGF` via the D46 path.
- **Axioms follow the SystemAdequacy baseline.** `#print axioms` must be the same list: DU9 adds
  nothing, because `Classical.choice` is already in it.
- **Deviations go in file headers, not in notes.** Every DU deviation is recorded in the header of
  the file that makes it.

---

## 4. (d) The decisions

See the table at the top: DU1–DU10. The genuinely open ones are DU2 (the engine interface and its
owner), DU3/DU4/DU8/DU9 (deviations from Rocq's letter that save about 100k Rocq-equivalent lines),
DU5 (kernel re-spec scope), DU6 (reversing D49(a)), DU7 (splitting the bump) and DU10 (the file rule).

---

## 5. (e) Agent split: waves, disjoint files, order

Legend:
- **[NOW]**: can start today;
- **[BUMP]**: after the 7b2c1b1b Lean kernel bump lands;
- **[USER-L]**: after the user_layer's lower tower;
- **[Kn]**: after that kernel prerequisite.

Sizes are Rocq lines, followed by an estimated Lean size. Main-tree agents write new files only;
worktree agents edit landed files. All follow wave7b_prompt.txt.

### Wave U0 [NOW]: 11 agents in parallel

| agent | files (Lean, new) | Rocq | ≈Lean |
|---|---|---|---|
| **U0-X** audit (read-only, first day) | `notes/briefs/union_cone.md`: the real cone of `union_adequacy_closed` (on the GCP VM: `coqdep`/glob-based reverse cone, not Require-closure); the corollary-only files DU8 drops; the exact Rocq→Lean name table for §3.2's boundary; per-file camera classes for `unionGF` | — | — |
| **U0-1** line model | LineModel, LineModelInst, LineModelLinks, LineWords, LineBytes, GenOutPure, GenOutHist, GenOutWild, EchoDisc, EchoOutPure | 11.8k | 7k |
| **U0-2** file model | FileState, FileClass, FileName, UNameBytes, UNamePath, FileDisc, FileHooks, FileLineWit, FileOutPure, EchoFsPure, FileFsPure, FsFPin (FileDiscDec → DU9) | 6.0k | 3.5k |
| **U0-3** pipes model | PipeDisc, PipesDisc, PipesCut, PipesUline, PipesView, PipesPair, PipesLedPure, PipesFire, PipeOutPure, PipeBothNPure (PipesDiscDec/PipesDecE → DU9) | 9.2k | 5.5k |
| **U0-4** trees + parser | ProgTree, ProgTreeFile, ProgTreePipes, GrepFilt, GrepTree, RefParse, RefParseSym, RefParseBridge, UkShParseSym, UkShPipeLex, UkShPipesLex, UkShRedirCut/Lex/Line, UkShWords, UShLexRedir | 10.7k | 6.5k |
| **U0-5** union model (starts once U0-1..3 have statements) | UnionDisc, UnionView, UnionOutPure (+ DU9's classical `lm_disc` decidability and a few `decide` demos, in place of UnionDiscDec/UnionDecU) | 1.3k (+4.7k skipped) | 1.2k |
| **U0-6** engine interface + run core | `SpecUkLeaves` (UK_LEAVES statements, DU2), UmodeAbi, UmodeArith, UserHeap, UkRun, UkAbi, UkProgAbi, ExecWords | ~9k | 6k |
| **U0-7** user images (DU3) | `tools/dump_user_elf.py` + `tools/gen_user_text.py` (from xv6-riscv@7b2c1b1b `user/_{init,sh,echo,cat,grep,seccomp}`), `Xv6/User/<P>Image.lean` + text trees, `UserText` (the one tree→fetch lemma), `ElfUser` sanity (general ELF semantics, `ElfFile`/`ElfBridge`), `UkCatLit`/`UkInitLit`/`UkSeccLit` literal pins. Spike first on echo | 47.2k gen + 1.2k | 3k + generated |
| **U0-8** printf-once spike (DU4) | `Spec/ProofUlibPutc` at a load offset (pc-relative), relocation lemma; if green, vprintf/vprintfS/fprintf follow in U2 | — | 1k |
| **U0-A** app laws | `Xv6/AppLaws.lean` (§3.1); written at today's hooks, amended after K1/K3 (the two fields `al_pow`/`al_programs`) | 0.7k | 0.5k |
| **U0-C** console/file claims | EchoOut, EchoLinks*, GenOut, GenLinks*, LinkRec, StageRec, ReadRec (wild arms stubbed to the `wildNone` interface until K3) | 12.2k | 7k |
| **K1** (worktree, MachCSL) | DU6: MachCSL/Power + Adequacy (`Tn`), SystemBootEra, SystemAdequacy, AppIface (`turn` carried) | — | 0.3k edits |
| **K2** (worktree) PQ-a | DU5: PipeNames/PipeQueue/PipeReg defs; Spec/Proof pipealloc/pipewrite/piperead/pipeclose/sys_pipe; the fileread/filewrite pipe arms; PipeInv(Defs) | 1.05k new + ~12 files re-proved | 4–6k |

### Wave U1 [BUMP] + K1/K2

| agent | files | needs |
|---|---|---|
| **K3** (worktree) K-SECC, DU7 | AppIface wild/rdwild; AppInv `app_rdcred`; ConsLog/UartInv/ConsoleInv (`cons_licence_at`, marked arm, `cons_era` threaded through Boot*/Main); UexecSlot secc key + `seccAll`; UsysMemOk secc rows; InitBoot secc argument; EraInitBoot; UserFd whole-table view | BUMP |
| **K4** (worktree) PQ-b | fileclose `cpay(s)`; SpecKexit/SysExit deposit; SysClose deposit; SysPipe receipt; SyscallArms*/Usertrap arms; UexecSG/UexecExecInst/UexecExecMint (`udepw` suppliers) | BUMP, K2 |
| **K5** small kernel gaps | FsAbsCreateNm, the SysOpen trunc family, UserCwd, OffGv `off_link*`, FsAbsDelta/Write/Read `*_adv`, ObsTrace cycle lemmas, FsImgCheck `fname_*` pins (U0-X's exact list) | BUMP (fs.img pins); the rest NOW |
| **U1-F** file claims | AppEcho, AppFile, AppFileCons, FileOut, FileLinks, FileLinkGen, FileLinksLine, FileDeltas, FileOpen, FileWrite, FileWritePart, FsAbsWritePart, FsDurSyscall (11.2k → 6.5k) | K5 |
| **U1-T** tree/pins/exec | AppTree, TreeView, TreeImg, TreeObs, Pinned*, Fs*Pin, ExecBundle, ExecEntry, UInitFd, UStrImg, UImgWordDefs, UserConsole, UConsLine, UConsOpen (16.3k → 9k) | BUMP (fs.img) |
| **U1-P** pipes/union claims | PipeProto, PipeBothN, PipeOut, PipeOutN, PipeOutNEv, PipeOutW, PipesOut, PipesLinksV, UexecSecc, UnionOut, UnionLinks, UnionLinkInst(At), UnionReadInst(At) (11.8k → 7k) | K2, K3, K4 |
| **U1-R** run leaves | UkRunLeaf, UkRunMem, UkRunSys, UkRunBr, UkRunExecRef, UkRunSecc, UkStub, UkFork; the echo program's old tier: UkEcho, UEchoKernel (14.9k → 8.5k) | U0-6, K3/K4 (for UkRunSys's secc/close rows) |

### Wave U2: programs and handlers (the bulk; about 12 agents, one program per agent, per-function files per DU10)

| agent | files | Rocq → ≈Lean |
|---|---|---|
| **P-printf** | the ulib cone once (putc, vprintf, vprintfS, fprintf) + per-image instances for cat/grep/init/seccomp | 25k → 8k |
| **P-echo** | UkEchoTree, UEchoOut/File/Pipe (after H-io); echo's walk itself is U1-R's UkEcho | 1.8k → 1k |
| **P-cat** | cat main + cat() loop, UkCatTree | 5.9k → 3.5k |
| **P-grep** | grep main/grep/match/matchhere/matchstar + lib, UkGrepTree | 8.5k → 5k |
| **P-init** | init main (console open, dup, fork, exec sh, wait loop) | 5.4k → 3k |
| **P-secc** | seccomp main + entry | 1.4k → 1k |
| **sh-parse** | gettoken, peek, parseredirs, parseexec, parsepipe, parseline, parsecmd, nulterminate at the reference parser (UkShGettoken, UkShRedirs, UkShArgs, UkShParser, UkShSeam, UkShPipeNode, UkShRedirCmd, UkShPipeCmd, UkShPipesCmd/Parse), legacy walks skipped (DU8) | ~16k → 9k |
| **sh-malloc** | malloc/free/morecore (UkShMalloc) | 4.8k → 3k |
| **sh-run** | runcmd, fork1, the pipe/redir/child/paid/seam/fork-twin arms (UkShRun, UkShFork, UkShPipe, UkShPipeWait, UkShRedir*, UkShPipe{Paid,Seam,ForkTwin}, UkShCatForkTwin, UkShPipes{Fork,Round,Seam}) | ~15k → 8k |
| **sh-main** | main, getcmd, the loop, cd, diagnostics (UkSh, UkShMain, UkShLoop, UkShCd, UkShDiag, UkShDiagAt) | ~20k → 10k |
| **sh-exec** | the exec arms UkShEcho, UkShCat | 2.8k → 1.5k |
| **H-tree** | UkTree, UkTreeEntry, UkTreeRead, UkHandler, UkFreeHandler, ExecArgs, ExecRun | 4.7k → 2.5k |
| **H-io** | UkRead{Cons,File,Pipe,Rows}, UkWrite{Closed,File,Leaf,Pipe}, UkConsOut | 5.2k → 3k |
| **H-file** | UkFileDev, UkFileOpen, UkFileIface, UkFileEntries | 5.0k → 3k |
| **H-pipe** | UkPipeDev, UkPipesIface, UkPipesEntries, UkCatFIface, UkCatFEntries, UkUnionEntries | 7.2k → 4k |

Program WALKS need only U1-R, U0-7 and P-printf. Program ENTRIES (`*_image_entry`) need H-tree and
the claims.

### Wave U3: rounds and init (5 agents)

| agent | files |
|---|---|
| **R-sh** | UShLine, UShLineHold, UShPanic, UShPanicHold, UShOut, UShKernel, UShConsK, UShGeom, UShExecPin |
| **R-prog** | UShEcho, UShEchoOut, UShEchoPipePay, UShCat, UShCatPay, UShCatFStage, UShGrep, UShSecc, UShFileRedir |
| **R-pipes** | UShPipeCall, UShPipeLeaves, UShPipesDefs, UShPipesNode, UShPipesStage, UShUPipes |
| **R-round** | UShURoundDefs, UShURoundShapes, UShURound, UShURoundLaws |
| **I-init** | UInitArgv, UInitBanner, UInitBoot, UInitCons, UInitConsFile, UInitConsK, UInitDiag, UInitFileLeaves, UInitKernel, UInitSh |

Together: 27.7k → about 15k.

### Wave U4: the top (1 agent)

- `Xv6/AppUnionRec.lean`, `UInitUnionBoot.lean`, `UInitUnionCC.lean`, `UnionBootAdequacy.lean`
  (`unionGF`, `unionAdequacyAtImg`, `unionAdequacy_unionGF`) and `UInitUnion.lean`
  (`unionHinitBoot`, **`unionAdequacyClosed : USER → UK_LEAVES → g.gen = 0 → g.pow = false →
  diskOf g.m.devs = fsImgDisk → NSteps … → (∀ reducible) ∧ unionPhi κs`**).
- The `#print axioms` baseline must equal SystemAdequacy's.
- Size: 2.4k → 1.5k.

### The engine link [USER-L]: user_layer lane

- `LinkUkLeaves`: WpUmode*, Umode{Fetch,FetchX,Mem,Text,Regs,Cap}, UkStep, UkLeaf, UkLoad,
  UkStore, UkLoadText, UkBranch (21k → about 12k).
- When it lands, drop `UK_LEAVES` from the theorem. When USER is proved, `US` goes too, and the
  closed corollary has only `Hgen0 Hpow Hdisk`, exactly as Rocq's does.

### Order and critical path

```
NOW:   U0-1..5 (pure) ─┐   U0-6 → U1-R ─────────────┐
       U0-7, U0-8 ─────┼──────────────→ P-* walks ──┤
       U0-C, U0-A, K1, K2                           │
BUMP → K3, K4, K5 → U1-F, U1-T, U1-P → H-* → entries → U3 → U4
USER-L → LinkUkLeaves (anytime before U4's final corollary; not on the critical path)
```

- **The critical path runs through the kernel prerequisites.** It is BUMP → K3/K4 → UkRunSys and
  the pipe claims → handlers → rounds → top.
- **The bulk runs in parallel with it.** The program walks (about 60% of the lines) only need U1-R
  and the images, and U1-R's non-syscall leaves only need U0-6.
- **Build discipline (memory rules).** Big-literal and generated files build under
  `ulimit -v 40000000; timeout 300`. No theorem may take more than a few seconds; the Rocq incidents
  in §0.6 are the ones to watch. Main-tree agents build only their own modules and share the GCP
  tree `_shared_lean-xv6`.

### Risks

1. **Rocq drift (DU1).** user-once B/C and possibly more widening will land during the port. Pin,
   then re-survey at the U1→U2 and U3→U4 boundaries.
2. **K3's console marked arm reaches into landed boot and main proofs** (`cons_era` through
   BootShared/SpecMain/ProofMain). It needs a worktree, the root build, and coordination with any
   BootShared work.
3. **DU3/DU4 are Lean-side designs with no Rocq precedent.** Spike each (U0-7 on echo, U0-8 on putc)
   before committing the program wave to them.
4. **PQ's contract shape must match what the union reads.** State PQ-a from Rocq's
   `SpecPipe{write,read,close}` and `PipeQueue` verbatim, then check it against `UkReadPipe`,
   `UkWritePipe` and `PipeProto`'s uses before re-proving.
5. **One instance per camera.** `unionGF`'s camera classes must reuse existing instances (for
   example, `ghost_var Z` and `mono_list` cameras shared with Xv6G). U0-X lists them.
6. **Memory representation.** `UserHeap` over the `Int → Option` view must meet UexecRet's `ElfMem`
   and Lean's page-list image at `urun`. Prove that bridge once, in U0-6, not per leaf.
