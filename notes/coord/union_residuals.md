# Union: open items

Rewritten Sept 29 2026 (cleanup lane A), after U4 (2504c6277) and krelax (af31d1908).  Each entry of
the old file was checked against the tree at b210bd3ea.  The discharged ones are gone: the fprintf
entries (`ushFprintf_holds`, `catFprintf_link`, `seccFprintf_link`, `initPrintf_link`), all the
parameter entries (R-pipes, R-round, I-init, sh-run, sh-main, R-sh, H-file/H-pipe), the H-io
follow-ups (`ukSysIO_holds`, `ukPostRows_holds`, `wp_uk_pipe_read_end`), the UkRunSys gaps, the K3/K4
and U1-T/U1-R/U1-P/U1-F follow-ups, and the camera slots (`UnionGF.lean`).  For their history, see git
(`git show b210bd3ea:notes/coord/union_residuals.md`).

## State

- `Xv6.unionAdequacyClosed` (LinkUInitUnion) takes Rocq's hypotheses exactly: `Hgen0`/`Hpow0`/`Hdisk`.
  Its axioms are the baseline: propext, Classical.choice, Quot.sound, the bv_decide certificates.
- `userProof : USER` and the system theorem are closed too.
- **Cone re-audit** (notes/cone_reaudit.md; kernel-term walker `tools/cone_reaudit/`, which sees
  instance, hint, canonical and obligation resolution).
  - It finds NO real gap: no reached Rocq declaration is missing in a way that weakens a Lean statement.
  - The 116 undocumented unported union-side declarations are proof-internal helpers of ported
    consumers.

## Open (optional cleanups; nothing blocks a theorem)

1. **Redundant K1/K2/K3 premises.**
   - These U4 seal lemmas take `hK1`/`hK2`/`hK3` beside `hev : consEvOk …`, which carries them since
     krelax: `GenOutHistSeal.gclPure_open/_close`, `GenOutSeal.gcl_open/_close`,
     `PipeOutNEvSealPure.gclPureO_open/_close`, `PipeOutNEvSeal.popenV_*`/`peclV_*`,
     `PipeOutWSeal.pwclV_open/_close`, `UnionOutSealSteps.ucl_open/_close`.
   - The callers pass `hev`'s projections (`UnionLinksSeal.union_happ_echo`).
   - Fix: derive them inside and drop the premises.  This is a signature change, so rebuild the chain.
2. **Lean over-ports** (reached by the glob walk only; the kernel walk finds them unreached, and no
   Lean file uses them): `PipesDisc.allCats`, `admEcho`, `pipesLmE` (Rocq `all_cats`, `adm_echo`,
   `pipes_lmE`).  They can be deleted.  The union reads `UnionDisc`'s admission, not the pipeline
   application's.
3. **Intermediate link statements still carry the parameter records they are discharged from
   downstream.**  This is by design (one function per file): `cat_linked (HF : CAT_FPRINTF)`,
   `init_linked (HP : INIT_PRINTF)`, `secc_linked (HS HF)`, `shMain_linked (HS HSS HF)`, and
   `UshExecEnv` in the sh-exec specs.
   - Each header now names its discharger: `CatPrintfLink`, `InitPrintfLink`, `SeccPrintfLink`,
     `UkSysPHolds`, `UshSysPHolds`, `LinkShFprintf`, `ushExecEnvOf`.
   - Collapsing them into `*_linked_ulib` forms is cosmetic.
4. **Re-run the cone audit after the drift wave** (Rocq has moved past 1900b8a43; user instruction,
   Sept 29).  Use `tools/cone_reaudit/run_vm.sh` on the new pin, then the local scripts.
   - `trimcheck.py` lists every Lean header that calls a reached declaration "unreached".
   - `stmt.py` re-checks the statement cones.

## Deviations kept on purpose (documented in the headers; listed so they are not re-opened)

- AppLaws deviation 8: `al_tx`/`al_rx`/`al_echo` take `MachFixedGS.mono = MachGpreS.mono_pre`
  (`appUnion` is built at the placeholder `AppPreGS.appPreGS` and read back by `preGS_transport`).
- `udepwfK` carries ⌜uszOk sz⌝, the BitVec lazyFree size (gaps lane); `udepwfK_std` is one-way.
- DU2/DU3/DU4/DU8/DU9 per the union brief.  In particular, the sh exec child and the N-stage pipes are
  re-pointed at the general parser walk (DU8, `SpecShChildExec`, `UshPipesCmd`).
- The statement cones rest on Lean's own machine and device model (the Lean Sail model plus
  `MachCSL/Dev`), not a port of Rocq's `RiscvLang`/`DevModel`/`VirtioModel`.  A faithfulness review
  of the model is a separate question from this port audit.

## Standing advice (from I-init)

- Never intro a proof-mode hypothesis whose head is the xv6 instance's unreduced post
  (`UexecSG.spostAt (self := uexecSGXv6) …` / `xv6Spost …`).  It costs ~6 s per leaf and can
  deterministic-timeout.  Read the post via a Lean-level entailment onto the continuation's premise
  (the `consOpen_post_pre` pattern).
- Run walks generic in the class and read the post at the instance in a separate lemma.  Never let the
  kernel evaluate a literal ELF: state size lemmas over an arbitrary file.

## Drift SY2 (the `sync` line, Rocq b23e6791f): ported in the pre-hook shape

- Ported: `LSync`/`RSyncRan`/`RSyncExec`/`usyncOk` and their arms (FileDiscLine, FileDisc, FileHooks,
  FileOutPure, PipesUline, UnionDisc, UshURoundPure, UkUnionEntriesPure, UInitUnionDisc, UshMainLine),
  /sync's image (User/Sync*, ElfUser, FsImgFiles/Names), `FsSyncPin` (the seventh pin, threaded as
  `i ≠ SYNC_INO`), the program (UkSyncDefs/Stubs, Spec/ProofSyncMain, Spec/ProofSyncStart, LinkSync),
  `UshSync`, `UkSyncEntry`, `UshURoundSync.uHchild_sync`, the dispatch at `LSync` (UshURoundBody), the
  slot (`shSyncSlot`, UshUPipesBody, UInitUnionBoot), the sync demos of UnionDiscDec §6 (UnionDemo;
  the `I_sy` trace demos are not ported).
- **Left for the durability lanes (D2-dur / E)**: Rocq main's hook form.  `syncPay P R := P -∗ R` is
  b23e6791f's; main's is `sync_pay P Qr R := P -∗ Qr -∗ R` with `Qr := Q_opt oQ`, the ecall at 0x36a a
  parameter `ksync_leaf oQ` (discharged by `ksync_leaf_none` / `UkSyncEntry.ksync_leaf_xv6`), the
  entry's Pay `P ∗ hook_opt gen_id oQ`, and `uHchild_sync`'s lend split (`usync_q`/`usync_lend`,
  `Hhk`).  Lean walks the ecall with the CURRENT quiet leaf (`UK_SYS_P.quiet`, 22 ∈ `freeNum`).
- Not ported (unreached, as at DU1): `USyncKernel` (the generic entry's sync gate), `UCodeSync` as a
  catalog (DU3: text evaluations), the deciders (`FileDiscDec`, `UnionDecU`), `FileOutPure.ralt_def`.
