# Union wave U0 — residuals handed to later lanes

Collected from the U0 agent reports (Sept 26 2026). Each item names the lane that owns it.

## U1-T (image pins)
- `EchoFsPure`, `FileFsPure` (U0-2) wait on `FsInitPinBoot`, `FsShPin`, `FsEchoPin`, `FsCatPin`,
  `FsGrepPin`, `FsSeccPin`.
- Rest of `Xv6/FileName.lean` (existing file → worktree lane): `sys_names`, `name_laws`,
  `txt_laws`, `txt_sys_ok`, `txt_img_ok`, `nl_ne_sys`, `nl_ne_console`, three `era0_*` lemmas.
  Needs `fname_*` pins (missing from `FsImgCheck`), `fname_console`, `TreeImg.img_root_ents`,
  `FsInitPin`.
- `UNamePath.cat_words_head` needs `fname_cat` (then `rfl`).
- When porting `UserConsole`: reuse the kernel's `consSwallow` / `consStoredLb` (as `ReadRec`
  does) instead of redefining Rocq's `ucons_*` duplicates.

## MachCSL/ObsTrace
- `obs_ins` missing (U0-1 defined `consIns` directly by recursion); `open_seg_prefix_of_boots`
  missing (copy lives at `EchoOutPure.openSeg_prefix_boots`). Fold back when convenient.

## U4 (seal)
- `EchoOutG` (new camera class, one field: era map `GhostMapG GF Nat EraPins RegMapF`) needs a
  slot in `xv6GF` / `unionGF`.

## U0-5 (union model)
- DU9: parser and `stripGt`/`parseLine`/`seccParse` are classical/noncomputable, so FileDisc's
  §8 demos were not ported; the anti-vacuity demos belong to U0-5 (or need a computable parser).

## K3 (seccomp)
- `LinkRec.lkWildNone` is deliberately distinct from K3's `wildNone`; K3 changes no U0-C statement.

## UkShPipes* / UShUPipes wave (after DU8 repoint)
- `Xv6/PipesCut.lean` (U0-3) is partial: 15/37 reached decls. The other 22 are statements about
  the shell's lexer/parser (`UkSh.ush_line_at`, `UkShPipesLex`/`UkShPipesCmd`/`UkShParseCmd`/
  `UkShMain`/`UkShEcho`, `UmodeAbi.ubyte0`); only consumer is UShUPipes.
- U0-2 owner note: FileDiscLine's trim dropped `all_cats`, but it is reached via `adm_echo`;
  U0-3 defines `allCats` in PipesDisc.

## K4 (PQ-b, after the bump) — absorbs the rest of PQ-a
- K2 landed only PQ-a steps 1–2 (PipeNames/PipeQueue/PipeReg defs, `Xv6G.pipeqG` slot 94,
  `FdType.pipe γp`, `fdstateOk … γp`, `Xv6/PipeQstep.lean` ghost steps). The re-proofs of
  pipealloc/pipewrite/piperead/pipeclose/sys_pipe and the fileread/filewrite pipe arms are
  BLOCKED on PQ-b: `pipeQres` must enter `pipeResAt`, and then pipeclose's flag store needs
  `pipe_cpay`, which only fileclose_cpay → sys_close/kexit deposits → syscall close arm /
  usertrap exit+kill / UexecExecInst rows 2, 21 can pay. The kill path needs Rocq's KILL-TAINT
  kill row (Lean `killRow` has no taint). So K4 = rest of PQ-a + PQ-b in one worktree lane.
- Interim deviations to retire in K4: PipeInvDefs (queue not in payload), SpecPipealloc dev 4
  (no `pipe_qfrag … pst0` handed out), SpecSysPipe, PipeReg dev 1; PipeReg §4 (fileclose_cpay).
- Name watch: K2 added `fdstNopipe` in FileDefs (Rocq FdSlots name) — U1-R / U0-6 must reuse it.
