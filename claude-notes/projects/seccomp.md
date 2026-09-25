# Worklist: seccomp -- the bump to a083670 and `seccomp x` in the union theorem

Design of record: [`../design/seccomp.md`](../design/seccomp.md).
Opened 2026-09-25.  Read `xv6-bump-playbook.md` before lane K or U.

## RESUME HERE

- Lane K (kernel bump + the mask in the contracts): IN FLIGHT in
  `/shared/xv6iris-3` (branch `main`, uncommitted: Makefile pin,
  kernel-rocq/ + user-rocq/ dumps, iris/Code*.v + KernelDecode*.v
  regenerated).  Owner: the top-level agent.
- Lane U (user tier relayout + the seccomp binary's dumps/catalog):
  IN FLIGHT in worktree `/shared/xv6iris-3-lanes/secc-user` (branch
  `secc/user`, from the same uncommitted base).  Textual until K lands.
- Lane M (pure model: `LSecc`, `US`, line-indexed `lm_merge`, knob off):
  IN FLIGHT in worktree `/shared/xv6iris-3-lanes/secc-model` (branch
  `secc/model`, from HEAD = the OLD pin; rebased onto K+U when they land).
- RESOLVED (owner, same day): the mask must clear `{6,15,17,18,19,20}`;
  upstream 7b2c1b1 does; pin moved (commit c2ee5c64c on `secc/bump`).
- Then S1 (universe slot), S2 (claim arm + licence + dirty credential),
  S3 (the seccomp program), S4 (sh's round, knob on, top theorem, audits).

## Lane K -- the kernel bump and the mask (design §4)

Base state: the pin, dumps and generated layer are already in the tree
(`make xv6-rev-check`, `make check-decode` show the bump's own diff).
Old dumps for the tools: `$SCRATCH/old/OldKernelInstrs.v`,
`OldKernelSyms.v` (the scratchpad path is in the brief).

1. Playbook §1-§3: `fix_proof_imms.py --old-image`, `relayout_batch.py`
   (`--skip` the four reshaped Code files: Syscall, Userinit, Kfork; and
   there is no old CodeSysSeccomp), the `.rodata` content sweep, the
   `.data`/`.bss` remap (everything from `started` to `proc` moved +0x30,
   `tickslock`..`end_` +0x230; SWEEP DECIMAL AND PRE-DIVIDED FORMS), the
   stride 360 -> 368 wherever a proof spells it (`ProcGeom.proc_size`
   and any literal 360/`0x168`; the `proc[]` loops in procinit, allocproc,
   wakeup, kkill, scheduler, procdump, kexit's reparent, kwait).  ONE
   PASS EACH, from the pre-bump text.
2. §4's semantic changes: `pv_secc`, `proc_fields`, `uvis_secc`,
   `skey_eq`, `usys_eff`, `sysc_raw`/`sysc_num`, `uvis_num`,
   `usys_secc_ok` (LAST rows), `secc_all`, `uvis_num_full`, the pin in
   `UkRun.urun`, `USYS_seccomp`.
3. The four reshaped functions: `syscall` (the blocked arm at
   `sysc_num = 0`; the 23rd table entry), `userinit` (the store of
   `secc_all`), `kfork` (the copy), `sys_seccomp` (new Spec/Proof/Link/
   Code + manifest row + `_CoqProject`).  Stack budgets: re-derive from
   the image (`K_syscall` should not move).
4. `FsImgCheck`: 23 live inodes.
5. Build on the VM to green in the KERNEL tier; the user tier is lane U's
   and goes red only where the user images moved.  Then merge `secc/user`,
   build to green, `make check-decode`, `make check-ucode`, `make
   audit-all-only` (13 / 14), `make vtest-check-ci`.
6. Commit by explicit path; update `xv6-bump-playbook.md` with anything
   this bump taught; a `completed/xv6-bump-a083670.md` narrative.

## Lane U -- the user tier (design §0, §4 last bullet)

1. `make gen-ucode` on the VM against the OLD build (the remote tree's
   `.vo` are the old pin's; the generator needs only the model and
   `WpDecodeBridge`/`DecodeTotalU`/`WpRvcBridge`), diff the catalogs:
   every shift is +8 in text after `usys` and +0x10 in data.
2. Hand-written user proofs (`Uk*`, `USh*`, `UEcho*`, `UInit*`,
   `UkAbi`, `ElfUser`): every immediate that crosses the shift boundary
   (calls from main/ulib into printf/malloc, `auipc/addi` pairs at
   `digits`), every user DATA address literal, every ELF geometry
   constant (`sz`, data start, entry rows).  Verify each from the new
   dump, not by +8.
3. The seccomp binary: `USER_DUMPS += seccomp:Seccomp`, the four dumps
   in `user-rocq/_CoqProject`, `ElfUser.seccomp_elf`,
   `FsImgCheck.fsimg_seccomp_path/type/bytes` at inum 23, a
   `tools/ucode_seccomp.txt` (main, the stubs it issues, fprintf cone)
   and the manifest row, `UCodeSeccomp.v` generated.
4. Deliver as commits on `secc/user`; lane K merges and builds.

## Lane M -- the pure model (design §3)

Worktree at the OLD pin, so the tree is green underneath.

1. `LineModel.lm_merge` line-indexed; port `lml_term_merge`,
   `lml_merge_prefix`, `lm_d4`, the determinacy section, `GenOut`,
   `PipesDisc`/`PipesDecE`/`UnionDisc`/`UnionDecU` instances.
2. `FileDisc.uline` gains `LSecc`; the parser; `uline_ws`/`line_body`/
   `line_file`; every `match` on `uline` in the pure files.
3. `UnionDisc`: `US`, codes mod 4, `uok`/`ucont`/`ustep`/`uterm`/
   `upanic`/`ufree`/`umerge`, `ulm adm adm_s`, laws, hooks, `ulmG` at
   the knob OFF.  `UnionDiscDec` decidability, `UnionDecU`'s decider
   (canonical `US []`), `UnionView.pview_union` (no pipeline at `LSecc`).
4. The Iris tier must stay green with the knob off: every law that cases
   on a `uline` refutes the `LSecc` arm from `uline_ok`; where a lemma is
   stated over an arbitrary line, add the admitted-line premise its
   callers already have.  `union_adequacy_closed`'s statement may change
   only through the model's definitions.
5. Demos (design §3 last bullet).  Build green, audits 13/14, commit on
   `secc/model`.

## S1-S4 (after K, U, M land) -- briefs written when they start.
