# Design: `seccomp x` -- an arbitrary binary under a syscall mask, in the union theorem

Owner's request (2026-09-25): bump to upstream `verified` at a083670
(`8e195e0 seccomp`, `a083670 add user/seccomp.c`), then extend
`UInitUnion.union_adequacy_closed` so that the user may type `seccomp x`
for ANY `x` -- whatever binary runs under the mask -- and the theorem still
holds, because a masked process cannot affect the state the theorem cares
about.  Worklist: [`../projects/seccomp.md`](../projects/seccomp.md).

## 0. What upstream added

- `struct proc` gains `uint64 seccomp` LAST (offset 360; `sizeof` 360 ->
  368, so `proc[]`'s stride and every `.bss` symbol after `proc` move).
  "Bit n set => syscall n allowed".
- `syscall()`: after the table lookup, `if ((p->seccomp & (1ULL << num))
  == 0) { p->trapframe->a0 = -1; return; }` -- a BLOCKED call stores -1
  and runs nothing (no printk, unlike the unknown-number arm).
- `sys_seccomp` (number 23): `argaddr(0,&mask); myproc()->seccomp &=
  mask; return 0;` -- the mask only ever SHRINKS.
- `userinit`: `p->seccomp = ~0ULL`.  `kfork`: `np->seccomp = p->seccomp`.
  exec leaves it alone.  `freeproc`/`allocproc` do not touch it (every
  live process got its mask from userinit or its parent).
- `user/seccomp.c`: fork; child: `mask = ~0 & ~(1<<SYS_open) &
  ~(1<<SYS_kill)`, `seccomp(mask)`, `exec(argv[1], argv+1)`, diagnostic
  and `exit(1)` on failure; parent: `wait(0); exit(0)`.  Diagnostics on
  fd 2.  A new binary in `fs.img` (appended after `_sync`, so the
  existing inums stand; 23 live inodes).
- Every user ELF gains the `seccomp` stub in `usys.S` (8 bytes), so
  `putc`/`printint`/`vprintf`/`fprintf`/`printf`/`free`/`malloc` move
  +8 and the data (`digits`) +0x10 in all six tracked programs.

## 1. THE FINDING THE THEOREM DEPENDS ON: the mask is too small

What the union model's state is: the map of named user files (since W1,
`fstate := gmap fname bytes`).  What a process with open and kill blocked
can still do to it: `unlink` (17? no: 18), `link` (19), `mkdir` (20),
`mknod` (17) -- all reachable by path with no descriptor.  `seccomp rm
f` deletes `f`; `unlink f; link README f` makes `f` README's bytes;
`mkdir f` makes it a directory; `mknod f 1 1` makes it the console.  None
of those is a state the model has, and after a power cycle the next
cycle's `cat f` would print bytes no `echo .. > f` line called for.  So
with the binary's mask `{open, kill}` the statement "the binary cannot
affect the state we care about" is FALSE, and no invariant proves it.

WHAT IS TRUE, and what this design proves, is the statement at a mask
that also clears the four namespace-writing numbers:

    B := {6 kill, 15 open, 17 mknod, 18 unlink, 19 link, 20 mkdir}

Every remaining number is view-preserving (fork/exit/wait/pipe/read/
exec/fstat/chdir/dup/getpid/sbrk/pause/uptime/write/close/sync/seccomp):
`write` reaches only the descriptors the process holds, and without
`open` those are the console it inherited and pipes it made; `chdir`,
`exec`, `close`, `exit` move reference counts, never a link count or a
byte.  The proof is built mask-parametric at `B`; the ONE place the
binary's literal mask enters is the seccomp program's own tree proof
(`mask = ~0 & ~(1<<15) & ~(1<<6)` does NOT clear 17-20), so with the
upstream binary as it stands the final assembly fails LOUDLY at that
literal.  OWNER DECISION NEEDED (asked 2026-09-25): extend
`user/seccomp.c`'s mask to `B` upstream (two lines), or accept the
weaker theorem where the seccomp round leaves the state arbitrary (which
the model cannot represent without a directory/device arm, so it is not
a small change either).  Everything below except the last assembly step
is independent of the answer.

## 2. The console cannot be tamed, so the round is TERMINAL

A masked binary keeps fds 0/1/2 = the console.  It prints anything, it
consumes input the user types, and a child it forks and abandons keeps
doing so after the shell prints its prompt -- so nothing about the
console after the `seccomp x` line is determined by the input.  The line
model already has exactly the arm for this: a COVERAGE-ENDING
alternative (`lm_term`), after which the discipline reads no more of the
era (D4: the line is the input's last, with no partial line after it)
and the output claim admits the arm's bytes (`lm_merge`).  A power cycle
kills every process, so the NEXT era is disciplined again -- and its boot
state is admissible against the earlier `echo .. > f` lines exactly as
today, because (§1) nothing the masked universe did moved a file.

THAT IS THE THEOREM: `seccomp x` may appear as the last line of any
cycle; the console up to and including the echo of that line is as the
transcript says; everything after it in that cycle is unconstrained; and
every later cycle keeps the union's guarantees relative to the file
lines typed before it.  The arbitrary binary affected no state that
outlives its own power cycle.

## 3. The pure model (cut M)

- `FileDisc.uline` gains `LSecc (ws : list word)` -- the line `seccomp`
  followed by one or more alphanumeric words (`wl_alnum`; `x` is any
  word of the class, so `seccomp rm f`, `seccomp sh`, `seccomp init` are
  all lines).  `parse_line`: first word `seccomp`, `ws <> []`.  `uline_ws`
  / `line_body` accordingly; `line_file (LSecc _) = None`.
- `UnionDisc.ualt` gains `US (u : list (bv 8))` -- the bytes the round
  put on the wire after the echo, ARBITRARY.  Codes interleave mod 4
  (`UR 4k`, `UPE 4k+1`, `UPC 4k+2`, `US 4k+3` with `k = encode_nat u`;
  `ualt_dec` total via `decode_nat`, default `[]`).  `uterm (US _) =
  true`, `upanic = false`, `ucont s l (US u) = u`, `ustep s l (US _) = s`
  (THE STATE DOES NOT MOVE -- that is §1's claim, stated), `ufree (US _)
  = false`.
- `uok s (LSecc ws) a` := `a = US u` for any `u`, OR `a = UR r` for the
  SHELL's own alternatives every line admits (the fork panic, the exec
  failure `exec seccomp failed`, the silent round) so the hooks
  `lmh_pan`/`lmh_exf`/`lmh_noc` have codes; nothing else.  A pipeline or
  file alternative at `LSecc`, and `US` at any other line, is `False`.
- THE MODEL GAINS AN ADMISSION KNOB for the seccomp lines, as `adm` is
  for pipelines: `ulm adm adm_s` with `adm_s : list word -> bool`;
  `uline_ok (LSecc ws) := adm_s ws = true /\ ws <> [] /\ words ok`.
  `ulmG := ulm adm_u_g (fun _ => false)` until the round is proved, then
  `(fun ws => bool_decide (ws <> []))`.  Every Iris law cases on
  admitted lines, so the arm is refuted while the knob is off.
- `LineModel.lm_merge` BECOMES LINE-INDEXED: `lm_merge : lm_line ->
  list (bv 8) -> Prop`.  Why: D4 says "a round whose line admits a
  terminal arm and whose chosen continuation is mergeable is the last
  line"; a `seccomp` round's continuation is ANY byte string, so at that
  line `lm_merge` must be `True`, while at a pipeline line it must stay
  `pl_merge`, or every pipeline round would end the era's coverage.
  `lml_term_merge`, `lml_merge_prefix`, `lm_d4`, the determinacy lemmas
  and `GenOut`'s `lm_d4_nomerge_snoc` take the line (both witnesses of
  the determinacy argument are at one line, so nothing else changes).
  `umerge (LSecc _) u := True`; `umerge l u := ∃ s, fstate_ok s /\
  pl_merge (files_of s) adm u` as today for every other line.
- Laws: `lml_term_st` (every state admits `US []`), `lml_term_merge`,
  `lml_cont_shape` (the shell alternatives at `LSecc` have the usual
  `u ++ prompt` shape; `US` is exempt as terminal), `lml_st_step`
  (identity).  Hooks: `lmh_free_term` needs `ufree (US _) = false`.
- THE DECIDER (`UnionDecU`): at a `seccomp` line the canonical witness
  is `US []` -- D4 makes the line the last complete one with no partial
  line after it, so no input point's `done_of` contains it and its
  continuation is read by nothing; `lm_good_out` picks `US u` for the
  actual tail separately (`lm_expected_rel` has its own `∃ ps cs`).
- Demos (`UnionDiscDec`): `echo hi > f`, `seccomp rm f`, power cycle,
  `cat f` prints `hi` (the state survived -- vm_compute at the model);
  a negative demo: a byte typed after the `seccomp` line's newline is
  not disciplined; and `seccomp` alone (no `x`) is not a line.

## 4. The kernel and the trap contract (cut K, "the bump")

The mask is process state that decides a syscall's effect, so it enters
the per-process record and the user-visible key, and the syscall NUMBER
the contracts case on becomes the EFFECTIVE number.

- `ProcDefs.pprivate` gains `pv_secc : mword 64` LAST; `upd_secc V m :=
  V with pv_secc := and_vec (pv_secc V) m`; every other `upd_*`
  preserves it; `KforkChild.kfork_child` copies it (it is `us_tf` of the
  parent's record, so for free); `KexecDefs.kexec_ok`'s success arm pins
  `pv_secc V' = pv_secc V`; userinit's first record has `pv_secc =
  secc_all := mword_of_int (-1)`.  `ProcGeom.proc_size := 368`; `p_secc
  pa := pa + 360` is owned in `ProcInv.proc_fields` beside `name[16]`
  (same discipline as `name`: written by userinit and by kfork under the
  dormant child's lock, read and written by the owner with no lock).
- `UexecSlot.uvis` gains `uvis_secc : mword 64` LAST; `uvis_of` reads
  `pv_secc`; `skey_eq` gains the equation LAST.
- THE EFFECTIVE NUMBER.  `UsysMemOk.usys_eff (secc : mword 64) tf : Z :=
  if Z.testbit (bv_unsigned secc) (usys_num tf) then usys_num tf else 0`.
  A blocked call IS the unknown-number call: a0 := -1, nothing else
  moves, no deposit is consumed and no post is owed -- the dispatcher's
  out-of-range arm, already verified, is its contract.  So:
  `SpecSyscall.sysc_raw V` is the a7 reading (the old `sysc_num`) and
  `sysc_num V := usys_eff (pv_secc V) (pv_tf V)`; every existing row is
  textually unchanged and now means the effective number.  The blocked
  arm proves the post with the quiet rows at `sysc_num = 0`
  (`sysc_sys_out_quiet`, the `_ne` lemmas; the deposit is dropped).
  `UexecSlot.uvis_num W := usys_eff (uvis_secc W) (uvis_tf W)` replaces
  `usys_num (uvis_tf W)` in `UexecRet`'s arms and in every trap-contract
  row (`SpecUsertrap.ut_*`; rows that had only `tf` gain the mask);
  `uvis_num_full : uvis_secc W = secc_all -> 0 < usys_num (uvis_tf W) <
  64 -> uvis_num W = usys_num (uvis_tf W)` is what a verified program's
  ecall leaf rewrites with, off the mask its run pins (`UkRun.urun`
  carries `uvis_secc = secc_all`; fork copies and exec keeps it, so the
  pin costs the entry constructors one equation).
- THE ONE NEW ROW: `usys_secc_ok n tf secc secc' r := if n = 23 then
  secc' = and_vec secc (tf !!! tf_arg_idx 0) /\ r = 0 else secc' = secc`,
  LAST among `uexec_ret_cont_F`'s pure rows (`bump` takes `secc'` as it
  takes `lz'`) and LAST among the dispatcher's, relayed by the trap
  route.  `USYS_seccomp := 23`.
- `SpecSysSeccomp` / `ProofSysSeccomp` / `LinkSysSeccomp` /
  `CodeSysSeccomp` (manifest row), on `SpecSysGetpid`'s mould plus
  `argaddr`: `proc_priv` in at `U`, out at `upd_secc`, a0 = 0.  The table
  gains entry 23; `syscall_env` and `K_syscall` do not change.
- `FsImgCheck.fsimg_live_set` counts 23; `seccomp` is inum 23
  (`fsimg_seccomp_path/type/bytes`, `ElfUser.seccomp_elf`, the four
  `user-rocq/Seccomp*.v` dumps, `USER_DUMPS += seccomp:Seccomp`).

## 5. The universe: a generic slot without the taint (cut S1)

`UexecRet.uexec_dep_F_of_supply` builds the GENERIC keyed slot from `□
ssupply` and the taint; the seccomp universe gets the same construction
from a different, weaker credential, and the whole novelty is which
numbers it has to pay and with what.  A key `W` is IN THE UNIVERSE when

    secc_key W := ⌜forall n, n ∈ B -> Z.testbit (uvis_secc W) n = false⌝
                  ∗ [∗ list] st ∈ uvis_fd W, secc_row st
    secc_row (FdOpen _ _ (FdInode _ _ _)) := False
    secc_row (FdOpen _ _ (FdPipe γp))     := wild_pipe γp      (persistent)
    secc_row _                            := True               (console, closed)

and `useccomp_slot : secc_env -∗ □ secc_key W -∗ my_pay .. -∗ uslot W`
with `secc_env := secc_lic (S gen_id)` (§6) is a Löb over the same arms
as the generic slot.  Per number (`UexecExecInst.xv6_sbundle`):

| n | deposit | paid by |
|---|---|---|
| free numbers, 23 | `emp` | -- |
| 6 15 17 18 19 20 | never asked: `uvis_num W = 0` under `secc_key` | the mask |
| 5 read | `fileread_in` at the row | inode: refuted by `secc_row`; pipe: `pipe_rpay` from `wild_pipe`; console: `cons_acc` DIRTY arm + `cons_read_pay` from `secc_lic` (see §6 for the dirty credential) |
| 16 write | `filewrite_in` | inode: refuted; pipe: `pipe_wpay` links from `wild_pipe`; console: `cons_out_chain` from `secc_lic` |
| 21 close, 2 exit | `fileclose_cpay(s)` | pipe rows: `pipe_reg_of_inv` at `wild_pipe`; others `emp` |
| 4 pipe | `emp`; the POST hands the fragment | allocate `wild_pipe γp` from it; the resume key satisfies `secc_key` |
| 1 fork | the child's slot at the copied key | Löb: `secc_key` is the same table and mask |
| 7 exec | `exec_sbundle`: the AU (observations) and the slot wand | Löb: `exec_key` keeps table and mask |
| the rest | `emp` | -- |

`wild_pipe γp := inv seccN (∃ s, pipe_qfrag (pn_queue γp) s)` -- the
pipe's queue fragment parked with NO protocol; every link the universe
needs (`pipe_wlink`/`rlink`/`clink` are `={⊤}=∗`-shaped) opens it, and
`PipeProto.pipe_reg_of_inv` is the mould.  `secc_key` is preserved by
every row of `usys_fd_ok` (pipe adds pipe rows, dup copies, close
removes, open never runs) and by `usys_secc_ok` (the mask shrinks).

`ExecEntry.image_entry_secc S Q X := □ (∀ W', S -∗ □ secc_key W' -∗
my_pay (uvis_gen W') Q -∗ X W')` is the seccomp twin of
`image_entry_taint`; the seccomp program's tree answers its `exec(x)`
with it, and `exec_bundle_of` gets a third arm beside the pinned and the
taint ones.

## 6. The claim's terminal arm and the era licence (cut S2)

`UnionOut.ucl := peclV ..` is `gcl ∨ popenU`.  It gains a third arm and a
per-era token:

    ucl' k ho H := UT ∨ (secc_clean k ∗ ucl k ho H) ∨ usecc k ho H
    usecc k ho H := secc_tok k ∗ ∃ v ps cs s0 I0 u,
        PIN k v ∗ ps_lb v ps ∗ cs_lb v cs ∗ inp_lb v I0 ∗ WA k s0
        ∗ ⌜nlines I0 = S (length cs) /\ rest_of I0 = []
           /\ lm_of U (last body of I0) = LSecc _
           /\ lm_pro_ok ps cs (nlines I0) /\ (lm_alts_ok at the first length cs lines)
           /\ out(H) = lm_sess ps cs s0 I0' ++ body ++ [nl] ++ u⌝

where `secc_clean k`/`secc_tok k` are the exclusive authority at 0 and
the persistent lower bound at 1 of ONE `mono_nat` per era, minted with
the era's pins (`EchoOut.era_pins` gains `ep_secc`; `PIN k v` carries
the name and `era_pin_agree` identifies it).  `secc_tok k` refutes the
middle arm, so the LICENCE

    secc_lic k := □ ∀ h H ev, riscv_cons_res k h H ==∗ riscv_cons_res k h (cons_step H ev)

follows from `secc_tok k` (the T arm is closed under everything, the
`usecc` arm under every event because `u` is existential and the input
side is not read), and `WpUart.cons_link_of_licence`'s proof is the
era-restricted twin.  `RiscvPtsto.app_iface` gains `ai_wild : nat ->
iProp Σ` with law `ai_wild_lic`, instantiated at `secc_tok`; the trivial
application takes `False`.

THE DIRTY CREDENTIAL.  A tokenless console read pays
`ConsoleInv.cons_dirty_cred Wd = □ Wd`, and `SpecFileread` names `Wd :=
AppInv.app_sup`, which only the taint yields.  `Wd` becomes `app_sup ∨
riscv_wild (S gen_id)`: the generic reader still pays with `app_sup`;
the universe pays with `secc_tok`; the token holder (sh) that finds the
ring dirty gets `□ (app_sup ∨ secc_tok k)` back and either arm ends its
round -- `app_sup` gives `T` as today, `secc_tok k` says the era is in
its terminal arm, which sh's non-terminal credential refutes through the
claim's middle arm.  (Rejected: a shared reader token in an invariant --
`cons_acc`'s left arm returns the token under a plain `==∗`, so an
invariant cannot close around it; and `Wd := app_taint` alone, which the
universe never holds.)

ENTERING THE ARM.  sh's round law at `LSecc ws`: after `gets` returns
the line and before the fork, sh opens the claim (it holds the round's
cursor, `uWcu I p`), moves `gcl` into `usecc` at `u := []`, bumps the
`mono_nat` to 1 and keeps `secc_tok k`; it forks, the child execs
`/seccomp` with `secc_tok k` in its supplier, sh waits.  sh's widened
credential `uWcu` gains a fourth disjunct, the SECCOMP-TERMINAL shape
`useccomp_shape I := secc_tok (S gen_id) ∗ era_pin .. ∗ inp_lb v I`
(no deed -- ruling B3's reason), under which the prompt, the next `gets`
and every later round are paid by the licence and the read's byte, if
one ever comes, is undisciplined by D4 and yields `T` exactly as the
pipeline's terminal shape does (`ush_deed_taint`).

THE EXPORT.  `union_led`'s per-cycle conclusion at the `usecc` arm:
`ins seg = I0` under the discipline (D4), and `lm_good_out` holds at
`cs ++ [ualt_code (US u)]` with `u` the wire's tail -- `lm_sess` at the
extended list IS `out(H)` by `lm_blk`'s definition.  The durable claim
and the boot-state admissibility are untouched: the seccomp round's
`lm_step` is the identity and no universe syscall retags a row.

## 7. The seccomp program (cut S3) and the round (cut S4)

`user/seccomp.c` is a verified program on the `Uk*` engine like `cat`:
`UCodeSeccomp.v` (main, fork/seccomp/exec/wait/exit stubs, the fprintf
cone), a tree `secc_tree ws` in `ProgTree`, `UkSeccompTree.v`, an entry
`UkTreeEntry.secc_image_entry` with the exec of `x` answered by
`image_entry_secc` at `secc_key` -- the one place the mask LITERAL must
clear `B`.  `FsImgCheck` pins `/seccomp` as inum 23.  sh's round:
`UShURound`'s dispatch gains the `LSecc` arm through the fork twin
(`UkShCatForkTwin`'s shape), the entry resolution `(W)` for the name
`seccomp` at the image, and the terminal-shape laws for the main loop
(`UShURoundLaws` at `useccomp_shape`).  Then the knob flips
(`adm_s := fun ws => bool_decide (ws <> [])`) and the top theorem's
statement changes only through the model.

## 8. Honest limits

- The mask must be `B`, not `{open, kill}` (§1); pending the owner.
- Nothing is claimed about the console after the `seccomp` line within
  its cycle, nor about the universe's exit status.
- `x` ranges over alphanumeric words; a path with `/` is not a word of
  the class (the class is the union's).
- The universe's `sync`, `chdir` and `exec` of the image's binaries are
  admitted by the proof, not excluded -- they move no row.
