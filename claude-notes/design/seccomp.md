# Design: `seccomp x` -- an arbitrary binary under a syscall mask, in the union theorem

Owner's request (2026-09-25): bump to upstream `verified` (a083670:
`8e195e0 seccomp`, `a083670 add user/seccomp.c`; then 7b2c1b1, the mask
widened at our finding in §1), then extend
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
byte.  The proof is built mask-parametric at `B`; the ONE place the binary's
literal mask enters is the seccomp program's own tree proof.  RESOLVED
(owner, 2026-09-25): upstream 7b2c1b1 ("seccomp: block more syscalls")
makes `user/seccomp.c` clear exactly `B` (open, kill, link, unlink,
mkdir, mknod), and the tree is pinned there.  Everything else `x` can
still do -- print anything, read the console, fork, pipe, exec any
binary in the image, chdir, sbrk, sync, exit with any status -- is
admitted by the proof, not excluded.

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

`UexecRet.uexec_dep_F_of_supply` / `uexec_ret_of_all` build the GENERIC
keyed slot from `□ ssupply` and the taint, and `UexecExecMint.uslot_mint_all`
(the minter the union boot binds as `Hmint`; `uslot_mint_pay` has no
callers) packages it.  The seccomp universe gets the same construction
from a weaker, per-era credential; the novelty is which numbers it must
pay and with what.  A key `W` is IN THE UNIVERSE when

    secc_key W := ⌜forall n, n ∈ B -> Z.testbit (bv_unsigned (uvis_secc W)) n = false⌝
                  ∗ [∗ list] st ∈ uvis_fd W, secc_row st
    secc_row (FdOpen _ _ (FdInode _ _ _)) := False
    secc_row (FdOpen _ _ (FdPipe γp))     := wild_pipe γp      (persistent)
    secc_row _                            := True               (console, closed)

and `useccomp_mint : secc_env -∗ □ (∀ W, □ secc_key W -∗ my_pay (uvis_gen W)
(fun _ => True) -∗ uslot W)` with `secc_env := secc_tok (S gen_id)` (§6) is
a Löb over the same arms as `uexec_ret_of_all`, at the trivial payload.
Per number (`UexecExecInst.xv6_sbundle` / `xv6_spost`):

| n | deposit | paid by |
|---|---|---|
| free numbers, 23 | `emp` | -- |
| 6 15 17 18 19 20 | never asked: `uvis_num W = 0` under `secc_key` | the mask |
| 5 read | `fileread_in` at the row | inode: refuted by `secc_row`; pipe: `pipe_rchain` from `wild_pipe`; console: `cons_acc` DIRTY arm at the widened credential (§6) + `cons_read_pay` from the era licence |
| 16 write | `filewrite_in` | inode: refuted; pipe: `pipe_wchain` from `wild_pipe`; console: `cons_out_chain` from the era licence (`cons_run_of_licence`'s era-k twin) |
| 21 close, 2 exit | `fileclose_cpay(s)` | pipe rows: `pipe_clink` from `wild_pipe` (`PipeProto.pipe_clink_of_inv`'s mould); others `emp` |
| 4 pipe | `emp`; the POST hands `pipe_qfrag (pn_queue γp) pst0` and the two rows | allocate `wild_pipe γp`; the resume key satisfies `secc_key` |
| 1 fork | the child's slot at `kfork_child`'s key, `sfork_pay = fun _ => True`, lend `emp` | Löb: same table, same mask |
| 7 exec | `exec_sbundle`: the AU at the escape `T := secc_tok k` (`ExecRun.exec_walk_of_taint` is already parametric in `T`; `ex_node_id T` says nothing at a true `T`) and the slot wand | Löb: `exec_key` keeps the table; a NEW pin in the wand's premises says the new key's mask is the caller's |
| the kill arm | the payload at -1 is `True` | free (check `uexec_kill_arm_F_of_cred` at the trivial payload) |
| the rest | `emp` | -- |

`wild_pipe γp := inv seccN (∃ s, pipe_qfrag (pn_queue γp) s)` -- the queue
fragment parked with NO protocol; every link the universe needs
(`pipe_wlink`/`rlink`/`clink` are `={⊤}=∗`-shaped) opens it, and
`PipeProto.pipe_reg_of_inv` is the mould.  `secc_key` is preserved by every
row of `usys_fd_ok` (pipe adds pipe rows, dup copies, close removes, open
never runs) and by `usys_secc_ok` (the mask shrinks).

`ExecEntry.image_entry_secc S Q X := □ (∀ W', S -∗ □ secc_key W' -∗ my_pay
(uvis_gen W') Q -∗ X W')` is the seccomp twin of `image_entry_taint`.
`exec_bundle_of` takes BOTH `image_entry f ..` and `image_entry_taint T` and
the WALK decides (`exec_walk_of_pin` identifies the node unless `T`;
`exec_walk_of_taint` identifies it only by `T`); the seccomp program's
`exec(x)` uses the taint-shaped walk at `T := secc_tok k` and answers the
`image_entry_taint`-slot with `image_entry_secc`, proving `secc_key W'` from
its own key (the table is the caller's, the mask is the caller's -- the pin
added to `SpecKexec.exec_slot_pre`'s wand premises).

## 6. The claim's terminal arm, the era token and the licence (cut S2)

THE EXPORT IS AT EVERY OUTPUT BYTE, NOT AT THE END.  `AppUnionRec.union_al_tx`
calls `UnionOut.ucl_drain` at each `ObsUartOut Uart0 b`, which must return

    udrain_ret k seg := UT ∨ ∃ s0 vf, ⌜lm_good_out U s0 seg⌝ ∗ ⌜fstate_ok s0⌝
                        ∗ f0_typed gf s0 ∗ file_era_pin gf k vf ∗ f0_lb vf s0

with `s0` the era's already-drained state, under `ins seg = ins (open_seg
h)` and `obs_wire Uart0 seg ⊑ ch_acc CH`.  So the third arm must carry the
era's boot witness (`f0cw gf k s0`, which `WA k s0` is) and a pure fact
giving `obs_wire seg ⊑ lm_sess ps cs' s0 (ins seg)` at `cs' := cs ++
[ualt_code (US u)]`, `u` the wire's tail after the echoed line -- which
`lm_blk`'s definition makes literal.  `ins seg = I0` is pinned by
`inp_lb v I0` plus D4 (`lm_disc_in`: no input after the last line).

`UnionOut.ucl := peclV ..` is `gcl ∨ popenU`.  It gains a third arm and the
era gains ONE `mono_nat`:

    ucl' k ho H := UT ∨ (secc_clean_half k ∗ ucl k ho H) ∨ usecc k ho H
    usecc k ho H := secc_tok k ∗ ∃ v ps cs s0 I0 u,
        PIN k v ∗ ps_lb v ps ∗ cs_lb v cs ∗ inp_lb v I0 ∗ f0cw gf k s0
        ∗ cs_frozen v cs
        ∗ ⌜nlines I0 = S (length cs) /\ rest_of I0 = []
           /\ lm_of U (last body of I0) = LSecc _
           /\ lm_pro_ok ps cs (nlines I0) /\ lm_alts_ok' (the first length cs lines)
           /\ ch_acc H = lm_sess ps cs s0 I0' ++ body ++ [wl_nl] ++ u⌝

`EchoOut.era_pins` gains `ep_secc : gname` (only `EchoOut.v` and
`PipeOut.v:539` name pins' fields, so this is cheap); `era_full` gains
`mono_nat_auth_own (ep_secc v) 1 0`, split at `union_era_split` into TWO
HALVES: one in the claim's middle arm, one in the SHELL's per-round
credential (`uWcu' I p := secc_clean_half k ∗ uWcu I p ∨ useccomp_shape I`,
riding down from init's lend beside `fturn`).  `secc_tok k :=
mono_nat_lb_own (ep_secc v) 1` under `PIN k v`; it refutes either half.

THE LICENCE.  `secc_lic k := □ ∀ h H ev, riscv_cons_res k h H ==∗
riscv_cons_res k h (cons_step H ev)` follows from `secc_tok k` (the T arm
is closed under everything, the middle arm is refuted, the `usecc` arm is
closed under every event because `u` is existential and it reads no input
ghost).  `RiscvPtsto.app_iface` gains `ai_wild : nat -> iProp Σ` with the
law `ai_wild_lic : ai_wild k ⊢ □ ∀ h H ev, ai_cons k h H ==∗ ai_cons k h
(cons_step H ev)`; the union instantiates it at `secc_tok`, the trivial
application at `False`; `RiscvPtsto.riscv_wild := ai_wild riscvF_app_iface`;
`WpUart.cons_link_of_licence` / `cons_run_of_licence` / `cons_read_pay_triv`
get era-k twins.

THE DIRTY CREDENTIAL.  A tokenless console read pays
`ConsoleInv.cons_dirty_cred Wd = □ Wd`, and the boot (`ProofMain.v:755`),
`SpecFileread` (a dozen sites), `SpecSysRead`, `ProofFileread`,
`FsAbsInvFire`, `UkReadCons` and `UShLine` all fix `Wd := AppInv.app_sup`.
It becomes ONE new name, `AppInv.app_rdcred := app_sup ∨ riscv_wild (S
gen_id)`: the generic reader still pays `app_sup` (`iLeft`), the universe
pays `secc_tok` (`iRight`).  The token holder's dirty arm
(`UShLine.ush_read_pay_era_at`, which today turns `□ app_sup` into `T`
through the premise `app_sup -∗ lk_T L`) returns a THIRD outcome of
`ush_rd_ret`, "the era is wild": `secc_tok k ∗ position`; the loop laws
(`uWcu_read` and its siblings) refute it with the shell's half in every
non-seccomp shape and absorb it in `useccomp_shape`.  Rejected: a shared
reader token in an invariant -- `cons_acc`'s left arm returns the token
under a plain `==∗`, and two concurrent universe readers would both need
it at deposit time; and `Wd := app_taint`, which the universe never holds.

ENTERING THE ARM.  sh's round law at `LSecc ws`: after `gets` returns the
line and before the fork, sh opens the claim with its half and the
round's cursor (`uWcu I p` at the pre-fork shape), joins the halves,
bumps the `mono_nat` to 1 (keeping `secc_tok k`), freezes `cs`
(`PipeOut.pcs_freeze`, as the pipeline's terminal round does at
`peclV_blkN_open_gen`), and re-closes at `usecc` with `u := []`; it
forks, the child execs `/seccomp` with `secc_tok k` in its supplier, sh
waits.  Afterwards sh runs at `useccomp_shape I := secc_tok (S gen_id) ∗
era_pin .. v ∗ inp_lb v I ∗ cs_frozen_at v (nlines I - 1)` (no deed --
ruling B3's reason): the prompt and every later write go through the
licence, and a later read's `cs_lb`, one longer, is absurd against the
freeze (`PipeOut.cs_frozen_at_lb_absurd`) exactly as `uterm_read_law`
does it for the pipeline's terminal shape.

THE DRAIN.  `ucl'_drain` at the `usecc` arm: `lm_good_out s0 seg` from the
pure fact at `cs ++ [ualt_code (US u)]`, `u` read off `ch_acc H`; the
existing arms through `ucl_drain` unchanged.  The durable claim and the
boot-state admissibility are untouched: the seccomp round's `lm_step` is
the identity and no universe syscall retags a row.

## 7. The seccomp program (cut S3) and the round (cut S4)

`user/seccomp.c` is a verified program on the `Uk*` engine.  It forks and
waits, which no tree program does today (`ProgTree` has no fork node), so
it is proved sh-style rather than as a tree: `UCodeSeccomp.v`, the walk
of `main` (fork; child: `seccomp(mask)` -- row 23's post gives the new
mask -- then `exec(argv[1], argv+1)` through the taint-shaped walk at `T
:= secc_tok k` and `image_entry_secc`, the `fprintf` diagnostic and
`exit(1)` on failure; parent: `wait(0)`, `exit(0)`), an entry
`secc_image_entry` on `UkTreeEntry`'s mould, `FsImgCheck` pinning
`/seccomp` as inum 23 and an `FsSeccPin.v` twin of `FsGrepPin.v`.  THE ONE
PLACE THE MASK LITERAL ENTERS is the child's `secc_key` after row 23:
`Z.testbit (~0 & ~(1<<15) & ~(1<<6)) n = false` for `n ∈ B` is FALSE at
17-20 with the upstream binary (§1).

sh's round (S4): `UShURound`'s dispatch gains the `LSecc` arm through the
fork twin (`UkShCatForkTwin`'s shape), the exec resolution `(W)` of the
name `seccomp` at the image, the enter-the-arm step above, and the
terminal-shape laws for the main loop (`UShURoundLaws` at
`useccomp_shape`).  Then the knob flips (`adm_s := fun ws => bool_decide
(ws <> [])`) and the top theorem's statement changes only through the
model.

## 8. Honest limits

- The mask must be `B`, not `{open, kill}` (§1); pending the owner.
- Nothing is claimed about the console after the `seccomp` line within
  its cycle, nor about the universe's exit status.
- `x` ranges over alphanumeric words; a path with `/` is not a word of
  the class (the class is the union's).
- The universe's `sync`, `chdir` and `exec` of the image's binaries are
  admitted by the proof, not excluded -- they move no row.

## 9. Amendments after lane M and the second survey (owner, 2026-09-25)

Rulings that supersede the sections above where they differ.  The cut
plan is S0 -> S1 || S2 -> S3 -> S4 (worklist `projects/seccomp.md`).

§3, lane M's deviations ACCEPTED as the design:
- `uok s (LSecc ws) (US u)` requires `u <> []` (the hook law
  `LineModelLinks.lmh_cont_nonnil` quantifies over every admitted
  alternative); the decider's canonical witness is `US [wl_nl]`, not
  `US []`.  The claim is a prefix of the transcript, so nothing is lost.
- `FileDisc.parse_line` is untouched (the `LPipe` precedent): the union
  reads a seccomp body through `FileDisc.secc_parse` in
  `UnionDisc.uline_of_u`'s fallback, and `uline_nopipe` excludes `LSecc`.
  Extending `parse_line` would put seccomp lines into `fbody_ok`, where no
  knob refutes them.
- `secc_ok ws` := `wl_wf ws`, `ws <> []`, sh's MAXARGS (`S (length ws) <
  10`) and the line buffer -- `line_ok`'s shape.
- The exec failure at a seccomp line is a NEW `ralt`, `RSExec` (`exec
  seccomp failed`, code 17); the fork panic and the silent round reuse
  `RCFork`/`RCSilent`.
- The knob: `ulm adm adm_s`, `lm_line_ok := uline_okU adm_s`, `ubody_ok
  adm adm_s := fbody_ok \/ upipe_ok \/ usecc_ok`, `ulmG := ulm adm_u_g
  adm_s_off`; `UShURound.ush_line_union` is `False` at `LSecc` until S4.
  The decider is generic in the knob (`UnionDecU.u_seg_at`), so the
  knob-on decider `lm_disc_ulmS_dec` already exists.
- `ualt_code (US u) = 4 * encode_nat u + 3` is astronomically large for
  any real `u`: never let a conversion reduce a code.

§5, the universe:
- `image_entry_secc` is WITHDRAWN.  Instead `ExecEntry.image_entry_taint
  T Q X` is GENERALISED with the exec's own two key pins, which
  `SpecKexec.exec_slot_pre` already has in hand: `□ (∀ W', T -∗ ⌜uvis_fd
  W' = sts⌝ -∗ ⌜uvis_secc W' = secc⌝ -∗ my_pay (uvis_gen W') Q -∗ X W')`
  (so it takes `sts` and `secc`).  Every generic taint entry ignores the
  two premises; the universe reads `secc_key W'` off them (the table is
  the caller's -- `kexec_image_ok` pins `uvis_fd W' = sts` -- and the
  mask is the caller's).  `exec_bundle_of` keeps its shape and the
  taint-shaped walk `exec_walk_of_taint` at `T := riscv_wild k` is the
  seccomp program's and the universe's exec.
- The minter's credential is the ERA credential `riscv_wild (S gen_id)`
  (§6's `secc_tok`, read through the interface) and `□ uexec_wp`; it
  takes NO `app_sup` and NO `app_taint`: `chdir`'s AU needs no supply
  (`FsAbsInvFire.fsabs_chdir_pre`), and the kill arm is paid at the RIGHT
  disjunct of `UexecRet.ukill_cred_at` -- `ChildTok.kill_owed gn` is
  `my_pay gn (fun _ => True) ∗ True`, free at the trivial payload, beside
  the exit bundle (the table's close payments: pipe rows from
  `wild_pipe`, console rows `emp`, inode rows refuted by `secc_key`).
- `wild_pipe γp` is ALLOCATED at pipe's resume inside the slot: `uslot_F`
  is a WP, so `inv_alloc` runs under `fupd_wp` after one unfold of the
  fixpoint and before the Löb hypothesis is applied at the new key.
- The mask condition is `secc_masked m := forall n, n ∈ secc_B ->
  Z.testbit (bv_unsigned m) n = false` with `secc_B := [6;15;17;18;19;20]`;
  `usys_eff` returns 0 at every such number (and at every number outside
  0..63), so the dispatcher's out-of-range arm is what a blocked call
  hits.  `usys_secc_ok` ands the mask, so `secc_masked` is preserved.

§6, the plumbing is its own cut S0, ahead of S1 and S2 and shared by both:
- `RiscvPtsto.app_iface` gains `ai_wild : nat -> iProp Σ` (persistent,
  timeless) and `ai_wild_lic : forall k, ai_wild k ⊢ □ ∀ h H ev, ai_cons
  k h H ==∗ ai_cons k h (cons_step H ev)` -- the per-era twin of
  `ai_lic`; `riscv_wild := ai_wild riscvF_app_iface`.  The trivial and
  echo instances set it to `fun _ => False`; the union sets it to `fun _
  => False` in S0 and to `secc_tok k` in S2.
- `WpUart.cons_licence_at k` is the era-k licence; `cons_licence ⊢
  cons_licence_at k`, `riscv_wild k ⊢ cons_licence_at k`;
  `cons_link_of_licence` / `cons_run_of_licence` / `cons_read_pay_triv`
  are RESTATED at `cons_licence_at k` (one general lemma each) with the
  old forms as corollaries.
- `AppInv.app_rdcred := app_sup ∨ riscv_wild (S gen_id)` under a `GenId`
  binder (AppInv has none today; the era is the one of the console
  escrow's allocation in `ProofMain`).  Every `cons_dirty_cred app_sup`
  becomes `cons_dirty_cred app_rdcred`; the generic reader pays `iLeft`.
- In S0 the shell tier keeps `ush_rd_ret`'s two arms: the token holder's
  dirty arm gets `□ app_rdcred` back and turns it into `lk_T L` through
  the premise `(⊢ riscv_wild (S gen_id) -∗ lk_T L)` beside the E2
  readings `(⊢ app_sup -∗ lk_T L)`, discharged where those are (the
  instance is `False` there).  S2 replaces that premise with the third
  outcome ("the era is wild") and the loop laws' handling of it.

## 10. The claim's terminal arm, worked out against the tree (owner, 2026-09-25)

Section 6 sketched cut S2; the survey of the union tier (UnionOut, PipeOutN,
GenOut, EchoOut, UShURound*, UShLine, ConsoleInv, ProofConsoleread) fixes
the shapes below.  They supersede §6 where they differ.  The knob stays OFF
through S2: every shape and law lands, the transition is a lemma of the
claim that fires only at an ADMITTED `LSecc` line, and no `LSecc` line is
admitted until S4.

### 10.1 The flag and the token

`EchoOut.era_pins` gains `ep_secc : gname` (a `mono_nat`); `era_full`
gains `mono_nat_auth_own (ep_secc v) 1 0`.  `secc_flag v n :=
mono_nat_auth_own (ep_secc v) 1 n` -- the FULL authority, held by the
claim and by nobody else, so no process ever carries a half.  THE TOKEN
CARRIES THE FREEZE: 

    secc_tok k := ∃ v I0, UPIN k v ∗ mono_nat_lb_own (ep_secc v) 1
                  ∗ inp_lb v I0 ∗ ⌜0 < nlines I0 ∧ rest_of I0 = []⌝
                  ∗ cs_frozen_at v (nlines I0 - 1)

(persistent, timeless: two `mono_list` lower bounds, a `mono_nat` lower
bound and a discarded authority); `secc_tok k -∗ UPIN k v -∗ secc_flag v
0 -∗ False`.  `I0` is the era's input up to and including the seccomp
line.  The union's `ai_wild k := secc_tok k`; the trivial and echo
instances stay at `False`.  Every holder of the token -- the universe,
sh after its read, sh after a dirty read outcome, init after a panic --
therefore holds the two facts the wild read law needs, and nothing has
to travel beside the token.

### 10.2 The licence is for the two process events only

The interrupt's echo arm (`EvOpen`/`EvByte`/`EvClose`, `WpUart.cons_run`)
is stepped by the application's own echo law with the trace's discipline
in hand (`peclV_step_echo`'s premises come from the rx tag); a PROCESS
steps the claim only at `EvOut` (`out_link`, the write chain) and
`EvRead` (`cons_read_pay`).  So `ai_wild_lic` is stated for those two,
with the validity facts `cons_link` supplies:

    ai_wild_lic : forall k, ai_wild k ⊢ □ ∀ h H ev, ⌜wild_ev ev⌝ -∗
        ⌜cons_ev_ok H ev⌝ -∗ ai_cons k h H ==∗ ai_cons k h (cons_step H ev)
    wild_ev (EvOut _) := True;  wild_ev (EvRead _) := True;  wild_ev _ := False

(no `cons_hist_ok H`: the write link `out_link` does not carry it, and
the third arm needs only `read_ok` at `EvRead` and nothing at `EvOut`),
and S0's `cons_licence_at k` is the same statement; `out_link_of_licence`
and `cons_read_pay_triv` get their `_at k` twins, `cons_run_of_licence`
does not (nobody needs it at era k).

### 10.3 The claim: three arms, the old lemmas refute the third

    ucl k ho H := UT
                  ∨ (∃ v, UPIN k v ∗ secc_flag v 0 ∗ peclV pg U ucparams ∅ uwa k ho H)
                  ∨ usecc k ho H

The NAME `ucl` is kept (seven files carry `Hcons : riscv_cons_res = ucl
ug` as a context), so every consumer sees the new shape through the old
name.  `usecc k ho H` holds, for the era's pins `v`, the state at the
moment of the transition (10.4) and nothing that moves afterwards:

    ∃ v ps cs s0 I0 u,  UPIN k v ∗ secc_flag v 1 ∗ turn_auth v P ∗ ps_auth v ps
      ∗ cs_frozen v cs ∗ Elist_auth v E ∗ dl_cnt v (1/2) (length (ch_dl H))
      ∗ dl_list_auth v (ch_dl H) ∗ WA k (Some s0) ∗ f0cw gf k s0
      ∗ ⌜ P = length (lm_proc_before U ps cs s0 I0)
          ∧ nlines I0 = S (length cs) ∧ rest_of I0 = []
          ∧ lm_of U (bodies_of I0 !!! (nlines I0 - 1)) = LSecc ws  (admitted)
          ∧ lm_pro_ok ps cs (nlines I0) ∧ lm_alts_ok' s0 I0 cs (the first length cs lines)
          ∧ ch_acc H = lm_sess_pre ps cs s0 I0 ++ u      (the session with the last
                                                          line's continuation omitted)
          ∧ ch_dl H = echoed (ch_log H) ∧ snd <$> ch_dl H = I0 ∧ gin_pure k (ch_log H) (ch_dl H) cs
          ∧ ch_arm H = None ⌝

`u` is the wire's tail after the echoed line, ARBITRARY.  What each arm
of `usecc` is for:
- `secc_flag v 1` refutes nothing and is what `secc_tok` was minted from;
  `secc_flag v 0` in the MIDDLE arm is what refutes the middle arm under
  the wild licence.
- `turn_auth v P` (the claim's half; sh keeps its half) and the pure
  `P = …` are what REFUTE every clean presenter: every `ucl_step_*` /
  `pwc_blkU_file*` / `eclN` step takes `turn v P'` from its caller, the
  halves agree, and a writer at the cursor of the seccomp line's read is
  pinned to that line -- `lm_proc_before` grows by at least the prompt
  per line, so an `inp_lb v I` presenter has `I = I0`; then a pipeline
  block at `I0` contradicts `LSecc`, a `_pro` write's `cs_lb` is longer
  than the frozen `cs`, a `_blk` write at `I0` would append to a frozen
  `cs`, and a plain `ucl_step_write` at `P` reads past the end of
  `lm_proc_stream ps cs s0 I0`.  So the old lemmas hold at the new `ucl`
  with their statements UNCHANGED and the third arm closed by refutation.
  FALLBACK, only if one of those refutations turns out underivable from
  lane M's model: that lemma's outcome gains the escape `∨ (secc_tok k ∗
  cs_frozen_at v (nlines I0 - 1) ∗ inp_lb v I0 ∗ ⌜I = I0⌝)` and its
  consumers move to the wild shape (10.5) at their own `I`.
- `dl_cnt` (the claim's half) and `dl_list_auth` keep serving sh's TOKEN
  reads: under `read_ok` and `ch_dl = echoed ch_log` every read delivers
  `ws = []`, so `rd_retV`'s right arm is returned with its `⌜ws = []⌝`
  disjunct; the wild licence's `EvRead` is the same fact with no half
  presented.  `EvOut b` under the licence extends `u`.
- The log is FROZEN in this arm: an `EvOpen h c cs` carries the rx tag
  `lm_disc U h ∨ UT`; `lm_disc U h` is refuted by D4 (`lm_d4`: a line
  admitting a terminal alternative whose merge is `True` is the era's
  last, and `h`'s input has a byte after it -- `cons_ev_ok`'s index
  clause puts the new byte at `length (ch_log H) + 1 + f`), and `UT`
  sends the claim to its first arm.  This is why the arm can say `ch_dl
  = echoed ch_log`.
- `WA k (Some s0) ∗ f0cw gf k s0` and the pure session fact are the
  drain's: `ucl_drain` at this arm returns `udrain_ret`'s right arm with
  `lm_good_out U s0 seg` at the choices `cs ++ [ualt_code (US u')]`, `u'
  := u` if `u <> []` else `[wl_nl]` (`uok` needs a non-empty `u`; the wire
  is a prefix either way).

### 10.4 The transition is the claim's READ step at the seccomp line

sh reaches the claim only through console events, and its halves (turn,
dl) are not in the read link, so the arm change happens INSIDE the
union's read wrapper of `peclV_step_read` (the law behind `rk_rd`): after
the generic step, if the delivered input `I' := snd <$> (ch_dl ++ ws)`
now ends in a complete, ADMITTED `LSecc` line that was not complete
before the read, the wrapper (in the `gcl` arm -- `popenV` cannot be the
arm at such a read: `gin_pure`'s `nlines ≤ S (length cs)` against the open
round's frozen `cs`) bumps the flag to 1, freezes `cs` (`cs_freeze`, at
`length cs = nlines I' - 1`, derived from `gcl_pure`), records the
session fact off `lm_out_pure`, and re-closes at `usecc` with `u := []`.
The reader gets `rd_retV` as before PLUS `secc_tok k ∗ cs_frozen_at v
(nlines I' - 1)` in that case (the union's `lk_rr` carries it), which is
what sh's read law turns into the wild shape.  Nothing else in sh's round
is a transition: the fork panic, the exec failure and the silent round
are all inside the arm's arbitrary `u` (so lane M's `RSExec`/`RCFork`/
`RCSilent` codes at `LSecc` are never chosen by the claim; they stay for
the hooks).

For this the claim must KNOW, at the read, that no logged entry lies
beyond the delivered newline: `GenOutHist.gin_pure` gains the conjunct
`forall e, e ∈ pops -> lm_disc M (le_hist e)` (maintained at `EvClose`
from `garm_era`'s `lm_disc M h`; every other step leaves `pops` alone).
An entry beyond a seccomp newline then contradicts D4.  This is the one
change in the generic tier.

### 10.5 The wild shape of sh, and of init; the union's `lk_T`

    T' := UT ∨ secc_tok (S gen_id)
    useccomp_shape I := secc_tok (S gen_id) ∗ ∃ v, era_pin (fgn_echo gf) (S gen_id) v

The union's `LinkRec` sets `lk_T := T'` (today `UT`): every LinkRec
family's taint arm and the lease's tainted arm (`ush_lease`, `ush_rd_ret`'s
right arm) absorb the token as they absorb the taint, and the two
premises of `ush_read_pay_era_at` are discharged at the union as
`app_rdcred -∗ T'` (`app_sup -∗ UT` as today, `riscv_wild (S gen_id) -∗
secc_tok` by definition) and `T' -∗ app_rdcred` (both disjuncts).  S0's
interim premise `(⊢ riscv_wild (S gen_id) -∗ lk_T L)` is then the
`iRight` of `T'`, and its `False` discharge goes away.  The deed
(`ush_deed_at`) and the pipeline families (`pwc_blkU`, `ptkU`, the
shapes `PT`/`PD`) stay at `UT`: no clean presenter survives the third arm
(10.3), so they never meet the token.

`uWcu I p` gains `useccomp_shape I` as a fourth arm, `uWbf I` a wild arm
of the same two resources (the fork-panic path hands it to init through
sh's exit payload).  No deed in the wild arm (B3).  `uWcu_taint` becomes
`era_pin -∗ T' -∗ uWcu I p` (the `UT` half as today, the token half the
wild arm), so every law that today ends a taint case with `uWcu_taint`
ends a token case the same way.  The laws at the wild arm:
- `uWcu_read` is VACUOUS.  The post-read `Pm (I ++ l ++ [wl_nl])` carries
  `lk_rres v (I ++ l ++ [wl_nl])`, i.e. `cs_lb v cs0` with `length cs0 >=
  nlines I`, and the reading's `⌜length (ch_dl CH) = length I⌝` beside
  `inp_lb v (snd <$> ch_dl CH)`; the token's `inp_lb v I0` is a bound of
  the same list, so `I0 `prefix_of` I` and `nlines I0 <= nlines I`, and
  `cs_frozen_at_lb_absurd` closes it (`uterm_read_law`'s argument).
  This matches the kernel: the console marks its escrow dirty only when
  a tokenless reader CONSUMES bytes (`ProofConsoleread.cr_racc` at `None`:
  `⌜d = 0⌝ ∨ cons_dirty_lb`), and under the third arm nobody consumes, so
  a wild-era read never returns.  The union's `lk_rr` must carry the
  count and the bound; check `urr`.
- a DIRTY read outcome at the token (`ush_rd_ret`'s right arm at the
  `secc_tok` half of `T'`: another reader consumed bytes while the call
  slept) is unreachable in fact and unrefutable in the proof; the clean
  read laws send it to the wild arm like the taint case, which is a
  legal state at any `I` because the token carries its own `I0`.
- the prompt law and the panic law write through `out_link_of_licence_at`
  (from the token); the kill law is from `UT` as today; `uHwbl_u`,
  `uWcu_inp`, `ush_prompt_law_u`, `uHpanic`, `ush_kill_law_u` each gain
  the arm.
- init's prologue after a wild-era fork panic goes through the licence
  from `uWbf`'s wild arm (S4 proves the path; S2 states the arm).

### 10.6 What S2 delivers and what it leaves to S4

S2: 10.1-10.5 with every existing law re-proved at the new `ucl`/`uWcu`/
`uWbf`, `union_cons_lic` (from `UT`) and the wild licence (from
`secc_tok`), `ucl_drain` at the third arm, the read wrapper's transition,
`union_era_split` at `secc_flag v 0`, and the U-tier premises threaded.
Audits unchanged.  S4: `ush_line_union` at `LSecc`, sh's round law at the
wild shape (fork; the child's exec of `/seccomp` with `secc_tok` in its
`Pay`; wait; prompt through the licence), init's wild arm on the panic
path, the knob, the top theorem's statement through the model.

### 10.7 Rulings from lane S2 (owner, 2026-09-25)

- THE MODEL STAYS: `LineModelLinks.lm_hooks` requires an admitted
  NON-terminal alternative at every line (`lmh_pan_ok`/`lmh_pan_panic`:
  a panic is non-terminal by `lml_term_nopanic`; `lmh_noc_ok`/`lmh_noc_free`
  and `lmh_exf_ok`/`lmh_exf_free` with `lmh_free_term`: the silent pad and
  the exec failure are admitted and non-terminal everywhere, and
  `lm_alts_pad` pads the drain's lines with the silent pad).  So `uok`
  at `LSecc` keeps `RCFork`/`RSExec`/`RCSilent` beside `US u`, and the
  presenter "block-first byte at the seccomp line with a non-terminal
  admitted alternative" is unrefutable in the third arm.  It is the ONE
  escape: `ucl_step_write_blk` / `union_write_link_blk` may return
  `secc_tok k ∗ cs_frozen_at v (nlines I0 - 1) ∗ inp_lb v I0` (with `I =
  I0`, the presenter's own line) instead of progress; inside
  `GenLinksLine.gl_blk` it is absorbed into the family taint, so
  `glinks`' statement is unchanged.  Every other presenter is refuted
  (`write_first`: `turn 0 < P`; `write`: the stage byte pins the echoed
  list against the frozen `cs`; `_pro`: the prologue pin likewise; the
  `pre <> []` family bytes and `pwc_blkU_file`: `pext`'s full `cur_half`;
  `pwc_blkU_file_empty`: a pipeline line is not the wild line).
  `pblkU_ecl_holds` takes the premise that the line is not the wild
  line, discharged at its pipeline-line callers.  CONSEQUENCE FOR S4:
  sh's round at `LSecc` never presents a block-first byte; its
  diagnostics go through the licence.
- `lk_T := UT ∨ secc_tok (S gen_id)` IS SOUND BY PINNING THE ERA: the
  union's link record's pin is `gPIN k v := UPIN k v ∗ ⌜k = S gen_id⌝`,
  `GenLinksLine.gl_taint` and `ReadRec.rk_rd_taint` (and every taint law
  the records state at an arbitrary era) take the family's `PIN k v`; a
  token of era `k` licenses only era `k`'s claim.  Rejected: an
  era-indexed `lk_T` (a sweep of the generic sh tier) and a third read
  outcome with era-indexed wild arms in the families.

### 10.8 Lane S1's deviations, accepted (owner, 2026-09-25)

- THE UNIVERSE'S OWN EXEC needs no credential: it is the closed generic
  bundle (`fsabs_exec_half` + `ax_hops_triv`, the mould of
  `xv6_sbundle_of_supply`'s exec branch) with both slot wands answered
  from the Löb hypothesis at the exec'd key.  The taint-shaped walk at
  `T := riscv_wild` is the seccomp PROGRAM's (S3), where a name to
  resolve is in hand.
- The generalised `image_entry_taint T sts secc Q X` is stated
  `∀ sts` in the U-tier exec rules and `TreeExec` (no single key in
  scope), and `∀ sts secc` at sh's entry (`UShKernel`, `UInitSh`), with
  `image_entry_taint_all_elim` giving the unpinned wand back.
- `secc_key` is persistent but NOT timeless (`wild_pipe` is an
  invariant).  `UexecSecc.useccomp_image_entry_taint` answers the
  generalised taint entry at a table in the universe and a masked mask;
  S3 uses it.
