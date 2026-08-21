# forkret_park: the plan to retire the last assumed Link

> **STATUS 2026-08-21.** Steps A–D and E1–E2 have landed. The park is PROVED
> (over the real `SpecForkret.FORKRET` at `LinkForkret.Forkret`, so its cone
> carries no first-related axiom), and `syscall_env` finally has a producer
> — the one `LinkSyscall.v` has been owing since the dispatch was linked.
> What is left is E3, and it is BOOT-CHAIN work: three rows of `park_env`
> have no producer anywhere in the tree (`is_ftable`, the `wait_lock`
> invariant, `devintr_caps_any`), and two of those need cells carved out of
> BSS that `BootCarveMain.v` currently drops. Read §2 and Step E before touching anything; both
> record designs that were tried and do not type.

`LinkForkretPark.ForkretPark.forkret_park` is the one assumed Link in the boot
cone, and the assumption every proven process-side function carries
(`forkret`, `kfork`, `main`, `sys_fork`, `syscall`, `userinit`, `usertrap`).

## 0. What has landed

| commit | what |
|---|---|
| `f2646655` | **forkret is PROVED** — `ProofForkret.fkr_boot`, `Qed`, both arms of the `== -1` test, no admits anywhere in the cone |
| `48baeac0` | `SpecForkretParkPaid.v` restored, restated against forkret's real contract |
| `d6bb1464` | the bio slot supply has a CANONICAL ghost name (`Xv6Cameras.bioslotG`, `bioslot_name`) |
| `bbcd2687` | three bslots per proc slot, resident at every state, returned on every path |
| *(this commit)* | `UsertrapRes.park_own`; the closer takes `fs_ready`; `ForkretParkClose.v` restored |

## 1. Resource inventory — EVERY row now has a source

`SpecForkretParkPaid.forkret_park_pkg`'s seven conjuncts:

| conjunct | status |
|---|---|
| `kernel_text`, `wire_inv`, `kmap_at tramp_vpn tramp_ppn KP_rx` | persistent, free |
| `procs_inv γs` | persistent; also inside `ut_caps` (`ut_caps_procs`) |
| `pslot_used_at pa` | persistent, already in `SpecAllocproc`'s post |
| `stack_own (ks+4096) av` | **AVAILABLE.** `ProcDefs.kstack_free` is a `proc_dormant` conjunct and `SpecAllocproc:208` returns it; `ProcDefs.kstack_free_at` recovers the words at the concrete `ks`. The old header calling this "a real hole in the chain" is WRONG. |
| the residue closer | the subject of this plan — see §2 |

Budget, and it is exact: `KSTACK_AV = 342 = K_usertrap = 4 + kv_frame_slots(90)
+ K_syscall(248)`. So `av := KSTACK_AV` meets `K_usertrap <= av` on the nose,
and `(trap_res eb + av2) = av - 6 = 336` gives `av2 = 336` at `eb = false`,
`246` at `eb = true` — both ≥ `K_kexec = 184`. The park works at EITHER `eb'`,
though this revision's scheduler only ever produces `false`.

`ForkretParkClose`'s residual `park_own` is now fully sourced: the `initproc`
share is persistent (userinit discards the cell right after its store at
+0x14), and `bslots 3` landed in `bbcd2687` — **both park call sites already
hold their three units at the `iMod`** (`ProofUserinit.v:671`,
`ProofKforkB5.v:204`), where before there was no source at all. They are
dropped there today, which is sound and is exactly the right staging.

## 2. THE ONE REAL PROBLEM, and how it was solved

`ForkretParkClose.forkret_park_closer_intro` has to produce
`UsertrapRes.ut_res_bare`, whose two halves are `ut_caps` (which carries
`FsReady.fs_ready` as a conjunct) and the syscall environment `Rsys`
(concretely `ProofSyscall.syscall_env`, itself derived from `fs_ready`).

**AT USERINIT'S PARK, `fs_ready` DOES NOT EXIST YET.** forkret's boot arm is
what establishes it (`fs_ready_establish`), and that runs *after* userinit
parks. So a closer that had to OWN the file system is unbuildable at that
site. This is not a plumbing gap; it is an ordering fact.

(Note also: `syscall_env` has no producer anywhere. `LinkSyscall.v` says so —
"Establishing the environment is the boot chain's job and is still owed". An
earlier revision of this file called it "on the free list" because it is
persistent. That was wrong: persistent means duplicable once you have it, not
conjurable.)

**THE FIX (2026-08-21): move the RESOURCE, not the proof.** The residue
closer takes `fs_ready` as an ARGUMENT. forkret is the party that can pay it,
on both arms and for the same reason the `if (first)` exists at all:

* steady arm — `first_tok`'s steady disjunct IS `first_addr ↦₄□ 0 ∗ fs_ready`,
  persistent, so putting the token back into the block costs nothing;
* boot arm — forkret establishes it itself, at the release store at +0x38,
  and holds it (persistent) to the `c.jalr`.

`+0x64` is where the two arms meet, which is `fkr_tail`, which is where the
closer is applied. So one premise on `fkr_tail` and one extra argument at the
application is the whole proof-side cost.

### WHY NOT INVERT THE DEPENDENCY (the earlier plan, and why it is wrong)

An earlier revision of this file proposed building the residue inside
forkret's own proof: give forkret a wand `□ (fs_ready -∗ ut_caps N ∗ Rsys …)`
and have it call `forkret_park_closer_intro` at its tail.

**THAT CANNOT TYPE.** `ProofForkret` is a functor over `USERRET_CLOSED`, and
`usertrap_res_bare` is a `Parameter` of that module type — abstract inside the
functor, and re-exported by `ProofForkret` as `UC.usertrap_res_bare`. forkret's
conclusion feeds it to `UC.wp_userret_closed`. `ut_res_bare Rsys pt' ksp` is
not convertible with an opaque module parameter, so forkret cannot BUILD the
residue at all — only receive it and pass it on. Inverting would have meant
adding an intro rule to `USERTRAP_RES` and threading an abstract syscall
environment through the module type, i.e. de-abstracting the residue for
every consumer, to fix an ordering problem that one extra wand argument
fixes.

Keep the closer premise. Hand it `fs_ready`.

## 3. Steps, in order

### Step A — `ForkretParkClose.v`, restored and restated — **LANDED**

Recovered from `git show 4bbc418f:iris/ForkretParkClose.v`. It is a LEAF —
nothing requires it — so it sits after `SpecForkretParkPaid.v` in
`_CoqProject` (line 1320). `park_own` moved out to `UsertrapRes.v`.

`forkret_park_closer_intro` now takes the DERIVATION rather than the
environment, and the `V` parameter is gone (the shape is `∀ pt'`):

```coq
  Lemma forkret_park_closer_intro Rsys N av :
    ut_wf N -> (K_usertrap <= av)%nat ->
    (fs_ready -∗ ut_caps N ∗ Rsys (un_f N) (un_pj N) (un_bn N) (un_fn N)) -∗
    park_own N -∗
    (∀ (h : CpuId) (pt' : uptd) (V' : pprivate),
       ⌜pv_upt V' = pt'⌝ -∗ ⌜ud_data pt' = ud_pas pt'⌝ -∗ ⌜proc_pt_wf pt'⌝ -∗
       fs_ready -∗
       forkret_yield (CID := h) (un_f N) (un_pj N)
         (add_vec (un_ks N) (mword_of_int 4096)) (un_pid N) av V' -∗
       fd_slots FDSPARE -∗ iref_slots IREFSPARE -∗
       ut_res_bare (CID := h) Rsys pt'
         (add_vec (un_ks N) (mword_of_int 4096))).
```

The wand is NOT `□`: it is applied once, so the weaker premise is the right
one. The two page-table facts are `clear`ed — `ut_res_bare` does not restate
them; they are handed in so forkret can prove them of the descriptor it
actually ends on.

`forkret_park_pkg_intro` takes `procs_inv (un_s N)` as its own premise now
(it used to read it off `ut_caps` via `ut_caps_procs`, and `ut_caps` is behind
the wand). That premise is free: it is persistent and both parkers hold it.
`ut_caps_procs` is kept as the fact that makes it free rather than new.

Requires that had to be added: `FsReady`, `UserPtTree` (`uptd`),
`ProcPtOwn` (`proc_pt_wf`/`ud_data`/`ud_pas`), and `!bioslotG Σ` in the
section context (`park_own` names `bslots`).

### Step B — the contract change — **LANDED, and it is one line**

`SpecForkret.wp_forkret_gen_body`'s residue closer gains `FsReady.fs_ready -∗`
between the three pure premises and `forkret_yield`. `URes` stays abstract;
`Rsys` never appears; `FORKRET` still includes `USERTRAP_RES` and is still
stated at `usertrap_res_bare`. Nothing else in the contract moves.

`SpecForkretParkPaid.forkret_park_pkg`'s closer gains the same argument in the
same position, so the park can still partially apply it with the two
allowances.

### Step C — `ProofForkret.v` — **LANDED, four sites**

* `fkr_tail` gains a `FsReady.fs_ready -∗` premise (introduced `#Hfsready`)
  and passes it at the `iDestruct ("Hyield" …)`;
* `fkr_boot`'s closer premise gains the argument, and its call into
  `fkr_tail` hands over `Hfsr` — the one `fs_ready_establish` minted;
* `wp_forkret`'s steady arm hands over `Hfsready`, destructured out of
  `first_tok`'s `Hdone` at +0x24;
* the boot arm needs no change: `fkr_boot` produces what it owes.

`ProofForkret.v` rebuilds green in 2m26s.

### Step D — `ProofForkretPark.v`, restored — **LANDED**

Recover with `git show 4bbc418f:iris/ProofForkretPark.v` (222 lines, 5 helper
lemmas + 1 theorem, 0 admits). It is NOT a Löb argument — the header says so:
"Nothing here recurses: the NEXT park is inside the trap loop's own theorem".
The retype, itemised:

* functor over `SpecForkret.FORKRET` (instantiated at `LinkForkret.Forkret`),
  NOT the deleted `FORKRET_NF`. This makes the park cone carry **no
  first-related axiom at all**, which the deleted version could not say.
* delete the `iDestruct (procs_inv_lookup …) as "#Hlk"` line and `"Hlk"` from
  the `with` string; insert `"Hpinv"` after `"Hpc"`; drop the `s`/`Rlk`
  explicit arguments; add `Hgl : γs !! j = Some γl` as the second pure
  argument (it already comes out of `p_sched_at_proc`).
* drop `pt`, the `eq_refl`, `Hnorm`, `Hptwf`, the `[]` for the lock string
  and the trailing `done.` (`Hnorm`/`Hptwf` left the park's premises: they are
  handed to the closer by forkret instead.)
* rename `Hpr` → `Hkx` and prove `(K_kexec <= av - 6 - trap_res eb')%nat`
  instead of the `K_prepare_return` one. `6 + trap_res true + K_kexec = 280 <=
  342 = K_usertrap`, so it follows from `Hut` by `lia` — no new premise. NOTE
  `trap_res` is a `Definition` (`IntrDefs.v:570`), not a `Notation`: `lia`
  will not see `trap_res true = 90` on its own. Keep `fkp_trap_res_le` and add
  an explicit `trap_res true` fact, or `rewrite /trap_res` first.
* the closer conjunct STAYS in `forkret_park_pkg` (see §2 — the inversion
  does not type), but its wand now takes `fs_ready`, so the `iAssert` that
  partially applies it with `Hfd`/`Hirsp` grows three pure binders and one
  resource binder:

  ```coq
    iAssert (∀ (h : CpuId) (pt' : uptd) (V' : pprivate),
               ⌜pv_upt V' = pt'⌝ -∗ ⌜ud_data pt' = ud_pas pt'⌝ -∗
               ⌜proc_pt_wf pt'⌝ -∗ fs_ready -∗
               forkret_yield (CID := h) γf (proc_addr j) … -∗
               FR.usertrap_res_bare (CID := h) pt' …)%I
      with "[Hclose Hfd Hirsp]" as "Hclose".
    { iIntros (h pt' V') "%HV %Hnrm %Hwf Hfsr Hy".
      iApply ("Hclose" with "[%] [%] [%] Hfsr Hy Hfd Hirsp"); done. }
  ```

UNCHANGED and worth knowing: the 5 helper lemmas (`fkp_img_nth0/1`,
`fkp_ret_pc`, `fkp_trap_res_le`, `fkp_pstate_split`), the `valid_context`
unfold, the `p_sched_at_proc` payload read, the `proc_lock_res` reconstruction,
the register/pc bookkeeping, and **the `eb'` handling** — `eb'` is introduced as
a variable, never case-split, and passed straight through as forkret's `eb`.
No value of `eb'` is ever fixed and no enabled base is assumed anywhere.

### Step E — the syscall environment's producer

**THE OLD PLAN WAS WRONG ABOUT THIS STEP'S SIZE.** Writing Step D exposed a
second abstraction wall, and it is the one that actually blocks the Axiom.

`forkret_park_pkg (fun h => usertrap_res_bare) …`'s last conjunct is a wand
whose CONCLUSION is `usertrap_res_bare` — a `Parameter` of
`SpecUsertrap.USERTRAP_RES`, hence opaque to userinit and kfork.
`ForkretParkClose.forkret_park_pkg_intro` produces
`forkret_park_pkg (fun h => ut_res_bare Rsys) …`, not convertible with the
opaque one. And underneath that, `syscall_env` had no producer anywhere —
`LinkSyscall.v` has said so all along.

#### E1 — the channel — **LANDED**

`ut_park_intro_body` (`UsertrapRes.v`, outside the section so the hart is a
free argument) states the producer once, `_body`-style, over an abstract
bare residue `URB`. Two module types beside `UtResFits` carry it:

```coq
  Module Type USERTRAP_RES_PARK.  Include SpecUsertrap.USERTRAP_RES.
    Parameter usertrap_res_bare_park : … ut_park_intro_body … .  End
  Module Type USERTRAP_PARK.      Include SpecUsertrap.USERTRAP.
    Parameter usertrap_res_bare_park : … ut_park_intro_body … .  End
```

It could NOT go in `SpecUsertrap.v`: `UsertrapRes.v` requires *it* (its foot
is the `<: USERTRAP_RES` fit check), so `SpecUsertrap` cannot name
`ut_names`, `ut_caps`, `park_own` or `ut_res_bare`.

Threaded through the four module types that include the residue —
`SpecUservec.USERVEC`, `SpecUserretClosed.USERRET_CLOSED`,
`SpecForkret.FORKRET`, `SpecForkretParkPaid.FORKRET_PARK_PAID` — and
re-exported one line each in `ProofUservec`, `ProofUserretClosed`,
`ProofForkret`, `ProofForkretPark`. `ProofUsertrap` is sealed at
`USERTRAP_PARK` now and gets the proof by `Module Fits := UtResFits SY` —
the fit check has always been a functor over `SYSCALL` for exactly this
reason, so the entry is proved there and renamed here.

#### E2 — the producer — **LANDED**

Three lemmas, and between them they say what parking a process costs:

* `UsertrapRes.ut_park_caps N` / `ut_caps_of_park` — `ut_caps` splits on a
  second axis, orthogonal to persistence: what `FsReady.fs_ready` supplies
  (eleven conjuncts) and what it does not (seven, all persistent, all in
  existence before either parker runs). `ut_caps_of_park` is the join, and
  it is a WAND because the file system is owed later, by forkret.
  The disk row is the only one that is not a copy: `fs_ready` quantifies the
  three ring pages (R1) while `ut_caps` names them at the record's fields,
  so `FsReady.disk_geom_agree` identifies them. `un_pr` is the one field
  `fclose_ties` does not reach, so its equation rides beside it.
* `SyscParkEnv.sysc_park_extra γtk` — the four rows the file system does not
  carry: the nextpid lock, `procs_avail None`, the ticks lock,
  `console_ready`. A new leaf file, because `SpecSyscall` has to name it and
  cannot see `UsertrapRes`.
* `ProofSyscall.syscall_env_park` — **the producer `LinkSyscall.v` has been
  owing since the dispatch was linked.** From `first_done` plus
  `sysc_park_extra` plus four rows the caller holds anyway for `ut_caps`
  (`wait_lock`, `is_ftable`, `procs_inv`, `disk_geom`) it builds
  `syscall_env γf (proc_addr (fcn_j fn)) (fcn_bio fn) fn`.
  `sysc_ties` is DERIVED, not taken (`sysc_ties_of_fclose`): fourteen of its
  equations are `fclose_ties`' verbatim, two are that record's `fcn_bio` row
  read twice, and four are pure premises the caller owes anyway.

`UsertrapRes.ut_res_bare_park` ties the two together at an abstract `Rsys`,
and `UtResFits.usertrap_res_bare_park` instantiates it at
`SY.syscall_env` with `SY.syscall_env_park` as the wand.

#### E3 — WHAT IS LEFT, and it is BOOT-CHAIN work, not park work

The machinery is in place. What remains is that neither parker HOLDS
`park_env N`, and — surveyed 2026-08-21, after E2 landed — **three of its
rows have no producer anywhere in the tree.** They are not missing plumbing;
they are resources nobody has ever built.

`park_env N = ut_park_caps N ∗ sysc_park_extra (un_tk N)`, eleven rows:
`fclose_ties`, `un_pr = fsc_printk`, `procs_inv`, `is_kstack`,
`devintr_caps_any`, the `wait_lock` `is_lock`, `is_ftable`, `disk_geom`, the
nextpid lock, `procs_avail None`, `is_tickslock`, `console_ready`.

##### The three with no producer

**`is_ftable γft γf`.** Only ever consumed (`SpecFilealloc`,
`SpecPipealloc`, `ProofSyscall`). `fileinit()` IS proved and IS called by
main (`ProofMain.v:1518`), and `SpecFileinit.v`'s header says the rest
outright: *"Whether the lock then becomes an `is_lock` over the open-file
table is the caller's ghost step, not fileinit's"* — and main currently
DROPS all three of its outputs (`iIntros (mfi) "Hcg Hpc %Hcsfi _ _ _"`).
The ghost step needs `ftable_res γf`, which at `M = ∅` is NFILE copies of
`a_fref k ↦₄ 0 ∗ file_fields k 1 C ∗ file_pay γ k 1 C` — i.e. the ftable's
`file[NFILE]` array has to be CARVED OUT OF BSS (`BootCarveMain.v`) and its
authority allocated. That is the real cost.

**The `wait_lock` `is_lock`.** Same shape, and `BootCarveMain.v:1669` names
the gap in passing: `wait_res` is `∃ ps, parents_own ps` =
`⌜length ps = NPROC⌝ ∗ [∗ list] j ↦ v ∈ ps, p_parent (proc_addr j) ↦₈ v`,
and of `p_parent` (+56) that file says *"claimed by no bundle and is dropped
with the padding"*. So the cells exist in the image and the carve throws
them away. Un-drop them, thread `parents_own` to main (which already holds
`lk_raw wait_lock_addr`), `is_lock_intro`.

**`devintr_caps_any`.** The `□ ∀ h` form. Six of `devintr_caps`' seven
members are hart-free and main has all six (`dev_inv`, `console_caps`,
`disk_geom`, the virtio `is_lock`, `tick_keeper`'s real arm, `procs_inv`);
the seventh is `timer_cap`, which is per-hart and which `BootChain.v:566`
mints with `timer_cap_intro`. So this one is assembly, not construction —
but the `∀ h` quantifier has to be discharged at every hart, which is what
`UsertrapRes.v`'s note on `devintr_caps_any` explains the boot chain can do.

##### The one that is a decision, not a gap

**`procs_avail None`.** userinit is handed `procs_avail (Some (S np))` and
returns `Some np`. `sysc_park_extra` wants the SEALED form, and
`ProcAvail.procs_avail_seal` is a one-way fupd. Sealing it at the park is
the right move and is exactly symmetric with the `kalloc_env_at_seal`
userinit already performs three lines earlier — but it changes userinit's
postcondition, so check `ProofMain` discards the row (the kalloc analogue's
comment says main does, "the boot chain has no further kalloc client").

##### And then the easy part

**kfork (`ProofKforkB5.v:204`)** needs none of the above: its parent holds
`syscall_env`, and `syscall_env_all` / `_console` / `_first` project out ten
of the eleven rows, with `is_kstack` already a premise at the site. The one
exception is `devintr_caps_any` — a `ut_caps` conjunct usertrap holds and
does not pass down — so it wants threading usertrap → syscall → sys_fork →
kfork. Persistent, so four contract widenings and no proof obligations.

**userinit (`ProofUserinit.v:674`)** has `procs_inv`, the nextpid lock,
`printk_env` and `procs_avail` in scope, and `is_kstack` from allocproc. It
needs the three built rows plus `disk_geom` and `is_tickslock` and
`console_ready` threaded from main, which holds all three
(`ProofMain.v:1579`, `:1084`, `:590`). Note it currently picks the ftable's
gname out of thin air — *"THE FTABLE'S GNAME IS PICKED HERE, and `γp` is as
good as any"* — which stops being true once `is_ftable γft γf` is a premise:
`wp_userinit_sconf_body` grows a real `γf`.

Then: build `N` (mostly the ambient `fsc_*`/`icfg_*` fields, which is what
makes `fclose_ties` hold), reshape the park closer into
`forkret_park_pkg`'s (mechanical — `forkret_yield` IS `ut_trap_parked ∗
proc_priv_nopt`, and the two pure page-table arguments are unused), switch
both callers from `FORKRET_PARK` to `FORKRET_PARK_PAID`, and replace
`LinkForkretPark.v`'s `Axiom` with an application of `ProofForkretPark`.

**Suggested order:** the two BSS carves first (they are independent of
everything else and each is one file plus threading), then
`devintr_caps_any`, then userinit, then kfork, then the Link.

## 4. How to build

    cd /shared/xv6iris-5 && QUIET=1 ./gcp-rocq/run-on-gcp make -k -j 36

Single file (list dependencies ahead of it if they changed):

    QUIET=1 ./gcp-rocq/run-on-gcp bash -lc "cd iris && opam exec --switch=/shared/xv6rocq -- coqc -R . xv6iris -R ../model-xv6iris Riscv -R ../kernel-rocq Kernel -R ../user-rocq User -w -notation-overridden FILE.v"

`opam exec --switch=…` is required — `coqc` is not on the VM's PATH. Local
`coqc` fails on stale `.vo`. **Rebase before any whole-tree rebuild.**

## 5. Two process lessons from the session that produced this

* **Never regex proof scripts on an unanchored pattern.** A `bslot <ident>` →
  `bslot` rule silently ate a `rewrite /bslot H3` tactic argument and two
  comment words. Anchor to the exact form (`bslots bn`, `bslot bn`).
* **Never compute match offsets on a snapshot you then mutate.** A
  parameter-dropping script did, and spliced six lemma headers into each other
  (`Lemma iu_slots` / `Lemma iu_slots_join  bslots a -∗ …`). Re-scan the
  mutated text each pass. Verify with a structural scan afterwards, not just
  the build: `Lemma <name>` followed immediately by another `Lemma` line is the
  signature.
