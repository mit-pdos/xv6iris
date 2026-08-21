# forkret_park: the plan to retire the last assumed Link

> **STATUS 2026-08-21.** Steps A–D have landed: the park is PROVED again, as
> a functor over the real `SpecForkret.FORKRET` at `LinkForkret.Forkret`, so
> its cone carries no first-related axiom. What is left is Step E, and Step E
> is bigger than this file used to say — it is the syscall environment's
> missing producer, not two `iMod`s. Read §2 and Step E before touching
> anything; both record designs that were tried and do not type.

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

### Step E — the syscall environment's producer, and it is NOT "pay at two sites"

**THE OLD PLAN WAS WRONG ABOUT THIS STEP'S SIZE.** Writing Step D exposed a
second abstraction wall, and it is the one that actually blocks the Axiom.

`forkret_park_pkg (fun h => usertrap_res_bare) …`'s last conjunct is a wand
whose CONCLUSION is `usertrap_res_bare` — a `Parameter` of
`SpecUsertrap.USERTRAP_RES`, hence opaque to userinit and kfork.
`ForkretParkClose.forkret_park_pkg_intro` produces
`forkret_park_pkg (fun h => ut_res_bare Rsys) …`, which is not convertible
with the opaque one. So the callers cannot use the very lemma written for
them.

The concrete definition is `ProofUsertrap.v:1138`,
`usertrap_res_bare := ut_res_bare SY.syscall_env`, inside
`UsertrapProof … : USERTRAP` — sealed. Every re-export up the chain
(`ProofUserretClosed`, `ProofForkret`, `ProofForkretPark`) is
`Definition usertrap_res_bare := UC.usertrap_res_bare`, opaque all the way.

So Step E is two pieces:

#### E1 — a channel for the residue's SHAPE (small, but NOT in SpecUsertrap)

The channel is two names:

```coq
  Parameter usertrap_syscall_env :
    forall `{…} `{GEN : GenId},
      gname -> mword 64 -> bio_names -> fclose_names -> iProp Σ.
  Parameter usertrap_res_bare_eq :
    forall `{…} `{GEN : GenId} `{CID : CpuId} (pt : uptd) (ksp : mword 64),
      usertrap_res_bare pt ksp ⊣⊢ ut_res_bare usertrap_syscall_env pt ksp.
```

`ProofUsertrap` discharges the equation by `reflexivity` — it IS the
definition (`ProofUsertrap.v:1138`). Each re-export block (three of them)
gains two lines. The syscall ENVIRONMENT stays abstract; only the residue's
shape stops being, which was never the secret.

**CHECK THE DEPENDENCY DIRECTION BEFORE WRITING IT.** These do NOT go in
`SpecUsertrap.USERTRAP_RES`: `_CoqProject` has `SpecUsertrap.v` at 146 and
`UsertrapRes.v` at 147, and `UsertrapRes.v` requires `SpecUsertrap` (its
foot is `UtResFits <: USERTRAP_RES`, the fit check). So `SpecUsertrap`
cannot name `ut_res_bare` — nor `ut_names`, `ut_caps` or `park_own`, which
is the whole vocabulary such a parameter would need.

The home is a NEW module type at the foot of `UsertrapRes.v`, beside
`UtResFits`:

```coq
  Module Type USERTRAP_PARK.
    Include SpecUsertrap.USERTRAP.
    Parameter usertrap_syscall_env : … .
    Parameter usertrap_res_bare_eq : … .
  End USERTRAP_PARK.
```

and `ProofUsertrap` is ascribed to it instead of to `USERTRAP` (it already
requires `UsertrapRes`). Everything downstream that threads the residue
re-exports the two extra names the same way it re-exports the twelve.

#### E2 — a PRODUCER for the syscall environment (the real work)

Even with E1 the caller still owes
`first_done -∗ ut_caps N ∗ usertrap_syscall_env (un_f N) (un_pj N) (un_bn N) (un_fn N)`
and `usertrap_syscall_env` is abstract, so it must come from the module:

```coq
  (* SpecSyscall.SYSCALL *)
  Parameter syscall_env_intro : … -> <the persistent rows> -∗ first_done -∗
    syscall_env γf pj bn fn.
```

proved in `ProofSyscall.v` and threaded through `USERTRAP_RES` the same way.
**This is exactly the gap `LinkSyscall.v` already records** — "Establishing
the environment is the boot chain's job and is still owed", and
`ProofSyscall.v:975` says the same at the definition. It is not new debt;
Step D is what made it the *next* thing rather than a distant one.

Sizing it — `syscall_env γf pj bn fn` is four conjuncts:

| conjunct | producer |
|---|---|
| `sysc_proc_env γf` = nextpid `is_lock`, `procs_avail None`, `wait_lock`, `is_ftable`, `is_tickslock` | all persistent, all created by main before userinit runs |
| `ConsoleInv.console_ready` | persistent, main |
| `sysc_fs_env pj bn fn` = `⌜sysc_ties⌝ ∗ procs_inv ∗ disk_geom ∗ virtio_disk `is_lock` ∗ fs_ready` | `fs_ready` is `first_done`'s second half; `procs_inv` is a park premise already |
| `FirstTok.first_done` | the argument itself |

ONE WRINKLE, and `sysc_fs_env`'s own header anticipates it: `fs_ready`
QUANTIFIES the three disk ring pages (`∃ pd pav pu`, since R1 took them out
of `fscfg`), while `sysc_fs_env` names them at `fn`'s fields. A producer
that holds `fs_ready` "unpacks the existential and builds `fn` with `fcn_pd`
at the witness" — but the park fixes `N` (hence `un_fn N`, hence the pages)
BEFORE `fs_ready` exists, so it cannot choose the witness. The escape is
`FsReady.disk_geom_agree`, which identifies any two: the park supplies its
own `disk_geom` (persistent, from main's `virtio_disk_init`) and the
equation transports the lock. Mechanical, but it is a premise
`syscall_env_intro` must take.

#### E3 — then, and only then, the two call sites

`forkret_park` is invoked in exactly two places, both
`iMod (FP.forkret_park γs γf (proc_addr j) ks rest pid V Hrest with "Hks Hctx Hpriv Hfd Hirsp")`:

* `ProofUserinit.v:674` — the first process. Its comment block already calls
  itself "THE DEPOSIT SITE", and `Hbsl` (the three bslots) is in scope.
* `ProofKforkB5.v:204` — every process after. `Hbslp` is in scope. One
  caveat: `ut_caps` is persistent but UNPACKED here — its members arrive as
  separate premises (`#Htext`, `#Hpinv`, `#Hwl`, …), so reassembling the
  bundle is mechanical but not free.

Widen `SpecForkretPark.forkret_park_body` to carry the package (or switch
both callers to `FORKRET_PARK_PAID`), pay at those two `iMod`s, and replace
`LinkForkretPark.v`'s `Axiom` with an application of `ProofForkretPark`.

Do **userinit first** — it is the harder site (no `fs_ready` yet, which is
what this whole plan is about) and proves the design.

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
