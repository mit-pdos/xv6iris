# Building on the GCP VM

The proofs compile on a shared Google Cloud VM instead of locally: a full clean
build of all 1092 `.v` files takes ~6 minutes there. The agent stays on your
machine and the VM does the compiling, so a Spot preemption costs you the
machine, never the agent — it just starts it again.

Two scripts in [`gcp-rocq/`](../gcp-rocq) do everything:

| | |
|---|---|
| `provision-gcp.sh` | build the VM from nothing. Idempotent, so it is also the repair tool. |
| `run-on-gcp` | run a command on the VM against a mirror of `$PWD`. What you use daily. |

`gcp-rocq/config.sh` holds every tunable; each value can be overridden from the
environment (`ROCQ_MACHINE_TYPE=c3d-standard-180 ./gcp-rocq/run-on-gcp …`).

## Daily use

**From a git WORKTREE** (agent lanes): the bare `run-on-gcp make` fails —
`xv6-riscv/` is gitignored, so a worktree has no clone and the remote `make`
tries to rebuild the ELF/fs.img. Use the explicit
`run-on-gcp make -C iris -f CoqMakefile -j180 -k` form (the tracked
`kernel-rocq/` sources are all the iris build needs); verify any re-dump the
remote performs is byte-identical (md5) before trusting it.


From any project directory:

```sh
./gcp-rocq/run-on-gcp make
```

That starts the VM if it is stopped, mirrors `$PWD` to the VM, runs `make`
there, streams the output back, and exits with the remote command's status.
No `SWITCH=` override: the VM carries a copy of `/shared/xv6rocq` at the same
path, so the Makefile's default is already right (see "Getting the .vo back"
for why that identity matters).

Useful flags:

```sh
run-on-gcp --shell            # interactive shell in the remote work tree
run-on-gcp --status           # instance state, address, how long it has been idle
run-on-gcp --start | --stop   # power it on or off by hand
run-on-gcp --sync-only        # push the tree, run nothing
run-on-gcp --no-sync <cmd>    # run against the tree as it already is remotely
run-on-gcp --pull doc/ <cmd>  # copy something back afterwards
run-on-gcp --where            # print the remote path for $PWD
```

Measured on `c3d-standard-90` (the original default, since replaced): initial
sync of the tree ~4.5s, clean build ~7m15s, a no-op `make` ~6s. A one-file
edit costs whatever its reverse dependency cone costs — touching
`iris/PrintkFmt.v` rebuilt its dependents in ~3m15s. The sync itself is never
the bottleneck, so there is no reason to avoid going through it.

**Machine type history.** `c3d-standard-90` was the default until a benchmark
comparing it against `c4-standard-192`, `c4d-standard-192`, and
`h4d-standard-192` (same clean build, same tree, `make clean` then timed
`make -k proofs`) found:

| machine type | vCPUs | clean build |
|---|---|---|
| c3d-standard-90 (old default) | 90 | 435s (7m15s) |
| c4-standard-192 | 192 | 425s (7m5s) |
| c4d-standard-192 | 192 | 340s (5m40s) |
| **h4d-standard-192 (current default)** | 192 | **314s (5m14s)** |

`h4d-standard-192` won on both speed and price (see the pricing note in
"Preemption and cost" below), so it is now the default — instance
`rocq-builder-v2` in `us-central1`, since `h4d-standard-192` is not offered in
`us-east4` where the original `rocq-builder` lived. `rocq-builder` /
`rocq-data` (the `c3d-standard-90` instance and its disk) were left in place
rather than deleted; `rocq-data-v2` is a clone of `rocq-data` taken at
migration time, so the opam switch and already-synced work trees carried over.

**NEVER RUN `make kernel-rocq` / `make user-rocq` (or plain `make`) ON THE VM.**
Their dump rules regenerate `kernel-rocq/*.v` and `user-rocq/*.v` from the
VM's OWN `xv6-riscv` ELF, which is not
necessarily the pinned revision — the rsync stamps the synced sources with the
VM's clock, but the ELF is older still, so make happily re-dumps and **clobbers
the tracked image the sync just pushed**. The failure surfaces later and
elsewhere, as `durable-notes.md`'s bogus-address error (`Unable to unify
"2147558360" with "2147558392"` in `ProcGeom.v`), and it reads like a broken
proof. Compile the SYNCED image instead:

```sh
touch kernel-rocq/*.v user-rocq/*.v   # make them newer than the VM's ELF
opam exec --switch=/shared/xv6rocq -- make -C model-xv6iris -f CoqMakefile -j192
opam exec --switch=/shared/xv6rocq -- make -C kernel-rocq   -f CoqMakefile -j192
opam exec --switch=/shared/xv6rocq -- make -C user-rocq     -f CoqMakefile -j192
opam exec --switch=/shared/xv6rocq -- make -C iris          -f CoqMakefile -j180 -k
```

It only bites after an upstream commit MOVES the image (a dump-tool or xv6
source change): before that the re-dump is byte-identical and invisible.

**Same trap in the assumption audit: use `make audit-only`, never `make
audit`.** `audit` depends on `proofs`, which depends on `kernel-rocq`, which is
the rule above. `audit-only` runs `coqc` on `iris/SystemAssumptions.v` against
the tree as it stands and touches no dump rule:

```sh
run-on-gcp --no-sync bash -c 'cd /mnt/rocq/trees/<tree> && make -s SWITCH=/shared/xv6rocq audit-only'
```

Budget ~6½ minutes for it (379 s, re-measured 2026-08-22; the 95 s this note
used to give is stale — the cone widened, not the tree). That is the command,
not the build — see claude-notes/optimization.md §"`Print Assumptions` is a
whole-tree walk", which also has the perf breakdown and the GC negative result.

**`user-rocq` is a THIRD compiled directory, and forgetting it does not look
like a missing step** — `iris/_CoqProject` maps `-R ../user-rocq User`, so the
symptom is a wall of `make[1]: *** No rule to make target
'../user-rocq/EchoData.vo', needed by 'UCodeEcho.vo'` with **no Rocq error
anywhere in the log**, and `make -k` then reports `Error 2` from the top rule
alone. It appeared the day the user-program dumps landed (`959f47cd`..
`519da425`); a build script written before that silently stops covering the
tree. Its `CoqMakefile` may also not exist yet on the VM, so generate it if
missing (`coq_makefile -f _CoqProject -o CoqMakefile`) — same for
`kernel-rocq`.

## Getting the .vo back for a local recheck

Rechecking one file locally normally means building the whole tree locally
first, just to have its dependencies' `.vo`. Instead, pull the VM's:

```sh
./gcp-rocq/run-on-gcp --pull-vo          # standalone
./gcp-rocq/run-on-gcp --pull-vo make     # build, then bring the artifacts back
```

That copies `.vo`/`.vos`/`.vok`/`.glob`/`.aux` and the `CoqMakefile` trio into
the local tree — precisely the files the push excludes, since the VM owns them.
All of it is gitignored, so the checkout stays clean. Then a single file
rechecks locally against them:

```sh
cd iris
opam exec --switch=/shared/xv6rocq -- coqc \
  -R . xv6iris -R ../model-xv6iris Riscv -R ../kernel-rocq Kernel -R ../user-rocq User \
  -w -notation-overridden ProofKexecB2.v
```

Measured: pulling all 1092 `.vo` takes ~15s, and rechecking `ProofKexecB2.v`
(85 `Require`s, deep in the tree) takes ~17s locally.

**This only works because the VM's switch is a byte-identical copy of the local
one.** A `.vo` records digests of every library it was built against, and two
opam builds of the same Rocq version are never byte-identical — they embed
build-specific data. Artifacts from an independently built switch are rejected:

```
Compiled library Riscv.rv64d_types makes inconsistent assumptions
over library Corelib.Init.Prelude
```

So `/shared/xv6rocq` on the VM is an rsync of `/shared/xv6rocq` from here, at
the *same absolute path* — which is also why the Makefile's default `SWITCH`
needs no override on either machine. The VM's `/shared` is bind-mounted off the
persistent disk, so it survives a rebuild. If you ever `opam install` into the
switch on one side, re-copy it to the other or pulled `.vo` will stop loading:

```sh
rsync -a --no-owner --no-group -e "ssh …" /shared/xv6rocq/_opam/ rocq@VM:/shared/xv6rocq/_opam/
```

(~1.7 GB, about 15s.) After re-copying, everything built against the old switch
must be rebuilt.

## What lives where

Each local directory gets its own remote work tree, named by flattening the
path (`/shared/xv6iris-7` → `/mnt/rocq/trees/_shared_xv6iris-7`), so several
agents working in different checkouts never collide. Each tree records where it
came from in `.source-path`.

```
/mnt/rocq/                     the 1TB persistent disk
├── opam/                      OPAMROOT, shared across every tree
├── shared/                    bind-mounted at /shared; holds xv6rocq/_opam,
│                              the byte-identical copy of the dev switch
│                              (Rocq 9.0.1, coq-iris 4.4.0, coq-sail-stdpp 0.20.1)
└── trees/_shared_xv6iris-7/   your work tree
```

The `default` switch in the opam root is a plain Rocq 9.2 and is **not** what
this project builds against — 9.2 does not even ship `coq_makefile`. The
Makefile's default `SWITCH=/shared/xv6rocq` resolves correctly on the VM, so
plain `make` is right; no override needed.

## Creating the VM

Needs a service-account key with `roles/compute.admin` and Compute Engine
enabled on the project:

```sh
gcloud auth activate-service-account --key-file=/shared/tmp/rocq-sa.json
./gcp-rocq/provision-gcp.sh
```

That creates the firewall rule, the 1 TB data disk, the Spot instance, the
idle-shutdown timer, and the shared opam switch. Every step checks before it
creates, so re-running is safe and cheap.

### Who can ssh in

`$SSH_KEY.pub` plus every key in `$EXTRA_AUTHORIZED_KEYS` (default
`~/.ssh/authorized_keys`) is authorized for `$SSH_USER`, so anyone who can
already reach this machine can also ssh straight to the VM and watch a build
the agent started. Re-running `provision-gcp.sh` is how a key change reaches
an EXISTING instance: `ssh-keys` metadata is written only at create time, and
`ensure_ssh_keys` re-writes it wholesale on every run. That makes removals work
too — a key dropped locally is revoked on the VM by the same step, and the
guest agent rewrites the VM's `authorized_keys` within seconds, with nothing to
restart.

Entries carrying **options** (`command="…" ssh-ed25519 …`, `restrict,…`) are
dropped rather than forwarded. The guest agent copies each metadata line into
`authorized_keys` verbatim, so an options prefix would carry a forced command
onto the VM under a key that reads as ordinary — and, the likelier mistake, a
`from="…"` restriction naming your local network would silently not apply
there. What is authorized on the VM is therefore always a bare key.

`provision-gcp.sh` does **not** create the project switch — that is specific to
this development. After provisioning:

```sh
./gcp-rocq/run-on-gcp --no-sync bash -c '
  export OPAMROOT=/mnt/rocq/opam OPAMYES=1
  opam switch create /mnt/rocq/switches/xv6rocq ocaml-base-compiler.4.14.2 -j $(nproc)
  opam install --switch=/mnt/rocq/switches/xv6rocq -j $(nproc) -y \
    coq.9.0.1 coq-iris.4.4.0 coq-sail-stdpp.0.20.1'
```

## Preemption and cost

The instance is Spot with `--instance-termination-action=STOP`, so a preemption
stops it rather than deleting it. Everything that matters — the opam switches,
every work tree, every `.vo` — lives on a separate persistent disk that is
never deleted with the instance, so recovery is just starting it again.
`run-on-gcp` does that automatically; you see a slow command, not a failure.
Verified: stop → restart takes ~15s with all state intact.

Rocq builds are incrementally resumable, so a preemption mid-build costs only
the file in flight — `make` picks up where it left off.

**BUT A BUILD DRIVEN THROUGH THE SSH PIPE LOSES ITS LOG WITH THE MACHINE, AND
THE LOG IS WHAT YOU WANTED.** `run-on-gcp make | tee build.log` streams through
`ssh`, so a preemption kills the pipe and the local log ends wherever the pipe
buffer last flushed — which is nowhere near where the build actually got to,
and reads like a stall rather than a preemption. Worse, the block buffering
means a *live* build also looks stalled for minutes at a time, so you cannot
tell the two apart. Run it detached ON THE VM, writing its own log and its own
sentinel, and poll that:

```sh
run-on-gcp --no-sync bash -c '
  cd /mnt/rocq/trees/<tree>
  setsid nohup bash -c "make -k proofs > /mnt/rocq/build.log 2>&1;
                        echo MAKEEXIT=\$? >> /mnt/rocq/build.log" \
    >/dev/null 2>&1 </dev/null &'
run-on-gcp --no-sync grep -c MAKEEXIT /mnt/rocq/build.log     # 1 = finished
```

The log then survives the preemption too, so the restart resumes against a log
you can still read.

**THE VM IS SHARED, so every whole-machine reading is somebody else's build as
much as yours.** `uptime`'s load, `pgrep -c rocqworker`, even `pgrep -x make`
count every tree at once — several `/mnt/rocq/trees/*` build concurrently. To
find YOUR build, ask for the working directory, which is the only thing that
distinguishes them (the command line does not — it is `make -k proofs` in all
of them):

```sh
for p in $(pgrep -x make); do echo "$p $(readlink /proc/$p/cwd)"; done
```

**TWO `make`s IN THE *SAME* REMOTE TREE RACE, AND THE ERROR LOOKS LIKE A
BROKEN SWITCH.** A parent agent and its subagent share one work tree (the
remote path is derived from `$PWD`, so it is the same tree), and two
concurrent `make`s there can catch each other mid-write: the loser dies with
*"Cannot find a physical path bound to logical path `<SomeModule>`"*, which
is character-for-character the failure `durable-notes.md` attributes to a
missing `eval $(opam env …)`. It is neither — the switch is fine and a plain
rerun is green. **Before chasing that message, check whether anything else
you launched is building in the same tree**; the `/proc/*/cwd` loop below
answers it. Serialise the builds, or give the subagent its own checkout.

**AND NEVER PATTERN-KILL ON THE VM.** `pkill -f "rocqworker --kind=compile"` to
stop your own build kills every *other* tree's workers in the same breath —
their `make` reports `Error 143` on whatever was in flight and their agent sees
a broken build with no cause. (This is `durable-notes.md`'s `pkill -f coqc`
trap one level up: there the pattern matched the killer's own shell, here it
matches the neighbours.) Kill the `make` you launched **by PID**, from the
`/proc/*/cwd` list above, and leave the workers to exit with it.

**Switching to on-demand when Spot capacity is thrashing.** Repeated
preemptions inside one build (each restart re-syncs, restarts the VM and
resumes, so a build can take several wall-clock multiples of its compile time)
are the signal. The instance must be **TERMINATED** for the change, and it
takes THREE flags, not one:

```sh
run-on-gcp --stop        # wait for TERMINATED; the change is rejected while RUNNING
gcloud compute instances set-scheduling rocq-builder-v2 --zone=us-central1-a \
  --no-preemptible --provisioning-model=STANDARD --clear-instance-termination-action
run-on-gcp --start
```

Each flag exists because of an error the previous one produces, and none of the
messages names the flag you actually need:

- `--provisioning-model=STANDARD` alone → *"For preemptible, only allowed
  provisioning_model value is SPOT"*. The instance carries the LEGACY
  `preemptible: true` field beside the modern `provisioningModel`, and both
  have to move; hence `--no-preemptible`.
- adding `--no-preemptible` → *"You cannot specify a termination action for a
  VM instance that has the standard provisioning model"*. `set-scheduling`
  re-sends the existing `instanceTerminationAction=STOP` as UNSPECIFIED rather
  than dropping it, and the API counts that as specifying it; hence
  `--clear-instance-termination-action`.

**The flag is on `set-scheduling`, not on `instances update`** — the latter has
no `--provisioning-model` at all in current gcloud. Going back is the same
command with `--preemptible --provisioning-model=SPOT
--instance-termination-action=STOP`.

Verify with:

```sh
gcloud compute instances describe rocq-builder-v2 --zone=us-central1-a \
  --format="value(scheduling.provisioningModel,scheduling.preemptible)"   # STANDARD  False
```

**The change survives the idle shutdown, and resets when the instance is
RECREATED.** Provisioning model is a property of the instance resource, not a
per-boot setting, so the 30-minute idle power-off and every later `--start` keep
it. But `config.sh` deliberately keeps `PROVISIONING_MODEL=SPOT` as the
default, so `provision-gcp.sh` — the documented way to change the machine or
boot image — brings a recreated instance back as Spot with no warning. Re-apply
`set-scheduling` after any recreate, or pass
`ROCQ_PROVISIONING_MODEL=STANDARD ROCQ_TERMINATION_ACTION=` for that one run.

On-demand `c3d-standard-90` is ~$4.30/hr against Spot's ~$1.68, so switch back
once capacity recovers — and note the idle-shutdown timer matters much more at
that rate.

The VM powers itself off after **30 minutes idle**, judged by live SSH sessions and
running `rocq`/`make`/`opam` processes, so a detached build keeps it alive on
its own. To pin it up (a long run you do not want interrupted):

```sh
run-on-gcp --no-sync touch /mnt/rocq/.keep-awake   # rm to release
```

Spot pricing is ~$1.68/hr for `c3d-standard-90` in `us-east4`, plus ~$110/mo
for the 1 TB disk, which is charged whether or not the instance is running.
Idle time costs far more than machine size does: leaving it up 24/7 is roughly
10× the cost of using it a few hours a day.

**On sizing:** the build peaks at ~119 concurrent workers but spends a narrow
head and about a minute of tail running 1–3 files wide, so 180 vCPU sat mostly
idle. Measured, 90 is ~19% slower on the `iris` phase (375s vs 315s) at half
the price — about 40% cheaper per build. Revisit only if several agents
routinely build at once.

## The VM is where a bump's reproducibility check is free

The push excludes `xv6-riscv/`, so a fresh work tree has none and the first
`make` clones it at `$(XV6_REV)` and builds the ELF itself. That makes the VM a
SECOND, independent build of the image from the same pin — run `make
dump-force` there and compare digests with the local tree:

```sh
run-on-gcp --no-sync bash -c 'make dump-force >/dev/null && md5sum kernel-rocq/Kernel*.v user-rocq/Sync*.v'
md5sum kernel-rocq/Kernel*.v user-rocq/Sync*.v
```

Six equal digests is the toolchain-match proof the playbook asks for, obtained
on a machine that shares nothing with yours but the pin.

**AND `--no-sync` IS FOR QUERYING THE VM, NEVER FOR DIAGNOSING YOUR OWN LATEST
EDIT.** A `--no-sync` build compiles whatever was last pushed, so after a local
`git reset` or an edit you have not synced it reports errors from a file you no
longer have — confidently, with line numbers that do not match your source. Two
ways this bites: a re-run of a failing build to "get more detail" reads the
stale copy and blames a lemma you already fixed; and a repin/re-dump diagnostic
run before syncing re-dumps with the OLD `tools/dump_elf.py`, so the digest
comparison disagrees for a reason that has nothing to do with the toolchain.
Sync first, then diagnose. Related: a build you did not FORCE is not evidence
either — `make` reporting "up to date" after a whole-tree sync is the mtime
artefact documented in `durable-notes.md`, so `rm` the `.vo` before timing or
trusting a single-file result.

**AND THE VM'S CLONE IS PINNED ONLY AT CREATION, SO IT GOES STALE ACROSS A
BUMP AND THEN SILENTLY CLOBBERS THE IMAGE YOU JUST SYNCED.** The VM clones
`xv6-riscv/` at `$(XV6_REV)` the first time a tree is built and never revisits
it, so a later bump leaves the remote clone on the OLD revision while the
remote `Makefile` (which IS synced) names the new one. That is dormant —
`make proofs`' dump rules stay quiet while the synced `kernel-rocq/*.v` are
newer than the stale ELF — until **anything makes the dump targets out of
date, and a change to `tools/dump_elf.py` does exactly that**: the rules fire,
re-dump from the OLD ELF, and overwrite the correct files the sync just
delivered. The build then fails hundreds of files deep with
`Unable to unify "<addr>" with "<addr>"` in `ProcGeom.v` / `ColdBoot.v` —
`durable-notes.md`'s standard bogus-address symptom, except that every LOCAL
check passes: `make xv6-rev-check`, a byte-identical local `make dump-force`,
and `make check-decode` are all green, because they all read the LOCAL tree.

The tell is one command, and it is worth running after any pull that touches
the dump tooling or the pin:

```sh
run-on-gcp --no-sync bash -c 'git -C xv6-riscv rev-parse HEAD; grep -oP "XV6_REV \?= \K\w+" Makefile'
```

Two lines that disagree is the bug. The fix is the same three steps as
locally, run remotely — `git -C xv6-riscv fetch && checkout --detach $REV`,
rebuild `kernel/kernel` **and** the user ELFs, `make dump-force` — after which
the digest comparison above is not merely a reproducibility check but the
proof that the remote image is the tracked one. **The remote build log is the
other tell**: `grep dump_elf.py` on it. A `make proofs` that prints dump lines
at all has rewritten your image, and on a correctly-pinned tree it prints
none.

**`git status` is not available to check this.** `SYNC_GIT=0`, so the remote
tree is not a git repository at all — `git status kernel-rocq/` there dies with
*"not a git repository (or any parent up to mount point /mnt)"*, which reads
like a broken tree and is only the sync policy. Compare digests, not
`git status`. The same reason makes any remote step that shells out to git
fail; do the git half locally.

**The VM's Ubuntu must match the dev container's.** Both are 26.04. This is not
cosmetic: 24.04 ships riscv64 gcc 13.3.0, 26.04 ships 15.2.0, and building the
kernel with the wrong one yields a different image whose dump differs from the
tracked `kernel-rocq/*.v` in every file — which breaks every proof naming a
symbol address, and the whole generated decode layer, with no obvious cause.
Verified: on 26.04 the dump reproduces byte for byte. If the container's Ubuntu
ever moves, change `BOOT_IMAGE_FAMILY` in `config.sh` and rebuild the instance
(the data disk survives), then confirm by re-dumping to a scratch path and
diffing against the tracked files.

**Build artifacts live only on the VM.** The sync excludes `.vo`/`.glob`/etc.
and honours `.gitignore`, which is also what protects them from `--delete` —
along with `xv6-riscv/` and `sail-riscv/`, which the VM clones and builds but
which do not exist locally. If you add a generated directory, make sure git
ignores it or the next sync will delete it.

**Incremental correctness comes from `--checksum --no-times`.** The sync decides
what to send by content, and transferred files land stamped with the VM's clock,
so an edit always comes out newer than its `.vo` and an untouched file stays
older. This is why a file whose mtime moves *backwards* (restore from backup,
`cp -p`, tar extract) still rebuilds correctly, and why clock skew between your
machine and the VM cannot cause a missed rebuild. `--no-checksum` is faster on
very large trees but gives that guarantee up; the wrapper warns when you use it.

**Rebuilding the instance is cheap; losing the data disk is not.** `rocq-data`
has `auto-delete=NO`, so deleting the instance costs only the boot disk. To
change the machine image, delete the instance and re-run `provision-gcp.sh` —
switches and trees come back attached. To change only the size, stop it and
`gcloud compute instances set-machine-type`, which keeps the boot disk too.
