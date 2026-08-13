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

Measured on `c3d-standard-90`: initial sync of the tree ~4.5s, clean build
~7m15s, a no-op `make` ~6s. A one-file edit costs whatever its reverse
dependency cone costs — touching `iris/PrintkFmt.v` rebuilt its dependents in
~3m15s. The sync itself is never the bottleneck, so there is no reason to
avoid going through it.

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

The VM powers itself off after **1 hour idle**, judged by live SSH sessions and
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

## Things that will bite you

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
