# Using `rocq-warm` on this tree

A big `iris/` file costs one to three minutes to `coqc`, and fixing one tactic
in it costs that again for every attempt. [`rocq-warm`](https://github.com/zeldovich/rocq-warm)
keeps a `rocq repl` alive with the file already executed, so an edit
re-executes only from the edit onwards. It reports diagnostics in `coqc`'s
exact format and returns `coqc`'s exit code.

**This file is about using it here.** The tool's own design — how it drives the
REPL, why the look-ahead window is sized the way it is, what the message
anchors are relative to — lives beside the code in that repo, not here.

## Getting it

It is not vendored in this tree and nothing installs it. Clone it once and put
the entry point on your `PATH`:

```sh
git clone https://github.com/zeldovich/rocq-warm ~/src/rocq-warm
ln -s ~/src/rocq-warm/rocq-warm ~/bin/rocq-warm     # symlinking is supported
```

Pure Python 3, no dependencies, and nothing to add to the opam switch — which
matters here, because `/shared/xv6rocq` has to stay byte-identical with the
build VM's copy (see [`remote-build-gcp.md`](remote-build-gcp.md)).

## Using it

**The switch must be active in the shell you invoke from**, as for any raw
`coqc`:

```sh
eval $(opam env --switch=/shared/xv6rocq)
rocq-warm check iris/ProofIput.v
```

The session runs the `rocq` *that shell* resolved, and a call from a different
switch cold-starts rather than answering from the old one — so the usual
`eval $(opam env …)` discipline is enough, and forgetting it fails loudly
instead of silently.

Load path and flags come from `iris/_CoqProject`, so there is nothing to
configure. The daemon is per-checkout (rooted at the git worktree), so
`rocq-warm status` and `stop` find it from anywhere in the tree.

## What it does NOT do

**It writes no `.vo`.** `make` stays the source of truth; `rocq-warm` is for
the edit loop only. `rocq-warm check F.v --compile` runs a real `coqc`
afterwards when you want both.

It runs under `Set Silent`, so it reports errors and warnings but not what the
proof itself prints — no `Time` output, no `Print Assumptions`. Use
`--show-output` when you want those, or just run `coqc`.

## Several agents on the build VM at once

The daemon is **per checkout**, rooted at the git worktree, so agents in
separate trees share nothing: separate sockets under their own `.rocq-warm/`,
separate sessions, and one agent's `rocq-warm stop` leaves the others alone.
Nothing in the tool pattern-kills — the stray reaper matches cmdline as well as
pid precisely so a neighbour's sessions are never in scope. This is the
opposite of the `pkill -f rocqworker` trap in
[`remote-build-gcp.md`](remote-build-gcp.md), and deliberately so.

What does not isolate itself is memory, and this tree's proofs are not small: a
session costs roughly **twice what `coqc` peaks at**, so `ProofCreate.v` sits
at 9.0 GB warm and `ProofNamex.v` at 8.9 GB. Each daemon caps its own sessions
at 32 GB and yields its least-recently-used session — its last one if need be —
whenever the machine's `MemAvailable` drops below ~5% of RAM. That floor is
what actually bounds ten agents, because it is the only signal that moves when
the pressure is somebody else's `make -j180`.

Concurrent invocations are safe in both directions: several checks racing in
one tree end up sharing a single daemon (startup is locked), and checks of the
same file serialise rather than interleaving.

`rocq-warm status` prints both its own footprint and how close the machine is
to the floor. If you want a smaller share than the default:

```sh
export ROCQ_WARM_MAX_RSS_GB=16        # this agent's sessions, together
export ROCQ_WARM_MIN_FREE_GB=64       # leave more room for everyone else
```

Sessions also expire after 30 minutes idle, and the daemon exits once it holds
nothing, so an agent that wanders off does not keep memory resident.

## It invalidates itself, but know when

A session is thrown away when `iris/_CoqProject` changes or when any `.vo` in
the file's `rocq dep` closure is rebuilt — so a `make proofs` underneath it is
safe, at the cost of a cold start on the next check. Editing the `Require`
header also forces a cold start.

## Checking it still agrees with `coqc` here

`tests/rocq_warm_corpus.py` in the tool's repo replays a scripted edit sequence
against a real `coqc`, once per version. Point it at `iris/`:

```sh
./gcp-rocq/run-on-gcp opam exec --switch=/shared/xv6rocq -- \
  python3 -u ~/src/rocq-warm/tests/rocq_warm_corpus.py \
    --dir iris --sample 8 --spread 24 --jobs 6 --rss-limit-gb 24 --keep-going
```

Those are minutes-long compiles — **run it on the VM**, not here. Two things
about this tree will otherwise look like tool bugs and are not:

- **`iris/` holds files that are deliberately not in `_CoqProject`** and do not
  compile standalone (they need `UCodeShP`, `UkShRun`, …). The runner samples
  only what `_CoqProject` lists, and reports the reason when you name one
  explicitly.
- **A neighbour's `pkill -f rocqworker` kills every checkout's workers**, the
  same trap [`remote-build-gcp.md`](remote-build-gcp.md) records as `Error 143`.
  It hits both the session and the reference `coqc`; the runner names the signal
  and retries rather than calling it a disagreement.

## What it is worth here

Measured on this tree, agreeing with `coqc` at every step on 18 medium proofs
and 32 larger ones:

| | `coqc` | `rocq-warm` |
|---|---|---|
| `ProofCreate.v` (6475 sentences), break a tactic at 85% | 98 s | **5.5 s** |
| the same, fixed and re-checked | 131 s | **32 s** |
| `FsImgCheck.v`, fixed and re-checked | 180 s | **1.5 s** |
| `ProofIput.v`, edit at 80% | 102 s | **25 s** |
| any file, comment-only edit | full rebuild | **executes nothing** |

The first check of a file costs a full `coqc`; the win is every check after it.
