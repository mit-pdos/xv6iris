# The toolchain: `opam/xv6rocq.export`

`xv6rocq.export` is the **only** description of the Rocq toolchain this tree builds with. It is a
full, frozen opam switch export (`opam switch export --full --freeze`): every package of the switch
with its exact version, its embedded package definition and its source pinned to a commit or a
release tarball, so importing it needs no extra opam repository (not even iris-dev for the Iris
and stdpp development versions) and reproduces the switch exactly — re-exporting the result is
byte-identical to this file (checked on three independent builds, 2026-09-26/27).

CI imports it (`.github/workflows/*.yml`), the agent container's default switch is built from it
(`/shared/xv6rocq`), and the shared development switch should be too. **Changing the toolchain
means changing this file** (build the new switch, export it, replace the file, rebuild every tree)
— never `opam install`/`upgrade` into the shared switch.

## What is in it (the packages that matter)

| Package | Version | Source |
|---|---|---|
| ocaml-base-compiler | 5.3.0 | opam default repository |
| coq / rocq-prover | 9.0.1 / 9.0.0 (`coq` is the compatibility package; the binaries are `rocq` and `coqc`) | rocq-released |
| rocq-stdpp, rocq-stdpp-bitvector | dev.2026-09-17.0.d510b616 (stdpp master) | git rocq-iris/stdpp @ `d510b616` |
| rocq-iris | dev.2026-09-24.0.8e490959 (Iris master) | git rocq-iris/iris @ `8e4909593a` |
| rocq-elpi, elpi | 3.5.1, 3.7.3 (Iris master needs rocq-elpi) | release tarballs |
| rocq-sail-stdpp | 0.20.3 | git rems-project/coq-sail @ `e7b914cd` |
| coq-lsp | 0.2.5+9.0 (`pet`, `fcc`: editor and agent tooling; harmless if unused) | release tarball |

91 packages in all; the rest are their OCaml dependencies. Linux only as exported
(`conf-linux-libc-dev` is in the list). Not included, on purpose: the Sail compiler (only
`make model-gen` needs it, in its own switch — README "Regenerating the Sail model") and z3.

## Installing it (a new machine, or moving a shared switch to a new toolchain)

Always a **fresh switch**, never an in-place upgrade — a `.vo` records the digests of the
libraries it was built against, and every tree built against the old switch must be rebuilt from
clean anyway. About 10 minutes at `jobs=6`, network access to GitHub and opam.ocaml.org, system
packages `m4 pkg-config libgmp-dev` (what `conf-gmp` and friends check for).

```sh
# 1. the switch, at the path the Makefile and notes expect (any path works: pass SWITCH=... to make)
opam switch create /shared/xv6rocq ocaml-base-compiler.5.3.0 \
     --repos default,rocq-released=https://rocq-prover.org/opam/released
opam switch import --switch /shared/xv6rocq opam/xv6rocq.export

# 2. check it is exactly this file
make toolchain-check            # or: tools/toolchain_check.sh /shared/xv6rocq

# 3. rebuild every tree from clean (old .vo are rejected: "inconsistent assumptions")
for d in model-xv6iris kernel-rocq user-rocq iris; do (cd $d && make -f CoqMakefile cleanall); done
make
```

Replacing a shared switch that other machines copy (the GCP builder rsyncs `/shared/xv6rocq` at
the same absolute path, see `claude-notes/remote-build-gcp.md`): build the new switch beside the
old one (`/shared/xv6rocq-new`), run `tools/toolchain_check.sh /shared/xv6rocq-new`, then swap the
directories, re-copy to the other machines, and clean-rebuild everywhere. Keep the old directory
until the new tree is green.

## Changing it

1. Build the candidate switch somewhere else (in the agent container: `/work/opam/<name>`), get the
   tree green against it, run the audits.
2. `opam switch export --full --freeze --switch <name> opam/xv6rocq.export`, commit it with the
   proof changes it required. The integrity gate treats this file as a trust file: a commit to
   `main` that changes it needs the owner's `INTEGRITY_ALLOW=<fingerprint>`.
3. CI's cache key is the hash of this file, so the next run rebuilds its switch (~15 min, once per
   runner). The container image (`~/agents/Dockerfile`) is rebuilt from it; shared switches on
   other machines follow the recipe above.
4. Say so in the commit message and in `claude-notes/durable-notes.md` ("Build"): the git history
   of this file is the toolchain changelog.

## History

- 2026-09-26: Rocq 9.0.1 kept; coq-iris 4.4.0 → rocq-iris master `8e490959`; coq-stdpp 1.12.0 →
  rocq-stdpp master `d510b616`; coq-sail-stdpp 0.20.1 → rocq-sail-stdpp 0.20.3; rocq-elpi added
  (Iris master); coq-lsp added; `.github/coq-deps.txt` replaced by this file. The reason: the
  liveness work needs Transfinite Iris on top of Iris master. The proof changes it required are
  mechanical (renames, imports, explicit instances, `clear`s, tactic-script adjustments; the
  generated model regenerated with Sail 0.20.3); the three `Print Assumptions` audits are unchanged.
