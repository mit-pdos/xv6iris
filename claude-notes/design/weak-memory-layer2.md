# Layer 2 — the transfer theorem, designed as a DIRECT acyclicity theorem (2026-08-18)

**Status: DESIGN (orchestrator).  Supersedes the "Ψ ⇒ main_premises′" framing
of [`weak-memory-deps.md`](weak-memory-deps.md) §4.2 and Track B of
[`weak-memory-premise-discharge.md`](weak-memory-premise-discharge.md).
D2/D3 (dependency tracking) are LANDED; A0/A0′ (relativized premises)
LANDED; the forward bank fixed (D-7).  This file says what Layer 2 must
prove, in what shape, and what remains a site fact.**

## 1. Why the per-edge premises are the wrong INTERFACE (even relativized)

`edges_split` (per cross-rf edge, every later fulfil), `edges_split_ms`
(A0: only milestone-source fulfils, coverage at the fulfil's EXT view) and
`ee_ok` are SUFFICIENT conditions for the milestone-measure walk
(`WeakRobustAcyc2`), stated per edge so as to carry no cycle quantifier.
But xv6 has harmless edges that violate ANY per-edge form:
- `holding()`'s plain lock read before the acquire RMW (A0 fixed that one:
  the RMW is the next fulfil and its own aq read covers).
- **The walker's A/D CAS traffic** (kernel page table shared by all harts;
  `WCexcl` messages by hart k's walker CAS, read by hart j's later walk):
  j's next milestone-source store `f` may be promised below `ts_CAS`
  (nothing in RVWMO orders an implicit walk read before a later
  unrelated store), so `ts_CAS < ts_f` fails — yet no cycle can pass
  through it (k's CAS is po-before k's own data access, so k cannot read
  `f` before its CAS).
The walk consumes edge facts ONLY for readers ON A CYCLE
(`WeakRobustMain.rf_edges_ok_on TS W`, `gdep2_acyclic_on` for any `W`
closed under mutual reachability).  So the honest Layer-1 interface is:

**Layer 2 proves `gdep2_acyclic TS` (and the other conclusions of the
premise package) DIRECTLY, by minimal-cycle analysis, and Layer 1 exposes
`robust_main` in a form that consumes those conclusions.**  The per-edge
premises stay as proven sufficient conditions (useful for litmus/small
programs), not as the theorem's hypothesis.

## 2. The Layer-1 interface to build (A0″, small)

- `on_cyc TS e := tc (gdep2 TS) e e` (closed under mutual reachability);
  `edges_split_cyc nh TS DS` := `edges_split_ms` restricted to readers
  `e2` with `on_cyc TS e2` — the weakest per-bundle form; prove
  `edges_split_ms → edges_split_cyc` and re-land `gdep2_acyclic_main` on
  it via `rf_edges_ok_on_ms` at `W := on_cyc` (`gdep2_acyclic_on` at that
  `W` gives "no cycle through an on-cycle event" = `gdep2_acyclic`).
- `robust_main_acyc`: `robust_main` with the graph obligations replaced by
  their CONCLUSIONS — `gdep2_acyclic TS` (or the pointwise
  `¬ tc gdep2 e e` the cone needs), `∀ a, co_tc TS a`, `dev_wit_ok`,
  and the bad-edge handling (`bad_wf` or, better, `no_bad_edge` derived
  from φ) — so that Layer 2 can discharge them one by one.  `robust_main`
  becomes a corollary (`main_premises ⇒ those conclusions`, all existing
  lemmas).

## 3. What Layer 2 proves, and from what

Given a canonical bundle `(TS, DS)` of a full behavior, `pf_violation_free_hart`
(φ, exported), an exported pf-state predicate Ψ (§5), and the machine.

**Theorem L2-acyc: `gdep2_acyclic TS`.**  By contradiction: take a cycle
of minimal length (finite graph — `WeakRobustMain`'s `gev_enum`).  Because
`gpo` is program order (transitive), a minimal cycle visits each agent in
ONE po-segment `[h_j .. f_j]`: `h_j` entered by a cross edge (rf from a
fulfil `v` at timestamp µ, or `gE`), `f_j` a fulfil that is the next
milestone's source.  The measure walk (`mile_mu`) closes if for every
segment `µ_entry < ts(f_j)` (S1).  Cases, per segment, in the FULL trace:
- **(C1) fence** `pr∧sw` between `h` and `f`: `disciplined` — trace fact,
  S1 by the machine.
- **(C2) aq entry** (`h` is an aq read / aq RMW): S1 by the machine.
- **(C3) dependent exit** — `f`'s EXT view includes a register/`vcap`
  chain from `h`'s result (`LRegW rd [DLdRes]` … `LCtrl`/`vsrc`/`asrc` at
  `f`): S1 by the machine (NEW lemma `fcov_of_dep_chain`, D2's rules).
  With D3 this covers every store control-dependent on a branch that
  depends on `h` (`while(started==0)`, `if(holding) panic`, every CS
  store after a lock spin), i.e. all of xv6's racy sites.
- **(C4) covered exit** — `j` acquired (aq read / read+fence, po-before
  `f`) a message `ts_a` above a release `ts_r` of `v`'s agent that is
  po-after `v` with a `pw∧sw` fence between (or an A2 chain): S1 by
  Track A1/A2 (`fcov_of_acquire_before`, `covered_of_release_chain`).
- **(C5)** the entry message is `bad` (owned, unpublished): the minimal
  bad edge's cone is pf-real and φ refutes it (`bad_edge_violates`,
  existing).
- **(C6) the residue**: none of the above.  §4 says what closes it.

**Theorem L2-co: `∀ a, co_tc TS a`** (write serialization): from
`ptraces_bytes_ok` as today (A4: RMW-only bytes; single-writer bytes;
handoff chains) — the byte classification is the one site fact that is a
genuine PROPERTY OF THE PROGRAM's memory layout, see §4.

**L2-dev: `dev_wit_ok`** — a `gdep2` path from a later fabric access to an
earlier one needs a backward-in-behavior-time rf edge (a promise read)
across a fabric access; C1–C4 at that segment give the same S1 inequality
and contradict the witness order (details to be worked out; the segment
structure is the same as L2-acyc's).

## 4. The residue (C6), and the pf-realness argument that shrinks it

At a minimal cycle, the strict ancestry `U` of the cycle is acyclic and
pf-replayable, so every segment head `h_j` has a pf-real PRE-state σ_h
(the pool holds `j`'s residual monad, so σ_h names the instruction).  Two
consequences that are THEOREMS about traces (to be mechanized as the core
of L2-acyc):
- **Lock-mediated reads cannot be cycle entries.**  If `h` is a plain read
  of byte `b` whose message `m` (author `i`) sits inside `i`'s critical
  section of lock word `L` (`ts_i(acq) < ts_m < ts_r(i)`, RMW-only lock
  word, so `excl_ok` totally orders the CS windows), and `j`'s read `h`
  sits inside `j`'s CS of `L` with `j`'s acquire pf-real, then `i`'s
  release is in `U`, hence `m` is in the pf log, hence `h` is NOT an early
  read and its rf edge cannot come from the cycle: the entry into `j`
  must be `j`'s ACQUIRE (aq, C2) or earlier.  If `j`'s CS is BEFORE `i`'s
  in gmo, `h` reading `m` early contradicts the release fence between `h`
  and `j`'s release (EXT).  So for lock-protected bytes, C1–C5 are
  exhaustive PROVIDED the two site facts hold: **(SF-1)** `m` was written
  inside its author's CS of `L` and `h` read inside the reader's CS of the
  SAME `L`.
- **Sync bytes** (lock words, `started`/`first`, the disk's used index,
  PTE A/D bits): entries are aq RMWs (C2), or plain reads followed by a
  dependent branch/fence (C1/C3), or walker reads whose later stores are
  never on a cycle through the CAS (the A/D structural fact — to be
  proved: k's CAS precedes k's data access in po).
- **Private bytes** (single-agent): no cross edges.
So the residue is exactly the ownership discipline of the byte: **(SF-1)
lock protection per edge, (SF-2) the sync-byte discipline per site, (SF-3)
the byte classification** — the same three facts the M6 design called
"Layer 2 site facts".  They are NOT machine-visible.

## 5. Ψ — what the pf side can export, and how it supplies SF-1/2/3

Ψ is exported at every pf-reachable state, like φ, from `weak_state_interp`.
What is expressible without ghost history: (i) the READ WATERMARK
`w_rdw` (inert `wstate` field: max ts of plain foreign reads since the
last `pr∧sw` fence) with the invariant "no fulfil with EXT view <
`w_rdw`" — this is S1 as a pf-state invariant and covers C1/C3-shaped
sites; (ii) a per-hart "in CS of lock word `L`" inert component
`w_lock : option Z` set by an aq RMW on `L` (the acquire) and cleared by
the release store to `L` — MACHINE-computable (the RMW's byte address is
in the label), and gives "j's read/store of b happened while j held L"
as a trace fact; (iii) SF-1 then needs "b is protected by L", which is
NOT machine-computable — the honest options: (α) an explicit per-image
side condition (a byte→lock map for the kernel's shared data, checked
against the WP proof's lock ownership — D-M6-8's decision), or (β) a
GHOST byte→lock map in the state interpretation whose evolution is tied
to the release/acquire leaves and exported per state, plus a
monotonicity lemma making the per-state exports coherent along a trace.
⚑ **Decision for the user**: (α) now, (β) as the upgrade — or (β)
directly.  Everything else in §3–4 is machine work.

## 6. Staging

- **A0″** (Layer 1, small): `on_cyc`, `edges_split_cyc`, `robust_main_acyc`.
- **L2-M1** (Layer 1, machine facts): `fcov_of_dep_chain` (C3),
  `S1_of_fence`/`S1_of_aq` restated for the segment shape, the CS-window
  lemma (mutual exclusion from `excl_ok` on an RMW-only lock word), the
  "lock-mediated read is not an early read" structural lemma over
  `U`-pf-realness (uses the exhibit's replay of `U`), the A/D CAS
  structural fact.
- **L2-M2**: the minimal-cycle skeleton (`gev_enum`, minimal length,
  one-segment-per-agent via `gpo` transitivity), the case split, L2-acyc
  under SF-1/2/3 as explicit hypotheses.
- **L2-M3**: `w_rdw`/`w_lock` in the machine + the export; SF-2 from the
  export; L2-co from `bytes_ok`; L2-dev.
- **L2-M4**: SF-1/SF-3 by (α) or (β) per the decision.
