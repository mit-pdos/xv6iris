# proofmode: represent hypothesis names as primitive strings

**Status: proposal + measurements + validated design. The patch itself is not
written yet** — see [What is still open](#what-is-still-open). Everything below
is reproducible with stock Iris 4.4 / Rocq 9.0 using
[`bench/`](bench/).

## Summary

`iris/proofmode/base.v` represents a proofmode hypothesis name as a Stdlib
string:

```coq
Inductive ident :=
  | IAnon : positive → ident
  | INamed :> string → ident.
```

A Stdlib `string` is a cons-list of `Ascii` applied to eight `bool`s, so a name
costs **12 term nodes per character**. That name is part of every `Esnoc`, and
every proofmode step's proof term mentions the whole environment. The result is
that in a long Iris proof **hypothesis names alone are about half of the proof
term** — and `Qed` cost is linear in proof-term size.

Rocq 9.0 ships `Corelib.Strings.PrimString`, whose literals are **one term node
regardless of length** and whose comparison is a kernel primitive. Changing
`INamed` to carry a primitive string removes that cost. Measured below: **−47 to
−52 % proof-term size and −29 to −42 % compile time** on a synthetic proofmode
benchmark, with no change to user-facing syntax and no loss of goal
readability.

## Why this matters: `Qed` is linear in proof-term size

Profiled with `rocq compile -profile` on a 17 s `Qed` in a large development
(921 files, ~440 kLoC of Iris proofs):

| phase | s | what it is |
|---|---|---|
| `HConstr.of_constr` | 6.57 | builds the sharing DAG — walks the whole TREE |
| `close_proof` (self) | 3.33 | incl. `global_vars_set` over the body — TREE |
| `Typeops.execute` | 3.18 | the only actual typechecking; DAG-linear |
| `interp-delayed-qed` (self) | 2.43 | plumbing |
| `sort_and_universes_of_constr` | 1.54 | vernac + kernel, twice — TREE |

Only about a sixth of `Qed` is typechecking. The rest is four full traversals of
the proof term, each `Constr.fold`-shaped with no memo, i.e. linear in the
number of *occurrences*. So term size is the lever, and anything that is
re-embedded per proof step is paid for hundreds of times.

(We checked the other way out first: memoising those kernel walks on physical
identity. We patched `kernel/hConstr.ml` and `Typeops.execute` in Rocq 9.0.1 and
measured 0.5–1.6 % hit rates — the tactic engine genuinely materialises the tree,
so there is no sharing for the kernel to exploit. Term size it is.)

## Measurement 1 — the representation itself

[`bench/repr.v`](bench/repr.v), read with `rocq compile -d hconstr`, which prints
each constant's proof-term tree size:

| name length | Stdlib `string` | `PrimString.string` |
|---:|---:|---:|
| 1 | 13 | **1** |
| 2 | 25 | **1** |
| 4 | 49 | **1** |
| 8 | 97 | **1** |
| 10 | 121 | **1** |
| 16 | 181 | **1** |
| 31 | 361 | **1** |

Exactly `12n + 1` versus `1`.

## Measurement 2 — end to end in the proofmode

[`bench/gen.py`](bench/gen.py) generates a self-contained proof (needs only
`iris.base_logic` + `iris.proofmode`) that holds **N** hypotheses in the spatial
context and then performs **M** proofmode steps which leave the context
unchanged (`iIntros "z"; iClear "z"`). Only the *length of the N hypothesis
names* varies between runs, so the delta is the `ident` representation and
nothing else.

The `anon` row introduces the same N hypotheses with `?` instead of a name, so
they become `IAnon p`. That is stock, unpatched Iris, and it is a **conservative
proxy for the proposed change**: `IAnon p` for p ≤ 60 costs a few nodes, a
primitive-string literal costs one — so the real patch lands at or slightly
below the `anon` row.

```
./bench/run.sh 40 200 4 8 12 16 anon
```

**N = 40 hypotheses, M = 200 steps**

| names | tree nodes | `bindings` (DAG) | wall s | peak RSS |
|---|---:|---:|---:|---:|
| length 4 | 2,080,509 | 1,652 | 4.86 | 644 MB |
| **length 8** | **2,889,789** | 1,812 | **5.97** | **703 MB** |
| length 12 | 3,699,069 | 1,972 | 7.21 | 761 MB |
| length 16 | 4,508,349 | 2,132 | 8.27 | 820 MB |
| **`anon` (≈ this proposal)** | **1,395,049** | 1,553 | **3.81** | **596 MB** |
| | **−51.7 %** | | **−36.2 %** | **−15.2 %** |

**Two more shapes, same conclusion**

| N, M | tree @ len 8 | tree @ `anon` | Δ | wall @ 8 | wall @ `anon` | Δ |
|---|---:|---:|---:|---:|---:|---:|
| 20, 100 | 738,569 | 356,819 | **−51.7 %** | 2.49 s | 1.77 s | **−28.9 %** |
| 40, 200 | 2,889,789 | 1,395,049 | **−51.7 %** | 5.97 s | 3.81 s | **−36.2 %** |
| 60, 400 | 9,320,609 | 4,941,609 | **−47.0 %** | 15.23 s | 8.82 s | **−42.1 %** |

The scaling is exactly what the model predicts: at N = 60, M = 400 each extra
character of name costs 598,680 nodes, i.e. **24.9 nodes per (name character ×
proof step)** = 12 nodes/char × ~2 embeddings of the environment per step (a
`tac_*` lemma names both the input and the output environment).

Note that `bindings` — the number of *distinct* subterms — barely moves. The
cost is pure duplication, which is exactly the shape `Qed`'s tree-linear walks
are worst at.

## Measurement 3 — corroboration on a real proof

In a 1,374-line whole-function WP proof (`ProofUservec` in
[mit-pdos/xv6iris](https://github.com/mit-pdos/xv6iris)), renaming 40 of its ~75
Iris hypotheses:

| names | proof-term tree |
|---|---:|
| 2–3 chars | 1,471,889 (**−10.0 %**) |
| 8.25 chars (as written) | 1,636,181 |
| 41 chars | 2,604,449 (**+59 %**) |

~730 nodes per character of hypothesis name in that proof. Since only 40 of ~75
names were touched, the whole-file ident cost there is roughly 20 %.

## The change

### 1. `iris/proofmode/base.v`

```coq
From Corelib Require Import PrimString.

Module Export ident.
Inductive ident :=
  | IAnon : positive → ident
  | INamed : PrimString.string → ident.     (* NOTE: no longer a coercion *)
End ident.

Definition pstring_beq (s1 s2 : PrimString.string) : bool :=
  match PrimString.compare s1 s2 with Eq => true | _ => false end.

Definition ident_beq (i1 i2 : ident) : bool :=
  match i1, i2 with
  | IAnon n1, IAnon n2 => positive_beq n1 n2
  | INamed s1, INamed s2 => pstring_beq s1 s2
  | _, _ => false
  end.
```

`pstring_beq_true : pstring_beq s1 s2 = true ↔ s1 = s2` follows from
`PrimStringAxioms.compare_spec` plus `of_to_list`; `EqDecision ident` follows
from that. `string_beq`/`ascii_beq` and their two lemmas can be deleted outright
— they exist only for `ident_beq`.

`ident_beq` gets *faster* as well as smaller: it becomes one kernel primitive
instead of a fixpoint over `lazy_andb` of eight booleans per character, and the
proofmode calls it on every `envs_lookup`.

### 2. The parsing bridge

Keep the whole parsing layer (`tokens.v`, `intro_patterns.v`,
`spec_patterns.v`, `sel_patterns.v`) on Stdlib `string` — user-facing syntax is
unchanged — and convert **only where an `ident` is constructed**:

```coq
Definition char63_of_ascii (a : ascii) : char63 :=
  Uint63.of_Z (Z.of_N (N_of_ascii a)).

Fixpoint ident_string (s : string) : PrimString.string :=
  match s with
  | EmptyString => PrimString.make 0 0
  | String a s' => PrimString.cat (PrimString.make 1 (char63_of_ascii a)) (ident_string s')
  end.
```

**This is the load-bearing design claim, and it is verified** in
[`bench/feas.v`](bench/feas.v): `eval vm_compute in (ident_string "…")` reduces
to a **1-node primitive-string literal** (`-d hconstr` reports `tree size = 1`
for a 31-character name), and three `eq_refl`s comparing the result against
`"…"%pstring` are accepted by the kernel. So the conversion never survives into
a proof term, and it is correct.

That matters because the construction sites already force reduction — e.g.
`ltac_tactics.v` has several `let Hs := eval vm_compute in (INamed <$> Hs)`.
Those become `eval vm_compute in ((INamed ∘ ident_string) <$> Hs)`. The Gallina
parsers that build idents inside `vm_compute`d functions (`spec_patterns.v`'s
`parse_goal … (INamed s :: hyps)`, `sel_patterns.v`'s `SelIdent ∘ INamed <$> s`)
just gain the composition.

### 3. Dropping the coercion

`INamed :> string` must go, because a coercion from Stdlib `string` would leave
`ident_string "H"` unreduced wherever reduction is not forced — strictly worse
than today. The affected sites are few (all of `INamed` is 16 occurrences across
five files):

- `base.v` — `maybe_INamed`
- `notation.v:12` — the display notation `Notation "Γ H : P" := (Esnoc Γ (INamed H) P%I)`; `H` becomes a `PrimString.string`, printed as `"H"%pstring`. If bare `"H"` is wanted in goal display, add a `Print`-only notation or open `pstring_scope` in the proofmode's display scope.
- `sel_patterns.v:37`, `spec_patterns.v:78-79` — insert `ident_string`
- `ltac_tactics.v:21, 1015, 1093, 1200, 1216, 1384, 1485, 1506, 1538, 1693` — the `lazymatch type of … with string => constr:(INamed …)` sites become `constr:(INamed (ident_string …))` under the existing `vm_compute`

### 4. Backwards compatibility for downstream developments

Source-level syntax (`iIntros "Hfoo"`, `iDestruct "H" as …`, spec and selection
patterns) is untouched, because those are Stdlib string literals consumed by the
parser. What breaks is code that constructs an `ident` *directly* from a Coq
string — e.g. `INamed "H"` written by hand, or a tactic that pattern-matches
`INamed ?s` and then treats `s` as a Stdlib string. A `Definition INamed_string
(s : string) : ident := INamed (ident_string s).` plus a deprecation alias
covers the first; the second needs the site updated (there are two in Iris
itself, `ltac_tactics.v:21` and `:1015`).

## What is still open

1. ~~`string_ident.v`.~~ **Checked: not affected.** `iIntros (%H)` goes through
   `IPure (IGallinaNamed s)`, and `gallina_ident` (`intro_patterns.v:5`) is a
   *separate* type carrying a Stdlib `string` that never becomes an `ident`.
   Since this design leaves the parsing layer on Stdlib strings,
   `string_ident.v` and the Ltac2 bridge are untouched.
2. **Minimum Rocq version.** `PrimString` is Rocq ≥ 9.0 (Coq 8.20 has it under
   `Coq.Strings.PrimString`). Supporting older versions means a compatibility
   shim selecting the representation, which would negate much of the simplicity;
   more likely this rides a version bump.
3. **The patch.** Not written. The measurements and the reduction/correctness
   feasibility above are what this document establishes; the mechanical edit is
   about 20 sites plus the two lemmas.

## Reproducing

```bash
cd bench
# representation cost
rocq compile -q -d hconstr repr.v
# the vm_compute bridge reduces to a literal and is kernel-checked correct
rocq compile -q -d hconstr feas.v
# end-to-end proofmode benchmark: N hypotheses, M steps, name length | anon
./run.sh 40 200 4 8 12 16 anon
./run.sh 20 100 4 8 12 anon
./run.sh 60 400 4 8 12 anon
```

`run.sh` prints `N M mode tree bindings wall_s peak_RSS_KB` per row; raw output
of the runs quoted above is in [`bench/raw-results.txt`](bench/raw-results.txt).
Measured on Rocq 9.0.1 / OCaml 4.14.2 (no flambda), coq-iris 4.4.0,
coq-stdpp 1.12.0.
