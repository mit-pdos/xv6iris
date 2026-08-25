# Sweeping a new AMBIENT INTERFACE AXIS across the tree

How to add a new typeclass-indexed parameter — an *interface axis* — to
every WP statement in `iris/`, mechanically. The tree has now done this
three times: `CpuId` (the explicit-hart sweep,
[`completed/explicit-cpuid.md`](completed/explicit-cpuid.md)), `CurKtier`
(the sp-migration tier), and `CurCtx` (the TSO port's thread-of-control
context, [`projects/tso-port.md`](projects/tso-port.md)). The three ran
into the SAME classes and the SAME traps, so this file is the recipe
rather than a fourth rediscovery.

**The tool is [`tools/ctx_convert.py`](../tools/ctx_convert.py)** — named
for the context sweep but written to be re-pointed: the axis name, the
class name and the blacklist are constants at the top. Modes: `binders`
(add the ambient binder), `caps` (repair a resource-bundle destructure).
Both take `--apply`; without it they print a scoreboard and change
nothing.

**Scale, measured on the `CurCtx` sweep (1321 `.v` files):** ~2900
scripted edits over ~600 files; six repair classes, all scriptable once
seen; five decisions that genuinely needed a human; four bugs in the
sweep tool itself. About twenty build rounds. The tool did the bulk; the
thinking was concentrated in the five seams and in getting the tool's
rules right.

## 0. Before you start: is the axis ambient or explicit?

An AMBIENT axis (`Context `{XI : CurCtx}`) leaves every spec statement's
text unchanged and is what makes a sweep cheap. It works only if the
value does not change under the code being specified. If it DOES change
mid-proof, it belongs in a resource, not in an ambient binder — put it
inside an existing ambient bundle instead (for `CurCtx`, `IntrDefs.sie_cap`)
so no proof has to thread a new separation-logic resource by hand.

**Give the class no default instance** if its inhabitant is exclusive:
a global default would be one ghost shared by every thread. The cost is
that a vacuous occurrence cannot be resolved — see the phantom trap below.

## 1. The procedure, in order

1. **Land the definitions first** (the class, the resource, its laws),
   compiling standalone. Nothing else can proceed until this is green.
2. **Fold the resource into the ambient bundle** by hand, at the level
   that minimizes fallout. For `CurCtx` that was `sie_cap` — one level
   BELOW `sie_cap_gpr` — so that the 20 `rewrite /sie_cap_gpr` sites,
   the ~55 four-tuple destructs, and `sie_cap_gpr_split`/`_join`/
   `IntoSep`/`FromSep` all kept their shape and only capability OPENERS
   saw the change. **Choose this level deliberately; it decides the size
   of the whole sweep.**
3. **Run `binders --apply` to a FIXPOINT** (see the two-pass trap), then
   sync and do a full build.
4. **Harvest.** Each round, classify the errors, fix the RULE not the
   file where the class is mechanical, and re-run. Expect the error
   count to spike when a bottom-of-tree file goes green and a whole cone
   opens at once — a spike is progress, not regression. Count DISTINCT
   CAUSES, not errors: one contract mismatch cascades into every
   subsequent goal in its proof, so 42 errors routinely meant one cause.
5. **Delegate the tail.** When the failures stop being uniform — when
   each file threads the bundle differently — the sweep is over and it
   is per-file work. Hand it to agents in batches with the class
   catalogue and the standing principle, and tell them to STOP and
   report rather than invent if a file needs a design call.

## 2. The six repair classes

1. **Bundle destructure.** An opener whose trailing name absorbed the
   remainder now fails: `(A & B & C & #D & #E)` must bind the new
   conjunct. Symptom is always the same error (for a non-persistent
   conjunct, `iIntuitionistic: … not persistent`). Scriptable — `caps`
   mode does it, anchored on the FULL slot shape so a shorter opener,
   which is a different resource, is left alone.
2. **Re-assembly.** Every rebuild (`rewrite /R` + `iFrame`) needs the new
   conjunct in its framing list, AND its enclosing hand-over list
   (`iSplitL "…"`, `iAssert … with "[…]"`) needs it too. **Always fix
   both halves**: the destructure alone compiles while dropping the
   resource.
3. **Threading.** Bound at the open, "not found" at the rebuild. The
   culprit is almost never a destruct arity — it is an intervening
   `iApply … with "[explicit list]"` that did not carry it, with `[-]`
   sweeping it into the sibling goal. Add it to the list, and to the
   ad-hoc bundle TYPE that list feeds.
4. **Bundle-residue definitions.** A definition naming "everything in
   the bundle except X" must carry the new conjunct, and its producers
   and consumers with it. These hide in two places: named definitions,
   and ANONYMOUS `W`-bundles spelled inline in a proof term.
5. **Explicit quantifiers.** A statement that binds the OLD axis by hand
   rather than through its section needs the new one beside it, and
   every positional application gains a slot. Four shapes, all seen:
   `Prop`-carried callee contracts, Module Type `Parameter`s,
   function-valued arguments (`URB : CpuId → … → iProp`), and
   `Definition`s whose old-axis binder sits in the BODY rather than the
   binder list.
6. **Fixpoint/contract genericity.** A contract served to *whichever*
   client traps must quantify the axis in its `□`-prefix; producers then
   gain a leading `iIntros` binder and consumers specialize at the
   ambient value.

## 3. Traps that COMPILE (the dangerous ones)

- **A trailing wildcard in a destructure is a silent leak.**
  `iDestruct "H" as "(A & B & _)"` swallows the new conjunct and the
  file compiles; the consuming direction fails loudly later, but the
  producing direction just drops the resource into the affine void.
  Grep every opener for a trailing `_`. **One benign shape to waive:**
  a wildcard inside `iAssert (⌜…⌝)%I as %H` (pure extraction) restores
  the context afterwards and drops nothing.
- **An implicit argument left to typeclass resolution picks the
  most-recently-introduced instance** — which, inside a statement that
  quantifies its OWN, is not the one it means. Rule: **wherever a
  statement quantifies its own instance, every application inside it
  must NAME it.** Audit only files with TWO instances in scope; the
  naive grep (applications lacking an explicit `:=`) returns ~1000 sites
  and almost all are correct.
- **A vacuous inline binder is a PHANTOM.** A section variable is
  self-cleaning — Rocq generalizes it only where used — but an inline
  binder is always in the signature, so on a statement that never
  mentions the axis it becomes an argument nothing can infer, and the
  consumer fails at `Qed` with an unresolved evar, far from the cause.
  **Prefer section binders to inline ones for exactly this reason.**
  The end state for a genuinely vacuous occurrence is to DROP the
  binder, not to have callers invent a witness. Do not hunt these by
  grepping for absent vocabulary — a statement that merely NAMES a
  dependent body does not spell it, so the scan is mostly false
  positives; the compiler's unresolved-evar-at-`Qed` is the detector.
- **A binder inside a `fun` is silently demoted.** A lambda cannot carry
  an implicit binder, so the sweep's edit there becomes a POSITIONAL
  argument (Rocq warns, does not error). Never fix it by deleting the
  binder: the lambda has a partner `Hypothesis`/`Parameter` that must
  gain the matching quantifier.
- **Binder POSITION is load-bearing across a module-type boundary.**
  Section variables are prepended, so a `Parameter` at
  `∀ {A} {B} {NEW}` does not match an implementation inheriting `NEW`
  from its section (`∀ {NEW} {A} {B}`); subtyping breaks with no clue at
  the definition site. Implementation and Parameter must move together.

## 4. Rules for the sweep tool itself

Every tooling bug in the `CurCtx` sweep was **a rule reasoning at the
wrong granularity**, and each one was caught by the same discipline:

- **Anchor a rewrite to a SYNTACTIC POSITION** (declaration line, binder
  slot), never to a token that can appear anywhere. A raw
  `(CID0 : CPU)` rule fired inside `(CID1 : CPU) = (CID0 : CPU)` in 27
  places across 12 files, and the build hid all but one behind the
  first.
- **Prefer the rule that UNDER-fires.** A miss is a compile error next
  round; a corruption silently rewrites a theorem statement.
- **Be idempotent, and check for a DRY-RUN FIXPOINT after every apply.**
  Some rules need two passes because their own edit changes their
  precondition (whether a file has a section binder is decided before
  section binders are added). A dry run printing nothing is the signal
  the tree is stable.
- **Insert after a COMPLETE statement**, not after a matching line: a
  multi-line `Require Import A B\n C.` breaks if you insert between its
  lines, and the error (`Cannot find a physical path bound to logical
  path Require`) reads like a missing library. Strip trailing comments
  before deciding a statement ended, and never move a line whose
  trailing comment continues onto the next.
- **Scope by SECTION, not by file.** "This file has a section binding
  the axis" does not mean "this declaration is inside it": a top-level
  declaration in such a file still needs its own binder, while an inline
  one inside the section shadows and is rejected.
- **Match the old axis by SHAPE, not by name.** Binders appear as
  `CID`, `CID0`, `CIDa`/`CIDb` (hart-shift lemmas), `CIDx`, `CIDq`, …
  and a declaration may bind SEVERAL. Insert the new binder ONCE, after
  the last of them.
- **Blacklist two populations**: files BELOW the new definitions in the
  import order (a cycle), and files that are indexed by the old axis but
  genuinely independent of the new one (`HartTp.v` is register-file
  code; `WpNext.v` must stay transparent because the design point is
  that the axis does NOT change across it).

## 5. What still needs a human

The decisions the script cannot make are the ones asking **"whose is
this resource?"** For `CurCtx` they were five, and every one turned out
to be an instance of a single principle, which is what to look for
first:

> A resource describing THIS client carries the ambient value; a
> resource describing ANOTHER (parked, or not yet created) carries that
> client's value INTERNALLY — existentially in a record, or
> ∀-quantified in a wand its resumer applies.

Under that principle: a trap handler is ∀-quantified (it serves
whichever client traps); a parked scheduler context is existential (a
FOREIGN client resumes it, so its identity must be internal, which also
means no consumer's arity changes); a user-excursion residue is ambient
(nothing but this client can resume it); a child's package is
∀-quantified beside the hart it already quantifies, for the same reason.
Get the principle stated early — it then decides a dozen mechanical
questions that would otherwise each be a judgement call.

**Two consequences worth planning for.** A resource with a lifecycle
needs its birth, transfer and death sites identified up front (for
`CurCtx`: born per hart at the adequacy layer that first has per-client
identity, born again per child at the fork park, transferred at the
context switch, dropped at a zombie park). And a type existentially
bound inside a `▷`-guarded record **needs `Inhabited`** — `bi.later_exist`
holds only over an inhabited domain, so without it the resumer cannot
open the record it is about to run.
