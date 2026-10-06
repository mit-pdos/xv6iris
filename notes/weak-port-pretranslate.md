# Weak port: the pre-translator draft (`tools/weak_rocq2lean.py`)

*Section to append to `notes/weak-port-protocol.md`.  Written 2026-10-06, measured against the ports in the tree on that date.*

## Workers: start from the draft

Before writing anything by hand for an assigned file `<Name>`, generate the draft:

    tools/weak_rocq2lean.py <Name> -o Weak/<Name>.lean            # whole file
    tools/weak_rocq2lean.py <Name> --rocq-comments -o /tmp/x.lean # each tactic followed by its Rocq line
    tools/weak_rocq2lean.py --names <Name>                        # just the name map (Rocq<TAB>Lean)

The script runs locally in about 5 s and never builds anything.  Nothing in it is ever committed as it comes out: `sorry` and the draft notes must all be gone before you report.

**What the draft gives you, and how far to trust it** (see "Measured" below):

* **Header skeleton.**  It has the Rocq path, the Rocq header comment (rewrite it to "in substance"), Deviation 1 with the file-qualified dup names already listed, the full **name map**, and `DRAFT NOTES`.  The notes list the translator's guesses (`XLAT?:`), the names it could not find in the Lean tree, and the top-level items it skipped (Ltac, Hint, most Notations, non-`Decision`/`Reflexive`/`Transitive` Instances).  Delete the `DRAFT NOTES` block once you have dealt with each entry.
* **Imports.**  Rocq weak imports become `Weak.<Dep>`; a dep that is not ported yet shows up as a `-- Weak.<Dep> -- NOT PORTED` line, and then you STOP and report, as the protocol says.  An extra import tagged `-- XLAT: a resolved name lives here` means a name you use lives in a Lean file that your Rocq imports do not reach (for example `execNil` in `WeakAxiomatic2`).  The three `Batteries.Tactic.*` imports are there for the drafted tactics (`<;> [..]`, `on_goal`, `pick_goal`, `eapply`).  Drop any you end up not using.
* **Names.**  Names come from a global table.  It is built from every ported `Weak/*.lean` (its declarations, its structure fields and constructors, and the pairs in its header name map), every `MachCSL`/`Xv6` declaration, and the Rocq sources of the dependencies.  Fields become `Struct.field`, constructors `Type.Ctor`, record constructors `Type.mk`, and dup names `<File>.<name>` for the file you actually import.  Your own declarations get the default camelCase (types UpperCamel, Prop inductives lowerCamel), or `<Name>.<camel>` if they are in `notes/weak-port-dupnames.json`.  **The table is only as good as its sources.**  A dependency that broke the convention, such as `WeakVProp` (`vwpHold_ne`), `WeakView` (`View.join_l`) or the `<File>`-namespaced `WeakPromiseLitmus`, is honoured only through its header name map.  Check the "names not found" list.
* **Statements and definitions.**  These are transliterated: vocabulary (`Z`→`Int`, `bv`→`BitVec`, `gmap`→`GMapF`, `S n`→`n + 1`, `!!`→`[i]?` or `get?` on a known map, `<$>`→`List.map`/`Option.map`, `Forall`, `is_Some`, `bool_decide`, …), binders, `match`/`if`/`let`, `ltac:(…)`.  Section variables become explicit leading arguments.  A declaration gets only the variables it uses, and that includes the ones used through the section lemmas it cites.  Inside the section, references to those lemmas are passed the variables back, with implicit ones as `(P := P)`.  An untyped binder that is used as a list index gets typed `Nat`.  `Reflexive`/`Transitive` instances become theorems (WeakMem deviation 1), and `Decision` instances become `instance … := by first | infer_instance | (unfold h; infer_instance)`.  **Read every statement against the Rocq before you touch its proof.**  Known silent mistranslations: `<[i:=x]>` on something not known to be a map becomes `List.set` (flagged `XLAT?`); `filter P` becomes `List.filter (decide ∘ P)`; and `*` between types becomes `×` only when both sides look like types.
* **Proofs.**  These are transliterated tactic by tactic, with bullets and `{ }` kept.  `t; [a|b|]` becomes `on_goal`, and `[done..|…]` becomes `all_goals try`.  `induction … as [..]` becomes `next names =>`/`rename_i`; `apply` becomes Batteries `eapply`, with `.mpr`/`.mp` fallbacks for iff lemmas; `pose proof H as pat` becomes `obtain pat := id H`, which keeps `H`; `assert` becomes `have … := ?_; pick_goal 2`; `rewrite` becomes `rewrite [..]`, `//` becomes `<;> try CLOSE`, and `by` becomes `<;> CLOSE`.  `done`, `naive_solver` and `auto` become `first | …` closers.  Basic Iris proof-mode tactics map to their iris-lean names (`iIntros`→`iintro`, `iDestruct … as`→`icases … with`, …).  A tactic it cannot translate becomes

      all_goals sorry  -- ROCQ: <the Rocq tactic>

  and the rest of that goal block is kept as `-- ROCQ:` comment lines.  Replace each such block by hand.
* **The drafted proofs are verbose.**  Once a proof builds, shrink it, because the tree's style is the hand-written ports: drop the `first | …` alternatives that never fire, collapse `(eapply X) <;> (first | done | …)` to `exact X …`, and turn the `try simp only [List.getElem?_cons_succ, …]` from Rocq `simpl` into what is actually needed.  A drafted proof that does not build is a hint, not a constraint.  If it fails on the first real step, port the Rocq proof directly; do not debug the draft.

**Workflow.**

1. Generate the draft.
2. Build it once with `lean-gcp … lake build Weak.<Name>`.  The draft is meant to elaborate with errors only inside proofs.
3. Fix the statement-level errors first, which are usually few, and diff each statement against Rocq.
4. Go through the proofs in file order, fixing the failing and `sorry` ones.  Use `--rocq-comments` if you want the Rocq line next to every tactic.
5. Clean up the header (Deviations, Not ported, the name-map spellings you changed) and delete `DRAFT NOTES`.
6. Run lint (no `sorry`).

## Measured (2026-10-06)

Each file was drafted with its own Lean port **and every module downstream of it hidden** from the name table (`--eval`), and then built on the VM.  "Statements" counts definitions, inductives and theorem statements that elaborate with every proof replaced by `sorry`.  "Faithful" counts drafted theorem statements that the real port's theorem proves (`exact`/`apply` real ⇒ draft).  "Proofs" counts drafted proofs that build as emitted, with no error and no translator `sorry`.

| files | statements | faithful (thm) | proofs built | proofs with no translator sorry |
|---|---:|---:|---:|---:|
| WeakRvwmoLock, WeakRvwmoKill, WeakLitmusProj, WeakRvwmoProbeSwap, WeakPromiseLitmus | 119/120 (99%) | 93/97 (96%) | 70/97 (72%) | 94/97 |
| WeakErase, WeakRvwmoNorm, WeakRobust | 153/159 (96%) | 88/123 (72%) | 71/123 (58%) | 116/123 |
| WeakVProp, WeakView (MonPred / Iris) | 24/158 (15%) | 0/114 | 9/114 (8%) | 81/114 |

The emitted names agree with the real ports on 285/285 declarations of the eight non-Iris files.  On the two Iris files they agree on 14/134, because those ports used `_`-suffixed names.

On the first eight files, about two thirds of the proofs, and a little more for small files, need no work beyond tidying.  The `faithful` gaps on WeakErase and WeakRvwmoNorm are mostly the real ports' recorded deviations, such as a dropped `Lbl` argument and changed implicitness, and not translator errors.  **On MonPred/Iris files the draft is not useful for statements.**  The `vProp Σ`/`⊑`/`@@`/`⊒` vocabulary, their typeclass instances and the custom Rocq notations are not translated.  For those files, use the draft only for its header, its name map and its pure (non-Iris) lemmas.

**Main failure classes** (first error per failing declaration, non-Iris files):

* Lean's goal shape differs from Rocq's, and `on_goal` indices or a bullet then hit the wrong goal.  Causes: `rw` side goals; `apply` leaving instance or metavariable goals; `split_and!` versus syntactic `∧`.
* Rocq conversion that Lean does not do: `simpl`/`cbn` reducing a recursive function or a `match`, `↑0` versus `0`, setoid `reflexivity`.
* `->` intro patterns on non-variable equations (`subst` fails), and `is_Some` (Rocq `∃`, Lean `isSome = true`) destructed or introduced with `⟨…⟩`.
* Arity or implicitness differences in the ported dependencies (constructor arguments, explicit versus implicit `G`).
* Closer gaps, where `done`/`naive_solver` became `first | … | grind` and that failed: 3–7 per run.
* Iris and statement-level: the MonPred vocabulary above, and `Decision` instances the Rocq file declares and Lean needs (`decide (violp G x)`).

## Re-running the evaluation

`tools/weak_rocq2lean.py --eval <Ported1> <Ported2> … --tree <scratch copy>` writes `Weak/Draft/<Name>{S,P,C}.lean` into the scratch tree, builds them with `lean-gcp`, and prints the table above (`--report` re-reads the last `build.log`).  Use a scratch copy, never the main tree.  Put `moreLeanArgs = ["-DmaxErrors=100000"]` on the scratch lakefile's `Weak` lib, or a draft with many errors stops being checked after 100.  Re-`rsync` the scratch tree when new ports land: a draft that imports a module the scratch copy lacks fails at the import, and the whole file then counts as failed.
