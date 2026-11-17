# The minimal stack (Weak/Mini) — a reading guide for vetting

Owner ruling [OWN.P18]: "For the reference program proofs, can we minimize the machinery to work for those? … I still
want the semantics and the logic. Just want them minimial."  Plan: `~/dev/weak-orch/promising/mini/plan.md` rev 4.
You vet DEFINITIONS and four THEOREM STATEMENTS; Lean checks every proof (no `sorry`/axiom/`native_decide`; every
statement below depends only on `propext`, `Classical.choice`, `Quot.sound`: `Weak/Mini/HeadCheck.lean`).

## 1. What to read, in order

| # | file | lines | role |
|---|---|---|---|
| 1 | `Weak/Mini/Val.lean` | 57 | ALU operations and branch conditions on 64-bit values, `sext` (one copy for ref and machine) |
| 2 | `Weak/Mini/Prog.lean` | 74 | the program syntax of the fragment F: `MI`, `MProg` (harts, initial registers, word image, size `sz`) |
| 3 | `Weak/Mini/Ref.lean` | 371 | **MiniRef = RVWMO on F**: events, THE AXIOM BLOCK `MEvs.ax` (§2), concrete harts with loops (§3), `miniExec` / `miniCut` (§4), `MProg.wf` (§5) |
| 4 | `Weak/Mini/Mach.lean` | 343 | **MiniMach = the Promising machine on F**: views, messages, `mMem`, looping front end, `miniValidRun` |
| 5 | `Weak/Mini/Logic.lean` :41–:120 | ~80 | **the logic's definitions**: the hart language `HE`/`hstep`, `hartSt`, `hartInterp`, `wpH`, `wp` |
| 6 | `Weak/Mini/Run.lean` :24–:40 | 13 | trace vocabulary used by the soundness statement: `Trace`, `fulfilsOf`, `ownAt`, `entryWf` |
| 7 | the four VETTED STATEMENTS | — | §2 below |

Program texts the headlines name (one definition each): `lbddP` LitLbdd.lean:22, `mpFFP` LitMpFF.lean:30
(fences `fWWm`/`fRRWm` :25/:27), `loopP` LitLoop.lean:30 (fence `fRRm` :27).  Ref.lean quotes `rvwmo.adoc` and the
FENCE text of `unpriv_rv32.adoc` (both under `~/dev/weak-orch/promising/spec/`) at every rule, with a mark.

## 2. The four vetted statements

1. `Weak.Mini.mini_forbidden_lbdd` — `Weak/Mini/Head.lean:82`: every finite execution `C` (`miniCut lbddP C`) does
   not have both harts' first loads returning 1 (`C.obsLoad`, Head.lean:33).
2. `Weak.Mini.mini_forbidden_mpFF` — `Head.lean:96`: every finite execution of `mpFFP` does not have hart 1's flag
   load returning 1 and its data load returning 0.
3. `Weak.Mini.mini_inf_mpLoop` — `Head.lean:238`: in every INFINITE execution of `loopP` (`miniExec loopP X`, the
   only premise besides the selected events), a data load that is the next memory operation after a flag load that
   returned 1 returns 1 (the shape of `inf_mpLoop`, Weak/Prom/InfLoop.lean:172).
4. `Weak.Mini.Logic.mini_adequacy` — `Weak/Mini/Adeq.lean:123`: soundness of MiniLogic in A0 shape (Ψ at every
   trace prefix, Φ of finished harts, the partition of fulfils, well-formed entries), over every MiniMach run with
   no outstanding promise.

## 3. Cone manifests (what each statement depends on; regenerate with `tools/ci/cone.sh`)

`notes/mini/cone/<decl>.txt` lists, in file order, every declaration reached from the statement through definition
bodies (never proofs), with its line span.  Weak/Mini line counts (gate K5: 600; 750 for `mini_adequacy`):

| statement | Weak/Mini lines | by file | non-Mini |
|---|---|---|---|
| `mini_forbidden_lbdd` | 339 | Ref 230, Prog 56, Val 37, Head 10, LitLbdd 6 | Lean core only |
| `mini_forbidden_mpFF` | 344 | Ref 230, Prog 56, Val 37, Head 11, LitMpFF 10 | Lean core only |
| `mini_inf_mpLoop` | 339 | Ref 224, Prog 54, Val 37, Head 13, LitLoop 9, LitMpFF 2 | Lean core only |
| `mini_adequacy` | 482 | Mach 265, Logic 62, Prog 54, Adeq 51, Val 37, Run 13 | Lean core, Std, iris-lean (by name) |

No declaration outside Weak/Mini ∪ Lean core ∪ iris-lean (and Batteries/Qq) is reached (no ALIEN line).  The tool
counts a structure's fields and an inductive's recursor as their own lines, and a declaration's docstring; it counts
`mini_adequacy`'s proof too (51 lines, of which ~16 are docstring and statement); the three headlines are one-line
wrappers of `Head.forbiddenLbdd`/`Head.forbiddenMpFF`/`Head.infMpLoop`, so their proofs are not counted.

## 4. Checked by Lean — need not be read

* every proof;
* `Eq*.lean` — the equalities with the full development on F: E1 (`e1a`/`e1b` EqRef.lean, finite cut
  `e1aCut`/`e1bCut` EqRefCut.lean, loop-free `e1aLF`/`e1bLF` EqRefLF.lean), E2 (`e2a`/`e2b` EqMach.lean), and the
  P3 cross-checks `EqHead.lean`;
* `Cmp*.lean` — L4 completeness `mini_complete` (CmpMain.lean:256): every finite MiniRef execution is a valid
  MiniMach run with the same load values;
* `Pfx*.lean` — L5 the prefix lemma `mini_prefix` (PfxMain.lean:155) and `mini_inf_complete` (:201);
* `Run.lean` (beyond the 13 lines above), `Rules.lean` (leaf rules), `LitBase`/`LitLbdd`/`LitMpFF`/`LitLoop`
  (machine-level lemmas `mini_lit_*`, proved in MiniLogic), `HeadAlt.lean` (hart 1 of `loopP` alternates
  flag/data loads, machine and reference), `MachLb.lean`, `Wf.lean`, `*Check.lean`.

## 5. Scope

* The fragment F (plan §1): `alui`, `alu`, aligned loads/stores of ONE size per program, `fence` with any sets,
  branches (any target: loops), `jal x0`, `nop`.  No AMO, LR/SC, `.aq`/`.rl`, `fence.tso`, `fence.i`, CMO, CSR, I/O,
  misaligned or mixed-size access, translation.
* `MProg.wf` (Ref.lean:357): size 1/2/4/8, aligned image, branch/jump targets inside the text, registers `< 32`, and
  ALU immediates `< 2^64` (`MI.immOk`, Ref.lean:349).  The headlines carry no `wf` premise: their three programs are
  proved well formed (`lbddP_wf`, `mpFFP_wf`, `loopP_wf`, Head.lean §2).
* Alignment is part of `miniExec`/`miniCut`: a misaligned program has NO execution, so a verdict over it would be
  vacuous.  The K4 witnesses guard this (`Weak/Mini/HeadWit.lean`): `mini_lbdd_witness` (a finite execution of lbdd in
  which both first loads exist), `mini_mpFF_witness`, `mini_infExec_witness`, and `mini_inf_mpLoop_exercised` (an
  infinite execution of `loopP` meeting EVERY premise of `mini_inf_mpLoop` at once).

## 6. Known STRONGER / WEAKER points

* MiniRef vs `rvwmo.adoc` on F: FAITHFUL rule by rule (P1 gate review, `promising/mini/P1gate-review.md` §1; no WEAKER
  item); rule 13 follows [OWN.P6]'s `[R];addr;[M];po;[W]` reading (equal to the letter on F).
* MiniMach promise rule: per step STRONGER than machine v2 (a promise is one aligned word, `tid` = the hart); equal
  on VALID runs (E2a + E2b).
* TORN runs [OWN.P19]: machine v2 admits a torn aligned same-size word read that RVWMO forbids (finding F3,
  Weak/Prom/MachTornWit.lean); MiniMach cannot tear (one message per word), so it is STRONGER than machine v2
  exactly on torn runs, which the reference excludes.  E2b carries `untorn run`; Machine.lean is unchanged until S3c.

## 7. Two notes from P2-D

* THE CUT RE-SOURCES LATE LOADS.  `mini_prefix` keeps every event of the infinite execution up to each observed
  one UNCHANGED and keeps every hart's path (pc, control taint, events up to their values); loads outside that
  po-down set may read different stores in the cut (an iterated po ∪ gmo-down closure can be infinite; plan §6).
  The headline `mini_inf_mpLoop` observes only the data load, so its row is exact.
* `immOk`.  The reference reduces an ALU immediate mod 2^64, the machine (as machine v2) uses it raw; for
  `slti`/`sltiu` with `imm ≥ 2^64` they differ, so L4 needs `imm < 2^64`.  Real RISC-V immediates are 12-bit: a scope
  artefact, now part of `MProg.wf` ([MiniP3 (0)]).

## 8. Cross-checks with the full stack (EqHead.lean)

`lbddP.toTest Lit.lbdd.cond = Lit.lbdd`, `mpFFP.toTest Lit.mpFF.cond = Lit.mpFF`, `loopP.toTest tLoop.cond = tLoop`,
`loopP.xs = xsLoop`, `lbddP = lbddM` (all `rfl`).  From the mini headlines via E1: `ref_lbdd_of_mini : forbiddenRef
Lit.lbdd`, `ref_mpFF_of_mini : forbiddenRef Lit.mpFF` (RefLitmus.lean's statements), `inf_mpLoop_recovered` (the
statement of `inf_mpLoop`, verbatim) and `inf_mpLoop_of_mini` (any `cond`).
