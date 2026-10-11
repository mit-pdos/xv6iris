# W1b done — line references for plan §A(b) / §C W1 (the plan itself is not edited)

The plan's references to `Xv6/AllocprocTrace.lean` predate W1b and its follow-up.  Current lines
(2026-10-11, after the W1b follow-up; file 343 lines, was 274 at W1 interim):

| plan cites | name | now |
|---|---|---|
| §A "Names" `:111`, §C W1 `pidPick_range :111` | `pidPick_range` | `:145` |
| §C W1 `pidPick_range_of_wf :120` | `pidPick_range_of_wf` | `:154` |
| §C W1 `pidPick_badHist :141` | `pidPick_badHist` | `:172` |
| §C W1 `badWord :146` | `AllocprocTrace.badWord` | `:177` |
| §A "Names" `:254`, §C W1 `allocprocTraceAns :254` | `allocprocTraceAns` | `:308` |
| (new, W1b) | `pidHistWf_nextOf` / `pidHistWf_nodup` | `:122` / `:202` |
| (new, W1b) | `AllocprocTrace.forkStep` | `:254` |
| (new, follow-up) | `AllocprocTrace.forkPev_comparable` | `:334` |

Related: `UsysDet.usysForkTie :321`, `NiLedger.niForkTie :230`, `niEntryOk`'s fork-tie row `:329`,
`niChain :764`, `niHist :775`, `niHist_below :818`, `NiEvid.niJoin :82`, `niLonger :53`,
`PidEv.pidAllocOk :230`, `pidHistWf :234`, `NiAdequacy.xv6NiPhi :91`, `SyscallArmsFork.syscArmFork_ev
:137` / `syscArmFork_evNeg :211`.

## What §A(b) should now say

The "INTERIM (W1-Q RULED (c), until W1b)" comment in §A(b) is stale: the fallback disjunct is gone and
`allocprocTraceAns` exports, at every filed fork round's citation ι of era k: the answer is
`usysForkAns ι`, `-1` or in `[1, PIDMAX]`; `pidPick PIDMAX ι.pev ∈ [1, PIDMAX]`, `nextOf PIDMAX ι.pev ≤
PIDMAX`; on success the pick not live at `ι.pev`; `pidHistWf PIDMAX ι.pev` and its live multiset
(`liveList`) duplicate-free and equal to `liveOf`; `ι.kNull → poolEmpty ι.kev.dropLast`, `ι.kOk → ¬
poolEmpty …`; and (follow-up) the filing's chain `niChain F (niHist F)` with `niBelow ι (niHist F k)`.

"Live pids pairwise distinct" holds at every fork citation, all of which are prefixes of one pid history
per era.  It is NOT a fact about the era's joined history `(niHist F k).pev`: that statement cannot be
derived from the NI conclusion (see `PROGRESS-W1bfix.md`: only fork rounds file `pidHistWf`).  Options
(A) fork-joined history, S / (B) file it at every citation, M are awaiting a ruling.

"-1 cites the empty pid prefix" is how `syscArmFork_evNeg` builds its citation (`UIota.boot with
kev/sev := …`), not something the theorem guarantees.
