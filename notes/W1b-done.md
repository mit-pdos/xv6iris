# W1b done — line references for plan §A(b) / §C W1 (the plan itself is not edited)

The plan's references to `Xv6/AllocprocTrace.lean` predate W1b and its follow-up.  Current lines
(2026-10-11, after the W1b follow-up incl. [OWN.28] (A); file 447 lines, was 274 at W1 interim):

| plan cites | name | now |
|---|---|---|
| §A "Names" `:111`, §C W1 `pidPick_range :111` | `pidPick_range` | `:152` |
| §C W1 `pidPick_range_of_wf :120` | `pidPick_range_of_wf` | `:161` |
| §C W1 `pidPick_badHist :141` | `pidPick_badHist` | `:179` |
| §C W1 `badWord :146` | `AllocprocTrace.badWord` | `:184` |
| §A "Names" `:254`, §C W1 `allocprocTraceAns :254` | `allocprocTraceAns` | `:402` |
| (new, W1b) | `pidHistWf_nextOf` / `pidHistWf_nodup` | `:129` / `:209` |
| (new, W1b) | `AllocprocTrace.forkStep` | `:269` |
| (new, follow-up) | `AllocprocTrace.forkPev_comparable` | `:437` |
| (new, [OWN.28] (A)) | `AllocprocTrace.forkCite` / `forkHist` / `foldLonger_spec` / `forkCite_facts` / `forkHist_spec` | `:260` / `:318` / `:324` / `:343` / `:367` |

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

Also exported ([OWN.28] (A)): for every era k, the FORK history `AllocprocTrace.forkHist F k` (the
`niLonger` join of the pid prefixes era k's fork rounds cite) is a prefix of `(niHist F k).pev`, satisfies
`pidHistWf PIDMAX`, and its `liveList` is duplicate-free and equal to `liveOf`; every fork round's
`ι.pev` is a prefix of it.  So "live pids pairwise distinct" holds across the era's forks.  It is NOT
stated for the joined history `(niHist F k).pev` itself: that is not derivable from the NI conclusion
(only fork rounds file `pidHistWf`, via `niForkTie`; the other citing rows never read `ι.pev`).  Not
covered: pid-ledger events after the era's last fork citation.

"-1 cites the empty pid prefix" is how `syscArmFork_evNeg` builds its citation (`UIota.boot with
kev/sev := …`), not something the theorem guarantees.
