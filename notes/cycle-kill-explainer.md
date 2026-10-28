# The cycle kill: what it proves and why the bridge needs it

Written 2026-10-28 for the owner. Same content as the page
https://claude.ai/artifact/Qee4YbsFmLWHrzGp9ZkwWG.

The cycle kill is the proof that no execution of the xv6 kernel on RVWMO contains a *racy cycle*. Without
it, the bridge from RVWMO to our step-by-step proof machine (MachCSL) cannot replay every execution.

## 1. The problem: we need an order to replay in

RVWMO describes an execution as a graph of memory events. MachCSL executes one step at a time, and each
hart in program order. To turn a graph into a machine run, the bridge needs an order to step through
the events in. Every event must come after the things the machine needs to have happened first:

| Edge | Meaning | Why the machine needs it first |
| --- | --- | --- |
| program order into a store | an earlier instruction on the same hart, then a store | the machine issues a hart's stores in order |
| reads-from (rf) | a store, then a load that returns its value | the store must exist before the load can read it |
| coherence (co) | two stores to the same byte, in their final order | stores to one byte land in that order |
| from-read (fr) | a load of an older value, then the store that overwrote it | the load must read before the newer store lands |
| preserved program order (ppo) | RVWMO's own ordering rules: fences, acquire, release, dependencies | RVWMO itself requires it |

The union of these edges is `racy` (`Weak/WeakRvwmoAcyc.lean:206-214`). An order that respects all of
them exists exactly when `racy` has no cycle. A *racy cycle* is a set of events each of which must come
before the next, all the way round. No step-by-step run can produce one.

## 2. RVWMO allows racy cycles in general

RVWMO guarantees a single *global memory order* (gmo) over memory events. It contains preserved program
order and every cross-hart reads-from, coherence and from-read edge. It does **not** contain plain program
order. A load followed by an unrelated store on the same hart, with no fence, acquire or dependency
between them, can appear in either order. Those are exactly the `racy` edges that gmo lacks.

The classic case is load buffering:

```
        hart A                         hart B
   +-------------+               +-------------+
   |  ld x -> 1  |<----- rf -----|   sd x, 1   |
   +-------------+               +-------------+
          :  po (not in gmo)            ^  po (not in gmo)
          v                             :
   +-------------+               +-------------+
   |   sd y, 1   |------ rf ---->|  ld y -> 1  |
   +-------------+               +-------------+

   racy cycle:  A.ld x -po-> A.sd y -rf-> B.ld y -po-> B.sd x -rf-> A.ld x
```

RVWMO allows both loads to return 1. A machine that runs each hart in order cannot: each store would have
to exist before the load that comes before it. So "every RVWMO execution has a matching machine run" is
false for programs in general. It can only hold for a program whose structure rules racy cycles out.
Proving that for xv6 is the cycle kill's job.

## 3. How the proof works: everything must fit into gmo

The proof is by contradiction. Assume a racy cycle exists, then cut it into pieces:

- **Segments:** stretches of program order on one hart. These are the edges RVWMO may leave unordered.
- **Cross-hart edges:** the rf, co and fr edges joining one segment to the next. RVWMO already puts each
  of these in gmo.

```
   prove: first<last      prove: first<last      prove: first<last
  +----------------+     +----------------+     +----------------+
  | segment hart A |---->| segment hart B |---->| segment hart C |
  | first ---> last| gmo | first ---> last| gmo | first ---> last|
  +----------------+     +----------------+     +----------------+
          ^                                              |
          +---------------- rf / co / fr (gmo) ----------+

  all edges in gmo  =>  a cycle inside a total order  =>  impossible
```

If the kill shows that each segment's first event is before its last event in gmo, the whole cycle lies
inside gmo. A total order has no cycles, so no racy cycle exists. The kill classifies each segment:

| Class | Why the segment is ordered in gmo | xv6 example |
| --- | --- | --- |
| Preserved directly | RVWMO's own rules order it: a fence, an acquire or release, a dependency, a same-address pair, or a branch on a loaded value that guards the store (rule 11). | `release`: the critical section, then `fence rw,w`, then `sw 0` |
| Certified by a sync path | A chain of lock hand-offs starts after the segment's first event and ends before its last. Each release→acquire pair is in gmo. | A page freed by one hart and handed out by `kalloc` on another, through `kmem.lock` |
| Inside a critical section | Both ends lie between this hart's `acquire(L)` and `release(L)`, and the neighbouring events are inside other critical sections of L. Mutual exclusion orders the sections. | Two harts updating `p->state` under `p->lock` |
| Corner case | The data belongs to one hart or one process, so any cycle must leave through a kernel hand-off. | User pages: one address space per process, one hart at a time |
| Bad | None of the above. The proof must show this never occurs. | (must be empty) |

## 4. Worked example: load buffering under a lock

```
  gmo        hart A                          hart B
   |   acquire(L)
   |   ld x            (critical section)
   |   sd y            (critical section)
   |   fence rw,w; sw 0  ----- reads 0 (hand-off) ----->  amoswap.aq L
   |                                                      ld y   (critical section)
   |                                                      sd x   (critical section)
   v
       the cycle needs  B.sd x  -->  A.ld x,  i.e. an edge pointing UP: impossible
```

One of the two `amoswap`s on L wins first in coherence order; say A's. Then:

- A's fence orders A's whole critical section before its unlock.
- B's swap reads that unlock.
- B's `.aq` orders B's critical section after the swap.

So A's section lies entirely before B's in gmo, and for A's load to read B's store an edge would have to
point backwards. The cycle cannot close. The kill runs this argument, or one of the other classes, for
every segment of every possible execution of the whole kernel.

## 5. What the kill needs to know about xv6

- **The kernel proof's export:** facts proved true at every reachable machine state, such as lock-word
  discipline, page custody, and certified lock hand-offs (`Xv6/AccessDiscipline.lean`).
- **Census facts about the fixed kernel binary,** checked by `decide`: exactly seven fences in the text,
  the 18 load sites that can block, no LR/SC.
- **Named inputs, still unproved:** graph-level facts such as `WwCustody` (two harts never store to one
  byte without a hand-off between them), `NonCensusSrc`, `HeadOrdRd`, and the classification itself,
  `l2ClaimP`.

## 6. Where it stands (2026-10-28)

| Part | Status |
| --- | --- |
| The contradiction argument: classified segments ⇒ no racy cycle (`Weak/SbKill*.lean`, about 16k lines of core) | proved |
| The classification for every segment of every kernel execution (`l2ClaimP`, plan row 6n) | open |
| The graph-level named inputs (`WwCustody`, `NonCensusSrc`, `HeadOrdRd`, …) | argued, not checked |
| Segments entered through a from-read edge (F-6J-3, found 2026-10-22) | not covered until now |

Today the cycle kill is a correct proof shape whose xv6-specific premises are not all established. If any
real xv6 execution has a racy cycle, those premises are false. MachCSL then cannot reproduce that
execution, and the theorem cannot be finished on this route.

## 7. What the bridge gets from it

- **A replay order K,** in which every racy edge points forward. The replay steps through the graph in it.
- **No load buffering in xv6's executions,** so MachCSL's lack of a load buffer costs nothing.
- **Same-byte stores from different harts are always ordered by a hand-off.** That is what MachCSL's
  issue-order landing relies on (F-PW6-1).

Any machine that executes loads in order needs this argument, including the by-construction graph
machine. Only a machine whose loads can read stores that haven't executed yet (promises) avoids it.
