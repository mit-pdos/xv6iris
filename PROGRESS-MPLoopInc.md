# PROGRESS — MPLoopInc (MP forever, with hart 0 incrementing t1 each iteration)

Owner request 2026-11-13 (verbatim): "Can we modify the lit_mpLoop program to increment t1 at the hart 0's
loop?" … "We can do a wrapping add" … "Just to make the trace property better".  Worker: Opus, workspace pcsl8.
Files (new only): `Weak/Prom/CoreLitLoopInc*.lean` (namespace `Weak.Prom.PF.LoopInc`).  `CoreLitLoop.lean` is
imported, not edited.  No root edits.

## Status

**GREEN — PASS (2026-11-13).**  `lake build Weak.Prom.CoreLitLoopIncH` succeeds (via lean-gcp; it builds
`Weak.Prom.CoreLitLoopInc` too), no warnings in the new files; two new files, 558 + 452 = 1,010 lines (target 1k,
hard stop 2.5k).  `CoreLitLoop.lean` imported, not edited; no root edits.
* `lit_mpLoopInc` (Weak/Prom/CoreLitLoopIncH.lean:326): `∀ M run, PF.validRun (xStep xsLoopInc) imgLoopInc ()
  (progs tLoopInc) M run → ∀ h, qLoopInc M (run.trace h)` — every hart, every finite run, no `done` premise.
* `loopInc_noDone` (CoreLitLoopIncH.lean:430): `∀ M run, PF.validRun … M run → ∀ h v, ¬ run.done litDone h v`.
* `qLoopInc` (Weak/Prom/CoreLitLoopInc.lean:185); value-form corollary `qLoopInc_val` (:192):
  `v1 = (v0 + (k' − k)) % 2^32`.  Index `idxOf` (:176) = number of messages to the address below `t` in `M`.
* `#print axioms` of both: `[propext, Classical.choice, Quot.sound]`.  0 named inputs (machine fact used: the
  front end's `OA.x_noInvalT`, as CoreLitLoop).

### The property as formalized (`qLoopInc M τ`)
Among the memory entries of `τ`, for every flag load `e0` immediately followed by a data load `e1`
(`ldRet Y e0 = some v0`, `ldRet X e1 = some v1`): IF `src0 e0 ≠ 0` (the flag load's byte 0 read a message, not
the initial 0 — a flag load that reads the initial 0 constrains nothing, the clean formulation), THEN
`src0 e1 ≠ 0` (the data load never reads the initial 0), `M[src0 e0 − 1]` is a FLAG message and `M[src0 e1 − 1]` a
DATA message, `v0 = wv k`, `v1 = wv k'`, `k ≤ k'`, where `k = idxOf Y M (src0 e0)`, `k' = idxOf X M (src0 e1)`,
`wv i = (1 + i) mod 2^32`.  The index is defined from `M` (as the brief's first option); that it is hart 0's
program-order iteration number is PROVED (`idx_at`: if the messages to `a` are exactly `f 0 < … < f (n−1)` then
`idxOf a M (f i) = i`; `idx_par`: hart 0's `j`-th data/flag store has index `j`).  Values are the full 32-bit
words returned (`obsOf` of all 4 bytes), not byte 0 only.

### Proof shape
* Hart 0 (`h0_loop`, Löb at `pc = 0`, quantified over the iteration `i`): Ψ0 = `Q0` — entries are
  `D 0, F 0, D 1, F 1, …` with `D i`/`F i` storing `toBytes (rv i) 4`, `rv i = (1+i) mod 2^64` (the `addi`
  wraps mod 2^64, `aluOp .add`; `sw` stores the low 32 bits); same-parity (same-address) stores are
  timestamp-increasing; `ts (D i) < ts (F i)`.  Loop invariant `I0`: `2 i` entries, every own store `≤ vwOld`,
  every data store `≤ vwNew`.  `D (i+1) > vwNew ≥ D i` (fence w,w of iteration i raised `vwNew`);
  `F (i+1) > vwNew' ≥ vwOld ≥ F i, D (i+1)` (fence w,w of iteration i+1).  NOTE: `F i < D (i+1)` is NOT
  claimed and not true in general (no ppo between them, RVWMO allows the reorder).
* Hart 1 (`h1_loop`): CoreLitLoop's Ψ1 plus, per load, its single-copy-atomicity fact `scaP` (from `loadOk`'s M9
  common read point with `wFwd = ∅`, `sca_of`).  CHECK of the brief's question: the "no DATA write between the
  data load's source and the flag load's source" fact still suffices for the INDEX argument, but NOT alone for the
  VALUES: with distinct words bytes 1–3 are no longer all 0, so each load also needs single-copy atomicity (all 4
  bytes from one message; `byte_same`, `word_read`).  It is the machine's M9 rule, recorded in Ψ1, no new input.
* Glue (`reader_ok`, A0 exports only): `msg_cls` (every message is hart 0's entry `j`, address by parity, word
  `rv (j/2)`); flag message = `F k` (index `k`); `D k < F k`; no data write in `(src0 e1, src0 e0]` ⇒
  `src0 e1 ≥ ts (D k) > 0` ⇒ data message `D k'` with `ts (D k) ≤ ts (D k')` ⇒ `k ≤ k'`; `word_read` ⇒ values.

## The program

    hart 0:  0: sw t1,0(a2)  1: fence w,w  2: sw t1,0(a3)  3: addi t1,t1,1  4: beq zero,zero,0   (t1 = 1 initially)
    hart 1:  0: lw a0,0(a3)  1: fence r,r  2: lw a1,0(a2)  3: beq zero,zero,0

## RVWMO first

RVWMO guarantees exactly this, per iteration, with distinct values: hart 0's stores to DATA are ordered among
themselves, and so are its stores to FLAG, by rule 1 ("b is a store, and a and b access overlapping memory
addresses") plus the coherence axiom, so the `k`-th store to each address in global memory order is iteration
`k`'s (the index is the iteration number).  `fence w,w` puts iteration `k`'s data store before its flag store in
ppo (rule 4: "a and b are separated by a FENCE instruction, a is in the predecessor set and b in the successor
set"); on hart 1 `fence r,r` puts the flag load before the next data load (rule 4).  If the flag load reads `F k`
(rf), then `D k <gmo F k <gmo` the data load (rf ; ppo), so by the load value axiom the data load returns `D k`'s
value or a coherence-later DATA store's, i.e. some `D k'` with `k' ≥ k`; the initial value is coherence-before
`D k` and cannot be returned.  Each aligned `lw`/`sw` is single-copy atomic (§rvwmo "All memory operations are
single-copy atomic: they can never be observed in a partially complete state"), so each load returns one store's
whole word: `wv k` and `wv k'`.  Mark: FAITHFUL (the theorem states only what RVWMO guarantees; `k' ≥ k`, not
`k' = k`, since hart 0 may run ahead).  Machine facts used (machine v2): FULFIL raises `vwOld`; `fence w,w`
raises `vwNew ≥ vwOld`; a store's timestamp exceeds `stPre ≥ vwNew`; a load raises `vrOld` to its byte-0 source
(no forwarding, `wFwd = ∅`); `fence r,r` raises `vrNew`; `loadOk` forbids a write to a byte between its source and
the floor, which M9 raises to the common read point.
