# PROGRESS — MPLoop ("MP forever": a non-terminating program proved in the logic)

Owner request 2026-11-13 (verbatim): "I want that example. ASAP".  Worker: Opus, workspace pcsl8.
Files (new only): `Weak/Prom/CoreLitLoop.lean` (namespace `Weak.Prom.PF.Loop`).  No root edits, no edits to
existing files.

## Status

**GREEN — PASS (2026-11-13).**  `lake build Weak.Prom.CoreLitLoop` succeeds (via lean-gcp), no warnings in the
new file; 679 lines, one new file.
* `lit_mpLoop` (Weak/Prom/CoreLitLoop.lean:541): `∀ M run, PF.validRun (xStep xsLoop) imgLoop () (progs tLoop) M run →
  ∀ h, qLoop (run.trace h)`; `qLoop` (:106) is a plain trace predicate over `memEv` — every data load immediately
  after (among memory entries) a flag load that returned 1 returned 1.  Every hart, every finite run, no
  `done` premise.
* `loop_noDone` (:653): `∀ M run, PF.validRun … M run → ∀ h v, ¬ run.done litDone h v` — pure, from the front end
  (`solo_inv`: every reachable program state of each hart has its own program and `pc < 4`).
* `#print axioms` of both: `[propext, Classical.choice, Quot.sound]`.  0 named inputs (the only machine fact is
  the front end's `OA.x_noInvalT`).
* LOGIC: the base logic A0 (`PF.adequacy`, CoreAdeq.lean, export (ii) at the final trace), `Proto.triv`, the CoreKit
  instruction rules over the loop front end's worlds (`xW` are `LitW` worlds, `OA.litW_x`/`OA.litAg_x`), plus one
  new composition `wpK_brx` (A0 twin of track (a)'s `wpKA_brx`, built from `wpK_q1`/`wpK_drainA`; no new rule of
  the logic).  Track (a)/(b) not used.  `kitAdeqX` = `kitAdeq` for `xStep`.
* Proof shape: per hart a Löb induction at `pc = 0` (`h0_loop`, `h1_loop`).  Ψ0 (`Q0`): every memory entry is a
  data store or a flag store above a data store of the same hart (fence w,w per iteration).  Ψ1 (`Q1`): every
  entry is a flag/data load, and for every ADJACENT pair (flag load, data load) no data write lies between the
  data load's byte-0 source and the flag load's (fence r,r per iteration; loop invariant `wFwd = ∅`).  After A0:
  `msg_shape` (every message is hart 0's word 1, a flag message above a data message), `byteX` (data bytes),
  `reader_ok`.

## The program

Image all zero; DATA = `X = 0x1000`, FLAG = `Y = 0x2000`; both harts loop unconditionally with
`beq zero,zero,0` (a backward branch of the loop front end `xStep`, OwnAFront.lean):

    hart 0:  0: sw t1,0(a2)   1: fence w,w   2: sw t1,0(a3)   3: beq zero,zero,0     (t1=x6=1, a2=x12=X, a3=x13=Y)
    hart 1:  0: lw a0,0(a3)   1: fence r,r   2: lw a1,0(a2)   3: beq zero,zero,0     (a2=x12=X, a3=x13=Y)

## RVWMO first

RVWMO forbids "flag = 1 then data = 0" for each iteration's pair of loads.  On hart 0, `fence w,w` puts the data
store before the (same or any later iteration's) flag store in ppo (rule 4: "a and b are separated by a FENCE
instruction, a is in the predecessor set and b in the successor set"); on hart 1, `fence r,r` puts the flag load
before the data load that follows it (rule 4 again).  If the flag load reads a flag store `f` (every flag store
writes 1, so "returned 1" means it read some `f`, rf), then the data store `d` of the same hart-0 iteration
precedes `f` in global memory order, `f` precedes the data load in global memory order (rf ; ppo), and the data
load must therefore return `d`'s value or a later one in memory order (load value axiom) — every such store
writes 1; the initial 0 is coherence-before `d`.  This is the manual's MP+fence.w.w+fence.r.r row, per iteration.
Machine facts the proof uses (machine v2): FULFIL raises `vwOld` to the store's timestamp; `fence w,w` raises the
store floor `vwNew ≥ vwOld`, which is below the next store's pre-view (EXT `stPre < ts`), so data `tx` < flag
`ty`; a LOAD raises `vrOld` to its byte-0 source (X4; no forwarding: hart 1 never stores, `wFwd = ∅` is a loop
invariant); `fence r,r` raises the load floor `vrNew ≥ vrOld`; the next load's pre-view contains `vrNew` and its
`loadOk` forbids a write to its byte between its source and the pre-view; every data message is hart 0's and
holds the word 1 (bytes 1,0,0,0), every flag message holds 1; the image holds 0.
