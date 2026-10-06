/-
Weak: Phase 0.5 SIZE SPIKE for the spinlock plan -- mock tagged graphs with the event shape of
the pid allocation's normal path on THIS tree's xv6 kernel, and the costs of checking them
(Rocq `iris/AxSpinSpike.v` @ xxvzwolszwmp).  MEASUREMENT ONLY: no theorem of the plan is proved
here.

The Rocq header, in substance (Rocq vocabulary):

    §1 a generator of MOCK tagged graphs [gdexec_t] with the event shape of allocpid's normal
       path (real instruction lists, real KernelSyms addresses and RVC flags): per instruction
       the Sv39 walker reads of a 64-entry direct-mapped TLB miss (3 PTE reads), the fetch
       read(s) (4 B at a 4-aligned pc, else 2 B; a 4-byte instruction at pc = 2 mod 4 fetches
       twice), then the data event.  Dependency edges come from a register-provenance fold
       shaped like [AxDeps.dstep_t]: [DTaddr]/[DTdata] from the operand registers, [DTctrl]
       from the NEVER-RESET branch-source accumulator to EVERY later store (so Hctrl_closed
       holds by construction), [DTtrans] from the instruction's own walker/fetch reads.  gmo
       is an SC interleaving (round-robin chunks), rf/values by simulating memory along gmo
       (image all-zero, every store writes 1s).
    §2/§3 the boolean checks: [cat_t_consistent_b] (and its six conjuncts), [ctrl_closed_b]
       (Hctrl_closed), the gsrc sets.  §4 timings; §5 an UNVERIFIED indexed prototype
       checker, to price a re-engineered one.  The S-mode driver timing is [AxSpinSpikeRun].

    ROCQ RESULTS (VM, vm_compute): per hart (k failed spins) 209 + 4k instructions, 220/224
    fetch reads, 15 walker reads, data 37 R + 36 W + (k+1) RMW + 1 fence, 309/314 memory
    events, 224/250 DTctrl edges, 280/308 edges.  Graphs (a) 623 gmo events / 588 deps,
    (a') 932 / 868, (b) 634 / 590.  ctrl_closed_b (a) 16.5 s, (a') 35.9 s, (b) 16.3 s; gsrc
    (a) 4.5 s.  SHIPPED cat_t_consistent_b ~N^3.5, 235 s already at N = 136 (ppo conjunct),
    extrapolated (a) ~16 h => INFEASIBLE as is.  PROTOTYPE: ppo <= gmo (a) 6.7 s, (a') 12.9 s,
    load-value + atomicity < 0.1 s; rejects a reversed gmo (95 events: 0.06 s vs 100.8 s).

WHAT THIS FILE PROVES (Lean).  The generator, the checks and the prototype (all definitions),
plus, in place of Rocq's `Eval` commands, THEOREMS pinning the kernel's evaluation
(`decide +kernel`): the trace/kernel-text agreement `traceText` (Lean-only: every pc of a hart
trace is an instruction of THIS kernel's text, of the width the RVC flag says), the counts
(`countsHart00/11`, `countsRacer`), the graph sizes (`gsizeGA/GA'/GB`, `gsizeSmall`) and the
prototype verdicts on the small graphs (`fastG40PpoG10`, `fastG601`, `fastRevG601`).  The
full-size prototype load-value runs are `#eval`s (`tm` prints value and time).

LEAN RESULTS (this tree's kernel, xv6 b72cbac1; VM c4d):
- Per hart (k failed spins): 464 + 4k instructions; 499/503 fetch reads; 33 walker reads (11
  cold pages, 6 of them the proc table beyond pid_lock's page); data 98 R + 34 W + (k+1) RMW + 1
  fence; 665/670 memory events; 1338/1365 DTctrl edges, 1394/1423 edges in all.  Racer: 3
  instructions, 11 events.  THE DRIFT IS ALMOST ALL THE INLINED pid ALLOCATION (below): its
  64-round uniqueness scan adds 256 instructions and 64 loads, and every scan load enters the
  never-reset ctrl accumulator, so each later store carries about 70 DTctrl edges.
- Graphs: (a) 1335 gmo events / 2817 deps; (a') 2000 / 4211; (b) 1346 / 2819 (about 2.1x
  Rocq's events, 4.8x its deps).  Truncated: g10 (50, 12), g20 (80, 20), g40 (144, 36),
  g601 (101, 31).
- SHIPPED checker under the compiled evaluator (`#eval`, the `vm_compute` analogue; the
  library's list functions are native code and `&&`/`||` short-circuit, which is what made
  Rocq's strict `vm_compute` cubic-and-worse): `catTConsistentB` (a) = true in 208 s
  (Rocq: extrapolated ~16 h); conjuncts on (a): c_wf 0.15 s, c_dw 0.03 s, c_dg 1.8 s, c_lv
  12.2 s, c_at 0.2 s, c_ppo 173 s, c_ppo_po 173 s (the same: the cost is inside gppoCatB).
  Ladder: c_lv g10/g20/g40 0.010/0.024/0.077 s, c_ppo 0.020/0.051/0.18 s (~N^2),
  catTConsistentB g10 0.031 s; the shipped checker rejects reversed g601 in 0.13 s (Rocq
  100.8 s).  ctrlClosedB (a) 6.7 s, (a') 14.0 s, (b) 6.7 s (all true); gsrcAll (a) 273916 in
  2.6 s, (a') 407470 in 4.9 s, (b) 273916 in 2.7 s.  So the VERDICT DIFFERS from Rocq's: on
  this evaluator the shipped checker is FEASIBLE at size (a) (minutes, not hours) -- but a
  closed PROOF needs the kernel, which is far slower (below).
- Prototype (§5): ppo <= gmo (a) 14.5 s, (a') 23.5 s, (b) 14.7 s (#eval; kept as comments,
  too slow to re-run on every build); load-value + atomicity (a) 0.08 s, (a') 0.12 s, (b)
  0.08 s (live `#eval`s); rejects the reversed gmo (a) in 14.7 s, g601 (kernel).
- Kernel (`decide +kernel`, theorems checked in parallel, so times include contention):
  counts 1.5-3 s each; gsize (a)/(a')/(b) 6/10/13 s; `fastG40PpoG10` 36 s; `fastG601` 57 s;
  `fastRevG601` 72 s; for scale, `ctrlClosedB g40` took 62 s and `lvAtFast gA` 100 s (not
  kept).  Build of this file: about 75 s wall.

KERNEL-IMAGE DRIFT (Rocq build -> this tree, `MachCSL.KernelSyms`):
- holding 0x80000ba2 -> 0x80000bf2, push_off 0x80000bce -> 0x80000c1e, acquire 0x80000c08 ->
  0x80000c58, pop_off 0x80000c48 -> 0x80000c98, release 0x80000c90 -> 0x80000ce0, mycpu
  0x800018e6 -> 0x8000195c, nextpid 0x8000a1f4 -> 0x8000a384, stack0 0x8000a250 ->
  0x8000a420, pid_lock 0x80012348 -> 0x80012500, cpus 0x80012378 -> 0x80012530, proc
  0x80012778 -> 0x80012930.  The offsets, RVC flags and register use inside mycpu, push_off,
  holding (both paths), acquire, pop_off and release are IDENTICAL to Rocq's lists (checked
  against the disassembly; widths re-checked by `traceText`).  mycpu now starts at 0 mod 4,
  so its `auipc`/`addi` pair sits at 2 mod 4 and fetches twice (Rocq: once).
- `allocpid` (Rocq 0x800019de) DOES NOT EXIST: this build inlines it into `allocproc`
  (0x80001b72), and the verified branch's allocpid also SCANS `proc[0..NPROC)` for a pid
  collision.  `allocpidTr` is the inlined copy `allocproc+0x38..+0x94` on the normal path (no
  wrap at 1000, no collision): `auipc/addi a0 = &pid_lock; jal acquire; auipc/lw a3 =
  nextpid; li a6,1000; li a0,1; auipc/addi a2 = &tickslock; j; mv a1,a0; beq a3,a6; addiw
  a1,a3,1; auipc/addi a5 = proc;` 64 x `lw a4,48(a5); beq a4,a3; addi a5,a5,376; bne a5,a2`;
  `auipc a5; sw a1,nextpid; sw a3,48(s1)` (p->pid, now INSIDE the critical section);
  `auipc/addi a0; jal release`.  No own frame, no prologue/epilogue (Rocq's allocpid had
  both); acquire/release get `allocproc`'s frame `sp - 32`.  `sAllocpid` names the start of
  the copy, `allocproc + 0x38`.  Consequence for downstream (`AxSpinCtl` D3): the `s1`
  release/holding spill now stores `p` (exact; allocproc's `s1`), not a LOADED pid, and
  offsets `apid 0x1e` etc. have no counterpart.
- The racer stays at Rocq's mock page 0x80002000 (not real text, as in Rocq).

Deviations from Rocq:
- The kernel image (above).  `allocpidTr` takes the process slot `p` (new argument; `hartTr`
  passes `hproc i = proc + 376 i`, hart i's slot — the mock does not model allocproc's slot
  search); new `sAllocproc`, `sProc`, `nproc`, `scanTr`, `hproc`.
- ALL names are in `namespace Weak.AxSpinSpike` (the Rocq module's own names `step`, `gen`,
  `walk`, `emit`, `edges`, `prov`, ... are too generic for the shared `Weak` namespace); this
  covers the duplicated names `aev g0 sched ctrl_closed_b gN rdb wrb`
  (`notes/weak-port-dupnames.json`) as `AxSpinSpike.*`.
- Rocq `at_` is `atBase` (`at` is a Lean keyword); trace entries are right-nested
  `(pc, rvc, ins)` triples, dependency triples left-nested `((j, k), tag)` (AxDeps' `Redge`).
- Rocq `gmap` (memory, the prototype's indices) is the Lean-only binary trie `NMap` (exact
  for keys below 2^64; `GMap2` curried for `geid` keys, `zget`/`zset` at Int addresses):
  `ExtTreeMap` does not evaluate well in the kernel.  `imap` is a structural Lean-only
  `imapFrom` (`List.mapIdx` goes through an `Array`).  `list_to_map` is `NMap.ofList`
  (`foldr`, first binding wins, as stdpp).
- `Z.land`/`Z.shiftr` on (non-negative) addresses are computed on `Int.toNat`; `gsrc_all`
  returns `Nat` (Rocq `N`).  `zn` is `Int.toNat`.
- The measurements: Rocq's `Eval`/`Time Eval` lines become kernel theorems where the kernel is
  fast enough, live `#eval`s for the full-size load-value runs, comments with recorded results
  for the full-size ppo runs and the shipped checker (Rocq too kept its slow runs as comments).
  Rocq's `Time Eval vm_compute in ppo_gmo_fast gA` etc. are therefore comments here.

Rocq -> Lean names (all `Weak.AxSpinSpike.`): `s_mycpu s_push_off s_pop_off s_holding s_acquire
s_release s_allocpid s_pid_lock s_nextpid s_stack0 s_cpus` -> `sMycpu sPushOff sPopOff
sHolding sAcquire sRelease sAllocpid sPidLock sNextpid sStack0 sCpus`; `ins`/`IOp ...` ->
`Ins`/`Ins.IOp ...`; `ti`/`TI`/`t_pc t_rvc t_ins` -> `Ti`/`Ti.mk`/`tPc tRvc tIns`; `at_` ->
`atBase`; `mycpu_tr push_off_tr holding_nh_tr holding_h_tr spin_tr acquire_tr pop_off_tr
release_tr allocpid_tr racer_tr hsp hcpu hart_tr` -> `mycpuTr pushOffTr holdingNhTr holdingHTr
spinTr acquireTr popOffTr releaseTr allocpidTr racerTr hsp hcpu hartTr`; `akind`/`KR KW KRmw
KF` -> `Akind`/same; `aev`/`AE`/`ae_k ae_a ae_n ae_cls` -> `Aev`/`Aev.mk`/`aeK aeA aeN aeCls`;
`gst`/`GS`/`g_pos g_prov g_ctl g_tlb g_evs g_deps` -> `Gst`/`Gst.mk`/`gPos gProv gCtl gTlb gEvs
gDeps`; `g0 nodup_app' prov provs setprov emit add_deps set_ctl pt_root pt_l1 pt_l0 walk edges
wdeps zn step gen` -> `g0 nodupApp' prov provs setprov emit addDeps setCtl ptRoot ptL1 ptL0 walk
edges wdeps zn step gen`; `ast`/`AS`/`a_mem a_nw a_gmo a_rows` -> `Ast`/`Ast.mk`/`aMem aNw aGmo
aRows`; `rd_byte rd_bytes wr_bytes push_row do_ev sched mkGT` -> `rdByte rdBytes wrBytes pushRow
doEv sched mkGT`; `cnt_ins cnt_cls cnt_kind cnt_tag counts` -> `cntIns cntCls cntKind cntTag
counts`; `dtag_eqb geid_eqb ctrl_closed_b gsrc_l gsrc_all c_wf c_lv c_at c_dw c_dg c_ppo gsize
gN gA gA' gB ppo_gmo_po_b c_ppo_po g10 g20 g40` -> `dtagEqb geidEqb ctrlClosedB gsrcL gsrcAll
cWf cLv cAt cDw cDg cPpo gsize gN gA gA' gB ppoGmoPoB cPpoPo g10 g20 g40`; `rdb wrb`/`fidx`/
`FI`/`f_pos f_wix f_wev f_wa` -> `rdb wrb`/`Fidx`/`Fidx.mk`/`fPos fWix fWev fWa`; `mk_idx pos_lt
between ppo_fast ppo_gmo_fast vis lv_at_fast rev_gmo g60_1` -> `mkIdx posLt between ppoFast
ppoGmoFast vis lvAtFast revGmo g601`.  The `Eval` lines -> `countsHart00 countsHart11
countsRacer gsizeGA gsizeGA' gsizeGB fastG40PpoG10 fastG601 fastRevG601` (theorems) and the
`#eval`s.  Lean-only: `sAllocproc sProc nproc scanTr hproc traceText imapFrom imap NMap
NMap.get? NMap.ins NMap.lookup NMap.insert NMap.ofList GMap2 GMap2.lookup GMap2.insert
GMap2.ofList zget zset tm gsizeSmall`.

Dropped: nothing.  (WeakEvInst device arms: not used.)
-/
import Weak.WeakMem
import Weak.WeakLitmus
import Weak.WeakAxiomatic
import Weak.WeakRvwmoGraph
import Weak.WeakRvwmoDec
import Weak.AxGraphCat
import Weak.AxGraphDec
import Weak.AxDeps
import Xv6.KernelTree

namespace Weak

open MachCSL
open Lbl Dtag

namespace AxSpinSpike

/-! ## 0. The kernel symbols (this tree's build, `Xv6/KernelImage.lean`) -/

def sMycpu : Int := KernelSyms.«mycpu»
def sPushOff : Int := KernelSyms.«push_off»
def sPopOff : Int := KernelSyms.«pop_off»
def sHolding : Int := KernelSyms.«holding»
def sAcquire : Int := KernelSyms.«acquire»
def sRelease : Int := KernelSyms.«release»
/-- (Lean-only) `allocproc`, into which this build inlines `allocpid`. -/
def sAllocproc : Int := KernelSyms.«allocproc»
/-- Rocq `s_allocpid`: there is no `allocpid` function in this build; the name is kept for the
START of its inlined copy, `allocproc+0x38` (`auipc a0,pid_lock`). -/
def sAllocpid : Int := sAllocproc + 0x38
def sPidLock : Int := KernelSyms.«pid_lock»
def sNextpid : Int := KernelSyms.«nextpid»
def sStack0 : Int := KernelSyms.«stack0»
def sCpus : Int := KernelSyms.«cpus»
/-- (Lean-only) the process table, `proc[NPROC]`, 376 bytes an entry, `pid` at offset 48. -/
def sProc : Int := KernelSyms.«proc»
/-- (Lean-only) `NPROC` (`(tickslock - proc) / 376`). -/
def nproc : Nat := 64

/-! ## 1. Instruction traces of the pid allocation's normal path -/

/-- Register numbers and widths as `Int` (Rocq's `%Z` lists). -/
inductive Ins where
  | IOp (rd : Int) (rs : List Int)
  | IJal (rd : Int)
  | IBr (rs : List Int)
  | ILd (rd rb : Int) (a : Int) (n : Int)
  | ISt (rv rb : Int) (a : Int) (n : Int)
  | IAmo (rd rv rb : Int) (a : Int)
  | IFence
  deriving DecidableEq, Repr

open Ins

structure Ti where
  mk ::
  tPc : Int
  tRvc : Bool
  tIns : Ins
  deriving DecidableEq, Repr

/-- Rocq `at_`. -/
def atBase (b : Int) (l : List (Int × Bool × Ins)) : List Ti :=
  l.map fun x => ⟨b + x.1, x.2.1, x.2.2⟩

/- x1 ra, x2 sp, x4 tp, x8 s0, x9 s1, x10 a0, x11 a1, x12 a2, x13 a3, x14 a4, x15 a5, x16 a6 -/

def mycpuTr (sp : Int) : List Ti :=
  let f := sp - 16
  atBase sMycpu
   [(0x0, true, IOp 2 [2]), (0x2, true, ISt 1 2 (f + 8) 8), (0x4, true, ISt 8 2 f 8),
    (0x6, true, IOp 8 [2]), (0x8, true, IOp 15 [4]), (0xa, true, IOp 15 [15]),
    (0xc, true, IOp 15 [15]), (0xe, false, IOp 10 []), (0x12, false, IOp 10 [10]),
    (0x16, true, IOp 10 [15, 10]), (0x18, true, ILd 1 2 (f + 8) 8),
    (0x1a, true, ILd 8 2 f 8), (0x1c, true, IOp 2 [2]), (0x1e, true, IBr [1])]

def pushOffTr (sp c : Int) : List Ti :=
  let f := sp - 32
  atBase sPushOff
   [(0x0, true, IOp 2 [2]), (0x2, true, ISt 1 2 (f + 24) 8), (0x4, true, ISt 8 2 (f + 16) 8),
    (0x6, true, ISt 9 2 (f + 8) 8), (0x8, true, IOp 8 [2]), (0xa, false, IOp 15 []),
    (0xe, true, IOp 9 [15]), (0x10, false, IJal 1)] ++
  mycpuTr f ++
  atBase sPushOff [(0x14, true, ILd 15 10 (c + 120) 4), (0x16, true, IBr [15]),
                (0x2c, false, IJal 1)] ++
  mycpuTr f ++
  atBase sPushOff [(0x30, false, IOp 15 [9]), (0x34, true, IOp 15 [15]),
                (0x36, true, ISt 15 10 (c + 124) 4), (0x38, true, IJal 0),
                (0x18, false, IJal 1)] ++
  mycpuTr f ++
  atBase sPushOff
   [(0x1c, true, ILd 15 10 (c + 120) 4), (0x1e, true, IOp 15 [15]),
    (0x20, true, ISt 15 10 (c + 120) 4), (0x22, true, ILd 1 2 (f + 24) 8),
    (0x24, true, ILd 8 2 (f + 16) 8), (0x26, true, ILd 9 2 (f + 8) 8),
    (0x28, true, IOp 2 [2]), (0x2a, true, IBr [1])]

/-- `holding`, lock not held (acquire's call). -/
def holdingNhTr (lk : Int) : List Ti :=
  atBase sHolding [(0x0, true, ILd 15 10 lk 4), (0x2, true, IBr [15]),
               (0x4, true, IOp 10 []), (0x6, true, IBr [1])]

/-- `holding`, lock held (release's call). -/
def holdingHTr (sp lk : Int) : List Ti :=
  let f := sp - 32
  atBase sHolding
   [(0x0, true, ILd 15 10 lk 4), (0x2, true, IBr [15]), (0x8, true, IOp 2 [2]),
    (0xa, true, ISt 1 2 (f + 24) 8), (0xc, true, ISt 8 2 (f + 16) 8),
    (0xe, true, ISt 9 2 (f + 8) 8), (0x10, true, IOp 8 [2]),
    (0x12, true, ILd 15 10 (lk + 16) 8), (0x14, true, IOp 9 [15]), (0x16, false, IJal 1)] ++
  mycpuTr f ++
  atBase sHolding
   [(0x1a, false, IOp 10 [9, 10]), (0x1e, false, IOp 10 [10]),
    (0x22, true, ILd 1 2 (f + 24) 8), (0x24, true, ILd 8 2 (f + 16) 8),
    (0x26, true, ILd 9 2 (f + 8) 8), (0x28, true, IOp 2 [2]), (0x2a, true, IBr [1])]

def spinTr (lk : Int) : List Ti :=
  atBase sAcquire [(0x1a, true, IOp 15 [14]), (0x1c, false, IAmo 15 15 9 lk),
               (0x20, true, IOp 15 [15]), (0x22, true, IBr [15])]

/-- `acquire` with `k` failed spins. -/
def acquireTr (k : Nat) (sp lk c : Int) : List Ti :=
  let f := sp - 32
  atBase sAcquire
   [(0x0, true, IOp 2 [2]), (0x2, true, ISt 1 2 (f + 24) 8), (0x4, true, ISt 8 2 (f + 16) 8),
    (0x6, true, ISt 9 2 (f + 8) 8), (0x8, true, IOp 8 [2]), (0xa, true, IOp 9 [10]),
    (0xc, false, IJal 1)] ++
  pushOffTr f c ++
  atBase sAcquire [(0x10, true, IOp 10 [9]), (0x12, false, IJal 1)] ++
  holdingNhTr lk ++
  atBase sAcquire [(0x16, true, IOp 14 []), (0x18, true, IBr [10])] ++
  (List.replicate (k + 1) (spinTr lk)).flatten ++
  atBase sAcquire [(0x24, false, IJal 1)] ++
  mycpuTr f ++
  atBase sAcquire
   [(0x28, true, ISt 10 9 (lk + 16) 8), (0x2a, true, ILd 1 2 (f + 24) 8),
    (0x2c, true, ILd 8 2 (f + 16) 8), (0x2e, true, ILd 9 2 (f + 8) 8),
    (0x30, true, IOp 2 [2]), (0x32, true, IBr [1])]

def popOffTr (sp c : Int) : List Ti :=
  let f := sp - 16
  atBase sPopOff
   [(0x0, true, IOp 2 [2]), (0x2, true, ISt 1 2 (f + 8) 8), (0x4, true, ISt 8 2 f 8),
    (0x6, true, IOp 8 [2]), (0x8, false, IJal 1)] ++
  mycpuTr f ++
  atBase sPopOff
   [(0xc, false, IOp 15 []), (0x10, true, IOp 15 [15]), (0x12, true, IBr [15]),
    (0x14, true, ILd 15 10 (c + 120) 4), (0x16, false, IBr [15]),
    (0x1a, true, IOp 15 [15]), (0x1c, true, ISt 15 10 (c + 120) 4), (0x1e, true, IBr [15]),
    (0x20, true, ILd 15 10 (c + 124) 4), (0x22, true, IBr [15]),
    (0x28, true, ILd 1 2 (f + 8) 8), (0x2a, true, ILd 8 2 f 8),
    (0x2c, true, IOp 2 [2]), (0x2e, true, IBr [1])]

def releaseTr (sp lk c : Int) : List Ti :=
  let f := sp - 32
  atBase sRelease
   [(0x0, true, IOp 2 [2]), (0x2, true, ISt 1 2 (f + 24) 8), (0x4, true, ISt 8 2 (f + 16) 8),
    (0x6, true, ISt 9 2 (f + 8) 8), (0x8, true, IOp 8 [2]), (0xa, true, IOp 9 [10]),
    (0xc, false, IJal 1)] ++
  holdingHTr f lk ++
  atBase sRelease
   [(0x10, true, IBr [10]), (0x12, false, ISt 0 9 (lk + 16) 8), (0x16, false, IFence),
    (0x1a, false, ISt 0 9 lk 4), (0x1e, false, IJal 1)] ++
  popOffTr f c ++
  atBase sRelease
   [(0x22, true, ILd 1 2 (f + 24) 8), (0x24, true, ILd 8 2 (f + 16) 8),
    (0x26, true, ILd 9 2 (f + 8) 8), (0x28, true, IOp 2 [2]), (0x2a, true, IBr [1])]

/-- (Lean-only) one round of the inlined pid-uniqueness scan, `allocproc+0x74..0x7e`, over
`proc[j]` (normal path: no collision). -/
def scanTr (j : Nat) : List Ti :=
  atBase sAllocproc
   [(0x74, true, ILd 14 15 (sProc + 376 * (j : Int) + 48) 4), (0x76, false, IBr [14, 13]),
    (0x7a, false, IOp 15 [15]), (0x7e, false, IBr [15, 12])]

/-- Rocq `allocpid_tr`: here the INLINED copy, `allocproc+0x38..0x94` (`allocproc`'s frame is
`sp - 32`; `p` is the slot `allocproc` holds, `s1`): `acquire(&pid_lock)`, read `nextpid`, the
scan of all `nproc` slots for the pid, `nextpid = pid + 1`, `p->pid = pid`,
`release(&pid_lock)`. -/
def allocpidTr (k : Nat) (sp c p : Int) : List Ti :=
  let f := sp - 32
  atBase sAllocproc
   [(0x38, false, IOp 10 []), (0x3c, false, IOp 10 [10]), (0x40, false, IJal 1)] ++
  acquireTr k f sPidLock c ++
  atBase sAllocproc
   [(0x44, false, IOp 13 []), (0x48, false, ILd 13 13 sNextpid 4), (0x4c, false, IOp 16 []),
    (0x50, true, IOp 10 []), (0x52, false, IOp 12 []), (0x56, false, IOp 12 [12]),
    (0x5a, true, IJal 0), (0x62, true, IOp 11 [10]), (0x64, false, IBr [13, 16]),
    (0x68, false, IOp 11 [13]), (0x6c, false, IOp 15 []), (0x70, false, IOp 15 [15])] ++
  (List.range nproc).flatMap scanTr ++
  atBase sAllocproc
   [(0x82, false, IOp 15 []), (0x86, false, ISt 11 15 sNextpid 4),
    (0x8a, true, ISt 13 9 (p + 48) 4), (0x8c, false, IOp 10 []), (0x90, false, IOp 10 [10]),
    (0x94, false, IJal 1)] ++
  releaseTr f sPidLock c

/-- Certificate (b)'s racy hart C: `lw a5,0(a0); addiw a5,a5,1; sw a5,0(a0)` at some other text
page. -/
def racerTr : List Ti :=
  atBase 0x80002000 [(0x0, false, ILd 15 10 sNextpid 4), (0x4, false, IOp 15 [15]),
                    (0x8, false, ISt 15 10 sNextpid 4)]

/-- Hart `i`'s geometry: stack top `stack0 + 4096 (i+1)`, `cpus[i]` (128 B each). -/
def hsp (i : Nat) : Int := sStack0 + 4096 * ((i : Int) + 1)
def hcpu (i : Nat) : Int := sCpus + 128 * (i : Int)
/-- (Lean-only) hart `i`'s process slot, `proc[i]`. -/
def hproc (i : Nat) : Int := sProc + 376 * (i : Int)
def hartTr (k i : Nat) : List Ti := allocpidTr k (hsp i) (hcpu i) (hproc i)

/-- (Lean-only) the drift check: every pc of the traces is an instruction of THIS kernel's
text, of the width the trace's RVC flag says. -/
theorem traceText :
    ((hartTr 1 0) ++ hartTr 0 1).all (fun t =>
      match Xv6.Kernel.textTree.find? t.tPc.toNat with
      | some k => Nat.beq k.width (if t.tRvc then 2 else 4)
      | none => false) = true := by
  decide +kernel

/-! ## 2. Event generation: TLB, fetches, provenance fold -/

inductive Akind where
  | KR | KW | KRmw | KF
  deriving DecidableEq, Repr

open Akind

/-- `aeCls`: 0 data, 1 fetch, 2 walker. -/
structure Aev where
  mk ::
  aeK : Akind
  aeA : Int
  aeN : Nat
  aeCls : Nat
  deriving DecidableEq, Repr

structure Gst where
  mk ::
  gPos : Nat
  /-- 32 registers. -/
  gProv : List (List Nat)
  gCtl : List Nat
  /-- 64 direct-mapped entries. -/
  gTlb : List (Option Int)
  /-- Reversed. -/
  gEvs : List Aev
  gDeps : List ((Nat × Nat) × Dtag)

def g0 : Gst := ⟨0, List.replicate 32 [], [], List.replicate 64 none, [], []⟩

def nodupApp' (l1 l2 : List Nat) : List Nat :=
  l1 ++ l2.filter (fun x => !(l1.any (Nat.beq x)))

def prov (s : Gst) (r : Nat) : List Nat := (s.gProv[r]?).getD []
def provs (s : Gst) (rs : List Nat) : List Nat :=
  rs.foldl (fun acc r => nodupApp' acc (prov s r)) []

def setprov (s : Gst) (r : Nat) (p : List Nat) : Gst :=
  if Nat.beq r 0 then s else
  ⟨s.gPos, s.gProv.set r p, s.gCtl, s.gTlb, s.gEvs, s.gDeps⟩

def emit (s : Gst) (e : Aev) : Gst × Nat :=
  (⟨s.gPos + 1, s.gProv, s.gCtl, s.gTlb, e :: s.gEvs, s.gDeps⟩, s.gPos)

def addDeps (s : Gst) (ds : List ((Nat × Nat) × Dtag)) : Gst :=
  ⟨s.gPos, s.gProv, s.gCtl, s.gTlb, s.gEvs, ds ++ s.gDeps⟩

def setCtl (s : Gst) (c : List Nat) : Gst :=
  ⟨s.gPos, s.gProv, c, s.gTlb, s.gEvs, s.gDeps⟩

def ptRoot : Int := 0x87fff000
def ptL1 : Int := 0x87ffe000
def ptL0 : Int := 0x87ffd000

/-- Translation: hit, or 3 walker reads (root, L1, L0) and a TLB fill. -/
def walk (s : Gst) (va : Int) : Gst × List Nat :=
  let vpn := va.toNat >>> 12
  let idx := vpn &&& 63
  let hit := match s.gTlb[idx]? with
    | some (some v) => decide (v = (vpn : Int))
    | _ => false
  if hit then (s, []) else
  let (s, p1) := emit s ⟨KR, ptRoot + 8 * (((vpn >>> 18) &&& 511 : Nat) : Int), 8, 2⟩
  let (s, p2) := emit s ⟨KR, ptL1 + 8 * (((vpn >>> 9) &&& 511 : Nat) : Int), 8, 2⟩
  let (s, p3) := emit s ⟨KR, ptL0 + 8 * ((vpn &&& 511 : Nat) : Int), 8, 2⟩
  (⟨s.gPos, s.gProv, s.gCtl, s.gTlb.set idx (some (vpn : Int)), s.gEvs, s.gDeps⟩, [p1, p2, p3])

def edges (tg : Dtag) (k : Nat) (js : List Nat) : List ((Nat × Nat) × Dtag) :=
  js.map fun j => ((j, k), tg)

/-- Store-like dependency edges (`dedgesW` minus r13/ctx, both empty here). -/
def wdeps (s : Gst) (k : Nat) (rb rv : Nat) (ld : List Nat) : List ((Nat × Nat) × Dtag) :=
  edges DTaddr k (prov s rb) ++ edges DTdata k (prov s rv) ++
  edges DTctrl k s.gCtl ++ edges DTtrans k ld

def zn : Int → Nat := Int.toNat

def step (s : Gst) (t : Ti) : Gst :=
  let (s, w1) := walk s t.tPc
  let al := Nat.beq (t.tPc.toNat &&& 3) 0
  let (s, f1) := emit s ⟨KR, t.tPc, if al then 4 else 2, 1⟩
  let (s, f2) := if !t.tRvc && !al
                 then let (s, f) := emit s ⟨KR, t.tPc + 2, 2, 1⟩; (s, [f])
                 else (s, [])
  let ld := w1 ++ [f1] ++ f2
  match t.tIns with
  | IOp rd rs => setprov s (zn rd) (provs s (rs.map zn))
  | IJal rd => setprov s (zn rd) []
  | IBr rs => setCtl s (nodupApp' s.gCtl (provs s (rs.map zn)))
  | ILd rd rb a n =>
      let (s, _) := walk s a
      let (s, k) := emit s ⟨KR, a, zn n, 0⟩
      setprov (addDeps s (edges DTaddr k (prov s (zn rb)))) (zn rd) [k]
  | ISt rv rb a n =>
      let (s, w2) := walk s a
      let (s, k) := emit s ⟨KW, a, zn n, 0⟩
      addDeps s (wdeps s k (zn rb) (zn rv) (ld ++ w2))
  | IAmo rd rv rb a =>
      let (s, w2) := walk s a
      let (s, k) := emit s ⟨KRmw, a, 4, 0⟩
      setprov (addDeps s (wdeps s k (zn rb) (zn rv) (ld ++ w2))) (zn rd) [k]
  | IFence => (emit s ⟨KF, 0, 0, 0⟩).1

def gen (tr : List Ti) : List Aev × List ((Nat × Nat) × Dtag) :=
  let s := tr.foldl step g0
  (s.gEvs.reverse, s.gDeps)

/-! ### 2.1 Assembly: SC interleaving, memory simulation, labels -/

/-- (Lean-only) Rocq's `imap`, structurally (`List.mapIdx` goes through an `Array`, which the
kernel evaluates slowly). -/
def imapFrom {A B : Type} (f : Nat → A → B) : Nat → List A → List B
  | _, [] => []
  | n, a :: l => f n a :: imapFrom f (n + 1) l

def imap {A B : Type} (f : Nat → A → B) (l : List A) : List B := imapFrom f 0 l

/-- (Lean-only) a finite map keyed by `Nat` (a binary trie, stdpp `Pmap`-style): Rocq's `gmap`
for the closed computations (kernel-friendly; exact below `2 ^ 64`). -/
inductive NMap (V : Type) where
  | leaf
  | node (v : Option V) (l r : NMap V)

def NMap.get? {V : Type} : Nat → NMap V → Nat → Option V
  | _, .leaf, _ => none
  | 0, .node v _ _, _ => v
  | d + 1, .node v l r, k =>
    if Nat.beq k 0 then v
    else if Nat.beq (k % 2) 0 then NMap.get? d l (k / 2) else NMap.get? d r (k / 2)

def NMap.ins {V : Type} : Nat → NMap V → Nat → V → NMap V
  | 0, .leaf, _, x => .node (some x) .leaf .leaf
  | 0, .node _ l r, _, x => .node (some x) l r
  | d + 1, t, k, x =>
    let (v, l, r) := match t with
      | .leaf => (none, .leaf, .leaf)
      | .node v l r => (v, l, r)
    if Nat.beq k 0 then .node (some x) l r
    else if Nat.beq (k % 2) 0 then .node v (NMap.ins d l (k / 2) x) r
    else .node v l (NMap.ins d r (k / 2) x)

/-- `m !! k`. -/
def NMap.lookup {V : Type} (m : NMap V) (k : Nat) : Option V := NMap.get? 64 m k
/-- `<[k := x]> m`. -/
def NMap.insert {V : Type} (m : NMap V) (k : Nat) (x : V) : NMap V := NMap.ins 64 m k x
/-- Rocq `list_to_map` (`foldr`: the first binding of a key wins). -/
def NMap.ofList {V : Type} (l : List (Nat × V)) : NMap V :=
  l.foldr (fun p m => m.insert p.1 p.2) .leaf

/-- (Lean-only) `gmap (nat * nat) V`, curried. -/
abbrev GMap2 (V : Type) : Type := NMap (NMap V)
def GMap2.lookup {V : Type} (m : GMap2 V) (e : Geid) : Option V :=
  (NMap.lookup m e.1).bind fun m' => NMap.lookup m' e.2
def GMap2.insert {V : Type} (m : GMap2 V) (e : Geid) (x : V) : GMap2 V :=
  NMap.insert m e.1 (NMap.insert ((NMap.lookup m e.1).getD .leaf) e.2 x)
def GMap2.ofList {V : Type} (l : List (Geid × V)) : GMap2 V :=
  l.foldr (fun p m => GMap2.insert m p.1 p.2) .leaf

/-- (Lean-only) `gmap Z V` at the (non-negative) addresses. -/
def zget {V : Type} (m : NMap V) (a : Int) : Option V := m.lookup a.toNat
def zset {V : Type} (m : NMap V) (a : Int) (x : V) : NMap V := m.insert a.toNat x

structure Ast where
  mk ::
  aMem : NMap (Nat × BitVec 8)
  aNw : Nat
  /-- Reversed. -/
  aGmo : List Geid
  /-- Each reversed. -/
  aRows : List (List Lbl)

def rdByte (m : NMap (Nat × BitVec 8)) (a : Int) : Nat × BitVec 8 :=
  (zget m a).getD (0, b0)

def rdBytes (m : NMap (Nat × BitVec 8)) (a : Int) (n : Nat) : List (Nat × BitVec 8) :=
  (List.range n).map fun j => rdByte m (a + (j : Int))

def wrBytes (m : NMap (Nat × BitVec 8)) (a : Int) (n t : Nat) : NMap (Nat × BitVec 8) :=
  (List.range n).foldl (fun m j => zset m (a + (j : Int)) (t, b1)) m

def pushRow (rows : List (List Lbl)) (i : Nat) (l : Lbl) : List (List Lbl) :=
  rows.modify i fun r => l :: r

def doEv (s : Ast) (i : Nat) (pos : Nat) (e : Aev) : Ast :=
  let m := s.aMem
  match e.aeK with
  | KR =>
      let bs := rdBytes m e.aeA e.aeN
      ⟨m, s.aNw, (i, pos) :: s.aGmo,
       pushRow s.aRows i (LLoad false e.aeA (bs.map Prod.fst) (bs.map Prod.snd))⟩
  | KW =>
      let t := s.aNw + 1
      ⟨wrBytes m e.aeA e.aeN t, t, (i, pos) :: s.aGmo,
       pushRow s.aRows i (LStore false e.aeA (List.replicate e.aeN b1) .WCplain)⟩
  | KRmw =>
      let bs := rdBytes m e.aeA e.aeN
      let t := s.aNw + 1
      ⟨wrBytes m e.aeA e.aeN t, t, (i, pos) :: s.aGmo,
       pushRow s.aRows i
         (LRmw true false e.aeA (bs.map Prod.fst) (bs.map Prod.snd) (List.replicate e.aeN b1)
           .WCplain)⟩
  | KF => ⟨m, s.aNw, s.aGmo, pushRow s.aRows i (LFence true true true true)⟩

/-- Round-robin over the harts, `ch` events per turn. -/
def sched : Nat → Nat → Ast → List (Nat × List Aev) → Ast
  | 0, _, s, _ => s
  | fuel + 1, ch, s, rest =>
      if rest.all (fun x => decide (x.2 = [])) then s else
      let r := (imap Prod.mk rest).foldl
        (fun (acc : Ast × List (Nat × List Aev)) (ie : Nat × (Nat × List Aev)) =>
           let (s, r) := acc
           let i := ie.1
           let p := ie.2.1
           let evs := ie.2.2
           let now := evs.take ch
           let s := (imap Prod.mk now).foldl (fun s (je : Nat × Aev) => doEv s i (p + je.1) je.2) s
           (s, r ++ [(p + now.length, evs.drop ch)]))
        (s, [])
      sched fuel ch r.1 r.2

def mkGT (harts : List (List Ti)) : GdexecT :=
  let gs := harts.map gen
  let n := harts.length
  let s0 : Ast := ⟨.leaf, 0, [], List.replicate n []⟩
  let s := sched 100000 16 s0 (gs.map fun g => (0, g.1))
  let deps := (imap (fun i (g : List Aev × List ((Nat × Nat) × Dtag)) =>
    g.2.map fun d => (((i, d.1.1), (i, d.1.2)), d.2)) gs).flatten
  ⟨⟨fun _ => some b0, s.aRows.map List.reverse, s.aGmo.reverse⟩, deps⟩

/-! ### 2.2 Counts -/

def cntIns (tr : List Ti) : Nat := tr.length
def cntCls (c : Nat) (tr : List Ti) : Nat :=
  ((gen tr).1.filter fun e =>
    Nat.beq e.aeCls c && match e.aeK with | KF => false | _ => true).length
def cntKind (k : Akind) (tr : List Ti) : Nat :=
  ((gen tr).1.filter fun e =>
    Nat.beq e.aeCls 0 &&
    match e.aeK, k with
    | KR, KR | KW, KW | KRmw, KRmw | KF, KF => true
    | _, _ => false).length
def cntTag (tg : Dtag) (tr : List Ti) : Nat :=
  ((gen tr).2.filter fun d => decide (d.2 = tg)).length

/-- (instructions, fetch reads, walker reads, data R, data W, RMW, fences, total memory events,
ctrl edges, all edges). -/
def counts (tr : List Ti) : Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat :=
  (cntIns tr, cntCls 1 tr, cntCls 2 tr, cntKind KR tr, cntKind KW tr,
   cntKind KRmw tr, cntKind KF tr,
   cntCls 0 tr + cntCls 1 tr + cntCls 2 tr, cntTag DTctrl tr,
   (gen tr).2.length)

/-! ## 3. The checks -/

def dtagEqb (a b : Dtag) : Bool := decide (a = b)
def geidEqb (a b : Geid) : Bool := Nat.beq a.1 b.1 && Nat.beq a.2 b.2

/-- `Hctrl_closed`, boolean (list membership, `if` for laziness). -/
def ctrlClosedB (GT : GdexecT) : Bool :=
  let G := GT.gtG
  let D := GT.gtDeps
  D.all fun (d : Tdep) =>
    if dtagEqb d.2 DTctrl then
      (gevents G).all fun e =>
        if gpoB G d.1.2 e && glblB G e lbIsW then
          D.any fun (d' : Tdep) => geidEqb d'.1.1 d.1.1 && geidEqb d'.1.2 e && dtagEqb d'.2 DTctrl
        else true
    else true

/-- `gsrc e := {r | ∃ w, (r,w,DTctrl) ∈ deps ∧ (w = e ∨ gpo w e)}`, for every event. -/
def gsrcL (GT : GdexecT) (e : Geid) : List Geid :=
  GT.gtDeps.filterMap fun (d : Tdep) =>
    if dtagEqb d.2 DTctrl && (geidEqb d.1.2 e || gpoB GT.gtG d.1.2 e) then some d.1.1 else none
def gsrcAll (GT : GdexecT) : Nat :=
  (gevents GT.gtG).foldl (fun acc e => acc + (gsrcL GT e).length) 0

/-- The six conjuncts of `catTConsistentB`, separately. -/
def cWf (GT : GdexecT) : Bool := gwfB GT.gtG
def cLv (GT : GdexecT) : Bool := gloadValueB GT.gtG
def cAt (GT : GdexecT) : Bool := gatomB GT.gtG
def cDw (GT : GdexecT) : Bool := gtdepsWfB GT.gtG GT.gtDeps
def cDg (GT : GdexecT) : Bool := gtdepsGmoB GT.gtG GT.gtDeps
def cPpo (GT : GdexecT) : Bool := ppoGmoB (gppoCatB (gtAdGd GT)) GT.gtG

def gsize (GT : GdexecT) : Nat × Nat := (GT.gtG.gxGmo.length, GT.gtDeps.length)

/-- Truncated harts: the first `m` instructions of hart `i`'s trace. -/
def gN (m : Nat) (nh : Nat) : GdexecT :=
  mkGT ((List.range nh).map fun i => (hartTr (if Nat.beq i 1 then 1 else 0) i).take m)

/-! ## 4. Timings -/

/-- The three certificate graphs at full size: (a), (a′), (b). -/
def gA : GdexecT := mkGT [hartTr 0 0, hartTr 1 1]
def gA' : GdexecT := mkGT [hartTr 0 0, hartTr 1 1, hartTr 0 2]
def gB : GdexecT := mkGT [hartTr 0 0, hartTr 1 1, racerTr]

/-- STRICTNESS PROBE: `ppoGmoB` with the pair loop guarded by `if` on same-hart po (sound:
`gppoCat` ⊆ same hart); the inner `gppoCatB` unchanged. -/
def ppoGmoPoB (P : Geid → Geid → Bool) (G : Gexec) : Bool :=
  (gevents G).all fun e1 => (gevents G).all fun e2 =>
    if Nat.beq e1.1 e2.1 then !(P e1 e2) || gmoLtB G e1 e2 else true
def cPpoPo (GT : GdexecT) : Bool := ppoGmoPoB (gppoCatB (gtAdGd GT)) GT.gtG

def g10 : GdexecT := gN 10 2
def g20 : GdexecT := gN 20 2
def g40 : GdexecT := gN 40 2

/-! ## 5. PROTOTYPE indexed checker -- UNVERIFIED, timing only -/

def rdb (l : Lbl) : List ((Int × Nat) × BitVec 8) :=
  match lbRd l with
  | some (b, ts, vs) => imap (fun j (tv : Nat × BitVec 8) => ((accAddr b j, tv.1), tv.2)) (ts.zip vs)
  | none => []
def wrb (l : Lbl) : List (Int × BitVec 8) :=
  match lbWr l with
  | some (b, vs) => imap (fun j v => (accAddr b j, v)) vs
  | none => []

structure Fidx where
  mk ::
  /-- gmo position. -/
  fPos : GMap2 Nat
  /-- Write index, 1-based. -/
  fWix : GMap2 Nat
  /-- Write index → event. -/
  fWev : NMap Geid
  /-- Address → writers. -/
  fWa : NMap (List (Geid × Nat))

def mkIdx (G : Gexec) : Fidx :=
  let ws := G.gxGmo.filter (gisW G)
  let wl := imap (fun n e => (e, n + 1)) ws
  ⟨GMap2.ofList (imap (fun n e => (e, n)) G.gxGmo),
   GMap2.ofList wl,
   NMap.ofList (wl.map fun x => (x.2, x.1)),
   wl.foldl (fun m (x : Geid × Nat) =>
     match gxLbl G x.1 with
     | some l => (wrb l).foldl (fun m (av : Int × BitVec 8) =>
                   zset m av.1 (x :: (zget m av.1).getD [])) m
     | none => m) .leaf⟩

def posLt (I : Fidx) (e1 e2 : Geid) : Bool :=
  match I.fPos.lookup e1, I.fPos.lookup e2 with
  | some a, some b => Nat.blt a b
  | _, _ => false

def between (row : List Lbl) (k1 k2 : Nat) : List Lbl :=
  (row.drop (k1 + 1)).take (k2 - (k1 + 1))

def ppoFast (I : Fidx) (ad : List (Geid × Geid)) (i : Nat) (row : List Lbl)
    (k1 k2 : Nat) (l1 l2 : Lbl) : Bool :=
  if lbIsMem l1 && lbIsMem l2 then
    (if lbIsW l2 then
       (((rdb l1).map fun x => x.1.1) ++ ((wrb l1).map fun x => x.1)).any fun a =>
         (wrb l2).any fun y => decide (a = y.1)
     else false) ||
    (rdb l1).any (fun x => (rdb l2).any fun y =>
       if decide (x.1.1 = y.1.1) then
         !(Nat.beq x.1.2 y.1.2) &&
         (between row k1 k2).all (fun l => !((wrb l).any fun z => decide (z.1 = x.1.1)))
       else false) ||
    (if lbIsRmw l1 then
       match I.fWix.lookup (i, k1) with
       | some w => (rdb l2).any fun y => Nat.beq y.1.2 w
       | none => false
     else false) ||
    (between row k1 k2).any (fun l => match l with
       | LFence pr pw sr sw =>
           ((lbIsR l1 && pr) || (lbIsW l1 && pw)) && ((lbIsR l2 && sr) || (lbIsW l2 && sw))
       | _ => false) ||
    (lbIsR l1 && lbAq l1) || (lbRcsc l1 && lbRcsc l2) ||
    ad.any (fun (rw : Geid × Geid) =>
       if geidEqb rw.1 (i, k1) then
         match I.fWix.lookup rw.2 with
         | some w => (rdb l2).any fun y => Nat.beq y.1.2 w
         | none => false
       else false)
  else false

def ppoGmoFast (GT : GdexecT) : Bool :=
  let G := GT.gtG
  let I := mkIdx G
  let ad := gtAd G GT.gtDeps
  (imap (fun i row =>
    (imap (fun k1 l1 =>
      (imap (fun j l2 =>
        let k2 := k1 + 1 + j
        if ppoFast I ad i row k1 k2 l1 l2 then posLt I (i, k1) (i, k2) else true)
        (row.drop (k1 + 1))).all id) row).all id) G.gxProg).all id

/-- Load-value + atomicity, per read byte against the address's writers. -/
def vis (I : Fidx) (w e : Geid) : Bool :=
  posLt I w e || (Nat.beq w.1 e.1 && Nat.blt w.2 e.2)

def lvAtFast (GT : GdexecT) : Bool :=
  let G := GT.gtG
  let I := mkIdx G
  (imap (fun i row => (imap (fun k l =>
    let e := (i, k)
    (rdb l).all fun x =>
      let ws := (zget I.fWa x.1.1).getD []
      (match x.1.2 with
       | 0 => match G.gxImg x.1.1 with
              | some v => bvEqb v x.2
              | none => false
       | _ + 1 => match I.fWev.lookup x.1.2 with
                  | some w => (match gxLbl G w with
                               | some lw => (wrb lw).any fun y =>
                                   decide (y.1 = x.1.1) && bvEqb y.2 x.2
                               | none => false) && vis I w e
                  | none => false) &&
      ws.all (fun (wn : Geid × Nat) => if vis I wn.1 e then Nat.ble wn.2 x.1.2 else true) &&
      (if lbIsW l then
         match I.fWix.lookup e with
         | some we => ws.all fun (wn : Geid × Nat) => !(Nat.blt x.1.2 wn.2 && Nat.blt wn.2 we)
         | none => false
       else true)) row).all id) G.gxProg).all id

/-- Sanity: both checkers REJECT a reversed gmo. -/
def revGmo (GT : GdexecT) : GdexecT :=
  ⟨⟨GT.gtG.gxImg, GT.gtG.gxProg, GT.gtG.gxGmo.reverse⟩, GT.gtDeps⟩
def g601 : GdexecT := gN 60 1

/-! ## 6. The measurements

Rocq's `Eval vm_compute` / `Time Eval vm_compute` commands are of two kinds here: the values
are pinned by THEOREMS checked by the KERNEL (`decide +kernel`, as `Weak/AxSpinSpikeRun.lean`),
and the full-size prototype runs, too slow for the kernel, are `#eval` (the compiled
evaluator, Rocq's `vm_compute` analogue) through `tm`, which prints the value and its time. -/

/-- (Lean-only) `Time Eval`: evaluate, print the value and the milliseconds. -/
def tm (msg : String) (f : Unit → String) : IO Unit := do
  let t0 ← IO.monoMsNow
  let r := f ()
  IO.println s!"{msg} = {r}"
  let t1 ← IO.monoMsNow
  IO.println s!"  {msg}: {t1 - t0} ms"

set_option synthInstance.maxSize 1024

/-- Rocq `Eval vm_compute in counts (hart_tr 0 0)`. -/
theorem countsHart00 :
    counts (hartTr 0 0) = (464, 499, 33, 98, 34, 1, 1, 665, 1338, 1394) := by decide +kernel
/-- Rocq `Eval vm_compute in counts (hart_tr 1 1)`. -/
theorem countsHart11 :
    counts (hartTr 1 1) = (468, 503, 33, 98, 34, 2, 1, 670, 1365, 1423) := by decide +kernel
/-- Rocq `Eval vm_compute in counts racer_tr`. -/
theorem countsRacer : counts racerTr = (3, 3, 6, 1, 1, 0, 0, 11, 0, 2) := by decide +kernel

/-- Rocq `Time Eval vm_compute in gsize gA` (and `gA'`, `gB`). -/
theorem gsizeGA : gsize gA = (1335, 2817) := by decide +kernel
theorem gsizeGA' : gsize gA' = (2000, 4211) := by decide +kernel
theorem gsizeGB : gsize gB = (1346, 2819) := by decide +kernel

/-- The truncated graphs' sizes (Rocq: in the §4 comment). -/
theorem gsizeSmall :
    (gsize g10, gsize g20, gsize g40, gsize g601) = ((50, 12), (80, 20), (144, 36), (101, 31)) := by
  decide +kernel

/-- Rocq `Time Eval vm_compute in (ppo_gmo_fast g40, c_ppo g10)`. -/
theorem fastG40PpoG10 : (ppoGmoFast g40, cPpo g10) = (true, true) := by decide +kernel

/-- Rocq `Time Eval vm_compute in (gsize g60_1, ppo_gmo_fast g60_1, lv_at_fast g60_1)`. -/
theorem fastG601 : (gsize g601, ppoGmoFast g601, lvAtFast g601) = ((101, 31), true, true) := by
  decide +kernel

/-- Rocq `Time Eval vm_compute in (ppo_gmo_fast (rev_gmo g60_1), lv_at_fast (rev_gmo g60_1))`:
the prototype REJECTS the reversed gmo. -/
theorem fastRevG601 : (ppoGmoFast (revGmo g601), lvAtFast (revGmo g601)) = (false, false) := by
  decide +kernel

/- Full-size prototype ppo runs (recorded, VM, too slow to re-run on every build):
#eval tm "ppoGmoFast gA" ...                          = true, 14.5 s
#eval tm "ppoGmoFast gA'" ...                         = true, 23.5 s
#eval tm "ppoGmoFast gB" ...                          = true, 14.7 s
#eval tm "(ppoGmoFast (revGmo gA), lvAtFast (revGmo gA))" ... = (false, false), 14.7 s
   The shipped checker (recorded): catTConsistentB gA = true, 208 s; see the header. -/

#eval tm "lvAtFast gA" fun _ => toString (lvAtFast gA)
#eval tm "lvAtFast gA'" fun _ => toString (lvAtFast gA')
#eval tm "lvAtFast gB" fun _ => toString (lvAtFast gB)

end AxSpinSpike

end Weak
