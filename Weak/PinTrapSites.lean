/-
Weak: **W9a (B) B2-census — the TRAP-PATH census of the kernel image** (plan
`notes/weak-allocproc-plan.md` rev 51 §C "W9a (B)" (B2-census); spike `notes/W9aB-spike.md`
§§1.2, 5; rulings [OWN.60], [OWN.68]).  Lean-only, no Rocq twin.

Decidable static facts over the tracked image (the SAME decoders as the pin checker:
`KernelPinsDef.kflowOf`, `krole`, `KernelSitesDef.kw`), all `decide +kernel`, no premise.

**The walk.**  A trap path starts at `kernelvec` (`0x800057c0`, the direct-mode `stvec` of every
kernel-mode interrupt; kernel exceptions panic in `kerneltrap`) and is followed until
  * its FIRST COVERING FENCE (`tcov`: a `fence` with R in its predecessor set and W in its
    successor set — riscv.cat ppo rule 4 then orders every po-earlier read before every po-later
    write of the hart, `gfenceCovers`), or
  * `kernelvec`'s `sret` (`kernelvec+0x4c`), or
  * a call to `swtch` (the hart leaves the interrupted thread's context).
Calls are SUMMARISED per function (`TSum`): a call edge's successor is the return point only if
the callee MAY RETURN fence-free (`tsRet`), and it carries `tsSwt` if the callee may reach a
`swtch` call fence-free.  The one indirect call on a trap path, `uartintr+0x5a` (`c.jalr a5`, the
port's rx hook), is resolved to `consoleintr` (`Xv6.uartRxHook`: port 0's hook is
`consoleintr`, port 1's is 0 and the `beqz` before the `jalr` skips it); every other indirect
transfer FAILS the walk.  A trap is NOT an ordering point anywhere below (no fence-like reading of
trap entry, `sret`, CSR accesses or `swtch`).

**What is decided (§3).**
  * `trapTabOk`: every summary of the generated table `trapTab` is CLOSED (its `reach` set holds
    the entry and every successor, no step fails), its flags are exact, and its `free` set (the
    pcs from which a `ret`/`sret` is reachable fence-free) satisfies its defining equation.
  * `trapFreeFunsOk`: the functions entered on a fence-free `kernelvec` → `sret` path
    (`trapFreeFuns`, 12 of them) are closed under the call sites of their free regions.
  * THE THREE FENCE-FREE PATHS (spike §1.2 (a)/(b)/(c)), read off the free regions: no call site
    of `yield`, `wakeup`, `acquire`, `virtio_disk_intr`, `printk` or the rx hook is in a free
    region; the free call sites are exactly `kerneltrap`→`devintr`/`myproc`,
    `devintr`→`plic_claim`/`uartintr`(×2)/`plic_complete`/`clockintr`, `clockintr`→`cpuid`, and the
    helper calls below them (`trapFreeCallSites`).  REFINEMENT of the spike's (b): `uartintr`'s
    free region includes the rx loop with a NULL hook (`uartintr+0x46..+0x58`: port 1's received
    characters are read and dropped), not only "nothing to do".
  * `trapSwtchSites`: the ONLY fence-free `swtch` call is `sched+0x6e` (timer → `yield` →
    `sched`); its hart-side continuation (`swtch`'s body — 14 context stores, `swtchCtx` — then
    `scheduler+0x7a`, the return address `cpus[h].context` holds) has `tsRet = tsSwt = false`:
    every path from the resume point reaches `release+0x16` after two `cpus[h]` stores.  (That
    `swtch` returns there is a RUN fact — `cpus[h].context.ra` is written only by `scheduler`'s own
    `swtch` call — named here, not proved.)
  * THE PRE-FENCE EXIT TABLE (`trapExits`, 163 rows): every store/AMO a trap path can execute
    before its first covering fence, with its class; `frame` (base `sp`) and `amo` are decided
    (`trapExitsClassOk`), the other classes are the generator's annotation (`cpuCell`, `lockCpu`,
    `procField`, `ticks`, `mmio`, `consBuf`, `frameS0`, `frameBuf`, `swtchCtx`).  The FENCE-FREE
    exits (`trapFreeExits`, 51): 47 `sp`-frame spills (`kernelvec`'s 16 + the callee saves), the
    three `push_off`/`pop_off` cpu cells, and `plic_complete`'s MMIO store.
  * The covering fences reached: `release+0x16` (`fence rw,w`) and `virtio_disk_intr+0x2c`
    (`fence iorw,iorw`) — every fenced trap path passes one of them.

**§4 — what the census MEANS (the soundness lemmas the B2-fenced / B2-free parts consume).**
`TRun` is the static control semantics (decoded transfers, calls push their return point, `ret`
pops, the rx hook calls `consoleintr`), FENCE-FREE and `swtch`-FREE by construction.
`trapRunReach`: every state of a `TRun` from `kernelvec`'s entry is in its function's `reach`
set, each frame of its return stack in its caller's; `trapRunFree`: on a `TRun` from `kernelvec`'s
entry to its `sret`, every pc lies in the free region of a `trapFreeFuns` function, so every store
executed is a `trapFreeExits` row.  That a REAL run of the hart follows `TRun` (returns land on
the pushed return point — the frame fact; the hook word is `consoleintr`) is the alignment
premise of the consumers, not proved here.

**§5 — the carry analysis (B2-free's static half).**  Over the 383 walk states of the free
regions (call stacks included), a forward MUST-analysis of which interrupted register each
register and each `sp`-slot (keyed by its offset from the trap's entry `sp`, tracked through the
`addi sp,sp,imm` forms) carries: `flowOk` checks the generated table edge by edge against the
decoded register effect (`xferR`/`xferS`/`xferSp`); `flowEnd`: at the `sret`, `sp` is back at
offset 0 and every register `x1..x31` and every CSR pseudo-register but `stimecmp` (52,
`clockintr` rearms it: `flowStimecmp`) carries its own interrupted value.

Spec (`model/Lean_RV64D/LeanRV64D/Step.lean:331-333`, `SysControl.lean:733-788,852`): a pending
enabled S-interrupt is taken at an instruction boundary BEFORE the fetch, `sepc` ← pc, SPIE ← SIE,
SIE ← 0, pc ← `stvec`; RVWMO/riscv.cat: no ppo rule names trap entry, CSR accesses or `sret`;
Zifencei/PMAs silent.  FAITHFUL: nothing here is a model change.

The table block between the GENERATED markers is emitted by `tools/gen_weak_trapsites.py --emit`
(UNTRUSTED; `--check` re-generates and diffs; the report is its default output).
-/
import Weak.KernelPinsDef

namespace Weak

open MachCSL

namespace PinTrapSites

/-! ## 1. The walk -/

/-- `kernelvec`, the direct-mode `stvec` of kernel-mode traps. -/
def kvPc : Int := (KernelSyms.«kernelvec» : Int)
/-- `kernelvec`'s `sret`. -/
def kvSretPc : Int := kvPc + 0x4c
def swtchPc : Int := (KernelSyms.«swtch» : Int)
/-- `uartintr`'s indirect call of the port's rx hook (`c.jalr a5`). -/
def hookPc : Int := (KernelSyms.«uartintr» : Int) + 0x5a
/-- The hook's only non-null value (`Xv6.uartRxHook .uart0`). -/
def hookTgt : Int := (KernelSyms.«consoleintr» : Int)
/-- `scheduler`'s resume point after its own `swtch` call: the return address `cpus[h].context`
holds when a thread's `sched` switches to it. -/
def resumePc : Int := (KernelSyms.«scheduler» : Int) + 0x7a
/-- The fence-free `swtch` call site (timer → `yield` → `sched`). -/
def schedSwtchPc : Int := (KernelSyms.«sched» : Int) + 0x6e
/-- `release`'s `fence rw,w`. -/
def relFencePc : Int := (KernelSyms.«release» : Int) + 0x16

/-- A COVERING fence: R in the predecessor set, W in the successor set (riscv.cat ppo rule 4
orders a po-earlier read before a po-later write across it). -/
def tcov (w : Nat) : Bool := wIsFence w && wFencePr w && wFenceSw w

/-- One function's fence-free summary. -/
structure TSum where
  TS ::
  tsEnt : Int
  /-- may return to its caller on a fence-free path -/
  tsRet : Bool
  /-- may reach a `swtch` call on a fence-free path -/
  tsSwt : Bool
  /-- the pcs reachable fence-free from the entry (closed under `tstep`'s successors) -/
  tsReach : List Int
  /-- those from which a `ret`/`sret` is reachable fence-free -/
  tsFree : List Int
  deriving Repr

/-- What one step of the walk says. -/
inductive TOut where
  | fenced
  | ret
  | sret
  | swtch
  | fail
  /-- the successors; the flag: the edge's callee may reach `swtch` fence-free -/
  | next (l : List Int) (sw : Bool)
  deriving Repr

def tlook (tab : List TSum) (tgt : Int) : Option TSum := tab.find? (fun f => f.tsEnt == tgt)

def tcall (tab : List TSum) (tgt ra : Int) : TOut :=
  match tlook tab tgt with
  | some f => .next (if f.tsRet then [ra] else []) f.tsSwt
  | none => .fail

/-- Where control goes from a LIVE pc (inside the text, not a covering fence). -/
def tflow (tab : List TSum) (pc : Int) : TOut :=
  match kflowOf pc with
  | .FLnone => .next [pc + wSize (kw pc)] false
  | .FLbranch tgt => .next [pc + wSize (kw pc), tgt] false
  | .FLjump tgt => .next [tgt] false
  | .FLcall tgt => if tgt == swtchPc then .swtch else tcall tab tgt (pc + wSize (kw pc))
  | .FLret => .ret
  | .FLind =>
      if pc == kvSretPc then .sret
      else if pc == hookPc then tcall tab hookTgt (pc + wSize (kw pc))
      else .fail

/-- ONE STEP of the trap walk (header). -/
def tstep (tab : List TSum) (pc : Int) : TOut :=
  if decide (pc < textLo) || decide (textHi ≤ pc) then .fail
  else if tcov (kw pc) then .fenced
  else tflow tab pc

def intMem (x : Int) (l : List Int) : Bool := l.any (fun y => y == x)

def TOut.isRet : TOut → Bool
  | .ret => true
  | _ => false

def TOut.isExit : TOut → Bool
  | .ret | .sret => true
  | _ => false

def TOut.isSwt : TOut → Bool
  | .swtch => true
  | .next _ b => b
  | _ => false

def TOut.isFail : TOut → Bool
  | .fail => true
  | _ => false

def TOut.succs : TOut → List Int
  | .next l _ => l
  | _ => []

/-! ## 2. The checks -/

/-- The callees of a pc, as the walk resolves them (`swtch` excluded: it is a terminal). -/
def tcallees (pc : Int) : List Int :=
  match kflowOf pc with
  | .FLcall tgt => if tgt == swtchPc then [] else [tgt]
  | .FLind => if pc == hookPc then [hookTgt] else []
  | _ => []

/-- A summary is CLOSED, its flags EXACT, its free set a solution of its equation; an entry in
its own free region returns (unless it is `kernelvec`'s, whose exit is the `sret`), and no call
targets `kernelvec`. -/
def sumOkb (tab : List TSum) (f : TSum) : Bool :=
  intMem f.tsEnt f.tsReach &&
  f.tsReach.all (fun pc =>
    !(tstep tab pc).isFail && (tstep tab pc).succs.all (fun q => intMem q f.tsReach)) &&
  (f.tsRet == f.tsReach.any (fun pc => (tstep tab pc).isRet)) &&
  (f.tsSwt == f.tsReach.any (fun pc => (tstep tab pc).isSwt)) &&
  f.tsFree.all (fun pc => intMem pc f.tsReach) &&
  f.tsReach.all (fun pc =>
    intMem pc f.tsFree ==
      ((tstep tab pc).isExit || (tstep tab pc).succs.any (fun q => intMem q f.tsFree))) &&
  (f.tsEnt == kvPc || !intMem f.tsEnt f.tsFree || f.tsRet) &&
  f.tsReach.all (fun pc => (tcallees pc).all (fun g => g != kvPc))

def freeOf (tab : List TSum) (f : Int) : List Int :=
  match tlook tab f with
  | some s => s.tsFree
  | none => []

def reachOf (tab : List TSum) (f : Int) : List Int :=
  match tlook tab f with
  | some s => s.tsReach
  | none => []

/-- The free-called functions are closed under the call sites of their free regions. -/
def freeFunsOkb (tab : List TSum) (ff : List Int) : Bool :=
  intMem kvPc ff &&
  ff.all (fun f => (tlook tab f).isSome &&
    (freeOf tab f).all (fun pc => (tcallees pc).all (fun g => intMem g ff)))

def isStoreb (pc : Int) : Bool := roleIsStore (krole pc)

/-- The census CLASS of a pre-fence exit. -/
inductive TExit where
  /-- a store through `sp`: the hart's own frame (`stackStore`) -/
  | frame
  /-- a store through `s0` (the frame pointer): the function's own frame (`printk`'s va_list) -/
  | frameS0
  /-- a store through a pointer into the function's own frame (`printint`'s digit buffer) -/
  | frameBuf
  /-- an AMO (`acquire`'s `amoswap.w.aq`) -/
  | amo
  /-- a `cpus[h]` cell (`noff`, `intena`, `c->proc`) -/
  | cpuCell
  /-- `lk->cpu` -/
  | lockCpu
  /-- a `struct proc` field (`p->state`, `p->chan`) under its lock -/
  | procField
  /-- `ticks` under `tickslock` -/
  | ticks
  /-- a device register -/
  | mmio
  /-- the console ring's indices under `cons.lock` -/
  | consBuf
  /-- `swtch`'s saves into the old `struct context` -/
  | swtchCtx
  deriving DecidableEq, Repr

/-- The decided classes: `frame` is exactly a `sp`-based store, `amo` exactly an AMO. -/
def exitClassOkb (pc : Int) (c : TExit) : Bool :=
  match c with
  | .frame => stackStore (krole pc)
  | .amo => (match krole pc with | .ORamo _ _ _ => true | _ => false)
  | _ => !stackStore (krole pc) && (match krole pc with | .ORamo _ _ _ => false | _ => true)

def allReach (tab : List TSum) : List Int := tab.flatMap (fun f => f.tsReach)

/-- Strictly increasing (so `List` equality against a filter is order-exact). -/
def sortedb : List Int → Bool
  | x :: y :: l => decide (x < y) && sortedb (y :: l)
  | _ => true

/-- `virtio_disk_intr`'s `fence iorw,iorw` (`__sync_synchronize`). -/
def virtioFencePc : Int := (KernelSyms.«virtio_disk_intr» : Int) + 0x2c

/-- A LIVE pc for the walk: inside the text and not a covering fence. -/
def tliveb (pc : Int) : Bool := !(decide (pc < textLo) || decide (textHi ≤ pc)) && !tcov (kw pc)

/-- A walk/run STATE: the current function (a ghost: the entry of the summary the pc is checked
against), the pc, and the frames (caller's entry, return pc), innermost first. -/
structure TSt where
  TS ::
  tFn : Int
  tPc : Int
  tFr : List (Int × Int)
  deriving DecidableEq, Repr

/-- A carry map: register → the interrupted registers it carries; `sp`-slot (offset from the
trap's entry `sp`) → the same. -/
structure CMap where
  CM ::
  cmR : List (Nat × List Nat)
  cmS : List (Int × List Nat)
  deriving Repr

-- BEGIN GENERATED (tools/gen_weak_trapsites.py --emit)
/-- The per-function fence-free summaries (entry, ret, swt, reach, free). -/
def trapTab : List TSum := [
  ⟨0x8000028c, false, false,
    [0x8000028c, 0x8000028e, 0x80000290, 0x80000292, 0x80000294, 0x80000298, 0x8000029c, 0x8000029e, 0x800002a0, 0x800002ac, 0x800002ae, 0x800002b0],
    []⟩,
  ⟨0x800002c8, false, false,
    [0x800002c8, 0x800002ca, 0x800002cc, 0x800002ce, 0x800002d0, 0x800002d2, 0x800002d4, 0x800002d8, 0x800002dc, 0x800002e0, 0x800002e2, 0x800002e6, 0x800002ea, 0x800002ee, 0x800002f0, 0x800002f4, 0x800002f6, 0x800002fa, 0x800002fe, 0x80000302, 0x80000306, 0x80000308, 0x8000030c, 0x80000310, 0x80000312, 0x80000316, 0x80000318, 0x8000035a, 0x8000035c, 0x8000035e, 0x80000362, 0x80000366, 0x8000036a, 0x8000036e, 0x80000372, 0x80000376, 0x80000378, 0x8000037c, 0x80000380, 0x80000382, 0x80000386, 0x80000388, 0x8000038c, 0x80000390, 0x80000394, 0x80000396, 0x800003ac, 0x800003ae, 0x800003b0, 0x800003b2, 0x800003b4, 0x800003b6, 0x800003b8, 0x800003bc, 0x800003c0, 0x800003c4, 0x800003c8, 0x800003cc, 0x800003d0, 0x800003d4, 0x800003e2, 0x800003e4, 0x800003e8, 0x800003ec, 0x800003f0, 0x800003f6, 0x800003f8],
    []⟩,
  ⟨0x80000478, false, false,
    [0x80000478, 0x8000047a, 0x8000047c, 0x8000047e, 0x80000480, 0x80000482, 0x80000484],
    []⟩,
  ⟨0x80000490, true, false,
    [0x80000490, 0x80000492, 0x80000494, 0x80000496, 0x80000498, 0x8000049a, 0x8000049c, 0x800004a0, 0x800004a2, 0x800004a6, 0x800004a8, 0x800004aa, 0x800004ae, 0x800004b2, 0x800004b4, 0x800004b8, 0x800004ba, 0x800004be, 0x800004c0, 0x800004c4, 0x800004c8, 0x800004ca, 0x800004ce, 0x800004d0, 0x800004d4, 0x800004d8, 0x800004dc, 0x800004e0, 0x800004e4, 0x800004e8, 0x800004ec, 0x800004f0, 0x800004f2, 0x800004f4, 0x800004f8, 0x800004fa, 0x800004fc, 0x800004fe, 0x80000500, 0x80000504, 0x80000508, 0x80000514, 0x80000516, 0x80000518, 0x8000051a, 0x8000051c, 0x8000051e, 0x80000522, 0x80000524],
    [0x80000490, 0x80000492, 0x80000494, 0x80000496, 0x80000498, 0x8000049a, 0x8000049c, 0x800004a0, 0x800004a2, 0x800004a6, 0x800004a8, 0x800004aa, 0x800004ae, 0x800004b2, 0x800004b4, 0x800004b8, 0x800004ba, 0x800004be, 0x800004c0, 0x800004c4, 0x800004c8, 0x800004ca, 0x800004ce, 0x800004d0, 0x800004d4, 0x800004d8, 0x800004dc, 0x800004e0, 0x800004e4, 0x800004e8, 0x800004ec, 0x80000514, 0x80000516, 0x80000518, 0x8000051a, 0x8000051c, 0x8000051e, 0x80000522, 0x80000524]⟩,
  ⟨0x80000526, false, false,
    [0x80000526, 0x80000528, 0x8000052a, 0x8000052c, 0x8000052e, 0x80000530, 0x80000532, 0x80000534, 0x80000536, 0x80000538, 0x8000053a, 0x8000053c, 0x80000540, 0x80000544, 0x80000548, 0x8000054c, 0x80000550, 0x80000554, 0x80000558, 0x8000055c, 0x80000560, 0x80000562, 0x80000564, 0x80000566, 0x80000568, 0x8000056a, 0x8000056c, 0x8000056e, 0x80000570, 0x80000572, 0x80000574, 0x80000578, 0x8000057c, 0x80000580, 0x80000584, 0x80000586, 0x8000058a, 0x8000058c, 0x80000592, 0x80000594, 0x80000596, 0x80000598, 0x8000059c, 0x800005a0, 0x800005a4, 0x800005a8, 0x800005aa, 0x800005ae, 0x800005b2, 0x800005b6, 0x800005ba, 0x800005be, 0x800005c2, 0x800005c6, 0x800005ca, 0x800005ce, 0x800005d0, 0x800005d2, 0x800005d6, 0x800005da, 0x800005de, 0x800005e0, 0x800005e2, 0x800005e4, 0x800005e8, 0x800005ec, 0x800005ee, 0x800005f2, 0x800005f6, 0x800005fa, 0x800005fc, 0x800005fe, 0x80000600, 0x80000604, 0x80000606, 0x80000608, 0x8000060a, 0x8000060e, 0x80000610, 0x80000614, 0x80000618, 0x8000061c, 0x8000061e, 0x80000620, 0x80000622, 0x80000626, 0x8000062a, 0x8000062c, 0x80000630, 0x80000634, 0x80000638, 0x8000063a, 0x8000063c, 0x80000640, 0x80000644, 0x80000646, 0x8000064a, 0x8000064e, 0x80000652, 0x80000654, 0x80000656, 0x80000658, 0x8000065c, 0x80000660, 0x80000662, 0x80000666, 0x8000066a, 0x8000066e, 0x80000670, 0x80000672, 0x80000674, 0x80000678, 0x8000067c, 0x8000067e, 0x80000682, 0x80000686, 0x8000068a, 0x8000068c, 0x8000068e, 0x80000692, 0x80000696, 0x80000698, 0x8000069c, 0x800006a0, 0x800006a4, 0x800006a6, 0x800006a8, 0x800006ac, 0x800006b0, 0x800006b2, 0x800006b6, 0x800006ba, 0x800006be, 0x800006c0, 0x800006c2, 0x800006c4, 0x800006c8, 0x800006cc, 0x800006ce, 0x800006d0, 0x800006d4, 0x800006d8, 0x800006dc, 0x800006e0, 0x800006e4, 0x80000714, 0x80000718, 0x8000071c, 0x80000720, 0x80000722, 0x80000728, 0x8000072c, 0x80000730, 0x80000734, 0x80000738, 0x8000073c, 0x80000740, 0x80000744, 0x80000752, 0x80000756, 0x8000075a, 0x8000075e, 0x80000760, 0x80000762, 0x80000768, 0x8000076a, 0x8000076c, 0x8000076e, 0x80000770, 0x80000772, 0x80000774, 0x80000776, 0x80000778, 0x8000077a, 0x8000077e, 0x80000782, 0x80000792, 0x80000796, 0x8000079a, 0x8000079e, 0x800007a0, 0x800007a2, 0x800007a4, 0x800007a8, 0x800007ac, 0x800007ae, 0x800007b0, 0x800007b4, 0x800007b8, 0x800007ba, 0x800007be, 0x800007c0, 0x800007c4, 0x800007c8, 0x800007cc, 0x800007ce, 0x800007d2, 0x800007d6, 0x800007d8, 0x800007dc, 0x800007e0, 0x800007e4, 0x800007e6, 0x800007ea, 0x800007ee, 0x800007f0, 0x800007f4, 0x800007f8, 0x800007fc, 0x80000800, 0x80000804, 0x80000808, 0x8000080c, 0x80000810, 0x80000814, 0x80000818, 0x80000824, 0x80000826, 0x80000828, 0x8000082a, 0x8000082c, 0x8000082e, 0x80000830, 0x80000832, 0x80000834, 0x80000836],
    []⟩,
  ⟨0x80000860, false, false,
    [0x80000860, 0x80000862, 0x80000864, 0x80000866, 0x80000868, 0x8000086c, 0x80000870],
    []⟩,
  ⟨0x800009ac, false, false,
    [0x800009ac, 0x800009ae, 0x800009b0, 0x800009b2, 0x800009b4, 0x800009b6, 0x800009b8, 0x800009ba, 0x800009bc, 0x800009be, 0x800009c0, 0x800009c2, 0x800009c6, 0x800009ca, 0x800009ce, 0x800009d2, 0x800009d4, 0x800009d6, 0x800009d8, 0x800009da, 0x800009de, 0x800009e0, 0x800009e2, 0x800009e4, 0x800009e8, 0x800009ec, 0x800009f0, 0x800009f4, 0x800009f6, 0x800009fa, 0x800009fe, 0x80000a00],
    []⟩,
  ⟨0x80000a16, true, false,
    [0x80000a16, 0x80000a18, 0x80000a1a, 0x80000a1c, 0x80000a1e, 0x80000a20, 0x80000a22, 0x80000a26, 0x80000a28, 0x80000a2a, 0x80000a2e, 0x80000a32, 0x80000a34, 0x80000a36, 0x80000a3a, 0x80000a3e, 0x80000a42, 0x80000a44, 0x80000a48, 0x80000a4a, 0x80000a4c, 0x80000a50, 0x80000a54, 0x80000a56, 0x80000a58, 0x80000a5c, 0x80000a60, 0x80000a62, 0x80000a64, 0x80000a68, 0x80000a6c, 0x80000a6e, 0x80000a70, 0x80000a74, 0x80000a78, 0x80000a7a, 0x80000a7c, 0x80000a80, 0x80000a84, 0x80000a86, 0x80000a8c, 0x80000a8e, 0x80000a90, 0x80000a92, 0x80000a94],
    [0x80000a16, 0x80000a18, 0x80000a1a, 0x80000a1c, 0x80000a1e, 0x80000a20, 0x80000a22, 0x80000a26, 0x80000a28, 0x80000a2a, 0x80000a2e, 0x80000a32, 0x80000a34, 0x80000a36, 0x80000a3a, 0x80000a3e, 0x80000a42, 0x80000a44, 0x80000a48, 0x80000a4a, 0x80000a4c, 0x80000a50, 0x80000a54, 0x80000a56, 0x80000a58, 0x80000a5c, 0x80000a60, 0x80000a62, 0x80000a64, 0x80000a68, 0x80000a6c, 0x80000a6e, 0x80000a8c, 0x80000a8e, 0x80000a90, 0x80000a92, 0x80000a94]⟩,
  ⟨0x80000bf2, true, false,
    [0x80000bf2, 0x80000bf4, 0x80000bf6, 0x80000bf8, 0x80000bfa, 0x80000bfc, 0x80000bfe, 0x80000c00, 0x80000c02, 0x80000c04, 0x80000c06, 0x80000c08, 0x80000c0c, 0x80000c10, 0x80000c14, 0x80000c16, 0x80000c18, 0x80000c1a, 0x80000c1c],
    [0x80000bf2, 0x80000bf4, 0x80000bf6, 0x80000bf8, 0x80000bfa, 0x80000bfc, 0x80000bfe, 0x80000c00, 0x80000c02, 0x80000c04, 0x80000c06, 0x80000c08, 0x80000c0c, 0x80000c10, 0x80000c14, 0x80000c16, 0x80000c18, 0x80000c1a, 0x80000c1c]⟩,
  ⟨0x80000c1e, true, false,
    [0x80000c1e, 0x80000c20, 0x80000c22, 0x80000c24, 0x80000c26, 0x80000c28, 0x80000c2c, 0x80000c2e, 0x80000c32, 0x80000c34, 0x80000c36, 0x80000c3a, 0x80000c3c, 0x80000c3e, 0x80000c40, 0x80000c42, 0x80000c44, 0x80000c46, 0x80000c48, 0x80000c4a, 0x80000c4e, 0x80000c52, 0x80000c54, 0x80000c56],
    [0x80000c1e, 0x80000c20, 0x80000c22, 0x80000c24, 0x80000c26, 0x80000c28, 0x80000c2c, 0x80000c2e, 0x80000c32, 0x80000c34, 0x80000c36, 0x80000c3a, 0x80000c3c, 0x80000c3e, 0x80000c40, 0x80000c42, 0x80000c44, 0x80000c46, 0x80000c48, 0x80000c4a, 0x80000c4e, 0x80000c52, 0x80000c54, 0x80000c56]⟩,
  ⟨0x80000c58, true, false,
    [0x80000c58, 0x80000c5a, 0x80000c5c, 0x80000c5e, 0x80000c60, 0x80000c62, 0x80000c64, 0x80000c68, 0x80000c6a, 0x80000c6e, 0x80000c70, 0x80000c72, 0x80000c74, 0x80000c78, 0x80000c7a, 0x80000c7c, 0x80000c80, 0x80000c82, 0x80000c84, 0x80000c86, 0x80000c88, 0x80000c8a, 0x80000c8c, 0x80000c90, 0x80000c94],
    [0x80000c58, 0x80000c5a, 0x80000c5c, 0x80000c5e, 0x80000c60, 0x80000c62, 0x80000c64, 0x80000c68, 0x80000c6a, 0x80000c6e, 0x80000c70, 0x80000c72, 0x80000c74, 0x80000c78, 0x80000c7a, 0x80000c7c, 0x80000c80, 0x80000c82, 0x80000c84, 0x80000c86, 0x80000c88, 0x80000c8a]⟩,
  ⟨0x80000c98, true, false,
    [0x80000c98, 0x80000c9a, 0x80000c9c, 0x80000c9e, 0x80000ca0, 0x80000ca4, 0x80000ca8, 0x80000caa, 0x80000cac, 0x80000cae, 0x80000cb2, 0x80000cb4, 0x80000cb6, 0x80000cb8, 0x80000cba, 0x80000cbc, 0x80000cc0, 0x80000cc2, 0x80000cc4, 0x80000cc6, 0x80000cc8, 0x80000ccc, 0x80000cd0, 0x80000cd4, 0x80000cd8, 0x80000cdc],
    [0x80000c98, 0x80000c9a, 0x80000c9c, 0x80000c9e, 0x80000ca0, 0x80000ca4, 0x80000ca8, 0x80000caa, 0x80000cac, 0x80000cae, 0x80000cb2, 0x80000cb4, 0x80000cb6, 0x80000cb8, 0x80000cba, 0x80000cbc, 0x80000cc0, 0x80000cc2, 0x80000cc4, 0x80000cc6]⟩,
  ⟨0x80000ce0, false, false,
    [0x80000ce0, 0x80000ce2, 0x80000ce4, 0x80000ce6, 0x80000ce8, 0x80000cea, 0x80000cec, 0x80000cf0, 0x80000cf2, 0x80000cf6, 0x80000d0c, 0x80000d10, 0x80000d14],
    []⟩,
  ⟨0x80001948, true, false,
    [0x80001948, 0x8000194a, 0x8000194c, 0x8000194e, 0x80001950, 0x80001952, 0x80001954, 0x80001956, 0x80001958, 0x8000195a],
    [0x80001948, 0x8000194a, 0x8000194c, 0x8000194e, 0x80001950, 0x80001952, 0x80001954, 0x80001956, 0x80001958, 0x8000195a]⟩,
  ⟨0x8000195c, true, false,
    [0x8000195c, 0x8000195e, 0x80001960, 0x80001962, 0x80001964, 0x80001966, 0x80001968, 0x8000196a, 0x8000196e, 0x80001972, 0x80001974, 0x80001976, 0x80001978, 0x8000197a],
    [0x8000195c, 0x8000195e, 0x80001960, 0x80001962, 0x80001964, 0x80001966, 0x80001968, 0x8000196a, 0x8000196e, 0x80001972, 0x80001974, 0x80001976, 0x80001978, 0x8000197a]⟩,
  ⟨0x8000197c, true, false,
    [0x8000197c, 0x8000197e, 0x80001980, 0x80001982, 0x80001984, 0x80001986, 0x8000198a, 0x8000198c, 0x8000198e, 0x80001990, 0x80001994, 0x80001998, 0x8000199a, 0x8000199c, 0x8000199e, 0x800019a2, 0x800019a4, 0x800019a6, 0x800019a8, 0x800019aa, 0x800019ac],
    [0x8000197c, 0x8000197e, 0x80001980, 0x80001982, 0x80001984, 0x80001986, 0x8000198a, 0x8000198c, 0x8000198e, 0x80001990, 0x80001994, 0x80001998, 0x8000199a, 0x8000199c, 0x8000199e, 0x800019a2, 0x800019a4, 0x800019a6, 0x800019a8, 0x800019aa, 0x800019ac]⟩,
  ⟨0x80001eb2, false, false,
    [0x80001e86, 0x80001e88, 0x80001eb2, 0x80001eb4, 0x80001eb6, 0x80001eb8, 0x80001eba, 0x80001ebe, 0x80001ec2, 0x80001ec4],
    []⟩,
  ⟨0x80001eec, false, true,
    [0x80001eec, 0x80001eee, 0x80001ef0, 0x80001ef2, 0x80001ef4, 0x80001ef6, 0x80001ef8, 0x80001efa, 0x80001efe, 0x80001f00, 0x80001f04, 0x80001f06, 0x80001f08, 0x80001f0a, 0x80001f0c, 0x80001f10, 0x80001f14, 0x80001f16, 0x80001f1a, 0x80001f1c, 0x80001f20, 0x80001f22, 0x80001f24, 0x80001f28, 0x80001f2c, 0x80001f2e, 0x80001f30, 0x80001f32, 0x80001f36, 0x80001f3a, 0x80001f3c, 0x80001f3e, 0x80001f40, 0x80001f44, 0x80001f46, 0x80001f48, 0x80001f4a, 0x80001f4c, 0x80001f50, 0x80001f54, 0x80001f56, 0x80001f5a, 0x80001f78, 0x80001f7c, 0x80001f80, 0x80001f84, 0x80001f88, 0x80001f8c, 0x80001f90, 0x80001f94, 0x80001f98, 0x80001f9c, 0x80001fa0, 0x80001fa4],
    []⟩,
  ⟨0x80001fa8, false, true,
    [0x80001fa8, 0x80001faa, 0x80001fac, 0x80001fae, 0x80001fb0, 0x80001fb2, 0x80001fb6, 0x80001fb8, 0x80001fbc, 0x80001fbe, 0x80001fc0],
    []⟩,
  ⟨0x80002040, false, false,
    [0x80002040, 0x80002042, 0x80002044, 0x80002046, 0x80002048, 0x8000204a, 0x8000204c, 0x8000204e, 0x80002050, 0x80002052, 0x80002054, 0x80002058, 0x8000205c, 0x8000205e, 0x80002060, 0x80002064, 0x80002068, 0x8000206a, 0x8000206c, 0x80002078, 0x8000207a, 0x8000207e, 0x80002080, 0x80002084, 0x80002088, 0x8000208a, 0x8000208e, 0x80002092],
    []⟩,
  ⟨0x800024b6, true, false,
    [0x800024b6, 0x800024ba, 0x800024be, 0x800024c0, 0x800024c2, 0x800024c6, 0x800024ca, 0x800024ce, 0x800024d2, 0x800024d6, 0x800024da, 0x800024de, 0x800024e2, 0x800024e6, 0x800024ea, 0x800024ee, 0x800024f2, 0x800024f4, 0x800024f6, 0x800024fa, 0x800024fe, 0x80002502, 0x80002506, 0x8000250a, 0x8000250e, 0x80002512, 0x80002516, 0x8000251a, 0x8000251e],
    [0x800024b6, 0x800024ba, 0x800024be, 0x800024c0, 0x800024c2, 0x800024c6, 0x800024ca, 0x800024ce, 0x800024d2, 0x800024d6, 0x800024da, 0x800024de, 0x800024e2, 0x800024e6, 0x800024ea, 0x800024ee, 0x800024f2, 0x800024f4, 0x800024f6, 0x800024fa, 0x800024fe, 0x80002502, 0x80002506, 0x8000250a, 0x8000250e, 0x80002512, 0x80002516, 0x8000251a, 0x8000251e]⟩,
  ⟨0x800025d4, true, false,
    [0x800025d4, 0x800025d6, 0x800025d8, 0x800025da, 0x800025dc, 0x800025e0, 0x800025e2, 0x800025e6, 0x800025ea, 0x800025ee, 0x800025f0, 0x800025f4, 0x800025f6, 0x800025f8, 0x800025fa, 0x800025fc, 0x80002600, 0x80002604, 0x80002608, 0x8000260c, 0x80002610, 0x80002612, 0x80002614, 0x80002616, 0x80002618],
    [0x800025d4, 0x800025d6, 0x800025d8, 0x800025da, 0x800025dc, 0x800025e0, 0x800025e2, 0x800025e6, 0x800025ea, 0x800025ee, 0x800025f0, 0x800025f4, 0x800025f6, 0x800025f8, 0x800025fa]⟩,
  ⟨0x8000262a, true, false,
    [0x8000262a, 0x8000262c, 0x8000262e, 0x80002630, 0x80002632, 0x80002636, 0x80002638, 0x8000263a, 0x8000263c, 0x80002640, 0x80002642, 0x80002644, 0x80002646, 0x80002648, 0x8000264c, 0x8000264e, 0x80002650, 0x80002652, 0x80002654, 0x80002656, 0x8000265a, 0x8000265c, 0x8000265e, 0x80002660, 0x80002664, 0x80002666, 0x8000266a, 0x8000266c, 0x80002670, 0x80002672, 0x80002674, 0x80002676, 0x80002678, 0x8000267a, 0x8000267e, 0x80002680, 0x80002684, 0x80002686, 0x80002688, 0x8000268a, 0x8000268c, 0x80002690, 0x80002692, 0x80002698, 0x8000269a, 0x8000269e, 0x800026a2, 0x800026a8, 0x800026ac, 0x800026ae],
    [0x8000262a, 0x8000262c, 0x8000262e, 0x80002630, 0x80002632, 0x80002636, 0x80002638, 0x8000263a, 0x8000263c, 0x80002640, 0x80002642, 0x80002644, 0x80002646, 0x80002648, 0x8000264c, 0x8000264e, 0x80002650, 0x80002652, 0x80002654, 0x80002656, 0x8000265a, 0x8000265c, 0x8000265e, 0x80002660, 0x80002664, 0x80002666, 0x8000266a, 0x8000266c, 0x80002670, 0x80002672, 0x80002674, 0x80002676, 0x80002678, 0x8000267a, 0x8000267e, 0x80002680, 0x80002684, 0x80002686, 0x80002688, 0x8000268a, 0x8000268c, 0x80002690, 0x800026a8, 0x800026ac, 0x800026ae]⟩,
  ⟨0x800027b8, true, true,
    [0x800027b8, 0x800027ba, 0x800027bc, 0x800027be, 0x800027c0, 0x800027c2, 0x800027c4, 0x800027c6, 0x800027ca, 0x800027ce, 0x800027d2, 0x800027d4, 0x800027d8, 0x800027da, 0x800027de, 0x800027e0, 0x800027e2, 0x800027e6, 0x800027e8, 0x800027ea, 0x800027ee, 0x800027f2, 0x800027f6, 0x800027f8, 0x800027fa, 0x800027fc, 0x800027fe, 0x80002800, 0x80002802, 0x80002804, 0x80002808, 0x8000280c, 0x80002810, 0x80002814, 0x80002818, 0x8000281c, 0x80002820, 0x80002824, 0x80002826, 0x8000282a, 0x8000282e, 0x8000283e, 0x80002842, 0x80002844],
    [0x800027b8, 0x800027ba, 0x800027bc, 0x800027be, 0x800027c0, 0x800027c2, 0x800027c4, 0x800027c6, 0x800027ca, 0x800027ce, 0x800027d2, 0x800027d4, 0x800027d8, 0x800027da, 0x800027de, 0x800027e0, 0x800027e2, 0x800027e6, 0x800027e8, 0x800027ea, 0x800027ee, 0x800027f2, 0x800027f6, 0x800027f8, 0x800027fa, 0x800027fc, 0x800027fe, 0x80002800, 0x80002802, 0x8000283e, 0x80002842]⟩,
  ⟨0x800057c0, false, true,
    [0x800057c0, 0x800057c2, 0x800057c4, 0x800057c6, 0x800057c8, 0x800057ca, 0x800057cc, 0x800057ce, 0x800057d0, 0x800057d2, 0x800057d4, 0x800057d6, 0x800057d8, 0x800057da, 0x800057dc, 0x800057de, 0x800057e0, 0x800057e2, 0x800057e4, 0x800057e8, 0x800057ea, 0x800057ec, 0x800057ee, 0x800057f0, 0x800057f2, 0x800057f4, 0x800057f6, 0x800057f8, 0x800057fa, 0x800057fc, 0x800057fe, 0x80005800, 0x80005802, 0x80005804, 0x80005806, 0x80005808, 0x8000580a, 0x8000580c],
    [0x800057c0, 0x800057c2, 0x800057c4, 0x800057c6, 0x800057c8, 0x800057ca, 0x800057cc, 0x800057ce, 0x800057d0, 0x800057d2, 0x800057d4, 0x800057d6, 0x800057d8, 0x800057da, 0x800057dc, 0x800057de, 0x800057e0, 0x800057e2, 0x800057e4, 0x800057e8, 0x800057ea, 0x800057ec, 0x800057ee, 0x800057f0, 0x800057f2, 0x800057f4, 0x800057f6, 0x800057f8, 0x800057fa, 0x800057fc, 0x800057fe, 0x80005800, 0x80005802, 0x80005804, 0x80005806, 0x80005808, 0x8000580a, 0x8000580c]⟩,
  ⟨0x80005870, true, false,
    [0x80005870, 0x80005872, 0x80005874, 0x80005876, 0x80005878, 0x8000587c, 0x80005880, 0x80005884, 0x80005886, 0x80005888, 0x8000588a, 0x8000588c, 0x8000588e],
    [0x80005870, 0x80005872, 0x80005874, 0x80005876, 0x80005878, 0x8000587c, 0x80005880, 0x80005884, 0x80005886, 0x80005888, 0x8000588a, 0x8000588c, 0x8000588e]⟩,
  ⟨0x80005890, true, false,
    [0x80005890, 0x80005892, 0x80005894, 0x80005896, 0x80005898, 0x8000589a, 0x8000589c, 0x800058a0, 0x800058a4, 0x800058a8, 0x800058aa, 0x800058ac, 0x800058ae, 0x800058b0, 0x800058b2, 0x800058b4],
    [0x80005890, 0x80005892, 0x80005894, 0x80005896, 0x80005898, 0x8000589a, 0x8000589c, 0x800058a0, 0x800058a4, 0x800058a8, 0x800058aa, 0x800058ac, 0x800058ae, 0x800058b0, 0x800058b2, 0x800058b4]⟩,
  ⟨0x80005d28, false, false,
    [0x80005d28, 0x80005d2a, 0x80005d2c, 0x80005d2e, 0x80005d30, 0x80005d32, 0x80005d36, 0x80005d3a, 0x80005d3e, 0x80005d42, 0x80005d46, 0x80005d4a, 0x80005d4c, 0x80005d4e, 0x80005d52, 0x80005d54],
    []⟩
]

/-- The functions entered on a fence-free `kernelvec` → `sret` path. -/
def trapFreeFuns : List Int := [0x80000a16, 0x80000c1e, 0x80000c98, 0x80001948, 0x8000195c, 0x8000197c, 0x800025d4, 0x8000262a, 0x800027b8, 0x800057c0, 0x80005870, 0x80005890]

/-- THE PRE-FENCE EXIT TABLE: every store/AMO on a trap path before its first covering
fence, by class. -/
def trapExits : List (Int × TExit) := [
  (0x8000028e, .frame),
  (0x80000290, .frame),
  (0x800002ca, .frame),
  (0x800002cc, .frame),
  (0x800002ce, .frame),
  (0x8000035a, .frame),
  (0x8000035c, .frame),
  (0x80000390, .consBuf),
  (0x800003e8, .consBuf),
  (0x8000047a, .frame),
  (0x8000047c, .frame),
  (0x80000492, .frame),
  (0x80000494, .frame),
  (0x80000496, .frame),
  (0x800004c4, .frameBuf),
  (0x800004e4, .frameBuf),
  (0x800004f0, .frame),
  (0x80000528, .frame),
  (0x8000052a, .frame),
  (0x8000052c, .frame),
  (0x80000532, .frameS0),
  (0x80000534, .frameS0),
  (0x80000536, .frameS0),
  (0x80000538, .frameS0),
  (0x8000053a, .frameS0),
  (0x8000053c, .frameS0),
  (0x80000540, .frameS0),
  (0x80000554, .frameS0),
  (0x80000560, .frame),
  (0x80000562, .frame),
  (0x80000564, .frame),
  (0x80000566, .frame),
  (0x80000568, .frame),
  (0x8000056a, .frame),
  (0x8000056c, .frame),
  (0x8000056e, .frame),
  (0x80000570, .frame),
  (0x800005da, .frameS0),
  (0x800005f6, .frameS0),
  (0x80000618, .frameS0),
  (0x80000634, .frameS0),
  (0x8000064e, .frameS0),
  (0x8000066a, .frameS0),
  (0x80000686, .frameS0),
  (0x800006a0, .frameS0),
  (0x800006ba, .frameS0),
  (0x800006ce, .frame),
  (0x800006d8, .frameS0),
  (0x8000071c, .frameS0),
  (0x80000730, .frameS0),
  (0x80000862, .frame),
  (0x80000864, .frame),
  (0x8000086c, .mmio),
  (0x800009ae, .frame),
  (0x800009b0, .frame),
  (0x800009b2, .frame),
  (0x800009b4, .frame),
  (0x800009b6, .frame),
  (0x800009b8, .frame),
  (0x800009ba, .frame),
  (0x800009fa, .mmio),
  (0x80000a18, .frame),
  (0x80000a1a, .frame),
  (0x80000a1c, .frame),
  (0x80000bfc, .frame),
  (0x80000bfe, .frame),
  (0x80000c00, .frame),
  (0x80000c20, .frame),
  (0x80000c22, .frame),
  (0x80000c24, .frame),
  (0x80000c3e, .cpuCell),
  (0x80000c54, .cpuCell),
  (0x80000c5a, .frame),
  (0x80000c5c, .frame),
  (0x80000c5e, .frame),
  (0x80000c74, .amo),
  (0x80000c80, .lockCpu),
  (0x80000c9a, .frame),
  (0x80000c9c, .frame),
  (0x80000cb4, .cpuCell),
  (0x80000ce2, .frame),
  (0x80000ce4, .frame),
  (0x80000ce6, .frame),
  (0x80000cf2, .lockCpu),
  (0x8000194a, .frame),
  (0x8000194c, .frame),
  (0x8000195e, .frame),
  (0x80001960, .frame),
  (0x8000197e, .frame),
  (0x80001980, .frame),
  (0x80001982, .frame),
  (0x80001eba, .cpuCell),
  (0x80001ebe, .cpuCell),
  (0x80001eee, .frame),
  (0x80001ef0, .frame),
  (0x80001ef2, .frame),
  (0x80001ef4, .frame),
  (0x80001ef6, .frame),
  (0x80001faa, .frame),
  (0x80001fac, .frame),
  (0x80001fae, .frame),
  (0x80001fbe, .procField),
  (0x80002042, .frame),
  (0x80002044, .frame),
  (0x80002046, .frame),
  (0x80002048, .frame),
  (0x8000204a, .frame),
  (0x8000204c, .frame),
  (0x8000204e, .frame),
  (0x80002084, .procField),
  (0x8000208e, .procField),
  (0x800024b6, .swtchCtx),
  (0x800024ba, .swtchCtx),
  (0x800024be, .swtchCtx),
  (0x800024c0, .swtchCtx),
  (0x800024c2, .swtchCtx),
  (0x800024c6, .swtchCtx),
  (0x800024ca, .swtchCtx),
  (0x800024ce, .swtchCtx),
  (0x800024d2, .swtchCtx),
  (0x800024d6, .swtchCtx),
  (0x800024da, .swtchCtx),
  (0x800024de, .swtchCtx),
  (0x800024e2, .swtchCtx),
  (0x800024e6, .swtchCtx),
  (0x800025d6, .frame),
  (0x800025d8, .frame),
  (0x80002614, .ticks),
  (0x8000262c, .frame),
  (0x8000262e, .frame),
  (0x80002654, .frame),
  (0x800027ba, .frame),
  (0x800027bc, .frame),
  (0x800027be, .frame),
  (0x800027c0, .frame),
  (0x800027c2, .frame),
  (0x800057c2, .frame),
  (0x800057c4, .frame),
  (0x800057c6, .frame),
  (0x800057c8, .frame),
  (0x800057ca, .frame),
  (0x800057cc, .frame),
  (0x800057ce, .frame),
  (0x800057d0, .frame),
  (0x800057d2, .frame),
  (0x800057d4, .frame),
  (0x800057d6, .frame),
  (0x800057d8, .frame),
  (0x800057da, .frame),
  (0x800057dc, .frame),
  (0x800057de, .frame),
  (0x800057e0, .frame),
  (0x800057e2, .frame),
  (0x80005872, .frame),
  (0x80005874, .frame),
  (0x80005892, .frame),
  (0x80005894, .frame),
  (0x80005896, .frame),
  (0x800058aa, .mmio),
  (0x80005d2a, .frame),
  (0x80005d2c, .frame),
  (0x80005d2e, .frame),
  (0x80005d52, .mmio)
]

/-- The exits on the FENCE-FREE paths (the stores of the free region of `trapFreeFuns`). -/
def trapFreeExits : List Int := [0x80000a18, 0x80000a1a, 0x80000a1c, 0x80000c20, 0x80000c22, 0x80000c24, 0x80000c3e, 0x80000c54, 0x80000c9a, 0x80000c9c, 0x80000cb4, 0x8000194a, 0x8000194c, 0x8000195e, 0x80001960, 0x8000197e, 0x80001980, 0x80001982, 0x800025d6, 0x800025d8, 0x8000262c, 0x8000262e, 0x80002654, 0x800027ba, 0x800027bc, 0x800027be, 0x800027c0, 0x800027c2, 0x800057c2, 0x800057c4, 0x800057c6, 0x800057c8, 0x800057ca, 0x800057cc, 0x800057ce, 0x800057d0, 0x800057d2, 0x800057d4, 0x800057d6, 0x800057d8, 0x800057da, 0x800057dc, 0x800057de, 0x800057e0, 0x800057e2, 0x80005872, 0x80005874, 0x80005892, 0x80005894, 0x80005896, 0x800058aa]

/-- A concrete fence-free `kernelvec` → `sret` run after `tStart`: path (a), the spurious
PLIC claim (`devintr` → `plic_claim` → irq = 0 → return 1). -/
def trapWitnessTail : List TSt := [
  ⟨0x800057c0, 0x800057c2, []⟩,
  ⟨0x800057c0, 0x800057c4, []⟩,
  ⟨0x800057c0, 0x800057c6, []⟩,
  ⟨0x800057c0, 0x800057c8, []⟩,
  ⟨0x800057c0, 0x800057ca, []⟩,
  ⟨0x800057c0, 0x800057cc, []⟩,
  ⟨0x800057c0, 0x800057ce, []⟩,
  ⟨0x800057c0, 0x800057d0, []⟩,
  ⟨0x800057c0, 0x800057d2, []⟩,
  ⟨0x800057c0, 0x800057d4, []⟩,
  ⟨0x800057c0, 0x800057d6, []⟩,
  ⟨0x800057c0, 0x800057d8, []⟩,
  ⟨0x800057c0, 0x800057da, []⟩,
  ⟨0x800057c0, 0x800057dc, []⟩,
  ⟨0x800057c0, 0x800057de, []⟩,
  ⟨0x800057c0, 0x800057e0, []⟩,
  ⟨0x800057c0, 0x800057e2, []⟩,
  ⟨0x800057c0, 0x800057e4, []⟩,
  ⟨0x800027b8, 0x800027b8, [(0x800057c0, 0x800057e8)]⟩,
  ⟨0x800027b8, 0x800027ba, [(0x800057c0, 0x800057e8)]⟩,
  ⟨0x800027b8, 0x800027bc, [(0x800057c0, 0x800057e8)]⟩,
  ⟨0x800027b8, 0x800027be, [(0x800057c0, 0x800057e8)]⟩,
  ⟨0x800027b8, 0x800027c0, [(0x800057c0, 0x800057e8)]⟩,
  ⟨0x800027b8, 0x800027c2, [(0x800057c0, 0x800057e8)]⟩,
  ⟨0x800027b8, 0x800027c4, [(0x800057c0, 0x800057e8)]⟩,
  ⟨0x800027b8, 0x800027c6, [(0x800057c0, 0x800057e8)]⟩,
  ⟨0x800027b8, 0x800027ca, [(0x800057c0, 0x800057e8)]⟩,
  ⟨0x800027b8, 0x800027ce, [(0x800057c0, 0x800057e8)]⟩,
  ⟨0x800027b8, 0x800027d2, [(0x800057c0, 0x800057e8)]⟩,
  ⟨0x800027b8, 0x800027d4, [(0x800057c0, 0x800057e8)]⟩,
  ⟨0x800027b8, 0x800027d8, [(0x800057c0, 0x800057e8)]⟩,
  ⟨0x800027b8, 0x800027da, [(0x800057c0, 0x800057e8)]⟩,
  ⟨0x800027b8, 0x800027de, [(0x800057c0, 0x800057e8)]⟩,
  ⟨0x800027b8, 0x800027e0, [(0x800057c0, 0x800057e8)]⟩,
  ⟨0x800027b8, 0x800027e2, [(0x800057c0, 0x800057e8)]⟩,
  ⟨0x8000262a, 0x8000262a, [(0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩,
  ⟨0x8000262a, 0x8000262c, [(0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩,
  ⟨0x8000262a, 0x8000262e, [(0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩,
  ⟨0x8000262a, 0x80002630, [(0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩,
  ⟨0x8000262a, 0x80002632, [(0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩,
  ⟨0x8000262a, 0x80002636, [(0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩,
  ⟨0x8000262a, 0x80002638, [(0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩,
  ⟨0x8000262a, 0x8000263a, [(0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩,
  ⟨0x8000262a, 0x8000263c, [(0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩,
  ⟨0x8000262a, 0x80002654, [(0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩,
  ⟨0x8000262a, 0x80002656, [(0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩,
  ⟨0x80005870, 0x80005870, [(0x8000262a, 0x8000265a), (0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩,
  ⟨0x80005870, 0x80005872, [(0x8000262a, 0x8000265a), (0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩,
  ⟨0x80005870, 0x80005874, [(0x8000262a, 0x8000265a), (0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩,
  ⟨0x80005870, 0x80005876, [(0x8000262a, 0x8000265a), (0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩,
  ⟨0x80005870, 0x80005878, [(0x8000262a, 0x8000265a), (0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩,
  ⟨0x80001948, 0x80001948, [(0x80005870, 0x8000587c), (0x8000262a, 0x8000265a), (0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩,
  ⟨0x80001948, 0x8000194a, [(0x80005870, 0x8000587c), (0x8000262a, 0x8000265a), (0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩,
  ⟨0x80001948, 0x8000194c, [(0x80005870, 0x8000587c), (0x8000262a, 0x8000265a), (0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩,
  ⟨0x80001948, 0x8000194e, [(0x80005870, 0x8000587c), (0x8000262a, 0x8000265a), (0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩,
  ⟨0x80001948, 0x80001950, [(0x80005870, 0x8000587c), (0x8000262a, 0x8000265a), (0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩,
  ⟨0x80001948, 0x80001952, [(0x80005870, 0x8000587c), (0x8000262a, 0x8000265a), (0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩,
  ⟨0x80001948, 0x80001954, [(0x80005870, 0x8000587c), (0x8000262a, 0x8000265a), (0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩,
  ⟨0x80001948, 0x80001956, [(0x80005870, 0x8000587c), (0x8000262a, 0x8000265a), (0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩,
  ⟨0x80001948, 0x80001958, [(0x80005870, 0x8000587c), (0x8000262a, 0x8000265a), (0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩,
  ⟨0x80001948, 0x8000195a, [(0x80005870, 0x8000587c), (0x8000262a, 0x8000265a), (0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩,
  ⟨0x80005870, 0x8000587c, [(0x8000262a, 0x8000265a), (0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩,
  ⟨0x80005870, 0x80005880, [(0x8000262a, 0x8000265a), (0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩,
  ⟨0x80005870, 0x80005884, [(0x8000262a, 0x8000265a), (0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩,
  ⟨0x80005870, 0x80005886, [(0x8000262a, 0x8000265a), (0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩,
  ⟨0x80005870, 0x80005888, [(0x8000262a, 0x8000265a), (0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩,
  ⟨0x80005870, 0x8000588a, [(0x8000262a, 0x8000265a), (0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩,
  ⟨0x80005870, 0x8000588c, [(0x8000262a, 0x8000265a), (0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩,
  ⟨0x80005870, 0x8000588e, [(0x8000262a, 0x8000265a), (0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩,
  ⟨0x8000262a, 0x8000265a, [(0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩,
  ⟨0x8000262a, 0x8000265c, [(0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩,
  ⟨0x8000262a, 0x8000265e, [(0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩,
  ⟨0x8000262a, 0x80002660, [(0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩,
  ⟨0x8000262a, 0x80002664, [(0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩,
  ⟨0x8000262a, 0x80002666, [(0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩,
  ⟨0x8000262a, 0x8000266a, [(0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩,
  ⟨0x8000262a, 0x8000266c, [(0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩,
  ⟨0x8000262a, 0x80002670, [(0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩,
  ⟨0x8000262a, 0x80002672, [(0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩,
  ⟨0x8000262a, 0x80002674, [(0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩,
  ⟨0x8000262a, 0x80002676, [(0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩,
  ⟨0x8000262a, 0x8000264c, [(0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩,
  ⟨0x8000262a, 0x8000264e, [(0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩,
  ⟨0x8000262a, 0x80002650, [(0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩,
  ⟨0x8000262a, 0x80002652, [(0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩,
  ⟨0x800027b8, 0x800027e6, [(0x800057c0, 0x800057e8)]⟩,
  ⟨0x800027b8, 0x800027e8, [(0x800057c0, 0x800057e8)]⟩,
  ⟨0x800027b8, 0x800027ea, [(0x800057c0, 0x800057e8)]⟩,
  ⟨0x800027b8, 0x800027ee, [(0x800057c0, 0x800057e8)]⟩,
  ⟨0x800027b8, 0x800027f2, [(0x800057c0, 0x800057e8)]⟩,
  ⟨0x800027b8, 0x800027f6, [(0x800057c0, 0x800057e8)]⟩,
  ⟨0x800027b8, 0x800027f8, [(0x800057c0, 0x800057e8)]⟩,
  ⟨0x800027b8, 0x800027fa, [(0x800057c0, 0x800057e8)]⟩,
  ⟨0x800027b8, 0x800027fc, [(0x800057c0, 0x800057e8)]⟩,
  ⟨0x800027b8, 0x800027fe, [(0x800057c0, 0x800057e8)]⟩,
  ⟨0x800027b8, 0x80002800, [(0x800057c0, 0x800057e8)]⟩,
  ⟨0x800027b8, 0x80002802, [(0x800057c0, 0x800057e8)]⟩,
  ⟨0x800057c0, 0x800057e8, []⟩,
  ⟨0x800057c0, 0x800057ea, []⟩,
  ⟨0x800057c0, 0x800057ec, []⟩,
  ⟨0x800057c0, 0x800057ee, []⟩,
  ⟨0x800057c0, 0x800057f0, []⟩,
  ⟨0x800057c0, 0x800057f2, []⟩,
  ⟨0x800057c0, 0x800057f4, []⟩,
  ⟨0x800057c0, 0x800057f6, []⟩,
  ⟨0x800057c0, 0x800057f8, []⟩,
  ⟨0x800057c0, 0x800057fa, []⟩,
  ⟨0x800057c0, 0x800057fc, []⟩,
  ⟨0x800057c0, 0x800057fe, []⟩,
  ⟨0x800057c0, 0x80005800, []⟩,
  ⟨0x800057c0, 0x80005802, []⟩,
  ⟨0x800057c0, 0x80005804, []⟩,
  ⟨0x800057c0, 0x80005806, []⟩,
  ⟨0x800057c0, 0x80005808, []⟩,
  ⟨0x800057c0, 0x8000580a, []⟩,
  ⟨0x800057c0, 0x8000580c, []⟩
]

/-- THE CARRY MAPS (B2-free): which interrupted registers each register / `sp`-slot
(offset from the trap's entry `sp`) carries, on EVERY fence-free path. -/
def trapMaps : List CMap := [
  ⟨[(2, [2]), (3, [3]), (4, [4]), (5, [5]), (6, [6]), (7, [7]), (8, [2]), (9, [4]), (11, [11]), (12, [12]), (13, [13]), (14, [4]), (16, [16]), (17, [17]), (18, [33]), (19, [50]), (20, [20]), (21, [21]), (22, [22]), (23, [23]), (24, [24]), (25, [25]), (26, [26]), (27, [27]), (28, [28]), (29, [29]), (30, [30]), (31, [31]), (32, [32]), (33, [33]), (34, [34]), (35, [35]), (36, [36]), (37, [37]), (38, [38]), (39, [39]), (40, [40]), (41, [41]), (42, [42]), (43, [43]), (44, [44]), (45, [45]), (46, [46]), (47, [47]), (48, [48]), (49, [49]), (50, [50]), (51, [51]), (52, [52])],
    [(-368, [2]), (-352, [2]), (-328, [39]), (-320, [2]), (-296, [19]), (-288, [18]), (-280, [9]), (-272, [8]), (-256, [1]), (-240, [3]), (-224, [5]), (-216, [6]), (-208, [7]), (-184, [10]), (-176, [11]), (-168, [12]), (-160, [13]), (-152, [14]), (-144, [15]), (-136, [16]), (-128, [17]), (-40, [28]), (-32, [29]), (-24, [30]), (-16, [31])]⟩,
  ⟨[(2, [2]), (3, [3]), (4, [4]), (5, [5]), (6, [6]), (7, [7]), (8, [2]), (9, [4]), (11, [11]), (12, [12]), (13, [13]), (14, [4]), (16, [16]), (17, [17]), (18, [33]), (19, [50]), (20, [20]), (21, [21]), (22, [22]), (23, [23]), (24, [24]), (25, [25]), (26, [26]), (27, [27]), (28, [28]), (29, [29]), (30, [30]), (31, [31]), (32, [32]), (33, [33]), (34, [34]), (35, [35]), (36, [36]), (37, [37]), (38, [38]), (39, [39]), (40, [40]), (41, [41]), (42, [42]), (43, [43]), (44, [44]), (45, [45]), (46, [46]), (47, [47]), (48, [48]), (49, [49]), (50, [50]), (51, [51]), (52, [52])],
    [(-368, [2]), (-360, [4]), (-352, [2]), (-328, [39]), (-320, [2]), (-296, [19]), (-288, [18]), (-280, [9]), (-272, [8]), (-256, [1]), (-240, [3]), (-224, [5]), (-216, [6]), (-208, [7]), (-184, [10]), (-176, [11]), (-168, [12]), (-160, [13]), (-152, [14]), (-144, [15]), (-136, [16]), (-128, [17]), (-40, [28]), (-32, [29]), (-24, [30]), (-16, [31])]⟩,
  ⟨[(2, [2]), (3, [3]), (4, [4]), (5, [5]), (6, [6]), (7, [7]), (8, [2]), (11, [11]), (12, [12]), (13, [13]), (14, [4]), (16, [16]), (17, [17]), (18, [33]), (19, [50]), (20, [20]), (21, [21]), (22, [22]), (23, [23]), (24, [24]), (25, [25]), (26, [26]), (27, [27]), (28, [28]), (29, [29]), (30, [30]), (31, [31]), (32, [32]), (33, [33]), (34, [34]), (35, [35]), (36, [36]), (37, [37]), (38, [38]), (39, [39]), (40, [40]), (41, [41]), (42, [42]), (43, [43]), (44, [44]), (45, [45]), (46, [46]), (47, [47]), (48, [48]), (49, [49]), (50, [50]), (51, [51]), (52, [52])],
    [(-368, [2]), (-360, [4]), (-352, [2]), (-328, [39]), (-320, [2]), (-296, [19]), (-288, [18]), (-280, [9]), (-272, [8]), (-256, [1]), (-240, [3]), (-224, [5]), (-216, [6]), (-208, [7]), (-184, [10]), (-176, [11]), (-168, [12]), (-160, [13]), (-152, [14]), (-144, [15]), (-136, [16]), (-128, [17]), (-40, [28]), (-32, [29]), (-24, [30]), (-16, [31])]⟩,
  ⟨[(2, [2]), (3, [3]), (4, [4]), (5, [5]), (6, [6]), (7, [7]), (8, [2]), (11, [11]), (12, [12]), (13, [13]), (16, [16]), (17, [17]), (18, [33]), (19, [50]), (20, [20]), (21, [21]), (22, [22]), (23, [23]), (24, [24]), (25, [25]), (26, [26]), (27, [27]), (28, [28]), (29, [29]), (30, [30]), (31, [31]), (32, [32]), (33, [33]), (34, [34]), (35, [35]), (36, [36]), (37, [37]), (38, [38]), (39, [39]), (40, [40]), (41, [41]), (42, [42]), (43, [43]), (44, [44]), (45, [45]), (46, [46]), (47, [47]), (48, [48]), (49, [49]), (50, [50]), (51, [51]), (52, [52])],
    [(-368, [2]), (-360, [4]), (-352, [2]), (-328, [39]), (-320, [2]), (-296, [19]), (-288, [18]), (-280, [9]), (-272, [8]), (-256, [1]), (-240, [3]), (-224, [5]), (-216, [6]), (-208, [7]), (-184, [10]), (-176, [11]), (-168, [12]), (-160, [13]), (-152, [14]), (-144, [15]), (-136, [16]), (-128, [17]), (-40, [28]), (-32, [29]), (-24, [30]), (-16, [31])]⟩,
  ⟨[(2, [2]), (3, [3]), (4, [4]), (5, [5]), (6, [6]), (7, [7]), (8, [2]), (11, [11]), (12, [12]), (16, [16]), (17, [17]), (18, [33]), (19, [50]), (20, [20]), (21, [21]), (22, [22]), (23, [23]), (24, [24]), (25, [25]), (26, [26]), (27, [27]), (28, [28]), (29, [29]), (30, [30]), (31, [31]), (32, [32]), (33, [33]), (34, [34]), (35, [35]), (36, [36]), (37, [37]), (38, [38]), (39, [39]), (40, [40]), (41, [41]), (42, [42]), (43, [43]), (44, [44]), (45, [45]), (46, [46]), (47, [47]), (48, [48]), (49, [49]), (50, [50]), (51, [51]), (52, [52])],
    [(-368, [2]), (-360, [4]), (-352, [2]), (-328, [39]), (-320, [2]), (-296, [19]), (-288, [18]), (-280, [9]), (-272, [8]), (-256, [1]), (-240, [3]), (-224, [5]), (-216, [6]), (-208, [7]), (-184, [10]), (-176, [11]), (-168, [12]), (-160, [13]), (-152, [14]), (-144, [15]), (-136, [16]), (-128, [17]), (-40, [28]), (-32, [29]), (-24, [30]), (-16, [31])]⟩,
  ⟨[(1, [2]), (2, [2]), (3, [3]), (4, [4]), (5, [5]), (6, [6]), (7, [7]), (8, [2]), (11, [11]), (12, [12]), (16, [16]), (17, [17]), (18, [33]), (19, [50]), (20, [20]), (21, [21]), (22, [22]), (23, [23]), (24, [24]), (25, [25]), (26, [26]), (27, [27]), (28, [28]), (29, [29]), (30, [30]), (31, [31]), (32, [32]), (33, [33]), (34, [34]), (35, [35]), (36, [36]), (37, [37]), (38, [38]), (39, [39]), (40, [40]), (41, [41]), (42, [42]), (43, [43]), (44, [44]), (45, [45]), (46, [46]), (47, [47]), (48, [48]), (49, [49]), (50, [50]), (51, [51]), (52, [52])],
    [(-368, [2]), (-360, [4]), (-352, [2]), (-328, [39]), (-320, [2]), (-296, [19]), (-288, [18]), (-280, [9]), (-272, [8]), (-256, [1]), (-240, [3]), (-224, [5]), (-216, [6]), (-208, [7]), (-184, [10]), (-176, [11]), (-168, [12]), (-160, [13]), (-152, [14]), (-144, [15]), (-136, [16]), (-128, [17]), (-40, [28]), (-32, [29]), (-24, [30]), (-16, [31])]⟩,
  ⟨[(1, [2]), (2, [2]), (3, [3]), (4, [4]), (5, [5]), (6, [6]), (7, [7]), (8, [2]), (9, [2, 4]), (11, [11]), (12, [12]), (16, [16]), (17, [17]), (18, [33]), (19, [50]), (20, [20]), (21, [21]), (22, [22]), (23, [23]), (24, [24]), (25, [25]), (26, [26]), (27, [27]), (28, [28]), (29, [29]), (30, [30]), (31, [31]), (32, [32]), (33, [33]), (34, [34]), (35, [35]), (36, [36]), (37, [37]), (38, [38]), (39, [39]), (40, [40]), (41, [41]), (42, [42]), (43, [43]), (44, [44]), (45, [45]), (46, [46]), (47, [47]), (48, [48]), (49, [49]), (50, [50]), (51, [51]), (52, [52])],
    [(-368, [2]), (-360, [4]), (-352, [2]), (-328, [39]), (-320, [2]), (-296, [19]), (-288, [18]), (-280, [9]), (-272, [8]), (-256, [1]), (-240, [3]), (-224, [5]), (-216, [6]), (-208, [7]), (-184, [10]), (-176, [11]), (-168, [12]), (-160, [13]), (-152, [14]), (-144, [15]), (-136, [16]), (-128, [17]), (-40, [28]), (-32, [29]), (-24, [30]), (-16, [31])]⟩,
  ⟨[(2, [2]), (3, [3]), (4, [4]), (5, [5]), (6, [6]), (7, [7]), (8, [2]), (9, [39]), (11, [11]), (12, [12]), (16, [16]), (17, [17]), (18, [33]), (19, [50]), (20, [20]), (21, [21]), (22, [22]), (23, [23]), (24, [24]), (25, [25]), (26, [26]), (27, [27]), (28, [28]), (29, [29]), (30, [30]), (31, [31]), (32, [32]), (33, [33]), (34, [34]), (35, [35]), (36, [36]), (37, [37]), (38, [38]), (39, [39]), (40, [40]), (41, [41]), (42, [42]), (43, [43]), (44, [44]), (45, [45]), (46, [46]), (47, [47]), (48, [48]), (49, [49]), (50, [50]), (51, [51])],
    [(-328, [39]), (-320, [2]), (-296, [19]), (-288, [18]), (-280, [9]), (-272, [8]), (-256, [1]), (-240, [3]), (-224, [5]), (-216, [6]), (-208, [7]), (-184, [10]), (-176, [11]), (-168, [12]), (-160, [13]), (-152, [14]), (-144, [15]), (-136, [16]), (-128, [17]), (-40, [28]), (-32, [29]), (-24, [30]), (-16, [31])]⟩,
  ⟨[(2, [2]), (3, [3]), (4, [4]), (5, [5]), (6, [6]), (7, [7]), (8, [2]), (9, [39]), (11, [11]), (12, [12]), (16, [16]), (17, [17]), (18, [33]), (19, [50]), (20, [20]), (21, [21]), (22, [22]), (23, [23]), (24, [24]), (25, [25]), (26, [26]), (27, [27]), (28, [28]), (29, [29]), (30, [30]), (31, [31]), (32, [32]), (33, [33]), (34, [34]), (35, [35]), (36, [36]), (37, [37]), (38, [38]), (39, [39]), (40, [40]), (41, [41]), (42, [42]), (43, [43]), (44, [44]), (45, [45]), (46, [46]), (47, [47]), (48, [48]), (49, [49]), (50, [50]), (51, [51])],
    [(-352, [2]), (-328, [39]), (-320, [2]), (-296, [19]), (-288, [18]), (-280, [9]), (-272, [8]), (-256, [1]), (-240, [3]), (-224, [5]), (-216, [6]), (-208, [7]), (-184, [10]), (-176, [11]), (-168, [12]), (-160, [13]), (-152, [14]), (-144, [15]), (-136, [16]), (-128, [17]), (-40, [28]), (-32, [29]), (-24, [30]), (-16, [31])]⟩,
  ⟨[(2, [2]), (3, [3]), (4, [4]), (5, [5]), (6, [6]), (7, [7]), (8, [2]), (9, [39]), (11, [11]), (12, [12]), (16, [16]), (17, [17]), (18, [33]), (19, [50]), (20, [20]), (21, [21]), (22, [22]), (23, [23]), (24, [24]), (25, [25]), (26, [26]), (27, [27]), (28, [28]), (29, [29]), (30, [30]), (31, [31]), (32, [32]), (33, [33]), (34, [34]), (35, [35]), (36, [36]), (37, [37]), (38, [38]), (39, [39]), (40, [40]), (41, [41]), (42, [42]), (43, [43]), (44, [44]), (45, [45]), (46, [46]), (47, [47]), (48, [48]), (49, [49]), (50, [50]), (51, [51])],
    [(-360, [39]), (-352, [2]), (-328, [39]), (-320, [2]), (-296, [19]), (-288, [18]), (-280, [9]), (-272, [8]), (-256, [1]), (-240, [3]), (-224, [5]), (-216, [6]), (-208, [7]), (-184, [10]), (-176, [11]), (-168, [12]), (-160, [13]), (-152, [14]), (-144, [15]), (-136, [16]), (-128, [17]), (-40, [28]), (-32, [29]), (-24, [30]), (-16, [31])]⟩,
  ⟨[(2, [2]), (3, [3]), (4, [4]), (5, [5]), (6, [6]), (7, [7]), (8, [2]), (9, [39]), (11, [11]), (12, [12]), (15, [39]), (16, [16]), (17, [17]), (18, [33]), (19, [50]), (20, [20]), (21, [21]), (22, [22]), (23, [23]), (24, [24]), (25, [25]), (26, [26]), (27, [27]), (28, [28]), (29, [29]), (30, [30]), (31, [31]), (32, [32]), (33, [33]), (34, [34]), (35, [35]), (36, [36]), (37, [37]), (38, [38]), (39, [39]), (40, [40]), (41, [41]), (42, [42]), (43, [43]), (44, [44]), (45, [45]), (46, [46]), (47, [47]), (48, [48]), (49, [49]), (50, [50]), (51, [51])],
    [(-360, [39]), (-352, [2]), (-328, [39]), (-320, [2]), (-296, [19]), (-288, [18]), (-280, [9]), (-272, [8]), (-256, [1]), (-240, [3]), (-224, [5]), (-216, [6]), (-208, [7]), (-184, [10]), (-176, [11]), (-168, [12]), (-160, [13]), (-152, [14]), (-144, [15]), (-136, [16]), (-128, [17]), (-40, [28]), (-32, [29]), (-24, [30]), (-16, [31])]⟩,
  ⟨[(1, [2]), (2, [2]), (3, [3]), (4, [4]), (5, [5]), (6, [6]), (7, [7]), (8, [2]), (9, [39]), (10, [4]), (11, [11]), (12, [12]), (15, [4]), (16, [16]), (17, [17]), (18, [33]), (19, [50]), (20, [20]), (21, [21]), (22, [22]), (23, [23]), (24, [24]), (25, [25]), (26, [26]), (27, [27]), (28, [28]), (29, [29]), (30, [30]), (31, [31]), (32, [32]), (33, [33]), (34, [34]), (35, [35]), (36, [36]), (37, [37]), (38, [38]), (39, [39]), (40, [40]), (41, [41]), (42, [42]), (43, [43]), (44, [44]), (45, [45]), (46, [46]), (47, [47]), (48, [48]), (49, [49]), (50, [50]), (51, [51])],
    [(-384, [2]), (-360, [39]), (-352, [2]), (-328, [39]), (-320, [2]), (-296, [19]), (-288, [18]), (-280, [9]), (-272, [8]), (-256, [1]), (-240, [3]), (-224, [5]), (-216, [6]), (-208, [7]), (-184, [10]), (-176, [11]), (-168, [12]), (-160, [13]), (-152, [14]), (-144, [15]), (-136, [16]), (-128, [17]), (-40, [28]), (-32, [29]), (-24, [30]), (-16, [31])]⟩,
  ⟨[(1, [2]), (2, [2]), (3, [3]), (4, [4]), (5, [5]), (6, [6]), (7, [7]), (8, [2]), (9, [39]), (10, [4]), (11, [11]), (12, [12]), (16, [16]), (17, [17]), (18, [33]), (19, [50]), (20, [20]), (21, [21]), (22, [22]), (23, [23]), (24, [24]), (25, [25]), (26, [26]), (27, [27]), (28, [28]), (29, [29]), (30, [30]), (31, [31]), (32, [32]), (33, [33]), (34, [34]), (35, [35]), (36, [36]), (37, [37]), (38, [38]), (39, [39]), (40, [40]), (41, [41]), (42, [42]), (43, [43]), (44, [44]), (45, [45]), (46, [46]), (47, [47]), (48, [48]), (49, [49]), (50, [50]), (51, [51])],
    [(-384, [2]), (-360, [39]), (-352, [2]), (-328, [39]), (-320, [2]), (-296, [19]), (-288, [18]), (-280, [9]), (-272, [8]), (-256, [1]), (-240, [3]), (-224, [5]), (-216, [6]), (-208, [7]), (-184, [10]), (-176, [11]), (-168, [12]), (-160, [13]), (-152, [14]), (-144, [15]), (-136, [16]), (-128, [17]), (-40, [28]), (-32, [29]), (-24, [30]), (-16, [31])]⟩,
  ⟨[(1, [2]), (2, [2]), (3, [3]), (4, [4]), (5, [5]), (6, [6]), (7, [7]), (8, [2]), (9, [2, 39]), (10, [4]), (11, [11]), (12, [12]), (15, [4]), (16, [16]), (17, [17]), (18, [33]), (19, [50]), (20, [20]), (21, [21]), (22, [22]), (23, [23]), (24, [24]), (25, [25]), (26, [26]), (27, [27]), (28, [28]), (29, [29]), (30, [30]), (31, [31]), (32, [32]), (33, [33]), (34, [34]), (35, [35]), (36, [36]), (37, [37]), (38, [38]), (39, [39]), (40, [40]), (41, [41]), (42, [42]), (43, [43]), (44, [44]), (45, [45]), (46, [46]), (47, [47]), (48, [48]), (49, [49]), (50, [50]), (51, [51])],
    [(-384, [2]), (-360, [39]), (-352, [2]), (-328, [39]), (-320, [2]), (-296, [19]), (-288, [18]), (-280, [9]), (-272, [8]), (-256, [1]), (-240, [3]), (-224, [5]), (-216, [6]), (-208, [7]), (-184, [10]), (-176, [11]), (-168, [12]), (-160, [13]), (-152, [14]), (-144, [15]), (-136, [16]), (-128, [17]), (-40, [28]), (-32, [29]), (-24, [30]), (-16, [31])]⟩,
  ⟨[(1, [2]), (2, [2]), (3, [3]), (4, [4]), (5, [5]), (6, [6]), (7, [7]), (8, [2]), (9, [39]), (10, [4]), (11, [11]), (12, [12]), (15, [39]), (16, [16]), (17, [17]), (18, [33]), (19, [50]), (20, [20]), (21, [21]), (22, [22]), (23, [23]), (24, [24]), (25, [25]), (26, [26]), (27, [27]), (28, [28]), (29, [29]), (30, [30]), (31, [31]), (32, [32]), (33, [33]), (34, [34]), (35, [35]), (36, [36]), (37, [37]), (38, [38]), (39, [39]), (40, [40]), (41, [41]), (42, [42]), (43, [43]), (44, [44]), (45, [45]), (46, [46]), (47, [47]), (48, [48]), (49, [49]), (50, [50]), (51, [51])],
    [(-384, [2]), (-360, [39]), (-352, [2]), (-328, [39]), (-320, [2]), (-296, [19]), (-288, [18]), (-280, [9]), (-272, [8]), (-256, [1]), (-240, [3]), (-224, [5]), (-216, [6]), (-208, [7]), (-184, [10]), (-176, [11]), (-168, [12]), (-160, [13]), (-152, [14]), (-144, [15]), (-136, [16]), (-128, [17]), (-40, [28]), (-32, [29]), (-24, [30]), (-16, [31])]⟩,
  ⟨[(2, [2]), (3, [3]), (4, [4]), (5, [5]), (6, [6]), (7, [7]), (8, [2]), (9, [4]), (10, [4]), (11, [11]), (12, [12]), (15, [4]), (16, [16]), (17, [17]), (18, [33]), (19, [50]), (20, [20]), (21, [21]), (22, [22]), (23, [23]), (24, [24]), (25, [25]), (26, [26]), (27, [27]), (28, [28]), (29, [29]), (30, [30]), (31, [31]), (32, [32]), (33, [33]), (34, [34]), (35, [35]), (36, [36]), (37, [37]), (38, [38]), (39, [39]), (40, [40]), (41, [41]), (42, [42]), (43, [43]), (44, [44]), (45, [45]), (46, [46]), (47, [47]), (48, [48]), (49, [49]), (50, [50]), (51, [51])],
    [(-384, [2]), (-360, [39]), (-352, [2]), (-328, [39]), (-320, [2]), (-296, [19]), (-288, [18]), (-280, [9]), (-272, [8]), (-256, [1]), (-240, [3]), (-224, [5]), (-216, [6]), (-208, [7]), (-184, [10]), (-176, [11]), (-168, [12]), (-160, [13]), (-152, [14]), (-144, [15]), (-136, [16]), (-128, [17]), (-40, [28]), (-32, [29]), (-24, [30]), (-16, [31])]⟩,
  ⟨[(1, [2]), (2, [2]), (3, [3]), (4, [4]), (5, [5]), (6, [6]), (7, [7]), (8, [2]), (9, [4]), (10, [4]), (11, [11]), (12, [12]), (15, [4]), (16, [16]), (17, [17]), (18, [33]), (19, [50]), (20, [20]), (21, [21]), (22, [22]), (23, [23]), (24, [24]), (25, [25]), (26, [26]), (27, [27]), (28, [28]), (29, [29]), (30, [30]), (31, [31]), (32, [32]), (33, [33]), (34, [34]), (35, [35]), (36, [36]), (37, [37]), (38, [38]), (39, [39]), (40, [40]), (41, [41]), (42, [42]), (43, [43]), (44, [44]), (45, [45]), (46, [46]), (47, [47]), (48, [48]), (49, [49]), (50, [50]), (51, [51])],
    [(-384, [2]), (-368, [2]), (-352, [2]), (-328, [39]), (-320, [2]), (-296, [19]), (-288, [18]), (-280, [9]), (-272, [8]), (-256, [1]), (-240, [3]), (-224, [5]), (-216, [6]), (-208, [7]), (-184, [10]), (-176, [11]), (-168, [12]), (-160, [13]), (-152, [14]), (-144, [15]), (-136, [16]), (-128, [17]), (-40, [28]), (-32, [29]), (-24, [30]), (-16, [31])]⟩,
  ⟨[(1, [2]), (2, [2]), (3, [3]), (4, [4]), (5, [5]), (6, [6]), (7, [7]), (8, [2]), (9, [4]), (10, [4]), (11, [11]), (12, [12]), (15, [39]), (16, [16]), (17, [17]), (18, [33]), (19, [50]), (20, [20]), (21, [21]), (22, [22]), (23, [23]), (24, [24]), (25, [25]), (26, [26]), (27, [27]), (28, [28]), (29, [29]), (30, [30]), (31, [31]), (32, [32]), (33, [33]), (34, [34]), (35, [35]), (36, [36]), (37, [37]), (38, [38]), (39, [39]), (40, [40]), (41, [41]), (42, [42]), (43, [43]), (44, [44]), (45, [45]), (46, [46]), (47, [47]), (48, [48]), (49, [49]), (50, [50]), (51, [51])],
    [(-384, [2]), (-368, [2]), (-352, [2]), (-328, [39]), (-320, [2]), (-296, [19]), (-288, [18]), (-280, [9]), (-272, [8]), (-256, [1]), (-240, [3]), (-224, [5]), (-216, [6]), (-208, [7]), (-184, [10]), (-176, [11]), (-168, [12]), (-160, [13]), (-152, [14]), (-144, [15]), (-136, [16]), (-128, [17]), (-40, [28]), (-32, [29]), (-24, [30]), (-16, [31])]⟩,
  ⟨[(2, [2]), (3, [3]), (4, [4]), (5, [5]), (6, [6]), (7, [7]), (8, [2]), (9, [39]), (11, [11]), (12, [12]), (13, [13]), (14, [50]), (16, [16]), (17, [17]), (18, [33]), (19, [50]), (20, [20]), (21, [21]), (22, [22]), (23, [23]), (24, [24]), (25, [25]), (26, [26]), (27, [27]), (28, [28]), (29, [29]), (30, [30]), (31, [31]), (32, [32]), (33, [33]), (34, [34]), (35, [35]), (36, [36]), (37, [37]), (38, [38]), (39, [39]), (40, [40]), (41, [41]), (42, [42]), (43, [43]), (44, [44]), (45, [45]), (46, [46]), (47, [47]), (48, [48]), (49, [49]), (50, [50]), (51, [51]), (52, [52])],
    [(-352, [2]), (-320, [2]), (-296, [19]), (-288, [18]), (-280, [9]), (-272, [8]), (-256, [1]), (-240, [3]), (-224, [5]), (-216, [6]), (-208, [7]), (-184, [10]), (-176, [11]), (-168, [12]), (-160, [13]), (-152, [14]), (-144, [15]), (-136, [16]), (-128, [17]), (-40, [28]), (-32, [29]), (-24, [30]), (-16, [31])]⟩,
  ⟨[(2, [2]), (3, [3]), (4, [4]), (5, [5]), (6, [6]), (7, [7]), (8, [2]), (9, [39]), (10, [10]), (11, [11]), (12, [12]), (13, [13]), (14, [50]), (16, [16]), (17, [17]), (18, [33]), (19, [50]), (20, [20]), (21, [21]), (22, [22]), (23, [23]), (24, [24]), (25, [25]), (26, [26]), (27, [27]), (28, [28]), (29, [29]), (30, [30]), (31, [31]), (32, [32]), (33, [33]), (34, [34]), (35, [35]), (36, [36]), (37, [37]), (38, [38]), (39, [39]), (40, [40]), (41, [41]), (42, [42]), (43, [43]), (44, [44]), (45, [45]), (46, [46]), (47, [47]), (48, [48]), (49, [49]), (50, [50]), (51, [51]), (52, [52])],
    [(-352, [2]), (-328, [39]), (-320, [2]), (-296, [19]), (-288, [18]), (-280, [9]), (-272, [8]), (-256, [1]), (-240, [3]), (-224, [5]), (-216, [6]), (-208, [7]), (-184, [10]), (-176, [11]), (-168, [12]), (-160, [13]), (-152, [14]), (-144, [15]), (-136, [16]), (-128, [17]), (-40, [28]), (-32, [29]), (-24, [30]), (-16, [31])]⟩,
  ⟨[(2, [2]), (3, [3]), (4, [4]), (5, [5]), (6, [6]), (7, [7]), (8, [2]), (9, [2, 4]), (10, [2, 4]), (11, [11]), (12, [12]), (16, [16]), (17, [17]), (18, [33]), (19, [50]), (20, [20]), (21, [21]), (22, [22]), (23, [23]), (24, [24]), (25, [25]), (26, [26]), (27, [27]), (28, [28]), (29, [29]), (30, [30]), (31, [31]), (32, [32]), (33, [33]), (34, [34]), (35, [35]), (36, [36]), (37, [37]), (38, [38]), (39, [39]), (40, [40]), (41, [41]), (42, [42]), (43, [43]), (44, [44]), (45, [45]), (46, [46]), (47, [47]), (48, [48]), (49, [49]), (50, [50]), (51, [51]), (52, [52])],
    [(-368, [2]), (-360, [2, 4]), (-352, [2]), (-328, [39]), (-320, [2]), (-296, [19]), (-288, [18]), (-280, [9]), (-272, [8]), (-256, [1]), (-240, [3]), (-224, [5]), (-216, [6]), (-208, [7]), (-184, [10]), (-176, [11]), (-168, [12]), (-160, [13]), (-152, [14]), (-144, [15]), (-136, [16]), (-128, [17]), (-40, [28]), (-32, [29]), (-24, [30]), (-16, [31])]⟩,
  ⟨[(2, [2]), (3, [3]), (4, [4]), (5, [5]), (6, [6]), (7, [7]), (8, [2]), (9, [39]), (11, [11]), (12, [12]), (13, [13]), (14, [50]), (16, [16]), (17, [17]), (18, [33]), (19, [50]), (20, [20]), (21, [21]), (22, [22]), (23, [23]), (24, [24]), (25, [25]), (26, [26]), (27, [27]), (28, [28]), (29, [29]), (30, [30]), (31, [31]), (32, [32]), (33, [33]), (34, [34]), (35, [35]), (36, [36]), (37, [37]), (38, [38]), (39, [39]), (40, [40]), (41, [41]), (42, [42]), (43, [43]), (44, [44]), (45, [45]), (46, [46]), (47, [47]), (48, [48]), (49, [49]), (50, [50]), (51, [51]), (52, [52])],
    [(-368, [2]), (-352, [2]), (-320, [2]), (-296, [19]), (-288, [18]), (-280, [9]), (-272, [8]), (-256, [1]), (-240, [3]), (-224, [5]), (-216, [6]), (-208, [7]), (-184, [10]), (-176, [11]), (-168, [12]), (-160, [13]), (-152, [14]), (-144, [15]), (-136, [16]), (-128, [17]), (-40, [28]), (-32, [29]), (-24, [30]), (-16, [31])]⟩,
  ⟨[(2, [2]), (3, [3]), (4, [4]), (5, [5]), (6, [6]), (7, [7]), (8, [2]), (9, [39]), (10, [10]), (11, [11]), (12, [12]), (13, [13]), (14, [50]), (16, [16]), (17, [17]), (18, [33]), (19, [50]), (20, [20]), (21, [21]), (22, [22]), (23, [23]), (24, [24]), (25, [25]), (26, [26]), (27, [27]), (28, [28]), (29, [29]), (30, [30]), (31, [31]), (32, [32]), (33, [33]), (34, [34]), (35, [35]), (36, [36]), (37, [37]), (38, [38]), (39, [39]), (40, [40]), (41, [41]), (42, [42]), (43, [43]), (44, [44]), (45, [45]), (46, [46]), (47, [47]), (48, [48]), (49, [49]), (50, [50]), (51, [51]), (52, [52])],
    [(-368, [2]), (-352, [2]), (-328, [39]), (-320, [2]), (-296, [19]), (-288, [18]), (-280, [9]), (-272, [8]), (-256, [1]), (-240, [3]), (-224, [5]), (-216, [6]), (-208, [7]), (-184, [10]), (-176, [11]), (-168, [12]), (-160, [13]), (-152, [14]), (-144, [15]), (-136, [16]), (-128, [17]), (-40, [28]), (-32, [29]), (-24, [30]), (-16, [31])]⟩,
  ⟨[(2, [2]), (3, [3]), (4, [4]), (5, [5]), (6, [6]), (7, [7]), (8, [2]), (9, [2, 4]), (10, [2, 4]), (11, [11]), (12, [12]), (16, [16]), (17, [17]), (18, [33]), (19, [50]), (20, [20]), (21, [21]), (22, [22]), (23, [23]), (24, [24]), (25, [25]), (26, [26]), (27, [27]), (28, [28]), (29, [29]), (30, [30]), (31, [31]), (32, [32]), (33, [33]), (34, [34]), (35, [35]), (36, [36]), (37, [37]), (38, [38]), (39, [39]), (40, [40]), (41, [41]), (42, [42]), (43, [43]), (44, [44]), (45, [45]), (46, [46]), (47, [47]), (48, [48]), (49, [49]), (50, [50]), (51, [51]), (52, [52])],
    [(-384, [2]), (-368, [2]), (-360, [2, 4]), (-352, [2]), (-328, [39]), (-320, [2]), (-296, [19]), (-288, [18]), (-280, [9]), (-272, [8]), (-256, [1]), (-240, [3]), (-224, [5]), (-216, [6]), (-208, [7]), (-184, [10]), (-176, [11]), (-168, [12]), (-160, [13]), (-152, [14]), (-144, [15]), (-136, [16]), (-128, [17]), (-40, [28]), (-32, [29]), (-24, [30]), (-16, [31])]⟩,
  ⟨[(2, [2]), (3, [3]), (4, [4]), (5, [5]), (6, [6]), (7, [7]), (8, [2]), (9, [39]), (10, [4]), (11, [11]), (12, [12]), (13, [13]), (14, [50]), (16, [16]), (17, [17]), (18, [33]), (19, [50]), (20, [20]), (21, [21]), (22, [22]), (23, [23]), (24, [24]), (25, [25]), (26, [26]), (27, [27]), (28, [28]), (29, [29]), (30, [30]), (31, [31]), (32, [32]), (33, [33]), (34, [34]), (35, [35]), (36, [36]), (37, [37]), (38, [38]), (39, [39]), (40, [40]), (41, [41]), (42, [42]), (43, [43]), (44, [44]), (45, [45]), (46, [46]), (47, [47]), (48, [48]), (49, [49]), (50, [50]), (51, [51]), (52, [52])],
    [(-368, [2]), (-352, [2]), (-320, [2]), (-296, [19]), (-288, [18]), (-280, [9]), (-272, [8]), (-256, [1]), (-240, [3]), (-224, [5]), (-216, [6]), (-208, [7]), (-184, [10]), (-176, [11]), (-168, [12]), (-160, [13]), (-152, [14]), (-144, [15]), (-136, [16]), (-128, [17]), (-40, [28]), (-32, [29]), (-24, [30]), (-16, [31])]⟩,
  ⟨[(2, [2]), (3, [3]), (4, [4]), (5, [5]), (6, [6]), (7, [7]), (8, [2]), (9, [39]), (10, [4]), (11, [11]), (12, [12]), (13, [13]), (14, [50]), (16, [16]), (17, [17]), (18, [33]), (19, [50]), (20, [20]), (21, [21]), (22, [22]), (23, [23]), (24, [24]), (25, [25]), (26, [26]), (27, [27]), (28, [28]), (29, [29]), (30, [30]), (31, [31]), (32, [32]), (33, [33]), (34, [34]), (35, [35]), (36, [36]), (37, [37]), (38, [38]), (39, [39]), (40, [40]), (41, [41]), (42, [42]), (43, [43]), (44, [44]), (45, [45]), (46, [46]), (47, [47]), (48, [48]), (49, [49]), (50, [50]), (51, [51]), (52, [52])],
    [(-368, [2]), (-352, [2]), (-328, [39]), (-320, [2]), (-296, [19]), (-288, [18]), (-280, [9]), (-272, [8]), (-256, [1]), (-240, [3]), (-224, [5]), (-216, [6]), (-208, [7]), (-184, [10]), (-176, [11]), (-168, [12]), (-160, [13]), (-152, [14]), (-144, [15]), (-136, [16]), (-128, [17]), (-40, [28]), (-32, [29]), (-24, [30]), (-16, [31])]⟩,
  ⟨[(2, [2]), (3, [3]), (4, [4]), (5, [5]), (6, [6]), (7, [7]), (8, [2]), (9, [2, 4]), (10, [4]), (11, [11]), (12, [12]), (16, [16]), (17, [17]), (18, [33]), (19, [50]), (20, [20]), (21, [21]), (22, [22]), (23, [23]), (24, [24]), (25, [25]), (26, [26]), (27, [27]), (28, [28]), (29, [29]), (30, [30]), (31, [31]), (32, [32]), (33, [33]), (34, [34]), (35, [35]), (36, [36]), (37, [37]), (38, [38]), (39, [39]), (40, [40]), (41, [41]), (42, [42]), (43, [43]), (44, [44]), (45, [45]), (46, [46]), (47, [47]), (48, [48]), (49, [49]), (50, [50]), (51, [51]), (52, [52])],
    [(-384, [2]), (-368, [2]), (-360, [2, 4]), (-352, [2]), (-328, [39]), (-320, [2]), (-296, [19]), (-288, [18]), (-280, [9]), (-272, [8]), (-256, [1]), (-240, [3]), (-224, [5]), (-216, [6]), (-208, [7]), (-184, [10]), (-176, [11]), (-168, [12]), (-160, [13]), (-152, [14]), (-144, [15]), (-136, [16]), (-128, [17]), (-40, [28]), (-32, [29]), (-24, [30]), (-16, [31])]⟩,
  ⟨[(1, [2]), (2, [2]), (3, [3]), (4, [4]), (5, [5]), (6, [6]), (7, [7]), (8, [2]), (9, [39]), (10, [4]), (11, [11]), (12, [12]), (13, [13]), (14, [50]), (16, [16]), (17, [17]), (18, [33]), (19, [50]), (20, [20]), (21, [21]), (22, [22]), (23, [23]), (24, [24]), (25, [25]), (26, [26]), (27, [27]), (28, [28]), (29, [29]), (30, [30]), (31, [31]), (32, [32]), (33, [33]), (34, [34]), (35, [35]), (36, [36]), (37, [37]), (38, [38]), (39, [39]), (40, [40]), (41, [41]), (42, [42]), (43, [43]), (44, [44]), (45, [45]), (46, [46]), (47, [47]), (48, [48]), (49, [49]), (50, [50]), (51, [51]), (52, [52])],
    [(-368, [2]), (-352, [2]), (-320, [2]), (-296, [19]), (-288, [18]), (-280, [9]), (-272, [8]), (-256, [1]), (-240, [3]), (-224, [5]), (-216, [6]), (-208, [7]), (-184, [10]), (-176, [11]), (-168, [12]), (-160, [13]), (-152, [14]), (-144, [15]), (-136, [16]), (-128, [17]), (-40, [28]), (-32, [29]), (-24, [30]), (-16, [31])]⟩,
  ⟨[(1, [2]), (2, [2]), (3, [3]), (4, [4]), (5, [5]), (6, [6]), (7, [7]), (8, [2]), (9, [39]), (10, [4]), (11, [11]), (12, [12]), (13, [13]), (14, [50]), (16, [16]), (17, [17]), (18, [33]), (19, [50]), (20, [20]), (21, [21]), (22, [22]), (23, [23]), (24, [24]), (25, [25]), (26, [26]), (27, [27]), (28, [28]), (29, [29]), (30, [30]), (31, [31]), (32, [32]), (33, [33]), (34, [34]), (35, [35]), (36, [36]), (37, [37]), (38, [38]), (39, [39]), (40, [40]), (41, [41]), (42, [42]), (43, [43]), (44, [44]), (45, [45]), (46, [46]), (47, [47]), (48, [48]), (49, [49]), (50, [50]), (51, [51]), (52, [52])],
    [(-368, [2]), (-352, [2]), (-328, [39]), (-320, [2]), (-296, [19]), (-288, [18]), (-280, [9]), (-272, [8]), (-256, [1]), (-240, [3]), (-224, [5]), (-216, [6]), (-208, [7]), (-184, [10]), (-176, [11]), (-168, [12]), (-160, [13]), (-152, [14]), (-144, [15]), (-136, [16]), (-128, [17]), (-40, [28]), (-32, [29]), (-24, [30]), (-16, [31])]⟩,
  ⟨[(1, [2]), (2, [2]), (3, [3]), (4, [4]), (5, [5]), (6, [6]), (7, [7]), (8, [2]), (9, [2, 4]), (10, [4]), (11, [11]), (12, [12]), (16, [16]), (17, [17]), (18, [33]), (19, [50]), (20, [20]), (21, [21]), (22, [22]), (23, [23]), (24, [24]), (25, [25]), (26, [26]), (27, [27]), (28, [28]), (29, [29]), (30, [30]), (31, [31]), (32, [32]), (33, [33]), (34, [34]), (35, [35]), (36, [36]), (37, [37]), (38, [38]), (39, [39]), (40, [40]), (41, [41]), (42, [42]), (43, [43]), (44, [44]), (45, [45]), (46, [46]), (47, [47]), (48, [48]), (49, [49]), (50, [50]), (51, [51]), (52, [52])],
    [(-384, [2]), (-368, [2]), (-360, [2, 4]), (-352, [2]), (-328, [39]), (-320, [2]), (-296, [19]), (-288, [18]), (-280, [9]), (-272, [8]), (-256, [1]), (-240, [3]), (-224, [5]), (-216, [6]), (-208, [7]), (-184, [10]), (-176, [11]), (-168, [12]), (-160, [13]), (-152, [14]), (-144, [15]), (-136, [16]), (-128, [17]), (-40, [28]), (-32, [29]), (-24, [30]), (-16, [31])]⟩,
  ⟨[(2, [2]), (3, [3]), (4, [4]), (5, [5]), (6, [6]), (7, [7]), (8, [2]), (9, [39]), (10, [4]), (11, [11]), (12, [12]), (16, [16]), (17, [17]), (18, [33]), (19, [50]), (20, [20]), (21, [21]), (22, [22]), (23, [23]), (24, [24]), (25, [25]), (26, [26]), (27, [27]), (28, [28]), (29, [29]), (30, [30]), (31, [31]), (32, [32]), (33, [33]), (34, [34]), (35, [35]), (36, [36]), (37, [37]), (38, [38]), (39, [39]), (40, [40]), (41, [41]), (42, [42]), (43, [43]), (44, [44]), (45, [45]), (46, [46]), (47, [47]), (48, [48]), (49, [49]), (50, [50]), (51, [51])],
    [(-384, [2]), (-360, [39]), (-352, [2]), (-328, [39]), (-320, [2]), (-296, [19]), (-288, [18]), (-280, [9]), (-272, [8]), (-256, [1]), (-240, [3]), (-224, [5]), (-216, [6]), (-208, [7]), (-184, [10]), (-176, [11]), (-168, [12]), (-160, [13]), (-152, [14]), (-144, [15]), (-136, [16]), (-128, [17]), (-40, [28]), (-32, [29]), (-24, [30]), (-16, [31])]⟩,
  ⟨[(2, [2]), (3, [3]), (4, [4]), (5, [5]), (6, [6]), (7, [7]), (8, [2]), (9, [39]), (10, [4]), (11, [11]), (12, [12]), (15, [4]), (16, [16]), (17, [17]), (18, [33]), (19, [50]), (20, [20]), (21, [21]), (22, [22]), (23, [23]), (24, [24]), (25, [25]), (26, [26]), (27, [27]), (28, [28]), (29, [29]), (30, [30]), (31, [31]), (32, [32]), (33, [33]), (34, [34]), (35, [35]), (36, [36]), (37, [37]), (38, [38]), (39, [39]), (40, [40]), (41, [41]), (42, [42]), (43, [43]), (44, [44]), (45, [45]), (46, [46]), (47, [47]), (48, [48]), (49, [49]), (50, [50]), (51, [51])],
    [(-384, [2]), (-360, [39]), (-352, [2]), (-328, [39]), (-320, [2]), (-296, [19]), (-288, [18]), (-280, [9]), (-272, [8]), (-256, [1]), (-240, [3]), (-224, [5]), (-216, [6]), (-208, [7]), (-184, [10]), (-176, [11]), (-168, [12]), (-160, [13]), (-152, [14]), (-144, [15]), (-136, [16]), (-128, [17]), (-40, [28]), (-32, [29]), (-24, [30]), (-16, [31])]⟩,
  ⟨[(2, [2]), (3, [3]), (4, [4]), (5, [5]), (6, [6]), (7, [7]), (8, [2]), (9, [4]), (10, [4]), (11, [11]), (12, [12]), (15, [4]), (16, [16]), (17, [17]), (18, [33]), (19, [50]), (20, [20]), (21, [21]), (22, [22]), (23, [23]), (24, [24]), (25, [25]), (26, [26]), (27, [27]), (28, [28]), (29, [29]), (30, [30]), (31, [31]), (32, [32]), (33, [33]), (34, [34]), (35, [35]), (36, [36]), (37, [37]), (38, [38]), (39, [39]), (40, [40]), (41, [41]), (42, [42]), (43, [43]), (44, [44]), (45, [45]), (46, [46]), (47, [47]), (48, [48]), (49, [49]), (50, [50]), (51, [51])],
    [(-384, [2]), (-352, [2]), (-328, [39]), (-320, [2]), (-296, [19]), (-288, [18]), (-280, [9]), (-272, [8]), (-256, [1]), (-240, [3]), (-224, [5]), (-216, [6]), (-208, [7]), (-184, [10]), (-176, [11]), (-168, [12]), (-160, [13]), (-152, [14]), (-144, [15]), (-136, [16]), (-128, [17]), (-40, [28]), (-32, [29]), (-24, [30]), (-16, [31])]⟩,
  ⟨[(2, [2]), (3, [3]), (4, [4]), (5, [5]), (6, [6]), (7, [7]), (8, [2]), (9, [39]), (11, [11]), (12, [12]), (15, [39]), (16, [16]), (17, [17]), (18, [33]), (19, [50]), (20, [20]), (21, [21]), (22, [22]), (23, [23]), (24, [24]), (25, [25]), (26, [26]), (27, [27]), (28, [28]), (29, [29]), (30, [30]), (31, [31]), (32, [32]), (33, [33]), (34, [34]), (35, [35]), (36, [36]), (37, [37]), (38, [38]), (39, [39]), (40, [40]), (41, [41]), (42, [42]), (43, [43]), (44, [44]), (45, [45]), (46, [46]), (47, [47]), (48, [48]), (49, [49]), (50, [50]), (51, [51])],
    [(-384, [2]), (-360, [39]), (-352, [2]), (-328, [39]), (-320, [2]), (-296, [19]), (-288, [18]), (-280, [9]), (-272, [8]), (-256, [1]), (-240, [3]), (-224, [5]), (-216, [6]), (-208, [7]), (-184, [10]), (-176, [11]), (-168, [12]), (-160, [13]), (-152, [14]), (-144, [15]), (-136, [16]), (-128, [17]), (-40, [28]), (-32, [29]), (-24, [30]), (-16, [31])]⟩,
  ⟨[(2, [2]), (3, [3]), (4, [4]), (5, [5]), (6, [6]), (7, [7]), (8, [2]), (9, [4]), (10, [4]), (11, [11]), (12, [12]), (15, [4]), (16, [16]), (17, [17]), (18, [33]), (19, [50]), (20, [20]), (21, [21]), (22, [22]), (23, [23]), (24, [24]), (25, [25]), (26, [26]), (27, [27]), (28, [28]), (29, [29]), (30, [30]), (31, [31]), (32, [32]), (33, [33]), (34, [34]), (35, [35]), (36, [36]), (37, [37]), (38, [38]), (39, [39]), (40, [40]), (41, [41]), (42, [42]), (43, [43]), (44, [44]), (45, [45]), (46, [46]), (47, [47]), (48, [48]), (49, [49]), (50, [50]), (51, [51])],
    [(-384, [2]), (-368, [2]), (-352, [2]), (-328, [39]), (-320, [2]), (-296, [19]), (-288, [18]), (-280, [9]), (-272, [8]), (-256, [1]), (-240, [3]), (-224, [5]), (-216, [6]), (-208, [7]), (-184, [10]), (-176, [11]), (-168, [12]), (-160, [13]), (-152, [14]), (-144, [15]), (-136, [16]), (-128, [17]), (-40, [28]), (-32, [29]), (-24, [30]), (-16, [31])]⟩,
  ⟨[(2, [2]), (3, [3]), (4, [4]), (5, [5]), (6, [6]), (7, [7]), (8, [2]), (9, [39]), (11, [11]), (12, [12]), (15, [4]), (16, [16]), (17, [17]), (18, [33]), (19, [50]), (20, [20]), (21, [21]), (22, [22]), (23, [23]), (24, [24]), (25, [25]), (26, [26]), (27, [27]), (28, [28]), (29, [29]), (30, [30]), (31, [31]), (32, [32]), (33, [33]), (34, [34]), (35, [35]), (36, [36]), (37, [37]), (38, [38]), (39, [39]), (40, [40]), (41, [41]), (42, [42]), (43, [43]), (44, [44]), (45, [45]), (46, [46]), (47, [47]), (48, [48]), (49, [49]), (50, [50]), (51, [51])],
    [(-384, [2]), (-360, [39]), (-352, [2]), (-328, [39]), (-320, [2]), (-296, [19]), (-288, [18]), (-280, [9]), (-272, [8]), (-256, [1]), (-240, [3]), (-224, [5]), (-216, [6]), (-208, [7]), (-184, [10]), (-176, [11]), (-168, [12]), (-160, [13]), (-152, [14]), (-144, [15]), (-136, [16]), (-128, [17]), (-40, [28]), (-32, [29]), (-24, [30]), (-16, [31])]⟩,
  ⟨[(2, [2]), (3, [3]), (4, [4]), (5, [5]), (6, [6]), (7, [7]), (8, [2]), (9, [4]), (11, [11]), (12, [12]), (15, [4]), (16, [16]), (17, [17]), (18, [33]), (19, [50]), (20, [20]), (21, [21]), (22, [22]), (23, [23]), (24, [24]), (25, [25]), (26, [26]), (27, [27]), (28, [28]), (29, [29]), (30, [30]), (31, [31]), (32, [32]), (33, [33]), (34, [34]), (35, [35]), (36, [36]), (37, [37]), (38, [38]), (39, [39]), (40, [40]), (41, [41]), (42, [42]), (43, [43]), (44, [44]), (45, [45]), (46, [46]), (47, [47]), (48, [48]), (49, [49]), (50, [50]), (51, [51])],
    [(-384, [2]), (-368, [2]), (-352, [2]), (-328, [39]), (-320, [2]), (-296, [19]), (-288, [18]), (-280, [9]), (-272, [8]), (-256, [1]), (-240, [3]), (-224, [5]), (-216, [6]), (-208, [7]), (-184, [10]), (-176, [11]), (-168, [12]), (-160, [13]), (-152, [14]), (-144, [15]), (-136, [16]), (-128, [17]), (-40, [28]), (-32, [29]), (-24, [30]), (-16, [31])]⟩,
  ⟨[(2, [2]), (3, [3]), (4, [4]), (5, [5]), (6, [6]), (7, [7]), (8, [2]), (9, [39]), (11, [11]), (12, [12]), (16, [16]), (17, [17]), (18, [33]), (19, [50]), (20, [20]), (21, [21]), (22, [22]), (23, [23]), (24, [24]), (25, [25]), (26, [26]), (27, [27]), (28, [28]), (29, [29]), (30, [30]), (31, [31]), (32, [32]), (33, [33]), (34, [34]), (35, [35]), (36, [36]), (37, [37]), (38, [38]), (39, [39]), (40, [40]), (41, [41]), (42, [42]), (43, [43]), (44, [44]), (45, [45]), (46, [46]), (47, [47]), (48, [48]), (49, [49]), (50, [50]), (51, [51])],
    [(-320, [2]), (-296, [19]), (-288, [18]), (-280, [9]), (-272, [8]), (-256, [1]), (-240, [3]), (-224, [5]), (-216, [6]), (-208, [7]), (-184, [10]), (-176, [11]), (-168, [12]), (-160, [13]), (-152, [14]), (-144, [15]), (-136, [16]), (-128, [17]), (-40, [28]), (-32, [29]), (-24, [30]), (-16, [31])]⟩,
  ⟨[(1, [2]), (2, [2]), (3, [3]), (4, [4]), (5, [5]), (6, [6]), (7, [7]), (8, [2]), (9, [4]), (10, [4]), (11, [11]), (12, [12]), (15, [4]), (16, [16]), (17, [17]), (18, [33]), (19, [50]), (20, [20]), (21, [21]), (22, [22]), (23, [23]), (24, [24]), (25, [25]), (26, [26]), (27, [27]), (28, [28]), (29, [29]), (30, [30]), (31, [31]), (32, [32]), (33, [33]), (34, [34]), (35, [35]), (36, [36]), (37, [37]), (38, [38]), (39, [39]), (40, [40]), (41, [41]), (42, [42]), (43, [43]), (44, [44]), (45, [45]), (46, [46]), (47, [47]), (48, [48]), (49, [49]), (50, [50]), (51, [51])],
    [(-384, [2]), (-360, [39]), (-352, [2]), (-328, [39]), (-320, [2]), (-296, [19]), (-288, [18]), (-280, [9]), (-272, [8]), (-256, [1]), (-240, [3]), (-224, [5]), (-216, [6]), (-208, [7]), (-184, [10]), (-176, [11]), (-168, [12]), (-160, [13]), (-152, [14]), (-144, [15]), (-136, [16]), (-128, [17]), (-40, [28]), (-32, [29]), (-24, [30]), (-16, [31])]⟩,
  ⟨[(1, [2]), (2, [2]), (3, [3]), (4, [4]), (5, [5]), (6, [6]), (7, [7]), (8, [2]), (9, [2, 39]), (10, [4]), (11, [11]), (12, [12]), (15, [4]), (16, [16]), (17, [17]), (18, [33]), (19, [50]), (20, [20]), (21, [21]), (22, [22]), (23, [23]), (24, [24]), (25, [25]), (26, [26]), (27, [27]), (28, [28]), (29, [29]), (30, [30]), (31, [31]), (32, [32]), (33, [33]), (34, [34]), (35, [35]), (36, [36]), (37, [37]), (38, [38]), (39, [39]), (40, [40]), (41, [41]), (42, [42]), (43, [43]), (44, [44]), (45, [45]), (46, [46]), (47, [47]), (48, [48]), (49, [49]), (50, [50]), (51, [51])],
    [(-384, [2]), (-368, [2]), (-352, [2]), (-328, [39]), (-320, [2]), (-296, [19]), (-288, [18]), (-280, [9]), (-272, [8]), (-256, [1]), (-240, [3]), (-224, [5]), (-216, [6]), (-208, [7]), (-184, [10]), (-176, [11]), (-168, [12]), (-160, [13]), (-152, [14]), (-144, [15]), (-136, [16]), (-128, [17]), (-40, [28]), (-32, [29]), (-24, [30]), (-16, [31])]⟩,
  ⟨[(2, [2]), (3, [3]), (4, [4]), (5, [5]), (6, [6]), (7, [7]), (8, [2]), (9, [39]), (11, [11]), (12, [12]), (13, [13]), (14, [50]), (16, [16]), (17, [17]), (18, [33]), (19, [50]), (20, [20]), (21, [21]), (22, [22]), (23, [23]), (24, [24]), (25, [25]), (26, [26]), (27, [27]), (28, [28]), (29, [29]), (30, [30]), (31, [31]), (32, [32]), (33, [33]), (34, [34]), (35, [35]), (36, [36]), (37, [37]), (38, [38]), (39, [39]), (40, [40]), (41, [41]), (42, [42]), (43, [43]), (44, [44]), (45, [45]), (46, [46]), (47, [47]), (48, [48]), (49, [49]), (50, [50]), (51, [51]), (52, [52])],
    [(-320, [2]), (-296, [19]), (-288, [18]), (-280, [9]), (-272, [8]), (-256, [1]), (-240, [3]), (-224, [5]), (-216, [6]), (-208, [7]), (-184, [10]), (-176, [11]), (-168, [12]), (-160, [13]), (-152, [14]), (-144, [15]), (-136, [16]), (-128, [17]), (-40, [28]), (-32, [29]), (-24, [30]), (-16, [31])]⟩,
  ⟨[(1, [2]), (2, [2]), (3, [3]), (4, [4]), (5, [5]), (6, [6]), (7, [7]), (8, [2]), (9, [39]), (10, [4]), (11, [11]), (12, [12]), (13, [13]), (14, [50]), (15, [49]), (16, [16]), (17, [17]), (18, [33]), (19, [50]), (20, [20]), (21, [21]), (22, [22]), (23, [23]), (24, [24]), (25, [25]), (26, [26]), (27, [27]), (28, [28]), (29, [29]), (30, [30]), (31, [31]), (32, [32]), (33, [33]), (34, [34]), (35, [35]), (36, [36]), (37, [37]), (38, [38]), (39, [39]), (40, [40]), (41, [41]), (42, [42]), (43, [43]), (44, [44]), (45, [45]), (46, [46]), (47, [47]), (48, [48]), (49, [49]), (50, [50]), (51, [51]), (52, [52])],
    [(-368, [2]), (-352, [2]), (-320, [2]), (-296, [19]), (-288, [18]), (-280, [9]), (-272, [8]), (-256, [1]), (-240, [3]), (-224, [5]), (-216, [6]), (-208, [7]), (-184, [10]), (-176, [11]), (-168, [12]), (-160, [13]), (-152, [14]), (-144, [15]), (-136, [16]), (-128, [17]), (-40, [28]), (-32, [29]), (-24, [30]), (-16, [31])]⟩,
  ⟨[(1, [2]), (2, [2]), (3, [3]), (4, [4]), (5, [5]), (6, [6]), (7, [7]), (8, [2]), (9, [39]), (10, [4]), (11, [11]), (12, [12]), (13, [13]), (15, [49]), (16, [16]), (17, [17]), (18, [33]), (19, [50]), (20, [20]), (21, [21]), (22, [22]), (23, [23]), (24, [24]), (25, [25]), (26, [26]), (27, [27]), (28, [28]), (29, [29]), (30, [30]), (31, [31]), (32, [32]), (33, [33]), (34, [34]), (35, [35]), (36, [36]), (37, [37]), (38, [38]), (39, [39]), (40, [40]), (41, [41]), (42, [42]), (43, [43]), (44, [44]), (45, [45]), (46, [46]), (47, [47]), (48, [48]), (49, [49]), (50, [50]), (51, [51]), (52, [52])],
    [(-368, [2]), (-352, [2]), (-320, [2]), (-296, [19]), (-288, [18]), (-280, [9]), (-272, [8]), (-256, [1]), (-240, [3]), (-224, [5]), (-216, [6]), (-208, [7]), (-184, [10]), (-176, [11]), (-168, [12]), (-160, [13]), (-152, [14]), (-144, [15]), (-136, [16]), (-128, [17]), (-40, [28]), (-32, [29]), (-24, [30]), (-16, [31])]⟩,
  ⟨[(1, [2]), (2, [2]), (3, [3]), (4, [4]), (5, [5]), (6, [6]), (7, [7]), (8, [2]), (9, [39]), (10, [4]), (11, [11]), (12, [12]), (13, [13]), (15, [49]), (16, [16]), (17, [17]), (18, [33]), (19, [50]), (20, [20]), (21, [21]), (22, [22]), (23, [23]), (24, [24]), (25, [25]), (26, [26]), (27, [27]), (28, [28]), (29, [29]), (30, [30]), (31, [31]), (32, [32]), (33, [33]), (34, [34]), (35, [35]), (36, [36]), (37, [37]), (38, [38]), (39, [39]), (40, [40]), (41, [41]), (42, [42]), (43, [43]), (44, [44]), (45, [45]), (46, [46]), (47, [47]), (48, [48]), (49, [49]), (50, [50]), (51, [51]), (52, [49])],
    [(-368, [2]), (-352, [2]), (-320, [2]), (-296, [19]), (-288, [18]), (-280, [9]), (-272, [8]), (-256, [1]), (-240, [3]), (-224, [5]), (-216, [6]), (-208, [7]), (-184, [10]), (-176, [11]), (-168, [12]), (-160, [13]), (-152, [14]), (-144, [15]), (-136, [16]), (-128, [17]), (-40, [28]), (-32, [29]), (-24, [30]), (-16, [31])]⟩,
  ⟨[(2, [2]), (3, [3]), (4, [4]), (5, [5]), (6, [6]), (7, [7]), (8, [2]), (9, [39]), (10, [10]), (11, [11]), (12, [12]), (13, [13]), (14, [14]), (15, [39]), (16, [16]), (17, [17]), (18, [33]), (19, [50]), (20, [20]), (21, [21]), (22, [22]), (23, [23]), (24, [24]), (25, [25]), (26, [26]), (27, [27]), (28, [28]), (29, [29]), (30, [30]), (31, [31]), (32, [32]), (33, [33]), (34, [34]), (35, [35]), (36, [36]), (37, [37]), (38, [38]), (39, [39]), (40, [40]), (41, [41]), (42, [42]), (43, [43]), (44, [44]), (45, [45]), (46, [46]), (47, [47]), (48, [48]), (49, [49]), (50, [50]), (51, [51]), (52, [52])],
    [(-296, [19]), (-288, [18]), (-280, [9]), (-272, [8]), (-256, [1]), (-240, [3]), (-224, [5]), (-216, [6]), (-208, [7]), (-184, [10]), (-176, [11]), (-168, [12]), (-160, [13]), (-152, [14]), (-144, [15]), (-136, [16]), (-128, [17]), (-40, [28]), (-32, [29]), (-24, [30]), (-16, [31])]⟩,
  ⟨[(2, [2]), (3, [3]), (4, [4]), (5, [5]), (6, [6]), (7, [7]), (8, [2]), (9, [39]), (10, [10]), (11, [11]), (12, [12]), (13, [13]), (14, [14]), (15, [39]), (16, [16]), (17, [17]), (18, [33]), (19, [50]), (20, [20]), (21, [21]), (22, [22]), (23, [23]), (24, [24]), (25, [25]), (26, [26]), (27, [27]), (28, [28]), (29, [29]), (30, [30]), (31, [31]), (32, [32]), (33, [33]), (34, [34]), (35, [35]), (36, [36]), (37, [37]), (38, [38]), (39, [39]), (40, [40]), (41, [41]), (42, [42]), (43, [43]), (44, [44]), (45, [45]), (46, [46]), (47, [47]), (48, [48]), (49, [49]), (50, [50]), (51, [51]), (52, [52])],
    [(-320, [2]), (-296, [19]), (-288, [18]), (-280, [9]), (-272, [8]), (-256, [1]), (-240, [3]), (-224, [5]), (-216, [6]), (-208, [7]), (-184, [10]), (-176, [11]), (-168, [12]), (-160, [13]), (-152, [14]), (-144, [15]), (-136, [16]), (-128, [17]), (-40, [28]), (-32, [29]), (-24, [30]), (-16, [31])]⟩,
  ⟨[(2, [2]), (3, [3]), (4, [4]), (5, [5]), (6, [6]), (7, [7]), (8, [2]), (9, [39]), (10, [10]), (11, [11]), (12, [12]), (13, [13]), (14, [50]), (15, [39]), (16, [16]), (17, [17]), (18, [33]), (19, [50]), (20, [20]), (21, [21]), (22, [22]), (23, [23]), (24, [24]), (25, [25]), (26, [26]), (27, [27]), (28, [28]), (29, [29]), (30, [30]), (31, [31]), (32, [32]), (33, [33]), (34, [34]), (35, [35]), (36, [36]), (37, [37]), (38, [38]), (39, [39]), (40, [40]), (41, [41]), (42, [42]), (43, [43]), (44, [44]), (45, [45]), (46, [46]), (47, [47]), (48, [48]), (49, [49]), (50, [50]), (51, [51]), (52, [52])],
    [(-320, [2]), (-296, [19]), (-288, [18]), (-280, [9]), (-272, [8]), (-256, [1]), (-240, [3]), (-224, [5]), (-216, [6]), (-208, [7]), (-184, [10]), (-176, [11]), (-168, [12]), (-160, [13]), (-152, [14]), (-144, [15]), (-136, [16]), (-128, [17]), (-40, [28]), (-32, [29]), (-24, [30]), (-16, [31])]⟩,
  ⟨[(2, [2]), (3, [3]), (4, [4]), (5, [5]), (6, [6]), (7, [7]), (8, [2]), (9, [39]), (10, [10]), (11, [11]), (12, [12]), (13, [13]), (14, [50]), (16, [16]), (17, [17]), (18, [33]), (19, [50]), (20, [20]), (21, [21]), (22, [22]), (23, [23]), (24, [24]), (25, [25]), (26, [26]), (27, [27]), (28, [28]), (29, [29]), (30, [30]), (31, [31]), (32, [32]), (33, [33]), (34, [34]), (35, [35]), (36, [36]), (37, [37]), (38, [38]), (39, [39]), (40, [40]), (41, [41]), (42, [42]), (43, [43]), (44, [44]), (45, [45]), (46, [46]), (47, [47]), (48, [48]), (49, [49]), (50, [50]), (51, [51]), (52, [52])],
    [(-320, [2]), (-296, [19]), (-288, [18]), (-280, [9]), (-272, [8]), (-256, [1]), (-240, [3]), (-224, [5]), (-216, [6]), (-208, [7]), (-184, [10]), (-176, [11]), (-168, [12]), (-160, [13]), (-152, [14]), (-144, [15]), (-136, [16]), (-128, [17]), (-40, [28]), (-32, [29]), (-24, [30]), (-16, [31])]⟩,
  ⟨[(1, [2]), (2, [2]), (3, [3]), (4, [4]), (5, [5]), (6, [6]), (7, [7]), (8, [2]), (9, [39]), (11, [11]), (12, [12]), (16, [16]), (17, [17]), (18, [33]), (19, [50]), (20, [20]), (21, [21]), (22, [22]), (23, [23]), (24, [24]), (25, [25]), (26, [26]), (27, [27]), (28, [28]), (29, [29]), (30, [30]), (31, [31]), (32, [32]), (33, [33]), (34, [34]), (35, [35]), (36, [36]), (37, [37]), (38, [38]), (39, [39]), (40, [40]), (41, [41]), (42, [42]), (43, [43]), (44, [44]), (45, [45]), (46, [46]), (47, [47]), (48, [48]), (49, [49]), (50, [50]), (51, [51])],
    [(-320, [2]), (-296, [19]), (-288, [18]), (-280, [9]), (-272, [8]), (-256, [1]), (-240, [3]), (-224, [5]), (-216, [6]), (-208, [7]), (-184, [10]), (-176, [11]), (-168, [12]), (-160, [13]), (-152, [14]), (-144, [15]), (-136, [16]), (-128, [17]), (-40, [28]), (-32, [29]), (-24, [30]), (-16, [31])]⟩,
  ⟨[(2, [2]), (3, [3]), (4, [4]), (5, [5]), (6, [6]), (7, [7]), (8, [2]), (9, [39]), (10, [10]), (11, [11]), (12, [12]), (13, [13]), (14, [50]), (16, [16]), (17, [17]), (18, [33]), (19, [50]), (20, [20]), (21, [21]), (22, [22]), (23, [23]), (24, [24]), (25, [25]), (26, [26]), (27, [27]), (28, [28]), (29, [29]), (30, [30]), (31, [31]), (32, [32]), (33, [33]), (34, [34]), (35, [35]), (36, [36]), (37, [37]), (38, [38]), (39, [39]), (40, [40]), (41, [41]), (42, [42]), (43, [43]), (44, [44]), (45, [45]), (46, [46]), (47, [47]), (48, [48]), (49, [49]), (50, [50]), (51, [51]), (52, [52])],
    [(-328, [39]), (-320, [2]), (-296, [19]), (-288, [18]), (-280, [9]), (-272, [8]), (-256, [1]), (-240, [3]), (-224, [5]), (-216, [6]), (-208, [7]), (-184, [10]), (-176, [11]), (-168, [12]), (-160, [13]), (-152, [14]), (-144, [15]), (-136, [16]), (-128, [17]), (-40, [28]), (-32, [29]), (-24, [30]), (-16, [31])]⟩,
  ⟨[(1, [2]), (2, [2]), (3, [3]), (4, [4]), (5, [5]), (6, [6]), (7, [7]), (8, [2]), (9, [39]), (10, [4]), (11, [11]), (12, [12]), (13, [13]), (14, [50]), (15, [4]), (16, [16]), (17, [17]), (18, [33]), (19, [50]), (20, [20]), (21, [21]), (22, [22]), (23, [23]), (24, [24]), (25, [25]), (26, [26]), (27, [27]), (28, [28]), (29, [29]), (30, [30]), (31, [31]), (32, [32]), (33, [33]), (34, [34]), (35, [35]), (36, [36]), (37, [37]), (38, [38]), (39, [39]), (40, [40]), (41, [41]), (42, [42]), (43, [43]), (44, [44]), (45, [45]), (46, [46]), (47, [47]), (48, [48]), (49, [49]), (50, [50]), (51, [51]), (52, [52])],
    [(-368, [2]), (-352, [2]), (-328, [39]), (-320, [2]), (-296, [19]), (-288, [18]), (-280, [9]), (-272, [8]), (-256, [1]), (-240, [3]), (-224, [5]), (-216, [6]), (-208, [7]), (-184, [10]), (-176, [11]), (-168, [12]), (-160, [13]), (-152, [14]), (-144, [15]), (-136, [16]), (-128, [17]), (-40, [28]), (-32, [29]), (-24, [30]), (-16, [31])]⟩,
  ⟨[(1, [2]), (2, [2]), (3, [3]), (4, [4]), (5, [5]), (6, [6]), (7, [7]), (8, [2]), (9, [39]), (10, [4]), (11, [11]), (12, [12]), (13, [13]), (14, [4]), (15, [4]), (16, [16]), (17, [17]), (18, [33]), (19, [50]), (20, [20]), (21, [21]), (22, [22]), (23, [23]), (24, [24]), (25, [25]), (26, [26]), (27, [27]), (28, [28]), (29, [29]), (30, [30]), (31, [31]), (32, [32]), (33, [33]), (34, [34]), (35, [35]), (36, [36]), (37, [37]), (38, [38]), (39, [39]), (40, [40]), (41, [41]), (42, [42]), (43, [43]), (44, [44]), (45, [45]), (46, [46]), (47, [47]), (48, [48]), (49, [49]), (50, [50]), (51, [51]), (52, [52])],
    [(-368, [2]), (-352, [2]), (-328, [39]), (-320, [2]), (-296, [19]), (-288, [18]), (-280, [9]), (-272, [8]), (-256, [1]), (-240, [3]), (-224, [5]), (-216, [6]), (-208, [7]), (-184, [10]), (-176, [11]), (-168, [12]), (-160, [13]), (-152, [14]), (-144, [15]), (-136, [16]), (-128, [17]), (-40, [28]), (-32, [29]), (-24, [30]), (-16, [31])]⟩,
  ⟨[(1, [2]), (2, [2]), (3, [3]), (4, [4]), (5, [5]), (6, [6]), (7, [7]), (8, [2]), (9, [4]), (10, [4]), (11, [11]), (12, [12]), (13, [13]), (14, [4]), (15, [4]), (16, [16]), (17, [17]), (18, [33]), (19, [50]), (20, [20]), (21, [21]), (22, [22]), (23, [23]), (24, [24]), (25, [25]), (26, [26]), (27, [27]), (28, [28]), (29, [29]), (30, [30]), (31, [31]), (32, [32]), (33, [33]), (34, [34]), (35, [35]), (36, [36]), (37, [37]), (38, [38]), (39, [39]), (40, [40]), (41, [41]), (42, [42]), (43, [43]), (44, [44]), (45, [45]), (46, [46]), (47, [47]), (48, [48]), (49, [49]), (50, [50]), (51, [51]), (52, [52])],
    [(-368, [2]), (-352, [2]), (-328, [39]), (-320, [2]), (-296, [19]), (-288, [18]), (-280, [9]), (-272, [8]), (-256, [1]), (-240, [3]), (-224, [5]), (-216, [6]), (-208, [7]), (-184, [10]), (-176, [11]), (-168, [12]), (-160, [13]), (-152, [14]), (-144, [15]), (-136, [16]), (-128, [17]), (-40, [28]), (-32, [29]), (-24, [30]), (-16, [31])]⟩,
  ⟨[(1, [2]), (2, [2]), (3, [3]), (4, [4]), (5, [5]), (6, [6]), (7, [7]), (8, [2]), (9, [4]), (10, [4]), (11, [11]), (12, [12]), (13, [13]), (14, [4]), (16, [16]), (17, [17]), (18, [33]), (19, [50]), (20, [20]), (21, [21]), (22, [22]), (23, [23]), (24, [24]), (25, [25]), (26, [26]), (27, [27]), (28, [28]), (29, [29]), (30, [30]), (31, [31]), (32, [32]), (33, [33]), (34, [34]), (35, [35]), (36, [36]), (37, [37]), (38, [38]), (39, [39]), (40, [40]), (41, [41]), (42, [42]), (43, [43]), (44, [44]), (45, [45]), (46, [46]), (47, [47]), (48, [48]), (49, [49]), (50, [50]), (51, [51]), (52, [52])],
    [(-368, [2]), (-352, [2]), (-328, [39]), (-320, [2]), (-296, [19]), (-288, [18]), (-280, [9]), (-272, [8]), (-256, [1]), (-240, [3]), (-224, [5]), (-216, [6]), (-208, [7]), (-184, [10]), (-176, [11]), (-168, [12]), (-160, [13]), (-152, [14]), (-144, [15]), (-136, [16]), (-128, [17]), (-40, [28]), (-32, [29]), (-24, [30]), (-16, [31])]⟩,
  ⟨[(1, [2]), (2, [2]), (3, [3]), (4, [4]), (5, [5]), (6, [6]), (7, [7]), (8, [2]), (9, [4]), (11, [11]), (12, [12]), (13, [13]), (14, [4]), (16, [16]), (17, [17]), (18, [33]), (19, [50]), (20, [20]), (21, [21]), (22, [22]), (23, [23]), (24, [24]), (25, [25]), (26, [26]), (27, [27]), (28, [28]), (29, [29]), (30, [30]), (31, [31]), (32, [32]), (33, [33]), (34, [34]), (35, [35]), (36, [36]), (37, [37]), (38, [38]), (39, [39]), (40, [40]), (41, [41]), (42, [42]), (43, [43]), (44, [44]), (45, [45]), (46, [46]), (47, [47]), (48, [48]), (49, [49]), (50, [50]), (51, [51]), (52, [52])],
    [(-368, [2]), (-352, [2]), (-328, [39]), (-320, [2]), (-296, [19]), (-288, [18]), (-280, [9]), (-272, [8]), (-256, [1]), (-240, [3]), (-224, [5]), (-216, [6]), (-208, [7]), (-184, [10]), (-176, [11]), (-168, [12]), (-160, [13]), (-152, [14]), (-144, [15]), (-136, [16]), (-128, [17]), (-40, [28]), (-32, [29]), (-24, [30]), (-16, [31])]⟩,
  ⟨[(1, [2]), (2, [2]), (3, [3]), (4, [4]), (5, [5]), (6, [6]), (7, [7]), (8, [2]), (9, [2, 39]), (11, [11]), (12, [12]), (13, [13]), (14, [4]), (16, [16]), (17, [17]), (18, [33]), (19, [50]), (20, [20]), (21, [21]), (22, [22]), (23, [23]), (24, [24]), (25, [25]), (26, [26]), (27, [27]), (28, [28]), (29, [29]), (30, [30]), (31, [31]), (32, [32]), (33, [33]), (34, [34]), (35, [35]), (36, [36]), (37, [37]), (38, [38]), (39, [39]), (40, [40]), (41, [41]), (42, [42]), (43, [43]), (44, [44]), (45, [45]), (46, [46]), (47, [47]), (48, [48]), (49, [49]), (50, [50]), (51, [51]), (52, [52])],
    [(-368, [2]), (-352, [2]), (-328, [39]), (-320, [2]), (-296, [19]), (-288, [18]), (-280, [9]), (-272, [8]), (-256, [1]), (-240, [3]), (-224, [5]), (-216, [6]), (-208, [7]), (-184, [10]), (-176, [11]), (-168, [12]), (-160, [13]), (-152, [14]), (-144, [15]), (-136, [16]), (-128, [17]), (-40, [28]), (-32, [29]), (-24, [30]), (-16, [31])]⟩,
  ⟨[(1, [2]), (2, [2]), (3, [3]), (4, [4]), (5, [5]), (6, [6]), (7, [7]), (8, [2]), (9, [2, 4]), (10, [2, 4]), (11, [11]), (12, [12]), (16, [16]), (17, [17]), (18, [33]), (19, [50]), (20, [20]), (21, [21]), (22, [22]), (23, [23]), (24, [24]), (25, [25]), (26, [26]), (27, [27]), (28, [28]), (29, [29]), (30, [30]), (31, [31]), (32, [32]), (33, [33]), (34, [34]), (35, [35]), (36, [36]), (37, [37]), (38, [38]), (39, [39]), (40, [40]), (41, [41]), (42, [42]), (43, [43]), (44, [44]), (45, [45]), (46, [46]), (47, [47]), (48, [48]), (49, [49]), (50, [50]), (51, [51]), (52, [52])],
    [(-368, [2]), (-360, [4]), (-352, [2]), (-328, [39]), (-320, [2]), (-296, [19]), (-288, [18]), (-280, [9]), (-272, [8]), (-256, [1]), (-240, [3]), (-224, [5]), (-216, [6]), (-208, [7]), (-184, [10]), (-176, [11]), (-168, [12]), (-160, [13]), (-152, [14]), (-144, [15]), (-136, [16]), (-128, [17]), (-40, [28]), (-32, [29]), (-24, [30]), (-16, [31])]⟩,
  ⟨[(1, [2]), (2, [2]), (3, [3]), (4, [4]), (5, [5]), (6, [6]), (7, [7]), (8, [2]), (9, [2, 4]), (10, [4]), (11, [11]), (12, [12]), (15, [4]), (16, [16]), (17, [17]), (18, [33]), (19, [50]), (20, [20]), (21, [21]), (22, [22]), (23, [23]), (24, [24]), (25, [25]), (26, [26]), (27, [27]), (28, [28]), (29, [29]), (30, [30]), (31, [31]), (32, [32]), (33, [33]), (34, [34]), (35, [35]), (36, [36]), (37, [37]), (38, [38]), (39, [39]), (40, [40]), (41, [41]), (42, [42]), (43, [43]), (44, [44]), (45, [45]), (46, [46]), (47, [47]), (48, [48]), (49, [49]), (50, [50]), (51, [51]), (52, [52])],
    [(-384, [2]), (-368, [2]), (-360, [2, 4]), (-352, [2]), (-328, [39]), (-320, [2]), (-296, [19]), (-288, [18]), (-280, [9]), (-272, [8]), (-256, [1]), (-240, [3]), (-224, [5]), (-216, [6]), (-208, [7]), (-184, [10]), (-176, [11]), (-168, [12]), (-160, [13]), (-152, [14]), (-144, [15]), (-136, [16]), (-128, [17]), (-40, [28]), (-32, [29]), (-24, [30]), (-16, [31])]⟩,
  ⟨[(1, [2]), (2, [2]), (3, [3]), (4, [4]), (5, [5]), (6, [6]), (7, [7]), (8, [2]), (9, [2, 4]), (11, [11]), (12, [12]), (15, [4]), (16, [16]), (17, [17]), (18, [33]), (19, [50]), (20, [20]), (21, [21]), (22, [22]), (23, [23]), (24, [24]), (25, [25]), (26, [26]), (27, [27]), (28, [28]), (29, [29]), (30, [30]), (31, [31]), (32, [32]), (33, [33]), (34, [34]), (35, [35]), (36, [36]), (37, [37]), (38, [38]), (39, [39]), (40, [40]), (41, [41]), (42, [42]), (43, [43]), (44, [44]), (45, [45]), (46, [46]), (47, [47]), (48, [48]), (49, [49]), (50, [50]), (51, [51]), (52, [52])],
    [(-384, [2]), (-368, [2]), (-360, [2, 4]), (-352, [2]), (-328, [39]), (-320, [2]), (-296, [19]), (-288, [18]), (-280, [9]), (-272, [8]), (-256, [1]), (-240, [3]), (-224, [5]), (-216, [6]), (-208, [7]), (-184, [10]), (-176, [11]), (-168, [12]), (-160, [13]), (-152, [14]), (-144, [15]), (-136, [16]), (-128, [17]), (-40, [28]), (-32, [29]), (-24, [30]), (-16, [31])]⟩,
  ⟨[(1, [2]), (2, [2]), (3, [3]), (4, [4]), (5, [5]), (6, [6]), (7, [7]), (8, [2]), (9, [2, 39]), (11, [11]), (12, [12]), (15, [4]), (16, [16]), (17, [17]), (18, [33]), (19, [50]), (20, [20]), (21, [21]), (22, [22]), (23, [23]), (24, [24]), (25, [25]), (26, [26]), (27, [27]), (28, [28]), (29, [29]), (30, [30]), (31, [31]), (32, [32]), (33, [33]), (34, [34]), (35, [35]), (36, [36]), (37, [37]), (38, [38]), (39, [39]), (40, [40]), (41, [41]), (42, [42]), (43, [43]), (44, [44]), (45, [45]), (46, [46]), (47, [47]), (48, [48]), (49, [49]), (50, [50]), (51, [51]), (52, [52])],
    [(-384, [2]), (-368, [2]), (-360, [2, 4]), (-352, [2]), (-328, [39]), (-320, [2]), (-296, [19]), (-288, [18]), (-280, [9]), (-272, [8]), (-256, [1]), (-240, [3]), (-224, [5]), (-216, [6]), (-208, [7]), (-184, [10]), (-176, [11]), (-168, [12]), (-160, [13]), (-152, [14]), (-144, [15]), (-136, [16]), (-128, [17]), (-40, [28]), (-32, [29]), (-24, [30]), (-16, [31])]⟩,
  ⟨[(1, [2]), (2, [2]), (3, [3]), (4, [4]), (5, [5]), (6, [6]), (7, [7]), (8, [2]), (9, [39]), (11, [11]), (12, [12]), (13, [13]), (15, [49]), (16, [16]), (17, [17]), (18, [33]), (19, [50]), (20, [20]), (21, [21]), (22, [22]), (23, [23]), (24, [24]), (25, [25]), (26, [26]), (27, [27]), (28, [28]), (29, [29]), (30, [30]), (31, [31]), (32, [32]), (33, [33]), (34, [34]), (35, [35]), (36, [36]), (37, [37]), (38, [38]), (39, [39]), (40, [40]), (41, [41]), (42, [42]), (43, [43]), (44, [44]), (45, [45]), (46, [46]), (47, [47]), (48, [48]), (49, [49]), (50, [50]), (51, [51]), (52, [49])],
    [(-368, [2]), (-352, [2]), (-320, [2]), (-296, [19]), (-288, [18]), (-280, [9]), (-272, [8]), (-256, [1]), (-240, [3]), (-224, [5]), (-216, [6]), (-208, [7]), (-184, [10]), (-176, [11]), (-168, [12]), (-160, [13]), (-152, [14]), (-144, [15]), (-136, [16]), (-128, [17]), (-40, [28]), (-32, [29]), (-24, [30]), (-16, [31])]⟩,
  ⟨[(2, [2]), (3, [3]), (4, [4]), (5, [5]), (6, [6]), (7, [7]), (8, [8]), (9, [9]), (10, [10]), (11, [11]), (12, [12]), (13, [13]), (14, [14]), (15, [15]), (16, [16]), (17, [17]), (18, [18]), (19, [19]), (20, [20]), (21, [21]), (22, [22]), (23, [23]), (24, [24]), (25, [25]), (26, [26]), (27, [27]), (28, [28]), (29, [29]), (30, [30]), (31, [31]), (32, [32]), (33, [33]), (34, [34]), (35, [35]), (36, [36]), (37, [37]), (38, [38]), (39, [39]), (40, [40]), (41, [41]), (42, [42]), (43, [43]), (44, [44]), (45, [45]), (46, [46]), (47, [47]), (48, [48]), (49, [49]), (50, [50]), (51, [51]), (52, [52])],
    [(-256, [1]), (-240, [3]), (-224, [5]), (-216, [6]), (-208, [7]), (-184, [10]), (-176, [11]), (-168, [12]), (-160, [13]), (-152, [14]), (-144, [15]), (-136, [16]), (-128, [17]), (-40, [28]), (-32, [29]), (-24, [30]), (-16, [31])]⟩,
  ⟨[(2, [2]), (3, [3]), (4, [4]), (5, [5]), (6, [6]), (7, [7]), (8, [8]), (9, [9]), (10, [10]), (11, [11]), (12, [12]), (13, [13]), (14, [14]), (15, [15]), (16, [16]), (17, [17]), (18, [18]), (19, [19]), (20, [20]), (21, [21]), (22, [22]), (23, [23]), (24, [24]), (25, [25]), (26, [26]), (27, [27]), (28, [28]), (29, [29]), (30, [30]), (31, [31]), (32, [32]), (33, [33]), (34, [34]), (35, [35]), (36, [36]), (37, [37]), (38, [38]), (39, [39]), (40, [40]), (41, [41]), (42, [42]), (43, [43]), (44, [44]), (45, [45]), (46, [46]), (47, [47]), (48, [48]), (49, [49]), (50, [50]), (51, [51]), (52, [52])],
    [(-272, [8]), (-256, [1]), (-240, [3]), (-224, [5]), (-216, [6]), (-208, [7]), (-184, [10]), (-176, [11]), (-168, [12]), (-160, [13]), (-152, [14]), (-144, [15]), (-136, [16]), (-128, [17]), (-40, [28]), (-32, [29]), (-24, [30]), (-16, [31])]⟩,
  ⟨[(2, [2]), (3, [3]), (4, [4]), (5, [5]), (6, [6]), (7, [7]), (8, [8]), (9, [9]), (10, [10]), (11, [11]), (12, [12]), (13, [13]), (14, [14]), (15, [15]), (16, [16]), (17, [17]), (18, [18]), (19, [19]), (20, [20]), (21, [21]), (22, [22]), (23, [23]), (24, [24]), (25, [25]), (26, [26]), (27, [27]), (28, [28]), (29, [29]), (30, [30]), (31, [31]), (32, [32]), (33, [33]), (34, [34]), (35, [35]), (36, [36]), (37, [37]), (38, [38]), (39, [39]), (40, [40]), (41, [41]), (42, [42]), (43, [43]), (44, [44]), (45, [45]), (46, [46]), (47, [47]), (48, [48]), (49, [49]), (50, [50]), (51, [51]), (52, [52])],
    [(-280, [9]), (-272, [8]), (-256, [1]), (-240, [3]), (-224, [5]), (-216, [6]), (-208, [7]), (-184, [10]), (-176, [11]), (-168, [12]), (-160, [13]), (-152, [14]), (-144, [15]), (-136, [16]), (-128, [17]), (-40, [28]), (-32, [29]), (-24, [30]), (-16, [31])]⟩,
  ⟨[(2, [2]), (3, [3]), (4, [4]), (5, [5]), (6, [6]), (7, [7]), (8, [8]), (9, [9]), (10, [10]), (11, [11]), (12, [12]), (13, [13]), (14, [14]), (15, [15]), (16, [16]), (17, [17]), (18, [18]), (19, [19]), (20, [20]), (21, [21]), (22, [22]), (23, [23]), (24, [24]), (25, [25]), (26, [26]), (27, [27]), (28, [28]), (29, [29]), (30, [30]), (31, [31]), (32, [32]), (33, [33]), (34, [34]), (35, [35]), (36, [36]), (37, [37]), (38, [38]), (39, [39]), (40, [40]), (41, [41]), (42, [42]), (43, [43]), (44, [44]), (45, [45]), (46, [46]), (47, [47]), (48, [48]), (49, [49]), (50, [50]), (51, [51]), (52, [52])],
    [(-288, [18]), (-280, [9]), (-272, [8]), (-256, [1]), (-240, [3]), (-224, [5]), (-216, [6]), (-208, [7]), (-184, [10]), (-176, [11]), (-168, [12]), (-160, [13]), (-152, [14]), (-144, [15]), (-136, [16]), (-128, [17]), (-40, [28]), (-32, [29]), (-24, [30]), (-16, [31])]⟩,
  ⟨[(2, [2]), (3, [3]), (4, [4]), (5, [5]), (6, [6]), (7, [7]), (8, [8]), (9, [9]), (10, [10]), (11, [11]), (12, [12]), (13, [13]), (14, [14]), (15, [15]), (16, [16]), (17, [17]), (18, [18]), (19, [19]), (20, [20]), (21, [21]), (22, [22]), (23, [23]), (24, [24]), (25, [25]), (26, [26]), (27, [27]), (28, [28]), (29, [29]), (30, [30]), (31, [31]), (32, [32]), (33, [33]), (34, [34]), (35, [35]), (36, [36]), (37, [37]), (38, [38]), (39, [39]), (40, [40]), (41, [41]), (42, [42]), (43, [43]), (44, [44]), (45, [45]), (46, [46]), (47, [47]), (48, [48]), (49, [49]), (50, [50]), (51, [51]), (52, [52])],
    [(-296, [19]), (-288, [18]), (-280, [9]), (-272, [8]), (-256, [1]), (-240, [3]), (-224, [5]), (-216, [6]), (-208, [7]), (-184, [10]), (-176, [11]), (-168, [12]), (-160, [13]), (-152, [14]), (-144, [15]), (-136, [16]), (-128, [17]), (-40, [28]), (-32, [29]), (-24, [30]), (-16, [31])]⟩,
  ⟨[(2, [2]), (3, [3]), (4, [4]), (5, [5]), (6, [6]), (7, [7]), (8, [2]), (9, [9]), (10, [10]), (11, [11]), (12, [12]), (13, [13]), (14, [14]), (15, [15]), (16, [16]), (17, [17]), (18, [18]), (19, [19]), (20, [20]), (21, [21]), (22, [22]), (23, [23]), (24, [24]), (25, [25]), (26, [26]), (27, [27]), (28, [28]), (29, [29]), (30, [30]), (31, [31]), (32, [32]), (33, [33]), (34, [34]), (35, [35]), (36, [36]), (37, [37]), (38, [38]), (39, [39]), (40, [40]), (41, [41]), (42, [42]), (43, [43]), (44, [44]), (45, [45]), (46, [46]), (47, [47]), (48, [48]), (49, [49]), (50, [50]), (51, [51]), (52, [52])],
    [(-296, [19]), (-288, [18]), (-280, [9]), (-272, [8]), (-256, [1]), (-240, [3]), (-224, [5]), (-216, [6]), (-208, [7]), (-184, [10]), (-176, [11]), (-168, [12]), (-160, [13]), (-152, [14]), (-144, [15]), (-136, [16]), (-128, [17]), (-40, [28]), (-32, [29]), (-24, [30]), (-16, [31])]⟩,
  ⟨[(2, [2]), (3, [3]), (4, [4]), (5, [5]), (6, [6]), (7, [7]), (8, [2]), (9, [9]), (10, [10]), (11, [11]), (12, [12]), (13, [13]), (14, [14]), (15, [15]), (16, [16]), (17, [17]), (18, [33]), (19, [19]), (20, [20]), (21, [21]), (22, [22]), (23, [23]), (24, [24]), (25, [25]), (26, [26]), (27, [27]), (28, [28]), (29, [29]), (30, [30]), (31, [31]), (32, [32]), (33, [33]), (34, [34]), (35, [35]), (36, [36]), (37, [37]), (38, [38]), (39, [39]), (40, [40]), (41, [41]), (42, [42]), (43, [43]), (44, [44]), (45, [45]), (46, [46]), (47, [47]), (48, [48]), (49, [49]), (50, [50]), (51, [51]), (52, [52])],
    [(-296, [19]), (-288, [18]), (-280, [9]), (-272, [8]), (-256, [1]), (-240, [3]), (-224, [5]), (-216, [6]), (-208, [7]), (-184, [10]), (-176, [11]), (-168, [12]), (-160, [13]), (-152, [14]), (-144, [15]), (-136, [16]), (-128, [17]), (-40, [28]), (-32, [29]), (-24, [30]), (-16, [31])]⟩,
  ⟨[(2, [2]), (3, [3]), (4, [4]), (5, [5]), (6, [6]), (7, [7]), (8, [2]), (9, [39]), (10, [10]), (11, [11]), (12, [12]), (13, [13]), (14, [14]), (15, [15]), (16, [16]), (17, [17]), (18, [33]), (19, [19]), (20, [20]), (21, [21]), (22, [22]), (23, [23]), (24, [24]), (25, [25]), (26, [26]), (27, [27]), (28, [28]), (29, [29]), (30, [30]), (31, [31]), (32, [32]), (33, [33]), (34, [34]), (35, [35]), (36, [36]), (37, [37]), (38, [38]), (39, [39]), (40, [40]), (41, [41]), (42, [42]), (43, [43]), (44, [44]), (45, [45]), (46, [46]), (47, [47]), (48, [48]), (49, [49]), (50, [50]), (51, [51]), (52, [52])],
    [(-296, [19]), (-288, [18]), (-280, [9]), (-272, [8]), (-256, [1]), (-240, [3]), (-224, [5]), (-216, [6]), (-208, [7]), (-184, [10]), (-176, [11]), (-168, [12]), (-160, [13]), (-152, [14]), (-144, [15]), (-136, [16]), (-128, [17]), (-40, [28]), (-32, [29]), (-24, [30]), (-16, [31])]⟩,
  ⟨[(2, [2]), (3, [3]), (4, [4]), (5, [5]), (6, [6]), (7, [7]), (8, [2]), (9, [39]), (10, [10]), (11, [11]), (12, [12]), (13, [13]), (14, [14]), (15, [50]), (16, [16]), (17, [17]), (18, [33]), (19, [19]), (20, [20]), (21, [21]), (22, [22]), (23, [23]), (24, [24]), (25, [25]), (26, [26]), (27, [27]), (28, [28]), (29, [29]), (30, [30]), (31, [31]), (32, [32]), (33, [33]), (34, [34]), (35, [35]), (36, [36]), (37, [37]), (38, [38]), (39, [39]), (40, [40]), (41, [41]), (42, [42]), (43, [43]), (44, [44]), (45, [45]), (46, [46]), (47, [47]), (48, [48]), (49, [49]), (50, [50]), (51, [51]), (52, [52])],
    [(-296, [19]), (-288, [18]), (-280, [9]), (-272, [8]), (-256, [1]), (-240, [3]), (-224, [5]), (-216, [6]), (-208, [7]), (-184, [10]), (-176, [11]), (-168, [12]), (-160, [13]), (-152, [14]), (-144, [15]), (-136, [16]), (-128, [17]), (-40, [28]), (-32, [29]), (-24, [30]), (-16, [31])]⟩,
  ⟨[(2, [2]), (3, [3]), (4, [4]), (5, [5]), (6, [6]), (7, [7]), (8, [2]), (9, [39]), (10, [10]), (11, [11]), (12, [12]), (13, [13]), (14, [14]), (15, [50]), (16, [16]), (17, [17]), (18, [33]), (19, [50]), (20, [20]), (21, [21]), (22, [22]), (23, [23]), (24, [24]), (25, [25]), (26, [26]), (27, [27]), (28, [28]), (29, [29]), (30, [30]), (31, [31]), (32, [32]), (33, [33]), (34, [34]), (35, [35]), (36, [36]), (37, [37]), (38, [38]), (39, [39]), (40, [40]), (41, [41]), (42, [42]), (43, [43]), (44, [44]), (45, [45]), (46, [46]), (47, [47]), (48, [48]), (49, [49]), (50, [50]), (51, [51]), (52, [52])],
    [(-296, [19]), (-288, [18]), (-280, [9]), (-272, [8]), (-256, [1]), (-240, [3]), (-224, [5]), (-216, [6]), (-208, [7]), (-184, [10]), (-176, [11]), (-168, [12]), (-160, [13]), (-152, [14]), (-144, [15]), (-136, [16]), (-128, [17]), (-40, [28]), (-32, [29]), (-24, [30]), (-16, [31])]⟩,
  ⟨[(1, [2]), (2, [2]), (3, [3]), (4, [4]), (5, [5]), (6, [6]), (7, [7]), (8, [2, 8]), (9, [39]), (11, [11]), (12, [12]), (16, [16]), (17, [17]), (18, [33]), (19, [50]), (20, [20]), (21, [21]), (22, [22]), (23, [23]), (24, [24]), (25, [25]), (26, [26]), (27, [27]), (28, [28]), (29, [29]), (30, [30]), (31, [31]), (32, [32]), (33, [33]), (34, [34]), (35, [35]), (36, [36]), (37, [37]), (38, [38]), (39, [39]), (40, [40]), (41, [41]), (42, [42]), (43, [43]), (44, [44]), (45, [45]), (46, [46]), (47, [47]), (48, [48]), (49, [49]), (50, [50]), (51, [51])],
    [(-320, [2]), (-296, [19]), (-288, [18]), (-280, [9]), (-272, [8]), (-256, [1]), (-240, [3]), (-224, [5]), (-216, [6]), (-208, [7]), (-184, [10]), (-176, [11]), (-168, [12]), (-160, [13]), (-152, [14]), (-144, [15]), (-136, [16]), (-128, [17]), (-40, [28]), (-32, [29]), (-24, [30]), (-16, [31])]⟩,
  ⟨[(1, [2]), (2, [2]), (3, [3]), (4, [4]), (5, [5]), (6, [6]), (7, [7]), (8, [2, 8]), (9, [2, 9]), (11, [11]), (12, [12]), (16, [16]), (17, [17]), (18, [33]), (19, [50]), (20, [20]), (21, [21]), (22, [22]), (23, [23]), (24, [24]), (25, [25]), (26, [26]), (27, [27]), (28, [28]), (29, [29]), (30, [30]), (31, [31]), (32, [32]), (33, [33]), (34, [34]), (35, [35]), (36, [36]), (37, [37]), (38, [38]), (39, [39]), (40, [40]), (41, [41]), (42, [42]), (43, [43]), (44, [44]), (45, [45]), (46, [46]), (47, [47]), (48, [48]), (49, [49]), (50, [50]), (51, [51])],
    [(-320, [2]), (-296, [19]), (-288, [18]), (-280, [9]), (-272, [8]), (-256, [1]), (-240, [3]), (-224, [5]), (-216, [6]), (-208, [7]), (-184, [10]), (-176, [11]), (-168, [12]), (-160, [13]), (-152, [14]), (-144, [15]), (-136, [16]), (-128, [17]), (-40, [28]), (-32, [29]), (-24, [30]), (-16, [31])]⟩,
  ⟨[(1, [2]), (2, [2]), (3, [3]), (4, [4]), (5, [5]), (6, [6]), (7, [7]), (8, [2, 8]), (9, [2, 9]), (11, [11]), (12, [12]), (16, [16]), (17, [17]), (18, [2, 18]), (19, [50]), (20, [20]), (21, [21]), (22, [22]), (23, [23]), (24, [24]), (25, [25]), (26, [26]), (27, [27]), (28, [28]), (29, [29]), (30, [30]), (31, [31]), (32, [32]), (33, [33]), (34, [34]), (35, [35]), (36, [36]), (37, [37]), (38, [38]), (39, [39]), (40, [40]), (41, [41]), (42, [42]), (43, [43]), (44, [44]), (45, [45]), (46, [46]), (47, [47]), (48, [48]), (49, [49]), (50, [50]), (51, [51])],
    [(-320, [2]), (-296, [19]), (-288, [18]), (-280, [9]), (-272, [8]), (-256, [1]), (-240, [3]), (-224, [5]), (-216, [6]), (-208, [7]), (-184, [10]), (-176, [11]), (-168, [12]), (-160, [13]), (-152, [14]), (-144, [15]), (-136, [16]), (-128, [17]), (-40, [28]), (-32, [29]), (-24, [30]), (-16, [31])]⟩,
  ⟨[(1, [2]), (2, [2]), (3, [3]), (4, [4]), (5, [5]), (6, [6]), (7, [7]), (8, [2, 8]), (9, [2, 9]), (11, [11]), (12, [12]), (16, [16]), (17, [17]), (18, [2, 18]), (19, [2, 19]), (20, [20]), (21, [21]), (22, [22]), (23, [23]), (24, [24]), (25, [25]), (26, [26]), (27, [27]), (28, [28]), (29, [29]), (30, [30]), (31, [31]), (32, [32]), (33, [33]), (34, [34]), (35, [35]), (36, [36]), (37, [37]), (38, [38]), (39, [39]), (40, [40]), (41, [41]), (42, [42]), (43, [43]), (44, [44]), (45, [45]), (46, [46]), (47, [47]), (48, [48]), (49, [49]), (50, [50]), (51, [51])],
    [(-320, [2]), (-296, [19]), (-288, [18]), (-280, [9]), (-272, [8]), (-256, [1]), (-240, [3]), (-224, [5]), (-216, [6]), (-208, [7]), (-184, [10]), (-176, [11]), (-168, [12]), (-160, [13]), (-152, [14]), (-144, [15]), (-136, [16]), (-128, [17]), (-40, [28]), (-32, [29]), (-24, [30]), (-16, [31])]⟩,
  ⟨[(1, [1]), (2, [2]), (3, [3]), (4, [4]), (5, [5]), (6, [6]), (7, [7]), (8, [8]), (9, [9]), (10, [10]), (11, [11]), (12, [12]), (13, [13]), (14, [14]), (15, [15]), (16, [16]), (17, [17]), (18, [18]), (19, [19]), (20, [20]), (21, [21]), (22, [22]), (23, [23]), (24, [24]), (25, [25]), (26, [26]), (27, [27]), (28, [28]), (29, [29]), (30, [30]), (31, [31]), (32, [32]), (33, [33]), (34, [34]), (35, [35]), (36, [36]), (37, [37]), (38, [38]), (39, [39]), (40, [40]), (41, [41]), (42, [42]), (43, [43]), (44, [44]), (45, [45]), (46, [46]), (47, [47]), (48, [48]), (49, [49]), (50, [50]), (51, [51]), (52, [52])],
    []⟩,
  ⟨[(1, [1]), (2, [2]), (3, [3]), (4, [4]), (5, [5]), (6, [6]), (7, [7]), (8, [8]), (9, [9]), (10, [10]), (11, [11]), (12, [12]), (13, [13]), (14, [14]), (15, [15]), (16, [16]), (17, [17]), (18, [18]), (19, [19]), (20, [20]), (21, [21]), (22, [22]), (23, [23]), (24, [24]), (25, [25]), (26, [26]), (27, [27]), (28, [28]), (29, [29]), (30, [30]), (31, [31]), (32, [32]), (33, [33]), (34, [34]), (35, [35]), (36, [36]), (37, [37]), (38, [38]), (39, [39]), (40, [40]), (41, [41]), (42, [42]), (43, [43]), (44, [44]), (45, [45]), (46, [46]), (47, [47]), (48, [48]), (49, [49]), (50, [50]), (51, [51]), (52, [52])],
    [(-256, [1])]⟩,
  ⟨[(1, [1]), (2, [2]), (3, [3]), (4, [4]), (5, [5]), (6, [6]), (7, [7]), (8, [8]), (9, [9]), (10, [10]), (11, [11]), (12, [12]), (13, [13]), (14, [14]), (15, [15]), (16, [16]), (17, [17]), (18, [18]), (19, [19]), (20, [20]), (21, [21]), (22, [22]), (23, [23]), (24, [24]), (25, [25]), (26, [26]), (27, [27]), (28, [28]), (29, [29]), (30, [30]), (31, [31]), (32, [32]), (33, [33]), (34, [34]), (35, [35]), (36, [36]), (37, [37]), (38, [38]), (39, [39]), (40, [40]), (41, [41]), (42, [42]), (43, [43]), (44, [44]), (45, [45]), (46, [46]), (47, [47]), (48, [48]), (49, [49]), (50, [50]), (51, [51]), (52, [52])],
    [(-256, [1]), (-240, [3])]⟩,
  ⟨[(1, [1]), (2, [2]), (3, [3]), (4, [4]), (5, [5]), (6, [6]), (7, [7]), (8, [8]), (9, [9]), (10, [10]), (11, [11]), (12, [12]), (13, [13]), (14, [14]), (15, [15]), (16, [16]), (17, [17]), (18, [18]), (19, [19]), (20, [20]), (21, [21]), (22, [22]), (23, [23]), (24, [24]), (25, [25]), (26, [26]), (27, [27]), (28, [28]), (29, [29]), (30, [30]), (31, [31]), (32, [32]), (33, [33]), (34, [34]), (35, [35]), (36, [36]), (37, [37]), (38, [38]), (39, [39]), (40, [40]), (41, [41]), (42, [42]), (43, [43]), (44, [44]), (45, [45]), (46, [46]), (47, [47]), (48, [48]), (49, [49]), (50, [50]), (51, [51]), (52, [52])],
    [(-256, [1]), (-240, [3]), (-224, [5])]⟩,
  ⟨[(1, [1]), (2, [2]), (3, [3]), (4, [4]), (5, [5]), (6, [6]), (7, [7]), (8, [8]), (9, [9]), (10, [10]), (11, [11]), (12, [12]), (13, [13]), (14, [14]), (15, [15]), (16, [16]), (17, [17]), (18, [18]), (19, [19]), (20, [20]), (21, [21]), (22, [22]), (23, [23]), (24, [24]), (25, [25]), (26, [26]), (27, [27]), (28, [28]), (29, [29]), (30, [30]), (31, [31]), (32, [32]), (33, [33]), (34, [34]), (35, [35]), (36, [36]), (37, [37]), (38, [38]), (39, [39]), (40, [40]), (41, [41]), (42, [42]), (43, [43]), (44, [44]), (45, [45]), (46, [46]), (47, [47]), (48, [48]), (49, [49]), (50, [50]), (51, [51]), (52, [52])],
    [(-256, [1]), (-240, [3]), (-224, [5]), (-216, [6])]⟩,
  ⟨[(1, [1]), (2, [2]), (3, [3]), (4, [4]), (5, [5]), (6, [6]), (7, [7]), (8, [8]), (9, [9]), (10, [10]), (11, [11]), (12, [12]), (13, [13]), (14, [14]), (15, [15]), (16, [16]), (17, [17]), (18, [18]), (19, [19]), (20, [20]), (21, [21]), (22, [22]), (23, [23]), (24, [24]), (25, [25]), (26, [26]), (27, [27]), (28, [28]), (29, [29]), (30, [30]), (31, [31]), (32, [32]), (33, [33]), (34, [34]), (35, [35]), (36, [36]), (37, [37]), (38, [38]), (39, [39]), (40, [40]), (41, [41]), (42, [42]), (43, [43]), (44, [44]), (45, [45]), (46, [46]), (47, [47]), (48, [48]), (49, [49]), (50, [50]), (51, [51]), (52, [52])],
    [(-256, [1]), (-240, [3]), (-224, [5]), (-216, [6]), (-208, [7])]⟩,
  ⟨[(1, [1]), (2, [2]), (3, [3]), (4, [4]), (5, [5]), (6, [6]), (7, [7]), (8, [8]), (9, [9]), (10, [10]), (11, [11]), (12, [12]), (13, [13]), (14, [14]), (15, [15]), (16, [16]), (17, [17]), (18, [18]), (19, [19]), (20, [20]), (21, [21]), (22, [22]), (23, [23]), (24, [24]), (25, [25]), (26, [26]), (27, [27]), (28, [28]), (29, [29]), (30, [30]), (31, [31]), (32, [32]), (33, [33]), (34, [34]), (35, [35]), (36, [36]), (37, [37]), (38, [38]), (39, [39]), (40, [40]), (41, [41]), (42, [42]), (43, [43]), (44, [44]), (45, [45]), (46, [46]), (47, [47]), (48, [48]), (49, [49]), (50, [50]), (51, [51]), (52, [52])],
    [(-256, [1]), (-240, [3]), (-224, [5]), (-216, [6]), (-208, [7]), (-184, [10])]⟩,
  ⟨[(1, [1]), (2, [2]), (3, [3]), (4, [4]), (5, [5]), (6, [6]), (7, [7]), (8, [8]), (9, [9]), (10, [10]), (11, [11]), (12, [12]), (13, [13]), (14, [14]), (15, [15]), (16, [16]), (17, [17]), (18, [18]), (19, [19]), (20, [20]), (21, [21]), (22, [22]), (23, [23]), (24, [24]), (25, [25]), (26, [26]), (27, [27]), (28, [28]), (29, [29]), (30, [30]), (31, [31]), (32, [32]), (33, [33]), (34, [34]), (35, [35]), (36, [36]), (37, [37]), (38, [38]), (39, [39]), (40, [40]), (41, [41]), (42, [42]), (43, [43]), (44, [44]), (45, [45]), (46, [46]), (47, [47]), (48, [48]), (49, [49]), (50, [50]), (51, [51]), (52, [52])],
    [(-256, [1]), (-240, [3]), (-224, [5]), (-216, [6]), (-208, [7]), (-184, [10]), (-176, [11])]⟩,
  ⟨[(1, [1]), (2, [2]), (3, [3]), (4, [4]), (5, [5]), (6, [6]), (7, [7]), (8, [8]), (9, [9]), (10, [10]), (11, [11]), (12, [12]), (13, [13]), (14, [14]), (15, [15]), (16, [16]), (17, [17]), (18, [18]), (19, [19]), (20, [20]), (21, [21]), (22, [22]), (23, [23]), (24, [24]), (25, [25]), (26, [26]), (27, [27]), (28, [28]), (29, [29]), (30, [30]), (31, [31]), (32, [32]), (33, [33]), (34, [34]), (35, [35]), (36, [36]), (37, [37]), (38, [38]), (39, [39]), (40, [40]), (41, [41]), (42, [42]), (43, [43]), (44, [44]), (45, [45]), (46, [46]), (47, [47]), (48, [48]), (49, [49]), (50, [50]), (51, [51]), (52, [52])],
    [(-256, [1]), (-240, [3]), (-224, [5]), (-216, [6]), (-208, [7]), (-184, [10]), (-176, [11]), (-168, [12])]⟩,
  ⟨[(1, [1]), (2, [2]), (3, [3]), (4, [4]), (5, [5]), (6, [6]), (7, [7]), (8, [8]), (9, [9]), (10, [10]), (11, [11]), (12, [12]), (13, [13]), (14, [14]), (15, [15]), (16, [16]), (17, [17]), (18, [18]), (19, [19]), (20, [20]), (21, [21]), (22, [22]), (23, [23]), (24, [24]), (25, [25]), (26, [26]), (27, [27]), (28, [28]), (29, [29]), (30, [30]), (31, [31]), (32, [32]), (33, [33]), (34, [34]), (35, [35]), (36, [36]), (37, [37]), (38, [38]), (39, [39]), (40, [40]), (41, [41]), (42, [42]), (43, [43]), (44, [44]), (45, [45]), (46, [46]), (47, [47]), (48, [48]), (49, [49]), (50, [50]), (51, [51]), (52, [52])],
    [(-256, [1]), (-240, [3]), (-224, [5]), (-216, [6]), (-208, [7]), (-184, [10]), (-176, [11]), (-168, [12]), (-160, [13])]⟩,
  ⟨[(1, [1]), (2, [2]), (3, [3]), (4, [4]), (5, [5]), (6, [6]), (7, [7]), (8, [8]), (9, [9]), (10, [10]), (11, [11]), (12, [12]), (13, [13]), (14, [14]), (15, [15]), (16, [16]), (17, [17]), (18, [18]), (19, [19]), (20, [20]), (21, [21]), (22, [22]), (23, [23]), (24, [24]), (25, [25]), (26, [26]), (27, [27]), (28, [28]), (29, [29]), (30, [30]), (31, [31]), (32, [32]), (33, [33]), (34, [34]), (35, [35]), (36, [36]), (37, [37]), (38, [38]), (39, [39]), (40, [40]), (41, [41]), (42, [42]), (43, [43]), (44, [44]), (45, [45]), (46, [46]), (47, [47]), (48, [48]), (49, [49]), (50, [50]), (51, [51]), (52, [52])],
    [(-256, [1]), (-240, [3]), (-224, [5]), (-216, [6]), (-208, [7]), (-184, [10]), (-176, [11]), (-168, [12]), (-160, [13]), (-152, [14])]⟩,
  ⟨[(1, [1]), (2, [2]), (3, [3]), (4, [4]), (5, [5]), (6, [6]), (7, [7]), (8, [8]), (9, [9]), (10, [10]), (11, [11]), (12, [12]), (13, [13]), (14, [14]), (15, [15]), (16, [16]), (17, [17]), (18, [18]), (19, [19]), (20, [20]), (21, [21]), (22, [22]), (23, [23]), (24, [24]), (25, [25]), (26, [26]), (27, [27]), (28, [28]), (29, [29]), (30, [30]), (31, [31]), (32, [32]), (33, [33]), (34, [34]), (35, [35]), (36, [36]), (37, [37]), (38, [38]), (39, [39]), (40, [40]), (41, [41]), (42, [42]), (43, [43]), (44, [44]), (45, [45]), (46, [46]), (47, [47]), (48, [48]), (49, [49]), (50, [50]), (51, [51]), (52, [52])],
    [(-256, [1]), (-240, [3]), (-224, [5]), (-216, [6]), (-208, [7]), (-184, [10]), (-176, [11]), (-168, [12]), (-160, [13]), (-152, [14]), (-144, [15])]⟩,
  ⟨[(1, [1]), (2, [2]), (3, [3]), (4, [4]), (5, [5]), (6, [6]), (7, [7]), (8, [8]), (9, [9]), (10, [10]), (11, [11]), (12, [12]), (13, [13]), (14, [14]), (15, [15]), (16, [16]), (17, [17]), (18, [18]), (19, [19]), (20, [20]), (21, [21]), (22, [22]), (23, [23]), (24, [24]), (25, [25]), (26, [26]), (27, [27]), (28, [28]), (29, [29]), (30, [30]), (31, [31]), (32, [32]), (33, [33]), (34, [34]), (35, [35]), (36, [36]), (37, [37]), (38, [38]), (39, [39]), (40, [40]), (41, [41]), (42, [42]), (43, [43]), (44, [44]), (45, [45]), (46, [46]), (47, [47]), (48, [48]), (49, [49]), (50, [50]), (51, [51]), (52, [52])],
    [(-256, [1]), (-240, [3]), (-224, [5]), (-216, [6]), (-208, [7]), (-184, [10]), (-176, [11]), (-168, [12]), (-160, [13]), (-152, [14]), (-144, [15]), (-136, [16])]⟩,
  ⟨[(1, [1]), (2, [2]), (3, [3]), (4, [4]), (5, [5]), (6, [6]), (7, [7]), (8, [8]), (9, [9]), (10, [10]), (11, [11]), (12, [12]), (13, [13]), (14, [14]), (15, [15]), (16, [16]), (17, [17]), (18, [18]), (19, [19]), (20, [20]), (21, [21]), (22, [22]), (23, [23]), (24, [24]), (25, [25]), (26, [26]), (27, [27]), (28, [28]), (29, [29]), (30, [30]), (31, [31]), (32, [32]), (33, [33]), (34, [34]), (35, [35]), (36, [36]), (37, [37]), (38, [38]), (39, [39]), (40, [40]), (41, [41]), (42, [42]), (43, [43]), (44, [44]), (45, [45]), (46, [46]), (47, [47]), (48, [48]), (49, [49]), (50, [50]), (51, [51]), (52, [52])],
    [(-256, [1]), (-240, [3]), (-224, [5]), (-216, [6]), (-208, [7]), (-184, [10]), (-176, [11]), (-168, [12]), (-160, [13]), (-152, [14]), (-144, [15]), (-136, [16]), (-128, [17])]⟩,
  ⟨[(1, [1]), (2, [2]), (3, [3]), (4, [4]), (5, [5]), (6, [6]), (7, [7]), (8, [8]), (9, [9]), (10, [10]), (11, [11]), (12, [12]), (13, [13]), (14, [14]), (15, [15]), (16, [16]), (17, [17]), (18, [18]), (19, [19]), (20, [20]), (21, [21]), (22, [22]), (23, [23]), (24, [24]), (25, [25]), (26, [26]), (27, [27]), (28, [28]), (29, [29]), (30, [30]), (31, [31]), (32, [32]), (33, [33]), (34, [34]), (35, [35]), (36, [36]), (37, [37]), (38, [38]), (39, [39]), (40, [40]), (41, [41]), (42, [42]), (43, [43]), (44, [44]), (45, [45]), (46, [46]), (47, [47]), (48, [48]), (49, [49]), (50, [50]), (51, [51]), (52, [52])],
    [(-256, [1]), (-240, [3]), (-224, [5]), (-216, [6]), (-208, [7]), (-184, [10]), (-176, [11]), (-168, [12]), (-160, [13]), (-152, [14]), (-144, [15]), (-136, [16]), (-128, [17]), (-40, [28])]⟩,
  ⟨[(1, [1]), (2, [2]), (3, [3]), (4, [4]), (5, [5]), (6, [6]), (7, [7]), (8, [8]), (9, [9]), (10, [10]), (11, [11]), (12, [12]), (13, [13]), (14, [14]), (15, [15]), (16, [16]), (17, [17]), (18, [18]), (19, [19]), (20, [20]), (21, [21]), (22, [22]), (23, [23]), (24, [24]), (25, [25]), (26, [26]), (27, [27]), (28, [28]), (29, [29]), (30, [30]), (31, [31]), (32, [32]), (33, [33]), (34, [34]), (35, [35]), (36, [36]), (37, [37]), (38, [38]), (39, [39]), (40, [40]), (41, [41]), (42, [42]), (43, [43]), (44, [44]), (45, [45]), (46, [46]), (47, [47]), (48, [48]), (49, [49]), (50, [50]), (51, [51]), (52, [52])],
    [(-256, [1]), (-240, [3]), (-224, [5]), (-216, [6]), (-208, [7]), (-184, [10]), (-176, [11]), (-168, [12]), (-160, [13]), (-152, [14]), (-144, [15]), (-136, [16]), (-128, [17]), (-40, [28]), (-32, [29])]⟩,
  ⟨[(1, [1]), (2, [2]), (3, [3]), (4, [4]), (5, [5]), (6, [6]), (7, [7]), (8, [8]), (9, [9]), (10, [10]), (11, [11]), (12, [12]), (13, [13]), (14, [14]), (15, [15]), (16, [16]), (17, [17]), (18, [18]), (19, [19]), (20, [20]), (21, [21]), (22, [22]), (23, [23]), (24, [24]), (25, [25]), (26, [26]), (27, [27]), (28, [28]), (29, [29]), (30, [30]), (31, [31]), (32, [32]), (33, [33]), (34, [34]), (35, [35]), (36, [36]), (37, [37]), (38, [38]), (39, [39]), (40, [40]), (41, [41]), (42, [42]), (43, [43]), (44, [44]), (45, [45]), (46, [46]), (47, [47]), (48, [48]), (49, [49]), (50, [50]), (51, [51]), (52, [52])],
    [(-256, [1]), (-240, [3]), (-224, [5]), (-216, [6]), (-208, [7]), (-184, [10]), (-176, [11]), (-168, [12]), (-160, [13]), (-152, [14]), (-144, [15]), (-136, [16]), (-128, [17]), (-40, [28]), (-32, [29]), (-24, [30])]⟩,
  ⟨[(1, [1]), (2, [2]), (3, [3]), (4, [4]), (5, [5]), (6, [6]), (7, [7]), (8, [8]), (9, [9]), (10, [10]), (11, [11]), (12, [12]), (13, [13]), (14, [14]), (15, [15]), (16, [16]), (17, [17]), (18, [18]), (19, [19]), (20, [20]), (21, [21]), (22, [22]), (23, [23]), (24, [24]), (25, [25]), (26, [26]), (27, [27]), (28, [28]), (29, [29]), (30, [30]), (31, [31]), (32, [32]), (33, [33]), (34, [34]), (35, [35]), (36, [36]), (37, [37]), (38, [38]), (39, [39]), (40, [40]), (41, [41]), (42, [42]), (43, [43]), (44, [44]), (45, [45]), (46, [46]), (47, [47]), (48, [48]), (49, [49]), (50, [50]), (51, [51]), (52, [52])],
    [(-256, [1]), (-240, [3]), (-224, [5]), (-216, [6]), (-208, [7]), (-184, [10]), (-176, [11]), (-168, [12]), (-160, [13]), (-152, [14]), (-144, [15]), (-136, [16]), (-128, [17]), (-40, [28]), (-32, [29]), (-24, [30]), (-16, [31])]⟩,
  ⟨[(1, [1, 2]), (2, [2]), (3, [3]), (4, [4]), (5, [5]), (6, [6]), (7, [7]), (8, [2, 8]), (9, [2, 9]), (11, [11]), (12, [12]), (16, [16]), (17, [17]), (18, [2, 18]), (19, [2, 19]), (20, [20]), (21, [21]), (22, [22]), (23, [23]), (24, [24]), (25, [25]), (26, [26]), (27, [27]), (28, [28]), (29, [29]), (30, [30]), (31, [31]), (32, [32]), (33, [33]), (34, [34]), (35, [35]), (36, [36]), (37, [37]), (38, [38]), (39, [39]), (40, [40]), (41, [41]), (42, [42]), (43, [43]), (44, [44]), (45, [45]), (46, [46]), (47, [47]), (48, [48]), (49, [49]), (50, [50]), (51, [51])],
    [(-320, [2]), (-296, [19]), (-288, [18]), (-280, [9]), (-272, [8]), (-256, [1]), (-240, [3]), (-224, [5]), (-216, [6]), (-208, [7]), (-184, [10]), (-176, [11]), (-168, [12]), (-160, [13]), (-152, [14]), (-144, [15]), (-136, [16]), (-128, [17]), (-40, [28]), (-32, [29]), (-24, [30]), (-16, [31])]⟩,
  ⟨[(1, [1, 2]), (2, [2]), (3, [2, 3]), (4, [4]), (5, [5]), (6, [6]), (7, [7]), (8, [2, 8]), (9, [2, 9]), (11, [11]), (12, [12]), (16, [16]), (17, [17]), (18, [2, 18]), (19, [2, 19]), (20, [20]), (21, [21]), (22, [22]), (23, [23]), (24, [24]), (25, [25]), (26, [26]), (27, [27]), (28, [28]), (29, [29]), (30, [30]), (31, [31]), (32, [32]), (33, [33]), (34, [34]), (35, [35]), (36, [36]), (37, [37]), (38, [38]), (39, [39]), (40, [40]), (41, [41]), (42, [42]), (43, [43]), (44, [44]), (45, [45]), (46, [46]), (47, [47]), (48, [48]), (49, [49]), (50, [50]), (51, [51])],
    [(-320, [2]), (-296, [19]), (-288, [18]), (-280, [9]), (-272, [8]), (-256, [1]), (-240, [3]), (-224, [5]), (-216, [6]), (-208, [7]), (-184, [10]), (-176, [11]), (-168, [12]), (-160, [13]), (-152, [14]), (-144, [15]), (-136, [16]), (-128, [17]), (-40, [28]), (-32, [29]), (-24, [30]), (-16, [31])]⟩,
  ⟨[(1, [1, 2]), (2, [2]), (3, [2, 3]), (4, [4]), (5, [2, 5]), (6, [6]), (7, [7]), (8, [2, 8]), (9, [2, 9]), (11, [11]), (12, [12]), (16, [16]), (17, [17]), (18, [2, 18]), (19, [2, 19]), (20, [20]), (21, [21]), (22, [22]), (23, [23]), (24, [24]), (25, [25]), (26, [26]), (27, [27]), (28, [28]), (29, [29]), (30, [30]), (31, [31]), (32, [32]), (33, [33]), (34, [34]), (35, [35]), (36, [36]), (37, [37]), (38, [38]), (39, [39]), (40, [40]), (41, [41]), (42, [42]), (43, [43]), (44, [44]), (45, [45]), (46, [46]), (47, [47]), (48, [48]), (49, [49]), (50, [50]), (51, [51])],
    [(-320, [2]), (-296, [19]), (-288, [18]), (-280, [9]), (-272, [8]), (-256, [1]), (-240, [3]), (-224, [5]), (-216, [6]), (-208, [7]), (-184, [10]), (-176, [11]), (-168, [12]), (-160, [13]), (-152, [14]), (-144, [15]), (-136, [16]), (-128, [17]), (-40, [28]), (-32, [29]), (-24, [30]), (-16, [31])]⟩,
  ⟨[(1, [1, 2]), (2, [2]), (3, [2, 3]), (4, [4]), (5, [2, 5]), (6, [2, 6]), (7, [7]), (8, [2, 8]), (9, [2, 9]), (11, [11]), (12, [12]), (16, [16]), (17, [17]), (18, [2, 18]), (19, [2, 19]), (20, [20]), (21, [21]), (22, [22]), (23, [23]), (24, [24]), (25, [25]), (26, [26]), (27, [27]), (28, [28]), (29, [29]), (30, [30]), (31, [31]), (32, [32]), (33, [33]), (34, [34]), (35, [35]), (36, [36]), (37, [37]), (38, [38]), (39, [39]), (40, [40]), (41, [41]), (42, [42]), (43, [43]), (44, [44]), (45, [45]), (46, [46]), (47, [47]), (48, [48]), (49, [49]), (50, [50]), (51, [51])],
    [(-320, [2]), (-296, [19]), (-288, [18]), (-280, [9]), (-272, [8]), (-256, [1]), (-240, [3]), (-224, [5]), (-216, [6]), (-208, [7]), (-184, [10]), (-176, [11]), (-168, [12]), (-160, [13]), (-152, [14]), (-144, [15]), (-136, [16]), (-128, [17]), (-40, [28]), (-32, [29]), (-24, [30]), (-16, [31])]⟩,
  ⟨[(1, [1, 2]), (2, [2]), (3, [2, 3]), (4, [4]), (5, [2, 5]), (6, [2, 6]), (7, [2, 7]), (8, [2, 8]), (9, [2, 9]), (11, [11]), (12, [12]), (16, [16]), (17, [17]), (18, [2, 18]), (19, [2, 19]), (20, [20]), (21, [21]), (22, [22]), (23, [23]), (24, [24]), (25, [25]), (26, [26]), (27, [27]), (28, [28]), (29, [29]), (30, [30]), (31, [31]), (32, [32]), (33, [33]), (34, [34]), (35, [35]), (36, [36]), (37, [37]), (38, [38]), (39, [39]), (40, [40]), (41, [41]), (42, [42]), (43, [43]), (44, [44]), (45, [45]), (46, [46]), (47, [47]), (48, [48]), (49, [49]), (50, [50]), (51, [51])],
    [(-320, [2]), (-296, [19]), (-288, [18]), (-280, [9]), (-272, [8]), (-256, [1]), (-240, [3]), (-224, [5]), (-216, [6]), (-208, [7]), (-184, [10]), (-176, [11]), (-168, [12]), (-160, [13]), (-152, [14]), (-144, [15]), (-136, [16]), (-128, [17]), (-40, [28]), (-32, [29]), (-24, [30]), (-16, [31])]⟩,
  ⟨[(1, [1, 2]), (2, [2]), (3, [2, 3]), (4, [4]), (5, [2, 5]), (6, [2, 6]), (7, [2, 7]), (8, [2, 8]), (9, [2, 9]), (10, [2, 10]), (11, [11]), (12, [12]), (16, [16]), (17, [17]), (18, [2, 18]), (19, [2, 19]), (20, [20]), (21, [21]), (22, [22]), (23, [23]), (24, [24]), (25, [25]), (26, [26]), (27, [27]), (28, [28]), (29, [29]), (30, [30]), (31, [31]), (32, [32]), (33, [33]), (34, [34]), (35, [35]), (36, [36]), (37, [37]), (38, [38]), (39, [39]), (40, [40]), (41, [41]), (42, [42]), (43, [43]), (44, [44]), (45, [45]), (46, [46]), (47, [47]), (48, [48]), (49, [49]), (50, [50]), (51, [51])],
    [(-320, [2]), (-296, [19]), (-288, [18]), (-280, [9]), (-272, [8]), (-256, [1]), (-240, [3]), (-224, [5]), (-216, [6]), (-208, [7]), (-184, [10]), (-176, [11]), (-168, [12]), (-160, [13]), (-152, [14]), (-144, [15]), (-136, [16]), (-128, [17]), (-40, [28]), (-32, [29]), (-24, [30]), (-16, [31])]⟩,
  ⟨[(1, [1, 2]), (2, [2]), (3, [2, 3]), (4, [4]), (5, [2, 5]), (6, [2, 6]), (7, [2, 7]), (8, [2, 8]), (9, [2, 9]), (10, [2, 10]), (11, [2, 11]), (12, [12]), (16, [16]), (17, [17]), (18, [2, 18]), (19, [2, 19]), (20, [20]), (21, [21]), (22, [22]), (23, [23]), (24, [24]), (25, [25]), (26, [26]), (27, [27]), (28, [28]), (29, [29]), (30, [30]), (31, [31]), (32, [32]), (33, [33]), (34, [34]), (35, [35]), (36, [36]), (37, [37]), (38, [38]), (39, [39]), (40, [40]), (41, [41]), (42, [42]), (43, [43]), (44, [44]), (45, [45]), (46, [46]), (47, [47]), (48, [48]), (49, [49]), (50, [50]), (51, [51])],
    [(-320, [2]), (-296, [19]), (-288, [18]), (-280, [9]), (-272, [8]), (-256, [1]), (-240, [3]), (-224, [5]), (-216, [6]), (-208, [7]), (-184, [10]), (-176, [11]), (-168, [12]), (-160, [13]), (-152, [14]), (-144, [15]), (-136, [16]), (-128, [17]), (-40, [28]), (-32, [29]), (-24, [30]), (-16, [31])]⟩,
  ⟨[(1, [1, 2]), (2, [2]), (3, [2, 3]), (4, [4]), (5, [2, 5]), (6, [2, 6]), (7, [2, 7]), (8, [2, 8]), (9, [2, 9]), (10, [2, 10]), (11, [2, 11]), (12, [2, 12]), (16, [16]), (17, [17]), (18, [2, 18]), (19, [2, 19]), (20, [20]), (21, [21]), (22, [22]), (23, [23]), (24, [24]), (25, [25]), (26, [26]), (27, [27]), (28, [28]), (29, [29]), (30, [30]), (31, [31]), (32, [32]), (33, [33]), (34, [34]), (35, [35]), (36, [36]), (37, [37]), (38, [38]), (39, [39]), (40, [40]), (41, [41]), (42, [42]), (43, [43]), (44, [44]), (45, [45]), (46, [46]), (47, [47]), (48, [48]), (49, [49]), (50, [50]), (51, [51])],
    [(-320, [2]), (-296, [19]), (-288, [18]), (-280, [9]), (-272, [8]), (-256, [1]), (-240, [3]), (-224, [5]), (-216, [6]), (-208, [7]), (-184, [10]), (-176, [11]), (-168, [12]), (-160, [13]), (-152, [14]), (-144, [15]), (-136, [16]), (-128, [17]), (-40, [28]), (-32, [29]), (-24, [30]), (-16, [31])]⟩,
  ⟨[(1, [1, 2]), (2, [2]), (3, [2, 3]), (4, [4]), (5, [2, 5]), (6, [2, 6]), (7, [2, 7]), (8, [2, 8]), (9, [2, 9]), (10, [2, 10]), (11, [2, 11]), (12, [2, 12]), (13, [2, 13]), (16, [16]), (17, [17]), (18, [2, 18]), (19, [2, 19]), (20, [20]), (21, [21]), (22, [22]), (23, [23]), (24, [24]), (25, [25]), (26, [26]), (27, [27]), (28, [28]), (29, [29]), (30, [30]), (31, [31]), (32, [32]), (33, [33]), (34, [34]), (35, [35]), (36, [36]), (37, [37]), (38, [38]), (39, [39]), (40, [40]), (41, [41]), (42, [42]), (43, [43]), (44, [44]), (45, [45]), (46, [46]), (47, [47]), (48, [48]), (49, [49]), (50, [50]), (51, [51])],
    [(-320, [2]), (-296, [19]), (-288, [18]), (-280, [9]), (-272, [8]), (-256, [1]), (-240, [3]), (-224, [5]), (-216, [6]), (-208, [7]), (-184, [10]), (-176, [11]), (-168, [12]), (-160, [13]), (-152, [14]), (-144, [15]), (-136, [16]), (-128, [17]), (-40, [28]), (-32, [29]), (-24, [30]), (-16, [31])]⟩,
  ⟨[(1, [1, 2]), (2, [2]), (3, [2, 3]), (4, [4]), (5, [2, 5]), (6, [2, 6]), (7, [2, 7]), (8, [2, 8]), (9, [2, 9]), (10, [2, 10]), (11, [2, 11]), (12, [2, 12]), (13, [2, 13]), (14, [2, 14]), (16, [16]), (17, [17]), (18, [2, 18]), (19, [2, 19]), (20, [20]), (21, [21]), (22, [22]), (23, [23]), (24, [24]), (25, [25]), (26, [26]), (27, [27]), (28, [28]), (29, [29]), (30, [30]), (31, [31]), (32, [32]), (33, [33]), (34, [34]), (35, [35]), (36, [36]), (37, [37]), (38, [38]), (39, [39]), (40, [40]), (41, [41]), (42, [42]), (43, [43]), (44, [44]), (45, [45]), (46, [46]), (47, [47]), (48, [48]), (49, [49]), (50, [50]), (51, [51])],
    [(-320, [2]), (-296, [19]), (-288, [18]), (-280, [9]), (-272, [8]), (-256, [1]), (-240, [3]), (-224, [5]), (-216, [6]), (-208, [7]), (-184, [10]), (-176, [11]), (-168, [12]), (-160, [13]), (-152, [14]), (-144, [15]), (-136, [16]), (-128, [17]), (-40, [28]), (-32, [29]), (-24, [30]), (-16, [31])]⟩,
  ⟨[(1, [1, 2]), (2, [2]), (3, [2, 3]), (4, [4]), (5, [2, 5]), (6, [2, 6]), (7, [2, 7]), (8, [2, 8]), (9, [2, 9]), (10, [2, 10]), (11, [2, 11]), (12, [2, 12]), (13, [2, 13]), (14, [2, 14]), (15, [2, 15]), (16, [16]), (17, [17]), (18, [2, 18]), (19, [2, 19]), (20, [20]), (21, [21]), (22, [22]), (23, [23]), (24, [24]), (25, [25]), (26, [26]), (27, [27]), (28, [28]), (29, [29]), (30, [30]), (31, [31]), (32, [32]), (33, [33]), (34, [34]), (35, [35]), (36, [36]), (37, [37]), (38, [38]), (39, [39]), (40, [40]), (41, [41]), (42, [42]), (43, [43]), (44, [44]), (45, [45]), (46, [46]), (47, [47]), (48, [48]), (49, [49]), (50, [50]), (51, [51])],
    [(-320, [2]), (-296, [19]), (-288, [18]), (-280, [9]), (-272, [8]), (-256, [1]), (-240, [3]), (-224, [5]), (-216, [6]), (-208, [7]), (-184, [10]), (-176, [11]), (-168, [12]), (-160, [13]), (-152, [14]), (-144, [15]), (-136, [16]), (-128, [17]), (-40, [28]), (-32, [29]), (-24, [30]), (-16, [31])]⟩,
  ⟨[(1, [1, 2]), (2, [2]), (3, [2, 3]), (4, [4]), (5, [2, 5]), (6, [2, 6]), (7, [2, 7]), (8, [2, 8]), (9, [2, 9]), (10, [2, 10]), (11, [2, 11]), (12, [2, 12]), (13, [2, 13]), (14, [2, 14]), (15, [2, 15]), (16, [2, 16]), (17, [17]), (18, [2, 18]), (19, [2, 19]), (20, [20]), (21, [21]), (22, [22]), (23, [23]), (24, [24]), (25, [25]), (26, [26]), (27, [27]), (28, [28]), (29, [29]), (30, [30]), (31, [31]), (32, [32]), (33, [33]), (34, [34]), (35, [35]), (36, [36]), (37, [37]), (38, [38]), (39, [39]), (40, [40]), (41, [41]), (42, [42]), (43, [43]), (44, [44]), (45, [45]), (46, [46]), (47, [47]), (48, [48]), (49, [49]), (50, [50]), (51, [51])],
    [(-320, [2]), (-296, [19]), (-288, [18]), (-280, [9]), (-272, [8]), (-256, [1]), (-240, [3]), (-224, [5]), (-216, [6]), (-208, [7]), (-184, [10]), (-176, [11]), (-168, [12]), (-160, [13]), (-152, [14]), (-144, [15]), (-136, [16]), (-128, [17]), (-40, [28]), (-32, [29]), (-24, [30]), (-16, [31])]⟩,
  ⟨[(1, [1, 2]), (2, [2]), (3, [2, 3]), (4, [4]), (5, [2, 5]), (6, [2, 6]), (7, [2, 7]), (8, [2, 8]), (9, [2, 9]), (10, [2, 10]), (11, [2, 11]), (12, [2, 12]), (13, [2, 13]), (14, [2, 14]), (15, [2, 15]), (16, [2, 16]), (17, [2, 17]), (18, [2, 18]), (19, [2, 19]), (20, [20]), (21, [21]), (22, [22]), (23, [23]), (24, [24]), (25, [25]), (26, [26]), (27, [27]), (28, [28]), (29, [29]), (30, [30]), (31, [31]), (32, [32]), (33, [33]), (34, [34]), (35, [35]), (36, [36]), (37, [37]), (38, [38]), (39, [39]), (40, [40]), (41, [41]), (42, [42]), (43, [43]), (44, [44]), (45, [45]), (46, [46]), (47, [47]), (48, [48]), (49, [49]), (50, [50]), (51, [51])],
    [(-320, [2]), (-296, [19]), (-288, [18]), (-280, [9]), (-272, [8]), (-256, [1]), (-240, [3]), (-224, [5]), (-216, [6]), (-208, [7]), (-184, [10]), (-176, [11]), (-168, [12]), (-160, [13]), (-152, [14]), (-144, [15]), (-136, [16]), (-128, [17]), (-40, [28]), (-32, [29]), (-24, [30]), (-16, [31])]⟩,
  ⟨[(1, [1, 2]), (2, [2]), (3, [2, 3]), (4, [4]), (5, [2, 5]), (6, [2, 6]), (7, [2, 7]), (8, [2, 8]), (9, [2, 9]), (10, [2, 10]), (11, [2, 11]), (12, [2, 12]), (13, [2, 13]), (14, [2, 14]), (15, [2, 15]), (16, [2, 16]), (17, [2, 17]), (18, [2, 18]), (19, [2, 19]), (20, [20]), (21, [21]), (22, [22]), (23, [23]), (24, [24]), (25, [25]), (26, [26]), (27, [27]), (28, [2, 28]), (29, [29]), (30, [30]), (31, [31]), (32, [32]), (33, [33]), (34, [34]), (35, [35]), (36, [36]), (37, [37]), (38, [38]), (39, [39]), (40, [40]), (41, [41]), (42, [42]), (43, [43]), (44, [44]), (45, [45]), (46, [46]), (47, [47]), (48, [48]), (49, [49]), (50, [50]), (51, [51])],
    [(-320, [2]), (-296, [19]), (-288, [18]), (-280, [9]), (-272, [8]), (-256, [1]), (-240, [3]), (-224, [5]), (-216, [6]), (-208, [7]), (-184, [10]), (-176, [11]), (-168, [12]), (-160, [13]), (-152, [14]), (-144, [15]), (-136, [16]), (-128, [17]), (-40, [28]), (-32, [29]), (-24, [30]), (-16, [31])]⟩,
  ⟨[(1, [1, 2]), (2, [2]), (3, [2, 3]), (4, [4]), (5, [2, 5]), (6, [2, 6]), (7, [2, 7]), (8, [2, 8]), (9, [2, 9]), (10, [2, 10]), (11, [2, 11]), (12, [2, 12]), (13, [2, 13]), (14, [2, 14]), (15, [2, 15]), (16, [2, 16]), (17, [2, 17]), (18, [2, 18]), (19, [2, 19]), (20, [20]), (21, [21]), (22, [22]), (23, [23]), (24, [24]), (25, [25]), (26, [26]), (27, [27]), (28, [2, 28]), (29, [2, 29]), (30, [30]), (31, [31]), (32, [32]), (33, [33]), (34, [34]), (35, [35]), (36, [36]), (37, [37]), (38, [38]), (39, [39]), (40, [40]), (41, [41]), (42, [42]), (43, [43]), (44, [44]), (45, [45]), (46, [46]), (47, [47]), (48, [48]), (49, [49]), (50, [50]), (51, [51])],
    [(-320, [2]), (-296, [19]), (-288, [18]), (-280, [9]), (-272, [8]), (-256, [1]), (-240, [3]), (-224, [5]), (-216, [6]), (-208, [7]), (-184, [10]), (-176, [11]), (-168, [12]), (-160, [13]), (-152, [14]), (-144, [15]), (-136, [16]), (-128, [17]), (-40, [28]), (-32, [29]), (-24, [30]), (-16, [31])]⟩,
  ⟨[(1, [1, 2]), (2, [2]), (3, [2, 3]), (4, [4]), (5, [2, 5]), (6, [2, 6]), (7, [2, 7]), (8, [2, 8]), (9, [2, 9]), (10, [2, 10]), (11, [2, 11]), (12, [2, 12]), (13, [2, 13]), (14, [2, 14]), (15, [2, 15]), (16, [2, 16]), (17, [2, 17]), (18, [2, 18]), (19, [2, 19]), (20, [20]), (21, [21]), (22, [22]), (23, [23]), (24, [24]), (25, [25]), (26, [26]), (27, [27]), (28, [2, 28]), (29, [2, 29]), (30, [2, 30]), (31, [31]), (32, [32]), (33, [33]), (34, [34]), (35, [35]), (36, [36]), (37, [37]), (38, [38]), (39, [39]), (40, [40]), (41, [41]), (42, [42]), (43, [43]), (44, [44]), (45, [45]), (46, [46]), (47, [47]), (48, [48]), (49, [49]), (50, [50]), (51, [51])],
    [(-320, [2]), (-296, [19]), (-288, [18]), (-280, [9]), (-272, [8]), (-256, [1]), (-240, [3]), (-224, [5]), (-216, [6]), (-208, [7]), (-184, [10]), (-176, [11]), (-168, [12]), (-160, [13]), (-152, [14]), (-144, [15]), (-136, [16]), (-128, [17]), (-40, [28]), (-32, [29]), (-24, [30]), (-16, [31])]⟩,
  ⟨[(1, [1, 2]), (2, [2]), (3, [2, 3]), (4, [4]), (5, [2, 5]), (6, [2, 6]), (7, [2, 7]), (8, [2, 8]), (9, [2, 9]), (10, [2, 10]), (11, [2, 11]), (12, [2, 12]), (13, [2, 13]), (14, [2, 14]), (15, [2, 15]), (16, [2, 16]), (17, [2, 17]), (18, [2, 18]), (19, [2, 19]), (20, [20]), (21, [21]), (22, [22]), (23, [23]), (24, [24]), (25, [25]), (26, [26]), (27, [27]), (28, [2, 28]), (29, [2, 29]), (30, [2, 30]), (31, [2, 31]), (32, [32]), (33, [33]), (34, [34]), (35, [35]), (36, [36]), (37, [37]), (38, [38]), (39, [39]), (40, [40]), (41, [41]), (42, [42]), (43, [43]), (44, [44]), (45, [45]), (46, [46]), (47, [47]), (48, [48]), (49, [49]), (50, [50]), (51, [51])],
    [(-320, [2]), (-296, [19]), (-288, [18]), (-280, [9]), (-272, [8]), (-256, [1]), (-240, [3]), (-224, [5]), (-216, [6]), (-208, [7]), (-184, [10]), (-176, [11]), (-168, [12]), (-160, [13]), (-152, [14]), (-144, [15]), (-136, [16]), (-128, [17]), (-40, [28]), (-32, [29]), (-24, [30]), (-16, [31])]⟩,
  ⟨[(2, [2]), (3, [3]), (4, [4]), (5, [5]), (6, [6]), (7, [7]), (8, [2]), (9, [2, 4]), (10, [2, 4]), (11, [11]), (12, [12]), (16, [16]), (17, [17]), (18, [33]), (19, [50]), (20, [20]), (21, [21]), (22, [22]), (23, [23]), (24, [24]), (25, [25]), (26, [26]), (27, [27]), (28, [28]), (29, [29]), (30, [30]), (31, [31]), (32, [32]), (33, [33]), (34, [34]), (35, [35]), (36, [36]), (37, [37]), (38, [38]), (39, [39]), (40, [40]), (41, [41]), (42, [42]), (43, [43]), (44, [44]), (45, [45]), (46, [46]), (47, [47]), (48, [48]), (49, [49]), (50, [50]), (51, [51]), (52, [52])],
    [(-368, [2]), (-360, [4]), (-352, [2]), (-328, [39]), (-320, [2]), (-296, [19]), (-288, [18]), (-280, [9]), (-272, [8]), (-256, [1]), (-240, [3]), (-224, [5]), (-216, [6]), (-208, [7]), (-184, [10]), (-176, [11]), (-168, [12]), (-160, [13]), (-152, [14]), (-144, [15]), (-136, [16]), (-128, [17]), (-40, [28]), (-32, [29]), (-24, [30]), (-16, [31])]⟩
]

def trapFlow0 : List (TSt × Int × Nat) := [
  ((⟨0x80000a16, 0x80000a16, [(0x8000262a, 0x8000267e), (0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩ : TSt), (-336 : Int), 0),
  ((⟨0x80000a16, 0x80000a16, [(0x8000262a, 0x80002690), (0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩ : TSt), (-336 : Int), 0),
  ((⟨0x80000a16, 0x80000a18, [(0x8000262a, 0x8000267e), (0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩ : TSt), (-368 : Int), 0),
  ((⟨0x80000a16, 0x80000a18, [(0x8000262a, 0x80002690), (0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩ : TSt), (-368 : Int), 0),
  ((⟨0x80000a16, 0x80000a1a, [(0x8000262a, 0x8000267e), (0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩ : TSt), (-368 : Int), 0),
  ((⟨0x80000a16, 0x80000a1a, [(0x8000262a, 0x80002690), (0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩ : TSt), (-368 : Int), 0),
  ((⟨0x80000a16, 0x80000a1c, [(0x8000262a, 0x8000267e), (0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩ : TSt), (-368 : Int), 0),
  ((⟨0x80000a16, 0x80000a1c, [(0x8000262a, 0x80002690), (0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩ : TSt), (-368 : Int), 0),
  ((⟨0x80000a16, 0x80000a1e, [(0x8000262a, 0x8000267e), (0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩ : TSt), (-368 : Int), 1),
  ((⟨0x80000a16, 0x80000a1e, [(0x8000262a, 0x80002690), (0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩ : TSt), (-368 : Int), 1),
  ((⟨0x80000a16, 0x80000a20, [(0x8000262a, 0x8000267e), (0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩ : TSt), (-368 : Int), 1),
  ((⟨0x80000a16, 0x80000a20, [(0x8000262a, 0x80002690), (0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩ : TSt), (-368 : Int), 1),
  ((⟨0x80000a16, 0x80000a22, [(0x8000262a, 0x8000267e), (0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩ : TSt), (-368 : Int), 2),
  ((⟨0x80000a16, 0x80000a22, [(0x8000262a, 0x80002690), (0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩ : TSt), (-368 : Int), 2),
  ((⟨0x80000a16, 0x80000a26, [(0x8000262a, 0x8000267e), (0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩ : TSt), (-368 : Int), 2),
  ((⟨0x80000a16, 0x80000a26, [(0x8000262a, 0x80002690), (0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩ : TSt), (-368 : Int), 2),
  ((⟨0x80000a16, 0x80000a28, [(0x8000262a, 0x8000267e), (0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩ : TSt), (-368 : Int), 2),
  ((⟨0x80000a16, 0x80000a28, [(0x8000262a, 0x80002690), (0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩ : TSt), (-368 : Int), 2),
  ((⟨0x80000a16, 0x80000a2a, [(0x8000262a, 0x8000267e), (0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩ : TSt), (-368 : Int), 2),
  ((⟨0x80000a16, 0x80000a2a, [(0x8000262a, 0x80002690), (0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩ : TSt), (-368 : Int), 2),
  ((⟨0x80000a16, 0x80000a2e, [(0x8000262a, 0x8000267e), (0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩ : TSt), (-368 : Int), 3),
  ((⟨0x80000a16, 0x80000a2e, [(0x8000262a, 0x80002690), (0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩ : TSt), (-368 : Int), 3),
  ((⟨0x80000a16, 0x80000a32, [(0x8000262a, 0x8000267e), (0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩ : TSt), (-368 : Int), 3),
  ((⟨0x80000a16, 0x80000a32, [(0x8000262a, 0x80002690), (0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩ : TSt), (-368 : Int), 3),
  ((⟨0x80000a16, 0x80000a34, [(0x8000262a, 0x8000267e), (0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩ : TSt), (-368 : Int), 3),
  ((⟨0x80000a16, 0x80000a34, [(0x8000262a, 0x80002690), (0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩ : TSt), (-368 : Int), 3),
  ((⟨0x80000a16, 0x80000a36, [(0x8000262a, 0x8000267e), (0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩ : TSt), (-368 : Int), 3),
  ((⟨0x80000a16, 0x80000a36, [(0x8000262a, 0x80002690), (0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩ : TSt), (-368 : Int), 3),
  ((⟨0x80000a16, 0x80000a3a, [(0x8000262a, 0x8000267e), (0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩ : TSt), (-368 : Int), 3),
  ((⟨0x80000a16, 0x80000a3a, [(0x8000262a, 0x80002690), (0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩ : TSt), (-368 : Int), 3),
  ((⟨0x80000a16, 0x80000a3e, [(0x8000262a, 0x8000267e), (0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩ : TSt), (-368 : Int), 3),
  ((⟨0x80000a16, 0x80000a3e, [(0x8000262a, 0x80002690), (0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩ : TSt), (-368 : Int), 3),
  ((⟨0x80000a16, 0x80000a42, [(0x8000262a, 0x8000267e), (0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩ : TSt), (-368 : Int), 3),
  ((⟨0x80000a16, 0x80000a42, [(0x8000262a, 0x80002690), (0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩ : TSt), (-368 : Int), 3),
  ((⟨0x80000a16, 0x80000a44, [(0x8000262a, 0x8000267e), (0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩ : TSt), (-368 : Int), 3),
  ((⟨0x80000a16, 0x80000a44, [(0x8000262a, 0x80002690), (0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩ : TSt), (-368 : Int), 3),
  ((⟨0x80000a16, 0x80000a48, [(0x8000262a, 0x8000267e), (0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩ : TSt), (-368 : Int), 3),
  ((⟨0x80000a16, 0x80000a48, [(0x8000262a, 0x80002690), (0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩ : TSt), (-368 : Int), 3),
  ((⟨0x80000a16, 0x80000a4a, [(0x8000262a, 0x8000267e), (0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩ : TSt), (-368 : Int), 3),
  ((⟨0x80000a16, 0x80000a4a, [(0x8000262a, 0x80002690), (0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩ : TSt), (-368 : Int), 3),
  ((⟨0x80000a16, 0x80000a4c, [(0x8000262a, 0x8000267e), (0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩ : TSt), (-368 : Int), 3),
  ((⟨0x80000a16, 0x80000a4c, [(0x8000262a, 0x80002690), (0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩ : TSt), (-368 : Int), 3),
  ((⟨0x80000a16, 0x80000a50, [(0x8000262a, 0x8000267e), (0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩ : TSt), (-368 : Int), 3),
  ((⟨0x80000a16, 0x80000a50, [(0x8000262a, 0x80002690), (0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩ : TSt), (-368 : Int), 3),
  ((⟨0x80000a16, 0x80000a54, [(0x8000262a, 0x8000267e), (0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩ : TSt), (-368 : Int), 3),
  ((⟨0x80000a16, 0x80000a54, [(0x8000262a, 0x80002690), (0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩ : TSt), (-368 : Int), 3),
  ((⟨0x80000a16, 0x80000a56, [(0x8000262a, 0x8000267e), (0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩ : TSt), (-368 : Int), 3),
  ((⟨0x80000a16, 0x80000a56, [(0x8000262a, 0x80002690), (0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩ : TSt), (-368 : Int), 3)
]

def trapFlow1 : List (TSt × Int × Nat) := [
  ((⟨0x80000a16, 0x80000a58, [(0x8000262a, 0x8000267e), (0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩ : TSt), (-368 : Int), 3),
  ((⟨0x80000a16, 0x80000a58, [(0x8000262a, 0x80002690), (0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩ : TSt), (-368 : Int), 3),
  ((⟨0x80000a16, 0x80000a5c, [(0x8000262a, 0x8000267e), (0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩ : TSt), (-368 : Int), 4),
  ((⟨0x80000a16, 0x80000a5c, [(0x8000262a, 0x80002690), (0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩ : TSt), (-368 : Int), 4),
  ((⟨0x80000a16, 0x80000a60, [(0x8000262a, 0x8000267e), (0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩ : TSt), (-368 : Int), 4),
  ((⟨0x80000a16, 0x80000a60, [(0x8000262a, 0x80002690), (0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩ : TSt), (-368 : Int), 4),
  ((⟨0x80000a16, 0x80000a62, [(0x8000262a, 0x8000267e), (0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩ : TSt), (-368 : Int), 4),
  ((⟨0x80000a16, 0x80000a62, [(0x8000262a, 0x80002690), (0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩ : TSt), (-368 : Int), 4),
  ((⟨0x80000a16, 0x80000a64, [(0x8000262a, 0x8000267e), (0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩ : TSt), (-368 : Int), 4),
  ((⟨0x80000a16, 0x80000a64, [(0x8000262a, 0x80002690), (0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩ : TSt), (-368 : Int), 4),
  ((⟨0x80000a16, 0x80000a68, [(0x8000262a, 0x8000267e), (0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩ : TSt), (-368 : Int), 4),
  ((⟨0x80000a16, 0x80000a68, [(0x8000262a, 0x80002690), (0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩ : TSt), (-368 : Int), 4),
  ((⟨0x80000a16, 0x80000a6c, [(0x8000262a, 0x8000267e), (0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩ : TSt), (-368 : Int), 4),
  ((⟨0x80000a16, 0x80000a6c, [(0x8000262a, 0x80002690), (0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩ : TSt), (-368 : Int), 4),
  ((⟨0x80000a16, 0x80000a6e, [(0x8000262a, 0x8000267e), (0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩ : TSt), (-368 : Int), 4),
  ((⟨0x80000a16, 0x80000a6e, [(0x8000262a, 0x80002690), (0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩ : TSt), (-368 : Int), 4),
  ((⟨0x80000a16, 0x80000a8c, [(0x8000262a, 0x8000267e), (0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩ : TSt), (-368 : Int), 4),
  ((⟨0x80000a16, 0x80000a8c, [(0x8000262a, 0x80002690), (0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩ : TSt), (-368 : Int), 4),
  ((⟨0x80000a16, 0x80000a8e, [(0x8000262a, 0x8000267e), (0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩ : TSt), (-368 : Int), 5),
  ((⟨0x80000a16, 0x80000a8e, [(0x8000262a, 0x80002690), (0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩ : TSt), (-368 : Int), 5),
  ((⟨0x80000a16, 0x80000a90, [(0x8000262a, 0x8000267e), (0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩ : TSt), (-368 : Int), 5),
  ((⟨0x80000a16, 0x80000a90, [(0x8000262a, 0x80002690), (0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩ : TSt), (-368 : Int), 5),
  ((⟨0x80000a16, 0x80000a92, [(0x8000262a, 0x8000267e), (0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩ : TSt), (-368 : Int), 6),
  ((⟨0x80000a16, 0x80000a92, [(0x8000262a, 0x80002690), (0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩ : TSt), (-368 : Int), 6),
  ((⟨0x80000a16, 0x80000a94, [(0x8000262a, 0x8000267e), (0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩ : TSt), (-336 : Int), 6),
  ((⟨0x80000a16, 0x80000a94, [(0x8000262a, 0x80002690), (0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩ : TSt), (-336 : Int), 6),
  ((⟨0x80000c1e, 0x80000c1e, [(0x8000197c, 0x8000198a), (0x800027b8, 0x80002842), (0x800057c0, 0x800057e8)]⟩ : TSt), (-336 : Int), 7),
  ((⟨0x80000c1e, 0x80000c20, [(0x8000197c, 0x8000198a), (0x800027b8, 0x80002842), (0x800057c0, 0x800057e8)]⟩ : TSt), (-368 : Int), 7),
  ((⟨0x80000c1e, 0x80000c22, [(0x8000197c, 0x8000198a), (0x800027b8, 0x80002842), (0x800057c0, 0x800057e8)]⟩ : TSt), (-368 : Int), 7),
  ((⟨0x80000c1e, 0x80000c24, [(0x8000197c, 0x8000198a), (0x800027b8, 0x80002842), (0x800057c0, 0x800057e8)]⟩ : TSt), (-368 : Int), 8),
  ((⟨0x80000c1e, 0x80000c26, [(0x8000197c, 0x8000198a), (0x800027b8, 0x80002842), (0x800057c0, 0x800057e8)]⟩ : TSt), (-368 : Int), 9),
  ((⟨0x80000c1e, 0x80000c28, [(0x8000197c, 0x8000198a), (0x800027b8, 0x80002842), (0x800057c0, 0x800057e8)]⟩ : TSt), (-368 : Int), 9),
  ((⟨0x80000c1e, 0x80000c2c, [(0x8000197c, 0x8000198a), (0x800027b8, 0x80002842), (0x800057c0, 0x800057e8)]⟩ : TSt), (-368 : Int), 10),
  ((⟨0x80000c1e, 0x80000c2e, [(0x8000197c, 0x8000198a), (0x800027b8, 0x80002842), (0x800057c0, 0x800057e8)]⟩ : TSt), (-368 : Int), 10),
  ((⟨0x80000c1e, 0x80000c32, [(0x8000197c, 0x8000198a), (0x800027b8, 0x80002842), (0x800057c0, 0x800057e8)]⟩ : TSt), (-368 : Int), 11),
  ((⟨0x80000c1e, 0x80000c34, [(0x8000197c, 0x8000198a), (0x800027b8, 0x80002842), (0x800057c0, 0x800057e8)]⟩ : TSt), (-368 : Int), 11),
  ((⟨0x80000c1e, 0x80000c36, [(0x8000197c, 0x8000198a), (0x800027b8, 0x80002842), (0x800057c0, 0x800057e8)]⟩ : TSt), (-368 : Int), 12),
  ((⟨0x80000c1e, 0x80000c3a, [(0x8000197c, 0x8000198a), (0x800027b8, 0x80002842), (0x800057c0, 0x800057e8)]⟩ : TSt), (-368 : Int), 11),
  ((⟨0x80000c1e, 0x80000c3c, [(0x8000197c, 0x8000198a), (0x800027b8, 0x80002842), (0x800057c0, 0x800057e8)]⟩ : TSt), (-368 : Int), 11),
  ((⟨0x80000c1e, 0x80000c3e, [(0x8000197c, 0x8000198a), (0x800027b8, 0x80002842), (0x800057c0, 0x800057e8)]⟩ : TSt), (-368 : Int), 11),
  ((⟨0x80000c1e, 0x80000c40, [(0x8000197c, 0x8000198a), (0x800027b8, 0x80002842), (0x800057c0, 0x800057e8)]⟩ : TSt), (-368 : Int), 11),
  ((⟨0x80000c1e, 0x80000c42, [(0x8000197c, 0x8000198a), (0x800027b8, 0x80002842), (0x800057c0, 0x800057e8)]⟩ : TSt), (-368 : Int), 11),
  ((⟨0x80000c1e, 0x80000c44, [(0x8000197c, 0x8000198a), (0x800027b8, 0x80002842), (0x800057c0, 0x800057e8)]⟩ : TSt), (-368 : Int), 11),
  ((⟨0x80000c1e, 0x80000c46, [(0x8000197c, 0x8000198a), (0x800027b8, 0x80002842), (0x800057c0, 0x800057e8)]⟩ : TSt), (-368 : Int), 13),
  ((⟨0x80000c1e, 0x80000c48, [(0x8000197c, 0x8000198a), (0x800027b8, 0x80002842), (0x800057c0, 0x800057e8)]⟩ : TSt), (-336 : Int), 13),
  ((⟨0x80000c1e, 0x80000c4a, [(0x8000197c, 0x8000198a), (0x800027b8, 0x80002842), (0x800057c0, 0x800057e8)]⟩ : TSt), (-368 : Int), 11),
  ((⟨0x80000c1e, 0x80000c4e, [(0x8000197c, 0x8000198a), (0x800027b8, 0x80002842), (0x800057c0, 0x800057e8)]⟩ : TSt), (-368 : Int), 11),
  ((⟨0x80000c1e, 0x80000c52, [(0x8000197c, 0x8000198a), (0x800027b8, 0x80002842), (0x800057c0, 0x800057e8)]⟩ : TSt), (-368 : Int), 14)
]

def trapFlow2 : List (TSt × Int × Nat) := [
  ((⟨0x80000c1e, 0x80000c54, [(0x8000197c, 0x8000198a), (0x800027b8, 0x80002842), (0x800057c0, 0x800057e8)]⟩ : TSt), (-368 : Int), 14),
  ((⟨0x80000c1e, 0x80000c56, [(0x8000197c, 0x8000198a), (0x800027b8, 0x80002842), (0x800057c0, 0x800057e8)]⟩ : TSt), (-368 : Int), 14),
  ((⟨0x80000c98, 0x80000c98, [(0x8000197c, 0x800019a2), (0x800027b8, 0x80002842), (0x800057c0, 0x800057e8)]⟩ : TSt), (-336 : Int), 15),
  ((⟨0x80000c98, 0x80000c9a, [(0x8000197c, 0x800019a2), (0x800027b8, 0x80002842), (0x800057c0, 0x800057e8)]⟩ : TSt), (-352 : Int), 15),
  ((⟨0x80000c98, 0x80000c9c, [(0x8000197c, 0x800019a2), (0x800027b8, 0x80002842), (0x800057c0, 0x800057e8)]⟩ : TSt), (-352 : Int), 15),
  ((⟨0x80000c98, 0x80000c9e, [(0x8000197c, 0x800019a2), (0x800027b8, 0x80002842), (0x800057c0, 0x800057e8)]⟩ : TSt), (-352 : Int), 15),
  ((⟨0x80000c98, 0x80000ca0, [(0x8000197c, 0x800019a2), (0x800027b8, 0x80002842), (0x800057c0, 0x800057e8)]⟩ : TSt), (-352 : Int), 15),
  ((⟨0x80000c98, 0x80000ca4, [(0x8000197c, 0x800019a2), (0x800027b8, 0x80002842), (0x800057c0, 0x800057e8)]⟩ : TSt), (-352 : Int), 16),
  ((⟨0x80000c98, 0x80000ca8, [(0x8000197c, 0x800019a2), (0x800027b8, 0x80002842), (0x800057c0, 0x800057e8)]⟩ : TSt), (-352 : Int), 17),
  ((⟨0x80000c98, 0x80000caa, [(0x8000197c, 0x800019a2), (0x800027b8, 0x80002842), (0x800057c0, 0x800057e8)]⟩ : TSt), (-352 : Int), 17),
  ((⟨0x80000c98, 0x80000cac, [(0x8000197c, 0x800019a2), (0x800027b8, 0x80002842), (0x800057c0, 0x800057e8)]⟩ : TSt), (-352 : Int), 17),
  ((⟨0x80000c98, 0x80000cae, [(0x8000197c, 0x800019a2), (0x800027b8, 0x80002842), (0x800057c0, 0x800057e8)]⟩ : TSt), (-352 : Int), 16),
  ((⟨0x80000c98, 0x80000cb2, [(0x8000197c, 0x800019a2), (0x800027b8, 0x80002842), (0x800057c0, 0x800057e8)]⟩ : TSt), (-352 : Int), 16),
  ((⟨0x80000c98, 0x80000cb4, [(0x8000197c, 0x800019a2), (0x800027b8, 0x80002842), (0x800057c0, 0x800057e8)]⟩ : TSt), (-352 : Int), 16),
  ((⟨0x80000c98, 0x80000cb6, [(0x8000197c, 0x800019a2), (0x800027b8, 0x80002842), (0x800057c0, 0x800057e8)]⟩ : TSt), (-352 : Int), 16),
  ((⟨0x80000c98, 0x80000cb8, [(0x8000197c, 0x800019a2), (0x800027b8, 0x80002842), (0x800057c0, 0x800057e8)]⟩ : TSt), (-352 : Int), 16),
  ((⟨0x80000c98, 0x80000cba, [(0x8000197c, 0x800019a2), (0x800027b8, 0x80002842), (0x800057c0, 0x800057e8)]⟩ : TSt), (-352 : Int), 16),
  ((⟨0x80000c98, 0x80000cbc, [(0x8000197c, 0x800019a2), (0x800027b8, 0x80002842), (0x800057c0, 0x800057e8)]⟩ : TSt), (-352 : Int), 16),
  ((⟨0x80000c98, 0x80000cc0, [(0x8000197c, 0x800019a2), (0x800027b8, 0x80002842), (0x800057c0, 0x800057e8)]⟩ : TSt), (-352 : Int), 16),
  ((⟨0x80000c98, 0x80000cc2, [(0x8000197c, 0x800019a2), (0x800027b8, 0x80002842), (0x800057c0, 0x800057e8)]⟩ : TSt), (-352 : Int), 16),
  ((⟨0x80000c98, 0x80000cc4, [(0x8000197c, 0x800019a2), (0x800027b8, 0x80002842), (0x800057c0, 0x800057e8)]⟩ : TSt), (-352 : Int), 16),
  ((⟨0x80000c98, 0x80000cc6, [(0x8000197c, 0x800019a2), (0x800027b8, 0x80002842), (0x800057c0, 0x800057e8)]⟩ : TSt), (-336 : Int), 16),
  ((⟨0x80001948, 0x80001948, [(0x800025d4, 0x800025e0), (0x8000262a, 0x800026ac), (0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩ : TSt), (-352 : Int), 18),
  ((⟨0x80001948, 0x80001948, [(0x80005870, 0x8000587c), (0x8000262a, 0x8000265a), (0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩ : TSt), (-352 : Int), 19),
  ((⟨0x80001948, 0x80001948, [(0x80005890, 0x800058a0), (0x8000262a, 0x80002684), (0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩ : TSt), (-368 : Int), 20),
  ((⟨0x80001948, 0x8000194a, [(0x800025d4, 0x800025e0), (0x8000262a, 0x800026ac), (0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩ : TSt), (-368 : Int), 18),
  ((⟨0x80001948, 0x8000194a, [(0x80005870, 0x8000587c), (0x8000262a, 0x8000265a), (0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩ : TSt), (-368 : Int), 19),
  ((⟨0x80001948, 0x8000194a, [(0x80005890, 0x800058a0), (0x8000262a, 0x80002684), (0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩ : TSt), (-384 : Int), 20),
  ((⟨0x80001948, 0x8000194c, [(0x800025d4, 0x800025e0), (0x8000262a, 0x800026ac), (0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩ : TSt), (-368 : Int), 18),
  ((⟨0x80001948, 0x8000194c, [(0x80005870, 0x8000587c), (0x8000262a, 0x8000265a), (0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩ : TSt), (-368 : Int), 19),
  ((⟨0x80001948, 0x8000194c, [(0x80005890, 0x800058a0), (0x8000262a, 0x80002684), (0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩ : TSt), (-384 : Int), 20),
  ((⟨0x80001948, 0x8000194e, [(0x800025d4, 0x800025e0), (0x8000262a, 0x800026ac), (0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩ : TSt), (-368 : Int), 21),
  ((⟨0x80001948, 0x8000194e, [(0x80005870, 0x8000587c), (0x8000262a, 0x8000265a), (0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩ : TSt), (-368 : Int), 22),
  ((⟨0x80001948, 0x8000194e, [(0x80005890, 0x800058a0), (0x8000262a, 0x80002684), (0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩ : TSt), (-384 : Int), 23),
  ((⟨0x80001948, 0x80001950, [(0x800025d4, 0x800025e0), (0x8000262a, 0x800026ac), (0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩ : TSt), (-368 : Int), 21),
  ((⟨0x80001948, 0x80001950, [(0x80005870, 0x8000587c), (0x8000262a, 0x8000265a), (0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩ : TSt), (-368 : Int), 22),
  ((⟨0x80001948, 0x80001950, [(0x80005890, 0x800058a0), (0x8000262a, 0x80002684), (0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩ : TSt), (-384 : Int), 23),
  ((⟨0x80001948, 0x80001952, [(0x800025d4, 0x800025e0), (0x8000262a, 0x800026ac), (0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩ : TSt), (-368 : Int), 24),
  ((⟨0x80001948, 0x80001952, [(0x80005870, 0x8000587c), (0x8000262a, 0x8000265a), (0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩ : TSt), (-368 : Int), 25),
  ((⟨0x80001948, 0x80001952, [(0x80005890, 0x800058a0), (0x8000262a, 0x80002684), (0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩ : TSt), (-384 : Int), 26),
  ((⟨0x80001948, 0x80001954, [(0x800025d4, 0x800025e0), (0x8000262a, 0x800026ac), (0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩ : TSt), (-368 : Int), 24),
  ((⟨0x80001948, 0x80001954, [(0x80005870, 0x8000587c), (0x8000262a, 0x8000265a), (0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩ : TSt), (-368 : Int), 25),
  ((⟨0x80001948, 0x80001954, [(0x80005890, 0x800058a0), (0x8000262a, 0x80002684), (0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩ : TSt), (-384 : Int), 26),
  ((⟨0x80001948, 0x80001956, [(0x800025d4, 0x800025e0), (0x8000262a, 0x800026ac), (0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩ : TSt), (-368 : Int), 27),
  ((⟨0x80001948, 0x80001956, [(0x80005870, 0x8000587c), (0x8000262a, 0x8000265a), (0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩ : TSt), (-368 : Int), 28),
  ((⟨0x80001948, 0x80001956, [(0x80005890, 0x800058a0), (0x8000262a, 0x80002684), (0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩ : TSt), (-384 : Int), 29),
  ((⟨0x80001948, 0x80001958, [(0x800025d4, 0x800025e0), (0x8000262a, 0x800026ac), (0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩ : TSt), (-368 : Int), 27),
  ((⟨0x80001948, 0x80001958, [(0x80005870, 0x8000587c), (0x8000262a, 0x8000265a), (0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩ : TSt), (-368 : Int), 28)
]

def trapFlow3 : List (TSt × Int × Nat) := [
  ((⟨0x80001948, 0x80001958, [(0x80005890, 0x800058a0), (0x8000262a, 0x80002684), (0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩ : TSt), (-384 : Int), 29),
  ((⟨0x80001948, 0x8000195a, [(0x800025d4, 0x800025e0), (0x8000262a, 0x800026ac), (0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩ : TSt), (-352 : Int), 27),
  ((⟨0x80001948, 0x8000195a, [(0x80005870, 0x8000587c), (0x8000262a, 0x8000265a), (0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩ : TSt), (-352 : Int), 28),
  ((⟨0x80001948, 0x8000195a, [(0x80005890, 0x800058a0), (0x8000262a, 0x80002684), (0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩ : TSt), (-368 : Int), 29),
  ((⟨0x8000195c, 0x8000195c, [(0x80000c1e, 0x80000c32), (0x8000197c, 0x8000198a), (0x800027b8, 0x80002842), (0x800057c0, 0x800057e8)]⟩ : TSt), (-368 : Int), 10),
  ((⟨0x8000195c, 0x8000195c, [(0x80000c1e, 0x80000c3a), (0x8000197c, 0x8000198a), (0x800027b8, 0x80002842), (0x800057c0, 0x800057e8)]⟩ : TSt), (-368 : Int), 30),
  ((⟨0x8000195c, 0x8000195c, [(0x80000c1e, 0x80000c4e), (0x8000197c, 0x8000198a), (0x800027b8, 0x80002842), (0x800057c0, 0x800057e8)]⟩ : TSt), (-368 : Int), 31),
  ((⟨0x8000195c, 0x8000195c, [(0x80000c98, 0x80000ca4), (0x8000197c, 0x800019a2), (0x800027b8, 0x80002842), (0x800057c0, 0x800057e8)]⟩ : TSt), (-352 : Int), 15),
  ((⟨0x8000195c, 0x8000195e, [(0x80000c1e, 0x80000c32), (0x8000197c, 0x8000198a), (0x800027b8, 0x80002842), (0x800057c0, 0x800057e8)]⟩ : TSt), (-384 : Int), 10),
  ((⟨0x8000195c, 0x8000195e, [(0x80000c1e, 0x80000c3a), (0x8000197c, 0x8000198a), (0x800027b8, 0x80002842), (0x800057c0, 0x800057e8)]⟩ : TSt), (-384 : Int), 30),
  ((⟨0x8000195c, 0x8000195e, [(0x80000c1e, 0x80000c4e), (0x8000197c, 0x8000198a), (0x800027b8, 0x80002842), (0x800057c0, 0x800057e8)]⟩ : TSt), (-384 : Int), 31),
  ((⟨0x8000195c, 0x8000195e, [(0x80000c98, 0x80000ca4), (0x8000197c, 0x800019a2), (0x800027b8, 0x80002842), (0x800057c0, 0x800057e8)]⟩ : TSt), (-368 : Int), 15),
  ((⟨0x8000195c, 0x80001960, [(0x80000c1e, 0x80000c32), (0x8000197c, 0x8000198a), (0x800027b8, 0x80002842), (0x800057c0, 0x800057e8)]⟩ : TSt), (-384 : Int), 10),
  ((⟨0x8000195c, 0x80001960, [(0x80000c1e, 0x80000c3a), (0x8000197c, 0x8000198a), (0x800027b8, 0x80002842), (0x800057c0, 0x800057e8)]⟩ : TSt), (-384 : Int), 30),
  ((⟨0x8000195c, 0x80001960, [(0x80000c1e, 0x80000c4e), (0x8000197c, 0x8000198a), (0x800027b8, 0x80002842), (0x800057c0, 0x800057e8)]⟩ : TSt), (-384 : Int), 31),
  ((⟨0x8000195c, 0x80001960, [(0x80000c98, 0x80000ca4), (0x8000197c, 0x800019a2), (0x800027b8, 0x80002842), (0x800057c0, 0x800057e8)]⟩ : TSt), (-368 : Int), 32),
  ((⟨0x8000195c, 0x80001962, [(0x80000c1e, 0x80000c32), (0x8000197c, 0x8000198a), (0x800027b8, 0x80002842), (0x800057c0, 0x800057e8)]⟩ : TSt), (-384 : Int), 33),
  ((⟨0x8000195c, 0x80001962, [(0x80000c1e, 0x80000c3a), (0x8000197c, 0x8000198a), (0x800027b8, 0x80002842), (0x800057c0, 0x800057e8)]⟩ : TSt), (-384 : Int), 30),
  ((⟨0x8000195c, 0x80001962, [(0x80000c1e, 0x80000c4e), (0x8000197c, 0x8000198a), (0x800027b8, 0x80002842), (0x800057c0, 0x800057e8)]⟩ : TSt), (-384 : Int), 31),
  ((⟨0x8000195c, 0x80001962, [(0x80000c98, 0x80000ca4), (0x8000197c, 0x800019a2), (0x800027b8, 0x80002842), (0x800057c0, 0x800057e8)]⟩ : TSt), (-368 : Int), 34),
  ((⟨0x8000195c, 0x80001964, [(0x80000c1e, 0x80000c32), (0x8000197c, 0x8000198a), (0x800027b8, 0x80002842), (0x800057c0, 0x800057e8)]⟩ : TSt), (-384 : Int), 33),
  ((⟨0x8000195c, 0x80001964, [(0x80000c1e, 0x80000c3a), (0x8000197c, 0x8000198a), (0x800027b8, 0x80002842), (0x800057c0, 0x800057e8)]⟩ : TSt), (-384 : Int), 30),
  ((⟨0x8000195c, 0x80001964, [(0x80000c1e, 0x80000c4e), (0x8000197c, 0x8000198a), (0x800027b8, 0x80002842), (0x800057c0, 0x800057e8)]⟩ : TSt), (-384 : Int), 31),
  ((⟨0x8000195c, 0x80001964, [(0x80000c98, 0x80000ca4), (0x8000197c, 0x800019a2), (0x800027b8, 0x80002842), (0x800057c0, 0x800057e8)]⟩ : TSt), (-368 : Int), 34),
  ((⟨0x8000195c, 0x80001966, [(0x80000c1e, 0x80000c32), (0x8000197c, 0x8000198a), (0x800027b8, 0x80002842), (0x800057c0, 0x800057e8)]⟩ : TSt), (-384 : Int), 35),
  ((⟨0x8000195c, 0x80001966, [(0x80000c1e, 0x80000c3a), (0x8000197c, 0x8000198a), (0x800027b8, 0x80002842), (0x800057c0, 0x800057e8)]⟩ : TSt), (-384 : Int), 31),
  ((⟨0x8000195c, 0x80001966, [(0x80000c1e, 0x80000c4e), (0x8000197c, 0x8000198a), (0x800027b8, 0x80002842), (0x800057c0, 0x800057e8)]⟩ : TSt), (-384 : Int), 31),
  ((⟨0x8000195c, 0x80001966, [(0x80000c98, 0x80000ca4), (0x8000197c, 0x800019a2), (0x800027b8, 0x80002842), (0x800057c0, 0x800057e8)]⟩ : TSt), (-368 : Int), 34),
  ((⟨0x8000195c, 0x80001968, [(0x80000c1e, 0x80000c32), (0x8000197c, 0x8000198a), (0x800027b8, 0x80002842), (0x800057c0, 0x800057e8)]⟩ : TSt), (-384 : Int), 35),
  ((⟨0x8000195c, 0x80001968, [(0x80000c1e, 0x80000c3a), (0x8000197c, 0x8000198a), (0x800027b8, 0x80002842), (0x800057c0, 0x800057e8)]⟩ : TSt), (-384 : Int), 31),
  ((⟨0x8000195c, 0x80001968, [(0x80000c1e, 0x80000c4e), (0x8000197c, 0x8000198a), (0x800027b8, 0x80002842), (0x800057c0, 0x800057e8)]⟩ : TSt), (-384 : Int), 31),
  ((⟨0x8000195c, 0x80001968, [(0x80000c98, 0x80000ca4), (0x8000197c, 0x800019a2), (0x800027b8, 0x80002842), (0x800057c0, 0x800057e8)]⟩ : TSt), (-368 : Int), 34),
  ((⟨0x8000195c, 0x8000196a, [(0x80000c1e, 0x80000c32), (0x8000197c, 0x8000198a), (0x800027b8, 0x80002842), (0x800057c0, 0x800057e8)]⟩ : TSt), (-384 : Int), 35),
  ((⟨0x8000195c, 0x8000196a, [(0x80000c1e, 0x80000c3a), (0x8000197c, 0x8000198a), (0x800027b8, 0x80002842), (0x800057c0, 0x800057e8)]⟩ : TSt), (-384 : Int), 31),
  ((⟨0x8000195c, 0x8000196a, [(0x80000c1e, 0x80000c4e), (0x8000197c, 0x8000198a), (0x800027b8, 0x80002842), (0x800057c0, 0x800057e8)]⟩ : TSt), (-384 : Int), 31),
  ((⟨0x8000195c, 0x8000196a, [(0x80000c98, 0x80000ca4), (0x8000197c, 0x800019a2), (0x800027b8, 0x80002842), (0x800057c0, 0x800057e8)]⟩ : TSt), (-368 : Int), 34),
  ((⟨0x8000195c, 0x8000196e, [(0x80000c1e, 0x80000c32), (0x8000197c, 0x8000198a), (0x800027b8, 0x80002842), (0x800057c0, 0x800057e8)]⟩ : TSt), (-384 : Int), 35),
  ((⟨0x8000195c, 0x8000196e, [(0x80000c1e, 0x80000c3a), (0x8000197c, 0x8000198a), (0x800027b8, 0x80002842), (0x800057c0, 0x800057e8)]⟩ : TSt), (-384 : Int), 35),
  ((⟨0x8000195c, 0x8000196e, [(0x80000c1e, 0x80000c4e), (0x8000197c, 0x8000198a), (0x800027b8, 0x80002842), (0x800057c0, 0x800057e8)]⟩ : TSt), (-384 : Int), 35),
  ((⟨0x8000195c, 0x8000196e, [(0x80000c98, 0x80000ca4), (0x8000197c, 0x800019a2), (0x800027b8, 0x80002842), (0x800057c0, 0x800057e8)]⟩ : TSt), (-368 : Int), 36),
  ((⟨0x8000195c, 0x80001972, [(0x80000c1e, 0x80000c32), (0x8000197c, 0x8000198a), (0x800027b8, 0x80002842), (0x800057c0, 0x800057e8)]⟩ : TSt), (-384 : Int), 35),
  ((⟨0x8000195c, 0x80001972, [(0x80000c1e, 0x80000c3a), (0x8000197c, 0x8000198a), (0x800027b8, 0x80002842), (0x800057c0, 0x800057e8)]⟩ : TSt), (-384 : Int), 35),
  ((⟨0x8000195c, 0x80001972, [(0x80000c1e, 0x80000c4e), (0x8000197c, 0x8000198a), (0x800027b8, 0x80002842), (0x800057c0, 0x800057e8)]⟩ : TSt), (-384 : Int), 35),
  ((⟨0x8000195c, 0x80001972, [(0x80000c98, 0x80000ca4), (0x8000197c, 0x800019a2), (0x800027b8, 0x80002842), (0x800057c0, 0x800057e8)]⟩ : TSt), (-368 : Int), 36),
  ((⟨0x8000195c, 0x80001974, [(0x80000c1e, 0x80000c32), (0x8000197c, 0x8000198a), (0x800027b8, 0x80002842), (0x800057c0, 0x800057e8)]⟩ : TSt), (-384 : Int), 31),
  ((⟨0x8000195c, 0x80001974, [(0x80000c1e, 0x80000c3a), (0x8000197c, 0x8000198a), (0x800027b8, 0x80002842), (0x800057c0, 0x800057e8)]⟩ : TSt), (-384 : Int), 31),
  ((⟨0x8000195c, 0x80001974, [(0x80000c1e, 0x80000c4e), (0x8000197c, 0x8000198a), (0x800027b8, 0x80002842), (0x800057c0, 0x800057e8)]⟩ : TSt), (-384 : Int), 31),
  ((⟨0x8000195c, 0x80001974, [(0x80000c98, 0x80000ca4), (0x8000197c, 0x800019a2), (0x800027b8, 0x80002842), (0x800057c0, 0x800057e8)]⟩ : TSt), (-368 : Int), 34)
]

def trapFlow4 : List (TSt × Int × Nat) := [
  ((⟨0x8000195c, 0x80001976, [(0x80000c1e, 0x80000c32), (0x8000197c, 0x8000198a), (0x800027b8, 0x80002842), (0x800057c0, 0x800057e8)]⟩ : TSt), (-384 : Int), 11),
  ((⟨0x8000195c, 0x80001976, [(0x80000c1e, 0x80000c3a), (0x8000197c, 0x8000198a), (0x800027b8, 0x80002842), (0x800057c0, 0x800057e8)]⟩ : TSt), (-384 : Int), 11),
  ((⟨0x8000195c, 0x80001976, [(0x80000c1e, 0x80000c4e), (0x8000197c, 0x8000198a), (0x800027b8, 0x80002842), (0x800057c0, 0x800057e8)]⟩ : TSt), (-384 : Int), 11),
  ((⟨0x8000195c, 0x80001976, [(0x80000c98, 0x80000ca4), (0x8000197c, 0x800019a2), (0x800027b8, 0x80002842), (0x800057c0, 0x800057e8)]⟩ : TSt), (-368 : Int), 16),
  ((⟨0x8000195c, 0x80001978, [(0x80000c1e, 0x80000c32), (0x8000197c, 0x8000198a), (0x800027b8, 0x80002842), (0x800057c0, 0x800057e8)]⟩ : TSt), (-384 : Int), 11),
  ((⟨0x8000195c, 0x80001978, [(0x80000c1e, 0x80000c3a), (0x8000197c, 0x8000198a), (0x800027b8, 0x80002842), (0x800057c0, 0x800057e8)]⟩ : TSt), (-384 : Int), 11),
  ((⟨0x8000195c, 0x80001978, [(0x80000c1e, 0x80000c4e), (0x8000197c, 0x8000198a), (0x800027b8, 0x80002842), (0x800057c0, 0x800057e8)]⟩ : TSt), (-384 : Int), 11),
  ((⟨0x8000195c, 0x80001978, [(0x80000c98, 0x80000ca4), (0x8000197c, 0x800019a2), (0x800027b8, 0x80002842), (0x800057c0, 0x800057e8)]⟩ : TSt), (-368 : Int), 16),
  ((⟨0x8000195c, 0x8000197a, [(0x80000c1e, 0x80000c32), (0x8000197c, 0x8000198a), (0x800027b8, 0x80002842), (0x800057c0, 0x800057e8)]⟩ : TSt), (-368 : Int), 11),
  ((⟨0x8000195c, 0x8000197a, [(0x80000c1e, 0x80000c3a), (0x8000197c, 0x8000198a), (0x800027b8, 0x80002842), (0x800057c0, 0x800057e8)]⟩ : TSt), (-368 : Int), 11),
  ((⟨0x8000195c, 0x8000197a, [(0x80000c1e, 0x80000c4e), (0x8000197c, 0x8000198a), (0x800027b8, 0x80002842), (0x800057c0, 0x800057e8)]⟩ : TSt), (-368 : Int), 11),
  ((⟨0x8000195c, 0x8000197a, [(0x80000c98, 0x80000ca4), (0x8000197c, 0x800019a2), (0x800027b8, 0x80002842), (0x800057c0, 0x800057e8)]⟩ : TSt), (-352 : Int), 16),
  ((⟨0x8000197c, 0x8000197c, [(0x800027b8, 0x80002842), (0x800057c0, 0x800057e8)]⟩ : TSt), (-304 : Int), 37),
  ((⟨0x8000197c, 0x8000197e, [(0x800027b8, 0x80002842), (0x800057c0, 0x800057e8)]⟩ : TSt), (-336 : Int), 37),
  ((⟨0x8000197c, 0x80001980, [(0x800027b8, 0x80002842), (0x800057c0, 0x800057e8)]⟩ : TSt), (-336 : Int), 37),
  ((⟨0x8000197c, 0x80001982, [(0x800027b8, 0x80002842), (0x800057c0, 0x800057e8)]⟩ : TSt), (-336 : Int), 37),
  ((⟨0x8000197c, 0x80001984, [(0x800027b8, 0x80002842), (0x800057c0, 0x800057e8)]⟩ : TSt), (-336 : Int), 7),
  ((⟨0x8000197c, 0x80001986, [(0x800027b8, 0x80002842), (0x800057c0, 0x800057e8)]⟩ : TSt), (-336 : Int), 7),
  ((⟨0x8000197c, 0x8000198a, [(0x800027b8, 0x80002842), (0x800057c0, 0x800057e8)]⟩ : TSt), (-336 : Int), 13),
  ((⟨0x8000197c, 0x8000198c, [(0x800027b8, 0x80002842), (0x800057c0, 0x800057e8)]⟩ : TSt), (-336 : Int), 13),
  ((⟨0x8000197c, 0x8000198e, [(0x800027b8, 0x80002842), (0x800057c0, 0x800057e8)]⟩ : TSt), (-336 : Int), 13),
  ((⟨0x8000197c, 0x80001990, [(0x800027b8, 0x80002842), (0x800057c0, 0x800057e8)]⟩ : TSt), (-336 : Int), 13),
  ((⟨0x8000197c, 0x80001994, [(0x800027b8, 0x80002842), (0x800057c0, 0x800057e8)]⟩ : TSt), (-336 : Int), 13),
  ((⟨0x8000197c, 0x80001998, [(0x800027b8, 0x80002842), (0x800057c0, 0x800057e8)]⟩ : TSt), (-336 : Int), 13),
  ((⟨0x8000197c, 0x8000199a, [(0x800027b8, 0x80002842), (0x800057c0, 0x800057e8)]⟩ : TSt), (-336 : Int), 13),
  ((⟨0x8000197c, 0x8000199c, [(0x800027b8, 0x80002842), (0x800057c0, 0x800057e8)]⟩ : TSt), (-336 : Int), 13),
  ((⟨0x8000197c, 0x8000199e, [(0x800027b8, 0x80002842), (0x800057c0, 0x800057e8)]⟩ : TSt), (-336 : Int), 38),
  ((⟨0x8000197c, 0x800019a2, [(0x800027b8, 0x80002842), (0x800057c0, 0x800057e8)]⟩ : TSt), (-336 : Int), 16),
  ((⟨0x8000197c, 0x800019a4, [(0x800027b8, 0x80002842), (0x800057c0, 0x800057e8)]⟩ : TSt), (-336 : Int), 16),
  ((⟨0x8000197c, 0x800019a6, [(0x800027b8, 0x80002842), (0x800057c0, 0x800057e8)]⟩ : TSt), (-336 : Int), 16),
  ((⟨0x8000197c, 0x800019a8, [(0x800027b8, 0x80002842), (0x800057c0, 0x800057e8)]⟩ : TSt), (-336 : Int), 16),
  ((⟨0x8000197c, 0x800019aa, [(0x800027b8, 0x80002842), (0x800057c0, 0x800057e8)]⟩ : TSt), (-336 : Int), 39),
  ((⟨0x8000197c, 0x800019ac, [(0x800027b8, 0x80002842), (0x800057c0, 0x800057e8)]⟩ : TSt), (-304 : Int), 39),
  ((⟨0x800025d4, 0x800025d4, [(0x8000262a, 0x800026ac), (0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩ : TSt), (-336 : Int), 40),
  ((⟨0x800025d4, 0x800025d6, [(0x8000262a, 0x800026ac), (0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩ : TSt), (-352 : Int), 40),
  ((⟨0x800025d4, 0x800025d8, [(0x8000262a, 0x800026ac), (0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩ : TSt), (-352 : Int), 40),
  ((⟨0x800025d4, 0x800025da, [(0x8000262a, 0x800026ac), (0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩ : TSt), (-352 : Int), 18),
  ((⟨0x800025d4, 0x800025dc, [(0x8000262a, 0x800026ac), (0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩ : TSt), (-352 : Int), 18),
  ((⟨0x800025d4, 0x800025e0, [(0x8000262a, 0x800026ac), (0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩ : TSt), (-352 : Int), 27),
  ((⟨0x800025d4, 0x800025e2, [(0x8000262a, 0x800026ac), (0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩ : TSt), (-352 : Int), 27),
  ((⟨0x800025d4, 0x800025e6, [(0x8000262a, 0x800026ac), (0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩ : TSt), (-352 : Int), 41),
  ((⟨0x800025d4, 0x800025ea, [(0x8000262a, 0x800026ac), (0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩ : TSt), (-352 : Int), 42),
  ((⟨0x800025d4, 0x800025ee, [(0x8000262a, 0x800026ac), (0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩ : TSt), (-352 : Int), 42),
  ((⟨0x800025d4, 0x800025f0, [(0x8000262a, 0x800026ac), (0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩ : TSt), (-352 : Int), 42),
  ((⟨0x800025d4, 0x800025f4, [(0x8000262a, 0x800026ac), (0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩ : TSt), (-352 : Int), 43),
  ((⟨0x800025d4, 0x800025f6, [(0x8000262a, 0x800026ac), (0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩ : TSt), (-352 : Int), 43),
  ((⟨0x800025d4, 0x800025f8, [(0x8000262a, 0x800026ac), (0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩ : TSt), (-352 : Int), 43),
  ((⟨0x800025d4, 0x800025fa, [(0x8000262a, 0x800026ac), (0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩ : TSt), (-336 : Int), 43)
]

def trapFlow5 : List (TSt × Int × Nat) := [
  ((⟨0x8000262a, 0x8000262a, [(0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩ : TSt), (-304 : Int), 44),
  ((⟨0x8000262a, 0x8000262c, [(0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩ : TSt), (-336 : Int), 44),
  ((⟨0x8000262a, 0x8000262e, [(0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩ : TSt), (-336 : Int), 44),
  ((⟨0x8000262a, 0x80002630, [(0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩ : TSt), (-336 : Int), 45),
  ((⟨0x8000262a, 0x80002632, [(0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩ : TSt), (-336 : Int), 45),
  ((⟨0x8000262a, 0x80002636, [(0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩ : TSt), (-336 : Int), 46),
  ((⟨0x8000262a, 0x80002638, [(0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩ : TSt), (-336 : Int), 47),
  ((⟨0x8000262a, 0x8000263a, [(0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩ : TSt), (-336 : Int), 47),
  ((⟨0x8000262a, 0x8000263c, [(0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩ : TSt), (-336 : Int), 47),
  ((⟨0x8000262a, 0x80002640, [(0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩ : TSt), (-336 : Int), 47),
  ((⟨0x8000262a, 0x80002642, [(0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩ : TSt), (-336 : Int), 47),
  ((⟨0x8000262a, 0x80002644, [(0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩ : TSt), (-336 : Int), 47),
  ((⟨0x8000262a, 0x80002646, [(0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩ : TSt), (-336 : Int), 47),
  ((⟨0x8000262a, 0x80002648, [(0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩ : TSt), (-336 : Int), 40),
  ((⟨0x8000262a, 0x8000264c, [(0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩ : TSt), (-336 : Int), 37),
  ((⟨0x8000262a, 0x8000264e, [(0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩ : TSt), (-336 : Int), 48),
  ((⟨0x8000262a, 0x80002650, [(0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩ : TSt), (-336 : Int), 48),
  ((⟨0x8000262a, 0x80002652, [(0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩ : TSt), (-304 : Int), 48),
  ((⟨0x8000262a, 0x80002654, [(0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩ : TSt), (-336 : Int), 47),
  ((⟨0x8000262a, 0x80002656, [(0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩ : TSt), (-336 : Int), 49),
  ((⟨0x8000262a, 0x8000265a, [(0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩ : TSt), (-336 : Int), 50),
  ((⟨0x8000262a, 0x8000265c, [(0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩ : TSt), (-336 : Int), 51),
  ((⟨0x8000262a, 0x8000265e, [(0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩ : TSt), (-336 : Int), 52),
  ((⟨0x8000262a, 0x80002660, [(0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩ : TSt), (-336 : Int), 53),
  ((⟨0x8000262a, 0x80002664, [(0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩ : TSt), (-336 : Int), 53),
  ((⟨0x8000262a, 0x80002666, [(0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩ : TSt), (-336 : Int), 53),
  ((⟨0x8000262a, 0x8000266a, [(0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩ : TSt), (-336 : Int), 53),
  ((⟨0x8000262a, 0x8000266c, [(0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩ : TSt), (-336 : Int), 53),
  ((⟨0x8000262a, 0x80002670, [(0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩ : TSt), (-336 : Int), 53),
  ((⟨0x8000262a, 0x80002672, [(0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩ : TSt), (-336 : Int), 54),
  ((⟨0x8000262a, 0x80002674, [(0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩ : TSt), (-336 : Int), 54),
  ((⟨0x8000262a, 0x80002676, [(0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩ : TSt), (-336 : Int), 55),
  ((⟨0x8000262a, 0x80002678, [(0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩ : TSt), (-336 : Int), 53),
  ((⟨0x8000262a, 0x8000267a, [(0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩ : TSt), (-336 : Int), 54),
  ((⟨0x8000262a, 0x8000267e, [(0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩ : TSt), (-336 : Int), 6),
  ((⟨0x8000262a, 0x80002680, [(0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩ : TSt), (-336 : Int), 56),
  ((⟨0x8000262a, 0x80002684, [(0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩ : TSt), (-336 : Int), 57),
  ((⟨0x8000262a, 0x80002686, [(0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩ : TSt), (-336 : Int), 58),
  ((⟨0x8000262a, 0x80002688, [(0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩ : TSt), (-336 : Int), 59),
  ((⟨0x8000262a, 0x8000268a, [(0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩ : TSt), (-336 : Int), 53),
  ((⟨0x8000262a, 0x8000268c, [(0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩ : TSt), (-336 : Int), 54),
  ((⟨0x8000262a, 0x80002690, [(0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩ : TSt), (-336 : Int), 6),
  ((⟨0x8000262a, 0x800026a8, [(0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩ : TSt), (-336 : Int), 40),
  ((⟨0x8000262a, 0x800026ac, [(0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩ : TSt), (-336 : Int), 43),
  ((⟨0x8000262a, 0x800026ae, [(0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩ : TSt), (-336 : Int), 60),
  ((⟨0x800027b8, 0x800027b8, [(0x800057c0, 0x800057e8)]⟩ : TSt), (-256 : Int), 61),
  ((⟨0x800027b8, 0x800027ba, [(0x800057c0, 0x800057e8)]⟩ : TSt), (-304 : Int), 61),
  ((⟨0x800027b8, 0x800027bc, [(0x800057c0, 0x800057e8)]⟩ : TSt), (-304 : Int), 61)
]

def trapFlow6 : List (TSt × Int × Nat) := [
  ((⟨0x800027b8, 0x800027be, [(0x800057c0, 0x800057e8)]⟩ : TSt), (-304 : Int), 62),
  ((⟨0x800027b8, 0x800027c0, [(0x800057c0, 0x800057e8)]⟩ : TSt), (-304 : Int), 63),
  ((⟨0x800027b8, 0x800027c2, [(0x800057c0, 0x800057e8)]⟩ : TSt), (-304 : Int), 64),
  ((⟨0x800027b8, 0x800027c4, [(0x800057c0, 0x800057e8)]⟩ : TSt), (-304 : Int), 65),
  ((⟨0x800027b8, 0x800027c6, [(0x800057c0, 0x800057e8)]⟩ : TSt), (-304 : Int), 66),
  ((⟨0x800027b8, 0x800027ca, [(0x800057c0, 0x800057e8)]⟩ : TSt), (-304 : Int), 67),
  ((⟨0x800027b8, 0x800027ce, [(0x800057c0, 0x800057e8)]⟩ : TSt), (-304 : Int), 68),
  ((⟨0x800027b8, 0x800027d2, [(0x800057c0, 0x800057e8)]⟩ : TSt), (-304 : Int), 69),
  ((⟨0x800027b8, 0x800027d4, [(0x800057c0, 0x800057e8)]⟩ : TSt), (-304 : Int), 70),
  ((⟨0x800027b8, 0x800027d8, [(0x800057c0, 0x800057e8)]⟩ : TSt), (-304 : Int), 44),
  ((⟨0x800027b8, 0x800027da, [(0x800057c0, 0x800057e8)]⟩ : TSt), (-304 : Int), 44),
  ((⟨0x800027b8, 0x800027de, [(0x800057c0, 0x800057e8)]⟩ : TSt), (-304 : Int), 44),
  ((⟨0x800027b8, 0x800027e0, [(0x800057c0, 0x800057e8)]⟩ : TSt), (-304 : Int), 44),
  ((⟨0x800027b8, 0x800027e2, [(0x800057c0, 0x800057e8)]⟩ : TSt), (-304 : Int), 44),
  ((⟨0x800027b8, 0x800027e6, [(0x800057c0, 0x800057e8)]⟩ : TSt), (-304 : Int), 48),
  ((⟨0x800027b8, 0x800027e8, [(0x800057c0, 0x800057e8)]⟩ : TSt), (-304 : Int), 48),
  ((⟨0x800027b8, 0x800027ea, [(0x800057c0, 0x800057e8)]⟩ : TSt), (-304 : Int), 48),
  ((⟨0x800027b8, 0x800027ee, [(0x800057c0, 0x800057e8)]⟩ : TSt), (-304 : Int), 48),
  ((⟨0x800027b8, 0x800027f2, [(0x800057c0, 0x800057e8)]⟩ : TSt), (-304 : Int), 48),
  ((⟨0x800027b8, 0x800027f6, [(0x800057c0, 0x800057e8)]⟩ : TSt), (-304 : Int), 48),
  ((⟨0x800027b8, 0x800027f8, [(0x800057c0, 0x800057e8)]⟩ : TSt), (-304 : Int), 48),
  ((⟨0x800027b8, 0x800027fa, [(0x800057c0, 0x800057e8)]⟩ : TSt), (-304 : Int), 71),
  ((⟨0x800027b8, 0x800027fc, [(0x800057c0, 0x800057e8)]⟩ : TSt), (-304 : Int), 72),
  ((⟨0x800027b8, 0x800027fe, [(0x800057c0, 0x800057e8)]⟩ : TSt), (-304 : Int), 73),
  ((⟨0x800027b8, 0x80002800, [(0x800057c0, 0x800057e8)]⟩ : TSt), (-304 : Int), 74),
  ((⟨0x800027b8, 0x80002802, [(0x800057c0, 0x800057e8)]⟩ : TSt), (-256 : Int), 74),
  ((⟨0x800027b8, 0x8000283e, [(0x800057c0, 0x800057e8)]⟩ : TSt), (-304 : Int), 48),
  ((⟨0x800027b8, 0x80002842, [(0x800057c0, 0x800057e8)]⟩ : TSt), (-304 : Int), 39),
  ((⟨0x800057c0, 0x800057c0, []⟩ : TSt), (0 : Int), 75),
  ((⟨0x800057c0, 0x800057c2, []⟩ : TSt), (-256 : Int), 75),
  ((⟨0x800057c0, 0x800057c4, []⟩ : TSt), (-256 : Int), 76),
  ((⟨0x800057c0, 0x800057c6, []⟩ : TSt), (-256 : Int), 77),
  ((⟨0x800057c0, 0x800057c8, []⟩ : TSt), (-256 : Int), 78),
  ((⟨0x800057c0, 0x800057ca, []⟩ : TSt), (-256 : Int), 79),
  ((⟨0x800057c0, 0x800057cc, []⟩ : TSt), (-256 : Int), 80),
  ((⟨0x800057c0, 0x800057ce, []⟩ : TSt), (-256 : Int), 81),
  ((⟨0x800057c0, 0x800057d0, []⟩ : TSt), (-256 : Int), 82),
  ((⟨0x800057c0, 0x800057d2, []⟩ : TSt), (-256 : Int), 83),
  ((⟨0x800057c0, 0x800057d4, []⟩ : TSt), (-256 : Int), 84),
  ((⟨0x800057c0, 0x800057d6, []⟩ : TSt), (-256 : Int), 85),
  ((⟨0x800057c0, 0x800057d8, []⟩ : TSt), (-256 : Int), 86),
  ((⟨0x800057c0, 0x800057da, []⟩ : TSt), (-256 : Int), 87),
  ((⟨0x800057c0, 0x800057dc, []⟩ : TSt), (-256 : Int), 88),
  ((⟨0x800057c0, 0x800057de, []⟩ : TSt), (-256 : Int), 89),
  ((⟨0x800057c0, 0x800057e0, []⟩ : TSt), (-256 : Int), 90),
  ((⟨0x800057c0, 0x800057e2, []⟩ : TSt), (-256 : Int), 91),
  ((⟨0x800057c0, 0x800057e4, []⟩ : TSt), (-256 : Int), 92),
  ((⟨0x800057c0, 0x800057e8, []⟩ : TSt), (-256 : Int), 74)
]

def trapFlow7 : List (TSt × Int × Nat) := [
  ((⟨0x800057c0, 0x800057ea, []⟩ : TSt), (-256 : Int), 93),
  ((⟨0x800057c0, 0x800057ec, []⟩ : TSt), (-256 : Int), 94),
  ((⟨0x800057c0, 0x800057ee, []⟩ : TSt), (-256 : Int), 95),
  ((⟨0x800057c0, 0x800057f0, []⟩ : TSt), (-256 : Int), 96),
  ((⟨0x800057c0, 0x800057f2, []⟩ : TSt), (-256 : Int), 97),
  ((⟨0x800057c0, 0x800057f4, []⟩ : TSt), (-256 : Int), 98),
  ((⟨0x800057c0, 0x800057f6, []⟩ : TSt), (-256 : Int), 99),
  ((⟨0x800057c0, 0x800057f8, []⟩ : TSt), (-256 : Int), 100),
  ((⟨0x800057c0, 0x800057fa, []⟩ : TSt), (-256 : Int), 101),
  ((⟨0x800057c0, 0x800057fc, []⟩ : TSt), (-256 : Int), 102),
  ((⟨0x800057c0, 0x800057fe, []⟩ : TSt), (-256 : Int), 103),
  ((⟨0x800057c0, 0x80005800, []⟩ : TSt), (-256 : Int), 104),
  ((⟨0x800057c0, 0x80005802, []⟩ : TSt), (-256 : Int), 105),
  ((⟨0x800057c0, 0x80005804, []⟩ : TSt), (-256 : Int), 106),
  ((⟨0x800057c0, 0x80005806, []⟩ : TSt), (-256 : Int), 107),
  ((⟨0x800057c0, 0x80005808, []⟩ : TSt), (-256 : Int), 108),
  ((⟨0x800057c0, 0x8000580a, []⟩ : TSt), (-256 : Int), 109),
  ((⟨0x800057c0, 0x8000580c, []⟩ : TSt), (0 : Int), 109),
  ((⟨0x80005870, 0x80005870, [(0x8000262a, 0x8000265a), (0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩ : TSt), (-336 : Int), 49),
  ((⟨0x80005870, 0x80005872, [(0x8000262a, 0x8000265a), (0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩ : TSt), (-352 : Int), 49),
  ((⟨0x80005870, 0x80005874, [(0x8000262a, 0x8000265a), (0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩ : TSt), (-352 : Int), 49),
  ((⟨0x80005870, 0x80005876, [(0x8000262a, 0x8000265a), (0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩ : TSt), (-352 : Int), 19),
  ((⟨0x80005870, 0x80005878, [(0x8000262a, 0x8000265a), (0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩ : TSt), (-352 : Int), 19),
  ((⟨0x80005870, 0x8000587c, [(0x8000262a, 0x8000265a), (0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩ : TSt), (-352 : Int), 28),
  ((⟨0x80005870, 0x80005880, [(0x8000262a, 0x8000265a), (0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩ : TSt), (-352 : Int), 28),
  ((⟨0x80005870, 0x80005884, [(0x8000262a, 0x8000265a), (0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩ : TSt), (-352 : Int), 28),
  ((⟨0x80005870, 0x80005886, [(0x8000262a, 0x8000265a), (0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩ : TSt), (-352 : Int), 50),
  ((⟨0x80005870, 0x80005888, [(0x8000262a, 0x8000265a), (0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩ : TSt), (-352 : Int), 50),
  ((⟨0x80005870, 0x8000588a, [(0x8000262a, 0x8000265a), (0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩ : TSt), (-352 : Int), 50),
  ((⟨0x80005870, 0x8000588c, [(0x8000262a, 0x8000265a), (0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩ : TSt), (-352 : Int), 50),
  ((⟨0x80005870, 0x8000588e, [(0x8000262a, 0x8000265a), (0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩ : TSt), (-336 : Int), 50),
  ((⟨0x80005890, 0x80005890, [(0x8000262a, 0x80002684), (0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩ : TSt), (-336 : Int), 110),
  ((⟨0x80005890, 0x80005892, [(0x8000262a, 0x80002684), (0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩ : TSt), (-368 : Int), 110),
  ((⟨0x80005890, 0x80005894, [(0x8000262a, 0x80002684), (0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩ : TSt), (-368 : Int), 110),
  ((⟨0x80005890, 0x80005896, [(0x8000262a, 0x80002684), (0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩ : TSt), (-368 : Int), 110),
  ((⟨0x80005890, 0x80005898, [(0x8000262a, 0x80002684), (0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩ : TSt), (-368 : Int), 20),
  ((⟨0x80005890, 0x8000589a, [(0x8000262a, 0x80002684), (0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩ : TSt), (-368 : Int), 20),
  ((⟨0x80005890, 0x8000589c, [(0x8000262a, 0x80002684), (0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩ : TSt), (-368 : Int), 20),
  ((⟨0x80005890, 0x800058a0, [(0x8000262a, 0x80002684), (0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩ : TSt), (-368 : Int), 29),
  ((⟨0x80005890, 0x800058a4, [(0x8000262a, 0x80002684), (0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩ : TSt), (-368 : Int), 57),
  ((⟨0x80005890, 0x800058a8, [(0x8000262a, 0x80002684), (0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩ : TSt), (-368 : Int), 57),
  ((⟨0x80005890, 0x800058aa, [(0x8000262a, 0x80002684), (0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩ : TSt), (-368 : Int), 57),
  ((⟨0x80005890, 0x800058ac, [(0x8000262a, 0x80002684), (0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩ : TSt), (-368 : Int), 57),
  ((⟨0x80005890, 0x800058ae, [(0x8000262a, 0x80002684), (0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩ : TSt), (-368 : Int), 57),
  ((⟨0x80005890, 0x800058b0, [(0x8000262a, 0x80002684), (0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩ : TSt), (-368 : Int), 57),
  ((⟨0x80005890, 0x800058b2, [(0x8000262a, 0x80002684), (0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩ : TSt), (-368 : Int), 57),
  ((⟨0x80005890, 0x800058b4, [(0x8000262a, 0x80002684), (0x800027b8, 0x800027e6), (0x800057c0, 0x800057e8)]⟩ : TSt), (-336 : Int), 57)
]

/-- The fence-free walk states with their `sp` offset and carry map (index into `trapMaps`). -/
def trapFlow : List (TSt × Int × Nat) :=
  trapFlow0 ++ trapFlow1 ++ trapFlow2 ++ trapFlow3 ++ trapFlow4 ++ trapFlow5 ++ trapFlow6 ++ trapFlow7
-- END GENERATED

/-! ## 3. The census, decided -/

/-- THE SUMMARIES ARE CLOSED AND EXACT (header). -/
theorem trapTabOk : trapTab.all (sumOkb trapTab) = true := by decide +kernel

/-- The fence-free functions are closed under their free call sites. -/
theorem trapFreeFunsOk : freeFunsOkb trapTab trapFreeFuns = true := by decide +kernel

/-- `kernelvec`'s entry is reached and its `sret` is in its free region. -/
theorem trapKvEnds :
    intMem kvPc (reachOf trapTab kvPc) = true ∧ intMem kvSretPc (freeOf trapTab kvPc) = true :=
  ⟨by decide +kernel, by decide +kernel⟩

/-- The stores of the free regions of `trapFreeFuns` are exactly `trapFreeExits`. -/
def freeExitsOkb : Bool :=
  sortedb trapFreeExits &&
  trapFreeFuns.all (fun f =>
    (freeOf trapTab f).all (fun pc => !isStoreb pc || intMem pc trapFreeExits)) &&
  trapFreeExits.all (fun pc =>
    isStoreb pc && trapFreeFuns.any (fun f => intMem pc (freeOf trapTab f)))

theorem trapFreeExitsOk : freeExitsOkb = true := by decide +kernel

/-- The stores of every summary's `reach` set are exactly `trapExits`; the classes decided where
they can be. -/
def exitsOkb : Bool :=
  sortedb (trapExits.map Prod.fst) &&
  (allReach trapTab).all (fun pc => !isStoreb pc || intMem pc (trapExits.map Prod.fst)) &&
  trapExits.all (fun e => isStoreb e.1 && intMem e.1 (allReach trapTab) && exitClassOkb e.1 e.2)

theorem trapExitsOk : exitsOkb = true := by decide +kernel

/-- The covering fences a trap path can reach: `release+0x16` and `virtio_disk_intr+0x2c`. -/
theorem trapFences :
    (allReach trapTab).all (fun pc => !tcov (kw pc) || pc == relFencePc || pc == virtioFencePc)
      = true := by decide +kernel

def TOut.isSwtch : TOut → Bool
  | .swtch => true
  | _ => false

/-- THE ONLY FENCE-FREE `swtch` CALL is `sched+0x6e` (timer → `yield` → `sched`). -/
theorem trapSwtchSites :
    (allReach trapTab).all (fun pc => !(tstep trapTab pc).isSwtch || pc == schedSwtchPc) = true :=
  by decide +kernel

/-- The free call sites (site, callee) of the fence-free functions. -/
def freeCallSites : List (Int × Int) :=
  trapFreeFuns.flatMap (fun f =>
    (freeOf trapTab f).flatMap (fun pc => (tcallees pc).map (fun g => (pc, g))))

/-- THE THREE FENCE-FREE PATHS, by their call sites (header): `kerneltrap` calls only `devintr`
and `myproc` (NOT `yield`); `devintr` only `plic_claim`, `uartintr` (twice), `plic_complete` and
`clockintr` (NOT `virtio_disk_intr`, NOT `printk`); `clockintr` only `cpuid` (NOT `acquire`: the
hart-0 tick); `uartintr` NOTHING (NOT `wakeup`, NOT the rx hook); the helpers below them. -/
theorem trapFreeCallSites :
    freeCallSites = [
      ((KernelSyms.«push_off» : Int) + 0x10, (KernelSyms.«mycpu» : Int)),
      ((KernelSyms.«push_off» : Int) + 0x18, (KernelSyms.«mycpu» : Int)),
      ((KernelSyms.«push_off» : Int) + 0x2c, (KernelSyms.«mycpu» : Int)),
      ((KernelSyms.«pop_off» : Int) + 0x8, (KernelSyms.«mycpu» : Int)),
      ((KernelSyms.«myproc» : Int) + 0xa, (KernelSyms.«push_off» : Int)),
      ((KernelSyms.«myproc» : Int) + 0x22, (KernelSyms.«pop_off» : Int)),
      ((KernelSyms.«clockintr» : Int) + 0x8, (KernelSyms.«cpuid» : Int)),
      ((KernelSyms.«devintr» : Int) + 0x2c, (KernelSyms.«plic_claim» : Int)),
      ((KernelSyms.«devintr» : Int) + 0x50, (KernelSyms.«uartintr» : Int)),
      ((KernelSyms.«devintr» : Int) + 0x56, (KernelSyms.«plic_complete» : Int)),
      ((KernelSyms.«devintr» : Int) + 0x62, (KernelSyms.«uartintr» : Int)),
      ((KernelSyms.«devintr» : Int) + 0x7e, (KernelSyms.«clockintr» : Int)),
      ((KernelSyms.«kerneltrap» : Int) + 0x2a, (KernelSyms.«devintr» : Int)),
      ((KernelSyms.«kerneltrap» : Int) + 0x86, (KernelSyms.«myproc» : Int)),
      ((KernelSyms.«kernelvec» : Int) + 0x24, (KernelSyms.«kerneltrap» : Int)),
      ((KernelSyms.«plic_claim» : Int) + 0x8, (KernelSyms.«cpuid» : Int)),
      ((KernelSyms.«plic_complete» : Int) + 0xc, (KernelSyms.«cpuid» : Int))] := by
  decide +kernel

/-- (b) refined: `uartintr`'s rx loop with a NULL hook (`+0x46..+0x58`: `lbu` LSR, `lbu` RBR,
`ld` the hook, `beqz` back) is FENCE-FREE; the hook's `jalr` (`+0x5a`) and the `wakeup` call
(`+0x70`) are not. -/
theorem trapUartNullHook :
    intMem ((KernelSyms.«uartintr» : Int) + 0x4e) (freeOf trapTab (KernelSyms.«uartintr» : Int))
      = true ∧
    intMem ((KernelSyms.«uartintr» : Int) + 0x58) (freeOf trapTab (KernelSyms.«uartintr» : Int))
      = true ∧
    intMem hookPc (freeOf trapTab (KernelSyms.«uartintr» : Int)) = false ∧
    intMem ((KernelSyms.«uartintr» : Int) + 0x70) (freeOf trapTab (KernelSyms.«uartintr» : Int))
      = false := by
  decide +kernel

/-- THE `swtch` CONTINUATION, hart side (header): `swtch`'s body is straight-line context saves
(class `swtchCtx`) to its `ret`; from `scheduler`'s resume point no path returns or switches
fence-free, and its only stores are the two `cpus[h]` cells before `release`. -/
theorem trapSwtchCont :
    (reachOf trapTab swtchPc).all (fun pc =>
      (tstep trapTab pc).succs.length ≤ 1 &&
      (!isStoreb pc || intMem pc (trapExits.filter (fun e => e.2 == .swtchCtx) |>.map Prod.fst)))
      = true ∧
    (match tlook trapTab resumePc with
     | some s => !s.tsRet && !s.tsSwt
     | none => false) = true ∧
    (reachOf trapTab resumePc).filter isStoreb
      = [(KernelSyms.«scheduler» : Int) + 0x82, (KernelSyms.«scheduler» : Int) + 0x86] := by
  decide +kernel

/-! ## 4. What the census MEANS

`tmove` is the static control semantics of a FENCE-FREE, `swtch`-FREE trap path (header). -/

inductive tmove : TSt → TSt → Prop where
  | seq (f pc : Int) (fr : List (Int × Int)) :
      tliveb pc = true → kflowOf pc = .FLnone →
      tmove ⟨f, pc, fr⟩ ⟨f, pc + wSize (kw pc), fr⟩
  | brN (f pc tgt : Int) (fr : List (Int × Int)) :
      tliveb pc = true → kflowOf pc = .FLbranch tgt →
      tmove ⟨f, pc, fr⟩ ⟨f, pc + wSize (kw pc), fr⟩
  | brT (f pc tgt : Int) (fr : List (Int × Int)) :
      tliveb pc = true → kflowOf pc = .FLbranch tgt →
      tmove ⟨f, pc, fr⟩ ⟨f, tgt, fr⟩
  | jmp (f pc tgt : Int) (fr : List (Int × Int)) :
      tliveb pc = true → kflowOf pc = .FLjump tgt →
      tmove ⟨f, pc, fr⟩ ⟨f, tgt, fr⟩
  | call (f pc tgt : Int) (fr : List (Int × Int)) :
      tliveb pc = true → kflowOf pc = .FLcall tgt → (tgt == swtchPc) = false →
      tmove ⟨f, pc, fr⟩ ⟨tgt, tgt, (f, pc + wSize (kw pc)) :: fr⟩
  | hook (f : Int) (fr : List (Int × Int)) :
      tliveb hookPc = true → kflowOf hookPc = .FLind →
      tmove ⟨f, hookPc, fr⟩ ⟨hookTgt, hookTgt, (f, hookPc + wSize (kw hookPc)) :: fr⟩
  | ret (f pc g a : Int) (fr : List (Int × Int)) :
      tliveb pc = true → kflowOf pc = .FLret →
      tmove ⟨f, pc, (g, a) :: fr⟩ ⟨g, a, fr⟩

/-- The start (`kernelvec`'s entry) and the end (`kernelvec`'s `sret`, empty stack). -/
def tStart : TSt := ⟨kvPc, kvPc, []⟩
def tEnd : TSt := ⟨kvPc, kvSretPc, []⟩

/-! ### 4.1 Unpacking the checks (generic in the table) -/

theorem tstepLive (tab : List TSum) (pc : Int) (h : tliveb pc = true) :
    tstep tab pc = tflow tab pc := by
  unfold tliveb at h
  rw [Bool.and_eq_true, Bool.not_eq_true', Bool.not_eq_true'] at h
  unfold tstep
  rw [h.1, h.2]
  rfl

theorem tlookSome (tab : List TSum) (g : Int) (s : TSum) :
    tlook tab g = some s → s ∈ tab ∧ s.tsEnt = g := by
  intro h
  unfold tlook at h
  have h2 := List.find?_some h
  simp only [beq_iff_eq] at h2
  exact ⟨List.mem_of_find?_eq_some h, h2⟩

theorem intMemIff (x : Int) (l : List Int) : intMem x l = true ↔ x ∈ l := by
  unfold intMem
  rw [List.any_eq_true]
  constructor
  · rintro ⟨y, hy, he⟩
    rw [beq_iff_eq] at he
    exact he ▸ hy
  · intro h
    exact ⟨x, h, beq_self_eq_true x⟩

theorem reachOfEq (tab : List TSum) (f : Int) (s : TSum) :
    tlook tab f = some s → reachOf tab f = s.tsReach := by
  intro h; unfold reachOf; rw [h]

theorem freeOfEq (tab : List TSum) (f : Int) (s : TSum) :
    tlook tab f = some s → freeOf tab f = s.tsFree := by
  intro h; unfold freeOf; rw [h]

/-- What one checked summary gives. -/
structure SumFacts (tab : List TSum) (s : TSum) : Prop where
  ent : s.tsEnt ∈ s.tsReach
  noFail : ∀ pc, pc ∈ s.tsReach → (tstep tab pc).isFail = false
  closed : ∀ pc, pc ∈ s.tsReach → ∀ q, q ∈ (tstep tab pc).succs → q ∈ s.tsReach
  ret : ∀ pc, pc ∈ s.tsReach → (tstep tab pc).isRet = true → s.tsRet = true
  freeSub : ∀ pc, pc ∈ s.tsFree → pc ∈ s.tsReach
  freeBack : ∀ pc, pc ∈ s.tsReach →
    ((tstep tab pc).isExit = true ∨ ∃ q, q ∈ (tstep tab pc).succs ∧ q ∈ s.tsFree) →
    pc ∈ s.tsFree
  entRet : s.tsEnt ∈ s.tsFree → s.tsEnt = kvPc ∨ s.tsRet = true
  noKv : ∀ pc, pc ∈ s.tsReach → kvPc ∉ tcallees pc

theorem sumFacts (tab : List TSum) (s : TSum) : sumOkb tab s = true → SumFacts tab s := by
  intro h
  unfold sumOkb at h
  simp only [Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true', beq_iff_eq,
    Bool.or_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hent, hcl⟩, hret⟩, -⟩, hfs⟩, hfe⟩, her⟩, hnk⟩ := h
  refine ⟨(intMemIff _ _).1 hent, fun pc hp => (hcl pc hp).1,
    fun pc hp q hq => (intMemIff _ _).1 ((hcl pc hp).2 q hq), ?_,
    fun pc hp => (intMemIff _ _).1 (hfs pc hp), ?_, ?_, ?_⟩
  · intro pc hp hr
    rw [hret, List.any_eq_true]
    exact ⟨pc, hp, hr⟩
  · intro pc hp hor
    apply (intMemIff _ _).1
    rw [hfe pc hp, Bool.or_eq_true, List.any_eq_true]
    rcases hor with h1 | ⟨q, hq, hq'⟩
    · exact .inl h1
    · exact .inr ⟨q, hq, (intMemIff _ _).2 hq'⟩
  · intro he
    rcases her with (h1 | h2) | h3
    · exact .inl h1
    · rw [(intMemIff _ _).2 he] at h2; cases h2
    · exact .inr h3
  · intro pc hp hk
    have := hnk pc hp kvPc hk
    simp at this

theorem tabFacts (tab : List TSum) (htab : tab.all (sumOkb tab) = true) (s : TSum) :
    s ∈ tab → SumFacts tab s :=
  fun hm => sumFacts tab s (List.all_eq_true.mp htab s hm)

/-- The checked summary of a function whose `reach` holds a pc. -/
theorem reachSum (tab : List TSum) (htab : tab.all (sumOkb tab) = true) (f pc : Int) :
    intMem pc (reachOf tab f) = true →
    ∃ s, tlook tab f = some s ∧ SumFacts tab s ∧ s.tsEnt = f ∧ pc ∈ s.tsReach := by
  unfold reachOf
  cases h : tlook tab f with
  | none => intro e; simp [intMem] at e
  | some s =>
    intro e
    obtain ⟨hm, he⟩ := tlookSome tab f s h
    exact ⟨s, rfl, tabFacts tab htab s hm, he, (intMemIff _ _).1 e⟩

/-- A call's step, unfolded: the callee is summarised, the successor is its return point when it
may return. -/
theorem tcallSum (tab : List TSum) (htab : tab.all (sumOkb tab) = true) (tgt ra : Int) :
    (tcall tab tgt ra).isFail = false →
    ∃ s1, tlook tab tgt = some s1 ∧ SumFacts tab s1 ∧ s1.tsEnt = tgt ∧
      tcall tab tgt ra = .next (if s1.tsRet then [ra] else []) s1.tsSwt := by
  unfold tcall
  cases h : tlook tab tgt with
  | none => intro e; simp [TOut.isFail] at e
  | some s1 =>
    intro _
    obtain ⟨hm, he⟩ := tlookSome tab tgt s1 h
    exact ⟨s1, rfl, tabFacts tab htab s1 hm, he, rfl⟩

def tsRetOf (tab : List TSum) (f : Int) : Bool :=
  match tlook tab f with
  | some s => s.tsRet
  | none => false

theorem hookNotSret : (hookPc == kvSretPc) = false := by decide

theorem tflowHook (tab : List TSum) (hk : kflowOf hookPc = .FLind) :
    tflow tab hookPc = tcall tab hookTgt (hookPc + wSize (kw hookPc)) := by
  unfold tflow
  simp only [hk, hookNotSret, beq_self_eq_true, Bool.false_eq_true, ↓reduceIte]

theorem tflowCall (tab : List TSum) (pc tgt : Int) (hk : kflowOf pc = .FLcall tgt)
    (hs : (tgt == swtchPc) = false) : tflow tab pc = tcall tab tgt (pc + wSize (kw pc)) := by
  unfold tflow
  simp only [hk, hs, Bool.false_eq_true, ↓reduceIte]

theorem tcalleesCall (pc tgt : Int) (hk : kflowOf pc = .FLcall tgt)
    (hs : (tgt == swtchPc) = false) : tcallees pc = [tgt] := by
  unfold tcallees
  simp only [hk, hs, Bool.false_eq_true, ↓reduceIte]

theorem tcalleesHook (hk : kflowOf hookPc = .FLind) : tcallees hookPc = [hookTgt] := by
  unfold tcallees
  simp only [hk, beq_self_eq_true, ↓reduceIte]

theorem succsNone (tab : List TSum) (pc : Int) (hk : kflowOf pc = .FLnone) :
    pc + wSize (kw pc) ∈ (tflow tab pc).succs := by
  unfold tflow; simp [hk, TOut.succs]

theorem succsBrN (tab : List TSum) (pc tgt : Int) (hk : kflowOf pc = .FLbranch tgt) :
    pc + wSize (kw pc) ∈ (tflow tab pc).succs := by
  unfold tflow; simp [hk, TOut.succs]

theorem succsBrT (tab : List TSum) (pc tgt : Int) (hk : kflowOf pc = .FLbranch tgt) :
    tgt ∈ (tflow tab pc).succs := by
  unfold tflow; simp [hk, TOut.succs]

theorem succsJmp (tab : List TSum) (pc tgt : Int) (hk : kflowOf pc = .FLjump tgt) :
    tgt ∈ (tflow tab pc).succs := by
  unfold tflow; simp [hk, TOut.succs]

theorem tflowRet (tab : List TSum) (pc : Int) (hk : kflowOf pc = .FLret) :
    tflow tab pc = .ret := by
  unfold tflow; simp only [hk]

theorem tsRetOfEq (tab : List TSum) (f : Int) (s : TSum) :
    tlook tab f = some s → tsRetOf tab f = s.tsRet := by
  intro h; unfold tsRetOf; rw [h]

/-! ### 4.2 Forward: every state of a run from `kernelvec` is in its function's `reach` -/

/-- The frames: each return point is in its caller's `reach` once the callee may return. -/
def tfrOk (tab : List TSum) : Int → List (Int × Int) → Prop
  | _, [] => True
  | f, (g, a) :: fr => (tsRetOf tab f = true → intMem a (reachOf tab g) = true) ∧ tfrOk tab g fr

abbrev tinv (tab : List TSum) (s : TSt) : Prop :=
  intMem s.tPc (reachOf tab s.tFn) = true ∧ tfrOk tab s.tFn s.tFr

/-- One intraprocedural step stays in `reach`. -/
theorem tinvLocal (tab : List TSum) (htab : tab.all (sumOkb tab) = true) (f pc q : Int)
    (fr : List (Int × Int)) (hl : tliveb pc = true) (hq : q ∈ (tflow tab pc).succs) :
    tinv tab ⟨f, pc, fr⟩ → tinv tab ⟨f, q, fr⟩ := by
  intro hx
  obtain ⟨hr, hfr⟩ : intMem pc (reachOf tab f) = true ∧ tfrOk tab f fr := hx
  obtain ⟨s, hs, F, -, hp⟩ := reachSum tab htab f pc hr
  refine ⟨?_, hfr⟩
  show intMem q (reachOf tab f) = true
  rw [reachOfEq tab f s hs, intMemIff]
  exact F.closed pc hp q (by rw [tstepLive tab pc hl]; exact hq)

theorem tinvCallee (tab : List TSum) (htab : tab.all (sumOkb tab) = true) (f pc tgt ra : Int)
    (fr : List (Int × Int)) (hl : tliveb pc = true) (hc : tflow tab pc = tcall tab tgt ra) :
    tinv tab ⟨f, pc, fr⟩ → tinv tab ⟨tgt, tgt, (f, ra) :: fr⟩ := by
  intro hx
  obtain ⟨hr, hfr⟩ : intMem pc (reachOf tab f) = true ∧ tfrOk tab f fr := hx
  obtain ⟨s, hs, F, -, hp⟩ := reachSum tab htab f pc hr
  have hnf : (tcall tab tgt ra).isFail = false := by
    rw [← hc, ← tstepLive tab pc hl]; exact F.noFail pc hp
  obtain ⟨s1, hs1, F1, he1, hcall⟩ := tcallSum tab htab tgt ra hnf
  have h1 : intMem tgt (reachOf tab tgt) = true := by
    rw [reachOfEq tab tgt s1 hs1, intMemIff, ← he1]; exact F1.ent
  have h2 : tsRetOf tab tgt = true → intMem ra (reachOf tab f) = true := by
    intro hret
    have hret' : s1.tsRet = true := (tsRetOfEq tab tgt s1 hs1).symm.trans hret
    rw [reachOfEq tab f s hs, intMemIff]
    refine F.closed pc hp ra ?_
    rw [tstepLive tab pc hl, hc, hcall, hret']
    exact List.mem_singleton_self ra
  exact ⟨h1, h2, hfr⟩

/-- **FORWARD (header).** -/
theorem tinvStep (tab : List TSum) (htab : tab.all (sumOkb tab) = true) (x y : TSt) :
    tmove x y → tinv tab x → tinv tab y := by
  intro hm
  cases hm with
  | seq f pc fr hl hk => exact tinvLocal tab htab f pc _ fr hl (succsNone tab pc hk)
  | brN f pc tgt fr hl hk => exact tinvLocal tab htab f pc _ fr hl (succsBrN tab pc tgt hk)
  | brT f pc tgt fr hl hk => exact tinvLocal tab htab f pc _ fr hl (succsBrT tab pc tgt hk)
  | jmp f pc tgt fr hl hk => exact tinvLocal tab htab f pc _ fr hl (succsJmp tab pc tgt hk)
  | call f pc tgt fr hl hk hs =>
    exact tinvCallee tab htab f pc tgt _ fr hl (tflowCall tab pc tgt hk hs)
  | hook f fr hl hk =>
    exact tinvCallee tab htab f hookPc hookTgt _ fr hl (tflowHook tab hk)
  | ret f pc g a fr hl hk =>
    intro hx
    obtain ⟨hr, hret, hfr⟩ : intMem pc (reachOf tab f) = true ∧
        (tsRetOf tab f = true → intMem a (reachOf tab g) = true) ∧ tfrOk tab g fr := hx
    obtain ⟨s, hs, F, -, hp⟩ := reachSum tab htab f pc hr
    have h1 : s.tsRet = true :=
      F.ret pc hp (by rw [tstepLive tab pc hl, tflowRet tab pc hk]; rfl)
    exact ⟨hret ((tsRetOfEq tab f s hs).trans h1), hfr⟩

/-! ### 4.3 Backward: on a run that reaches the `sret`, every pc is in its function's `free` -/

abbrev tgood (tab : List TSum) (s : TSt) : Prop :=
  intMem s.tPc (freeOf tab s.tFn) = true ∧
    ∀ ga, ga ∈ s.tFr → intMem ga.2 (freeOf tab ga.1) = true

theorem tgoodLocal (tab : List TSum) (htab : tab.all (sumOkb tab) = true) (f pc q : Int)
    (fr : List (Int × Int)) (hl : tliveb pc = true) (hq : q ∈ (tflow tab pc).succs) :
    tinv tab ⟨f, pc, fr⟩ → tgood tab ⟨f, q, fr⟩ → tgood tab ⟨f, pc, fr⟩ := by
  intro hx hy
  obtain ⟨hr, -⟩ : intMem pc (reachOf tab f) = true ∧ tfrOk tab f fr := hx
  obtain ⟨hq', hfr⟩ : intMem q (freeOf tab f) = true ∧
      ∀ ga, ga ∈ fr → intMem ga.2 (freeOf tab ga.1) = true := hy
  obtain ⟨s, hs, F, -, hp⟩ := reachSum tab htab f pc hr
  refine ⟨?_, hfr⟩
  show intMem pc (freeOf tab f) = true
  rw [freeOfEq tab f s hs, intMemIff]
  rw [freeOfEq tab f s hs, intMemIff] at hq'
  exact F.freeBack pc hp (.inr ⟨q, by rw [tstepLive tab pc hl]; exact hq, hq'⟩)

theorem tgoodCallee (tab : List TSum) (htab : tab.all (sumOkb tab) = true) (f pc tgt ra : Int)
    (fr : List (Int × Int)) (hl : tliveb pc = true) (hc : tflow tab pc = tcall tab tgt ra)
    (hcl : tcallees pc = [tgt]) :
    tinv tab ⟨f, pc, fr⟩ → tgood tab ⟨tgt, tgt, (f, ra) :: fr⟩ → tgood tab ⟨f, pc, fr⟩ := by
  intro hx hy
  obtain ⟨hr, -⟩ : intMem pc (reachOf tab f) = true ∧ tfrOk tab f fr := hx
  obtain ⟨ht, hfr⟩ : intMem tgt (freeOf tab tgt) = true ∧
      ∀ ga, ga ∈ (f, ra) :: fr → intMem ga.2 (freeOf tab ga.1) = true := hy
  obtain ⟨s, hs, F, -, hp⟩ := reachSum tab htab f pc hr
  have hnf : (tcall tab tgt ra).isFail = false := by
    rw [← hc, ← tstepLive tab pc hl]; exact F.noFail pc hp
  obtain ⟨s1, hs1, F1, he1, hcall⟩ := tcallSum tab htab tgt ra hnf
  have hra : intMem ra (freeOf tab f) = true := hfr (f, ra) (List.mem_cons_self ..)
  refine ⟨?_, fun ga hga => hfr ga (List.mem_cons_of_mem _ hga)⟩
  have hret : s1.tsRet = true := by
    rw [freeOfEq tab tgt s1 hs1, intMemIff, ← he1] at ht
    rcases F1.entRet ht with e | e
    · exfalso
      apply F.noKv pc hp
      rw [hcl, ← he1, e]
      exact List.mem_singleton_self _
    · exact e
  show intMem pc (freeOf tab f) = true
  rw [freeOfEq tab f s hs, intMemIff]
  rw [freeOfEq tab f s hs, intMemIff] at hra
  refine F.freeBack pc hp (.inr ⟨ra, ?_, hra⟩)
  rw [tstepLive tab pc hl, hc, hcall, hret]
  exact List.mem_singleton_self ra

/-- **BACKWARD (header).** -/
theorem tgoodStep (tab : List TSum) (htab : tab.all (sumOkb tab) = true) (x y : TSt) :
    tmove x y → tinv tab x → tgood tab y → tgood tab x := by
  intro hm
  cases hm with
  | seq f pc fr hl hk => exact tgoodLocal tab htab f pc _ fr hl (succsNone tab pc hk)
  | brN f pc tgt fr hl hk => exact tgoodLocal tab htab f pc _ fr hl (succsBrN tab pc tgt hk)
  | brT f pc tgt fr hl hk => exact tgoodLocal tab htab f pc _ fr hl (succsBrT tab pc tgt hk)
  | jmp f pc tgt fr hl hk => exact tgoodLocal tab htab f pc _ fr hl (succsJmp tab pc tgt hk)
  | call f pc tgt fr hl hk hs =>
    exact tgoodCallee tab htab f pc tgt _ fr hl (tflowCall tab pc tgt hk hs)
      (tcalleesCall pc tgt hk hs)
  | hook f fr hl hk =>
    exact tgoodCallee tab htab f hookPc hookTgt _ fr hl (tflowHook tab hk) (tcalleesHook hk)
  | ret f pc g a fr hl hk =>
    intro hx hy
    obtain ⟨hr, -⟩ : intMem pc (reachOf tab f) = true ∧ tfrOk tab f ((g, a) :: fr) := hx
    obtain ⟨ha, hfr⟩ : intMem a (freeOf tab g) = true ∧
        ∀ ga, ga ∈ fr → intMem ga.2 (freeOf tab ga.1) = true := hy
    obtain ⟨s, hs, F, -, hp⟩ := reachSum tab htab f pc hr
    have h1 : intMem pc (freeOf tab f) = true := by
      rw [freeOfEq tab f s hs, intMemIff]
      exact F.freeBack pc hp (.inl (by rw [tstepLive tab pc hl, tflowRet tab pc hk]; rfl))
    refine ⟨h1, ?_⟩
    intro ga hga
    rcases List.mem_cons.mp hga with e | hga
    · subst e; exact ha
    · exact hfr ga hga

/-! ### 4.4 The census's meaning, at the image's table -/

theorem trapStartInv : tinv trapTab tStart := ⟨trapKvEnds.1, trivial⟩

/-- **Every state of a run from `kernelvec`'s entry is in its function's `reach` set** (header). -/
theorem trapRunInv (s : TSt) : rtc tmove tStart s → tinv trapTab s := by
  intro h
  exact rtc_ind_r (R := tmove) (fun z => tinv trapTab z) tStart trapStartInv
    (fun y z _ hyz hy => tinvStep trapTab trapTabOk y z hyz hy) s h

theorem trapEndGood : tgood trapTab tEnd := ⟨trapKvEnds.2, fun _ h => by simp [tEnd] at h⟩

/-- **On a run from `kernelvec`'s entry to its `sret`, every state is in its function's free
region**, every return point in its caller's. -/
theorem trapRunGood (s : TSt) : rtc tmove tStart s → rtc tmove s tEnd → tgood trapTab s := by
  intro h1 h2
  have key := rtc_ind_l (R := tmove) (fun x => tinv trapTab x → tgood trapTab x) tEnd
    (fun _ => trapEndGood)
    (fun x y hxy _ ihy hx => tgoodStep trapTab trapTabOk x y hxy hx (ihy (tinvStep trapTab
      trapTabOk x y hxy hx)))
  exact key s h2 (trapRunInv s h1)

abbrev tff (s : TSt) : Prop :=
  intMem s.tFn trapFreeFuns = true ∧ ∀ ga, ga ∈ s.tFr → intMem ga.1 trapFreeFuns = true

theorem freeFunsCallee (f pc g : Int) :
    intMem f trapFreeFuns = true → intMem pc (freeOf trapTab f) = true → g ∈ tcallees pc →
    intMem g trapFreeFuns = true := by
  intro hf hp hg
  have h := trapFreeFunsOk
  unfold freeFunsOkb at h
  rw [Bool.and_eq_true, List.all_eq_true] at h
  have h2 := h.2 f ((intMemIff _ _).1 hf)
  rw [Bool.and_eq_true, List.all_eq_true] at h2
  have h3 := h2.2 pc ((intMemIff _ _).1 hp)
  rw [List.all_eq_true] at h3
  exact h3 g hg

/-- **The functions of a fence-free `kernelvec` → `sret` run are `trapFreeFuns`.** -/
theorem trapRunFreeFuns (s : TSt) : rtc tmove tStart s → rtc tmove s tEnd → tff s := by
  intro h1 h2
  have key := rtc_ind_r (R := tmove) (fun z => rtc tmove z tEnd → tff z) tStart
    (fun _ => ⟨by decide +kernel, fun _ h => by simp [tStart] at h⟩)
    (fun y z hy hyz ih hz => by
      have hy' : rtc tmove y tEnd := rtc_l hyz hz
      obtain ⟨hfy, hfry⟩ := ih hy'
      have hg : tgood trapTab y := trapRunGood y hy hy'
      cases hyz with
      | seq f pc fr _ _ => exact ⟨hfy, hfry⟩
      | brN f pc tgt fr _ _ => exact ⟨hfy, hfry⟩
      | brT f pc tgt fr _ _ => exact ⟨hfy, hfry⟩
      | jmp f pc tgt fr _ _ => exact ⟨hfy, hfry⟩
      | call f pc tgt fr hl hk hs =>
        have hc : tgt ∈ tcallees pc := by
          rw [tcalleesCall pc tgt hk hs]; exact List.mem_singleton_self _
        refine ⟨freeFunsCallee f pc tgt hfy hg.1 hc, fun ga hga => ?_⟩
        rcases List.mem_cons.mp hga with e | hga
        · subst e; exact hfy
        · exact hfry ga hga
      | hook f fr hl hk =>
        have hc : hookTgt ∈ tcallees hookPc := by
          rw [tcalleesHook hk]; exact List.mem_singleton_self _
        refine ⟨freeFunsCallee f hookPc hookTgt hfy hg.1 hc, fun ga hga => ?_⟩
        rcases List.mem_cons.mp hga with e | hga
        · subst e; exact hfy
        · exact hfry ga hga
      | ret f pc g a fr _ _ =>
        exact ⟨hfry (g, a) (List.mem_cons_self ..), fun ga hga => hfry ga
          (List.mem_cons_of_mem _ hga)⟩)
  exact key s h1 h2

/-- **THE FENCE-FREE EXITS (header)**: a store executed on a fence-free `kernelvec` → `sret` run
is a `trapFreeExits` row — an `sp`-frame spill, a `push_off`/`pop_off` cpu cell, or
`plic_complete`'s MMIO store. -/
theorem trapRunFreeStore (s : TSt) :
    rtc tmove tStart s → rtc tmove s tEnd → isStoreb s.tPc = true →
    intMem s.tPc trapFreeExits = true := by
  intro h1 h2 hst
  have hf := (trapRunFreeFuns s h1 h2).1
  have hp := (trapRunGood s h1 h2).1
  have h := trapFreeExitsOk
  unfold freeExitsOkb at h
  rw [Bool.and_eq_true, Bool.and_eq_true, List.all_eq_true] at h
  have h2' := h.1.2 s.tFn ((intMemIff _ _).1 hf)
  rw [List.all_eq_true] at h2'
  have h3 := h2' s.tPc ((intMemIff _ _).1 hp)
  rw [hst, Bool.not_true, Bool.false_or] at h3
  exact h3

theorem allReachMem (f pc : Int) : intMem pc (reachOf trapTab f) = true →
    intMem pc (allReach trapTab) = true := by
  intro h
  obtain ⟨s, hs, -, -, hp⟩ := reachSum trapTab trapTabOk f pc h
  rw [intMemIff]
  unfold allReach
  exact List.mem_flatMap.mpr ⟨s, (tlookSome trapTab f s hs).1, hp⟩

/-- **THE PRE-FENCE EXITS (header)**: a store executed on ANY run from `kernelvec`'s entry (before
its first covering fence, `swtch`-free) is a `trapExits` row. -/
theorem trapRunStore (s : TSt) : rtc tmove tStart s → isStoreb s.tPc = true →
    intMem s.tPc (trapExits.map Prod.fst) = true := by
  intro h hst
  have hp := allReachMem s.tFn s.tPc (trapRunInv s h).1
  have h := trapExitsOk
  unfold exitsOkb at h
  rw [Bool.and_eq_true, Bool.and_eq_true, List.all_eq_true] at h
  have h3 := h.1.2 s.tPc ((intMemIff _ _).1 hp)
  rw [hst, Bool.not_true, Bool.false_or] at h3
  exact h3

/-- **THE COVERING FENCES (header)**: a run from `kernelvec`'s entry that reaches a covering fence
reaches `release+0x16` or `virtio_disk_intr+0x2c`. -/
theorem trapRunFence (s : TSt) : rtc tmove tStart s → tcov (kw s.tPc) = true →
    s.tPc = relFencePc ∨ s.tPc = virtioFencePc := by
  intro h hc
  have hp := allReachMem s.tFn s.tPc (trapRunInv s h).1
  have h : (!tcov (kw s.tPc) || s.tPc == relFencePc || s.tPc == virtioFencePc) = true :=
    List.all_eq_true.mp trapFences s.tPc ((intMemIff _ _).1 hp)
  rw [hc, Bool.not_true, Bool.false_or, Bool.or_eq_true, beq_iff_eq, beq_iff_eq] at h
  exact h

/-- **THE `swtch` CALL (header)**: a run from `kernelvec`'s entry that reaches a live call of
`swtch` is at `sched+0x6e`. -/
theorem trapRunSwtch (s : TSt) : rtc tmove tStart s → tliveb s.tPc = true →
    kflowOf s.tPc = .FLcall swtchPc → s.tPc = schedSwtchPc := by
  intro h hl hk
  have hp := allReachMem s.tFn s.tPc (trapRunInv s h).1
  have h : (!(tstep trapTab s.tPc).isSwtch || s.tPc == schedSwtchPc) = true :=
    List.all_eq_true.mp trapSwtchSites s.tPc ((intMemIff _ _).1 hp)
  rw [tstepLive trapTab _ hl] at h
  unfold tflow at h
  simp only [hk, beq_self_eq_true, ↓reduceIte, TOut.isSwtch, Bool.not_true, Bool.false_or,
    beq_iff_eq] at h
  exact h

/-! ### 4.5 Non-vacuity: a concrete run, decided -/

/-- The step relation as a boolean (the witness checker). -/
def tmoveb (x y : TSt) : Bool :=
  tliveb x.tPc &&
  match kflowOf x.tPc with
  | .FLnone => y == ⟨x.tFn, x.tPc + wSize (kw x.tPc), x.tFr⟩
  | .FLbranch tgt => y == ⟨x.tFn, x.tPc + wSize (kw x.tPc), x.tFr⟩ || y == ⟨x.tFn, tgt, x.tFr⟩
  | .FLjump tgt => y == ⟨x.tFn, tgt, x.tFr⟩
  | .FLcall tgt =>
      !(tgt == swtchPc) && y == ⟨tgt, tgt, (x.tFn, x.tPc + wSize (kw x.tPc)) :: x.tFr⟩
  | .FLind =>
      x.tPc == hookPc && y == ⟨hookTgt, hookTgt, (x.tFn, x.tPc + wSize (kw x.tPc)) :: x.tFr⟩
  | .FLret =>
      match x.tFr with
      | (g, a) :: fr' => y == ⟨g, a, fr'⟩
      | [] => false

theorem tmovebSound (x y : TSt) : tmoveb x y = true → tmove x y := by
  obtain ⟨f, pc, fr⟩ := x
  intro h
  unfold tmoveb at h
  rw [Bool.and_eq_true] at h
  obtain ⟨hl, h⟩ := h
  cases hk : kflowOf pc with
  | FLnone =>
    simp only [hk, beq_iff_eq] at h; subst h; exact .seq f pc fr hl hk
  | FLbranch tgt =>
    simp only [hk, Bool.or_eq_true, beq_iff_eq] at h
    rcases h with h | h
    · subst h; exact .brN f pc tgt fr hl hk
    · subst h; exact .brT f pc tgt fr hl hk
  | FLjump tgt =>
    simp only [hk, beq_iff_eq] at h; subst h; exact .jmp f pc tgt fr hl hk
  | FLcall tgt =>
    simp only [hk, Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at h
    obtain ⟨hs, h⟩ := h
    subst h; exact .call f pc tgt fr hl hk hs
  | FLind =>
    simp only [hk, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨hp, h⟩ := h
    subst hp; subst h
    exact .hook f fr hl hk
  | FLret =>
    cases fr with
    | nil => simp only [hk, Bool.false_eq_true] at h
    | cons ga fr =>
      obtain ⟨g, a⟩ := ga
      simp only [hk, beq_iff_eq] at h; subst h
      exact .ret f pc g a fr hl hk

def tpathOkb : TSt → List TSt → Bool
  | _, [] => true
  | x, y :: l => tmoveb x y && tpathOkb y l

def tpathEnd : TSt → List TSt → TSt
  | x, [] => x
  | _, y :: l => tpathEnd y l

theorem tpathRtc (x : TSt) (l : List TSt) : tpathOkb x l = true → rtc tmove x (tpathEnd x l) := by
  induction l generalizing x with
  | nil => intro _; exact rtc_refl x
  | cons y l ih =>
    intro h
    unfold tpathOkb at h
    rw [Bool.and_eq_true] at h
    exact rtc_l (tmovebSound x y h.1) (ih y h.2)

/-- **NON-VACUITY (header)**: path (a) — `kernelvec` → `kerneltrap` → `devintr` → `plic_claim`
(→ `cpuid`) → irq = 0 → back up to the `sret` — is a fence-free `swtch`-free run. -/
theorem trapWitnessRun : rtc tmove tStart tEnd := by
  have h1 : tpathOkb tStart trapWitnessTail = true := by decide +kernel
  have h2 : tpathEnd tStart trapWitnessTail = tEnd := by decide +kernel
  exact h2 ▸ tpathRtc tStart trapWitnessTail h1

/-- On it, `plic_claim`'s MMIO claim read is executed (`plic_claim+0x16`, `lw a0,4(a5)`) and the
stores are `trapFreeExits` rows. -/
theorem trapWitnessClaim :
    trapWitnessTail.any (fun s => s.tPc == (KernelSyms.«plic_claim» : Int) + 0x16) = true := by
  decide +kernel


/-! ## 5. B2-free: the carry analysis over the fence-free walk states (decided)

Which interrupted register each register / `sp`-slot carries, on EVERY fence-free path: a
forward MUST-analysis (intersection at merges) over the 383 walk states of the free regions,
keyed by the trap's entry `sp` (`spoff`: `sp`'s offset from it, tracked through the
`addi sp,sp,imm` forms).  The table (`trapFlow`, `trapMaps`) is generated; `flowOkb` checks it
edge by edge against `xferR`/`xferS`/`xferSp`, the port of the instruction's register effect
(`depsRd`/`depsRd2`, the decoded destinations and sources — the same role B1's `grpOkb` realizes)
plus the spill/restore of an `sp`-slot.  RESULT (`flowEnd`): at the `sret`, every register
`x1..x31` and every CSR pseudo-register but `stimecmp` (52, written by `clockintr`) carries its
own interrupted value — the trap path is transparent to the walk's taint. -/

/-- The offset of an `sp`-based load/store form (`c.sdsp`, `c.swsp`, `c.ldsp`, `c.lwsp`, the base S- and
I-type forms; the role says the base is `sp`). -/
def spMemOff (w : Nat) : Option Int :=
  if wIsRvc w then
    if (w &&& 3) == 2 && wfield w 15 13 == 7 then
      some (((wfield w 12 10 <<< 3) + (wfield w 9 7 <<< 6) : Nat) : Int)
    else if (w &&& 3) == 2 && wfield w 15 13 == 6 then
      some (((wfield w 12 9 <<< 2) + (wfield w 8 7 <<< 6) : Nat) : Int)
    else if (w &&& 3) == 2 && wfield w 15 13 == 3 then
      some (((wfield w 12 12 <<< 5) + (wfield w 6 5 <<< 3) + (wfield w 4 2 <<< 6) : Nat) : Int)
    else if (w &&& 3) == 2 && wfield w 15 13 == 2 then
      some (((wfield w 12 12 <<< 5) + (wfield w 6 4 <<< 2) + (wfield w 3 2 <<< 6) : Nat) : Int)
    else none
  else if wOp w == 0x23 then some (zsext ((wfield w 31 25 <<< 5) + wfield w 11 7) 12)
  else if wOp w == 0x03 then some (zsext (wfield w 31 20) 12)
  else none

/-- The immediate of an `sp := sp + imm` form (`c.addi16sp`, `c.addi sp`, `addi sp,sp,imm`). -/
def spAdj (w : Nat) : Option Int :=
  if wIsRvc w then
    if (w &&& 3) == 1 && wfield w 15 13 == 3 then
      some (zsext ((wfield w 12 12 <<< 9) + (wfield w 6 6 <<< 4) + (wfield w 5 5 <<< 6)
        + (wfield w 4 3 <<< 7) + (wfield w 2 2 <<< 5)) 10)
    else if (w &&& 3) == 1 && wfield w 15 13 == 0 then
      some (zsext ((wfield w 12 12 <<< 5) + wfield w 6 2) 6)
    else none
  else if wOp w == 0x13 && wF3 w == 0 && wfield w 19 15 == 2 then
    some (zsext (wfield w 31 20) 12)
  else none

/-- An `sp`-slot STORE (a spill) and its offset. -/
def spSt (pc : Int) : Option Int :=
  match krole pc with
  | .ORstore rs1 _ => if rs1 == 2 then spMemOff (kw pc) else none
  | _ => none

/-- An `sp`-slot LOAD (a restore) and its offset. -/
def spLd (pc : Int) : Option Int :=
  match krole pc with
  | .ORload _ rs1 => if rs1 == 2 then spMemOff (kw pc) else none
  | _ => none

def cr (m : List (Nat × List Nat)) (x : Nat) : List Nat :=
  match m.find? (fun p => p.1 == x) with
  | some p => p.2
  | none => []

def cs (m : List (Int × List Nat)) (o : Int) : List Nat :=
  match m.find? (fun p => p.1 == o) with
  | some p => p.2
  | none => []

def setR (m : List (Nat × List Nat)) (x : Nat) (v : List Nat) : List (Nat × List Nat) :=
  (x, v) :: m

def setS (m : List (Int × List Nat)) (o : Int) (v : List Nat) : List (Int × List Nat) :=
  (o, v) :: m

def cunion (m : List (Nat × List Nat)) (srcs : List Dsrc) : List Nat :=
  srcs.flatMap (fun s => match s with
    | .DReg x => cr m x
    | .DLdRes => [])

/-- The restored slot's carry (an `sp`-slot load). -/
def slotOf (pc sp : Int) (m : CMap) : List Nat :=
  match spLd pc with
  | some o => cs m.cmS (sp + o)
  | none => []

/-- The instruction's effect on the register carries: the first destination ... -/
def xferR1 (pc sp : Int) (m : CMap) : List (Nat × List Nat) :=
  match depsRd (krole pc) with
  | none => m.cmR
  | some (rd, dec) => setR m.cmR rd (cunion m.cmR dec ++ slotOf pc sp m)

/-- ... then the second (a CSR access's GPR destination, from the CSR's NEW carry, in
`taintStep`'s order). -/
def xferR (pc sp : Int) (m : CMap) : List (Nat × List Nat) :=
  match depsRd2 (krole pc) with
  | none => xferR1 pc sp m
  | some (rd2, dec2) => setR (xferR1 pc sp m) rd2 (cunion (xferR1 pc sp m) dec2)

/-- ... on the slot carries. -/
def xferS (pc sp : Int) (m : CMap) : List (Int × List Nat) :=
  match spSt pc with
  | some o => setS m.cmS (sp + o) (cunion m.cmR (depsVsrc (krole pc)))
  | none => m.cmS

/-- ... on the `sp` offset (`none`: an unsupported write of `sp`). -/
def xferSp (pc sp : Int) : Option Int :=
  if (depsRd2 (krole pc)).any (fun p => p.1 == 2) then none
  else if (depsRd (krole pc)).any (fun p => p.1 == 2) then
    (match krole pc with
     | .ORalu _ _ => (spAdj (kw pc)).map (fun i => sp + i)
     | _ => none)
  else some sp

def cmLe (a b : CMap) : Bool :=
  a.cmR.all (fun p => p.2.all (fun r => (cr b.cmR p.1).contains r)) &&
  a.cmS.all (fun p => p.2.all (fun r => (cs b.cmS p.1).contains r))

/-- The `tmove` successors of a state. -/
def tsuccs (s : TSt) : List TSt :=
  if tliveb s.tPc then
    match kflowOf s.tPc with
    | .FLnone => [⟨s.tFn, s.tPc + wSize (kw s.tPc), s.tFr⟩]
    | .FLbranch tgt => [⟨s.tFn, s.tPc + wSize (kw s.tPc), s.tFr⟩, ⟨s.tFn, tgt, s.tFr⟩]
    | .FLjump tgt => [⟨s.tFn, tgt, s.tFr⟩]
    | .FLcall tgt =>
        if tgt == swtchPc then [] else [⟨tgt, tgt, (s.tFn, s.tPc + wSize (kw s.tPc)) :: s.tFr⟩]
    | .FLind =>
        if s.tPc == hookPc then [⟨hookTgt, hookTgt, (s.tFn, s.tPc + wSize (kw s.tPc)) :: s.tFr⟩]
        else []
    | .FLret =>
        match s.tFr with
        | (g, a) :: fr => [⟨g, a, fr⟩]
        | [] => []
  else []

def tgoodb (s : TSt) : Bool :=
  intMem s.tPc (freeOf trapTab s.tFn) && s.tFr.all (fun ga => intMem ga.2 (freeOf trapTab ga.1))

def mapOf (n : Nat) : CMap := trapMaps.getD n ⟨[], []⟩

def rowOf (s : TSt) : Option (Int × Nat) := (trapFlow.find? (fun r => r.1 == s)).map (·.2)

/-- THE TABLE IS A POST-FIXPOINT, edge by edge (header). -/
def flowOkb : Bool :=
  trapFlow.all (fun row =>
    (tsuccs row.1).all (fun s' => !tgoodb s' ||
      match rowOf s', xferSp row.1.tPc row.2.1 with
      | some (sp', n'), some sp2 =>
          sp' == sp2 &&
          cmLe (mapOf n') ⟨xferR row.1.tPc row.2.1 (mapOf row.2.2),
            xferS row.1.tPc row.2.1 (mapOf row.2.2)⟩
      | _, _ => false))

theorem flowOk : flowOkb = true := by decide +kernel

/-- The registers tracked: `x1..x31` and the CSR pseudo-registers `32..52`. -/
def flowRegs : List Nat := (List.range 52).map (· + 1)

/-- The registers an excursion PRESERVES: all but `stimecmp` (52). -/
def presRegs : List Nat := (List.range 51).map (· + 1)

def cmId : CMap := ⟨flowRegs.map (fun x => (x, [x])), []⟩

/-- At the trap's entry: offset 0, every register carries itself (and no slot anything). -/
theorem flowStart :
    (match rowOf tStart with
     | some (sp, n) => sp == 0 && cmLe (mapOf n) cmId
     | none => false) = true := by decide +kernel

/-- **TRANSPARENCY (header)**: at the `sret` the `sp` offset is back to 0 and every preserved
register carries its own interrupted value. -/
theorem flowEnd :
    (match rowOf tEnd with
     | some (sp, n) => sp == 0 && presRegs.all (fun x => (cr (mapOf n).cmR x).contains x)
     | none => false) = true := by decide +kernel

/-- `stimecmp` is NOT preserved (`clockintr` rearms the timer): the excursion certificate
requires the walk's taint to avoid it (`presRegs`). -/
theorem flowStimecmp :
    (match rowOf tEnd with
     | some (_, n) => (cr (mapOf n).cmR 52).contains 52
     | none => true) = false := by decide +kernel

end PinTrapSites
end Weak
