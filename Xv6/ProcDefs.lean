/-
The process predicates of the xv6 kernel, modelled on the Rocq prototype's
`ProcGeom.v` / `ProcDefs.v` / `SchedCtx.v` / `ProcInv.v` / `IntrDefs.v`,
scaled to what the Lean framework has: memory cells (`wordPointsTo`),
byte buffers, the per-cpu bookkeeping of `MachCSL/KCtx.lean`.  No page
files, inodes or locks yet: the places where the Rocq predicates own
those are named placeholders (like `kptSlot` in `KCtx.lean`), so that the
shape of every predicate is already the final one and only the
placeholders will be filled in.  The user address space and the trapframe
page ARE ported: `ProcPriv` carries the table description `upt : UPtd`
and the trapframe words `tf`, and the private block owns them through
`procPtAt` / `tfPageAt` (`Xv6/UPtDefs.lean`).

Layout of `struct proc` (kernel/proc.h, spinlock = {locked; name; cpu} =
24 bytes, NOFILE = 16), corroborated by the compiled image (`myproc`'s
`ld a5,48(a5)` off `pid_lock` = `cpus` + 48 - 48 ...; `allocproc`'s
`auipc/addi` pins `proc` at (KernelSyms.«cpus» + 0x3b0); sizeof = 360 = 96 + 14*8 + 16*8
+ 8 + 16, the Rocq `proc_size`):

  lock@0 (locked@0, name@8, cpu@16), state@24, chan@32, killed@40,
  xstate@44, pid@48, parent@56, kstack@64, sz@72, pagetable@80,
  trapframe@88, context@96..207 (14 words: ra sp s0..s11),
  ofile@208..335 (16 pointers), cwd@336, name@344..359.

Imports only definitional files.
-/
import MachCSL.KCtx
import MachCSL.CallConv
import Xv6.Geom
import Xv6.KernelText
import Xv6.UPtDefs
import Xv6.IrefSlots

set_option linter.unusedSectionVars false

namespace Xv6

open Iris Iris.ProgramLogic Iris.BI Std MachCSL
open LeanRV64D

variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [CurCtx]

/-! ## Geometry (Rocq `ProcGeom.v`) -/

/-- `proc[NPROC]` (kernel/proc.c) in this image: `procinit`'s and
`proc_mapstacks`' `auipc s1,0x11; addi s1,s1,-116` / `addi s1,s1,82`
both land on `KernelSyms.«proc»`, and `&proc[NPROC] = KernelSyms.«tickslock» = tickslock`
(`KernelSyms.«proc» + 64 * 360`).  (The Rocq `KernelSyms.proc` is (KernelSyms.«cpus» + 0x3b0): a
different build of the same kernel.) -/
def procsAddr : BitVec 64 := KA.«proc»

-- `NPROC` / `NOFILE` are `Xv6/SlotSupply.lean`'s (the slot supplies'
-- bounds need them below this file).
/-- `sizeof (struct proc)` (Rocq `proc_size`). -/
def procSize : Nat := 360
/-- `sizeof (p->name)` (Rocq `PNAMELEN`). -/
def PNAMELEN : Nat := 16
/-- `MAXVA` (kernel/riscv.h): `1 << 38`. -/
def MAXVA : Nat := 2 ^ 38

/-- `&proc[i]` (Rocq `proc_addr`). -/
def procAddr (i : Nat) : BitVec 64 := procsAddr + BitVec.ofNat 64 (procSize * i)

/-- `&p->lock` (offset 0; `locked` at 0, `name` at 8, `cpu` at 16). -/
def pLock (pa : BitVec 64) : BitVec 64 := pa
def pState (pa : BitVec 64) : BitVec 64 := pa + 24#64
def pChan (pa : BitVec 64) : BitVec 64 := pa + 32#64
def pKilled (pa : BitVec 64) : BitVec 64 := pa + 40#64
def pXstate (pa : BitVec 64) : BitVec 64 := pa + 44#64
def pPid (pa : BitVec 64) : BitVec 64 := pa + 48#64
def pParent (pa : BitVec 64) : BitVec 64 := pa + 56#64
def pKstack (pa : BitVec 64) : BitVec 64 := pa + 64#64
def pSz (pa : BitVec 64) : BitVec 64 := pa + 72#64
def pPagetable (pa : BitVec 64) : BitVec 64 := pa + 80#64
def pTrapframe (pa : BitVec 64) : BitVec 64 := pa + 88#64
/-- word `j` of `p->context` (`ra sp s0 .. s11`, `j < 14`). -/
def pContext (pa : BitVec 64) (j : Nat) : BitVec 64 := pa + 96#64 + BitVec.ofNat 64 (8 * j)
/-- `&p->ofile[j]` (`j < NOFILE`). -/
def pOfile (pa : BitVec 64) (j : Nat) : BitVec 64 := pa + 208#64 + BitVec.ofNat 64 (8 * j)
def pCwd (pa : BitVec 64) : BitVec 64 := pa + 336#64
/-- `&p->name` (16 bytes). -/
def pName (pa : BitVec 64) : BitVec 64 := pa + 344#64

/-- `enum procstate`. -/
def UNUSED : BitVec 32 := 0#32
def USED : BitVec 32 := 1#32
def SLEEPING : BitVec 32 := 2#32
def RUNNABLE : BitVec 32 := 3#32
def RUNNING : BitVec 32 := 4#32
def ZOMBIE : BitVec 32 := 5#32

/-! ## The private block (Rocq `pprivate` / `proc_fields` / `proc_priv_bare`) -/

/-- The values of the fields private to the process (Rocq `pprivate`, plus
`kstack`, `pagetable`, `trapframe` and the saved `context`, which the Rocq
block reaches through its page-table and scheduler resources).  Every Rocq
field is here, at its Rocq-relative position (Rocq order: `sz upt tf ofile
fdg cwd name cwi gen chg lazy`); the four Lean-only fields (`kstack`,
`pagetable`, `trapframe`, `context`) are interleaved where they were.  Three
of the Rocq fields are GHOST NAMES reserved ahead of their predicates (wave 7
item A3, decision D7: the record is edited once): `fdg` (P2's per-incarnation
descriptor ghost), `gen` and `chg` (D8's generation machinery). -/
structure ProcPriv where
  kstack : BitVec 64
  sz : BitVec 64
  pagetable : BitVec 64
  trapframe : BitVec 64
  /-- the user address space `p->pagetable` describes (Rocq `pv_upt`) -/
  upt : UPtd
  /-- the 36 words of the trapframe page (Rocq `pv_tf`) -/
  tf : List (BitVec 64)
  /-- the 14 saved words of `p->context` -/
  context : List (BitVec 64)
  /-- the 16 file pointers of `p->ofile` -/
  ofile : List (BitVec 64)
  /-- **The descriptor ghost's name** (Rocq `pv_fdg`): THIS incarnation's
  per-descriptor state ghost (`FdSlots.fd_st`), minted fresh by allocproc and
  dropped at the process's death; a field rather than a parameter of the
  block because every spec that touches a process already threads `V`.  No
  xv6 operation reassigns it (not even exec).  RESERVED: no predicate names
  it yet (P2, wave-7 item C0, makes `procPrivFd` read it in place of its
  external `γd : Nat → GName`). -/
  fdg : GName
  cwd : BitVec 64
  /-- the 16 bytes of `p->name` -/
  name : List (BitVec 8)
  /-- **The working directory's inum** (Rocq `pv_cwi`, lane C1): what user
  code can observe of its cwd is the directory it names, not the cached
  `struct inode *`, so the block carries the inum beside the pointer and
  `ProcInv.cwdRefAt V.cwd V.cwi` ties the two (`IcacheHeld.inodeHeldAt`, the
  reference AT this inum).  Not a cell.  chdir writes it, fork copies it,
  exec and everything else keep it.  A `Nat`, not Rocq's `Z`: the Lean
  `inodeHeldAt` takes a `Nat` inum (IcacheHeld deviation 3). -/
  cwi : Nat
  /-- **This incarnation's generation** (Rocq `pv_gen`): the ghost name
  allocproc mints for the process (`ChildTok.gen_own`: slot, pid, exit
  payload).  Changes only at allocproc's mint and the process's death; exec
  keeps it.  RESERVED: the generation machinery (D8) is a later item. -/
  gen : GName
  /-- **The name of its children row** (Rocq `pv_chg`): the key of this
  process's row in the `wait_lock` children map (`WaitInv.ch_frag`),
  installed by whoever creates the process under `wait_lock`.  RESERVED (D8). -/
  chg : GName
  /-- **The lazy-page bit** (Rocq `ProcDefs.pv_lazy`): "this process MAY
  have pages the kernel has promised and not yet mapped".  What it MEANS is
  the claim every live block carries beside `umBelow`:

    `V.pvLazy = false → lazyFree V.upt.um V.sz`

  i.e. at `false` every page below the break is in the table.  STORED, not
  computed (Rocq's reason: `vmfault` maps pages across a trap the process
  cannot see, so a computed verdict would move where a stored one does
  not), and monotone the safe way: `true` promises nothing, so only
  `sys_sbrk`'s lazy grow has to raise it, and a dormant slot sits at
  `true`.  Not a cell: nothing in `struct proc` stores it and `procFields`
  does not mention it.  LAST in the record, as in Rocq. -/
  pvLazy : Bool

/-- `p->name` is a C string: a NUL somewhere in its 16 bytes (Rocq `pname_wf`). -/
def pnameWf (bs : List (BitVec 8)) : Prop := bs.length = PNAMELEN ∧ ∃ j, j < PNAMELEN ∧ bs[j]? = some 0#8

/-- The 14 context words (Rocq: the `p_context` cells of `proc_ctx`). -/
def contextCells (pa : BitVec 64) (dq : DFrac) (ws : List (BitVec 64)) : IProp GF := iprop%
  ⌜ws.length = 14⌝ ∗ [∗list] j ↦ w ∈ ws, wordPointsTo (pContext pa j) 8 dq w

/-- `p->ofile[0..NOFILE)` (Rocq `ofile_cells`). -/
def ofileCells (pa : BitVec 64) (dq : DFrac) (fs : List (BitVec 64)) : IProp GF := iprop%
  ⌜fs.length = NOFILE⌝ ∗ [∗list] j ↦ f ∈ fs, wordPointsTo (pOfile pa j) 8 dq f

/-- `p->name` (Rocq `pname_cells`). -/
def pnameCells (pa : BitVec 64) (dq : DFrac) (bs : List (BitVec 8)) : IProp GF := iprop%
  ⌜pnameWf bs⌝ ∗ byteBuf (pName pa) dq bs

/-- The private fields' cells at the values `V` (Rocq `proc_fields`: `sz`,
`cwd`, `name`; here also `kstack`, `pagetable`, `trapframe`, the context
words and the descriptor pointers). -/
def procFields (pa : BitVec 64) (dq : DFrac) (V : ProcPriv) : IProp GF := iprop%
  wordPointsTo (pKstack pa) 8 dq V.kstack ∗
  wordPointsTo (pSz pa) 8 dq V.sz ∗
  wordPointsTo (pPagetable pa) 8 dq V.pagetable ∗
  wordPointsTo (pTrapframe pa) 8 dq V.trapframe ∗
  contextCells pa dq V.context ∗
  ofileCells pa dq V.ofile ∗
  wordPointsTo (pCwd pa) 8 dq V.cwd ∗
  pnameCells pa dq V.name

/-- The pid cell's three fractions (Rocq): a HALF rides in the private
block, a QUARTER is lock-protected (`procPub`), a QUARTER sits in the
`pid_lock` payload, which `allocpid`'s scan reads without the proc locks. -/
def pidPriv : DFrac := DFrac.own (Qp.half 1)
def pidPub : DFrac := DFrac.own (Qp.half (Qp.half 1))
def pidLockQ : DFrac := DFrac.own (Qp.half (Qp.half 1))

/-- The private block of a running process (Rocq `proc_priv_bare`, and
`proc_priv_core` minus the cwd inode reference): the size bounds, half of
`p->pid`, the private fields, the address space at the view `M`, the
trapframe page, and -- at Rocq `proc_priv_core`'s place, after the
trapframe page -- what the lazy bit claims (`ProcPriv.pvLazy`). -/
def procPriv (pa : BitVec 64) (pid : BitVec 32) (V : ProcPriv) (M : Nat → List (BitVec 8)) :
    IProp GF := iprop%
  ⌜V.sz.toNat ≤ uvmMaxsz ∧ umBelow V.sz V.upt ∧
    V.pagetable = pageAddr V.upt.root ∧ V.trapframe = pageAddr V.upt.tfp⌝ ∗
  wordPointsTo (pPid pa) 4 pidPriv pid ∗
  procFields pa (DFrac.own 1) V ∗
  procPtAt V.upt M ∗
  tfPageAt V.upt.tfp V.tf ∗
  ⌜V.pvLazy = false → lazyFree V.upt.um V.sz⌝

/-! ## The public part (Rocq `SchedCtx.proc_pub`, `proc_held`) -/

/-- The fields `p->lock` protects (Rocq `proc_held` minus the lock token
and the state ghost mirror): `state`, `chan`, `killed`, `xstate` whole and
the `pid_lock`-free quarter of `pid`. -/
def procPub (pa : BitVec 64) (st : BitVec 32) (chan : BitVec 64) (killed xstate pid : BitVec 32) :
    IProp GF := iprop%
  wordPointsTo (pState pa) 4 (DFrac.own 1) st ∗
  wordPointsTo (pChan pa) 8 (DFrac.own 1) chan ∗
  wordPointsTo (pKilled pa) 4 (DFrac.own 1) killed ∗
  wordPointsTo (pXstate pa) 4 (DFrac.own 1) xstate ∗
  wordPointsTo (pPid pa) 4 pidPub pid

/-! ## Dormant slots (Rocq `proc_dormant`, `proc_slots`) -/

/-- The memory a dormant slot still owns (the tail of Rocq
`proc_dormant`): its whole kernel stack (the 512 slots below `kstack +
PGSIZE`: nobody runs on it), and at ZOMBIE the address space and the
trapframe page, which `wait` reaps; at UNUSED `pagetable`, `trapframe`,
`sz` and `pid` are zero. -/
def dormantSpace (st : BitVec 32) (V : ProcPriv) (pid : BitVec 32) : IProp GF :=
  if st = UNUSED then
    iprop(⌜V.pagetable = 0#64 ∧ V.trapframe = 0#64 ∧ V.sz = 0#64 ∧ pid = 0#32⌝ ∗
      stackOwn (V.kstack + 4096#64) 512)
  else
    iprop(∃ M : Nat → List (BitVec 8),
      ⌜V.pagetable = pageAddr V.upt.root ∧ V.trapframe = pageAddr V.upt.tfp ∧
        umBelow V.sz V.upt⌝ ∗
      procPtAt V.upt M ∗ tfPageAt V.upt.tfp V.tf ∗ stackOwn (V.kstack + 4096#64) 512)

/-- A slot nobody runs (UNUSED or ZOMBIE): the private block's cells with
existential values, no open files, no cwd (Rocq `proc_dormant`; its file
descriptor / inode / buffer allowances are not ported).  A ZOMBIE keeps
its address space and trapframe page until `wait` reaps it; `freeproc`
empties them and the slot becomes UNUSED.  The lazy bit is SET (Rocq
`proc_dormant`'s `pv_lazy V = true`): the block invariant's claim is vacuous
there, which is what lets `allocproc` hand out an empty table with nothing
to prove; `freeproc` and `kexit`'s park write it (it is not a cell). -/
def procDormant (pa : BitVec 64) (st : BitVec 32) : IProp GF := iprop%
  ⌜st = UNUSED ∨ st = ZOMBIE⌝ ∗
  ∃ (V : ProcPriv) (pid : BitVec 32),
    ⌜V.ofile = List.replicate NOFILE 0#64 ∧ V.cwd = 0#64 ∧ V.sz.toNat ≤ uvmMaxsz ∧
      V.pvLazy = true⌝ ∗
    wordPointsTo (pPid pa) 4 pidPriv pid ∗
    procFields pa (DFrac.own 1) V ∗
    dormantSpace st V pid

/-- What slot `i` owes at state `st` besides the lock-protected part
(Rocq `proc_slots`): the dormant block at UNUSED/ZOMBIE, nothing else yet
(the running/parked contexts of `SchedCtx.v` are not ported). -/
def procSlot (i : Nat) (st : BitVec 32) : IProp GF :=
  if st = UNUSED ∨ st = ZOMBIE then procDormant (procAddr i) st else iprop(True)

/-! ## The current process (Rocq `ProcGeom.cur_proc`) -/

/-- The current-process resource: `cpus[cpu].proc` holds `p` (Rocq
`cur_proc p`; the hart is explicit here where Rocq's is the ambient
`CpuId`).  `myproc()` returns exactly this value. -/
def curProc [KernelGeom] (cpu : CPU) (p : BitVec 64) : IProp GF :=
  wordPointsTo (aCpuProc cpu) 8 (DFrac.own 1) p

/-- `cur_proc` is the first cell of the per-cpu bundle (Rocq `cpu_cells`). -/
theorem cpuCells_curProc [KernelGeom] (cpu : CPU) (lent sie : Bool) (noff : Nat) (intena : Bool) (p : BitVec 64) :
    cpuCells (GF := GF) cpu lent sie noff intena p ⊢
      curProc cpu p ∗ (curProc cpu p -∗ cpuCells cpu lent sie noff intena p) := by
  unfold cpuCells curProc
  iintro ⟨Hp, Hn, Hi⟩
  iframe Hp
  iintro Hp
  iframe

end Xv6
