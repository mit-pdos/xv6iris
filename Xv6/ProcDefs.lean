/-
The process predicates of the xv6 kernel, modelled on the Rocq prototype's
`ProcGeom.v` / `ProcDefs.v` / `SchedCtx.v` / `ProcInv.v` / `IntrDefs.v`,
scaled to what the Lean framework has: memory cells (`wordPointsTo`),
byte buffers, the per-cpu bookkeeping of `MachCSL/KCtx.lean`.  No page
tables, trapframe pages, files, inodes or locks yet: the places where the
Rocq predicates own those are named placeholders (like `kptSlot` in
`KCtx.lean`), so that the shape of every predicate is already the final
one and only the placeholders will be filled in.

Layout of `struct proc` (kernel/proc.h, spinlock = {locked; name; cpu} =
24 bytes, NOFILE = 16), corroborated by the compiled image (`myproc`'s
`ld a5,48(a5)` off `pid_lock` = `cpus` + 48 - 48 ...; `allocproc`'s
`auipc/addi` pins `proc` at 0x80012768; sizeof = 360 = 96 + 14*8 + 16*8
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

set_option linter.unusedSectionVars false

namespace Xv6

open Iris Iris.ProgramLogic Iris.BI Std MachCSL
open LeanRV64D

variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [CurCtx]

/-! ## Geometry (Rocq `ProcGeom.v`) -/

/-- `proc[NPROC]` (kernel/proc.c), from the ELF symbol table of
`xv6-riscv/kernel/kernel` (`objdump -t`: `800127e8 g O .bss 5a00 proc`,
= `cpus` + 8·128); corroborated by `allocproc`'s `auipc s1,0x11; addi
s1,s1,-810`.  (The Rocq `KernelSyms.proc` is 0x80012768: a different
build of the same kernel.) -/
def procsAddr : BitVec 64 := 0x80012768#64

/-- `NPROC`. -/
def NPROC : Nat := 64
/-- `NOFILE`. -/
def NOFILE : Nat := 16
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
block reaches through its page-table and scheduler resources).  Left out:
the user page-table description `pv_upt`, the trapframe page contents
`pv_tf`, the descriptor ghost name `pv_fdg`, the cwd inum `pv_cwi`. -/
structure ProcPriv where
  kstack : BitVec 64
  sz : BitVec 64
  pagetable : BitVec 64
  trapframe : BitVec 64
  /-- the 14 saved words of `p->context` -/
  context : List (BitVec 64)
  /-- the 16 file pointers of `p->ofile` -/
  ofile : List (BitVec 64)
  cwd : BitVec 64
  /-- the 16 bytes of `p->name` -/
  name : List (BitVec 8)

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

/-- The process's user page table at `V.pagetable`, `V.sz` bytes mapped
(Rocq `proc_ptm_at`): not ported yet (placeholder). -/
def procPt (V : ProcPriv) : IProp GF := iprop(⌜V = V⌝)

/-- The trapframe page at `V.trapframe` (Rocq `tf_page`): not ported yet
(placeholder). -/
def tfPage (V : ProcPriv) : IProp GF := iprop(⌜V = V⌝)

/-- The pid cell's fractions: the running thread's half rides in `procPriv`,
the lock-protected public part has the other half (Rocq: a quarter in
`proc_pub`, a quarter with `pid_lock`; the lock is not ported, so its
quarter is merged into the public part here). -/
def pidHalf : DFrac := DFrac.own (Qp.half 1)

/-- The private block of a running process (Rocq `proc_priv_bare`, and
`proc_priv_core` minus the cwd inode reference): the size bounds, half of
`p->pid`, the private fields, the page table and the trapframe page. -/
def procPriv (pa : BitVec 64) (pid : BitVec 32) (V : ProcPriv) : IProp GF := iprop%
  ⌜V.sz.toNat ≤ MAXVA⌝ ∗
  wordPointsTo (pPid pa) 4 pidHalf pid ∗
  procFields pa (DFrac.own 1) V ∗
  procPt V ∗
  tfPage V

/-! ## The public part (Rocq `SchedCtx.proc_pub`, `proc_held`) -/

/-- The fields `p->lock` protects (Rocq `proc_held` minus the lock token
and the state ghost mirror): `state`, `chan`, `killed`, `xstate` whole and
the other half of `pid`. -/
def procPub (pa : BitVec 64) (st : BitVec 32) (chan : BitVec 64) (killed xstate pid : BitVec 32) :
    IProp GF := iprop%
  wordPointsTo (pState pa) 4 (DFrac.own 1) st ∗
  wordPointsTo (pChan pa) 8 (DFrac.own 1) chan ∗
  wordPointsTo (pKilled pa) 4 (DFrac.own 1) killed ∗
  wordPointsTo (pXstate pa) 4 (DFrac.own 1) xstate ∗
  wordPointsTo (pPid pa) 4 pidHalf pid

/-! ## Dormant slots (Rocq `proc_dormant`, `proc_slots`) -/

/-- A slot nobody runs (UNUSED or ZOMBIE): the private block's cells with
existential values, no open files, no cwd (Rocq `proc_dormant`; its file
descriptor / inode / buffer allowances are not ported). -/
def procDormant (pa : BitVec 64) (st : BitVec 32) : IProp GF := iprop%
  ⌜st = UNUSED ∨ st = ZOMBIE⌝ ∗
  ∃ (V : ProcPriv) (pid : BitVec 32),
    ⌜V.ofile = List.replicate NOFILE 0#64 ∧ V.cwd = 0#64 ∧ V.sz.toNat ≤ MAXVA⌝ ∗
    wordPointsTo (pPid pa) 4 pidHalf pid ∗
    procFields pa (DFrac.own 1) V

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
