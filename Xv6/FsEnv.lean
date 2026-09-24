/-
Xv6: the ASSUMED file-system interface.

The file system and user mode are not modelled.  The process code calls a
handful of fs entry points (`fileclose`, `begin_op`/`end_op`, `iput`,
`namei`, `filedup`, `idup`); every one of them may sleep, so its assumed
contract is SLEEP-SHAPED: exactly the premises and post of `wp_sleep_body`
(`Xv6.SpecSleep`) with the entry address abstracted -- the caller runs
with interrupts off at depth 0, holding no lock, on its own process; the
scheduler invariant, the trap CSRs, the hart's claim and the interrupt
resource go in and come back; callee-saved registers are preserved; the
return register is unconstrained (`fileclose(f)` ignores `f`;
`filedup`/`idup`/`namei` return some word).

The whole of `forkret` is assumed too (`Xv6.SpecForkret`): it runs `fsinit`
and `kexec` on the first process and returns to user mode through the
trampoline.

These are class assumptions in the style of `ClaimIs`/`EnvIs`: a proof
that needs them takes `[FsEnv GF]`.
-/
import Xv6.SpecSleep

namespace Xv6

open Iris Iris.ProgramLogic Iris.BI Std MachCSL
open LeanRV64D

def filecloseAddr : BitVec 64 := KA.«fileclose»
def fsBeginOpAddr : BitVec 64 := KA.«begin_op»
def fsEndOpAddr : BitVec 64 := KA.«end_op»
def iputAddr : BitVec 64 := KA.«iput»
def nameiAddr : BitVec 64 := KA.«namei»
def filedupAddr : BitVec 64 := KA.«filedup»
def idupAddr : BitVec 64 := KA.«idup»

/-- The stack an fs entry point may use (assumed). -/
def fsSlots : Nat := 64

/-- **A blocking call** (the shape of `wp_sleep_body` at entry `entry`). -/
def wp_blocking_body {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF] [CurCtx]
    (Γ : SchedNames) [ClaimIs (hlc := hlc) GF Γ]
    (cpu : CPU) (k : KCtx) (j : Nat) (entry : BitVec 64)
    (hj : j < NPROC) (hproc : k.proc = procAddr j) (hK : fsSlots ≤ k.avail)
    (hsie : k.sie = false) (hnoff : k.noff = 0) (hlocks : k.locks = [])
    (htier : k.tier = KTier.kpt) : Prop :=
  kctx cpu k ∗ pcIs cpu entry ∗ procsInv Γ ∗
  trapCsrs cpu ∗ cpuClaim cpu k.proc ∗ intrRes cpu ∗
  wpNext true k.proc cpu (fun cpu' => iprop(∀ spie : Bool, ∀ spp : Bool, ∀ R' : RegMap,
    kctx cpu' ((k.withSpie spie spp).withRegs R') -∗ pcIs cpu' (jumpPc (k.regs 1#5)) -∗
    trapCsrs cpu' -∗ cpuClaim cpu' k.proc -∗ intrRes cpu' -∗
    ⌜calleeSaved k.regs R'⌝ -∗ wpLoop cpu'))
  ⊢ wpLoop (GF := GF) cpu

/-- **A NON-BLOCKING fs call**: one that takes only its own file-system
spinlocks (below `"proc"` in rank) and never sleeps -- `filedup`/`idup`
(ref-count bumps under `ftable`/`itable`), and `namei("/")` at boot (no
scheduler to sleep on).  Balanced and generic: any interrupt index, any
lock depth (`kfork` calls `filedup`/`idup` holding the child's `p->lock`;
`userinit` calls `namei` holding it too), any process (`k.proc`
unconstrained).  It gives `k.locks`/`k.noff` back unchanged and returns
some word in `a0`.  This is the sound contract for a call that only takes
lower-ranked locks -- the sleep-shaped `FsEntry` (which pins
`k.locks = []`) would wrongly forbid the held `"proc"` lock. -/
def wp_nb_blocking_body {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF] [CurCtx]
    (Γ : SchedNames) (cpu : CPU) (k : KCtx) (entry : BitVec 64)
    (hK : fsSlots ≤ k.avail) (hnoff : k.noff + 1 < 2 ^ 31)
    (htier : k.tier = KTier.kpt) : Prop :=
  kctx cpu k ∗ pcIs cpu entry ∗ procsInv Γ ∗
  wpNext k.sie k.proc cpu (fun cpu' => iprop(∀ spie : Bool, ∀ spp : Bool, ∀ R' : RegMap,
    ⌜k.sie = false → spie = k.spie ∧ spp = k.spp⌝ -∗
    kctx cpu' ((k.withSpie spie spp).withRegs R') -∗ pcIs cpu' (jumpPc (k.regs 1#5)) -∗
    ⌜calleeSaved k.regs R'⌝ -∗ wpLoop cpu'))
  ⊢ wpLoop (GF := GF) cpu

/-- The assumed contract of one non-blocking fs entry point. -/
def FsEntryNB (entry : BitVec 64) : Prop :=
  ∀ {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF] [CurCtx]
    (Γ : SchedNames) (cpu : CPU) (k : KCtx) hK hnoff htier,
    wp_nb_blocking_body (hlc := hlc) (GF := GF) Γ cpu k entry hK hnoff htier

/-- The assumed contract of one fs entry point. -/
def FsEntry (entry : BitVec 64) : Prop :=
  ∀ {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF] [CurCtx]
    (Γ : SchedNames) [ClaimIs (hlc := hlc) GF Γ]
    (cpu : CPU) (k : KCtx) (j : Nat) hj hproc hK hsie hnoff hlocks htier,
    wp_blocking_body (hlc := hlc) (GF := GF) Γ cpu k j entry hj hproc hK hsie hnoff hlocks htier

/-- **The file-system boundary** (assumed). -/
class FsEnv : Prop where
  fileclose : FsEntry filecloseAddr
  begin_op : FsEntry fsBeginOpAddr
  end_op : FsEntry fsEndOpAddr
  iput : FsEntry iputAddr
  namei : FsEntry nameiAddr
  filedup : FsEntryNB filedupAddr
  idup : FsEntryNB idupAddr
  /-- `userinit` calls `namei("/")` on the boot hart, where no process runs
  yet (`Xv6/SpecUserinit.lean`). -/
  nameiBoot : FsEntryNB nameiAddr

end Xv6
