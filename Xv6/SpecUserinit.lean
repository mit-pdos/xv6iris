/-
Specification of `userinit` (kernel/proc.c), the first process:

    void userinit(void) {
      struct proc *p = allocproc();
      initproc = p;
      p->cwd = namei("/");
      p->state = RUNNABLE;
      release(&p->lock);
    }

BOOT CODE: it runs on the boot hart before any scheduler does, so there
is no process on this hart (`k.proc = 0`), no claim and no parking.  Both
of its callees are fine with that -- `allocproc` never calls `myproc` and
is generic in the interrupt index, and `namei("/")` is the REAL root corner
(`SpecNamei.NAMEI_ROOT`, Rocq `NAMEI_ROOT_BOOT`, wave 7 W7-C retired the
assumed `FsEnv.nameiBoot`): a path of one separator never walks, so the only
callee is `iget(ROOTDEV, ROOTINO)` -- no process, no transaction, nothing to
sleep on.  Its demand is Rocq's four inode-cache rows (`isItable2`,
`itableInv`, `iregReg`; Rocq's `ic_escrows` rides `isItable2`, SpecNamex's
"Dropped") and `panicEnv` (iget's live "no inodes" panic), plus the two
configuration ties `icfgDev = ROOTDEV` and `0 < icfgNib`.  The path "/" is a
`.rodata` literal, read off `kernelData`.

INTERRUPTS ARE OFF (`hsie : k.sie = false`): `main` runs the whole of boot
at `SIE = 0` (it is `scheduler` that first enables them).  The hypothesis is
REQUIRED, not cosmetic: `userinit`'s closing `release` is the pop of the
push_off `allocproc`'s last `acquire` did, and at `SIE = 1` that pop has to
hand the trap resources back (`popArm`/`sieArm`) -- but `allocproc`'s
success arm returns its context at `pushOffAt` (interrupts off) without
returning the arm, so a caller at `SIE = 1` cannot re-enable them.  Drop
this hypothesis only together with an `allocproc` post that hands
`sieArm cpu' k.sie k.proc` back on the success arm.

THE NEW PROCESS'S SUPPLY ALLOWANCES (`dormantAllow`, wave 7 P3) come out
of `allocproc`, and are spent as Rocq's are (SpecUserinit.v: "THE ONE
[iref_slot] namei's [iget] spends is NOT a premise"): the cwd's unit pays
the root's `iget`, and the rest (`liveAllow`) is parked with the process
(`ForkretRecord.newbornPay`).  PROCESS-LAYER DEVIATION (flagged): the
process's null descriptor table (with its per-descriptor units) and its cwd
reference (`inodeHeldAt ipv ROOTINO`, namei's result) are DROPPED at the park
(`SpecForkret`'s deviation: the file-layer predicates have no `CtxMorph`
yet); Rocq parks the whole `proc_priv`.  The D8 boot-token deposit
(`first_*`), `init_pid_tok`, the six park rows and the exec bundle are not
in this contract yet (D8 / the trap path).

IT PUBLISHES `initproc`.  The word at `&initproc` is written exactly once,
here, and read forever after (`kexit`'s "init exiting" check, `reparent`'s
target), so `userinit` takes it owned and gives it back DISCARDED, as the
persistent `initprocIs` every later reader takes as a premise.

COUNTED: `allocproc` needs a trapframe page and up to
`procPagetableNodes` table nodes, so the caller lends `kallocAvail γk
(some nb)` with `nb` over that bound and gets back what is left; and it
needs a FREE SLOT, which it does not check for, so the caller lends the
proc table's counted regime `procsAvail Γ (some (np + 1))`
(`Xv6/ProcAvail.lean`) -- the only thing that can refute `allocproc`'s
empty-table arm -- and gets back `procsAvail Γ (some np)`.  The
whole of the first process -- its block, its kernel stack, its parked
`forkret` record (`Xv6/ForkretRecord.lean`, whence `[ForkretIs]`) -- goes
into `procsInv` at the closing `release`, and the slot is left RUNNABLE
for the first scheduler that looks.

Imports only definitional files (never a `Code*` or `Proof*` file).
-/
import Xv6.SchedCtx
import Xv6.WaitLock
import Xv6.PidLock
import Xv6.SpecForkret
import Xv6.SpecNamei
import Xv6.SpecAllocproc
import Xv6.ProcAvail
import MachCSL.Lock
import MachCSL.WpSmodeIntr

namespace Xv6

open Iris Iris.ProgramLogic Iris.BI Std MachCSL
open LeanRV64D

/-- Address of `userinit`. -/
def userinitAddr : BitVec 64 := KA.«userinit»

/-- The stack `userinit`'s cone needs (Rocq `K_userinit = 4 +
K_namei_root_boot`): its own 4-slot frame over `namei`'s root corner
(`allocproc` needs 48, `release` 10). -/
def userinitSlots : Nat := 4 + nameiRootSlots

/-- **WP of `userinit`.** -/
def wp_userinit_body {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF] [FdslotG GF] [BioslotG GF]
    [IcacheG GF] [LogG GF] [FsBlocksG GF] [IregG GF] [FsTopG GF] [FsLinkG GF] [IcboxG GF]
    [SleepLockG GF] [IrefslotG GF] [CtokG GF] [WchG GF] [Appcfg GF] [Fscfg] [Icfg] [CurCtx]
    (Γ : SchedNames) [ClaimIs (hlc := hlc) GF Γ] [ForkretIs]
    (cpu : CPU) (k : KCtx) (γp γl : GName) (γk : KmemNames) (nb np : Nat)
    (hnoff : k.noff + 2 < 2 ^ 31) (hnoff0 : k.noff = 0) (hK : userinitSlots ≤ k.avail)
    (hlk : "kmem" ∉ k.locks) (hlp : "nextpid" ∉ k.locks) (hlq : "proc" ∉ k.locks)
    (hlocks : k.locks = []) (htier : k.tier = KTier.kpt) (hproc : k.proc = 0#64)
    (hsie : k.sie = false) (hnb : procPagetableNodes + 1 < nb)
    (hroot : icfgDev = BitVec.ofNat 32 ROOTDEV) (hnib0 : 0 < icfgNib) : Prop :=
  kctx cpu k ∗ pcIs cpu userinitAddr ∗ procsInv Γ ∗
  isLock γl kmemLockAddr "kmem" (kmemRes γk) ∗ isLock γp pidLockAddr "nextpid" pidLockPay ∗
  kallocAvail γk (some nb) ∗ procsAvail Γ (some (np + 1)) ∗
  (∃ w : BitVec 64, wordPointsTo initprocAddr 8 (DFrac.own 1) w) ∗
  -- namei("/")'s four inode-cache rows and iget's live panic
  isItable2 fscItlock fscIc fscFs fscIreg fscCov fscLogst icfgNib icfgDev ∗
  itableInv (hlc := hlc) ∗ iregReg (hlc := hlc) fscIreg fscFs icfgIst icfgNib ∗ panicEnv ∗
  wpNext k.sie k.proc cpu (fun cpu' => iprop(∀ (spie spp : Bool) (R' : RegMap) (ip : BitVec 64)
    (g : Nat),
    ⌜(k.sie = false → spie = k.spie ∧ spp = k.spp) ∧ calleeSaved k.regs R' ∧
      g ≤ procPagetableNodes + 1 ∧ ∃ i : Nat, i < NPROC ∧ ip = procAddr i⌝ -∗
    kctx cpu' ((k.withSpie spie spp).withRegs R') -∗ pcIs cpu' (jumpPc (k.regs 1#5)) -∗
    initprocIs ip -∗ kallocAvail γk (availSub (some nb) g) -∗ procsAvail Γ (some np) -∗ wpLoop cpu'))
  ⊢ wpLoop (GF := GF) cpu

/-- The interface of `userinit`. -/
structure USERINIT : Prop where
  wp_userinit : ∀ {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF] [FdslotG GF] [BioslotG GF]
    [IcacheG GF] [LogG GF] [FsBlocksG GF] [IregG GF] [FsTopG GF] [FsLinkG GF] [IcboxG GF]
    [SleepLockG GF] [IrefslotG GF] [CtokG GF] [WchG GF] [Appcfg GF] [Fscfg] [Icfg] [CurCtx]
    (Γ : SchedNames) [ClaimIs (hlc := hlc) GF Γ] [ForkretIs]
    (cpu : CPU) (k : KCtx) (γp γl : GName) (γk : KmemNames) (nb np : Nat)
    hnoff hnoff0 hK hlk hlp hlq hlocks htier hproc hsie hnb hroot hnib0,
    wp_userinit_body (hlc := hlc) (GF := GF) Γ cpu k γp γl γk nb np
      hnoff hnoff0 hK hlk hlp hlq hlocks htier hproc hsie hnb hroot hnib0

end Xv6
