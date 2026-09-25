/-
`forkret` (kernel/proc.c) -- ASSUMED as a whole.

    void forkret(void) {
      static int first = 1;
      release(&myproc()->lock);
      if (first) { fsinit(ROOTDEV); first = 0; __sync_synchronize();
                   kexec("/init", argv); }
      usertrapret();
    }

It is the entry point every process is BORN at: `allocproc` writes
`p->context.ra = forkret` and `p->context.sp = p->kstack + PGSIZE`, so the
first thing a fresh process ever does is to be RESUMED by a scheduler at
`forkret` out of its own parked record.  It runs `fsinit` and `kexec` on
the very first process and then leaves the kernel through the trampoline
(`usertrapret` / `userret`), which this port does not model -- so `forkret`
is assumed, and what is assumed is exactly THE RESUME WAND OF A FRESH
PROCESS'S RECORD: the configuration `sched`'s swtch hands a resumed
thread (`Xv6.wp_sched_body`'s continuation, `MachCSL.resumedK`), with the
bundle's `ra` already pointing at `forkret` and its `sp` at the top of the
process's kernel stack.

The premises are, one for one, what the record of `Xv6/ForkretRecord.lean`
produces when a scheduler resumes it:

* `kctx cpu (resumedK R spie spp 512 intena root (procAddr j))` -- interrupts
  off, `noff = 1`, `locks = ["proc"]`, the kernel table, the whole kernel
  stack (512 slots below `R sp`), and the resumed proc as `c->proc`;
* `pcIs cpu forkretAddr` (`R ra = forkretAddr`, and `jumpPc` of an even
  address is itself);
* the scheduler invariant, the resuming hart's trap CSRs and installed
  handler;
* `p->lock` HELD at RUNNING with the whole hart tag and the resuming hart's
  parked scheduler record -- what `swtch` handed over;
* the process's WHOLE private block (`procPrivFd`: the core -- bare block,
  cwd reference, D8 generation row `procGenAt` with the `firstTok` forkret's
  `if (first)` branches on -- and the descriptor table with its payloads)
  beside its fragment bundle `fdFrags V.fdg sts` and the 14 save-area words
  (`contextCells`, which the record hands back and forkret splits off
  itself when it releases `p->lock`), its spare allowances (`liveAllow`:
  `fdSlots FDSPARE ∗ irefSlots IREFSPARE ∗ bslots 3`, wave 7 W7-C -- the rest
  of what its creator took out of the slot's dormant block; Rocq's newborn
  park carries them into the trap residue, `SpecForkretParkPaid`), and the
  slot's children row at `∅` (`chFrag V.chg (procAddr j) ∅`, D8 wiring;
  Rocq's `UsertrapRes.ut_own` carries it, where fork moves it).

THE WHOLE BLOCK (D8 wiring; closes wave 7 W7-C's flagged deviation "the
newborn record drops the file table, fragments and cwd reference"): the
record transports its payload across the context move (`ctx_move`, a
`CtxMorph`), and the file-layer predicates have their transports now
(`FileMorph`, `EnvMorph.procPrivFd_morph`, `FileMorph.isPipe_morph`), so
the record parks Rocq's whole `proc_priv` and `fd_frags`.

Imports only definitional files.
-/
import Xv6.SchedCtx
import Xv6.SpecAllocproc
import Xv6.FdTable
import MachCSL.WpSmodeIntr

namespace Xv6

open Iris Iris.ProgramLogic Iris.BI Std MachCSL
open LeanRV64D

/-- The kernel stack a born process resumes on: the whole `KSTACK` page,
512 slots below `p->kstack + PGSIZE`. -/
def forkretStack : Nat := 512

/-- `forkret`'s entry is even, so `jumpPc` of it is itself. -/
theorem jumpPc_forkretAddr : jumpPc forkretAddr = forkretAddr := by
  unfold forkretAddr jumpPc
  decide

/-- **WP of `forkret`** (assumed): the resume wand of a fresh process's
record. -/
def wp_forkret_body {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF] [FdslotG GF] [BioslotG GF]
    [BcacheG GF] [SleepLockG GF] [DiskG GF] [IcacheG GF] [LogG GF] [FsBlocksG GF] [IregG GF]
    [FsTopG GF] [FsLinkG GF] [IcboxG GF] [OffboxG GF] [OffboxBoxG GF] [IrefslotG GF] [CtokG GF] [WchG GF]
    [Appcfg GF] [FileG GF] [Fscfg] [Icfg] [CurCtx]
    (Γ : SchedNames) [ClaimIs (hlc := hlc) GF Γ]
    (cpu : CPU) (R : RegMap) (spie spp intena : Bool) (root : BitVec 44)
    (j : Nat) (ch : BitVec 64) (γ : FileNames) (pid : BitVec 32) (V : ProcPriv) (M : Nat → List (BitVec 8))
    (sts : List FdState)
    (hj : j < NPROC) (hra : R 1#5 = forkretAddr) (hsp : R 2#5 = V.kstack + 4096#64) : Prop :=
  kctx cpu (resumedK R spie spp forkretStack intena root (procAddr j)) ∗
  pcIs cpu forkretAddr ∗ procsInv Γ ∗ trapCsrs cpu ∗ intrRes cpu ∗
  procHeld Γ cpu j RUNNING ch ∗ hartFull Γ j cpu ∗
  ▷ schedVcAt Γ cpu (cpuCtxAddr cpu) (procAddr j) ∗
  contextCells (procAddr j) (DFrac.own 1) V.context ∗
  procPrivFd γ (procAddr j) pid V M ∗ fdFrags V.fdg sts ∗ liveAllow ∗ chFrag V.chg (procAddr j) ∅
  ⊢ wpLoop (GF := GF) cpu

/-- **The `forkret` boundary** (assumed; the retired `FsEnv` boundary's last sibling): the user-mode
return is out of scope. -/
class ForkretIs : Prop where
  wp_forkret : ∀ {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF] [FdslotG GF] [BioslotG GF]
    [BcacheG GF] [SleepLockG GF] [DiskG GF] [IcacheG GF] [LogG GF] [FsBlocksG GF] [IregG GF]
    [FsTopG GF] [FsLinkG GF] [IcboxG GF] [OffboxG GF] [OffboxBoxG GF] [IrefslotG GF] [CtokG GF] [WchG GF]
    [Appcfg GF] [FileG GF] [Fscfg] [Icfg] [CurCtx]
    (Γ : SchedNames) [ClaimIs (hlc := hlc) GF Γ]
    (cpu : CPU) (R : RegMap) (spie spp intena : Bool) (root : BitVec 44)
    (j : Nat) (ch : BitVec 64) (γ : FileNames) (pid : BitVec 32) (V : ProcPriv) (M : Nat → List (BitVec 8))
    (sts : List FdState) hj hra hsp,
    wp_forkret_body (hlc := hlc) (GF := GF) Γ cpu R spie spp intena root j ch γ pid V M sts hj hra hsp

end Xv6
