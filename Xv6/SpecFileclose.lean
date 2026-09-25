/-
The interface of `fileclose` (Rocq SpecFileclose.v), for the file types the
Lean development models: a closed (`FD_NONE`) file and a pipe end.

    void fileclose(struct file *f) {
      struct file ff;
      acquire(&ftable.lock);
      if (f->ref < 1) panic("fileclose");
      if (--f->ref > 0) { release(&ftable.lock); return; }
      ff = *f; f->ref = 0; f->type = FD_NONE;
      release(&ftable.lock);
      if (ff.type == FD_PIPE) pipeclose(ff.pipe, ff.writable);
      else if (ff.type == FD_INODE || ff.type == FD_DEVICE) { begin_op(); iput(ff.ip); end_op(); }
    }

THE REFERENCE HALF (stable): a `fileRef γ k q st` goes in, one `fdSlot γ`
comes back, and nothing says which arm ran.  Not the last reference: the
departing fraction is absorbed into the lock's leftover (`fileRest_absorb`).
The last: the lock's leftover makes it the whole slot (`fileRest_join`),
which licenses the `ff = *f` read, the `f->type = FD_NONE` store, and puts a
WHOLE pipe end in `pipeclose`'s hands.  The `f->ref < 1` panic is dead: the
caller's reference is in the slot's list, so `ref >= 1`.

THE OTHER HALF: the last close of a pipe end runs `pipeclose`, whose fabric
(the kmem lock and page count, `procsInv` for the wakeup) the caller must
own; `fclosePost` says the page count is untouched unless the file was a
pipe.  The inode/device arm is out of scope (no inode layer yet), so `st` is
restricted to `.closed` or a pipe (`fcStateOk`).  As `pipeclose`, this is
balanced and generic in the interrupt index: the continuation is at
whichever hart the thread lands on, at `k.sie` with `SPIE`/`SPP` pinned by
whatever trap ran.
-/
import Xv6.SpecPipeclose
import Xv6.FileDefs
import Xv6.FsEnv

namespace Xv6

open Iris Iris.ProgramLogic Iris.BI Std MachCSL
open LeanRV64D

/-- The states this interface covers. -/
def fcStateOk : FdState → Prop
  | .closed => True
  | .open _ _ .pipe => True
  | _ => False

/-- The stack `fileclose`'s cone needs: its own 8-slot frame over
`pipeclose`'s 22 (`acquire`/`release`'s 10 fit under). -/
def filecloseSlots : Nat := 8 + pipecloseSlots

/-- What comes back about the page count: `pipeclose`'s disjunction on a pipe,
the count unchanged otherwise. -/
def fclosePost {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF]
    (γk : KmemNames) (on : Option Nat) : FdState → IProp GF
  | .open _ _ .pipe => iprop(kallocAvail γk on ∨ kallocAvail γk (availInc on))
  | _ => kallocAvail γk on

def wp_fileclose_body {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF] [FileG GF] [IcacheG GF] [SleepLockG GF] [IcboxG GF] [IrefslotG GF] [OffboxG GF] [OffboxBoxG GF] [Icfg] [CurCtx]
    (Γ : SchedNames) (cpu : CPU) (k : KCtx) (γl : GName) (γ : FileNames) (kk : Nat) (q : Qp) (st : FdState)
    (γkl : GName) (γk : KmemNames) (on : Option Nat)
    (hst : fcStateOk st)
    (hnoff : k.noff + 2 < 2 ^ 31) (hK : filecloseSlots ≤ k.avail) (hlk : "ftable" ∉ k.locks)
    (hpipe : "pipe" ∉ k.locks) (hproc : "proc" ∉ k.locks) (hkmem : "kmem" ∉ k.locks)
    (htier : k.tier = KTier.kpt)
    (ha0 : k.regs 10#5 = fnode kk) : Prop :=
  kctx cpu k ∗ pcIs cpu filecloseAddr ∗ isFtable γl γ ∗ fileRef γ kk q st ∗
  isLock γkl kmemLockAddr "kmem" (kmemRes γk) ∗ kallocAvail γk on ∗ procsInv Γ ∗
  wpNext k.sie k.proc cpu (fun cpu' => iprop(∀ spie : Bool, ∀ spp : Bool, ∀ R' : RegMap,
    ⌜k.sie = false → spie = k.spie ∧ spp = k.spp⌝ -∗
    kctx cpu' ((k.withSpie spie spp).withRegs R') -∗ pcIs cpu' (jumpPc (k.regs 1#5)) -∗
    ⌜calleeSaved k.regs R'⌝ -∗ fdSlot γ -∗ fclosePost γk on st -∗ wpLoop cpu'))
  ⊢ wpLoop (GF := GF) cpu

structure FILECLOSE : Prop where
  wp_fileclose : ∀ {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF] [FileG GF] [IcacheG GF] [SleepLockG GF] [IcboxG GF] [IrefslotG GF] [OffboxG GF] [OffboxBoxG GF] [Icfg] [CurCtx]
    (Γ : SchedNames) (cpu : CPU) (k : KCtx) (γl : GName) (γ : FileNames) (kk : Nat) (q : Qp) (st : FdState)
    (γkl : GName) (γk : KmemNames) (on : Option Nat)
    hst hnoff hK hlk hpipe hproc hkmem htier ha0,
    wp_fileclose_body (hlc := hlc) (GF := GF) Γ cpu k γl γ kk q st γkl γk on hst hnoff hK hlk hpipe hproc
      hkmem htier ha0

end Xv6
