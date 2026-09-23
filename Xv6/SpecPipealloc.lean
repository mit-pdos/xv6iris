/-
The interface of `pipealloc` (Rocq SpecPipealloc.v).

    int pipealloc(struct file **f0, struct file **f1) {
      struct pipe *pi = 0;
      *f0 = *f1 = 0;
      if ((*f0 = filealloc()) == 0 || (*f1 = filealloc()) == 0) goto bad;
      if ((pi = (struct pipe*)kalloc()) == 0) goto bad;
      pi->readopen = 1; pi->writeopen = 1; pi->nwrite = 0; pi->nread = 0;
      initlock(&pi->lock, "pipe");
      (*f0)->type = FD_PIPE; (*f0)->readable = 1; (*f0)->writable = 0; (*f0)->pipe = pi;
      (*f1)->type = FD_PIPE; (*f1)->readable = 0; (*f1)->writable = 1; (*f1)->pipe = pi;
      return 0;
    bad:
      if (pi) kfree((char*)pi);   -- dead: every path to bad has pi = 0
      if (*f0) fileclose(*f0);
      if (*f1) fileclose(*f1);
      return -1;
    }

pipealloc is the sole constructor of a pipe: the two exclusive `fileRef`s
filealloc hands back license the eight unlocked stores into the two
`struct file`s, and the fresh page kalloc hands back becomes the pipe.  A
file's PAYLOAD is published as `f->pipe` is written: the slot's
payload-names field is updated (`fpayTok_update`) with the pipe's names,
legal with no lock because this is the only reference.  The two ends come
out INSIDE their files: `FdState.open true false .pipe` is the read end and
`.open false true .pipe` the write end (`fdstateOk` ties the flags to the
cells).  On the bad paths the two `struct file *` cells are NOT restored,
so failure promises the cells back with unspecified contents, both fd
units back, and the page count untouched.

pipealloc holds no lock across a call; its callees are push/pop balanced.
Since `fileclose` returns hart-generically, so does pipealloc.
-/
import Xv6.SpecFileclose
import Xv6.SpecKalloc

namespace Xv6

open Iris Iris.ProgramLogic Iris.BI Std MachCSL
open LeanRV64D

def pipeallocAddr : BitVec 64 := KA.«pipealloc»

/-- pipealloc's own 6-slot frame over `fileclose`'s cone (the deepest callee). -/
def pipeallocSlots : Nat := 6 + filecloseSlots

def pipeallocPost {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF] [FileG GF] [CurCtx]
    (γ : FileNames) (γk : KmemNames) (on : Option Nat) (pf0 pf1 r : BitVec 64) : IProp GF := iprop%
  (⌜r = 0xFFFFFFFFFFFFFFFF#64⌝ ∗ kallocAvail γk on ∗ fdSlot γ ∗ fdSlot γ ∗
    (∃ w0 w1 : BitVec 64, wordPointsTo pf0 8 (DFrac.own 1) w0 ∗ wordPointsTo pf1 8 (DFrac.own 1) w1)) ∨
  (⌜r = 0#64⌝ ∗ kallocAvail γk (availDec on) ∗
    ∃ k0 k1 : Nat, ⌜k0 < NFILE ∧ k1 < NFILE⌝ ∗
      wordPointsTo pf0 8 (DFrac.own 1) (fnode k0) ∗ wordPointsTo pf1 8 (DFrac.own 1) (fnode k1) ∗
      fileRef γ k0 1 (.open true false .pipe) ∗ fileRef γ k1 1 (.open false true .pipe))

def wp_pipealloc_body {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF] [FileG GF] [CurCtx]
    (Γ : SchedNames) (cpu : CPU) (k : KCtx) (γl : GName) (γ : FileNames)
    (γkl : GName) (γk : KmemNames) (on : Option Nat) (v0 v1 : BitVec 64)
    (hnoff : k.noff + 2 < 2 ^ 31) (hK : pipeallocSlots ≤ k.avail) (hlk : "ftable" ∉ k.locks)
    (hpipe : "pipe" ∉ k.locks) (hproc : "proc" ∉ k.locks) (hkmem : "kmem" ∉ k.locks)
    (htier : k.tier = KTier.kpt) : Prop :=
  kctx cpu k ∗ pcIs cpu pipeallocAddr ∗ isFtable γl γ ∗
  isLock γkl kmemLockAddr "kmem" (kmemRes γk) ∗ kallocAvail γk on ∗ procsInv Γ ∗
  fdSlot γ ∗ fdSlot γ ∗
  wordPointsTo (k.regs 10#5) 8 (DFrac.own 1) v0 ∗ wordPointsTo (k.regs 11#5) 8 (DFrac.own 1) v1 ∗
  wpNext k.sie k.proc cpu (fun cpu' => iprop(∀ spie : Bool, ∀ spp : Bool, ∀ R' : RegMap,
    ⌜k.sie = false → spie = k.spie ∧ spp = k.spp⌝ -∗
    kctx cpu' ((k.withSpie spie spp).withRegs R') -∗ pcIs cpu' (jumpPc (k.regs 1#5)) -∗
    ⌜calleeSaved k.regs R'⌝ -∗ pipeallocPost γ γk on (k.regs 10#5) (k.regs 11#5) (R' 10#5) -∗ wpLoop cpu'))
  ⊢ wpLoop (GF := GF) cpu

structure PIPEALLOC : Prop where
  wp_pipealloc : ∀ {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF] [FileG GF] [CurCtx]
    (Γ : SchedNames) (cpu : CPU) (k : KCtx) (γl : GName) (γ : FileNames)
    (γkl : GName) (γk : KmemNames) (on : Option Nat) (v0 v1 : BitVec 64)
    hnoff hK hlk hpipe hproc hkmem htier,
    wp_pipealloc_body (hlc := hlc) (GF := GF) Γ cpu k γl γ γkl γk on v0 v1 hnoff hK hlk hpipe hproc hkmem htier

end Xv6
