/-
The interface of `sys_close` (Rocq SpecSysClose.v).

    uint64 sys_close(void) {
      int fd; struct file *f;
      if (argfd(0, &fd, &f) < 0) return -1;
      myproc()->ofile[fd] = 0;
      fileclose(f);
      return 0;
    }

TWO ARMS, decided by the syscall argument and the process's own array
(`argFd`): no such descriptor, everything untouched; or the descriptor's
cell is nulled, its row in the fragment bundle becomes `.closed`, and the
file's reference is spent into `fileclose`.  The page-count fact comes back
as `fileclose`'s disjunction (the descriptor may have held a pipe's last
end), separately from the two arms.

RESTRICTION: the Lean `fileclose` covers only pipes (there is no inode
layer), so the descriptor argument 0 names, if any, must be a pipe end --
`hpipe`, read off the caller's bundle.  `hsp` is the stack bound Rocq
takes from `sie_cap_gpr`: the two locals are passed to argfd by address.
-/
import Xv6.SpecArgfd
import Xv6.SpecFileclose

namespace Xv6

open Iris Iris.ProgramLogic Iris.BI Std MachCSL
open LeanRV64D

def sysCloseAddr : BitVec 64 := KA.«sys_close»

/-- sys_close's 4-slot frame over `fileclose`'s cone (argfd's 24, myproc's 10 fit under). -/
def sysCloseSlots : Nat := 4 + filecloseSlots

section
variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF] [FileG GF] [IcacheG GF] [SleepLockG GF] [IcboxG GF] [IrefslotG GF] [OffboxG GF] [OffboxBoxG GF] [Icfg] [CurCtx]

/-- sys_close's result, keyed by the returned `a0`. -/
def sysClosePost (γ : FileNames) (γd : Nat → GName) (pa : BitVec 64) (pid : BitVec 32) (V : ProcPriv)
    (M : Nat → List (BitVec 8)) (sts : List FdState) (v : BitVec 64) (r : BitVec 64) : IProp GF := iprop%
  (⌜r = 0xFFFFFFFFFFFFFFFF#64 ∧ argFd v V.ofile = none⌝ ∗ procPrivFd γ γd pa pid V M ∗ fdFrags γd sts) ∨
  (∃ (fd : Nat) (fv : BitVec 64), ⌜r = 0#64 ∧ argFd v V.ofile = some (fd, fv)⌝ ∗
    procPrivFd γ γd pa pid { V with ofile := V.ofile.set fd 0#64 } M ∗ fdFrags γd (sts.set fd .closed))

def wp_sys_close_body (Γ : SchedNames) (cpu : CPU) (k : KCtx) (γl : GName) (γ : FileNames) (γd : Nat → GName)
    (pa : BitVec 64) (pid : BitVec 32) (V : ProcPriv) (M : Nat → List (BitVec 8)) (sts : List FdState)
    (v : BitVec 64) (γkl : GName) (γk : KmemNames) (on : Option Nat)
    (hv : V.tf[tfArgIdx 0]? = some v) (hproc : k.proc = pa) (htier : k.tier = KTier.kpt)
    (hsp : 48 ≤ (k.regs 2#5).toNat)
    (hpipe : ∀ fd fv, argFd v V.ofile = some (fd, fv) → ∃ r w, sts[fd]? = some (.open r w .pipe))
    (hnoff : k.noff + 2 < 2 ^ 31) (hK : sysCloseSlots ≤ k.avail) (hlk : "ftable" ∉ k.locks)
    (hplk : "pipe" ∉ k.locks) (hprc : "proc" ∉ k.locks) (hkmem : "kmem" ∉ k.locks) : Prop :=
  kctx cpu k ∗ pcIs cpu sysCloseAddr ∗ isFtable γl γ ∗
  isLock γkl kmemLockAddr "kmem" (kmemRes γk) ∗ kallocAvail γk on ∗ procsInv Γ ∗
  procPrivFd γ γd pa pid V M ∗ fdFrags γd sts ∗
  wpNext k.sie k.proc cpu (fun cpu' => iprop(∀ spie : Bool, ∀ spp : Bool, ∀ R' : RegMap,
    ⌜k.sie = false → spie = k.spie ∧ spp = k.spp⌝ -∗
    kctx cpu' ((k.withSpie spie spp).withRegs R') -∗ pcIs cpu' (jumpPc (k.regs 1#5)) -∗
    ⌜calleeSaved k.regs R'⌝ -∗ sysClosePost γ γd pa pid V M sts v (R' 10#5) -∗
    (kallocAvail γk on ∨ kallocAvail γk (availInc on)) -∗ wpLoop cpu'))
  ⊢ wpLoop (GF := GF) cpu

end

structure SYSCLOSE : Prop where
  wp_sys_close : ∀ {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF] [FileG GF] [IcacheG GF] [SleepLockG GF] [IcboxG GF] [IrefslotG GF] [OffboxG GF] [OffboxBoxG GF] [Icfg] [CurCtx]
    (Γ : SchedNames) (cpu : CPU) (k : KCtx) (γl : GName) (γ : FileNames) (γd : Nat → GName)
    (pa : BitVec 64) (pid : BitVec 32) (V : ProcPriv) (M : Nat → List (BitVec 8)) (sts : List FdState)
    (v : BitVec 64) (γkl : GName) (γk : KmemNames) (on : Option Nat)
    hv hproc htier hsp hpipe hnoff hK hlk hplk hprc hkmem,
    wp_sys_close_body (hlc := hlc) (GF := GF) Γ cpu k γl γ γd pa pid V M sts v γkl γk on
      hv hproc htier hsp hpipe hnoff hK hlk hplk hprc hkmem

end Xv6
