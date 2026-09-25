/-
**THE DISPATCH'S DEPOSIT LAWS, AT THE KERNEL'S INSTANCE** (the Lean-side
half of Rocq `ProofSyscall`'s `sysc_dep_<n>`/`sysc_out_<n>` over
`UexecExecInst`'s per-number readers).

Each syscall arm file states the deposit law it consumes as a `Prop`
hypothesis over an ABSTRACT `[UexecSG GF]` (`SyscallArmsPath.SyscDep{Chdir,
Open,Mknod,Unlink,Link,Mkdir}`, `SyscallArmsProc.SyscDepKill`,
`SyscallArmsExec.SyscDepExec`, `SyscallArmsFdDefs.SyscDep{Read,Pipe,Close}`),
and the syscall seal specialises `SYSCALL` to `UexecExecInst.uexecSGXv6`
(Rocq's single global instance).  This file proves each of them there, in
exactly the arm file's statement, beside `SyscSpostEmp`
(`UexecExecInst.syscSpostEmp_xv6`).

## Deviations / blockers

1. **`SyscDepWrite` is NOT proved unconditionally**: it asks for
   `SpecFilewrite.filewriteIn` at the key, whose inode and device arms carry
   the caller's NO-WRAP conjunct `ua.toNat + n.toNat ≤ 2^64` (SpecFilewrite
   deviation 5).  That conjunct is a fact about the caller's buffer, not
   payable from the class's supply at every key, so the instance's row 16 is
   `FsAbsInvFire.filewriteChainIn` (UexecExecInst deviation 5) and the law is
   proved here only AT A NO-WRAP KEY (`syscDepWrite_at_nw`).  Unblocking:
   SpecWritei's `WriteiOut.usr` reports `src.toNat + tot ≤ 2^64` and
   SpecFilewrite drops the conjunct (a landed edit), after which
   `filewriteIn = filewriteChainIn` and the law is `syscDepWrite_at_nw`
   without its premise.
2. `syscFdKey` (SyscallArmsFdDefs) and `fdStOfKey` (UexecExecInst) are the
   same definition (Rocq `fd_st_of_key`), equal by `rfl`
   (`fdStOfKey_eq_syscFdKey`); recommended cleanup: keep one.
-/
import Xv6.UexecExecInst
import Xv6.SyscallArmsFdDefs
import Xv6.SyscallArmsPath
import Xv6.SyscallArmsProc
import Xv6.SyscallArmsExec

namespace Xv6

open Iris Iris.BI Iris.ProofMode Std MachCSL

set_option linter.unusedSectionVars false

theorem fdStOfKey_eq_syscFdKey (v : BitVec 64) (sts : List FdState) : fdStOfKey v sts = syscFdKey v sts :=
  rfl

section Laws
variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF] [FdslotG GF] [BioslotG GF]
  [BcacheG GF] [SleepLockG GF] [DiskG GF] [IcacheG GF] [LogG GF] [FsBlocksG GF] [IregG GF]
  [FsTopG GF] [FsLinkG GF] [IcboxG GF] [OffboxG GF] [OffboxBoxG GF] [IrefslotG GF] [CtokG GF] [WchG GF]
  [Appcfg GF] [FileG GF] [Fscfg] [Icfg] [CurCtx]

/-- **`SyscDepKill`** at the instance. -/
theorem syscDepKill_holds : SyscDepKill (hlc := hlc) (GF := GF) :=
  fun f W => syscDepKill_xv6 (hlc := hlc) _ f W

/-- **`SyscDepChdir`** at the instance. -/
theorem syscDepChdir_holds : SyscDepChdir (hlc := hlc) (GF := GF) := by
  intro f W
  refine (syscDepChdir_xv6 (hlc := hlc) f W).trans ?_
  iintro H
  iexists (Xfam.cP f), (Xfam.cPmiss f), (Xfam.cFo f)
  iexact H

/-- **`SyscDepUnlink`** at the instance. -/
theorem syscDepUnlink_holds : SyscDepUnlink (hlc := hlc) (GF := GF) := by
  intro f W
  refine (syscDepUnlink_xv6 (hlc := hlc) f W).trans ?_
  iintro H
  iexists (Xfam.uP f), (Xfam.uPmiss f), (Xfam.uFent f), (Xfam.uFtgt f), (Xfam.uFex f), (Xfam.uFmiss f)
  iexact H

/-- **`SyscDepLink`** at the instance. -/
theorem syscDepLink_holds : SyscDepLink (hlc := hlc) (GF := GF) := by
  intro f W
  refine (syscDepLink_xv6 (hlc := hlc) f W).trans ?_
  iintro H
  iexists (Xfam.lFtgt f), (Xfam.lFent f), (Xfam.lFunt f)
  iexact H

/-- **`SyscDepMkdir`** at the instance. -/
theorem syscDepMkdir_holds : SyscDepMkdir (hlc := hlc) (GF := GF) := by
  intro f W
  refine (syscDepMkdir_xv6 (hlc := hlc) f W).trans ?_
  iintro H
  iexists (Xfam.dP f), (Xfam.dPmiss f), (Xfam.dFarm f), (Xfam.dFdots f), (Xfam.dFun f), (Xfam.dFok f), (Xfam.dFex f)
  iexact H

/-- **`SyscDepMknod`** at the instance. -/
theorem syscDepMknod_holds : SyscDepMknod (hlc := hlc) (GF := GF) := by
  intro f W
  refine (syscDepMknod_xv6 (hlc := hlc) f W).trans ?_
  dsimp only [imgAgrees, xkA]
  iintro H
  iexists (Xfam.nP f), (Xfam.nPmiss f), (Xfam.nFarm f), (Xfam.nFun f), (Xfam.nFok f), (Xfam.nFex f)
  iexact H

/-- **`SyscDepOpen`** at the instance. -/
theorem syscDepOpen_holds : SyscDepOpen (hlc := hlc) (GF := GF) := by
  intro f W
  refine (syscDepOpen_xv6 (hlc := hlc) f W).trans ?_
  dsimp only [imgAgrees, xkA]
  iintro H
  iexists (Xfam.oP f), (Xfam.oPmiss f), (Xfam.oFarm f), (Xfam.oFun f), (Xfam.oFok f), (Xfam.oFex f), (Xfam.oFo f), (Xfam.oFt f)
  iexact H

/-- **`SyscDepExec`** at the instance: the key's guard instantiated at the
dispatch's own view (`imgAgrees_viewLazy`). -/
theorem syscDepExec_holds : SyscDepExec (hlc := hlc) (GF := GF) := by
  intro f V M sts gn cs pid
  refine (syscDepExec_xv6 (hlc := hlc) _ f (uvisOf V M sts gn cs pid)).trans ?_
  dsimp only [uvisOf, xkA]
  iintro ⟨#Hp, H⟩
  iframe Hp
  iexists (Xfam.xP f), (Xfam.xPmiss f), (Xfam.xFo f)
  iapply H
  ipureintro
  exact imgAgrees_viewLazy V.upt V.sz M

/-- **`SyscDepRead`** at the instance: the payload `True`, and the receipt
at the page view the returned block is at (`permOf_extSz` for the table
row). -/
theorem syscDepRead_holds : SyscDepRead (hlc := hlc) (GF := GF) := by
  intro f V M sts gn cs pid
  refine (syscDepRead_xv6 (hlc := hlc) f (uvisOf V M sts gn cs pid)).trans ?_
  dsimp only [uvisOf, xkA, fdStOfKey, syscFdKey, xpostRead, filereadExtra]
  iintro ⟨H, Hw⟩
  iexists (Xfam.rF f), (Xfam.rRd f), (Xfam.rRin f), iprop(True)
  iframe H
  isplitl []
  · ipureintro; trivial
  iintro %r %P' %M1 %d %⟨hext, -, hret⟩ ⟨-, Hc⟩
  iapply Hw
  isplitl []
  · ipureintro; exact hret
  iexists P', M1
  iframe Hc
  isplitl []
  · ipureintro; rfl
  · ipureintro; exact permOf_extSz hext

/-- **`SyscDepWrite`, AT A NO-WRAP KEY** (deviation 1: the unconditional
law is blocked on SpecFilewrite deviation 5). -/
theorem syscDepWrite_at_nw (f : Xfam GF) (V : ProcPriv) (M : Nat → List (BitVec 8)) (sts : List FdState)
    (gn : GName) (cs : ExtTreeSet GName compare) (pid : BitVec 32)
    (hnw : (tfW V.tf (tfArgIdx 1)).toNat + (argZ (tfW V.tf (tfArgIdx 2))).toNat ≤ 2 ^ 64) :
    @UexecSG.sbundleAt GF _ uexecSGXv6 (uslot (hlc := hlc)) 16 f (uvisOf V M sts gn cs pid) ⊢
      ∃ Q : Nat → IProp GF,
        filewriteIn (hlc := hlc) (syscFdKey (tfW V.tf (tfArgIdx 0)) sts) (argZ (tfW V.tf (tfArgIdx 2)))
          (writerImg V.upt M) (tfW V.tf (tfArgIdx 1)) Q ∗
        (∀ r : BitVec 64, ⌜filewriteRet (argZ (tfW V.tf (tfArgIdx 2))) r⌝ -∗
          filewriteExtra (hlc := hlc) V.upt (syscFdKey (tfW V.tf (tfArgIdx 0)) sts)
            (argZ (tfW V.tf (tfArgIdx 2))) (writerImg V.upt M) (tfW V.tf (tfArgIdx 1)) Q r -∗
          @UexecSG.spostAt GF _ uexecSGXv6 (uslot (hlc := hlc)) 16 f (uvisOf V M sts gn cs pid) r
            (syscImg V M) sts V.cwi cs) := by
  refine (syscDepWrite_xv6 (hlc := hlc) f (uvisOf V M sts gn cs pid)).trans ?_
  dsimp only [uvisOf, xkA, fdStOfKey, syscFdKey, xpostWrite]
  iintro ⟨H, Hw⟩
  iexists f.wQ
  isplitl [H]
  · iapply (filewriteIn_of_chain (hlc := hlc) _ _ _ _ _ hnw)
    iapply H
    ipureintro
    exact imgAgrees_writerImg V.upt V.sz.toNat M
  · iintro %r %hret Hx
    iapply Hw
    isplitl []
    · ipureintro; exact hret
    iexists V.upt, (writerImg V.upt M)
    iframe Hx
    isplitl []
    · ipureintro; rfl
    · ipureintro; exact imgAgrees_writerImg V.upt V.sz.toNat M

/-- **`SyscDepPipe`** at the instance (UexecExecInst deviation 4: both rows
`emp`). -/
theorem syscDepPipe_holds : SyscDepPipe (hlc := hlc) (GF := GF) := by
  intro f V M sts gn cs pid r M' sts' _ _
  exact sbundleAt_spostAt_pipe_xv6 (hlc := hlc) _ f _ r M' sts' _ cs

/-- **`SyscDepClose`** at the instance (UexecExecInst deviation 4). -/
theorem syscDepClose_holds : SyscDepClose (hlc := hlc) (GF := GF) := by
  intro f V M sts gn cs pid r sts' _
  exact sbundleAt_spostAt_close_xv6 (hlc := hlc) _ f _ r _ sts' _ cs

end Laws

end Xv6
