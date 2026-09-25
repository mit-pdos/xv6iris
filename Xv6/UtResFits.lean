/-
**The residue at the syscall environment, and the park's channel** (Rocq
`UtResFits.v`).

Rocq's file is a functor `UtResFits (SY : SYSCALL) <: USERTRAP_RES_PARK`: it
instantiates `UsertrapRes`'s definitions at the abstract `SY.syscall_env`,
checks them against `SpecUsertrap.USERTRAP_RES` (the module type's binder list
verbatim, so a missing class is caught here rather than at ProofUsertrap's
seal), and proves the park's one producer entry `usertrap_res_bare_park`
(`ut_park_intro_body` at `usertrap_res_bare` and `ParkCap.park_token`),
discharging `ut_res_bare_park`'s environment derivation with
`SY.syscall_env_park`.

In Lean the syscall environment is CONCRETE (D30, `SyscallEnv.syscallEnv PT
Γ γ`), so there is no functor and no module type to fit: this file DEFINES
the residue the trap loop threads (`usertrapRes PT`, Rocq
`usertrap_res_bare`; `usertrapResRun PT`, Rocq `usertrap_res`), restates the
accessors at it, and proves the park entry (`usertrapRes_park`) at the park
token `PT Γ` (SyscallEnv's header: ParkCap supplies `PT := parkToken`,
W8-P2).  SpecUsertrap (the boundary) is stated over `usertrapRes`, which is
the fit check.

## Deviations from Rocq

1. **No module types** (D30): `USERTRAP_RES_PARK` / `USERTRAP_PARK` are not
   stated; ParkCap consumes `usertrapRes_park` (an ordinary theorem) and the
   boundary is SpecUsertrap's `USERTRAP` structure over `usertrapRes`.
2. **The park token is the parameter `PT`** (SyscallEnv's header); the
   `W` of `utParkIntroBody` is `PT N.Γ`.
3. **The resumer's syscall-side rows are `utSysParkRows`** (Rocq's
   `park_globals` rows beyond `ut_caps`' -- console, ticks, nextpid -- and
   the park world, which Rocq rebuilds out of the parker's `park_world` and
   the resumer's globals): the resumer supplies both at its context
   (UsertrapRes deviation 8), so no parker-side world is needed.
4. The accessors Rocq restates for the module type (`_tlb_*`, `_pt(m)_*`,
   `_tf_open`, `_csrs_open`, `_tf_csrs_open`, `_sstc`, `_norm`) have no
   Lean counterpart (UsertrapRes deviations 1, 6, 9); `_fsabs` is
   `usertrapRes_firstDone` (FirstTok deviation 1: no application layer, so
   the loop reads the file system's `firstDone` instead).

Imports only definitional files.
-/
import Xv6.UsertrapRes
import Xv6.SyscallEnv

namespace Xv6

open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode Std MachCSL
open LeanRV64D

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

section
variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF] [FdslotG GF] [BioslotG GF]
    [BcacheG GF] [SleepLockG GF] [DiskG GF] [IcacheG GF] [LogG GF] [FsBlocksG GF] [IregG GF]
    [FsTopG GF] [FsLinkG GF] [IcboxG GF] [OffboxG GF] [OffboxBoxG GF] [IrefslotG GF] [CtokG GF] [WchG GF]
    [Appcfg GF] [FileG GF] [Fscfg] [Icfg]

/-! ## §1 The residue at `syscallEnv` -/

section Res
variable [X : CurCtx] (PT : SchedNames → IProp GF)

/-- The residue's syscall environment (Rocq `SY.syscall_env (un_f N)
(un_pj N) (un_fn N pid)`): D30's `syscallEnv` at the record's proc table and
file table. -/
def utSysEnv : UtNames → BitVec 32 → IProp GF := fun N _ => syscallEnv (hlc := hlc) PT N.Γ N.f

/-- **Rocq `usertrap_res_bare`** (= `UtResFits.usertrap_res_bare`): the
residue the trap loop parks across user execution. -/
def usertrapRes (cpu : CPU) (P : UPtd) (ksp : BitVec 64) (V : ProcPriv) (sts : List FdState)
    (cs : ExtTreeSet GName compare) (pid : BitVec 32) : IProp GF :=
  utResBare cpu (utSysEnv (hlc := hlc) PT) P ksp V sts cs pid

/-- **Rocq `usertrap_res`**: the running form (usertrap's body). -/
def usertrapResRun (cpu : CPU) (P : UPtd) (ksp : BitVec 64) (V : ProcPriv)
    (M : Nat → List (BitVec 8)) (sts : List FdState) (cs : ExtTreeSet GName compare)
    (pid : BitVec 32) : IProp GF :=
  utResRun cpu (utSysEnv (hlc := hlc) PT) P ksp V M sts cs pid

variable (cpu : CPU) (P : UPtd) (ksp : BitVec 64) (V : ProcPriv) (sts : List FdState)
  (cs : ExtTreeSet GName compare) (pid : BitVec 32)

/-- **Rocq `usertrap_res_tlb_close` / `_ptm_close`** (UsertrapRes
`utResBare_join`). -/
theorem usertrapRes_join (h : curTier = KTier.kpt) (M : Nat → List (BitVec 8)) :
    usertrapRes (GF := GF) PT cpu P ksp V sts cs pid ∗ procPtAt P M ∗ tfPageAt P.tfp V.tf ⊢
      usertrapResRun PT cpu P ksp V M sts cs pid :=
  utResBare_join h cpu _ P ksp V M sts cs pid

/-- **Rocq `usertrap_res_tlb_open` / `_ptm_open`** (UsertrapRes
`utResBare_split`). -/
theorem usertrapRes_split (h : curTier = KTier.kpt) (M : Nat → List (BitVec 8)) :
    usertrapResRun (GF := GF) PT cpu P ksp V M sts cs pid ⊢
      usertrapRes PT cpu P ksp V sts cs pid ∗ procPtAt P M ∗ tfPageAt P.tfp V.tf :=
  utResBare_split h cpu _ P ksp V M sts cs pid

/-- The kernel words (uservec's `hkw`, with `utTfk_uservec`). -/
theorem usertrapRes_tfk :
    usertrapRes (GF := GF) PT cpu P ksp V sts cs pid ⊢
      utTfk cpu ksp V ∗ usertrapRes PT cpu P ksp V sts cs pid :=
  utResBare_tfk cpu _ P ksp V sts cs pid

/-- The re-key at uservec's saved frame. -/
theorem usertrapRes_uservec (g : RegMap) :
    usertrapRes (GF := GF) PT cpu P ksp V sts cs pid ⊢
      usertrapRes PT cpu P ksp { V with tf := uservecTf V.tf g } sts cs pid :=
  utResBare_retf cpu _ P ksp V _ sts cs pid (uservecTf_low V.tf g)

/-- **Rocq `usertrap_res_bare_sz`**. -/
theorem usertrapRes_sz :
    usertrapRes (GF := GF) PT cpu P ksp V sts cs pid ⊢
      usertrapRes PT cpu P ksp V sts cs pid ∗ ⌜V.sz.toNat ≤ uvmMaxsz⌝ :=
  utResBare_sz cpu _ P ksp V sts cs pid

/-- **Rocq `usertrap_res_bare_lazy`**. -/
theorem usertrapRes_lazy :
    usertrapRes (GF := GF) PT cpu P ksp V sts cs pid ⊢
      usertrapRes PT cpu P ksp V sts cs pid ∗ ⌜V.pvLazy = false → lazyFree P.um V.sz⌝ :=
  utResBare_lazy cpu _ P ksp V sts cs pid

/-- **Rocq `usertrap_res_bare_fd_open`**. -/
theorem usertrapRes_fd_open :
    usertrapRes (GF := GF) PT cpu P ksp V sts cs pid ⊢
      fdFrags V.fdg sts ∗
      (∀ sts' : List FdState, fdFrags V.fdg sts' -∗ usertrapRes PT cpu P ksp V sts' cs pid) :=
  utResBare_fd_open cpu _ P ksp V sts cs pid

/-- **Rocq `usertrap_res_bare_fsabs`** (deviation 4): the file system's
steady token, off the syscall environment. -/
theorem usertrapRes_firstDone [∀ Γ, Persistent (PT Γ)] :
    usertrapRes (GF := GF) PT cpu P ksp V sts cs pid ⊢
      firstDone (hlc := hlc) ∗ usertrapRes PT cpu P ksp V sts cs pid :=
  utResBare_env _ cpu _ P ksp V sts cs pid (fun N _ => by
    unfold utSysEnv
    iintro #H
    ihave #F := syscallEnv_first PT N.Γ N.f $$ H
    iframe F H)

end Res

/-! ## §2 The park's channel (Rocq `usertrap_res_bare_park`) -/

/-- The resumer's syscall-side rows (deviation 3): `syscParkExtra` at some
ticks lock and the park world, at its context. -/
def utSysParkRows [Xc : CurCtx] (Γ : SchedNames) : IProp GF :=
  iprop(∃ γtk : GName, syscParkExtra Γ γtk ∗ parkWorld Γ)

/-- **Rocq `UtResFits.usertrap_res_bare_park`**: the park's producer entry at
the concrete residue and the park token -- `utResBare_park` with the
environment derived by `syscallEnv_park` at the resumer's context. -/
theorem usertrapRes_park (PT : SchedNames → IProp GF) (N : UtNames) :
    utParkIntroBody (GF := GF) (fun h Xc => usertrapRes (X := Xc) PT h) (PT N.Γ)
      (fun Xc => utSysParkRows (Xc := Xc) N.Γ) N := by
  refine utResBare_park (fun Xc => utSysEnv (X := Xc) PT) (PT N.Γ)
    (fun Xc => utSysParkRows (Xc := Xc) N.Γ) N (fun Xc => ?_)
  unfold utParkDerive parkGlobals utSysParkRows utSysEnv
  iintro ⟨-, #Hpe, #Hwl, #Hft, -⟩ ⟨%γtk, Hx, Hw⟩ Hdone Ht
  iapply syscallEnv_park PT N.Γ N.f N.w N.ft γtk $$ Hx Hwl Hft Hpe Hdone Hw Ht

end

end Xv6
