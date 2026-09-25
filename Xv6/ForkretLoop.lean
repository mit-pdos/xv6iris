/-
**What forkret's `jalr` hands the closed trap loop** (Rocq
`SpecUserretClosed.wp_userret_closed_body`, at forkret's entry into it).

forkret does not return: its `c.jalr a5` at +0x7e enters userret at
`TRAMPOLINE + 0x9c` with `a0 = MAKE_SATP(p->pagetable)`, and from there the
machine runs the CLOSED trap loop -- userret, user code, uservec, usertrap,
userret, ... (Rocq `ProofUserretClosed`, the Löb).  Rocq's forkret is a
functor over `USERRET_CLOSED`; this is the Lean statement of the one
`USERRET_CLOSED` entry forkret uses, stated at forkret's jump:

* the kernel context at prepare_return's post shape (interrupts off,
  `SPIE = 1`, `SPP = U`, the kernel table), `a0` the user `satp`, the pc at
  userret;
* forkret's own 6-slot frame, never popped (Rocq SpecForkret "the frame
  merged back in"): `m` dead stack cells above `k.sp`, which the loop merges
  back into the whole-page stack (`UsertrapRes.userretLeft_pop` /
  `_top`, the uservec obligation);
* the trampoline claim, the four trap CSR cells (`sepc` at the resume pc),
  the address space and trapframe page;
* THE SLOT (`UexecRet.uslot`) at the record the loop resumes, and THE
  RESIDUE (`UtResFits.usertrapResAt`) at the park token.

## Deviations from Rocq

1. **This is an interface, not a proof** (W8-P2): the closed loop is W8-L's
   (`SpecUserretClosed` / `ProofUserretClosed` / `LinkUserretClosed`, not
   landed).  `FORKRET_LOOP` is the one statement forkret needs of it, in
   Lean's kernel-context form (SpecUserret deviation 1); W8-L's link is to
   provide it (a restatement of Rocq's `wp_userret_closed` at forkret's
   entry: the frame cells re-formed, the slot read at the natural state
   `uslot_ukc`).  It is a PARAMETER of `ProofForkret.forkret_proof`, as
   Rocq's `UC : USERRET_CLOSED` is of `ForkretProof`.
2. At the kernel's deposit instance (`uexecSGXv6`) and the park token
   (`ParkCap.parkToken`), where the usertrap seal is.
3. Rocq's `loop_ok` / `usertrap_ret_ms` / `satp_rooted` / `upt_map_wf`
   premises are the context's indices (`sie`/`spie`/`spp`, `ha0`) and the
   block's own facts (the residue carries the block).

Imports only definitional files and Spec files.
-/
import Xv6.SpecUserret
import Xv6.ParkCap
import Xv6.UexecExecInst

namespace Xv6

open Iris Iris.ProgramLogic Iris.BI Std MachCSL
open LeanRV64D

set_option linter.unusedVariables false

/-- **The closed loop, entered at forkret's jump** (deviation 1). -/
def wp_forkret_loop_body {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF] [FdslotG GF]
    [BioslotG GF] [BcacheG GF] [SleepLockG GF] [DiskG GF] [IcacheG GF] [LogG GF] [FsBlocksG GF]
    [IregG GF] [FsTopG GF] [FsLinkG GF] [IcboxG GF] [OffboxG GF] [OffboxBoxG GF] [IrefslotG GF]
    [CtokG GF] [WchG GF] [Appcfg GF] [FileG GF] [Fscfg] [Icfg] [CurCtx]
    (Γ : SchedNames) [ClaimIs (hlc := hlc) GF Γ]
    (cpu : CPU) (k : KCtx) (j : Nat) (V : ProcPriv) (M : Nat → List (BitVec 8)) (sts : List FdState)
    (gn : GName) (cs : ExtTreeSet GName compare) (pid : BitVec 32) (m : Nat)
    (hj : j < NPROC) (hproc : k.proc = procAddr j) (hsie : k.sie = false) (hspie : k.spie = true)
    (hspp : k.spp = false) (htier : k.tier = KTier.kpt) (hnoff : k.noff = 0)
    (ha0 : k.regs 10#5 = satpOf KTier.kpt V.upt.root)
    (hsp : k.sp + 8#64 * BitVec.ofNat 64 m = V.kstack + 4096#64) (hav : k.avail + m = 512)
    (hgn : gn = V.gen) : Prop :=
  kctx cpu k ∗ pcIs cpu userretVa ∗ syscTrampCl ∗
  Register.sepc ↦ᵣ[cpu] tfResumePc V.tf ∗
  (∃ v : BitVec 64, Register.scause ↦ᵣ[cpu] v) ∗ (∃ v : BitVec 64, Register.stval ↦ᵣ[cpu] v) ∗
  Register.stvec ↦ᵣ[cpu] uservecTvec ∗
  ([∗list] i ∈ List.range m, ∃ w : BitVec 64, wordPointsTo (k.sp + 8#64 * BitVec.ofNat 64 i) 8 (DFrac.own 1) w) ∗
  procPtAt V.upt M ∗ tfPageAt V.upt.tfp V.tf ∗
  uslot (hlc := hlc) (SG := uexecSGXv6) (uvisOf V M sts gn cs pid) ∗
  usertrapResAt (hlc := hlc) (parkToken (hlc := hlc) (SG := uexecSGXv6)) Γ j cpu V.upt (V.kstack + 4096#64) V
    sts cs pid
  ⊢ wpLoop (GF := GF) cpu

/-- **What `ProofForkret` needs of the closed loop** (deviation 1; W8-L). -/
structure FORKRET_LOOP : Prop where
  wp_forkret_loop : ∀ {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF] [FdslotG GF]
    [BioslotG GF] [BcacheG GF] [SleepLockG GF] [DiskG GF] [IcacheG GF] [LogG GF] [FsBlocksG GF]
    [IregG GF] [FsTopG GF] [FsLinkG GF] [IcboxG GF] [OffboxG GF] [OffboxBoxG GF] [IrefslotG GF]
    [CtokG GF] [WchG GF] [Appcfg GF] [FileG GF] [Fscfg] [Icfg] [CurCtx]
    (Γ : SchedNames) [ClaimIs (hlc := hlc) GF Γ]
    (cpu : CPU) (k : KCtx) (j : Nat) (V : ProcPriv) (M : Nat → List (BitVec 8)) (sts : List FdState)
    (gn : GName) (cs : ExtTreeSet GName compare) (pid : BitVec 32) (m : Nat)
    hj hproc hsie hspie hspp htier hnoff ha0 hsp hav hgn,
    wp_forkret_loop_body (hlc := hlc) (GF := GF) Γ cpu k j V M sts gn cs pid m
      hj hproc hsie hspie hspp htier hnoff ha0 hsp hav hgn

end Xv6
