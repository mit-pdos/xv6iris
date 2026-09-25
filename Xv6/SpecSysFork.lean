/-
Specification of `sys_fork` (kernel/sysproc.c; Rocq SpecSysFork.v):

    uint64 sys_fork(void) { return kfork(); }

Nine instructions: the two-slot frame (byte-identical to `sys_getpid`'s),
`jal kfork`, the epilogue.  gcc emits no cast, so `a0` comes back from
`kfork` and leaves untouched.

THE POINT OF THIS SPEC (Rocq's header, in substance) is that it is THIN:
`sys_fork` is a pure forwarder, everything interesting is in
`Xv6/SpecKfork.lean`, and this contract's only job is to show that a
syscall-altitude caller can PAY what `kfork` asks.  Every premise here is
`kfork`'s, verbatim: the running-thread bundle (`procsInv`, trap CSRs,
claim, installed handler -- at the interrupts-off instance), the `wait_lock` / `nextpid` / `kmem` locks, the
allocator and the proc table at their sealed regimes (`kallocAvail`,
`procsAvail`), the file-system boundary `[FsEnv]` and the newborn resume
wand `[ForkretIs]` as instance arguments, and the caller's own private
block, handed back verbatim (`kfork` only READS the parent).

THE RETURN VALUE is kfork's, unchanged: `-1` on either failure arm, or the
child's pid in `[1, PIDMAX]`, sign-extended exactly as kfork left it
(`kforkAns`, restated by name rather than unfolded).

DEVIATION FROM ROCQ, inherited from the Lean `kfork` contract (used as is):
Rocq's `kfork` additionally threads the child's user-execution slot
(`uslot`), the parent's lend `Rc`, the exit payload `Q` / `child_tok`, the
children row `ch_frag`, `fd_frags` and `first_done`/`park_world`; the Lean
`kfork` spec has none of these (the child is parked under `procsInv` via
`[ForkretIs]`), so neither does this wrapper.

`kfork` does not sleep (`filedup`/`idup` are the non-blocking fs entries):
like `kfork`'s, the contract is BALANCED and generic in the entry interrupt
index (`wp_sys_fork_eb_body`: no trap bundle, crossing `k.sie`, the post
`kforkPost` restated at sys_fork's own entry context).  The old
interrupts-off, trap-bundle-threading contract `SYSFORK.wp_sys_fork` is
derived.

Imports only definitional files (never a `Code*` or `Proof*` file).
-/
import Xv6.SpecKfork
import Iris.ProofMode

namespace Xv6

open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode Std MachCSL
open LeanRV64D

/-- Address of `sys_fork`. -/
def sysForkAddr : BitVec 64 := KA.«sys_fork»

/-- sys_fork's 2-slot frame over `kfork`'s cone (Rocq `K_sys_fork`). -/
def sysForkSlots : Nat := 2 + kforkSlots

/-- **WP of `sys_fork()`.** -/
def wp_sys_fork_body {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF] [CurCtx]
    (Γ : SchedNames) [ClaimIs (hlc := hlc) GF Γ] [FsEnv] [ForkretIs]
    (cpu : CPU) (k : KCtx) (γw γp γl : GName) (γk : KmemNames) (j : Nat) (pid : BitVec 32)
    (V : ProcPriv) (M : Nat → List (BitVec 8))
    (hj : j < NPROC) (hproc : k.proc = procAddr j) (hK : sysForkSlots ≤ k.avail)
    (hsie : k.sie = false) (hnoff : k.noff = 0) (hlocks : k.locks = [])
    (htier : k.tier = KTier.kpt) : Prop :=
  kctx cpu k ∗ pcIs cpu sysForkAddr ∗ procsInv Γ ∗
  trapCsrs cpu ∗ cpuClaim cpu k.proc ∗ intrRes cpu ∗
  isLock γw waitLockAddr "wait_lock" waitLockPay ∗
  isLock γp pidLockAddr "nextpid" pidLockPay ∗
  isLock γl kmemLockAddr "kmem" (kmemRes γk) ∗ kallocAvail γk none ∗ procsAvail Γ none ∗
  procPrivNoctxAt curCtx (procAddr j) pid V M ∗
  wpNext true k.proc cpu (fun cpu' => iprop(∀ (spie spp : Bool) (R' : RegMap) (rv : BitVec 32),
    ⌜calleeSaved k.regs R' ∧ R' 10#5 = BitVec.signExtend 64 rv ∧ kforkAns rv⌝ -∗
    kctx cpu' ((k.withSpie spie spp).withRegs R') -∗ pcIs cpu' (jumpPc (k.regs 1#5)) -∗
    trapCsrs cpu' -∗ cpuClaim cpu' k.proc -∗ intrRes cpu' -∗
    procPrivNoctxAt curCtx (procAddr j) pid V M -∗ wpLoop cpu'))
  ⊢ wpLoop (GF := GF) cpu

/-- **WP of `sys_fork()`, at either entry `SIE`** (Rocq `wp_sys_fork_sconf_body`):
kfork's balanced contract forwarded through the two-slot frame. -/
def wp_sys_fork_eb_body {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF] [CurCtx]
    (Γ : SchedNames) [ClaimIs (hlc := hlc) GF Γ] [FsEnv] [ForkretIs]
    (cpu : CPU) (k : KCtx) (γw γp γl : GName) (γk : KmemNames) (j : Nat) (pid : BitVec 32)
    (V : ProcPriv) (M : Nat → List (BitVec 8))
    (hj : j < NPROC) (hproc : k.proc = procAddr j) (hK : sysForkSlots ≤ k.avail)
    (hnoff : k.noff = 0) (htier : k.tier = KTier.kpt) : Prop :=
  kctx cpu k ∗ pcIs cpu sysForkAddr ∗ procsInv Γ ∗
  isLock γw waitLockAddr "wait_lock" waitLockPay ∗
  isLock γp pidLockAddr "nextpid" pidLockPay ∗
  isLock γl kmemLockAddr "kmem" (kmemRes γk) ∗ kallocAvail γk none ∗ procsAvail Γ none ∗
  procPrivNoctxAt curCtx (procAddr j) pid V M ∗
  wpNext k.sie k.proc cpu (kforkPost k j pid V M)
  ⊢ wpLoop (GF := GF) cpu

/-- The interface of `sys_fork`. -/
structure SYSFORK : Prop where
  wp_sys_fork_eb : ∀ {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF] [CurCtx]
    (Γ : SchedNames) [ClaimIs (hlc := hlc) GF Γ] [FsEnv] [ForkretIs]
    (cpu : CPU) (k : KCtx) (γw γp γl : GName) (γk : KmemNames) (j : Nat) (pid : BitVec 32)
    (V : ProcPriv) (M : Nat → List (BitVec 8)) hj hproc hK hnoff htier,
    wp_sys_fork_eb_body (hlc := hlc) (GF := GF) Γ cpu k γw γp γl γk j pid V M
      hj hproc hK hnoff htier

/-- The interrupts-off instance of `wp_sys_fork_eb`: the hart is pinned, so
the trap bundle frames across the call. -/
theorem SYSFORK.wp_sys_fork (A : SYSFORK) {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF]
    [Xv6G GF] [CurCtx] (Γ : SchedNames) [ClaimIs (hlc := hlc) GF Γ] [FsEnv] [ForkretIs]
    (cpu : CPU) (k : KCtx) (γw γp γl : GName) (γk : KmemNames) (j : Nat) (pid : BitVec 32)
    (V : ProcPriv) (M : Nat → List (BitVec 8)) hj hproc hK hsie hnoff hlocks htier :
    wp_sys_fork_body (hlc := hlc) (GF := GF) Γ cpu k γw γp γl γk j pid V M
      hj hproc hK hsie hnoff hlocks htier := by
  have h := A.wp_sys_fork_eb (hlc := hlc) (GF := GF) Γ cpu k γw γp γl γk j pid V M hj hproc hK hnoff htier
  unfold wp_sys_fork_eb_body at h
  unfold wp_sys_fork_body
  iintro ⟨H0, H1, H2, Htc, Hcl, Hir, H6, H7, H8, H9, H10, H11, Hnext⟩
  iapply h
  iframe H0 H1 H2 H6 H7 H8 H9 H10 H11
  rw [hsie]
  iapply wpNext_off_intro
  unfold kforkPost
  iintro %spie %spp %R' %rv %hpost Hk Hpc Hpriv
  ihave Hn := wpNext_at true k.proc cpu cpu _ (fun _ => rfl) $$ Hnext
  iapply Hn $$ %spie %spp %R' %rv %hpost Hk Hpc Htc Hcl Hir Hpriv

end Xv6
