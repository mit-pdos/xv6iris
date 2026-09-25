/-
Xv6: the ASSUMED file-system interface.

The file system and user mode are not modelled.  The process code calls a
handful of fs entry points (`fileclose`, `begin_op`/`end_op`, `iput`,
`namei`, `filedup`, `idup`); every one of them may sleep, so its assumed
contract is SLEEP-SHAPED: exactly the premises and post of
`wp_sleep_eb_body` (`Xv6.SpecSleep`) with the entry address abstracted --
the caller runs at depth 0 at either interrupt index, holding no lock, on
its own process; the scheduler invariant and the trap-CSR complement go
in and come back; callee-saved registers are preserved; the
return register is unconstrained (`fileclose(f)` ignores `f`;
`filedup`/`idup`/`namei` return some word).

The whole of `forkret` is assumed too (`Xv6.SpecForkret`): it runs `fsinit`
and `kexec` on the first process and returns to user mode through the
trampoline.

These are class assumptions in the style of `ClaimIs`/`EnvIs`: a proof
that needs them takes `[FsEnv GF]`.

THE BLOCKING ENTRIES ARE ASSUMED AT EITHER ENTRY SIE (`FsEntryEb`, the
shape of `wp_sleep_eb_body`): the caller brings the trap-CSR complement
`trapCsrsExt` / `cpuClaimExt` (emp at `sie = true`, the whole bundle at
`sie = false`) and gets it back at the resuming hart; depth 0 (so, by
`KCtx.wf`, no spinlock held); the crossing is the literal `true`.  This
used to be the `sie = false` shape only (`FsEntry`, now DERIVED:
`FsEntryEb.pinned`).  The change strengthens the assumption, and is
justified by the real functions: `begin_op`, `end_op`, `iput` are now
proved in exactly this eb shape (`SpecBeginOp.wp_begin_op_eb_body`,
`SpecEndOp`, `SpecIput`), and Rocq's `kexit` calls them eb-generic
(`SpecKexit.v`: `cpu_own 0 eb`, `trap_csrs_ext eb` / `cpu_claim_ext eb`).
-/
import Xv6.SpecSleep
import Xv6.SpecFiledup
import Iris.ProofMode

namespace Xv6

open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode Std MachCSL
open LeanRV64D

def filecloseAddr : BitVec 64 := KA.«fileclose»
def fsBeginOpAddr : BitVec 64 := KA.«begin_op»
def fsEndOpAddr : BitVec 64 := KA.«end_op»
def iputAddr : BitVec 64 := KA.«iput»
def nameiAddr : BitVec 64 := KA.«namei»
-- `filedupAddr` is `Xv6/SpecFiledup.lean`'s (D13: the entry address lives with its Spec).
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

/-- **A blocking call at either entry `SIE`** (the shape of
`wp_sleep_eb_body` at entry `entry`): the complement in and out, crossing
`true`, depth 0. -/
def wp_blocking_eb_body {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF] [CurCtx]
    (Γ : SchedNames) [ClaimIs (hlc := hlc) GF Γ]
    (cpu : CPU) (k : KCtx) (j : Nat) (entry : BitVec 64)
    (hj : j < NPROC) (hproc : k.proc = procAddr j) (hK : fsSlots ≤ k.avail)
    (hnoff : k.noff = 0) (htier : k.tier = KTier.kpt) : Prop :=
  kctx cpu k ∗ pcIs cpu entry ∗ procsInv Γ ∗
  trapCsrsExt cpu k.sie ∗ cpuClaimExt cpu k.sie k.proc ∗
  wpNext true k.proc cpu (fun cpu' => iprop(∀ spie : Bool, ∀ spp : Bool, ∀ R' : RegMap,
    kctx cpu' ((k.withSpie spie spp).withRegs R') -∗ pcIs cpu' (jumpPc (k.regs 1#5)) -∗
    trapCsrsExt cpu' k.sie -∗ cpuClaimExt cpu' k.sie k.proc -∗
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

/-- The assumed contract of one fs entry point, at either entry `SIE`. -/
def FsEntryEb (entry : BitVec 64) : Prop :=
  ∀ {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF] [CurCtx]
    (Γ : SchedNames) [ClaimIs (hlc := hlc) GF Γ]
    (cpu : CPU) (k : KCtx) (j : Nat) hj hproc hK hnoff htier,
    wp_blocking_eb_body (hlc := hlc) (GF := GF) Γ cpu k j entry hj hproc hK hnoff htier

/-- The interrupts-off instance (the complement is the whole bundle). -/
theorem FsEntryEb.pinned {entry : BitVec 64} (A : FsEntryEb entry) : FsEntry entry := by
  intro hlc GF _ _ _ Γ _ cpu k j hj hproc hK hsie hnoff hlocks htier
  have h := A (hlc := hlc) (GF := GF) Γ cpu k j hj hproc hK hnoff htier
  unfold wp_blocking_eb_body at h
  unfold wp_blocking_body
  rw [hsie] at h
  simp only [trapCsrsExt_false, cpuClaimExt_false] at h
  iintro ⟨Hk, Hpc, Hpi, Htc, Hcl, Hir, Hnext⟩
  iapply h
  iframe Hk Hpc Hpi Htc Hcl Hir
  iapply wpNext_mono $$ Hnext
  iintro %cpu' HK %spie %spp %R' Hk Hpc ⟨Htc, Hir⟩ Hcl %hcs
  iapply HK $$ %spie %spp %R' Hk Hpc Htc Hcl Hir %hcs

/-- **The file-system boundary** (assumed). -/
class FsEnv : Prop where
  fileclose : FsEntryEb filecloseAddr
  begin_op : FsEntryEb fsBeginOpAddr
  end_op : FsEntryEb fsEndOpAddr
  iput : FsEntryEb iputAddr
  namei : FsEntryEb nameiAddr
  filedup : FsEntryNB filedupAddr
  idup : FsEntryNB idupAddr
  /-- `userinit` calls `namei("/")` on the boot hart, where no process runs
  yet (`Xv6/SpecUserinit.lean`). -/
  nameiBoot : FsEntryNB nameiAddr

end Xv6
