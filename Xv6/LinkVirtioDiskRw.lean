/-
`virtio_disk_rw`'s interface, assembled from its six phases and closed
with the linked callees.

    P1  Xv6.vdrw_P1   entry        -> +0xbc   prologue, sector, acquire
    P2  Xv6.vdrw_P2   +0xbc        -> +0xc4   alloc3_desc, with its park
    P3  Xv6.vdrw_P3   +0xc4        -> +0x176  the chain, formatted
    P4  Xv6.vdrw_P4   +0x176       -> +0x1a2  ring, publish, notify
    P5  Xv6.vdrw_P5   +0x1a2       -> +0x1d2  the completion wait
    P6  Xv6.vdrw_P6   +0x1d2       -> ret     collect, free_chain, release

A `Proof` file may not import another `Proof` file, so the assembler
lives here rather than beside P6.

What stays open are two assumption bundles: `Xv6.DISK_ACC_ASSUMPTIONS`
(the disk's one unproved accessor, `disk_collect`) and `Xv6.VDRW_OPEN`
(the three facts the landed seams and the frozen accessor do not state;
see `Xv6/VirtioDiskRwDefs4.lean`).
-/
import Xv6.ProofVirtioDiskRwA
import Xv6.ProofVirtioDiskRwB
import Xv6.ProofVirtioDiskRwC
import Xv6.ProofVirtioDiskRwD
import Xv6.ProofVirtioDiskRwE
import Xv6.ProofVirtioDiskRwF
import Xv6.LinkAcquire
import Xv6.LinkRelease
import Xv6.LinkMyproc
import Xv6.LinkSched
import Xv6.LinkSleep
import Xv6.LinkSleepPrepare
import Xv6.LinkFreeDesc

namespace Xv6

open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode Std MachCSL
open LeanRV64D

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

set_option maxHeartbeats 4000000 in
/-- **The six phases, composed.** -/
theorem virtio_disk_rw_proof (HA : DISK_ACC_ASSUMPTIONS) (HO : VDRW_OPEN)
    (SP : SLEEP_PREPARE) (AC : ACQUIRE) (RE : RELEASE) (SL : SLEEP) (FD : FREE_DESC) :
    VIRTIO_DISK_RW :=
  ⟨fun {hlc GF} _ _ _ _ Γ _ cpu k γ γl pd pav pu j bno dsk0 dataBuf dataDisk
      hj hproc hK hsie hnoff hlocks htier hbno hdata hpd hkm => by
    unfold wp_virtio_disk_rw_body
    iintro ⟨Hk, Hpc, #Hpi, Htc, Hcc, Hir, #Hcaps, Hbuf, Hblk, Hnext⟩
    icases kctx_wf _ _ $$ Hk with ⟨%hwf, Hk⟩
    have hintena : k.intena = false := by
      have h := hwf.1 hnoff
      rw [hsie] at h
      exact h.symm
    have hbz : k.regs 10#5 ≠ 0#64 := vdrw5_buf_nz (k.regs 10#5) hkm
    ihave #Hcaps2 := vdrwCaps_of_diskCaps γ γl pd pav pu $$ Hcaps
    -- P1
    iapply (vdrw_P1 AC Γ cpu k γ γl pd pav pu j bno dsk0 dataBuf dataDisk hK hsie hnoff
      hlocks hbno)
    unfold vdrwPostK
    iframe Hk Hpc Hpi Htc Hcc Hir Hcaps2 Hbuf Hblk Hnext
    iintro %R1 HP1
    -- P2
    iapply (vdrw_P2 FD SP AC RE SL Γ cpu k γ γl pd pav pu j bno dsk0 dataBuf dataDisk R1
      hj hproc hK hsie hnoff hlocks htier hintena hpd)
    isplitl [HP1]
    · iexact HP1
    iintro %c1 %a1 %b1 %R2 %hix %mix %tix %yy HP2
    -- P3
    iapply (vdrw_P3 Γ c1 (k.withSpie a1 b1) γ γl pd pav pu bno dsk0 dataBuf dataDisk
      (decide (k.regs 11#5 ≠ 0#64)) hix mix tix yy R2 hpd hbno rfl)
    isplitl [HP2]
    · iexact HP2
    iintro %R3 HP3
    -- P4
    iapply (vdrw_P4 Γ c1 (k.withSpie a1 b1) γ γl pd pav pu bno dataBuf dataDisk
      (decide (k.regs 11#5 ≠ 0#64))
      (vdrwChain ((k.withSpie a1 b1).regs 10#5) bno (decide (k.regs 11#5 ≠ 0#64)) hix mix tix) yy R3
      (vdrwPayw (vdrwChain ((k.withSpie a1 b1).regs 10#5) bno
        (decide (k.regs 11#5 ≠ 0#64)) hix mix tix) dataBuf dataDisk)
      (fun hd => vdrwPayw_write _ dataBuf dataDisk hd)
      (fun hd => by
        rw [vdrwPayw_read _ dataBuf dataDisk hd]
        exact (bytesOf_bvOfBytes BSIZE dataDisk hdata).symm)
      hkm)
    isplitl [HP3]
    · iexact HP3
    iintro %R4 %ep HP4
    -- P5
    iapply (vdrw_P5 SP AC RE SL Γ c1 (k.withSpie a1 b1) γ γl pd pav pu j bno dataBuf
      dataDisk (decide (k.regs 11#5 ≠ 0#64))
      (Chain.arm (vdrwChain ((k.withSpie a1 b1).regs 10#5) bno
          (decide (k.regs 11#5 ≠ 0#64)) hix mix tix) ep
        (vdrwPayw (vdrwChain ((k.withSpie a1 b1).regs 10#5) bno
          (decide (k.regs 11#5 ≠ 0#64)) hix mix tix) dataBuf dataDisk) curCtx)
      yy R4 hj hproc hK hsie hnoff hlocks htier hintena hbz)
    isplitl [HP4]
    · iexact HP4
    iintro %c2 %a2 %b2 %R5 HP5
    -- P6
    iapply (vdrw_P6 HA HO FD RE Γ c2 ((k.withSpie a1 b1).withSpie a2 b2) γ γl pd pav pu bno
      dataBuf dataDisk (decide (k.regs 11#5 ≠ 0#64))
      (Chain.arm (vdrwChain ((k.withSpie a1 b1).regs 10#5) bno
          (decide (k.regs 11#5 ≠ 0#64)) hix mix tix) ep
        (vdrwPayw (vdrwChain ((k.withSpie a1 b1).regs 10#5) bno
          (decide (k.regs 11#5 ≠ 0#64)) hix mix tix) dataBuf dataDisk) curCtx)
      yy R5 hK hsie hnoff hlocks htier hintena hwf hpd rfl hkm)
    iexact HP5⟩

/-- The proved `virtio_disk_rw` interface, given the disk's accessor
assumption and the completion wait's open facts. -/
theorem VirtioDiskRw (HA : DISK_ACC_ASSUMPTIONS) (HO : VDRW_OPEN) : VIRTIO_DISK_RW :=
  virtio_disk_rw_proof HA HO
    (SleepPrepare Myproc Acquire Release) Acquire Release
    (Sleep Myproc Acquire Release Sched) FreeDesc

end Xv6
