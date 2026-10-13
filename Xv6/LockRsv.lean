/-
Which xv6 locks are RESERVED (W8-β′): the `MachCSL.lkRsvIn` facts the lock
births, `initlock` and the destroying release need, read off the era's static
list (`kctx_rsvEq`) and `Xv6.KernelRsv`'s decidable checks: the image's static
spinlocks are registered (`rsvLockAt`); every other lock (a pipe lock, in a
kalloc page) is dynamic.
-/
import Xv6.Image
import MachCSL.Lock
import Xv6.SpecInitlock

namespace Xv6

open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode Std MachCSL

variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF]

/-- A lock at or above the linker's `end` (every kalloc page) is DYNAMIC: no
registered lock region lies there (`xv6RsvStatic_lockLow`). -/
theorem lkRsvIn_high [KernelGeom] {lk : BitVec 64}
    (heq : MachFixedGS.rsvStatic (hlc := hlc) (GF := GF) = KernelRsv.static)
    (hhi : ¬ lk.ult KA.«end») : ¬ lkRsvIn (hlc := hlc) (GF := GF) lk := by
  intro hm
  unfold lkRsvIn at hm
  rw [heq] at hm
  exact hhi (xv6RsvStatic_lockLow hm)

theorem kctx_lkHigh [CurCtx] [KernelGeom] {lent : Bool} (cpu : CPU) (k : KCtx) {lk : BitVec 64}
    (hhi : ¬ lk.ult KA.«end») :
    kctxL (GF := GF) lent cpu k ⊢ ⌜¬ lkRsvIn (hlc := hlc) (GF := GF) lk⌝ ∗ kctxL lent cpu k := by
  iintro H
  icases kctx_rsvEq cpu k $$ H with ⟨%heq, H⟩
  iframe H
  ipureintro; exact lkRsvIn_high heq hhi

/-- A registered static lock (by the era's list). -/
theorem lkRsvIn_of {lk : BitVec 64} (heq : MachFixedGS.rsvStatic (hlc := hlc) (GF := GF) = KernelRsv.static)
    (h : xv6LockR lk ∈ xv6RsvStatic) : lkRsvIn (hlc := hlc) (GF := GF) lk := by
  unfold lkRsvIn; rw [heq]; exact h

theorem lkRsvIn_pid (heq : MachFixedGS.rsvStatic (hlc := hlc) (GF := GF) = KernelRsv.static) :
    lkRsvIn (hlc := hlc) (GF := GF) KA.«pid_lock» := lkRsvIn_of heq xv6RsvStatic_pid

theorem lkRsvIn_wait (heq : MachFixedGS.rsvStatic (hlc := hlc) (GF := GF) = KernelRsv.static) :
    lkRsvIn (hlc := hlc) (GF := GF) KA.«wait_lock» := lkRsvIn_of heq xv6RsvStatic_wait

theorem lkRsvIn_proc (heq : MachFixedGS.rsvStatic (hlc := hlc) (GF := GF) = KernelRsv.static)
    (i : Nat) (hi : i < 64) : lkRsvIn (hlc := hlc) (GF := GF) (rsvProcLk i) :=
  lkRsvIn_of heq (xv6RsvStatic_proc i hi)

/-- Every registered lock is `rsvLockAt`. -/
theorem lkRsvIn_range {lk : BitVec 64} (heq : MachFixedGS.rsvStatic (hlc := hlc) (GF := GF) = KernelRsv.static)
    (h : lkRsvIn (hlc := hlc) (GF := GF) lk) : rsvLockAt lk := by
  unfold lkRsvIn at h
  rw [heq] at h
  exact h

/-- A lock outside `rsvLockAt` is DYNAMIC. -/
theorem kctx_lkOut [CurCtx] {lent : Bool} (cpu : CPU) (k : KCtx) (lk : BitVec 64) (hout : ¬ rsvLockAt lk) :
    kctxL (GF := GF) lent cpu k ⊢ ⌜¬ lkRsvIn (hlc := hlc) (GF := GF) lk⌝ ∗ kctxL lent cpu k := by
  iintro H
  icases kctx_rsvEq cpu k $$ H with ⟨%heq, H⟩
  iframe H
  ipureintro
  exact fun hm => hout (lkRsvIn_range heq hm)

/-- A registered static lock needs no name word at its birth (W8 (f2-ctx):
its byte is a static hop byte), out of the context's copy of the list. -/
theorem kctx_lkNameFor [CurCtx] {lent : Bool} (cpu : CPU) (k : KCtx) {lk : BitVec 64}
    (h : xv6LockR lk ∈ xv6RsvStatic) :
    kctxL (GF := GF) lent cpu k ⊢ lkNameFor (hlc := hlc) (GF := GF) lk ∗ kctxL lent cpu k := by
  iintro H
  icases kctx_rsvEq cpu k $$ H with ⟨%heq, H⟩
  iframe H
  iapply lkNameFor_rsv lk (lkRsvIn_of heq h)

/-- `initlock` at OWNED raw words, at a lock outside `rsvLockAt`
(`kctx_lkOut`: a dynamic lock). -/
theorem wp_initlock_own (IL : INITLOCK) [CurCtx] (cpu : CPU) (k : KCtx) (vlock : BitVec 32)
    (vname vcpu : BitVec 64) (hK : 2 ≤ k.avail) (hout : ¬ rsvLockAt (k.regs 10#5)) :
    wp_initlock_own_body (hlc := hlc) (GF := GF) cpu k vlock vname vcpu hK := by
  have h := IL.wp_initlock (hlc := hlc) (GF := GF) cpu k vlock vname vcpu hK
  unfold wp_initlock_body at h
  unfold wp_initlock_own_body
  iintro ⟨Hk, Hpc, #Hcl, #Hcl', Hw, Hn, Hc, HΦ⟩
  icases kctx_lkOut cpu k (k.regs 10#5) hout $$ Hk with ⟨%hm, Hk⟩
  iapply h
  iframe Hk Hpc Hcl Hcl' Hn HΦ
  iapply lkRaw_intro _ vlock vcpu hm
  iframe Hw Hc

end Xv6
