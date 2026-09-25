/-
THE HANDLER ENVIRONMENT (Rocq `SpecKernelvec.kernelvec_env`).

The trap handler closes over more than the proc table: `kernelvec` calls
`kerneltrap`, whose timer path yields (`yield` needs `procsInv`) and whose
device path calls `devintr` (which needs `devintrCaps`: the PLIC's
invariant, the two ports' bundles, the console, the disk and the ticks
lock).  A trap arrives at whatever context the interrupted hart runs, and
both bundles are context-relative (every lock handle carries its creator's
floor, every read-only word its context's bytes), so they travel with the
installed handler (`MachCSL.KCtx.intrResP`) as `MachGS.envP`, the ambient
instance's environment family.  `EnvIs` is the client's choice of that
family, the way `ClaimIs` is its choice of the claim.

Everything in the family is persistent, and its only context dependence is
through lock handles (`MachCSL.isLock`, whose floors transport) and the
read-only `uarts[i]` words (`MachCSL.wordPointsTo`, whose bytes transport)
-- hence `instCtxMorphEnvFam`, the re-homing witness `envMorph` needs.  A
lock handle transports only because its PAYLOAD is a genuine function of
the holder's context (`procLockPay`, `ticksResAt`, `diskRes`, and -- since
this file demanded it -- `consRes`); the instances below say so at the
kernel tier, where a handler always runs.

The family is pinned at that tier (`KTier.kpt`): `procsInv` does not see
the tier at all (`procsInv_toKpt` is `rfl`), but `devintrCaps` does,
through its read-only words, so `devintrCaps_of_envAt'` takes the ambient
tier equation the interrupted bundle supplies (`MachCSL.kctx_tier`).
Imports only definitional files.
-/
import Xv6.SpecDevintr

namespace Xv6

open Iris Iris.ProgramLogic Iris.BI Std MachCSL
open LeanRV64D

section
variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF] [FdslotG GF] [BioslotG GF] [IrefslotG GF]

/-! ## The credentials transport

Each handle's payload is `KTier.kpt`-canonical -- it mentions the ambient
only through `curTier` -- so at the kernel tier it does not depend on the
context the handle is read at, and `MachCSL.instCtxMorphIsLock` applies. -/

/-- Port `i`'s bundle: a ghost invariant, the transmit lock (a ghost
payload), a ghost flag and the read-only base word. -/
instance instCtxMorphUartPort (i : UartId) (γl : GName) (γ : UartNames) :
    CtxMorph (GF := GF) (fun ξ => @uartPort hlc GF _ _ ⟨ξ, KTier.kpt⟩ i γl γ) := by
  unfold uartPort isTxLockAt uartBaseWord
  infer_instance

/-- `uarts[i].rx`, read-only. -/
instance instCtxMorphUartRxWord (i : UartId) :
    CtxMorph (GF := GF) (fun ξ => @uartRxWord hlc GF _ ⟨ξ, KTier.kpt⟩ i) := by
  unfold uartRxWord
  infer_instance

/-- The console lock. -/
instance instCtxMorphIsConsLock (γc : GName) :
    CtxMorph (GF := GF) (fun ξ => @isConsLock hlc GF _ ⟨ξ, KTier.kpt⟩ γc) :=
  show CtxMorph (GF := GF) (fun ξ => @isLock hlc GF _ _ ⟨ξ, KTier.kpt⟩ γc consAddr "cons"
      (fun ζ => @consBody hlc GF _ ⟨ζ, KTier.kpt⟩)) from
    instCtxMorphIsLock _ _ _ _ _

/-- The console's credentials at port 0 (nothing at port 1). -/
instance instCtxMorphUartRxCaps (i : UartId) (γc γl : GName) (γ : UartNames)
    (bs : List (BitVec 8)) :
    CtxMorph (GF := GF) (fun ξ => @uartRxCaps hlc GF _ ⟨ξ, KTier.kpt⟩ _ i γc γl γ bs) := by
  cases i <;> (unfold uartRxCaps; infer_instance)

/-- The ticks lock. -/
instance instCtxMorphIsTickslock (γt : GName) :
    CtxMorph (GF := GF) (fun ξ => @isTickslock hlc GF _ ⟨ξ, KTier.kpt⟩ γt) :=
  show CtxMorph (GF := GF) (fun ξ => @isLock hlc GF _ _ ⟨ξ, KTier.kpt⟩ γt tickslockAddr "time"
      (fun ζ => @ticksResAt hlc GF _ ⟨ζ, KTier.kpt⟩ ζ)) from
    instCtxMorphIsLock _ _ _ _ _

section
variable [DiskG GF]

/-- The `virtio_disk` lock. -/
instance instCtxMorphIsVdiskLock (γd : DiskNames) (γdl : GName) (pd pav pu : BitVec 64) :
    CtxMorph (GF := GF) (fun ξ => @isLock hlc GF _ _ ⟨ξ, KTier.kpt⟩ γdl aVdiskLock
      "virtio_disk" (@diskRes hlc GF _ _ _ ⟨ξ, KTier.kpt⟩ γd pd pav pu)) :=
  show CtxMorph (GF := GF) (fun ξ => @isLock hlc GF _ _ ⟨ξ, KTier.kpt⟩ γdl aVdiskLock
      "virtio_disk" (fun ζ => @diskRes hlc GF _ _ _ ⟨ζ, KTier.kpt⟩ γd pd pav pu ζ)) from
    instCtxMorphIsLock _ _ _ _ _

/-- The queue's frozen geometry: a ghost and three read-only words. -/
instance instCtxMorphDiskGeom (γd : DiskNames) (pd pav pu : BitVec 64) :
    CtxMorph (GF := GF) (fun ξ => @diskGeom hlc GF _ _ ⟨ξ, KTier.kpt⟩ γd pd pav pu) := by
  unfold diskGeom
  infer_instance

/-- The disk's credentials: the invariant, the geometry and the driver lock. -/
instance instCtxMorphDiskCaps (γd : DiskNames) (γdl : GName) (pd pav pu : BitVec 64) :
    CtxMorph (GF := GF) (fun ξ => @diskCaps hlc GF _ _ _ _ _ _ ⟨ξ, KTier.kpt⟩ γd γdl pd pav pu) := by
  unfold diskCaps
  infer_instance

/-- **devintr's credentials transport**: all persistent, and
context-dependent only through lock handles and read-only words. -/
instance instCtxMorphDevintrCaps (Γ : SchedNames) (γ0 γ1 : UartNames) (γc γl0 γl1 : GName)
    (γd : DiskNames) (γdl γt : GName) (pd pav pu : BitVec 64) (bs : List (BitVec 8)) :
    CtxMorph (GF := GF) (fun ξ =>
      @devintrCaps hlc GF _ _ _ _ _ _ ⟨ξ, KTier.kpt⟩ Γ γ0 γ1 γc γl0 γl1 γd γdl γt pd pav pu bs) := by
  unfold devintrCaps
  infer_instance

/-! ## The family and the client's choice -/

/-- **The handler environment family**: the proc table and devintr's
credentials, at the kernel tier. -/
def envFam (Γ : SchedNames) (γ0 γ1 : UartNames) (γc γl0 γl1 : GName) (γd : DiskNames)
    (γdl γt : GName) (pd pav pu : BitVec 64) (bs : List (BitVec 8)) (ξ : CtxId) : IProp GF :=
  iprop(@procsInv hlc GF _ _ ⟨ξ, KTier.kpt⟩ Γ ∗
    @devintrCaps hlc GF _ _ _ _ _ _ ⟨ξ, KTier.kpt⟩ Γ γ0 γ1 γc γl0 γl1 γd γdl γt pd pav pu bs)

instance envFam_persistent (Γ : SchedNames) (γ0 γ1 : UartNames) (γc γl0 γl1 : GName)
    (γd : DiskNames) (γdl γt : GName) (pd pav pu : BitVec 64) (bs : List (BitVec 8)) (ξ : CtxId) :
    Persistent (envFam (hlc := hlc) (GF := GF) Γ γ0 γ1 γc γl0 γl1 γd γdl γt pd pav pu bs ξ) := by
  unfold envFam; infer_instance

instance instCtxMorphEnvFam (Γ : SchedNames) (γ0 γ1 : UartNames) (γc γl0 γl1 : GName)
    (γd : DiskNames) (γdl γt : GName) (pd pav pu : BitVec 64) (bs : List (BitVec 8)) :
    CtxMorph (GF := GF) (envFam (hlc := hlc) (GF := GF) Γ γ0 γ1 γc γl0 γl1 γd γdl γt pd pav pu bs) := by
  unfold envFam; infer_instance

end

/-- **The client's choice, as a class**: the boot instantiates `MachGS`
with `envP := envFam ...` -- the proc table beside devintr's credentials,
at the kernel tier -- and the instance is `rfl`. -/
class EnvIs (GF : BundledGFunctors) [MachGS hlc GF] [Xv6G GF] [FdslotG GF] [BioslotG GF] [IrefslotG GF] [DiskG GF]
    (Γ : SchedNames) (γ0 γ1 : UartNames) (γc γl0 γl1 : GName) (γd : DiskNames) (γdl γt : GName)
    (pd pav pu : BitVec 64) (bs : List (BitVec 8)) : Prop where
  eq : ∀ ξ : CtxId, MachGS.envP (hlc := hlc) (GF := GF) ξ =
    envFam (hlc := hlc) (GF := GF) Γ γ0 γ1 γc γl0 γl1 γd γdl γt pd pav pu bs ξ

end

section

/-- The environment family, spelled out. -/
theorem envP_eq {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF] [FdslotG GF] [BioslotG GF] [IrefslotG GF] [DiskG GF]
    (Γ : SchedNames) (γ0 γ1 : UartNames) (γc γl0 γl1 : GName) (γd : DiskNames) (γdl γt : GName)
    (pd pav pu : BitVec 64) (bs : List (BitVec 8))
    [EnvIs (hlc := hlc) GF Γ γ0 γ1 γc γl0 γl1 γd γdl γt pd pav pu bs] (ξ : CtxId) :
    MachGS.envP (hlc := hlc) (GF := GF) ξ = envFam (hlc := hlc) (GF := GF) Γ γ0 γ1 γc γl0 γl1 γd γdl γt pd pav pu bs ξ := EnvIs.eq ξ

/-- The environment's re-homing witness, discharged: the family transports. -/
theorem envMorph_env {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF] [FdslotG GF] [BioslotG GF] [IrefslotG GF] [DiskG GF]
    (Γ : SchedNames) (γ0 γ1 : UartNames) (γc γl0 γl1 : GName) (γd : DiskNames) (γdl γt : GName)
    (pd pav pu : BitVec 64) (bs : List (BitVec 8))
    [EnvIs (hlc := hlc) GF Γ γ0 γ1 γc γl0 γl1 γd γdl γt pd pav pu bs] :
    ⊢ envMorph (hlc := hlc) (GF := GF) := by
  unfold envMorph
  iintro !> %ξ %ξ' Hdom He
  rw [envP_eq Γ γ0 γ1 γc γl0 γl1 γd γdl γt pd pav pu bs ξ, envP_eq Γ γ0 γ1 γc γl0 γl1 γd γdl γt pd pav pu bs ξ']
  imod CtxMorph.morph (R := envFam (hlc := hlc) (GF := GF) Γ γ0 γ1 γc γl0 γl1 γd γdl γt pd pav pu bs) ξ ξ' $$ [$Hdom $He] with ⟨Hdom, He⟩
  imodintro
  iframe

/-- The family, out of the environment. -/
theorem env_of_envAt {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF] [FdslotG GF] [BioslotG GF] [IrefslotG GF] [DiskG GF]
    (Γ : SchedNames) (γ0 γ1 : UartNames) (γc γl0 γl1 : GName) (γd : DiskNames) (γdl γt : GName)
    (pd pav pu : BitVec 64) (bs : List (BitVec 8))
    [EnvIs (hlc := hlc) GF Γ γ0 γ1 γc γl0 γl1 γd γdl γt pd pav pu bs] (ξ : CtxId) :
    envAt (hlc := hlc) (GF := GF) ξ ⊢ envFam (hlc := hlc) (GF := GF) Γ γ0 γ1 γc γl0 γl1 γd γdl γt pd pav pu bs ξ := by
  rw [← envP_eq Γ γ0 γ1 γc γl0 γl1 γd γdl γt pd pav pu bs ξ]
  exact envAt_env ξ

/-- ...and back: the family IS the environment (with its witness). -/
theorem envAt_of_env {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF] [FdslotG GF] [BioslotG GF] [IrefslotG GF] [DiskG GF]
    (Γ : SchedNames) (γ0 γ1 : UartNames) (γc γl0 γl1 : GName) (γd : DiskNames) (γdl γt : GName)
    (pd pav pu : BitVec 64) (bs : List (BitVec 8))
    [EnvIs (hlc := hlc) GF Γ γ0 γ1 γc γl0 γl1 γd γdl γt pd pav pu bs] (ξ : CtxId) :
    envFam (hlc := hlc) (GF := GF) Γ γ0 γ1 γc γl0 γl1 γd γdl γt pd pav pu bs ξ ⊢ envAt (hlc := hlc) (GF := GF) ξ := by
  iintro #H
  iapply envAt_intro ξ
  isplitl []
  · rw [envP_eq Γ γ0 γ1 γc γl0 γl1 γd γdl γt pd pav pu bs ξ]; iexact H
  · iapply envMorph_env Γ γ0 γ1 γc γl0 γl1 γd γdl γt pd pav pu bs

/-- The table, out of the environment. -/
theorem procsInv_of_envAt {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF] [FdslotG GF] [BioslotG GF] [IrefslotG GF] [DiskG GF]
    (Γ : SchedNames) (γ0 γ1 : UartNames) (γc γl0 γl1 : GName) (γd : DiskNames) (γdl γt : GName)
    (pd pav pu : BitVec 64) (bs : List (BitVec 8))
    [EnvIs (hlc := hlc) GF Γ γ0 γ1 γc γl0 γl1 γd γdl γt pd pav pu bs] (ξ : CtxId) :
    envAt (hlc := hlc) (GF := GF) ξ ⊢ @procsInv hlc GF _ _ ⟨ξ, KTier.kpt⟩ Γ := by
  refine (env_of_envAt Γ γ0 γ1 γc γl0 γl1 γd γdl γt pd pav pu bs ξ).trans ?_
  unfold envFam
  iintro ⟨H, _⟩
  iexact H

/-- devintr's credentials, out of the environment. -/
theorem devintrCaps_of_envAt {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF] [FdslotG GF] [BioslotG GF] [IrefslotG GF] [DiskG GF]
    (Γ : SchedNames) (γ0 γ1 : UartNames) (γc γl0 γl1 : GName) (γd : DiskNames) (γdl γt : GName)
    (pd pav pu : BitVec 64) (bs : List (BitVec 8))
    [EnvIs (hlc := hlc) GF Γ γ0 γ1 γc γl0 γl1 γd γdl γt pd pav pu bs] (ξ : CtxId) :
    envAt (hlc := hlc) (GF := GF) ξ ⊢
      @devintrCaps hlc GF _ _ _ _ _ _ ⟨ξ, KTier.kpt⟩ Γ γ0 γ1 γc γl0 γl1 γd γdl γt pd pav pu bs := by
  refine (env_of_envAt Γ γ0 γ1 γc γl0 γl1 γd γdl γt pd pav pu bs ξ).trans ?_
  unfold envFam
  iintro ⟨_, H⟩
  iexact H

/-- The table at the AMBIENT context, out of the environment: `procsInv`
does not see the tier. -/
theorem procsInv_of_envAt' {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF] [FdslotG GF] [BioslotG GF] [IrefslotG GF] [DiskG GF]
    (Γ : SchedNames) (γ0 γ1 : UartNames) (γc γl0 γl1 : GName) (γd : DiskNames) (γdl γt : GName)
    (pd pav pu : BitVec 64) (bs : List (BitVec 8))
    [EnvIs (hlc := hlc) GF Γ γ0 γ1 γc γl0 γl1 γd γdl γt pd pav pu bs] [X : CurCtx] :
    envAt (hlc := hlc) (GF := GF) curCtx ⊢ procsInv Γ := by
  rw [procsInv_toKpt X Γ]
  exact procsInv_of_envAt Γ γ0 γ1 γc γl0 γl1 γd γdl γt pd pav pu bs curCtx

/-- The credentials at the AMBIENT context: the family is pinned at the
kernel tier, which is the ambient one in a trap handler
(`MachCSL.kctx_tier` on the interrupted bundle). -/
theorem devintrCaps_of_envAt' {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF] [FdslotG GF] [BioslotG GF] [IrefslotG GF] [DiskG GF]
    (Γ : SchedNames) (γ0 γ1 : UartNames) (γc γl0 γl1 : GName) (γd : DiskNames) (γdl γt : GName)
    (pd pav pu : BitVec 64) (bs : List (BitVec 8))
    [EnvIs (hlc := hlc) GF Γ γ0 γ1 γc γl0 γl1 γd γdl γt pd pav pu bs] [X : CurCtx] (hT : curTier = KTier.kpt) :
    envAt (hlc := hlc) (GF := GF) curCtx ⊢ devintrCaps (GF := GF) Γ γ0 γ1 γc γl0 γl1 γd γdl γt pd pav pu bs := by
  have h : devintrCaps (GF := GF) Γ γ0 γ1 γc γl0 γl1 γd γdl γt pd pav pu bs =
      @devintrCaps hlc GF _ _ _ _ _ _ ⟨X.curCtx, KTier.kpt⟩ Γ γ0 γ1 γc γl0 γl1 γd γdl γt pd pav pu bs := by
    rw [← hT]
  rw [h]
  exact devintrCaps_of_envAt Γ γ0 γ1 γc γl0 γl1 γd γdl γt pd pav pu bs X.curCtx

/-- ...and the environment, from the two at the ambient context. -/
theorem envAt_of_caps' {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF] [FdslotG GF] [BioslotG GF] [IrefslotG GF] [DiskG GF]
    (Γ : SchedNames) (γ0 γ1 : UartNames) (γc γl0 γl1 : GName) (γd : DiskNames) (γdl γt : GName)
    (pd pav pu : BitVec 64) (bs : List (BitVec 8))
    [EnvIs (hlc := hlc) GF Γ γ0 γ1 γc γl0 γl1 γd γdl γt pd pav pu bs] [X : CurCtx] (hT : curTier = KTier.kpt) :
    procsInv (GF := GF) Γ ∗ devintrCaps Γ γ0 γ1 γc γl0 γl1 γd γdl γt pd pav pu bs ⊢ envAt (hlc := hlc) (GF := GF) curCtx := by
  have h : devintrCaps (GF := GF) Γ γ0 γ1 γc γl0 γl1 γd γdl γt pd pav pu bs =
      @devintrCaps hlc GF _ _ _ _ _ _ ⟨X.curCtx, KTier.kpt⟩ Γ γ0 γ1 γc γl0 γl1 γd γdl γt pd pav pu bs := by
    rw [← hT]
  rw [procsInv_toKpt X Γ, h]
  have H := envAt_of_env (hlc := hlc) (GF := GF) Γ γ0 γ1 γc γl0 γl1 γd γdl γt pd pav pu bs X.curCtx
  unfold envFam at H
  exact H

end

end Xv6
