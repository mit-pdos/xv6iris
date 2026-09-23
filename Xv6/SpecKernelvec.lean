/-
Specification of `kernelvec` (kernel/kernelvec.S), xv6's supervisor trap
vector.  Nothing calls it: the hardware traps to it.  Its contract is
therefore not a function spec but the trap engine's handler contract
`ihs ⟨cpu, kernelvec⟩` (`MachCSL.KCtx`): from the context a supervisor
interrupt leaves, the handler runs and resumes the interrupted context at
the trapped pc, on whichever hart the thread lands on.

The handler's ENVIRONMENT -- the proc table, which `kerneltrap`'s timer
path needs to call `yield`, and devintr's credentials, which its device
path needs -- is not a premise: the trap engine threads it.  `MachGS.envP` is the ambient instance's environment family, the
installed handler carries it at the context the interrupted bundle runs
(`MachCSL.KCtx.intrResP`), and `ihsF` hands it to the handler there
(`MachCSL.CtxLaws.envAt`, with the witness that re-homes it across a
domination -- the Rocq `IntrDefs.env_move`).  `EnvIs` (`Xv6.HandlerEnv`)
is the client's choice of the family, as `ClaimIs` is its choice of the
claim.
Imports only definitional files.
-/
import Xv6.HandlerEnv
import MachCSL.WpSmodeIntr

namespace Xv6

open Iris Iris.ProgramLogic Iris.BI Std MachCSL
open LeanRV64D

/-- Address of `kernelvec`. -/
def kernelvecAddr : BitVec 64 := KA.«kernelvec»

/-- `stvec := kernelvec` is a direct-mode vector. -/
theorem kernelvecAddr_direct : stvecDirect kernelvecAddr := by
  unfold stvecDirect kernelvecAddr; decide

/-- The interface of `kernelvec`: the handler contract, at every hart.

It is stated under the handler's ENVIRONMENT, which the trap engine
threads for us: `MachGS.envP` is the ambient instance's environment
family, the installed handler (`MachCSL.KCtx.intrResP`) carries it at the
context the interrupted bundle runs, and `ihsF` hands it to the handler at
that context together with the witness that re-homes it
(`MachCSL.CtxLaws.envAt`, the Rocq `IntrDefs.env_move`).  `[EnvIs GF Γ ..]`
is the client's choice of that family -- the proc table's `procsInv`
beside `devintrCaps` -- which is what `kernelvec` needs: it calls
`kerneltrap`, whose timer path yields (and `yield` needs the table) and
whose device path calls `devintr`.  Nothing else about the interrupted
context is assumed -- `ihsF` quantifies it freely, and the running slot is
named by THE CLAIM the trap hands over (`Xv6.cpuClaim_proc_shape`). -/
structure KERNELVEC : Prop where
  handler : ∀ {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF] [DiskG GF]
    (Γ : SchedNames) (γ0 γ1 : UartNames) (γc γl0 γl1 : GName) (γd : DiskNames) (γdl γt : GName)
    (pd pav pu : BitVec 64) (bs : List (BitVec 8))
    [ClaimIs (hlc := hlc) GF Γ]
    [EnvIs (hlc := hlc) GF Γ γ0 γ1 γc γl0 γl1 γd γdl γt pd pav pu bs] (cpu : CPU),
    ⊢ ihs (GF := GF) ⟨cpu, kernelvecAddr⟩

/-- **The contract is usable at boot**: a hart holding the vector cell, the
proc table and devintr's credentials -- both at ITS OWN context, which is
all a boot hart ever has, and at the kernel tier (`hT`) -- installs the
handler.  (This is what `procsInvAll`, the family over ALL contexts the
contract used to demand, made impossible.) -/
theorem intrRes_of_kernelvec {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF]
    [DiskG GF] [CurCtx] (KV : KERNELVEC) (Γ : SchedNames) (γ0 γ1 : UartNames)
    (γc γl0 γl1 : GName) (γd : DiskNames) (γdl γt : GName) (pd pav pu : BitVec 64)
    (bs : List (BitVec 8)) [ClaimIs (hlc := hlc) GF Γ]
    [EnvIs (hlc := hlc) GF Γ γ0 γ1 γc γl0 γl1 γd γdl γt pd pav pu bs]
    (hT : curTier = KTier.kpt) (cpu : CPU) :
    Register.stvec ↦ᵣ[cpu] kernelvecAddr ∗ procsInv Γ ∗
      devintrCaps Γ γ0 γ1 γc γl0 γl1 γd γdl γt pd pav pu bs ⊢ intrRes (GF := GF) cpu := by
  iintro ⟨Hstv, #Hpinv, #Hcaps⟩
  unfold intrRes intrResP
  iexists kernelvecAddr
  iframe Hstv
  isplit
  · ipureintro; exact kernelvecAddr_direct
  isplit
  · imodintro
    iapply (KV.handler Γ γ0 γ1 γc γl0 γl1 γd γdl γt pd pav pu bs cpu)
  · iapply envAt_of_caps' Γ γ0 γ1 γc γl0 γl1 γd γdl γt pd pav pu bs hT $$ [$Hpinv $Hcaps]

end Xv6
