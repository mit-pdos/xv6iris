/-
`pid_lock` (kernel/proc.c): protects `nextpid` and the pid scan of
`allocpid` (inlined into `allocproc`), which reads every process's `pid`
without its lock.  The payload carries the `nextpid` word and a quarter
of every `pid` word (the private block keeps a half, `p->lock` a quarter),
with the invariant that live pids are distinct and in `[1, PIDMAX]`.

THE PID LEDGER (NI-LEDGER-REST W2, Rocq 8043e4cdd; design
`claude-notes/design/ni-pid-ledger.md` D3): a fourth thing the lock
protects, riding beside the register it mirrors -- the authority of the
actor-labelled history of every allocation and release (`PidEv.Pev`, at the
canonical `WchG.wplName`), tied to the register by its live set alone
(`pidLedger R`: `liveOf h = PartialMap.dom R`).  allocproc appends
`PAlloc p pid` at its insert and freeproc `PFree p pid` at its delete, each
handing its caller a persistent receipt (`SlotGen.pidReceipt`).  The counter
tie and the scan's first-ness are not stated (ruling R2(a)).

## Deviations from Rocq (the ledger)

1. The tie is an equality of PREDICATES on `Int` (`PidEv` deviation 2):
   `liveOf h = PartialMap.dom R`, Rocq `live_of h = dom R` (a `gset Z`).
   `pidDom_empty/insert/delete` are the three `dom` rewrites the steps use
   (Rocq's `dom_empty_L`/`dom_insert_L`/`dom_delete_L`).
2. `pidLockResAt` changes IN PLACE, as Rocq's `nextpid_res_at` did: its
   statement and every statement naming it (`pidLockPay`, the
   `isLock … pidLockPay` of every client) are byte-identical; the body gains
   the conjunct `pidLedger R` right after `pidRegAuth R`.  No Timeless
   instance (the Lean payload has none to keep).
-/
import Xv6.ProcDefs

namespace Xv6

open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode Std MachCSL

/-- `&nextpid`, `&initproc` (`&pid_lock` is `Xv6/SpecProcinit.lean`'s
`pidLockAddr`). -/
def nextpidAddr : BitVec 64 := KA.«nextpid»
def initprocAddr : BitVec 64 := KA.«initproc»
-- `PIDMAX` is `Xv6/ProcGeom.lean`'s (Rocq `ProcGeom.PIDMAX`).

/-- The pids are distinct where nonzero, and in range. -/
def pidsOk (pids : Nat → BitVec 32) : Prop :=
  ∀ j1 j2, j1 < NPROC → j2 < NPROC → pids j1 ≠ 0#32 → pids j1 = pids j2 → j1 = j2

/-! ## The register's domain, step by step (deviation 1) -/

theorem pidDom_empty : PartialMap.dom (∅ : IntMapF GName) = fun _ => False := by
  funext k
  simp only [PartialMap.dom, get?_empty, Option.isSome_none, Bool.false_eq_true]

theorem pidDom_insert (R : IntMapF GName) (x : Int) (g : GName) :
    PartialMap.dom (PartialMap.insert R x g) = fun k => k = x ∨ PartialMap.dom R k := by
  funext k
  apply propext
  rw [Iris.Std.LawfulPartialMap.dom_insert_iff, eq_comm]

theorem pidDom_delete (R : IntMapF GName) (x : Int) :
    PartialMap.dom (PartialMap.delete R x) = fun k => PartialMap.dom R k ∧ k ≠ x := by
  funext k
  apply propext
  by_cases h : x = k
  · subst h
    simp only [PartialMap.dom, get?_delete_eq rfl, Option.isSome_none, Bool.false_eq_true,
      ne_eq, not_true_eq_false, and_false]
  · simp only [PartialMap.dom, get?_delete_ne h, ne_eq]
    exact ⟨fun h' => ⟨h', fun e => h e.symm⟩, fun h' => h'.1⟩

section
variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [WchG GF]

/-- THE PID LEDGER, as the lock's payload holds it (Rocq `pid_ledger`, design
ni-pid-ledger.md D3, ruling R2(a)): the history's authority, tied to the
register by its live set alone.  Context-free, so the payload is still a
`CtxMorph`. -/
def pidLedger (R : IntMapF GName) : IProp GF := iprop%
  ∃ h : List Pev, pidLedAuth h ∗ ⌜liveOf h = PartialMap.dom R⌝

/-- The payload of `pid_lock` at context `ξ` (Rocq `PidLock.nextpid_res_at`):
the counter in `[1, PIDMAX]`, a quarter of every slot's `pid` cell, THE PID
REGISTER's authority (`SlotGen.pidRegAuth`, D8) with its domain fact
(`pidRegDom`: every registered pid is nonzero and held by some slot), and
THE BOOT ERA'S TWO MARKS -- the counter is 1, and no slot holds pid 1 --
each discharged for good by the one-shot `nextpidShot` (fired by the first
allocation's store to `nextpid`).  The distinctness conjunct `pidsOk` is
Lean's (kept from the pre-D8 payload; Rocq derives what it needs from the
scan and the register).  ...AND THE PID LEDGER beside the register
(`pidLedger R`, NI-LEDGER-REST; header). -/
def pidLockResAt [CurCtx] (ξ : CtxId) : IProp GF := iprop%
  ∃ (np : BitVec 32) (pids : Nat → BitVec 32),
    ⌜1 ≤ np.toNat ∧ np.toNat ≤ PIDMAX ∧ pidsOk pids⌝ ∗
    wordAtN ξ nextpidAddr 4 (DFrac.own 1) np ∗
    ([∗list] j ∈ List.range NPROC, wordAtN ξ (pPid (procAddr j)) 4 pidLockQ (pids j)) ∗
    (⌜np.toNat = 1⌝ ∨ nextpidShot) ∗
    ∃ R : IntMapF GName, ⌜pidRegDom R pids⌝ ∗ pidRegAuth R ∗ pidLedger R ∗
      (⌜∀ j, j < NPROC → (pids j).toNat ≠ 1⌝ ∨ nextpidShot)

/-- The payload as a function of the holder's context. -/
def pidLockPay [CurCtx] : CtxId → IProp GF := fun ξ => pidLockResAt ξ

/-- `pid_lock`'s payload transports between contexts, so `acquire` and
`release` apply to it (the register rows are ghost: constants). -/
instance instCtxMorphPidLockPay [CurCtx] : CtxMorph (GF := GF) pidLockPay := by
  unfold pidLockPay pidLockResAt
  exact @instCtxMorphExists hlc GF _ _ _ (fun _ => @instCtxMorphExists hlc GF _ _ _ (fun pids =>
    @instCtxMorphSep hlc GF _ _ _ (instCtxMorphConst _)
      (@instCtxMorphSep hlc GF _ _ _ (instCtxMorphWordAtN _ _ _ _)
        (@instCtxMorphSep hlc GF _ _ _
          (ctxMorph_bigSepL (List.range NPROC)
            (fun _ y ξ => wordAtN ξ (pPid (procAddr y)) 4 pidLockQ (pids y))
            (fun _ _ => instCtxMorphWordAtN _ _ _ _))
          (instCtxMorphConst _)))))

/-! ## The ledger's ghost steps (design ni-pid-ledger.md §3 W2)

Each mirrors the register step it rides beside (`SlotGen.pidReg_insert` /
`pidReg_delete`) and hands back the receipt of the event it appended. -/

/-- The boot's: the empty history is the empty register's ledger (Rocq
`pid_ledger_empty`). -/
theorem pidLedger_empty : pidLedAuth (GF := GF) [] ⊢ pidLedger ∅ := by
  unfold pidLedger
  iintro Ha
  iexists []
  iframe Ha
  ipureintro
  rw [pidDom_empty]; rfl

/-- allocproc's, at the register's insert (Rocq `pid_ledger_alloc`). -/
theorem pidLedger_alloc (R : IntMapF GName) (act : BitVec 64) (pid : BitVec 32) (g : GName) :
    pidLedger (GF := GF) R ⊢
      |==> (pidLedger (PartialMap.insert R (pid.toNat : Int) g) ∗
        ∃ h, pidReceipt h (.PAlloc act pid)) := by
  unfold pidLedger pidReceipt
  iintro ⟨%h, Ha, %hl⟩
  imod pidLedAuth_grow h (.PAlloc act pid) $$ Ha with ⟨Ha, #Hb⟩
  imodintro
  isplitl [Ha]
  · iexists h ++ [.PAlloc act pid]
    iframe Ha
    ipureintro
    rw [liveOf_snoc_alloc_dom _ h act pid hl, pidDom_insert]
  · iexists h
    iexact Hb

/-- freeproc's, at the register's delete (Rocq `pid_ledger_free`). -/
theorem pidLedger_free (R : IntMapF GName) (act : BitVec 64) (pid : BitVec 32) :
    pidLedger (GF := GF) R ⊢
      |==> (pidLedger (PartialMap.delete R (pid.toNat : Int)) ∗
        ∃ h, pidReceipt h (.PFree act pid)) := by
  unfold pidLedger pidReceipt
  iintro ⟨%h, Ha, %hl⟩
  imod pidLedAuth_grow h (.PFree act pid) $$ Ha with ⟨Ha, #Hb⟩
  imodintro
  isplitl [Ha]
  · iexists h ++ [.PFree act pid]
    iframe Ha
    ipureintro
    rw [liveOf_snoc_free_dom _ h act pid hl, pidDom_delete]
  · iexists h
    iexact Hb

end

end Xv6
