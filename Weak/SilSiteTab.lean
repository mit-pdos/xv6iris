/-
Weak: **row 6m (W11-F B5), increment C1 — THE SITE CENSUS of the twin's per-step datum, as a checked
table** (`notes/W10-6m-census.md`; `PROGRESS-W11F-6i6m.md` Task C).  Lean-only, no Rocq twin.

The census of `CatLin.SilOrd.stepSupplyS` (`Weak/SilOrd.lean:288`) names the load sites whose value
the twin walk may have to POISON (the graph's source is not available to the walk): 18 kernel-text
load sites of the 1 689 (`Weak/KernelPins.lean`), the one failed-acquire slot, and the device
program's reads.  This file records them with their custody class and their ROUTE, and checks against
the image, by `decide +kernel`, everything about them that is a property of the binary:

  * every listed pc is a LOAD (`roleIsLoad (krole pc)`) and carries the pin-table witness the census
    read (`kSitesPinned`), the pcs are distinct (`kSitesNodup`) — 18 rows (`kSitesLen`);
  * the failed-acquire slot `acquire+0x1c` is the image's ONLY AMO (`amoOnlySilent`), and its spin
    loop is the census's 4-instruction shape: the AMO's `a5` reaches the back-edge `bnez` through
    `sext.w` only, and the loop head `mv a5,a4` overwrites it (`spinShape`);
  * `holding+0x0`'s three call contexts are exactly `holding`'s direct callers
    (`PinHoldingCtrl.holdingCallersCover`, `holdingNoJumpIn`, `holdingNoFallIn`, re-exported as
    `holdCtxCover`): from `acquire` ORDER-pinned, from `release` / `sched` the caller holds the lock;
  * the ORDER-pinned kernel reads (`pinRd`, census §7 item 1) are exactly the rows of route `order`
    plus `holding+0x0` (`pinRdOfTab`).

Routes (census §3): `taint` — a value argument or a dead (bit-level) taint, ORDER-FREE (C2,
`Weak/SilSiteTaint.lean`); `ctx` — per call context (`holdCtx`); `order` — the walk order must honour
the read's source (row 6l; named premises in `Weak/SilSite.lean`); `noTaint` — not dischargeable by
taint (the PTE value reaches exit-write DATA; Q-6M-PTE).

Spec: none — a table of image facts (the decoder `depsOfBits`/`kflowOf` is the pin checker's;
`KernelPinsDef`'s residual trust items apply unchanged).  Lean-only helpers `SilSite.*`.
-/
import Weak.PinHoldingCtrl

namespace Weak

open MachCSL KernelPinsDef KernelPinsDef.Pin

namespace SilSite

/-- The custody class of the byte a census site reads (`Xv6/AccessDiscipline.lean` `custAt`; `disk` =
a RAM byte written by the disk, `e.tid = NCPU`, outside `chainOkAt`). -/
inductive Cls where
  | lockw
  | pub
  | racy
  | pte
  | disk
  deriving DecidableEq, Repr

/-- How the census discharges the site (`notes/W10-6m-census.md` §3). -/
inductive Route where
  /-- T: a value argument / dead (bit-level) taint — ORDER-FREE -/
  | taint
  /-- per call context (`holding+0x0`: `holdCtx`) -/
  | ctx
  /-- P: the walk order must walk the read between its graph source and that source's co-successor -/
  | order
  /-- N: a poisoned value reaches exit-write data — only a PTE custody chain makes it agree -/
  | noTaint
  deriving DecidableEq, Repr

/-- One census row: the load pc, the class of its byte, its route, and the pin-table witness. -/
structure Site where
  pc : Int
  cls : Cls
  route : Route
  pin : Pin
  deriving DecidableEq, Repr

def sym (s : Nat) (off : Int) : Int := (s : Int) + off

/-- **THE 18 KERNEL-TEXT CENSUS SITES** (census §3.1–§3.5), in census order. -/
def kSites : List Site :=
  [ -- 3.1 lock words
    ⟨sym KernelSyms.«holding» 0x0, .lockw, .ctx, .PCtrl 0x80000bf4 false⟩
  , ⟨sym KernelSyms.«holding» 0x12, .lockw, .taint, .PResidue⟩
    -- 3.2 publication word
  , ⟨sym KernelSyms.«main» 0x16, .pub, .order, .PFence 0x80000ee6 false⟩
    -- 3.3 racy word (ip->ref)
  , ⟨sym KernelSyms.«ilock» 0xe, .racy, .taint, .PCtrl 0x80003362 false⟩
  , ⟨sym KernelSyms.«iunlock» 0x1c, .racy, .taint, .PCtrl 0x8000341e false⟩
    -- 3.4 user page-table bytes
  , ⟨sym KernelSyms.«walk» 0x32, .pte, .taint, .PCtrl 0x80000fe8 false⟩
  , ⟨sym KernelSyms.«walkaddr» 0x1c, .pte, .taint, .PCtrl 0x8000106e false⟩
  , ⟨sym KernelSyms.«mappages» 0x4a, .pte, .taint, .PCtrl 0x800010d0 false⟩
  , ⟨sym KernelSyms.«uvmunmap» 0x5e, .pte, .taint, .PCtrl 0x800012c4 false⟩
  , ⟨sym KernelSyms.«freewalk» 0x2a, .pte, .taint, .PCtrl 0x80001408 false⟩
  , ⟨sym KernelSyms.«ismapped» 0x10, .pte, .taint, .PResidue⟩
  , ⟨sym KernelSyms.«copyout» 0x82, .pte, .taint, .PCtrl 0x80001648 false⟩
  , ⟨sym KernelSyms.«uvmcopy» 0x36, .pte, .noTaint, .PCtrl 0x800014a4 false⟩
  , ⟨sym KernelSyms.«uvmclear» 0x10, .pte, .noTaint, .PDep 0x80001514 false⟩
    -- 3.5 disk-written RAM (virtio used ring / status)
  , ⟨sym KernelSyms.«virtio_disk_intr» 0x36, .disk, .order, .PCtrl 0x80005d62 false⟩
  , ⟨sym KernelSyms.«virtio_disk_intr» 0x4e, .disk, .order, .PCtrl 0x80005d86 false⟩
  , ⟨sym KernelSyms.«virtio_disk_intr» 0x5a, .disk, .order, .PCtrl 0x80005d86 false⟩
  , ⟨sym KernelSyms.«virtio_disk_intr» 0x82, .disk, .order, .PCtrl 0x80005dae false⟩ ]

theorem kSitesLen : kSites.length = 18 := rfl

theorem kSitesNodup : (kSites.map Site.pc).Nodup := by decide +kernel

/-- Every census row is a LOAD of the image and carries the pin table's witness. -/
theorem kSitesPinned :
    kSites.all (fun s => roleIsLoad (krole s.pc) && decide ((s.pc, s.pin) ∈ pins)) = true := by
  decide +kernel

theorem kSitesLoad (s : Site) (h : s ∈ kSites) : roleIsLoad (krole s.pc) = true := by
  have := List.all_eq_true.1 kSitesPinned s h
  simp only [Bool.and_eq_true] at this
  exact this.1

theorem kSitesPin (s : Site) (h : s ∈ kSites) : (s.pc, s.pin) ∈ pins := by
  have := List.all_eq_true.1 kSitesPinned s h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at this
  exact this.2

/-! ## The failed-acquire slot -/

/-- `acquire+0x1c`, `amoswap.w.aq a5,a5,(s1)` — the twin's only SILENT slot. -/
def silentPc : Int := sym KernelSyms.«acquire» 0x1c

def roleIsAmo (r : OpRoles) : Bool :=
  match r with
  | .ORamo _ _ _ => true
  | _ => false

/-- **THE ONLY AMO** of the flat text walk is the failed-acquire slot. -/
theorem amoOnlySilent :
    textPcs.all (fun pc => !(roleIsAmo (krole pc)) || pc == silentPc) = true := by
  decide +kernel

theorem silentIsAmo : krole silentPc = .ORamo 15 9 15 := by decide +kernel

/-- **THE SPIN LOOP'S SHAPE**: the loop head `mv a5,a4` (`acquire+0x1a`) overwrites `a5`; the AMO
(`+0x1c`) is followed by `sext.w a5,a5` (`+0x20`, keeps the taint of `a5`) and the back-edge `bnez a5`
(`+0x22`) to the loop head, which tests it. -/
theorem spinShape :
    taintStep [15] (sym KernelSyms.«acquire» 0x1a) = [] ∧
    kflowOf silentPc = .FLnone ∧ silentPc + wSize (kw silentPc) = sym KernelSyms.«acquire» 0x20 ∧
    taintStep [15] (sym KernelSyms.«acquire» 0x20) = [15] ∧
    kflowOf (sym KernelSyms.«acquire» 0x20) = .FLnone ∧
    kflowOf (sym KernelSyms.«acquire» 0x22) = .FLbranch (sym KernelSyms.«acquire» 0x1a) ∧
    srcsTainted [15] (depsCtrl (krole (sym KernelSyms.«acquire» 0x22))) = true := by
  decide +kernel

/-! ## `holding+0x0`'s call contexts -/

/-- The route of `holding+0x0` per call context, by the call's RETURN POINT (`holdingCallSites`):
from `acquire` the caller does not hold the lock (ORDER-pinned, census F2 / Q-6M-HOLD); from
`release` and `sched` it does (the value is the holder's `1` on both sides). -/
def holdCtx : List (Int × Route) :=
  [ (sym KernelSyms.«acquire» 0x16, .order)
  , (sym KernelSyms.«release» 0x10, .taint)
  , (sym KernelSyms.«sched» 0x18, .taint) ]

theorem holdCtxSites : holdCtx.map Prod.fst = holdingCallSites.map Prod.fst := by decide +kernel

/-- `holding`'s ONLY entries are the three direct calls of `holdCtx` (re-export of
`Weak/PinHoldingCtrl.lean` §1): every direct call of `holding` returns to a `holdCtx` point, no
direct transfer from outside lands in its body, nothing falls into it.  (Indirect transfers into
`holding` are not decided — `PinHoldingCtrl`'s residual item.) -/
theorem holdCtxCover :
    textPcs.all (fun pc =>
      match kflowOf pc with
      | .FLcall tgt =>
          !(tgt == (KernelSyms.«holding» : Int)) || holdCtx.any (fun ab => ab.1 == pc + wSize (kw pc))
      | _ => true) = true ∧
    textPcs.all PinHoldingCtrl.noJumpInAt = true ∧
    kflowOf ((KernelSyms.«holding» : Int) - 2) = .FLret := by
  refine ⟨?_, holdingNoJumpIn, holdingNoFallIn⟩
  decide +kernel

/-! ## The order-pinned kernel reads (census §7 item 1) -/

/-- **THE PINNED-READ SET** (kernel text): the `order` rows and `holding+0x0` (its `acquire` context). -/
def pinRd : List Int :=
  [ sym KernelSyms.«holding» 0x0, sym KernelSyms.«main» 0x16
  , sym KernelSyms.«virtio_disk_intr» 0x36, sym KernelSyms.«virtio_disk_intr» 0x4e
  , sym KernelSyms.«virtio_disk_intr» 0x5a, sym KernelSyms.«virtio_disk_intr» 0x82 ]

theorem pinRdOfTab :
    pinRd = (kSites.filter (fun s => s.route == .order || s.route == .ctx)).map Site.pc := by
  decide +kernel

/-- The ORDER-FREE rows (route `taint`): 3 value-argument sites + 7 bit-level PTE sites. -/
def tSites : List Int := (kSites.filter (fun s => s.route == .taint)).map Site.pc

theorem tSitesLen : tSites.length = 10 := by decide +kernel

end SilSite

end Weak
