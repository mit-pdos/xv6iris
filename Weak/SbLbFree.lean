/-
Weak: **allocproc route P — [R46.s1] "LB-FREEDOM UNUSED": no census read precedes a store before its
ordering point** (`notes/weak-allocproc-plan-review-R46.md` §2 row 2, §7 [R46.s1]).  Lean-only, no Rocq
twin.  A PRIMED TWIN: nothing registered imports this file.

**Spec, stated first.**  riscv.cat orders a plain load before a po-later STORE only by rule 4 (a fence
with the `r` predecessor and `w` successor bits), rules 9–11 (an address / data / control dependency
into the store) and rule 13; with none of these, RVWMO lets the store become visible before the load
is satisfied (load buffering, LB).  MachCSL-P executes loads in program order and has no LB.  This
file checks, on the image, that for the 18 census load sites (`SilSite.kSites`) the straight-line
path from the load to its certified ordering point (the pinned branch / fence / dependent store of
its `KernelPins` witness) contains NO store, except:

  * `holding+0x12` (`ld a5,16(a0)`, `PResidue`): in each of `holding`'s three call contexts the
    path to the caller's branch on the compare result holds exactly two stores, `mycpu`'s `sd ra,8(sp)`
    / `sd s0,0(sp)` — `sp`-based spills into the hart's own frame (`holding12FrameOnly`);
  * `ismapped+0x10` (`ld a0,0(a0)`, `PResidue`): the path crosses `ismapped`'s `ret` into `vmfault`
    (its only caller) and reaches `vmfault`'s `beqz a0` with NO store (`ismapped10RetFree`).

All 16 other sites reach their point store-free (`lbFreeStatic`); `ilock+0xe` / `iunlock+0x1c` are
stated explicitly (`irefBlezNext`: the pinned `blez` is the next instruction).  CAVEAT (finding
F-W2-LB-1, PROGRESS-W2-blocked.md): `uvmclear+0x10`'s point is a `PDep` STORE (rule 10 orders that
store only) — po-later stores of its caller (`kexec`) are NOT statically ordered after the load;
harmless for the replay because the site is never blocked (PTE custody, Q-6M-PTE (a)), but it is a
third site where RVWMO's LB freedom is not excluded by the text alone.

The walker `SbLbFree.stTo` follows fall-through, enters direct calls (pushing the return point) and
returns through `ret` (popping it); it FAILS on a branch, jump or indirect transfer, so a `some`
result means the path is the unique straight-line one.  Indirect transfers into `holding` /
`ismapped` are not decided (`PinHoldingCtrl`'s residual item, unchanged).

Spec mark: FAITHFUL (image facts; no new trusted text).  Lean-only helpers `SbLbFree.*`.
-/
import Weak.SilSiteTab

namespace Weak

open MachCSL KernelPinsDef KernelPinsDef.Pin

/-- The STORES met on the straight-line path from `pc` to `b` (reached with an empty extra call
stack `cs`), entering direct calls and returning through `ret`; `none` on a branch, jump, indirect
transfer, an unmatched `ret`, or out of fuel.  The store at `b` itself is not counted. -/
def SbLbFree.stTo : Nat → List Int → Int → Int → Option (List Int)
  | 0, _, _, _ => none
  | n + 1, cs, pc, b =>
    if cs.isEmpty && pc == b then some [] else
    let st : List Int := if roleIsStore (krole pc) then [pc] else []
    match kflowOf pc with
    | .FLnone => (SbLbFree.stTo n cs (pc + wSize (kw pc)) b).map (st ++ ·)
    | .FLcall t => (SbLbFree.stTo n ((pc + wSize (kw pc)) :: cs) t b).map (st ++ ·)
    | .FLret =>
      match cs with
      | r :: cs' => (SbLbFree.stTo n cs' r b).map (st ++ ·)
      | [] => none
    | _ => none

/-- The certified ordering point of a pin witness (`PCtrl` branch, `PFence` fence, `PDep` store). -/
def SbLbFree.certPt : Pin → Option Int
  | .PCtrl b _ => some b
  | .PFence b _ => some b
  | .PDep b _ => some b
  | _ => none

/-- The two exception sites of [R46.s1]. -/
def SbLbFree.exc : List Int :=
  [SilSite.sym KernelSyms.«holding» 0x12, SilSite.sym KernelSyms.«ismapped» 0x10]

/-- **THE 16 STATIC SITES**: every census site other than the two exceptions has a certified point,
and the straight-line path from the instruction after the load to it holds NO store. -/
theorem SbLbFree.lbFreeStatic :
    SilSite.kSites.all (fun s => SbLbFree.exc.contains s.pc ||
      match SbLbFree.certPt s.pin with
      | some b => SbLbFree.stTo 16 [] (s.pc + wSize (kw s.pc)) b == some []
      | none => false) = true ∧
    (SilSite.kSites.filter (fun s => !SbLbFree.exc.contains s.pc)).length = 16 := by
  decide +kernel

/-- **`ilock+0xe` / `iunlock+0x1c`** (the exempt `ip->ref` reads, [OWN.112]): the pinned `blez` is the
NEXT instruction. -/
theorem SbLbFree.irefBlezNext :
    (SilSite.sym KernelSyms.«ilock» 0xe, Pin.PCtrl 0x80003362 false) ∈ pins ∧
    SilSite.sym KernelSyms.«ilock» 0xe + wSize (kw (SilSite.sym KernelSyms.«ilock» 0xe)) = 0x80003362 ∧
    roleIsBranch (krole 0x80003362) = true ∧
    (SilSite.sym KernelSyms.«iunlock» 0x1c, Pin.PCtrl 0x8000341e false) ∈ pins ∧
    SilSite.sym KernelSyms.«iunlock» 0x1c + wSize (kw (SilSite.sym KernelSyms.«iunlock» 0x1c)) =
      0x8000341e ∧
    roleIsBranch (krole 0x8000341e) = true := by
  decide +kernel

/-- **`uvmclear+0x10`** (`PDep`): the dependent store `sd a5,0(a0)` is reached store-free — and it is
the ONLY instruction rule 10 orders after the load (finding F-W2-LB-1). -/
theorem SbLbFree.uvmclearDep :
    (SilSite.sym KernelSyms.«uvmclear» 0x10, Pin.PDep 0x80001514 false) ∈ pins ∧
    SbLbFree.stTo 8 [] (SilSite.sym KernelSyms.«uvmclear» 0x10 +
      wSize (kw (SilSite.sym KernelSyms.«uvmclear» 0x10))) 0x80001514 = some [] ∧
    roleIsStore (krole 0x80001514) = true := by
  decide +kernel

/-- **EXCEPTION 1, `holding+0x12`**: in each of `holding`'s three call contexts (`holdingCallSites`:
return point, the caller's branch on `a0`), the path from the load to the caller's branch holds
exactly `mycpu`'s two spills `sd ra,8(sp)` (`mycpu+0x2`) and `sd s0,0(sp)` (`mycpu+0x4`), both with
base register `sp` (x2); the caller's branch tests `a0` (x10).  (The callers are exactly these three:
`SilSite.holdCtxCover`.) -/
theorem SbLbFree.holding12FrameOnly :
    holdingCallSites.all (fun rb =>
      SbLbFree.stTo 40 [rb.1] (SilSite.sym KernelSyms.«holding» 0x12 +
          wSize (kw (SilSite.sym KernelSyms.«holding» 0x12))) rb.2 ==
        some [SilSite.sym KernelSyms.«mycpu» 0x2, SilSite.sym KernelSyms.«mycpu» 0x4] &&
      roleIsBranch (krole rb.2) && srcsTainted [10] (depsCtrl (krole rb.2))) = true ∧
    krole (SilSite.sym KernelSyms.«mycpu» 0x2) = .ORstore 2 1 ∧
    krole (SilSite.sym KernelSyms.«mycpu» 0x4) = .ORstore 2 8 := by
  decide +kernel

/-- `ismapped`'s only caller: its return point `vmfault+0x2e`, and the branch `vmfault+0x30`. -/
def SbLbFree.ismappedRet : Int := SilSite.sym KernelSyms.«vmfault» 0x2e

/-- **EXCEPTION 2, `ismapped+0x10`**: every direct call of `ismapped` returns to `vmfault+0x2e`, and
from the load the path across `ismapped`'s `ret` reaches `vmfault+0x30`'s `beqz a0` with NO store. -/
theorem SbLbFree.ismapped10RetFree :
    textPcs.all (fun pc =>
      match kflowOf pc with
      | .FLcall tgt => !(tgt == (KernelSyms.«ismapped» : Int)) || pc + wSize (kw pc) == SbLbFree.ismappedRet
      | _ => true) = true ∧
    SbLbFree.stTo 16 [SbLbFree.ismappedRet] (SilSite.sym KernelSyms.«ismapped» 0x10 +
      wSize (kw (SilSite.sym KernelSyms.«ismapped» 0x10))) (SilSite.sym KernelSyms.«vmfault» 0x30) =
      some [] ∧
    roleIsBranch (krole (SilSite.sym KernelSyms.«vmfault» 0x30)) = true ∧
    srcsTainted [10] (depsCtrl (krole (SilSite.sym KernelSyms.«vmfault» 0x30))) = true := by
  decide +kernel

end Weak
