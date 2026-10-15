/-
Weak: **W11-C2′ [OWN.82] — the interface of the `relSiteWCrel` proof** (plan rev 52 §D
Q-WCREL-2, route (a)).

`relSiteWCrel σ log` (`Weak/RvwmoXv6Adequacy.lean`) says every pf log message whose entry is a
sync path's first move (a hop release on a hop byte, or a publication store) is `.WCrel`.  The
ruled route splits it in three; this file NAMES the two halves of that split and proves the
composition, so the MachCSL lane ((a1)) and the pf lane ((a2)+(a3)) can work to a fixed
statement.

* (a1) `RelSiteProv.relProvExport σ pl` — the MachCSL PROVENANCE export (NAMED; the machine
  lane's): `pl` is the issuing-pc log, one entry per store timestamp (the twin of `σ.log`,
  `pl[q]` = the PC of the instruction whose store created timestamp `q + 1`), and every
  first-move entry was issued at a pc in `releasePcs`.  Maintained by `wp_s_sw_zero_release_gen`
  and the boot `started` store; exported like `powerInterp_accessDisc`.
* (a2)+(a3) `RelSiteProv.relPcWCrel log pl` — the pf side (NAMED): a log message issued at a
  release pc is `.WCrel`.  (a2) is that the SAME `pl` indexes the pf log (W4 `SimRel`'s
  per-hart lock-step: same Sail node, same registers, so the same PC at the store step);
  (a3) is the pf-run invariant "a store at a release pc sees `wRelp = true`", whose last step is
  `RelSiteProv.pclsEvPlainRelp`.
* `RelSiteProv.relSiteWCrelOfProv` — the composition.

Lean-only (no Rocq counterpart); every name is file-qualified (`RelSiteProv.*`).
-/
import Weak.RvwmoXv6Adequacy
import Weak.KernelSitesDef
import Weak.WeakEvInst

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D
open Wlabel

/-- **(a1) NAMED — the MachCSL provenance export.**  `pl` is the issuing-pc log (one entry per
store timestamp, aligned with `σ.log`: the issuing hart's `PC` for a PLAIN store, `-1` for an
exclusive / AMO write — including the page walker's A/D write-back — and for the disk; see
`RelSiteProvPc.recPc`); every entry that is a sync path's first move
(`RvwmoXv6Adequacy.relEntAt`) was issued at a pc in `releasePcs` (`release+0x1a`,
`main+0xb0`). -/
def RelSiteProv.relProvExport (σ : MState) (pl : List Int) : Prop :=
  pl.length = σ.log.length ∧
  ∀ q : Nat, RvwmoXv6Adequacy.relEntAt σ (q + 1) →
    ∃ pc, pl[q]? = some pc ∧ pc ∈ releasePcs

/-- **(a2)+(a3) NAMED — the pf side.**  A pf log message whose issuing pc (by the same `pl`)
is a release pc is release-class. -/
def RelSiteProv.relPcWCrel (log : List Wmsg) (pl : List Int) : Prop :=
  ∀ (q : Nat) (mq : Wmsg) (pc : Int), log[q]? = some mq → pl[q]? = some pc →
    pc ∈ releasePcs → mq.wmAk = .WCrel

/-- **The composition**: (a1) and (a2)+(a3) at one issuing-pc log give `relSiteWCrel`. -/
theorem RelSiteProv.relSiteWCrelOfProv (σ : MState) (log : List Wmsg) (pl : List Int) :
    RelSiteProv.relProvExport σ pl → RelSiteProv.relPcWCrel log pl → relSiteWCrel σ log := by
  rintro ⟨-, hprov⟩ hpf q mq hq hrel
  obtain ⟨pc, hpc, hmem⟩ := hprov q hrel
  exact hpf q mq pc hq hpc hmem

/-- **(a3)'s last step**: at a hart's `memWrite` node of a non-exclusive access kind (the
release `sw`: `AK_explicit` plain/normal), a store label is stamped `.WCrel` when the hart's
`wRelp` is set. -/
theorem RelSiteProv.pclsEvPlainRelp (cpu : CPU) (n va : Nat)
    (req : Mem_write_request n va Arch.pa Arch.translation Arch.arch_ak) K (rs : RegFile)
    (fn : Option (Bool × Bool × Bool × Bool)) (ib : Ibch) (ws : Wstate) (rl : Bool) (base : Int)
    (data : List (BitVec 8)) (asrc vsrc : List Dsrc) :
    (classify req.access_kind).akLatest = false → ws.wRelp = true →
    pclsEv (.PHart cpu (.impure (.ok (.memWrite n va req)) K) rs fn ib)
      (LStore rl base data asrc vsrc) ws = .WCrel := by
  intro hlat hrelp
  simp [pclsEv, pnodeWclass, wmClassOf, hlat, hrelp]

end Weak
