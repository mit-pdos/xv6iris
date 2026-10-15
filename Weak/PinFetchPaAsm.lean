/-
Weak: **r2 glue (C) — THE ASSEMBLY: `fetchRealized` ⇒ a walk cycle's fetch reads are at
`pc + 2k`** (`fetchOkRF` (i); `PROGRESS-r2glue.md`).  Lean-only.

`fetchRealized` is the fetch twin of `PinDataOk.dataRealized` (W11-F's obligation): at every walk
cycle at `pc` (from its boundary's FIRST `LInstr`), configurations of the two fetch translations —
`c1` for `PC`, `c2` for `PC + 2` (one register filter `c` for both, `TCfg.vs`; pages in RAM; root
below `2^31`; kernel-text `pc`) — such that the cycle's starting register file is `tvRk c`-admitted
(`satp` the kernel's, the TLB caching only identity entries for both vpns, boot-admitted) and
every RAM-read label of the cycle answers the walks' PTE slots (`labAnsOk`).

**Deviation (spec):** cycRun's `fetchOkR2` (i) is UNPROVABLE as stated: its premise
`cycIn em pfx ls0 (ls1 ++ [LIFetch a tvs])` only says the label is in the EMISSION; nothing ties it
to a step of the hart from the `irun ls1` end state (the hart is nondeterministic — `choose` nodes,
the memory-write retry loop), and `ls0` may run whole further cycles.  `fetchOkRF` (i) adds
`LInstr ∉ ls0` (as `dataOkRF`) and `irun (ls1 ++ [LIFetch a tvs]) q d1 pm dm` — the fetch label is
a step of the in-cycle run.  Its use `cycWalk` gets that from `cyRun` passing the label's step to
its `hA` premise (w1's change).  Every helper is `Weak.PinFetchPa.*`.
-/
import Weak.PinFetchPaRunF
import Weak.PinDataOkAsm

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open Sail Sail.ConcurrencyInterfaceV1 LeanRV64D LeanRV64D.Functions
open Sail.ArchSem (FreeM)
open Wlabel KernelPinsDef

namespace PinFetchPa
open SailCycleOrderK PinCycRun PinDataflow
open PinDataOk (labD splitLast pevrunNil)

/-- The answer filter of the two fetch translations. -/
def fqD (c1 c2 : TCfg) (pa : BitVec 64) (n : Nat) (w : BitVec (8 * n)) : Prop :=
  tvAns c1 pa n w ∧ tvAns c2 pa n w

/-- **THE FETCH, REALIZED (INTERFACE, header; W11-F's obligation).** -/
def fetchRealized (p0 : Pexv6) (d0 : Efab) (em : Hemission) (pc : Int) : Prop :=
  ∀ (pfx : List Eitem) (ls0 : List Wlabel) (q : Pexv6) (d1 : Efab),
    LInstr ∉ ls0 → cycStart p0 d0 em pfx pc ls0 q d1 →
    ∃ c c1 c2 : TCfg,
      fqCfg c (fqD c1 c2) (BitVec.ofInt 64 pc) c1 ∧
      fqCfg c (fqD c1 c2) (BitVec.addInt (BitVec.ofInt 64 pc) 2) c2 ∧
      (∀ (cpu : CPU) (tick : Bool) (rs : RegFile), q = .PHart cpu (riscvStep tick) rs none ibNone →
        tvRkAll c rs) ∧
      ∀ (ls1 : List Wlabel) (pm : Pexv6) (dm : Efab), cycIn em pfx ls0 ls1 → irun ls1 q d1 pm dm →
        ∀ l ∈ ls1, labAnsOk c1 l ∧ labAnsOk c2 l

/-- **`fetchOkR2` (i), restated** (header). -/
def fetchOkRFi (p0 : Pexv6) (d0 : Efab) (em : Hemission) (pc : Int) : Prop :=
  ∀ (pfx : List Eitem) (ls0 : List Wlabel) (q : Pexv6) (d1 : Efab) (ls1 : List Wlabel)
    (pm : Pexv6) (dm : Efab) (a : Int) (tvs : List (Nat × BitVec 8)),
    LInstr ∉ ls0 → cycStart p0 d0 em pfx pc ls0 q d1 → cycIn em pfx ls0 (ls1 ++ [LIFetch a tvs]) →
    irun (ls1 ++ [LIFetch a tvs]) q d1 pm dm → a = pc + 2 * ((feLabs ls1).length : Int)

/-- A label admitted by both translations' PTE filters is `fqD`-admitted. -/
theorem labDOfAnsOk2 (c1 c2 : TCfg) (l : Wlabel) (h1 : labAnsOk c1 l) (h2 : labAnsOk c2 l) :
    labD (fqD c1 c2) l := by
  cases l <;> first
    | exact fun pa n w ha hb => ⟨h1 pa n w ha hb, h2 pa n w ha hb⟩
    | trivial

set_option maxHeartbeats 4000000 in
/-- **`fetchOkRF` (i) FROM THE INTERFACE** (header). -/
theorem fetchOkRFiOf (p0 : Pexv6) (d0 : Efab) (em : Hemission) (pc : Int) (h0 : 0 ≤ pc)
    (hlt : pc + 2 < 2 ^ 64) (hreal : fetchRealized p0 d0 em pc) : fetchOkRFi p0 d0 em pc := by
  intro pfx ls0 q d1 ls1 pm dm a tvs hni hcs hcin hir
  obtain ⟨c, c1, c2, hc1, hc2, hrk, hlabs⟩ := hreal pfx ls0 q d1 hni hcs
  obtain ⟨p, d, hbd, hrun0, -⟩ := hcs
  obtain ⟨-, -, cpu0, rs, fn, ib, rfl, hkinv⟩ := hbd
  rcases pureSplit _ _ _ _ _ hrun0 cpu0 rs fn ib rfl hkinv.2.2 with hni' |
    ⟨ls0', ls1', rs'', tick', d1'', hls, -, -, hr0, hr1, hag, hrb'⟩
  · exact absurd (List.mem_append_right _ List.mem_cons_self) hni'
  obtain ⟨hs1, hs2⟩ := splitLast LInstr ls0 ls0' ls1' hni hls
  subst ls0'
  subst ls1'
  obtain ⟨hq, hd1⟩ := pevrunNil hr1
  subst d1''
  have hall := hrk cpu0 tick' rs'' hq
  subst hq
  have hkinv' : kInv pc rs'' := PinCycRun.kInvAgree pc rs rs'' hag hrb' hkinv
  let st0 : CySt := ⟨rs'', [], false, ⟨OpRoles.ORnone, [], 0, true⟩⟩
  have hcy0 := cyFSailOf c (fqD c1 c2) pc h0 hlt c1 c2 hc1 hc2 tick' st0 rfl rfl hkinv'.1 hall
  have hm0 : cyMatch st0 rs'' ibNone := ⟨fun _ _ => rfl, hrb', hrb', rfl, rfl, rfl⟩
  have hL : ∀ l ∈ ls1 ++ [LIFetch a tvs], labD (fqD c1 c2) l := by
    intro l hl
    obtain ⟨h1, h2⟩ := hlabs _ pm dm hcin hir l hl
    exact labDOfAnsOk2 c1 c2 l h1 h2
  have hdev : ∀ pa n w, devAddr pa = true → fqD c1 c2 pa n w :=
    fun pa n w hd => ⟨tvAnsDev hc1.1 pa n w hd, tvAnsDev hc2.1 pa n w hd⟩
  have := cyFRun _ _ _ _ _ hir cpu0 (riscvStep tick') rs'' none ibNone st0 rfl hcy0 hm0 hL hdev
    ls1 a tvs [] rfl
  show a = pc + 2 * ((feLabs ls1).length : Int)
  simpa [kAa, st0] using this

end PinFetchPa
end Weak
