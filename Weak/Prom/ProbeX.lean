/-
Weak/Prom: **the G5 / Table-S rows the phase-1 pipelines could not run** (S0 exit, (E3) (b)), as extended programs
(`Weak/Prom/RefX.lean`'s `XI`), each with its INDEPENDENT TEXT VERDICT (quoted at the probe).  Family `G5x`.
Run by `ProbeXRun.lean` on the extended reference (`RefX.refOutcomesX`) and on machine v2 through the Sail model
(`MachSailX`); the label level has no form for these instructions (`na`).

Locations as everywhere (`X = 0x1000`, `Y = 0x2000` in `x8`, `x9`); the I/O address `IO = 0x3000000` lies in the
platform's I/O PMA region `[0x2000000, 0x12000000)` (model/sail-config-rv64d.json regions[1]: IOMemory, readable,
writable) and has no device (`MachCSL.devDecode` = none: not the CLINT, UARTs, PLIC or virtio windows).

**Table S correction (platform fact).**  Table S §19.3 gives G5-MIS1 and G5-MIS2 the verdict ALLOWED from
rvwmo.adoc:92–98 alone.  This platform's RAM PMA has a misaligned atomicity granule of 16 bytes (regions[2]
`misaligned_atomicity_granule_size_exp = 4`), and priv_machine.adoc:3094–3098 makes every base-ISA load and store
whose bytes "lie within the same misaligned atomicity granule … give rise to only one memory operation for the
purposes of RVWMO--i.e., it will execute atomically".  Both probes' stores lie inside `[x, x+16)`, so on this
platform their designated outcomes are FORBIDDEN; the decomposition freedom applies to accesses that cross a
granule (priv_machine.adoc:3103–3105 "not guaranteed to be atomic"), probed by MIS3–MIS5.
-/
import Weak.Prom.ProbeGen
import Weak.Prom.RefX

namespace Weak.Prom.Probe

open Weak.Prom Weak.Prom.Ref Weak.Prom.Ref.Lit Weak.Prom.RefX

/-- An extended probe: name, test, observables, text verdict `(cond, ALLOWED?)` (or none: compare only), and the
quote it rests on. -/
structure XProbe where
  name : String
  T : XTest
  obs : List OKey
  verdict : Option (OC × Bool)
  quote : String

def ioAddr : Nat := 0x3000000

def ioRegion : IoRegion := ⟨0x2000000, 0x12000000, false, 0⟩

def xi (l : List Instr) : List XI := l.map XI.i

def regs2 : List (List (Nat × Nat)) := [regsStd, regsStd]

/-- 64 bytes of `1` at `a`. -/
def ones64 (a : Nat) : List (Nat × Nat) := (List.range 64).map (fun k => (a + k, 1))

def g5xProbes : List XProbe :=
  [ -- misaligned, inside the 16-byte granule: one memory operation on this platform
    ⟨"MIS1", ⟨[xi [li 5 (two64 - 1)] ++ [.stM 4 5 rX 1], [.ldM 2 false 10 rX 2]], regs2, [], []⟩,
      [.reg 1 10], some (r 1 10 0xff, false),
      "priv_machine.adoc:3094-3098 (MAG16: one memory operation); Table S G5-MIS1 ALLOWED corrected"⟩,
    ⟨"MIS2", ⟨[xi [li 5 (two64 - 1)] ++ [.stM 4 5 rX 2], [.ldM 2 false 10 rX 4] ++ xi [fRR] ++ [.ldM 2 false 11 rX 2]],
      regs2, [], []⟩, [.reg 1 10, .reg 1 11], some (ands [r 1 10 0xffff, r 1 11 0], false),
      "priv_machine.adoc:3094-3098 (MAG16); Table S G5-MIS2 ALLOWED corrected"⟩,
    -- misaligned, crossing the granule: decomposable, components unordered in po
    ⟨"MIS3", ⟨[xi [li 5 (two64 - 1)] ++ [.stM 4 5 rX 14],
              [.ldM 2 false 10 rX 16] ++ xi [fRR] ++ [.ldM 2 false 11 rX 14]], regs2, [], []⟩,
      [.reg 1 10, .reg 1 11], some (ands [r 1 10 0xffff, r 1 11 0], true),
      "rvwmo.adoc:92-98 (any granularity; components not ordered by po); priv_machine.adoc:3103-3105"⟩,
    ⟨"MIS4", ⟨[xi [li 5 (two64 - 1)] ++ [.stM 4 5 rX 14], [.ldM 2 false 10 rX 14]], regs2, [], []⟩,
      [.reg 1 10], some (r 1 10 0xff, true),
      "rvwmo.adoc:92-93 (any granularity; RV-U11 byte by byte); priv_machine.adoc:3103-3105"⟩,
    ⟨"MIS5", ⟨[xi [li 5 (two64 - 1), sw 5 rX 16, fWW, sw 5 rX 12], [.ldM 4 false 10 rX 14]], regs2, [], []⟩,
      [.reg 1 10], some (r 1 10 0xffff, true),
      "rvwmo.adoc:92-98: a crossing load's components read at different points"⟩,
    -- cbo.zero: may or may not update the block atomically
    ⟨"CMO-TEAR", ⟨[[.cboZero rX], xi [.load 1 false 10 rX 0, fRR, .load 1 false 11 rX 63]], regs2, ones64 X, []⟩,
      [.reg 1 10, .reg 1 11], some (ands [r 1 10 0, r 1 11 1], true),
      "cmo.adoc:137-138 'may or may not update the entire set of bytes atomically with a single store operation'"⟩,
    ⟨"CMO-TEAR2", ⟨[[.cboZero rX], xi [.load 1 false 10 rX 63, fRR, .load 1 false 11 rX 0]], regs2, ones64 X, []⟩,
      [.reg 1 10, .reg 1 11], some (ands [r 1 10 0, r 1 11 1], true),
      "cmo.adoc:137-138 (the converse order)"⟩,
    -- Zicbom: the invalidate clause of the load value axiom
    ⟨"CMO-INV", ⟨[xi [li 5 1, sw 5 rX, fRWRW] ++ [.cbo .inval rX] ++ xi [lw 10 rX]], [regsStd], [], []⟩,
      [.reg 0 10], some (r 0 10 0, true),
      "cmo.adoc:259-268 bullet 1: no clean/flush precedes i: the initial value or any store preceding i"⟩,
    ⟨"CMO-CLEANINV", ⟨[xi [li 5 1, sw 5 rX, fRWRW] ++ [.cbo .clean rX, .cbo .inval rX] ++ xi [lw 10 rX]], [regsStd], [], []⟩,
      [.reg 0 10], some (r 0 10 0, false),
      "cmo.adoc:271-274 bullet 3: a store precedes the clean: only the latest store before the clean, or later ones"⟩,
    ⟨"CMO-FLUSHINV", ⟨[xi [li 5 1, sw 5 rX, fRWRW] ++ [.cbo .flush rX] ++ xi [lw 10 rX]], [regsStd], [], []⟩,
      [.reg 0 10], some (r 0 10 0, false),
      "cmo.adoc:116-126 'a flush operation atomically performs a clean operation followed by an invalidate operation' + bullet 3"⟩,
    ⟨"CMO-PPO", ⟨[xi [li 5 1, sw 5 rX] ++ [.cbo .flush rX] ++ xi [lw 10 rX], xi [li 5 2, sw 5 rX]], regs2, [], []⟩,
      [.reg 0 10, .mem X 4], none, "cmo.adoc:228-235 (compare only: the flush is ordered before the overlapping load)"⟩,
    -- amocas
    ⟨"ZC-WB", ⟨[xi [li 10 1, li 11 5] ++ [.amocas 4 false false 10 11 rX], xi [lw 12 rX]], regs2, [], []⟩,
      [.reg 0 10, .reg 1 12, .mem X 4], none,
      "zacas.adoc:159-161 (compare only: no RAM-observable outcome of the write-back, Table S ZC-5)"⟩,
    ⟨"ZC-WB2", ⟨[xi [li 10 1, li 11 5] ++ [.amocas 4 false false 10 11 rX], xi [lrW 12 rX, li 5 2, scW 13 5 rX]],
      regs2, [], []⟩, [.reg 0 10, .reg 1 12, .reg 1 13, .mem X 4], none,
      "zacas.adoc:159-161 (compare only, an LR/SC observer)"⟩,
    ⟨"ZC-PPO", ⟨[xi [li 10 5] ++ [.amocas 4 false false 10 11 rX] ++ xi [fWW, li 5 1, sw 5 rY],
                xi [lw 12 rY, fence true false false true, li 5 2, sw 5 rX]], regs2, [], []⟩,
      [.reg 0 10, .reg 1 12], some (ands [r 1 12 1, r 0 10 2], false),
      "zacas.adoc NOTE 'treated as an AMO for the purposes of the RVWMO PPO rules': fence w,w orders the failed amocas"⟩,
    ⟨"ZC-AQRL", ⟨[xi [li 5 1, sw 5 rX, li 10 7, li 11 1] ++ [.amocas 4 false true 10 11 rY],
                 xi [lw 12 rY, fRR, lw 13 rX]], regs2, [], []⟩,
      [.reg 0 10, .reg 1 12, .reg 1 13], some (ands [r 1 12 0, r 1 13 0], true),
      "zacas.adoc:152-154 'when not successful … does not have release semantics, regardless of rl'"⟩,
    -- I/O with no device
    ⟨"NODEV-R", ⟨[xi [li 5 ioAddr, lw 10 5, sw 10 rX]], [regsStd], [], [ioRegion]⟩,
      [.reg 0 10, .mem X 4], some (r 0 10 1, true),
      "mm-explanatory.adoc:1139-1140 (no load value axiom for I/O); priv_machine.adoc:2924-2928 (I/O attributes)"⟩,
    ⟨"NODEV-W", ⟨[xi [li 5 ioAddr, li 6 1, sw 6 5, lw 10 5]], [regsStd], [], [ioRegion]⟩,
      [.reg 0 10], some (r 0 10 0, true),
      "mm-explanatory.adoc:1139-1140: an I/O read need not return the value written"⟩ ]

/-- The probe names of a family (for `#tableCx_check`). -/
def probeNames (f : String) : List String :=
  if f = "G5x" then g5xProbes.map (·.name) else (family f).map (·.name)

end Weak.Prom.Probe
