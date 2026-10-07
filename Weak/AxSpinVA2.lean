/-
Weak: **the spinlock plan, PHASE 5 item (4), part 2** — the CONCRETE certificate of `AxSpinVA`'s
chain at a real Sv39 S-mode state, for diverted PCs, cross-checked against real `riscvStep` runs.

Rocq: `iris/AxSpinVA2.v` @ xxvzwolszwmp.

## What this file proves

STATE (as Rocq).  `AxSmodeProbe`'s supervisor hart (Sv39 over the 3-level table root 0x80010000
→ L1 0x80011000 → L0 0x80012000, cold TLB, SIE = 0, medeleg = 0xB109), plus stvec = 0x80000040
(direct), L0[2] = 0 (an UNMAPPED page 0x80002000), L0[3] = a valid R/W leaf WITHOUT X
(0x80003000).  The image `vaImg` is the whole memory.  The PINNED instruction is the probe's
`ld x1, 8(x2)` at 0x80000000.

§1 THE COMPUTED CHAINS (`fstep`, both ticks, all pin answers, `decide +kernel`; e2 = root slot
0x80010010, e1 = L1[0] 0x80011000, e0(j) = L0[j] 0x80012000 + 8j, eD(a) = the 8-byte data read
at a, eF(a) = the hart stops at a 4-byte fetch at a with NO image bytes (`ekey.ENf`, Q13); under
Stage C a fetch that HAS image bytes is no key — it is the pinned administrative step answered
from the image, see deviation 1):

    pinned 0x80000000            [e2; e1; e0(0); e2; e1; e0(1); eD 0x80001008]
    mapped text 0x80000004       [e2; e1; e0(0); eF 0x80000008]  (fuel 3)  diff @3
    mapped X data 0x80001000     [e2; e1; e0(1); eF 0x80001000]            diff @2
    misaligned 0x80000001        [e2; e1; e0(0); eF stvec]                 diff @3
    non-canonical 0x80_0000_0000 [e2; e1; e0(0); eF stvec]                 diff @3
    unmapped 0x80002000          [e2; e1; e0(2); e2; e1; e0(0); eF stvec]  diff @2
    mapped NON-X 0x80003000      [e2; e1; e0(3); e2; e1; e0(0); eF stvec]  diff @2

The misaligned / non-canonical arms still emit NO memory event in the faulting step and land at
stvec, whose fetch has no image bytes.  WARM TLB (after the pinned `ld`): pinned
`[eD 0x80001008]`; mapped 0x80000004 `[eF 0x80000008]` (fuel 3: two `c.nop`s, then a fetch past
the image) — diff @0 (stuck AT the boundary); Lean-only: unmapped 0x80002000
`[e2; e1; e0(2); eF stvec]` — diff @0.

§2 CROSS-CHECK: each chain's NON-`eF` prefix is the prefix of the (width, pa) NON-FETCH read list
of the REAL run (`mtr` of `riscvStep false`, then of the next `riscvStep false` from the
post-state).

§3 STUCK CERTIFICATES against the pinned ROW (`pinRow` = the pinned chain's items): the diverted
hart fits the row on the common prefix (`*Fits`) and at the first differing index `j` every node
it reaches through `j` image-answered reads is row-stuck along `fetchPin vaImg`-pinned runs
(`*Stuck`, from `AxSpinVA.rowStuckOfChain`).  `warmStuckBoundary` and the Lean-only
`AxSpinVA2.warmUnmappedStuckBoundary`: the j = 0 case, fully closed.  `pinFits`: the pinned
chain fits its own row everywhere.

## Deviations from Rocq

1. O2 STAGE C (fetches are not graph events; `AxSpinVA` deviation 1).  Rocq's chains contained the
   4-byte fetch key `eF a` for EVERY fetch.  In Lean a fetch with image bytes is an
   administrative step pinned to the image (`FEC.fcIf`), so it is no chain key and no row item;
   only a fetch with NO image bytes is a key — the chain's END `eF a := ekey.ENf (a, 4)` (Q13,
   provisional; `FEC.fcNf`): along image-pinned runs such a hart has no step at all, and no row
   item fits `eF`.  The pinned chain therefore continues to the `ld`'s data walk and data read
   (7 keys, `len = 8` everywhere; Rocq `len = 4`/`8`).  Consequences:
   - `pinRow` has 7 items (Rocq 4); `pinWrow` is `[rdItem false 0x80001008 8]` (Rocq the fetch).
   - the text / misaligned / non-canonical / warm-text verdicts were Rocq fetch-ADDRESS
     mismatches (`F 0x80000004` / `F stvec` vs the row's `F 0x80000000`).  In Lean those harts
     reach the row's index 3 (resp. 0) and stop at a fetch past the image (`eF 0x80000008` /
     `eF stvec`) where the row has the data walk's root read `e2` (resp. the data read):
     `textStuck`, `misalStuck`, `noncanonStuck` (at index 3, as Rocq) and `warmStuckBoundary`
     (at index 0, as Rocq) are restored with Rocq's statements (modulo deviation 2/3 and Q12's
     pin).  The text hart needs ONE MORE boundary (fuel 3; Rocq 2): its first fetch is no key,
     the stuck fetch is after two `c.nop`s (`chText`, `chWarmText` at fuel 3; their `eF` is at
     `sPc + 8`, Rocq `s_pc + 4`).
   - the data / unmapped / non-X / misaligned / non-canonical chains end with `eF` at the address
     Rocq's `eF` had (Rocq: the fetch read; Lean: the fetch past the image).
   - `xc*` compare only the non-`eF` prefix (`real2` drops fetch events, `akTag = 1`, as the
     chain drops pinned fetches); `xcWarmText` states that the real warm-text run has NO
     non-fetch read (Rocq: its first read is the fetch).  `keyWp`/`itemOf` give `eF a` the
     fetch's `(4, a)` / `rdItem false a 4`, as Rocq.
   - Lean-only, kept: `AxSpinVA2.chWarmUnmapped`, `AxSpinVA2.xcWarmUnmapped`,
     `AxSpinVA2.warmUnmappedStuckBoundary` (warm TLB, PC := 0x80002000: the data walk's root
     read at index 0 vs the row's data read).
   - `rowStuckR` takes the pin `WeakAxRealize.fetchPin vaImg` (Q12); Rocq's `T img0` parameters
     of the stuck lemmas are gone.
2. THE PINS: `regs_agree seip_reg` ↦ `regsAgree AxRunClose.pinReg` (`AxRunClose` deviation 1).
3. TYPES: PCs/addresses `Z` ↦ `Nat` (keys keep `Int`, as `paZ`); `list_to_map` ↦
   `AxSmodeProbe.memOfList`; `register_set` ↦ `RegFile.set`; `mstate`/`sregs` ↦ `ExecSt`/`regs`;
   `set_reg` ↦ `ExecSt.setReg`; `img_of` ↦ `imgOf`; `Interface.Ret tt` ↦ `.pure ()`;
   `option_map` ↦ `Option.map`; `forallb` over `take j (zip Ks row)` ↦ `List.all`;
   `vm_compute; reflexivity` ↦ `decide +kernel`.  `stuckAt` is stated with explicit
   `(cpu rs ib p')` binders.

**Rocq → Lean name map.**  `va_stvec` `vaStvec`, `pte_nox` `pteNox`, `va_bytes` `vaBytes`,
`va_mem` `vaMem`, `va_regs` `vaRegs`, `va_at` `vaAt`, `va_img` `vaImg`, `va_chain` `vaChain`,
`va_wt` `vaWt`, `va_wchain` `vaWchain`, `e2`/`e1`/`e0` same, `pin_chain` `pinChain`,
`ch_pinned`/`ch_text`/`ch_data`/`ch_misal`/`ch_noncanon`/`ch_unmapped`/`ch_nox`/`ch_warm_pinned`/
`ch_warm_text` `chPinned`/…/`chWarmText`, `key_wp` `keyWp`, `mtr_evs` `mtrEvs`, `real2` `real2`,
`xc_*` `xc*`, `misal_step_no_read` `misalStepNoRead`, `noncanon_step_no_read`
`noncanonStepNoRead`, `misal_lands_stvec` `misalLandsStvec`, `rd_item` `rdItem`, `item_of`
`itemOf`, `pin_row` `pinRow`, `fits_upto` `fitsUpto`, `stuck_at` `stuckAt`, `pin_fits` `pinFits`,
`eF` `eF`, `text_fits` `textFits`, `text_stuck` `textStuck`, `data_fits` `dataFits`,
`data_stuck` `dataStuck`, `misal_fits` `misalFits`, `misal_stuck` `misalStuck`,
`noncanon_stuck` `noncanonStuck`, `unmapped_fits` `unmappedFits`, `unmapped_stuck`
`unmappedStuck`, `nox_stuck` `noxStuck`, `pin_wrow` `pinWrow`, `warm_stuck_boundary`
`warmStuckBoundary`, `warm_pin_fits` `warmPinFits`.  Lean-only (`AxSpinVA2.*`):
`eD`, `chWarmUnmapped`, `xcWarmUnmapped`, `warmUnmappedStuckBoundary`.

**Dropped:** nothing (no Rocq file imports AxSpinVA2).  Rocq 57 definitions/lemmas; Lean 57 +
4 Lean-only.  **Not ported:** the `Print Assumptions` block (the lint's axiom check covers it).
-/
import Weak.AxSpinVA
import Weak.AxSmodeProbe
import Weak.AxSpineOk

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D
open Wlabel

/-! # 0. The state -/

def vaStvec : Nat := 0x80000040
/-- a valid R/W leaf WITHOUT X (D A W R V) -/
def pteNox (ppn : Nat) : Nat := (ppn <<< 10) ||| 0xC7
def vaBytes : List (Nat × Nat) :=
  sBytes ++ AxSmodeProbe.dwBytes (AxSmodeProbe.sL0 * 4096 + 2 * 8) 0 ++
    AxSmodeProbe.dwBytes (AxSmodeProbe.sL0 * 4096 + 3 * 8) (pteNox 0x80003)
def vaMem : BMap := AxSmodeProbe.memOfList vaBytes
def vaRegs (pc : Nat) : RegFile := (sRegs pc).set .stvec (AxEpiProbe.w64 vaStvec)
def vaAt (pc : Nat) : ExecSt := ⟨vaRegs pc, vaMem, testDevs⟩
def vaImg : Image := imgOf (vaAt sPc)

noncomputable def vaChain (fuel len : Nat) (pc : Nat) : Option (List ekey) :=
  fstep vaImg fuel len (vaAt pc)

/-- the warm-TLB boundary: after the pinned `ld`, PC := v -/
noncomputable def vaWt (v : Nat) : ExecSt :=
  match mfin (riscvStep false) (vaAt sPc) with
  | some t => (t.setReg .PC (AxEpiProbe.w64 v)).setReg .nextPC (AxEpiProbe.w64 v)
  | none => vaAt sPc

noncomputable def vaWchain (fuel len : Nat) (v : Nat) : Option (List ekey) :=
  fstep vaImg fuel len (vaWt v)

/-! # 1. The chains -/

def e2 : ekey := .ERd (false, ((AxSmodeProbe.sRoot * 4096 + 16 : Nat) : Int), 8)
def e1 : ekey := .ERd (false, ((AxSmodeProbe.sL1 * 4096 : Nat) : Int), 8)
def e0 (j : Nat) : ekey := .ERd (false, ((AxSmodeProbe.sL0 * 4096 + 8 * j : Nat) : Int), 8)
/-- the hart stops at a 4-byte FETCH at `a` that has no image bytes (Q13: Rocq the fetch read
key `ERd (false, a, 4)`) -/
def eF (a : Nat) : ekey := .ENf ((a : Int), 4)
/-- (Lean-only) the 8-byte data read at `a` -/
def AxSpinVA2.eD (a : Nat) : ekey := .ERd (false, (a : Int), 8)

def pinChain : List ekey :=
  [e2, e1, e0 0, e2, e1, e0 1, AxSpinVA2.eD (AxSmodeProbe.sSp + 8)]

theorem chPinned : vaChain 2 8 sPc = some pinChain := by decide +kernel
theorem chText : vaChain 3 8 (sPc + 4) = some [e2, e1, e0 0, eF (sPc + 8)] := by decide +kernel
theorem chData : vaChain 2 8 0x80001000 = some [e2, e1, e0 1, eF 0x80001000] := by decide +kernel
theorem chMisal : vaChain 2 8 (sPc + 1) = some [e2, e1, e0 0, eF vaStvec] := by decide +kernel
theorem chNoncanon : vaChain 2 8 0x8000000000 = some [e2, e1, e0 0, eF vaStvec] := by
  decide +kernel
theorem chUnmapped :
    vaChain 2 8 0x80002000 = some [e2, e1, e0 2, e2, e1, e0 0, eF vaStvec] := by
  decide +kernel
theorem chNox : vaChain 2 8 0x80003000 = some [e2, e1, e0 3, e2, e1, e0 0, eF vaStvec] := by
  decide +kernel
theorem chWarmPinned : vaWchain 2 1 sPc = some [AxSpinVA2.eD (AxSmodeProbe.sSp + 8)] := by
  decide +kernel
/-- (deviation 1) the warm text hart: two `c.nop`s, then a fetch past the image -/
theorem chWarmText : vaWchain 3 1 (sPc + 4) = some [eF (sPc + 8)] := by decide +kernel
/-- (Lean-only) warm TLB, PC := the unmapped page: the data walk at the boundary -/
theorem AxSpinVA2.chWarmUnmapped :
    vaWchain 2 8 0x80002000 = some [e2, e1, e0 2, eF vaStvec] := by
  decide +kernel


/-! # 2. Cross-check against the real run -/

def keyWp (e : ekey) : Int × Int :=
  match e with
  | .ERd (_, a, n) | .EWr (_, a, n) => ((n : Int), a)
  | .EFn _ => (0, 0)
  | .ENf (a, n) => ((n : Int), a)

def mtrEvs (r : (List AxSmodeProbe.mev × Nat) ⊕ (Nat × List AxSmodeProbe.mev)) :
    List AxSmodeProbe.mev :=
  match r with
  | .inl (l, _) => l
  | .inr (_, l) => l

/-- the (width, pa) NON-FETCH reads of the REAL run: this step, then the next one from its
post-state (deviation 1: fetch events, `akTag = 1`, are dropped) -/
noncomputable def real2 (t : ExecSt) : List (Int × Int) :=
  let ev1 := mtrEvs (mtr (riscvStep false) t [] 0)
  let ev2 := match mfin (riscvStep false) t with
    | some t' => mtrEvs (mtr (riscvStep false) t' [] 0)
    | none => []
  ((ev1 ++ ev2).filter fun e => e.2.1 != 1).map fun e => ((e.2.2.1 : Int), (e.2.2.2 : Int))

theorem xcPinned : pinChain.map keyWp = (real2 (vaAt sPc)).take 7 := by decide +kernel
theorem xcText : [e2, e1, e0 0].map keyWp = (real2 (vaAt (sPc + 4))).take 3 := by decide +kernel
theorem xcData : [e2, e1, e0 1].map keyWp = (real2 (vaAt 0x80001000)).take 3 := by decide +kernel
theorem xcMisal : [e2, e1, e0 0].map keyWp = (real2 (vaAt (sPc + 1))).take 3 := by decide +kernel
theorem xcNoncanon : [e2, e1, e0 0].map keyWp = (real2 (vaAt 0x8000000000)).take 3 := by
  decide +kernel
theorem xcUnmapped :
    [e2, e1, e0 2, e2, e1, e0 0].map keyWp = (real2 (vaAt 0x80002000)).take 6 := by
  decide +kernel
theorem xcNox : [e2, e1, e0 3, e2, e1, e0 0].map keyWp = (real2 (vaAt 0x80003000)).take 6 := by
  decide +kernel
/-- (deviation 1) the real warm text run has no non-fetch read -/
theorem xcWarmText : real2 (vaWt (sPc + 4)) = [] := by decide +kernel
/-- (Lean-only) -/
theorem AxSpinVA2.xcWarmUnmapped :
    [e2, e1, e0 2].map keyWp = (real2 (vaWt 0x80002000)).take 3 := by decide +kernel

/-- the faulting step of the misaligned / non-canonical PCs is LABEL-FREE: the real first step
reads nothing -/
theorem misalStepNoRead : mtrEvs (mtr (riscvStep false) (vaAt (sPc + 1)) [] 0) = [] := by
  decide +kernel
theorem noncanonStepNoRead : mtrEvs (mtr (riscvStep false) (vaAt 0x8000000000) [] 0) = [] := by
  decide +kernel
/-- ... and lands at stvec -/
theorem misalLandsStvec :
    (mfin (riscvStep false) (vaAt (sPc + 1))).map AxEpiProbe.pcOf = some vaStvec := by
  decide +kernel

/-! # 3. Stuck certificates against the pinned row -/

def rdItem (aq : Bool) (a : Int) (n : Nat) : Lbl :=
  .LLoad aq a (List.replicate n 0) (List.replicate n 0#8)

def itemOf (e : ekey) : Lbl :=
  match e with
  | .ERd (aq, a, n) => rdItem aq a n
  | .EWr (rl, a, n) => .LStore rl a (List.replicate n 0#8) .WCplain
  | .EFn (pr, pw, sr, sw) => .LFence pr pw sr sw
  | .ENf (a, n) => rdItem false a n

def pinRow : List Lbl := pinChain.map itemOf

/-- prefix fit, as a boolean -/
def fitsUpto (Ks : List ekey) (row : List Lbl) (j : Nat) : Bool :=
  ((Ks.zip row).take j).all fun p => keyFitsb p.1 p.2

theorem stuckAt (fuel len : Nat) (t : ExecSt) (Ks : List ekey) (row : List Lbl) (j : Nat)
    (e : ekey) (lb : Lbl) (cpu : CPU) (rs : RegFile) (ib : Ibch) (p' : Pexv6) :
    fstep vaImg fuel len t = some Ks → regsAgree AxRunClose.pinReg rs t.regs →
    Ks[j]? = some e → row[j]? = some lb → keyFitsb e lb = false →
    ireach vaImg (.PHart cpu (.pure ()) rs none ib) j p' →
    rowStuckR (WeakAxRealize.fetchPin vaImg) row ⟨p', j⟩ := by
  intro Hf Hag He Hlb Hb Hr
  obtain ⟨Hlt, _⟩ := List.getElem?_eq_some_iff.mp Hlb
  exact rowStuckOfChain vaImg Ks _ j p' e j row
    (hthrBoundary vaImg fuel Ks t cpu rs ib (fstepSound vaImg fuel len t Ks Hf) Hag) Hr He
    (rowRejectsKey1 row j e lb Hlb Hb) Hlt

theorem pinFits : fitsUpto pinChain pinRow 7 = true := by decide +kernel

theorem textFits : fitsUpto [e2, e1, e0 0, eF (sPc + 8)] pinRow 3 = true := by decide +kernel
theorem textStuck (cpu : CPU) (ib : Ibch) (p' : Pexv6) :
    ireach vaImg (.PHart cpu (.pure ()) (vaRegs (sPc + 4)) none ib) 3 p' →
    rowStuckR (WeakAxRealize.fetchPin vaImg) pinRow ⟨p', 3⟩ :=
  stuckAt 3 8 (vaAt (sPc + 4)) [e2, e1, e0 0, eF (sPc + 8)] pinRow 3 (eF (sPc + 8))
    (rdItem false ((AxSmodeProbe.sRoot * 4096 + 16 : Nat) : Int) 8) cpu _ ib p'
    chText (regsAgreeRefl _ _) rfl (by decide +kernel) (by decide +kernel)

theorem dataFits : fitsUpto [e2, e1, e0 1, eF 0x80001000] pinRow 2 = true := by decide +kernel
theorem dataStuck (cpu : CPU) (ib : Ibch) (p' : Pexv6) :
    ireach vaImg (.PHart cpu (.pure ()) (vaRegs 0x80001000) none ib) 2 p' →
    rowStuckR (WeakAxRealize.fetchPin vaImg) pinRow ⟨p', 2⟩ :=
  stuckAt 2 8 (vaAt 0x80001000) [e2, e1, e0 1, eF 0x80001000] pinRow 2 (e0 1)
    (rdItem false ((AxSmodeProbe.sL0 * 4096 : Nat) : Int) 8) cpu _ ib p'
    chData (regsAgreeRefl _ _) rfl (by decide +kernel) (by decide +kernel)

theorem misalFits : fitsUpto [e2, e1, e0 0, eF vaStvec] pinRow 3 = true := by decide +kernel
theorem misalStuck (cpu : CPU) (ib : Ibch) (p' : Pexv6) :
    ireach vaImg (.PHart cpu (.pure ()) (vaRegs (sPc + 1)) none ib) 3 p' →
    rowStuckR (WeakAxRealize.fetchPin vaImg) pinRow ⟨p', 3⟩ :=
  stuckAt 2 8 (vaAt (sPc + 1)) [e2, e1, e0 0, eF vaStvec] pinRow 3 (eF vaStvec)
    (rdItem false ((AxSmodeProbe.sRoot * 4096 + 16 : Nat) : Int) 8) cpu _ ib p'
    chMisal (regsAgreeRefl _ _) rfl (by decide +kernel) (by decide +kernel)

theorem noncanonStuck (cpu : CPU) (ib : Ibch) (p' : Pexv6) :
    ireach vaImg (.PHart cpu (.pure ()) (vaRegs 0x8000000000) none ib) 3 p' →
    rowStuckR (WeakAxRealize.fetchPin vaImg) pinRow ⟨p', 3⟩ :=
  stuckAt 2 8 (vaAt 0x8000000000) [e2, e1, e0 0, eF vaStvec] pinRow 3 (eF vaStvec)
    (rdItem false ((AxSmodeProbe.sRoot * 4096 + 16 : Nat) : Int) 8) cpu _ ib p'
    chNoncanon (regsAgreeRefl _ _) rfl (by decide +kernel) (by decide +kernel)

theorem unmappedFits : fitsUpto [e2, e1, e0 2, e2, e1, e0 0, eF vaStvec] pinRow 2 = true := by decide +kernel
theorem unmappedStuck (cpu : CPU) (ib : Ibch) (p' : Pexv6) :
    ireach vaImg (.PHart cpu (.pure ()) (vaRegs 0x80002000) none ib) 2 p' →
    rowStuckR (WeakAxRealize.fetchPin vaImg) pinRow ⟨p', 2⟩ :=
  stuckAt 2 8 (vaAt 0x80002000) [e2, e1, e0 2, e2, e1, e0 0, eF vaStvec] pinRow 2 (e0 2)
    (rdItem false ((AxSmodeProbe.sL0 * 4096 : Nat) : Int) 8) cpu _ ib p'
    chUnmapped (regsAgreeRefl _ _) rfl (by decide +kernel) (by decide +kernel)

theorem noxStuck (cpu : CPU) (ib : Ibch) (p' : Pexv6) :
    ireach vaImg (.PHart cpu (.pure ()) (vaRegs 0x80003000) none ib) 2 p' →
    rowStuckR (WeakAxRealize.fetchPin vaImg) pinRow ⟨p', 2⟩ :=
  stuckAt 2 8 (vaAt 0x80003000) [e2, e1, e0 3, e2, e1, e0 0, eF vaStvec] pinRow 2 (e0 3)
    (rdItem false ((AxSmodeProbe.sL0 * 4096 : Nat) : Int) 8) cpu _ ib p'
    chNox (regsAgreeRefl _ _) rfl (by decide +kernel) (by decide +kernel)

/-- the warm row: the pinned warm hart's data read (deviation 1; Rocq: its fetch) -/
def pinWrow : List Lbl := [rdItem false ((AxSmodeProbe.sSp + 8 : Nat) : Int) 8]

/-- WARM TLB: the diverted hart is stuck AT THE BOUNDARY — fully closed (Q13: at the fetch of
0x80000008, past the image, after two `c.nop`s; Rocq at its fetch of s_pc + 4) -/
theorem warmStuckBoundary (cpu : CPU) (ib : Ibch) :
    rowStuckR (WeakAxRealize.fetchPin vaImg) pinWrow
      ⟨.PHart cpu (.pure ()) (vaWt (sPc + 4)).regs none ib, 0⟩ :=
  stuckAt 3 1 (vaWt (sPc + 4)) [eF (sPc + 8)] pinWrow 0 (eF (sPc + 8))
    (rdItem false ((AxSmodeProbe.sSp + 8 : Nat) : Int) 8) cpu _ ib _
    chWarmText (regsAgreeRefl _ _) rfl rfl (by decide +kernel) (.irRefl _)

/-- (Lean-only, deviation 1) WARM TLB, PC := the unmapped page: the diverted hart is stuck AT
THE BOUNDARY — fully closed -/
theorem AxSpinVA2.warmUnmappedStuckBoundary (cpu : CPU) (ib : Ibch) :
    rowStuckR (WeakAxRealize.fetchPin vaImg) pinWrow
      ⟨.PHart cpu (.pure ()) (vaWt 0x80002000).regs none ib, 0⟩ :=
  stuckAt 2 8 (vaWt 0x80002000) [e2, e1, e0 2, eF vaStvec] pinWrow 0 e2
    (rdItem false ((AxSmodeProbe.sSp + 8 : Nat) : Int) 8) cpu _ ib _
    AxSpinVA2.chWarmUnmapped (regsAgreeRefl _ _) rfl rfl (by decide +kernel) (.irRefl _)

/-- ... and the pinned warm hart is NOT rejected there -/
theorem warmPinFits : fitsUpto [AxSpinVA2.eD (AxSmodeProbe.sSp + 8)] pinWrow 1 = true := by
  decide +kernel

end Weak
