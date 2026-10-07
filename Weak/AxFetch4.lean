/-
Weak: **track F, the AxSL instruction bridge — PART E** (`AxFetch4`): §3, THE DEMONSTRATION —
the two-event `ld8`/`sd8` opax run on a HAND-BUILT residual monad.

Rocq: `iris/AxFetch.v` @ xxvzwolszwmp, lines 3590–3818 (§3, `Module AxFetchDemo`).  Imports
`AxFetch1` (part A: the row shapes `afLd8RowShape`/`afSd8RowShape`, the generic single-node
bridges `afAstepFetchOfMemread`/`afAreadStepOfMemread`/`afAstepWriteOfMemwrite`).

## What this file proves

`AxOpsem.OpaxWit`'s recipe at the `ld8`/`sd8` SHAPE: a fetch (4 bytes at `fPa`) whose
continuation is a SINGLE 8-byte data node (at `dPa ≠ fPa`).  Not built from the real
`execute (LOAD/STORE …)` term: it shows the row shape (§1) and the generic bridges (§2) compose
into the whole opax run once a residual monad of the right shape is in hand.  `ldRun`: fetch,
then the data read, for every fetched word and every read answer; `sdRun`: fetch, then the data
write.

## Deviations from Rocq

1. O2 STAGE C (`notes/weak-port-o2-stageC.md`, `AxFetch1` header): the fetch is an ADMIN step
   (`AStepAdmin` at `LIFetch baseF (tagVals vf)`) that KEEPS the row position.  So the rows have
   ONE item, the data event (Rocq: `[fetch; data]`), and are re-indexed: the fetch goes `0 → 0`
   (Rocq `0 → 1`), the data step `0 → 1` (Rocq `1 → 2`), the runs end at position 1 (Rocq 2).
   The rows' fetch-value argument `wf` and its `length wf = 4` premises are gone (`ldRow v`,
   `sdRow`, `ldRowShape v`, `sdRowShape`, `ldFetch cpu rs v vf`, `ldAread cpu rs v`,
   `ldRun cpu rs v vf vd`, `sdFetch cpu rs vf`, `sdAstepWrite cpu rs`, `sdRun cpu rs vf`); the
   oracle parameters `T`/`img` of `astep_prog`/`astep_any` are gone (so `sdAstepWrite` loses its
   `img` binder).  The fetch label is `LIFetch baseF (tagVals vf)` (Rocq
   `WeakPromise.LLoad false false base_f (tag_vals vf) []`).
2. THE FETCH REQUEST's access kind is `AK_ifetch ()` (Rocq `ak_plain`): Lean's fetch bridge
   `afAstepFetchOfMemread` takes `akIfetch = true` (the i-cache read class
   `WeakFetchEff.wakIfetch`; `AxFetch1` header).  `ldAccessKindFreq` states it.
3. Rocq `init_regstate` ↦ an arbitrary register file `rs` (as `AxOpsem.OpaxWit`, its
   deviation 6); every hart state and lemma takes `rs`.  Rocq `dev0_state` ↦ `OpaxWit.wtD0`.
   `ib_none` ↦ `ibNone`; `z_pa 0x…` ↦ `BitVec.ofNat 64 0x…`; `dev_addr … = false` by
   `decide +kernel` (Rocq `vm_compute`).  The data word is `BitVec (8 * 8)` (Rocq `bv 64`; the
   same type, stated so that `wbytes 8` takes it without a cast); `sdVal` is `0`
   (Rocq `Z_to_bv 64 0`).  A request is a lean-sail `Mem_read_request`/`Mem_write_request`
   record (`va := none`, `translation := ()`, Rocq `ReadReq.make`/`WriteReq.make`).
4. NAMES: every name is declared in `namespace AxFetch.AxFetchDemo` (Rocq module path
   `AxFetch.AxFetchDemo`) — file-qualified, as the duplicated-name rule requires for `ak_plain`,
   `ld_m`, `ld_p0`, `ld_p1`, `ld_row`, `sd_m` (in `notes/weak-port-dupnames.json`) and applied to
   the whole demo.  The `Print Assumptions` commands are not ported.

**Rocq → Lean name map** (all under `AxFetch.AxFetchDemo.`).  `f_pa` `fPa`, `d_pa` `dPa`,
`f_pa_ram` `fPaRam`, `d_pa_ram` `dPaRam`, `ak_plain` `akPlain`, `ak_plain_class`
`akPlainClass`, `base_f` `baseF`, `base_d` `baseD`, `freq` `freq`, `dreq_ld` `dreqLd`, `ld_m2`
`ldM2`, `ld_m` `ldM`, `ld_p0`/`ld_p1`/`ld_p2` `ldP0`/`ldP1`/`ldP2`, `ld_row` `ldRow`,
`ld_row_shape` `ldRowShape`, `ld_access_kind_freq` `ldAccessKindFreq`, `ld_access_kind_dreq`
`ldAccessKindDreq`, `ld_fetch` `ldFetch`, `ld_aread` `ldAread`, `ld_run` `ldRun`, `sd_val`
`sdVal`, `dreq_sd` `dreqSd`, `sd_m2` `sdM2`, `sd_m` `sdM`, `sd_p0`/`sd_p1`/`sd_p2`
`sdP0`/`sdP1`/`sdP2`, `sd_row` `sdRow`, `sd_row_shape` `sdRowShape`, `sd_access_kind_dreq`
`sdAccessKindDreq`, `sd_fetch` `sdFetch`, `sd_astep_write` `sdAstepWrite`, `sd_run` `sdRun`.

**Dropped (O2 Stage C: no fetch oracle):** `ld_T` (the text range), `ld_img` (the fetch image),
`ld_fetch_answers` (the oracle's answer fact) — the `T`/`img` parameters they instantiate are
deleted; no weak file outside AxFetch.v uses them (AxLock3Race.v names `f_pa`/`d_pa` only in a
comment).  Counts: Rocq 38 declarations in lines 3590–3818; Lean 35 + 0 Lean-only.
-/
import Weak.AxFetch1

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D LeanRV64D.Functions
open Wlabel

namespace AxFetch.AxFetchDemo

def fPa : PAddr := BitVec.ofNat 64 0x80001000
def dPa : PAddr := BitVec.ofNat 64 0x80002000

theorem fPaRam : devAddr fPa = false := by decide +kernel
theorem dPaRam : devAddr dPa = false := by decide +kernel

def akPlain : AK := .AK_explicit ⟨.AV_plain, .AS_normal⟩

theorem akPlainClass : classify akPlain = ⟨false, false, false⟩ := rfl

def baseF : Int := paZ fPa
def baseD : Int := paZ dPa

/-! ### The LOAD shape -/

/-- The fetch request (deviation 2: access kind `AK_ifetch`). -/
def freq : Mem_read_request 4 64 Arch.pa Arch.translation Arch.arch_ak :=
  { access_kind := .AK_ifetch (), va := none, pa := fPa, translation := (), size := 4,
    tag := false }

def dreqLd : Mem_read_request 8 64 Arch.pa Arch.translation Arch.arch_ak :=
  { access_kind := akPlain, va := none, pa := dPa, translation := (), size := 8, tag := false }

def ldM2 : SailM Unit := .impure (.ok (.memRead 8 64 dreqLd)) (fun _ => .pure ())
def ldM : SailM Unit := .impure (.ok (.memRead 4 64 freq)) (fun _ => ldM2)

def ldP0 (cpu : CPU) (rs : RegFile) : Pexv6 := .PHart cpu ldM rs none ibNone
def ldP1 (cpu : CPU) (rs : RegFile) : Pexv6 := .PHart cpu ldM2 rs none ibNone
def ldP2 (cpu : CPU) (rs : RegFile) : Pexv6 := .PHart cpu (.pure ()) rs none ibNone

/-- The row (Stage C: the data item only). -/
def ldRow (v : BitVec (8 * 8)) : List Lbl :=
  [.LLoad false baseD [0, 0, 0, 0, 0, 0, 0, 0] (WeakInterpProj.wbytes 8 v)]

theorem ldRowShape (v : BitVec (8 * 8)) : afLd8RowShape (ldRow v) 0 baseD :=
  ⟨_, rfl, by simp [aident, afLd8DataIdent, wbytesLength]⟩

theorem ldAccessKindFreq : freq.access_kind = .AK_ifetch () := rfl
theorem ldAccessKindDreq : dreqLd.access_kind = akPlain := rfl

/-- The fetch step: an ADMIN step at position 0, landing at `ldP1` for every fetched word `vf`
(Stage C: the position is kept). -/
theorem ldFetch (cpu : CPU) (rs : RegFile) (v : BitVec (8 * 8)) (vf : List (BitVec 8)) :
    vf.length = 4 →
    AxOpsem.astepProg (ldRow v) ⟨ldP0 cpu rs, 0⟩ (LIFetch baseF (tagVals vf))
      ⟨ldP1 cpu rs, 0⟩ :=
  fun hvf =>
    afAstepFetchOfMemread (ldRow v) cpu 4 64 freq (fun _ => ldM2) rs ibNone OpaxWit.wtD0 0 vf
      fPaRam rfl hvf

/-- The data read: position 0 to 1, value free. -/
theorem ldAread (cpu : CPU) (rs : RegFile) (v : BitVec (8 * 8)) :
    areadStep (ldRow v) ⟨ldP1 cpu rs, 0⟩ (afLd8DataIdent baseD)
      (fun _ => ⟨.PHart cpu (.pure ()) rs none ibNone, 1⟩) := by
  obtain ⟨lbd, hrowd, hidd⟩ := ldRowShape v
  exact afAreadStepOfMemread (ldRow v) cpu 8 64 dreqLd (fun _ => .pure ()) rs ibNone
    OpaxWit.wtD0 0 lbd dPaRam rfl rfl hrowd hidd

/-- The full run: fetch then the data read, position 0 to 1 (Stage C), for every answer to
both memory events. -/
theorem ldRun (cpu : CPU) (rs : RegFile) (v : BitVec (8 * 8)) (vf vd : List (BitVec 8)) :
    vf.length = 4 → vd.length = 8 →
    nsteps (astepAny (ldRow v)) 2 ⟨ldP0 cpu rs, 0⟩ ⟨ldP2 cpu rs, 1⟩ := by
  intro hvf hvd
  exact nsteps_l (astepAny.AAStep _ _ (.inl ⟨_, ldFetch cpu rs v vf hvf⟩))
    (nsteps_l (astepOfRead _ _ _ _ (ldAread cpu rs v) vd hvd) (nsteps_O _))

/-! ### The STORE shape -/

def sdVal : BitVec (8 * 8) := 0

def dreqSd : Mem_write_request 8 64 Arch.pa Arch.translation Arch.arch_ak :=
  { access_kind := akPlain, va := none, pa := dPa, translation := (), size := 8,
    value := some sdVal, tag := none }

def sdM2 : SailM Unit := .impure (.ok (.memWrite 8 64 dreqSd)) (fun _ => .pure ())
def sdM : SailM Unit := .impure (.ok (.memRead 4 64 freq)) (fun _ => sdM2)

def sdP0 (cpu : CPU) (rs : RegFile) : Pexv6 := .PHart cpu sdM rs none ibNone
def sdP1 (cpu : CPU) (rs : RegFile) : Pexv6 := .PHart cpu sdM2 rs none ibNone
def sdP2 (cpu : CPU) (rs : RegFile) : Pexv6 := .PHart cpu (.pure ()) rs none ibNone

/-- The row (Stage C: the data item only). -/
def sdRow : List Lbl := [.LStore false baseD (WeakInterpProj.wbytes 8 sdVal) .WCplain]

theorem sdRowShape : afSd8RowShape sdRow 0 baseD :=
  ⟨_, rfl, by simp [aident, afSd8DataIdent, wbytesLength]⟩

theorem sdAccessKindDreq : dreqSd.access_kind = akPlain := rfl

theorem sdFetch (cpu : CPU) (rs : RegFile) (vf : List (BitVec 8)) :
    vf.length = 4 →
    AxOpsem.astepProg sdRow ⟨sdP0 cpu rs, 0⟩ (LIFetch baseF (tagVals vf)) ⟨sdP1 cpu rs, 0⟩ :=
  fun hvf =>
    afAstepFetchOfMemread sdRow cpu 4 64 freq (fun _ => sdM2) rs ibNone OpaxWit.wtD0 0 vf
      fPaRam rfl hvf

/-- The data write: position 0 to 1 (Stage C: no oracle to be independent of). -/
theorem sdAstepWrite (cpu : CPU) (rs : RegFile) :
    AxOpsem.astepProg sdRow ⟨sdP1 cpu rs, 0⟩
      (LStore false baseD (WeakInterpProj.wbytes 8 sdVal) (depsAsrc (depsOfIb ibNone.ibBits))
        (depsVsrc (depsOfIb ibNone.ibBits)))
      ⟨sdP2 cpu rs, 1⟩ := by
  obtain ⟨lbd, hrowd, hidd⟩ := sdRowShape
  have hdat : lblData lbd = some (WeakInterpProj.wbytes 8 sdVal) := by
    simp only [sdRow, List.getElem?_cons_zero, Option.some.injEq] at hrowd
    subst hrowd; rfl
  exact afAstepWriteOfMemwrite sdRow cpu 8 64 dreqSd (fun _ => .pure ()) rs ibNone OpaxWit.wtD0
    0 lbd sdVal dPaRam (by decide) rfl rfl hrowd hidd hdat

/-- The full run for `sd8`: fetch then the data write, position 0 to 1 (Stage C). -/
theorem sdRun (cpu : CPU) (rs : RegFile) (vf : List (BitVec 8)) :
    vf.length = 4 →
    nsteps (astepAny sdRow) 2 ⟨sdP0 cpu rs, 0⟩ ⟨sdP2 cpu rs, 1⟩ := by
  intro hvf
  exact nsteps_l (astepAny.AAStep _ _ (.inl ⟨_, sdFetch cpu rs vf hvf⟩))
    (nsteps_l (astepAny.AAStep _ _ (.inl ⟨_, sdAstepWrite cpu rs⟩)) (nsteps_O _))

end AxFetch.AxFetchDemo

end Weak
