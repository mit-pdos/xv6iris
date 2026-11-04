/-
Weak: **FEASIBILITY PROBE** -- ONE `riscvStep` at a concrete M-mode hart state, evaluated by the
KERNEL through the footprint evaluators (`WeakEvFunnel.erun`, `AxBoundaryWpd.erd`,
`WeakEvExecEff.epure`, `WeakCert.execEff`).

Rocq: `iris/AxEpiProbe.v` @ xxvzwolszwmp.

Rocq header, in substance: not a proof development; every fact is a closed `vm_compute;
reflexivity` on a small observable.  Text `c.sdsp ra,8(sp)` @ 0x80000000, `c.ldsp ra,8(sp)` @
+2, `c.jr ra` @ +4 and again @ +6 (2 mod 4: the model fetches 2 bytes there, 4 at a 4-aligned
pc); the stack slot sp+8..sp+15 holds 0x1817161514131211.  Q0 a tracer discovers the register
footprints; Q1 `erun` of the whole step; Q2 walk to the `sig_seip` read, answer it, `erd` to the
fetch node; Q3 the rest of the instruction from the fetch node (`erun`, `epure`, `execEff`).
FINDING: with `tick = true`, `sig_seip` is read AGAIN after the fetch (`tick_clock`).

LEAN RESULTS: every Rocq lemma holds with Rocq's value.  Lean read order at the boundary:
`... mip, sig_meip, misa, sig_seip, ...` (meip BEFORE the seip node); after the fetch with
`tick = true` both `sig_seip` and `sig_meip` are read once more (none with `tick = false`).
Footprint sizes (`DrAll`, `DwAll`, `DrNoseip`) = (28, 8, 27).  Each closed evaluation takes
0.1-4 s in the kernel; the file builds in about 50 s.

## Deviations from Rocq

1. `vm_compute; reflexivity` ↦ `decide +kernel` (the `AxSpinSpikeRun` recipe: `riscvStep` is
   `noncomputable`, so the observables are `noncomputable def`s evaluated by the kernel only);
   `Time Eval vm_compute in e` ↦ `#kernel_eval e` (imported from `AxSpinSpikeRun`).
2. Vocabulary (as `AxBoundaryWpd` deviation 4): `gset register` ↦ `List Register` (unions are
   `++` then `eraseDups`, `size` is `length`, `∖ {[sig_seip]}` is a `filter`); `remove_dups` ↦
   `eraseDups`; `mstate` ↦ `ExecSt`; `M unit` ↦ `SailM Unit`; `Z`/`N` ↦ `Nat` (all values are
   non-negative; `uint` ↦ `toNat`); `init_regstate` ↦ `zeroRegs`; `pma_boot` ↦ `bootPMA`;
   `dev0_state` ↦ `testDevs` (ExecLib; the probe never touches a device); `list_to_map` ↦ a
   `find?` byte map (no duplicate addresses); `read_bytes`/`write_bytes` ↦ `bmRead`/`bmWrite`.
3. Tracer `ftp`: a write is answered `.Ok (some true)` (Rocq `inl None`) and a write request
   with no value is stuck code 5; `.error` is code 4 (Rocq `GenericFail`); the wildcard (code 5)
   also covers `choose` and the legacy RAM events.  `to_seip` stops at `.error` with `none`.
4. O2 STAGE C does not touch this file: the probe runs the Sail program, where the fetch is
   still a `memRead` node (`erd` stops at it; `erun`/`execEff` list it as a `WEread`); there are
   no graph rows here.
5. THE PIN SET (`AxRunClose` deviation 1): `AxBoundaryWpd.erdGstep` needs BOTH pins outside
   `Dr`, whereas Rocq's `Dr_noseip` (ported verbatim as `DrNoseip`) removes only `sig_seip`.
   Lean-only `AxEpiProbe.drNopin` / `AxEpiProbe.q2ObsNopin` / `AxEpiProbe.q2NopinSame` check the
   two Q2 fetch facts with neither pin readable (same results).

**Rocq → Lean name map.**  `w64` `AxEpiProbe.w64` (dup), `ra_val` `raVal`, `sp_val` `spVal`,
`pc_sd` `pcSd`, `pc_ld` `pcLd`, `pc_jr` `pcJr`, `pc_jr2` `pcJr2`, `probe_bytes` `probeBytes`,
`probe_mem` `probeMem`, `probe_regs` `probeRegs`, `t_at` `tAt`, `tres`/`TOk`/`TStuck`
`AxEpiProbe.Tres`/`.TOk`/`.TStuck` (dup), `ftp` `ftp`, `pc_of` `AxEpiProbe.pcOf` (dup), `x1_of`
`x1Of`, `ftp_obs` `ftpObs`, `fp_rd` `fpRd`, `fp_wr` `fpWr`, `Dr_all` `DrAll`, `Dw_all` `DwAll`,
`Dr_noseip` `DrNoseip`, `erun_obs` `erunObs`, `q1_cjr` `q1Cjr`, `to_seip` `toSeip`, `feed`
`feed`, `seip_set` `seipSet`, `is_seip_node` `isSeipNode`, `fetch_info` `fetchInfo`, `seip_obs`
`seipObs`, `q2_run` `q2Run`, `q2_obs` `q2Obs`, `q2_seip` `q2Seip`, `q2_cjr_false` `q2CjrFalse`,
`q2_cjr2_true` `q2Cjr2True`, `q3_erun` `q3Erun`, `q3_epure` `q3Epure`, `q3_eff` `q3Eff`,
`q3_cjr2_epure` `q3Cjr2Epure`, `q3_cldsp_erun` `q3CldspErun`, `q3_csdsp_eff` `q3CsdspEff`,
`q3_csdsp_erun_none` `q3CsdspErunNone`, `q3_cjr_epure` `q3CjrEpure`, `post_fetch_seip`
`postFetchSeip`, `post_fetch_seip_tick` `postFetchSeipTick`.  Lean-only: `AxEpiProbe.drNopin`,
`AxEpiProbe.q2ObsNopin`, `AxEpiProbe.q2NopinSame`.

**Dropped:** nothing (44 Rocq definitions/lemmas, incl. the inductive `tres`; Lean 44 + 3 Lean-only).  `Set Printing Depth`
has no twin.
-/
import Weak.AxBoundaryWpd
import Weak.ExecLib
import Weak.AxSpinSpikeRun

namespace Weak

open Sail Sail.ConcurrencyInterfaceV1
open Sail.ArchSem (FreeM)
open LeanRV64D
open MachCSL

/-! ## 1. The concrete state -/

/-- Rocq `w64`. -/
def AxEpiProbe.w64 (z : Nat) : BitVec 64 := BitVec.ofNat 64 z

def raVal : Nat := 0x80000100
def spVal : Nat := 0x80001000

/-- `c.sdsp ra,8(sp)` at `+0`, `c.ldsp ra,8(sp)` at `+2`, `c.jr ra` at `+4`. -/
def pcSd : Nat := 0x80000000
def pcLd : Nat := 0x80000002
def pcJr : Nat := 0x80000004
/-- `c.jr` again at a 2-but-not-4-aligned pc. -/
def pcJr2 : Nat := 0x80000006

def probeBytes : List (Nat × Nat) :=
  [ (0x80000000, 0x06), (0x80000001, 0xe4),
    (0x80000002, 0xa2), (0x80000003, 0x60),
    (0x80000004, 0x82), (0x80000005, 0x80),
    (0x80000006, 0x82), (0x80000007, 0x80),
    (0x80000008, 0x01), (0x80000009, 0x00),
    (0x8000000a, 0x01), (0x8000000b, 0x00) ] ++
  ((List.range 8).map fun j => (spVal + 8 + j, 0x11 + j))

def probeMem : BMap := fun a =>
  (probeBytes.find? fun p => AxEpiProbe.w64 p.1 == a).map fun p => BitVec.ofNat 8 p.2

def probeRegs (pc : Nat) : RegFile :=
  let w64 := AxEpiProbe.w64
  let rs := zeroRegs
  let rs := rs.set .PC (w64 pc)
  let rs := rs.set .nextPC (w64 pc)
  let rs := rs.set .cur_privilege .Machine
  let rs := rs.set .hart_state (.HART_ACTIVE ())
  let rs := rs.set .misa (w64 0x8000000000141105)
  let rs := rs.set .mstatus (w64 0xA00000000)
  let rs := rs.set .mseccfg (w64 0)
  let rs := rs.set .menvcfg (w64 0)
  let rs := rs.set .htif_tohost_base none
  let rs := rs.set .pma_regions bootPMA
  let rs := rs.set .elp 0#1
  let rs := rs.set .x1 (w64 raVal)
  let rs := rs.set .x2 (w64 spVal)
  rs

def tAt (pc : Nat) : ExecSt := ⟨probeRegs pc, probeMem, testDevs⟩

/-! ## 2. A tracing interpreter -/

inductive AxEpiProbe.Tres (X : Type) where
  | TOk (x : X) (t : ExecSt) (rd wr : List Register)
  | TStuck (why : Nat) (rd : List Register)

def ftp {X : Type} : SailM X → ExecSt → List Register → List Register → AxEpiProbe.Tres X
  | .pure y, t, rd, wr => .TOk y t rd wr
  | .impure (.error _) _, _, rd, _ => .TStuck 4 rd
  | .impure (.ok o) k, t, rd, wr =>
    match o, k with
    | .regRead r, k => ftp (k (t.regs r)) t (r :: rd) wr
    | .regWrite r v, k => ftp (k PUnit.unit) (t.setReg r v) rd (r :: wr)
    | .memRead n _ req, k =>
      if devAddr req.pa then .TStuck 1 rd
      else match bmRead t.mem req.pa n with
        | some w => ftp (k (.Ok (w, none))) t rd wr
        | none => .TStuck 2 rd
    | .memWrite n _ req, k =>
      if devAddr req.pa then .TStuck 3 rd
      else match req.value with
        | some w => ftp (k (.Ok (some true))) (t.setMem (bmWrite t.mem req.pa n w)) rd wr
        | none => .TStuck 5 rd
    | .instrAnnounce _ _, k => ftp (k ()) t rd wr
    | .branchAnnounce _ _, k => ftp (k ()) t rd wr
    | .barrier _, k => ftp (k ()) t rd wr
    | .cacheOp _, k => ftp (k ()) t rd wr
    | .tlbi _, k => ftp (k ()) t rd wr
    | .takeException _, k => ftp (k ()) t rd wr
    | .returnException _, k => ftp (k ()) t rd wr
    | .translationStart _, k => ftp (k ()) t rd wr
    | .translationEnd _, k => ftp (k ()) t rd wr
    | .cycleCount, k => ftp (k ()) t rd wr
    | .message _, k => ftp (k ()) t rd wr
    | .getCycleCount, k => ftp (k (0 : Nat)) t rd wr
    | _, _ => .TStuck 5 rd

def AxEpiProbe.pcOf (t : ExecSt) : Nat := (t.regs .PC).toNat
def x1Of (t : ExecSt) : Nat := (t.regs .x1).toNat

def ftpObs (m : SailM Unit) (t : ExecSt) : (Nat × Nat × Nat × Nat × Nat) ⊕ (Nat × Nat) :=
  match ftp m t [] [] with
  | .TOk _ t' rd wr =>
    .inl (AxEpiProbe.pcOf t', x1Of t', rd.eraseDups.length, wr.eraseDups.length,
      (rd.filter fun r => decide (r = .sig_seip)).length)
  | .TStuck why rd => .inr (why, rd.length)

#kernel_eval ftpObs (riscvStep false) (tAt pcJr)
#kernel_eval ftpObs (riscvStep false) (tAt pcLd)
#kernel_eval ftpObs (riscvStep false) (tAt pcSd)
#kernel_eval ftpObs (riscvStep true) (tAt pcJr)

noncomputable def fpRd (m : SailM Unit) (t : ExecSt) : List Register :=
  match ftp m t [] [] with | .TOk _ _ rd _ => rd.eraseDups | _ => []
noncomputable def fpWr (m : SailM Unit) (t : ExecSt) : List Register :=
  match ftp m t [] [] with | .TOk _ _ _ wr => wr.eraseDups | _ => []

noncomputable def DrAll : List Register :=
  (fpRd (riscvStep true) (tAt pcJr) ++ fpRd (riscvStep true) (tAt pcLd)
    ++ fpRd (riscvStep true) (tAt pcSd) ++ fpRd (riscvStep true) (tAt pcJr2)).eraseDups
noncomputable def DwAll : List Register :=
  (fpWr (riscvStep true) (tAt pcJr) ++ fpWr (riscvStep true) (tAt pcLd)
    ++ fpWr (riscvStep true) (tAt pcSd) ++ fpWr (riscvStep true) (tAt pcJr2)).eraseDups
noncomputable def DrNoseip : List Register := DrAll.filter fun r => !decide (r = .sig_seip)

/-- (Lean-only) `DrAll` without EITHER pin (the premise shape of `erdGstep`). -/
noncomputable def AxEpiProbe.drNopin : List Register :=
  DrAll.filter fun r => !decide (r = .sig_seip) && !decide (r = .sig_meip)

#kernel_eval (DrAll.length, DwAll.length, DrNoseip.length)

/-! ## Q1: `erun` of the whole step -/

noncomputable def erunObs (tick : Bool) (t : ExecSt) : Option (Nat × Nat × Nat) :=
  match erun DrAll DwAll (riscvStep tick) t with
  | some (_, t', es) => some (AxEpiProbe.pcOf t', x1Of t', es.length)
  | none => none

#kernel_eval erunObs false (tAt pcJr)
#kernel_eval erunObs true (tAt pcJr)
#kernel_eval erunObs false (tAt pcLd)
#kernel_eval erunObs false (tAt pcSd)

theorem q1Cjr : erunObs false (tAt pcJr) = some (raVal, raVal, 1) := by
  decide +kernel

/-! ## Q2: walk to the `sig_seip` read, then `erd` to the fetch -/

def toSeip : SailM Unit → ExecSt → Option (SailM Unit × ExecSt)
  | .pure _, _ => none
  | .impure (.error _) _, _ => none
  | .impure (.ok o) k, t =>
    match o, k with
    | .regRead r, k =>
      if r = .sig_seip then some (.impure (.ok (.regRead r)) k, t)
      else toSeip (k (t.regs r)) t
    | .regWrite r v, k => toSeip (k PUnit.unit) (t.setReg r v)
    | .instrAnnounce _ _, k => toSeip (k ()) t
    | .branchAnnounce _ _, k => toSeip (k ()) t
    | .cacheOp _, k => toSeip (k ()) t
    | .tlbi _, k => toSeip (k ()) t
    | .takeException _, k => toSeip (k ()) t
    | .returnException _, k => toSeip (k ()) t
    | .translationStart _, k => toSeip (k ()) t
    | .translationEnd _, k => toSeip (k ()) t
    | .cycleCount, k => toSeip (k ()) t
    | .message _, k => toSeip (k ()) t
    | .getCycleCount, k => toSeip (k (0 : Nat)) t
    | _, _ => none

def feed (m : SailM Unit) (t : ExecSt) : SailM Unit :=
  match m with
  | .impure (.ok o) k =>
    match o, k with
    | .regRead r, k => k (t.regs r)
    | .memRead n _ req, k =>
      match bmRead t.mem req.pa n with
      | some w => k (.Ok (w, none))
      | none => m
    | _, _ => m
  | _ => m

def seipSet (t : ExecSt) (v : Bool) : ExecSt :=
  t.setReg .sig_seip (if v then 1#1 else 0#1)

def isSeipNode (m : SailM Unit) : Bool :=
  match m with
  | .impure (.ok (.regRead r)) _ => decide (r = .sig_seip)
  | _ => false

def fetchInfo (m : SailM Unit) : Option (Nat × Nat) :=
  match m with
  | .impure (.ok (.memRead n _ req)) _ => some (n, req.pa.toNat)
  | _ => none

noncomputable def seipObs (tick : Bool) (t : ExecSt) : Option Bool :=
  match toSeip (riscvStep tick) t with
  | some (m0, _) => some (isSeipNode m0)
  | none => none

noncomputable def q2Run (tick : Bool) (t : ExecSt) (v : Bool) : Option (SailM Unit × ExecSt) :=
  match toSeip (riscvStep tick) t with
  | some (m0, t1) => erd DrNoseip DwAll (feed m0 (seipSet t1 v)) t1
  | none => none

noncomputable def q2Obs (tick : Bool) (t : ExecSt) (v : Bool) : Option (Nat × Nat) :=
  match q2Run tick t v with
  | some (mf, _) => fetchInfo mf
  | none => none

/-- (Lean-only) `q2Obs` with `erd` over `AxEpiProbe.drNopin` (neither pin readable). -/
noncomputable def AxEpiProbe.q2ObsNopin (tick : Bool) (t : ExecSt) (v : Bool) : Option (Nat × Nat) :=
  match toSeip (riscvStep tick) t with
  | some (m0, t1) =>
    match erd AxEpiProbe.drNopin DwAll (feed m0 (seipSet t1 v)) t1 with
    | some (mf, _) => fetchInfo mf
    | none => none
  | none => none

#kernel_eval seipObs false (tAt pcJr)
#kernel_eval q2Obs false (tAt pcJr) false
#kernel_eval q2Obs false (tAt pcJr) true
#kernel_eval q2Obs true (tAt pcLd) false
#kernel_eval q2Obs true (tAt pcSd) true
#kernel_eval q2Obs true (tAt pcJr2) false
#kernel_eval AxEpiProbe.q2ObsNopin false (tAt pcJr) false
#kernel_eval AxEpiProbe.q2ObsNopin true (tAt pcJr2) true

theorem q2Seip : seipObs false (tAt pcJr) = some true := by
  decide +kernel

theorem q2CjrFalse : q2Obs false (tAt pcJr) false = some (4, pcJr) := by
  decide +kernel

theorem q2Cjr2True : q2Obs true (tAt pcJr2) true = some (2, pcJr2) := by
  decide +kernel

/-- (Lean-only) The same fetch nodes with NEITHER pin in the read footprint (the `meip` read
comes before the `seip` node and the tick's re-reads come after the fetch). -/
theorem AxEpiProbe.q2NopinSame :
    AxEpiProbe.q2ObsNopin false (tAt pcJr) false = some (4, pcJr) ∧
    AxEpiProbe.q2ObsNopin true (tAt pcJr2) true = some (2, pcJr2) := by
  decide +kernel

/-! ## Q3: from the fetch node, the rest of the instruction -/

noncomputable def q3Erun (tick : Bool) (t : ExecSt) (v : Bool) : Option (Nat × Nat × Nat) :=
  match q2Run tick t v with
  | some (mf, t2) =>
    match erun DrAll DwAll mf t2 with
    | some (_, t', es) => some (AxEpiProbe.pcOf t', x1Of t', es.length)
    | none => none
  | none => none

noncomputable def q3Epure (tick : Bool) (t : ExecSt) (v : Bool) : Option (Nat × Nat) :=
  match q2Run tick t v with
  | some (mf, t2) =>
    match epure (DrAll ++ DwAll) (feed mf t2) t2 with
    | some (_, t') => some (AxEpiProbe.pcOf t', x1Of t')
    | none => none
  | none => none

noncomputable def q3Eff (tick : Bool) (t : ExecSt) (v : Bool) : Option (Nat × Nat × Nat × Option Nat) :=
  match q2Run tick t v with
  | some (mf, t2) =>
    match execEff (feed mf t2) t2 with
    | some (_, t', es) =>
      some (AxEpiProbe.pcOf t', x1Of t', es.length,
        match bmRead t'.mem (AxEpiProbe.w64 (spVal + 8)) 8 with
        | some w => some w.toNat
        | none => none)
    | none => none
  | none => none

#kernel_eval q3Erun false (tAt pcJr) false
#kernel_eval q3Epure false (tAt pcJr) false
#kernel_eval q3Erun true (tAt pcLd) false
#kernel_eval q3Epure true (tAt pcLd) false
#kernel_eval q3Erun true (tAt pcSd) false
#kernel_eval q3Eff true (tAt pcSd) false
#kernel_eval q3Eff true (tAt pcLd) true
#kernel_eval q3Epure true (tAt pcJr2) true
#kernel_eval q3Erun true (tAt pcJr2) false

theorem q3Cjr2Epure : q3Epure true (tAt pcJr2) false = some (raVal, raVal) := by
  decide +kernel

theorem q3CldspErun :
    q3Erun true (tAt pcLd) false = some (pcLd + 2, 0x1817161514131211, 2) := by
  decide +kernel

theorem q3CsdspEff :
    q3Eff true (tAt pcSd) false = some (pcSd + 2, raVal, 1, some raVal) := by
  decide +kernel

theorem q3CsdspErunNone : q3Erun true (tAt pcSd) false = none := by
  decide +kernel

theorem q3CjrEpure : q3Epure false (tAt pcJr) false = some (raVal, raVal) := by
  decide +kernel

noncomputable def postFetchSeip (tick : Bool) (t : ExecSt) : Option Nat :=
  match q2Run tick t false with
  | some (mf, t2) =>
    match ftp (feed mf t2) t2 [] [] with
    | .TOk _ _ rd _ => some (rd.filter fun r => decide (r = .sig_seip)).length
    | .TStuck _ _ => none
  | none => none

#kernel_eval (postFetchSeip false (tAt pcJr2), postFetchSeip true (tAt pcJr2))

theorem postFetchSeipTick : postFetchSeip true (tAt pcJr2) = some 1 := by
  decide +kernel


end Weak
