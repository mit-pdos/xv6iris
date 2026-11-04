/-
Weak: **FEASIBILITY PROBE** -- does the J0 concrete-state ledger method survive S-mode + Sv39
paging?  Mirror of `AxEpiProbe` at a concrete SUPERVISOR hart state with `satp` = Sv39 over a
concrete 3-level page table in memory; the closed facts are evaluated by the KERNEL.

Rocq: `iris/AxSmodeProbe.v` @ xxvzwolszwmp.

Rocq header, in substance: the Sail model HAS a TLB (`tlb`, 64 direct-mapped entries, all `none`
at reset).  Cold TLB, `ld x1,8(x2)`: 8 RAM reads in order root[2], L1[0], L0[0] (8 B each), the
fetch (4 B), root[2], L1[0], L0[1], the data (8 B); 2 TLB fills; no writes (A/D preset).  Warm
TLB: fetch + data only.  A/D CLEAR (xv6-faithful, Svadu): +1 re-read and +1 PTE WRITE per walk
(10 R + 2 W).  Warm TLB: the UNMODIFIED M-mode `AxLdModelFacts` instantiates
(`sLedgerLdWarm`, `wpdSldWarmConcrete`).  Cold TLB: the generic known-read chain `wpdKnode`
+ `wpdSldCold`, a closed `wpd` of the cold S-mode ld.  RESIDUALS (as Rocq): `kgdOk`'s per-read
premises (row items / graph values = image = PT bytes) are premises; tick = true and the D-bit
store are not ledgered.

LEAN RESULTS: every Rocq observable has Rocq's value (same 8 reads at the same PAs, 2 TLB fills,
warm = fetch + data, noad = 10 R + 2 W + 2 fills), EXCEPT the access kinds (deviation 3).
Footprints: `sDr` 29 registers (`DrAll` + stimecmp, tlb, satp), `sDw` 9 (`DwAll` + tlb).  Each
closed evaluation 0.4-9 s in the kernel; the file builds in about 50 s.

## Deviations from Rocq

1. TWO WIRE-READ NODES AT THE BOUNDARY (`AxEpiLedger` deviation 1): the cold ledger
   `sColdBranch` takes TWO answers `v'` (`sig_meip`) `v` (`sig_seip`) and walks with
   `AxEpiLedger.toPin`; Rocq's `s_cold_branch0/1` become `sColdBranch00/01/10/11`; `sColdInv`
   adds the meip-level `Pseip` disjunct and quantifies the seip node per meip answer (as
   `ledgerLdInv`); `wpdSldCold` splits twice (`AxEpiLedger.wpdOfSplitFrom`, `meipN0Ok`,
   `seipN0Ok`), in place of `wpd_boundary_erd` + `to_seip_gstep`.  The probes of §4
   (`sChain`, verbatim) still walk with `AxEpiProbe.toSeip`.
2. THE PINS (`AxRunClose` deviation 1): the ledgers run over the Lean-only
   `AxSmodeProbe.sDrNopin` (Rocq `sDr_noseip`, which is kept for the §4/§5 probes) and `sD`
   removes BOTH pins (Rocq only `sig_seip`); `sSeipDr` is stated over `sDrNopin`, with the
   Lean-only twins `AxSmodeProbe.sMeipDr`/`sMeipD`; `wpdKnode` takes `HDrm : sig_meip ∉ Dr`.
3. ACCESS KINDS (O2): the Lean model tags the walker reads `AK_ttw` (tag 2) and the fetch
   `AK_ifetch` (tag 1); only the data load is `AK_explicit`.  `sColdAllExplicit` therefore
   states the per-event (R/W, kind) list `[(0,2)×3, (0,1), (0,2)×3, (0,0)]` and the 2 fills
   (Rocq: all `(0, 0)`); `sWarmReads`' fetch has tag 1; `sNoadCounts` unchanged.  `sWarmReads`
   is stated through a projection to `Option (List mev × Nat)` (the kernel does not unfold the
   `Option`-of-`Sum` decidability instance).
4. O2 STAGE C (`AxCjrWpd` deviation 1) in the COLD CHAIN: a walker read is a plain graph read
   (row position `k ↦ k + 1`), the fetch is a pinned admin step at the SAME position.  The chain
   entries are `(pa, bytes, isFetch)` (Rocq `(Z * list (bv 8))`); `knodeOk`/`knodeOkB` check
   `akIfetch = isFetch` (Rocq `ak_latest = false` only, kept); `kinv` moves the position by
   `AxSmodeProbe.kpos`; `kend`'s end position is `k + AxSmodeProbe.kadv reads` (graph reads
   only).  `kgdOk` (Rocq: index-wise, three conjuncts per read at `k + j`) is recursive: a
   walker read has Rocq's `fetchGdOk` (row item, graph value, image) and `fetchFlow` (its
   deposit) at its position (Rocq's third, local-interp, conjunct is dropped: a plain read
   node has no non-read step, `AxCjrWpd` deviation 1); the fetch has `AxCjrWpd.fetchImgOk`
   (Q8).  Each walker read is discharged by the Lean-only `AxSmodeProbe.wpdKreadStep` (Rocq
   used `wpd_fetch_step`, the fetch being a row read there), the fetch by `wpdFetchStep`.
   Hence the positions: data load, `Hrow`, the flow `F` at `kk + 6` (Rocq `kk + 7`), `RetLd`
   and the post-load `Pbefore` at `kk + 6 + 1` (Rocq `S (kk + 7)`).  `Hntext` is dropped
   (`ldLoadOk` carries `akIfetch = false`, `AxEpiLedger` deviation 3); `wpdSldWarmConcrete`
   has `wpdCldspConcrete`'s Stage-C premises (`Hgd` = `fetchImgOk`, no `Hflow`/`Hloc`/`Hntext`,
   `Hrow`/`F` at `kk`, `RetLd` at `kk + 1`).
5. `vm_compute` ↦ `decide +kernel`; `Time Eval vm_compute` ↦ `#kernel_eval`.  The cold branch
   facts quantify over the loaded word, so they go through Lean-only boolean twins at ONE free
   64-bit word (`AxSmodeProbe.knodeOkB`, `sColdBranchB`, bridges `knodeOkOfB`,
   `sColdBranchOfB`, `ax_epi_ledger_krfl`), as `AxEpiLedger` deviation 5; the warm ledger
   reuses `AxEpiLedger.ldBranchAtOfB` with the Lean-only `AxSmodeProbe.sPostB`/`sPostOfB`.
6. TYPES (as `AxEpiProbe` deviation 2): `Z`/`N` ↦ `Nat` (PAs in the chain/ledger are `Int`,
   as `paZ`), `gset` ↦ `List Register` (`∪` ↦ `++`, `∖` ↦ `filter`), `mstate` ↦ `ExecSt`,
   `list_to_map` ↦ the `find?` byte map `AxSmodeProbe.memOfList`, `init_regstate` ↦
   `zeroRegs`, `dev0_state` ↦ `testDevs`, `read_bytes`/`write_bytes` ↦ `bmRead`/`bmWrite`;
   the tracer `mtr` answers a write `.Ok (some true)`, codes as `AxEpiProbe.ftp`.
   `Mem_read_request n va …` (new bound `va`), `WPd … @ MaybeStuck; i {{ Φ }}` ↦
   `wpd .MaybeStuck i s Φ`, `invGS_gen HasNoLc Σ` ↦ `[InvGS_gen hlc GF]`.  Q7: `erd`/`toPin`
   stop at an sfence announce (not reached here); Q10: no `noSfAnn` premise is needed (every
   run is an `erd`/`epure` certificate).

**Rocq → Lean name map.**  Duplicated (file-qualified): `s_root` `AxSmodeProbe.sRoot`, `s_l1`
`.sL1`, `s_l0` `.sL0`, `pte_nl` `.pteNl`, `pte_leaf` `.pteLeaf`, `s_satp` `.sSatp`, `s_sp`
`.sSp`, `dw_bytes` `.dwBytes`, `s_pmpcfg` `.sPmpcfg`, `s_pmpaddr` `.sPmpaddr`, `mev` `.mev`.
Others: `s_pc` `sPc`, `s_bytes` `sBytes`, `s_mem` `sMem`, `s_regs` `sRegs`, `s_at` `sAt`,
`ak_tag` `akTag`, `mtr` `mtr`, `mfin` `mfin`, `s_warm` `sWarm`, `warm_obs` `warmObs`,
`step2_obs` `step2Obs`, `sDr` `sDr`, `sDw` `sDw`, `sDr_noseip` `sDrNoseip`, `erd_chain`
`erdChain`, `s_chain` `sChain`, `s_chain_reads` `sChainReads`, `s_tail_obs` `sTailObs`,
`s_cold_expected` `sColdExpected`, `s_cold_reads_0/1/tick` `sColdReads0/1/Tick`,
`s_cold_tail` `sColdTail`, `s_cold_all_explicit` `sColdAllExplicit`, `s_warm_reads`
`sWarmReads`, `s_warm_t` `sWarmT`, `sD` `sD`, `s_vs` `sVs`, `s_ldaddr` `sLdaddr`, `s_post`
`sPost`, `s_ledger_ld_warm` `sLedgerLdWarm`, `wpd_sld_warm_concrete` `wpdSldWarmConcrete`,
`pte_leaf_noad` `pteLeafNoad`, `s_bytes_noad` `sBytesNoad`, `s_mem_noad` `sMemNoad`,
`s_at_noad` `sAtNoad`, `s_noad_counts` `sNoadCounts`, `knode_ok` `knodeOk`, `kend` `kend`,
`kinv` `kinv`, `kgd_ok` `kgdOk`, `wpd_knode` `wpdKnode`, `pte_bv` `pteBv`, `s_walk7`
`sWalk7`, `s_cold_branch` `sColdBranch`, `s_cold_branch0/1` `sColdBranch00/01/10/11`,
`s_seip_at` `sSeipAt`, `s_head` `sHead`, `s_seip_Dr` `sSeipDr`, `s_seip_D` `sSeipD`,
`s_cold_inv` `sColdInv`, `wpd_sld_cold` `wpdSldCold`.  Lean-only (all `AxSmodeProbe.*`):
`memOfList`, `sDrNopin`, `sPostB`, `sPostOfB`, `kpos`, `kadv`, `knodeOkCons`, `kendCons`,
`kinvCons`, `ldLoadOkShape`, `wpdKreadStep`, `knodeOkB`, `knodeOkOfB`, `sColdBranchB`,
`sColdBranchOfB`, `sMeipDr`, `sMeipD`, `sColdBranchAt`.

**Dropped:** nothing (Rocq 64 definitions/lemmas; Lean 66 = 64 + the two extra pin branches,
+ 18 Lean-only).  **Not ported:** `Set Printing Depth`, the `Print Assumptions` lines (the
lint's axiom check covers them).
-/
import Weak.AxEpiLedger

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std Iris.Std.PartialMap MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open Sail.ArchSem (FreeM)
open LeanRV64D
open Wlabel

/-! # 1. The concrete S-mode state -/

def AxSmodeProbe.sRoot : Nat := 0x80010
def AxSmodeProbe.sL1 : Nat := 0x80011
def AxSmodeProbe.sL0 : Nat := 0x80012
def AxSmodeProbe.pteNl (ppn : Nat) : Nat := (ppn <<< 10) ||| 0x01
def AxSmodeProbe.pteLeaf (ppn : Nat) : Nat := (ppn <<< 10) ||| 0xCF

def AxSmodeProbe.sSatp : Nat := (8 <<< 60) ||| AxSmodeProbe.sRoot

def sPc : Nat := 0x80000000
def AxSmodeProbe.sSp : Nat := 0x80001000

def AxSmodeProbe.dwBytes (a v : Nat) : List (Nat × Nat) :=
  (List.range 8).map fun j => (a + j, (v >>> (8 * j)) &&& 0xFF)

def sBytes : List (Nat × Nat) :=
  [ (0x80000000, 0x83), (0x80000001, 0x30), (0x80000002, 0x81), (0x80000003, 0x00),
    (0x80000004, 0x01), (0x80000005, 0x00), (0x80000006, 0x01), (0x80000007, 0x00) ] ++
  ((List.range 8).map fun j => (AxSmodeProbe.sSp + 8 + j, 0x11 + j)) ++
  AxSmodeProbe.dwBytes (AxSmodeProbe.sRoot * 4096 + 2 * 8) (AxSmodeProbe.pteNl AxSmodeProbe.sL1) ++
  AxSmodeProbe.dwBytes (AxSmodeProbe.sL1 * 4096 + 0 * 8) (AxSmodeProbe.pteNl AxSmodeProbe.sL0) ++
  AxSmodeProbe.dwBytes (AxSmodeProbe.sL0 * 4096 + 0 * 8) (AxSmodeProbe.pteLeaf 0x80000) ++
  AxSmodeProbe.dwBytes (AxSmodeProbe.sL0 * 4096 + 1 * 8) (AxSmodeProbe.pteLeaf 0x80001)

def AxSmodeProbe.memOfList (l : List (Nat × Nat)) : BMap := fun a =>
  (l.find? fun p => AxEpiProbe.w64 p.1 == a).map fun p => BitVec.ofNat 8 p.2

def sMem : BMap := AxSmodeProbe.memOfList sBytes

def AxSmodeProbe.sPmpcfg : Vector (BitVec 8) 64 := (zeroRegs .pmpcfg_n).set 0 0x0F#8
def AxSmodeProbe.sPmpaddr : Vector (BitVec 64) 64 :=
  (zeroRegs .pmpaddr_n).set 0 (AxEpiProbe.w64 0x22000000)

def sRegs (pc : Nat) : RegFile :=
  let w64 := AxEpiProbe.w64
  let rs := zeroRegs
  let rs := rs.set .PC (w64 pc)
  let rs := rs.set .nextPC (w64 pc)
  let rs := rs.set .cur_privilege .Supervisor
  let rs := rs.set .hart_state (.HART_ACTIVE ())
  let rs := rs.set .misa (w64 0x8000000000141105)
  let rs := rs.set .mstatus (w64 0xA00000000)
  let rs := rs.set .mseccfg (w64 0)
  let rs := rs.set .menvcfg (w64 0xA000000000000000)
  let rs := rs.set .mie (w64 0)
  let rs := rs.set .mideleg (w64 0x222)
  let rs := rs.set .medeleg (w64 0xB109)
  let rs := rs.set .satp (w64 AxSmodeProbe.sSatp)
  let rs := rs.set .pmpcfg_n AxSmodeProbe.sPmpcfg
  let rs := rs.set .pmpaddr_n AxSmodeProbe.sPmpaddr
  let rs := rs.set .htif_tohost_base none
  let rs := rs.set .pma_regions bootPMA
  let rs := rs.set .elp 0#1
  let rs := rs.set .x2 (w64 AxSmodeProbe.sSp)
  rs

def sAt (pc : Nat) : ExecSt := ⟨sRegs pc, sMem, testDevs⟩

/-! # 2. Memory-event tracer -/

def akTag {A : Type} (ak : Access_kind A) : Nat :=
  match ak with
  | .AK_explicit _ => 0 | .AK_ifetch _ => 1 | .AK_ttw _ => 2 | .AK_arch _ => 3

abbrev AxSmodeProbe.mev := Nat × Nat × Nat × Nat

def mtr {X : Type} : SailM X → ExecSt → List AxSmodeProbe.mev → Nat →
    (List AxSmodeProbe.mev × Nat) ⊕ (Nat × List AxSmodeProbe.mev)
  | .pure _, _, acc, ntlb => .inl (acc.reverse, ntlb)
  | .impure (.error _) _, _, acc, _ => .inr (4, acc.reverse)
  | .impure (.ok o) k, t, acc, ntlb =>
    match o, k with
    | .regRead r, k => mtr (k (t.regs r)) t acc ntlb
    | .regWrite r v, k =>
      mtr (k PUnit.unit) (t.setReg r v) acc (if r = .tlb then ntlb + 1 else ntlb)
    | .memRead n _ req, k =>
      let e : AxSmodeProbe.mev := (0, akTag req.access_kind, n, req.pa.toNat)
      if devAddr req.pa then .inr (1, (e :: acc).reverse)
      else match bmRead t.mem req.pa n with
        | some w => mtr (k (.Ok (w, none))) t (e :: acc) ntlb
        | none => .inr (2, (e :: acc).reverse)
    | .memWrite n _ req, k =>
      let e : AxSmodeProbe.mev := (1, akTag req.access_kind, n, req.pa.toNat)
      if devAddr req.pa then .inr (3, (e :: acc).reverse)
      else match req.value with
        | some w => mtr (k (.Ok (some true))) (t.setMem (bmWrite t.mem req.pa n w)) (e :: acc) ntlb
        | none => .inr (5, acc.reverse)
    | .instrAnnounce _ _, k => mtr (k ()) t acc ntlb
    | .branchAnnounce _ _, k => mtr (k ()) t acc ntlb
    | .barrier _, k => mtr (k ()) t acc ntlb
    | .cacheOp _, k => mtr (k ()) t acc ntlb
    | .tlbi _, k => mtr (k ()) t acc ntlb
    | .takeException _, k => mtr (k ()) t acc ntlb
    | .returnException _, k => mtr (k ()) t acc ntlb
    | .translationStart _, k => mtr (k ()) t acc ntlb
    | .translationEnd _, k => mtr (k ()) t acc ntlb
    | .cycleCount, k => mtr (k ()) t acc ntlb
    | .message _, k => mtr (k ()) t acc ntlb
    | .getCycleCount, k => mtr (k (0 : Nat)) t acc ntlb
    | _, _ => .inr (5, acc.reverse)

#kernel_eval ftpObs (riscvStep false) (sAt sPc)
#kernel_eval mtr (riscvStep false) (sAt sPc) [] 0

noncomputable def mfin (m : SailM Unit) (t : ExecSt) : Option ExecSt :=
  match ftp m t [] [] with
  | .TOk _ t' _ _ => some t'
  | .TStuck _ _ => none

noncomputable def sWarm : Option ExecSt :=
  match mfin (riscvStep false) (sAt sPc) with
  | some t => some ((t.setReg .PC (AxEpiProbe.w64 sPc)).setReg .nextPC (AxEpiProbe.w64 sPc))
  | none => none

noncomputable def warmObs (tick : Bool) :
    Option ((List AxSmodeProbe.mev × Nat) ⊕ (Nat × List AxSmodeProbe.mev)) :=
  match sWarm with
  | some t => some (mtr (riscvStep tick) t [] 0)
  | none => none

noncomputable def step2Obs :
    Option ((List AxSmodeProbe.mev × Nat) ⊕ (Nat × List AxSmodeProbe.mev)) :=
  match mfin (riscvStep false) (sAt sPc) with
  | some t => some (mtr (riscvStep true) t [] 0)
  | none => none

#kernel_eval warmObs false
#kernel_eval warmObs true
#kernel_eval step2Obs
#kernel_eval mtr (riscvStep true) (sAt sPc) [] 0

noncomputable def sDr : List Register := fpRd (riscvStep true) (sAt sPc)
noncomputable def sDw : List Register := fpWr (riscvStep true) (sAt sPc)
noncomputable def sDrNoseip : List Register := sDr.filter fun r => !decide (r = .sig_seip)

#kernel_eval (sDr.length, sDw.length, (sDr.filter fun r => r ∉ DrAll).length,
  (sDw.filter fun r => r ∉ DwAll).length)
#kernel_eval ((sDr.filter fun r => r ∉ DrAll), (sDw.filter fun r => r ∉ DwAll))

/-! # 4. J0 evaluators -/

def erdChain (Dr Dw : List Register) : Nat → SailM Unit → ExecSt →
    List (Nat × Nat) × Option (SailM Unit × ExecSt)
  | 0, m, t => ([], some (m, t))
  | f + 1, m, t =>
    match erd Dr Dw m t with
    | some (mr, t1) =>
      match fetchInfo mr with
      | some i =>
        let lr := erdChain Dr Dw f (feed mr t1) t1
        (i :: lr.1, lr.2)
      | none => ([], none)
    | none => ([], none)

noncomputable def sChain (tick v : Bool) (Dr : List Register) (n : Nat) :
    List (Nat × Nat) × Option (SailM Unit × ExecSt) :=
  match toSeip (riscvStep tick) (sAt sPc) with
  | some (m0, t1) => erdChain Dr sDw n (feed m0 (seipSet t1 v)) t1
  | none => ([], none)

noncomputable def sChainReads (tick v : Bool) (Dr : List Register) : List (Nat × Nat) :=
  (sChain tick v Dr 8).1

noncomputable def sTailObs (tick v : Bool) (Dr : List Register) : Option (Nat × Nat) :=
  match (sChain tick v Dr 8).2 with
  | some (m, t) =>
    match epure (sDr ++ sDw) m t with
    | some (_, t') => some (AxEpiProbe.pcOf t', x1Of t')
    | none => none
  | none => none

#kernel_eval seipObs false (sAt sPc)
#kernel_eval sChainReads false false sDrNoseip
#kernel_eval sChainReads false true sDrNoseip
#kernel_eval sChainReads true false sDrNoseip
#kernel_eval sChainReads true false sDr
#kernel_eval sTailObs false false sDrNoseip
#kernel_eval sTailObs true true sDr

/-! # 5. Closed facts -/

/-- Cold TLB, both seip answers: 8 RAM reads — walk(fetch) ×3, fetch, walk(data) ×3, data — at
exactly these PAs, in this order. -/
def sColdExpected : List (Nat × Nat) :=
  [(8, AxSmodeProbe.sRoot * 4096 + 16), (8, AxSmodeProbe.sL1 * 4096), (8, AxSmodeProbe.sL0 * 4096),
   (4, sPc),
   (8, AxSmodeProbe.sRoot * 4096 + 16), (8, AxSmodeProbe.sL1 * 4096),
   (8, AxSmodeProbe.sL0 * 4096 + 8),
   (8, AxSmodeProbe.sSp + 8)]

theorem sColdReads0 : sChainReads false false sDrNoseip = sColdExpected := by
  decide +kernel
theorem sColdReads1 : sChainReads false true sDrNoseip = sColdExpected := by
  decide +kernel
theorem sColdReadsTick : sChainReads true false sDrNoseip = sColdExpected := by
  decide +kernel
theorem sColdTail : sTailObs false false sDrNoseip = some (sPc + 4, 0x1817161514131211) := by
  decide +kernel

/-- The access kinds of the cold step (deviation 3): every event is a READ (no write: A/D
preset); the six walker reads are `AK_ttw` (tag 2), the fetch `AK_ifetch` (tag 1), the data
load `AK_explicit` (tag 0); two TLB fills. -/
theorem sColdAllExplicit :
    (match mtr (riscvStep false) (sAt sPc) [] 0 with
     | .inl (l, ntlb) => (l.map fun e => (e.1, e.2.1), ntlb)
     | .inr _ => ([], 0)) =
      ([(0, 2), (0, 2), (0, 2), (0, 1), (0, 2), (0, 2), (0, 2), (0, 0)], 2) := by
  decide +kernel

/-- Warm TLB: the same ld issues only fetch + data, no TLB write. -/
theorem sWarmReads :
    (match warmObs false with
     | some (.inl (l, ntlb)) => some (l, ntlb)
     | _ => none) = some ([(0, 1, 4, sPc), (0, 0, 8, AxSmodeProbe.sSp + 8)], 0) := by
  decide +kernel

/-- The warm-TLB state as a closed `ExecSt`. -/
noncomputable def sWarmT : ExecSt :=
  match sWarm with
  | some t => t
  | none => sAt sPc

/-- (Lean-only) `sDr` without EITHER pin (the premise shape of `erdGstep`; deviation 2). -/
noncomputable def AxSmodeProbe.sDrNopin : List Register :=
  sDr.filter fun r => !decide (r = .sig_seip) && !decide (r = .sig_meip)

/-- Rocq `(sDr ∪ sDw) ∖ {[sig_seip]}`; Lean removes BOTH pins (deviation 2). -/
noncomputable def sD : List Register :=
  (sDr ++ sDw).eraseDups.filter fun r => !decide (r = .sig_seip) && !decide (r = .sig_meip)

def sVs : List (BitVec 8) := [0x83#8, 0x30#8, 0x81#8, 0x00#8]
def sLdaddr : Int := (AxSmodeProbe.sSp : Int) + 8
def sPost (_x : Int) (rs : RegFile) : Prop := (rs .PC).toNat = sPc + 4

/-- (Lean-only) The boolean twin of `sPost`. -/
def AxSmodeProbe.sPostB (rs : RegFile) : Bool := decide ((rs .PC).toNat = sPc + 4)

theorem AxSmodeProbe.sPostOfB (z : Int) (rs : RegFile) :
    AxSmodeProbe.sPostB rs = true → sPost z rs :=
  fun h => (of_decide_eq_true h : (rs .PC).toNat = sPc + 4)

/-- THE S-MODE LOAD LEDGER at the WARM-TLB state: the unmodified M-mode `AxLdModelFacts` record
(one fetch, one data read) instantiates. -/
theorem sLedgerLdWarm :
    AxLdModelFacts sWarmT AxSmodeProbe.sDrNopin sDw sD (sPc : Int) sVs sLdaddr sPost where
  lgSeipDr := by decide +kernel
  lgMeipDr := by decide +kernel
  lgSeipD := by decide +kernel
  lgMeipD := by decide +kernel
  lgHead := by decide +kernel
  lgToSeip := by decide +kernel
  lgBranch00 := AxEpiLedger.ldBranchAtOfB _ _ _ _ _ _ AxSmodeProbe.sPostB _
    AxSmodeProbe.sPostOfB _ _ _ (by intro x; ax_epi_ledger_krfl)
  lgBranch01 := AxEpiLedger.ldBranchAtOfB _ _ _ _ _ _ AxSmodeProbe.sPostB _
    AxSmodeProbe.sPostOfB _ _ _ (by intro x; ax_epi_ledger_krfl)
  lgBranch10 := AxEpiLedger.ldBranchAtOfB _ _ _ _ _ _ AxSmodeProbe.sPostB _
    AxSmodeProbe.sPostOfB _ _ _ (by intro x; ax_epi_ledger_krfl)
  lgBranch11 := AxEpiLedger.ldBranchAtOfB _ _ _ _ _ _ AxSmodeProbe.sPostB _
    AxSmodeProbe.sPostOfB _ _ _ (by intro x; ax_epi_ledger_krfl)

section sWarmWpd
variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [AxirisG GF] [Axpol]

/-- `wpd` of the S-mode `ld x1, 8(x2)` at the warm-TLB concrete state: the premises of
`AxEpiLedger.wpdCldspConcrete`. -/
theorem wpdSldWarmConcrete (i : Agent) (Φ : Athread → IProp GF) (cpu : CPU) (ib : Ibch)
    (kk : Nat) (Rv : Gdexec → List (BitVec 8) → IProp GF)
    (Hgd : ∀ GD, rvwmoCatConsistent GD →
      AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜AxCjrWpd.fetchImgOk GD i kk (sPc : Int) sVs⌝)
    (Hrow : ∀ GD, rvwmoCatConsistent GD →
      AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜loadRowOk GD i kk⌝) :
    ⊢ (∀ (GD : Gdexec) (ls : AxirisG.logTsT GF) (v : List (BitVec 8)),
         ⌜rvwmoCatConsistent GD⌝ -∗ □ AxirisG.gconstInterp GD -∗ AxirisG.localInterp GD i kk ls -∗
         ⌜graphValue GD (i, kk) = some v⌝ -∗ loadFlow GD i kk (Rv GD v)) -∗
      ((∀ s', ⌜RetLd cpu sPost (kk + 1) s'⌝ -∗ wpd .MaybeStuck i s' Φ) ∧
       (∀ (GD : Gdexec) s1,
          ⌜ledgerLdInv sWarmT AxSmodeProbe.sDrNopin sDw sD sVs cpu kk s1⌝ -∗
          ⌜s1.atK = (AxOpsem.grow GD i).length⌝ -∗ postLifting Φ i s1)) -∗
      wpd .MaybeStuck i ⟨.PHart cpu (riscvStep false) sWarmT.regs none ib, kk⟩ Φ :=
  wpdCldspStepOfLedger i Φ cpu ib kk sWarmT _ _ _ _ _ _ _ Rv sLedgerLdWarm Hgd Hrow

end sWarmWpd

/-! # 6. xv6-faithful leaves (A/D CLEAR, flags 0x0F): Svadu write-back -/

def pteLeafNoad (ppn : Nat) : Nat := (ppn <<< 10) ||| 0x0F
def sBytesNoad : List (Nat × Nat) :=
  sBytes.take 16 ++
  AxSmodeProbe.dwBytes (AxSmodeProbe.sRoot * 4096 + 2 * 8) (AxSmodeProbe.pteNl AxSmodeProbe.sL1) ++
  AxSmodeProbe.dwBytes (AxSmodeProbe.sL1 * 4096 + 0 * 8) (AxSmodeProbe.pteNl AxSmodeProbe.sL0) ++
  AxSmodeProbe.dwBytes (AxSmodeProbe.sL0 * 4096 + 0 * 8) (pteLeafNoad 0x80000) ++
  AxSmodeProbe.dwBytes (AxSmodeProbe.sL0 * 4096 + 1 * 8) (pteLeafNoad 0x80001)
def sMemNoad : BMap := AxSmodeProbe.memOfList sBytesNoad
def sAtNoad : ExecSt := ⟨sRegs sPc, sMemNoad, testDevs⟩

#kernel_eval mtr (riscvStep false) sAtNoad [] 0

/-- With A clear, each walk adds a re-read of the leaf + a PTE WRITE (the A-bit write-back):
10 reads + 2 writes on the cold ld (Lean: the re-read and the write are `AK_explicit`). -/
theorem sNoadCounts :
    (match mtr (riscvStep false) sAtNoad [] 0 with
     | .inl (l, ntlb) => ((l.filter fun e => e.1 == 0).length,
                          (l.filter fun e => e.1 == 1).length, ntlb)
     | .inr _ => (0, 0, 0)) = (10, 2, 2) := by
  decide +kernel

/-! # 7. COLD-TLB `wpd`: a generic chain of KNOWN-VALUE reads (walker PTE reads + the fetch),
then the data load

Each entry is `(pa, bytes, isFetch)` (deviation 4).  A walker read (`isFetch = false`, an
`AK_ttw` plain read) is a graph read at the next row position whose GRAPH VALUE is pinned to the
PTE bytes (`fetchGdOk`, as Rocq), discharged by the Lean-only `AxSmodeProbe.wpdKreadStep`; the
fetch (`isFetch = true`) is the pinned admin step at the SAME position (`wpdFetchStep`, Q8). -/

/-- (Lean-only) The row position after an entry. -/
def AxSmodeProbe.kpos : Bool → Nat → Nat
  | true, k => k
  | false, k => k + 1

/-- (Lean-only) How far a chain moves the row position: its number of graph reads. -/
def AxSmodeProbe.kadv : List (Int × List (BitVec 8) × Bool) → Nat
  | [] => 0
  | (_, _, true) :: r => AxSmodeProbe.kadv r
  | (_, _, false) :: r => AxSmodeProbe.kadv r + 1

/-- `knodeOk reads Fin m t`: `m` is a RAM read at the head of `reads` (PA, bytes, kind);
feeding the bytes, `erd` reaches the next node; at the end `Fin`. -/
def knodeOk (Dr Dw : List Register) (reads : List (Int × List (BitVec 8) × Bool))
    (Fin : SailM Unit → ExecSt → Prop) (m : SailM Unit) (t : ExecSt) : Prop :=
  match reads with
  | [] => Fin m t
  | (b, vs, f) :: r =>
    match m with
    | .impure (.ok (.memRead n _ req)) KK =>
      devAddr req.pa = false ∧ (classify req.access_kind).akLatest = false ∧
      (classify req.access_kind).akIfetch = f ∧ paZ req.pa = b ∧ vs.length = n ∧
      match erd Dr Dw (KK (.Ok (wordOfBytes n vs, none))) t with
      | some (m2, t2) => knodeOk Dr Dw r Fin m2 t2
      | none => False
    | _ => False

def kend (Dr Dw : List Register) (reads : List (Int × List (BitVec 8) × Bool))
    (m : SailM Unit) (t : ExecSt) : Option (SailM Unit × ExecSt) :=
  match reads with
  | [] => some (m, t)
  | (_, vs, _) :: r =>
    match m with
    | .impure (.ok (.memRead n _ _)) KK =>
      match erd Dr Dw (KK (.Ok (wordOfBytes n vs, none))) t with
      | some (m2, t2) => kend Dr Dw r m2 t2
      | none => none
    | _ => none

/-- Row-end set of the chain: strictly before any node reached after a read. -/
def kinv (cpu : CPU) (Dr Dw : List Register) (reads : List (Int × List (BitVec 8) × Bool))
    (m : SailM Unit) (t : ExecSt) (k : Nat) (s1 : Athread) : Prop :=
  match reads with
  | [] => False
  | (_, vs, f) :: r =>
    match m with
    | .impure (.ok (.memRead n _ _)) KK =>
      match erd Dr Dw (KK (.Ok (wordOfBytes n vs, none))) t with
      | some (m2, t2) =>
        (∃ ib2, Pbefore ⟨.PHart cpu m2 t2.regs none ib2, AxSmodeProbe.kpos f k⟩ s1) ∨
        kinv cpu Dr Dw r m2 t2 (AxSmodeProbe.kpos f k) s1
      | none => False
    | _ => False

/-- (Lean-only) The head node of a `knodeOk` chain. -/
theorem AxSmodeProbe.knodeOkCons (Dr Dw : List Register) (b : Int) (vs : List (BitVec 8))
    (f : Bool) (r : List (Int × List (BitVec 8) × Bool)) (Fin : SailM Unit → ExecSt → Prop)
    (m : SailM Unit) (t : ExecSt) (H : knodeOk Dr Dw ((b, vs, f) :: r) Fin m t) :
    ∃ (n va : Nat) (req : Mem_read_request n va Arch.pa Arch.translation Arch.arch_ak)
      (KK : Result (BitVec (8 * n) × Option Bool) Arch.abort → SailM Unit)
      (m2 : SailM Unit) (t2 : ExecSt),
      m = .impure (.ok (.memRead n va req)) KK ∧ devAddr req.pa = false ∧
      (classify req.access_kind).akLatest = false ∧ (classify req.access_kind).akIfetch = f ∧
      paZ req.pa = b ∧ vs.length = n ∧
      erd Dr Dw (KK (.Ok (wordOfBytes n vs, none))) t = some (m2, t2) ∧
      knodeOk Dr Dw r Fin m2 t2 := by
  cases m with
  | pure _ => simp [knodeOk] at H
  | impure call KK =>
    cases call with
    | error _ => simp [knodeOk] at H
    | ok o =>
      cases o
      case memRead n va req =>
        simp only [knodeOk] at H
        obtain ⟨h1, h2, h3, h4, h5, h6⟩ := H
        cases he : erd Dr Dw (KK (.Ok (wordOfBytes n vs, none))) t with
        | none => rw [he] at h6; exact h6.elim
        | some p =>
          obtain ⟨m2, t2⟩ := p
          rw [he] at h6
          exact ⟨n, va, req, KK, m2, t2, rfl, h1, h2, h3, h4, h5, he, h6⟩
      all_goals simp [knodeOk] at H

theorem AxSmodeProbe.kendCons (Dr Dw : List Register) (b : Int) (vs : List (BitVec 8)) (f : Bool)
    (r : List (Int × List (BitVec 8) × Bool)) (n va : Nat)
    (req : Mem_read_request n va Arch.pa Arch.translation Arch.arch_ak)
    (KK : Result (BitVec (8 * n) × Option Bool) Arch.abort → SailM Unit) (t : ExecSt)
    (m2 : SailM Unit) (t2 : ExecSt)
    (He : erd Dr Dw (KK (.Ok (wordOfBytes n vs, none))) t = some (m2, t2)) :
    kend Dr Dw ((b, vs, f) :: r) (.impure (.ok (.memRead n va req)) KK) t = kend Dr Dw r m2 t2 := by
  simp only [kend, He]

theorem AxSmodeProbe.kinvCons (cpu : CPU) (Dr Dw : List Register) (b : Int)
    (vs : List (BitVec 8)) (f : Bool) (r : List (Int × List (BitVec 8) × Bool)) (n va : Nat)
    (req : Mem_read_request n va Arch.pa Arch.translation Arch.arch_ak)
    (KK : Result (BitVec (8 * n) × Option Bool) Arch.abort → SailM Unit) (t : ExecSt)
    (m2 : SailM Unit) (t2 : ExecSt) (k : Nat) (s1 : Athread)
    (He : erd Dr Dw (KK (.Ok (wordOfBytes n vs, none))) t = some (m2, t2)) :
    kinv cpu Dr Dw ((b, vs, f) :: r) (.impure (.ok (.memRead n va req)) KK) t k s1 ↔
      ((∃ ib2, Pbefore ⟨.PHart cpu m2 t2.regs none ib2, AxSmodeProbe.kpos f k⟩ s1) ∨
        kinv cpu Dr Dw r m2 t2 (AxSmodeProbe.kpos f k) s1) := by
  simp only [kinv, He]

/-- (Lean-only) The node shape of `ldLoadOk`. -/
theorem AxSmodeProbe.ldLoadOkShape (D : List Register) (ldaddr : Int)
    (postLd : Int → RegFile → Prop) (m : SailM Unit) (t : ExecSt)
    (H : ldLoadOk D ldaddr postLd m t) :
    ∃ (nl val : Nat) (reql : Mem_read_request nl val Arch.pa Arch.translation Arch.arch_ak)
      (KK : Result (BitVec (8 * nl) × Option Bool) Arch.abort → SailM Unit),
      m = .impure (.ok (.memRead nl val reql)) KK := by
  cases m with
  | pure _ => simp [ldLoadOk] at H
  | impure call KK =>
    cases call with
    | error _ => simp [ldLoadOk] at H
    | ok o =>
      cases o
      case memRead n va req => exact ⟨n, va, req, KK, rfl⟩
      all_goals simp [ldLoadOk] at H

section kchain
variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [AxirisG GF] [Axpol]

/-- The per-read graph premises of a chain starting at row position `k` (deviation 4): a walker
read at `k` has Rocq's `fetchGdOk` (row item, graph value = image = PTE bytes) and the deposit
`fetchFlow`, and moves to `k + 1`; the fetch has `AxCjrWpd.fetchImgOk` at `k` and stays. -/
def kgdOk (i : Agent) : Nat → List (Int × List (BitVec 8) × Bool) → Prop
  | _, [] => True
  | k, (b, vs, true) :: r =>
    (∀ GD, rvwmoCatConsistent GD →
      AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜AxCjrWpd.fetchImgOk GD i k b vs⌝) ∧
    kgdOk i k r
  | k, (b, vs, false) :: r =>
    ((∀ GD, rvwmoCatConsistent GD →
       AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜fetchGdOk GD i k b vs⌝) ∧
     (∀ GD ls, rvwmoCatConsistent GD →
       AxirisG.gconstInterp (GF := GF) GD ∗ AxirisG.localInterp GD i k ls ⊢ fetchFlow GD i k)) ∧
    kgdOk i (k + 1) r

/-- (Lean-only) A KNOWN-VALUE plain RAM read (a walker read): Rocq's `wpd_fetch_step` at a
graph read.  Clause (a) reads the graph value, which `Hgd` pins to `vs`, so the continuation is
owed for `vs` only (at `k + 1`); clause (b) is empty; (c) Löb; (d) refuted by the row item. -/
theorem AxSmodeProbe.wpdKreadStep (Φ : Athread → IProp GF) (i : Agent) (cpu : CPU) (n va : Nat)
    (req : Mem_read_request n va Arch.pa Arch.translation Arch.arch_ak)
    (KK : Result (BitVec (8 * n) × Option Bool) Arch.abort → SailM Unit) (ib : Ibch) (k : Nat)
    (vs : List (BitVec 8)) (rs0 : RegFile)
    (Hdev : devAddr req.pa = false) (Hlat : (classify req.access_kind).akLatest = false)
    (Hnf : (classify req.access_kind).akIfetch = false)
    (Hgd : ∀ GD, rvwmoCatConsistent GD →
      AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜fetchGdOk GD i k (paZ req.pa) vs⌝)
    (Hflow : ∀ GD ls, rvwmoCatConsistent GD →
      AxirisG.gconstInterp (GF := GF) GD ∗ AxirisG.localInterp GD i k ls ⊢ fetchFlow GD i k) :
    ⊢ ∀ rs, ⌜regsAgree AxRunClose.pinReg rs0 rs⌝ -∗
      (∀ rs', ⌜regsAgree AxRunClose.pinReg rs0 rs'⌝ -∗
         wpd .MaybeStuck i ⟨.PHart cpu (KK (.Ok (wordOfBytes n vs, none))) rs' none ib, k + 1⟩ Φ) -∗
      wpd .MaybeStuck i ⟨.PHart cpu (.impure (.ok (.memRead n va req)) KK) rs none ib, k⟩ Φ := by
  iloeb as IH
  iintro %rs %HP C
  iapply (AxWpD.wpdMUnfoldStep rvwmoCatConsistent .MaybeStuck i _ Φ).2
  isplit
  · iapply (progressOblMaybestuck (GF := GF) i _).2
    itrivial
  unfold wpdMPreStepDef
  iintro %GD %ls ⟨%Hc, #Hg, Hloc⟩
  ihave Hok := (Hgd GD Hc) $$ Hg
  icases Hok with %Hok
  obtain ⟨⟨lb0, Hlb0, Hid0⟩, Hgv, -⟩ := Hok
  have Hadv0 : aidentAdvRd (aident lb0) = 1 := by rw [Hid0]; rfl
  isplit
  · -- (a) the walker read: its value is the graph's, pinned to `vs`
    iintro %id %K %Hst
    obtain ⟨lb, Hlb, Hid, -, HK⟩ := Hst
    simp only at Hlb
    rw [Hlb0, Option.some.injEq] at Hlb
    subst Hlb Hid
    simp only [Hadv0, ↓reduceIte]
    iintro %v %Hv %Hlenv
    obtain ⟨l, d, d', -, Hrv, Hps, Hk'⟩ := HK v Hlenv
    obtain ⟨tvs, Htl, rfl, Hp'⟩ :=
      AxLdspWpd.loadStepInv cpu n va req KK rs ib d l _ d' Hdev Hlat Hnf Hps
    simp only [wlRvals] at Hrv
    subst Hrv
    have hvs : tvs.map Prod.snd = vs := by
      rw [Hgv] at Hv
      exact (Option.some.inj Hv).symm
    rw [Hadv0] at Hk'
    have hKv : K (tvs.map Prod.snd) =
        ⟨.PHart cpu (KK (.Ok (wordOfBytes n vs, none))) rs none ib, k + 1⟩ := by
      cases hK : K (tvs.map Prod.snd) with
      | AThread p' k' =>
        rw [hK] at Hp' Hk'
        simp only at Hp' Hk'
        rw [Hp', Hk', hvs]
    rw [hKv]
    unfold wpEvStep
    iintro %na Hpg
    ihave Hf := (BI.wand_intro (Hflow GD ls Hc)) $$ Hg Hloc
    unfold fetchFlow
    imod Hf $$ %na Hpg with Hf
    imodintro
    inext
    imod Hf with ⟨%R, %nu, %nuu, %ls', Hs, Hfe, Hna, Hl⟩
    imodintro
    iexists (), R, nu, nuu, ls'
    isplitr
    · ipureintro
      trivial
    iframe Hs Hna Hl
    isplitl [Hfe]
    · iapply (flowEqDynMono GD (i, k) _ nu R
        iprop(R ∗ ⌜graphValue GD (i, k) = some (tvs.map Prod.snd)⌝))
      · inext
        iintro HR
        iframe HR
        ipureintro
        exact Hv
      · iexact Hfe
    · iapply C $$ %rs %HP
  isplit
  · -- (b) no program step exists at a plain read node
    iintro %l %s' %Hst %Hpin
    have hfalse : False := by
      obtain ⟨d, d', hps⟩ := astepProgPstep _ _ _ _ Hst
      obtain ⟨tvs, -, hl, -⟩ :=
        AxLdspWpd.loadStepInv cpu n va req KK rs ib d l _ d' Hdev Hlat Hnf hps
      subst hl
      cases Hst with
      | AStepAdmin _ _ _ _ _ _ hadm _ => exact hadm
      | AStepWrite _ _ _ _ _ _ _ _ hwr _ _ _ => simp [wlWr] at hwr
      | AStepFence _ _ _ _ _ _ _ _ hf _ _ => simp [wlFence] at hf
    exact hfalse.elim
  isplit
  · -- (c) the PLIC wire: back to the read node, Löb
    iintro %s' %Hw
    obtain ⟨hk, hp⟩ := awireAeqv _ _ Hw
    obtain ⟨p', k'⟩ := s'
    simp only at hk hp
    subst hk
    match p', hp with
    | .PHart c m' rs' fn' ib', hp =>
      obtain ⟨rfl, rfl, rfl, rfl, hag⟩ := hp
      unfold wpSkipStep
      iintro %na Hna
      imodintro
      inext
      imodintro
      iexists ls
      iframe Hna Hloc
      iapply IH $$ %rs' %(regsAgreeTrans _ _ _ _ HP (regsAgreeSym _ _ _ hag)) C
  · -- (d) row end: the read's item sits at `k`
    iintro %Heq
    have h1 := lookup_lt_Some Hlb0
    simp only at Heq
    omega

theorem wpdKnode (Φ : Athread → IProp GF) (i : Agent) (cpu : CPU) (Dr Dw : List Register)
    (HDr : Register.sig_seip ∉ Dr) (HDrm : Register.sig_meip ∉ Dr)
    (Fin : SailM Unit → ExecSt → Prop) :
    ∀ (reads : List (Int × List (BitVec 8) × Bool)) (m : SailM Unit) (t : ExecSt) (ib : Ibch)
      (k : Nat) (s : Athread),
      knodeOk Dr Dw reads Fin m t → kgdOk (GF := GF) i k reads →
      ⊢ ⌜Qat ⟨.PHart cpu m t.regs none ib, k⟩ s⌝ -∗
        ((∀ (m' : SailM Unit) (t' : ExecSt) (ib' : Ibch) (s' : Athread), ⌜Fin m' t'⌝ -∗
            ⌜kend Dr Dw reads m t = some (m', t')⌝ -∗
            ⌜Qat ⟨.PHart cpu m' t'.regs none ib', k + AxSmodeProbe.kadv reads⟩ s'⌝ -∗
            wpd .MaybeStuck i s' Φ) ∧
         (∀ (GD : Gdexec) s1, ⌜kinv cpu Dr Dw reads m t k s1⌝ -∗
            ⌜s1.atK = (AxOpsem.grow GD i).length⌝ -∗ postLifting Φ i s1)) -∗
        wpd .MaybeStuck i s Φ := by
  intro reads
  induction reads with
  | nil =>
    intro m t ib k s Hok _
    iintro %Hq R
    icases R with ⟨R, -⟩
    iapply R $$ %m %t %ib %s %Hok %rfl %Hq
  | cons e r IH =>
    obtain ⟨b, vs, f⟩ := e
    intro m t ib k s Hok Hgd
    obtain ⟨n, va, req, KK, m2, t2, rfl, Hdev, Hlat, Hfe, Hpa, Hlen, He, Hk⟩ :=
      AxSmodeProbe.knodeOkCons Dr Dw b vs f r Fin m t Hok
    have Hend := AxSmodeProbe.kendCons Dr Dw b vs f r n va req KK t m2 t2 He
    iintro %Hq R
    obtain ⟨p2, k2⟩ := s
    obtain ⟨hk, hp⟩ := Hq
    simp only at hk hp
    subst k2
    match p2, hp with
    | .PHart c2 m2' rs2 fn2 ib2, hp =>
      obtain ⟨hc, hm, hf, hi, hag⟩ := hp
      subst c2 m2' fn2 ib2
      cases f with
      | true =>
        obtain ⟨Hg0, Hgr⟩ := Hgd
        have Hg0' : ∀ GD, rvwmoCatConsistent GD →
            AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜AxCjrWpd.fetchImgOk GD i k (paZ req.pa) vs⌝ := by
          rw [Hpa]; exact Hg0
        obtain ⟨ib3, -, -, Hrun⟩ := erdGstep Dr Dw _ HDr HDrm t ib _ _ He cpu k
        iapply (wpdFetchStep Φ i cpu n va req KK ib k vs t.regs Hdev Hfe Hlen Hg0') $$
          %rs2 %(regsAgreeSym _ _ _ hag)
        iintro %rs' %hag'
        iapply (wpdRunTo Φ i _ _ Hrun) $$
          %⟨.PHart cpu (KK (.Ok (wordOfBytes n vs, none))) rs' none ib, k⟩
          %⟨rfl, rfl, rfl, rfl, rfl, regsAgreeSym _ _ _ hag'⟩
        isplit
        · iintro %s3 %Hq3
          iapply (IH m2 t2 ib3 k s3 Hk Hgr) $$ %Hq3
          isplit
          · icases R with ⟨R, -⟩
            iintro %m' %t' %ib' %s' %Hfin %Hend' %Hq'
            iapply R $$ %m' %t' %ib' %s' %Hfin %(Hend.trans Hend') %Hq'
          · icases R with ⟨-, R⟩
            iintro %GD %s1 %Hinv %Hl
            iapply R $$ %GD %s1
              %((AxSmodeProbe.kinvCons cpu Dr Dw b vs true r n va req KK t m2 t2 k s1 He).2
                (.inr Hinv)) %Hl
        · icases R with ⟨-, R⟩
          iintro %GD %s1 %Hb %Hl
          iapply R $$ %GD %s1
            %((AxSmodeProbe.kinvCons cpu Dr Dw b vs true r n va req KK t m2 t2 k s1 He).2
              (.inl ⟨ib3, Hb⟩)) %Hl
      | false =>
        obtain ⟨⟨Hg0, Hfl⟩, Hgr⟩ := Hgd
        have Hg0' : ∀ GD, rvwmoCatConsistent GD →
            AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜fetchGdOk GD i k (paZ req.pa) vs⌝ := by
          rw [Hpa]; exact Hg0
        obtain ⟨ib3, -, -, Hrun⟩ := erdGstep Dr Dw _ HDr HDrm t ib _ _ He cpu (k + 1)
        iapply (AxSmodeProbe.wpdKreadStep Φ i cpu n va req KK ib k vs t.regs Hdev Hlat Hfe Hg0'
          Hfl) $$ %rs2 %(regsAgreeSym _ _ _ hag)
        iintro %rs' %hag'
        iapply (wpdRunTo Φ i _ _ Hrun) $$
          %⟨.PHart cpu (KK (.Ok (wordOfBytes n vs, none))) rs' none ib, k + 1⟩
          %⟨rfl, rfl, rfl, rfl, rfl, regsAgreeSym _ _ _ hag'⟩
        isplit
        · iintro %s3 %Hq3
          iapply (IH m2 t2 ib3 (k + 1) s3 Hk Hgr) $$ %Hq3
          isplit
          · icases R with ⟨R, -⟩
            iintro %m' %t' %ib' %s' %Hfin %Hend' %Hq'
            have Hq'' : Qat ⟨.PHart cpu m' t'.regs none ib',
                k + AxSmodeProbe.kadv ((b, vs, false) :: r)⟩ s' := by
              simp only [AxSmodeProbe.kadv]
              rw [show k + (AxSmodeProbe.kadv r + 1) = k + 1 + AxSmodeProbe.kadv r by omega]
              exact Hq'
            iapply R $$ %m' %t' %ib' %s' %Hfin %(Hend.trans Hend') %Hq''
          · icases R with ⟨-, R⟩
            iintro %GD %s1 %Hinv %Hl
            iapply R $$ %GD %s1
              %((AxSmodeProbe.kinvCons cpu Dr Dw b vs false r n va req KK t m2 t2 k s1 He).2
                (.inr Hinv)) %Hl
        · icases R with ⟨-, R⟩
          iintro %GD %s1 %Hb %Hl
          iapply R $$ %GD %s1
            %((AxSmodeProbe.kinvCons cpu Dr Dw b vs false r n va req KK t m2 t2 k s1 He).2
              (.inl ⟨ib3, Hb⟩)) %Hl
    | .PDisk _, hp => exact (hp : False).elim

end kchain

/-! # 8. The concrete COLD-TLB S-mode ld: ledger + `wpd` -/

def pteBv (v : Nat) : List (BitVec 8) :=
  (List.range 8).map fun j => BitVec.ofNat 8 ((v >>> (8 * j)) &&& 0xFF)

/-- The 7 known-value reads before the data load: walk(fetch) ×3, fetch, walk(data) ×3 — PAs,
bytes, and (Lean, deviation 4) whether the read is the fetch. -/
def sWalk7 : List (Int × List (BitVec 8) × Bool) :=
  [ ((AxSmodeProbe.sRoot * 4096 + 16 : Nat), pteBv (AxSmodeProbe.pteNl AxSmodeProbe.sL1), false),
    ((AxSmodeProbe.sL1 * 4096 : Nat), pteBv (AxSmodeProbe.pteNl AxSmodeProbe.sL0), false),
    ((AxSmodeProbe.sL0 * 4096 : Nat), pteBv (AxSmodeProbe.pteLeaf 0x80000), false),
    ((sPc : Nat), sVs, true),
    ((AxSmodeProbe.sRoot * 4096 + 16 : Nat), pteBv (AxSmodeProbe.pteNl AxSmodeProbe.sL1), false),
    ((AxSmodeProbe.sL1 * 4096 : Nat), pteBv (AxSmodeProbe.pteNl AxSmodeProbe.sL0), false),
    ((AxSmodeProbe.sL0 * 4096 + 8 : Nat), pteBv (AxSmodeProbe.pteLeaf 0x80001), false) ]

/-- THE COLD S-MODE LOAD LEDGER (per pin answers; Lean: two wire reads, `sig_meip` answer `v'`
then `sig_seip` answer `v`, deviation 1): from the boundary, `erd` reaches the first walker
read; the 7 known reads chain by `erd`; the 8th read is the data load at `sLdaddr`, after which
`epure` reaches `.pure ()` for EVERY loaded word with PC = sPc + 4. -/
def sColdBranch (v' v : BitVec 1) : Prop :=
  match AxEpiLedger.toPin (riscvStep false) (sAt sPc) with
  | some (m0, t0) =>
    match AxEpiLedger.toPin (AxEpiLedger.ansMeip m0 v') t0 with
    | some (m1, t1) =>
      match erd AxSmodeProbe.sDrNopin sDw (ansSeip m1 v) t1 with
      | some (q, t2) => knodeOk AxSmodeProbe.sDrNopin sDw sWalk7 (ldLoadOk sD sLdaddr sPost) q t2
      | none => False
    | none => False
  | none => False

/-- (Lean-only) The boolean twin of `knodeOk`, with a boolean end check. -/
def AxSmodeProbe.knodeOkB (Dr Dw : List Register) (reads : List (Int × List (BitVec 8) × Bool))
    (FinB : SailM Unit → ExecSt → Bool) (m : SailM Unit) (t : ExecSt) : Bool :=
  match reads with
  | [] => FinB m t
  | (b, vs, f) :: r =>
    match m with
    | .impure (.ok (.memRead n _ req)) KK =>
      !devAddr req.pa && !(classify req.access_kind).akLatest &&
      decide ((classify req.access_kind).akIfetch = f) && decide (paZ req.pa = b) &&
      decide (vs.length = n) &&
      match erd Dr Dw (KK (.Ok (wordOfBytes n vs, none))) t with
      | some (m2, t2) => AxSmodeProbe.knodeOkB Dr Dw r FinB m2 t2
      | none => false
    | _ => false

theorem AxSmodeProbe.knodeOkOfB (Dr Dw : List Register) (Fin : SailM Unit → ExecSt → Prop)
    (FinB : BitVec 64 → SailM Unit → ExecSt → Bool)
    (HF : ∀ m t, (∀ x, FinB x m t = true) → Fin m t) :
    ∀ (reads : List (Int × List (BitVec 8) × Bool)) (m : SailM Unit) (t : ExecSt),
      (∀ x, AxSmodeProbe.knodeOkB Dr Dw reads (FinB x) m t = true) →
      knodeOk Dr Dw reads Fin m t := by
  intro reads
  induction reads with
  | nil =>
    intro m t H
    exact HF m t H
  | cons e r IH =>
    obtain ⟨b, vs, f⟩ := e
    intro m t H
    cases m with
    | pure _ => exact absurd (H 0) (by simp [AxSmodeProbe.knodeOkB])
    | impure call KK =>
      cases call with
      | error _ => exact absurd (H 0) (by simp [AxSmodeProbe.knodeOkB])
      | ok o =>
        cases o
        case memRead n va req =>
          cases he : erd Dr Dw (KK (.Ok (wordOfBytes n vs, none))) t with
          | none =>
            have h0 := H 0
            simp only [AxSmodeProbe.knodeOkB, he, Bool.and_false] at h0
            exact absurd h0 Bool.false_ne_true
          | some p =>
            obtain ⟨m2, t2⟩ := p
            have h0 := H 0
            simp only [AxSmodeProbe.knodeOkB, he, Bool.and_eq_true, Bool.not_eq_true',
              decide_eq_true_eq] at h0
            obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, -⟩ := h0
            simp only [knodeOk, he]
            refine ⟨h1, h2, h3, h4, h5, IH m2 t2 (fun x => ?_)⟩
            have hx := H x
            simp only [AxSmodeProbe.knodeOkB, he, Bool.and_eq_true] at hx
            exact hx.2
        all_goals exact absurd (H 0) (by simp [AxSmodeProbe.knodeOkB])

/-- (Lean-only) The boolean twin of `sColdBranch`, at one free 64-bit loaded word `x`. -/
noncomputable def AxSmodeProbe.sColdBranchB (v' v : BitVec 1) (x : BitVec 64) : Bool :=
  match AxEpiLedger.toPin (riscvStep false) (sAt sPc) with
  | some (m0, t0) =>
    match AxEpiLedger.toPin (AxEpiLedger.ansMeip m0 v') t0 with
    | some (m1, t1) =>
      match erd AxSmodeProbe.sDrNopin sDw (ansSeip m1 v) t1 with
      | some (q, t2) =>
        AxSmodeProbe.knodeOkB AxSmodeProbe.sDrNopin sDw sWalk7
          (fun m t => AxEpiLedger.ldLoadB sD sLdaddr AxSmodeProbe.sPostB m t x) q t2
      | none => false
    | none => false
  | none => false

theorem AxSmodeProbe.sColdBranchOfB (v' v : BitVec 1)
    (H : ∀ x, AxSmodeProbe.sColdBranchB v' v x = true) : sColdBranch v' v := by
  unfold sColdBranch
  cases h1 : AxEpiLedger.toPin (riscvStep false) (sAt sPc) with
  | none =>
    have h0 := H 0
    simp only [AxSmodeProbe.sColdBranchB, h1] at h0
    exact absurd h0 Bool.false_ne_true
  | some p =>
    obtain ⟨m0, t0⟩ := p
    dsimp only
    cases h2 : AxEpiLedger.toPin (AxEpiLedger.ansMeip m0 v') t0 with
    | none =>
      have h0 := H 0
      simp only [AxSmodeProbe.sColdBranchB, h1, h2] at h0
      exact absurd h0 Bool.false_ne_true
    | some p2 =>
      obtain ⟨m1, t1⟩ := p2
      dsimp only
      cases h3 : erd AxSmodeProbe.sDrNopin sDw (ansSeip m1 v) t1 with
      | none =>
        have h0 := H 0
        simp only [AxSmodeProbe.sColdBranchB, h1, h2, h3] at h0
        exact absurd h0 Bool.false_ne_true
      | some p3 =>
        obtain ⟨q, t2⟩ := p3
        dsimp only
        refine AxSmodeProbe.knodeOkOfB _ _ _ _
          (fun m t hx => AxEpiLedger.ldLoadOfB sD sLdaddr AxSmodeProbe.sPostB sPost
            AxSmodeProbe.sPostOfB m t hx) _ _ _ (fun x => ?_)
        have hx := H x
        simp only [AxSmodeProbe.sColdBranchB, h1, h2, h3] at hx
        exact hx

theorem sColdBranch00 : sColdBranch 0#1 0#1 :=
  AxSmodeProbe.sColdBranchOfB _ _ (by intro x; ax_epi_ledger_krfl)
theorem sColdBranch01 : sColdBranch 0#1 1#1 :=
  AxSmodeProbe.sColdBranchOfB _ _ (by intro x; ax_epi_ledger_krfl)
theorem sColdBranch10 : sColdBranch 1#1 0#1 :=
  AxSmodeProbe.sColdBranchOfB _ _ (by intro x; ax_epi_ledger_krfl)
theorem sColdBranch11 : sColdBranch 1#1 1#1 :=
  AxSmodeProbe.sColdBranchOfB _ _ (by intro x; ax_epi_ledger_krfl)

theorem sSeipAt : seipAt (sAt sPc) = true := by decide +kernel
theorem sHead : isSeipNode (riscvStep false) = false := by decide +kernel
theorem sSeipDr : decide (Register.sig_seip ∈ AxSmodeProbe.sDrNopin) = false := by decide +kernel
theorem sSeipD : decide (Register.sig_seip ∈ sD) = false := by decide +kernel
theorem AxSmodeProbe.sMeipDr : decide (Register.sig_meip ∈ AxSmodeProbe.sDrNopin) = false := by
  decide +kernel
theorem AxSmodeProbe.sMeipD : decide (Register.sig_meip ∈ sD) = false := by decide +kernel

/-- (Lean-only) The cold branch at the two computed pin nodes. -/
theorem AxSmodeProbe.sColdBranchAt (km : RegisterType Register.sig_meip → SailM Unit)
    (t0 : ExecSt) (v' : BitVec 1) (k0 : RegisterType Register.sig_seip → SailM Unit)
    (t1 : ExecSt)
    (Hts : AxEpiLedger.toPin (riscvStep false) (sAt sPc)
      = some (.impure (.ok (.regRead Register.sig_meip)) km, t0))
    (Hts1 : AxEpiLedger.toPin (km v') t0
      = some (.impure (.ok (.regRead Register.sig_seip)) k0, t1)) (v : BitVec 1) :
    ∃ q t2, erd AxSmodeProbe.sDrNopin sDw (k0 v) t1 = some (q, t2) ∧
      knodeOk AxSmodeProbe.sDrNopin sDw sWalk7 (ldLoadOk sD sLdaddr sPost) q t2 := by
  have Hc : sColdBranch v' v := by
    rcases bv1Cases v' with rfl | rfl <;> rcases bv1Cases v with rfl | rfl
    · exact sColdBranch00
    · exact sColdBranch01
    · exact sColdBranch10
    · exact sColdBranch11
  unfold sColdBranch at Hc
  rw [Hts] at Hc
  dsimp only at Hc
  rw [AxEpiLedger.ansMeipNode, Hts1] at Hc
  dsimp only at Hc
  rw [AxEpiLedger.ansSeipNode] at Hc
  cases he : erd AxSmodeProbe.sDrNopin sDw (k0 v) t1 with
  | none => rw [he] at Hc; exact Hc.elim
  | some p =>
    obtain ⟨q, t2⟩ := p
    rw [he] at Hc
    exact ⟨q, t2, rfl, Hc⟩

/-- Row-end set of the cold ld (Lean: the two boundary splits, deviation 1). -/
def sColdInv (cpu : CPU) (kk : Nat) (s1 : Athread) : Prop :=
  ∃ (km : RegisterType Register.sig_meip → SailM Unit) (t0 : ExecSt) (ib0 : Ibch),
    AxEpiLedger.toPin (riscvStep false) (sAt sPc)
      = some (.impure (.ok (.regRead Register.sig_meip)) km, t0) ∧
    (Pseip (AxEpiLedger.meipNode cpu km t0.regs ib0 kk) (AxEpiLedger.seipExit cpu km t0 kk) s1 ∨
     ∃ (v' : BitVec 1) (k0 : RegisterType Register.sig_seip → SailM Unit) (t1 : ExecSt)
       (ib1 : Ibch),
       AxEpiLedger.toPin (km v') t0 = some (.impure (.ok (.regRead Register.sig_seip)) k0, t1) ∧
       (Pseip (seipNode cpu k0 t1.regs ib1 kk) (erdExit AxSmodeProbe.sDrNopin sDw cpu k0 t1 kk)
          s1 ∨
        ∃ (v : BitVec 1) (q : SailM Unit) (t2 : ExecSt),
          erd AxSmodeProbe.sDrNopin sDw (k0 v) t1 = some (q, t2) ∧
          (kinv cpu AxSmodeProbe.sDrNopin sDw sWalk7 q t2 kk s1 ∨
           ∃ (nl val : Nat) (reql : Mem_read_request nl val Arch.pa Arch.translation Arch.arch_ak)
             (KK : Result (BitVec (8 * nl) × Option Bool) Arch.abort → SailM Unit) (t' : ExecSt)
             (x : BitVec (8 * nl)) (sEnd : ExecSt) (ib' : Ibch),
             kend AxSmodeProbe.sDrNopin sDw sWalk7 q t2
               = some (.impure (.ok (.memRead nl val reql)) KK, t') ∧
             epure sD (KK (.Ok (x, none))) t' = some ((), sEnd) ∧
             Pbefore ⟨.PHart cpu (.pure ()) sEnd.regs none ib', kk + 6 + 1⟩ s1)))

section sColdWpd
variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [AxirisG GF] [Axpol]

/-- `wpd` of the S-mode `ld x1, 8(x2)` at the COLD-TLB concrete Sv39 state: 7 graph reads at
row positions kk .. kk+6 (the six walker reads pinned by `kgdOk`, the data load demonic at
kk+6), the fetch a pinned admin step at kk+3 (deviation 4). -/
theorem wpdSldCold (i : Agent) (Φ : Athread → IProp GF) (cpu : CPU) (ib : Ibch) (kk : Nat)
    (Rv : Gdexec → List (BitVec 8) → IProp GF)
    (Hgd : kgdOk (GF := GF) i kk sWalk7)
    (Hrow : ∀ GD, rvwmoCatConsistent GD →
      AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜loadRowOk GD i (kk + 6)⌝) :
    ⊢ (∀ (GD : Gdexec) (ls : AxirisG.logTsT GF) (v : List (BitVec 8)),
         ⌜rvwmoCatConsistent GD⌝ -∗ □ AxirisG.gconstInterp GD -∗
         AxirisG.localInterp GD i (kk + 6) ls -∗
         ⌜graphValue GD (i, kk + 6) = some v⌝ -∗ loadFlow GD i (kk + 6) (Rv GD v)) -∗
      ((∀ s', ⌜RetLd cpu sPost (kk + 6 + 1) s'⌝ -∗ wpd .MaybeStuck i s' Φ) ∧
       (∀ (GD : Gdexec) s1, ⌜sColdInv cpu kk s1⌝ -∗
          ⌜s1.atK = (AxOpsem.grow GD i).length⌝ -∗ postLifting Φ i s1)) -∗
      wpd .MaybeStuck i ⟨.PHart cpu (riscvStep false) (sAt sPc).regs none ib, kk⟩ Φ := by
  have HDr := of_decide_eq_false sSeipDr
  have HDrm := of_decide_eq_false AxSmodeProbe.sMeipDr
  have HD := of_decide_eq_false sSeipD
  have HDm := of_decide_eq_false AxSmodeProbe.sMeipD
  obtain ⟨km, t0, Hts⟩ := AxEpiLedger.seipAtSpec _ sSeipAt
  have Hnext := AxEpiLedger.seipAtNext _ km t0 sSeipAt Hts
  obtain ⟨ib0, Hr0⟩ := AxEpiLedger.toPinGstep _ (sAt sPc) ib _ _ Hts cpu kk
  iintro F R
  iapply (AxEpiLedger.wpdOfSplitFrom i Φ _ _ _
    (AxEpiLedger.pseipStart cpu _ (sAt sPc).regs ib kk _ (AxEpiLedger.seipExit cpu km t0 kk) Hr0)
    (AxEpiLedger.meipN0Ok cpu km t0 ib0 kk Hnext))
  isplit
  · iintro %s2 %HQ
    obtain ⟨q, ⟨v', k0, t1, ib1, Hts1, rfl⟩, Hq⟩ := HQ
    have Hb := AxSmodeProbe.sColdBranchAt km t0 v' k0 t1 Hts Hts1
    have Herd : ∀ v, ∃ q t2, erd AxSmodeProbe.sDrNopin sDw (k0 v) t1 = some (q, t2) := by
      intro v
      obtain ⟨q, t2, he, -⟩ := Hb v
      exact ⟨q, t2, he⟩
    iapply (AxEpiLedger.wpdOfSplitFrom i Φ s2 _ (erdExit AxSmodeProbe.sDrNopin sDw cpu k0 t1 kk)
      (.inr (.inl Hq)) (AxEpiLedger.seipN0Ok cpu k0 t1 ib1 kk _ _ HDr HDrm Herd))
    isplit
    · iintro %s3 %HQ3
      obtain ⟨q3, ⟨v, qm, t2, ib2, He, rfl, -⟩, Hs3⟩ := HQ3
      obtain ⟨qm', t2', He', Hk⟩ := Hb v
      rw [He, Option.some.injEq, Prod.mk.injEq] at He'
      obtain ⟨rfl, rfl⟩ := He'
      iapply (wpdKnode Φ i cpu _ sDw HDr HDrm _ sWalk7 qm t2 ib2 kk s3 Hk Hgd) $$ %Hs3
      isplit
      · iintro %m' %t' %ib' %s' %Hfin %Hend %Hq'
        obtain ⟨nl, val, reql, KK, rfl⟩ := AxSmodeProbe.ldLoadOkShape _ _ _ _ _ Hfin
        obtain ⟨Hdevl, Hlatl, Hnfl, -, Hn, Hx⟩ := ldLoadOkNode _ _ _ _ _ _ _ _ Hfin
        have Hpost : ∀ x : BitVec (8 * nl), ∃ sEnd : ExecSt,
            epure sD (KK (.Ok (x, none))) t' = some ((), sEnd) := by
          intro x
          obtain ⟨sEnd, Hep, -⟩ := Hx x
          exact ⟨sEnd, Hep⟩
        have Hq'' : Qat ⟨.PHart cpu (.impure (.ok (.memRead nl val reql)) KK) t'.regs none ib',
            kk + 6⟩ s' := Hq'
        iapply (wpdLoadThenRetN Φ i cpu nl val reql KK ib' (kk + 6) t' sD Rv Hdevl Hlatl Hn Hnfl
          Hrow HD HDm Hpost) $$ %s' %Hq'' F
        isplit
        · icases R with ⟨R, -⟩
          iintro %x %sEnd %ib3 %s'' %Hep %Hs''
          obtain ⟨sEnd', Hep', Hpost'⟩ := Hx x
          rw [Hep, Option.some.injEq, Prod.mk.injEq] at Hep'
          obtain ⟨-, rfl⟩ := Hep'
          iapply R $$ %s'' %⟨_, sEnd.regs, ib3, Hpost', Hs''⟩
        · icases R with ⟨-, R⟩
          iintro %x %sEnd %ib3 %GD %s1 %Hep %Hs1 %Hl
          iapply R $$ %GD %s1
            %⟨km, t0, ib0, Hts, .inr ⟨v', k0, t1, ib1, Hts1, .inr ⟨v, qm, t2, He,
              .inr ⟨nl, val, reql, KK, t', x, sEnd, ib3, Hend, Hep, Hs1⟩⟩⟩⟩ %Hl
      · icases R with ⟨-, R⟩
        iintro %GD %s1 %Hinv %Hl
        iapply R $$ %GD %s1
          %⟨km, t0, ib0, Hts, .inr ⟨v', k0, t1, ib1, Hts1, .inr ⟨v, qm, t2, He, .inl Hinv⟩⟩⟩ %Hl
    · icases R with ⟨-, R⟩
      iintro %GD %s1 %Hs1 %Hl
      iapply R $$ %GD %s1 %⟨km, t0, ib0, Hts, .inr ⟨v', k0, t1, ib1, Hts1, .inl Hs1⟩⟩ %Hl
  · icases R with ⟨-, R⟩
    iintro %GD %s1 %Hs1 %Hl
    iapply R $$ %GD %s1 %⟨km, t0, ib0, Hts, .inl Hs1⟩ %Hl

end sColdWpd

end Weak
