/-
Weak: **track F, the AxSL instruction bridge — PART B** (`AxFetch5`): §4, the `c.jr ra` CONTROL
GATE — `WeakDeps.depsCtrl` / `WeakEvLang.erwOf` into `AxDeps.dstepT`'s `LCtrl` arm and
`AxGate.gateSrcs` — and §4.5–§4.8, the small-step run of `execute_JALR` to its `nextPC` write
that DISCHARGES the gate's one open hypothesis (`ra`'s GPR number already in the dynamic read set).

Rocq: `iris/AxFetch.v` @ xxvzwolszwmp, lines 3819–4880 (§4 "THE c.jr ra CTRL GATE" through §4.8
`af_cjr_epilogue_gate_srcs'`).  Part A is `Weak.AxFetch1` (its header describes the whole port).

## What this file proves (the Rocq comments, in substance)

* §4: an ordinary `jalr`'s `nextPC` write carries its base register's provenance as a REAL
  `LCtrl` source: `depsCtrl (ORjalr rd rs1) = [DReg rs1]` for `rs1 ≠ 0`, `erwOf`'s `nextPC` arm
  is `ERWctrl (erwSrcs [DReg rs1] rds)` over the WHOLE dynamic read set `rds`, so given
  `rs1 ∈ rds` the ctrl node's sources contain `DReg rs1`, `dstepT`'s `LCtrl` arm appends `rs1`'s
  current provenance into `dtCtl` (`afCjrCtrlSrc`), those positions are `AxGate.gateSrcs`
  (`afCjrGateSrcs`), and a register-only row middle that never writes `rs1` preserves them
  (`afDtProvPreservedRow`, `afCjrEpilogueGateSrcs`).
* §4.5–§4.6: the one-step admin facts of `execute_JALR`'s register traffic: the config reads
  (`cur_privilege`, `mseccfg`, `nextPC`, `misa`) are NON-carriers (`eregNum … = none`) so they leave
  the channel unchanged; `ra`'s own GPR read IS a carrier at exactly its number
  (`afCjrRaGprCarrier`) and appends it (`afCjrRaGprRead`); `set_next_pc` is one silent
  `branchAnnounce` step to the `nextPC` `regWrite` node (`afCjrSetNextPcStep`); away from a
  boundary the read set only grows (`afPnodeStepIbRdsApp`/`Mono`).
* §4.7: the pure sub-computations of the `Ext_Zicfilp`/`Ext_Zca` probes as TERM equalities.
* §4.8: `afCjrRdsAtNextpc` — ONE admin run from `execute_JALR (zeros 12) (Regidx i) rd >>= f` to
  the `nextPC` `regWrite` node with `i.toNat` already in the landing read set (M-mode,
  `mseccfg.MLPE` clear, `misa.C` set; both bit-1 arms of `jump_to` reach the write), and the
  hypothesis-free gate corollaries `afCjrCtrlSrc'`/`afCjrGateSrcs'`/`afCjrEpilogueGateSrcs'`.

## O2 Stage C

Nothing in this range is a fetch: the run of §4.8 is the EXECUTE part of `c.jr`, a register-only
admin run that consumes no row position (all steps `AStepAdmin`, position `kpos` kept).  The opax
relations lose their `T`/`img` oracle parameters (`AxFetch1` deviation 2).

## Deviations from Rocq

1. VOCABULARY (as `AxFetch1` deviation 1 and `WeakLeafJump` deviation 1): `astep_prog row Tt img`
   ↦ `AxOpsem.astepProg row`; the device state `d : dev_state` ↦ `d : Efab`; `oib32` ↦ `Ibch`;
   `ib_rds`/`ib_rd` ↦ `.ibRds`/`ibRd`; `ereg_num` ↦ `eregNum`; `erw_of` ↦ `erwOf`;
   `Defs.bind m f` ↦ `m >>= f`; `Defs.read_reg r` ↦ `readReg r`; `register_lookup r rs` ↦ `rs r`;
   `mword n` ↦ `BitVec n`; `uint i` ↦ `i.toNat` (so `Z.to_nat (uint i)` ↦ `i.toNat`);
   `eq_vec (_get_Misa_C w) 'b"1"` ↦ `(_get_Misa_C w == 1#1)`; `zeros' 12` ↦ `zeros (n := 12)`;
   `dt_prov s !! r` ↦ `s.dtProv r` (a total map); `dstate_t_after` ↦ `dstateTAfter`; `agent` ↦
   `Agent`; `default ib oib` ↦ `oib.getD ib`.
2. GPR REGISTERS: Lean has no `gpr_of_Z`; the Lean-only `AxFetch5.gprReg i` (the 31-way
   `x1 … x31` choice `rX` makes; `0` ↦ `x31`, never used since every statement takes
   `i.toNat ≠ 0`).  The value `register_lookup (R_bitvector_64 (gpr_of_Z (uint i))) rs` is
   `uxaXget rs i` (= `ExecSt.gpr`), which avoids a dependent `RegisterType (gprReg i)`.
3. THE CONFIG READS keep the bank `ib` in their successor (Rocq states `ib` too); Lean's step
   records `ibRd ib r`, definitionally `ib` for a non-carrier.
4. §4.7 RECURSION GUARDS: Lean's `currentlyEnabled`/`get_xLPE` are well-founded definitions
   without fuel and `hartSupports` is a pure `Bool` function.  So: `af_cjr_bind_assert_exp'`
   ↦ `afCjrBindAssertExp'` over Lean's plain `assert` (`assert true msg >>= f = f ()`); the
   `hartSupports` "pure" lemmas and the `_rec_hartSupports … acc` leaves (`af_cjr_rec_hs_*`) are
   the `Bool` facts `hartSupports .Ext_X = b` (no `Acc` witness, no positivity premises `Hk`/`Hk1`);
   `af_cjr_rec_cE_Zicsr_pure`/`af_cjr_rec_cE_C_misa_pure`/`af_cjr_get_xLPE_machine_pure` are
   stated at `currentlyEnabled`/`get_xLPE` themselves (no `k`/`acc`/`Hk`).  The Zicsr leaf's
   value is `pure true`; `af_cjr_rec_hs_Zcf_pure`'s value `andb false (xlen =? 32)` is stated as
   `false`.
5. `af_cjr_bind_assoc` and its three head-symbol twins: Lean's `>>=` on `SailM` IS `FreeM.bind`
   up to instance unfolding; the four are kept (`>>=`/`FreeM.bind` at either level) and proved by
   the library's `bind_assoc`.  The Ltac `af_cjr_bindassoc` ↦ tactic `axfetch5_bindassoc`.
6. §4.8: the Rocq proof's goal-side rewriting is replaced by Lean-only, continuation-generic
   pieces: `AxFetch5.executeJALRSpine` (the do-block's bind spine), `AxFetch5.updateElpRun`
   (`update_elp_state`'s two config reads), `AxFetch5.jumpToRun` (`jump_to`'s run to the `nextPC`
   write, both bit-1 arms), `AxFetch5.cEZicfilpEq`/`cEZcaEq` (the two probes as terms) and the rtc
   glue `AxFetch5.rtcExL`/`rtcExStep`.  The alignment of the target uses
   `WeakLeafJump.retPcJalr`/`retPcAligned` (Rocq `UserBits.bit0_update0_64`).  The `f`
   continuation and the run start are as in Rocq; `k'` is `Unit → SailM Unit`.
7. The primed corollaries take Rocq's `(rd : Z)` as `rd : Int` and state the role as
   `ORjalr rd (i.toNat : Int)`; the parameters `Tt`/`img` are gone (Stage C).

**Rocq → Lean name map.**  `af_nextPC_beq_refl` `afNextPCBeqRefl`, `af_cjr_deps_ctrl`
`afCjrDepsCtrl`, `af_cjr_erw_of` `afCjrErwOf`, `af_cjr_ctrl_src` `afCjrCtrlSrc`,
`af_cjr_gate_srcs` `afCjrGateSrcs`, `af_dstate_t_after_app` `afDstateTAfterApp`,
`af_dt_prov_preserved_step` `afDtProvPreservedStep`, `af_dt_prov_preserved_row`
`afDtProvPreservedRow`, `af_cjr_epilogue_gate_srcs` `afCjrEpilogueGateSrcs`,
`af_cjr_cur_privilege_noncarrier` `afCjrCurPrivilegeNoncarrier`, `af_cjr_mseccfg_noncarrier`
`afCjrMseccfgNoncarrier`, `af_cjr_nextpc_noncarrier` `afCjrNextpcNoncarrier`,
`af_cjr_misa_noncarrier` `afCjrMisaNoncarrier`, `af_cjr_ra_gpr_carrier` `afCjrRaGprCarrier`,
`af_cjr_ra_gpr_read` `afCjrRaGprRead`, `af_cjr_get_next_pc_read` `afCjrGetNextPcRead`,
`af_cjr_set_next_pc_step` `afCjrSetNextPcStep`, `af_pnode_step_ib_rds_app` `afPnodeStepIbRdsApp`,
`af_pnode_step_ib_rds_mono` `afPnodeStepIbRdsMono`, `af_cjr_cur_privilege_read`
`afCjrCurPrivilegeRead`, `af_cjr_mseccfg_read` `afCjrMseccfgRead`, `af_cjr_misa_read`
`afCjrMisaRead`, `af_cjr_bind_assert_exp'` `afCjrBindAssertExp'`, `af_cjr_bind_assoc`
`afCjrBindAssoc`, `af_cjr_bind_assoc_mixed` `afCjrBindAssocMixed`, `af_cjr_bind_assoc_mixed2`
`afCjrBindAssocMixed2`, `af_cjr_bind_assoc_raw` `afCjrBindAssocRaw`, `af_cjr_ra_gpr_read_nested`
`afCjrRaGprReadNested`, `af_cjr_hartSupports_Zicfilp_pure` `afCjrHartSupportsZicfilpPure`,
`af_cjr_hartSupports_Zicsr_pure` `afCjrHartSupportsZicsrPure`, `af_cjr_hartSupports_Zca_pure`
`afCjrHartSupportsZcaPure`, `af_cjr_rec_hs_Zca_pure` `afCjrRecHsZcaPure`, `af_cjr_rec_hs_Zcf_pure`
`afCjrRecHsZcfPure`, `af_cjr_rec_hs_F_pure` `afCjrRecHsFPure`, `af_cjr_rec_hs_Zcd_pure`
`afCjrRecHsZcdPure`, `af_cjr_rec_hs_D_pure` `afCjrRecHsDPure`, `af_cjr_hartSupports_C_pure`
`afCjrHartSupportsCPure`, `af_cjr_rec_cE_Zicsr_pure` `afCjrRecCEZicsrPure`,
`af_cjr_rec_cE_C_misa_pure` `afCjrRecCECMisaPure`, `af_cjr_get_xLPE_machine_pure`
`afCjrGetXLPEMachinePure`, `af_cjr_ib_rd_carrier_mem` `afCjrIbRdCarrierMem`,
`af_cjr_rds_at_nextpc` `afCjrRdsAtNextpc`, `af_cjr_ctrl_src'` `afCjrCtrlSrc'`,
`af_cjr_gate_srcs'` `afCjrGateSrcs'`, `af_cjr_epilogue_gate_srcs'` `afCjrEpilogueGateSrcs'`.
None is in `notes/weak-port-dupnames.json`.  Lean-only (file-qualified): `AxFetch5.dtsrcsMem`,
`AxFetch5.gprReg`,
`AxFetch5.cEZicfilpEq`, `AxFetch5.cEZcaEq`, `AxFetch5.executeJALRSpine`, `AxFetch5.updateElpRun`,
`AxFetch5.jumpToRun`, `AxFetch5.rtcExL`, `AxFetch5.rtcExStep`.

**Dropped:** nothing (Rocq 45 lemmas + 1 Ltac in lines 3819–4880; Lean 45 theorems + 1 tactic
+ 9 Lean-only).  The Rocq `Print Assumptions` commands are not declarations.
-/
import Weak.AxFetch1
import Weak.AxGate
import Weak.WeakEvProv
import Weak.WeakLeafJump
import Weak.WeakFetchRvc
import Weak.WeakLeafEffCommon

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open Sail Sail.ConcurrencyInterfaceV1
open Sail.ArchSem (FreeM)
open LeanRV64D LeanRV64D.Functions
open Wlabel

/-! # 4. THE `c.jr ra` CTRL GATE -/

/-- Rocq `af_nextPC_beq_refl`: the `nextPC` test of `erwOf` fires at `nextPC`. -/
theorem afNextPCBeqRefl : decide (Register.nextPC = Register.nextPC) = true := by decide

/-- THE DECODER FACT: `depsCtrl` of a `jalr`-shaped role names exactly its base register. -/
theorem afCjrDepsCtrl (rd rs1 : Int) (hrs1 : rs1 ≠ 0) :
    depsCtrl (.ORjalr rd rs1) = [.DReg rs1.toNat] := by
  simp only [depsCtrl, dsrcOfNum, wregOfNum, hrs1, ↓reduceIte]

/-- THE ERW FACT: `erwOf` at `nextPC` of a `jalr`-shaped role is `ERWctrl` over the WHOLE
dynamic read set. -/
theorem afCjrErwOf (rd rs1 : Int) (rds : List Nat) (hrs1 : rs1 ≠ 0) :
    erwOf (.ORjalr rd rs1) rds .nextPC = .ERWctrl (erwSrcs [.DReg rs1.toNat] rds) := by
  rw [erwOf, if_pos rfl, afCjrDepsCtrl rd rs1 hrs1]

/-- (Lean-only) a register's provenance positions are inside `dtsrcs` of any source list
containing it. -/
theorem AxFetch5.dtsrcsMem (s0 : DstateT) (srcs : List Dsrc) (r p : Nat) :
    Dsrc.DReg r ∈ srcs → p ∈ dprov (dsOfT s0) r → p ∈ dtsrcs s0 srcs := by
  intro hm hp
  exact List.mem_flatten.2 ⟨dprov (dsOfT s0) r, List.mem_map.2 ⟨.DReg r, hm, rfl⟩, hp⟩

/-- THE TASK'S LEMMA: given `rs1 ∈ rds`, the `nextPC` node is `ERWctrl srcs` with `DReg rs1 ∈
srcs`, and `dstepT`'s `LCtrl` arm appends `rs1`'s current provenance into `dtCtl`. -/
theorem afCjrCtrlSrc (rd rs1 : Int) (rds : List Nat) (s0 : DstateT)
    (hrs1 : rs1 ≠ 0) (hrds : rs1.toNat ∈ rds) :
    ∃ srcs,
      erwOf (.ORjalr rd rs1) rds .nextPC = .ERWctrl srcs ∧
      Dsrc.DReg rs1.toNat ∈ srcs ∧
      ∀ p, p ∈ dprov (dsOfT s0) rs1.toNat →
        p ∈ (dstepT s0 (LCtrl srcs, none)).1.dtCtl :=
  ⟨erwSrcs [.DReg rs1.toNat] rds, afCjrErwOf rd rs1 rds hrs1, erwSrcsReg _ _ _ hrds,
    fun p hp => dtsrcsGateDtCtl s0 _
      (AxFetch5.dtsrcsMem s0 _ _ p (erwSrcsReg _ _ _ hrds) hp)⟩

/-- THE `gateSrcs`-FACING COROLLARY. -/
theorem afCjrGateSrcs (i : Agent) (rd rs1 : Int) (rds : List Nat) (s0 : DstateT)
    (hrs1 : rs1 ≠ 0) (hrds : rs1.toNat ∈ rds) (p : Nat)
    (hp : p ∈ dprov (dsOfT s0) rs1.toNat) :
    ∃ srcs,
      erwOf (.ORjalr rd rs1) rds .nextPC = .ERWctrl srcs ∧
      (i, p) ∈ gateSrcs i s0 srcs := by
  obtain ⟨srcs, herw, hmem, _⟩ := afCjrCtrlSrc rd rs1 rds s0 hrs1 hrds
  exact ⟨srcs, herw, List.mem_map.2 ⟨p, AxFetch5.dtsrcsMem s0 srcs _ p hmem hp, rfl⟩⟩

theorem afDstateTAfterApp (s : DstateT) (es1 es2 : List Eitem) :
    dstateTAfter s (es1 ++ es2) = dstateTAfter (dstateTAfter s es1) es2 := by
  induction es1 generalizing s with
  | nil => rfl
  | cons it es1' ih => exact ih _

theorem afDtProvPreservedStep (s : DstateT) (it : Eitem) (r : Nat)
    (H : ∀ rd srcs, it.1 = LRegW rd srcs → rd ≠ r) :
    (dstepT s it).1.dtProv r = s.dtProv r := by
  obtain ⟨l, ok⟩ := it
  cases l <;> cases ok <;>
    first
    | rfl
    | exact if_neg (fun h => H _ _ rfl h.symm)

theorem afDtProvPreservedRow (s : DstateT) (es : List Eitem) (r : Nat)
    (H : ∀ it, it ∈ es → ∀ rd srcs, it.1 = LRegW rd srcs → rd ≠ r) :
    (dstateTAfter s es).dtProv r = s.dtProv r := by
  induction es generalizing s with
  | nil => rfl
  | cons it es' ih =>
    show (dstateTAfter (dstepT s it).1 es').dtProv r = s.dtProv r
    rw [ih (dstepT s it).1 (fun it' hit' => H it' (List.mem_cons_of_mem _ hit'))]
    exact afDtProvPreservedStep s it r (H it List.mem_cons_self)

theorem afCjrEpilogueGateSrcs (i : Agent) (rd rs1 : Int) (rds : List Nat)
    (esLd esMid : List Eitem) (p : Nat)
    (hrs1 : rs1 ≠ 0) (hrds : rs1.toNat ∈ rds)
    (hp : p ∈ dprov (dsOfT (dstateTAfter dtInit esLd)) rs1.toNat)
    (hmid : ∀ it, it ∈ esMid → ∀ rd' srcs, it.1 = LRegW rd' srcs → rd' ≠ rs1.toNat) :
    ∃ srcs,
      erwOf (.ORjalr rd rs1) rds .nextPC = .ERWctrl srcs ∧
      (i, p) ∈ gateSrcs i (dstateTAfter dtInit (esLd ++ esMid)) srcs := by
  refine afCjrGateSrcs i rd rs1 rds _ hrs1 hrds p ?_
  show p ∈ (dstateTAfter dtInit (esLd ++ esMid)).dtProv rs1.toNat
  rw [afDstateTAfterApp, afDtProvPreservedRow _ esMid _ hmid]
  exact hp

/-! ## 4.5 `c.jr ra`'s ONE OPEN HYPOTHESIS, DISCHARGED FOR THE REAL RUN -/

theorem afCjrCurPrivilegeNoncarrier : eregNum .cur_privilege = none := rfl
theorem afCjrMseccfgNoncarrier : eregNum .mseccfg = none := rfl
theorem afCjrNextpcNoncarrier : eregNum .nextPC = none := rfl
theorem afCjrMisaNoncarrier : eregNum .misa = none := rfl

/-- (Lean-only, deviation 2) the GPR register `rX` reads for index `i` (`i ≠ 0`). -/
def AxFetch5.gprReg (i : BitVec 5) : Register :=
  match i.toNat with
  | 1 => .x1 | 2 => .x2 | 3 => .x3 | 4 => .x4 | 5 => .x5 | 6 => .x6 | 7 => .x7 | 8 => .x8
  | 9 => .x9 | 10 => .x10 | 11 => .x11 | 12 => .x12 | 13 => .x13 | 14 => .x14 | 15 => .x15
  | 16 => .x16 | 17 => .x17 | 18 => .x18 | 19 => .x19 | 20 => .x20 | 21 => .x21 | 22 => .x22
  | 23 => .x23 | 24 => .x24 | 25 => .x25 | 26 => .x26 | 27 => .x27 | 28 => .x28 | 29 => .x29
  | 30 => .x30 | _ => .x31

/-- `ra`'s own GPR IS a carrier, at exactly its GPR number. -/
theorem afCjrRaGprCarrier (i : BitVec 5) (hi : i.toNat ≠ 0) :
    eregNum (AxFetch5.gprReg i) = some i.toNat := by
  revert i; decide

/-- THE ONE REAL STEP: `rX_bits (Regidx ra)` is a single `regRead` of `ra`'s own GPR. -/
theorem afCjrRaGprRead (i : BitVec 5) (hi : i.toNat ≠ 0) (f : BitVec 64 → SailM Unit)
    (cpu : CPU) (rs : RegFile) (ib : Ibch) (d : Efab) (row : List Lbl) (kpos : Nat) :
    AxOpsem.astepProg row ⟨.PHart cpu (rX_bits (.Regidx i) >>= f) rs none ib, kpos⟩ .LSilent
      ⟨.PHart cpu (f (uxaXget rs i)) rs none (ibRd ib (AxFetch5.gprReg i)), kpos⟩ := by
  rcases uxa_bv5_cases i with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd rfl hi
  all_goals
    exact .AStepAdmin _ kpos d .LSilent _ d trivial
      ⟨rfl, none, some _, none, rfl, rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl⟩

/-- `get_next_pc ()`: one `regRead` of `nextPC`, a non-carrier. -/
theorem afCjrGetNextPcRead (f : BitVec 64 → SailM Unit) (cpu : CPU) (rs : RegFile) (ib : Ibch)
    (d : Efab) (row : List Lbl) (kpos : Nat) :
    AxOpsem.astepProg row ⟨.PHart cpu (get_next_pc () >>= f) rs none ib, kpos⟩ .LSilent
      ⟨.PHart cpu (f (rs .nextPC)) rs none ib, kpos⟩ :=
  .AStepAdmin _ kpos d .LSilent _ d trivial
    ⟨rfl, none, some (ibRd ib .nextPC), none, rfl, rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl⟩

/-- `set_next_pc target`: one silent `branchAnnounce` step to the `nextPC` `regWrite` node. -/
theorem afCjrSetNextPcStep (target : BitVec 64) (f : Unit → SailM Unit) (cpu : CPU)
    (rs : RegFile) (ib : Ibch) (d : Efab) (row : List Lbl) (kpos : Nat) :
    AxOpsem.astepProg row ⟨.PHart cpu (set_next_pc target >>= f) rs none ib, kpos⟩ .LSilent
      ⟨.PHart cpu (.impure (.ok (.regWrite .nextPC target)) (fun _ => f (redirect_callback target)))
        rs none ib, kpos⟩ :=
  .AStepAdmin _ kpos d .LSilent _ d trivial
    ⟨rfl, none, none, none, rfl, rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl⟩

/-! ## 4.6 `ibRds` MONOTONICITY, AND THREE MORE NON-CARRIER ADMIN STEPS -/

theorem afPnodeStepIbRdsApp (m : SailM Unit) (rs : RegFile) (ib : Ibch) (d : DevStates)
    (l : Wlabel) (m' : SailM Unit) (ors : Option RegFile)
    (fn' : Option (Bool × Bool × Bool × Bool)) (d' : DevStates) (oib : Option Ibch)
    (obar : Option barrier_kind) :
    ibnAnn m = false →
    pnodeStep m rs ib d l m' ors fn' d' oib obar →
    (oib.getD ib).ibRds = ib.ibRds ++ pnodeRds m := by
  intro hann hstep
  rw [pnodeStepChannel m rs ib d l m' ors fn' d' oib obar hstep]
  exact ibnStepRds m ib hann

theorem afPnodeStepIbRdsMono (m : SailM Unit) (rs : RegFile) (ib : Ibch) (d : DevStates)
    (l : Wlabel) (m' : SailM Unit) (ors : Option RegFile)
    (fn' : Option (Bool × Bool × Bool × Bool)) (d' : DevStates) (oib : Option Ibch)
    (obar : Option barrier_kind) (n : Nat) :
    ibnAnn m = false →
    pnodeStep m rs ib d l m' ors fn' d' oib obar →
    n ∈ ib.ibRds → n ∈ (oib.getD ib).ibRds := by
  intro hann hstep hn
  rw [afPnodeStepIbRdsApp m rs ib d l m' ors fn' d' oib obar hann hstep]
  exact List.mem_append_left _ hn

theorem afCjrCurPrivilegeRead (f : Privilege → SailM Unit) (cpu : CPU) (rs : RegFile)
    (ib : Ibch) (d : Efab) (row : List Lbl) (kpos : Nat) :
    AxOpsem.astepProg row ⟨.PHart cpu (readReg .cur_privilege >>= f) rs none ib, kpos⟩ .LSilent
      ⟨.PHart cpu (f (rs .cur_privilege)) rs none ib, kpos⟩ :=
  .AStepAdmin _ kpos d .LSilent _ d trivial
    ⟨rfl, none, some (ibRd ib .cur_privilege), none, rfl, rfl,
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl⟩

theorem afCjrMseccfgRead (f : BitVec 64 → SailM Unit) (cpu : CPU) (rs : RegFile)
    (ib : Ibch) (d : Efab) (row : List Lbl) (kpos : Nat) :
    AxOpsem.astepProg row ⟨.PHart cpu (readReg .mseccfg >>= f) rs none ib, kpos⟩ .LSilent
      ⟨.PHart cpu (f (rs .mseccfg)) rs none ib, kpos⟩ :=
  .AStepAdmin _ kpos d .LSilent _ d trivial
    ⟨rfl, none, some (ibRd ib .mseccfg), none, rfl, rfl,
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl⟩

theorem afCjrMisaRead (f : BitVec 64 → SailM Unit) (cpu : CPU) (rs : RegFile)
    (ib : Ibch) (d : Efab) (row : List Lbl) (kpos : Nat) :
    AxOpsem.astepProg row ⟨.PHart cpu (readReg .misa >>= f) rs none ib, kpos⟩ .LSilent
      ⟨.PHart cpu (f (rs .misa)) rs none ib, kpos⟩ :=
  .AStepAdmin _ kpos d .LSilent _ d trivial
    ⟨rfl, none, some (ibRd ib .misa), none, rfl, rfl,
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl⟩

/-! ## 4.7 TOWARD `afCjrRdsAtNextpc`: the pure sub-computations as term equalities -/

/-- Lean's `assert` on a true condition is transparent to the bind (deviation 4). -/
theorem afCjrBindAssertExp' {B : Type} (exp : Bool) (hexp : exp = true) (msg : String)
    (f : Unit → SailM B) :
    (assert exp msg >>= f) = f () := by
  subst hexp; rfl

theorem afCjrBindAssoc {A B C : Type} (m : SailM A) (g : A → SailM B) (h : B → SailM C) :
    ((m >>= g) >>= h) = m >>= fun x => g x >>= h :=
  bind_assoc m g h

theorem afCjrBindAssocMixed {A B C : Type} (m : SailM A) (g : A → SailM B) (h : B → SailM C) :
    FreeM.bind (m >>= g) h = m >>= fun x => g x >>= h :=
  bind_assoc m g h

theorem afCjrBindAssocMixed2 {A B C : Type} (m : SailM A) (g : A → SailM B) (h : B → SailM C) :
    (FreeM.bind m g >>= h) = m >>= fun x => g x >>= h :=
  bind_assoc m g h

theorem afCjrBindAssocRaw {A B C : Type} (m : SailM A) (g : A → SailM B) (h : B → SailM C) :
    FreeM.bind (FreeM.bind m g) h = FreeM.bind m (fun x => FreeM.bind (g x) h) :=
  bind_assoc m g h

/-- Rocq Ltac `af_cjr_bindassoc`: re-associate one left-nested bind, any head symbol. -/
macro "axfetch5_bindassoc" : tactic =>
  `(tactic| first
    | rw [afCjrBindAssoc] | rw [afCjrBindAssocMixed] | rw [afCjrBindAssocMixed2]
    | rw [afCjrBindAssocRaw])

/-- `afCjrRaGprRead` for the NESTED shape `(rX_bits (Regidx i) >>= g) >>= h`. -/
theorem afCjrRaGprReadNested {B : Type} (i : BitVec 5) (hi : i.toNat ≠ 0)
    (g : BitVec 64 → SailM B) (h : B → SailM Unit) (cpu : CPU) (rs : RegFile) (ib : Ibch)
    (d : Efab) (row : List Lbl) (kpos : Nat) :
    AxOpsem.astepProg row
      ⟨.PHart cpu ((rX_bits (.Regidx i) >>= g) >>= h) rs none ib, kpos⟩ .LSilent
      ⟨.PHart cpu (g (uxaXget rs i) >>= h) rs none (ibRd ib (AxFetch5.gprReg i)), kpos⟩ := by
  rw [afCjrBindAssoc (rX_bits (.Regidx i)) g h]
  exact afCjrRaGprRead i hi (fun x => g x >>= h) cpu rs ib d row kpos

theorem afCjrHartSupportsZicfilpPure : hartSupports .Ext_Zicfilp = true := by decide +kernel
theorem afCjrHartSupportsZicsrPure : hartSupports .Ext_Zicsr = true := by decide +kernel
theorem afCjrHartSupportsZcaPure : hartSupports .Ext_Zca = true := by decide +kernel
theorem afCjrRecHsZcaPure : hartSupports .Ext_Zca = true := by decide +kernel
theorem afCjrRecHsZcfPure : hartSupports .Ext_Zcf = false := by decide +kernel
theorem afCjrRecHsFPure : hartSupports .Ext_F = true := by decide +kernel
theorem afCjrRecHsZcdPure : hartSupports .Ext_Zcd = true := by decide +kernel
theorem afCjrRecHsDPure : hartSupports .Ext_D = true := by decide +kernel
theorem afCjrHartSupportsCPure : hartSupports .Ext_C = true := by decide +kernel

theorem afCjrRecCEZicsrPure : currentlyEnabled .Ext_Zicsr = pure true := by
  rw [currentlyEnabled]
  simp only [afCjrHartSupportsZicsrPure]

theorem afCjrRecCECMisaPure :
    currentlyEnabled .Ext_C = (readReg .misa >>= fun w => pure (_get_Misa_C w == 1#1)) := by
  rw [currentlyEnabled]
  simp only [afCjrHartSupportsCPure, ↓reduceIte]

theorem afCjrGetXLPEMachinePure :
    get_xLPE .Machine =
      (readReg .mseccfg >>= fun w => pure (bool_bit_backwards (_get_Seccfg_MLPE w))) := by
  rw [get_xLPE]

/-! ## 4.8 `afCjrRdsAtNextpc`: THE COMBINED RUN -/

theorem afCjrIbRdCarrierMem (ib0 : Ibch) (n : Nat) (r : Register) (hr : eregNum r = some n) :
    n ∈ (ibRd ib0 r).ibRds := by
  unfold ibRd
  rw [hr, ibReadRdsSome]
  exact List.mem_append_right _ (List.mem_singleton_self _)

/-- (Lean-only) the `Ext_Zicfilp` probe as a term: under `Zicsr` and `hartSupports Zicfilp`, a
`cur_privilege` read feeding `get_xLPE`. -/
theorem AxFetch5.cEZicfilpEq :
    currentlyEnabled .Ext_Zicfilp = (readReg .cur_privilege >>= fun p => get_xLPE p) := by
  rw [currentlyEnabled]
  simp only [afCjrRecCEZicsrPure, afCjrHartSupportsZicfilpPure, pure_bind, ↓reduceIte]

/-- (Lean-only) the `Ext_Zca` probe as a term: one `misa` read. -/
theorem AxFetch5.cEZcaEq :
    currentlyEnabled .Ext_Zca =
      (readReg .misa >>= fun w => pure ((_get_Misa_C w == 1#1) || !hartSupports .Ext_C)) := by
  rw [currentlyEnabled]
  simp only [afCjrHartSupportsZcaPure, ↓reduceIte, afCjrRecCECMisaPure]
  rfl

/-- (Lean-only) `execute_JALR`'s bind spine. -/
theorem AxFetch5.executeJALRSpine (imm : BitVec 12) (rs1 rd : regidx) :
    ∃ M : BitVec 64 → ExecutionResult → SailM ExecutionResult,
      execute_JALR imm rs1 rd =
        (update_elp_state rs1 >>= fun _ => get_next_pc () >>= fun link =>
          rX_bits rs1 >>= fun v => jump_to (BitVec.update (v + sign_extend (m := 64) imm) 0 0#1) >>=
            M link) :=
  ⟨_, rfl⟩

/-- (Lean-only) rtc glue: a run in front of an existential run. -/
theorem AxFetch5.rtcExL {A K : Type} {R : A → A → Prop} {x y : A} {Z : K → A} :
    rtc R x y → (∃ k, rtc R y (Z k)) → ∃ k, rtc R x (Z k) :=
  fun h ⟨k, hk⟩ => ⟨k, rtc_transitive h hk⟩

theorem AxFetch5.rtcExStep {A K : Type} {R : A → A → Prop} {x y : A} {Z : K → A} :
    R x y → (∃ k, rtc R y (Z k)) → ∃ k, rtc R x (Z k) :=
  fun h ⟨k, hk⟩ => ⟨k, rtc_l h hk⟩

/-- (Lean-only) `update_elp_state`'s admin run: two non-carrier config reads, landing at the
continuation (M-mode, `mseccfg.MLPE` clear). -/
theorem AxFetch5.updateElpRun (rs1 : regidx) (g : Unit → SailM Unit) (cpu : CPU) (rs : RegFile)
    (ib : Ibch) (d : Efab) (row : List Lbl) (kpos : Nat)
    (hpriv : rs .cur_privilege = .Machine)
    (hmlpe : bool_bit_backwards (_get_Seccfg_MLPE (rs .mseccfg)) = false) :
    rtc (fun t1 t2 => ∃ l, AxOpsem.astepProg row t1 l t2)
      ⟨.PHart cpu (update_elp_state rs1 >>= g) rs none ib, kpos⟩
      ⟨.PHart cpu (g ()) rs none ib, kpos⟩ := by
  unfold update_elp_state
  rw [AxFetch5.cEZicfilpEq, bind_assoc, bind_assoc]
  refine rtc_l ⟨_, afCjrCurPrivilegeRead _ cpu rs ib d row kpos⟩ ?_
  rw [hpriv, afCjrGetXLPEMachinePure, bind_assoc]
  refine rtc_l ⟨_, afCjrMseccfgRead _ cpu rs ib d row kpos⟩ ?_
  rw [hmlpe]
  exact rtc_refl _

/-- (Lean-only) `jump_to t`'s admin run to the `nextPC` write, at a 0-aligned target under
`misa.C`: the bit-1 arm reads `misa` first, the other goes straight to `set_next_pc`. -/
theorem AxFetch5.jumpToRun (t : BitVec 64) (g : ExecutionResult → SailM Unit) (cpu : CPU)
    (rs : RegFile) (ib : Ibch) (d : Efab) (row : List Lbl) (kpos : Nat)
    (halign : (BitVec.access t 0 == 0#1) = true)
    (hC : (_get_Misa_C (rs .misa) == 1#1) = true) :
    ∃ k' : Unit → SailM Unit,
      rtc (fun t1 t2 => ∃ l, AxOpsem.astepProg row t1 l t2)
        ⟨.PHart cpu (jump_to t >>= g) rs none ib, kpos⟩
        ⟨.PHart cpu (.impure (.ok (.regWrite .nextPC t)) k') rs none ib, kpos⟩ := by
  unfold jump_to
  simp only [halign]
  cases hb : bit_to_bool (BitVec.access t 1)
  · apply Exists.intro
    refine AxFetch1.admPrepend row cpu _ _ rs ib d.efDev d.efDev .LSilent none none none kpos _
      ?_ ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ trivial
    exact rtc_refl _
  · rw [AxFetch5.cEZcaEq]
    apply Exists.intro
    refine AxFetch1.admPrepend row cpu _ _ rs ib d.efDev d.efDev .LSilent none
      (some (ibRd ib .misa)) none kpos _ ?_ ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ trivial
    simp only [FreeMLemmas.bind_pure, hC]
    refine AxFetch1.admPrepend row cpu _ _ _ _ d.efDev d.efDev .LSilent none none none kpos _
      ?_ ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ trivial
    exact rtc_refl _

/-- THE COMBINED RUN: from `execute_JALR (zeros 12) (Regidx i) rd`'s own term to the `nextPC`
`regWrite` node, `i.toNat` already in the landing read set. -/
theorem afCjrRdsAtNextpc (i : BitVec 5) (rd : regidx) (hi : i.toNat ≠ 0)
    (f : ExecutionResult → SailM Unit) (cpu : CPU) (rs : RegFile) (ib : Ibch) (d : Efab)
    (row : List Lbl) (kpos : Nat)
    (hpriv : rs .cur_privilege = .Machine)
    (hmlpe : bool_bit_backwards (_get_Seccfg_MLPE (rs .mseccfg)) = false)
    (hC : (_get_Misa_C (rs .misa) == 1#1) = true) :
    ∃ (target : BitVec 64) (ib' : Ibch) (k' : Unit → SailM Unit),
      i.toNat ∈ ib'.ibRds ∧
      rtc (fun t1 t2 => ∃ l, AxOpsem.astepProg row t1 l t2)
        ⟨.PHart cpu (execute_JALR (zeros (n := 12)) (.Regidx i) rd >>= f) rs none ib, kpos⟩
        ⟨.PHart cpu (.impure (.ok (.regWrite .nextPC target)) k') rs none ib', kpos⟩ := by
  have halign : (BitVec.access (BitVec.update (uxaXget rs i + sign_extend (m := 64)
      (zeros (n := 12))) 0 0#1) 0 == 0#1) = true := by
    rw [WeakLeafJump.retPcJalr]; exact WeakLeafJump.retPcAligned _
  suffices H : ∃ k' : Unit → SailM Unit,
      rtc (fun t1 t2 => ∃ l, AxOpsem.astepProg row t1 l t2)
        ⟨.PHart cpu (execute_JALR (zeros (n := 12)) (.Regidx i) rd >>= f) rs none ib, kpos⟩
        ⟨.PHart cpu (.impure (.ok (.regWrite .nextPC (BitVec.update (uxaXget rs i +
          sign_extend (m := 64) (zeros (n := 12))) 0 0#1))) k') rs none
          (ibRd ib (AxFetch5.gprReg i)), kpos⟩ by
    obtain ⟨k', hk⟩ := H
    exact ⟨_, _, k', afCjrIbRdCarrierMem ib _ _ (afCjrRaGprCarrier i hi), hk⟩
  obtain ⟨M, hM⟩ := AxFetch5.executeJALRSpine (zeros (n := 12)) (.Regidx i) rd
  rw [hM, bind_assoc]
  refine AxFetch5.rtcExL (AxFetch5.updateElpRun (.Regidx i) _ cpu rs ib d row kpos hpriv hmlpe) ?_
  rw [bind_assoc]
  refine AxFetch5.rtcExStep ⟨_, afCjrGetNextPcRead _ cpu rs ib d row kpos⟩ ?_
  rw [bind_assoc]
  refine AxFetch5.rtcExStep ⟨_, afCjrRaGprRead i hi _ cpu rs ib d row kpos⟩ ?_
  rw [bind_assoc]
  exact AxFetch5.jumpToRun _ _ cpu rs _ d row kpos halign hC

/-! ### The hypothesis-free variants -/

theorem afCjrCtrlSrc' (rd : Int) (i : BitVec 5) (sailRd : regidx) (hi : i.toNat ≠ 0)
    (f : ExecutionResult → SailM Unit) (cpu : CPU) (rs : RegFile) (ib : Ibch) (d : Efab)
    (row : List Lbl) (kpos : Nat) (s0 : DstateT)
    (hpriv : rs .cur_privilege = .Machine)
    (hmlpe : bool_bit_backwards (_get_Seccfg_MLPE (rs .mseccfg)) = false)
    (hC : (_get_Misa_C (rs .misa) == 1#1) = true) :
    ∃ (ib' : Ibch) (srcs : List Dsrc),
      erwOf (.ORjalr rd (i.toNat : Int)) ib'.ibRds .nextPC = .ERWctrl srcs ∧
      Dsrc.DReg i.toNat ∈ srcs ∧
      ∀ p, p ∈ dprov (dsOfT s0) i.toNat →
        p ∈ (dstepT s0 (LCtrl srcs, none)).1.dtCtl := by
  obtain ⟨_, ib', _, hmem, _⟩ :=
    afCjrRdsAtNextpc i sailRd hi f cpu rs ib d row kpos hpriv hmlpe hC
  exact ⟨ib', afCjrCtrlSrc rd (i.toNat : Int) ib'.ibRds s0 (by omega) (by simpa using hmem)⟩

theorem afCjrGateSrcs' (agt : Agent) (rd : Int) (i : BitVec 5) (sailRd : regidx)
    (hi : i.toNat ≠ 0)
    (f : ExecutionResult → SailM Unit) (cpu : CPU) (rs : RegFile) (ib : Ibch) (d : Efab)
    (row : List Lbl) (kpos : Nat) (s0 : DstateT) (p : Nat)
    (hpriv : rs .cur_privilege = .Machine)
    (hmlpe : bool_bit_backwards (_get_Seccfg_MLPE (rs .mseccfg)) = false)
    (hC : (_get_Misa_C (rs .misa) == 1#1) = true)
    (hp : p ∈ dprov (dsOfT s0) i.toNat) :
    ∃ (ib' : Ibch) (srcs : List Dsrc),
      erwOf (.ORjalr rd (i.toNat : Int)) ib'.ibRds .nextPC = .ERWctrl srcs ∧
      (agt, p) ∈ gateSrcs agt s0 srcs := by
  obtain ⟨_, ib', _, hmem, _⟩ :=
    afCjrRdsAtNextpc i sailRd hi f cpu rs ib d row kpos hpriv hmlpe hC
  exact ⟨ib', afCjrGateSrcs agt rd (i.toNat : Int) ib'.ibRds s0 (by omega)
    (by simpa using hmem) p (by simpa using hp)⟩

theorem afCjrEpilogueGateSrcs' (agt : Agent) (rd : Int) (i : BitVec 5) (sailRd : regidx)
    (hi : i.toNat ≠ 0)
    (f : ExecutionResult → SailM Unit) (cpu : CPU) (rs : RegFile) (ib : Ibch) (d : Efab)
    (row : List Lbl) (kpos : Nat)
    (esLd esMid : List Eitem) (p : Nat)
    (hpriv : rs .cur_privilege = .Machine)
    (hmlpe : bool_bit_backwards (_get_Seccfg_MLPE (rs .mseccfg)) = false)
    (hC : (_get_Misa_C (rs .misa) == 1#1) = true)
    (hp : p ∈ dprov (dsOfT (dstateTAfter dtInit esLd)) i.toNat)
    (hmid : ∀ it, it ∈ esMid → ∀ rd' srcs, it.1 = LRegW rd' srcs → rd' ≠ i.toNat) :
    ∃ (ib' : Ibch) (srcs : List Dsrc),
      erwOf (.ORjalr rd (i.toNat : Int)) ib'.ibRds .nextPC = .ERWctrl srcs ∧
      (agt, p) ∈ gateSrcs agt (dstateTAfter dtInit (esLd ++ esMid)) srcs := by
  obtain ⟨_, ib', _, hmem, _⟩ :=
    afCjrRdsAtNextpc i sailRd hi f cpu rs ib d row kpos hpriv hmlpe hC
  exact ⟨ib', afCjrEpilogueGateSrcs agt rd (i.toNat : Int) ib'.ibRds esLd esMid p (by omega)
    (by simpa using hmem) (by simpa using hp) (by simpa using hmid)⟩

end Weak
