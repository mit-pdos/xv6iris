/-
Weak: **the weak `start()` boot chain** (M4: the second whole-function port, after `wwpEntry`) --
xv6's `start()` (39 instructions at `KernelSyms.«start»` .. `+0x72`, INCLUDING the call to
`timerinit()`) as ONE `wwpTriv` theorem, composed from `WeakLeafO`'s wrappers over
`WkStartAux`'s per-instruction `winstrM` tokens and `WkTimerinit.wwpTimerinit`.

Rocq: `iris/WkStartNew.v` @ xxvzwolszwmp.

The Rocq header, in substance.  The weak twin of `WpStartNew.wp_start` with the SC statement's
spellings swapped per the porting guide: `kernel_text` ↦ `wkernelText kbs` + `wkbCovers kbs`;
`mmode_config (DfracOwn 1)` ↦ the bundle `whartRun cpu ξ 1 c` (this hart's view token rides
inside it); `stack_own_phys sp0 n` ↦ OBJECTIVE ownership `cobj ξ (wstackOwnPhys cpu sp0 n)` --
no `wstate`, no `wsLe`, no view inequality anywhere: the frames are `cobj`s, which cross a step
untouched.  The postcondition hands back `wrunning cpu ξ` rather than the bundle, because the
last instruction is `mret`: it moves `cur_privilege`, i.e. it DISSOLVES the M-mode config rather
than preserving it (the M→S boundary).  Every instruction is one `iapply` of its wrapper and one
`iintro` naming the resources back, over a `WkStartAux.wstiNN` token spent with one `ihave`.
The two prologue `c.sdsp` stores use `wwpSd8OffRvcRun` (the all-OFF boot PMP; the `pmpcfg0`
write is instruction 58) and are RELEASE stores whose two extra outputs this chain drops (a
private stack slot publishes nothing).  FOUR instructions do not ride the bundle -- `csrr
mstatus`, `csrw mstatus`, `csrw pmpcfg0` and `mret`: their wrappers take the CELLS the config is
built from, so those sites open `whartRun`, split the config (`mconf_cases`), apply, and close it
again (`mConf_introW` / `whartRunClose`; at `mret`, `confCells_introW` at Supervisor).  The
`jal` into `timerinit` is `wwpJalRun`; the call itself applies `wwpTimerinit`, stated on this
very interface.

**Deviations from Rocq.**
1. VOCABULARY: as `Weak/WkTimerinit.lean` deviation 1 (`mword n` ↦ `BitVec n`, `regfile` ↦
   `MachCSL.RegMap`, `gpr_file` ↦ `MachCSL.gprFile cpu`, `pc_is` ↦ `pcIs cpu`, `WWP Loop` ↦
   `wwpTriv ⊤ (WExpr.loop gen cpu)` with `gen = 0` for Rocq `gen_id = 0`, `wstack_own_phys` ↦
   `wstackOwnPhys cpu`, `pa_stk` ↦ `paStk`, `cms5` ↦ `WeakLeafMret.cms5`, `ret_pc` ↦
   `WeakLeafMret.retPc`, `mstatus_legalized` ↦ `WeakLeafCsrw.mstatusLegalized`, `satp_legalized`
   ↦ `WeakLeafCsrw3.satpLegalized`, `mideleg_legalized` ↦ `WeakLeafCsrw2.midelegLegalized`,
   `sie_new_mie` ↦ `WeakLeafCsrw3.sieNewMie`, `pmp0_newaddr` ↦ `WeakLeafCsrw3.pmp0Newaddr`,
   `pmpcfg_written` ↦ `WeakLeafPmpcfg0.pmpcfgWritten`, `menvcfg_legalized` ↦
   `WeakLeafCsrw2.menvcfgLegalized`, `mepc_val` ↦ `WeakLeafCsrw2.mepcVal`).
2. THE CONFIGURATION (owner decision Q3): Rocq's separate cells `pmpcfg_n`, `pmpaddr_n`, `mepc`,
   `satp`, `medeleg`, `mideleg`, `mie`, `menvcfg`, `mcounteren`, `stimecmp` (in and out) and the
   entry `mstatus` `ms0` are fields of the config `c` inside `whartRun cpu ξ 1 c` (Rocq's
   `pmpcfg_n` read slot is `clockCells cpu`, as in WeakLeafM); `mhartid` stays a separate cell.
   The writes are threaded as the Lean-only configs `WkStartNew.stC41 … stCAe4` (each wrapper's
   `{ c with … }`, folded by `rfl`), and the postcondition's cells are ONE `sConf cpu (own 1)
   (WkStartNew.stConfOut c tv)` (the Supervisor-mode cells `mret` leaves), whose fields are
   Rocq's output values (`mstatus = cms5 (st_ms1 ms0)`, `mepc = st_main`, `satp = satp_legalized
   satp0 0`, …, `stimecmp = stimecmp_legalized … (ti_deadline tv)`).  Rocq's `mmode_config` packs
   an existential `ms0` with `MIE = 0`, `MPRV = 0`, `SXL = 2` and `mstatus_kernel_facts`; Lean's
   `mConf` is at the named `c`, so these are the premises `MConf.mok c` (MIE/MPRV) and
   `_get_Mstatus_SXL c.mstatus = 2#2` (satp leaf), Rocq's `HoKF` is not needed by any Lean leaf
   and is dropped, and the continuation no longer re-binds `ms0` and its four facts (`ms0 =
   c.mstatus` is visible to the caller).  `pmp_all_off pmpcfg0` ↦ `pmpAllOff c.pmpcfg`.
3. THE FRACTION (orchestrator ruling, checked against the Rocq source): Rocq splits every config
   cell into a 1/2 working bundle plus pinned halves held by this same proof and recombined at
   each config-writing site (`reg_half_join` … `mmode_config_rebuild (DfracOwn (1/2))`) -- a
   bookkeeping choreography; nothing else holds a fraction of the config concurrently.  Lean
   keeps the FULL config `whartRun cpu ξ 1 c` throughout and calls the fraction-1 wrappers and
   `wwpTimerinit` (which is stated at `1`) directly; Rocq's `reg_half_join` script is gone.
4. RAM premises: Rocq `∀ j < 8, addr_is_ram (pa_add ea j)` ↦ `inRam ea 8`; the TOR bounds `uint
   ea + 8 <= 0xfffffffffffffc` ↦ `ea.toNat + 8 ≤ 0xfffffffffffffc`.
5. THE SC VOCABULARY of `WpStartNew` (`st_mask_and`, `st_va5_40`, `st_ms1`, `st_a42v`,
   `st_main`, `st_ffff`, `st_pmpw`, `st_ra_link`, `st_adue_bit`, `st_menv_adue`, `st_mdl1`,
   `st_va5_52`, `st_mie1`, `st_pmpcfg1`, `st_pmpaddr1`, `st_tpv`, the register maps `st_m30` …
   `st_mout`) and its pure facts (`st_s0_16`, `st_va5_40_MIE/MPRV/MPP`, `mstatus_legalized_*`,
   `pmp_allows_all_written`, `st_pmp_tor0_grants`, `st_mret_priv`, `st_menvcfg_LPE_final`,
   `st_menv_adue_LPE`, `st_Hb61`, …): no Lean twin (`notes/weak-port-map.md`), restated here
   file-qualified (`WkStartNew.*`, §0-§1).  The register maps take the config `c` in place of
   Rocq's `ms0 mie0 mdl0 menv0 mcen0` (`c.mstatus`, …).  The closed-value bridges and the
   `pcNN`/`pcNN+1` arithmetic are `decide +kernel`.
6. THE STACK: Rocq's `cobj_mono`/`cobj_sep`/`cobj_exist` script is `WkTimerinit.stackSplit` /
   `stackRebuild` for the top two slots plus one `wstackOwnPhys_split_1/_2` for timerinit's
   frame, which is handed over as `wstackOwnPhys cpu (tiSp1 sp0) 2` (Rocq: rebuilt from two
   slots).  The stores are stated at `paStk sp0 1` / `paStk sp0 2`.
7. Ltacs `st_reg_neq`/`st_look`/`st_unfold` ↦ `decide +kernel` / the macro `wk_sn_look`;
   Rocq `iEval (change … with st_mNN …)` ↦ `rw [show … = stMNN … from rfl]`.

**Rocq → Lean name map.**  `wwp_start` `wwpStart`; `wstack2_intro_ent` (Local)
`WkStartNew.wstack2IntroEnt`.  None is in the duplicated-name table.  Lean-only (file-qualified
`WkStartNew.*`): the SC stand-ins `stMaskAnd stMaskOr stVa540 stMs1 stA42v stMain stFfff stPmpw
stRaLink stAdueBit stMenvAdue stMdl1 stVa552 stPmpcfg1 stPmpaddr1 stTpv`, `stM30 stM33 stM34
stM35 stM36 stM37 stM38 stM39 stM40 stM42 stM43 stM45 stM47 stM48 stM51 stM52 stM54 stM55 stM57
stMAe0 stMAe1 stMAe2 stMAe3 stM59 stMti stM60 stM61 stMout`, the configs `stC41 stC44 stC46
stC49 stC50 stC53 stC56 stC58 stCAe4 stConfOut`, the facts `stS016 tiSp1Stk ea1Stk ea2Stk
ms1Bits cms2Mpp mretPriv lpeLegal lpeFinal wcfgUnlocked torOf vecupdLockFree vecupdUnl vecupdKeep0
pmpcfg1Ent0 pmpcfg1AllowsAll pmpaddr1Ent0 torGrants`, and the macro `wk_sn_look`.

**Dropped:** nothing (Rocq: 1 Local lemma + 1 theorem; Lean: both, plus the Lean-only
declarations above).
-/
import Weak.WkStartAux
import Weak.WkTimerinit

namespace Weak

open Iris Iris.BI Iris.BI.MonPred Iris.ProofMode Iris.Std
open MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D LeanRV64D.Functions
open WkStartAux

/-! ## 0. The `WpStartNew` vocabulary (Lean-only stand-ins, deviation 5) -/

/-- Rocq `st_mask_and`. -/
def WkStartNew.stMaskAnd : BitVec 64 := 0xffffffffffffe7ff#64
/-- Rocq `st_mask_or`. -/
def WkStartNew.stMaskOr : BitVec 64 := 0x800#64
/-- Rocq `st_va5_40`: the value `csrw mstatus` writes. -/
def WkStartNew.stVa540 (ms : BitVec 64) : BitVec 64 :=
  (ms &&& WkStartNew.stMaskAnd) ||| WkStartNew.stMaskOr
/-- Rocq `st_ms1`: the legalized mstatus after instruction 41. -/
def WkStartNew.stMs1 (ms : BitVec 64) : BitVec 64 :=
  WeakLeafCsrw.mstatusLegalized ms (WkStartNew.stVa540 ms)
/-- Rocq `st_a42v`: the `auipc a5, 1` value. -/
def WkStartNew.stA42v : BitVec 64 := BitVec.ofInt 64 ((KernelSyms.«start» : Int) + 0x1020)
/-- Rocq `st_main`: `<main>`. -/
def WkStartNew.stMain : BitVec 64 := BitVec.ofInt 64 (KernelSyms.«main» : Int)
/-- Rocq `st_ffff`. -/
def WkStartNew.stFfff : BitVec 64 := 0xffff#64
/-- Rocq `st_pmpw`. -/
def WkStartNew.stPmpw : BitVec 64 := 0x3fffffffffffff#64
/-- Rocq `st_ra_link`: the `jal` link. -/
def WkStartNew.stRaLink : BitVec 64 := BitVec.ofInt 64 ((KernelSyms.«start» : Int) + 0x6a)
/-- Rocq `st_adue_bit`. -/
def WkStartNew.stAdueBit : BitVec 64 := 0x2000000000000000#64
/-- Rocq `st_menv_adue`. -/
def WkStartNew.stMenvAdue (menv0 : BitVec 64) : BitVec 64 :=
  WeakLeafCsrw2.menvcfgLegalized menv0 (menv0 ||| WkStartNew.stAdueBit)
/-- Rocq `st_mdl1`. -/
def WkStartNew.stMdl1 (mdl0 : BitVec 64) : BitVec 64 :=
  WeakLeafCsrw2.midelegLegalized mdl0 WkStartNew.stFfff
/-- Rocq `st_va5_52`. -/
def WkStartNew.stVa552 (mie0 mdl0 : BitVec 64) : BitVec 64 :=
  lower_mie mie0 (WkStartNew.stMdl1 mdl0) ||| sign_extend (m := 64) si52
/-- Rocq `st_pmpcfg1`. -/
def WkStartNew.stPmpcfg1 (cfg0 : RegisterType .pmpcfg_n) : RegisterType .pmpcfg_n :=
  WeakLeafPmpcfg0.pmpcfgWritten 15#64 cfg0
/-- Rocq `st_pmpaddr1`. -/
def WkStartNew.stPmpaddr1 (cfg0 : RegisterType .pmpcfg_n) (pa0 : RegisterType .pmpaddr_n) :
    RegisterType .pmpaddr_n :=
  WeakLeafCsrw3.pmp0Newaddr cfg0 pa0 WkStartNew.stPmpw
/-- Rocq `st_tpv`. -/
def WkStartNew.stTpv (mh : BitVec 64) : BitVec 64 :=
  sign_extend (m := 64) (Sail.BitVec.extractLsb (mh + sign_extend (m := 64) si61) 31 0)

open WkStartNew

/-! ### The register file after each write (Rocq `st_m*`, deviation 5) -/

/-- Rocq `st_m30`. -/
def WkStartNew.stM30 (m : RegMap) (sp0 : BitVec 64) : RegMap := m.set cspRs1 (WkTimerinit.tiSp1 sp0)
/-- Rocq `st_m33`. -/
def WkStartNew.stM33 (m : RegMap) (sp0 : BitVec 64) : RegMap := (stM30 m sp0).set tiS0 sp0
/-- Rocq `st_m34`. -/
def WkStartNew.stM34 (m : RegMap) (sp0 : BitVec 64) (c : MConf) : RegMap :=
  (stM33 m sp0).set tiA5 c.mstatus
/-- Rocq `st_m35`. -/
def WkStartNew.stM35 (m : RegMap) (sp0 : BitVec 64) (c : MConf) : RegMap :=
  (stM34 m sp0 c).set tiA4 (WkEntryEff.luival (sign_extend (m := 20) si35))
/-- Rocq `st_m36`. -/
def WkStartNew.stM36 (m : RegMap) (sp0 : BitVec 64) (c : MConf) : RegMap :=
  (stM35 m sp0 c).set tiA4 stMaskAnd
/-- Rocq `st_m37`. -/
def WkStartNew.stM37 (m : RegMap) (sp0 : BitVec 64) (c : MConf) : RegMap :=
  (stM36 m sp0 c).set tiA5 (c.mstatus &&& stMaskAnd)
/-- Rocq `st_m38`. -/
def WkStartNew.stM38 (m : RegMap) (sp0 : BitVec 64) (c : MConf) : RegMap :=
  (stM37 m sp0 c).set tiA4 (WkEntryEff.luival (sign_extend (m := 20) si38))
/-- Rocq `st_m39`. -/
def WkStartNew.stM39 (m : RegMap) (sp0 : BitVec 64) (c : MConf) : RegMap :=
  (stM38 m sp0 c).set tiA4 stMaskOr
/-- Rocq `st_m40`. -/
def WkStartNew.stM40 (m : RegMap) (sp0 : BitVec 64) (c : MConf) : RegMap :=
  (stM39 m sp0 c).set tiA5 (stVa540 c.mstatus)
/-- Rocq `st_m42`. -/
def WkStartNew.stM42 (m : RegMap) (sp0 : BitVec 64) (c : MConf) : RegMap :=
  (stM40 m sp0 c).set tiA5 stA42v
/-- Rocq `st_m43`. -/
def WkStartNew.stM43 (m : RegMap) (sp0 : BitVec 64) (c : MConf) : RegMap :=
  (stM42 m sp0 c).set tiA5 stMain
/-- Rocq `st_m45`. -/
def WkStartNew.stM45 (m : RegMap) (sp0 : BitVec 64) (c : MConf) : RegMap :=
  (stM43 m sp0 c).set tiA5 0#64
/-- Rocq `st_m47`. -/
def WkStartNew.stM47 (m : RegMap) (sp0 : BitVec 64) (c : MConf) : RegMap :=
  (stM45 m sp0 c).set tiA5 (WkEntryEff.luival (sign_extend (m := 20) si47))
/-- Rocq `st_m48`. -/
def WkStartNew.stM48 (m : RegMap) (sp0 : BitVec 64) (c : MConf) : RegMap :=
  (stM47 m sp0 c).set tiA5 stFfff
/-- Rocq `st_m51`. -/
def WkStartNew.stM51 (m : RegMap) (sp0 : BitVec 64) (c : MConf) : RegMap :=
  (stM48 m sp0 c).set tiA5 (lower_mie c.mie (stMdl1 c.mideleg))
/-- Rocq `st_m52`. -/
def WkStartNew.stM52 (m : RegMap) (sp0 : BitVec 64) (c : MConf) : RegMap :=
  (stM51 m sp0 c).set tiA5 (stVa552 c.mie c.mideleg)
/-- Rocq `st_m54`. -/
def WkStartNew.stM54 (m : RegMap) (sp0 : BitVec 64) (c : MConf) : RegMap :=
  (stM52 m sp0 c).set tiA5 (WkTimerinit.cliWval si54)
/-- Rocq `st_m55`. -/
def WkStartNew.stM55 (m : RegMap) (sp0 : BitVec 64) (c : MConf) : RegMap :=
  (stM54 m sp0 c).set tiA5 stPmpw
/-- Rocq `st_m57`. -/
def WkStartNew.stM57 (m : RegMap) (sp0 : BitVec 64) (c : MConf) : RegMap :=
  (stM55 m sp0 c).set tiA5 15#64
/-- Rocq `st_m_ae0`. -/
def WkStartNew.stMAe0 (m : RegMap) (sp0 : BitVec 64) (c : MConf) : RegMap :=
  (stM57 m sp0 c).set tiA5 c.menvcfg
/-- Rocq `st_m_ae1`. -/
def WkStartNew.stMAe1 (m : RegMap) (sp0 : BitVec 64) (c : MConf) : RegMap :=
  (stMAe0 m sp0 c).set tiA4 (WkTimerinit.cliWval saeLi)
/-- Rocq `st_m_ae2`. -/
def WkStartNew.stMAe2 (m : RegMap) (sp0 : BitVec 64) (c : MConf) : RegMap :=
  (stMAe1 m sp0 c).set tiA4 stAdueBit
/-- Rocq `st_m_ae3`. -/
def WkStartNew.stMAe3 (m : RegMap) (sp0 : BitVec 64) (c : MConf) : RegMap :=
  (stMAe2 m sp0 c).set tiA5 (c.menvcfg ||| stAdueBit)
/-- Rocq `st_m59`. -/
def WkStartNew.stM59 (m : RegMap) (sp0 : BitVec 64) (c : MConf) : RegMap :=
  (stMAe3 m sp0 c).set tiRa stRaLink
/-- Rocq `st_mti`: the file `timerinit()` returns. -/
def WkStartNew.stMti (m : RegMap) (sp0 : BitVec 64) (c : MConf) (tv : BitVec 64) : RegMap :=
  WkTimerinit.tiMout (stM59 m sp0 c) (WkTimerinit.tiSp1 sp0) (stMenvAdue c.menvcfg) c.mcounteren tv
    stRaLink sp0
/-- Rocq `st_m60`. -/
def WkStartNew.stM60 (m : RegMap) (sp0 : BitVec 64) (c : MConf) (tv mh : BitVec 64) : RegMap :=
  (stMti m sp0 c tv).set tiA5 mh
/-- Rocq `st_m61`. -/
def WkStartNew.stM61 (m : RegMap) (sp0 : BitVec 64) (c : MConf) (tv mh : BitVec 64) : RegMap :=
  (stM60 m sp0 c tv mh).set tiA5 (stTpv mh)
/-- Rocq `st_mout`: the FINAL file (sp = the still-open frame, tp = sext32 mhartid). -/
def WkStartNew.stMout (m : RegMap) (sp0 : BitVec 64) (c : MConf) (tv mh : BitVec 64) : RegMap :=
  (stM61 m sp0 c tv mh).set stTp (stTpv mh)

/-! ### The configuration after each CSR write (deviation 2) -/

/-- After `csrw mstatus, a5`. -/
def WkStartNew.stC41 (c : MConf) : MConf := { c with mstatus := stMs1 c.mstatus }
/-- After `csrw mepc, a5`. -/
def WkStartNew.stC44 (c : MConf) : MConf := { stC41 c with mepc := stMain }
/-- After `csrw satp, a5`. -/
def WkStartNew.stC46 (c : MConf) : MConf :=
  { stC44 c with satp := WeakLeafCsrw3.satpLegalized (stC44 c).satp 0#64 }
/-- After `csrw medeleg, a5`. -/
def WkStartNew.stC49 (c : MConf) : MConf :=
  { stC46 c with medeleg := legalize_medeleg (stC46 c).medeleg stFfff }
/-- After `csrw mideleg, a5`. -/
def WkStartNew.stC50 (c : MConf) : MConf :=
  { stC49 c with mideleg := WeakLeafCsrw2.midelegLegalized (stC49 c).mideleg stFfff }
/-- After `csrw sie, a5`. -/
def WkStartNew.stC53 (c : MConf) : MConf :=
  { stC50 c with mie := WeakLeafCsrw3.sieNewMie (stC50 c).mie (stC50 c).mideleg (stVa552 c.mie c.mideleg) }
/-- After `csrw pmpaddr0, a5`. -/
def WkStartNew.stC56 (c : MConf) : MConf :=
  { stC53 c with pmpaddr := WeakLeafCsrw3.pmp0Newaddr (stC53 c).pmpcfg (stC53 c).pmpaddr stPmpw }
/-- After `csrw pmpcfg0, a5`. -/
def WkStartNew.stC58 (c : MConf) : MConf :=
  { stC56 c with pmpcfg := WeakLeafPmpcfg0.pmpcfgWritten 15#64 (stC56 c).pmpcfg }
/-- After `csrw menvcfg, a5` (the ADUE write). -/
def WkStartNew.stCAe4 (c : MConf) : MConf :=
  { stC58 c with menvcfg := WeakLeafCsrw2.menvcfgLegalized (stC58 c).menvcfg (c.menvcfg ||| stAdueBit) }
/-- The configuration `start()` hands to the kernel (after `timerinit()` and `mret`). -/
def WkStartNew.stConfOut (c : MConf) (tv : BitVec 64) : MConf :=
  { WkTimerinit.tiConfOut (stCAe4 c) tv with
    mstatus := WeakLeafMret.cms5 (WkTimerinit.tiConfOut (stCAe4 c) tv).mstatus }

/-! ## 1. Pure facts (deviation 5) -/

/-- Rocq `st_s0_16`: `s0 := sp + 16` after the `-16` prologue is the original `sp`. -/
theorem WkStartNew.stS016 (sp0 : BitVec 64) :
    WkTimerinit.tiSp1 sp0 + sign_extend (m := 64) (caddi4spnImm nz12) = sp0 := by
  unfold WkTimerinit.tiSp1
  rw [BitVec.add_assoc,
    show sign_extend (m := 64) WkTimerinitAux.i9 + sign_extend (m := 64) (caddi4spnImm nz12) = 0#64 by
      decide +kernel,
    BitVec.add_zero]

/-- `sp` after the prologue is the second stack slot. -/
theorem WkStartNew.tiSp1Stk (sp0 : BitVec 64) : WkTimerinit.tiSp1 sp0 = paStk sp0 2 := by
  unfold WkTimerinit.tiSp1 paStk
  rw [BitVec.sub_eq_add_neg]
  exact congrArg (sp0 + ·) (by decide +kernel)

/-- The `c.sdsp ra, 8(sp)` address. -/
theorem WkStartNew.ea1Stk (sp0 : BitVec 64) :
    WkTimerinit.tiSp1 sp0 + sign_extend (m := 64) (zero_extend (m := 12) (u10 +++ 0b000#3)) =
      paStk sp0 1 := by
  unfold WkTimerinit.tiSp1 paStk
  rw [BitVec.sub_eq_add_neg, BitVec.add_assoc]
  exact congrArg (sp0 + ·) (by decide +kernel)

/-- The `c.sdsp s0, 0(sp)` address. -/
theorem WkStartNew.ea2Stk (sp0 : BitVec 64) :
    WkTimerinit.tiSp1 sp0 + sign_extend (m := 64) (zero_extend (m := 12) (u11 +++ 0b000#3)) =
      paStk sp0 2 := by
  unfold WkTimerinit.tiSp1 paStk
  rw [BitVec.sub_eq_add_neg, BitVec.add_assoc]
  exact congrArg (sp0 + ·) (by decide +kernel)

/-- Rocq `st_va5_40_MIE/MPRV/MPP` + `mstatus_legalized_MIE/MPRV/SXL`: the legalized write keeps
`MIE`, `MPRV` and `SXL`, and sets `MPP` to Supervisor. -/
theorem WkStartNew.ms1Bits (ms : BitVec 64) :
    BitVec.extractLsb' 3 1 (stMs1 ms) = BitVec.extractLsb' 3 1 ms ∧
    BitVec.extractLsb' 17 1 (stMs1 ms) = BitVec.extractLsb' 17 1 ms ∧
    _get_Mstatus_SXL (stMs1 ms) = _get_Mstatus_SXL ms ∧
    _get_Mstatus_MPP (stMs1 ms) = 1#2 := by
  have hmpp : _get_Mstatus_MPP (Mk_Mstatus (stVa540 ms)) = 1#2 := by
    simp only [_get_Mstatus_MPP, Mk_Mstatus, stVa540, stMaskAnd, stMaskOr, Sail.BitVec.extractLsb,
      BitVec.extractLsb]
    bv_decide
  unfold stMs1 WeakLeafCsrw.mstatusLegalized
  rw [hmpp, show haveNomVal 1#2 = true from rfl, if_pos rfl]
  generalize (bool_to_bit _) = d
  generalize legalize_extStatus plat_mstatus_legal_fs _ = fs
  generalize legalize_extStatus plat_mstatus_legal_vs _ = vs
  generalize extStatus_map_forwards ExtStatus.Off = xs
  simp only [_update_Mstatus_SD, _update_Mstatus_SIE, _update_Mstatus_MIE, _update_Mstatus_SPIE,
    _update_Mstatus_MPIE, _update_Mstatus_SPP, _update_Mstatus_MPP, _update_Mstatus_VS,
    _update_Mstatus_FS, _update_Mstatus_XS, _update_Mstatus_MPRV, _update_Mstatus_SUM,
    _update_Mstatus_MXR, _update_Mstatus_TVM, _update_Mstatus_TW, _update_Mstatus_TSR,
    _update_Mstatus_SPELP, _update_Mstatus_MPELP, _get_Mstatus_MPELP, _get_Mstatus_SPELP,
    _get_Mstatus_TSR, _get_Mstatus_TW, _get_Mstatus_TVM, _get_Mstatus_MXR, _get_Mstatus_SUM,
    _get_Mstatus_MPRV, _get_Mstatus_SPP, _get_Mstatus_MPIE, _get_Mstatus_SPIE, _get_Mstatus_MIE,
    _get_Mstatus_SIE, _get_Mstatus_SXL, _get_Mstatus_MPP, Mk_Mstatus, stVa540, stMaskAnd, stMaskOr,
    Sail.BitVec.updateSubrange, Sail.BitVec.updateSubrange', Sail.BitVec.extractLsb,
    BitVec.extractLsb]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> bv_decide

/-- `cms2` (MIE := MPIE, MPIE := 1) keeps `MPP`. -/
theorem WkStartNew.cms2Mpp (x : BitVec 64) :
    _get_Mstatus_MPP (WeakLeafMret.cms2 x) = _get_Mstatus_MPP x := by
  simp only [WeakLeafMret.cms2, WeakLeafMret.cms1, _get_Mstatus_MPP, _get_Mstatus_MPIE,
    Sail.BitVec.updateSubrange, Sail.BitVec.updateSubrange', Sail.BitVec.extractLsb,
    BitVec.extractLsb]
  bv_decide

/-- Rocq `st_mret_priv`: the `mret` lands in Supervisor mode. -/
theorem WkStartNew.mretPriv (ms : BitVec 64) :
    privLevel_bits_forwards (_get_Mstatus_MPP (WeakLeafMret.cms2 (stMs1 ms)), 0#1) =
      pure .Supervisor := by
  rw [WkStartNew.cms2Mpp, (WkStartNew.ms1Bits ms).2.2.2]
  rfl

/-- Rocq `menvcfg_legalized_LPE`: the legalized `menvcfg` takes the written `LPE`. -/
theorem WkStartNew.lpeLegal (o v : BitVec 64) :
    _get_MEnvcfg_LPE (WeakLeafCsrw2.menvcfgLegalized o v) = _get_MEnvcfg_LPE v := by
  unfold WeakLeafCsrw2.menvcfgLegalized
  generalize WeakLeafCsrw2.menvcfgCbie v = cb
  generalize (if sys_enable_writable_fiom then _get_MEnvcfg_FIOM (Mk_MEnvcfg v) else 0#1) = fi
  generalize (if (true && is_supported_pmm .PM_SMNPM (pmm_mode_backwards (_get_MEnvcfg_PMM
    (Mk_MEnvcfg v)))) then _get_MEnvcfg_PMM (Mk_MEnvcfg v) else _get_MEnvcfg_PMM o) = pm
  simp only [_update_MEnvcfg_PBMTE, _update_MEnvcfg_ADUE, _update_MEnvcfg_PMM, _update_MEnvcfg_STCE,
    _update_MEnvcfg_CBIE, _update_MEnvcfg_CBCFE, _update_MEnvcfg_CBZE, _update_MEnvcfg_SSE,
    _update_MEnvcfg_LPE, _update_MEnvcfg_FIOM, _get_MEnvcfg_LPE, _get_MEnvcfg_SSE,
    _get_MEnvcfg_CBZE, _get_MEnvcfg_CBCFE, _get_MEnvcfg_STCE, _get_MEnvcfg_ADUE,
    _get_MEnvcfg_PBMTE, Mk_MEnvcfg, Sail.BitVec.updateSubrange, Sail.BitVec.updateSubrange',
    Sail.BitVec.extractLsb, BitVec.extractLsb]
  bv_decide

/-- Rocq `st_menvcfg_LPE_final` ∘ `st_menv_adue_LPE`: the `menvcfg` the `mret` sees has
`LPE = 0`. -/
theorem WkStartNew.lpeFinal (menv0 : BitVec 64) (h : _get_MEnvcfg_LPE menv0 = 0#1) :
    _get_MEnvcfg_LPE (WeakLeafCsrw2.menvcfgLegalized (stMenvAdue menv0)
      (WkTimerinit.tiMenv1 (stMenvAdue menv0))) = 0#1 := by
  have hor : ∀ x c : BitVec 64, BitVec.extractLsb' 2 1 c = 0#1 →
      _get_MEnvcfg_LPE (x ||| c) = _get_MEnvcfg_LPE x := by
    intro x c hc
    simp only [_get_MEnvcfg_LPE, Sail.BitVec.extractLsb, BitVec.extractLsb] at hc ⊢
    bv_decide
  rw [WkStartNew.lpeLegal, WkTimerinit.tiMenv1, hor _ _ (by decide +kernel), stMenvAdue,
    WkStartNew.lpeLegal, hor _ _ (by decide +kernel), h]

/-! ### PMP (Rocq `pmp_allows_all_written`, `st_pmp_tor0_grants`) -/

/-- An unlocked entry's write result depends on the written byte only. -/
theorem WkStartNew.wcfgUnlocked (cfg v : BitVec 8) (h : pmpLocked cfg = false) :
    pmpWriteCfgVal cfg v = pmpWriteCfgVal 0#8 v := by
  unfold pmpWriteCfgVal
  simp only [h, show pmpLocked 0#8 = false by decide, Bool.false_eq_true, ↓reduceIte]

/-- Each of `pmpcfg0`'s eight bytes of `15` writes an unlocked entry. -/
theorem WkStartNew.vecupdLockFree (Y : Vector (BitVec 8) 64) (i : Nat) (hi : i < 8)
    (hY : pmpLocked Y[i]! = false) :
    pmpLocked (WeakLeafPmpcfg0.pmpcfg0Vecupd 15#64 Y i)[i]! = false := by
  unfold WeakLeafPmpcfg0.pmpcfg0Vecupd
  rw [vectorUpdate_get_same _ _ _ (by omega), WkStartNew.wcfgUnlocked _ _ hY]
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

/-- One byte step of `csrw pmpcfg0, 15` keeps every entry unlocked. -/
theorem WkStartNew.vecupdUnl (X : Vector (BitVec 8) 64) (i : Nat) (hi : i < 8)
    (hX : ∀ j : Nat, pmpLocked X[j]! = false) :
    ∀ j : Nat, pmpLocked (WeakLeafPmpcfg0.pmpcfg0Vecupd 15#64 X i)[j]! = false := by
  intro j
  by_cases hj : j = i
  · subst hj
    exact WkStartNew.vecupdLockFree X j hi (hX j)
  · unfold WeakLeafPmpcfg0.pmpcfg0Vecupd
    rw [vectorUpdate_get_ne _ _ _ _ hj]
    exact hX j

/-- A byte step at `i ≠ 0` leaves entry 0 alone. -/
theorem WkStartNew.vecupdKeep0 (X : Vector (BitVec 8) 64) (i : Nat) (hi : 0 ≠ i) :
    (WeakLeafPmpcfg0.pmpcfg0Vecupd 15#64 X i)[0]! = X[0]! := by
  unfold WeakLeafPmpcfg0.pmpcfg0Vecupd
  exact vectorUpdate_get_ne _ _ _ _ hi

/-- An entry whose A field is `0b01` is a TOR entry. -/
theorem WkStartNew.torOf (y : BitVec 8) (h : _get_Pmpcfg_ent_A y = 1#2) :
    pmpAddrMatchType_encdec_backwards (_get_Pmpcfg_ent_A y) = .TOR := by
  rw [h]; rfl

/-- Entry 0 after `csrw pmpcfg0, 15`: TOR, unlocked. -/
theorem WkStartNew.pmpcfg1Ent0 (cfg0 : RegisterType .pmpcfg_n) (hoff : pmpAllOff cfg0) :
    pmpAddrMatchType_encdec_backwards (_get_Pmpcfg_ent_A (stPmpcfg1 cfg0)[0]!) = .TOR ∧
      pmpLocked (stPmpcfg1 cfg0)[0]! = false := by
  unfold stPmpcfg1 WeakLeafPmpcfg0.pmpcfgWritten
  rw [WkStartNew.vecupdKeep0 _ 7 (by decide), WkStartNew.vecupdKeep0 _ 6 (by decide),
    WkStartNew.vecupdKeep0 _ 5 (by decide), WkStartNew.vecupdKeep0 _ 4 (by decide),
    WkStartNew.vecupdKeep0 _ 3 (by decide), WkStartNew.vecupdKeep0 _ 2 (by decide),
    WkStartNew.vecupdKeep0 _ 1 (by decide)]
  unfold WeakLeafPmpcfg0.pmpcfg0Vecupd
  rw [vectorUpdate_get_same _ _ _ (by decide), WkStartNew.wcfgUnlocked _ _ (hoff 0).2]
  exact ⟨WkStartNew.torOf _ (by decide +kernel), by decide +kernel⟩

/-- Rocq `pmp_allows_all_written`: no entry is locked after `csrw pmpcfg0, 15`. -/
theorem WkStartNew.pmpcfg1AllowsAll (cfg0 : RegisterType .pmpcfg_n) (hoff : pmpAllOff cfg0) :
    pmpAllowsAll (stPmpcfg1 cfg0) := by
  unfold stPmpcfg1 WeakLeafPmpcfg0.pmpcfgWritten pmpAllowsAll
  have h0 := WkStartNew.vecupdUnl cfg0 0 (by decide) (fun j => (hoff j).2)
  have h1 := WkStartNew.vecupdUnl _ 1 (by decide) h0
  have h2 := WkStartNew.vecupdUnl _ 2 (by decide) h1
  have h3 := WkStartNew.vecupdUnl _ 3 (by decide) h2
  have h4 := WkStartNew.vecupdUnl _ 4 (by decide) h3
  have h5 := WkStartNew.vecupdUnl _ 5 (by decide) h4
  have h6 := WkStartNew.vecupdUnl _ 6 (by decide) h5
  exact WkStartNew.vecupdUnl _ 7 (by decide) h6

/-- Entry 0 of the address table after `csrw pmpaddr0, 0x3fffffffffffff` from an all-off PMP. -/
theorem WkStartNew.pmpaddr1Ent0 (cfg0 : RegisterType .pmpcfg_n) (pa0 : RegisterType .pmpaddr_n)
    (hoff : pmpAllOff cfg0) : (stPmpaddr1 cfg0 pa0)[0]! = 0x3fffffffffffff#64 := by
  unfold stPmpaddr1 WeakLeafCsrw3.pmp0Newaddr
  rw [vectorUpdate_get_same _ _ _ (by decide)]
  have h0 : pmpLocked (GetElem?.getElem! cfg0 (0 : Nat)) = false := (hoff 0).2
  have h1 : pmpTORLocked (GetElem?.getElem! cfg0 ((0 : Nat) +i 1)) = false := by
    have h := (hoff 1).2
    unfold pmpLocked at h
    unfold pmpTORLocked
    rw [show (GetElem?.getElem! cfg0 ((0 : Nat) +i 1) : BitVec 8) = cfg0[1]! from rfl, h]
  simp only [pmpWriteAddr, h0, h1, Bool.or_false, Bool.false_eq_true, ↓reduceIte]
  decide +kernel

/-- Rocq `st_pmp_tor0_grants`: after the two PMP writes, TOR entry 0 grants an 8-byte access
below `0xfffffffffffffc`. -/
theorem WkStartNew.torGrants (cfg0 : RegisterType .pmpcfg_n) (pa0 : RegisterType .pmpaddr_n)
    (hoff : pmpAllOff cfg0) (ea : BitVec 64) (hb : ea.toNat + 8 ≤ 0xfffffffffffffc) :
    pmpTor0Grants (stPmpcfg1 cfg0) (stPmpaddr1 cfg0 pa0) ea 8 := by
  obtain ⟨hA, hL⟩ := WkStartNew.pmpcfg1Ent0 cfg0 hoff
  refine ⟨hA, hL, by decide, ?_⟩
  rw [WkStartNew.pmpaddr1Ent0 cfg0 pa0 hoff]
  have h4 : (0x3fffffffffffff#64 : BitVec 64).toNat * 4 = 0xfffffffffffffc := by decide
  omega

/-- Total lookups over the `stM*` insert chains (Rocq `st_unfold; st_look`, deviation 7). -/
macro "wk_sn_look" : tactic =>
  `(tactic| (simp (disch := decide +kernel) only [WkStartNew.stM30, WkStartNew.stM33,
      WkStartNew.stM34, WkStartNew.stM35, WkStartNew.stM36, WkStartNew.stM37, WkStartNew.stM38,
      WkStartNew.stM39, WkStartNew.stM40, WkStartNew.stM42, WkStartNew.stM43, WkStartNew.stM45,
      WkStartNew.stM47, WkStartNew.stM48, WkStartNew.stM51, WkStartNew.stM52, WkStartNew.stM54,
      WkStartNew.stM55, WkStartNew.stM57, WkStartNew.stMAe0, WkStartNew.stMAe1, WkStartNew.stMAe2,
      WkStartNew.stMAe3, WkStartNew.stM59, WkStartNew.stM60, WkStartNew.stM61, WkStartNew.stMout,
      RegMap.get_ne, RegMap.set_same, RegMap.set_other]; done))

/-! ## 2. The stack (deviation 6) -/

section stack
variable {GF : BundledGFunctors} [WeakGS GF]

/-- Rocq `wstack2_intro_ent` (Local): `wstackOwnPhys_2_intro` as one `∗`-shaped entailment. -/
theorem WkStartNew.wstack2IntroEnt (cpu : CPU) (sp : PAddr) (w1 w2 : BitVec 64) :
    iprop(wpt8Own (GF := GF) cpu (paStk sp 1) w1 ∗ wpt8Own cpu (paStk sp 2) w2) ⊢
      wstackOwnPhys cpu sp 2 :=
  WkTimerinit.stack2IntroEnt cpu sp w1 w2

end stack

/-! ## 3. THE THEOREM -/

section start
variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [WeakGS GF]

/-- Rocq `wwp_start` (deviations 1-6): the whole weak `start()` chain, through the `timerinit()`
call and the `mret` into Supervisor mode at `<main>`. -/
theorem wwpStart (gen : Nat) (cpu : CPU) (ξ : CtxId) (c : MConf) (m : RegMap)
    (sp0 ra0 s00 mhartidIn : BitVec 64) (n : Nat) (kbs : GMapF PAddr (BitVec 8)) :
    gen = 0 →
    4 ≤ n →
    MConf.mok c →
    pmpAllOff c.pmpcfg →
    _get_MEnvcfg_LPE c.menvcfg = 0#1 →
    _get_Mstatus_SXL c.mstatus = 2#2 →
    m cspRs1 = sp0 →
    m tiRa = ra0 →
    m tiS0 = s00 →
    (WkTimerinit.tiEaRa (WkTimerinit.tiSp1 sp0)).toNat + 8 ≤ 0xfffffffffffffc →
    (WkTimerinit.tiEaS0 (WkTimerinit.tiSp1 sp0)).toNat + 8 ≤ 0xfffffffffffffc →
    inRam (WkTimerinit.tiEaRa sp0) 8 →
    inRam (WkTimerinit.tiEaS0 sp0) 8 →
    inRam (WkTimerinit.tiEaRa (WkTimerinit.tiSp1 sp0)) 8 →
    inRam (WkTimerinit.tiEaS0 (WkTimerinit.tiSp1 sp0)) 8 →
    wkbCovers kbs →
    whartRun (GF := GF) cpu ξ 1 c ⊢
      clockCells cpu -∗
      pcIs cpu stPc30 -∗
      gprFile cpu m -∗
      Register.mhartid ↦ᵣ[cpu] mhartidIn -∗
      cobj ξ (wstackOwnPhys (GF := GF) cpu sp0 n) -∗
      wkernelText (GF := GF) kbs -∗
      (∀ tv : BitVec 64,
        sConf cpu (DFrac.own 1) (stConfOut c tv) -∗
        clockCells cpu -∗
        pcIs cpu stMain -∗
        gprFile cpu (stMout m sp0 c tv mhartidIn) -∗
        Register.mhartid ↦ᵣ[cpu] mhartidIn -∗
        wrunning cpu ξ -∗
        cobj ξ (wstackOwnPhys (GF := GF) cpu sp0 n) -∗
        wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu)) -∗
      wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu) := by
  intro hgid hn4 hmok hoff hlpe hsxl hsp hra hs0 hbndRa hbndS0 hram1 hram2 hramTiRa hramTiS0 hcov
  iintro Hrun Hclk Hpc Hfile Hmh Hstk #Htext Hcont
  -- ---- the stack: start's two slots, timerinit's frame, the deep rest (all OBJECTIVE) ----
  icases WkTimerinit.stackSplit ξ cpu sp0 n (by omega) $$ Hstk with ⟨%vra, %vs0, Hsra, Hss0, Hdeep⟩
  icases cobjMono ξ _ _ (wstackOwnPhys_split_1 cpu (paStk sp0 2) 2 (n - 2) (by omega)) $$ Hdeep
    with Hdeep
  icases (cobjSep ξ _ _).1 $$ Hdeep with ⟨Hti2, Hdeep⟩
  have hstkTo : cobj (GF := GF) ξ (wstackOwnPhys cpu (paStk sp0 2) 2) ⊢
      cobj ξ (wstackOwnPhys cpu (WkTimerinit.tiSp1 sp0) 2) := by
    rw [WkStartNew.tiSp1Stk]
  have hstkFrom : cobj (GF := GF) ξ (wstackOwnPhys cpu (WkTimerinit.tiSp1 sp0) 2) ⊢
      cobj ξ (wstackOwnPhys cpu (paStk sp0 2) 2) := by
    rw [WkStartNew.tiSp1Stk]
  ihave Hti2 := hstkTo $$ Hti2
  have hram1' : inRam (paStk sp0 1) 8 := WkTimerinit.eaRaStk sp0 ▸ hram1
  have hram2' : inRam (paStk sp0 2) 8 := WkTimerinit.eaS0Stk sp0 ▸ hram2
  -- ---- pure side conditions ----
  have hpmpU : pmpAllowsAll c.pmpcfg := fun i => (hoff i).2
  have hpmp1 : pmpAllowsAll (stPmpcfg1 c.pmpcfg) := WkStartNew.pmpcfg1AllowsAll c.pmpcfg hoff
  have htorRa : pmpTor0Grants (stPmpcfg1 c.pmpcfg) (stPmpaddr1 c.pmpcfg c.pmpaddr)
      (WkTimerinit.tiEaRa (WkTimerinit.tiSp1 sp0)) 8 :=
    WkStartNew.torGrants c.pmpcfg c.pmpaddr hoff _ hbndRa
  have htorS0 : pmpTor0Grants (stPmpcfg1 c.pmpcfg) (stPmpaddr1 c.pmpcfg c.pmpaddr)
      (WkTimerinit.tiEaS0 (WkTimerinit.tiSp1 sp0)) 8 :=
    WkStartNew.torGrants c.pmpcfg c.pmpaddr hoff _ hbndS0
  obtain ⟨hb3, hb17, hbsxl, -⟩ := WkStartNew.ms1Bits c.mstatus
  have hmok1 : MConf.mok (stC41 c) := ⟨by rw [← hmok.1]; exact hb3, by rw [← hmok.2]; exact hb17⟩
  have hsxl1 : _get_Mstatus_SXL (stC41 c).mstatus = 2#2 := hbsxl.trans hsxl
  have hb0 := WeakLeafCsrw2.mokBits c hmok
  have hb1 := WeakLeafCsrw2.mokBits (stC41 c) hmok1
  have hcli : ∀ M : RegMap, M.get cliRs1 = 0#64 := fun M => by
    unfold RegMap.get; rw [if_pos (show cliRs1 = 0#5 by decide)]
  have hcspT : WkTimerinitAux.cspRs1 = cspRs1 := by decide +kernel
  -- closed-value bridges (Rocq: verbatim off WpStartNew)
  have hs9 : sign_extend (m := 64) (sign_extend (m := 12) i9) =
      sign_extend (m := 64) WkTimerinitAux.i9 := by decide +kernel
  have hm1v : WkEntryEff.luival (sign_extend (m := 20) si35) + sign_extend (m := 64) si36 =
      stMaskAnd := by decide +kernel
  have hm2v : WkEntryEff.luival (sign_extend (m := 20) si38) + sign_extend (m := 64) si39 =
      stMaskOr := by decide +kernel
  have ha42v : stPc42 + auipcOff si42 = stA42v := by decide +kernel
  have ha43v : stA42v + sign_extend (m := 64) si43 = stMain := by decide +kernel
  have hmepcv : WeakLeafCsrw2.mepcVal stMain = stMain := by decide +kernel
  have hs45 : sign_extend (m := 64) (sign_extend (m := 12) si45) = 0#64 := by decide +kernel
  have hffv : WkEntryEff.luival (sign_extend (m := 20) si47) +
      sign_extend (m := 64) (sign_extend (m := 12) si48) = stFfff := by decide +kernel
  have hs54 : sign_extend (m := 64) (sign_extend (m := 12) si54) = WkTimerinit.cliWval si54 := by
    decide +kernel
  have hshv : shift_bits_right (WkTimerinit.cliWval si54)
      (Sail.BitVec.extractLsb ssh55 (Functions.log2_xlen -i 1) 0) = stPmpw := by decide +kernel
  have hs57 : sign_extend (m := 64) (sign_extend (m := 12) si57) = 15#64 := by decide +kernel
  have hsae : sign_extend (m := 64) (sign_extend (m := 12) saeLi) = WkTimerinit.cliWval saeLi := by
    decide +kernel
  have hb61 : shift_bits_left (WkTimerinit.cliWval saeLi)
      (Sail.BitVec.extractLsb saeSlli (Functions.log2_xlen -i 1) 0) = stAdueBit := by decide +kernel
  have hlinkv : BitVec.addInt stPc59 4 = stRaLink := by decide +kernel
  have hjal : is_aligned_paddr (.Physaddr (stPc59 + sign_extend (m := 64) sjimm59)) 4 = true := by
    decide +kernel
  have hp59 : stPc59 + sign_extend (m := 64) sjimm59 = WkTimerinitAux.tiPc9 := by decide +kernel
  have hcretv : WeakLeafMret.retPc stRaLink = stPc60 := by decide +kernel
  have hs61 : sign_extend (m := 64) (sign_extend (m := 12) si61) = sign_extend (m := 64) si61 := by
    decide +kernel
  -- ==================================================================
  -- ---- 30. c.addi sp, -16 ----
  ihave #Hi30 := wsti30 (GF := GF) kbs hcov $$ Htext
  iapply wwpAddiRun gen cpu ξ stPc30 true cspRs1 cspRs1 (sign_extend (m := 12) i9) m c 1 hgid hmok
    hpmpU (by decide +kernel) $$ Hrun Hclk Hpc Hfile Hi30
  iintro Hrun Hclk Hpc Hfile
  rw [RegMap.get_ne m cspRs1 (by decide +kernel), hsp, hs9,
    show m.set cspRs1 (sp0 + sign_extend (m := 64) WkTimerinitAux.i9) = stM30 m sp0 from rfl,
    show BitVec.addInt stPc30 (if true then 2 else 4) = stPc31 by decide +kernel]
  -- ---- 31. c.sdsp ra, 8(sp)  (RELEASE store, all-OFF PMP) ----
  have Lsp : stM30 m sp0 cspRs1 = WkTimerinit.tiSp1 sp0 := by wk_sn_look
  have Lra : stM30 m sp0 tiRa = ra0 := by rw [← hra]; wk_sn_look
  have Ls0 : stM30 m sp0 tiS0 = s00 := by rw [← hs0]; wk_sn_look
  ihave #Hi31 := wsti31 (GF := GF) kbs hcov $$ Htext
  icases gprFile_acc_2 cpu (stM30 m sp0) cspRs1 tiRa (by decide +kernel) (by decide +kernel)
    (by decide +kernel) $$ Hfile with ⟨Hspc, Hrac, Hfacc⟩
  rw [Lsp, Lra]
  ihave HR := WkTimerinit.cobjTrue (GF := GF) ξ
  iapply wwpSd8OffRvcRun gen cpu ξ stPc31 cspRs1 tiRa (zero_extend (m := 12) (u10 +++ 0b000#3))
    (paStk sp0 1) vra iprop(⌜True⌝) 1 c (WkTimerinit.tiSp1 sp0) ra0 hgid hmok hoff
    (by decide +kernel) (by decide +kernel) (WkStartNew.ea1Stk sp0) hram1'
    $$ Hrun Hclk Hpc Hspc Hrac Hi31 Hsra HR
  iintro %T31 - Hrun Hclk Hpc Hspc Hrac Hsra -
  ihave Hfile := Hfacc $$ %(WkTimerinit.tiSp1 sp0) %ra0 Hspc Hrac
  rw [rfUpd2Same (stM30 m sp0) cspRs1 tiRa _ _ (by decide +kernel) Lsp Lra,
    show BitVec.addInt stPc31 2 = stPc32 by decide +kernel]
  -- ---- 32. c.sdsp s0, 0(sp) ----
  ihave #Hi32 := wsti32 (GF := GF) kbs hcov $$ Htext
  icases gprFile_acc_2 cpu (stM30 m sp0) cspRs1 tiS0 (by decide +kernel) (by decide +kernel)
    (by decide +kernel) $$ Hfile with ⟨Hspc, Hs0c, Hfacc⟩
  rw [Lsp, Ls0]
  ihave HR := WkTimerinit.cobjTrue (GF := GF) ξ
  iapply wwpSd8OffRvcRun gen cpu ξ stPc32 cspRs1 tiS0 (zero_extend (m := 12) (u11 +++ 0b000#3))
    (paStk sp0 2) vs0 iprop(⌜True⌝) 1 c (WkTimerinit.tiSp1 sp0) s00 hgid hmok hoff
    (by decide +kernel) (by decide +kernel) (WkStartNew.ea2Stk sp0) hram2'
    $$ Hrun Hclk Hpc Hspc Hs0c Hi32 Hss0 HR
  iintro %T32 - Hrun Hclk Hpc Hspc Hs0c Hss0 -
  ihave Hfile := Hfacc $$ %(WkTimerinit.tiSp1 sp0) %s00 Hspc Hs0c
  rw [rfUpd2Same (stM30 m sp0) cspRs1 tiS0 _ _ (by decide +kernel) Lsp Ls0,
    show BitVec.addInt stPc32 2 = stPc33 by decide +kernel]
  -- ---- 33. c.addi4spn s0, sp, 16  (s0 := sp0) ----
  ihave #Hi33 := wsti33 (GF := GF) kbs hcov $$ Htext
  iapply wwpAddiRun gen cpu ξ stPc33 true cspRs1 tiS0 (caddi4spnImm nz12) (stM30 m sp0) c 1 hgid
    hmok hpmpU (by decide +kernel) $$ Hrun Hclk Hpc Hfile Hi33
  iintro Hrun Hclk Hpc Hfile
  rw [RegMap.get_ne (stM30 m sp0) cspRs1 (by decide +kernel), Lsp, WkStartNew.stS016,
    show (stM30 m sp0).set tiS0 sp0 = stM33 m sp0 from rfl,
    show BitVec.addInt stPc33 (if true then 2 else 4) = stPc34 by decide +kernel]
  -- ---- 34. csrr a5, mstatus  (cell-based: open the bundle) ----
  ihave #Hi34 := wsti34 (GF := GF) kbs hcov $$ Htext
  icases whartRunOpen (GF := GF) cpu ξ 1 c $$ Hrun with ⟨Hm, Hview⟩
  mconf_cases Hm
  icases gprFile_acc cpu (stM33 m sp0) tiA5 (by decide +kernel) $$ Hfile with ⟨Ha5c, Hfins⟩
  iapply wwpCsrrMstatusO gen cpu ξ stPc34 tiA5 c.mstatus (stM33 m sp0 tiA5) c.pmpcfg hgid hpmpU
    (by decide +kernel) hb0.1 hb0.2
    $$ Hhw Hclk Hhart_state Hcur_privilege Hmstatus Hpmpcfg_n Hpc Ha5c Hi34 Hview
  iintro Hhart_state Hcur_privilege Hmstatus Hpmpcfg_n Hclk Hpc Ha5c Hview
  ihave Hm := mConf_introW cpu (DFrac.own 1) c $$ Hcur_privilege Hhart_state Hmstatus Hmie Hmideleg
    Hmedeleg Hmepc Hsatp Hmenvcfg Hmcounteren Hmtimecmp Hstimecmp Hpmpcfg_n Hpmpaddr_n Hhw
  ihave Hrun := whartRunClose (GF := GF) cpu ξ 1 c $$ Hm Hview
  ihave Hfile := Hfins $$ %(c.mstatus) Ha5c
  rw [show (stM33 m sp0).set tiA5 c.mstatus = stM34 m sp0 c from rfl,
    show BitVec.addInt stPc34 4 = stPc35 by decide +kernel]
  -- ---- 35. c.lui a4, 0xffffe ----
  ihave #Hi35 := wsti35 (GF := GF) kbs hcov $$ Htext
  iapply wwpLuiRun gen cpu ξ stPc35 true tiA4 (sign_extend (m := 20) si35) (stM34 m sp0 c) c 1 hgid
    hmok hpmpU (by decide +kernel) $$ Hrun Hclk Hpc Hfile Hi35
  iintro Hrun Hclk Hpc Hfile
  rw [show (stM34 m sp0 c).set tiA4 (WkEntryEff.luival (sign_extend (m := 20) si35)) =
      stM35 m sp0 c from rfl,
    show BitVec.addInt stPc35 (if true then 2 else 4) = stPc36 by decide +kernel]
  -- ---- 36. addi a4, a4, 2047 ----
  have L36a4 : (stM35 m sp0 c).get tiA4 = WkEntryEff.luival (sign_extend (m := 20) si35) := by
    wk_sn_look
  ihave #Hi36 := wsti36 (GF := GF) kbs hcov $$ Htext
  iapply wwpAddiRun gen cpu ξ stPc36 false tiA4 tiA4 si36 (stM35 m sp0 c) c 1 hgid hmok hpmpU
    (by decide +kernel) $$ Hrun Hclk Hpc Hfile Hi36
  iintro Hrun Hclk Hpc Hfile
  rw [L36a4, hm1v, show (stM35 m sp0 c).set tiA4 stMaskAnd = stM36 m sp0 c from rfl,
    show BitVec.addInt stPc36 (if false then 2 else 4) = stPc37 by decide +kernel]
  -- ---- 37. c.and a5, a4 ----
  have L37a5 : (stM36 m sp0 c).get tiA5 = c.mstatus := by wk_sn_look
  have L37a4 : (stM36 m sp0 c).get tiA4 = stMaskAnd := by wk_sn_look
  ihave #Hi37 := wsti37 (GF := GF) kbs hcov $$ Htext
  iapply wwpAndRvcRun gen cpu ξ stPc37 tiA4 tiA5 tiA5 (stM36 m sp0 c) c 1 hgid hmok hpmpU
    (by decide +kernel) $$ Hrun Hclk Hpc Hfile Hi37
  iintro Hrun Hclk Hpc Hfile
  rw [L37a5, L37a4, show (stM36 m sp0 c).set tiA5 (c.mstatus &&& stMaskAnd) = stM37 m sp0 c from rfl,
    show BitVec.addInt stPc37 2 = stPc38 by decide +kernel]
  -- ---- 38. c.lui a4, 1 ----
  ihave #Hi38 := wsti38 (GF := GF) kbs hcov $$ Htext
  iapply wwpLuiRun gen cpu ξ stPc38 true tiA4 (sign_extend (m := 20) si38) (stM37 m sp0 c) c 1 hgid
    hmok hpmpU (by decide +kernel) $$ Hrun Hclk Hpc Hfile Hi38
  iintro Hrun Hclk Hpc Hfile
  rw [show (stM37 m sp0 c).set tiA4 (WkEntryEff.luival (sign_extend (m := 20) si38)) =
      stM38 m sp0 c from rfl,
    show BitVec.addInt stPc38 (if true then 2 else 4) = stPc39 by decide +kernel]
  -- ---- 39. addi a4, a4, -2048 ----
  have L39a4 : (stM38 m sp0 c).get tiA4 = WkEntryEff.luival (sign_extend (m := 20) si38) := by
    wk_sn_look
  ihave #Hi39 := wsti39 (GF := GF) kbs hcov $$ Htext
  iapply wwpAddiRun gen cpu ξ stPc39 false tiA4 tiA4 si39 (stM38 m sp0 c) c 1 hgid hmok hpmpU
    (by decide +kernel) $$ Hrun Hclk Hpc Hfile Hi39
  iintro Hrun Hclk Hpc Hfile
  rw [L39a4, hm2v, show (stM38 m sp0 c).set tiA4 stMaskOr = stM39 m sp0 c from rfl,
    show BitVec.addInt stPc39 (if false then 2 else 4) = stPc40 by decide +kernel]
  -- ---- 40. c.or a5, a4 ----
  have L40a5 : (stM39 m sp0 c).get tiA5 = c.mstatus &&& stMaskAnd := by wk_sn_look
  have L40a4 : (stM39 m sp0 c).get tiA4 = stMaskOr := by wk_sn_look
  ihave #Hi40 := wsti40 (GF := GF) kbs hcov $$ Htext
  iapply wwpOrRvcRun gen cpu ξ stPc40 tiA4 tiA5 tiA5 (stM39 m sp0 c) c 1 hgid hmok hpmpU
    (by decide +kernel) $$ Hrun Hclk Hpc Hfile Hi40
  iintro Hrun Hclk Hpc Hfile
  rw [L40a5, L40a4,
    show (stM39 m sp0 c).set tiA5 ((c.mstatus &&& stMaskAnd) ||| stMaskOr) = stM40 m sp0 c from rfl,
    show BitVec.addInt stPc40 2 = stPc41 by decide +kernel]
  -- ---- 41. csrw mstatus, a5  (cell-based) ----
  have L41a5 : stM40 m sp0 c tiA5 = stVa540 c.mstatus := by wk_sn_look
  ihave #Hi41 := wsti41 (GF := GF) kbs hcov $$ Htext
  icases whartRunOpen (GF := GF) cpu ξ 1 c $$ Hrun with ⟨Hm, Hview⟩
  mconf_cases Hm
  icases gprFile_lookup_acc cpu (stM40 m sp0 c) tiA5 (by decide +kernel) $$ Hfile with ⟨Ha5c, Hfb⟩
  rw [L41a5]
  iapply wwpCsrwMstatusO gen cpu ξ stPc41 tiA5 c.mstatus (stVa540 c.mstatus) c.pmpcfg hgid hpmpU
    (by decide +kernel) (by decide +kernel) hb0.1 hb0.2
    $$ Hhw Hclk Hhart_state Hcur_privilege Hmstatus Hpmpcfg_n Hpc Ha5c Hi41 Hview
  iintro Hhart_state Hcur_privilege Hmstatus Hpmpcfg_n Hclk Hpc Ha5c Hview
  ihave Hm := mConf_introW cpu (DFrac.own 1)
      { c with mstatus := WeakLeafCsrw.mstatusLegalized c.mstatus (stVa540 c.mstatus) }
    $$ Hcur_privilege Hhart_state Hmstatus Hmie Hmideleg Hmedeleg Hmepc Hsatp Hmenvcfg Hmcounteren
      Hmtimecmp Hstimecmp Hpmpcfg_n Hpmpaddr_n Hhw
  ihave Hrun := whartRunClose (GF := GF) cpu ξ 1 _ $$ Hm Hview
  ihave Hfile := Hfb $$ Ha5c
  rw [show ({ c with mstatus := WeakLeafCsrw.mstatusLegalized c.mstatus (stVa540 c.mstatus) } :
      MConf) = stC41 c from rfl,
    show BitVec.addInt stPc41 4 = stPc42 by decide +kernel]
  -- ---- 42. auipc a5, 1 ----
  ihave #Hi42 := wsti42 (GF := GF) kbs hcov $$ Htext
  iapply wwpAuipcRun gen cpu ξ stPc42 tiA5 si42 (stM40 m sp0 c) (stC41 c) 1 hgid hmok1 hpmpU
    (by decide +kernel) $$ Hrun Hclk Hpc Hfile Hi42
  iintro Hrun Hclk Hpc Hfile
  rw [ha42v, show (stM40 m sp0 c).set tiA5 stA42v = stM42 m sp0 c from rfl,
    show BitVec.addInt stPc42 4 = stPc43 by decide +kernel]
  -- ---- 43. addi a5, a5, -426  (a5 := <main>) ----
  have L43a5 : (stM42 m sp0 c).get tiA5 = stA42v := by wk_sn_look
  ihave #Hi43 := wsti43 (GF := GF) kbs hcov $$ Htext
  iapply wwpAddiRun gen cpu ξ stPc43 false tiA5 tiA5 si43 (stM42 m sp0 c) (stC41 c) 1 hgid hmok1
    hpmpU (by decide +kernel) $$ Hrun Hclk Hpc Hfile Hi43
  iintro Hrun Hclk Hpc Hfile
  rw [L43a5, ha43v, show (stM42 m sp0 c).set tiA5 stMain = stM43 m sp0 c from rfl,
    show BitVec.addInt stPc43 (if false then 2 else 4) = stPc44 by decide +kernel]
  -- ---- 44. csrw mepc, a5 ----
  have L44a5 : stM43 m sp0 c tiA5 = stMain := by wk_sn_look
  ihave #Hi44 := wsti44 (GF := GF) kbs hcov $$ Htext
  icases gprFile_lookup_acc cpu (stM43 m sp0 c) tiA5 (by decide +kernel) $$ Hfile with ⟨Ha5c, Hfb⟩
  rw [L44a5]
  iapply wwpCsrwMepcRun gen cpu ξ stPc44 tiA5 stMain (stC41 c) hgid hmok1 hpmpU (by decide +kernel)
    $$ Hrun Hclk Hpc Ha5c Hi44
  iintro Hrun Hclk Hpc Ha5c
  ihave Hfile := Hfb $$ Ha5c
  rw [hmepcv, show ({ stC41 c with mepc := stMain } : MConf) = stC44 c from rfl,
    show BitVec.addInt stPc44 4 = stPc45 by decide +kernel]
  -- ---- 45. c.li a5, 0 ----
  ihave #Hi45 := wsti45 (GF := GF) kbs hcov $$ Htext
  iapply wwpAddiRun gen cpu ξ stPc45 true cliRs1 tiA5 (sign_extend (m := 12) si45) (stM43 m sp0 c)
    (stC44 c) 1 hgid hmok1 hpmpU (by decide +kernel) $$ Hrun Hclk Hpc Hfile Hi45
  iintro Hrun Hclk Hpc Hfile
  rw [hcli, BitVec.zero_add, hs45, show (stM43 m sp0 c).set tiA5 0#64 = stM45 m sp0 c from rfl,
    show BitVec.addInt stPc45 (if true then 2 else 4) = stPc46 by decide +kernel]
  -- ---- 46. csrw satp, a5  (Bare) ----
  have L46a5 : stM45 m sp0 c tiA5 = 0#64 := by wk_sn_look
  ihave #Hi46 := wsti46 (GF := GF) kbs hcov $$ Htext
  icases gprFile_lookup_acc cpu (stM45 m sp0 c) tiA5 (by decide +kernel) $$ Hfile with ⟨Ha5c, Hfb⟩
  rw [L46a5]
  iapply wwpCsrwSatpRun gen cpu ξ stPc46 tiA5 0#64 (stC44 c) hgid hmok1 hpmpU (by decide +kernel)
    hsxl1 $$ Hrun Hclk Hpc Ha5c Hi46
  iintro Hrun Hclk Hpc Ha5c
  ihave Hfile := Hfb $$ Ha5c
  rw [show ({ stC44 c with satp := WeakLeafCsrw3.satpLegalized (stC44 c).satp 0#64 } : MConf) =
      stC46 c from rfl,
    show BitVec.addInt stPc46 4 = stPc47 by decide +kernel]
  -- ---- 47. c.lui a5, 0x10 ----
  ihave #Hi47 := wsti47 (GF := GF) kbs hcov $$ Htext
  iapply wwpLuiRun gen cpu ξ stPc47 true tiA5 (sign_extend (m := 20) si47) (stM45 m sp0 c) (stC46 c)
    1 hgid hmok1 hpmpU (by decide +kernel) $$ Hrun Hclk Hpc Hfile Hi47
  iintro Hrun Hclk Hpc Hfile
  rw [show (stM45 m sp0 c).set tiA5 (WkEntryEff.luival (sign_extend (m := 20) si47)) =
      stM47 m sp0 c from rfl,
    show BitVec.addInt stPc47 (if true then 2 else 4) = stPc48 by decide +kernel]
  -- ---- 48. c.addi a5, -1  (a5 := 0xffff) ----
  have L48a5 : (stM47 m sp0 c).get tiA5 = WkEntryEff.luival (sign_extend (m := 20) si47) := by
    wk_sn_look
  ihave #Hi48 := wsti48 (GF := GF) kbs hcov $$ Htext
  iapply wwpAddiRun gen cpu ξ stPc48 true tiA5 tiA5 (sign_extend (m := 12) si48) (stM47 m sp0 c)
    (stC46 c) 1 hgid hmok1 hpmpU (by decide +kernel) $$ Hrun Hclk Hpc Hfile Hi48
  iintro Hrun Hclk Hpc Hfile
  rw [L48a5, hffv, show (stM47 m sp0 c).set tiA5 stFfff = stM48 m sp0 c from rfl,
    show BitVec.addInt stPc48 (if true then 2 else 4) = stPc49 by decide +kernel]
  -- ---- 49. csrw medeleg, a5 ----
  have L49a5 : stM48 m sp0 c tiA5 = stFfff := by wk_sn_look
  ihave #Hi49 := wsti49 (GF := GF) kbs hcov $$ Htext
  icases gprFile_lookup_acc cpu (stM48 m sp0 c) tiA5 (by decide +kernel) $$ Hfile with ⟨Ha5c, Hfb⟩
  rw [L49a5]
  iapply wwpCsrwMedelegRun gen cpu ξ stPc49 tiA5 stFfff (stC46 c) hgid hmok1 hpmpU (by decide +kernel)
    $$ Hrun Hclk Hpc Ha5c Hi49
  iintro Hrun Hclk Hpc Ha5c
  ihave Hfile := Hfb $$ Ha5c
  rw [show ({ stC46 c with medeleg := legalize_medeleg (stC46 c).medeleg stFfff } : MConf) =
      stC49 c from rfl,
    show BitVec.addInt stPc49 4 = stPc50 by decide +kernel]
  -- ---- 50. csrw mideleg, a5 ----
  ihave #Hi50 := wsti50 (GF := GF) kbs hcov $$ Htext
  icases gprFile_lookup_acc cpu (stM48 m sp0 c) tiA5 (by decide +kernel) $$ Hfile with ⟨Ha5c, Hfb⟩
  rw [L49a5]
  iapply wwpCsrwMidelegRun gen cpu ξ stPc50 tiA5 stFfff (stC49 c) hgid hmok1 hpmpU (by decide +kernel)
    $$ Hrun Hclk Hpc Ha5c Hi50
  iintro Hrun Hclk Hpc Ha5c
  ihave Hfile := Hfb $$ Ha5c
  rw [show ({ stC49 c with mideleg := WeakLeafCsrw2.midelegLegalized (stC49 c).mideleg stFfff } :
      MConf) = stC50 c from rfl,
    show BitVec.addInt stPc50 4 = stPc51 by decide +kernel]
  -- ---- 51. csrr a5, sie ----
  ihave #Hi51 := wsti51 (GF := GF) kbs hcov $$ Htext
  icases gprFile_acc cpu (stM48 m sp0 c) tiA5 (by decide +kernel) $$ Hfile with ⟨Ha5c, Hfins⟩
  iapply wwpCsrrSieRun gen cpu ξ stPc51 tiA5 (stM48 m sp0 c tiA5) (stC50 c) 1 hgid hmok1 hpmpU
    (by decide +kernel) $$ Hrun Hclk Hpc Ha5c Hi51
  iintro Hrun Hclk Hpc Ha5c
  ihave Hfile := Hfins $$ %(lower_mie (stC50 c).mie (stC50 c).mideleg) Ha5c
  rw [show (stM48 m sp0 c).set tiA5 (lower_mie (stC50 c).mie (stC50 c).mideleg) = stM51 m sp0 c
      from rfl,
    show BitVec.addInt stPc51 4 = stPc52 by decide +kernel]
  -- ---- 52. ori a5, a5, 544 ----
  have L52a5 : (stM51 m sp0 c).get tiA5 = lower_mie c.mie (stMdl1 c.mideleg) := by wk_sn_look
  ihave #Hi52 := wsti52 (GF := GF) kbs hcov $$ Htext
  iapply wwpOriRun gen cpu ξ stPc52 tiA5 tiA5 si52 (stM51 m sp0 c) (stC50 c) 1 hgid hmok1 hpmpU
    (by decide +kernel) $$ Hrun Hclk Hpc Hfile Hi52
  iintro Hrun Hclk Hpc Hfile
  rw [L52a5, show (stM51 m sp0 c).set tiA5 (lower_mie c.mie (stMdl1 c.mideleg) |||
      sign_extend (m := 64) si52) = stM52 m sp0 c from rfl,
    show BitVec.addInt stPc52 4 = stPc53 by decide +kernel]
  -- ---- 53. csrw sie, a5 ----
  have L53a5 : stM52 m sp0 c tiA5 = stVa552 c.mie c.mideleg := by wk_sn_look
  ihave #Hi53 := wsti53 (GF := GF) kbs hcov $$ Htext
  icases gprFile_lookup_acc cpu (stM52 m sp0 c) tiA5 (by decide +kernel) $$ Hfile with ⟨Ha5c, Hfb⟩
  rw [L53a5]
  iapply wwpCsrwSieRun gen cpu ξ stPc53 tiA5 (stVa552 c.mie c.mideleg) (stC50 c) hgid hmok1 hpmpU
    (by decide +kernel) $$ Hrun Hclk Hpc Ha5c Hi53
  iintro Hrun Hclk Hpc Ha5c
  ihave Hfile := Hfb $$ Ha5c
  rw [show ({ stC50 c with
      mie := (WeakLeafCsrw3.sieNewMie (stC50 c).mie (stC50 c).mideleg (stVa552 c.mie c.mideleg)) } : MConf) = stC53 c from rfl,
    show BitVec.addInt stPc53 4 = stPc54 by decide +kernel]
  -- ---- 54. c.li a5, -1 ----
  ihave #Hi54 := wsti54 (GF := GF) kbs hcov $$ Htext
  iapply wwpAddiRun gen cpu ξ stPc54 true cliRs1 tiA5 (sign_extend (m := 12) si54) (stM52 m sp0 c)
    (stC53 c) 1 hgid hmok1 hpmpU (by decide +kernel) $$ Hrun Hclk Hpc Hfile Hi54
  iintro Hrun Hclk Hpc Hfile
  rw [hcli, BitVec.zero_add, hs54,
    show (stM52 m sp0 c).set tiA5 (WkTimerinit.cliWval si54) = stM54 m sp0 c from rfl,
    show BitVec.addInt stPc54 (if true then 2 else 4) = stPc55 by decide +kernel]
  -- ---- 55. c.srli a5, 10 ----
  have L55a5 : (stM54 m sp0 c).get tiA5 = WkTimerinit.cliWval si54 := by wk_sn_look
  ihave #Hi55 := wsti55 (GF := GF) kbs hcov $$ Htext
  iapply wwpSrliRvcRun gen cpu ξ stPc55 tiA5 tiA5 ssh55 (stM54 m sp0 c) (stC53 c) 1 hgid hmok1 hpmpU
    (by decide +kernel) $$ Hrun Hclk Hpc Hfile Hi55
  iintro Hrun Hclk Hpc Hfile
  rw [L55a5, hshv, show (stM54 m sp0 c).set tiA5 stPmpw = stM55 m sp0 c from rfl,
    show BitVec.addInt stPc55 2 = stPc56 by decide +kernel]
  -- ---- 56. csrw pmpaddr0, a5 ----
  have L56a5 : stM55 m sp0 c tiA5 = stPmpw := by wk_sn_look
  ihave #Hi56 := wsti56 (GF := GF) kbs hcov $$ Htext
  icases gprFile_lookup_acc cpu (stM55 m sp0 c) tiA5 (by decide +kernel) $$ Hfile with ⟨Ha5c, Hfb⟩
  rw [L56a5]
  iapply wwpCsrwPmpaddr0Run gen cpu ξ stPc56 tiA5 stPmpw (stC53 c) hgid hmok1 hpmpU
    (by decide +kernel) $$ Hrun Hclk Hpc Ha5c Hi56
  iintro Hrun Hclk Hpc Ha5c
  ihave Hfile := Hfb $$ Ha5c
  rw [show ({ stC53 c with
      pmpaddr := (WeakLeafCsrw3.pmp0Newaddr (stC53 c).pmpcfg (stC53 c).pmpaddr stPmpw) } : MConf) = stC56 c from rfl,
    show BitVec.addInt stPc56 4 = stPc57 by decide +kernel]
  -- ---- 57. c.li a5, 15 ----
  ihave #Hi57 := wsti57 (GF := GF) kbs hcov $$ Htext
  iapply wwpAddiRun gen cpu ξ stPc57 true cliRs1 tiA5 (sign_extend (m := 12) si57) (stM55 m sp0 c)
    (stC56 c) 1 hgid hmok1 hpmpU (by decide +kernel) $$ Hrun Hclk Hpc Hfile Hi57
  iintro Hrun Hclk Hpc Hfile
  rw [hcli, BitVec.zero_add, hs57, show (stM55 m sp0 c).set tiA5 15#64 = stM57 m sp0 c from rfl,
    show BitVec.addInt stPc57 (if true then 2 else 4) = stPc58 by decide +kernel]
  -- ---- 58. csrw pmpcfg0, a5  (cell-based) ----
  have L58a5 : stM57 m sp0 c tiA5 = 15#64 := by wk_sn_look
  ihave #Hi58 := wsti58 (GF := GF) kbs hcov $$ Htext
  icases whartRunOpen (GF := GF) cpu ξ 1 (stC56 c) $$ Hrun with ⟨Hm, Hview⟩
  mconf_cases Hm
  icases gprFile_lookup_acc cpu (stM57 m sp0 c) tiA5 (by decide +kernel) $$ Hfile with ⟨Ha5c, Hfb⟩
  rw [L58a5]
  iapply wwpCsrwPmpcfg0O gen cpu ξ stPc58 tiA5 (stC56 c).mstatus 15#64 (stC56 c).pmpcfg hgid hpmpU
    (by decide +kernel) hb1.1 hb1.2
    $$ Hhw Hclk Hhart_state Hcur_privilege Hmstatus Hpmpcfg_n Hpc Ha5c Hi58 Hview
  iintro Hhart_state Hcur_privilege Hmstatus Hpmpcfg_n Hclk Hpc Ha5c Hview
  ihave Hm := mConf_introW cpu (DFrac.own 1)
      { stC56 c with pmpcfg := WeakLeafPmpcfg0.pmpcfgWritten 15#64 (stC56 c).pmpcfg }
    $$ Hcur_privilege Hhart_state Hmstatus Hmie Hmideleg Hmedeleg Hmepc Hsatp Hmenvcfg Hmcounteren
      Hmtimecmp Hstimecmp Hpmpcfg_n Hpmpaddr_n Hhw
  ihave Hrun := whartRunClose (GF := GF) cpu ξ 1 _ $$ Hm Hview
  ihave Hfile := Hfb $$ Ha5c
  rw [show ({ stC56 c with pmpcfg := WeakLeafPmpcfg0.pmpcfgWritten 15#64 (stC56 c).pmpcfg } :
      MConf) = stC58 c from rfl,
    show BitVec.addInt stPc58 4 = stPcAe0 by decide +kernel]
  -- ---- ae0. csrr a5, menvcfg  (the ADUE read-modify-write) ----
  ihave #HiAe0 := wstiAe0 (GF := GF) kbs hcov $$ Htext
  icases gprFile_acc cpu (stM57 m sp0 c) tiA5 (by decide +kernel) $$ Hfile with ⟨Ha5c, Hfins⟩
  iapply wwpCsrrMenvcfgRun gen cpu ξ stPcAe0 tiA5 (stM57 m sp0 c tiA5) (stC58 c) 1 hgid hmok1 hpmp1
    (by decide +kernel) $$ Hrun Hclk Hpc Ha5c HiAe0
  iintro Hrun Hclk Hpc Ha5c
  ihave Hfile := Hfins $$ %((stC58 c).menvcfg) Ha5c
  rw [show (stM57 m sp0 c).set tiA5 (stC58 c).menvcfg = stMAe0 m sp0 c from rfl,
    show BitVec.addInt stPcAe0 4 = stPcAe1 by decide +kernel]
  -- ---- ae1. c.li a4, 1 ----
  ihave #HiAe1 := wstiAe1 (GF := GF) kbs hcov $$ Htext
  iapply wwpAddiRun gen cpu ξ stPcAe1 true cliRs1 tiA4 (sign_extend (m := 12) saeLi) (stMAe0 m sp0 c)
    (stC58 c) 1 hgid hmok1 hpmp1 (by decide +kernel) $$ Hrun Hclk Hpc Hfile HiAe1
  iintro Hrun Hclk Hpc Hfile
  rw [hcli, BitVec.zero_add, hsae,
    show (stMAe0 m sp0 c).set tiA4 (WkTimerinit.cliWval saeLi) = stMAe1 m sp0 c from rfl,
    show BitVec.addInt stPcAe1 (if true then 2 else 4) = stPcAe2 by decide +kernel]
  -- ---- ae2. c.slli a4, 0x3d  (a4 := 1 << 61) ----
  have LAe2a4 : (stMAe1 m sp0 c).get tiA4 = WkTimerinit.cliWval saeLi := by wk_sn_look
  ihave #HiAe2 := wstiAe2 (GF := GF) kbs hcov $$ Htext
  iapply wwpSlliRvcRun gen cpu ξ stPcAe2 tiA4 tiA4 saeSlli (stMAe1 m sp0 c) (stC58 c) 1 hgid hmok1
    hpmp1 (by decide +kernel) $$ Hrun Hclk Hpc Hfile HiAe2
  iintro Hrun Hclk Hpc Hfile
  rw [LAe2a4, hb61, show (stMAe1 m sp0 c).set tiA4 stAdueBit = stMAe2 m sp0 c from rfl,
    show BitVec.addInt stPcAe2 2 = stPcAe3 by decide +kernel]
  -- ---- ae3. c.or a5, a4 ----
  have LAe3a5 : (stMAe2 m sp0 c).get tiA5 = c.menvcfg := by wk_sn_look
  have LAe3a4 : (stMAe2 m sp0 c).get tiA4 = stAdueBit := by wk_sn_look
  ihave #HiAe3 := wstiAe3 (GF := GF) kbs hcov $$ Htext
  iapply wwpOrRvcRun gen cpu ξ stPcAe3 tiA4 tiA5 tiA5 (stMAe2 m sp0 c) (stC58 c) 1 hgid hmok1 hpmp1
    (by decide +kernel) $$ Hrun Hclk Hpc Hfile HiAe3
  iintro Hrun Hclk Hpc Hfile
  rw [LAe3a5, LAe3a4, show (stMAe2 m sp0 c).set tiA5 (c.menvcfg ||| stAdueBit) = stMAe3 m sp0 c
      from rfl,
    show BitVec.addInt stPcAe3 2 = stPcAe4 by decide +kernel]
  -- ---- ae4. csrw menvcfg, a5 ----
  have LAe4a5 : stMAe3 m sp0 c tiA5 = c.menvcfg ||| stAdueBit := by wk_sn_look
  ihave #HiAe4 := wstiAe4 (GF := GF) kbs hcov $$ Htext
  icases gprFile_lookup_acc cpu (stMAe3 m sp0 c) tiA5 (by decide +kernel) $$ Hfile with ⟨Ha5c, Hfb⟩
  rw [LAe4a5]
  iapply wwpCsrwMenvcfgRun gen cpu ξ stPcAe4 tiA5 (c.menvcfg ||| stAdueBit) (stC58 c) hgid hmok1
    hpmp1 (by decide +kernel) $$ Hrun Hclk Hpc Ha5c HiAe4
  iintro Hrun Hclk Hpc Ha5c
  ihave Hfile := Hfb $$ Ha5c
  rw [show ({ stC58 c with
      menvcfg := (WeakLeafCsrw2.menvcfgLegalized (stC58 c).menvcfg (c.menvcfg ||| stAdueBit)) } : MConf) = stCAe4 c from rfl,
    show BitVec.addInt stPcAe4 4 = stPc59 by decide +kernel]
  -- ---- 59. jal ra, timerinit ----
  ihave #Hi59 := wsti59 (GF := GF) kbs hcov $$ Htext
  icases gprFile_acc cpu (stMAe3 m sp0 c) tiRa (by decide +kernel) $$ Hfile with ⟨Hrac, Hfins⟩
  iapply wwpJalRun gen cpu ξ stPc59 tiRa sjimm59 (stMAe3 m sp0 c tiRa) (stCAe4 c) 1 hgid hmok1 hpmp1
    (by decide +kernel) hjal $$ Hrun Hclk Hpc Hrac Hi59
  iintro Hrun Hclk Hpc Hrac
  ihave Hfile := Hfins $$ %(BitVec.addInt stPc59 4) Hrac
  rw [hlinkv, show (stMAe3 m sp0 c).set tiRa stRaLink = stM59 m sp0 c from rfl, hp59]
  -- ---- timerinit() (21 instructions), at the FULL fraction (deviation 3) ----
  have L59sp : stM59 m sp0 c WkTimerinitAux.cspRs1 = WkTimerinit.tiSp1 sp0 := by
    rw [hcspT]; wk_sn_look
  have L59ra : stM59 m sp0 c WkTimerinitAux.tiRa = stRaLink := by
    rw [show WkTimerinitAux.tiRa = tiRa by decide +kernel]; wk_sn_look
  have L59s0 : stM59 m sp0 c WkTimerinitAux.tiS0 = sp0 := by
    rw [show WkTimerinitAux.tiS0 = tiS0 by decide +kernel]; wk_sn_look
  iapply wwpTimerinit gen cpu ξ (stCAe4 c) (stM59 m sp0 c) (WkTimerinit.tiSp1 sp0) stRaLink sp0 2 kbs
    (Nat.le_refl 2) hgid hmok1 hpmp1 htorRa htorS0 hcov L59sp L59ra L59s0 hramTiRa hramTiS0
    $$ Hrun Hclk Hpc Hfile Hti2 Htext
  iintro %tv Hrun Hclk Hpc Hfile Hti2
  rw [hcretv, show WkTimerinit.tiMout (stM59 m sp0 c) (WkTimerinit.tiSp1 sp0) (stCAe4 c).menvcfg
      (stCAe4 c).mcounteren tv stRaLink sp0 = stMti m sp0 c tv from rfl]
  -- ---- 60. csrr a5, mhartid ----
  ihave #Hi60 := wsti60 (GF := GF) kbs hcov $$ Htext
  icases gprFile_acc cpu (stMti m sp0 c tv) tiA5 (by decide +kernel) $$ Hfile with ⟨Ha5c, Hfins⟩
  iapply wwpCsrrMhartidRun gen cpu ξ stPc60 tiA5 mhartidIn (stMti m sp0 c tv tiA5)
    (WkTimerinit.tiConfOut (stCAe4 c) tv) 1 hgid hmok1 hpmp1 (by decide +kernel)
    $$ Hrun Hclk Hpc Hmh Ha5c Hi60
  iintro Hrun Hclk Hpc Ha5c Hmh
  ihave Hfile := Hfins $$ %mhartidIn Ha5c
  rw [show (stMti m sp0 c tv).set tiA5 mhartidIn = stM60 m sp0 c tv mhartidIn from rfl,
    show BitVec.addInt stPc60 4 = stPc61 by decide +kernel]
  -- ---- 61. c.addiw a5, 0  (sext.w) ----
  have L61a5 : (stM60 m sp0 c tv mhartidIn).get tiA5 = mhartidIn := by wk_sn_look
  ihave #Hi61 := wsti61 (GF := GF) kbs hcov $$ Htext
  iapply wwpAddiwRvcRun gen cpu ξ stPc61 tiA5 tiA5 (sign_extend (m := 12) si61)
    (stM60 m sp0 c tv mhartidIn) (WkTimerinit.tiConfOut (stCAe4 c) tv) 1 hgid hmok1 hpmp1
    (by decide +kernel) $$ Hrun Hclk Hpc Hfile Hi61
  iintro Hrun Hclk Hpc Hfile
  rw [L61a5, hs61, show (stM60 m sp0 c tv mhartidIn).set tiA5 (sign_extend (m := 64)
      (Sail.BitVec.extractLsb (mhartidIn + sign_extend (m := 64) si61) 31 0)) =
      stM61 m sp0 c tv mhartidIn from rfl,
    show BitVec.addInt stPc61 2 = stPc62 by decide +kernel]
  -- ---- 62. c.mv tp, a5 ----
  have L62a5 : (stM61 m sp0 c tv mhartidIn).get tiA5 = stTpv mhartidIn := by wk_sn_look
  ihave #Hi62 := wsti62 (GF := GF) kbs hcov $$ Htext
  iapply wwpAddRvcRun gen cpu ξ stPc62 tiA5 cliRs1 stTp (stM61 m sp0 c tv mhartidIn)
    (WkTimerinit.tiConfOut (stCAe4 c) tv) 1 hgid hmok1 hpmp1 (by decide +kernel)
    $$ Hrun Hclk Hpc Hfile Hi62
  iintro Hrun Hclk Hpc Hfile
  rw [hcli, BitVec.zero_add, L62a5, show (stM61 m sp0 c tv mhartidIn).set stTp (stTpv mhartidIn) =
      stMout m sp0 c tv mhartidIn from rfl,
    show BitVec.addInt stPc62 2 = stPc63 by decide +kernel]
  -- ---- 63. MRET into Supervisor mode at <main>: dissolves the M-mode bundle ----
  ihave #Hi63 := wsti63 (GF := GF) kbs hcov $$ Htext
  icases whartRunOpen (GF := GF) cpu ξ 1 (WkTimerinit.tiConfOut (stCAe4 c) tv) $$ Hrun
    with ⟨Hm, Hview⟩
  mconf_cases Hm
  have hnp : privLevel_bits_forwards (_get_Mstatus_MPP (WeakLeafMret.cms2
      (WkTimerinit.tiConfOut (stCAe4 c) tv).mstatus), 0#1) = pure .Supervisor :=
    WkStartNew.mretPriv c.mstatus
  have hlpeF : _get_MEnvcfg_LPE (WkTimerinit.tiConfOut (stCAe4 c) tv).menvcfg = 0#1 :=
    WkStartNew.lpeFinal c.menvcfg hlpe
  have hret : WeakLeafMret.retPc (WkTimerinit.tiConfOut (stCAe4 c) tv).mepc = stMain := by
    show WeakLeafMret.retPc stMain = stMain
    decide +kernel
  iapply wwpMretO gen cpu ξ stPc63 .Supervisor (WkTimerinit.tiConfOut (stCAe4 c) tv).mstatus
    (WkTimerinit.tiConfOut (stCAe4 c) tv).mepc (WkTimerinit.tiConfOut (stCAe4 c) tv).menvcfg
    (WkTimerinit.tiConfOut (stCAe4 c) tv).pmpcfg hgid hpmp1 hb1.1 hb1.2 hnp rfl hlpeF
    $$ Hhw Hclk Hhart_state Hcur_privilege Hmstatus Hpmpcfg_n Hpc Hmenvcfg Hmepc Hi63 Hview
  iintro Hhart_state Hclk Hcur_privilege Hmstatus Hpmpcfg_n Hmenvcfg Hmepc Hpc Hview
  rw [hret]
  -- name the final M-mode config, so the Supervisor cells are its projections (a structure
  -- literal over the unfolded `tiConfOut` sends the unifier into the CSR legalizers)
  generalize hT : WkTimerinit.tiConfOut (stCAe4 c) tv = cT
  ihave Hs := confCells_introW cpu (DFrac.own 1) .Supervisor
      { cT with mstatus := WeakLeafMret.cms5 cT.mstatus }
    $$ Hcur_privilege Hhart_state Hmstatus Hmie Hmideleg Hmedeleg Hmepc Hsatp Hmenvcfg Hmcounteren
      Hmtimecmp Hstimecmp Hpmpcfg_n Hpmpaddr_n Hhw
  subst hT
  rw [show ({ WkTimerinit.tiConfOut (stCAe4 c) tv with
      mstatus := WeakLeafMret.cms5 (WkTimerinit.tiConfOut (stCAe4 c) tv).mstatus } : MConf) =
    stConfOut c tv from rfl]
  -- ---- re-bundle the frame and hand everything to the caller ----
  ihave Hti2 := hstkFrom $$ Hti2
  ihave Hdeep := (cobjSep ξ _ _).2 $$ [Hti2 Hdeep]
  · isplitl [Hti2]
    · iexact Hti2
    · iexact Hdeep
  ihave Hdeep := cobjMono ξ _ _ (wstackOwnPhys_split_2 cpu (paStk sp0 2) 2 (n - 2) (by omega))
    $$ Hdeep
  ihave Hstk := WkTimerinit.stackRebuild ξ cpu sp0 n (by omega) ra0 s00 $$ Hsra Hss0 Hdeep
  iapply Hcont $$ %tv Hs Hclk Hpc Hfile Hmh Hview Hstk

end start

end Weak
