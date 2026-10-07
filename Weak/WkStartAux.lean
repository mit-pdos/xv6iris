/-
Weak: **the per-instruction scaffolding of the weak `start()` chain** (M4) -- the 39 encoding
words, their kernel-image byte windows, the decode facts at the reference state, the RVC
expansions, the small register-map drivers, and the 39 `winstrM` tokens.

Rocq: `iris/WkStartAux.v` @ xxvzwolszwmp.

The Rocq header, in substance.  Split out of `WkStartNew` (which holds only the theorem) for the
reason `WkEntryEff`/`WkEntryNew` were split: the decode layer is STABLE and expensive, the proof
script above it is iterated.  Nothing here is weak-memory-specific; it is the `CodeStartAux`
vocabulary re-derived in the `winstrM`/`goodb0` shapes the weak leaves consume.  A caller spends
ONE `wstiNN kbs hcov` per instruction and never mentions a decode fact again.

**Deviations from Rocq.**
1. VOCABULARY: as `Weak/WkEntryEff.lean` deviation 1 and `Weak/WeakLeafM.lean` deviation 1
   (`mword n` ↦ `BitVec n`, `mword_of_int k` ↦ `k#n`, `sign_extend' n x` ↦ `sign_extend (m := n) x`,
   `zero_extend' n x` ↦ `zero_extend (m := n) x`, `concat_vec a b` ↦ `a +++ b`, `'b"000"` ↦
   `0b000#3`, `tt` ↦ `()`, `nth_byte w j` ↦ `nthByte (n := 4) w j`, `D_m`/`D_none`/`dstateM` ↦
   `WkEntryEff.dM`/`dNone`/`WkEntryEff.dstateM`, `wkb_covers` ↦ `wkbCovers`, `wkernel_text` ↦
   `wkernelText`, `winstr_m` ↦ `winstrM`).  The CSR operands are the literals the `WeakLeafM`
   wrappers consume (`WpGprCsrrA.csr_mstatus` ↦ `0x300#12`, `WpGprCsrwB.csr_satp` ↦ `0x180#12`,
   `ExecCommon.csr_csrr` ↦ `0xF14#12`, …).
2. THE KERNEL IMAGE (xv6 b72cbac1, `Weak/KernelSitesDef.lean`): `start` is the Lean
   `KernelSyms.«start»` (`0x80000058`); the image bytes are `WkEntryEff.kernelBytes` (Rocq
   `KernelInstrs.kernel_bytes`, `WkEntryEff` deviation 3).  All 39 offsets are Rocq's; 38 of the 39
   words are Rocq's; DRIFT at `start+0x24`: the word is `0xE5678793` (`addi a5,a5,-426`; Rocq
   `0xE0678793`, `-506`, because the Lean image's `main` is at `start+0xe76`, Rocq's at
   `start+0xe26`), so `stw43` and the Lean-only operand `WkStartAux.si43` (`3670`; Rocq `si43 =
   3590`) are the Lean image's, and `wsti43`'s statement carries that immediate.
3. THE SC VOCABULARY (`CodeStartAux`, `CodeTimerinitAux`, `WpMmodeLeafBase`: no Lean twin,
   `notes/weak-port-map.md` "MISSING by design") is restated as Lean-only definitions,
   file-qualified (`WkStartAux.stPc30` … for `st_pcNN`, `WkStartAux.si35`, `i9`, `u10`, `tiRa`, …).
   The register numbers are literals (`WkStartAux.cspRs1 = 2#5`, Rocq `zero_extend' 5 'b"10"`;
   `WkStartAux.cliRs1 = 0#5`); `caddi4spn_imm` is `ExecSC.caddi4spnImm`.
4. THE DECODE FACTS: Rocq's `wdec_all` arguments are the generated catalogue `KernelDecode*.kd_*`
   (no Lean twin); here they are `WkEntryNew.decBase`/`decRvc` fed by two read-only walks per
   instruction (`WkStartAux.walkNNM` on `MachCSL.drefM`, `WkStartAux.walkNNS` on
   `WkEntryNew.drefS0`), each closed by `kernel_rfl` (`WkEntryNew` deviation 5).  The decodes at
   `dstateM` (`stdecNN`) are DERIVED from the machine-mode walk (`WkStartAux.decRef`) instead of a
   third evaluation; the `goodb0`/`is_lpad` facts are `decide +kernel`, the RVC `goodb0`
   expansions `rfl`, the expansions `stexpNN` `kernel_rfl` (Rocq: the model's
   `exec_execute_C_*` plus a `bv_eq` loop).  `decode_pair_of_bool` (Rocq's workaround for a
   universe artifact of `vm_compute`) has no use in Lean and is dropped.
5. THE TOKENS: Rocq's per-token `winstr_m_of_text` script is factored through the Lean-only
   `WkStartAux.tokBase`/`tokRvc` (the same seven premises, the window via `wkbWindow`); each
   `wstiNN` is one application.  Statement shape: Rocq `wkb_covers kbs -> wkernel_text kbs -∗
   winstr_m pc rvc i` ↦ `wkbCovers kbs → wkernelText kbs ⊢ winstrM pc rvc i`.  `stexp_35` does
   not exist in Rocq (it inlines `exec_execute_C_LUI`); Lean has the file-qualified
   `WkStartAux.stexp35`.
6. REGISTER-MAP DRIVERS (§3): Rocq's `regfile` is a raw function with `<[k := v]>` updates;
   Lean's is `MachCSL.RegMap` with `RegMap.set` (`Weak/WkGprAcc.lean` deviation 1).
   `rf_upd2_same` is stated over `RegMap` in the order `gprFile_acc_2` returns
   (`(f.set k2 v2).set k1 v1 = f`).  The Ltacs `st_reg_neq` / `st_look` are the macros
   `wk_start_reg_neq` (`decide` on a `BitVec 5` disequality) / `wk_start_look` (`RegMap.set_same`
   / `RegMap.set_other` rewrites, side conditions by `decide`).  `st_unfold` unfolds the SC maps
   `st_m*`/`ti_m*` of `WpStartNew`/`WpTimerinit`, which have no Lean twin (the Lean `WkStartNew`
   defines its own maps), and is dropped; `st_ram4`/`st_ram8` are unused anywhere and dropped
   (`wk_entry_ram_win` covers the 4-byte case).

**Rocq → Lean name map.**  `stw_NN` `stwNN`, `sth_NN` `sthNN`, `stkb_NN` `stkbNN`,
`st_misaC_dstateM` `stMisaCDstateM`, `stdec_NN` `stdecNN`, `stgood_NN` `stgoodNN`, `stlpad_NN`
`stlpadNN`, `stgoodexp_NN` `stgoodexpNN`, `stexp_NN` `stexpNN`, `rf_upd2_same` `rfUpd2Same`,
`wsti_NN` `wstiNN` (`NN` ∈ 30…63; `ae0…ae4` ↦ `Ae0…Ae4`, e.g. `stw_ae0` `stwAe0`, `wsti_ae4`
`wstiAe4`), Ltacs `st_reg_neq` `wk_start_reg_neq`, `st_look` `wk_start_look`.  None is in the
duplicated-name table.  Lean-only (file-qualified `WkStartAux.*`): the SC stand-ins `stPcNN`,
`stPcAeK`, `i9`, `u10`, `u11`, `nz12`, `tiRa`, `tiS0`, `tiA4`, `tiA5`, `stTp`, `cspRs1`, `cliRs1`,
`si35`, `si36`, `si38`, `si39`, `si42`, `si43`, `si45`, `si47`, `si48`, `si52`, `si54`, `ssh55`,
`si57`, `saeLi`, `saeSlli`, `sjimm59`, `si61`; the helpers `cfgOkD`, `decRef`, `tokBase`, `tokRvc`,
`stexp35`, and the 78 walks `walkNNM`/`walkNNS`.

**Dropped:** `decode_pair_of_bool` (deviation 4), Ltacs `st_unfold`, `st_ram4`, `st_ram8`
(deviation 6).  Rocq: 39 + 19 definitions, 39 `stkb`, 1 `st_misaC_dstateM`, 39 `stdec`,
39 `stgood`, 19 `stlpad`, 19 `stgoodexp`, 18 `stexp`, `rf_upd2_same`, `decode_pair_of_bool`,
39 `wsti`, 6 Ltacs; Lean: all of them but the four dropped, plus the Lean-only declarations above.
-/
import Weak.WeakLeafM

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std
open MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D LeanRV64D.Functions

/-! ## 0a. The `CodeStartAux` / `CodeTimerinitAux` operand vocabulary (Lean-only, deviation 3) -/

namespace WkStartAux

/-- Rocq `CodeTimerinitAux.i9`: `c.addi` immediate `-16`. -/
def i9 : BitVec 6 := 48#6
/-- Rocq `CodeTimerinitAux.u10`: `c.sdsp` offset 8. -/
def u10 : BitVec 6 := 1#6
/-- Rocq `CodeTimerinitAux.u11`: `c.sdsp` offset 0. -/
def u11 : BitVec 6 := 0#6
/-- Rocq `CodeTimerinitAux.nz12`: `c.addi4spn` immediate (16/4). -/
def nz12 : BitVec 8 := 4#8
/-- Rocq `CodeTimerinitAux.ti_ra` (x1). -/
def tiRa : BitVec 5 := 1#5
/-- Rocq `CodeTimerinitAux.ti_s0` (x8). -/
def tiS0 : BitVec 5 := 8#5
/-- Rocq `CodeTimerinitAux.ti_a4` (x14). -/
def tiA4 : BitVec 5 := 14#5
/-- Rocq `CodeTimerinitAux.ti_a5` (x15). -/
def tiA5 : BitVec 5 := 15#5
/-- Rocq `CodeStartAux.st_tp` (x4). -/
def stTp : BitVec 5 := 4#5
/-- Rocq `WpMmodeLeafBase.csp_rs1` (x2, `sp`). -/
def cspRs1 : BitVec 5 := 2#5
/-- Rocq `WpMmodeLeafBase.cli_rs1` (x0). -/
def cliRs1 : BitVec 5 := 0#5
/-- Rocq `CodeStartAux.si35`: `c.lui a4` immediate (`-2`, i.e. `0xffffe`). -/
def si35 : BitVec 6 := 62#6
/-- Rocq `CodeStartAux.si36`: `addi a4, 2047`. -/
def si36 : BitVec 12 := 2047#12
/-- Rocq `CodeStartAux.si38`: `c.lui a4, 1`. -/
def si38 : BitVec 6 := 1#6
/-- Rocq `CodeStartAux.si39`: `addi a4, -2048`. -/
def si39 : BitVec 12 := 2048#12
/-- Rocq `CodeStartAux.si42`: `auipc a5, 1`. -/
def si42 : BitVec 20 := 1#20
/-- Rocq `CodeStartAux.si43`: `addi a5, -426` (DRIFT, deviation 2: Rocq `3590`, `-506`). -/
def si43 : BitVec 12 := 3670#12
/-- Rocq `CodeStartAux.si45`: `c.li a5, 0`. -/
def si45 : BitVec 6 := 0#6
/-- Rocq `CodeStartAux.si47`: `c.lui a5, 0x10`. -/
def si47 : BitVec 6 := 16#6
/-- Rocq `CodeStartAux.si48`: `c.addi a5, -1`. -/
def si48 : BitVec 6 := 63#6
/-- Rocq `CodeStartAux.si52`: `ori a5, 544`. -/
def si52 : BitVec 12 := 544#12
/-- Rocq `CodeStartAux.si54`: `c.li a5, -1`. -/
def si54 : BitVec 6 := 63#6
/-- Rocq `CodeStartAux.ssh55`: `c.srli a5, 10`. -/
def ssh55 : BitVec 6 := 10#6
/-- Rocq `CodeStartAux.si57`: `c.li a5, 15`. -/
def si57 : BitVec 6 := 15#6
/-- Rocq `CodeStartAux.sae_li`: `c.li a4, 1`. -/
def saeLi : BitVec 6 := 1#6
/-- Rocq `CodeStartAux.sae_slli`: `c.slli a4, 0x3d`. -/
def saeSlli : BitVec 6 := 61#6
/-- Rocq `CodeStartAux.sjimm59`: `jal` offset `-162` (to `timerinit`). -/
def sjimm59 : BitVec 21 := 0x1fff5e#21
/-- Rocq `CodeStartAux.si61`: `c.addiw a5, 0`. -/
def si61 : BitVec 6 := 0#6

end WkStartAux

open WkStartAux

/-! ## 0. Per-instruction encoding words (closed literals, the Lean kernel image's bytes) -/

/-- Rocq `stw_30`: c.addi sp,-16 (start + 0x0). -/
def stw30 : BitVec 32 := 0xE4061141#32
/-- Rocq `stw_31`: c.sdsp ra,8(sp) (start + 0x2). -/
def stw31 : BitVec 32 := 0xE022E406#32
/-- Rocq `stw_32`: c.sdsp s0,0(sp) (start + 0x4). -/
def stw32 : BitVec 32 := 0x0800E022#32
/-- Rocq `stw_33`: c.addi4spn s0,sp,16 (start + 0x6). -/
def stw33 : BitVec 32 := 0x27F30800#32
/-- Rocq `stw_34`: csrr a5,mstatus (start + 0x8). -/
def stw34 : BitVec 32 := 0x300027F3#32
/-- Rocq `stw_35`: c.lui a4,0xffffe (start + 0xc). -/
def stw35 : BitVec 32 := 0x07137779#32
/-- Rocq `stw_36`: addi a4,a4,2047 (start + 0xe). -/
def stw36 : BitVec 32 := 0x7FF70713#32
/-- Rocq `stw_37`: c.and a5,a4 (start + 0x12). -/
def stw37 : BitVec 32 := 0x67058FF9#32
/-- Rocq `stw_38`: c.lui a4,1 (start + 0x14). -/
def stw38 : BitVec 32 := 0x07136705#32
/-- Rocq `stw_39`: addi a4,a4,-2048 (start + 0x16). -/
def stw39 : BitVec 32 := 0x80070713#32
/-- Rocq `stw_40`: c.or a5,a4 (start + 0x1a). -/
def stw40 : BitVec 32 := 0x90738FD9#32
/-- Rocq `stw_41`: csrw mstatus,a5 (start + 0x1c). -/
def stw41 : BitVec 32 := 0x30079073#32
/-- Rocq `stw_42`: auipc a5,1 (start + 0x20). -/
def stw42 : BitVec 32 := 0x00001797#32
/-- Rocq `stw_43`: addi a5,a5,-426 (drift: Rocq -506) (start + 0x24). -/
def stw43 : BitVec 32 := 0xE5678793#32
/-- Rocq `stw_44`: csrw mepc,a5 (start + 0x28). -/
def stw44 : BitVec 32 := 0x34179073#32
/-- Rocq `stw_45`: c.li a5,0 (start + 0x2c). -/
def stw45 : BitVec 32 := 0x90734781#32
/-- Rocq `stw_46`: csrw satp,a5 (start + 0x2e). -/
def stw46 : BitVec 32 := 0x18079073#32
/-- Rocq `stw_47`: c.lui a5,0x10 (start + 0x32). -/
def stw47 : BitVec 32 := 0x17FD67C1#32
/-- Rocq `stw_48`: c.addi a5,-1 (start + 0x34). -/
def stw48 : BitVec 32 := 0x907317FD#32
/-- Rocq `stw_49`: csrw medeleg,a5 (start + 0x36). -/
def stw49 : BitVec 32 := 0x30279073#32
/-- Rocq `stw_50`: csrw mideleg,a5 (start + 0x3a). -/
def stw50 : BitVec 32 := 0x30379073#32
/-- Rocq `stw_51`: csrr a5,sie (start + 0x3e). -/
def stw51 : BitVec 32 := 0x104027F3#32
/-- Rocq `stw_52`: ori a5,a5,544 (start + 0x42). -/
def stw52 : BitVec 32 := 0x2207E793#32
/-- Rocq `stw_53`: csrw sie,a5 (start + 0x46). -/
def stw53 : BitVec 32 := 0x10479073#32
/-- Rocq `stw_54`: c.li a5,-1 (start + 0x4a). -/
def stw54 : BitVec 32 := 0x83A957FD#32
/-- Rocq `stw_55`: c.srli a5,10 (start + 0x4c). -/
def stw55 : BitVec 32 := 0x907383A9#32
/-- Rocq `stw_56`: csrw pmpaddr0,a5 (start + 0x4e). -/
def stw56 : BitVec 32 := 0x3B079073#32
/-- Rocq `stw_57`: c.li a5,15 (start + 0x52). -/
def stw57 : BitVec 32 := 0x907347BD#32
/-- Rocq `stw_58`: csrw pmpcfg0,a5 (start + 0x54). -/
def stw58 : BitVec 32 := 0x3A079073#32
/-- Rocq `stw_ae0`: csrr a5,menvcfg (start + 0x58). -/
def stwAe0 : BitVec 32 := 0x30A027F3#32
/-- Rocq `stw_ae1`: c.li a4,1 (start + 0x5c). -/
def stwAe1 : BitVec 32 := 0x17764705#32
/-- Rocq `stw_ae2`: c.slli a4,0x3d (start + 0x5e). -/
def stwAe2 : BitVec 32 := 0x8FD91776#32
/-- Rocq `stw_ae3`: c.or a5,a4 (start + 0x60). -/
def stwAe3 : BitVec 32 := 0x90738FD9#32
/-- Rocq `stw_ae4`: csrw menvcfg,a5 (start + 0x62). -/
def stwAe4 : BitVec 32 := 0x30A79073#32
/-- Rocq `stw_59`: jal ra,timerinit (start + 0x66). -/
def stw59 : BitVec 32 := 0xF5FFF0EF#32
/-- Rocq `stw_60`: csrr a5,mhartid (start + 0x6a). -/
def stw60 : BitVec 32 := 0xF14027F3#32
/-- Rocq `stw_61`: c.addiw a5,0 (sext.w) (start + 0x6e). -/
def stw61 : BitVec 32 := 0x823E2781#32
/-- Rocq `stw_62`: c.mv tp,a5 (start + 0x70). -/
def stw62 : BitVec 32 := 0x0073823E#32
/-- Rocq `stw_63`: mret (start + 0x72). -/
def stw63 : BitVec 32 := 0x30200073#32

/-- Rocq `sth_30`. -/
def sth30 : BitVec 16 := 0x1141#16
/-- Rocq `sth_31`. -/
def sth31 : BitVec 16 := 0xE406#16
/-- Rocq `sth_32`. -/
def sth32 : BitVec 16 := 0xE022#16
/-- Rocq `sth_33`. -/
def sth33 : BitVec 16 := 0x0800#16
/-- Rocq `sth_35`. -/
def sth35 : BitVec 16 := 0x7779#16
/-- Rocq `sth_37`. -/
def sth37 : BitVec 16 := 0x8FF9#16
/-- Rocq `sth_38`. -/
def sth38 : BitVec 16 := 0x6705#16
/-- Rocq `sth_40`. -/
def sth40 : BitVec 16 := 0x8FD9#16
/-- Rocq `sth_45`. -/
def sth45 : BitVec 16 := 0x4781#16
/-- Rocq `sth_47`. -/
def sth47 : BitVec 16 := 0x67C1#16
/-- Rocq `sth_48`. -/
def sth48 : BitVec 16 := 0x17FD#16
/-- Rocq `sth_54`. -/
def sth54 : BitVec 16 := 0x57FD#16
/-- Rocq `sth_55`. -/
def sth55 : BitVec 16 := 0x83A9#16
/-- Rocq `sth_57`. -/
def sth57 : BitVec 16 := 0x47BD#16
/-- Rocq `sth_ae1`. -/
def sthAe1 : BitVec 16 := 0x4705#16
/-- Rocq `sth_ae2`. -/
def sthAe2 : BitVec 16 := 0x1776#16
/-- Rocq `sth_ae3`. -/
def sthAe3 : BitVec 16 := 0x8FD9#16
/-- Rocq `sth_61`. -/
def sth61 : BitVec 16 := 0x2781#16
/-- Rocq `sth_62`. -/
def sth62 : BitVec 16 := 0x823E#16

namespace WkStartAux

/-! ### 0b. The instruction addresses (Rocq `CodeStartAux.st_pcNN`; Lean-only stand-ins) -/

/-- Rocq `st_pc30`. -/
def stPc30 : BitVec 64 := BitVec.ofInt 64 ((KernelSyms.«start» : Int) + 0x0)
/-- Rocq `st_pc31`. -/
def stPc31 : BitVec 64 := BitVec.ofInt 64 ((KernelSyms.«start» : Int) + 0x2)
/-- Rocq `st_pc32`. -/
def stPc32 : BitVec 64 := BitVec.ofInt 64 ((KernelSyms.«start» : Int) + 0x4)
/-- Rocq `st_pc33`. -/
def stPc33 : BitVec 64 := BitVec.ofInt 64 ((KernelSyms.«start» : Int) + 0x6)
/-- Rocq `st_pc34`. -/
def stPc34 : BitVec 64 := BitVec.ofInt 64 ((KernelSyms.«start» : Int) + 0x8)
/-- Rocq `st_pc35`. -/
def stPc35 : BitVec 64 := BitVec.ofInt 64 ((KernelSyms.«start» : Int) + 0xc)
/-- Rocq `st_pc36`. -/
def stPc36 : BitVec 64 := BitVec.ofInt 64 ((KernelSyms.«start» : Int) + 0xe)
/-- Rocq `st_pc37`. -/
def stPc37 : BitVec 64 := BitVec.ofInt 64 ((KernelSyms.«start» : Int) + 0x12)
/-- Rocq `st_pc38`. -/
def stPc38 : BitVec 64 := BitVec.ofInt 64 ((KernelSyms.«start» : Int) + 0x14)
/-- Rocq `st_pc39`. -/
def stPc39 : BitVec 64 := BitVec.ofInt 64 ((KernelSyms.«start» : Int) + 0x16)
/-- Rocq `st_pc40`. -/
def stPc40 : BitVec 64 := BitVec.ofInt 64 ((KernelSyms.«start» : Int) + 0x1a)
/-- Rocq `st_pc41`. -/
def stPc41 : BitVec 64 := BitVec.ofInt 64 ((KernelSyms.«start» : Int) + 0x1c)
/-- Rocq `st_pc42`. -/
def stPc42 : BitVec 64 := BitVec.ofInt 64 ((KernelSyms.«start» : Int) + 0x20)
/-- Rocq `st_pc43`. -/
def stPc43 : BitVec 64 := BitVec.ofInt 64 ((KernelSyms.«start» : Int) + 0x24)
/-- Rocq `st_pc44`. -/
def stPc44 : BitVec 64 := BitVec.ofInt 64 ((KernelSyms.«start» : Int) + 0x28)
/-- Rocq `st_pc45`. -/
def stPc45 : BitVec 64 := BitVec.ofInt 64 ((KernelSyms.«start» : Int) + 0x2c)
/-- Rocq `st_pc46`. -/
def stPc46 : BitVec 64 := BitVec.ofInt 64 ((KernelSyms.«start» : Int) + 0x2e)
/-- Rocq `st_pc47`. -/
def stPc47 : BitVec 64 := BitVec.ofInt 64 ((KernelSyms.«start» : Int) + 0x32)
/-- Rocq `st_pc48`. -/
def stPc48 : BitVec 64 := BitVec.ofInt 64 ((KernelSyms.«start» : Int) + 0x34)
/-- Rocq `st_pc49`. -/
def stPc49 : BitVec 64 := BitVec.ofInt 64 ((KernelSyms.«start» : Int) + 0x36)
/-- Rocq `st_pc50`. -/
def stPc50 : BitVec 64 := BitVec.ofInt 64 ((KernelSyms.«start» : Int) + 0x3a)
/-- Rocq `st_pc51`. -/
def stPc51 : BitVec 64 := BitVec.ofInt 64 ((KernelSyms.«start» : Int) + 0x3e)
/-- Rocq `st_pc52`. -/
def stPc52 : BitVec 64 := BitVec.ofInt 64 ((KernelSyms.«start» : Int) + 0x42)
/-- Rocq `st_pc53`. -/
def stPc53 : BitVec 64 := BitVec.ofInt 64 ((KernelSyms.«start» : Int) + 0x46)
/-- Rocq `st_pc54`. -/
def stPc54 : BitVec 64 := BitVec.ofInt 64 ((KernelSyms.«start» : Int) + 0x4a)
/-- Rocq `st_pc55`. -/
def stPc55 : BitVec 64 := BitVec.ofInt 64 ((KernelSyms.«start» : Int) + 0x4c)
/-- Rocq `st_pc56`. -/
def stPc56 : BitVec 64 := BitVec.ofInt 64 ((KernelSyms.«start» : Int) + 0x4e)
/-- Rocq `st_pc57`. -/
def stPc57 : BitVec 64 := BitVec.ofInt 64 ((KernelSyms.«start» : Int) + 0x52)
/-- Rocq `st_pc58`. -/
def stPc58 : BitVec 64 := BitVec.ofInt 64 ((KernelSyms.«start» : Int) + 0x54)
/-- Rocq `st_pc_ae0`. -/
def stPcAe0 : BitVec 64 := BitVec.ofInt 64 ((KernelSyms.«start» : Int) + 0x58)
/-- Rocq `st_pc_ae1`. -/
def stPcAe1 : BitVec 64 := BitVec.ofInt 64 ((KernelSyms.«start» : Int) + 0x5c)
/-- Rocq `st_pc_ae2`. -/
def stPcAe2 : BitVec 64 := BitVec.ofInt 64 ((KernelSyms.«start» : Int) + 0x5e)
/-- Rocq `st_pc_ae3`. -/
def stPcAe3 : BitVec 64 := BitVec.ofInt 64 ((KernelSyms.«start» : Int) + 0x60)
/-- Rocq `st_pc_ae4`. -/
def stPcAe4 : BitVec 64 := BitVec.ofInt 64 ((KernelSyms.«start» : Int) + 0x62)
/-- Rocq `st_pc59`. -/
def stPc59 : BitVec 64 := BitVec.ofInt 64 ((KernelSyms.«start» : Int) + 0x66)
/-- Rocq `st_pc60`. -/
def stPc60 : BitVec 64 := BitVec.ofInt 64 ((KernelSyms.«start» : Int) + 0x6a)
/-- Rocq `st_pc61`. -/
def stPc61 : BitVec 64 := BitVec.ofInt 64 ((KernelSyms.«start» : Int) + 0x6e)
/-- Rocq `st_pc62`. -/
def stPc62 : BitVec 64 := BitVec.ofInt 64 ((KernelSyms.«start» : Int) + 0x70)
/-- Rocq `st_pc63`. -/
def stPc63 : BitVec 64 := BitVec.ofInt 64 ((KernelSyms.«start» : Int) + 0x72)

end WkStartAux

open WkStartAux

/-! ## 1. Kernel-image byte-window facts (reuses `wk_entry_kb_win`) -/

/-- Rocq `stkb_30`. -/
theorem stkb30 : ∀ j : Nat, j < 4 →
    WkEntryEff.kernelBytes ((KernelSyms.«start» : Int) + 0x0 + (j : Int)) =
      some (nthByte (n := 4) stw30 j) := by
  wk_entry_kb_win
/-- Rocq `stkb_31`. -/
theorem stkb31 : ∀ j : Nat, j < 4 →
    WkEntryEff.kernelBytes ((KernelSyms.«start» : Int) + 0x2 + (j : Int)) =
      some (nthByte (n := 4) stw31 j) := by
  wk_entry_kb_win
/-- Rocq `stkb_32`. -/
theorem stkb32 : ∀ j : Nat, j < 4 →
    WkEntryEff.kernelBytes ((KernelSyms.«start» : Int) + 0x4 + (j : Int)) =
      some (nthByte (n := 4) stw32 j) := by
  wk_entry_kb_win
/-- Rocq `stkb_33`. -/
theorem stkb33 : ∀ j : Nat, j < 4 →
    WkEntryEff.kernelBytes ((KernelSyms.«start» : Int) + 0x6 + (j : Int)) =
      some (nthByte (n := 4) stw33 j) := by
  wk_entry_kb_win
/-- Rocq `stkb_34`. -/
theorem stkb34 : ∀ j : Nat, j < 4 →
    WkEntryEff.kernelBytes ((KernelSyms.«start» : Int) + 0x8 + (j : Int)) =
      some (nthByte (n := 4) stw34 j) := by
  wk_entry_kb_win
/-- Rocq `stkb_35`. -/
theorem stkb35 : ∀ j : Nat, j < 4 →
    WkEntryEff.kernelBytes ((KernelSyms.«start» : Int) + 0xc + (j : Int)) =
      some (nthByte (n := 4) stw35 j) := by
  wk_entry_kb_win
/-- Rocq `stkb_36`. -/
theorem stkb36 : ∀ j : Nat, j < 4 →
    WkEntryEff.kernelBytes ((KernelSyms.«start» : Int) + 0xe + (j : Int)) =
      some (nthByte (n := 4) stw36 j) := by
  wk_entry_kb_win
/-- Rocq `stkb_37`. -/
theorem stkb37 : ∀ j : Nat, j < 4 →
    WkEntryEff.kernelBytes ((KernelSyms.«start» : Int) + 0x12 + (j : Int)) =
      some (nthByte (n := 4) stw37 j) := by
  wk_entry_kb_win
/-- Rocq `stkb_38`. -/
theorem stkb38 : ∀ j : Nat, j < 4 →
    WkEntryEff.kernelBytes ((KernelSyms.«start» : Int) + 0x14 + (j : Int)) =
      some (nthByte (n := 4) stw38 j) := by
  wk_entry_kb_win
/-- Rocq `stkb_39`. -/
theorem stkb39 : ∀ j : Nat, j < 4 →
    WkEntryEff.kernelBytes ((KernelSyms.«start» : Int) + 0x16 + (j : Int)) =
      some (nthByte (n := 4) stw39 j) := by
  wk_entry_kb_win
/-- Rocq `stkb_40`. -/
theorem stkb40 : ∀ j : Nat, j < 4 →
    WkEntryEff.kernelBytes ((KernelSyms.«start» : Int) + 0x1a + (j : Int)) =
      some (nthByte (n := 4) stw40 j) := by
  wk_entry_kb_win
/-- Rocq `stkb_41`. -/
theorem stkb41 : ∀ j : Nat, j < 4 →
    WkEntryEff.kernelBytes ((KernelSyms.«start» : Int) + 0x1c + (j : Int)) =
      some (nthByte (n := 4) stw41 j) := by
  wk_entry_kb_win
/-- Rocq `stkb_42`. -/
theorem stkb42 : ∀ j : Nat, j < 4 →
    WkEntryEff.kernelBytes ((KernelSyms.«start» : Int) + 0x20 + (j : Int)) =
      some (nthByte (n := 4) stw42 j) := by
  wk_entry_kb_win
/-- Rocq `stkb_43`. -/
theorem stkb43 : ∀ j : Nat, j < 4 →
    WkEntryEff.kernelBytes ((KernelSyms.«start» : Int) + 0x24 + (j : Int)) =
      some (nthByte (n := 4) stw43 j) := by
  wk_entry_kb_win
/-- Rocq `stkb_44`. -/
theorem stkb44 : ∀ j : Nat, j < 4 →
    WkEntryEff.kernelBytes ((KernelSyms.«start» : Int) + 0x28 + (j : Int)) =
      some (nthByte (n := 4) stw44 j) := by
  wk_entry_kb_win
/-- Rocq `stkb_45`. -/
theorem stkb45 : ∀ j : Nat, j < 4 →
    WkEntryEff.kernelBytes ((KernelSyms.«start» : Int) + 0x2c + (j : Int)) =
      some (nthByte (n := 4) stw45 j) := by
  wk_entry_kb_win
/-- Rocq `stkb_46`. -/
theorem stkb46 : ∀ j : Nat, j < 4 →
    WkEntryEff.kernelBytes ((KernelSyms.«start» : Int) + 0x2e + (j : Int)) =
      some (nthByte (n := 4) stw46 j) := by
  wk_entry_kb_win
/-- Rocq `stkb_47`. -/
theorem stkb47 : ∀ j : Nat, j < 4 →
    WkEntryEff.kernelBytes ((KernelSyms.«start» : Int) + 0x32 + (j : Int)) =
      some (nthByte (n := 4) stw47 j) := by
  wk_entry_kb_win
/-- Rocq `stkb_48`. -/
theorem stkb48 : ∀ j : Nat, j < 4 →
    WkEntryEff.kernelBytes ((KernelSyms.«start» : Int) + 0x34 + (j : Int)) =
      some (nthByte (n := 4) stw48 j) := by
  wk_entry_kb_win
/-- Rocq `stkb_49`. -/
theorem stkb49 : ∀ j : Nat, j < 4 →
    WkEntryEff.kernelBytes ((KernelSyms.«start» : Int) + 0x36 + (j : Int)) =
      some (nthByte (n := 4) stw49 j) := by
  wk_entry_kb_win
/-- Rocq `stkb_50`. -/
theorem stkb50 : ∀ j : Nat, j < 4 →
    WkEntryEff.kernelBytes ((KernelSyms.«start» : Int) + 0x3a + (j : Int)) =
      some (nthByte (n := 4) stw50 j) := by
  wk_entry_kb_win
/-- Rocq `stkb_51`. -/
theorem stkb51 : ∀ j : Nat, j < 4 →
    WkEntryEff.kernelBytes ((KernelSyms.«start» : Int) + 0x3e + (j : Int)) =
      some (nthByte (n := 4) stw51 j) := by
  wk_entry_kb_win
/-- Rocq `stkb_52`. -/
theorem stkb52 : ∀ j : Nat, j < 4 →
    WkEntryEff.kernelBytes ((KernelSyms.«start» : Int) + 0x42 + (j : Int)) =
      some (nthByte (n := 4) stw52 j) := by
  wk_entry_kb_win
/-- Rocq `stkb_53`. -/
theorem stkb53 : ∀ j : Nat, j < 4 →
    WkEntryEff.kernelBytes ((KernelSyms.«start» : Int) + 0x46 + (j : Int)) =
      some (nthByte (n := 4) stw53 j) := by
  wk_entry_kb_win
/-- Rocq `stkb_54`. -/
theorem stkb54 : ∀ j : Nat, j < 4 →
    WkEntryEff.kernelBytes ((KernelSyms.«start» : Int) + 0x4a + (j : Int)) =
      some (nthByte (n := 4) stw54 j) := by
  wk_entry_kb_win
/-- Rocq `stkb_55`. -/
theorem stkb55 : ∀ j : Nat, j < 4 →
    WkEntryEff.kernelBytes ((KernelSyms.«start» : Int) + 0x4c + (j : Int)) =
      some (nthByte (n := 4) stw55 j) := by
  wk_entry_kb_win
/-- Rocq `stkb_56`. -/
theorem stkb56 : ∀ j : Nat, j < 4 →
    WkEntryEff.kernelBytes ((KernelSyms.«start» : Int) + 0x4e + (j : Int)) =
      some (nthByte (n := 4) stw56 j) := by
  wk_entry_kb_win
/-- Rocq `stkb_57`. -/
theorem stkb57 : ∀ j : Nat, j < 4 →
    WkEntryEff.kernelBytes ((KernelSyms.«start» : Int) + 0x52 + (j : Int)) =
      some (nthByte (n := 4) stw57 j) := by
  wk_entry_kb_win
/-- Rocq `stkb_58`. -/
theorem stkb58 : ∀ j : Nat, j < 4 →
    WkEntryEff.kernelBytes ((KernelSyms.«start» : Int) + 0x54 + (j : Int)) =
      some (nthByte (n := 4) stw58 j) := by
  wk_entry_kb_win
/-- Rocq `stkb_ae0`. -/
theorem stkbAe0 : ∀ j : Nat, j < 4 →
    WkEntryEff.kernelBytes ((KernelSyms.«start» : Int) + 0x58 + (j : Int)) =
      some (nthByte (n := 4) stwAe0 j) := by
  wk_entry_kb_win
/-- Rocq `stkb_ae1`. -/
theorem stkbAe1 : ∀ j : Nat, j < 4 →
    WkEntryEff.kernelBytes ((KernelSyms.«start» : Int) + 0x5c + (j : Int)) =
      some (nthByte (n := 4) stwAe1 j) := by
  wk_entry_kb_win
/-- Rocq `stkb_ae2`. -/
theorem stkbAe2 : ∀ j : Nat, j < 4 →
    WkEntryEff.kernelBytes ((KernelSyms.«start» : Int) + 0x5e + (j : Int)) =
      some (nthByte (n := 4) stwAe2 j) := by
  wk_entry_kb_win
/-- Rocq `stkb_ae3`. -/
theorem stkbAe3 : ∀ j : Nat, j < 4 →
    WkEntryEff.kernelBytes ((KernelSyms.«start» : Int) + 0x60 + (j : Int)) =
      some (nthByte (n := 4) stwAe3 j) := by
  wk_entry_kb_win
/-- Rocq `stkb_ae4`. -/
theorem stkbAe4 : ∀ j : Nat, j < 4 →
    WkEntryEff.kernelBytes ((KernelSyms.«start» : Int) + 0x62 + (j : Int)) =
      some (nthByte (n := 4) stwAe4 j) := by
  wk_entry_kb_win
/-- Rocq `stkb_59`. -/
theorem stkb59 : ∀ j : Nat, j < 4 →
    WkEntryEff.kernelBytes ((KernelSyms.«start» : Int) + 0x66 + (j : Int)) =
      some (nthByte (n := 4) stw59 j) := by
  wk_entry_kb_win
/-- Rocq `stkb_60`. -/
theorem stkb60 : ∀ j : Nat, j < 4 →
    WkEntryEff.kernelBytes ((KernelSyms.«start» : Int) + 0x6a + (j : Int)) =
      some (nthByte (n := 4) stw60 j) := by
  wk_entry_kb_win
/-- Rocq `stkb_61`. -/
theorem stkb61 : ∀ j : Nat, j < 4 →
    WkEntryEff.kernelBytes ((KernelSyms.«start» : Int) + 0x6e + (j : Int)) =
      some (nthByte (n := 4) stw61 j) := by
  wk_entry_kb_win
/-- Rocq `stkb_62`. -/
theorem stkb62 : ∀ j : Nat, j < 4 →
    WkEntryEff.kernelBytes ((KernelSyms.«start» : Int) + 0x70 + (j : Int)) =
      some (nthByte (n := 4) stw62 j) := by
  wk_entry_kb_win
/-- Rocq `stkb_63`. -/
theorem stkb63 : ∀ j : Nat, j < 4 →
    WkEntryEff.kernelBytes ((KernelSyms.«start» : Int) + 0x72 + (j : Int)) =
      some (nthByte (n := 4) stw63 j) := by
  wk_entry_kb_win

/-! ## 2a. The reference state and the generic decode/token helpers -/

/-- Rocq `st_misaC_dstateM`. -/
theorem stMisaCDstateM : (_get_Misa_C (WkEntryEff.dstateM.regs .misa) == 1#1) = true := by
  decide +kernel

/-- Lean-only: the reference state satisfies the funnel's configuration premise. -/
theorem WkStartAux.cfgOkD : cfgOk WkEntryEff.dstateM := Or.inl ⟨rfl, rfl⟩

/-- Lean-only (deviation 4): the decode at `dstateM` from the two walks. -/
theorem WkStartAux.decRef {X : Type} (m : SailM X) (x : X)
    (hM : runRead drefM m = some (x, true)) (hS : runRead WkEntryNew.drefS0 m = some (x, true)) :
    exec m WkEntryEff.dstateM = some (x, WkEntryEff.dstateM) :=
  WkEntryNew.execAnyCfg m x hM hS WkEntryEff.dstateM rfl WkStartAux.cfgOkD

section tok
variable {GF : BundledGFunctors} [WeakGS GF]

/-- Lean-only (deviation 5): Rocq's `winstr_m_of_text` script for a full-word instruction. -/
theorem WkStartAux.tokBase (kbs : GMapF PAddr (BitVec 8)) (hcov : wkbCovers kbs) (A : Int)
    (w : BitVec 32) (i : instruction)
    (hal : is_aligned_vaddr (.Virtaddr (BitVec.ofInt 64 A)) 2 = true)
    (hacc : decide (paZ (BitVec.ofInt 64 A) + ((4 : Nat) : Int) ≤ 18446744073709551616) = true)
    (hram : inRam (BitVec.ofInt 64 A) 4)
    (hnrvc : isRVC (Sail.BitVec.extractLsb w 15 0) = false)
    (hlp : is_lpad_instruction i = false)
    (hM : runRead drefM (ext_decode w) = some (i, true))
    (hS : runRead WkEntryNew.drefS0 (ext_decode w) = some (i, true))
    (hgood : goodb0 WkEntryEff.dM (ext_decode w) WkEntryEff.dstateM = true)
    (hdec : exec (ext_decode w) WkEntryEff.dstateM = some (i, WkEntryEff.dstateM))
    (hkb : ∀ j : Nat, j < 4 →
      WkEntryEff.kernelBytes (A + (j : Int)) = some (nthByte (n := 4) w j)) :
    wkernelText (GF := GF) kbs ⊢ winstrM (GF := GF) (BitVec.ofInt 64 A) false i := by
  have hall : wdecAll (.F_Base w) i := WkEntryNew.decBase w i hM hS
  have href : wdecRef (.F_Base w) i := ⟨hgood, hdec⟩
  have key : wkernelText (GF := GF) kbs ⊢
      winstrM (GF := GF) (BitVec.ofInt 64 A) (fetchIsRvc (.F_Base w)) i := by
    iintro #Ht
    ihave H := winstrMOfText (GF := GF) kbs (BitVec.ofInt 64 A) (.F_Base w) w i hal
      (accWfOfLeb _ _ hacc) hram ⟨rfl, hnrvc⟩ hlp hall href $$ Ht
      %(wkbWindow kbs A w hcov hkb)
    iexact H
  exact key

/-- Lean-only (deviation 5): Rocq's `winstr_m_of_text` script for a compressed instruction. -/
theorem WkStartAux.tokRvc (kbs : GMapF PAddr (BitVec 8)) (hcov : wkbCovers kbs) (A : Int)
    (w : BitVec 32) (h : BitVec 16) (i0 i : instruction)
    (hal : is_aligned_vaddr (.Virtaddr (BitVec.ofInt 64 A)) 2 = true)
    (hacc : decide (paZ (BitVec.ofInt 64 A) + ((4 : Nat) : Int) ≤ 18446744073709551616) = true)
    (hram : inRam (BitVec.ofInt 64 A) 4)
    (hsub : Sail.BitVec.extractLsb w 15 0 = h)
    (hrvc : isRVC h = true)
    (hlp : is_lpad_instruction i = false)
    (hl0 : is_lpad_instruction i0 = false)
    (hM : runRead drefM (ext_decode_compressed h) = some (i0, true))
    (hS : runRead WkEntryNew.drefS0 (ext_decode_compressed h) = some (i0, true))
    (hgood : goodb0 WkEntryEff.dM (ext_decode_compressed h) WkEntryEff.dstateM = true)
    (hdec : exec (ext_decode_compressed h) WkEntryEff.dstateM = some (i0, WkEntryEff.dstateM))
    (hgexp : ∀ s : ExecSt, goodb0 dNone (execute i0) s = true)
    (hexp : ∀ s : ExecSt, exec (execute i0) s = some (.ExecuteAs i, s))
    (hkb : ∀ j : Nat, j < 4 →
      WkEntryEff.kernelBytes (A + (j : Int)) = some (nthByte (n := 4) w j)) :
    wkernelText (GF := GF) kbs ⊢ winstrM (GF := GF) (BitVec.ofInt 64 A) true i := by
  have hall : wdecAll (.F_RVC h) i := WkEntryNew.decRvc h i0 i hM hS hl0 hexp
  have href : wdecRef (.F_RVC h) i := ⟨hgood, i0, hdec, hl0, hgexp, hexp⟩
  have key : wkernelText (GF := GF) kbs ⊢
      winstrM (GF := GF) (BitVec.ofInt 64 A) (fetchIsRvc (.F_RVC h)) i := by
    iintro #Ht
    ihave H := winstrMOfText (GF := GF) kbs (BitVec.ofInt 64 A) (.F_RVC h) w i hal
      (accWfOfLeb _ _ hacc) hram ⟨hsub, hrvc⟩ hlp hall href $$ Ht
      %(wkbWindow kbs A w hcov hkb)
    iexact H
  exact key

end tok

/-! ## 3. Register-map drivers (deviation 6) -/

/-- Rocq Ltac `st_reg_neq`: a disequality of two concrete register numbers. -/
macro "wk_start_reg_neq" : tactic => `(tactic| decide)

/-- Rocq Ltac `st_look`: a lookup through a chain of concrete `RegMap.set`s. -/
macro "wk_start_look" : tactic =>
  `(tactic| first
    | rfl
    | (simp (disch := decide) only [RegMap.set_same, RegMap.set_other]; done)
    | (simp (disch := decide) only [RegMap.set_same, RegMap.set_other]; assumption))

example (m : RegMap) (v w : BitVec 64) : (m.set 15#5 v).set 14#5 w 15#5 = v := by wk_start_look
example : (WkStartAux.cspRs1 ≠ WkStartAux.tiRa) := by wk_start_reg_neq

/-- Rocq `rf_upd2_same`: two cells taken out of a file at their own values fold back. -/
theorem rfUpd2Same (f : RegMap) (k1 k2 : BitVec 5) (v1 v2 : BitVec 64) :
    k1 ≠ k2 → f k1 = v1 → f k2 = v2 → (f.set k2 v2).set k1 v1 = f := by
  intro _ h1 h2
  subst h1 h2
  rw [RegMap.set_self, RegMap.set_self]

/-! ## 2. Decode facts

Per instruction: the two read-only decode walks (Lean-only `WkStartAux.walkNNM`/`walkNNS`, the
`kernel_rfl` recipe of `WkEntryNew` deviation 5, standing in for Rocq's `KernelDecode*.kd_*`),
the decode at the reference state `dstateM` (`stdecNN`, derived from the walks), the read-set
witness (`stgoodNN`) and, for RVC instructions, the intermediate AST's landing-pad / read-set /
expansion facts (`stlpadNN`, `stgoodexpNN`, `stexpNN`). -/

section walks
attribute [local semireducible] LeanRV64D.Functions.hartSupports
  LeanRV64D.Functions.currentlyEnabled

theorem WkStartAux.walk30M : runRead drefM (ext_decode_compressed sth30) =
    some (.C_ADDI (i9, .Regidx cspRs1), true) := by kernel_rfl
theorem WkStartAux.walk30S : runRead WkEntryNew.drefS0 (ext_decode_compressed sth30) =
    some (.C_ADDI (i9, .Regidx cspRs1), true) := by kernel_rfl
theorem WkStartAux.walk31M : runRead drefM (ext_decode_compressed sth31) =
    some (.C_SDSP (u10, .Regidx tiRa), true) := by kernel_rfl
theorem WkStartAux.walk31S : runRead WkEntryNew.drefS0 (ext_decode_compressed sth31) =
    some (.C_SDSP (u10, .Regidx tiRa), true) := by kernel_rfl
theorem WkStartAux.walk32M : runRead drefM (ext_decode_compressed sth32) =
    some (.C_SDSP (u11, .Regidx tiS0), true) := by kernel_rfl
theorem WkStartAux.walk32S : runRead WkEntryNew.drefS0 (ext_decode_compressed sth32) =
    some (.C_SDSP (u11, .Regidx tiS0), true) := by kernel_rfl
theorem WkStartAux.walk33M : runRead drefM (ext_decode_compressed sth33) =
    some (.C_ADDI4SPN (.Cregidx 0#3, nz12), true) := by kernel_rfl
theorem WkStartAux.walk33S : runRead WkEntryNew.drefS0 (ext_decode_compressed sth33) =
    some (.C_ADDI4SPN (.Cregidx 0#3, nz12), true) := by kernel_rfl
theorem WkStartAux.walk34M : runRead drefM (ext_decode stw34) =
    some (.CSRReg (0x300#12, zreg, .Regidx tiA5, .CSRRS), true) := by kernel_rfl
theorem WkStartAux.walk34S : runRead WkEntryNew.drefS0 (ext_decode stw34) =
    some (.CSRReg (0x300#12, zreg, .Regidx tiA5, .CSRRS), true) := by kernel_rfl
theorem WkStartAux.walk35M : runRead drefM (ext_decode_compressed sth35) =
    some (.C_LUI (si35, .Regidx tiA4), true) := by kernel_rfl
theorem WkStartAux.walk35S : runRead WkEntryNew.drefS0 (ext_decode_compressed sth35) =
    some (.C_LUI (si35, .Regidx tiA4), true) := by kernel_rfl
theorem WkStartAux.walk36M : runRead drefM (ext_decode stw36) =
    some (.ITYPE (si36, .Regidx tiA4, .Regidx tiA4, .ADDI), true) := by kernel_rfl
theorem WkStartAux.walk36S : runRead WkEntryNew.drefS0 (ext_decode stw36) =
    some (.ITYPE (si36, .Regidx tiA4, .Regidx tiA4, .ADDI), true) := by kernel_rfl
theorem WkStartAux.walk37M : runRead drefM (ext_decode_compressed sth37) =
    some (.C_AND (.Cregidx 7#3, .Cregidx 6#3), true) := by kernel_rfl
theorem WkStartAux.walk37S : runRead WkEntryNew.drefS0 (ext_decode_compressed sth37) =
    some (.C_AND (.Cregidx 7#3, .Cregidx 6#3), true) := by kernel_rfl
theorem WkStartAux.walk38M : runRead drefM (ext_decode_compressed sth38) =
    some (.C_LUI (si38, .Regidx tiA4), true) := by kernel_rfl
theorem WkStartAux.walk38S : runRead WkEntryNew.drefS0 (ext_decode_compressed sth38) =
    some (.C_LUI (si38, .Regidx tiA4), true) := by kernel_rfl
theorem WkStartAux.walk39M : runRead drefM (ext_decode stw39) =
    some (.ITYPE (si39, .Regidx tiA4, .Regidx tiA4, .ADDI), true) := by kernel_rfl
theorem WkStartAux.walk39S : runRead WkEntryNew.drefS0 (ext_decode stw39) =
    some (.ITYPE (si39, .Regidx tiA4, .Regidx tiA4, .ADDI), true) := by kernel_rfl
theorem WkStartAux.walk40M : runRead drefM (ext_decode_compressed sth40) =
    some (.C_OR (.Cregidx 7#3, .Cregidx 6#3), true) := by kernel_rfl
theorem WkStartAux.walk40S : runRead WkEntryNew.drefS0 (ext_decode_compressed sth40) =
    some (.C_OR (.Cregidx 7#3, .Cregidx 6#3), true) := by kernel_rfl
theorem WkStartAux.walk41M : runRead drefM (ext_decode stw41) =
    some (.CSRReg (0x300#12, .Regidx tiA5, zreg, .CSRRW), true) := by kernel_rfl
theorem WkStartAux.walk41S : runRead WkEntryNew.drefS0 (ext_decode stw41) =
    some (.CSRReg (0x300#12, .Regidx tiA5, zreg, .CSRRW), true) := by kernel_rfl
theorem WkStartAux.walk42M : runRead drefM (ext_decode stw42) =
    some (.UTYPE (si42, .Regidx tiA5, .AUIPC), true) := by kernel_rfl
theorem WkStartAux.walk42S : runRead WkEntryNew.drefS0 (ext_decode stw42) =
    some (.UTYPE (si42, .Regidx tiA5, .AUIPC), true) := by kernel_rfl
theorem WkStartAux.walk43M : runRead drefM (ext_decode stw43) =
    some (.ITYPE (si43, .Regidx tiA5, .Regidx tiA5, .ADDI), true) := by kernel_rfl
theorem WkStartAux.walk43S : runRead WkEntryNew.drefS0 (ext_decode stw43) =
    some (.ITYPE (si43, .Regidx tiA5, .Regidx tiA5, .ADDI), true) := by kernel_rfl
theorem WkStartAux.walk44M : runRead drefM (ext_decode stw44) =
    some (.CSRReg (0x341#12, .Regidx tiA5, zreg, .CSRRW), true) := by kernel_rfl
theorem WkStartAux.walk44S : runRead WkEntryNew.drefS0 (ext_decode stw44) =
    some (.CSRReg (0x341#12, .Regidx tiA5, zreg, .CSRRW), true) := by kernel_rfl
theorem WkStartAux.walk45M : runRead drefM (ext_decode_compressed sth45) =
    some (.C_LI (si45, .Regidx tiA5), true) := by kernel_rfl
theorem WkStartAux.walk45S : runRead WkEntryNew.drefS0 (ext_decode_compressed sth45) =
    some (.C_LI (si45, .Regidx tiA5), true) := by kernel_rfl
theorem WkStartAux.walk46M : runRead drefM (ext_decode stw46) =
    some (.CSRReg (0x180#12, .Regidx tiA5, zreg, .CSRRW), true) := by kernel_rfl
theorem WkStartAux.walk46S : runRead WkEntryNew.drefS0 (ext_decode stw46) =
    some (.CSRReg (0x180#12, .Regidx tiA5, zreg, .CSRRW), true) := by kernel_rfl
theorem WkStartAux.walk47M : runRead drefM (ext_decode_compressed sth47) =
    some (.C_LUI (si47, .Regidx tiA5), true) := by kernel_rfl
theorem WkStartAux.walk47S : runRead WkEntryNew.drefS0 (ext_decode_compressed sth47) =
    some (.C_LUI (si47, .Regidx tiA5), true) := by kernel_rfl
theorem WkStartAux.walk48M : runRead drefM (ext_decode_compressed sth48) =
    some (.C_ADDI (si48, .Regidx tiA5), true) := by kernel_rfl
theorem WkStartAux.walk48S : runRead WkEntryNew.drefS0 (ext_decode_compressed sth48) =
    some (.C_ADDI (si48, .Regidx tiA5), true) := by kernel_rfl
theorem WkStartAux.walk49M : runRead drefM (ext_decode stw49) =
    some (.CSRReg (0x302#12, .Regidx tiA5, zreg, .CSRRW), true) := by kernel_rfl
theorem WkStartAux.walk49S : runRead WkEntryNew.drefS0 (ext_decode stw49) =
    some (.CSRReg (0x302#12, .Regidx tiA5, zreg, .CSRRW), true) := by kernel_rfl
theorem WkStartAux.walk50M : runRead drefM (ext_decode stw50) =
    some (.CSRReg (0x303#12, .Regidx tiA5, zreg, .CSRRW), true) := by kernel_rfl
theorem WkStartAux.walk50S : runRead WkEntryNew.drefS0 (ext_decode stw50) =
    some (.CSRReg (0x303#12, .Regidx tiA5, zreg, .CSRRW), true) := by kernel_rfl
theorem WkStartAux.walk51M : runRead drefM (ext_decode stw51) =
    some (.CSRReg (0x104#12, zreg, .Regidx tiA5, .CSRRS), true) := by kernel_rfl
theorem WkStartAux.walk51S : runRead WkEntryNew.drefS0 (ext_decode stw51) =
    some (.CSRReg (0x104#12, zreg, .Regidx tiA5, .CSRRS), true) := by kernel_rfl
theorem WkStartAux.walk52M : runRead drefM (ext_decode stw52) =
    some (.ITYPE (si52, .Regidx tiA5, .Regidx tiA5, .ORI), true) := by kernel_rfl
theorem WkStartAux.walk52S : runRead WkEntryNew.drefS0 (ext_decode stw52) =
    some (.ITYPE (si52, .Regidx tiA5, .Regidx tiA5, .ORI), true) := by kernel_rfl
theorem WkStartAux.walk53M : runRead drefM (ext_decode stw53) =
    some (.CSRReg (0x104#12, .Regidx tiA5, zreg, .CSRRW), true) := by kernel_rfl
theorem WkStartAux.walk53S : runRead WkEntryNew.drefS0 (ext_decode stw53) =
    some (.CSRReg (0x104#12, .Regidx tiA5, zreg, .CSRRW), true) := by kernel_rfl
theorem WkStartAux.walk54M : runRead drefM (ext_decode_compressed sth54) =
    some (.C_LI (si54, .Regidx tiA5), true) := by kernel_rfl
theorem WkStartAux.walk54S : runRead WkEntryNew.drefS0 (ext_decode_compressed sth54) =
    some (.C_LI (si54, .Regidx tiA5), true) := by kernel_rfl
theorem WkStartAux.walk55M : runRead drefM (ext_decode_compressed sth55) =
    some (.C_SRLI (ssh55, .Cregidx 7#3), true) := by kernel_rfl
theorem WkStartAux.walk55S : runRead WkEntryNew.drefS0 (ext_decode_compressed sth55) =
    some (.C_SRLI (ssh55, .Cregidx 7#3), true) := by kernel_rfl
theorem WkStartAux.walk56M : runRead drefM (ext_decode stw56) =
    some (.CSRReg (0x3B0#12, .Regidx tiA5, zreg, .CSRRW), true) := by kernel_rfl
theorem WkStartAux.walk56S : runRead WkEntryNew.drefS0 (ext_decode stw56) =
    some (.CSRReg (0x3B0#12, .Regidx tiA5, zreg, .CSRRW), true) := by kernel_rfl
theorem WkStartAux.walk57M : runRead drefM (ext_decode_compressed sth57) =
    some (.C_LI (si57, .Regidx tiA5), true) := by kernel_rfl
theorem WkStartAux.walk57S : runRead WkEntryNew.drefS0 (ext_decode_compressed sth57) =
    some (.C_LI (si57, .Regidx tiA5), true) := by kernel_rfl
theorem WkStartAux.walk58M : runRead drefM (ext_decode stw58) =
    some (.CSRReg (0x3A0#12, .Regidx tiA5, zreg, .CSRRW), true) := by kernel_rfl
theorem WkStartAux.walk58S : runRead WkEntryNew.drefS0 (ext_decode stw58) =
    some (.CSRReg (0x3A0#12, .Regidx tiA5, zreg, .CSRRW), true) := by kernel_rfl
theorem WkStartAux.walkAe0M : runRead drefM (ext_decode stwAe0) =
    some (.CSRReg (0x30A#12, zreg, .Regidx tiA5, .CSRRS), true) := by kernel_rfl
theorem WkStartAux.walkAe0S : runRead WkEntryNew.drefS0 (ext_decode stwAe0) =
    some (.CSRReg (0x30A#12, zreg, .Regidx tiA5, .CSRRS), true) := by kernel_rfl
theorem WkStartAux.walkAe1M : runRead drefM (ext_decode_compressed sthAe1) =
    some (.C_LI (saeLi, .Regidx tiA4), true) := by kernel_rfl
theorem WkStartAux.walkAe1S : runRead WkEntryNew.drefS0 (ext_decode_compressed sthAe1) =
    some (.C_LI (saeLi, .Regidx tiA4), true) := by kernel_rfl
theorem WkStartAux.walkAe2M : runRead drefM (ext_decode_compressed sthAe2) =
    some (.C_SLLI (saeSlli, .Regidx tiA4), true) := by kernel_rfl
theorem WkStartAux.walkAe2S : runRead WkEntryNew.drefS0 (ext_decode_compressed sthAe2) =
    some (.C_SLLI (saeSlli, .Regidx tiA4), true) := by kernel_rfl
theorem WkStartAux.walkAe3M : runRead drefM (ext_decode_compressed sthAe3) =
    some (.C_OR (.Cregidx 7#3, .Cregidx 6#3), true) := by kernel_rfl
theorem WkStartAux.walkAe3S : runRead WkEntryNew.drefS0 (ext_decode_compressed sthAe3) =
    some (.C_OR (.Cregidx 7#3, .Cregidx 6#3), true) := by kernel_rfl
theorem WkStartAux.walkAe4M : runRead drefM (ext_decode stwAe4) =
    some (.CSRReg (0x30A#12, .Regidx tiA5, zreg, .CSRRW), true) := by kernel_rfl
theorem WkStartAux.walkAe4S : runRead WkEntryNew.drefS0 (ext_decode stwAe4) =
    some (.CSRReg (0x30A#12, .Regidx tiA5, zreg, .CSRRW), true) := by kernel_rfl
theorem WkStartAux.walk59M : runRead drefM (ext_decode stw59) =
    some (.JAL (sjimm59, .Regidx tiRa), true) := by kernel_rfl
theorem WkStartAux.walk59S : runRead WkEntryNew.drefS0 (ext_decode stw59) =
    some (.JAL (sjimm59, .Regidx tiRa), true) := by kernel_rfl
theorem WkStartAux.walk60M : runRead drefM (ext_decode stw60) =
    some (.CSRReg (0xF14#12, zreg, .Regidx tiA5, .CSRRS), true) := by kernel_rfl
theorem WkStartAux.walk60S : runRead WkEntryNew.drefS0 (ext_decode stw60) =
    some (.CSRReg (0xF14#12, zreg, .Regidx tiA5, .CSRRS), true) := by kernel_rfl
theorem WkStartAux.walk61M : runRead drefM (ext_decode_compressed sth61) =
    some (.C_ADDIW (si61, .Regidx tiA5), true) := by kernel_rfl
theorem WkStartAux.walk61S : runRead WkEntryNew.drefS0 (ext_decode_compressed sth61) =
    some (.C_ADDIW (si61, .Regidx tiA5), true) := by kernel_rfl
theorem WkStartAux.walk62M : runRead drefM (ext_decode_compressed sth62) =
    some (.C_MV (.Regidx stTp, .Regidx tiA5), true) := by kernel_rfl
theorem WkStartAux.walk62S : runRead WkEntryNew.drefS0 (ext_decode_compressed sth62) =
    some (.C_MV (.Regidx stTp, .Regidx tiA5), true) := by kernel_rfl
theorem WkStartAux.walk63M : runRead drefM (ext_decode stw63) =
    some (.MRET (), true) := by kernel_rfl
theorem WkStartAux.walk63S : runRead WkEntryNew.drefS0 (ext_decode stw63) =
    some (.MRET (), true) := by kernel_rfl

end walks

/-! ### 30: c.addi sp,-16 -/

/-- Rocq `stdec_30`. -/
theorem stdec30 : exec (ext_decode_compressed sth30) WkEntryEff.dstateM =
    some (.C_ADDI (i9, .Regidx cspRs1), WkEntryEff.dstateM) :=
  WkStartAux.decRef _ _ WkStartAux.walk30M WkStartAux.walk30S
/-- Rocq `stgood_30`. -/
theorem stgood30 : goodb0 WkEntryEff.dM (ext_decode_compressed sth30) WkEntryEff.dstateM = true := by
  decide +kernel
/-- Rocq `stlpad_30`. -/
theorem stlpad30 : is_lpad_instruction (.C_ADDI (i9, .Regidx cspRs1)) = false := by decide +kernel
/-- Rocq `stgoodexp_30`. -/
theorem stgoodexp30 : ∀ s : ExecSt, goodb0 dNone (execute (.C_ADDI (i9, .Regidx cspRs1))) s = true :=
  fun _ => rfl

/-! ### 31: c.sdsp ra,8(sp) -/

/-- Rocq `stdec_31`. -/
theorem stdec31 : exec (ext_decode_compressed sth31) WkEntryEff.dstateM =
    some (.C_SDSP (u10, .Regidx tiRa), WkEntryEff.dstateM) :=
  WkStartAux.decRef _ _ WkStartAux.walk31M WkStartAux.walk31S
/-- Rocq `stgood_31`. -/
theorem stgood31 : goodb0 WkEntryEff.dM (ext_decode_compressed sth31) WkEntryEff.dstateM = true := by
  decide +kernel
/-- Rocq `stlpad_31`. -/
theorem stlpad31 : is_lpad_instruction (.C_SDSP (u10, .Regidx tiRa)) = false := by decide +kernel
/-- Rocq `stgoodexp_31`. -/
theorem stgoodexp31 : ∀ s : ExecSt, goodb0 dNone (execute (.C_SDSP (u10, .Regidx tiRa))) s = true :=
  fun _ => rfl

/-! ### 32: c.sdsp s0,0(sp) -/

/-- Rocq `stdec_32`. -/
theorem stdec32 : exec (ext_decode_compressed sth32) WkEntryEff.dstateM =
    some (.C_SDSP (u11, .Regidx tiS0), WkEntryEff.dstateM) :=
  WkStartAux.decRef _ _ WkStartAux.walk32M WkStartAux.walk32S
/-- Rocq `stgood_32`. -/
theorem stgood32 : goodb0 WkEntryEff.dM (ext_decode_compressed sth32) WkEntryEff.dstateM = true := by
  decide +kernel
/-- Rocq `stlpad_32`. -/
theorem stlpad32 : is_lpad_instruction (.C_SDSP (u11, .Regidx tiS0)) = false := by decide +kernel
/-- Rocq `stgoodexp_32`. -/
theorem stgoodexp32 : ∀ s : ExecSt, goodb0 dNone (execute (.C_SDSP (u11, .Regidx tiS0))) s = true :=
  fun _ => rfl

/-! ### 33: c.addi4spn s0,sp,16 -/

/-- Rocq `stdec_33`. -/
theorem stdec33 : exec (ext_decode_compressed sth33) WkEntryEff.dstateM =
    some (.C_ADDI4SPN (.Cregidx 0#3, nz12), WkEntryEff.dstateM) :=
  WkStartAux.decRef _ _ WkStartAux.walk33M WkStartAux.walk33S
/-- Rocq `stgood_33`. -/
theorem stgood33 : goodb0 WkEntryEff.dM (ext_decode_compressed sth33) WkEntryEff.dstateM = true := by
  decide +kernel
/-- Rocq `stlpad_33`. -/
theorem stlpad33 : is_lpad_instruction (.C_ADDI4SPN (.Cregidx 0#3, nz12)) = false := by decide +kernel
/-- Rocq `stgoodexp_33`. -/
theorem stgoodexp33 : ∀ s : ExecSt, goodb0 dNone (execute (.C_ADDI4SPN (.Cregidx 0#3, nz12))) s = true :=
  fun _ => rfl

/-! ### 34: csrr a5,mstatus -/

/-- Rocq `stdec_34`. -/
theorem stdec34 : exec (ext_decode stw34) WkEntryEff.dstateM =
    some (.CSRReg (0x300#12, zreg, .Regidx tiA5, .CSRRS), WkEntryEff.dstateM) :=
  WkStartAux.decRef _ _ WkStartAux.walk34M WkStartAux.walk34S
/-- Rocq `stgood_34`. -/
theorem stgood34 : goodb0 WkEntryEff.dM (ext_decode stw34) WkEntryEff.dstateM = true := by
  decide +kernel

/-! ### 35: c.lui a4,0xffffe -/

/-- Rocq `stdec_35`. -/
theorem stdec35 : exec (ext_decode_compressed sth35) WkEntryEff.dstateM =
    some (.C_LUI (si35, .Regidx tiA4), WkEntryEff.dstateM) :=
  WkStartAux.decRef _ _ WkStartAux.walk35M WkStartAux.walk35S
/-- Rocq `stgood_35`. -/
theorem stgood35 : goodb0 WkEntryEff.dM (ext_decode_compressed sth35) WkEntryEff.dstateM = true := by
  decide +kernel
/-- Rocq `stlpad_35`. -/
theorem stlpad35 : is_lpad_instruction (.C_LUI (si35, .Regidx tiA4)) = false := by decide +kernel
/-- Rocq `stgoodexp_35`. -/
theorem stgoodexp35 : ∀ s : ExecSt, goodb0 dNone (execute (.C_LUI (si35, .Regidx tiA4))) s = true :=
  fun _ => rfl

/-! ### 36: addi a4,a4,2047 -/

/-- Rocq `stdec_36`. -/
theorem stdec36 : exec (ext_decode stw36) WkEntryEff.dstateM =
    some (.ITYPE (si36, .Regidx tiA4, .Regidx tiA4, .ADDI), WkEntryEff.dstateM) :=
  WkStartAux.decRef _ _ WkStartAux.walk36M WkStartAux.walk36S
/-- Rocq `stgood_36`. -/
theorem stgood36 : goodb0 WkEntryEff.dM (ext_decode stw36) WkEntryEff.dstateM = true := by
  decide +kernel

/-! ### 37: c.and a5,a4 -/

/-- Rocq `stdec_37`. -/
theorem stdec37 : exec (ext_decode_compressed sth37) WkEntryEff.dstateM =
    some (.C_AND (.Cregidx 7#3, .Cregidx 6#3), WkEntryEff.dstateM) :=
  WkStartAux.decRef _ _ WkStartAux.walk37M WkStartAux.walk37S
/-- Rocq `stgood_37`. -/
theorem stgood37 : goodb0 WkEntryEff.dM (ext_decode_compressed sth37) WkEntryEff.dstateM = true := by
  decide +kernel
/-- Rocq `stlpad_37`. -/
theorem stlpad37 : is_lpad_instruction (.C_AND (.Cregidx 7#3, .Cregidx 6#3)) = false := by decide +kernel
/-- Rocq `stgoodexp_37`. -/
theorem stgoodexp37 : ∀ s : ExecSt, goodb0 dNone (execute (.C_AND (.Cregidx 7#3, .Cregidx 6#3))) s = true :=
  fun _ => rfl

/-! ### 38: c.lui a4,1 -/

/-- Rocq `stdec_38`. -/
theorem stdec38 : exec (ext_decode_compressed sth38) WkEntryEff.dstateM =
    some (.C_LUI (si38, .Regidx tiA4), WkEntryEff.dstateM) :=
  WkStartAux.decRef _ _ WkStartAux.walk38M WkStartAux.walk38S
/-- Rocq `stgood_38`. -/
theorem stgood38 : goodb0 WkEntryEff.dM (ext_decode_compressed sth38) WkEntryEff.dstateM = true := by
  decide +kernel
/-- Rocq `stlpad_38`. -/
theorem stlpad38 : is_lpad_instruction (.C_LUI (si38, .Regidx tiA4)) = false := by decide +kernel
/-- Rocq `stgoodexp_38`. -/
theorem stgoodexp38 : ∀ s : ExecSt, goodb0 dNone (execute (.C_LUI (si38, .Regidx tiA4))) s = true :=
  fun _ => rfl

/-! ### 39: addi a4,a4,-2048 -/

/-- Rocq `stdec_39`. -/
theorem stdec39 : exec (ext_decode stw39) WkEntryEff.dstateM =
    some (.ITYPE (si39, .Regidx tiA4, .Regidx tiA4, .ADDI), WkEntryEff.dstateM) :=
  WkStartAux.decRef _ _ WkStartAux.walk39M WkStartAux.walk39S
/-- Rocq `stgood_39`. -/
theorem stgood39 : goodb0 WkEntryEff.dM (ext_decode stw39) WkEntryEff.dstateM = true := by
  decide +kernel

/-! ### 40: c.or a5,a4 -/

/-- Rocq `stdec_40`. -/
theorem stdec40 : exec (ext_decode_compressed sth40) WkEntryEff.dstateM =
    some (.C_OR (.Cregidx 7#3, .Cregidx 6#3), WkEntryEff.dstateM) :=
  WkStartAux.decRef _ _ WkStartAux.walk40M WkStartAux.walk40S
/-- Rocq `stgood_40`. -/
theorem stgood40 : goodb0 WkEntryEff.dM (ext_decode_compressed sth40) WkEntryEff.dstateM = true := by
  decide +kernel
/-- Rocq `stlpad_40`. -/
theorem stlpad40 : is_lpad_instruction (.C_OR (.Cregidx 7#3, .Cregidx 6#3)) = false := by decide +kernel
/-- Rocq `stgoodexp_40`. -/
theorem stgoodexp40 : ∀ s : ExecSt, goodb0 dNone (execute (.C_OR (.Cregidx 7#3, .Cregidx 6#3))) s = true :=
  fun _ => rfl

/-! ### 41: csrw mstatus,a5 -/

/-- Rocq `stdec_41`. -/
theorem stdec41 : exec (ext_decode stw41) WkEntryEff.dstateM =
    some (.CSRReg (0x300#12, .Regidx tiA5, zreg, .CSRRW), WkEntryEff.dstateM) :=
  WkStartAux.decRef _ _ WkStartAux.walk41M WkStartAux.walk41S
/-- Rocq `stgood_41`. -/
theorem stgood41 : goodb0 WkEntryEff.dM (ext_decode stw41) WkEntryEff.dstateM = true := by
  decide +kernel

/-! ### 42: auipc a5,1 -/

/-- Rocq `stdec_42`. -/
theorem stdec42 : exec (ext_decode stw42) WkEntryEff.dstateM =
    some (.UTYPE (si42, .Regidx tiA5, .AUIPC), WkEntryEff.dstateM) :=
  WkStartAux.decRef _ _ WkStartAux.walk42M WkStartAux.walk42S
/-- Rocq `stgood_42`. -/
theorem stgood42 : goodb0 WkEntryEff.dM (ext_decode stw42) WkEntryEff.dstateM = true := by
  decide +kernel

/-! ### 43: addi a5,a5,-426 (drift: Rocq -506) -/

/-- Rocq `stdec_43`. -/
theorem stdec43 : exec (ext_decode stw43) WkEntryEff.dstateM =
    some (.ITYPE (si43, .Regidx tiA5, .Regidx tiA5, .ADDI), WkEntryEff.dstateM) :=
  WkStartAux.decRef _ _ WkStartAux.walk43M WkStartAux.walk43S
/-- Rocq `stgood_43`. -/
theorem stgood43 : goodb0 WkEntryEff.dM (ext_decode stw43) WkEntryEff.dstateM = true := by
  decide +kernel

/-! ### 44: csrw mepc,a5 -/

/-- Rocq `stdec_44`. -/
theorem stdec44 : exec (ext_decode stw44) WkEntryEff.dstateM =
    some (.CSRReg (0x341#12, .Regidx tiA5, zreg, .CSRRW), WkEntryEff.dstateM) :=
  WkStartAux.decRef _ _ WkStartAux.walk44M WkStartAux.walk44S
/-- Rocq `stgood_44`. -/
theorem stgood44 : goodb0 WkEntryEff.dM (ext_decode stw44) WkEntryEff.dstateM = true := by
  decide +kernel

/-! ### 45: c.li a5,0 -/

/-- Rocq `stdec_45`. -/
theorem stdec45 : exec (ext_decode_compressed sth45) WkEntryEff.dstateM =
    some (.C_LI (si45, .Regidx tiA5), WkEntryEff.dstateM) :=
  WkStartAux.decRef _ _ WkStartAux.walk45M WkStartAux.walk45S
/-- Rocq `stgood_45`. -/
theorem stgood45 : goodb0 WkEntryEff.dM (ext_decode_compressed sth45) WkEntryEff.dstateM = true := by
  decide +kernel
/-- Rocq `stlpad_45`. -/
theorem stlpad45 : is_lpad_instruction (.C_LI (si45, .Regidx tiA5)) = false := by decide +kernel
/-- Rocq `stgoodexp_45`. -/
theorem stgoodexp45 : ∀ s : ExecSt, goodb0 dNone (execute (.C_LI (si45, .Regidx tiA5))) s = true :=
  fun _ => rfl

/-! ### 46: csrw satp,a5 -/

/-- Rocq `stdec_46`. -/
theorem stdec46 : exec (ext_decode stw46) WkEntryEff.dstateM =
    some (.CSRReg (0x180#12, .Regidx tiA5, zreg, .CSRRW), WkEntryEff.dstateM) :=
  WkStartAux.decRef _ _ WkStartAux.walk46M WkStartAux.walk46S
/-- Rocq `stgood_46`. -/
theorem stgood46 : goodb0 WkEntryEff.dM (ext_decode stw46) WkEntryEff.dstateM = true := by
  decide +kernel

/-! ### 47: c.lui a5,0x10 -/

/-- Rocq `stdec_47`. -/
theorem stdec47 : exec (ext_decode_compressed sth47) WkEntryEff.dstateM =
    some (.C_LUI (si47, .Regidx tiA5), WkEntryEff.dstateM) :=
  WkStartAux.decRef _ _ WkStartAux.walk47M WkStartAux.walk47S
/-- Rocq `stgood_47`. -/
theorem stgood47 : goodb0 WkEntryEff.dM (ext_decode_compressed sth47) WkEntryEff.dstateM = true := by
  decide +kernel
/-- Rocq `stlpad_47`. -/
theorem stlpad47 : is_lpad_instruction (.C_LUI (si47, .Regidx tiA5)) = false := by decide +kernel
/-- Rocq `stgoodexp_47`. -/
theorem stgoodexp47 : ∀ s : ExecSt, goodb0 dNone (execute (.C_LUI (si47, .Regidx tiA5))) s = true :=
  fun _ => rfl

/-! ### 48: c.addi a5,-1 -/

/-- Rocq `stdec_48`. -/
theorem stdec48 : exec (ext_decode_compressed sth48) WkEntryEff.dstateM =
    some (.C_ADDI (si48, .Regidx tiA5), WkEntryEff.dstateM) :=
  WkStartAux.decRef _ _ WkStartAux.walk48M WkStartAux.walk48S
/-- Rocq `stgood_48`. -/
theorem stgood48 : goodb0 WkEntryEff.dM (ext_decode_compressed sth48) WkEntryEff.dstateM = true := by
  decide +kernel
/-- Rocq `stlpad_48`. -/
theorem stlpad48 : is_lpad_instruction (.C_ADDI (si48, .Regidx tiA5)) = false := by decide +kernel
/-- Rocq `stgoodexp_48`. -/
theorem stgoodexp48 : ∀ s : ExecSt, goodb0 dNone (execute (.C_ADDI (si48, .Regidx tiA5))) s = true :=
  fun _ => rfl

/-! ### 49: csrw medeleg,a5 -/

/-- Rocq `stdec_49`. -/
theorem stdec49 : exec (ext_decode stw49) WkEntryEff.dstateM =
    some (.CSRReg (0x302#12, .Regidx tiA5, zreg, .CSRRW), WkEntryEff.dstateM) :=
  WkStartAux.decRef _ _ WkStartAux.walk49M WkStartAux.walk49S
/-- Rocq `stgood_49`. -/
theorem stgood49 : goodb0 WkEntryEff.dM (ext_decode stw49) WkEntryEff.dstateM = true := by
  decide +kernel

/-! ### 50: csrw mideleg,a5 -/

/-- Rocq `stdec_50`. -/
theorem stdec50 : exec (ext_decode stw50) WkEntryEff.dstateM =
    some (.CSRReg (0x303#12, .Regidx tiA5, zreg, .CSRRW), WkEntryEff.dstateM) :=
  WkStartAux.decRef _ _ WkStartAux.walk50M WkStartAux.walk50S
/-- Rocq `stgood_50`. -/
theorem stgood50 : goodb0 WkEntryEff.dM (ext_decode stw50) WkEntryEff.dstateM = true := by
  decide +kernel

/-! ### 51: csrr a5,sie -/

/-- Rocq `stdec_51`. -/
theorem stdec51 : exec (ext_decode stw51) WkEntryEff.dstateM =
    some (.CSRReg (0x104#12, zreg, .Regidx tiA5, .CSRRS), WkEntryEff.dstateM) :=
  WkStartAux.decRef _ _ WkStartAux.walk51M WkStartAux.walk51S
/-- Rocq `stgood_51`. -/
theorem stgood51 : goodb0 WkEntryEff.dM (ext_decode stw51) WkEntryEff.dstateM = true := by
  decide +kernel

/-! ### 52: ori a5,a5,544 -/

/-- Rocq `stdec_52`. -/
theorem stdec52 : exec (ext_decode stw52) WkEntryEff.dstateM =
    some (.ITYPE (si52, .Regidx tiA5, .Regidx tiA5, .ORI), WkEntryEff.dstateM) :=
  WkStartAux.decRef _ _ WkStartAux.walk52M WkStartAux.walk52S
/-- Rocq `stgood_52`. -/
theorem stgood52 : goodb0 WkEntryEff.dM (ext_decode stw52) WkEntryEff.dstateM = true := by
  decide +kernel

/-! ### 53: csrw sie,a5 -/

/-- Rocq `stdec_53`. -/
theorem stdec53 : exec (ext_decode stw53) WkEntryEff.dstateM =
    some (.CSRReg (0x104#12, .Regidx tiA5, zreg, .CSRRW), WkEntryEff.dstateM) :=
  WkStartAux.decRef _ _ WkStartAux.walk53M WkStartAux.walk53S
/-- Rocq `stgood_53`. -/
theorem stgood53 : goodb0 WkEntryEff.dM (ext_decode stw53) WkEntryEff.dstateM = true := by
  decide +kernel

/-! ### 54: c.li a5,-1 -/

/-- Rocq `stdec_54`. -/
theorem stdec54 : exec (ext_decode_compressed sth54) WkEntryEff.dstateM =
    some (.C_LI (si54, .Regidx tiA5), WkEntryEff.dstateM) :=
  WkStartAux.decRef _ _ WkStartAux.walk54M WkStartAux.walk54S
/-- Rocq `stgood_54`. -/
theorem stgood54 : goodb0 WkEntryEff.dM (ext_decode_compressed sth54) WkEntryEff.dstateM = true := by
  decide +kernel
/-- Rocq `stlpad_54`. -/
theorem stlpad54 : is_lpad_instruction (.C_LI (si54, .Regidx tiA5)) = false := by decide +kernel
/-- Rocq `stgoodexp_54`. -/
theorem stgoodexp54 : ∀ s : ExecSt, goodb0 dNone (execute (.C_LI (si54, .Regidx tiA5))) s = true :=
  fun _ => rfl

/-! ### 55: c.srli a5,10 -/

/-- Rocq `stdec_55`. -/
theorem stdec55 : exec (ext_decode_compressed sth55) WkEntryEff.dstateM =
    some (.C_SRLI (ssh55, .Cregidx 7#3), WkEntryEff.dstateM) :=
  WkStartAux.decRef _ _ WkStartAux.walk55M WkStartAux.walk55S
/-- Rocq `stgood_55`. -/
theorem stgood55 : goodb0 WkEntryEff.dM (ext_decode_compressed sth55) WkEntryEff.dstateM = true := by
  decide +kernel
/-- Rocq `stlpad_55`. -/
theorem stlpad55 : is_lpad_instruction (.C_SRLI (ssh55, .Cregidx 7#3)) = false := by decide +kernel
/-- Rocq `stgoodexp_55`. -/
theorem stgoodexp55 : ∀ s : ExecSt, goodb0 dNone (execute (.C_SRLI (ssh55, .Cregidx 7#3))) s = true :=
  fun _ => rfl

/-! ### 56: csrw pmpaddr0,a5 -/

/-- Rocq `stdec_56`. -/
theorem stdec56 : exec (ext_decode stw56) WkEntryEff.dstateM =
    some (.CSRReg (0x3B0#12, .Regidx tiA5, zreg, .CSRRW), WkEntryEff.dstateM) :=
  WkStartAux.decRef _ _ WkStartAux.walk56M WkStartAux.walk56S
/-- Rocq `stgood_56`. -/
theorem stgood56 : goodb0 WkEntryEff.dM (ext_decode stw56) WkEntryEff.dstateM = true := by
  decide +kernel

/-! ### 57: c.li a5,15 -/

/-- Rocq `stdec_57`. -/
theorem stdec57 : exec (ext_decode_compressed sth57) WkEntryEff.dstateM =
    some (.C_LI (si57, .Regidx tiA5), WkEntryEff.dstateM) :=
  WkStartAux.decRef _ _ WkStartAux.walk57M WkStartAux.walk57S
/-- Rocq `stgood_57`. -/
theorem stgood57 : goodb0 WkEntryEff.dM (ext_decode_compressed sth57) WkEntryEff.dstateM = true := by
  decide +kernel
/-- Rocq `stlpad_57`. -/
theorem stlpad57 : is_lpad_instruction (.C_LI (si57, .Regidx tiA5)) = false := by decide +kernel
/-- Rocq `stgoodexp_57`. -/
theorem stgoodexp57 : ∀ s : ExecSt, goodb0 dNone (execute (.C_LI (si57, .Regidx tiA5))) s = true :=
  fun _ => rfl

/-! ### 58: csrw pmpcfg0,a5 -/

/-- Rocq `stdec_58`. -/
theorem stdec58 : exec (ext_decode stw58) WkEntryEff.dstateM =
    some (.CSRReg (0x3A0#12, .Regidx tiA5, zreg, .CSRRW), WkEntryEff.dstateM) :=
  WkStartAux.decRef _ _ WkStartAux.walk58M WkStartAux.walk58S
/-- Rocq `stgood_58`. -/
theorem stgood58 : goodb0 WkEntryEff.dM (ext_decode stw58) WkEntryEff.dstateM = true := by
  decide +kernel

/-! ### Ae0: csrr a5,menvcfg -/

/-- Rocq `stdec_ae0`. -/
theorem stdecAe0 : exec (ext_decode stwAe0) WkEntryEff.dstateM =
    some (.CSRReg (0x30A#12, zreg, .Regidx tiA5, .CSRRS), WkEntryEff.dstateM) :=
  WkStartAux.decRef _ _ WkStartAux.walkAe0M WkStartAux.walkAe0S
/-- Rocq `stgood_ae0`. -/
theorem stgoodAe0 : goodb0 WkEntryEff.dM (ext_decode stwAe0) WkEntryEff.dstateM = true := by
  decide +kernel

/-! ### Ae1: c.li a4,1 -/

/-- Rocq `stdec_ae1`. -/
theorem stdecAe1 : exec (ext_decode_compressed sthAe1) WkEntryEff.dstateM =
    some (.C_LI (saeLi, .Regidx tiA4), WkEntryEff.dstateM) :=
  WkStartAux.decRef _ _ WkStartAux.walkAe1M WkStartAux.walkAe1S
/-- Rocq `stgood_ae1`. -/
theorem stgoodAe1 : goodb0 WkEntryEff.dM (ext_decode_compressed sthAe1) WkEntryEff.dstateM = true := by
  decide +kernel
/-- Rocq `stlpad_ae1`. -/
theorem stlpadAe1 : is_lpad_instruction (.C_LI (saeLi, .Regidx tiA4)) = false := by decide +kernel
/-- Rocq `stgoodexp_ae1`. -/
theorem stgoodexpAe1 : ∀ s : ExecSt, goodb0 dNone (execute (.C_LI (saeLi, .Regidx tiA4))) s = true :=
  fun _ => rfl

/-! ### Ae2: c.slli a4,0x3d -/

/-- Rocq `stdec_ae2`. -/
theorem stdecAe2 : exec (ext_decode_compressed sthAe2) WkEntryEff.dstateM =
    some (.C_SLLI (saeSlli, .Regidx tiA4), WkEntryEff.dstateM) :=
  WkStartAux.decRef _ _ WkStartAux.walkAe2M WkStartAux.walkAe2S
/-- Rocq `stgood_ae2`. -/
theorem stgoodAe2 : goodb0 WkEntryEff.dM (ext_decode_compressed sthAe2) WkEntryEff.dstateM = true := by
  decide +kernel
/-- Rocq `stlpad_ae2`. -/
theorem stlpadAe2 : is_lpad_instruction (.C_SLLI (saeSlli, .Regidx tiA4)) = false := by decide +kernel
/-- Rocq `stgoodexp_ae2`. -/
theorem stgoodexpAe2 : ∀ s : ExecSt, goodb0 dNone (execute (.C_SLLI (saeSlli, .Regidx tiA4))) s = true :=
  fun _ => rfl

/-! ### Ae3: c.or a5,a4 -/

/-- Rocq `stdec_ae3`. -/
theorem stdecAe3 : exec (ext_decode_compressed sthAe3) WkEntryEff.dstateM =
    some (.C_OR (.Cregidx 7#3, .Cregidx 6#3), WkEntryEff.dstateM) :=
  WkStartAux.decRef _ _ WkStartAux.walkAe3M WkStartAux.walkAe3S
/-- Rocq `stgood_ae3`. -/
theorem stgoodAe3 : goodb0 WkEntryEff.dM (ext_decode_compressed sthAe3) WkEntryEff.dstateM = true := by
  decide +kernel
/-- Rocq `stlpad_ae3`. -/
theorem stlpadAe3 : is_lpad_instruction (.C_OR (.Cregidx 7#3, .Cregidx 6#3)) = false := by decide +kernel
/-- Rocq `stgoodexp_ae3`. -/
theorem stgoodexpAe3 : ∀ s : ExecSt, goodb0 dNone (execute (.C_OR (.Cregidx 7#3, .Cregidx 6#3))) s = true :=
  fun _ => rfl

/-! ### Ae4: csrw menvcfg,a5 -/

/-- Rocq `stdec_ae4`. -/
theorem stdecAe4 : exec (ext_decode stwAe4) WkEntryEff.dstateM =
    some (.CSRReg (0x30A#12, .Regidx tiA5, zreg, .CSRRW), WkEntryEff.dstateM) :=
  WkStartAux.decRef _ _ WkStartAux.walkAe4M WkStartAux.walkAe4S
/-- Rocq `stgood_ae4`. -/
theorem stgoodAe4 : goodb0 WkEntryEff.dM (ext_decode stwAe4) WkEntryEff.dstateM = true := by
  decide +kernel

/-! ### 59: jal ra,timerinit -/

/-- Rocq `stdec_59`. -/
theorem stdec59 : exec (ext_decode stw59) WkEntryEff.dstateM =
    some (.JAL (sjimm59, .Regidx tiRa), WkEntryEff.dstateM) :=
  WkStartAux.decRef _ _ WkStartAux.walk59M WkStartAux.walk59S
/-- Rocq `stgood_59`. -/
theorem stgood59 : goodb0 WkEntryEff.dM (ext_decode stw59) WkEntryEff.dstateM = true := by
  decide +kernel

/-! ### 60: csrr a5,mhartid -/

/-- Rocq `stdec_60`. -/
theorem stdec60 : exec (ext_decode stw60) WkEntryEff.dstateM =
    some (.CSRReg (0xF14#12, zreg, .Regidx tiA5, .CSRRS), WkEntryEff.dstateM) :=
  WkStartAux.decRef _ _ WkStartAux.walk60M WkStartAux.walk60S
/-- Rocq `stgood_60`. -/
theorem stgood60 : goodb0 WkEntryEff.dM (ext_decode stw60) WkEntryEff.dstateM = true := by
  decide +kernel

/-! ### 61: c.addiw a5,0 (sext.w) -/

/-- Rocq `stdec_61`. -/
theorem stdec61 : exec (ext_decode_compressed sth61) WkEntryEff.dstateM =
    some (.C_ADDIW (si61, .Regidx tiA5), WkEntryEff.dstateM) :=
  WkStartAux.decRef _ _ WkStartAux.walk61M WkStartAux.walk61S
/-- Rocq `stgood_61`. -/
theorem stgood61 : goodb0 WkEntryEff.dM (ext_decode_compressed sth61) WkEntryEff.dstateM = true := by
  decide +kernel
/-- Rocq `stlpad_61`. -/
theorem stlpad61 : is_lpad_instruction (.C_ADDIW (si61, .Regidx tiA5)) = false := by decide +kernel
/-- Rocq `stgoodexp_61`. -/
theorem stgoodexp61 : ∀ s : ExecSt, goodb0 dNone (execute (.C_ADDIW (si61, .Regidx tiA5))) s = true :=
  fun _ => rfl

/-! ### 62: c.mv tp,a5 -/

/-- Rocq `stdec_62`. -/
theorem stdec62 : exec (ext_decode_compressed sth62) WkEntryEff.dstateM =
    some (.C_MV (.Regidx stTp, .Regidx tiA5), WkEntryEff.dstateM) :=
  WkStartAux.decRef _ _ WkStartAux.walk62M WkStartAux.walk62S
/-- Rocq `stgood_62`. -/
theorem stgood62 : goodb0 WkEntryEff.dM (ext_decode_compressed sth62) WkEntryEff.dstateM = true := by
  decide +kernel
/-- Rocq `stlpad_62`. -/
theorem stlpad62 : is_lpad_instruction (.C_MV (.Regidx stTp, .Regidx tiA5)) = false := by decide +kernel
/-- Rocq `stgoodexp_62`. -/
theorem stgoodexp62 : ∀ s : ExecSt, goodb0 dNone (execute (.C_MV (.Regidx stTp, .Regidx tiA5))) s = true :=
  fun _ => rfl

/-! ### 63: mret -/

/-- Rocq `stdec_63`. -/
theorem stdec63 : exec (ext_decode stw63) WkEntryEff.dstateM =
    some (.MRET (), WkEntryEff.dstateM) :=
  WkStartAux.decRef _ _ WkStartAux.walk63M WkStartAux.walk63S
/-- Rocq `stgood_63`. -/
theorem stgood63 : goodb0 WkEntryEff.dM (ext_decode stw63) WkEntryEff.dstateM = true := by
  decide +kernel

/-! ## 4b. The RVC expansion facts -/

/-- Rocq `stexp_30`. -/
theorem stexp30 : ∀ s : ExecSt,
    exec (execute (.C_ADDI (i9, .Regidx cspRs1))) s = some (.ExecuteAs (.ITYPE (sign_extend (m := 12) i9, .Regidx cspRs1, .Regidx cspRs1, .ADDI)), s) := by
  intro s; kernel_rfl
/-- Rocq `stexp_31`. -/
theorem stexp31 : ∀ s : ExecSt,
    exec (execute (.C_SDSP (u10, .Regidx tiRa))) s = some (.ExecuteAs (.STORE (zero_extend (m := 12) (u10 +++ 0b000#3), .Regidx tiRa, .Regidx cspRs1, 8)), s) := by
  intro s; kernel_rfl
/-- Rocq `stexp_32`. -/
theorem stexp32 : ∀ s : ExecSt,
    exec (execute (.C_SDSP (u11, .Regidx tiS0))) s = some (.ExecuteAs (.STORE (zero_extend (m := 12) (u11 +++ 0b000#3), .Regidx tiS0, .Regidx cspRs1, 8)), s) := by
  intro s; kernel_rfl
/-- Rocq `stexp_33`. -/
theorem stexp33 : ∀ s : ExecSt,
    exec (execute (.C_ADDI4SPN (.Cregidx 0#3, nz12))) s = some (.ExecuteAs (.ITYPE (caddi4spnImm nz12, .Regidx cspRs1, .Regidx tiS0, .ADDI)), s) := by
  intro s; kernel_rfl
/-- Lean-only (Rocq inlines `exec_execute_C_LUI`). -/
theorem WkStartAux.stexp35 : ∀ s : ExecSt,
    exec (execute (.C_LUI (si35, .Regidx tiA4))) s = some (.ExecuteAs (.UTYPE (sign_extend (m := 20) si35, .Regidx tiA4, .LUI)), s) := by
  intro s; kernel_rfl
/-- Rocq `stexp_37`. -/
theorem stexp37 : ∀ s : ExecSt,
    exec (execute (.C_AND (.Cregidx 7#3, .Cregidx 6#3))) s = some (.ExecuteAs (.RTYPE (.Regidx tiA4, .Regidx tiA5, .Regidx tiA5, .AND)), s) := by
  intro s; kernel_rfl
/-- Rocq `stexp_38`. -/
theorem stexp38 : ∀ s : ExecSt,
    exec (execute (.C_LUI (si38, .Regidx tiA4))) s = some (.ExecuteAs (.UTYPE (sign_extend (m := 20) si38, .Regidx tiA4, .LUI)), s) := by
  intro s; kernel_rfl
/-- Rocq `stexp_40`. -/
theorem stexp40 : ∀ s : ExecSt,
    exec (execute (.C_OR (.Cregidx 7#3, .Cregidx 6#3))) s = some (.ExecuteAs (.RTYPE (.Regidx tiA4, .Regidx tiA5, .Regidx tiA5, .OR)), s) := by
  intro s; kernel_rfl
/-- Rocq `stexp_45`. -/
theorem stexp45 : ∀ s : ExecSt,
    exec (execute (.C_LI (si45, .Regidx tiA5))) s = some (.ExecuteAs (.ITYPE (sign_extend (m := 12) si45, .Regidx cliRs1, .Regidx tiA5, .ADDI)), s) := by
  intro s; kernel_rfl
/-- Rocq `stexp_47`. -/
theorem stexp47 : ∀ s : ExecSt,
    exec (execute (.C_LUI (si47, .Regidx tiA5))) s = some (.ExecuteAs (.UTYPE (sign_extend (m := 20) si47, .Regidx tiA5, .LUI)), s) := by
  intro s; kernel_rfl
/-- Rocq `stexp_48`. -/
theorem stexp48 : ∀ s : ExecSt,
    exec (execute (.C_ADDI (si48, .Regidx tiA5))) s = some (.ExecuteAs (.ITYPE (sign_extend (m := 12) si48, .Regidx tiA5, .Regidx tiA5, .ADDI)), s) := by
  intro s; kernel_rfl
/-- Rocq `stexp_54`. -/
theorem stexp54 : ∀ s : ExecSt,
    exec (execute (.C_LI (si54, .Regidx tiA5))) s = some (.ExecuteAs (.ITYPE (sign_extend (m := 12) si54, .Regidx cliRs1, .Regidx tiA5, .ADDI)), s) := by
  intro s; kernel_rfl
/-- Rocq `stexp_55`. -/
theorem stexp55 : ∀ s : ExecSt,
    exec (execute (.C_SRLI (ssh55, .Cregidx 7#3))) s = some (.ExecuteAs (.SHIFTIOP (ssh55, .Regidx tiA5, .Regidx tiA5, .SRLI)), s) := by
  intro s; kernel_rfl
/-- Rocq `stexp_57`. -/
theorem stexp57 : ∀ s : ExecSt,
    exec (execute (.C_LI (si57, .Regidx tiA5))) s = some (.ExecuteAs (.ITYPE (sign_extend (m := 12) si57, .Regidx cliRs1, .Regidx tiA5, .ADDI)), s) := by
  intro s; kernel_rfl
/-- Rocq `stexp_ae1`. -/
theorem stexpAe1 : ∀ s : ExecSt,
    exec (execute (.C_LI (saeLi, .Regidx tiA4))) s = some (.ExecuteAs (.ITYPE (sign_extend (m := 12) saeLi, .Regidx cliRs1, .Regidx tiA4, .ADDI)), s) := by
  intro s; kernel_rfl
/-- Rocq `stexp_ae2`. -/
theorem stexpAe2 : ∀ s : ExecSt,
    exec (execute (.C_SLLI (saeSlli, .Regidx tiA4))) s = some (.ExecuteAs (.SHIFTIOP (saeSlli, .Regidx tiA4, .Regidx tiA4, .SLLI)), s) := by
  intro s; kernel_rfl
/-- Rocq `stexp_ae3`. -/
theorem stexpAe3 : ∀ s : ExecSt,
    exec (execute (.C_OR (.Cregidx 7#3, .Cregidx 6#3))) s = some (.ExecuteAs (.RTYPE (.Regidx tiA4, .Regidx tiA5, .Regidx tiA5, .OR)), s) := by
  intro s; kernel_rfl
/-- Rocq `stexp_61`. -/
theorem stexp61 : ∀ s : ExecSt,
    exec (execute (.C_ADDIW (si61, .Regidx tiA5))) s = some (.ExecuteAs (.ADDIW (sign_extend (m := 12) si61, .Regidx tiA5, .Regidx tiA5)), s) := by
  intro s; kernel_rfl
/-- Rocq `stexp_62`. -/
theorem stexp62 : ∀ s : ExecSt,
    exec (execute (.C_MV (.Regidx stTp, .Regidx tiA5))) s = some (.ExecuteAs (.RTYPE (.Regidx tiA5, .Regidx cliRs1, .Regidx stTp, .ADD)), s) := by
  intro s; kernel_rfl

/-! ## 5. The per-instruction tokens (`winstrM`) -- this file's `CodeStart.sti_*` analogue -/

section tokens
variable {GF : BundledGFunctors} [WeakGS GF]

/-- Rocq `wsti_30`: c.addi sp,-16 (start + 0x0). -/
theorem wsti30 (kbs : GMapF PAddr (BitVec 8)) : wkbCovers kbs →
    wkernelText (GF := GF) kbs ⊢ winstrM (GF := GF) stPc30 true
      (.ITYPE (sign_extend (m := 12) i9, .Regidx cspRs1, .Regidx cspRs1, .ADDI)) := fun hcov =>
  WkStartAux.tokRvc kbs hcov ((KernelSyms.«start» : Int) + 0x0) stw30 sth30 (.C_ADDI (i9, .Regidx cspRs1)) _
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) stlpad30 WkStartAux.walk30M WkStartAux.walk30S
    stgood30 stdec30 stgoodexp30 stexp30 stkb30

/-- Rocq `wsti_31`: c.sdsp ra,8(sp) (start + 0x2). -/
theorem wsti31 (kbs : GMapF PAddr (BitVec 8)) : wkbCovers kbs →
    wkernelText (GF := GF) kbs ⊢ winstrM (GF := GF) stPc31 true
      (.STORE (zero_extend (m := 12) (u10 +++ 0b000#3), .Regidx tiRa, .Regidx cspRs1, 8)) := fun hcov =>
  WkStartAux.tokRvc kbs hcov ((KernelSyms.«start» : Int) + 0x2) stw31 sth31 (.C_SDSP (u10, .Regidx tiRa)) _
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) stlpad31 WkStartAux.walk31M WkStartAux.walk31S
    stgood31 stdec31 stgoodexp31 stexp31 stkb31

/-- Rocq `wsti_32`: c.sdsp s0,0(sp) (start + 0x4). -/
theorem wsti32 (kbs : GMapF PAddr (BitVec 8)) : wkbCovers kbs →
    wkernelText (GF := GF) kbs ⊢ winstrM (GF := GF) stPc32 true
      (.STORE (zero_extend (m := 12) (u11 +++ 0b000#3), .Regidx tiS0, .Regidx cspRs1, 8)) := fun hcov =>
  WkStartAux.tokRvc kbs hcov ((KernelSyms.«start» : Int) + 0x4) stw32 sth32 (.C_SDSP (u11, .Regidx tiS0)) _
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) stlpad32 WkStartAux.walk32M WkStartAux.walk32S
    stgood32 stdec32 stgoodexp32 stexp32 stkb32

/-- Rocq `wsti_33`: c.addi4spn s0,sp,16 (start + 0x6). -/
theorem wsti33 (kbs : GMapF PAddr (BitVec 8)) : wkbCovers kbs →
    wkernelText (GF := GF) kbs ⊢ winstrM (GF := GF) stPc33 true
      (.ITYPE (caddi4spnImm nz12, .Regidx cspRs1, .Regidx tiS0, .ADDI)) := fun hcov =>
  WkStartAux.tokRvc kbs hcov ((KernelSyms.«start» : Int) + 0x6) stw33 sth33 (.C_ADDI4SPN (.Cregidx 0#3, nz12)) _
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) stlpad33 WkStartAux.walk33M WkStartAux.walk33S
    stgood33 stdec33 stgoodexp33 stexp33 stkb33

/-- Rocq `wsti_34`: csrr a5,mstatus (start + 0x8). -/
theorem wsti34 (kbs : GMapF PAddr (BitVec 8)) : wkbCovers kbs →
    wkernelText (GF := GF) kbs ⊢ winstrM (GF := GF) stPc34 false
      (.CSRReg (0x300#12, zreg, .Regidx tiA5, .CSRRS)) := fun hcov =>
  WkStartAux.tokBase kbs hcov ((KernelSyms.«start» : Int) + 0x8) stw34 _
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) WkStartAux.walk34M WkStartAux.walk34S stgood34 stdec34 stkb34

/-- Rocq `wsti_35`: c.lui a4,0xffffe (start + 0xc). -/
theorem wsti35 (kbs : GMapF PAddr (BitVec 8)) : wkbCovers kbs →
    wkernelText (GF := GF) kbs ⊢ winstrM (GF := GF) stPc35 true
      (.UTYPE (sign_extend (m := 20) si35, .Regidx tiA4, .LUI)) := fun hcov =>
  WkStartAux.tokRvc kbs hcov ((KernelSyms.«start» : Int) + 0xc) stw35 sth35 (.C_LUI (si35, .Regidx tiA4)) _
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) stlpad35 WkStartAux.walk35M WkStartAux.walk35S
    stgood35 stdec35 stgoodexp35 WkStartAux.stexp35 stkb35

/-- Rocq `wsti_36`: addi a4,a4,2047 (start + 0xe). -/
theorem wsti36 (kbs : GMapF PAddr (BitVec 8)) : wkbCovers kbs →
    wkernelText (GF := GF) kbs ⊢ winstrM (GF := GF) stPc36 false
      (.ITYPE (si36, .Regidx tiA4, .Regidx tiA4, .ADDI)) := fun hcov =>
  WkStartAux.tokBase kbs hcov ((KernelSyms.«start» : Int) + 0xe) stw36 _
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) WkStartAux.walk36M WkStartAux.walk36S stgood36 stdec36 stkb36

/-- Rocq `wsti_37`: c.and a5,a4 (start + 0x12). -/
theorem wsti37 (kbs : GMapF PAddr (BitVec 8)) : wkbCovers kbs →
    wkernelText (GF := GF) kbs ⊢ winstrM (GF := GF) stPc37 true
      (.RTYPE (.Regidx tiA4, .Regidx tiA5, .Regidx tiA5, .AND)) := fun hcov =>
  WkStartAux.tokRvc kbs hcov ((KernelSyms.«start» : Int) + 0x12) stw37 sth37 (.C_AND (.Cregidx 7#3, .Cregidx 6#3)) _
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) stlpad37 WkStartAux.walk37M WkStartAux.walk37S
    stgood37 stdec37 stgoodexp37 stexp37 stkb37

/-- Rocq `wsti_38`: c.lui a4,1 (start + 0x14). -/
theorem wsti38 (kbs : GMapF PAddr (BitVec 8)) : wkbCovers kbs →
    wkernelText (GF := GF) kbs ⊢ winstrM (GF := GF) stPc38 true
      (.UTYPE (sign_extend (m := 20) si38, .Regidx tiA4, .LUI)) := fun hcov =>
  WkStartAux.tokRvc kbs hcov ((KernelSyms.«start» : Int) + 0x14) stw38 sth38 (.C_LUI (si38, .Regidx tiA4)) _
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) stlpad38 WkStartAux.walk38M WkStartAux.walk38S
    stgood38 stdec38 stgoodexp38 stexp38 stkb38

/-- Rocq `wsti_39`: addi a4,a4,-2048 (start + 0x16). -/
theorem wsti39 (kbs : GMapF PAddr (BitVec 8)) : wkbCovers kbs →
    wkernelText (GF := GF) kbs ⊢ winstrM (GF := GF) stPc39 false
      (.ITYPE (si39, .Regidx tiA4, .Regidx tiA4, .ADDI)) := fun hcov =>
  WkStartAux.tokBase kbs hcov ((KernelSyms.«start» : Int) + 0x16) stw39 _
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) WkStartAux.walk39M WkStartAux.walk39S stgood39 stdec39 stkb39

/-- Rocq `wsti_40`: c.or a5,a4 (start + 0x1a). -/
theorem wsti40 (kbs : GMapF PAddr (BitVec 8)) : wkbCovers kbs →
    wkernelText (GF := GF) kbs ⊢ winstrM (GF := GF) stPc40 true
      (.RTYPE (.Regidx tiA4, .Regidx tiA5, .Regidx tiA5, .OR)) := fun hcov =>
  WkStartAux.tokRvc kbs hcov ((KernelSyms.«start» : Int) + 0x1a) stw40 sth40 (.C_OR (.Cregidx 7#3, .Cregidx 6#3)) _
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) stlpad40 WkStartAux.walk40M WkStartAux.walk40S
    stgood40 stdec40 stgoodexp40 stexp40 stkb40

/-- Rocq `wsti_41`: csrw mstatus,a5 (start + 0x1c). -/
theorem wsti41 (kbs : GMapF PAddr (BitVec 8)) : wkbCovers kbs →
    wkernelText (GF := GF) kbs ⊢ winstrM (GF := GF) stPc41 false
      (.CSRReg (0x300#12, .Regidx tiA5, zreg, .CSRRW)) := fun hcov =>
  WkStartAux.tokBase kbs hcov ((KernelSyms.«start» : Int) + 0x1c) stw41 _
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) WkStartAux.walk41M WkStartAux.walk41S stgood41 stdec41 stkb41

/-- Rocq `wsti_42`: auipc a5,1 (start + 0x20). -/
theorem wsti42 (kbs : GMapF PAddr (BitVec 8)) : wkbCovers kbs →
    wkernelText (GF := GF) kbs ⊢ winstrM (GF := GF) stPc42 false
      (.UTYPE (si42, .Regidx tiA5, .AUIPC)) := fun hcov =>
  WkStartAux.tokBase kbs hcov ((KernelSyms.«start» : Int) + 0x20) stw42 _
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) WkStartAux.walk42M WkStartAux.walk42S stgood42 stdec42 stkb42

/-- Rocq `wsti_43`: addi a5,a5,-426 (drift: Rocq -506) (start + 0x24). -/
theorem wsti43 (kbs : GMapF PAddr (BitVec 8)) : wkbCovers kbs →
    wkernelText (GF := GF) kbs ⊢ winstrM (GF := GF) stPc43 false
      (.ITYPE (si43, .Regidx tiA5, .Regidx tiA5, .ADDI)) := fun hcov =>
  WkStartAux.tokBase kbs hcov ((KernelSyms.«start» : Int) + 0x24) stw43 _
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) WkStartAux.walk43M WkStartAux.walk43S stgood43 stdec43 stkb43

/-- Rocq `wsti_44`: csrw mepc,a5 (start + 0x28). -/
theorem wsti44 (kbs : GMapF PAddr (BitVec 8)) : wkbCovers kbs →
    wkernelText (GF := GF) kbs ⊢ winstrM (GF := GF) stPc44 false
      (.CSRReg (0x341#12, .Regidx tiA5, zreg, .CSRRW)) := fun hcov =>
  WkStartAux.tokBase kbs hcov ((KernelSyms.«start» : Int) + 0x28) stw44 _
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) WkStartAux.walk44M WkStartAux.walk44S stgood44 stdec44 stkb44

/-- Rocq `wsti_45`: c.li a5,0 (start + 0x2c). -/
theorem wsti45 (kbs : GMapF PAddr (BitVec 8)) : wkbCovers kbs →
    wkernelText (GF := GF) kbs ⊢ winstrM (GF := GF) stPc45 true
      (.ITYPE (sign_extend (m := 12) si45, .Regidx cliRs1, .Regidx tiA5, .ADDI)) := fun hcov =>
  WkStartAux.tokRvc kbs hcov ((KernelSyms.«start» : Int) + 0x2c) stw45 sth45 (.C_LI (si45, .Regidx tiA5)) _
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) stlpad45 WkStartAux.walk45M WkStartAux.walk45S
    stgood45 stdec45 stgoodexp45 stexp45 stkb45

/-- Rocq `wsti_46`: csrw satp,a5 (start + 0x2e). -/
theorem wsti46 (kbs : GMapF PAddr (BitVec 8)) : wkbCovers kbs →
    wkernelText (GF := GF) kbs ⊢ winstrM (GF := GF) stPc46 false
      (.CSRReg (0x180#12, .Regidx tiA5, zreg, .CSRRW)) := fun hcov =>
  WkStartAux.tokBase kbs hcov ((KernelSyms.«start» : Int) + 0x2e) stw46 _
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) WkStartAux.walk46M WkStartAux.walk46S stgood46 stdec46 stkb46

/-- Rocq `wsti_47`: c.lui a5,0x10 (start + 0x32). -/
theorem wsti47 (kbs : GMapF PAddr (BitVec 8)) : wkbCovers kbs →
    wkernelText (GF := GF) kbs ⊢ winstrM (GF := GF) stPc47 true
      (.UTYPE (sign_extend (m := 20) si47, .Regidx tiA5, .LUI)) := fun hcov =>
  WkStartAux.tokRvc kbs hcov ((KernelSyms.«start» : Int) + 0x32) stw47 sth47 (.C_LUI (si47, .Regidx tiA5)) _
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) stlpad47 WkStartAux.walk47M WkStartAux.walk47S
    stgood47 stdec47 stgoodexp47 stexp47 stkb47

/-- Rocq `wsti_48`: c.addi a5,-1 (start + 0x34). -/
theorem wsti48 (kbs : GMapF PAddr (BitVec 8)) : wkbCovers kbs →
    wkernelText (GF := GF) kbs ⊢ winstrM (GF := GF) stPc48 true
      (.ITYPE (sign_extend (m := 12) si48, .Regidx tiA5, .Regidx tiA5, .ADDI)) := fun hcov =>
  WkStartAux.tokRvc kbs hcov ((KernelSyms.«start» : Int) + 0x34) stw48 sth48 (.C_ADDI (si48, .Regidx tiA5)) _
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) stlpad48 WkStartAux.walk48M WkStartAux.walk48S
    stgood48 stdec48 stgoodexp48 stexp48 stkb48

/-- Rocq `wsti_49`: csrw medeleg,a5 (start + 0x36). -/
theorem wsti49 (kbs : GMapF PAddr (BitVec 8)) : wkbCovers kbs →
    wkernelText (GF := GF) kbs ⊢ winstrM (GF := GF) stPc49 false
      (.CSRReg (0x302#12, .Regidx tiA5, zreg, .CSRRW)) := fun hcov =>
  WkStartAux.tokBase kbs hcov ((KernelSyms.«start» : Int) + 0x36) stw49 _
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) WkStartAux.walk49M WkStartAux.walk49S stgood49 stdec49 stkb49

/-- Rocq `wsti_50`: csrw mideleg,a5 (start + 0x3a). -/
theorem wsti50 (kbs : GMapF PAddr (BitVec 8)) : wkbCovers kbs →
    wkernelText (GF := GF) kbs ⊢ winstrM (GF := GF) stPc50 false
      (.CSRReg (0x303#12, .Regidx tiA5, zreg, .CSRRW)) := fun hcov =>
  WkStartAux.tokBase kbs hcov ((KernelSyms.«start» : Int) + 0x3a) stw50 _
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) WkStartAux.walk50M WkStartAux.walk50S stgood50 stdec50 stkb50

/-- Rocq `wsti_51`: csrr a5,sie (start + 0x3e). -/
theorem wsti51 (kbs : GMapF PAddr (BitVec 8)) : wkbCovers kbs →
    wkernelText (GF := GF) kbs ⊢ winstrM (GF := GF) stPc51 false
      (.CSRReg (0x104#12, zreg, .Regidx tiA5, .CSRRS)) := fun hcov =>
  WkStartAux.tokBase kbs hcov ((KernelSyms.«start» : Int) + 0x3e) stw51 _
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) WkStartAux.walk51M WkStartAux.walk51S stgood51 stdec51 stkb51

/-- Rocq `wsti_52`: ori a5,a5,544 (start + 0x42). -/
theorem wsti52 (kbs : GMapF PAddr (BitVec 8)) : wkbCovers kbs →
    wkernelText (GF := GF) kbs ⊢ winstrM (GF := GF) stPc52 false
      (.ITYPE (si52, .Regidx tiA5, .Regidx tiA5, .ORI)) := fun hcov =>
  WkStartAux.tokBase kbs hcov ((KernelSyms.«start» : Int) + 0x42) stw52 _
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) WkStartAux.walk52M WkStartAux.walk52S stgood52 stdec52 stkb52

/-- Rocq `wsti_53`: csrw sie,a5 (start + 0x46). -/
theorem wsti53 (kbs : GMapF PAddr (BitVec 8)) : wkbCovers kbs →
    wkernelText (GF := GF) kbs ⊢ winstrM (GF := GF) stPc53 false
      (.CSRReg (0x104#12, .Regidx tiA5, zreg, .CSRRW)) := fun hcov =>
  WkStartAux.tokBase kbs hcov ((KernelSyms.«start» : Int) + 0x46) stw53 _
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) WkStartAux.walk53M WkStartAux.walk53S stgood53 stdec53 stkb53

/-- Rocq `wsti_54`: c.li a5,-1 (start + 0x4a). -/
theorem wsti54 (kbs : GMapF PAddr (BitVec 8)) : wkbCovers kbs →
    wkernelText (GF := GF) kbs ⊢ winstrM (GF := GF) stPc54 true
      (.ITYPE (sign_extend (m := 12) si54, .Regidx cliRs1, .Regidx tiA5, .ADDI)) := fun hcov =>
  WkStartAux.tokRvc kbs hcov ((KernelSyms.«start» : Int) + 0x4a) stw54 sth54 (.C_LI (si54, .Regidx tiA5)) _
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) stlpad54 WkStartAux.walk54M WkStartAux.walk54S
    stgood54 stdec54 stgoodexp54 stexp54 stkb54

/-- Rocq `wsti_55`: c.srli a5,10 (start + 0x4c). -/
theorem wsti55 (kbs : GMapF PAddr (BitVec 8)) : wkbCovers kbs →
    wkernelText (GF := GF) kbs ⊢ winstrM (GF := GF) stPc55 true
      (.SHIFTIOP (ssh55, .Regidx tiA5, .Regidx tiA5, .SRLI)) := fun hcov =>
  WkStartAux.tokRvc kbs hcov ((KernelSyms.«start» : Int) + 0x4c) stw55 sth55 (.C_SRLI (ssh55, .Cregidx 7#3)) _
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) stlpad55 WkStartAux.walk55M WkStartAux.walk55S
    stgood55 stdec55 stgoodexp55 stexp55 stkb55

/-- Rocq `wsti_56`: csrw pmpaddr0,a5 (start + 0x4e). -/
theorem wsti56 (kbs : GMapF PAddr (BitVec 8)) : wkbCovers kbs →
    wkernelText (GF := GF) kbs ⊢ winstrM (GF := GF) stPc56 false
      (.CSRReg (0x3B0#12, .Regidx tiA5, zreg, .CSRRW)) := fun hcov =>
  WkStartAux.tokBase kbs hcov ((KernelSyms.«start» : Int) + 0x4e) stw56 _
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) WkStartAux.walk56M WkStartAux.walk56S stgood56 stdec56 stkb56

/-- Rocq `wsti_57`: c.li a5,15 (start + 0x52). -/
theorem wsti57 (kbs : GMapF PAddr (BitVec 8)) : wkbCovers kbs →
    wkernelText (GF := GF) kbs ⊢ winstrM (GF := GF) stPc57 true
      (.ITYPE (sign_extend (m := 12) si57, .Regidx cliRs1, .Regidx tiA5, .ADDI)) := fun hcov =>
  WkStartAux.tokRvc kbs hcov ((KernelSyms.«start» : Int) + 0x52) stw57 sth57 (.C_LI (si57, .Regidx tiA5)) _
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) stlpad57 WkStartAux.walk57M WkStartAux.walk57S
    stgood57 stdec57 stgoodexp57 stexp57 stkb57

/-- Rocq `wsti_58`: csrw pmpcfg0,a5 (start + 0x54). -/
theorem wsti58 (kbs : GMapF PAddr (BitVec 8)) : wkbCovers kbs →
    wkernelText (GF := GF) kbs ⊢ winstrM (GF := GF) stPc58 false
      (.CSRReg (0x3A0#12, .Regidx tiA5, zreg, .CSRRW)) := fun hcov =>
  WkStartAux.tokBase kbs hcov ((KernelSyms.«start» : Int) + 0x54) stw58 _
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) WkStartAux.walk58M WkStartAux.walk58S stgood58 stdec58 stkb58

/-- Rocq `wsti_ae0`: csrr a5,menvcfg (start + 0x58). -/
theorem wstiAe0 (kbs : GMapF PAddr (BitVec 8)) : wkbCovers kbs →
    wkernelText (GF := GF) kbs ⊢ winstrM (GF := GF) stPcAe0 false
      (.CSRReg (0x30A#12, zreg, .Regidx tiA5, .CSRRS)) := fun hcov =>
  WkStartAux.tokBase kbs hcov ((KernelSyms.«start» : Int) + 0x58) stwAe0 _
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) WkStartAux.walkAe0M WkStartAux.walkAe0S stgoodAe0 stdecAe0 stkbAe0

/-- Rocq `wsti_ae1`: c.li a4,1 (start + 0x5c). -/
theorem wstiAe1 (kbs : GMapF PAddr (BitVec 8)) : wkbCovers kbs →
    wkernelText (GF := GF) kbs ⊢ winstrM (GF := GF) stPcAe1 true
      (.ITYPE (sign_extend (m := 12) saeLi, .Regidx cliRs1, .Regidx tiA4, .ADDI)) := fun hcov =>
  WkStartAux.tokRvc kbs hcov ((KernelSyms.«start» : Int) + 0x5c) stwAe1 sthAe1 (.C_LI (saeLi, .Regidx tiA4)) _
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) stlpadAe1 WkStartAux.walkAe1M WkStartAux.walkAe1S
    stgoodAe1 stdecAe1 stgoodexpAe1 stexpAe1 stkbAe1

/-- Rocq `wsti_ae2`: c.slli a4,0x3d (start + 0x5e). -/
theorem wstiAe2 (kbs : GMapF PAddr (BitVec 8)) : wkbCovers kbs →
    wkernelText (GF := GF) kbs ⊢ winstrM (GF := GF) stPcAe2 true
      (.SHIFTIOP (saeSlli, .Regidx tiA4, .Regidx tiA4, .SLLI)) := fun hcov =>
  WkStartAux.tokRvc kbs hcov ((KernelSyms.«start» : Int) + 0x5e) stwAe2 sthAe2 (.C_SLLI (saeSlli, .Regidx tiA4)) _
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) stlpadAe2 WkStartAux.walkAe2M WkStartAux.walkAe2S
    stgoodAe2 stdecAe2 stgoodexpAe2 stexpAe2 stkbAe2

/-- Rocq `wsti_ae3`: c.or a5,a4 (start + 0x60). -/
theorem wstiAe3 (kbs : GMapF PAddr (BitVec 8)) : wkbCovers kbs →
    wkernelText (GF := GF) kbs ⊢ winstrM (GF := GF) stPcAe3 true
      (.RTYPE (.Regidx tiA4, .Regidx tiA5, .Regidx tiA5, .OR)) := fun hcov =>
  WkStartAux.tokRvc kbs hcov ((KernelSyms.«start» : Int) + 0x60) stwAe3 sthAe3 (.C_OR (.Cregidx 7#3, .Cregidx 6#3)) _
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) stlpadAe3 WkStartAux.walkAe3M WkStartAux.walkAe3S
    stgoodAe3 stdecAe3 stgoodexpAe3 stexpAe3 stkbAe3

/-- Rocq `wsti_ae4`: csrw menvcfg,a5 (start + 0x62). -/
theorem wstiAe4 (kbs : GMapF PAddr (BitVec 8)) : wkbCovers kbs →
    wkernelText (GF := GF) kbs ⊢ winstrM (GF := GF) stPcAe4 false
      (.CSRReg (0x30A#12, .Regidx tiA5, zreg, .CSRRW)) := fun hcov =>
  WkStartAux.tokBase kbs hcov ((KernelSyms.«start» : Int) + 0x62) stwAe4 _
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) WkStartAux.walkAe4M WkStartAux.walkAe4S stgoodAe4 stdecAe4 stkbAe4

/-- Rocq `wsti_59`: jal ra,timerinit (start + 0x66). -/
theorem wsti59 (kbs : GMapF PAddr (BitVec 8)) : wkbCovers kbs →
    wkernelText (GF := GF) kbs ⊢ winstrM (GF := GF) stPc59 false
      (.JAL (sjimm59, .Regidx tiRa)) := fun hcov =>
  WkStartAux.tokBase kbs hcov ((KernelSyms.«start» : Int) + 0x66) stw59 _
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) WkStartAux.walk59M WkStartAux.walk59S stgood59 stdec59 stkb59

/-- Rocq `wsti_60`: csrr a5,mhartid (start + 0x6a). -/
theorem wsti60 (kbs : GMapF PAddr (BitVec 8)) : wkbCovers kbs →
    wkernelText (GF := GF) kbs ⊢ winstrM (GF := GF) stPc60 false
      (.CSRReg (0xF14#12, zreg, .Regidx tiA5, .CSRRS)) := fun hcov =>
  WkStartAux.tokBase kbs hcov ((KernelSyms.«start» : Int) + 0x6a) stw60 _
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) WkStartAux.walk60M WkStartAux.walk60S stgood60 stdec60 stkb60

/-- Rocq `wsti_61`: c.addiw a5,0 (sext.w) (start + 0x6e). -/
theorem wsti61 (kbs : GMapF PAddr (BitVec 8)) : wkbCovers kbs →
    wkernelText (GF := GF) kbs ⊢ winstrM (GF := GF) stPc61 true
      (.ADDIW (sign_extend (m := 12) si61, .Regidx tiA5, .Regidx tiA5)) := fun hcov =>
  WkStartAux.tokRvc kbs hcov ((KernelSyms.«start» : Int) + 0x6e) stw61 sth61 (.C_ADDIW (si61, .Regidx tiA5)) _
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) stlpad61 WkStartAux.walk61M WkStartAux.walk61S
    stgood61 stdec61 stgoodexp61 stexp61 stkb61

/-- Rocq `wsti_62`: c.mv tp,a5 (start + 0x70). -/
theorem wsti62 (kbs : GMapF PAddr (BitVec 8)) : wkbCovers kbs →
    wkernelText (GF := GF) kbs ⊢ winstrM (GF := GF) stPc62 true
      (.RTYPE (.Regidx tiA5, .Regidx cliRs1, .Regidx stTp, .ADD)) := fun hcov =>
  WkStartAux.tokRvc kbs hcov ((KernelSyms.«start» : Int) + 0x70) stw62 sth62 (.C_MV (.Regidx stTp, .Regidx tiA5)) _
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) stlpad62 WkStartAux.walk62M WkStartAux.walk62S
    stgood62 stdec62 stgoodexp62 stexp62 stkb62

/-- Rocq `wsti_63`: mret (start + 0x72). -/
theorem wsti63 (kbs : GMapF PAddr (BitVec 8)) : wkbCovers kbs →
    wkernelText (GF := GF) kbs ⊢ winstrM (GF := GF) stPc63 false
      (.MRET ()) := fun hcov =>
  WkStartAux.tokBase kbs hcov ((KernelSyms.«start» : Int) + 0x72) stw63 _
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) WkStartAux.walk63M WkStartAux.walk63S stgood63 stdec63 stkb63

end tokens

end Weak
