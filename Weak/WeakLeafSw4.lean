/-
Weak: **the `sw`-class 4-byte STORE leaf** (M4 batch 2): from the M-mode
config bundle, the PC cell, the instruction bytes and the OWNED four-byte
window at the effective address to `WWP Loop`.

Rocq: `iris/WeakLeafSw4.v` @ xxvzwolszwmp.

The Rocq header, in substance.  The width-4 replay of `WeakLeafSd8` over
`WeakLeafWin`'s 4+4 window `wwin pc ea 4`:
* THE CERTIFICATE IS FREE: `WeakFetchEff.wcertStoreBase4` is this leaf's
  certificate (Rocq §1 is empty).
* THE STORED VALUE IS A TRUNCATION: the store writes the low word
  `Sail.BitVec.extractLsb rs2v 31 0`, tied to the leaf's `vw` by a premise; the
  window comes back as `wpt4Own cpu ea vw`.
* THE Q HALF: `wpt4OwnAtElems` → `wlat4StorePrimOwn` (retarget at
  `wQStore`'s message) → `wlogUpdate` → `wlat4OwnWpt4Own` with `wQStore`'s
  view conjunct as the floor (FULL fraction forced).
* THE RELEASE DEPOSIT: `vwpHold R ws` in, `R.monPred_at (viewScl T)` out at
  `T = σ.wmLog.length + 1`.
* Reused, not cloned: the window kit of `WeakLeafWin` (`wwin`, `wwinNonzero`,
  `wwinPinned`, `wwinConfText`, `wwinWdom`, `setLookupNe`/`leaf_peel`,
  `storeRegsFacts`, `wpt4OwnAlign`) and `WeakFetchEff.execEffWithinHtifWFalse`.
Every pure / geometry side condition is a premise.

Sections: §2c `execEffSw4At` (the `execute` fact over an arbitrary state
under the funnel's two pre-writes); §2d `wPEffSw4` (the certificate's
precondition); §3 `wwpSw4Leaf` (the leaf).

**Deviations from Rocq.**
1. NAMES / VOCABULARY: the tree's camelCase (map below), as
   `Weak/WeakLeafWin.lean` / `Weak/WeakFetchEff.lean` deviation 1
   (`register_lookup r s.(sregs)` ↦ `s.regs r`, `eq_vec x 'b"1"` ↦ `(x == 1#1)`,
   `subrange_vec_dec v 31 0` ↦ `Sail.BitVec.extractLsb v 31 0`, `add_vec_int` ↦
   `Sail.BitVec.addInt`, `write_bytes` ↦ `bmWrite`, `RETIRE_SUCCESS` ↦
   `RETIRE_SUCCESS`, `mword n`/`bv n` ↦ `BitVec n`).  Rocq's GPR read
   `if uint rs =? 0 then zero_reg else register_lookup (R_bitvector_64 …)` is
   `s.gpr rs` (the ExecSC convention); at a `Wmstate` it is
   `(wflatSt σ).gpr rs`.
2. RAM / PMA / PMP (WeakFunnel deviation 2): `∀ j < 4, addr_is_ram (pa_add ea j)`
   ↦ `inRam ea 4`; `pma_allows_all` ↦ `pma_regions = bootPMA` (the region is
   `ramRegion`, `matching_pma_ram`); `pmp_all_off` ↦ `pmpAllOff`
   (`pmp_all_off_allows_all` is `(h i).2`).  The CLINT / SIG / device side
   conditions are discharged from `inRam` (`within_clint_ram`, `devAddrRam`).
3. `exec_eff_sw4_at`: the result state `MState (sregs s) (write_bytes s0.(mem)
   ea 4 vw) s0.(mdev)` is `s.setMem (bmWrite s0.mem ea 4 vw)` (`s` the
   pre-written state; equal by conversion).
4. O2 (`Weak/WeakFetchEff.lean` deviation 2): the fetch element is
   `.WEread WeakFetchEff.wakIfetch pc 4` (Rocq `WEread wak_plain pc 4`);
   `wPEffSw4` discharges `wPEffOfLeafBase`'s extra `fetchPin` premise from the
   text pin (`winstrTextPinned`, `fetchPinOfText`, `fetchInWindowStore`,
   `fetchFreshStore`).
5. THE CONFIG INTERFACE (owner decision Q3, WeakFunnel deviation 7): Rocq
   `mmode_config (DfracOwn q)` ∗ `pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0` ↦
   `mConf cpu (DFrac.own q) c` ∗ `clockCells cpu`, with `pmpcfg0 := c.pmpcfg`
   and the extra premise `MConf.mok c`; the funnel is `wwpInstr`, whose callback
   also threads `mtime`/`mip` (passed back unchanged).  Rocq's `gen_id = 0` /
   `cpu_id` are the explicit `gen` / `cpu`; `WWP Loop` ↦
   `wwpTriv ⊤ (WExpr.loop gen cpu)`; `pc_is` ↦ `pcIs cpu`; `hart_ws` ↦ `hartWs`.
6. GPR CELLS: Rocq `R_bitvector_64 (gpr_of_Z (uint rs)) ↦ᵣ v` (with `uint rs ≠ 0`)
   ↦ `gpr cpu rs (DFrac.own 1) v` (with `rs.toNat ≠ 0`); the read is the
   Lean-only `WeakLeafLw4.gprValid` (imported).
7. The decode premise's `register_lookup misa = MISA_C` / `decode_fetch` /
   `priv_mSU` / `cfg_ok` ↦ `misaC` / `decodeFetch` / `privMSU` / `cfgOk`
   (WeakFunnel §0); `regstate` ↦ `RegFile`, `mseccfg = mword_of_int 0` ↦
   `= 0#64`.  `wP_eff_sw4`'s `vwp_hold … (wm_ws σ)` is at `σ.wmWs`.
8. Rocq §4's `Print Assumptions` commands are not declarations.

**Rocq → Lean name map.**  `exec_eff_sw4_at` `execEffSw4At`, `wP_eff_sw4`
`wPEffSw4`, `wwp_sw4_leaf` `wwpSw4Leaf`.  Lean-only (file-qualified):
`WeakLeafSw4.uxaXgetSetNonGpr`, `WeakLeafSw4.gprPreWrites`,
`WeakLeafSw4.ramRegionWrite`, `WeakLeafSw4.execEffWithinSigRam`.  Reused from
`Weak/WeakLeafLw4.lean`: `WeakLeafLw4.gprValid`, `WeakLeafLw4.gprSetNe`,
`WeakLeafLw4.winstrBytesNotRVC`, `WeakLeafLw4.keepPure2`.

**Dropped:** nothing (3 Rocq `Lemma`s; Lean 3 theorems + 4 Lean-only).
-/
import Weak.WeakLeafWin
import Weak.WeakLeafLw4
import Weak.WeakLeafBase4
import Weak.WeakStore
import MachCSL.Gpr

namespace Weak

open Iris Iris.BI Iris.BI.MonPred Iris.ProofMode Iris.Std
open MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D LeanRV64D.Functions

/-! ## 2c. THE SECOND INSTANTIATION: the `execute` fact under the pre-writes -/

/-- Lean-only: a write of a non-GPR register leaves every GPR read alone. -/
theorem WeakLeafSw4.uxaXgetSetNonGpr (f : RegFile) (r : Register) (x : RegisterType r)
    (hr : r ∉ uxaGprs) (i : BitVec 5) : uxaXget (f.set r x) i = uxaXget f i :=
  uxaXget_congr f (f.set r x)
    (fun r' hr' => RegFile.set_other _ _ _ _ (fun h => hr (h ▸ hr'))) i

/-- Lean-only: the funnel's two pre-writes leave every GPR read alone. -/
theorem WeakLeafSw4.gprPreWrites (s0 : ExecSt) (b : Bool) (npc : BitVec 64) (i : BitVec 5) :
    ((s0.setReg .minstret_increment b).setReg .nextPC npc).gpr i = s0.gpr i := by
  show uxaXget ((s0.regs.set .minstret_increment b).set .nextPC npc) i = uxaXget s0.regs i
  rw [WeakLeafSw4.uxaXgetSetNonGpr _ _ _ (by decide),
    WeakLeafSw4.uxaXgetSetNonGpr _ _ _ (by decide)]

/-- Lean-only: the RAM region is writable. -/
theorem WeakLeafSw4.ramRegionWrite : (override_PMA ramRegion.attributes .PBMT_PMA).writable = true := by
  first
  | rfl
  | decide +kernel

/-- Lean-only: the platform has no SIG window. -/
theorem WeakLeafSw4.execEffWithinSigRam (a : BitVec 64) (w : Nat) (s : ExecSt) :
    execEff (within_sig (.Physaddr a) w) s = some (false, s, []) := by
  first
  | rfl
  | (simp only [within_sig, plat_have_sig, Functions.not]; rfl)

/-- Rocq `exec_eff_sw4_at` (deviations 1–3). -/
theorem execEffSw4At (s0 : ExecSt) (b : Bool) (pc : BitVec 64) (rs1 rs2 : BitVec 5)
    (imm : BitVec 12) (ea : PAddr) (vs : BitVec 64) (vw : BitVec 32) :
    s0.regs .cur_privilege = .Machine →
    (_get_Mstatus_MPRV (s0.regs .mstatus) == 1#1) = false →
    pmm_mode_backwards (_get_Seccfg_PMM (s0.regs .mseccfg)) = .PMM_Disabled →
    pmpAllOff (s0.regs .pmpcfg_n) →
    s0.regs .pma_regions = bootPMA →
    s0.regs .htif_tohost_base = none →
    s0.gpr rs1 + sign_extend (m := 64) imm = ea →
    s0.gpr rs2 = vs →
    Sail.BitVec.extractLsb vs 31 0 = vw →
    is_aligned_paddr (.Physaddr ea) 4 = true →
    inRam ea 4 →
    execEff (execute (.STORE (imm, .Regidx rs2, .Regidx rs1, 4)))
        ((s0.setReg .minstret_increment b).setReg .nextPC (Sail.BitVec.addInt pc 4)) =
      some (.Retire_Success (),
        ((s0.setReg .minstret_increment b).setReg .nextPC (Sail.BitVec.addInt pc 4)).setMem
          (bmWrite s0.mem ea 4 vw),
        [.WEwrite wakPlain ea 4 vw]) := by
  intro lpriv lmprv lpmm lpmp lpma lhtif hea hvs hvw hal hram
  have hE : ((s0.setReg .minstret_increment b).setReg .nextPC (Sail.BitVec.addInt pc 4)).gpr rs1 +
      sign_extend (m := 64) imm = ea := by
    rw [WeakLeafSw4.gprPreWrites]; exact hea
  have hV : (Sail.BitVec.extractLsb
      (((s0.setReg .minstret_increment b).setReg .nextPC (Sail.BitVec.addInt pc 4)).gpr rs2) 31 0 :
        BitVec 32) = vw := by
    rw [WeakLeafSw4.gprPreWrites, hvs]; exact hvw
  have key := execEffExecuteSTORE4Gpr rs2 rs1 imm ramRegion
    ((s0.setReg .minstret_increment b).setReg .nextPC (Sail.BitVec.addInt pc 4))
    (by leaf_peel .cur_privilege; exact lpriv)
    (by leaf_peel .mstatus; exact lmprv)
    (by leaf_peel .mseccfg; exact lpmm)
    (by rw [hE]; exact hal)
    (execEffPmpCheckMachineNone _ 4 _ _ (fun i => by leaf_peel .pmpcfg_n; exact (lpmp i).1))
    (by leaf_peel .pma_regions; rw [lpma, hE]; exact matching_pma_ram ea 4 hram (by decide) (by decide))
    (by rw [hE]; exact hal)
    WeakLeafSw4.ramRegionWrite
    (by rw [hE, within_clint_ram ea 4 hram]; rfl)
    (WeakLeafSw4.execEffWithinSigRam _ 4 _)
    (execEffWithinHtifWFalse _ 4 _ (by leaf_peel .htif_tohost_base; exact lhtif))
    (by rw [hE]; exact devAddrRam ea 4 hram)
  rw [hE, hV] at key
  exact key

/-! ## 2d. THE `wPEff` HALF, as a standalone lemma over the resources -/

section wPEffHalf
variable {GF : BundledGFunctors} [WeakGS GF]

/-- Rocq `wP_eff_sw4` (deviations 1, 2, 4, 7). -/
theorem wPEffSw4 (cid : Nat) (cid4 : CPU) (σ : Wmstate) (pc : BitVec 64) (w : BitVec 32)
    (rs1 rs2 : BitVec 5) (imm : BitVec 12) (ea : PAddr) (vold : BitVec 32) (vs : BitVec 64)
    (vw : BitVec 32) (D : Register → Bool) (dst : ExecSt) :
    wlogWf σ.wmLog →
    -- the M-mode config tower, at σ's own registers
    σ.wmRegs .PC = pc →
    σ.wmRegs .cur_privilege = .Machine →
    pmpAllOff (σ.wmRegs .pmpcfg_n) →
    σ.wmRegs .pma_regions = bootPMA →
    σ.wmRegs .htif_tohost_base = none →
    σ.wmRegs .hart_state = .HART_ACTIVE () →
    (_get_Misa_S (σ.wmRegs .misa) == 1#1) = true →
    (_get_Mstatus_MIE (σ.wmRegs .mstatus) == 1#1) = false →
    (_get_Mstatus_MPRV (σ.wmRegs .mstatus) == 1#1) = false →
    pmm_mode_backwards (_get_Seccfg_PMM (σ.wmRegs .mseccfg)) = .PMM_Disabled →
    (σ.wmRegs .elp == landing_pad_bits_backwards .LP_EXPECTED) = false →
    -- the instruction's pure geometry
    is_aligned_vaddr (.Virtaddr pc) 4 = true →
    isRVC (Sail.BitVec.extractLsb w 15 0) = false →
    (wflatSt σ).gpr rs1 + sign_extend (m := 64) imm = ea →
    (wflatSt σ).gpr rs2 = vs →
    Sail.BitVec.extractLsb vs 31 0 = vw →
    inRam ea 4 →
    -- the decode, exactly as the decode library states it
    (∀ r, D r = true → σ.wmRegs r = dst.regs r) →
    D .minstret_increment = false →
    goodb0 D (ext_decode w) dst = true →
    exec (ext_decode w) dst = some (.STORE (imm, .Regidx rs2, .Regidx rs1, 4), dst) →
    -- the resources
    wlatInterp (GF := GF) σ.wmImg σ.wmLog ⊢
      winstrBytes (GF := GF) pc (.F_Base w) -∗
      vwpHold (wpt4Own (GF := GF) cid4 ea vold) σ.wmWs -∗
      ⌜wPEff (some cid) ([.WEread WeakFetchEff.wakIfetch pc 4] ++ [.WEwrite wakPlain ea 4 vw]) σ⌝ := by
  intro hwf lpc lpriv lpmp lpma lhtif lhart lmisaS lmIE lmprv lpmm lelp hal4 hnotRVC hea hvs hvw hram
    hagree hDmi hgood hdec
  iintro Hlat #Hbs Hpt
  ihave %haccpc := winstrBytesAccWf pc (.F_Base w) $$ Hbs
  icases keepPure (winstrBytesLookup σ pc (.F_Base w) hwf) $$ Hlat Hbs with ⟨%hfok, Hlat, -⟩
  icases keepPure (winstrTextPinned σ pc (.F_Base w) hwf) $$ Hlat Hbs with ⟨%htp, Hlat, -⟩
  icases keepPure (wpt4OwnFlatPin cid4 σ ea vold hwf) $$ Hlat Hpt with ⟨%hfp, Hlat, Hpt⟩
  ihave %halea := wpt4OwnAlign cid4 ea vold σ.wmWs $$ Hpt
  ipureintro
  obtain ⟨haccea, hflatpin⟩ := hfp
  obtain ⟨-, ⟨-, hrampc, w', ⟨hww, -⟩, htext⟩⟩ := hfok
  subst hww
  apply wPEffOfLeafBase cid σ (wwin pc ea 4) pc w (.STORE (imm, .Regidx rs2, .Regidx rs1, 4))
    [.WEwrite wakPlain ea 4 vw] D dst hwf
    (wwinNonzero pc ea 4 (fun j hj => WeakLeafWin.inRamByte pc 4 j hrampc hj)
      (fun j hj => WeakLeafWin.inRamByte ea 4 j hram hj))
    (wwinPinned σ pc ea 4 haccpc haccea (fun j hj => (htp j hj).1) (fun j hj => (hflatpin j hj).2))
  · -- the O2 fetch pin
    refine ⟨fun ak pa n hin hif j hj => ?_, by simp [fetchFresh, weffWrites]⟩
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, _root_.or_false,
      Weff.WEread.injEq, reduceCtorEq] at hin
    obtain ⟨rfl, rfl, rfl⟩ := hin
    exact (htp j hj).2
  · exact lpc
  · exact lpriv
  · exact fun i => (lpmp i).2
  · exact lpma
  · exact lhtif
  · exact lhart
  · exact lmisaS
  · exact lmIE
  · exact lelp
  · exact hal4
  · exact hrampc
  · exact wwinConfText σ pc ea 4 w htext
  · exact hnotRVC
  · exact hagree
  · exact hDmi
  · exact hgood
  · exact hdec
  · first | rfl | decide
  · intro b
    have hfacts := storeRegsFacts ⟨σ.wmRegs, wmemRestrict σ (wwin pc ea 4), σ.wmDev⟩ b
      (BitVec.addInt pc 4)
    have hea_c : (⟨σ.wmRegs, wmemRestrict σ (wwin pc ea 4), σ.wmDev⟩ : ExecSt).gpr rs1 +
        sign_extend (m := 64) imm = ea := by
      unfold ExecSt.gpr at hea ⊢; exact hea
    have hvs_c : (⟨σ.wmRegs, wmemRestrict σ (wwin pc ea 4), σ.wmDev⟩ : ExecSt).gpr rs2 = vs := by
      unfold ExecSt.gpr at hvs ⊢; exact hvs
    have hrun := execEffSw4At ⟨σ.wmRegs, wmemRestrict σ (wwin pc ea 4), σ.wmDev⟩ b pc rs1 rs2 imm ea
      vs vw lpriv lmprv lpmm lpmp lpma lhtif hea_c hvs_c hvw halea hram
    refine ⟨_, hrun, ?_, ?_, ?_⟩
    · exact hfacts.1.trans lhart
    · exact hfacts.2.1
    · exact wwinWdom σ pc ea 4 vw

end wPEffHalf

/-! ## 3. THE LEAF -/

section leaf
variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [WeakGS GF]

/-- Rocq `wwp_sw4_leaf` (deviations 1, 2, 5, 6, 7). -/
theorem wwpSw4Leaf (gen : Nat) (cpu : CPU) (pc : BitVec 64) (w : BitVec 32) (rs1 rs2 : BitVec 5)
    (imm : BitVec 12) (ea : PAddr) (vold vw : BitVec 32) (R : VProp GF) (q : Qp) (c : MConf)
    (rs1v rs2v npc0 : BitVec 64) (D : Register → Bool) (dst : ExecSt) (ws : Wstate) :
    gen = 0 →
    MConf.mok c →
    pmpAllOff c.pmpcfg →
    is_aligned_vaddr (.Virtaddr pc) 4 = true →
    rs1.toNat ≠ 0 →
    rs2.toNat ≠ 0 →
    rs1v + sign_extend (m := 64) imm = ea →
    Sail.BitVec.extractLsb rs2v 31 0 = vw →
    inRam ea 4 →
    -- the decode, in the two shapes its two consumers ask for
    (∀ t : ExecSt,
      privMSU (t.regs .cur_privilege) = true →
      (_get_Misa_C (t.regs .misa) == 1#1) = true →
      (_get_Misa_A (t.regs .misa) == 1#1) = true →
      t.regs .misa = misaC →
      cfgOk t →
      exec (decodeFetch (.F_Base w)) t = some (.STORE (imm, .Regidx rs2, .Regidx rs1, 4), t)) →
    (∀ rs : RegFile,
      rs .cur_privilege = .Machine →
      rs .misa = misaC →
      rs .mseccfg = 0#64 →
      ∀ r, D r = true → rs r = dst.regs r) →
    D .minstret_increment = false →
    goodb0 D (ext_decode w) dst = true →
    exec (ext_decode w) dst = some (.STORE (imm, .Regidx rs2, .Regidx rs1, 4), dst) →
    mConf (GF := GF) cpu (DFrac.own q) c ⊢
      clockCells cpu -∗
      Register.PC ↦ᵣ[cpu] pc -∗
      Register.nextPC ↦ᵣ[cpu] npc0 -∗
      gpr cpu rs1 (DFrac.own 1) rs1v -∗
      gpr cpu rs2 (DFrac.own 1) rs2v -∗
      winstrBytes (GF := GF) pc (.F_Base w) -∗
      hartWs (GF := GF) cpu ws -∗
      vwpHold (wpt4Own (GF := GF) cpu ea vold) ws -∗
      vwpHold R ws -∗
      (∀ (ws' : Wstate) (T : Nat),
        ⌜wsLe ws ws'⌝ -∗
        ⌜∀ j : Nat, j < 4 → T ≤ flr (wsView ws') (WeakInterp.accAddr ea j)⌝ -∗
        mConf cpu (DFrac.own q) c -∗
        clockCells cpu -∗
        pcIs cpu (Sail.BitVec.addInt pc 4) -∗
        gpr cpu rs1 (DFrac.own 1) rs1v -∗
        gpr cpu rs2 (DFrac.own 1) rs2v -∗
        hartWs cpu ws' -∗
        vwpHold (wpt4Own (GF := GF) cpu ea vw) ws' -∗
        R.monPred_at (viewScl T) -∗
        wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu)) -∗
      wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu) := by
  intro hgid hmok hpmp hal4 hrs1nz hrs2nz hea hvw hram hdecf hagree hDmi hgood hdec
  iintro Hm Hclk Hpc Hnpc Hrs1c Hrs2c #Hbs Hhws Hpt HR Hcont
  ihave %haccpc := winstrBytesAccWf pc (.F_Base w) $$ Hbs
  ihave %hnotRVC := WeakLeafLw4.winstrBytesNotRVC pc w $$ Hbs
  have hdecW : winstrDec (.F_Base w) (.STORE (imm, .Regidx rs2, .Regidx rs1, 4)) := by
    intro t h1 h2 h3 h4 h5
    simp only [fetchIsRvc, Bool.false_eq_true, ↓reduceIte]
    exact hdecf t h1 h2 h3 h4 h5
  ihave #Hwi := winstrIntro (GF := GF) pc false (.STORE (imm, .Regidx rs2, .Regidx rs1, 4)) (.F_Base w)
    (by first | rfl | decide) rfl hdecW $$ Hbs
  -- THE WHOLE config goes to the funnel: it hands the reads back
  iapply wwpInstr gen cpu pc false (.STORE (imm, .Regidx rs2, .Regidx rs1, 4)) c (DFrac.own q)
    (wPEff (some cpu.val) ([.WEread WeakFetchEff.wakIfetch pc 4] ++ [.WEwrite wakPlain ea 4 vw]))
    (wQFr (wQStore (some cpu.val) ea vw) (some cpu.val)
      ([.WEread WeakFetchEff.wakIfetch pc 4] ++ [.WEwrite wakPlain ea 4 vw]))
    hgid haccpc hmok (fun i => (hpmp i).2)
    (wstepCertFr _ _ _ _ (wcertStoreBase4 cpu.val pc wakPlain ea vw)) $$ Hm Hclk Hpc Hwi
  unfold wwpCb
  iintro %σ %b %mt %ip %Lpc0 %hcfg Hlat Hreg Hnorg Hti Hip
  unfold wmstateNorg
  icases Hnorg with ⟨%hbnd, %hnv, %hwf, Hdev, Hlogauth, Hwsauth⟩
  ihave ⟨%hws, Hwsauth, Hhws⟩ := persistent_entails_right (hartWsAgree cpu σ.wmWs ws) $$ [Hwsauth Hhws]
  · iframe Hwsauth Hhws
  subst hws
  -- the config, as the funnel read it (seam 2)
  obtain ⟨Lpriv, Lhart, Lmisa, Lsec, Lpmpc, Lpma, Lhtif, LmisaS, LmIE, Lmprv, Lpmm, Lelp⟩ := hcfg
  -- the TWO registers the funnel does not read: base and data
  icases keepPure (WeakLeafLw4.gprValid cpu _ rs1 _ rs1v hrs1nz) $$ Hreg Hrs1c with ⟨%Lrs1a, Hreg, Hrs1c⟩
  icases keepPure (WeakLeafLw4.gprValid cpu _ rs2 _ rs2v hrs2nz) $$ Hreg Hrs2c with ⟨%Lrs2a, Hreg, Hrs2c⟩
  have Lrs1 : (wflatSt σ).gpr rs1 = rs1v := by
    rw [← WeakLeafLw4.gprSetNe (wflatSt σ) .minstret_increment b rs1 (by decide)]
    exact Lrs1a
  have Lrs2 : (wflatSt σ).gpr rs2 = rs2v := by
    rw [← WeakLeafLw4.gprSetNe (wflatSt σ) .minstret_increment b rs2 (by decide)]
    exact Lrs2a
  -- the effective address, at σ's own register file
  have hea_σ : (wflatSt σ).gpr rs1 + sign_extend (m := 64) imm = ea := by rw [Lrs1]; exact hea
  -- the agreement, at σ's registers
  have hag_σ : ∀ r, D r = true → σ.wmRegs r = dst.regs r := hagree _ Lpriv Lmisa Lsec
  have lpmp_σ : pmpAllOff (σ.wmRegs .pmpcfg_n) := by rw [Lpmpc]; exact hpmp
  -- ---- the certificate's precondition (§2d) ----
  icases WeakLeafLw4.keepPure2 (wPEffSw4 cpu.val cpu σ pc w rs1 rs2 imm ea vold rs2v vw D dst hwf Lpc0
      Lpriv lpmp_σ Lpma Lhtif Lhart LmisaS LmIE Lmprv Lpmm Lelp hal4 hnotRVC hea_σ Lrs2 hvw hram hag_σ
      hDmi hgood hdec) $$ Hlat Hbs Hpt with ⟨%HP, Hlat, -, Hpt⟩
  icases keepPure1 (wpt4OwnAlign cpu ea vold σ.wmWs) $$ Hpt with ⟨%halea, Hpt⟩
  -- ---- the run, at the FLAT state ----
  have hexf := execEffSw4At (wflatSt σ) b pc rs1 rs2 imm ea rs2v vw Lpriv Lmprv Lpmm lpmp_σ Lpma Lhtif
    hea_σ Lrs2 hvw halea hram
  have hfacts := storeRegsFacts (wflatSt σ) b (BitVec.addInt pc 4)
  -- ---- the ONE register write the wrapper expects: nextPC ----
  imod (wand_intro (reg_update cpu _ .nextPC npc0 (BitVec.addInt pc 4))) $$ Hreg Hnpc with ⟨Hreg, Hnpc⟩
  iapply fupd_mask_intro LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro; exact HP
  iexists ((((wflatSt σ).setReg .minstret_increment b).setReg .nextPC (BitVec.addInt pc 4)).setMem
    (bmWrite (wflatSt σ).mem ea 4 vw))
  isplitr
  · ipureintro; exact execEffExec _ _ _ _ _ hexf
  isplitl [Hreg]
  · rw [show ((((wflatSt σ).setReg .minstret_increment b).setReg .nextPC (BitVec.addInt pc 4)).setMem
        (bmWrite (wflatSt σ).mem ea 4 vw)).regs =
        ((wflatSt σ).setReg .minstret_increment b).regs.set .nextPC (BitVec.addInt pc 4) from rfl]
    iexact Hreg
  isplitl [Hti Hip]
  · iexists mt, ip
    iframe Hti Hip
  inext
  iintro %tick %σ' %t %hstep %hdevt0 %hpost %hQ Hm' Hclk' Hpc'
  -- the device frame (seam 1): the `execute` moved no device
  have hdevt : t.dev = σ.wmDev := by rw [hdevt0]; rfl
  obtain ⟨hregs, hdevs, hmems, himgs, hlogs, hwsle, hwf', hbnd'⟩ := hpost
  obtain ⟨⟨hQi, ⟨kc, hQl, -⟩, -, hQv⟩, hQeff⟩ := hQ
  -- the release deposit: freeze R at the store's own timestamp
  ihave HRdep := wwpReleaseDeposit R σ hbnd $$ HR
  -- THE WINDOW UPDATE: retarget the four elements at the message `wQStore` names
  icases wpt4OwnAtElems cpu ea vold σ.wmWs $$ Hpt with
    ⟨%halea2, %haccea, %t0, %t1, %t2, %t3, H0, S0, H1, S1, H2, S2, H3, S3⟩
  imod wlat4StorePrimOwn cpu kc σ ea vw t0 t1 t2 t3 _ _ _ _ $$ Hlat H0 S0 H1 S1 H2 S2 H3 S3
    with ⟨Hlat, Hl4⟩
  icases keepPure (winstrNv cpu σ.wmImg (σ.wmLog ++ [wwriteMsg (some cpu.val) kc ea 4 vw]) pc (.F_Base w))
    $$ Hlat Hbs with ⟨%hnvpc, Hlat, -⟩
  icases keepPure (nvOkWlat4Own cpu σ.wmImg (σ.wmLog ++ [wwriteMsg (some cpu.val) kc ea 4 vw]) ea
    (σ.wmLog.length + 1) vw) $$ Hlat Hl4 with ⟨%hnvea, Hlat, Hl4⟩
  -- the log authority grows by the SAME message
  imod wlogUpdate σ.wmLog [wwriteMsg (some cpu.val) kc ea 4 vw] $$ Hlogauth with Hlogauth
  -- the hart's own view cell moves to σ'
  imod hartWsUpdate cpu σ.wmWs σ.wmWs σ'.wmWs $$ [$Hwsauth $Hhws] with ⟨Hwsauth, Hhws⟩
  imod Hclose
  -- the PC the funnel hands back IS `pc+4`
  rw [show ((((wflatSt σ).setReg .minstret_increment b).setReg .nextPC (BitVec.addInt pc 4)).setMem
      (bmWrite (wflatSt σ).mem ea 4 vw)).regs .nextPC = BitVec.addInt pc 4 from hfacts.2.2]
  imodintro
  isplitl [Hlat]
  · rw [hQi, hQl]; iexact Hlat
  isplitl [Hdev Hlogauth Hwsauth]
  · isplitr
    · ipureintro; exact hbnd'
    isplitr
    · ipureintro
      apply nvHartOfWQEffOk cpu σ σ' _ hQeff hnv
      intro a ha
      rw [hQl]
      rcases weffsTouchApp _ _ a ha with ha | ha
      · obtain ⟨j, hj, rfl⟩ := weffsTouchRead1 _ pc _ a ha
        exact hnvpc j hj
      · obtain ⟨j, hj, rfl⟩ := weffsTouchWrite1 _ ea _ _ a ha
        exact hnvea j hj
    isplitr
    · ipureintro; exact hwf'
    rw [hdevs, hdevt, hQl]
    iframe Hdev Hlogauth Hwsauth
  -- the config comes back WHOLE from the funnel: nothing to recombine
  iapply Hcont $$ %σ'.wmWs %(σ.wmLog.length + 1) %hwsle %(fun j hj => hQv j hj) Hm' Hclk'
    [Hpc' Hnpc] Hrs1c Hrs2c Hhws [Hl4] HRdep
  · unfold pcIs
    iframe Hpc' Hnpc
  · -- the window, rebuilt at the successor's view AT THE STORED VALUE
    iapply wlat4OwnWpt4Own cpu ea (σ.wmLog.length + 1) vw σ'.wmWs halea2 haccea
      (fun j hj => hQv j hj)
    iexact Hl4

end leaf

end Weak
