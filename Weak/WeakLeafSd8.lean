/-
Weak: **the `sd`-class 8-byte STORE leaf, end to end** (M4 batch 2): from the
M-mode configuration, the PC cell, the text bytes of the instruction and the
OWNED eight-byte window at the effective address to `WWP (Loop)`.  Nothing
about the weak machine is left as a premise -- no certificate, no `wPEff`, no
`exec`/`execEff` fact.

Rocq: `iris/WeakLeafSd8.v` @ xxvzwolszwmp.

The Rocq header, in substance.  The store analog of `WeakLeafLd8` (and
mirroring its sections).  What the store exercises that the load did not:
* THE `Q` HALF IS REAL: `wQStore8` names the MESSAGE the step appended
  (`wwriteMsg (some cid) k ea 8 v` at the log's fresh top), and the leaf USES
  it: the eight latest-write elements of the window are retargeted at that
  message (`WeakWord8.wlat8StorePrimOwn`) and the log authority grows by it
  (`WeakGhost.wlogUpdate`), or `wmstateNorg σ'` would be unprovable.
* THE `↦w₈`-IN / `↦w₈`-OUT CONTRACT: the caller hands
  `vwpHold (ea ↦w₈ₒ[cpu] vold) ws` and receives
  `vwpHold (ea ↦w₈ₒ[cpu] vnew) ws'` (the window at the STORED value, at the
  successor's view) plus the store's timestamp fact in the `wQStore` shape,
  `T ≤ flr (wsView ws') (accAddr ea j)` for every byte, at the leaf-chosen
  `T = σ.wmLog.length + 1`.
* THE RELEASE-DEPOSIT SURFACE: the leaf takes `vwpHold R ws` and hands back
  `R.monPred_at (viewScl T)` (`WeakInstr.wwpReleaseDeposit`), the OBJECTIVE
  payload a lock/escrow invariant stores (`R := emp` if there is none).
Sections: §1 `wcertStoreW` (`WeakCert.wcertStore` made width-generic, with the
subsumption check `wcertStoreW4` and the width-8 instance at the fetch element
`wcertStore8Base4`); §2 the window (the shared `WeakLeafWin.wwin pc ea 8`) and
the `wPEff` half -- the `execute` lemma at an arbitrary state
(`execEffSd8At`) and `wPEffSd8`; §3 the leaf `wwpSd8Leaf`, through
`WeakFunnel.wwpInstr` at `P := wPEff …`, `Q := wQFr (wQStore8 …) …`.
Every pure / geometry side condition is a premise (alignment, RAM, the decode
facts, `goodb0`).

**Deviations from Rocq.**
1. NAMES / VOCABULARY: the tree's camelCase (map below); as
   `Weak/WeakLeafWin.lean` / `Weak/WeakFunnel.lean` deviation 1
   (`register_lookup r s.(sregs)` ↦ `s.regs r`, `eq_vec x 'b"1" = b` ↦
   `(x == 1#1) = b`, `mword n` ↦ `BitVec n`, `N` widths ↦ `Nat`,
   `S (length l)` ↦ `l.length + 1`, `add_vec_int` ↦ `BitVec.addInt`,
   `write_bytes` ↦ `bmWrite`, `MState r m d` ↦ `⟨r, m, d⟩`, `acc_addr` ↦
   `WeakInterp.accAddr`, `view_scl` ↦ `viewScl`, `fin_to_nat cpu_id` ↦
   `cpu.val`).
2. GPRs: Rocq's `if uint rs =? 0 then zero_reg else register_lookup
   (R_bitvector_64 (gpr_of_Z (uint rs))) regs` ↦ `s.gpr rs` (the ExecSC
   convention; in `wPEffSd8` the operands are stated at `(wflatSt σ).gpr`, as
   `WeakLeafLw4.wPEffLw4` does); Rocq's cells `R_bitvector_64 (gpr_of_Z
   (uint rs)) ↦ᵣ v` (with `uint rs <> 0`) ↦ `gpr cpu rs (DFrac.own 1) v` (with
   `rs.toNat ≠ 0`), the SC tree's GPR cell, read against `regInterp` by
   `WeakLeafLw4.gprValid` (reused; Rocq `reg_valid` + `reg_at_flat`).
   The Lean-only `WeakLeafSd8.gprSetRegNe` is the frame of a non-GPR write
   (used by `execEffSd8At`; the leaf uses `WeakLeafLw4.gprSetNe`).
3. RAM / PMA / PMP: Rocq's per-byte `∀ j < 8, addr_is_ram (pa_add ea j)` is the
   window form `inRam ea 8` (WeakFunnel deviation 2); `pma_allows_all` ↦
   `pma_regions = bootPMA`; `pmp_all_off` ↦ `MachCSL.pmpAllOff`.  The region
   is `ramRegion` (`matching_pma_ram`), the CLINT/SIG/HTIF/device side
   conditions are discharged as in `WeakFetchEff` §4.
4. O2 (owner decision; `Weak/WeakFetchEff.lean` deviation 2): the fetch
   element is `.WEread WeakFetchEff.wakIfetch pc 4` (Rocq `WEread wak_plain pc
   4`) in `wcertStore8Base4`, `wPEffSd8` and the leaf.  `wPEffOfLeafBase`'s
   extra premise `fetchPin` is discharged inside `wPEffSd8` from the text
   bytes (`WeakFunnel.winstrTextPinned`; `fetchFresh` of a read then a write),
   so no statement gains a premise; `is_lpad_instruction (STORE …) = false` is
   by computation.
5. `exec_eff_sd8_at`'s successor `MState (sregs s) (write_bytes s0.(mem) ea 8
   vs) s0.(mdev)` is the literal `⟨s.regs, bmWrite s0.mem ea 8 vs, s0.dev⟩`
   with `s` written out.
6. STATEMENT SHAPES (WeakFunnel deviation 3): `A -∗ B -∗ C` ↦ `A ⊢ B -∗ C`.
7. THE CONFIG INTERFACE (owner decision Q3, WeakFunnel deviation 7): Rocq's
   `mmode_config (DfracOwn q)` ↦ `mConf cpu (DFrac.own q) c ∗ clockCells cpu`;
   Rocq's `pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0` and `pmp_all_off pmpcfg0` ↦
   `mConf`'s own cell and `pmpAllOff c.pmpcfg`; the premise `MConf.mok c`
   (what `wwpInstr` needs of mstatus) is added.  The section's `GenId`/`CpuId`
   are the explicit `gen`/`cpu`; `pc_is` ↦ `pcIs`; `WWP Loop` ↦
   `wwpTriv ⊤ (WExpr.loop gen cpu)`.  The decode's first shape is stated
   literally (`decodeFetch`, `privMSU`, `cfgOk`, `misaC`), the agreement's
   `mword_of_int 0` is `0#64`.
8. Rocq's `wwp_sd8_leaf` opens the mask with `fupd_mask_intro` before the
   `execute` witness and closes it after the ghost updates; the Lean funnel's
   callback is `={⊤,∅}=∗ … ▷ (… |={∅,⊤}=> …)` and the leaf hands back the
   `mtime`/`mip` cells unchanged (Q3).
9. Rocq §5's `Print Assumptions` are not declarations.
10. Rocq's in-proof `assert (HnotRVC …)` is `WeakLeafLw4.winstrBytesNotRVC`;
   Rocq's `iDestruct … as %HP` keeping the three resources is
   `WeakLeafLw4.keepPure2` (both reused from `Weak/WeakLeafLw4.lean`).

**Rocq → Lean name map.**  `wcert_store_w` `wcertStoreW`, `wcert_store_w_4`
`wcertStoreW4`, `wcert_store8_base4` `wcertStore8Base4`, `exec_eff_sd8_at`
`execEffSd8At`, `wP_eff_sd8` `wPEffSd8`, `wwp_sd8_leaf` `wwpSd8Leaf`.  None is
in the duplicated-name table.  Lean-only (file-qualified):
`WeakLeafSd8.gprSetRegNe`; reused from `WeakLeafLw4`: `gprValid`, `gprSetNe`,
`winstrBytesNotRVC`, `keepPure2`.

**Dropped:** nothing (6 Rocq `Lemma`s; Lean 6 theorems + 1 Lean-only).
-/
import Weak.WeakLeafWin
import Weak.WeakLeafEff8s
import Weak.WeakLeafLw4
import MachCSL.Boot
import MachCSL.Gpr

namespace Weak

open Iris Iris.BI Iris.BI.MonPred Iris.ProofMode Iris.Std
open MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D LeanRV64D.Functions

/-! ## 1. THE WIDTH-GENERIC STORE CERTIFICATE

`WeakCert.wcertStore`'s script with `4` replaced by `n`. -/

theorem wcertStoreW (n : Nat) (cid : Nat) (pc : BitVec 64) (akf : AkInfo) (pf : PAddr) (nf : Nat)
    (akw : AkInfo) (ea : PAddr) (v : BitVec (8 * n)) :
    wstepCert cid pc (wPEff (some cid) [.WEread akf pf nf, .WEwrite akw ea n v])
      (wQStoreW n (some cid) ea v) := by
  apply wstepCertEff
  intro s s' hi hl hws
  have hle : wsLe s.wmWs s'.wmWs := by rw [hws]; exact weffsWsLe _ _ _
  rw [weffsCons2, weffApplyRead, weffApplyWrite] at hl hws
  rw [wwritePostLog, wreadPostLog] at hl
  rw [wwritePostWs, wreadPostLog] at hws
  unfold wQStoreW wVStoreW
  refine ⟨hi, ⟨_, hl, fun hr => WeakInstr.wmClassOfRelp _ _ (by rw [WeakInstr.wreadPostRelp]; exact hr)⟩,
    hle, fun j hj => ?_⟩
  rw [hws, flr_wsView]
  have := storePostRunCoh (wreadPost s akf pf (cohTs s pf nf)).wmWs akw.akSync (paZ ea) n
    (s.wmLog.length + 1) j hj
  simp only [WeakInterp.accAddr]
  omega

/-- THE SUBSUMPTION CHECK: `WeakCert.wcertStore`'s statement is the `n := 4`
instance. -/
theorem wcertStoreW4 (cid : Nat) (pc : BitVec 64) (akf : AkInfo) (pf : PAddr) (nf : Nat)
    (akw : AkInfo) (ea : PAddr) (v : BitVec 32) :
    wstepCert cid pc (wPEff (some cid) [.WEread akf pf nf, .WEwrite akw ea 4 v])
      (wQStore (some cid) ea v) :=
  wcertStoreW 4 cid pc akf pf nf akw ea v

/-- ... and the width-8 instance at the fetch element `WeakFetchEff`'s replay
produces (deviation 4). -/
theorem wcertStore8Base4 (cid : Nat) (pc : BitVec 64) (akw : AkInfo) (ea : PAddr) (v : BitVec 64) :
    wstepCert cid pc
      (wPEff (some cid) ([.WEread WeakFetchEff.wakIfetch pc 4] ++ [.WEwrite akw ea 8 v]))
      (wQStore8 (some cid) ea v) :=
  wcertStoreW 8 cid pc WeakFetchEff.wakIfetch pc 4 akw ea v

/-! ## 2. THE WINDOW AND THE `wPEff` HALF

The window and its obligations are the shared kit's (`WeakLeafWin`):
`wwin pc ea 8` with `wwinNonzero` / `wwinPinned` / `wwinConfText` and the
write-domain confinement `wwinWdom`. -/

/-- Lean-only (deviation 2): a non-GPR register write leaves every GPR alone. -/
theorem WeakLeafSd8.gprSetRegNe (s : ExecSt) (r : Register) (x : RegisterType r) (i : BitVec 5)
    (h : r ∉ uxaGprs) : (s.setReg r x).gpr i = s.gpr i := by
  unfold ExecSt.gpr
  apply uxaXget_congr
  intro r' hr'
  have hne : r' ≠ r := by rintro rfl; exact h hr'
  exact setLookupNe r' r s x hne

/-- Rocq `exec_eff_sd8_at`: the 8-byte store's `execute` at an ARBITRARY `s0`
with the funnel's two pre-writes on top (deviations 2, 3, 5).  A store reads
nothing: no memory premise. -/
theorem execEffSd8At (s0 : ExecSt) (b : Bool) (pc : BitVec 64) (rs1 rs2 : BitVec 5) (imm : BitVec 12)
    (ea vs : BitVec 64) :
    s0.regs .cur_privilege = .Machine →
    (_get_Mstatus_MPRV (s0.regs .mstatus) == 1#1) = false →
    pmm_mode_backwards (_get_Seccfg_PMM (s0.regs .mseccfg)) = .PMM_Disabled →
    pmpAllOff (s0.regs .pmpcfg_n) →
    s0.regs .pma_regions = bootPMA →
    s0.regs .htif_tohost_base = none →
    s0.gpr rs1 + sign_extend (m := 64) imm = ea →
    s0.gpr rs2 = vs →
    is_aligned_paddr (.Physaddr ea) 8 = true →
    inRam ea 8 →
    execEff (execute (.STORE (imm, .Regidx rs2, .Regidx rs1, 8)))
        ((s0.setReg .minstret_increment b).setReg .nextPC (BitVec.addInt pc 4)) =
      some (RETIRE_SUCCESS,
        ⟨((s0.setReg .minstret_increment b).setReg .nextPC (BitVec.addInt pc 4)).regs,
          bmWrite s0.mem ea 8 vs, s0.dev⟩,
        [.WEwrite wakPlain ea 8 vs]) := by
  intro lpriv lmprv lpmm lpmp lpma lhtif hea hvs hal hram
  obtain ⟨s, hs⟩ : ∃ s, s = (s0.setReg .minstret_increment b).setReg .nextPC (BitVec.addInt pc 4) :=
    ⟨_, rfl⟩
  rw [← hs]
  -- every config register, moved past the funnel's two pre-writes
  have lpriv_s : s.regs .cur_privilege = .Machine := by rw [hs]; leaf_peel .cur_privilege; exact lpriv
  have lms_s : s.regs .mstatus = s0.regs .mstatus := by rw [hs]; leaf_peel .mstatus
  have lsec_s : s.regs .mseccfg = s0.regs .mseccfg := by rw [hs]; leaf_peel .mseccfg
  have lpmpc_s : s.regs .pmpcfg_n = s0.regs .pmpcfg_n := by rw [hs]; leaf_peel .pmpcfg_n
  have lpma_s : s.regs .pma_regions = bootPMA := by rw [hs]; leaf_peel .pma_regions; exact lpma
  have lhtif_s : s.regs .htif_tohost_base = none := by
    rw [hs]; leaf_peel .htif_tohost_base; exact lhtif
  -- the base and data registers (x0 reads zero on both sides)
  have hgea : s.gpr rs1 + sign_extend (m := 64) imm = ea := by
    rw [hs, WeakLeafSd8.gprSetRegNe _ _ _ _ (by decide), WeakLeafSd8.gprSetRegNe _ _ _ _ (by decide)]
    exact hea
  have hgvs : s.gpr rs2 = vs := by
    rw [hs, WeakLeafSd8.gprSetRegNe _ _ _ _ (by decide), WeakLeafSd8.gprSetRegNe _ _ _ _ (by decide)]
    exact hvs
  have hmem : s.mem = s0.mem := by rw [hs]; rfl
  have hdev : s.dev = s0.dev := by rw [hs]; rfl
  have key := execEffExecuteSTORE8Gpr rs2 rs1 imm ramRegion s lpriv_s
    (by rw [lms_s]; exact lmprv) (by rw [lsec_s]; exact lpmm) (by rw [hgea]; exact hal)
    (by
      rw [hgea]
      exact execEffPmpCheckMachineNone _ _ _ s (fun i => by rw [lpmpc_s]; exact (lpmp i).1))
    (by rw [hgea, lpma_s]; exact matching_pma_ram ea 8 hram (by omega) (by omega))
    (by rw [hgea]; exact hal)
    (by first | rfl | decide +kernel)
    (by rw [hgea, within_clint_ram ea 8 hram]; rfl)
    (by
      first
      | rfl
      | (simp only [within_sig, plat_have_sig, Functions.not]; rfl))
    (by rw [hgea]; exact execEffWithinHtifWFalse ea 8 s lhtif_s)
    (by rw [hgea]; exact devAddrRam ea 8 hram)
  rw [hgea, hgvs, hmem] at key
  rw [key, ← hdev]
  rfl

/-! ### 2d. THE `wPEff` HALF -/

section wPEffHalf
variable {GF : BundledGFunctors} [WeakGS GF]

/-- Rocq `wP_eff_sd8`: THE `wPEff` HALF, from the four text bytes and the
owned eight-byte window, plus the M-mode register tower and the instruction's
pure geometry (deviations 2-4). -/
theorem wPEffSd8 (cid : Nat) (cid8 : CPU) (σ : Wmstate) (pc : BitVec 64) (w : BitVec 32)
    (rs1 rs2 : BitVec 5) (imm : BitVec 12) (ea : PAddr) (vold vs : BitVec 64)
    (D : Register → Bool) (dst : ExecSt) :
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
    inRam ea 8 →
    -- the decode, exactly as the decode library states it
    (∀ r, D r = true → σ.wmRegs r = dst.regs r) →
    D .minstret_increment = false →
    goodb0 D (ext_decode w) dst = true →
    exec (ext_decode w) dst = some (.STORE (imm, .Regidx rs2, .Regidx rs1, 8), dst) →
    -- the resources
    wlatInterp (GF := GF) σ.wmImg σ.wmLog ⊢
      winstrBytes (GF := GF) pc (.F_Base w) -∗
      vwpHold (wpt8Own (GF := GF) cid8 ea vold) σ.wmWs -∗
      ⌜wPEff (some cid) ([.WEread WeakFetchEff.wakIfetch pc 4] ++ [.WEwrite wakPlain ea 8 vs]) σ⌝ := by
  intro hwf lpc lpriv lpmp lpma lhtif lhart lmisaS lmIE lmprv lpmm lelp hal4 hnotRVC hea hvs hram
    hagree hDmi hgood hdec
  iintro Hlat #Hbs Hpt
  ihave %haccpc := winstrBytesAccWf pc (.F_Base w) $$ Hbs
  icases keepPure (winstrBytesLookup σ pc (.F_Base w) hwf) $$ Hlat Hbs with ⟨%hfok, Hlat, -⟩
  icases keepPure (winstrTextPinned σ pc (.F_Base w) hwf) $$ Hlat Hbs with ⟨%htp, Hlat, -⟩
  icases keepPure1 (wpt8OwnAlign cid8 ea vold σ.wmWs) $$ Hpt with ⟨%halea, Hpt⟩
  ihave %hfp := wpt8OwnFlatPin cid8 σ ea vold hwf $$ Hlat Hpt
  ipureintro
  obtain ⟨haccea, hflatpin⟩ := hfp
  obtain ⟨-, ⟨-, hrampc, w', ⟨hww, -⟩, htext⟩⟩ := hfok
  subst hww
  apply wPEffOfLeafBase cid σ (wwin pc ea 8) pc w (.STORE (imm, .Regidx rs2, .Regidx rs1, 8))
    [.WEwrite wakPlain ea 8 vs] D dst hwf
    (wwinNonzero pc ea 8 (fun j hj => WeakLeafWin.inRamByte pc 4 j hrampc hj)
      (fun j hj => WeakLeafWin.inRamByte ea 8 j hram hj))
    (wwinPinned σ pc ea 8 haccpc haccea (fun j hj => (htp j hj).1) (fun j hj => (hflatpin j hj).2))
  · -- the O2 fetch pin
    refine ⟨fun ak pa n hin hif j hj => ?_, by simp [fetchFresh, weffWrites]⟩
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, _root_.or_false] at hin
    rcases hin with hin | hin
    · cases hin
      exact (htp j hj).2
    · cases hin
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
  · exact wwinConfText σ pc ea 8 w htext
  · exact hnotRVC
  · exact hagree
  · exact hDmi
  · exact hgood
  · exact hdec
  · first | rfl | decide
  · intro b
    have hfacts := storeRegsFacts ⟨σ.wmRegs, wmemRestrict σ (wwin pc ea 8), σ.wmDev⟩ b
      (BitVec.addInt pc 4)
    have hea_c : (⟨σ.wmRegs, wmemRestrict σ (wwin pc ea 8), σ.wmDev⟩ : ExecSt).gpr rs1 +
        sign_extend (m := 64) imm = ea := by
      unfold ExecSt.gpr at hea ⊢; exact hea
    have hvs_c : (⟨σ.wmRegs, wmemRestrict σ (wwin pc ea 8), σ.wmDev⟩ : ExecSt).gpr rs2 = vs := by
      unfold ExecSt.gpr at hvs ⊢; exact hvs
    have hrun := execEffSd8At ⟨σ.wmRegs, wmemRestrict σ (wwin pc ea 8), σ.wmDev⟩ b pc rs1 rs2 imm ea vs
      lpriv lmprv lpmm lpmp lpma lhtif hea_c hvs_c halea hram
    refine ⟨_, hrun, ?_, ?_, ?_⟩
    · exact hfacts.1.trans lhart
    · exact hfacts.2.1
    · dsimp only
      exact wwinWdom σ pc ea 8 vs

end wPEffHalf

/-! ## 3. THE LEAF -/

section leaf
variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [WeakGS GF]

/-- Rocq `wwp_sd8_leaf` (deviations 2, 3, 7, 8): THE LEAF.  The window comes
back at the STORED value and the successor's view; the continuation gains the
store's timestamp `T` with its per-byte floor fact and the release payload `R`
frozen at `viewScl T`. -/
theorem wwpSd8Leaf (gen : Nat) (cpu : CPU) (pc : BitVec 64) (w : BitVec 32) (rs1 rs2 : BitVec 5)
    (imm : BitVec 12) (ea : PAddr) (vold : BitVec 64) (R : VProp GF) (q : Qp) (c : MConf)
    (rs1v rs2v npc0 : BitVec 64) (D : Register → Bool) (dst : ExecSt) (ws : Wstate) :
    gen = 0 →
    MConf.mok c →
    pmpAllOff c.pmpcfg →
    is_aligned_vaddr (.Virtaddr pc) 4 = true →
    rs1.toNat ≠ 0 →
    rs2.toNat ≠ 0 →
    rs1v + sign_extend (m := 64) imm = ea →
    inRam ea 8 →
    -- the decode, in the two shapes its two consumers ask for
    (∀ t : ExecSt,
      privMSU (t.regs .cur_privilege) = true →
      (_get_Misa_C (t.regs .misa) == 1#1) = true →
      (_get_Misa_A (t.regs .misa) == 1#1) = true →
      t.regs .misa = misaC →
      cfgOk t →
      exec (decodeFetch (.F_Base w)) t = some (.STORE (imm, .Regidx rs2, .Regidx rs1, 8), t)) →
    (∀ rs : RegFile,
      rs .cur_privilege = .Machine →
      rs .misa = misaC →
      rs .mseccfg = 0#64 →
      ∀ r, D r = true → rs r = dst.regs r) →
    D .minstret_increment = false →
    goodb0 D (ext_decode w) dst = true →
    exec (ext_decode w) dst = some (.STORE (imm, .Regidx rs2, .Regidx rs1, 8), dst) →
    mConf (GF := GF) cpu (DFrac.own q) c ⊢
      clockCells cpu -∗
      Register.PC ↦ᵣ[cpu] pc -∗
      Register.nextPC ↦ᵣ[cpu] npc0 -∗
      gpr cpu rs1 (DFrac.own 1) rs1v -∗
      gpr cpu rs2 (DFrac.own 1) rs2v -∗
      winstrBytes (GF := GF) pc (.F_Base w) -∗
      hartWs (GF := GF) cpu ws -∗
      vwpHold (wpt8Own (GF := GF) cpu ea vold) ws -∗
      vwpHold R ws -∗
      (∀ (ws' : Wstate) (T : Nat),
        ⌜wsLe ws ws'⌝ -∗
        ⌜∀ j : Nat, j < 8 → T ≤ flr (wsView ws') (WeakInterp.accAddr ea j)⌝ -∗
        mConf cpu (DFrac.own q) c -∗
        clockCells cpu -∗
        pcIs cpu (BitVec.addInt pc 4) -∗
        gpr cpu rs1 (DFrac.own 1) rs1v -∗
        gpr cpu rs2 (DFrac.own 1) rs2v -∗
        hartWs cpu ws' -∗
        vwpHold (wpt8Own (GF := GF) cpu ea rs2v) ws' -∗
        R.monPred_at (viewScl T) -∗
        wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu)) -∗
      wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu) := by
  intro hgid hmok hpmp hal4 hrs1nz hrs2nz hea hram hdecf hagree hDmi hgood hdec
  iintro Hm Hclk Hpc Hnpc Hrs1c Hrs2c #Hbs Hhws Hpt HR Hcont
  ihave %haccpc := winstrBytesAccWf pc (.F_Base w) $$ Hbs
  ihave %hnotRVC := WeakLeafLw4.winstrBytesNotRVC pc w $$ Hbs
  have hdecW : winstrDec (.F_Base w) (.STORE (imm, .Regidx rs2, .Regidx rs1, 8)) := by
    intro t h1 h2 h3 h4 h5
    simp only [fetchIsRvc, Bool.false_eq_true, ↓reduceIte]
    exact hdecf t h1 h2 h3 h4 h5
  ihave #Hwi := winstrIntro (GF := GF) pc false (.STORE (imm, .Regidx rs2, .Regidx rs1, 8)) (.F_Base w)
    (by first | rfl | decide) rfl hdecW $$ Hbs
  -- THE WHOLE config goes to the funnel: it hands the reads back
  iapply wwpInstr gen cpu pc false (.STORE (imm, .Regidx rs2, .Regidx rs1, 8)) c (DFrac.own q)
    (wPEff (some cpu.val) ([.WEread WeakFetchEff.wakIfetch pc 4] ++ [.WEwrite wakPlain ea 8 rs2v]))
    (wQFr (wQStore8 (some cpu.val) ea rs2v) (some cpu.val)
      ([.WEread WeakFetchEff.wakIfetch pc 4] ++ [.WEwrite wakPlain ea 8 rs2v]))
    hgid haccpc hmok (fun i => (hpmp i).2)
    (wstepCertFr _ _ _ _ (wcertStore8Base4 cpu.val pc wakPlain ea rs2v)) $$ Hm Hclk Hpc Hwi
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
  icases WeakLeafLw4.keepPure2 (wPEffSd8 cpu.val cpu σ pc w rs1 rs2 imm ea vold rs2v D dst hwf Lpc0
      Lpriv lpmp_σ Lpma Lhtif Lhart LmisaS LmIE Lmprv Lpmm Lelp hal4 hnotRVC hea_σ Lrs2 hram hag_σ
      hDmi hgood hdec) $$ Hlat Hbs Hpt with ⟨%HP, Hlat, -, Hpt⟩
  icases keepPure1 (wpt8OwnAlign cpu ea vold σ.wmWs) $$ Hpt with ⟨%halea, Hpt⟩
  -- ---- the run, at the FLAT state ----
  have hexf := execEffSd8At (wflatSt σ) b pc rs1 rs2 imm ea rs2v Lpriv Lmprv Lpmm lpmp_σ Lpma Lhtif
    hea_σ Lrs2 halea hram
  obtain ⟨sE, hsE⟩ : ∃ sE : ExecSt, sE =
      ⟨(((wflatSt σ).setReg .minstret_increment b).setReg .nextPC (BitVec.addInt pc 4)).regs,
        bmWrite (wflatSt σ).mem ea 8 rs2v, (wflatSt σ).dev⟩ := ⟨_, rfl⟩
  rw [← hsE] at hexf
  have hsEregs : sE.regs = (((wflatSt σ).setReg .minstret_increment b).regs).set .nextPC
      (BitVec.addInt pc 4) := by rw [hsE]; rfl
  have hsEdev : sE.dev = σ.wmDev := by rw [hsE]; rfl
  have hsEnpc : sE.regs .nextPC = BitVec.addInt pc 4 := by
    rw [hsE]; exact (storeRegsFacts (wflatSt σ) b (BitVec.addInt pc 4)).2.2
  -- ---- the ONE register write the wrapper expects: nextPC ----
  imod (wand_intro (reg_update cpu _ .nextPC npc0 (BitVec.addInt pc 4))) $$ Hreg Hnpc with ⟨Hreg, Hnpc⟩
  rw [← hsEregs]
  iapply fupd_mask_intro LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro; exact HP
  iexists sE
  isplitr
  · ipureintro; exact execEffExec _ _ _ _ _ hexf
  isplitl [Hreg]
  · iexact Hreg
  isplitl [Hti Hip]
  · iexists mt, ip
    iframe Hti Hip
  inext
  iintro %tick %σ' %t %hstep %hdevt %hpost %hQ Hm' Hclk' Hpc'
  obtain ⟨-, hdevs, -, -, -, hwsle, hwf', hbnd'⟩ := hpost
  obtain ⟨⟨hQi, ⟨kc, hQl, -⟩, -, hQv⟩, hQeff⟩ := hQ
  -- the release deposit: freeze R at the store's own timestamp
  ihave HRdep := wwpReleaseDeposit R σ hbnd $$ HR
  -- THE WINDOW UPDATE: retarget the eight elements at the message `wQStore8` names
  icases wpt8OwnAtElems cpu ea vold σ.wmWs $$ Hpt with
    ⟨%halea2, %haccea, %t0, %t1, %t2, %t3, %t4, %t5, %t6, %t7,
      H0, S0, H1, S1, H2, S2, H3, S3, H4, S4, H5, S5, H6, S6, H7, S7⟩
  imod wlat8StorePrimOwn cpu kc σ ea rs2v t0 t1 t2 t3 t4 t5 t6 t7 _ _ _ _ _ _ _ _
      $$ Hlat H0 S0 H1 S1 H2 S2 H3 S3 H4 S4 H5 S5 H6 S6 H7 S7 with ⟨Hlat, Hl8⟩
  icases keepPure (winstrNv cpu _ _ pc _) $$ Hlat Hbs with ⟨%hnvpc, Hlat, -⟩
  icases keepPure (nvOkWlat8Own cpu _ _ ea _ rs2v) $$ Hlat Hl8 with ⟨%hnvea, Hlat, Hl8⟩
  -- the log authority grows by the SAME message
  imod wlogUpdate σ.wmLog [wwriteMsg (some cpu.val) kc ea 8 rs2v] $$ Hlogauth with Hlogauth
  -- the hart's own view cell moves to σ'
  imod hartWsUpdate cpu σ.wmWs σ.wmWs σ'.wmWs $$ [$Hwsauth $Hhws] with ⟨Hwsauth, Hhws⟩
  imod Hclose
  -- the PC the funnel hands back IS pc+4
  rw [hsEnpc]
  ihave Hpt' := wlat8OwnWpt8Own cpu ea (σ.wmLog.length + 1) rs2v σ'.wmWs halea2 haccea
    (fun j hj => hQv j hj) $$ Hl8
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
    rw [hdevs, hdevt, hsEdev, hQl]
    iframe Hdev Hlogauth Hwsauth
  -- the config comes back WHOLE from the funnel: nothing to recombine
  iapply Hcont $$ %σ'.wmWs %(σ.wmLog.length + 1) %hwsle %(fun j hj => hQv j hj) Hm' Hclk'
    [Hpc' Hnpc] Hrs1c Hrs2c Hhws Hpt' HRdep
  unfold pcIs
  iframe Hpc' Hnpc

end leaf

end Weak
