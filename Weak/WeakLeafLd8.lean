/-
Weak: **M4's FIRST COMPLETE WEAK INSTRUCTION LEAF** (batch 2): the `ld`-class
plain 8-byte LOAD, end to end -- from the M-mode config bundle, the PC cell,
the text bytes and eight owned data bytes to `wwpTriv ⊤ (WExpr.loop gen cpu)`.

Rocq: `iris/WeakLeafLd8.v` @ xxvzwolszwmp.

The Rocq header, in substance.  Nothing about the weak machine is left as a
premise -- no certificate, no `wPEff`, no `exec`/`execEff` fact.  Every leaf of
the M4 sweep is this file with a different `execute` lemma and a different
data width.  It is assembled out of: `WeakFunnel.wwpInstr` (THE FUNNEL: the
whole `riscv_step` wrapper, so the leaf owes ONE `execute` fact);
`WeakFetchEff.wPEffOfLeafBase` (THE RECIPE: text bytes + decode fact + the
`execute`'s `execEff` fact ⇒ the certificate's `wPEff` obligation);
`WeakLeafEff8.execEffExecuteLOAD8Gpr` (THE SHAPE: trace `[WEread plain ea 8]`);
`WeakWord8`'s `wpt8` family (THE RESOURCE: `wwpLd8` discharges the read
obligation and pins the flat doubleword, `wwpLd8Carry` frames it).
* §1 `wcertLoadW` -- `WeakCert.wcertLoad` made WIDTH-GENERIC (the same script
  with `4` replaced by `n`), the subsumption check `wcertLoadW4` and the
  width-8 instance at the concrete fetch element `wcertLoad8Base4`.
* §2 THE WINDOW AND THE `wPEff` HALF: the window is `WeakLeafWin.wwin pc ea 8`;
  `execEffLd8At` is the `execute` fact over an ARBITRARY state (instantiated
  twice: at the confined state and at the flat one); `wPEffLd8` discharges
  the certificate's precondition from the resources.
* §3 `wwpLd8Leaf` -- the leaf: `wwpInstr` at `P := wPEff …`,
  `Q := wQFr (wQLoadW 8 ea) …` and §1's certificate.
Every pure / geometry side condition is a premise (alignment, the PMP/PMA
match, the decode facts, the agreement, `goodb0`).

**Deviations from Rocq.**
1. NAMES / VOCABULARY: the tree's camelCase (map below); as
   `Weak/WeakLeafWin.lean` deviation 1 and `Weak/WeakFetchEff.lean`
   deviation 1 (`register_lookup r s.(sregs)` ↦ `s.regs r`, `set_reg` ↦
   `ExecSt.setReg`, `eq_vec x 'b"1" = b` ↦ `(x == 1#1) = b`, `pa_add a j` ↦
   `a + BitVec.ofNat 64 j`, `add_vec_int` ↦ `Sail.BitVec.addInt`, `uint` ↦
   `toNat`, `RETIRE_SUCCESS` ↦ `.Retire_Success ()`); the GPR read
   `if uint rs1 =? 0 then zero_reg else register_lookup (R_bitvector_64 …)` is
   `s.gpr rs1` (`uxaXget s.regs rs1` at a bare register file); the GPR write is
   `setGpr` (equal for `rd ≠ 0`, `WeakLeafWin` deviation 5); the data window
   `∀ j < 8, s0.(mem) !! pa_add ea j = Some (nth_byte v j)` is
   `BytesAt s0 ea 8 v`; the GPR cell `R_bitvector_64 (gpr_of_Z (uint r)) ↦ᵣ x`
   is `MachCSL.gpr cpu r (DFrac.own 1) x`; `regval_into_reg v` is `v`.
2. O2 (owner decision; `Weak/WeakFetchEff.lean` deviation 2): the fetch's
   trace element is `.WEread WeakFetchEff.wakIfetch pc 4` (Rocq
   `WEread wak_plain pc 4`); `WeakCert.wcertLoad`'s side condition is
   `akl.akIfetch = false` (Rocq `ak_coh akl = false`), and so is
   `wcertLoadW`'s / `wcertLoad8Base4`'s.  `wPEffLd8` discharges the extra
   `fetchPin` obligation of `wPEffOfLeafBase` (its deviation 9) from the text
   bytes (`winstrTextPinned`) -- the Lean-only `WeakLeafLd8.fetchPinLd8`.
3. RAM AND PMA (`Weak/WeakFunnel.lean` deviation 2): Rocq's per-byte
   `∀ j < 8, addr_is_ram (pa_add ea j)` is the window form `inRam ea 8`;
   `pma_allows_all` is `pma_regions = bootPMA` (so the RAM region is
   `MachCSL.ramRegion`, `matching_pma_ram`); `pmp_all_off` is
   `MachCSL.pmpAllOff` (`pmp_all_off_allows_all` is its `.2`).
4. THE CONFIG INTERFACE (owner decision Q3; `Weak/WeakFunnel.lean`
   deviation 7): Rocq `mmode_config (DfracOwn q)` ∗ `pmpcfg_n ↦ᵣ{q} pmpcfg0`
   is `mConf cpu dq c ∗ clockCells cpu` (`pmpcfg0 := c.pmpcfg`, the fraction
   generalised to any `dq`), with the extra premise `MConf.mok c`; the
   continuation gets back `mConf cpu dq c` and `clockCells cpu`.  `GEN`/`CID`
   are the explicit `gen`/`cpu` (`fin_to_nat cpu_id` ↦ `cpu.val`), `WWP Loop`
   is `wwpTriv ⊤ (WExpr.loop gen cpu)`, `hart_ws` is `hartWs`.  The callback
   passes the `mtime`/`mip` cells back untouched.  The decode premise is
   Rocq's verbatim (`InstrBytes.decode_fetch` ↦ `WeakFunnel.decodeFetch`,
   `priv_mSU` ↦ `privMSU`, `cfg_ok` ↦ `cfgOk`, `MISA_C` ↦ `misaC`); the
   agreement premise quantifies over a `RegFile`.
5. STATEMENT SHAPES (WeakInstr deviation 3): `A -∗ B -∗ ⌜φ⌝` is
   `A ⊢ B -∗ ⌜φ⌝`.  `wPEffLd8`'s base-register premise is stated at
   `(wflatSt σ).gpr rs1` (= `uxaXget σ.wmRegs rs1`, as `wPEffLw4`).
6. Lean-only helpers (file-qualified): `WeakLeafLd8.gprsNe`,
   `WeakLeafLd8.extendValueFalse64`, `WeakLeafLd8.fetchPinLd8`, and
   `WeakLeafLd8.confBytes`/`confDom` (the confined state's data bytes and
   domain, stated over an abstract window: instantiating them at
   `wwin pc ea 8` inline times out `whnf`).  The GPR-cell `reg_valid`/
   `reg_update` steps and Rocq's `iDestruct … as %` reuse
   `WeakLeafLw4.gprValid`/`gprUpdate`/`gprSetNe`/`keepPure2`/
   `winstrBytesNotRVC`.
7. Rocq §4 (the price accounting) is a comment; §5's `Print Assumptions` are
   not declarations.

**Rocq → Lean name map.**  `wcert_load_w` `wcertLoadW`, `wcert_load_w_4`
`wcertLoadW4`, `wcert_load8_base4` `wcertLoad8Base4`, `exec_eff_ld8_at`
`execEffLd8At`, `wP_eff_ld8` `wPEffLd8`, `wwp_ld8_leaf` `wwpLd8Leaf` (none in
the duplicated-name table).  Lean-only (file-qualified):
`WeakLeafLd8.gprsNe`, `WeakLeafLd8.extendValueFalse64`,
`WeakLeafLd8.fetchPinLd8`, `WeakLeafLd8.confBytes`, `WeakLeafLd8.confDom`.

**Dropped:** nothing (6 Rocq `Lemma`s; Lean 6 theorems + 5 Lean-only).
-/
import Weak.WeakLeafWin
import Weak.WeakLeafEff8
import Weak.WeakLeafLw4
import Weak.WeakWord8

namespace Weak

open Iris Iris.BI Iris.BI.MonPred Iris.ProofMode Iris.Std
open MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D LeanRV64D.Functions

/-! ## 1. THE WIDTH-GENERIC PLAIN-LOAD CERTIFICATE -/

/-- Rocq `wcert_load_w` (deviation 2): `WeakCert.wcertLoad`'s script with `4`
replaced by `n`. -/
theorem wcertLoadW (n : Nat) (cid : Nat) (pc : BitVec 64) (akf : AkInfo) (pf : PAddr) (nf : Nat)
    (akl : AkInfo) (ea : PAddr) :
    akl.akIfetch = false →
    wstepCert cid pc (wPEff (some cid) [.WEread akf pf nf, .WEread akl ea n]) (wQLoadW n ea) := by
  intro hcoh
  apply wstepCertEff
  intro s s' hi hl hws
  rw [weffsCons2, weffApplyRead, weffApplyRead] at hl hws
  rw [cohTsLog (wreadPost s akf pf (cohTs s pf nf)) s ea n (wreadPostLog _ _ _ _)] at hl hws
  rw [wreadPostLog, wreadPostLog] at hl
  rw [wreadPostWsWeak (wreadPost s akf pf (cohTs s pf nf)) akl ea (cohTs s ea n) hcoh] at hws
  unfold wQLoadW wVLoadW
  refine ⟨hi, hl, fun j hj => ?_⟩
  rw [hws, ← cohTsLookup s ea n j hj]
  exact loadPostRunGain (fun a t => viewByte a t) (wreadPost s akf pf (cohTs s pf nf)).wmWs akl.akSync
    (paZ ea) (cohTs s ea n) j (fun w a t => load_byte_gain w _ _ a t) (by rw [cohTsLength]; exact hj)

/-- Rocq `wcert_load_w_4`: `WeakCert.wcertLoad` is the `n := 4` instance. -/
theorem wcertLoadW4 (cid : Nat) (pc : BitVec 64) (akf : AkInfo) (pf : PAddr) (nf : Nat) (akl : AkInfo)
    (ea : PAddr) :
    akl.akIfetch = false →
    wstepCert cid pc (wPEff (some cid) [.WEread akf pf nf, .WEread akl ea 4]) (wQLoad ea) :=
  wcertLoadW 4 cid pc akf pf nf akl ea

/-- Rocq `wcert_load8_base4` (deviation 2): the width-8 instance at the fetch
element `WeakFetchEff` produces. -/
theorem wcertLoad8Base4 (cid : Nat) (pc : BitVec 64) (akl : AkInfo) (ea : PAddr) :
    akl.akIfetch = false →
    wstepCert cid pc
      (wPEff (some cid) ([.WEread WeakFetchEff.wakIfetch pc 4] ++ [.WEread akl ea 8])) (wQLoadW 8 ea) :=
  fun hcoh => wcertLoadW 8 cid pc WeakFetchEff.wakIfetch pc 4 akl ea hcoh

/-! ## 2. THE WINDOW AND THE `wPEff` HALF -/

/-- Lean-only: the GPRs are neither of the funnel's two pre-written registers. -/
theorem WeakLeafLd8.gprsNe : ∀ r ∈ uxaGprs, r ≠ .minstret_increment ∧ r ≠ .nextPC := by
  decide

/-- Lean-only: a signed 64-bit load value is itself. -/
theorem WeakLeafLd8.extendValueFalse64 (v : BitVec 64) : extend_value false v = v := by
  simp [extend_value, sign_extend_eq]

/-- Rocq `exec_eff_ld8_at` (deviations 1, 3): the LOAD's `execEff` fact at an
ARBITRARY state under the funnel's two pre-writes. -/
theorem execEffLd8At (s0 : ExecSt) (b : Bool) (pc : BitVec 64) (rs1 rd : BitVec 5) (imm : BitVec 12)
    (ea : PAddr) (v : BitVec 64) :
    rd.toNat ≠ 0 →
    s0.regs .cur_privilege = .Machine →
    (_get_Mstatus_MPRV (s0.regs .mstatus) == 1#1) = false →
    pmm_mode_backwards (_get_Seccfg_PMM (s0.regs .mseccfg)) = .PMM_Disabled →
    pmpAllOff (s0.regs .pmpcfg_n) →
    s0.regs .pma_regions = bootPMA →
    s0.regs .htif_tohost_base = none →
    s0.gpr rs1 + sign_extend (m := 64) imm = ea →
    is_aligned_paddr (.Physaddr ea) 8 = true →
    inRam ea 8 →
    BytesAt s0 ea 8 v →
    execEff (execute (.LOAD (imm, .Regidx rs1, .Regidx rd, false, 8)))
        ((s0.setReg .minstret_increment b).setReg .nextPC (Sail.BitVec.addInt pc 4)) =
      some (.Retire_Success (),
        ((s0.setReg .minstret_increment b).setReg .nextPC (Sail.BitVec.addInt pc 4)).setGpr rd v,
        [.WEread wakPlain ea 8]) := by
  intro hrd lpriv lmprv lpmm lpmp lpma lhtif hea hal hram hbytes
  -- every config register, moved past the funnel's two pre-writes
  have lpriv_s : ((s0.setReg .minstret_increment b).setReg .nextPC (Sail.BitVec.addInt pc 4)).regs
      .cur_privilege = .Machine := by
    leaf_peel .cur_privilege; exact lpriv
  have lms_s : ((s0.setReg .minstret_increment b).setReg .nextPC (Sail.BitVec.addInt pc 4)).regs
      .mstatus = s0.regs .mstatus := by
    leaf_peel .mstatus
  have lsec_s : ((s0.setReg .minstret_increment b).setReg .nextPC (Sail.BitVec.addInt pc 4)).regs
      .mseccfg = s0.regs .mseccfg := by
    leaf_peel .mseccfg
  have lpmpc_s : ((s0.setReg .minstret_increment b).setReg .nextPC (Sail.BitVec.addInt pc 4)).regs
      .pmpcfg_n = s0.regs .pmpcfg_n := by
    leaf_peel .pmpcfg_n
  have lpma_s : ((s0.setReg .minstret_increment b).setReg .nextPC (Sail.BitVec.addInt pc 4)).regs
      .pma_regions = s0.regs .pma_regions := by
    leaf_peel .pma_regions
  have lhtif_s : ((s0.setReg .minstret_increment b).setReg .nextPC (Sail.BitVec.addInt pc 4)).regs
      .htif_tohost_base = none := by
    leaf_peel .htif_tohost_base; exact lhtif
  -- the base register
  have hbase : ((s0.setReg .minstret_increment b).setReg .nextPC (Sail.BitVec.addInt pc 4)).gpr rs1 =
      s0.gpr rs1 :=
    uxaXget_congr _ _ (fun r hr => by
      rw [setLookupNe r .nextPC _ _ (WeakLeafLd8.gprsNe r hr).2,
        setLookupNe r .minstret_increment _ _ (WeakLeafLd8.gprsNe r hr).1]) rs1
  have hea' : ((s0.setReg .minstret_increment b).setReg .nextPC (Sail.BitVec.addInt pc 4)).gpr rs1 +
      sign_extend (m := 64) imm = ea := by rw [hbase]; exact hea
  have h := execEffExecuteLOAD8Gpr rs1 rd imm v ramRegion
    ((s0.setReg .minstret_increment b).setReg .nextPC (Sail.BitVec.addInt pc 4)) hrd lpriv_s
    (by rw [lms_s]; exact lmprv) (by rw [lsec_s]; exact lpmm) (by rw [hea']; exact hal)
    (by
      rw [hea']
      exact execEffPmpCheckMachineNone _ 8 _ _ (fun i => by rw [lpmpc_s]; exact (lpmp i).1))
    (by rw [lpma_s, lpma, hea']; exact matching_pma_ram ea 8 hram (by decide) (by decide))
    (by rw [hea']; exact hal)
    (by first | rfl | decide +kernel)
    (by rw [hea', within_clint_ram ea 8 hram]; rfl)
    (by
      first
      | rfl
      | (simp only [within_sig, plat_have_sig, Functions.not]; rfl))
    (by rw [hea']; exact execEffWithinHtifFalse _ 8 _ lhtif_s)
    (by rw [hea']; exact devAddrRam ea 8 hram)
    (by rw [hea']; exact hbytes)
  rw [hea', WeakLeafLd8.extendValueFalse64] at h
  exact h

/-- Lean-only (deviation 2): the O2 fetch obligation of the LOAD trace. -/
theorem WeakLeafLd8.fetchPinLd8 (σ : Wmstate) (pc : BitVec 64) (ea : PAddr) :
    (∀ j : Nat, j < 4 → fetchPinned σ (WeakInterp.accAddr pc j)) →
    fetchPin σ ([.WEread WeakFetchEff.wakIfetch pc 4] ++ [.WEread wakPlain ea 8]) := by
  intro h
  refine ⟨fun ak pa n hin hif j hj => ?_, by simp [fetchFresh, weffWrites]⟩
  simp only [List.singleton_append, List.mem_cons, Weff.WEread.injEq,
    List.not_mem_nil, or_false] at hin
  rcases hin with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · exact h j hj
  · simp [wakPlain] at hif



/-- Lean-only: a confined state carries the window's data bytes. -/
theorem WeakLeafLd8.confBytes (σ : Wmstate) (W : GSet PAddr) (ea : PAddr) (n : Nat)
    (v : BitVec (8 * n)) (hW : ∀ j : Nat, j < n → ea + BitVec.ofNat 64 j ∈ W)
    (h : ∀ j : Nat, j < n →
      wflatMem σ.wmImg σ.wmLog (ea + BitVec.ofNat 64 j) = some (nthByte v j)) :
    BytesAt (⟨σ.wmRegs, wmemRestrict σ W, σ.wmDev⟩ : ExecSt) ea n v :=
  fun j hj => wmemRestrictLookup σ W _ _ (hW j hj) (h j hj)

/-- Lean-only: a confined state's memory lives in its window. -/
theorem WeakLeafLd8.confDom (σ : Wmstate) (W : GSet PAddr) (regs : RegFile) (dev : DevStates) :
    bmDomSub (⟨regs, wmemRestrict σ W, dev⟩ : ExecSt).mem W :=
  wmemRestrictDom σ W

section wPEffHalf
variable {GF : BundledGFunctors} [WeakGS GF]

/-- Rocq `wP_eff_ld8` (deviations 1-3, 5). -/
theorem wPEffLd8 (cid : Nat) (σ : Wmstate) (pc : BitVec 64) (w : BitVec 32)
    (rs1 rd : BitVec 5) (imm : BitVec 12) (ea : PAddr) (v : BitVec 64) (dq : DFrac)
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
    rd.toNat ≠ 0 →
    (wflatSt σ).gpr rs1 + sign_extend (m := 64) imm = ea →
    inRam ea 8 →
    -- the decode
    (∀ r, D r = true → σ.wmRegs r = dst.regs r) →
    D .minstret_increment = false →
    goodb0 D (ext_decode w) dst = true →
    exec (ext_decode w) dst = some (.LOAD (imm, .Regidx rs1, .Regidx rd, false, 8), dst) →
    -- the resources
    wlatInterp (GF := GF) σ.wmImg σ.wmLog ⊢
      winstrBytes (GF := GF) pc (.F_Base w) -∗
      vwpHold (wpt8 (GF := GF) ea dq v) σ.wmWs -∗
      ⌜wPEff (some cid) ([.WEread WeakFetchEff.wakIfetch pc 4] ++ [.WEread wakPlain ea 8]) σ⌝ := by
  intro hwf lpc lpriv lpmp lpma lhtif lhart lmisaS lmIE lmprv lpmm lelp hal4 hnotRVC hrd hea hram8
    hagree hDmi hgood hdec
  iintro Hlat #Hbs Hpt
  ihave %haccpc := winstrBytesAccWf pc (.F_Base w) $$ Hbs
  icases keepPure (winstrBytesLookup σ pc (.F_Base w) hwf) $$ Hlat Hbs with ⟨%hfok, Hlat, -⟩
  icases keepPure (winstrTextPinned σ pc (.F_Base w) hwf) $$ Hlat Hbs with ⟨%htp, Hlat, -⟩
  icases keepPure1 (wpt8Align ea dq v σ.wmWs) $$ Hpt with ⟨%halea, Hpt⟩
  ihave %hld := wwpLd8 σ ea dq v hwf $$ Hlat Hpt
  ipureintro
  obtain ⟨⟨haccea, hpinea⟩, hflat8⟩ := hld
  obtain ⟨-, ⟨-, hrampc, w', ⟨hww, -⟩, htext⟩⟩ := hfok
  subst hww
  apply wPEffOfLeafBase cid σ (wwin pc ea 8) pc w (.LOAD (imm, .Regidx rs1, .Regidx rd, false, 8))
    [.WEread wakPlain ea 8] D dst hwf
    (wwinNonzero pc ea 8 (fun j hj => WeakLeafWin.inRamByte pc 4 j hrampc hj)
      (fun j hj => WeakLeafWin.inRamByte ea 8 j hram8 hj))
    (wwinPinned σ pc ea 8 haccpc haccea (fun j hj => (htp j hj).1) hpinea)
  · exact WeakLeafLd8.fetchPinLd8 σ pc ea (fun j hj => (htp j hj).2)
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
    have hfacts := loadSexecFacts ⟨σ.wmRegs, wmemRestrict σ (wwin pc ea 8), σ.wmDev⟩ b
      (BitVec.addInt pc 4) rd v
    have hea_c : (⟨σ.wmRegs, wmemRestrict σ (wwin pc ea 8), σ.wmDev⟩ : ExecSt).gpr rs1 +
        sign_extend (m := 64) imm = ea := by
      unfold ExecSt.gpr at hea ⊢; exact hea
    have hbytes_c := WeakLeafLd8.confBytes σ (wwin pc ea 8) ea 8 v
      (fun j hj => wwinData pc ea 8 j hj) hflat8
    have hrun := execEffLd8At ⟨σ.wmRegs, wmemRestrict σ (wwin pc ea 8), σ.wmDev⟩ b pc rs1 rd imm ea v
      hrd lpriv lmprv lpmm lpmp lpma lhtif hea_c halea hram8 hbytes_c
    refine ⟨_, hrun, ?_, ?_, ?_⟩
    · rw [hfacts.1]; exact lhart
    · exact hfacts.2.1
    · rw [hfacts.2.2.1]
      exact WeakLeafLd8.confDom σ (wwin pc ea 8) σ.wmRegs σ.wmDev

end wPEffHalf

/-! ## 3. THE LEAF -/

section leaf
variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [WeakGS GF]

/-- Rocq `wwp_ld8_leaf` (deviations 1-4). -/
theorem wwpLd8Leaf (gen : Nat) (cpu : CPU) (pc : BitVec 64) (w : BitVec 32)
    (rs1 rd : BitVec 5) (imm : BitVec 12) (ea : PAddr) (v : BitVec 64) (dqv : DFrac)
    (c : MConf) (dq : DFrac) (rs1v rd0 npc0 : BitVec 64) (D : Register → Bool) (dst : ExecSt)
    (ws : Wstate) :
    gen = 0 →
    MConf.mok c →
    pmpAllOff c.pmpcfg →
    is_aligned_vaddr (.Virtaddr pc) 4 = true →
    rs1.toNat ≠ 0 →
    rd.toNat ≠ 0 →
    rs1v + sign_extend (m := 64) imm = ea →
    inRam ea 8 →
    -- the decode, in the two shapes its two consumers ask for
    (∀ t : ExecSt,
      privMSU (t.regs .cur_privilege) = true →
      (_get_Misa_C (t.regs .misa) == 1#1) = true →
      (_get_Misa_A (t.regs .misa) == 1#1) = true →
      t.regs .misa = misaC →
      cfgOk t →
      exec (decodeFetch (.F_Base w)) t = some (.LOAD (imm, .Regidx rs1, .Regidx rd, false, 8), t)) →
    (∀ rs : RegFile,
      rs .cur_privilege = .Machine →
      rs .misa = misaC →
      rs .mseccfg = 0#64 →
      ∀ r, D r = true → rs r = dst.regs r) →
    D .minstret_increment = false →
    goodb0 D (ext_decode w) dst = true →
    exec (ext_decode w) dst = some (.LOAD (imm, .Regidx rs1, .Regidx rd, false, 8), dst) →
    mConf (GF := GF) cpu dq c ⊢
      clockCells cpu -∗
      Register.PC ↦ᵣ[cpu] pc -∗
      Register.nextPC ↦ᵣ[cpu] npc0 -∗
      gpr cpu rs1 (DFrac.own 1) rs1v -∗
      gpr cpu rd (DFrac.own 1) rd0 -∗
      winstrBytes (GF := GF) pc (.F_Base w) -∗
      hartWs (GF := GF) cpu ws -∗
      vwpHold (wpt8 (GF := GF) ea dqv v) ws -∗
      (∀ ws' : Wstate,
        ⌜wsLe ws ws'⌝ -∗
        mConf cpu dq c -∗
        clockCells cpu -∗
        pcIs cpu (BitVec.addInt pc 4) -∗
        gpr cpu rs1 (DFrac.own 1) rs1v -∗
        gpr cpu rd (DFrac.own 1) v -∗
        hartWs cpu ws' -∗
        vwpHold (wpt8 (GF := GF) ea dqv v) ws' -∗
        wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu)) -∗
      wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu) := by
  intro hgid hmok hpmp hal4 hrs1nz hrd hea hram8 hdecf hagree hDmi hgood hdec
  iintro Hm Hclk Hpc Hnpc Hrs1c Hrdc #Hbs Hhws Hpt Hcont
  ihave %haccpc := winstrBytesAccWf pc (.F_Base w) $$ Hbs
  ihave %hnotRVC := WeakLeafLw4.winstrBytesNotRVC pc w $$ Hbs
  have hdecW : winstrDec (.F_Base w) (.LOAD (imm, .Regidx rs1, .Regidx rd, false, 8)) := by
    intro t h1 h2 h3 h4 h5
    simp only [fetchIsRvc, Bool.false_eq_true, ↓reduceIte]
    exact hdecf t h1 h2 h3 h4 h5
  ihave #Hwi := winstrIntro (GF := GF) pc false (.LOAD (imm, .Regidx rs1, .Regidx rd, false, 8))
    (.F_Base w) (by first | rfl | decide) rfl hdecW $$ Hbs
  iapply wwpInstr gen cpu pc false (.LOAD (imm, .Regidx rs1, .Regidx rd, false, 8)) c dq
    (wPEff (some cpu.val) ([.WEread WeakFetchEff.wakIfetch pc 4] ++ [.WEread wakPlain ea 8]))
    (wQFr (wQLoadW 8 ea) (some cpu.val)
      ([.WEread WeakFetchEff.wakIfetch pc 4] ++ [.WEread wakPlain ea 8]))
    hgid haccpc hmok (fun i => (hpmp i).2)
    (wstepCertFr _ _ _ _ (wcertLoad8Base4 cpu.val pc wakPlain ea rfl)) $$ Hm Hclk Hpc Hwi
  unfold wwpCb
  iintro %σ %b %mt %ip %Lpc0 %hcfg Hlat Hreg Hnorg Hti Hip
  unfold wmstateNorg
  icases Hnorg with ⟨%hbnd, %hnv, %hwf, Hdev, Hlogauth, Hwsauth⟩
  ihave ⟨%hws, Hwsauth, Hhws⟩ := persistent_entails_right (hartWsAgree cpu σ.wmWs ws) $$ [Hwsauth Hhws]
  · iframe Hwsauth Hhws
  subst hws
  obtain ⟨Lpriv, Lhart, Lmisa, Lsec, Lpmpc, Lpma, Lhtif, LmisaS, LmIE, Lmprv, Lpmm, Lelp⟩ := hcfg
  icases keepPure (WeakLeafLw4.gprValid cpu _ rs1 _ rs1v hrs1nz) $$ Hreg Hrs1c with ⟨%Lrs1a, Hreg, Hrs1c⟩
  have Lrs1 : (wflatSt σ).gpr rs1 = rs1v := by
    rw [← WeakLeafLw4.gprSetNe (wflatSt σ) .minstret_increment b rs1 (by decide)]
    exact Lrs1a
  have hea_σ : (wflatSt σ).gpr rs1 + sign_extend (m := 64) imm = ea := by rw [Lrs1]; exact hea
  have hag_σ : ∀ r, D r = true → σ.wmRegs r = dst.regs r := hagree _ Lpriv Lmisa Lsec
  have lpmp_σ : pmpAllOff (σ.wmRegs .pmpcfg_n) := by rw [Lpmpc]; exact hpmp
  -- ---- the certificate's precondition (§2) ----
  icases WeakLeafLw4.keepPure2 (wPEffLd8 cpu.val σ pc w rs1 rd imm ea v dqv D dst hwf Lpc0 Lpriv lpmp_σ
      Lpma Lhtif Lhart LmisaS LmIE Lmprv Lpmm Lelp hal4 hnotRVC hrd hea_σ hram8 hag_σ hDmi hgood hdec)
    $$ Hlat Hbs Hpt with ⟨%HP, Hlat, -, Hpt⟩
  -- ---- the flat facts ----
  icases keepPure (wwpLd8 σ ea dqv v hwf) $$ Hlat Hpt with ⟨%hld, Hlat, Hpt⟩
  icases keepPure (winstrUnwritten σ pc (.F_Base w) hwf) $$ Hlat Hbs with ⟨%hunw, Hlat, -⟩
  icases keepPure (nvOkWpt8 cpu σ.wmImg σ.wmLog ea dqv v σ.wmWs) $$ Hlat Hpt with ⟨%hnvea, Hlat, Hpt⟩
  icases keepPure1 (wpt8Align ea dqv v σ.wmWs) $$ Hpt with ⟨%halea, Hpt⟩
  -- ---- the run, at the FLAT state ----
  have hexf := execEffLd8At (wflatSt σ) b pc rs1 rd imm ea v hrd Lpriv Lmprv Lpmm lpmp_σ Lpma Lhtif
    hea_σ halea hram8 hld.2
  have hfacts := loadSexecFacts (wflatSt σ) b (BitVec.addInt pc 4) rd v
  -- ---- the two register writes the `execute` performs ----
  imod (wand_intro (reg_update cpu _ .nextPC npc0 (BitVec.addInt pc 4))) $$ Hreg Hnpc with ⟨Hreg, Hnpc⟩
  rw [show (((wflatSt σ).setReg .minstret_increment b).regs.set .nextPC (BitVec.addInt pc 4)) =
      (((wflatSt σ).setReg .minstret_increment b).setReg .nextPC (BitVec.addInt pc 4)).regs from rfl]
  imod WeakLeafLw4.gprUpdate cpu (((wflatSt σ).setReg .minstret_increment b).setReg .nextPC
      (BitVec.addInt pc 4)) rd rd0 v hrd $$ Hreg Hrdc with ⟨Hreg, Hrdc⟩
  iapply fupd_mask_intro LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro; exact HP
  iexists ((((wflatSt σ).setReg .minstret_increment b).setReg .nextPC (BitVec.addInt pc 4)).setGpr rd v)
  isplitr
  · ipureintro; exact execEffExec _ _ _ _ _ hexf
  isplitl [Hreg]
  · iexact Hreg
  isplitl [Hti Hip]
  · iexists mt, ip
    iframe Hti Hip
  inext
  iintro %tick %σ' %t %hstep %hdevt0 %hpost %hQ Hm' Hclk' Hpc'
  have hdevt : t.dev = σ.wmDev := by rw [hdevt0, hfacts.2.2.2.1]; rfl
  obtain ⟨hregs, hdevs, hmems, himgs, hlogs, hwsle, hwf', hbnd'⟩ := hpost
  obtain ⟨⟨hQi, hQl, -⟩, hQeff⟩ := hQ
  imod hartWsUpdate cpu σ.wmWs σ.wmWs σ'.wmWs $$ [$Hwsauth $Hhws] with ⟨Hwsauth, Hhws⟩
  imod Hclose
  rw [hfacts.2.2.2.2]
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
        exact nvOkUnwritten _ _ _ (hunw j hj)
      · obtain ⟨j, hj, rfl⟩ := weffsTouchRead1 _ ea _ a ha
        exact hnvea j hj
    isplitr
    · ipureintro; exact hwf'
    rw [hdevs, hdevt, hQl]
    iframe Hdev Hlogauth Hwsauth
  ihave Hpt' := wwpLd8Carry σ σ' t ea dqv v ⟨hregs, hdevs, hmems, himgs, hlogs, hwsle, hwf', hbnd'⟩ $$ Hpt
  iapply Hcont $$ %σ'.wmWs %hwsle Hm' Hclk' [Hpc' Hnpc] Hrs1c Hrdc Hhws Hpt'
  unfold pcIs
  iframe Hpc' Hnpc

end leaf

end Weak
