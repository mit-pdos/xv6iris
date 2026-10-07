/-
Weak: **track F, the AxSL instruction bridge — PART D, second file** (`AxFetch3b`): the
COMPRESSED load/store (`c.ldsp` / `c.sdsp`) row runs.

Rocq: `iris/AxFetch.v` @ xxvzwolszwmp, lines 2158–2626 (§2.7).  Part D is `AxFetch3` (§2.5–§2.6),
this file (§2.7) and `AxFetch3c` (§2.8).

## What this file proves

* `execEffLd8OffAt`: the LOAD mirror of `WeakLeafSdspOff.execEffSd8OffAt` —
  `WeakLeafLd8.execEffLd8At` (which bakes `nextPC := pc + 4`) at the shifted argument `npc - 4`,
  the shift folded away, so it holds at EVERY successor pc (the compressed callers need `pc + 2`).
* `afSpUint`: `c.ldsp`/`c.sdsp`'s base register `sp = Regidx (zero_extend 0b10)` has index 2 —
  the one arithmetic fact that turns the generic GPR read at `sp`'s bits into `σ.wmRegs .x2`.
* `afCsdspRowShape` / `afCldspRowShape`: the row at position `k` carries the 8-byte data item
  (Stage C: no fetch item before it).
* `afCsdspRowRun` / `afCldspRowRun`: `afSd8RowRun` / `afLd8RowRun` (`AxFetch2`) with
  `execEffStepOfLeafRvc2` (`AxFetch3`, the 2-byte fetch at a 2-but-not-4-aligned pc) in place of
  `execEffStepOfLeafBase` and `execEffSd8OffAt` / `execEffLd8OffAt` (successor pc `pc + 2`) in
  place of `execEffSd8At` / `execEffLd8At`: from `riscvStep tick` at `k`, admin steps and the
  admin fetch (all at `k`) to the DATA node at `k`, and the data step to `k + 1`.

## Deviations from Rocq

1. NAMES / VOCABULARY: as `AxFetch3` deviation 1; the GPR read `if uint rs =? 0 then zero_reg
   else register_lookup …` at `wm_regs σ` ↦ `uxaXget σ.wmRegs rs`, at `s0` ↦ `s0.gpr rs`;
   `register_lookup (R_bitvector_64 (gpr_of_Z 2)) (wm_regs σ)` ↦ `σ.wmRegs .x2`;
   `zero_extend' 5 ('b"10")` ↦ `zero_extend (m := 5) 0b10#2` (Lean `sp`'s own payload);
   `regval_into_reg v` ↦ `v`; the result of a load is `….setGpr rd v` (`Weak/ExecSC` §1, equal
   to Rocq's `set_reg` under `uint rd ≠ 0`); the byte window of `exec_eff_ld8_off_at` is
   `BytesAt s0 ea 8 v`; `RETIRE_SUCCESS` ↦ `.Retire_Success ()`.  No name of this file is in
   `notes/weak-port-dupnames.json`.
2. O2 STAGE C (`AxFetch1` header): the row shapes lose their FETCH item and the pc argument
   (`afCsdspRowShape row k ea`, `afCldspRowShape row k ea`: the data item at `k`; Rocq: the
   fetch at `k`, the data at `S k`); the `Tt`/`img` parameters and the `fetch_answers` premises
   are gone; the runs end at the data node at `k` (Rocq `S k`) and the data step lands at
   `k + 1` (Rocq `S (S k)`); `afCsdspRowRun`'s data premise is at `row[k]?` (Rocq
   `row !! S k`).
3. THE ROUND-TRIP (Rocq step (c), via `InstrBytes.nth_byte_subrange_lo`) is not needed
   (`AxFetch2` deviation 3: `AxFetch2.fetchPeel` answers the admin fetch with whatever the RAM
   read returns).
4. `afSpUint` is proved by `decide` (Rocq `vm_compute`) and consumed by `simp only` (Rocq
   `rewrite`) where the GPR read at `sp`'s bits is collapsed; `sp` itself is matched against
   `Regidx (zero_extend …)` by conversion, as in Rocq.
5. `∀ j < 8, addr_is_ram (pa_add ea j)` ↦ `inRam ea 8`; `pa_add ea j ∈ W` ↦
   `ea + BitVec.ofNat 64 j ∈ W`.

Q7 (owner ruling, `notes/weak-port-q7-sfence.md` route (a), Lean-only): `afCsdspRowRun`/`afCldspRowRun` took `WeakEvLang.noSfAnn (riscvStep tick) ⟨…⟩` per tick; Q10: discharged (`AxFetch3.execEffStepOfLeafRvc2Sf` with the Lean-only twins `AxFetch3b.noSfAnnLd8OffAt`/`noSfAnnSd8OffAt`), the pre-Q7 statements restored.

**Rocq → Lean name map.**  `exec_eff_ld8_off_at` `execEffLd8OffAt`, `af_sp_uint` `afSpUint`
(Rocq `Local`), `af_csdsp_row_shape` `afCsdspRowShape`, `af_cldsp_row_shape` `afCldspRowShape`,
`af_csdsp_row_run` `afCsdspRowRun`, `af_cldsp_row_run` `afCldspRowRun`.

**Dropped (O2 Stage C: no fetch row item):** `af_csdsp_row_shape_fetch`,
`af_cldsp_row_shape_fetch` (projections onto the fetch item; `AxEpiChain.v` uses the latter
only to obtain the fetch item for its fetch step, which is admin in Lean).  Counts: Rocq 8
declarations in lines 2158–2626; Lean 6 + 1 Lean-only (`AxFetch3b.spGpr`, the GPR read at
`sp`'s bits is `x2`).
-/
import Weak.AxFetch3
import Weak.WeakLeafSdspOff

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open Sail Sail.ConcurrencyInterfaceV1
open Sail.ArchSem (FreeM)
open LeanRV64D LeanRV64D.Functions
open Wlabel

/-! ## 2.7 THE COMPRESSED LOAD/STORE (`c.ldsp` / `c.sdsp`) ROW RUNS -/

/-- Rocq `exec_eff_ld8_off_at` (deviation 1): `execEffLd8At` at the successor `npc - 4`, the
shift folded away — the load twin of `execEffSd8OffAt`. -/
theorem execEffLd8OffAt (s0 : ExecSt) (b : Bool) (npc : BitVec 64) (rs1 rd : BitVec 5)
    (imm : BitVec 12) (ea : PAddr) (v : BitVec 64) :
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
        ((s0.setReg .minstret_increment b).setReg .nextPC npc) =
      some (.Retire_Success (),
        ((s0.setReg .minstret_increment b).setReg .nextPC npc).setGpr rd v,
        [.WEread wakPlain ea 8]) := by
  intro hrd lpriv lmprv lpmm lpmp lpma lhtif hea hal hram hbytes
  have H := execEffLd8At s0 b (BitVec.addInt npc (-4)) rs1 rd imm ea v hrd lpriv lmprv lpmm lpmp
    lpma lhtif hea hal hram hbytes
  have hz : BitVec.addInt (BitVec.addInt npc (-4)) 4 = npc := by
    unfold BitVec.addInt
    rw [BitVec.add_assoc, show BitVec.ofInt 64 (-4) + BitVec.ofInt 64 4 = 0#64 by decide,
      BitVec.add_zero]
  rw [hz] at H
  exact H

/-- (Lean-only, Q10) `execEffLd8OffAt`'s `noSfAnn` twin. -/
theorem AxFetch3b.noSfAnnLd8OffAt (s0 : ExecSt) (b : Bool) (npc : BitVec 64) (rs1 rd : BitVec 5)
    (imm : BitVec 12) (ea : PAddr) (v : BitVec 64) :
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
    WeakEvLang.noSfAnn (execute (.LOAD (imm, .Regidx rs1, .Regidx rd, false, 8))) ((s0.setReg .minstret_increment b).setReg .nextPC npc) := by
  intro hrd lpriv lmprv lpmm lpmp lpma lhtif hea hal hram hbytes
  have H := AxFetch1.noSfAnnLd8At s0 b (BitVec.addInt npc (-4)) rs1 rd imm ea v hrd lpriv lmprv lpmm lpmp
    lpma lhtif hea hal hram hbytes
  have hz : BitVec.addInt (BitVec.addInt npc (-4)) 4 = npc := by
    unfold BitVec.addInt
    rw [BitVec.add_assoc, show BitVec.ofInt 64 (-4) + BitVec.ofInt 64 4 = 0#64 by decide,
      BitVec.add_zero]
  rw [hz] at H
  exact H


/-- (Lean-only, Q10) `execEffSd8OffAt`'s `noSfAnn` twin. -/
theorem AxFetch3b.noSfAnnSd8OffAt (s0 : ExecSt) (b : Bool) (npc : BitVec 64) (rs1 rs2 : BitVec 5)
    (imm : BitVec 12) (ea vs : BitVec 64) :
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
    WeakEvLang.noSfAnn (execute (.STORE (imm, .Regidx rs2, .Regidx rs1, 8))) ((s0.setReg .minstret_increment b).setReg .nextPC npc) := by
  intro lpriv lmprv lpmm lpmp lpma lhtif hea hvs hal hram
  have H := AxFetch2.noSfAnnSd8At s0 b (BitVec.addInt npc (-4)) rs1 rs2 imm ea vs lpriv lmprv lpmm lpmp lpma
    lhtif hea hvs hal hram
  have hz : BitVec.addInt (BitVec.addInt npc (-4)) 4 = npc := by
    unfold BitVec.addInt
    rw [BitVec.add_assoc, show BitVec.ofInt 64 (-4) + BitVec.ofInt 64 4 = 0#64 by decide,
      BitVec.add_zero]
  rw [hz] at H
  exact H


/-- Rocq `af_sp_uint` (deviation 4): `sp`'s payload is index 2. -/
theorem afSpUint : (zero_extend (m := 5) 0b10#2).toNat = 2 := by decide

/-- (Lean-only, deviation 4) The GPR read at `sp`'s bits is `x2`. -/
theorem AxFetch3b.spGpr (f : RegFile) : uxaXget f (zero_extend (m := 5) 0b10#2) = f .x2 := by
  simp only [uxaXget, afSpUint]

/-- The row at position `k` carries `c.sdsp`'s data item (Stage C: no fetch item before it). -/
def afCsdspRowShape (row : List Lbl) (k : Nat) (ea : Int) : Prop :=
  ∃ lbd, row[k]? = some lbd ∧ aident lbd = afSd8DataIdent ea

/-- The row at position `k` carries `c.ldsp`'s data item (Stage C: no fetch item before it). -/
def afCldspRowShape (row : List Lbl) (k : Nat) (ea : Int) : Prop :=
  ∃ lbd, row[k]? = some lbd ∧ aident lbd = afLd8DataIdent ea

/-- Rocq `af_csdsp_row_run` (deviations 1-5): `c.sdsp rs2, imm(sp)` — the 2-byte fetch (admin,
position kept) glued in front of the 8-byte data WRITE at `ea = sp + imm`. -/
theorem afCsdspRowRun (σ : Wmstate) (W : GSet PAddr) (pc : BitVec 64) (h : BitVec 16)
    (w : BitVec 32) (rs2 : BitVec 5) (imm : BitVec 12) (ea : PAddr) (vs : BitVec 64)
    (i0 : instruction) (D D0 : Register → Bool) (dst : ExecSt) (cpu : CPU) (row : List Lbl)
    (k : Nat) (ib0 : Ibch) :
    -- the M-mode config tower
    σ.wmRegs .PC = pc →
    σ.wmRegs .cur_privilege = .Machine →
    (_get_Mstatus_MPRV (σ.wmRegs .mstatus) == 1#1) = false →
    pmm_mode_backwards (_get_Seccfg_PMM (σ.wmRegs .mseccfg)) = .PMM_Disabled →
    pmpAllOff (σ.wmRegs .pmpcfg_n) →
    σ.wmRegs .pma_regions = bootPMA →
    σ.wmRegs .htif_tohost_base = none →
    σ.wmRegs .hart_state = .HART_ACTIVE () →
    (_get_Misa_S (σ.wmRegs .misa) == 1#1) = true →
    (_get_Misa_C (σ.wmRegs .misa) == 1#1) = true →
    (_get_Mstatus_MIE (σ.wmRegs .mstatus) == 1#1) = false →
    (σ.wmRegs .elp == landing_pad_bits_backwards .LP_EXPECTED) = false →
    -- the text word, in the confined memory, at a 2-but-not-4-aligned pc
    is_aligned_vaddr (.Virtaddr pc) 2 = true →
    is_aligned_vaddr (.Virtaddr pc) 4 = false →
    inRam pc 4 →
    (∀ j : Nat, j < 4 → wmemRestrict σ W (pc + BitVec.ofNat 64 j) = some (nthByte (n := 4) w j)) →
    Sail.BitVec.extractLsb w 15 0 = h →
    isRVC h = true →
    -- the COMPRESSED decode, and the expansion
    (∀ r, D r = true → σ.wmRegs r = dst.regs r) →
    D .minstret_increment = false →
    goodb0 D (ext_decode_compressed h) dst = true →
    exec (ext_decode_compressed h) dst = some (i0, dst) →
    (∀ s : ExecSt, goodb0 D0 (execute i0) s = true) →
    (∀ s : ExecSt, exec (execute i0) s = some (.ExecuteAs (.STORE (imm, .Regidx rs2, sp, 8)), s)) →
    -- c.sdsp's own geometry: `ea = sp + imm`
    σ.wmRegs .x2 + sign_extend (m := 64) imm = ea →
    uxaXget σ.wmRegs rs2 = vs →
    is_aligned_paddr (.Physaddr ea) 8 = true →
    inRam ea 8 →
    (∀ j : Nat, j < 8 → ea + BitVec.ofNat 64 j ∈ W) →
    -- the row's shape and the data item's value
    afCsdspRowShape row k (paZ ea) →
    (row[k]?).bind lblData = some (WeakInterpProj.wbytes 8 vs) →
    ∀ tick : Bool,
    ∃ (s3 : ExecSt) (ib3 : Ibch) (va : Nat)
      (req2 : Mem_write_request 8 va Arch.pa Arch.translation Arch.arch_ak)
      (KK2 : Result (Option Bool) Arch.abort → SailM Unit),
      classify req2.access_kind = wakPlain ∧ req2.pa = ea ∧
      rtc (fun t1 t2 => ∃ l, AxOpsem.astepProg row t1 l t2)
        ⟨.PHart cpu (riscvStep tick) σ.wmRegs none ib0, k⟩
        ⟨.PHart cpu (.impure (.ok (.memWrite 8 va req2)) KK2) s3.regs none ib3, k⟩ ∧
      AxOpsem.astepProg row
        ⟨.PHart cpu (.impure (.ok (.memWrite 8 va req2)) KK2) s3.regs none ib3, k⟩
        (LStore (classify req2.access_kind).akSync (paZ req2.pa) (WeakInterpProj.wbytes 8 vs)
          (depsAsrc (depsOfIb ib3.ibBits)) (depsVsrc (depsOfIb ib3.ibBits)))
        ⟨.PHart cpu (KK2 (.Ok (some true))) s3.regs none ib3, k + 1⟩ := by
  intro lpc lpriv lmprv lpmm lpmp lpma lhtif lhart lmisaS lmisaC lmIE lelp hal2 hal4 hram htext
    hsub hisRVC hagree hDmi hgood hdec hgood0 hexp hea hvs hal8 hram8 hwdom hshape hdat tick
  obtain ⟨lbd, hrowd, hidd⟩ := hshape
  have hea2 : (⟨σ.wmRegs, wmemRestrict σ W, σ.wmDev⟩ : ExecSt).gpr (zero_extend (m := 5) 0b10#2) +
      sign_extend (m := 64) imm = ea := by
    unfold ExecSt.gpr; rw [AxFetch3b.spGpr]; exact hea
  have hvs2 : (⟨σ.wmRegs, wmemRestrict σ W, σ.wmDev⟩ : ExecSt).gpr rs2 = vs := by
    unfold ExecSt.gpr; exact hvs
  -- (a) the combined fetch + data `execEff` fact for the whole instruction, sfence-free (Q10)
  obtain ⟨⟨t', hex, -⟩, hsf⟩ := AxFetch3.execEffStepOfLeafRvc2Sf σ W pc h w i0
    (.STORE (imm, .Regidx rs2, sp, 8)) [.WEwrite wakPlain ea 8 vs] D D0 dst
    lpc lpriv (fun i => (lpmp i).2) lpma lhtif lhart lmisaS lmisaC lmIE lelp hal2 hal4 hram htext
    hsub hisRVC hagree hDmi hgood hdec hgood0 hexp
    (by
      intro b
      have hfacts := storeRegsFacts ⟨σ.wmRegs, wmemRestrict σ W, σ.wmDev⟩ b (BitVec.addInt pc 2)
      refine ⟨_, execEffSd8OffAt ⟨σ.wmRegs, wmemRestrict σ W, σ.wmDev⟩ b (BitVec.addInt pc 2)
        (zero_extend (m := 5) 0b10#2) rs2 imm ea vs lpriv lmprv lpmm lpmp lpma lhtif hea2 hvs2
        hal8 hram8, ?_, ?_, ?_⟩
      · exact hfacts.1.trans lhart
      · exact hfacts.2.1
      · dsimp only
        exact writeBytesDomSub _ ea 8 vs W (wmemRestrictDom σ W) hwdom)
    (fun b => AxFetch3b.noSfAnnSd8OffAt ⟨σ.wmRegs, wmemRestrict σ W, σ.wmDev⟩ b (BitVec.addInt pc 2)
      (zero_extend (m := 5) 0b10#2) rs2 imm ea vs lpriv lmprv lpmm lpmp lpma lhtif hea2 hvs2 hal8 hram8)
    tick
  -- (b) the admin run to the (width-2) fetch node and the admin fetch step (position kept)
  obtain ⟨m2, s2, ib2, -, hex2, hrtcb, hsf2⟩ :=
    AxFetch2.fetchPeel (riscvStep tick) ⟨σ.wmRegs, wmemRestrict σ W, σ.wmDev⟩ ib0
      WeakFetchEff.wakIfetch pc 2 t' [.WEwrite wakPlain ea 8 vs] cpu k row (by decide) rfl hex hsf
  -- (d) the admin run to the data (write) node, then the data event
  obtain ⟨s3, ib3, va, req2, KK2, hcld, hpad, hvald, hdevd, -, -, hrtcd⟩ :=
    afAdminRunToMemwrite m2 s2 ib2 wakPlain ea 8 vs t' [] (by decide) hex2 hsf2 cpu k row
  refine ⟨s3, ib3, va, req2, KK2, hcld, hpad, rtc_transitive hrtcb hrtcd, ?_⟩
  exact afAstepWriteOfMemwrite row cpu 8 va req2 KK2 s3.regs ib3 (efInit s3.dev) k lbd vs
    (by rw [hpad]; exact hdevd) (by decide) (by rw [hcld]; rfl) hvald hrowd
    (by rw [hidd, hcld, hpad]; rfl) (by rw [hrowd] at hdat; exact hdat)

/-- Rocq `af_cldsp_row_run` (deviations 1-5): `c.ldsp rd, imm(sp)` — the 2-byte fetch (admin,
position kept) glued in front of the 8-byte data READ at `ea = sp + imm`. -/
theorem afCldspRowRun (σ : Wmstate) (W : GSet PAddr) (pc : BitVec 64) (h : BitVec 16)
    (w : BitVec 32) (rd : BitVec 5) (imm : BitVec 12) (ea : PAddr) (v : BitVec 64)
    (i0 : instruction) (D D0 : Register → Bool) (dst : ExecSt) (cpu : CPU) (row : List Lbl)
    (k : Nat) (ib0 : Ibch) :
    -- the M-mode config tower
    σ.wmRegs .PC = pc →
    σ.wmRegs .cur_privilege = .Machine →
    (_get_Mstatus_MPRV (σ.wmRegs .mstatus) == 1#1) = false →
    pmm_mode_backwards (_get_Seccfg_PMM (σ.wmRegs .mseccfg)) = .PMM_Disabled →
    pmpAllOff (σ.wmRegs .pmpcfg_n) →
    σ.wmRegs .pma_regions = bootPMA →
    σ.wmRegs .htif_tohost_base = none →
    σ.wmRegs .hart_state = .HART_ACTIVE () →
    (_get_Misa_S (σ.wmRegs .misa) == 1#1) = true →
    (_get_Misa_C (σ.wmRegs .misa) == 1#1) = true →
    (_get_Mstatus_MIE (σ.wmRegs .mstatus) == 1#1) = false →
    (σ.wmRegs .elp == landing_pad_bits_backwards .LP_EXPECTED) = false →
    -- the text word, in the confined memory, at a 2-but-not-4-aligned pc
    is_aligned_vaddr (.Virtaddr pc) 2 = true →
    is_aligned_vaddr (.Virtaddr pc) 4 = false →
    inRam pc 4 →
    (∀ j : Nat, j < 4 → wmemRestrict σ W (pc + BitVec.ofNat 64 j) = some (nthByte (n := 4) w j)) →
    Sail.BitVec.extractLsb w 15 0 = h →
    isRVC h = true →
    -- the COMPRESSED decode, and the expansion
    (∀ r, D r = true → σ.wmRegs r = dst.regs r) →
    D .minstret_increment = false →
    goodb0 D (ext_decode_compressed h) dst = true →
    exec (ext_decode_compressed h) dst = some (i0, dst) →
    (∀ s : ExecSt, goodb0 D0 (execute i0) s = true) →
    (∀ s : ExecSt, exec (execute i0) s =
      some (.ExecuteAs (.LOAD (imm, sp, .Regidx rd, false, 8)), s)) →
    -- c.ldsp's own geometry: `ea = sp + imm`, `rd ≠ x0`
    rd.toNat ≠ 0 →
    σ.wmRegs .x2 + sign_extend (m := 64) imm = ea →
    is_aligned_paddr (.Physaddr ea) 8 = true →
    inRam ea 8 →
    (∀ j : Nat, j < 8 → wmemRestrict σ W (ea + BitVec.ofNat 64 j) = some (nthByte (n := 8) v j)) →
    -- the row's shape
    afCldspRowShape row k (paZ ea) →
    ∀ tick : Bool,
    ∃ (s3 : ExecSt) (ib3 : Ibch) (va : Nat)
      (req2 : Mem_read_request 8 va Arch.pa Arch.translation Arch.arch_ak)
      (KK2 : Result (BitVec (8 * 8) × Option Bool) Arch.abort → SailM Unit),
      classify req2.access_kind = wakPlain ∧ req2.pa = ea ∧
      rtc (fun t1 t2 => ∃ l, AxOpsem.astepProg row t1 l t2)
        ⟨.PHart cpu (riscvStep tick) σ.wmRegs none ib0, k⟩
        ⟨.PHart cpu (.impure (.ok (.memRead 8 va req2)) KK2) s3.regs none ib3, k⟩ ∧
      areadStep row ⟨.PHart cpu (.impure (.ok (.memRead 8 va req2)) KK2) s3.regs none ib3, k⟩
        (.IRead (classify req2.access_kind).akSync (paZ req2.pa) 8)
        (fun vs => ⟨.PHart cpu (KK2 (.Ok (wordOfBytes 8 vs, none))) s3.regs none ib3, k + 1⟩) := by
  intro lpc lpriv lmprv lpmm lpmp lpma lhtif lhart lmisaS lmisaC lmIE lelp hal2 hal4 hram htext
    hsub hisRVC hagree hDmi hgood hdec hgood0 hexp hrd hea hal8 hram8 hbytes8 hshape tick
  obtain ⟨lbd, hrowd, hidd⟩ := hshape
  have hea2 : (⟨σ.wmRegs, wmemRestrict σ W, σ.wmDev⟩ : ExecSt).gpr (zero_extend (m := 5) 0b10#2) +
      sign_extend (m := 64) imm = ea := by
    unfold ExecSt.gpr; rw [AxFetch3b.spGpr]; exact hea
  -- (a) the combined fetch + data `execEff` fact for the whole instruction, sfence-free (Q10)
  obtain ⟨⟨t', hex, -⟩, hsf⟩ := AxFetch3.execEffStepOfLeafRvc2Sf σ W pc h w i0
    (.LOAD (imm, sp, .Regidx rd, false, 8)) [.WEread wakPlain ea 8] D D0 dst
    lpc lpriv (fun i => (lpmp i).2) lpma lhtif lhart lmisaS lmisaC lmIE lelp hal2 hal4 hram htext
    hsub hisRVC hagree hDmi hgood hdec hgood0 hexp
    (by
      intro b
      have hfacts := loadSexecFacts ⟨σ.wmRegs, wmemRestrict σ W, σ.wmDev⟩ b (BitVec.addInt pc 2)
        rd v
      have hbytes_c : BytesAt (⟨σ.wmRegs, wmemRestrict σ W, σ.wmDev⟩ : ExecSt) ea 8 v :=
        fun j hj => hbytes8 j hj
      refine ⟨_, execEffLd8OffAt ⟨σ.wmRegs, wmemRestrict σ W, σ.wmDev⟩ b (BitVec.addInt pc 2)
        (zero_extend (m := 5) 0b10#2) rd imm ea v hrd lpriv lmprv lpmm lpmp lpma lhtif hea2 hal8
        hram8 hbytes_c, ?_, ?_, ?_⟩
      · rw [hfacts.1]; exact lhart
      · exact hfacts.2.1
      · rw [hfacts.2.2.1]
        exact WeakLeafLd8.confDom σ W σ.wmRegs σ.wmDev)
    (fun b => AxFetch3b.noSfAnnLd8OffAt ⟨σ.wmRegs, wmemRestrict σ W, σ.wmDev⟩ b (BitVec.addInt pc 2)
      (zero_extend (m := 5) 0b10#2) rd imm ea v hrd lpriv lmprv lpmm lpmp lpma lhtif hea2 hal8
      hram8 (fun j hj => hbytes8 j hj))
    tick
  -- (b) the admin run to the (width-2) fetch node and the admin fetch step (position kept)
  obtain ⟨m2, s2, ib2, -, hex2, hrtcb, hsf2⟩ :=
    AxFetch2.fetchPeel (riscvStep tick) ⟨σ.wmRegs, wmemRestrict σ W, σ.wmDev⟩ ib0
      WeakFetchEff.wakIfetch pc 2 t' [.WEread wakPlain ea 8] cpu k row (by decide) rfl hex hsf
  -- (d) the admin run to the data node, then the data event
  obtain ⟨s3, ib3, va, req2, KK2, hcld, hpad, hdevd, -, -, hrtcd, -⟩ :=
    afAdminRunToMemread m2 s2 ib2 wakPlain ea 8 t' [] (by decide) hex2 hsf2 cpu k row
  refine ⟨s3, ib3, va, req2, KK2, hcld, hpad, rtc_transitive hrtcb hrtcd, ?_⟩
  exact afAreadStepOfMemread row cpu 8 va req2 KK2 s3.regs ib3 (efInit s3.dev) k lbd
    (by rw [hpad]; exact hdevd) (by rw [hcld]; rfl) (by rw [hcld]; rfl) hrowd
    (by rw [hidd, hcld, hpad]; rfl)

end Weak
