/-
Weak: **track F, the AxSL instruction bridge — PART C** (`AxFetch2`): the WHOLE-INSTRUCTION row
runs of `ld8` and `sd8` against the REAL `riscvStep tick` term, and the `sd8` data-event
instantiation.

Rocq: `iris/AxFetch.v` @ xxvzwolszwmp, lines 1056–1532 (§2.2 the ld8 row run, §2.3 the sd8
instantiation, §2.4 the sd8 row run).  Part A is `Weak/AxFetch1.lean` (its header carries the
whole port's summary and the O2 Stage C account); part D (§2.5 onwards) imports this file.

## What this file proves

* `AxFetch2.fetchPeel` (Lean-only, the reusable core of every row run): if `execEff m s` runs to
  a trace whose first effect is an i-cache read `.WEread ak pa n` (`ak.akIfetch = true`,
  `n ≠ 0`), then opax steps that KEEP the row position (the admin peel `afAdminRunToMemread`,
  then the ADMIN fetch step `afAstepFetchOfMemread`) reach a continuation `m2` at a state `s2`
  with the same memory whose `execEff` runs to the REST of the trace.
* §2.2 `afLd8RowRun`: from the hart at `riscvStep tick` at row position `k`, a run (admin steps
  and the admin fetch, all at `k`) to the `ld8` DATA `memRead` node at `k`, and that node's
  `areadStep` to `k + 1`.  Composition: (a) `execEffStepOfLeafBase` at the LOAD (the whole
  instruction's `execEff` fact, fed by `execEffLd8At`); (b) `AxFetch2.fetchPeel`; (d)
  `afAdminRunToMemread` a second time to the data node, then `afAreadStepOfMemread`.
* §2.3 `afSd8RunToWrite`: the store twin of `afLd8RunToRead` — the admin run from the
  bind-embedded `execute (STORE …)` to the data `memWrite` node and its eager `astepProg` (the
  `LStore` step, `k → k + 1`).
* §2.4 `afSd8RowRun`: the store twin of §2.2 (the data half peeled by `afAdminRunToMemwrite`,
  closed by `afAstepWriteOfMemwrite`).

## Deviations from Rocq

1. NAMES / VOCABULARY: as `AxFetch1` deviation 1, and as `WeakLeafLd8`/`WeakLeafSd8` deviation 1
   (`register_lookup r (wm_regs σ)` ↦ `σ.wmRegs r`; the GPR read `if uint rs =? 0 then zero_reg
   else …` at `wm_regs σ` ↦ `uxaXget σ.wmRegs rs`, at `s0` ↦ `s0.gpr rs`;
   `wmem_restrict σ W !! pa_add a j` ↦ `wmemRestrict σ W (a + BitVec.ofNat 64 j)`; `nth_byte` ↦
   `nthByte`; `pa_add ea j ∈ W` ↦ `ea + BitVec.ofNat 64 j ∈ W`; `row !! S k ≫= lbl_data` ↦
   `(row[k]?).bind lblData`).  The data bytes of `afLd8RowRun` are `BytesAt`'s per-byte form
   over the confined memory.  No name of this file is in `notes/weak-port-dupnames.json`.
2. O2 STAGE C (`AxFetch1` header): the fetch is an ADMIN step that keeps the row position.  So
   (i) the `Tt`/`img` parameters and the `fetch_answers Tt img (pa_z pc) (tag_vals (wbytes 4 w))`
   premise are gone; (ii) the row shapes have no fetch item (`afLd8RowShape row k (paZ ea)`, the
   pc argument dropped), the DATA item sits at `k`; (iii) the run ends at the data node at `k`
   (Rocq `S k`) and the data step lands at `k + 1` (Rocq `S (S k)`); `afSd8RowRun`'s data
   premise is at `row[k]?` (Rocq `row !! S k`).
3. THE ROUND-TRIP (Rocq step (c)) is not needed: Rocq FIXED the fetch oracle's answer to the
   real text bytes `wbytes 4 w` and so had to show the small-step RAM read at the fetch node
   returns `w` (`read_bytes_of_bytes` over the peel's `.mem`-invariance).  In Lean the admin
   fetch step accepts ANY byte list of the width, so `AxFetch2.fetchPeel` answers it with the
   bytes of the word the RAM read actually returns (`wordOfBytesWbytes`), whatever it is.  The
   text premises stay (they feed `execEffStepOfLeafBase`).
4. The fetch's trace element is `.WEread WeakFetchEff.wakIfetch pc 4` (Rocq `wak_plain`;
   `WeakFetchEff` deviation 2); RAM/PMA/PMP premises as `WeakLeafLd8` deviation 3 (`inRam pc 4`,
   `inRam ea 8`, `pma_regions = bootPMA`, `pmpAllOff`); `is_lpad_instruction` (an extra premise of
   the Lean `execEffStepOfLeafBase`) is discharged inside.
5. `afSd8RunToWrite`'s premises are `execEffSd8At`'s (`s0.gpr rs1 + sign_extend imm = ea`,
   `s0.gpr rs2 = vs`, `inRam ea 8`); the embedding is `execute (…) >>= fun _ => pure ()`.
6. Lean-only helper (file-qualified): `AxFetch2.fetchPeel` (above; part D's jalr / c.jr / RVC
   runs reuse it).

Q7 (owner ruling, `notes/weak-port-q7-sfence.md` route (a), Lean-only): `AxFetch2.fetchPeel` takes and propagates `WeakEvLang.noSfAnn` (AxFetch1); the row runs (`afLd8RowRun`, `afSd8RowRun`) take `noSfAnn (riscvStep tick) ⟨…⟩` per tick and `afSd8RunToWrite` for its `execute` run.  NOT discharged: the announce word on `riscvStep`'s path is fixed only inside the leaf assembly (`WeakEffSkel`), whose components (fetch, decode, `execute i`) would each need a path fact.

**Rocq → Lean name map.**  `af_ld8_row_run` `afLd8RowRun`, `af_sd8_run_to_write`
`afSd8RunToWrite`, `af_sd8_row_run` `afSd8RowRun`.

**Dropped:** nothing.  Counts: Rocq 3 lemmas in lines 1056–1532; Lean 3 + 1 Lean-only.
-/
import Weak.AxFetch1
import Weak.WeakFetchEff
import Weak.WeakLeafSd8

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open Sail Sail.ConcurrencyInterfaceV1
open Sail.ArchSem (FreeM)
open LeanRV64D LeanRV64D.Functions
open Wlabel

/-! ## THE FETCH PEEL (Lean-only, deviation 3) -/

/-- (Lean-only) THE FETCH PEEL: an `execEff` run whose first effect is an i-cache read is, at the
opax level, a position-keeping run (admin peel + the admin fetch) to a continuation whose
`execEff` runs to the rest of the trace, at a state with the same memory. -/
theorem AxFetch2.fetchPeel (m : SailM Unit) (s : ExecSt) (ib : Ibch) (ak : AkInfo) (pa : PAddr)
    (n : Nat) (s' : ExecSt) (es : List Weff) (cpu : CPU) (kpos : Nat) (row : List Lbl) :
    n ≠ 0 → ak.akIfetch = true →
    execEff m s = some ((), s', .WEread ak pa n :: es) →
    WeakEvLang.noSfAnn m s →
    ∃ (m2 : SailM Unit) (s2 : ExecSt) (ib2 : Ibch),
      s2.mem = s.mem ∧ execEff m2 s2 = some ((), s', es) ∧
      rtc (fun t1 t2 => ∃ l, AxOpsem.astepProg row t1 l t2)
        ⟨.PHart cpu m s.regs none ib, kpos⟩ ⟨.PHart cpu m2 s2.regs none ib2, kpos⟩ ∧
      WeakEvLang.noSfAnn m2 s2 := by
  intro hn hfe hex hsf
  obtain ⟨s2, ib2, va, req, KK, hcl, hpa, hdev, hmem, hee, hrtc, hns⟩ :=
    afAdminRunToMemread m s ib ak pa n s' es hn hex hsf cpu kpos row
  have hdev' : devAddr req.pa = false := by rw [hpa]; exact hdev
  have hm : mmioAcc req.pa n = false := by simp [mmioAcc, hdev']
  simp only [execEff, hm, Bool.false_eq_true, ↓reduceIte] at hee
  cases hrb : bmRead s2.mem req.pa n with
  | none => simp only [hrb] at hee; cases hee
  | some w0 =>
    simp only [hrb] at hee
    obtain ⟨es0, h0, hcons⟩ := Weff.consEqSome.1 hee
    have hes : es = es0 := (List.cons.inj hcons).2
    subst hes
    have hst := afAstepFetchOfMemread row cpu n va req KK s2.regs ib2 (efInit s2.dev) kpos
      (WeakInterpProj.wbytes n w0) hdev' (by rw [hcl]; exact hfe) (wbytesLength n w0)
    rw [wordOfBytesWbytes] at hst
    simp only [WeakEvLang.noSfAnn, hm, hrb, Bool.false_eq_true, ↓reduceIte] at hns
    exact ⟨KK (.Ok (w0, none)), s2, ib2, hmem, h0, rtc_r hrtc ⟨_, hst⟩, hns⟩

/-! ## 2.2 THE ld8 ROW RUN: the fetch glued in front of the data read, at `riscvStep tick` -/

/-- Rocq `af_ld8_row_run` (deviations 1-4): from the hart at `riscvStep tick` at the row's
position `k`, a run to the `ld8` DATA `memRead` node, still at `k` (the fetch is admin), and the
data event's `areadStep` to `k + 1`. -/
theorem afLd8RowRun (σ : Wmstate) (W : GSet PAddr) (pc : BitVec 64) (w : BitVec 32)
    (rs1 rd : BitVec 5) (imm : BitVec 12) (ea : PAddr) (v : BitVec 64)
    (D : Register → Bool) (dst : ExecSt) (cpu : CPU) (row : List Lbl) (k : Nat) (ib0 : Ibch) :
    -- the M-mode config tower
    σ.wmRegs .PC = pc →
    σ.wmRegs .cur_privilege = .Machine →
    pmpAllOff (σ.wmRegs .pmpcfg_n) →
    σ.wmRegs .pma_regions = bootPMA →
    σ.wmRegs .htif_tohost_base = none →
    σ.wmRegs .hart_state = .HART_ACTIVE () →
    (_get_Misa_S (σ.wmRegs .misa) == 1#1) = true →
    (_get_Mstatus_MIE (σ.wmRegs .mstatus) == 1#1) = false →
    (σ.wmRegs .elp == landing_pad_bits_backwards .LP_EXPECTED) = false →
    (_get_Mstatus_MPRV (σ.wmRegs .mstatus) == 1#1) = false →
    pmm_mode_backwards (_get_Seccfg_PMM (σ.wmRegs .mseccfg)) = .PMM_Disabled →
    -- the text word, in the confined memory, at a 4-aligned pc
    is_aligned_vaddr (.Virtaddr pc) 4 = true →
    inRam pc 4 →
    (∀ j : Nat, j < 4 → wmemRestrict σ W (pc + BitVec.ofNat 64 j) = some (nthByte (n := 4) w j)) →
    isRVC (Sail.BitVec.extractLsb w 15 0) = false →
    -- the decode
    (∀ r, D r = true → σ.wmRegs r = dst.regs r) →
    D .minstret_increment = false →
    goodb0 D (ext_decode w) dst = true →
    exec (ext_decode w) dst = some (.LOAD (imm, .Regidx rs1, .Regidx rd, false, 8), dst) →
    -- ld8's own geometry
    rd.toNat ≠ 0 →
    uxaXget σ.wmRegs rs1 + sign_extend (m := 64) imm = ea →
    is_aligned_paddr (.Physaddr ea) 8 = true →
    inRam ea 8 →
    (∀ j : Nat, j < 8 → wmemRestrict σ W (ea + BitVec.ofNat 64 j) = some (nthByte (n := 8) v j)) →
    -- the row's shape
    afLd8RowShape row k (paZ ea) →
    ∀ tick : Bool,
    -- Q7: the instruction's run announces no sfence.vma word (header, Q7)
    WeakEvLang.noSfAnn (riscvStep tick) ⟨σ.wmRegs, wmemRestrict σ W, σ.wmDev⟩ →
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
  intro lpc lpriv lpmp lpma lhtif lhart lmisaS lmIE lelp lmprv lpmm hal hram4 htext hnotRVC
    hagree hDmi hgood hdec hrd hea hal8 hram8 hbytes8 hshape tick hsf
  obtain ⟨lbd, hrowd, hidd⟩ := hshape
  -- (a) the whole instruction's `execEff` fact
  obtain ⟨t', hex, -⟩ := execEffStepOfLeafBase σ W pc w
    (.LOAD (imm, .Regidx rs1, .Regidx rd, false, 8)) [.WEread wakPlain ea 8] D dst
    lpc lpriv (fun i => (lpmp i).2) lpma lhtif lhart lmisaS lmIE lelp hal hram4 htext hnotRVC
    hagree hDmi hgood hdec (by first | rfl | decide)
    (by
      intro b
      have hfacts := loadSexecFacts ⟨σ.wmRegs, wmemRestrict σ W, σ.wmDev⟩ b
        (Sail.BitVec.addInt pc 4) rd v
      have hea_c : (⟨σ.wmRegs, wmemRestrict σ W, σ.wmDev⟩ : ExecSt).gpr rs1 +
          sign_extend (m := 64) imm = ea := by
        unfold ExecSt.gpr; exact hea
      have hbytes_c : BytesAt (⟨σ.wmRegs, wmemRestrict σ W, σ.wmDev⟩ : ExecSt) ea 8 v :=
        fun j hj => hbytes8 j hj
      have hrun := execEffLd8At ⟨σ.wmRegs, wmemRestrict σ W, σ.wmDev⟩ b pc rs1 rd imm ea v
        hrd lpriv lmprv lpmm lpmp lpma lhtif hea_c hal8 hram8 hbytes_c
      refine ⟨_, hrun, ?_, ?_, ?_⟩
      · rw [hfacts.1]; exact lhart
      · exact hfacts.2.1
      · rw [hfacts.2.2.1]
        exact WeakLeafLd8.confDom σ W σ.wmRegs σ.wmDev)
    tick
  -- (b) the admin run to the fetch node and the admin fetch step (position kept)
  obtain ⟨m2, s2, ib2, -, hex2, hrtcb, hsf2⟩ :=
    AxFetch2.fetchPeel (riscvStep tick) ⟨σ.wmRegs, wmemRestrict σ W, σ.wmDev⟩ ib0
      WeakFetchEff.wakIfetch pc 4 t' [.WEread wakPlain ea 8] cpu k row (by decide) rfl hex hsf
  -- (d) the admin run to the data node, then the data event
  obtain ⟨s3, ib3, va, req2, KK2, hcld, hpad, hdevd, -, -, hrtcd, -⟩ :=
    afAdminRunToMemread m2 s2 ib2 wakPlain ea 8 t' [] (by decide) hex2 hsf2 cpu k row
  refine ⟨s3, ib3, va, req2, KK2, hcld, hpad, rtc_transitive hrtcb hrtcd, ?_⟩
  exact afAreadStepOfMemread row cpu 8 va req2 KK2 s3.regs ib3 (efInit s3.dev) k lbd
    (by rw [hpad]; exact hdevd) (by rw [hcld]; rfl) (by rw [hcld]; rfl) hrowd
    (by rw [hidd, hcld, hpad]; rfl)

/-! ## 2.3 THE sd8 INSTANTIATION: the REAL `execute (STORE …)` term -/

/-- Rocq `af_sd8_run_to_write` (deviations 1, 2, 5): the admin run from the bind-embedded
`execute (STORE …)` to the data `memWrite` node, and the eager data step `k → k + 1`. -/
theorem afSd8RunToWrite (s0 : ExecSt) (b : Bool) (pc : BitVec 64) (rs1 rs2 : BitVec 5)
    (imm : BitVec 12) (ea : PAddr) (vs : BitVec 64) (cpu : CPU) (row : List Lbl) (ib : Ibch)
    (k : Nat) (lb : Lbl) :
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
    row[k]? = some lb →
    aident lb = .IWrite false (paZ ea) 8 →
    lblData lb = some (WeakInterpProj.wbytes 8 vs) →
    -- Q7: the run announces no sfence.vma word (header, Q7)
    WeakEvLang.noSfAnn
      (execute (.STORE (imm, .Regidx rs2, .Regidx rs1, 8)) >>= fun _ => (pure () : SailM Unit))
      ((s0.setReg .minstret_increment b).setReg .nextPC (Sail.BitVec.addInt pc 4)) →
    ∃ (s2 : ExecSt) (ib2 : Ibch) (va : Nat)
      (req : Mem_write_request 8 va Arch.pa Arch.translation Arch.arch_ak)
      (KK : Result (Option Bool) Arch.abort → SailM Unit),
      classify req.access_kind = wakPlain ∧ req.pa = ea ∧
      rtc (fun t1 t2 => ∃ l, AxOpsem.astepProg row t1 l t2)
        ⟨.PHart cpu (execute (.STORE (imm, .Regidx rs2, .Regidx rs1, 8)) >>= fun _ => pure ())
          ((s0.setReg .minstret_increment b).setReg .nextPC (Sail.BitVec.addInt pc 4)).regs
          none ib, k⟩
        ⟨.PHart cpu (.impure (.ok (.memWrite 8 va req)) KK) s2.regs none ib2, k⟩ ∧
      AxOpsem.astepProg row ⟨.PHart cpu (.impure (.ok (.memWrite 8 va req)) KK) s2.regs none ib2, k⟩
        (LStore (classify req.access_kind).akSync (paZ req.pa) (WeakInterpProj.wbytes 8 vs)
          (depsAsrc (depsOfIb ib2.ibBits)) (depsVsrc (depsOfIb ib2.ibBits)))
        ⟨.PHart cpu (KK (.Ok (some true))) s2.regs none ib2, k + 1⟩ := by
  intro lpriv lmprv lpmm lpmp lpma lhtif hea hvs hal hram hrow hid hdat hsf
  have hm0 := execEffSd8At s0 b pc rs1 rs2 imm ea vs lpriv lmprv lpmm lpmp lpma lhtif hea hvs hal
    hram
  have hex := execEffBind _ (fun _ : ExecutionResult => (pure () : SailM Unit)) _ _ _ _ () _ []
    hm0 rfl
  rw [List.append_nil] at hex
  obtain ⟨s2, ib2, va, req, KK, hcl, hpa, hval, hdev, -, -, hrtc⟩ :=
    afAdminRunToMemwrite _ _ ib wakPlain ea 8 vs _ [] (by decide) hex hsf cpu k row
  refine ⟨s2, ib2, va, req, KK, hcl, hpa, hrtc, ?_⟩
  exact afAstepWriteOfMemwrite row cpu 8 va req KK s2.regs ib2 (efInit s2.dev) k lb vs
    (by rw [hpa]; exact hdev) (by decide) (by rw [hcl]; rfl) hval hrow
    (by rw [hid, hcl, hpa]; rfl) hdat

/-! ## 2.4 THE sd8 ROW RUN: the fetch glued in front of the data write, at `riscvStep tick` -/

/-- Rocq `af_sd8_row_run` (deviations 1-4): the store twin of `afLd8RowRun`.  `hwdom` (the
write's 8 bytes lie in the window) closes the domain obligation of `execEffStepOfLeafBase`. -/
theorem afSd8RowRun (σ : Wmstate) (W : GSet PAddr) (pc : BitVec 64) (w : BitVec 32)
    (rs1 rs2 : BitVec 5) (imm : BitVec 12) (ea : PAddr) (vs : BitVec 64)
    (D : Register → Bool) (dst : ExecSt) (cpu : CPU) (row : List Lbl) (k : Nat) (ib0 : Ibch) :
    -- the M-mode config tower
    σ.wmRegs .PC = pc →
    σ.wmRegs .cur_privilege = .Machine →
    pmpAllOff (σ.wmRegs .pmpcfg_n) →
    σ.wmRegs .pma_regions = bootPMA →
    σ.wmRegs .htif_tohost_base = none →
    σ.wmRegs .hart_state = .HART_ACTIVE () →
    (_get_Misa_S (σ.wmRegs .misa) == 1#1) = true →
    (_get_Mstatus_MIE (σ.wmRegs .mstatus) == 1#1) = false →
    (σ.wmRegs .elp == landing_pad_bits_backwards .LP_EXPECTED) = false →
    (_get_Mstatus_MPRV (σ.wmRegs .mstatus) == 1#1) = false →
    pmm_mode_backwards (_get_Seccfg_PMM (σ.wmRegs .mseccfg)) = .PMM_Disabled →
    -- the text word, in the confined memory, at a 4-aligned pc
    is_aligned_vaddr (.Virtaddr pc) 4 = true →
    inRam pc 4 →
    (∀ j : Nat, j < 4 → wmemRestrict σ W (pc + BitVec.ofNat 64 j) = some (nthByte (n := 4) w j)) →
    isRVC (Sail.BitVec.extractLsb w 15 0) = false →
    -- the decode
    (∀ r, D r = true → σ.wmRegs r = dst.regs r) →
    D .minstret_increment = false →
    goodb0 D (ext_decode w) dst = true →
    exec (ext_decode w) dst = some (.STORE (imm, .Regidx rs2, .Regidx rs1, 8), dst) →
    -- sd8's own geometry
    uxaXget σ.wmRegs rs1 + sign_extend (m := 64) imm = ea →
    uxaXget σ.wmRegs rs2 = vs →
    is_aligned_paddr (.Physaddr ea) 8 = true →
    inRam ea 8 →
    (∀ j : Nat, j < 8 → ea + BitVec.ofNat 64 j ∈ W) →
    -- the row's shape and the data item's value
    afSd8RowShape row k (paZ ea) →
    (row[k]?).bind lblData = some (WeakInterpProj.wbytes 8 vs) →
    ∀ tick : Bool,
    -- Q7: the instruction's run announces no sfence.vma word (header, Q7)
    WeakEvLang.noSfAnn (riscvStep tick) ⟨σ.wmRegs, wmemRestrict σ W, σ.wmDev⟩ →
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
  intro lpc lpriv lpmp lpma lhtif lhart lmisaS lmIE lelp lmprv lpmm hal hram4 htext hnotRVC
    hagree hDmi hgood hdec hea hvs hal8 hram8 hwdom hshape hdat tick hsf
  obtain ⟨lbd, hrowd, hidd⟩ := hshape
  -- (a) the whole instruction's `execEff` fact
  obtain ⟨t', hex, -⟩ := execEffStepOfLeafBase σ W pc w
    (.STORE (imm, .Regidx rs2, .Regidx rs1, 8)) [.WEwrite wakPlain ea 8 vs] D dst
    lpc lpriv (fun i => (lpmp i).2) lpma lhtif lhart lmisaS lmIE lelp hal hram4 htext hnotRVC
    hagree hDmi hgood hdec (by first | rfl | decide)
    (by
      intro b
      have hfacts := storeRegsFacts ⟨σ.wmRegs, wmemRestrict σ W, σ.wmDev⟩ b
        (Sail.BitVec.addInt pc 4)
      have hea_c : (⟨σ.wmRegs, wmemRestrict σ W, σ.wmDev⟩ : ExecSt).gpr rs1 +
          sign_extend (m := 64) imm = ea := by
        unfold ExecSt.gpr; exact hea
      have hvs_c : (⟨σ.wmRegs, wmemRestrict σ W, σ.wmDev⟩ : ExecSt).gpr rs2 = vs := by
        unfold ExecSt.gpr; exact hvs
      have hrun := execEffSd8At ⟨σ.wmRegs, wmemRestrict σ W, σ.wmDev⟩ b pc rs1 rs2 imm ea vs
        lpriv lmprv lpmm lpmp lpma lhtif hea_c hvs_c hal8 hram8
      refine ⟨_, hrun, ?_, ?_, ?_⟩
      · exact hfacts.1.trans lhart
      · exact hfacts.2.1
      · dsimp only
        exact writeBytesDomSub _ ea 8 vs W (wmemRestrictDom σ W) hwdom)
    tick
  -- (b) the admin run to the fetch node and the admin fetch step (position kept)
  obtain ⟨m2, s2, ib2, -, hex2, hrtcb, hsf2⟩ :=
    AxFetch2.fetchPeel (riscvStep tick) ⟨σ.wmRegs, wmemRestrict σ W, σ.wmDev⟩ ib0
      WeakFetchEff.wakIfetch pc 4 t' [.WEwrite wakPlain ea 8 vs] cpu k row (by decide) rfl hex
      hsf
  -- (d) the admin run to the data (write) node, then the data event
  obtain ⟨s3, ib3, va, req2, KK2, hcld, hpad, hvald, hdevd, -, -, hrtcd⟩ :=
    afAdminRunToMemwrite m2 s2 ib2 wakPlain ea 8 vs t' [] (by decide) hex2 hsf2 cpu k row
  refine ⟨s3, ib3, va, req2, KK2, hcld, hpad, rtc_transitive hrtcb hrtcd, ?_⟩
  exact afAstepWriteOfMemwrite row cpu 8 va req2 KK2 s3.regs ib3 (efInit s3.dev) k lbd vs
    (by rw [hpad]; exact hdevd) (by decide) (by rw [hcld]; rfl) hvald hrowd
    (by rw [hidd, hcld, hpad]; rfl) (by rw [hrowd] at hdat; exact hdat)

end Weak
