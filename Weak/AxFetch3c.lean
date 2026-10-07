/-
Weak: **track F, the AxSL instruction bridge — PART D, third file** (`AxFetch3c`): §2.8,
`af_cldsp_cont_rd` — GIVING the `c.ldsp` data node's continuation `KK2` A SPEC.

Rocq: `iris/AxFetch.v` @ xxvzwolszwmp, lines 2627–3589 (§2.8).  Part D is `AxFetch3` (§2.5–§2.6),
`AxFetch3b` (§2.7) and this file.

## What this file proves

`afCldspRowRun` (`AxFetch3b`) stops at the data `memRead` node; nothing says what the register
file is once the reload's bytes are in hand.  This section adds that spec.
* `afRiscvStepAllTicksFrame`: `execEffRiscvStepAllTicks` plus the device and an explicit register
  frame — the clock tick writes exactly `mcycle`/`mtime`/`mip`.
* `afCldspRowRun'Mem`: `afCldspRowRun` over an ARBITRARY confined memory `mm`, proved by INLINING
  `execEffStepOfLeafRvc2`'s construction (so the post-instruction state `t'` stays transparent),
  and returning, besides the run to the data node and its `areadStep`: `devAddr ea = false`, the
  node's memory `s3.mem = mm`, the node's own `execEff` fact (one round trip short of `KK2`'s
  spec), and `t'`'s register content (destination GPR = `v`, `PC = pc + 2`, the frame).
* `afCldspRowRun'`: its instance at `mm := wmemRestrict σ W` (Rocq: the primary, proved inline;
  the `_mem` version a verbatim generalization).
* `afCldspContRd`: the second round trip — the data node answered at a caller-supplied byte list
  `vs` that the confined memory holds — and `afAdminRunToEnd`: from `KK2 (.Ok (wordOfBytes 8 vs,
  none))` at `k + 1` to the boundary `.pure ()` at `t'`, with `t'.gpr rd = wordOfBytes 8 vs`.
* `afCldspContRdAll`: the same WITHOUT the byte premise on `vs`: `afCldspRowRun'Mem` is fed the
  hypothetical memory `bmWrite (wmemRestrict σ W) ea 8 (wordOfBytes 8 vs)`, which holds `vs` at
  `ea` and (under the new disjointness premise: the fetch window misses the data window) the
  real text at `pc`; the run's start (`riscvStep tick` at `σ.wmRegs`) does not mention memory.

## Deviations from Rocq

1. NAMES / VOCABULARY: as `AxFetch3b` deviation 1; `register_beq r X = false` ↦ `r ≠ X`;
   `register_lookup r t'.(sregs)` ↦ `t'.regs r`; `mdev` ↦ `dev`;
   `register_lookup (R_bitvector_64 (gpr_of_Z (uint rd))) t'.(sregs)` ↦ `t'.gpr rd`;
   `gmap Arch.pa (bv 8)` ↦ `BMap`; `write_bytes` ↦ `bmWrite`; `pa_add pc i <> pa_add ea j` ↦
   `pc + BitVec.ofNat 64 i ≠ ea + BitVec.ofNat 64 j`; `length vs = 8` ↦ `vs.length = 8`.  The
   Lean names keep Rocq's prime: `afCldspRowRun'`, `afCldspRowRun'Mem`.  No name of this file is
   in `notes/weak-port-dupnames.json`.
2. O2 STAGE C (`AxFetch1` header): the row shape is `afCldspRowShape row k (paZ ea)` (no fetch
   item, no pc), the `Tt`/`img` parameters and the `fetch_answers` premise are gone; the run to
   the data node ends at `k` (Rocq `S k`), the data step and the continuation run are at `k + 1`
   (Rocq `S (S k)`).  The fetch's round trip is not needed (`AxFetch2` deviation 3).
3. THE REGISTER FRAME.  Lean has no function from a GPR index to its `Register` (the GPR file is
   read by `uxaXget`, written by `ExecSt.setGpr`), so Rocq's one frame conjunct `∀ r, r ≠
   gpr(rd) → r ≠ PC → … → r ≠ mip → t'[r] = σ[r]` is split, equivalently, in two: every
   NON-GPR register (`r ∉ uxaGprs`) outside `PC, nextPC, minstret_increment, minstret, mcycle,
   mtime, mip` is unchanged, and every GPR index `j ≠ rd` reads as before
   (`t'.gpr j = uxaXget σ.wmRegs j`).
4. `afCldspContRdAll`: Rocq's `acc_wf ea 8` (from `Hram8`, for `write_bytes_lookup_at`) is not
   needed — `bmWrite_at` needs only `8 ≤ 2 ^ 64`.  The existential `s4` of
   `afCldspContRd(All)` is the `t'` of `afCldspRowRun'(Mem)`, as in Rocq's proof.
5. `afCldspRowRun'` is proved as the instance of `afCldspRowRun'Mem` (Rocq proves both inline,
   with the same script).

Q7 (owner ruling, `notes/weak-port-q7-sfence.md` route (a), Lean-only): `afCldspRowRun'Mem`/`afCldspRowRun'`/`afCldspContRd`/`afCldspContRdAll` take `WeakEvLang.noSfAnn (riscvStep tick) ⟨σ.wmRegs, mm, σ.wmDev⟩` per tick (at their memory; see `AxFetch2`'s Q7 note), the first two also return `noSfAnn` at the data node, which `AxFetch3c.nodeCont` takes.

**Rocq → Lean name map.**  `af_riscv_step_all_ticks_frame` `afRiscvStepAllTicksFrame`,
`af_cldsp_row_run'` `afCldspRowRun'`, `af_cldsp_cont_rd` `afCldspContRd`,
`af_cldsp_row_run'_mem` `afCldspRowRun'Mem`, `af_cldsp_cont_rd_all` `afCldspContRdAll`.
Lean-only (file-qualified): `AxFetch3c.gprSetGprSame` / `AxFetch3c.gprSetGprNe` (a GPR write
reads back / leaves the other GPRs alone), `AxFetch3c.nodeCont` (the data node's second round
trip + `afAdminRunToEnd`, shared by the two `cont_rd` lemmas).

**Dropped:** nothing.  Counts: Rocq 5 lemmas in lines 2627–3589; Lean 5 + 3 Lean-only.
-/
import Weak.AxFetch3b

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open Sail Sail.ConcurrencyInterfaceV1
open Sail.ArchSem (FreeM)
open LeanRV64D LeanRV64D.Functions
open Wlabel

/-! ## 2.8 GIVING `KK2` A SPEC -/

/-- Rocq `af_riscv_step_all_ticks_frame`: `execEffRiscvStepAllTicks` with the device and an
explicit register frame (the tick writes exactly `mcycle`, `mtime`, `mip`). -/
theorem afRiscvStepAllTicksFrame (s t0 : ExecSt) (es : List Weff) :
    execEff (riscvStep false) s = some ((), t0, es) →
    ∀ tick : Bool, ∃ t' : ExecSt,
      execEff (riscvStep tick) s = some ((), t', es) ∧
      t'.mem = t0.mem ∧ t'.dev = t0.dev ∧
      (∀ r, r ≠ .mcycle → r ≠ .mtime → r ≠ .mip → t'.regs r = t0.regs r) := by
  intro h0 tick
  cases tick
  · exact ⟨t0, h0, rfl, rfl, fun _ _ _ _ => rfl⟩
  · obtain ⟨c, ti, p, htick⟩ := execEffTickClock t0
    refine ⟨_, execEffRiscvStepTick s t0 _ es h0 htick, rfl, rfl, ?_⟩
    intro r h1 h2 h3
    rw [setLookupNe r .mip _ _ h3, setLookupNe r .mtime _ _ h2, setLookupNe r .mcycle _ _ h1]

/-- (Lean-only) A GPR write reads back. -/
theorem AxFetch3c.gprSetGprSame (s : ExecSt) (i : BitVec 5) (v : BitVec 64) (h : i.toNat ≠ 0) :
    (s.setGpr i v).gpr i = v := by
  rcases uxa_bv5_cases i with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | exact absurd rfl h | rfl

/-- (Lean-only) A GPR write leaves every other GPR index alone. -/
theorem AxFetch3c.gprSetGprNe (s : ExecSt) (i j : BitVec 5) (v : BitVec 64) (h : j ≠ i) :
    (s.setGpr i v).gpr j = s.gpr j := by
  rcases uxa_bv5_cases i with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  rcases uxa_bv5_cases j with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | exact absurd rfl h | rfl

/-- (Lean-only) THE DATA NODE'S SECOND ROUND TRIP: a plain RAM read node whose `execEff` runs to
`((), t', [.WEread wakPlain ea 8])`, answered at the word its memory holds, runs (admin only,
position kept) to the boundary at `t'`. -/
theorem AxFetch3c.nodeCont (va : Nat) (req : Mem_read_request 8 va Arch.pa Arch.translation Arch.arch_ak)
    (KK : Result (BitVec (8 * 8) × Option Bool) Arch.abort → SailM Unit) (s3 t' : ExecSt)
    (ea : PAddr) (w : BitVec 64) (ib3 : Ibch) (cpu : CPU) (kpos : Nat) (row : List Lbl) :
    req.pa = ea → devAddr ea = false → bmRead s3.mem ea 8 = some w →
    execEff (.impure (.ok (.memRead 8 va req)) KK) s3 = some ((), t', [.WEread wakPlain ea 8]) →
    WeakEvLang.noSfAnn (.impure (.ok (.memRead 8 va req)) KK) s3 →
    ∃ ib4 : Ibch,
      rtc (fun t1 t2 => ∃ l, AxOpsem.astepProg row t1 l t2)
        ⟨.PHart cpu (KK (.Ok (w, none))) s3.regs none ib3, kpos⟩
        ⟨.PHart cpu (.pure ()) t'.regs none ib4, kpos⟩ := by
  intro hpa hdev hrb hee hns
  have hm : mmioAcc req.pa 8 = false := by simp [mmioAcc, hpa, hdev]
  have hrb' : bmRead s3.mem req.pa 8 = some w := by rw [hpa]; exact hrb
  simp only [execEff, hm, Bool.false_eq_true, ↓reduceIte, hrb'] at hee
  obtain ⟨es0, h0, hcons⟩ := Weff.consEqSome.1 hee
  have hes : es0 = [] := (List.cons.inj hcons).2.symm
  subst hes
  simp only [WeakEvLang.noSfAnn, hm, Bool.false_eq_true, ↓reduceIte, hrb'] at hns
  exact afAdminRunToEnd _ s3 ib3 t' h0 hns cpu kpos row

/-- Rocq `af_cldsp_row_run'_mem` (deviations 1-3): `afCldspRowRun` over an arbitrary confined
memory `mm`, plus the node's memory, its `execEff` fact, and the post-instruction state `t'`'s
register content. -/
theorem afCldspRowRun'Mem (σ : Wmstate) (mm : BMap) (pc : BitVec 64) (h : BitVec 16)
    (w : BitVec 32) (rd : BitVec 5) (imm : BitVec 12) (ea : PAddr) (v : BitVec 64)
    (i0 : instruction) (D D0 : Register → Bool) (dst : ExecSt) (cpu : CPU) (row : List Lbl)
    (k : Nat) (ib0 : Ibch) :
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
    is_aligned_vaddr (.Virtaddr pc) 2 = true →
    is_aligned_vaddr (.Virtaddr pc) 4 = false →
    inRam pc 4 →
    (∀ j : Nat, j < 4 → mm (pc + BitVec.ofNat 64 j) = some (nthByte (n := 4) w j)) →
    Sail.BitVec.extractLsb w 15 0 = h →
    isRVC h = true →
    (∀ r, D r = true → σ.wmRegs r = dst.regs r) →
    D .minstret_increment = false →
    goodb0 D (ext_decode_compressed h) dst = true →
    exec (ext_decode_compressed h) dst = some (i0, dst) →
    (∀ s : ExecSt, goodb0 D0 (execute i0) s = true) →
    (∀ s : ExecSt, exec (execute i0) s =
      some (.ExecuteAs (.LOAD (imm, sp, .Regidx rd, false, 8)), s)) →
    rd.toNat ≠ 0 →
    σ.wmRegs .x2 + sign_extend (m := 64) imm = ea →
    is_aligned_paddr (.Physaddr ea) 8 = true →
    inRam ea 8 →
    (∀ j : Nat, j < 8 → mm (ea + BitVec.ofNat 64 j) = some (nthByte (n := 8) v j)) →
    afCldspRowShape row k (paZ ea) →
    ∀ tick : Bool,
    -- Q7: the instruction's run announces no sfence.vma word (header, Q7)
    WeakEvLang.noSfAnn (riscvStep tick) ⟨σ.wmRegs, mm, σ.wmDev⟩ →
    ∃ (s3 : ExecSt) (ib3 : Ibch) (va : Nat)
      (req2 : Mem_read_request 8 va Arch.pa Arch.translation Arch.arch_ak)
      (KK2 : Result (BitVec (8 * 8) × Option Bool) Arch.abort → SailM Unit) (t' : ExecSt),
      classify req2.access_kind = wakPlain ∧ req2.pa = ea ∧ devAddr ea = false ∧ s3.mem = mm ∧
      rtc (fun t1 t2 => ∃ l, AxOpsem.astepProg row t1 l t2)
        ⟨.PHart cpu (riscvStep tick) σ.wmRegs none ib0, k⟩
        ⟨.PHart cpu (.impure (.ok (.memRead 8 va req2)) KK2) s3.regs none ib3, k⟩ ∧
      areadStep row ⟨.PHart cpu (.impure (.ok (.memRead 8 va req2)) KK2) s3.regs none ib3, k⟩
        (.IRead (classify req2.access_kind).akSync (paZ req2.pa) 8)
        (fun vs => ⟨.PHart cpu (KK2 (.Ok (wordOfBytes 8 vs, none))) s3.regs none ib3, k + 1⟩) ∧
      execEff (.impure (.ok (.memRead 8 va req2)) KK2) s3 =
        some ((), t', [.WEread wakPlain ea 8]) ∧
      t'.gpr rd = v ∧
      t'.regs .PC = BitVec.addInt pc 2 ∧
      (∀ r, r ∉ uxaGprs → r ≠ .PC → r ≠ .nextPC → r ≠ .minstret_increment → r ≠ .minstret →
        r ≠ .mcycle → r ≠ .mtime → r ≠ .mip → t'.regs r = σ.wmRegs r) ∧
      (∀ j : BitVec 5, j ≠ rd → t'.gpr j = uxaXget σ.wmRegs j) ∧
      WeakEvLang.noSfAnn (.impure (.ok (.memRead 8 va req2)) KK2) s3 := by
  intro lpc lpriv lmprv lpmm lpmp lpma lhtif lhart lmisaS lmisaC lmIE lelp hal2 hal4 hram htext
    hsub hisRVC hagree hDmi hgood hdec hgood0 hexp hrd hea hal8 hram8 hbytes8 hshape tick hsf
  obtain ⟨lbd, hrowd, hidd⟩ := hshape
  -- the inlined `execEffStepOfLeafRvc2` construction, at `s := ⟨σ.wmRegs, mm, σ.wmDev⟩`
  obtain ⟨b, hsi⟩ := execEffShouldIncMinstretSome (σ.wmRegs .cur_privilege)
    (⟨σ.wmRegs, mm, σ.wmDev⟩ : ExecSt)
  have lpriv_a : (hartActiveSA ⟨σ.wmRegs, mm, σ.wmDev⟩ b).regs .cur_privilege = .Machine := by
    rw [WeakFetchEff.saLookup _ _ _ (by decide)]; exact lpriv
  have lpc_a : (hartActiveSA ⟨σ.wmRegs, mm, σ.wmDev⟩ b).regs .PC = pc := by
    rw [WeakFetchEff.saLookup _ _ _ (by decide)]; exact lpc
  have lhart_a : (hartActiveSA ⟨σ.wmRegs, mm, σ.wmDev⟩ b).regs .hart_state = .HART_ACTIVE () := by
    rw [WeakFetchEff.saLookup _ _ _ (by decide)]; exact lhart
  have lelp_a : ((hartActiveSA ⟨σ.wmRegs, mm, σ.wmDev⟩ b).regs .elp ==
      landing_pad_bits_backwards .LP_EXPECTED) = false := by
    rw [WeakFetchEff.saLookup _ _ _ (by decide)]; exact lelp
  have hdisp : execEff (dispatchInterrupt .Machine) (hartActiveSA ⟨σ.wmRegs, mm, σ.wmDev⟩ b) =
      some (none, hartActiveSA ⟨σ.wmRegs, mm, σ.wmDev⟩ b, []) :=
    execEffDispatchInterruptMachineNone _
      (by rw [WeakFetchEff.saLookup _ _ _ (by decide)]; exact lmisaS)
      (by rw [WeakFetchEff.saLookup _ _ _ (by decide)]; exact lmIE)
  have hzca : execEff (currentlyEnabled .Ext_Zca) (hartActiveSA ⟨σ.wmRegs, mm, σ.wmDev⟩ b) =
      some (true, hartActiveSA ⟨σ.wmRegs, mm, σ.wmDev⟩ b, []) :=
    execEffCurrentlyEnabledZca _ (by rw [WeakFetchEff.saLookup _ _ _ (by decide)]; exact lmisaC)
  have hfetch : execEff (fetch ()) (hartActiveSA ⟨σ.wmRegs, mm, σ.wmDev⟩ b) =
      some (.F_RVC h, hartActiveSA ⟨σ.wmRegs, mm, σ.wmDev⟩ b,
        [.WEread WeakFetchEff.wakIfetch pc 2]) :=
    execEffFetchFlatRvc2 _ pc h
      (by rw [WeakFetchEff.saLookup _ _ _ (by decide)]; exact fun i => (lpmp i).2)
      (by rw [WeakFetchEff.saLookup _ _ _ (by decide)]; exact lpma)
      (by rw [WeakFetchEff.saLookup _ _ _ (by decide)]; exact lmisaC)
      lpc_a lpriv_a
      (by rw [WeakFetchEff.saLookup _ _ _ (by decide)]; exact lhtif)
      hal4 ⟨hal2, hram, w, ⟨hsub, hisRVC⟩, htext⟩
  have hdec_a : execEff (ext_decode_compressed h) (hartActiveSA ⟨σ.wmRegs, mm, σ.wmDev⟩ b) =
      some (i0, hartActiveSA ⟨σ.wmRegs, mm, σ.wmDev⟩ b, []) := by
    refine execEffDecodeBridge D (ext_decode_compressed h) dst _ i0 ?_ hgood hdec
    intro r hD
    have hne : r ≠ .minstret_increment := by
      rintro rfl
      rw [hDmi] at hD
      exact absurd hD (by decide)
    rw [WeakFetchEff.saLookup r _ b hne]
    exact hagree r hD
  have hexp_a : execEff (execute i0)
      ((hartActiveSA ⟨σ.wmRegs, mm, σ.wmDev⟩ b).setReg .nextPC (BitVec.addInt pc 2)) =
      some (.ExecuteAs (.LOAD (imm, sp, .Regidx rd, false, 8)),
        (hartActiveSA ⟨σ.wmRegs, mm, σ.wmDev⟩ b).setReg .nextPC (BitVec.addInt pc 2), []) :=
    execEffOfGoodb0Self D0 (execute i0) _ _ (hgood0 _) (hexp _)
  have hea2 : (⟨σ.wmRegs, mm, σ.wmDev⟩ : ExecSt).gpr (zero_extend (m := 5) 0b10#2) +
      sign_extend (m := 64) imm = ea := by
    unfold ExecSt.gpr; rw [AxFetch3b.spGpr]; exact hea
  have hex := execEffLd8OffAt ⟨σ.wmRegs, mm, σ.wmDev⟩ b (BitVec.addInt pc 2)
    (zero_extend (m := 5) 0b10#2) rd imm ea v hrd lpriv lmprv lpmm lpmp lpma lhtif hea2 hal8 hram8
    (fun j hj => hbytes8 j hj)
  obtain ⟨Fhart, Fmi, -, -, Fnpc⟩ :=
    loadSexecFacts ⟨σ.wmRegs, mm, σ.wmDev⟩ b (BitVec.addInt pc 2) rd v
  have hstep := execEffRiscvStepRvc ⟨σ.wmRegs, mm, σ.wmDev⟩ _ h i0
    (.LOAD (imm, sp, .Regidx rd, false, 8)) pc b [.WEread WeakFetchEff.wakIfetch pc 2]
    [.WEread wakPlain ea 8] hsi lhart_a lpriv_a hdisp hfetch hdec_a lelp_a lpc_a hzca hexp_a hex
    (Fhart.trans lhart) Fmi
  obtain ⟨t', ht', -, -, hframet⟩ := afRiscvStepAllTicksFrame _ _ _ hstep tick
  -- the run: the admin peel + the admin fetch, then the peel to the data node
  obtain ⟨m2, s2, ib2, hmem2, hex2, hrtcb, hsf2⟩ :=
    AxFetch2.fetchPeel (riscvStep tick) ⟨σ.wmRegs, mm, σ.wmDev⟩ ib0
      WeakFetchEff.wakIfetch pc 2 t' [.WEread wakPlain ea 8] cpu k row (by decide) rfl ht' hsf
  obtain ⟨s3, ib3, va, req2, KK2, hcld, hpad, hdevd, hmem3, hee3, hrtcd, hns3⟩ :=
    afAdminRunToMemread m2 s2 ib2 wakPlain ea 8 t' [] (by decide) hex2 hsf2 cpu k row
  -- the post-instruction state, register by register
  have hT : ∀ r, r ≠ .PC → r ≠ .minstret → r ≠ .mcycle → r ≠ .mtime → r ≠ .mip →
      t'.regs r = ((((⟨σ.wmRegs, mm, σ.wmDev⟩ : ExecSt).setReg .minstret_increment b).setReg
        .nextPC (BitVec.addInt pc 2)).setGpr rd v).regs r := by
    intro r h1 h2 h3 h4 h5
    rw [hframet r h3 h4 h5]
    cases b
    · simp only [hartActiveSFinal, hartActiveSTick, Bool.false_eq_true, ↓reduceIte]
      rw [setLookupNe r .PC _ _ h1]
    · simp only [hartActiveSFinal, hartActiveSTick, ↓reduceIte]
      rw [setLookupNe r .minstret _ _ h2, setLookupNe r .PC _ _ h1]
  have hgprT : ∀ j : BitVec 5, t'.gpr j = ((((⟨σ.wmRegs, mm, σ.wmDev⟩ : ExecSt).setReg
      .minstret_increment b).setReg .nextPC (BitVec.addInt pc 2)).setGpr rd v).gpr j := by
    intro j
    unfold ExecSt.gpr
    apply uxaXget_congr
    intro r hr
    have hnot : ∀ r' : Register, r' ∉ uxaGprs → r ≠ r' := fun r' hr' e => hr' (e ▸ hr)
    exact hT r (hnot _ (by decide)) (hnot _ (by decide)) (hnot _ (by decide)) (hnot _ (by decide))
      (hnot _ (by decide))
  refine ⟨s3, ib3, va, req2, KK2, t', hcld, hpad, hdevd, hmem3.trans hmem2,
    rtc_transitive hrtcb hrtcd, ?_, hee3, ?_, ?_, ?_, ?_, hns3⟩
  · exact afAreadStepOfMemread row cpu 8 va req2 KK2 s3.regs ib3 (efInit s3.dev) k lbd
      (by rw [hpad]; exact hdevd) (by rw [hcld]; rfl) (by rw [hcld]; rfl) hrowd
      (by rw [hidd, hcld, hpad]; rfl)
  · rw [hgprT]; exact AxFetch3c.gprSetGprSame _ rd v hrd
  · rw [hframet .PC (by decide) (by decide) (by decide)]
    cases b
    · simp only [hartActiveSFinal, hartActiveSTick, Bool.false_eq_true, ↓reduceIte,
        ExecSt.setReg_regs, RegFile.set_same]
      exact Fnpc
    · simp only [hartActiveSFinal, hartActiveSTick, ↓reduceIte]
      rw [setLookupNe .PC .minstret _ _ (by decide)]
      simp only [ExecSt.setReg_regs, RegFile.set_same]
      exact Fnpc
  · intro r hg h1 h2 h3 h4 h5 h6 h7
    rw [hT r h1 h4 h5 h6 h7, WeakLeafWin.setGprRegsNe _ _ _ _ hg, setLookupNe r .nextPC _ _ h2,
      setLookupNe r .minstret_increment _ _ h3]
  · intro j hj
    rw [hgprT, AxFetch3c.gprSetGprNe _ rd j v hj]
    unfold ExecSt.gpr
    apply uxaXget_congr
    intro r hr
    have hnot : ∀ r' : Register, r' ∉ uxaGprs → r ≠ r' := fun r' hr' e => hr' (e ▸ hr)
    rw [setLookupNe r .nextPC _ _ (hnot _ (by decide)),
      setLookupNe r .minstret_increment _ _ (hnot _ (by decide))]

/-- Rocq `af_cldsp_row_run'` (deviations 1-3, 5): `afCldspRowRun'Mem` at the real confined
memory `wmemRestrict σ W`. -/
theorem afCldspRowRun' (σ : Wmstate) (W : GSet PAddr) (pc : BitVec 64) (h : BitVec 16)
    (w : BitVec 32) (rd : BitVec 5) (imm : BitVec 12) (ea : PAddr) (v : BitVec 64)
    (i0 : instruction) (D D0 : Register → Bool) (dst : ExecSt) (cpu : CPU) (row : List Lbl)
    (k : Nat) (ib0 : Ibch) :
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
    is_aligned_vaddr (.Virtaddr pc) 2 = true →
    is_aligned_vaddr (.Virtaddr pc) 4 = false →
    inRam pc 4 →
    (∀ j : Nat, j < 4 → wmemRestrict σ W (pc + BitVec.ofNat 64 j) = some (nthByte (n := 4) w j)) →
    Sail.BitVec.extractLsb w 15 0 = h →
    isRVC h = true →
    (∀ r, D r = true → σ.wmRegs r = dst.regs r) →
    D .minstret_increment = false →
    goodb0 D (ext_decode_compressed h) dst = true →
    exec (ext_decode_compressed h) dst = some (i0, dst) →
    (∀ s : ExecSt, goodb0 D0 (execute i0) s = true) →
    (∀ s : ExecSt, exec (execute i0) s =
      some (.ExecuteAs (.LOAD (imm, sp, .Regidx rd, false, 8)), s)) →
    rd.toNat ≠ 0 →
    σ.wmRegs .x2 + sign_extend (m := 64) imm = ea →
    is_aligned_paddr (.Physaddr ea) 8 = true →
    inRam ea 8 →
    (∀ j : Nat, j < 8 → wmemRestrict σ W (ea + BitVec.ofNat 64 j) = some (nthByte (n := 8) v j)) →
    afCldspRowShape row k (paZ ea) →
    ∀ tick : Bool,
    -- Q7: the instruction's run announces no sfence.vma word (header, Q7)
    WeakEvLang.noSfAnn (riscvStep tick) ⟨σ.wmRegs, wmemRestrict σ W, σ.wmDev⟩ →
    ∃ (s3 : ExecSt) (ib3 : Ibch) (va : Nat)
      (req2 : Mem_read_request 8 va Arch.pa Arch.translation Arch.arch_ak)
      (KK2 : Result (BitVec (8 * 8) × Option Bool) Arch.abort → SailM Unit) (t' : ExecSt),
      classify req2.access_kind = wakPlain ∧ req2.pa = ea ∧ devAddr ea = false ∧
      s3.mem = wmemRestrict σ W ∧
      rtc (fun t1 t2 => ∃ l, AxOpsem.astepProg row t1 l t2)
        ⟨.PHart cpu (riscvStep tick) σ.wmRegs none ib0, k⟩
        ⟨.PHart cpu (.impure (.ok (.memRead 8 va req2)) KK2) s3.regs none ib3, k⟩ ∧
      areadStep row ⟨.PHart cpu (.impure (.ok (.memRead 8 va req2)) KK2) s3.regs none ib3, k⟩
        (.IRead (classify req2.access_kind).akSync (paZ req2.pa) 8)
        (fun vs => ⟨.PHart cpu (KK2 (.Ok (wordOfBytes 8 vs, none))) s3.regs none ib3, k + 1⟩) ∧
      execEff (.impure (.ok (.memRead 8 va req2)) KK2) s3 =
        some ((), t', [.WEread wakPlain ea 8]) ∧
      t'.gpr rd = v ∧
      t'.regs .PC = BitVec.addInt pc 2 ∧
      (∀ r, r ∉ uxaGprs → r ≠ .PC → r ≠ .nextPC → r ≠ .minstret_increment → r ≠ .minstret →
        r ≠ .mcycle → r ≠ .mtime → r ≠ .mip → t'.regs r = σ.wmRegs r) ∧
      (∀ j : BitVec 5, j ≠ rd → t'.gpr j = uxaXget σ.wmRegs j) ∧
      WeakEvLang.noSfAnn (.impure (.ok (.memRead 8 va req2)) KK2) s3 :=
  afCldspRowRun'Mem σ (wmemRestrict σ W) pc h w rd imm ea v i0 D D0 dst cpu row k ib0

/-- Rocq `af_cldsp_cont_rd` (deviations 1-4): `KK2`'s own spec, for a caller-supplied read answer
`vs` that the confined memory holds — from the data node's answer at `k + 1` to the boundary,
with the destination register holding `wordOfBytes 8 vs`. -/
theorem afCldspContRd (σ : Wmstate) (W : GSet PAddr) (pc : BitVec 64) (h : BitVec 16)
    (w : BitVec 32) (rd : BitVec 5) (imm : BitVec 12) (ea : PAddr) (i0 : instruction)
    (D D0 : Register → Bool) (dst : ExecSt) (cpu : CPU) (row : List Lbl) (k : Nat) (ib0 : Ibch) :
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
    is_aligned_vaddr (.Virtaddr pc) 2 = true →
    is_aligned_vaddr (.Virtaddr pc) 4 = false →
    inRam pc 4 →
    (∀ j : Nat, j < 4 → wmemRestrict σ W (pc + BitVec.ofNat 64 j) = some (nthByte (n := 4) w j)) →
    Sail.BitVec.extractLsb w 15 0 = h →
    isRVC h = true →
    (∀ r, D r = true → σ.wmRegs r = dst.regs r) →
    D .minstret_increment = false →
    goodb0 D (ext_decode_compressed h) dst = true →
    exec (ext_decode_compressed h) dst = some (i0, dst) →
    (∀ s : ExecSt, goodb0 D0 (execute i0) s = true) →
    (∀ s : ExecSt, exec (execute i0) s =
      some (.ExecuteAs (.LOAD (imm, sp, .Regidx rd, false, 8)), s)) →
    rd.toNat ≠ 0 →
    σ.wmRegs .x2 + sign_extend (m := 64) imm = ea →
    is_aligned_paddr (.Physaddr ea) 8 = true →
    inRam ea 8 →
    afCldspRowShape row k (paZ ea) →
    ∀ vs : List (BitVec 8), vs.length = 8 →
    (∀ j : Nat, j < 8 → wmemRestrict σ W (ea + BitVec.ofNat 64 j) =
      some (nthByte (n := 8) (wordOfBytes 8 vs) j)) →
    ∀ tick : Bool,
    -- Q7: the instruction's run announces no sfence.vma word (header, Q7)
    WeakEvLang.noSfAnn (riscvStep tick) ⟨σ.wmRegs, wmemRestrict σ W, σ.wmDev⟩ →
    ∃ (s3 : ExecSt) (ib3 : Ibch) (va : Nat)
      (req2 : Mem_read_request 8 va Arch.pa Arch.translation Arch.arch_ak)
      (KK2 : Result (BitVec (8 * 8) × Option Bool) Arch.abort → SailM Unit) (s4 : ExecSt)
      (ib4 : Ibch),
      classify req2.access_kind = wakPlain ∧ req2.pa = ea ∧
      rtc (fun t1 t2 => ∃ l, AxOpsem.astepProg row t1 l t2)
        ⟨.PHart cpu (riscvStep tick) σ.wmRegs none ib0, k⟩
        ⟨.PHart cpu (.impure (.ok (.memRead 8 va req2)) KK2) s3.regs none ib3, k⟩ ∧
      areadStep row ⟨.PHart cpu (.impure (.ok (.memRead 8 va req2)) KK2) s3.regs none ib3, k⟩
        (.IRead (classify req2.access_kind).akSync (paZ req2.pa) 8)
        (fun vs' => ⟨.PHart cpu (KK2 (.Ok (wordOfBytes 8 vs', none))) s3.regs none ib3, k + 1⟩) ∧
      rtc (fun t1 t2 => ∃ l, AxOpsem.astepProg row t1 l t2)
        ⟨.PHart cpu (KK2 (.Ok (wordOfBytes 8 vs, none))) s3.regs none ib3, k + 1⟩
        ⟨.PHart cpu (.pure ()) s4.regs none ib4, k + 1⟩ ∧
      s4.gpr rd = wordOfBytes 8 vs ∧
      s4.regs .PC = BitVec.addInt pc 2 ∧
      (∀ r, r ∉ uxaGprs → r ≠ .PC → r ≠ .nextPC → r ≠ .minstret_increment → r ≠ .minstret →
        r ≠ .mcycle → r ≠ .mtime → r ≠ .mip → s4.regs r = σ.wmRegs r) ∧
      (∀ j : BitVec 5, j ≠ rd → s4.gpr j = uxaXget σ.wmRegs j) := by
  intro lpc lpriv lmprv lpmm lpmp lpma lhtif lhart lmisaS lmisaC lmIE lelp hal2 hal4 hram htext
    hsub hisRVC hagree hDmi hgood hdec hgood0 hexp hrd hea hal8 hram8 hshape vs _ hbytes8 tick hsf
  obtain ⟨s3, ib3, va, req2, KK2, t', hcl, hpa, hdev, hmem, hrtc, harw, hee, hrdr, hpcr, hfr,
      hfg, hns⟩ :=
    afCldspRowRun' σ W pc h w rd imm ea (wordOfBytes 8 vs) i0 D D0 dst cpu row k ib0 lpc lpriv
      lmprv lpmm lpmp lpma lhtif lhart lmisaS lmisaC lmIE lelp hal2 hal4 hram htext hsub hisRVC
      hagree hDmi hgood hdec hgood0 hexp hrd hea hal8 hram8 hbytes8 hshape tick hsf
  have hrb : bmRead s3.mem ea 8 = some (wordOfBytes 8 vs) := by
    rw [hmem]; exact bmRead_of_bytes _ ea 8 _ hbytes8
  obtain ⟨ib4, hrtc2⟩ :=
    AxFetch3c.nodeCont va req2 KK2 s3 t' ea (wordOfBytes 8 vs) ib3 cpu (k + 1) row hpa hdev hrb hee hns
  exact ⟨s3, ib3, va, req2, KK2, t', ib4, hcl, hpa, hrtc, harw, hrtc2, hrdr, hpcr, hfr, hfg⟩

/-- Rocq `af_cldsp_cont_rd_all` (deviations 1-4): `afCldspContRd` WITHOUT the byte premise on
`vs` — the continuation spec at ANY 8-byte answer, given that the fetch window misses the data
window. -/
theorem afCldspContRdAll (σ : Wmstate) (W : GSet PAddr) (pc : BitVec 64) (h : BitVec 16)
    (w : BitVec 32) (rd : BitVec 5) (imm : BitVec 12) (ea : PAddr) (i0 : instruction)
    (D D0 : Register → Bool) (dst : ExecSt) (cpu : CPU) (row : List Lbl) (k : Nat) (ib0 : Ibch) :
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
    is_aligned_vaddr (.Virtaddr pc) 2 = true →
    is_aligned_vaddr (.Virtaddr pc) 4 = false →
    inRam pc 4 →
    (∀ j : Nat, j < 4 → wmemRestrict σ W (pc + BitVec.ofNat 64 j) = some (nthByte (n := 4) w j)) →
    Sail.BitVec.extractLsb w 15 0 = h →
    isRVC h = true →
    (∀ r, D r = true → σ.wmRegs r = dst.regs r) →
    D .minstret_increment = false →
    goodb0 D (ext_decode_compressed h) dst = true →
    exec (ext_decode_compressed h) dst = some (i0, dst) →
    (∀ s : ExecSt, goodb0 D0 (execute i0) s = true) →
    (∀ s : ExecSt, exec (execute i0) s =
      some (.ExecuteAs (.LOAD (imm, sp, .Regidx rd, false, 8)), s)) →
    rd.toNat ≠ 0 →
    σ.wmRegs .x2 + sign_extend (m := 64) imm = ea →
    is_aligned_paddr (.Physaddr ea) 8 = true →
    inRam ea 8 →
    (∀ i j : Nat, i < 4 → j < 8 → pc + BitVec.ofNat 64 i ≠ ea + BitVec.ofNat 64 j) →
    afCldspRowShape row k (paZ ea) →
    ∀ vs : List (BitVec 8), vs.length = 8 →
    ∀ tick : Bool,
    -- Q7: the instruction's run announces no sfence.vma word (header, Q7)
    WeakEvLang.noSfAnn (riscvStep tick) ⟨σ.wmRegs, bmWrite (wmemRestrict σ W) ea 8 (wordOfBytes 8 vs), σ.wmDev⟩ →
    ∃ (s3 : ExecSt) (ib3 : Ibch) (va : Nat)
      (req2 : Mem_read_request 8 va Arch.pa Arch.translation Arch.arch_ak)
      (KK2 : Result (BitVec (8 * 8) × Option Bool) Arch.abort → SailM Unit) (s4 : ExecSt)
      (ib4 : Ibch),
      classify req2.access_kind = wakPlain ∧ req2.pa = ea ∧
      rtc (fun t1 t2 => ∃ l, AxOpsem.astepProg row t1 l t2)
        ⟨.PHart cpu (riscvStep tick) σ.wmRegs none ib0, k⟩
        ⟨.PHart cpu (.impure (.ok (.memRead 8 va req2)) KK2) s3.regs none ib3, k⟩ ∧
      areadStep row ⟨.PHart cpu (.impure (.ok (.memRead 8 va req2)) KK2) s3.regs none ib3, k⟩
        (.IRead (classify req2.access_kind).akSync (paZ req2.pa) 8)
        (fun vs' => ⟨.PHart cpu (KK2 (.Ok (wordOfBytes 8 vs', none))) s3.regs none ib3, k + 1⟩) ∧
      rtc (fun t1 t2 => ∃ l, AxOpsem.astepProg row t1 l t2)
        ⟨.PHart cpu (KK2 (.Ok (wordOfBytes 8 vs, none))) s3.regs none ib3, k + 1⟩
        ⟨.PHart cpu (.pure ()) s4.regs none ib4, k + 1⟩ ∧
      s4.gpr rd = wordOfBytes 8 vs ∧
      s4.regs .PC = BitVec.addInt pc 2 ∧
      (∀ r, r ∉ uxaGprs → r ≠ .PC → r ≠ .nextPC → r ≠ .minstret_increment → r ≠ .minstret →
        r ≠ .mcycle → r ≠ .mtime → r ≠ .mip → s4.regs r = σ.wmRegs r) ∧
      (∀ j : BitVec 5, j ≠ rd → s4.gpr j = uxaXget σ.wmRegs j) := by
  intro lpc lpriv lmprv lpmm lpmp lpma lhtif lhart lmisaS lmisaC lmIE lelp hal2 hal4 hram htext
    hsub hisRVC hagree hDmi hgood hdec hgood0 hexp hrd hea hal8 hram8 hdisj hshape vs _ tick hsf
  -- the hypothetical confined memory: the real one, patched at `ea` to hold `vs`
  have htext' : ∀ j : Nat, j < 4 →
      bmWrite (wmemRestrict σ W) ea 8 (wordOfBytes 8 vs) (pc + BitVec.ofNat 64 j) =
        some (nthByte (n := 4) w j) := by
    intro j hj
    rw [bmWrite_other _ ea 8 _ _ (fun ha => by
      obtain ⟨j', hj', e⟩ := (ubWin_mem ea 8 _).1 ha
      exact hdisj j j' hj hj' e)]
    exact htext j hj
  have hbytes8' : ∀ j : Nat, j < 8 →
      bmWrite (wmemRestrict σ W) ea 8 (wordOfBytes 8 vs) (ea + BitVec.ofNat 64 j) =
        some (nthByte (n := 8) (wordOfBytes 8 vs) j) :=
    fun j hj => bmWrite_at _ ea 8 _ (by decide) j hj
  obtain ⟨s3, ib3, va, req2, KK2, t', hcl, hpa, hdev, hmem, hrtc, harw, hee, hrdr, hpcr, hfr,
      hfg, hns⟩ :=
    afCldspRowRun'Mem σ (bmWrite (wmemRestrict σ W) ea 8 (wordOfBytes 8 vs)) pc h w rd imm ea
      (wordOfBytes 8 vs) i0 D D0 dst cpu row k ib0 lpc lpriv lmprv lpmm lpmp lpma lhtif lhart
      lmisaS lmisaC lmIE lelp hal2 hal4 hram htext' hsub hisRVC hagree hDmi hgood hdec hgood0 hexp
      hrd hea hal8 hram8 hbytes8' hshape tick hsf
  have hrb : bmRead s3.mem ea 8 = some (wordOfBytes 8 vs) := by
    rw [hmem]; exact bmRead_of_bytes _ ea 8 _ hbytes8'
  obtain ⟨ib4, hrtc2⟩ :=
    AxFetch3c.nodeCont va req2 KK2 s3 t' ea (wordOfBytes 8 vs) ib3 cpu (k + 1) row hpa hdev hrb hee hns
  exact ⟨s3, ib3, va, req2, KK2, t', ib4, hcl, hpa, hrtc, harw, hrtc2, hrdr, hpcr, hfr, hfg⟩

end Weak
