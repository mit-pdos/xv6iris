/-
Weak: **track F, epilogue row-run CHAINING (thin slice)** (`AxRegOnly`): the inter-instruction
boundary as an opax step, and the register-only compressed row run generalized over the
instruction.

Rocq: `iris/AxRegOnly.v` @ xxvzwolszwmp (334 lines).

## What this file proves

* (c) `afRetToNextFetch`: for ANY hart state `.PHart cpu (.pure ()) rs none ib` (any instruction's
  landing state, parked-fence slot `none` as every row run concludes) and ANY `tick`, ONE
  `AxOpsem.astepProg` step labelled `LInstr` to `.PHart cpu (riscvStep tick) rs none ibNone` AT
  THE SAME ROW POSITION.  It is `WeakEvInst.pnodeStep`'s boundary (`.pure _`) arm (the reset point:
  no register write, no device change, the announced-bits bank reset to `ibNone`) routed by
  `pstepNode` (unparked) and realized as an `AStepAdmin` (`lbAdmin true LInstr` is the `instr =
  true` arm).  The register file `rs` is carried UNCHANGED across the splice.  This is the splice
  point between one row run's landing `.pure ()` and the next row run's `riscvStep tick` start.
* (a) `afRegonlyRowRun`: `AxFetch3.afCjrRowRun` with the JALR-specific `execute` derivation
  (`execEffExecuteCretZca` / `cjrSexecFacts`) pulled out into a caller-supplied hypothesis: any
  register-only COMPRESSED instruction (2-byte fetch at a 2-but-not-4-aligned pc) whose expanded
  `execute` retires with the EMPTY trace runs from position `k` to the boundary `.pure ()`.
  Composition: `execEffStepOfLeafRvc2` (with `es_x := []`), `AxFetch2.fetchPeel` (admin peel to the
  fetch node + the admin fetch step), `afAdminRunToEnd`.
* (b) (Rocq: on paper only, no lemma) the config-tower framing lemma — nothing to port.

## Deviations from Rocq

1. NAMES / VOCABULARY: as `AxFetch1`/`AxFetch3` deviation 1 (`register_lookup r (wm_regs σ)` ↦
   `σ.wmRegs r`; `eq_vec x 'b"1" = b` ↦ `(x == 1#1) = b`; `pma_allows_all` ↦ `pma_regions =
   bootPMA`; `∀ j < 4, addr_is_ram (pa_add pc j)` ↦ `inRam pc 4`; `Interface.Ret tt` ↦ `.pure ()`;
   `dom (mem s) ⊆ W` ↦ `bmDomSub s.mem W`; `ib_none` ↦ `ibNone`; `dev_state` ↦ `Efab`;
   `RiscvLang.mstate` ↦ `ExecSt`; `oib32` ↦ `Ibch`).
2. O2 STAGE C (`AxFetch1` header): `astep_prog row Tt img` ↦ `AxOpsem.astepProg row` (the
   `Tt`/`img` binders are gone).  In `afRegonlyRowRun` the premises `af_cjr_row_shape row k (pa_z
   pc)` and `fetch_answers Tt img (pa_z pc) …` (the fetch row item and the oracle) are DROPPED with
   `af_cjr_row_shape` (`AxFetch3` "Dropped"); the fetch is an admin step that keeps the position,
   so the run ends at `k` (Rocq `S k`).  The fetched-halfword round-trip (Rocq step (c)) is not
   needed (`AxFetch3` deviation 3).
3. `afRetToNextFetch` keeps Rocq's (unused) device binder `d`, now an `Efab`; the step is taken
   at `d` → `d`.

Q7 (owner ruling, `notes/weak-port-q7-sfence.md` route (a), Lean-only): `afRegonlyRowRun` takes `WeakEvLang.noSfAnn (riscvStep tick) ⟨…⟩` per tick (see `AxFetch2`'s Q7 note).

**Rocq → Lean name map.**  `af_ret_to_next_fetch` `afRetToNextFetch`, `af_regonly_row_run`
`afRegonlyRowRun`.  Neither name is in `notes/weak-port-dupnames.json`.

**Dropped:** nothing.  Counts: Rocq 2 lemmas; Lean 2 + 0 Lean-only.
-/
import Weak.AxFetch

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open Sail Sail.ConcurrencyInterfaceV1
open Sail.ArchSem (FreeM)
open LeanRV64D LeanRV64D.Functions
open Wlabel

/-! ## 1. (c) THE INTER-INSTRUCTION BOUNDARY, AS A LEMMA -/

set_option linter.unusedVariables false in
/-- Rocq `af_ret_to_next_fetch` (deviations 1-3): the landing `.pure ()` steps, for any `tick`,
to the next instruction's `riscvStep tick` at the SAME row position, registers unchanged. -/
theorem afRetToNextFetch (rs : RegFile) (ib : Ibch) (d : Efab) (cpu : CPU) (kpos : Nat)
    (row : List Lbl) :
    ∀ tick : Bool,
      AxOpsem.astepProg row
        ⟨.PHart cpu (.pure ()) rs none ib, kpos⟩ LInstr
        ⟨.PHart cpu (riscvStep tick) rs none ibNone, kpos⟩ := by
  intro tick
  exact .AStepAdmin _ kpos d LInstr _ d rfl
    ⟨rfl, none, some ibNone, none, rfl, rfl, ⟨tick, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl⟩

/-! ## 2. (a) THE REGISTER-ONLY ROW RUN, GENERALIZED OVER THE INSTRUCTION -/

/-- Rocq `af_regonly_row_run` (deviations 1, 2): `afCjrRowRun` with the instruction's `execute`
fact taken as a hypothesis — any register-only compressed instruction at a 2-but-not-4-aligned
pc runs from position `k` to the boundary `.pure ()`, still at `k`. -/
theorem afRegonlyRowRun (σ : Wmstate) (W : GSet PAddr) (pc : BitVec 64) (h : BitVec 16)
    (w : BitVec 32) (i0 i : instruction) (D D0 : Register → Bool) (dst : ExecSt)
    (cpu : CPU) (row : List Lbl) (k : Nat) (ib0 : Ibch) :
    -- the M-mode config tower
    σ.wmRegs .PC = pc →
    σ.wmRegs .cur_privilege = .Machine →
    pmpAllowsAll (σ.wmRegs .pmpcfg_n) →
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
    (∀ s : ExecSt, exec (execute i0) s = some (.ExecuteAs i, s)) →
    -- THE GENERAL "register-only" premise: `i`'s `execute` retires with NO memory effect
    (∀ b : Bool, ∃ sExec : ExecSt,
      execEff (execute i)
        (((⟨σ.wmRegs, wmemRestrict σ W, σ.wmDev⟩ : ExecSt).setReg .minstret_increment b).setReg
          .nextPC (BitVec.addInt pc 2)) = some (.Retire_Success (), sExec, []) ∧
      sExec.regs .hart_state = .HART_ACTIVE () ∧
      sExec.regs .minstret_increment = b ∧
      bmDomSub sExec.mem W) →
    ∀ tick : Bool,
    -- Q7: the instruction's run announces no sfence.vma word (header, Q7)
    WeakEvLang.noSfAnn (riscvStep tick) ⟨σ.wmRegs, wmemRestrict σ W, σ.wmDev⟩ →
    ∃ (s3 : ExecSt) (ib3 : Ibch),
      rtc (fun t1 t2 => ∃ l, AxOpsem.astepProg row t1 l t2)
        ⟨.PHart cpu (riscvStep tick) σ.wmRegs none ib0, k⟩
        ⟨.PHart cpu (.pure ()) s3.regs none ib3, k⟩ := by
  intro lpc lpriv lpmp lpma lhtif lhart lmisaS lmisaC lmIE lelp hal2 hal4 hram htext hsub
    hisRVC hagree hDmi hgood hdec hgood0 hexp hexec tick hsf
  -- (a) the whole instruction's `execEff` fact: the 2-byte fetch, no data event
  obtain ⟨t', hex, -⟩ := execEffStepOfLeafRvc2 σ W pc h w i0 i [] D D0 dst
    lpc lpriv lpmp lpma lhtif lhart lmisaS lmisaC lmIE lelp hal2 hal4 hram htext
    hsub hisRVC hagree hDmi hgood hdec hgood0 hexp hexec tick
  -- (b) the admin run to the (width-2) fetch node and the admin fetch step (position kept)
  obtain ⟨m2, s2, ib2, -, hex2, hrtcb, hsf2⟩ :=
    AxFetch2.fetchPeel (riscvStep tick) ⟨σ.wmRegs, wmemRestrict σ W, σ.wmDev⟩ ib0
      WeakFetchEff.wakIfetch pc 2 t' [] cpu k row (by decide) rfl hex hsf
  -- (d) the admin run to the boundary (no data node)
  obtain ⟨ib3, hrtcd⟩ := afAdminRunToEnd m2 s2 ib2 t' hex2 hsf2 cpu k row
  exact ⟨t', ib3, rtc_transitive hrtcb hrtcd⟩

end Weak
