/-
Weak: **track F, the AxSL instruction bridge — PART D, first file** (`AxFetch3`): the
END-OF-INSTRUCTION peel, the `jalr x0,0(ra)` (`ret`) row run, the RVC fetch twin of
`execEffStepOfLeafBase`, and the compressed `c.jr ra` / `c.ret` row run.

Rocq: `iris/AxFetch.v` @ xxvzwolszwmp, lines 1533–2157 (§2.5 the jalr/ret row run, §2.6 the RVC
(compressed) fetch twin).  Part D is split at section boundaries: `AxFetch3` (this file, §2.5–
§2.6), `AxFetch3b` (§2.7, the `c.ldsp`/`c.sdsp` row runs), `AxFetch3c` (§2.8,
`af_cldsp_cont_rd`).  Parts A/C are `Weak/AxFetch1.lean` / `Weak/AxFetch2.lean` (`AxFetch1`'s
header carries the whole port's summary and the O2 Stage C account).

## What this file proves

* §2.5 `afAdminRunToEnd`: `afAdminRunToMemread`'s twin for an EMPTY trace — if `execEff m s`
  runs to `((), s', [])`, admin-only opax steps (at the row position `kpos`, kept) reach the
  boundary `.pure ()` at `s'.regs` (the monad's `pure` is `pnodeStep`'s boundary arm).  Induction
  on the monad: the base case IS the proof (`execEff (pure y) s = some (y, s, [])` forces
  `s = s'`); a RAM read / write / barrier conses an effect onto the trace and is impossible; the
  register and announce outcomes and MMIO are admin steps, as in `afAdminRunToMemread`.
* §2.5 `afJalrRowRun`: from the hart at `riscvStep tick` at position `k`, a run — admin steps and
  the ADMIN fetch, all at `k` — to `.pure ()`: `jalr x0,0(ra)` has no data event and so, under
  Stage C, consumes NO row position.  Composition: (a) `execEffStepOfLeafBase` at
  `.JALR (zeros, .Regidx ra, zreg)` with `es_x := []`, fed by `WeakLeafJump.execEffExecuteCretZca`
  and `cjrSexecFacts`; (b) `AxFetch2.fetchPeel` (the admin peel to the fetch node + the admin
  fetch step); (d) `afAdminRunToEnd`.
* §2.6 `execEffStepOfLeafRvc2`: the run-assembly half of `WeakFetch2.wPEffOfLeafRvc2` (2-byte
  fetch at a 2-but-not-4-aligned pc, compressed decode, the EXPANSION's `execute`) as a
  standalone `∀ tick` run fact at the confined state — the instance of the Lean
  `WeakFetch2.execEffStepOfLeafRvc2St` at `⟨σ.wmRegs, wmemRestrict σ W, σ.wmDev⟩`.
* §2.6 `afCjrRowRun`: `afJalrRowRun`'s compressed twin (the kernel epilogue's own `c.jr ra`).

## Deviations from Rocq

1. NAMES / VOCABULARY: as `AxFetch1`/`AxFetch2` deviation 1 (`register_lookup r (wm_regs σ)` ↦
   `σ.wmRegs r`; `eq_vec x 'b"1" = b` ↦ `(x == 1#1) = b`; `register_lookup mseccfg … =
   mword_of_int 0` ↦ `… = 0#64`; `∀ j < 4, addr_is_ram (pa_add pc j)` ↦ `inRam pc 4`;
   `wmem_restrict σ W !! pa_add a j` ↦ `wmemRestrict σ W (a + BitVec.ofNat 64 j)`;
   `subrange_vec_dec w 15 0` ↦ `Sail.BitVec.extractLsb w 15 0`; `zeros' 12` ↦ `zeros (n := 12)`;
   `uint ra <> 0` ↦ `ra.toNat ≠ 0`; `pma_allows_all` ↦ `pma_regions = bootPMA`; `pmp_all_off` ↦
   `pmpAllOff` and `pmp_all_off_allows_all` ↦ `fun i => (h i).2`; `pmp_allows_all` ↦
   `pmpAllowsAll`; `Interface.Ret tt` ↦ the boundary `.pure ()`; `dom (mem s) ⊆ W` ↦
   `bmDomSub s.mem W`).  No name of this file is in `notes/weak-port-dupnames.json`.
2. O2 STAGE C (`AxFetch1` header): the fetch is an ADMIN step that KEEPS the row position, the
   oracle parameters `Tt`/`img` and the `fetch_answers …` premises are gone.  So
   `af_jalr_row_shape` / `af_cjr_row_shape` (whose only content was the FETCH item) carry
   nothing and are DROPPED (below), with their premise; both row runs end at position `k`
   (Rocq `S k`): a fetch-only instruction consumes no position.
3. THE ROUND-TRIP (Rocq step (c)) is not needed: as `AxFetch2` deviation 3, the admin fetch
   accepts any byte list of the width, so `AxFetch2.fetchPeel` answers it with whatever the RAM
   read returns.  The text premises stay (they feed (a)).
4. The fetch's trace element is `.WEread WeakFetchEff.wakIfetch pc n` (Rocq `wak_plain`;
   `WeakFetchEff` deviation 2).  `execEffStepOfLeafBase` takes the extra Lean premise
   `is_lpad_instruction i = false`, discharged inside `afJalrRowRun`.
5. `execEffStepOfLeafRvc2` is stated (and proved) as the instance of the Lean-only
   `WeakFetch2.execEffStepOfLeafRvc2St`, which carries Rocq's proof (`WeakFetch2` deviation 5).

Q7 (owner ruling, `notes/weak-port-q7-sfence.md` route (a), Lean-only): `afAdminRunToEnd` takes `WeakEvLang.noSfAnn m s` (as AxFetch1's peels); `afJalrRowRun`/`afCjrRowRun` take `noSfAnn (riscvStep tick) ⟨…⟩` per tick (see `AxFetch2`'s Q7 note).

**Rocq → Lean name map.**  `af_admin_run_to_end` `afAdminRunToEnd`, `af_jalr_row_run`
`afJalrRowRun`, `exec_eff_step_of_leaf_rvc2` `execEffStepOfLeafRvc2`, `af_cjr_row_run`
`afCjrRowRun`.

**Dropped (O2 Stage C: no fetch row item):** `af_jalr_row_shape`, `af_jalr_row_shape_fetch`,
`af_cfetch_ident`, `af_cjr_row_shape`, `af_cjr_row_shape_fetch` — every one is the fetch item
(or its identity / projection).  `af_cfetch_ident` / `af_cjr_row_shape` ARE named downstream
(`AxRegOnly.v`, `AxEpiChain.v`), but only as the fetch-item premise of row runs and in the
fetch-step identity check; those ports drop the premise as this file does.  Counts: Rocq 9
declarations in lines 1533–2157; Lean 4 + 0 Lean-only.
-/
import Weak.AxFetch2
import Weak.WeakLeafJump
import Weak.WeakFetch2

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open Sail Sail.ConcurrencyInterfaceV1
open Sail.ArchSem (FreeM)
open LeanRV64D LeanRV64D.Functions
open Wlabel

/-! ## 2.5 THE jalr/ret ROW RUN: the end-of-instruction peel, and the fetch-only row run -/

/-- Rocq `af_admin_run_to_end`: `afAdminRunToMemread`'s twin for an EMPTY trace — an admin-only
run (position kept) from `m` to the boundary `.pure ()` at the final registers. -/
theorem afAdminRunToEnd (m : SailM Unit) :
    ∀ (s : ExecSt) (ib : Ibch) (s' : ExecSt),
      execEff m s = some ((), s', []) →
      WeakEvLang.noSfAnn m s →
      ∀ (cpu : CPU) (kpos : Nat) (row : List Lbl),
        ∃ ib2 : Ibch,
          rtc (fun t1 t2 => ∃ l, AxOpsem.astepProg row t1 l t2)
            ⟨.PHart cpu m s.regs none ib, kpos⟩
            ⟨.PHart cpu (.pure ()) s'.regs none ib2, kpos⟩ := by
  induction m with
  | pure y =>
    intro s ib s' hex _ cpu kpos row
    simp only [execEff, Option.some.injEq, Prod.mk.injEq] at hex
    obtain ⟨-, rfl, -⟩ := hex
    exact ⟨ib, rtc_refl _⟩
  | impure call k ih =>
    intro s ib s' hex hsf cpu kpos row
    cases call with
    | error e => simp [execEff] at hex
    | ok o =>
      cases o
      case memRead n0 va req =>
        simp only [execEff] at hex
        by_cases hm : mmioAcc req.pa n0 = true
        · rw [if_pos hm] at hex
          have hdevT : devAddr req.pa = true := by
            simp only [mmioAcc, Bool.and_eq_true] at hm; exact hm.1
          cases hdr : devRead s.dev req.pa n0 with
          | none => simp only [hdr] at hex; cases hex
          | some p =>
            obtain ⟨w0, d0⟩ := p
            simp only [hdr] at hex
            simp only [WeakEvLang.noSfAnn, if_pos hm, hdr] at hsf
            obtain ⟨ib2, hrtc⟩ := ih _ (s.setDev d0) ib s' hex hsf cpu kpos row
            refine ⟨ib2, ?_⟩
            refine AxFetch1.admPrepend row cpu _ _ s.regs ib s.dev d0 .LDev none none none kpos _
              hrtc ?_ trivial
            simp only [pnodeStep, hdevT, ↓reduceIte]
            exact ⟨w0, by simp [hdr]⟩
        · rw [if_neg hm] at hex
          cases hrb : bmRead s.mem req.pa n0 with
          | none => simp only [hrb] at hex; cases hex
          | some w0 =>
            simp only [hrb] at hex
            obtain ⟨es0, _, hcons⟩ := Weff.consEqSome.1 hex
            cases hcons
      case memWrite n0 va req =>
        simp only [execEff] at hex
        cases hv : req.value with
        | none => simp only [hv] at hex; cases hex
        | some w =>
          simp only [hv] at hex
          by_cases hm : mmioAcc req.pa n0 = true
          · rw [if_pos hm] at hex
            have hdevT : devAddr req.pa = true := by
              simp only [mmioAcc, Bool.and_eq_true] at hm; exact hm.1
            cases hdw : devWrite s.dev req.pa n0 w with
            | none => simp only [hdw] at hex; cases hex
            | some d0 =>
              simp only [hdw] at hex
              simp only [WeakEvLang.noSfAnn, hv, if_pos hm, hdw] at hsf
              obtain ⟨ib2, hrtc⟩ := ih _ (s.setDev d0) ib s' hex hsf cpu kpos row
              refine ⟨ib2, ?_⟩
              refine AxFetch1.admPrepend row cpu _ _ s.regs ib s.dev d0 .LDev none none none kpos
                _ hrtc ?_ trivial
              simp only [pnodeStep, hdevT, hv, ↓reduceIte]
              simp [hdw]
          · rw [if_neg hm] at hex
            obtain ⟨es0, _, hcons⟩ := Weff.consEqSome.1 hex
            cases hcons
      case barrier b =>
        simp only [execEff] at hex
        obtain ⟨es0, _, hcons⟩ := Weff.consEqSome.1 hex
        cases hcons
      case regRead r =>
        simp only [execEff] at hex
        simp only [WeakEvLang.noSfAnn] at hsf
        obtain ⟨ib2, hrtc⟩ := ih _ s (ibRd ib r) s' hex hsf cpu kpos row
        exact ⟨ib2, AxFetch1.admPrepend row cpu _ _ s.regs ib s.dev s.dev .LSilent none
          (some (ibRd ib r)) none kpos _ hrtc ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ trivial⟩
      case regWrite r v =>
        simp only [execEff] at hex
        simp only [WeakEvLang.noSfAnn] at hsf
        obtain ⟨ib2, hrtc⟩ := ih _ (s.setReg r v) ib s' hex hsf cpu kpos row
        exact ⟨ib2, AxFetch1.admPrepend row cpu _ _ s.regs ib s.dev s.dev
          (erwLabel (erwOf (depsOfIb ib.ibBits) ib.ibRds r)) (some (s.regs.set r v)) none none
          kpos _ hrtc ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ (erwLabelLbAdmin _)⟩
      case instrAnnounce nw w =>
        simp only [execEff] at hex
        simp only [WeakEvLang.noSfAnn] at hsf
        obtain ⟨hsw, hsf⟩ := hsf
        obtain ⟨ib2, hrtc⟩ := ih _ s (ibAnn (ibOfBvn w)) s' hex hsf cpu kpos row
        exact ⟨ib2, AxFetch1.admPrepend row cpu _ _ s.regs ib s.dev s.dev .LInstr none
          (some (ibAnn (ibOfBvn w))) none kpos _ hrtc
          ⟨(annLabelNot hsw).symm, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl⟩
      all_goals first
        | (simp [execEff] at hex; done)
        | (simp only [execEff] at hex
           simp only [WeakEvLang.noSfAnn] at hsf
           obtain ⟨ib2, hrtc⟩ := ih _ s ib s' hex hsf cpu kpos row
           exact ⟨ib2, AxFetch1.admPrepend row cpu _ _ s.regs ib s.dev s.dev .LSilent none none
             none kpos _ hrtc ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ trivial⟩)

/-- Rocq `af_jalr_row_run` (deviations 1-4): the fetch glued in front of the register-only tail
of `jalr x0,0(ra)`, against the REAL `riscvStep tick` term: a run from position `k` to the
boundary `.pure ()`, still at `k` (Stage C: the fetch is admin; there is no data event). -/
theorem afJalrRowRun (σ : Wmstate) (W : GSet PAddr) (pc : BitVec 64) (w : BitVec 32)
    (ra : BitVec 5) (D : Register → Bool) (dst : ExecSt) (cpu : CPU) (row : List Lbl) (k : Nat)
    (ib0 : Ibch) :
    -- the M-mode config tower
    σ.wmRegs .PC = pc →
    σ.wmRegs .cur_privilege = .Machine →
    σ.wmRegs .mseccfg = 0#64 →
    (_get_Misa_C (σ.wmRegs .misa) == 1#1) = true →
    pmpAllOff (σ.wmRegs .pmpcfg_n) →
    σ.wmRegs .pma_regions = bootPMA →
    σ.wmRegs .htif_tohost_base = none →
    σ.wmRegs .hart_state = .HART_ACTIVE () →
    (_get_Misa_S (σ.wmRegs .misa) == 1#1) = true →
    (_get_Mstatus_MIE (σ.wmRegs .mstatus) == 1#1) = false →
    (σ.wmRegs .elp == landing_pad_bits_backwards .LP_EXPECTED) = false →
    -- the text word, in the confined memory, at a 4-aligned pc
    is_aligned_vaddr (.Virtaddr pc) 4 = true →
    inRam pc 4 →
    (∀ j : Nat, j < 4 → wmemRestrict σ W (pc + BitVec.ofNat 64 j) = some (nthByte (n := 4) w j)) →
    isRVC (Sail.BitVec.extractLsb w 15 0) = false →
    -- the decode
    (∀ r, D r = true → σ.wmRegs r = dst.regs r) →
    D .minstret_increment = false →
    goodb0 D (ext_decode w) dst = true →
    exec (ext_decode w) dst = some (.JALR (zeros (n := 12), .Regidx ra, zreg), dst) →
    -- jalr's own geometry: `jalr x0,0(ra)`, `ra ≠ x0`
    ra.toNat ≠ 0 →
    ∀ tick : Bool,
    -- Q7: the instruction's run announces no sfence.vma word (header, Q7)
    WeakEvLang.noSfAnn (riscvStep tick) ⟨σ.wmRegs, wmemRestrict σ W, σ.wmDev⟩ →
    ∃ (s3 : ExecSt) (ib3 : Ibch),
      rtc (fun t1 t2 => ∃ l, AxOpsem.astepProg row t1 l t2)
        ⟨.PHart cpu (riscvStep tick) σ.wmRegs none ib0, k⟩
        ⟨.PHart cpu (.pure ()) s3.regs none ib3, k⟩ := by
  intro lpc lpriv lsec lmisaC lpmp lpma lhtif lhart lmisaS lmIE lelp hal hram4 htext hnotRVC
    hagree hDmi hgood hdec hranz tick hsf
  -- (a) the whole instruction's `execEff` fact: the fetch, no data event
  obtain ⟨t', hex, -⟩ := execEffStepOfLeafBase σ W pc w
    (.JALR (zeros (n := 12), .Regidx ra, zreg)) [] D dst
    lpc lpriv (fun i => (lpmp i).2) lpma lhtif lhart lmisaS lmIE lelp hal hram4 htext hnotRVC
    hagree hDmi hgood hdec (by first | rfl | decide)
    (by
      intro b
      have hprivc : (((⟨σ.wmRegs, wmemRestrict σ W, σ.wmDev⟩ : ExecSt).setReg .minstret_increment
          b).setReg .nextPC (BitVec.addInt pc 4)).regs .cur_privilege = .Machine := by
        leaf_peel .cur_privilege; exact lpriv
      have hsecc : (((⟨σ.wmRegs, wmemRestrict σ W, σ.wmDev⟩ : ExecSt).setReg .minstret_increment
          b).setReg .nextPC (BitVec.addInt pc 4)).regs .mseccfg = 0#64 := by
        leaf_peel .mseccfg; exact lsec
      have hCc : (_get_Misa_C ((((⟨σ.wmRegs, wmemRestrict σ W, σ.wmDev⟩ : ExecSt).setReg
          .minstret_increment b).setReg .nextPC (BitVec.addInt pc 4)).regs .misa) == 1#1) = true := by
        leaf_peel .misa; exact lmisaC
      have he := execEffExecuteCretZca ra _ hranz hprivc hsecc hCc
      obtain ⟨F1, F2, F3, -, -⟩ := cjrSexecFacts ⟨σ.wmRegs, wmemRestrict σ W, σ.wmDev⟩ b
        (BitVec.addInt pc 4)
        (WeakLeafMret.retPc ((((⟨σ.wmRegs, wmemRestrict σ W, σ.wmDev⟩ : ExecSt).setReg
          .minstret_increment b).setReg .nextPC (BitVec.addInt pc 4)).gpr ra))
      refine ⟨_, he, ?_, F2, ?_⟩
      · exact F1.trans lhart
      · rw [F3]; exact wmemRestrictDom σ W)
    tick
  -- (b) the admin run to the fetch node and the admin fetch step (position kept)
  obtain ⟨m2, s2, ib2, -, hex2, hrtcb, hsf2⟩ :=
    AxFetch2.fetchPeel (riscvStep tick) ⟨σ.wmRegs, wmemRestrict σ W, σ.wmDev⟩ ib0
      WeakFetchEff.wakIfetch pc 4 t' [] cpu k row (by decide) rfl hex hsf
  -- (d) the admin run to the boundary, the END of the instruction (no data node)
  obtain ⟨ib3, hrtcd⟩ := afAdminRunToEnd m2 s2 ib2 t' hex2 hsf2 cpu k row
  exact ⟨t', ib3, rtc_transitive hrtcb hrtcd⟩

/-! ## 2.6 THE RVC (COMPRESSED) FETCH TWIN, and the `c.jr ra` / `c.ret` row run -/

/-- Rocq `exec_eff_step_of_leaf_rvc2` (deviations 1, 4, 5): the 2-byte-fetch, compressed-decode
twin of `execEffStepOfLeafBase` — `WeakFetch2.wPEffOfLeafRvc2`'s run-assembly half, standalone,
at the confined state. -/
theorem execEffStepOfLeafRvc2 (σ : Wmstate) (W : GSet PAddr) (pc : BitVec 64) (h : BitVec 16)
    (w : BitVec 32) (i0 i : instruction) (es_x : List Weff) (D D0 : Register → Bool)
    (dst : ExecSt) :
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
    -- the text word, IN THE CONFINED MEMORY, at a 2-but-not-4-aligned pc
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
    -- the EXPANDED instruction's `execute`, at `execEff`
    (∀ b : Bool, ∃ sExec : ExecSt,
      execEff (execute i)
        (((⟨σ.wmRegs, wmemRestrict σ W, σ.wmDev⟩ : ExecSt).setReg .minstret_increment b).setReg
          .nextPC (BitVec.addInt pc 2)) = some (.Retire_Success (), sExec, es_x) ∧
      sExec.regs .hart_state = .HART_ACTIVE () ∧
      sExec.regs .minstret_increment = b ∧
      bmDomSub sExec.mem W) →
    -- the per-tick run fact
    ∀ tick : Bool, ∃ t' : ExecSt,
      execEff (riscvStep tick) ⟨σ.wmRegs, wmemRestrict σ W, σ.wmDev⟩ =
        some ((), t', [.WEread WeakFetchEff.wakIfetch pc 2] ++ es_x) ∧
      bmDomSub t'.mem W :=
  WeakFetch2.execEffStepOfLeafRvc2St ⟨σ.wmRegs, wmemRestrict σ W, σ.wmDev⟩ W pc h w i0 i es_x D D0
    dst

/-- Rocq `af_cjr_row_run` (deviations 1-4): the COMPRESSED `c.jr ra` / `c.ret` row run — the
kernel epilogue's own instruction, at a 2-but-not-4-aligned pc: a run from position `k` to the
boundary `.pure ()`, still at `k`. -/
theorem afCjrRowRun (σ : Wmstate) (W : GSet PAddr) (pc : BitVec 64) (h : BitVec 16)
    (w : BitVec 32) (ra : BitVec 5) (i0 : instruction) (D D0 : Register → Bool) (dst : ExecSt)
    (cpu : CPU) (row : List Lbl) (k : Nat) (ib0 : Ibch) :
    -- the M-mode config tower
    σ.wmRegs .PC = pc →
    σ.wmRegs .cur_privilege = .Machine →
    σ.wmRegs .mseccfg = 0#64 →
    (_get_Misa_C (σ.wmRegs .misa) == 1#1) = true →
    pmpAllOff (σ.wmRegs .pmpcfg_n) →
    σ.wmRegs .pma_regions = bootPMA →
    σ.wmRegs .htif_tohost_base = none →
    σ.wmRegs .hart_state = .HART_ACTIVE () →
    (_get_Misa_S (σ.wmRegs .misa) == 1#1) = true →
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
      some (.ExecuteAs (.JALR (zeros (n := 12), .Regidx ra, zreg)), s)) →
    -- c.jr's own geometry
    ra.toNat ≠ 0 →
    ∀ tick : Bool,
    -- Q7: the instruction's run announces no sfence.vma word (header, Q7)
    WeakEvLang.noSfAnn (riscvStep tick) ⟨σ.wmRegs, wmemRestrict σ W, σ.wmDev⟩ →
    ∃ (s3 : ExecSt) (ib3 : Ibch),
      rtc (fun t1 t2 => ∃ l, AxOpsem.astepProg row t1 l t2)
        ⟨.PHart cpu (riscvStep tick) σ.wmRegs none ib0, k⟩
        ⟨.PHart cpu (.pure ()) s3.regs none ib3, k⟩ := by
  intro lpc lpriv lsec lmisaC lpmp lpma lhtif lhart lmisaS lmIE lelp hal2 hal4 hram htext hsub
    hisRVC hagree hDmi hgood hdec hgood0 hexp hranz tick hsf
  -- (a) the whole instruction's `execEff` fact: the 2-byte fetch, no data event
  obtain ⟨t', hex, -⟩ := execEffStepOfLeafRvc2 σ W pc h w i0
    (.JALR (zeros (n := 12), .Regidx ra, zreg)) [] D D0 dst
    lpc lpriv (fun i => (lpmp i).2) lpma lhtif lhart lmisaS lmisaC lmIE lelp hal2 hal4 hram htext
    hsub hisRVC hagree hDmi hgood hdec hgood0 hexp
    (by
      intro b
      have hprivc : (((⟨σ.wmRegs, wmemRestrict σ W, σ.wmDev⟩ : ExecSt).setReg .minstret_increment
          b).setReg .nextPC (BitVec.addInt pc 2)).regs .cur_privilege = .Machine := by
        leaf_peel .cur_privilege; exact lpriv
      have hsecc : (((⟨σ.wmRegs, wmemRestrict σ W, σ.wmDev⟩ : ExecSt).setReg .minstret_increment
          b).setReg .nextPC (BitVec.addInt pc 2)).regs .mseccfg = 0#64 := by
        leaf_peel .mseccfg; exact lsec
      have hCc : (_get_Misa_C ((((⟨σ.wmRegs, wmemRestrict σ W, σ.wmDev⟩ : ExecSt).setReg
          .minstret_increment b).setReg .nextPC (BitVec.addInt pc 2)).regs .misa) == 1#1) = true := by
        leaf_peel .misa; exact lmisaC
      have he := execEffExecuteCretZca ra _ hranz hprivc hsecc hCc
      obtain ⟨F1, F2, F3, -, -⟩ := cjrSexecFacts ⟨σ.wmRegs, wmemRestrict σ W, σ.wmDev⟩ b
        (BitVec.addInt pc 2)
        (WeakLeafMret.retPc ((((⟨σ.wmRegs, wmemRestrict σ W, σ.wmDev⟩ : ExecSt).setReg
          .minstret_increment b).setReg .nextPC (BitVec.addInt pc 2)).gpr ra))
      refine ⟨_, he, ?_, F2, ?_⟩
      · exact F1.trans lhart
      · rw [F3]; exact wmemRestrictDom σ W)
    tick
  -- (b) the admin run to the (width-2) fetch node and the admin fetch step (position kept)
  obtain ⟨m2, s2, ib2, -, hex2, hrtcb, hsf2⟩ :=
    AxFetch2.fetchPeel (riscvStep tick) ⟨σ.wmRegs, wmemRestrict σ W, σ.wmDev⟩ ib0
      WeakFetchEff.wakIfetch pc 2 t' [] cpu k row (by decide) rfl hex hsf
  -- (d) the admin run to the boundary (no data node)
  obtain ⟨ib3, hrtcd⟩ := afAdminRunToEnd m2 s2 ib2 t' hex2 hsf2 cpu k row
  exact ⟨t', ib3, rtc_transitive hrtcb hrtcd⟩

end Weak
