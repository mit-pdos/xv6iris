/-
Weak: **the CONSECUTIVE kernel epilogue** (LB/AxSL rev 7) `c.sdsp ra, imm(sp) ; c.ldsp ra,
imm(sp) ; c.jr ra` as ONE connected opax run, its reload value from ownership, and `c.jr`'s jump
target.

Rocq: `iris/AxEpiChain.v` @ xxvzwolszwmp (1406 lines).

## What this file proves (the Rocq header, in substance)

* §1 `afCsdspFrame`: the STORE mirror of `AxFetch3c.afCldspRowRun'` + `afAdminRunToEnd` fused:
  `c.sdsp` from `riscvStep tick` at `k` through the admin fetch, the data WRITE at `k` and the
  store's continuation to the boundary `.pure ()` at `k + 1`, exposing what `afCsdspRowRun`
  discards — the landing register file's `PC = pc + 2` and a frame over every register outside
  the seven instruction-bookkeeping ones (`PC`, `nextPC`, `minstret_increment`, `minstret`,
  `mcycle`, `mtime`, `mip`; the store writes no GPR).
* §2 `epilogueConsecutiveRet`: the connected run — `afCsdspFrame`, the boundary
  (`AxRegOnly.afRetToNextFetch`), `AxFetch3c.afCldspContRd` (the reload, answered at the ROW's
  recorded store value `AxEpiShape.epiWriteVal row k`), a second boundary, `AxFetch3.afCjrRowRun`
  — SEGMENTED at the reload's data read (an `areadStep`).  `Hbridge` (the GPR `ra` holds the
  spilled word) is DISCHARGED by `afCldspContRd`'s register conclusion; `c.jr`'s M-mode tower is
  RE-ESTABLISHED from the two frames; `graphValue` and the jump come from
  `AxEpiShape.epilogueRetTargetSpillReloadOfRow` at `kLd := k + 1` with the trivial middle.
  Closed modulo `Hram8Ld` (the reload is fed the PRE-SPILL confined memory: `ra` tracks
  sequential memory, not ownership).
* §2 `epilogueConsecutiveRetOwn`: the fix — `Hram8Ld` deleted, `AxFetch3c.afCldspContRdAll` at
  `vs := epiWriteVal row k`, one new geometry premise `HdisjLd` (c.ldsp's text word misses the
  stack slot).  Smell test (Rocq's): the `ra`/PC conclusion is produced by ONE call to
  `epilogueRetTargetSpillReloadOfRow`, which cannot be built without the ownership premises.

RESIDUALS (named premises, as in Rocq): the pre-spill token's well-formedness
(`HsBefore`/`HlensBefore`/`HwrBefore`/`HchBefore`/`HownBefore`/`HlinkBefore`) and the POST-SPILL
`tokn` + coverage wand (the spill write rule's own postcondition, taken as a precondition); the
row shapes `HshapeSd`/`HshapeLd`; the M-mode tower at `σ0` only (`Lpc`…`Lsec`); the text/decode
facts; the decode-bridge frame-safety `HDLdSafe`/`HDJrSafe`; `Hra`/`Hra2`; `HVsvs` (the stored
register value is the row's recorded bytes — `AStepWrite` checks them); `Hram8Ld` (first
capstone) / `HdisjLd` (second).  The run stops at `c.jr`'s own landing `.pure ()`; the jump is
stated as a pure `execEff` fact about the register file reached there.

## Deviations from Rocq

1. NAMES / VOCABULARY: camelCase (map below; none is in `notes/weak-port-dupnames.json`); as
   `AxFetch3c` deviation 1 / `AxEpilogue` deviations 3-4 (`register_lookup r (wm_regs σ)` ↦
   `σ.wmRegs r`; `register_beq r X = false` ↦ `r ≠ X`; `eq_vec x 'b"1" = b` ↦ `(x == 1#1) = b`;
   `pma_allows_all` ↦ `pma_regions = bootPMA`; `∀ j < n, addr_is_ram (pa_add a j)` ↦ `inRam a n`;
   `wmem_restrict σ W !! pa_add a j` ↦ `wmemRestrict σ W (a + BitVec.ofNat 64 j)`;
   `add_vec_int` ↦ `BitVec.addInt`; `mword_of_int 0` ↦ `0#64`; the GPR read at `rs2` ↦
   `uxaXget σ.wmRegs rs2`, at `sp` ↦ `σ.wmRegs .x2`; `MState r m d` ↦ `⟨r, m, d⟩ : ExecSt`;
   `WMState regs1 (wm_img σ0) …` ↦ `{ σ0 with wmRegs := regs1 }`; `ib_none` ↦ `ibNone`; the
   boundary's device `wm_dev σ0` ↦ `efInit σ0.wmDev`; `Interface.Ret tt` ↦ `.pure ()`;
   `uint ra <> 0` ↦ `ra.toNat ≠ 0`; `Hs !! j` ↦ `Hs[j]?`; `last` ↦ `getLast?`; `.*1` ↦
   `map Prod.fst`).  The theorems' hypotheses are named binders as in Rocq (camelCase).
2. O2 STAGE C (`AxFetch1` header; `AxFetch3`/`AxFetch3b` "Dropped"): rows have NO fetch items
   and no oracle.  So (i) `Tt`/`img` and every `fetch_answers` premise (`Hfa_sd`/`Hfa_ld`/`Hfa_jr`,
   and `af_csdsp_frame`'s `Hfa`) are gone; (ii) `Hshape_jr : af_cjr_row_shape …` is DROPPED
   (`af_cjr_row_shape` was only the fetch item); the row shapes lose their pc argument; (iii)
   RE-INDEXED: Rocq's positions k (sdsp fetch), S k (spill data), S(S k) (ldsp fetch),
   S(S(S k)) (reload data), S⁴ k (ldsp landing = c.jr fetch), S⁵ k (c.jr landing) become `k`
   (spill data), `k + 1` (reload data), `k + 2` (ldsp landing = c.jr start = c.jr landing: a
   fetch-only instruction consumes no position).  Hence the spill event is `(i, k)` (Rocq
   `(i, S k)`): `writenHist (i, k)`, `{[(i, k) := 1]}`, `gpo … (i, k)` in `HownBefore`/
   `HlinkBefore`; the reload is `(i, k + 1)` (Rocq `(i, S(S(S k)))`): the coverage wand's
   `gmoLt w (i, k + 1)`, `graphValue GD (i, k + 1)`; `HshapeSd : afCsdspRowShape row k a`,
   `HshapeLd : afCldspRowShape row (k + 1) a`; `af_csdsp_frame`'s data premise is at `row[k]?`
   (Rocq `row !! S k`) and its run ends at `k + 1` (Rocq `S (S k)`).  The middle
   `epiMidRegOnly row k (k + 1)` is vacuous (Rocq: one fetch read in between, discharged via the
   dropped `af_cldsp_row_shape_fetch`).  The fetch round-trip of Rocq's `af_csdsp_frame` proof
   is not needed (`AxFetch2` deviation 3).
3. GPR REGISTERS (as `AxFetch3c` deviation 3, `AxFetch5` deviation 2): Lean has no
   `gpr_of_Z`.  `HD_jr_safe`'s `register_beq r (R_bitvector_64 (gpr_of_Z (uint ra))) = false` ↦
   `r ≠ AxFetch5.gprReg ra`; the reload's frame is `AxFetch3c`'s split pair (non-GPR registers /
   GPR indices `j ≠ ra`), recombined by the Lean-only `AxEpiChain.gprAgree`.
4. `afCsdspFrame` is proved by INLINING the `execEffStepOfLeafRvc2` construction (as
   `AxFetch3c.afCldspRowRun'Mem`), so its premises are Rocq's (no `bmDomSub`/`Hwdom`), and peels
   the store's continuation with `afAdminRunToEnd`; that needs `noSfAnn` at the write node, which
   `afAdminRunToMemwrite` does not return — the Lean-only `AxEpiChain.adminRunToMemwriteSf` is
   its copy with that conjunct.
5. Q7 (owner ruling, `notes/weak-port-q7-sfence.md` route (a), Lean-only; the row runs take
   `noSfAnn (riscvStep tick) ⟨…⟩`): `afCsdspFrame` takes it per tick (at `σ`'s confined state).
   After Q10 (`WeakEffSkel`/`WeakFetchEff` yield `noSfAnn`), `afCldspContRd`/`afCjrRowRun` no
   longer take it, so the capstones keep only `HsfSd` (at `σ0`, for `afCsdspFrame`'s write-node
   peel, which the inlined construction still needs).
6. CONTEXT (as `AxEpiShape` deviation 3): the section's `invGS_gen`/`axirisG` instances are used
   by nothing and dropped; `γ`, `GD`, `Hcons` are explicit arguments; `axlogG Σ hent` ↦
   `[AxlogG GF Hent]`.  `Hpaz : paZ ea = a` is kept (and `subst`ed in the proofs).
7. STATEMENT SHAPES: `⊢ Hcov -∗ tokn … -∗ ⌜∃ …⌝` (as `AxEpilogue` deviation 6); the reload's
   data identity `ident : AidentT` and continuation `K : List (BitVec 8) → Athread`.

**Rocq → Lean name map.**  `af_csdsp_frame` `afCsdspFrame`, `epilogue_consecutive_ret`
`epilogueConsecutiveRet`, `epilogue_consecutive_ret_own` `epilogueConsecutiveRetOwn`.
Lean-only (file-qualified): `AxEpiChain.adminRunToMemwriteSf` (deviation 4),
`AxEpiChain.gprAgree` (deviation 3), `AxEpiChain.gprNe7` (GPRs are none of the seven
bookkeeping registers), `AxEpiChain.addInt22` (Rocq `avi_assoc` at `2 + 2 = 4`).

**Dropped:** nothing (Rocq 3 declarations; Lean 3 + 4 Lean-only).  **Not ported:** the two
`Print Assumptions` commands (the lint's axiom check covers them).
-/
import Weak.AxEpiShape
import Weak.AxRegOnly

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open Sail Sail.ConcurrencyInterfaceV1
open Sail.ArchSem (FreeM)
open LeanRV64D LeanRV64D.Functions
open Wlabel

/-! ## 0. Lean-only helpers -/

/-- (Lean-only, deviation 4) `afAdminRunToMemwrite` that ALSO returns `noSfAnn` at the reached
write node (the read peel `afAdminRunToMemread` already does), so the store's continuation can
be peeled to the boundary by `afAdminRunToEnd`.  Same proof, the extra conjunct threaded. -/
theorem AxEpiChain.adminRunToMemwriteSf (m : SailM Unit) :
    ∀ (s : ExecSt) (ib : Ibch) (ak : AkInfo) (pa : PAddr) (n : Nat) (v : BitVec (8 * n))
      (s' : ExecSt) (es : List Weff),
      n ≠ 0 →
      execEff m s = some ((), s', .WEwrite ak pa n v :: es) →
      WeakEvLang.noSfAnn m s →
      ∀ (cpu : CPU) (kpos : Nat) (row : List Lbl),
        ∃ (s2 : ExecSt) (ib2 : Ibch) (va : Nat)
          (req : Mem_write_request n va Arch.pa Arch.translation Arch.arch_ak)
          (KK : Result (Option Bool) Arch.abort → SailM Unit),
          classify req.access_kind = ak ∧ req.pa = pa ∧ req.value = some v ∧
          devAddr pa = false ∧ s2.mem = s.mem ∧
          execEff (.impure (.ok (.memWrite n va req)) KK) s2 =
            some ((), s', .WEwrite ak pa n v :: es) ∧
          rtc (fun t1 t2 => ∃ l, AxOpsem.astepProg row t1 l t2)
            ⟨.PHart cpu m s.regs none ib, kpos⟩
            ⟨.PHart cpu (.impure (.ok (.memWrite n va req)) KK) s2.regs none ib2, kpos⟩ ∧
          WeakEvLang.noSfAnn (.impure (.ok (.memWrite n va req)) KK) s2 := by
  induction m with
  | pure y =>
    intro s ib ak pa n v s' es _ hex
    simp [execEff] at hex
  | impure call k ih =>
    intro s ib ak pa n v s' es hn hex hsf cpu kpos row
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
            obtain ⟨s2, ib2, va2, req2, KK, hcl, hpa, hval, hdev, hmem, hee, hrtc, hns⟩ :=
              ih _ (s.setDev d0) ib ak pa n v s' es hn hex hsf cpu kpos row
            refine ⟨s2, ib2, va2, req2, KK, hcl, hpa, hval, hdev, hmem, hee, ?_, hns⟩
            refine AxFetch1.admPrepend row cpu _ _ s.regs ib s.dev d0
              (.LDev .rd (paZ req.pa) (WeakInterpProj.wbytes n0 w0)) none none none kpos _
              hrtc ?_ trivial
            simp only [pnodeStep, hdevT, ↓reduceIte]
            exact ⟨w0, by simp [hdr]⟩
        · rw [if_neg hm] at hex
          cases hrb : bmRead s.mem req.pa n0 with
          | none => simp only [hrb] at hex; cases hex
          | some w0 =>
            simp only [hrb] at hex
            obtain ⟨es0, _, hcons⟩ := Weff.consEqSome.1 hex
            simp at hcons
      case memWrite n0 va req =>
        have hex0 := hex
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
              obtain ⟨s2, ib2, va2, req2, KK, hcl, hpa, hval, hdev, hmem, hee, hrtc, hns⟩ :=
                ih _ (s.setDev d0) ib ak pa n v s' es hn hex hsf cpu kpos row
              refine ⟨s2, ib2, va2, req2, KK, hcl, hpa, hval, hdev, hmem, hee, ?_, hns⟩
              refine AxFetch1.admPrepend row cpu _ _ s.regs ib s.dev d0
                (.LDev .wr (paZ req.pa) (WeakInterpProj.wbytes n0 w)) none none none kpos
                _ hrtc ?_ trivial
              simp only [pnodeStep, hdevT, hv, ↓reduceIte]
              simp [hdw]
          · rw [if_neg hm] at hex
            obtain ⟨es0, _, hcons⟩ := Weff.consEqSome.1 hex
            simp only [List.cons.injEq] at hcons
            obtain ⟨he, rfl⟩ := hcons
            injection he with hak hpa hnn hvv
            subst hnn
            have hvv' : v = w := eq_of_heq hvv
            subst hvv'
            have hdevF : devAddr req.pa = false := by
              cases hd : devAddr req.pa
              · rfl
              · simp [mmioAcc, hd, hn] at hm
            exact ⟨s, ib, va, req, k, hak.symm, hpa.symm, hv, hpa ▸ hdevF, rfl, hex0,
              rtc_refl _, hsf⟩
      case barrier b =>
        simp only [execEff] at hex
        obtain ⟨es0, _, hcons⟩ := Weff.consEqSome.1 hex
        simp at hcons
      case regRead r =>
        simp only [execEff] at hex
        simp only [WeakEvLang.noSfAnn] at hsf
        obtain ⟨s2, ib2, va, req, KK, hcl, hpa, hval, hdev, hmem, hee, hrtc, hns⟩ :=
          ih _ s (ibRd ib r) ak pa n v s' es hn hex hsf cpu kpos row
        exact ⟨s2, ib2, va, req, KK, hcl, hpa, hval, hdev, hmem, hee,
          AxFetch1.admPrepend row cpu _ _ s.regs ib s.dev s.dev .LSilent none (some (ibRd ib r))
            none kpos _ hrtc ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ trivial, hns⟩
      case regWrite r v0 =>
        simp only [execEff] at hex
        simp only [WeakEvLang.noSfAnn] at hsf
        obtain ⟨s2, ib2, va, req, KK, hcl, hpa, hval, hdev, hmem, hee, hrtc, hns⟩ :=
          ih _ (s.setReg r v0) ib ak pa n v s' es hn hex hsf cpu kpos row
        exact ⟨s2, ib2, va, req, KK, hcl, hpa, hval, hdev, hmem, hee,
          AxFetch1.admPrepend row cpu _ _ s.regs ib s.dev s.dev
            (erwLabel (erwOf (depsOfIb ib.ibBits) ib.ibRds r)) (some (s.regs.set r v0)) none none
            kpos _ hrtc ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ (erwLabelLbAdmin _), hns⟩
      case instrAnnounce nw w =>
        simp only [execEff] at hex
        simp only [WeakEvLang.noSfAnn] at hsf
        obtain ⟨hsw, hsf⟩ := hsf
        obtain ⟨s2, ib2, va, req, KK, hcl, hpa, hval, hdev, hmem, hee, hrtc, hns⟩ :=
          ih _ s (ibAnn (ibOfBvn w)) ak pa n v s' es hn hex hsf cpu kpos row
        exact ⟨s2, ib2, va, req, KK, hcl, hpa, hval, hdev, hmem, hee,
          AxFetch1.admPrepend row cpu _ _ s.regs ib s.dev s.dev .LInstr none
            (some (ibAnn (ibOfBvn w))) none kpos _ hrtc
            ⟨(annLabelNot hsw).symm, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl, hns⟩
      all_goals first
        | (simp [execEff] at hex; done)
        | (simp only [execEff] at hex
           simp only [WeakEvLang.noSfAnn] at hsf
           obtain ⟨s2, ib2, va, req, KK, hcl, hpa, hval, hdev, hmem, hee, hrtc, hns⟩ :=
             ih _ s ib ak pa n v s' es hn hex hsf cpu kpos row
           exact ⟨s2, ib2, va, req, KK, hcl, hpa, hval, hdev, hmem, hee,
             AxFetch1.admPrepend row cpu _ _ s.regs ib s.dev s.dev .LSilent none none none kpos _
               hrtc ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ trivial, hns⟩)


/-- (Lean-only, deviation 3) a GPR register other than `ra`'s own (`AxFetch5.gprReg ra`) is
read by `uxaXget` at an index other than `ra`: two files that agree on every GPR index but `ra`
agree on it. -/
theorem AxEpiChain.gprAgree (r : Register) (hr : r ∈ uxaGprs) (ra : BitVec 5)
    (hne : r ≠ AxFetch5.gprReg ra) (f f' : RegFile)
    (hg : ∀ j : BitVec 5, j ≠ ra → uxaXget f j = uxaXget f' j) : f r = f' r := by
  simp only [uxaGprs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hg 1#5 (fun e => hne (by subst e; rfl))
  · exact hg 2#5 (fun e => hne (by subst e; rfl))
  · exact hg 3#5 (fun e => hne (by subst e; rfl))
  · exact hg 4#5 (fun e => hne (by subst e; rfl))
  · exact hg 5#5 (fun e => hne (by subst e; rfl))
  · exact hg 6#5 (fun e => hne (by subst e; rfl))
  · exact hg 7#5 (fun e => hne (by subst e; rfl))
  · exact hg 8#5 (fun e => hne (by subst e; rfl))
  · exact hg 9#5 (fun e => hne (by subst e; rfl))
  · exact hg 10#5 (fun e => hne (by subst e; rfl))
  · exact hg 11#5 (fun e => hne (by subst e; rfl))
  · exact hg 12#5 (fun e => hne (by subst e; rfl))
  · exact hg 13#5 (fun e => hne (by subst e; rfl))
  · exact hg 14#5 (fun e => hne (by subst e; rfl))
  · exact hg 15#5 (fun e => hne (by subst e; rfl))
  · exact hg 16#5 (fun e => hne (by subst e; rfl))
  · exact hg 17#5 (fun e => hne (by subst e; rfl))
  · exact hg 18#5 (fun e => hne (by subst e; rfl))
  · exact hg 19#5 (fun e => hne (by subst e; rfl))
  · exact hg 20#5 (fun e => hne (by subst e; rfl))
  · exact hg 21#5 (fun e => hne (by subst e; rfl))
  · exact hg 22#5 (fun e => hne (by subst e; rfl))
  · exact hg 23#5 (fun e => hne (by subst e; rfl))
  · exact hg 24#5 (fun e => hne (by subst e; rfl))
  · exact hg 25#5 (fun e => hne (by subst e; rfl))
  · exact hg 26#5 (fun e => hne (by subst e; rfl))
  · exact hg 27#5 (fun e => hne (by subst e; rfl))
  · exact hg 28#5 (fun e => hne (by subst e; rfl))
  · exact hg 29#5 (fun e => hne (by subst e; rfl))
  · exact hg 30#5 (fun e => hne (by subst e; rfl))
  · exact hg 31#5 (fun e => hne (by subst e; rfl))

/-- (Lean-only) the GPRs are none of the seven instruction-bookkeeping registers. -/
theorem AxEpiChain.gprNe7 :
    ∀ r ∈ uxaGprs, r ≠ .PC ∧ r ≠ .nextPC ∧ r ≠ .minstret_increment ∧ r ≠ .minstret ∧
      r ≠ .mcycle ∧ r ≠ .mtime ∧ r ≠ .mip := by
  decide

/-- (Lean-only) Rocq `avi_assoc` at the epilogue's offsets. -/
theorem AxEpiChain.addInt22 (pc : BitVec 64) :
    BitVec.addInt (BitVec.addInt pc 2) 2 = BitVec.addInt pc 4 := by
  unfold BitVec.addInt
  rw [BitVec.add_assoc, show BitVec.ofInt 64 2 + BitVec.ofInt 64 2 = BitVec.ofInt 64 4 by decide]

/-! ## 1. `afCsdspFrame`: the STORE mirror of `afCldspRowRun'` + `afAdminRunToEnd` -/

/-- Rocq `af_csdsp_frame` (deviations 1-2, 4): `c.sdsp rs2, imm(sp)` run from `riscvStep tick`
at `k` through the admin fetch (position kept), the data WRITE at `k`, and the store's
continuation to the boundary `.pure ()` at `k + 1`; the landing register file has `PC = pc + 2`
and agrees with `σ` outside the seven instruction-bookkeeping registers. -/
theorem afCsdspFrame (σ : Wmstate) (W : GSet PAddr) (pc : BitVec 64) (h : BitVec 16)
    (w : BitVec 32) (rs2 : BitVec 5) (imm : BitVec 12) (ea : PAddr) (vs : BitVec 64)
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
    (∀ s : ExecSt, exec (execute i0) s = some (.ExecuteAs (.STORE (imm, .Regidx rs2, sp, 8)), s)) →
    σ.wmRegs .x2 + sign_extend (m := 64) imm = ea →
    uxaXget σ.wmRegs rs2 = vs →
    is_aligned_paddr (.Physaddr ea) 8 = true →
    inRam ea 8 →
    afCsdspRowShape row k (paZ ea) →
    (row[k]?).bind lblData = some (WeakInterpProj.wbytes 8 vs) →
    ∀ tick : Bool,
    -- Q7: the instruction's run announces no sfence.vma word (header, Q7)
    WeakEvLang.noSfAnn (riscvStep tick) ⟨σ.wmRegs, wmemRestrict σ W, σ.wmDev⟩ →
    ∃ (s4 : ExecSt) (ib4 : Ibch),
      rtc (fun t1 t2 => ∃ l, AxOpsem.astepProg row t1 l t2)
        ⟨.PHart cpu (riscvStep tick) σ.wmRegs none ib0, k⟩
        ⟨.PHart cpu (.pure ()) s4.regs none ib4, k + 1⟩ ∧
      s4.regs .PC = BitVec.addInt pc 2 ∧
      (∀ r, r ≠ .PC → r ≠ .nextPC → r ≠ .minstret_increment → r ≠ .minstret → r ≠ .mcycle →
        r ≠ .mtime → r ≠ .mip → s4.regs r = σ.wmRegs r) := by
  intro lpc lpriv lmprv lpmm lpmp lpma lhtif lhart lmisaS lmisaC lmIE lelp hal2 hal4 hram htext
    hsub hisRVC hagree hDmi hgood hdec hgood0 hexp hea hvs hal8 hram8 hshape hdat tick hsf
  obtain ⟨lbd, hrowd, hidd⟩ := hshape
  -- the inlined `execEffStepOfLeafRvc2` construction (keeps the post-instruction state visible)
  obtain ⟨b, hsi⟩ := execEffShouldIncMinstretSome (σ.wmRegs .cur_privilege)
    (⟨σ.wmRegs, wmemRestrict σ W, σ.wmDev⟩ : ExecSt)
  have lpriv_a : (hartActiveSA ⟨σ.wmRegs, wmemRestrict σ W, σ.wmDev⟩ b).regs .cur_privilege =
      .Machine := by
    rw [WeakFetchEff.saLookup _ _ _ (by decide)]; exact lpriv
  have lpc_a : (hartActiveSA ⟨σ.wmRegs, wmemRestrict σ W, σ.wmDev⟩ b).regs .PC = pc := by
    rw [WeakFetchEff.saLookup _ _ _ (by decide)]; exact lpc
  have lhart_a : (hartActiveSA ⟨σ.wmRegs, wmemRestrict σ W, σ.wmDev⟩ b).regs .hart_state =
      .HART_ACTIVE () := by
    rw [WeakFetchEff.saLookup _ _ _ (by decide)]; exact lhart
  have lelp_a : ((hartActiveSA ⟨σ.wmRegs, wmemRestrict σ W, σ.wmDev⟩ b).regs .elp ==
      landing_pad_bits_backwards .LP_EXPECTED) = false := by
    rw [WeakFetchEff.saLookup _ _ _ (by decide)]; exact lelp
  have hdisp : execEff (dispatchInterrupt .Machine)
      (hartActiveSA ⟨σ.wmRegs, wmemRestrict σ W, σ.wmDev⟩ b) =
      some (none, hartActiveSA ⟨σ.wmRegs, wmemRestrict σ W, σ.wmDev⟩ b, []) :=
    execEffDispatchInterruptMachineNone _
      (by rw [WeakFetchEff.saLookup _ _ _ (by decide)]; exact lmisaS)
      (by rw [WeakFetchEff.saLookup _ _ _ (by decide)]; exact lmIE)
  have hzca : execEff (currentlyEnabled .Ext_Zca)
      (hartActiveSA ⟨σ.wmRegs, wmemRestrict σ W, σ.wmDev⟩ b) =
      some (true, hartActiveSA ⟨σ.wmRegs, wmemRestrict σ W, σ.wmDev⟩ b, []) :=
    execEffCurrentlyEnabledZca _ (by rw [WeakFetchEff.saLookup _ _ _ (by decide)]; exact lmisaC)
  have hfetch : execEff (fetch ()) (hartActiveSA ⟨σ.wmRegs, wmemRestrict σ W, σ.wmDev⟩ b) =
      some (.F_RVC h, hartActiveSA ⟨σ.wmRegs, wmemRestrict σ W, σ.wmDev⟩ b,
        [.WEread WeakFetchEff.wakIfetch pc 2]) :=
    execEffFetchFlatRvc2 _ pc h
      (by rw [WeakFetchEff.saLookup _ _ _ (by decide)]; exact fun i => (lpmp i).2)
      (by rw [WeakFetchEff.saLookup _ _ _ (by decide)]; exact lpma)
      (by rw [WeakFetchEff.saLookup _ _ _ (by decide)]; exact lmisaC)
      lpc_a lpriv_a
      (by rw [WeakFetchEff.saLookup _ _ _ (by decide)]; exact lhtif)
      hal4 ⟨hal2, hram, w, ⟨hsub, hisRVC⟩, htext⟩
  have hdec_a : execEff (ext_decode_compressed h)
      (hartActiveSA ⟨σ.wmRegs, wmemRestrict σ W, σ.wmDev⟩ b) =
      some (i0, hartActiveSA ⟨σ.wmRegs, wmemRestrict σ W, σ.wmDev⟩ b, []) := by
    refine execEffDecodeBridge D (ext_decode_compressed h) dst _ i0 ?_ hgood hdec
    intro r hD
    have hne : r ≠ .minstret_increment := by
      rintro rfl
      rw [hDmi] at hD
      exact absurd hD (by decide)
    rw [WeakFetchEff.saLookup r _ b hne]
    exact hagree r hD
  have hexp_a : execEff (execute i0)
      ((hartActiveSA ⟨σ.wmRegs, wmemRestrict σ W, σ.wmDev⟩ b).setReg .nextPC (BitVec.addInt pc 2)) =
      some (.ExecuteAs (.STORE (imm, .Regidx rs2, sp, 8)),
        (hartActiveSA ⟨σ.wmRegs, wmemRestrict σ W, σ.wmDev⟩ b).setReg .nextPC
          (BitVec.addInt pc 2), []) :=
    execEffOfGoodb0Self D0 (execute i0) _ _ (hgood0 _) (hexp _)
  have hea2 : (⟨σ.wmRegs, wmemRestrict σ W, σ.wmDev⟩ : ExecSt).gpr (zero_extend (m := 5) 0b10#2) +
      sign_extend (m := 64) imm = ea := by
    unfold ExecSt.gpr; rw [AxFetch3b.spGpr]; exact hea
  have hvs2 : (⟨σ.wmRegs, wmemRestrict σ W, σ.wmDev⟩ : ExecSt).gpr rs2 = vs := by
    unfold ExecSt.gpr; exact hvs
  have hex := execEffSd8OffAt ⟨σ.wmRegs, wmemRestrict σ W, σ.wmDev⟩ b (BitVec.addInt pc 2)
    (zero_extend (m := 5) 0b10#2) rs2 imm ea vs lpriv lmprv lpmm lpmp lpma lhtif hea2 hvs2 hal8
    hram8
  obtain ⟨Fhart, Fmi, -⟩ :=
    storeRegsFacts ⟨σ.wmRegs, wmemRestrict σ W, σ.wmDev⟩ b (BitVec.addInt pc 2)
  have hstep := execEffRiscvStepRvc ⟨σ.wmRegs, wmemRestrict σ W, σ.wmDev⟩ _ h i0
    (.STORE (imm, .Regidx rs2, sp, 8)) pc b [.WEread WeakFetchEff.wakIfetch pc 2]
    [.WEwrite wakPlain ea 8 vs] hsi lhart_a lpriv_a hdisp hfetch hdec_a lelp_a lpc_a hzca hexp_a
    hex (Fhart.trans lhart) Fmi
  obtain ⟨t', ht', -, -, hframet⟩ := afRiscvStepAllTicksFrame _ _ _ hstep tick
  -- the run: the admin peel + the admin fetch, the peel to the write node, the write
  obtain ⟨m2, s2, ib2, -, hex2, hrtcb, hsf2⟩ :=
    AxFetch2.fetchPeel (riscvStep tick) ⟨σ.wmRegs, wmemRestrict σ W, σ.wmDev⟩ ib0
      WeakFetchEff.wakIfetch pc 2 t' [.WEwrite wakPlain ea 8 vs] cpu k row (by decide) rfl ht' hsf
  obtain ⟨s3, ib3, va, req2, KK2, hcld, hpad, hvald, hdevd, -, hee3, hrtcd, hns3⟩ :=
    AxEpiChain.adminRunToMemwriteSf m2 s2 ib2 wakPlain ea 8 vs t' [] (by decide) hex2 hsf2 cpu k
      row
  have hwr := afAstepWriteOfMemwrite row cpu 8 va req2 KK2 s3.regs ib3 (efInit s3.dev) k lbd vs
    (by rw [hpad]; exact hdevd) (by decide) (by rw [hcld]; rfl) hvald hrowd
    (by rw [hidd, hcld, hpad]; rfl) (by rw [hrowd] at hdat; exact hdat)
  -- the store's continuation, admin only, to the boundary
  have hm : mmioAcc req2.pa 8 = false := by simp [mmioAcc, hpad, hdevd]
  simp only [execEff, hvald, hm, Bool.false_eq_true, ↓reduceIte] at hee3
  obtain ⟨es0, h0, hcons⟩ := Weff.consEqSome.1 hee3
  have hes : es0 = [] := (List.cons.inj hcons).2.symm
  subst hes
  simp only [WeakEvLang.noSfAnn, hvald, hm, Bool.false_eq_true, ↓reduceIte] at hns3
  obtain ⟨ib4, hrtc4⟩ := afAdminRunToEnd _ _ ib3 t' h0 hns3 cpu (k + 1) row
  refine ⟨t', ib4, rtc_transitive (rtc_transitive hrtcb hrtcd) (rtc_l ⟨_, hwr⟩ hrtc4), ?_, ?_⟩
  · rw [hframet .PC (by decide) (by decide) (by decide)]
    cases b
    · simp only [hartActiveSFinal, hartActiveSTick, Bool.false_eq_true, ↓reduceIte,
        ExecSt.setReg_regs, RegFile.set_same]
    · simp only [hartActiveSFinal, hartActiveSTick, ↓reduceIte]
      rw [setLookupNe .PC .minstret _ _ (by decide)]
      simp only [ExecSt.setReg_regs, RegFile.set_same]
  · intro r h1 h2 h3 h4 h5 h6 h7
    rw [hframet r h5 h6 h7]
    cases b
    · simp only [hartActiveSFinal, hartActiveSTick, Bool.false_eq_true, ↓reduceIte]
      rw [setLookupNe r .PC _ _ h1]
      dsimp only
      rw [setLookupNe r .nextPC _ _ h2, setLookupNe r .minstret_increment _ _ h3]
    · simp only [hartActiveSFinal, hartActiveSTick, ↓reduceIte]
      rw [setLookupNe r .minstret _ _ h4, setLookupNe r .PC _ _ h1]
      dsimp only
      rw [setLookupNe r .nextPC _ _ h2, setLookupNe r .minstret_increment _ _ h3]

/-! ## 2. `epilogueConsecutiveRet`: the capstone -/

section epiChain

open Iris Iris.BI Iris.ProofMode Iris.Std.PartialMap

variable {GF : BundledGFunctors} [AxlogG GF Hent]

set_option linter.unusedVariables false in
/-- Rocq `epilogue_consecutive_ret` (deviations 1-3, 5-7): the CONSECUTIVE kernel epilogue
`c.sdsp ra, imm(sp) ; c.ldsp ra, imm(sp) ; c.jr ra` — spill data at `k`, reload data at `k + 1`,
`c.jr` fetch-only (position `k + 2` kept) — as one connected run SEGMENTED at the reload's data
read, with the reload's value from ownership and `c.jr`'s jump target.  CLOSED MODULO `Hram8Ld`
(the reload's row run is fed the PRE-SPILL confined memory at `ea`; see
`epilogueConsecutiveRetOwn`). -/
theorem epilogueConsecutiveRet (γ : GName) (GD : Gdexec) (Hcons : rvwmoCatConsistent GD)
    (i : Nat) (row : List Lbl) (k : Nat) (cpu : CPU) (ib0 : Ibch) (σ0 : Wmstate) (W : GSet PAddr)
    (Hprog : GD.gdG.gxProg[i]? = some row)
    -- ---------- c.sdsp, at row position k, pc `pc0` ----------
    (pc0 : BitVec 64) (hSd : BitVec 16) (wSd : BitVec 32) (rs2 : BitVec 5) (immSd : BitVec 12)
    (ea : PAddr) (a : Int) (Hpaz : paZ ea = a) (vsSd : BitVec 64)
    (i0Sd : instruction) (DSd D0Sd : Register → Bool) (dstSd : ExecSt)
    -- the M-mode config tower, AT THE START of the epilogue
    (Lpc : σ0.wmRegs .PC = pc0)
    (Lpriv : σ0.wmRegs .cur_privilege = .Machine)
    (Lmprv : (_get_Mstatus_MPRV (σ0.wmRegs .mstatus) == 1#1) = false)
    (Lpmm : pmm_mode_backwards (_get_Seccfg_PMM (σ0.wmRegs .mseccfg)) = .PMM_Disabled)
    (Lpmp : pmpAllOff (σ0.wmRegs .pmpcfg_n))
    (Lpma : σ0.wmRegs .pma_regions = bootPMA)
    (Lhtif : σ0.wmRegs .htif_tohost_base = none)
    (Lhart : σ0.wmRegs .hart_state = .HART_ACTIVE ())
    (LmisaS : (_get_Misa_S (σ0.wmRegs .misa) == 1#1) = true)
    (LmisaC : (_get_Misa_C (σ0.wmRegs .misa) == 1#1) = true)
    (LmIE : (_get_Mstatus_MIE (σ0.wmRegs .mstatus) == 1#1) = false)
    (Lelp : (σ0.wmRegs .elp == landing_pad_bits_backwards .LP_EXPECTED) = false)
    (Lsec : σ0.wmRegs .mseccfg = 0#64)
    -- c.sdsp's own text word + decode
    (Hal2Sd : is_aligned_vaddr (.Virtaddr pc0) 2 = true)
    (Hal4Sd : is_aligned_vaddr (.Virtaddr pc0) 4 = false)
    (HramSd : inRam pc0 4)
    (HtextSd : ∀ j : Nat, j < 4 →
      wmemRestrict σ0 W (pc0 + BitVec.ofNat 64 j) = some (nthByte (n := 4) wSd j))
    (HsubSd : Sail.BitVec.extractLsb wSd 15 0 = hSd)
    (HisRVCSd : isRVC hSd = true)
    (HagreeSd : ∀ r, DSd r = true → σ0.wmRegs r = dstSd.regs r)
    (HDmiSd : DSd .minstret_increment = false)
    (HgoodSd : goodb0 DSd (ext_decode_compressed hSd) dstSd = true)
    (HdecSd : exec (ext_decode_compressed hSd) dstSd = some (i0Sd, dstSd))
    (Hgood0Sd : ∀ s : ExecSt, goodb0 D0Sd (execute i0Sd) s = true)
    (HexpSd : ∀ s : ExecSt, exec (execute i0Sd) s =
      some (.ExecuteAs (.STORE (immSd, .Regidx rs2, sp, 8)), s))
    (HeaSd : σ0.wmRegs .x2 + sign_extend (m := 64) immSd = ea)
    (HvsSd : uxaXget σ0.wmRegs rs2 = vsSd)
    (Hal8 : is_aligned_paddr (.Physaddr ea) 8 = true)
    (Hram8 : inRam ea 8)
    (Hwdom : ∀ j : Nat, j < 8 → ea + BitVec.ofNat 64 j ∈ W)
    (HshapeSd : afCsdspRowShape row k a)
    (HVsvs : vsSd = wordOfBytes 8 (epiWriteVal row k))
    -- ---------- c.ldsp, at row position k + 1, pc `pc0 + 2`, same `ea` ----------
    (hLd : BitVec 16) (wLd : BitVec 32) (ra : BitVec 5)
    (i0Ld : instruction) (DLd D0Ld : Register → Bool) (dstLd : ExecSt)
    (Hra : ra.toNat ≠ 0) (Hra2 : ra.toNat ≠ 2)
    (Hal2Ld : is_aligned_vaddr (.Virtaddr (BitVec.addInt pc0 2)) 2 = true)
    (Hal4Ld : is_aligned_vaddr (.Virtaddr (BitVec.addInt pc0 2)) 4 = false)
    (HramLd : inRam (BitVec.addInt pc0 2) 4)
    (HtextLd : ∀ j : Nat, j < 4 → wmemRestrict σ0 W (BitVec.addInt pc0 2 + BitVec.ofNat 64 j) =
      some (nthByte (n := 4) wLd j))
    (HsubLd : Sail.BitVec.extractLsb wLd 15 0 = hLd)
    (HisRVCLd : isRVC hLd = true)
    (HagreeLd : ∀ r, DLd r = true → σ0.wmRegs r = dstLd.regs r)
    (HDLdSafe : ∀ r, DLd r = true →
      r ≠ .PC ∧ r ≠ .nextPC ∧ r ≠ .minstret_increment ∧ r ≠ .minstret ∧ r ≠ .mcycle ∧
      r ≠ .mtime ∧ r ≠ .mip)
    (HDmiLd : DLd .minstret_increment = false)
    (HgoodLd : goodb0 DLd (ext_decode_compressed hLd) dstLd = true)
    (HdecLd : exec (ext_decode_compressed hLd) dstLd = some (i0Ld, dstLd))
    (Hgood0Ld : ∀ s : ExecSt, goodb0 D0Ld (execute i0Ld) s = true)
    (HexpLd : ∀ s : ExecSt, exec (execute i0Ld) s =
      some (.ExecuteAs (.LOAD (immSd, sp, .Regidx ra, false, 8)), s))
    (Hram8Ld : ∀ j : Nat, j < 8 → wmemRestrict σ0 W (ea + BitVec.ofNat 64 j) =
      some (nthByte (n := 8) (wordOfBytes 8 (epiWriteVal row k)) j))
    (HshapeLd : afCldspRowShape row (k + 1) a)
    -- ---------- c.jr, at row position k + 2, pc `pc0 + 4` ----------
    (hJr : BitVec 16) (wJr : BitVec 32)
    (i0Jr : instruction) (DJr D0Jr : Register → Bool) (dstJr : ExecSt)
    (Hal2Jr : is_aligned_vaddr (.Virtaddr (BitVec.addInt pc0 4)) 2 = true)
    (Hal4Jr : is_aligned_vaddr (.Virtaddr (BitVec.addInt pc0 4)) 4 = false)
    (HramJr : inRam (BitVec.addInt pc0 4) 4)
    (HtextJr : ∀ j : Nat, j < 4 → wmemRestrict σ0 W (BitVec.addInt pc0 4 + BitVec.ofNat 64 j) =
      some (nthByte (n := 4) wJr j))
    (HsubJr : Sail.BitVec.extractLsb wJr 15 0 = hJr)
    (HisRVCJr : isRVC hJr = true)
    (HagreeJr : ∀ r, DJr r = true → σ0.wmRegs r = dstJr.regs r)
    (HDJrSafe : ∀ r, DJr r = true →
      r ≠ AxFetch5.gprReg ra ∧
      r ≠ .PC ∧ r ≠ .nextPC ∧ r ≠ .minstret_increment ∧ r ≠ .minstret ∧ r ≠ .mcycle ∧
      r ≠ .mtime ∧ r ≠ .mip)
    (HDmiJr : DJr .minstret_increment = false)
    (HgoodJr : goodb0 DJr (ext_decode_compressed hJr) dstJr = true)
    (HdecJr : exec (ext_decode_compressed hJr) dstJr = some (i0Jr, dstJr))
    (Hgood0Jr : ∀ s : ExecSt, goodb0 D0Jr (execute i0Jr) s = true)
    (HexpJr : ∀ s : ExecSt, exec (execute i0Jr) s =
      some (.ExecuteAs (.JALR (zeros (n := 12), .Regidx ra, zreg)), s))
    -- ---------- the pre-spill ownership token ----------
    (HsBefore : List (List Hent)) (HlensBefore : HsBefore.length = 8)
    (HwrBefore : ∀ (j : Nat) (H : List Hent), HsBefore[j]? = some H →
      ∀ p, p ∈ H → gwritesByte GD.gdG p.1 (a + (j : Int)) p.2)
    (HchBefore : ∀ (j : Nat) (H : List Hent), HsBefore[j]? = some H →
      chainWith (gmoLt GD.gdG) (H.map Prod.fst))
    (HownBefore : ∀ (j : Nat) (H : List Hent), HsBefore[j]? = some H →
      ∀ w v, gwritesByte GD.gdG w (a + (j : Int)) v → WeakRvwmoGraph.gpo GD.gdG w (i, k) →
        w ∈ H.map Prod.fst)
    (HlinkBefore : ∀ (j : Nat) (H : List Hent) wlast vlast, HsBefore[j]? = some H →
      H.getLast? = some (wlast, vlast) → WeakRvwmoGraph.gpo GD.gdG wlast (i, k))
    -- ---------- Q7 (Lean-only, header): the three runs announce no sfence.vma word ----------
    (HsfSd : WeakEvLang.noSfAnn (riscvStep true) ⟨σ0.wmRegs, wmemRestrict σ0 W, σ0.wmDev⟩) :
    ⊢ (∀ (j : Nat) (w : Geid) (v : BitVec 8), ⌜gwritesByte GD.gdG w (a + (j : Int)) v⌝ -∗
        ⌜gmoLt GD.gdG w (i, k + 1)⌝ -∗
        ∃ H' : List Hent, ⌜w ∈ H'.map Prod.fst⌝ ∗ histSnap (GF := GF) γ (a + (j : Int)) H') -∗
      tokn γ GD a (writenHist (i, k) (epiWriteVal row k) HsBefore)
        ({[(i, k) := (1 : Qp)]} : GMapF Geid Qp) -∗
      ⌜∃ (regsMid regsEnd : RegFile) (ibMid ibEnd : Ibch) (tRd : Athread) (ident : AidentT)
          (K : List (BitVec 8) → Athread),
        rtc (fun t1 t2 => ∃ l, AxOpsem.astepProg row t1 l t2)
          ⟨.PHart cpu (riscvStep true) σ0.wmRegs none ib0, k⟩ tRd ∧
        areadStep row tRd ident K ∧
        rtc (fun t1 t2 => ∃ l, AxOpsem.astepProg row t1 l t2)
          (K (epiWriteVal row k)) ⟨.PHart cpu (.pure ()) regsMid none ibMid, k + 2⟩ ∧
        rtc (fun t1 t2 => ∃ l, AxOpsem.astepProg row t1 l t2)
          ⟨.PHart cpu (.pure ()) regsMid none ibMid, k + 2⟩
          ⟨.PHart cpu (.pure ()) regsEnd none ibEnd, k + 2⟩ ∧
        graphValue GD (i, k + 1) = some (epiWriteVal row k) ∧
        execEff (execute (.JALR (zeros (n := 12), .Regidx ra, zreg)))
            (⟨regsMid, wmemRestrict σ0 W, σ0.wmDev⟩ : ExecSt) =
          some (RETIRE_SUCCESS,
            (⟨regsMid, wmemRestrict σ0 W, σ0.wmDev⟩ : ExecSt).setReg .nextPC
              (WeakLeafMret.retPc (wordOfBytes 8 (epiWriteVal row k))), []) ∧
        ((⟨regsMid, wmemRestrict σ0 W, σ0.wmDev⟩ : ExecSt).setReg .nextPC
            (WeakLeafMret.retPc (wordOfBytes 8 (epiWriteVal row k)))).regs .nextPC =
          WeakLeafMret.retPc (wordOfBytes 8 (epiWriteVal row k))⌝ := by
  subst Hpaz
  -- (1a) the spill: c.sdsp's own connected run, via `afCsdspFrame`
  have HshapeSd0 := HshapeSd
  obtain ⟨lbd, Hrowd, Hidd⟩ := HshapeSd0
  obtain ⟨Vs, kCls, Hlbd, HlenVs⟩ := aidentInvStore lbd false (paZ ea) 8 Hidd
  have Hev : epiWriteVal row k = Vs := by simp only [epiWriteVal, Hrowd, Hlbd]
  have Hlen : (epiWriteVal row k).length = 8 := Hev ▸ HlenVs
  have HdatSd : (row[k]?).bind lblData = some (WeakInterpProj.wbytes 8 vsSd) := by
    rw [Hrowd, Hlbd, HVsvs, Hev, wbytesWordOfBytes 8 Vs HlenVs]; rfl
  obtain ⟨s1, ib1, HrunSd, Hpc1, HFsd⟩ :=
    afCsdspFrame σ0 W pc0 hSd wSd rs2 immSd ea vsSd i0Sd DSd D0Sd dstSd cpu row k ib0
      Lpc Lpriv Lmprv Lpmm Lpmp Lpma Lhtif Lhart LmisaS LmisaC LmIE Lelp
      Hal2Sd Hal4Sd HramSd HtextSd HsubSd HisRVCSd HagreeSd HDmiSd HgoodSd HdecSd Hgood0Sd HexpSd
      HeaSd HvsSd Hal8 Hram8 HshapeSd HdatSd true HsfSd
  -- (1b) the boundary: `.pure ()` at k + 1 → `riscvStep` at k + 1
  have Hbnd1 := afRetToNextFetch s1.regs ib1 (efInit σ0.wmDev) cpu (k + 1) row true
  have hF1 : ∀ r : Register, (r ≠ .PC ∧ r ≠ .nextPC ∧ r ≠ .minstret_increment ∧ r ≠ .minstret ∧
      r ≠ .mcycle ∧ r ≠ .mtime ∧ r ≠ .mip) → s1.regs r = σ0.wmRegs r :=
    fun r h => HFsd r h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2.1 h.2.2.2.2.2.2
  -- decode-bridge transport for c.ldsp, at `s1.regs`
  have HagreeLd1 : ∀ r, DLd r = true → s1.regs r = dstLd.regs r :=
    fun r hr => (hF1 r (HDLdSafe r hr)).trans (HagreeLd r hr)
  -- `sp` survives the spill (STORE writes no GPR), and the config tower
  have HeaLd1 : s1.regs .x2 + sign_extend (m := 64) immSd = ea := by
    rw [hF1 .x2 (by decide)]; exact HeaSd
  have Lpriv1 : s1.regs .cur_privilege = .Machine := by
    rw [hF1 .cur_privilege (by decide)]; exact Lpriv
  have Lmprv1 : (_get_Mstatus_MPRV (s1.regs .mstatus) == 1#1) = false := by
    rw [hF1 .mstatus (by decide)]; exact Lmprv
  have Lpmm1 : pmm_mode_backwards (_get_Seccfg_PMM (s1.regs .mseccfg)) = .PMM_Disabled := by
    rw [hF1 .mseccfg (by decide)]; exact Lpmm
  have Lpmp1 : pmpAllOff (s1.regs .pmpcfg_n) := by
    rw [hF1 .pmpcfg_n (by decide)]; exact Lpmp
  have Lpma1 : s1.regs .pma_regions = bootPMA := by
    rw [hF1 .pma_regions (by decide)]; exact Lpma
  have Lhtif1 : s1.regs .htif_tohost_base = none := by
    rw [hF1 .htif_tohost_base (by decide)]; exact Lhtif
  have Lhart1 : s1.regs .hart_state = .HART_ACTIVE () := by
    rw [hF1 .hart_state (by decide)]; exact Lhart
  have LmisaS1 : (_get_Misa_S (s1.regs .misa) == 1#1) = true := by
    rw [hF1 .misa (by decide)]; exact LmisaS
  have LmisaC1 : (_get_Misa_C (s1.regs .misa) == 1#1) = true := by
    rw [hF1 .misa (by decide)]; exact LmisaC
  have LmIE1 : (_get_Mstatus_MIE (s1.regs .mstatus) == 1#1) = false := by
    rw [hF1 .mstatus (by decide)]; exact LmIE
  have Lelp1 : (s1.regs .elp == landing_pad_bits_backwards .LP_EXPECTED) = false := by
    rw [hF1 .elp (by decide)]; exact Lelp
  -- (1c)+(2) the reload, at `s1.regs`, answered at the ROW's own value
  obtain ⟨s3, ib3, va, req2, KK2, s4, ib4, -, -, HrunLd, HarwLd, Hrtc2Ld, HrdReg, HpcReg, HFrLd,
      HFgLd⟩ :=
    afCldspContRd { σ0 with wmRegs := s1.regs } W (BitVec.addInt pc0 2) hLd wLd ra immSd ea i0Ld DLd
      D0Ld dstLd cpu row (k + 1) ibNone
      Hpc1 Lpriv1 Lmprv1 Lpmm1 Lpmp1 Lpma1 Lhtif1 Lhart1 LmisaS1 LmisaC1 LmIE1 Lelp1
      Hal2Ld Hal4Ld HramLd HtextLd HsubLd HisRVCLd HagreeLd1 HDmiLd HgoodLd HdecLd Hgood0Ld HexpLd
      Hra HeaLd1 Hal8 Hram8 HshapeLd (epiWriteVal row k) Hlen Hram8Ld true
  -- (3) c.jr's config tower, transported across BOTH boundaries
  have hJ : ∀ r : Register, r ∉ uxaGprs → (r ≠ .PC ∧ r ≠ .nextPC ∧ r ≠ .minstret_increment ∧
      r ≠ .minstret ∧ r ≠ .mcycle ∧ r ≠ .mtime ∧ r ≠ .mip) → s4.regs r = σ0.wmRegs r :=
    fun r hg h => (HFrLd r hg h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2.1
      h.2.2.2.2.2.2).trans (hF1 r h)
  have hGj : ∀ j : BitVec 5, j ≠ ra → uxaXget s4.regs j = uxaXget σ0.wmRegs j := by
    intro j hj
    have e := HFgLd j hj
    unfold ExecSt.gpr at e
    rw [e]
    exact uxaXget_congr _ _ (fun r hr => hF1 r (AxEpiChain.gprNe7 r hr)) j
  have HPCJr : s4.regs .PC = BitVec.addInt pc0 4 := HpcReg.trans (AxEpiChain.addInt22 pc0)
  have Hbridge : (⟨s4.regs, wmemRestrict σ0 W, σ0.wmDev⟩ : ExecSt).gpr ra =
      wordOfBytes 8 (epiWriteVal row k) := by
    unfold ExecSt.gpr at HrdReg ⊢; exact HrdReg
  have HagreeJr1 : ∀ r, DJr r = true → s4.regs r = dstJr.regs r := by
    intro r hr
    obtain ⟨hra, hs⟩ := HDJrSafe r hr
    refine Eq.trans ?_ (HagreeJr r hr)
    by_cases hg : r ∈ uxaGprs
    · exact AxEpiChain.gprAgree r hg ra hra _ _ hGj
    · exact hJ r hg hs
  have LprivM : s4.regs .cur_privilege = .Machine := by
    rw [hJ .cur_privilege (by decide) (by decide)]; exact Lpriv
  have LsecM : s4.regs .mseccfg = 0#64 := by
    rw [hJ .mseccfg (by decide) (by decide)]; exact Lsec
  have LmisaCM : (_get_Misa_C (s4.regs .misa) == 1#1) = true := by
    rw [hJ .misa (by decide) (by decide)]; exact LmisaC
  have LpmpM : pmpAllOff (s4.regs .pmpcfg_n) := by
    rw [hJ .pmpcfg_n (by decide) (by decide)]; exact Lpmp
  have LpmaM : s4.regs .pma_regions = bootPMA := by
    rw [hJ .pma_regions (by decide) (by decide)]; exact Lpma
  have LhtifM : s4.regs .htif_tohost_base = none := by
    rw [hJ .htif_tohost_base (by decide) (by decide)]; exact Lhtif
  have LhartM : s4.regs .hart_state = .HART_ACTIVE () := by
    rw [hJ .hart_state (by decide) (by decide)]; exact Lhart
  have LmisaSM : (_get_Misa_S (s4.regs .misa) == 1#1) = true := by
    rw [hJ .misa (by decide) (by decide)]; exact LmisaS
  have LmIEM : (_get_Mstatus_MIE (s4.regs .mstatus) == 1#1) = false := by
    rw [hJ .mstatus (by decide) (by decide)]; exact LmIE
  have LelpM : (s4.regs .elp == landing_pad_bits_backwards .LP_EXPECTED) = false := by
    rw [hJ .elp (by decide) (by decide)]; exact Lelp
  -- (1d) the second boundary, then c.jr's own run (fetch-only: position kept)
  have Hbnd2 := afRetToNextFetch s4.regs ib4 (efInit σ0.wmDev) cpu (k + 2) row true
  obtain ⟨s5, ib5, HrunJr⟩ :=
    afCjrRowRun { σ0 with wmRegs := s4.regs } W (BitVec.addInt pc0 4) hJr wJr ra i0Jr DJr D0Jr
      dstJr cpu row (k + 2) ibNone
      HPCJr LprivM LsecM LmisaCM LpmpM LpmaM LhtifM LhartM LmisaSM LmIEM LelpM
      Hal2Jr Hal4Jr HramJr HtextJr HsubJr HisRVCJr HagreeJr1 HDmiJr HgoodJr HdecJr Hgood0Jr HexpJr
      Hra true
  -- (2) `graphValue` and the PC target, from AxEpiShape's spill/reload capstone
  have Hmid : epiMidRegOnly row k (k + 1) := by
    intro p lb h1 h2 _
    omega
  iintro Hcov Htoks
  ihave %H := epilogueRetTargetSpillReloadOfRow (GF := GF) γ GD Hcons i row k (k + 1) (paZ ea)
    Hprog HshapeSd HshapeLd (by omega) Hmid ⟨.PHart cpu (riscvStep true) σ0.wmRegs none ib0, k⟩
    HsBefore HlensBefore HwrBefore HchBefore HownBefore HlinkBefore ra Hra
    ⟨s4.regs, wmemRestrict σ0 W, σ0.wmDev⟩ LprivM LsecM LmisaCM Hbridge $$ Hcov Htoks
  obtain ⟨Hval, Hexec, Hpcj⟩ := H
  ipureintro
  -- assemble the SEGMENTED connected run
  exact ⟨s4.regs, s5.regs, ib4, ib5,
    ⟨.PHart cpu (.impure (.ok (.memRead 8 va req2)) KK2) s3.regs none ib3, k + 1⟩,
    .IRead (classify req2.access_kind).akSync (paZ req2.pa) 8,
    fun vs' => ⟨.PHart cpu (KK2 (.Ok (wordOfBytes 8 vs', none))) s3.regs none ib3, k + 1 + 1⟩,
    rtc_transitive HrunSd (rtc_l ⟨LInstr, Hbnd1⟩ HrunLd), HarwLd, Hrtc2Ld,
    rtc_l ⟨LInstr, Hbnd2⟩ HrunJr, Hval, Hexec, Hpcj⟩

set_option linter.unusedVariables false in
/-- Rocq `epilogue_consecutive_ret_own` (deviations 1-3, 5-7): `epilogueConsecutiveRet` with
`Hram8Ld` DELETED — the reload's continuation spec comes from `afCldspContRdAll` at the row's own
recorded value `epiWriteVal row k` (fed a `bmWrite`-patched confined memory, so no memory-content
premise), at the price of the geometry fact `HdisjLd` (c.ldsp's text word misses the stack
slot). -/
theorem epilogueConsecutiveRetOwn (γ : GName) (GD : Gdexec) (Hcons : rvwmoCatConsistent GD)
    (i : Nat) (row : List Lbl) (k : Nat) (cpu : CPU) (ib0 : Ibch) (σ0 : Wmstate) (W : GSet PAddr)
    (Hprog : GD.gdG.gxProg[i]? = some row)
    -- ---------- c.sdsp, at row position k, pc `pc0` ----------
    (pc0 : BitVec 64) (hSd : BitVec 16) (wSd : BitVec 32) (rs2 : BitVec 5) (immSd : BitVec 12)
    (ea : PAddr) (a : Int) (Hpaz : paZ ea = a) (vsSd : BitVec 64)
    (i0Sd : instruction) (DSd D0Sd : Register → Bool) (dstSd : ExecSt)
    -- the M-mode config tower, AT THE START of the epilogue
    (Lpc : σ0.wmRegs .PC = pc0)
    (Lpriv : σ0.wmRegs .cur_privilege = .Machine)
    (Lmprv : (_get_Mstatus_MPRV (σ0.wmRegs .mstatus) == 1#1) = false)
    (Lpmm : pmm_mode_backwards (_get_Seccfg_PMM (σ0.wmRegs .mseccfg)) = .PMM_Disabled)
    (Lpmp : pmpAllOff (σ0.wmRegs .pmpcfg_n))
    (Lpma : σ0.wmRegs .pma_regions = bootPMA)
    (Lhtif : σ0.wmRegs .htif_tohost_base = none)
    (Lhart : σ0.wmRegs .hart_state = .HART_ACTIVE ())
    (LmisaS : (_get_Misa_S (σ0.wmRegs .misa) == 1#1) = true)
    (LmisaC : (_get_Misa_C (σ0.wmRegs .misa) == 1#1) = true)
    (LmIE : (_get_Mstatus_MIE (σ0.wmRegs .mstatus) == 1#1) = false)
    (Lelp : (σ0.wmRegs .elp == landing_pad_bits_backwards .LP_EXPECTED) = false)
    (Lsec : σ0.wmRegs .mseccfg = 0#64)
    -- c.sdsp's own text word + decode
    (Hal2Sd : is_aligned_vaddr (.Virtaddr pc0) 2 = true)
    (Hal4Sd : is_aligned_vaddr (.Virtaddr pc0) 4 = false)
    (HramSd : inRam pc0 4)
    (HtextSd : ∀ j : Nat, j < 4 →
      wmemRestrict σ0 W (pc0 + BitVec.ofNat 64 j) = some (nthByte (n := 4) wSd j))
    (HsubSd : Sail.BitVec.extractLsb wSd 15 0 = hSd)
    (HisRVCSd : isRVC hSd = true)
    (HagreeSd : ∀ r, DSd r = true → σ0.wmRegs r = dstSd.regs r)
    (HDmiSd : DSd .minstret_increment = false)
    (HgoodSd : goodb0 DSd (ext_decode_compressed hSd) dstSd = true)
    (HdecSd : exec (ext_decode_compressed hSd) dstSd = some (i0Sd, dstSd))
    (Hgood0Sd : ∀ s : ExecSt, goodb0 D0Sd (execute i0Sd) s = true)
    (HexpSd : ∀ s : ExecSt, exec (execute i0Sd) s =
      some (.ExecuteAs (.STORE (immSd, .Regidx rs2, sp, 8)), s))
    (HeaSd : σ0.wmRegs .x2 + sign_extend (m := 64) immSd = ea)
    (HvsSd : uxaXget σ0.wmRegs rs2 = vsSd)
    (Hal8 : is_aligned_paddr (.Physaddr ea) 8 = true)
    (Hram8 : inRam ea 8)
    (Hwdom : ∀ j : Nat, j < 8 → ea + BitVec.ofNat 64 j ∈ W)
    (HshapeSd : afCsdspRowShape row k a)
    (HVsvs : vsSd = wordOfBytes 8 (epiWriteVal row k))
    -- ---------- c.ldsp, at row position k + 1, pc `pc0 + 2`, same `ea` ----------
    (hLd : BitVec 16) (wLd : BitVec 32) (ra : BitVec 5)
    (i0Ld : instruction) (DLd D0Ld : Register → Bool) (dstLd : ExecSt)
    (Hra : ra.toNat ≠ 0) (Hra2 : ra.toNat ≠ 2)
    (Hal2Ld : is_aligned_vaddr (.Virtaddr (BitVec.addInt pc0 2)) 2 = true)
    (Hal4Ld : is_aligned_vaddr (.Virtaddr (BitVec.addInt pc0 2)) 4 = false)
    (HramLd : inRam (BitVec.addInt pc0 2) 4)
    (HtextLd : ∀ j : Nat, j < 4 → wmemRestrict σ0 W (BitVec.addInt pc0 2 + BitVec.ofNat 64 j) =
      some (nthByte (n := 4) wLd j))
    (HsubLd : Sail.BitVec.extractLsb wLd 15 0 = hLd)
    (HisRVCLd : isRVC hLd = true)
    (HagreeLd : ∀ r, DLd r = true → σ0.wmRegs r = dstLd.regs r)
    (HDLdSafe : ∀ r, DLd r = true →
      r ≠ .PC ∧ r ≠ .nextPC ∧ r ≠ .minstret_increment ∧ r ≠ .minstret ∧ r ≠ .mcycle ∧
      r ≠ .mtime ∧ r ≠ .mip)
    (HDmiLd : DLd .minstret_increment = false)
    (HgoodLd : goodb0 DLd (ext_decode_compressed hLd) dstLd = true)
    (HdecLd : exec (ext_decode_compressed hLd) dstLd = some (i0Ld, dstLd))
    (Hgood0Ld : ∀ s : ExecSt, goodb0 D0Ld (execute i0Ld) s = true)
    (HexpLd : ∀ s : ExecSt, exec (execute i0Ld) s =
      some (.ExecuteAs (.LOAD (immSd, sp, .Regidx ra, false, 8)), s))
    (HdisjLd : ∀ i j : Nat, i < 4 → j < 8 →
      BitVec.addInt pc0 2 + BitVec.ofNat 64 i ≠ ea + BitVec.ofNat 64 j)
    (HshapeLd : afCldspRowShape row (k + 1) a)
    -- ---------- c.jr, at row position k + 2, pc `pc0 + 4` ----------
    (hJr : BitVec 16) (wJr : BitVec 32)
    (i0Jr : instruction) (DJr D0Jr : Register → Bool) (dstJr : ExecSt)
    (Hal2Jr : is_aligned_vaddr (.Virtaddr (BitVec.addInt pc0 4)) 2 = true)
    (Hal4Jr : is_aligned_vaddr (.Virtaddr (BitVec.addInt pc0 4)) 4 = false)
    (HramJr : inRam (BitVec.addInt pc0 4) 4)
    (HtextJr : ∀ j : Nat, j < 4 → wmemRestrict σ0 W (BitVec.addInt pc0 4 + BitVec.ofNat 64 j) =
      some (nthByte (n := 4) wJr j))
    (HsubJr : Sail.BitVec.extractLsb wJr 15 0 = hJr)
    (HisRVCJr : isRVC hJr = true)
    (HagreeJr : ∀ r, DJr r = true → σ0.wmRegs r = dstJr.regs r)
    (HDJrSafe : ∀ r, DJr r = true →
      r ≠ AxFetch5.gprReg ra ∧
      r ≠ .PC ∧ r ≠ .nextPC ∧ r ≠ .minstret_increment ∧ r ≠ .minstret ∧ r ≠ .mcycle ∧
      r ≠ .mtime ∧ r ≠ .mip)
    (HDmiJr : DJr .minstret_increment = false)
    (HgoodJr : goodb0 DJr (ext_decode_compressed hJr) dstJr = true)
    (HdecJr : exec (ext_decode_compressed hJr) dstJr = some (i0Jr, dstJr))
    (Hgood0Jr : ∀ s : ExecSt, goodb0 D0Jr (execute i0Jr) s = true)
    (HexpJr : ∀ s : ExecSt, exec (execute i0Jr) s =
      some (.ExecuteAs (.JALR (zeros (n := 12), .Regidx ra, zreg)), s))
    -- ---------- the pre-spill ownership token ----------
    (HsBefore : List (List Hent)) (HlensBefore : HsBefore.length = 8)
    (HwrBefore : ∀ (j : Nat) (H : List Hent), HsBefore[j]? = some H →
      ∀ p, p ∈ H → gwritesByte GD.gdG p.1 (a + (j : Int)) p.2)
    (HchBefore : ∀ (j : Nat) (H : List Hent), HsBefore[j]? = some H →
      chainWith (gmoLt GD.gdG) (H.map Prod.fst))
    (HownBefore : ∀ (j : Nat) (H : List Hent), HsBefore[j]? = some H →
      ∀ w v, gwritesByte GD.gdG w (a + (j : Int)) v → WeakRvwmoGraph.gpo GD.gdG w (i, k) →
        w ∈ H.map Prod.fst)
    (HlinkBefore : ∀ (j : Nat) (H : List Hent) wlast vlast, HsBefore[j]? = some H →
      H.getLast? = some (wlast, vlast) → WeakRvwmoGraph.gpo GD.gdG wlast (i, k))
    -- ---------- Q7 (Lean-only, header): the three runs announce no sfence.vma word ----------
    (HsfSd : WeakEvLang.noSfAnn (riscvStep true) ⟨σ0.wmRegs, wmemRestrict σ0 W, σ0.wmDev⟩) :
    ⊢ (∀ (j : Nat) (w : Geid) (v : BitVec 8), ⌜gwritesByte GD.gdG w (a + (j : Int)) v⌝ -∗
        ⌜gmoLt GD.gdG w (i, k + 1)⌝ -∗
        ∃ H' : List Hent, ⌜w ∈ H'.map Prod.fst⌝ ∗ histSnap (GF := GF) γ (a + (j : Int)) H') -∗
      tokn γ GD a (writenHist (i, k) (epiWriteVal row k) HsBefore)
        ({[(i, k) := (1 : Qp)]} : GMapF Geid Qp) -∗
      ⌜∃ (regsMid regsEnd : RegFile) (ibMid ibEnd : Ibch) (tRd : Athread) (ident : AidentT)
          (K : List (BitVec 8) → Athread),
        rtc (fun t1 t2 => ∃ l, AxOpsem.astepProg row t1 l t2)
          ⟨.PHart cpu (riscvStep true) σ0.wmRegs none ib0, k⟩ tRd ∧
        areadStep row tRd ident K ∧
        rtc (fun t1 t2 => ∃ l, AxOpsem.astepProg row t1 l t2)
          (K (epiWriteVal row k)) ⟨.PHart cpu (.pure ()) regsMid none ibMid, k + 2⟩ ∧
        rtc (fun t1 t2 => ∃ l, AxOpsem.astepProg row t1 l t2)
          ⟨.PHart cpu (.pure ()) regsMid none ibMid, k + 2⟩
          ⟨.PHart cpu (.pure ()) regsEnd none ibEnd, k + 2⟩ ∧
        graphValue GD (i, k + 1) = some (epiWriteVal row k) ∧
        execEff (execute (.JALR (zeros (n := 12), .Regidx ra, zreg)))
            (⟨regsMid, wmemRestrict σ0 W, σ0.wmDev⟩ : ExecSt) =
          some (RETIRE_SUCCESS,
            (⟨regsMid, wmemRestrict σ0 W, σ0.wmDev⟩ : ExecSt).setReg .nextPC
              (WeakLeafMret.retPc (wordOfBytes 8 (epiWriteVal row k))), []) ∧
        ((⟨regsMid, wmemRestrict σ0 W, σ0.wmDev⟩ : ExecSt).setReg .nextPC
            (WeakLeafMret.retPc (wordOfBytes 8 (epiWriteVal row k)))).regs .nextPC =
          WeakLeafMret.retPc (wordOfBytes 8 (epiWriteVal row k))⌝ := by
  subst Hpaz
  -- (1a) the spill: c.sdsp's own connected run, via `afCsdspFrame`
  have HshapeSd0 := HshapeSd
  obtain ⟨lbd, Hrowd, Hidd⟩ := HshapeSd0
  obtain ⟨Vs, kCls, Hlbd, HlenVs⟩ := aidentInvStore lbd false (paZ ea) 8 Hidd
  have Hev : epiWriteVal row k = Vs := by simp only [epiWriteVal, Hrowd, Hlbd]
  have Hlen : (epiWriteVal row k).length = 8 := Hev ▸ HlenVs
  have HdatSd : (row[k]?).bind lblData = some (WeakInterpProj.wbytes 8 vsSd) := by
    rw [Hrowd, Hlbd, HVsvs, Hev, wbytesWordOfBytes 8 Vs HlenVs]; rfl
  obtain ⟨s1, ib1, HrunSd, Hpc1, HFsd⟩ :=
    afCsdspFrame σ0 W pc0 hSd wSd rs2 immSd ea vsSd i0Sd DSd D0Sd dstSd cpu row k ib0
      Lpc Lpriv Lmprv Lpmm Lpmp Lpma Lhtif Lhart LmisaS LmisaC LmIE Lelp
      Hal2Sd Hal4Sd HramSd HtextSd HsubSd HisRVCSd HagreeSd HDmiSd HgoodSd HdecSd Hgood0Sd HexpSd
      HeaSd HvsSd Hal8 Hram8 HshapeSd HdatSd true HsfSd
  -- (1b) the boundary: `.pure ()` at k + 1 → `riscvStep` at k + 1
  have Hbnd1 := afRetToNextFetch s1.regs ib1 (efInit σ0.wmDev) cpu (k + 1) row true
  have hF1 : ∀ r : Register, (r ≠ .PC ∧ r ≠ .nextPC ∧ r ≠ .minstret_increment ∧ r ≠ .minstret ∧
      r ≠ .mcycle ∧ r ≠ .mtime ∧ r ≠ .mip) → s1.regs r = σ0.wmRegs r :=
    fun r h => HFsd r h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2.1 h.2.2.2.2.2.2
  -- decode-bridge transport for c.ldsp, at `s1.regs`
  have HagreeLd1 : ∀ r, DLd r = true → s1.regs r = dstLd.regs r :=
    fun r hr => (hF1 r (HDLdSafe r hr)).trans (HagreeLd r hr)
  -- `sp` survives the spill (STORE writes no GPR), and the config tower
  have HeaLd1 : s1.regs .x2 + sign_extend (m := 64) immSd = ea := by
    rw [hF1 .x2 (by decide)]; exact HeaSd
  have Lpriv1 : s1.regs .cur_privilege = .Machine := by
    rw [hF1 .cur_privilege (by decide)]; exact Lpriv
  have Lmprv1 : (_get_Mstatus_MPRV (s1.regs .mstatus) == 1#1) = false := by
    rw [hF1 .mstatus (by decide)]; exact Lmprv
  have Lpmm1 : pmm_mode_backwards (_get_Seccfg_PMM (s1.regs .mseccfg)) = .PMM_Disabled := by
    rw [hF1 .mseccfg (by decide)]; exact Lpmm
  have Lpmp1 : pmpAllOff (s1.regs .pmpcfg_n) := by
    rw [hF1 .pmpcfg_n (by decide)]; exact Lpmp
  have Lpma1 : s1.regs .pma_regions = bootPMA := by
    rw [hF1 .pma_regions (by decide)]; exact Lpma
  have Lhtif1 : s1.regs .htif_tohost_base = none := by
    rw [hF1 .htif_tohost_base (by decide)]; exact Lhtif
  have Lhart1 : s1.regs .hart_state = .HART_ACTIVE () := by
    rw [hF1 .hart_state (by decide)]; exact Lhart
  have LmisaS1 : (_get_Misa_S (s1.regs .misa) == 1#1) = true := by
    rw [hF1 .misa (by decide)]; exact LmisaS
  have LmisaC1 : (_get_Misa_C (s1.regs .misa) == 1#1) = true := by
    rw [hF1 .misa (by decide)]; exact LmisaC
  have LmIE1 : (_get_Mstatus_MIE (s1.regs .mstatus) == 1#1) = false := by
    rw [hF1 .mstatus (by decide)]; exact LmIE
  have Lelp1 : (s1.regs .elp == landing_pad_bits_backwards .LP_EXPECTED) = false := by
    rw [hF1 .elp (by decide)]; exact Lelp
  -- (1c)+(2) the reload, at `s1.regs`, answered at the ROW's own value
  obtain ⟨s3, ib3, va, req2, KK2, s4, ib4, -, -, HrunLd, HarwLd, Hrtc2Ld, HrdReg, HpcReg, HFrLd,
      HFgLd⟩ :=
    afCldspContRdAll { σ0 with wmRegs := s1.regs } W (BitVec.addInt pc0 2) hLd wLd ra immSd ea i0Ld DLd
      D0Ld dstLd cpu row (k + 1) ibNone
      Hpc1 Lpriv1 Lmprv1 Lpmm1 Lpmp1 Lpma1 Lhtif1 Lhart1 LmisaS1 LmisaC1 LmIE1 Lelp1
      Hal2Ld Hal4Ld HramLd HtextLd HsubLd HisRVCLd HagreeLd1 HDmiLd HgoodLd HdecLd Hgood0Ld HexpLd
      Hra HeaLd1 Hal8 Hram8 HdisjLd HshapeLd (epiWriteVal row k) Hlen true
  -- (3) c.jr's config tower, transported across BOTH boundaries
  have hJ : ∀ r : Register, r ∉ uxaGprs → (r ≠ .PC ∧ r ≠ .nextPC ∧ r ≠ .minstret_increment ∧
      r ≠ .minstret ∧ r ≠ .mcycle ∧ r ≠ .mtime ∧ r ≠ .mip) → s4.regs r = σ0.wmRegs r :=
    fun r hg h => (HFrLd r hg h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2.1
      h.2.2.2.2.2.2).trans (hF1 r h)
  have hGj : ∀ j : BitVec 5, j ≠ ra → uxaXget s4.regs j = uxaXget σ0.wmRegs j := by
    intro j hj
    have e := HFgLd j hj
    unfold ExecSt.gpr at e
    rw [e]
    exact uxaXget_congr _ _ (fun r hr => hF1 r (AxEpiChain.gprNe7 r hr)) j
  have HPCJr : s4.regs .PC = BitVec.addInt pc0 4 := HpcReg.trans (AxEpiChain.addInt22 pc0)
  have Hbridge : (⟨s4.regs, wmemRestrict σ0 W, σ0.wmDev⟩ : ExecSt).gpr ra =
      wordOfBytes 8 (epiWriteVal row k) := by
    unfold ExecSt.gpr at HrdReg ⊢; exact HrdReg
  have HagreeJr1 : ∀ r, DJr r = true → s4.regs r = dstJr.regs r := by
    intro r hr
    obtain ⟨hra, hs⟩ := HDJrSafe r hr
    refine Eq.trans ?_ (HagreeJr r hr)
    by_cases hg : r ∈ uxaGprs
    · exact AxEpiChain.gprAgree r hg ra hra _ _ hGj
    · exact hJ r hg hs
  have LprivM : s4.regs .cur_privilege = .Machine := by
    rw [hJ .cur_privilege (by decide) (by decide)]; exact Lpriv
  have LsecM : s4.regs .mseccfg = 0#64 := by
    rw [hJ .mseccfg (by decide) (by decide)]; exact Lsec
  have LmisaCM : (_get_Misa_C (s4.regs .misa) == 1#1) = true := by
    rw [hJ .misa (by decide) (by decide)]; exact LmisaC
  have LpmpM : pmpAllOff (s4.regs .pmpcfg_n) := by
    rw [hJ .pmpcfg_n (by decide) (by decide)]; exact Lpmp
  have LpmaM : s4.regs .pma_regions = bootPMA := by
    rw [hJ .pma_regions (by decide) (by decide)]; exact Lpma
  have LhtifM : s4.regs .htif_tohost_base = none := by
    rw [hJ .htif_tohost_base (by decide) (by decide)]; exact Lhtif
  have LhartM : s4.regs .hart_state = .HART_ACTIVE () := by
    rw [hJ .hart_state (by decide) (by decide)]; exact Lhart
  have LmisaSM : (_get_Misa_S (s4.regs .misa) == 1#1) = true := by
    rw [hJ .misa (by decide) (by decide)]; exact LmisaS
  have LmIEM : (_get_Mstatus_MIE (s4.regs .mstatus) == 1#1) = false := by
    rw [hJ .mstatus (by decide) (by decide)]; exact LmIE
  have LelpM : (s4.regs .elp == landing_pad_bits_backwards .LP_EXPECTED) = false := by
    rw [hJ .elp (by decide) (by decide)]; exact Lelp
  -- (1d) the second boundary, then c.jr's own run (fetch-only: position kept)
  have Hbnd2 := afRetToNextFetch s4.regs ib4 (efInit σ0.wmDev) cpu (k + 2) row true
  obtain ⟨s5, ib5, HrunJr⟩ :=
    afCjrRowRun { σ0 with wmRegs := s4.regs } W (BitVec.addInt pc0 4) hJr wJr ra i0Jr DJr D0Jr
      dstJr cpu row (k + 2) ibNone
      HPCJr LprivM LsecM LmisaCM LpmpM LpmaM LhtifM LhartM LmisaSM LmIEM LelpM
      Hal2Jr Hal4Jr HramJr HtextJr HsubJr HisRVCJr HagreeJr1 HDmiJr HgoodJr HdecJr Hgood0Jr HexpJr
      Hra true
  -- (2) `graphValue` and the PC target, from AxEpiShape's spill/reload capstone
  have Hmid : epiMidRegOnly row k (k + 1) := by
    intro p lb h1 h2 _
    omega
  iintro Hcov Htoks
  ihave %H := epilogueRetTargetSpillReloadOfRow (GF := GF) γ GD Hcons i row k (k + 1) (paZ ea)
    Hprog HshapeSd HshapeLd (by omega) Hmid ⟨.PHart cpu (riscvStep true) σ0.wmRegs none ib0, k⟩
    HsBefore HlensBefore HwrBefore HchBefore HownBefore HlinkBefore ra Hra
    ⟨s4.regs, wmemRestrict σ0 W, σ0.wmDev⟩ LprivM LsecM LmisaCM Hbridge $$ Hcov Htoks
  obtain ⟨Hval, Hexec, Hpcj⟩ := H
  ipureintro
  -- assemble the SEGMENTED connected run
  exact ⟨s4.regs, s5.regs, ib4, ib5,
    ⟨.PHart cpu (.impure (.ok (.memRead 8 va req2)) KK2) s3.regs none ib3, k + 1⟩,
    .IRead (classify req2.access_kind).akSync (paZ req2.pa) 8,
    fun vs' => ⟨.PHart cpu (KK2 (.Ok (wordOfBytes 8 vs', none))) s3.regs none ib3, k + 1 + 1⟩,
    rtc_transitive HrunSd (rtc_l ⟨LInstr, Hbnd1⟩ HrunLd), HarwLd, Hrtc2Ld,
    rtc_l ⟨LInstr, Hbnd2⟩ HrunJr, Hval, Hexec, Hpcj⟩

end epiChain

end Weak
