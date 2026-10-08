# Q22 — `textAt4S` demands a 4-aligned pc; this kernel's 4-byte words sit at pc ≡ 2 (mod 4)

Advisory note (design only; no proofs run). 2026-10-08.

## A. The finding, verified

### A.1 What the Sail `fetch` does at pc ≡ 2 mod 4

`model/Lean_RV64D/LeanRV64D/Fetch.lean:233-275` (`fetch`):

1. :239-247 misaligned-pc guard: bit 0 set → `E_Fetch_Addr_Align`; bit 1 set → error only
   if `¬ currentlyEnabled Ext_Zca` (so the 2-mod-4 path EVALUATES the misa.C probe; our
   regime has `misa = misaC`, probe = true — `execACurrentlyEnabledZca`, AxSpineOk3:285).
2. :250-252 the 4-byte fast path `fetch_bytes PC PC 4` is taken ONLY when
   `is_aligned_vaddr PC 4 && currentlyEnabled Ext_Ziccif`. At pc ≡ 2 mod 4 the condition is
   false regardless of Ziccif.
3. :262-275 the slow path: `fetch_bytes PC PC 2` → `ilo`; if `isRVC ilo` then `F_RVC ilo`,
   else `fetch_bytes PC (PC + 2) 2` → `ihi`, result `F_Base (ihi ++ ilo)`.
4. `fetch_bytes fs gs n` (:213-231) runs `translateAddr (Virtaddr gs)` on the GRANULE start
   and then `mem_read … n` — so a 32-bit word at pc ≡ 2 mod 4 costs TWO translations
   (pc, pc+2) and TWO 2-byte reads. The second translation runs from the state the first left
   (a TLB fill on the first makes the second a hit; same page unless pc's page offset is 0xffe).

So a 4-byte instruction at pc ≡ 2 mod 4 is NOT fetched via the arm `textAt4S` → `SpineFetch4TS`
models (AxDataX6.lean:80-96 requires `is_aligned_vaddr (.Virtaddr pc) 4 = true`, :49-78
`execAFetchBase4SGen` is the Ziccif fast path). The premise is simply unsatisfiable there.

### A.2 What the tree already provides for the 2-mod-4 arms

| level | RVC at 2 | Base at 2 (two halfwords) |
|---|---|---|
| `exec` (SmodeCore) | `ExecSC5.execFetchRVC2SGen` :317 | `ExecSC5.execFetchFBase2SGen` :329 (two `translateAddr`, s→s1→s2, `FetchS 2` bundles for `pal`/`pah`) — Rocq `SmodeCore.exec_fetch_F_Base_2_S_gen` |
| `execEff` (M-mode flat) | `WeakFetch2.execEffFetch2Rvc` :227, `execEffFetchRVC2` :255 | `WeakFetch2.execEffFetch2Base` :241, `execEffFetchFBase2` :276 (trace = two `wakIfetch` reads) |
| `execA` (image regime) | `execAFetchRVC2SGen` AxSpineOk3:334 | **MISSING** |
| `cntA` (Stage C count) | `cntFetchRVC2SGen` AxSymCtl4:997 | **MISSING** |
| text predicate | `textAtS` AxSpineOk6:110-129 — already has `if is_aligned_vaddr pc 4 then … 4-byte window … else bit1 ∧ inRam pa 2 ∧ aligned 2 ∧ BytesAt pa 2 h` | `textAt4S` AxDataX6:80 — aligned only |
| spine lemma | `sptFetchS` AxSpineOk6:181-260 and `fetchHitS` AxSpinE:144 case-split on `is_aligned_vaddr pc 4` | `SpineFetch4TS` AxDataX6:99, `fetch4HitS` AxSpinE:210 — aligned only |

Helpers in place: `AxSpineOk3.execAFetchBytesOk fs gs pa n` (generic in the granule `gs`),
`execAMemReadFetch2S` (:218), `cntMemReadFetch2S`, `AxSymCtl4.cntFetchBytesOk … = ntr + c`,
`execATranslateAddrImg` (AxSpineOk4:399: result `σ' = σ ∨ σ' = σ.setReg .tlb (fill)`),
`cntTranslateAddrImg` (AxSymCtl4:810: `if tlbHitv … then σ/0 else fill/3`), `ctrlOkSTlbFill`
(AxSpineOk6:173), `ExecSt.setReg_setReg_same` (ExecSC7:108), byte-split `nthByteLo/Hi`
(WeakFunnel:204/212), `WeakLeafWin.inRamByte`. Rocq never had an `execA`/`SpineFetch4T` 2-arm
(its kernel's 4-byte words at the certified sites were 4-aligned); the fix is Lean-only.

### A.3 The kernel image (script over `Xv6/KernelImage.lean`, symbols = first `KernelSyms` def)

8814 instructions, 3340 4-byte, **1611 at pc ≡ 2 mod 4** (176 functions), exactly ONE crossing
a page boundary (offset 0xffe): `log_write+0x34` = 0x80003ffe — not in any ported line.

Per certified function (offsets of 4-byte words; `@2` = 2 mod 4, `@0` = aligned):

| function | base | 4-byte @2 (VACUOUS sites) | 4-byte @0 (fine) |
|---|---|---|---|
| mycpu | 0x8000195c | +0x0e, +0x12 (`W0e`, `W12`) | — |
| push_off | 0x80000c1e | +0x10, +0x18, +0x2c, +0x30 (`Wq10 Wq18 Wq2c Wq30`) | +0x0a (`Wq0a`) |
| acquire | 0x80000c58 | +0x12 (`Wa12`, jal holding) | +0x0c, +0x1c, +0x24, +0x34, +0x38, +0x3c |
| pop_off | 0x80000c98 | **+0x16 (`Wp16`)** — the finding's "pop_off unaffected" is WRONG | +0x08, +0x0c (`Wp08 Wp0c`), +0x24… |
| release | 0x80000ce0 | +0x12, +0x16, +0x1a, +0x1e | +0x0c, +0x2c… (no `textAt4S` use in the release line — unaffected) |
| holding | 0x80000bf2 | — | +0x16, +0x1a, +0x1e (`W16 W1a W1e`) — `holdingText` SATISFIABLE |
| cpuid | 0x80001948 | — (all compressed) | — |
| initlock | 0x80000bd8 | +0x0a, +0x0e | — |
| allocproc | 0x80001b72 | 29 incl. +0x38..+0x4c, +0x5c, +0x64..+0x70, +0x8c..+0x94 (allocpid copy) | +0x52, +0x56, +0x76..+0x86 |
| myproc | 0x8000197c | +0x0a, +0x22 | +0x14, +0x18 |
| sched / scheduler / swtch / usertrap | | 7 / 14 / 24 (ALL of swtch) / 19 | |

### A.4 Merged files carrying an unsatisfiable text hypothesis (31)

Direct consumers of a `…Text` predicate containing a 2-mod-4 `textAt4S` conjunct
(`grep -l`); every theorem in them with that hypothesis is vacuous:

- `mycpuText` (AxSpinE7:118; W0e/W12): AxSpinE7, E7b, E7e, E7f, E7g, AxSpinE8, **AxSpinE8f**
  (proves `mycpuTextFalse`), AxSpinHd, Hd9, HdA, HdB, HdC, AxSpinPO1, PO2, PO3, PO4, PO5, PO6,
  AxSpinAp.
- `pushOffText` (AxSpinPO:143; Wq10/Wq18/Wq2c/Wq30): AxSpinPO, POt1–POt6 (+ PO1–PO4 above).
- `popOffText` (AxSpinPO:170; Wp16): AxSpinPO, POt1–POt6, PO5, PO6 (all already listed).
- `acquireText` (AxSpinAq:152; Wa12): AxSpinAq, Aqt1, Aqt2, Aqr.
- `allocpidText` (AxSpinAp:269; 20 of its 27 `textAt4S` conjuncts): AxSpinAp, AxSpinAp6.

NOT vacuous: `holdingText` (AxSpinHd, Hd2, Hd2b, Hd2c, Hd3, Hd4, Hd5, Hd8 — 12 files) unless
they also take `mycpuText`; the generic-pc `tw4*`/`tokB`/`tokAmo` lemmas (AxSpinPOd, POd2, Aqd,
AxSpinAm:498 — only their kernel instantiations are); the leaf/cond/ctl files (AxLeafS,
AxLeafS2–4, AxCondM2/M3, AxSpinCtl2, AxSpinRow2, AxSfence2) which take `textAt4S` as an opaque
parameter or construct it at the synthetic 4-aligned `sPc = 0x80000000` (`AxLeafS3.text4Of`).

KEY STRUCTURAL FACT: outside AxDataX6, AxSpinE, AxLeafS3 (constructor) and AxSpinE8f
(refutation), no file destructures `textAt4S` — all 31 vacuous files pass it opaquely to
`tokB`/`textOkB`. Generalising the definition in place therefore repairs them with NO
restatement.

## B. The fix: generalise `textAt4S` in place, mirroring `textAtS` (candidate 1)

Keep the name, arity and the 14-conjunct spine (so the three destructuring sites keep their
patterns); replace the two alignment conjuncts:

```lean
/-- Rocq `text_at4_S pc w32`, both alignments (Lean deviation Q22: the 2-mod-4 arm is the
model's two-halfword path; pc may not straddle a page). -/
def textAt4S (σi : ExecSt) (T : PTree) (pc : BitVec 64) (w32 : BitVec 32) : Prop :=
  ∃ (p2 p1 w pa : BitVec 64),
    AxPtProt.ptreeMaps T (WeakKpt.svpnOf pc) p2 p1 w ∧
    WeakWalkEff.ptSlotMem σi (AxPtProt.ptAddr2 T (WeakKpt.svpnOf pc)) p2 ∧
    WeakWalkEff.ptSlotMem σi (AxPtProt.ptAddr1 p2 (WeakKpt.svpnOf pc)) p1 ∧
    WeakWalkEff.ptSlotMem σi (AxPtProt.ptAddr0 p1 (WeakKpt.svpnOf pc)) w ∧
    (∀ mxr dosum : Bool, pteCheckOk (.InstructionFetch ()) .Supervisor mxr dosum w) ∧
    update_PTE_Bits w (.InstructionFetch ()) = none ∧ ptePbmt0 w ∧
    (pc != sign_extend (m := 64) (Sail.BitVec.extractLsb pc 38 0)) = false ∧
    zero_extend (m := 64) (ppn0 w +++ Sail.BitVec.extractLsb pc (Functions.pagesize_bits - 1) 0) = pa ∧
    (Sail.BitVec.access pc 0 != 0#1) = false ∧                    -- was: is_aligned_vaddr pc 4 = true
    isRVC (Sail.BitVec.extractLsb w32 15 0) = false ∧
    inRam pa 4 ∧
    (if is_aligned_vaddr (.Virtaddr pc) 4 then is_aligned_paddr (.Physaddr pa) 4 = true
     else (Sail.BitVec.access pc 1 != 0#1) = true ∧ is_aligned_paddr (.Physaddr pa) 2 = true ∧
          (Sail.BitVec.extractLsb pc 11 1 != 0x7ff#11) = true) ∧ -- was: is_aligned_paddr pa 4
    BytesAt σi pa 4 w32
```

Why this shape: it is exactly `textAtS`'s precedent (AxSpineOk6:122-129), so `SpineFetch4TS`
and `fetch4HitS` get the same `cases hal4 : is_aligned_vaddr …` skeleton as `sptFetchS` /
`fetchHitS`; `inRam pa 4 ∧ BytesAt σi pa 4 w32` stay unconditional so the word's bytes are one
fact in both arms (the halves are derived by `nthByteLo/Hi`). The no-page-straddle conjunct
(`pc[11:1] ≠ 0x7ff`) is what lets ONE `ptreeMaps` serve both halfword translations; it is
decided at every literal pc and false for a single kernel word (`log_write+0x34`).

Pivotal new/changed statements (all in `Weak/AxDataX6.lean` unless noted):

```lean
-- bit-vector facts for the high half (bv_decide after unfolding extractLsb/addInt/svpnOf)
theorem AxDataX6.svpnOfAdd2 (pc) : (extractLsb pc 11 1 != 0x7ff#11) = true →
  WeakKpt.svpnOf (BitVec.addInt pc 2) = WeakKpt.svpnOf pc
theorem AxDataX6.canonAdd2 (pc) : (pc != sign_extend (extractLsb pc 38 0)) = false →
  (extractLsb pc 11 1 != 0x7ff#11) = true →
  (BitVec.addInt pc 2 != sign_extend (extractLsb (BitVec.addInt pc 2) 38 0)) = false
theorem AxDataX6.paAdd2 (q : BitVec 44) (pc) : (extractLsb pc 11 1 != 0x7ff#11) = true →
  zero_extend 64 (q +++ extractLsb (BitVec.addInt pc 2) 11 0) =
    zero_extend 64 (q +++ extractLsb pc 11 0) + 2#64
theorem AxDataX6.alignedPaddr2Add2 (pa) : is_aligned_paddr (.Physaddr pa) 2 = true →
  is_aligned_paddr (.Physaddr (pa + 2#64)) 2 = true
theorem AxDataX6.inRamHi (pa) : inRam pa 4 → inRam pa 2 ∧ inRam (pa + 2#64) 2   -- omega
theorem AxDataX6.bytesAtLo (s pa w) : BytesAt s pa 4 w → BytesAt s pa 2 (extractLsb w 15 0)
theorem AxDataX6.bytesAtHi (s pa w) : BytesAt s pa 4 w → BytesAt s (pa + 2#64) 2 (extractLsb w 31 16)

/-- The `execA` twin of `ExecSC5.execFetchFBase2SGen`: two translations s→s1→s2, two
2-byte fetch reads (premise bundle = `execAFetchRVC2SGen`'s, twice, at `pa`/`pa+2`). -/
theorem execAFetchBase2SGen (va pal pah : BitVec 64) (w : BitVec 32) (s s1 s2 : ExecSt)
    (regl regh : PMA_Region) (hpc : s.regs .PC = va) (hpc1 : s1.regs .PC = va)
    (hmisaC : (_get_Misa_C (s.regs .misa) == 1#1) = true)
    (hbit0 : (access va 0 != 0#1) = false) (hbit1 : (access va 1 != 0#1) = true)
    (hvalign : is_aligned_vaddr (.Virtaddr va) 4 = false)
    (htr1 : execA (translateAddr (.Virtaddr va) (.InstructionFetch ())) s
        = some (.Ok (.Physaddr pal, .PBMT_PMA, ()), s1))
    (htr2 : execA (translateAddr (.Virtaddr (BitVec.addInt va 2)) (.InstructionFetch ())) s1
        = some (.Ok (.Physaddr pah, .PBMT_PMA, ()), s2))
    (…the 13 `execAMemReadFetch2S` premises at `s1`/`pal` for `extractLsb w 15 0`…)
    (…the same 13 at `s2`/`pah` for `extractLsb w 31 16`…)
    (hnot : isRVC (extractLsb w 15 0) = false) :
    execA (fetch ()) s = some (.F_Base w, s2)
-- proof: two `AxSpineOk3.execAFetchBytesOk`, `execACurrentlyEnabledZca`, the
-- `execAFetchRVC2SGen` simp set + `hpc1 htr2`, then `congr; bv_decide` as ExecSC5:339-343.

-- AxSpinE.lean (Stage C count), beside cntFetchBase4SGen:
theorem cntFetchBase2SGen … (ntr1 ntr2 : Nat) (htrc1 : cntA (translateAddr va …) s = ntr1)
    (htrc2 : cntA (translateAddr (va+2) …) s1 = ntr2) … : cntA (fetch ()) s = ntr1 + ntr2
```

`SpineFetch4TS` keeps its statement byte-for-byte; its proof becomes `sptFetchS`'s skeleton:
aligned arm unchanged; 2-arm = first `execATranslateAddrImg` at `pc` → `σ'`, `hc'` by
`ctrlOkSTlbFill`, second `execATranslateAddrImg` at `pc+2` from `σ'` (slots via `hmem'`,
`tlbExact` from `hc'`, `svpnOfAdd2`/`canonAdd2`/`paAdd2` rewrite the vpn/pa) → `σ''`, `hc''`,
`tlbFrame t σ''` by cases (`setReg_setReg_same` for fill∘fill), `hpc1` by `RegFile.set_other`,
then `execAFetchBase2SGen`. `fetch4HitS` likewise, with `cntTranslateAddrImg` twice: `hitW`
plus `svpnOfAdd2` makes both hits, so `σ' = σ`, counts `0 + 0` (post `b = b'` unchanged).

Rejected: (2) a sibling `textAt4S2` + arm would thread a FOURTH text parameter through
`SpineFetch4T`, `textOkCtl`, `XCertT/XJal/XBtype/XCjr/XFence` (AxSymCtl2 + 8 consumer files),
duplicate `tokB`/`tw4*`/`insAt`, and force per-pc arm choices in all five `…Text` predicates
(31 files restated). (3) dropping alignment from `textAt4S` with no `if` would lose the
`is_aligned_paddr pa 4` the fast path needs. (1) touches 4 files and restates nothing.

## C. Rework list (dependency order; S/M/L)

One lane (W1); W2 can start once W1's step 1 compiles (it only needs the new statement).

| # | file | change | size |
|---|---|---|---|
| 1 | `Weak/AxDataX6.lean` | new `textAt4S` (B); the 7 bv/byte helpers; `execAFetchBase2SGen`; re-prove `SpineFetch4TS` (two-translation 2-arm); header deviation "Q22". | **L** |
| 2 | `Weak/AxLeafS3.lean` :242-260 `text4Of` | `sPc = 0x80000000` is 4-aligned: `hal4` conjunct → `by decide`, `if` arm → `rw [if_pos (by decide)]; decide +kernel`. AxSfence2 `text4Sfence` unchanged (goes through `text4Of`). | S |
| 3 | `Weak/AxSpinE.lean` :84 `cntFetchBase4SGen` keep; add `cntFetchBase2SGen`; re-prove `fetch4HitS` :210 with the alignment case split (template `fetchHitS` :144-196). | M |
| 4 | `Weak/AxSpinE8f.lean` | DELETE `mycpuTextFalse` :287 (+ header :29, :285); add `AxSpinE8f.textAt4T2` (the 2-arm twin of `textAtT2` :240, on `σ8`/`tT`/`L1leaf`) and `AxSpinE8f.mycpuTextOf : mycpuText AxSpinE8f.σ8 AxSpinE8f.tT` (12 × `textAtT4/T2` + 2 × `textAt4T2`, bytes by `decide +kernel`); restore `Htxt8` into `wpdMycpuPremises` :749 and state the capstone instance `AxSpinE8.wpdMycpu` APPLIED (the non-vacuity cert proper). | M |
| 5 | protocol notes | AxDataX6, AxSpinE, AxSpinE8f, AxSpinAqr (:33 comment) entries; drop "Q22 open". | S |
| 6 (W2) | `Weak/AxSpinPOd.lean`-style cert: `pushOffText`/`popOffText` instance on the E8f image (`σ8` holds the kernel text; push_off/pop_off/acquire pages need `tT` to map them — if `tT` maps only mycpu's page (`vpnT`), use one `textAt4T2`-style constructor per page or a 2-page `tT'`) | acceptance for `Wq10/Wq30/Wp16`: `pushOffText σ8 tT' ∧ popOffText σ8 tT'` | M |
| 7 (W2) | `AxSpinAq`/`AxSpinAp6` acceptance: `acquireText σ8 tT'` (Wa12) and `allocpidText σ8 tT'` (27 conjuncts, 20 at 2 mod 4; `decide +kernel` per word) | M |
| 8 | lint: `#print axioms` on `SpineFetch4TS`, `fetch4HitS`, `mycpuTextOf`; grep that no file still mentions `mycpuTextFalse` | S |

Nothing else recompiles with a changed statement: the 31 vacuous files, `tokB`, `textOkB`,
`textOkCtl`, the `X*` leaves and `SpineOkTSW` all take `textAt4S` opaquely.

Acceptance (the E8f-style non-vacuity certs): (a) `mycpuTextOf` type-checks (replaces the
refutation), (b) `wpdMycpu` instantiated on `σ8` with every premise discharged, (c) one
`pushOffText`/`popOffText` instance and one `acquireText` instance (covers `Wq30`, `Wp16`,
`Wa12`), (d) `allocpidText` instance. Each is `decide +kernel` over image bytes plus the page
map, exactly `AxLeafS3.text4Of` / `AxSpinE8f.textAtT2` patterns.

## D. Risks and the owner question

Risks
1. `bv_decide` on `paAdd2`/`svpnOfAdd2`/`canonAdd2`: 64-bit with `+++`/`zero_extend`/
   `setWidth`; literalise `Functions.pagesize_bits` (= 12) first (protocol lesson AxSpinPO1).
   Fallback: `BitVec.toNat` + `omega` on the three.
2. The second `execATranslateAddrImg` needs `exec (translationMode …) σ'` etc. at the filled
   state — the helpers (`execTranslationModeSSv39`, `execEffectivePrivilegeFetch`,
   `execIsShadowStackFetch`) take the regime from `ctrlOkS σ'.regs`, which `hc'` gives; the
   `tlbExact` of the filled vector comes from `hc'` too (`ctrlOkSTlbFill`). Low risk.
3. `fetch4HitS` 2-arm: `cntTranslateAddrImg`'s `if tlbHitv tlbvec vpn` must be rewritten with
   `svpnOfAdd2` BEFORE `simp only [↓reduceIte]`; otherwise the second count is stuck.
4. `tlbFrame` with fill∘fill: `ExecSt.setReg_setReg_same` collapses to one `setReg .tlb`; the
   `∃ v` witness is the inner fill vector. S.
5. Acceptance certs for push_off/acquire/allocproc need a page table mapping THEIR pages; if
   `AxSpinE8f.tT` maps only `vpnT` (mycpu's page 0x80001000), either all four functions share
   pages 0x80000000/0x80001000 (push_off, acquire, pop_off ARE in 0x80000000's page; mycpu,
   allocproc in 0x80001000's) — check `tT` covers both, else extend it (S).
6. The `pop_off` correction (Wp16 at 2 mod 4) means the earlier "release/holding/pop_off/cpuid
   unaffected" line in weak-port-protocol must be fixed to "holding/cpuid only".

Owner question (one, non-blocking — park nothing): the 2-arm carries a NEW conjunct "pc does
not straddle a page" (`pc[11:1] ≠ 0x7ff`), decided at literals. Alternative: carry a second
`ptreeMaps` for `svpnOf (pc+2)` and handle the straddle too (general but +4 conjuncts and a
second walk in every proof). RECOMMENDED: the no-straddle conjunct — one kernel word straddles
(`log_write+0x34`, outside every ported line), and it is a one-line `decide` at each use.

Verdict: finding CONFIRMED and WIDENED (pop_off `Wp16` also vacuous; 31 files carry an
unsatisfiable text hypothesis). Fix: candidate (1), 4 files change (AxDataX6 L, AxSpinE M,
AxSpinE8f M, AxLeafS3 S) + acceptance certs; no downstream restatement.
