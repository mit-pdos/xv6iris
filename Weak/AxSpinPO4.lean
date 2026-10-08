/-
Weak: **PHASE 5, stage 5: THE CERTIFICATE `wpdPushOff`** — xv6's REAL `push_off` (the 23
instructions at `push_off` = 0x80000c1e, both arms of `if(c->noff == 0)`, THREE calls of the real
mycpu composed with `AxSpinE8.wpdMycpu`) as a POSITIONAL, CALLER-INDEXED CPS WPd at the joint
instance Ixv6, interrupts off (`ctrlOkSW`: S-mode, SIE = 0), WARM TLB.  Composes
`AxSpinPO1.wpdPoHead`, `AxSpinPO2.wpdPoInt` (arm `b = true`) and `AxSpinPO3.wpdPoTail`.

Rocq: `iris/AxSpinPO4.v` @ xxvzwolszwmp.

## The Rocq header, in substance (as restated under Stage C)

`poSh b` = `poHead ++ ((if b then poInt else []) ++ poTail)` (AxSpinPOr): 17 items (`b = false`)
or 22 (`b = true`), the arm `b` ("noff == 0").  For every `k`, `b` and every row with
`RowSh k row (poSh b …)`:
  WPd (boundary at k, regs rs0) {{Ψ}}
  ⇐ (∀ vn0 vn vra' vs0' vs1' rs' ib',
       ⌜regime ∧ PC = ret ∧ TLB kept ∧ a0 = mycpuRet tp ∧ sp = sp0 ∧ a5 = addiw1 (second noff
        load) ∧ ra / s0 / s1 = the RELOADED words ∧ every other GPR kept ∧ the spills' row data
        = ra0 / s00 / s10's bytes ∧ the first noff load's graph value = vn0 with (vn0 == 0) = b
        ∧ (b → the intena store's row data = stBytes 4 0) ∧ the second noff load = vn ∧ the noff
        store's row data = stBytes 4 (addiw1 vn) ∧ the reloads' graph values⌝
       -∗ the three reload annotations (reload bytes = spill bytes)
       -∗ WPd (boundary at tk + 9, regs rs') {{Ψ}})
with `tk = k + 8 + (if b then 5 else 0)` (the tail's start).  mycpu's own reload annotations are
dropped (affine); push_off's three are handed on.

GRAPH-VALUE PINNING (Q20', provisional Option V, `notes/weak-port-q20-offrow.md`; Rocq:
"TEMPORARY ASSUMPTION — ROW PINNING", owner decision 2026-10-03).  The row fixes which positions
are loads / stores and the data base addresses; the control targets are pinned by GRAPH VALUES:
mycpu's three returns (ra reloads at `k + 5`, `k + 10` (arm `b` only), `tk + 2`), the arm of the
`beqz` (the first noff load at `k + 7`) and push_off's own return (`tk + 6`, + `Hret`).  The
theorem proves nothing about a graph whose values differ; the follow-up ROW-INTEGRITY theorem is
to discharge the pins.  Ownership is load-bearing for data values.

Kernel words: this file states no instruction word (pure composition); the three return targets
`+ 0x14` / `+ 0x30` / `+ 0x1c` were cross-checked against `Xv6/KernelImage.lean` (`jal mycpu` at
0x80000c2e / 0x80000c4a / 0x80000c36, push_off = 0x80000c1e … `c.j` at 0x80000c56).

## Deviations from Rocq

1. O2 STAGE C / Q20' (provisional Option V; protocol "Cross-file facts" Q20', AxSpinPOr,
   AxSpinPO1 / PO2 / PO3 entries):
   * `po_sh b pra ps0 ps1 pmra pms0 pn pint p14 p2c p30 p18 p1c pret nret` (65 / 89 items) ↦
     `poSh b pra ps0 ps1 pmra pms0 pn pint` (17 / 22 items; no fetch items, so the fetch
     parameters `p14 p2c p30 p18 p1c pret nret` and the premise `nret = 2 ∨ nret = 4` are
     DROPPED).
   * POSITIONS (a fetch consumes no row item): spills `k / k+1 / k+2` (Rocq `k+2/4/6`), first
     noff load `k + 7` (Rocq `k + 30`), int window at `k + 8` (Rocq `k + 32`), intena store
     `k + 12` (Rocq `k + 54`), `tk = k + 8 (+ 5)` (Rocq `k + 32 (+ 24)`), second noff load /
     store `tk + 4 / 5` (Rocq `tk + 20 / 23`), reloads `tk + 6/7/8` (Rocq `tk + 25/27/29`),
     final continuation `tk + 9` (Rocq `tk + 32`).
   * the `fpin` premises (four or five) are DROPPED; NEW value pins surfaced as premises
     (the callees' pins, Q20' Option V): `graphValue GD0 (i, k + 5) = some (stBytes 8 (ppo
     0x14))` (PO1's mycpu return), `Hvb : ∀ vn, graphValue GD0 (i, k + 7) = some vn →
     (ldRes false 4 vn == zero_reg) = b` (PO1's arm selection; Rocq: the arm is chosen by the
     row), `b = true → graphValue GD0 (i, k + 10) = some (stBytes 8 (ppo 0x30))` (PO2's mycpu
     return, arm `b` only — Rocq's `if b then fpin … ∧ fpin …`), `graphValue GD0 (i, tk + 2) =
     some (stBytes 8 (ppo 0x1c))` and `graphValue GD0 (i, tk + 6) = some (stBytes 8 ret)` +
     `jalrTgt 0#12 ret = ret` (PO3's two returns).
   * NEW length premise `tk + 9 < row.length` (PO3's: the boundary after the c.ret needs a next
     row item; Rocq got it from the return-fetch item).  PO1's `k + 8 < row.length` and PO2's
     `u + 5 < row.length` are DISCHARGED from it.
   * the section context `stv` and the Sail premise `va_first_read` are DROPPED (as PO1–PO3).
2. TYPES / SPELLING (as AxSpinPO1 deviation 3): `uint P` ↦ `paZ P`; `gpr_val` ↦ `gprVal`;
   `register_lookup PC rs` ↦ `rs .PC`; `uint r ≠ n` ↦ `r.toNat ≠ n`; `eq_vec a b` ↦ `a == b`;
   `(i,k) ↦ₐ P` ↦ `AxAnnot.annotOwn (i, k) P`; the `let`s are inlined (`sp0` ↦
   `gprVal rs0 AxSpinE8.r2`, `spb` ↦ `spo …`, `tp` ↦ `gprVal rs0 AxSpinE8.r4`, `tk` ↦
   `k + 8 + (if b then 5 else 0)`); `mword_of_int 0 : mword 64` ↦ `0#64`; Rocq's right-nested
   `a ++ b ++ c` is written `a ++ (b ++ c)`.
3. INSTANCES / SECTION (as AxSpinPO1 deviation 4): `[InvGS_gen hlc GF]` (any `hlc`); the local
   instances `pw_pol`/`pw_G` are inlined as `xv6Pol GT` / `AxSpinX2.xG L GT nm`; section
   variables are explicit arguments in AxSpinE6's order (+ `Htxm Htxp`).
4. PROOF SHAPE: Rocq's `iAssert … with "[C]" as "TL"` (the tail, once for both arms) is a Lean
   `have` generic in the continuation proposition (`Cp`), instantiated at the goal's.
   `frame_cancel_32` is inlined (it lives in AxSpinHd9, not imported).  The trailing
   `Print Assumptions` is not ported.

**Rocq → Lean name map.**  `po_sh` `poSh`, `slot8_tlb` `slot8Tlb`, `fld4_tlb` `fld4Tlb`,
`wpd_push_off` `wpdPushOff`.  The local instances `pw_pol`, `pw_G` are inlined (deviation 3).
No Lean-only declarations.

**Dropped:** nothing (Rocq 4 definitions/lemmas + 2 local instances; Lean 4).
-/
import Weak.AxSpinPO2
import Weak.AxSpinPO3

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D LeanRV64D.Functions

/-- Rocq `po_sh` (deviation 1: no fetch items / parameters). -/
def poSh (b : Bool) (pra ps0 ps1 pmra pms0 pn pint : Int) : List Ritem :=
  poHead pra ps0 ps1 pmra pms0 pn ++
    ((if b then poInt pmra pms0 pint else []) ++ poTail pra ps0 ps1 pmra pms0 pn)

/-- Rocq `slot8_tlb`. -/
theorem slot8Tlb (σi : ExecSt) (T : PTree) (L : Xlay) (i : Agent) (rs rs' : RegFile)
    (va P : BitVec 64) :
    rs' .tlb = rs .tlb → AxSpinPO1.slot8 σi T L i rs va P → AxSpinPO1.slot8 σi T L i rs' va P := by
  rintro Ht ⟨H1, H2, H3, H4, H5⟩
  exact ⟨H1, H2, hitWAgree rs rs' va Ht H3, H4, H5⟩

/-- Rocq `fld4_tlb`. -/
theorem fld4Tlb (σi : ExecSt) (T : PTree) (L : Xlay) (i : Agent) (rs rs' : RegFile)
    (va P : BitVec 64) :
    rs' .tlb = rs .tlb → fld4 σi T L i rs va P → fld4 σi T L i rs' va P := by
  rintro Ht ⟨H1, H2, H3, H4, H5⟩
  exact ⟨H1, H2, hitWAgree rs rs' va Ht H3, H4, H5⟩

section pushoff
variable {hlc : HasLC} {GF : BundledGFunctors.{0,0,0}} [InvGS_gen hlc GF] [AxannotGS GF]
  [AxSpinX.Xv6G GF]
variable (L : Xlay) (GT : GdexecT) (nm : Xv6N)
variable (HL : xlayOk L) (Hcons : rvwmoCatConsistent (gtAdGd GT))
variable (σi : ExecSt) (T : PTree) (satp0 : BitVec 64)
variable (hmode : _get_Satp64_Mode (Mk_Satp64 satp0) = 8#4)
variable (hasid : zero_extend (m := 16) (satp_to_asid satp0) = 0#16)
variable (hppn : BitVec.setWidth 44 (satp_to_ppn satp0) = T.base)
variable (i : Agent) (cpu : CPU)
variable (Hfix : textFixed (gtAdGd GT) i (imgS σi))
variable (Htxm : mycpuText σi T) (Htxp : pushOffText σi T)
variable (Ψ : Athread → IProp GF)
variable (HΨmid : ∀ s, midState s → s.atK = (AxOpsem.grow (gtAdGd GT) i).length →
  ⊢ @postLifting GF (AxSpinX2.xG L GT nm) Ψ i s)

set_option maxHeartbeats 3200000 in
include HL Hcons hmode hasid hppn Hfix Htxm Htxp HΨmid in
/-- Rocq `wpd_push_off` (deviation 1: Stage C positions; the callees' value pins replace the
`fpin` premises; new length premise `tk + 9 < row.length`). -/
theorem wpdPushOff (k : Nat) (b : Bool) (rs0 : RegFile) (ib0 : Ibch) (ret : BitVec 64)
    (Pra Ps0 Ps1 Pmra Pms0 Pn Pi : BitVec 64) :
    -- the row
    RowSh k (AxOpsem.grow (gtAdGd GT) i)
      (poSh b (paZ Pra) (paZ Ps0) (paZ Ps1) (paZ Pmra) (paZ Pms0) (paZ Pn) (paZ Pi)) →
    k + 8 + (if b then 5 else 0) + 9 < (AxOpsem.grow (gtAdGd GT) i).length →
    rowW8 (AxOpsem.grow (gtAdGd GT) i) →
    noRmw8 (AxOpsem.grow (gtAdGd GT) i) (paZ Pra) → noRmw8 (AxOpsem.grow (gtAdGd GT) i) (paZ Ps0) →
    noRmw8 (AxOpsem.grow (gtAdGd GT) i) (paZ Ps1) →
    noRmw8 (AxOpsem.grow (gtAdGd GT) i) (paZ Pmra) →
    noRmw8 (AxOpsem.grow (gtAdGd GT) i) (paZ Pms0) →
    rowWle (AxOpsem.grow (gtAdGd GT) i) (paZ Pn) 4 → noRmwn (AxOpsem.grow (gtAdGd GT) i) (paZ Pn) 4 →
    rowWle (AxOpsem.grow (gtAdGd GT) i) (paZ Pi) 4 →
    -- the entry state
    ctrlOkSW T satp0 rs0 → rs0 .PC = AxSpinPO.ppo 0 → hitW rs0 (AxSpinPO.ppo 0) →
    hitW rs0 (pcm 0) →
    -- the slots and the cpu fields
    AxSpinPO1.slot8 σi T L i rs0
      (spo (gprVal rs0 AxSpinE8.r2) + sign_extend (m := 64) AxSpinPO3.imm24) Pra →
    AxSpinPO1.slot8 σi T L i rs0
      (spo (gprVal rs0 AxSpinE8.r2) + sign_extend (m := 64) AxSpinPO3.imm16) Ps0 →
    AxSpinPO1.slot8 σi T L i rs0
      (spo (gprVal rs0 AxSpinE8.r2) + sign_extend (m := 64) AxSpinPO3.imm8) Ps1 →
    AxSpinPO1.slot8 σi T L i rs0
      (AxSpinE8.sp1Of (spo (gprVal rs0 AxSpinE8.r2)) + sign_extend (m := 64) AxSpinE8.immRa) Pmra →
    AxSpinPO1.slot8 σi T L i rs0
      (AxSpinE8.sp1Of (spo (gprVal rs0 AxSpinE8.r2)) + sign_extend (m := 64) AxSpinE8.immS0) Pms0 →
    fld4 σi T L i rs0
      (AxSpinE8.mycpuRet (gprVal rs0 AxSpinE8.r4) + sign_extend (m := 64) i120) Pn →
    fld4 σi T L i rs0
      (AxSpinE8.mycpuRet (gprVal rs0 AxSpinE8.r4) + sign_extend (m := 64) i124) Pi →
    alldj [(paZ Pra, 8), (paZ Ps0, 8), (paZ Ps1, 8), (paZ Pmra, 8), (paZ Pms0, 8), (paZ Pn, 4),
      (paZ Pi, 4)] →
    -- the value pins (Q20': the callees' returns and the arm; deviation 1)
    graphValue (gtAdGd GT) (i, k + 5) = some (stBytes 8 (AxSpinPO.ppo 0x14)) →
    (∀ vn, graphValue (gtAdGd GT) (i, k + 7) = some vn → (ldRes false 4 vn == zero_reg) = b) →
    (b = true → graphValue (gtAdGd GT) (i, k + 10) = some (stBytes 8 (AxSpinPO.ppo 0x30))) →
    graphValue (gtAdGd GT) (i, k + 8 + (if b then 5 else 0) + 2) =
      some (stBytes 8 (AxSpinPO.ppo 0x1c)) →
    graphValue (gtAdGd GT) (i, k + 8 + (if b then 5 else 0) + 6) = some (stBytes 8 ret) →
    jalrTgt 0#12 ret = ret →
    ⊢ (∀ (vn0 vn vra' vs0' vs1' : List (BitVec 8)) (rs' : RegFile) (ib' : Ibch),
        ⌜ctrlOkSW T satp0 rs' ∧ rs' .PC = ret ∧ rs' .tlb = rs0 .tlb ∧
          gprVal rs' AxSpinE8.r10 = AxSpinE8.mycpuRet (gprVal rs0 AxSpinE8.r4) ∧
          gprVal rs' AxSpinE8.r2 = gprVal rs0 AxSpinE8.r2 ∧
          gprVal rs' AxSpinE8.r15 = AxSpinPO3.addiw1 (ldRes false 4 vn) ∧
          gprVal rs' AxSpinE8.r1 = ldRes false 8 vra' ∧ gprVal rs' AxSpinE8.r8 = ldRes false 8 vs0' ∧
          gprVal rs' AxSpinPOr.r9 = ldRes false 8 vs1' ∧
          (∀ r : BitVec 5, r.toNat ≠ 1 → r.toNat ≠ 2 → r.toNat ≠ 8 → r.toNat ≠ 9 →
            r.toNat ≠ 10 → r.toNat ≠ 15 → gprVal rs' r = gprVal rs0 r) ∧
          graphData (gtAdGd GT) (i, k) = some (stBytes 8 (gprVal rs0 AxSpinE8.r1)) ∧
          graphData (gtAdGd GT) (i, k + 1) = some (stBytes 8 (gprVal rs0 AxSpinE8.r8)) ∧
          graphData (gtAdGd GT) (i, k + 2) = some (stBytes 8 (gprVal rs0 AxSpinPOr.r9)) ∧
          graphValue (gtAdGd GT) (i, k + 7) = some vn0 ∧ (ldRes false 4 vn0 == zero_reg) = b ∧
          (b = true → graphData (gtAdGd GT) (i, k + 12) = some (stBytes 4 0#64)) ∧
          graphValue (gtAdGd GT) (i, k + 8 + (if b then 5 else 0) + 4) = some vn ∧
          graphData (gtAdGd GT) (i, k + 8 + (if b then 5 else 0) + 5) =
            some (stBytes 4 (AxSpinPO3.addiw1 (ldRes false 4 vn))) ∧
          graphValue (gtAdGd GT) (i, k + 8 + (if b then 5 else 0) + 6) = some vra' ∧
          graphValue (gtAdGd GT) (i, k + 8 + (if b then 5 else 0) + 7) = some vs0' ∧
          graphValue (gtAdGd GT) (i, k + 8 + (if b then 5 else 0) + 8) = some vs1'⌝ -∗
        AxAnnot.annotOwn (GF := GF) (i, k + 8 + (if b then 5 else 0) + 6)
          iprop(⌜RLfact GT i (paZ Pra) (k + 8 + (if b then 5 else 0) + 6)
            (stBytes 8 (gprVal rs0 AxSpinE8.r1))⌝) -∗
        AxAnnot.annotOwn (GF := GF) (i, k + 8 + (if b then 5 else 0) + 7)
          iprop(⌜RLfact GT i (paZ Ps0) (k + 8 + (if b then 5 else 0) + 7)
            (stBytes 8 (gprVal rs0 AxSpinE8.r8))⌝) -∗
        AxAnnot.annotOwn (GF := GF) (i, k + 8 + (if b then 5 else 0) + 8)
          iprop(⌜RLfact GT i (paZ Ps1) (k + 8 + (if b then 5 else 0) + 8)
            (stBytes 8 (gprVal rs0 AxSpinPOr.r9))⌝) -∗
        @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
          ⟨.PHart cpu (.pure ()) rs' none ib', k + 8 + (if b then 5 else 0) + 9⟩ Ψ) -∗
      @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
        ⟨.PHart cpu (.pure ()) rs0 none ib0, k⟩ Ψ := by
  intro HR Hlen Hw8 Hnr_ra Hnr_s0 Hnr_s1 Hnr_mra Hnr_ms0 Hwle_n Hnrn Hwle_i Hc0 HPC0 Hhit0 HhitM
    Bra Bs0 Bs1 Bmra Bms0 Bn Bi Hdj Hval14 Hvb Hval30 Hval1c Hvalr Hret
  -- ---- the seven ranges, pairwise ----
  have D_ra_s0 : dj (paZ Pra) 8 (paZ Ps0) 8 := Hdj 0 1 (paZ Pra, 8) (paZ Ps0, 8) rfl rfl (by decide)
  have D_ra_s1 : dj (paZ Pra) 8 (paZ Ps1) 8 := Hdj 0 2 (paZ Pra, 8) (paZ Ps1, 8) rfl rfl (by decide)
  have D_ra_mra : dj (paZ Pra) 8 (paZ Pmra) 8 :=
    Hdj 0 3 (paZ Pra, 8) (paZ Pmra, 8) rfl rfl (by decide)
  have D_ra_ms0 : dj (paZ Pra) 8 (paZ Pms0) 8 :=
    Hdj 0 4 (paZ Pra, 8) (paZ Pms0, 8) rfl rfl (by decide)
  have D_ra_n : dj (paZ Pra) 8 (paZ Pn) 4 := Hdj 0 5 (paZ Pra, 8) (paZ Pn, 4) rfl rfl (by decide)
  have D_ra_i : dj (paZ Pra) 8 (paZ Pi) 4 := Hdj 0 6 (paZ Pra, 8) (paZ Pi, 4) rfl rfl (by decide)
  have D_s0_s1 : dj (paZ Ps0) 8 (paZ Ps1) 8 := Hdj 1 2 (paZ Ps0, 8) (paZ Ps1, 8) rfl rfl (by decide)
  have D_s0_mra : dj (paZ Ps0) 8 (paZ Pmra) 8 :=
    Hdj 1 3 (paZ Ps0, 8) (paZ Pmra, 8) rfl rfl (by decide)
  have D_s0_ms0 : dj (paZ Ps0) 8 (paZ Pms0) 8 :=
    Hdj 1 4 (paZ Ps0, 8) (paZ Pms0, 8) rfl rfl (by decide)
  have D_s0_n : dj (paZ Ps0) 8 (paZ Pn) 4 := Hdj 1 5 (paZ Ps0, 8) (paZ Pn, 4) rfl rfl (by decide)
  have D_s0_i : dj (paZ Ps0) 8 (paZ Pi) 4 := Hdj 1 6 (paZ Ps0, 8) (paZ Pi, 4) rfl rfl (by decide)
  have D_s1_mra : dj (paZ Ps1) 8 (paZ Pmra) 8 :=
    Hdj 2 3 (paZ Ps1, 8) (paZ Pmra, 8) rfl rfl (by decide)
  have D_s1_ms0 : dj (paZ Ps1) 8 (paZ Pms0) 8 :=
    Hdj 2 4 (paZ Ps1, 8) (paZ Pms0, 8) rfl rfl (by decide)
  have D_s1_n : dj (paZ Ps1) 8 (paZ Pn) 4 := Hdj 2 5 (paZ Ps1, 8) (paZ Pn, 4) rfl rfl (by decide)
  have D_s1_i : dj (paZ Ps1) 8 (paZ Pi) 4 := Hdj 2 6 (paZ Ps1, 8) (paZ Pi, 4) rfl rfl (by decide)
  have D_mra_ms0 : dj (paZ Pmra) 8 (paZ Pms0) 8 :=
    Hdj 3 4 (paZ Pmra, 8) (paZ Pms0, 8) rfl rfl (by decide)
  have D_mra_n : dj (paZ Pmra) 8 (paZ Pn) 4 := Hdj 3 5 (paZ Pmra, 8) (paZ Pn, 4) rfl rfl (by decide)
  have D_mra_i : dj (paZ Pmra) 8 (paZ Pi) 4 := Hdj 3 6 (paZ Pmra, 8) (paZ Pi, 4) rfl rfl (by decide)
  have D_ms0_n : dj (paZ Pms0) 8 (paZ Pn) 4 := Hdj 4 5 (paZ Pms0, 8) (paZ Pn, 4) rfl rfl (by decide)
  have D_ms0_i : dj (paZ Pms0) 8 (paZ Pi) 4 := Hdj 4 6 (paZ Pms0, 8) (paZ Pi, 4) rfl rfl (by decide)
  have D_n_i : dj (paZ Pn) 4 (paZ Pi) 4 := Hdj 5 6 (paZ Pn, 4) (paZ Pi, 4) rfl rfl (by decide)
  clear Hdj
  -- ---- the windows ----
  have HRh : RowSh k (AxOpsem.grow (gtAdGd GT) i)
      (poHead (paZ Pra) (paZ Ps0) (paZ Ps1) (paZ Pmra) (paZ Pms0) (paZ Pn)) :=
    rowShAppL k _ _ _ HR
  have HRr : RowSh (k + 8) (AxOpsem.grow (gtAdGd GT) i)
      ((if b then poInt (paZ Pmra) (paZ Pms0) (paZ Pi) else []) ++
        poTail (paZ Pra) (paZ Ps0) (paZ Ps1) (paZ Pmra) (paZ Pms0) (paZ Pn)) :=
    rowShAppR k _ (poHead (paZ Pra) (paZ Ps0) (paZ Ps1) (paZ Pmra) (paZ Pms0) (paZ Pn)) _ HR
  have HRt : RowSh (k + 8 + (if b then 5 else 0)) (AxOpsem.grow (gtAdGd GT) i)
      (poTail (paZ Pra) (paZ Ps0) (paZ Ps1) (paZ Pmra) (paZ Pms0) (paZ Pn)) := by
    have h := rowShAppR (k + 8) _ (if b then poInt (paZ Pmra) (paZ Pms0) (paZ Pi) else []) _ HRr
    rwa [show (if b then poInt (paZ Pmra) (paZ Pms0) (paZ Pi) else []).length =
      (if b then 5 else 0) by cases b <;> rfl] at h
  have Hlen8 : k + 8 < (AxOpsem.grow (gtAdGd GT) i).length := by
    revert Hlen; split <;> intro Hlen <;> omega
  -- ---- the head and the arm, generic in the continuation (Rocq's "TL" assertion) ----
  have HI : ∀ Cp : IProp GF,
      (∀ (vn0 : List (BitVec 8)) (rs1 : RegFile) (ib1 : Ibch),
        ctrlOkSW T satp0 rs1 ∧ rs1 .PC = AxSpinPO.ppo 0x18 ∧ rs1 .tlb = rs0 .tlb ∧
          gprVal rs1 AxSpinE8.r2 = spo (gprVal rs0 AxSpinE8.r2) ∧
          gprVal rs1 AxSpinE8.r4 = gprVal rs0 AxSpinE8.r4 ∧
          (∀ r : BitVec 5, r.toNat ≠ 1 → r.toNat ≠ 2 → r.toNat ≠ 8 → r.toNat ≠ 9 →
            r.toNat ≠ 10 → r.toNat ≠ 15 → gprVal rs1 r = gprVal rs0 r) ∧
          graphData (gtAdGd GT) (i, k) = some (stBytes 8 (gprVal rs0 AxSpinE8.r1)) ∧
          graphData (gtAdGd GT) (i, k + 1) = some (stBytes 8 (gprVal rs0 AxSpinE8.r8)) ∧
          graphData (gtAdGd GT) (i, k + 2) = some (stBytes 8 (gprVal rs0 AxSpinPOr.r9)) ∧
          graphValue (gtAdGd GT) (i, k + 7) = some vn0 ∧ (ldRes false 4 vn0 == zero_reg) = b ∧
          (b = true → graphData (gtAdGd GT) (i, k + 12) = some (stBytes 4 0#64)) →
        ⊢ Cp -∗ @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
          ⟨.PHart cpu (.pure ()) rs1 none ib1, k + 8 + (if b then 5 else 0)⟩ Ψ) →
      ⊢ Cp -∗ @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
        ⟨.PHart cpu (.pure ()) rs0 none ib0, k⟩ Ψ := by
    intro Cp TL
    iintro C
    iapply (wpdPoHead L GT nm HL Hcons σi T satp0 hmode hasid hppn i cpu Hfix Htxm Htxp Ψ HΨmid
      k b rs0 ib0 Pra Ps0 Ps1 Pmra Pms0 Pn HRh Hlen8 Hw8 Hnr_mra Hnr_ms0 Hnrn Hc0 HPC0 Hhit0
      HhitM Bra Bs0 Bs1 Bmra Bms0 Bn (djSym _ _ _ _ D_mra_ms0) Hval14 Hvb)
    iintro %vn0 %m %rs1 %ib1 %Hh
    obtain ⟨Hc1, HPC1, Htl1, _, Esp1, Es1, HSIE, _, _, Hkeep1, Hgd0, Hgd1, Hgd2, Hgv7, Hb⟩ := Hh
    have Etp1 : gprVal rs1 AxSpinE8.r4 = gprVal rs0 AxSpinE8.r4 :=
      Hkeep1 AxSpinE8.r4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    cases b with
    | false =>
      -- the noff != 0 arm: straight to the tail
      have TL' := TL vn0 rs1 ib1 ⟨Hc1, HPC1, Htl1, Esp1, Etp1, Hkeep1, Hgd0, Hgd1, Hgd2, Hgv7, Hb,
        fun h => absurd h Bool.false_ne_true⟩
      rw [show k + 8 + (if false = true then 5 else 0) = k + 8 from rfl] at TL'
      ihave TLi := TL'
      iapply TLi
      iexact C
    | true =>
      -- the noff == 0 arm
      have HRi : RowSh (k + 8) (AxOpsem.grow (gtAdGd GT) i)
          (poInt (paZ Pmra) (paZ Pms0) (paZ Pi)) := rowShAppL (k + 8) _ _ _ HRr
      iapply (wpdPoInt L GT nm HL Hcons σi T satp0 hmode hasid hppn i cpu Hfix Htxm Htxp Ψ HΨmid
        (k + 8) rs1 ib1 Pmra Pms0 Pi m HRi (by revert Hlen; simp only [↓reduceIte]; omega)
        Hw8 Hnr_mra Hnr_ms0 Hwle_i Hc1 HPC1
        (hitWAgree rs0 rs1 _ Htl1 Hhit0) (hitWAgree rs0 rs1 _ Htl1 HhitM) Es1 HSIE
        (by rw [Esp1]; exact slot8Tlb _ _ _ _ _ _ _ _ Htl1 Bmra)
        (by rw [Esp1]; exact slot8Tlb _ _ _ _ _ _ _ _ Htl1 Bms0)
        (by rw [Etp1]; exact fld4Tlb _ _ _ _ _ _ _ _ Htl1 Bi)
        (djSym _ _ _ _ D_mra_ms0)
        (by rw [show k + 8 + 2 = k + 10 by omega]; exact Hval30 rfl))
      iintro %rs2 %ib2 %Hi
      obtain ⟨Hc2, HPC2, Htl2, _, Esp2, Hkeep2, Hgd4⟩ := Hi
      have TL' := TL vn0 rs2 ib2 ⟨Hc2, HPC2, Htl2.trans Htl1, Esp2.trans Esp1,
        by rw [Hkeep2 AxSpinE8.r4 (by decide) (by decide) (by decide) (by decide) (by decide)];
           exact Etp1,
        fun r Hr1 Hr2 Hr8 Hr9 Hr10 Hr15 => by
          rw [Hkeep2 r Hr1 Hr2 Hr8 Hr10 Hr15]; exact Hkeep1 r Hr1 Hr2 Hr8 Hr9 Hr10 Hr15,
        Hgd0, Hgd1, Hgd2, Hgv7, Hb,
        fun _ => by rw [show k + 12 = k + 8 + 4 by omega]; exact Hgd4⟩
      rw [show k + 8 + (if true = true then 5 else 0) = k + 8 + 5 from rfl] at TL'
      ihave TLi := TL'
      iapply TLi
      iexact C
  refine HI _ (fun vn0 rs1 ib1 Hf => ?_)
  -- ---- the tail, once for both arms ----
  obtain ⟨Hc1, HPC1, Htl1, Esp1, Etp1, Hkeep1, Hgd0, Hgd1, Hgd2, Hgv7, Hb, Hint⟩ := Hf
  iintro C
  obtain ⟨vra, cra, Hkra, Hlra⟩ := shStore k _
    (poSh b (paZ Pra) (paZ Ps0) (paZ Ps1) (paZ Pmra) (paZ Pms0) (paZ Pn) (paZ Pi)) 0 (paZ Pra) 8
    HR rfl
  rw [Nat.add_zero] at Hkra
  obtain ⟨vs0, cs0, Hks0, Hls0⟩ := shStore k _
    (poSh b (paZ Pra) (paZ Ps0) (paZ Ps1) (paZ Pmra) (paZ Pms0) (paZ Pn) (paZ Pi)) 1 (paZ Ps0) 8
    HR rfl
  obtain ⟨vs1, cs1, Hks1, Hls1⟩ := shStore k _
    (poSh b (paZ Pra) (paZ Ps0) (paZ Ps1) (paZ Pmra) (paZ Pms0) (paZ Pn) (paZ Pi)) 2 (paZ Ps1) 8
    HR rfl
  have Evra : vra = stBytes 8 (gprVal rs0 AxSpinE8.r1) := by
    unfold graphData at Hgd0
    rw [AxWp.growLookup _ _ _ _ Hkra] at Hgd0
    simpa only [Option.bind_some, lblData, Option.some.injEq] using Hgd0
  have Evs0 : vs0 = stBytes 8 (gprVal rs0 AxSpinE8.r8) := by
    unfold graphData at Hgd1
    rw [AxWp.growLookup _ _ _ _ Hks0] at Hgd1
    simpa only [Option.bind_some, lblData, Option.some.injEq] using Hgd1
  have Evs1 : vs1 = stBytes 8 (gprVal rs0 AxSpinPOr.r9) := by
    unfold graphData at Hgd2
    rw [AxWp.growLookup _ _ _ _ Hks1] at Hgd2
    simpa only [Option.bind_some, lblData, Option.some.injEq] using Hgd2
  subst Evra Evs0 Evs1
  -- no write to a spill slot between its spill and the tail's start
  have NW : ∀ (jw : Nat) (pa : Int) (w : Nat),
      (∀ it ∈ ((poSh b (paZ Pra) (paZ Ps0) (paZ Ps1) (paZ Pmra) (paZ Pms0) (paZ Pn)
        (paZ Pi)).take (9 + (if b then 5 else 0))).drop (jw + 1), itDisj pa w it) →
      nowr (AxOpsem.grow (gtAdGd GT) i) (k + jw) (k + 8 + (if b then 5 else 0) + 1) pa w := by
    intro jw pa w HF
    rw [show k + 8 + (if b then 5 else 0) + 1 = k + (9 + (if b then 5 else 0)) by
      cases b <;> rfl]
    exact rowShNowr k _ _ jw _ pa w HR (by cases b <;> exact Nat.le_of_ble_eq_true rfl) HF
  obtain ⟨_, HdaL_ra, Hh_ra, Hpr_ra, Hnt_ra⟩ := Bra
  obtain ⟨_, HdaL_s0, Hh_s0, Hpr_s0, Hnt_s0⟩ := Bs0
  obtain ⟨_, HdaL_s1, Hh_s1, Hpr_s1, Hnt_s1⟩ := Bs1
  obtain ⟨HdaS_mra, HdaL_mra, Hh_mra, Hpr_mra, Hnt_mra⟩ := Bmra
  obtain ⟨HdaS_ms0, HdaL_ms0, Hh_ms0, Hpr_ms0, Hnt_ms0⟩ := Bms0
  obtain ⟨HdaS_n, HdaL_n, Hh_n, Hpr_n, Hnt_n⟩ := Bn
  have Evra : AxSpinE8.vaRa rs1 =
      AxSpinE8.sp1Of (spo (gprVal rs0 AxSpinE8.r2)) + sign_extend (m := 64) AxSpinE8.immRa := by
    unfold AxSpinE8.vaRa; rw [Esp1]
  have Evs0 : AxSpinE8.vaS0 rs1 =
      AxSpinE8.sp1Of (spo (gprVal rs0 AxSpinE8.r2)) + sign_extend (m := 64) AxSpinE8.immS0 := by
    unfold AxSpinE8.vaS0; rw [Esp1]
  have Hktk : ∀ j, j ≤ 2 → k + j < k + 8 + (if b then 5 else 0) := by
    intro j hj; split <;> omega
  iapply (wpdPoTail L GT nm HL Hcons σi T satp0 hmode hasid hppn i cpu Hfix Htxm Htxp Ψ HΨmid
    (k + 8 + (if b then 5 else 0)) rs1 ib1 ret Pra Ps0 Ps1 Pmra Pms0 Pn k (k + 1) (k + 2)
    _ _ _ cra cs0 cs1 HRt Hlen Hw8 Hnr_ra Hnr_s0 Hnr_s1 Hnr_mra Hnr_ms0 Hwle_n Hnrn
    Hkra Hlra (Hktk 0 (by omega))
    (NW 0 (paZ Pra) 8 (by
      cases b <;> simp only [poSh, ↓reduceIte, Bool.false_eq_true, List.nil_append,
        Nat.reduceAdd] <;> ax_spin_por_nowr))
    Hks0 Hls0 (Hktk 1 (by omega))
    (NW 1 (paZ Ps0) 8 (by
      cases b <;> simp only [poSh, ↓reduceIte, Bool.false_eq_true, List.nil_append,
        Nat.reduceAdd] <;> ax_spin_por_nowr))
    Hks1 Hls1 (Hktk 2 (by omega))
    (NW 2 (paZ Ps1) 8 (by
      cases b <;> simp only [poSh, ↓reduceIte, Bool.false_eq_true, List.nil_append,
        Nat.reduceAdd] <;> ax_spin_por_nowr))
    Hc1 HPC1 (hitWAgree rs0 rs1 _ Htl1 Hhit0) (hitWAgree rs0 rs1 _ Htl1 HhitM)
    (by rw [Esp1]; exact HdaL_ra) (by rw [Esp1]; exact hitWAgree rs0 rs1 _ Htl1 Hh_ra)
    (by rw [Esp1]; exact HdaL_s0) (by rw [Esp1]; exact hitWAgree rs0 rs1 _ Htl1 Hh_s0)
    (by rw [Esp1]; exact HdaL_s1) (by rw [Esp1]; exact hitWAgree rs0 rs1 _ Htl1 Hh_s1)
    Hpr_ra Hnt_ra Hpr_s0 Hnt_s0 Hpr_s1 Hnt_s1
    (by rw [Evra]; exact HdaS_mra) (by rw [Evra]; exact HdaL_mra)
    (by rw [Evra]; exact hitWAgree rs0 rs1 _ Htl1 Hh_mra)
    (by rw [Evs0]; exact HdaS_ms0) (by rw [Evs0]; exact HdaL_ms0)
    (by rw [Evs0]; exact hitWAgree rs0 rs1 _ Htl1 Hh_ms0)
    Hpr_mra Hnt_mra Hpr_ms0 Hnt_ms0
    (by rw [Etp1]; exact HdaS_n) (by rw [Etp1]; exact HdaL_n)
    (by rw [Etp1]; exact hitWAgree rs0 rs1 _ Htl1 Hh_n) Hpr_n Hnt_n
    (by ax_spin_por_dj_close) (by ax_spin_por_dj_close) (by ax_spin_por_dj_close)
    (by ax_spin_por_dj_close) (by ax_spin_por_dj_close) (by ax_spin_por_dj_close)
    (by ax_spin_por_dj_close) (by ax_spin_por_dj_close) (by ax_spin_por_dj_close)
    (by ax_spin_por_dj_close)
    Hval1c Hvalr Hret)
  iintro %vn %vra' %vs0' %vs1' %rs' %ib' %Hf H6 H7 H8
  obtain ⟨Hcr, HPCr, Htlr, Ea0r, Espr, -, Ea5r, -, -, -, Hrar, Hs0r, Hs1r, Hkeepr, Hgv4, Hgd5,
    Hgv6, Hgv7', Hgv8⟩ := Hf
  iapply C $$ %vn0 %vn %vra' %vs0' %vs1' %rs' %ib' [] H6 H7 H8
  ipureintro
  refine ⟨Hcr, HPCr, Htlr.trans Htl1, ?_, ?_, Ea5r, Hrar, Hs0r, Hs1r, ?_, Hgd0, Hgd1, Hgd2, Hgv7,
    Hb, Hint, Hgv4, Hgd5, Hgv6, Hgv7', Hgv8⟩
  · -- a0 = mycpuRet tp
    rw [Ea0r, Etp1]
  · -- sp restored (Rocq `frame_cancel_32`)
    rw [Espr, Esp1]
    unfold spo
    rw [BitVec.add_assoc,
      show sign_extend (m := 64) (sign_extend (m := 12) (32#6)) +
        sign_extend (m := 64) (caddi16spImm 2#6) = 0#64 by decide]
    exact BitVec.add_zero _
  · -- every other GPR kept
    intro r Hr1 Hr2 Hr8 Hr9 Hr10 Hr15
    rw [Hkeepr r Hr1 Hr2 Hr8 Hr9 Hr10 Hr15]
    exact Hkeep1 r Hr1 Hr2 Hr8 Hr9 Hr10 Hr15

end pushoff

end Weak
