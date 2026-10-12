/-
Weak: **A7-T2b: hand-written `Pexv6` programs for the lock3s per-hart rows, and their opax
runs, WITHOUT Sail decode** (AxSL tier).

Rocq: `iris/AxLock3Prog.v` @ xxvzwolszwmp.

## The Rocq header, in substance

Style: `AxOpsem`'s `OpaxWit` — a DIRECT Sail-monad term (bare `.impure (.ok (.memRead/.memWrite/
.barrier …)) k` chains), no decoder, no fetch.  The target run relation is
`astepAnyNfGv GD i` (AxWpDSteps).

ROWS (design §7.A7 / `AxLock3.lock3`'s per-hart shape), stated as a HYPOTHESIS over an ABSTRACT
`GD`, rf indices and read values quantified:
  writer: `[RMW acquire L (read t/old, write locked); store x v; fence rw,w; release store L
          unlocked]`
  reader: `[RMW acquire L; load x (tx/vB free); fence rw,w; release store L unlocked]`

ADDRESS DEVIATION (Rocq's own): `AxLock3`'s `l3`/`x3` are graph-only placeholders below the RAM
floor (`devAddr` would route them through the MMIO arm, label `LDev`), so the programs abstract
over two RAM addresses `Lpa`/`xpa` with `devAddr … = false` hypotheses.  The row's byte
constants `b0`/`b1` (WeakLitmus) are reused unchanged.

THE RMW SPLIT (S3): the graph's fused `LRmw` row item is realized by TWO opax steps — an
exclusive READ half (`areadStep`, row position unchanged, `aidentAdvRd (.IRmw ..) = 0`) and an
exclusive WRITE half (`AStepWrite`, which advances the position).  The exclusive write's node
also has the `LSilent` retry self-loop (`pnodeStep`'s `memWrite` arm) — stated honestly
(`l3pWriteExclRetry`, `l3pWriteExclDet`), not hidden.

READER'S RECORDED VALUE: the loaded byte `vB` is written into GPR `x10` by a hand-built
`regWrite` (always administrative: `AxOpsem.lbAdminAx true (erwLabel _)`), so the final register file
carries `vB` literally.

**Fetches.** None: the programs are hand-built monad terms with no fetch node; every label of
the runs is a non-fetch label, so the boot-image pin `WeakAxRealize.fetchPin` of
`astepProgNf` holds trivially.

## Deviations from Rocq

1. NAMES: camelCase, `l3p_` ↦ `l3p` (map below).  No name of this file is in the duplicated-name
   table; no Lean-only helpers.  `bv 8` ↦ `BitVec 8`, `Arch.pa` ↦ `PAddr`, `Z` ↦ `Int`.
2. O2 STAGE C: `AxOpsem.astepProg`/`astepProgNf` have no `T`/`img`-oracle parameters (Rocq's
   `T`, `img` arguments of every `astep_prog` lemma are gone; `astepProgNf` takes the image
   `img` for the fetch PIN).  `l3pAstepProgShape` has THREE disjuncts (Rocq's fourth,
   `wlabel_is_fetch l = true ∧ is_Some (wl_rd l)`, came from the deleted `AStep_fetch`).
   `l3pReadStep`'s premise `ak_coh (classify ak) = false` ↦ `(classify ak).akIfetch = false`
   (the Lean read label carries the fetch flag, `rdLabel false …`); `l3pReadNoPrognf` takes
   the same premise (Lean `pstepProgMemreadLbl` needs it: an `AK_ifetch` node steps by the
   ADMIN label `LIFetch`, so its admin step would be an `astepProgNf` step).
3. lean-sail shapes: requests are `Mem_read_request 1 64 …` / `Mem_write_request 1 64 …`
   records (`va := none`, `value := some v`); a read continuation receives `.Ok (w, none)`
   (Rocq `inl (w, None)`), a RAM write's continuation `.Ok (some true)` (Rocq `inl None`), and
   the reader's default on an abort is `.Err _ => b0`.  `pstepProg` quantifies the barrier
   report `obar` (the fence step reports `some .Barrier_RISCV_rw_w`).
4. `init_regstate` ↦ an arbitrary register file `rs` (section variable, as `OpaxWit`
   deviation 6 — Lean has no named initial register file at this layer); `dev0_state` ↦
   `OpaxWit.wtD0`.  `register_set (R_bitvector_64 x10) (Z_to_bv 64 (bv_unsigned vB))` ↦
   `rs.set .x10 (BitVec.ofNat 64 vB.toNat)`; `erw_of ORnone [] (R_bitvector_64 x10)` ↦
   `erwOf .ORnone [] .x10`.
5. Section hypotheses `HLram`/`Hxram` are explicit arguments of the lemmas that use them (Lean
   section variables are not added by proof usage); Rocq's unused `axirisG Σ` context is
   dropped.

**Rocq → Lean name map.**  `l3p_wbytes1` `l3pWbytes1`, `l3p_Lbase` `l3pLbase`, `l3p_xbase`
`l3pXbase`, `l3p_akP/akXaq/akXpl` `l3pAkP/AkXaq/AkXpl`, `l3p_rreq` `l3pRreq`, `l3p_wreq`
`l3pWreq`, `l3p_read_step` `l3pReadStep`, `l3p_write_plain_step` `l3pWritePlainStep`,
`l3p_write_plain_det` `l3pWritePlainDet`, `l3p_write_excl_step` `l3pWriteExclStep`,
`l3p_write_excl_retry` `l3pWriteExclRetry`, `l3p_write_excl_det` `l3pWriteExclDet`,
`l3p_fence_step` `l3pFenceStep`, `l3p_fence_det` `l3pFenceDet`, `l3p_rd_excl_admin/wr/fence`
`l3pRdExclAdmin/Wr/Fence`, `l3p_astep_prog_shape` `l3pAstepProgShape`, `l3p_read_no_prognf`
`l3pReadNoPrognf`, `l3p_w_m0..m4` `l3pWM0..M4`, `l3p_w_p0..p4/pfin` `l3pWP0..P4/Pfin`,
`l3p_w_row` `l3pWRow`, `l3p_w_aread` `l3pWAread`, `l3p_w_astep_write1/2/3`
`l3pWAstepWrite1/2/3`, `l3p_w_astep_fence` `l3pWAstepFence`, `l3p_w_run` `l3pWRun`,
`l3p_r_m0/m1/m2/m2b/m3/m4` `l3pRM0/M1/M2/M2b/M3/M4`, `l3p_r_p0/p1/p2/p2b/p3/p4/pfin`
`l3pRP0/P1/P2/P2b/P3/P4/Pfin`, `l3p_r_row` `l3pRRow`, `l3p_r_aread0/1` `l3pRAread0/1`,
`l3p_r_astep_write1/2` `l3pRAstepWrite1/2`, `l3p_r_pstep_regw` `l3pRPstepRegw`,
`l3p_r_astep_admin_regw` `l3pRAstepAdminRegw`, `l3p_r_astep_fence` `l3pRAstepFence`,
`l3p_r_run` `l3pRRun`.

**Not ported:** the `Print Assumptions` block (the lint's axiom check covers it).
-/
import Weak.AxWpDSteps
import Weak.WeakLitmus

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open Sail Sail.ConcurrencyInterfaceV1
open Sail.ArchSem (FreeM)
open LeanRV64D
open Wlabel

/-! ## 0. Two RAM addresses, parametric -/

/-- A one-byte store's data is the byte itself. -/
theorem l3pWbytes1 (b : BitVec 8) : WeakInterpProj.wbytes 1 b = [b] := by
  simp only [WeakInterpProj.wbytes, List.range'_one, List.map_cons, List.map_nil,
    List.cons.injEq, and_true]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.extractLsb'_toNat, Nat.mul_zero, Nat.shiftRight_zero]
  exact Nat.mod_eq_of_lt b.isLt

section lock3Prog

variable (Lpa xpa : PAddr) (cpu : CPU) (rs : RegFile)

def l3pLbase : Int := paZ Lpa
def l3pXbase : Int := paZ xpa

/-- Access kinds: plain (unlock/store/load), exclusive-acquire (RMW read half),
exclusive-plain (RMW write half, no release bit). -/
def l3pAkP : AK := .AK_explicit ⟨.AV_plain, .AS_normal⟩
def l3pAkXaq : AK := .AK_explicit ⟨.AV_exclusive, .AS_rel_or_acq⟩
def l3pAkXpl : AK := .AK_explicit ⟨.AV_exclusive, .AS_normal⟩

def l3pRreq (ak : AK) (pa : PAddr) : Mem_read_request 1 64 Arch.pa Arch.translation Arch.arch_ak :=
  { access_kind := ak, va := none, pa := pa, translation := (), size := 1, tag := false }

def l3pWreq (ak : AK) (pa : PAddr) (v : BitVec 8) :
    Mem_write_request 1 64 Arch.pa Arch.translation Arch.arch_ak :=
  { access_kind := ak, va := none, pa := pa, translation := (), size := 1, value := some v,
    tag := none }

/-! ## 1. Generic step facts -/

/-- 1.1 A read step, at every returned byte. -/
theorem l3pReadStep (ak : AK) (pa : PAddr) :
    devAddr pa = false → (classify ak).akIfetch = false →
    ∀ (KK : Result (BitVec (8 * 1) × Option Bool) Arch.abort → SailM Unit) (rs : RegFile)
      (ib : Ibch) (d : Efab) (vs : List (BitVec 8)),
    vs.length = 1 →
    pstepProg (.PHart cpu (.impure (.ok (.memRead 1 64 (l3pRreq ak pa))) KK) rs none ib) d
      (rdLabel false (classify ak).akLatest (classify ak).akSync (paZ pa) (tagVals vs)
        (rdAsrc (classify ak).akLatest ib))
      (.PHart cpu (KK (.Ok (wordOfBytes 1 vs, none))) rs none ib) d := by
  intro hdev hfe KK rs ib d vs hlen
  refine ⟨rfl, none, none, none, rfl, rfl, ?_, rfl⟩
  have h := pnodeStepReadAny 1 64 (l3pRreq ak pa) KK rs ib d.efDev vs hdev hlen
  have hfe' : (classify (l3pRreq ak pa).access_kind).akIfetch = false := hfe
  rw [hfe'] at h
  exact h

/-- 1.2 A plain write's step is UNIQUE. -/
theorem l3pWritePlainStep (pa : PAddr) (hdev : devAddr pa = false) (val : BitVec 8) :
    ∀ (KK : Result (Option Bool) Arch.abort → SailM Unit) (rs : RegFile) (ib : Ibch) (d : Efab),
    pstepProg (.PHart cpu (.impure (.ok (.memWrite 1 64 (l3pWreq l3pAkP pa val))) KK) rs none ib) d
      (LStore false (paZ pa) (WeakInterpProj.wbytes 1 val)
        (depsAsrc (depsOfIb ib.ibBits)) (depsVsrc (depsOfIb ib.ibBits)))
      (.PHart cpu (KK (.Ok (some true))) rs none ib) d := by
  intro KK rs ib d
  refine ⟨rfl, none, none, none, rfl, rfl, ?_, rfl⟩
  have hpa : devAddr (l3pWreq l3pAkP pa val).pa = false := hdev
  have hval : (l3pWreq l3pAkP pa val).value = some val := rfl
  simp only [pstepNode, pnodeStep, hpa, hval, Bool.false_eq_true, ↓reduceIte]
  refine ⟨by decide, Or.inl ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩ <;> first | rfl | trivial

theorem l3pWritePlainDet (pa : PAddr) (hdev : devAddr pa = false) (val : BitVec 8) :
    ∀ (KK : Result (Option Bool) Arch.abort → SailM Unit) (rs : RegFile) (ib : Ibch) (d : Efab)
      (l : Wlabel) (p' : Pexv6) (d' : Efab),
    pstepProg (.PHart cpu (.impure (.ok (.memWrite 1 64 (l3pWreq l3pAkP pa val))) KK) rs none ib)
      d l p' d' →
    l = LStore false (paZ pa) (WeakInterpProj.wbytes 1 val)
          (depsAsrc (depsOfIb ib.ibBits)) (depsVsrc (depsOfIb ib.ibBits)) ∧
    p' = .PHart cpu (KK (.Ok (some true))) rs none ib ∧ d' = d := by
  intro KK rs ib d l p' d' h
  cases p' with
  | PDisk _ => exact False.elim h
  | PHart cpu' m' rs' fn' ib' =>
    obtain ⟨rfl, ors, oib, obar, rfl, rfl, hn, hd⟩ := h
    have hpa : devAddr (l3pWreq l3pAkP pa val).pa = false := hdev
    have hval : (l3pWreq l3pAkP pa val).value = some val := rfl
    simp only [pstepNode, pnodeStep, hpa, hval, Bool.false_eq_true, ↓reduceIte] at hn
    rcases hn with ⟨_, ⟨_, rfl, rfl, rfl, rfl, hdd, rfl, rfl⟩ | ⟨hlat, _⟩⟩
    · refine ⟨rfl, rfl, ?_⟩
      rw [hd, hdd]
    · exact absurd hlat Bool.false_ne_true

/-- 1.3 An exclusive write's step: the intended `LExStore` (success) … -/
theorem l3pWriteExclStep (pa : PAddr) (hdev : devAddr pa = false) (val : BitVec 8) :
    ∀ (KK : Result (Option Bool) Arch.abort → SailM Unit) (rs : RegFile) (ib : Ibch) (d : Efab),
    pstepProg (.PHart cpu (.impure (.ok (.memWrite 1 64 (l3pWreq l3pAkXpl pa val))) KK) rs none ib)
      d
      (LExStore false (paZ pa) (WeakInterpProj.wbytes 1 val)
        (depsAsrc (depsOfIb ib.ibBits)) (depsVsrc (depsOfIb ib.ibBits)))
      (.PHart cpu (KK (.Ok (some true))) rs none ib) d := by
  intro KK rs ib d
  refine ⟨rfl, none, none, none, rfl, rfl, ?_, rfl⟩
  have hpa : devAddr (l3pWreq l3pAkXpl pa val).pa = false := hdev
  have hval : (l3pWreq l3pAkXpl pa val).value = some val := rfl
  simp only [pstepNode, pnodeStep, hpa, hval, Bool.false_eq_true, ↓reduceIte]
  refine ⟨by decide, Or.inr ⟨rfl, Or.inl ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩⟩ <;> first | rfl | trivial

/-- … or the `LSilent` retry self-loop. -/
theorem l3pWriteExclRetry (pa : PAddr) (hdev : devAddr pa = false) (val : BitVec 8) :
    ∀ (KK : Result (Option Bool) Arch.abort → SailM Unit) (rs : RegFile) (ib : Ibch) (d : Efab),
    pstepProg (.PHart cpu (.impure (.ok (.memWrite 1 64 (l3pWreq l3pAkXpl pa val))) KK) rs none ib)
      d LSilent
      (.PHart cpu (.impure (.ok (.memWrite 1 64 (l3pWreq l3pAkXpl pa val))) KK) rs none ib) d := by
  intro KK rs ib d
  refine ⟨rfl, none, none, none, rfl, rfl, ?_, rfl⟩
  have hpa : devAddr (l3pWreq l3pAkXpl pa val).pa = false := hdev
  have hval : (l3pWreq l3pAkXpl pa val).value = some val := rfl
  simp only [pstepNode, pnodeStep, hpa, hval, Bool.false_eq_true, ↓reduceIte]
  refine ⟨by decide, Or.inr ⟨rfl, Or.inr ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩⟩ <;> first | rfl | trivial

theorem l3pWriteExclDet (pa : PAddr) (hdev : devAddr pa = false) (val : BitVec 8) :
    ∀ (KK : Result (Option Bool) Arch.abort → SailM Unit) (rs : RegFile) (ib : Ibch) (d : Efab)
      (l : Wlabel) (p' : Pexv6) (d' : Efab),
    pstepProg (.PHart cpu (.impure (.ok (.memWrite 1 64 (l3pWreq l3pAkXpl pa val))) KK) rs none ib)
      d l p' d' →
    (l = LExStore false (paZ pa) (WeakInterpProj.wbytes 1 val)
          (depsAsrc (depsOfIb ib.ibBits)) (depsVsrc (depsOfIb ib.ibBits)) ∧
      p' = .PHart cpu (KK (.Ok (some true))) rs none ib ∧ d' = d) ∨
    (l = LSilent ∧
      p' = .PHart cpu (.impure (.ok (.memWrite 1 64 (l3pWreq l3pAkXpl pa val))) KK) rs none ib ∧
      d' = d) := by
  intro KK rs ib d l p' d' h
  cases p' with
  | PDisk _ => exact False.elim h
  | PHart cpu' m' rs' fn' ib' =>
    obtain ⟨rfl, ors, oib, obar, rfl, rfl, hn, hd⟩ := h
    have hpa : devAddr (l3pWreq l3pAkXpl pa val).pa = false := hdev
    have hval : (l3pWreq l3pAkXpl pa val).value = some val := rfl
    simp only [pstepNode, pnodeStep, hpa, hval, Bool.false_eq_true, ↓reduceIte] at hn
    rcases hn with ⟨_, ⟨hlat, _⟩ | ⟨_, ⟨rfl, rfl, rfl, rfl, hdd, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl, rfl, hdd, rfl, rfl⟩⟩⟩
    · exact absurd hlat.symm Bool.false_ne_true
    · exact .inl ⟨rfl, rfl, by rw [hd, hdd]⟩
    · exact .inr ⟨rfl, rfl, by rw [hd, hdd]⟩

/-- 1.4 The fence step: unique; `ebarPark .Barrier_RISCV_rw_w = none`, so no fence parks. -/
theorem l3pFenceStep :
    ∀ (KK : Unit → SailM Unit) (rs : RegFile) (ib : Ibch) (d : Efab),
    pstepProg (.PHart cpu (.impure (.ok (.barrier .Barrier_RISCV_rw_w)) KK) rs none ib) d
      (LFence true true false true)
      (.PHart cpu (KK ()) rs none ib) d := by
  intro KK rs ib d
  exact ⟨rfl, none, none, some .Barrier_RISCV_rw_w, rfl, rfl,
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl⟩

theorem l3pFenceDet :
    ∀ (KK : Unit → SailM Unit) (rs : RegFile) (ib : Ibch) (d : Efab) (l : Wlabel) (p' : Pexv6)
      (d' : Efab),
    pstepProg (.PHart cpu (.impure (.ok (.barrier .Barrier_RISCV_rw_w)) KK) rs none ib) d l p' d' →
    l = LFence true true false true ∧ p' = .PHart cpu (KK ()) rs none ib ∧ d' = d := by
  intro KK rs ib d l p' d' h
  cases p' with
  | PDisk _ => exact False.elim h
  | PHart cpu' m' rs' fn' ib' =>
    obtain ⟨rfl, ors, oib, obar, rfl, rfl, hn, hd⟩ := h
    obtain ⟨rfl, rfl, rfl, rfl, hdd, rfl, rfl⟩ := hn
    exact ⟨rfl, rfl, by rw [hd, hdd]⟩

/-- 1.5 A `memRead` node never steps by anything but a read: read labels are disjoint from
admin / write / fence labels. -/
theorem l3pRdExclAdmin (l : Wlabel) : (wlRd l).isSome = true → AxOpsem.lbAdminAx true l → False := by
  cases l <;> simp [wlRd, AxOpsem.lbAdminAx]

theorem l3pRdExclWr (l : Wlabel) : (wlRd l).isSome = true → (wlWr l).isSome = true → False := by
  cases l <;> simp [wlRd, wlWr]

theorem l3pRdExclFence (l : Wlabel) :
    (wlRd l).isSome = true → (wlFence l).isSome = true → False := by
  cases l <;> simp [wlRd, wlFence]

/-- `AxOpsem.astepProg`'s own shape, at arbitrary indices (deviation 2: three disjuncts). -/
theorem l3pAstepProgShape (row : List Lbl) (s : Athread) (l : Wlabel) (s' : Athread) :
    AxOpsem.astepProg row s l s' →
    AxOpsem.lbAdminAx true l ∨ (wlWr l).isSome = true ∨ (wlFence l).isSome = true := by
  intro h
  cases h with
  | AStepAdmin _ _ _ _ _ _ hadm _ => exact .inl hadm
  | AStepWrite _ _ _ _ _ _ _ _ hwr _ _ _ => exact .inr (.inl hwr)
  | AStepFence _ _ _ _ _ _ _ _ hfe _ _ => exact .inr (.inr hfe)

theorem l3pReadNoPrognf (ak : AK) (pa : PAddr) (hdev : devAddr pa = false)
    (hfe : (classify ak).akIfetch = false) :
    ∀ (row : List Lbl) (img : Image)
      (KK : Result (BitVec (8 * 1) × Option Bool) Arch.abort → SailM Unit) (rs : RegFile)
      (ib : Ibch) (k : Nat) (s' : Athread),
    astepProgNf row img ⟨.PHart cpu (.impure (.ok (.memRead 1 64 (l3pRreq ak pa))) KK) rs none ib, k⟩
      s' → False := by
  intro row img KK rs ib k s' ⟨l, hap, _⟩
  obtain ⟨d, d', hst⟩ := astepProgPstep row _ l s' hap
  obtain ⟨hrd, _⟩ := pstepProgMemreadLbl cpu 1 64 (l3pRreq ak pa) KK rs ib d l s'.atP d' hdev hfe hst
  rcases l3pAstepProgShape row _ l s' hap with hadm | hwr | hfn
  · exact l3pRdExclAdmin l hrd hadm
  · exact l3pRdExclWr l hrd hwr
  · exact l3pRdExclFence l hrd hfn

/-! ## 2. The writer hart: `[RMW-acq L; store x v; fence rw,w; store L unlocked]` -/

def l3pWM4 : SailM Unit :=
  .impure (.ok (.memWrite 1 64 (l3pWreq l3pAkP Lpa b0))) (fun _ => .pure ())
def l3pWM3 : SailM Unit :=
  .impure (.ok (.barrier .Barrier_RISCV_rw_w)) (fun _ => l3pWM4 Lpa)
def l3pWM2 (v : BitVec 8) : SailM Unit :=
  .impure (.ok (.memWrite 1 64 (l3pWreq l3pAkP xpa v))) (fun _ => l3pWM3 Lpa)
def l3pWM1 (v : BitVec 8) : SailM Unit :=
  .impure (.ok (.memWrite 1 64 (l3pWreq l3pAkXpl Lpa b1))) (fun _ => l3pWM2 Lpa xpa v)
def l3pWM0 (v : BitVec 8) : SailM Unit :=
  .impure (.ok (.memRead 1 64 (l3pRreq l3pAkXaq Lpa))) (fun _ => l3pWM1 Lpa xpa v)

def l3pWP0 (v : BitVec 8) : Pexv6 := .PHart cpu (l3pWM0 Lpa xpa v) rs none ibNone
def l3pWP1 (v : BitVec 8) : Pexv6 := .PHart cpu (l3pWM1 Lpa xpa v) rs none ibNone
def l3pWP2 (v : BitVec 8) : Pexv6 := .PHart cpu (l3pWM2 Lpa xpa v) rs none ibNone
def l3pWP3 : Pexv6 := .PHart cpu (l3pWM3 Lpa) rs none ibNone
def l3pWP4 : Pexv6 := .PHart cpu (l3pWM4 Lpa) rs none ibNone
def l3pWPfin : Pexv6 := .PHart cpu (.pure ()) rs none ibNone

def l3pWRow (t : Nat) (old v : BitVec 8) : List Lbl :=
  [.LRmw true false (l3pLbase Lpa) [t] [old] [b1] .WCplain,
   .LStore false (l3pXbase xpa) [v] .WCplain,
   .LFence true true false true,
   .LStore false (l3pLbase Lpa) [b0] .WCplain]

/-! ### 2.1 The five step lemmas -/

theorem l3pWAread (HLram : devAddr Lpa = false) (row : List Lbl) (v : BitVec 8) (t : Nat)
    (old : BitVec 8) :
    row[0]? = some (.LRmw true false (l3pLbase Lpa) [t] [old] [b1] .WCplain) →
    areadStep row ⟨l3pWP0 Lpa xpa cpu rs v, 0⟩ (.IRmw true false (l3pLbase Lpa) 1)
      (fun _ => ⟨l3pWP1 Lpa xpa cpu rs v, 0⟩) := by
  intro hrow
  refine ⟨_, hrow, rfl, rfl, ?_⟩
  intro vs hvs
  refine ⟨rdLabel false true (classify l3pAkXaq).akSync (l3pLbase Lpa) (tagVals vs)
      (rdAsrc true ibNone), OpaxWit.wtD0, OpaxWit.wtD0, ?_, ?_,
    l3pReadStep cpu l3pAkXaq Lpa HLram rfl _ rs ibNone OpaxWit.wtD0 vs hvs, rfl⟩
  · simp only [rdLabel, wlRd, aidentRd, tagValsLength, Bool.false_eq_true, ↓reduceIte]
    rw [hvs]; rfl
  · rw [rdLabelRvals _ _ _ _ _ _ rfl, tagValsSnd]

theorem l3pWAstepWrite1 (HLram : devAddr Lpa = false) (row : List Lbl) (v : BitVec 8) (t : Nat)
    (old : BitVec 8) :
    row[0]? = some (.LRmw true false (l3pLbase Lpa) [t] [old] [b1] .WCplain) →
    AxOpsem.astepProg row ⟨l3pWP1 Lpa xpa cpu rs v, 0⟩
      (LExStore false (l3pLbase Lpa) (WeakInterpProj.wbytes 1 b1) [] [])
      ⟨l3pWP2 Lpa xpa cpu rs v, 1⟩ := by
  intro hrow
  refine .AStepWrite _ 0 OpaxWit.wtD0 _ _ _ OpaxWit.wtD0 hrow rfl rfl ?_ ?_
  · simp only [wlWdata, lblData, l3pWbytes1]
  · exact l3pWriteExclStep cpu Lpa HLram b1 (fun _ => l3pWM2 Lpa xpa v) rs ibNone OpaxWit.wtD0

theorem l3pWAstepWrite2 (Hxram : devAddr xpa = false) (row : List Lbl) (v : BitVec 8) :
    row[1]? = some (.LStore false (l3pXbase xpa) [v] .WCplain) →
    AxOpsem.astepProg row ⟨l3pWP2 Lpa xpa cpu rs v, 1⟩
      (LStore false (l3pXbase xpa) (WeakInterpProj.wbytes 1 v) [] [])
      ⟨l3pWP3 Lpa cpu rs, 2⟩ := by
  intro hrow
  refine .AStepWrite _ 1 OpaxWit.wtD0 _ _ _ OpaxWit.wtD0 hrow rfl rfl ?_ ?_
  · simp only [wlWdata, lblData, l3pWbytes1]
  · exact l3pWritePlainStep cpu xpa Hxram v (fun _ => l3pWM3 Lpa) rs ibNone OpaxWit.wtD0

theorem l3pWAstepFence (row : List Lbl) :
    row[2]? = some (.LFence true true false true) →
    AxOpsem.astepProg row ⟨l3pWP3 Lpa cpu rs, 2⟩ (LFence true true false true)
      ⟨l3pWP4 Lpa cpu rs, 3⟩ := by
  intro hrow
  exact .AStepFence _ 2 OpaxWit.wtD0 _ _ _ OpaxWit.wtD0 hrow rfl rfl
    (l3pFenceStep cpu (fun _ => l3pWM4 Lpa) rs ibNone OpaxWit.wtD0)

theorem l3pWAstepWrite3 (HLram : devAddr Lpa = false) (row : List Lbl) :
    row[3]? = some (.LStore false (l3pLbase Lpa) [b0] .WCplain) →
    AxOpsem.astepProg row ⟨l3pWP4 Lpa cpu rs, 3⟩
      (LStore false (l3pLbase Lpa) (WeakInterpProj.wbytes 1 b0) [] [])
      ⟨l3pWPfin cpu rs, 4⟩ := by
  intro hrow
  refine .AStepWrite _ 3 OpaxWit.wtD0 _ _ _ OpaxWit.wtD0 hrow rfl rfl ?_ ?_
  · simp only [wlWdata, lblData, l3pWbytes1]
  · exact l3pWritePlainStep cpu Lpa HLram b0 (fun _ => .pure ()) rs ibNone OpaxWit.wtD0

/-! ### 2.2 THE RUN, over an abstract `GD`: 5 opax steps, the RMW's read value from
`graphValue` -/

theorem l3pWRun (HLram : devAddr Lpa = false) (Hxram : devAddr xpa = false) (GD : Gdexec)
    (i : Agent) (t : Nat) (old v : BitVec 8)
    (Hrow : AxOpsem.grow GD i = l3pWRow Lpa xpa t old v) :
    nsteps (astepAnyNfGv GD i) 5 ⟨l3pWP0 Lpa xpa cpu rs v, 0⟩ ⟨l3pWPfin cpu rs, 4⟩ := by
  have hl0 : (AxOpsem.grow GD i)[0]? =
      some (.LRmw true false (l3pLbase Lpa) [t] [old] [b1] .WCplain) := by rw [Hrow]; rfl
  have hl1 : (AxOpsem.grow GD i)[1]? = some (.LStore false (l3pXbase xpa) [v] .WCplain) := by
    rw [Hrow]; rfl
  have hl2 : (AxOpsem.grow GD i)[2]? = some (.LFence true true false true) := by rw [Hrow]; rfl
  have hl3 : (AxOpsem.grow GD i)[3]? = some (.LStore false (l3pLbase Lpa) [b0] .WCplain) := by
    rw [Hrow]; rfl
  have hgv0 : graphValue GD (i, 0) = some [old] := by
    simp only [graphValue, AxWp.growLookup GD i 0 _ hl0, Option.bind_some, lblValue]
  refine nsteps_l (astepAnyNfGv.ANFGVRead _ (.IRmw true false (l3pLbase Lpa) 1)
    (fun _ => ⟨l3pWP1 Lpa xpa cpu rs v, 0⟩) [old]
    (l3pWAread Lpa xpa cpu rs HLram _ v t old hl0) hgv0 rfl) ?_
  refine nsteps_l (astepAnyNfGv.ANFGVProg _ _
    ⟨_, l3pWAstepWrite1 Lpa xpa cpu rs HLram _ v t old hl0, trivial⟩) ?_
  refine nsteps_l (astepAnyNfGv.ANFGVProg _ _
    ⟨_, l3pWAstepWrite2 Lpa xpa cpu rs Hxram _ v hl1, trivial⟩) ?_
  refine nsteps_l (astepAnyNfGv.ANFGVProg _ _
    ⟨_, l3pWAstepFence Lpa cpu rs _ hl2, trivial⟩) ?_
  refine nsteps_l (astepAnyNfGv.ANFGVProg _ _
    ⟨_, l3pWAstepWrite3 Lpa cpu rs HLram _ hl3, trivial⟩) ?_
  exact nsteps_O _

/-! ## 3. The reader hart (B): `[RMW-acq L; load x; fence rw,w; store L unlocked]`; `vB` is
recorded into GPR `x10` -/

def l3pRM4 : SailM Unit :=
  .impure (.ok (.memWrite 1 64 (l3pWreq l3pAkP Lpa b0))) (fun _ => .pure ())
def l3pRM3 : SailM Unit :=
  .impure (.ok (.barrier .Barrier_RISCV_rw_w)) (fun _ => l3pRM4 Lpa)
def l3pRM2b (vB : BitVec 8) : SailM Unit :=
  .impure (.ok (.regWrite .x10 (BitVec.ofNat 64 vB.toNat))) (fun _ => l3pRM3 Lpa)
def l3pRM2 : SailM Unit :=
  .impure (.ok (.memRead 1 64 (l3pRreq l3pAkP xpa)))
    (fun ans => l3pRM2b Lpa (match ans with | .Ok (w, _) => w | .Err _ => b0))
def l3pRM1 : SailM Unit :=
  .impure (.ok (.memWrite 1 64 (l3pWreq l3pAkXpl Lpa b1))) (fun _ => l3pRM2 Lpa xpa)
def l3pRM0 : SailM Unit :=
  .impure (.ok (.memRead 1 64 (l3pRreq l3pAkXaq Lpa))) (fun _ => l3pRM1 Lpa xpa)

def l3pRP0 : Pexv6 := .PHart cpu (l3pRM0 Lpa xpa) rs none ibNone
def l3pRP1 : Pexv6 := .PHart cpu (l3pRM1 Lpa xpa) rs none ibNone
def l3pRP2 : Pexv6 := .PHart cpu (l3pRM2 Lpa xpa) rs none ibNone
def l3pRP2b (vB : BitVec 8) : Pexv6 := .PHart cpu (l3pRM2b Lpa vB) rs none ibNone
def l3pRP3 (vB : BitVec 8) : Pexv6 :=
  .PHart cpu (l3pRM3 Lpa) (rs.set .x10 (BitVec.ofNat 64 vB.toNat)) none ibNone
def l3pRP4 (vB : BitVec 8) : Pexv6 :=
  .PHart cpu (l3pRM4 Lpa) (rs.set .x10 (BitVec.ofNat 64 vB.toNat)) none ibNone
def l3pRPfin (vB : BitVec 8) : Pexv6 :=
  .PHart cpu (.pure ()) (rs.set .x10 (BitVec.ofNat 64 vB.toNat)) none ibNone

def l3pRRow (t : Nat) (old : BitVec 8) (tx : Nat) (vB : BitVec 8) : List Lbl :=
  [.LRmw true false (l3pLbase Lpa) [t] [old] [b1] .WCplain,
   .LLoad false (l3pXbase xpa) [tx] [vB],
   .LFence true true false true,
   .LStore false (l3pLbase Lpa) [b0] .WCplain]

theorem l3pRAread0 (HLram : devAddr Lpa = false) (row : List Lbl) (t : Nat) (old : BitVec 8) :
    row[0]? = some (.LRmw true false (l3pLbase Lpa) [t] [old] [b1] .WCplain) →
    areadStep row ⟨l3pRP0 Lpa xpa cpu rs, 0⟩ (.IRmw true false (l3pLbase Lpa) 1)
      (fun _ => ⟨l3pRP1 Lpa xpa cpu rs, 0⟩) := by
  intro hrow
  refine ⟨_, hrow, rfl, rfl, ?_⟩
  intro vs hvs
  refine ⟨rdLabel false true (classify l3pAkXaq).akSync (l3pLbase Lpa) (tagVals vs)
      (rdAsrc true ibNone), OpaxWit.wtD0, OpaxWit.wtD0, ?_, ?_,
    l3pReadStep cpu l3pAkXaq Lpa HLram rfl _ rs ibNone OpaxWit.wtD0 vs hvs, rfl⟩
  · simp only [rdLabel, wlRd, aidentRd, tagValsLength, Bool.false_eq_true, ↓reduceIte]
    rw [hvs]; rfl
  · rw [rdLabelRvals _ _ _ _ _ _ rfl, tagValsSnd]

theorem l3pRAstepWrite1 (HLram : devAddr Lpa = false) (row : List Lbl) (t : Nat)
    (old : BitVec 8) :
    row[0]? = some (.LRmw true false (l3pLbase Lpa) [t] [old] [b1] .WCplain) →
    AxOpsem.astepProg row ⟨l3pRP1 Lpa xpa cpu rs, 0⟩
      (LExStore false (l3pLbase Lpa) (WeakInterpProj.wbytes 1 b1) [] [])
      ⟨l3pRP2 Lpa xpa cpu rs, 1⟩ := by
  intro hrow
  refine .AStepWrite _ 0 OpaxWit.wtD0 _ _ _ OpaxWit.wtD0 hrow rfl rfl ?_ ?_
  · simp only [wlWdata, lblData, l3pWbytes1]
  · exact l3pWriteExclStep cpu Lpa HLram b1 (fun _ => l3pRM2 Lpa xpa) rs ibNone OpaxWit.wtD0

theorem l3pRAread1 (Hxram : devAddr xpa = false) (row : List Lbl) (tx : Nat) (vB : BitVec 8) :
    row[1]? = some (.LLoad false (l3pXbase xpa) [tx] [vB]) →
    areadStep row ⟨l3pRP2 Lpa xpa cpu rs, 1⟩ (.IRead false (l3pXbase xpa) 1)
      (fun vs => ⟨l3pRP2b Lpa cpu rs (wordOfBytes 1 vs), 2⟩) := by
  intro hrow
  refine ⟨_, hrow, rfl, rfl, ?_⟩
  intro vs hvs
  refine ⟨rdLabel false false (classify l3pAkP).akSync (l3pXbase xpa) (tagVals vs)
      (rdAsrc false ibNone), OpaxWit.wtD0, OpaxWit.wtD0, ?_, ?_,
    l3pReadStep cpu l3pAkP xpa Hxram rfl _ rs ibNone OpaxWit.wtD0 vs hvs, rfl⟩
  · simp only [rdLabel, wlRd, aidentRd, tagValsLength, Bool.false_eq_true, ↓reduceIte]
    rw [hvs]; rfl
  · rw [rdLabelRvals _ _ _ _ _ _ rfl, tagValsSnd]

/-- The `regWrite` recording `vB` is administrative. -/
theorem l3pRPstepRegw (vB : BitVec 8) :
    pstepProg (l3pRP2b Lpa cpu rs vB) OpaxWit.wtD0 (erwLabel (erwOf .ORnone [] .x10))
      (.PHart cpu (l3pRM3 Lpa) (rs.set .x10 (BitVec.ofNat 64 vB.toNat)) none ibNone)
      OpaxWit.wtD0 :=
  ⟨rfl, some (rs.set .x10 (BitVec.ofNat 64 vB.toNat)), none, none, rfl, rfl,
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl⟩

theorem l3pRAstepAdminRegw (row : List Lbl) (vB : BitVec 8) :
    AxOpsem.astepProg row ⟨l3pRP2b Lpa cpu rs vB, 2⟩ (erwLabel (erwOf .ORnone [] .x10))
      ⟨l3pRP3 Lpa cpu rs vB, 2⟩ :=
  .AStepAdmin _ 2 OpaxWit.wtD0 _ _ OpaxWit.wtD0
    (by cases erwOf .ORnone [] .x10 <;> trivial) (l3pRPstepRegw Lpa cpu rs vB)

theorem l3pRAstepFence (row : List Lbl) (vB : BitVec 8) :
    row[2]? = some (.LFence true true false true) →
    AxOpsem.astepProg row ⟨l3pRP3 Lpa cpu rs vB, 2⟩ (LFence true true false true)
      ⟨l3pRP4 Lpa cpu rs vB, 3⟩ := by
  intro hrow
  exact .AStepFence _ 2 OpaxWit.wtD0 _ _ _ OpaxWit.wtD0 hrow rfl rfl
    (l3pFenceStep cpu (fun _ => l3pRM4 Lpa) (rs.set .x10 (BitVec.ofNat 64 vB.toNat)) ibNone
      OpaxWit.wtD0)

theorem l3pRAstepWrite2 (HLram : devAddr Lpa = false) (row : List Lbl) (vB : BitVec 8) :
    row[3]? = some (.LStore false (l3pLbase Lpa) [b0] .WCplain) →
    AxOpsem.astepProg row ⟨l3pRP4 Lpa cpu rs vB, 3⟩
      (LStore false (l3pLbase Lpa) (WeakInterpProj.wbytes 1 b0) [] [])
      ⟨l3pRPfin cpu rs vB, 4⟩ := by
  intro hrow
  refine .AStepWrite _ 3 OpaxWit.wtD0 _ _ _ OpaxWit.wtD0 hrow rfl rfl ?_ ?_
  · simp only [wlWdata, lblData, l3pWbytes1]
  · exact l3pWritePlainStep cpu Lpa HLram b0 (fun _ => .pure ())
      (rs.set .x10 (BitVec.ofNat 64 vB.toNat)) ibNone OpaxWit.wtD0

/-! ### 3.1 THE RUN: 6 opax steps (the extra administrative `regWrite`); `old`/`vB` from
`graphValue` -/

theorem l3pRRun (HLram : devAddr Lpa = false) (Hxram : devAddr xpa = false) (GD : Gdexec)
    (i : Agent) (t : Nat) (old : BitVec 8) (tx : Nat) (vB : BitVec 8)
    (Hrow : AxOpsem.grow GD i = l3pRRow Lpa xpa t old tx vB) :
    nsteps (astepAnyNfGv GD i) 6 ⟨l3pRP0 Lpa xpa cpu rs, 0⟩
      ⟨l3pRPfin cpu rs (wordOfBytes 1 [vB]), 4⟩ := by
  have hl0 : (AxOpsem.grow GD i)[0]? =
      some (.LRmw true false (l3pLbase Lpa) [t] [old] [b1] .WCplain) := by rw [Hrow]; rfl
  have hl1 : (AxOpsem.grow GD i)[1]? = some (.LLoad false (l3pXbase xpa) [tx] [vB]) := by
    rw [Hrow]; rfl
  have hl2 : (AxOpsem.grow GD i)[2]? = some (.LFence true true false true) := by rw [Hrow]; rfl
  have hl3 : (AxOpsem.grow GD i)[3]? = some (.LStore false (l3pLbase Lpa) [b0] .WCplain) := by
    rw [Hrow]; rfl
  have hgv0 : graphValue GD (i, 0) = some [old] := by
    simp only [graphValue, AxWp.growLookup GD i 0 _ hl0, Option.bind_some, lblValue]
  have hgv1 : graphValue GD (i, 1) = some [vB] := by
    simp only [graphValue, AxWp.growLookup GD i 1 _ hl1, Option.bind_some, lblValue]
  refine nsteps_l (astepAnyNfGv.ANFGVRead _ (.IRmw true false (l3pLbase Lpa) 1)
    (fun _ => ⟨l3pRP1 Lpa xpa cpu rs, 0⟩) [old]
    (l3pRAread0 Lpa xpa cpu rs HLram _ t old hl0) hgv0 rfl) ?_
  refine nsteps_l (astepAnyNfGv.ANFGVProg _ _
    ⟨_, l3pRAstepWrite1 Lpa xpa cpu rs HLram _ t old hl0, trivial⟩) ?_
  refine nsteps_l (astepAnyNfGv.ANFGVRead _ (.IRead false (l3pXbase xpa) 1)
    (fun vs => ⟨l3pRP2b Lpa cpu rs (wordOfBytes 1 vs), 2⟩) [vB]
    (l3pRAread1 Lpa xpa cpu rs Hxram _ tx vB hl1) hgv1 rfl) ?_
  refine nsteps_l (astepAnyNfGv.ANFGVProg _ _
    ⟨_, l3pRAstepAdminRegw Lpa cpu rs _ (wordOfBytes 1 [vB]), trivial⟩) ?_
  refine nsteps_l (astepAnyNfGv.ANFGVProg _ _
    ⟨_, l3pRAstepFence Lpa cpu rs _ (wordOfBytes 1 [vB]) hl2, trivial⟩) ?_
  refine nsteps_l (astepAnyNfGv.ANFGVProg _ _
    ⟨_, l3pRAstepWrite2 Lpa cpu rs HLram _ (wordOfBytes 1 [vB]) hl3, trivial⟩) ?_
  exact nsteps_O _

end lock3Prog

end Weak
