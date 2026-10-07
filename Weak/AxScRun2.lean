/-
Weak: **THE CERTIFICATE TOOLKIT, run side** — a driver with FENCE and fused-RMW (`amoswap`) arms,
its soundness for `astepAnyNfGv`, the emission it records, and the bridge from a driven run to the
RUN premise of the tier-A theorems at a `graphOfSc` graph.

Rocq: `iris/AxScRun2.v` @ xxvzwolszwmp.

## What this file proves

`AxEpiRun.drive`/`nodeStep` stop at a barrier node and refuse every `akLatest` (exclusive) access
and every `LRmw` row item, so they cannot run acquire (`amoswap.w.aq`) or release (`fence rw,w`).
`nodeStep2` is that driver plus:
  - BARRIER arm: a non-parking barrier (`ebarPark b = none`: every kind but `fence.tso`) whose
    bits (`ebarBits`) equal the row's `LFence` item realizes it (`AStepFence`) and advances;
  - RMW READ arm: an exclusive RAM read at an `LRmw` row item reads the item's `rvs` (the GRAPH
    VALUE) through `ANFGVRead` at identity `IRmw aq rl base wvs.length`, and does NOT advance;
  - RMW WRITE arm: the exclusive write (`LExStore`) realizes the item's write half through
    `AStepWrite` (bytes = `wvs`) and advances.
It also RECORDS the emission: each node yields the `Eitem` the program half
(`WeakEvInst.pnodeStep`) labels that node with (positioned at the row index for memory nodes).
`drive2` iterates to the row end.

PROVED: `nodeStep2Sound`/`drive2Sound` (a successful drive is an `astepAnyNfGv GD i` run ending
at `kend`); `nodeStep2Label` (the recorded item's label IS the label of a real `pstepProg` step
between the same two states); `drive2Erase` (the driver ignores read timestamps);
`runGraphOfSc` (drive2 on the GRAPH's row ⇒ the `tierAAstep`-form run premise at
`gtAdGd (graphOfSc …)`, as `AxSpinGate.tierAAdequacyAnnGateT`'s `Hrun` takes it); `runBridge`
(drive2 on the INPUT row + `valsOkB` ⇒ the same premise, via `graphOfScErase`).

SCOPE (Rocq).  fence.tso (parking) is not supported; a failed exclusive write (the retry
self-loop) is not driven; device (MMIO) accesses stop the driver.

## Deviations from Rocq

1. O2 STAGE C (as `AxEpiRun` deviation 1): an `akIfetch` read is an ADMIN step answered from the
   boot image (`AxEpiRun.imgRead`, timestamps 0, position unchanged), so `nodeStep2`/`drive2`
   take the image `img` first; the recorded item of a fetch is `(LIFetch (paZ pa) (tagVals vs),
   none)` (the program's own label; `dstepT`'s `LIFetch` arm is inert, so the deps are as in
   Rocq, where the fetch was a positioned row read).  Rocq's `ak_coh = false` test is the else
   branch of the fetch test.  `nodeStep2Sound`/`drive2Sound` are stated at `img :=
   GD.gdG.gxImg`; `runGraphOfSc`/`runBridge` at the graph image `fun a => some (img a)`.
2. Q7: an `instrAnnounce` at an SFENCE.VMA word is not driven (`sfAnnB n w = true` ⇒ `none`).
3. TYPES (as `AxEpiRun` deviation 3): write values are `Option` (`req.value = none` ⇒ `none`;
   `nfRmwWrite` takes `req.value = some v` and `WeakInterpProj.wbytes n v = wvs`); answers
   `.Ok (w, none)` / `.Ok (some true)`; `S k` ↦ `k + 1`; `dev0_state` ↦ `OpaxWit.wtD0`;
   `rd_label ex …` ↦ `rdLabel false ex …`.  The Lean `pnodeStep` carries `obar`.  The
   check order inside the memory arms puts the `akLatest` test inside each row-item arm (as
   Rocq).
4. INSTANCES: `astepAnyNfGv`/`tierAAstep` take no Iris instance in Lean, so `drive2Sound`
   quantifies over `cpu` only, and `runGraphOfSc`/`runBridge` over `cpu (N : Type) (nm : N)`
   (Rocq: `∀ cpu Σ axannotG T N ob_st0 ob_st_interp0 nm axannotGS`; Lean `tierAAstep` has no
   `T`, `obSt0`, `obStInterp0`).
5. `nodeStep2Label` takes the image (deviation 1).

**Rocq → Lean name map.**  `ebar_bits` `ebarBits`, `ebar_label_bits` `ebarLabelBits`, `step2_t`
`Step2T`, `node_step2` `nodeStep2`, `drive2` `drive2`, `nf_fence` `nfFence`, `nf_rmw_read`
`nfRmwRead`, `nf_rmw_write` `nfRmwWrite`, `node_step2_sound` `nodeStep2Sound`, `drive2_sound`
`drive2Sound`, `node_step2_label` `nodeStep2Label`, `node_step2_erase` `nodeStep2Erase`,
`drive2_erase_1` `drive2Erase1`, `drive2_erase` `drive2Erase`, `run_graph_of_sc` `runGraphOfSc`,
`run_bridge` `runBridge`.  None is in the duplicated-name table.  Lean-only (file-qualified):
`AxScRun2.ebarWlFence`, `AxScRun2.fetchPinEbar`, `AxScRun2.pstepOfNode`.

**Dropped:** nothing (Rocq 16; Lean 16 + 3 Lean-only helpers).  **Not ported:** the
`Print Assumptions` lines (the lint's axiom check covers them).
-/
import Weak.AxEpiRun
import Weak.AxScRun

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open Sail Sail.ConcurrencyInterfaceV1
open Sail.ArchSem (FreeM)
open LeanRV64D
open Wlabel

/-! # 1. The driver -/

def ebarBits (b : barrier_kind) : Bool × Bool × Bool × Bool :=
  match ebarNow b with
  | some x => x
  | none => (false, false, false, false)

theorem ebarLabelBits (b : barrier_kind) :
    ebarLabel b = LFence (ebarBits b).1 (ebarBits b).2.1 (ebarBits b).2.2.1 (ebarBits b).2.2.2 := by
  cases b <;> rfl

theorem AxScRun2.ebarWlFence (b : barrier_kind) : wlFence (ebarLabel b) = some (ebarBits b) := by
  cases b <;> rfl

theorem AxScRun2.fetchPinEbar (img : Image) (b : barrier_kind) :
    WeakAxRealize.fetchPin img (ebarLabel b) := by
  rw [ebarLabelBits]; trivial

abbrev Step2T : Type := SailM Unit × RegFile × Ibch × Nat × Eitem

/-- The driver's one node, with fence and RMW arms, recording the emitted item. -/
noncomputable def nodeStep2 (img : Image) (row : List Lbl) (m : SailM Unit) (rs : RegFile)
    (ib : Ibch) (k : Nat) : Option Step2T :=
  match m with
  | .pure _ => some (riscvStep false, rs, ibNone, k, (LInstr, none))
  | .impure (.error _) _ => none
  | .impure (.ok o) kk =>
    match o, kk with
    | .regRead r, kk => some (kk (rs r), rs, ibRd ib r, k, (LSilent, none))
    | .regWrite r v, kk =>
      some (kk PUnit.unit, rs.set r v, ib, k,
        (erwLabel (erwOf (depsOfIb ib.ibBits) ib.ibRds r), none))
    | .memRead n _ req, kk =>
      if devAddr req.pa then none else
      if (classify req.access_kind).akIfetch then
        match AxEpiRun.imgRead img (paZ req.pa) n with
        | some vs =>
          some (kk (.Ok (wordOfBytes n vs, none)), rs, ib, k,
            (LIFetch (paZ req.pa) (tagVals vs), none))
        | none => none
      else
      match row[k]? with
      | some (.LLoad aq base _ vs) =>
        if (classify req.access_kind).akLatest then none else
        if (classify req.access_kind).akSync = aq ∧ paZ req.pa = base ∧ vs.length = n
        then some (kk (.Ok (wordOfBytes n vs, none)), rs, ib, k + 1,
          (rdLabel false false (classify req.access_kind).akSync (paZ req.pa) (tagVals vs)
            (rdAsrc false ib), some k))
        else none
      | some (.LRmw aq _ base _ rvs wvs _) =>
        if (classify req.access_kind).akLatest then
          if (classify req.access_kind).akSync = aq ∧ paZ req.pa = base ∧ rvs.length = n ∧
              wvs.length = n
          then some (kk (.Ok (wordOfBytes n rvs, none)), rs, ib, k,
            (rdLabel false true (classify req.access_kind).akSync (paZ req.pa) (tagVals rvs)
              (rdAsrc true ib), some k))
          else none
        else none
      | _ => none
    | .memWrite n _ req, kk =>
      if devAddr req.pa then none else
      if n = 0 then none else
      match req.value with
      | none => none
      | some v =>
        match row[k]? with
        | some (.LStore rl base vs _) =>
          if (classify req.access_kind).akLatest then none else
          if (classify req.access_kind).akSync = rl ∧ paZ req.pa = base ∧
              WeakInterpProj.wbytes n v = vs
          then some (kk (.Ok (some true)), rs, ib, k + 1,
            (Wlabel.LStore (classify req.access_kind).akSync (paZ req.pa)
              (WeakInterpProj.wbytes n v) (depsAsrc (depsOfIb ib.ibBits))
              (depsVsrc (depsOfIb ib.ibBits)), some k))
          else none
        | some (.LRmw _ rl base _ _ wvs _) =>
          if (classify req.access_kind).akLatest then
            if (classify req.access_kind).akSync = rl ∧ paZ req.pa = base ∧
                WeakInterpProj.wbytes n v = wvs
            then some (kk (.Ok (some true)), rs, ib, k + 1,
              (LExStore (classify req.access_kind).akSync (paZ req.pa)
                (WeakInterpProj.wbytes n v) (depsAsrc (depsOfIb ib.ibBits))
                (depsVsrc (depsOfIb ib.ibBits)), some k))
            else none
          else none
        | _ => none
    | .barrier b, kk =>
      match ebarPark b with
      | some _ => none
      | none =>
        match row[k]? with
        | some (.LFence pr pw sr sw) =>
          if ebarBits b = (pr, pw, sr, sw)
          then some (kk (), rs, ib, k + 1, (ebarLabel b, some k)) else none
        | _ => none
    | .instrAnnounce n w, kk =>
      if sfAnnB n w then none else some (kk (), rs, ibAnn (ibOfBvn w), k, (LInstr, none))
    | .branchAnnounce _ _, kk => some (kk (), rs, ib, k, (LSilent, none))
    | .cacheOp _, kk => some (kk (), rs, ib, k, (LSilent, none))
    | .tlbi _, kk => some (kk (), rs, ib, k, (LSilent, none))
    | .takeException _, kk => some (kk (), rs, ib, k, (LSilent, none))
    | .returnException _, kk => some (kk (), rs, ib, k, (LSilent, none))
    | .translationStart _, kk => some (kk (), rs, ib, k, (LSilent, none))
    | .translationEnd _, kk => some (kk (), rs, ib, k, (LSilent, none))
    | .cycleCount, kk => some (kk (), rs, ib, k, (LSilent, none))
    | .message _, kk => some (kk (), rs, ib, k, (LSilent, none))
    | .getCycleCount, kk => some (kk (0 : Nat), rs, ib, k, (LSilent, none))
    | _, _ => none

/-- Iterate to the row position `kend`; the recorded emission, in order. -/
noncomputable def drive2 (img : Image) (row : List Lbl) (kend : Nat) :
    Nat → SailM Unit → RegFile → Ibch → Nat →
      Option (SailM Unit × RegFile × Ibch × Nat × List Eitem)
  | fuel, m, rs, ib, k =>
    if k = kend then some (m, rs, ib, k, []) else
    match fuel with
    | 0 => none
    | f + 1 =>
      match nodeStep2 img row m rs ib k with
      | some (m1, rs1, ib1, k1, it) =>
        match drive2 img row kend f m1 rs1 ib1 k1 with
        | some (m', rs', ib', k', its) => some (m', rs', ib', k', it :: its)
        | none => none
      | none => none

/-! # 2. Soundness for `astepAnyNfGv` -/

section sound
variable (GD : Gdexec) (i : Agent)

theorem nfFence (cpu : CPU) (b : barrier_kind) (KK : Unit → SailM Unit) (rs : RegFile)
    (ib : Ibch) (k : Nat) (pr pw sr sw : Bool) :
    (AxOpsem.grow GD i)[k]? = some (.LFence pr pw sr sw) →
    ebarPark b = none → ebarBits b = (pr, pw, sr, sw) →
    astepAnyNfGv GD i (AxEpiRun.st cpu (.impure (.ok (.barrier b)) KK) rs ib k)
      (AxEpiRun.st cpu (KK ()) rs ib (k + 1)) := by
  intro Hlb Hpark Hbits
  refine .ANFGVProg _ _ ⟨ebarLabel b, .AStepFence _ _ OpaxWit.wtD0 _ _ _ OpaxWit.wtD0 Hlb
    ?_ ?_ ?_, AxScRun2.fetchPinEbar _ b⟩
  · rw [AxScRun2.ebarWlFence]; rfl
  · rw [AxScRun2.ebarWlFence, Hbits]; rfl
  · exact ⟨rfl, none, none, some b, rfl, rfl, ⟨rfl, rfl, rfl, Hpark.symm, rfl, rfl, rfl⟩, rfl⟩

theorem nfRmwRead (cpu : CPU) (n va : Nat)
    (req : Mem_read_request n va Arch.pa Arch.translation Arch.arch_ak)
    (KK : Result (BitVec (8 * n) × Option Bool) Arch.abort → SailM Unit) (rs : RegFile)
    (ib : Ibch) (k : Nat) (aq rl : Bool) (base : Int) (ts : List Nat)
    (rvs wvs : List (BitVec 8)) (c : WmClass) :
    (AxOpsem.grow GD i)[k]? = some (.LRmw aq rl base ts rvs wvs c) →
    devAddr req.pa = false →
    (classify req.access_kind).akIfetch = false →
    (classify req.access_kind).akLatest = true →
    (classify req.access_kind).akSync = aq →
    paZ req.pa = base →
    rvs.length = n → wvs.length = n →
    astepAnyNfGv GD i (AxEpiRun.st cpu (.impure (.ok (.memRead n va req)) KK) rs ib k)
      (AxEpiRun.st cpu (KK (.Ok (wordOfBytes n rvs, none))) rs ib k) := by
  intro Hlb Hdev Hfe Hlat Hsync Hpa Hlr Hlw
  refine astepAnyNfGv.ANFGVRead _ (.IRmw aq rl base wvs.length)
    (fun vs' => AxEpiRun.st cpu (KK (.Ok (wordOfBytes n vs', none))) rs ib k) rvs
    ⟨_, Hlb, rfl, rfl, ?_⟩ ?_ (Hlr.trans Hlw.symm)
  · intro vs' Hvs'
    have h := pnodeStepReadAny n va req KK rs ib OpaxWit.wtD0.efDev vs' Hdev
      (by rw [Hvs', ← Hlw]; rfl)
    rw [Hfe, Hlat, Hsync, Hpa] at h
    refine ⟨rdLabel false true aq base (tagVals vs') (rdAsrc true ib), OpaxWit.wtD0,
      OpaxWit.wtD0, ?_, ?_, ⟨rfl, none, none, none, rfl, rfl, h, rfl⟩, rfl⟩
    · simp only [rdLabel, wlRd, aidentRd, tagValsLength, Bool.false_eq_true, ↓reduceIte]
      rw [Hvs']; rfl
    · rw [rdLabelRvals _ _ _ _ _ _ rfl, tagValsSnd]
  · show (gxLbl GD.gdG (i, k)).bind lblValue = some rvs
    rw [growGxLbl GD i k _ Hlb]
    rfl

theorem nfRmwWrite (cpu : CPU) (n va : Nat)
    (req : Mem_write_request n va Arch.pa Arch.translation Arch.arch_ak)
    (KK : Result (Option Bool) Arch.abort → SailM Unit) (rs : RegFile) (ib : Ibch) (k : Nat)
    (aq rl : Bool) (base : Int) (ts : List Nat) (rvs wvs : List (BitVec 8)) (c : WmClass)
    (v : BitVec (8 * n)) :
    (AxOpsem.grow GD i)[k]? = some (.LRmw aq rl base ts rvs wvs c) →
    devAddr req.pa = false → n ≠ 0 →
    (classify req.access_kind).akLatest = true →
    (classify req.access_kind).akSync = rl →
    paZ req.pa = base →
    req.value = some v →
    WeakInterpProj.wbytes n v = wvs →
    astepAnyNfGv GD i (AxEpiRun.st cpu (.impure (.ok (.memWrite n va req)) KK) rs ib k)
      (AxEpiRun.st cpu (KK (.Ok (some true))) rs ib (k + 1)) := by
  intro Hlb Hdev Hn Hlat Hsync Hpa Hval Hvs
  subst Hsync Hpa Hvs
  refine .ANFGVProg _ _ ⟨LExStore (classify req.access_kind).akSync (paZ req.pa)
      (WeakInterpProj.wbytes n v) (depsAsrc (depsOfIb ib.ibBits)) (depsVsrc (depsOfIb ib.ibBits)),
    .AStepWrite _ _ OpaxWit.wtD0 _ _ _ OpaxWit.wtD0 Hlb rfl rfl rfl ?_, trivial⟩
  refine ⟨rfl, none, none, none, rfl, rfl, ?_, rfl⟩
  simp only [pstepNode, pnodeStep, Hdev, Hval, Bool.false_eq_true, ↓reduceIte]
  refine ⟨Hn, Or.inr ⟨Hlat, Or.inl ?_⟩⟩
  simp

theorem nodeStep2Sound (cpu : CPU) (m : SailM Unit) (rs : RegFile) (ib : Ibch) (k : Nat)
    (m' : SailM Unit) (rs' : RegFile) (ib' : Ibch) (k' : Nat) (it : Eitem) :
    nodeStep2 GD.gdG.gxImg (AxOpsem.grow GD i) m rs ib k = some (m', rs', ib', k', it) →
    astepAnyNfGv GD i (AxEpiRun.st cpu m rs ib k) (AxEpiRun.st cpu m' rs' ib' k') := by
  intro Hs
  cases m with
  | pure y =>
    simp only [nodeStep2, Option.some.injEq, Prod.mk.injEq] at Hs
    obtain ⟨rfl, rfl, rfl, rfl, -⟩ := Hs
    exact nfAdmin GD i cpu _ rs ib k LInstr _ none (some ibNone) none rs ibNone
      ⟨false, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl trivial rfl rfl
  | impure c kk =>
    cases c with
    | error e => simp only [nodeStep2, reduceCtorEq] at Hs
    | ok o =>
      cases o
      case regRead r =>
        simp only [nodeStep2, Option.some.injEq, Prod.mk.injEq] at Hs
        obtain ⟨rfl, rfl, rfl, rfl, -⟩ := Hs
        exact nfAdmin GD i cpu _ rs ib k LSilent _ none (some (ibRd ib r)) none rs _
          ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ trivial trivial rfl rfl
      case regWrite r v =>
        simp only [nodeStep2, Option.some.injEq, Prod.mk.injEq] at Hs
        obtain ⟨rfl, rfl, rfl, rfl, -⟩ := Hs
        exact nfAdmin GD i cpu _ rs ib k _ _ (some (rs.set r v)) none none _ ib
          ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ (AxEpiRun.lbAdminErw _) (by
            cases erwOf (depsOfIb ib.ibBits) ib.ibRds r <;> trivial) rfl rfl
      case memRead n va req =>
        simp only [nodeStep2] at Hs
        cases Hdev : devAddr req.pa
        · simp only [Hdev, Bool.false_eq_true, ↓reduceIte] at Hs
          cases Hfe : (classify req.access_kind).akIfetch
          · simp only [Hfe, Bool.false_eq_true, ↓reduceIte] at Hs
            cases Hlb : (AxOpsem.grow GD i)[k]? with
            | none => simp only [Hlb, reduceCtorEq] at Hs
            | some lb =>
              cases lb with
              | LLoad aq base sv vs =>
                simp only [Hlb] at Hs
                cases Hlat : (classify req.access_kind).akLatest
                · simp only [Hlat, Bool.false_eq_true, ↓reduceIte] at Hs
                  split at Hs
                  · rename_i Hc
                    obtain ⟨Hsync, Hpa, Hlen⟩ := Hc
                    simp only [Option.some.injEq, Prod.mk.injEq] at Hs
                    obtain ⟨rfl, rfl, rfl, rfl, -⟩ := Hs
                    exact nfRead GD i cpu n va req kk rs ib k aq base sv vs Hlb Hdev Hfe Hlat
                      Hsync Hpa Hlen
                  · exact absurd Hs (by simp)
                · simp only [Hlat, ↓reduceIte, reduceCtorEq] at Hs
              | LRmw aq rl base sv rvs wvs c =>
                simp only [Hlb] at Hs
                cases Hlat : (classify req.access_kind).akLatest
                · simp only [Hlat, Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at Hs
                · simp only [Hlat, ↓reduceIte] at Hs
                  split at Hs
                  · rename_i Hc
                    obtain ⟨Hsync, Hpa, Hlr, Hlw⟩ := Hc
                    simp only [Option.some.injEq, Prod.mk.injEq] at Hs
                    obtain ⟨rfl, rfl, rfl, rfl, -⟩ := Hs
                    exact nfRmwRead GD i cpu n va req kk rs ib k aq rl base sv rvs wvs c Hlb Hdev
                      Hfe Hlat Hsync Hpa Hlr Hlw
                  · exact absurd Hs (by simp)
              | _ => simp only [Hlb, reduceCtorEq] at Hs
          · -- THE FETCH (deviation 1): an admin step, pinned by the image
            simp only [Hfe, ↓reduceIte] at Hs
            cases Hr : AxEpiRun.imgRead GD.gdG.gxImg (paZ req.pa) n with
            | none => simp only [Hr, reduceCtorEq] at Hs
            | some vs =>
              simp only [Hr, Option.some.injEq, Prod.mk.injEq] at Hs
              obtain ⟨rfl, rfl, rfl, rfl, -⟩ := Hs
              obtain ⟨Hlen, Himg⟩ := AxEpiRun.imgReadSpec _ n _ vs Hr
              have h := pnodeStepReadAny n va req kk rs ib OpaxWit.wtD0.efDev vs Hdev Hlen
              rw [Hfe] at h
              simp only [rdLabel, ↓reduceIte] at h
              refine nfAdmin GD i cpu _ rs ib k _ _ none none none rs ib h rfl ⟨?_, ?_⟩
                rfl rfl
              · intro t ht
                simp only [tagVals, List.map_map, List.mem_map] at ht
                obtain ⟨_, _, rfl⟩ := ht
                rfl
              · intro j hj
                rw [tagValsSnd]
                rw [tagValsLength] at hj
                exact Himg j hj
        · simp only [Hdev, ↓reduceIte, reduceCtorEq] at Hs
      case memWrite n va req =>
        simp only [nodeStep2] at Hs
        cases Hdev : devAddr req.pa
        · simp only [Hdev, Bool.false_eq_true, ↓reduceIte] at Hs
          by_cases Hn : n = 0
          · simp only [Hn, ↓reduceIte, reduceCtorEq] at Hs
          · simp only [Hn, ↓reduceIte] at Hs
            cases Hval : req.value with
            | none => simp only [Hval, reduceCtorEq] at Hs
            | some v =>
              cases Hlb : (AxOpsem.grow GD i)[k]? with
              | none => simp only [Hval, Hlb, reduceCtorEq] at Hs
              | some lb =>
                cases lb with
                | LStore rl base vs sv =>
                  simp only [Hval, Hlb] at Hs
                  cases Hlat : (classify req.access_kind).akLatest
                  · simp only [Hlat, Bool.false_eq_true, ↓reduceIte] at Hs
                    split at Hs
                    · rename_i Hc
                      obtain ⟨Hsync, Hpa, Hvs⟩ := Hc
                      simp only [Option.some.injEq, Prod.mk.injEq] at Hs
                      obtain ⟨rfl, rfl, rfl, rfl, -⟩ := Hs
                      exact nfWrite GD i cpu n va req kk rs ib k rl base vs sv v Hlb Hdev Hn
                        Hlat Hsync Hpa Hval Hvs
                    · exact absurd Hs (by simp)
                  · simp only [Hlat, ↓reduceIte, reduceCtorEq] at Hs
                | LRmw aq rl base sv rvs wvs c =>
                  simp only [Hval, Hlb] at Hs
                  cases Hlat : (classify req.access_kind).akLatest
                  · simp only [Hlat, Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at Hs
                  · simp only [Hlat, ↓reduceIte] at Hs
                    split at Hs
                    · rename_i Hc
                      obtain ⟨Hsync, Hpa, Hvs⟩ := Hc
                      simp only [Option.some.injEq, Prod.mk.injEq] at Hs
                      obtain ⟨rfl, rfl, rfl, rfl, -⟩ := Hs
                      exact nfRmwWrite GD i cpu n va req kk rs ib k aq rl base sv rvs wvs c v Hlb
                        Hdev Hn Hlat Hsync Hpa Hval Hvs
                    · exact absurd Hs (by simp)
                | _ => simp only [Hval, Hlb, reduceCtorEq] at Hs
        · simp only [Hdev, ↓reduceIte, reduceCtorEq] at Hs
      case barrier b =>
        simp only [nodeStep2] at Hs
        cases Hpark : ebarPark b with
        | some _ => simp only [Hpark, reduceCtorEq] at Hs
        | none =>
          cases Hlb : (AxOpsem.grow GD i)[k]? with
          | none => simp only [Hpark, Hlb, reduceCtorEq] at Hs
          | some lb =>
            cases lb with
            | LFence pr pw sr sw =>
              simp only [Hpark, Hlb] at Hs
              split at Hs
              · rename_i Hc
                simp only [Option.some.injEq, Prod.mk.injEq] at Hs
                obtain ⟨rfl, rfl, rfl, rfl, -⟩ := Hs
                exact nfFence GD i cpu b kk rs ib k pr pw sr sw Hlb Hpark Hc
              · exact absurd Hs (by simp)
            | _ => simp only [Hpark, Hlb, reduceCtorEq] at Hs
      case instrAnnounce n w =>
        simp only [nodeStep2] at Hs
        cases Hsf : sfAnnB n w
        · simp only [Hsf, Bool.false_eq_true, ↓reduceIte, Option.some.injEq,
            Prod.mk.injEq] at Hs
          obtain ⟨rfl, rfl, rfl, rfl, -⟩ := Hs
          refine nfAdmin GD i cpu _ rs ib k LInstr _ none (some (ibAnn (ibOfBvn w))) none rs _
            ⟨(annLabelNot Hsf).symm, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl trivial rfl rfl
        · simp only [Hsf, ↓reduceIte, reduceCtorEq] at Hs
      all_goals first
        | (simp only [nodeStep2, reduceCtorEq] at Hs; done)
        | (simp only [nodeStep2, Option.some.injEq, Prod.mk.injEq] at Hs
           obtain ⟨rfl, rfl, rfl, rfl, -⟩ := Hs
           exact nfAdmin GD i cpu _ rs ib k LSilent _ none none none rs ib
             ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ trivial trivial rfl rfl)

end sound

theorem drive2Sound (GD : Gdexec) (i : Agent) (kend fuel : Nat) :
    ∀ (m : SailM Unit) (rs : RegFile) (ib : Ibch) (k : Nat) (m' : SailM Unit) (rs' : RegFile)
      (ib' : Ibch) (k' : Nat) (its : List Eitem),
      drive2 GD.gdG.gxImg (AxOpsem.grow GD i) kend fuel m rs ib k =
        some (m', rs', ib', k', its) →
      k' = kend ∧
      ∃ n, ∀ cpu : CPU,
        nsteps (astepAnyNfGv GD i) n (AxEpiRun.st cpu m rs ib k)
          (AxEpiRun.st cpu m' rs' ib' k') := by
  induction fuel with
  | zero =>
    intro m rs ib k m' rs' ib' k' its Hd
    unfold drive2 at Hd
    split at Hd
    · rename_i hk
      simp only [Option.some.injEq, Prod.mk.injEq] at Hd
      obtain ⟨rfl, rfl, rfl, rfl, -⟩ := Hd
      exact ⟨hk, 0, fun _ => nsteps_O _⟩
    · simp only [reduceCtorEq] at Hd
  | succ f ih =>
    intro m rs ib k m' rs' ib' k' its Hd
    unfold drive2 at Hd
    split at Hd
    · rename_i hk
      simp only [Option.some.injEq, Prod.mk.injEq] at Hd
      obtain ⟨rfl, rfl, rfl, rfl, -⟩ := Hd
      exact ⟨hk, 0, fun _ => nsteps_O _⟩
    · simp only at Hd
      cases Hn : nodeStep2 GD.gdG.gxImg (AxOpsem.grow GD i) m rs ib k with
      | none => simp only [Hn, reduceCtorEq] at Hd
      | some r =>
        obtain ⟨m1, rs1, ib1, k1, it⟩ := r
        simp only [Hn] at Hd
        cases Hd2 : drive2 GD.gdG.gxImg (AxOpsem.grow GD i) kend f m1 rs1 ib1 k1 with
        | none => simp only [Hd2, reduceCtorEq] at Hd
        | some r2 =>
          obtain ⟨m2, rs2, ib2, k2, its2⟩ := r2
          simp only [Hd2, Option.some.injEq, Prod.mk.injEq] at Hd
          obtain ⟨rfl, rfl, rfl, rfl, -⟩ := Hd
          obtain ⟨Hk, n, Hr⟩ := ih m1 rs1 ib1 k1 m2 rs2 ib2 k2 its2 Hd2
          exact ⟨Hk, n + 1, fun cpu =>
            nsteps_l (nodeStep2Sound GD i cpu m rs ib k m1 rs1 ib1 k1 it Hn) (Hr cpu)⟩

/-! # 3. The recorded emission is the run's label sequence -/

theorem AxScRun2.pstepOfNode (cpu : CPU) (m : SailM Unit) (rs : RegFile) (ib : Ibch)
    (l : Wlabel) (m' : SailM Unit) (ors : Option RegFile) (oib : Option Ibch)
    (obar : Option barrier_kind) :
    pnodeStep m rs ib OpaxWit.wtD0.efDev l m' ors none OpaxWit.wtD0.efDev oib obar →
    pstepProg (.PHart cpu m rs none ib) OpaxWit.wtD0 l
      (.PHart cpu m' (ors.getD rs) none (oib.getD ib)) OpaxWit.wtD0 :=
  fun h => ⟨rfl, ors, oib, obar, rfl, rfl, h, rfl⟩

theorem nodeStep2Label (cpu : CPU) (img : Image) (row : List Lbl) (m : SailM Unit)
    (rs : RegFile) (ib : Ibch) (k : Nat) (m' : SailM Unit) (rs' : RegFile) (ib' : Ibch)
    (k' : Nat) (it : Eitem) :
    nodeStep2 img row m rs ib k = some (m', rs', ib', k', it) →
    pstepProg (.PHart cpu m rs none ib) OpaxWit.wtD0 it.1 (.PHart cpu m' rs' none ib')
      OpaxWit.wtD0 := by
  intro Hs
  cases m with
  | pure y =>
    simp only [nodeStep2, Option.some.injEq, Prod.mk.injEq] at Hs
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := Hs
    exact AxScRun2.pstepOfNode cpu _ rs ib LInstr _ none (some ibNone) none
      ⟨false, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  | impure c kk =>
    cases c with
    | error e => simp only [nodeStep2, reduceCtorEq] at Hs
    | ok o =>
      cases o
      case regRead r =>
        simp only [nodeStep2, Option.some.injEq, Prod.mk.injEq] at Hs
        obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := Hs
        exact AxScRun2.pstepOfNode cpu _ rs ib LSilent _ none (some (ibRd ib r)) none
          ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      case regWrite r v =>
        simp only [nodeStep2, Option.some.injEq, Prod.mk.injEq] at Hs
        obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := Hs
        exact AxScRun2.pstepOfNode cpu _ rs ib _ _ (some (rs.set r v)) none none
          ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      case memRead n va req =>
        simp only [nodeStep2] at Hs
        cases Hdev : devAddr req.pa
        · simp only [Hdev, Bool.false_eq_true, ↓reduceIte] at Hs
          cases Hfe : (classify req.access_kind).akIfetch
          · simp only [Hfe, Bool.false_eq_true, ↓reduceIte] at Hs
            cases Hlb : row[k]? with
            | none => simp only [Hlb, reduceCtorEq] at Hs
            | some lb =>
              cases lb with
              | LLoad aq base sv vs =>
                simp only [Hlb] at Hs
                cases Hlat : (classify req.access_kind).akLatest
                · simp only [Hlat, Bool.false_eq_true, ↓reduceIte] at Hs
                  split at Hs
                  · rename_i Hc
                    obtain ⟨_, _, Hlen⟩ := Hc
                    simp only [Option.some.injEq, Prod.mk.injEq] at Hs
                    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := Hs
                    have h := pnodeStepReadAny n va req kk rs ib OpaxWit.wtD0.efDev vs Hdev Hlen
                    rw [Hfe, Hlat] at h
                    exact AxScRun2.pstepOfNode cpu _ rs ib _ _ none none none h
                  · exact absurd Hs (by simp)
                · simp only [Hlat, ↓reduceIte, reduceCtorEq] at Hs
              | LRmw aq rl base sv rvs wvs c =>
                simp only [Hlb] at Hs
                cases Hlat : (classify req.access_kind).akLatest
                · simp only [Hlat, Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at Hs
                · simp only [Hlat, ↓reduceIte] at Hs
                  split at Hs
                  · rename_i Hc
                    obtain ⟨_, _, Hlr, _⟩ := Hc
                    simp only [Option.some.injEq, Prod.mk.injEq] at Hs
                    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := Hs
                    have h := pnodeStepReadAny n va req kk rs ib OpaxWit.wtD0.efDev rvs Hdev Hlr
                    rw [Hfe, Hlat] at h
                    exact AxScRun2.pstepOfNode cpu _ rs ib _ _ none none none h
                  · exact absurd Hs (by simp)
              | _ => simp only [Hlb, reduceCtorEq] at Hs
          · simp only [Hfe, ↓reduceIte] at Hs
            cases Hr : AxEpiRun.imgRead img (paZ req.pa) n with
            | none => simp only [Hr, reduceCtorEq] at Hs
            | some vs =>
              simp only [Hr, Option.some.injEq, Prod.mk.injEq] at Hs
              obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := Hs
              obtain ⟨Hlen, -⟩ := AxEpiRun.imgReadSpec _ n _ vs Hr
              have h := pnodeStepReadAny n va req kk rs ib OpaxWit.wtD0.efDev vs Hdev Hlen
              rw [Hfe] at h
              simp only [rdLabel, ↓reduceIte] at h
              exact AxScRun2.pstepOfNode cpu _ rs ib _ _ none none none h
        · simp only [Hdev, ↓reduceIte, reduceCtorEq] at Hs
      case memWrite n va req =>
        simp only [nodeStep2] at Hs
        cases Hdev : devAddr req.pa
        · simp only [Hdev, Bool.false_eq_true, ↓reduceIte] at Hs
          by_cases Hn : n = 0
          · simp only [Hn, ↓reduceIte, reduceCtorEq] at Hs
          · simp only [Hn, ↓reduceIte] at Hs
            cases Hval : req.value with
            | none => simp only [Hval, reduceCtorEq] at Hs
            | some v =>
              cases Hlb : row[k]? with
              | none => simp only [Hval, Hlb, reduceCtorEq] at Hs
              | some lb =>
                cases lb with
                | LStore rl base vs sv =>
                  simp only [Hval, Hlb] at Hs
                  cases Hlat : (classify req.access_kind).akLatest
                  · simp only [Hlat, Bool.false_eq_true, ↓reduceIte] at Hs
                    split at Hs
                    · simp only [Option.some.injEq, Prod.mk.injEq] at Hs
                      obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := Hs
                      refine AxScRun2.pstepOfNode cpu _ rs ib _ _ none none none ?_
                      simp only [pnodeStep, Hdev, Hval, Bool.false_eq_true, ↓reduceIte]
                      refine ⟨Hn, Or.inl ⟨Hlat, ?_⟩⟩
                      simp
                    · exact absurd Hs (by simp)
                  · simp only [Hlat, ↓reduceIte, reduceCtorEq] at Hs
                | LRmw aq rl base sv rvs wvs c =>
                  simp only [Hval, Hlb] at Hs
                  cases Hlat : (classify req.access_kind).akLatest
                  · simp only [Hlat, Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at Hs
                  · simp only [Hlat, ↓reduceIte] at Hs
                    split at Hs
                    · simp only [Option.some.injEq, Prod.mk.injEq] at Hs
                      obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := Hs
                      refine AxScRun2.pstepOfNode cpu _ rs ib _ _ none none none ?_
                      simp only [pnodeStep, Hdev, Hval, Bool.false_eq_true, ↓reduceIte]
                      refine ⟨Hn, Or.inr ⟨Hlat, Or.inl ?_⟩⟩
                      simp
                    · exact absurd Hs (by simp)
                | _ => simp only [Hval, Hlb, reduceCtorEq] at Hs
        · simp only [Hdev, ↓reduceIte, reduceCtorEq] at Hs
      case barrier b =>
        simp only [nodeStep2] at Hs
        cases Hpark : ebarPark b with
        | some _ => simp only [Hpark, reduceCtorEq] at Hs
        | none =>
          cases Hlb : row[k]? with
          | none => simp only [Hpark, Hlb, reduceCtorEq] at Hs
          | some lb =>
            cases lb with
            | LFence pr pw sr sw =>
              simp only [Hpark, Hlb] at Hs
              split at Hs
              · simp only [Option.some.injEq, Prod.mk.injEq] at Hs
                obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := Hs
                exact AxScRun2.pstepOfNode cpu _ rs ib _ _ none none (some b)
                  ⟨rfl, rfl, rfl, Hpark.symm, rfl, rfl, rfl⟩
              · exact absurd Hs (by simp)
            | _ => simp only [Hpark, Hlb, reduceCtorEq] at Hs
      case instrAnnounce n w =>
        simp only [nodeStep2] at Hs
        cases Hsf : sfAnnB n w
        · simp only [Hsf, Bool.false_eq_true, ↓reduceIte, Option.some.injEq,
            Prod.mk.injEq] at Hs
          obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := Hs
          exact AxScRun2.pstepOfNode cpu _ rs ib LInstr _ none (some (ibAnn (ibOfBvn w))) none
            ⟨(annLabelNot Hsf).symm, rfl, rfl, rfl, rfl, rfl, rfl⟩
        · simp only [Hsf, ↓reduceIte, reduceCtorEq] at Hs
      all_goals first
        | (simp only [nodeStep2, reduceCtorEq] at Hs; done)
        | (simp only [nodeStep2, Option.some.injEq, Prod.mk.injEq] at Hs
           obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := Hs
           exact AxScRun2.pstepOfNode cpu _ rs ib LSilent _ none none none
             ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩)

/-! # 4. The driver ignores read timestamps -/

theorem nodeStep2Erase (img : Image) (row : List Lbl) (m : SailM Unit) (rs : RegFile)
    (ib : Ibch) (k : Nat) :
    nodeStep2 img row m rs ib k = nodeStep2 img (row.map erase) m rs ib k := by
  cases m with
  | pure _ => rfl
  | impure c kk =>
    cases c with
    | error _ => rfl
    | ok o =>
      cases o <;> (try rfl) <;>
        (simp only [nodeStep2, List.getElem?_map]
         cases row[k]? with
         | none => rfl
         | some lb => cases lb <;> rfl)

theorem drive2Erase1 (img : Image) (row : List Lbl) (kend fuel : Nat) :
    ∀ (m : SailM Unit) (rs : RegFile) (ib : Ibch) (k : Nat),
      drive2 img row kend fuel m rs ib k = drive2 img (row.map erase) kend fuel m rs ib k := by
  induction fuel with
  | zero => intro m rs ib k; unfold drive2; rfl
  | succ f ih =>
    intro m rs ib k
    unfold drive2
    rw [← nodeStep2Erase]
    cases nodeStep2 img row m rs ib k with
    | none => rfl
    | some r =>
      obtain ⟨m1, rs1, ib1, k1, it⟩ := r
      simp only [ih]

theorem drive2Erase (img : Image) (row row' : List Lbl) (kend fuel : Nat) (m : SailM Unit)
    (rs : RegFile) (ib : Ibch) (k : Nat) :
    row.map erase = row'.map erase →
    drive2 img row kend fuel m rs ib k = drive2 img row' kend fuel m rs ib k := by
  intro H
  rw [drive2Erase1, H, ← drive2Erase1]

/-! # 5. The RUN premise at a `graphOfSc` graph -/

/-- (a) Driven on the GRAPH's own row: the tier-A run premise, in the form
`AxSpinGate.tierAAdequacyAnnGateT`'s `Hrun` takes it (`GD := gtAdGd GT`). -/
theorem runGraphOfSc (img : Int → BitVec 8) (rows : List (List Lbl)) (il : List Geid)
    (ems : List (List Eitem)) (i : Agent) (kend fuel : Nat) (m : SailM Unit) (rs : RegFile)
    (ib : Ibch) (m' : SailM Unit) (rs' : RegFile) (ib' : Ibch) (k' : Nat) (its : List Eitem) :
    drive2 (fun a => some (img a)) (rowOf (graphOfSc img rows il ems).gtG i) kend fuel m rs ib 0 =
      some (m', rs', ib', k', its) →
    k' = kend ∧
    ∃ n, ∀ (cpu : CPU) (N : Type) (nm : N),
      nsteps (tierAAstep (gtAdGd (graphOfSc img rows il ems)) nm i) n
        (AxEpiRun.st cpu m rs ib 0) (AxEpiRun.st cpu m' rs' ib' k') := by
  intro Hd
  obtain ⟨Hk, n, Hr⟩ := drive2Sound (gtAdGd (graphOfSc img rows il ems)) i kend fuel
    _ _ _ _ _ _ _ _ _ Hd
  exact ⟨Hk, n, fun cpu _ _ => Hr cpu⟩

/-- (b) THE BRIDGE: driven on the INPUT row, whose read values are the SC values (`valsOkB`):
the same premise. -/
theorem runBridge (img : Int → BitVec 8) (rows : List (List Lbl)) (il : List Geid)
    (ems : List (List Eitem)) (i : Agent) (kend fuel : Nat) (m : SailM Unit) (rs : RegFile)
    (ib : Ibch) (m' : SailM Unit) (rs' : RegFile) (ib' : Ibch) (k' : Nat) (its : List Eitem) :
    valsOkB img rows il = true →
    drive2 (fun a => some (img a)) ((rows[i]?).getD []) kend fuel m rs ib 0 =
      some (m', rs', ib', k', its) →
    k' = kend ∧
    ∃ n, ∀ (cpu : CPU) (N : Type) (nm : N),
      nsteps (tierAAstep (gtAdGd (graphOfSc img rows il ems)) nm i) n
        (AxEpiRun.st cpu m rs ib 0) (AxEpiRun.st cpu m' rs' ib' k') := by
  intro Hv Hd
  refine runGraphOfSc img rows il ems i kend fuel m rs ib m' rs' ib' k' its ?_
  rw [drive2Erase _ _ ((rows[i]?).getD []) _ _ _ _ _ _ (graphOfScErase img rows il ems i Hv)]
  exact Hd

end Weak
