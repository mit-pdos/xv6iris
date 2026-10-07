/-
Weak: **the RUN premise of `AxEpiAdeq.epiReloadSound`, discharged at the concrete witness graph
`AxEpiSdLdSat.gsdld`**: the fully closed corollary `epiReloadSoundGsdld : graphValue gsdld (0, 1)
= some sdData` with NO remaining hypotheses — every premise of `epiReloadSound`, `Hrun`/`Hend`
included, is met by one concrete (graph, run) pair.

Rocq: `iris/AxEpiRun.v` @ xxvzwolszwmp.

## What this file proves

METHOD (as Rocq): a computable one-node DRIVER `nodeStep` over the Sail monad (the program half
`WeakEvInst.pnodeStep`, deterministic by construction: register reads answer from the register
file — the pins included, they are plain `LSilent` reads there; RAM reads take the ROW's own value
at the current position; RAM writes must match the row's store label byte for byte; the `.pure ()`
boundary continues with `riscvStep false`, i.e. the run chooses `tick := false`), proved SOUND for
`astepAnyNfGv` (`nodeStepSound`: admin nodes via `ANFGVProg`/`AStepAdmin`, writes via
`ANFGVProg`/`AStepWrite`, data reads via `ANFGVRead` at `graphValue`), iterated by `drive` until
the row position reaches its end (`driveSound`).  The concrete run is then a single kernel
evaluation of `drive` from `probeRegs pcSd` (`driveGsdldOk`).

## Deviations from Rocq

1. O2 STAGE C (fetches are not graph events; `AxEpiSdLdSat`/`AxEpiAdeq` deviation 1): Rocq's
   driver answered the two instruction fetches from the ROW (text `LLoad`s, via `ANFGVRead`).  In
   Lean an `akIfetch` read is an ADMIN step (`lbAdmin true (LIFetch ..)`), and `astepProgNf`
   carries the boot-image pin `WeakAxRealize.fetchPin GD.gdG.gxImg l`.  So `nodeStep`/`drive`
   take the image `img` (first argument) and answer a fetch of `n` bytes at `paZ pa` with the
   image bytes at timestamp 0 (`AxEpiRun.imgRead`; stuck if any byte is unmapped), position
   unchanged; `nodeStepSound`/`driveSound` are stated at `img := GD.gdG.gxImg`.  Data reads keep
   Rocq's `ak_coh = false` test as `akIfetch = false` (it is the else branch of the fetch test).
   `nfAdmin` takes the extra premise `fetchPin GD.gdG.gxImg l`.  The `gsdld` run ends at row
   position 2 (Rocq 4): `driveGsdld` has `kend := 2`, `driveGsdldB` tests `k == 2`.
2. Q7 (sfence announce): an `instrAnnounce` at an SFENCE.VMA word is a graph event
   (`annLabel` = `LFence …`), not an admin step; `nodeStep` returns `none` there
   (`sfAnnB n w = true`).  Elsewhere the announce is `LInstr` as in Rocq.
3. TYPES: lean-sail write values are `Option`: `nodeStep` matches `req.value = some v` (none ↦
   `none`) and answers `.Ok (some true)` (Rocq `inl None`); reads answer `.Ok (w, none)` (Rocq
   `inl (w, None)`); `Interface.Ret` ↦ `.pure _`; the model-error outcome ↦ `none`.  `oib32` ↦
   `Ibch`, `ib_rd`/`ib_ann`/`ib_of_bvn`/`ib_none` ↦ `ibRd`/`ibAnn`/`ibOfBvn`/`ibNone`;
   `register_lookup r rs` ↦ `rs r`, `register_set r v rs` ↦ `rs.set r v`; `S k` ↦ `k + 1`;
   `vm_compute` ↦ `decide +kernel`.  The Lean `pnodeStep` carries `obar` (the barrier executed):
   `nfAdmin` takes it as an argument (`none` at every use).
4. INSTANCES: `astepAnyNfGv` (= `tierAAstep`) takes no `AxirisG` instance in Lean, so
   `driveSound` / `epiRunGsdld` quantify over `cpu` only (Rocq `∀ cpu Σ (HG : axirisG Σ)`); the
   section `HG` of `sound` is dropped.  `epiReloadSoundGsdld` meets `Hrun`'s `∀ Hann nm` trivially.
5. `nfWrite`'s data equation: Rocq `wbytes n (WriteReq.value req) = vs` ↦ `req.value = some v` and
   `WeakInterpProj.wbytes n v = vs`.
6. NAMES: Rocq `st` is file-qualified `AxEpiRun.st` (a bare global `st` in `namespace Weak` would
   capture far too many identifiers).  `grow_gx_lbl` is ported as `growGxLbl` though
   `AxWp.growLookup` states the same fact.

**Rocq → Lean name map.**  `st` `AxEpiRun.st`, `node_step` `nodeStep`, `drive` `drive`,
`grow_gx_lbl` `growGxLbl`, `nf_admin` `nfAdmin`, `nf_read` `nfRead`, `nf_write` `nfWrite`,
`node_step_sound` `nodeStepSound`, `drive_sound` `driveSound`, `run_fuel` `runFuel`,
`drive_gsdld` `driveGsdld`, `drive_gsdld_b` `driveGsdldB`, `drive_gsdld_ok` `driveGsdldOk`,
`epi_run_gsdld` `epiRunGsdld`, `epi_reload_sound_gsdld` `epiReloadSoundGsdld`.  None is in the
duplicated-name table.  Lean-only (file-qualified): `AxEpiRun.imgRead`, `AxEpiRun.imgReadSpec`,
`AxEpiRun.lbAdminErw`.

**Dropped:** nothing (Rocq 15 definitions/lemmas; Lean 15 + 3 Lean-only helpers).  **Not ported:**
the `Print Assumptions` line (the lint's axiom check covers it).
-/
import Weak.AxEpiAdeq

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open Sail Sail.ConcurrencyInterfaceV1
open Sail.ArchSem (FreeM)
open LeanRV64D
open Wlabel

/-! # 1. The driver -/

def AxEpiRun.st (cpu : CPU) (m : SailM Unit) (rs : RegFile) (ib : Ibch) (k : Nat) : Athread :=
  ⟨.PHart cpu m rs none ib, k⟩

/-- (Lean-only, deviation 1) The image bytes `[base, base + n)`, if all mapped. -/
def AxEpiRun.imgRead (img : Image) (base : Int) : Nat → Option (List (BitVec 8))
  | 0 => some []
  | n + 1 =>
    match img base, AxEpiRun.imgRead img (base + 1) n with
    | some b, some vs => some (b :: vs)
    | _, _ => none

theorem AxEpiRun.imgReadSpec (img : Image) (n : Nat) :
    ∀ (base : Int) (vs : List (BitVec 8)), AxEpiRun.imgRead img base n = some vs →
      vs.length = n ∧ ∀ j, j < vs.length → img (base + (j : Int)) = vs[j]? := by
  induction n with
  | zero =>
    intro base vs h
    simp only [AxEpiRun.imgRead, Option.some.injEq] at h
    subst h
    exact ⟨rfl, fun j hj => absurd hj (Nat.not_lt_zero j)⟩
  | succ n ih =>
    intro base vs h
    simp only [AxEpiRun.imgRead] at h
    cases hb : img base with
    | none => rw [hb] at h; exact absurd h (by simp)
    | some b =>
      cases hr : AxEpiRun.imgRead img (base + 1) n with
      | none => rw [hb, hr] at h; exact absurd h (by simp)
      | some vs' =>
        rw [hb, hr, Option.some.injEq] at h
        subst h
        obtain ⟨hl, hj⟩ := ih (base + 1) vs' hr
        refine ⟨by simp [hl], ?_⟩
        intro j hjl
        cases j with
        | zero => simp [hb]
        | succ j =>
          have hjl' : j < vs'.length := by simp at hjl; omega
          have := hj j hjl'
          rw [show base + ((j + 1 : Nat) : Int) = base + 1 + (j : Int) by omega, this]
          rfl

/-- The driver's one node (deviations 1–3). -/
noncomputable def nodeStep (img : Image) (row : List Lbl) (m : SailM Unit) (rs : RegFile)
    (ib : Ibch) (k : Nat) : Option (SailM Unit × RegFile × Ibch × Nat) :=
  match m with
  | .pure _ => some (riscvStep false, rs, ibNone, k)
  | .impure (.error _) _ => none
  | .impure (.ok o) kk =>
    match o, kk with
    | .regRead r, kk => some (kk (rs r), rs, ibRd ib r, k)
    | .regWrite r v, kk => some (kk PUnit.unit, rs.set r v, ib, k)
    | .memRead n _ req, kk =>
      if devAddr req.pa then none else
      if (classify req.access_kind).akIfetch then
        match AxEpiRun.imgRead img (paZ req.pa) n with
        | some vs => some (kk (.Ok (wordOfBytes n vs, none)), rs, ib, k)
        | none => none
      else
      if (classify req.access_kind).akLatest then none else
      match row[k]? with
      | some (.LLoad aq base _ vs) =>
        if (classify req.access_kind).akSync = aq ∧ paZ req.pa = base ∧ vs.length = n
        then some (kk (.Ok (wordOfBytes n vs, none)), rs, ib, k + 1) else none
      | _ => none
    | .memWrite n _ req, kk =>
      if devAddr req.pa then none else
      if n = 0 then none else
      if (classify req.access_kind).akLatest then none else
      match req.value, row[k]? with
      | some v, some (.LStore rl base vs _) =>
        if (classify req.access_kind).akSync = rl ∧ paZ req.pa = base ∧
            WeakInterpProj.wbytes n v = vs
        then some (kk (.Ok (some true)), rs, ib, k + 1) else none
      | _, _ => none
    | .instrAnnounce n w, kk =>
      if sfAnnB n w then none else some (kk (), rs, ibAnn (ibOfBvn w), k)
    | .branchAnnounce _ _, kk => some (kk (), rs, ib, k)
    | .cacheOp _, kk => some (kk (), rs, ib, k)
    | .tlbi _, kk => some (kk (), rs, ib, k)
    | .takeException _, kk => some (kk (), rs, ib, k)
    | .returnException _, kk => some (kk (), rs, ib, k)
    | .translationStart _, kk => some (kk (), rs, ib, k)
    | .translationEnd _, kk => some (kk (), rs, ib, k)
    | .cycleCount, kk => some (kk (), rs, ib, k)
    | .message _, kk => some (kk (), rs, ib, k)
    | .getCycleCount, kk => some (kk (0 : Nat), rs, ib, k)
    | _, _ => none

/-- Iterate `nodeStep` until the row position reaches `kend`. -/
noncomputable def drive (img : Image) (row : List Lbl) (kend : Nat) :
    Nat → SailM Unit → RegFile → Ibch → Nat → Option (SailM Unit × RegFile × Ibch × Nat)
  | fuel, m, rs, ib, k =>
    if k = kend then some (m, rs, ib, k) else
    match fuel with
    | 0 => none
    | f + 1 =>
      match nodeStep img row m rs ib k with
      | some (m1, rs1, ib1, k1) => drive img row kend f m1 rs1 ib1 k1
      | none => none

/-! # 2. Soundness for `astepAnyNfGv` -/

theorem growGxLbl (GD : Gdexec) (i k : Nat) (lb : Lbl) :
    (AxOpsem.grow GD i)[k]? = some lb → gxLbl GD.gdG (i, k) = some lb :=
  AxWp.growLookup GD i k lb

theorem AxEpiRun.lbAdminErw (w : ErwKind) : lbAdmin true (erwLabel w) := by
  cases w <;> trivial

section sound
variable (GD : Gdexec) (i : Agent)

theorem nfAdmin (cpu : CPU) (m : SailM Unit) (rs : RegFile) (ib : Ibch) (k : Nat) (l : Wlabel)
    (m' : SailM Unit) (ors : Option RegFile) (oib : Option Ibch) (obar : Option barrier_kind)
    (rs' : RegFile) (ib' : Ibch) :
    pnodeStep m rs ib OpaxWit.wtD0.efDev l m' ors none OpaxWit.wtD0.efDev oib obar →
    lbAdmin true l → WeakAxRealize.fetchPin GD.gdG.gxImg l →
    rs' = ors.getD rs → ib' = oib.getD ib →
    astepAnyNfGv GD i (AxEpiRun.st cpu m rs ib k) (AxEpiRun.st cpu m' rs' ib' k) := by
  intro Hn Hadm Hpin hrs hib
  subst hrs hib
  exact .ANFGVProg _ _ ⟨l, .AStepAdmin _ _ OpaxWit.wtD0 _ _ OpaxWit.wtD0 Hadm
    ⟨rfl, ors, oib, obar, rfl, rfl, Hn, rfl⟩, Hpin⟩

theorem nfRead (cpu : CPU) (n va : Nat)
    (req : Mem_read_request n va Arch.pa Arch.translation Arch.arch_ak)
    (KK : Result (BitVec (8 * n) × Option Bool) Arch.abort → SailM Unit) (rs : RegFile)
    (ib : Ibch) (k : Nat) (aq : Bool) (base : Int) (sv : List Nat) (vs : List (BitVec 8)) :
    (AxOpsem.grow GD i)[k]? = some (.LLoad aq base sv vs) →
    devAddr req.pa = false →
    (classify req.access_kind).akIfetch = false →
    (classify req.access_kind).akLatest = false →
    (classify req.access_kind).akSync = aq →
    paZ req.pa = base →
    vs.length = n →
    astepAnyNfGv GD i (AxEpiRun.st cpu (.impure (.ok (.memRead n va req)) KK) rs ib k)
      (AxEpiRun.st cpu (KK (.Ok (wordOfBytes n vs, none))) rs ib (k + 1)) := by
  intro Hlb Hdev Hfe Hlat Hsync Hpa Hlen
  refine astepAnyNfGv.ANFGVRead _ (.IRead aq base vs.length)
    (fun vs' => AxEpiRun.st cpu (KK (.Ok (wordOfBytes n vs', none))) rs ib (k + 1)) vs
    ⟨_, Hlb, rfl, rfl, ?_⟩ ?_ rfl
  · intro vs' Hvs'
    have h := pnodeStepReadAny n va req KK rs ib OpaxWit.wtD0.efDev vs' Hdev
      (by rw [Hvs', ← Hlen]; rfl)
    rw [Hfe, Hlat, Hsync, Hpa] at h
    refine ⟨rdLabel false false aq base (tagVals vs') (rdAsrc false ib), OpaxWit.wtD0,
      OpaxWit.wtD0, ?_, ?_, ⟨rfl, none, none, none, rfl, rfl, h, rfl⟩, rfl⟩
    · simp only [rdLabel, wlRd, aidentRd, tagValsLength, Bool.false_eq_true, ↓reduceIte]
      rw [Hvs']; rfl
    · rw [rdLabelRvals _ _ _ _ _ _ rfl, tagValsSnd]
  · show (gxLbl GD.gdG (i, k)).bind lblValue = some vs
    rw [growGxLbl GD i k _ Hlb]
    rfl

theorem nfWrite (cpu : CPU) (n va : Nat)
    (req : Mem_write_request n va Arch.pa Arch.translation Arch.arch_ak)
    (KK : Result (Option Bool) Arch.abort → SailM Unit) (rs : RegFile) (ib : Ibch) (k : Nat)
    (rl : Bool) (base : Int) (vs : List (BitVec 8)) (sv : WmClass) (v : BitVec (8 * n)) :
    (AxOpsem.grow GD i)[k]? = some (.LStore rl base vs sv) →
    devAddr req.pa = false → n ≠ 0 →
    (classify req.access_kind).akLatest = false →
    (classify req.access_kind).akSync = rl →
    paZ req.pa = base →
    req.value = some v →
    WeakInterpProj.wbytes n v = vs →
    astepAnyNfGv GD i (AxEpiRun.st cpu (.impure (.ok (.memWrite n va req)) KK) rs ib k)
      (AxEpiRun.st cpu (KK (.Ok (some true))) rs ib (k + 1)) := by
  intro Hlb Hdev Hn Hlat Hsync Hpa Hval Hvs
  subst Hsync Hpa Hvs
  refine .ANFGVProg _ _ ⟨LStore (classify req.access_kind).akSync (paZ req.pa)
      (WeakInterpProj.wbytes n v) (depsAsrc (depsOfIb ib.ibBits)) (depsVsrc (depsOfIb ib.ibBits)),
    .AStepWrite _ _ OpaxWit.wtD0 _ _ _ OpaxWit.wtD0 Hlb rfl rfl rfl ?_, trivial⟩
  refine ⟨rfl, none, none, none, rfl, rfl, ?_, rfl⟩
  simp only [pstepNode, pnodeStep, Hdev, Hval, Bool.false_eq_true, ↓reduceIte]
  refine ⟨Hn, Or.inl ⟨Hlat, ?_⟩⟩
  simp

theorem nodeStepSound (cpu : CPU) (m : SailM Unit) (rs : RegFile) (ib : Ibch) (k : Nat)
    (m' : SailM Unit) (rs' : RegFile) (ib' : Ibch) (k' : Nat) :
    nodeStep GD.gdG.gxImg (AxOpsem.grow GD i) m rs ib k = some (m', rs', ib', k') →
    astepAnyNfGv GD i (AxEpiRun.st cpu m rs ib k) (AxEpiRun.st cpu m' rs' ib' k') := by
  intro Hs
  cases m with
  | pure y =>
    simp only [nodeStep, Option.some.injEq, Prod.mk.injEq] at Hs
    obtain ⟨rfl, rfl, rfl, rfl⟩ := Hs
    exact nfAdmin GD i cpu _ rs ib k LInstr _ none (some ibNone) none rs ibNone
      ⟨false, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl trivial rfl rfl
  | impure c kk =>
    cases c with
    | error e => simp only [nodeStep, reduceCtorEq] at Hs
    | ok o =>
      cases o
      case regRead r =>
        simp only [nodeStep, Option.some.injEq, Prod.mk.injEq] at Hs
        obtain ⟨rfl, rfl, rfl, rfl⟩ := Hs
        exact nfAdmin GD i cpu _ rs ib k LSilent _ none (some (ibRd ib r)) none rs _
          ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ trivial trivial rfl rfl
      case regWrite r v =>
        simp only [nodeStep, Option.some.injEq, Prod.mk.injEq] at Hs
        obtain ⟨rfl, rfl, rfl, rfl⟩ := Hs
        exact nfAdmin GD i cpu _ rs ib k _ _ (some (rs.set r v)) none none _ ib
          ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ (AxEpiRun.lbAdminErw _) (by
            cases erwOf (depsOfIb ib.ibBits) ib.ibRds r <;> trivial) rfl rfl
      case memRead n va req =>
        simp only [nodeStep] at Hs
        cases Hdev : devAddr req.pa
        · simp only [Hdev, Bool.false_eq_true, ↓reduceIte] at Hs
          cases Hfe : (classify req.access_kind).akIfetch
          · simp only [Hfe, Bool.false_eq_true, ↓reduceIte] at Hs
            cases Hlat : (classify req.access_kind).akLatest
            · simp only [Hlat, Bool.false_eq_true, ↓reduceIte] at Hs
              cases Hlb : (AxOpsem.grow GD i)[k]? with
              | none => simp only [Hlb, reduceCtorEq] at Hs
              | some lb =>
                cases lb with
                | LLoad aq base sv vs =>
                  simp only [Hlb] at Hs
                  split at Hs
                  · rename_i Hc
                    obtain ⟨Hsync, Hpa, Hlen⟩ := Hc
                    simp only [Option.some.injEq, Prod.mk.injEq] at Hs
                    obtain ⟨rfl, rfl, rfl, rfl⟩ := Hs
                    exact nfRead GD i cpu n va req kk rs ib k aq base sv vs Hlb Hdev Hfe Hlat
                      Hsync Hpa Hlen
                  · exact absurd Hs (by simp)
                | _ => simp only [Hlb, reduceCtorEq] at Hs
            · simp only [Hlat, ↓reduceIte, reduceCtorEq] at Hs
          · -- THE FETCH (deviation 1): an admin step, pinned by the image
            simp only [Hfe, ↓reduceIte] at Hs
            cases Hr : AxEpiRun.imgRead GD.gdG.gxImg (paZ req.pa) n with
            | none => simp only [Hr, reduceCtorEq] at Hs
            | some vs =>
              simp only [Hr, Option.some.injEq, Prod.mk.injEq] at Hs
              obtain ⟨rfl, rfl, rfl, rfl⟩ := Hs
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
        simp only [nodeStep] at Hs
        cases Hdev : devAddr req.pa
        · simp only [Hdev, Bool.false_eq_true, ↓reduceIte] at Hs
          by_cases Hn : n = 0
          · simp only [Hn, ↓reduceIte, reduceCtorEq] at Hs
          · simp only [Hn, ↓reduceIte] at Hs
            cases Hlat : (classify req.access_kind).akLatest
            · simp only [Hlat, Bool.false_eq_true, ↓reduceIte] at Hs
              cases Hval : req.value with
              | none => simp only [Hval, reduceCtorEq] at Hs
              | some v =>
                cases Hlb : (AxOpsem.grow GD i)[k]? with
                | none => simp only [Hval, Hlb, reduceCtorEq] at Hs
                | some lb =>
                  cases lb with
                  | LStore rl base vs sv =>
                    simp only [Hval, Hlb] at Hs
                    split at Hs
                    · rename_i Hc
                      obtain ⟨Hsync, Hpa, Hvs⟩ := Hc
                      simp only [Option.some.injEq, Prod.mk.injEq] at Hs
                      obtain ⟨rfl, rfl, rfl, rfl⟩ := Hs
                      exact nfWrite GD i cpu n va req kk rs ib k rl base vs sv v Hlb Hdev Hn
                        Hlat Hsync Hpa Hval Hvs
                    · exact absurd Hs (by simp)
                  | _ => simp only [Hval, Hlb, reduceCtorEq] at Hs
            · simp only [Hlat, ↓reduceIte, reduceCtorEq] at Hs
        · simp only [Hdev, ↓reduceIte, reduceCtorEq] at Hs
      case instrAnnounce n w =>
        simp only [nodeStep] at Hs
        cases Hsf : sfAnnB n w
        · simp only [Hsf, Bool.false_eq_true, ↓reduceIte, Option.some.injEq,
            Prod.mk.injEq] at Hs
          obtain ⟨rfl, rfl, rfl, rfl⟩ := Hs
          refine nfAdmin GD i cpu _ rs ib k LInstr _ none (some (ibAnn (ibOfBvn w))) none rs _
            ⟨(annLabelNot Hsf).symm, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl trivial rfl rfl
        · simp only [Hsf, ↓reduceIte, reduceCtorEq] at Hs
      all_goals first
        | (simp only [nodeStep, reduceCtorEq] at Hs; done)
        | (simp only [nodeStep, Option.some.injEq, Prod.mk.injEq] at Hs
           obtain ⟨rfl, rfl, rfl, rfl⟩ := Hs
           exact nfAdmin GD i cpu _ rs ib k LSilent _ none none none rs ib
             ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ trivial trivial rfl rfl)

end sound

theorem driveSound (GD : Gdexec) (i : Agent) (kend fuel : Nat) :
    ∀ (m : SailM Unit) (rs : RegFile) (ib : Ibch) (k : Nat) (m' : SailM Unit) (rs' : RegFile)
      (ib' : Ibch) (k' : Nat),
      drive GD.gdG.gxImg (AxOpsem.grow GD i) kend fuel m rs ib k = some (m', rs', ib', k') →
      k' = kend ∧
      ∃ n, ∀ cpu : CPU,
        nsteps (astepAnyNfGv GD i) n (AxEpiRun.st cpu m rs ib k) (AxEpiRun.st cpu m' rs' ib' k') := by
  induction fuel with
  | zero =>
    intro m rs ib k m' rs' ib' k' Hd
    unfold drive at Hd
    split at Hd
    · rename_i hk
      simp only [Option.some.injEq, Prod.mk.injEq] at Hd
      obtain ⟨rfl, rfl, rfl, rfl⟩ := Hd
      exact ⟨hk, 0, fun _ => nsteps_O _⟩
    · simp only [reduceCtorEq] at Hd
  | succ f ih =>
    intro m rs ib k m' rs' ib' k' Hd
    unfold drive at Hd
    split at Hd
    · rename_i hk
      simp only [Option.some.injEq, Prod.mk.injEq] at Hd
      obtain ⟨rfl, rfl, rfl, rfl⟩ := Hd
      exact ⟨hk, 0, fun _ => nsteps_O _⟩
    · simp only at Hd
      cases Hn : nodeStep GD.gdG.gxImg (AxOpsem.grow GD i) m rs ib k with
      | none => simp only [Hn, reduceCtorEq] at Hd
      | some r =>
        obtain ⟨m1, rs1, ib1, k1⟩ := r
        simp only [Hn] at Hd
        obtain ⟨Hk, n, Hr⟩ := ih m1 rs1 ib1 k1 m' rs' ib' k' Hd
        exact ⟨Hk, n + 1, fun cpu =>
          nsteps_l (nodeStepSound GD i cpu m rs ib k m1 rs1 ib1 k1 Hn) (Hr cpu)⟩

/-! # 3. The concrete run at `gsdld` -/

def runFuel : Nat := Nat.pow 10 5

noncomputable def driveGsdld : Option (SailM Unit × RegFile × Ibch × Nat) :=
  drive gsdld.gdG.gxImg (AxOpsem.grow gsdld 0) 2 runFuel (riscvStep false) (probeRegs pcSd)
    ibNone 0

noncomputable def driveGsdldB : Bool :=
  match driveGsdld with
  | some (_, _, _, k) => k == 2
  | none => false

theorem driveGsdldOk : driveGsdldB = true := by
  decide +kernel

theorem epiRunGsdld (cpu : CPU) :
    ∃ n sN, sN.atK = (AxOpsem.grow gsdld 0).length ∧
      nsteps (astepAnyNfGv gsdld 0) n
        ⟨.PHart cpu (riscvStep false) (probeRegs pcSd) none ibNone, 0⟩ sN := by
  have Hok := driveGsdldOk
  unfold driveGsdldB at Hok
  cases Hd : driveGsdld with
  | none => rw [Hd] at Hok; exact absurd Hok Bool.false_ne_true
  | some r =>
    obtain ⟨m, rs, ib, k⟩ := r
    obtain ⟨Hk, n, Hr⟩ := driveSound gsdld 0 2 runFuel _ _ _ _ m rs ib k Hd
    subst Hk
    exact ⟨n, AxEpiRun.st cpu m rs ib 2, rfl, Hr cpu⟩

/-! # 4. THE CLOSED COROLLARY -/

theorem epiReloadSoundGsdld : graphValue gsdld (0, 1) = some sdData := by
  obtain ⟨Hcons, Hharts, Hgd_sd, Hrow_sd, Hw_sd, Hgd_ld, Hrow_ld, Hok_ld, Hlen, Hlob⟩ :=
    epiReloadPremisesGsdld
  obtain ⟨n, sN, Hend, Hrun⟩ := epiRunGsdld (⟨0, by decide⟩ : CPU)
  exact epiReloadSound gsdld ⟨0, by decide⟩ ldAddr Hcons Hharts Hgd_sd Hrow_sd Hw_sd Hgd_ld
    Hrow_ld Hok_ld Hlen Hlob sN n (fun _ _ => Hrun) Hend

end Weak
