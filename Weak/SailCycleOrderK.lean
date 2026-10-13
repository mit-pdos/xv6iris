/-
Weak: **W-SCO (A) — `sailCycleOrder`, the GENERIC half** (allocproc plan
`notes/weak-allocproc-plan.md` rev 36 §C W-SCO (A); [OWN.42] the cycle fact for EVERY
instruction; [OWN.45] Q-SCO-PMA = (α); [R32.1][R33.1] the boot register filter; [R28.2] shape
(0); [R29.s1] the past-fetch recipe).  Lean-only (no Rocq source).

This file proves everything of W-SCO that does NOT depend on the instructions executed: the
reduction of the named premise `sailCycleOrder` (restated under `wbootFacts σ0`,
`Weak/SrvwmoXv6Adequacy.lean`) — and of its kernel-text restriction `sailCycleOrderK` (i′) — to
ONE closed proposition about the Sail cycle's monad tree, `SailCycleOrderK.cycleOkBoot`, plus the
(iii)/(iv) corollary machinery conditional on `sailCycleOrderK`.  The tree fact itself
(`cycleOkBoot_holds`, the per-instruction half) lives in `Weak/SailCycleOrder*.lean`.  Nothing
here is registered.

## The residual invariant (`SailCycleOrderK.good`) [R28.s2][R32.1][R33.1]

`good A R Q ph m` is an all-paths predicate on a Sail tree `m` started at cycle PHASE `ph` (the
latest own `LInstr`/`LIFetch` label: `instr`, `fetch`, or none yet), mirroring the event
instance's node dispatch `pnodeStep` (`WeakEvInst.lean:294`):
* a RAM instruction-fetch read (`devAddr = false`, `akIfetch`; label `LIFetch`) continues at
  phase `fetch`, for the answers `w` whose bytes the fetch filter `A` admits at their addresses;
* every other read (MMIO `LDev`, data/page-table `LLoad`/`LExLoad`) continues, any answer, at
  the same phase;
* a `Barrier_RISCV_i` barrier (`fence.i`) requires phase `instr`;
* an announce requires phase `fetch` if it is an SFENCE.VMA word (`sfAnnB`, the marker
  `LFence false×4`) and continues at the same phase; any other announce (`LInstr`) continues
  at phase `instr`;
* a register READ continues for every answer the REGISTER FILTER `R` admits; a register WRITE
  must write a value `R` admits (so "every register admitted" is a run invariant);
* every other node continues, any answer, at the same phase; a failure node is stuck (`True`);
  at `.pure` the post `Q` holds.
The hart's own `.pure` boundary (`LInstr`) restarts the cycle `riscvStep tick` at phase
`instr`, so a per-run invariant needs exactly `cycleOk A R := ∀ tick, good A R (fun _ _ => True)
.instr (riscvStep tick)`.  `invRun` proves, by induction over `pfRunST`, that every hart's
register file is admitted by `R` and its residual tree satisfies `good` at the phase of its
latest cycle label, provided the boot register files are admitted (`hR0`), the PLIC wire's pin
writes are (`hpin`), and every fetch of the run returns bytes `A` admits (`hF`); `scoOfInv`
reads `sailCycleOrder`'s two clauses off the head node.

## The boot register filter `Rboot` [R32.1][R33.1] (platform note)

`sailCycleOrder` is FALSE over arbitrary register files: `pnodeStep` labels a read at a device
address `LDev` whatever its kind (`WeakEvInst.lean:315-321`), so a fetch from MMIO under a
`pma_regions` marking an I/O region executable leaves no `LIFetch`; and with an HTIF window over
RAM (`htif_tohost_base = some _`), `checked_mem_read` answers a fetch from the `htif_tohost`
register through `within_mmio_readable` (`Mem.lean:437-446`, `Platform.lean:243-249`) with NO
memory node at all.  Either way an SFENCE.VMA word is announced at phase `instr`.  On THIS board
both registers are pinned at reset (`bootPost`, `MachCSL/BootInitModel.lean:39,41`: `pma_regions =
bootPMA`, both I/O regions non-executable; `htif_tohost_base = none`) and are never written by
the cycle; `Rboot` pins exactly these two.  `rbootInit` reads them off `wbootFacts σ0` through
`resetRegsRun_of_run` (`MachCSL/BootReset.lean`, [R33.s2]); `rbootPin`: the PLIC wire writes
`sig_meip`/`sig_seip` only.

## The two instances

* **Every fetched word** (`A = True`, `R = Rboot`): `sailCycleOrderOfCycle : cycleOkBoot →
  sailCycleOrder` — the general premise from the tree fact (option (a) of §B(11), [OWN.42]).
* **Kernel text** (`A = kWin`): `sailCycleOrderKOfCycle : cycleOkK → sailCycleOrderK` (the (i′)
  record; `cycleOkKOfBoot : cycleOkBoot → cycleOkK`).  Every fetch of an M1 run is admitted:
  its addresses by `candKfetch` (`pfStepFacts`), its bytes by [R29.s1] (`MachOfPf.noWriteOfPristine`,
  `SailCycleOrderK.stepLogPrefix`, `MachOfPf.fetchIsImage`).

## The corollary machinery (iii)/(iv)

`SailCycleOrderK.fiOfScoK`, `m1HypsK`, `srvwmoXv6M1OfK` (M1 without `hsco`, from
`sailCycleOrderK`) — REDUNDANT once `sailCycleOrder_holds` lands (`srvwmoXv6M1` applies
`srvwmoXv6M1Core` directly); kept as a record.

## Deviations from the brief

1. (rev 36 §C W-SCO (A) (ii)) `good`'s `.regWrite r v` arm requires `R r v` (the written value is
   admitted) rather than `r ≠ pma_regions ∧ r ≠ htif_tohost_base`: for `Rboot` this is the same
   up to also admitting a write of the pinned value itself; the run invariant is preserved
   generically (`rSet`).  `Rboot` uses the `match` form ([R33.s3]).
2. `cycleOkAll` (FALSE as defined — fetch from MMIO, [R32.1]) is DELETED; `cycleOkK` is kept with
   the register filter (now implied by `cycleOkBoot`).
3. [R29.s1]'s `fetchIsImage` is stated per fetch STEP; the position-generic use is
   `SailCycleOrderK.invRun`'s induction, which carries the final log's cleanliness BACKWARD
   (`stepLogPrefix`).

Every helper is `Weak.SailCycleOrderK.*`; `Weak.sailCycleOrderK` is top-level.
-/
import Weak.SrvwmoXv6Adequacy

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open Sail Sail.ConcurrencyInterfaceV1 LeanRV64D
open Sail.ArchSem (FreeM)
open TsoShadow PfStepTsoMem PfStepTsoView
open Iris.ProgramLogic

/-! ## (1) The statement (i′) -/

/-- **`sailCycleOrder` restricted to M1's kernel-text runs** (W-SCO (i′) [R28.2]): along every
`candKfetch bcRoLo bcRoHi` run from a booted pf configuration (`wbootFacts σ0`), related by
`SimRel` to a MachCSL run from a machine-off state `g0` as in `m1Hyps` (generation 0, power off,
`fs.img`), at an own `fence.i` BARRIER node the latest own `LInstr`/`LIFetch` step is `LInstr`,
and at an own `sfence.vma` ANNOUNCE node it is an `LIFetch`. -/
def sailCycleOrderK : Prop :=
  ∀ (σ0 : WGState) (g0 : GState), wbootFacts σ0 → g0.gen = 0 → g0.pow = false →
    diskOf g0.m.devs = Xv6.fsImgDisk →
    ∀ (st : List (Nat × Wlabel)) (c : Wpcfg Pexv6 Efab) (t : List Expr) (g : GState) (n : Nat)
      (κ : List Obs),
      pfRunST pstepEv pclsEv (candKfetch (Xv6.bcRoLo : Int) (Xv6.bcRoHi : Int)) TsoShadow.cohSrc
        (wpInit (imgZ σ0.wgimg) (efInit σ0.wgdev) (epsInit σ0)) st c →
      MachOfPf.MRun n ([Expr.power], g0) κ (t, g) → MachOfPf.SimRel c st t g →
      ∀ (cpu : CPU) (o : Outcome Register RegisterType) (k : o.ret → SailM Unit) (rs : RegFile)
        (ib : Ibch) (ws : Wstate) (pr : GSet Nat),
        c.pcAgs[cpu.val]? = some ⟨.PHart cpu (.impure (.ok o) k) rs none ib, ws, pr⟩ →
        (o = .barrier .Barrier_RISCV_i →
           SrvwmoXv6Adequacy.lastCyc (hartAgent cpu) st = some .LInstr) ∧
        (∀ n w, o = .instrAnnounce n w → sfAnnB n w = true →
           ∃ base tvs, SrvwmoXv6Adequacy.lastCyc (hartAgent cpu) st = some (.LIFetch base tvs))

/-! ## (2) The residual invariant -/

/-- The phase of Sail's cycle (Lean-only): no cycle label yet, after an `LInstr` (boundary or
announce), after an `LIFetch`. -/
inductive SailCycleOrderK.Ph where
  | none
  | instr
  | fetch
  deriving DecidableEq

/-- The phase a latest own cycle label stands for. -/
def SailCycleOrderK.phOf (x : Option Wlabel) : SailCycleOrderK.Ph :=
  match x with
  | some .LInstr => .instr
  | some (.LIFetch ..) => .fetch
  | _ => .none

theorem SailCycleOrderK.phOfInstr (x : Option Wlabel) (h : SailCycleOrderK.phOf x = .instr) :
    x = some .LInstr := by
  rcases x with _ | l
  · cases h
  · cases l <;> first | rfl | cases h

theorem SailCycleOrderK.phOfFetch (x : Option Wlabel) (h : SailCycleOrderK.phOf x = .fetch) :
    ∃ base tvs, x = some (.LIFetch base tvs) := by
  rcases x with _ | l
  · cases h
  · cases l <;> first | exact ⟨_, _, rfl⟩ | cases h

/-- **THE RESIDUAL INVARIANT** (header): all paths of `m`, from phase `ph`, under the fetch filter
`A` (per byte: address, value), the REGISTER FILTER `R` [R32.1][R33.1] (a register read is
answered by a value `R` admits; a register write must write one) and the post `Q`. -/
def SailCycleOrderK.good {α : Type} (A : Int → BitVec 8 → Prop)
    (R : (r : Register) → RegisterType r → Prop)
    (Q : SailCycleOrderK.Ph → α → Prop) : SailCycleOrderK.Ph → SailM α → Prop
  | ph, .pure a => Q ph a
  | _, .impure (.error _) _ => True
  | ph, .impure (.ok o) k =>
    match o, k with
    | .memRead n _ req, k =>
        (devAddr req.pa = false → (classify req.access_kind).akIfetch = true →
          ∀ w : BitVec (8 * n), (∀ j, j < n → A (paZ req.pa + (j : Int)) (nthByte w j)) →
            SailCycleOrderK.good A R Q .fetch (k (.Ok (w, none)))) ∧
        ((devAddr req.pa = false → (classify req.access_kind).akIfetch = false) →
          ∀ v, SailCycleOrderK.good A R Q ph (k v))
    | .barrier b, k =>
        (b = .Barrier_RISCV_i → ph = .instr) ∧ SailCycleOrderK.good A R Q ph (k ())
    | .instrAnnounce n w, k =>
        (sfAnnB n w = true → ph = .fetch) ∧
        SailCycleOrderK.good A R Q (if sfAnnB n w then ph else .instr) (k ())
    | .regRead r, k => ∀ v, R r v → SailCycleOrderK.good A R Q ph (k v)
    | .regWrite r v, k => R r v ∧ ∀ u, SailCycleOrderK.good A R Q ph (k u)
    | .memWrite .., k => ∀ v, SailCycleOrderK.good A R Q ph (k v)
    | .branchAnnounce .., k => ∀ v, SailCycleOrderK.good A R Q ph (k v)
    | .cacheOp _, k => ∀ v, SailCycleOrderK.good A R Q ph (k v)
    | .tlbi _, k => ∀ v, SailCycleOrderK.good A R Q ph (k v)
    | .takeException _, k => ∀ v, SailCycleOrderK.good A R Q ph (k v)
    | .returnException _, k => ∀ v, SailCycleOrderK.good A R Q ph (k v)
    | .translationStart _, k => ∀ v, SailCycleOrderK.good A R Q ph (k v)
    | .translationEnd _, k => ∀ v, SailCycleOrderK.good A R Q ph (k v)
    | .cycleCount, k => ∀ v, SailCycleOrderK.good A R Q ph (k v)
    | .getCycleCount, k => ∀ v, SailCycleOrderK.good A R Q ph (k v)
    | .message _, k => ∀ v, SailCycleOrderK.good A R Q ph (k v)
    | .choose _, k => ∀ v, SailCycleOrderK.good A R Q ph (k v)
    | .readRam .., k => ∀ v, SailCycleOrderK.good A R Q ph (k v)
    | .writeRam .., k => ∀ v, SailCycleOrderK.good A R Q ph (k v)

/-- The kit's bind law: `good` of `m >>= f` from `good` of `m` with post "`good` of `f`". -/
theorem SailCycleOrderK.goodBind {α β : Type} (A : Int → BitVec 8 → Prop)
    (R : (r : Register) → RegisterType r → Prop)
    (Q : SailCycleOrderK.Ph → β → Prop) (f : α → SailM β) :
    ∀ (m : SailM α) (ph : SailCycleOrderK.Ph),
      SailCycleOrderK.good A R (fun ph' a => SailCycleOrderK.good A R Q ph' (f a)) ph m →
      SailCycleOrderK.good A R Q ph (m >>= f) := by
  intro m
  induction m with
  | pure a => intro ph h; exact h
  | impure call k ih =>
    intro ph hm
    cases call with
    | error e => trivial
    | ok o =>
      show SailCycleOrderK.good A R Q ph (FreeM.impure (.ok o) (fun v => k v >>= f))
      cases o
      case memRead n va req =>
        exact ⟨fun h1 h2 w hw => ih _ _ (hm.1 h1 h2 w hw), fun h v => ih _ _ (hm.2 h v)⟩
      case barrier b => exact ⟨hm.1, ih _ _ hm.2⟩
      case instrAnnounce n w => exact ⟨hm.1, ih _ _ hm.2⟩
      case regRead r => exact fun v hv => ih _ _ (hm v hv)
      case regWrite r v => exact ⟨hm.1, fun u => ih _ _ (hm.2 u)⟩
      all_goals exact fun v => ih _ _ (hm v)

/-- The kit's consequence law (posts and fetch filters). -/
theorem SailCycleOrderK.goodMono {α : Type} (A A' : Int → BitVec 8 → Prop)
    (R : (r : Register) → RegisterType r → Prop)
    (Q Q' : SailCycleOrderK.Ph → α → Prop) (hA : ∀ a v, A' a v → A a v)
    (hQ : ∀ ph a, Q ph a → Q' ph a) :
    ∀ (m : SailM α) (ph : SailCycleOrderK.Ph),
      SailCycleOrderK.good A R Q ph m → SailCycleOrderK.good A' R Q' ph m := by
  intro m
  induction m with
  | pure a => intro ph h; exact hQ ph a h
  | impure call k ih =>
    intro ph hm
    cases call with
    | error e => trivial
    | ok o =>
      cases o
      case memRead n va req =>
        exact ⟨fun h1 h2 w hw => ih _ _ (hm.1 h1 h2 w (fun j hj => hA _ _ (hw j hj))),
          fun h v => ih _ _ (hm.2 h v)⟩
      case barrier b => exact ⟨hm.1, ih _ _ hm.2⟩
      case instrAnnounce n w => exact ⟨hm.1, ih _ _ hm.2⟩
      case regRead r => exact fun v hv => ih _ _ (hm v hv)
      case regWrite r v => exact ⟨hm.1, fun u => ih _ _ (hm.2 u)⟩
      all_goals exact fun v => ih _ _ (hm v)

/-- **The boot register filter** [R32.1][R33.1] (Q-SCO-PMA (α), [OWN.45]): the two configuration
registers on the instruction-fetch path that this board pins at reset (`bootPost`,
`MachCSL/BootInitModel.lean:39,41`; `MachCSL.hwVal`) — the PMA table `pma_regions = bootPMA`
(both I/O regions non-executable) and the HTIF window `htif_tohost_base = none` (disabled); every
other register unconstrained. -/
def SailCycleOrderK.Rboot : (r : Register) → RegisterType r → Prop
  | .pma_regions, v => v = bootPMA
  | .htif_tohost_base, v => v = none
  | _, _ => True

/-- **THE TREE OBLIGATION** under fetch filter `A` and register filter `R`: every cycle
`riscvStep tick`, started at the boundary (phase `instr`), satisfies the residual invariant. -/
def SailCycleOrderK.cycleOk (A : Int → BitVec 8 → Prop)
    (R : (r : Register) → RegisterType r → Prop) : Prop :=
  ∀ tick : Bool, SailCycleOrderK.good A R (fun _ _ => True) .instr (riscvStep tick)

/-- **W-SCO (A)'s deliverable (1)** [R32.1][R33.1]: the cycle obligation for EVERY fetched word,
under the boot register filter. -/
def SailCycleOrderK.cycleOkBoot : Prop :=
  SailCycleOrderK.cycleOk (fun _ _ => True) SailCycleOrderK.Rboot

/-- The kernel-text fetch filter: a byte inside `[bcRoLo, bcRoHi)` holding the boot image's
byte. -/
def SailCycleOrderK.kWin (a : Int) (v : BitVec 8) : Prop :=
  (Xv6.bcRoLo : Int) ≤ a ∧ a < (Xv6.bcRoHi : Int) ∧ imgZ bootImage a = some v

/-- The kernel-text cycle obligation (the (i′) record; implied by `cycleOkBoot`,
`cycleOkKOfBoot`). -/
def SailCycleOrderK.cycleOkK : Prop := SailCycleOrderK.cycleOk SailCycleOrderK.kWin SailCycleOrderK.Rboot

theorem SailCycleOrderK.cycleOkKOfBoot (h : SailCycleOrderK.cycleOkBoot) : SailCycleOrderK.cycleOkK :=
  fun tick => SailCycleOrderK.goodMono _ _ _ _ _ (fun _ _ _ => trivial) (fun _ _ h => h) _ _ (h tick)

/-! ## (3) The run invariant -/

/-- The latest own cycle label after one more step. -/
theorem SailCycleOrderK.lastCycSnoc (i j : Nat) (l : Wlabel) (st : List (Nat × Wlabel)) :
    SrvwmoXv6Adequacy.lastCyc i (st ++ [(j, l)]) =
      if j = i ∧ SrvwmoXv6Adequacy.lbCyc l = true then some l
      else SrvwmoXv6Adequacy.lastCyc i st := by
  unfold SrvwmoXv6Adequacy.lastCyc
  rw [List.filter_append]
  by_cases h : j = i ∧ SrvwmoXv6Adequacy.lbCyc l = true
  · rw [if_pos h]
    obtain ⟨rfl, hl⟩ := h
    simp [hl]
  · rw [if_neg h]
    have hf : List.filter
        (fun y : Nat × Wlabel => y.1 == i && SrvwmoXv6Adequacy.lbCyc y.2) [(j, l)] = [] := by
      simp only [List.filter_cons, List.filter_nil]
      rw [if_neg]
      simpa [Bool.and_eq_true, beq_iff_eq] using h
    rw [hf, List.append_nil]

/-- A label that is not a cycle label keeps the phase. -/
theorem SailCycleOrderK.phSnocOther (i j : Nat) (l : Wlabel) (st : List (Nat × Wlabel))
    (h : SrvwmoXv6Adequacy.lbCyc l = false) :
    SailCycleOrderK.phOf (SrvwmoXv6Adequacy.lastCyc i (st ++ [(j, l)])) =
      SailCycleOrderK.phOf (SrvwmoXv6Adequacy.lastCyc i st) := by
  rw [SailCycleOrderK.lastCycSnoc, if_neg (by rw [h]; simp)]

/-- A register write of an admitted value keeps "every register admitted". -/
theorem SailCycleOrderK.rSet (R : (r : Register) → RegisterType r → Prop) (rs : RegFile)
    (r : Register) (v : RegisterType r) (hrs : ∀ r', R r' (rs r')) (hv : R r v) :
    ∀ r', R r' (rs.set r v r') := by
  intro r'
  by_cases h : r' = r
  · subst h
    rw [RegFile.set_same]
    exact hv
  · rw [RegFile.set_other _ _ _ _ h]
    exact hrs r'

/-- The run invariant: every hart's register file is admitted by `R`, and its residual tree is
`good` at the phase of its latest cycle label. -/
def SailCycleOrderK.inv (A : Int → BitVec 8 → Prop) (R : (r : Register) → RegisterType r → Prop)
    (st : List (Nat × Wlabel)) (c : Wpcfg Pexv6 Efab) : Prop :=
  ∀ (cpu : CPU) (m : SailM Unit) (rs : RegFile) (fn : Option (Bool × Bool × Bool × Bool))
    (ib : Ibch) (ws : Wstate) (pr : GSet Nat),
    c.pcAgs[cpu.val]? = some ⟨.PHart cpu m rs fn ib, ws, pr⟩ →
    (∀ r, R r (rs r)) ∧
    SailCycleOrderK.good A R (fun _ _ => True)
      (SailCycleOrderK.phOf (SrvwmoXv6Adequacy.lastCyc (hartAgent cpu) st)) m

/-- The ONE-NODE step of the invariant (the hart's own `pnodeStep`, not at the boundary). -/
theorem SailCycleOrderK.nodeStep (A : Int → BitVec 8 → Prop)
    (R : (r : Register) → RegisterType r → Prop) (ph : SailCycleOrderK.Ph)
    (o : Outcome Register RegisterType) (k : o.ret → SailM Unit) (rs : RegFile) (ib : Ibch)
    (d : DevStates) (l : Wlabel) (m' : SailM Unit) (ors : Option RegFile)
    (fn' : Option (Bool × Bool × Bool × Bool)) (d' : DevStates) (oib : Option Ibch)
    (obar : Option barrier_kind)
    (hn : pnodeStep (.impure (.ok o) k) rs ib d l m' ors fn' d' oib obar)
    (hA : ∀ base tvs, l = .LIFetch base tvs →
      ∀ (j t : Nat) (v : BitVec 8), tvs[j]? = some (t, v) → A (base + (j : Int)) v)
    (hrs : ∀ r, R r (rs r))
    (hg : SailCycleOrderK.good A R (fun _ _ => True) ph (.impure (.ok o) k)) :
    (∀ r, R r ((ors.getD rs) r)) ∧
    SailCycleOrderK.good A R (fun _ _ => True)
      (if SrvwmoXv6Adequacy.lbCyc l = true then SailCycleOrderK.phOf (some l) else ph) m' := by
  cases o
  case memRead nb va req =>
    simp only [pnodeStep] at hn
    split at hn
    · rename_i hdev
      obtain ⟨w, -, rfl, rfl, rfl, -⟩ := hn
      exact ⟨hrs, hg.2 (fun h => by rw [hdev] at h; cases h) _⟩
    · rename_i hdev
      have hdev' : devAddr req.pa = false := by simpa using hdev
      rcases hn with ⟨hif, w, tvs, hlen, hbytes, rfl, rfl, rfl, -⟩ | ⟨hif, hn⟩
      · simp only [SrvwmoXv6Adequacy.lbCyc, ↓reduceIte, SailCycleOrderK.phOf]
        refine ⟨hrs, hg.1 hdev' hif w (fun j hj => ?_)⟩
        have hj' : j < tvs.length := by omega
        obtain ⟨⟨t, v⟩, hx⟩ : ∃ x, tvs[j]? = some x := ⟨_, List.getElem?_eq_getElem hj'⟩
        have hv : (tvs.map Prod.snd)[j]? = some v := by simp [hx]
        rw [hbytes j hj] at hv
        cases hv
        exact hA _ _ rfl j t _ hx
      · rcases hn with ⟨-, w, tvs, -, -, rfl, rfl, rfl, -⟩ | ⟨-, w, tvs, -, -, rfl, rfl, rfl, -⟩
        · exact ⟨hrs, hg.2 (fun _ => hif) _⟩
        · exact ⟨hrs, hg.2 (fun _ => hif) _⟩
  case memWrite nb va req =>
    simp only [pnodeStep] at hn
    split at hn
    · split at hn
      · obtain ⟨-, rfl, rfl, rfl, -⟩ := hn
        exact ⟨hrs, hg _⟩
      · exact hn.elim
    · split at hn
      · obtain ⟨-, ⟨-, rfl, rfl, rfl, -⟩ | ⟨-, ⟨rfl, rfl, rfl, -⟩ | ⟨rfl, rfl, rfl, -⟩⟩⟩ := hn
        · exact ⟨hrs, hg _⟩
        · exact ⟨hrs, hg _⟩
        · exact ⟨hrs, hg⟩
      · exact hn.elim
  case barrier b =>
    simp only [pnodeStep] at hn
    obtain ⟨rfl, rfl, rfl, -⟩ := hn
    have : SrvwmoXv6Adequacy.lbCyc (ebarLabel b) = false := by
      unfold ebarLabel; split <;> rfl
    rw [if_neg (by rw [this]; simp)]
    exact ⟨hrs, hg.2⟩
  case instrAnnounce n w =>
    simp only [pnodeStep] at hn
    obtain ⟨rfl, rfl, rfl, -⟩ := hn
    have hg2 := hg.2
    refine ⟨hrs, ?_⟩
    unfold annLabel
    cases hs : sfAnnB n w
    · simp only [hs, Bool.false_eq_true, ↓reduceIte] at hg2 ⊢
      exact hg2
    · simp only [hs, ↓reduceIte] at hg2 ⊢
      exact hg2
  case regRead r =>
    simp only [pnodeStep] at hn
    obtain ⟨rfl, rfl, rfl, -⟩ := hn
    exact ⟨hrs, hg _ (hrs r)⟩
  case regWrite r v =>
    simp only [pnodeStep] at hn
    obtain ⟨rfl, rfl, rfl, -⟩ := hn
    have : SrvwmoXv6Adequacy.lbCyc (erwLabel (erwOf (depsOfIb ib.ibBits) ib.ibRds r)) = false := by
      unfold erwLabel; split <;> rfl
    rw [if_neg (by rw [this]; simp)]
    exact ⟨SailCycleOrderK.rSet R rs r v hrs hg.1, hg.2 _⟩
  case choose _ =>
    simp only [pnodeStep] at hn
    obtain ⟨ch, rfl, rfl, rfl, -⟩ := hn
    exact ⟨hrs, hg _⟩
  case readRam => exact hn.elim
  case writeRam => exact hn.elim
  all_goals
    simp only [pnodeStep] at hn
    obtain ⟨rfl, rfl, rfl, -⟩ := hn
    exact ⟨hrs, hg _⟩

/-- **The step of the run invariant**: one `wpPfStep` keeps `inv`, provided a fetch step returns
bytes the filter admits and the PLIC wire's pin writes are admitted (`hpin`). -/
theorem SailCycleOrderK.invStep (A : Int → BitVec 8 → Prop)
    (R : (r : Register) → RegisterType r → Prop) (hcyc : SailCycleOrderK.cycleOk A R)
    (hpin : ∀ (rs : RegFile) (mm b : Bool), (∀ r, R r (rs r)) → ∀ r, R r (pinSet rs mm b r))
    (st : List (Nat × Wlabel)) (i : Nat) (l : Wlabel) (c1 c2 : Wpcfg Pexv6 Efab)
    (hs : wpPfStep pstepEv pclsEv i l c1 c2)
    (hA : ∀ base tvs, l = .LIFetch base tvs →
      ∀ (j t : Nat) (v : BitVec 8), tvs[j]? = some (t, v) → A (base + (j : Int)) v)
    (hI : SailCycleOrderK.inv A R st c1) : SailCycleOrderK.inv A R (st ++ [(i, l)]) c2 := by
  intro cpu m rs fn ib ws pr hlk
  obtain ⟨ag, p', d', ws', hlk1, hps, -, -, hags⟩ := MachOfPf.wpPfStepInv _ _ i l c1 c2 hs
  rw [hags] at hlk
  by_cases hi : i = cpu.val
  · subst hi
    rw [List.getElem?_set_self (lookup_lt_Some hlk1)] at hlk
    simp only [Option.some.injEq, Wpagent.mk.injEq] at hlk
    obtain ⟨rfl, -, -⟩ := hlk
    rcases hag : ag with ⟨p0, ws0, pr0⟩
    rw [hag] at hlk1 hps
    cases p0 with
    | PDisk dp => exact hps.elim
    | PHart cpu0 m0 rs0 fn0 ib0 =>
      obtain ⟨hcpu, ors, oib, obar, hrs', -, hh⟩ := hps
      subst hcpu
      subst hrs'
      obtain ⟨hR0, hg⟩ := hI cpu m0 rs0 fn0 ib0 ws0 pr0 hlk1
      have hph : SailCycleOrderK.phOf (SrvwmoXv6Adequacy.lastCyc (hartAgent cpu)
            (st ++ [(cpu.val, l)])) =
          if SrvwmoXv6Adequacy.lbCyc l = true then SailCycleOrderK.phOf (some l)
          else SailCycleOrderK.phOf (SrvwmoXv6Adequacy.lastCyc (hartAgent cpu) st) := by
        rw [SailCycleOrderK.lastCycSnoc]
        by_cases hc : SrvwmoXv6Adequacy.lbCyc l = true
        · rw [if_pos ⟨rfl, hc⟩, if_pos hc]
        · rw [if_neg (fun h => hc h.2), if_neg hc]
      rw [hph]
      rcases hh with ⟨hnd, -⟩ | ⟨mm, b, kp, -, rfl, rfl, -, -, -, -, rfl⟩
      · unfold pstepNode at hnd
        split at hnd
        · obtain ⟨rfl, rfl, rfl, -⟩ := hnd
          rw [if_neg (by simp [SrvwmoXv6Adequacy.lbCyc])]
          exact ⟨hR0, hg⟩
        · cases m0 with
          | pure u =>
            simp only [pnodeStep] at hnd
            obtain ⟨tick, rfl, rfl, rfl, -⟩ := hnd
            simp only [SrvwmoXv6Adequacy.lbCyc, ↓reduceIte, SailCycleOrderK.phOf]
            exact ⟨hR0, hcyc tick⟩
          | impure call kk =>
            cases call with
            | error e => exact hnd.elim
            | ok o => exact SailCycleOrderK.nodeStep A R _ o kk rs0 ib0 _ l m _ _ _ _ _ hnd hA hR0 hg
      · rw [if_neg (by simp [SrvwmoXv6Adequacy.lbCyc])]
        exact ⟨hpin rs0 mm b hR0, hg⟩
  · rw [List.getElem?_set_ne hi] at hlk
    have hg := hI cpu m rs fn ib ws pr hlk
    rw [SailCycleOrderK.lastCycSnoc, if_neg (fun h => hi h.1)]
    exact hg

/-- Every hart of the pf boot configuration sits at the boundary (`.pure ()`) on its boot
register file. -/
theorem SailCycleOrderK.invInit (A : Int → BitVec 8 → Prop)
    (R : (r : Register) → RegisterType r → Prop) (img : Image) (d0 : Efab)
    (σ0 : WGState) (hR0 : ∀ (c : CPU) r, R r (σ0.wgregs c r)) :
    SailCycleOrderK.inv A R [] (wpInit img d0 (epsInit σ0)) := by
  intro cpu m rs fn ib ws pr hlk
  have hm := List.mem_of_getElem? hlk
  simp only [wpInit, epsInit, List.map_append, List.map_map, List.mem_append, List.mem_map,
    List.mem_singleton, Function.comp_def] at hm
  rcases hm with ⟨c, -, hc⟩ | hc
  · simp only [Wpagent.mk.injEq, Pexv6.PHart.injEq] at hc
    obtain ⟨⟨-, rfl, rfl, -⟩, -⟩ := hc
    exact ⟨hR0 c, trivial⟩
  · simp at hc

/-- **THE RUN INVARIANT** (induction over `pfRunST`): under the cycle obligation, along every run
from the pf boot configuration whose register files `R` admits (`hR0`, `hpin`) and whose fetches
return bytes the filter admits — as read off a backward-stable fact `E` of the run's
configurations (`hE`, `hF`) — every hart's register file is admitted and its residual tree is
`good` at the phase of its latest cycle label. -/
theorem SailCycleOrderK.invRun (A : Int → BitVec 8 → Prop)
    (R : (r : Register) → RegisterType r → Prop) (hcyc : SailCycleOrderK.cycleOk A R)
    (fok : Image → List Wmsg → Nat → Int → List (Nat × BitVec 8) → Prop)
    (img : Image) (d0 : Efab) (σ0 : WGState) (hR0 : ∀ (c : CPU) r, R r (σ0.wgregs c r))
    (hpin : ∀ (rs : RegFile) (mm b : Bool), (∀ r, R r (rs r)) → ∀ r, R r (pinSet rs mm b r))
    (E : Wpcfg Pexv6 Efab → Prop)
    (hE : ∀ i l c1 c2, wpPfStep pstepEv pclsEv i l c1 c2 → E c2 → E c1)
    (hF : ∀ i base tvs c1 c2, wpPfStep pstepEv pclsEv i (.LIFetch base tvs) c1 c2 →
      pfStepFacts fok c1 i (.LIFetch base tvs) → E c1 →
      ∀ (j t : Nat) (v : BitVec 8), tvs[j]? = some (t, v) → A (base + (j : Int)) v) :
    ∀ (st : List (Nat × Wlabel)) (c : Wpcfg Pexv6 Efab),
      pfRunST pstepEv pclsEv fok TsoShadow.cohSrc (wpInit img d0 (epsInit σ0)) st c → E c →
      SailCycleOrderK.inv A R st c := by
  intro st c hrun
  induction hrun with
  | nil => intro _; exact SailCycleOrderK.invInit A R img d0 σ0 hR0
  | snoc c1 c2 st i l _ hs hf _ _ ih =>
    intro hE2
    have hE1 := hE i l c1 c2 hs hE2
    exact SailCycleOrderK.invStep A R hcyc hpin st i l c1 c2 hs
      (fun base tvs hl => by subst hl; exact hF i base tvs c1 c2 hs hf hE1) (ih hE1)

/-- **The conclusion** read off the invariant at a hart's head node. -/
theorem SailCycleOrderK.scoOfInv (A : Int → BitVec 8 → Prop)
    (R : (r : Register) → RegisterType r → Prop) (st : List (Nat × Wlabel))
    (c : Wpcfg Pexv6 Efab) (hI : SailCycleOrderK.inv A R st c) :
    ∀ (cpu : CPU) (o : Outcome Register RegisterType) (k : o.ret → SailM Unit) (rs : RegFile)
      (ib : Ibch) (ws : Wstate) (pr : GSet Nat),
      c.pcAgs[cpu.val]? = some ⟨.PHart cpu (.impure (.ok o) k) rs none ib, ws, pr⟩ →
      (o = .barrier .Barrier_RISCV_i →
         SrvwmoXv6Adequacy.lastCyc (hartAgent cpu) st = some .LInstr) ∧
      (∀ n w, o = .instrAnnounce n w → sfAnnB n w = true →
         ∃ base tvs, SrvwmoXv6Adequacy.lastCyc (hartAgent cpu) st = some (.LIFetch base tvs)) := by
  intro cpu o k rs ib ws pr hlk
  have hg := (hI cpu _ rs none ib ws pr hlk).2
  refine ⟨fun ho => ?_, fun n w ho hsf => ?_⟩
  · subst ho
    exact SailCycleOrderK.phOfInstr _ (hg.1 rfl)
  · subst ho
    exact SailCycleOrderK.phOfFetch _ (hg.1 hsf)

/-! ## (4) The two instances -/

/-- The boot register files are admitted by `Rboot` (`wbootFacts` → `resetRegsRun_of_run`
[R33.s2]: `bootPost`'s `pma_regions = bootPMA` and `htif_tohost_base = none`). -/
theorem SailCycleOrderK.rbootInit (σ0 : WGState) (hb : wbootFacts σ0) :
    ∀ (c : CPU) r, SailCycleOrderK.Rboot r (σ0.wgregs c r) := by
  intro c r
  obtain ⟨f₀, hf⟩ := hb.2.2.2.2.2.1 c
  have h := (resetRegsRun_of_run c f₀ _ hf).1
  unfold SailCycleOrderK.Rboot
  split
  · exact h _ _ rfl
  · exact h _ _ rfl
  · trivial

/-- The PLIC wire writes `sig_meip`/`sig_seip` only: `Rboot` is kept. -/
theorem SailCycleOrderK.rbootPin (rs : RegFile) (mm b : Bool)
    (h : ∀ r, SailCycleOrderK.Rboot r (rs r)) : ∀ r, SailCycleOrderK.Rboot r (pinSet rs mm b r) := by
  unfold pinSet
  split
  · exact SailCycleOrderK.rSet _ rs _ _ h trivial
  · exact SailCycleOrderK.rSet _ rs _ _ h trivial

/-- **The general premise from the tree fact** [R32.1]: `cycleOkBoot → sailCycleOrder`. -/
theorem SailCycleOrderK.sailCycleOrderOfCycle (h : SailCycleOrderK.cycleOkBoot) :
    sailCycleOrder := by
  intro fok σ0 hb st c hrun
  exact SailCycleOrderK.scoOfInv _ _ st c
    (SailCycleOrderK.invRun _ _ h fok _ _ σ0 (SailCycleOrderK.rbootInit σ0 hb)
      SailCycleOrderK.rbootPin (fun _ => True) (fun _ _ _ _ _ _ => trivial)
      (fun _ _ _ _ _ _ _ _ _ _ _ _ => trivial) st c hrun trivial)

/-- [R29.s1] (b): a step only APPENDS to the log and keeps the image. -/
theorem SailCycleOrderK.stepLogPrefix (i : Nat) (l : Wlabel) (c1 c2 : Wpcfg Pexv6 Efab)
    (hs : wpPfStep pstepEv pclsEv i l c1 c2) :
    c2.pcImg = c1.pcImg ∧ ∃ ms, c2.pcLog = c1.pcLog ++ ms := by
  cases hs <;> first | exact ⟨rfl, _, (List.append_nil _).symm⟩ | exact ⟨rfl, _, rfl⟩

/-- The run keeps its image. -/
theorem SailCycleOrderK.runImg (fok : Image → List Wmsg → Nat → Int → List (Nat × BitVec 8) → Prop)
    (c0 : Wpcfg Pexv6 Efab) :
    ∀ (st : List (Nat × Wlabel)) (c : Wpcfg Pexv6 Efab),
      pfRunST pstepEv pclsEv fok TsoShadow.cohSrc c0 st c → c.pcImg = c0.pcImg := by
  intro st c h
  induction h with
  | nil => rfl
  | snoc c1 c2 st i l _ hs _ _ _ ih =>
    exact (SailCycleOrderK.stepLogPrefix i l c1 c2 hs).1.trans ih

/-- The backward-stable fact of an M1 run: the boot image, and no log message writing a window
byte. -/
def SailCycleOrderK.cleanK (c : Wpcfg Pexv6 Efab) : Prop :=
  c.pcImg = imgZ bootImage ∧
  ∀ a : Int, (Xv6.bcRoLo : Int) ≤ a → a < (Xv6.bcRoHi : Int) →
    ∀ i : Nat, c.pcLog[i]?.bind (fun m => msgByte m a) = none

theorem SailCycleOrderK.cleanKBack (i : Nat) (l : Wlabel) (c1 c2 : Wpcfg Pexv6 Efab)
    (hs : wpPfStep pstepEv pclsEv i l c1 c2) (h : SailCycleOrderK.cleanK c2) :
    SailCycleOrderK.cleanK c1 := by
  obtain ⟨himg, ms, hlog⟩ := SailCycleOrderK.stepLogPrefix i l c1 c2 hs
  refine ⟨himg ▸ h.1, fun a h1 h2 j => ?_⟩
  have h' := h.2 a h1 h2 j
  rw [hlog] at h'
  cases hj : c1.pcLog[j]? with
  | none => rfl
  | some x =>
    rw [List.getElem?_append_left (lookup_lt_Some hj), hj] at h'
    exact h'

/-- Every fetch of an M1 run reads window bytes holding the boot image ([R29.s1]). -/
theorem SailCycleOrderK.fetchK (i : Nat) (base : Int) (tvs : List (Nat × BitVec 8))
    (c1 c2 : Wpcfg Pexv6 Efab)
    (hs : wpPfStep pstepEv pclsEv i (.LIFetch base tvs) c1 c2)
    (hf : pfStepFacts (candKfetch (Xv6.bcRoLo : Int) (Xv6.bcRoHi : Int)) c1 i (.LIFetch base tvs))
    (hc : SailCycleOrderK.cleanK c1) :
    ∀ (j t : Nat) (v : BitVec 8), tvs[j]? = some (t, v) → SailCycleOrderK.kWin (base + (j : Int)) v := by
  intro j t v hj
  have hif : ifetchOk c1.pcImg c1.pcLog 0 base tvs := by
    cases hs with
    | PFIFetch _ _ _ _ _ _ _ _ h => exact h
  have hnw : ∀ j, j < tvs.length →
      ∀ i : Nat, c1.pcLog[i]?.bind (fun m => msgByte m (base + (j : Int))) = none := by
    intro j hj
    obtain ⟨h1, h2⟩ := hf j hj
    exact hc.2 _ h1 h2
  obtain ⟨-, hv⟩ := MachOfPf.fetchIsImage _ _ _ _ _ hif hnw j t v hj
  obtain ⟨h1, h2⟩ := hf j (lookup_lt_Some hj)
  rw [logByte0, hc.1] at hv
  exact ⟨h1, h2, hv⟩

/-- **`sailCycleOrderK` from the kernel-text tree fact.** -/
theorem SailCycleOrderK.sailCycleOrderKOfCycle (h : SailCycleOrderK.cycleOkK) :
    sailCycleOrderK := by
  intro σ0 g0 hb hg0 hp0 hfs st c t g n κ hrun hreach hR
  have hwin := SrvwmoXv6Adequacy.winOfText g0 hg0 hp0 hfs n κ t g hreach hR.pow
  have hclean : SailCycleOrderK.cleanK c := by
    refine ⟨?_, fun a h1 h2 => ?_⟩
    · rw [SailCycleOrderK.runImg _ _ st c hrun]
      show imgZ σ0.wgimg = imgZ bootImage
      rw [hb.2.1]
    · exact MachOfPf.noWriteOfPristine Xv6.bcRoLo Xv6.bcRoHi (Nat.le_refl _)
        SrvwmoXv6Adequacy.bcRoHiLe hR hwin a h1 h2
  exact SailCycleOrderK.scoOfInv _ _ st c
    (SailCycleOrderK.invRun _ _ h _ _ _ σ0 (SailCycleOrderK.rbootInit σ0 hb)
      SailCycleOrderK.rbootPin SailCycleOrderK.cleanK SailCycleOrderK.cleanKBack
      SailCycleOrderK.fetchK st c hrun hclean)

/-! ## (5) The corollary machinery (iii)/(iv), conditional on `sailCycleOrderK` -/

/-- (iii) **`fiOfScoK`**: `MachOfPf.Hyps.fi` at M1 from `sailCycleOrderK` (the widened shape). -/
theorem SailCycleOrderK.fiOfScoK (hK : sailCycleOrderK) (σ0 : WGState) (g0 : GState)
    (hb : wbootFacts σ0) (hg0 : g0.gen = 0) (hp0 : g0.pow = false)
    (hfs : diskOf g0.m.devs = Xv6.fsImgDisk) :
    ∀ (st : List (Nat × Wlabel)) (c : Wpcfg Pexv6 Efab) (t : List Expr) (g : GState) (n : Nat)
      (κ : List Obs),
      pfRunST pstepEv pclsEv (candKfetch (Xv6.bcRoLo : Int) (Xv6.bcRoHi : Int)) TsoShadow.cohSrc
        (wpInit (imgZ σ0.wgimg) (efInit σ0.wgdev) (epsInit σ0)) st c →
      MachOfPf.MRun n ([Expr.power], g0) κ (t, g) → MachOfPf.SimRel c st t g →
      ∀ (cpu : CPU) (o : Outcome Register RegisterType) (k : o.ret → SailM Unit) (rs : RegFile)
        (ib : Ibch) (ws : Wstate) (pr : GSet Nat),
        c.pcAgs[cpu.val]? = some ⟨.PHart cpu (.impure (.ok o) k) rs none ib, ws, pr⟩ →
        (o = .barrier .Barrier_RISCV_i →
           (tsoShadow TsoShadow.cohSrc st (hartAgent cpu)).fiArm = true) ∧
        (∀ n w, o = .instrAnnounce n w → sfAnnB n w = true →
           (tsoShadow TsoShadow.cohSrc st (hartAgent cpu)).fiArm = false) := by
  intro st c t g n κ hrun hreach hR cpu o k rs ib ws pr hag
  obtain ⟨hb', ha⟩ := hK σ0 g0 hb hg0 hp0 hfs st c t g n κ hrun hreach hR cpu o k rs ib ws pr hag
  rw [SrvwmoXv6Adequacy.fiArmLastCyc]
  refine ⟨fun h => by rw [hb' h]; rfl, fun n w h hs => ?_⟩
  obtain ⟨base, tvs, e⟩ := ha n w h hs
  rw [e]
  rfl

/-- **`MachOfPf.Hyps` at M1 without `hsco`**, from `sailCycleOrderK`. -/
theorem SailCycleOrderK.m1HypsK (hK : sailCycleOrderK) (σ0 : WGState) (g0 : GState)
    (hb : wbootFacts σ0) (hg0 : g0.gen = 0) (hp0 : g0.pow = false)
    (hfs : diskOf g0.m.devs = Xv6.fsImgDisk) :
    MachOfPf.Hyps (candKfetch (Xv6.bcRoLo : Int) (Xv6.bcRoHi : Int)) g0
      (wpInit (imgZ σ0.wgimg) (efInit σ0.wgdev) (epsInit σ0)) where
  tso := pfStepTsoProposed _
  safe := fun n κs t g hm =>
    (Xv6.xv6FsAdequacy_closed (hlc := Iris.HasLC.hasLC) g0 hg0 hp0 hfs n κs t g hm).1
  cut := MachOfPf.cutIgnore <| MachOfPf.cutOfPristine Xv6.bcRoLo Xv6.bcRoHi (Nat.le_refl _) SrvwmoXv6Adequacy.bcRoHiLe
    g0 _ (SrvwmoXv6Adequacy.winOfText g0 hg0 hp0 hfs)
  fi := SailCycleOrderK.fiOfScoK hK σ0 g0 hb hg0 hp0 hfs

/-- (iv) **M1 without `sailCycleOrder`, from `sailCycleOrderK`**: `srvwmoXv6M1Core`'s statement
without `hsco`, re-running the composition with `m1HypsK`.  (`srvwmoXv6M1` is this at
`sailCycleOrderKOfCycle cycleOkK`, once the per-word half lands.) -/
theorem SailCycleOrderK.srvwmoXv6M1OfK (hK : sailCycleOrderK) (σ0 : WGState) (c : Cand)
    (pst : Nat → List Pexv6) (dv : Nat → Efab)
    (hP : srvwmoXv6M1Premises σ0 c pst dv)
    (g0 : GState) (hg0 : g0.gen = 0) (hp0 : g0.pow = false) (hgd : σ0.wgdev = g0.m.devs.reset)
    (hfs : diskOf g0.m.devs = Xv6.fsImgDisk) :
    ∃ (cf : Wpcfg Pexv6 Efab) (st : List (Nat × Wlabel)) (r : List MachOfPf.PfRec) (n : Nat)
      (t : List Expr) (g : GState),
      pfRunST pstepEv pclsEv (candKfetch (Xv6.bcRoLo : Int) (Xv6.bcRoHi : Int)) TsoShadow.cohSrc
        (wpInit (imgZ σ0.wgimg) (efInit σ0.wgdev) (epsInit σ0)) st cf ∧
      pairAdjacent st ∧
      cf.pcAgs.map Wpagent.paSt = pst c.cdTr.length ∧ cf.pcDev = dv c.cdTr.length ∧
      cfgMatchd cf (stt (candExec c) c.cdTr.length) ∧
      (∀ i, (tsoShadow TsoShadow.cohSrc st i).mem = shadowOf TsoShadow.cohSrc c.cdTr i) ∧
      MachOfPf.contR (candKfetch (Xv6.bcRoLo : Int) (Xv6.bcRoHi : Int))
        (wpInit (imgZ σ0.wgimg) (efInit σ0.wgdev) (epsInit σ0)) [] r cf ∧
      MachOfPf.recLabels r = st ∧
      MachOfPf.MRun n ([Expr.power], g0) (Obs.powerOn :: MachOfPf.pfObsOf r) (t, g) ∧
      MachOfPf.SimRel cf st t g ∧
      (∀ e, e ∈ t → PrimStep.Reducible (e, g)) ∧
      Xv6.xv6TracePure Xv6.fsimgCov Xv6.fsimgSb.sbLogstart g ∧
      Xv6.xv6NiPhi g (Obs.powerOn :: MachOfPf.pfObsOf r) ∧
      Xv6.unionPhiSync (Obs.powerOn :: MachOfPf.pfObsOf r) ∧
      Xv6.textPristine g ∧
      SrvwmoXv6Adequacy.allocprocAns (Obs.powerOn :: MachOfPf.pfObsOf r) := by
  have hb : wbootFacts σ0 := hP.1
  obtain ⟨cf, st, hrun, hadj, h1, h2, h3, h4⟩ := srvwmoXv6M1PfRun σ0 c pst dv hP
  have hH := SailCycleOrderK.m1HypsK hK σ0 g0 hb hg0 hp0 hfs
  obtain ⟨r, hr, hl, n, t, g, hm, hR⟩ :=
    MachOfPf.machRunOfPfRun _ σ0 g0.m.devs g0 hb hgd hg0 hp0 rfl hH st cf hrun hadj
  obtain ⟨hred, hpure, hni, hun, htext, hap⟩ :=
    SrvwmoXv6Adequacy.xv6Concl g0 hg0 hp0 hfs n _ t g hm
  exact ⟨cf, st, r, n, t, g, hrun, hadj, h1, h2, h3, h4, hr, hl, hm, hR, hred, hpure, hni, hun,
    htext hR.pow, hap⟩

end Weak

#print axioms Weak.SailCycleOrderK.sailCycleOrderOfCycle
#print axioms Weak.SailCycleOrderK.sailCycleOrderKOfCycle
#print axioms Weak.SailCycleOrderK.srvwmoXv6M1OfK
