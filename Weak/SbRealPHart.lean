/-
Weak: **allocproc route P, row P-W6 — THE HART ROWS of the realization: one Sail event of a hart,
answered by MachCSL's `evStep` (or the land arm), against the state map `rmemP`** (`PROGRESS-PW6.md` §3
row "hart rows", `notes/twin-machine-conformance.md` cells a–j).  Lean-only, no Rocq twin.  A PRIMED
TWIN: nothing registered imports this file.

The program side of a walk event item (`SbWalk.evData`) is the hart's Sail run: its admin star (register
reads and writes, silent outcomes, the instruction boundary, fetches) and then the realizing pf label (one
memory outcome, or the exclusive pair).  Each row below takes ONE Sail outcome of hart `cpu` at a MachCSL
state `σ` related to the twin state `c` by `rmemP`, and gives the `evStep` answer and the post-state,
together with `rmemP` at the twin's post-state (the same `c` for admin outcomes, `SbCand.nextE c …` for the
realizing label).  The per-row premises are exactly the conformance matrix's (cell letter in brackets):

* `rmemPRegs`/`rmemPSetReg`/`rmemPDropResv` — `rmemP` reads no register; the boundary drops a
  reservation no item boundary holds (`R-resv`);
* `evRegReadP`, `evRegWriteP` (the armed instrument `excOk`, from HSafe as W4's (5)) [p];
* `evFetchP` — the fetch arm at a cut `itv ≤ tvn ≤ ltop` (the matrix's fetch pair: P-W6's `FetchCutP`,
  stated in MachCSL's terms; `fetchOk` from HSafe as W4's (6)) [o, p];
* `evLoadP` — the plain read at the LANDED TOP, its bytes the twin's forwarded-or-top bytes
  (`SbRealP.byteFwdTop`) [a];
* `evStoreP` — the plain write's ISSUE (`SbRealP.rmemPIssue`) [b];
* `evFenceP` — the barrier, every kind but `fence.tso` (F-PW6-3: no `fence.tso` in the image), its drain
  from the twin's (`fenceGuardOf`) and, at `fence.i`, from the walk's fence.i gate (the marker) [c, d];
* `evExReadP` → `rmemPMid` (register-only steps keep it: `midSetReg`) → `evExWriteP` — the exclusive pair:
  MachCSL's exclusive read at the landed top, then its write landing at once (`SbRealP.rmemPRmw`) [f, g];
* `evMmioReadP`/`evMmioWriteP` — MMIO (inert on memory), the `DRIVER_OK` guard from the I/O gate's empty
  buffer ([OWN.152]) [h, i];
* `landStepP` — the land arm: `SbRealP.rmemPLand`, given `ForeignBelowLanded` (F-PW6-1:
  `SbIssueCo.noForeignBelow` through the stamp map) and `¬ kStuck` (HSafe) [j].

Spec: FAITHFUL (proof organisation; every premise is a matrix cell's, all named in the plan).  Lean-only
helpers `SbRealPHart.*`.
-/
import Weak.SbRealP

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open Sail Sail.ConcurrencyInterfaceV1 LeanRV64D
open Lbl PfStepTsoMem SbRealP
open Iris.ProgramLogic

namespace SbRealPHart

/-! # 1. The state map reads no register -/

theorem rmemPRegs (img : Image) (c : SbCand.CandS) (σ : MState) (R : CPU → RegFile) :
    rmemP img c { σ with regs := R } ↔ rmemP img c σ := Iff.rfl

theorem rmemPSetReg (img : Image) (c : SbCand.CandS) (σ : MState) (cpu : CPU) (r : Register)
    (v : RegisterType r) : rmemP img c (σ.setReg cpu r v) ↔ rmemP img c σ := Iff.rfl

/-- The instruction boundary (`hartStep`'s `.pure` arm) and a blocked exclusive read drop the hart's
reservation — none is held between items. -/
theorem rmemPDropResv (img : Image) (c : SbCand.CandS) (σ : MState) (cpu : CPU) (hR : rmemP img c σ) :
    rmemP img c (σ.dropResv cpu) := by
  obtain ⟨himg, hlog, hlogB, hH, hsb, hoth, hresv, hnd, hok⟩ := hR
  refine ⟨himg, hlog, hlogB, hH, hsb, hoth, fun c' => ?_, hnd, σ.okP_dropResv cpu hok⟩
  show updCpu σ.resv cpu none c' = none
  by_cases h : c' = cpu
  · subst h; simp [updCpu]
  · simp only [updCpu, h, if_false]; exact hresv c'

/-! # 2. Register events -/

theorem evRegReadP (cpu : CPU) (σ : MState) (r : Register) :
    evStep cpu (.regRead r) σ (σ.regs cpu r) σ := ⟨rfl, rfl⟩

theorem evRegWriteP (cpu : CPU) (σ : MState) (r : Register) (v : RegisterType r)
    (hex : σ.excOk cpu r v) : evStep cpu (.regWrite r v) σ () (σ.setReg cpu r v) := ⟨rfl, hex⟩

/-! # 3. The fetch (the cut, `FetchCutP`'s consumer) -/

/-- **THE FETCH ROW** [o, p]: at a cut `itv ≤ tvn ≤ ltop` whose landed bytes are the fetched word (the
fetch pair's premise, P-W6's `FetchCutP`), with the armed fetch guard (HSafe), MachCSL's ifetch arm
answers and moves nothing. -/
theorem evFetchP (cpu : CPU) (σ : MState) (n va : Nat)
    (req : Mem_read_request n va Arch.pa Arch.translation Arch.arch_ak) (w : BitVec (8 * n))
    (hram : ramBytes req.pa n) (hif : akIfetch req.access_kind = true) (hfo : σ.fetchOk cpu req.pa)
    (hcut : ∃ tvn, σ.itv cpu ≤ tvn ∧ tvn ≤ σ.ltop ∧
      σ.mem.readBytesP σ.lp (ifetchAgent cpu) tvn req.pa n w) :
    evStep cpu (.memRead n va req) σ (.Ok (w, none)) σ := by
  obtain ⟨tvn, h1, h2, h3⟩ := hcut
  exact .inr (.inl ⟨hram, hif, hfo, tvn, w, h1, h2, h3, rfl, rfl⟩)

/-! # 4. The plain read at the landed top -/

/-- **THE LOAD ROW** [a]: a plain RAM read whose bytes are the twin's forwarded-or-top bytes (the walk's
read gate makes every member read a TOP read) is MachCSL's plain read at `tvn = σ.ltop`; only the read
side moves. -/
theorem evLoadP (img : Image) (c : SbCand.CandS) (σ : MState) (cpu : CPU) (n va : Nat)
    (req : Mem_read_request n va Arch.pa Arch.translation Arch.arch_ak) (w : BitVec (8 * n))
    (aq : Bool) (base : Int) (ts : List Nat) (vs : List (BitVec 8))
    (hR : rmemP img c σ) (hram : ramBytes req.pa n) (hpl : akPlain req.access_kind = true)
    (pa : PAddr) (hpa : req.pa = pa)
    (hval : ∀ j, j < n →
      (SbCand.fwdByte (c.sb (hartAgent cpu)) (paZ (pa + BitVec.ofNat 64 j))).or
        (topByte img c.ms.msLog (paZ (pa + BitVec.ofNat 64 j))) = some (nthByte w j)) :
    evStep cpu (.memRead n va req) σ (.Ok (w, none)) (σ.afterLoad cpu req.pa n σ.ltop) ∧
      rmemP img (SbCand.nextE c (hartAgent cpu) (LLoad aq base ts vs))
        (σ.afterLoad cpu req.pa n σ.ltop) := by
  obtain ⟨htv, hcoh⟩ := topLoadEnabled img c σ hR cpu req.pa n
  refine ⟨.inr (.inr (.inl ⟨hram, hpl, σ.ltop, w, htv, Nat.le_refl _, hcoh, fun j hj => ?_, rfl, rfl⟩)),
    rmemPLoad img c σ cpu req.pa n aq base ts vs hR⟩
  subst hpa
  rw [byteFwdTop img c σ hR cpu _ (hram j hj)]
  exact hval j hj

/-! # 5. The plain write: its ISSUE -/

/-- **THE STORE ROW** [b]: a plain RAM write ISSUES (`MState.issue`), the twin's `LStore` issues. -/
theorem evStoreP (img : Image) (c : SbCand.CandS) (σ : MState) (cpu : CPU) (n va : Nat)
    (req : Mem_write_request n va Arch.pa Arch.translation Arch.arch_ak) (w : BitVec (8 * n))
    (vs : List (BitVec 8)) (k : WmClass) (hR : rmemP img c σ) (hram : ramBytes req.pa n)
    (hnx : akExcl req.access_kind = false) (hv : req.value = some w) (hd : vs.length = n)
    (hb : ∀ j, j < n → vs[j]? = some (nthByte w j)) :
    evStep cpu (.memWrite n va req) σ (.Ok (some true)) (σ.issue cpu req.pa n w) ∧
      rmemP img (SbCand.nextE c (hartAgent cpu) (LStore false (paZ req.pa) vs k))
        (σ.issue cpu req.pa n w) :=
  ⟨.inr (.inl ⟨hram, hnx, w, hv, rfl, rfl⟩), rmemPIssue img c σ cpu req.pa n w vs k hram hd hb hR⟩

/-! # 6. The barrier -/

/-- **THE FENCE ROW** [c, d]: a barrier other than `fence.tso` (F-PW6-3), its twin label `ebarLabel b`;
its drain from the twin's (`pw ∧ sr`) and, at `fence.i`, from the walk's `fence.i` gate (the marker
O-P-W1-a: the kept drain [OWN.146]). -/
theorem evFenceP (img : Image) (c : SbCand.CandS) (σ : MState) (cpu : CPU) (b : barrier_kind)
    (pr pw sr sw : Bool) (hR : rmemP img c σ) (htso : b ≠ .Barrier_RISCV_tso)
    (hl : ebarLabel b = .LFence pr pw sr sw)
    (hdr : SbCand.drains pw sr = true → c.sb (hartAgent cpu) = [])
    (hfi : fenceIfetch b = true → σ.sb cpu = []) :
    evStep cpu (.barrier b) σ () (σ.fence cpu b) ∧
      rmemP img (SbCand.nextE c (hartAgent cpu) (LFence pr pw sr sw)) (σ.fence cpu b) :=
  ⟨⟨fenceGuardOf img c σ cpu b pr pw sr sw hl hR hdr hfi, rfl⟩,
    rmemPFence img c σ cpu b pr pw sr sw (fenceEpochOfEbar b htso pr pw sr sw hl) hR⟩

/-- **M-S2's MACHINE RULE, NAMED** ([OWN.156], supersedes [OWN.146]): MachCSL's `fence.i` is NON-DRAINING —
the barrier guard `fenceDrainsSb` is the data-side W→R drain `fenceDrains` alone (Zifencei: `fence.i` orders
no data access; riscv.cat has no `fence.i`).  FALSE at the current tip (`fenceDrainsSb` still joins
`fenceIfetch`, the kept drain EX-FENCEI-1); TRUE by definition once w1's M-S2 lands (`fenceDrainsSb b :=
fenceDrains b`), so every row below stated against it closes then with `fun _ => rfl`. -/
def MS2FenceINoDrain : Prop := ∀ b : barrier_kind, fenceDrainsSb b = fenceDrains b

/-- The barrier guard under M-S2: the twin's data drain alone. -/
theorem fenceGuardNd (img : Image) (c : SbCand.CandS) (σ : MState) (cpu : CPU) (b : barrier_kind)
    (pr pw sr sw : Bool) (hl : ebarLabel b = .LFence pr pw sr sw) (hR : rmemP img c σ)
    (hms2 : MS2FenceINoDrain) (hdr : SbCand.drains pw sr = true → c.sb (hartAgent cpu) = []) :
    fenceDrainsSb b = true → σ.sb cpu = [] := by
  intro h
  rw [hms2 b, fenceDrainsOfEbar b pr pw sr sw hl] at h
  have := hdr (by simpa [SbCand.drains] using h)
  have hf := hR.2.2.2.2.1 cpu
  rw [this] at hf
  exact forall2NilRight hf

/-- **THE FENCE ROW FOR THE NON-DRAINING MACHINE** [c, d] (M-S2, [OWN.156]): a barrier other than `fence.tso`
(F-PW6-3), its twin label `ebarLabel b`, its drain from the twin's (`pw ∧ sr`) ALONE — `fence.i` (twin label
`LFence false false false false`, no S-R gate: `SbOrdR.enbLR`'s fence arm asks nothing) goes with the hart's
buffer non-empty (the `userret` shape of F-CM-3).  No walk gate and no fetch marker. -/
theorem evFenceNdP (img : Image) (c : SbCand.CandS) (σ : MState) (cpu : CPU) (b : barrier_kind)
    (pr pw sr sw : Bool) (hR : rmemP img c σ) (htso : b ≠ .Barrier_RISCV_tso)
    (hl : ebarLabel b = .LFence pr pw sr sw) (hms2 : MS2FenceINoDrain)
    (hdr : SbCand.drains pw sr = true → c.sb (hartAgent cpu) = []) :
    evStep cpu (.barrier b) σ () (σ.fence cpu b) ∧
      rmemP img (SbCand.nextE c (hartAgent cpu) (LFence pr pw sr sw)) (σ.fence cpu b) :=
  ⟨⟨fenceGuardNd img c σ cpu b pr pw sr sw hl hR hms2 hdr, rfl⟩,
    rmemPFence img c σ cpu b pr pw sr sw (fenceEpochOfEbar b htso pr pw sr sw hl) hR⟩

/-- `fence.i`'s twin label asks no drain (so the S-R gate asks nothing of it). -/
theorem fenceIDrainsFalse (pr pw sr sw : Bool) (hl : ebarLabel .Barrier_RISCV_i = .LFence pr pw sr sw) :
    SbCand.drains pw sr = false := by
  have h : (Wlabel.LFence false false false false) = .LFence pr pw sr sw := hl
  cases h
  rfl

/-! # 7. The exclusive pair -/

/-- **INSIDE THE EXCLUSIVE PAIR**: the MachCSL state is the exclusive read's post-state of a related
`σ0` (bytes `r` its landed top), up to the registers the admin steps between the halves write. -/
def rmemPMid (img : Image) (c : SbCand.CandS) (σ : MState) (cpu : CPU) (pa : PAddr) (n : Nat)
    (r : BitVec (8 * n)) (acq : Bool) : Prop :=
  ∃ σ0, rmemP img c σ0 ∧ σ0.mem.topBytesL σ0.lp pa n r ∧
    σ = { σ0.afterExcl cpu pa n r acq with regs := σ.regs }

/-- A register write between the halves keeps the pair relation. -/
theorem midSetReg (img : Image) (c : SbCand.CandS) (σ : MState) (cpu cpu' : CPU) (pa : PAddr) (n : Nat)
    (r : BitVec (8 * n)) (acq : Bool) (rg : Register) (v : RegisterType rg)
    (h : rmemPMid img c σ cpu pa n r acq) : rmemPMid img c (σ.setReg cpu' rg v) cpu pa n r acq := by
  obtain ⟨σ0, h1, h2, h3⟩ := h
  refine ⟨σ0, h1, h2, ?_⟩
  rw [h3]

/-- The twin's top bytes are MachCSL's landed top bytes. -/
theorem topBytesOfTwin (img : Image) (c : SbCand.CandS) (σ : MState) (hR : rmemP img c σ) (pa : PAddr)
    (n : Nat) (r : BitVec (8 * n)) (hram : ramBytes pa n)
    (hv : ∀ j, j < n → topByte img c.ms.msLog (paZ (pa + BitVec.ofNat 64 j)) = some (nthByte r j)) :
    σ.mem.topBytesL σ.lp pa n r := fun j hj => by
  rw [topLEq img c σ hR _ (hram j hj)]; exact hv j hj

/-- **THE EXCLUSIVE READ** [f, g]: at the landed top (bytes `r`), unblocked — no reservation between
items (`R-resv`) and no own pending entry on the footprint (the twin's `amoOk`, `amoGuardOf`). -/
theorem evExReadP (img : Image) (c : SbCand.CandS) (σ : MState) (cpu : CPU) (n va : Nat)
    (req : Mem_read_request n va Arch.pa Arch.translation Arch.arch_ak) (r : BitVec (8 * n))
    (hR : rmemP img c σ) (hram : ramBytes req.pa n) (hx : akExcl req.access_kind = true)
    (htop : σ.mem.topBytesL σ.lp req.pa n r)
    (hamo : SbCand.amoOk (c.sb (hartAgent cpu)) (paZ req.pa) n) :
    evStep cpu (.memRead n va req) σ (.Ok (r, none))
        (σ.afterExcl cpu req.pa n r (akAcq req.access_kind)) ∧
      rmemPMid img c (σ.afterExcl cpu req.pa n r (akAcq req.access_kind)) cpu req.pa n r
        (akAcq req.access_kind) := by
  have hno : ¬ othersReserve σ.resv cpu req.pa n := by
    rintro ⟨c', -, rr, hrr, -⟩
    rw [hR.2.2.2.2.2.2.1 c'] at hrr; cases hrr
  -- the read half asks only `¬ sbOverlaps` (`amoGuardOf`'s first half does not read the access kind)
  have hg := amoGuardOf img c σ cpu req.pa n (.AK_ifetch ()) hR hram hamo
    (fun h => by simp [akRel] at h)
  exact ⟨.inr (.inr (.inr ⟨hram, hx, hno, hg.1, r, htop, rfl, rfl⟩)), σ, hR, htop, rfl⟩

/-- **THE EXCLUSIVE WRITE** [f, g]: lands at once (`MState.storeL`), guarded by `landNowOk` (the twin's
`amoOk` and `.rl` condition) and no other reservation; the pair is the twin's `LRmw`. -/
theorem evExWriteP (img : Image) (c : SbCand.CandS) (σ : MState) (cpu : CPU) (n va : Nat)
    (req : Mem_write_request n va Arch.pa Arch.translation Arch.arch_ak) (r w : BitVec (8 * n))
    (acq : Bool) (aq rl : Bool) (ts : List Nat) (rvs wvs : List (BitVec 8)) (k : WmClass)
    (hM : rmemPMid img c σ cpu req.pa n r acq) (hram : ramBytes req.pa n)
    (hx : akExcl req.access_kind = true) (hv : req.value = some w)
    (hamo : SbCand.amoOk (c.sb (hartAgent cpu)) (paZ req.pa) n)
    (hrl : akRel req.access_kind = true → c.sb (hartAgent cpu) = [])
    (hd : wvs.length = n) (hb : ∀ j, j < n → wvs[j]? = some (nthByte w j)) :
    evStep cpu (.memWrite n va req) σ (.Ok (some true)) (σ.storeL cpu req.pa n w) ∧
      rmemP img (SbCand.nextE c (hartAgent cpu) (LRmw aq rl (paZ req.pa) ts rvs wvs k))
        (σ.storeL cpu req.pa n w) := by
  obtain ⟨σ0, hR0, htop, hσ⟩ := hM
  have hg := amoGuardOf img c σ0 cpu req.pa n req.access_kind hR0 hram hamo hrl
  have hno : ¬ othersReserve σ.resv cpu req.pa n := by
    rintro ⟨c', hc', rr, hrr, -⟩
    rw [hσ] at hrr
    have : (σ0.afterExcl cpu req.pa n r acq).resv c' = σ0.resv c' := by simp [updCpu, hc']
    rw [this, hR0.2.2.2.2.2.2.1 c'] at hrr; cases hrr
  have hnow : σ.landNowOk cpu req.pa n req.access_kind := by
    rw [hσ]; exact hg.2
  refine ⟨.inr (.inr ⟨hram, hx, w, hv, hno, hnow, rfl, rfl⟩), ?_⟩
  have h := rmemPRmw img c σ0 cpu req.pa n r w acq rl ts rvs wvs k hram hd hb htop hR0
  rw [hσ]
  exact h

/-! # 8. MMIO -/

/-- **THE MMIO READ** [h]: inert on memory. -/
theorem evMmioReadP (img : Image) (c : SbCand.CandS) (σ : MState) (cpu : CPU) (n va : Nat)
    (req : Mem_read_request n va Arch.pa Arch.translation Arch.arch_ak) (w : BitVec (8 * n))
    (ds' : DevStates) (kd : IoKind) (base : Int) (vs : List (BitVec 8)) (hR : rmemP img c σ)
    (hdev : devBytes req.pa n) (hrd : devRead σ.devs req.pa n = some (w, ds')) :
    evStep cpu (.memRead n va req) σ (.Ok (w, none)) { σ with devs := ds' } ∧
      rmemP img (SbCand.nextE c (hartAgent cpu) (LIo kd base vs)) { σ with devs := ds' } :=
  ⟨.inl ⟨hdev, w, ds', hrd, rfl, rfl⟩, rmemPIo img c σ _ kd base vs ds' hR⟩

/-- **THE MMIO WRITE** [h, i]: inert on memory; the `DRIVER_OK` guard holds because the I/O gate
([OWN.152]) found the hart's buffer empty — hence MachCSL's (`R-sb`). -/
theorem evMmioWriteP (img : Image) (c : SbCand.CandS) (σ : MState) (cpu : CPU) (n va : Nat)
    (req : Mem_write_request n va Arch.pa Arch.translation Arch.arch_ak) (w : BitVec (8 * n))
    (ds' : DevStates) (kd : IoKind) (base : Int) (vs : List (BitVec 8)) (hR : rmemP img c σ)
    (hdev : devBytes req.pa n) (hv : req.value = some w) (hwr : devWrite σ.devs req.pa n w = some ds')
    (hemp : c.sb (hartAgent cpu) = []) :
    evStep cpu (.memWrite n va req) σ (.Ok (some true)) { σ with devs := ds' } ∧
      rmemP img (SbCand.nextE c (hartAgent cpu) (LIo kd base vs)) { σ with devs := ds' } := by
  have hsb : σ.sb cpu = [] := by
    have h := hR.2.2.2.2.1 cpu
    rw [hemp] at h
    exact forall2NilRight h
  exact ⟨.inl ⟨hdev, w, ds', hv, hwr, rfl, rfl, σ.drvOkGuard_of_sb_nil cpu hsb⟩,
    rmemPIo img c σ _ kd base vs ds' hR⟩

/-! # 9. The land arm -/

/-- **THE LAND ROW** [j]: a twin landing under `SbPol.epoch` of hart `cpu`'s `k`-th entry is MachCSL's land
arm (silent, the hart's computation stuttering), given F-PW6-1's `ForeignBelowLanded` and the hart not
stuck (HSafe). -/
theorem landStepP (img : Image) (c : SbCand.CandS) (gen : Nat) (cpu : CPU) (m : SailM Unit) (g : GState)
    (k : Nat) (hR : rmemP img c g.m) (hpol : SbPol.epochOk (c.sb (hartAgent cpu)) k)
    (hl : threadLive g gen) (hks : ¬ g.m.kStuck cpu m)
    (hfor : ∀ p, (g.m.sb cpu)[k]? = some p → ForeignBelowLanded g.m cpu p.1) :
    ∃ t, PrimStep.primStep (Expr.hart gen cpu m, g) ([] : List Obs)
        (.hart gen cpu m, { g with m := g.m.land cpu t }, []) ∧
      rmemP img (SbCand.nextL c (hartAgent cpu) k) (g.m.land cpu t) := by
  obtain ⟨p, hp, hland⟩ := rmemPLand img c g.m cpu k hR hpol
  obtain ⟨hok, hR'⟩ := hland (hfor p hp)
  exact ⟨p.1, primStep_hart_land hl hks hok, hR'⟩

#print axioms Weak.SbRealPHart.evLoadP
#print axioms Weak.SbRealPHart.evExWriteP
#print axioms Weak.SbRealPHart.evMmioWriteP
#print axioms Weak.SbRealPHart.landStepP

end SbRealPHart

end Weak
