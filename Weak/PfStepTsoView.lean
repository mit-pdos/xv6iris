/-
Weak: **W2b — the VISIBILITY (`R-view`) half of `pfStepTso`** (allocproc plan
`notes/weak-allocproc-plan.md` §C Stage 0 "W2", §B(10) "The redesign", `R-view` = EQUALITY
through `tsoShadow`; `notes/W2-spike.md` §R and its table).

Lean-only (no Rocq source).  For every memory label row of the W2 table: from a TsoMem state
whose per-hart READ SIDE (`tv`, `hr.rv`, `hr.coh`, `hr.acq`, `itv`) EQUALS the step-list shadow
(`PfStepTsoView.viewRel stamp σ st`: `tsoShadow stamp st (hartAgent cpu)`), the TsoMem post-state
— stated against the COMPILED `MState` functions (`afterLoad`, `store`, `afterExcl`, `fence`,
`storeDma`, the identity) — has read fields EQUAL to the shadow after the step, and the view TsoMem
reads at (`PfStepTsoView.minView`, the shadow's MINIMAL legal view `shTvn`) meets TsoMem's side
conditions (`tv ≤ tvn ≤ top`, `cohOk`; `itv ≤ tvn ≤ top` for a fetch).  The coherence stamp that
matches the compiled TsoMem (W-COH, G2-Q RULED (a′) BOTH components [OWN.20][OWN.23]) is the
merged instance `TsoShadow.cohSrc`; the rows that never touch `coh` (exclusive read, fences,
`fence.i` / the `sfence.vma` marker, fetches, inert and foreign-agent steps) hold for EVERY stamp
(instance-independent, plan §C W2 [R14.2]).

NOT here (W2a, `Weak/PfStepTsoMem.lean`, the MEMORY half): byte histories (`R-hist`, `histOf`),
`readBytes`/`topBytes`/`writeBytes`, `R-log` (`σ.log = stAuthors st` is a HYPOTHESIS of the rows
that read the top or `ownPub`), `R-img`, `R-resv` (`¬ othersReserve`/`¬ anyReserve`).  The one
seam is the per-byte SOURCE list of a plain load: the TsoMem side computes it from the histories
(`FlatMem.loadSrcs`, W-COH), the shadow from the pf log (`PfStepTsoView.shLoadSrcs` = the
`shSrc` map `TsoShadow.shStep` uses); `rowLoad` takes their agreement at the minimal view as the
hypothesis `hsrc` (W2a discharges it from `R-hist`).

## The (↓) table, with the faithful / stronger / weaker column [R9.s4][R10.s5][R11.s4]

Each row: the pf label (and its source), the TsoMem match (compiled function), the view TsoMem
reads at, the Lean theorem of THIS file (the `R-view` half), and the mark of the TsoMem behaviour
on that row w.r.t. the spec (RVWMO / riscv.cat, Sail, Zifencei, PMAs; owner rule 2026-10-09):
*faithful* = the spec's behaviour, *stronger* = TsoMem forbids something the spec allows,
*weaker* = TsoMem allows something the spec forbids.  `(↓)` = a TsoMem step exists with the same
bytes into a related state (✓), conditionally (cond.), or not applicable.

| label (source) | TsoMem match | view / side conditions | Lean (`PfStepTsoView.`) | (↓) | mark |
|---|---|---|---|---|---|
| `LSilent` (regRead, choose, announce of a branch, cacheOp, tlbi, the lost-SC retry) | 0 steps (stutter) or an `evStep` arm with `σ' = σ` | none | `viewRelInert` (+ `sameReadRefl`) | ✓ | faithful (no memory event) |
| `LRegW` / `LCtrl` (dependency views) | `regWrite` → `σ.setReg`, or none | none | `viewRelInert` (+ `sameReadSetReg`) | ✓ | WEAKER: TsoMem has no dependency order (ppo 9–13), the sound direction (§0 F1) |
| `LInstr` (cycle boundary / announce) | `hartStep .pure` (`σ' = σ.dropResv cpu`) / `instrAnnounce` (`σ' = σ`) | none | `viewRelInert` | ✓ | faithful for the views; the boundary CLEARS the hart's reservation (W-RSV, D19 (b) form (i-a): Zalrsc lets a reservation be invalidated at any time; the pf twin's `instrPost` clears `wRes` alike — `R-resv`, `MachOfPf.rmemDropResv`) |
| `LIFetch`, M1 (`candKfetch`, pristine text) | fetch arm, `σ' = σ` | `tvn := itv` (= the shadow's): `itv ≤ tvn ≤ top` | `rowFetchM1` | ✓ (bytes: W2a) | faithful: Zifencei permits a non-coherent i-cache; `candKfetch` is a premise, not a semantics change |
| `LIFetch`, M2 (cut form, view `q`) | fetch arm at `q`, `σ' = σ` | `itv ≤ q ≤ top` given the shadow's `itv ≤ q` (W5d's `itvOf`) | `rowFetchM2` | cond. (§B(4)(iii) (i)–(ii)) | faithful modulo the graph-tier fetch model `gzFetch` (trusted, no reference model, D27) |
| hart `LLoad` (plain, `pa` in RAM) | `afterLoad cpu pa n tvn` | `tvn := minView` = `max(F, max_{foreign j} t_j)`: `tv ≤ tvn ≤ top`, `cohOk` (and `tvn ≤` every `scaOkT` witness: `minViewLeSca`) | `rowLoad` (`cohSrc`) | ✓ iff (★), discharged by `candScaT` (bytes: W2a) | faithful: the foreign-only stamp is rule 2 exactly ([OWN.23]); `candScaT` is FAITHFUL at Stage 2 (derived, G1-Q (e)) and ISA-faithful for naturally aligned loads (D20) — STRONGER only as a premise on a misaligned load (N10, out of scope) |
| disk `DRead` (`LLoad aq false` by agent `NCPU`) | `dmaRead`, `σ' = σ` | none on views (the TOP: `dmaView`) | `viewRelForeign` (`diskNotHart`) | ✓ under `candDiskLat` (bytes: W2a) | STRONGER: reads at the top — the device model of record over the appendix's DEVICE sentence (G3, F6; G3-Q (a″) [OWN.17]) |
| hart `LStore` | `store cpu pa n w false` | none on views (append at the top) | `rowStore` (`cohSrc`) | ✓ (`¬ othersReserve`: W2a) | the `coh` RESET is faithful (rule 2's `po-loc-no-w`, [R11.1][OWN.21]); `resv := none` faithful (Zalrsc); the single store order is STRONGER (no W→W reordering / load buffering, §0 F1 (i)) |
| disk `DWriteDev` STORE (`LStore false` by agent `NCPU`; W-DISK: the fabric delta in the same step) | `storeDma` + `setDev` (`dmaWrite`'s moving guard), no hart view moves | none | `rowDiskWrite` = `viewRelForeign` (+ `sameReadStoreDma`, `sameReadSetDev`) | ✓ (`¬ anyReserve`: W2a) | faithful for the views; DMA at the top is the named device model (F6) |
| disk `DWriteDev` SKIP / ABORT (`LSilent`), `DPop` (`LDev`) (W-DISK) | `setDev` only (`dmaWrite`'s no-op arm with the folded moves; the guard-pop) | none | `rowDiskDevMove` = `viewRelForeign` (+ `sameReadSetDev`) | ✓ | views faithful (no memory event) |
| `LExLoad aq` | `afterExcl cpu pa n w aq` | none (reads the top) | `rowExLoad` (any stamp) | views ✓ given `R-view` equality (bytes `topBytes`: W2a) | `tv := top` iff `aq`, `rv := top`: FAITHFUL once the log is gmo-ordered (rule 5 / rule 4, G1/G1′ under `candScaT`, G1-Q (e)); the reservation's blocking lasts only within the issuing instruction (W-RSV: cleared at the boundary) — FAITHFUL for AMOs (D19 (b)) |
| `LExStore rl` | `store cpu pa n w true` | none | `rowExStore` (`cohSrc`) | ✓ | `tv := top + 1` iff the pair is `aq`: faithful (rule 5, as above); `coh` reset faithful ([R14.s3]); `resv := none` faithful |
| `LFence pr pw sr sw` (`ebarNow b`, the 10 non-`fence.i` kinds incl. `fence.tso`) | `fence cpu b` | none | `rowFence` (any stamp) | ✓ | faithful for the R-successor kinds (rule 4: a W→R edge drains, an R→R edge acquires); the W-successor kinds (`rw,w`, `w,w`, `r,w`) are no-ops because the single order is STRONGER (D7 (i)) |
| `LFence` false×4 at `fence.i` (`fiArm`) | `fence cpu .Barrier_RISCV_i`: `itv` raised, `tv` fixed | none | `rowFence` | ✓ | faithful: Zifencei (own stores fetched after `fence.i`); no RVWMO ordering [OWN.15] |
| `LFence` false×4 = the `sfence.vma` marker (`¬ fiArm`) | `instrAnnounce`, `σ' = σ` | none | `rowSfenceMarker` (any stamp) | ✓ | faithful (no RVWMO ordering of data, [OWN.15]) |
| parked `fence rw,w` (`fence.tso`'s park; no label) | 0 steps | none | — (`ShSt.fenceNoSucc`) | ✓ | STRONGER globally (W→W free from the single order, D7 (i)) |
| `LDev` (hart MMIO `rd`/`wr`, any payload) | MMIO arm, `σ' = {σ with devs}` | none | `viewRelInert` (+ `sameReadDevs`) | ✓ (`R-dev`: W4) | views faithful; I/O ordering is the named platform assumption `ioResidueGmo` (W13, STRONGER than RVWMO + PMAs) |
| `LDev` (disk START, device moves, PLIC pins) | device-thread steps (`setDev`/`setRt`/`setReg`) | none | `viewRelInert` / `viewRelForeign` (+ `sameRead*`) | structural (D51) | views faithful |
| `LRmw` | none | — | — | N/A (`pstepEv` never emits it) | — |

The rows' arguments per D19 (b) (§B(10)): the hart `LStore`/disk store need `¬ othersReserve`
/ `¬ anyReserve` only against in-flight reservations (W2a, from `pairAdjacent`); `LExStore` needs
nothing of the own reservation.

Deviations from the plan's text: (1) `R-log` (`σ.log = stAuthors st`) is a hypothesis, not proved
(W2a's half); (2) a plain load's per-byte source agreement is the hypothesis `hsrc` (the seam with
W2a, above); (3) the hart-index of the shadow is the agent `hartAgent cpu` (TsoShadow deviation 1);
(4) `rowFence` needs the shadow's `fiArm` exactly at `fence.i` (`emFenceI`'s criterion) and
`rowSfenceMarker` its negation — facts of the Sail cycle's event order, the named premise
`sailCycleOrder` [OWN.35] (`Weak/SrvwmoXv6Adequacy.lean`, derived for the shadow by `fiOfSco`);
`sailCycleOrder_holds` (W-SCO (A), `Weak/SailCycleOrderK.lean`) proves it for every instruction [R32.s2]; (5) `LDev` is matched by a WILDCARD arm only (`lbInert`), so W13 (E)/(I)'s payload changes
join without a rebase.
-/
import Weak.TsoShadow
import Weak.WeakEvInst

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open Sail Sail.ConcurrencyInterfaceV1 LeanRV64D
open TsoShadow

namespace PfStepTsoView

/-! ## (0) Addresses: the pf footprint byte `paZ pa + j` is TsoMem's `pa + j` (no wrap) -/

theorem pow64 : (2 : Nat) ^ 64 = 18446744073709551616 := rfl

/-- A DRAM footprint does not wrap around the address space. -/
theorem ramBytesFit {pa : PAddr} {n : Nat} (h : ramBytes pa n) :
    pa.toNat + n < 18446744073709551616 := by
  have hlt : pa.toNat < 18446744073709551616 := pa.isLt
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · omega
  · refine Decidable.byContradiction (fun hc => ?_)
    have hj : 18446744073709551615 - pa.toNat < n := by omega
    obtain ⟨-, h1⟩ := h _ hj
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, ramEnd, pow64] at h1
    rw [Nat.mod_eq_of_lt (a := 18446744073709551615 - pa.toNat) (by omega),
      Nat.mod_eq_of_lt (by omega)] at h1
    omega

theorem paZAddFit (pa : PAddr) (n j : Nat) (hfit : pa.toNat + n < 18446744073709551616)
    (hj : j < n) : paZ (pa + BitVec.ofNat 64 j) = accAddr (paZ pa) j :=
  paZAdd pa j (by simp only [paZ]; omega)

theorem paZInj {a b : PAddr} (h : paZ a = paZ b) : a = b := by
  apply BitVec.eq_of_toNat_eq
  simp only [paZ] at h
  omega

theorem footIdxPaAt (pa : PAddr) (n j : Nat) (hfit : pa.toNat + n < 18446744073709551616)
    (hj : j < n) : footIdx (paZ pa) n (paZ (pa + BitVec.ofNat 64 j)) = some j := by
  rw [paZAddFit pa n j hfit hj]
  exact footIdxAcc _ _ _ hj

theorem footIdxPaSome (pa pa' : PAddr) (n j : Nat) (hfit : pa.toNat + n < 18446744073709551616)
    (h : footIdx (paZ pa) n (paZ pa') = some j) : j < n ∧ pa' = pa + BitVec.ofNat 64 j := by
  obtain ⟨hj, he⟩ := (footIdxSome _ _ _ _).1 h
  exact ⟨hj, paZInj (he.trans (paZAddFit pa n j hfit hj).symm)⟩

theorem footIdxPaNone (pa pa' : PAddr) (n : Nat) (hfit : pa.toNat + n < 18446744073709551616)
    (h : footIdx (paZ pa) n (paZ pa') = none) : ∀ j, j < n → pa' ≠ pa + BitVec.ofNat 64 j := by
  intro j hj he
  subst he
  rw [footIdxPaAt pa n j hfit hj] at h
  cases h

/-! ## (1) `R-view`: the TsoMem read side EQUALS the shadow -/

/-- Hart `cpu`'s read side in `σ` equals the shadow `f` (memory fields and `itv`; `coh` through
the address seam `paZ`). -/
structure hartRel (σ : MState) (cpu : CPU) (f : ShFull) : Prop where
  tvEq : σ.tv cpu = f.mem.tv
  rvEq : (σ.hr cpu).rv = f.mem.rv
  cohEq : ∀ pa : PAddr, (σ.hr cpu).coh pa = f.mem.coh (paZ pa)
  acqEq : (σ.hr cpu).acq = f.mem.acq
  itvEq : σ.itv cpu = f.itv

/-- **`R-view`** (plan §B(10)): every hart's TsoMem read side is the step-list shadow's. -/
def viewRel (stamp : CohStamp) (σ : MState) (st : List (Nat × Wlabel)) : Prop :=
  ∀ cpu : CPU, hartRel σ cpu (tsoShadow stamp st (hartAgent cpu))

/-- Two TsoMem states with the same read side (every hart). -/
def sameRead (σ σ' : MState) : Prop := σ'.tv = σ.tv ∧ σ'.hr = σ.hr ∧ σ'.itv = σ.itv

theorem sameReadRefl (σ : MState) : sameRead σ σ := ⟨rfl, rfl, rfl⟩

theorem sameReadSetReg (σ : MState) (cpu : CPU) (r : Register) (v : RegisterType r) :
    sameRead σ (σ.setReg cpu r v) := ⟨rfl, rfl, rfl⟩

theorem sameReadDevs (σ : MState) (ds : DevStates) : sameRead σ { σ with devs := ds } :=
  ⟨rfl, rfl, rfl⟩

theorem sameReadSetDev (σ : MState) (d : DevId) (s : DevSt d) : sameRead σ (σ.setDev d s) :=
  ⟨rfl, rfl, rfl⟩

theorem sameReadSetRt (σ : MState) (d : DevId) (rt : DevRt) : sameRead σ (σ.setRt d rt) :=
  ⟨rfl, rfl, rfl⟩

theorem sameReadStoreDma (σ : MState) (pa : PAddr) (n : Nat) (w : BitVec (8 * n)) :
    sameRead σ (σ.storeDma pa n w) := ⟨rfl, rfl, rfl⟩

theorem sameReadDropResv (σ : MState) (cpu : CPU) : sameRead σ (σ.dropResv cpu) := ⟨rfl, rfl, rfl⟩

theorem sameReadTrans {σ1 σ2 σ3 : MState} (h1 : sameRead σ1 σ2) (h2 : sameRead σ2 σ3) :
    sameRead σ1 σ3 :=
  ⟨h2.1.trans h1.1, h2.2.1.trans h1.2.1, h2.2.2.trans h1.2.2⟩

/-- The relation reads only the memory fields and `itv` of the shadow. -/
theorem hartRelCongr {σ : MState} {cpu : CPU} {f f' : ShFull} (h : hartRel σ cpu f)
    (hm : f'.mem = f.mem) (hi : f'.itv = f.itv) : hartRel σ cpu f' :=
  ⟨by rw [hm]; exact h.tvEq, by rw [hm]; exact h.rvEq, by rw [hm]; exact h.cohEq,
   by rw [hm]; exact h.acqEq, by rw [hi]; exact h.itvEq⟩

/-- A hart whose read side a step leaves alone stays related. -/
theorem hartRelOther (σ σ' : MState) (c : CPU) (f : ShFull) (h : hartRel σ c f)
    (htv : σ'.tv c = σ.tv c) (hhr : σ'.hr c = σ.hr c) (hitv : σ'.itv c = σ.itv c) :
    hartRel σ' c f :=
  ⟨by rw [htv]; exact h.tvEq, by rw [hhr]; exact h.rvEq, by rw [hhr]; exact h.cohEq,
   by rw [hhr]; exact h.acqEq, by rw [hitv]; exact h.itvEq⟩

/-- BOOT: TsoMem's power-on read side (`tv = itv = 0`, `HRead.zero`; `Lang.lean:300,315`) is the
shadow of the empty step list. -/
theorem viewRelNil (stamp : CohStamp) (σ : MState) (htv : ∀ c, σ.tv c = 0)
    (hhr : ∀ c, σ.hr c = HRead.zero) (hitv : ∀ c, σ.itv c = 0) : viewRel stamp σ [] := by
  intro c
  refine ⟨?_, ?_, fun pa => ?_, ?_, ?_⟩
  · rw [htv c]; rfl
  · rw [hhr c]; rfl
  · rw [hhr c]; rfl
  · rw [hhr c]; rfl
  · rw [hitv c]; rfl

/-! ## (2) The shadow after one more step -/

theorem tsoRunSnoc (stamp : CohStamp) (i : Nat) (st : List (Nat × Wlabel)) (y : Nat × Wlabel) :
    tsoRun stamp i (st ++ [y]) = shActF stamp i (tsoRun stamp i st) y := by
  simp [tsoRun, List.foldl_append]

/-- THE SNOC LAW: the viewer's own step moves its shadow by `shStepF` at the prefix's authors;
any other agent's step leaves it. -/
theorem tsoShadowSnoc (stamp : CohStamp) (st : List (Nat × Wlabel)) (j : Nat) (l : Wlabel)
    (i : Nat) :
    tsoShadow stamp (st ++ [(j, l)]) i =
      if j = i then shStepF stamp i (stAuthors st) (tsoShadow stamp st i) l
      else tsoShadow stamp st i := by
  unfold tsoShadow
  rw [tsoRunSnoc, ← tsoRunAuthors stamp i st]
  rfl

theorem tsoShadowOwn (stamp : CohStamp) (st : List (Nat × Wlabel)) (l : Wlabel) (i : Nat) :
    tsoShadow stamp (st ++ [(i, l)]) i = shStepF stamp i (stAuthors st) (tsoShadow stamp st i) l := by
  rw [tsoShadowSnoc, if_pos rfl]

theorem tsoShadowOther (stamp : CohStamp) (st : List (Nat × Wlabel)) (j : Nat) (l : Wlabel)
    (i : Nat) (h : j ≠ i) : tsoShadow stamp (st ++ [(j, l)]) i = tsoShadow stamp st i := by
  rw [tsoShadowSnoc, if_neg h]

/-- THE GENERIC ROW: hart `cpu`'s step relates the post-state if its own read side matches
`shStepF` and every other hart's read side is untouched. -/
theorem viewRelStep (stamp : CohStamp) (σ σ' : MState) (st : List (Nat × Wlabel)) (cpu : CPU)
    (l : Wlabel) (hrel : viewRel stamp σ st)
    (hown : hartRel σ' cpu
      (shStepF stamp (hartAgent cpu) (stAuthors st) (tsoShadow stamp st (hartAgent cpu)) l))
    (hoth : ∀ c, c ≠ cpu → σ'.tv c = σ.tv c ∧ σ'.hr c = σ.hr c ∧ σ'.itv c = σ.itv c) :
    viewRel stamp σ' (st ++ [(hartAgent cpu, l)]) := by
  intro c
  rw [tsoShadowSnoc]
  by_cases hc : c = cpu
  · subst hc
    rw [if_pos rfl]
    exact hown
  · rw [if_neg (fun h => hc (Fin.ext h.symm))]
    obtain ⟨h1, h2, h3⟩ := hoth c hc
    exact hartRelOther σ σ' c _ (hrel c) h1 h2 h3

/-- The labels that move no memory field and no `itv` of their author's shadow (`fiArm` may
move: `LInstr` arms it, `LIFetch` disarms it).  `LDev` by a WILDCARD arm. -/
def lbInert (l : Wlabel) : Bool :=
  match l with
  | .LSilent | .LRegW .. | .LCtrl .. | .LInstr | .LIFetch .. | .LDev .. => true
  | _ => false

theorem shStepFInert (stamp : CohStamp) (i : Nat) (au : List Nat) (f : ShFull) (l : Wlabel)
    (hl : lbInert l = true) :
    (shStepF stamp i au f l).mem = f.mem ∧ (shStepF stamp i au f l).itv = f.itv := by
  cases l <;> simp_all [lbInert, shStepF, shStep, lbFenceZero]

/-- **Inert rows** (`LSilent`, `LRegW`, `LCtrl`, `LInstr`, `LIFetch`, `LDev` at ANY payload), by
ANY agent: a TsoMem state with the same read side relates. -/
theorem viewRelInert (stamp : CohStamp) (σ σ' : MState) (st : List (Nat × Wlabel)) (j : Nat)
    (l : Wlabel) (hl : lbInert l = true) (hrel : viewRel stamp σ st) (hs : sameRead σ σ') :
    viewRel stamp σ' (st ++ [(j, l)]) := by
  intro c
  obtain ⟨htv, hhr, hitv⟩ := hs
  have h0 := hartRelOther σ σ' c _ (hrel c) (by rw [htv]) (by rw [hhr]) (by rw [hitv])
  rw [tsoShadowSnoc]
  split
  · subst j
    obtain ⟨hm, hi⟩ := shStepFInert stamp (hartAgent c) (stAuthors st)
      (tsoShadow stamp st (hartAgent c)) l hl
    exact hartRelCongr h0 hm hi
  · exact h0

/-- The disk row is no hart. -/
theorem diskNotHart (c : CPU) : diskAgent ≠ hartAgent c := by
  intro h
  have h1 := hartAgent_lt c
  rw [← h] at h1
  exact Nat.lt_irrefl _ h1

/-- **Non-hart rows** (the disk agent's `DRead` = `dmaRead`, `DWriteDev` = `storeDma` + `setDev`, its `DFence`
and `LDev` moves): no hart's shadow moves, no hart's read side moves. -/
theorem viewRelForeign (stamp : CohStamp) (σ σ' : MState) (st : List (Nat × Wlabel)) (j : Nat)
    (l : Wlabel) (hj : ∀ c : CPU, j ≠ hartAgent c) (hrel : viewRel stamp σ st)
    (hs : sameRead σ σ') : viewRel stamp σ' (st ++ [(j, l)]) := by
  intro c
  obtain ⟨htv, hhr, hitv⟩ := hs
  rw [tsoShadowOther stamp st j l _ (hj c)]
  exact hartRelOther σ σ' c _ (hrel c) (by rw [htv]) (by rw [hhr]) (by rw [hitv])

/-! ## (3) The shadow is bounded by the top -/

/-- Every memory field of a shadow is a legal position `≤ L`. -/
def memBound (L : Nat) (sh : ShSt) : Prop := sh.tv ≤ L ∧ sh.rv ≤ L ∧ ∀ a, sh.coh a ≤ L

/-- ... and `itv`. -/
def shBound (L : Nat) (f : ShFull) : Prop := memBound L f.mem ∧ f.itv ≤ L

theorem memBoundMono {L L' : Nat} {sh : ShSt} (h : memBound L sh) (hl : L ≤ L') : memBound L' sh :=
  ⟨Nat.le_trans h.1 hl, Nat.le_trans h.2.1 hl, fun a => Nat.le_trans (h.2.2 a) hl⟩

theorem shBoundMono {L L' : Nat} {f : ShFull} (h : shBound L f) (hl : L ≤ L') : shBound L' f :=
  ⟨memBoundMono h.1 hl, Nat.le_trans h.2 hl⟩

/-- A stamp pair that keeps floors legal: a load stamps at most its view on a foreign byte's
source (`t ≤ tvn`) or the view itself; a store's effect never raises a floor. -/
def StampOk (stamp : CohStamp) : Prop :=
  (∀ (i : Nat) (coh : Int → Nat) (base : Int) (srcs : List (Option (Nat × Nat))) (tvn L : Nat),
    (∀ a, coh a ≤ L) → tvn ≤ L →
    (∀ (j au t : Nat), srcs[j]? = some (some (au, t)) → au ≠ i → t ≤ tvn) →
    ∀ a, stamp.load i coh base srcs tvn a ≤ L) ∧
  (∀ (coh : Int → Nat) (base : Int) (n L : Nat), (∀ a, coh a ≤ L) →
    ∀ a, stamp.store coh base n a ≤ L)

theorem cohSrcOk : StampOk cohSrc := by
  refine ⟨fun i coh base srcs tvn L hc ht hf a => ?_, fun coh base n L hc a => ?_⟩
  · cases hfi : footIdx base srcs.length a with
    | none => rw [cohSrcLoadOut i coh base srcs tvn a hfi]; exact hc a
    | some j =>
      obtain ⟨hj, rfl⟩ := (footIdxSome _ _ _ _).1 hfi
      cases hs : srcs[j]? with
      | none => simp only [cohSrc, footIdxAcc base _ j hj, hs]; exact hc _
      | some x =>
        cases x with
        | none => simp only [cohSrc, footIdxAcc base _ j hj, hs]; exact hc _
        | some p =>
          obtain ⟨au, t⟩ := p
          by_cases he : au = i
          · subst he
            rw [cohSrcLoadOwn au coh base srcs tvn j t hs]
            exact hc _
          · rw [cohSrcLoadForeign i coh base srcs tvn j au t hs he]
            exact Nat.max_le.2 ⟨hc _, Nat.le_trans (hf j au t hs he) ht⟩
  · cases hfi : footIdx base n a with
    | none => rw [cohSrcStoreOut coh base n a hfi]; exact hc a
    | some j =>
      obtain ⟨hj, rfl⟩ := (footIdxSome _ _ _ _).1 hfi
      rw [cohSrcStoreIn coh base n j hj]
      exact Nat.zero_le _

theorem cohFootOk : StampOk cohFoot := by
  refine ⟨fun i coh base srcs tvn L hc ht _ a => ?_, fun coh base n L hc a => hc a⟩
  simp only [cohFoot]
  split
  · exact ht
  · exact hc a

theorem cohOffOk : StampOk cohOff := ⟨fun _ _ _ _ _ _ hc _ _ a => hc a, fun _ _ _ _ hc a => hc a⟩

/-- The per-byte sources the shadow's load step uses (`TsoShadow.shStep`'s `LLoad` arm): byte
`j`'s (author, timestamp) from the pf log's authors `au`, `some (0, 0)` for the image. -/
def shLoadSrcs (au : List Nat) (tvs : List (Nat × BitVec 8)) : LoadSrcs :=
  (tvs.map Prod.fst).map (shSrc au)

theorem shLoadSrcsLength (au : List Nat) (tvs : List (Nat × BitVec 8)) :
    (shLoadSrcs au tvs).length = tvs.length := by
  simp [shLoadSrcs]

theorem shLoadSrcsGet (au : List Nat) (tvs : List (Nat × BitVec 8)) (j a t : Nat)
    (h : (shLoadSrcs au tvs)[j]? = some (some (a, t))) :
    ∃ t0, (tvs.map Prod.fst)[j]? = some t0 ∧ shSrc au t0 = some (a, t) := by
  unfold shLoadSrcs at h
  rw [List.getElem?_map] at h
  cases h0 : (tvs.map Prod.fst)[j]? with
  | none => rw [h0] at h; cases h
  | some t0 =>
    rw [h0] at h
    simp only [Option.map_some, Option.some.injEq] at h
    exact ⟨t0, rfl, h⟩

theorem shSrcSome (au : List Nat) (t0 a t : Nat) (h : shSrc au t0 = some (a, t)) :
    (t0 = 0 ∧ a = 0 ∧ t = 0) ∨ (0 < t0 ∧ t = t0 ∧ au[t0 - 1]? = some a) := by
  unfold shSrc at h
  by_cases h0 : t0 = 0
  · rw [if_pos h0] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    exact Or.inl ⟨h0, h.1.symm, h.2.symm⟩
  · rw [if_neg h0] at h
    cases hg : au[t0 - 1]? with
    | none => rw [hg] at h; cases h
    | some b =>
      rw [hg] at h
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact Or.inr ⟨by omega, rfl, rfl⟩

theorem shSrcLe (au : List Nat) (t0 a t : Nat) (h : shSrc au t0 = some (a, t)) : t ≤ au.length := by
  rcases shSrcSome au t0 a t h with ⟨-, -, rfl⟩ | ⟨_, rfl, hg⟩
  · exact Nat.zero_le _
  · have := (List.getElem?_eq_some_iff.1 hg).1
    omega

theorem shForeignGe (i : Nat) : ∀ (srcs : List (Option (Nat × Nat))) (j a t : Nat),
    srcs[j]? = some (some (a, t)) → a ≠ i → t ≤ shForeign i srcs
  | [], _, _, _, h, _ => by simp at h
  | x :: r, 0, a, t, h, hne => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h
    simp only [shForeign, if_neg hne]
    exact Nat.le_max_left _ _
  | x :: r, j + 1, a, t, h, hne => by
    simp only [List.getElem?_cons_succ] at h
    have ih := shForeignGe i r j a t h hne
    cases x with
    | none => simpa only [shForeign] using ih
    | some p =>
      obtain ⟨b, u⟩ := p
      simp only [shForeign]
      split
      · exact ih
      · exact Nat.le_trans ih (Nat.le_max_right _ _)

theorem shForeignLe (i B : Nat) : ∀ (srcs : List (Option (Nat × Nat))),
    (∀ (j a t : Nat), srcs[j]? = some (some (a, t)) → a ≠ i → t ≤ B) → shForeign i srcs ≤ B
  | [], _ => Nat.zero_le _
  | x :: r, h => by
    have ih := shForeignLe i B r (fun j a t hj hne => h (j + 1) a t (by simpa using hj) hne)
    cases x with
    | none => simpa only [shForeign] using ih
    | some p =>
      obtain ⟨b, u⟩ := p
      simp only [shForeign]
      split
      · exact ih
      · rename_i hne
        exact Nat.max_le.2 ⟨h 0 b u (by simp) hne, ih⟩

theorem cohMaxLe (coh : Int → Nat) (base : Int) (L : Nat) (h : ∀ a, coh a ≤ L) :
    ∀ n, cohMax coh base n ≤ L
  | 0 => Nat.zero_le _
  | n + 1 => by
    simp only [cohMax]
    exact Nat.max_le.2 ⟨cohMaxLe coh base L h n, h _⟩

/-- The minimal view is a legal position. -/
theorem shTvnLe (i : Nat) (au : List Nat) (sh : ShSt) (base : Int) (tvs : List (Nat × BitVec 8))
    (h : memBound au.length sh) : shTvn i sh base (shLoadSrcs au tvs) ≤ au.length := by
  obtain ⟨htv, -, hcoh⟩ := h
  unfold shTvn shFloor
  refine Nat.max_le.2 ⟨Nat.max_le.2 ⟨htv, cohMaxLe _ _ _ hcoh _⟩,
    shForeignLe i _ _ (fun j a t hj _ => ?_)⟩
  obtain ⟨t0, -, hs⟩ := shLoadSrcsGet au tvs j a t hj
  exact shSrcLe au t0 a t hs

/-- One own step keeps the memory fields legal (the top grows by a writing step). -/
theorem shStepBound (stamp : CohStamp) (hs : StampOk stamp) (i : Nat) (au : List Nat) (sh : ShSt)
    (l : Wlabel) (h : memBound au.length sh) :
    memBound (au.length + (if lbWrites l then 1 else 0)) (shStep stamp i au sh l) := by
  obtain ⟨htv, hrv, hcoh⟩ := h
  have hstore : ∀ (base : Int) (n : Nat) (a : Int), stamp.store sh.coh base n a ≤ au.length + 1 :=
    fun base n a => Nat.le_trans (hs.2 sh.coh base n au.length hcoh a) (Nat.le_succ _)
  cases l
  case LLoad aq lat base tvs asrc =>
    show memBound au.length (sh.load stamp i base (shLoadSrcs au tvs))
    have hT := shTvnLe i au sh base tvs ⟨htv, hrv, hcoh⟩
    refine ⟨htv, Nat.max_le.2 ⟨hrv, hT⟩, hs.1 i sh.coh base _ _ au.length hcoh hT
      (fun j a t hj hne => Nat.le_trans (shForeignGe i _ j a t hj hne) (Nat.le_max_right _ _))⟩
  case LStore rl base data asrc vsrc =>
    show memBound (au.length + 1) (sh.store stamp au.length false base data.length)
    exact ⟨Nat.le_trans htv (Nat.le_succ _), Nat.le_trans hrv (Nat.le_succ _), hstore base _⟩
  case LRmw aq rl base tvs data asrc vsrc =>
    show memBound (au.length + 1) ((sh.excl au.length aq).store stamp au.length true base data.length)
    refine ⟨?_, Nat.le_succ _, hstore base _⟩
    show (if true && aq then au.length + 1 else (if aq then au.length else sh.tv)) ≤ au.length + 1
    cases aq
    · exact Nat.le_trans htv (Nat.le_succ _)
    · exact Nat.le_refl _
  case LFence pr pw sr sw =>
    show memBound au.length (sh.fence (MachCSL.ownPub i au) pr pw sr sw)
    exact ⟨MachCSL.fencePost_le _ _ _ _ _ _ htv hrv (MachCSL.ownPub_le i au), hrv, hcoh⟩
  case LExLoad aq base tvs asrc =>
    show memBound au.length (sh.excl au.length aq)
    refine ⟨?_, Nat.le_refl _, hcoh⟩
    show (if aq then au.length else sh.tv) ≤ au.length
    cases aq
    · exact htv
    · exact Nat.le_refl _
  case LExStore rl base data asrc vsrc =>
    show memBound (au.length + 1) (sh.store stamp au.length true base data.length)
    refine ⟨?_, Nat.le_trans hrv (Nat.le_succ _), hstore base _⟩
    show (if true && sh.acq then au.length + 1 else sh.tv) ≤ au.length + 1
    cases sh.acq
    · exact Nat.le_trans htv (Nat.le_succ _)
    · exact Nat.le_refl _
  all_goals exact memBoundMono ⟨htv, hrv, hcoh⟩ (Nat.le_add_right _ _)

theorem shStepFBound (stamp : CohStamp) (hs : StampOk stamp) (i : Nat) (au : List Nat) (f : ShFull)
    (l : Wlabel) (h : shBound au.length f) :
    shBound (au.length + (if lbWrites l then 1 else 0)) (shStepF stamp i au f l) := by
  obtain ⟨⟨htv, hrv, hcoh⟩, hitv⟩ := h
  refine ⟨shStepBound stamp hs i au f.mem l ⟨htv, hrv, hcoh⟩, Nat.le_trans ?_ (Nat.le_add_right _ _)⟩
  show (if lbFenceZero l && f.fiArm then
      max f.itv (MachCSL.fencePost true false f.mem.tv f.mem.rv (MachCSL.ownPub i au))
    else f.itv) ≤ au.length
  split
  · exact Nat.max_le.2 ⟨hitv, MachCSL.fencePost_le _ _ _ _ _ _ htv hrv (MachCSL.ownPub_le i au)⟩
  · exact hitv

/-- **THE SHADOW IS BOUNDED BY THE TOP**: every field of every agent's shadow is `≤ |stAuthors
st|` (= TsoMem's top under `R-log`), for every stamp pair that keeps floors legal. -/
theorem tsoShadowBound (stamp : CohStamp) (hs : StampOk stamp) (i : Nat) (st : List (Nat × Wlabel)) :
    shBound (stAuthors st).length (tsoShadow stamp st i) := by
  induction hk : st.length generalizing st with
  | zero =>
    obtain rfl := List.eq_nil_of_length_eq_zero hk
    refine ⟨⟨?_, ?_, fun _ => ?_⟩, ?_⟩ <;> exact Nat.le_refl 0
  | succ k ihk =>
    obtain ⟨st, y, rfl⟩ := (List.eq_nil_or_concat st).resolve_left (by rintro rfl; simp at hk)
    rw [List.concat_eq_append] at hk ⊢
    have ih := ihk st (by simp at hk; omega)
    obtain ⟨j, l⟩ := y
    have hlen : (stAuthors (st ++ [(j, l)])).length =
        (stAuthors st).length + (if lbWrites l then 1 else 0) := by
      rw [stAuthorsSnoc]; cases lbWrites l <;> simp
    rw [tsoShadowSnoc, hlen]
    by_cases hji : j = i
    · rw [if_pos hji]
      subst hji
      exact shStepFBound stamp hs _ _ _ l ih
    · rw [if_neg hji]
      exact shBoundMono ih (Nat.le_add_right _ _)

/-! ## (4) THE ROWS -/

/-- TsoMem's plain-read side conditions at view `tvn` (`evStep`'s plain arm, `Lang.lean`). -/
def tsoLoadOk (σ : MState) (cpu : CPU) (pa : PAddr) (n tvn : Nat) : Prop :=
  σ.tv cpu ≤ tvn ∧ tvn ≤ σ.top ∧ (σ.hr cpu).cohOk pa n tvn

/-- THE VIEW a hart load reads at: the shadow's MINIMAL legal view
`max(F, max_{foreign j} t_j)` (`TsoShadow.shTvn`) at the prefix `st`. -/
def minView (stamp : CohStamp) (st : List (Nat × Wlabel)) (i : Nat) (base : Int)
    (tvs : List (Nat × BitVec 8)) : Nat :=
  shTvn i (tsoShadow stamp st i).mem base (shLoadSrcs (stAuthors st) tvs)

/-- The minimal view is at most every `scaOkT` witness (so the load's bytes, `scaByte` at that
witness, are what TsoMem reads at the minimal view once no foreign write lies in between — W2a's
`(★)`). -/
theorem minViewLeSca (sh : ShSt) (img : Image) (log : List Wmsg) (au : List Nat) (i : Nat)
    (base : Int) (tvs : List (Nat × BitVec 8)) (hau : log.map Wmsg.wmTid = au.map some)
    (h : scaOkT sh img log i base (tvs.map Prod.fst)) :
    ∃ tvn, tvn ≤ log.length ∧ shTvn i sh base (shLoadSrcs au tvs) ≤ tvn ∧
      ∀ (j t : Nat), (tvs.map Prod.fst)[j]? = some t → scaByte img log i tvn (accAddr base j) t := by
  obtain ⟨tvn, hle, hF, hb⟩ := h
  refine ⟨tvn, hle, Nat.max_le.2 ⟨?_, shForeignLe i _ _ (fun j a t hj hne => ?_)⟩, hb⟩
  · rw [shLoadSrcsLength]
    simpa using hF
  · obtain ⟨t0, ht0, hs⟩ := shLoadSrcsGet au tvs j a t hj
    rcases shSrcSome au t0 a t hs with ⟨-, -, rfl⟩ | ⟨hpos, rfl, hg⟩
    · exact Nat.zero_le _
    · obtain ⟨-, hvis, -⟩ := hb j t ht0
      rcases hvis with hv | ⟨_, m, hm, hmt⟩
      · exact hv
      · exfalso
        have h1 := congrArg (fun l => l[t - 1]?) hau
        simp only [List.getElem?_map, hm, hg, Option.map_some, Option.some.injEq] at h1
        rw [hmt] at h1
        exact hne (Option.some.inj h1).symm

/-- The TsoMem load stamp at a byte equals the shadow's `cohSrc` stamp at its `paZ` image. -/
theorem loadCohEq (hr : HRead) (coh : Int → Nat) (hc : ∀ pa, hr.coh pa = coh (paZ pa)) (me : Nat)
    (pa : PAddr) (n : Nat) (srcs : LoadSrcs) (tvn : Nat) (hn : srcs.length = n)
    (hfit : pa.toNat + n < 18446744073709551616) (pa' : PAddr) :
    max (hr.coh pa') (srcs.stamp me pa n pa') = cohSrc.load me coh (paZ pa) srcs tvn (paZ pa') := by
  rw [hc pa']
  subst hn
  cases hfi : footIdx (paZ pa) srcs.length (paZ pa') with
  | none =>
    rw [cohSrcLoadOut me coh (paZ pa) srcs tvn _ hfi]
    have h0 : srcs.stamp me pa srcs.length pa' = 0 := by
      apply Nat.le_zero.1
      unfold LoadSrcs.stamp
      refine TsoMem.foldrMax_le _ _ (fun x hx => ?_)
      obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hx
      rw [if_neg (footIdxPaNone pa pa' _ hfit hfi j (List.mem_range.1 hj))]
      exact Nat.le_refl _
    rw [h0, Nat.max_zero]
  | some j =>
    obtain ⟨hj, rfl⟩ := footIdxPaSome pa pa' _ j hfit hfi
    rw [LoadSrcs.stamp_at srcs me pa srcs.length j (by rw [pow64]; omega) hj]
    simp only [cohSrc, hfi]
    unfold LoadSrcs.stampAt
    cases hs : srcs[j]? with
    | none => simp
    | some x =>
      cases x with
      | none => simp
      | some p =>
        obtain ⟨tid, t⟩ := p
        by_cases ht : tid = me <;> simp [ht]

/-- The compiled load's read side for its author, against the shadow's load step (`cohSrc`:
FOREIGN-sourced bytes stamped with their source, [OWN.23]) at the minimal view. -/
theorem loadOwn (σ : MState) (cpu : CPU) (pa : PAddr) (n : Nat) (srcs : LoadSrcs) (f f' : ShFull)
    (hr : hartRel σ cpu f) (hn : srcs.length = n) (hfit : pa.toNat + n < 18446744073709551616)
    (hsrc : σ.mem.loadSrcs (hartAgent cpu) (shTvn (hartAgent cpu) f.mem (paZ pa) srcs) pa n = srcs)
    (hm : f'.mem = f.mem.load cohSrc (hartAgent cpu) (paZ pa) srcs) (hi : f'.itv = f.itv) :
    hartRel (σ.afterLoad cpu pa n (shTvn (hartAgent cpu) f.mem (paZ pa) srcs)) cpu f' := by
  have hH : (σ.afterLoad cpu pa n (shTvn (hartAgent cpu) f.mem (paZ pa) srcs)).hr cpu =
      (σ.hr cpu).afterLoad (hartAgent cpu) pa n (shTvn (hartAgent cpu) f.mem (paZ pa) srcs)
        (σ.mem.loadSrcs (hartAgent cpu) (shTvn (hartAgent cpu) f.mem (paZ pa) srcs) pa n) :=
    if_pos rfl
  rw [hsrc] at hH
  refine ⟨?_, ?_, fun pa' => ?_, ?_, ?_⟩
  · rw [hm]; exact hr.tvEq
  · rw [hH, hm]
    show max (σ.hr cpu).rv _ = max f.mem.rv _
    rw [hr.rvEq]
  · rw [hH, hm]
    exact loadCohEq (σ.hr cpu) f.mem.coh hr.cohEq (hartAgent cpu) pa n srcs
      (shTvn (hartAgent cpu) f.mem (paZ pa) srcs) hn hfit pa'
  · rw [hH, hm]; exact hr.acqEq
  · rw [hi]; exact hr.itvEq

/-- **ROW: hart `LLoad`** (plain RAM read; instance `cohSrc` = the compiled TsoMem after W-COH).
At the shadow's minimal view `tvn`, TsoMem's side conditions hold and the compiled
`MState.afterLoad` lands in `R-view`.  `hsrc` is the per-byte source seam with W2a. -/
theorem rowLoad (σ : MState) (st : List (Nat × Wlabel)) (cpu : CPU) (pa : PAddr) (aq lat : Bool)
    (tvs : List (Nat × BitVec 8)) (asrc : List Dsrc) (hrel : viewRel cohSrc σ st)
    (hlog : σ.log = stAuthors st) (hfit : pa.toNat + tvs.length < 18446744073709551616)
    (hsrc : σ.mem.loadSrcs (hartAgent cpu) (minView cohSrc st (hartAgent cpu) (paZ pa) tvs) pa
      tvs.length = shLoadSrcs (stAuthors st) tvs) :
    tsoLoadOk σ cpu pa tvs.length (minView cohSrc st (hartAgent cpu) (paZ pa) tvs) ∧
    viewRel cohSrc (σ.afterLoad cpu pa tvs.length (minView cohSrc st (hartAgent cpu) (paZ pa) tvs))
      (st ++ [(hartAgent cpu, .LLoad aq lat (paZ pa) tvs asrc)]) := by
  have hr := hrel cpu
  have hb := (tsoShadowBound cohSrc cohSrcOk (hartAgent cpu) st).1
  generalize hf : tsoShadow cohSrc st (hartAgent cpu) = f at hr hb
  have hmv : minView cohSrc st (hartAgent cpu) (paZ pa) tvs =
      shTvn (hartAgent cpu) f.mem (paZ pa) (shLoadSrcs (stAuthors st) tvs) := by
    rw [← hf]; rfl
  rw [hmv] at hsrc ⊢
  have hlen := shLoadSrcsLength (stAuthors st) tvs
  have hfl := shFloorGe f.mem (paZ pa) (shLoadSrcs (stAuthors st) tvs).length
  have hFT : shFloor f.mem (paZ pa) (shLoadSrcs (stAuthors st) tvs).length ≤
      shTvn (hartAgent cpu) f.mem (paZ pa) (shLoadSrcs (stAuthors st) tvs) := Nat.le_max_left _ _
  refine ⟨⟨?_, ?_, fun j hj => ?_⟩, viewRelStep cohSrc σ _ st cpu _ hrel ?_ ?_⟩
  · rw [hr.tvEq]; exact Nat.le_trans hfl.1 hFT
  · show _ ≤ σ.log.length
    rw [hlog]
    exact shTvnLe _ _ _ _ _ hb
  · show (σ.hr cpu).coh (pa + BitVec.ofNat 64 j) ≤ _
    rw [hr.cohEq, paZAddFit pa _ j hfit hj]
    exact Nat.le_trans (hfl.2 j (by rw [hlen]; exact hj)) hFT
  · rw [hf]
    exact loadOwn σ cpu pa tvs.length _ f _ hr hlen hfit hsrc rfl rfl
  · intro c hc
    exact ⟨rfl, if_neg hc, rfl⟩

/-- The compiled store's read side for its author, against the shadow's store step (`cohSrc`:
the footprint RESET, [R11.1][OWN.21]; `excl` a parameter, no case split [R14.s3]). -/
theorem storeOwn (σ : MState) (au : List Nat) (cpu : CPU) (pa : PAddr) (n : Nat)
    (w : BitVec (8 * n)) (excl : Bool) (f f' : ShFull) (hr : hartRel σ cpu f) (hlog : σ.log = au)
    (hfit : pa.toNat + n < 18446744073709551616)
    (hm : f'.mem = f.mem.store cohSrc au.length excl (paZ pa) n) (hi : f'.itv = f.itv) :
    hartRel (σ.store cpu pa n w excl) cpu f' := by
  have hT : (σ.store cpu pa n w excl).tv cpu =
      (if excl && (σ.hr cpu).acq then σ.log.length + 1 else σ.tv cpu) := if_pos rfl
  have hH : (σ.store cpu pa n w excl).hr cpu = ((σ.hr cpu).clearAcq).resetCoh pa n := if_pos rfl
  refine ⟨?_, ?_, fun pa' => ?_, ?_, ?_⟩
  · rw [hT, hm]
    show _ = (if excl && f.mem.acq then au.length + 1 else f.mem.tv)
    rw [hr.acqEq, hr.tvEq, hlog]
  · rw [hH, hm]; exact hr.rvEq
  · rw [hH, hm]
    show (if (List.range n).any (fun j => pa' == pa + BitVec.ofNat 64 j) then 0
        else (σ.hr cpu).coh pa') = cohSrc.store f.mem.coh (paZ pa) n (paZ pa')
    cases hfi : footIdx (paZ pa) n (paZ pa') with
    | none =>
      rw [cohSrcStoreOut _ _ _ _ hfi, hr.cohEq pa']
      have hany : (List.range n).any (fun j => pa' == pa + BitVec.ofNat 64 j) = false := by
        rw [List.any_eq_false]
        intro j hj
        simp only [beq_iff_eq]
        exact footIdxPaNone pa pa' n hfit hfi j (List.mem_range.1 hj)
      rw [hany]
      rfl
    | some j =>
      obtain ⟨hj, rfl⟩ := footIdxPaSome pa pa' n j hfit hfi
      rw [paZAddFit pa n j hfit hj, cohSrcStoreIn _ _ _ _ hj]
      have hany : (List.range n).any
          (fun j' => pa + BitVec.ofNat 64 j == pa + BitVec.ofNat 64 j') = true :=
        List.any_eq_true.2 ⟨j, List.mem_range.2 hj, beq_self_eq_true _⟩
      rw [hany]
      rfl
  · rw [hH, hm]; rfl
  · rw [hi]; exact hr.itvEq

/-- **ROW: hart `LStore`** (`MState.store … false`; `cohSrc`): the footprint's floors RESET, the
acquire bit cleared, `tv` kept. -/
theorem rowStore (σ : MState) (st : List (Nat × Wlabel)) (cpu : CPU) (pa : PAddr) (n : Nat)
    (w : BitVec (8 * n)) (rl : Bool) (data : List (BitVec 8)) (asrc vsrc : List Dsrc)
    (hn : data.length = n) (hrel : viewRel cohSrc σ st) (hlog : σ.log = stAuthors st)
    (hfit : pa.toNat + n < 18446744073709551616) :
    viewRel cohSrc (σ.store cpu pa n w false)
      (st ++ [(hartAgent cpu, .LStore rl (paZ pa) data asrc vsrc)]) := by
  subst hn
  refine viewRelStep cohSrc σ _ st cpu _ hrel ?_ (fun c hc => ⟨if_neg hc, if_neg hc, rfl⟩)
  exact storeOwn σ (stAuthors st) cpu pa data.length w false _ _ (hrel cpu) hlog hfit rfl rfl

/-- **ROW: `LExStore`** (the SAME `MState.store`, `excl = true`; `cohSrc`): the reset, and the
floor to `top + 1` iff the pair's read was an acquire. -/
theorem rowExStore (σ : MState) (st : List (Nat × Wlabel)) (cpu : CPU) (pa : PAddr) (n : Nat)
    (w : BitVec (8 * n)) (rl : Bool) (data : List (BitVec 8)) (asrc vsrc : List Dsrc)
    (hn : data.length = n) (hrel : viewRel cohSrc σ st) (hlog : σ.log = stAuthors st)
    (hfit : pa.toNat + n < 18446744073709551616) :
    viewRel cohSrc (σ.store cpu pa n w true)
      (st ++ [(hartAgent cpu, .LExStore rl (paZ pa) data asrc vsrc)]) := by
  subst hn
  refine viewRelStep cohSrc σ _ st cpu _ hrel ?_ (fun c hc => ⟨if_neg hc, if_neg hc, rfl⟩)
  exact storeOwn σ (stAuthors st) cpu pa data.length w true _ _ (hrel cpu) hlog hfit rfl rfl

/-- **ROW: `LExLoad aq`** (`MState.afterExcl`; ANY stamp — `coh` kept, instance-independent
[R14.2]): `rv := top`, the floor to the top iff an acquire, the acquire bit recorded. -/
theorem rowExLoad (stamp : CohStamp) (σ : MState) (st : List (Nat × Wlabel)) (cpu : CPU)
    (pa : PAddr) (n : Nat) (w : BitVec (8 * n)) (aq : Bool) (base : Int)
    (tvs : List (Nat × BitVec 8)) (asrc : List Dsrc) (hrel : viewRel stamp σ st)
    (hlog : σ.log = stAuthors st) :
    viewRel stamp (σ.afterExcl cpu pa n w aq) (st ++ [(hartAgent cpu, .LExLoad aq base tvs asrc)]) := by
  refine viewRelStep stamp σ _ st cpu _ hrel ?_ (fun c hc => ⟨if_neg hc, if_neg hc, rfl⟩)
  have hr := hrel cpu
  have hT : (σ.afterExcl cpu pa n w aq).tv cpu = (if aq then σ.log.length else σ.tv cpu) :=
    if_pos rfl
  have hH : (σ.afterExcl cpu pa n w aq).hr cpu = (σ.hr cpu).afterExcl σ.log.length aq := if_pos rfl
  refine ⟨?_, ?_, fun pa' => ?_, ?_, hr.itvEq⟩
  · rw [hT]
    show _ = (if aq then (stAuthors st).length else (tsoShadow stamp st (hartAgent cpu)).mem.tv)
    rw [hr.tvEq, hlog]
  · rw [hH]
    show σ.log.length = (stAuthors st).length
    rw [hlog]
  · rw [hH]; exact hr.cohEq pa'
  · rw [hH]; rfl

/-- **ROW: `LFence` / `fence.i`** (`MState.fence cpu b`; ANY stamp): the label is `ebarLabel b`
(the `ebarNow` bits; `LFence false×4` at `fence.i`), and at `fence.i` the shadow's `fiArm` is set
(`emFenceI`'s criterion).  `tv` per `fencePost` (the 10 kinds), `itv` raised at `fence.i` only. -/
theorem rowFence (stamp : CohStamp) (σ : MState) (st : List (Nat × Wlabel)) (cpu : CPU)
    (b : barrier_kind) (hrel : viewRel stamp σ st) (hlog : σ.log = stAuthors st)
    (hfi : b = .Barrier_RISCV_i → (tsoShadow stamp st (hartAgent cpu)).fiArm = true) :
    viewRel stamp (σ.fence cpu b) (st ++ [(hartAgent cpu, ebarLabel b)]) := by
  refine viewRelStep stamp σ _ st cpu _ hrel ?_ (fun c hc => ⟨if_neg hc, rfl, if_neg hc⟩)
  have hr := hrel cpu
  have hT : (σ.fence cpu b).tv cpu = MachCSL.fencePost (fenceDrains b) (fenceAcq b) (σ.tv cpu)
      (σ.hr cpu).rv (MachCSL.ownPub (hartAgent cpu) σ.log) := if_pos rfl
  have hI : (σ.fence cpu b).itv cpu =
      (if fenceIfetch b then max (σ.itv cpu) (MachCSL.fencePost true false (σ.tv cpu) (σ.hr cpu).rv
        (MachCSL.ownPub (hartAgent cpu) σ.log)) else σ.itv cpu) := if_pos rfl
  generalize hf : tsoShadow stamp st (hartAgent cpu) = f at hr hfi ⊢
  refine ⟨?_, ?_, fun pa' => ?_, ?_, ?_⟩
  · rw [hT, hr.tvEq, hr.rvEq, hlog]
    cases b <;> rfl
  · cases b <;> exact hr.rvEq
  · cases b <;> exact hr.cohEq pa'
  · cases b <;> exact hr.acqEq
  · rw [hI, hr.tvEq, hr.rvEq, hlog, hr.itvEq]
    cases b
    case Barrier_RISCV_i =>
      have h1 := hfi rfl
      show _ = (if true && f.fiArm then _ else _)
      rw [h1]
      rfl
    all_goals rfl

/-- **ROW: the `sfence.vma` marker** (`LFence false×4` at an SFENCE.VMA announce, `fiArm`
cleared by the fetch; TsoMem's `instrAnnounce` arm, `σ' = σ`; ANY stamp). -/
theorem rowSfenceMarker (stamp : CohStamp) (σ : MState) (st : List (Nat × Wlabel)) (cpu : CPU)
    (hrel : viewRel stamp σ st) (hfi : (tsoShadow stamp st (hartAgent cpu)).fiArm = false) :
    viewRel stamp σ (st ++ [(hartAgent cpu, .LFence false false false false)]) := by
  refine viewRelStep stamp σ _ st cpu _ hrel ?_ (fun _ _ => ⟨rfl, rfl, rfl⟩)
  refine hartRelCongr (hrel cpu) (ShSt.fenceNoSucc (tsoShadow stamp st (hartAgent cpu)).mem
    (MachCSL.ownPub (hartAgent cpu) (stAuthors st)) false false false) ?_
  show (if true && (tsoShadow stamp st (hartAgent cpu)).fiArm then _ else _) = _
  rw [hfi]
  rfl

/-- **ROW: `LIFetch`, M1** (ANY stamp): the fetch reads at `tvn := itv` — TsoMem's
`itv ≤ tvn ≤ top` hold — and `σ' = σ` relates (`fiArm` cleared). -/
theorem rowFetchM1 (stamp : CohStamp) (hs : StampOk stamp) (σ : MState)
    (st : List (Nat × Wlabel)) (cpu : CPU) (base : Int) (tvs : List (Nat × BitVec 8))
    (hrel : viewRel stamp σ st) (hlog : σ.log = stAuthors st) :
    σ.itv cpu = (tsoShadow stamp st (hartAgent cpu)).itv ∧ σ.itv cpu ≤ σ.itv cpu ∧
    σ.itv cpu ≤ σ.top ∧ viewRel stamp σ (st ++ [(hartAgent cpu, .LIFetch base tvs)]) := by
  refine ⟨(hrel cpu).itvEq, Nat.le_refl _, ?_,
    viewRelInert stamp σ σ st _ _ rfl hrel (sameReadRefl σ)⟩
  show _ ≤ σ.log.length
  rw [(hrel cpu).itvEq, hlog]
  exact (tsoShadowBound stamp hs (hartAgent cpu) st).2

/-- **ROW: `LIFetch`, M2's `itv` side** (ANY stamp): a cut view `q` at or above the shadow's
`itv` (W5d's `itvOf`) and at most the top is a legal TsoMem fetch view. -/
theorem rowFetchM2 (stamp : CohStamp) (σ : MState) (st : List (Nat × Wlabel)) (cpu : CPU)
    (base : Int) (tvs : List (Nat × BitVec 8)) (q : Nat) (hrel : viewRel stamp σ st)
    (hlog : σ.log = stAuthors st) (hq : (tsoShadow stamp st (hartAgent cpu)).itv ≤ q)
    (hqt : q ≤ (stAuthors st).length) :
    σ.itv cpu ≤ q ∧ q ≤ σ.top ∧ viewRel stamp σ (st ++ [(hartAgent cpu, .LIFetch base tvs)]) := by
  refine ⟨by rw [(hrel cpu).itvEq]; exact hq, ?_,
    viewRelInert stamp σ σ st _ _ rfl hrel (sameReadRefl σ)⟩
  show q ≤ σ.log.length
  rw [hlog]
  exact hqt

/-- **ROW: disk `DRead`** (agent `NCPU`, `LLoad aq false`; TsoMem's `dmaRead`, `σ' = σ`; ANY
stamp; its bytes against `dmaView` under `candDiskLat` are W2a's). -/
theorem rowDiskRead (stamp : CohStamp) (σ : MState) (st : List (Nat × Wlabel)) (aq : Bool)
    (base : Int) (tvs : List (Nat × BitVec 8)) (hrel : viewRel stamp σ st) :
    viewRel stamp σ (st ++ [(diskAgent, .LLoad aq false base tvs [])]) :=
  viewRelForeign stamp σ σ st _ _ diskNotHart hrel (sameReadRefl σ)

/-- **ROW: disk `DWriteDev` store** (agent `NCPU`, `LStore false`; TsoMem's `storeDma` with the
device's own move `setDev` -- W-DISK's fabric delta rides the same step; ANY stamp). -/
theorem rowDiskWrite (stamp : CohStamp) (σ : MState) (st : List (Nat × Wlabel)) (pa : PAddr)
    (n : Nat) (w : BitVec (8 * n)) (d : DevId) (s : DevSt d) (base : Int)
    (data : List (BitVec 8)) (hrel : viewRel stamp σ st) :
    viewRel stamp ((σ.storeDma pa n w).setDev d s)
      (st ++ [(diskAgent, .LStore false base data [] [])]) :=
  viewRelForeign stamp σ _ st _ _ diskNotHart hrel
    (sameReadTrans (sameReadStoreDma σ pa n w) (sameReadSetDev _ d s))

/-- **ROW: disk `DWriteDev` skip / abort, `DPop`** (W-DISK; agent `NCPU`, label `LSilent` /
`LDev`; the device's own move `setDev` only; ANY stamp). -/
theorem rowDiskDevMove (stamp : CohStamp) (σ : MState) (st : List (Nat × Wlabel)) (l : Wlabel)
    (d : DevId) (s : DevSt d) (hrel : viewRel stamp σ st) :
    viewRel stamp (σ.setDev d s) (st ++ [(diskAgent, l)]) :=
  viewRelForeign stamp σ _ st _ _ diskNotHart hrel (sameReadSetDev σ d s)

end PfStepTsoView

end Weak
