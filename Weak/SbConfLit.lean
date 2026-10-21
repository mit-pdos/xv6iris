/-
Weak: **allocproc route P, row P-W6 step 1 ([OWN.149]) — the twin↔machine CONFORMANCE MATRIX's
litmus tests** (`notes/twin-machine-conformance.md`; design `weakmach/proposal-A7.md` §5.1).
Lean-only, no Rocq twin.  A PRIMED TWIN: nothing registered imports this file.

The matrix pairs each rule of the buffered twin `SbCand` (rows) with each memory-relevant arm of
MachCSL's `evStep` / `blockedStep` / `primStep` land arm / `devOpStep` (columns).  For EVERY cell where
the MACHINE IS STRONGER (a twin step the realization cannot answer by a machine step under the state
map `SbRealP.rmemP`), this file gives a small litmus in the `SbRealP.wit1Run` pattern:

* the TWIN SIDE is a concrete `SbCand` run, checked by `decide +kernel` — under EVERY lawful policy
  (`SbCand.runOfB`, oldest-entry landings) or, when the run lands a hart's entries OUT OF ORDER, under
  the primary policy `SbPol.epoch` (the indexed checker `SbConfLit.runOfIB` of §1);
* the MACHINE SIDE is the MachCSL guard (or atomic transition) that forbids it, stated over every
  state.

| § | cell (matrix id) | twin run | machine side | status |
|---|---|---|---|---|
| 2 | land × land arm (F-PW6-1), the FULL S-shape chain of `PROGRESS-PW6.md` §2 | `sRun`/`sLog` (epoch) | `SbRealP.landBlockedForeign` | known |
| 3 | fence × draining-fence blocked arm, `fence.i` (the kept drain [OWN.146]) | `fiRun` (epoch) | `fenceIBlocked` | known (fetch marker O-P-W1-a) |
| 4 | device row × `storeDma` (F-PW6-2): same-epoch device stores land out of order | `dmaRun` (epoch) | `dmaLandsAtOnce` | known, ruled [OWN.148] |
| 5 | io × MMIO-write `drvOkGuard` (**F-CM-2, NEW**): the `DRIVER_OK` store with pending queue-page stores | `drvRun` (every policy) | `drvOkBlocked` | **new** |
| 6 | device row × `dmaWrite` (**F-CM-1, NEW**): the fabric move of a BUFFERED device store is seen by a fabric-later hart MMIO access before the store lands | `fabRun` (every policy) | `dmaWriteAtomic` | **new** |
| 7 | fetch × ifetch arm (the fetch pair: view 0 vs `itv ≤ tvn`) | `fetchStale` | `fenceIItvPub` | known (`FetchCutP`, F-6m-1) |

Spec: FAITHFUL (litmus tests; the twin side is `SbCand`'s own rules, the machine side MachCSL's own
definitions).  Lean-only helpers `SbConfLit.*`.
-/
import Weak.SbRealP

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open Sail Sail.ConcurrencyInterfaceV1 LeanRV64D
open Lbl

namespace SbConfLit

/-! # 1. An indexed-landing checker for `SbPol.epoch` runs

`SbCand.runOfB` lands only the OLDEST entry (every lawful policy allows it).  The litmus tests below
that land a hart's YOUNGER entry first need the primary policy: a step's landings are a list of
(agent, index) pairs, each checked by `epochOkB` (same epoch as every older entry, no common byte). -/

/-- `e'` writes a byte of `e`'s footprint (the decision procedure for `SbEnt.overlaps`). -/
def overlapsB (e' e : SbEnt) : Bool := e'.hitsB e.msg.wmPa e.msg.wmData.length

/-- The `SbPol.epoch` landing condition, decided. -/
def epochOkB (es : List SbEnt) (k : Nat) : Bool :=
  decide (k < es.length) &&
  (List.range k).all (fun k' =>
    match es[k']?, es[k]? with
    | some e', some e => decide (e'.fs = e.fs) && !overlapsB e' e
    | _, _ => true)

theorem epochOkBSound (es : List SbEnt) (k : Nat) :
    epochOkB es k = true → SbPol.epoch.landOk es k := by
  intro h
  simp only [epochOkB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨hk, hall⟩ := h
  refine And.intro hk (fun k' e' e hlt h1 h2 => ?_)
  have hc := hall k' (List.mem_range.2 hlt)
  simp only [h1, h2, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hc
  refine ⟨hc.1, fun ho => ?_⟩
  have := SbEnt.hitsBOf _ _ _ ho
  rw [overlapsB, this] at hc
  cases hc.2

/-- Landings of the listed (agent, index) entries, in order. -/
def landIdx (σ : SbCand.CandS) : List (Nat × Nat) → SbCand.CandS
  | [] => σ
  | p :: ps => landIdx (SbCand.nextL σ p.1 p.2) ps

def landIdxB (σ : SbCand.CandS) : List (Nat × Nat) → Bool
  | [] => true
  | p :: ps => epochOkB (σ.sb p.1) p.2 && landIdxB (SbCand.nextL σ p.1 p.2) ps

theorem landIdxSound : ∀ (ps : List (Nat × Nat)) (σ : SbCand.CandS),
    SbCand.Inv σ → landIdxB σ ps = true →
    SbCand.Lands SbPol.epoch σ (landIdx σ ps) ∧ SbCand.Inv (landIdx σ ps)
  | [], σ, hI, _ => ⟨.refl σ, hI⟩
  | p :: ps, σ, hI, h => by
    simp only [landIdxB, Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    have hl : SbCand.land SbPol.epoch σ p.1 p.2 (SbCand.nextL σ p.1 p.2) := .mk (epochOkBSound _ _ h1)
    obtain ⟨h3, h4⟩ := landIdxSound ps _ (SbCand.invNextL σ p.1 p.2 hI) h2
    exact ⟨.step _ _ _ p.1 p.2 hl h3, h4⟩

/-- A macro step: an event, then the listed indexed landings. -/
def nextMI (σ : SbCand.CandS) (st : Estep × List (Nat × Nat)) : SbCand.CandS :=
  landIdx (SbCand.nextE σ st.1.esAg st.1.esLb) st.2

def statesOfI (σ : SbCand.CandS) : List (Estep × List (Nat × Nat)) → List SbCand.CandS
  | [] => [σ]
  | st :: rest => σ :: statesOfI (nextMI σ st) rest

def runOkIB (σ : SbCand.CandS) : List (Estep × List (Nat × Nat)) → Bool
  | [] => true
  | st :: rest => SbCand.okEB σ st.1.esAg st.1.esLb &&
      landIdxB (SbCand.nextE σ st.1.esAg st.1.esLb) st.2 &&
      runOkIB (nextMI σ st) rest

theorem statesOfIHead (σ : SbCand.CandS) (steps : List (Estep × List (Nat × Nat))) :
    (statesOfI σ steps)[0]? = some σ := by
  cases steps <;> rfl

theorem runSoundI : ∀ (steps : List (Estep × List (Nat × Nat))) (σ : SbCand.CandS),
    SbCand.Inv σ → runOkIB σ steps = true →
    SbCand.Steps SbPol.epoch (statesOfI σ steps) (steps.map Prod.fst)
  | [], _, _, _ => ⟨rfl, fun _ _ _ _ hs => by simp at hs⟩
  | st :: rest, σ, hI, h => by
    simp only [runOkIB, Bool.and_eq_true] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    have he := SbCand.okEBSound σ st.1.esAg st.1.esLb hI h1
    obtain ⟨hl, hI'⟩ := landIdxSound st.2 _ (SbCand.invStepE _ _ _ _ hI he) h2
    exact SbCand.stepsCons SbPol.epoch σ (nextMI σ st) st.1 _ _
      (runSoundI rest _ hI' h3) (statesOfIHead _ _) ⟨_, he, hl⟩

/-- **THE INDEXED CHECKER**: a passing step list from an initial state is a buffered run under the
primary policy `SbPol.epoch` (RVWMO's store order, `SbPol.leEpoch`). -/
theorem runOfIB (σ0 : SbCand.CandS) (steps : List (Estep × List (Nat × Nat))) :
    SbCand.initS σ0 → runOkIB σ0 steps = true →
    SbCand.execWfP SbPol.epoch ⟨statesOfI σ0 steps, steps.map Prod.fst⟩ := fun hi h =>
  ⟨fun σ h0 => by
      rw [statesOfIHead, Option.some.injEq] at h0
      subst h0; exact hi,
    runSoundI steps σ0 (SbCand.invInit σ0 hi) h⟩

/-- The litmus start: every byte `0` in the image, empty log, initial views, empty buffers. -/
def litInit : SbCand.CandS := ⟨⟨fun _ => some 0#8, [], fun _ => wsInit⟩, fun _ => []⟩

theorem litInitOk : SbCand.initS litInit := ⟨rfl, fun _ => rfl, fun _ => rfl⟩

/-! # 2. F-PW6-1, the full S shape (land × land arm; known)

Hart 0: `sw x,1 ; sw z,1`.  Hart 1: `lw z (= 1) ; sw x,2`.  Final `x = 1` (co: `x:=2` before `x:=1`).
Addresses `x = 0`, `z = 1`.  RVWMO allows it (no ppo between hart 0's two stores, none between hart 1's
load and store).  The twin: hart 0's `z` lands first (its younger entry: same epoch, other byte), hart 1
reads it at the top, issues and lands `x:=2`, hart 0's `x:=1` lands last.  MachCSL: hart 0's `x:=1` is
pending below hart 1's `x:=2` (issued first), so `x:=2` cannot land (`SbRealP.landBlockedForeign`);
`x:=1` landing first gives final `x = 2`.  (This mechanizes the chain the B6 review noted as "argued,
not checked" [B6.s4].) -/

def sSteps : List (Estep × List (Nat × Nat)) :=
  [(⟨0, LStore false 0 [1#8] .WCplain⟩, []),
   (⟨0, LStore false 1 [1#8] .WCplain⟩, [(0, 1)]),
   (⟨1, LLoad false 1 [1] [1#8]⟩, []),
   (⟨1, LStore false 0 [2#8] .WCplain⟩, [(1, 0), (0, 0)])]

theorem sRun : SbCand.execWfP SbPol.epoch ⟨statesOfI litInit sSteps, sSteps.map Prod.fst⟩ :=
  runOfIB litInit sSteps litInitOk (by decide +kernel)

/-- The final log (co order of `x`: `x:=2` then `x:=1`, so final `x = 1`). -/
theorem sLog :
    (statesOfI litInit sSteps).getLast?.map (·.ms.msLog) =
      some [⟨1, [1#8], some 0, .WCplain⟩, ⟨0, [2#8], some 1, .WCplain⟩, ⟨0, [1#8], some 0, .WCplain⟩] := by
  decide +kernel

/-! # 3. `fence.i`'s kept drain (fence × blocked draining fence; known — the fetch marker)

Message passing with `fence.i` on the writer: hart 0 `sw x,1 ; fence.i ; sw y,1`; hart 1
`lw y (= 1) ; fence r,r ; lw x (= 0)`.  riscv.cat has no `fence.i` ordering, so hart 0's two stores may
reach memory in either order: ALLOWED.  The twin's `fence.i` label is `LFence false×4` (no drain, no
epoch), so `y` lands first.  MachCSL's `fence.i` waits for an empty buffer ([OWN.146], EX-FENCEI-1):
with `x` pending there is no `evStep` answer (`fenceIBlocked`), so `x` lands before `y` issues and hart
1's `fence r,r` then forces `x = 1`. -/

def fiSteps : List (Estep × List (Nat × Nat)) :=
  [(⟨0, LStore false 0 [1#8] .WCplain⟩, []),
   (⟨0, LFence false false false false⟩, []),
   (⟨0, LStore false 1 [1#8] .WCplain⟩, [(0, 1)]),
   (⟨1, LLoad false 1 [1] [1#8]⟩, []),
   (⟨1, LFence true false true false⟩, []),
   (⟨1, LLoad false 0 [0] [0#8]⟩, [(0, 0)])]

theorem fiRun : SbCand.execWfP SbPol.epoch ⟨statesOfI litInit fiSteps, fiSteps.map Prod.fst⟩ :=
  runOfIB litInit fiSteps litInitOk (by decide +kernel)

/-- **The machine side**: with a pending store, `fence.i` has no answer and is blocked. -/
theorem fenceIBlocked (σ : MState) (cpu : CPU) (h : σ.sb cpu ≠ []) :
    (∀ v σ', ¬ evStep cpu (.barrier .Barrier_RISCV_i) σ v σ') ∧
    blockedStep cpu (.barrier .Barrier_RISCV_i) σ σ := by
  refine ⟨fun v σ' hs => ?_, ⟨rfl, h, rfl⟩⟩
  obtain ⟨h1, -⟩ := hs
  exact h (h1 rfl)

/-! # 4. F-PW6-2, DMA order (device row × `storeDma`; known, ruled [OWN.148])

The disk (agent `NCPU = 8`) writes `x := 1` then `y := 1` (two `DWriteDev` stores, no `DFence` between);
hart 0 reads `y (= 1) ; fence r,r ; x (= 0)`.  The twin buffers the device's stores and, under
`SbPol.epoch`, lands `y` first.  MachCSL's DMA write lands in the device's program step
(`dmaLandsAtOnce`: the landing log grows by the store, no buffer), so `x` is landed before `y` and the
`fence r,r` forces `x = 1`.  (The device model is platform text: OUTSIDE SPEC.  The [OWN.148] gate — a
device-row head waits for an empty own buffer — removes this run from the walk.) -/

def dmaSteps : List (Estep × List (Nat × Nat)) :=
  [(⟨8, LStore false 0 [1#8] .WCplain⟩, []),
   (⟨8, LStore false 1 [1#8] .WCplain⟩, [(8, 1)]),
   (⟨0, LLoad false 1 [1] [1#8]⟩, []),
   (⟨0, LFence true false true false⟩, []),
   (⟨0, LLoad false 0 [0] [0#8]⟩, [(8, 0)])]

theorem dmaRun : SbCand.execWfP SbPol.epoch ⟨statesOfI litInit dmaSteps, dmaSteps.map Prod.fst⟩ :=
  runOfIB litInit dmaSteps litInitOk (by decide +kernel)

/-- **The machine side**: a DMA write of at least one byte lands AT ONCE (the landing log grows by its
issue stamp) and touches no store buffer. -/
theorem dmaLandsAtOnce (σ : MState) (pa : PAddr) (n : Nat) (w : BitVec (8 * n)) (hn : n ≠ 0) :
    (σ.storeDma pa n w).llog = σ.llog ++ [σ.top + 1] ∧ (σ.storeDma pa n w).sb = σ.sb :=
  ⟨MState.storeDma_llog_of_ne σ pa n w hn, rfl⟩

/-! # 5. F-CM-2 (NEW): the `DRIVER_OK` step guard (io × MMIO-write arm / its blocked arm)

xv6 weak-memory bug #1 ([OWN.127]/[OWN.131]): hart 0 zeroes a virtqueue page (`sw q,0`, `q = 5`, the
image holds junk `7` there) and then stores `DRIVER_OK` to MMIO (`LIo .wr`); the disk then reads `q`.
RVWMO + PMAs allow the device to read the junk (no `fence w,o`).  The twin's `LIo` is inert and has no
guard, so the run below is an `SbCand` run under every lawful policy (the disk reads `7` at the top,
hart 0's store lands last).  MachCSL's MMIO-write arm requires `MState.drvOkGuard` (hart 0, at
`drvOkPc`, no pending store to the three queue pages) and the store is otherwise BLOCKED
(`drvOkBlocked`), so the device can only read the landed `0`.  The realization has no machine step for
the twin's `LIo` while the zeroing store is pending: a gap NOT handled by the walk (`SbOrd.enbL`'s `LIo`
arm is `True`) and not among F-PW6-1/2/3 or the fetch pair.  At the GRAPH level the trusted (R1)
(`GraphFabResidue.ioResidue`: a RAM access po-before an I/O event is gmo-before it) already orders the
zeroing store before the `DRIVER_OK` event, so a walk gate (a hart's I/O head waits for its pending
stores) has its progress from (R1); this run is a twin run, not a walk of an (R1)-graph. -/

/-- The junk image: byte `5` holds `7`. -/
def junkInit : SbCand.CandS :=
  ⟨⟨fun a => if a = 5 then some 7#8 else some 0#8, [], fun _ => wsInit⟩, fun _ => []⟩

def drvSteps : List (Estep × List Nat) :=
  [(⟨0, LStore false 5 [0#8] .WCplain⟩, []),
   (⟨0, LIo .wr 100 [4#8]⟩, []),
   (⟨8, LLoad false 5 [0] [7#8]⟩, [0])]

theorem drvRun (pol : SbPol) :
    SbCand.execWfP pol ⟨SbCand.statesOf junkInit drvSteps, drvSteps.map Prod.fst⟩ :=
  SbCand.runOfB pol _ _ ⟨rfl, fun _ => rfl, fun _ => rfl⟩ (by decide +kernel)

/-- **The machine side**: at `drvOkPc`, with a pending queue-page store, hart 0's guard fails, so its
`DRIVER_OK` MMIO store has no `evStep` answer and is blocked (`blockedStep`'s MMIO arm). -/
theorem drvOkBlocked (σ : MState) (cpu : CPU) (h0 : cpu.val = 0)
    (hpc : (σ.regs cpu) Register.PC = drvOkPc) (hp : σ.vqPagesPend cpu) :
    ¬ σ.drvOkGuard cpu ∧
    ∀ o, (∃ n va req, o = Outcome.memWrite n va req ∧ devBytes req.pa n ∧ 0 < n) →
      blockedStep cpu o σ σ := by
  refine ⟨fun hg => hg h0 hpc hp, ?_⟩
  rintro o ⟨n, va, req, rfl, hd, hn⟩
  exact Or.inr ⟨hd, hn, fun hg => hg h0 hpc hp, rfl⟩

/-! # 6. F-CM-1 (NEW): a buffered device store's FABRIC MOVE before its landing (device row × `dmaWrite`)

The disk's used-index `DWriteDev` (`u = 5`, value `1`) moves the fabric IN ITS PROGRAM STEP (`complete`:
`isr` set, `usedIdx + 1`; `VirtioProg.lean` node table) while `SbCand` buffers its RAM store.  A
fabric-LATER hart MMIO access — here hart 0's read of `InterruptStatus` (`LIo .rd`, answered `1` by the
moved fabric) — is enabled once the store is ISSUED (`SbOrd.fabOk` asks "realized", not "landed"), and the
hart's following top read of `u` sees the old `0`.  The run is an `SbCand` run under every lawful
policy.  MachCSL performs the device-state move and the DMA landing in ONE transition
(`dmaWriteAtomic`), so under `rmemP` (R-lp: landing order = the walk's) the realization has, between
the twin's issue and landing, either a machine device state that has not moved (the MMIO read answers
`isr = 0`: `R-dev` broken) or a landed `u` (R-lp broken).  The [OWN.148] gate (the device ROW's own
head waits) does not cover it: the reader is a HART row.  At the graph level the trusted (R3) (fabric
order ⊆ gmo on memory events, `SbOrd.blkFab`'s `hr3`) puts the store gmo-before the reader, so a gate
"an earlier fabric STORE has LANDED" has its progress from (R3). -/

def fabSteps : List (Estep × List Nat) :=
  [(⟨8, LStore false 5 [1#8] .WCplain⟩, []),
   (⟨0, LIo .rd 200 [1#8]⟩, []),
   (⟨0, LLoad false 5 [0] [0#8]⟩, [8])]

theorem fabRun (pol : SbPol) :
    SbCand.execWfP pol ⟨SbCand.statesOf litInit fabSteps, fabSteps.map Prod.fst⟩ :=
  SbCand.runOfB pol _ _ litInitOk (by decide +kernel)

/-- **The machine side**: an answered DMA write over DRAM moves the device state AND lands the store in
the same transition. -/
theorem dmaWriteAtomic (gen : Nat) (d : DevId) (g : DevSt d → Option (DevSt d)) (pa : PAddr) (n : Nat)
    (w : BitVec (8 * n)) (σ : MState) (s' : DevSt d) (hg : g (σ.devs.st d) = some s')
    (hram : ramBytes pa n) (hn : n ≠ 0) :
    ∀ v σ' obs efs, devOpStep gen d (.dmaWrite g pa n w) σ v σ' obs efs →
      σ'.llog = σ.llog ++ [σ.top + 1] ∧ σ'.devs = σ.devs.set d s' := by
  intro v σ' obs efs hs
  obtain ⟨-, -, ⟨s'', hg', -, -, -, rfl⟩ | ⟨hno, rfl⟩⟩ := hs
  · rw [hg] at hg'
    cases hg'
    exact ⟨MState.storeDma_llog_of_ne σ pa n w hn, rfl⟩
  · rcases hno with h | h
    · rw [hg] at h; cases h
    · exact absurd hram h

/-! # 7. The fetch pair (fetch × ifetch arm; known — `FetchCutP`, F-6m-1)

The walk's fetch reads at view `0` of the landed log (`SbWalk.evData`: `ifetchOk … 0`): every value a
byte EVER held is fetchable (`ifetchByteOk0`), the image's in particular, even after the byte was
rewritten and landed.  MachCSL's ifetch arm reads at `itv ≤ tvn ≤ ltop`, and `fence.i` raises `itv` past
the hart's own last landed store (`fenceIItvPub`), so after `sw x,1 ; (landed) ; fence.i` the machine
cannot fetch the old byte. -/

/-- The twin fetch reads the image byte `0` at `x = 0` although the log rewrote it to `1`. -/
theorem fetchStale :
    ifetchOk (fun _ => some 0#8) [⟨0, [1#8], some 0, .WCplain⟩] 0 0 [(0, 0#8)] := by
  intro j t v h
  cases j with
  | zero =>
    simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact (ifetchByteOk0 _ _ _ _ _).2 (by decide +kernel)
  | succ j => simp at h

/-- **The machine side**: `fence.i` raises the instruction view to at least the hart's own last LANDED
store (`ownPubL`), the floor of every later fetch (`evStep`'s ifetch arm: `itv ≤ tvn`). -/
theorem fenceIItvPub (σ : MState) (cpu : CPU) :
    ownPubL (hartAgent cpu) σ.log σ.llog ≤ (σ.fence cpu .Barrier_RISCV_i).itv cpu := by
  show ownPubL (hartAgent cpu) σ.log σ.llog ≤
    (if cpu = cpu then
      (if fenceIfetch .Barrier_RISCV_i then
        max (σ.itv cpu) (MachCSL.fencePost true true (σ.tv cpu) (σ.hr cpu).rv (ownPubL (hartAgent cpu) σ.log σ.llog))
       else σ.itv cpu)
     else σ.itv cpu)
  simp only [if_true, fenceIfetch]
  unfold MachCSL.fencePost
  simp only [if_true]
  omega

#print axioms Weak.SbConfLit.sRun
#print axioms Weak.SbConfLit.fiRun
#print axioms Weak.SbConfLit.dmaRun
#print axioms Weak.SbConfLit.drvRun
#print axioms Weak.SbConfLit.fabRun
#print axioms Weak.SbConfLit.fenceIBlocked
#print axioms Weak.SbConfLit.drvOkBlocked
#print axioms Weak.SbConfLit.dmaWriteAtomic
#print axioms Weak.SbConfLit.fetchStale
#print axioms Weak.SbConfLit.fenceIItvPub

end SbConfLit

end Weak
