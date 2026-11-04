/-
Weak: **THEOREM 2 / certificate (a′): `allocpidOpen` APPLIED** — Theorem 2 (AxSpinT2b) instantiated
on the concrete 3-hart serial run of xv6's REAL inlined-allocpid segment built in AxSpinT2pt and
AxSpinT2c1..c5 (harts A, B, C = 0, 1, 2 on slots proc[0], proc[1], proc[2]; nextpid 1 → 2 → 3 → 4),
with C := the SAME allocpid segment on its slot.  Every premise of `allocpidOpen` is discharged;
the final theorem `allocpidOpenCert` has NO hypotheses.  It is the non-vacuity certificate of
Theorem 2: its premises are jointly satisfiable, on a graph whose rows are the real machine's.

Lean-only (no Rocq source).  Design `notes/weak-lb-thm2-design.md` §C.6, §D row `AxSpinT2c`
(in ../xv6iris-lbthm2).

## What this file proves

§1 THE ENTRY STATE.  `ctrlOkSWE`: `ctrlOkSW tX satpX (regsE h)` for h ∈ {0, 1, 2} (the S-mode
regime of AxSpineOk6's `ctrlOkS` — every conjunct a closed `decide +kernel` / `rfl` on the
register file, its TLB conjunct AxSpinT2c5's `tlbExactW` — plus the PMP W bit `pmpW`);
`entryOkE`: AxSpinT2a's `entryOk` of `s0X h = AxEpiRun.st (cpuOf h) (.pure ()) (regsE h) ibNone 0`
(PC = allocproc + 0x38, `sp = sZ h`, `s1 = &proc[h]`, `tp = h`, warm TLB `AxSpinT2c1.entryHit`).
§2 THE RUN.  `hartsX` (`Hharts`: `gmo` = the interleaving `il3`, every event of hart 0, 1, 2, read
off `AxSpinT2c1.shil3`); the runs, end states and step counts of the three harts are taken from
`AxSpinT2c2.runA` / `AxSpinT2c3.runB` / `AxSpinT2c4.runC` at the emission
`E = [emsA, emsB, emsC]` — the DRIVES' OWN EMISSION (the honest choice: the graph's
dependency/emission component is what the real `riscvStep` emitted).
§3 C's WPd.  `wpdC`: C runs the same segment, so its `HwpC` is `AxSpinApA.wpdAllocpidSegE` for hart
2 (its `AxSpinApA.Hyp` by `AxSpinApA.hypXv6`, its `entryOk` by `entryOkE`), weakened to post
`True` by `AxSpinWit.tierAWpdMono`, from C's share `xv6Init` (`AxSpinT2b.initCs`).
§4 THE PIDS.  `pidLit`: the stored pid words of A, B, C on the literal rows are 1, 2, 3.
§5 **`allocpidOpenCert`** (NO hypotheses), at `GD = gtAdGd (gT3 [emsA, emsB, emsC])`,
`L = xlayXv6 0 1 2 sZ pEx ptpX`, `q = AxSpinT2c1.q0`:
  `npSrc GD.gdG L (0, t2KBd q0) (0, t2KA q0) ∧ npSrc GD.gdG L (1, t2KBd q0) (1, t2KA q0) ∧
   t2Complete GD 0 (sZ 0) (pEx 0) ∧ t2Complete GD 1 (sZ 1) (pEx 1) ∧
   pidOf GD 0 q0 ≠ pidOf GD 1 q0 ∧
   pidOf GD 0 q0 = some (wbytes 4 1#32) ∧ pidOf GD 1 q0 = some (wbytes 4 2#32) ∧
   pidOf GD 2 q0 = some (wbytes 4 3#32)`
— the first, second and fifth conjuncts come from `allocpidOpen` (its `t2Complete →` premises
discharged by `AxSpinT2c1.completeG`, so they are NOT vacuous here); the pid words are read off
the literal rows (`pidLit`).  The model premises (`rvwmoCatConsistentT`, `ctrlClosed`) are the
GENERIC SC lemmas `AxSpinT2c1.cat3` / `ctrl3` on the drives' `hartOkB` checks.

## Pins / honesty

* No drive is re-evaluated here: every fact about `drvA/B/C` / `emsA/B/C` comes through `runA/B/C`
  (AxSpinT2c1.runOfChk, stated over a variable drive result); the proofs never `cases` / `decide`
  on `emsA`, and `gT3 E`'s rows are `E`-independent (`AxSpinT2c1.growG3`).
* The pins of `allocpidOpen` (AllocPins, the value conditions of `allocFull`) hold on this run
  (AxSpinT2c1 `pinsG` / `fullG`); the certificate shows the PREMISES are satisfiable, on a serial
  (SC) run.  It does not exercise C's freedom (C here is the same allocpid); the theorem's content
  for an adversarial C is AxSpinT2b's, and its necessity is certificate (b) (AxSpinT2d).
* The entry state is AxSpinT2pt's `regsE` (the S-mode spike register file re-pointed, warm TLB
  `tlbW`, A/D-preset kvmmake-shaped `tX`: design §A.5 HAD scope), the image is AxSpinT2c5's `σX`.

Reused: `allocpidOpen`, `AxSpinT2b.initCs` (AxSpinT2b), `AxSpinApA.hypXv6`/`wpdAllocpidSegE`/
`t2PostS`, `AxSpinWit.tierAWpdMono`, `AxSpinT2pt.regsE`/`satpXFacts`/`regsEFacts`, `AxSpinT2c1.*`
(`gT3`, `growG3`, `gdRow`, `shil3`, `cat3`, `ctrl3`, `fullG`, `pinsG`, `completeG`, `layHyp3`,
`entryHit`, `finNotMid`, `sZ`, `q0`, `ptpX`), `AxSpinT2c2.runA`, `AxSpinT2c3.runB`,
`AxSpinT2c4.runC`, `AxSpinT2c5.*` (`σX`, the text premises, `textFixedX`, `mapOk3`, `tlbExactW`,
`imgClb`, `imgNp`, `al3`), `ctrlOkS`/`pmpW`/`ctrlOkSW`, tactic pattern of `nvSCtrlOk`
(AxSpineOk8).
Names: `allocpidOpenCert` (Lean-only, grepped absent); helpers in the namespace `Weak.AxSpinT2c`.
-/
import Weak.AxSpinT2b
import Weak.AxSpinT2c2
import Weak.AxSpinT2c3
import Weak.AxSpinT2c4
import Weak.AxSpinT2c5

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D LeanRV64D.Functions
open AxSpinT2pt AxSpinT2c1 AxSpinT2c5

namespace AxSpinT2c

/-! # 1. The entry state -/

/-- The entry `satp` value. -/
def satpE : BitVec 64 := BitVec.ofNat 64 satpX

/-- Hart `h`'s entry state (allocproc + 0x38, `regsE h`, row position 0). -/
def s0X (h : Agent) : Athread := AxEpiRun.st (cpuOf h) (.pure ()) (regsE h) ibNone 0

/-- One `ctrlOkSW` conjunct of `regsE h` (closed). -/
local macro "ax_t2c_ctrl" : tactic => `(tactic|
  (unfold ctrlOkSW ctrlOkS AxSpineOk6.pmpOk AxSpineOk6.sconfMsFacts pmpW
   refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_,
     tlbExactW, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
   all_goals first | rfl | decide +kernel))

theorem ctrlOkSW0 : ctrlOkSW tX satpE (regsE 0) := by ax_t2c_ctrl
theorem ctrlOkSW1 : ctrlOkSW tX satpE (regsE 1) := by ax_t2c_ctrl
theorem ctrlOkSW2 : ctrlOkSW tX satpE (regsE 2) := by ax_t2c_ctrl

/-- **`ctrlOkSW`** of the entry registers of (a′)'s three harts. -/
theorem ctrlOkSWE (h : Agent) (hh : h < 3) : ctrlOkSW tX satpE (regsE h) := by
  match h, hh with
  | 0, _ => exact ctrlOkSW0
  | 1, _ => exact ctrlOkSW1
  | 2, _ => exact ctrlOkSW2
  | n + 3, hh => exact absurd hh (Nat.not_lt.2 (Nat.le_add_left 3 n))

/-- The register facts of `entryOk` (closed, per hart). -/
theorem regFacts (h : Agent) (hh : h < 3) :
    (regsE h) .PC = pca 0x38 ∧ gprVal (regsE h) 2#5 = BitVec.ofInt 64 (sZ h) ∧
    gprVal (regsE h) 9#5 = BitVec.ofInt 64 (AxSpinT2a.pEx h) ∧
    gprVal (regsE h) 4#5 = hartId (cpuOf h) := by
  match h, hh with
  | 0, _ => exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩
  | 1, _ => exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩
  | 2, _ => exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩
  | n + 3, hh => exact absurd hh (Nat.not_lt.2 (Nat.le_add_left 3 n))

/-- **`entryOk`** of (a′)'s three harts (AxSpinT2b `HentA` / `HentB`, and C's). -/
theorem entryOkE (h : Agent) (hh : h < 3) :
    entryOk tX satpE h (sZ h) (AxSpinT2a.pEx h) (s0X h) := by
  obtain ⟨h1, h2, h3, h4⟩ := regFacts h hh
  exact ⟨regsE h, ibNone, rfl, ctrlOkSWE h hh, h1, h2, h3, h4, entryHit h hh⟩

/-! # 2. The run -/

/-- **`Hharts`**: only harts 0, 1, 2 emit events (`gmo` is the interleaving `il3`). -/
theorem hartsX (E : List (List Eitem)) :
    ∀ e, e ∈ (gT3 E).gtG.gxGmo → e.1 ∈ [(0 : Agent), 1, 2] := by
  intro e he
  have H := shil3
  simp only [ilOkB, Bool.and_eq_true] at H
  have hl := of_decide_eq_true (List.all_eq_true.1 H.2.1 e he)
  have h3 : rows3.length = 3 := rfl
  rw [h3] at hl
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  omega

/-- Pick by hart (0 → `a`, 1 → `b`, else `c`). -/
def pick3 {α : Type} (a b c : α) (i : Agent) : α :=
  if i = 0 then a else if i = 1 then b else c

theorem pick3Z {α : Type} (a b c : α) : pick3 a b c 0 = a := rfl
theorem pick3O {α : Type} (a b c : α) : pick3 a b c 1 = b := rfl
theorem pick3T {α : Type} (a b c : α) : pick3 a b c 2 = c := rfl

theorem stAtK (cpu : CPU) (m : SailM Unit) (rs : RegFile) (ib : Ibch) (k : Nat) :
    (AxEpiRun.st cpu m rs ib k).atK = k := rfl

/-! # 3. C's WPd -/

section wpdC
variable [Hinv : InvGS_gen .hasNoLC AxSpinX7.xv6GF] [Hann : AxannotGS AxSpinX7.xv6GF]

/-- **C's `HwpC`**: C runs the same allocpid segment (AxSpinApA's whole-segment WPd for hart 2),
weakened to post `True`. -/
theorem wpdC (E : List (List Eitem)) (nm : Xv6N) (Hcons : rvwmoCatConsistent (gtAdGd (gT3 E))) :
    ⊢ xv6Init (xlayXv6 0 1 2 sZ AxSpinT2a.pEx ptpX) (gtAdGd (gT3 E)) nm 2 -∗
      @tierAWpd AxSpinX7.xv6GF .hasNoLC _ _ (xv6Pol (gT3 E)) (gtAdGd (gT3 E)) Xv6N Unit
        (protXv6 (xlayXv6 0 1 2 sZ AxSpinT2a.pEx ptpX)) nm (s0X 2) .MaybeStuck 2
        (fun _ => iprop(True)) := by
  have HL := xlayXv6Ok 0 1 2 sZ AxSpinT2a.pEx ptpX layHyp3
  obtain ⟨hmode, hasid, hppn⟩ := satpXFacts
  have HyC := AxSpinApA.hypXv6 0 1 2 sZ AxSpinT2a.pEx ptpX layHyp3 (gT3 E) σX tX 2 q0
    (.inr (.inr rfl)) (al3 2) (fullG E 2 (by decide)) (pinsG E 2 (by decide)) (mapOk3 2 (by decide))
    acquireTextX mycpuTextX pushOffTextX holdingTextX popOffTextX releaseTextX allocpidTextX
    tailTextX (textFixedX E 2 (by decide))
  have WC := (AxSpinApA.wpdAllocpidSegE (hlc := .hasNoLC) (GF := AxSpinX7.xv6GF)
    (xlayXv6 0 1 2 sZ AxSpinT2a.pEx ptpX) (gT3 E) nm HL Hcons σX tX satpE hmode hasid hppn 2 q0
    (sZ 2) (AxSpinT2a.pEx 2) HyC (s0X 2) (entryOkE 2 (by decide))).trans
    (wand_mono .rfl (wand_mono .rfl
      (AxSpinWit.tierAWpdMono (hlc := .hasNoLC) (pol := xv6Pol (gT3 E)) (gtAdGd (gT3 E)) Xv6N Unit
        (protXv6 (xlayXv6 0 1 2 sZ AxSpinT2a.pEx ptpX)) nm (s0X 2) .MaybeStuck 2
        (AxSpinApA.t2PostS (gtAdGd (gT3 E)) (xlayXv6 0 1 2 sZ AxSpinT2a.pEx ptpX) nm 2 q0)
        (fun _ => iprop(True)) (fun _ => by iintro -; itrivial))))
  iintro HC
  ihave HC := AxSpinT2b.initCs (xlayXv6 0 1 2 sZ AxSpinT2a.pEx ptpX) (gtAdGd (gT3 E)) nm 2 $$ HC
  icases HC with ⟨Hil, Hnh⟩
  ihave W := WC $$ []
  · iempintro
  iapply W $$ Hil Hnh

end wpdC

/-! # 4. The pids -/

/-- The pid words A, B, C store in `p->pid` (literal rows; `E`-independent). -/
theorem pidLit (E : List (List Eitem)) :
    pidOf (gtAdGd (gT3 E)) 0 q0 = some (WeakInterpProj.wbytes 4 1#32) ∧
    pidOf (gtAdGd (gT3 E)) 1 q0 = some (WeakInterpProj.wbytes 4 2#32) ∧
    pidOf (gtAdGd (gT3 E)) 2 q0 = some (WeakInterpProj.wbytes 4 3#32) := by
  simp only [pidOf, gdRow, growG3]
  decide +kernel

end AxSpinT2c

open AxSpinT2c AxSpinT2c2 AxSpinT2c3 AxSpinT2c4

/-! # 5. THE CERTIFICATE -/

set_option maxHeartbeats 1600000 in
/-- **Certificate (a′): Theorem 2 APPLIED, no hypotheses.**  On the concrete 3-hart serial run of
xv6's real inlined allocpid (harts 0, 1, 2 on proc[0..2], C := the same segment), at the drives'
own emission: A's and B's nextpid reads are sourced by the gmo-latest nextpid write before their
claim, both rows are complete, and the stored pids are distinct — concretely 1 and 2 (C's is 3). -/
theorem allocpidOpenCert :
    npSrc (gtAdGd (gT3 [emsA, emsB, emsC])).gdG (xlayXv6 0 1 2 sZ AxSpinT2a.pEx ptpX)
      (0, t2KBd q0) (0, t2KA q0) ∧
    npSrc (gtAdGd (gT3 [emsA, emsB, emsC])).gdG (xlayXv6 0 1 2 sZ AxSpinT2a.pEx ptpX)
      (1, t2KBd q0) (1, t2KA q0) ∧
    t2Complete (gtAdGd (gT3 [emsA, emsB, emsC])) 0 (sZ 0) (AxSpinT2a.pEx 0) ∧
    t2Complete (gtAdGd (gT3 [emsA, emsB, emsC])) 1 (sZ 1) (AxSpinT2a.pEx 1) ∧
    pidOf (gtAdGd (gT3 [emsA, emsB, emsC])) 0 q0 ≠ pidOf (gtAdGd (gT3 [emsA, emsB, emsC])) 1 q0 ∧
    pidOf (gtAdGd (gT3 [emsA, emsB, emsC])) 0 q0 = some (WeakInterpProj.wbytes 4 1#32) ∧
    pidOf (gtAdGd (gT3 [emsA, emsB, emsC])) 1 q0 = some (WeakInterpProj.wbytes 4 2#32) ∧
    pidOf (gtAdGd (gT3 [emsA, emsB, emsC])) 2 q0 = some (WeakInterpProj.wbytes 4 3#32) := by
  obtain ⟨uA, rsA, ibA, -, okA, runA'⟩ := runA
  obtain ⟨uB, rsB, ibB, -, okB, runB'⟩ := runB
  obtain ⟨uC, rsC, ibC, -, okC, runC'⟩ := runC
  obtain ⟨nA, HnA⟩ := runA' [emsA, emsB, emsC]
  obtain ⟨nB, HnB⟩ := runB' [emsA, emsB, emsC]
  obtain ⟨nC, HnC⟩ := runC' [emsA, emsB, emsC]
  have HconsT := cat3 emsA emsB emsC okA okB okC
  have Hcl := ctrl3 emsA emsB emsC okA okB okC
  obtain ⟨hmode, hasid, hppn⟩ := satpXFacts
  obtain ⟨sN, hsN⟩ : ∃ f : Agent → Athread, f = pick3
    (AxEpiRun.st (cpuOf 0) (.pure uA) rsA ibA
      (AxOpsem.grow (gtAdGd (gT3 [emsA, emsB, emsC])) 0).length)
    (AxEpiRun.st (cpuOf 1) (.pure uB) rsB ibB
      (AxOpsem.grow (gtAdGd (gT3 [emsA, emsB, emsC])) 1).length)
    (AxEpiRun.st (cpuOf 2) (.pure uC) rsC ibC
      (AxOpsem.grow (gtAdGd (gT3 [emsA, emsB, emsC])) 2).length) := ⟨_, rfl⟩
  have Hrun : ∀ (_ : AxannotGS AxSpinX7.xv6GF) (nm : Xv6N) i, i ∈ [(0 : Agent), 1, 2] →
      nsteps (tierAAstep (gtAdGd (gT3 [emsA, emsB, emsC])) nm i) (pick3 nA nB nC i) (s0X i)
        (sN i) := by
    intro _ nm i Hi
    rcases AxSpinT2b.mem3 Hi with rfl | rfl | rfl
    · rw [hsN, pick3Z, pick3Z]; exact HnA (cpuOf 0) Xv6N nm
    · rw [hsN, pick3O, pick3O]; exact HnB (cpuOf 1) Xv6N nm
    · rw [hsN, pick3T, pick3T]; exact HnC (cpuOf 2) Xv6N nm
  have Hend : ∀ i, i ∈ [(0 : Agent), 1, 2] →
      (sN i).atK = (AxOpsem.grow (gtAdGd (gT3 [emsA, emsB, emsC])) i).length := by
    intro i Hi
    rcases AxSpinT2b.mem3 Hi with rfl | rfl | rfl
    · rw [hsN, pick3Z]; exact stAtK _ _ _ _ _
    · rw [hsN, pick3O]; exact stAtK _ _ _ _ _
    · rw [hsN, pick3T]; exact stAtK _ _ _ _ _
  have H := allocpidOpen (gT3 [emsA, emsB, emsC]) 0 1 2 sZ AxSpinT2a.pEx ptpX q0 q0 σX tX satpE 1
    s0X sN (pick3 nA nB nC) HconsT Hcl (hartsX _) layHyp3 (al3 0) (al3 1)
    (imgClb _ _ rfl) (by decide) (imgNp _ _ rfl)
    acquireTextX mycpuTextX pushOffTextX holdingTextX popOffTextX releaseTextX allocpidTextX
    tailTextX (textFixedX _ 0 (by decide)) (textFixedX _ 1 (by decide)) hmode hasid hppn
    (mapOk3 0 (by decide)) (mapOk3 1 (by decide))
    (fullG _ 0 (by decide)) (fullG _ 1 (by decide)) (pinsG _ 0 (by decide)) (pinsG _ 1 (by decide))
    (entryOkE 0 (by decide)) (entryOkE 1 (by decide)) rfl Hrun Hend
    (by rw [hsN, pick3Z]; exact finNotMid _ _ _ _ _) (by rw [hsN, pick3O]; exact finNotMid _ _ _ _ _)
    (fun nm => wpdC _ nm (catTAd _ HconsT))
  obtain ⟨HsA, HsB, Hpid⟩ := H
  have HcA := completeG [emsA, emsB, emsC] 0 (by decide)
  have HcB := completeG [emsA, emsB, emsC] 1 (by decide)
  obtain ⟨Hne, -⟩ := Hpid HcA HcB
  exact ⟨HsA, HsB, HcA, HcB, Hne, pidLit _⟩

end Weak
