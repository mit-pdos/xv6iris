/-
**THE NI TRACE** (NI M2-W4, the pure half; design of record
`claude-notes/projects/noninterference.md`, "M2-W2 design (2026-10-02)" §4
"How W4 consumes it", rulings O1/O5/O6): the boundary trace `h` read per
INCARNATION through a filing `F` the ledger hands back (`NiLedger.niOk`),
the per-round CLASS LAW every incarnation's trace obeys, and the two pure
corollaries -- the two-run statement and the strong instance.

* §1 the incarnation (O1): `incOf h f = (era, pid)` of a filing -- the era
  is `obsBoots (h.take j)` at the filed enter, the pid the filing's key's
  (`NiEntry.pid`); `inc h F j` the incarnation of the enter at `j`.
* §2 the trace: `NiStep` (an origin: its first key and the enter; a round:
  the trapped key's MASK, the cited exit, the enter), `niStepOf`,
  `utrace q h F` (the steps of `q`'s filings in enter order), `firstKey`.
* §3 what a step says: `exitView`/`enterView` (the user-visible content of a
  boundary event: cause, epc and `x1..x31` at an exit; resume pc and
  `x1..x31` at an enter -- the cpu and `satp` are scheduling and placement,
  not the process's), `gprsNum` (the effective syscall number read off an
  exit's registers through a mask), `NiStep.reading` and `events q h F`
  (the class's readings: the answers of the uptime ecalls).
* §4 THE CLASS LAW `NiClassLaw`, and `niOk_classLaw` (pure: from `niOk`).
* §5 the pure corollaries: `niTwoRun` (two runs, one incarnation: equal
  inputs and equal uptime readings give equal enters) and `niStrongInstance`
  (before its first ecall an incarnation's enters replay its exits).

## Honest scope

1. **The class is {exit, getpid, uptime}** (`UsysDet.usysDetClass`, M2-W3);
   every other ecall's enter is UNCONSTRAINED by the law, and the two-run
   corollary assumes the incarnation's ecalls are all in the class.
2. **Origins are honest only with W2d's `niOneShot`** (`NiLedger` F4):
   `niFit none e` is satisfiable by any enter, so `niOk` alone admits filing
   a round's resume as a fresh origin.  The theorem (`NiAdequacy.xv6NiPhi`)
   adds `niOneShot h F` (every filing spent a distinct claim minted in `h`
   before its enter); this file is stated over `niOk h F` only.
3. **THE MASK IS CARRIED PER FILING** (the design's "mask caveat"; the
   alternative -- a lemma that the mask is constant within an incarnation
   until a seccomp round -- is NOT provable from `niOk`: nothing in the
   ledger ties a round's trapped key to the previous round's resumed key).
   The class of a round is decided by `usysEff W.secc`, `W` the round
   filing's trapped key, and the mask is not in `h`; so a round step carries
   `W.secc`, and the two-run corollary's "equal inputs" include each round's
   mask.  Origins carry their whole first key (`firstKey`).
4. **The tick is the reading** (O5): uptime's answer is read off the enter
   (`a0`), and the law says it IS a tick count's word (`usysUptimeRet`);
   cross-process monotonicity of the readings is not exported.
5. **getpid's answer is the incarnation's pid** (§4's "getpid → a0 := sext
   pid_q"): W2d's pid row `niPidRow` in the round filing gives
   `a0 = signExtend 64 W.pid`, and the filing's pid is `W'.pid = W.pid`, the
   incarnation's.  So `events` holds only the uptime readings.

## Deviations from the design text

1. `inc h F j : Option (Nat × BitVec 32)` (no filing at `j`, no
   incarnation); `incOf h f` is the total reading at a filing.
2. `utrace`, `firstKey`, `events` take `h` (the era is read off it).
3. `NiClassLaw q tr` reads only `q`'s pid (getpid's row); the law of one
   step is `NiStep.law pid`, and `niStepOf_law` gives it at the filing's pid
   (`NiEntry.pid`), which `utrace q` makes `q.2`.
4. The class law is derived from `uroundOk`'s readers directly
   (`uroundOk_transparent`/`_ecall`, `UsysDet.uroundOk_exit`,
   `usysMemOk_uptimeRet`, and W2d's `niPidRow` with `usysRetPid_getpid`);
   W3's `usysDet_of_rows`/`uexecRet_roundDet` need the descriptor and
   children rows, which `niOk` does not carry.  At the
   class the two agree: the bumped key's registers are the ones below.
5. `niFilingAt` (not `niFiling`: `NiLedger` names its filing constructor
   so).

PURE: imports `NiLedger` (its pure definitions only) and `UsysDet`.
-/
import Xv6.NiLedger
import Xv6.UsysDet

namespace Xv6

open MachCSL Std

/-! ## §1 The incarnation (ruling O1)

The constructors of `NiEntry` are matched only in `NiEntry.pid` and
`niStepOf` below, and in `niStepOf_law`'s two arms; each pattern ends in
`..`, which absorbs W2d's origin field `p` (the spent claim's position). -/

/-- The pid a filing names: the origin's first key's, a round's resumed key's
(= its trapped key's, `niEntryOk`'s pid tie). -/
def NiEntry.pid : NiEntry → BitVec 32
  | .origin _ W0 .. => W0.pid
  | .round _ _ _ _ W' .. => W'.pid

/-- **An incarnation**: an era (the boot count) and a pid.  Pids are not
reused within an era (`nextpid` only grows; wrap-around is M2-G2's tie) and
restart across eras, hence the pair. -/
abbrev NiInc := Nat × BitVec 32

/-- The incarnation a filing belongs to: the era of its enter's position and
its pid. -/
def incOf (h : List Obs) (f : NiEntry) : NiInc := (obsBoots (h.take f.j), f.pid)

/-- The filing of the enter at `j` (`niOk`: exactly one). -/
def niFilingAt (F : List NiEntry) (j : Nat) : Option NiEntry := F.find? (fun f => f.j == j)

/-- **`inc h F j`**: the incarnation of the enter at position `j`. -/
def inc (h : List Obs) (F : List NiEntry) (j : Nat) : Option NiInc := (niFilingAt F j).map (incOf h)

theorem niFilingAt_mem {F : List NiEntry} {j : Nat} {f : NiEntry} (hf : niFilingAt F j = some f) : f ∈ F :=
  List.mem_of_find?_eq_some hf

/-! ## §2 The trace of an incarnation -/

/-- **One step of an incarnation's trace**: an ORIGIN (the first key the
filing names, the enter at it) or a ROUND (the trapped key's syscall mask --
carried per filing, scope 3 --, the cited exit, the enter). -/
inductive NiStep where
  | origin (W0 : Uvis) (e : Obs)
  | round (secc : BitVec 64) (x e : Obs)

/-- The step a filing reads in `h` (`none` only for a filing `niEntryOk`
rejects). -/
def niStepOf (h : List Obs) : NiEntry → Option NiStep
  | .origin j W0 .. => h[j]?.map (NiStep.origin W0)
  | .round i j _ W _ .. =>
    match h[i]?, h[j]? with
    | some x, some e => some (.round W.secc x e)
    | _, _ => none

/-- **`utrace q h F`**: incarnation `q`'s steps, in the order of their
enters in `h`: at each position, the filing of the enter there, if it is
`q`'s. -/
def utrace (q : NiInc) (h : List Obs) (F : List NiEntry) : List NiStep :=
  (List.range h.length).filterMap fun j =>
    match niFilingAt F j with
    | some f => if incOf h f = q then niStepOf h f else none
    | none => none

/-- **`firstKey q h F`**: the first key of `q`, the key of the origin its
trace starts at (`none` if the trace does not start at an origin). -/
def firstKey (q : NiInc) (h : List Obs) (F : List NiEntry) : Option Uvis :=
  match utrace q h F with
  | .origin W0 _ :: _ => some W0
  | _ => none

theorem mem_utrace {q : NiInc} {h : List Obs} {F : List NiEntry} {s : NiStep}
    (hs : s ∈ utrace q h F) : ∃ f, f ∈ F ∧ incOf h f = q ∧ niStepOf h f = some s := by
  unfold utrace at hs
  obtain ⟨j, -, hj⟩ := List.mem_filterMap.mp hs
  revert hj
  split
  · rename_i f hf
    split
    · rename_i hq; intro hj; exact ⟨f, niFilingAt_mem hf, hq, hj⟩
    · intro hj; cases hj
  · intro hj; cases hj

/-! ## §3 What a step says -/

/-- An exit's user-visible content: the cause, the trapped epc, `x1..x31`. -/
def exitView : Obs → Option (BitVec 64 × BitVec 64 × List (BitVec 64))
  | .uExit _ _ sc ep gs => some (sc, ep, gs)
  | _ => none

/-- An enter's user-visible content: the pc it lands at, `x1..x31`. -/
def enterView : Obs → Option (BitVec 64 × List (BitVec 64))
  | .uEnter _ _ ep gs => some (retPc ep, gs)
  | _ => none

/-- `a0` of a register list `x1..x31`. -/
def gprsA0 (gs : List (BitVec 64)) : BitVec 64 := gs.getD 9 0#64

/-- `a0` of an enter (its answer, at a returning ecall). -/
def enterA0 : Obs → BitVec 64
  | .uEnter _ _ _ gs => gprsA0 gs
  | _ => 0#64

/-- **The effective syscall number** of an exit's registers `x1..x31`
through a mask: `usysEff` at the frame that names them at words 5..35. -/
def gprsNum (secc : BitVec 64) (gs : List (BitVec 64)) : Int :=
  usysEff secc ([0#64, 0#64, 0#64, 0#64, 0#64] ++ gs)

/-- The step's INPUT: everything its enter is a function of, by the law, but
for the reading: an origin's first key; a round's mask and its exit's
content. -/
def NiStep.input : NiStep → Uvis ⊕ (BitVec 64 × Option (BitVec 64 × BitVec 64 × List (BitVec 64)))
  | .origin W0 _ => .inl W0
  | .round secc x _ => .inr (secc, exitView x)

/-- The step's OUTPUT: its enter's content. -/
def NiStep.output : NiStep → Option (BitVec 64 × List (BitVec 64))
  | .origin _ e => enterView e
  | .round _ _ e => enterView e

/-- A step READS: it is an uptime ecall -- an ecall exit whose effective
number is uptime (getpid's answer is the incarnation's pid, a first-key
datum: no reading). -/
def NiStep.reads : NiStep → Bool
  | .origin .. => false
  | .round secc x _ =>
    match exitView x with
    | some (sc, _, xg) => decide (sc = uecallScause) && decide (gprsNum secc xg = USYS_uptime)
    | none => false

/-- **The step's reading** (O5: the tick is the uptime ANSWER in the trace):
at a resuming class ecall, the enter's `a0`. -/
def NiStep.reading : NiStep → Option (BitVec 64)
  | .origin .. => none
  | s@(.round _ _ e) => if s.reads then some (enterA0 e) else none

/-- The readings of a trace, in order. -/
def traceEvents (tr : List NiStep) : List (BitVec 64) := tr.filterMap NiStep.reading

/-- **`events q h F`**: incarnation `q`'s readings -- its uptime readings. -/
def events (q : NiInc) (h : List Obs) (F : List NiEntry) : List (BitVec 64) :=
  traceEvents (utrace q h F)

/-- A step is an ecall round. -/
def NiStep.ecall : NiStep → Bool
  | .origin .. => false
  | .round _ x _ =>
    match exitView x with
    | some (sc, _, _) => decide (sc = uecallScause)
    | none => false

/-- A round's enter REPLAYS its exit: same registers, resumed at the trapped
pc. -/
def NiStep.replays : NiStep → Prop
  | .origin .. => True
  | .round _ x e => ∃ sc ep xg, exitView x = some (sc, ep, xg) ∧ enterView e = some (retPc ep, xg)

/-! ## §4 THE CLASS LAW -/

/-- **One round's law** (§4 of the W2 design, per round): the exit is an
exit, the enter an enter, and
* a non-ecall cause (interrupt, fault) is TRANSPARENT: the enter replays the
  exit's registers and pc (`uroundIdOk`);
* an ecall is never at exit's effective number (exit does not resume);
* at getpid / uptime the enter is the exit BUMPED at its answer: `a0 :=` the
  answer, every other register kept, pc + 4 -- getpid's answer is the
  incarnation's pid, sign-extended, and uptime's (the reading) a tick
  count's word;
* every other ecall is unconstrained. -/
def niRoundLaw (secc : BitVec 64) (pid : BitVec 32) (x e : Obs) : Prop :=
  ∃ (sc ep : BitVec 64) (xg : List (BitVec 64)) (pc' : BitVec 64) (eg : List (BitVec 64)),
    exitView x = some (sc, ep, xg) ∧ enterView e = some (pc', eg) ∧
    (sc ≠ uecallScause → pc' = retPc ep ∧ eg = xg) ∧
    (sc = uecallScause → gprsNum secc xg ≠ USYS_exit) ∧
    (sc = uecallScause → usysDetResumes (gprsNum secc xg) →
      pc' = retPc (retPc ep + 4#64) ∧ eg = xg.set 9 (gprsA0 eg) ∧
      (gprsNum secc xg = USYS_getpid → gprsA0 eg = BitVec.signExtend 64 pid) ∧
      (gprsNum secc xg = USYS_uptime → usysUptimeRet (gprsA0 eg)))

/-- One step's law, at the incarnation's pid: an origin's enter is its first
key's resume; a round obeys `niRoundLaw`. -/
def NiStep.law (pid : BitVec 32) : NiStep → Prop
  | .origin W0 e => enterView e = some (tfResumePc W0.tf, tfGprs W0.tf)
  | .round secc x e => niRoundLaw secc pid x e

/-- **THE CLASS LAW of incarnation `q`'s trace**: every step obeys its law
at `q`'s pid. -/
def NiClassLaw (q : NiInc) (tr : List NiStep) : Prop := ∀ s ∈ tr, s.law q.2

/-! ### The law from the ledger -/

/-- The trapped frame `roundOkKeys` reads has the trapped key's effective
number, read off the exit's registers. -/
theorem gprsNum_tfGprs (W : Uvis) (pc : BitVec 64) :
    usysEff W.secc (tfOf (tfResumeGpr0 W.tf) pc) = gprsNum W.secc (tfGprs W.tf) := by
  unfold gprsNum
  apply usysEff_argCong
  rw [tfOf_arg _ _ 7 (by decide)]
  simp [tfResumeGpr0, tfResumeGpr, tfW, tfGprs, tfArgIdx, List.getD_eq_getElem?_getD]

theorem gprList_set10 (m : RegMap) (r : BitVec 64) : gprList (m.set 10#5 r) = (gprList m).set 9 r := by
  simp [gprList, gprIdxs, RegMap.set]

theorem gprsA0_gprList (m : RegMap) : gprsA0 (gprList m) = m 10#5 := by
  simp [gprsA0, gprList, gprIdxs]

theorem gprsA0_tfGprs (tf : List (BitVec 64)) : gprsA0 (tfGprs tf) = tfW tf (tfArgIdx 0) := by
  rw [← gprList_tfResumeGpr0, gprsA0_gprList]; rfl

/-- **A valid filing's step obeys the law.** -/
theorem niStepOf_law {h : List Obs} {f : NiEntry} {s : NiStep} (hf : niEntryOk h f)
    (hs : niStepOf h f = some s) : s.law f.pid := by
  match f, hf, hs with
  | .origin j W0 .., hf, hs =>
    obtain ⟨e, he, cpu, sa, ep, rfl, hpc⟩ := hf
    simp only [niStepOf, he, Option.map_some, Option.some.injEq] at hs
    subst hs
    show enterView _ = _
    simp only [enterView, hpc]
  | .round i j sc W W' .., hf, hs =>
    obtain ⟨-, ⟨x, hx, cpu, sa, rfl⟩, ⟨e, he, cpu', sa', ep', rfl, hpc⟩, hr, hpid, hprow⟩ := hf
    simp only [niStepOf, hx, he, Option.some.injEq] at hs
    subst hs
    -- the trapped frame `roundOkKeys` reads
    have hg0 : tfResumeGpr0 (tfOf (tfResumeGpr0 W.tf) (retPc (tfW W.tf tfEpcIdx))) = tfResumeGpr0 W.tf :=
      tfOf_resumeGpr _ _ (tfResumeGpr0_x0 W.tf)
    have hep : tfW (tfOf (tfResumeGpr0 W.tf) (retPc (tfW W.tf tfEpcIdx))) tfEpcIdx = retPc (tfW W.tf tfEpcIdx) :=
      tfOf_epc _ _
    have hnum := gprsNum_tfGprs W (retPc (tfW W.tf tfEpcIdx))
    refine ⟨sc, tfW W.tf tfEpcIdx, tfGprs W.tf, retPc ep', tfGprs W'.tf, rfl, rfl, ?_, ?_, ?_⟩
    · intro hsc
      obtain ⟨⟨hi1, hi2⟩, -⟩ := uroundOk_transparent hsc hr
      refine ⟨?_, ?_⟩
      · rw [hpc, hi2]; unfold tfResumePc; rw [hep, retPc_idem]
      · rw [← gprList_tfResumeGpr0, ← gprList_tfResumeGpr0, hi1, hg0]
    · intro hsc hx
      rw [hsc] at hr
      rw [← hnum] at hx
      exact uroundOk_exit hx hr
    · intro hsc hres
      have hprow' := hprow hsc
      rw [hsc] at hr
      rw [hnum] at hprow'
      rw [← hnum] at hres ⊢
      obtain ⟨h7, -⟩ := usysDetResumes_ne hres
      rcases uroundOk_ecall hr with ⟨hexec, -⟩ | ⟨-, r, ⟨hb1, hb2⟩, hm, -⟩
      · exact absurd hexec h7
      · have heg : tfGprs W'.tf = (tfGprs W.tf).set 9 r := by
          rw [← gprList_tfResumeGpr0, ← gprList_tfResumeGpr0, hb1, hg0, gprList_set10]
        have ha0 : gprsA0 (tfGprs W'.tf) = r := by
          rw [← gprList_tfResumeGpr0, gprsA0_gprList, hb1]; simp
        refine ⟨?_, ?_, ?_, ?_⟩
        · rw [hpc, hb2, hep]
        · rw [ha0, heg]
        · intro hg
          rw [hnum] at hg
          show gprsA0 (tfGprs W'.tf) = BitVec.signExtend 64 W'.pid
          rw [gprsA0_tfGprs, hpid]
          rw [hg] at hprow'
          exact usysRetPid_getpid hprow'
        · intro hu
          rw [ha0]
          rw [hu] at hm
          exact usysMemOk_uptimeRet hm

/-- **`niOk_classLaw`: THE LEDGER'S FILING OBEYS THE CLASS LAW** -- pure, at
every incarnation. -/
theorem niOk_classLaw {h : List Obs} {F : List NiEntry} (hF : niOk h F) :
    ∀ q, NiClassLaw q (utrace q h F) := by
  intro q s hs
  obtain ⟨f, hfF, hq, hfs⟩ := mem_utrace hs
  have := niStepOf_law (hF.1 f hfF) hfs
  rw [← hq]; exact this

/-! ## §5 The pure corollaries -/

/-- Whether a step reads is a function of its input. -/
theorem NiStep.reads_input {s₁ s₂ : NiStep} (hin : s₁.input = s₂.input) : s₁.reads = s₂.reads := by
  cases s₁ <;> cases s₂ <;> simp_all [NiStep.input, NiStep.reads]

theorem NiStep.reading_isSome {s₁ s₂ : NiStep} (hin : s₁.input = s₂.input) :
    s₁.reading.isSome = s₂.reading.isSome := by
  have := NiStep.reads_input hin
  cases s₁ <;> cases s₂ <;> simp_all [NiStep.input, NiStep.reading] <;> split <;> simp_all

theorem enterA0_of_view {e : Obs} {pc : BitVec 64} {eg : List (BitVec 64)}
    (he : enterView e = some (pc, eg)) : enterA0 e = gprsA0 eg := by
  cases e with
  | uEnter _ _ ep gs =>
    simp only [enterView, Option.some.injEq, Prod.mk.injEq] at he
    rw [← he.2]; rfl
  | _ => simp [enterView] at he

/-- **ONE STEP, TWO RUNS**: at equal inputs and equal readings, a lawful step
whose ecall (if any) is in the class has the same output. -/
theorem NiStep.output_eq {pid : BitVec 32} {s₁ s₂ : NiStep} (h₁ : s₁.law pid) (h₂ : s₂.law pid) (hin : s₁.input = s₂.input)
    (hrd : s₁.reading = s₂.reading)
    (hcls : ∀ secc x e, s₁ = .round secc x e → ∀ ep xg,
      exitView x = some (uecallScause, ep, xg) → usysDetClass (gprsNum secc xg)) :
    s₁.output = s₂.output := by
  cases s₁ with
  | origin W0 e =>
    cases s₂ with
    | origin W0' e' =>
      simp only [NiStep.input, Sum.inl.injEq] at hin
      subst hin
      simp only [NiStep.law] at h₁ h₂
      simp only [NiStep.output, h₁, h₂]
    | round => simp [NiStep.input] at hin
  | round secc x e =>
    cases s₂ with
    | origin => simp [NiStep.input] at hin
    | round secc' x' e' =>
      simp only [NiStep.input, Sum.inr.injEq, Prod.mk.injEq] at hin
      obtain ⟨rfl, hxv⟩ := hin
      obtain ⟨sc, ep, xg, pc₁, eg₁, hx₁, he₁, ht₁, hxt₁, hb₁⟩ := h₁
      obtain ⟨sc', ep', xg', pc₂, eg₂, hx₂, he₂, ht₂, -, hb₂⟩ := h₂
      rw [← hxv, hx₁] at hx₂
      simp only [Option.some.injEq, Prod.mk.injEq] at hx₂
      obtain ⟨h1, h2, h3⟩ := hx₂
      subst h1 h2 h3
      simp only [NiStep.output, he₁, he₂]
      by_cases hsc : sc = uecallScause
      · subst hsc
        have hc := hcls secc x e rfl ep xg hx₁
        have hres : usysDetResumes (gprsNum secc xg) := usysDetClass_resumes hc (hxt₁ rfl)
        obtain ⟨hp₁, hg₁, hpid₁, -⟩ := hb₁ rfl hres
        obtain ⟨hp₂, hg₂, hpid₂, -⟩ := hb₂ rfl hres
        have hx₂ : exitView x' = some (uecallScause, ep, xg) := hxv ▸ hx₁
        -- the two answers agree: getpid's is the pid, uptime's the reading
        have ha : gprsA0 eg₁ = gprsA0 eg₂ := by
          rcases hres with hn | hn
          · rw [hpid₁ hn, hpid₂ hn]
          · have hr₁ : NiStep.reads (.round secc x e) = true := by
              simp only [NiStep.reads, hx₁, decide_true, decide_eq_true hn, Bool.and_self]
            have hr₂ : NiStep.reads (.round secc x' e') = true := by
              simp only [NiStep.reads, hx₂, decide_true, decide_eq_true hn, Bool.and_self]
            simp only [NiStep.reading, hr₁, hr₂, if_true, Option.some.injEq] at hrd
            rw [← enterA0_of_view he₁, ← enterA0_of_view he₂, hrd]
        rw [hp₁, hp₂, hg₁, hg₂, ha]
      · obtain ⟨hp₁, hg₁⟩ := ht₁ hsc
        obtain ⟨hp₂, hg₂⟩ := ht₂ hsc
        rw [hp₁, hp₂, hg₁, hg₂]

/-- Every ecall of the trace is in the class (getpid, uptime; exit cannot
resume). -/
def NiInClass (tr : List NiStep) : Prop :=
  ∀ secc x e, NiStep.round secc x e ∈ tr → ∀ ep xg,
    exitView x = some (uecallScause, ep, xg) → usysDetClass (gprsNum secc xg)

/-- **`niTwoRun`, the trace form**: two lawful traces with equal inputs
(first keys, masks, exits) and equal readings, whose ecalls are in the
class, have equal outputs (enters). -/
theorem niTwoRun_trace (q : NiInc) : ∀ (tr₁ tr₂ : List NiStep), NiClassLaw q tr₁ → NiClassLaw q tr₂ →
    NiInClass tr₁ →
    tr₁.map NiStep.input = tr₂.map NiStep.input → traceEvents tr₁ = traceEvents tr₂ →
    tr₁.map NiStep.output = tr₂.map NiStep.output
  | [], [], _, _, _, _, _ => rfl
  | [], _ :: _, _, _, _, hin, _ => by simp at hin
  | _ :: _, [], _, _, _, hin, _ => by simp at hin
  | s₁ :: tr₁, s₂ :: tr₂, h₁, h₂, hc, hin, hev => by
    simp only [List.map_cons, List.cons.injEq] at hin ⊢
    have hsome := NiStep.reading_isSome hin.1
    have hrd : s₁.reading = s₂.reading ∧ traceEvents tr₁ = traceEvents tr₂ := by
      unfold traceEvents at hev
      simp only [List.filterMap_cons] at hev
      cases hr₁ : s₁.reading <;> cases hr₂ : s₂.reading <;> rw [hr₁, hr₂] at hsome hev <;>
        simp_all [traceEvents]
    refine ⟨NiStep.output_eq (h₁ s₁ (List.mem_cons_self ..)) (h₂ s₂ (List.mem_cons_self ..)) hin.1 hrd.1
      (fun secc x e hs => hc secc x e (hs ▸ List.mem_cons_self ..)), ?_⟩
    exact niTwoRun_trace q tr₁ tr₂ (fun s hs => h₁ s (List.mem_cons_of_mem _ hs))
      (fun s hs => h₂ s (List.mem_cons_of_mem _ hs))
      (fun secc x e hs => hc secc x e (List.mem_cons_of_mem _ hs)) hin.2 hrd.2

/-- **`niTwoRun`**: two histories with ledger filings, one incarnation `q`
whose two traces agree on their inputs (the first key and every later
origin's key, every round's mask and exit content) and on their readings
(`events`), with every ecall of `q` in the class: `q`'s enters agree. -/
theorem niTwoRun {h₁ h₂ : List Obs} {F₁ F₂ : List NiEntry} (hF₁ : niOk h₁ F₁) (hF₂ : niOk h₂ F₂)
    (q : NiInc) (hcls : NiInClass (utrace q h₁ F₁))
    (hin : (utrace q h₁ F₁).map NiStep.input = (utrace q h₂ F₂).map NiStep.input)
    (hev : events q h₁ F₁ = events q h₂ F₂) :
    (utrace q h₁ F₁).map NiStep.output = (utrace q h₂ F₂).map NiStep.output :=
  niTwoRun_trace q _ _ (niOk_classLaw hF₁ q) (niOk_classLaw hF₂ q) hcls hin hev

/-- The first keys of two traces with equal inputs agree. -/
theorem firstKey_of_input {q : NiInc} {h₁ h₂ : List Obs} {F₁ F₂ : List NiEntry}
    (hin : (utrace q h₁ F₁).map NiStep.input = (utrace q h₂ F₂).map NiStep.input) :
    firstKey q h₁ F₁ = firstKey q h₂ F₂ := by
  unfold firstKey
  generalize utrace q h₁ F₁ = t₁ at hin
  generalize utrace q h₂ F₂ = t₂ at hin
  match t₁, t₂, hin with
  | [], [], _ => rfl
  | [], _ :: _, hin => simp at hin
  | _ :: _, [], hin => simp at hin
  | s₁ :: _, s₂ :: _, hin =>
    simp only [List.map_cons, List.cons.injEq] at hin
    cases s₁ <;> cases s₂ <;> simp_all [NiStep.input]

/-- A lawful non-ecall step replays. -/
theorem NiStep.replays_of_law {pid : BitVec 32} {s : NiStep} (hl : s.law pid) (hq : s.ecall = false) : s.replays := by
  cases s with
  | origin => trivial
  | round secc x e =>
    obtain ⟨sc, ep, xg, pc', eg, hx, he, ht, -⟩ := hl
    have hsc : sc ≠ uecallScause := by
      intro h; simp [NiStep.ecall, hx, h] at hq
    obtain ⟨hp, hg⟩ := ht hsc
    exact ⟨sc, ep, xg, hx, by rw [he, hp, hg]⟩

/-- **`niStrongInstance`, the trace form**: a lawful trace none of whose
rounds is an ecall replays its exits. -/
theorem niStrongInstance_trace (q : NiInc) (tr : List NiStep) (hl : NiClassLaw q tr)
    (hq : ∀ s ∈ tr, s.ecall = false) : ∀ s ∈ tr, s.replays :=
  fun s hs => NiStep.replays_of_law (hl s hs) (hq s hs)

/-- **`niStrongInstance`** (T's `utRoundQuiet` -- its module `UtRoundQuiet` since deleted as
unreached by the dead-code sweep -- lifted to the trace: there, a quiet run's event counter is constant; here, BEFORE ITS
FIRST ECALL every round of an incarnation is transparent, so its enters
replay its exits).  T's other half -- no ledger event labelled with the
process -- stays in-logic: the ledgers are not in `h`. -/
theorem niStrongInstance {h : List Obs} {F : List NiEntry} (hF : niOk h F) (q : NiInc) :
    ∀ s ∈ (utrace q h F).takeWhile (fun s => !s.ecall), s.replays := by
  intro s hs
  have hmem := List.takeWhile_subset _ hs
  have hq : s.ecall = false := by
    have := List.all_eq_true.mp (List.all_takeWhile (p := fun s => !s.ecall) (l := utrace q h F)) s hs
    simpa using this
  exact NiStep.replays_of_law (niOk_classLaw hF q s hmem) hq

end Xv6
