/-
Weak: **W9a (B) B2-fenced and B2-free — the trap excursion inside a certified sequence** (plan
`notes/weak-allocproc-plan.md` rev 51 §C "W9a (B)" (B2-fenced), (B2-free); spike
`notes/W9aB-spike.md` §§1.1–1.3, 2; rulings [OWN.60], [OWN.68]).  Lean-only, no Rocq twin.

The census is `Weak/PinTrapSites.lean` (B2-census): the static control semantics `tmove` of a
fence-free, `swtch`-free trap path, and what is decided about it.  This file is the GRAPH side.

**B2-fenced (§2).**  A trap path that reaches a COVERING fence (`tcov`: R in the predecessor set,
W in the successor set; the census: `release+0x16` or `virtio_disk_intr+0x2c`, `trapRunFence`)
orders the interrupted certified load `L` before EVERY po-later write of the hart by riscv.cat
ppo rule 4 (`gfenceCovers`): `trapFencedSegPinC` — the fence's row label read off the hart's
conformance (`hartConfFenceLbl`), whatever the trap path did before the fence and wherever the
hart resumes (the interrupted code after `sret`, or — on the one fence-free `swtch` path —
`scheduler`'s resume point, whose every path fences in `release`: `trapSwtchContFence`).  The
exits BEFORE the fence are not pinned by this (spike §1.2): they are W11's re-route / the
lock-layer, cpu-cell and I/O arms (`trapExits` classifies them).

**B2-free (§3–§5).**  On the three FENCE-FREE paths the interrupted walk must CONTINUE after
`sret` at the interrupted state, so the walk's taint must survive the excursion.  Rule 12
(`gppo12`, `[R];(addr|data);[W];rfi;[R]` ⊆ ppo) carries it through `kernelvec`'s and the
callees' register spills and restores:
  * §3 the multi-entry invariant `invOkS P` — every tainted register carries SOME position
    satisfying `P` — with `tEnt GD ad i j` = the load `j` itself or a read `pinStep`-chained
    after it; B1's group test (`grpOkb`) preserves it (`grpSoundS`, any `P`);
  * §3 `reachesT X`: `reachesA` + an EXCURSION constructor (`rtTrap`: items `gx`, after the
    emission prefix `pfx`, certified by `X` for the state's taint; the walk then resumes at the
    SAME walk state — Sail takes the interrupt BEFORE the fetch and `sret` returns to `sepc`);
    `psitesT X ⊇ psitesA` (`psitesTOfPsitesA`); the certifying classes under `psitesT` for any
    `X` sound for `tEnt` (`pinSegPinStoreT`, `pinSegPinCtrlT`);
  * §4 THE CROSSING (`hopEnt`): a register carrying an entry, SPILLED at row position `w` and
    read back at `k` by a load that READS FROM the spill, makes `k` an entry — the tagged data
    edge into the spill (`rowDepsT`), then `gppo12`;
  * §5 THE REAL EXCURSION (`texcFree`, `texcFreeSound`): an excursion whose items are the trap
    entry's (neutral), an alignment `texcM` with a fence-free census run from `kernelvec`'s entry
    to its `sret` (B1's `grpOkb` per instruction + the spill's store item / the restore's load
    item, `memOk`), and the `sret`'s group, IS certified for every walk taint avoiding `stimecmp`
    — by the census's carry table (`PinTrapSites.flowOk`/`flowEnd`: every register comes back
    through its spill/restore pair or untouched, on every fence-free path), the concrete
    invariant `cInv` (`cInvStep`, `cInvRun`), and `hopEnt` at each pair.  Headlines:
    `pinSegPinStoreFree`, `pinSegPinCtrlFree` — PDep/PCtrl certificates with the site oracle
    `psitesT (texcFree …)`, in the published quantifier (`forget GT`, `ad := gtAd`).
  * `hemitPosLt` / `hartConfReadsBefore`: the emission's positions increase (the `j < k` /
    `e < w` side conditions), from `hemit`.

**THE FRAME FACT — where it plugs in.**  `texcFree` instantiates `texcM`'s relation `FR` with
`fun w k => grf G (i, w) (i, k)`: at every restore, the load READS FROM its slot's last spill
(slots keyed by the census's `sp` offsets).  It is consumed in `cInvStep` (the restore case)
through `hopEnt`.  W8 (f3-trapres) — hart custody of the trap reserve's frame bytes during a
fence-free window — with the load-value axiom (no own store to the slot in between: the census
pairs each restore with the LAST spill) supplies it; until then it is a NAMED premise of the
alignment.

**What the alignment `texcM` still assumes (B5's per-state discharge, `psitesA`'s kind).**  (i)
each instruction's group passes `grpOkb` (B1: `dfInstrAll` + `dfScanGrpOkb`); (ii) the run
follows `tmove` — a `ret` lands on the pushed return point (the `ra` VALUE restored from the
frame: the frame fact again), the rx hook word is `consoleintr` (`Xv6.uartRxHook`), no nested
interrupt inside the excursion (SIE stays 0: `pop_off`'s `csrsi` is in the free region but runs
only with `intena`, 0 in a trap); (iii) a spill's group carries its store item, a restore's its
load item before the destination write (Sail's STORE/LOAD clauses); (iv) the trap entry's and
the `sret`'s items are provenance-neutral (B1's `dfNoneNeutral`; `sret` has no destination).

Spec: Sail (`model/Lean_RV64D/LeanRV64D/Step.lean:331-333`; `SysControl.lean:733-788,852`): the
interrupt is taken at the boundary before the fetch, `sepc` ← pc; RVWMO/riscv.cat: rules 4
(`gfenceCovers`) and 12 (`gppo12`) only — NO ppo rule names trap entry, CSRs or `sret`, and
neither is read as a fence anywhere below; Zifencei/PMAs silent.  FAITHFUL throughout.
-/
import Weak.PinTrapSites
import Weak.WeakRvwmoPinBridge3

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open KernelPinsDef
open WeakRvwmoConf (Dstate dstep)
open CatLin
open PinTrapSites

namespace PinTrap

/-! ## 1. The excursion's alignment with the census run -/

/-- THE TRAP-EXCURSION ALIGNMENT: the emission's item groups follow a `tmove` run, instruction by
instruction, each group passing B1's test (`grpOkb`, `PinDataflowGlue.dfScanGrpOkb`). -/
inductive texc : TSt → List Eitem → TSt → Prop where
  | stop (s : TSt) : texc s [] s
  | step (s : TSt) (g1 g2 : List Eitem) (s' : TSt) (mid : List Eitem) (s'' : TSt) :
      grpOkb s.tPc g1 g2 = true → tmove s s' → texc s' mid s'' →
      texc s (g1 ++ (g2 ++ mid)) s''

/-- The alignment's run is a census run. -/
theorem texcRtc (s : TSt) (g : List Eitem) (s'' : TSt) : texc s g s'' → rtc tmove s s'' := by
  intro h
  induction h with
  | stop s => exact rtc_refl s
  | step s g1 g2 s' mid s'' _ hm _ ih => exact rtc_l hm ih

/-! ## 2. B2-fenced: post-fence exits are fence-pinned (rule 4) -/

/-- A fence item of the emission realizes the row's fence label at its position. -/
theorem hemitFenceLbl (dv : Nat → Efab) (k : Nat) (ws : Wstate) (row : List Lbl) (p : Pexv6)
    (es : List Eitem) (pfin : Pexv6) (pr pw sr sw : Bool) (kf : Nat) :
    hemit dv k ws row p es pfin → (Wlabel.LFence pr pw sr sw, some kf) ∈ es →
    k ≤ kf ∧ row[kf - k]? = some (Lbl.LFence pr pw sr sw) := by
  intro h
  induction h with
  | HEnil k ws p => intro hit; exact absurd hit List.not_mem_nil
  | HEone k ws lb row p ls pa da l p' es pfin _ hre _ _ ih =>
    intro hit
    rcases List.mem_append.1 hit with hit | hit
    · simp only [eadm, List.mem_map] at hit
      obtain ⟨_, _, e⟩ := hit
      simp at e
    rcases List.mem_cons.1 hit with e | hit
    · simp only [Prod.mk.injEq, Option.some.injEq] at e
      obtain ⟨rfl, rfl⟩ := e
      obtain ⟨_, _, _, hpr⟩ := hre
      simp only [projLbl, Option.some.injEq] at hpr
      subst hpr
      exact ⟨Nat.le_refl _, by simp⟩
    · obtain ⟨hle, hlk⟩ := ih hit
      refine ⟨by omega, ?_⟩
      rw [show kf - k = (kf - (k + 1)) + 1 by omega, List.getElem?_cons_succ]
      exact hlk
  | HEpair k ws lb row p ls1 pa da l1 pm dm ls2 pm2 dm2 l2 p' es pfin _ hre _ _ _ _ ih =>
    intro hit
    obtain ⟨aq, rl, base, tvs, data, asrc1, asrc2, vsrc2, rfl, rfl, _, _, _⟩ := hre
    rcases List.mem_append.1 hit with hit | hit
    · simp only [eadm, List.mem_map] at hit
      obtain ⟨_, _, e⟩ := hit
      simp at e
    rcases List.mem_cons.1 hit with e | hit
    · simp at e
    rcases List.mem_append.1 hit with hit | hit
    · simp only [eadm, List.mem_map] at hit
      obtain ⟨_, _, e⟩ := hit
      simp at e
    rcases List.mem_cons.1 hit with e | hit
    · simp at e
    · obtain ⟨hle, hlk⟩ := ih hit
      refine ⟨by omega, ?_⟩
      rw [show kf - k = (kf - (k + 1)) + 1 by omega, List.getElem?_cons_succ]
      exact hlk

theorem hartConfFenceLbl (i : Nat) (row : List Lbl) (p0 : Pexv6) (dv : Nat → Efab)
    (em : Hemission) (pr pw sr sw : Bool) (kf : Nat) :
    hartConf i row p0 dv em → (Wlabel.LFence pr pw sr sw, some kf) ∈ em.emItems →
    row[kf]? = some (Lbl.LFence pr pw sr sw) := by
  intro hem hit
  have := (hemitFenceLbl dv 0 wsInit row p0 _ _ pr pw sr sw kf hem hit).2
  rw [Nat.sub_zero] at this
  exact this

/-- **POST-FENCE EXITS ARE FENCE-PINNED (header)**: a covering fence item of the hart's emission
between the certified load `j` and a later write `k` pins the segment — riscv.cat rule 4, no
dataflow and no frame fact.  Whatever the trap path did before the fence, and wherever the hart
resumes. -/
theorem trapFencedSegPinC (GD : Gdexec) (ad : List (Geid × Geid)) (i : Nat) (row : List Lbl)
    (p0 : Pexv6) (dv : Nat → Efab) (em : Hemission) (sg : Seg) (j kf k : Nat)
    (pr pw sr sw : Bool) :
    GD.gdG.gxProg[i]? = some row → hartConf i row p0 dv em →
    (Wlabel.LFence pr pw sr sw, some kf) ∈ em.emItems → pr = true → sw = true →
    sg.sgEntry = (i, j) → sg.sgExit = (i, k) → j < kf → kf < k →
    glblIs GD.gdG (i, j) lbIsR → glblIs GD.gdG (i, k) lbIsW →
    segPinC GD ad sg := by
  intro hrow hcf hit hpr hsw he hx hj hk hr hw
  have hf : gxLbl GD.gdG (i, kf) = some (Lbl.LFence pr pw sr sw) := by
    show (GD.gdG.gxProg[i]?).bind (fun p => p[kf]?) = _
    rw [hrow]
    exact hartConfFenceLbl i row p0 dv em pr pw sr sw kf hcf hit
  exact pinSegPinFenceC GD ad i sg j kf k pr pw sr sw he hx hj hk hf hr hpr hw hsw

/-- The fence item a covering fence word emits (`ebarLabel`), as the excursion's group carries
it: a per-instruction emission fact of `psitesA`'s kind (Sail's FENCE clause → `sail_barrier`
→ the `LFence` label with the word's predecessor/successor bits), NAMED. -/
def fenceGrp (pc : Int) (g : List Eitem) (kf : Nat) : Prop :=
  (Wlabel.LFence (wFencePr (kw pc)) (wFencePw (kw pc)) (wFenceSr (kw pc)) (wFenceSw (kw pc)),
    some kf) ∈ g

theorem tcovBits (w : Nat) : tcov w = true → wFencePr w = true ∧ wFenceSw w = true := by
  intro h
  unfold tcov at h
  rw [Bool.and_eq_true, Bool.and_eq_true] at h
  exact ⟨h.1.2, h.2⟩

/-- **A FENCED EXCURSION PINS EVERY LATER WRITE (header)**: an excursion aligned with a census
run from `kernelvec`'s entry that reaches a covering fence — `release+0x16` or
`virtio_disk_intr+0x2c` (`trapRunFence`) — whose group carries its fence item at `kf` pins the
certified load `j` before every write `k > kf` of the hart. -/
theorem trapFencedExcursion (GD : Gdexec) (ad : List (Geid × Geid)) (i : Nat) (row : List Lbl)
    (p0 : Pexv6) (dv : Nat → Efab) (em : Hemission) (sg : Seg) (gx gf pre post : List Eitem)
    (s : TSt) (j kf k : Nat) :
    texc tStart gx s → tcov (kw s.tPc) = true → fenceGrp s.tPc gf kf →
    em.emItems = pre ++ gf ++ post →
    GD.gdG.gxProg[i]? = some row → hartConf i row p0 dv em →
    sg.sgEntry = (i, j) → sg.sgExit = (i, k) → j < kf → kf < k →
    glblIs GD.gdG (i, j) lbIsR → glblIs GD.gdG (i, k) lbIsW →
    (s.tPc = relFencePc ∨ s.tPc = virtioFencePc) ∧ segPinC GD ad sg := by
  intro hx hc hg hes hrow hcf he hxk hj hk hr hw
  refine ⟨trapRunFence s (texcRtc _ _ _ hx) hc, ?_⟩
  obtain ⟨hpr, hsw⟩ := tcovBits _ hc
  have hit : (Wlabel.LFence (wFencePr (kw s.tPc)) (wFencePw (kw s.tPc)) (wFenceSr (kw s.tPc))
      (wFenceSw (kw s.tPc)), some kf) ∈ em.emItems := by
    rw [hes]; exact List.mem_append_left _ (List.mem_append_right _ hg)
  exact trapFencedSegPinC GD ad i row p0 dv em sg j kf k _ _ _ _ hrow hcf hit hpr hsw he hxk hj
    hk hr hw

/-! ### 2.1 The `swtch` path: the hart side fences too -/

/-- The functions the hart can enter from `scheduler`'s resume point before its first covering
fence (the `swtch` continuation's call closure). -/
def contFuns : List Int :=
  [resumePc, (KernelSyms.«release» : Int), (KernelSyms.«holding» : Int),
    (KernelSyms.«pop_off» : Int), (KernelSyms.«mycpu» : Int), (KernelSyms.«unreachable» : Int),
    swtchPc]

/-- Decided: the closure is closed under the call sites of its `reach` sets, and none of them
holds `kernelvec`'s `sret` or a `swtch` call. -/
def contOkb : Bool :=
  contFuns.all (fun f => (tlook trapTab f).isSome &&
    (reachOf trapTab f).all (fun pc =>
      (tcallees pc).all (fun g => intMem g contFuns) && !(pc == kvSretPc) &&
      !(tstep trapTab pc).isSwtch))

theorem contOk : contOkb = true := by decide +kernel

/-- `swtch`'s `ret`, as the HART follows it, lands on `scheduler`'s resume point: the root of the
continuation is `swtch`'s entry with the frame (`scheduler`'s resume, `scheduler`'s resume).
(That `cpus[h].context.ra` holds `resumePc` is the run fact named in `PinTrapSites`.) -/
def contStart : TSt := ⟨swtchPc, swtchPc, [(resumePc, resumePc)]⟩

abbrev tcont (s : TSt) : Prop :=
  intMem s.tFn contFuns = true ∧ ∀ ga, ga ∈ s.tFr → intMem ga.1 contFuns = true

theorem tinvCont : tinv trapTab contStart := by
  refine ⟨by decide +kernel, fun _ => by decide +kernel, trivial⟩

theorem contStep (x y : TSt) : tmove x y → tinv trapTab x → tcont x → tcont y := by
  intro hm hi hc
  have hcl : ∀ pc, intMem pc (reachOf trapTab x.tFn) = true → ∀ g, g ∈ tcallees pc →
      intMem g contFuns = true := by
    intro pc hp g hg
    have h := contOk
    unfold contOkb at h
    rw [List.all_eq_true] at h
    have h1 := h x.tFn ((intMemIff _ _).1 hc.1)
    rw [Bool.and_eq_true, List.all_eq_true] at h1
    have h2 := h1.2 pc ((intMemIff _ _).1 hp)
    rw [Bool.and_eq_true, Bool.and_eq_true, List.all_eq_true] at h2
    exact h2.1.1 g hg
  cases hm with
  | seq f pc fr _ _ => exact hc
  | brN f pc tgt fr _ _ => exact hc
  | brT f pc tgt fr _ _ => exact hc
  | jmp f pc tgt fr _ _ => exact hc
  | call f pc tgt fr hl hk hs =>
    refine ⟨hcl pc hi.1 tgt (by rw [tcalleesCall pc tgt hk hs]; exact List.mem_singleton_self _),
      fun ga hga => ?_⟩
    rcases List.mem_cons.mp hga with e | hga
    · subst e; exact hc.1
    · exact hc.2 ga hga
  | hook f fr hl hk =>
    refine ⟨hcl hookPc hi.1 hookTgt (by rw [tcalleesHook hk]; exact List.mem_singleton_self _),
      fun ga hga => ?_⟩
    rcases List.mem_cons.mp hga with e | hga
    · subst e; exact hc.1
    · exact hc.2 ga hga
  | ret f pc g a fr _ _ =>
    exact ⟨hc.2 (g, a) (List.mem_cons_self ..), fun ga hga => hc.2 ga (List.mem_cons_of_mem _ hga)⟩

/-- **THE `swtch` CONTINUATION FENCES (header)**: on the hart side of the one fence-free `swtch`
call (`sched+0x6e`), a fence-free run from `swtch`'s entry (returning to `scheduler`'s resume
point) never reaches `kernelvec`'s `sret` nor another `swtch` call, and every store it executes is
a `trapExits` row (`swtchCtx`, the two `cpus[h]` cells, then `release`'s `lk->cpu` …): the hart
cannot leave `scheduler` without passing a covering fence. -/
theorem trapSwtchContFence (s : TSt) : rtc tmove contStart s →
    s.tPc ≠ kvSretPc ∧ (tstep trapTab s.tPc).isSwtch = false ∧
    (isStoreb s.tPc = true → intMem s.tPc (trapExits.map Prod.fst) = true) := by
  intro h
  have key := rtc_ind_r (R := tmove) (fun z => tinv trapTab z ∧ tcont z) contStart
    ⟨tinvCont, by decide +kernel, fun ga hga => by
      simp only [contStart, List.mem_singleton] at hga; subst hga; decide +kernel⟩
    (fun y z _ hyz hy => ⟨tinvStep trapTab trapTabOk y z hyz hy.1,
      contStep y z hyz hy.1 hy.2⟩) s h
  obtain ⟨⟨hr, -⟩, hc, -⟩ := key
  have h := contOk
  unfold contOkb at h
  rw [List.all_eq_true] at h
  have h1 := h s.tFn ((intMemIff _ _).1 hc)
  rw [Bool.and_eq_true, List.all_eq_true] at h1
  have h2 := h1.2 s.tPc ((intMemIff _ _).1 hr)
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.not_eq_true', Bool.not_eq_true'] at h2
  refine ⟨fun e => by rw [e, beq_self_eq_true] at h2; exact Bool.noConfusion h2.1.2, h2.2, ?_⟩
  intro hst
  have hp := allReachMem s.tFn s.tPc hr
  have h3 := trapExitsOk
  unfold exitsOkb at h3
  rw [Bool.and_eq_true, Bool.and_eq_true, List.all_eq_true] at h3
  have h4 := h3.1.2 s.tPc ((intMemIff _ _).1 hp)
  rw [hst, Bool.not_true, Bool.false_or] at h4
  exact h4

/-! ## 3. B2-free: the multi-entry invariant and the excursion alignment -/

/-- THE MULTI-ENTRY INVARIANT (header): every register the checker calls tainted carries SOME
row position satisfying `P` in the emission's provenance. -/
def invOkS (P : Nat → Prop) (s : Dstate) (t : List Nat) : Prop :=
  ∀ r : Nat, taintMem r t = true → ∃ e, e ∈ dprov s r ∧ P e

theorem invOkSOfInvOk (j : Nat) (s : Dstate) (t : List Nat) (P : Nat → Prop) (hj : P j) :
    invOk j s t → invOkS P s t :=
  fun h r hr => ⟨j, h r hr, hj⟩

theorem invNeutralS (P : Nat → Prop) (s : Dstate) (t : List Nat) (it : Eitem) :
    provNeutralb it = true → invOkS P s t → invOkS P (dstep s it).1 t := by
  intro hn h r hr
  obtain ⟨e, he, hp⟩ := h r hr
  exact ⟨e, by rw [dprovNeutralItem s it r hn]; exact he, hp⟩

theorem invNeutralRunS (P : Nat → Prop) (s : Dstate) (t : List Nat) (g : List Eitem) :
    g.all provNeutralb = true → invOkS P s t → invOkS P (dsRun s g) t := by
  induction g generalizing s with
  | nil => intro _ h; exact h
  | cons it g ih =>
    intro hg hinv
    rw [List.all_cons, Bool.and_eq_true] at hg
    rw [dsRunCons]
    exact ih _ hg.2 (invNeutralS _ _ _ _ hg.1 hinv)

theorem regwStepS (P : Nat → Prop) (s : Dstate) (t : List Nat) (rd : Nat) (dec srcs : List Dsrc)
    (k : Option Nat) :
    invOkS P s t → dsubb dec srcs = true →
    invOkS P (dstep s (Wlabel.LRegW rd srcs, k)).1 (taintUpd1 t (some (rd, dec))) := by
  intro hinv hsub r hr
  rcases taintUpd1Inv _ _ _ _ hr with ⟨rfl, hs⟩ | ⟨hne, hr⟩
  · obtain ⟨r', hr', ht'⟩ := srcsTaintedReg _ _ hs
    obtain ⟨e, he, hp⟩ := hinv r' ht'
    refine ⟨e, ?_, hp⟩
    rw [dprovRegwEq]
    exact dsrcsPosReg _ _ _ _ (dsubbElem _ _ _ hsub hr') he
  · obtain ⟨e, he, hp⟩ := hinv r hr
    exact ⟨e, by rw [dprovRegwNe _ _ _ _ _ hne]; exact he, hp⟩

theorem regwSegSoundS (P : Nat → Prop) (rd : Nat) (dec : List Dsrc) (g : List Eitem)
    (s : Dstate) (t : List Nat) :
    regwSeg rd dec g = true → invOkS P s t →
    invOkS P (dsRun s g) (taintUpd1 t (some (rd, dec))) := by
  induction g generalizing s with
  | nil => intro h; exact absurd h Bool.false_ne_true
  | cons it g ih =>
    intro hg hinv
    rw [dsRunCons]
    obtain ⟨l, k⟩ := it
    cases l
    case LRegW rd' srcs =>
      simp only [regwSeg, Bool.and_eq_true] at hg
      obtain ⟨⟨hrd, hsub⟩, hn⟩ := hg
      have e : rd' = rd := Nat.eq_of_beq_eq_true hrd
      subst e
      exact invNeutralRunS _ _ _ _ hn (regwStepS _ _ _ _ _ _ _ hinv hsub)
    all_goals
      simp only [regwSeg] at hg
      exact ih _ hg (invNeutralS _ _ _ _ rfl hinv)

theorem realizesbSoundS (P : Nat → Prop) (d : Option (Nat × List Dsrc)) (g : List Eitem)
    (s : Dstate) (t : List Nat) :
    realizesb d g = true → invOkS P s t → invOkS P (dsRun s g) (taintUpd1 t d) := by
  cases d with
  | none => exact invNeutralRunS P s t g
  | some p =>
    obtain ⟨rd, dec⟩ := p
    exact regwSegSoundS P rd dec g s t

/-- B1's group test preserves the multi-entry invariant, for ANY entry predicate. -/
theorem grpSoundS (P : Nat → Prop) (pc : Int) (g1 g2 : List Eitem) (s : Dstate) (t : List Nat) :
    grpOkb pc g1 g2 = true → invOkS P s t → invOkS P (dsRun s (g1 ++ g2)) (taintStep t pc) := by
  intro h hinv
  unfold grpOkb at h
  rw [Bool.and_eq_true] at h
  rw [dsRunApp, taintStepUnfold]
  exact realizesbSoundS _ _ _ _ _ h.2 (realizesbSoundS _ _ _ _ _ h.1 hinv)

/-- THE ALIGNMENT WITH TRAP EXCURSIONS (header): `reachesA`'s steps, plus an EXCURSION at any
walk state — items `gx` that `X` certifies, given the emission prefix `pfx` before them and the
state's taint — after which the walk resumes at the SAME walk state (the interrupted
instruction executes after `sret`).  The first index is the emission prefix before the items. -/
inductive reachesT (X : List Eitem → List Nat → List Eitem → Prop) (own : Bool) :
    List Eitem → PState → List Eitem → PState → Prop where
  | rtStop (pfx : List Eitem) (s : PState) : reachesT X own pfx s [] s
  | rtStep (pfx : List Eitem) (s : PState) (g1 g2 : List Eitem) (l : List PState) (s' : PState)
      (mid : List Eitem) (s'' : PState) :
      grpOkb s.psPc g1 g2 = true →
      pstep own s = some l → s' ∈ l →
      taintSub s'.psT (taintStep s.psT s.psPc) →
      reachesT X own (pfx ++ (g1 ++ g2)) s' mid s'' →
      reachesT X own pfx s (g1 ++ (g2 ++ mid)) s''
  | rtTrap (pfx : List Eitem) (s : PState) (gx mid : List Eitem) (s'' : PState) :
      X pfx s.psT gx → reachesT X own (pfx ++ gx) s mid s'' → reachesT X own pfx s (gx ++ mid) s''

theorem reachesTOfReachesA (X : List Eitem → List Nat → List Eitem → Prop) (own : Bool)
    (pfx : List Eitem) (s : PState) (g : List Eitem) (s'' : PState) :
    reachesA own s g s'' → reachesT X own pfx s g s'' := by
  intro h
  induction h generalizing pfx with
  | raStop s => exact .rtStop pfx s
  | raStep s g1 g2 l s' mid s'' hg hp hm hsub _ ih =>
    exact .rtStep pfx s g1 g2 l s' mid s'' hg hp hm hsub (ih _)

/-- `X` is SOUND for the entry predicate `P`: an excursion it certifies keeps every tainted
register carrying a `P` position. -/
def xSound (X : List Eitem → List Nat → List Eitem → Prop) (P : Nat → Prop) : Prop :=
  ∀ pfx t gx, X pfx t gx → invOkS P (dsRun dsInit pfx) t → invOkS P (dsRun dsInit (pfx ++ gx)) t

/-- THE INVARIANT TRAVELS, excursions included. -/
theorem reachesTInv (X : List Eitem → List Nat → List Eitem → Prop) (P : Nat → Prop)
    (hX : xSound X P) (own : Bool) (pfx : List Eitem) (s : PState) (g : List Eitem)
    (s'' : PState) :
    reachesT X own pfx s g s'' → invOkS P (dsRun dsInit pfx) s.psT →
    invOkS P (dsRun dsInit (pfx ++ g)) s''.psT := by
  intro hr
  induction hr with
  | rtStop pfx s => intro h; rw [List.append_nil]; exact h
  | rtStep pfx s g1 g2 l s' mid s'' hg _ _ hsub _ ih =>
    intro hinv
    have h1 : invOkS P (dsRun dsInit (pfx ++ (g1 ++ g2))) s'.psT := by
      rw [dsRunApp]
      intro r hr'
      exact grpSoundS _ _ _ _ _ _ hg hinv r (hsub r hr')
    have := ih h1
    rw [show pfx ++ (g1 ++ g2) ++ mid = pfx ++ (g1 ++ (g2 ++ mid)) by
      simp only [List.append_assoc]] at this
    exact this
  | rtTrap pfx s gx mid s'' hx _ ih =>
    intro hinv
    have := ih (hX _ _ _ hx hinv)
    rw [List.append_assoc] at this
    exact this

/-- THE SITE ORACLE WITH TRAP EXCURSIONS. -/
def psitesT (X : List Eitem → List Nat → List Eitem → Prop) (pcL : Int) (own : Bool)
    (base pre : List Eitem) (s : PState) : Prop :=
  ∃ mid, pre = base ++ mid ∧ reachesT X own base (pinStart pcL) mid s

/-- **`psitesT ⊇ psitesA` (header)**: every run `psitesA` admits, `psitesT` admits. -/
theorem psitesTOfPsitesA (X : List Eitem → List Nat → List Eitem → Prop) (pcL : Int) (own : Bool)
    (base pre : List Eitem) (s : PState) :
    psitesA pcL own base pre s → psitesT X pcL own base pre s := by
  rintro ⟨mid, hpre, hr⟩
  exact ⟨mid, hpre, reachesTOfReachesA X own base _ _ _ hr⟩

/-! ### 3.1 The entries and the certifying classes under `psitesT` -/

/-- THE ENTRIES of the load at row position `j` of hart `i`: `j` itself, or a read the load is
ordered before by a chain of `pinStep`s (rule 12 through a spill/restore pair). -/
def tEnt (GD : Gdexec) (ad : List (Geid × Geid)) (i j : Nat) (e : Nat) : Prop :=
  e = j ∨ tc (pinStep GD ad) (i, j) (i, e)

/-- An entry pinned to a write is a pinned segment. -/
theorem tEntSegPinC (GD : Gdexec) (ad : List (Geid × Geid)) (i j e k : Nat) (sg : Seg) :
    sg.sgEntry = (i, j) → sg.sgExit = (i, k) → tEnt GD ad i j e →
    pinStep GD ad (i, e) (i, k) → segPinC GD ad sg := by
  intro he hx hent hst
  unfold segPinC
  rw [he, hx]
  rcases hent with rfl | h
  · exact tc_once hst
  · exact tc_r h hst

theorem dsRunWithin (P : Nat → Prop) (s : Dstate) (es : List Eitem) :
    dsWithin P s → ereadOk P es → dsWithin P (dsRun s es) := by
  induction es generalizing s with
  | nil => intro h _; exact h
  | cons it es ih =>
    intro hs hok
    rw [dsRunCons]
    exact ih _ (dstepWithin P s it hs (fun k hk hr => hok it k (List.mem_cons_self ..) hk hr)).1
      (fun it0 k hin => hok it0 k (List.mem_cons_of_mem _ hin))

theorem psitesTInv (X : List Eitem → List Nat → List Eitem → Prop) (GD : Gdexec)
    (ad : List (Geid × Geid)) (i j : Nat) (hX : xSound X (tEnt GD ad i j)) (pcL : Int)
    (own : Bool) (base pre g0 : List Eitem) (s : PState) :
    invOk j (dsRun dsInit base) (pinT0 pcL) →
    psitesT X pcL own base pre s →
    g0.all provNeutralb = true →
    invOkS (tEnt GD ad i j) (dsRun dsInit (pre ++ g0)) s.psT := by
  intro hbase hsite hg0
  obtain ⟨mid, rfl, hr⟩ := hsite
  rw [dsRunApp]
  apply invNeutralRunS _ _ _ _ hg0
  exact reachesTInv X _ hX own base _ _ _ hr (invOkSOfInvOk j _ _ _ (Or.inl rfl) hbase)

/-- **PDep under `psitesT` (header)**: at any reached store with a tainted address or data
source, the segment from the load to the store is `segPinC` — through every trap excursion `X`
certifies.  `ereadOk (· < k) (pre ++ g0)`: the emission's reads before the store sit at smaller
row positions (a fact of the hart's conformance). -/
theorem pinSegPinStoreT (X : List Eitem → List Nat → List Eitem → Prop) (GD : Gdexec)
    (ad : List (Geid × Geid)) (i : Nat) (em : Hemission) (sg : Seg) (pcL : Int) (j k : Nat)
    (own : Bool) (base pre g0 post : List Eitem) (s : PState) (rl : Bool) (a : Int)
    (v : List (BitVec 8)) (asrc vsrc : List Dsrc) :
    xSound X (tEnt GD ad i j) →
    (∀ jk, jk ∈ rowDeps em.emItems → ((i, jk.1), (i, jk.2)) ∈ GD.gdDeps) →
    sg.sgEntry = (i, j) → sg.sgExit = (i, k) →
    invOk j (dsRun dsInit base) (pinT0 pcL) →
    em.emItems = pre ++ g0 ++ (Wlabel.LStore rl a v asrc vsrc, some k) :: post →
    psitesT X pcL own base pre s →
    g0.all provNeutralb = true →
    ereadOk (fun e => e < k) (pre ++ g0) →
    dsubb (depsAddr (krole s.psPc)) asrc = true → dsubb (depsVsrc (krole s.psPc)) vsrc = true →
    (srcsTainted s.psT (depsAddr (krole s.psPc))
      || srcsTainted s.psT (depsVsrc (krole s.psPc))) = true →
    segPinC GD ad sg := by
  intro hX hconf he hx hbase hes hsite hg0 hlt hca hcv htn
  have hinv := psitesTInv X GD ad i j hX pcL own base pre g0 s hbase hsite hg0
  have hwin := dsRunWithin (fun e => e < k) dsInit (pre ++ g0) (dsWithinInit _) hlt
  have hedge : ∀ r, (Dsrc.DReg r ∈ asrc ∨ Dsrc.DReg r ∈ vsrc) → taintMem r s.psT = true →
      segPinC GD ad sg := by
    intro r hr ht
    obtain ⟨e, he', hent⟩ := hinv r ht
    have hek : e < k := hwin.1 r e he'
    have hjk : (e, k) ∈ rowDeps em.emItems :=
      rowDepsItem _ (pre ++ g0) _ post _ hes (dedgesReg _ _ _ _ _ _ hek hr he')
    exact tEntSegPinC GD ad i j e k sg he hx hent (Or.inr (Or.inl (hconf _ hjk)))
  rw [Bool.or_eq_true] at htn
  rcases htn with h | h
  · obtain ⟨r, hr, ht⟩ := srcsTaintedReg _ _ h
    exact hedge r (Or.inl (dsubbElem _ _ _ hca hr)) ht
  · obtain ⟨r, hr, ht⟩ := srcsTaintedReg _ _ h
    exact hedge r (Or.inr (dsubbElem _ _ _ hcv hr)) ht

/-- **PCtrl under `psitesT` (header)**: at any reached branch testing a tainted register, every
later store is pinned to the load — through every trap excursion `X` certifies. -/
theorem pinSegPinCtrlT (X : List Eitem → List Nat → List Eitem → Prop) (GD : Gdexec)
    (ad : List (Geid × Geid)) (i : Nat) (em : Hemission) (sg : Seg) (pcL : Int) (j k : Nat)
    (own : Bool) (base pre g0 mid post : List Eitem) (s : PState) (srcs : List Dsrc)
    (kc : Option Nat) (rl : Bool) (a : Int) (v : List (BitVec 8)) (asrc vsrc : List Dsrc) :
    xSound X (tEnt GD ad i j) →
    (∀ jk, jk ∈ rowDeps em.emItems → ((i, jk.1), (i, jk.2)) ∈ GD.gdDeps) →
    sg.sgEntry = (i, j) → sg.sgExit = (i, k) →
    invOk j (dsRun dsInit base) (pinT0 pcL) →
    em.emItems = pre ++ g0 ++ (Wlabel.LCtrl srcs, kc)
      :: (mid ++ (Wlabel.LStore rl a v asrc vsrc, some k) :: post) →
    psitesT X pcL own base pre s →
    g0.all provNeutralb = true →
    ereadOk (fun e => e < k) (pre ++ g0) →
    dsubb (depsCtrl (krole s.psPc)) srcs = true →
    srcsTainted s.psT (depsCtrl (krole s.psPc)) = true →
    segPinC GD ad sg := by
  intro hX hconf he hx hbase hes hsite hg0 hlt hcov htn
  have hinv := psitesTInv X GD ad i j hX pcL own base pre g0 s hbase hsite hg0
  have hwin := dsRunWithin (fun e => e < k) dsInit (pre ++ g0) (dsWithinInit _) hlt
  obtain ⟨r, hr, ht⟩ := srcsTaintedReg _ _ htn
  obtain ⟨e, he', hent⟩ := hinv r ht
  have hek : e < k := hwin.1 r e he'
  have hctl : e ∈ (dsRun dsInit (pre ++ g0 ++ [(Wlabel.LCtrl srcs, kc)])).dsCtl := by
    rw [dsRunApp, dsRunCons, dsRunNil]
    exact dstepCtlIntro _ _ _ _ _ (dsubbElem _ _ _ hcov hr) he'
  have hctl' : e ∈ (dsRun dsInit (pre ++ g0 ++ (Wlabel.LCtrl srcs, kc) :: mid)).dsCtl := by
    rw [show pre ++ g0 ++ (Wlabel.LCtrl srcs, kc) :: mid
        = (pre ++ g0 ++ [(Wlabel.LCtrl srcs, kc)]) ++ mid by
      simp only [List.append_assoc, List.cons_append, List.nil_append], dsRunApp]
    exact dsRunCtlSub _ _ hctl
  have hjk : (e, k) ∈ rowDeps em.emItems := by
    apply rowDepsItem _ (pre ++ g0 ++ (Wlabel.LCtrl srcs, kc) :: mid)
      (Wlabel.LStore rl a v asrc vsrc, some k) post
    · rw [hes]; simp only [List.append_assoc, List.cons_append]
    · exact dedgesCtl _ _ _ _ _ hek hctl'
  exact tEntSegPinC GD ad i j e k sg he hx hent (Or.inr (Or.inl (hconf _ hjk)))

/-! ## 4. THE CROSSING: rule 12 through one spill/restore pair -/

/-- The tagged state of a prefix covers the untagged one (`dsLeRun`). -/
theorem provTagged (pre : List Eitem) (r e : Nat) :
    e ∈ dprov (dsRun dsInit pre) r →
    e ∈ dsrcPos (dsOfT (WeakRvwmoPinBridge3.dtRun dtInit pre)) (.DReg r) :=
  fun h => (WeakRvwmoPinBridge3.dsLeRun pre dsInit dtInit dsLeInit).1 r e h

/-- **THE RULE-12 HOP (header)**: the register `r`, carrying the entry `e` (a RAM read of hart
`i`), is SPILLED by the store item at row position `w` (its data sources name `r`); the read at
`k` READS FROM the spill — THE FRAME FACT `hrf`, named: W8 (f3-trapres)'s hart custody of the
trap reserve plus the load-value axiom supply it.  Then `k` is an entry too: the tagged data
edge `e → w` is a `gtAd` edge, and `gppo12` orders `e` before `k`. -/
theorem hopEnt (GT : GdexecT) (i j : Nat) (em : Hemission) (pre post : List Eitem) (rl : Bool)
    (a : Int) (v : List (BitVec 8)) (asrc vsrc : List Dsrc) (w k r e : Nat) :
    (∀ x, x ∈ rowDepsT em.emItems → (((i, x.1.1), (i, x.1.2)), x.2) ∈ GT.gtDeps) →
    em.emItems = pre ++ (Wlabel.LStore rl a v asrc vsrc, some w) :: post →
    Dsrc.DReg r ∈ vsrc → e ∈ dprov (dsRun dsInit pre) r → e < w →
    gisRd GT.gtG (i, e) = true → gisW GT.gtG (i, w) = true →
    WeakRvwmoAcyc.grf GT.gtG (i, w) (i, k) →
    tEnt (forget GT) (gtAd GT.gtG GT.gtDeps) i j e →
    tEnt (forget GT) (gtAd GT.gtG GT.gtDeps) i j k := by
  intro hconfT hes hr he hlt hrd hwr hrf hent
  let s := WeakRvwmoPinBridge3.dtRun dtInit pre
  have hT : ((e, w), Dtag.DTdata) ∈ rowDepsT em.emItems := by
    have hsplit : rowDepsT em.emItems = rowDepsTAux dtInit pre ++
        ((dedgesW s w asrc vsrc) ++
          rowDepsTAux (dstepT s (Wlabel.LStore rl a v asrc vsrc, some w)).1 post) := by
      rw [hes]
      unfold rowDepsT
      rw [WeakRvwmoPinBridge3.rowDepsTAuxApp]
      rfl
    rw [hsplit]
    refine List.mem_append_right _ (List.mem_append_left _ ?_)
    refine List.mem_append_right _ (List.mem_append_left _ ((elemOfTagEdges ..).2
      ⟨rfl, rfl, ?_, hlt⟩))
    unfold dtsrcs dsrcsPos
    exact List.mem_flatten.mpr ⟨_, List.mem_map_of_mem hr, provTagged pre r e he⟩
  have had : ((i, e), (i, w)) ∈ gtAd GT.gtG GT.gtDeps :=
    (elemOfGtAd GT.gtG GT.gtDeps (i, e) (i, w)).2 ⟨Dtag.DTdata, hconfT _ hT, rfl, hrd, hwr⟩
  have h12 : pinStep (forget GT) (gtAd GT.gtG GT.gtDeps) (i, e) (i, k) :=
    Or.inr (Or.inr ⟨rfl, (i, w), had, hrf⟩)
  refine Or.inr ?_
  rcases hent with rfl | h
  · exact tc_once h12
  · exact tc_r h h12

/-- The canonical excursion certificate: the excursion keeps every tainted register carrying an
entry.  Sound by construction (`texcOkSound`); a REAL fence-free excursion satisfies it
(`texcFreeOk`, §5). -/
def texcOk (GD : Gdexec) (ad : List (Geid × Geid)) (i j : Nat) (pfx : List Eitem)
    (t : List Nat) (gx : List Eitem) : Prop :=
  invOkS (tEnt GD ad i j) (dsRun dsInit pfx) t → invOkS (tEnt GD ad i j) (dsRun dsInit (pfx ++ gx)) t

theorem texcOkSound (GD : Gdexec) (ad : List (Geid × Geid)) (i j : Nat) :
    xSound (texcOk GD ad i j) (tEnt GD ad i j) :=
  fun _ _ _ hx h => hx h

/-! ## 5. B2-free: a REAL fence-free excursion is certified

The census's carry table (`PinTrapSites` §5: `trapFlow`, `flowOk`, `flowEnd`) is read against the
excursion's items.  `texcM` is the excursion's alignment with a census run, WITH its memory items
(`memOk`): each instruction's group passes B1's test (`grpOkb`); a spill (`spSt`) carries its
store item, a restore (`spLd`) its load item before the destination write; the slot map `S`
records each slot's LAST spill (its row position); and at a restore the FRAME relation `FR`
holds between the slot's last spill and the load — instantiated (`texcFree`) with "the restore
READS FROM that spill" (`grf`): THE FRAME FACT, a named premise (W8 (f3-trapres)). -/

def notInstrb (it : Eitem) : Bool :=
  match it.1 with
  | .LInstr => false
  | _ => true

/-- The slot map after a spill of slot `o` at row position `w`. -/
def slotSet (S : Int → Option Nat) (o : Int) (w : Nat) : Int → Option Nat :=
  fun o' => if o' = o then some w else S o'

/-- THE MEMORY ITEMS OF ONE EXCURSION INSTRUCTION (header). -/
def memOk (FR : Nat → Nat → Prop) (pc sp : Int) (S : Int → Option Nat) (g1 g2 : List Eitem)
    (S' : Int → Option Nat) : Prop :=
  match spSt pc with
  | some o =>
      ∃ (ga gb : List Eitem) (rl : Bool) (a : Int) (v : List (BitVec 8)) (asrc vsrc : List Dsrc)
        (w : Nat), g1 ++ g2 = ga ++ (Wlabel.LStore rl a v asrc vsrc, some w) :: gb ∧
        dsubb (depsVsrc (krole pc)) vsrc = true ∧ S' = slotSet S (sp + o) w
  | none =>
      match spLd pc with
      | some o =>
          (∃ (ga gb : List Eitem) (aq lat : Bool) (base : Int) (tvs : List (Nat × BitVec 8))
            (asrc : List Dsrc) (k : Nat),
            g1 = ga ++ (Wlabel.LLoad aq lat base tvs asrc, some k) :: gb ∧
            ga.all provNeutralb = true ∧ gb.all notInstrb = true ∧
            ∀ w, S (sp + o) = some w → FR w k) ∧ S' = S
      | none => S' = S

def spAt (s : TSt) : Int :=
  match rowOf s with
  | some (sp, _) => sp
  | none => 0

def mapAt (s : TSt) : CMap :=
  match rowOf s with
  | some (_, n) => mapOf n
  | none => ⟨[], []⟩

/-- THE EXCURSION'S ALIGNMENT, WITH ITS MEMORY ITEMS (header). -/
inductive texcM (FR : Nat → Nat → Prop) : TSt → (Int → Option Nat) → List Eitem → TSt → Prop where
  | stop (s : TSt) (S : Int → Option Nat) : texcM FR s S [] s
  | step (s : TSt) (S : Int → Option Nat) (g1 g2 : List Eitem) (s' : TSt)
      (S' : Int → Option Nat) (mid : List Eitem) (s'' : TSt) :
      grpOkb s.tPc g1 g2 = true → tmove s s' → memOk FR s.tPc (spAt s) S g1 g2 S' →
      texcM FR s' S' mid s'' → texcM FR s S (g1 ++ (g2 ++ mid)) s''

theorem texcMRtc (FR : Nat → Nat → Prop) (s : TSt) (S : Int → Option Nat) (g : List Eitem)
    (s'' : TSt) : texcM FR s S g s'' → rtc tmove s s'' := by
  intro h
  induction h with
  | stop s S => exact rtc_refl s
  | step s S g1 g2 s' S' mid s'' _ hm _ _ ih => exact rtc_l hm ih

/-! ### 5.1 The carry maps, unfolded -/

theorem crSetSame (m : List (Nat × List Nat)) (x : Nat) (v : List Nat) :
    cr (setR m x v) x = v := by
  simp [cr, setR]

theorem crSetOther (m : List (Nat × List Nat)) (x y : Nat) (v : List Nat) (h : y ≠ x) :
    cr (setR m x v) y = cr m y := by
  have : (x == y) = false := by simp [beq_eq_false_iff_ne]; omega
  simp [cr, setR, this]

theorem csSetSame (m : List (Int × List Nat)) (o : Int) (v : List Nat) :
    cs (setS m o v) o = v := by
  simp [cs, setS]

theorem csSetOther (m : List (Int × List Nat)) (o o' : Int) (v : List Nat) (h : o' ≠ o) :
    cs (setS m o v) o' = cs m o' := by
  have : (o == o') = false := by simp [beq_eq_false_iff_ne]; omega
  simp [cs, setS, this]

theorem cunionMem (m : List (Nat × List Nat)) (srcs : List Dsrc) (r : Nat) :
    r ∈ cunion m srcs → ∃ y, Dsrc.DReg y ∈ srcs ∧ r ∈ cr m y := by
  intro h
  unfold cunion at h
  obtain ⟨s, hs, hr⟩ := List.mem_flatMap.mp h
  cases s with
  | DReg y => exact ⟨y, hs, hr⟩
  | DLdRes => simp at hr

theorem crMem (m : List (Nat × List Nat)) (x r : Nat) :
    r ∈ cr m x → ∃ p, p ∈ m ∧ p.1 = x ∧ r ∈ p.2 := by
  unfold cr
  cases h : m.find? (fun p => p.1 == x) with
  | none => intro e; simp at e
  | some p =>
    intro e
    exact ⟨p, List.mem_of_find?_eq_some h, by simpa using List.find?_some h, e⟩

theorem csMem (m : List (Int × List Nat)) (o : Int) (r : Nat) :
    r ∈ cs m o → ∃ p, p ∈ m ∧ p.1 = o ∧ r ∈ p.2 := by
  unfold cs
  cases h : m.find? (fun p => p.1 == o) with
  | none => intro e; simp at e
  | some p =>
    intro e
    exact ⟨p, List.mem_of_find?_eq_some h, by simpa using List.find?_some h, e⟩

theorem cmLeSound (a b : CMap) (h : cmLe a b = true) :
    (∀ x r, r ∈ cr a.cmR x → r ∈ cr b.cmR x) ∧ (∀ o r, r ∈ cs a.cmS o → r ∈ cs b.cmS o) := by
  unfold cmLe at h
  rw [Bool.and_eq_true, List.all_eq_true, List.all_eq_true] at h
  refine ⟨fun x r hr => ?_, fun o r hr => ?_⟩
  · obtain ⟨p, hp, rfl, hrp⟩ := crMem _ _ _ hr
    have := List.all_eq_true.mp (h.1 p hp) r hrp
    exact List.contains_iff_mem.mp this
  · obtain ⟨p, hp, rfl, hrp⟩ := csMem _ _ _ hr
    have := List.all_eq_true.mp (h.2 p hp) r hrp
    exact List.contains_iff_mem.mp this

/-! ### 5.2 The roles of a spill and a restore -/

theorem spStRole (pc : Int) (o : Int) :
    spSt pc = some o → depsRd (krole pc) = none ∧ depsRd2 (krole pc) = none := by
  unfold spSt
  cases h : krole pc <;> intro e <;> simp at e
  exact ⟨rfl, rfl⟩

theorem spLdNotSt (pc : Int) (o : Int) : spLd pc = some o → spSt pc = none := by
  unfold spLd spSt
  cases krole pc <;> intro e <;> simp at e <;> rfl

theorem spLdDec (pc : Int) (o : Int) (rd : Nat) (dec : List Dsrc) :
    spLd pc = some o → depsRd (krole pc) = some (rd, dec) → Dsrc.DLdRes ∈ dec := by
  unfold spLd
  cases h : krole pc <;> intro e <;> simp at e
  intro hd
  simp only [depsRd] at hd
  split at hd
  · simp only [Option.some.injEq, Prod.mk.injEq] at hd
    obtain ⟨-, rfl⟩ := hd
    exact List.mem_cons_self ..
  · cases hd

/-! ### 5.3 Provenance across one instruction's group -/

theorem dprovNeutralRun (s : Dstate) (g : List Eitem) (x : Nat) :
    g.all provNeutralb = true → dprov (dsRun s g) x = dprov s x := by
  induction g generalizing s with
  | nil => intro _; rfl
  | cons it g ih =>
    intro h
    rw [List.all_cons, Bool.and_eq_true] at h
    rw [dsRunCons, ih _ h.2, dprovNeutralItem s it x h.1]

theorem regwSegOther (rd : Nat) (dec : List Dsrc) (g : List Eitem) (s : Dstate) (x : Nat) :
    regwSeg rd dec g = true → x ≠ rd → dprov (dsRun s g) x = dprov s x := by
  induction g generalizing s with
  | nil => intro h; exact absurd h Bool.false_ne_true
  | cons it g ih =>
    intro hg hne
    rw [dsRunCons]
    obtain ⟨l, k⟩ := it
    cases l
    case LRegW rd' srcs =>
      simp only [regwSeg, Bool.and_eq_true] at hg
      obtain ⟨⟨hrd, -⟩, hn⟩ := hg
      have e : rd' = rd := Nat.eq_of_beq_eq_true hrd
      subst e
      rw [dprovNeutralRun _ _ _ hn, dprovRegwNe _ _ _ _ _ hne]
    all_goals
      simp only [regwSeg] at hg
      rw [ih _ hg hne, dprovNeutralItem _ _ _ rfl]

theorem regwSegSrc (rd : Nat) (dec : List Dsrc) (g : List Eitem) (s : Dstate) (y e : Nat) :
    regwSeg rd dec g = true → Dsrc.DReg y ∈ dec → e ∈ dprov s y → e ∈ dprov (dsRun s g) rd := by
  induction g generalizing s with
  | nil => intro h; exact absurd h Bool.false_ne_true
  | cons it g ih =>
    intro hg hy he
    rw [dsRunCons]
    obtain ⟨l, k⟩ := it
    cases l
    case LRegW rd' srcs =>
      simp only [regwSeg, Bool.and_eq_true] at hg
      obtain ⟨⟨hrd, hsub⟩, hn⟩ := hg
      have e' : rd' = rd := Nat.eq_of_beq_eq_true hrd
      subst e'
      rw [dprovNeutralRun _ _ _ hn, dprovRegwEq]
      exact dsrcsPosReg _ _ _ _ (dsubbElem _ _ _ hsub hy) he
    all_goals
      simp only [regwSeg] at hg
      exact ih _ hg hy (by rw [dprovNeutralItem _ _ _ rfl]; exact he)

theorem regwSegSkip (rd : Nat) (dec : List Dsrc) (ga g : List Eitem) :
    ga.all provNeutralb = true → regwSeg rd dec (ga ++ g) = regwSeg rd dec g := by
  induction ga with
  | nil => intro _; rfl
  | cons it ga ih =>
    intro h
    rw [List.all_cons, Bool.and_eq_true] at h
    obtain ⟨l, k⟩ := it
    cases l
    case LRegW => simp [provNeutralb] at h
    all_goals simp only [List.cons_append, regwSeg]; exact ih h.2

theorem dstepLdKeep (s : Dstate) (it : Eitem) (k : Nat) :
    notInstrb it = true → k ∈ s.dsLd → k ∈ (dstep s it).1.dsLd := by
  intro hn hk
  obtain ⟨l, ko⟩ := it
  cases l <;> cases ko <;> simp only [dstep, notInstrb] at hn ⊢ <;>
    first | exact hk | exact List.mem_cons_of_mem _ hk | exact absurd hn Bool.false_ne_true

theorem regwSegLdAux (rd : Nat) (dec : List Dsrc) (k : Nat) (gb : List Eitem) (s : Dstate) :
    regwSeg rd dec gb = true → Dsrc.DLdRes ∈ dec → gb.all notInstrb = true → k ∈ s.dsLd →
    k ∈ dprov (dsRun s gb) rd := by
  induction gb generalizing s with
  | nil => intro h; exact absurd h Bool.false_ne_true
  | cons it gb ih =>
    intro hg hd hni hk
    rw [List.all_cons, Bool.and_eq_true] at hni
    rw [dsRunCons]
    obtain ⟨l, ko⟩ := it
    cases l
    case LRegW rd' srcs =>
      simp only [regwSeg, Bool.and_eq_true] at hg
      obtain ⟨⟨hrd, hsub⟩, hn⟩ := hg
      have e' : rd' = rd := Nat.eq_of_beq_eq_true hrd
      subst e'
      rw [dprovNeutralRun _ _ _ hn, dprovRegwEq]
      unfold dsrcsPos
      exact List.mem_flatten.mpr ⟨dsrcPos s .DLdRes,
        List.mem_map_of_mem (dsubbElem _ _ _ hsub hd), hk⟩
    all_goals
      simp only [regwSeg] at hg
      exact ih _ hg hd hni.2 (dstepLdKeep _ _ k hni.1 hk)

/-- A restore: the load item's position reaches the destination's provenance. -/
theorem regwSegLd (rd : Nat) (dec : List Dsrc) (ga gb : List Eitem) (aq lat : Bool) (base : Int)
    (tvs : List (Nat × BitVec 8)) (asrc : List Dsrc) (k : Nat) (s : Dstate) :
    regwSeg rd dec (ga ++ (Wlabel.LLoad aq lat base tvs asrc, some k) :: gb) = true →
    ga.all provNeutralb = true → gb.all notInstrb = true → Dsrc.DLdRes ∈ dec →
    k ∈ dprov (dsRun s (ga ++ (Wlabel.LLoad aq lat base tvs asrc, some k) :: gb)) rd := by
  intro hg hga hgb hd
  rw [regwSegSkip _ _ _ _ hga] at hg
  simp only [regwSeg] at hg
  rw [dsRunApp, dsRunCons]
  exact regwSegLdAux rd dec k gb _ hg hd hgb (List.mem_cons_self ..)

theorem realizesbOther (d0 : Option (Nat × List Dsrc)) (g : List Eitem) (s : Dstate) (x : Nat) :
    realizesb d0 g = true → (∀ rd dec, d0 = some (rd, dec) → x ≠ rd) →
    dprov (dsRun s g) x = dprov s x := by
  cases d0 with
  | none => intro h _; exact dprovNeutralRun s g x h
  | some p =>
    obtain ⟨rd, dec⟩ := p
    intro h hne
    exact regwSegOther rd dec g s x h (hne rd dec rfl)

/-! ### 5.4 The concrete invariant, one instruction -/

/-- THE CONCRETE INVARIANT (header): every register (slot) the carry map says carries an
interrupted tainted register carries an entry (its last spill is a HOP — every read that reads
from it is an entry). -/
def cInv (Ent Hop : Nat → Prop) (t : List Nat) (d : Dstate) (S : Int → Option Nat) (m : CMap) :
    Prop :=
  (∀ x r, r ∈ cr m.cmR x → taintMem r t = true → ∃ e, e ∈ dprov d x ∧ Ent e) ∧
  (∀ o r, r ∈ cs m.cmS o → taintMem r t = true → ∃ w, S o = some w ∧ Hop w)

theorem cInvMono (Ent Hop : Nat → Prop) (t : List Nat) (d : Dstate) (S : Int → Option Nat)
    (m m' : CMap) : cmLe m' m = true → cInv Ent Hop t d S m → cInv Ent Hop t d S m' := by
  intro hle ⟨h1, h2⟩
  obtain ⟨l1, l2⟩ := cmLeSound m' m hle
  exact ⟨fun x r hr ht => h1 x r (l1 x r hr) ht, fun o r hr ht => h2 o r (l2 o r hr) ht⟩

/-- **ONE EXCURSION INSTRUCTION (header)**: B1's group test, the memory items and the frame
relation carry the invariant from the carry map to its transfer. -/
theorem cInvStep (Ent Hop : Nat → Prop) (FR : Nat → Nat → Prop)
    (hFR : ∀ w k, Hop w → FR w k → Ent k) (em : Hemission)
    (hspill : ∀ (pre post : List Eitem) (rl : Bool) (a : Int) (v : List (BitVec 8))
      (asrc vsrc : List Dsrc) (w x e : Nat),
      em.emItems = pre ++ (Wlabel.LStore rl a v asrc vsrc, some w) :: post →
      Dsrc.DReg x ∈ vsrc → e ∈ dprov (dsRun dsInit pre) x → Ent e → Hop w)
    (t : List Nat) (p rest g1 g2 : List Eitem) (pc sp : Int) (S S' : Int → Option Nat)
    (m : CMap) :
    em.emItems = p ++ (g1 ++ g2) ++ rest →
    grpOkb pc g1 g2 = true → memOk FR pc sp S g1 g2 S' →
    cInv Ent Hop t (dsRun dsInit p) S m →
    cInv Ent Hop t (dsRun dsInit (p ++ (g1 ++ g2))) S' ⟨xferR pc sp m, xferS pc sp m⟩ := by
  intro hes hg hmem ⟨hR, hS⟩
  unfold grpOkb at hg
  rw [Bool.and_eq_true] at hg
  obtain ⟨hg1, hg2⟩ := hg
  have hrun : dsRun dsInit (p ++ (g1 ++ g2)) = dsRun (dsRun (dsRun dsInit p) g1) g2 := by
    rw [dsRunApp, dsRunApp]
  -- the first destination
  have claim1 : ∀ x r, r ∈ cr (xferR1 pc sp m) x → taintMem r t = true →
      ∃ e, e ∈ dprov (dsRun (dsRun dsInit p) g1) x ∧ Ent e := by
    intro x r hr ht
    unfold xferR1 at hr
    cases hd : depsRd (krole pc) with
    | none =>
      rw [hd] at hr hg1
      obtain ⟨e, he, hent⟩ := hR x r hr ht
      exact ⟨e, by rw [dprovNeutralRun _ _ _ hg1]; exact he, hent⟩
    | some pr =>
      obtain ⟨rd, dec⟩ := pr
      rw [hd] at hr hg1
      by_cases hx : x = rd
      · subst hx
        rw [crSetSame] at hr
        rcases List.mem_append.mp hr with hr | hr
        · obtain ⟨y, hy, hry⟩ := cunionMem _ _ _ hr
          obtain ⟨e, he, hent⟩ := hR y r hry ht
          exact ⟨e, regwSegSrc _ _ _ _ _ _ hg1 hy he, hent⟩
        · unfold slotOf at hr
          cases hl : spLd pc with
          | none => rw [hl] at hr; simp at hr
          | some o =>
            rw [hl] at hr
            obtain ⟨w, hw, hhop⟩ := hS (sp + o) r hr ht
            have hst := spLdNotSt pc o hl
            unfold memOk at hmem
            rw [hst, hl] at hmem
            obtain ⟨⟨ga, gb, aq, lat, base, tvs, asrc, k, rfl, hga, hgb, hfr⟩, -⟩ := hmem
            exact ⟨k, regwSegLd _ _ ga gb aq lat base tvs asrc k _ hg1 hga hgb
              (spLdDec pc o x dec hl hd), hFR w k hhop (hfr w hw)⟩
      · rw [crSetOther _ _ _ _ hx] at hr
        obtain ⟨e, he, hent⟩ := hR x r hr ht
        exact ⟨e, by rw [regwSegOther _ _ _ _ _ hg1 hx]; exact he, hent⟩
  refine ⟨?_, ?_⟩
  · -- registers
    intro x r hr ht
    rw [hrun]
    unfold xferR at hr
    cases hd2 : depsRd2 (krole pc) with
    | none =>
      rw [hd2] at hr hg2
      obtain ⟨e, he, hent⟩ := claim1 x r hr ht
      exact ⟨e, by rw [dprovNeutralRun _ _ _ hg2]; exact he, hent⟩
    | some pr =>
      obtain ⟨rd2, dec2⟩ := pr
      rw [hd2] at hr hg2
      by_cases hx : x = rd2
      · subst hx
        rw [crSetSame] at hr
        obtain ⟨y, hy, hry⟩ := cunionMem _ _ _ hr
        obtain ⟨e, he, hent⟩ := claim1 y r hry ht
        exact ⟨e, regwSegSrc _ _ _ _ _ _ hg2 hy he, hent⟩
      · rw [crSetOther _ _ _ _ hx] at hr
        obtain ⟨e, he, hent⟩ := claim1 x r hr ht
        exact ⟨e, by rw [regwSegOther _ _ _ _ _ hg2 hx]; exact he, hent⟩
  · -- slots
    intro o' r hr ht
    show ∃ w, S' o' = some w ∧ Hop w
    unfold xferS at hr
    cases hs : spSt pc with
    | none =>
      rw [hs] at hr
      have hS' : S' = S := by
        unfold memOk at hmem
        rw [hs] at hmem
        cases hl : spLd pc with
        | none => rw [hl] at hmem; exact hmem
        | some o => rw [hl] at hmem; exact hmem.2
      rw [hS']
      exact hS o' r hr ht
    | some o =>
      rw [hs] at hr
      unfold memOk at hmem
      rw [hs] at hmem
      obtain ⟨ga, gb, rl, a, v, asrc, vsrc, w, hsplit, hcv, rfl⟩ := hmem
      by_cases ho : o' = sp + o
      · subst ho
        rw [csSetSame] at hr
        obtain ⟨y, hy, hry⟩ := cunionMem _ _ _ hr
        obtain ⟨e, he, hent⟩ := hR y r hry ht
        obtain ⟨hr1, hr2⟩ := spStRole pc o hs
        rw [hr1] at hg1
        rw [hr2] at hg2
        have hg1' : g1.all provNeutralb = true := hg1
        have hg2' : g2.all provNeutralb = true := hg2
        have hneu : (g1 ++ g2).all provNeutralb = true := by
          rw [List.all_append, hg1', hg2']
        rw [hsplit, List.all_append, Bool.and_eq_true] at hneu
        refine ⟨w, by simp [slotSet], ?_⟩
        refine hspill (p ++ ga) (gb ++ rest) rl a v asrc vsrc w y e ?_
          (dsubbElem _ _ _ hcv hy) ?_ hent
        · rw [hes, hsplit]; simp only [List.append_assoc, List.cons_append]
        · rw [dsRunApp, dprovNeutralRun _ _ _ hneu.1]; exact he
      · rw [csSetOther _ _ _ _ ho] at hr
        obtain ⟨w', hw', hhop⟩ := hS o' r hr ht
        exact ⟨w', by simp only [slotSet, ho, ↓reduceIte]; exact hw', hhop⟩

/-! ### 5.5 Along the excursion -/

theorem tmoveSuccs (s s' : TSt) : tmove s s' → s' ∈ tsuccs s := by
  intro h
  cases h with
  | seq f pc fr hl hk => simp [tsuccs, hl, hk]
  | brN f pc tgt fr hl hk => simp [tsuccs, hl, hk]
  | brT f pc tgt fr hl hk => simp [tsuccs, hl, hk]
  | jmp f pc tgt fr hl hk => simp [tsuccs, hl, hk]
  | call f pc tgt fr hl hk hs => simp [tsuccs, hl, hk, hs]
  | hook f fr hl hk => simp [tsuccs, hl, hk]
  | ret f pc g a fr hl hk => simp [tsuccs, hl, hk]

theorem tgoodbOf (s : TSt) : tgood trapTab s → tgoodb s = true := by
  rintro ⟨h1, h2⟩
  unfold tgoodb
  rw [Bool.and_eq_true, List.all_eq_true]
  exact ⟨h1, fun ga hga => h2 ga hga⟩

theorem rowOfMem (s : TSt) (sp : Int) (n : Nat) :
    rowOf s = some (sp, n) → (s, sp, n) ∈ trapFlow := by
  unfold rowOf
  cases h : trapFlow.find? (fun r => r.1 == s) with
  | none => intro e; cases e
  | some r =>
    intro e
    simp only [Option.map_some, Option.some.injEq] at e
    have hm := List.mem_of_find?_eq_some h
    have hk := List.find?_some h
    simp only [beq_iff_eq] at hk
    obtain ⟨r1, r2⟩ := r
    simp only at hk e
    subst hk e
    exact hm

/-- The table's edge check, at one step of a run that reaches the `sret`. -/
theorem flowEdge (s s' : TSt) (sp : Int) (n : Nat) :
    rowOf s = some (sp, n) → tmove s s' → tgood trapTab s' →
    ∃ sp' n', rowOf s' = some (sp', n') ∧
      cmLe (mapOf n') ⟨xferR s.tPc sp (mapOf n), xferS s.tPc sp (mapOf n)⟩ = true := by
  intro hr hm hg
  have hrow := List.all_eq_true.mp flowOk _ (rowOfMem s sp n hr)
  have h2 := List.all_eq_true.mp hrow s' (tmoveSuccs s s' hm)
  rw [tgoodbOf s' hg, Bool.not_true, Bool.false_or] at h2
  revert h2
  cases hr' : rowOf s' with
  | none => intro h; simp at h
  | some pn =>
    obtain ⟨sp', n'⟩ := pn
    cases xferSp s.tPc sp with
    | none => intro h; simp at h
    | some sp2 =>
      intro h
      simp only [Bool.and_eq_true] at h
      exact ⟨sp', n', rfl, h.2⟩

/-- **ALONG THE EXCURSION (header)**: a census-aligned run from a tabled state, on a run that
reaches the `sret`, carries the invariant from the state's carry map to the end state's. -/
theorem cInvRun (Ent Hop : Nat → Prop) (FR : Nat → Nat → Prop)
    (hFR : ∀ w k, Hop w → FR w k → Ent k) (em : Hemission)
    (hspill : ∀ (pre post : List Eitem) (rl : Bool) (a : Int) (v : List (BitVec 8))
      (asrc vsrc : List Dsrc) (w x e : Nat),
      em.emItems = pre ++ (Wlabel.LStore rl a v asrc vsrc, some w) :: post →
      Dsrc.DReg x ∈ vsrc → e ∈ dprov (dsRun dsInit pre) x → Ent e → Hop w)
    (t : List Nat) (s : TSt) (S : Int → Option Nat) (g : List Eitem) (s'' : TSt) :
    texcM FR s S g s'' →
    ∀ (p rest : List Eitem) (sp : Int) (n : Nat), em.emItems = p ++ g ++ rest →
    rtc tmove tStart s → rtc tmove s'' tEnd → rowOf s = some (sp, n) →
    cInv Ent Hop t (dsRun dsInit p) S (mapOf n) →
    ∃ S'' sp'' n'', rowOf s'' = some (sp'', n'') ∧
      cInv Ent Hop t (dsRun dsInit (p ++ g)) S'' (mapOf n'') := by
  intro hx
  induction hx with
  | stop s S =>
    intro p rest sp n _ _ _ hr hc
    exact ⟨S, sp, n, hr, by rw [List.append_nil]; exact hc⟩
  | step s S g1 g2 s' S' mid s'' hgrp hm hmem hrest ih =>
    intro p rest sp n hes h0 hend hr hc
    have hspAt : spAt s = sp := by unfold spAt; rw [hr]
    rw [hspAt] at hmem
    have hes' : em.emItems = p ++ (g1 ++ g2) ++ (mid ++ rest) := by
      rw [hes]; simp only [List.append_assoc]
    have hstep := cInvStep Ent Hop FR hFR em hspill t p (mid ++ rest) g1 g2 s.tPc sp S S'
      (mapOf n) hes' hgrp hmem hc
    have h0' : rtc tmove tStart s' := rtc_r h0 hm
    have hend' : rtc tmove s' tEnd := rtc_transitive (texcMRtc FR _ _ _ _ hrest) hend
    obtain ⟨sp', n', hr', hle⟩ := flowEdge s s' sp n hr hm (trapRunGood s' h0' hend')
    have hc' := cInvMono Ent Hop t _ S' _ _ hle hstep
    obtain ⟨S'', sp'', n'', hr'', hc''⟩ :=
      ih (p ++ (g1 ++ g2)) rest sp' n' (by rw [hes]; simp only [List.append_assoc]) h0' hend
        hr' hc'
    refine ⟨S'', sp'', n'', hr'', ?_⟩
    rw [show p ++ (g1 ++ (g2 ++ mid)) = p ++ (g1 ++ g2) ++ mid by simp only [List.append_assoc]]
    exact hc''

/-! ### 5.7 The emission's reads precede its stores (a structural fact of `hemit`) -/

theorem eadmNone (ls : List Wlabel) (it : Eitem) : it ∈ eadm ls → it.2 = none := by
  intro h
  simp only [eadm, List.mem_map] at h
  obtain ⟨_, _, rfl⟩ := h
  rfl

theorem hemitPosGe (dv : Nat → Efab) (k : Nat) (ws : Wstate) (row : List Lbl) (p : Pexv6)
    (es : List Eitem) (pfin : Pexv6) :
    hemit dv k ws row p es pfin → ∀ it, it ∈ es → ∀ j, it.2 = some j → k ≤ j := by
  intro h it hit j hj
  obtain ⟨_, hle, _⟩ := hemitTagLbl dv k ws row p es pfin it j h hit hj
  exact hle

/-- **POSITIONS INCREASE (header)**: in a conformant emission, every positioned item before an
item that is not an `sc`'s store half sits at a smaller row position. -/
theorem hemitPosLt (dv : Nat → Efab) (k0 : Nat) (ws : Wstate) (row : List Lbl) (p : Pexv6)
    (es : List Eitem) (pfin : Pexv6) :
    hemit dv k0 ws row p es pfin →
    ∀ (pre : List Eitem) (l0 : Wlabel) (w : Nat) (post : List Eitem),
      es = pre ++ (l0, some w) :: post →
      (∀ rl b d a v, l0 ≠ Wlabel.LExStore rl b d a v) →
      ∀ it, it ∈ pre → ∀ j, it.2 = some j → j < w := by
  intro h
  induction h with
  | HEnil k ws p =>
    intro pre l0 w post hes
    simp at hes
  | HEone k ws lb row p ls pa da l p' es pfin _ _ _ hrest ih =>
    intro pre l0 w post hes hnot it hit j hj
    rcases List.append_eq_append_iff.mp hes with ⟨a', hpre, hb⟩ | ⟨c', ha, hd⟩
    · cases a' with
      | nil =>
        simp only [List.append_nil] at hpre
        subst hpre
        rw [eadmNone _ _ hit] at hj; cases hj
      | cons x a'' =>
        simp only [List.cons_append, List.cons.injEq] at hb
        obtain ⟨rfl, hes'⟩ := hb
        have hmem : (l0, some w) ∈ es := by
          rw [hes']; exact List.mem_append_right _ (List.mem_cons_self ..)
        have hw : k + 1 ≤ w := hemitPosGe _ _ _ _ _ _ _ hrest _ hmem w rfl
        subst hpre
        rcases List.mem_append.mp hit with hit | hit
        · rw [eadmNone _ _ hit] at hj; cases hj
        rcases List.mem_cons.mp hit with rfl | hit
        · simp only [Option.some.injEq] at hj; omega
        · exact ih a'' l0 w post hes' hnot it hit j hj
    · cases c' with
      | nil =>
        simp only [List.append_nil] at ha
        subst ha
        rw [eadmNone _ _ hit] at hj; cases hj
      | cons y c'' =>
        simp only [List.cons_append, List.cons.injEq] at hd
        obtain ⟨rfl, -⟩ := hd
        have hmem : (l0, some w) ∈ eadm ls := by
          rw [ha]; exact List.mem_append_right _ (List.mem_cons_self ..)
        have := eadmNone ls (l0, some w) hmem
        cases this
  | HEpair k ws lb row p ls1 pa da l1 pm dm ls2 pm2 dm2 l2 p' es pfin _ hre _ _ _ hrest ih =>
    intro pre l0 w post hes hnot it hit j hj
    obtain ⟨aq, rl, base, tvs, data, asrc1, asrc2, vsrc2, rfl, rfl, _, _, _⟩ := hre
    rcases List.append_eq_append_iff.mp hes with ⟨a', hpre, hb⟩ | ⟨c', ha, hd⟩
    · cases a' with
      | nil =>
        simp only [List.append_nil] at hpre
        subst hpre
        rw [eadmNone _ _ hit] at hj; cases hj
      | cons x a'' =>
        simp only [List.cons_append, List.cons.injEq] at hb
        obtain ⟨rfl, hb2⟩ := hb
        subst hpre
        rcases List.append_eq_append_iff.mp hb2 with ⟨b', ha'', hb3⟩ | ⟨c'', ha2, hd2⟩
        · cases b' with
          | nil =>
            simp only [List.nil_append, List.cons.injEq, Prod.mk.injEq] at hb3
            obtain ⟨⟨rfl, -⟩, -⟩ := hb3
            exact absurd rfl (hnot rl base data asrc2 vsrc2)
          | cons z b'' =>
            simp only [List.cons_append, List.cons.injEq] at hb3
            obtain ⟨rfl, hes'⟩ := hb3
            have hmem : (l0, some w) ∈ es := by
              rw [hes']; exact List.mem_append_right _ (List.mem_cons_self ..)
            have hw : k + 1 ≤ w := hemitPosGe _ _ _ _ _ _ _ hrest _ hmem w rfl
            subst ha''
            rcases List.mem_append.mp hit with hit | hit
            · rw [eadmNone _ _ hit] at hj; cases hj
            rcases List.mem_cons.mp hit with rfl | hit
            · simp only [Option.some.injEq] at hj; omega
            rcases List.mem_append.mp hit with hit | hit
            · rw [eadmNone _ _ hit] at hj; cases hj
            rcases List.mem_cons.mp hit with rfl | hit
            · simp only [Option.some.injEq] at hj; omega
            · exact ih b'' l0 w post hes' hnot it hit j hj
        · cases c'' with
          | nil =>
            simp only [List.nil_append, List.cons.injEq, Prod.mk.injEq] at hd2
            obtain ⟨⟨rfl, -⟩, -⟩ := hd2
            exact absurd rfl (hnot rl base data asrc2 vsrc2)
          | cons y c3 =>
            simp only [List.cons_append, List.cons.injEq] at hd2
            obtain ⟨rfl, -⟩ := hd2
            have hmem : (l0, some w) ∈ eadm ls2 := by
              rw [ha2]; exact List.mem_append_right _ (List.mem_cons_self ..)
            have := eadmNone ls2 (l0, some w) hmem
            cases this
    · cases c' with
      | nil =>
        simp only [List.append_nil] at ha
        subst ha
        rw [eadmNone _ _ hit] at hj; cases hj
      | cons y c'' =>
        simp only [List.cons_append, List.cons.injEq] at hd
        obtain ⟨rfl, -⟩ := hd
        have hmem : (l0, some w) ∈ eadm ls1 := by
          rw [ha]; exact List.mem_append_right _ (List.mem_cons_self ..)
        have := eadmNone ls1 (l0, some w) hmem
        cases this

/-- **The reads before a store** (`hmono` of `texcFreeSound`, `ereadOk` of `pinSegPinStoreT`),
from the hart's conformance. -/
theorem hartConfReadsBefore (i : Nat) (row : List Lbl) (p0 : Pexv6) (dv : Nat → Efab)
    (em : Hemission) (pre post : List Eitem) (l : Wlabel) (w : Nat) :
    hartConf i row p0 dv em → em.emItems = pre ++ (l, some w) :: post →
    (∀ rl b d a v, l ≠ Wlabel.LExStore rl b d a v) →
    ereadOk (fun e => e < w) pre := by
  intro hcf hes hnot it k hit hk _
  exact hemitPosLt dv 0 wsInit row p0 _ _ hcf pre l w post hes hnot it hit k hk

/-! ### 5.6 THE REAL EXCURSION CERTIFICATE -/

/-- **A FENCE-FREE TRAP EXCURSION (header)**: the walk's taint avoids `stimecmp` (`presRegs`);
the excursion's items are the trap entry's (provenance-neutral: no `LRegW` before the
announce, B1's `dfNoneNeutral`), an alignment `texcM` with a fence-free census run from
`kernelvec`'s entry to its `sret` WITH THE FRAME FACT as its `FR` — every restore READS FROM its
slot's last spill (`grf`) — and the `sret`'s own group (no destination: neutral). -/
def texcFree (G : Gexec) (i : Nat) (em : Hemission) (pfx : List Eitem) (t : List Nat)
    (gx : List Eitem) : Prop :=
  (∀ r, taintMem r t = true → r ∈ presRegs) ∧
  ∃ (gi gk gs rest : List Eitem) (S0 : Int → Option Nat),
    gx = gi ++ (gk ++ gs) ∧ em.emItems = pfx ++ gx ++ rest ∧
    gi.all provNeutralb = true ∧ gs.all provNeutralb = true ∧
    texcM (fun w k => WeakRvwmoAcyc.grf G (i, w) (i, k)) tStart S0 gk tEnd

theorem cmIdCr (x r : Nat) : r ∈ cr cmId.cmR x → r = x := by
  intro h
  obtain ⟨p, hp, rfl, hr⟩ := crMem _ _ _ h
  unfold cmId at hp
  obtain ⟨y, -, rfl⟩ := List.mem_map.mp hp
  simpa using hr

theorem cmIdCs (o : Int) (r : Nat) : r ∈ cs cmId.cmS o → False := by
  intro h
  obtain ⟨p, hp, -, -⟩ := csMem _ _ _ h
  simp [cmId] at hp

/-- **THE REAL EXCURSION IS CERTIFIED (header)**: for the hart's conformant emission (`hartConf`,
the tagged dependency clause), `texcFree` is sound for the load's entries: the walk's taint
survives every fence-free trap excursion, through `hopEnt` at each spill/restore pair. -/
theorem texcFreeSound (GT : GdexecT) (i : Nat) (row : List Lbl) (p0 : Pexv6) (dv : Nat → Efab)
    (em : Hemission) (j : Nat) :
    GT.gtG.gxProg[i]? = some row → hartConf i row p0 dv em →
    (∀ x, x ∈ rowDepsT em.emItems → (((i, x.1.1), (i, x.1.2)), x.2) ∈ GT.gtDeps) →
    xSound (texcFree GT.gtG i em) (tEnt (forget GT) (gtAd GT.gtG GT.gtDeps) i j) := by
  intro hrow hcf hconfT pfx t gx hx hinv
  have hmono : ∀ (pre post : List Eitem) (rl : Bool) (a : Int) (v : List (BitVec 8))
      (asrc vsrc : List Dsrc) (w : Nat),
      em.emItems = pre ++ (Wlabel.LStore rl a v asrc vsrc, some w) :: post →
      ereadOk (fun e => e < w) pre :=
    fun pre post _ _ _ _ _ w hes' =>
      hartConfReadsBefore i row p0 dv em pre post _ w hcf hes' (fun _ _ _ _ _ h => by cases h)
  obtain ⟨hpres, gi, gk, gs, rest, S0, rfl, hes, hgi, hgs, hrun⟩ := hx
  let Ent := tEnt (forget GT) (gtAd GT.gtG GT.gtDeps) i j
  let FR := fun w k => WeakRvwmoAcyc.grf GT.gtG (i, w) (i, k)
  let Hop := fun w => ∀ k, FR w k → Ent k
  have hFR : ∀ w k, Hop w → FR w k → Ent k := fun w k h hf => h k hf
  -- the row kinds of the emission's positioned items
  have hkind : ∀ it, it ∈ em.emItems → ∀ x, it.2 = some x →
      (elbIsR it.1 = true → gisRd GT.gtG (i, x) = true) ∧
      (elbIsW it.1 = true → gisW GT.gtG (i, x) = true) := by
    intro it hit x hx
    obtain ⟨lb, hlk, hr, hw⟩ := hartConfTagLbl i row p0 dv em it x hcf hit hx
    have hg : gxLbl GT.gtG (i, x) = some lb := by
      show (GT.gtG.gxProg[i]?).bind (fun p => p[x]?) = _
      rw [hrow]; exact hlk
    exact ⟨fun h => by simp [gisRd, hg, hr h], fun h => by simp [gisW, hg, hw h]⟩
  have hspill : ∀ (pre post : List Eitem) (rl : Bool) (a : Int) (v : List (BitVec 8))
      (asrc vsrc : List Dsrc) (w x e : Nat),
      em.emItems = pre ++ (Wlabel.LStore rl a v asrc vsrc, some w) :: post →
      Dsrc.DReg x ∈ vsrc → e ∈ dprov (dsRun dsInit pre) x → Ent e → Hop w := by
    intro pre post rl a v asrc vsrc w x e hes' hx he hent k hfr
    have hlt : e < w :=
      (dsRunWithin (fun e => e < w) dsInit pre (dsWithinInit _) (hmono _ _ _ _ _ _ _ _ hes')).1
        x e he
    have hrd : gisRd GT.gtG (i, e) = true := by
      have hw := dsRunWithin (fun e => ∃ it, it ∈ em.emItems ∧ it.2 = some e ∧
          elbIsR it.1 = true) dsInit pre (dsWithinInit _)
        (fun it k hin hpos hr => ⟨it, by rw [hes']; exact List.mem_append_left _ hin, hpos, hr⟩)
      obtain ⟨it, hit, hpos, hr⟩ := hw.1 x e he
      exact (hkind it hit e hpos).1 hr
    have hwr : gisW GT.gtG (i, w) = true :=
      (hkind _ (by rw [hes']; exact List.mem_append_right _ (List.mem_cons_self ..)) w rfl).2 rfl
    exact hopEnt GT i j em pre post rl a v asrc vsrc w k x e hconfT hes' hx he hlt hrd hwr hfr hent
  -- the start
  have hstart : invOkS Ent (dsRun dsInit (pfx ++ gi)) t := by
    rw [dsRunApp]; exact invNeutralRunS _ _ _ _ hgi hinv
  obtain ⟨n0, hr0, hle0⟩ : ∃ n0, rowOf tStart = some (0, n0) ∧ cmLe (mapOf n0) cmId = true := by
    have h := flowStart
    revert h
    cases rowOf tStart with
    | none => intro h; simp at h
    | some pn =>
      obtain ⟨sp, n⟩ := pn
      intro h
      simp only [Bool.and_eq_true, beq_iff_eq] at h
      exact ⟨n, by rw [h.1], h.2⟩
  have hc0 : cInv Ent Hop t (dsRun dsInit (pfx ++ gi)) S0 (mapOf n0) := by
    obtain ⟨l1, l2⟩ := cmLeSound _ _ hle0
    refine ⟨fun x r hr ht => ?_, fun o r hr _ => (cmIdCs o r (l2 o r hr)).elim⟩
    have := cmIdCr x r (l1 x r hr)
    subst this
    exact hstart r ht
  have hes2 : em.emItems = (pfx ++ gi) ++ gk ++ (gs ++ rest) := by
    rw [hes]; simp only [List.append_assoc]
  obtain ⟨S'', sp'', n'', hr'', hc''⟩ :=
    cInvRun Ent Hop FR hFR em hspill t tStart S0 gk tEnd hrun (pfx ++ gi) (gs ++ rest) 0 n0 hes2
      (rtc_refl _) (rtc_refl _) hr0 hc0
  -- the end: every preserved register carries itself
  have hend : ∀ x, x ∈ presRegs → x ∈ cr (mapOf n'').cmR x := by
    have h := flowEnd
    rw [hr''] at h
    simp only [Bool.and_eq_true, List.all_eq_true] at h
    intro x hx
    exact List.contains_iff_mem.mp (h.2 x hx)
  intro r ht
  obtain ⟨e, he, hent⟩ := hc''.1 r r (hend r (hpres r ht)) ht
  refine ⟨e, ?_, hent⟩
  rw [show pfx ++ (gi ++ (gk ++ gs)) = (pfx ++ gi ++ gk) ++ gs by simp only [List.append_assoc],
    dsRunApp, dprovNeutralRun _ _ _ hgs]
  exact he


/-! ### 5.8 The certifying classes through fence-free trap excursions -/

/-- The untagged dependency clause on `forget`, from the tagged one (`gdexecQconfTForget`). -/
theorem forgetConf (GT : GdexecT) (i : Nat) (row : List Lbl) (p0 : Pexv6) (dv : Nat → Efab)
    (em : Hemission) :
    GT.gtG.gxProg[i]? = some row → hartConf i row p0 dv em →
    (∀ x, x ∈ rowDepsT em.emItems → (((i, x.1.1), (i, x.1.2)), x.2) ∈ GT.gtDeps) →
    ∀ jk, jk ∈ rowDeps em.emItems → ((i, jk.1), (i, jk.2)) ∈ (forget GT).gdDeps := by
  intro hrow hcf hdeps jk hjk
  obtain ⟨tg, htg, -⟩ := rowDepsSubT em.emItems jk.1 jk.2 hjk
  obtain ⟨-, ⟨lr, hlr, hr⟩, lb, hlb, hw⟩ := hartConfRowDepsWf i row p0 dv em jk hcf hjk
  refine (elemOfForgetDeps GT.gtG GT.gtDeps (i, jk.1) (i, jk.2)).2 ⟨tg, hdeps _ htg, ?_, ?_⟩
  · simp [gisRd, gxLbl, hrow, hlr, hr]
  · simp [gisW, gxLbl, hrow, hlb, hw]

/-- **PDep THROUGH FENCE-FREE TRAP EXCURSIONS (header)**: the any-path PDep certificate with the
site oracle `psitesT (texcFree …)` — trap excursions allowed at any walk state, each certified
by its census alignment and the frame fact — in the published quantifier (`forget GT`,
`ad := gtAd`). -/
theorem pinSegPinStoreFree (GT : GdexecT) (i : Nat) (row : List Lbl) (p0 : Pexv6)
    (dv : Nat → Efab) (em : Hemission) (sg : Seg) (pcL : Int) (j k : Nat) (own : Bool)
    (base pre g0 post : List Eitem) (s : PState) (rl : Bool) (a : Int) (v : List (BitVec 8))
    (asrc vsrc : List Dsrc) :
    GT.gtG.gxProg[i]? = some row → hartConf i row p0 dv em →
    (∀ x, x ∈ rowDepsT em.emItems → (((i, x.1.1), (i, x.1.2)), x.2) ∈ GT.gtDeps) →
    sg.sgEntry = (i, j) → sg.sgExit = (i, k) →
    invOk j (dsRun dsInit base) (pinT0 pcL) →
    em.emItems = pre ++ g0 ++ (Wlabel.LStore rl a v asrc vsrc, some k) :: post →
    psitesT (texcFree GT.gtG i em) pcL own base pre s →
    g0.all provNeutralb = true →
    dsubb (depsAddr (krole s.psPc)) asrc = true → dsubb (depsVsrc (krole s.psPc)) vsrc = true →
    (srcsTainted s.psT (depsAddr (krole s.psPc))
      || srcsTainted s.psT (depsVsrc (krole s.psPc))) = true →
    segPinC (forget GT) (gtAd GT.gtG GT.gtDeps) sg := by
  intro hrow hcf hdeps he hx hbase hes hsite hg0 hca hcv htn
  exact pinSegPinStoreT _ (forget GT) (gtAd GT.gtG GT.gtDeps) i em sg pcL j k own base pre g0
    post s rl a v asrc vsrc (texcFreeSound GT i row p0 dv em j hrow hcf hdeps)
    (forgetConf GT i row p0 dv em hrow hcf hdeps) he hx hbase hes hsite hg0
    (hartConfReadsBefore i row p0 dv em (pre ++ g0) post _ k hcf hes
      (fun _ _ _ _ _ h => by cases h)) hca hcv htn

/-- **PCtrl THROUGH FENCE-FREE TRAP EXCURSIONS (header).** -/
theorem pinSegPinCtrlFree (GT : GdexecT) (i : Nat) (row : List Lbl) (p0 : Pexv6)
    (dv : Nat → Efab) (em : Hemission) (sg : Seg) (pcL : Int) (j k : Nat) (own : Bool)
    (base pre g0 mid post : List Eitem) (s : PState) (srcs : List Dsrc) (kc : Option Nat)
    (rl : Bool) (a : Int) (v : List (BitVec 8)) (asrc vsrc : List Dsrc) :
    GT.gtG.gxProg[i]? = some row → hartConf i row p0 dv em →
    (∀ x, x ∈ rowDepsT em.emItems → (((i, x.1.1), (i, x.1.2)), x.2) ∈ GT.gtDeps) →
    sg.sgEntry = (i, j) → sg.sgExit = (i, k) →
    invOk j (dsRun dsInit base) (pinT0 pcL) →
    em.emItems = pre ++ g0 ++ (Wlabel.LCtrl srcs, kc)
      :: (mid ++ (Wlabel.LStore rl a v asrc vsrc, some k) :: post) →
    psitesT (texcFree GT.gtG i em) pcL own base pre s →
    g0.all provNeutralb = true →
    dsubb (depsCtrl (krole s.psPc)) srcs = true →
    srcsTainted s.psT (depsCtrl (krole s.psPc)) = true →
    segPinC (forget GT) (gtAd GT.gtG GT.gtDeps) sg := by
  intro hrow hcf hdeps he hx hbase hes hsite hg0 hcov htn
  have hes' : em.emItems = (pre ++ g0 ++ (Wlabel.LCtrl srcs, kc) :: mid) ++
      (Wlabel.LStore rl a v asrc vsrc, some k) :: post := by
    rw [hes]; simp only [List.append_assoc, List.cons_append]
  have hrb := hartConfReadsBefore i row p0 dv em _ post _ k hcf hes'
    (fun _ _ _ _ _ h => by cases h)
  refine pinSegPinCtrlT _ (forget GT) (gtAd GT.gtG GT.gtDeps) i em sg pcL j k own base pre g0 mid
    post s srcs kc rl a v asrc vsrc (texcFreeSound GT i row p0 dv em j hrow hcf hdeps)
    (forgetConf GT i row p0 dv em hrow hcf hdeps) he hx hbase hes hsite hg0
    (fun it k' hit hk hr => hrb it k' (List.mem_append_left _ hit) hk hr)
    hcov htn

end PinTrap
end Weak
