/-
Weak: **the weak-memory lifting tower** (M1c): the `RiscvExec.wp_exec_step` analogue over
`Weak.weakRiscvLang` -- the single per-hart framing point, plus the device-thread rule.

Rocq: `iris/WeakExec.v` @ xxvzwolszwmp (1cc222280).

The Rocq header, in substance (Rocq vocabulary).

THE ORACLE, AND WHY THERE ARE TWO HART RULES.  `RiscvExec`'s contract is "the caller supplies
an `exec` witness for both tick values; `exec_run_det`'s uniqueness half then discharges
`wp_lift_step`'s ∀-successor obligation".  Uniqueness is FALSE for the weak machine by design (a
load has many admissible timestamps), so the ∀-successor obligation has to be handed to the
caller.  Two forms:
- `wpWrunStep` -- the PRIMITIVE.  The continuation is universally quantified over the
  successors of the RELATIONAL interpreter (`Weak.wrun`), which is literally what `wprimStep`
  produces.  Premise-free, and the one the adequacy/soundness story rests on.
- `wpWexecStep` -- the shape M2's leaves want: the continuation is universally quantified over
  the ORACLE and the successors of the FUNCTIONAL interpreter (`Weak.wexec`), which is what a
  leaf can compute with.  It is `wpWrunStep` plus one caller obligation, `wexecCovers` --
  "every `wrun` successor of THIS program in THIS state is also a `wexec` successor at some
  oracle".

WHY `wexecCovers` IS A PREMISE AND NOT A LEMMA.  The general bridge `wrun → ∃ χ χ', wexec … χ …
= some …` is NOT provable, and the obstacle is exactly the one `WeakInterp`'s §8 comment names:
`choose`, which `wrun` branches over and `wexec` rejects.  Nor does the caller's exec witness at
one oracle pin the path: a `wrun` may read a DIFFERENT admissible value than the witness did,
and from there descend into a different subtree of the monad -- possibly one with a `choose` in
it (the generated model's `undefined_bitvector` sites are `choose`s).  So the bridge holds
exactly on the choice-free fragment, which is what `wrunWexec` proves -- the sufficient
condition a leaf discharges (over the concrete instruction it has peeled) to obtain
`wexecCovers`.

SIMPLIFICATIONS (see `Weak/WeakGhost.lean`'s header): single era -- the rules read the
generation off the state interpretation's `wgenPin` rather than off a generation counter, and
take `gen = 0` as a premise, so there are no corpse arms to tail into.

**Deviations from Rocq.**

1. NAMES: the tree's camelCase (map below).  Rocq's ambient `GenId`/`CpuId` classes and the
   `Loop`/`UartLoop`/… notations do not exist in Lean (WeakGhost deviation 12): the rules take
   the generation `gen : Nat` and the hart `cpu : CPU` explicitly, `Loop` is `WExpr.loop gen
   cpu`, and the Rocq premise `gen_id = 0` is the hypothesis `gen = 0`.
2. THE MONAD (WeakInterp deviation 4): `M X` is `SailM X`.  `mchoiceFree` is structural over
   it, as `wrun`; the model's `.error` node (no Rocq counterpart; `wrun` is `False` there) is
   choice-free (`True`); every other non-`choose` node quantifies over its answers, as Rocq's
   catch-all arm.
3. O2 (`notes/weak-port-o2-design.md`, WeakInterp's header).  Rocq `wread_coh_ts` says an
   `ak_coh` read is pinned to `coh_ts`; its `ak_coh` is now `akIfetch`, the i-cache read, whose
   admissibility is the window `¬ writesIn log a t (max t itv)` -- NOT the latest write -- so
   the Rocq statement is false.  `wreadCohTs` carries the extra premise `|log| ≤ itv` (the
   i-cache has seen the whole log), under which it holds; it is `WeakInterp.wreadAllSeen`'s
   i-cache arm.  The bridge `wrunWexec` no longer needs it at all: Lean's `wexec` CONSUMES the
   oracle at an i-cache read like at every RAM read (WeakInterp deviation 8), so its RAM-read
   arm is the one Rocq used for non-coherent reads (cons the chosen timestamps).
4. THE DEVICE THREADS (WeakLang deviation 2).  Lean's three devices are programs of one
   device language, stepped by ONE arm `wdevStep` (Rocq `uart_step` / `plic_step` /
   `wdisk_step` are gone), and a device task's expression carries its residual program.  So
   Rocq's three rules `wp_wuart_step`, `wp_wplic_step`, `wp_wdisk_step` are the ONE rule
   `wpWdevStep` for any device `d`, task `tid` and program `m`: the caller gets the whole state
   interpretation and, at every `wdevStep` successor `(m', g', efs)`, re-establishes it and
   gives the WP of the residual program `WExpr.dev gen d tid m'` and of every forked task in
   `efs` (Rocq: the successor expression is the same loop and nothing forks; the Lean
   device language has `fork`).  The Rocq post-state names `wg_dev`, `wg_regs`, `wg_dma`
   (which existed to spell those three arms' successors) are therefore not ported: `wdevStep`
   spells its successors itself (`setDev`, `setReg`, the `wdmaMsgs` log append).
5. THE NEW `WGState` FIELDS `wgitv`, `wgrt` and `Wmstate.wmItv` (WeakGhost deviation 18): the
   state interpretations do not mention them, and WeakExec does not need them to.  The hart
   rule hands its caller `whartView g cpu` (whose `wmItv` is `g.wgitv cpu`) and writes the
   successor back with `whartWrite` (which writes `wmItv` back to `wgitv`); nothing in the
   reassembly reads either.  A device step may move `wgrt` (`fork`/`join`), and the caller
   re-establishes `weakStateInterp g'` at whatever `g'` it is handed.
6. Lean-only helpers: `weakStateInterpEq` (the `StateInterp` instance, by `rfl`), `regsInterpAcc`
   (Rocq `RiscvPtsto.gregs_interp_acc` over the `[∗list] c ∈ cpus` register conjunct, the
   `wwsInterpAcc` pattern), `weakStateInterpPin`.
7. STATEMENT SHAPES (the WeakGhost deviation 9 convention): Rocq `P -∗ WWP e` is `P ⊢ WWP e`.

**Rocq → Lean name map.**  `wexec_covers` `wexecCovers`, `mchoice_free` `mchoiceFree`,
`wread_coh_ts` `wreadCohTs` (deviation 3), `wrun_wexec` `wrunWexec`, `wexec_covers_choice_free`
`wexecCoversChoiceFree`, `wp_wrun_step` `wpWrunStep`, `wp_wexec_step` `wpWexecStep`,
`wp_wuart_step`/`wp_wplic_step`/`wp_wdisk_step` `wpWdevStep` (deviation 4).

**Not ported:** `wg_dev`, `wg_regs`, `wg_dma` (deviation 4; uses checked: none outside
`WeakExec.v`).

**Statements checked** (diffed against Rocq by hand): all; the changed ones are deviations 1, 3
and 4.
-/
import Weak.WeakGhost
import Iris.ProgramLogic.Lifting

namespace Weak

open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode Iris.Std
open MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open Sail.ArchSem (FreeM)
open LeanRV64D

/-! ## 1. The wrun/wexec bridge -/

/-- The caller obligation of `wpWexecStep`: every relational successor is a functional one, at
SOME oracle.  (The oracle and the post-state move together -- a different timestamp choice
gives a different post-view.) -/
def wexecCovers (tid : Option Nat) {X : Type} (m : SailM X) (s : Wmstate) : Prop :=
  ∀ (x : X) (s' : Wmstate), wrun tid m s x s' →
    ∃ χ χ', wexec tid m χ s = some (x, s', χ')

/-- The choice-free fragment of the monad: no reachable node is `choose` (deviation 2). -/
def mchoiceFree {X : Type} : SailM X → Prop
  | .pure _ => True
  | .impure (.error _) _ => True
  | .impure (.ok o) k =>
    match o, k with
    | .choose _, _ => False
    | _, k => ∀ t, mchoiceFree (k t)

/-- An i-cache read that has seen the whole log has no choice either: its window then forces
the latest write (deviation 3; Rocq `wread_coh_ts`). -/
theorem wreadCohTs (s : Wmstate) (ak : AkInfo) (pa : PAddr) (n : Nat) (ts : List Nat)
    (w : BitVec (8 * n)) :
    ak.akIfetch = true → s.wmLog.length ≤ s.wmItv → wreadOk s ak pa n ts w →
    ts = cohTs s pa n := by
  intro hc hall hok
  exact wreadAllSeen s ak pa n ts w (by simp only [hc, ↓reduceIte]; exact hall) hok

/-- THE BRIDGE, on the choice-free fragment.  Every read arm is complete on its own
(`wreadBytesComplete`), so the oracle is built by consing the timestamps the run chose; every
other arm is deterministic and `wexec` follows `wrun` step for step. -/
theorem wrunWexec (tid : Option Nat) {X : Type} (m : SailM X) :
    mchoiceFree m →
    ∀ (s : Wmstate) (x : X) (s' : Wmstate), wrun tid m s x s' →
      ∃ χ χ', wexec tid m χ s = some (x, s', χ') := by
  induction m with
  | pure y =>
    intro _ s x s' h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨[], [], rfl⟩
  | impure call k ih =>
    intro hcf s x s' h
    cases call with
    | error e => simp only [wrun] at h
    | ok o =>
      cases o
      case memRead n va req =>
        simp only [mchoiceFree] at hcf
        simp only [wrun] at h
        split at h
        · rename_i hd
          split at h
          · rename_i w d' hdr
            obtain ⟨χ, χ', hex⟩ := ih _ (hcf _) _ _ _ h
            refine ⟨χ, χ', ?_⟩
            simp only [wexec, if_pos hd, hdr]
            exact hex
          · exact h.elim
        · rename_i hd
          obtain ⟨w, ts, hok, hr⟩ := h
          obtain ⟨χ, χ', hex⟩ := ih _ (hcf _) _ _ _ hr
          refine ⟨ts :: χ, χ', ?_⟩
          simp only [wexec, if_neg hd, List.head?_cons, List.tail_cons,
            wreadBytesComplete _ _ _ _ _ _ hok]
          exact hex
      case memWrite n va req =>
        simp only [mchoiceFree] at hcf
        simp only [wrun] at h
        split at h
        · rename_i hd
          split at h
          · rename_i v hv
            split at h
            · rename_i d' hdw
              obtain ⟨χ, χ', hex⟩ := ih _ (hcf _) _ _ _ h
              refine ⟨χ, χ', ?_⟩
              simp only [wexec, if_pos hd, hv, hdw]
              exact hex
            · exact h.elim
          · exact h.elim
        · rename_i hd
          split at h
          · rename_i v hv
            obtain ⟨χ, χ', hex⟩ := ih _ (hcf _) _ _ _ h
            refine ⟨χ, χ', ?_⟩
            simp only [wexec, if_neg hd, hv]
            exact hex
          · exact h.elim
      case choose =>
        simp only [mchoiceFree] at hcf
      case readRam => simp only [wrun] at h
      case writeRam => simp only [wrun] at h
      all_goals
        simp only [mchoiceFree] at hcf
        simp only [wrun] at h
        obtain ⟨χ, χ', hex⟩ := ih _ (hcf _) _ _ _ h
        exact ⟨χ, χ', by simp only [wexec]; exact hex⟩

theorem wexecCoversChoiceFree (tid : Option Nat) {X : Type} (m : SailM X) (s : Wmstate) :
    mchoiceFree m → wexecCovers tid m s :=
  fun hcf x s' hrun => wrunWexec tid m hcf s x s' hrun

/-! ## 2. The hart rule -/

section WeakHart

variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [WeakGS GF]

/-- The language's state interpretation IS `weakStateInterp` (deviation 6). -/
theorem weakStateInterpEq (g : WGState) (ns : Nat) (κs : List Empty) (nt : Nat) :
    StateInterp.stateInterp (GF := GF) g ns κs nt = weakStateInterp (hlc := hlc) (GF := GF) g :=
  rfl

/-- Focus one hart's register file, with the handle to put an updated one back (deviation 6;
Rocq `RiscvPtsto.gregs_interp_acc`). -/
theorem regsInterpAcc (cpu : CPU) (f : CPU → RegFile) :
    iprop([∗list] c ∈ cpus, regInterp (hlc := hlc) (GF := GF) c (f c)) ⊢
      regInterp cpu (f cpu) ∗
        ∀ rs : RegFile, regInterp cpu rs -∗
          iprop([∗list] c ∈ cpus, regInterp (hlc := hlc) (GF := GF) c (updCpu f cpu rs c)) := by
  iintro H
  icases BigSepL.bigSepL_lookup_acc_impl (Φ := fun _ c => regInterp (hlc := hlc) (GF := GF) c (f c))
    (cpus_get? cpu) $$ H with ⟨Hc, Hclose⟩
  iframe Hc
  iintro %rs Hc'
  iapply Hclose $$ %(fun _ c => regInterp (hlc := hlc) (GF := GF) c (updCpu f cpu rs c))
  · imodintro
    iintro %k %y %hk %hne Hy
    have hy : y ≠ cpu := cpus_get?_ne hk cpu hne
    simp only [gregInsertNe f cpu y rs hy]
    iexact Hy
  · simp only [gregInsertEq]
    iexact Hc'

/-- THE PRIMITIVE.  The caller opens the hart's view of the state (`wmstateInterp`, i.e. the SC
`mstate_interp` with the memory conjunct replaced by log + latest-write map + this hart's weak
state), supplies ONE witness that the machine can step, and a continuation that must
re-establish the hart interpretation at EVERY relational successor.  `wp_lift_step`'s tick
nondeterminism rides in the continuation's `tick` binder. -/
theorem wpWrunStep (gen : Nat) (cpu : CPU) (hgen : gen = 0) :
    (∀ σ : Wmstate, wmstateInterp (hlc := hlc) (GF := GF) cpu σ ={⊤,∅}=∗
      ⌜∃ χ σ0 χ', wexec (some cpu.val) (riscvStep false) χ σ = some ((), σ0, χ')⌝ ∗
      ▷ (∀ (tick : Bool) (σ' : Wmstate),
          ⌜wrun (some cpu.val) (riscvStep tick) σ () σ'⌝ ={∅,⊤}=∗
            wmstateInterp (hlc := hlc) (GF := GF) cpu σ' ∗
            wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu))) ⊢
    wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu) := by
  iintro H
  unfold wwpTriv
  iapply wp_lift_step rfl
  iintro %g %ns %obs %obs' %nt Hσ
  rw [weakStateInterpEq]
  unfold weakStateInterp
  icases Hσ with ⟨%Hpin, %Hbnd, %Hnv, %Hwf, Hgr, Hdev, Hlog, Hlat, Hws⟩
  have hlive : wthreadLive g gen := ⟨Hpin.1, by rw [hgen]; exact Hpin.2⟩
  icases regsInterpAcc cpu g.wgregs $$ Hgr with ⟨Hri, Hclose⟩
  icases wwsInterpAcc cpu g.wgws $$ Hws with ⟨Hwsc, Hwsclose⟩
  imod H $$ %(whartView g cpu) [Hri Hdev Hlog Hlat Hwsc] with ⟨%Hred, Hk⟩
  · simp only [wmstateInterp, whartView]
    isplitr
    · ipureintro; exact Hbnd cpu
    isplitr
    · ipureintro; exact noViolationHart _ _ cpu Hnv
    isplitr
    · ipureintro; exact Hwf
    isplitl [Hri]
    · iexact Hri
    isplitl [Hdev]
    · iexact Hdev
    isplitl [Hlog]
    · iexact Hlog
    isplitl [Hlat]
    · iexact Hlat
    · iexact Hwsc
  imodintro
  isplit
  · ipureintro
    obtain ⟨χ, σ0, χ', hex⟩ := Hred
    exact ⟨[], WExpr.loop gen cpu, whartWrite g cpu σ0, [], rfl, rfl, rfl,
      Or.inl ⟨hlive, false, (), σ0, wexecWrun _ _ _ _ _ _ _ hex, rfl⟩⟩
  inext
  iintro %e₂ %g₂ %eₜ %Hstep _
  obtain ⟨rfl, rfl, rfl, harm⟩ := wprimStepLoopInv gen cpu g obs e₂ g₂ eₜ Hstep
  rcases harm with ⟨_, tick, u, s', hrun, rfl⟩ | ⟨hnl, _⟩
  case inr => exact absurd hlive hnl
  cases u
  -- the era-initial image is never written, so the post-state's image IS the one the state
  -- interpretation holds (`wrunImg`)
  have Himg : s'.wmImg = g.wgimg := wrunImg _ _ _ _ _ hrun
  -- the OTHER harts' views did not move, but the log may have grown: `wsBounded` is monotone
  -- in its bound, and the log is append-only
  obtain ⟨l, hl, hown⟩ := wrunLogTid _ _ _ _ _ hrun
  have hl' : s'.wmLog = g.wglog ++ l := hl
  have Hlen : g.wglog.length ≤ s'.wmLog.length := by rw [hl', List.length_append]; omega
  imod Hk $$ %tick %s' %hrun with ⟨Hs', HWP⟩
  unfold wmstateInterp
  icases Hs' with ⟨%Hbnd', %Hnv', %Hwf', Hri', Hdev', Hlog', Hlat', Hwsc'⟩
  have Hbnd2 : ∀ c : CPU,
      wsBounded ((whartWrite g cpu s').wgws c) (whartWrite g cpu s').wglog.length := by
    intro c
    rw [whartWriteLog]
    by_cases hc : c = cpu
    · subst hc
      rw [whartWriteWsEq]
      exact Hbnd'
    · rw [whartWriteWsNe _ _ _ _ hc]
      exact wsBoundedMono _ _ _ (Hbnd c) Hlen
  -- THE GLOBAL φ REASSEMBLY.  Every message this step appended carries THIS hart's tid
  -- (`wrunLogTid`), so the fresh obligations are vacuous for the author; every other hart's
  -- cell is untouched and its floors are below the OLD log's top (`noViolationStep`).
  have Hnv2 : noViolation (whartWrite g cpu s').wglog (whartWrite g cpu s').wgws := by
    show noViolation s'.wmLog (updCpu g.wgws cpu s'.wmWs)
    rw [hl']
    apply noViolationStep g.wglog l g.wgws _ cpu Hnv Hbnd hown
    · intro c0 hne
      exact gwsInsertNe _ _ _ _ hne
    · rw [gwsInsertEq, ← hl']
      exact Hnv'
  ihave Hlat' := (show wlatInterp (GF := GF) s'.wmImg s'.wmLog ⊢ wlatInterp g.wgimg s'.wmLog
    from by rw [Himg]) $$ Hlat'
  imodintro
  rw [weakStateInterpEq]
  unfold weakStateInterp
  simp only [whartWrite]
  isplitl [Hri' Hclose Hdev' Hlog' Hlat' Hwsc' Hwsclose]
  · isplitr
    · ipureintro; exact Hpin
    isplitr
    · ipureintro; exact Hbnd2
    isplitr
    · ipureintro; exact Hnv2
    isplitr
    · ipureintro; exact Hwf'
    isplitl [Hri' Hclose]
    · iapply Hclose $$ %s'.wmRegs Hri'
    isplitl [Hdev']
    · iexact Hdev'
    isplitl [Hlog']
    · iexact Hlog'
    isplitl [Hlat']
    · iexact Hlat'
    · iapply Hwsclose $$ %s'.wmWs Hwsc'
  isplitl [HWP]
  · iexact HWP
  · exact BigSepL.bigSepL_nil_intro

/-- THE LEAF-FACING FORM: the same rule with the continuation quantified over the ORACLE and
`wexec`'s successors.  The first conjunct is the bridge obligation discussed in the header --
dischargeable by `wexecCoversChoiceFree` on the choice-free fragment. -/
theorem wpWexecStep (gen : Nat) (cpu : CPU) (hgen : gen = 0) :
    (∀ σ : Wmstate, wmstateInterp (hlc := hlc) (GF := GF) cpu σ ={⊤,∅}=∗
      ⌜∀ tick : Bool, wexecCovers (some cpu.val) (riscvStep tick) σ⌝ ∗
      ⌜∃ χ σ0 χ', wexec (some cpu.val) (riscvStep false) χ σ = some ((), σ0, χ')⌝ ∗
      ▷ (∀ (tick : Bool) (χ : List (List Nat)) (σ' : Wmstate) (χ' : List (List Nat)),
          ⌜wexec (some cpu.val) (riscvStep tick) χ σ = some ((), σ', χ')⌝ ={∅,⊤}=∗
            wmstateInterp (hlc := hlc) (GF := GF) cpu σ' ∗
            wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu))) ⊢
    wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu) := by
  iintro H
  iapply wpWrunStep gen cpu hgen
  iintro %σ Hσ
  imod H $$ %σ Hσ with ⟨%Hcov, %Hred, Hk⟩
  imodintro
  isplitr
  · ipureintro; exact Hred
  inext
  iintro %tick %σ' %Hrun
  obtain ⟨χ, χ', hex⟩ := Hcov tick () σ' Hrun
  iapply Hk $$ %tick %χ %σ' %χ' %hex

end WeakHart

/-! ## 3. The device threads

Each hands the caller the WHOLE state interpretation and takes it back at its arm's successor:
a device thread touches no per-hart resource, so there is nothing to focus.  The disk's DMA
write is the only device primitive that appends to the log -- re-establishing `wlatInterp`
across that append is the caller's obligation and is where M5's device-view work lands. -/

section WeakDev

variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [WeakGS GF]

/-- The single-era pin, read off without consuming the state interpretation (deviation 6). -/
theorem weakStateInterpPin (g : WGState) :
    weakStateInterp (hlc := hlc) (GF := GF) g ⊢
      ⌜wgenPin g⌝ ∗ weakStateInterp (hlc := hlc) (GF := GF) g := by
  unfold weakStateInterp
  iintro ⟨%h, H⟩
  isplitr
  · ipureintro; exact h
  isplitr
  · ipureintro; exact h
  · iexact H

/-- THE DEVICE RULE (deviation 4: Rocq `wp_wuart_step`, `wp_wplic_step`, `wp_wdisk_step`). -/
theorem wpWdevStep (gen : Nat) (d : DevId) (tid : TaskId) (m : DevProg d) (hgen : gen = 0) :
    (∀ g : WGState, weakStateInterp (hlc := hlc) (GF := GF) g ={⊤,∅}=∗
      ▷ (∀ (m' : DevProg d) (g' : WGState) (efs : List WExpr),
          ⌜wdevStep gen d tid m g m' g' efs⌝ ={∅,⊤}=∗
            weakStateInterp (hlc := hlc) (GF := GF) g' ∗
            wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.dev gen d tid m') ∗
            iprop([∗list] ef ∈ efs, wwpTriv (hlc := hlc) (GF := GF) ⊤ ef))) ⊢
    wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.dev gen d tid m) := by
  iintro H
  unfold wwpTriv
  iapply wp_lift_step rfl
  iintro %g %ns %obs %obs' %nt Hσ
  rw [weakStateInterpEq]
  icases weakStateInterpPin g $$ Hσ with ⟨%Hpin, Hσ⟩
  have hlive : wthreadLive g gen := ⟨Hpin.1, by rw [hgen]; exact Hpin.2⟩
  imod H $$ %g Hσ with Hk
  imodintro
  isplit
  · ipureintro
    obtain ⟨e', g', efs, hs⟩ := wprimStepDevLive gen d tid m g hlive
    exact ⟨[], e', g', efs, hs⟩
  inext
  iintro %e₂ %g₂ %eₜ %Hstep _
  obtain ⟨_, ⟨_, m', rfl, hs⟩ | ⟨hnl, _⟩⟩ := wprimStepDevInv gen d tid m g obs e₂ g₂ eₜ Hstep
  · imod Hk $$ %m' %g₂ %eₜ %hs with ⟨Hσ', HWP, Hefs⟩
    imodintro
    rw [weakStateInterpEq]
    isplitl [Hσ']
    · iexact Hσ'
    isplitl [HWP]
    · iexact HWP
    · iexact Hefs
  · exact absurd hlive hnl

end WeakDev

end Weak
