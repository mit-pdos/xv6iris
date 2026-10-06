/-
Weak: **confinement for a variant-tolerant window** (6a): the producers of
`WeakRacy.wstepOkRacy` from confined `execEff` runs.

Rocq: `iris/WeakVarCert.v` @ xxvzwolszwmp.

The Rocq header, in substance.  `WeakCert`'s confinement theorem turns ONE
confined `execEff` run into `WeakBridge.wstepOk`, and it can do that only
because every non-self-pinning read of the trace is pinned.  The page-table
walk's LEAF slot is not pinnable (the walker writes A/D bits back, from any
hart, lazily), so that route is closed for every S-mode instruction.
`WeakRacy.wstepOkRacy` is the peel that tolerates such a window; this file
supplies its PRODUCERS.

* §1 `traceDisj`: every access of the trace is disjoint from the window.
* §2 THE POST-RACY PEEL (`wstepOkRacyFalseOfConfined`): `WeakCert`'s
  `wstepEffConfinedPin` with the conclusion `wstepOkRacy … false` and the
  agreement half dropped.  The one premise that is not `WeakCert`'s: the
  confined memory is compared against the PATCHED flat memory
  `bmWrite (wflatMem …) ra rn wp` (`WeakRacy.wpatchSt`'s memory), and the two
  arms that consumed the old premise go through `readBytesPatchDisj` and
  `writeBytesPatchComm` -- both need only disjointness, which `traceDisj`
  carries.
* §3 THE PRE-RACY TRACE: `tracePinOff` (pinnedness demanded only off the
  window) and the ORDERED `traceRacy` (before the racy read every read is
  disjoint and there is no RAM write at all; at the racy read the phase flips
  and the tail is `traceDisj`).
* §4 THE PHASE-`true` PEEL (`wstepOkRacyTrueOfConfined`): from a FAMILY of
  confined runs, one per `Φ`-satisfying window value, at the confined memory
  PATCHED with that value.  The member at `w` reads `w` back at the window, so
  the racy arm hands it to §2 at `wp := w` with no reconciliation step; off the
  window the patch is invisible, so ONE member (the witness, from the
  inhabitation premise) decides every arm's shape.  `wadmFilterInhabited`
  produces that witness from what the rule's caller holds.

**Deviations from Rocq.**
1. NAMES: the tree's camelCase (map below).  No name of this file is in the
   duplicated-name table.  Vocabulary as `Weak/WeakCert.lean` deviations 1-2:
   `pa_add a j` ↦ `a + BitVec.ofNat 64 j`, `rn n : N` ↦ `Nat`, `acc_addr` ↦
   `WeakInterp.accAddr`, `MState r m d` ↦ `⟨r, m, d⟩ : ExecSt`, `mm ⊆ mm2` ↦
   `bmSub mm mm2`, `dom mm ⊆ W` ↦ `bmDomSub mm W`, `read_bytes`/`write_bytes`
   ↦ `bmRead`/`bmWrite`, `is_Some o` ↦ `o.isSome = true`, `M X` ↦ `SailM X`.
2. O2 (`Weak/WeakCert.lean` deviation 3): `tracePinOff`'s per-byte obligation
   is `readPinned s ak` (Rocq `pinned_read s`), and it is CONJOINED with
   `WeakCert.fetchFresh es`, so that `tracePinOfOff` can rebuild Lean's
   `tracePin` (which carries `fetchFresh`).  Hence `tracePinOffMono`
   additionally takes `s.wmItv ≤ s'.wmItv` (as `tracePinMono`), and
   `tracePinOffTail`/`tracePinOffHead` read the first conjunct.  The trace
   premise of §2 is Lean's `tracePin` (so also `fetchFresh`).
3. Stage B: the barrier arm moves to `wbarrierPost` (data views AND `wmItv`),
   as in `wstepOkRacy` and `execEff`.
4. The Rocq `Print Assumptions` lines are not ported (no declarations).

**Rocq → Lean name map.**  `trace_disj` `traceDisj`, `trace_disj_tail`
`traceDisjTail`, `trace_disj_read` `traceDisjRead`, `trace_disj_write`
`traceDisjWrite`, `wstep_ok_racy_false_of_confined`
`wstepOkRacyFalseOfConfined`, `wstep_ok_racy_false_of_window`
`wstepOkRacyFalseOfWindow`, `trace_pin_off` `tracePinOff`,
`trace_pin_off_of_pin` `tracePinOffOfPin`, `trace_pin_of_off` `tracePinOfOff`,
`trace_pin_off_mono` `tracePinOffMono`, `trace_pin_off_tail` `tracePinOffTail`,
`trace_pin_off_head` `tracePinOffHead`, `trace_racy` `traceRacy`,
`racc_disj_irrefl` `raccDisjIrrefl`, `trace_racy_disj_tail` `traceRacyDisjTail`,
`trace_racy_win_tail` `traceRacyWinTail`, `wstep_ok_racy_true_of_confined`
`wstepOkRacyTrueOfConfined`, `wstep_ok_racy_true_of_window`
`wstepOkRacyTrueOfWindow`, `wadm_filter_inhabited` `wadmFilterInhabited`.

**Dropped:** nothing (19 Rocq declarations, 19 Lean).

**Statements checked** (by hand, against Rocq): all; the changed ones are
deviations 2-3.
-/
import Weak.WeakCert
import Weak.WeakRacy

namespace Weak

open Iris Iris.Std
open MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open Sail.ArchSem (FreeM)
open LeanRV64D LeanRV64D.Functions

/-! ## 1. A trace that stays off the window -/

def traceDisj (ra : PAddr) (rn : Nat) (es : List Weff) : Prop :=
  (∀ (ak : AkInfo) (pa : PAddr) (n : Nat), Weff.WEread ak pa n ∈ es → raccDisj ra rn pa n) ∧
  (∀ (ak : AkInfo) (pa : PAddr) (n : Nat) (v : BitVec (8 * n)),
    Weff.WEwrite ak pa n v ∈ es → raccDisj ra rn pa n)

theorem traceDisjTail (ra : PAddr) (rn : Nat) (e : Weff) (es : List Weff) :
    traceDisj ra rn (e :: es) → traceDisj ra rn es := by
  rintro ⟨hr, hw⟩
  exact ⟨fun ak pa n hin => hr ak pa n (List.mem_cons_of_mem _ hin),
    fun ak pa n v hin => hw ak pa n v (List.mem_cons_of_mem _ hin)⟩

theorem traceDisjRead (ra : PAddr) (rn : Nat) (ak : AkInfo) (pa : PAddr) (n : Nat)
    (es : List Weff) : traceDisj ra rn (.WEread ak pa n :: es) → raccDisj ra rn pa n :=
  fun h => h.1 ak pa n List.mem_cons_self

theorem traceDisjWrite (ra : PAddr) (rn : Nat) (ak : AkInfo) (pa : PAddr) (n : Nat)
    (v : BitVec (8 * n)) (es : List Weff) :
    traceDisj ra rn (.WEwrite ak pa n v :: es) → raccDisj ra rn pa n :=
  fun h => h.2 ak pa n v List.mem_cons_self

/-! ## 2. THE POST-RACY PEEL -/

theorem wstepOkRacyFalseOfConfined (tid : Option Nat) (ra : PAddr) (rn : Nat) (rak : AkInfo)
    (Φ : (Nat → BitVec 8) → Prop) (Wp : Prop) (wp : BitVec (8 * rn)) {X : Type} (m : SailM X) :
    accWf ra rn →
    ∀ (s : Wmstate) (mm : BMap) (W : GSet PAddr) (x : X) (t' : ExecSt) (es : List Weff),
      wlogWf s.wmLog →
      (∀ a, a ∈ W → paZ a ≠ 0) →
      tracePin s es →
      traceDisj ra rn es →
      bmDomSub mm W →
      bmSub mm (bmWrite (wflatMem s.wmImg s.wmLog) ra rn wp) →
      bmDomSub t'.mem W →
      execEff m ⟨s.wmRegs, mm, s.wmDev⟩ = some (x, t', es) →
      wstepOkRacy tid ra rn rak Φ (raccDisj ra rn) Wp false m s := by
  intro hracc
  induction m with
  | pure y => intros; simp only [wstepOkRacy]
  | impure call k ih =>
    intro s mm W x t' es hwf hW0 hpin hdes hdom hsub hdom' hex
    cases call with
    | error e => simp only [wstepOkRacy]
    | ok o =>
      cases o
      case regWrite r v =>
        simp only [execEff] at hex
        simp only [wstepOkRacy]
        exact ih PUnit.unit (wsetReg s r v) mm W x t' es hwf hW0 hpin hdes hdom hsub hdom' hex
      case memRead n va req =>
        simp only [execEff] at hex
        simp only [wstepOkRacy]
        by_cases hd : mmioAcc req.pa n = true
        · rw [if_pos hd] at hex ⊢
          intro w d' hdr'
          simp only [hdr'] at hex
          exact ih _ (wsetDev s d') mm W x t' es hwf hW0 hpin hdes hdom hsub hdom' hex
        · rw [if_neg hd] at hex ⊢
          cases hrb : bmRead mm req.pa n with
          | none => simp only [hrb] at hex; cases hex
          | some w0 =>
            simp only [hrb] at hex
            obtain ⟨es0, hee, rfl⟩ := Weff.consEqSome.1 hex
            have hin := fun j (hj : j < n) => hdom _ (readBytesDom mm req.pa n w0 hrb j hj)
            have hacc : accWf req.pa n := accWfWindow W req.pa n hW0 hin
            have hpinf : akPins (classify req.access_kind) = false → ∀ j, j < n →
                readPinned s (classify req.access_kind) (WeakInterp.accAddr req.pa j) :=
              fun hnp j hj => hpin.1 _ _ _ List.mem_cons_self hnp j hj
            have hdisj : raccDisj ra rn req.pa n := traceDisjRead ra rn _ _ _ es0 hdes
            -- off the window the patch is invisible, so the confined read IS the flat one
            have hwrb : wreadBytes s (classify req.access_kind) req.pa n (cohTs s req.pa n) =
                some w0 := by
              rw [wreadBytesReadBytes s _ req.pa n hwf hacc,
                ← readBytesPatchDisj (wflatMem s.wmImg s.wmLog) ra rn wp req.pa n hracc hacc hdisj]
              exact readBytesMono _ _ _ _ _ hsub hrb
            have hpin2 : tracePin (wreadPost s (classify req.access_kind) req.pa (cohTs s req.pa n))
                es0 :=
              tracePinMono _ _ _ (wreadPostLog _ _ _ _) (wreadPostWsLe _ _ _ _)
                (by rw [wreadPostItv]; exact Nat.le_refl _) (tracePinTail _ _ _ hpin)
            have hsub2 : bmSub mm (bmWrite
                (wflatMem (wreadPost s (classify req.access_kind) req.pa (cohTs s req.pa n)).wmImg
                  (wreadPost s (classify req.access_kind) req.pa (cohTs s req.pa n)).wmLog)
                ra rn wp) := by
              rw [wreadPostImg, wreadPostLog]; exact hsub
            have hee2 : execEff (k (.Ok (w0, none)))
                ⟨(wreadPost s (classify req.access_kind) req.pa (cohTs s req.pa n)).wmRegs, mm,
                  (wreadPost s (classify req.access_kind) req.pa (cohTs s req.pa n)).wmDev⟩ =
                some (x, t', es0) := by
              rw [wreadPostRegs, wreadPostDev]; exact hee
            refine ⟨hacc, Or.inl ⟨hdisj, hpinf, fun w hw => ?_⟩⟩
            rw [hwrb] at hw
            simp only [Option.some.injEq] at hw
            subst hw
            exact ih _ _ mm W x t' es0 (wlogWfReadPost _ _ _ _ hwf) hW0 hpin2
              (traceDisjTail ra rn _ es0 hdes) hdom hsub2 hdom' hee2
      case memWrite n va req =>
        simp only [execEff] at hex
        simp only [wstepOkRacy]
        cases hv : req.value with
        | none => simp only [hv] at hex; cases hex
        | some w =>
          simp only [hv] at hex ⊢
          by_cases hd : mmioAcc req.pa n = true
          · rw [if_pos hd] at hex ⊢
            intro d' hdw'
            simp only [hdw'] at hex
            exact ih _ (wsetDev s d') mm W x t' es hwf hW0 hpin hdes hdom hsub hdom' hex
          · rw [if_neg hd] at hex ⊢
            obtain ⟨es0, hee, rfl⟩ := Weff.consEqSome.1 hex
            have hdm := execDomMono _ _ _ _ (execEffExec _ _ _ _ _ hee)
            have hin := fun j (hj : j < n) => hdom' _ (hdm _ (writeBytesDom mm req.pa n w j hj))
            have hacc : accWf req.pa n := accWfWindow W req.pa n hW0 hin
            have hpin2 : tracePin (wwritePost tid s (classify req.access_kind) req.pa n w) es0 :=
              tracePinWrite tid s _ _ _ w es0 hpin
            have hdom2 : bmDomSub (bmWrite mm req.pa n w) W := fun a ha => hdom' _ (hdm _ ha)
            have hdisjw : raccDisj ra rn req.pa n := traceDisjWrite ra rn _ _ _ _ es0 hdes
            have hsub2 : bmSub (bmWrite mm req.pa n w)
                (bmWrite (wflatMem (wwritePost tid s (classify req.access_kind) req.pa n w).wmImg
                  (wwritePost tid s (classify req.access_kind) req.pa n w).wmLog) ra rn wp) := by
              show bmSub _ (bmWrite (wflatMem s.wmImg
                (wwritePost tid s (classify req.access_kind) req.pa n w).wmLog) ra rn wp)
              rw [wflatWrite tid s _ req.pa n w hacc,
                ← writeBytesPatchComm _ ra rn wp req.pa n w hracc hacc hdisjw]
              exact writeBytesMono _ _ _ _ _ hsub
            exact ⟨Or.inl trivial, hacc, hdisjw,
              ih _ _ (bmWrite mm req.pa n w) W x t' es0 (wflatWriteWf _ _ _ _ _ _ hwf hacc) hW0
                hpin2 (traceDisjTail ra rn _ es0 hdes) hdom2 hsub2 hdom' hee⟩
      case barrier b =>
        simp only [execEff] at hex
        obtain ⟨es0, hee, rfl⟩ := Weff.consEqSome.1 hex
        have hpin2 : tracePin (wbarrierPost s b) es0 :=
          tracePinMono s (wbarrierPost s b) es0 rfl (barrierPostLe _ _) (itvPostLe _ _ _)
            (tracePinTail _ _ _ hpin)
        simp only [wstepOkRacy]
        exact ih () (wbarrierPost s b) mm W x t' es0 hwf hW0 hpin2
          (traceDisjTail ra rn _ es0 hdes) hdom hsub hdom' hee
      all_goals first
        | (simp only [execEff, reduceCtorEq] at hex; done)
        | (simp only [execEff] at hex
           simp only [wstepOkRacy]
           exact ih _ s mm W x t' es hwf hW0 hpin hdes hdom hsub hdom' hex)

/-- The instance the phase-`true` half hands it: the confined memory is the
restriction PATCHED at the window. -/
theorem wstepOkRacyFalseOfWindow (tid : Option Nat) (ra : PAddr) (rn : Nat) (rak : AkInfo)
    (Φ : (Nat → BitVec 8) → Prop) (Wp : Prop) (wp : BitVec (8 * rn)) {X : Type} (m : SailM X)
    (s : Wmstate) (W : GSet PAddr) (x : X) (t' : ExecSt) (es : List Weff) :
    accWf ra rn →
    wlogWf s.wmLog →
    (∀ a, a ∈ W → paZ a ≠ 0) →
    -- the window itself is part of the confined footprint
    (∀ j, j < rn → ra + BitVec.ofNat 64 j ∈ W) →
    tracePin s es →
    traceDisj ra rn es →
    bmDomSub t'.mem W →
    execEff m ⟨s.wmRegs, bmWrite (wmemRestrict s W) ra rn wp, s.wmDev⟩ = some (x, t', es) →
    wstepOkRacy tid ra rn rak Φ (raccDisj ra rn) Wp false m s := by
  intro hracc hwf hW0 hwin hpes hdes hdom' hex
  exact wstepOkRacyFalseOfConfined tid ra rn rak Φ Wp wp m hracc s _ W x t' es hwf hW0 hpes hdes
    (writeBytesDomSub _ _ _ _ _ (wmemRestrictDom s W) hwin)
    (writeBytesMono _ _ _ _ _ (wmemRestrictSub s W)) hdom' hex

/-! ## 3. THE PRE-RACY TRACE: what replaces `tracePin` and `traceDisj` -/

/-- PINNEDNESS, DEMANDED ONLY OFF THE WINDOW (deviation 2: `readPinned`, plus
`fetchFresh`). -/
def tracePinOff (s : Wmstate) (ra : PAddr) (rn : Nat) (es : List Weff) : Prop :=
  (∀ (ak : AkInfo) (pa : PAddr) (n : Nat),
    Weff.WEread ak pa n ∈ es → akPins ak = false → raccDisj ra rn pa n →
    ∀ j, j < n → readPinned s ak (WeakInterp.accAddr pa j)) ∧
  fetchFresh es

theorem tracePinOffOfPin (s : Wmstate) (ra : PAddr) (rn : Nat) (es : List Weff) :
    tracePin s es → tracePinOff s ra rn es := by
  rintro ⟨hp, hf⟩
  exact ⟨fun ak pa n hin hnp _ j hj => hp ak pa n hin hnp j hj, hf⟩

theorem tracePinOfOff (s : Wmstate) (ra : PAddr) (rn : Nat) (es : List Weff) :
    traceDisj ra rn es → tracePinOff s ra rn es → tracePin s es := by
  rintro ⟨hr, -⟩ ⟨hp, hf⟩
  exact ⟨fun ak pa n hin hnp j hj => hp ak pa n hin hnp (hr ak pa n hin) j hj, hf⟩

theorem tracePinOffMono (s s' : Wmstate) (ra : PAddr) (rn : Nat) (es : List Weff) :
    s'.wmLog = s.wmLog → wsLe s.wmWs s'.wmWs → s.wmItv ≤ s'.wmItv →
    tracePinOff s ra rn es → tracePinOff s' ra rn es := by
  rintro hl hle hitv ⟨hp, hf⟩
  refine ⟨fun ak pa n hin hnp hd j hj => ?_, hf⟩
  have h0 := hp ak pa n hin hnp hd j hj
  unfold readPinned at h0 ⊢
  by_cases hif : ak.akIfetch = true
  · rw [if_pos hif] at h0 ⊢
    unfold fetchPinned at h0 ⊢
    rw [hl]
    omega
  · rw [if_neg hif] at h0 ⊢
    exact pinnedReadMono s s' _ hl hle h0

theorem tracePinOffTail (s : Wmstate) (ra : PAddr) (rn : Nat) (e : Weff) (es : List Weff) :
    tracePinOff s ra rn (e :: es) → tracePinOff s ra rn es := by
  rintro ⟨hp, -, hf⟩
  exact ⟨fun ak pa n hin => hp ak pa n (List.mem_cons_of_mem _ hin), hf⟩

theorem tracePinOffHead (s : Wmstate) (ra : PAddr) (rn : Nat) (ak : AkInfo) (pa : PAddr)
    (n : Nat) (es : List Weff) :
    tracePinOff s ra rn (.WEread ak pa n :: es) →
    akPins ak = false → raccDisj ra rn pa n →
    ∀ j, j < n → readPinned s ak (WeakInterp.accAddr pa j) :=
  fun hp => hp.1 ak pa n List.mem_cons_self

/-- THE ORDERED HALF.  Before the racy read every read is disjoint from the
window and there is no RAM write at all; at the racy read the phase flips and
the rest is `traceDisj`. -/
def traceRacy (rak : AkInfo) (ra : PAddr) (rn : Nat) : List Weff → Prop
  | [] => True
  | .WEread ak pa n :: es' =>
    (raccDisj ra rn pa n ∧ traceRacy rak ra rn es') ∨
    (ak = rak ∧ pa = ra ∧ n = rn ∧ traceDisj ra rn es')
  | .WEwrite .. :: _ => False
  | .WEbar _ :: es' => traceRacy rak ra rn es'

theorem raccDisjIrrefl (ra : PAddr) (rn : Nat) : 0 < rn → ¬ raccDisj ra rn ra rn := by
  intro hrn h
  unfold raccDisj at h
  omega

theorem traceRacyDisjTail (rak : AkInfo) (ra : PAddr) (rn : Nat) (ak : AkInfo) (pa : PAddr)
    (n : Nat) (es : List Weff) :
    0 < rn → raccDisj ra rn pa n →
    traceRacy rak ra rn (.WEread ak pa n :: es) → traceRacy rak ra rn es := by
  intro hrn hd h
  rcases h with ⟨_, hr⟩ | ⟨_, hpa, hn, _⟩
  · exact hr
  · subst hpa hn
    exact (raccDisjIrrefl _ _ hrn hd).elim

theorem traceRacyWinTail (rak : AkInfo) (ra : PAddr) (rn : Nat) (ak : AkInfo) (pa : PAddr)
    (n : Nat) (es : List Weff) :
    0 < rn → ¬ raccDisj ra rn pa n →
    traceRacy rak ra rn (.WEread ak pa n :: es) →
    ak = rak ∧ pa = ra ∧ n = rn ∧ traceDisj ra rn es := by
  intro _ hnd h
  rcases h with ⟨hd, _⟩ | h
  · exact (hnd hd).elim
  · exact h

/-! ## 4. THE PHASE-`true` PEEL -/

theorem wstepOkRacyTrueOfConfined (tid : Option Nat) (ra : PAddr) (rn : Nat) (rak : AkInfo)
    (Φ : (Nat → BitVec 8) → Prop) (Wp : Prop) {X : Type} (m : SailM X) :
    accWf ra rn →
    0 < rn →
    (∃ w0 : BitVec (8 * rn), Φ (fun j => nthByte w0 j)) →
    ∀ (s : Wmstate) (mm : BMap) (W : GSet PAddr),
      wlogWf s.wmLog →
      (∀ a, a ∈ W → paZ a ≠ 0) →
      -- the window itself is part of the confined footprint
      (∀ j, j < rn → ra + BitVec.ofNat 64 j ∈ W) →
      bmDomSub mm W →
      bmSub mm (wflatMem s.wmImg s.wmLog) →
      -- THE FAMILY: one confined run per `Φ`-satisfying window value
      (∀ w : BitVec (8 * rn), Φ (fun j => nthByte w j) →
        ∃ (x : X) (t' : ExecSt) (es : List Weff),
          execEff m ⟨s.wmRegs, bmWrite mm ra rn w, s.wmDev⟩ = some (x, t', es) ∧
          bmDomSub t'.mem W ∧
          tracePinOff s ra rn es ∧
          traceRacy rak ra rn es) →
      wstepOkRacy tid ra rn rak Φ (raccDisj ra rn) Wp true m s := by
  rintro hracc hrn ⟨w0, hΦ0⟩
  -- the patched memory holds the patch word AT the window
  have hrdw : ∀ (u : BitVec (8 * rn)) (mp : BMap), bmRead (bmWrite mp ra rn u) ra rn = some u :=
    fun u mp => readBytesOfBytes _ ra rn u (fun j hj => writeBytesLookupAt mp ra rn u j hracc hj)
  induction m with
  | pure y => intros; simp only [wstepOkRacy]
  | impure call k ih =>
    intro s mm W hwf hW0 hwin hdom hsub hfam
    cases call with
    | error e => simp only [wstepOkRacy]
    | ok o =>
      cases o
      case regWrite r v =>
        simp only [wstepOkRacy]
        refine ih PUnit.unit (wsetReg s r v) mm W hwf hW0 hwin hdom hsub (fun u hu => ?_)
        obtain ⟨x1, t1, es1, hex1, hd1, hp1, hr1⟩ := hfam u hu
        simp only [execEff] at hex1
        exact ⟨x1, t1, es1, hex1, hd1,
          tracePinOffMono s _ ra rn es1 rfl (wsLeRefl _) (Nat.le_refl _) hp1, hr1⟩
      case memRead n va req =>
        simp only [wstepOkRacy]
        by_cases hd : mmioAcc req.pa n = true
        · -- device: no effect emitted, and the answer does not depend on the patch
          rw [if_pos hd]
          intro wv d' hdr'
          refine ih _ (wsetDev s d') mm W hwf hW0 hwin hdom hsub (fun u hu => ?_)
          obtain ⟨x1, t1, es1, hex1, hd1, hp1, hr1⟩ := hfam u hu
          simp only [execEff, if_pos hd, hdr'] at hex1
          exact ⟨x1, t1, es1, hex1, hd1,
            tracePinOffMono s _ ra rn es1 rfl (wsLeRefl _) (Nat.le_refl _) hp1, hr1⟩
        · rw [if_neg hd]
          -- RAM: the witness run fixes the footprint ...
          obtain ⟨x0, t0, es0, hex0, -, hp0, hr0⟩ := hfam w0 hΦ0
          simp only [execEff, if_neg hd] at hex0
          cases hrb0 : bmRead (bmWrite mm ra rn w0) req.pa n with
          | none => simp only [hrb0] at hex0; cases hex0
          | some v0 =>
            simp only [hrb0] at hex0
            obtain ⟨es1, -, rfl⟩ := Weff.consEqSome.1 hex0
            have hdomp : bmDomSub (bmWrite mm ra rn w0) W := writeBytesDomSub _ _ _ _ _ hdom hwin
            have hin := fun j (hj : j < n) => hdomp _ (readBytesDom _ req.pa n v0 hrb0 j hj)
            have hacc : accWf req.pa n := accWfWindow W req.pa n hW0 hin
            refine ⟨hacc, ?_⟩
            -- ... and its ADDRESS decides which arm this is, for every member at once
            by_cases hdisj : raccDisj ra rn req.pa n
            · -- AWAY FROM THE WINDOW: `wstepOk`'s own arm, at every member
              left
              have hrbmm : bmRead mm req.pa n = some v0 := by
                rw [← readBytesPatchDisj mm ra rn w0 _ n hracc hacc hdisj]; exact hrb0
              have hrbu : ∀ u : BitVec (8 * rn), bmRead (bmWrite mm ra rn u) req.pa n = some v0 :=
                fun u => by rw [readBytesPatchDisj mm ra rn u _ n hracc hacc hdisj]; exact hrbmm
              have hwrb : wreadBytes s (classify req.access_kind) req.pa n (cohTs s req.pa n) =
                  some v0 := by
                rw [wreadBytesReadBytes s _ req.pa n hwf hacc]
                exact readBytesMono _ _ _ _ _ hsub hrbmm
              refine ⟨hdisj, fun hnp j hj => tracePinOffHead s ra rn _ _ _ es1 hp0 hnp hdisj j hj,
                fun w hw => ?_⟩
              rw [hwrb] at hw
              simp only [Option.some.injEq] at hw
              subst hw
              refine ih _ (wreadPost s (classify req.access_kind) req.pa (cohTs s req.pa n)) mm W
                (wlogWfReadPost _ _ _ _ hwf) hW0 hwin hdom
                (by rw [wreadPostImg, wreadPostLog]; exact hsub) (fun u hu => ?_)
              obtain ⟨x2, t2, es2, hex2, hd2, hp2, hr2⟩ := hfam u hu
              simp only [execEff, if_neg hd, hrbu u] at hex2
              obtain ⟨es3, hee2, rfl⟩ := Weff.consEqSome.1 hex2
              refine ⟨x2, t2, es3, ?_, hd2, ?_, traceRacyDisjTail rak ra rn _ _ n es3 hrn hdisj hr2⟩
              · rw [wreadPostRegs, wreadPostDev]; exact hee2
              · exact tracePinOffMono s _ ra rn es3 (wreadPostLog _ _ _ _) (wreadPostWsLe _ _ _ _)
                  (by rw [wreadPostItv]; exact Nat.le_refl _) (tracePinOffTail s ra rn _ es3 hp2)
            · -- THE RACY READ, handed to §2 at `wp := w`
              right
              obtain ⟨hak, hpa, hn, -⟩ := traceRacyWinTail rak ra rn _ _ n es1 hrn hdisj hr0
              subst hpa
              subst hak
              subst hn
              refine ⟨trivial, rfl, rfl, rfl, fun ts w _ hΦw => ?_⟩
              obtain ⟨x2, t2, es2, hex2, hd2, hp2, hr2⟩ := hfam w hΦw
              simp only [execEff, if_neg hd, hrdw w mm] at hex2
              obtain ⟨es3, hee2, rfl⟩ := Weff.consEqSome.1 hex2
              obtain ⟨-, -, -, hdes3⟩ :=
                traceRacyWinTail _ _ _ _ _ _ es3 hrn (raccDisjIrrefl _ _ hrn) hr2
              apply wstepOkRacyFalseOfConfined tid _ _ _ Φ Wp w _ hracc
                (wreadPost s _ _ ts) (bmWrite mm _ _ w) W x2 t2 es3
                (wlogWfReadPost _ _ _ _ hwf) hW0
              · -- the tail is disjoint, so off-window pinnedness IS pinnedness
                exact tracePinMono s _ es3 (wreadPostLog _ _ _ _) (wreadPostWsLe _ _ _ _)
                  (by rw [wreadPostItv]; exact Nat.le_refl _)
                  (tracePinOfOff s _ _ es3 hdes3 (tracePinOffTail s _ _ _ es3 hp2))
              · exact hdes3
              · exact writeBytesDomSub _ _ _ _ _ hdom hwin
              · rw [wreadPostImg, wreadPostLog]; exact writeBytesMono _ _ _ _ _ hsub
              · exact hd2
              · rw [wreadPostRegs, wreadPostDev]; exact hee2
      case memWrite n va req =>
        simp only [wstepOkRacy]
        obtain ⟨x0, t0, es0, hex0, -, -, hr0⟩ := hfam w0 hΦ0
        simp only [execEff] at hex0
        cases hv : req.value with
        | none => simp only [hv] at hex0; cases hex0
        | some v =>
          simp only [hv] at hex0 ⊢
          by_cases hd : mmioAcc req.pa n = true
          · -- a device write emits no effect, so the phase is untouched
            rw [if_pos hd]
            intro d' hdw'
            refine ih _ (wsetDev s d') mm W hwf hW0 hwin hdom hsub (fun u hu => ?_)
            obtain ⟨x1, t1, es1, hex1, hd1, hp1, hr1⟩ := hfam u hu
            simp only [execEff, hv, if_pos hd, hdw'] at hex1
            exact ⟨x1, t1, es1, hex1, hd1,
              tracePinOffMono s _ ra rn es1 rfl (wsLeRefl _) (Nat.le_refl _) hp1, hr1⟩
          · -- A RAM WRITE BEFORE THE RACY READ IS EXCLUDED BY `traceRacy`
            exfalso
            rw [if_neg hd] at hex0
            obtain ⟨es1, -, rfl⟩ := Weff.consEqSome.1 hex0
            simp only [traceRacy] at hr0
      case barrier b =>
        -- no address, so the phase is untouched here too
        simp only [wstepOkRacy]
        refine ih () (wbarrierPost s b) mm W hwf hW0 hwin hdom hsub (fun u hu => ?_)
        obtain ⟨x2, t2, es2, hex2, hd2, hp2, hr2⟩ := hfam u hu
        simp only [execEff] at hex2
        obtain ⟨es3, hee2, rfl⟩ := Weff.consEqSome.1 hex2
        exact ⟨x2, t2, es3, hee2, hd2,
          tracePinOffMono s _ ra rn es3 rfl (barrierPostLe _ _) (itvPostLe _ _ _)
            (tracePinOffTail s ra rn _ es3 hp2), hr2⟩
      all_goals first
        | (obtain ⟨_, _, _, hex0, -⟩ := hfam w0 hΦ0
           simp only [execEff, reduceCtorEq] at hex0; done)
        | (simp only [wstepOkRacy]
           refine ih _ s mm W hwf hW0 hwin hdom hsub (fun u hu => ?_)
           obtain ⟨x1, t1, es1, hex1, hd1, hp1, hr1⟩ := hfam u hu
           simp only [execEff] at hex1
           exact ⟨x1, t1, es1, hex1, hd1, hp1, hr1⟩)

/-- The `wmemRestrict` instance, the shape a certificate carries. -/
theorem wstepOkRacyTrueOfWindow (tid : Option Nat) (ra : PAddr) (rn : Nat) (rak : AkInfo)
    (Φ : (Nat → BitVec 8) → Prop) (Wp : Prop) {X : Type} (m : SailM X) (s : Wmstate)
    (W : GSet PAddr) :
    accWf ra rn →
    0 < rn →
    (∃ w0 : BitVec (8 * rn), Φ (fun j => nthByte w0 j)) →
    wlogWf s.wmLog →
    (∀ a, a ∈ W → paZ a ≠ 0) →
    (∀ j, j < rn → ra + BitVec.ofNat 64 j ∈ W) →
    (∀ w : BitVec (8 * rn), Φ (fun j => nthByte w j) →
      ∃ (x : X) (t' : ExecSt) (es : List Weff),
        execEff m ⟨s.wmRegs, bmWrite (wmemRestrict s W) ra rn w, s.wmDev⟩ = some (x, t', es) ∧
        bmDomSub t'.mem W ∧
        tracePinOff s ra rn es ∧
        traceRacy rak ra rn es) →
    wstepOkRacy tid ra rn rak Φ (raccDisj ra rn) Wp true m s := by
  intro hracc hrn hΦ hwf hW0 hwin hfam
  exact wstepOkRacyTrueOfConfined tid ra rn rak Φ Wp m hracc hrn hΦ s (wmemRestrict s W) W hwf hW0
    hwin (wmemRestrictDom s W) (wmemRestrictSub s W) hfam

/-- THE INHABITATION PREMISE, from what the rule's caller already holds: the
canonical word is admissible, so the filter accepts it. -/
theorem wadmFilterInhabited (s : Wmstate) (rak : AkInfo) (ra : PAddr) (rn : Nat)
    (Φ : (Nat → BitVec 8) → Prop) :
    wadmFilter s rak ra rn Φ →
    (wreadBytes s rak ra rn (cohTs s ra rn)).isSome = true →
    ∃ w0 : BitVec (8 * rn), Φ (fun j => nthByte w0 j) := by
  intro hΦ hs
  cases hw : wreadBytes s rak ra rn (cohTs s ra rn) with
  | none => rw [hw] at hs; cases hs
  | some w =>
    exact ⟨w, hΦ w (wadmOfWreadOk _ _ _ _ _ _ (wreadBytesSpec _ _ _ _ _ _ hw))⟩

end Weak
