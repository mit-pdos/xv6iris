/-
Weak: **the SC mirror with a STALE memory for unpinned reads** (6a).

Rocq: `iris/WeakStale.v` @ xxvzwolszwmp.

The Rocq header, in substance.  `WeakRacy.wstepOkRacy` (with the disjointness parameter at
`wDAny`) can DESCRIBE the walk's blocked trace shape -- the leaf slot read twice in one step,
plain and racy, then exclusive and latest -- but no producer could PRODUCE it: every
`WeakVarCert` producer runs the confined SC interpreter on ONE memory patched with the racy value,
so the CAS re-read (demanded at the coherence-latest word) returns the racy word instead.  The
answer: give the mirror TWO memories, selected per read by the bit the weak machine uses to decide
pinnedness (`staleMem ra rn w ak s := if akPins ak then s.mem else bmWrite s.mem ra rn w`).  A
PLAIN window read sees the patch (the racy word); a PINNED one (the CAS re-read) sees the real
memory (the latest word); off the window the two agree, so no non-window fact changes.

§1 `staleMem`, `execStale` (`WeakCert.execEff` arm for arm, one changed RAM-read arm); §2 the
composition kit; §3 THE TRANSFER both ways (`execStaleOfExecEff`, `execEffOfExecStale`) under
`traceOffWin`; §4 the phase-`false` embedding of `wstepOk`; §5 THE PRODUCER
`wstepOkRacyTrueOfStale` over a `traceStale` family; §6 the second transfer (against the PATCHED
memory, for write-free runs whose pinned reads miss the window); §6b the footprint restriction;
§7 the peel in CPS (`wstepOkRacyK`, its intro and bind rules); §8 phase monotonicity at `W` and
the store-shaped bind; §9 the sequential-window traversals; §10 THE ⇐-BRIDGE: every weak run of a
peeled program is ONE family member's `execStale` run, with the log footprint (`wtraceWonly`)
and the log identity (`wtraceMsgs`) exported.

**Deviations from Rocq.**
1. NAMES: the tree's camelCase (map below).  File-qualified (duplicated-name rule):
   `WeakStale.wtraceWonlyReads`, `WeakStale.barrierPostRelp`, `WeakStale.loadPostBytesRelp`,
   `WeakStale.wreadPostRelp`.  Vocabulary as `Weak/WeakCert.lean` deviations 1-2 and
   `Weak/WeakEff.lean` deviation 1: `MState r m d` ↦ `⟨r, m, d⟩ : ExecSt`, `mem`/`sregs`/`mdev` ↦
   `.mem`/`.regs`/`.dev`, `read_bytes`/`write_bytes` ↦ `bmRead`/`bmWrite`, `mm ⊆ mm2` ↦
   `bmSub mm mm2`, `dom mm ⊆ W` ↦ `bmDomSub mm W`, `a ∈ dom mm` ↦ `(mm a).isSome = true`,
   `dom mm ⊆ dom mm2` ↦ `∀ a, (mm a).isSome = true → (mm2 a).isSome = true`, `is_Some o` ↦
   `o.isSome = true`, `pa_add a j` ↦ `a + BitVec.ofNat 64 j`, `n : N` ↦ `n : Nat` (so `N.to_nat n`
   ↦ `n`), `M X` ↦ `SailM X`, `Defs.bind m f` ↦ `m >>= f`, `Defs.bind0 m n` ↦ `m >>= fun _ => n`,
   `Defs.returnm` ↦ `pure`, `Defs.read_reg`/`write_reg` ↦ `readReg`/`writeReg`, `inl (v, None)` ↦
   `.Ok (v, none)`, `inl None` ↦ `.Ok (some true)`.  `acc_win`: `list_to_set` ↦
   `LawfulSet.ofList`, `≫=` ↦ `List.flatMap`, `seq 0 n` ↦ `List.range n`.  stdpp `Forall` ↦
   `∀ e, e ∈ es → …` (WeakEff deviation 4).
2. `execStale` is Lean's `execEff` arm for arm (its write arm matches on `req.value` first, the MMIO
   test is `mmioAcc`, the trace consing is `Weff.cons`); `wstepOkRacyK` is Lean's `wstepOkRacy` arm
   for arm with `K` at the `pure` leaf (O2 `readPinned` obligation, the `wbarrierPost` barrier arm,
   the `.error` arm `True`, `choose` `False`).
3. O2, THE TRACE PIN (`WeakCert` deviation 3, `WeakVarCert` deviation 2): Lean's `tracePin` and
   `tracePinOff` carry `fetchFresh`, so `tracePinOfOffWin` rebuilds it from `tracePinOff`'s; the
   producer's `tracePinMono`/`tracePinOffMono` steps take the `wmItv` premise (`wreadPostItv`,
   `itvPostLe`).
4. Stage B: the barrier step is `wbarrierPost` (Rocq `wset_ws s (barrier_post …)`); §10 reads its
   flag through `wbarrierPostWs` and `WeakStale.barrierPostRelp` (stated, as in Rocq, of
   `barrierPost`; `fence.i` moves no data view, so `wrelpBar` leaves the flag alone there).
5. O2, THE I-CACHE VIEW IN THE TRANSPORT (`WeakRacy` deviation 4): `wrunExecStaleElimGen` carries
   the extra premise `s0.wmItv ≤ s.wmItv` (what `WeakRacy.wadmDown` needs at an i-cache window);
   `wrunExecStaleElimMsgs` supplies it by reflexivity, so the consumer-facing statements of §10c/d
   are unchanged.
6. O2, THE `ak_coh` ARMS COLLAPSE (`WeakRacy` deviation 4): `wexec` consumes the oracle at every RAM
   read, so `wexecOfExecRacyKseq`/`wrunWexecRacyKseq` cons the chosen timestamps in both read arms;
   the Rocq case splits on `ak_coh` and the use of `wread_coh_ts` (false under O2 for an i-cache
   read unless `|log| ≤ itv`) are gone.  Statements unchanged.
7. The bind kit is proved through the Lean-only bind EQUATION `WeakStale.execStaleBindEq` (the twin
   of `WeakEff.execEffBindEq`, reusing its `effThen`); `execStaleBindNone`/`execStaleBindSome` follow
   from it (Rocq: one induction each).
8. Rocq's `filt_step` Ltac: each arm of the §9 traversals applies the matching `wadmFilter*` lemma
   (`WeakRacy` deviation 6).  The coherent-word step of §10b/d is the Lean-only helper
   `WeakStale.cohWord`.
9. `foldlLoadPostAtRelp`, `WeakStale.loadPostBytesRelp`, `WeakStale.wreadPostRelp` are proved from
   their `WeakInstr` twins; `wwritePostRelp` goes through Lean's `storePostRun` (a relp-neutral
   `ctrlPost` around `storePostBytes`).

**Rocq → Lean name map.**  `stale_mem` `staleMem`, `stale_mem_pins` `staleMemPins`, `stale_mem_unpinned` `staleMemUnpinned`,
`exec_stale` `execStale`, `exec_stale_returnm` `execStaleReturnm`, `exec_stale_read_reg`
`execStaleReadReg`, `exec_stale_write_reg` `execStaleWriteReg`, `exec_stale_bind`
`execStaleBind`, `exec_stale_bind_nil` `execStaleBindNil`, `exec_stale_bind0_nil`
`execStaleBind0Nil`, `exec_stale_bind_cons` `execStaleBindCons`, `exec_stale_bind_None`
`execStaleBindNone`, `exec_stale_bind_Some` `execStaleBindSome`, `trace_off_win` `traceOffWin`,
`trace_off_win_tail` `traceOffWinTail`, `trace_off_win_head` `traceOffWinHead`,
`trace_off_win_of_all` `traceOffWinOfAll`, `exec_stale_of_exec_eff` `execStaleOfExecEff`,
`exec_eff_of_exec_stale` `execEffOfExecStale`, `read_bytes_stale_win` `readBytesStaleWin`,
`wD_any` `wDAny`, `wstep_ok_racy_false_of_wstep_ok` `wstepOkRacyFalseOfWstepOk`, `trace_stale`
`traceStale`, `trace_stale_pin_tail` `traceStalePinTail`, `trace_stale_disj_tail`
`traceStaleDisjTail`, `trace_stale_win` `traceStaleWin`, `trace_pin_of_off_win`
`tracePinOfOffWin`, `wstep_ok_racy_true_of_stale` `wstepOkRacyTrueOfStale`,
`wstep_ok_racy_true_of_stale_window` `wstepOkRacyTrueOfStaleWindow`, `mpatch` `mpatch`,
`mpatch_set_reg` `mpatchSetReg`, `trace_pin_win` `tracePinWin`, `trace_pin_win_tail`
`tracePinWinTail`, `trace_pin_win_head` `tracePinWinHead`, `exec_stale_of_patch_nowrite`
`execStaleOfPatchNowrite`, `exec_stale_of_patch_id` `execStaleOfPatchId`, `acc_win` `accWin`,
`acc_win_in` `accWinIn`, `acc_win_inv` `accWinInv`, `trace_rdom` `traceRdom`, `trace_wdom`
`traceWdom`, `trace_rdom_tail` `traceRdomTail`, `trace_rdom_head` `traceRdomHead`,
`trace_rdom_mono` `traceRdomMono`, `trace_wdom_tail` `traceWdomTail`, `trace_wdom_head`
`traceWdomHead`, `read_bytes_restrict` `readBytesRestrict`, `exec_stale_restrict`
`execStaleRestrict`, `wstep_ok_racy_k` `wstepOkRacyK`, `wstep_ok_racy_k_triv` `wstepOkRacyKTriv`,
`wstep_ok_racy_k_of_run` `wstepOkRacyKOfRun`, `wstep_ok_racy_k_bind` `wstepOkRacyKBind`,
`wstep_ok_racy_bind` `wstepOkRacyBind`, `wstep_ok_racy_phase_mono_gen` `wstepOkRacyPhaseMonoGen`,
`wstep_ok_racy_phase_mono` `wstepOkRacyPhaseMono`, `wstep_ok_racy_k_of_run_false`
`wstepOkRacyKOfRunFalse`, `wstep_ok_racy_bind_false` `wstepOkRacyBindFalse`,
`wexec_of_exec_racy_kseq` `wexecOfExecRacyKseq`, `wrun_wexec_racy_kseq` `wrunWexecRacyKseq`,
`wexec_of_exec_racy_seq2` `wexecOfExecRacySeq2`, `wrun_wexec_racy_seq2` `wrunWexecRacySeq2`,
`wstep_ok_racy_k_seq_intro` `wstepOkRacyKSeqIntro`, `wtrace_wonly` `wtraceWonly`,
`wtrace_wonly_tail` `wtraceWonlyTail`, `wtrace_wonly_head` `wtraceWonlyHead`,
`wtrace_wonly_reads` `WeakStale.wtraceWonlyReads`, `msg_writesb_wwrite_ne` `msgWritesbWwriteNe`,
`latest_ts_write_post_ne` `latestTsWritePostNe`, `wm_class_rp` `wmClassRp`, `wm_class_of_rp`
`wmClassOfRp`, `wm_class_rp_latest` `wmClassRpLatest`, `wrelp_bar` `wrelpBar`, `wrelp_write`
`wrelpWrite`, `barrier_post_relp` `WeakStale.barrierPostRelp`, `foldl_load_post_at_relp`
`foldlLoadPostAtRelp`, `load_post_bytes_relp` `WeakStale.loadPostBytesRelp`, `wset_ws_relp`
`wsetWsRelp`, `wread_post_relp` `WeakStale.wreadPostRelp`, `store_post_bytes_relp`
`storePostBytesRelp`, `wwrite_post_relp` `wwritePostRelp`, `wtrace_msgs` `wtraceMsgs`,
`wtrace_msgs_reads_nil` `wtraceMsgsReadsNil`, `wtrace_msgs_snoc_write` `wtraceMsgsSnocWrite`,
`wrun_exec_stale_elim_off` `wrunExecStaleElimOff`, `wrun_exec_stale_elim_gen`
`wrunExecStaleElimGen`, `wrun_exec_stale_elim_msgs` `wrunExecStaleElimMsgs`,
`wrun_exec_stale_elim` `wrunExecStaleElim`, `wexec_exec_stale_elim` `wexecExecStaleElim`,
`wrun_exec_stale_elim_const_msgs` `wrunExecStaleElimConstMsgs`, `wrun_exec_stale_elim_const`
`wrunExecStaleElimConst`.
Lean-only (2): `WeakStale.execStaleBindEq`, `WeakStale.cohWord` (90 Rocq declarations, 92 Lean).

**Dropped:** nothing.

**Statements checked** (by hand, against Rocq): all; the changed ones are deviations 2-6.
-/
import Weak.WeakVarCert
import Weak.WeakEff

namespace Weak

open Iris Iris.Std
open MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open Sail.ArchSem (FreeM)
open LeanRV64D LeanRV64D.Functions

/-! ## 1. The stale memory and the mirror -/

/-- The memory a read of kind `ak` sees: the real one if the weak machine PINS the read, the
memory patched at the window otherwise. -/
def staleMem (ra : PAddr) (rn : Nat) (w : BitVec (8 * rn)) (ak : AkInfo) (s : ExecSt) : BMap :=
  if akPins ak then s.mem else bmWrite s.mem ra rn w

theorem staleMemPins (ra : PAddr) (rn : Nat) (w : BitVec (8 * rn)) (ak : AkInfo) (s : ExecSt) :
    akPins ak = true → staleMem ra rn w ak s = s.mem := by
  intro h; simp only [staleMem, h, ↓reduceIte]

theorem staleMemUnpinned (ra : PAddr) (rn : Nat) (w : BitVec (8 * rn)) (ak : AkInfo) (s : ExecSt) :
    akPins ak = false → staleMem ra rn w ak s = bmWrite s.mem ra rn w := by
  intro h; simp only [staleMem, h, Bool.false_eq_true, ↓reduceIte]

/-- `WeakCert.execEff`, arm for arm; the ONLY difference is which memory the RAM read arm
reads. -/
def execStale (ra : PAddr) (rn : Nat) (w : BitVec (8 * rn)) {X : Type} :
    SailM X → ExecSt → Option (X × ExecSt × List Weff)
  | .pure x, s => some (x, s, [])
  | .impure (.error _) _, _ => none
  | .impure (.ok o) k, s =>
    match o, k with
    | .regRead r, k => execStale ra rn w (k (s.regs r)) s
    | .regWrite r v, k => execStale ra rn w (k PUnit.unit) (s.setReg r v)
    | .memRead n _ req, k =>
      if mmioAcc req.pa n then
        match devRead s.dev req.pa n with
        | some (v, d') => execStale ra rn w (k (.Ok (v, none))) (s.setDev d')
        | none => none
      else
        match bmRead (staleMem ra rn w (classify req.access_kind) s) req.pa n with
        | some v =>
          Weff.cons (.WEread (classify req.access_kind) req.pa n)
            (execStale ra rn w (k (.Ok (v, none))) s)
        | none => none
    | .memWrite n _ req, k =>
      match req.value with
      | none => none
      | some v =>
        if mmioAcc req.pa n then
          match devWrite s.dev req.pa n v with
          | some d' => execStale ra rn w (k (.Ok (some true))) (s.setDev d')
          | none => none
        else
          Weff.cons (.WEwrite (classify req.access_kind) req.pa n v)
            (execStale ra rn w (k (.Ok (some true))) (s.setMem (bmWrite s.mem req.pa n v)))
    | .barrier b, k => Weff.cons (.WEbar b) (execStale ra rn w (k ()) s)
    | .cacheOp _, k => execStale ra rn w (k ()) s
    | .tlbi _, k => execStale ra rn w (k ()) s
    | .translationStart _, k => execStale ra rn w (k ()) s
    | .translationEnd _, k => execStale ra rn w (k ()) s
    | .takeException _, k => execStale ra rn w (k ()) s
    | .returnException _, k => execStale ra rn w (k ()) s
    | .cycleCount, k => execStale ra rn w (k ()) s
    | .getCycleCount, k => execStale ra rn w (k (0 : Nat)) s
    | .message _, k => execStale ra rn w (k ()) s
    | .instrAnnounce _ _, k => execStale ra rn w (k ()) s
    | .branchAnnounce _ _, k => execStale ra rn w (k ()) s
    | .choose _, _ => none
    | .readRam .., _ => none
    | .writeRam .., _ => none

/-! ## 2. The composition kit (`WeakEff` §§1–2, restated) -/

section kit
variable (ra : PAddr) (rn : Nat) (w : BitVec (8 * rn))

theorem execStaleReturnm {X : Type} (x : X) (s : ExecSt) :
    execStale ra rn w (pure x : SailM X) s = some (x, s, []) := rfl

theorem execStaleReadReg (r : Register) (s : ExecSt) :
    execStale ra rn w (readReg r) s = some (s.regs r, s, []) := rfl

theorem execStaleWriteReg (r : Register) (v : RegisterType r) (s : ExecSt) :
    execStale ra rn w (writeReg r v) s = some (PUnit.unit, s.setReg r v, []) := rfl

/-- The bind law of the mirror (Lean-only, the twin of `WeakEff.execEffBindEq`). -/
theorem WeakStale.execStaleBindEq {X Y : Type} (m : SailM X) (f : X → SailM Y) :
    ∀ s, execStale ra rn w (m >>= f) s =
      effThen (execStale ra rn w m s) (fun x s1 => execStale ra rn w (f x) s1) := by
  induction m with
  | pure x =>
    intro s
    show execStale ra rn w (f x) s = effThen (some (x, s, [])) _
    cases h : execStale ra rn w (f x) s with
    | none => simp [effThen, h]
    | some p =>
      obtain ⟨y, s2, es'⟩ := p
      simp [effThen, h]
  | impure call k ih =>
    intro s
    cases call with
    | error e => rfl
    | ok o =>
      show execStale ra rn w (FreeM.impure (.ok o) (fun v => k v >>= f)) s = _
      cases o
      case memRead n va req =>
        by_cases hm : mmioAcc req.pa n = true
        · simp only [execStale, hm, ↓reduceIte]
          cases devRead s.dev req.pa n with
          | none => rfl
          | some p =>
            obtain ⟨v, d'⟩ := p
            exact ih _ _
        · simp only [execStale, hm, Bool.false_eq_true, ↓reduceIte]
          cases bmRead (staleMem ra rn w (classify req.access_kind) s) req.pa n with
          | none => rfl
          | some v => exact (congrArg (Weff.cons _) (ih _ _)).trans (effThenCons _ _ _).symm
      case memWrite n va req =>
        cases hv : req.value with
        | none => simp only [execStale, hv]; rfl
        | some v =>
          by_cases hm : mmioAcc req.pa n = true
          · simp only [execStale, hv, hm, ↓reduceIte]
            cases devWrite s.dev req.pa n v with
            | none => rfl
            | some d' => exact ih _ _
          · simp only [execStale, hv, hm, Bool.false_eq_true, ↓reduceIte]
            exact (congrArg (Weff.cons _) (ih _ _)).trans (effThenCons _ _ _).symm
      case barrier b =>
        simp only [execStale]
        exact (congrArg (Weff.cons _) (ih _ _)).trans (effThenCons _ _ _).symm
      all_goals first | rfl | exact ih _ _ | (simp only [execStale]; exact ih _ _)

theorem execStaleBind {X Y : Type} (m : SailM X) (f : X → SailM Y) :
    ∀ (s : ExecSt) (v : X) (st : ExecSt) (es : List Weff) (y : Y) (s' : ExecSt) (es' : List Weff),
      execStale ra rn w m s = some (v, st, es) →
      execStale ra rn w (f v) st = some (y, s', es') →
      execStale ra rn w (m >>= f) s = some (y, s', es ++ es') := by
  intro s v st es y s' es' hm hf
  rw [WeakStale.execStaleBindEq, hm]
  simp only [effThen, hf]

/-- The EQUALITY form. -/
theorem execStaleBindNil {X Y : Type} (m : SailM X) (f : X → SailM Y) (s : ExecSt) (v : X)
    (st : ExecSt) :
    execStale ra rn w m s = some (v, st, []) →
    execStale ra rn w (m >>= f) s = execStale ra rn w (f v) st := by
  intro hm
  rw [WeakStale.execStaleBindEq, hm]
  cases h : execStale ra rn w (f v) st with
  | none => simp [effThen, h]
  | some p =>
    obtain ⟨y, s2, es'⟩ := p
    simp [effThen, h]

theorem execStaleBind0Nil {Y : Type} (m : SailM Unit) (n : SailM Y) (s : ExecSt) (u : Unit)
    (st : ExecSt) :
    execStale ra rn w m s = some (u, st, []) →
    execStale ra rn w (m >>= fun _ => n) s = execStale ra rn w n st :=
  execStaleBindNil ra rn w m (fun _ => n) s u st

theorem execStaleBindCons {X Y : Type} (m : SailM X) (f : X → SailM Y) (s : ExecSt) (v : X)
    (st : ExecSt) (e : Weff) (y : Y) (s' : ExecSt) (es' : List Weff) :
    execStale ra rn w m s = some (v, st, [e]) →
    execStale ra rn w (f v) st = some (y, s', es') →
    execStale ra rn w (m >>= f) s = some (y, s', e :: es') :=
  fun hm hf => execStaleBind ra rn w m f s v st [e] y s' es' hm hf

/-- The composite cannot succeed where the tail does not. -/
theorem execStaleBindNone {X Y : Type} (m : SailM X) (f : X → SailM Y) (v : X) (st : ExecSt) :
    execStale ra rn w (f v) st = none →
    ∀ s es, execStale ra rn w m s = some (v, st, es) →
      execStale ra rn w (m >>= f) s = none := by
  intro hf s es hm
  rw [WeakStale.execStaleBindEq, hm]
  simp only [effThen, hf]

theorem execStaleBindSome {X Y : Type} (m : SailM X) (f : X → SailM Y) (s : ExecSt) (v : X)
    (st : ExecSt) (es : List Weff) :
    execStale ra rn w m s = some (v, st, es) →
    execStale ra rn w (m >>= f) s =
      match execStale ra rn w (f v) st with
      | some (y, s', es') => some (y, s', es ++ es')
      | none => none := by
  intro hm
  rw [WeakStale.execStaleBindEq, hm]
  rfl

end kit

/-! ## 3. THE TRANSFER -/

def traceOffWin (ra : PAddr) (rn : Nat) (es : List Weff) : Prop :=
  ∀ (ak : AkInfo) (pa : PAddr) (n : Nat), Weff.WEread ak pa n ∈ es → akPins ak = false →
    accWf pa n ∧ raccDisj ra rn pa n

theorem traceOffWinTail (ra : PAddr) (rn : Nat) (e : Weff) (es : List Weff) :
    traceOffWin ra rn (e :: es) → traceOffWin ra rn es :=
  fun h ak pa n hin => h ak pa n (List.mem_cons_of_mem _ hin)

theorem traceOffWinHead (ra : PAddr) (rn : Nat) (ak : AkInfo) (pa : PAddr) (n : Nat)
    (es : List Weff) :
    traceOffWin ra rn (.WEread ak pa n :: es) → akPins ak = false →
    accWf pa n ∧ raccDisj ra rn pa n :=
  fun h => h ak pa n List.mem_cons_self

theorem traceOffWinOfAll (ra : PAddr) (rn : Nat) (es : List Weff) :
    (∀ ak pa n, Weff.WEread ak pa n ∈ es → accWf pa n ∧ raccDisj ra rn pa n) →
    traceOffWin ra rn es :=
  fun h ak pa n hin _ => h ak pa n hin

/-- THE TRANSFER, forward: an `execEff` fact about a window-free run is an `execStale` fact. -/
theorem execStaleOfExecEff (ra : PAddr) (rn : Nat) (w : BitVec (8 * rn)) {X : Type} (m : SailM X) :
    accWf ra rn →
    ∀ s x t es, execEff m s = some (x, t, es) → traceOffWin ra rn es →
      execStale ra rn w m s = some (x, t, es) := by
  intro hracc
  induction m with
  | pure y => intro s x t es h _; exact h
  | impure call k ih =>
    intro s x t es h hoff
    cases call with
    | error e => simp [execEff] at h
    | ok o =>
      cases o
      case memRead n va req =>
        simp only [execEff] at h
        simp only [execStale]
        by_cases hd : mmioAcc req.pa n = true
        · rw [if_pos hd] at h ⊢
          cases hdr : devRead s.dev req.pa n with
          | none => simp only [hdr] at h; cases h
          | some p =>
            obtain ⟨w0, d0⟩ := p
            simp only [hdr] at h ⊢
            exact ih _ _ _ _ _ h hoff
        · rw [if_neg hd] at h ⊢
          cases hrb : bmRead s.mem req.pa n with
          | none => simp only [hrb] at h; cases h
          | some v0 =>
            simp only [hrb] at h
            obtain ⟨es0, h0, rfl⟩ := Weff.consEqSome.1 h
            have hmem : bmRead (staleMem ra rn w (classify req.access_kind) s) req.pa n =
                some v0 := by
              cases hpin : akPins (classify req.access_kind) with
              | true => rw [staleMemPins _ _ _ _ _ hpin]; exact hrb
              | false =>
                rw [staleMemUnpinned _ _ _ _ _ hpin]
                obtain ⟨hacc, hdisj⟩ := traceOffWinHead ra rn _ _ _ _ hoff hpin
                rw [readBytesPatchDisj _ ra rn w _ n hracc hacc hdisj]; exact hrb
            simp only [hmem]
            exact Weff.consEqSome.2 ⟨es0, ih _ _ _ _ _ h0 (traceOffWinTail _ _ _ _ hoff), rfl⟩
      case memWrite n va req =>
        simp only [execEff] at h
        simp only [execStale]
        cases hv : req.value with
        | none => simp only [hv] at h; cases h
        | some v =>
          simp only [hv] at h ⊢
          by_cases hd : mmioAcc req.pa n = true
          · rw [if_pos hd] at h ⊢
            cases hdw : devWrite s.dev req.pa n v with
            | none => simp only [hdw] at h; cases h
            | some d0 =>
              simp only [hdw] at h ⊢
              exact ih _ _ _ _ _ h hoff
          · rw [if_neg hd] at h ⊢
            obtain ⟨es0, h0, rfl⟩ := Weff.consEqSome.1 h
            exact Weff.consEqSome.2 ⟨es0, ih _ _ _ _ _ h0 (traceOffWinTail _ _ _ _ hoff), rfl⟩
      case barrier b =>
        simp only [execEff] at h
        simp only [execStale]
        obtain ⟨es0, h0, rfl⟩ := Weff.consEqSome.1 h
        exact Weff.consEqSome.2 ⟨es0, ih _ _ _ _ _ h0 (traceOffWinTail _ _ _ _ hoff), rfl⟩
      all_goals first
        | (simp only [execEff, reduceCtorEq] at h; done)
        | (simp only [execEff] at h; simp only [execStale]; exact ih _ _ _ _ _ h hoff)

/-- THE TRANSFER, backward: the direction the PRODUCER uses. -/
theorem execEffOfExecStale (ra : PAddr) (rn : Nat) (w : BitVec (8 * rn)) {X : Type} (m : SailM X) :
    accWf ra rn →
    ∀ s x t es, execStale ra rn w m s = some (x, t, es) → traceOffWin ra rn es →
      execEff m s = some (x, t, es) := by
  intro hracc
  induction m with
  | pure y => intro s x t es h _; exact h
  | impure call k ih =>
    intro s x t es h hoff
    cases call with
    | error e => simp [execStale] at h
    | ok o =>
      cases o
      case memRead n va req =>
        simp only [execStale] at h
        simp only [execEff]
        by_cases hd : mmioAcc req.pa n = true
        · rw [if_pos hd] at h ⊢
          cases hdr : devRead s.dev req.pa n with
          | none => simp only [hdr] at h; cases h
          | some p =>
            obtain ⟨w0, d0⟩ := p
            simp only [hdr] at h ⊢
            exact ih _ _ _ _ _ h hoff
        · rw [if_neg hd] at h ⊢
          cases hrb : bmRead (staleMem ra rn w (classify req.access_kind) s) req.pa n with
          | none => simp only [hrb] at h; cases h
          | some v0 =>
            simp only [hrb] at h
            obtain ⟨es0, h0, rfl⟩ := Weff.consEqSome.1 h
            have hmem : bmRead s.mem req.pa n = some v0 := by
              cases hpin : akPins (classify req.access_kind) with
              | true => rw [staleMemPins _ _ _ _ _ hpin] at hrb; exact hrb
              | false =>
                rw [staleMemUnpinned _ _ _ _ _ hpin] at hrb
                obtain ⟨hacc, hdisj⟩ := traceOffWinHead ra rn _ _ _ _ hoff hpin
                rw [readBytesPatchDisj _ ra rn w _ n hracc hacc hdisj] at hrb; exact hrb
            simp only [hmem]
            exact Weff.consEqSome.2 ⟨es0, ih _ _ _ _ _ h0 (traceOffWinTail _ _ _ _ hoff), rfl⟩
      case memWrite n va req =>
        simp only [execStale] at h
        simp only [execEff]
        cases hv : req.value with
        | none => simp only [hv] at h; cases h
        | some v =>
          simp only [hv] at h ⊢
          by_cases hd : mmioAcc req.pa n = true
          · rw [if_pos hd] at h ⊢
            cases hdw : devWrite s.dev req.pa n v with
            | none => simp only [hdw] at h; cases h
            | some d0 =>
              simp only [hdw] at h ⊢
              exact ih _ _ _ _ _ h hoff
          · rw [if_neg hd] at h ⊢
            obtain ⟨es0, h0, rfl⟩ := Weff.consEqSome.1 h
            exact Weff.consEqSome.2 ⟨es0, ih _ _ _ _ _ h0 (traceOffWinTail _ _ _ _ hoff), rfl⟩
      case barrier b =>
        simp only [execStale] at h
        simp only [execEff]
        obtain ⟨es0, h0, rfl⟩ := Weff.consEqSome.1 h
        exact Weff.consEqSome.2 ⟨es0, ih _ _ _ _ _ h0 (traceOffWinTail _ _ _ _ hoff), rfl⟩
      all_goals first
        | (simp only [execStale, reduceCtorEq] at h; done)
        | (simp only [execStale] at h; simp only [execEff]; exact ih _ _ _ _ _ h hoff)

/-- THE ONE ARM THAT IS NOT A TRANSFER: an unpinned read OF the window returns the racy word. -/
theorem readBytesStaleWin (ra : PAddr) (rn : Nat) (w : BitVec (8 * rn)) (ak : AkInfo) (s : ExecSt) :
    accWf ra rn → akPins ak = false → bmRead (staleMem ra rn w ak s) ra rn = some w := by
  intro hracc hpin
  rw [staleMemUnpinned _ _ _ _ _ hpin]
  exact readBytesOfBytes _ ra rn w (fun j hj => writeBytesLookupAt s.mem ra rn w j hracc hj)

/-! ## 4. The phase-`false` embedding -/

def wDAny : PAddr → Nat → Prop := fun _ _ => True

theorem wstepOkRacyFalseOfWstepOk (tid : Option Nat) (ra : PAddr) (rn : Nat) (rak : AkInfo)
    (Φ : (Nat → BitVec 8) → Prop) (Wp : Prop) {X : Type} (m : SailM X) :
    ∀ s, wstepOk tid m s → wstepOkRacy tid ra rn rak Φ wDAny Wp false m s := by
  induction m with
  | pure y => intros; simp only [wstepOkRacy]
  | impure call k ih =>
    intro s hok
    cases call with
    | error e => simp only [wstepOkRacy]
    | ok o =>
      cases o
      case memRead n va req =>
        simp only [wstepOk] at hok
        simp only [wstepOkRacy]
        by_cases hd : mmioAcc req.pa n = true
        · rw [if_pos hd] at hok ⊢
          intro v d' hdr
          exact ih _ _ (hok v d' hdr)
        · rw [if_neg hd] at hok ⊢
          obtain ⟨hacc, hpin, hk⟩ := hok
          exact ⟨hacc, Or.inl ⟨trivial, hpin, fun v hv => ih _ _ (hk v hv)⟩⟩
      case memWrite n va req =>
        simp only [wstepOk] at hok
        simp only [wstepOkRacy]
        by_cases hd : mmioAcc req.pa n = true
        · rw [if_pos hd] at hok ⊢
          cases hv : req.value with
          | none => trivial
          | some v =>
            simp only [hv] at hok ⊢
            intro d' hdw
            exact ih _ _ (hok d' hdw)
        · rw [if_neg hd] at hok ⊢
          obtain ⟨hacc, hk⟩ := hok
          refine ⟨by simp, hacc, trivial, ?_⟩
          cases hv : req.value with
          | none => trivial
          | some v =>
            simp only [hv] at hk ⊢
            exact ih _ _ hk
      case choose => simp only [wstepOk] at hok
      all_goals first
        | (simp only [wstepOkRacy]; done)
        | (simp only [wstepOk] at hok; simp only [wstepOkRacy]; exact ih _ _ hok)

/-! ## 5. THE PRODUCER -/

/-- The `WeakVarCert.traceRacy` analogue: before the racy read every read is PINNED (any
address) or disjoint, and there is no RAM write; after it, only the unpinned reads must stay
off the window. -/
def traceStale (rak : AkInfo) (ra : PAddr) (rn : Nat) : List Weff → Prop
  | [] => True
  | .WEread ak pa n :: es' =>
    (akPins ak = true ∧ traceStale rak ra rn es') ∨
    (akPins ak = false ∧ raccDisj ra rn pa n ∧ traceStale rak ra rn es') ∨
    (ak = rak ∧ pa = ra ∧ n = rn ∧ traceOffWin ra rn es')
  | .WEwrite .. :: _ => False
  | .WEbar _ :: es' => traceStale rak ra rn es'

theorem traceStalePinTail (rak : AkInfo) (ra : PAddr) (rn : Nat) (ak : AkInfo) (pa : PAddr)
    (n : Nat) (es : List Weff) :
    akPins rak = false → akPins ak = true →
    traceStale rak ra rn (.WEread ak pa n :: es) → traceStale rak ra rn es := by
  intro hrk hpin h
  rcases h with ⟨_, ht⟩ | ⟨hnp, -⟩ | ⟨hak, -⟩
  · exact ht
  · rw [hnp] at hpin; cases hpin
  · rw [hak, hrk] at hpin; cases hpin

theorem traceStaleDisjTail (rak : AkInfo) (ra : PAddr) (rn : Nat) (ak : AkInfo) (pa : PAddr)
    (n : Nat) (es : List Weff) :
    0 < rn → akPins ak = false → raccDisj ra rn pa n →
    traceStale rak ra rn (.WEread ak pa n :: es) → traceStale rak ra rn es := by
  intro hrn hnp hd h
  rcases h with ⟨hpin, _⟩ | ⟨_, _, ht⟩ | ⟨_, hpa, hn, _⟩
  · rw [hnp] at hpin; cases hpin
  · exact ht
  · subst hpa hn
    exact (raccDisjIrrefl _ _ hrn hd).elim

theorem traceStaleWin (rak : AkInfo) (ra : PAddr) (rn : Nat) (ak : AkInfo) (pa : PAddr)
    (n : Nat) (es : List Weff) :
    akPins ak = false → ¬ raccDisj ra rn pa n →
    traceStale rak ra rn (.WEread ak pa n :: es) →
    ak = rak ∧ pa = ra ∧ n = rn ∧ traceOffWin ra rn es := by
  intro hnp hnd h
  rcases h with ⟨hpin, _⟩ | ⟨_, hd, _⟩ | h
  · rw [hnp] at hpin; cases hpin
  · exact (hnd hd).elim
  · exact h

/-- Off the window, `tracePinOff`'s weakening IS `WeakCert.tracePin`. -/
theorem tracePinOfOffWin (s : Wmstate) (ra : PAddr) (rn : Nat) (es : List Weff) :
    traceOffWin ra rn es → tracePinOff s ra rn es → tracePin s es := by
  rintro hd ⟨hp, hf⟩
  exact ⟨fun ak pa n hin hnp j hj => hp ak pa n hin hnp (hd ak pa n hin hnp).2 j hj, hf⟩

theorem wstepOkRacyTrueOfStale (tid : Option Nat) (ra : PAddr) (rn : Nat) (rak : AkInfo)
    (Φ : (Nat → BitVec 8) → Prop) (Wp : Prop) {X : Type} (m : SailM X) :
    accWf ra rn →
    0 < rn →
    akPins rak = false →
    (∃ w0 : BitVec (8 * rn), Φ (fun j => nthByte w0 j)) →
    ∀ (s : Wmstate) (mm : BMap) (W : GSet PAddr),
      wlogWf s.wmLog →
      (∀ a, a ∈ W → paZ a ≠ 0) →
      (∀ j, j < rn → ra + BitVec.ofNat 64 j ∈ W) →
      bmDomSub mm W →
      bmSub mm (wflatMem s.wmImg s.wmLog) →
      (∀ w : BitVec (8 * rn), Φ (fun j => nthByte w j) →
        ∃ (x : X) (t' : ExecSt) (es : List Weff),
          execStale ra rn w m ⟨s.wmRegs, mm, s.wmDev⟩ = some (x, t', es) ∧
          bmDomSub t'.mem W ∧
          tracePinOff s ra rn es ∧
          traceStale rak ra rn es) →
      wstepOkRacy tid ra rn rak Φ wDAny Wp true m s := by
  rintro hracc hrn hrk ⟨w0, hΦ0⟩
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
        simp only [execStale] at hex1
        exact ⟨x1, t1, es1, hex1, hd1,
          tracePinOffMono s _ ra rn es1 rfl (wsLeRefl _) (Nat.le_refl _) hp1, hr1⟩
      case memRead n va req =>
        simp only [wstepOkRacy]
        by_cases hd : mmioAcc req.pa n = true
        · rw [if_pos hd]
          intro wv d' hdr'
          refine ih _ (wsetDev s d') mm W hwf hW0 hwin hdom hsub (fun u hu => ?_)
          obtain ⟨x1, t1, es1, hex1, hd1, hp1, hr1⟩ := hfam u hu
          simp only [execStale, if_pos hd, hdr'] at hex1
          exact ⟨x1, t1, es1, hex1, hd1,
            tracePinOffMono s _ ra rn es1 rfl (wsLeRefl _) (Nat.le_refl _) hp1, hr1⟩
        · rw [if_neg hd]
          obtain ⟨x0, t0, es0, hex0, -, hp0, hr0⟩ := hfam w0 hΦ0
          simp only [execStale, if_neg hd] at hex0
          cases hpin : akPins (classify req.access_kind) with
          | true =>
            -- PINNED (the CAS re-read): every member reads the REAL memory
            simp only [staleMemPins _ _ _ _ _ hpin] at hex0
            cases hrb0 : bmRead mm req.pa n with
            | none => simp only [hrb0] at hex0; cases hex0
            | some v0 =>
              simp only [hrb0] at hex0
              obtain ⟨es1, -, rfl⟩ := Weff.consEqSome.1 hex0
              have hin := fun j (hj : j < n) => hdom _ (readBytesDom mm req.pa n v0 hrb0 j hj)
              have hacc : accWf req.pa n := accWfWindow W req.pa n hW0 hin
              have hwrb : wreadBytes s (classify req.access_kind) req.pa n (cohTs s req.pa n) =
                  some v0 := by
                rw [wreadBytesReadBytes s _ req.pa n hwf hacc]
                exact readBytesMono _ _ _ _ _ hsub hrb0
              refine ⟨hacc, Or.inl ⟨trivial, (fun hnp => by cases hnp), fun v hv => ?_⟩⟩
              rw [hwrb] at hv
              simp only [Option.some.injEq] at hv
              subst hv
              refine ih _ (wreadPost s (classify req.access_kind) req.pa (cohTs s req.pa n)) mm W
                (wlogWfReadPost _ _ _ _ hwf) hW0 hwin hdom
                (by rw [wreadPostImg, wreadPostLog]; exact hsub) (fun u hu => ?_)
              obtain ⟨x2, t2, es2, hex2, hd2, hp2, hr2⟩ := hfam u hu
              simp only [execStale, if_neg hd, staleMemPins _ _ _ _ _ hpin, hrb0] at hex2
              obtain ⟨es3, hee2, rfl⟩ := Weff.consEqSome.1 hex2
              refine ⟨x2, t2, es3, ?_, hd2, ?_, traceStalePinTail rak ra rn _ _ n es3 hrk hpin hr2⟩
              · rw [wreadPostRegs, wreadPostDev]; exact hee2
              · exact tracePinOffMono s _ ra rn es3 (wreadPostLog _ _ _ _) (wreadPostWsLe _ _ _ _)
                  (by rw [wreadPostItv]; exact Nat.le_refl _) (tracePinOffTail s ra rn _ es3 hp2)
          | false =>
            simp only [staleMemUnpinned _ _ _ _ _ hpin] at hex0
            cases hrb0 : bmRead (bmWrite mm ra rn w0) req.pa n with
            | none => simp only [hrb0] at hex0; cases hex0
            | some v0 =>
              simp only [hrb0] at hex0
              obtain ⟨es1, -, rfl⟩ := Weff.consEqSome.1 hex0
              have hdomp : bmDomSub (bmWrite mm ra rn w0) W :=
                writeBytesDomSub _ _ _ _ _ hdom hwin
              have hin := fun j (hj : j < n) => hdomp _ (readBytesDom _ req.pa n v0 hrb0 j hj)
              have hacc : accWf req.pa n := accWfWindow W req.pa n hW0 hin
              refine ⟨hacc, ?_⟩
              by_cases hdisj : raccDisj ra rn req.pa n
              · -- UNPINNED, OFF the window: `wstepOk`'s own arm
                left
                have hrbmm : bmRead mm req.pa n = some v0 := by
                  rw [← readBytesPatchDisj mm ra rn w0 _ n hracc hacc hdisj]; exact hrb0
                have hrbu : ∀ u : BitVec (8 * rn), bmRead (bmWrite mm ra rn u) req.pa n = some v0 :=
                  fun u => by rw [readBytesPatchDisj mm ra rn u _ n hracc hacc hdisj]; exact hrbmm
                have hwrb : wreadBytes s (classify req.access_kind) req.pa n (cohTs s req.pa n) =
                    some v0 := by
                  rw [wreadBytesReadBytes s _ req.pa n hwf hacc]
                  exact readBytesMono _ _ _ _ _ hsub hrbmm
                refine ⟨trivial,
                  fun _ j hj => tracePinOffHead s ra rn _ _ _ es1 hp0 hpin hdisj j hj,
                  fun v hv => ?_⟩
                rw [hwrb] at hv
                simp only [Option.some.injEq] at hv
                subst hv
                refine ih _ (wreadPost s (classify req.access_kind) req.pa (cohTs s req.pa n)) mm W
                  (wlogWfReadPost _ _ _ _ hwf) hW0 hwin hdom
                  (by rw [wreadPostImg, wreadPostLog]; exact hsub) (fun u hu => ?_)
                obtain ⟨x2, t2, es2, hex2, hd2, hp2, hr2⟩ := hfam u hu
                simp only [execStale, if_neg hd, staleMemUnpinned _ _ _ _ _ hpin, hrbu u] at hex2
                obtain ⟨es3, hee2, rfl⟩ := Weff.consEqSome.1 hex2
                refine ⟨x2, t2, es3, ?_, hd2, ?_,
                  traceStaleDisjTail rak ra rn _ _ n es3 hrn hpin hdisj hr2⟩
                · rw [wreadPostRegs, wreadPostDev]; exact hee2
                · exact tracePinOffMono s _ ra rn es3 (wreadPostLog _ _ _ _)
                    (wreadPostWsLe _ _ _ _) (by rw [wreadPostItv]; exact Nat.le_refl _)
                    (tracePinOffTail s ra rn _ es3 hp2)
              · -- THE RACY READ: the member indexed by `w` returns `w`, and its tail is an
                -- ordinary confined run at the UNPATCHED memory (§3 backward, then §4)
                right
                obtain ⟨hak, hpa, hn, -⟩ := traceStaleWin rak ra rn _ _ n es1 hpin hdisj hr0
                subst hpa
                subst hak
                subst hn
                refine ⟨trivial, rfl, rfl, rfl, fun ts w _ hΦw => ?_⟩
                obtain ⟨x2, t2, es2, hex2, hd2, hp2, hr2⟩ := hfam w hΦw
                simp only [execStale, if_neg hd, staleMemUnpinned _ _ _ _ _ hpin, hrdw w mm] at hex2
                obtain ⟨es3, hee2, rfl⟩ := Weff.consEqSome.1 hex2
                obtain ⟨-, -, -, hoff3⟩ :=
                  traceStaleWin _ _ _ _ _ _ es3 hpin (raccDisjIrrefl _ _ hrn) hr2
                apply wstepOkRacyFalseOfWstepOk
                refine (wstepEffConfinedPin tid _ (wreadPost s _ _ ts) mm W x2 t2 es3
                  (wlogWfReadPost _ _ _ _ hwf) hW0 ?_ hdom
                  (by rw [wreadPostImg, wreadPostLog]; exact hsub) hd2 ?_).1
                · exact tracePinMono s _ es3 (wreadPostLog _ _ _ _) (wreadPostWsLe _ _ _ _)
                    (by rw [wreadPostItv]; exact Nat.le_refl _)
                    (tracePinOfOffWin s _ _ es3 hoff3 (tracePinOffTail s _ _ _ es3 hp2))
                · rw [wreadPostRegs, wreadPostDev]
                  exact execEffOfExecStale _ _ w _ hracc _ _ _ _ hee2 hoff3
      case memWrite n va req =>
        simp only [wstepOkRacy]
        obtain ⟨x0, t0, es0, hex0, -, -, hr0⟩ := hfam w0 hΦ0
        simp only [execStale] at hex0
        cases hv : req.value with
        | none => simp only [hv] at hex0; cases hex0
        | some v =>
          simp only [hv] at hex0 ⊢
          by_cases hd : mmioAcc req.pa n = true
          · rw [if_pos hd]
            intro d' hdw'
            refine ih _ (wsetDev s d') mm W hwf hW0 hwin hdom hsub (fun u hu => ?_)
            obtain ⟨x1, t1, es1, hex1, hd1, hp1, hr1⟩ := hfam u hu
            simp only [execStale, hv, if_pos hd, hdw'] at hex1
            exact ⟨x1, t1, es1, hex1, hd1,
              tracePinOffMono s _ ra rn es1 rfl (wsLeRefl _) (Nat.le_refl _) hp1, hr1⟩
          · -- a RAM write before the racy read is REFUTED by the trace
            exfalso
            rw [if_neg hd] at hex0
            obtain ⟨es1, -, rfl⟩ := Weff.consEqSome.1 hex0
            simp only [traceStale] at hr0
      case barrier b =>
        simp only [wstepOkRacy]
        refine ih () (wbarrierPost s b) mm W hwf hW0 hwin hdom hsub (fun u hu => ?_)
        obtain ⟨x2, t2, es2, hex2, hd2, hp2, hr2⟩ := hfam u hu
        simp only [execStale] at hex2
        obtain ⟨es3, hee2, rfl⟩ := Weff.consEqSome.1 hex2
        exact ⟨x2, t2, es3, hee2, hd2,
          tracePinOffMono s _ ra rn es3 rfl (barrierPostLe _ _) (itvPostLe _ _ _)
            (tracePinOffTail s ra rn _ es3 hp2), hr2⟩
      all_goals first
        | (obtain ⟨_, _, _, hex0, -⟩ := hfam w0 hΦ0
           simp only [execStale, reduceCtorEq] at hex0; done)
        | (simp only [wstepOkRacy]
           refine ih _ s mm W hwf hW0 hwin hdom hsub (fun u hu => ?_)
           obtain ⟨x1, t1, es1, hex1, hd1, hp1, hr1⟩ := hfam u hu
           simp only [execStale] at hex1
           exact ⟨x1, t1, es1, hex1, hd1, hp1, hr1⟩)

/-- The `wmemRestrict` instance -- the shape a certificate carries. -/
theorem wstepOkRacyTrueOfStaleWindow (tid : Option Nat) (ra : PAddr) (rn : Nat) (rak : AkInfo)
    (Φ : (Nat → BitVec 8) → Prop) (Wp : Prop) {X : Type} (m : SailM X) (s : Wmstate)
    (W : GSet PAddr) :
    accWf ra rn →
    0 < rn →
    akPins rak = false →
    (∃ w0 : BitVec (8 * rn), Φ (fun j => nthByte w0 j)) →
    wlogWf s.wmLog →
    (∀ a, a ∈ W → paZ a ≠ 0) →
    (∀ j, j < rn → ra + BitVec.ofNat 64 j ∈ W) →
    (∀ w : BitVec (8 * rn), Φ (fun j => nthByte w j) →
      ∃ (x : X) (t' : ExecSt) (es : List Weff),
        execStale ra rn w m ⟨s.wmRegs, wmemRestrict s W, s.wmDev⟩ = some (x, t', es) ∧
        bmDomSub t'.mem W ∧
        tracePinOff s ra rn es ∧
        traceStale rak ra rn es) →
    wstepOkRacy tid ra rn rak Φ wDAny Wp true m s := by
  intro hracc hrn hrk hΦ hwf hW0 hwin hfam
  exact wstepOkRacyTrueOfStale tid ra rn rak Φ Wp m hracc hrn hrk hΦ s (wmemRestrict s W) W hwf
    hW0 hwin (wmemRestrictDom s W) (wmemRestrictSub s W) hfam

/-! ## 6. THE SECOND TRANSFER: the mirror against the PATCHED memory -/

def mpatch (ra : PAddr) (rn : Nat) (w : BitVec (8 * rn)) (s : ExecSt) : ExecSt :=
  ⟨s.regs, bmWrite s.mem ra rn w, s.dev⟩

theorem mpatchSetReg (ra : PAddr) (rn : Nat) (w : BitVec (8 * rn)) (s : ExecSt) (r : Register)
    (v : RegisterType r) : mpatch ra rn w (s.setReg r v) = (mpatch ra rn w s).setReg r v := rfl

/-- `traceOffWin`'s mirror image: the PINNED reads must miss the window here. -/
def tracePinWin (ra : PAddr) (rn : Nat) (es : List Weff) : Prop :=
  ∀ (ak : AkInfo) (pa : PAddr) (n : Nat), Weff.WEread ak pa n ∈ es → akPins ak = true →
    accWf pa n ∧ raccDisj ra rn pa n

theorem tracePinWinTail (ra : PAddr) (rn : Nat) (e : Weff) (es : List Weff) :
    tracePinWin ra rn (e :: es) → tracePinWin ra rn es :=
  fun h ak pa n hin => h ak pa n (List.mem_cons_of_mem _ hin)

theorem tracePinWinHead (ra : PAddr) (rn : Nat) (ak : AkInfo) (pa : PAddr) (n : Nat)
    (es : List Weff) :
    tracePinWin ra rn (.WEread ak pa n :: es) → akPins ak = true →
    accWf pa n ∧ raccDisj ra rn pa n :=
  fun h => h ak pa n List.mem_cons_self

theorem execStaleOfPatchNowrite (ra : PAddr) (rn : Nat) (w : BitVec (8 * rn)) {X : Type}
    (m : SailM X) :
    accWf ra rn →
    ∀ s x T es,
      execEff m (mpatch ra rn w s) = some (x, T, es) →
      nowriteTrace es →
      tracePinWin ra rn es →
      execStale ra rn w m s = some (x, ⟨T.regs, s.mem, T.dev⟩, es) ∧
      T = mpatch ra rn w ⟨T.regs, s.mem, T.dev⟩ := by
  intro hracc
  induction m with
  | pure y =>
    intro s x T es h _ _
    simp only [execEff, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨rfl, rfl⟩
  | impure call k ih =>
    intro s x T es h hnw hpw
    cases call with
    | error e => simp [execEff] at h
    | ok o =>
      cases o
      case regWrite r v =>
        simp only [execEff] at h
        exact ih _ (s.setReg r v) _ _ _ h hnw hpw
      case memRead n va req =>
        simp only [execEff, mpatch] at h
        by_cases hd : mmioAcc req.pa n = true
        · rw [if_pos hd] at h
          cases hdr : devRead s.dev req.pa n with
          | none => simp only [hdr] at h; cases h
          | some p =>
            obtain ⟨v0, d'⟩ := p
            simp only [hdr] at h
            obtain ⟨hst, hpt⟩ := ih _ (s.setDev d') _ _ _ h hnw hpw
            refine ⟨?_, hpt⟩
            simp only [execStale, if_pos hd, hdr]
            exact hst
        · rw [if_neg hd] at h
          cases hrb : bmRead (bmWrite s.mem ra rn w) req.pa n with
          | none => simp only [hrb] at h; cases h
          | some v0 =>
            simp only [hrb] at h
            obtain ⟨es0, h0, rfl⟩ := Weff.consEqSome.1 h
            have hmem : bmRead (staleMem ra rn w (classify req.access_kind) s) req.pa n =
                some v0 := by
              cases hpin : akPins (classify req.access_kind) with
              | true =>
                rw [staleMemPins _ _ _ _ _ hpin]
                obtain ⟨hacc, hdisj⟩ := tracePinWinHead ra rn _ _ _ _ hpw hpin
                rw [← readBytesPatchDisj s.mem ra rn w _ n hracc hacc hdisj]; exact hrb
              | false => rw [staleMemUnpinned _ _ _ _ _ hpin]; exact hrb
            obtain ⟨hst, hpt⟩ := ih _ s _ _ _ h0 (nowriteTraceConsInv _ _ hnw).2
              (tracePinWinTail _ _ _ _ hpw)
            refine ⟨?_, hpt⟩
            simp only [execStale, if_neg hd, hmem]
            exact Weff.consEqSome.2 ⟨_, hst, rfl⟩
      case memWrite n va req =>
        simp only [execEff, mpatch] at h
        cases hv : req.value with
        | none => simp only [hv] at h; cases h
        | some v =>
          simp only [hv] at h
          by_cases hd : mmioAcc req.pa n = true
          · rw [if_pos hd] at h
            cases hdw : devWrite s.dev req.pa n v with
            | none => simp only [hdw] at h; cases h
            | some d' =>
              simp only [hdw] at h
              obtain ⟨hst, hpt⟩ := ih _ (s.setDev d') _ _ _ h hnw hpw
              refine ⟨?_, hpt⟩
              simp only [execStale, hv, if_pos hd, hdw]
              exact hst
          · -- the RAM arm is excluded by `nowriteTrace`
            exfalso
            rw [if_neg hd] at h
            obtain ⟨es0, -, rfl⟩ := Weff.consEqSome.1 h
            have := (nowriteTraceConsInv _ _ hnw).1
            simp [weffNowrite] at this
      case barrier b =>
        simp only [execEff] at h
        obtain ⟨es0, h0, rfl⟩ := Weff.consEqSome.1 h
        obtain ⟨hst, hpt⟩ := ih _ s _ _ _ h0 (nowriteTraceConsInv _ _ hnw).2
          (tracePinWinTail _ _ _ _ hpw)
        refine ⟨?_, hpt⟩
        simp only [execStale]
        exact Weff.consEqSome.2 ⟨_, hst, rfl⟩
      all_goals first
        | (simp only [execEff, reduceCtorEq] at h; done)
        | (simp only [execEff] at h
           obtain ⟨hst, hpt⟩ := ih _ s _ _ _ h hnw hpw
           exact ⟨by simp only [execStale]; exact hst, hpt⟩)

/-- The shape the walk uses: a sub-run that leaves the patched state alone leaves the real one
alone too. -/
theorem execStaleOfPatchId (ra : PAddr) (rn : Nat) (w : BitVec (8 * rn)) {X : Type} (m : SailM X)
    (s : ExecSt) (x : X) (es : List Weff) :
    accWf ra rn →
    execEff m (mpatch ra rn w s) = some (x, mpatch ra rn w s, es) →
    nowriteTrace es →
    tracePinWin ra rn es →
    execStale ra rn w m s = some (x, s, es) := by
  intro hracc hex hnw hpw
  exact (execStaleOfPatchNowrite ra rn w m hracc s x _ es hex hnw hpw).1

/-! ## 6b. THE FOOTPRINT RESTRICTION -/

/-- THE BYTE FOOTPRINT of a list of `n`-byte accesses. -/
def accWin (l : List PAddr) (n : Nat) : GSet PAddr :=
  LawfulSet.ofList (l.flatMap (fun a => (List.range n).map (fun j => a + BitVec.ofNat 64 j)))

theorem accWinIn (l : List PAddr) (n : Nat) (a : PAddr) (j : Nat) :
    a ∈ l → j < n → a + BitVec.ofNat 64 j ∈ accWin l n := by
  intro ha hj
  unfold accWin
  rw [elemOfListToSet]
  simp only [List.mem_flatMap, List.mem_map, List.mem_range]
  exact ⟨a, ha, j, hj, rfl⟩

theorem accWinInv (l : List PAddr) (n : Nat) (b : PAddr) :
    b ∈ accWin l n → ∃ (a : PAddr) (j : Nat), a ∈ l ∧ j < n ∧ b = a + BitVec.ofNat 64 j := by
  intro h
  unfold accWin at h
  rw [elemOfListToSet] at h
  simp only [List.mem_flatMap, List.mem_map, List.mem_range] at h
  obtain ⟨a, ha, j, hj, rfl⟩ := h
  exact ⟨a, j, ha, hj, rfl⟩

/-- Every byte of every READ of the trace is in the confined map ... -/
def traceRdom (mm : BMap) (es : List Weff) : Prop :=
  ∀ (ak : AkInfo) (pa : PAddr) (n : Nat), Weff.WEread ak pa n ∈ es →
    ∀ j, j < n → (mm (pa + BitVec.ofNat 64 j)).isSome = true

/-- ... and every byte of every WRITE is in the window. -/
def traceWdom (W : GSet PAddr) (es : List Weff) : Prop :=
  ∀ (ak : AkInfo) (pa : PAddr) (n : Nat) (v : BitVec (8 * n)), Weff.WEwrite ak pa n v ∈ es →
    ∀ j, j < n → pa + BitVec.ofNat 64 j ∈ W

theorem traceRdomTail (mm : BMap) (e : Weff) (es : List Weff) :
    traceRdom mm (e :: es) → traceRdom mm es :=
  fun h ak pa n hin => h ak pa n (List.mem_cons_of_mem _ hin)

theorem traceRdomHead (mm : BMap) (ak : AkInfo) (pa : PAddr) (n : Nat) (es : List Weff) :
    traceRdom mm (.WEread ak pa n :: es) →
    ∀ j, j < n → (mm (pa + BitVec.ofNat 64 j)).isSome = true :=
  fun h => h ak pa n List.mem_cons_self

theorem traceRdomMono (mm mm2 : BMap) (es : List Weff) :
    (∀ a, (mm a).isSome = true → (mm2 a).isSome = true) → traceRdom mm es → traceRdom mm2 es :=
  fun hd h ak pa n hin j hj => hd _ (h ak pa n hin j hj)

theorem traceWdomTail (W : GSet PAddr) (e : Weff) (es : List Weff) :
    traceWdom W (e :: es) → traceWdom W es :=
  fun h ak pa n v hin => h ak pa n v (List.mem_cons_of_mem _ hin)

theorem traceWdomHead (W : GSet PAddr) (ak : AkInfo) (pa : PAddr) (n : Nat) (v : BitVec (8 * n))
    (es : List Weff) :
    traceWdom W (.WEwrite ak pa n v :: es) → ∀ j, j < n → pa + BitVec.ofNat 64 j ∈ W :=
  fun h => h ak pa n v List.mem_cons_self

/-- `WeakCert.readBytesMono`'s converse under a footprint hypothesis. -/
theorem readBytesRestrict (mm mm2 : BMap) (pa : PAddr) (n : Nat) (v : BitVec (8 * n)) :
    bmSub mm mm2 → bmRead mm2 pa n = some v →
    (∀ j, j < n → (mm (pa + BitVec.ofNat 64 j)).isSome = true) →
    bmRead mm pa n = some v := by
  intro hsub hr hin
  apply readBytesOfBytes
  intro j hj
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 (hin j hj)
  have h2 := bmRead_spec mm2 pa n v hr j hj
  rw [hsub _ _ hb] at h2
  rw [hb, h2]

theorem execStaleRestrict (ra : PAddr) (rn : Nat) (w : BitVec (8 * rn)) {X : Type} (m : SailM X) :
    ∀ (s : ExecSt) (mm : BMap) (W : GSet PAddr) (x : X) (t' : ExecSt) (es : List Weff),
      execStale ra rn w m s = some (x, t', es) →
      bmSub mm s.mem →
      bmDomSub mm W →
      traceRdom mm es →
      traceWdom W es →
      ∃ t'' : ExecSt,
        execStale ra rn w m ⟨s.regs, mm, s.dev⟩ = some (x, t'', es) ∧
        t''.regs = t'.regs ∧ t''.dev = t'.dev ∧ bmSub t''.mem t'.mem ∧ bmDomSub t''.mem W := by
  induction m with
  | pure y =>
    intro s mm W x t' es h hsub hdom _ _
    simp only [execStale, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨⟨s.regs, mm, s.dev⟩, rfl, rfl, rfl, hsub, hdom⟩
  | impure call k ih =>
    intro s mm W x t' es h hsub hdom hrd hwd
    cases call with
    | error e => simp [execStale] at h
    | ok o =>
      cases o
      case regWrite r v =>
        simp only [execStale] at h
        exact ih _ (s.setReg r v) mm W x t' es h hsub hdom hrd hwd
      case memRead n va req =>
        simp only [execStale] at h
        by_cases hd : mmioAcc req.pa n = true
        · rw [if_pos hd] at h
          cases hdr : devRead s.dev req.pa n with
          | none => simp only [hdr] at h; cases h
          | some p =>
            obtain ⟨v0, d'⟩ := p
            simp only [hdr] at h
            obtain ⟨t'', hex'', hrest⟩ := ih _ (s.setDev d') mm W x t' es h hsub hdom hrd hwd
            refine ⟨t'', ?_, hrest⟩
            simp only [execStale, if_pos hd, hdr]
            exact hex''
        · rw [if_neg hd] at h
          cases hrb : bmRead (staleMem ra rn w (classify req.access_kind) s) req.pa n with
          | none => simp only [hrb] at h; cases h
          | some v0 =>
            simp only [hrb] at h
            obtain ⟨es0, h0, rfl⟩ := Weff.consEqSome.1 h
            have hrb' : bmRead (staleMem ra rn w (classify req.access_kind) ⟨s.regs, mm, s.dev⟩)
                req.pa n = some v0 := by
              cases hpin : akPins (classify req.access_kind) with
              | true =>
                rw [staleMemPins _ _ _ _ _ hpin] at hrb ⊢
                exact readBytesRestrict mm s.mem _ _ _ hsub hrb (traceRdomHead mm _ _ n es0 hrd)
              | false =>
                rw [staleMemUnpinned _ _ _ _ _ hpin] at hrb ⊢
                exact readBytesRestrict (bmWrite mm ra rn w) (bmWrite s.mem ra rn w) _ _ _
                  (writeBytesMono _ _ _ _ _ hsub) hrb
                  (fun j hj => writeBytesDomMono mm ra rn w _ (traceRdomHead mm _ _ n es0 hrd j hj))
            obtain ⟨t'', hex'', hrest⟩ := ih _ s mm W x t' es0 h0 hsub hdom
              (traceRdomTail _ _ _ hrd) (traceWdomTail _ _ _ hwd)
            refine ⟨t'', ?_, hrest⟩
            simp only [execStale, if_neg hd, hrb']
            exact Weff.consEqSome.2 ⟨_, hex'', rfl⟩
      case memWrite n va req =>
        simp only [execStale] at h
        cases hv : req.value with
        | none => simp only [hv] at h; cases h
        | some v =>
          simp only [hv] at h
          by_cases hd : mmioAcc req.pa n = true
          · rw [if_pos hd] at h
            cases hdw : devWrite s.dev req.pa n v with
            | none => simp only [hdw] at h; cases h
            | some d' =>
              simp only [hdw] at h
              obtain ⟨t'', hex'', hrest⟩ := ih _ (s.setDev d') mm W x t' es h hsub hdom hrd hwd
              refine ⟨t'', ?_, hrest⟩
              simp only [execStale, hv, if_pos hd, hdw]
              exact hex''
          · rw [if_neg hd] at h
            obtain ⟨es0, h0, rfl⟩ := Weff.consEqSome.1 h
            have hwin := traceWdomHead W _ _ n v es0 hwd
            obtain ⟨t'', hex'', hrest⟩ := ih _ (s.setMem (bmWrite s.mem req.pa n v))
              (bmWrite mm req.pa n v) W x t' es0 h0 (writeBytesMono _ _ _ _ _ hsub)
              (writeBytesDomSub _ _ _ _ _ hdom hwin)
              (traceRdomMono _ _ _ (writeBytesDomMono mm _ n v) (traceRdomTail _ _ _ hrd))
              (traceWdomTail _ _ _ hwd)
            refine ⟨t'', ?_, hrest⟩
            simp only [execStale, hv, if_neg hd]
            exact Weff.consEqSome.2 ⟨_, hex'', rfl⟩
      case barrier b =>
        simp only [execStale] at h
        obtain ⟨es0, h0, rfl⟩ := Weff.consEqSome.1 h
        obtain ⟨t'', hex'', hrest⟩ := ih _ s mm W x t' es0 h0 hsub hdom
          (traceRdomTail _ _ _ hrd) (traceWdomTail _ _ _ hwd)
        refine ⟨t'', ?_, hrest⟩
        simp only [execStale]
        exact Weff.consEqSome.2 ⟨_, hex'', rfl⟩
      all_goals first
        | (simp only [execStale, reduceCtorEq] at h; done)
        | (simp only [execStale] at h
           obtain ⟨t'', hex'', hrest⟩ := ih _ s mm W x t' es h hsub hdom hrd hwd
           exact ⟨t'', by simp only [execStale]; exact hex'', hrest⟩)

/-! ## 7. THE PEEL, IN CPS -/

def wstepOkRacyK (tid : Option Nat) (ra : PAddr) (rn : Nat) (rak : AkInfo)
    (Φ : (Nat → BitVec 8) → Prop) (D : PAddr → Nat → Prop) (W : Prop) {X : Type} :
    Bool → SailM X → Wmstate → (X → Wmstate → Bool → Prop) → Prop
  | b, .pure y, s, K => K y s b
  | _, .impure (.error _) _, _, _ => True
  | b, .impure (.ok o) k, s, K =>
    match o, k with
    | .regRead r, k => wstepOkRacyK tid ra rn rak Φ D W b (k (s.wmRegs r)) s K
    | .regWrite r v, k => wstepOkRacyK tid ra rn rak Φ D W b (k PUnit.unit) (wsetReg s r v) K
    | .memRead n _ req, k =>
      if mmioAcc req.pa n then
        ∀ w d', devRead s.wmDev req.pa n = some (w, d') →
          wstepOkRacyK tid ra rn rak Φ D W b (k (.Ok (w, none))) (wsetDev s d') K
      else
        accWf req.pa n ∧
        ((D req.pa n ∧
           (akPins (classify req.access_kind) = false →
             ∀ j, j < n → readPinned s (classify req.access_kind) (WeakInterp.accAddr req.pa j)) ∧
           (∀ w, wreadBytes s (classify req.access_kind) req.pa n (cohTs s req.pa n) = some w →
             wstepOkRacyK tid ra rn rak Φ D W b (k (.Ok (w, none)))
               (wreadPost s (classify req.access_kind) req.pa (cohTs s req.pa n)) K)) ∨
          (b = true ∧ req.pa = ra ∧ n = rn ∧ classify req.access_kind = rak ∧
           (∀ ts w, wreadBytes s (classify req.access_kind) req.pa n ts = some w →
             Φ (fun j => nthByte w j) →
             wstepOkRacyK tid ra rn rak Φ D W false (k (.Ok (w, none)))
               (wreadPost s (classify req.access_kind) req.pa ts) K)))
    | .memWrite n _ req, k =>
      if mmioAcc req.pa n then
        match req.value with
        | some v =>
          ∀ d', devWrite s.wmDev req.pa n v = some d' →
            wstepOkRacyK tid ra rn rak Φ D W b (k (.Ok (some true))) (wsetDev s d') K
        | none => True
      else
        (b = false ∨ W) ∧ accWf req.pa n ∧ D req.pa n ∧
        (match req.value with
         | some v =>
           wstepOkRacyK tid ra rn rak Φ D W false (k (.Ok (some true)))
             (wwritePost tid s (classify req.access_kind) req.pa n v) K
         | none => True)
    | .barrier bk, k => wstepOkRacyK tid ra rn rak Φ D W b (k ()) (wbarrierPost s bk) K
    | .instrAnnounce _ _, k => wstepOkRacyK tid ra rn rak Φ D W b (k ()) s K
    | .branchAnnounce _ _, k => wstepOkRacyK tid ra rn rak Φ D W b (k ()) s K
    | .cacheOp _, k => wstepOkRacyK tid ra rn rak Φ D W b (k ()) s K
    | .tlbi _, k => wstepOkRacyK tid ra rn rak Φ D W b (k ()) s K
    | .takeException _, k => wstepOkRacyK tid ra rn rak Φ D W b (k ()) s K
    | .returnException _, k => wstepOkRacyK tid ra rn rak Φ D W b (k ()) s K
    | .translationStart _, k => wstepOkRacyK tid ra rn rak Φ D W b (k ()) s K
    | .translationEnd _, k => wstepOkRacyK tid ra rn rak Φ D W b (k ()) s K
    | .cycleCount, k => wstepOkRacyK tid ra rn rak Φ D W b (k ()) s K
    | .message _, k => wstepOkRacyK tid ra rn rak Φ D W b (k ()) s K
    | .getCycleCount, k => wstepOkRacyK tid ra rn rak Φ D W b (k (0 : Nat)) s K
    | .choose _, _ => False
    | .readRam .., _ => True
    | .writeRam .., _ => True

/-- The trivial continuation IS the peel. -/
theorem wstepOkRacyKTriv (tid : Option Nat) (ra : PAddr) (rn : Nat) (rak : AkInfo)
    (Φ : (Nat → BitVec 8) → Prop) (D : PAddr → Nat → Prop) (W : Prop) (b : Bool) {X : Type}
    (m : SailM X) (s : Wmstate) :
    wstepOkRacyK tid ra rn rak Φ D W b m s (fun _ _ _ => True) ↔
      wstepOkRacy tid ra rn rak Φ D W b m s := by
  induction m generalizing b s with
  | pure y => simp only [wstepOkRacyK, wstepOkRacy]
  | impure call k ih =>
    cases call with
    | error e => simp only [wstepOkRacyK, wstepOkRacy]
    | ok o =>
      cases o
      case memRead n va req =>
        simp only [wstepOkRacyK, wstepOkRacy]
        by_cases hd : mmioAcc req.pa n = true
        · simp only [hd, ↓reduceIte, ih]
        · simp only [hd, Bool.false_eq_true, ↓reduceIte, ih]
      case memWrite n va req =>
        simp only [wstepOkRacyK, wstepOkRacy]
        cases req.value <;> by_cases hd : mmioAcc req.pa n = true <;>
          simp only [hd, ↓reduceIte, Bool.false_eq_true, ih]
      all_goals simp only [wstepOkRacyK, wstepOkRacy, ih]

/-- THE INTRODUCTION RULE: a peel plus a fact about every reachable state is a peel in CPS. -/
theorem wstepOkRacyKOfRun (tid : Option Nat) (ra : PAddr) (rn : Nat) (rak : AkInfo)
    (Φ : (Nat → BitVec 8) → Prop) (D : PAddr → Nat → Prop) (W : Prop) (b : Bool) {X : Type}
    (m : SailM X) (s : Wmstate) (K : X → Wmstate → Bool → Prop) :
    wstepOkRacy tid ra rn rak Φ D W b m s →
    (∀ x s', wrun tid m s x s' → ∀ b', K x s' b') →
    wstepOkRacyK tid ra rn rak Φ D W b m s K := by
  induction m generalizing b s with
  | pure y =>
    intro _ hK
    exact hK y s ⟨rfl, rfl⟩ b
  | impure call k ih =>
    intro hok hK
    cases call with
    | error e => simp only [wstepOkRacyK]
    | ok o =>
      cases o
      case memRead n va req =>
        simp only [wstepOkRacy] at hok
        simp only [wstepOkRacyK]
        by_cases hd : mmioAcc req.pa n = true
        · rw [if_pos hd] at hok ⊢
          intro w d' hdr
          refine ih _ _ _ (hok w d' hdr) (fun x s' hrun => hK x s' ?_)
          simp only [wrun, if_pos hd, hdr]
          exact hrun
        · rw [if_neg hd] at hok ⊢
          obtain ⟨hacc, hor⟩ := hok
          refine ⟨hacc, ?_⟩
          rcases hor with ⟨hdisj, hpin, hk⟩ | ⟨hb, hpa, hn, hak, hk⟩
          · refine Or.inl ⟨hdisj, hpin, fun w hw => ih _ _ _ (hk w hw) (fun x s' hrun => hK x s' ?_)⟩
            simp only [wrun, if_neg hd]
            exact ⟨w, cohTs s req.pa n, wreadBytesSpec _ _ _ _ _ _ hw, hrun⟩
          · refine Or.inr ⟨hb, hpa, hn, hak, fun ts w hw hΦ =>
              ih _ _ _ (hk ts w hw hΦ) (fun x s' hrun => hK x s' ?_)⟩
            simp only [wrun, if_neg hd]
            exact ⟨w, ts, wreadBytesSpec _ _ _ _ _ _ hw, hrun⟩
      case memWrite n va req =>
        simp only [wstepOkRacy] at hok
        simp only [wstepOkRacyK]
        by_cases hd : mmioAcc req.pa n = true
        · rw [if_pos hd] at hok ⊢
          cases hv : req.value with
          | none => trivial
          | some v =>
            simp only [hv] at hok ⊢
            intro d' hdw
            refine ih _ _ _ (hok d' hdw) (fun x s' hrun => hK x s' ?_)
            simp only [wrun, if_pos hd, hv, hdw]
            exact hrun
        · rw [if_neg hd] at hok ⊢
          obtain ⟨hb, hacc, hdisj, hk⟩ := hok
          refine ⟨hb, hacc, hdisj, ?_⟩
          cases hv : req.value with
          | none => trivial
          | some v =>
            simp only [hv] at hk ⊢
            refine ih _ _ _ hk (fun x s' hrun => hK x s' ?_)
            simp only [wrun, if_neg hd, hv]
            exact hrun
      case choose => simp only [wstepOkRacy] at hok
      all_goals first
        | (simp only [wstepOkRacyK]; done)
        | (simp only [wstepOkRacy] at hok
           simp only [wstepOkRacyK]
           refine ih _ _ _ hok (fun x s' hrun => hK x s' ?_)
           simp only [wrun]
           exact hrun)

/-- THE BIND RULE. -/
theorem wstepOkRacyKBind (tid : Option Nat) (ra : PAddr) (rn : Nat) (rak : AkInfo)
    (Φ : (Nat → BitVec 8) → Prop) (D : PAddr → Nat → Prop) (W : Prop) (b : Bool) {X Y : Type}
    (m : SailM X) (f : X → SailM Y) (s : Wmstate) (K : Y → Wmstate → Bool → Prop) :
    wstepOkRacyK tid ra rn rak Φ D W b m s
      (fun x s' b' => wstepOkRacyK tid ra rn rak Φ D W b' (f x) s' K) →
    wstepOkRacyK tid ra rn rak Φ D W b (m >>= f) s K := by
  induction m generalizing b s with
  | pure y => intro hok; exact hok
  | impure call k ih =>
    intro hok
    rw [bindNext]
    cases call with
    | error e => simp only [wstepOkRacyK]
    | ok o =>
      cases o
      case memRead n va req =>
        simp only [wstepOkRacyK] at hok ⊢
        by_cases hd : mmioAcc req.pa n = true
        · rw [if_pos hd] at hok ⊢
          exact fun w d' hdr => ih _ _ _ (hok w d' hdr)
        · rw [if_neg hd] at hok ⊢
          obtain ⟨hacc, hor⟩ := hok
          refine ⟨hacc, ?_⟩
          rcases hor with ⟨hdisj, hpin, hk⟩ | ⟨hb, hpa, hn, hak, hk⟩
          · exact Or.inl ⟨hdisj, hpin, fun w hw => ih _ _ _ (hk w hw)⟩
          · exact Or.inr ⟨hb, hpa, hn, hak, fun ts w hw hΦ => ih _ _ _ (hk ts w hw hΦ)⟩
      case memWrite n va req =>
        simp only [wstepOkRacyK] at hok ⊢
        by_cases hd : mmioAcc req.pa n = true
        · rw [if_pos hd] at hok ⊢
          cases hv : req.value with
          | none => trivial
          | some v =>
            simp only [hv] at hok ⊢
            exact fun d' hdw => ih _ _ _ (hok d' hdw)
        · rw [if_neg hd] at hok ⊢
          obtain ⟨hb, hacc, hdisj, hk⟩ := hok
          refine ⟨hb, hacc, hdisj, ?_⟩
          cases hv : req.value with
          | none => trivial
          | some v =>
            simp only [hv] at hk ⊢
            exact ih _ _ _ hk
      case choose => simp only [wstepOkRacyK] at hok
      all_goals first
        | (simp only [wstepOkRacyK]; done)
        | (simp only [wstepOkRacyK] at hok ⊢; exact ih _ _ _ hok)

/-- THE FORM A LEAF USES. -/
theorem wstepOkRacyBind (tid : Option Nat) (ra : PAddr) (rn : Nat) (rak : AkInfo)
    (Φ : (Nat → BitVec 8) → Prop) (D : PAddr → Nat → Prop) (W : Prop) (b : Bool) {X Y : Type}
    (m : SailM X) (f : X → SailM Y) (s : Wmstate) :
    wstepOkRacy tid ra rn rak Φ D W b m s →
    (∀ x s', wrun tid m s x s' → ∀ b', wstepOkRacy tid ra rn rak Φ D W b' (f x) s') →
    wstepOkRacy tid ra rn rak Φ D W b (m >>= f) s := by
  intro hm hf
  apply (wstepOkRacyKTriv tid ra rn rak Φ D W b (m >>= f) s).1
  apply wstepOkRacyKBind
  exact wstepOkRacyKOfRun tid ra rn rak Φ D W b m s _ hm
    (fun x s' hrun b' => (wstepOkRacyKTriv tid ra rn rak Φ D W b' (f x) s').2 (hf x s' hrun b'))

/-! ## 8. THE PHASE, RENOUNCED: what the write parameter `W` buys -/

theorem wstepOkRacyPhaseMonoGen (tid : Option Nat) (ra : PAddr) (rn : Nat) (rak : AkInfo)
    (Φ : (Nat → BitVec 8) → Prop) (D : PAddr → Nat → Prop) (W : Prop) {X : Type} (m : SailM X) :
    W →
    ∀ s, wstepOkRacy tid ra rn rak Φ D W false m s → wstepOkRacy tid ra rn rak Φ D W true m s := by
  intro hW
  induction m with
  | pure y => intros; simp only [wstepOkRacy]
  | impure call k ih =>
    intro s hok
    cases call with
    | error e => simp only [wstepOkRacy]
    | ok o =>
      cases o
      case memRead n va req =>
        simp only [wstepOkRacy] at hok ⊢
        by_cases hd : mmioAcc req.pa n = true
        · rw [if_pos hd] at hok ⊢
          exact fun w d' hdr => ih _ _ (hok w d' hdr)
        · rw [if_neg hd] at hok ⊢
          obtain ⟨hacc, hor⟩ := hok
          rcases hor with ⟨hd', hpin, hk⟩ | ⟨hb, _⟩
          · exact ⟨hacc, Or.inl ⟨hd', hpin, fun w hw => ih _ _ (hk w hw)⟩⟩
          · exact absurd hb (by simp)
      case memWrite n va req =>
        simp only [wstepOkRacy] at hok ⊢
        by_cases hd : mmioAcc req.pa n = true
        · rw [if_pos hd] at hok ⊢
          cases hv : req.value with
          | none => trivial
          | some v =>
            simp only [hv] at hok ⊢
            exact fun d' hdw => ih _ _ (hok d' hdw)
        · rw [if_neg hd] at hok ⊢
          obtain ⟨-, hacc, hd', hk⟩ := hok
          exact ⟨by simp [hW], hacc, hd', hk⟩
      case choose => simp only [wstepOkRacy] at hok
      all_goals first
        | (simp only [wstepOkRacy]; done)
        | (simp only [wstepOkRacy] at hok ⊢; exact ih _ _ hok)

/-- The instance the reducibility-only consumers use. -/
theorem wstepOkRacyPhaseMono (tid : Option Nat) (ra : PAddr) (rn : Nat) (rak : AkInfo)
    (Φ : (Nat → BitVec 8) → Prop) (D : PAddr → Nat → Prop) {X : Type} (m : SailM X)
    (s : Wmstate) :
    wstepOkRacy tid ra rn rak Φ D True false m s → wstepOkRacy tid ra rn rak Φ D True true m s :=
  wstepOkRacyPhaseMonoGen tid ra rn rak Φ D True m trivial s

/-- `wstepOkRacyKOfRun` with `K` demanded at phase `false` ALONE, for a phase-monotone `K`. -/
theorem wstepOkRacyKOfRunFalse (tid : Option Nat) (ra : PAddr) (rn : Nat) (rak : AkInfo)
    (Φ : (Nat → BitVec 8) → Prop) (D : PAddr → Nat → Prop) (W : Prop) (b : Bool) {X : Type}
    (m : SailM X) (s : Wmstate) (K : X → Wmstate → Bool → Prop) :
    (∀ x s', K x s' false → K x s' true) →
    wstepOkRacy tid ra rn rak Φ D W b m s →
    (∀ x s', wrun tid m s x s' → K x s' false) →
    wstepOkRacyK tid ra rn rak Φ D W b m s K := by
  intro hmono hok hK
  refine wstepOkRacyKOfRun tid ra rn rak Φ D W b m s K hok (fun x s' hrun b' => ?_)
  cases b'
  · exact hK x s' hrun
  · exact hmono x s' (hK x s' hrun)

/-- THE STORE-SHAPED BIND: the tail is certified at phase `false` only. -/
theorem wstepOkRacyBindFalse (tid : Option Nat) (ra : PAddr) (rn : Nat) (rak : AkInfo)
    (Φ : (Nat → BitVec 8) → Prop) (D : PAddr → Nat → Prop) (W : Prop) (b : Bool) {X Y : Type}
    (m : SailM X) (f : X → SailM Y) (s : Wmstate) :
    W →
    wstepOkRacy tid ra rn rak Φ D W b m s →
    (∀ x s', wrun tid m s x s' → wstepOkRacy tid ra rn rak Φ D W false (f x) s') →
    wstepOkRacy tid ra rn rak Φ D W b (m >>= f) s := by
  intro hW hm hf
  apply (wstepOkRacyKTriv tid ra rn rak Φ D W b (m >>= f) s).1
  apply wstepOkRacyKBind
  refine wstepOkRacyKOfRunFalse tid ra rn rak Φ D W b m s _ ?_ hm ?_
  · intro x s' hK
    exact (wstepOkRacyKTriv tid ra rn rak Φ D W true (f x) s').2
      (wstepOkRacyPhaseMonoGen tid ra rn rak Φ D W (f x) hW s'
        ((wstepOkRacyKTriv tid ra rn rak Φ D W false (f x) s').1 hK))
  · intro x s' hrun
    exact (wstepOkRacyKTriv tid ra rn rak Φ D W false (f x) s').2 (hf x s' hrun)

/-! ## 9. SEQUENTIAL WINDOWS: the certification traversals at the CPS form -/

theorem wexecOfExecRacyKseq (tid : Option Nat) (ra : PAddr) (rn : Nat) (rak : AkInfo)
    (Φ : (Nat → BitVec 8) → Prop) (D : PAddr → Nat → Prop) (W : Prop) {X Y : Type}
    (m : SailM X) (f : X → SailM Y) (K : X → Wmstate → Bool → Prop) :
    accWf ra rn →
    ∀ (b : Bool) (s : Wmstate),
      wstepOkRacyK tid ra rn rak Φ D W b m s K →
      wlogWf s.wmLog →
      (b = true → wadmFilter s rak ra rn Φ) →
      (∀ (y : X) (s1 : Wmstate) (b1 : Bool), K y s1 b1 → wlogWf s1.wmLog →
        ∀ (z : Y) (t1 : ExecSt), exec (f y) (wflatSt s1) = some (z, t1) →
          ∃ χ1 s1' χ1', wexec tid (f y) χ1 s1 = some (z, s1', χ1') ∧ wflatSt s1' = t1) →
      ∀ (z : Y) (t' : ExecSt), exec (m >>= f) (wflatSt s) = some (z, t') →
        ∃ χ s' χ', wexec tid (m >>= f) χ s = some (z, s', χ') ∧ wflatSt s' = t' := by
  intro hracc
  induction m with
  | pure y =>
    intro b s hok hwf _ hK z t' h
    exact hK y s b hok hwf z t' h
  | impure call k ih =>
    intro b s hok hwf hΦ hK z t' h
    rw [bindNext] at h ⊢
    cases call with
    | error e => simp [exec] at h
    | ok o =>
      cases o
      case memRead n va req =>
        simp only [wstepOkRacyK] at hok
        by_cases hd : mmioAcc req.pa n = true
        · rw [if_pos hd] at hok
          rw [execMemReadDev n va req _ _ hd, wflatStDev] at h
          cases hdr : devRead s.wmDev req.pa n with
          | none => rw [hdr] at h; cases h
          | some p =>
            obtain ⟨w0, d'⟩ := p
            rw [hdr] at h
            obtain ⟨χ, s2, χ', hw, heq⟩ := ih _ _ _ (hok w0 d' hdr) hwf
              (fun hb => wadmFilterSetDev _ _ _ _ _ _ (hΦ hb)) hK _ _ h
            exact ⟨χ, s2, χ', by simp only [wexec, if_pos hd, hdr]; exact hw, heq⟩
        · have hd' : mmioAcc req.pa n = false := by simpa using hd
          rw [if_neg hd] at hok
          obtain ⟨hacc, hor⟩ := hok
          rw [execMemRead n va req _ _ hd', wflatStMem] at h
          cases hbr : bmRead (wflatMem s.wmImg s.wmLog) req.pa n with
          | none => rw [hbr] at h; cases h
          | some w0 =>
            rw [hbr] at h
            have hrb : wreadBytes s (classify req.access_kind) req.pa n (cohTs s req.pa n) =
                some w0 := by
              rw [wreadBytesReadBytes s _ req.pa n hwf hacc, hbr]
            rcases hor with ⟨_, _, hk⟩ | ⟨hbt, hpa, hn, hak, hk⟩
            · have h2 : exec (k (.Ok (w0, none)) >>= f)
                  (wflatSt (wreadPost s (classify req.access_kind) req.pa (cohTs s req.pa n))) =
                  some (z, t') := by
                rw [wflatStReadPost]; exact h
              obtain ⟨χ, s2, χ', hw, heq⟩ := ih _ _ _ (hk w0 hrb) (wlogWfReadPost _ _ _ _ hwf)
                (fun hb => wadmFilterReadPost _ _ _ _ _ _ _ _ (hΦ hb)) hK _ _ h2
              exact ⟨cohTs s req.pa n :: χ, s2, χ',
                by simp only [wexec, if_neg hd, List.head?_cons, List.tail_cons, hrb]; exact hw, heq⟩
            · subst hn
              subst hpa
              subst hak
              -- the CANONICAL word is admissible, so the filter accepts it
              have hp2 := hk (cohTs s req.pa n) w0 hrb
                (hΦ hbt w0 (wadmOfWreadOk _ _ _ _ _ _ (wreadBytesSpec _ _ _ _ _ _ hrb)))
              have h2 : exec (k (.Ok (w0, none)) >>= f)
                  (wflatSt (wreadPost s (classify req.access_kind) req.pa (cohTs s req.pa n))) =
                  some (z, t') := by
                rw [wflatStReadPost]; exact h
              obtain ⟨χ, s2, χ', hw, heq⟩ := ih _ _ _ hp2 (wlogWfReadPost _ _ _ _ hwf)
                (fun hb => by cases hb) hK _ _ h2
              exact ⟨cohTs s req.pa n :: χ, s2, χ',
                by simp only [wexec, if_neg hd, List.head?_cons, List.tail_cons, hrb]; exact hw, heq⟩
      case memWrite n va req =>
        simp only [wstepOkRacyK] at hok
        cases hv : req.value with
        | none =>
          simp only [exec, hv] at h
          cases h
        | some v =>
          by_cases hd : mmioAcc req.pa n = true
          · rw [if_pos hd] at hok
            simp only [hv] at hok
            rw [execMemWriteDev n va req _ _ v hv hd, wflatStDev] at h
            cases hdw : devWrite s.wmDev req.pa n v with
            | none => rw [hdw] at h; cases h
            | some d' =>
              rw [hdw] at h
              obtain ⟨χ, s2, χ', hw, heq⟩ := ih _ _ _ (hok d' hdw) hwf
                (fun hb => wadmFilterSetDev _ _ _ _ _ _ (hΦ hb)) hK _ _ h
              exact ⟨χ, s2, χ', by simp only [wexec, if_pos hd, hv, hdw]; exact hw, heq⟩
          · have hd' : mmioAcc req.pa n = false := by simpa using hd
            rw [if_neg hd] at hok
            simp only [hv] at hok
            obtain ⟨_, hacc, _, hok⟩ := hok
            rw [execMemWrite n va req _ _ v hv hd'] at h
            have h2 : exec (k (.Ok (some true)) >>= f)
                (wflatSt (wwritePost tid s (classify req.access_kind) req.pa n v)) =
                some (z, t') := by
              rw [wflatStWritePost _ _ _ _ _ _ hacc]; exact h
            obtain ⟨χ, s2, χ', hw, heq⟩ := ih _ _ _ hok (wflatWriteWf _ _ _ _ _ _ hwf hacc)
              (fun hb => by cases hb) hK _ _ h2
            exact ⟨χ, s2, χ', by simp only [wexec, if_neg hd, hv]; exact hw, heq⟩
      case regWrite r v =>
        simp only [wstepOkRacyK] at hok
        simp only [exec] at h
        obtain ⟨χ, s2, χ', hw, heq⟩ := ih _ _ _ hok hwf
          (fun hb => wadmFilterSetReg _ _ _ _ _ _ _ (hΦ hb)) hK _ _ h
        exact ⟨χ, s2, χ', by simp only [wexec]; exact hw, heq⟩
      case barrier bk =>
        simp only [wstepOkRacyK] at hok
        simp only [exec] at h
        obtain ⟨χ, s2, χ', hw, heq⟩ := ih _ _ _ hok hwf
          (fun hb => wadmFilterBarrierPost _ _ _ _ _ _ (hΦ hb)) hK _ _ h
        exact ⟨χ, s2, χ', by simp only [wexec]; exact hw, heq⟩
      case choose => simp only [wstepOkRacyK] at hok
      all_goals first
        | (simp only [exec, reduceCtorEq] at h; done)
        | (simp only [wstepOkRacyK] at hok
           simp only [exec] at h
           obtain ⟨χ, s2, χ', hw, heq⟩ := ih _ _ _ hok hwf hΦ hK _ _ h
           exact ⟨χ, s2, χ', by simp only [wexec]; exact hw, heq⟩)

theorem wrunWexecRacyKseq (tid : Option Nat) (ra : PAddr) (rn : Nat) (rak : AkInfo)
    (Φ : (Nat → BitVec 8) → Prop) (D : PAddr → Nat → Prop) (W : Prop) {X Y : Type}
    (m : SailM X) (f : X → SailM Y) (K : X → Wmstate → Bool → Prop) :
    ∀ (b : Bool) (s : Wmstate),
      wstepOkRacyK tid ra rn rak Φ D W b m s K →
      (b = true → wadmFilter s rak ra rn Φ) →
      (∀ (y : X) (s1 : Wmstate) (b1 : Bool), K y s1 b1 →
        ∀ (z : Y) (s1' : Wmstate), wrun tid (f y) s1 z s1' →
          ∃ χ1 χ1', wexec tid (f y) χ1 s1 = some (z, s1', χ1')) →
      ∀ (z : Y) (s' : Wmstate), wrun tid (m >>= f) s z s' →
        ∃ χ χ', wexec tid (m >>= f) χ s = some (z, s', χ') := by
  induction m with
  | pure y =>
    intro b s hok _ hK z s' hrun
    exact hK y s b hok z s' hrun
  | impure call k ih =>
    intro b s hok hΦ hK z s' hrun
    rw [bindNext] at hrun ⊢
    cases call with
    | error e => exact hrun.elim
    | ok o =>
      cases o
      case memRead n va req =>
        simp only [wstepOkRacyK] at hok
        simp only [wrun] at hrun
        by_cases hd : mmioAcc req.pa n = true
        · rw [if_pos hd] at hok hrun
          cases hdr : devRead s.wmDev req.pa n with
          | none => rw [hdr] at hrun; exact hrun.elim
          | some p =>
            obtain ⟨w0, d'⟩ := p
            rw [hdr] at hrun
            obtain ⟨χ, χ', hex⟩ := ih _ _ _ (hok w0 d' hdr)
              (fun hb => wadmFilterSetDev _ _ _ _ _ _ (hΦ hb)) hK _ _ hrun
            exact ⟨χ, χ', by simp only [wexec, if_pos hd, hdr]; exact hex⟩
        · rw [if_neg hd] at hok hrun
          obtain ⟨w0, ts, hokr, hrun⟩ := hrun
          obtain ⟨_, hor⟩ := hok
          have hrb := wreadBytesComplete _ _ _ _ _ _ hokr
          rcases hor with ⟨_, hpin, hk⟩ | ⟨hbt, hpa, hn, hak, hk⟩
          · have hts := wreadPinnedTs s _ _ _ _ _ hpin hokr
            subst hts
            obtain ⟨χ, χ', hex⟩ := ih _ _ _ (hk w0 hrb)
              (fun hb => wadmFilterReadPost _ _ _ _ _ _ _ _ (hΦ hb)) hK _ _ hrun
            exact ⟨cohTs s req.pa n :: χ, χ',
              by simp only [wexec, if_neg hd, List.head?_cons, List.tail_cons, hrb]; exact hex⟩
          · subst hn
            subst hpa
            subst hak
            -- the word the run actually read is admissible, so the filter accepts it
            obtain ⟨χ, χ', hex⟩ := ih _ _ _
              (hk ts w0 hrb (hΦ hbt w0 (wadmOfWreadOk _ _ _ _ _ _ hokr)))
              (fun hb => by cases hb) hK _ _ hrun
            exact ⟨ts :: χ, χ',
              by simp only [wexec, if_neg hd, List.head?_cons, List.tail_cons, hrb]; exact hex⟩
      case memWrite n va req =>
        simp only [wstepOkRacyK] at hok
        simp only [wrun] at hrun
        cases hv : req.value with
        | none =>
          by_cases hd : mmioAcc req.pa n = true
          · simp [hd, hv] at hrun
          · simp [hd, hv] at hrun
        | some v =>
          by_cases hd : mmioAcc req.pa n = true
          · rw [if_pos hd] at hok hrun
            simp only [hv] at hok hrun
            cases hdw : devWrite s.wmDev req.pa n v with
            | none => rw [hdw] at hrun; exact hrun.elim
            | some d' =>
              rw [hdw] at hrun
              obtain ⟨χ, χ', hex⟩ := ih _ _ _ (hok d' hdw)
                (fun hb => wadmFilterSetDev _ _ _ _ _ _ (hΦ hb)) hK _ _ hrun
              exact ⟨χ, χ', by simp only [wexec, if_pos hd, hv, hdw]; exact hex⟩
          · rw [if_neg hd] at hok hrun
            simp only [hv] at hok hrun
            obtain ⟨_, _, _, hok⟩ := hok
            obtain ⟨χ, χ', hex⟩ := ih _ _ _ hok (fun hb => by cases hb) hK _ _ hrun
            exact ⟨χ, χ', by simp only [wexec, if_neg hd, hv]; exact hex⟩
      case regWrite r v =>
        simp only [wstepOkRacyK] at hok
        simp only [wrun] at hrun
        obtain ⟨χ, χ', hex⟩ := ih _ _ _ hok
          (fun hb => wadmFilterSetReg _ _ _ _ _ _ _ (hΦ hb)) hK _ _ hrun
        exact ⟨χ, χ', by simp only [wexec]; exact hex⟩
      case barrier bk =>
        simp only [wstepOkRacyK] at hok
        simp only [wrun] at hrun
        obtain ⟨χ, χ', hex⟩ := ih _ _ _ hok
          (fun hb => wadmFilterBarrierPost _ _ _ _ _ _ (hΦ hb)) hK _ _ hrun
        exact ⟨χ, χ', by simp only [wexec]; exact hex⟩
      case choose => simp only [wstepOkRacyK] at hok
      case readRam => exact hrun.elim
      case writeRam => exact hrun.elim
      all_goals
        simp only [wstepOkRacyK] at hok
        simp only [wrun] at hrun
        obtain ⟨χ, χ', hex⟩ := ih _ _ _ hok hΦ hK _ _ hrun
        exact ⟨χ, χ', by simp only [wexec]; exact hex⟩

/-- The two-window instances: window₂'s peel and filter ride the seam continuation. -/
theorem wexecOfExecRacySeq2 (tid : Option Nat)
    (ra1 : PAddr) (rn1 : Nat) (rak1 : AkInfo) (Φ1 : (Nat → BitVec 8) → Prop)
    (D1 : PAddr → Nat → Prop) (W1 : Prop)
    (ra2 : PAddr) (rn2 : Nat) (rak2 : AkInfo) (Φ2 : (Nat → BitVec 8) → Prop)
    (D2 : PAddr → Nat → Prop) (W2 : Prop)
    {X Y : Type} (m : SailM X) (f : X → SailM Y) (s : Wmstate) :
    accWf ra1 rn1 → accWf ra2 rn2 →
    wstepOkRacyK tid ra1 rn1 rak1 Φ1 D1 W1 true m s
      (fun x s1 _ => wstepOkRacy tid ra2 rn2 rak2 Φ2 D2 W2 true (f x) s1 ∧
                     wadmFilter s1 rak2 ra2 rn2 Φ2) →
    wlogWf s.wmLog →
    wadmFilter s rak1 ra1 rn1 Φ1 →
    ∀ (z : Y) (t' : ExecSt), exec (m >>= f) (wflatSt s) = some (z, t') →
      ∃ χ s' χ', wexec tid (m >>= f) χ s = some (z, s', χ') ∧ wflatSt s' = t' := by
  intro hw1 hw2 hok hwf hflt
  refine wexecOfExecRacyKseq tid ra1 rn1 rak1 Φ1 D1 W1 m f _ hw1 true s hok hwf (fun _ => hflt) ?_
  rintro y s1 b1 ⟨hok2, hflt2⟩ hwf1 z t1 hex1
  exact wexecOfExecRacy tid ra2 rn2 rak2 Φ2 D2 W2 (f y) hw2 true s1 hok2 hwf1 (fun _ => hflt2)
    z t1 hex1

theorem wrunWexecRacySeq2 (tid : Option Nat)
    (ra1 : PAddr) (rn1 : Nat) (rak1 : AkInfo) (Φ1 : (Nat → BitVec 8) → Prop)
    (D1 : PAddr → Nat → Prop) (W1 : Prop)
    (ra2 : PAddr) (rn2 : Nat) (rak2 : AkInfo) (Φ2 : (Nat → BitVec 8) → Prop)
    (D2 : PAddr → Nat → Prop) (W2 : Prop)
    {X Y : Type} (m : SailM X) (f : X → SailM Y) (s : Wmstate) :
    wstepOkRacyK tid ra1 rn1 rak1 Φ1 D1 W1 true m s
      (fun x s1 _ => wstepOkRacy tid ra2 rn2 rak2 Φ2 D2 W2 true (f x) s1 ∧
                     wadmFilter s1 rak2 ra2 rn2 Φ2) →
    wadmFilter s rak1 ra1 rn1 Φ1 →
    ∀ (z : Y) (s' : Wmstate), wrun tid (m >>= f) s z s' →
      ∃ χ χ', wexec tid (m >>= f) χ s = some (z, s', χ') := by
  intro hok hflt
  refine wrunWexecRacyKseq tid ra1 rn1 rak1 Φ1 D1 W1 m f _ true s hok (fun _ => hflt) ?_
  rintro y s1 b1 ⟨hok2, hflt2⟩ z s1' hrun1
  exact wrunWexecRacy tid ra2 rn2 rak2 Φ2 D2 W2 (f y) true s1 hok2 (fun _ => hflt2) z s1' hrun1

/-- Building the nested object: a plain peel of the prefix plus, at every run result, window₂'s
peel and filter for the tail. -/
theorem wstepOkRacyKSeqIntro (tid : Option Nat)
    (ra1 : PAddr) (rn1 : Nat) (rak1 : AkInfo) (Φ1 : (Nat → BitVec 8) → Prop)
    (D1 : PAddr → Nat → Prop) (W1 : Prop)
    (ra2 : PAddr) (rn2 : Nat) (rak2 : AkInfo) (Φ2 : (Nat → BitVec 8) → Prop)
    (D2 : PAddr → Nat → Prop) (W2 : Prop)
    (b : Bool) {X Y : Type} (m : SailM X) (f : X → SailM Y) (s : Wmstate) :
    wstepOkRacy tid ra1 rn1 rak1 Φ1 D1 W1 b m s →
    (∀ x s', wrun tid m s x s' →
      wstepOkRacy tid ra2 rn2 rak2 Φ2 D2 W2 true (f x) s' ∧ wadmFilter s' rak2 ra2 rn2 Φ2) →
    wstepOkRacyK tid ra1 rn1 rak1 Φ1 D1 W1 b m s
      (fun x s1 _ => wstepOkRacy tid ra2 rn2 rak2 Φ2 D2 W2 true (f x) s1 ∧
                     wadmFilter s1 rak2 ra2 rn2 Φ2) := by
  intro hok hK
  exact wstepOkRacyKOfRun tid ra1 rn1 rak1 Φ1 D1 W1 b m s _ hok (fun x s' hrun _ => hK x s' hrun)

/-! ## 10. THE ⇐-BRIDGE: every weak run of a peeled program lands on a FAMILY MEMBER's
`execStale` outcome

### 10-0. WHERE THE RUN WROTE: the trace's LOG FOOTPRINT -/

/-- Every write the trace performs has footprint in `A`. -/
def wtraceWonly (A : PAddr → Nat → Prop) (es : List Weff) : Prop :=
  ∀ (ak : AkInfo) (pa : PAddr) (n : Nat) (v : BitVec (8 * n)), Weff.WEwrite ak pa n v ∈ es → A pa n

theorem wtraceWonlyTail (A : PAddr → Nat → Prop) (e : Weff) (es : List Weff) :
    wtraceWonly A (e :: es) → wtraceWonly A es :=
  fun h ak pa n v hin => h ak pa n v (List.mem_cons_of_mem _ hin)

theorem wtraceWonlyHead (A : PAddr → Nat → Prop) (ak : AkInfo) (pa : PAddr) (n : Nat)
    (v : BitVec (8 * n)) (es : List Weff) :
    wtraceWonly A (.WEwrite ak pa n v :: es) → A pa n :=
  fun h => h ak pa n v List.mem_cons_self

/-- A trace with no `WEwrite` at all constrains nothing. -/
theorem WeakStale.wtraceWonlyReads (A : PAddr → Nat → Prop) (es : List Weff) :
    (∀ e, e ∈ es → match e with | .WEwrite .. => False | _ => True) → wtraceWonly A es :=
  fun hall ak pa n v hin => False.elim (hall _ hin)

/-- The appended message does not write a byte outside its own range. -/
theorem msgWritesbWwriteNe (tid : Option Nat) (k : WmClass) (pa : PAddr) (n : Nat)
    (v : BitVec (8 * n)) (a : PAddr) :
    (∀ j, j < n → pa + BitVec.ofNat 64 j ≠ a) →
    msgWritesb (wwriteMsg tid k pa n v) (paZ a) = false := by
  intro hne
  cases h : msgWritesb (wwriteMsg tid k pa n v) (paZ a) with
  | false => rfl
  | true =>
    exfalso
    obtain ⟨j, hj, he⟩ := (wwriteMsgWritesbIff _ _ _ _ _ _).1 h
    apply hne j hj
    rw [← zPaAccAddr pa j, ← he, zPaPaZ]

theorem latestTsWritePostNe (tid : Option Nat) (s : Wmstate) (ak : AkInfo) (pa : PAddr) (n : Nat)
    (v : BitVec (8 * n)) (a : PAddr) :
    (∀ j, j < n → pa + BitVec.ofNat 64 j ≠ a) →
    latestTs (wwritePost tid s ak pa n v).wmLog (paZ a) = latestTs s.wmLog (paZ a) := by
  intro hne
  rw [wwritePostLog, latestTsApp, msgWritesbWwriteNe tid _ pa n v a hne]
  simp only [Bool.false_eq_true, ↓reduceIte]

/-- The class, as a function of the access kind and the pending-release flag. -/
def wmClassRp (ak : AkInfo) (rp : Bool) : WmClass :=
  if ak.akLatest then .WCexcl else if (rp || ak.akSync) then .WCrel else .WCplain

theorem wmClassOfRp (ak : AkInfo) (ws : Wstate) : wmClassOf ak ws = wmClassRp ak ws.wRelp := rfl

theorem wmClassRpLatest (ak : AkInfo) (rp : Bool) : ak.akLatest = true → wmClassRp ak rp = .WCexcl := by
  intro h; simp only [wmClassRp, h, ↓reduceIte]

/-- The flag after a fence: a `pw ∧ sw` fence arms it. -/
def wrelpBar (b : barrier_kind) (rp : Bool) : Bool :=
  match b with
  | .Barrier_RISCV_rw_rw | .Barrier_RISCV_rw_w | .Barrier_RISCV_w_w
  | .Barrier_RISCV_w_rw | .Barrier_RISCV_tso => true
  | _ => rp

/-- The flag after a store: one of at least one byte clears it. -/
def wrelpWrite (n : Nat) (rp : Bool) : Bool :=
  match n with
  | 0 => rp
  | _ + 1 => false

theorem WeakStale.barrierPostRelp (ws : Wstate) (b : barrier_kind) :
    (barrierPost ws b).wRelp = wrelpBar b ws.wRelp := by
  cases b <;> simp [barrierPost, Weak.fencePost, wrelpBar]

theorem foldlLoadPostAtRelp (aq : Bool) (vpre : Nat) (ats : List (Int × Nat)) (ws : Wstate) :
    (ats.foldl (fun w at_ => loadPostAt w aq vpre at_.1 at_.2) ws).wRelp = ws.wRelp :=
  loadPostFoldRelp aq vpre ats ws

theorem WeakStale.loadPostBytesRelp (ws : Wstate) (aq : Bool) (ats : List (Int × Nat)) :
    (loadPostBytes ws aq ats).wRelp = ws.wRelp :=
  foldlLoadPostAtRelp _ _ _ _

theorem wsetWsRelp (s : Wmstate) (ws : Wstate) : (wsetWs s ws).wmWs.wRelp = ws.wRelp := rfl

theorem WeakStale.wreadPostRelp (s : Wmstate) (ak : AkInfo) (pa : PAddr) (ts : List Nat) :
    (wreadPost s ak pa ts).wmWs.wRelp = s.wmWs.wRelp :=
  WeakInstr.wreadPostRelp s ak pa ts

theorem storePostBytesRelp (ws : Wstate) (rl : Bool) (as_ : List Int) (t : Nat) :
    (storePostBytes ws rl as_ t).wRelp = (match as_ with | [] => ws.wRelp | _ :: _ => false) := by
  induction as_ generalizing ws with
  | nil => rfl
  | cons a l ih =>
    show (storePostBytes (storePost ws rl a t) rl l t).wRelp = false
    rw [ih]
    cases l <;> rfl

theorem wwritePostRelp (tid : Option Nat) (s : Wmstate) (ak : AkInfo) (pa : PAddr) (n : Nat)
    (v : BitVec (8 * n)) :
    (wwritePost tid s ak pa n v).wmWs.wRelp = wrelpWrite n s.wmWs.wRelp := by
  show (ctrlPost (storePostBytes s.wmWs ak.akSync
    ((List.range' 0 n).map (fun j : Nat => paZ pa + (j : Int))) (s.wmLog.length + 1))
    s.wmWs.wTbank).wRelp = _
  rw [ctrlPostRelp, storePostBytesRelp]
  cases n <;> rfl

/-- THE PROJECTION: the messages a run whose trace is `es` appended, in order (`rp` is the
pending-release flag of the state the run starts in). -/
def wtraceMsgs (tid : Option Nat) (rp : Bool) : List Weff → List Wmsg
  | [] => []
  | .WEread .. :: es' => wtraceMsgs tid rp es'
  | .WEbar b :: es' => wtraceMsgs tid (wrelpBar b rp) es'
  | .WEwrite ak pa n v :: es' =>
    wwriteMsg tid (wmClassRp ak rp) pa n v :: wtraceMsgs tid (wrelpWrite n rp) es'

theorem wtraceMsgsReadsNil (tid : Option Nat) (rp : Bool) (es : List Weff) :
    (∀ (ak : AkInfo) (pa : PAddr) (n : Nat) (v : BitVec (8 * n)),
      Weff.WEwrite ak pa n v ∈ es → False) →
    wtraceMsgs tid rp es = [] := by
  induction es generalizing rp with
  | nil => intro _; rfl
  | cons e es ih =>
    intro hno
    have hno' : ∀ (ak : AkInfo) (pa : PAddr) (n : Nat) (v : BitVec (8 * n)),
        Weff.WEwrite ak pa n v ∈ es → False :=
      fun ak pa n v hin => hno ak pa n v (List.mem_cons_of_mem _ hin)
    cases e with
    | WEread ak pa n => exact ih rp hno'
    | WEwrite ak pa n v => exact (hno ak pa n v List.mem_cons_self).elim
    | WEbar b => exact ih _ hno'

theorem wtraceMsgsSnocWrite (tid : Option Nat) (rp : Bool) (rs : List Weff) (ak : AkInfo)
    (pa : PAddr) (n : Nat) (v : BitVec (8 * n)) :
    (∀ (ak' : AkInfo) (pa' : PAddr) (n' : Nat) (v' : BitVec (8 * n')),
      Weff.WEwrite ak' pa' n' v' ∈ rs → False) →
    ak.akLatest = true →
    wtraceMsgs tid rp (rs ++ [.WEwrite ak pa n v]) = [wwriteMsg tid .WCexcl pa n v] := by
  induction rs generalizing rp with
  | nil =>
    intro _ hak
    show wwriteMsg tid (wmClassRp ak rp) pa n v :: [] = _
    rw [wmClassRpLatest _ _ hak]
  | cons e rs ih =>
    intro hno hak
    have hno' : ∀ (ak' : AkInfo) (pa' : PAddr) (n' : Nat) (v' : BitVec (8 * n')),
        Weff.WEwrite ak' pa' n' v' ∈ rs → False :=
      fun ak' pa' n' v' hin => hno ak' pa' n' v' (List.mem_cons_of_mem _ hin)
    cases e with
    | WEread ak' pa' n' => exact ih rp hno' hak
    | WEwrite ak' pa' n' v' => exact (hno ak' pa' n' v' List.mem_cons_self).elim
    | WEbar b => exact ih _ hno' hak

/-! ### 10a. The core, at a FIXED `w` -/

theorem wrunExecStaleElimOff (tid : Option Nat) (ra : PAddr) (rn : Nat) (rak : AkInfo)
    (Φ : (Nat → BitVec 8) → Prop) (W : Prop) (w : BitVec (8 * rn)) {X : Type} (m : SailM X) :
    accWf ra rn → 0 < rn → akPins rak = false →
    ∀ (b : Bool) (s : Wmstate) (x0 : X) (t0 : ExecSt) (es : List Weff),
      execStale ra rn w m (wflatSt s) = some (x0, t0, es) →
      traceOffWin ra rn es →
      wstepOkRacy tid ra rn rak Φ wDAny W b m s →
      wlogWf s.wmLog →
    ∀ (x : X) (s' : Wmstate), wrun tid m s x s' →
      execStale ra rn w m (wflatSt s) = some (x, wflatSt s', es) ∧
      wlogWf s'.wmLog ∧
      (∀ a : PAddr,
        wtraceWonly (fun pa n => ∀ j, j < n → pa + BitVec.ofNat 64 j ≠ a) es →
        latestTs s'.wmLog (paZ a) = latestTs s.wmLog (paZ a)) ∧
      s'.wmLog = s.wmLog ++ wtraceMsgs tid s.wmWs.wRelp es := by
  intro hracc hrn hrk
  induction m with
  | pure y =>
    intro b s x0 t0 es hex0 _ _ hwf x s' hrun
    obtain ⟨rfl, rfl⟩ := hrun
    simp only [execStale, Option.some.injEq, Prod.mk.injEq] at hex0
    obtain ⟨-, -, rfl⟩ := hex0
    exact ⟨rfl, hwf, fun _ _ => rfl, (List.append_nil _).symm⟩
  | impure call k ih =>
    intro b s x0 t0 es hex0 hoff hok hwf x s' hrun
    cases call with
    | error e => exact hrun.elim
    | ok o =>
      cases o
      case regWrite r v =>
        simp only [wstepOkRacy] at hok
        simp only [wrun] at hrun
        simp only [execStale] at hex0 ⊢
        exact ih _ b (wsetReg s r v) x0 t0 es hex0 hoff hok hwf x s' hrun
      case memRead n va req =>
        simp only [wstepOkRacy] at hok
        simp only [wrun] at hrun
        simp only [execStale] at hex0
        by_cases hd : mmioAcc req.pa n = true
        · rw [if_pos hd] at hok hrun hex0
          cases hdr : devRead s.wmDev req.pa n with
          | none => rw [hdr] at hrun; exact hrun.elim
          | some p =>
            obtain ⟨v0, d'⟩ := p
            rw [hdr] at hrun
            simp only [wflatStDev, hdr] at hex0
            have := ih _ b (wsetDev s d') x0 t0 es hex0 hoff (hok v0 d' hdr) hwf x s' hrun
            simp only [execStale, if_pos hd, wflatStDev, hdr]
            exact this
        · rw [if_neg hd] at hok hrun hex0
          cases hrb0 : bmRead (staleMem ra rn w (classify req.access_kind) (wflatSt s)) req.pa n with
          | none => simp only [hrb0] at hex0; cases hex0
          | some v0 =>
            simp only [hrb0] at hex0
            obtain ⟨es1, hee0, rfl⟩ := Weff.consEqSome.1 hex0
            obtain ⟨v, ts, hokr, hrun⟩ := hrun
            obtain ⟨hacc, hor⟩ := hok
            rcases hor with ⟨-, hpin, hk⟩ | ⟨-, hpa, hn, hak, -⟩
            · -- the away arm: the machine is pinned to `cohTs`
              have hts := wreadPinnedTs s _ req.pa n ts v hpin hokr
              subst hts
              have hrbw := wreadBytesComplete _ _ _ _ _ _ hokr
              have hrbf : bmRead (wflatMem s.wmImg s.wmLog) req.pa n = some v := by
                rw [← wreadBytesReadBytes s (classify req.access_kind) req.pa n hwf hacc]
                exact hrbw
              have hstm : bmRead (staleMem ra rn w (classify req.access_kind) (wflatSt s))
                  req.pa n = some v := by
                cases hpk : akPins (classify req.access_kind) with
                | true => rw [staleMemPins _ _ _ _ _ hpk]; exact hrbf
                | false =>
                  rw [staleMemUnpinned _ _ _ _ _ hpk]
                  obtain ⟨haccp, hdisj⟩ := traceOffWinHead ra rn _ _ n es1 hoff hpk
                  rw [wflatStMem, readBytesPatchDisj _ ra rn w _ n hracc haccp hdisj]
                  exact hrbf
              rw [hstm] at hrb0
              simp only [Option.some.injEq] at hrb0
              subst hrb0
              obtain ⟨hexf, hwf', hlt', hlog'⟩ :=
                ih _ b (wreadPost s (classify req.access_kind) req.pa (cohTs s req.pa n)) x0 t0 es1
                  (by rw [wflatStReadPost]; exact hee0) (traceOffWinTail _ _ _ _ hoff) (hk v hrbw)
                  (wlogWfReadPost _ _ _ _ hwf) x s' hrun
              rw [wflatStReadPost, hee0] at hexf
              simp only [Option.some.injEq, Prod.mk.injEq] at hexf
              obtain ⟨rfl, rfl, -⟩ := hexf
              refine ⟨?_, hwf', fun a hwo => ?_, ?_⟩
              · simp only [execStale, if_neg hd, hstm]
                exact Weff.consEqSome.2 ⟨_, hee0, rfl⟩
              · rw [hlt' a (wtraceWonlyTail _ _ _ hwo), wreadPostLog]
              · rw [hlog', wreadPostLog, WeakStale.wreadPostRelp]
                rfl
            · -- the racy arm is REFUTED by `traceOffWin`
              exfalso
              subst hn
              obtain ⟨-, hdisj⟩ := traceOffWinHead ra _ _ _ _ es1 hoff (by rw [hak]; exact hrk)
              rw [hpa] at hdisj
              exact raccDisjIrrefl _ _ hrn hdisj
      case memWrite n va req =>
        simp only [wstepOkRacy] at hok
        simp only [wrun] at hrun
        simp only [execStale] at hex0
        cases hv : req.value with
        | none => simp only [hv] at hex0; cases hex0
        | some v =>
          simp only [hv] at hok hrun hex0
          by_cases hd : mmioAcc req.pa n = true
          · rw [if_pos hd] at hok hrun hex0
            cases hdw : devWrite s.wmDev req.pa n v with
            | none => rw [hdw] at hrun; exact hrun.elim
            | some d' =>
              rw [hdw] at hrun
              simp only [wflatStDev, hdw] at hex0
              have := ih _ b (wsetDev s d') x0 t0 es hex0 hoff (hok d' hdw) hwf x s' hrun
              simp only [execStale, hv, if_pos hd, wflatStDev, hdw]
              exact this
          · rw [if_neg hd] at hok hrun hex0
            obtain ⟨-, hacc, -, hok⟩ := hok
            obtain ⟨es1, hee0, rfl⟩ := Weff.consEqSome.1 hex0
            obtain ⟨hexf, hwf', hlt', hlog'⟩ :=
              ih _ false (wwritePost tid s (classify req.access_kind) req.pa n v) x0 t0 es1
                (by rw [wflatStWritePost _ _ _ _ _ _ hacc]; exact hee0)
                (traceOffWinTail _ _ _ _ hoff) hok (wflatWriteWf _ _ _ _ _ _ hwf hacc) x s' hrun
            rw [wflatStWritePost _ _ _ _ _ _ hacc, hee0] at hexf
            simp only [Option.some.injEq, Prod.mk.injEq] at hexf
            obtain ⟨rfl, rfl, -⟩ := hexf
            refine ⟨?_, hwf', fun a hwo => ?_, ?_⟩
            · simp only [execStale, hv, if_neg hd]
              exact Weff.consEqSome.2 ⟨_, hee0, rfl⟩
            · rw [hlt' a (wtraceWonlyTail _ _ _ hwo)]
              exact latestTsWritePostNe tid s _ _ _ v a (wtraceWonlyHead _ _ _ _ _ _ hwo)
            · rw [hlog', wwritePostLog, wwritePostRelp, List.append_assoc]
              rfl
      case barrier bk =>
        simp only [wstepOkRacy] at hok
        simp only [wrun] at hrun
        simp only [execStale] at hex0
        obtain ⟨es1, hee0, rfl⟩ := Weff.consEqSome.1 hex0
        obtain ⟨hexf, hwf', hlt', hlog'⟩ := ih () b (wbarrierPost s bk) x0 t0 es1 hee0
          (traceOffWinTail _ _ _ _ hoff) hok hwf x s' hrun
        rw [wflatStBarrier, hee0] at hexf
        simp only [Option.some.injEq, Prod.mk.injEq] at hexf
        obtain ⟨rfl, rfl, -⟩ := hexf
        refine ⟨?_, hwf', fun a hwo => hlt' a (wtraceWonlyTail _ _ _ hwo), ?_⟩
        · simp only [execStale]
          exact Weff.consEqSome.2 ⟨_, hee0, rfl⟩
        · rw [hlog', wbarrierPostLog, wbarrierPostWs, WeakStale.barrierPostRelp]
          rfl
      case choose => simp only [wstepOkRacy] at hok
      case readRam => exact hrun.elim
      case writeRam => exact hrun.elim
      all_goals
        simp only [wstepOkRacy] at hok
        simp only [wrun] at hrun
        simp only [execStale] at hex0 ⊢
        exact ih _ b s x0 t0 es hex0 hoff hok hwf x s' hrun

/-! ### 10b. The front: the phase-`true` traversal, which CHOOSES the witness -/

/-- The COHERENT word of the window at `s0`: admissible, hence accepted by the filter
(Lean-only helper). -/
theorem WeakStale.cohWord (s0 : Wmstate) (rak : AkInfo) (ra : PAddr) (rn : Nat)
    (Φ : (Nat → BitVec 8) → Prop) :
    wlogWf s0.wmLog → accWf ra rn → wadmFilter s0 rak ra rn Φ →
    (bmRead (wflatMem s0.wmImg s0.wmLog) ra rn).isSome = true →
    ∃ wc : BitVec (8 * rn), bmRead (wflatMem s0.wmImg s0.wmLog) ra rn = some wc ∧
      wadm s0 rak ra rn wc ∧ Φ (fun j => nthByte wc j) := by
  intro hwf hracc hΦ hrd
  obtain ⟨wc, hwc⟩ := Option.isSome_iff_exists.1 hrd
  have hwcw : wreadBytes s0 rak ra rn (cohTs s0 ra rn) = some wc := by
    rw [wreadBytesReadBytes s0 rak ra rn hwf hracc]; exact hwc
  have hadmc := wadmOfWreadOk _ _ _ _ _ _ (wreadBytesSpec _ _ _ _ _ _ hwcw)
  exact ⟨wc, hwc, hadmc, hΦ wc hadmc⟩

theorem wrunExecStaleElimGen (tid : Option Nat) (ra : PAddr) (rn : Nat) (rak : AkInfo)
    (Φ : (Nat → BitVec 8) → Prop) (W : Prop) {X : Type} (m : SailM X) :
    accWf ra rn → 0 < rn → akPins rak = false →
    ∀ (s0 s : Wmstate),
      wadmFilter s0 rak ra rn Φ →
      wstepOkRacy tid ra rn rak Φ wDAny W true m s →
      s.wmImg = s0.wmImg → s.wmLog = s0.wmLog → wsLe s0.wmWs s.wmWs → s0.wmItv ≤ s.wmItv →
      wlogWf s.wmLog →
      (bmRead (wflatMem s0.wmImg s0.wmLog) ra rn).isSome = true →
      (∀ u : BitVec (8 * rn), Φ (fun j => nthByte u j) →
        ∃ (y : X) (t' : ExecSt) (es : List Weff),
          execStale ra rn u m (wflatSt s) = some (y, t', es) ∧ traceStale rak ra rn es) →
    ∀ (x : X) (s' : Wmstate), wrun tid m s x s' →
      ∃ (w : BitVec (8 * rn)) (es : List Weff),
        wadm s0 rak ra rn w ∧ Φ (fun j => nthByte w j) ∧
        execStale ra rn w m (wflatSt s) = some (x, wflatSt s', es) ∧
        wlogWf s'.wmLog ∧
        (∀ a : PAddr,
          wtraceWonly (fun pa n => ∀ j, j < n → pa + BitVec.ofNat 64 j ≠ a) es →
          latestTs s'.wmLog (paZ a) = latestTs s.wmLog (paZ a)) ∧
        s'.wmLog = s.wmLog ++ wtraceMsgs tid s.wmWs.wRelp es := by
  intro hracc hrn hrk
  induction m with
  | pure y =>
    -- the run ended with the racy read still ahead: the COHERENT word
    intro s0 s hΦ _ _ hlog _ _ hwf hrd _ x s' hrun
    obtain ⟨rfl, rfl⟩ := hrun
    obtain ⟨wc, -, hadmc, hΦc⟩ := WeakStale.cohWord s0 rak ra rn Φ (hlog ▸ hwf) hracc hΦ hrd
    exact ⟨wc, [], hadmc, hΦc, rfl, hwf, fun _ _ => rfl, (List.append_nil _).symm⟩
  | impure call k ih =>
    intro s0 s hΦ hok himg hlog hle hitv hwf hrd hfam x s' hrun
    have hwf0 : wlogWf s0.wmLog := hlog ▸ hwf
    cases call with
    | error e => exact hrun.elim
    | ok o =>
      cases o
      case regWrite r v =>
        simp only [wstepOkRacy] at hok
        simp only [wrun] at hrun
        simp only [execStale] at hfam ⊢
        exact ih _ s0 (wsetReg s r v) hΦ hok himg hlog hle hitv hwf hrd hfam x s' hrun
      case memRead n va req =>
        simp only [wstepOkRacy] at hok
        simp only [wrun] at hrun
        simp only [execStale] at hfam
        by_cases hd : mmioAcc req.pa n = true
        · rw [if_pos hd] at hok hrun
          simp only [if_pos hd] at hfam
          cases hdr : devRead s.wmDev req.pa n with
          | none => rw [hdr] at hrun; exact hrun.elim
          | some p =>
            obtain ⟨v0, d'⟩ := p
            rw [hdr] at hrun
            simp only [wflatStDev, hdr] at hfam
            have := ih _ s0 (wsetDev s d') hΦ (hok v0 d' hdr) himg hlog hle hitv hwf hrd hfam x s'
              hrun
            simp only [execStale, if_pos hd, wflatStDev, hdr]
            exact this
        · rw [if_neg hd] at hok hrun
          simp only [if_neg hd] at hfam
          obtain ⟨wc, hwc, hadmc, hΦc⟩ := WeakStale.cohWord s0 rak ra rn Φ hwf0 hracc hΦ hrd
          obtain ⟨v, ts, hokr, hrun⟩ := hrun
          obtain ⟨hacc, hor⟩ := hok
          rcases hor with ⟨-, hpin, hk⟩ | ⟨-, hpa, hn, hak, hk⟩
          · -- THE PEEL'S AWAY ARM: the machine is pinned to `cohTs`
            have hts := wreadPinnedTs s _ req.pa n ts v hpin hokr
            subst hts
            have hrbw := wreadBytesComplete _ _ _ _ _ _ hokr
            have hrbf : bmRead (wflatMem s.wmImg s.wmLog) req.pa n = some v := by
              rw [← wreadBytesReadBytes s (classify req.access_kind) req.pa n hwf hacc]
              exact hrbw
            -- the CLASSIFYING member: the head's arm is decided by the read's kind, address and
            -- width, never by the patch value
            obtain ⟨yc, tc, esc, hexc, hstc⟩ := hfam wc hΦc
            cases hrbc : bmRead (staleMem ra rn wc (classify req.access_kind) (wflatSt s)) req.pa n with
            | none => simp only [hrbc] at hexc; cases hexc
            | some vc =>
              simp only [hrbc] at hexc
              obtain ⟨esc2, heec, rfl⟩ := Weff.consEqSome.1 hexc
              by_cases hwin : akPins (classify req.access_kind) = true ∨ raccDisj ra rn req.pa n
              · -- PINNED kind, or UNPINNED OFF the window: every member returns the machine's word
                obtain ⟨hstm, hstep⟩ :
                    (∀ u : BitVec (8 * rn), bmRead (staleMem ra rn u (classify req.access_kind)
                      (wflatSt s)) req.pa n = some v) ∧
                    (∀ es, traceStale rak ra rn (.WEread (classify req.access_kind) req.pa n :: es) →
                      traceStale rak ra rn es) := by
                  cases hpk : akPins (classify req.access_kind) with
                  | true =>
                    exact ⟨fun u => by rw [staleMemPins _ _ _ _ _ hpk]; exact hrbf,
                      fun es h => traceStalePinTail rak ra rn _ _ n es hrk hpk h⟩
                  | false =>
                    have hdisj : raccDisj ra rn req.pa n := by
                      rcases hwin with h | h
                      · rw [hpk] at h; cases h
                      · exact h
                    exact ⟨fun u => by
                        rw [staleMemUnpinned _ _ _ _ _ hpk, wflatStMem,
                          readBytesPatchDisj _ ra rn u _ n hracc hacc hdisj]
                        exact hrbf,
                      fun es h => traceStaleDisjTail rak ra rn _ _ n es hrn hpk hdisj h⟩
                have hfam2 : ∀ u : BitVec (8 * rn), Φ (fun j => nthByte u j) →
                    ∃ (y : X) (t' : ExecSt) (es : List Weff),
                      execStale ra rn u (k (.Ok (v, none)))
                        (wflatSt (wreadPost s (classify req.access_kind) req.pa (cohTs s req.pa n))) =
                        some (y, t', es) ∧ traceStale rak ra rn es := by
                  intro u hu
                  obtain ⟨y1, t1, es1, hex1, hst1⟩ := hfam u hu
                  simp only [hstm u] at hex1
                  obtain ⟨es2, hee1, rfl⟩ := Weff.consEqSome.1 hex1
                  exact ⟨y1, t1, es2, by rw [wflatStReadPost]; exact hee1, hstep es2 hst1⟩
                obtain ⟨w, es, hadm, hΦw, hexw, hwf', hlt', hlog'⟩ := ih _ s0 _ hΦ (hk v hrbw)
                  ((wreadPostImg _ _ _ _).trans himg) ((wreadPostLog _ _ _ _).trans hlog)
                  (wsLeTrans hle (wreadPostWsLe _ _ _ _)) (by rw [wreadPostItv]; exact hitv)
                  (wlogWfReadPost _ _ _ _ hwf) hrd hfam2 x s' hrun
                refine ⟨w, .WEread (classify req.access_kind) req.pa n :: es, hadm, hΦw, ?_, hwf',
                  fun a hwo => ?_, ?_⟩
                · simp only [execStale, if_neg hd, hstm w]
                  rw [wflatStReadPost] at hexw
                  exact Weff.consEqSome.2 ⟨_, hexw, rfl⟩
                · rw [hlt' a (wtraceWonlyTail _ _ _ hwo), wreadPostLog]
                · rw [hlog', wreadPostLog, WeakStale.wreadPostRelp]
                  rfl
              · -- THE WINDOW, taken at the AWAY arm: the peel PINNED it, so the machine read the
                -- coherence-latest word, and that word is the witness
                have hpk : akPins (classify req.access_kind) = false := by
                  cases h : akPins (classify req.access_kind) with
                  | true => exact absurd (Or.inl h) hwin
                  | false => rfl
                have hndisj : ¬ raccDisj ra rn req.pa n := fun h => hwin (Or.inr h)
                obtain ⟨hak, hpa, hn, hoffc⟩ := traceStaleWin rak ra rn _ _ n esc2 hpk hndisj hstc
                subst hn
                subst hpa
                subst hak
                have hvc : vc = wc := by
                  rw [readBytesStaleWin _ _ wc _ (wflatSt s) hracc hpk] at hrbc
                  simp only [Option.some.injEq] at hrbc
                  exact hrbc.symm
                have hvw : v = wc := by
                  rw [himg, hlog, hwc] at hrbf
                  simp only [Option.some.injEq] at hrbf
                  exact hrbf.symm
                subst hvc
                subst hvw
                obtain ⟨hexf, hwf', hlt', hlog'⟩ := wrunExecStaleElimOff tid _ _ _ Φ W v _
                  hracc hrn hrk true
                  (wreadPost s (classify req.access_kind) req.pa (cohTs s req.pa n)) yc tc esc2
                  (by rw [wflatStReadPost]; exact heec) hoffc (hk v hrbw)
                  (wlogWfReadPost _ _ _ _ hwf) x s' hrun
                refine ⟨v, .WEread (classify req.access_kind) req.pa n :: esc2, hadmc, hΦc, ?_,
                  hwf', fun a hwo => ?_, ?_⟩
                · simp only [execStale, if_neg hd, readBytesStaleWin _ _ v _ (wflatSt s) hracc hpk]
                  rw [wflatStReadPost] at hexf
                  exact Weff.consEqSome.2 ⟨_, hexf, rfl⟩
                · rw [hlt' a (wtraceWonlyTail _ _ _ hwo), wreadPostLog]
                · rw [hlog', wreadPostLog, WeakStale.wreadPostRelp]
                  rfl
          · -- THE RACY READ: the run's own value is the witness
            subst hn
            subst hpa
            subst hak
            have hrbw := wreadBytesComplete _ _ _ _ _ _ hokr
            have hadm0 := wadmDown s0 s _ _ _ v himg hlog hle hitv (wadmOfWreadOk _ _ _ _ _ _ hokr)
            have hΦv := hΦ v hadm0
            obtain ⟨yv, tv, esv, hexv, hstv⟩ := hfam v hΦv
            simp only [readBytesStaleWin _ _ v _ (wflatSt s) hracc hrk] at hexv
            obtain ⟨esv2, heev, rfl⟩ := Weff.consEqSome.1 hexv
            obtain ⟨-, -, -, hoffv⟩ :=
              traceStaleWin _ _ _ _ _ _ esv2 hrk (raccDisjIrrefl _ _ hrn) hstv
            obtain ⟨hexf, hwf', hlt', hlog'⟩ := wrunExecStaleElimOff tid _ _ _ Φ W v _
              hracc hrn hrk false (wreadPost s _ _ ts) yv tv esv2
              (by rw [wflatStReadPost]; exact heev) hoffv (hk ts v hrbw hΦv)
              (wlogWfReadPost _ _ _ _ hwf) x s' hrun
            refine ⟨v, .WEread (classify req.access_kind) req.pa n :: esv2, hadm0, hΦv, ?_, hwf',
              fun a hwo => ?_, ?_⟩
            · simp only [execStale, if_neg hd, readBytesStaleWin _ _ v _ (wflatSt s) hracc hrk]
              rw [wflatStReadPost] at hexf
              exact Weff.consEqSome.2 ⟨_, hexf, rfl⟩
            · rw [hlt' a (wtraceWonlyTail _ _ _ hwo), wreadPostLog]
            · rw [hlog', wreadPostLog, WeakStale.wreadPostRelp]
              rfl
      case memWrite n va req =>
        simp only [wstepOkRacy] at hok
        simp only [wrun] at hrun
        simp only [execStale] at hfam
        cases hv : req.value with
        | none =>
          by_cases hd : mmioAcc req.pa n = true
          · simp [hd, hv] at hrun
          · simp [hd, hv] at hrun
        | some v =>
          simp only [hv] at hok hrun hfam
          by_cases hd : mmioAcc req.pa n = true
          · rw [if_pos hd] at hok hrun
            simp only [if_pos hd] at hfam
            cases hdw : devWrite s.wmDev req.pa n v with
            | none => rw [hdw] at hrun; exact hrun.elim
            | some d' =>
              rw [hdw] at hrun
              simp only [wflatStDev, hdw] at hfam
              have := ih _ s0 (wsetDev s d') hΦ (hok d' hdw) himg hlog hle hitv hwf hrd hfam x s'
                hrun
              simp only [execStale, hv, if_pos hd, wflatStDev, hdw]
              exact this
          · -- a RAM write BEFORE the racy read: `traceStale` gives it no arm
            exfalso
            simp only [if_neg hd] at hfam
            obtain ⟨wc, -, -, hΦc⟩ := WeakStale.cohWord s0 rak ra rn Φ hwf0 hracc hΦ hrd
            obtain ⟨yc, tc, esc, hexc, hstc⟩ := hfam wc hΦc
            obtain ⟨es1, -, rfl⟩ := Weff.consEqSome.1 hexc
            simp only [traceStale] at hstc
      case barrier bk =>
        simp only [wstepOkRacy] at hok
        simp only [wrun] at hrun
        have hfam2 : ∀ u : BitVec (8 * rn), Φ (fun j => nthByte u j) →
            ∃ (y : X) (t' : ExecSt) (es : List Weff),
              execStale ra rn u (k ()) (wflatSt (wbarrierPost s bk)) = some (y, t', es) ∧
              traceStale rak ra rn es := by
          intro u hu
          obtain ⟨y1, t1, es1, hex1, hst1⟩ := hfam u hu
          simp only [execStale] at hex1
          obtain ⟨es2, hee1, rfl⟩ := Weff.consEqSome.1 hex1
          exact ⟨y1, t1, es2, hee1, hst1⟩
        obtain ⟨w, es, hadm, hΦw, hexw, hwf', hlt', hlog'⟩ := ih () s0 (wbarrierPost s bk) hΦ hok
          himg hlog (wsLeTrans hle (barrierPostLe _ _)) (Nat.le_trans hitv (itvPostLe _ _ _)) hwf hrd
          hfam2 x s' hrun
        refine ⟨w, .WEbar bk :: es, hadm, hΦw, ?_, hwf', fun a hwo => hlt' a (wtraceWonlyTail _ _ _ hwo),
          ?_⟩
        · simp only [execStale]
          exact Weff.consEqSome.2 ⟨_, hexw, rfl⟩
        · rw [hlog', wbarrierPostLog, wbarrierPostWs, WeakStale.barrierPostRelp]
          rfl
      case choose => simp only [wstepOkRacy] at hok
      case readRam => exact hrun.elim
      case writeRam => exact hrun.elim
      all_goals
        simp only [wstepOkRacy] at hok
        simp only [wrun] at hrun
        simp only [execStale] at hfam ⊢
        exact ih _ s0 s hΦ hok himg hlog hle hitv hwf hrd hfam x s' hrun

/-! ### 10c. THE ⇐-BRIDGE, as a consumer states it -/

theorem wrunExecStaleElimMsgs (tid : Option Nat) (ra : PAddr) (rn : Nat) (rak : AkInfo)
    (Φ : (Nat → BitVec 8) → Prop) (W : Prop) {X : Type} (m : SailM X) :
    accWf ra rn → 0 < rn → akPins rak = false →
    ∀ s : Wmstate,
      wstepOkRacy tid ra rn rak Φ wDAny W true m s →
      wlogWf s.wmLog →
      wadmFilter s rak ra rn Φ →
      (bmRead (wflatMem s.wmImg s.wmLog) ra rn).isSome = true →
      (∀ u : BitVec (8 * rn), Φ (fun j => nthByte u j) →
        ∃ (y : X) (t' : ExecSt) (es : List Weff),
          execStale ra rn u m (wflatSt s) = some (y, t', es) ∧ traceStale rak ra rn es) →
    ∀ (x : X) (s' : Wmstate), wrun tid m s x s' →
      ∃ (w : BitVec (8 * rn)) (es : List Weff),
        wadm s rak ra rn w ∧ Φ (fun j => nthByte w j) ∧
        execStale ra rn w m (wflatSt s) = some (x, wflatSt s', es) ∧
        wlogWf s'.wmLog ∧
        (∀ a : PAddr,
          wtraceWonly (fun pa n => ∀ j, j < n → pa + BitVec.ofNat 64 j ≠ a) es →
          latestTs s'.wmLog (paZ a) = latestTs s.wmLog (paZ a)) ∧
        s'.wmLog = s.wmLog ++ wtraceMsgs tid s.wmWs.wRelp es := by
  intro hracc hrn hrk s hok hwf hΦ hrd hfam x s' hrun
  exact wrunExecStaleElimGen tid ra rn rak Φ W m hracc hrn hrk s s hΦ hok rfl rfl (wsLeRefl _)
    (Nat.le_refl _) hwf hrd hfam x s' hrun

/-- The five-conjunct view, kept for the positional consumer (Rocq `WkFetchPeel`). -/
theorem wrunExecStaleElim (tid : Option Nat) (ra : PAddr) (rn : Nat) (rak : AkInfo)
    (Φ : (Nat → BitVec 8) → Prop) (W : Prop) {X : Type} (m : SailM X) :
    accWf ra rn → 0 < rn → akPins rak = false →
    ∀ s : Wmstate,
      wstepOkRacy tid ra rn rak Φ wDAny W true m s →
      wlogWf s.wmLog →
      wadmFilter s rak ra rn Φ →
      (bmRead (wflatMem s.wmImg s.wmLog) ra rn).isSome = true →
      (∀ u : BitVec (8 * rn), Φ (fun j => nthByte u j) →
        ∃ (y : X) (t' : ExecSt) (es : List Weff),
          execStale ra rn u m (wflatSt s) = some (y, t', es) ∧ traceStale rak ra rn es) →
    ∀ (x : X) (s' : Wmstate), wrun tid m s x s' →
      ∃ (w : BitVec (8 * rn)) (es : List Weff),
        wadm s rak ra rn w ∧ Φ (fun j => nthByte w j) ∧
        execStale ra rn w m (wflatSt s) = some (x, wflatSt s', es) ∧
        wlogWf s'.wmLog ∧
        (∀ a : PAddr,
          wtraceWonly (fun pa n => ∀ j, j < n → pa + BitVec.ofNat 64 j ≠ a) es →
          latestTs s'.wmLog (paZ a) = latestTs s.wmLog (paZ a)) := by
  intro hracc hrn hrk s hok hwf hΦ hrd hfam x s' hrun
  obtain ⟨w, es, hadm, hΦw, hexw, hwf', hlt, -⟩ :=
    wrunExecStaleElimMsgs tid ra rn rak Φ W m hracc hrn hrk s hok hwf hΦ hrd hfam x s' hrun
  exact ⟨w, es, hadm, hΦw, hexw, hwf', hlt⟩

/-- The `wexec` corollary: the FUNCTIONAL interpreter's outcomes are a fortiori covered. -/
theorem wexecExecStaleElim (tid : Option Nat) (ra : PAddr) (rn : Nat) (rak : AkInfo)
    (Φ : (Nat → BitVec 8) → Prop) (W : Prop) {X : Type} (m : SailM X) :
    accWf ra rn → 0 < rn → akPins rak = false →
    ∀ s : Wmstate,
      wstepOkRacy tid ra rn rak Φ wDAny W true m s →
      wlogWf s.wmLog →
      wadmFilter s rak ra rn Φ →
      (bmRead (wflatMem s.wmImg s.wmLog) ra rn).isSome = true →
      (∀ u : BitVec (8 * rn), Φ (fun j => nthByte u j) →
        ∃ (y : X) (t' : ExecSt) (es : List Weff),
          execStale ra rn u m (wflatSt s) = some (y, t', es) ∧ traceStale rak ra rn es) →
    ∀ (χ : List (List Nat)) (x : X) (s' : Wmstate) (χ' : List (List Nat)),
      wexec tid m χ s = some (x, s', χ') →
      ∃ (w : BitVec (8 * rn)) (es : List Weff),
        wadm s rak ra rn w ∧ Φ (fun j => nthByte w j) ∧
        execStale ra rn w m (wflatSt s) = some (x, wflatSt s', es) ∧
        wlogWf s'.wmLog ∧
        (∀ a : PAddr,
          wtraceWonly (fun pa n => ∀ j, j < n → pa + BitVec.ofNat 64 j ≠ a) es →
          latestTs s'.wmLog (paZ a) = latestTs s.wmLog (paZ a)) ∧
        s'.wmLog = s.wmLog ++ wtraceMsgs tid s.wmWs.wRelp es := by
  intro hracc hrn hrk s hok hwf hΦ hrd hfam χ x s' χ' hex
  exact wrunExecStaleElimMsgs tid ra rn rak Φ W m hracc hrn hrk s hok hwf hΦ hrd hfam x s'
    (wexecWrun tid m χ s x s' χ' hex)

/-! ### 10d. The CONSTANT-family arm, in the same shape -/

theorem wrunExecStaleElimConstMsgs (tid : Option Nat) (ra : PAddr) (rn : Nat) (rak : AkInfo)
    (Φ : (Nat → BitVec 8) → Prop) (W : Prop) (b : Bool) {X : Type} (m : SailM X) :
    accWf ra rn → 0 < rn → akPins rak = false →
    ∀ s : Wmstate,
      wstepOkRacy tid ra rn rak Φ wDAny W b m s →
      wlogWf s.wmLog →
      wadmFilter s rak ra rn Φ →
      (bmRead (wflatMem s.wmImg s.wmLog) ra rn).isSome = true →
      (∀ u : BitVec (8 * rn), Φ (fun j => nthByte u j) →
        ∃ (y : X) (t' : ExecSt) (es : List Weff),
          execStale ra rn u m (wflatSt s) = some (y, t', es) ∧ traceOffWin ra rn es) →
    ∀ (x : X) (s' : Wmstate), wrun tid m s x s' →
      ∃ (w : BitVec (8 * rn)) (es : List Weff),
        wadm s rak ra rn w ∧ Φ (fun j => nthByte w j) ∧
        execStale ra rn w m (wflatSt s) = some (x, wflatSt s', es) ∧
        wlogWf s'.wmLog ∧
        (∀ a : PAddr,
          wtraceWonly (fun pa n => ∀ j, j < n → pa + BitVec.ofNat 64 j ≠ a) es →
          latestTs s'.wmLog (paZ a) = latestTs s.wmLog (paZ a)) ∧
        s'.wmLog = s.wmLog ++ wtraceMsgs tid s.wmWs.wRelp es := by
  intro hracc hrn hrk s hok hwf hΦ hrd hfam x s' hrun
  obtain ⟨wc, -, hadmc, hΦc⟩ := WeakStale.cohWord s rak ra rn Φ hwf hracc hΦ hrd
  obtain ⟨yc, tc, esc, hexc, hoffc⟩ := hfam wc hΦc
  obtain ⟨hexf, hwf', hlt, hlog⟩ := wrunExecStaleElimOff tid ra rn rak Φ W wc m hracc hrn hrk
    b s yc tc esc hexc hoffc hok hwf x s' hrun
  exact ⟨wc, esc, hadmc, hΦc, hexf, hwf', hlt, hlog⟩

/-- The five-conjunct view, for the positional consumer. -/
theorem wrunExecStaleElimConst (tid : Option Nat) (ra : PAddr) (rn : Nat) (rak : AkInfo)
    (Φ : (Nat → BitVec 8) → Prop) (W : Prop) (b : Bool) {X : Type} (m : SailM X) :
    accWf ra rn → 0 < rn → akPins rak = false →
    ∀ s : Wmstate,
      wstepOkRacy tid ra rn rak Φ wDAny W b m s →
      wlogWf s.wmLog →
      wadmFilter s rak ra rn Φ →
      (bmRead (wflatMem s.wmImg s.wmLog) ra rn).isSome = true →
      (∀ u : BitVec (8 * rn), Φ (fun j => nthByte u j) →
        ∃ (y : X) (t' : ExecSt) (es : List Weff),
          execStale ra rn u m (wflatSt s) = some (y, t', es) ∧ traceOffWin ra rn es) →
    ∀ (x : X) (s' : Wmstate), wrun tid m s x s' →
      ∃ (w : BitVec (8 * rn)) (es : List Weff),
        wadm s rak ra rn w ∧ Φ (fun j => nthByte w j) ∧
        execStale ra rn w m (wflatSt s) = some (x, wflatSt s', es) ∧
        wlogWf s'.wmLog ∧
        (∀ a : PAddr,
          wtraceWonly (fun pa n => ∀ j, j < n → pa + BitVec.ofNat 64 j ≠ a) es →
          latestTs s'.wmLog (paZ a) = latestTs s.wmLog (paZ a)) := by
  intro hracc hrn hrk s hok hwf hΦ hrd hfam x s' hrun
  obtain ⟨w, es, hadm, hΦw, hexw, hwf', hlt, -⟩ :=
    wrunExecStaleElimConstMsgs tid ra rn rak Φ W b m hracc hrn hrk s hok hwf hΦ hrd hfam x s' hrun
  exact ⟨w, es, hadm, hΦw, hexw, hwf', hlt⟩

end Weak
