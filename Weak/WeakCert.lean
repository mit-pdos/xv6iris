/-
Weak: **discharging the step certificate** (`WeakInstr.wstepCert`, M3b item 2):
the confined-exec certificate, the instrumented interpreter `execEff` and its
effect trace, the four instruction certificates, the coherence footprint of a
trace and the trace-carrying certificates.

Rocq: `iris/WeakCert.v` @ xxvzwolszwmp (1cc222280).

The Rocq header, in substance.  The per-instruction peel `WeakBridge.wstepOk`
does not have to be walked: it is CERTIFIED BY RUNNING THE SC INTERPRETER ON A
CONFINED MEMORY.  `exec`'s RAM read arm fails on a byte the map does not hold,
so if `exec` succeeds from a state whose memory is a SMALL map `mm` (the text
bytes at the pc plus the data word), every read of the run is inside
`dom mm`; writes are confined by the domain of the FINAL memory (memory only
grows along a run); and since `mm` agrees with the real (flat) memory on its
domain, the run at `mm` and the run at the real memory are the SAME run.  So
pinnedness of a fixed window `W`, plus ONE `exec` fact re-instantiated at the
confined state, gives `wstepOk` for the whole step (`wstepOkConfined`, §5;
`wstepCertConf`, §6).  The certificate's second component `Q` (the weak-memory
EFFECT) is read off the instrumented interpreter `execEff` (§4): `exec` plus an
effect trace, one `Weff` per RAM access and per barrier; under the same
confinement the weak successor's log and views are the FOLD `weffs` of that
trace (`wstepEffConfinedPin`).  A per-instruction `Q` is then pure view
arithmetic over a two- or three-element effect list (§7, §8).  §5b′ adds the
coherence footprint of a trace (a step raises `coh` only at the bytes its trace
names) and §5c′ the trace-carrying certificates the violation-freedom conjunct
consumes.

**O2 (the i-cache fetch; owner decision, `Weak/WeakBridge.lean` header).**  In
the Lean model the fetch is an `AK_ifetch` read, view-silent, whose admissible
timestamps are forced not by its kind but by THE FETCH PIN `fetchPinned s a`
(`latestTs ≤ wmItv`); `WeakBridge.wstepOk`'s read obligation is
`readPinned s ak a` (the fetch pin at an i-cache read, `pinnedRead` otherwise).
Two consequences shape this file (deviations 3–5):
* the fetch pin, unlike `pinnedRead`, does NOT survive the hart's own write to
  the byte (the write raises `latestTs`, not `wmItv`).  The trace-keyed pin
  therefore also asks that no WRITE of the trace precedes an i-cache read of a
  byte it writes (`fetchFresh`; trivially true of every instruction trace,
  where the fetch comes first);
* the whole-window forms cannot ask `fetchPinned` of the whole window (an owned
  data byte the hart wrote since its last `fence.i` is `pinnedRead` but not
  fetch-pinned), so they keep Rocq's `pinnedRead` on `W` and add the
  trace-keyed fetch obligation `fetchPin s es` (the i-cache reads of the trace
  are fetch-pinned, and `fetchFresh`).

**Deviations from Rocq.**
1. NAMES: the tree's camelCase (map below).  File-qualified (duplicated-name
   rule): `WeakCert.paZZPa`, `WeakCert.paZRange`, `WeakCert.cohLoadPostAtNe`,
   `WeakCert.cohStorePostNe`.  Vocabulary as `Weak/WeakBridge.lean` deviation 2
   and `Weak/WeakInstr.lean` deviation 1: `pa_add a j` ↦ `a + BitVec.ofNat 64 j`,
   `n : N` ↦ `n : Nat`, `S (length l)` ↦ `l.length + 1`, `⊑` ↦ `≤`,
   `register_lookup PC` ↦ `.wmRegs .PC`, `fin_to_nat c` ↦ `c.val`,
   `MState r m d` ↦ `⟨r, m, d⟩ : ExecSt`, `mem`/`sregs`/`mdev` ↦
   `.mem`/`.regs`/`.dev`, `M X` ↦ `SailM X`, `riscv_step` ↦ `riscvStep`.
2. MAPS AND SETS: the confined map is MachCSL's function map `BMap`
   (`Weak/Exec.lean` deviation 1); `read_bytes`/`write_bytes` are
   `bmRead`/`bmWrite`; Rocq `mm ⊆ mm2` is `bmSub mm mm2` and `dom mm ⊆ W` is
   `bmDomSub mm W` (both Lean-only definitions); `x ∈ dom mm` is
   `(mm x).isSome = true`.  The window is `W : GSet PAddr` (Rocq `gset
   Arch.pa`); `wmemRestrict s W` is the flat map cut down by `if a ∈ W`
   (Rocq `filter`).  `wflat … !! a` is `wflatMem … a`.  `mapMLookupMono` is
   stated over `List.mapM` of `BMap` lookups (Lean's `bmRead` is a recursion,
   not a `mapM`).
3. O2, THE TRACE PIN: `tracePin s es` is Rocq's membership statement with the
   per-byte obligation `readPinned s ak` (Rocq `pinned_read s`), CONJOINED with
   `fetchFresh es` (header).  Hence `tracePinMono` additionally takes
   `s.wmItv ≤ s'.wmItv`, and `tracePinWrite` takes the pin of `WEwrite … :: es`
   (Rocq: of `es`, the write being the head consumed by the induction).
4. O2, THE WHOLE-WINDOW FORMS: `wstepConf`, `wstepConfEff`, `confinedTracePin`,
   `wstepEffConfined`, `wstepOkConfined` carry the Lean-only `fetchPin s es`
   next to Rocq's whole-window `pinnedRead` premise (for `wstepConf` and
   `wstepOkConfined`, whose run is an `exec` fact, as "every trace the
   instrumented run produces is fetch-pinned").
5. Stage B: the barrier effect is `wbarrierPost` (data views AND `wmItv`;
   Rocq `wset_ws s (barrier_post …)`), as in `wexec`.  The fold's image, log
   and views (all the theorems state) do not depend on `wmItv`.
6. `Weff.WEwrite` carries `v : BitVec (8 * n)` (Rocq `bv (8 * n)`); Lean's
   write request value is optional, so `execEff`'s write arm matches on it like
   `exec` (Exec deviation 3), and the MMIO test is `mmioAcc` (Exec deviation 2).
   The trace-consing in `execEff` goes through the Lean-only `Weff.cons`.
   `Weff` has no `DecidableEq` (the model's `barrier_kind` derives only `BEq`).
7. `loadPostRunGain` reads `ts[j]!` (Rocq `ts !!! j`); `loadPostFoldGain` is
   over `List.foldl` with the init first.
8. `weffsTouchFetch2`: the high half's base is `pc + BitVec.ofNat 64 2` (Rocq
   `add_vec_int pc 2`, which the Rocq proof rewrites to `pa_add pc 2`).
9. `weffTouchesDec`/`weffsTouchDec` are `instance`s; the fetch-freshness and
   fetch-pin predicates (`weffWrites`, `fetchFresh`, `fetchPin`), the step
   lemmas `wwriteMsgWritesbIff`, `latestTsWriteNe`, `execEffDet`,
   `weffTouchesIv`, `viewLeTrans`, the `BMap` helpers (`bmSub`, `bmDomSub`,
   `bmSetSub`, `bmFoldDomMono`) and `Weff.cons`/`Weff.consEqSome` are Lean-only
   (14 declarations: 110 Rocq + 14 = 124).
10. `wmem_restrict_*` are stated over the function map: `wmemRestrictSub` is
   `bmSub`, `wmemRestrictDom` is `bmDomSub`.

**Rocq → Lean name map.**  `mapM_lookup_mono` `mapMLookupMono`,
`read_bytes_mono` `readBytesMono`, `read_bytes_dom` `readBytesDom`,
`write_bytes_mono` `writeBytesMono`, `write_bytes_dom_mono` `writeBytesDomMono`,
`write_bytes_dom` `writeBytesDom`, `write_bytes_dom_sub` `writeBytesDomSub`,
`exec_dom_mono` `execDomMono`, `pinned_read_mono` `pinnedReadMono`,
`pinned_read_write` `pinnedReadWrite`, `pa_z_z_pa` `WeakCert.paZZPa`,
`pa_z_range` `WeakCert.paZRange`, `pa_z_add_wrap` `paZAddWrap`, `acc_wf_window`
`accWfWindow`, `weff` `Weff` (`WEread`/`WEwrite`/`WEbar` ↦ `Weff.WEread`/…),
`weff_apply` `weffApply`, `weffs` `weffs`, `weff_apply_read/write/bar`
`weffApplyRead/Write/Bar`, `weffs_nil/cons/cons2/cons3`
`weffsNil/Cons/Cons2/Cons3`, `wwrite_post_ws` `wwritePostWs`,
`wread_post_ws_weak` `wreadPostWsWeak`, `coh_ts_log` `cohTsLog`,
`weff_apply_img` `weffApplyImg`, `weffs_img` `weffsImg`, `weff_apply_ws_le`
`weffApplyWsLe`, `weffs_ws_le` `weffsWsLe`, `weff_apply_log_app`
`weffApplyLogApp`, `weffs_log_app` `weffsLogApp`, `weff_apply_congr`
`weffApplyCongr`, `weffs_congr` `weffsCongr`, `weffs_transport`
`weffsTransport`, `exec_eff` `execEff`, `exec_eff_exec` `execEffExec`,
`exec_exec_eff` `execExecEff`, `trace_pin` `tracePin`, `trace_pin_mono`
`tracePinMono`, `trace_pin_write` `tracePinWrite`, `trace_pin_tail`
`tracePinTail`, `wstep_eff_confined_pin` `wstepEffConfinedPin`,
`exec_eff_reads_dom` `execEffReadsDom`, `confined_trace_pin`
`confinedTracePin`, `wstep_eff_confined` `wstepEffConfined`,
`wstep_ok_confined` `wstepOkConfined`, `wmem_restrict` `wmemRestrict`,
`wmem_restrict_sub/dom/lookup` `wmemRestrictSub/Dom/Lookup`, `wstep_conf`
`wstepConf`, `wP_conf` `wPConf`, `wstep_ok_conf` `wstepOkConf`,
`wstep_cert_conf` `wstepCertConf`, `wstep_cert_conf_none`
`wstepCertConfNone`, `wstep_cert_of_conf` `wstepCertOfConf`,
`wstep_conf_eff_pin` `wstepConfEffPin`, `wP_eff_pin` `wPEffPin`,
`wP_eff_pin_of_window` `wPEffPinOfWindow`, `wstep_cert_eff_pin`
`wstepCertEffPin`, `wstep_conf_eff` `wstepConfEff`, `wP_eff` `wPEff`,
`wP_eff_conf` `wPEffConf`, `wP_eff_pin_of_eff` `wPEffPinOfEff`,
`wstep_cert_eff` `wstepCertEff`, `wm_ws_wset_ws` `wmWsWsetWs`,
`fence_post_mono` `fencePostMono`, `barrier_post_mono` `barrierPostMono`,
`load_post_fold_gain` `loadPostFoldGain`, `load_post_run_gain`
`loadPostRunGain`, `wcert_fence` `wcertFence`, `wcert_store` `wcertStore`,
`wcert_amo_aq` `wcertAmoAq`, `wcert_load` `wcertLoad`, `wcert_amo_aq_pin`
`wcertAmoAqPin`, `weff_touches` `weffTouches`, `weffs_touch` `weffsTouch`,
`weff_touches_dec` `weffTouchesDec`, `weffs_touch_dec` `weffsTouchDec`,
`weffs_touch_cons/app/nil/read1/write1` `weffsTouchCons/App/Nil/Read1/Write1`,
`weffs_touch_read1_4` `weffsTouchRead14`, `weffs_touch_fetch2`
`weffsTouchFetch2`, `coh_load_post_at_ne` `WeakCert.cohLoadPostAtNe`,
`coh_store_post_ne` `WeakCert.cohStorePostNe`, `coh_foldl_load_ne`
`cohFoldlLoadNe`, `coh_load_post_bytes_ne` `cohLoadPostBytesNe`,
`coh_foldl_store_ne` `cohFoldlStoreNe`, `coh_store_post_bytes_ne`
`cohStorePostBytesNe`, `coh_load_post_run_ne` `cohLoadPostRunNe`,
`coh_store_post_run_ne` `cohStorePostRunNe`, `weff_apply_coh_frame`
`weffApplyCohFrame`, `weffs_coh_frame` `weffsCohFrame`, `weffs_log_own`
`weffsLogOwn`, `nv_hart_weffs` `nvHartWeffs`, `wQ_eff` `wQEff`, `wQ_fr` `wQFr`,
`wcert_eff` `wcertEff`, `wstep_cert_pair` `wstepCertPair`, `wstep_cert_fr`
`wstepCertFr`, `wcert_eff_pin` `wcertEffPin`, `wstep_cert_fr_pin`
`wstepCertFrPin`, `nv_hart_of_wQ_eff(_ok/_unwritten)`
`nvHartOfWQEff(Ok/Unwritten)`.

**Dropped:** nothing -- every Rocq definition and lemma has a Lean twin.

**Statements checked** (by hand, against Rocq): all; the changed ones are listed
under the deviations.
-/
import Weak.WeakInstr
import MachCSL.StdppSet

namespace Weak

open Iris Iris.Std
open MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open Sail.ArchSem (FreeM)
open LeanRV64D LeanRV64D.Functions

/-! ## 1. The two memory primitives under map inclusion -/

/-- Rocq `mm ⊆ mm2` for a byte map (deviation 2). -/
def bmSub (mm mm2 : BMap) : Prop := ∀ a b, mm a = some b → mm2 a = some b

/-- Rocq `dom mm ⊆ W` for a byte map (deviation 2). -/
def bmDomSub (mm : BMap) (W : GSet PAddr) : Prop := ∀ a, (mm a).isSome = true → a ∈ W

theorem mapMLookupMono (mm mm2 : BMap) (pa : PAddr) (l : List Nat) (bs : List (BitVec 8)) :
    bmSub mm mm2 →
    l.mapM (fun j : Nat => mm (pa + BitVec.ofNat 64 j)) = some bs →
    l.mapM (fun j : Nat => mm2 (pa + BitVec.ofNat 64 j)) = some bs := by
  intro hsub hm
  exact mapM_Some_2 (Forall2_impl (mapM_Some_1 hm) fun _ _ hj => hsub _ _ hj)

theorem readBytesMono (mm mm2 : BMap) (pa : PAddr) (n : Nat) (w : BitVec (8 * n)) :
    bmSub mm mm2 → bmRead mm pa n = some w → bmRead mm2 pa n = some w := by
  intro hsub hr
  have h2 : ∀ j, j < n → mm2 (pa + BitVec.ofNat 64 j) = some (nthByte w j) :=
    fun j hj => hsub _ _ (bmRead_spec mm pa n w hr j hj)
  rw [bmReadAssemble mm2 pa n (nthByte w) h2]
  congr 1
  apply bvEqOfBytes
  intro j hj
  rw [nthByteAssembleBytes n _ j hj]

/-- Every byte of a successful read is IN the map. -/
theorem readBytesDom (mm : BMap) (pa : PAddr) (n : Nat) (w : BitVec (8 * n)) :
    bmRead mm pa n = some w → ∀ j, j < n → (mm (pa + BitVec.ofNat 64 j)).isSome = true := by
  intro hr j hj
  rw [bmRead_spec mm pa n w hr j hj]
  rfl

theorem bmSetSub (mm mm2 : BMap) (a : PAddr) (b : BitVec 8) :
    bmSub mm mm2 → bmSub (bmSet mm a b) (bmSet mm2 a b) := by
  intro hs a' b' h
  simp only [bmSet] at h ⊢
  by_cases e : a' = a
  · rw [if_pos e] at h ⊢; exact h
  · rw [if_neg e] at h ⊢; exact hs _ _ h

theorem writeBytesMono (mm mm2 : BMap) (pa : PAddr) (n : Nat) (v : BitVec (8 * n)) :
    bmSub mm mm2 → bmSub (bmWrite mm pa n v) (bmWrite mm2 pa n v) := by
  unfold bmWrite
  generalize List.range n = l
  induction l generalizing mm mm2 with
  | nil => intro h; exact h
  | cons j l ih =>
    intro h
    simp only [List.foldl_cons]
    exact ih _ _ (bmSetSub _ _ _ _ h)

theorem bmFoldDomMono (pa : PAddr) (g : Nat → BitVec 8) :
    ∀ (l : List Nat) (m : BMap) (a : PAddr), (m a).isSome = true →
      ((l.foldl (fun m j => bmSet m (pa + BitVec.ofNat 64 j) (g j)) m) a).isSome = true := by
  intro l
  induction l with
  | nil => intro m a h; exact h
  | cons j l ih =>
    intro m a h
    simp only [List.foldl_cons]
    apply ih
    simp only [bmSet]
    split
    · rfl
    · exact h

theorem writeBytesDomMono (mm : BMap) (pa : PAddr) (n : Nat) (v : BitVec (8 * n)) :
    ∀ a, (mm a).isSome = true → (bmWrite mm pa n v a).isSome = true :=
  fun a h => bmFoldDomMono pa (nthByte v) _ mm a h

theorem writeBytesDom (mm : BMap) (pa : PAddr) (n : Nat) (v : BitVec (8 * n)) :
    ∀ j, j < n → (bmWrite mm pa n v (pa + BitVec.ofNat 64 j)).isSome = true := by
  intro j hj
  unfold bmWrite
  have hin : j ∈ List.range n := List.mem_range.2 hj
  revert hin
  generalize List.range n = l
  induction l generalizing mm with
  | nil => intro h; cases h
  | cons j0 l ih =>
    intro h
    simp only [List.foldl_cons]
    rcases List.mem_cons.1 h with rfl | h
    · apply bmFoldDomMono
      simp only [bmSet]
      simp
    · exact ih _ h

/-- The SUBSET form: a write whose base map and footprint both live in `X`
stays inside `X`. -/
theorem writeBytesDomSub (mm : BMap) (pa : PAddr) (n : Nat) (v : BitVec (8 * n)) (X : GSet PAddr) :
    bmDomSub mm X → (∀ j, j < n → pa + BitVec.ofNat 64 j ∈ X) → bmDomSub (bmWrite mm pa n v) X := by
  intro hbase hin
  unfold bmWrite
  have hin' : ∀ j, j ∈ List.range n → pa + BitVec.ofNat 64 j ∈ X :=
    fun j hj => hin j (List.mem_range.1 hj)
  revert hin'
  generalize List.range n = l
  induction l generalizing mm with
  | nil => intro _; exact hbase
  | cons j l ih =>
    intro hin'
    simp only [List.foldl_cons]
    apply ih
    · intro a ha
      simp only [bmSet] at ha
      split at ha
      · rename_i e; rw [e]; exact hin' j List.mem_cons_self
      · exact hbase a ha
    · exact fun j' hj' => hin' j' (List.mem_cons_of_mem _ hj')

/-- MEMORY ONLY GROWS along an `exec` run. -/
theorem execDomMono {X : Type} (m : SailM X) :
    ∀ s x s', exec m s = some (x, s') → ∀ a, (s.mem a).isSome = true → (s'.mem a).isSome = true := by
  induction m with
  | pure y =>
    intro s x s' h a ha
    simp only [exec, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact ha
  | impure call k ih =>
    intro s x s' h a ha
    cases call with
    | error e => simp [exec] at h
    | ok o =>
      cases o
      case memRead n va req =>
        simp only [exec] at h
        by_cases hd : mmioAcc req.pa n = true
        · rw [if_pos hd] at h
          cases hdr : devRead s.dev req.pa n with
          | none => simp only [hdr] at h; cases h
          | some p =>
            obtain ⟨w0, d0⟩ := p
            simp only [hdr] at h
            exact ih _ _ _ _ h a ha
        · rw [if_neg hd] at h
          cases hrb : bmRead s.mem req.pa n with
          | none => simp only [hrb] at h; cases h
          | some w0 =>
            simp only [hrb] at h
            exact ih _ _ _ _ h a ha
      case memWrite n va req =>
        simp only [exec] at h
        cases hv : req.value with
        | none => simp only [hv] at h; cases h
        | some w =>
          simp only [hv] at h
          by_cases hd : mmioAcc req.pa n = true
          · rw [if_pos hd] at h
            cases hdw : devWrite s.dev req.pa n w with
            | none => simp only [hdw] at h; cases h
            | some d0 =>
              simp only [hdw] at h
              exact ih _ _ _ _ h a ha
          · rw [if_neg hd] at h
            exact ih _ _ _ _ h a (writeBytesDomMono s.mem req.pa n w a ha)
      all_goals first
        | (simp only [exec, reduceCtorEq] at h; done)
        | (simp only [exec] at h; exact ih _ _ _ _ h a ha)

/-! ## 2. Pinnedness survives the run -/

theorem pinnedReadMono (s s' : Wmstate) (a : Int) :
    s'.wmLog = s.wmLog → wsLe s.wmWs s'.wmWs → pinnedRead s a → pinnedRead s' a := by
  intro hl hle hp
  unfold pinnedRead at hp ⊢
  rw [hl]
  have h1 := hle.1 a
  have h2 := hle.2.2.2.1
  omega

/-- Which bytes the written message writes (Lean helper). -/
theorem wwriteMsgWritesbIff (tid : Option Nat) (k : WmClass) (pa : PAddr) (n : Nat)
    (v : BitVec (8 * n)) (a : Int) :
    msgWritesb (wwriteMsg tid k pa n v) a = true ↔ ∃ j, j < n ∧ a = WeakInterp.accAddr pa j := by
  rw [msgWritesbTrue]
  simp only [msgByte, wwriteMsg, WeakInterp.accAddr]
  constructor
  · intro h
    by_cases h1 : paZ pa ≤ a
    · rw [if_pos h1] at h
      refine ⟨(a - paZ pa).toNat, ?_, by omega⟩
      have hh := h
      rw [List.getElem?_map] at hh
      cases hlk : (List.range' 0 n)[(a - paZ pa).toNat]? with
      | none => rw [hlk] at hh; cases hh
      | some x =>
        have := lookup_lt_Some hlk
        simpa using this
    · rw [if_neg h1] at h; cases h
  · rintro ⟨j, hj, rfl⟩
    rw [if_pos (by omega)]
    have e : (paZ pa + (j : Int) - paZ pa).toNat = j := by omega
    rw [e, List.getElem?_map]
    simp [hj]

/-- A write that does not touch `a` leaves its latest timestamp alone (Lean helper). -/
theorem latestTsWriteNe (tid : Option Nat) (s : Wmstate) (ak : AkInfo) (pa : PAddr) (n : Nat)
    (v : BitVec (8 * n)) (a : Int) :
    ¬ (∃ j, j < n ∧ a = WeakInterp.accAddr pa j) →
    latestTs (wwritePost tid s ak pa n v).wmLog a = latestTs s.wmLog a := by
  intro hno
  rw [wwritePostLog, latestTsApp]
  have : msgWritesb (wwriteMsg tid (wmClassOf ak s.wmWs) pa n v) a = false := by
    cases h : msgWritesb (wwriteMsg tid (wmClassOf ak s.wmWs) pa n v) a with
    | false => rfl
    | true => exact absurd ((wwriteMsgWritesbIff _ _ _ _ _ _).1 h) hno
  rw [this]
  rfl

/-- The write case (`t ≤ coh` at every byte the store touches is
`WeakMem.storePostRunCoh`). -/
theorem pinnedReadWrite (tid : Option Nat) (s : Wmstate) (ak : AkInfo) (pa : PAddr) (n : Nat)
    (v : BitVec (8 * n)) (a : Int) :
    pinnedRead s a → pinnedRead (wwritePost tid s ak pa n v) a := by
  intro hp
  unfold pinnedRead at hp ⊢
  rw [wwritePostLog, latestTsApp]
  cases hw : msgWritesb (wwriteMsg tid (wmClassOf ak s.wmWs) pa n v) a with
  | true =>
    obtain ⟨j, hj, rfl⟩ := (wwriteMsgWritesbIff _ _ _ _ _ _).1 hw
    have hc := storePostRunCoh s.wmWs ak.akSync (paZ pa) n (s.wmLog.length + 1) j hj
    simp only [if_true]
    show s.wmLog.length + 1 ≤
      max (storePostRun s.wmWs ak.akSync (paZ pa) n (s.wmLog.length + 1)).wVrNew
        (coh (storePostRun s.wmWs ak.akSync (paZ pa) n (s.wmLog.length + 1)) (paZ pa + (j : Int)))
    omega
  | false =>
    have hle := storePostRunLe s.wmWs ak.akSync (paZ pa) n (s.wmLog.length + 1)
    have h1 := hle.1 a
    have h2 := hle.2.2.2.1
    show latestTs s.wmLog a ≤
      max (storePostRun s.wmWs ak.akSync (paZ pa) n (s.wmLog.length + 1)).wVrNew
        (coh (storePostRun s.wmWs ak.akSync (paZ pa) n (s.wmLog.length + 1)) a)
    omega

/-! ## 3. Wrap-freedom out of the window -/

theorem WeakCert.paZZPa (z : Int) : paZ (zPa z) = z % 18446744073709551616 := by
  simp only [paZ, zPa, BitVec.toNat_ofInt]
  omega

theorem WeakCert.paZRange (a : PAddr) : 0 ≤ paZ a ∧ paZ a < 18446744073709551616 :=
  WeakInterp.paZRange a

theorem paZAddWrap (pa : PAddr) (j : Nat) :
    paZ (pa + BitVec.ofNat 64 j) = (paZ pa + (j : Int)) % 18446744073709551616 := by
  simp only [paZ, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem accWfWindow (W : GSet PAddr) (pa : PAddr) (n : Nat) :
    (∀ a, a ∈ W → paZ a ≠ 0) →
    (∀ j, j < n → pa + BitVec.ofNat 64 j ∈ W) →
    accWf pa n := by
  intro hW hin
  unfold accWf
  apply Classical.byContradiction
  intro hgt
  have hr := pa.isLt
  have hj0 : 18446744073709551616 - pa.toNat < n := by
    simp only [paZ] at hgt; omega
  apply hW _ (hin _ hj0)
  simp only [paZ, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

/-! ## 4. THE EFFECT TRACE, and the instrumented SC interpreter -/

/-- One weak-memory-relevant thing a run does (Rocq `weff`). -/
inductive Weff where
  | WEread (ak : AkInfo) (pa : PAddr) (n : Nat)
  | WEwrite (ak : AkInfo) (pa : PAddr) (n : Nat) (v : BitVec (8 * n))
  | WEbar (b : barrier_kind)

/-- Rocq `weff_apply` (deviation 5: the barrier is `wbarrierPost`). -/
def weffApply (tid : Option Nat) (s : Wmstate) : Weff → Wmstate
  | .WEread ak pa n => wreadPost s ak pa (cohTs s pa n)
  | .WEwrite ak pa n v => wwritePost tid s ak pa n v
  | .WEbar b => wbarrierPost s b

def weffs (tid : Option Nat) (s : Wmstate) (es : List Weff) : Wmstate :=
  es.foldl (weffApply tid) s

theorem weffApplyRead (tid : Option Nat) (s : Wmstate) (ak : AkInfo) (pa : PAddr) (n : Nat) :
    weffApply tid s (.WEread ak pa n) = wreadPost s ak pa (cohTs s pa n) := rfl
theorem weffApplyWrite (tid : Option Nat) (s : Wmstate) (ak : AkInfo) (pa : PAddr) (n : Nat)
    (v : BitVec (8 * n)) : weffApply tid s (.WEwrite ak pa n v) = wwritePost tid s ak pa n v := rfl
theorem weffApplyBar (tid : Option Nat) (s : Wmstate) (b : barrier_kind) :
    weffApply tid s (.WEbar b) = wbarrierPost s b := rfl

theorem weffsNil (tid : Option Nat) (s : Wmstate) : weffs tid s [] = s := rfl
theorem weffsCons (tid : Option Nat) (s : Wmstate) (e : Weff) (es : List Weff) :
    weffs tid s (e :: es) = weffs tid (weffApply tid s e) es := rfl
theorem weffsCons2 (tid : Option Nat) (s : Wmstate) (e1 e2 : Weff) :
    weffs tid s [e1, e2] = weffApply tid (weffApply tid s e1) e2 := rfl
theorem weffsCons3 (tid : Option Nat) (s : Wmstate) (e1 e2 e3 : Weff) :
    weffs tid s [e1, e2, e3] = weffApply tid (weffApply tid (weffApply tid s e1) e2) e3 := rfl

theorem wwritePostWs (tid : Option Nat) (s : Wmstate) (ak : AkInfo) (pa : PAddr) (n : Nat)
    (v : BitVec (8 * n)) :
    (wwritePost tid s ak pa n v).wmWs = storePostRun s.wmWs ak.akSync (paZ pa) n (s.wmLog.length + 1) :=
  rfl

theorem wreadPostWsWeak (s : Wmstate) (ak : AkInfo) (pa : PAddr) (ts : List Nat) :
    ak.akIfetch = false → (wreadPost s ak pa ts).wmWs = loadPostRun s.wmWs ak.akSync (paZ pa) ts := by
  intro h
  unfold wreadPost
  rw [if_neg (by simp [h])]
  rfl

theorem cohTsLog (s1 s2 : Wmstate) (pa : PAddr) (n : Nat) :
    s1.wmLog = s2.wmLog → cohTs s1 pa n = cohTs s2 pa n := by
  intro h; unfold cohTs; rw [h]

theorem weffApplyImg (tid : Option Nat) (s : Wmstate) (e : Weff) : (weffApply tid s e).wmImg = s.wmImg := by
  cases e with
  | WEread ak pa n => exact wreadPostImg _ _ _ _
  | WEwrite => rfl
  | WEbar => rfl

theorem weffsImg (tid : Option Nat) (s : Wmstate) (es : List Weff) : (weffs tid s es).wmImg = s.wmImg := by
  induction es generalizing s with
  | nil => rfl
  | cons e es ih => rw [weffsCons, ih]; exact weffApplyImg _ _ _

theorem weffApplyWsLe (tid : Option Nat) (s : Wmstate) (e : Weff) : wsLe s.wmWs (weffApply tid s e).wmWs := by
  cases e with
  | WEread ak pa n => exact wreadPostWsLe _ _ _ _
  | WEwrite ak pa n v => exact wwritePostWsLe _ _ _ _ _ _
  | WEbar b => exact barrierPostLe _ _

theorem weffsWsLe (tid : Option Nat) (s : Wmstate) (es : List Weff) : wsLe s.wmWs (weffs tid s es).wmWs := by
  induction es generalizing s with
  | nil => exact wsLeRefl _
  | cons e es ih => rw [weffsCons]; exact wsLeTrans (weffApplyWsLe _ _ _) (ih _)

theorem weffApplyLogApp (tid : Option Nat) (s : Wmstate) (e : Weff) :
    ∃ l : List Wmsg, (weffApply tid s e).wmLog = s.wmLog ++ l := by
  cases e with
  | WEread ak pa n => exact ⟨[], by rw [weffApplyRead, wreadPostLog, List.append_nil]⟩
  | WEwrite ak pa n v => exact ⟨_, rfl⟩
  | WEbar b => exact ⟨[], by rw [List.append_nil]; rfl⟩

theorem weffsLogApp (tid : Option Nat) (s : Wmstate) (es : List Weff) :
    ∃ l : List Wmsg, (weffs tid s es).wmLog = s.wmLog ++ l := by
  induction es generalizing s with
  | nil => exact ⟨[], by rw [List.append_nil]; rfl⟩
  | cons e es ih =>
    rw [weffsCons]
    obtain ⟨l1, h1⟩ := weffApplyLogApp tid s e
    obtain ⟨l2, h2⟩ := ih (weffApply tid s e)
    exact ⟨l1 ++ l2, by rw [h2, h1, List.append_assoc]⟩

/-- THE CONGRUENCE: the fold only looks at the image, the log and the views. -/
theorem weffApplyCongr (tid : Option Nat) (s1 s2 : Wmstate) (e : Weff) :
    s1.wmImg = s2.wmImg → s1.wmLog = s2.wmLog → s1.wmWs = s2.wmWs →
    (weffApply tid s1 e).wmImg = (weffApply tid s2 e).wmImg ∧
    (weffApply tid s1 e).wmLog = (weffApply tid s2 e).wmLog ∧
    (weffApply tid s1 e).wmWs = (weffApply tid s2 e).wmWs := by
  intro hi hl hw
  cases e with
  | WEread ak pa n =>
    rw [weffApplyRead, weffApplyRead, cohTsLog s1 s2 pa n hl]
    unfold wreadPost
    cases ak.akIfetch <;> simp [wsetWs, hi, hl, hw]
  | WEwrite ak pa n v =>
    refine ⟨hi, ?_, ?_⟩ <;> simp only [weffApplyWrite, wwritePost, hl, hw]
  | WEbar b =>
    exact ⟨hi, hl, by simp only [weffApplyBar, wbarrierPostWs, hw]⟩

theorem weffsCongr (tid : Option Nat) (s1 s2 : Wmstate) (es : List Weff) :
    s1.wmImg = s2.wmImg → s1.wmLog = s2.wmLog → s1.wmWs = s2.wmWs →
    (weffs tid s1 es).wmImg = (weffs tid s2 es).wmImg ∧
    (weffs tid s1 es).wmLog = (weffs tid s2 es).wmLog ∧
    (weffs tid s1 es).wmWs = (weffs tid s2 es).wmWs := by
  induction es generalizing s1 s2 with
  | nil => intro hi hl hw; exact ⟨hi, hl, hw⟩
  | cons e es ih =>
    intro hi hl hw
    rw [weffsCons, weffsCons]
    obtain ⟨hi', hl', hw'⟩ := weffApplyCongr tid s1 s2 e hi hl hw
    exact ih _ _ hi' hl' hw'

theorem weffsTransport (tid : Option Nat) (s1 s2 : Wmstate) (es : List Weff) (s' : Wmstate) :
    s1.wmImg = s2.wmImg → s1.wmLog = s2.wmLog → s1.wmWs = s2.wmWs →
    (s'.wmImg = s2.wmImg ∧ s'.wmLog = (weffs tid s2 es).wmLog ∧ s'.wmWs = (weffs tid s2 es).wmWs) →
    s'.wmImg = s1.wmImg ∧ s'.wmLog = (weffs tid s1 es).wmLog ∧ s'.wmWs = (weffs tid s1 es).wmWs := by
  rintro hi hl hw ⟨hi', hl', hw'⟩
  obtain ⟨_, hl2, hw2⟩ := weffsCongr tid s1 s2 es hi hl hw
  exact ⟨by rw [hi', hi], by rw [hl', hl2], by rw [hw', hw2]⟩

/-- Cons an effect onto a successful instrumented run (Lean helper). -/
def Weff.cons {X : Type} (e : Weff) : Option (X × ExecSt × List Weff) → Option (X × ExecSt × List Weff)
  | some (y, s', es) => some (y, s', e :: es)
  | none => none

theorem Weff.consEqSome {X : Type} {e : Weff} {r : Option (X × ExecSt × List Weff)} {y : X}
    {s' : ExecSt} {es' : List Weff} :
    Weff.cons e r = some (y, s', es') ↔ ∃ es, r = some (y, s', es) ∧ es' = e :: es := by
  cases r with
  | none => simp [Weff.cons]
  | some p =>
    obtain ⟨y0, s0, es0⟩ := p
    simp only [Weff.cons, Option.some.injEq, Prod.mk.injEq]
    constructor
    · rintro ⟨rfl, rfl, rfl⟩; exact ⟨es0, ⟨rfl, rfl, rfl⟩, rfl⟩
    · rintro ⟨es, ⟨rfl, rfl, rfl⟩, rfl⟩; exact ⟨rfl, rfl, rfl⟩

/-- **The instrumented interpreter** (Rocq `exec_eff`): `exec`, arm for arm, with
the effect trace threaded. -/
def execEff {X : Type} : SailM X → ExecSt → Option (X × ExecSt × List Weff)
  | .pure x, s => some (x, s, [])
  | .impure (.error _) _, _ => none
  | .impure (.ok o) k, s =>
    match o, k with
    | .regRead r, k => execEff (k (s.regs r)) s
    | .regWrite r v, k => execEff (k PUnit.unit) (s.setReg r v)
    | .memRead n _ req, k =>
      if mmioAcc req.pa n then
        match devRead s.dev req.pa n with
        | some (w, d') => execEff (k (.Ok (w, none))) (s.setDev d')
        | none => none
      else
        match bmRead s.mem req.pa n with
        | some w =>
          Weff.cons (.WEread (classify req.access_kind) req.pa n) (execEff (k (.Ok (w, none))) s)
        | none => none
    | .memWrite n _ req, k =>
      match req.value with
      | none => none
      | some w =>
        if mmioAcc req.pa n then
          match devWrite s.dev req.pa n w with
          | some d' => execEff (k (.Ok (some true))) (s.setDev d')
          | none => none
        else
          Weff.cons (.WEwrite (classify req.access_kind) req.pa n w)
            (execEff (k (.Ok (some true))) (s.setMem (bmWrite s.mem req.pa n w)))
    | .barrier b, k => Weff.cons (.WEbar b) (execEff (k ()) s)
    | .cacheOp _, k => execEff (k ()) s
    | .tlbi _, k => execEff (k ()) s
    | .translationStart _, k => execEff (k ()) s
    | .translationEnd _, k => execEff (k ()) s
    | .takeException _, k => execEff (k ()) s
    | .returnException _, k => execEff (k ()) s
    | .cycleCount, k => execEff (k ()) s
    | .getCycleCount, k => execEff (k (0 : Nat)) s
    | .message _, k => execEff (k ()) s
    | .instrAnnounce _ _, k => execEff (k ()) s
    | .branchAnnounce _ _, k => execEff (k ()) s
    | .choose _, _ => none
    | .readRam .., _ => none
    | .writeRam .., _ => none

theorem execEffExec {X : Type} (m : SailM X) :
    ∀ s x s' es, execEff m s = some (x, s', es) → exec m s = some (x, s') := by
  induction m with
  | pure y =>
    intro s x s' es h
    simp only [execEff, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, -⟩ := h
    rfl
  | impure call k ih =>
    intro s x s' es h
    cases call with
    | error e => simp [execEff] at h
    | ok o =>
      cases o
      case memRead n va req =>
        simp only [execEff] at h
        simp only [exec]
        by_cases hd : mmioAcc req.pa n = true
        · rw [if_pos hd] at h ⊢
          cases hdr : devRead s.dev req.pa n with
          | none => simp only [hdr] at h; cases h
          | some p =>
            obtain ⟨w0, d0⟩ := p
            simp only [hdr] at h ⊢
            exact ih _ _ _ _ _ h
        · rw [if_neg hd] at h ⊢
          cases hrb : bmRead s.mem req.pa n with
          | none => simp only [hrb] at h; cases h
          | some w0 =>
            simp only [hrb] at h ⊢
            obtain ⟨es0, h0, -⟩ := Weff.consEqSome.1 h
            exact ih _ _ _ _ _ h0
      case memWrite n va req =>
        simp only [execEff] at h
        simp only [exec]
        cases hv : req.value with
        | none => simp only [hv] at h; cases h
        | some w =>
          simp only [hv] at h ⊢
          by_cases hd : mmioAcc req.pa n = true
          · rw [if_pos hd] at h ⊢
            cases hdw : devWrite s.dev req.pa n w with
            | none => simp only [hdw] at h; cases h
            | some d0 =>
              simp only [hdw] at h ⊢
              exact ih _ _ _ _ _ h
          · rw [if_neg hd] at h ⊢
            obtain ⟨es0, h0, -⟩ := Weff.consEqSome.1 h
            exact ih _ _ _ _ _ h0
      case barrier b =>
        simp only [execEff] at h
        simp only [exec]
        obtain ⟨es0, h0, -⟩ := Weff.consEqSome.1 h
        exact ih _ _ _ _ _ h0
      all_goals first
        | (simp only [execEff, reduceCtorEq] at h; done)
        | (simp only [execEff] at h; simp only [exec]; exact ih _ _ _ _ _ h)

theorem execExecEff {X : Type} (m : SailM X) :
    ∀ s x s', exec m s = some (x, s') → ∃ es, execEff m s = some (x, s', es) := by
  induction m with
  | pure y =>
    intro s x s' h
    simp only [exec, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨[], rfl⟩
  | impure call k ih =>
    intro s x s' h
    cases call with
    | error e => simp [exec] at h
    | ok o =>
      cases o
      case memRead n va req =>
        simp only [exec] at h
        simp only [execEff]
        by_cases hd : mmioAcc req.pa n = true
        · rw [if_pos hd] at h ⊢
          cases hdr : devRead s.dev req.pa n with
          | none => simp only [hdr] at h; cases h
          | some p =>
            obtain ⟨w0, d0⟩ := p
            simp only [hdr] at h ⊢
            exact ih _ _ _ _ h
        · rw [if_neg hd] at h ⊢
          cases hrb : bmRead s.mem req.pa n with
          | none => simp only [hrb] at h; cases h
          | some w0 =>
            simp only [hrb] at h ⊢
            obtain ⟨es0, h0⟩ := ih _ _ _ _ h
            exact ⟨_, Weff.consEqSome.2 ⟨es0, h0, rfl⟩⟩
      case memWrite n va req =>
        simp only [exec] at h
        simp only [execEff]
        cases hv : req.value with
        | none => simp only [hv] at h; cases h
        | some w =>
          simp only [hv] at h ⊢
          by_cases hd : mmioAcc req.pa n = true
          · rw [if_pos hd] at h ⊢
            cases hdw : devWrite s.dev req.pa n w with
            | none => simp only [hdw] at h; cases h
            | some d0 =>
              simp only [hdw] at h ⊢
              exact ih _ _ _ _ h
          · rw [if_neg hd] at h ⊢
            obtain ⟨es0, h0⟩ := ih _ _ _ _ h
            exact ⟨_, Weff.consEqSome.2 ⟨es0, h0, rfl⟩⟩
      case barrier b =>
        simp only [exec] at h
        simp only [execEff]
        obtain ⟨es0, h0⟩ := ih _ _ _ _ h
        exact ⟨_, Weff.consEqSome.2 ⟨es0, h0, rfl⟩⟩
      all_goals first
        | (simp only [exec, reduceCtorEq] at h; done)
        | (simp only [exec] at h; simp only [execEff]; exact ih _ _ _ _ h)

/-- The instrumented run is a function (Lean helper). -/
theorem execEffDet {X : Type} (m : SailM X) (s : ExecSt) (x1 x2 : X) (t1 t2 : ExecSt)
    (es1 es2 : List Weff) :
    execEff m s = some (x1, t1, es1) → execEff m s = some (x2, t2, es2) → es1 = es2 := by
  intro h1 h2
  rw [h1] at h2
  simp only [Option.some.injEq, Prod.mk.injEq] at h2
  exact h2.2.2

/-! ## 5. THE CONFINED-EXEC CERTIFICATE

### 5a. `tracePin` -- pinnedness, keyed on the TRACE (deviation 3) -/

/-- The bytes a WRITE effect writes (Lean helper). -/
def weffWrites (e : Weff) (a : Int) : Prop :=
  match e with
  | .WEwrite _ pa n _ => ∃ j, j < n ∧ a = WeakInterp.accAddr pa j
  | _ => False

/-- O2: no write of the trace precedes an i-cache read of a byte it writes
(Lean-only; every instruction trace fetches first). -/
def fetchFresh : List Weff → Prop
  | [] => True
  | e :: es =>
    (∀ (ak : AkInfo) (pa : PAddr) (n : Nat), Weff.WEread ak pa n ∈ es → ak.akIfetch = true →
      ∀ j, j < n → ¬ weffWrites e (WeakInterp.accAddr pa j)) ∧ fetchFresh es

/-- THE PRIMARY CONFINEMENT PREMISE (Rocq `trace_pin`; O2: `readPinned`, plus
`fetchFresh`). -/
def tracePin (s : Wmstate) (es : List Weff) : Prop :=
  (∀ (ak : AkInfo) (pa : PAddr) (n : Nat), Weff.WEread ak pa n ∈ es → akPins ak = false →
    ∀ j, j < n → readPinned s ak (WeakInterp.accAddr pa j)) ∧
  fetchFresh es

/-- The i-cache half of `tracePin`, for the whole-window forms (Lean-only,
deviation 4). -/
def fetchPin (s : Wmstate) (es : List Weff) : Prop :=
  (∀ (ak : AkInfo) (pa : PAddr) (n : Nat), Weff.WEread ak pa n ∈ es → ak.akIfetch = true →
    ∀ j, j < n → fetchPinned s (WeakInterp.accAddr pa j)) ∧
  fetchFresh es

theorem tracePinMono (s s' : Wmstate) (es : List Weff) :
    s'.wmLog = s.wmLog → wsLe s.wmWs s'.wmWs → s.wmItv ≤ s'.wmItv →
    tracePin s es → tracePin s' es := by
  rintro hl hle hitv ⟨hp, hf⟩
  refine ⟨fun ak pa n hin hnp j hj => ?_, hf⟩
  have h0 := hp ak pa n hin hnp j hj
  unfold readPinned at h0 ⊢
  by_cases hif : ak.akIfetch = true
  · rw [if_pos hif] at h0 ⊢
    unfold fetchPinned at h0 ⊢
    rw [hl]
    omega
  · rw [if_neg hif] at h0 ⊢
    exact pinnedReadMono s s' _ hl hle h0

theorem tracePinWrite (tid : Option Nat) (s : Wmstate) (ak0 : AkInfo) (pa0 : PAddr) (n0 : Nat)
    (v : BitVec (8 * n0)) (es : List Weff) :
    tracePin s (.WEwrite ak0 pa0 n0 v :: es) → tracePin (wwritePost tid s ak0 pa0 n0 v) es := by
  rintro ⟨hp, hhead, hfr⟩
  refine ⟨fun ak pa n hin hnp j hj => ?_, hfr⟩
  have h0 := hp ak pa n (List.mem_cons_of_mem _ hin) hnp j hj
  unfold readPinned at h0 ⊢
  by_cases hif : ak.akIfetch = true
  · rw [if_pos hif] at h0 ⊢
    unfold fetchPinned at h0 ⊢
    rw [latestTsWriteNe tid s ak0 pa0 n0 v _ (hhead ak pa n hin hif j hj)]
    exact h0
  · rw [if_neg hif] at h0 ⊢
    exact pinnedReadWrite tid s ak0 pa0 n0 v _ h0

theorem tracePinTail (s : Wmstate) (e : Weff) (es : List Weff) :
    tracePin s (e :: es) → tracePin s es := by
  rintro ⟨hp, -, hf⟩
  exact ⟨fun ak pa n hin => hp ak pa n (List.mem_cons_of_mem _ hin), hf⟩

/-! ### 5b. THE CONFINED-RUN INDUCTION, under `tracePin` -- THE theorem -/

theorem wstepEffConfinedPin (tid : Option Nat) {X : Type} (m : SailM X) :
    ∀ (s : Wmstate) (mm : BMap) (W : GSet PAddr) (x : X) (t' : ExecSt) (es : List Weff),
      wlogWf s.wmLog →
      (∀ a, a ∈ W → paZ a ≠ 0) →
      tracePin s es →
      bmDomSub mm W →
      bmSub mm (wflatMem s.wmImg s.wmLog) →
      bmDomSub t'.mem W →
      execEff m ⟨s.wmRegs, mm, s.wmDev⟩ = some (x, t', es) →
      wstepOk tid m s ∧
      (∀ χ (y : X) (s' : Wmstate) χ', wexec tid m χ s = some (y, s', χ') →
        s'.wmImg = s.wmImg ∧ s'.wmLog = (weffs tid s es).wmLog ∧
        s'.wmWs = (weffs tid s es).wmWs) := by
  induction m with
  | pure y =>
    intro s mm W x t' es _ _ _ _ _ _ hex
    simp only [execEff, Option.some.injEq, Prod.mk.injEq] at hex
    obtain ⟨-, -, rfl⟩ := hex
    refine ⟨trivial, fun χ y0 s' χ' hw => ?_⟩
    simp only [wexec, Option.some.injEq, Prod.mk.injEq] at hw
    obtain ⟨-, rfl, -⟩ := hw
    exact ⟨rfl, rfl, rfl⟩
  | impure call k ih =>
    intro s mm W x t' es hwf hW0 hpin hdom hsub hdom' hex
    cases call with
    | error e => simp [execEff] at hex
    | ok o =>
      cases o
      case regWrite r v =>
        simp only [execEff] at hex
        obtain ⟨hok, hag⟩ := ih PUnit.unit (wsetReg s r v) mm W x t' es hwf hW0 hpin hdom hsub hdom' hex
        refine ⟨by simp only [wstepOk]; exact hok, fun χ y s' χ' hw => ?_⟩
        simp only [wexec] at hw
        exact weffsTransport tid s (wsetReg s r v) es s' rfl rfl rfl (hag χ y s' χ' hw)
      case memRead n va req =>
        simp only [execEff] at hex
        by_cases hd : mmioAcc req.pa n = true
        · rw [if_pos hd] at hex
          cases hdr : devRead s.wmDev req.pa n with
          | none => simp only [hdr] at hex; cases hex
          | some p =>
            obtain ⟨w0, d0⟩ := p
            simp only [hdr] at hex
            obtain ⟨hok, hag⟩ := ih _ (wsetDev s d0) mm W x t' es hwf hW0 hpin hdom hsub hdom' hex
            refine ⟨?_, fun χ y s' χ' hw => ?_⟩
            · simp only [wstepOk, if_pos hd]
              intro w d' h
              rw [hdr] at h
              simp only [Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              exact hok
            · simp only [wexec, if_pos hd, hdr] at hw
              exact weffsTransport tid s (wsetDev s d0) es s' rfl rfl rfl (hag χ y s' χ' hw)
        · rw [if_neg hd] at hex
          cases hrb : bmRead mm req.pa n with
          | none => simp only [hrb] at hex; cases hex
          | some w0 =>
            simp only [hrb] at hex
            obtain ⟨es0, hee, rfl⟩ := Weff.consEqSome.1 hex
            -- the footprint is inside the window
            have hin := fun j (hj : j < n) => hdom _ (readBytesDom mm req.pa n w0 hrb j hj)
            have hacc : accWf req.pa n := accWfWindow W req.pa n hW0 hin
            -- THE PIN REFINEMENT, off the trace's head element
            have hpinf : akPins (classify req.access_kind) = false → ∀ j, j < n →
                readPinned s (classify req.access_kind) (WeakInterp.accAddr req.pa j) :=
              fun hnp j hj => hpin.1 _ _ _ List.mem_cons_self hnp j hj
            -- the canonical weak read IS the confined one
            have hwrb : wreadBytes s (classify req.access_kind) req.pa n (cohTs s req.pa n) = some w0 := by
              rw [wreadBytesReadBytes s _ req.pa n hwf hacc]
              exact readBytesMono _ _ _ _ _ hsub hrb
            have hpin2 : tracePin (wreadPost s (classify req.access_kind) req.pa (cohTs s req.pa n)) es0 :=
              tracePinMono _ _ _ (wreadPostLog _ _ _ _) (wreadPostWsLe _ _ _ _)
                (by rw [wreadPostItv]; exact Nat.le_refl _) (tracePinTail _ _ _ hpin)
            have hsub2 : bmSub mm
                (wflatMem (wreadPost s (classify req.access_kind) req.pa (cohTs s req.pa n)).wmImg
                  (wreadPost s (classify req.access_kind) req.pa (cohTs s req.pa n)).wmLog) := by
              rw [wreadPostImg, wreadPostLog]; exact hsub
            have hee2 : execEff (k (.Ok (w0, none)))
                ⟨(wreadPost s (classify req.access_kind) req.pa (cohTs s req.pa n)).wmRegs, mm,
                  (wreadPost s (classify req.access_kind) req.pa (cohTs s req.pa n)).wmDev⟩ =
                some (x, t', es0) := by
              rw [wreadPostRegs, wreadPostDev]; exact hee
            obtain ⟨hok, hag⟩ := ih _ _ mm W x t' es0 (wlogWfReadPost _ _ _ _ hwf) hW0 hpin2 hdom
              hsub2 hdom' hee2
            refine ⟨?_, fun χ y s' χ' hw => ?_⟩
            · simp only [wstepOk, if_neg hd]
              refine ⟨hacc, hpinf, fun w hw => ?_⟩
              rw [hwrb] at hw
              simp only [Option.some.injEq] at hw
              subst hw
              exact hok
            · simp only [wexec, if_neg hd] at hw
              cases hχ : χ.head? with
              | none => simp only [hχ] at hw; cases hw
              | some ts =>
                simp only [hχ] at hw
                cases hrb2 : wreadBytes s (classify req.access_kind) req.pa n ts with
                | none => simp only [hrb2] at hw; cases hw
                | some w =>
                  simp only [hrb2] at hw
                  -- the oracle's timestamps ARE the canonical ones
                  have hts := wreadPinnedTs s _ req.pa n ts w hpinf (wreadBytesSpec _ _ _ _ _ _ hrb2)
                  subst hts
                  rw [hwrb] at hrb2
                  simp only [Option.some.injEq] at hrb2
                  subst hrb2
                  obtain ⟨h1, h2, h3⟩ := hag _ y s' χ' hw
                  exact ⟨h1.trans (wreadPostImg _ _ _ _), h2, h3⟩
      case memWrite n va req =>
        simp only [execEff] at hex
        cases hv : req.value with
        | none => simp only [hv] at hex; cases hex
        | some w =>
          simp only [hv] at hex
          by_cases hd : mmioAcc req.pa n = true
          · rw [if_pos hd] at hex
            cases hdw : devWrite s.wmDev req.pa n w with
            | none => simp only [hdw] at hex; cases hex
            | some d0 =>
              simp only [hdw] at hex
              obtain ⟨hok, hag⟩ := ih _ (wsetDev s d0) mm W x t' es hwf hW0 hpin hdom hsub hdom' hex
              refine ⟨?_, fun χ y s' χ' hw => ?_⟩
              · simp only [wstepOk, if_pos hd, hv]
                intro d' h
                rw [hdw] at h
                simp only [Option.some.injEq] at h
                subst h
                exact hok
              · simp only [wexec, if_pos hd, hv, hdw] at hw
                exact weffsTransport tid s (wsetDev s d0) es s' rfl rfl rfl (hag χ y s' χ' hw)
          · rw [if_neg hd] at hex
            obtain ⟨es0, hee, rfl⟩ := Weff.consEqSome.1 hex
            -- the written footprint is inside the final memory, hence in `W`
            have hdm := execDomMono _ _ _ _ (execEffExec _ _ _ _ _ hee)
            have hin := fun j (hj : j < n) => hdom' _ (hdm _ (writeBytesDom mm req.pa n w j hj))
            have hacc : accWf req.pa n := accWfWindow W req.pa n hW0 hin
            have hpin2 : tracePin (wwritePost tid s (classify req.access_kind) req.pa n w) es0 :=
              tracePinWrite tid s _ _ _ w es0 hpin
            have hdom2 : bmDomSub (bmWrite mm req.pa n w) W := fun a ha => hdom' _ (hdm _ ha)
            have hsub2 : bmSub (bmWrite mm req.pa n w)
                (wflatMem (wwritePost tid s (classify req.access_kind) req.pa n w).wmImg
                  (wwritePost tid s (classify req.access_kind) req.pa n w).wmLog) := by
              show bmSub _ (wflatMem s.wmImg (wwritePost tid s (classify req.access_kind) req.pa n w).wmLog)
              rw [wflatWrite tid s _ req.pa n w hacc]
              exact writeBytesMono _ _ _ _ _ hsub
            obtain ⟨hok, hag⟩ := ih _ _ (bmWrite mm req.pa n w) W x t' es0
              (wflatWriteWf _ _ _ _ _ _ hwf hacc) hW0 hpin2 hdom2 hsub2 hdom' hee
            refine ⟨?_, fun χ y s' χ' hw => ?_⟩
            · simp only [wstepOk, if_neg hd, hv]
              exact ⟨hacc, hok⟩
            · simp only [wexec, if_neg hd, hv] at hw
              exact hag χ y s' χ' hw
      case barrier b =>
        simp only [execEff] at hex
        obtain ⟨es0, hee, rfl⟩ := Weff.consEqSome.1 hex
        have hpin2 : tracePin (wbarrierPost s b) es0 :=
          tracePinMono s (wbarrierPost s b) es0 rfl (barrierPostLe _ _) (itvPostLe _ _ _) (tracePinTail _ _ _ hpin)
        obtain ⟨hok, hag⟩ := ih () (wbarrierPost s b) mm W x t' es0 hwf hW0 hpin2 hdom hsub hdom' hee
        exact ⟨by simp only [wstepOk]; exact hok,
          fun χ y s' χ' hw => by simp only [wexec] at hw; exact hag χ y s' χ' hw⟩
      all_goals first
        | (simp only [execEff, reduceCtorEq] at hex; done)
        | (simp only [execEff] at hex
           obtain ⟨hok, hag⟩ := ih _ s mm W x t' es hwf hW0 hpin hdom hsub hdom' hex
           exact ⟨by simp only [wstepOk]; exact hok,
             fun χ y s' χ' hw => by simp only [wexec] at hw; exact hag χ y s' χ' hw⟩)

/-! ### 5c. The whole-window form, as the EVERY-READ-PINNED instance -/

theorem execEffReadsDom {X : Type} (m : SailM X) :
    ∀ (s : ExecSt) (x : X) (s' : ExecSt) (es : List Weff),
      execEff m s = some (x, s', es) →
      ∀ (ak : AkInfo) (pa : PAddr) (n : Nat), Weff.WEread ak pa n ∈ es →
        ∀ j, j < n → (s'.mem (pa + BitVec.ofNat 64 j)).isSome = true := by
  induction m with
  | pure y =>
    intro s x s' es h ak pa n hin j hj
    simp only [execEff, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, -, rfl⟩ := h
    cases hin
  | impure call k ih =>
    intro s x s' es h ak pa n hin j hj
    cases call with
    | error e => simp [execEff] at h
    | ok o =>
      cases o
      case memRead n0 va req =>
        simp only [execEff] at h
        by_cases hd : mmioAcc req.pa n0 = true
        · rw [if_pos hd] at h
          cases hdr : devRead s.dev req.pa n0 with
          | none => simp only [hdr] at h; cases h
          | some p =>
            obtain ⟨w0, d0⟩ := p
            simp only [hdr] at h
            exact ih _ _ _ _ _ h ak pa n hin j hj
        · rw [if_neg hd] at h
          cases hrb : bmRead s.mem req.pa n0 with
          | none => simp only [hrb] at h; cases h
          | some w0 =>
            simp only [hrb] at h
            obtain ⟨es0, hee, rfl⟩ := Weff.consEqSome.1 h
            rcases List.mem_cons.1 hin with he | hin
            · cases he
              exact execDomMono _ _ _ _ (execEffExec _ _ _ _ _ hee) _
                (readBytesDom _ _ _ _ hrb j hj)
            · exact ih _ _ _ _ _ hee ak pa n hin j hj
      case memWrite n0 va req =>
        simp only [execEff] at h
        cases hv : req.value with
        | none => simp only [hv] at h; cases h
        | some w =>
          simp only [hv] at h
          by_cases hd : mmioAcc req.pa n0 = true
          · rw [if_pos hd] at h
            cases hdw : devWrite s.dev req.pa n0 w with
            | none => simp only [hdw] at h; cases h
            | some d0 =>
              simp only [hdw] at h
              exact ih _ _ _ _ _ h ak pa n hin j hj
          · rw [if_neg hd] at h
            obtain ⟨es0, hee, rfl⟩ := Weff.consEqSome.1 h
            rcases List.mem_cons.1 hin with he | hin
            · cases he
            · exact ih _ _ _ _ _ hee ak pa n hin j hj
      case barrier b =>
        simp only [execEff] at h
        obtain ⟨es0, hee, rfl⟩ := Weff.consEqSome.1 h
        rcases List.mem_cons.1 hin with he | hin
        · cases he
        · exact ih _ _ _ _ _ hee ak pa n hin j hj
      all_goals first
        | (simp only [execEff, reduceCtorEq] at h; done)
        | (simp only [execEff] at h; exact ih _ _ _ _ _ h ak pa n hin j hj)

/-- Whole-window pinnedness (plus the i-cache half, deviation 4) implies `tracePin`. -/
theorem confinedTracePin {X : Type} (m : SailM X) (s : Wmstate) (mm : BMap) (W : GSet PAddr) (x : X)
    (t' : ExecSt) (es : List Weff) :
    (∀ a, a ∈ W → paZ a ≠ 0) →
    (∀ a, a ∈ W → pinnedRead s (paZ a)) →
    fetchPin s es →
    bmDomSub t'.mem W →
    execEff m ⟨s.wmRegs, mm, s.wmDev⟩ = some (x, t', es) →
    tracePin s es := by
  intro hW0 hWp hfp hdom' hex
  refine ⟨fun ak pa n hin _ j hj => ?_, hfp.2⟩
  have hin' : ∀ j0, j0 < n → pa + BitVec.ofNat 64 j0 ∈ W := fun j0 hj0 =>
    hdom' _ (execEffReadsDom m _ _ _ _ hex ak pa n hin j0 hj0)
  have hacc : accWf pa n := accWfWindow W pa n hW0 hin'
  unfold readPinned
  by_cases hif : ak.akIfetch = true
  · rw [if_pos hif]; exact hfp.1 ak pa n hin hif j hj
  · rw [if_neg hif, ← accWfByte pa n j hacc hj]
    exact hWp _ (hin' j hj)

theorem wstepEffConfined (tid : Option Nat) {X : Type} (m : SailM X) :
    ∀ (s : Wmstate) (mm : BMap) (W : GSet PAddr) (x : X) (t' : ExecSt) (es : List Weff),
      wlogWf s.wmLog →
      (∀ a, a ∈ W → paZ a ≠ 0) →
      (∀ a, a ∈ W → pinnedRead s (paZ a)) →
      fetchPin s es →
      bmDomSub mm W →
      bmSub mm (wflatMem s.wmImg s.wmLog) →
      bmDomSub t'.mem W →
      execEff m ⟨s.wmRegs, mm, s.wmDev⟩ = some (x, t', es) →
      wstepOk tid m s ∧
      (∀ χ (y : X) (s' : Wmstate) χ', wexec tid m χ s = some (y, s', χ') →
        s'.wmImg = s.wmImg ∧ s'.wmLog = (weffs tid s es).wmLog ∧
        s'.wmWs = (weffs tid s es).wmWs) := by
  intro s mm W x t' es hwf hW0 hWp hfp hdom hsub hdom' hex
  exact wstepEffConfinedPin tid m s mm W x t' es hwf hW0
    (confinedTracePin m s mm W x t' es hW0 hWp hfp hdom' hex) hdom hsub hdom' hex

/-- The peel alone, at M3b's statement (deviation 4: plus the i-cache half,
stated of the instrumented twin of the run). -/
theorem wstepOkConfined (tid : Option Nat) {X : Type} (m : SailM X) :
    ∀ (s : Wmstate) (mm : BMap) (W : GSet PAddr) (x : X) (t' : ExecSt),
      wlogWf s.wmLog →
      (∀ a, a ∈ W → paZ a ≠ 0) →
      (∀ a, a ∈ W → pinnedRead s (paZ a)) →
      (∀ es, execEff m ⟨s.wmRegs, mm, s.wmDev⟩ = some (x, t', es) → fetchPin s es) →
      bmDomSub mm W →
      bmSub mm (wflatMem s.wmImg s.wmLog) →
      bmDomSub t'.mem W →
      exec m ⟨s.wmRegs, mm, s.wmDev⟩ = some (x, t') →
      wstepOk tid m s := by
  intro s mm W x t' hwf hW0 hWp hfp hdom hsub hdom' hex
  obtain ⟨es, hee⟩ := execExecEff _ _ _ _ hex
  exact (wstepEffConfined tid m s mm W x t' es hwf hW0 hWp (hfp es hee) hdom hsub hdom' hee).1

/-! ## 6. Packaged as the certificate -/

/-- The real memory RESTRICTED to the window (Rocq `wmem_restrict`). -/
def wmemRestrict (s : Wmstate) (W : GSet PAddr) : BMap :=
  fun a => if a ∈ W then wflatMem s.wmImg s.wmLog a else none

theorem wmemRestrictSub (s : Wmstate) (W : GSet PAddr) :
    bmSub (wmemRestrict s W) (wflatMem s.wmImg s.wmLog) := by
  intro a b h
  unfold wmemRestrict at h
  split at h
  · exact h
  · cases h

theorem wmemRestrictDom (s : Wmstate) (W : GSet PAddr) : bmDomSub (wmemRestrict s W) W := by
  intro a h
  unfold wmemRestrict at h
  split at h
  · assumption
  · cases h

theorem wmemRestrictLookup (s : Wmstate) (W : GSet PAddr) (a : PAddr) (b : BitVec 8) :
    a ∈ W → wflatMem s.wmImg s.wmLog a = some b → wmemRestrict s W a = some b := by
  intro hW h
  unfold wmemRestrict
  rw [if_pos hW]
  exact h

/-- THE CONFINED WITNESS (deviation 4: plus the i-cache half). -/
def wstepConf (s : Wmstate) : Prop :=
  ∃ W : GSet PAddr,
    (∀ a, a ∈ W → paZ a ≠ 0) ∧
    (∀ a, a ∈ W → pinnedRead s (paZ a)) ∧
    (∀ tick : Bool, ∃ t' : ExecSt,
      exec (riscvStep tick) ⟨s.wmRegs, wmemRestrict s W, s.wmDev⟩ = some ((), t') ∧
      bmDomSub t'.mem W) ∧
    (∀ (tick : Bool) (t' : ExecSt) (es : List Weff),
      execEff (riscvStep tick) ⟨s.wmRegs, wmemRestrict s W, s.wmDev⟩ = some ((), t', es) →
      fetchPin s es)

def wPConf : Wmstate → Prop := fun s => wlogWf s.wmLog ∧ wstepConf s

theorem wstepOkConf (tid : Option Nat) (s : Wmstate) (tick : Bool) :
    wPConf s → wstepOk tid (riscvStep tick) s := by
  rintro ⟨hwf, W, hW0, hWp, hex, hfp⟩
  obtain ⟨t', ht', hdom'⟩ := hex tick
  exact wstepOkConfined tid (riscvStep tick) s (wmemRestrict s W) W () t' hwf hW0 hWp
    (fun es hes => hfp tick t' es hes) (wmemRestrictDom s W) (wmemRestrictSub s W) hdom' ht'

/-- THE CERTIFICATE, `wstepOk` half discharged for EVERY instruction at once. -/
theorem wstepCertConf (cid : Nat) (pc : BitVec 64) (Q : Wmstate → Wmstate → Prop) :
    (∀ (s : Wmstate) (tick : Bool), s.wmRegs .PC = pc → wPConf s →
      ∀ χ s' χ', wexec (some cid) (riscvStep tick) χ s = some ((), s', χ') → Q s s') →
    wstepCert cid pc wPConf Q := by
  intro hQ s tick hpc _ _ hP
  exact ⟨wstepOkConf _ s tick hP, fun χ s' χ' hex => hQ s tick hpc hP χ s' χ' hex⟩

theorem wstepCertConfNone (cid : Nat) (pc : BitVec 64) : wstepCert cid pc wPConf wQNone :=
  wstepCertConf cid pc wQNone fun _ _ _ _ _ _ _ _ => trivial

/-- Anything that IMPLIES the confined witness certifies the step. -/
theorem wstepCertOfConf (cid : Nat) (pc : BitVec 64) (P : Wmstate → Prop) (Q : Wmstate → Wmstate → Prop) :
    (∀ s, P s → wPConf s) →
    (∀ (s : Wmstate) (tick : Bool), s.wmRegs .PC = pc → P s →
      ∀ χ s' χ', wexec (some cid) (riscvStep tick) χ s = some ((), s', χ') → Q s s') →
    wstepCert cid pc P Q := by
  intro hP hQ s tick hpc _ _ hPs
  exact ⟨wstepOkConf _ s tick (hP s hPs), fun χ s' χ' hex => hQ s tick hpc hPs χ s' χ' hex⟩

/-! ## 7. A CERTIFICATE WHOSE `Q` COMES FROM THE TRACE -/

def wstepConfEffPin (_tid : Option Nat) (es : List Weff) (s : Wmstate) : Prop :=
  ∃ W : GSet PAddr,
    (∀ a, a ∈ W → paZ a ≠ 0) ∧
    tracePin s es ∧
    (∀ tick : Bool, ∃ t' : ExecSt,
      execEff (riscvStep tick) ⟨s.wmRegs, wmemRestrict s W, s.wmDev⟩ = some ((), t', es) ∧
      bmDomSub t'.mem W)

def wPEffPin (tid : Option Nat) (es : List Weff) : Wmstate → Prop :=
  fun s => wlogWf s.wmLog ∧ wstepConfEffPin tid es s

/-- The pin obligation, as an `apply`-able rule. -/
theorem wPEffPinOfWindow (cid : Nat) (es : List Weff) (σ : Wmstate) (W : GSet PAddr) :
    wlogWf σ.wmLog →
    (∀ a, a ∈ W → paZ a ≠ 0) →
    tracePin σ es →
    (∀ tick : Bool, ∃ t' : ExecSt,
      execEff (riscvStep tick) ⟨σ.wmRegs, wmemRestrict σ W, σ.wmDev⟩ = some ((), t', es) ∧
      bmDomSub t'.mem W) →
    wPEffPin (some cid) es σ :=
  fun hwf hW0 hWp hrun => ⟨hwf, W, hW0, hWp, hrun⟩

theorem wstepCertEffPin (cid : Nat) (pc : BitVec 64) (es : List Weff) (Q : Wmstate → Wmstate → Prop) :
    (∀ s s' : Wmstate,
      s'.wmImg = s.wmImg →
      s'.wmLog = (weffs (some cid) s es).wmLog →
      s'.wmWs = (weffs (some cid) s es).wmWs →
      Q s s') →
    wstepCert cid pc (wPEffPin (some cid) es) Q := by
  intro hQ s tick _ _ _ hP
  obtain ⟨hwf, W, hW0, hWp, hex⟩ := hP
  obtain ⟨t', ht', hdom'⟩ := hex tick
  obtain ⟨hok, hag⟩ := wstepEffConfinedPin (some cid) (riscvStep tick) s (wmemRestrict s W) W () t' es
    hwf hW0 hWp (wmemRestrictDom s W) (wmemRestrictSub s W) hdom' ht'
  refine ⟨hok, fun χ s' χ' hw => ?_⟩
  obtain ⟨hi, hl, hws⟩ := hag χ () s' χ' hw
  exact hQ s s' hi hl hws

/-- THE WHOLE-WINDOW FORM (deviation 4: plus the i-cache half). -/
def wstepConfEff (_tid : Option Nat) (es : List Weff) (s : Wmstate) : Prop :=
  ∃ W : GSet PAddr,
    (∀ a, a ∈ W → paZ a ≠ 0) ∧
    (∀ a, a ∈ W → pinnedRead s (paZ a)) ∧
    fetchPin s es ∧
    (∀ tick : Bool, ∃ t' : ExecSt,
      execEff (riscvStep tick) ⟨s.wmRegs, wmemRestrict s W, s.wmDev⟩ = some ((), t', es) ∧
      bmDomSub t'.mem W)

def wPEff (tid : Option Nat) (es : List Weff) : Wmstate → Prop :=
  fun s => wlogWf s.wmLog ∧ wstepConfEff tid es s

theorem wPEffConf (tid : Option Nat) (es : List Weff) (s : Wmstate) : wPEff tid es s → wPConf s := by
  rintro ⟨hwf, W, hW0, hWp, hfp, hex⟩
  refine ⟨hwf, W, hW0, hWp, fun tick => ?_, fun tick t' es' hes => ?_⟩
  · obtain ⟨t', ht', hdom'⟩ := hex tick
    exact ⟨t', execEffExec _ _ _ _ _ ht', hdom'⟩
  · obtain ⟨t0, ht0, -⟩ := hex tick
    rw [← execEffDet _ _ _ _ _ _ _ _ ht0 hes]
    exact hfp

theorem wPEffPinOfEff (tid : Option Nat) (es : List Weff) (s : Wmstate) : wPEff tid es s → wPEffPin tid es s := by
  rintro ⟨hwf, W, hW0, hWp, hfp, hex⟩
  refine ⟨hwf, W, hW0, ?_, hex⟩
  obtain ⟨t', ht', hdom'⟩ := hex false
  exact confinedTracePin _ s _ W () t' es hW0 hWp hfp hdom' ht'

theorem wstepCertEff (cid : Nat) (pc : BitVec 64) (es : List Weff) (Q : Wmstate → Wmstate → Prop) :
    (∀ s s' : Wmstate,
      s'.wmImg = s.wmImg →
      s'.wmLog = (weffs (some cid) s es).wmLog →
      s'.wmWs = (weffs (some cid) s es).wmWs →
      Q s s') →
    wstepCert cid pc (wPEff (some cid) es) Q := by
  intro hQ s tick _ _ _ hP
  obtain ⟨hwf, W, hW0, hWp, hfp, hex⟩ := hP
  obtain ⟨t', ht', hdom'⟩ := hex tick
  obtain ⟨hok, hag⟩ := wstepEffConfined (some cid) (riscvStep tick) s (wmemRestrict s W) W () t' es
    hwf hW0 hWp hfp (wmemRestrictDom s W) (wmemRestrictSub s W) hdom' ht'
  refine ⟨hok, fun χ s' χ' hw => ?_⟩
  obtain ⟨hi, hl, hws⟩ := hag χ () s' χ' hw
  exact hQ s s' hi hl hws

/-! ## 8. THE FOUR INSTRUCTION CERTIFICATES

### 8a. The view arithmetic -/

theorem wmWsWsetWs (s : Wmstate) (ws : Wstate) : (wsetWs s ws).wmWs = ws := rfl

theorem viewLeTrans {V1 V2 V3 : View} (h1 : V1 ≤ V2) (h2 : V2 ≤ V3) : V1 ≤ V3 :=
  fun a => Nat.le_trans (h1 a) (h2 a)

/-- A fence is monotone in the state it fences. -/
theorem fencePostMono (ws1 ws2 : Wstate) (pr pw sr sw : Bool) :
    wsLe ws1 ws2 → wsLe (Weak.fencePost ws1 pr pw sr sw) (Weak.fencePost ws2 pr pw sr sw) := by
  rintro ⟨hc, h1, h2, h3, h4, h5, h6, h7⟩
  refine ⟨fun a => hc a, h1, h2, ?_, ?_, h5, h6, h7⟩ <;>
    cases pr <;> cases pw <;> cases sr <;> cases sw <;> simp [Weak.fencePost] <;> omega

theorem barrierPostMono (ws1 ws2 : Wstate) (b : barrier_kind) :
    wsLe ws1 ws2 → wsLe (barrierPost ws1 b) (barrierPost ws2 b) := by
  intro h
  cases b <;> simp only [barrierPost]
  all_goals first
    | exact h
    | exact fencePostMono _ _ _ _ _ _ (fencePostMono _ _ _ _ _ _ h)
    | exact fencePostMono _ _ _ _ _ _ h

/-- THE PER-BYTE GAIN OF A MULTI-BYTE LOAD. -/
theorem loadPostFoldGain (V : Int → Nat → View) (aq : Bool) (vpre : Nat) :
    (∀ ws a t, V a t ≤ wsView (loadPostAt ws aq vpre a t)) →
    ∀ (ats : List (Int × Nat)) (ws : Wstate) (j : Nat) (at_ : Int × Nat),
      ats[j]? = some at_ →
      V at_.1 at_.2 ≤ wsView (ats.foldl (fun w a => loadPostAt w aq vpre a.1 a.2) ws) := by
  intro hgain ats
  induction ats with
  | nil => intro ws j at_ hj; simp at hj
  | cons a0 l ih =>
    intro ws j at_ hj
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
      subst hj
      simp only [List.foldl_cons]
      exact viewLeTrans (hgain _ _ _) (wsView_mono _ _ (loadPostFoldLe _ _ _ _))
    | succ j =>
      simp only [List.getElem?_cons_succ] at hj
      simp only [List.foldl_cons]
      exact ih _ j at_ hj

theorem loadPostRunGain (V : Int → Nat → View) (ws : Wstate) (aq : Bool) (base : Int) (ts : List Nat)
    (j : Nat) :
    (∀ w a t, V a t ≤ wsView (loadPostAt w aq (loadVpre ws aq) a t)) →
    j < ts.length →
    V (base + (j : Int)) ts[j]! ≤ wsView (loadPostRun ws aq base ts) := by
  intro hgain hj
  show _ ≤ wsView (loadPostBytes ws aq _)
  apply loadPostFoldGain V aq (loadVpre ws aq) hgain _ ws j (base + (j : Int), ts[j]!)
  rw [getBangLt _ _ hj]
  simp [hj]

/-! ### 8b. `fence` -/

theorem wcertFence (cid : Nat) (pc : BitVec 64) (akf : AkInfo) (pf : PAddr) (nf : Nat) (b : barrier_kind) :
    wstepCert cid pc (wPEff (some cid) [.WEread akf pf nf, .WEbar b]) (wQFence b) := by
  apply wstepCertEff
  intro s s' _ _ hws
  unfold wQFence wVFence
  rw [hws, weffsCons2, weffApplyRead, weffApplyBar, wbarrierPostWs]
  exact ⟨barrierPostMono _ _ b (wreadPostWsLe _ _ _ _), fun ha => WeakInstr.barrierPostRelp _ b ha⟩

/-! ### 8c. The 4-byte STORE -/

theorem wcertStore (cid : Nat) (pc : BitVec 64) (akf : AkInfo) (pf : PAddr) (nf : Nat)
    (akw : AkInfo) (ea : PAddr) (v : BitVec 32) :
    wstepCert cid pc (wPEff (some cid) [.WEread akf pf nf, .WEwrite akw ea 4 v]) (wQStore (some cid) ea v) := by
  apply wstepCertEff
  intro s s' hi hl hws
  have hle : wsLe s.wmWs s'.wmWs := by rw [hws]; exact weffsWsLe _ _ _
  rw [weffsCons2, weffApplyRead, weffApplyWrite] at hl hws
  rw [wwritePostLog, wreadPostLog] at hl
  rw [wwritePostWs, wreadPostLog] at hws
  unfold wQStore wQStoreW wVStoreW
  refine ⟨hi, ⟨_, hl, fun hr => WeakInstr.wmClassOfRelp _ _ (by rw [WeakInstr.wreadPostRelp]; exact hr)⟩,
    hle, fun j hj => ?_⟩
  rw [hws, flr_wsView]
  have := storePostRunCoh (wreadPost s akf pf (cohTs s pf nf)).wmWs akw.akSync (paZ ea) 4
    (s.wmLog.length + 1) j hj
  simp only [WeakInterp.accAddr]
  omega

/-! ### 8d. `amoswap.w.aq` -- the store effect PLUS the acquire's index gain -/

theorem wcertAmoAq (cid : Nat) (pc : BitVec 64) (akf : AkInfo) (pf : PAddr) (nf : Nat)
    (aka akw : AkInfo) (ea : PAddr) (v : BitVec 32) :
    aka.akIfetch = false → aka.akSync = true → akw.akLatest = true →
    wstepCert cid pc
      (wPEff (some cid) [.WEread akf pf nf, .WEread aka ea 4, .WEwrite akw ea 4 v])
      (wQAmoAq (some cid) ea v) := by
  intro hcoh hsync hlat
  apply wstepCertEff
  intro s s' hi hl hws
  have hle : wsLe s.wmWs s'.wmWs := by rw [hws]; exact weffsWsLe _ _ _
  rw [weffsCons3, weffApplyRead, weffApplyRead, weffApplyWrite] at hl hws
  -- the fetch left the log alone, so the AMO's read is at `cohTs s`
  rw [cohTsLog (wreadPost s akf pf (cohTs s pf nf)) s ea 4 (wreadPostLog _ _ _ _)] at hl hws
  rw [wwritePostLog, wreadPostLog, wreadPostLog] at hl
  rw [wwritePostWs, wreadPostLog, wreadPostLog] at hws
  rw [wreadPostWsWeak (wreadPost s akf pf (cohTs s pf nf)) aka ea (cohTs s ea 4) hcoh, hsync] at hws
  have hexcl : wmClassOf akw (wreadPost (wreadPost s akf pf (cohTs s pf nf)) aka ea
      (cohTs s ea 4)).wmWs = .WCexcl := by
    simp [wmClassOf, hlat]
  unfold wQAmoAq wQAmoAqW
  refine ⟨?_, ?_, by rw [hl, hexcl]⟩
  · unfold wQStoreW wVStoreW
    refine ⟨hi, ⟨_, hl, fun hr => WeakInstr.wmClassOfRelp _ _
      (by rw [WeakInstr.wreadPostRelp, WeakInstr.wreadPostRelp]; exact hr)⟩, hle, fun j hj => ?_⟩
    rw [hws, flr_wsView]
    have := storePostRunCoh
      (loadPostRun (wreadPost s akf pf (cohTs s pf nf)).wmWs true (paZ ea) (cohTs s ea 4))
      akw.akSync (paZ ea) 4 (s.wmLog.length + 1) j hj
    simp only [WeakInterp.accAddr]
    omega
  · unfold wVAmoAqW
    intro j hj
    rw [hws, ← cohTsLookup s ea 4 j hj]
    exact viewLeTrans
      (loadPostRunGain (fun _ t => viewScl t) (wreadPost s akf pf (cohTs s pf nf)).wmWs true (paZ ea)
        (cohTs s ea 4) j (fun w a t => amo_acq_gain w _ a t) (by rw [cohTsLength]; exact hj))
      (wsView_mono _ _ (storePostRunLe _ _ _ _ _))

/-! ### 8e. The 4-byte plain LOAD -/

theorem wcertLoad (cid : Nat) (pc : BitVec 64) (akf : AkInfo) (pf : PAddr) (nf : Nat) (akl : AkInfo)
    (ea : PAddr) :
    akl.akIfetch = false →
    wstepCert cid pc (wPEff (some cid) [.WEread akf pf nf, .WEread akl ea 4]) (wQLoad ea) := by
  intro hcoh
  apply wstepCertEff
  intro s s' hi hl hws
  rw [weffsCons2, weffApplyRead, weffApplyRead] at hl hws
  rw [cohTsLog (wreadPost s akf pf (cohTs s pf nf)) s ea 4 (wreadPostLog _ _ _ _)] at hl hws
  rw [wreadPostLog, wreadPostLog] at hl
  rw [wreadPostWsWeak (wreadPost s akf pf (cohTs s pf nf)) akl ea (cohTs s ea 4) hcoh] at hws
  unfold wQLoad wQLoadW wVLoadW
  refine ⟨hi, hl, fun j hj => ?_⟩
  rw [hws, ← cohTsLookup s ea 4 j hj]
  exact loadPostRunGain (fun a t => viewByte a t) (wreadPost s akf pf (cohTs s pf nf)).wmWs akl.akSync
    (paZ ea) (cohTs s ea 4) j (fun w a t => load_byte_gain w _ _ a t) (by rw [cohTsLength]; exact hj)

/-! ### 8f. `amoswap.w.aq`, PIN FORM -/

theorem wcertAmoAqPin (cid : Nat) (pc : BitVec 64) (akf : AkInfo) (pf : PAddr) (nf : Nat)
    (aka akw : AkInfo) (ea : PAddr) (v : BitVec 32) :
    aka.akIfetch = false → aka.akSync = true → akw.akLatest = true →
    wstepCert cid pc
      (wPEffPin (some cid) [.WEread akf pf nf, .WEread aka ea 4, .WEwrite akw ea 4 v])
      (wQAmoAq (some cid) ea v) := by
  intro hcoh hsync hlat
  apply wstepCertEffPin
  intro s s' hi hl hws
  have hle : wsLe s.wmWs s'.wmWs := by rw [hws]; exact weffsWsLe _ _ _
  rw [weffsCons3, weffApplyRead, weffApplyRead, weffApplyWrite] at hl hws
  rw [cohTsLog (wreadPost s akf pf (cohTs s pf nf)) s ea 4 (wreadPostLog _ _ _ _)] at hl hws
  rw [wwritePostLog, wreadPostLog, wreadPostLog] at hl
  rw [wwritePostWs, wreadPostLog, wreadPostLog] at hws
  rw [wreadPostWsWeak (wreadPost s akf pf (cohTs s pf nf)) aka ea (cohTs s ea 4) hcoh, hsync] at hws
  have hexcl : wmClassOf akw (wreadPost (wreadPost s akf pf (cohTs s pf nf)) aka ea
      (cohTs s ea 4)).wmWs = .WCexcl := by
    simp [wmClassOf, hlat]
  unfold wQAmoAq wQAmoAqW
  refine ⟨?_, ?_, by rw [hl, hexcl]⟩
  · unfold wQStoreW wVStoreW
    refine ⟨hi, ⟨_, hl, fun hr => WeakInstr.wmClassOfRelp _ _
      (by rw [WeakInstr.wreadPostRelp, WeakInstr.wreadPostRelp]; exact hr)⟩, hle, fun j hj => ?_⟩
    rw [hws, flr_wsView]
    have := storePostRunCoh
      (loadPostRun (wreadPost s akf pf (cohTs s pf nf)).wmWs true (paZ ea) (cohTs s ea 4))
      akw.akSync (paZ ea) 4 (s.wmLog.length + 1) j hj
    simp only [WeakInterp.accAddr]
    omega
  · unfold wVAmoAqW
    intro j hj
    rw [hws, ← cohTsLookup s ea 4 j hj]
    exact viewLeTrans
      (loadPostRunGain (fun _ t => viewScl t) (wreadPost s akf pf (cohTs s pf nf)).wmWs true (paZ ea)
        (cohTs s ea 4) j (fun w a t => amo_acq_gain w _ a t) (by rw [cohTsLength]; exact hj))
      (wsView_mono _ _ (storePostRunLe _ _ _ _ _))

/-! ## 5b′. THE COHERENCE FOOTPRINT of a trace (φ-upgrade, deliverable C) -/

def weffTouches (e : Weff) (a : Int) : Prop :=
  match e with
  | .WEread _ pa n => ∃ j, j < n ∧ a = WeakInterp.accAddr pa j
  | .WEwrite _ pa n _ => ∃ j, j < n ∧ a = WeakInterp.accAddr pa j
  | .WEbar _ => False

def weffsTouch (es : List Weff) (a : Int) : Prop := ∃ e, e ∈ es ∧ weffTouches e a

theorem weffTouchesIv (pa : PAddr) (n : Nat) (a : Int) :
    (paZ pa ≤ a ∧ a < paZ pa + (n : Int)) ↔ ∃ j, j < n ∧ a = WeakInterp.accAddr pa j := by
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨(a - paZ pa).toNat, by omega, by unfold WeakInterp.accAddr; omega⟩
  · rintro ⟨j, hj, he⟩
    unfold WeakInterp.accAddr at he
    omega

instance weffTouchesDec (e : Weff) (a : Int) : Decidable (weffTouches e a) :=
  match e with
  | .WEread _ pa n => decidable_of_iff _ (weffTouchesIv pa n a)
  | .WEwrite _ pa n _ => decidable_of_iff _ (weffTouchesIv pa n a)
  | .WEbar _ => isFalse fun h => h

instance weffsTouchDec (es : List Weff) (a : Int) : Decidable (weffsTouch es a) :=
  inferInstanceAs (Decidable (∃ e, e ∈ es ∧ weffTouches e a))

theorem weffsTouchCons (e : Weff) (es : List Weff) (a : Int) :
    weffsTouch (e :: es) a → weffTouches e a ∨ weffsTouch es a := by
  rintro ⟨e', he', ht⟩
  rcases List.mem_cons.1 he' with rfl | he'
  · exact .inl ht
  · exact .inr ⟨e', he', ht⟩

theorem weffsTouchApp (es1 es2 : List Weff) (a : Int) :
    weffsTouch (es1 ++ es2) a → weffsTouch es1 a ∨ weffsTouch es2 a := by
  rintro ⟨e, he, ht⟩
  rcases List.mem_append.1 he with he | he
  · exact .inl ⟨e, he, ht⟩
  · exact .inr ⟨e, he, ht⟩

theorem weffsTouchNil (a : Int) : weffsTouch [] a → False := by
  rintro ⟨e, he, _⟩; cases he

theorem weffsTouchRead1 (ak : AkInfo) (pa : PAddr) (n : Nat) (a : Int) :
    weffsTouch [.WEread ak pa n] a → ∃ j, j < n ∧ a = WeakInterp.accAddr pa j := by
  rintro ⟨e, he, ht⟩
  rw [List.mem_singleton] at he
  subst he
  exact ht

theorem weffsTouchWrite1 (ak : AkInfo) (pa : PAddr) (n : Nat) (v : BitVec (8 * n)) (a : Int) :
    weffsTouch [.WEwrite ak pa n v] a → ∃ j, j < n ∧ a = WeakInterp.accAddr pa j := by
  rintro ⟨e, he, ht⟩
  rw [List.mem_singleton] at he
  subst he
  exact ht

theorem weffsTouchRead14 (ak : AkInfo) (pc : PAddr) (n : Nat) (a : Int) :
    n ≤ 4 → weffsTouch [.WEread ak pc n] a → ∃ j, j < 4 ∧ a = WeakInterp.accAddr pc j := by
  intro hn ha
  obtain ⟨j, hj, rfl⟩ := weffsTouchRead1 ak pc n a ha
  exact ⟨j, by omega, rfl⟩

/-- The COMPRESSED fetch trace (deviation 8). -/
theorem weffsTouchFetch2 (ak : AkInfo) (pc : PAddr) (a : Int) :
    accWf pc 4 →
    weffsTouch [.WEread ak pc 2, .WEread ak (pc + BitVec.ofNat 64 2) 2] a →
    ∃ j, j < 4 ∧ a = WeakInterp.accAddr pc j := by
  intro hacc ha
  have hhi : paZ (pc + BitVec.ofNat 64 2) = paZ pc + 2 := by
    rw [accWfByte pc 4 2 hacc (by omega)]
    unfold WeakInterp.accAddr
    omega
  rcases weffsTouchCons _ _ a ha with ha | ha
  · obtain ⟨j, hj, rfl⟩ := ha
    exact ⟨j, by omega, rfl⟩
  · obtain ⟨j, hj, rfl⟩ := weffsTouchRead1 _ _ _ a ha
    refine ⟨2 + j, by omega, ?_⟩
    unfold WeakInterp.accAddr
    rw [hhi]
    omega

/-- The two per-byte frames. -/
theorem WeakCert.cohLoadPostAtNe (ws : Wstate) (aq : Bool) (vpre : Nat) (a' : Int) (t : Nat) (a : Int) :
    a ≠ a' → coh (loadPostAt ws aq vpre a' t) a = coh ws a :=
  fun h => _root_.Weak.cohLoadPostAtNe ws aq vpre a' t a h

theorem WeakCert.cohStorePostNe (ws : Wstate) (rl : Bool) (a' : Int) (t : Nat) (a : Int) :
    a ≠ a' → coh (storePost ws rl a' t) a = coh ws a :=
  fun h => _root_.Weak.cohStorePostNe ws rl a' t a h

theorem cohFoldlLoadNe (aq : Bool) (vpre : Nat) (ats : List (Int × Nat)) (a : Int) :
    (∀ p, p ∈ ats → a ≠ p.1) →
    ∀ w, coh (ats.foldl (fun w at_ => loadPostAt w aq vpre at_.1 at_.2) w) a = coh w a := by
  induction ats with
  | nil => intro _ w; rfl
  | cons at_ ats ih =>
    intro hno w
    simp only [List.foldl_cons]
    rw [ih (fun p hp => hno p (List.mem_cons_of_mem _ hp))]
    exact WeakCert.cohLoadPostAtNe _ _ _ _ _ _ (hno _ List.mem_cons_self)

theorem cohLoadPostBytesNe (ws : Wstate) (aq : Bool) (ats : List (Int × Nat)) (a : Int) :
    (∀ p, p ∈ ats → a ≠ p.1) → coh (loadPostBytes ws aq ats) a = coh ws a :=
  fun hno => cohFoldlLoadNe _ _ _ _ hno _

theorem cohFoldlStoreNe (rl : Bool) (as_ : List Int) (t : Nat) (a : Int) :
    (∀ z, z ∈ as_ → a ≠ z) → ∀ w, coh (as_.foldl (fun w z => storePost w rl z t) w) a = coh w a := by
  induction as_ with
  | nil => intro _ w; rfl
  | cons z as_ ih =>
    intro hno w
    simp only [List.foldl_cons]
    rw [ih (fun z' hz' => hno z' (List.mem_cons_of_mem _ hz'))]
    exact WeakCert.cohStorePostNe _ _ _ _ _ (hno _ List.mem_cons_self)

theorem cohStorePostBytesNe (ws : Wstate) (rl : Bool) (as_ : List Int) (t : Nat) (a : Int) :
    (∀ z, z ∈ as_ → a ≠ z) → coh (storePostBytes ws rl as_ t) a = coh ws a :=
  fun hno => cohFoldlStoreNe _ _ _ _ hno _

theorem cohLoadPostRunNe (ws : Wstate) (aq : Bool) (pa : PAddr) (ts : List Nat) (a : Int) :
    (∀ j, j < ts.length → a ≠ WeakInterp.accAddr pa j) →
    coh (loadPostRun ws aq (paZ pa) ts) a = coh ws a := by
  intro hno
  unfold loadPostRun
  rw [ctrlPostCoh]
  apply cohLoadPostBytesNe
  intro p hp
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hp
  have hil : i < ts.length := by simp at hi; omega
  have := hno i hil
  simp only [List.getElem_zipWith, List.getElem_range']
  unfold WeakInterp.accAddr at this
  simpa using this

theorem cohStorePostRunNe (ws : Wstate) (rl : Bool) (pa : PAddr) (n t : Nat) (a : Int) :
    (∀ j, j < n → a ≠ WeakInterp.accAddr pa j) →
    coh (storePostRun ws rl (paZ pa) n t) a = coh ws a := by
  intro hno
  unfold storePostRun
  rw [ctrlPostCoh]
  apply cohStorePostBytesNe
  intro z hz
  obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hz
  rw [List.mem_range'_1] at hj
  exact hno j (by omega)

/-- THE FRAME, per effect and then along a whole trace. -/
theorem weffApplyCohFrame (tid : Option Nat) (s : Wmstate) (e : Weff) (a : Int) :
    ¬ weffTouches e a → coh (weffApply tid s e).wmWs a = coh s.wmWs a := by
  intro hno
  cases e with
  | WEread ak pa n =>
    rw [weffApplyRead]
    unfold wreadPost
    by_cases hif : ak.akIfetch = true
    · rw [if_pos hif]
    · rw [if_neg hif]
      apply cohLoadPostRunNe
      intro j hj heq
      exact hno ⟨j, by rw [cohTsLength] at hj; exact hj, heq⟩
  | WEwrite ak pa n v =>
    rw [weffApplyWrite, wwritePostWs]
    exact cohStorePostRunNe _ _ _ _ _ _ fun j hj heq => hno ⟨j, hj, heq⟩
  | WEbar b =>
    rw [weffApplyBar, wbarrierPostWs]
    cases b <;> rfl

theorem weffsCohFrame (tid : Option Nat) (s : Wmstate) (es : List Weff) (a : Int) :
    ¬ weffsTouch es a → coh (weffs tid s es).wmWs a = coh s.wmWs a := by
  induction es generalizing s with
  | nil => intro _; rfl
  | cons e es ih =>
    intro hno
    rw [weffsCons, ih]
    · exact weffApplyCohFrame _ _ _ _ fun ht => hno ⟨e, List.mem_cons_self, ht⟩
    · exact fun ⟨e', he', ht⟩ => hno ⟨e', List.mem_cons_of_mem _ he', ht⟩

/-- THE LOG SIDE: every message a trace appends carries the runner's own tid. -/
theorem weffsLogOwn (tid : Option Nat) (s : Wmstate) (es : List Weff) :
    ∃ ms, (weffs tid s es).wmLog = s.wmLog ++ ms ∧ ∀ m, m ∈ ms → m.wmTid = tid := by
  induction es generalizing s with
  | nil => exact ⟨[], by rw [weffsNil, List.append_nil], fun m hm => by cases hm⟩
  | cons e es ih =>
    obtain ⟨ms2, hms2, hown2⟩ := ih (weffApply tid s e)
    have hstep : ∃ ms1, (weffApply tid s e).wmLog = s.wmLog ++ ms1 ∧ ∀ m, m ∈ ms1 → m.wmTid = tid := by
      cases e with
      | WEread ak pa n =>
        exact ⟨[], by rw [weffApplyRead, wreadPostLog, List.append_nil], fun m hm => by cases hm⟩
      | WEwrite ak pa n v =>
        refine ⟨[wwriteMsg tid (wmClassOf ak s.wmWs) pa n v], rfl, fun m hm => ?_⟩
        rw [List.mem_singleton] at hm
        subst hm
        rfl
      | WEbar b => exact ⟨[], by rw [List.append_nil]; rfl, fun m hm => by cases hm⟩
    obtain ⟨ms1, hms1, hown1⟩ := hstep
    refine ⟨ms1 ++ ms2, by rw [weffsCons, hms2, hms1, List.append_assoc], fun m hm => ?_⟩
    rcases List.mem_append.1 hm with hm | hm
    · exact hown1 m hm
    · exact hown2 m hm

/-- THE LEAF-FACING COMBINATOR: violation-freedom reduces to one `nvByte` per
byte of the step's own effect trace. -/
theorem nvHartWeffs (c : CPU) (s : Wmstate) (es : List Weff) :
    nvHart s.wmLog c s.wmWs →
    (∀ a : Int, weffsTouch es a →
      nvByte (weffs (some c.val) s es).wmLog c a (coh (weffs (some c.val) s es).wmWs a)) →
    nvHart (weffs (some c.val) s es).wmLog c (weffs (some c.val) s es).wmWs := by
  intro hnv htouch
  obtain ⟨ms, hms, hown⟩ := weffsLogOwn (some c.val) s es
  rw [hms]
  apply nvHartCohStep _ c s.wmWs
  · exact nvHartAppOwn _ _ c _ hnv hown
  · intro a hlt
    rw [← hms]
    apply htouch
    by_cases ht : weffsTouch es a
    · exact ht
    · exfalso
      rw [weffsCohFrame (some c.val) s es a ht] at hlt
      omega

/-! ## 5c′. CARRYING THE TRACE THROUGH THE CERTIFICATE (φ-upgrade, (i)) -/

def wQEff (tid : Option Nat) (es : List Weff) : Wmstate → Wmstate → Prop :=
  fun s s' => s'.wmImg = s.wmImg ∧ s'.wmLog = (weffs tid s es).wmLog ∧ s'.wmWs = (weffs tid s es).wmWs

def wQFr (Q : Wmstate → Wmstate → Prop) (tid : Option Nat) (es : List Weff) :
    Wmstate → Wmstate → Prop :=
  fun s s' => Q s s' ∧ wQEff tid es s s'

theorem wcertEff (cid : Nat) (pc : BitVec 64) (es : List Weff) :
    wstepCert cid pc (wPEff (some cid) es) (wQEff (some cid) es) :=
  wstepCertEff cid pc es _ fun _ _ hi hl hws => ⟨hi, hl, hws⟩

/-- Two certificates over the SAME precondition conjoin. -/
theorem wstepCertPair (cid : Nat) (pc : BitVec 64) (P : Wmstate → Prop) (Q1 Q2 : Wmstate → Wmstate → Prop) :
    wstepCert cid pc P Q1 → wstepCert cid pc P Q2 →
    wstepCert cid pc P (fun s s' => Q1 s s' ∧ Q2 s s') := by
  intro h1 h2 s tick hpc hacc htext hP
  obtain ⟨hok, hq1⟩ := h1 s tick hpc hacc htext hP
  obtain ⟨_, hq2⟩ := h2 s tick hpc hacc htext hP
  exact ⟨hok, fun χ s' χ' hex => ⟨hq1 χ s' χ' hex, hq2 χ s' χ' hex⟩⟩

theorem wstepCertFr (cid : Nat) (pc : BitVec 64) (es : List Weff) (Q : Wmstate → Wmstate → Prop) :
    wstepCert cid pc (wPEff (some cid) es) Q →
    wstepCert cid pc (wPEff (some cid) es) (wQFr Q (some cid) es) :=
  fun hQ => wstepCertPair cid pc _ Q _ hQ (wcertEff cid pc es)

theorem wcertEffPin (cid : Nat) (pc : BitVec 64) (es : List Weff) :
    wstepCert cid pc (wPEffPin (some cid) es) (wQEff (some cid) es) :=
  wstepCertEffPin cid pc es _ fun _ _ hi hl hws => ⟨hi, hl, hws⟩

theorem wstepCertFrPin (cid : Nat) (pc : BitVec 64) (es : List Weff) (Q : Wmstate → Wmstate → Prop) :
    wstepCert cid pc (wPEffPin (some cid) es) Q →
    wstepCert cid pc (wPEffPin (some cid) es) (wQFr Q (some cid) es) :=
  fun hQ => wstepCertPair cid pc _ Q _ hQ (wcertEffPin cid pc es)

/-- THE LEAF-FACING ONE-LINER. -/
theorem nvHartOfWQEff (c : CPU) (σ σ' : Wmstate) (es : List Weff) :
    wQEff (some c.val) es σ σ' →
    nvHart σ.wmLog c σ.wmWs →
    (∀ a : Int, weffsTouch es a → nvByte σ'.wmLog c a (coh σ'.wmWs a)) →
    nvHart σ'.wmLog c σ'.wmWs := by
  rintro ⟨-, hl, hws⟩ hnv ht
  rw [hl, hws] at ht ⊢
  exact nvHartWeffs c σ es hnv ht

/-- The `nvOk` form (the DATA leaves). -/
theorem nvHartOfWQEffOk (c : CPU) (σ σ' : Wmstate) (es : List Weff) :
    wQEff (some c.val) es σ σ' →
    nvHart σ.wmLog c σ.wmWs →
    (∀ a : Int, weffsTouch es a → nvOk σ'.wmLog c a) →
    nvHart σ'.wmLog c σ'.wmWs :=
  fun hQ hnv ht => nvHartOfWQEff c σ σ' es hQ hnv fun a ha => nvByteOfOk _ _ _ _ (ht a ha)

/-- ... and its FETCH-ONLY instance (the register-only leaves). -/
theorem nvHartOfWQEffUnwritten (c : CPU) (σ σ' : Wmstate) (es : List Weff) :
    wQEff (some c.val) es σ σ' →
    nvHart σ.wmLog c σ.wmWs →
    (∀ a : Int, weffsTouch es a → latestTs σ'.wmLog a = 0) →
    nvHart σ'.wmLog c σ'.wmWs :=
  fun hQ hnv ht => nvHartOfWQEff c σ σ' es hQ hnv fun a ha => nvByteUnwritten _ _ _ _ (ht a ha)

end Weak
