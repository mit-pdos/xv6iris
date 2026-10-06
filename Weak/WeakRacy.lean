/-
Weak: **the RACY-LOAD rule** (M4-prep).

Rocq: `iris/WeakRacy.v` @ xxvzwolszwmp.

The Rocq header, in substance (Rocq vocabulary).

THE GAP THIS CLOSES.  `WeakInstr.wpWinstr` rests on the PINNED-fragment bridge of `WeakBridge`:
its read arm demands that the hart's own index already cover the latest write to every byte the
step reads, and then the whole step is described by an `exec` fact about the COHERENT flat
projection `wflatSt σ`.  A hart spinning on `started` is exactly the case where that fails: it
legally reads a STALE message while `wflatSt σ` already holds the setter's 1, so NO `exec` fact
about the flat projection describes the step.

THE SHAPE OF THE ANSWER.  One RACY WINDOW `[ra, ra+rn)` is singled out, and everything is stated
at the flat memory PATCHED at that window with the value the run actually read (`wpatchSt σ ra rn
w`).  Away from the window the machine is on the pinned fragment and the M3a argument goes through
verbatim; at the window nothing is pinned and the rule quantifies over the ADMISSIBLE read results
instead.  The ∀-oracle surface that survives to the user is ONE binder -- the racy WORD `w` --
together with the per-byte admissibility `wadm`, which is what `WeakStarted` consumes.

§1 the window (disjointness, and the `bmWrite` algebra the patch needs); §2 `wstepOkRacy` --
`WeakBridge.wstepOk` arm for arm, EXCEPT at a RAM read whose footprint IS the window (a boolean
phase says whether the racy read is still ahead); §3 the transport lemmas of the pre-racy phase
(its states differ from the initial one only in views, so admissibility transports DOWN); §4 THE
BRIDGE `execOfWrunRacy` (consumption direction, over `wrun`) and its window-free companion
`execOfWrunWin`; §4b the view GAIN of the racy read (`execOfWrunGain`); §5 the reducibility
direction `wexecOfExecRacy` and the `wexecCovers` mirror `wrunWexecRacy`, both at the CANONICAL
value; §6 THE RULE `wpWracyLoad` (and `wpWracyLoadGain`), over `WeakExec.wpWrunStep`; §7 the
`lw`-shaped racy leaf: the ∀-over-admissible-values collapses into a DISJUNCTION for a one-shot
flag.

DELIBERATELY RESTRICTED: a RAM write is allowed only AFTER the racy read (unless the parameter
`W` permits it; the bridge is stated at `W := False`), so in the pre-racy phase the states differ
from the initial one only in VIEWS.

**Deviations from Rocq.**

1. NAMES: the tree's camelCase (map below).  No Rocq name of this file is duplicated elsewhere.
2. THE FLAT MEMORY (WeakBridge deviation 2): `mstate` is `ExecSt`, `read_bytes`/`write_bytes`
   are MachCSL's `bmRead`/`bmWrite` over the function map `BMap`, `pa_add pa j` is
   `pa + BitVec.ofNat 64 j`.  `wpatchSt s ra rn w := ⟨s.wmRegs, bmWrite (wflatMem s.wmImg
   s.wmLog) ra rn w, s.wmDev⟩`.  `writeBytesLookupNe/At`, `writeBytesId`, `writeBytesPatchComm`
   are stated at value width `8 * n` (Rocq: any `{wd} (v : bv wd)`), because `bmWrite` is (as
   WeakInterp deviation 7).  `wpatchStDevSet`/`wpatchStWritePost` state their right-hand sides
   with `ExecSt.setDev`/`setMem` (Rocq `MState …` literals).  `wpatchStWritePost` uses
   `WeakBridge.wflatWrite`, which takes `accWf pa n` (already a premise here).
3. `is_Some o` is `o.isSome = true` (the tree's AxGraph convention).
4. O2 (`notes/weak-port-o2-design.md`; WeakInterp/WeakBridge/WeakExec headers):
   - `wstepOkRacy`'s off-window read arm is `wstepOk`'s: the obligation is `akPins … = false →
     readPinned …` (Rocq `ak_pins … = false → pinned_read …`), and the mmio test is `mmioAcc`;
     the write arms match on `req.value` and answer `.Ok (some true)` (WeakBridge deviations
     3-5).  The barrier arm moves to `wbarrierPost` (data views AND the i-cache view `wmItv`).
   - THE I-CACHE VIEW IN THE TRANSPORT.  Rocq `ak_coh`'s admissibility (`¬ writes_in log a t
     |log|`) did not depend on the hart's state; the Lean i-cache arm (`¬ writesIn log a t (max t
     itv)`) depends on `wmItv`, which the pre-racy phase may RAISE (`fence.i`).  A larger `itv` is
     a larger window, so admissibility still transports DOWN, under the extra premise `s.wmItv ≤
     s2.wmItv`: `wbyteOkDown`, `wadmDown`, `wadmFilterDown`, `execOfWrunRacyGen`,
     `execOfWrunGainGen` carry it (`s0.wmItv ≤ s.wmItv`, `wrunItvLe`'s direction).  The
     Lean-only `wadmFilterBarrierPost` is the barrier step of the traversals (Rocq used
     `wadm_filter_set_ws`, the barrier moving only the data views there).
   - THE `ak_coh` ARMS COLLAPSE.  Lean's `wexec` consumes the oracle at EVERY RAM read
     (WeakInterp deviation 8), so `wexecOfExecRacy`/`wrunWexecRacy` cons the chosen timestamps in
     both read arms and the Rocq case splits on `ak_coh` (and the use of `wread_coh_ts`, false
     under O2 -- WeakExec deviation 3) are gone.  The statements are unchanged.
   - `ak_coh rak = false` (the gain premise) is `rak.akIfetch = false`.
   - THE TEXT PIN: `wracyCert`'s and the rules' text hypothesis is `∀ j < 4, pinnedRead σ (accAddr
     pc j) ∧ fetchPinned σ (accAddr pc j)` (WeakInstr deviation 4; Rocq `pinned_read` only).
5. THE RULES (WeakExec deviations 1 and 7): the generation `gen` and hart `cpu` are explicit,
   `gen_id = 0` is `gen = 0`, `Loop` is `WExpr.loop gen cpu`, the certificate's hart id is
   `cpu.val`, and Rocq's `sync_win ra rn -∗ H -∗ WWP Loop` is `syncWin ra rn ∗ H ⊢ wwpTriv ⊤ …`
   (the sync premise, as in Rocq, is not consumed).  `register_lookup PC (wm_regs σ)` is
   `σ.wmRegs .PC`; the reducibility witness's `mstate` is `ExecSt`.
6. Rocq's `filt_step` Ltac is not a Lean tactic: each arm of the two `wexec`-direction
   traversals applies the matching `wadmFilter*` lemma explicitly.
7. Lean-only helpers: `paAddToNat`, `bmFoldLookupNe`, `bmReadExt`, `wpatchStRegs/Mem/Dev`,
   `wpatchStBarrier`, `wadmFilterBarrierPost`.

**Rocq → Lean name map.**  `racc_disj` `raccDisj`, `acc_addr_range` `accAddrRange`, `pa_add_neq`
`paAddNeq`, `pa_add_inj` `paAddInj`, `write_bytes_lookup_ne` `writeBytesLookupNe`,
`write_bytes_lookup_at` `writeBytesLookupAt`, `write_bytes_id` `writeBytesId`,
`read_bytes_of_bytes` `readBytesOfBytes`, `read_bytes_patch_disj` `readBytesPatchDisj`,
`write_bytes_patch_comm` `writeBytesPatchComm`, `wpatch_st` `wpatchSt`, `wpatch_st_reg_set`
`wpatchStRegSet`, `wpatch_st_ws` `wpatchStWs`, `wpatch_st_read_post` `wpatchStReadPost`,
`wpatch_st_dev_set` `wpatchStDevSet`, `wpatch_st_write_post` `wpatchStWritePost`,
`wstep_ok_racy` `wstepOkRacy`, `wadm` `wadm`, `wadm_of_wread_ok` `wadmOfWreadOk`, `wadm_filter`
`wadmFilter`, `wadm_any` `wadmAny`, `wadm_filter_any` `wadmFilterAny`, `load_vpre_mono`
`loadVpreMono`, `readable_ws_down` `readableWsDown`, `wbyte_ok_down` `wbyteOkDown`, `wadm_down`
`wadmDown`, `wadm_filter_down` `wadmFilterDown`, `wadm_filter_set_reg/dev/ws/read_post`
`wadmFilterSetReg/Dev/Ws/ReadPost`, `exec_of_wrun_win` `execOfWrunWin`, `exec_of_wrun_racy_gen`
`execOfWrunRacyGen`, `exec_of_wrun_racy` `execOfWrunRacy`, `wunwritten` `wunwritten`, `wgain`
`wgain`, `wgain_wadm` `wgainWadm`, `wgain_mono` `wgainMono`, `wread_post_fwd` `wreadPostFwd`,
`barrier_post_fwd` `barrierPostFwd`, `wread_post_vrOld` `wreadPostVrOld`,
`exec_of_wrun_gain_gen` `execOfWrunGainGen`, `exec_of_wrun_gain` `execOfWrunGain`,
`wexec_of_exec_racy` `wexecOfExecRacy`, `wrun_wexec_racy` `wrunWexecRacy`, `wstep_post_racy`
`wstepPostRacy`, `wracy_cert` `wracyCert`, `wp_wracy_load` `wpWracyLoad`, `wp_wracy_load_gain`
`wpWracyLoadGain`, `wreads_win` `wreadsWin`, `wtwo_valued` `wtwoValued`, `wadm_two_valued`
`wadmTwoValued`, `nth_byte_lock_zero` `nthByteLockZero`, `nth_byte_lock_one_high`
`nthByteLockOneHigh`, `wadm_started_lw4` `wadmStartedLw4`.  (`filt_step`: deviation 6.)

**Dropped:** nothing.

**Statements checked** (by hand, against Rocq): all; the changed ones are deviations 2-5.
-/
import Weak.WeakStarted

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std
open MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open Sail.ArchSem (FreeM)
open LeanRV64D LeanRV64D.Functions

/-! ## 1. The racy window and the patched memory -/

/-- Two accesses do not overlap (stated on the `Int` side, where `accWf` makes an access an
honest interval). -/
def raccDisj (ra : PAddr) (rn : Nat) (pa : PAddr) (n : Nat) : Prop :=
  paZ pa + (n : Int) ≤ paZ ra ∨ paZ ra + (rn : Int) ≤ paZ pa

theorem accAddrRange (pa : PAddr) (n j : Nat) :
    accWf pa n → j < n →
    0 ≤ WeakInterp.accAddr pa j ∧ WeakInterp.accAddr pa j < 18446744073709551616 := by
  intro hwf hj
  have := WeakInterp.paZRange pa
  unfold accWf at hwf
  unfold WeakInterp.accAddr
  omega

/-- A wrap-free byte address, numerically (Lean helper). -/
theorem paAddToNat (pa : PAddr) (n j : Nat) :
    accWf pa n → j < n → (pa + BitVec.ofNat 64 j).toNat = pa.toNat + j := by
  intro hwf hj
  unfold accWf paZ at hwf
  have := pa.isLt
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow]
  omega

/-- Distinct bytes of two disjoint accesses are distinct addresses ... -/
theorem paAddNeq (pa ra : PAddr) (n rn j i : Nat) :
    accWf pa n → accWf ra rn → raccDisj ra rn pa n → j < n → i < rn →
    pa + BitVec.ofNat 64 j ≠ ra + BitVec.ofNat 64 i := by
  intro hp hr hd hj hi heq
  have h := congrArg BitVec.toNat heq
  rw [paAddToNat pa n j hp hj, paAddToNat ra rn i hr hi] at h
  unfold raccDisj paZ at hd
  omega

/-- ... and distinct bytes of ONE wrap-free access are distinct addresses. -/
theorem paAddInj (pa : PAddr) (n j j' : Nat) :
    accWf pa n → j < n → j' < n →
    pa + BitVec.ofNat 64 j = pa + BitVec.ofNat 64 j' → j = j' := by
  intro hwf hj hj' heq
  have h := congrArg BitVec.toNat heq
  rw [paAddToNat pa n j hwf hj, paAddToNat pa n j' hwf hj'] at h
  omega

/-! ### The `bmWrite` algebra -/

/-- The fold under `bmWrite`, away from its footprint (Lean helper). -/
theorem bmFoldLookupNe (pa : PAddr) (g : Nat → BitVec 8) (a : PAddr) :
    ∀ (l : List Nat) (mm : BMap), (∀ j ∈ l, a ≠ pa + BitVec.ofNat 64 j) →
      (l.foldl (fun m j => bmSet m (pa + BitVec.ofNat 64 j) (g j)) mm) a = mm a
  | [], _, _ => rfl
  | j :: l, mm, h => by
    rw [List.foldl_cons, bmFoldLookupNe pa g a l _ (fun i hi => h i (List.mem_cons_of_mem _ hi))]
    unfold bmSet
    rw [if_neg (h j List.mem_cons_self)]

theorem writeBytesLookupNe (mm : BMap) (pa : PAddr) (n : Nat) (v : BitVec (8 * n)) (a : PAddr) :
    (∀ j : Nat, j < n → a ≠ pa + BitVec.ofNat 64 j) → bmWrite mm pa n v a = mm a := by
  intro h
  unfold bmWrite
  exact bmFoldLookupNe pa (nthByte v) a _ mm (fun j hj => h j (List.mem_range.1 hj))

theorem writeBytesLookupAt (mm : BMap) (pa : PAddr) (n : Nat) (v : BitVec (8 * n)) (j : Nat) :
    accWf pa n → j < n → bmWrite mm pa n v (pa + BitVec.ofNat 64 j) = some (nthByte v j) := by
  intro hwf hj
  have hn : n ≤ 18446744073709551616 := by
    have := WeakInterp.paZRange pa; unfold accWf at hwf; omega
  rw [bmWriteLookup _ _ _ _ _ hn]
  have hd : (pa + BitVec.ofNat 64 j - pa).toNat = j := by
    have := pa.isLt
    simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow]
    omega
  rw [hd, if_pos hj]

/-- Patching a window with the value it already holds is the identity. -/
theorem writeBytesId (mm : BMap) (pa : PAddr) (n : Nat) (v : BitVec (8 * n)) :
    (∀ j : Nat, j < n → mm (pa + BitVec.ofNat 64 j) = some (nthByte v j)) →
    bmWrite mm pa n v = mm := by
  intro hv
  unfold bmWrite
  suffices h : ∀ l : List Nat, (∀ j ∈ l, j < n) →
      l.foldl (fun m j => bmSet m (pa + BitVec.ofNat 64 j) (nthByte v j)) mm = mm from
    h _ (fun j hj => List.mem_range.1 hj)
  intro l
  induction l with
  | nil => intro _; rfl
  | cons j l ih =>
    intro hl
    rw [List.foldl_cons, bmSet_self mm _ _ (hv j (hl j List.mem_cons_self))]
    exact ih (fun i hi => hl i (List.mem_cons_of_mem _ hi))

/-- The converse of `bmRead_spec` -- the shape the caller of the rule uses to see the window in
the flat memory. -/
theorem readBytesOfBytes (mm : BMap) (pa : PAddr) (n : Nat) (v : BitVec (8 * n)) :
    (∀ j : Nat, j < n → mm (pa + BitVec.ofNat 64 j) = some (nthByte v j)) →
    bmRead mm pa n = some v := by
  intro hv
  rw [bmReadAssemble mm pa n (nthByte v) hv]
  congr 1
  apply bvEqOfBytes
  intro j hj
  exact nthByteAssembleBytes n _ j hj

/-- `bmRead` only looks at its footprint (Lean helper). -/
theorem bmReadExt (mm1 mm2 : BMap) (pa : PAddr) :
    ∀ n : Nat, (∀ j, j < n → mm1 (pa + BitVec.ofNat 64 j) = mm2 (pa + BitVec.ofNat 64 j)) →
      bmRead mm1 pa n = bmRead mm2 pa n
  | 0, _ => rfl
  | n + 1, h => by
    simp only [bmRead]
    rw [bmReadExt mm1 mm2 pa n (fun j hj => h j (by omega)), h n (by omega)]

/-- A read DISJOINT from the window does not see the patch ... -/
theorem readBytesPatchDisj (mm : BMap) (ra : PAddr) (rn : Nat) (w : BitVec (8 * rn)) (pa : PAddr)
    (n : Nat) :
    accWf ra rn → accWf pa n → raccDisj ra rn pa n →
    bmRead (bmWrite mm ra rn w) pa n = bmRead mm pa n := by
  intro hr hp hd
  exact bmReadExt _ _ pa n (fun j hj => writeBytesLookupNe mm ra rn w _
    (fun i hi => paAddNeq pa ra n rn j i hp hr hd hj hi))

/-- ... and a WRITE disjoint from the window commutes with it. -/
theorem writeBytesPatchComm (mm : BMap) (ra : PAddr) (rn : Nat) (w : BitVec (8 * rn))
    (pa : PAddr) (n : Nat) (v : BitVec (8 * n)) :
    accWf ra rn → accWf pa n → raccDisj ra rn pa n →
    bmWrite (bmWrite mm ra rn w) pa n v = bmWrite (bmWrite mm pa n v) ra rn w := by
  intro hr hp hd
  have hrn : rn ≤ 18446744073709551616 := by
    have := WeakInterp.paZRange ra; unfold accWf at hr; omega
  have hn : n ≤ 18446744073709551616 := by
    have := WeakInterp.paZRange pa; unfold accWf at hp; omega
  funext a
  have L1 : ∀ mm' : BMap, bmWrite mm' pa n v a =
      if (a - pa).toNat < n then some (nthByte v (a - pa).toNat) else mm' a :=
    fun mm' => bmWriteLookup mm' pa n v a hn
  have L2 : ∀ mm' : BMap, bmWrite mm' ra rn w a =
      if (a - ra).toNat < rn then some (nthByte w (a - ra).toNat) else mm' a :=
    fun mm' => bmWriteLookup mm' ra rn w a hrn
  have hno : ¬ ((a - pa).toNat < n ∧ (a - ra).toNat < rn) := by
    rintro ⟨h1, h2⟩
    have := pa.isLt
    have := ra.isLt
    have := a.isLt
    simp only [BitVec.toNat_sub, Nat.reducePow] at h1 h2
    unfold raccDisj paZ at hd
    unfold accWf paZ at hp hr
    omega
  rw [L1, L2, L2, L1]
  by_cases h1 : (a - pa).toNat < n
  · have h2 : ¬ (a - ra).toNat < rn := fun h2 => hno ⟨h1, h2⟩
    simp only [if_pos h1, if_neg h2]
  · by_cases h2 : (a - ra).toNat < rn
    · simp only [if_neg h1, if_pos h2]
    · simp only [if_neg h1, if_neg h2]

/-- THE PATCHED SC STATE: `WeakBridge.wflatSt` with the racy window overwritten by `w` -- the state
every `exec` fact in this file is about. -/
def wpatchSt (s : Wmstate) (ra : PAddr) (rn : Nat) (w : BitVec (8 * rn)) : ExecSt :=
  ⟨s.wmRegs, bmWrite (wflatMem s.wmImg s.wmLog) ra rn w, s.wmDev⟩

theorem wpatchStRegs (s : Wmstate) (ra : PAddr) (rn : Nat) (w : BitVec (8 * rn)) :
    (wpatchSt s ra rn w).regs = s.wmRegs := rfl
theorem wpatchStMem (s : Wmstate) (ra : PAddr) (rn : Nat) (w : BitVec (8 * rn)) :
    (wpatchSt s ra rn w).mem = bmWrite (wflatMem s.wmImg s.wmLog) ra rn w := rfl
theorem wpatchStDev (s : Wmstate) (ra : PAddr) (rn : Nat) (w : BitVec (8 * rn)) :
    (wpatchSt s ra rn w).dev = s.wmDev := rfl

theorem wpatchStRegSet (s : Wmstate) (ra : PAddr) (rn : Nat) (w : BitVec (8 * rn)) (r : Register)
    (v : RegisterType r) : wpatchSt (wsetReg s r v) ra rn w = (wpatchSt s ra rn w).setReg r v :=
  rfl

theorem wpatchStWs (s : Wmstate) (ra : PAddr) (rn : Nat) (w : BitVec (8 * rn)) (ws : Wstate) :
    wpatchSt (wsetWs s ws) ra rn w = wpatchSt s ra rn w := rfl

theorem wpatchStReadPost (s : Wmstate) (ra : PAddr) (rn : Nat) (w : BitVec (8 * rn)) (ak : AkInfo)
    (pa : PAddr) (ts : List Nat) : wpatchSt (wreadPost s ak pa ts) ra rn w = wpatchSt s ra rn w := by
  unfold wreadPost; split <;> rfl

theorem wpatchStDevSet (s : Wmstate) (ra : PAddr) (rn : Nat) (w : BitVec (8 * rn))
    (d : DevStates) : wpatchSt (wsetDev s d) ra rn w = (wpatchSt s ra rn w).setDev d := rfl

/-- Stage B's barrier post-state moves only what the patch does not see (Lean-only). -/
theorem wpatchStBarrier (s : Wmstate) (ra : PAddr) (rn : Nat) (w : BitVec (8 * rn))
    (b : barrier_kind) : wpatchSt (wbarrierPost s b) ra rn w = wpatchSt s ra rn w := rfl

/-- The patch of the successor of a DISJOINT write is the write over the patch. -/
theorem wpatchStWritePost (tid : Option Nat) (s : Wmstate) (ra : PAddr) (rn : Nat)
    (w : BitVec (8 * rn)) (ak : AkInfo) (pa : PAddr) (n : Nat) (v : BitVec (8 * n)) :
    accWf ra rn → accWf pa n → raccDisj ra rn pa n →
    wpatchSt (wwritePost tid s ak pa n v) ra rn w =
      (wpatchSt s ra rn w).setMem (bmWrite (wpatchSt s ra rn w).mem pa n v) := by
  intro hr hp hd
  show (⟨s.wmRegs, bmWrite (wflatMem s.wmImg (wwritePost tid s ak pa n v).wmLog) ra rn w,
      s.wmDev⟩ : ExecSt) =
    ⟨s.wmRegs, bmWrite (bmWrite (wflatMem s.wmImg s.wmLog) ra rn w) pa n v, s.wmDev⟩
  rw [wflatWrite tid s ak pa n v hp, writeBytesPatchComm _ ra rn w pa n v hr hp hd]

/-! ## 2. `wstepOkRacy`: the racy-window generalisation of `wstepOk`

Arm for arm `WeakBridge.wstepOk`, with two changes at the RAM arms.  A RAM READ must either be
DISJOINT from the window (`D`) and carry `wstepOk`'s obligations verbatim, or BE the window, and
then it carries NO pinnedness and quantifies over every admissible timestamp list and value
(filtered by `Φ`).  A RAM WRITE must be `D`, and -- unless `W` permits it -- may only occur AFTER
the racy read: `b` is `true` while the racy read is still ahead.  A permitted pre-racy write
renounces the racy read (its continuation is at phase `false`). -/

def wstepOkRacy (tid : Option Nat) (ra : PAddr) (rn : Nat) (rak : AkInfo)
    (Φ : (Nat → BitVec 8) → Prop) (D : PAddr → Nat → Prop) (W : Prop) {X : Type} :
    Bool → SailM X → Wmstate → Prop
  | _, .pure _, _ => True
  | _, .impure (.error _) _, _ => True
  | b, .impure (.ok o) k, s =>
    match o, k with
    | .regRead r, k => wstepOkRacy tid ra rn rak Φ D W b (k (s.wmRegs r)) s
    | .regWrite r v, k => wstepOkRacy tid ra rn rak Φ D W b (k PUnit.unit) (wsetReg s r v)
    | .memRead n _ req, k =>
      if mmioAcc req.pa n then
        ∀ w d', devRead s.wmDev req.pa n = some (w, d') →
          wstepOkRacy tid ra rn rak Φ D W b (k (.Ok (w, none))) (wsetDev s d')
      else
        accWf req.pa n ∧
        ( -- AWAY FROM THE WINDOW: `wstepOk`'s own arm
          (D req.pa n ∧
           (akPins (classify req.access_kind) = false →
             ∀ j, j < n → readPinned s (classify req.access_kind) (WeakInterp.accAddr req.pa j)) ∧
           (∀ w, wreadBytes s (classify req.access_kind) req.pa n (cohTs s req.pa n) = some w →
             wstepOkRacy tid ra rn rak Φ D W b (k (.Ok (w, none)))
               (wreadPost s (classify req.access_kind) req.pa (cohTs s req.pa n)))) ∨
          -- THE RACY READ: no pinnedness, ∀ admissible result
          (b = true ∧ req.pa = ra ∧ n = rn ∧ classify req.access_kind = rak ∧
           (∀ ts w, wreadBytes s (classify req.access_kind) req.pa n ts = some w →
             Φ (fun j => nthByte w j) →
             wstepOkRacy tid ra rn rak Φ D W false (k (.Ok (w, none)))
               (wreadPost s (classify req.access_kind) req.pa ts))))
    | .memWrite n _ req, k =>
      if mmioAcc req.pa n then
        match req.value with
        | some v =>
          ∀ d', devWrite s.wmDev req.pa n v = some d' →
            wstepOkRacy tid ra rn rak Φ D W b (k (.Ok (some true))) (wsetDev s d')
        | none => True
      else
        (b = false ∨ W) ∧ accWf req.pa n ∧ D req.pa n ∧
        (match req.value with
         | some v =>
           wstepOkRacy tid ra rn rak Φ D W false (k (.Ok (some true)))
             (wwritePost tid s (classify req.access_kind) req.pa n v)
         | none => True)
    | .barrier bk, k => wstepOkRacy tid ra rn rak Φ D W b (k ()) (wbarrierPost s bk)
    | .instrAnnounce _ _, k => wstepOkRacy tid ra rn rak Φ D W b (k ()) s
    | .branchAnnounce _ _, k => wstepOkRacy tid ra rn rak Φ D W b (k ()) s
    | .cacheOp _, k => wstepOkRacy tid ra rn rak Φ D W b (k ()) s
    | .tlbi _, k => wstepOkRacy tid ra rn rak Φ D W b (k ()) s
    | .takeException _, k => wstepOkRacy tid ra rn rak Φ D W b (k ()) s
    | .returnException _, k => wstepOkRacy tid ra rn rak Φ D W b (k ()) s
    | .translationStart _, k => wstepOkRacy tid ra rn rak Φ D W b (k ()) s
    | .translationEnd _, k => wstepOkRacy tid ra rn rak Φ D W b (k ()) s
    | .cycleCount, k => wstepOkRacy tid ra rn rak Φ D W b (k ()) s
    | .message _, k => wstepOkRacy tid ra rn rak Φ D W b (k ()) s
    | .getCycleCount, k => wstepOkRacy tid ra rn rak Φ D W b (k (0 : Nat)) s
    -- as in `wstepOk`: a `choose` breaks the wrun → wexec bridge
    | .choose _, _ => False
    | .readRam .., _ => True
    | .writeRam .., _ => True

/-- THE USER-FACING ADMISSIBILITY of a racy word: per byte, SOME timestamp of the log holds it,
admissibly for the load's access kind. -/
def wadm (s : Wmstate) (rak : AkInfo) (ra : PAddr) (rn : Nat) (w : BitVec (8 * rn)) : Prop :=
  ∀ j : Nat, j < rn → ∃ t : Nat, wbyteOk s rak (WeakInterp.accAddr ra j) t (nthByte w j)

theorem wadmOfWreadOk (s : Wmstate) (rak : AkInfo) (ra : PAddr) (rn : Nat) (ts : List Nat)
    (w : BitVec (8 * rn)) : wreadOk s rak ra rn ts w → wadm s rak ra rn w := by
  rintro ⟨_, hbytes⟩ j hj
  exact ⟨ts[j]!, hbytes j hj⟩

/-- THE VALUE FILTER's soundness: every admissible word passes `Φ` (what REPLACES pinnedness). -/
def wadmFilter (s : Wmstate) (rak : AkInfo) (ra : PAddr) (rn : Nat)
    (Φ : (Nat → BitVec 8) → Prop) : Prop :=
  ∀ w : BitVec (8 * rn), wadm s rak ra rn w → Φ (fun j => nthByte w j)

def wadmAny : (Nat → BitVec 8) → Prop := fun _ => True

theorem wadmFilterAny (s : Wmstate) (rak : AkInfo) (ra : PAddr) (rn : Nat) :
    wadmFilter s rak ra rn wadmAny :=
  fun _ _ => trivial

/-! ## 3. Transport: the pre-racy phase only moves VIEWS -/

theorem loadVpreMono (ws ws2 : Wstate) (aq : Bool) :
    wsLe ws ws2 → loadVpre ws aq ≤ loadVpre ws2 aq := by
  intro hle
  have h1 := wsLeVrNew _ _ hle
  have h2 := hle.2.2.2.2.2.1
  unfold loadVpre
  cases aq <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega

theorem readableWsDown (img : Image) (log : List Wmsg) (ws ws2 : Wstate) (vpre vpre2 : Nat)
    (a : Int) (t : Nat) :
    max vpre (coh ws a) ≤ max vpre2 (coh ws2 a) →
    readable img log ws2 vpre2 a t → readable img log ws vpre a t := by
  rintro hle ⟨hs, hn⟩
  exact ⟨hs, fun hw => hn (writesInMonoHi _ _ _ _ _ hle hw)⟩

/-- Deviation 4: the i-cache arm needs `s.wmItv ≤ s2.wmItv`. -/
theorem wbyteOkDown (s s2 : Wmstate) (ak : AkInfo) (a : Int) (t : Nat) (b : BitVec 8) :
    s2.wmImg = s.wmImg → s2.wmLog = s.wmLog → wsLe s.wmWs s2.wmWs → s.wmItv ≤ s2.wmItv →
    wbyteOk s2 ak a t b → wbyteOk s ak a t b := by
  rintro himg hlog hle hitv ⟨hv, hadm⟩
  unfold wimg at hv
  rw [himg, hlog] at hv
  refine ⟨hv, ?_⟩
  rw [hlog] at hadm
  cases hc : ak.akIfetch with
  | true =>
    rw [hc] at hadm
    simp only [↓reduceIte] at hadm ⊢
    exact fun hw => hadm (writesInMonoHi _ _ _ _ _ (by omega) hw)
  | false =>
    rw [hc] at hadm
    simp only [Bool.false_eq_true, ↓reduceIte] at hadm ⊢
    obtain ⟨hrd, hlat⟩ := hadm
    unfold wimg at hrd
    rw [himg] at hrd
    refine ⟨readableWsDown _ _ _ _ _ _ _ _ ?_ hrd, hlat⟩
    have := loadVpreMono s.wmWs s2.wmWs ak.akSync hle
    have := wsLeCoh _ _ a hle
    omega

theorem wadmDown (s s2 : Wmstate) (rak : AkInfo) (ra : PAddr) (rn : Nat) (w : BitVec (8 * rn)) :
    s2.wmImg = s.wmImg → s2.wmLog = s.wmLog → wsLe s.wmWs s2.wmWs → s.wmItv ≤ s2.wmItv →
    wadm s2 rak ra rn w → wadm s rak ra rn w := by
  intro himg hlog hle hitv hw j hj
  obtain ⟨t, ht⟩ := hw j hj
  exact ⟨t, wbyteOkDown s s2 rak _ t _ himg hlog hle hitv ht⟩

/-- ... and so does the filter's soundness, in the same direction. -/
theorem wadmFilterDown (s s2 : Wmstate) (rak : AkInfo) (ra : PAddr) (rn : Nat)
    (Φ : (Nat → BitVec 8) → Prop) :
    s2.wmImg = s.wmImg → s2.wmLog = s.wmLog → wsLe s.wmWs s2.wmWs → s.wmItv ≤ s2.wmItv →
    wadmFilter s rak ra rn Φ → wadmFilter s2 rak ra rn Φ := by
  intro himg hlog hle hitv hΦ w hw
  exact hΦ w (wadmDown s s2 rak ra rn w himg hlog hle hitv hw)

theorem wadmFilterSetReg (s : Wmstate) (r : Register) (v : RegisterType r) (rak : AkInfo)
    (ra : PAddr) (rn : Nat) (Φ : (Nat → BitVec 8) → Prop) :
    wadmFilter s rak ra rn Φ → wadmFilter (wsetReg s r v) rak ra rn Φ :=
  wadmFilterDown s _ rak ra rn Φ rfl rfl (wsLeRefl _) (Nat.le_refl _)

theorem wadmFilterSetDev (s : Wmstate) (d : DevStates) (rak : AkInfo) (ra : PAddr) (rn : Nat)
    (Φ : (Nat → BitVec 8) → Prop) :
    wadmFilter s rak ra rn Φ → wadmFilter (wsetDev s d) rak ra rn Φ :=
  wadmFilterDown s _ rak ra rn Φ rfl rfl (wsLeRefl _) (Nat.le_refl _)

theorem wadmFilterSetWs (s : Wmstate) (ws' : Wstate) (rak : AkInfo) (ra : PAddr) (rn : Nat)
    (Φ : (Nat → BitVec 8) → Prop) :
    wsLe s.wmWs ws' → wadmFilter s rak ra rn Φ → wadmFilter (wsetWs s ws') rak ra rn Φ :=
  fun hle => wadmFilterDown s (wsetWs s ws') rak ra rn Φ rfl rfl hle (Nat.le_refl _)

theorem wadmFilterReadPost (s : Wmstate) (ak : AkInfo) (pa : PAddr) (ts : List Nat)
    (rak : AkInfo) (ra : PAddr) (rn : Nat) (Φ : (Nat → BitVec 8) → Prop) :
    wadmFilter s rak ra rn Φ → wadmFilter (wreadPost s ak pa ts) rak ra rn Φ :=
  wadmFilterDown s _ rak ra rn Φ (wreadPostImg _ _ _ _) (wreadPostLog _ _ _ _)
    (wreadPostWsLe _ _ _ _) (Nat.le_of_eq (wreadPostItv _ _ _ _).symm)

/-- The barrier step (Lean-only, deviation 4): data views and the i-cache view both rise. -/
theorem wadmFilterBarrierPost (s : Wmstate) (b : barrier_kind) (rak : AkInfo) (ra : PAddr)
    (rn : Nat) (Φ : (Nat → BitVec 8) → Prop) :
    wadmFilter s rak ra rn Φ → wadmFilter (wbarrierPost s b) rak ra rn Φ :=
  wadmFilterDown s _ rak ra rn Φ rfl rfl (barrierPostLe _ _) (itvPostLe _ _ _)

/-! ## 4. THE BRIDGE, consumption direction

Over `wrun`, the relational interpreter.  First the window-free phase: with the racy read behind
(or never taken), the run is on the pinned fragment away from the window, and the patched memory
is carried through unchanged. -/

theorem execOfWrunWin (tid : Option Nat) (ra : PAddr) (rn : Nat) (rak : AkInfo)
    (Φ : (Nat → BitVec 8) → Prop) (D : PAddr → Nat → Prop) (w : BitVec (8 * rn)) {X : Type}
    (m : SailM X) :
    accWf ra rn → (∀ pa n, D pa n → raccDisj ra rn pa n) →
    ∀ s, wstepOkRacy tid ra rn rak Φ D False false m s → wlogWf s.wmLog →
    ∀ x s', wrun tid m s x s' →
      exec m (wpatchSt s ra rn w) = some (x, wpatchSt s' ra rn w) ∧ wlogWf s'.wmLog := by
  intro hracc hD
  induction m with
  | pure y =>
    intro s _ hwf x s' hrun
    obtain ⟨rfl, rfl⟩ := hrun
    exact ⟨rfl, hwf⟩
  | impure call k ih =>
    intro s hok hwf x s' hrun
    cases call with
    | error e => exact hrun.elim
    | ok o =>
      cases o
      case memRead n va req =>
        simp only [wstepOkRacy] at hok
        simp only [wrun] at hrun
        by_cases hd : mmioAcc req.pa n = true
        · rw [if_pos hd] at hok hrun
          rw [execMemReadDev n va req k _ hd, wpatchStDev]
          cases hdr : devRead s.wmDev req.pa n with
          | none => rw [hdr] at hrun; exact hrun.elim
          | some p =>
            obtain ⟨w0, d'⟩ := p
            rw [hdr] at hrun
            exact ih _ _ (hok w0 d' hdr) hwf _ _ hrun
        · have hd' : mmioAcc req.pa n = false := by simpa using hd
          rw [if_neg hd] at hok hrun
          rw [execMemRead n va req k _ hd', wpatchStMem]
          obtain ⟨hacc, hor⟩ := hok
          rcases hor with ⟨hdisj, hpin, hk⟩ | ⟨hb, _⟩
          · obtain ⟨w0, ts, hokr, hrun⟩ := hrun
            have hts := wreadPinnedTs s _ req.pa n ts w0 hpin hokr
            subst hts
            have hrb := wreadBytesComplete _ _ _ _ _ _ hokr
            obtain ⟨hex, hwf'⟩ := ih _ _ (hk w0 hrb) (wlogWfReadPost _ _ _ _ hwf) _ _ hrun
            rw [wpatchStReadPost] at hex
            rw [readBytesPatchDisj _ ra rn w _ _ hracc hacc (hD _ _ hdisj)]
            rw [wreadBytesReadBytes s _ req.pa n hwf hacc] at hrb
            rw [hrb]
            exact ⟨hex, hwf'⟩
          · cases hb
      case memWrite n va req =>
        simp only [wstepOkRacy] at hok
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
            rw [execMemWriteDev n va req k _ v hv hd, wpatchStDev]
            cases hdw : devWrite s.wmDev req.pa n v with
            | none => rw [hdw] at hrun; exact hrun.elim
            | some d' =>
              rw [hdw] at hrun
              exact ih _ _ (hok d' hdw) hwf _ _ hrun
          · have hd' : mmioAcc req.pa n = false := by simpa using hd
            rw [if_neg hd] at hok hrun
            simp only [hv] at hok hrun
            obtain ⟨_, hacc, hdisj, hok⟩ := hok
            rw [execMemWrite n va req k _ v hv hd']
            obtain ⟨hex, hwf'⟩ := ih _ _ hok (wflatWriteWf _ _ _ _ _ _ hwf hacc) _ _ hrun
            rw [wpatchStWritePost _ _ _ _ _ _ _ _ _ hracc hacc (hD _ _ hdisj)] at hex
            exact ⟨hex, hwf'⟩
      case choose => simp only [wstepOkRacy] at hok
      case readRam => exact hrun.elim
      case writeRam => exact hrun.elim
      all_goals
        simp only [wstepOkRacy] at hok
        simp only [wrun] at hrun
        simp only [exec]
        exact ih _ _ hok hwf _ _ hrun

/-- THE BRIDGE THEOREM, in the form the induction wants: the admissibility of the racy value is
reported at the state `s0` the WHOLE step started in, while the run is at an intermediate state
`s` that differs from it only in views (deviation 4: and in the i-cache view). -/
theorem execOfWrunRacyGen (tid : Option Nat) (ra : PAddr) (rn : Nat) (rak : AkInfo)
    (Φ : (Nat → BitVec 8) → Prop) (D : PAddr → Nat → Prop) {X : Type} (m : SailM X) :
    accWf ra rn → (∀ pa n, D pa n → raccDisj ra rn pa n) →
    ∀ (s0 s : Wmstate),
      wadmFilter s0 rak ra rn Φ →
      wstepOkRacy tid ra rn rak Φ D False true m s →
      s.wmImg = s0.wmImg → s.wmLog = s0.wmLog → wsLe s0.wmWs s.wmWs → s0.wmItv ≤ s.wmItv →
      wlogWf s.wmLog →
      (wreadBytes s0 rak ra rn (cohTs s0 ra rn)).isSome = true →
    ∀ x s', wrun tid m s x s' →
      ∃ w : BitVec (8 * rn),
        wadm s0 rak ra rn w ∧
        exec m (wpatchSt s ra rn w) = some (x, wpatchSt s' ra rn w) ∧
        wlogWf s'.wmLog := by
  intro hracc hD
  induction m with
  | pure y =>
    -- the run never took the racy read: the CANONICAL word serves
    intro s0 s _ _ _ _ _ _ hwf hrd x s' hrun
    obtain ⟨rfl, rfl⟩ := hrun
    obtain ⟨w0, hw0⟩ := Option.isSome_iff_exists.1 hrd
    exact ⟨w0, wadmOfWreadOk _ _ _ _ _ _ (wreadBytesSpec _ _ _ _ _ _ hw0), rfl, hwf⟩
  | impure call k ih =>
    intro s0 s hΦ hok himg hlog hle hitv hwf hrd x s' hrun
    cases call with
    | error e => exact hrun.elim
    | ok o =>
      cases o
      case memRead n va req =>
        simp only [wstepOkRacy] at hok
        simp only [wrun] at hrun
        by_cases hd : mmioAcc req.pa n = true
        · rw [if_pos hd] at hok hrun
          cases hdr : devRead s.wmDev req.pa n with
          | none => rw [hdr] at hrun; exact hrun.elim
          | some p =>
            obtain ⟨w0, d'⟩ := p
            rw [hdr] at hrun
            obtain ⟨w, hadm, hex, hwf'⟩ :=
              ih _ s0 _ hΦ (hok w0 d' hdr) himg hlog hle hitv hwf hrd _ _ hrun
            refine ⟨w, hadm, ?_, hwf'⟩
            rw [execMemReadDev n va req k _ hd, wpatchStDev, hdr]
            exact hex
        · have hd' : mmioAcc req.pa n = false := by simpa using hd
          rw [if_neg hd] at hok hrun
          obtain ⟨hacc, hor⟩ := hok
          obtain ⟨w0, ts, hokr, hrun⟩ := hrun
          rcases hor with ⟨hdisj, hpin, hk⟩ | ⟨_, hpa, hn, hak, hk⟩
          · -- a pinned read away from the window
            have hts := wreadPinnedTs s _ req.pa n ts w0 hpin hokr
            subst hts
            have hrb := wreadBytesComplete _ _ _ _ _ _ hokr
            obtain ⟨w, hadm, hex, hwf'⟩ := ih _ s0 _ hΦ (hk w0 hrb)
              ((wreadPostImg _ _ _ _).trans himg) ((wreadPostLog _ _ _ _).trans hlog)
              (wsLeTrans hle (wreadPostWsLe _ _ _ _)) (by rw [wreadPostItv]; exact hitv)
              (wlogWfReadPost _ _ _ _ hwf) hrd _ _ hrun
            refine ⟨w, hadm, ?_, hwf'⟩
            rw [wpatchStReadPost] at hex
            rw [wreadBytesReadBytes s _ req.pa n hwf hacc] at hrb
            rw [execMemRead n va req k _ hd', wpatchStMem,
              readBytesPatchDisj _ ra rn w _ _ hracc hacc (hD _ _ hdisj), hrb]
            exact hex
          · -- THE RACY READ
            subst hn
            subst hpa
            subst hak
            have hrb := wreadBytesComplete _ _ _ _ _ _ hokr
            -- the filter is discharged at the PRE-state, which is what `wadmDown` transports
            -- the admissibility to
            have hadm0 := wadmDown s0 s _ _ _ w0 himg hlog hle hitv (wadmOfWreadOk _ _ _ _ _ _ hokr)
            obtain ⟨hex, hwf'⟩ := execOfWrunWin tid _ _ _ Φ D w0 _ hracc hD _
              (hk ts w0 hrb (hΦ w0 hadm0)) (wlogWfReadPost _ _ _ _ hwf) _ _ hrun
            rw [wpatchStReadPost] at hex
            refine ⟨w0, hadm0, ?_, hwf'⟩
            rw [execMemRead n va req k _ hd', wpatchStMem,
              readBytesOfBytes _ _ _ w0 (fun j hj => writeBytesLookupAt _ _ _ w0 j hracc hj)]
            exact hex
      case memWrite n va req =>
        simp only [wstepOkRacy] at hok
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
              obtain ⟨w, hadm, hex, hwf'⟩ :=
                ih _ s0 _ hΦ (hok d' hdw) himg hlog hle hitv hwf hrd _ _ hrun
              refine ⟨w, hadm, ?_, hwf'⟩
              rw [execMemWriteDev n va req k _ v hv hd, wpatchStDev, hdw]
              exact hex
          · -- forbidden before the racy read
            rw [if_neg hd] at hok
            obtain ⟨hb, _⟩ := hok
            rcases hb with hb | hb
            · cases hb
            · exact hb.elim
      case barrier bk =>
        simp only [wstepOkRacy] at hok
        simp only [wrun] at hrun
        obtain ⟨w, hadm, hex, hwf'⟩ := ih _ s0 _ hΦ hok himg hlog
          (wsLeTrans hle (barrierPostLe _ _)) (Nat.le_trans hitv (itvPostLe _ _ _)) hwf hrd _ _ hrun
        exact ⟨w, hadm, by simp only [exec]; exact hex, hwf'⟩
      case choose => simp only [wstepOkRacy] at hok
      case readRam => exact hrun.elim
      case writeRam => exact hrun.elim
      all_goals
        simp only [wstepOkRacy] at hok
        simp only [wrun] at hrun
        obtain ⟨w, hadm, hex, hwf'⟩ := ih _ s0 _ hΦ hok himg hlog hle hitv hwf hrd _ _ hrun
        exact ⟨w, hadm, by simp only [exec]; exact hex, hwf'⟩

/-- THE BRIDGE THEOREM: whatever the racy run did, there is a word `w` -- admissible for the
window in the PRE-state, byte by byte -- such that the whole step IS the SC run over the flat
memory PATCHED at the window with it. -/
theorem execOfWrunRacy (tid : Option Nat) (ra : PAddr) (rn : Nat) (rak : AkInfo)
    (Φ : (Nat → BitVec 8) → Prop) (D : PAddr → Nat → Prop) {X : Type} (m : SailM X) :
    accWf ra rn → (∀ pa n, D pa n → raccDisj ra rn pa n) →
    ∀ s, wadmFilter s rak ra rn Φ → wlogWf s.wmLog →
      (wreadBytes s rak ra rn (cohTs s ra rn)).isSome = true →
      wstepOkRacy tid ra rn rak Φ D False true m s →
    ∀ x s', wrun tid m s x s' →
      ∃ w : BitVec (8 * rn),
        wadm s rak ra rn w ∧
        exec m (wpatchSt s ra rn w) = some (x, wpatchSt s' ra rn w) ∧
        wlogWf s'.wmLog := by
  intro hracc hD s hΦ hwf hrd hok x s' hrun
  exact execOfWrunRacyGen tid ra rn rak Φ D m hracc hD s s hΦ hok rfl rfl (wsLeRefl _)
    (Nat.le_refl _) hwf hrd x s' hrun

/-! ## 4b. THE GAIN: the racy read's VIEW content, taken from the model

The bridge's own induction knows the timestamp list the racy read took, and the read step puts
it under `wVrOld` on the spot (`loadPostRunVrOld`); every later step only raises the floor.  The
side condition is about the READER: the hart has not stored to the window (no forwarding).  A run
that never touches the window is patch-INDEPENDENT -- the second disjunct. -/

/-- The window is not in this hart's forward bank. -/
def wunwritten (ws : Wstate) (ra : PAddr) (rn : Nat) : Prop :=
  ∀ j : Nat, j < rn → get? ws.wFwd (WeakInterp.accAddr ra j) = none

/-- `wadm` with the timestamps pinned under the SUCCESSOR's read floor. -/
def wgain (s0 s' : Wmstate) (rak : AkInfo) (ra : PAddr) (rn : Nat) (w : BitVec (8 * rn)) : Prop :=
  ∀ j : Nat, j < rn →
    ∃ t : Nat, wbyteOk s0 rak (WeakInterp.accAddr ra j) t (nthByte w j) ∧ t ≤ s'.wmWs.wVrOld

theorem wgainWadm (s0 s' : Wmstate) (rak : AkInfo) (ra : PAddr) (rn : Nat) (w : BitVec (8 * rn)) :
    wgain s0 s' rak ra rn w → wadm s0 rak ra rn w := by
  intro hg j hj
  obtain ⟨t, hok, _⟩ := hg j hj
  exact ⟨t, hok⟩

theorem wgainMono (s0 s' s'' : Wmstate) (rak : AkInfo) (ra : PAddr) (rn : Nat)
    (w : BitVec (8 * rn)) :
    wsLe s'.wmWs s''.wmWs → wgain s0 s' rak ra rn w → wgain s0 s'' rak ra rn w := by
  intro hle hg j hj
  obtain ⟨t, hok, ht⟩ := hg j hj
  exact ⟨t, hok, Nat.le_trans ht (wsLeVrOld _ _ hle)⟩

/-- The forward bank is untouched by everything the pre-racy phase may do. -/
theorem wreadPostFwd (s : Wmstate) (ak : AkInfo) (pa : PAddr) (ts : List Nat) :
    (wreadPost s ak pa ts).wmWs.wFwd = s.wmWs.wFwd := by
  unfold wreadPost
  split
  · rfl
  · exact loadPostRunFwd _ _ _ _

theorem barrierPostFwd (ws : Wstate) (b : barrier_kind) : (barrierPost ws b).wFwd = ws.wFwd := by
  cases b <;> rfl

/-- THE READ STEP'S OWN GAIN, at the fold the interpreter builds. -/
theorem wreadPostVrOld (s : Wmstate) (ak : AkInfo) (pa : PAddr) (n : Nat) (ts : List Nat)
    (j : Nat) :
    ak.akIfetch = false → wunwritten s.wmWs pa n → ts.length = n → j < n →
    ts[j]! ≤ (wreadPost s ak pa ts).wmWs.wVrOld := by
  intro hc hun hlen hj
  unfold wreadPost
  rw [hc]
  simp only [Bool.false_eq_true, ↓reduceIte]
  exact loadPostRunVrOld _ _ _ _ _ (by omega) (hun j hj)

/-- THE STRENGTHENED BRIDGE: `execOfWrunRacyGen` with the gain threaded through the induction,
and the patch-independence escape hatch for a run that never read the window. -/
theorem execOfWrunGainGen (tid : Option Nat) (ra : PAddr) (rn : Nat) (rak : AkInfo)
    (Φ : (Nat → BitVec 8) → Prop) (D : PAddr → Nat → Prop) {X : Type} (m : SailM X) :
    accWf ra rn → (∀ pa n, D pa n → raccDisj ra rn pa n) → rak.akIfetch = false →
    ∀ (s0 s : Wmstate),
      wadmFilter s0 rak ra rn Φ →
      wstepOkRacy tid ra rn rak Φ D False true m s →
      s.wmImg = s0.wmImg → s.wmLog = s0.wmLog → wsLe s0.wmWs s.wmWs → s0.wmItv ≤ s.wmItv →
      s.wmWs.wFwd = s0.wmWs.wFwd →
      wunwritten s0.wmWs ra rn →
      wlogWf s.wmLog →
      (wreadBytes s0 rak ra rn (cohTs s0 ra rn)).isSome = true →
    ∀ x s', wrun tid m s x s' →
      ∃ w : BitVec (8 * rn),
        wadm s0 rak ra rn w ∧
        exec m (wpatchSt s ra rn w) = some (x, wpatchSt s' ra rn w) ∧
        wlogWf s'.wmLog ∧
        (wgain s0 s' rak ra rn w ∨
         ∀ u : BitVec (8 * rn), exec m (wpatchSt s ra rn u) = some (x, wpatchSt s' ra rn u)) := by
  intro hracc hD hakc
  induction m with
  | pure y =>
    -- the run never took the racy read: the CANONICAL word serves, and the whole step is
    -- patch-independent
    intro s0 s _ _ _ _ _ _ _ _ hwf hrd x s' hrun
    obtain ⟨rfl, rfl⟩ := hrun
    obtain ⟨w0, hw0⟩ := Option.isSome_iff_exists.1 hrd
    exact ⟨w0, wadmOfWreadOk _ _ _ _ _ _ (wreadBytesSpec _ _ _ _ _ _ hw0), rfl, hwf,
      Or.inr fun _ => rfl⟩
  | impure call k ih =>
    intro s0 s hΦ hok himg hlog hle hitv hfwd hun hwf hrd x s' hrun
    cases call with
    | error e => exact hrun.elim
    | ok o =>
      cases o
      case memRead n va req =>
        simp only [wstepOkRacy] at hok
        simp only [wrun] at hrun
        by_cases hd : mmioAcc req.pa n = true
        · rw [if_pos hd] at hok hrun
          cases hdr : devRead s.wmDev req.pa n with
          | none => rw [hdr] at hrun; exact hrun.elim
          | some p =>
            obtain ⟨w0, d'⟩ := p
            rw [hdr] at hrun
            obtain ⟨w, hadm, hex, hwf', hg⟩ :=
              ih _ s0 _ hΦ (hok w0 d' hdr) himg hlog hle hitv hfwd hun hwf hrd _ _ hrun
            have hstep : ∀ u : BitVec (8 * rn),
                exec (FreeM.impure (.ok (.memRead n va req)) k) (wpatchSt s ra rn u) =
                  exec (k (.Ok (w0, none))) (wpatchSt (wsetDev s d') ra rn u) := by
              intro u
              rw [execMemReadDev n va req k _ hd, wpatchStDev, hdr]
              rfl
            refine ⟨w, hadm, by rw [hstep]; exact hex, hwf', ?_⟩
            rcases hg with hg | huni
            · exact Or.inl hg
            · exact Or.inr fun u => by rw [hstep]; exact huni u
        · have hd' : mmioAcc req.pa n = false := by simpa using hd
          rw [if_neg hd] at hok hrun
          obtain ⟨hacc, hor⟩ := hok
          obtain ⟨w0, ts, hokr, hrun⟩ := hrun
          rcases hor with ⟨hdisj, hpin, hk⟩ | ⟨_, hpa, hn, hak, hk⟩
          · -- a pinned read away from the window
            have hts := wreadPinnedTs s _ req.pa n ts w0 hpin hokr
            subst hts
            have hrb := wreadBytesComplete _ _ _ _ _ _ hokr
            obtain ⟨w, hadm, hex, hwf', hg⟩ := ih _ s0 _ hΦ (hk w0 hrb)
              ((wreadPostImg _ _ _ _).trans himg) ((wreadPostLog _ _ _ _).trans hlog)
              (wsLeTrans hle (wreadPostWsLe _ _ _ _)) (by rw [wreadPostItv]; exact hitv)
              ((wreadPostFwd _ _ _ _).trans hfwd) hun
              (wlogWfReadPost _ _ _ _ hwf) hrd _ _ hrun
            rw [wreadBytesReadBytes s _ req.pa n hwf hacc] at hrb
            have hstep : ∀ u : BitVec (8 * rn),
                exec (FreeM.impure (.ok (.memRead n va req)) k) (wpatchSt s ra rn u) =
                  exec (k (.Ok (w0, none)))
                    (wpatchSt (wreadPost s (classify req.access_kind) req.pa (cohTs s req.pa n))
                      ra rn u) := by
              intro u
              rw [execMemRead n va req k _ hd', wpatchStMem,
                readBytesPatchDisj _ ra rn u _ _ hracc hacc (hD _ _ hdisj), hrb, wpatchStReadPost]
            refine ⟨w, hadm, by rw [hstep]; exact hex, hwf', ?_⟩
            rcases hg with hg | huni
            · exact Or.inl hg
            · exact Or.inr fun u => by rw [hstep]; exact huni u
          · -- THE RACY READ -- and this is where the gain is minted
            subst hn
            subst hpa
            subst hak
            have hrb := wreadBytesComplete _ _ _ _ _ _ hokr
            have hadm0 := wadmDown s0 s _ _ _ w0 himg hlog hle hitv (wadmOfWreadOk _ _ _ _ _ _ hokr)
            obtain ⟨hex, hwf'⟩ := execOfWrunWin tid _ _ _ Φ D w0 _ hracc hD _
              (hk ts w0 hrb (hΦ w0 hadm0)) (wlogWfReadPost _ _ _ _ hwf) _ _ hrun
            rw [wpatchStReadPost] at hex
            refine ⟨w0, hadm0, ?_, hwf', Or.inl ?_⟩
            · rw [execMemRead n va req k _ hd', wpatchStMem,
                readBytesOfBytes _ _ _ w0 (fun j hj => writeBytesLookupAt _ _ _ w0 j hracc hj)]
              exact hex
            · -- the timestamps the read took are under the successor's floor
              obtain ⟨hlen, hbytes⟩ := hokr
              refine wgainMono s0 _ s' _ _ _ _ (wrunWsLe _ _ _ _ _ hrun) ?_
              intro j hj
              refine ⟨ts[j]!, wbyteOkDown s0 s _ _ _ _ himg hlog hle hitv (hbytes j hj), ?_⟩
              exact wreadPostVrOld s _ req.pa _ ts j hakc
                (fun i hi => by rw [hfwd]; exact hun i hi) hlen hj
      case memWrite n va req =>
        simp only [wstepOkRacy] at hok
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
              obtain ⟨w, hadm, hex, hwf', hg⟩ :=
                ih _ s0 _ hΦ (hok d' hdw) himg hlog hle hitv hfwd hun hwf hrd _ _ hrun
              have hstep : ∀ u : BitVec (8 * rn),
                  exec (FreeM.impure (.ok (.memWrite n va req)) k) (wpatchSt s ra rn u) =
                    exec (k (.Ok (some true))) (wpatchSt (wsetDev s d') ra rn u) := by
                intro u
                rw [execMemWriteDev n va req k _ v hv hd, wpatchStDev, hdw]
                rfl
              refine ⟨w, hadm, by rw [hstep]; exact hex, hwf', ?_⟩
              rcases hg with hg | huni
              · exact Or.inl hg
              · exact Or.inr fun u => by rw [hstep]; exact huni u
          · -- forbidden before the racy read
            rw [if_neg hd] at hok
            obtain ⟨hb, _⟩ := hok
            rcases hb with hb | hb
            · cases hb
            · exact hb.elim
      case barrier bk =>
        simp only [wstepOkRacy] at hok
        simp only [wrun] at hrun
        obtain ⟨w, hadm, hex, hwf', hg⟩ := ih _ s0 _ hΦ hok himg hlog
          (wsLeTrans hle (barrierPostLe _ _)) (Nat.le_trans hitv (itvPostLe _ _ _))
          ((barrierPostFwd _ _).trans hfwd) hun hwf hrd _ _ hrun
        refine ⟨w, hadm, by simp only [exec]; exact hex, hwf', ?_⟩
        rcases hg with hg | huni
        · exact Or.inl hg
        · exact Or.inr fun u => by simp only [exec]; exact huni u
      case choose => simp only [wstepOkRacy] at hok
      case readRam => exact hrun.elim
      case writeRam => exact hrun.elim
      all_goals
        simp only [wstepOkRacy] at hok
        simp only [wrun] at hrun
        obtain ⟨w, hadm, hex, hwf', hg⟩ :=
          ih _ s0 _ hΦ hok himg hlog hle hitv hfwd hun hwf hrd _ _ hrun
        refine ⟨w, hadm, by simp only [exec]; exact hex, hwf', ?_⟩
        rcases hg with hg | huni
        · exact Or.inl hg
        · exact Or.inr fun u => by simp only [exec]; exact huni u

theorem execOfWrunGain (tid : Option Nat) (ra : PAddr) (rn : Nat) (rak : AkInfo)
    (Φ : (Nat → BitVec 8) → Prop) (D : PAddr → Nat → Prop) {X : Type} (m : SailM X) :
    accWf ra rn → (∀ pa n, D pa n → raccDisj ra rn pa n) → rak.akIfetch = false →
    ∀ s, wadmFilter s rak ra rn Φ → wlogWf s.wmLog →
      (wreadBytes s rak ra rn (cohTs s ra rn)).isSome = true →
      wunwritten s.wmWs ra rn →
      wstepOkRacy tid ra rn rak Φ D False true m s →
    ∀ x s', wrun tid m s x s' →
      ∃ w : BitVec (8 * rn),
        wadm s rak ra rn w ∧
        exec m (wpatchSt s ra rn w) = some (x, wpatchSt s' ra rn w) ∧
        wlogWf s'.wmLog ∧
        (wgain s s' rak ra rn w ∨
         ∀ u : BitVec (8 * rn), exec m (wpatchSt s ra rn u) = some (x, wpatchSt s' ra rn u)) := by
  intro hracc hD hakc s hΦ hwf hrd hun hok x s' hrun
  exact execOfWrunGainGen tid ra rn rak Φ D m hracc hD hakc s s hΦ hok rfl rfl (wsLeRefl _)
    (Nat.le_refl _) rfl hun hwf hrd x s' hrun

/-! ## 5. Reducibility, and the `wexecCovers` mirror

`WeakExec.wpWrunStep` asks for ONE witness that the weak machine can step.  It is obtained at the
CANONICAL (latest) value of the window -- which IS pinned -- so the caller's ORDINARY `exec` fact
about `wflatSt σ` serves. -/

theorem wexecOfExecRacy (tid : Option Nat) (ra : PAddr) (rn : Nat) (rak : AkInfo)
    (Φ : (Nat → BitVec 8) → Prop) (D : PAddr → Nat → Prop) (W : Prop) {X : Type} (m : SailM X) :
    accWf ra rn →
    ∀ b s, wstepOkRacy tid ra rn rak Φ D W b m s → wlogWf s.wmLog →
      (b = true → wadmFilter s rak ra rn Φ) →
    ∀ x t', exec m (wflatSt s) = some (x, t') →
      ∃ χ s' χ', wexec tid m χ s = some (x, s', χ') ∧ wflatSt s' = t' := by
  intro hracc
  induction m with
  | pure y =>
    intro b s _ _ _ x t' h
    simp only [exec, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨[], s, [], rfl, rfl⟩
  | impure call k ih =>
    intro b s hok hwf hΦ x t' h
    cases call with
    | error e => simp [exec] at h
    | ok o =>
      cases o
      case memRead n va req =>
        simp only [wstepOkRacy] at hok
        by_cases hd : mmioAcc req.pa n = true
        · rw [if_pos hd] at hok
          rw [execMemReadDev n va req k _ hd, wflatStDev] at h
          cases hdr : devRead s.wmDev req.pa n with
          | none => rw [hdr] at h; cases h
          | some p =>
            obtain ⟨w0, d'⟩ := p
            rw [hdr] at h
            obtain ⟨χ, s2, χ', hw, heq⟩ := ih _ _ _ (hok w0 d' hdr) hwf
              (fun hb => wadmFilterSetDev _ _ _ _ _ _ (hΦ hb)) _ _ h
            exact ⟨χ, s2, χ', by simp only [wexec, if_pos hd, hdr]; exact hw, heq⟩
        · have hd' : mmioAcc req.pa n = false := by simpa using hd
          rw [if_neg hd] at hok
          obtain ⟨hacc, hor⟩ := hok
          rw [execMemRead n va req k _ hd', wflatStMem] at h
          cases hbr : bmRead (wflatMem s.wmImg s.wmLog) req.pa n with
          | none => rw [hbr] at h; cases h
          | some w0 =>
            rw [hbr] at h
            have hrb : wreadBytes s (classify req.access_kind) req.pa n (cohTs s req.pa n) =
                some w0 := by
              rw [wreadBytesReadBytes s _ req.pa n hwf hacc, hbr]
            have h2 : exec (k (.Ok (w0, none)))
                (wflatSt (wreadPost s (classify req.access_kind) req.pa (cohTs s req.pa n))) =
                some (x, t') := by
              rw [wflatStReadPost]; exact h
            rcases hor with ⟨_, _, hk⟩ | ⟨hbt, hpa, hn, hak, hk⟩
            · obtain ⟨χ, s2, χ', hw, heq⟩ := ih _ _ _ (hk w0 hrb) (wlogWfReadPost _ _ _ _ hwf)
                (fun hb => wadmFilterReadPost _ _ _ _ _ _ _ _ (hΦ hb)) _ _ h2
              exact ⟨cohTs s req.pa n :: χ, s2, χ',
                by simp only [wexec, if_neg hd, List.head?_cons, List.tail_cons, hrb]; exact hw, heq⟩
            · subst hn
              subst hpa
              subst hak
              -- the CANONICAL word is admissible, so the filter accepts it
              have hp2 := hk (cohTs s req.pa n) w0 hrb
                (hΦ hbt w0 (wadmOfWreadOk _ _ _ _ _ _ (wreadBytesSpec _ _ _ _ _ _ hrb)))
              obtain ⟨χ, s2, χ', hw, heq⟩ := ih _ _ _ hp2 (wlogWfReadPost _ _ _ _ hwf)
                (fun hb => by cases hb) _ _ h2
              exact ⟨cohTs s req.pa n :: χ, s2, χ',
                by simp only [wexec, if_neg hd, List.head?_cons, List.tail_cons, hrb]; exact hw, heq⟩
      case memWrite n va req =>
        simp only [wstepOkRacy] at hok
        cases hv : req.value with
        | none =>
          simp only [exec, hv] at h
          cases h
        | some v =>
          by_cases hd : mmioAcc req.pa n = true
          · rw [if_pos hd] at hok
            simp only [hv] at hok
            rw [execMemWriteDev n va req k _ v hv hd, wflatStDev] at h
            cases hdw : devWrite s.wmDev req.pa n v with
            | none => rw [hdw] at h; cases h
            | some d' =>
              rw [hdw] at h
              obtain ⟨χ, s2, χ', hw, heq⟩ := ih _ _ _ (hok d' hdw) hwf
                (fun hb => wadmFilterSetDev _ _ _ _ _ _ (hΦ hb)) _ _ h
              exact ⟨χ, s2, χ', by simp only [wexec, if_pos hd, hv, hdw]; exact hw, heq⟩
          · have hd' : mmioAcc req.pa n = false := by simpa using hd
            rw [if_neg hd] at hok
            simp only [hv] at hok
            obtain ⟨_, hacc, _, hok⟩ := hok
            rw [execMemWrite n va req k _ v hv hd'] at h
            have h2 : exec (k (.Ok (some true)))
                (wflatSt (wwritePost tid s (classify req.access_kind) req.pa n v)) =
                some (x, t') := by
              rw [wflatStWritePost _ _ _ _ _ _ hacc]; exact h
            obtain ⟨χ, s2, χ', hw, heq⟩ := ih _ _ _ hok (wflatWriteWf _ _ _ _ _ _ hwf hacc)
              (fun hb => by cases hb) _ _ h2
            exact ⟨χ, s2, χ', by simp only [wexec, if_neg hd, hv]; exact hw, heq⟩
      case regWrite r v =>
        simp only [wstepOkRacy] at hok
        simp only [exec] at h
        obtain ⟨χ, s2, χ', hw, heq⟩ := ih _ _ _ hok hwf
          (fun hb => wadmFilterSetReg _ _ _ _ _ _ _ (hΦ hb)) _ _ h
        exact ⟨χ, s2, χ', by simp only [wexec]; exact hw, heq⟩
      case barrier bk =>
        simp only [wstepOkRacy] at hok
        simp only [exec] at h
        obtain ⟨χ, s2, χ', hw, heq⟩ := ih _ _ _ hok hwf
          (fun hb => wadmFilterBarrierPost _ _ _ _ _ _ (hΦ hb)) _ _ h
        exact ⟨χ, s2, χ', by simp only [wexec]; exact hw, heq⟩
      case choose => simp only [wstepOkRacy] at hok
      all_goals first
        | (simp only [exec, reduceCtorEq] at h; done)
        | (simp only [wstepOkRacy] at hok
           simp only [exec] at h
           obtain ⟨χ, s2, χ', hw, heq⟩ := ih _ _ _ hok hwf hΦ _ _ h
           exact ⟨χ, s2, χ', by simp only [wexec]; exact hw, heq⟩)

/-- The `wexecCovers` mirror: every relational successor of a racy run is a functional one at
SOME oracle (deviation 4: both read arms cons the chosen timestamps). -/
theorem wrunWexecRacy (tid : Option Nat) (ra : PAddr) (rn : Nat) (rak : AkInfo)
    (Φ : (Nat → BitVec 8) → Prop) (D : PAddr → Nat → Prop) (W : Prop) {X : Type} (m : SailM X) :
    ∀ b s, wstepOkRacy tid ra rn rak Φ D W b m s →
      (b = true → wadmFilter s rak ra rn Φ) →
    ∀ x s', wrun tid m s x s' → ∃ χ χ', wexec tid m χ s = some (x, s', χ') := by
  induction m with
  | pure y =>
    intro b s _ _ x s' hrun
    obtain ⟨rfl, rfl⟩ := hrun
    exact ⟨[], [], rfl⟩
  | impure call k ih =>
    intro b s hok hΦ x s' hrun
    cases call with
    | error e => exact hrun.elim
    | ok o =>
      cases o
      case memRead n va req =>
        simp only [wstepOkRacy] at hok
        simp only [wrun] at hrun
        by_cases hd : mmioAcc req.pa n = true
        · rw [if_pos hd] at hok hrun
          cases hdr : devRead s.wmDev req.pa n with
          | none => rw [hdr] at hrun; exact hrun.elim
          | some p =>
            obtain ⟨w0, d'⟩ := p
            rw [hdr] at hrun
            obtain ⟨χ, χ', hex⟩ := ih _ _ _ (hok w0 d' hdr)
              (fun hb => wadmFilterSetDev _ _ _ _ _ _ (hΦ hb)) _ _ hrun
            exact ⟨χ, χ', by simp only [wexec, if_pos hd, hdr]; exact hex⟩
        · rw [if_neg hd] at hok hrun
          obtain ⟨w0, ts, hokr, hrun⟩ := hrun
          obtain ⟨_, hor⟩ := hok
          have hrb := wreadBytesComplete _ _ _ _ _ _ hokr
          rcases hor with ⟨_, hpin, hk⟩ | ⟨hbt, hpa, hn, hak, hk⟩
          · have hts := wreadPinnedTs s _ _ _ _ _ hpin hokr
            subst hts
            obtain ⟨χ, χ', hex⟩ := ih _ _ _ (hk w0 hrb)
              (fun hb => wadmFilterReadPost _ _ _ _ _ _ _ _ (hΦ hb)) _ _ hrun
            exact ⟨cohTs s req.pa n :: χ, χ',
              by simp only [wexec, if_neg hd, List.head?_cons, List.tail_cons, hrb]; exact hex⟩
          · subst hn
            subst hpa
            subst hak
            -- the word the run actually read is admissible, so the filter accepts it
            obtain ⟨χ, χ', hex⟩ := ih _ _ _
              (hk ts w0 hrb (hΦ hbt w0 (wadmOfWreadOk _ _ _ _ _ _ hokr)))
              (fun hb => by cases hb) _ _ hrun
            exact ⟨ts :: χ, χ',
              by simp only [wexec, if_neg hd, List.head?_cons, List.tail_cons, hrb]; exact hex⟩
      case memWrite n va req =>
        simp only [wstepOkRacy] at hok
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
                (fun hb => wadmFilterSetDev _ _ _ _ _ _ (hΦ hb)) _ _ hrun
              exact ⟨χ, χ', by simp only [wexec, if_pos hd, hv, hdw]; exact hex⟩
          · rw [if_neg hd] at hok hrun
            simp only [hv] at hok hrun
            obtain ⟨_, _, _, hok⟩ := hok
            obtain ⟨χ, χ', hex⟩ := ih _ _ _ hok (fun hb => by cases hb) _ _ hrun
            exact ⟨χ, χ', by simp only [wexec, if_neg hd, hv]; exact hex⟩
      case regWrite r v =>
        simp only [wstepOkRacy] at hok
        simp only [wrun] at hrun
        obtain ⟨χ, χ', hex⟩ := ih _ _ _ hok
          (fun hb => wadmFilterSetReg _ _ _ _ _ _ _ (hΦ hb)) _ _ hrun
        exact ⟨χ, χ', by simp only [wexec]; exact hex⟩
      case barrier bk =>
        simp only [wstepOkRacy] at hok
        simp only [wrun] at hrun
        obtain ⟨χ, χ', hex⟩ := ih _ _ _ hok
          (fun hb => wadmFilterBarrierPost _ _ _ _ _ _ (hΦ hb)) _ _ hrun
        exact ⟨χ, χ', by simp only [wexec]; exact hex⟩
      case choose => simp only [wstepOkRacy] at hok
      case readRam => exact hrun.elim
      case writeRam => exact hrun.elim
      all_goals
        simp only [wstepOkRacy] at hok
        simp only [wrun] at hrun
        obtain ⟨χ, χ', hex⟩ := ih _ _ _ hok hΦ _ _ hrun
        exact ⟨χ, χ', by simp only [wexec]; exact hex⟩

/-! ## 6. THE RULE

`WeakInstr.wpWinstr`'s racy twin, over `WeakExec.wpWrunStep`.  The caller supplies that the
window is IN memory and ONE ordinary `exec` fact about `wflatSt σ` (the reducibility witness); it
gets back the racy word `w`, its per-byte admissibility, and the step described as an `exec` over
`wpatchSt σ ra rn w`. -/

def wstepPostRacy (σ σ' : Wmstate) : Prop :=
  σ'.wmImg = σ.wmImg ∧
  (∃ l, σ'.wmLog = σ.wmLog ++ l) ∧
  wsLe σ.wmWs σ'.wmWs ∧
  wlogWf σ'.wmLog ∧
  wsBounded σ'.wmWs σ'.wmLog.length

def wracyCert (cid : Nat) (pc : BitVec 64) (ra : PAddr) (rn : Nat) (rak : AkInfo)
    (Φ : (Nat → BitVec 8) → Prop) (P : Wmstate → Prop) (Q : Wmstate → Wmstate → Prop) : Prop :=
  ∀ (σ : Wmstate) (tick : Bool),
    σ.wmRegs .PC = pc →
    accWf pc 4 →
    (∀ j : Nat, j < 4 →
      pinnedRead σ (WeakInterp.accAddr pc j) ∧ fetchPinned σ (WeakInterp.accAddr pc j)) →
    P σ →
    wstepOkRacy (some cid) ra rn rak Φ (raccDisj ra rn) False true (riscvStep tick) σ ∧
    (∀ χ σ' χ', wexec (some cid) (riscvStep tick) χ σ = some ((), σ', χ') → Q σ σ')

section rule
variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [WeakGS GF]

/-- THE RACY-LOAD RULE.  The sync premise (φ-upgrade, deliverable A: THE RACY WINDOW IS SYNC) is
persistent and not consumed; it is what the violation-freedom preservation reads at this rule. -/
theorem wpWracyLoad (gen : Nat) (cpu : CPU) (pc : BitVec 64) (ra : PAddr) (rn : Nat)
    (rak : AkInfo) (Φ : (Nat → BitVec 8) → Prop) (P : Wmstate → Prop)
    (Q : Wmstate → Wmstate → Prop) :
    gen = 0 → accWf pc 4 → accWf ra rn → wracyCert cpu.val pc ra rn rak Φ P Q →
    (syncWin (GF := GF) ra rn ∗
      (∀ σ : Wmstate, wmstateInterp (hlc := hlc) (GF := GF) cpu σ ={⊤,∅}=∗
        ⌜σ.wmRegs .PC = pc⌝ ∗
        ⌜∀ j : Nat, j < 4 →
          pinnedRead σ (WeakInterp.accAddr pc j) ∧ fetchPinned σ (WeakInterp.accAddr pc j)⌝ ∗
        ⌜P σ⌝ ∗
        ⌜wadmFilter σ rak ra rn Φ⌝ ∗
        ⌜(bmRead (wflatMem σ.wmImg σ.wmLog) ra rn).isSome = true⌝ ∗
        (∃ t0 : ExecSt, ⌜exec (riscvStep false) (wflatSt σ) = some ((), t0)⌝) ∗
        ▷ (∀ (tick : Bool) (σ' : Wmstate) (w : BitVec (8 * rn)),
            ⌜wadm σ rak ra rn w⌝ -∗
            ⌜exec (riscvStep tick) (wpatchSt σ ra rn w) = some ((), wpatchSt σ' ra rn w)⌝ -∗
            ⌜wstepPostRacy σ σ'⌝ -∗
            ⌜Q σ σ'⌝ ={∅,⊤}=∗
              wmstateInterp (hlc := hlc) (GF := GF) cpu σ' ∗
              wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu)))) ⊢
    wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu) := by
  intro hgen haccpc hracc hcert
  iintro ⟨-, H⟩
  iapply wpWrunStep gen cpu hgen
  iintro %σ Hσ
  icases wmstateInterpFacts cpu σ $$ Hσ with ⟨%hfacts, Hσ⟩
  obtain ⟨hbnd, hwf⟩ := hfacts
  imod H $$ %σ Hσ with ⟨%hpc, %htext, %hP, %hΦ, %hrd, ⟨%t0, %hex0⟩, Hk⟩
  have hc : ∀ tick : Bool,
      wstepOkRacy (some cpu.val) ra rn rak Φ (raccDisj ra rn) False true (riscvStep tick) σ ∧
      (∀ χ σ' χ', wexec (some cpu.val) (riscvStep tick) χ σ = some ((), σ', χ') → Q σ σ') :=
    fun tick => hcert σ tick hpc haccpc htext hP
  -- the window's coherent word -- the pinned value, at which the reducibility witness is taken
  have hcoh : (wreadBytes σ rak ra rn (cohTs σ ra rn)).isSome = true := by
    rw [wreadBytesReadBytes σ rak ra rn hwf hracc]; exact hrd
  imodintro
  isplitr
  · ipureintro
    obtain ⟨χ, σ0, χ', hw, _⟩ := wexecOfExecRacy (some cpu.val) ra rn rak Φ (raccDisj ra rn) False
      (riscvStep false) hracc true σ (hc false).1 hwf (fun _ => hΦ) () t0 hex0
    exact ⟨χ, σ0, χ', hw⟩
  inext
  iintro %tick %σ' %hrun
  obtain ⟨w, hadm, hex, hwf'⟩ := execOfWrunRacy (some cpu.val) ra rn rak Φ (raccDisj ra rn)
    (riscvStep tick) hracc (fun _ _ h => h) σ hΦ hwf hcoh (hc tick).1 () σ' hrun
  obtain ⟨χ, χ', hwex⟩ := wrunWexecRacy (some cpu.val) ra rn rak Φ (raccDisj ra rn) False
    (riscvStep tick) true σ (hc tick).1 (fun _ => hΦ) () σ' hrun
  have hpost : wstepPostRacy σ σ' :=
    ⟨wrunImg _ _ _ _ _ hrun, wrunLogApp _ _ _ _ _ hrun, wrunWsLe _ _ _ _ _ hrun, hwf',
      wrunWsBounded _ _ _ _ _ hrun hbnd⟩
  iapply Hk $$ %tick %σ' %w
  · ipureintro; exact hadm
  · ipureintro; exact hex
  · ipureintro; exact hpost
  · ipureintro; exact (hc tick).2 χ σ' χ' hwex

/-- THE SAME RULE WITH THE VIEW GAIN ATTACHED (§4b): two premises more, both about the READER
(the access is not an i-cache read; the hart has not stored to the window), and one conclusion
more (the gain, or the step never looked at the window -- which a leaf kills with
`wreadsWin`). -/
theorem wpWracyLoadGain (gen : Nat) (cpu : CPU) (pc : BitVec 64) (ra : PAddr) (rn : Nat)
    (rak : AkInfo) (Φ : (Nat → BitVec 8) → Prop) (P : Wmstate → Prop)
    (Q : Wmstate → Wmstate → Prop) :
    gen = 0 → accWf pc 4 → accWf ra rn → rak.akIfetch = false →
    wracyCert cpu.val pc ra rn rak Φ P Q →
    (syncWin (GF := GF) ra rn ∗
      (∀ σ : Wmstate, wmstateInterp (hlc := hlc) (GF := GF) cpu σ ={⊤,∅}=∗
        ⌜σ.wmRegs .PC = pc⌝ ∗
        ⌜∀ j : Nat, j < 4 →
          pinnedRead σ (WeakInterp.accAddr pc j) ∧ fetchPinned σ (WeakInterp.accAddr pc j)⌝ ∗
        ⌜P σ⌝ ∗
        ⌜wunwritten σ.wmWs ra rn⌝ ∗
        ⌜wadmFilter σ rak ra rn Φ⌝ ∗
        ⌜(bmRead (wflatMem σ.wmImg σ.wmLog) ra rn).isSome = true⌝ ∗
        (∃ t0 : ExecSt, ⌜exec (riscvStep false) (wflatSt σ) = some ((), t0)⌝) ∗
        ▷ (∀ (tick : Bool) (σ' : Wmstate) (w : BitVec (8 * rn)),
            ⌜wadm σ rak ra rn w⌝ -∗
            ⌜exec (riscvStep tick) (wpatchSt σ ra rn w) = some ((), wpatchSt σ' ra rn w)⌝ -∗
            ⌜wstepPostRacy σ σ'⌝ -∗
            ⌜Q σ σ'⌝ -∗
            ⌜wgain σ σ' rak ra rn w ∨
              ∀ u : BitVec (8 * rn),
                exec (riscvStep tick) (wpatchSt σ ra rn u) = some ((), wpatchSt σ' ra rn u)⌝
            ={∅,⊤}=∗
              wmstateInterp (hlc := hlc) (GF := GF) cpu σ' ∗
              wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu)))) ⊢
    wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu) := by
  intro hgen haccpc hracc hakc hcert
  iintro ⟨-, H⟩
  iapply wpWrunStep gen cpu hgen
  iintro %σ Hσ
  icases wmstateInterpFacts cpu σ $$ Hσ with ⟨%hfacts, Hσ⟩
  obtain ⟨hbnd, hwf⟩ := hfacts
  imod H $$ %σ Hσ with ⟨%hpc, %htext, %hP, %hun, %hΦ, %hrd, ⟨%t0, %hex0⟩, Hk⟩
  have hc : ∀ tick : Bool,
      wstepOkRacy (some cpu.val) ra rn rak Φ (raccDisj ra rn) False true (riscvStep tick) σ ∧
      (∀ χ σ' χ', wexec (some cpu.val) (riscvStep tick) χ σ = some ((), σ', χ') → Q σ σ') :=
    fun tick => hcert σ tick hpc haccpc htext hP
  have hcoh : (wreadBytes σ rak ra rn (cohTs σ ra rn)).isSome = true := by
    rw [wreadBytesReadBytes σ rak ra rn hwf hracc]; exact hrd
  imodintro
  isplitr
  · ipureintro
    obtain ⟨χ, σ0, χ', hw, _⟩ := wexecOfExecRacy (some cpu.val) ra rn rak Φ (raccDisj ra rn) False
      (riscvStep false) hracc true σ (hc false).1 hwf (fun _ => hΦ) () t0 hex0
    exact ⟨χ, σ0, χ', hw⟩
  inext
  iintro %tick %σ' %hrun
  obtain ⟨w, hadm, hex, hwf', hg⟩ := execOfWrunGain (some cpu.val) ra rn rak Φ (raccDisj ra rn)
    (riscvStep tick) hracc (fun _ _ h => h) hakc σ hΦ hwf hcoh hun (hc tick).1 () σ' hrun
  obtain ⟨χ, χ', hwex⟩ := wrunWexecRacy (some cpu.val) ra rn rak Φ (raccDisj ra rn) False
    (riscvStep tick) true σ (hc tick).1 (fun _ => hΦ) () σ' hrun
  have hpost : wstepPostRacy σ σ' :=
    ⟨wrunImg _ _ _ _ _ hrun, wrunLogApp _ _ _ _ _ hrun, wrunWsLe _ _ _ _ _ hrun, hwf',
      wrunWsBounded _ _ _ _ _ hrun hbnd⟩
  iapply Hk $$ %tick %σ' %w
  · ipureintro; exact hadm
  · ipureintro; exact hex
  · ipureintro; exact hpost
  · ipureintro; exact (hc tick).2 χ σ' χ' hwex
  · ipureintro; exact hg

end rule

/-- THE LEAF-SIDE REFUTATION of the patch-independence arm: "this step READS the window" -- an
ordinary SC fact about the instruction. -/
def wreadsWin (ra : PAddr) (rn : Nat) (tick : Bool) (σ : Wmstate) : Prop :=
  ¬ ∃ σ' : Wmstate, ∀ u : BitVec (8 * rn),
      exec (riscvStep tick) (wpatchSt σ ra rn u) = some ((), wpatchSt σ' ra rn u)

/-! ## 7. The `lw`-shaped racy leaf: collapsing the ∀ into a DISJUNCTION

For a ONE-SHOT flag every timestamp that holds a non-clear byte is the setter's
(`WeakStarted.wstartedOneshot`), and the setter's word agrees with the cleared word everywhere
else.  So the racy word is one of TWO. -/

/-- Every value any timestamp holds for a byte of the window is the cleared one or the
setter's. -/
def wtwoValued (s : Wmstate) (ra : PAddr) (rn : Nat) (v0 v : BitVec (8 * rn)) : Prop :=
  ∀ j : Nat, j < rn →
    ∀ (t : Nat) (b : BitVec 8),
      logByte (wimg s) s.wmLog t (WeakInterp.accAddr ra j) = some b →
      b = nthByte v0 j ∨ b = nthByte v j

theorem wadmTwoValued (s : Wmstate) (rak : AkInfo) (ra : PAddr) (rn : Nat)
    (v0 v w : BitVec (8 * rn)) (i : Nat) :
    i < rn →
    (∀ j : Nat, j < rn → j ≠ i → nthByte v j = nthByte v0 j) →
    wtwoValued s ra rn v0 v →
    wadm s rak ra rn w →
    w = v0 ∨ w = v := by
  intro hi hagree htwo hadm
  by_cases hwi : nthByte w i = nthByte v0 i
  · left
    apply bvEqOfBytes
    intro j hj
    by_cases hji : j = i
    · subst hji; exact hwi
    · obtain ⟨t, ht, _⟩ := hadm j hj
      rcases htwo j hj t (nthByte w j) ht with hb | hb
      · exact hb
      · rw [hb]; exact hagree j hj hji
  · right
    apply bvEqOfBytes
    intro j hj
    by_cases hji : j = i
    · subst hji
      obtain ⟨t, ht, _⟩ := hadm j hi
      rcases htwo j hi t (nthByte w j) ht with hb | hb
      · exact absurd hb hwi
      · exact hb
    · obtain ⟨t, ht, _⟩ := hadm j hj
      rcases htwo j hj t (nthByte w j) ht with hb | hb
      · rw [hb]; exact (hagree j hj hji).symm
      · exact hb

theorem nthByteLockZero (j : Nat) :
    j < 4 → nthByte (n := 4) lockZero j = nthByte (n := 4) lockZero 0 := by
  intro hj
  match j, hj with
  | 0, _ => rfl
  | 1, _ => decide
  | 2, _ => decide
  | 3, _ => decide

theorem nthByteLockOneHigh (j : Nat) :
    0 < j ∧ j < 4 → nthByte (n := 4) lockOne j = nthByte (n := 4) lockZero j := by
  intro hj
  match j, hj with
  | 1, _ => decide
  | 2, _ => decide
  | 3, _ => decide

/-- The `started` instance: the escrow's one-shot fact plus the escrow's own value at its
timestamp turn the rule's ∀-over-admissible-words into the two-way case split. -/
theorem wadmStartedLw4 (σ : Wmstate) (rak : AkInfo) (a : PAddr) (t : Nat) (w : BitVec 32) :
    (∀ j : Nat, j < 4 → wstartedOneshot (wimg σ) σ.wmLog (WeakInterp.accAddr a j) t) →
    (∀ j : Nat, j < 4 →
      logByte (wimg σ) σ.wmLog t (WeakInterp.accAddr a j) = some (nthByte (n := 4) lockOne j)) →
    wadm σ rak a 4 w →
    w = lockZero ∨ w = lockOne := by
  intro hone hval hadm
  apply wadmTwoValued σ rak a 4 lockZero lockOne w 0 (by omega)
  · intro j hj hne
    exact nthByteLockOneHigh j ⟨by omega, hj⟩
  · intro j hj t' b hb
    by_cases hb0 : b = nthByte (n := 4) lockZero 0
    · left
      rw [hb0]
      exact (nthByteLockZero j hj).symm
    · right
      have ht' := hone j hj t' b hb hb0
      subst ht'
      rw [hval j hj] at hb
      exact (Option.some.inj hb).symm
  · exact hadm

end Weak
