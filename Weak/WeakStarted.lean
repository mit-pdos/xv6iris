/-
Weak: **the `started` handoff, weak-memory form** (M3b item 4) -- xv6's one unlocked cross-hart
channel (`started`, set once by hart 0 after the init, spun on by the others), as a ONE-SHOT
ESCROW keyed on the flag word, plus the writer's set (`fence rw,w ; sw`) and the reader's
observation and delivery (`lw ; fence r,rw`).

Rocq: `iris/WeakStarted.v` @ xxvzwolszwmp.

The Rocq header, in substance (Rocq vocabulary).

`StartedInv.v` gives the channel the SC reading: a one-shot escrow
`started_body P := ∃ v, started ↦₄ v ∗ (⌜v = 0⌝ ∨ P)` with a PERSISTENT payload.  THE WEAK READING
KEEPS THAT SHAPE AND ADDS ONE NUMBER, the timestamp: the right disjunct becomes
`monPred_at P (view_scl T)`, the payload frozen where the writer's store put it.  The two
machine-level fences become the two halves of the transfer: the WRITER's store publishes
(`WeakInstr.wwp_release_deposit`, resting on `ws_bounded`); the READER's load raises `w_vrOld` to
the timestamp it read (`load_post_vrOld_nofwd`) and the pred-R fence turns that into an index
gain (`wwp_fence_scl`).  Without the fence the reader gets the flag's value and nothing else --
the MP litmus test.

A plain load may read a STALE message, so "I read a nonzero flag" does not by itself identify
WHICH message was read; it does once the escrow records that the flag is written once.  That
record cannot be stored as the whole-log `wstarted_oneshot`: (a) it is a whole-log fact, so it is
stored CLIPPED against a log snapshot (`wlog_lb`), and the current-log form is derived at each use
(`wstarted_lb_now`); (b) the exact-timestamp form is not stable under a second set, so the stored
form is a LOWER BOUND `T` on the non-clear writes, with the payload frozen at `view_scl T`; (c)
timestamp 0 is the era image, which no `iProp` names, so the image half travels as the pure side
condition `wstarted_img_clear`, handed out by the MINT.

**Deviations from Rocq.**

1. NAMES: the tree's camelCase (map below).  No name of this file is in
   `notes/weak-port-dupnames.json`.  Vocabulary as `Weak/WeakLock.lean` deviation 1 (`S (length l)`
   ↦ `l.length + 1`, `acc_addr` ↦ `WeakInterp.accAddr`, `nth_byte w j` ↦ `nthByte (n := 4) w j`,
   `DfracOwn 1` ↦ `DFrac.own 1`, `monPred_at P V` ↦ `P.monPred_at V`, `view_scl` ↦ `viewScl`,
   `Arch.pa` ↦ `PAddr`, `bv n` ↦ `BitVec n`, `l1 `prefix_of` l2` ↦ `l1 <+: l2`, `wimg σ` /
   `wm_img σ` ↦ `wimg σ` / `σ.wmImg`); `lock_zero`/`lock_one` are `WeakLock.lockZero`/`lockOne`.
2. STATEMENT SHAPES (WeakLock deviation 5): Rocq `A -∗ B -∗ C` is `A ⊢ B -∗ C`, `A -∗ B ==∗ C`
   is `A ⊢ B -∗ |==> C`, `A -∗ B ={E}=∗ C` is `A ⊢ B -∗ |={E}=> C`; Rocq `P ⊢ Q` stays.
3. `Context {!riscvGS Σ, !weakGS Σ}` is `{hlc : HasLC} [MachGS hlc GF] [WeakGS GF]`
   (WeakLock deviation 6); `wstartedInv` takes `(hlc := hlc)` explicitly at use sites, as
   `WeakLock.wisLock`.  `{!Persistent P}` is `[Persistent P]`.
4. `wmstate_interp_log_lb`'s `{CpuId}` context is the explicit `cpu : CPU` of Lean's
   `wmstateInterp` (WeakGhost).
5. `wlat4_latest_val` is proved through `WeakStore.wlat4ElOfWlat4` + `wlat4ElLatestVal` (Rocq:
   four `wlat_lookup`s) -- same statement.
6. Lean-only helpers: `WeakStarted.writesInOfLookup` (a message at index `i` writing the byte is
   a `writesIn` witness; inlined `writes_in_log_byte` reasoning in Rocq) and
   `WeakStarted.wlat4SyncDupWin` (keep the sync bundle while reading out its persistent window;
   Rocq's `iDestruct ... as "#Hsw"` on a non-consumed hypothesis).

**Rocq → Lean name map.**  `wstarted_oneshot` `wstartedOneshot`, `wstarted_oneshot_app`
`wstartedOneshotApp`, `wstarted_lb` `wstartedLb`, `wstarted_img_clear` `wstartedImgClear`,
`nth_byte_clear` `nthByteClear`, `prefix_either_lookup` `prefixEitherLookup`, `wstarted_lb_now`
`wstartedLbNow`, `wstarted_collapse` `wstartedCollapse`, `wstarted_clear_now`
`wstartedClearNow`, `wstarted_two_valued` `wstartedTwoValued`, `wstartedN` `wstartedN`,
`wlat4_latest_val` `wlat4LatestVal`, `wlat4_sync_latest_val` `wlat4SyncLatestVal`,
`wlog_lb_compare` `wlogLbCompare`, `wstarted_hist` `wstartedHist`, `wstarted_at` `wstartedAt`,
`wstarted_at_sync` `wstartedAtSync`, `wstarted_body` `wstartedBody`, `wstarted_inv`
`wstartedInv`, `wstarted_inv_persistent` `wstartedInv_persistent`, `wstarted_alloc`
`wstartedAlloc`, `wmstate_interp_log_lb` `wmstateInterpLogLb`, `wstarted_set` `wstartedSet`,
`wstarted_read_ts` `wstartedReadTs`, `wstarted_read_vrOld` `wstartedReadVrOld`,
`wstarted_deliver_gen` `wstartedDeliverGen`, `wstarted_deliver` `wstartedDeliver`,
`wstarted_deliver_r` `wstartedDeliverR`, `wstarted_observe` `wstartedObserve`,
`wstarted_reader` `wstartedReader`.  Lean-only: `WeakStarted.writesInOfLookup`,
`WeakStarted.wlat4SyncDupWin` (deviation 6).

**Not ported:** nothing -- every Rocq definition and lemma has a Lean twin.
-/
import Weak.WeakLock
import MachCSL.MonPredExtra

namespace Weak

open Iris Iris.BI Iris.BI.MonPred Iris.ProofMode Iris.Std
open MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D

/-! ## 1. The one-shot fact -/

/-- THE ONE-SHOT FACT.  Every write of a NON-CLEAR value to byte `a` is the escrow's own message
at timestamp `t` (the era image holds the flag cleared -- it is in `.bss`). -/
def wstartedOneshot (img : Image) (log : List Wmsg) (a : Int) (t : Nat) : Prop :=
  ∀ (t' : Nat) (b : BitVec 8),
    logByte img log t' a = some b → b ≠ nthByte (n := 4) lockZero 0 → t' = t

/-- It survives every append that does not write the byte. -/
theorem wstartedOneshotApp (img : Image) (log ms : List Wmsg) (a : Int) (t : Nat) :
    wstartedOneshot img log a t →
    (∀ m, m ∈ ms → msgByte m a = none) →
    wstartedOneshot img (log ++ ms) a t := by
  intro hone hno t' b hb hne
  apply hone t' b _ hne
  cases t' with
  | zero => exact hb
  | succ i =>
    rw [logByteS] at hb ⊢
    cases hl : (log ++ ms)[i]? with
    | none => rw [hl] at hb; simp at hb
    | some m =>
      rw [hl] at hb
      change msgByte m a = some b at hb
      rcases lookup_app_Some.mp hl with hl2 | ⟨_, hms⟩
      · rw [hl2]; exact hb
      · exfalso
        rw [hno m (elem_of_list_lookup_2 hms)] at hb
        simp at hb

/-! ## 1b. THE STORABLE FORM: a lower bound on the non-clear writes -/

/-- The LOG half: every message of `log` that writes a non-clear byte anywhere in the flag word
does so at a timestamp at or above `T`, and writes the SETTER's byte there. -/
def wstartedLb (log : List Wmsg) (a : PAddr) (T : Nat) : Prop :=
  ∀ (j i : Nat) (m : Wmsg) (b : BitVec 8),
    j < 4 →
    log[i]? = some m →
    msgByte m (WeakInterp.accAddr a j) = some b →
    b ≠ nthByte (n := 4) lockZero 0 →
    T ≤ i + 1 ∧ b = nthByte (n := 4) lockOne j

/-- The IMAGE half: the era image holds the flag cleared. -/
def wstartedImgClear (σ : Wmstate) (a : PAddr) : Prop :=
  ∀ j : Nat, j < 4 →
    wimg σ (WeakInterp.accAddr a j) = some (nthByte (n := 4) lockZero j)

/-- Every byte of the cleared word is THE clear byte. -/
theorem nthByteClear (j : Nat) :
    j < 4 → nthByte (n := 4) lockZero j = nthByte (n := 4) lockZero 0 := by
  intro hj
  rcases j with _ | _ | _ | _ | j
  · rfl
  · decide
  · decide
  · decide
  · omega

/-- Two log lower bounds are comparable, so a snapshot's entries are read off the current log. -/
theorem prefixEitherLookup {A : Type _} (l1 l2 : List A) (i : Nat) (x : A) :
    (l1 <+: l2 ∨ l2 <+: l1) →
    l2[i]? = some x → i < l1.length → l1[i]? = some x := by
  rintro (⟨k, rfl⟩ | ⟨k, rfl⟩) hx hi
  · rwa [lookup_app_l hi] at hx
  · rw [lookup_app_l (lookup_lt_Some hx)]
    exact hx

/-- A message at index `i` writing byte `a` is a `writesIn` witness (Lean-only, deviation 6). -/
theorem WeakStarted.writesInOfLookup (log : List Wmsg) (a : Int) (lo i : Nat) (m : Wmsg)
    (b : BitVec 8) :
    lo < i + 1 → log[i]? = some m → msgByte m a = some b → writesIn log a lo log.length := by
  intro hlo hm hb
  refine ⟨i + 1, hlo, lookup_lt_Some hm, m, ?_, ?_⟩
  · rw [Nat.add_sub_cancel]; exact hm
  · rw [hb]; rfl

/-- THE EXTENSION, pure half: the snapshot's bound, the escrow's element and the log
comparison give the bound over the CURRENT log. -/
theorem wstartedLbNow (img : Image) (log log0 : List Wmsg) (a : PAddr) (T t : Nat)
    (v : BitVec 32) :
    t ≤ log0.length + 1 →
    wstartedLb log0 a T →
    (log0 <+: log ∨ log <+: log0) →
    (∀ k : Nat, k < 4 →
      latestVal img log (WeakInterp.accAddr a k) t (nthByte (n := 4) v k)) →
    ((v = lockZero ∧ log0.length < T) ∨ (v = lockOne ∧ T ≤ t)) →
    wstartedLb log a T := by
  intro hcov hlb hcmp hlv hdisj j i m b hj hm hbb hne
  have hbyte : logByte img log (i + 1) (WeakInterp.accAddr a j) = some b := by
    rw [logByteS, hm]; exact hbb
  -- nothing above the element's timestamp writes the byte
  have hle : i + 1 ≤ t := by
    by_cases h : i + 1 ≤ t
    · exact h
    · exfalso
      exact (hlv j hj).2
        (WeakStarted.writesInOfLookup log _ t i m b (by omega) hm hbb)
  by_cases hin : i < log0.length
  · exact hlb j i m b hj (prefixEitherLookup log0 log i m hcmp hm hin) hbb hne
  · -- `i` is the snapshot's own top: the write is the escrow's element
    have hit : i + 1 = t := by omega
    have hvj := (hlv j hj).1
    rw [← hit, hbyte] at hvj
    obtain rfl := Option.some.inj hvj
    rcases hdisj with ⟨rfl, _⟩ | ⟨rfl, hT⟩
    · exact absurd (nthByteClear j hj) hne
    · exact ⟨by omega, rfl⟩

/-- ... and its image-aware form, which is what the READER consumes. -/
theorem wstartedCollapse (img : Image) (log log0 : List Wmsg) (a : PAddr) (T t : Nat)
    (v : BitVec 32) (j t' : Nat) (b : BitVec 8) :
    j < 4 →
    (∀ k : Nat, k < 4 →
      img (WeakInterp.accAddr a k) = some (nthByte (n := 4) lockZero k)) →
    t ≤ log0.length + 1 →
    wstartedLb log0 a T →
    (log0 <+: log ∨ log <+: log0) →
    (∀ k : Nat, k < 4 →
      latestVal img log (WeakInterp.accAddr a k) t (nthByte (n := 4) v k)) →
    ((v = lockZero ∧ log0.length < T) ∨ (v = lockOne ∧ T ≤ t)) →
    logByte img log t' (WeakInterp.accAddr a j) = some b →
    b ≠ nthByte (n := 4) lockZero 0 →
    T ≤ t' ∧ b = nthByte (n := 4) lockOne j := by
  intro hj himg hcov hlb hcmp hlv hdisj hbyte hne
  cases t' with
  | zero =>
    exfalso
    rw [logByte0, himg j hj] at hbyte
    obtain rfl := Option.some.inj hbyte
    exact hne (nthByteClear j hj)
  | succ i =>
    rw [logByteS] at hbyte
    cases hm : log[i]? with
    | none => rw [hm] at hbyte; simp at hbyte
    | some m =>
      rw [hm] at hbyte
      exact wstartedLbNow img log log0 a T t v hcov hlb hcmp hlv hdisj j i m b hj hm hbyte hne

/-- IN THE CLEAR STATE THERE IS NO NON-CLEAR WRITE AT ALL -- image included. -/
theorem wstartedClearNow (img : Image) (log log0 : List Wmsg) (a : PAddr) (T t : Nat)
    (j t' : Nat) (b : BitVec 8) :
    j < 4 →
    (∀ k : Nat, k < 4 →
      img (WeakInterp.accAddr a k) = some (nthByte (n := 4) lockZero k)) →
    t ≤ log0.length + 1 →
    log0.length < T →
    wstartedLb log0 a T →
    (log0 <+: log ∨ log <+: log0) →
    (∀ k : Nat, k < 4 →
      latestVal img log (WeakInterp.accAddr a k) t (nthByte (n := 4) lockZero k)) →
    logByte img log t' (WeakInterp.accAddr a j) = some b →
    b ≠ nthByte (n := 4) lockZero 0 →
    False := by
  intro hj himg hcov hT hlb hcmp hlv hbyte hne
  cases t' with
  | zero =>
    rw [logByte0, himg j hj] at hbyte
    obtain rfl := Option.some.inj hbyte
    exact hne (nthByteClear j hj)
  | succ i =>
    rw [logByteS] at hbyte
    cases hm : log[i]? with
    | none => rw [hm] at hbyte; simp at hbyte
    | some m =>
      rw [hm] at hbyte
      change msgByte m (WeakInterp.accAddr a j) = some b at hbyte
      have hle : i + 1 ≤ t := by
        by_cases h : i + 1 ≤ t
        · exact h
        · exfalso
          exact (hlv j hj).2
            (WeakStarted.writesInOfLookup log _ t i m b (by omega) hm hbyte)
      by_cases hin : i < log0.length
      · have := (hlb j i m b hj (prefixEitherLookup log0 log i m hcmp hm hin) hbyte hne).1
        omega
      · have hteq : i + 1 = t := by omega
        have hb2 : logByte img log (i + 1) (WeakInterp.accAddr a j) = some b := by
          rw [logByteS, hm]; exact hbyte
        have hvj := (hlv j hj).1
        rw [← hteq, hb2] at hvj
        obtain rfl := Option.some.inj hvj
        exact hne (nthByteClear j hj)

/-- THE ESCROW STATE IS ONE OF TWO WORDS -- the premise `WeakRacy`'s `wadm_two_valued` takes. -/
theorem wstartedTwoValued (img : Image) (log : List Wmsg) (a : PAddr) (T : Nat) (j t' : Nat)
    (b : BitVec 8) :
    j < 4 →
    (∀ k : Nat, k < 4 →
      img (WeakInterp.accAddr a k) = some (nthByte (n := 4) lockZero k)) →
    wstartedLb log a T →
    logByte img log t' (WeakInterp.accAddr a j) = some b →
    b = nthByte (n := 4) lockZero j ∨ b = nthByte (n := 4) lockOne j := by
  intro hj himg hlb hbyte
  by_cases hb0 : b = nthByte (n := 4) lockZero 0
  · left
    rw [hb0]
    exact (nthByteClear j hj).symm
  · right
    cases t' with
    | zero =>
      exfalso
      rw [logByte0, himg j hj] at hbyte
      obtain rfl := Option.some.inj hbyte
      exact hb0 (nthByteClear j hj)
    | succ i =>
      rw [logByteS] at hbyte
      cases hm : log[i]? with
      | none => rw [hm] at hbyte; simp at hbyte
      | some m =>
        rw [hm] at hbyte
        exact (hlb j i m b hj hm hbyte hb0).2

/-! ## 2. The escrow -/

section weakStarted

variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [WeakGS GF]

def wstartedN : Namespace := ndot nroot "weakstarted"

/-- The escrow's LATEST-WRITE reading of its own elements. -/
theorem wlat4LatestVal (σ : Wmstate) (a : PAddr) (dq : DFrac) (t : Nat) (w : BitVec 32) :
    wlatInterp (GF := GF) σ.wmImg σ.wmLog ⊢
      wlat4 (GF := GF) a dq t w -∗
        ⌜∀ j : Nat, j < 4 →
          latestVal (wimg σ) σ.wmLog (WeakInterp.accAddr a j) t (nthByte (n := 4) w j)⌝ := by
  iintro Hi Hw
  ihave Hw := wlat4ElOfWlat4 a dq t w $$ Hw
  ihave %h := wlat4ElLatestVal σ.wmImg σ.wmLog a dq t w $$ Hi Hw
  ipureintro
  exact h

/-- ... and its `wlat4Sync` instance. -/
theorem wlat4SyncLatestVal (σ : Wmstate) (a : PAddr) (t : Nat) (w : BitVec 32) :
    wlatInterp (GF := GF) σ.wmImg σ.wmLog ⊢
      wlat4Sync (GF := GF) a t w -∗
        ⌜∀ j : Nat, j < 4 →
          latestVal (wimg σ) σ.wmLog (WeakInterp.accAddr a j) t (nthByte (n := 4) w j)⌝ := by
  unfold wlat4Sync
  iintro Hi ⟨He, -⟩
  ihave %h := wlat4ElLatestVal σ.wmImg σ.wmLog a (DFrac.own 1) t w $$ Hi He
  ipureintro
  exact h

/-- Two log lower bounds are comparable (mono-list). -/
theorem wlogLbCompare (l1 l2 : List Wmsg) :
    wlogLb (GF := GF) l1 ⊢ wlogLb l2 -∗ ⌜l1 <+: l2 ∨ l2 <+: l1⌝ := by
  unfold wlogLb
  iintro H1 H2
  iapply MonoList.lb_own_valid _ l1 l2 $$ H1 H2

/-- Keep the sync bundle while reading out its persistent window (Lean-only, deviation 6). -/
theorem WeakStarted.wlat4SyncDupWin (a : PAddr) (t : Nat) (w : BitVec 32) :
    wlat4Sync (GF := GF) a t w ⊢ wlat4Sync a t w ∗ syncWin a 4 := by
  unfold wlat4Sync
  iintro ⟨He, #H⟩
  isplitl [He]
  · isplitl [He]
    · iexact He
    · iexact H
  · iexact H

/-- THE ESCROW's history half, at a known timestamp/value pair: a log snapshot, the clipped
lower bound over it, and the deposit timestamp `T` the bound is keyed on.  COVERAGE is
`t ≤ log0.length + 1`, one more than `WeakKpt`'s, which lets `wstartedSet` refresh the snapshot to
the PRE-state's log. -/
def wstartedHist (a : PAddr) (P : VProp GF) (t : Nat) (v : BitVec 32) : IProp GF :=
  iprop(∃ (T : Nat) (log0 : List Wmsg),
    wlogLb (GF := GF) log0 ∗
    ⌜t ≤ log0.length + 1⌝ ∗
    ⌜wstartedLb log0 a T⌝ ∗
    ((⌜v = lockZero⌝ ∗ ⌜log0.length < T⌝) ∨
      (⌜v = lockOne⌝ ∗ ⌜T ≤ t⌝ ∗ P.monPred_at (viewScl T))))

def wstartedAt (a : PAddr) (P : VProp GF) (t : Nat) (v : BitVec 32) : IProp GF :=
  iprop(wlat4Sync (GF := GF) a t v ∗ wstartedHist a P t v)

/-- The flag word is a SYNC window, and the witness is persistent. -/
theorem wstartedAtSync (a : PAddr) (P : VProp GF) (t : Nat) (v : BitVec 32) :
    wstartedAt a P t v ⊢ syncWin a 4 := by
  unfold wstartedAt
  iintro ⟨Hw, -⟩
  iapply wlat4SyncWin a t v $$ Hw

/-- The invariant body: an `IProp`, hence objective, hence admissible in an `inv`. -/
def wstartedBody (a : PAddr) (P : VProp GF) : IProp GF :=
  iprop(∃ (t : Nat) (v : BitVec 32), wstartedAt a P t v)

def wstartedInv (a : PAddr) (P : VProp GF) : IProp GF :=
  inv wstartedN (wstartedBody (GF := GF) a P)

instance wstartedInv_persistent (a : PAddr) (P : VProp GF) :
    Persistent (wstartedInv (hlc := hlc) (GF := GF) a P) := by
  unfold wstartedInv; infer_instance

/-- THE MINT, from the flag word's ERA-IMAGE elements (timestamp 0, the cleared word). -/
theorem wstartedAlloc (a : PAddr) (P : VProp GF) (σ : Wmstate) (E : CoPset) :
    wlogLb (GF := GF) σ.wmLog ⊢
      wlatInterp (GF := GF) σ.wmImg σ.wmLog -∗
        wlat4 (GF := GF) a (DFrac.own 1) 0 lockZero -∗
          |={E}=> (wlatInterp (GF := GF) σ.wmImg σ.wmLog ∗
            ⌜wstartedImgClear σ a⌝ ∗ syncWin (GF := GF) a 4 ∗
            wstartedInv (hlc := hlc) (GF := GF) a P) := by
  iintro #Hlb Hi Hw
  icases keepPure (wlat4LatestVal σ a (DFrac.own 1) 0 lockZero) $$ Hi Hw with ⟨%hlv, Hi, Hw⟩
  have himg : wstartedImgClear σ a := fun j hj => (hlv j hj).1
  -- nothing in the log writes the flag: the element is the era image's
  have hlb0 : wstartedLb σ.wmLog a (σ.wmLog.length + 1) := by
    intro j i m b hj hm hbb _
    exfalso
    exact (hlv j hj).2 (WeakStarted.writesInOfLookup σ.wmLog _ 0 i m b (by omega) hm hbb)
  -- THE S MINT: the same fact IS `wcdsSync` at each of the four bytes
  have hsy : ∀ j : Nat, j < 4 → wcdsSync σ.wmLog (WeakInterp.accAddr a j) := by
    intro j hj p m ⟨hp, hs, _⟩
    apply (hlv j hj).2
    refine ⟨p + 1, by omega, lookup_lt_Some hp, m, ?_, hs⟩
    rw [Nat.add_sub_cancel]; exact hp
  imod wlat4SyncMint σ.wmImg σ.wmLog a 0 lockZero hsy $$ Hi Hw with ⟨Hi, Hw⟩
  icases WeakStarted.wlat4SyncDupWin a 0 lockZero $$ Hw with ⟨Hw, #Hsw⟩
  imod inv_alloc wstartedN E (wstartedBody (GF := GF) a P) $$ [Hw] with #Hinv
  · iapply later_intro
    unfold wstartedBody wstartedAt wstartedHist
    iexists 0, lockZero
    isplitl [Hw]
    · iexact Hw
    iexists σ.wmLog.length + 1, σ.wmLog
    isplitr
    · iexact Hlb
    isplitr
    · ipureintro; omega
    isplitr
    · ipureintro; exact hlb0
    ileft
    isplitr
    · ipureintro; rfl
    · ipureintro; omega
  imodintro
  isplitl [Hi]
  · iexact Hi
  isplitr
  · ipureintro; exact himg
  isplitr
  · iexact Hsw
  unfold wstartedInv
  iexact Hinv

/-- The log lower bound every consumer of the escrow needs, off the state interpretation. -/
theorem wmstateInterpLogLb (cpu : CPU) (σ : Wmstate) :
    wmstateInterp (hlc := hlc) (GF := GF) cpu σ ⊢
      wmstateInterp (hlc := hlc) (GF := GF) cpu σ ∗ wlogLb σ.wmLog := by
  unfold wmstateInterp
  iintro ⟨%hb, %hn, %hw, Hr, Hd, Hl, Hlat, Hws⟩
  icases wlogSnapshot σ.wmLog $$ Hl with ⟨Hl, #Hlb⟩
  isplitl [Hr Hd Hl Hlat Hws]
  · isplitr
    · ipureintro; exact hb
    isplitr
    · ipureintro; exact hn
    isplitr
    · ipureintro; exact hw
    iframe Hr Hd Hl Hlat Hws
  · iexact Hlb

/-! ### The WRITER: `fence rw,w` ; `sw a5,0(a4)` with a5 = 1

Structurally identical to `WeakLock.wreleaseCore` -- it IS a release.  THE ONE NEW PREMISE is
the PRE-state's log lower bound, which refreshes the escrow's snapshot.  THE SECOND SET IS
PROVED, NOT RATIONED: from the CLEAR state the deposit is the caller's; from an ALREADY-SET state
the old deposit (at a lower `T`, hence stronger) is KEPT. -/

theorem wstartedSet (a : PAddr) (P : VProp GF) (tid : Option Nat) (σ σ' : Wmstate) :
    wQStore tid a lockOne σ σ' →
    -- φ-upgrade §1: the `fence rw,w` makes the store release-class, keeping the bundle CLEAN.
    σ.wmWs.wRelp = true →
    wsBounded σ.wmWs σ.wmLog.length →
    wlogLb (GF := GF) σ.wmLog ⊢
      wlatInterp (GF := GF) σ.wmImg σ.wmLog -∗
        wstartedBody a P -∗
          vwpHold P σ.wmWs -∗
            |==> (wlatInterp (GF := GF) σ'.wmImg σ'.wmLog ∗
              wstartedAt a P (σ.wmLog.length + 1) lockOne) := by
  intro heff hrelp hbnd
  obtain ⟨himg, ⟨kc, hlog, hnp⟩, -, -⟩ := heff
  have hnp := hnp hrelp
  iintro #Hlbσ Hi Hbody HP
  unfold wstartedBody wstartedAt wstartedHist
  icases Hbody with ⟨%t, %v, Hw, %T, %log0, #Hlb0, %hcov, %hlbf, Hdisj⟩
  ihave %hcmp := wlogLbCompare log0 σ.wmLog $$ Hlb0 Hlbσ
  icases keepPure (wlat4SyncLatestVal σ a t v) $$ Hi Hw with ⟨%hlv, Hi, Hw⟩
  -- the element is a write of the log, so the escrow's timestamp is one the fresh snapshot covers
  have htlen : t ≤ σ.wmLog.length ∨ t = 0 := by
    cases t with
    | zero => exact Or.inr rfl
    | succ t =>
      left
      apply logByteBounded (wimg σ) σ.wmLog (t + 1) (WeakInterp.accAddr a 0)
      rw [(hlv 0 (by omega)).1]
      rfl
  ihave HPnew := wwpReleaseDeposit P σ hbnd $$ HP
  icases Hdisj with (⟨%hv, %hT⟩ | ⟨%hv, %hT, HP0⟩)
  · -- CLEAR: nothing non-clear was ever written, so the deposit is ours
    subst hv
    have hnow := wstartedLbNow (wimg σ) σ.wmLog log0 a T t lockZero hcov hlbf hcmp hlv
      (Or.inl ⟨rfl, hT⟩)
    imod wlat4SyncStoreGen tid kc σ σ' a t lockZero lockOne hnp himg hlog $$ Hi Hw with ⟨Hi, Hw⟩
    imodintro
    isplitl [Hi]
    · iexact Hi
    isplitl [Hw]
    · iexact Hw
    iexists σ.wmLog.length + 1, σ.wmLog
    isplitr
    · iexact Hlbσ
    isplitr
    · ipureintro; omega
    isplitr
    · ipureintro
      intro j i m b hj hm hbb hne
      exfalso
      have hTle := (hnow j i m b hj hm hbb hne).1
      -- the only candidate is the escrow's own message, and it is clear
      have hit : i + 1 ≤ t := by
        by_cases h : i + 1 ≤ t
        · exact h
        · exfalso
          exact (hlv j hj).2
            (WeakStarted.writesInOfLookup σ.wmLog _ t i m b (by omega) hm hbb)
      have hteq : i + 1 = t := by omega
      have hbyte : logByte (wimg σ) σ.wmLog (i + 1) (WeakInterp.accAddr a j) = some b := by
        rw [logByteS, hm]; exact hbb
      have hvj := (hlv j hj).1
      rw [← hteq, hbyte] at hvj
      obtain rfl := Option.some.inj hvj
      exact hne (nthByteClear j hj)
    iright
    isplitr
    · ipureintro; rfl
    isplitr
    · ipureintro; omega
    iexact HPnew
  · -- ALREADY SET: keep the earlier deposit, and with it the earlier `T`
    subst hv
    have hnow := wstartedLbNow (wimg σ) σ.wmLog log0 a T t lockOne hcov hlbf hcmp hlv
      (Or.inr ⟨rfl, hT⟩)
    imod wlat4SyncStoreGen tid kc σ σ' a t lockOne lockOne hnp himg hlog $$ Hi Hw with ⟨Hi, Hw⟩
    imodintro
    isplitl [Hi]
    · iexact Hi
    isplitl [Hw]
    · iexact Hw
    iexists T, σ.wmLog
    isplitr
    · iexact Hlbσ
    isplitr
    · ipureintro; omega
    isplitr
    · ipureintro; exact hnow
    iright
    isplitr
    · ipureintro; rfl
    isplitr
    · ipureintro; omega
    iexact HP0

/-! ### The READER: `lw a5,0(a4)` ; `fence rw,rw` -/

/-- (a) WHICH MESSAGE THE LOAD READ: the one-shot fact pins it once the byte read non-clear. -/
theorem wstartedReadTs (σ : Wmstate) (ak : AkInfo) (a : Int) (t t' : Nat) (b : BitVec 8) :
    wstartedOneshot (wimg σ) σ.wmLog a t →
    wbyteOk σ ak a t' b →
    b ≠ nthByte (n := 4) lockZero 0 →
    t' = t :=
  fun hone hok hne => hone t' b hok.1 hne

/-- (b) THE LOAD'S OWN GAIN: a non-forwarded plain load of timestamp `t` leaves
`t ≤ wVrOld`. -/
theorem wstartedReadVrOld (ws : Wstate) (a : Int) (t : Nat) :
    ws.wFwd = ∅ → t ≤ (loadPost ws false a t).wVrOld :=
  fun hfwd => loadPostVrOldNofwd ws false a t hfwd

/-- (c) THE DELIVERY, at any pred-R fence. -/
theorem wstartedDeliverGen (P : VProp GF) (σ : Wmstate) (ws' : Wstate) (t : Nat)
    (b : barrier_kind) :
    acqPredR b →
    t ≤ σ.wmWs.wVrOld →
    wVFence b σ ws' →
    P.monPred_at (viewScl t) ⊢ vwpHold P ws' :=
  fun hb ht hQ => wwpFenceSclGen P σ ws' t b hb hQ ht

theorem wstartedDeliver (P : VProp GF) (σ : Wmstate) (ws' : Wstate) (t : Nat) :
    t ≤ σ.wmWs.wVrOld →
    wVFence .Barrier_RISCV_rw_rw σ ws' →
    P.monPred_at (viewScl t) ⊢ vwpHold P ws' :=
  wstartedDeliverGen P σ ws' t _ acqPredR_rw_rw

/-- The kernel's own kind: `fence r,rw` at `main+0x18`. -/
theorem wstartedDeliverR (P : VProp GF) (σ : Wmstate) (ws' : Wstate) (t : Nat) :
    t ≤ σ.wmWs.wVrOld →
    wVFence .Barrier_RISCV_r_rw σ ws' →
    P.monPred_at (viewScl t) ⊢ vwpHold P ws' :=
  wstartedDeliverGen P σ ws' t _ acqPredR_r_rw

/-- (d) THE OBSERVATION -- the one-shot collapse at the escrow.  An ADMISSIBLE read of one flag
byte that came back NON-CLEAR read a timestamp at or above the escrow's deposit, and the payload
is frozen at that deposit; the escrow is handed back UNCHANGED (the payload is persistent). -/
theorem wstartedObserve (a : PAddr) (P : VProp GF) [Persistent P] (σ : Wmstate) (ak : AkInfo)
    (j t : Nat) (b : BitVec 8) :
    wstartedImgClear σ a →
    j < 4 →
    wbyteOk σ ak (WeakInterp.accAddr a j) t b →
    b ≠ nthByte (n := 4) lockZero 0 →
    wlogLb (GF := GF) σ.wmLog ⊢
      wlatInterp (GF := GF) σ.wmImg σ.wmLog -∗
        wstartedBody a P -∗
          wlatInterp (GF := GF) σ.wmImg σ.wmLog ∗ wstartedBody a P ∗
            ⌜b = nthByte (n := 4) lockOne j⌝ ∗
            (∃ T : Nat, ⌜T ≤ t⌝ ∗ P.monPred_at (viewScl T)) := by
  intro himg hj hok hne
  have hb := hok.1
  iintro #Hlbσ Hi Hbody
  unfold wstartedBody wstartedAt wstartedHist
  icases Hbody with ⟨%te, %v, Hw, %T, %log0, #Hlb0, %hcov, %hlbf, Hdisj⟩
  ihave %hcmp := wlogLbCompare log0 σ.wmLog $$ Hlb0 Hlbσ
  icases keepPure (wlat4SyncLatestVal σ a te v) $$ Hi Hw with ⟨%hlv, Hi, Hw⟩
  icases Hdisj with (⟨%hv, %hT⟩ | ⟨%hv, %hT, #HP0⟩)
  · -- the flag is still clear, so nothing non-clear is readable at all
    subst hv
    exact (wstartedClearNow (wimg σ) σ.wmLog log0 a T te j t b hj himg hcov hT hlbf hcmp hlv
      hb hne).elim
  · subst hv
    obtain ⟨hTle, hbb⟩ := wstartedCollapse (wimg σ) σ.wmLog log0 a T te lockOne j t b hj himg
      hcov hlbf hcmp hlv (Or.inr ⟨rfl, hT⟩) hb hne
    isplitl [Hi]
    · iexact Hi
    isplitl [Hw]
    · iexists te, lockOne
      isplitl [Hw]
      · iexact Hw
      iexists T, log0
      isplitr
      · iexact Hlb0
      isplitr
      · ipureintro; exact hcov
      isplitr
      · ipureintro; exact hlbf
      iright
      isplitr
      · ipureintro; rfl
      isplitr
      · ipureintro; exact hT
      iexact HP0
    isplitr
    · ipureintro; exact hbb
    iexists T
    isplitr
    · ipureintro; exact hTle
    iexact HP0

/-- (e) THE THREE COMPOSED, at the σ altitude: observation, the load's own view gain, the
fence.  `hgain` is the racy `lw`'s own ISA content (`wstartedReadVrOld` discharges it for a hart
with an empty forward bank). -/
theorem wstartedReader (a : PAddr) (P : VProp GF) [Persistent P] (σ σf : Wmstate) (ws' : Wstate)
    (ak : AkInfo) (j t : Nat) (b : BitVec 8) (bk : barrier_kind) :
    wstartedImgClear σ a →
    j < 4 →
    wbyteOk σ ak (WeakInterp.accAddr a j) t b →
    b ≠ nthByte (n := 4) lockZero 0 →
    t ≤ σf.wmWs.wVrOld →
    acqPredR bk →
    wVFence bk σf ws' →
    wlogLb (GF := GF) σ.wmLog ⊢
      wlatInterp (GF := GF) σ.wmImg σ.wmLog -∗
        wstartedBody a P -∗
          wlatInterp (GF := GF) σ.wmImg σ.wmLog ∗ wstartedBody a P ∗
            ⌜b = nthByte (n := 4) lockOne j⌝ ∗ vwpHold P ws' := by
  intro himg hj hok hne hgain hbk hQ
  iintro #Hlbσ Hi Hbody
  icases wstartedObserve a P σ ak j t b himg hj hok hne $$ Hlbσ Hi Hbody with
    ⟨Hi, Hbody, %hbb, %T, %hTle, #HP0⟩
  isplitl [Hi]
  · iexact Hi
  isplitl [Hbody]
  · iexact Hbody
  isplitr
  · ipureintro; exact hbb
  iapply wstartedDeliverGen P σf ws' T bk hbk (by omega) hQ
  iexact HP0

end weakStarted

end Weak
