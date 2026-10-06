/-
Weak: **the STORE WINDOW update** (M3b item 1).

Rocq: `iris/WeakStore.v` @ xxvzwolszwmp (1cc222280).

The Rocq header, in substance (Rocq vocabulary).

WHAT THIS IS FOR.  Everything the weak layer owned across a store so far was ONE
BYTE wide: `WeakGhost.wlatAgreeStore` re-establishes the state-interpretation's
latest-write tie only for a message that writes exactly one address, and
`WeakVProp.wpt_store_rule` inherits that restriction.  The lock library cannot
live with it.  A release is `sw` -- ONE message covering FOUR bytes -- and the
acquire is `amoswap.w.aq`, whose write half is the same four-byte message; and
what the lock invariant holds over the lock word is a FOUR-BYTE bundle
(`WeakInstr.wlat4`, the bare objective element bundle that crosses the invariant
boundary, or `WeakInstr.wpt4` at the owned altitude).  Neither bundle could be
RETARGETED at the timestamp a store creates, so the invariant could be opened and
read but never closed at the new value.

This file supplies exactly that retargeting, at three altitudes:

  §1  `wlatAgreeStoreWin` -- the PURE framing lemma, stated over an arbitrary
      window `W` rather than at width 4: the updated map holds the fresh
      message's bytes at the fresh top timestamp inside `W` and is unchanged
      outside it.  `WeakGhost.wlatAgreeStore` is the singleton instance
      (`wlatAgreeStoreWinSingleton`).
  §2  the width-`n` message facts: a `wwriteMsg` writes nothing outside
      `[paZ pa, paZ pa + n)`, and the floor a whole-window store leaves at EVERY
      byte of its window (`flrWwritePost`), which is the four-byte post-view
      side condition.
  §3  `winsw` / `wlatAgreeStoreW` -- THE WINDOW INSERT AT EVERY WIDTH AT ONCE,
      and the pure window update over it.  `wins4` (§3b) is its `n := 4`
      instance, on the nose.  §3c is the C/D/S state map's window (`winsl`).
  §4  `wlat4Store` -- the bundle update at the iProp altitude, full fraction, one
      four-byte message appended, all four elements retargeted at
      `σ.wmLog.length + 1`.  THIS is the deliverable the lock library consumes.
  §4b `wpt4Store` -- the same at the vProp/`vwpHold` altitude; §4c the owned
      (`wpt4Own`) altitude; §4d the sync bundle (`wlat4Sync`); §4d' the lock
      bundle (`wlat4L`); §4e the φ exporters.

NOTE ON THE PRE-TIMESTAMPS.  The primitive (`wlat4StorePrim`) takes the four
elements at FOUR INDEPENDENT timestamps and values: `wpt4` existentially binds one
timestamp PER BYTE, so a bundle owned at the vProp altitude does not come with a
common pre-timestamp -- only the POST-timestamp is shared, because it is the one
message's own.

**Deviations from Rocq.**

1. NAMES: the tree's camelCase (map below).  Vocabulary as `Weak/WeakInstr.lean`
   deviation 1: `S (length l)` ↦ `l.length + 1`, `pa_z` ↦ `paZ`, `acc_addr` ↦
   `WeakInterp.accAddr`, `pa_add a j` ↦ `a + BitVec.ofNat 64 j`, `n : N` ↦
   `n : Nat` (so `N.to_nat n` ↦ `n`), `fin_to_nat c` ↦ `c.val`, `nth_byte w j` ↦
   `nthByte (n := 4) w j`, `wflat … !! a = Some v` ↦ `wflatMem … a = some v`,
   `<[k := x]> m` ↦ `insert m k x`, `m !! k` ↦ `get? m k`, `Physaddr a` ↦
   `.Physaddr a`, `DfracOwn 1` ↦ `DFrac.own 1`.
2. WIDTHS: the stored value is `v : BitVec (8 * n)` wherever Rocq has any width
   `{w : N} (v : bv w)` (`wwriteMsgWinNone`, `wwriteMsgZs*`,
   `wcdsAgreeNonplain*`, `winsw`, `wlatAgreeStoreW`), because
   `WeakInterp.wwriteMsg` and `nthByte` are stated at `8 * n` (WeakInterp
   deviation 7).  The width-4 (8) instances take `v : BitVec 32` (`BitVec 64`).
3. STATEMENT SHAPES (WeakInstr deviation 3): Rocq `A -∗ B -∗ C` (and `A -∗ B ==∗
   C`) is `A ⊢ B -∗ C` (`A ⊢ B -∗ |==> C`); Rocq `P ⊢ Q` stays.
4. `wlatAgreeStoreWin`: Rocq proves it constructively (`dec_stable`); Lean is
   classical (`by_cases` on `W a`).  The statement is unchanged (no decidability
   of `W` assumed).
5. `wcds_plain_step`/`wcds_agree_winsl`: the Lean `WeakGhost.wcdsOkStoreOwn`
   steps with `wcdsOwnStep` (excl keeps the state), exactly Rocq's
   `wcds_ok_store_own`; the excl arm is closed by `wcdsCleanDirty` as in Rocq.
6. `↦w₄ₒ`: Rocq's notation uses the ambient `cpu_id`; Lean has no ambient hart,
   so it is `a ↦w₄ₒ[c] w` (`wpt4Own c a w`).
7. `wlat4_store`'s `acc_wf a 4` premise is kept (unused, as in Rocq).
8. Lean-only helpers: `wins4Unfold` (the insert chain `wins4` is, by `rfl`),
   `wlat4Unfold` (one `wlat4` unfolded, by `rfl`, so a single occurrence can be
   rewritten),
   `bigSepL4` (the four-element `[∗list]` unrolled, by `rfl`), `wownStUpdate`
   (one `ghost_map_update` of an owned state element, which Rocq inlines in
   `wcds_update_list`), `syncByteLookup` (the auth lookup of a sync witness,
   inlined in Rocq), `wpt4Own_at` (the definitional decode of a held
   `wpt4Own`), and `wlatElByteFlatGen` (the per-byte `accWfByte` rewrite Rocq
   performs inline in `wlat4_el_flat_gen`).
9. Rocq's `Print Assumptions` (§5) has no Lean counterpart in the file (the lint
   bans axioms tree-wide).

**Rocq → Lean name map.**  `wlat_agree_store_win` `wlatAgreeStoreWin`,
`wlat_agree_store_win_singleton` `wlatAgreeStoreWinSingleton`,
`wwrite_msg_win_none` `wwriteMsgWinNone`, `wwrite_msg_win_none1`
`wwriteMsgWinNone1`, `wwrite_msg_zs` `wwriteMsgZs`, `wwrite_msg_zs4`
`wwriteMsgZs4`, `wwrite_msg_zs8` `wwriteMsgZs8`, `wcds_agree_nonplain4`
`wcdsAgreeNonplain4`, `wcds_agree_nonplain8` `wcdsAgreeNonplain8`,
`coh_store_post_bytes_in` `cohStorePostBytesIn`, `flr_store_post_run`
`flrStorePostRun`, `flr_store_post_run_d` `flrStorePostRunD`, `wwrite_post_img`
`wwritePostImg`, `flr_wwrite_post` `flrWwritePost`, `winsw` `winsw`,
`winsw_lookup_in` `winswLookupIn`, `winsw_lookup_out` `winswLookupOut`,
`wlat_agree_store_w` `wlatAgreeStoreW`, `wins4` `wins4`, `wins4_winsw`
`wins4Winsw`, `wins4_lookup_in` `wins4LookupIn`, `wins4_lookup_out`
`wins4LookupOut`, `wlat_agree_store4` `wlatAgreeStore4`, `winsl` `winsl`,
`winsl_lookup_in` `winslLookupIn`, `winsl_lookup_out` `winslLookupOut`,
`wcds_plain_step` `wcdsPlainStep`, `wcds_agree_winsl` `wcdsAgreeWinsl`,
`wcds_lookup_list` `wcdsLookupList`, `wcds_update_list` `wcdsUpdateList`,
`wcds_store_list` `wcdsStoreList`, `wlat4_own` `wlat4Own`, `wpt4_own` `wpt4Own`,
`wpt4_own_of_wpt4` `wpt4OwnOfWpt4`, `wpt4_own_facts` `wpt4OwnFacts`,
`wpt4_own_mono` `wpt4OwnMono`, `wlat4_store_prim` `wlat4StorePrim`,
`wlat4_store_prim_own` `wlat4StorePrimOwn`, `wlat4_store_gen` `wlat4StoreGen`,
`wlat4_store` `wlat4Store`, `wpt4_at_elems` `wpt4AtElems`, `wlat4_wpt4`
`wlat4Wpt4`, `wpt4_store` `wpt4Store`, `wpt4_own_at_elems` `wpt4OwnAtElems`,
`wlat4_own_wpt4_own` `wlat4OwnWpt4Own`, `wpt4_store_own` `wpt4StoreOwn`,
`wpt4_own_flat_pin` `wpt4OwnFlatPin`, `wpt4_own_flat` `wpt4OwnFlat`,
`wpt4_own_pinned` `wpt4OwnPinned`, `wlat4_el` `wlat4El`, `wlat4_el_of_wlat4`
`wlat4ElOfWlat4`, `wlat4_sync` `wlat4Sync`, `wlat4_sync_win` `wlat4SyncWin`,
`wlat4_el_latest_val` `wlat4ElLatestVal`, `wlat4_sync_mint` `wlat4SyncMint`,
`wlat4_sync_store_prim` `wlat4SyncStorePrim`, `wlat_el_flat_pin`
`wlatElFlatPin`, `wlat4_el_flat_gen` `wlat4ElFlatGen`, `wlat4_sync_flat_gen`
`wlat4SyncFlatGen`, `wlat4_sync_store_gen` `wlat4SyncStoreGen`, `wlock_win`
`wlockWin`, `wlat4_lock` `wlat4Lock`, `wlat4L` `wlat4L`, `wlock_win_timeless`
`wlockWin_timeless`, `wlat4_lock_timeless` `wlat4Lock_timeless`,
`wlat4L_timeless` `wlat4L_timeless`, `wlat4L_objective` `wlat4L_objective`,
`wlock_win_lookup` `wlockWinLookup`, `wcds_ins4_in` `wcdsIns4In`,
`wcds_ins4_out` `wcdsIns4Out`, `wlat4_lock_mint` `wlat4LockMint`, `wlat4L_mint`
`wlat4LMint`, `wlat4_lock_store_prim` `wlat4LockStorePrim`, `wlat4L_store_prim`
`wlat4LStorePrim`, `wlat4L_store_gen` `wlat4LStoreGen`, `wlat4_lock_store_gen`
`wlat4LockStoreGen`, `wlat4_lock_flat_gen` `wlat4LockFlatGen`,
`wlat4L_flat_gen` `wlat4LFlatGen`, `wlp_at_wlat4L` `wlpAtWlat4L`,
`wlp_alt_wlat4L` `wlpAltWlat4L`, `nv_ok_wpt4` `nvOkWpt4`, `nv_ok_wlat4_own`
`nvOkWlat4Own`, `nv_ok_wlat4` `nvOkWlat4`, `nv_ok_wlat4L` `nvOkWlat4L`,
`nv_ok_wlat4_sync` `nvOkWlat4Sync`.  Notation `a ↦w₄ₒ w` ↦ `a ↦w₄ₒ[c] w`.

**Not ported:** nothing -- every Rocq definition and lemma has a Lean twin.

**Statements checked** (by hand, against Rocq): all; the changed ones are listed
under the deviations.
-/
import Weak.WeakInstr

namespace Weak

open Iris Iris.BI Iris.BI.MonPred Iris.ProofMode Iris.Std
open MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D LeanRV64D.Functions
open Wcds

/-! ## 1. The framing lemma over an arbitrary window -/

theorem wlatAgreeStoreWin (img : Image) (log : List Wmsg) (m : Wmsg) (W : Int → Prop)
    (mm mm' : GMapF Int (Nat × BitVec 8)) :
    (∀ a', ¬ W a' → msgByte m a' = none) →
    (∀ a' tv, W a' → get? mm' a' = some tv →
      tv.1 = log.length + 1 ∧ msgByte m a' = some tv.2) →
    (∀ a', ¬ W a' → get? mm' a' = get? mm a') →
    wlatAgree img log mm →
    wlatAgree img (log ++ [m]) mm' := by
  intro hout hin hframe hag a tv ha
  by_cases hW : W a
  · obtain ⟨ht, hb⟩ := hin a tv hW ha
    obtain ⟨t, v⟩ := tv
    simp only at ht hb
    subst ht
    refine ⟨?_, ?_⟩
    · show logByte img (log ++ [m]) (log.length + 1) a = some v
      rw [logByteS, list_lookup_middle rfl]
      exact hb
    · rintro ⟨t, hlo, hhi, _⟩
      simp only [List.length_append, List.length_singleton] at hhi
      omega
  · rw [hframe a hW] at ha
    refine latestValApp img log [m] a _ _ (hag a tv ha) ?_
    refine notWritesInAppNew log [m] a ?_
    intro m0 hm0
    rw [List.mem_singleton] at hm0
    subst hm0
    exact hout a hW

/-- THE SANITY CHECK: `WeakGhost.wlatAgreeStore` is the singleton instance. -/
theorem wlatAgreeStoreWinSingleton (img : Image) (log : List Wmsg) (m : Wmsg) (a : Int)
    (v' : BitVec 8) (mm : GMapF Int (Nat × BitVec 8)) :
    msgByte m a = some v' →
    (∀ a', a' ≠ a → msgByte m a' = none) →
    wlatAgree img log mm →
    wlatAgree img (log ++ [m]) (insert mm a (log.length + 1, v')) := by
  intro hma hother hag
  refine wlatAgreeStoreWin img log m (fun z => z = a) mm _ hother ?_ ?_ hag
  · intro a' tv ha' hlk
    subst ha'
    rw [lookupInsert] at hlk
    cases hlk
    exact ⟨rfl, hma⟩
  · intro a' hne
    exact lookupInsertNe (Ne.symm hne)

/-! ## 2. What a width-`n` store's message writes, and the floor it leaves -/

/-- Outside the half-open range the access covers, the message is silent. -/
theorem wwriteMsgWinNone (tid : Option Nat) (k : WmClass) (pa : PAddr) (n : Nat)
    (v : BitVec (8 * n)) (a : Int) :
    ¬ (paZ pa ≤ a ∧ a < paZ pa + (n : Int)) → msgByte (wwriteMsg tid k pa n v) a = none := by
  intro hout
  simp only [msgByte, wwriteMsg]
  split
  · rw [List.getElem?_eq_none]
    simp only [List.length_map, List.length_range']
    omega
  · rfl

/-- ... and it IS the one-byte lemma at `n = 1`. -/
theorem wwriteMsgWinNone1 (tid : Option Nat) (k : WmClass) (pa : PAddr) (v : BitVec (8 * 1))
    (a : Int) : a ≠ paZ pa → msgByte (wwriteMsg tid k pa 1 v) a = none := by
  intro hne
  apply wwriteMsgWinNone tid k pa 1 v a
  omega

/-- WHICH ADDRESSES A WIDTH-`n` STORE CAN WRITE: the message's footprint is inside the
caller's list. -/
theorem wwriteMsgZs (tid : Option Nat) (k : WmClass) (a : PAddr) (n : Nat) (v : BitVec (8 * n))
    (zs : List Int) :
    (∀ j : Nat, j < n → WeakInterp.accAddr a j ∈ zs) →
    ∀ z, msgByte (wwriteMsg tid k a n v) z ≠ none → z ∈ zs := by
  intro hzs z hz
  by_cases hr : paZ a ≤ z ∧ z < paZ a + (n : Int)
  · have hj := hzs (z - paZ a).toNat (by omega)
    have e : WeakInterp.accAddr a (z - paZ a).toNat = z := by
      unfold WeakInterp.accAddr; omega
    rwa [e] at hj
  · exact absurd (wwriteMsgWinNone tid k a n v z hr) hz

theorem wwriteMsgZs4 (tid : Option Nat) (k : WmClass) (a : PAddr) (v : BitVec 32) :
    ∀ z, msgByte (wwriteMsg tid k a 4 v) z ≠ none →
      z ∈ [WeakInterp.accAddr a 0, WeakInterp.accAddr a 1, WeakInterp.accAddr a 2,
        WeakInterp.accAddr a 3] := by
  apply wwriteMsgZs tid k a 4 v
  intro j hj
  have : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
  rcases this with rfl | rfl | rfl | rfl <;> simp

theorem wwriteMsgZs8 (tid : Option Nat) (k : WmClass) (a : PAddr) (v : BitVec 64) :
    ∀ z, msgByte (wwriteMsg tid k a 8 v) z ≠ none →
      z ∈ [WeakInterp.accAddr a 0, WeakInterp.accAddr a 1, WeakInterp.accAddr a 2,
        WeakInterp.accAddr a 3, WeakInterp.accAddr a 4, WeakInterp.accAddr a 5,
        WeakInterp.accAddr a 6, WeakInterp.accAddr a 7] := by
  apply wwriteMsgZs tid k a 8 v
  intro j hj
  have : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

/-- T2-0's FRAMING OF THE STATE MAP ACROSS A NON-PLAIN STORE, per width. -/
theorem wcdsAgreeNonplain4 (log : List Wmsg) (tid : Option Nat) (k : WmClass) (a : PAddr)
    (v : BitVec 32) (mc : GMapF Int Wcds) (s0 : Wcds) :
    k ≠ .WCplain → isWlock s0 = false →
    get? mc (WeakInterp.accAddr a 0) = some s0 → get? mc (WeakInterp.accAddr a 1) = some s0 →
    get? mc (WeakInterp.accAddr a 2) = some s0 → get? mc (WeakInterp.accAddr a 3) = some s0 →
    wcdsAgree log mc →
    wcdsAgree (log ++ [wwriteMsg tid k a 4 v]) mc := by
  intro hk hnl K0 K1 K2 K3 hag
  refine wcdsAgreeNonplainWin log _ mc _ hk (wwriteMsgZs4 tid k a v) ?_ hag
  intro z s hz hs
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl
  · rw [K0] at hs; cases hs; exact hnl
  · rw [K1] at hs; cases hs; exact hnl
  · rw [K2] at hs; cases hs; exact hnl
  · rw [K3] at hs; cases hs; exact hnl

theorem wcdsAgreeNonplain8 (log : List Wmsg) (tid : Option Nat) (k : WmClass) (a : PAddr)
    (v : BitVec 64) (mc : GMapF Int Wcds) (s0 : Wcds) :
    k ≠ .WCplain → isWlock s0 = false →
    (∀ j : Nat, j < 8 → get? mc (WeakInterp.accAddr a j) = some s0) →
    wcdsAgree log mc →
    wcdsAgree (log ++ [wwriteMsg tid k a 8 v]) mc := by
  intro hk hnl K hag
  refine wcdsAgreeNonplainWin log _ mc _ hk (wwriteMsgZs8 tid k a v) ?_ hag
  intro z s hz hs
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  have hz' : ∃ j, j < 8 ∧ z = WeakInterp.accAddr a j := by
    rcases hz with h | h | h | h | h | h | h | h
    · exact ⟨0, by omega, h⟩
    · exact ⟨1, by omega, h⟩
    · exact ⟨2, by omega, h⟩
    · exact ⟨3, by omega, h⟩
    · exact ⟨4, by omega, h⟩
    · exact ⟨5, by omega, h⟩
    · exact ⟨6, by omega, h⟩
    · exact ⟨7, by omega, h⟩
  obtain ⟨j, hj, rfl⟩ := hz'
  rw [K j hj] at hs
  cases hs
  exact hnl

/-- THE WINDOW FLOOR: a width-`n` store raises the floor at every byte of its window. -/
theorem cohStorePostBytesIn (ws : Wstate) (rl : Bool) (as_ : List Int) (t : Nat) (a : Int) :
    a ∈ as_ → t ≤ coh (storePostBytes ws rl as_ t) a :=
  storePostFoldCoh rl t as_ ws a

theorem flrStorePostRun (ws : Wstate) (rl : Bool) (base : Int) (n t j : Nat) :
    j < n → t ≤ flr (wsView (storePostRun ws rl base n t)) (base + (j : Int)) := by
  intro hj
  rw [flr_wsView]
  have := storePostRunCoh ws rl base n t j hj
  omega

/-- D3-2: the same, for the DEPENDENCY-CARRYING store. -/
theorem flrStorePostRunD (ws : Wstate) (rl : Bool) (vaddr vdata : Nat) (base : Int) (n t j : Nat) :
    j < n → t ≤ flr (wsView (storePostRunD ws rl vaddr vdata base n t)) (base + (j : Int)) := by
  intro hj
  rw [flr_wsView]
  have := storePostRunDCoh ws rl vaddr vdata base n t j hj
  omega

theorem wwritePostImg (tid : Option Nat) (s : Wmstate) (ak : AkInfo) (pa : PAddr) (n : Nat)
    (v : BitVec (8 * n)) : (wwritePost tid s ak pa n v).wmImg = s.wmImg := rfl

/-- After a width-`n` store, the hart's floor at EVERY byte of the window covers the store's
own timestamp. -/
theorem flrWwritePost (tid : Option Nat) (σ : Wmstate) (ak : AkInfo) (a : PAddr) (n : Nat)
    (v : BitVec (8 * n)) (j : Nat) :
    j < n →
    σ.wmLog.length + 1 ≤
      flr (wsView (wwritePost tid σ ak a n v).wmWs) (WeakInterp.accAddr a j) :=
  fun hj => flrStorePostRun σ.wmWs ak.akSync (paZ a) n (σ.wmLog.length + 1) j hj

/-! ## 3. THE WINDOW INSERT, AT EVERY WIDTH AT ONCE -/

def winsw (a : PAddr) (T : Nat) {m : Nat} (v : BitVec (8 * m)) :
    Nat → GMapF Int (Nat × BitVec 8) → GMapF Int (Nat × BitVec 8)
  | 0, mm => mm
  | k + 1, mm => insert (winsw a T v k mm) (WeakInterp.accAddr a k) (T, nthByte v k)

theorem winswLookupIn (a : PAddr) (T : Nat) {m : Nat} (v : BitVec (8 * m)) (n : Nat)
    (mm : GMapF Int (Nat × BitVec 8)) (j : Nat) :
    j < n → get? (winsw a T v n mm) (WeakInterp.accAddr a j) = some (T, nthByte v j) := by
  induction n generalizing j with
  | zero => intro hj; omega
  | succ k ih =>
    intro hj
    simp only [winsw]
    by_cases hjk : j = k
    · subst hjk; exact lookupInsert
    · rw [lookupInsertNe (by unfold WeakInterp.accAddr; omega)]
      exact ih j (by omega)

theorem winswLookupOut (a : PAddr) (T : Nat) {m : Nat} (v : BitVec (8 * m)) (n : Nat)
    (mm : GMapF Int (Nat × BitVec 8)) (z : Int) :
    (∀ j : Nat, j < n → WeakInterp.accAddr a j ≠ z) → get? (winsw a T v n mm) z = get? mm z := by
  induction n with
  | zero => intro _; rfl
  | succ k ih =>
    intro hne
    simp only [winsw]
    rw [lookupInsertNe (hne k (by omega))]
    exact ih (fun j hj => hne j (by omega))

/-- THE WINDOW UPDATE, pure part, at every width. -/
theorem wlatAgreeStoreW (img : Image) (log : List Wmsg) (tid : Option Nat) (k : WmClass)
    (a : PAddr) (n : Nat) (v : BitVec (8 * n)) (mm : GMapF Int (Nat × BitVec 8)) :
    wlatAgree img log mm →
    wlatAgree img (log ++ [wwriteMsg tid k a n v]) (winsw a (log.length + 1) v n mm) := by
  intro hag
  refine wlatAgreeStoreWin img log _ (fun z => paZ a ≤ z ∧ z < paZ a + (n : Int)) mm _ ?_ ?_ ?_ hag
  · intro z hz
    exact wwriteMsgWinNone tid k a n v z hz
  · intro z tv hz hlk
    have hex : ∃ j : Nat, j < n ∧ z = WeakInterp.accAddr a j :=
      ⟨(z - paZ a).toNat, by omega, by unfold WeakInterp.accAddr; omega⟩
    obtain ⟨j, hj, rfl⟩ := hex
    rw [winswLookupIn a _ v n mm j hj] at hlk
    cases hlk
    exact ⟨rfl, wwriteMsgByte tid k a n v j hj⟩
  · intro z hz
    apply winswLookupOut
    intro j hj heq
    apply hz
    subst heq
    unfold WeakInterp.accAddr
    omega

/-! ### 3b. The four-byte instance -/

def wins4 (a : PAddr) (T : Nat) (v : BitVec 32) (mm : GMapF Int (Nat × BitVec 8)) :
    GMapF Int (Nat × BitVec 8) :=
  winsw (m := 4) a T v 4 mm

theorem wins4Winsw (a : PAddr) (T : Nat) (v : BitVec 32) (mm : GMapF Int (Nat × BitVec 8)) :
    wins4 a T v mm = winsw (m := 4) a T v 4 mm := rfl

/-- The insert chain four successive `ghost_map_update`s leave behind (Lean-only). -/
theorem wins4Unfold (a : PAddr) (T : Nat) (v : BitVec 32) (mm : GMapF Int (Nat × BitVec 8)) :
    wins4 a T v mm =
      insert (insert (insert (insert mm (WeakInterp.accAddr a 0) (T, nthByte (n := 4) v 0))
        (WeakInterp.accAddr a 1) (T, nthByte (n := 4) v 1))
        (WeakInterp.accAddr a 2) (T, nthByte (n := 4) v 2))
        (WeakInterp.accAddr a 3) (T, nthByte (n := 4) v 3) := rfl

theorem wins4LookupIn (a : PAddr) (T : Nat) (v : BitVec 32) (mm : GMapF Int (Nat × BitVec 8))
    (j : Nat) :
    j < 4 → get? (wins4 a T v mm) (WeakInterp.accAddr a j) = some (T, nthByte (n := 4) v j) :=
  fun hj => winswLookupIn a T v 4 mm j hj

theorem wins4LookupOut (a : PAddr) (T : Nat) (v : BitVec 32) (mm : GMapF Int (Nat × BitVec 8))
    (z : Int) : ¬ (paZ a ≤ z ∧ z < paZ a + 4) → get? (wins4 a T v mm) z = get? mm z := by
  intro hout
  apply winswLookupOut
  intro j hj heq
  apply hout
  subst heq
  unfold WeakInterp.accAddr
  omega

theorem wlatAgreeStore4 (img : Image) (log : List Wmsg) (tid : Option Nat) (k : WmClass)
    (a : PAddr) (v : BitVec 32) (mm : GMapF Int (Nat × BitVec 8)) :
    wlatAgree img log mm →
    wlatAgree img (log ++ [wwriteMsg tid k a 4 v]) (wins4 a (log.length + 1) v mm) :=
  wlatAgreeStoreW img log tid k a 4 v mm

/-! ### 3c. THE C/D/S WINDOW, AT EVERY WIDTH AT ONCE -/

def winsl : List Int → Wcds → GMapF Int Wcds → GMapF Int Wcds
  | [], _, mc => mc
  | z :: zs', s, mc => insert (winsl zs' s mc) z s

theorem winslLookupIn (zs : List Int) (s : Wcds) (mc : GMapF Int Wcds) (z : Int) :
    z ∈ zs → get? (winsl zs s mc) z = some s := by
  induction zs with
  | nil => intro h; cases h
  | cons z0 zs ih =>
    intro hz
    simp only [winsl]
    by_cases h : z = z0
    · subst h; exact lookupInsert
    · rw [lookupInsertNe (Ne.symm h)]
      exact ih (by rcases List.mem_cons.1 hz with h' | h'; exact absurd h' h; exact h')

theorem winslLookupOut (zs : List Int) (s : Wcds) (mc : GMapF Int Wcds) (z : Int) :
    z ∉ zs → get? (winsl zs s mc) z = get? mc z := by
  induction zs with
  | nil => intro _; rfl
  | cons z0 zs ih =>
    intro hz
    simp only [winsl]
    rw [lookupInsertNe (by intro h; subst h; exact hz List.mem_cons_self)]
    exact ih (fun h => hz (List.mem_cons_of_mem _ h))

/-- The state a plain/release/exclusive store leaves inside its window. -/
def wcdsPlainStep (c : CPU) (k : WmClass) : Wcds :=
  match k with
  | .WCrel => WClean
  | _ => WDirty c

theorem wcdsAgreeWinsl (log : List Wmsg) (mnew : Wmsg) (zs : List Int) (c : CPU)
    (mc : GMapF Int Wcds) :
    mnew.wmTid = some c.val →
    (∀ z, msgByte mnew z ≠ none → z ∈ zs) →
    (∀ z, z ∈ zs → ∃ s, get? mc z = some s ∧ (s = WClean ∨ s = WDirty c)) →
    wcdsAgree log mc →
    wcdsAgree (log ++ [mnew]) (winsl zs (wcdsPlainStep c mnew.wmAk) mc) := by
  intro htid hcov hold hag z s hz
  by_cases hin : z ∈ zs
  · rw [winslLookupIn zs _ mc z hin] at hz
    cases hz
    obtain ⟨s0, hs0, hs0ok⟩ := hold z hin
    have hstep := wcdsOkStoreOwn log mnew z c s0 htid hs0ok (hag z s0 hs0)
    rcases hk : mnew.wmAk with _ | _ | _ <;>
      simp only [hk, wcdsPlainStep, wcdsOwnStep] at hstep ⊢
    · exact hstep
    · exact hstep
    · rcases hs0ok with rfl | rfl
      · exact wcdsCleanDirty _ z c hstep
      · exact hstep
  · rw [winslLookupOut zs _ mc z hin] at hz
    refine wcdsOkApp log [mnew] z s ?_ (hag z s hz)
    intro m0 hm0
    rw [List.mem_singleton] at hm0
    subst hm0
    apply Classical.byContradiction
    intro hb
    exact hin (hcov z hb)

section cdswin
variable {GF : BundledGFunctors} [WeakGS GF]

/-- The four-element `[∗list]`, unrolled (Lean-only). -/
theorem bigSepL4 {PROP : Type _} [BI PROP] {A : Type _} (Φ : A → PROP) (x0 x1 x2 x3 : A) :
    ([∗list] x ∈ [x0, x1, x2, x3], Φ x) ⊣⊢ iprop(Φ x0 ∗ Φ x1 ∗ Φ x2 ∗ Φ x3 ∗ emp) := .rfl

theorem wcdsLookupList (c : CPU) (zs : List Int) (mc : GMapF Int Wcds) :
    ghost_map_auth (GF := GF) (WeakGS.cdsName (GF := GF)) (DFrac.own 1) mc ⊢
      ([∗list] z ∈ zs, wownSt (GF := GF) c z) -∗
        ⌜∀ z, z ∈ zs → ∃ s, get? mc z = some s ∧ (s = WClean ∨ s = WDirty c)⌝ := by
  induction zs with
  | nil =>
    iintro _ _
    ipureintro
    intro z hz
    cases hz
  | cons z zs ih =>
    iintro Ha Hl
    icases BigSepL.bigSepL_cons.1 $$ Hl with ⟨Hz, Hl⟩
    icases keepPure (wand_intro (wownStLookup c z mc)) $$ Ha Hz with ⟨%h0, Ha, -⟩
    ihave %hr := ih $$ Ha Hl
    ipureintro
    intro z' hz'
    rcases List.mem_cons.1 hz' with rfl | h
    · exact h0
    · exact hr z' h

/-- One owned state element moved to `snew` (Lean-only; inlined in Rocq). -/
theorem wownStUpdate (c : CPU) (z : Int) (snew : Wcds) (mc : GMapF Int Wcds) :
    (snew = WClean ∨ snew = WDirty c) →
    ghost_map_auth (GF := GF) (WeakGS.cdsName (GF := GF)) (DFrac.own 1) mc ⊢
      wownSt (GF := GF) c z -∗
        |==> (ghost_map_auth (GF := GF) (WeakGS.cdsName (GF := GF)) (DFrac.own 1)
          (insert mc z snew) ∗ wownSt (GF := GF) c z) := by
  intro hnew
  unfold wownSt wcdsEl
  iintro Ha ⟨%s, Hel, -⟩
  imod ghost_map_update snew $$ Ha Hel with ⟨Ha, Hel⟩
  imodintro
  iframe Ha
  iexists snew
  iframe Hel
  ipureintro
  exact hnew

theorem wcdsUpdateList (c : CPU) (zs : List Int) (snew : Wcds) (mc : GMapF Int Wcds) :
    (snew = WClean ∨ snew = WDirty c) →
    ghost_map_auth (GF := GF) (WeakGS.cdsName (GF := GF)) (DFrac.own 1) mc ⊢
      ([∗list] z ∈ zs, wownSt (GF := GF) c z) -∗
        |==> (ghost_map_auth (GF := GF) (WeakGS.cdsName (GF := GF)) (DFrac.own 1)
          (winsl zs snew mc) ∗ [∗list] z ∈ zs, wownSt (GF := GF) c z) := by
  intro hnew
  induction zs generalizing mc with
  | nil =>
    simp only [winsl]
    iintro Ha Hl
    imodintro
    iframe Ha Hl
  | cons z zs ih =>
    simp only [winsl]
    iintro Ha Hl
    icases BigSepL.bigSepL_cons.1 $$ Hl with ⟨Hz, Hl⟩
    imod ih mc $$ Ha Hl with ⟨Ha, Hl⟩
    imod wownStUpdate c z snew _ hnew $$ Ha Hz with ⟨Ha, Hz⟩
    imodintro
    iframe Ha
    iapply BigSepL.bigSepL_cons.2
    iframe Hz Hl

/-- THE C/D/S HALF OF AN OWNED STORE, width-generic. -/
theorem wcdsStoreList (c : CPU) (mnew : Wmsg) (log : List Wmsg) (zs : List Int)
    (mc : GMapF Int Wcds) :
    mnew.wmTid = some c.val →
    (∀ z, msgByte mnew z ≠ none → z ∈ zs) →
    wcdsAgree log mc →
    ghost_map_auth (GF := GF) (WeakGS.cdsName (GF := GF)) (DFrac.own 1) mc ⊢
      ([∗list] z ∈ zs, wownSt (GF := GF) c z) -∗
        |==> (∃ mc', ghost_map_auth (GF := GF) (WeakGS.cdsName (GF := GF)) (DFrac.own 1) mc' ∗
          ⌜wcdsAgree (log ++ [mnew]) mc'⌝ ∗ [∗list] z ∈ zs, wownSt (GF := GF) c z) := by
  intro htid hcov hag
  iintro Ha Hl
  icases keepPure (wcdsLookupList c zs mc) $$ Ha Hl with ⟨%hold, Ha, Hl⟩
  imod wcdsUpdateList c zs (wcdsPlainStep c mnew.wmAk) mc
      (by unfold wcdsPlainStep; split <;> simp) $$ Ha Hl with ⟨Ha, Hl⟩
  imodintro
  iexists winsl zs (wcdsPlainStep c mnew.wmAk) mc
  iframe Ha Hl
  ipureintro
  exact wcdsAgreeWinsl log mnew zs c mc htid hcov hold hag

end cdswin

/-! ## 4. The bundle updates -/

section store
variable {GF : BundledGFunctors} [WeakGS GF]

/-- THE OWNED FOUR-BYTE BUNDLES (φ-upgrade §1). -/
def wlat4Own (c : CPU) (a : PAddr) (t : Nat) (w : BitVec 32) : IProp GF :=
  iprop(wlatElem (GF := GF) (WeakInterp.accAddr a 0) (DFrac.own 1) t (nthByte (n := 4) w 0) ∗
      wownSt (GF := GF) c (WeakInterp.accAddr a 0) ∗
    wlatElem (GF := GF) (WeakInterp.accAddr a 1) (DFrac.own 1) t (nthByte (n := 4) w 1) ∗
      wownSt (GF := GF) c (WeakInterp.accAddr a 1) ∗
    wlatElem (GF := GF) (WeakInterp.accAddr a 2) (DFrac.own 1) t (nthByte (n := 4) w 2) ∗
      wownSt (GF := GF) c (WeakInterp.accAddr a 2) ∗
    wlatElem (GF := GF) (WeakInterp.accAddr a 3) (DFrac.own 1) t (nthByte (n := 4) w 3) ∗
      wownSt (GF := GF) c (WeakInterp.accAddr a 3))

def wpt4Own (c : CPU) (a : PAddr) (w : BitVec 32) : VProp GF :=
  iprop(⌜is_aligned_paddr (.Physaddr a) 4 = true⌝ ∗ ⌜accWf a 4⌝ ∗
    wptOwnH (GF := GF) c (WeakInterp.accAddr a 0) (nthByte (n := 4) w 0) ∗
    wptOwnH (GF := GF) c (WeakInterp.accAddr a 1) (nthByte (n := 4) w 1) ∗
    wptOwnH (GF := GF) c (WeakInterp.accAddr a 2) (nthByte (n := 4) w 2) ∗
    wptOwnH (GF := GF) c (WeakInterp.accAddr a 3) (nthByte (n := 4) w 3))

notation:50 a:50 " ↦w₄ₒ[" c "] " w:50 => wpt4Own c a w

/-- The definitional decode of a held owned bundle (Lean-only). -/
theorem wpt4Own_at (c : CPU) (a : PAddr) (w : BitVec 32) (ws : Wstate) :
    vwpHold (wpt4Own (GF := GF) c a w) ws ⊣⊢
      iprop(⌜is_aligned_paddr (.Physaddr a) 4 = true⌝ ∗ ⌜accWf a 4⌝ ∗
        vwpHold (wptOwnH (GF := GF) c (WeakInterp.accAddr a 0) (nthByte (n := 4) w 0)) ws ∗
        vwpHold (wptOwnH (GF := GF) c (WeakInterp.accAddr a 1) (nthByte (n := 4) w 1)) ws ∗
        vwpHold (wptOwnH (GF := GF) c (WeakInterp.accAddr a 2) (nthByte (n := 4) w 2)) ws ∗
        vwpHold (wptOwnH (GF := GF) c (WeakInterp.accAddr a 3) (nthByte (n := 4) w 3)) ws) :=
  .rfl

theorem wpt4OwnOfWpt4 (c : CPU) (a : PAddr) (w : BitVec 32) :
    wpt4 (GF := GF) a (DFrac.own 1) w ⊢ wpt4Own c a w := by
  unfold wpt4 wpt4Own
  iintro ⟨%h1, %h2, H0, H1, H2, H3⟩
  isplitr
  · ipureintro; exact h1
  isplitr
  · ipureintro; exact h2
  isplitl [H0]
  · iapply wptOwnH_of_wpt c _ _; iexact H0
  isplitl [H1]
  · iapply wptOwnH_of_wpt c _ _; iexact H1
  isplitl [H2]
  · iapply wptOwnH_of_wpt c _ _; iexact H2
  · iapply wptOwnH_of_wpt c _ _; iexact H3

theorem wpt4OwnFacts (c : CPU) (a : PAddr) (w : BitVec 32) :
    wpt4Own (GF := GF) c a w ⊢ ⌜is_aligned_paddr (.Physaddr a) 4 = true ∧ accWf a 4⌝ := by
  unfold wpt4Own
  iintro ⟨%h1, %h2, -⟩
  ipureintro
  exact ⟨h1, h2⟩

theorem wpt4OwnMono (c : CPU) (a : PAddr) (w : BitVec 32) (ws ws' : Wstate) :
    wsLe ws ws' → vwpHold (wpt4Own (GF := GF) c a w) ws ⊢ vwpHold (wpt4Own (GF := GF) c a w) ws' :=
  fun h => vwpHold_mono _ h

/-- The definitional unfolding of one `wlat4` (Lean-only; rewrites a single occurrence). -/
theorem wlat4Unfold (a : PAddr) (dq : DFrac) (t : Nat) (w : BitVec 32) :
    wlat4 (GF := GF) a dq t w =
      iprop(wlatPointsto (GF := GF) (WeakInterp.accAddr a 0) dq t (nthByte (n := 4) w 0) ∗
        wlatPointsto (GF := GF) (WeakInterp.accAddr a 1) dq t (nthByte (n := 4) w 1) ∗
        wlatPointsto (GF := GF) (WeakInterp.accAddr a 2) dq t (nthByte (n := 4) w 2) ∗
        wlatPointsto (GF := GF) (WeakInterp.accAddr a 3) dq t (nthByte (n := 4) w 3)) := rfl

/-- THE PRIMITIVE.  Four full-fraction elements over the window, at arbitrary pre-timestamps
and pre-values, one four-byte message appended. -/
theorem wlat4StorePrim (tid : Option Nat) (k : WmClass) (σ : Wmstate) (a : PAddr) (v : BitVec 32)
    (t0 t1 t2 t3 : Nat) (b0 b1 b2 b3 : BitVec 8) :
    k ≠ .WCplain →
    wlatInterp (GF := GF) σ.wmImg σ.wmLog ⊢
      wlatPointsto (GF := GF) (WeakInterp.accAddr a 0) (DFrac.own 1) t0 b0 -∗
      wlatPointsto (GF := GF) (WeakInterp.accAddr a 1) (DFrac.own 1) t1 b1 -∗
      wlatPointsto (GF := GF) (WeakInterp.accAddr a 2) (DFrac.own 1) t2 b2 -∗
      wlatPointsto (GF := GF) (WeakInterp.accAddr a 3) (DFrac.own 1) t3 b3 -∗
        |==> (wlatInterp (GF := GF) σ.wmImg (σ.wmLog ++ [wwriteMsg tid k a 4 v]) ∗
          wlat4 (GF := GF) a (DFrac.own 1) (σ.wmLog.length + 1) v) := by
  intro hk
  unfold wlatInterp wlatPointsto wlat4 wlatElem wclean wcdsEl
  iintro ⟨%mm, %mc, Hauth, %hag, Hc, %hagc⟩ ⟨H0, C0⟩ ⟨H1, C1⟩ ⟨H2, C2⟩ ⟨H3, C3⟩
  imod ghost_map_update (σ.wmLog.length + 1, nthByte (n := 4) v 0) $$ Hauth H0 with ⟨Hauth, H0⟩
  imod ghost_map_update (σ.wmLog.length + 1, nthByte (n := 4) v 1) $$ Hauth H1 with ⟨Hauth, H1⟩
  imod ghost_map_update (σ.wmLog.length + 1, nthByte (n := 4) v 2) $$ Hauth H2 with ⟨Hauth, H2⟩
  imod ghost_map_update (σ.wmLog.length + 1, nthByte (n := 4) v 3) $$ Hauth H3 with ⟨Hauth, H3⟩
  -- T2-0: the window's four bytes are pinned CLEAN by the very fragments handed in
  icombine Hc C0 gives %K0
  icombine Hc C1 gives %K1
  icombine Hc C2 gives %K2
  icombine Hc C3 gives %K3
  imodintro
  isplitl [Hauth Hc]
  · iexists _, mc
    iframe Hauth Hc
    isplit
    · ipureintro
      rw [← wins4Unfold]
      exact wlatAgreeStore4 _ _ tid k a v mm hag
    · ipureintro
      exact wcdsAgreeNonplain4 _ tid k a v mc WClean hk rfl K0 K1 K2 K3 hagc
  · unfold wlatPointsto wlatElem wclean wcdsEl
    iframe H0 C0 H1 C1 H2 C2 H3 C3

/-- THE OWNED PRIMITIVE -- the entry form of every PLAIN store. -/
theorem wlat4StorePrimOwn (c : CPU) (k : WmClass) (σ : Wmstate) (a : PAddr) (v : BitVec 32)
    (t0 t1 t2 t3 : Nat) (b0 b1 b2 b3 : BitVec 8) :
    wlatInterp (GF := GF) σ.wmImg σ.wmLog ⊢
      wlatElem (GF := GF) (WeakInterp.accAddr a 0) (DFrac.own 1) t0 b0 -∗
        wownSt (GF := GF) c (WeakInterp.accAddr a 0) -∗
      wlatElem (GF := GF) (WeakInterp.accAddr a 1) (DFrac.own 1) t1 b1 -∗
        wownSt (GF := GF) c (WeakInterp.accAddr a 1) -∗
      wlatElem (GF := GF) (WeakInterp.accAddr a 2) (DFrac.own 1) t2 b2 -∗
        wownSt (GF := GF) c (WeakInterp.accAddr a 2) -∗
      wlatElem (GF := GF) (WeakInterp.accAddr a 3) (DFrac.own 1) t3 b3 -∗
        wownSt (GF := GF) c (WeakInterp.accAddr a 3) -∗
        |==> (wlatInterp (GF := GF) σ.wmImg (σ.wmLog ++ [wwriteMsg (some c.val) k a 4 v]) ∗
          wlat4Own (GF := GF) c a (σ.wmLog.length + 1) v) := by
  unfold wlatInterp wlat4Own wlatElem
  iintro ⟨%mm, %mc, Hauth, %hag, Hc, %hagc⟩ H0 C0 H1 C1 H2 C2 H3 C3
  imod ghost_map_update (σ.wmLog.length + 1, nthByte (n := 4) v 0) $$ Hauth H0 with ⟨Hauth, H0⟩
  imod ghost_map_update (σ.wmLog.length + 1, nthByte (n := 4) v 1) $$ Hauth H1 with ⟨Hauth, H1⟩
  imod ghost_map_update (σ.wmLog.length + 1, nthByte (n := 4) v 2) $$ Hauth H2 with ⟨Hauth, H2⟩
  imod ghost_map_update (σ.wmLog.length + 1, nthByte (n := 4) v 3) $$ Hauth H3 with ⟨Hauth, H3⟩
  imod wcdsStoreList c (wwriteMsg (some c.val) k a 4 v) σ.wmLog
      [WeakInterp.accAddr a 0, WeakInterp.accAddr a 1, WeakInterp.accAddr a 2,
        WeakInterp.accAddr a 3] mc rfl (wwriteMsgZs4 _ _ a v) hagc $$ Hc [C0 C1 C2 C3]
      with ⟨%mc', Hc, %hagc', Hl⟩
  · iapply (bigSepL4 (fun z => wownSt (GF := GF) c z) _ _ _ _).2
    iframe C0 C1 C2 C3
  icases (bigSepL4 (fun z => wownSt (GF := GF) c z) _ _ _ _).1 $$ Hl with ⟨C0, C1, C2, C3, -⟩
  imodintro
  isplitl [Hauth Hc]
  · iexists _, mc'
    iframe Hauth Hc
    isplit
    · ipureintro
      rw [← wins4Unfold]
      exact wlatAgreeStore4 _ _ _ k a v mm hag
    · ipureintro
      exact hagc'
  · iframe H0 C0 H1 C1 H2 C2 H3 C3

/-- THE BUNDLE UPDATE at an explicitly described post-state. -/
theorem wlat4StoreGen (tid : Option Nat) (k : WmClass) (σ σ' : Wmstate) (a : PAddr) (t : Nat)
    (w v : BitVec 32) :
    k ≠ .WCplain →
    σ'.wmImg = σ.wmImg →
    σ'.wmLog = σ.wmLog ++ [wwriteMsg tid k a 4 v] →
    wlatInterp (GF := GF) σ.wmImg σ.wmLog ⊢
      wlat4 (GF := GF) a (DFrac.own 1) t w -∗
        |==> (wlatInterp (GF := GF) σ'.wmImg σ'.wmLog ∗
          wlat4 (GF := GF) a (DFrac.own 1) (σ.wmLog.length + 1) v) := by
  intro hk himg hlog
  rw [himg, hlog]
  rw [wlat4Unfold a _ t w]
  iintro Hi ⟨H0, H1, H2, H3⟩
  iapply wlat4StorePrim tid k σ a v t t t t _ _ _ _ hk $$ Hi H0 H1 H2 H3

/-- ... and at the interpreter's OWN write post-state, which is what a leaf hands the lock
library. -/
theorem wlat4Store (tid : Option Nat) (σ : Wmstate) (ak : AkInfo) (a : PAddr) (t : Nat)
    (w : BitVec 32) (v : BitVec (8 * 4)) :
    ak.akLatest = true →
    accWf a 4 →
    wlatInterp (GF := GF) σ.wmImg σ.wmLog ⊢
      wlat4 (GF := GF) a (DFrac.own 1) t w -∗
        |==> (wlatInterp (GF := GF) (wwritePost tid σ ak a 4 v).wmImg
            (wwritePost tid σ ak a 4 v).wmLog ∗
          wlat4 (GF := GF) a (DFrac.own 1) (σ.wmLog.length + 1) v) := by
  intro hlt _
  exact wlat4StoreGen tid (wmClassOf ak σ.wmWs) σ (wwritePost tid σ ak a 4 v) a t w v
    (by simp [wmClassOf, hlt]) (wwritePostImg tid σ ak a 4 v) (wwritePostLog tid σ ak a 4 v)

/-! ### 4b. the same at the `vwpHold` / `wpt4` altitude -/

theorem wpt4AtElems (a : PAddr) (dq : DFrac) (w : BitVec 32) (ws : Wstate) :
    vwpHold (wpt4 (GF := GF) a dq w) ws ⊢
      iprop(⌜is_aligned_paddr (.Physaddr a) 4 = true⌝ ∗ ⌜accWf a 4⌝ ∗
        ∃ t0 t1 t2 t3 : Nat,
          wlatPointsto (GF := GF) (WeakInterp.accAddr a 0) dq t0 (nthByte (n := 4) w 0) ∗
          wlatPointsto (GF := GF) (WeakInterp.accAddr a 1) dq t1 (nthByte (n := 4) w 1) ∗
          wlatPointsto (GF := GF) (WeakInterp.accAddr a 2) dq t2 (nthByte (n := 4) w 2) ∗
          wlatPointsto (GF := GF) (WeakInterp.accAddr a 3) dq t3 (nthByte (n := 4) w 3)) := by
  iintro Hpt
  icases (wpt4_at a dq w ws).mp $$ Hpt with ⟨%hal, %hacc, H0, H1, H2, H3⟩
  icases (wpt_at _ dq _ ws).mp $$ H0 with ⟨%t0, H0, -⟩
  icases (wpt_at _ dq _ ws).mp $$ H1 with ⟨%t1, H1, -⟩
  icases (wpt_at _ dq _ ws).mp $$ H2 with ⟨%t2, H2, -⟩
  icases (wpt_at _ dq _ ws).mp $$ H3 with ⟨%t3, H3, -⟩
  isplitr
  · ipureintro; exact hal
  isplitr
  · ipureintro; exact hacc
  iexists t0, t1, t2, t3
  iframe H0 H1 H2 H3

/-- THE GLUE: an objective element bundle whose timestamp the hart's floor covers IS an owned
four-byte points-to. -/
theorem wlat4Wpt4 (a : PAddr) (dq : DFrac) (t : Nat) (w : BitVec 32) (ws : Wstate) :
    is_aligned_paddr (.Physaddr a) 4 = true →
    accWf a 4 →
    (∀ j : Nat, j < 4 → t ≤ flr (wsView ws) (WeakInterp.accAddr a j)) →
    wlat4 (GF := GF) a dq t w ⊢ vwpHold (wpt4 (GF := GF) a dq w) ws := by
  intro hal hacc hfl
  refine BIBase.Entails.trans ?_ (wpt4_at a dq w ws).mpr
  unfold wlat4
  iintro ⟨H0, H1, H2, H3⟩
  isplitr
  · ipureintro; exact hal
  isplitr
  · ipureintro; exact hacc
  isplitl [H0]
  · iapply wpt_at_intro _ dq _ t ws (hfl 0 (by omega)); iexact H0
  isplitl [H1]
  · iapply wpt_at_intro _ dq _ t ws (hfl 1 (by omega)); iexact H1
  isplitl [H2]
  · iapply wpt_at_intro _ dq _ t ws (hfl 2 (by omega)); iexact H2
  · iapply wpt_at_intro _ dq _ t ws (hfl 3 (by omega)); iexact H3

/-- THE STORE RULE FOR THE BUNDLE, owned altitude. -/
theorem wpt4Store (tid : Option Nat) (σ : Wmstate) (ak : AkInfo) (a : PAddr) (w : BitVec 32)
    (v : BitVec (8 * 4)) :
    ak.akLatest = true →
    wlatInterp (GF := GF) σ.wmImg σ.wmLog ⊢
      vwpHold (wpt4 (GF := GF) a (DFrac.own 1) w) σ.wmWs -∗
        |==> (wlatInterp (GF := GF) (wwritePost tid σ ak a 4 v).wmImg
            (wwritePost tid σ ak a 4 v).wmLog ∗
          vwpHold (wpt4 (GF := GF) a (DFrac.own 1) v) (wwritePost tid σ ak a 4 v).wmWs) := by
  intro hlt
  rw [wwritePostImg tid σ ak a 4 v, wwritePostLog tid σ ak a 4 v]
  iintro Hi Hpt
  icases wpt4AtElems a _ w σ.wmWs $$ Hpt with ⟨%hal, %hacc, %t0, %t1, %t2, %t3, H0, H1, H2, H3⟩
  imod wlat4StorePrim tid (wmClassOf ak σ.wmWs) σ a v t0 t1 t2 t3 _ _ _ _
      (by simp [wmClassOf, hlt]) $$ Hi H0 H1 H2 H3 with ⟨Hi, Hl⟩
  imodintro
  iframe Hi
  iapply wlat4Wpt4 a _ (σ.wmLog.length + 1) v _ hal hacc
    (fun j hj => flrWwritePost tid σ ak a 4 v j hj)
  iexact Hl

/-! ### 4c. THE OWNED ALTITUDE -- `wpt4Own` -/

theorem wpt4OwnAtElems (c : CPU) (a : PAddr) (w : BitVec 32) (ws : Wstate) :
    vwpHold (wpt4Own (GF := GF) c a w) ws ⊢
      iprop(⌜is_aligned_paddr (.Physaddr a) 4 = true⌝ ∗ ⌜accWf a 4⌝ ∗
        ∃ t0 t1 t2 t3 : Nat,
          wlatElem (GF := GF) (WeakInterp.accAddr a 0) (DFrac.own 1) t0 (nthByte (n := 4) w 0) ∗
            wownSt (GF := GF) c (WeakInterp.accAddr a 0) ∗
          wlatElem (GF := GF) (WeakInterp.accAddr a 1) (DFrac.own 1) t1 (nthByte (n := 4) w 1) ∗
            wownSt (GF := GF) c (WeakInterp.accAddr a 1) ∗
          wlatElem (GF := GF) (WeakInterp.accAddr a 2) (DFrac.own 1) t2 (nthByte (n := 4) w 2) ∗
            wownSt (GF := GF) c (WeakInterp.accAddr a 2) ∗
          wlatElem (GF := GF) (WeakInterp.accAddr a 3) (DFrac.own 1) t3 (nthByte (n := 4) w 3) ∗
            wownSt (GF := GF) c (WeakInterp.accAddr a 3)) := by
  iintro Hpt
  icases (wpt4Own_at c a w ws).mp $$ Hpt with ⟨%hal, %hacc, H0, H1, H2, H3⟩
  icases (wptOwnH_at c _ _ ws).mp $$ H0 with ⟨%t0, H0, S0, -⟩
  icases (wptOwnH_at c _ _ ws).mp $$ H1 with ⟨%t1, H1, S1, -⟩
  icases (wptOwnH_at c _ _ ws).mp $$ H2 with ⟨%t2, H2, S2, -⟩
  icases (wptOwnH_at c _ _ ws).mp $$ H3 with ⟨%t3, H3, S3, -⟩
  isplitr
  · ipureintro; exact hal
  isplitr
  · ipureintro; exact hacc
  iexists t0, t1, t2, t3
  iframe H0 S0 H1 S1 H2 S2 H3 S3

theorem wlat4OwnWpt4Own (c : CPU) (a : PAddr) (t : Nat) (w : BitVec 32) (ws : Wstate) :
    is_aligned_paddr (.Physaddr a) 4 = true →
    accWf a 4 →
    (∀ j : Nat, j < 4 → t ≤ flr (wsView ws) (WeakInterp.accAddr a j)) →
    wlat4Own (GF := GF) c a t w ⊢ vwpHold (wpt4Own (GF := GF) c a w) ws := by
  intro hal hacc hfl
  refine BIBase.Entails.trans ?_ (wpt4Own_at c a w ws).mpr
  unfold wlat4Own
  iintro ⟨H0, S0, H1, S1, H2, S2, H3, S3⟩
  isplitr
  · ipureintro; exact hal
  isplitr
  · ipureintro; exact hacc
  isplitl [H0 S0]
  · iapply wptOwnH_at_intro c _ _ t ws (hfl 0 (by omega)); iframe H0 S0
  isplitl [H1 S1]
  · iapply wptOwnH_at_intro c _ _ t ws (hfl 1 (by omega)); iframe H1 S1
  isplitl [H2 S2]
  · iapply wptOwnH_at_intro c _ _ t ws (hfl 2 (by omega)); iframe H2 S2
  · iapply wptOwnH_at_intro c _ _ t ws (hfl 3 (by omega)); iframe H3 S3

/-- THE OWNED STORE RULE at the interpreter's own write post-state. -/
theorem wpt4StoreOwn (c : CPU) (σ : Wmstate) (ak : AkInfo) (a : PAddr) (w : BitVec 32)
    (v : BitVec (8 * 4)) :
    wlatInterp (GF := GF) σ.wmImg σ.wmLog ⊢
      vwpHold (wpt4Own (GF := GF) c a w) σ.wmWs -∗
        |==> (wlatInterp (GF := GF) (wwritePost (some c.val) σ ak a 4 v).wmImg
            (wwritePost (some c.val) σ ak a 4 v).wmLog ∗
          vwpHold (wpt4Own (GF := GF) c a v) (wwritePost (some c.val) σ ak a 4 v).wmWs) := by
  rw [wwritePostImg (some c.val) σ ak a 4 v, wwritePostLog (some c.val) σ ak a 4 v]
  iintro Hi Hpt
  icases wpt4OwnAtElems c a w σ.wmWs $$ Hpt with
    ⟨%hal, %hacc, %t0, %t1, %t2, %t3, H0, S0, H1, S1, H2, S2, H3, S3⟩
  imod wlat4StorePrimOwn c (wmClassOf ak σ.wmWs) σ a v t0 t1 t2 t3 _ _ _ _
      $$ Hi H0 S0 H1 S1 H2 S2 H3 S3 with ⟨Hi, Hl⟩
  imodintro
  iframe Hi
  iapply wlat4OwnWpt4Own c a (σ.wmLog.length + 1) v _ hal hacc
    (fun j hj => flrWwritePost (some c.val) σ ak a 4 v j hj)
  iexact Hl

/-- THE OWNED LOAD FACTS: the flat window and its pinnedness. -/
theorem wpt4OwnFlatPin (c : CPU) (σ : Wmstate) (a : PAddr) (w : BitVec 32) :
    wlogWf σ.wmLog →
    wlatInterp (GF := GF) σ.wmImg σ.wmLog ⊢
      vwpHold (wpt4Own (GF := GF) c a w) σ.wmWs -∗
        ⌜accWf a 4 ∧ ∀ j : Nat, j < 4 →
          wflatMem σ.wmImg σ.wmLog (a + BitVec.ofNat 64 j) = some (nthByte (n := 4) w j) ∧
          pinnedRead σ (WeakInterp.accAddr a j)⌝ := by
  intro hwf
  iintro Hi Hpt
  icases (wpt4Own_at c a w σ.wmWs).mp $$ Hpt with ⟨%hal, %hacc, H0, H1, H2, H3⟩
  icases keepPure (wptOwnHByteFlatPin c σ a 4 _ 0 hwf hacc (by omega)) $$ Hi H0 with ⟨%E0, Hi, -⟩
  icases keepPure (wptOwnHByteFlatPin c σ a 4 _ 1 hwf hacc (by omega)) $$ Hi H1 with ⟨%E1, Hi, -⟩
  icases keepPure (wptOwnHByteFlatPin c σ a 4 _ 2 hwf hacc (by omega)) $$ Hi H2 with ⟨%E2, Hi, -⟩
  ihave %E3 := wptOwnHByteFlatPin c σ a 4 _ 3 hwf hacc (by omega) $$ Hi H3
  ipureintro
  refine ⟨hacc, ?_⟩
  intro j hj
  rcases j with _ | _ | _ | _ | j
  · exact E0
  · exact E1
  · exact E2
  · exact E3
  · omega

theorem wpt4OwnFlat (c : CPU) (σ : Wmstate) (a : PAddr) (w : BitVec 32) :
    wlogWf σ.wmLog →
    wlatInterp (GF := GF) σ.wmImg σ.wmLog ⊢
      vwpHold (wpt4Own (GF := GF) c a w) σ.wmWs -∗
        ⌜∀ j : Nat, j < 4 →
          wflatMem σ.wmImg σ.wmLog (a + BitVec.ofNat 64 j) = some (nthByte (n := 4) w j)⌝ := by
  intro hwf
  iintro Hi Hpt
  ihave %h := wpt4OwnFlatPin c σ a w hwf $$ Hi Hpt
  ipureintro
  exact fun j hj => (h.2 j hj).1

theorem wpt4OwnPinned (c : CPU) (σ : Wmstate) (a : PAddr) (w : BitVec 32) :
    wlogWf σ.wmLog →
    wlatInterp (GF := GF) σ.wmImg σ.wmLog ⊢
      vwpHold (wpt4Own (GF := GF) c a w) σ.wmWs -∗
        ⌜∀ j : Nat, j < 4 → pinnedRead σ (WeakInterp.accAddr a j)⌝ := by
  intro hwf
  iintro Hi Hpt
  ihave %h := wpt4OwnFlatPin c σ a w hwf $$ Hi Hpt
  ipureintro
  exact fun j hj => (h.2 j hj).2

/-! ### 4d. THE SYNC ALTITUDE -- `wlat4Sync` -/

def wlat4El (a : PAddr) (dq : DFrac) (t : Nat) (w : BitVec 32) : IProp GF :=
  iprop(wlatElem (GF := GF) (WeakInterp.accAddr a 0) dq t (nthByte (n := 4) w 0) ∗
    wlatElem (GF := GF) (WeakInterp.accAddr a 1) dq t (nthByte (n := 4) w 1) ∗
    wlatElem (GF := GF) (WeakInterp.accAddr a 2) dq t (nthByte (n := 4) w 2) ∗
    wlatElem (GF := GF) (WeakInterp.accAddr a 3) dq t (nthByte (n := 4) w 3))

theorem wlat4ElOfWlat4 (a : PAddr) (dq : DFrac) (t : Nat) (w : BitVec 32) :
    wlat4 (GF := GF) a dq t w ⊢ wlat4El a dq t w := by
  unfold wlat4 wlat4El wlatPointsto
  iintro ⟨⟨H0, -⟩, ⟨H1, -⟩, ⟨H2, -⟩, ⟨H3, -⟩⟩
  iframe H0 H1 H2 H3

def wlat4Sync (a : PAddr) (t : Nat) (w : BitVec 32) : IProp GF :=
  iprop(wlat4El (GF := GF) a (DFrac.own 1) t w ∗ syncWin (GF := GF) a 4)

theorem wlat4SyncWin (a : PAddr) (t : Nat) (w : BitVec 32) :
    wlat4Sync (GF := GF) a t w ⊢ syncWin a 4 := by
  unfold wlat4Sync
  iintro ⟨-, #H⟩
  iexact H

/-- The elementwise reading. -/
theorem wlat4ElLatestVal (img : GMapF PAddr (BitVec 8)) (log : List Wmsg) (a : PAddr) (dq : DFrac)
    (t : Nat) (w : BitVec 32) :
    wlatInterp (GF := GF) img log ⊢
      wlat4El (GF := GF) a dq t w -∗
        ⌜∀ j : Nat, j < 4 →
          latestVal (imgZ img) log (WeakInterp.accAddr a j) t (nthByte (n := 4) w j)⌝ := by
  unfold wlat4El
  iintro Hi ⟨H0, H1, H2, H3⟩
  icases keepPure (wand_intro (wlatLookupElem img log _ dq t _)) $$ Hi H0 with ⟨%E0, Hi, -⟩
  icases keepPure (wand_intro (wlatLookupElem img log _ dq t _)) $$ Hi H1 with ⟨%E1, Hi, -⟩
  icases keepPure (wand_intro (wlatLookupElem img log _ dq t _)) $$ Hi H2 with ⟨%E2, Hi, -⟩
  ihave %E3 := wand_intro (wlatLookupElem img log _ dq t _) $$ Hi H3
  ipureintro
  intro j hj
  rcases j with _ | _ | _ | _ | j
  · exact E0
  · exact E1
  · exact E2
  · exact E3
  · omega

/-- THE MINT.  A word no message has ever written may be turned sync once and for all. -/
theorem wlat4SyncMint (img : GMapF PAddr (BitVec 8)) (log : List Wmsg) (a : PAddr) (t : Nat)
    (w : BitVec 32) :
    (∀ j : Nat, j < 4 → wcdsSync log (WeakInterp.accAddr a j)) →
    wlatInterp (GF := GF) img log ⊢
      wlat4 (GF := GF) a (DFrac.own 1) t w -∗
        |==> (wlatInterp (GF := GF) img log ∗ wlat4Sync (GF := GF) a t w) := by
  intro hsy
  unfold wlat4 wlatPointsto wclean
  iintro Hi ⟨⟨E0, C0⟩, ⟨E1, C1⟩, ⟨E2, C2⟩, ⟨E3, C3⟩⟩
  imod syncMint img log _ _ (hsy 0 (by omega)) $$ [Hi C0] with ⟨Hi, #S0⟩
  · iframe Hi C0
  imod syncMint img log _ _ (hsy 1 (by omega)) $$ [Hi C1] with ⟨Hi, #S1⟩
  · iframe Hi C1
  imod syncMint img log _ _ (hsy 2 (by omega)) $$ [Hi C2] with ⟨Hi, #S2⟩
  · iframe Hi C2
  imod syncMint img log _ _ (hsy 3 (by omega)) $$ [Hi C3] with ⟨Hi, #S3⟩
  · iframe Hi C3
  imodintro
  iframe Hi
  unfold wlat4Sync wlat4El
  isplitl [E0 E1 E2 E3]
  · iframe E0 E1 E2 E3
  · iapply syncWin4 a
    iframe S0 S1 S2 S3

/-- The auth lookup of a sync witness (Lean-only; inlined in Rocq). -/
theorem syncByteLookup (a : Int) (mc : GMapF Int Wcds) :
    ghost_map_auth (GF := GF) (WeakGS.cdsName (GF := GF)) (DFrac.own 1) mc ⊢
      syncByte (GF := GF) a -∗ ⌜get? mc a = some WSync⌝ := by
  unfold syncByte wcdsEl
  iintro Ha Hel
  icombine Ha Hel gives %hlk
  ipureintro
  exact hlk

/-- THE SYNC STORE: the state map is untouched, only the four value elements move. -/
theorem wlat4SyncStorePrim (tid : Option Nat) (k : WmClass) (σ : Wmstate) (a : PAddr)
    (v : BitVec 32) (t : Nat) (w : BitVec 32) :
    k ≠ .WCplain →
    wlatInterp (GF := GF) σ.wmImg σ.wmLog ⊢
      wlat4Sync (GF := GF) a t w -∗
        |==> (wlatInterp (GF := GF) σ.wmImg (σ.wmLog ++ [wwriteMsg tid k a 4 v]) ∗
          wlat4Sync (GF := GF) a (σ.wmLog.length + 1) v) := by
  intro hk
  unfold wlatInterp wlat4Sync wlat4El wlatElem
  iintro ⟨%mm, %mc, Hauth, %hag, Hc, %hagc⟩ ⟨⟨H0, H1, H2, H3⟩, #Hs⟩
  imod ghost_map_update (σ.wmLog.length + 1, nthByte (n := 4) v 0) $$ Hauth H0 with ⟨Hauth, H0⟩
  imod ghost_map_update (σ.wmLog.length + 1, nthByte (n := 4) v 1) $$ Hauth H1 with ⟨Hauth, H1⟩
  imod ghost_map_update (σ.wmLog.length + 1, nthByte (n := 4) v 2) $$ Hauth H2 with ⟨Hauth, H2⟩
  imod ghost_map_update (σ.wmLog.length + 1, nthByte (n := 4) v 3) $$ Hauth H3 with ⟨Hauth, H3⟩
  -- T2-0: the window is pinned SYNC by the persistent witnesses, so it carries no `WLock` byte
  ihave #S0 := syncWinByte a 4 0 (by omega) $$ Hs
  ihave #S1 := syncWinByte a 4 1 (by omega) $$ Hs
  ihave #S2 := syncWinByte a 4 2 (by omega) $$ Hs
  ihave #S3 := syncWinByte a 4 3 (by omega) $$ Hs
  icases keepPure (syncByteLookup _ mc) $$ Hc S0 with ⟨%K0, Hc, -⟩
  icases keepPure (syncByteLookup _ mc) $$ Hc S1 with ⟨%K1, Hc, -⟩
  icases keepPure (syncByteLookup _ mc) $$ Hc S2 with ⟨%K2, Hc, -⟩
  icases keepPure (syncByteLookup _ mc) $$ Hc S3 with ⟨%K3, Hc, -⟩
  imodintro
  isplitl [Hauth Hc]
  · iexists _, mc
    iframe Hauth Hc
    isplit
    · ipureintro
      rw [← wins4Unfold]
      exact wlatAgreeStore4 _ _ tid k a v mm hag
    · ipureintro
      exact wcdsAgreeNonplain4 _ tid k a v mc WSync hk rfl K0 K1 K2 K3 hagc
  · iframe H0 H1 H2 H3 Hs

/-- The FLAT reading of a bare element. -/
theorem wlatElFlatPin (σ : Wmstate) (a : PAddr) (dq : DFrac) (t : Nat) (v : BitVec 8) :
    wlogWf σ.wmLog →
    wlatInterp (GF := GF) σ.wmImg σ.wmLog ⊢
      wlatElem (GF := GF) (paZ a) dq t v -∗
        ⌜wflatMem σ.wmImg σ.wmLog a = some v ∧ latestTs σ.wmLog (paZ a) = t⌝ := by
  intro hwf
  iintro Hi He
  icases keepPure (wlatFlatLookupE σ a dq t v hwf) $$ Hi He with ⟨%hfl, Hi, He⟩
  ihave %hlat := wand_intro (wlatLookupElem σ.wmImg σ.wmLog (paZ a) dq t v) $$ Hi He
  ipureintro
  exact ⟨hfl, latestValTs _ _ _ _ _ hlat⟩

/-- The same at byte `j` of a wrap-free window (Lean-only; Rocq rewrites inline). -/
theorem wlatElByteFlatGen (σ : Wmstate) (a : PAddr) (n : Nat) (dq : DFrac) (t : Nat)
    (b : BitVec 8) (j : Nat) :
    wlogWf σ.wmLog → accWf a n → j < n →
    wlatInterp (GF := GF) σ.wmImg σ.wmLog ⊢
      wlatElem (GF := GF) (WeakInterp.accAddr a j) dq t b -∗
        ⌜wflatMem σ.wmImg σ.wmLog (a + BitVec.ofNat 64 j) = some b ∧
         latestTs σ.wmLog (WeakInterp.accAddr a j) = t⌝ := by
  intro hwf hacc hj
  rw [← accWfByte a n j hacc hj]
  exact wlatElFlatPin σ (a + BitVec.ofNat 64 j) dq t b hwf

theorem wlat4ElFlatGen (σ : Wmstate) (a : PAddr) (dq : DFrac) (t : Nat) (w : BitVec 32) :
    wlogWf σ.wmLog → accWf a 4 →
    wlatInterp (GF := GF) σ.wmImg σ.wmLog ⊢
      wlat4El (GF := GF) a dq t w -∗
        ⌜(∀ j : Nat, j < 4 →
            wflatMem σ.wmImg σ.wmLog (a + BitVec.ofNat 64 j) = some (nthByte (n := 4) w j)) ∧
          (∀ j : Nat, j < 4 → latestTs σ.wmLog (WeakInterp.accAddr a j) = t)⌝ := by
  intro hwf hacc
  unfold wlat4El
  iintro Hi ⟨H0, H1, H2, H3⟩
  icases keepPure (wlatElByteFlatGen σ a 4 dq t _ 0 hwf hacc (by omega)) $$ Hi H0
    with ⟨%E0, Hi, -⟩
  icases keepPure (wlatElByteFlatGen σ a 4 dq t _ 1 hwf hacc (by omega)) $$ Hi H1
    with ⟨%E1, Hi, -⟩
  icases keepPure (wlatElByteFlatGen σ a 4 dq t _ 2 hwf hacc (by omega)) $$ Hi H2
    with ⟨%E2, Hi, -⟩
  ihave %E3 := wlatElByteFlatGen σ a 4 dq t _ 3 hwf hacc (by omega) $$ Hi H3
  ipureintro
  constructor
  · intro j hj
    rcases j with _ | _ | _ | _ | j
    · exact E0.1
    · exact E1.1
    · exact E2.1
    · exact E3.1
    · omega
  · intro j hj
    rcases j with _ | _ | _ | _ | j
    · exact E0.2
    · exact E1.2
    · exact E2.2
    · exact E3.2
    · omega

theorem wlat4SyncFlatGen (σ : Wmstate) (a : PAddr) (t : Nat) (w : BitVec 32) :
    wlogWf σ.wmLog → accWf a 4 →
    wlatInterp (GF := GF) σ.wmImg σ.wmLog ⊢
      wlat4Sync (GF := GF) a t w -∗
        ⌜(∀ j : Nat, j < 4 →
            wflatMem σ.wmImg σ.wmLog (a + BitVec.ofNat 64 j) = some (nthByte (n := 4) w j)) ∧
          (∀ j : Nat, j < 4 → latestTs σ.wmLog (WeakInterp.accAddr a j) = t)⌝ := by
  intro hwf hacc
  unfold wlat4Sync
  iintro Hi ⟨He, -⟩
  iapply wlat4ElFlatGen σ a (DFrac.own 1) t w hwf hacc $$ Hi He

theorem wlat4SyncStoreGen (tid : Option Nat) (k : WmClass) (σ σ' : Wmstate) (a : PAddr) (t : Nat)
    (w v : BitVec 32) :
    k ≠ .WCplain →
    σ'.wmImg = σ.wmImg →
    σ'.wmLog = σ.wmLog ++ [wwriteMsg tid k a 4 v] →
    wlatInterp (GF := GF) σ.wmImg σ.wmLog ⊢
      wlat4Sync (GF := GF) a t w -∗
        |==> (wlatInterp (GF := GF) σ'.wmImg σ'.wmLog ∗
          wlat4Sync (GF := GF) a (σ.wmLog.length + 1) v) := by
  intro hk himg hlog
  rw [himg, hlog]
  exact wlat4SyncStorePrim tid k σ a v t w hk

/-! ### 4d'. THE LOCK ALTITUDE -- `wlat4L` (T2-0) -/

def wlockWin (a : PAddr) (n0 : Nat) (h : Option Nat) : IProp GF :=
  iprop(wlockSt (GF := GF) (WeakInterp.accAddr a 0) (paZ a) n0 h ∗
    wlockSt (GF := GF) (WeakInterp.accAddr a 1) (paZ a) n0 h ∗
    wlockSt (GF := GF) (WeakInterp.accAddr a 2) (paZ a) n0 h ∗
    wlockSt (GF := GF) (WeakInterp.accAddr a 3) (paZ a) n0 h)

def wlat4Lock (a : PAddr) (n0 : Nat) (t : Nat) (w : BitVec 32) (h : Option Nat) : IProp GF :=
  iprop(wlat4El (GF := GF) a (DFrac.own 1) t w ∗ wlockWin (GF := GF) a n0 h)

/-- The bundle `wlock_inv` holds.  `n0` is hidden. -/
def wlat4L (a : PAddr) (t : Nat) (w : BitVec 32) (h : Option Nat) : IProp GF :=
  iprop(∃ n0 : Nat, wlat4Lock (GF := GF) a n0 t w h)

instance wlockWin_timeless (a : PAddr) (n0 : Nat) (h : Option Nat) :
    Timeless (wlockWin (GF := GF) a n0 h) := by
  unfold wlockWin; infer_instance

instance wlat4Lock_timeless (a : PAddr) (n0 t : Nat) (w : BitVec 32) (h : Option Nat) :
    Timeless (wlat4Lock (GF := GF) a n0 t w h) := by
  unfold wlat4Lock wlat4El wlatElem; infer_instance

instance wlat4L_timeless (a : PAddr) (t : Nat) (w : BitVec 32) (h : Option Nat) :
    Timeless (wlat4L (GF := GF) a t w h) := by
  unfold wlat4L; infer_instance

instance wlat4L_objective (a : PAddr) (t : Nat) (w : BitVec 32) (h : Option Nat) :
    Objective (iprop(⎡wlat4L (GF := GF) a t w h⎤) : VProp GF) := by
  infer_instance

theorem wlockWinLookup (a : PAddr) (n0 : Nat) (h : Option Nat) (mc : GMapF Int Wcds) :
    ghost_map_auth (GF := GF) (WeakGS.cdsName (GF := GF)) (DFrac.own 1) mc ⊢
      wlockWin (GF := GF) a n0 h -∗
        ⌜∀ j : Nat, j < 4 → get? mc (WeakInterp.accAddr a j) = some (WLock (paZ a) n0 h)⌝ := by
  unfold wlockWin
  iintro Ha ⟨S0, S1, S2, S3⟩
  icases keepPure (wand_intro (wlockStLookup _ _ n0 h mc)) $$ Ha S0 with ⟨%K0, Ha, -⟩
  icases keepPure (wand_intro (wlockStLookup _ _ n0 h mc)) $$ Ha S1 with ⟨%K1, Ha, -⟩
  icases keepPure (wand_intro (wlockStLookup _ _ n0 h mc)) $$ Ha S2 with ⟨%K2, Ha, -⟩
  ihave %K3 := wand_intro (wlockStLookup _ _ n0 h mc) $$ Ha S3
  ipureintro
  intro j hj
  rcases j with _ | _ | _ | _ | j
  · exact K0
  · exact K1
  · exact K2
  · exact K3
  · omega

/-- THE FOUR-BYTE STATE UPDATE the protocol store performs. -/
theorem wcdsIns4In (a : PAddr) (base : Int) (n0 : Nat) (h : Option Nat) (mc : GMapF Int Wcds)
    (z : Int) :
    z ∈ [WeakInterp.accAddr a 0, WeakInterp.accAddr a 1, WeakInterp.accAddr a 2,
      WeakInterp.accAddr a 3] →
    get? (insert (insert (insert (insert mc (WeakInterp.accAddr a 0) (WLock base n0 h))
      (WeakInterp.accAddr a 1) (WLock base n0 h)) (WeakInterp.accAddr a 2) (WLock base n0 h))
      (WeakInterp.accAddr a 3) (WLock base n0 h)) z = some (WLock base n0 h) := by
  intro hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl
  · rw [lookupInsertNe (by unfold WeakInterp.accAddr; omega),
      lookupInsertNe (by unfold WeakInterp.accAddr; omega),
      lookupInsertNe (by unfold WeakInterp.accAddr; omega)]
    exact lookupInsert
  · rw [lookupInsertNe (by unfold WeakInterp.accAddr; omega),
      lookupInsertNe (by unfold WeakInterp.accAddr; omega)]
    exact lookupInsert
  · rw [lookupInsertNe (by unfold WeakInterp.accAddr; omega)]
    exact lookupInsert
  · exact lookupInsert

theorem wcdsIns4Out (a : PAddr) (base : Int) (n0 : Nat) (h : Option Nat) (mc : GMapF Int Wcds)
    (z : Int) :
    z ∉ [WeakInterp.accAddr a 0, WeakInterp.accAddr a 1, WeakInterp.accAddr a 2,
      WeakInterp.accAddr a 3] →
    get? (insert (insert (insert (insert mc (WeakInterp.accAddr a 0) (WLock base n0 h))
      (WeakInterp.accAddr a 1) (WLock base n0 h)) (WeakInterp.accAddr a 2) (WLock base n0 h))
      (WeakInterp.accAddr a 3) (WLock base n0 h)) z = get? mc z := by
  intro hz
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hz
  obtain ⟨h0, h1, h2, h3⟩ := hz
  rw [lookupInsertNe (Ne.symm h3), lookupInsertNe (Ne.symm h2), lookupInsertNe (Ne.symm h1),
    lookupInsertNe (Ne.symm h0)]

/-- THE REGISTRATION MINT: an ordinary (clean) four-byte element bundle becomes the lock word's
bundle, registered at the CURRENT log length. -/
theorem wlat4LockMint (img : GMapF PAddr (BitVec 8)) (log : List Wmsg) (a : PAddr) (t : Nat)
    (w : BitVec 32) :
    wlatInterp (GF := GF) img log ⊢
      wlat4 (GF := GF) a (DFrac.own 1) t w -∗
        |==> (wlatInterp (GF := GF) img log ∗ wlat4Lock (GF := GF) a log.length t w none) := by
  unfold wlat4 wlatPointsto
  iintro Hi ⟨⟨E0, C0⟩, ⟨E1, C1⟩, ⟨E2, C2⟩, ⟨E3, C3⟩⟩
  imod wlockRegister img log (WeakInterp.accAddr a 0) (paZ a)
      (by unfold WeakInterp.accAddr; omega) $$ [Hi C0] with ⟨Hi, L0⟩
  · iframe Hi C0
  imod wlockRegister img log (WeakInterp.accAddr a 1) (paZ a)
      (by unfold WeakInterp.accAddr; omega) $$ [Hi C1] with ⟨Hi, L1⟩
  · iframe Hi C1
  imod wlockRegister img log (WeakInterp.accAddr a 2) (paZ a)
      (by unfold WeakInterp.accAddr; omega) $$ [Hi C2] with ⟨Hi, L2⟩
  · iframe Hi C2
  imod wlockRegister img log (WeakInterp.accAddr a 3) (paZ a)
      (by unfold WeakInterp.accAddr; omega) $$ [Hi C3] with ⟨Hi, L3⟩
  · iframe Hi C3
  imodintro
  iframe Hi
  unfold wlat4Lock wlat4El wlockWin
  iframe E0 E1 E2 E3 L0 L1 L2 L3

/-- ... and the `n0`-HIDING form the ordinary lock invariant holds. -/
theorem wlat4LMint (img : GMapF PAddr (BitVec 8)) (log : List Wmsg) (a : PAddr) (t : Nat)
    (w : BitVec 32) :
    wlatInterp (GF := GF) img log ⊢
      wlat4 (GF := GF) a (DFrac.own 1) t w -∗
        |==> (wlatInterp (GF := GF) img log ∗ wlat4L (GF := GF) a t w none) := by
  iintro Hi Hw
  imod wlat4LockMint img log a t w $$ Hi Hw with ⟨Hi, Hw⟩
  imodintro
  iframe Hi
  unfold wlat4L
  iexists log.length
  iexact Hw

/-- THE PROTOCOL STORE.  The four value elements move, and the four lock bytes move to the new
holder; the price is the shape premise. -/
theorem wlat4LockStorePrim (tid : Option Nat) (k : WmClass) (σ : Wmstate) (a : PAddr)
    (v : BitVec 32) (n0 t : Nat) (w : BitVec 32) (h h' : Option Nat) :
    wlockShaped (wwriteMsg tid k a 4 v) →
    altStep h (wwriteMsg tid k a 4 v) = some h' →
    wlatInterp (GF := GF) σ.wmImg σ.wmLog ⊢
      wlat4Lock (GF := GF) a n0 t w h -∗
        |==> (wlatInterp (GF := GF) σ.wmImg (σ.wmLog ++ [wwriteMsg tid k a 4 v]) ∗
          wlat4Lock (GF := GF) a n0 (σ.wmLog.length + 1) v h') := by
  intro hsh hst
  unfold wlatInterp wlat4Lock wlat4El wlatElem wlockWin wlockSt wcdsEl
  iintro ⟨%mm, %mc, Hauth, %hag, Hc, %hagc⟩ ⟨⟨H0, H1, H2, H3⟩, ⟨S0, S1, S2, S3⟩⟩
  imod ghost_map_update (σ.wmLog.length + 1, nthByte (n := 4) v 0) $$ Hauth H0 with ⟨Hauth, H0⟩
  imod ghost_map_update (σ.wmLog.length + 1, nthByte (n := 4) v 1) $$ Hauth H1 with ⟨Hauth, H1⟩
  imod ghost_map_update (σ.wmLog.length + 1, nthByte (n := 4) v 2) $$ Hauth H2 with ⟨Hauth, H2⟩
  imod ghost_map_update (σ.wmLog.length + 1, nthByte (n := 4) v 3) $$ Hauth H3 with ⟨Hauth, H3⟩
  icombine Hc S0 gives %K0
  icombine Hc S1 gives %K1
  icombine Hc S2 gives %K2
  icombine Hc S3 gives %K3
  -- the four lock bytes move to the new holder
  imod ghost_map_update (WLock (paZ a) n0 h') $$ Hc S0 with ⟨Hc, S0⟩
  imod ghost_map_update (WLock (paZ a) n0 h') $$ Hc S1 with ⟨Hc, S1⟩
  imod ghost_map_update (WLock (paZ a) n0 h') $$ Hc S2 with ⟨Hc, S2⟩
  imod ghost_map_update (WLock (paZ a) n0 h') $$ Hc S3 with ⟨Hc, S3⟩
  imodintro
  isplitl [Hauth Hc]
  · iexists _, _
    iframe Hauth Hc
    isplit
    · ipureintro
      rw [← wins4Unfold]
      exact wlatAgreeStore4 _ _ tid k a v mm hag
    · ipureintro
      refine wcdsAgreeStoreLock _ _ mc _
        [WeakInterp.accAddr a 0, WeakInterp.accAddr a 1, WeakInterp.accAddr a 2,
          WeakInterp.accAddr a 3] (paZ a) n0 h h' rfl hsh hst (wwriteMsgZs4 _ _ a v) ?_
        (fun z hz => wcdsIns4In a (paZ a) n0 h' mc z hz)
        (fun z hz => wcdsIns4Out a (paZ a) n0 h' mc z hz) hagc
      intro z hz
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
      rcases hz with rfl | rfl | rfl | rfl
      · exact K0
      · exact K1
      · exact K2
      · exact K3
  · iframe H0 H1 H2 H3 S0 S1 S2 S3

theorem wlat4LStorePrim (tid : Option Nat) (k : WmClass) (σ : Wmstate) (a : PAddr)
    (v : BitVec 32) (t : Nat) (w : BitVec 32) (h h' : Option Nat) :
    wlockShaped (wwriteMsg tid k a 4 v) →
    altStep h (wwriteMsg tid k a 4 v) = some h' →
    wlatInterp (GF := GF) σ.wmImg σ.wmLog ⊢
      wlat4L (GF := GF) a t w h -∗
        |==> (wlatInterp (GF := GF) σ.wmImg (σ.wmLog ++ [wwriteMsg tid k a 4 v]) ∗
          wlat4L (GF := GF) a (σ.wmLog.length + 1) v h') := by
  intro hsh hst
  unfold wlat4L
  iintro Hi ⟨%n0, Hw⟩
  imod wlat4LockStorePrim tid k σ a v n0 t w h h' hsh hst $$ Hi Hw with ⟨Hi, Hw⟩
  imodintro
  iframe Hi
  iexists n0
  iexact Hw

/-- ... at an explicitly described post-state. -/
theorem wlat4LStoreGen (tid : Option Nat) (k : WmClass) (σ σ' : Wmstate) (a : PAddr) (t : Nat)
    (w v : BitVec 32) (h h' : Option Nat) :
    wlockShaped (wwriteMsg tid k a 4 v) →
    altStep h (wwriteMsg tid k a 4 v) = some h' →
    σ'.wmImg = σ.wmImg →
    σ'.wmLog = σ.wmLog ++ [wwriteMsg tid k a 4 v] →
    wlatInterp (GF := GF) σ.wmImg σ.wmLog ⊢
      wlat4L (GF := GF) a t w h -∗
        |==> (wlatInterp (GF := GF) σ'.wmImg σ'.wmLog ∗
          wlat4L (GF := GF) a (σ.wmLog.length + 1) v h') := by
  intro hsh hst himg hlog
  rw [himg, hlog]
  exact wlat4LStorePrim tid k σ a v t w h h' hsh hst

/-- THE `n0`-EXPOSED TWINS (T2-0′ / F3″). -/
theorem wlat4LockStoreGen (tid : Option Nat) (k : WmClass) (σ σ' : Wmstate) (a : PAddr)
    (n0 t : Nat) (w v : BitVec 32) (h h' : Option Nat) :
    wlockShaped (wwriteMsg tid k a 4 v) →
    altStep h (wwriteMsg tid k a 4 v) = some h' →
    σ'.wmImg = σ.wmImg →
    σ'.wmLog = σ.wmLog ++ [wwriteMsg tid k a 4 v] →
    wlatInterp (GF := GF) σ.wmImg σ.wmLog ⊢
      wlat4Lock (GF := GF) a n0 t w h -∗
        |==> (wlatInterp (GF := GF) σ'.wmImg σ'.wmLog ∗
          wlat4Lock (GF := GF) a n0 (σ.wmLog.length + 1) v h') := by
  intro hsh hst himg hlog
  rw [himg, hlog]
  exact wlat4LockStorePrim tid k σ a v n0 t w h h' hsh hst

theorem wlat4LockFlatGen (σ : Wmstate) (a : PAddr) (n0 t : Nat) (w : BitVec 32) (h : Option Nat) :
    wlogWf σ.wmLog → accWf a 4 →
    wlatInterp (GF := GF) σ.wmImg σ.wmLog ⊢
      wlat4Lock (GF := GF) a n0 t w h -∗
        ⌜(∀ j : Nat, j < 4 →
            wflatMem σ.wmImg σ.wmLog (a + BitVec.ofNat 64 j) = some (nthByte (n := 4) w j)) ∧
          (∀ j : Nat, j < 4 → latestTs σ.wmLog (WeakInterp.accAddr a j) = t)⌝ := by
  intro hwf hacc
  unfold wlat4Lock
  iintro Hi ⟨He, -⟩
  iapply wlat4ElFlatGen σ a (DFrac.own 1) t w hwf hacc $$ Hi He

/-- The FLAT reading over the lock bundle -- what the acquire's spin test branches on. -/
theorem wlat4LFlatGen (σ : Wmstate) (a : PAddr) (t : Nat) (w : BitVec 32) (h : Option Nat) :
    wlogWf σ.wmLog → accWf a 4 →
    wlatInterp (GF := GF) σ.wmImg σ.wmLog ⊢
      wlat4L (GF := GF) a t w h -∗
        ⌜(∀ j : Nat, j < 4 →
            wflatMem σ.wmImg σ.wmLog (a + BitVec.ofNat 64 j) = some (nthByte (n := 4) w j)) ∧
          (∀ j : Nat, j < 4 → latestTs σ.wmLog (WeakInterp.accAddr a j) = t)⌝ := by
  intro hwf hacc
  unfold wlat4L wlat4Lock
  iintro Hi ⟨%n0, He, -⟩
  iapply wlat4ElFlatGen σ a (DFrac.own 1) t w hwf hacc $$ Hi He

/-- THE EXPORT AT THE BUNDLE ALTITUDE (T2-0's deliverable): the lock word's whole VALUE
PROTOCOL, per byte. -/
theorem wlpAtWlat4L (img : GMapF PAddr (BitVec 8)) (log : List Wmsg) (a : PAddr) (t : Nat)
    (w : BitVec 32) (h : Option Nat) :
    wlatInterp (GF := GF) img log ⊢
      wlat4L (GF := GF) a t w h -∗
        ⌜∃ n0 : Nat, ∀ j : Nat, j < 4 → wlpAt log (WeakInterp.accAddr a j) (paZ a) n0⌝ := by
  unfold wlat4L wlat4Lock wlockWin
  iintro Hi ⟨%n0, -, S0, S1, S2, S3⟩
  icases keepPure (wand_intro (wlpAtOfLock img log _ _ n0 h)) $$ Hi S0 with ⟨%P0, Hi, -⟩
  icases keepPure (wand_intro (wlpAtOfLock img log _ _ n0 h)) $$ Hi S1 with ⟨%P1, Hi, -⟩
  icases keepPure (wand_intro (wlpAtOfLock img log _ _ n0 h)) $$ Hi S2 with ⟨%P2, Hi, -⟩
  ihave %P3 := wand_intro (wlpAtOfLock img log _ _ n0 h) $$ Hi S3
  ipureintro
  refine ⟨n0, ?_⟩
  intro j hj
  rcases j with _ | _ | _ | _ | j
  · exact P0
  · exact P1
  · exact P2
  · exact P3
  · omega

/-- ... and T2-0′'s deliverable: the ALTERNATION, per byte, at the SAME registration point and
the SAME holder. -/
theorem wlpAltWlat4L (img : GMapF PAddr (BitVec 8)) (log : List Wmsg) (a : PAddr) (t : Nat)
    (w : BitVec 32) (h : Option Nat) :
    wlatInterp (GF := GF) img log ⊢
      wlat4L (GF := GF) a t w h -∗
        ⌜∃ n0 : Nat, ∀ j : Nat, j < 4 →
          wlpAt log (WeakInterp.accAddr a j) (paZ a) n0 ∧
          wlpAlt log (WeakInterp.accAddr a j) n0 h⌝ := by
  unfold wlat4L wlat4Lock wlockWin
  iintro Hi ⟨%n0, -, S0, S1, S2, S3⟩
  icases keepPure (wand_intro (wlpAtOfLock img log _ _ n0 h)) $$ Hi S0 with ⟨%P0, Hi, S0⟩
  icases keepPure (wand_intro (wlpAtOfLock img log _ _ n0 h)) $$ Hi S1 with ⟨%P1, Hi, S1⟩
  icases keepPure (wand_intro (wlpAtOfLock img log _ _ n0 h)) $$ Hi S2 with ⟨%P2, Hi, S2⟩
  icases keepPure (wand_intro (wlpAtOfLock img log _ _ n0 h)) $$ Hi S3 with ⟨%P3, Hi, S3⟩
  icases keepPure (wand_intro (wlpAltOfLock img log _ _ n0 h)) $$ Hi S0 with ⟨%A0, Hi, -⟩
  icases keepPure (wand_intro (wlpAltOfLock img log _ _ n0 h)) $$ Hi S1 with ⟨%A1, Hi, -⟩
  icases keepPure (wand_intro (wlpAltOfLock img log _ _ n0 h)) $$ Hi S2 with ⟨%A2, Hi, -⟩
  ihave %A3 := wand_intro (wlpAltOfLock img log _ _ n0 h) $$ Hi S3
  ipureintro
  refine ⟨n0, ?_⟩
  intro j hj
  rcases j with _ | _ | _ | _ | j
  · exact ⟨P0, A0⟩
  · exact ⟨P1, A1⟩
  · exact ⟨P2, A2⟩
  · exact ⟨P3, A3⟩
  · omega

/-! ### 4e. THE φ EXPORTERS (φ-upgrade, deliverable C) -/

theorem nvOkWpt4 (c : CPU) (img : GMapF PAddr (BitVec 8)) (log : List Wmsg) (a : PAddr)
    (dq : DFrac) (w : BitVec 32) (ws : Wstate) :
    wlatInterp (GF := GF) img log ⊢
      vwpHold (wpt4 (GF := GF) a dq w) ws -∗
        ⌜∀ j : Nat, j < 4 → nvOk log c (WeakInterp.accAddr a j)⌝ := by
  iintro Hi Hpt
  icases wpt4AtElems a dq w ws $$ Hpt with ⟨-, -, %t0, %t1, %t2, %t3, H0, H1, H2, H3⟩
  icases keepPure (wand_intro (nvOkOfPointsto img log c _ dq _ _)) $$ Hi H0 with ⟨%E0, Hi, -⟩
  icases keepPure (wand_intro (nvOkOfPointsto img log c _ dq _ _)) $$ Hi H1 with ⟨%E1, Hi, -⟩
  icases keepPure (wand_intro (nvOkOfPointsto img log c _ dq _ _)) $$ Hi H2 with ⟨%E2, Hi, -⟩
  ihave %E3 := wand_intro (nvOkOfPointsto img log c _ dq _ _) $$ Hi H3
  ipureintro
  intro j hj
  rcases j with _ | _ | _ | _ | j
  · exact E0
  · exact E1
  · exact E2
  · exact E3
  · omega

theorem nvOkWlat4Own (c : CPU) (img : GMapF PAddr (BitVec 8)) (log : List Wmsg) (a : PAddr)
    (t : Nat) (w : BitVec 32) :
    wlatInterp (GF := GF) img log ⊢
      wlat4Own (GF := GF) c a t w -∗
        ⌜∀ j : Nat, j < 4 → nvOk log c (WeakInterp.accAddr a j)⌝ := by
  unfold wlat4Own
  iintro Hi ⟨-, S0, -, S1, -, S2, -, S3⟩
  icases keepPure (wand_intro (nvOkOfOwnSt img log c _)) $$ Hi S0 with ⟨%E0, Hi, -⟩
  icases keepPure (wand_intro (nvOkOfOwnSt img log c _)) $$ Hi S1 with ⟨%E1, Hi, -⟩
  icases keepPure (wand_intro (nvOkOfOwnSt img log c _)) $$ Hi S2 with ⟨%E2, Hi, -⟩
  ihave %E3 := wand_intro (nvOkOfOwnSt img log c _) $$ Hi S3
  ipureintro
  intro j hj
  rcases j with _ | _ | _ | _ | j
  · exact E0
  · exact E1
  · exact E2
  · exact E3
  · omega

theorem nvOkWlat4 (c : CPU) (img : GMapF PAddr (BitVec 8)) (log : List Wmsg) (a : PAddr)
    (dq : DFrac) (t : Nat) (w : BitVec 32) :
    wlatInterp (GF := GF) img log ⊢
      wlat4 (GF := GF) a dq t w -∗
        ⌜∀ j : Nat, j < 4 → nvOk log c (WeakInterp.accAddr a j)⌝ := by
  unfold wlat4
  iintro Hi ⟨H0, H1, H2, H3⟩
  icases keepPure (wand_intro (nvOkOfPointsto img log c _ dq _ _)) $$ Hi H0 with ⟨%E0, Hi, -⟩
  icases keepPure (wand_intro (nvOkOfPointsto img log c _ dq _ _)) $$ Hi H1 with ⟨%E1, Hi, -⟩
  icases keepPure (wand_intro (nvOkOfPointsto img log c _ dq _ _)) $$ Hi H2 with ⟨%E2, Hi, -⟩
  ihave %E3 := wand_intro (nvOkOfPointsto img log c _ dq _ _) $$ Hi H3
  ipureintro
  intro j hj
  rcases j with _ | _ | _ | _ | j
  · exact E0
  · exact E1
  · exact E2
  · exact E3
  · omega

/-- The lock bundle's φ payment (T2-0), through the `WLock` arm. -/
theorem nvOkWlat4L (c : CPU) (img : GMapF PAddr (BitVec 8)) (log : List Wmsg) (a : PAddr)
    (t : Nat) (w : BitVec 32) (h : Option Nat) :
    wlatInterp (GF := GF) img log ⊢
      wlat4L (GF := GF) a t w h -∗
        ⌜∀ j : Nat, j < 4 → nvOk log c (WeakInterp.accAddr a j)⌝ := by
  unfold wlat4L wlat4Lock wlockWin
  iintro Hi ⟨%n0, -, S0, S1, S2, S3⟩
  icases keepPure (wand_intro (nvOkOfLock img log c _ _ n0 h)) $$ Hi S0 with ⟨%E0, Hi, -⟩
  icases keepPure (wand_intro (nvOkOfLock img log c _ _ n0 h)) $$ Hi S1 with ⟨%E1, Hi, -⟩
  icases keepPure (wand_intro (nvOkOfLock img log c _ _ n0 h)) $$ Hi S2 with ⟨%E2, Hi, -⟩
  ihave %E3 := wand_intro (nvOkOfLock img log c _ _ n0 h) $$ Hi S3
  ipureintro
  intro j hj
  rcases j with _ | _ | _ | _ | j
  · exact E0
  · exact E1
  · exact E2
  · exact E3
  · omega

theorem nvOkWlat4Sync (c : CPU) (img : GMapF PAddr (BitVec 8)) (log : List Wmsg) (a : PAddr)
    (t : Nat) (w : BitVec 32) :
    wlatInterp (GF := GF) img log ⊢
      wlat4Sync (GF := GF) a t w -∗
        ⌜∀ j : Nat, j < 4 → nvOk log c (WeakInterp.accAddr a j)⌝ := by
  unfold wlat4Sync
  iintro Hi ⟨-, #Hs⟩
  ihave #S0 := syncWinByte a 4 0 (by omega) $$ Hs
  ihave #S1 := syncWinByte a 4 1 (by omega) $$ Hs
  ihave #S2 := syncWinByte a 4 2 (by omega) $$ Hs
  ihave #S3 := syncWinByte a 4 3 (by omega) $$ Hs
  icases keepPure (wand_intro (nvOkOfSync img log c _)) $$ Hi S0 with ⟨%E0, Hi, -⟩
  icases keepPure (wand_intro (nvOkOfSync img log c _)) $$ Hi S1 with ⟨%E1, Hi, -⟩
  icases keepPure (wand_intro (nvOkOfSync img log c _)) $$ Hi S2 with ⟨%E2, Hi, -⟩
  ihave %E3 := wand_intro (nvOkOfSync img log c _) $$ Hi S3
  ipureintro
  intro j hj
  rcases j with _ | _ | _ | _ | j
  · exact E0
  · exact E1
  · exact E2
  · exact E3
  · omega

end store

end Weak
