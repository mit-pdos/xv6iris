/-
Weak: **the `wPub` bridge** (φ-upgrade, deliverable B): the machine fact tying the LOG reading of
publication (`wpublished`, `wpubUpto`) to the author's `wPub` watermark, and the three preservation
steps that make the premise `wpubCovers` a machine invariant.

Rocq: `iris/WeakViolation.v` @ xxvzwolszwmp (1cc222280).

The Rocq header, in substance.  STATEMENT ALIGNMENT with `WeakRobust.violation` (checked by hand;
this file deliberately does NOT import Layer 1): the violation-freedom predicate `noViolation`
(now in `Weak/WeakGhost.lean`) is the negation of `violation` with `cls m = SCowned ↦ wmAk m =
WCplain`, `pub c (p+1) ↦ wpublished log (wmTid m) p` (since the publication alignment L0(c),
2026-08-12, `pub_of` IS `wpublished`), `obs_flr ↦ coh`, agents ↦ `CPU`s.  The one remaining gap
is the agent quantifier (only HART authors are constrained; the disk, `wmTid = some n_disk`, is
exempt), matched by Layer 1's `bad` conjunct `e1.1 < nh`.  §§1–3 of the Rocq file (the predicate,
its induction algebra, the C/D/S discharge arms) MOVED INTO `WeakGhost`; what is left is §4, the
`wPub` bridge, which nothing in the tower consumes today (kept as the honest MACHINE statement
"the author's watermark has caught up with every `WCrel` message of its own in the log", for any
future spec that talks about `wPub` directly).

THE ONE CAVEAT (Rocq, verbatim in substance): a ZERO-WIDTH release-class write appends a `WCrel`
message while raising nothing (`storePostRun` folds per byte), so the store step carries
`0 < n` explicitly.

**Deviations from Rocq.**

1. NAMES: as `Weak/WeakMem.lean` deviation 1 (lowerCamelCase; `w_pub` ↦ `wPub`).  The two
   Rocq names also defined in `WeakRobustMain` (`w_pub_foldl_load`, `w_pub_load_post_bytes`,
   `notes/weak-port-dupnames.json`) are file-qualified: `WeakViolation.wPubFoldlLoad`,
   `WeakViolation.wPubLoadPostBytes`.
2. VOCABULARY: `l !! q` ↦ `l[q]?`, `S q` ↦ `q + 1`, `agent` ↦ `Nat`, `fin_to_nat c` ↦ `c.val`
   (`CPU = Fin NCPU`, `MachCSL/TsoMem.lean`), `N.to_nat n` ↦ `n` (widths are `Nat`,
   `WeakInterp` deviation 7), `bv (8 * n)` ↦ `BitVec (8 * n)`, `m ∈ ms` ↦ list membership.
3. `wpubCoversRead`: the Rocq proof splits on `ak_coh`; in Lean that field is `akIfetch`
   (O2, `WeakInterp` deviation 1).  The statement is unchanged (`wreadPost` is still the identity
   on that arm and a `loadPostRun` otherwise).
4. Lean's `storePostRun` / `loadPostRun` wrap a `ctrlPost` (the W-TV bank join) whose `wPub` is
   `rfl`-transparent, so the run-level lemmas reduce to the byte-level ones as in Rocq.

**Name map (Rocq → Lean).**
`wpub_covers`→`wpubCovers`, `wpublished_w_pub`→`wpublishedWPub`,
`wpub_upto_w_pub`→`wpubUptoWPub`, `wpublished_w_pub_cpu`→`wpublishedWPubCpu`,
`wpub_covers_nil`→`wpubCoversNil`, `wpub_covers_mono`→`wpubCoversMono`,
`wpub_covers_app_foreign`→`wpubCoversAppForeign`, `w_pub_load_post_at`→`wPubLoadPostAt`,
`w_pub_foldl_load`→`WeakViolation.wPubFoldlLoad`,
`w_pub_load_post_bytes`→`WeakViolation.wPubLoadPostBytes`, `wpub_covers_read`→`wpubCoversRead`,
`wpub_covers_bar`→`wpubCoversBar`, `w_pub_store_post`→`wPubStorePost`,
`w_pub_store_post_raise`→`wPubStorePostRaise`, `w_pub_foldl_store_mono`→`wPubFoldlStoreMono`,
`w_pub_store_post_bytes_mono`→`wPubStorePostBytesMono`,
`w_pub_store_post_bytes_raise`→`wPubStorePostBytesRaise`,
`w_pub_store_post_run_raise`→`wPubStorePostRunRaise`,
`w_pub_store_post_run_mono`→`wPubStorePostRunMono`, `wpub_covers_write`→`wpubCoversWrite`.

**Dropped lemmas.** None (20 Rocq declarations, 20 Lean declarations).
-/
import Weak.WeakGhost

namespace Weak

open MachCSL MachCSL.Stdpp
open LeanRV64D

/-! ## 4. The `wPub` bridge -/

/-- The author's watermark has caught up with every `WCrel` message of agent `i` in `log`. -/
def wpubCovers (log : List Wmsg) (i : Nat) (ws : Wstate) : Prop :=
  ∀ (q : Nat) (mq : Wmsg),
    log[q]? = some mq → mq.wmTid = some i → mq.wmAk = .WCrel → q + 1 ≤ ws.wPub

/-- THE BRIDGE. -/
theorem wpublishedWPub (log : List Wmsg) (i : Nat) (ws : Wstate) (p : Nat) :
    wpubCovers log i ws → wpublished log (some i) p → p + 1 ≤ ws.wPub := by
  rintro hcov ⟨q, mq, hle, hq, ht, hk⟩
  have := hcov q mq hq ht hk
  omega

/-- The same bridge for the publication-floor token (`WeakGhost.wpubUpto`). -/
theorem wpubUptoWPub (log : List Wmsg) (i : Nat) (ws : Wstate) (n : Nat) :
    wpubCovers log i ws → wpubUpto log (some i) n → n ≤ ws.wPub := by
  rintro hcov ⟨q, mq, hle, hq, ht, hk⟩
  have := hcov q mq hq ht hk
  omega

/-- The φ-export shape, at the hart index the state interpretation uses. -/
theorem wpublishedWPubCpu (log : List Wmsg) (c : CPU) (ws : Wstate) (p : Nat) :
    wpubCovers log c.val ws → wpublished log (some c.val) p → p + 1 ≤ ws.wPub :=
  wpublishedWPub log c.val ws p

/-! ### 4b. `wpubCovers` IS an invariant — the three preservation steps -/

theorem wpubCoversNil (i : Nat) (ws : Wstate) : wpubCovers [] i ws := by
  intro q mq hq; simp at hq

theorem wpubCoversMono (log : List Wmsg) (i : Nat) (ws ws' : Wstate) :
    wpubCovers log i ws → ws.wPub ≤ ws'.wPub → wpubCovers log i ws' := by
  intro h hle q mq hq ht hk
  have := h q mq hq ht hk
  omega

/-- A FOREIGN append adds no obligation to this agent's watermark. -/
theorem wpubCoversAppForeign (log ms : List Wmsg) (i : Nat) (ws : Wstate) :
    wpubCovers log i ws → (∀ m, m ∈ ms → m.wmTid ≠ some i) → wpubCovers (log ++ ms) i ws := by
  intro h hfor q mq hq ht hk
  rcases lookup_app_Some.1 hq with hq | ⟨_, hq⟩
  · exact h q mq hq ht hk
  · exact absurd ht (hfor mq (elem_of_list_lookup_2 hq))

/-- A READ moves neither the log nor `wPub`. -/
theorem wPubLoadPostAt (ws : Wstate) (aq : Bool) (vpre : Nat) (a : Int) (t : Nat) :
    (loadPostAt ws aq vpre a t).wPub = ws.wPub := rfl

theorem WeakViolation.wPubFoldlLoad (aq : Bool) (v : Nat) (ats : List (Int × Nat)) :
    ∀ w : Wstate, (ats.foldl (fun w at_ => loadPostAt w aq v at_.1 at_.2) w).wPub = w.wPub := by
  induction ats with
  | nil => intro w; rfl
  | cons at_ ats ih => intro w; simp only [List.foldl_cons]; rw [ih]; rfl

theorem WeakViolation.wPubLoadPostBytes (ws : Wstate) (aq : Bool) (ats : List (Int × Nat)) :
    (loadPostBytes ws aq ats).wPub = ws.wPub :=
  WeakViolation.wPubFoldlLoad aq _ ats ws

theorem wpubCoversRead (s : Wmstate) (i : Nat) (ak : AkInfo) (pa : PAddr) (ts : List Nat) :
    wpubCovers s.wmLog i s.wmWs →
    wpubCovers (wreadPost s ak pa ts).wmLog i (wreadPost s ak pa ts).wmWs := by
  intro h
  rw [wreadPostLog]
  refine wpubCoversMono _ _ _ _ h ?_
  unfold wreadPost
  split
  · exact Nat.le_refl _
  · simp only [wsetWs, loadPostRun, ctrlPostPub, WeakViolation.wPubLoadPostBytes]
    exact Nat.le_refl _

/-- A BARRIER moves neither. -/
theorem wpubCoversBar (log : List Wmsg) (i : Nat) (ws : Wstate) (b : barrier_kind) :
    wpubCovers log i ws → wpubCovers log i (barrierPost ws b) := by
  intro h
  refine wpubCoversMono _ _ _ _ h ?_
  cases b <;> exact Nat.le_refl _

/-- THE STORE STEP: a `WCrel` message's class is exactly `storePost`'s raise condition. -/
theorem wPubStorePost (ws : Wstate) (rl : Bool) (a : Int) (t : Nat) :
    ws.wPub ≤ (storePost ws rl a t).wPub := by
  simp only [storePost]
  split <;> omega

theorem wPubStorePostRaise (ws : Wstate) (rl : Bool) (a : Int) (t : Nat) :
    (ws.wRelp || rl) = true → t ≤ (storePost ws rl a t).wPub := by
  intro hr
  simp only [storePost, hr, ↓reduceIte]
  omega

theorem wPubFoldlStoreMono (rl : Bool) (as_ : List Int) (t : Nat) :
    ∀ w : Wstate, w.wPub ≤ (as_.foldl (fun w a => storePost w rl a t) w).wPub := by
  induction as_ with
  | nil => intro w; exact Nat.le_refl _
  | cons a as_ ih =>
    intro w
    simp only [List.foldl_cons]
    exact Nat.le_trans (wPubStorePost w rl a t) (ih _)

theorem wPubStorePostBytesMono (ws : Wstate) (rl : Bool) (as_ : List Int) (t : Nat) :
    ws.wPub ≤ (storePostBytes ws rl as_ t).wPub :=
  wPubFoldlStoreMono rl as_ t ws

theorem wPubStorePostBytesRaise (ws : Wstate) (rl : Bool) (as_ : List Int) (t : Nat)
    (a0 : Int) (as0 : List Int) :
    as_ = a0 :: as0 → (ws.wRelp || rl) = true → t ≤ (storePostBytes ws rl as_ t).wPub := by
  rintro rfl hr
  simp only [storePostBytes, List.foldl_cons]
  exact Nat.le_trans (wPubStorePostRaise ws rl a0 t hr)
    (wPubStorePostBytesMono (storePost ws rl a0 t) rl as0 t)

theorem wPubStorePostRunRaise (ws : Wstate) (rl : Bool) (base : Int) (n t : Nat) :
    0 < n → (ws.wRelp || rl) = true → t ≤ (storePostRun ws rl base n t).wPub := by
  intro hn hr
  simp only [storePostRun, ctrlPostPub]
  cases n with
  | zero => omega
  | succ n =>
    exact wPubStorePostBytesRaise ws rl _ t (base + ((0 : Nat) : Int))
      ((List.range' 1 n).map (fun j : Nat => base + (j : Int))) (by simp [List.range'_succ]) hr

theorem wPubStorePostRunMono (ws : Wstate) (rl : Bool) (base : Int) (n t : Nat) :
    ws.wPub ≤ (storePostRun ws rl base n t).wPub := by
  simp only [storePostRun, ctrlPostPub]
  exact wPubStorePostBytesMono _ _ _ _

theorem wpubCoversWrite (tid : Option Nat) (i : Nat) (s : Wmstate) (ak : AkInfo) (pa : PAddr)
    (n : Nat) (v : BitVec (8 * n)) :
    tid = some i → 0 < n → wpubCovers s.wmLog i s.wmWs →
    wpubCovers (wwritePost tid s ak pa n v).wmLog i (wwritePost tid s ak pa n v).wmWs := by
  rintro rfl hn h q mq hq ht hk
  rw [wwritePostLog] at hq
  show q + 1 ≤ (storePostRun s.wmWs ak.akSync (paZ pa) n (s.wmLog.length + 1)).wPub
  rcases lookup_app_Some.1 hq with hq | ⟨hge, hq⟩
  · exact Nat.le_trans (h q mq hq ht hk) (wPubStorePostRunMono _ _ _ _ _)
  · -- the fresh message: its class is `WCrel`, so the store published
    have hq0 : q - s.wmLog.length = 0 := by
      cases e : q - s.wmLog.length with
      | zero => rfl
      | succ k => rw [e] at hq; simp at hq
    rw [hq0] at hq
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hq
    subst hq
    have hqe : q = s.wmLog.length := by omega
    subst hqe
    apply wPubStorePostRunRaise _ _ _ _ _ hn
    simp only [wwriteMsg, wmClassOf] at hk
    by_cases hl : ak.akLatest = true
    · simp [hl] at hk
    · by_cases hr : (s.wmWs.wRelp || ak.akSync) = true
      · exact hr
      · simp [hl, hr] at hk

end Weak
