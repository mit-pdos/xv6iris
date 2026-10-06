/-
Weak: **the ownership ping-pong** (φ-upgrade §1c, Stage 1) -- the migration test for the C/D/S
points-to: a byte whose OWNERSHIP moves back and forth between two harts through a lock, while a
second byte owned by the first hart stays behind, dirty and untouched, across both handoffs.

Rocq: `iris/WkOwnPingPong.v` @ xxvzwolszwmp.

The Rocq header, in substance (Rocq vocabulary).

THE TWO PROGRAMS.  `x` is the TRANSFERRED byte, `y` hart A's PRIVATE byte, `lk` the lock word
(xv6's `acquire`/`release` idiom):

    hart A                                hart B
      sb   1, 0(x)     # x := 1  (D-A)      1: amoswap.w.aq a5, a4, 0(lk)
      sb   1, 0(y)     # y := 1  (D-A)         bnez a5, 1b        # acquire
      fence rw,w       # arms w_relp         lb  a5, 0(x)         # reads 1
      sw   zero, 0(lk) # release  ==>        sb   2, 0(x)  # x := 2   (D-B)
                                             fence rw,w
    1: amoswap.w.aq a5, a4, 0(lk)            sw zero, 0(lk)  # release  ==>
       bnez a5, 1b     # re-acquire
       lb  a5, 0(x)    # reads 2
       sb  3, 0(y)     # y is STILL A's, still dirty

WHAT IT DEMONSTRATES.  (1) The `WDirty A → WClean → WDirty B` cycle: A's `sb` dirties `x`; the
lock's payload is a CLEAN `x ↦w v`; the release's own D→C FLIP (§3) converts; after B stores, `x`
is `WDirty B`.  (2) The flip is PER-BYTE SELECTIVE: `y`, dirtied at the same time and crossing the
same release, is NOT flipped -- §3's frame lemma carries `wptDirty A y` IN and OUT.  (3) The view
transfer rides the payload exactly as in the spinlock (`wwpReleaseDeposit` / `wacquireCore`); §5's
load collapses every admissible timestamp onto the transferred value.  (4) All three arms of φ are
paid, by three different resources (§6): the fetch window (`nvOkUnwritten`), the owned byte
(`nvOk_of_wptOwn_at_cur`), the lock word (`nvOkOfPointsto`).

THE FLIP ROUTE.  `WeakLock.wreleaseCore` cannot do the flip: it takes the payload at the release's
PRE-state, whereas `WeakGhost.wlatFlip` needs the authority at the POST-state (the releasing hart's
`WCrel` message must be the log's LAST).  So `wreleaseFlipCore` is a different core: same script,
the flip spliced in between the lock word's element update and the deposit.  The one missing piece
is the message's CLASS: `wQStore` leaves it existential; §1 reads `WCrel` off the `wQEff` conjunct
every certificate already carries, under `akw.akLatest = false` and `σ.wmWs.wRelp = true`.

(The Rocq closing note, "WHAT A PORTED PROOF TAKES FROM THIS FILE": own-store sites use
`wpt_store_rule_own(_cur)` and never case-split on the class; a release that egresses owned memory
takes the payload in `↦wo` form, uses `wreleaseFlipCore`, and derives its log premise with
`wQEffStoreRel`; the receiving side needs only `wptOwn_of_wpt`; the index is a CONTEXT, not a hart;
and the context is ambient (`[CurCtx]`), the `ξ`-explicit primitives being for lemmas with two
contexts in scope.)

KERNEL IMAGE.  This file states NO kernel address or kernel code: the programs above are abstract
(`pc`, `lk`, `x`, `y` are parameters), so there is no drift against the Lean kernel image
(`Xv6/KernelImage.lean`, xv6 b72cbac1) to record.

**Deviations from Rocq.**

1. NAMES: the tree's camelCase (map below); `vwp_hold_ent` is FILE-QUALIFIED
   (`WkOwnPingPong.vwpHold_ent`, `notes/weak-port-dupnames.json`).  Vocabulary as
   `Weak/WeakVProp.lean` deviation 6 / `Weak/WeakAcquire.lean` deviation 1 (`wm_log σ` ↦
   `σ.wmLog`, `fin_to_nat i` ↦ `i.val`, `S (length l)` ↦ `l.length + 1`, `Arch.pa` ↦ `PAddr`,
   `bv n` ↦ `BitVec n`, `Z` ↦ `Int`, `N` widths ↦ `Nat`, `ak_coh` ↦ `akIfetch`, `ak_latest` ↦
   `akLatest`, `w_relp` ↦ `wRelp`, `wflat … !! pa_add a j` ↦ `wflatMem … (a + BitVec.ofNat 64 j)`,
   `locked γ i` ↦ `lockedEx γ i` (WeakLock deviation 2), `cur_ctx` ↦ `CurCtx.curCtx`,
   `register_lookup PC` ↦ `.wmRegs .PC`, `mstate` ↦ `ExecSt`, `WWP Loop` ↦
   `wwpTriv ⊤ (WExpr.loop gen cpu)`, ambient `GenId`/`CpuId` ↦ explicit `gen`/`cpu`).
2. CONTEXT: Rocq `{!riscvGS Σ, !weakGS Σ, !lockG Σ}` is `{hlc} [MachGS hlc GF] [WeakGS GF]
   [LockExG GF]` (only what each statement uses is included); `{XI : CurCtx}` is
   `[XI : CurCtx]`.  The `ξ`-explicit lemmas (`wptDirty*`, `vwpHold_ent`, `wpt_store_rule_dirty`,
   `wpt_store_post_dirty`) sit in a section WITHOUT the `CurCtx` binder (Lean would otherwise add
   an unused instance argument); Rocq has them in the `CurCtx` sections, where they do not use it.
3. STATEMENT SHAPES: the lock-side lemmas use WeakLock's curried form (Rocq `A -∗ B ==∗ C` is
   `A ⊢ B -∗ |==> C`); the store twins of `WeakVProp.wpt_store_rule_own` (`wpt_store_rule_dirty`,
   `wpt_store_post_dirty(_cur)`, `ppReceiveAndDirty`) use WeakVProp's sep-premise form
   (`A ∗ B ∗ C ∗ D ⊢ |==> (…)`), as their siblings do.
4. O2, THE TEXT PIN (WeakAcquire deviations 3/4): `wrelOwnCb` hands over
   `pinnedRead ∧ fetchPinned` per text byte (Rocq `pinned_read` only), and the callbacks of
   `wwpReleaseFlip` / `wwpPingpongAcquire` owe `wPEffText` (Rocq `wP_eff` verbatim) rather than
   Lean's `wPEff`; the certificate is `wstepCertText … (wstepCertFr … (wcertStore …))`, as in
   `WeakAcquire.wwpReleaseStoreCert`.
5. `wpt_dirty_at`'s Rocq proof goes through `monPred_at` rewriting; the Lean proof factors the
   view-level decode `wptDirty_at_view` (Lean-only, the twin of `WeakVProp.wptOwn_at_view`).
6. Lean-only helpers: `wptDirty_at_view` (deviation 5); `wlatStoreDirtyStep` (the ghost half of
   `wpt_store_rule_dirty`, which the Rocq proof inlines -- the `WeakVProp.wlatStoreOwnStep` twin
   with the state element pinned to `WDirty c`); `wmstateRestNonvLog` (the log authority out of
   `wmstateRestNonv` and back, Rocq's inline `iDestruct "Hrest" as (…)`).
7. `pp_handoff_load`'s `rewrite -Himg -Hlog` (on the proof-mode context) is a `rw` on the goal
   and on the instantiated load rule.

**Rocq → Lean name map.**  `wQ_eff_store_rel` `wQEffStoreRel`, `wQ_amo_aq_class`
`wQAmoAqClass`, `wpt_dirty` `wptDirty`, `wpt_dirty_own` `wptDirty_own`, `wpt_dirty_mono`
`wptDirty_mono`, `wpt_dirty_at` `wptDirty_at`, `wpt_dirty_at_intro` `wptDirty_at_intro`,
`wrelease_flip_core` `wreleaseFlipCore`, `wrelease_flip_frame` `wreleaseFlipFrame`,
`vwp_hold_ent` `WkOwnPingPong.vwpHold_ent`, `pp_receive` `ppReceive`, `wpt_store_rule_dirty`
`wpt_store_rule_dirty`, `wpt_store_post_dirty` `wpt_store_post_dirty`,
`wpt_store_post_dirty_cur` `wpt_store_post_dirty_cur` (the WeakVProp sibling spelling),
`pp_acquire_payload` `ppAcquirePayload`, `pp_acquire_own` `ppAcquireOwn`,
`pp_receive_and_dirty` `ppReceiveAndDirty`, `wrel_own_cb` `wrelOwnCb`, `wwp_release_flip`
`wwpReleaseFlip`, `wwp_pingpong_acquire` `wwpPingpongAcquire`, `pp_handoff_load`
`ppHandoffLoad`, `pp_return_leg` `ppReturnLeg`, `pp_phi_three_arms` `ppPhiThreeArms`.
Lean-only: `wptDirty_at_view`, `wlatStoreDirtyStep`, `wmstateRestNonvLog` (23 Rocq + 3 = 26).

**Dropped lemmas.**  None.
-/
import Weak.WeakAcquire
import Weak.WeakLock
import Weak.WeakVProp
import Weak.WeakInstr
import Weak.WeakCert
import MachCSL.MonPredExtra

namespace Weak

open Iris Iris.BI Iris.BI.MonPred Iris.ProofMode Iris.Std Iris.Std.PartialMap
open Iris.Std.LawfulPartialMap MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D LeanRV64D.Functions
open Wcds

/-! ## 1. Reading the release message's class off the trace -/

/-- The flip's missing premise: for the release `sw` (trace `fetch; write`), a non-AMO write at a
state whose release-pending flag is set appends a `WCrel` message. -/
theorem wQEffStoreRel (tid : Option Nat) (akf : AkInfo) (pf : PAddr) (nf : Nat) (akw : AkInfo)
    (ea : PAddr) (v : BitVec 32) (σ σ' : Wmstate) :
    akw.akLatest = false →
    σ.wmWs.wRelp = true →
    wQEff tid [.WEread akf pf nf, .WEwrite akw ea 4 v] σ σ' →
    σ'.wmLog = σ.wmLog ++ [wwriteMsg tid .WCrel ea 4 v] := by
  rintro hlat hrelp ⟨-, hlog, -⟩
  rw [hlog, weffsCons2, weffApplyRead, weffApplyWrite, wwritePostLog, wreadPostLog]
  have hk : wmClassOf akw (wreadPost σ akf pf (cohTs σ pf nf)).wmWs = .WCrel := by
    simp [wmClassOf, hlat, WeakInstr.wreadPostRelp, hrelp]
  rw [hk]

/-- ... and the AMO's write half, for contrast: always `WCexcl`. -/
theorem wQAmoAqClass (tid : Option Nat) (ea : PAddr) (v : BitVec 32) (σ σ' : Wmstate) :
    wQAmoAq tid ea v σ σ' → σ'.wmLog = σ.wmLog ++ [wwriteMsg tid .WCexcl ea 4 v] :=
  wQAmoAqExcl tid ea v σ σ'

/-! ## 2. A points-to that says "dirty" (context-explicit section, deviation 2) -/

section dirtyXi

variable {GF : BundledGFunctors} [WeakGS GF]

/-- `wptOwn` with the clean-or-dirty disjunction resolved to DIRTY by `c`. -/
def wptDirty (ξ : CtxId) (c : CPU) (a : Int) (v : BitVec 8) : VProp GF :=
  iprop(∃ t : Nat, ⎡wlatElem (GF := GF) a (DFrac.own 1) t v ∗ wdirty (GF := GF) c a ∗
    ctxWrote (GF := GF) ξ c (viewByte a t)⎤ ∗ ⊒(viewByte a t))

/-- The view-level decode (Lean-only, deviation 5). -/
theorem wptDirty_at_view (ξ : CtxId) (c : CPU) (a : Int) (v : BitVec 8) (V : View) :
    (wptDirty (GF := GF) ξ c a v).monPred_at V ⊣⊢
      ∃ t : Nat, wlatElem (GF := GF) a (DFrac.own 1) t v ∗ wdirty (GF := GF) c a ∗
        ctxWrote (GF := GF) ξ c (viewByte a t) ∗ ⌜t ≤ flr V a⌝ := by
  unfold wptDirty
  constructor
  · iintro ⟨%t, ⟨He, Hd, Hw⟩, %h⟩
    iexists t
    iframe He Hd Hw
    ipureintro; exact (viewByte_le a t V).mp h
  · iintro ⟨%t, He, Hd, Hw, %h⟩
    iexists t
    isplitl [He Hd Hw]
    · iframe He Hd Hw
    · ipureintro; exact (viewByte_le a t V).mpr h

theorem wptDirty_own (ξ : CtxId) (c : CPU) (a : Int) (v : BitVec 8) :
    wptDirty (GF := GF) ξ c a v ⊢ wptOwn (GF := GF) ξ a v := by
  refine entails_at.mpr fun V => ?_
  refine (wptDirty_at_view ξ c a v V).mp.trans
    (BIBase.Entails.trans ?_ (wptOwn_at_view ξ a v V).mpr)
  iintro ⟨%t, He, Hd, #Hw, %ht⟩
  iexists t
  iframe He
  isplitl [Hd]
  · iapply wownCtxOfDirty (GF := GF) ξ c a t
    iframe Hd Hw
  · ipureintro; exact ht

theorem wptDirty_mono (ξ : CtxId) (c : CPU) (a : Int) (v : BitVec 8) (ws ws' : Wstate) :
    wsLe ws ws' →
    vwpHold (wptDirty (GF := GF) ξ c a v) ws ⊢ vwpHold (wptDirty (GF := GF) ξ c a v) ws' :=
  fun h => vwpHold_mono _ h

/-- Its decode, the twin of `WeakVProp.wptOwn_at`. -/
theorem wptDirty_at (ξ : CtxId) (c : CPU) (a : Int) (v : BitVec 8) (ws : Wstate) :
    vwpHold (wptDirty (GF := GF) ξ c a v) ws ⊣⊢
      ∃ t : Nat, wlatElem (GF := GF) a (DFrac.own 1) t v ∗ wdirty (GF := GF) c a ∗
        ctxWrote (GF := GF) ξ c (viewByte a t) ∗ ⌜t ≤ flr (wsView ws) a⌝ :=
  wptDirty_at_view ξ c a v (wsView ws)

/-- ... and its introduction form. -/
theorem wptDirty_at_intro (ξ : CtxId) (c : CPU) (a : Int) (v : BitVec 8) (t : Nat) (ws : Wstate) :
    t ≤ flr (wsView ws) a →
    wlatElem (GF := GF) a (DFrac.own 1) t v ⊢ wdirty (GF := GF) c a -∗
      ctxWrote (GF := GF) ξ c (viewByte a t) -∗ vwpHold (wptDirty (GF := GF) ξ c a v) ws := by
  intro ht
  iintro He Hd Hw
  iapply (wptDirty_at ξ c a v ws).mpr
  iexists t
  iframe He Hd Hw
  ipureintro; exact ht

omit [WeakGS GF] in
theorem WkOwnPingPong.vwpHold_ent (P Q : VProp GF) (ws : Wstate) :
    (P ⊢ Q) → vwpHold P ws ⊢ vwpHold Q ws :=
  fun h => vwpHold_mono' ws h

/-- The ghost half of the DIRTYING store (Lean-only, deviation 6). -/
theorem wlatStoreDirtyStep (c : CPU) (img : GMapF PAddr (BitVec 8)) (log : List Wmsg) (m : Wmsg)
    (a : Int) (t : Nat) (v v' : BitVec 8) :
    msgByte m a = some v' →
    (∀ a', a' ≠ a → msgByte m a' = none) →
    m.wmTid = some c.val →
    m.wmAk = .WCplain →
    wlatInterp (GF := GF) img log ∗ wlatElem (GF := GF) a (DFrac.own 1) t v ∗
      wownSt (GF := GF) c a ⊢
      |==> (wlatInterp (GF := GF) img (log ++ [m]) ∗
        wlatElem (GF := GF) a (DFrac.own 1) (log.length + 1) v' ∗ wdirty (GF := GF) c a) := by
  intro hma hother htid hk
  unfold wlatInterp wlatElem wownSt wdirty wcdsEl
  iintro ⟨⟨%mm, %mc, Hauth, %hag, Hcauth, %hagc⟩, He, ⟨%s, Hsel, %hs⟩⟩
  icombine Hcauth Hsel gives %hlk
  imod ghost_map_update (log.length + 1, v') $$ Hauth He with ⟨Hauth, He⟩
  imod ghost_map_update (WDirty c) $$ Hcauth Hsel with ⟨Hcauth, Hsel⟩
  imodintro
  isplitl [Hauth Hcauth]
  · iexists insert mm a (log.length + 1, v'), insert mc a (WDirty c)
    iframe Hauth Hcauth
    isplit
    · ipureintro; exact wlatAgreeStore _ log m a v' mm hma hother hag
    · ipureintro
      intro a' s' ha'
      by_cases h : a' = a
      · subst h
        rw [lookupInsert] at ha'
        cases ha'
        have hok := wcdsOkStoreOwn log m a' c s htid hs (hagc a' s hlk)
        rw [hk] at hok
        exact hok
      · rw [lookupInsertNe (Ne.symm h)] at ha'
        refine wcdsOkApp log [m] a' s' ?_ (hagc a' s' ha')
        intro m0 hm0
        rw [List.mem_singleton] at hm0
        subst hm0
        exact hother a' h
  · iframe He Hsel

/-- DIRTYING AGAIN, under the new author: `WeakVProp.wpt_store_rule_own` with the message's class
pinned to `WCplain`, so that the postcondition is the SHARP `wptDirty`. -/
theorem wpt_store_rule_dirty (ξ : CtxId) (c : CPU) (σ σ' : Wmstate) (m : Wmsg) (a : Int)
    (v v' : BitVec 8) :
    msgByte m a = some v' →
    (∀ a', a' ≠ a → msgByte m a' = none) →
    m.wmTid = some c.val →
    m.wmAk = .WCplain →
    σ'.wmImg = σ.wmImg →
    σ'.wmLog = σ.wmLog ++ [m] →
    σ.wmLog.length + 1 ≤ flr (wsView σ'.wmWs) a →
    wlogAuth (GF := GF) σ'.wmLog ∗ ctxMigr (GF := GF) ξ c ∗
      wlatInterp (GF := GF) σ.wmImg σ.wmLog ∗ vwpHold (wptOwn (GF := GF) ξ a v) σ.wmWs ⊢
      |==> (wlogAuth (GF := GF) σ'.wmLog ∗ ctxMigr (GF := GF) ξ c ∗
        wlatInterp (GF := GF) σ'.wmImg σ'.wmLog ∗
        vwpHold (wptDirty (GF := GF) ξ c a v') σ'.wmWs) := by
  intro hma hother htid hk himg hlog hfl
  rw [himg, hlog]
  refine (sep_mono_right (sep_mono_right (sep_mono_right (wptOwn_at ξ a v σ.wmWs).mp))).trans ?_
  iintro ⟨Hlg, Hmg, Hi, ⟨%t, He, Hs, -⟩⟩
  imod wownCtxRetarget ξ c a t v σ.wmImg σ.wmLog (σ.wmLog ++ [m])
      (pubTransferSnoc σ.wmLog m c htid) $$ [Hlg Hmg Hi He Hs] with ⟨Hlg, Hmg, Hi, He, Hs⟩
  · iframe Hlg Hmg Hi He Hs
  imod ctxMigrMint ξ c (σ.wmLog ++ [m]) (σ.wmLog.length + 1)
      (by rw [List.length_append, List.length_singleton]; exact Nat.le_refl _) $$ [Hlg Hmg]
      with ⟨Hlg, Hmg, #Hbc⟩
  · iframe Hlg Hmg
  ihave #Hbca := ctxWroteByte (GF := GF) ξ c a (σ.wmLog.length + 1) $$ [Hbc]
  · iexact Hbc
  imod wlatStoreDirtyStep c σ.wmImg σ.wmLog m a t v v' hma hother htid hk $$ [Hi He Hs]
      with ⟨Hi, He, Hsel⟩
  · iframe Hi He Hs
  imodintro
  iframe Hlg Hmg Hi
  iapply wptDirty_at_intro ξ c a v' (σ.wmLog.length + 1) σ'.wmWs hfl $$ He Hsel Hbca

/-- ... at the machine's own store post-state, where the view premise is automatic. -/
theorem wpt_store_post_dirty (ξ : CtxId) (c : CPU) (σ : Wmstate) (m : Wmsg) (a : Int)
    (v v' : BitVec 8) (rl : Bool) :
    msgByte m a = some v' →
    (∀ a', a' ≠ a → msgByte m a' = none) →
    m.wmTid = some c.val →
    m.wmAk = .WCplain →
    wlogAuth (GF := GF) (σ.wmLog ++ [m]) ∗ ctxMigr (GF := GF) ξ c ∗
      wlatInterp (GF := GF) σ.wmImg σ.wmLog ∗ vwpHold (wptOwn (GF := GF) ξ a v) σ.wmWs ⊢
      |==> (wlogAuth (GF := GF) (σ.wmLog ++ [m]) ∗ ctxMigr (GF := GF) ξ c ∗
        wlatInterp (GF := GF) σ.wmImg (σ.wmLog ++ [m]) ∗
        vwpHold (wptDirty (GF := GF) ξ c a v') (storePost σ.wmWs rl a (σ.wmLog.length + 1))) :=
  fun hma hother htid hk =>
    wpt_store_rule_dirty ξ c σ
      { σ with wmLog := σ.wmLog ++ [m], wmWs := storePost σ.wmWs rl a (σ.wmLog.length + 1) }
      m a v v' hma hother htid hk rfl rfl (flr_storePost _ _ _ _)

end dirtyXi

/-! ## 3. The release that egresses a dirty byte -- the D→C flip at a real site -/

section pingpong

variable {GF : BundledGFunctors} [WeakGS GF] [LockExG GF] [XI : CurCtx]

/-- `WeakLock.wreleaseCore` with the deposit's own byte flipped clean on the way out.  The
premise `σ.wmWs.wRelp = true` is replaced by the sharper fact §1 derives from it: the appended
message is `WCrel` on the nose.  The payload goes in OWNED and comes out CLEAN. -/
theorem wreleaseFlipCore (γ : GName) (lk : PAddr) (x : Int) (v : BitVec 8) (i : CPU)
    (σ σ' : Wmstate) :
    wQStore (some i.val) lk lockZero σ σ' →
    σ'.wmLog = σ.wmLog ++ [wwriteMsg (some i.val) .WCrel lk 4 lockZero] →
    wsBounded σ.wmWs σ.wmLog.length →
    wlogAuth (GF := GF) σ'.wmLog ⊢ ctxMigr (GF := GF) CurCtx.curCtx i -∗
      wlatInterp (GF := GF) σ.wmImg σ.wmLog -∗
      wlockInv (GF := GF) γ lk (x ↦w v : VProp GF) -∗
      lockedEx (GF := GF) γ i -∗
      vwpHold (x ↦wo v : VProp GF) σ.wmWs -∗
      |==> (wlogAuth (GF := GF) σ'.wmLog ∗ ctxMigr (GF := GF) CurCtx.curCtx i ∗
        wlatInterp (GF := GF) σ'.wmImg σ'.wmLog ∗ wlockInv (GF := GF) γ lk (x ↦w v : VProp GF)) := by
  intro heff hlog hbnd
  obtain ⟨himg, -, -, -⟩ := heff
  iintro Hlg Hmg Hi Hinv Htok Hpt
  unfold wlockInv
  icases Hinv with ⟨%st, %t, %w, Hw, Ha, -⟩
  icases keepPure (lockedExState γ st i) $$ Ha Htok with ⟨%hst, Ha, Htok⟩
  subst hst
  -- the payload's element and its dirty-or-clean state
  icases (wptOwn_at CurCtx.curCtx x v σ.wmWs).mp $$ Hpt with ⟨%t0, Hel, Hs, %ht0⟩
  -- THE RETARGET, leaf-internally
  imod wownCtxRetarget CurCtx.curCtx i x t0 v σ.wmImg σ.wmLog σ'.wmLog
      (by rw [hlog]; exact pubTransferSnoc _ _ i rfl) $$ [Hlg Hmg Hi Hel Hs]
      with ⟨Hlg, Hmg, Hi, Hel, Hs⟩
  · iframe Hlg Hmg Hi Hel Hs
  -- the lock word's own bundle moves to the fresh top -- it stays CLEAN
  dsimp only [tidOf]
  imod wlat4LStoreGen (some i.val) .WCrel σ σ' lk t w lockZero (some i.val) none
      (wlockShapedRel _ .WCrel lk (by decide)) (altStepRelMsg i .WCrel lk) himg hlog $$ Hi Hw
      with ⟨Hi, Hw⟩
  -- THE FLIP: the authority is at the POST-log, whose last message is this hart's release
  have hflip := wlatFlip (GF := GF) σ'.wmImg σ.wmLog (wwriteMsg (some i.val) .WCrel lk 4 lockZero)
    i x rfl rfl
  rw [← hlog] at hflip
  imod hflip $$ [Hi Hs] with ⟨Hi, Hcl⟩
  · iframe Hi Hs
  -- the deposit: clean element + covered timestamp = `↦w`, frozen at the store's own timestamp
  have hdep : wlatElem (GF := GF) x (DFrac.own 1) t0 v ∗ wclean (GF := GF) x (DFrac.own 1) ⊢
      (x ↦w v : VProp GF).monPred_at (viewScl (σ.wmLog.length + 1)) :=
    (wpt_at_intro x (DFrac.own 1) v t0 σ.wmWs ht0).trans (wwpReleaseDeposit _ σ hbnd)
  ihave HR := hdep $$ [Hel Hcl]
  · iframe Hel Hcl
  imod lockClrcpu γ (some (i, true)) i $$ Ha Htok with ⟨-, Ha, Hpre⟩
  imod lockGive γ (some (i, false)) i $$ Ha Hpre with ⟨-, Ha, Hfrag⟩
  imodintro
  iframe Hlg Hmg Hi
  iexists none, σ.wmLog.length + 1, lockZero
  dsimp only [tidOf]
  iframe Hw Ha
  ileft
  iframe Hfrag HR
  ipureintro
  exact ⟨rfl, rfl⟩

/-- THE SAME LEMMA WITH THE PRIVATE BYTE IN THE FRAME: `y` enters DIRTY-`i` and leaves DIRTY-`i`,
at the releaser's post-state index, having crossed a release that flipped `x`. -/
theorem wreleaseFlipFrame (γ : GName) (lk : PAddr) (x y : Int) (v w : BitVec 8) (i : CPU)
    (σ σ' : Wmstate) :
    wQStore (some i.val) lk lockZero σ σ' →
    σ'.wmLog = σ.wmLog ++ [wwriteMsg (some i.val) .WCrel lk 4 lockZero] →
    wsBounded σ.wmWs σ.wmLog.length →
    wlogAuth (GF := GF) σ'.wmLog ⊢ ctxMigr (GF := GF) CurCtx.curCtx i -∗
      wlatInterp (GF := GF) σ.wmImg σ.wmLog -∗
      wlockInv (GF := GF) γ lk (x ↦w v : VProp GF) -∗
      lockedEx (GF := GF) γ i -∗
      vwpHold (x ↦wo v : VProp GF) σ.wmWs -∗
      vwpHold (wptDirty (GF := GF) CurCtx.curCtx i y w) σ.wmWs -∗
      |==> (wlogAuth (GF := GF) σ'.wmLog ∗ ctxMigr (GF := GF) CurCtx.curCtx i ∗
        wlatInterp (GF := GF) σ'.wmImg σ'.wmLog ∗ wlockInv (GF := GF) γ lk (x ↦w v : VProp GF) ∗
        vwpHold (wptDirty (GF := GF) CurCtx.curCtx i y w) σ'.wmWs) := by
  intro hQ hlog hbnd
  iintro Hlg Hmg Hi Hinv Htok Hpt Hy
  imod wreleaseFlipCore γ lk x v i σ σ' hQ hlog hbnd $$ Hlg Hmg Hi Hinv Htok Hpt
    with ⟨Hlg, Hmg, Hi, Hinv⟩
  imodintro
  iframe Hlg Hmg Hi Hinv
  iapply wptDirty_mono CurCtx.curCtx i y w σ.wmWs σ'.wmWs hQ.2.2.1
  iexact Hy

end pingpong

/-! ## 3'. The receiving side: take the clean byte, then dirty it -/

section receive

variable {GF : BundledGFunctors} [WeakGS GF] [LockExG GF] [XI : CurCtx]

omit [LockExG GF] in
/-- RE-OWNING.  One line, and it is the whole "receive". -/
theorem ppReceive (x : Int) (v : BitVec 8) (ws : Wstate) :
    vwpHold (x ↦w v : VProp GF) ws ⊢ vwpHold (x ↦wo v : VProp GF) ws :=
  WkOwnPingPong.vwpHold_ent _ _ ws (wptOwn_of_wpt _ x v)

omit [LockExG GF] in
/-- The AMBIENT form of `wpt_store_post_dirty`. -/
theorem wpt_store_post_dirty_cur (c : CPU) (σ : Wmstate) (m : Wmsg) (a : Int) (v v' : BitVec 8)
    (rl : Bool) :
    msgByte m a = some v' →
    (∀ a', a' ≠ a → msgByte m a' = none) →
    m.wmTid = some c.val →
    m.wmAk = .WCplain →
    wlogAuth (GF := GF) (σ.wmLog ++ [m]) ∗ ctxMigr (GF := GF) CurCtx.curCtx c ∗
      wlatInterp (GF := GF) σ.wmImg σ.wmLog ∗ vwpHold (a ↦wo v : VProp GF) σ.wmWs ⊢
      |==> (wlogAuth (GF := GF) (σ.wmLog ++ [m]) ∗ ctxMigr (GF := GF) CurCtx.curCtx c ∗
        wlatInterp (GF := GF) σ.wmImg (σ.wmLog ++ [m]) ∗
        vwpHold (wptDirty (GF := GF) CurCtx.curCtx c a v')
          (storePost σ.wmWs rl a (σ.wmLog.length + 1))) :=
  wpt_store_post_dirty _ c σ m a v v' rl

/-! ## 4'. One acquire, and what the acquirer gets -/

omit XI in
theorem ppAcquirePayload (γ : GName) (lk : PAddr) (x : Int) (v : BitVec 8) (c : CPU)
    (tid : Option Nat) (σ σ' : Wmstate) :
    wlogWf σ.wmLog → accWf lk 4 →
    wQAmoAq tid lk lockOne σ σ' →
    tid = some c.val →
    (∀ j : Nat, j < 4 →
      wflatMem σ.wmImg σ.wmLog (lk + BitVec.ofNat 64 j) = some (nthByte (n := 4) lockZero j)) →
    wlatInterp (GF := GF) σ.wmImg σ.wmLog ⊢
      wlockInv (GF := GF) γ lk (x ↦w v : VProp GF) -∗
      |==> (wlatInterp (GF := GF) σ'.wmImg σ'.wmLog ∗ wlockInv (GF := GF) γ lk (x ↦w v : VProp GF) ∗
        lockedEx (GF := GF) γ c ∗ vwpHold (x ↦w v : VProp GF) σ'.wmWs) := by
  intro hwf hacc hQ htid hzero
  iintro Hi Hinv
  icases wacquireCore γ lk (x ↦w v : VProp GF) c tid σ σ' hwf hacc hQ htid $$ Hi Hinv
    with ⟨%v0, %hflat, Hupd⟩
  have hv : lockZero = v0 := wflatWordAgree σ lk lockZero v0 hzero hflat
  imod Hupd with ⟨Hi, Hbody, Harm⟩
  icases Harm with (⟨-, HR, Htok⟩ | %hne)
  · imodintro
    iframe Hi Hbody Htok HR
  · exact absurd hv.symm hne

theorem ppAcquireOwn (γ : GName) (lk : PAddr) (x : Int) (v : BitVec 8) (c : CPU)
    (tid : Option Nat) (σ σ' : Wmstate) :
    wlogWf σ.wmLog → accWf lk 4 →
    wQAmoAq tid lk lockOne σ σ' →
    tid = some c.val →
    (∀ j : Nat, j < 4 →
      wflatMem σ.wmImg σ.wmLog (lk + BitVec.ofNat 64 j) = some (nthByte (n := 4) lockZero j)) →
    wlatInterp (GF := GF) σ.wmImg σ.wmLog ⊢
      wlockInv (GF := GF) γ lk (x ↦w v : VProp GF) -∗
      |==> (wlatInterp (GF := GF) σ'.wmImg σ'.wmLog ∗ wlockInv (GF := GF) γ lk (x ↦w v : VProp GF) ∗
        lockedEx (GF := GF) γ c ∗ vwpHold (x ↦wo v : VProp GF) σ'.wmWs) := by
  intro hwf hacc hQ htid hzero
  iintro Hi Hinv
  imod ppAcquirePayload γ lk x v c tid σ σ' hwf hacc hQ htid hzero $$ Hi Hinv
    with ⟨Hi, Hbody, Htok, HR⟩
  imodintro
  iframe Hi Hbody Htok
  iapply ppReceive x v σ'.wmWs
  iexact HR

omit [LockExG GF] in
/-- THE RECEIVER'S OWN STORE, in one step from the payload. -/
theorem ppReceiveAndDirty (c : CPU) (σ : Wmstate) (m : Wmsg) (x : Int) (v v' : BitVec 8)
    (rl : Bool) :
    msgByte m x = some v' →
    (∀ a', a' ≠ x → msgByte m a' = none) →
    m.wmTid = some c.val →
    m.wmAk = .WCplain →
    wlogAuth (GF := GF) (σ.wmLog ++ [m]) ∗ ctxMigr (GF := GF) CurCtx.curCtx c ∗
      wlatInterp (GF := GF) σ.wmImg σ.wmLog ∗ vwpHold (x ↦w v : VProp GF) σ.wmWs ⊢
      |==> (wlogAuth (GF := GF) (σ.wmLog ++ [m]) ∗ ctxMigr (GF := GF) CurCtx.curCtx c ∗
        wlatInterp (GF := GF) σ.wmImg (σ.wmLog ++ [m]) ∗
        vwpHold (wptDirty (GF := GF) CurCtx.curCtx c x v')
          (storePost σ.wmWs rl x (σ.wmLog.length + 1))) := by
  intro hma hother htid hk
  refine (sep_mono_right (sep_mono_right (sep_mono_right (ppReceive x v σ.wmWs)))).trans ?_
  exact wpt_store_post_dirty_cur c σ m x v v' rl hma hother htid hk

end receive

/-! ## 4. The same release at the WP altitude -- one `sw` through the invariant -/

section wpPingpong

variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [WeakGS GF] [LockExG GF]
  [XI : CurCtx]

omit [LockExG GF] XI in
/-- The log authority out of the φ-free remainder, and back (Lean-only, deviation 6). -/
theorem wmstateRestNonvLog (cpu : CPU) (σ : Wmstate) :
    wmstateRestNonv (hlc := hlc) (GF := GF) cpu σ ⊢
      wlogAuth (GF := GF) σ.wmLog ∗
        (wlogAuth (GF := GF) σ.wmLog -∗ wmstateRestNonv (hlc := hlc) (GF := GF) cpu σ) := by
  unfold wmstateRestNonv
  iintro ⟨%hb, %hw, Hr, Hd, Hl, Hws⟩
  iframe Hl
  iintro Hl
  isplitr
  · ipureintro; exact hb
  isplitr
  · ipureintro; exact hw
  iframe Hr Hd Hl Hws

/-- The release callback with the OWNED payload and the private dirty byte. -/
def wrelOwnCb (gen : Nat) (cpu : CPU) (x y : Int) (v w : BitVec 8) (pc : BitVec 64)
    (P : Wmstate → Prop) : IProp GF :=
  iprop(∀ σ : Wmstate,
    wlatInterp σ.wmImg σ.wmLog -∗
    wmstateRest (hlc := hlc) (GF := GF) cpu σ ={⊤ \ ↑wlockN, ∅}=∗
      ⌜σ.wmRegs .PC = pc⌝ ∗
      ⌜∀ j : Nat, j < 4 →
        pinnedRead σ (WeakInterp.accAddr pc j) ∧ fetchPinned σ (WeakInterp.accAddr pc j)⌝ ∗
      ⌜P σ⌝ ∗
      ⌜∀ j : Nat, j < 4 → nvOk σ.wmLog cpu (WeakInterp.accAddr pc j)⌝ ∗
      -- the `fence rw,w` at `pc-4`: it makes the message `WCrel`, which keeps the lock word clean
      -- AND licenses the flip
      ⌜σ.wmWs.wRelp = true⌝ ∗
      wlatInterp σ.wmImg σ.wmLog ∗
      vwpHold (x ↦wo v : VProp GF) σ.wmWs ∗
      vwpHold (wptDirty (GF := GF) CurCtx.curCtx cpu y w) σ.wmWs ∗
      ∃ t0 t1 : ExecSt,
        ⌜exec (riscvStep false) (wflatSt σ) = some ((), t0)⌝ ∗
        ⌜exec (riscvStep true) (wflatSt σ) = some ((), t1)⌝ ∗
        ▷ (∀ (tick : Bool) (σ' : Wmstate),
            ⌜wstepPost σ σ' (if tick then t1 else t0)⌝ -∗
            vwpHold (wptDirty (GF := GF) CurCtx.curCtx cpu y w) σ'.wmWs -∗
            |={∅, ⊤ \ ↑wlockN}=> wmstateRestNonv (hlc := hlc) (GF := GF) cpu σ' ∗
              -- the migration invariant comes back to the thread
              (ctxMigr (GF := GF) CurCtx.curCtx cpu -∗
                wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu))))

/-- `WeakAcquire.wwpReleaseStore` with the owned payload: the exemplar a ported release site
copies. -/
theorem wwpReleaseFlip (gen : Nat) (cpu : CPU) (γ : GName) (lk : PAddr) (x y : Int)
    (v w : BitVec 8) (pc : BitVec 64) (akf : AkInfo) (pf : PAddr) (nf : Nat) (akw : AkInfo) :
    gen = 0 →
    accWf pc 4 →
    accWf lk 4 →
    akw.akLatest = false →
    (∀ a : Int, weffTouches (.WEread akf pf nf) a → ∃ j, j < 4 ∧ a = WeakInterp.accAddr pc j) →
    inv wlockN (wlockInv (GF := GF) γ lk (x ↦w v : VProp GF)) ⊢
      lockedEx (GF := GF) γ cpu -∗
      ctxMigr (GF := GF) CurCtx.curCtx cpu -∗
      wrelOwnCb (hlc := hlc) gen cpu x y v w pc
        (wPEffText (some cpu.val) [.WEread akf pf nf, .WEwrite akw lk 4 lockZero]) -∗
      wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu) := by
  intro hgen haccpc hacclk hlatw hfetch
  have hfoot : ∀ a : Int, weffsTouch [.WEread akf pf nf, .WEwrite akw lk 4 lockZero] a →
      (∃ j, j < 4 ∧ a = WeakInterp.accAddr pc j) ∨ (∃ j, j < 4 ∧ a = WeakInterp.accAddr lk j) := by
    intro a ha
    rcases weffsTouchCons _ _ a ha with ha | ha
    · exact .inl (hfetch a ha)
    · exact .inr (weffsTouchWrite1 _ lk _ _ a ha)
  have hcert := wstepCertText _ pc _ _ (fetchInWindowStore pc akf pf nf akw lk lockZero hfetch)
    (fetchFreshStore akf pf nf akw lk lockZero)
    (wstepCertFr _ pc _ _ (wcertStore cpu.val pc akf pf nf akw lk lockZero))
  iintro #Hinv Htok Hmg Hk
  unfold wrelOwnCb
  iapply wpWinstr gen cpu pc _ _ hgen haccpc hcert
  iintro %σ Hσ
  icases (wmstateInterpSplit cpu σ).mp $$ Hσ with ⟨Hlat, Hrest⟩
  icases keepPure1 (wmstateRestFacts cpu σ) $$ Hrest with ⟨%hfacts, Hrest⟩
  icases keepPure1 (wmstateRestNv cpu σ) $$ Hrest with ⟨%hnvσ, Hrest⟩
  obtain ⟨hbnd, _⟩ := hfacts
  imod (inv_acc (E := ⊤) (N := wlockN) (P := wlockInv (GF := GF) γ lk (x ↦w v : VProp GF))
    CoPset.subseteq_top) $$ Hinv with ⟨Hbody, Hclose⟩
  imod Hk $$ %σ Hlat Hrest
    with ⟨%hpc, %htext, %hP, %hnvpc, %hrelp, Hlat, Hx, Hy, %t0, %t1, %hex0, %hex1, Hcont⟩
  imodintro
  isplitr
  · ipureintro; exact hpc
  isplitr
  · ipureintro; exact htext
  isplitr
  · ipureintro; exact hP
  iexists t0, t1
  isplitr
  · ipureintro; exact hex0
  isplitr
  · ipureintro; exact hex1
  inext
  iintro %tick %σ' %hpost %hQfr
  obtain ⟨hQ, hQeff⟩ := hQfr
  -- §1: the class of the message this step appended
  have hlog : σ'.wmLog = σ.wmLog ++ [wwriteMsg (some cpu.val) .WCrel lk 4 lockZero] :=
    wQEffStoreRel _ akf pf nf akw lk lockZero σ σ' hlatw hrelp hQeff
  -- the continuation FIRST: the log authority lives in the POST-state remainder it returns
  imod Hcont $$ %tick %σ' %hpost [Hy] with ⟨Hrest, Hk2⟩
  · iapply wptDirty_mono CurCtx.curCtx cpu y w σ.wmWs σ'.wmWs (wstepPostWsLe σ σ' _ hpost)
    iexact Hy
  icases wmstateRestNonvLog cpu σ' $$ Hrest with ⟨Hlogauth, Hrest⟩
  imod wreleaseFlipCore γ lk x v cpu σ σ' hQ hlog hbnd $$ Hlogauth Hmg Hlat Hbody Htok Hx
    with ⟨Hlogauth, Hmg, Hlat, Hbody⟩
  -- the φ payment, verbatim `WeakAcquire.wwpReleaseStore`'s
  icases keepPure (nvOkWlockInv cpu σ'.wmImg σ'.wmLog γ lk (x ↦w v : VProp GF)) $$ Hlat Hbody
    with ⟨%hnvlk, Hlat, Hbody⟩
  have hnv' : nvHart σ'.wmLog cpu σ'.wmWs := by
    apply nvHartOfWQEffOk cpu σ σ' _ hQeff hnvσ
    intro a ha
    rcases hfoot a ha with ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩
    · rw [hlog]
      intro n
      refine nvByteAppOwn _ _ cpu _ n (hnvpc j hj n) fun m hm => ?_
      rw [List.mem_singleton] at hm
      subst hm
      rfl
    · exact hnvlk j hj
  ihave Hwp := Hk2 $$ Hmg
  imod Hclose $$ [Hbody]
  · inext
    iexact Hbody
  imodintro
  isplitl [Hlat Hrest Hlogauth]
  · iapply (wmstateInterpSplit cpu σ').mpr
    iframe Hlat
    iapply wmstateRestOfNonv cpu σ' $$ %hnv'
    iapply Hrest
    iexact Hlogauth
  · iexact Hwp

omit XI in
/-- ... AND THE OTHER SIDE OF THE HANDOFF NEEDS NO NEW RULE AT ALL: the spin-acquire is
`WeakAcquire.wwpAcquireLoopCert` at `R := x ↦w v`, instantiated and nothing else. -/
theorem wwpPingpongAcquire (gen : Nat) (cpu : CPU) (γ : GName) (lk : PAddr) (x : Int)
    (v : BitVec 8) (pc : BitVec 64) (akf : AkInfo) (pf : PAddr) (nf : Nat) (aka akw : AkInfo)
    (K : IProp GF) :
    gen = 0 →
    accWf pc 4 →
    accWf lk 4 →
    aka.akIfetch = false →
    aka.akSync = true →
    akw.akLatest = true →
    (∀ a : Int, weffTouches (.WEread akf pf nf) a → ∃ j, j < 4 ∧ a = WeakInterp.accAddr pc j) →
    inv wlockN (wlockInv (GF := GF) γ lk (x ↦w v : VProp GF)) ⊢
      □ (K -∗ ▷ (K -∗ wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu)) -∗
          wacqCb (hlc := hlc) gen cpu γ lk (x ↦w v : VProp GF) pc
            (wPEffText (some cpu.val)
              [.WEread akf pf nf, .WEread aka lk 4, .WEwrite akw lk 4 lockOne])) -∗
        K -∗ wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu) :=
  wwpAcquireLoopCert gen cpu γ lk (x ↦w v : VProp GF) pc akf pf nf aka akw K

end wpPingpong

/-! ## 5. The payoff: what the receiving hart's load returns -/

section payoff

variable {GF : BundledGFunctors} [WeakGS GF] [LockExG GF] [XI : CurCtx]

theorem ppHandoffLoad (γ : GName) (lk : PAddr) (x : Int) (v : BitVec 8) (c : CPU)
    (tid : Option Nat) (σ σ' σn : Wmstate) (ak : AkInfo) (t' : Nat) (b : BitVec 8) :
    -- the acquire: the swap read 0, so the payload is thawed here
    wlogWf σ.wmLog → accWf lk 4 →
    wQAmoAq tid lk lockOne σ σ' →
    tid = some c.val →
    (∀ j : Nat, j < 4 →
      wflatMem σ.wmImg σ.wmLog (lk + BitVec.ofNat 64 j) = some (nthByte (n := 4) lockZero j)) →
    -- and then a PLAIN load of `x` at a state with the same memory
    ak.akIfetch = false →
    σn.wmImg = σ'.wmImg → σn.wmLog = σ'.wmLog →
    wsLe σ'.wmWs σn.wmWs →
    wbyteOk σn ak x t' b →
    wlatInterp (GF := GF) σ.wmImg σ.wmLog ⊢
      wlockInv (GF := GF) γ lk (x ↦w v : VProp GF) -∗
      |==> (wlatInterp (GF := GF) σn.wmImg σn.wmLog ∗
        wlockInv (GF := GF) γ lk (x ↦w v : VProp GF) ∗
        lockedEx (GF := GF) γ c ∗ ⌜b = v⌝ ∗ vwpHold (x ↦wo v : VProp GF) σn.wmWs) := by
  intro hwf hacc hQ htid hzero hcoh himg hlog hle hok
  have hload := wpt_load_rule (GF := GF) σn σn ak x (DFrac.own 1) v t' b hcoh hok rfl rfl
    (Nat.le_refl _)
  rw [himg, hlog] at hload
  rw [himg, hlog]
  iintro Hi Hinv
  imod ppAcquirePayload γ lk x v c tid σ σ' hwf hacc hQ htid hzero $$ Hi Hinv
    with ⟨Hi, Hbody, Htok, HR⟩
  -- carry the payload to the load's own state, then collapse the load
  ihave HR := vwpHold_mono (x ↦w v : VProp GF) hle $$ HR
  icases hload $$ [Hi HR] with ⟨%hv, Hi, HR⟩
  · iframe Hi HR
  imodintro
  iframe Hi Hbody Htok
  isplitr
  · ipureintro; exact hv
  iapply ppReceive x v σn.wmWs
  iexact HR

/-- THE RETURN LEG: the same statement at the hart that STARTED the example, carrying its private
byte through. -/
theorem ppReturnLeg (γ : GName) (lk : PAddr) (x y : Int) (v w : BitVec 8) (cA : CPU)
    (tid : Option Nat) (σ σ' σn : Wmstate) (ak : AkInfo) (t' : Nat) (b : BitVec 8) :
    wlogWf σ.wmLog → accWf lk 4 →
    wQAmoAq tid lk lockOne σ σ' →
    tid = some cA.val →
    (∀ j : Nat, j < 4 →
      wflatMem σ.wmImg σ.wmLog (lk + BitVec.ofNat 64 j) = some (nthByte (n := 4) lockZero j)) →
    ak.akIfetch = false →
    σn.wmImg = σ'.wmImg → σn.wmLog = σ'.wmLog →
    wsLe σ'.wmWs σn.wmWs →
    wbyteOk σn ak x t' b →
    wlatInterp (GF := GF) σ.wmImg σ.wmLog ⊢
      wlockInv (GF := GF) γ lk (x ↦w v : VProp GF) -∗
      vwpHold (wptDirty (GF := GF) CurCtx.curCtx cA y w) σ.wmWs -∗
      |==> (wlatInterp (GF := GF) σn.wmImg σn.wmLog ∗
        wlockInv (GF := GF) γ lk (x ↦w v : VProp GF) ∗
        lockedEx (GF := GF) γ cA ∗ ⌜b = v⌝ ∗
        vwpHold (x ↦wo v : VProp GF) σn.wmWs ∗
        vwpHold (wptDirty (GF := GF) CurCtx.curCtx cA y w) σn.wmWs) := by
  intro hwf hacc hQ htid hzero hcoh himg hlog hle hok
  iintro Hi Hinv Hy
  imod ppHandoffLoad γ lk x v cA tid σ σ' σn ak t' b hwf hacc hQ htid hzero hcoh himg hlog hle hok
    $$ Hi Hinv with ⟨Hi, Hbody, Htok, %hv, Hx⟩
  imodintro
  iframe Hi Hbody Htok Hx
  isplitr
  · ipureintro; exact hv
  iapply wptDirty_mono CurCtx.curCtx cA y w σ.wmWs σn.wmWs (wsLeTrans hQ.1.2.2.1 hle)
  iexact Hy

/-! ## 6. The three arms of φ, in one statement -/

omit [LockExG GF] in
theorem ppPhiThreeArms (c : CPU) (img : GMapF PAddr (BitVec 8)) (log : List Wmsg) (ws : Wstate)
    (pcb x lkb : Int) (vx : BitVec 8) (dq : DFrac) (t : Nat) (vl : BitVec 8) :
    latestTs log pcb = 0 →
    wlogAuth (GF := GF) log ⊢ ctxMigr (GF := GF) CurCtx.curCtx c -∗
      wlatInterp (GF := GF) img log -∗
      vwpHold (x ↦wo vx : VProp GF) ws -∗
      wlatPointsto (GF := GF) lkb dq t vl -∗
      ⌜nvOk log c pcb ∧ nvOk log c x ∧ nvOk log c lkb⌝ := by
  intro htext
  iintro Hlg Hmg Hi Hx Hlk
  icases keepPure1 (nvOkOfPointsto (GF := GF) img log c lkb dq t vl) $$ [Hi Hlk]
    with ⟨%hnl, Hi, -⟩
  · iframe Hi Hlk
  ihave %hnx := nvOk_of_wptOwn_at_cur c x vx img log ws $$ [Hlg Hmg Hi Hx]
  · iframe Hlg Hmg Hi Hx
  ipureintro
  exact ⟨nvOkUnwritten log c pcb htext, hnx, hnl⟩

end payoff

end Weak
