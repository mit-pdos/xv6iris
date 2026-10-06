/-
Weak: **the acceptance test for the `IProp` surface** (φ-upgrade §1.8) -- `WkYieldFrame`'s and
`WkOwnPingPong`'s function-proof-side lemmas restated over `WeakCtxPt`'s `↦wpo` / `↦wp{dq}` and
`ctxOwnAt`, and `WeakCtxLock`'s lock contexts; the test is what the STATEMENTS look like.

Rocq: `iris/WkCtxSurface.v` @ xxvzwolszwmp.

The Rocq header, in substance (Rocq vocabulary).

  - NO VIEW AND NO `monPred` APPEARS IN ANY STATEMENT.  The `VProp` versions carry
    `vwpHold P ws` in every memory slot, so the wstates of the pre- and post-state are written
    into the specification; here `x ↦wpo v` is a proposition with no state in it, and the fact
    in the precondition and in the postcondition are literally the same term.
  - NO FRAMING STEP AT A STATE CHANGE.  `WkYieldFrame` §4a ends with `vwpHold_mono` to carry the
    untouched `z` across the store's view growth; `WkOwnPingPong`'s `wreleaseFlipFrame` and
    `ppReturnLeg` each end with `wptDirty_mono`.  Here those lines are `iframe`.
  - NO FREEZE AND NO THAW AT THE YIELD.  `WkYieldFrame` §4c freezes T's facts at the parking index
    and §4d thaws them with `vwpHold_intro`; §3 below frames them through the park and the resume
    with `iframe`, and the resume's `⌜V ≤ wsView …⌝` postcondition is gone (it is inside
    `ctxOwnAt`).
  - NO UPGRADE AND NO RE-INDEX AT AN ACCESS SITE.  §2's access block is ONE lemma, applied on the
    hart that dirtied the byte and on the hart that resumed the thread; the ξ_L ↔ ξ re-indexing
    appears only in the signatures of §4's lock lemmas.

WHAT IS THE API.  This file's spellings are.  `WkYieldFrame` and `WkOwnPingPong` keep their
`VProp` statements -- the internal glue's own tests -- and the lemmas here are proved BY them.

(Rocq closing list, "what this file checks": §2 an access site's script is the same before and
after a migration (`wcsTouchA` / `wcsTouchB` are one lemma applied twice); §3 the thread's facts
frame around the yield by `iframe`, `ctxOwnAt` in / `ctxOwnAt` out with the cpu re-bound; §4 the
ξ_L ↔ ξ re-indexing appears only in the lock lemmas' signatures, ξ_L itself only under
`wctxIsLock`'s existential; §5 φ is paid by the same lemma at every arm; §6 the park's
WP-altitude rule with the handoff flag carrying the parking context's LEDGER -- the callback is
`WkYieldFrame.wyieldParkCb` verbatim, and the resume side needs no rule at all
(`WeakAcquire.wwpAcquireLoopCert` at `wctxBaton ξ`).)

§6, WHY THE PREMISE IS THE LEDGER AND NOT `ctxOwn`: `ctxOwn` bundles the hart's own wstate
fragment, which at this altitude belongs to the CALLBACK's obligation (it returns
`wmstateRestNonv σ'`, whose `wwsAuth` it can only move by holding the client half); a caller splits
its `ctxOwn` once (`ctxOwnOpen`) -- ledger and migration invariant to this rule, `hartWs` to its
callback -- and reassembles with `ctxOwnClose`.

KERNEL IMAGE.  No kernel address or code is stated (all programs abstract), so there is no drift
against `Xv6/KernelImage.lean` to record.

**Deviations from Rocq.**

1. NAMES: camelCase (map below); none is in the duplicated-name table.  Vocabulary as
   `Weak/WkYieldFrame.lean` deviation 1 (`wm_log σ` ↦ `σ.wmLog`, `fin_to_nat i` ↦ `i.val`,
   `S (length l)` ↦ `l.length + 1`, `Arch.pa` ↦ `PAddr`, `bv 8` ↦ `BitVec 8`, `Z` ↦ `Int`,
   `N` ↦ `Nat`, `ak_coh` ↦ `akIfetch`, `ak_latest` ↦ `akLatest`, `wflat … !! pa_add a j` ↦
   `wflatMem … (a + BitVec.ofNat 64 j)`, `locked γ i` ↦ `lockedEx γ i`, `cur_ctx` ↦
   `CurCtx.curCtx`, `WWP Loop` ↦ `wwpTriv ⊤ (WExpr.loop gen cpu)`, `DfracOwn 1` ↦
   `DFrac.own 1`, Rocq's untyped image `img : _` ↦ `GMapF PAddr (BitVec 8)`).
2. CONTEXT: Rocq `{!riscvGS Σ, !weakGS Σ, !lockG Σ}` is `[WeakGS GF] [LockExG GF]` plus
   `{hlc} [MachGS hlc GF]` where the statement mentions an invariant / WP (§4, §6); only what
   each statement uses (`omit` elsewhere).  `{XI : CurCtx}` is `[XI : CurCtx]`; ambient
   `GenId`/`CpuId` (§6) are explicit `gen`/`cpu`.
3. STATEMENT SHAPES: WeakLock's curried form (Rocq `A -∗ B ==∗ C` is `A ⊢ B -∗ |==> (C)`); the
   §1 one-premise lemma `wptstoDirtyOwn` is `A ⊢ B`.
4. O2, THE TEXT PIN (`WkYieldFrame` deviation 5): `wwpCtxYieldPark`'s callback owes `wPEffText`
   (Rocq `wP_eff`), and the certificate is `wstepCertText … (wstepCertFr … (wcertStore …))`.
5. `wcsHandoffLoad`: Rocq's `rewrite -Himg -Hlog` in the proof context is a rewrite of the
   intermediate `wlatInterp` entailment; the load rule's view premise (`reflexivity`) is
   `fun _ => Nat.le_refl _`.
6. Rocq's `Print Assumptions` lines have no Lean counterpart (the lint bans axioms).

**Rocq → Lean name map.**  `wptsto_dirty` `wptstoDirty`, `wptsto_dirty_own` `wptstoDirtyOwn`,
`wptsto_dirty_to_pt` `wptstoDirtyToPt`, `wptsto_dirty_of_pt` `wptstoDirtyOfPt`, `wcs_touch`
`wcsTouch`, `wcs_touch_A` `wcsTouchA`, `wcs_touch_B` `wcsTouchB`, `wcs_park_frames`
`wcsParkFrames`, `wcs_resume_frames` `wcsResumeFrames`, `wcs_yield_is_memory_silent`
`wcsYieldIsMemorySilent`, `wcs_release_leg` `wcsReleaseLeg`, `wcs_acquire_leg` `wcsAcquireLeg`,
`wcs_handoff_load` `wcsHandoffLoad`, `wcs_is_lock_internal` `wcsIsLockInternal`,
`wcs_phi_three_arms` `wcsPhiThreeArms`, `wwp_ctx_yield_park` `wwpCtxYieldPark` (16 Rocq = 16
Lean).

**Dropped lemmas.**  None.
-/
import Weak.WkYieldFrame
import Weak.WkOwnPingPong
import Weak.WeakCtxLock
import Weak.WeakCtxPt
import MachCSL.MonPredExtra

namespace Weak

open Iris Iris.BI Iris.BI.MonPred Iris.ProofMode Iris.Std Iris.Std.PartialMap
open Iris.Std.LawfulPartialMap MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D LeanRV64D.Functions
open Wcds

/-! ## 1. The sharp exhibit form -- a points-to that SAYS "dirty"

`WeakCtxPt.wptsto` absorbs clean-and-dirty on purpose; for the examples' claims ("the private
byte is still dirty on the far side of the handoff") the absorbing form is one bit too coarse,
exactly as `WkOwnPingPong.wptDirty` is the sharpened `wptOwn`.  Used only in statements. -/

section dirty

variable {GF : BundledGFunctors} [WeakGS GF]

def wptstoDirty (ξ : CtxId) (c : CPU) (a : Int) (v : BitVec 8) : IProp GF :=
  iprop(∃ t : Nat, wlatElem (GF := GF) a (DFrac.own 1) t v ∗ wdirty (GF := GF) c a ∗
    ctxWrote (GF := GF) ξ c (viewByte a t) ∗ ctxViewLb (GF := GF) ξ (viewByte a t))

theorem wptstoDirtyOwn (ξ : CtxId) (c : CPU) (a : Int) (v : BitVec 8) :
    wptstoDirty (GF := GF) ξ c a v ⊢ wptsto ξ a v := by
  unfold wptstoDirty wptsto
  iintro ⟨%t, He, Hd, #Hw, #Hf⟩
  iexists t
  iframe He Hf
  iapply wownCtxOfDirty ξ c a t
  iframe Hd Hw

theorem wptstoDirtyToPt (ξ : CtxId) (c : CPU) (ws : Wstate) (a : Int) (v : BitVec 8) :
    ctxLb (GF := GF) ξ ws ⊢ wptstoDirty ξ c a v -∗
      ctxLb ξ ws ∗ vwpHold (wptDirty (GF := GF) ξ c a v) ws := by
  unfold wptstoDirty
  iintro Hlb ⟨%t, He, Hd, #Hw, #Hf⟩
  icases ctxLbValid ξ ws (viewByte a t) $$ [Hlb Hf] with ⟨Hlb, %hle⟩
  · iframe Hlb Hf
  iframe Hlb
  iapply wptDirty_at_intro ξ c a v t ws ((viewByte_le a t _).mp hle) $$ He Hd Hw

theorem wptstoDirtyOfPt (ξ : CtxId) (c : CPU) (ws : Wstate) (a : Int) (v : BitVec 8) :
    ctxAuth (GF := GF) ξ (wsView ws) ⊢ vwpHold (wptDirty (GF := GF) ξ c a v) ws -∗
      ctxAuth ξ (wsView ws) ∗ wptstoDirty ξ c a v := by
  iintro Ha Hpt
  icases (wptDirty_at ξ c a v ws).mp $$ Hpt with ⟨%t, He, Hd, Hw, %ht⟩
  ihave #Hf := ctxViewLbGet ξ (wsView ws) (viewByte a t) ((viewByte_le a t _).mpr ht) $$ Ha
  iframe Ha
  unfold wptstoDirty
  iexists t
  iframe He Hd Hw Hf

end dirty

/-! ## 2. The access block -- `WkYieldFrame` §4a on the `IProp` surface

`load x; x := 2; load z`, with `x` owned (possibly dirtied on a hart the thread has since left)
and `z` a shared clean byte.  Compare with `WkYieldFrame.wyfTouch`: the clean byte's slot is the
SAME TERM in the precondition and the postcondition, and neither slot names a wstate. -/

section touch

variable {GF : BundledGFunctors} [WeakGS GF] [LockExG GF]
/- THREAD T'S CONTEXT, AMBIENT -- one instance for the section, as in `WkYieldFrame` §4: the
`x ↦wpo vx` of §2b (hart A) and of §2c (hart B) are the SAME proposition. -/
variable [XI : CurCtx]

omit [LockExG GF] in
theorem wcsTouch (c : CPU) (σ : Wmstate) (m : Wmsg) (x z : Int) (vx vz : BitVec 8) (q : DFrac)
    (akx akz : AkInfo) (tx tz : Nat) (bx bz : BitVec 8) (rl : Bool) :
    akx.akIfetch = false → wbyteOk σ akx x tx bx →
    akz.akIfetch = false → wbyteOk σ akz z tz bz →
    msgByte m x = some byte2 →
    (∀ a', a' ≠ x → msgByte m a' = none) →
    m.wmTid = some c.val →
    m.wmAk = .WCplain →
    wlogAuth (GF := GF) (σ.wmLog ++ [m]) ⊢
      wlatInterp (GF := GF) σ.wmImg σ.wmLog -∗
      ctxOwnAt (GF := GF) CurCtx.curCtx c σ.wmWs -∗
      (x ↦wpo vx : IProp GF) -∗ (z ↦wp{q} vz : IProp GF) -∗
      |==> (wlogAuth (GF := GF) (σ.wmLog ++ [m]) ∗
        wlatInterp (GF := GF) σ.wmImg (σ.wmLog ++ [m]) ∗
        ctxOwnAt (GF := GF) CurCtx.curCtx c (storePost σ.wmWs rl x (σ.wmLog.length + 1)) ∗
        ⌜bx = vx⌝ ∗ ⌜bz = vz⌝ ∗
        wptstoDirty (GF := GF) CurCtx.curCtx c x byte2 ∗ (z ↦wp{q} vz : IProp GF)) := by
  intro hcohx hokx hcohz hokz hmb hother htid hk
  unfold ctxOwnAt
  iintro Hlg Hi ⟨Hlb, Hmg⟩ Hx Hz
  -- into the internal glue ...
  icases wptstoToOwn CurCtx.curCtx σ.wmWs x vx $$ [Hlb Hx] with ⟨Hlb, Hx⟩
  · iframe Hlb Hx
  icases wptstoClToPt CurCtx.curCtx σ.wmWs z q vz $$ [Hlb Hz] with ⟨Hlb, Hz⟩
  · iframe Hlb Hz
  -- ... the landed `VProp` access block, unchanged ...
  imod wyfTouch c σ m x z vx vz q akx akz tx tz bx bz rl hcohx hokx hcohz hokz hmb hother htid hk
    $$ Hlg Hmg Hi Hx Hz with ⟨Hlg, Hmg, Hi, %hbx, %hbz, Hx, Hz⟩
  -- ... and back out, with the ledger registered at the store's post-view
  imod ctxLbSync CurCtx.curCtx (storePost σ.wmWs rl x (σ.wmLog.length + 1)) $$ [Hlb] with Ha
  · iapply ctxLbMono CurCtx.curCtx σ.wmWs _
      (wsView_mono _ _ (storePostLe σ.wmWs rl x (σ.wmLog.length + 1))) $$ Hlb
  icases wptstoDirtyOfPt CurCtx.curCtx c _ x byte2 $$ Ha Hx with ⟨Ha, Hx⟩
  icases wptstoClOfPt CurCtx.curCtx _ z q vz $$ [Ha Hz] with ⟨Ha, Hz⟩
  · iframe Ha Hz
  imodintro
  iframe Hlg Hi
  isplitl [Ha Hmg]
  · iframe Hmg
    iapply ctxLbOfAuth CurCtx.curCtx _ $$ Ha
  isplitr
  · ipureintro; exact hbx
  isplitr
  · ipureintro; exact hbz
  iframe Hx Hz

/-! ### 2b/2c. The same lemma on both sides of a migration

Two corollaries whose statements differ only in the hart and the machine state, and whose proofs
are the same one line.  In §2c the byte `x` is still `WDirty A` in the ghost map and `B ≠ A`;
there is no upgrade lemma in either proof. -/

omit [LockExG GF] in
theorem wcsTouchA (A : CPU) (σ : Wmstate) (m : Wmsg) (x z : Int) (vz : BitVec 8) (q : DFrac)
    (akx akz : AkInfo) (tx tz : Nat) (bx bz : BitVec 8) (rl : Bool) :
    akx.akIfetch = false → wbyteOk σ akx x tx bx →
    akz.akIfetch = false → wbyteOk σ akz z tz bz →
    msgByte m x = some byte2 →
    (∀ a', a' ≠ x → msgByte m a' = none) →
    m.wmTid = some A.val →
    m.wmAk = .WCplain →
    wlogAuth (GF := GF) (σ.wmLog ++ [m]) ⊢
      wlatInterp (GF := GF) σ.wmImg σ.wmLog -∗
      ctxOwnAt (GF := GF) CurCtx.curCtx A σ.wmWs -∗
      (x ↦wpo byte1 : IProp GF) -∗ (z ↦wp{q} vz : IProp GF) -∗
      |==> (wlogAuth (GF := GF) (σ.wmLog ++ [m]) ∗
        wlatInterp (GF := GF) σ.wmImg (σ.wmLog ++ [m]) ∗
        ctxOwnAt (GF := GF) CurCtx.curCtx A (storePost σ.wmWs rl x (σ.wmLog.length + 1)) ∗
        ⌜bx = byte1⌝ ∗ ⌜bz = vz⌝ ∗
        wptstoDirty (GF := GF) CurCtx.curCtx A x byte2 ∗ (z ↦wp{q} vz : IProp GF)) :=
  wcsTouch A σ m x z byte1 vz q akx akz tx tz bx bz rl

omit [LockExG GF] in
theorem wcsTouchB (B : CPU) (σ : Wmstate) (m : Wmsg) (x z : Int) (vz : BitVec 8) (q : DFrac)
    (akx akz : AkInfo) (tx tz : Nat) (bx bz : BitVec 8) (rl : Bool) :
    akx.akIfetch = false → wbyteOk σ akx x tx bx →
    akz.akIfetch = false → wbyteOk σ akz z tz bz →
    msgByte m x = some byte2 →
    (∀ a', a' ≠ x → msgByte m a' = none) →
    m.wmTid = some B.val →
    m.wmAk = .WCplain →
    wlogAuth (GF := GF) (σ.wmLog ++ [m]) ⊢
      wlatInterp (GF := GF) σ.wmImg σ.wmLog -∗
      ctxOwnAt (GF := GF) CurCtx.curCtx B σ.wmWs -∗
      (x ↦wpo byte1 : IProp GF) -∗ (z ↦wp{q} vz : IProp GF) -∗
      |==> (wlogAuth (GF := GF) (σ.wmLog ++ [m]) ∗
        wlatInterp (GF := GF) σ.wmImg (σ.wmLog ++ [m]) ∗
        ctxOwnAt (GF := GF) CurCtx.curCtx B (storePost σ.wmWs rl x (σ.wmLog.length + 1)) ∗
        ⌜bx = byte1⌝ ∗ ⌜bz = vz⌝ ∗
        wptstoDirty (GF := GF) CurCtx.curCtx B x byte2 ∗ (z ↦wp{q} vz : IProp GF)) :=
  wcsTouch B σ m x z byte1 vz q akx akz tx tz bx bz rl

/-! ## 3. The yield, with T's facts in the frame

`WkYieldFrame` §4c/§4d at this altitude.  The framed facts appear in the premise and in the
conclusion as the same terms; the park's postcondition is one scheduler resource (`ctxParked`),
the resume's is `ctxOwnAt` at the NEW cpu, a ∀-bound argument (the `wp_next`-style re-binding).
No freeze, no thaw, no `monPred_at`, no `⌜V ≤ wsView …⌝`. -/

theorem wcsParkFrames (γ : GName) (hf : PAddr) (A : CPU) (σ σ' : Wmstate) (x z : Int)
    (vx vz : BitVec 8) (q : DFrac) :
    wQStore (some A.val) hf lockZero σ σ' →
    σ'.wmLog = σ.wmLog ++ [wwriteMsg (some A.val) .WCrel hf 4 lockZero] →
    wsBounded σ.wmWs σ.wmLog.length →
    wlogAuth (GF := GF) σ.wmLog ⊢
      wlatInterp (GF := GF) σ.wmImg σ.wmLog -∗
      wlockInv (GF := GF) γ hf (wctxBaton CurCtx.curCtx) -∗ lockedEx (GF := GF) γ A -∗
      ctxOwnAt (GF := GF) CurCtx.curCtx A σ.wmWs -∗
      -- THE FRAME
      (x ↦wpo vx : IProp GF) -∗ (z ↦wp{q} vz : IProp GF) -∗
      |==> (wlogAuth (GF := GF) σ'.wmLog ∗ wlatInterp (GF := GF) σ'.wmImg σ'.wmLog ∗
        wlockInv (GF := GF) γ hf (wctxBaton CurCtx.curCtx) ∗
        ctxParked (GF := GF) CurCtx.curCtx ∗
        (x ↦wpo vx : IProp GF) ∗ (z ↦wp{q} vz : IProp GF)) := by
  intro hQ hlog hbnd
  iintro Hlog Hi Hinv Htok Hrun Hx Hz
  imod wctxParkCore CurCtx.curCtx γ hf A σ σ' hQ hlog hbnd $$ Hlog Hi Hinv Htok Hrun
    with ⟨Hlog, Hi, Hinv, Hall⟩
  imodintro
  iframe Hlog Hi Hinv Hall Hx Hz

theorem wcsResumeFrames (γ : GName) (hf : PAddr) (B : CPU) (tid : Option Nat) (σ σ' : Wmstate)
    (x z : Int) (vx vz : BitVec 8) (q : DFrac) :
    wlogWf σ.wmLog → accWf hf 4 →
    wQAmoAq tid hf lockOne σ σ' →
    -- T2-0′ (F3′): the swap's author IS the resuming hart.
    tid = some B.val →
    (∀ j : Nat, j < 4 →
      wflatMem σ.wmImg σ.wmLog (hf + BitVec.ofNat 64 j) = some (nthByte (n := 4) lockZero j)) →
    wlatInterp (GF := GF) σ.wmImg σ.wmLog ⊢
      wlockInv (GF := GF) γ hf (wctxBaton CurCtx.curCtx) -∗
      ctxParked (GF := GF) CurCtx.curCtx -∗
      -- THE FRAME
      (x ↦wpo vx : IProp GF) -∗ (z ↦wp{q} vz : IProp GF) -∗
      |==> (wlatInterp (GF := GF) σ'.wmImg σ'.wmLog ∗
        wlockInv (GF := GF) γ hf (wctxBaton CurCtx.curCtx) ∗ lockedEx (GF := GF) γ B ∗
        ctxOwnAt (GF := GF) CurCtx.curCtx B σ'.wmWs ∗
        (x ↦wpo vx : IProp GF) ∗ (z ↦wp{q} vz : IProp GF)) := by
  intro hwf hacc hQ htid hzero
  iintro Hi Hinv Hall Hx Hz
  imod wctxResumeCore CurCtx.curCtx γ hf B tid σ σ' hwf hacc hQ htid hzero $$ Hi Hinv Hall
    with ⟨Hi, Hinv, Htok, Hrun⟩
  imodintro
  iframe Hi Hinv Htok Hrun Hx Hz

/-- ... and the composite, at the shape a caller reads: `ctxOwnAt` in, `ctxOwnAt` out,
MEMORY-SILENT.  (The two halves cannot be one lemma: `wlatInterp` is the authority over the
latest-write map, so no proposition holds it at the parking hart's state and at the resuming
hart's later state at once -- `WkStartedMp` §2's reason.) -/
theorem wcsYieldIsMemorySilent (γ : GName) (hf : PAddr) (A B : CPU) (tid : Option Nat)
    (σ σ' σ2 σ2' : Wmstate) :
    wQStore (some A.val) hf lockZero σ σ' →
    σ'.wmLog = σ.wmLog ++ [wwriteMsg (some A.val) .WCrel hf 4 lockZero] →
    wsBounded σ.wmWs σ.wmLog.length →
    wlogWf σ2.wmLog → accWf hf 4 →
    wQAmoAq tid hf lockOne σ2 σ2' →
    tid = some B.val →
    (∀ j : Nat, j < 4 →
      wflatMem σ2.wmImg σ2.wmLog (hf + BitVec.ofNat 64 j) = some (nthByte (n := 4) lockZero j)) →
    wlogAuth (GF := GF) σ.wmLog ⊢
      wlatInterp (GF := GF) σ.wmImg σ.wmLog -∗
      wlockInv (GF := GF) γ hf (wctxBaton CurCtx.curCtx) -∗ lockedEx (GF := GF) γ A -∗
      ctxOwnAt (GF := GF) CurCtx.curCtx A σ.wmWs -∗
      |==> (wlogAuth (GF := GF) σ'.wmLog ∗ wlatInterp (GF := GF) σ'.wmImg σ'.wmLog ∗
        wlockInv (GF := GF) γ hf (wctxBaton CurCtx.curCtx) ∗
        -- the whole of what crosses: a scheduler resource, and the promise that WHATEVER cpu
        -- the scheduler picks, the bundle comes back there
        (wlatInterp (GF := GF) σ2.wmImg σ2.wmLog -∗
          wlockInv (GF := GF) γ hf (wctxBaton CurCtx.curCtx) -∗
          |==> (wlatInterp (GF := GF) σ2'.wmImg σ2'.wmLog ∗
            wlockInv (GF := GF) γ hf (wctxBaton CurCtx.curCtx) ∗ lockedEx (GF := GF) γ B ∗
            ctxOwnAt (GF := GF) CurCtx.curCtx B σ2'.wmWs))) := by
  intro hQ hlog hbnd hwf hacc hQa htid hzero
  iintro Hlog Hi Hinv Htok Hrun
  imod wctxParkCore CurCtx.curCtx γ hf A σ σ' hQ hlog hbnd $$ Hlog Hi Hinv Htok Hrun
    with ⟨Hlog, Hi, Hinv, Hall⟩
  imodintro
  iframe Hlog Hi Hinv
  iintro Hi2 Hinv2
  iapply wctxResumeCore CurCtx.curCtx γ hf B tid σ2 σ2' hwf hacc hQa htid hzero $$ Hi2 Hinv2 Hall

end touch

/-! ## 4. The ping-pong's two legs, through a lock context

`WkOwnPingPong`'s function-proof-side lemmas restated.  The lock's own context ξ_L appears in the
signatures -- and ONLY there: it is bound by `wctxIsLock`'s existential (§4d).  The re-indexing
`ptsto[ξ_p] → ptsto[ξ_L]` at the release and `ptsto[ξ_L] → ptsto[ξ_q]` at the acquire happens
inside these lemmas' proofs. -/

section legs

variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [WeakGS GF] [LockExG GF]
/- ONE thread's context per lemma (each is one leg); ξ_L is the OTHER context in scope and is
therefore spelled explicitly, per `WeakVProp` §3'''s convention. -/
variable [XI : CurCtx]

/-- 4a. THE RELEASE LEG, with the private byte in the frame.  In
`WkOwnPingPong.wreleaseFlipFrame` the private byte's slot is two different propositions joined
by a `wptDirty_mono` step; here it is the same proposition, and the step is `iframe`. -/
theorem wcsReleaseLeg (γ : GName) (ξL : CtxId) (lk : PAddr) (x y : Int) (v w : BitVec 8)
    (i : CPU) (σ σ' : Wmstate) :
    wQStore (some i.val) lk lockZero σ σ' →
    σ'.wmLog = σ.wmLog ++ [wwriteMsg (some i.val) .WCrel lk 4 lockZero] →
    wsBounded σ.wmWs σ.wmLog.length →
    wlogAuth (GF := GF) σ'.wmLog ⊢
      wlatInterp (GF := GF) σ.wmImg σ.wmLog -∗
      wclockBody (GF := GF) γ lk <{ x ↦wp v }> ξL -∗
      wctxHeld (GF := GF) γ ξL CurCtx.curCtx i -∗
      ctxOwnAt (GF := GF) CurCtx.curCtx i σ.wmWs -∗
      (x ↦wpo v : IProp GF) -∗ wptstoDirty (GF := GF) CurCtx.curCtx i y w -∗
      |==> (wlogAuth (GF := GF) σ'.wmLog ∗ wlatInterp (GF := GF) σ'.wmImg σ'.wmLog ∗
        wclockBody (GF := GF) γ lk <{ x ↦wp v }> ξL ∗
        ctxOwnAt (GF := GF) CurCtx.curCtx i σ.wmWs ∗
        wptstoDirty (GF := GF) CurCtx.curCtx i y w) := by
  intro hQ hlog hbnd
  iintro Hlg Hi Hinv Hheld Hrun Hx Hy
  imod wctxReleaseByte γ ξL CurCtx.curCtx lk x v i σ σ' hQ hlog hbnd
    $$ Hlg Hi Hinv Hheld Hrun Hx with ⟨Hlg, Hi, Hinv, Hrun⟩
  imodintro
  iframe Hlg Hi Hinv Hrun Hy

/-- 4b. THE ACQUIRE LEG -- take the byte, re-own it.  `WkOwnPingPong.ppAcquireOwn` at this
altitude: the payload comes out of the lock's context and lands in the acquirer's, and the
"receive" (`ppReceive`, clean-to-owned) is `wptstoOfCl`, inside. -/
theorem wcsAcquireLeg (γ : GName) (ξL : CtxId) (lk : PAddr) (x : Int) (v : BitVec 8) (c : CPU)
    (tid : Option Nat) (σ σ' : Wmstate) :
    wlogWf σ.wmLog → accWf lk 4 →
    wQAmoAq tid lk lockOne σ σ' →
    tid = some c.val →
    (∀ j : Nat, j < 4 →
      wflatMem σ.wmImg σ.wmLog (lk + BitVec.ofNat 64 j) = some (nthByte (n := 4) lockZero j)) →
    wlatInterp (GF := GF) σ.wmImg σ.wmLog ⊢
      wclockBody (GF := GF) γ lk <{ x ↦wp v }> ξL -∗
      ctxOwnAt (GF := GF) CurCtx.curCtx c σ.wmWs -∗
      |==> (wlatInterp (GF := GF) σ'.wmImg σ'.wmLog ∗
        wclockBody (GF := GF) γ lk <{ x ↦wp v }> ξL ∗
        wctxHeld (GF := GF) γ ξL CurCtx.curCtx c ∗ ctxOwnAt (GF := GF) CurCtx.curCtx c σ'.wmWs ∗
        (x ↦wpo v : IProp GF)) := by
  intro hwf hacc hQ htid hzero
  iintro Hi Hinv Hrun
  imod wctxAcquireCore γ ξL CurCtx.curCtx lk <{ x ↦wp v }> c tid σ σ'
      hwf hacc hQ htid hzero $$ Hi Hinv Hrun with ⟨Hi, Hinv, Hheld, Hrun, HR⟩
  imodintro
  iframe Hi Hinv Hheld Hrun
  iapply wptstoOfCl CurCtx.curCtx x v
  iexact HR

/-- 4c. THE PAYOFF -- the acquire followed by the receiver's own load: every admissible
timestamp for the transferred byte carries the value the OTHER thread wrote before its release,
and the loading thread ends up owning it. -/
theorem wcsHandoffLoad (γ : GName) (ξL : CtxId) (lk : PAddr) (x : Int) (v : BitVec 8) (c : CPU)
    (tid : Option Nat) (σ σ' σn : Wmstate) (ak : AkInfo) (t' : Nat) (b : BitVec 8) :
    wlogWf σ.wmLog → accWf lk 4 →
    wQAmoAq tid lk lockOne σ σ' →
    tid = some c.val →
    (∀ j : Nat, j < 4 →
      wflatMem σ.wmImg σ.wmLog (lk + BitVec.ofNat 64 j) = some (nthByte (n := 4) lockZero j)) →
    ak.akIfetch = false →
    σn.wmImg = σ'.wmImg → σn.wmLog = σ'.wmLog →
    wsLe σ'.wmWs σn.wmWs →
    wbyteOk σn ak x t' b →
    wlatInterp (GF := GF) σ.wmImg σ.wmLog ⊢
      wclockBody (GF := GF) γ lk <{ x ↦wp v }> ξL -∗
      ctxOwnAt (GF := GF) CurCtx.curCtx c σ.wmWs -∗
      |==> (wlatInterp (GF := GF) σn.wmImg σn.wmLog ∗
        wclockBody (GF := GF) γ lk <{ x ↦wp v }> ξL ∗
        wctxHeld (GF := GF) γ ξL CurCtx.curCtx c ∗ ctxOwnAt (GF := GF) CurCtx.curCtx c σn.wmWs ∗
        ⌜b = v⌝ ∗ (x ↦wpo v : IProp GF)) := by
  intro hwf hacc hQ htid hzero hcoh himg hlog hle hok
  have hlat : wlatInterp (GF := GF) σ'.wmImg σ'.wmLog ⊢
      wlatInterp (GF := GF) σn.wmImg σn.wmLog := by rw [himg, hlog]
  iintro Hi Hinv Hrun
  imod wcsAcquireLeg γ ξL lk x v c tid σ σ' hwf hacc hQ htid hzero $$ Hi Hinv Hrun
    with ⟨Hi, Hinv, Hheld, Hrun, Hx⟩
  ihave Hrun := ctxOwnAtMono CurCtx.curCtx c _ _ hle $$ Hrun
  ihave Hi := hlat $$ Hi
  imod wptstoLoadRule CurCtx.curCtx c σn σn ak x v t' b hcoh hok rfl rfl
      (fun _ => Nat.le_refl _) $$ [Hi Hrun Hx] with ⟨%hb, Hi, Hrun, Hx⟩
  · iframe Hi Hrun Hx
  imodintro
  iframe Hi Hinv Hheld Hrun Hx
  ipureintro
  exact hb

omit XI in
/-- 4d. ξ_L IS INTERNAL -- the client's handle, and its one destruct.  The payload is written
with bare `↦wp` inside `<{ … }>` and mentions no context; the lock's context is the handle's
existential, opened once at the top of a function proof. -/
theorem wcsIsLockInternal (γ : GName) (lk : PAddr) (x : Int) (v : BitVec 8) :
    wctxIsLock (hlc := hlc) (GF := GF) γ lk <{ x ↦wp v }> ⊢
      ∃ ξL : CtxId, inv wlockN (wclockBody (GF := GF) γ lk <{ x ↦wp v }> ξL) :=
  .rfl

/-! ## 5. The three arms of φ, on the `IProp` surface

`WkOwnPingPong` §6 restated: the fetch window (text, never written), the owned byte (paid by the
points-to itself, whichever hart dirtied it), and the lock word (clean inside the invariant).
The migration invariant comes out of `ctxOwnAt`; nothing else changed. -/

omit [LockExG GF] [MachGS hlc GF] in
theorem wcsPhiThreeArms (c : CPU) (img : GMapF PAddr (BitVec 8)) (log : List Wmsg) (ws : Wstate)
    (pcb x lkb : Int) (vx : BitVec 8) (dq : DFrac) (t : Nat) (vl : BitVec 8) :
    latestTs log pcb = 0 →
    wlogAuth (GF := GF) log ⊢ ctxOwnAt (GF := GF) CurCtx.curCtx c ws -∗
      wlatInterp (GF := GF) img log -∗
      (x ↦wpo vx : IProp GF) -∗ wlatPointsto (GF := GF) lkb dq t vl -∗
      ⌜nvOk log c pcb ∧ nvOk log c x ∧ nvOk log c lkb⌝ := by
  intro htext
  unfold ctxOwnAt
  iintro Hlg ⟨-, Hmg⟩ Hi Hx Hlk
  icases keepPure (wand_intro (nvOkOfPointsto img log c lkb dq t vl)) $$ Hi Hlk
    with ⟨%hnl, Hi, -⟩
  ihave %hnx := nvOkOfWptstoCur c x vx img log $$ [Hlg Hmg Hi Hx]
  · iframe Hlg Hmg Hi Hx
  ipureintro
  exact ⟨nvOkUnwritten log c pcb htext, hnx, hnl⟩

end legs

/-! ## 6. The park at the WP altitude, in the new surface

`WkYieldFrame` §5's rule with the handoff flag's payload changed from the raw view baton `⊒V` to
the parking context's own LEDGER (`WeakCtxLock.wctxBaton`).  What the park hands the flag is then
exactly what the resume needs to rebuild `ctxOwnAt`.  THE CALLBACK IS `WkYieldFrame.wyieldParkCb`
VERBATIM; the diff against `wwpYieldPark` is ONE premise (the ledger that travels) and ONE line
of proof (the deposit is that authority rather than a view receipt). -/

section wpPark

variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [WeakGS GF] [LockExG GF]

theorem wwpCtxYieldPark (gen : Nat) (cpu : CPU) (ξ : CtxId) (V : View) (γ : GName) (hf : PAddr)
    (pc : BitVec 64) (akf : AkInfo) (pf : PAddr) (nf : Nat) (akw : AkInfo) :
    gen = 0 →
    accWf pc 4 →
    accWf hf 4 →
    -- the handoff store is a plain `sw`, not an AMO
    akw.akLatest = false →
    (∀ a : Int, weffTouches (.WEread akf pf nf) a → ∃ j, j < 4 ∧ a = WeakInterp.accAddr pc j) →
    inv wlockN (wlockInv (GF := GF) γ hf (wctxBaton ξ)) ⊢
      lockedEx (GF := GF) γ cpu -∗
      ctxAuth (GF := GF) ξ V -∗
      ctxMigr (GF := GF) ξ cpu -∗
      wyieldParkCb (hlc := hlc) gen cpu ξ V pc
        (wPEffText (some cpu.val) [.WEread akf pf nf, .WEwrite akw hf 4 lockZero]) -∗
      wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu) := by
  intro hgen haccpc hacchf hlatw hfetch
  have hfoot : ∀ a : Int, weffsTouch [.WEread akf pf nf, .WEwrite akw hf 4 lockZero] a →
      (∃ j, j < 4 ∧ a = WeakInterp.accAddr pc j) ∨ (∃ j, j < 4 ∧ a = WeakInterp.accAddr hf j) := by
    intro a ha
    rcases weffsTouchCons _ _ a ha with ha | ha
    · exact .inl (hfetch a ha)
    · exact .inr (weffsTouchWrite1 _ hf _ _ a ha)
  have hcert := wstepCertText _ pc _ _ (fetchInWindowStore pc akf pf nf akw hf lockZero hfetch)
    (fetchFreshStore akf pf nf akw hf lockZero)
    (wstepCertFr _ pc _ _ (wcertStore cpu.val pc akf pf nf akw hf lockZero))
  iintro #Hinv Htok Hau Hmg Hk
  unfold wyieldParkCb
  iapply wpWinstr gen cpu pc _ _ hgen haccpc hcert
  iintro %σ Hσ
  icases (wmstateInterpSplit cpu σ).mp $$ Hσ with ⟨Hlat, Hrest⟩
  icases keepPure1 (wmstateRestFacts cpu σ) $$ Hrest with ⟨%hfacts, Hrest⟩
  icases keepPure1 (wmstateRestNv cpu σ) $$ Hrest with ⟨%hnvσ, Hrest⟩
  obtain ⟨hbnd, _⟩ := hfacts
  imod (inv_acc (E := ⊤) (N := wlockN) (P := wlockInv (GF := GF) γ hf (wctxBaton ξ))
    CoPset.subseteq_top) $$ Hinv with ⟨Hbody, Hclose⟩
  imod Hk $$ %σ Hlat Hrest
    with ⟨%hpc, %htext, %hP, %hnvpc, %hrelp, %hV, Hlat, %t0, %t1, %hex0, %hex1, Hcont⟩
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
  have hlog : σ'.wmLog = σ.wmLog ++ [wwriteMsg (some cpu.val) .WCrel hf 4 lockZero] :=
    wQEffStoreRel _ akf pf nf akw hf lockZero σ σ' hlatw hrelp hQeff
  have hmint : wlogAuth (GF := GF) σ'.wmLog ⊢
      wlogAuth (GF := GF) σ'.wmLog ∗ pubFloor (GF := GF) cpu (σ.wmLog.length + 1) := by
    rw [hlog]; exact pubFloorMint _ _ cpu rfl rfl
  have hlen : σ'.wmLog.length ≤ σ.wmLog.length + 1 := by
    rw [hlog, List.length_append, List.length_singleton]; exact Nat.le_refl _
  -- the continuation FIRST: the log authority the mint rides lives in its remainder
  imod Hcont $$ %tick %σ' %hpost with ⟨Hrest, Hk2⟩
  icases wmstateRestNonvLog cpu σ' $$ Hrest with ⟨Hlogauth, Hrest⟩
  icases hmint $$ Hlogauth with ⟨Hlogauth, #Hpf⟩
  -- THE PARK on the migration invariant, with no byte named
  icases ctxMigrPark ξ cpu σ'.wmLog (σ.wmLog.length + 1) hlen $$ [Hlogauth Hmg]
    with ⟨Hlogauth, Hall⟩
  · iframe Hlogauth Hpf Hmg
  ihave Hwp := Hk2 $$ Hall
  -- the release itself, and the φ payment -- the deposit is the context's LEDGER
  imod wreleaseCore γ hf (wctxBaton ξ) cpu (some cpu.val) σ σ' hQ rfl hrelp hbnd
    $$ Hlat Hbody Htok [Hau] with ⟨Hlat, Hbody⟩
  · unfold vwpHold wctxBaton
    iapply wledgerPayIntro ξ iprop(emp) V (wsView σ.wmWs) hV $$ Hau
    iempintro
  icases keepPure (nvOkWlockInv cpu σ'.wmImg σ'.wmLog γ hf (wctxBaton ξ)) $$ Hlat Hbody
    with ⟨%hnvhf, Hlat, Hbody⟩
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
    · exact hnvhf j hj
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

end wpPark

end Weak
