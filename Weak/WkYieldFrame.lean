/-
Weak: **the framing pattern: ownership across a `yield`** (φ-upgrade §1.5–§1.7) -- a thread's
ownership facts FRAME AROUND a call to `yield`: they appear in neither its precondition nor its
postcondition, while `yield` fences on the old CPU before migrating and acquires on the new CPU
before returning, and the only memory-visible thing it hands back is the context's migration
invariant (parked) plus one view inequality.

Rocq: `iris/WkYieldFrame.v` @ xxvzwolszwmp.

The Rocq header, in substance (Rocq vocabulary).

THE PROGRAM.

    thread T, running on hart A                  ... resumed on hart B
      sb  1, 0(x)      # x := 1   (D-A)
                       # z ↦w{q} vz in hand, CLEAN and untouched
      lb  a5, 0(x)     # reads 1   \
      sb  2, 0(x)      # x := 2     > §4a's ACCESS BLOCK, before the yield
      lb  a5, 0(z)     # reads vz  /
      call yield  --------------------------->
         fence rw,w    # arms w_relp                1: amoswap.w.aq a5,a4,0(hf)
         sw  zero,0(hf) # handoff release ========>     bnez a5,1b
                                                     ret
      <--------------------------------------------------
      lb  a5, 0(x)     # reads 1   \
      sb  2, 0(x)      # x := 2     > §4a's ACCESS BLOCK, AFTER the yield --
      lb  a5, 0(z)     # reads vz  /  the SAME lemma, the same script

WHAT MAKES IT WORK.  (1) THE FRAME IS LITERAL: a thread's facts are frozen at its own index
(`monPred_at P V`, objective), which the yield lemmas do not mention; `wyfParkFrames` is
`wyieldParkCore` plus `iframe`.  (2) WHAT COMES BACK IS TWO THINGS: the context's migration
invariant in its PARKED form `ctxMigrAll ξ` (a scheduler resource), and `V ≤ wsView σ'.wmWs`
(delivered by the handoff flag's lock payload, the BARE VIEW RECEIPT `wbaton V = ⊒V`).  Stage 1.5's
third thing, `pub_covers_view`, is gone -- that is the whole of Stage 1.6.  (3) BOTH FACTS FRAME
FOR FREE, AND BY THE SAME LINE: the clean `z ↦w{q} vz` and the owned `x ↦wo 1` are re-established
at B by `vwpHold_intro` and the view fact alone; the retarget (`wownCtxRetarget`) fires inside the
store leaf.  (4) φ COSTS NOTHING NEW: `nvOk_of_wptOwn_cur` pays for a foreign-dirty but published
byte exactly as for an unmigrated thread.  §2 mints the publication floor at the handoff release
(`pubFloorMint`) and parks the migration invariant (`ctxMigrPark`); §3 re-forms it at the resuming
hart (`ctxMigrAllRun`).  THE CONTEXT IS AMBIENT in §4 (one `[CurCtx]` instance on both sides of the
migration -- a thread's context is invariant across a yield, its hart is not); `ξ` survives
explicitly only in §2/§3/§5, which quantify over the context they park.

(The Rocq closing note, "WHAT A PORTED PROOF TAKES FROM THIS FILE": freeze at the own index and
frame `monPred_at P V` around the call; `yield`'s spec carries and returns the scheduler's
resources only, the invariant parked -- at the port the view half becomes
`WeakCtx.ctx_view_lb ξ V`; on the far side every framed fact is thawed by `vwpHold_intro` and the
index fact, with no upgrade step; the mint site is the handoff release store, fed by
`akLatest akw = false` and the `wRelp` fact through `wQEffStoreRel`.)

KERNEL IMAGE.  This file states NO kernel address or kernel code: the program above is abstract
(`pc`, `hf`, `x`, `z` are parameters), so there is no drift against the Lean kernel image
(`Xv6/KernelImage.lean`, xv6 b72cbac1) to record.

**Deviations from Rocq.**

1. NAMES: the tree's camelCase (map below); none is in the duplicated-name table.  Vocabulary as
   `Weak/WkOwnPingPong.lean` deviation 1 (`wm_log σ` ↦ `σ.wmLog`, `fin_to_nat i` ↦ `i.val`,
   `S (length l)` ↦ `l.length + 1`, `Arch.pa` ↦ `PAddr`, `bv n` ↦ `BitVec n`, `Z` ↦ `Int`,
   `N` ↦ `Nat`, `ak_coh` ↦ `akIfetch`, `ak_latest` ↦ `akLatest`, `w_relp` ↦ `wRelp`,
   `wflat … !! pa_add a j` ↦ `wflatMem … (a + BitVec.ofNat 64 j)`, `locked γ i` ↦
   `lockedEx γ i`, `cur_ctx` ↦ `CurCtx.curCtx`, `register_lookup PC` ↦ `.wmRegs .PC`,
   `mstate` ↦ `ExecSt`, `WWP Loop` ↦ `wwpTriv ⊤ (WExpr.loop gen cpu)`, ambient
   `GenId`/`CpuId` ↦ explicit `gen`/`cpu`, so `wyieldParkCb` takes `gen cpu` first).
   `byte1`/`byte2` (Rocq `mword_of_int 1/2 : mword 8`) are `(1 : BitVec 8)`/`(2 : BitVec 8)`.
2. CONTEXT: Rocq `{!riscvGS Σ, !weakGS Σ, !lockG Σ}` is `[WeakGS GF] [LockExG GF]` (+ `{hlc}
   [MachGS hlc GF]` in §5), only what each statement uses (`omit` elsewhere); `{XI : CurCtx}` is
   `[XI : CurCtx]`.  The baton section needs no `WeakGS`.
3. STATEMENT SHAPES: WeakLock's curried form (Rocq `A -∗ B ==∗ C` is `A ⊢ B -∗ |==> C`); a lemma
   with no spatial premise (`wbatonIntro`) is `⊢ …`.  Rocq `⊑` on views is `≤`.
4. `wbaton` gets a `MakeMonPredAt` instance (Lean-only, `makeMonPredAt_wbaton`), per the MonPred
   convention for `def`-level `VProp`s.
5. O2, THE TEXT PIN (WeakAcquire deviations 3/4, as `WkOwnPingPong.wrelOwnCb`): `wyieldParkCb`
   hands over `pinnedRead ∧ fetchPinned` per text byte (Rocq `pinned_read` only), and
   `wwpYieldPark`/`wwpYieldResume` owe `wPEffText` (Rocq `wP_eff` verbatim); the certificate is
   `wstepCertText … (wstepCertFr … (wcertStore …))`.
6. The load rules' view-floor premise (Rocq `ltac:(lia)`) is `Nat.le_refl _`; Rocq's
   `rewrite -Himg -Hlg` in the proof context (`wyfStoreAndUse`, `wyfResumeAndUse`) is a rewrite of
   the intermediate entailment (`wlatInterp` / `wlogAuth` at the substituted state).
7. Rocq's `Print Assumptions` has no Lean counterpart (the lint bans axioms).

**Rocq → Lean name map.**  `wbaton` `wbaton`, `wbaton_at` `wbatonAt`, `wbaton_intro`
`wbatonIntro`, `monPred_at_ent` `monPredAtEnt`, `byte1` `byte1`, `byte2` `byte2`,
`wyield_park_core` `wyieldParkCore`, `wyield_resume_core` `wyieldResumeCore`, `wyf_touch`
`wyfTouch`, `wyf_store_and_use` `wyfStoreAndUse`, `wyf_park_frames` `wyfParkFrames`,
`wyf_resume_and_use` `wyfResumeAndUse`, `wyf_phi_migrated` `wyfPhiMigrated`, `wyield_park_cb`
`wyieldParkCb`, `wwp_yield_park` `wwpYieldPark`, `wwp_yield_resume` `wwpYieldResume`.
Lean-only: `makeMonPredAt_wbaton` (16 Rocq + 1 = 17).

**Dropped lemmas.**  None.
-/
import Weak.WkOwnPingPong
import MachCSL.MonPredExtra

namespace Weak

open Iris Iris.BI Iris.BI.MonPred Iris.ProofMode Iris.Std Iris.Std.PartialMap
open Iris.Std.LawfulPartialMap MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D LeanRV64D.Functions
open Wcds

/-! ## 1. The scheduler baton -- the handoff flag's payload -/

section baton

variable {GF : BundledGFunctors}

/-- The handoff flag's lock payload: a bare view receipt, no memory. -/
def wbaton (V : View) : VProp GF := iprop(⊒V)

set_option synthInstance.checkSynthOrder false in
/-- Lean-only (deviation 4): the proofmode evaluates the baton at an index to the inequality. -/
instance makeMonPredAt_wbaton (d : MakeMonPredAt.Kind) (i V : View) :
    MakeMonPredAt d i (wbaton (GF := GF) V) (iprop(⌜V ≤ i⌝)) where
  make_monPred_at := .rfl

theorem wbatonAt (V : View) (ws : Wstate) :
    vwpHold (wbaton (GF := GF) V) ws ⊣⊢ ⌜V ≤ wsView ws⌝ :=
  vwpHold_seen V ws

theorem wbatonIntro (V : View) (ws : Wstate) :
    V ≤ wsView ws → ⊢ vwpHold (wbaton (GF := GF) V) ws :=
  fun h => (pure_intro h).trans (wbatonAt V ws).mpr

/-- A `VProp` entailment applied at a FROZEN index. -/
theorem monPredAtEnt (P Q : VProp GF) (V : View) :
    (P ⊢ Q) → P.monPred_at V ⊢ Q.monPred_at V :=
  fun h => entails_at.mp h V

end baton

/-- The two byte values the thread writes. -/
def byte1 : BitVec 8 := 1
def byte2 : BitVec 8 := 2

/-! ## 2./3. `yield_park` / `yield_resume` -- the scheduler's two halves -/

section yield

variable {GF : BundledGFunctors} [WeakGS GF] [LockExG GF]

/-- THE A-SIDE: the handoff release, the floor mint, the park.  No points-to anywhere. -/
theorem wyieldParkCore (ξ : CtxId) (γ : GName) (hf : PAddr) (V : View) (i : CPU)
    (σ σ' : Wmstate) :
    wQStore (some i.val) hf lockZero σ σ' →
    σ'.wmLog = σ.wmLog ++ [wwriteMsg (some i.val) .WCrel hf 4 lockZero] →
    wsBounded σ.wmWs σ.wmLog.length →
    -- the parking hart has observed `V` -- a fact about its INDEX
    V ≤ wsView σ.wmWs →
    wlogAuth (GF := GF) σ.wmLog ⊢ ctxMigr (GF := GF) ξ i -∗
      wlatInterp (GF := GF) σ.wmImg σ.wmLog -∗
      wlockInv (GF := GF) γ hf (wbaton V) -∗
      lockedEx (GF := GF) γ i -∗
      |==> (wlogAuth (GF := GF) σ'.wmLog ∗ ctxMigrAll (GF := GF) ξ ∗
        wlatInterp (GF := GF) σ'.wmImg σ'.wmLog ∗ wlockInv (GF := GF) γ hf (wbaton V)) := by
  intro heff hlog hbnd hV
  obtain ⟨himg, -, -, -⟩ := heff
  have hR : ⊢ (wbaton (GF := GF) V).monPred_at (viewScl (σ.wmLog.length + 1)) :=
    (wbatonIntro V σ.wmWs hV).trans (wwpReleaseDeposit _ σ hbnd)
  iintro Hlg Hmg Hi Hinv Htok
  unfold wlockInv
  icases Hinv with ⟨%st, %t, %w, Hw, Ha, -⟩
  icases keepPure (lockedExState γ st i) $$ Ha Htok with ⟨%hst, Ha, Htok⟩
  subst hst
  dsimp only [tidOf]
  -- the flag word's bundle moves to the fresh top and stays CLEAN
  imod wlat4LStoreGen (some i.val) .WCrel σ σ' hf t w lockZero (some i.val) none
      (wlockShapedRel _ .WCrel hf (by decide)) (altStepRelMsg i .WCrel hf) himg hlog $$ Hi Hw
      with ⟨Hi, Hw⟩
  rw [hlog]
  -- THE MINT
  imod wlogUpdate σ.wmLog [wwriteMsg (some i.val) .WCrel hf 4 lockZero] $$ Hlg with Hlg
  icases pubFloorMint σ.wmLog (wwriteMsg (some i.val) .WCrel hf 4 lockZero) i rfl rfl $$ Hlg
    with ⟨Hlg, #Hpf⟩
  -- THE PARK
  icases ctxMigrPark ξ i (σ.wmLog ++ [wwriteMsg (some i.val) .WCrel hf 4 lockZero])
      (σ.wmLog.length + 1)
      (by rw [List.length_append, List.length_singleton]; exact Nat.le_refl _)
      $$ [Hlg Hmg] with ⟨Hlg, Hall⟩
  · iframe Hlg Hpf Hmg
  -- the baton: the parking hart's own index, frozen at the store's timestamp
  ihave HR := hR
  imod lockClrcpu γ (some (i, true)) i $$ Ha Htok with ⟨-, Ha, Hpre⟩
  imod lockGive γ (some (i, false)) i $$ Ha Hpre with ⟨-, Ha, Hfrag⟩
  imodintro
  iframe Hlg Hall Hi
  iexists none, σ.wmLog.length + 1, lockZero
  dsimp only [tidOf]
  iframe Hw Ha
  ileft
  iframe Hfrag HR
  ipureintro
  exact ⟨rfl, rfl⟩

/-- THE B-SIDE: `wacquireCore` at the baton payload, plus the one line re-forming the
migration invariant at the resuming hart. -/
theorem wyieldResumeCore (ξ : CtxId) (γ : GName) (hf : PAddr) (V : View) (i : CPU)
    (tid : Option Nat) (σ σ' : Wmstate) :
    wlogWf σ.wmLog → accWf hf 4 →
    wQAmoAq tid hf lockOne σ σ' →
    -- T2-0′ (F3′): the swap's author IS the resuming hart
    tid = some i.val →
    -- the spin loop's successful attempt: the flag word read 0
    (∀ j : Nat, j < 4 →
      wflatMem σ.wmImg σ.wmLog (hf + BitVec.ofNat 64 j) = some (nthByte (n := 4) lockZero j)) →
    wlatInterp (GF := GF) σ.wmImg σ.wmLog ⊢
      ctxMigrAll (GF := GF) ξ -∗
      wlockInv (GF := GF) γ hf (wbaton V) -∗
      |==> (wlatInterp (GF := GF) σ'.wmImg σ'.wmLog ∗ wlockInv (GF := GF) γ hf (wbaton V) ∗
        lockedEx (GF := GF) γ i ∗ ctxMigr (GF := GF) ξ i ∗ ⌜V ≤ wsView σ'.wmWs⌝) := by
  intro hwf hacc hQ htid hzero
  iintro Hi Hall Hinv
  icases wacquireCore γ hf (wbaton V) i tid σ σ' hwf hacc hQ htid $$ Hi Hinv
    with ⟨%v0, %hflat, Hupd⟩
  have hv : lockZero = v0 := wflatWordAgree σ hf lockZero v0 hzero hflat
  imod Hupd with ⟨Hi, Hbody, Harm⟩
  icases Harm with (⟨-, HR, Htok⟩ | %hne)
  · icases (wbatonAt V σ'.wmWs).mp $$ HR with %hV
    imodintro
    iframe Hi Hbody Htok
    isplitl [Hall]
    · iapply ctxMigrAllRun ξ i
      iexact Hall
    · ipureintro; exact hV
  · exact absurd hv.symm hne

end yield

/-! ## 4. The example -- thread T's own facts, framed around the yield -/

section yieldExample

variable {GF : BundledGFunctors} [WeakGS GF] [LockExG GF] [XI : CurCtx]

omit [LockExG GF] in
/-- 4a. THE ACCESS BLOCK -- `load x; x := 2; load z` -- applied unchanged on hart A before the
yield (§4b) and on hart B after it (§4d). -/
theorem wyfTouch (c : CPU) (σ : Wmstate) (m : Wmsg) (x z : Int) (vx vz : BitVec 8) (q : DFrac)
    (akx akz : AkInfo) (tx tz : Nat) (bx bz : BitVec 8) (rl : Bool) :
    akx.akIfetch = false → wbyteOk σ akx x tx bx →
    akz.akIfetch = false → wbyteOk σ akz z tz bz →
    msgByte m x = some byte2 →
    (∀ a', a' ≠ x → msgByte m a' = none) →
    m.wmTid = some c.val →
    m.wmAk = .WCplain →
    wlogAuth (GF := GF) (σ.wmLog ++ [m]) ⊢ ctxMigr (GF := GF) CurCtx.curCtx c -∗
      wlatInterp (GF := GF) σ.wmImg σ.wmLog -∗
      vwpHold (x ↦wo vx : VProp GF) σ.wmWs -∗
      vwpHold (z ↦w{q} vz : VProp GF) σ.wmWs -∗
      |==> (wlogAuth (GF := GF) (σ.wmLog ++ [m]) ∗ ctxMigr (GF := GF) CurCtx.curCtx c ∗
        wlatInterp (GF := GF) σ.wmImg (σ.wmLog ++ [m]) ∗
        ⌜bx = vx⌝ ∗ ⌜bz = vz⌝ ∗
        vwpHold (wptDirty (GF := GF) CurCtx.curCtx c x byte2)
          (storePost σ.wmWs rl x (σ.wmLog.length + 1)) ∗
        vwpHold (z ↦w{q} vz : VProp GF) (storePost σ.wmWs rl x (σ.wmLog.length + 1))) := by
  intro hcohx hokx hcohz hokz hmb hother htid hk
  iintro Hlg Hmg Hi Hx Hz
  -- load `x`: THE OWNED LOAD RULE, and nothing else
  icases wpt_load_rule_own_cur (GF := GF) σ σ akx x vx tx bx hcohx hokx rfl rfl (Nat.le_refl _)
    $$ [Hi Hx] with ⟨%hbx, Hi, Hx⟩
  · iframe Hi Hx
  -- load `z`: the ordinary clean rule
  icases wpt_load_rule (GF := GF) σ σ akz z q vz tz bz hcohz hokz rfl rfl (Nat.le_refl _)
    $$ [Hi Hz] with ⟨%hbz, Hi, Hz⟩
  · iframe Hi Hz
  -- `x := 2`: the ordinary owned store
  imod wpt_store_post_dirty_cur c σ m x vx byte2 rl hmb hother htid hk $$ [Hlg Hmg Hi Hx]
    with ⟨Hlg, Hmg, Hi, Hx⟩
  · iframe Hlg Hmg Hi Hx
  imodintro
  iframe Hlg Hmg Hi Hx
  isplitr
  · ipureintro; exact hbx
  isplitr
  · ipureintro; exact hbz
  iapply vwpHold_mono (z ↦w{q} vz : VProp GF) (storePostLe σ.wmWs rl x (σ.wmLog.length + 1))
  iexact Hz

omit [LockExG GF] in
/-- 4b. ON HART A, BEFORE THE YIELD: dirty `x`, then use it. -/
theorem wyfStoreAndUse (A : CPU) (σ σ2 : Wmstate) (m m2 : Wmsg) (x z : Int) (v0 vz : BitVec 8)
    (q : DFrac) (rl : Bool) (akx akz : AkInfo) (tx tz : Nat) (bx bz : BitVec 8) :
    msgByte m x = some byte1 →
    (∀ a', a' ≠ x → msgByte m a' = none) →
    m.wmTid = some A.val →
    m.wmAk = .WCplain →
    -- the access block's state has the same memory as the store's post-state
    σ2.wmImg = σ.wmImg → σ2.wmLog = σ.wmLog ++ [m] →
    wsLe (storePost σ.wmWs rl x (σ.wmLog.length + 1)) σ2.wmWs →
    akx.akIfetch = false → wbyteOk σ2 akx x tx bx →
    akz.akIfetch = false → wbyteOk σ2 akz z tz bz →
    msgByte m2 x = some byte2 →
    (∀ a', a' ≠ x → msgByte m2 a' = none) →
    m2.wmTid = some A.val →
    m2.wmAk = .WCplain →
    wlogAuth (GF := GF) (σ.wmLog ++ [m]) ⊢ ctxMigr (GF := GF) CurCtx.curCtx A -∗
      wlogAuth (GF := GF) (σ2.wmLog ++ [m2]) -∗
      wlatInterp (GF := GF) σ.wmImg σ.wmLog -∗
      vwpHold (x ↦wo v0 : VProp GF) σ.wmWs -∗
      vwpHold (z ↦w{q} vz : VProp GF) σ.wmWs -∗
      |==> (wlogAuth (GF := GF) (σ2.wmLog ++ [m2]) ∗ ctxMigr (GF := GF) CurCtx.curCtx A ∗
        wlatInterp (GF := GF) σ2.wmImg (σ2.wmLog ++ [m2]) ∗
        ⌜bx = byte1⌝ ∗ ⌜bz = vz⌝ ∗
        vwpHold (wptDirty (GF := GF) CurCtx.curCtx A x byte2)
          (storePost σ2.wmWs rl x (σ2.wmLog.length + 1)) ∗
        vwpHold (z ↦w{q} vz : VProp GF) (storePost σ2.wmWs rl x (σ2.wmLog.length + 1))) := by
  intro hma hother htid hk himg hlg hle hcohx hokx hcohz hokz hmb hother2 htid2 hk2
  have hlat : wlatInterp (GF := GF) σ.wmImg (σ.wmLog ++ [m]) ⊢
      wlatInterp (GF := GF) σ2.wmImg σ2.wmLog := by rw [himg, hlg]
  iintro Hlg1 Hmg Hlg2 Hi Hx Hz
  imod wpt_store_post_dirty_cur A σ m x v0 byte1 rl hma hother htid hk $$ [Hlg1 Hmg Hi Hx]
    with ⟨-, Hmg, Hi, Hx⟩
  · iframe Hlg1 Hmg Hi Hx
  -- the clean fact rides the same step's view growth, and nothing else
  ihave Hz := vwpHold_mono (z ↦w{q} vz : VProp GF) (storePostLe σ.wmWs rl x (σ.wmLog.length + 1))
    $$ Hz
  ihave Hi := hlat $$ Hi
  ihave Hx := vwpHold_mono _ hle $$ Hx
  ihave Hz := vwpHold_mono _ hle $$ Hz
  ihave Hx := WkOwnPingPong.vwpHold_ent _ _ σ2.wmWs (wptDirty_own CurCtx.curCtx A x byte1) $$ Hx
  -- THE ACCESS BLOCK, ON HART A
  iapply wyfTouch A σ2 m2 x z byte1 vz q akx akz tx tz bx bz rl hcohx hokx hcohz hokz hmb hother2
    htid2 hk2 $$ Hlg2 Hmg Hi Hx Hz

/-- 4c. THE PARK, WITH T'S FACTS IN THE FRAME: `wyieldParkCore` with two conjuncts threaded from
premise to conclusion, untouched. -/
theorem wyfParkFrames (γ : GName) (hf : PAddr) (A : CPU) (σ σ' : Wmstate) (x z : Int)
    (vx vz : BitVec 8) (q : DFrac) :
    wQStore (some A.val) hf lockZero σ σ' →
    σ'.wmLog = σ.wmLog ++ [wwriteMsg (some A.val) .WCrel hf 4 lockZero] →
    wsBounded σ.wmWs σ.wmLog.length →
    wlogAuth (GF := GF) σ.wmLog ⊢ ctxMigr (GF := GF) CurCtx.curCtx A -∗
      wlatInterp (GF := GF) σ.wmImg σ.wmLog -∗
      wlockInv (GF := GF) γ hf (wbaton (wsView σ.wmWs)) -∗
      lockedEx (GF := GF) γ A -∗
      -- THE FRAME
      (x ↦wo vx : VProp GF).monPred_at (wsView σ.wmWs) -∗
      (z ↦w{q} vz : VProp GF).monPred_at (wsView σ.wmWs) -∗
      |==> (wlogAuth (GF := GF) σ'.wmLog ∗ ctxMigrAll (GF := GF) CurCtx.curCtx ∗
        wlatInterp (GF := GF) σ'.wmImg σ'.wmLog ∗
        wlockInv (GF := GF) γ hf (wbaton (wsView σ.wmWs)) ∗
        (x ↦wo vx : VProp GF).monPred_at (wsView σ.wmWs) ∗
        (z ↦w{q} vz : VProp GF).monPred_at (wsView σ.wmWs)) := by
  intro hQ hlog hbnd
  iintro Hlog Hmg Hi Hinv Htok Hx Hz
  -- the scheduler lemma is `ξ`-EXPLICIT: the seam is this one argument
  imod wyieldParkCore CurCtx.curCtx γ hf (wsView σ.wmWs) A σ σ' hQ hlog hbnd (fun _ => Nat.le_refl _)
    $$ Hlog Hmg Hi Hinv Htok with ⟨Hlog, Hall, Hi, Hinv⟩
  imodintro
  iframe Hlog Hall Hi Hinv Hx Hz

/-- 4d. ON HART B: resume, then USE the framed facts -- both thawed by the view alone. -/
theorem wyfResumeAndUse (γ : GName) (hf : PAddr) (V : View) (B : CPU) (tid : Option Nat)
    (σ σ' σn : Wmstate) (mB : Wmsg) (x z : Int) (vz : BitVec 8) (q : DFrac)
    (akx akz : AkInfo) (tx tz : Nat) (bx bz : BitVec 8) (rl : Bool) :
    -- the resume
    wlogWf σ.wmLog → accWf hf 4 →
    wQAmoAq tid hf lockOne σ σ' →
    tid = some B.val →
    (∀ j : Nat, j < 4 →
      wflatMem σ.wmImg σ.wmLog (hf + BitVec.ofNat 64 j) = some (nthByte (n := 4) lockZero j)) →
    -- and then T's own three accesses, at a state with the same memory
    σn.wmImg = σ'.wmImg → σn.wmLog = σ'.wmLog →
    wsLe σ'.wmWs σn.wmWs →
    akx.akIfetch = false → wbyteOk σn akx x tx bx →
    akz.akIfetch = false → wbyteOk σn akz z tz bz →
    msgByte mB x = some byte2 →
    (∀ a', a' ≠ x → msgByte mB a' = none) →
    mB.wmTid = some B.val →
    mB.wmAk = .WCplain →
    wlogAuth (GF := GF) (σn.wmLog ++ [mB]) ⊢
      -- the ONLY things the yield handed back
      ctxMigrAll (GF := GF) CurCtx.curCtx -∗
      wlatInterp (GF := GF) σ.wmImg σ.wmLog -∗
      wlockInv (GF := GF) γ hf (wbaton V) -∗
      -- the FRAMED facts, still frozen at the parking index
      (x ↦wo byte1 : VProp GF).monPred_at V -∗
      (z ↦w{q} vz : VProp GF).monPred_at V -∗
      |==> (wlogAuth (GF := GF) (σn.wmLog ++ [mB]) ∗ ctxMigr (GF := GF) CurCtx.curCtx B ∗
        wlatInterp (GF := GF) σn.wmImg (σn.wmLog ++ [mB]) ∗
        wlockInv (GF := GF) γ hf (wbaton V) ∗ lockedEx (GF := GF) γ B ∗
        ⌜bx = byte1⌝ ∗ ⌜bz = vz⌝ ∗
        vwpHold (wptDirty (GF := GF) CurCtx.curCtx B x byte2)
          (storePost σn.wmWs rl x (σn.wmLog.length + 1)) ∗
        vwpHold (z ↦w{q} vz : VProp GF) (storePost σn.wmWs rl x (σn.wmLog.length + 1))) := by
  intro hwf hacc hQ htidb hzero himg hlg hle hcohx hokx hcohz hokz hmb hother htid hk
  have hlat : wlatInterp (GF := GF) σ'.wmImg σ'.wmLog ⊢
      wlatInterp (GF := GF) σn.wmImg σn.wmLog := by rw [himg, hlg]
  iintro Hlog Hall Hi Hinv Hx Hz
  -- the resume: the index and the invariant arrive, and nothing else
  imod wyieldResumeCore CurCtx.curCtx γ hf V B tid σ σ' hwf hacc hQ htidb hzero $$ Hi Hall Hinv
    with ⟨Hi, Hbody, Htok, Hmg, %hV⟩
  have hVn : V ≤ wsView σn.wmWs := fun a => Nat.le_trans (hV a) (wsView_mono _ _ hle a)
  ihave Hi := hlat $$ Hi
  -- the FRAMED facts, thawed by the view alone: TWO IDENTICAL LINES
  ihave Hx := vwpHold_intro V (x ↦wo byte1 : VProp GF) σn.wmWs hVn $$ Hx
  ihave Hz := vwpHold_intro V (z ↦w{q} vz : VProp GF) σn.wmWs hVn $$ Hz
  -- THE ACCESS BLOCK, ON HART B -- §4b's line, at the new hart
  imod wyfTouch B σn mB x z byte1 vz q akx akz tx tz bx bz rl hcohx hokx hcohz hokz hmb hother
    htid hk $$ Hlog Hmg Hi Hx Hz with ⟨Hlog, Hmg, Hi, %hbx, %hbz, Hx, Hz⟩
  imodintro
  iframe Hlog Hmg Hi Hbody Htok Hx Hz
  isplitr
  · ipureintro; exact hbx
  · ipureintro; exact hbz

omit [LockExG GF] in
/-- 4e. THE φ PAYMENT OF THE MIGRATED THREAD'S FIRST TOUCH -- the same lemma a non-migrated
thread uses. -/
theorem wyfPhiMigrated (B : CPU) (V : View) (img : GMapF PAddr (BitVec 8)) (log : List Wmsg)
    (pcb x : Int) (vx : BitVec 8) :
    latestTs log pcb = 0 →
    wlogAuth (GF := GF) log ⊢ ctxMigr (GF := GF) CurCtx.curCtx B -∗ wlatInterp (GF := GF) img log -∗
      (x ↦wo vx : VProp GF).monPred_at V -∗
      ⌜nvOk log B pcb ∧ nvOk log B x⌝ := by
  intro htext
  iintro Hlog Hmg Hi Hx
  ihave %hnx := nvOk_of_wptOwn_cur B x vx V img log log (pubTransferRefl log B)
    $$ [Hlog Hmg Hi Hx]
  · iframe Hlog Hmg Hi Hx
  ipureintro
  exact ⟨nvOkUnwritten log B pcb htext, hnx⟩

end yieldExample

/-! ## 5. The park at the WP altitude -- one `sw` through the handoff flag -/

section wpYield

variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [WeakGS GF] [LockExG GF]

omit [LockExG GF] in
/-- The park's callback: NO payload, the pure index fact, and a continuation handed the PARKED
migration invariant. -/
def wyieldParkCb (gen : Nat) (cpu : CPU) (ξ : CtxId) (V : View) (pc : BitVec 64)
    (P : Wmstate → Prop) : IProp GF :=
  iprop(∀ σ : Wmstate,
    wlatInterp σ.wmImg σ.wmLog -∗
    wmstateRest (hlc := hlc) (GF := GF) cpu σ ={⊤ \ ↑wlockN, ∅}=∗
      ⌜σ.wmRegs .PC = pc⌝ ∗
      ⌜∀ j : Nat, j < 4 →
        pinnedRead σ (WeakInterp.accAddr pc j) ∧ fetchPinned σ (WeakInterp.accAddr pc j)⌝ ∗
      ⌜P σ⌝ ∗
      ⌜∀ j : Nat, j < 4 → nvOk σ.wmLog cpu (WeakInterp.accAddr pc j)⌝ ∗
      -- the `fence rw,w` at `pc-4`: what makes the handoff store `WCrel`, hence the mint site
      ⌜σ.wmWs.wRelp = true⌝ ∗
      -- the parked index -- a fact, not a resource
      ⌜V ≤ wsView σ.wmWs⌝ ∗
      wlatInterp σ.wmImg σ.wmLog ∗
      ∃ t0 t1 : ExecSt,
        ⌜exec (riscvStep false) (wflatSt σ) = some ((), t0)⌝ ∗
        ⌜exec (riscvStep true) (wflatSt σ) = some ((), t1)⌝ ∗
        ▷ (∀ (tick : Bool) (σ' : Wmstate),
            ⌜wstepPost σ σ' (if tick then t1 else t0)⌝ -∗
            |={∅, ⊤ \ ↑wlockN}=> wmstateRestNonv (hlc := hlc) (GF := GF) cpu σ' ∗
              -- THE WHOLE POSTCONDITION OF THE PARK
              (ctxMigrAll (GF := GF) ξ -∗
                wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu))))

theorem wwpYieldPark (gen : Nat) (cpu : CPU) (ξ : CtxId) (γ : GName) (hf : PAddr) (V : View)
    (pc : BitVec 64) (akf : AkInfo) (pf : PAddr) (nf : Nat) (akw : AkInfo) :
    gen = 0 →
    accWf pc 4 →
    accWf hf 4 →
    -- the handoff store is a plain `sw`, not an AMO
    akw.akLatest = false →
    (∀ a : Int, weffTouches (.WEread akf pf nf) a → ∃ j, j < 4 ∧ a = WeakInterp.accAddr pc j) →
    inv wlockN (wlockInv (GF := GF) γ hf (wbaton V)) ⊢
      lockedEx (GF := GF) γ cpu -∗
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
  iintro #Hinv Htok Hmg Hk
  unfold wyieldParkCb
  iapply wpWinstr gen cpu pc _ _ hgen haccpc hcert
  iintro %σ Hσ
  icases (wmstateInterpSplit cpu σ).mp $$ Hσ with ⟨Hlat, Hrest⟩
  icases keepPure1 (wmstateRestFacts cpu σ) $$ Hrest with ⟨%hfacts, Hrest⟩
  icases keepPure1 (wmstateRestNv cpu σ) $$ Hrest with ⟨%hnvσ, Hrest⟩
  obtain ⟨hbnd, _⟩ := hfacts
  imod (inv_acc (E := ⊤) (N := wlockN) (P := wlockInv (GF := GF) γ hf (wbaton V))
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
  -- the release itself, and the φ payment -- `wwpReleaseStore`'s verbatim
  imod wreleaseCore γ hf (wbaton V) cpu (some cpu.val) σ σ' hQ rfl hrelp hbnd $$ Hlat Hbody Htok []
    with ⟨Hlat, Hbody⟩
  · iapply (wbatonAt V σ.wmWs).mpr
    ipureintro; exact hV
  icases keepPure (nvOkWlockInv cpu σ'.wmImg σ'.wmLog γ hf (wbaton V)) $$ Hlat Hbody
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

/-- ... AND THE RESUME NEEDS NO NEW RULE AT ALL: `wwpAcquireLoopCert` at `R := wbaton V`. -/
theorem wwpYieldResume (gen : Nat) (cpu : CPU) (γ : GName) (hf : PAddr) (V : View)
    (pc : BitVec 64) (akf : AkInfo) (pf : PAddr) (nf : Nat) (aka akw : AkInfo) (K : IProp GF) :
    gen = 0 →
    accWf pc 4 →
    accWf hf 4 →
    aka.akIfetch = false →
    aka.akSync = true →
    akw.akLatest = true →
    (∀ a : Int, weffTouches (.WEread akf pf nf) a → ∃ j, j < 4 ∧ a = WeakInterp.accAddr pc j) →
    inv wlockN (wlockInv (GF := GF) γ hf (wbaton V)) ⊢
      □ (K -∗ ▷ (K -∗ wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu)) -∗
          wacqCb (hlc := hlc) gen cpu γ hf (wbaton V) pc
            (wPEffText (some cpu.val)
              [.WEread akf pf nf, .WEread aka hf 4, .WEwrite akw hf 4 lockOne])) -∗
        K -∗ wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu) :=
  wwpAcquireLoopCert gen cpu γ hf (wbaton V) pc akf pf nf aka akw K

end wpYield

end Weak
