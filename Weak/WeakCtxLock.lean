/-
Weak: **EVERY LOCK OWNS A CONTEXT (φ-upgrade §1.8)** — the lock payload `wledgerPay ξ P` (a
context's ledger, the `IProp` facts registered in it, and the receipt that the holder has seen the
ledger's view), the context-carrying lock `wclockBody` / `wctxIsLock` / `wctxHeld`, the acquire
core (withdraw, then re-index into the acquirer), the two release cores (the generic one for an
already-clean `CtxMorph` payload, and the one-byte OWNED deposit with the D→C flip spliced in), and
the yield in the new surface (`wctxPark` / `wctxResume`: `ctxOwn ξ c` in, `ctxOwn ξ c'` out, the
context's LEDGER travelling through the handoff flag as an empty-payload lock).

Rocq: `iris/WeakCtxLock.v` @ xxvzwolszwmp.

Rocq header (in substance, Rocq vocabulary).  A lock's payload is
`wledger_pay ξ P := ∃ V, ⎡ ctx_auth ξ V ∗ P ⎤ ∗ ⊒V` — the LEDGER of a context ξ, the view-free
`iProp` facts whose floors are registered against it, and the receipt that whoever holds the
payload has observed the ledger's view.  This is Cosmo's "the lock protects a view", with the view
ledger as the lock's CONTEXT: the releaser raises the lock's ledger to its own view and re-registers
the deposited facts there; the acquirer's `amoswap.w.aq` delivers `⊒V`, which puts the lock's
ledger below the acquirer's view, so the acquirer may re-register the facts against ITS context.
Function proofs see none of it, and the payload `P` is an ordinary `iProp` — exactly as a lock
invariant is in the SC tree.  ξ_L IS INTERNAL: the client handle is
`wctx_is_lock γ lk R := ∃ ξ_L, inv wlockN (wclock_body γ lk R ξ_L)` with `R : CtxId → iProp`
written `<{ … }>`; acquire hands back `R cur_ctx`, release consumes it, and the re-indexing between
`R ξ_L` and `R cur_ctx` is `WeakCtxPt.ctx_morph`, applied inside these lemmas and nowhere else.
THE HANDOFF IS THE SAME CONSTRUCTION WITH AN EMPTY PAYLOAD (§5): a yield parks a context by
depositing its ledger in the scheduler's handoff flag; the resuming hart withdraws it and the ledger
lands below the new hart's view — `ctx_own ξ c` in, `ctx_own ξ c'` out, and nothing memory-shaped
crosses.  (The section comments and the closing note "what a ported lock library takes from this
file" are kept on the corresponding Lean declarations below.)

**Deviations from Rocq.**

1. NAMES: the tree's camelCase convention (name map below).  Vocabulary as `Weak/WeakLock.lean`
   deviation 1 (`wm_log σ` ↦ `σ.wmLog`, `ws_view` ↦ `wsView`, `fin_to_nat i` ↦ `i.val`,
   `pa_add a j` ↦ `a + BitVec.ofNat 64 j`, `wflat … !! a = Some v` ↦ `wflatMem … a = some v`,
   `nth_byte w j` ↦ `nthByte (n := 4) w j`, `S (length l)` ↦ `l.length + 1`, `Arch.pa` ↦ `PAddr`,
   `bv 8` ↦ `BitVec 8`, the address `x : Z` ↦ `x : Int`, `monPred_at R V` ↦ `R.monPred_at V`,
   `V ⊑ W` ↦ `V ≤ W`).
2. THE SC LOCK GHOST (`WeakLock` deviation 2): Rocq's `locked γ i` is `lockedEx γ i`
   (`MachCSL/WeakAuxWeakLock.lean`), in `wctxHeld` and in the park/resume statements.
3. STATEMENT SHAPES (the `WeakLock` deviation 5 convention): Rocq `A -∗ B -∗ C` is `A ⊢ B -∗ C`,
   `A -∗ … -∗ B ==∗ C` is `A ⊢ … -∗ B -∗ |==> (C)` (parenthesised).  Rocq `P ⊣⊢ Q` stays.
4. `Context {!riscvGS Σ, !weakGS Σ, !lockG Σ}` is `{hlc : HasLC} [MachGS hlc GF] [WeakGS GF]
   [LockExG GF]` (`WeakLock` deviation 6); the payload section needs only `[WeakGS GF]`.
5. THE PAYLOAD WRAPPER (`WeakCtxPt` deviation 7): `<{ x ↦wp v }>` is the `CurCtx`-`letI` lambda;
   at `ξL` it is definitionally `wptstoCl ξL x (DFrac.own 1) v`, which is the form the proof
   re-indexes (`ctxMorphCl`'s function).
6. `wledgerPay` gets a `MakeMonPredAt` instance (`makeMonPredAt_wledgerPay`, Lean-only: the
   protocol's rule for `def`-level `VProp`s; Rocq's proofmode unfolds the definition itself).
7. `wctx_release_byte` / `wctx_park_core` rewrite the post-state's image and log into the
   pre-state's (`σ'.wmImg = σ.wmImg`, `σ'.wmLog = σ.wmLog ++ [m]`) at the start of the proof
   rather than by `rewrite Hlog` / `rewrite -Hlog` in the middle — same statements.

**Rocq → Lean name map.**  `wledger_pay` `wledgerPay`, `wledger_pay_at_view` `wledgerPayAtView`,
`wledger_pay_at` `wledgerPayAt`, `wledger_pay_intro` `wledgerPayIntro`, `wclock_body`
`wclockBody`, `wctx_is_lock` `wctxIsLock`, `wctx_is_lock_persistent` `wctxIsLock_persistent`,
`wctx_held` `wctxHeld`, `wctx_acquire_core` `wctxAcquireCore`, `wctx_release_core`
`wctxReleaseCore`, `wctx_release_byte` `wctxReleaseByte`, `wctx_baton` `wctxBaton`, `ctx_parked`
`ctxParked`, `wctx_park_core` `wctxParkCore`, `wctx_resume_core` `wctxResumeCore`, `wctx_park`
`wctxPark`, `wctx_resume` `wctxResume`.  Lean-only: `makeMonPredAt_wledgerPay` (deviation 6).
(None of these names is in `notes/weak-port-dupnames.json`.)

**Not ported:** nothing — every Rocq definition and lemma has a Lean twin.

**Statements checked** (diffed against Rocq by hand): all; the changed spellings are the
deviations above.
-/
import Weak.WeakLock
import Weak.WeakAcquire
import Weak.WeakCtxPt
import Weak.WeakInstr
import MachCSL.WeakAuxWeakLock
import MachCSL.MonPredExtra

namespace Weak

open Iris Iris.BI Iris.BI.MonPred Iris.ProofMode Iris.Std
open MachCSL MachCSL.Stdpp

/-! ## 1. THE PAYLOAD: a context's ledger, and the facts registered in it -/

section pay

variable {GF : BundledGFunctors} [WeakGS GF]

/-- Rocq `wledger_pay`. -/
def wledgerPay (ξ : CtxId) (P : IProp GF) : VProp GF :=
  iprop(∃ V : View, ⎡ctxAuth (GF := GF) ξ V ∗ P⎤ ∗ ⊒V)

theorem wledgerPayAtView (ξ : CtxId) (P : IProp GF) (W : View) :
    (wledgerPay ξ P).monPred_at W ⊣⊢ ∃ V : View, ctxAuth ξ V ∗ P ∗ ⌜V ≤ W⌝ := by
  unfold wledgerPay
  refine (monPred_at_exist (I := viewBiIndex) W _).trans (exists_congr fun V => ?_)
  show iprop((ctxAuth ξ V ∗ P) ∗ ⌜V ≤ W⌝) ⊣⊢ _
  exact sep_assoc

set_option synthInstance.checkSynthOrder false in
/-- Lean-only (deviation 6): the proofmode evaluates the payload at an index. -/
instance makeMonPredAt_wledgerPay (d : MakeMonPredAt.Kind) (i : View) (ξ : CtxId) (P : IProp GF) :
    MakeMonPredAt d i (wledgerPay ξ P) (iprop(∃ V : View, ctxAuth ξ V ∗ P ∗ ⌜V ≤ i⌝)) where
  make_monPred_at := wledgerPayAtView ξ P i

theorem wledgerPayAt (ξ : CtxId) (P : IProp GF) (ws : Wstate) :
    vwpHold (wledgerPay ξ P) ws ⊣⊢ ∃ V : View, ctxAuth ξ V ∗ P ∗ ⌜V ≤ wsView ws⌝ :=
  wledgerPayAtView ξ P (wsView ws)

theorem wledgerPayIntro (ξ : CtxId) (P : IProp GF) (V W : View) (h : V ≤ W) :
    ctxAuth (GF := GF) ξ V ⊢ P -∗ (wledgerPay ξ P).monPred_at W := by
  iintro Ha HP
  iapply (wledgerPayAtView ξ P W).mpr
  iexists V
  iframe Ha HP
  ipureintro
  exact h

end pay

/-! ## 2. THE LOCK WITH A CONTEXT -/

section clock

variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [WeakGS GF] [LockExG GF]

/-- The invariant BODY, with the lock's context named.  A client never writes this: it writes
`wctxIsLock` below, whose existential is the whole of "ξ_L is internal". -/
def wclockBody (γ : GName) (lk : PAddr) (R : CtxId → IProp GF) (ξL : CtxId) : IProp GF :=
  wlockInv (GF := GF) γ lk (wledgerPay ξL (R ξL))

/-- THE CLIENT-FACING HANDLE.  Persistent, objective, and free of the lock's context — which is
bound here and introduced into a proof exactly once. -/
def wctxIsLock (γ : GName) (lk : PAddr) (R : CtxId → IProp GF) : IProp GF :=
  iprop(∃ ξL : CtxId, inv wlockN (wclockBody (GF := GF) γ lk R ξL))

instance wctxIsLock_persistent (γ : GName) (lk : PAddr) (R : CtxId → IProp GF) :
    Persistent (wctxIsLock (hlc := hlc) (GF := GF) γ lk R) := by
  unfold wctxIsLock; infer_instance

/-- THE CRITICAL-SECTION TOKEN.  The holder token, plus the lock's ledger authority (which travels
with the payload and must come back at the release), plus the persistent receipt that the HOLDER's
ledger already dominates the lock's — minted at the acquire, and what lets the release raise the
lock's ledger to the holder's view.  It names both contexts (`WeakVProp` §3'''s convention): it is
proof-internal, living between one acquire and the matching release inside a single function
proof, so naming ξ_L here costs a client nothing. -/
def wctxHeld (γ : GName) (ξL ξ : CtxId) (i : CPU) : IProp GF :=
  iprop(lockedEx (GF := GF) γ i ∗ ∃ V : View, ctxAuth ξL V ∗ ctxViewLb ξ V)

/-! ## 3. ACQUIRE — the withdraw, and the re-index into the acquirer

`WeakLock.wacquireCore` with three lines after it: decode the payload, bump the acquirer's ledger
to its hart's view (which the `aq` transfer has put above the lock's), and move the facts.
`CtxMorph` does the last step for WHATEVER the client's payload is. -/

theorem wctxAcquireCore (γ : GName) (ξL ξ : CtxId) (lk : PAddr) (R : CtxId → IProp GF)
    [CtxMorph R] (i : CPU) (tid : Option Nat) (σ σ' : Wmstate) :
    wlogWf σ.wmLog → accWf lk 4 →
    wQAmoAq tid lk lockOne σ σ' →
    -- T2-0′ (F3′): the message's author IS this hart.
    tid = some i.val →
    (∀ j : Nat, j < 4 →
      wflatMem σ.wmImg σ.wmLog (lk + BitVec.ofNat 64 j) = some (nthByte (n := 4) lockZero j)) →
    wlatInterp (GF := GF) σ.wmImg σ.wmLog ⊢
      wclockBody γ lk R ξL -∗
        ctxOwnAt ξ i σ.wmWs -∗
          |==> (wlatInterp (GF := GF) σ'.wmImg σ'.wmLog ∗ wclockBody γ lk R ξL ∗
            wctxHeld γ ξL ξ i ∗ ctxOwnAt ξ i σ'.wmWs ∗ R ξ) := by
  intro hwf hacc hQ htid hzero
  have hle : wsLe σ.wmWs σ'.wmWs := hQ.1.2.2.1
  unfold wclockBody wctxHeld ctxOwnAt
  iintro Hi Hinv ⟨Hlb, Hmg⟩
  ihave Hlb := ctxLbMono ξ σ.wmWs σ'.wmWs (wsLeView _ _ hle) $$ Hlb
  icases wacquireCore γ lk (wledgerPay ξL (R ξL)) i tid σ σ' hwf hacc hQ htid $$ Hi Hinv
    with ⟨%v0, %hflat, Hupd⟩
  have hv : lockZero = v0 := wflatWordAgree σ lk lockZero v0 hzero hflat
  subst hv
  imod Hupd with ⟨Hi, Hbody, Harm⟩
  icases Harm with (⟨-, HR, Htok⟩ | %hne)
  · -- the payload: the lock's ledger, the facts, and the `aq` view fact
    icases (wledgerPayAt ξL (R ξL) σ'.wmWs).mp $$ HR with ⟨%V, HaL, HR, %hV⟩
    -- the acquirer's own ledger, bumped to its hart's view
    imod ctxLbSync ξ σ'.wmWs $$ Hlb with Ha
    ihave #Hd := ctxViewLbGet ξ (wsView σ'.wmWs) V hV $$ Ha
    -- THE RE-INDEX, once, for whatever the payload is
    ihave Hdom := ctxDomIntro ξL ξ V $$ [HaL]
    · iframe HaL Hd
    imod CtxMorph.ctxMorph (R := R) ξL ξ V $$ [Hdom HR] with ⟨Hdom, HR⟩
    · iframe Hdom HR
    ihave HaL := ctxDomAuth ξL ξ V $$ Hdom
    imodintro
    iframe Hi Hbody Htok Hmg HR
    isplitl [HaL]
    · iexists V
      iframe HaL Hd
    · iapply ctxLbOfAuth ξ σ'.wmWs $$ Ha
  · exact absurd rfl hne

/-! ## 4. RELEASE — the re-index out, and the deposit

Two cores, for the reason `WkOwnPingPong` §3 records: a release that EGRESSES OWNED MEMORY needs
the latest-write authority at the POST-state (where its `WCrel` message is the log's last) in order
to flip the deposit clean, and `WeakLock.wreleaseCore` consumes its payload at the PRE-state.  §4a
is the release whose payload is already clean — fully generic in `R`; §4b is the one-byte owned
deposit, with the flip spliced in, the shape a ported `release` that hands over memory copies. -/

/-- 4a. THE GENERIC RELEASE — any `CtxMorph` payload, already clean. -/
theorem wctxReleaseCore (γ : GName) (ξL ξ : CtxId) (lk : PAddr) (R : CtxId → IProp GF)
    [CtxMorph R] (i : CPU) (tid : Option Nat) (σ σ' : Wmstate) :
    wQStore tid lk lockZero σ σ' →
    -- T2-0′ (F3′): the message's author IS this hart.
    tid = some i.val →
    σ.wmWs.wRelp = true →
    wsBounded σ.wmWs σ.wmLog.length →
    wlatInterp (GF := GF) σ.wmImg σ.wmLog ⊢
      wclockBody γ lk R ξL -∗
        wctxHeld γ ξL ξ i -∗
          ctxOwnAt ξ i σ.wmWs -∗
            R ξ -∗
              |==> (wlatInterp (GF := GF) σ'.wmImg σ'.wmLog ∗ wclockBody γ lk R ξL ∗
                ctxOwnAt ξ i σ.wmWs) := by
  intro hQ htid hrelp hbnd
  unfold wclockBody wctxHeld ctxOwnAt
  iintro Hi Hinv ⟨Htok, %VL, HaL, #Hd⟩ ⟨Hlb, Hmg⟩ HR
  -- the depositor's ledger at its hart's view, and the lock's below it
  imod ctxLbSync ξ σ.wmWs $$ Hlb with Ha
  ihave %hVL := ctxViewLbValid ξ (wsView σ.wmWs) VL $$ [Ha]
  · iframe Ha Hd
  -- THE MINT: raise the lock's ledger to the release view
  imod ctxDomMint ξ ξL (wsView σ.wmWs) VL hVL $$ [Ha HaL] with ⟨HaL, Hdom⟩
  · iframe Ha HaL
  -- THE RE-INDEX, once, for whatever the payload is
  imod CtxMorph.ctxMorph (R := R) ξ ξL (wsView σ.wmWs) $$ [Hdom HR] with ⟨Hdom, HR⟩
  · iframe Hdom HR
  ihave Ha := ctxDomAuth ξ ξL _ $$ Hdom
  -- the deposit is now an ordinary `wreleaseCore` at the wrapped payload
  imod wreleaseCore γ lk (wledgerPay ξL (R ξL)) i tid σ σ' hQ htid hrelp hbnd
      $$ Hi Hinv Htok [HaL HR] with ⟨Hi, Hinv⟩
  · iapply (wledgerPayAt ξL (R ξL) σ.wmWs).mpr
    iexists wsView σ.wmWs
    iframe HaL HR
    ipureintro
    exact fun _ => Nat.le_refl _
  imodintro
  iframe Hi Hinv Hmg
  iapply ctxLbOfAuth ξ σ.wmWs $$ Ha

/-- 4b. THE OWNED ONE-BYTE RELEASE — the D→C flip at a real site.  `WkOwnPingPong`'s
`wrelease_flip_core` restated over the `IProp` surface.  The payload the caller hands over is the
OWNED `wptsto ξ x v` (what a plain `sb` leaves); what the lock ends up holding is the CLEAN
`wptstoCl ξL x v` that any context may take.  The three ghost steps in between — retarget (a byte
this context dirtied on a hart it has since left), flip (D→C at the release's own message),
re-index (into the lock's ledger) — are all here and none of them is visible in a function
proof. -/
theorem wctxReleaseByte (γ : GName) (ξL ξ : CtxId) (lk : PAddr) (x : Int) (v : BitVec 8)
    (i : CPU) (σ σ' : Wmstate) :
    wQStore (some i.val) lk lockZero σ σ' →
    σ'.wmLog = σ.wmLog ++ [wwriteMsg (some i.val) .WCrel lk 4 lockZero] →
    wsBounded σ.wmWs σ.wmLog.length →
    wlogAuth (GF := GF) σ'.wmLog ⊢
      wlatInterp (GF := GF) σ.wmImg σ.wmLog -∗
        wclockBody γ lk <{ x ↦wp v }> ξL -∗
          wctxHeld γ ξL ξ i -∗
            ctxOwnAt ξ i σ.wmWs -∗
              wptsto ξ x v -∗
                |==> (wlogAuth (GF := GF) σ'.wmLog ∗
                  wlatInterp (GF := GF) σ'.wmImg σ'.wmLog ∗
                  wclockBody γ lk <{ x ↦wp v }> ξL ∗ ctxOwnAt ξ i σ.wmWs) := by
  intro hQ hlog hbnd
  obtain ⟨himg, -, -, -⟩ := hQ
  have hst4 := fun t w => wlat4LStoreGen (GF := GF) (some i.val) .WCrel σ σ' lk t w lockZero
    (some i.val) none (wlockShapedRel _ .WCrel lk (by decide)) (altStepRelMsg i .WCrel lk)
    himg hlog
  simp only [himg, hlog] at hst4
  have htr : pubTransfer (σ.wmLog ++ [wwriteMsg (some i.val) .WCrel lk 4 lockZero]) σ.wmLog i :=
    pubTransferSnoc σ.wmLog _ i rfl
  have hm : ∀ V : View, ctxDom (GF := GF) ξ ξL V ∗ wptstoCl ξ x (DFrac.own 1) v ⊢
      |==> (ctxDom ξ ξL V ∗ wptstoCl ξL x (DFrac.own 1) v) := fun V =>
    CtxMorph.ctxMorph (R := fun ξ => wptstoCl (GF := GF) ξ x (DFrac.own 1) v) ξ ξL V
  have hdep := wwpReleaseDeposit
    (wledgerPay ξL ((<{ x ↦wp v }> : CtxId → IProp GF) ξL)) σ hbnd
  unfold vwpHold at hdep
  rw [himg, hlog]
  unfold wclockBody wctxHeld ctxOwnAt wptsto wlockInv
  iintro Hlg Hi ⟨%st, %t, %w, Hw, Ha, -⟩ ⟨Htok, %VL, HaL, #Hd⟩ ⟨Hlb, Hmg⟩ ⟨%t0, Hel, Hs, #Hf⟩
  icases keepPure (lockedExState γ st i) $$ Ha Htok with ⟨%hst, Ha, Htok⟩
  subst hst
  dsimp only [tidOf]
  -- THE RETARGET, leaf-internally
  imod wownCtxRetarget ξ i x t0 v σ.wmImg σ.wmLog _ htr $$ [Hlg Hmg Hi Hel Hs]
    with ⟨Hlg, Hmg, Hi, Hel, Hs⟩
  · iframe Hlg Hmg Hi Hel Hs
  -- the lock word's own bundle moves to the fresh top, and stays CLEAN
  imod hst4 t w $$ Hi Hw with ⟨Hi, Hw⟩
  -- THE FLIP, at the post-log whose last message is this hart's release
  imod wlatFlip σ.wmImg σ.wmLog (wwriteMsg (some i.val) .WCrel lk 4 lockZero) i x rfl rfl
    $$ [Hi Hs] with ⟨Hi, Hcl⟩
  · iframe Hi Hs
  -- THE MINT and THE RE-INDEX
  imod ctxLbSync ξ σ.wmWs $$ Hlb with Hau
  ihave %hVL := ctxViewLbValid ξ (wsView σ.wmWs) VL $$ [Hau]
  · iframe Hau Hd
  imod ctxDomMint ξ ξL (wsView σ.wmWs) VL hVL $$ [Hau HaL] with ⟨HaL, Hdom⟩
  · iframe Hau HaL
  -- the deposit's CLEAN form, at the ledger registration it already had
  imod hm (wsView σ.wmWs) $$ [Hdom Hel Hcl] with ⟨Hdom, HR⟩
  · iframe Hdom
    unfold wptstoCl wlatPointsto
    iexists t0
    iframe Hel Hcl Hf
  ihave Hau := ctxDomAuth ξ ξL _ $$ Hdom
  -- the deposit itself: view arithmetic and `wsBounded`, nothing else
  ihave Hdep := hdep $$ [HaL HR]
  · iapply wledgerPayIntro ξL ((<{ x ↦wp v }> : CtxId → IProp GF) ξL) (wsView σ.wmWs) (wsView σ.wmWs) (fun _ => Nat.le_refl _) $$ HaL
    iexact HR
  imod lockClrcpu γ (some (i, true)) i $$ Ha Htok with ⟨-, Ha, Hpre⟩
  imod lockGive γ (some (i, false)) i $$ Ha Hpre with ⟨-, Ha, Hfrag⟩
  imodintro
  iframe Hlg Hi Hmg
  isplitl [Hw Ha Hfrag Hdep]
  · iexists none, σ.wmLog.length + 1, lockZero
    dsimp only [tidOf]
    iframe Hw Ha
    ileft
    iframe Hfrag Hdep
    ipureintro
    exact ⟨rfl, rfl⟩
  · iapply ctxLbOfAuth ξ σ.wmWs $$ Hau

/-! ## 5. YIELD IN THE NEW SURFACE — `ctxOwn ξ c` in, `ctxOwn ξ c'` out

The handoff flag is §1's construction with an EMPTY payload: what the park deposits is the
context's LEDGER, and nothing else.  Note what does not appear in the two statements below: no
byte, no view variable in the postcondition, no publication token, no hart's memory state.  The
park's whole output is `ctxMigrAll ξ`, the scheduler-side migration invariant in its parked form;
the resume's whole output is `ctxOwn` at the NEW cpu, which is the lemma's ∀-bound `c'`.  Every
`wptsto` a thread owns therefore frames across the pair with nothing to prove — it is an `IProp`
that neither lemma mentions (`WkCtxSurface` §6 is that statement). -/

/-- Rocq `wctx_baton`. -/
def wctxBaton (ξ : CtxId) : VProp GF := wledgerPay ξ iprop(emp)

/-- THE PARKED CONTEXT: a scheduler resource naming no byte, no view and no hart.  (Its ledger is
not here — it is in the handoff flag.) -/
def ctxParked (ξ : CtxId) : IProp GF := ctxMigrAll ξ

theorem wctxParkCore (ξ : CtxId) (γ : GName) (hf : PAddr) (i : CPU) (σ σ' : Wmstate) :
    wQStore (some i.val) hf lockZero σ σ' →
    σ'.wmLog = σ.wmLog ++ [wwriteMsg (some i.val) .WCrel hf 4 lockZero] →
    wsBounded σ.wmWs σ.wmLog.length →
    wlogAuth (GF := GF) σ.wmLog ⊢
      wlatInterp (GF := GF) σ.wmImg σ.wmLog -∗
        wlockInv (GF := GF) γ hf (wctxBaton ξ) -∗
          lockedEx (GF := GF) γ i -∗
            ctxOwnAt ξ i σ.wmWs -∗
              |==> (wlogAuth (GF := GF) σ'.wmLog ∗
                wlatInterp (GF := GF) σ'.wmImg σ'.wmLog ∗
                wlockInv (GF := GF) γ hf (wctxBaton ξ) ∗ ctxParked ξ) := by
  intro hQ hlog hbnd
  obtain ⟨himg, -, -, -⟩ := hQ
  have hst4 := fun t w => wlat4LStoreGen (GF := GF) (some i.val) .WCrel σ σ' hf t w lockZero
    (some i.val) none (wlockShapedRel _ .WCrel hf (by decide)) (altStepRelMsg i .WCrel hf)
    himg hlog
  simp only [himg, hlog] at hst4
  have hdep := wwpReleaseDeposit (wctxBaton (GF := GF) ξ) σ hbnd
  unfold vwpHold wctxBaton at hdep
  have hlen : (σ.wmLog ++ [wwriteMsg (some i.val) .WCrel hf 4 lockZero]).length ≤
      σ.wmLog.length + 1 := by simp
  rw [himg, hlog]
  unfold wlockInv ctxOwnAt ctxParked wctxBaton
  iintro Hlog Hi ⟨%st, %t, %w, Hw, Ha, -⟩ Htok ⟨Hlb, Hmg⟩
  icases keepPure (lockedExState γ st i) $$ Ha Htok with ⟨%hst, Ha, Htok⟩
  subst hst
  dsimp only [tidOf]
  -- the flag word's bundle moves to the fresh top and stays CLEAN
  imod hst4 t w $$ Hi Hw with ⟨Hi, Hw⟩
  -- THE MINT: the handoff store is this hart's, release-class, at the log's fresh top, so it
  -- publishes every earlier position at once
  imod wlogUpdate σ.wmLog [wwriteMsg (some i.val) .WCrel hf 4 lockZero] $$ Hlog with Hlog
  icases pubFloorMint σ.wmLog (wwriteMsg (some i.val) .WCrel hf 4 lockZero) i rfl rfl $$ Hlog
    with ⟨Hlog, #Hpf⟩
  icases ctxMigrPark ξ i _ _ hlen $$ [Hlog Hmg] with ⟨Hlog, Hall⟩
  · iframe Hlog Hpf Hmg
  -- THE DEPOSIT: the context's LEDGER travels through the flag
  imod ctxLbSync ξ σ.wmWs $$ Hlb with Hau
  ihave Hdep := hdep $$ [Hau]
  · iapply wledgerPayIntro ξ iprop(emp) (wsView σ.wmWs) (wsView σ.wmWs)
      (fun _ => Nat.le_refl _) $$ Hau
    iempintro
  imod lockClrcpu γ (some (i, true)) i $$ Ha Htok with ⟨-, Ha, Hpre⟩
  imod lockGive γ (some (i, false)) i $$ Ha Hpre with ⟨-, Ha, Hfrag⟩
  imodintro
  iframe Hlog Hi Hall
  iexists none, σ.wmLog.length + 1, lockZero
  dsimp only [tidOf]
  iframe Hw Ha
  ileft
  iframe Hfrag Hdep
  ipureintro
  exact ⟨rfl, rfl⟩

/-- THE RESUME, at WHATEVER cpu the scheduler picked — `c'` is this lemma's binder, and the
`wp_next`-style re-binding is exactly that quantifier.  Nothing about the resuming hart has to be
checked: the parked invariant covers every hart, and the withdrawn ledger lands below the new
hart's view by the `aq` transfer. -/
theorem wctxResumeCore (ξ : CtxId) (γ : GName) (hf : PAddr) (c' : CPU) (tid : Option Nat)
    (σ σ' : Wmstate) :
    wlogWf σ.wmLog → accWf hf 4 →
    wQAmoAq tid hf lockOne σ σ' →
    -- T2-0′ (F3′): the message's author IS this hart.
    tid = some c'.val →
    (∀ j : Nat, j < 4 →
      wflatMem σ.wmImg σ.wmLog (hf + BitVec.ofNat 64 j) = some (nthByte (n := 4) lockZero j)) →
    wlatInterp (GF := GF) σ.wmImg σ.wmLog ⊢
      wlockInv (GF := GF) γ hf (wctxBaton ξ) -∗
        ctxParked ξ -∗
          |==> (wlatInterp (GF := GF) σ'.wmImg σ'.wmLog ∗
            wlockInv (GF := GF) γ hf (wctxBaton ξ) ∗ lockedEx (GF := GF) γ c' ∗
            ctxOwnAt ξ c' σ'.wmWs) := by
  intro hwf hacc hQ htid hzero
  unfold ctxParked ctxOwnAt ctxLb wctxBaton
  iintro Hi Hinv Hall
  icases wacquireCore γ hf (wledgerPay ξ iprop(emp)) c' tid σ σ' hwf hacc hQ htid $$ Hi Hinv
    with ⟨%v0, %hflat, Hupd⟩
  have hv : lockZero = v0 := wflatWordAgree σ hf lockZero v0 hzero hflat
  subst hv
  imod Hupd with ⟨Hi, Hbody, Harm⟩
  icases Harm with (⟨-, HR, Htok⟩ | %hne)
  · icases (wledgerPayAt ξ iprop(emp) σ'.wmWs).mp $$ HR with ⟨%V, Hau, -, %hV⟩
    imodintro
    iframe Hi Hbody Htok
    isplitl [Hau]
    · iexists V
      iframe Hau
      ipureintro
      exact hV
    · iapply ctxMigrAllRun ξ c' $$ Hall
  · exact absurd rfl hne

/-- ... and the bundle form, which is the user-facing shape: `ctxOwn ξ i` in, `ctxOwn ξ c'` out,
with the hart's own `wstate` fragment supplied by the machine on each side. -/
theorem wctxPark (ξ : CtxId) (γ : GName) (hf : PAddr) (i : CPU) (σ σ' : Wmstate) :
    wQStore (some i.val) hf lockZero σ σ' →
    σ'.wmLog = σ.wmLog ++ [wwriteMsg (some i.val) .WCrel hf 4 lockZero] →
    wsBounded σ.wmWs σ.wmLog.length →
    wwsAuth (GF := GF) i σ.wmWs ⊢
      wlogAuth (GF := GF) σ.wmLog -∗
        wlatInterp (GF := GF) σ.wmImg σ.wmLog -∗
          wlockInv (GF := GF) γ hf (wctxBaton ξ) -∗
            lockedEx (GF := GF) γ i -∗
              ctxOwn ξ i -∗
                |==> (wwsAuth (GF := GF) i σ.wmWs ∗ hartWs (GF := GF) i σ.wmWs ∗
                  wlogAuth (GF := GF) σ'.wmLog ∗ wlatInterp (GF := GF) σ'.wmImg σ'.wmLog ∗
                  wlockInv (GF := GF) γ hf (wctxBaton ξ) ∗ ctxParked ξ) := by
  intro hQ hlog hbnd
  iintro Hwsa Hlog Hi Hinv Htok Hrun
  icases ctxOwnAcc ξ i σ.wmWs $$ [Hwsa Hrun] with ⟨Hwsa, Hws, Hrun⟩
  · iframe Hwsa Hrun
  imod wctxParkCore ξ γ hf i σ σ' hQ hlog hbnd $$ Hlog Hi Hinv Htok Hrun
    with ⟨Hlog, Hi, Hinv, Hpk⟩
  imodintro
  iframe Hwsa Hws Hlog Hi Hinv Hpk

theorem wctxResume (ξ : CtxId) (γ : GName) (hf : PAddr) (c' : CPU) (tid : Option Nat)
    (σ σ' : Wmstate) :
    wlogWf σ.wmLog → accWf hf 4 →
    wQAmoAq tid hf lockOne σ σ' →
    tid = some c'.val →
    (∀ j : Nat, j < 4 →
      wflatMem σ.wmImg σ.wmLog (hf + BitVec.ofNat 64 j) = some (nthByte (n := 4) lockZero j)) →
    hartWs (GF := GF) c' σ'.wmWs ⊢
      wlatInterp (GF := GF) σ.wmImg σ.wmLog -∗
        wlockInv (GF := GF) γ hf (wctxBaton ξ) -∗
          ctxParked ξ -∗
            |==> (wlatInterp (GF := GF) σ'.wmImg σ'.wmLog ∗
              wlockInv (GF := GF) γ hf (wctxBaton ξ) ∗ lockedEx (GF := GF) γ c' ∗
              ctxOwn ξ c') := by
  intro hwf hacc hQ htid hzero
  iintro Hws Hi Hinv Hall
  imod wctxResumeCore ξ γ hf c' tid σ σ' hwf hacc hQ htid hzero $$ Hi Hinv Hall
    with ⟨Hi, Hinv, Htok, Hrun⟩
  imodintro
  iframe Hi Hinv Htok
  iapply ctxOwnClose ξ c' σ'.wmWs
  iframe Hws Hrun

end clock

/-! WHAT A PORTED LOCK LIBRARY TAKES FROM THIS FILE (the Rocq closing note).

1. `wctxIsLock γ lk R` is the handle, with `R : CtxId → IProp` written `<{ … }>`.  A client's lock
   invariant is plain `IProp` with bare `↦wp` spellings; the lock's own context is bound by the
   handle's existential and enters a proof once.
2. Acquire returns `R cur_ctx` and the critical-section token; release consumes `R cur_ctx` and the
   token.  The re-indexing between the lock's context and the client's is
   `WeakCtxPt`'s `CtxMorph.ctxMorph`, applied inside §3 and §4 and nowhere else, and the
   `CtxMorph` instance is found by instance resolution from the payload's SHAPE.
3. A release that egresses OWNED memory uses §4b (which flips D→C at the release's own message);
   a release whose payload is already clean or context-free uses §4a, generic in the payload.
4. A yield is §5: the same construction with an empty payload, so the context's LEDGER is what
   travels.  Pre `ctxOwn ξ c`, post `ctxOwn ξ c'` with `c'` the resume lemma's binder, and no
   memory fact in either. -/

end Weak
