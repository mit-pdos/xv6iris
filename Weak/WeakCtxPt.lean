/-
Weak: **THE iPROP RESURFACING (φ-upgrade §1.8)** — the objective, context-indexed byte points-to
in its clean (`wptstoCl`, the ambient `a ↦wp{dq} v`) and owned (`wptsto`, the ambient `a ↦wpo v`)
forms, the running bundle `ctxOwn` (the ledger tie relaxed to `≤`, the hart explicit), the
interconversion with `WeakVProp`'s `vwpHold` surface, the `IProp`-surface load/store leaf rules and
φ payments, and re-indexing between contexts: the permission `ctxDom` and the structural class
`CtxMorph` with its instances.

Rocq: `iris/WeakCtxPt.v` @ xxvzwolszwmp (1cc222280).

Rocq header (in substance, Rocq vocabulary): Stages 1.5–1.7 built an owned points-to that frames
across a migration ([WeakVProp.wpt_own]) — but it is a [vProp], and its subjective conjunct
[⊒(view_byte a t)] is exactly what makes it one.  The existing SC proofs are [iProp]-shaped, so
the target API is an [iProp] points-to, and the view receipt goes INTO THE CONTEXT'S LEDGER: a
byte's floor registered in [ctx_view_lb ξ] is a fact ABOUT THE CONTEXT, so it can live inside an
objective [iProp]:

    [wptsto ξ a v]  =  the value element + the C/D/S state (with its breadcrumb)
                       + [ctx_view_lb ξ (view_byte a t)]

and nothing in it mentions a view variable, a [monPred_at], or a hart.  Framing across a yield is
then not a lemma at all.  THE ONE INVARIANT THAT MAKES THE FLOORS USABLE is [ctx_own]'s: "ξ's
ledger is below the hart's view".  [ctx_own] is the successor of [WeakCtx.wrunning] with the CPU an
EXPLICIT argument (re-bound at a migration exactly as [cur_proc] is).  This file's [wptsto] /
[wptsto_cl] / [ctx_own] are THE API for the port; [WeakVProp]'s [wpt_own] / [wpt] and the
[vwp_hold] discipline remain the INTERNAL GLUE, and every rule below is its [vProp] twin with two
conversions (§3) wrapped around it.  THE TWO SPELLINGS: [a ↦wp{dq} v] ([wptsto_cl]) — CLEAN,
fractional, the only form that can be RE-INDEXED between contexts (§6); [a ↦wpo v] ([wptsto]) —
OWNED, exclusive, clean-or-dirty.  Both are ambiently ξ-indexed through [WeakVProp]'s [CurCtx]
class, under that file's one-context convention.

(The Rocq section comments are kept on the corresponding Lean declarations; the Rocq file's
closing note — "what a ported proof takes from this file" — is: memory facts are `a ↦wpo v` and
`a ↦wp{dq} v`, `IProp`s that frame across any call; `ctxOwn ξ c` is threaded exactly as
`cur_proc` is; a leaf converts with §3 and calls the `VProp` rule; a lock payload is a
`CtxId → IProp` written `<{ … }>`, re-indexed with `CtxMorph.ctxMorph`.)

**Deviations from Rocq.**

1. NAMES: the tree's camelCase convention (name map below).
2. STATEMENT SHAPES (the `WeakGhost` deviation 9 convention): Rocq `P -∗ Q` is `P ⊢ Q`,
   `P -∗ Q -∗ R` is `P ∗ Q ⊢ R`, `P -∗ Q -∗ R -∗ S` is `P ∗ Q ∗ R ⊢ S`, `P ==∗ Q` is
   `P ⊢ |==> Q`, `P -∗ Q ==∗ R` is `P ∗ Q ⊢ |==> (R)` (parenthesised: iris-lean's `|==> P ∗ Q`
   is `(|==> P) ∗ Q`).  `V ⊑ V'` is `V ≤ V'`.  The `CtxMorph` field `⊢ ctx_dom ξ ξ' V -∗ R ξ ==∗
   ctx_dom ξ ξ' V ∗ R ξ'` is `ctxDom ξ ξ' V ∗ R ξ ⊢ |==> (ctxDom ξ ξ' V ∗ R ξ')`.
3. `Context {!riscvGS Σ, !weakGS Σ}`: the SC instance is dropped (nothing here uses it; the
   `WeakGhost` deviation 10 convention), the ghost state is `[WeakGS GF]`.
4. MACHINE VOCABULARY (`WeakVProp` deviations 5/6): `ak_coh ak = false` is `ak.akIfetch = false`,
   `wm_img σ` ↦ `σ.wmImg` etc., `wm_tid m = Some (fin_to_nat c)` ↦ `m.wmTid = some c.val`,
   `S (length l)` ↦ `l.length + 1`; `wptsto_store_post` instantiates the post-state as
   `{ σ with wmLog := …, wmWs := … }` (Rocq's five-field `WMState` literal).  The address is an
   `Int`, the byte a `BitVec 8`, `dfrac` is `DFrac`.
5. `CpuId` does not exist in Lean (`WeakCtx` deviation 5): `ctx_own_of_running` /
   `ctx_own_to_running` take the hart `cpu : CPU` explicitly as their first argument, and
   `wrunning ξ` is `wrunning cpu ξ`.
6. NOTATIONS (`WeakVProp` deviation 3): Rocq's dfrac-custom `a ↦wp dq v` is `a ↦wp{dq} v` /
   `a ↦wp□ v` / `a ↦wp v` (the last at `DFrac.own 1`); `a ↦wpo v` is verbatim.  All are
   `CurCtx.curCtx`-indexed (`Weak.CurCtx`).
7. THE `CurCtx`-BINDER INSTANCE AND THE PAYLOAD WRAPPER.  Rocq's `CurCtx` is a singleton class,
   i.e. definitionally `CtxId`, so `λ XLK : CurCtx, P` IS a `CtxId → iProp`.  Lean's `CurCtx` is a
   one-field structure, so the bound context is turned into the ambient instance with `letI`:
   `<{ P }>` is `fun ξ : CtxId => letI : CurCtx := ⟨ξ⟩; P`, and `ctx_morph_cl_cur` is the instance
   at `fun ξ => letI : CurCtx := ⟨ξ⟩; a ↦wp{dq} v` (definitionally `ctxMorphCl`'s function, as in
   Rocq).  `Typeclasses Opaque cur_ctx` has no Lean counterpart (`WeakVProp` deviation 8).
8. Instance priority: Rocq `| 100` on `ctx_morph_const` is `(priority := low)`.
9. `wptsto_load_rule` passes `WeakVProp.wpt_load_rule_own` its PER-BYTE floor premise (the Lean
   statement of that rule), obtained from this file's whole-view premise; the statement here keeps
   Rocq's `ws_view (wm_ws σ) ⊑ ws_view (wm_ws σ')`.

**Rocq → Lean name map.**  §1 `wptsto_cl`→`wptstoCl`, `wptsto`→`wptsto`.  §2 `ctx_lb`→`ctxLb`,
`ctx_own_at`→`ctxOwnAt`, `ctx_own`→`ctxOwn`, `ctx_lb_of_auth/sync/mono/valid`→
`ctxLbOfAuth/Sync/Mono/Valid`, `ctx_own_at_mono/migr`→`ctxOwnAtMono/Migr`,
`ctx_own_open/close/acc/step`→`ctxOwnOpen/Close/Acc/Step`, `ctx_own_of_running/to_running`→
`ctxOwnOfRunning/ToRunning`.  §3 `wptsto_to_own/of_own`→`wptstoToOwn/OfOwn`,
`wptsto_cl_to_pt/of_pt`→`wptstoClToPt/OfPt`, `wptsto_of_cl`→`wptstoOfCl`, `wptsto_cobj`→
`wptstoCobj`, `wptsto_cl_cobj`→`wptstoClCobj`, `wptsto_agree`→`wptstoAgree`.  §4
`wptsto_load_rule/load_wread/store_rule/store_post`→`wptstoLoadRule/LoadWread/StoreRule/
StorePost`, `nv_ok_of_wptsto(_at/_cl)`→`nvOkOfWptsto(At/Cl)`.  §5 `wptsto_of_cl_cur`→
`wptstoOfClCur`, `wptsto_load_rule_cur`→`wptstoLoadRuleCur`, `wptsto_store_post_cur`→
`wptstoStorePostCur`, `nv_ok_of_wptsto_cur`→`nvOkOfWptstoCur`.  §6 `ctx_dom`→`ctxDom`,
`ctx_dom_lb/mint/intro/auth/ptsto`→`ctxDomLb/Mint/Intro/Auth/Ptsto`, `CtxMorph`→`CtxMorph`
(`Weak.CtxMorph`, distinct from `MachCSL.CtxMorph`), `ctx_morph`→`CtxMorph.ctxMorph`,
`ctx_morph_cl/cl_cur/const/sep/exist/or`→`ctxMorphCl/ClCur/Const/Sep/Exist/Or`; the notation
`<{ P }>` is kept.  (None of these names is in `notes/weak-port-dupnames.json`.)

**Not ported:** nothing.

**Statements checked** (diffed against Rocq by hand): all; the changed spellings are the
deviations above.
-/
import Weak.WeakCtx
import Weak.WeakVProp
import Weak.WeakGhost
import Weak.WeakView
import Weak.WeakInterp
import Weak.WeakMem
import MachCSL.MonPredExtra

namespace Weak

open Iris Iris.BI Iris.BI.MonPred Iris.ProofMode Iris.Std MachCSL MachCSL.Stdpp

/-! ## 1. THE TWO POINTS-TO -/

section defs

variable {GF : BundledGFunctors} [WeakGS GF]

/-- THE CLEAN FORM.  `WeakVProp.wpt`'s payload with the subjective receipt `⊒(viewByte a t)`
replaced by the ledger registration: "`t` is below what ξ has observed", which is the observation
that survives a change of hart. -/
def wptstoCl (ξ : CtxId) (a : Int) (dq : DFrac) (v : BitVec 8) : IProp GF :=
  iprop(∃ t : Nat, wlatPointsto (GF := GF) a dq t v ∗ ctxViewLb ξ (viewByte a t))

/-- THE OWNED FORM.  `WeakVProp.wptOwn`'s payload, same substitution.  The C/D/S state and its
migration breadcrumb ride inside `wownCtx` untouched — this stage changes the RECEIPT, not the
protocol. -/
def wptsto (ξ : CtxId) (a : Int) (v : BitVec 8) : IProp GF :=
  iprop(∃ t : Nat, wlatElem (GF := GF) a (DFrac.own 1) t v ∗ wownCtx (GF := GF) ξ a t ∗
    ctxViewLb ξ (viewByte a t))

end defs

/-! The ambient spellings (φ-upgrade §1.7's class, this stage's surface; deviation 6). -/
notation:50 a:50 " ↦wp{" dq "} " v:50 => wptstoCl CurCtx.curCtx a dq v
notation:50 a:50 " ↦wp□ " v:50 => wptstoCl CurCtx.curCtx a DFrac.discard v
notation:50 a:50 " ↦wp " v:50 => wptstoCl CurCtx.curCtx a (DFrac.own 1) v
notation:50 a:50 " ↦wpo " v:50 => wptsto CurCtx.curCtx a v

/-! ## 2. `ctxOwn` — the running bundle

`WeakCtx.wrunning` with the hart an EXPLICIT argument and the ledger tie RELAXED from equality to
`≤`.  WHY EXPLICIT: a thread's context is invariant across a migration and its hart is not, so ξ
is ambient and the CPU is written; `ctxOwn ξ c` is re-bound at a yield exactly as `cur_proc` is.
WHY `≤` AND NOT `=`: `WeakCtx.ctxRun` pins the ledger to the hart's view exactly, which costs a
ghost update at every view growth; the inequality is what every consumer needs, it is monotone in
the wstate FOR FREE, and it is restored to the exact form by one `ctxAuthUpdate` where a rule
needs to register a NEW floor.  That update is `ctxLbSync`, the only ghost operation this surface
performs on the ledger. -/

section running

variable {GF : BundledGFunctors} [WeakGS GF]

/-- THE INVARIANT: "ξ's ledger is below this hart's view". -/
def ctxLb (ξ : CtxId) (ws : Wstate) : IProp GF :=
  iprop(∃ V : View, ctxAuth ξ V ∗ ⌜V ≤ wsView ws⌝)

/-- ... plus the Stage-1.6 migration invariant, the OTHER half of the bundle: publication is not
view-implied, so the two halves are independent and both are needed. -/
def ctxOwnAt (ξ : CtxId) (c : CPU) (ws : Wstate) : IProp GF :=
  iprop(ctxLb ξ ws ∗ ctxMigr ξ c)

/-- THE CALLER-FACING BUNDLE, with the wstate hidden behind the hart's own exclusive fragment —
which is what pins it to the machine's when a leaf agrees the two halves (`ctxOwnAcc`). -/
def ctxOwn (ξ : CtxId) (c : CPU) : IProp GF :=
  iprop(∃ ws : Wstate, hartWs c ws ∗ ctxOwnAt ξ c ws)

theorem ctxLbOfAuth (ξ : CtxId) (ws : Wstate) :
    ctxAuth (GF := GF) ξ (wsView ws) ⊢ ctxLb ξ ws := by
  unfold ctxLb
  iintro H
  iexists wsView ws
  iframe H
  ipureintro
  exact fun _ => Nat.le_refl _

/-- THE SYNC — the one ledger update the surface performs: raising the ledger to the hart's own
view is always permitted, and is what lets a rule REGISTER a floor the hart has just acquired. -/
theorem ctxLbSync (ξ : CtxId) (ws : Wstate) :
    ctxLb (GF := GF) ξ ws ⊢ |==> ctxAuth ξ (wsView ws) := by
  unfold ctxLb
  iintro ⟨%V, Ha, %hle⟩
  iapply ctxAuthUpdate ξ V (wsView ws) hle $$ Ha

theorem ctxLbMono (ξ : CtxId) (ws ws' : Wstate) (h : wsView ws ≤ wsView ws') :
    ctxLb (GF := GF) ξ ws ⊢ ctxLb ξ ws' := by
  unfold ctxLb
  iintro ⟨%V, Ha, %h0⟩
  iexists V
  iframe Ha
  ipureintro
  exact fun a => Nat.le_trans (h0 a) (h a)

/-- The ledger's floors are the hart's floors — the ONE fact that makes every points-to's
registration usable at every leaf. -/
theorem ctxLbValid (ξ : CtxId) (ws : Wstate) (V : View) :
    ctxLb (GF := GF) ξ ws ∗ ctxViewLb ξ V ⊢ ctxLb ξ ws ∗ ⌜V ≤ wsView ws⌝ := by
  unfold ctxLb
  iintro ⟨⟨%V0, Ha, %h0⟩, #Hlb⟩
  ihave %hV := ctxViewLbValid ξ V0 V $$ [Ha Hlb]
  · iframe Ha Hlb
  isplitl [Ha]
  · iexists V0
    iframe Ha
    ipureintro
    exact h0
  · ipureintro
    exact fun a => Nat.le_trans (hV a) (h0 a)

theorem ctxOwnAtMono (ξ : CtxId) (c : CPU) (ws ws' : Wstate) (h : wsLe ws ws') :
    ctxOwnAt (GF := GF) ξ c ws ⊢ ctxOwnAt ξ c ws' := by
  unfold ctxOwnAt
  iintro ⟨Hlb, Hm⟩
  iframe Hm
  iapply ctxLbMono ξ ws ws' (wsLeView ws ws' h) $$ Hlb

/-- The migration invariant, borrowed — what the store leaf needs out of the bundle besides the
ledger. -/
theorem ctxOwnAtMigr (ξ : CtxId) (c : CPU) (ws : Wstate) :
    ctxOwnAt (GF := GF) ξ c ws ⊢ ctxMigr ξ c ∗ (ctxMigr ξ c -∗ ctxOwnAt ξ c ws) := by
  unfold ctxOwnAt
  iintro ⟨Hlb, Hm⟩
  iframe Hm
  iintro Hm
  iframe Hlb Hm

theorem ctxOwnOpen (ξ : CtxId) (c : CPU) :
    ctxOwn (GF := GF) ξ c ⊢ ∃ ws : Wstate, hartWs c ws ∗ ctxOwnAt ξ c ws := .rfl

theorem ctxOwnClose (ξ : CtxId) (c : CPU) (ws : Wstate) :
    hartWs (GF := GF) c ws ∗ ctxOwnAt ξ c ws ⊢ ctxOwn ξ c := by
  unfold ctxOwn
  iintro ⟨H1, H2⟩
  iexists ws
  iframe H1 H2

/-- THE LEAF ACCESSOR.  Against the machine's own authority the bundle's hidden wstate IS the
machine's, so a leaf may read the caller's ledger at the machine's wstate with nothing to
prove. -/
theorem ctxOwnAcc (ξ : CtxId) (c : CPU) (ws : Wstate) :
    wwsAuth (GF := GF) c ws ∗ ctxOwn ξ c ⊢ wwsAuth c ws ∗ hartWs c ws ∗ ctxOwnAt ξ c ws := by
  unfold ctxOwn
  iintro ⟨Ha, ⟨%ws0, Hf, Hrun⟩⟩
  ihave %h := hartWsAgree c ws ws0 $$ [Ha Hf]
  · iframe Ha Hf
  subst h
  iframe Ha Hf Hrun

/-- ... and the step: the hart's wstate grew, so the bundle follows.  No ghost update, because
the ledger tie is an inequality. -/
theorem ctxOwnStep (ξ : CtxId) (c : CPU) (ws ws' : Wstate) (h : wsLe ws ws') :
    ctxOwnAt (GF := GF) ξ c ws ∗ hartWs c ws' ⊢ ctxOwn ξ c := by
  iintro ⟨Hrun, Hws⟩
  iapply ctxOwnClose ξ c ws'
  iframe Hws
  iapply ctxOwnAtMono ξ c ws ws' h $$ Hrun

/-- The bridge to `WeakCtx`'s own bundle, both ways (deviation 5).  `wrunning` pins the ledger
exactly, so the way back is the sync. -/
theorem ctxOwnOfRunning (cpu : CPU) (ξ : CtxId) : wrunning (GF := GF) cpu ξ ⊢ ctxOwn ξ cpu := by
  unfold wrunning ctxRun ctxOwn ctxOwnAt
  iintro ⟨%ws, Hws, Ha, Hm⟩
  iexists ws
  iframe Hws Hm
  iapply ctxLbOfAuth ξ ws $$ Ha

theorem ctxOwnToRunning (cpu : CPU) (ξ : CtxId) :
    ctxOwn (GF := GF) ξ cpu ⊢ |==> wrunning cpu ξ := by
  unfold ctxOwn ctxOwnAt wrunning ctxRun
  iintro ⟨%ws, Hws, Hlb, Hm⟩
  imod ctxLbSync ξ ws $$ Hlb with Ha
  imodintro
  iexists ws
  iframe Hws Ha Hm

end running

/-! ## 3. THE INTERCONVERSION with the `VProp` surface

This is the whole seam.  Read it at `ws := σ.wmWs`: an `IProp` fact plus the ledger invariant IS
the `VProp` fact at the hart's index, and back. -/

section convert

variable {GF : BundledGFunctors} [WeakGS GF]

theorem wptstoToOwn (ξ : CtxId) (ws : Wstate) (a : Int) (v : BitVec 8) :
    ctxLb (GF := GF) ξ ws ∗ wptsto ξ a v ⊢ ctxLb ξ ws ∗ vwpHold (wptOwn (GF := GF) ξ a v) ws := by
  unfold wptsto
  iintro ⟨Hlb, ⟨%t, He, Hs, #Hf⟩⟩
  icases ctxLbValid ξ ws (viewByte a t) $$ [Hlb Hf] with ⟨Hlb, %hle⟩
  · iframe Hlb Hf
  iframe Hlb
  iapply wptOwn_at_intro ξ a v t ws ((viewByte_le a t _).mp hle)
  iframe He Hs

theorem wptstoOfOwn (ξ : CtxId) (ws : Wstate) (a : Int) (v : BitVec 8) :
    ctxAuth (GF := GF) ξ (wsView ws) ∗ vwpHold (wptOwn (GF := GF) ξ a v) ws ⊢
      ctxAuth ξ (wsView ws) ∗ wptsto ξ a v := by
  iintro ⟨Ha, Hpt⟩
  icases (wptOwn_at ξ a v ws).mp $$ Hpt with ⟨%t, He, Hs, %ht⟩
  ihave #Hf := ctxViewLbGet ξ (wsView ws) (viewByte a t) ((viewByte_le a t _).mpr ht) $$ Ha
  iframe Ha
  unfold wptsto
  iexists t
  iframe He Hs Hf

theorem wptstoClToPt (ξ : CtxId) (ws : Wstate) (a : Int) (dq : DFrac) (v : BitVec 8) :
    ctxLb (GF := GF) ξ ws ∗ wptstoCl ξ a dq v ⊢ ctxLb ξ ws ∗ vwpHold (wpt (GF := GF) a dq v) ws := by
  unfold wptstoCl
  iintro ⟨Hlb, ⟨%t, He, #Hf⟩⟩
  icases ctxLbValid ξ ws (viewByte a t) $$ [Hlb Hf] with ⟨Hlb, %hle⟩
  · iframe Hlb Hf
  iframe Hlb
  iapply wpt_at_intro a dq v t ws ((viewByte_le a t _).mp hle) $$ He

theorem wptstoClOfPt (ξ : CtxId) (ws : Wstate) (a : Int) (dq : DFrac) (v : BitVec 8) :
    ctxAuth (GF := GF) ξ (wsView ws) ∗ vwpHold (wpt (GF := GF) a dq v) ws ⊢
      ctxAuth ξ (wsView ws) ∗ wptstoCl ξ a dq v := by
  iintro ⟨Ha, Hpt⟩
  icases (wpt_at a dq v ws).mp $$ Hpt with ⟨%t, He, %ht⟩
  ihave #Hf := ctxViewLbGet ξ (wsView ws) (viewByte a t) ((viewByte_le a t _).mpr ht) $$ Ha
  iframe Ha
  unfold wptstoCl
  iexists t
  iframe He Hf

/-- A CLEAN FULL-FRACTION BYTE IS OWNED, at every context — `WeakVProp.wptOwn_of_wpt` at this
altitude, and the receiving side of every transfer in one line. -/
theorem wptstoOfCl (ξ : CtxId) (a : Int) (v : BitVec 8) :
    wptstoCl (GF := GF) ξ a (DFrac.own 1) v ⊢ wptsto ξ a v := by
  unfold wptstoCl wptsto wlatPointsto
  iintro ⟨%t, ⟨He, Hc⟩, #Hf⟩
  iexists t
  iframe He Hf
  iapply wownCtxOfClean ξ a t $$ Hc

/-- ... and the characterisation that says what the surface IS: the objective-ownership functor
of `WeakCtx` applied to the Stage-1.6 points-to ("where did the view go"). -/
theorem wptstoCobj (ξ : CtxId) (a : Int) (v : BitVec 8) :
    wptsto (GF := GF) ξ a v ⊣⊢ cobj ξ (wptOwn (GF := GF) ξ a v) := by
  unfold wptsto cobj
  constructor
  · iintro ⟨%t, He, Hs, #Hf⟩
    iexists viewByte a t
    iframe Hf
    iapply (wptOwn_at_view ξ a v (viewByte a t)).mpr
    iexists t
    iframe He Hs
    ipureintro
    rw [flr_byte_eq]
    exact Nat.le_refl _
  · iintro ⟨%V, #Hf, Hpt⟩
    icases (wptOwn_at_view ξ a v V).mp $$ Hpt with ⟨%t, He, Hs, %ht⟩
    iexists t
    iframe He Hs
    iapply ctxViewLbMono ξ V (viewByte a t) ((viewByte_le a t V).mpr ht) $$ Hf

theorem wptstoClCobj (ξ : CtxId) (a : Int) (dq : DFrac) (v : BitVec 8) :
    wptstoCl (GF := GF) ξ a dq v ⊣⊢ cobj ξ (wpt (GF := GF) a dq v) := by
  unfold wptstoCl cobj
  constructor
  · iintro ⟨%t, He, #Hf⟩
    iexists viewByte a t
    iframe Hf
    iapply (wpt_at_view a dq v (viewByte a t)).mpr
    iexists t
    iframe He
    ipureintro
    rw [flr_byte_eq]
    exact Nat.le_refl _
  · iintro ⟨%V, #Hf, Hpt⟩
    icases (wpt_at_view a dq v V).mp $$ Hpt with ⟨%t, He, %ht⟩
    iexists t
    iframe He
    iapply ctxViewLbMono ξ V (viewByte a t) ((viewByte_le a t V).mpr ht) $$ Hf

theorem wptstoAgree (ξ ξ' : CtxId) (a : Int) (v v' : BitVec 8) :
    wptsto (GF := GF) ξ a v ∗ wptsto ξ' a v' ⊢ ⌜v = v'⌝ := by
  unfold wptsto
  iintro ⟨⟨%t, He, -⟩, ⟨%t', He', -⟩⟩
  ihave %h := wlatElem_agree a _ t v _ t' v' $$ He He'
  ipureintro
  exact h.2

end convert

/-! ## 4. THE IPROP-SURFACE LEAF RULES

`WeakVProp` §4'/§5's owned rules with §3's conversions wrapped around them.  The memory fact
carries NO index, so the `wptsto` in and the `wptsto` out are the SAME proposition; the floor comes
from `ctxOwnAt`, not from the fact, which is why a store must REGISTER the new floor (the sync in
`ctxLbSync`) where the `VProp` rule merely widened a receipt. -/

section rules

variable {GF : BundledGFunctors} [WeakGS GF]

/-- THE OWNED LOAD.  A hart reads its own byte — clean, own-dirty, or dirtied on a hart it has
since left; `WeakVProp.wpt_load_rule_own` does not care and neither does this (deviation 9). -/
theorem wptstoLoadRule (ξ : CtxId) (c : CPU) (σ σ' : Wmstate) (ak : AkInfo) (a : Int)
    (v : BitVec 8) (t' : Nat) (b : BitVec 8) :
    ak.akIfetch = false →
    wbyteOk σ ak a t' b →
    σ'.wmImg = σ.wmImg →
    σ'.wmLog = σ.wmLog →
    wsView σ.wmWs ≤ wsView σ'.wmWs →
    wlatInterp (GF := GF) σ.wmImg σ.wmLog ∗ ctxOwnAt ξ c σ.wmWs ∗ wptsto ξ a v ⊢
      |==> (⌜b = v⌝ ∗ wlatInterp (GF := GF) σ'.wmImg σ'.wmLog ∗ ctxOwnAt ξ c σ'.wmWs ∗
        wptsto ξ a v) := by
  intro hcoh hok himg hlog hview
  unfold ctxOwnAt
  iintro ⟨Hi, ⟨Hlb, Hmg⟩, Hpt⟩
  icases wptstoToOwn ξ σ.wmWs a v $$ [Hlb Hpt] with ⟨Hlb, Hpt⟩
  · iframe Hlb Hpt
  icases wpt_load_rule_own ξ σ σ' ak a v t' b hcoh hok himg hlog
      ((View.le_spec _ _).1 hview a) $$ [Hi Hpt] with ⟨%hb, Hi, Hpt⟩
  · iframe Hi Hpt
  imod ctxLbSync ξ σ'.wmWs $$ [Hlb] with Ha
  · iapply ctxLbMono ξ σ.wmWs σ'.wmWs hview $$ Hlb
  icases wptstoOfOwn ξ σ'.wmWs a v $$ [Ha Hpt] with ⟨Ha, Hpt⟩
  · iframe Ha Hpt
  imodintro
  isplitr
  · ipureintro
    exact hb
  iframe Hi Hmg Hpt
  iapply ctxLbOfAuth ξ σ'.wmWs $$ Ha

/-- The framing side conditions at the interpreter's own read post-state, as
`WeakVProp.wpt_load_wread_own` discharges them. -/
theorem wptstoLoadWread (ξ : CtxId) (c : CPU) (σ : Wmstate) (ak : AkInfo) (a : Int)
    (v : BitVec 8) (pa : PAddr) (ts : List Nat) (t' : Nat) (b : BitVec 8) :
    ak.akIfetch = false →
    wbyteOk σ ak a t' b →
    wlatInterp (GF := GF) σ.wmImg σ.wmLog ∗ ctxOwnAt ξ c σ.wmWs ∗ wptsto ξ a v ⊢
      |==> (⌜b = v⌝ ∗
        wlatInterp (GF := GF) (wreadPost σ ak pa ts).wmImg (wreadPost σ ak pa ts).wmLog ∗
        ctxOwnAt ξ c (wreadPost σ ak pa ts).wmWs ∗ wptsto ξ a v) := fun hcoh hok =>
  wptstoLoadRule ξ c σ (wreadPost σ ak pa ts) ak a v t' b hcoh hok (wreadPostImg σ ak pa ts)
    (wreadPostLog σ ak pa ts) (wsView_mono _ _ (wreadPostWsLe σ ak pa ts))

/-- THE OWNED STORE.  Beyond `WeakVProp`'s: the post-log authority and the migration invariant
(both already threaded at every store site, the latter riding in `ctxOwnAt` now), and the
REGISTRATION of the new floor in ξ's ledger — the one ghost operation this surface adds, performed
here, inside the rule. -/
theorem wptstoStoreRule (ξ : CtxId) (c : CPU) (σ σ' : Wmstate) (m : Wmsg) (a : Int)
    (v v' : BitVec 8) :
    msgByte m a = some v' →
    (∀ a', a' ≠ a → msgByte m a' = none) →
    m.wmTid = some c.val →
    σ'.wmImg = σ.wmImg →
    σ'.wmLog = σ.wmLog ++ [m] →
    wsView σ.wmWs ≤ wsView σ'.wmWs →
    σ.wmLog.length + 1 ≤ flr (wsView σ'.wmWs) a →
    wlogAuth (GF := GF) σ'.wmLog ∗ wlatInterp (GF := GF) σ.wmImg σ.wmLog ∗
      ctxOwnAt ξ c σ.wmWs ∗ wptsto ξ a v ⊢
      |==> (wlogAuth (GF := GF) σ'.wmLog ∗ wlatInterp (GF := GF) σ'.wmImg σ'.wmLog ∗
        ctxOwnAt ξ c σ'.wmWs ∗ wptsto ξ a v') := by
  intro hma hother htid himg hlog hview hfl
  unfold ctxOwnAt
  iintro ⟨Hlg, Hi, ⟨Hlb, Hmg⟩, Hpt⟩
  icases wptstoToOwn ξ σ.wmWs a v $$ [Hlb Hpt] with ⟨Hlb, Hpt⟩
  · iframe Hlb Hpt
  imod wpt_store_rule_own ξ c σ σ' m a v v' hma hother htid himg hlog hfl
      $$ [Hlg Hmg Hi Hpt] with ⟨Hlg, Hmg, Hi, Hpt⟩
  · iframe Hlg Hmg Hi Hpt
  imod ctxLbSync ξ σ'.wmWs $$ [Hlb] with Ha
  · iapply ctxLbMono ξ σ.wmWs σ'.wmWs hview $$ Hlb
  icases wptstoOfOwn ξ σ'.wmWs a v' $$ [Ha Hpt] with ⟨Ha, Hpt⟩
  · iframe Ha Hpt
  imodintro
  iframe Hlg Hi Hmg Hpt
  iapply ctxLbOfAuth ξ σ'.wmWs $$ Ha

/-- ... at the machine's own store post-state, where both view premises are automatic. -/
theorem wptstoStorePost (ξ : CtxId) (c : CPU) (σ : Wmstate) (m : Wmsg) (a : Int)
    (v v' : BitVec 8) (rl : Bool) :
    msgByte m a = some v' →
    (∀ a', a' ≠ a → msgByte m a' = none) →
    m.wmTid = some c.val →
    wlogAuth (GF := GF) (σ.wmLog ++ [m]) ∗ wlatInterp (GF := GF) σ.wmImg σ.wmLog ∗
      ctxOwnAt ξ c σ.wmWs ∗ wptsto ξ a v ⊢
      |==> (wlogAuth (GF := GF) (σ.wmLog ++ [m]) ∗
        wlatInterp (GF := GF) σ.wmImg (σ.wmLog ++ [m]) ∗
        ctxOwnAt ξ c (storePost σ.wmWs rl a (σ.wmLog.length + 1)) ∗ wptsto ξ a v') :=
  fun hma hother htid =>
    wptstoStoreRule ξ c σ
      { σ with wmLog := σ.wmLog ++ [m], wmWs := storePost σ.wmWs rl a (σ.wmLog.length + 1) }
      m a v v' hma hother htid rfl rfl (wsView_mono _ _ (storePostLe _ _ _ _))
      (flr_storePost _ _ _ _)

/-- THE φ PAYMENT.  `WeakVProp.nvOk_of_wptOwn` at this altitude: the owned byte pays `nvOk` at
the running hart whether or not the context has migrated since it dirtied the byte, and the
ledger plays no part — the case split is `wownCtx`'s, inside. -/
theorem nvOkOfWptsto (ξ : CtxId) (c : CPU) (a : Int) (v : BitVec 8)
    (img : GMapF PAddr (BitVec 8)) (log logA : List Wmsg) :
    pubTransfer logA log c →
    wlogAuth (GF := GF) logA ∗ ctxMigr (GF := GF) ξ c ∗ wlatInterp (GF := GF) img log ∗
      wptsto ξ a v ⊢ ⌜nvOk log c a⌝ := by
  intro htr
  unfold wptsto
  iintro ⟨Hlog, Hmg, Hi, ⟨%t, He, Hs, -⟩⟩
  iapply nvOkOfWownCtx ξ c a t v img log logA htr
  iframe Hlog Hmg Hi He Hs

theorem nvOkOfWptstoAt (ξ : CtxId) (c : CPU) (a : Int) (v : BitVec 8)
    (img : GMapF PAddr (BitVec 8)) (log : List Wmsg) :
    wlogAuth (GF := GF) log ∗ ctxMigr (GF := GF) ξ c ∗ wlatInterp (GF := GF) img log ∗
      wptsto ξ a v ⊢ ⌜nvOk log c a⌝ :=
  nvOkOfWptsto ξ c a v img log log (pubTransferRefl log c)

/-- ... and the clean byte's, which needs neither the invariant nor the log authority (a clean
byte is never anybody's outstanding store). -/
theorem nvOkOfWptstoCl (ξ : CtxId) (c : CPU) (a : Int) (dq : DFrac) (v : BitVec 8)
    (img : GMapF PAddr (BitVec 8)) (log : List Wmsg) :
    wlatInterp (GF := GF) img log ∗ wptstoCl ξ a dq v ⊢ ⌜nvOk log c a⌝ := by
  unfold wptstoCl
  iintro ⟨Hi, ⟨%t, He, -⟩⟩
  iapply nvOkOfPointsto img log c a dq t v
  iframe Hi He

end rules

/-! ## 5. THE AMBIENT API (φ-upgrade §1.7's convention, this surface)

The rules above with the context read out of the `CurCtx` instance.  Thin wrappers and nothing
else; the ξ-explicit primitives stay, because a proof with TWO contexts in scope must be able to
use them at both. -/

section curApi

variable {GF : BundledGFunctors} [WeakGS GF] [XI : CurCtx]

theorem wptstoOfClCur (a : Int) (v : BitVec 8) : (a ↦wp v : IProp GF) ⊢ a ↦wpo v :=
  wptstoOfCl _ a v

theorem wptstoLoadRuleCur (c : CPU) (σ σ' : Wmstate) (ak : AkInfo) (a : Int) (v : BitVec 8)
    (t' : Nat) (b : BitVec 8) :
    ak.akIfetch = false →
    wbyteOk σ ak a t' b →
    σ'.wmImg = σ.wmImg →
    σ'.wmLog = σ.wmLog →
    wsView σ.wmWs ≤ wsView σ'.wmWs →
    wlatInterp (GF := GF) σ.wmImg σ.wmLog ∗ ctxOwnAt CurCtx.curCtx c σ.wmWs ∗ (a ↦wpo v) ⊢
      |==> (⌜b = v⌝ ∗ wlatInterp (GF := GF) σ'.wmImg σ'.wmLog ∗
        ctxOwnAt CurCtx.curCtx c σ'.wmWs ∗ a ↦wpo v) :=
  wptstoLoadRule _ c σ σ' ak a v t' b

theorem wptstoStorePostCur (c : CPU) (σ : Wmstate) (m : Wmsg) (a : Int) (v v' : BitVec 8)
    (rl : Bool) :
    msgByte m a = some v' →
    (∀ a', a' ≠ a → msgByte m a' = none) →
    m.wmTid = some c.val →
    wlogAuth (GF := GF) (σ.wmLog ++ [m]) ∗ wlatInterp (GF := GF) σ.wmImg σ.wmLog ∗
      ctxOwnAt CurCtx.curCtx c σ.wmWs ∗ (a ↦wpo v) ⊢
      |==> (wlogAuth (GF := GF) (σ.wmLog ++ [m]) ∗
        wlatInterp (GF := GF) σ.wmImg (σ.wmLog ++ [m]) ∗
        ctxOwnAt CurCtx.curCtx c (storePost σ.wmWs rl a (σ.wmLog.length + 1)) ∗ a ↦wpo v') :=
  wptstoStorePost _ c σ m a v v' rl

theorem nvOkOfWptstoCur (c : CPU) (a : Int) (v : BitVec 8) (img : GMapF PAddr (BitVec 8))
    (log : List Wmsg) :
    wlogAuth (GF := GF) log ∗ ctxMigr (GF := GF) CurCtx.curCtx c ∗
      wlatInterp (GF := GF) img log ∗ (a ↦wpo v) ⊢ ⌜nvOk log c a⌝ :=
  nvOkOfWptstoAt _ c a v img log

end curApi

/-! ## 6. RE-INDEXING: `ctxDom` and the `CtxMorph` structural class (φ-upgrade §1.8)

A lock owns a CONTEXT, exactly as a process does, and its invariant holds that context's facts.
Moving a fact between contexts is the lock library's basic operation, and it must be INVISIBLE to
function proofs: "whatever payload" is what makes it a structural class.  `ctxDom ξ ξ'` is the
permission "ξ''s ledger dominates ξ's", minted at a release and at an acquire and spent only
inside the lock library's lemmas.  IT IS NOT PERSISTENT, AND THAT IS FORCED: a persistent "ξ'
dominates ξ" would license registering into ξ' a floor for a fact created LATER, after ξ's ledger
has grown past ξ''s.  So the token CARRIES ξ's ledger authority, is threaded THROUGH the morphism
rather than consumed by it, and names the view the authority is at. -/

section morph

variable {GF : BundledGFunctors} [WeakGS GF]

/-- "at view `V`, ξ''s ledger dominates ξ's": ξ's authority (which bounds every floor ξ ever
registered by `V`) together with ξ''s registration of `V`. -/
def ctxDom (ξ ξ' : CtxId) (V : View) : IProp GF :=
  iprop(ctxAuth ξ V ∗ ctxViewLb ξ' V)

/-- THE CORE STEP, and the only thing any instance below does: a floor registered against ξ is a
floor registered against ξ'. -/
theorem ctxDomLb (ξ ξ' : CtxId) (V V0 : View) :
    ctxDom (GF := GF) ξ ξ' V ∗ ctxViewLb ξ V0 ⊢ ctxDom ξ ξ' V ∗ ctxViewLb ξ' V0 := by
  unfold ctxDom
  iintro ⟨⟨Ha, #Hd⟩, #Hf⟩
  ihave %hle := ctxViewLbValid ξ V V0 $$ [Ha Hf]
  · iframe Ha Hf
  iframe Ha Hd
  iapply ctxViewLbMono ξ' V V0 hle $$ Hd

/-- THE MINT.  Raise the target's ledger to the source's view; the source's authority then reads
every floor the source ever registered (the release direction; with the roles swapped, the
acquire direction). -/
theorem ctxDomMint (ξ ξ' : CtxId) (V V' : View) (h : V' ≤ V) :
    ctxAuth (GF := GF) ξ V ∗ ctxAuth ξ' V' ⊢ |==> (ctxAuth ξ' V ∗ ctxDom ξ ξ' V) := by
  unfold ctxDom
  iintro ⟨Ha, Ha'⟩
  imod ctxAuthUpdate ξ' V' V h $$ Ha' with Ha'
  ihave #Hd := ctxViewLbGet ξ' V V (fun _ => Nat.le_refl _) $$ Ha'
  imodintro
  iframe Ha' Ha Hd

/-- THE OTHER MINT — the acquire direction, where nothing has to be raised. -/
theorem ctxDomIntro (ξ ξ' : CtxId) (V : View) :
    ctxAuth (GF := GF) ξ V ∗ ctxViewLb ξ' V ⊢ ctxDom ξ ξ' V := by
  unfold ctxDom
  iintro ⟨H1, #H2⟩
  iframe H1 H2

/-- ... and the token's source authority, given back — how a release returns the depositor's
ledger to its `ctxOwn`. -/
theorem ctxDomAuth (ξ ξ' : CtxId) (V : View) : ctxDom (GF := GF) ξ ξ' V ⊢ ctxAuth ξ V := by
  unfold ctxDom
  iintro ⟨H, -⟩
  iexact H

/-- THE STRUCTURAL CLASS.  A payload is a FUNCTION of the context; being a `CtxMorph` is the
(instance-resolved) statement that it can be moved to another context given the permission
(deviation 2). -/
class CtxMorph (R : CtxId → IProp GF) : Prop where
  ctxMorph : ∀ (ξ ξ' : CtxId) (V : View), ctxDom ξ ξ' V ∗ R ξ ⊢ |==> (ctxDom ξ ξ' V ∗ R ξ')

/-- THE REAL INSTANCE — the re-registration.  It is the CLEAN points-to: the owned form carries a
dirty author's breadcrumb, a fact about ξ's own ghost with no image in ξ'; a deposit is flipped
clean by the release (`WeakGhost.wlatFlip`) before it is re-indexed. -/
instance ctxMorphCl (a : Int) (dq : DFrac) (v : BitVec 8) :
    CtxMorph (GF := GF) (fun ξ => wptstoCl ξ a dq v) where
  ctxMorph ξ ξ' V := by
    unfold wptstoCl
    iintro ⟨Hd, ⟨%t, He, #Hf⟩⟩
    icases ctxDomLb ξ ξ' V (viewByte a t) $$ [Hd Hf] with ⟨Hd, #Hf'⟩
    · iframe Hd Hf
    imodintro
    iframe Hd
    iexists t
    iframe He Hf'

/-- ... and the SAME instance at the spelling the client's `<{ … }>` wrapper produces, where the
bound context reaches the points-to through the `CurCtx` projection (deviation 7). -/
instance ctxMorphClCur (a : Int) (dq : DFrac) (v : BitVec 8) :
    CtxMorph (GF := GF) (fun ξ => letI XLK : CurCtx := ⟨ξ⟩; a ↦wp{dq} v) :=
  ctxMorphCl a dq v

/-- CONTEXT-FREE FACTS — tokens, pure facts, persistent knowledge, the residue a payload carries.
Low priority, so that a payload which really does mention its context is matched by the
instances that move it. -/
instance (priority := low) ctxMorphConst (P : IProp GF) : CtxMorph (GF := GF) (fun _ => P) where
  ctxMorph ξ ξ' V := by
    iintro ⟨Hd, HP⟩
    imodintro
    iframe Hd HP

instance ctxMorphSep (R1 R2 : CtxId → IProp GF) [CtxMorph R1] [CtxMorph R2] :
    CtxMorph (GF := GF) (fun ξ => iprop(R1 ξ ∗ R2 ξ)) where
  ctxMorph ξ ξ' V := by
    iintro ⟨Hd, H1, H2⟩
    imod CtxMorph.ctxMorph (R := R1) ξ ξ' V $$ [Hd H1] with ⟨Hd, H1⟩
    · iframe Hd H1
    imod CtxMorph.ctxMorph (R := R2) ξ ξ' V $$ [Hd H2] with ⟨Hd, H2⟩
    · iframe Hd H2
    imodintro
    iframe Hd H1 H2

instance ctxMorphExist {A : Type _} (Φ : A → CtxId → IProp GF) [∀ x, CtxMorph (Φ x)] :
    CtxMorph (GF := GF) (fun ξ => iprop(∃ x : A, Φ x ξ)) where
  ctxMorph ξ ξ' V := by
    iintro ⟨Hd, ⟨%x, H⟩⟩
    imod CtxMorph.ctxMorph (R := Φ x) ξ ξ' V $$ [Hd H] with ⟨Hd, H⟩
    · iframe Hd H
    imodintro
    iframe Hd
    iexists x
    iexact H

instance ctxMorphOr (R1 R2 : CtxId → IProp GF) [CtxMorph R1] [CtxMorph R2] :
    CtxMorph (GF := GF) (fun ξ => iprop(R1 ξ ∨ R2 ξ)) where
  ctxMorph ξ ξ' V := by
    iintro ⟨Hd, (H | H)⟩
    · imod CtxMorph.ctxMorph (R := R1) ξ ξ' V $$ [Hd H] with ⟨Hd, H⟩
      · iframe Hd H
      imodintro
      iframe Hd
      ileft
      iexact H
    · imod CtxMorph.ctxMorph (R := R2) ξ ξ' V $$ [Hd H] with ⟨Hd, H⟩
      · iframe Hd H
      imodintro
      iframe Hd
      iright
      iexact H

/-- The OWNED points-to, moved: available only through the clean form, recorded so that the
asymmetry is a lemma rather than folklore. -/
theorem ctxDomPtsto (ξ ξ' : CtxId) (V : View) (a : Int) (v : BitVec 8) :
    ctxDom (GF := GF) ξ ξ' V ∗ wptstoCl ξ a (DFrac.own 1) v ⊢
      |==> (ctxDom ξ ξ' V ∗ wptsto ξ' a v) :=
  (CtxMorph.ctxMorph (R := fun ξ => wptstoCl (GF := GF) ξ a (DFrac.own 1) v) ξ ξ' V).trans
    (bupd_mono (sep_mono_right (wptstoOfCl ξ' a v)))

end morph

/-- THE PAYLOAD WRAPPER (deviation 7).  A client writes a lock payload as a plain `IProp` with the
bare `↦wp` spellings; this turns it into the `CtxId → IProp` the library needs, by making the
bound context the AMBIENT one inside.  (Rocq: the brace form `<{ P }>`, not `<[ P ]>`, which
clashes with stdpp's insert notation.) -/
macro "<{ " P:term " }>" : term => `(fun ξ : CtxId => letI XLK : CurCtx := ⟨ξ⟩; $P)

end Weak
