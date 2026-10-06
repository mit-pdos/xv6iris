/-
Weak: **THE EXECUTION CONTEXT, and objective ownership indexed by it** — the context's view
authority `ctxAuth` with its persistent whole-view floor `ctxViewLb`, objective ownership `cobj`
at a context, the leaf bridge to `vwpHold`, the running bundle `ctxRun`/`wrunning` with the
ordinary step, MIGRATION (`wrunningResume`) and THE PARK (`wrunningPark`), the M-mode bridge
(`ctxAlloc`, `hartViewToRun`), and the release interface (`viewAddrs`, `ctxAddrsGet/Valid`).

Rocq: `iris/WeakCtx.v` @ xxvzwolszwmp (1cc222280).

Rocq header (in substance, Rocq vocabulary): [WeakObj.wobj] was indexed by [CpuId]; that
stops being fine the moment an S-mode step can trap, yield, and RESUME ON A DIFFERENT HART
([WpNext.wp_next b p (fun CID => K CID)]): every resource written inside [K] is elaborated at
the RESUMING hart, so a frame written outside the binder does not mean the same thing inside
it.  THE FIX IS NOT A NEW FRAME RULE: keep [hart_ws] per-hart (MACHINE state), move the view
authority to a CONTEXT, and objective ownership becomes hart-free.  [CtxId] IS DELIBERATELY NOT
A TYPECLASS, unlike [CpuId]: it is an explicit parameter so that nothing can rebind it and every
context-resource is spelled identically on both sides of the binder.  WHY THE AUTHORITY IS A
SINGLE [flr]-INDEXED AUTH and not [ws_auth]: [ws_le] between two harts is unavailable (hart B
may never have issued a load) and even pointwise-on-the-coherence-map fails (B SEES ξ's write
through its FLOOR, not its map), so the migrating object must be ordered by [⊑], i.e. by [flr];
[ctx_auth] is an authority on the single function [λ a, MaxNat (flr V a)], monotone exactly
along [⊑] — which is exactly what release/acquire delivers.

(The section comments of the Rocq file — the leaf bridge, the running bundle, migration, the
park on the migration invariant, the M-mode bridge, the release interface — are kept on the
corresponding Lean declarations below.)

**Deviations from Rocq.**

1. NAMES: the tree's camelCase convention (name map below).
2. STATEMENT SHAPES (the `WeakGhost` deviation 9 convention): Rocq `P -∗ Q` is `P ⊢ Q`,
   `P -∗ Q -∗ R` is `P ∗ Q ⊢ R`, `P -∗ Q -∗ R -∗ S` is `P ∗ Q ∗ R ⊢ S`, `P ==∗ Q` is
   `P ⊢ |==> Q`, `P -∗ Q ==∗ R` is `P ∗ Q ⊢ |==> R`; `V ⊑ V'` is `V ≤ V'`; `V1 ⊔ V2` is
   `WeakView`'s `View.join`; `monPred_at R V` is `R.monPred_at V`; `MaxNat n` is
   `MaxNat.ofNat n`; `cohUR` is `WeakViewMono.CohUR` (Rocq's `discrete_funUR`).
3. CAMERAS: `Context {!weakViewG Σ}` is `[WeakViewG GF]`; the view authority is
   `iOwn (F := CohRF) ξ.ctxVn …` (the `WeakViewMono` deviation 2 functor; Rocq `own (ctx_vn ξ)`).
4. `Context {!riscvGS Σ, !weakGS Σ}`: the SC instance is dropped (nothing here uses it; the
   `WeakGhost` deviation 10 convention), the ghost state is `[WeakGS GF]`.
5. `CpuId` (Rocq's ambient-hart class, the `` `{CID : CpuId} `` binder of §§5–7) does not exist
   in Lean (`WeakGhost` deviation 12): `ctxRun`, `wrunning` and every lemma about them take the
   hart `cpu : CPU` EXPLICITLY, as their first argument (where the Rocq class binder sat), and
   `cpu_id` is `cpu`.  The header's point is unaffected: `CtxId` is still a plain parameter.
6. SETOID INSTANCES (the `WeakVProp` deviation 4 convention): `cobj_mono'` (a `Proper ((⊢) ==>
   (⊢))` instance) is the theorem `cobjMono'` (so it states the same entailment as `cobjMono`);
   `cobj_proper` (`Proper ((≡) ==> (≡))`) is the theorem `cobjProper` over `⊣⊢` (iris-lean's
   OFE equality is Leibniz).  `flr_fun_op`'s `≡` is `=`.
7. `ctx_valloc`/`ctx_alloc`'s `CtxNames γv γw` is `CtxId.mk γv γw` (`WeakGhost` name map).
8. `view_addrs` is a structural recursion on the count (`n + 1` for `S k`), as in Rocq.
9. Lean-only helper: the private `flrValidInc` (the inclusion step `ctx_view_lb_valid` inlines;
   the twin of `WeakViewMono`'s private `cohValidInc`, which is not exported).

**Rocq → Lean name map.**  §1 `flr_fun`→`flrFun`, `flr_fun_incl`→`flrFunIncl`,
`flr_fun_local_update`→`flrFunLocalUpdate`, `flr_fun_core_id`→`flrFunCoreId`.  §2 `ctx_auth`→
`ctxAuth`, `ctx_view_lb`→`ctxViewLb`, `ctx_view_lb_persistent`→`ctxViewLbPersistent`,
`flr_fun_op`→`flrFunOp`, `ctx_view_lb_get/valid/bot/mono/join`→`ctxViewLbGet/Valid/Bot/Mono/
Join`, `ctx_auth_update`→`ctxAuthUpdate`, `ctx_valloc`→`ctxValloc`.  §3 `cobj`→`cobj`,
`cobj_mono'`→`cobjMono'`, `cobj_mono`→`cobjMono`, `cobj_proper`→`cobjProper`,
`cobj_sep/exist/pure/embed/emp/big_sepL`→`cobjSep/Exist/Pure/Embed/Emp/BigSepL`.  §4
`cobj_to_hold/of_hold/release/acquire`→`cobjToHold/OfHold/Release/Acquire`.  §5 `ctx_run`→
`ctxRun`, `wrunning`→`wrunning`, `ws_le_view`→`wsLeView`, `ctx_run_update/to_hold/of_hold`→
`ctxRunUpdate/ToHold/OfHold`, `wrunning_open/close/acc/step`→`wrunningOpen/Close/Acc/Step`.  §6
`wrunning_resume`→`wrunningResume`, `wrunning_park`→`wrunningPark`.  §7 `ctx_alloc`→`ctxAlloc`,
`hart_view_to_run`→`hartViewToRun`.  §8 `view_addrs`→`viewAddrs`, `view_addrs_le/ge`→
`viewAddrsLe/Ge`, `ctx_addrs_get/valid`→`ctxAddrsGet/Valid`, `ctx_run_addrs_get`→
`ctxRunAddrsGet`.  (None of these names is in `notes/weak-port-dupnames.json`.)

**Not ported:** nothing.

**Statements checked** (diffed against Rocq by hand): all; the changed spellings are the
deviations above.
-/
import Weak.WeakVProp
import Weak.WeakViewMono
import Weak.WeakGhost
import Weak.WeakView
import MachCSL.MonPredExtra

namespace Weak

open Iris Iris.BI Iris.BI.MonPred Iris.ProofMode Iris.Std MachCSL MachCSL.Stdpp

/-! ## 1. The algebra: a view as a single monotone function of floors. -/

/-- Rocq `flr_fun`. -/
def flrFun (V : View) : CohUR := fun a => .ofNat (flr V a)

theorem flrFunIncl (V V' : View) (h : V ≤ V') : flrFun V ≼ flrFun V' :=
  DiscreteFun.inc_iff.mpr fun a => MaxNat.inc_iff.mpr (by
    simp only [flrFun, MaxNat.le_toNat]; exact h a)

theorem flrFunLocalUpdate (V V' : View) (g : CohUR) (h : V ≤ V') :
    (flrFun V, g) ~l~> (flrFun V', flrFun V') := by
  refine (local_update_unital_discrete _ _ _ _).mpr fun z _ heq => ⟨fun _ => trivial, ?_⟩
  funext a
  have ha : flr V a = Nat.max (g a).toNat (z a).toNat := congrArg MaxNat.toNat (congrFun heq a)
  have hc : flr V a ≤ flr V' a := h a
  apply (MaxNat.eq_toNat _ _).mpr
  show flr V' a = Nat.max (flr V' a) (z a).toNat
  simp only [Nat.max_def] at ha ⊢
  (try split at ha) <;> (try split) <;> omega

instance flrFunCoreId (V : View) : CMRA.CoreId (flrFun V) where
  core_id := congrArg some (funext fun a => CMRA.core_eqv_self (flrFun V a))

/-! `CtxId` itself lives in `WeakGhost` (φ-upgrade §1.6): the OWNED POINTS-TO is indexed by a
context, and `WeakVProp` sits below this file.  It is a record of TWO ghost names — this
section's view authority (`ctxVn`) and the per-hart write watermark the migration invariant is
built on (`ctxWn`) — and it is still not a class, for exactly the reason the header gives. -/

/-! ## 2. The context's view: authority and floors. -/

section ctx

variable {GF : BundledGFunctors} [WeakViewG GF]

/-- The context's current view, exactly.  Carries the fragment at the same value, so handing
out a floor is inclusion rather than an update. -/
def ctxAuth (ξ : CtxId) (V : View) : IProp GF :=
  iOwn (F := CohRF) ξ.ctxVn ((● flrFun V) • ◯ flrFun V)

/-- THE PERSISTENT FLOOR, whole-view.  A single fragment rather than a family of per-byte ones:
the object we need to be monotone in is exactly `flr`, so validity, weakening and joining are
each ONE `iOwn` step.  The right disjunct is the unit case: `flrFun viewBot` is `ε`, and
`iOwn γ ε` is not derivable without a `bupd`, so an all-zero floor is carried as a pure fact. -/
def ctxViewLb (ξ : CtxId) (V : View) : IProp GF :=
  iprop(iOwn (F := CohRF) ξ.ctxVn (◯ flrFun V) ∨ ⌜∀ a, flr V a = 0⌝)

instance ctxViewLbPersistent (ξ : CtxId) (V : View) : Persistent (ctxViewLb (GF := GF) ξ V) := by
  unfold ctxViewLb; infer_instance

theorem flrFunOp (V1 V2 : View) : flrFun V1 • flrFun V2 = flrFun (V1 ⊔ V2) := by
  funext a
  apply (MaxNat.eq_toNat _ _).mpr
  show Nat.max (flr V1 a) (flr V2 a) = flr (V1 ⊔ V2) a
  rw [flr_join]

/-- From the validity of an authority-with-fragment joined with another fragment, the second
fragment is pointwise below the authority (deviation 9). -/
private theorem flrValidInc {x s : CohUR}
    (hv : ✓ (((● x : Auth CohUR) • ◯ x) • ◯ s)) (a : Int) : s a ≼ x a := by
  rw [← CMRA.assoc, ← Auth.frag_op] at hv
  have hinc := (Auth.auth_both_valid_discrete.mp hv).1
  exact CMRA.inc_trans (CMRA.inc_op_right _ _) (DiscreteFun.inc_apply hinc a)

theorem ctxViewLbGet (ξ : CtxId) (V V' : View) (h : V' ≤ V) :
    ctxAuth (GF := GF) ξ V ⊢ ctxViewLb ξ V' := by
  unfold ctxAuth ctxViewLb
  iintro H
  ileft
  iapply iOwn_mono (CMRA.inc_trans (Auth.frag_inc_of_inc (flrFunIncl V' V h))
    (CMRA.inc_op_right _ _)) $$ H

theorem ctxViewLbValid (ξ : CtxId) (V V' : View) :
    ctxAuth (GF := GF) ξ V ∗ ctxViewLb ξ V' ⊢ ⌜V' ≤ V⌝ := by
  unfold ctxAuth ctxViewLb
  iintro ⟨Ha, (Hf | %hz)⟩
  · icases iOwn_cmraValid_op $$ [$Ha $Hf] with %hv
    ipureintro
    intro a
    have h := MaxNat.inc_iff.mp (flrValidInc hv a)
    simpa [MaxNat.le_toNat, flrFun] using h
  · ipureintro
    intro a
    rw [hz a]; exact Nat.zero_le _

theorem ctxViewLbBot (ξ : CtxId) : ⊢ ctxViewLb (GF := GF) ξ viewBot := by
  unfold ctxViewLb
  iright
  ipureintro
  exact flr_bot

theorem ctxViewLbMono (ξ : CtxId) (V V' : View) (h : V' ≤ V) :
    ctxViewLb (GF := GF) ξ V ⊢ ctxViewLb ξ V' := by
  unfold ctxViewLb
  iintro (Hf | %hz)
  · ileft
    iapply iOwn_mono (Auth.frag_inc_of_inc (flrFunIncl V' V h)) $$ Hf
  · iright
    ipureintro
    intro a
    have := h a
    rw [hz a] at this
    omega

theorem ctxViewLbJoin (ξ : CtxId) (V1 V2 : View) :
    ctxViewLb (GF := GF) ξ V1 ∗ ctxViewLb ξ V2 ⊢ ctxViewLb ξ (V1 ⊔ V2) := by
  unfold ctxViewLb
  iintro ⟨(H1 | %z1), (H2 | %z2)⟩
  · ileft
    rw [← flrFunOp, Auth.frag_op]
    iapply iOwn_op.mpr
    isplitl [H1]
    · iexact H1
    · iexact H2
  · ileft
    iapply iOwn_mono (Auth.frag_inc_of_inc (flrFunIncl _ _ fun a => by
      rw [flr_join, z2 a]; omega)) $$ H1
  · ileft
    iapply iOwn_mono (Auth.frag_inc_of_inc (flrFunIncl _ _ fun a => by
      rw [flr_join, z1 a]; omega)) $$ H2
  · iright
    ipureintro
    intro a
    rw [flr_join, z1 a, z2 a]; rfl

/-- THE UPDATE.  Monotone along `≤` and nothing finer — which is the whole point of the
header's finding. -/
theorem ctxAuthUpdate (ξ : CtxId) (V V' : View) (h : V ≤ V') :
    ctxAuth (GF := GF) ξ V ⊢ |==> ctxAuth ξ V' :=
  iOwn_update (Auth.auth_update (flrFunLocalUpdate V V' _ h))

theorem ctxValloc (V : View) :
    ⊢@{IProp GF} |==> ∃ γ : GName, iOwn (F := CohRF) γ ((● flrFun V) • ◯ flrFun V) := by
  imod iOwn_alloc (F := CohRF) ((● flrFun V : Auth CohUR) • ◯ flrFun V)
    (Auth.auth_both_valid_discrete.mpr ⟨CMRA.inc_refl _, fun _ => trivial⟩) with ⟨%γ, H⟩
  imodintro
  iexists γ
  iexact H

end ctx

/-! ## 3. `cobj`: objective ownership at a context.

Verbatim `WeakObj.wobj` with the index changed.  The structural laws are the same laws, proved
the same way — they only ever use the lower bound's semilattice structure. -/

section cobj

variable {GF : BundledGFunctors} [WeakViewG GF]

/-- Rocq `cobj`. -/
def cobj (ξ : CtxId) (R : VProp GF) : IProp GF :=
  iprop(∃ V : View, ctxViewLb ξ V ∗ R.monPred_at V)

/-- Rocq's `Proper ((⊢) ==> (⊢)) (cobj ξ)` instance (deviation 6). -/
theorem cobjMono' (ξ : CtxId) {R R' : VProp GF} (h : R ⊢ R') : cobj ξ R ⊢ cobj ξ R' := by
  unfold cobj
  iintro ⟨%V, #Hlb, HR⟩
  iexists V
  iframe Hlb
  iapply entails_at.mp h V $$ HR

theorem cobjMono (ξ : CtxId) (R R' : VProp GF) (h : R ⊢ R') : cobj ξ R ⊢ cobj ξ R' :=
  cobjMono' ξ h

/-- Rocq's `Proper ((≡) ==> (≡)) (cobj ξ)` instance, over `⊣⊢` (deviation 6): what lets the
`bi` laws be used UNDER `cobj` — e.g. `bigSepL_nil` inside the modality. -/
theorem cobjProper (ξ : CtxId) {R R' : VProp GF} (h : R ⊣⊢ R') : cobj ξ R ⊣⊢ cobj ξ R' :=
  ⟨cobjMono ξ R R' h.mp, cobjMono ξ R' R h.mpr⟩

theorem cobjSep (ξ : CtxId) (R R' : VProp GF) :
    cobj ξ iprop(R ∗ R') ⊣⊢ cobj ξ R ∗ cobj ξ R' := by
  unfold cobj
  constructor
  · iintro ⟨%V, #Hlb, ⟨HR, HR'⟩⟩
    isplitl [HR]
    · iexists V
      iframe Hlb HR
    · iexists V
      iframe Hlb HR'
  · iintro ⟨⟨%V1, #H1, HR⟩, ⟨%V2, #H2, HR'⟩⟩
    iexists V1 ⊔ V2
    isplitr
    · iapply ctxViewLbJoin ξ V1 V2
      isplitl
      · iexact H1
      · iexact H2
    · isplitl [HR]
      · iapply R.monPred_mono (View.join_l V1 V2) $$ HR
      · iapply R'.monPred_mono (View.join_r V1 V2) $$ HR'

theorem cobjExist (ξ : CtxId) {A : Type _} (Φ : A → VProp GF) :
    cobj ξ iprop(∃ x, Φ x) ⊣⊢ ∃ x, cobj ξ (Φ x) := by
  unfold cobj
  constructor
  · iintro ⟨%V, #Hlb, ⟨%x, HR⟩⟩
    iexists x
    iexists V
    iframe Hlb HR
  · iintro ⟨%x, ⟨%V, #Hlb, HR⟩⟩
    iexists V
    iframe Hlb
    iexists x
    iexact HR

theorem cobjPure (ξ : CtxId) (φ : Prop) : cobj ξ (iprop(⌜φ⌝) : VProp GF) ⊣⊢ ⌜φ⌝ := by
  unfold cobj
  constructor
  · iintro ⟨%V, -, HR⟩
    iexact HR
  · iintro %h
    iexists viewBot
    isplitr
    · iapply ctxViewLbBot ξ
    · ipureintro
      exact h

theorem cobjEmbed (ξ : CtxId) (P : IProp GF) : cobj ξ (iprop(⎡P⎤) : VProp GF) ⊣⊢ P := by
  unfold cobj
  constructor
  · iintro ⟨%V, -, HR⟩
    iexact HR
  · iintro HP
    iexists viewBot
    isplitr
    · iapply ctxViewLbBot ξ
    · iexact HP

theorem cobjEmp (ξ : CtxId) : cobj ξ (iprop(emp) : VProp GF) ⊣⊢ emp := by
  unfold cobj
  constructor
  · iintro ⟨%V, -, H⟩
    iexact H
  · iintro H
    iexists viewBot
    isplitr
    · iapply ctxViewLbBot ξ
    · iexact H

theorem cobjBigSepL (ξ : CtxId) {A : Type _} (l : List A) (Φ : Nat → A → VProp GF) :
    cobj ξ iprop([∗list] k ↦ x ∈ l, Φ k x) ⊣⊢ [∗list] k ↦ x ∈ l, cobj ξ (Φ k x) := by
  induction l generalizing Φ with
  | nil =>
    exact (cobjProper ξ BigSepL.bigSepL_nil).trans ((cobjEmp (GF := GF) ξ).trans BigSepL.bigSepL_nil.symm)
  | cons x l ih =>
    exact (cobjProper ξ BigSepL.bigSepL_cons).trans
      ((cobjSep ξ _ _).trans
        ((sep_congr .rfl (ih fun k y => Φ (k + 1) y)).trans
          (BigSepL.bigSepL_cons (Φ := fun k y => cobj ξ (Φ k y))).symm))

/-! ## 4. THE LEAF BRIDGE.  A leaf takes its frame as `vwpHold F ws`, indexed by the wstate the
caller must not name.  These two convert, for an arbitrary `R`, given only the context's
authority. -/

theorem cobjToHold (ξ : CtxId) (ws : Wstate) (R : VProp GF) :
    ctxAuth (GF := GF) ξ (wsView ws) ∗ cobj ξ R ⊢ ctxAuth ξ (wsView ws) ∗ vwpHold R ws := by
  unfold cobj vwpHold
  iintro ⟨Ha, ⟨%V, #Hlb, HR⟩⟩
  ihave %hle := ctxViewLbValid ξ (wsView ws) V $$ [Ha Hlb]
  · isplitl [Ha]
    · iexact Ha
    · iexact Hlb
  iframe Ha
  iapply R.monPred_mono hle $$ HR

theorem cobjOfHold (ξ : CtxId) (ws : Wstate) (R : VProp GF) :
    ctxAuth (GF := GF) ξ (wsView ws) ∗ vwpHold R ws ⊢ ctxAuth ξ (wsView ws) ∗ cobj ξ R := by
  unfold cobj vwpHold
  iintro ⟨Ha, HR⟩
  ihave #Hlb := ctxViewLbGet ξ (wsView ws) (wsView ws) (fun _ => Nat.le_refl _) $$ Ha
  iframe Ha
  iexists wsView ws
  iframe Hlb HR

/-- The two halves of a lock/park boundary, for an arbitrary payload. -/
theorem cobjRelease (ξ : CtxId) (V : View) (T : Nat) (R : VProp GF) (hT : ∀ a, flr V a ≤ T) :
    ctxAuth (GF := GF) ξ V ∗ cobj ξ R ⊢ ctxAuth ξ V ∗ R.monPred_at (viewScl T) := by
  unfold cobj
  iintro ⟨Ha, ⟨%V0, #Hlb, HR⟩⟩
  ihave %hle := ctxViewLbValid ξ V V0 $$ [Ha Hlb]
  · isplitl [Ha]
    · iexact Ha
    · iexact Hlb
  iframe Ha
  iapply R.monPred_mono (fun a => by rw [flr_scl_eq]; exact Nat.le_trans (hle a) (hT a)) $$ HR

theorem cobjAcquire (ξ : CtxId) (V : View) (T : Nat) (R : VProp GF) (hT : ∀ a, T ≤ flr V a) :
    ctxAuth (GF := GF) ξ V ∗ R.monPred_at (viewScl T) ⊢ ctxAuth ξ V ∗ cobj ξ R := by
  unfold cobj
  iintro ⟨Ha, HR⟩
  ihave #Hlb := ctxViewLbGet ξ V (viewScl T) (fun a => by rw [flr_scl_eq]; exact hT a) $$ Ha
  iframe Ha
  iexists viewScl T
  iframe Hlb HR

end cobj

/-! ## 5. `wrunning`: which context this hart is running.

The successor of `WeakGhost.hartView`.  Same shape — the hart's wstate paired with the authority
that tracks it — but the authority belongs to the CONTEXT, so the pairing is what migrates. -/

/-- Pure: a `wsLe` step raises the hart's view. -/
theorem wsLeView (ws ws' : Wstate) (h : wsLe ws ws') : wsView ws ≤ wsView ws' :=
  wsView_mono ws ws' h

section running

variable {GF : BundledGFunctors} [WeakGS GF]

/-- THE CONTEXT'S HALF OF THE BUNDLE (φ-upgrade §1.6).  Two authorities, one resource: the VIEW
authority §2 is about, and the MIGRATION INVARIANT `WeakGhost.ctxMigr` — "every hart this
context has written through, other than the one it is running on, has published what it
wrote".  It is scheduler state, exactly like the view authority: a caller threads it because it
threads `wrunning`, never because a byte it owns is dirty. -/
def ctxRun (cpu : CPU) (ξ : CtxId) (ws : Wstate) : IProp GF :=
  iprop(ctxAuth ξ (wsView ws) ∗ ctxMigr ξ cpu)

/-- Rocq `wrunning`. -/
def wrunning (cpu : CPU) (ξ : CtxId) : IProp GF :=
  iprop(∃ ws : Wstate, hartWs cpu ws ∗ ctxRun cpu ξ ws)

/-- THE ONLY UPDATE A LEAF PERFORMS, and the reason `ctxRun` is a named definition: every
ws-threading leaf calls exactly this, and the migration half rides through untouched. -/
theorem ctxRunUpdate (cpu : CPU) (ξ : CtxId) (ws ws' : Wstate) (h : wsLe ws ws') :
    ctxRun (GF := GF) cpu ξ ws ⊢ |==> ctxRun cpu ξ ws' := by
  unfold ctxRun
  iintro ⟨Ha, Hm⟩
  imod ctxAuthUpdate ξ _ (wsView ws') (wsLeView ws ws' h) $$ Ha with Ha
  imodintro
  iframe Ha Hm

/-- §4's leaf bridge, against the bundle rather than the bare view authority. -/
theorem ctxRunToHold (cpu : CPU) (ξ : CtxId) (ws : Wstate) (R : VProp GF) :
    ctxRun (GF := GF) cpu ξ ws ∗ cobj ξ R ⊢ ctxRun cpu ξ ws ∗ vwpHold R ws := by
  unfold ctxRun
  iintro ⟨⟨Ha, Hm⟩, HR⟩
  icases cobjToHold ξ ws R $$ [Ha HR] with ⟨Ha, HR⟩
  · isplitl [Ha]
    · iexact Ha
    · iexact HR
  iframe Ha Hm HR

theorem ctxRunOfHold (cpu : CPU) (ξ : CtxId) (ws : Wstate) (R : VProp GF) :
    ctxRun (GF := GF) cpu ξ ws ∗ vwpHold R ws ⊢ ctxRun cpu ξ ws ∗ cobj ξ R := by
  unfold ctxRun
  iintro ⟨⟨Ha, Hm⟩, HR⟩
  icases cobjOfHold ξ ws R $$ [Ha HR] with ⟨Ha, HR⟩
  · isplitl [Ha]
    · iexact Ha
    · iexact HR
  iframe Ha Hm HR

theorem wrunningOpen (cpu : CPU) (ξ : CtxId) :
    wrunning (GF := GF) cpu ξ ⊢ ∃ ws, hartWs cpu ws ∗ ctxRun cpu ξ ws := .rfl

theorem wrunningClose (cpu : CPU) (ξ : CtxId) (ws : Wstate) :
    hartWs (GF := GF) cpu ws ∗ ctxRun cpu ξ ws ⊢ wrunning cpu ξ := by
  unfold wrunning
  iintro ⟨H1, H2⟩
  iexists ws
  iframe H1 H2

/-- THE OWN LEAVES' ACCESSOR.  A memory leaf takes `wrunning ξ` and needs the migration
invariant out of it for the duration of its ghost section; nothing else in the bundle is
touched. -/
theorem wrunningAcc (cpu : CPU) (ξ : CtxId) :
    wrunning (GF := GF) cpu ξ ⊢ ctxMigr ξ cpu ∗ (ctxMigr ξ cpu -∗ wrunning cpu ξ) := by
  unfold wrunning ctxRun
  iintro ⟨%ws, Hws, Ha, Hm⟩
  iframe Hm
  iintro Hm
  iexists ws
  iframe Hws Ha Hm

/-- The ordinary step: the hart's wstate grew, so the context's view grows with it. -/
theorem wrunningStep (cpu : CPU) (ξ : CtxId) (ws ws' : Wstate) (h : wsLe ws ws') :
    ctxRun (GF := GF) cpu ξ ws ∗ hartWs cpu ws' ⊢ |==> wrunning cpu ξ := by
  iintro ⟨Ha, Hws⟩
  imod ctxRunUpdate cpu ξ ws ws' h $$ Ha with Ha
  imodintro
  iapply wrunningClose cpu ξ ws'
  iframe Hws Ha

/-! ## 6. MIGRATION.

Hart A parks the context at whatever view it had; hart B picks it up.  The only premises are
the two halves of the synchronisation the scheduler already performs — A released past its
entire view, B acquired past that timestamp — and NEITHER MENTIONS A RESOURCE.  Note what is
NOT required: no relation between hart A's and hart B's wstates. -/

theorem wrunningResume (cpu : CPU) (ξ : CtxId) (VA : View) (ws : Wstate) (T : Nat)
    (hT : ∀ a, flr VA a ≤ T)      -- A released past its whole view
    (hacq : T ≤ ws.wVrNew) :       -- B acquired past T
    ctxAuth (GF := GF) ξ VA ∗ ctxMigrAll ξ ∗ hartWs cpu ws ⊢ |==> wrunning cpu ξ := by
  iintro ⟨Ha, Hall, Hws⟩
  imod ctxAuthUpdate ξ VA (wsView ws) (fun a => by
    rw [flr_wsView]; exact Nat.le_trans (hT a) (Nat.le_trans hacq (Nat.le_max_left _ _))) $$ Ha
    with Ha
  imodintro
  iapply wrunningClose cpu ξ ws
  iframe Hws
  unfold ctxRun
  iframe Ha
  iapply ctxMigrAllRun ξ cpu $$ Hall

/-! ## 6'. THE PARK, ON THE MIGRATION INVARIANT (φ-upgrade §1.6).

The scheduler's handoff store is a RELEASE at the log's fresh top, so it publishes every
position at or below the log's length — which, by the invariant's own position bound, is every
position this context has written through the parking hart.  So the live-hart exception
discharges, and what comes out is the PARKED form `ctxMigrAll`, which satisfies the invariant at
whatever hart the context is about to resume on.  No byte, no points-to, no view in the
statement. -/

theorem wrunningPark (cpu : CPU) (ξ : CtxId) (log : List Wmsg) (N : Nat) (ws : Wstate)
    (hN : log.length ≤ N) :
    wlogAuth (GF := GF) log ∗ pubFloor cpu N ∗ ctxRun cpu ξ ws ⊢
      wlogAuth log ∗ ctxAuth ξ (wsView ws) ∗ ctxMigrAll ξ := by
  unfold ctxRun
  iintro ⟨Hlog, #Hpf, Ha, Hm⟩
  icases ctxMigrPark ξ cpu log N hN $$ [Hlog Hm] with ⟨Hlog, Hall⟩
  · isplitl [Hlog]
    · iexact Hlog
    · isplitr
      · iexact Hpf
      · iexact Hm
  iframe Hlog Ha Hall

/-! ## 7. THE M-MODE BRIDGE.

`WeakAdequacy` hands each hart a `hartView` — its wstate with the value hidden.  A hart turns
that into a context exactly once, at the top of its chain: a boot context comes into existence
when execution starts. -/

/-- Allocation: BOTH ghost names, and the migration invariant at its empty map (a context that
has not run has written through no hart). -/
theorem ctxAlloc (cpu : CPU) (V : View) :
    ⊢@{IProp GF} |==> ∃ ξ : CtxId, ctxAuth ξ V ∗ ctxMigr ξ cpu := by
  imod ctxValloc (GF := GF) V with ⟨%γv, Hv⟩
  imod ctxWrAlloc (GF := GF) with ⟨%γw, Hw⟩
  imodintro
  iexists CtxId.mk γv γw
  unfold ctxAuth
  isplitl [Hv]
  · iexact Hv
  · iapply ctxMigrEmpty (CtxId.mk γv γw) cpu $$ Hw

theorem hartViewToRun (cpu : CPU) :
    hartView (GF := GF) cpu ⊢ |==> ∃ ξ : CtxId, wrunning cpu ξ := by
  unfold hartView
  iintro ⟨%ws, Hws⟩
  imod ctxAlloc (GF := GF) cpu (wsView ws) with ⟨%ξ, Ha, Hm⟩
  imodintro
  iexists ξ
  iapply wrunningClose cpu ξ ws
  iframe Hws
  unfold ctxRun
  iframe Ha Hm

end running

/-! ## 8. THE RELEASE INTERFACE: a floor at a FINITE SET of addresses.

A release store hands back `∀ j < 8, T ≤ flr (wsView ws') (accAddr ea j)` — a statement that
NAMES `ws'`, so any wrapper hiding the post-state erases it.  `ctxViewLb` is the objective form;
what remains is only to say WHICH view — the join of the `n` single-byte views — and that is a
fold.  ADDRESSES ARE A FUNCTION `f : Nat → Int`, not `accAddr ea`, so the same lemmas serve a
store of any width and any address pattern; `f` need not be injective. -/

/-- Rocq `view_addrs`. -/
def viewAddrs (f : Nat → Int) : Nat → Nat → View
  | 0, _ => viewBot
  | k + 1, T => viewByte (f k) T ⊔ viewAddrs f k T

/-- The bound is BELOW a view exactly when it holds at each address. -/
theorem viewAddrsLe (f : Nat → Int) (n T : Nat) (V : View)
    (hj : ∀ j : Nat, j < n → T ≤ flr V (f j)) : viewAddrs f n T ≤ V := by
  induction n with
  | zero => exact viewBot_le V
  | succ k ih =>
    exact View.join_lub _ _ _ ((viewByte_le _ _ _).mpr (hj k (Nat.lt_succ_self k)))
      (ih fun j hlt => hj j (Nat.lt_succ_of_lt hlt))

/-- ... and it really does bound each address (the converse, which a consumer spends). -/
theorem viewAddrsGe (f : Nat → Int) (n T : Nat) (j : Nat) (hlt : j < n) :
    T ≤ flr (viewAddrs f n T) (f j) := by
  induction n with
  | zero => omega
  | succ k ih =>
    simp only [viewAddrs]
    rw [flr_join]
    by_cases hjk : j = k
    · subst hjk
      rw [flr_byte_eq]; exact Nat.le_max_left _ _
    · have := ih (by omega)
      exact Nat.le_trans this (Nat.le_max_right _ _)

section release

variable {GF : BundledGFunctors} [WeakViewG GF]

/-- BUILD: what a release store's post-state authority yields. -/
theorem ctxAddrsGet (ξ : CtxId) (V : View) (f : Nat → Int) (n T : Nat)
    (hj : ∀ j : Nat, j < n → T ≤ flr V (f j)) :
    ctxAuth (GF := GF) ξ V ⊢ ctxViewLb ξ (viewAddrs f n T) :=
  ctxViewLbGet ξ V _ (viewAddrsLe f n T V hj)

/-- SPEND: what an acquirer recovers, against ITS OWN authority — the two authorities may be at
different views and even at different harts; the token is the same proposition on both
sides. -/
theorem ctxAddrsValid (ξ : CtxId) (V : View) (f : Nat → Int) (n T : Nat) :
    ctxAuth (GF := GF) ξ V ∗ ctxViewLb ξ (viewAddrs f n T) ⊢
      ⌜∀ j : Nat, j < n → T ≤ flr V (f j)⌝ := by
  iintro H
  ihave %hle := ctxViewLbValid ξ V (viewAddrs f n T) $$ H
  ipureintro
  intro j hj
  exact Nat.le_trans (viewAddrsGe f n T j hj) (hle (f j))

end release

/-! ... and the same BUILD against the RUNNING BUNDLE, which is what a leaf actually holds since
φ-upgrade §1.6: the migration half rides along untouched. -/

section releaseRun

variable {GF : BundledGFunctors} [WeakGS GF]

theorem ctxRunAddrsGet (cpu : CPU) (ξ : CtxId) (ws : Wstate) (f : Nat → Int) (n T : Nat)
    (hj : ∀ j : Nat, j < n → T ≤ flr (wsView ws) (f j)) :
    ctxRun (GF := GF) cpu ξ ws ⊢ ctxViewLb ξ (viewAddrs f n T) := by
  unfold ctxRun
  iintro ⟨Ha, -⟩
  iapply ctxAddrsGet ξ (wsView ws) f n T hj $$ Ha

end releaseRun

end Weak

