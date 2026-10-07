/-
Weak: **Phase 2, part 1 of the spinlock plan -- THE HANDLE SURFACE for critical sections**: the
value-tracking owned byte `Rbo`, the handle predicate `hdl`, the GENERIC owned load / store /
forwarded-reload leaves, and their instantiation at the Phase-1b instance `spinOb5` / `splPol`.
(Files: this one; `AxSpinH2` acquire/release contracts; `AxSpinH3` the `[ld x; addi; sd x; ld x]`
critical-section certificate.)

Rocq: `iris/AxSpinH.v` @ xxvzwolszwmp.

## The Rocq header, in substance

DEFINITIONS
  `Rbo γ GD a e mv` (§1) = `AxSpinProt5.Rb` (full history auth of byte `a`, tied at `e`) + "the
    history's LAST value is `v`" when `mv = some v` (the image value if the history is empty).
    `Rbo a e none ⊣⊢ RL [a] e` (`RL1Rbo`/`RboRL1`).
  `hdl O a e mv` (§2) = `e ↦ₐ O a e mv` -- THE HANDLE POINTS-TO "a ↦ₕ{e} mv": the owned byte
    arrives at `e`'s annotation in phase 2.  The ANCHOR `e` is part of the predicate.
    `hdlN` = n bytes at one anchor (definition only; leaves are 1-byte).
PROVED
  §1 `RboWrite` (phase-2 owned write: history appended IN THE STORE'S FLOW EQUATION, re-tied at
     the store, last value = stored byte); `RboRead` (phase-2 owned read: under "every po-earlier
     same-address write is gmo-before the read" and the handout `WPh`, the read value IS the last
     history value -- `ownedReadRule` case (i), or the genesis/image case refuted against
     ownInv's snapshots -- re-tied at the read).
  §2 GENERIC LEAVES over ANY `axGA2` instance / policy, against the OWNED-CLASS INTERFACE
     (hypotheses: `O`, side conditions `okw`/`okr`, flow equations `HOw`/`HOr`/`HOp`, policy
     facts `HpolGmo`/`HpolIntro`) -- event level (`ev*`) and on hand instruction nodes (`wpd*`):
       `wpdLdOwn`: `a ↦ₕ{e} mv`, `e ∈ lobp r`, every po-earlier same-address write gmo-before
         `r` ⇒ `a ↦ₕ{r} (some v)` ∗ `r ↦ₐ ⌜mv = some v0 → v = v0⌝`;
       `wpdSdOwn`: `a ↦ₕ{e} mv`, `e ∈ lobp w` ⇒ `a ↦ₕ{w} (some b)`;
       `wpdReloadOwn` (FORWARDED-RELOAD LEAF): store `w` of `b` then load `r` of the same byte,
         no same-address store po-between ⇒ `∃ e' ∈ {w, r}, a ↦ₕ{e'} (some b)` ∗ `r ↦ₐ ⌜v = b⌝`
         -- the case split on `gmoLt w r` INSIDE the leaf (ordered: the handle moves through
         `HOr`; forwarded: `ownedReadRuleFwd`, nothing drawn, handle stays at `w`).
  §3 the interface at `spinOb5`/`splPol`: `fe5hWrite`/`fe5hRead`/`fe5hPlain` (via `fe5Build`),
     `splPolGmo`/`splPolIntro`.
FINDINGS (anchors visible; load→load on one address not covered; values phase-2; AxSpinWit
FINDING 1 impossible for a handle): see the Rocq header (unchanged by the port).

## Deviations from Rocq

1. VOCABULARY (as `AxSpinProt5`/`AxSpinProt6`): `Z` ↦ `Int`, `bv 8` ↦ `BitVec 8`, `gd_g GD` ↦
   `GD.gdG`, `gx_img G a` ↦ `G.gxImg a`, `last H` ↦ `H.getLast?`, `H.*1` ↦ `H.map Prod.fst`,
   `grow GD i !! k` ↦ `(AxOpsem.grow GD i)[k]?`, `S k` ↦ `k + 1`, `pa_z` ↦ `paZ`.
2. CONTEXTS: Rocq section variables are explicit leading arguments in Rocq's order, only where
   Rocq's section mechanism includes them (§1 `γ GD`; §2 `GD N obSt0 obi nm [pol] Hwf cpu Hcons O
   okw okr HpolGmo HpolIntro HOw HOr HOp`, the ones in `Proof using` / the statement; §3
   `lk x Cl cv GT nm Hcons HlkX`; unused-but-listed ones are `_`-named).  O2 STAGE C (as
   `AxSpinProt2` deviation 1): Rocq's `Tf` argument of `AxGA2`/`tierA_wpd` is gone.
   `invGS_gen HasNoLc Σ` ↦ `[InvGS_gen hlc GF]` for any `hlc`.  The local instances: `hG` ↦
   `shG GD N obSt0 obi nm` (reducible, passed explicitly), `h5_pol` ↦ `splPol GT`, `h5_G` ↦
   `AxSpinProt6.s5G lk x Cl cv GT nm` (passed explicitly).  `hdl`/`hdlN`/`hdlN1` take `O` only.
3. STATEMENT SHAPES (as `AxSpinProt5` deviation 3): §1 `P -∗ Q -∗ R` ↦ `P ∗ Q ⊢ R`,
   `P -∗ Q ==∗ R` ↦ `P ∗ Q ⊢ |==> R`; §2/§3 wand chains ↦ `⊢ A -∗ B -∗ …`; pure premises stay
   `→`.  lean-sail hand nodes (as `AxSpinProt3` deviation 3): `Next (MemRead 1 (l3p_rreq l3p_akP
   pa)) KK` ↦ `.impure (.ok (.memRead 1 64 (l3pRreq l3pAkP pa))) KK`, answers `.Ok (v, none)`;
   `MemWrite` likewise.
4. PROOF ROUTE (not statements): `evReloadOwn` splits on `gmoLt w r` classically (Rocq: on the
   boolean `gmo_lt_b`); `RboRead` case-splits on `H.getLast?` (Rocq: on `H = []`, then `last H`).

**Rocq → Lean name map.**  `hval` `hval`, `Rbo` `Rbo`, `Rbo_of_Rb` `RboOfRb`, `Rbo_Rb` `RboRb`,
`RL1_Rbo` `RL1Rbo`, `Rbo_RL1` `RboRL1`, `Rbo_write` `RboWrite`, `Rbo_read` `RboRead`, `hdl` `hdl`,
`hdl_n` `hdlN`, `hdl_n_1` `hdlN1`, `ev_ld_own` `evLdOwn`, `ev_sd_own` `evSdOwn`,
`po_writes_gmo_before` `poWritesGmoBefore`, `ev_reload_own` `evReloadOwn`, `wpd_ld_own`
`wpdLdOwn`, `wpd_sd_own` `wpdSdOwn`, `wpd_reload_own` `wpdReloadOwn`, `okw5` `okw5`, `okr5`
`okr5`, `spl_pol_gmo` `splPolGmo`, `spl_pol_intro` `splPolIntro`, `fe5h_write` `fe5hWrite`,
`rd_nX` `rdNX`, `rd_not_lkread` `rdNotLkread`, `fe5h_read` `fe5hRead`, `fe5h_plain` `fe5hPlain`.
Lean-only (file-qualified): `AxSpinH.histInOfCov` (`Rbo_read`'s inner `iAssert`: every covered
write is in the auth's history; a copy of `AxSpinX.histInOfCov`, not imported here).

**Dropped:** none (30 Rocq decls incl. the 3 local instances `hG`/`h5_pol`/`h5_G` (inlined);
28 Lean = 27 + 1 Lean-only).
-/
import Weak.AxSpinProt4
import Weak.AxSpinProt7b

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std Iris.Std.PartialMap MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D

/-! # 1. The VALUE-TRACKING owned byte `Rbo a e mv` -/

def hval (G : Gexec) (a : Int) (H : List Hent) (v : BitVec 8) : Prop :=
  (H = [] ∧ G.gxImg a = some v) ∨ ∃ w, H.getLast? = some (w, v)

section rbo
variable {GF : BundledGFunctors} [AxlogG GF Hent]

def Rbo (γ : GName) (GD : Gdexec) (a : Int) (e : Geid) (mv : Option (BitVec 8)) : IProp GF :=
  iprop(∃ H, histAuth γ a 1 H ∗
    ⌜(H = [] ∨ tieBase GD.gdG (H.map Prod.fst) e) ∧ hwfa GD a H ∧
      ∀ v, mv = some v → hval GD.gdG a H v⌝)

theorem RboOfRb (γ : GName) (GD : Gdexec) (a : Int) (e : Geid) :
    Rb (GF := GF) γ GD a e ⊢ Rbo γ GD a e none := by
  unfold Rb Rbo
  iintro ⟨%H, Ha, %hp⟩
  iexists H
  isplitl [Ha]
  · iexact Ha
  · ipureintro
    exact ⟨hp.1, hp.2, fun _ h => by cases h⟩

theorem RboRb (γ : GName) (GD : Gdexec) (a : Int) (e : Geid) (mv : Option (BitVec 8)) :
    Rbo (GF := GF) γ GD a e mv ⊢ Rb γ GD a e := by
  unfold Rb Rbo
  iintro ⟨%H, Ha, %hp⟩
  iexists H
  isplitl [Ha]
  · iexact Ha
  · ipureintro
    exact ⟨hp.1, hp.2.1⟩

theorem RL1Rbo (γ : GName) (GD : Gdexec) (a : Int) (e : Geid) :
    RL (GF := GF) γ GD [a] e ⊢ Rbo γ GD a e none := by
  unfold RL
  exact BigSepL.bigSepL_singleton.1.trans (RboOfRb γ GD a e)

theorem RboRL1 (γ : GName) (GD : Gdexec) (a : Int) (e : Geid) (mv : Option (BitVec 8)) :
    Rbo (GF := GF) γ GD a e mv ⊢ RL γ GD [a] e := by
  unfold RL
  exact (RboRb γ GD a e mv).trans
    (BigSepL.bigSepL_singleton (Φ := fun _ b => Rb (GF := GF) γ GD b e)).2

/-- THE OWNED WRITE (single byte, phase 2): the history is appended in `w`'s flow equation, the
handle re-ties at `w` with last value `b`. -/
theorem RboWrite (γ : GName) (GD : Gdexec) (X : GSet Int) (a : Int) (s : GSet Geid) (e w : Geid)
    (b : BitVec 8) (mv : Option (BitVec 8)) :
    w ∉ s → a ∈ X → gmoLt GD.gdG e w → gwritesByte GD.gdG w a b →
    (∀ a' v', gwritesByte GD.gdG w a' v' → a' = a) →
    ownInv (GF := GF) X γ GD s ∗ Rbo γ GD a e mv ⊢
      |==> (ownInv X γ GD (({w} : GSet Geid) ∪ s) ∗ Rbo γ GD a w (some b)) := by
  intro hn ha hew hw hsg
  unfold Rbo
  iintro ⟨Hinv, %H, Hh, %hp⟩
  obtain ⟨ht, ⟨hwr, hch⟩, -⟩ := hp
  imod (ownInvWrite X γ GD s w a b H hn ha hw hsg) $$ [$Hinv $Hh] with ⟨Hinv, Hh⟩
  imodintro
  isplitl [Hinv]
  · iexact Hinv
  · iexists (H ++ [(w, b)])
    isplitl [Hh]
    · iexact Hh
    · ipureintro
      refine ⟨Or.inr (tieWrite GD.gdG H w b), ⟨?_, ?_⟩, ?_⟩
      · intro p hp
        rcases List.mem_append.1 hp with h | h
        · exact hwr p h
        · simp only [List.mem_singleton] at h
          subst h
          exact hw
      · rw [List.map_append]
        refine AxSpinProt.chainWithSnoc' _ _ w hch ?_
        intro wl hl
        rcases ht with rfl | ht | ⟨wl', ht, hlt⟩
        · simp at hl
        · rw [ht] at hl
          cases hl
          exact hew
        · rw [ht] at hl
          cases hl
          exact gmoLtTrans _ _ _ _ hlt hew
      · intro v hv
        cases hv
        unfold hval
        exact Or.inr ⟨w, by simp⟩

/-- (Lean-only) `Rbo_read`'s inner `iAssert`: every write covered (gmo-before `r`) is in the
auth's history. -/
theorem AxSpinH.histInOfCov (γ : GName) (GD : Gdexec) (a : Int) (r : Geid) (H : List Hent) :
    histAuth (GF := GF) γ a 1 H ∗
      (∀ w v, ⌜gwritesByte GD.gdG w a v⌝ -∗ ⌜gmoLt GD.gdG w r⌝ -∗
        ∃ H', ⌜w ∈ H'.map Prod.fst⌝ ∗ histSnap γ a H') ⊢
      ⌜∀ w v', gwritesByte GD.gdG w a v' → gmoLt GD.gdG w r → w ∈ H.map Prod.fst⌝ := by
  refine (BI.forall_intro fun w => ?_).trans BI.pure_forall.2
  refine (BI.forall_intro fun v => ?_).trans BI.pure_forall.2
  refine (BI.forall_intro fun hw => ?_).trans BI.pure_forall.2
  refine (BI.forall_intro fun hlt => ?_).trans BI.pure_forall.2
  iintro ⟨Ha, Hcov⟩
  icases Hcov $$ %w %v %hw %hlt with ⟨%H', %hw', Hs⟩
  iapply histSnapIn γ a 1 H H' w hw'
  isplitl [Ha]
  · iexact Ha
  · iexact Hs

/-- THE OWNED READ (phase 2): `e` gmo-before `r`, every po-EARLIER same-address write of `r`
gmo-before `r`, `r` handed every gmo-earlier write (`WPh`).  The read value is the history's last
value: the handle re-ties at `r` with last value `v`, and if it carried `v0`, `v = v0`. -/
theorem RboRead (γ : GName) (GD : Gdexec) (X : GSet Int) (a : Int) (s : GSet Geid) (e r : Geid)
    (t : Nat) (v : BitVec 8) (mv : Option (BitVec 8)) :
    rvwmoCatConsistent GD → a ∈ X → greadsByte GD.gdG r a t v → gmoLt GD.gdG e r →
    WPh GD.gdG s r →
    (∀ w v', gwritesByte GD.gdG w a v' → WeakRvwmoGraph.gpo GD.gdG w r → gmoLt GD.gdG w r) →
    ownInv (GF := GF) X γ GD s ∗ Rbo γ GD a e mv ⊢
      Rbo γ GD a r (some v) ∗ ⌜∀ v0, mv = some v0 → v = v0⌝ := by
  intro hcons haX hrd her hwp hfw
  unfold Rbo
  iintro ⟨#Hinv, %H, Ha, %hp⟩
  obtain ⟨ht, ⟨hwr, hch⟩, hmv⟩ := hp
  ihave #Hcov := AxSpinProt5.covMoX γ X a GD s r haX hwp $$ Hinv
  icases (persistent_entails_left (AxSpinH.histInOfCov (GF := GF) γ GD a r H))
    $$ [$Ha $Hcov] with ⟨⟨Ha, -⟩, %hin⟩
  cases hlast : H.getLast? with
  | none =>
    have hnil : H = [] := List.getLast?_eq_none_iff.1 hlast
    subst hnil
    have himg : GD.gdG.gxImg a = some v := by
      cases t with
      | zero => exact (hcons.2.2.1 r a 0 v hrd).1
      | succ j =>
        obtain ⟨w, -, hw', hvis⟩ := (hcons.2.2.1 r a (j + 1) v hrd).1
        have hlt : gmoLt GD.gdG w r := hvis.elim id (hfw w v hw')
        have := hin w v hw' hlt
        simp at this
    isplitl [Ha]
    · iexists ([] : List Hent)
      isplitl [Ha]
      · iexact Ha
      · ipureintro
        refine ⟨Or.inl rfl, hwfaNil GD a, fun v' hv' => ?_⟩
        cases hv'
        exact Or.inl ⟨rfl, himg⟩
    · ipureintro
      intro v0 hv0
      rcases hmv v0 hv0 with ⟨-, hi⟩ | ⟨w, hw⟩
      · rw [himg] at hi
        exact Option.some.inj hi
      · simp at hw
  | some p =>
    obtain ⟨wl, vl⟩ := p
    have hne : H ≠ [] := by
      intro h
      subst h
      simp at hlast
    have ht' : tieBase GD.gdG (H.map Prod.fst) e := ht.resolve_left hne
    have hown : ∀ w v', gwritesByte GD.gdG w a v' → WeakRvwmoGraph.gpo GD.gdG w r →
        w ∈ H.map Prod.fst := fun w v' hw' hp => hin w v' hw' (hfw w v' hw' hp)
    ihave HT := (AxSpinProt.tokTieSingleton GD γ a H e ht').1 $$ Ha
    icases (persistent_entails_left (ownedReadRule (GF := GF) GD a r γ H {[e := (1 : Qp)]} wl vl
        hcons hwr hch hown hlast ⟨t, v, hrd⟩
        (Or.inl ⟨e, by rw [domSingleton, elemOfSingleton], her⟩)))
      $$ [$HT $Hcov] with ⟨⟨HT, -⟩, %hv⟩
    have hvl : v = vl := hv.2 t v hrd
    subst vl
    ihave Ha := (AxSpinProt.tokTieSingleton GD γ a H e ht').2 $$ HT
    isplitl [Ha]
    · iexists H
      isplitl [Ha]
      · iexact Ha
      · ipureintro
        refine ⟨Or.inr (tieLob _ _ e r ht' her), ⟨hwr, hch⟩, fun v' hv' => ?_⟩
        cases hv'
        exact Or.inr ⟨wl, hlast⟩
    · ipureintro
      intro v0 hv0
      rcases hmv v0 hv0 with ⟨h, -⟩ | ⟨w, hw⟩
      · exact absurd h hne
      · rw [hlast] at hw
        simp only [Option.some.injEq, Prod.mk.injEq] at hw
        exact hw.2

end rbo

/-! # 2. THE GENERIC HANDLE LEAVES -/

section hdlDefs
variable {GF : BundledGFunctors} [AxannotGS GF]

/-- THE HANDLE: `hdl O a e mv` -- the owned byte `a` arrives (in phase 2) at event `e`'s
annotation, with last value `mv` if known. -/
def hdl (O : Int → Geid → Option (BitVec 8) → IProp GF) (a : Int) (e : Geid)
    (mv : Option (BitVec 8)) : IProp GF :=
  AxAnnot.annotOwn e (O a e mv)

/-- The n-byte handle at one anchor: one annotation FRAGMENT per byte. -/
def hdlN (O : Int → Geid → Option (BitVec 8) → IProp GF) (a : Int) (e : Geid)
    (vs : List (BitVec 8)) : IProp GF :=
  iprop([∗list] j ↦ v ∈ vs, hdl O (a + (j : Int)) e (some v))

theorem hdlN1 (O : Int → Geid → Option (BitVec 8) → IProp GF) (a : Int) (e : Geid)
    (v : BitVec 8) : hdlN O a e [v] ⊣⊢ hdl O a e (some v) := by
  unfold hdlN
  refine BigSepL.bigSepL_singleton.trans (BiEntails.of_eq ?_)
  show hdl O (a + ((0 : Nat) : Int)) e (some v) = hdl O a e (some v)
  rw [show a + ((0 : Nat) : Int) = a by omega]

end hdlDefs

section leaves
variable {hlc : HasLC} {GF : BundledGFunctors.{0,0,0}} [InvGS_gen hlc GF] [AxannotGS GF]
  (GD : Gdexec) (N obSt0 : Type) (obi : N → Gdexec → obSt0 → GSet Geid → IProp GF) (nm : N)
  [pol : Axpol]

/-! ## 2.1 EVENT LEAVES (`wpEvStep`) -/

/-- OWNED LOAD: the handle at a lob-predecessor `e` moves to `r`; its value becomes the READ
value `v`; the agreement with the old value is DEPOSITED at `r`. -/
theorem evLdOwn (Hwf : @axpolWf pol) (O : Int → Geid → Option (BitVec 8) → IProp GF)
    (okr : Geid → Int → Prop)
    (HpolGmo : ∀ e r : Geid, e ∈ Axpol.lobp GD r → gmoLt GD.gdG e r)
    (HOr : ∀ (r e : Geid) (a : Int) (t : Nat) (v : BitVec 8) (mv : Option (BitVec 8)),
      gxLbl GD.gdG r = some (Lbl.LLoad false a [t] [v]) → okr r a → gmoLt GD.gdG e r →
      (∀ w v', gwritesByte GD.gdG w a v' → WeakRvwmoGraph.gpo GD.gdG w r → gmoLt GD.gdG w r) →
      ⊢ @flowEqDyn hlc GF _ (shG GD N obSt0 obi nm) GD r (Axpol.sPol GD r)
          ({[e := O a e mv]} : Mea GF) iprop(O a r (some v) ∗ ⌜∀ v0, mv = some v0 → v = v0⌝))
    (i : Agent) (k : Nat) (a : Int) (t : Nat) (v : BitVec 8) (e : Geid)
    (mv : Option (BitVec 8)) (Ψ : IProp GF) :
    gxLbl GD.gdG (i, k) = some (Lbl.LLoad false a [t] [v]) → okr (i, k) a →
    e ∈ Axpol.lobp GD (i, k) →
    (∀ w v', gwritesByte GD.gdG w a v' → WeakRvwmoGraph.gpo GD.gdG w (i, k) →
      gmoLt GD.gdG w (i, k)) →
    ⊢ hdl O a e mv -∗
      (hdl O a (i, k) (some v) -∗
        AxAnnot.annotOwn (i, k) iprop(⌜∀ v0, mv = some v0 → v = v0⌝) -∗ Ψ) -∗
      @wpEvStep hlc GF _ (shG GD N obSt0 obi nm) pol Unit GD i k (fun _ => True)
        (fun _ => graphValue GD (i, k) = some [v]) (fun _ => k + 1) (fun _ => Ψ) := by
  intro Hl Hok Hin Hfw
  have Hgv : graphValue GD (i, k) = some [v] := by unfold graphValue; rw [Hl]; rfl
  unfold hdl
  iintro Hh HΨ
  ihave Hfe := HOr (i, k) e a t v mv Hl Hok (HpolGmo e (i, k) Hin) Hfw
  iapply (evDraw (hlc := hlc) GD N obSt0 obi nm Hwf i k e (O a e mv) (O a (i, k) (some v))
    iprop(⌜∀ v0, mv = some v0 → v = v0⌝) _ _ Hgv Hin) $$ Hh Hfe HΨ

/-- OWNED STORE: the handle moves to the store `w`; the history is appended in `w`'s flow
equation (phase 2); new last value = `b`. -/
theorem evSdOwn (Hwf : @axpolWf pol) (O : Int → Geid → Option (BitVec 8) → IProp GF)
    (okw : Geid → Int → BitVec 8 → Prop)
    (HpolGmo : ∀ e r : Geid, e ∈ Axpol.lobp GD r → gmoLt GD.gdG e r)
    (HOw : ∀ (w e : Geid) (a : Int) (b : BitVec 8) (cls : WmClass) (mv : Option (BitVec 8)),
      gxLbl GD.gdG w = some (Lbl.LStore false a [b] cls) → okw w a b → gmoLt GD.gdG e w →
      ⊢ @flowEqDyn hlc GF _ (shG GD N obSt0 obi nm) GD w (Axpol.sPol GD w)
          ({[e := O a e mv]} : Mea GF) (O a w (some b)))
    (i : Agent) (k : Nat) (a : Int) (b : BitVec 8) (cls : WmClass) (e : Geid)
    (mv : Option (BitVec 8)) (Ψ : IProp GF) :
    gxLbl GD.gdG (i, k) = some (Lbl.LStore false a [b] cls) → okw (i, k) a b →
    e ∈ Axpol.lobp GD (i, k) →
    ⊢ hdl O a e mv -∗ (hdl O a (i, k) (some b) -∗ Ψ) -∗
      @wpEvStep hlc GF _ (shG GD N obSt0 obi nm) pol Unit GD i k (fun _ => True)
        (fun _ => graphData GD (i, k) = some (WeakInterpProj.wbytes 1 b)) (fun _ => k + 1)
        (fun _ => Ψ) := by
  intro Hl Hok Hin
  have Hval : graphData GD (i, k) = some (WeakInterpProj.wbytes 1 b) := by
    unfold graphData; rw [Hl]; simp [lblData, l3pWbytes1]
  unfold hdl
  iintro Hh HΨ
  ihave Hfe := HOw (i, k) e a b cls mv Hl Hok (HpolGmo e (i, k) Hin)
  ihave Hfe := (@flowEqDynMono hlc GF _ (shG GD N obSt0 obi nm) pol GD (i, k) _ _
    (O a (i, k) (some b)) iprop(O a (i, k) (some b) ∗ True)) $$ [] Hfe
  · inext
    iintro H
    isplitl [H]
    · iexact H
    · itrivial
  iapply (evDraw (hlc := hlc) GD N obSt0 obi nm Hwf i k e (O a e mv) (O a (i, k) (some b))
    iprop(True) _ _ Hval Hin) $$ Hh Hfe
  iintro H _
  iapply HΨ $$ H

/-- Every po-earlier same-address write of `r` is gmo-before `r` once `r` is gmo-after the
po-latest one `w` (no same-address write po-between): the others are po-before `w`, hence ppo
rule 1. -/
theorem poWritesGmoBefore (Hcons : rvwmoCatConsistent GD) (i : Agent) (kw k : Nat) (a : Int)
    (b : BitVec 8) (cls : WmClass) :
    gxLbl GD.gdG (i, kw) = some (Lbl.LStore false a [b] cls) →
    (∀ w v', gwritesByte GD.gdG w a v' → WeakRvwmoGraph.gpo GD.gdG (i, kw) w →
      WeakRvwmoGraph.gpo GD.gdG w (i, k) → False) →
    gmoLt GD.gdG (i, kw) (i, k) →
    ∀ w v', gwritesByte GD.gdG w a v' → WeakRvwmoGraph.gpo GD.gdG w (i, k) →
      gmoLt GD.gdG w (i, k) := by
  intro Hlw Hnoint Hlt w v' Hw Hpo
  by_cases Hne : w = (i, kw)
  · subst Hne
    exact Hlt
  obtain ⟨wi, wk⟩ := w
  obtain ⟨Hh, Hk, Hs1, Hs2⟩ := Hpo
  have Hh' : wi = i := Hh
  subst wi
  by_cases Hlk : wk < kw
  · refine gmoLtTrans _ _ _ _ (gobGmo GD Hcons _ _ ?_) Hlt
    exact ppo1Gob GD (i, wk) (i, kw) a b ⟨rfl, Hlk, Hs1, by rw [Hlw]; rfl⟩ (.inl ⟨v', Hw⟩)
      (gwbStore _ _ _ _ _ Hlw).1
  · exfalso
    have Hne' : wk ≠ kw := fun h => Hne (by rw [h])
    exact Hnoint (i, wk) v' Hw ⟨rfl, by simp only; omega, by rw [Hlw]; rfl, Hs1⟩
      ⟨rfl, Hk, Hs1, Hs2⟩

/-- THE FORWARDED-RELOAD LEAF: a load `r` of `a` after the same hart's store `w` of `b` to `a`
(no same-address store po-between).  Case split on `gmoLt w r`: ordered ⇒ `w ∈ lobp r`, the
handle moves `w → r` through the owned-read flow equation; forwarded ⇒ `ownedReadRuleFwd` (pure,
`v = b`), NOTHING drawn, the handle stays at `w`. -/
theorem evReloadOwn (Hwf : @axpolWf pol) (Hcons : rvwmoCatConsistent GD)
    (O : Int → Geid → Option (BitVec 8) → IProp GF) (okr : Geid → Int → Prop)
    (_HpolGmo : ∀ e r : Geid, e ∈ Axpol.lobp GD r → gmoLt GD.gdG e r)
    (HpolIntro : ∀ (e r : Geid) (l : Lbl), gxLbl GD.gdG e = some l → lbIsMem l = true →
      WeakRvwmoGraph.gpo GD.gdG e r → gmoLt GD.gdG e r → e ∈ Axpol.lobp GD r)
    (HOr : ∀ (r e : Geid) (a : Int) (t : Nat) (v : BitVec 8) (mv : Option (BitVec 8)),
      gxLbl GD.gdG r = some (Lbl.LLoad false a [t] [v]) → okr r a → gmoLt GD.gdG e r →
      (∀ w v', gwritesByte GD.gdG w a v' → WeakRvwmoGraph.gpo GD.gdG w r → gmoLt GD.gdG w r) →
      ⊢ @flowEqDyn hlc GF _ (shG GD N obSt0 obi nm) GD r (Axpol.sPol GD r)
          ({[e := O a e mv]} : Mea GF) iprop(O a r (some v) ∗ ⌜∀ v0, mv = some v0 → v = v0⌝))
    (HOp : ∀ (r : Geid) (a : Int) (t : Nat) (v : BitVec 8),
      gxLbl GD.gdG r = some (Lbl.LLoad false a [t] [v]) → okr r a →
      ⊢ @flowEqDyn hlc GF _ (shG GD N obSt0 obi nm) GD r (Axpol.sPol GD r) (∅ : Mea GF)
          iprop(True))
    (i : Agent) (kw k : Nat) (a : Int) (b : BitVec 8) (cls : WmClass) (t : Nat) (v : BitVec 8)
    (Ψ : IProp GF) :
    gxLbl GD.gdG (i, kw) = some (Lbl.LStore false a [b] cls) →
    gxLbl GD.gdG (i, k) = some (Lbl.LLoad false a [t] [v]) → kw < k →
    okr (i, k) a →
    (∀ w v', gwritesByte GD.gdG w a v' → WeakRvwmoGraph.gpo GD.gdG (i, kw) w →
      WeakRvwmoGraph.gpo GD.gdG w (i, k) → False) →
    ⊢ hdl O a (i, kw) (some b) -∗
      ((∃ (e' : Geid), ⌜e' = (i, kw) ∨ e' = (i, k)⌝ ∗ hdl O a e' (some b)) -∗
        AxAnnot.annotOwn (i, k) iprop(⌜v = b⌝) -∗ Ψ) -∗
      @wpEvStep hlc GF _ (shG GD N obSt0 obi nm) pol Unit GD i k (fun _ => True)
        (fun _ => graphValue GD (i, k) = some [v]) (fun _ => k + 1) (fun _ => Ψ) := by
  intro Hlw Hlr Hlt Hok Hnoint
  have Hgv : graphValue GD (i, k) = some [v] := by unfold graphValue; rw [Hlr]; rfl
  have Hpo : WeakRvwmoGraph.gpo GD.gdG (i, kw) (i, k) :=
    ⟨rfl, Hlt, by rw [Hlw]; rfl, by rw [Hlr]; rfl⟩
  unfold hdl
  iintro Hh HΨ
  by_cases Hb : gmoLt GD.gdG (i, kw) (i, k)
  · have Hin : ((i, kw) : Geid) ∈ Axpol.lobp GD (i, k) := HpolIntro (i, kw) (i, k) _ Hlw rfl Hpo Hb
    have Hfw := poWritesGmoBefore GD Hcons i kw k a b cls Hlw Hnoint Hb
    ihave Hfe := HOr (i, k) (i, kw) a t v (some b) Hlr Hok Hb Hfw
    ihave Hfe := (@flowEqDynMono hlc GF _ (shG GD N obSt0 obi nm) pol GD (i, k) _ _
      iprop(O a (i, k) (some v) ∗ ⌜∀ v0, some b = some v0 → v = v0⌝)
      iprop(O a (i, k) (some b) ∗ ⌜v = b⌝)) $$ [] Hfe
    · inext
      iintro ⟨H, %Hf⟩
      have Hvb : v = b := Hf b rfl
      subst Hvb
      isplitl [H]
      · iexact H
      · ipureintro
        rfl
    iapply (evDraw (hlc := hlc) GD N obSt0 obi nm Hwf i k (i, kw) (O a (i, kw) (some b))
      (O a (i, k) (some b)) iprop(⌜v = b⌝) _ _ Hgv Hin) $$ Hh Hfe
    iintro H1 H2
    iapply HΨ $$ [H1] H2
    iexists (i, k)
    isplitr
    · ipureintro
      exact Or.inr rfl
    · iexact H1
  · have Hwb := (gwbStore _ _ _ _ _ Hlw).1
    obtain ⟨-, Hval⟩ := ownedReadRuleFwd GD a (i, k) (i, kw) b t v Hcons Hpo Hwb
      (grbLoad _ _ _ _ _ Hlr) Hb Hnoint
    have Hvb := Hval t v (grbLoad _ _ _ _ _ Hlr)
    ihave Hfe := HOp (i, k) a t v Hlr Hok
    ihave Hfe := (@flowEqDynMono hlc GF _ (shG GD N obSt0 obi nm) pol GD (i, k) _ (∅ : Mea GF)
      iprop(True) iprop(⌜v = b⌝ ∗ True)) $$ [] Hfe
    · inext
      iintro _
      isplitr
      · ipureintro
        exact Hvb
      · itrivial
    iapply (evPlain (hlc := hlc) GD N obSt0 obi nm i k iprop(⌜v = b⌝) iprop(True) _ _ Hgv)
      $$ Hfe
    iintro H _
    iapply HΨ $$ [Hh] H
    iexists (i, kw)
    isplitr
    · ipureintro
      exact Or.inl rfl
    · iexact Hh

/-! ## 2.2 INSTRUCTION LEAVES on hand nodes (`tierAWpd`): the value-dependent load
`.memRead 1 …` with continuation `KK`, the store `.memWrite 1 … b` then `m'`. -/

theorem wpdLdOwn (Hwf : @axpolWf pol) (cpu : CPU) (O : Int → Geid → Option (BitVec 8) → IProp GF)
    (okr : Geid → Int → Prop)
    (HpolGmo : ∀ e r : Geid, e ∈ Axpol.lobp GD r → gmoLt GD.gdG e r)
    (HOr : ∀ (r e : Geid) (a : Int) (t : Nat) (v : BitVec 8) (mv : Option (BitVec 8)),
      gxLbl GD.gdG r = some (Lbl.LLoad false a [t] [v]) → okr r a → gmoLt GD.gdG e r →
      (∀ w v', gwritesByte GD.gdG w a v' → WeakRvwmoGraph.gpo GD.gdG w r → gmoLt GD.gdG w r) →
      ⊢ @flowEqDyn hlc GF _ (shG GD N obSt0 obi nm) GD r (Axpol.sPol GD r)
          ({[e := O a e mv]} : Mea GF) iprop(O a r (some v) ∗ ⌜∀ v0, mv = some v0 → v = v0⌝))
    (i : Agent) (k : Nat) (pa : PAddr) (Hdev : devAddr pa = false)
    (KK : Result (BitVec (8 * 1) × Option Bool) Arch.abort → SailM Unit) (t : Nat)
    (v : BitVec 8) (e : Geid) (mv : Option (BitVec 8)) (Φ : Athread → IProp GF) :
    k ≠ (AxOpsem.grow GD i).length →
    (AxOpsem.grow GD i)[k]? = some (Lbl.LLoad false (paZ pa) [t] [v]) →
    okr (i, k) (paZ pa) → e ∈ Axpol.lobp GD (i, k) →
    (∀ w v', gwritesByte GD.gdG w (paZ pa) v' → WeakRvwmoGraph.gpo GD.gdG w (i, k) →
      gmoLt GD.gdG w (i, k)) →
    ⊢ hdl O (paZ pa) e mv -∗
      (hdl O (paZ pa) (i, k) (some v) -∗
        AxAnnot.annotOwn (i, k) iprop(⌜∀ v0, mv = some v0 → v = v0⌝) -∗
        ∀ rs : RegFile, tierAWpd (hlc := hlc) GD N obSt0 obi nm
          ⟨hp cpu (KK (.Ok (v, none))) rs, k + 1⟩ .MaybeStuck i Φ) -∗
      ∀ rs : RegFile, tierAWpd (hlc := hlc) GD N obSt0 obi nm
        ⟨hp cpu (.impure (.ok (.memRead 1 64 (l3pRreq l3pAkP pa))) KK) rs, k⟩ .MaybeStuck i Φ := by
  intro Hne Hrow Hok Hin Hfw
  have Hl : gxLbl GD.gdG (i, k) = some (Lbl.LLoad false (paZ pa) [t] [v]) := by
    rw [gxLblGrow]; exact Hrow
  have Hadv : ∀ lb, (AxOpsem.grow GD i)[k]? = some lb → aidentAdvRd (aident lb) = 1 := by
    rw [Hrow]
    intro lb h
    cases h
    rfl
  have H := shRead (hlc := hlc) GD N obSt0 obi nm cpu i Φ pa Hdev KK k Hne Hadv
    iprop(hdl O (paZ pa) e mv ∗ (hdl O (paZ pa) (i, k) (some v) -∗
      AxAnnot.annotOwn (i, k) iprop(⌜∀ v0, mv = some v0 → v = v0⌝) -∗
      ∀ rs : RegFile, tierAWpd (hlc := hlc) GD N obSt0 obi nm
        ⟨hp cpu (KK (.Ok (v, none))) rs, k + 1⟩ .MaybeStuck i Φ))
    (fun vs b' rs Hgv Hvs => by
      subst Hvs
      have Hgv' : (some [v] : Option (List (BitVec 8))) = some [b'] := by
        rw [← Hgv]; unfold graphValue; rw [Hl]; rfl
      have Hb : b' = v := by
        have h := Option.some.inj Hgv'
        simp only [List.cons.injEq, and_true] at h
        exact h.symm
      subst b'
      iintro ⟨Hh, HΨ⟩
      iapply (evLdOwn (hlc := hlc) GD N obSt0 obi nm Hwf O okr HpolGmo HOr i k (paZ pa) t v e mv _
        Hl Hok Hin Hfw) $$ Hh
      iintro H1 H2
      iapply HΨ $$ H1 H2 %rs)
  iintro Hh HΨ
  iapply H $$ [$Hh $HΨ]

theorem wpdSdOwn (Hwf : @axpolWf pol) (cpu : CPU) (O : Int → Geid → Option (BitVec 8) → IProp GF)
    (okw : Geid → Int → BitVec 8 → Prop)
    (HpolGmo : ∀ e r : Geid, e ∈ Axpol.lobp GD r → gmoLt GD.gdG e r)
    (HOw : ∀ (w e : Geid) (a : Int) (b : BitVec 8) (cls : WmClass) (mv : Option (BitVec 8)),
      gxLbl GD.gdG w = some (Lbl.LStore false a [b] cls) → okw w a b → gmoLt GD.gdG e w →
      ⊢ @flowEqDyn hlc GF _ (shG GD N obSt0 obi nm) GD w (Axpol.sPol GD w)
          ({[e := O a e mv]} : Mea GF) (O a w (some b)))
    (i : Agent) (k : Nat) (pa : PAddr) (Hdev : devAddr pa = false) (b : BitVec 8)
    (m' : SailM Unit) (cls : WmClass) (e : Geid) (mv : Option (BitVec 8))
    (Φ : Athread → IProp GF) :
    k ≠ (AxOpsem.grow GD i).length →
    (AxOpsem.grow GD i)[k]? = some (Lbl.LStore false (paZ pa) [b] cls) →
    okw (i, k) (paZ pa) b → e ∈ Axpol.lobp GD (i, k) →
    ⊢ hdl O (paZ pa) e mv -∗
      (hdl O (paZ pa) (i, k) (some b) -∗
        ∀ rs : RegFile, tierAWpd (hlc := hlc) GD N obSt0 obi nm ⟨hp cpu m' rs, k + 1⟩
          .MaybeStuck i Φ) -∗
      ∀ rs : RegFile, tierAWpd (hlc := hlc) GD N obSt0 obi nm
        ⟨hp cpu (.impure (.ok (.memWrite 1 64 (l3pWreq l3pAkP pa b))) (fun _ => m')) rs, k⟩
        .MaybeStuck i Φ := by
  intro Hne Hrow Hok Hin
  have Hl : gxLbl GD.gdG (i, k) = some (Lbl.LStore false (paZ pa) [b] cls) := by
    rw [gxLblGrow]; exact Hrow
  have H := shPos (hlc := hlc) GD N obSt0 obi nm cpu i Φ
    iprop(hdl O (paZ pa) e mv ∗ (hdl O (paZ pa) (i, k) (some b) -∗
      ∀ rs : RegFile, tierAWpd (hlc := hlc) GD N obSt0 obi nm ⟨hp cpu m' rs, k + 1⟩
        .MaybeStuck i Φ))
    k (.impure (.ok (.memWrite 1 64 (l3pWreq l3pAkP pa b))) (fun _ => m')) Hne
    (fun rs id K => noReadAtWrite cpu _ pa Hdev b m' rs k id K)
    (fun rs l s' Hst => by
      obtain ⟨rfl, Hs', -⟩ := writeInv2 cpu _ pa Hdev b m' rs k l s' Hst
      simp only [wlWdata]
      subst Hs'
      iintro ⟨Hh, HΨ⟩
      iapply (evSdOwn (hlc := hlc) GD N obSt0 obi nm Hwf O okw HpolGmo HOw i k (paZ pa) b cls e mv
        _ Hl Hok Hin) $$ Hh
      iintro H
      iapply HΨ $$ H %rs)
  iintro Hh HΨ
  iapply H $$ [$Hh $HΨ]

theorem wpdReloadOwn (Hwf : @axpolWf pol) (cpu : CPU) (Hcons : rvwmoCatConsistent GD)
    (O : Int → Geid → Option (BitVec 8) → IProp GF) (okr : Geid → Int → Prop)
    (HpolGmo : ∀ e r : Geid, e ∈ Axpol.lobp GD r → gmoLt GD.gdG e r)
    (HpolIntro : ∀ (e r : Geid) (l : Lbl), gxLbl GD.gdG e = some l → lbIsMem l = true →
      WeakRvwmoGraph.gpo GD.gdG e r → gmoLt GD.gdG e r → e ∈ Axpol.lobp GD r)
    (HOr : ∀ (r e : Geid) (a : Int) (t : Nat) (v : BitVec 8) (mv : Option (BitVec 8)),
      gxLbl GD.gdG r = some (Lbl.LLoad false a [t] [v]) → okr r a → gmoLt GD.gdG e r →
      (∀ w v', gwritesByte GD.gdG w a v' → WeakRvwmoGraph.gpo GD.gdG w r → gmoLt GD.gdG w r) →
      ⊢ @flowEqDyn hlc GF _ (shG GD N obSt0 obi nm) GD r (Axpol.sPol GD r)
          ({[e := O a e mv]} : Mea GF) iprop(O a r (some v) ∗ ⌜∀ v0, mv = some v0 → v = v0⌝))
    (HOp : ∀ (r : Geid) (a : Int) (t : Nat) (v : BitVec 8),
      gxLbl GD.gdG r = some (Lbl.LLoad false a [t] [v]) → okr r a →
      ⊢ @flowEqDyn hlc GF _ (shG GD N obSt0 obi nm) GD r (Axpol.sPol GD r) (∅ : Mea GF)
          iprop(True))
    (i : Agent) (kw k : Nat) (pa : PAddr) (Hdev : devAddr pa = false)
    (KK : Result (BitVec (8 * 1) × Option Bool) Arch.abort → SailM Unit) (b : BitVec 8)
    (cls : WmClass) (t : Nat) (v : BitVec 8) (Φ : Athread → IProp GF) :
    k ≠ (AxOpsem.grow GD i).length →
    (AxOpsem.grow GD i)[kw]? = some (Lbl.LStore false (paZ pa) [b] cls) →
    (AxOpsem.grow GD i)[k]? = some (Lbl.LLoad false (paZ pa) [t] [v]) → kw < k →
    okr (i, k) (paZ pa) →
    (∀ w v', gwritesByte GD.gdG w (paZ pa) v' → WeakRvwmoGraph.gpo GD.gdG (i, kw) w →
      WeakRvwmoGraph.gpo GD.gdG w (i, k) → False) →
    ⊢ hdl O (paZ pa) (i, kw) (some b) -∗
      ((∃ (e' : Geid), ⌜e' = (i, kw) ∨ e' = (i, k)⌝ ∗ hdl O (paZ pa) e' (some b)) -∗
        AxAnnot.annotOwn (i, k) iprop(⌜v = b⌝) -∗
        ∀ rs : RegFile, tierAWpd (hlc := hlc) GD N obSt0 obi nm
          ⟨hp cpu (KK (.Ok (v, none))) rs, k + 1⟩ .MaybeStuck i Φ) -∗
      ∀ rs : RegFile, tierAWpd (hlc := hlc) GD N obSt0 obi nm
        ⟨hp cpu (.impure (.ok (.memRead 1 64 (l3pRreq l3pAkP pa))) KK) rs, k⟩ .MaybeStuck i Φ := by
  intro Hne Hroww Hrow Hlt Hok Hnoint
  have Hlw : gxLbl GD.gdG (i, kw) = some (Lbl.LStore false (paZ pa) [b] cls) := by
    rw [gxLblGrow]; exact Hroww
  have Hl : gxLbl GD.gdG (i, k) = some (Lbl.LLoad false (paZ pa) [t] [v]) := by
    rw [gxLblGrow]; exact Hrow
  have Hadv : ∀ lb, (AxOpsem.grow GD i)[k]? = some lb → aidentAdvRd (aident lb) = 1 := by
    rw [Hrow]
    intro lb h
    cases h
    rfl
  have H := shRead (hlc := hlc) GD N obSt0 obi nm cpu i Φ pa Hdev KK k Hne Hadv
    iprop(hdl O (paZ pa) (i, kw) (some b) ∗
      ((∃ (e' : Geid), ⌜e' = (i, kw) ∨ e' = (i, k)⌝ ∗ hdl O (paZ pa) e' (some b)) -∗
        AxAnnot.annotOwn (i, k) iprop(⌜v = b⌝) -∗
        ∀ rs : RegFile, tierAWpd (hlc := hlc) GD N obSt0 obi nm
          ⟨hp cpu (KK (.Ok (v, none))) rs, k + 1⟩ .MaybeStuck i Φ))
    (fun vs b' rs Hgv Hvs => by
      subst Hvs
      have Hgv' : (some [v] : Option (List (BitVec 8))) = some [b'] := by
        rw [← Hgv]; unfold graphValue; rw [Hl]; rfl
      have Hb : b' = v := by
        have h := Option.some.inj Hgv'
        simp only [List.cons.injEq, and_true] at h
        exact h.symm
      subst b'
      iintro ⟨Hh, HΨ⟩
      iapply (evReloadOwn (hlc := hlc) GD N obSt0 obi nm Hwf Hcons O okr HpolGmo HpolIntro HOr HOp
        i kw k (paZ pa) b cls t v _ Hlw Hl Hlt Hok Hnoint) $$ Hh
      iintro H1 H2
      iapply HΨ $$ H1 H2 %rs)
  iintro Hh HΨ
  iapply H $$ [$Hh $HΨ]

end leaves

/-! # 3. THE INTERFACE AT `spinOb5` / `splPol`: `O := Rbo`, the three flow equations, the two
policy facts. -/

def okw5 (x : Int) (Cl : List Int) (cv : Agent → List (BitVec 8)) (GT : GdexecT) (w : Geid)
    (a : Int) (_b : BitVec 8) : Prop :=
  a ∈ X5 x Cl ∧ cpuOk Cl cv (gtAdGd GT).gdG w

def okr5 (x : Int) (Cl : List Int) (_r : Geid) (a : Int) : Prop := a ∈ X5 x Cl

theorem splPolGmo (GT : GdexecT) (e r : Geid) :
    e ∈ @Axpol.lobp (splPol GT) (gtAdGd GT) r → gmoLt (gtAdGd GT).gdG e r :=
  fun He => ((elemOfSplLobp _ _ _).1 He).2.2.2

theorem splPolIntro (GT : GdexecT) (e r : Geid) (l : Lbl) :
    gxLbl (gtAdGd GT).gdG e = some l → lbIsMem l = true →
    WeakRvwmoGraph.gpo (gtAdGd GT).gdG e r → gmoLt (gtAdGd GT).gdG e r →
    e ∈ @Axpol.lobp (splPol GT) (gtAdGd GT) r :=
  fun H1 H2 H3 H4 => lobpIntro (gtAdGd GT) e r l H1 H2 H3 H4

theorem rdNX (lk x : Int) (Cl : List Int) (cv : Agent → List (BitVec 8)) (GT : GdexecT)
    (r : Geid) (a : Int) (t : Nat) (v : BitVec 8) :
    gxLbl (gtAdGd GT).gdG r = some (Lbl.LLoad false a [t] [v]) →
    (∀ a' v', a' ∈ X5 x Cl → ¬ gwritesByte (gtAdGd GT).gdG r a' v') ∧
      cpuOk Cl cv (gtAdGd GT).gdG r ∧ (∀ v', ¬ gwritesByte (gtAdGd GT).gdG r lk v') := by
  intro Hl
  have Hnw : gisW (gtAdGd GT).gdG r = false := by unfold gisW; rw [Hl]; rfl
  exact ⟨fun a' v' _ => AxSpinProt6.nwb _ r Hnw a' v', nwCpu Cl cv GT r Hnw,
    fun v' => AxSpinProt6.nwb _ r Hnw lk v'⟩

theorem rdNotLkread (lk x : Int) (Cl : List Int) (GT : GdexecT) (HlkX : lk ∉ X5 x Cl)
    (r : Geid) (a : Int) (t : Nat) (v : BitVec 8) :
    gxLbl (gtAdGd GT).gdG r = some (Lbl.LLoad false a [t] [v]) → a ∈ X5 x Cl →
    ¬ lkread lk (gtAdGd GT).gdG r := by
  rintro Hl HaX ⟨⟨t', v', Hrd⟩, -⟩
  have h := (grbLoadOnly _ _ _ _ _ Hl lk t' v' Hrd).1
  rw [h] at HlkX
  exact HlkX HaX

section inst5h
variable {hlc : HasLC} {GF : BundledGFunctors.{0,0,0}} [InvGS_gen hlc GF] [AxannotGS GF]
  [AxlogG GF Hent] [SpinlockG GF]

theorem fe5hWrite (lk x : Int) (Cl : List Int) (cv : Agent → List (BitVec 8)) (GT : GdexecT)
    (nm : spinN) (_Hcons : rvwmoCatConsistent (gtAdGd GT)) (HlkX : lk ∉ X5 x Cl) (w e : Geid)
    (a : Int) (b : BitVec 8) (cls : WmClass) (mv : Option (BitVec 8)) :
    gxLbl (gtAdGd GT).gdG w = some (Lbl.LStore false a [b] cls) → okw5 x Cl cv GT w a b →
    gmoLt (gtAdGd GT).gdG e w →
    ⊢ @flowEqDyn hlc GF _ (s5G lk x Cl cv GT nm) (gtAdGd GT) w
        (@Axpol.sPol (splPol GT) (gtAdGd GT) w)
        ({[e := Rbo nm.1 (gtAdGd GT) a e mv]} : Mea GF) (Rbo nm.1 (gtAdGd GT) a w (some b)) := by
  rintro Hl ⟨HaX, Hok⟩ Hew
  obtain ⟨Hw, Hsg⟩ := gwbStore _ _ _ _ _ Hl
  iapply fe5Build
  iintro %s %Hn %_ %_ %_ %_ Ho Hlk Hin
  ihave Hin := (BigSepM.bigSepM_singleton (M := GMapF Geid)).1 $$ Hin
  imod (RboWrite nm.1 (gtAdGd GT) (X5 x Cl) a s e w b mv Hn HaX Hew Hw
    (fun a' v' H => (Hsg a' v' H).1)) $$ [$Ho $Hin] with ⟨Ho, HR⟩
  imodintro
  inext
  imodintro
  isplitr
  · ipureintro
    exact Hok
  isplitl [Ho]
  · iexact Ho
  isplitl [Hlk]
  · iapply (lkInvOther nm.2 lk (gtAdGd GT) s w Hn
      (fun v Hv => HlkX (by rw [(Hsg lk v Hv).1]; exact HaX))
      (fun ⟨_, Hnw⟩ => by simp [gisW, Hl, lbIsW] at Hnw)) $$ Hlk
  · iexact HR

theorem fe5hRead (lk x : Int) (Cl : List Int) (cv : Agent → List (BitVec 8)) (GT : GdexecT)
    (nm : spinN) (Hcons : rvwmoCatConsistent (gtAdGd GT)) (HlkX : lk ∉ X5 x Cl) (r e : Geid)
    (a : Int) (t : Nat) (v : BitVec 8) (mv : Option (BitVec 8)) :
    gxLbl (gtAdGd GT).gdG r = some (Lbl.LLoad false a [t] [v]) → okr5 x Cl r a →
    gmoLt (gtAdGd GT).gdG e r →
    (∀ w v', gwritesByte (gtAdGd GT).gdG w a v' → WeakRvwmoGraph.gpo (gtAdGd GT).gdG w r →
      gmoLt (gtAdGd GT).gdG w r) →
    ⊢ @flowEqDyn hlc GF _ (s5G lk x Cl cv GT nm) (gtAdGd GT) r
        (@Axpol.sPol (splPol GT) (gtAdGd GT) r)
        ({[e := Rbo nm.1 (gtAdGd GT) a e mv]} : Mea GF)
        iprop(Rbo nm.1 (gtAdGd GT) a r (some v) ∗ ⌜∀ v0, mv = some v0 → v = v0⌝) := by
  intro Hl HaX Her Hfw
  have Hrd := grbLoad _ _ _ _ _ Hl
  obtain ⟨HnX, Hok, Hnlk⟩ := rdNX lk x Cl cv GT r a t v Hl
  iapply fe5Build
  iintro %s %Hn %_ %Hwp %_ %_ #Ho Hlk Hin
  ihave Hin := (BigSepM.bigSepM_singleton (M := GMapF Geid)).1 $$ Hin
  ihave ⟨HR, %Hf⟩ := (RboRead nm.1 (gtAdGd GT) (X5 x Cl) a s e r t v mv Hcons HaX Hrd Her Hwp
    Hfw) $$ [$Ho $Hin]
  imodintro
  inext
  imodintro
  isplitr
  · ipureintro
    exact Hok
  isplitl []
  · iapply (ownInvOther (X5 x Cl) nm.1 (gtAdGd GT) s r Hn HnX) $$ Ho
  isplitl [Hlk]
  · iapply (lkInvOther nm.2 lk (gtAdGd GT) s r Hn Hnlk
      (rdNotLkread lk x Cl GT HlkX r a t v Hl HaX)) $$ Hlk
  · isplitl [HR]
    · iexact HR
    · ipureintro
      exact Hf

theorem fe5hPlain (lk x : Int) (Cl : List Int) (cv : Agent → List (BitVec 8)) (GT : GdexecT)
    (nm : spinN) (_Hcons : rvwmoCatConsistent (gtAdGd GT)) (HlkX : lk ∉ X5 x Cl) (r : Geid)
    (a : Int) (t : Nat) (v : BitVec 8) :
    gxLbl (gtAdGd GT).gdG r = some (Lbl.LLoad false a [t] [v]) → okr5 x Cl r a →
    ⊢ @flowEqDyn hlc GF _ (s5G lk x Cl cv GT nm) (gtAdGd GT) r
        (@Axpol.sPol (splPol GT) (gtAdGd GT) r) (∅ : Mea GF) iprop(True) := by
  intro Hl HaX
  obtain ⟨HnX, Hok, Hnlk⟩ := rdNX lk x Cl cv GT r a t v Hl
  iapply fe5Build
  iintro %s %Hn %_ %_ %_ %_ #Ho Hlk _
  imodintro
  inext
  imodintro
  isplitr
  · ipureintro
    exact Hok
  isplitl []
  · iapply (ownInvOther (X5 x Cl) nm.1 (gtAdGd GT) s r Hn HnX) $$ Ho
  isplitl [Hlk]
  · iapply (lkInvOther nm.2 lk (gtAdGd GT) s r Hn Hnlk
      (rdNotLkread lk x Cl GT HlkX r a t v Hl HaX)) $$ Hlk
  · itrivial

end inst5h

end Weak
