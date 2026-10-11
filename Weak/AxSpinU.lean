/-
Weak: **UNIFY, part 1 of the spinlock plan -- THE HANDLE SURFACE AT THE JOINT INSTANCE** `Ixv6`
= `AxSpinX2.xG Lx GT nm` (= `shG (gtAdGd GT) Xv6N Unit (protXv6 Lx) nm`) / `xv6Pol GT`, the
instance of `AxSpinX*` at the certificates' layout `Lx`.  Phase 2b's handle leaves
(`AxSpinH4`–`H7`) live at the SEPARATE instance `spinOb6`; WPds do not transport across instances,
so this file re-derives the surface at `Ixv6`, REUSING `AxSpinX2`'s flow equations (`fxBuild`,
`fxClaim`/`fxClaim'`, `fxNeutral`, `fxReleasePid`, `fxLkreadHeld`, `fxRVLWrite`, `fxCpuWrite`,
`fxOwnedRead`, `fxFwdRead`, `fxCpuRacy`, `fxRead`) and adding derived rules (§2).  (Rocq files:
this one; `AxSpinU2` the allocpid-shaped CS program; `AxSpinU3` the pure dichotomy; `AxSpinU4`
capstones.)

Rocq: `iris/AxSpinU.v` @ xxvzwolszwmp.

## The Rocq header, in substance

§1 PURE/GHOST: `RvRetie`/`RVLRetie` (an owned byte's tie moves along gmo, not only gob);
   `RvReadSrc` (the owned read's SOURCE: the image, or a write that is the anchor or gmo-before
   it -- `ownedReadRule`'s `grfAt` made explicit); `srcAt`/`npSrc`.
§2 NEW RULES at `protXv6 L` (any layout, derived from `fxBuild`):
   `fxuNpRead` the CS's `lw nextpid`: `RNp` drawn at an anchor gmo-before the read; deposits the
     VALUE handle `NPh r w8` (`RNpv` at value `v` with `BitVec.ofInt 32 v = w8`, `w8` the pinned
     read word) and the SOURCE fact `npSrc r e` (no nextpid write lands gmo-between the anchor and
     the read);
   `fxuNpIncr` the CS's `sw nextpid ← w8+1` from a VALUE handle: history appended, ●mono
     v → v+1, the EXCLUSIVE ◯{v} MINTED and deposited (`FRAG`);
   `fxuWrite1`/`fxuRead1` the one-byte owned write/read for §3.
§3 THE GENERIC OWNED-CLASS INTERFACE of `AxSpinH` §2 DISCHARGED AT Ixv6: `O1 nm GD a e mv` (an
   owned byte of `RPid` with its exact value), `okw1`/`okr1`, `HOw1`/`HOr1`/`HOp1`, the policy
   facts `uxPolGmo`/`uxPolIntro`; `AxSpinH`'s generic leaves instantiated: `wpdLdOwn1`,
   `wpdSdOwn1`, `wpdReloadOwn1` (one-byte; the real-width accesses are the word leaves below).
§4 REAL-WIDTH OWNED LEAVES at Ixv6 (hand nodes of `AxSpinX3`/`AxSpinX4`): nextpid (4 B)
   `wpdNpLwX` (handle `RNp` at a lob-predecessor ⇒ value handle at the lw + source fact),
   `wpdNpSwX` (value handle ⇒ `RNp` at the sw + the minted ◯{v}); lk->cpu (8 B) `wpdCpuSdX`
   (holder's sd of its cpu pointer or 0, any frame `Q`), `wpdCpuReloadX` (holder's ld after its
   own sd -- the gmo split inside: owned last-value read or forwarding; deposits `v = stored`),
   `wpdCpuRacyX` (non-holder's racy ld: deposits `v ≠ cpuAddr (cpuOf i)`).
§5 LOCK CONTRACTS at REAL WIDTH (4-byte `amoswap.w.aq`, `fence rw,w; sw`): `wpdAcquireX`
   (claim, notheld in hand, the claim's annotation pre-split along `LK ∗ RPid ⊢ R1 ∗ R2`),
   `wpdReacquireX` (notheld drawn from the hart's own release annotation), `wpdAcquireFailX` (the
   failed spin: frame passed to the retry), `wpdReleaseX` (any family of po-earlier anchors;
   lk->cpu and nextpid at their own anchors), `wpdLkHeldX` (the holder's `lw lk`: deposits
   `v ≠ 0`).
MILESTONE aspects: hand nodes (no fetch/decode), the layout is `Lx`.  §3, the lk->cpu leaves,
re-acquire, the failed spin and the holder `lw lk` are proved but not exercised by a certificate
in Rocq's AxSpinU2/U4.

## Deviations from Rocq

1. VOCABULARY (as `AxSpinX2`/`AxSpinX5` deviation 1): `Z` ↦ `Int`, `bv n` ↦ `BitVec n`,
   `gd_g GD` ↦ `GD.gdG`, `l !! j` ↦ `l[j]?` (indices `Nat`), `last l` ↦ `l.getLast?`, `H.*1` ↦
   `H.map Prod.fst`, `Z_to_bv 32` ↦ `BitVec.ofInt 32`, `bv_add w8 one32` ↦ `w8 + one32`,
   `bv_unsigned w8 + 1 < 2^32` ↦ `w8.toNat + 1 < 2 ^ 32` (over `Nat`), `0 ≤ v < 2^32` ↦
   `0 ≤ v ∧ v < 2 ^ 32`, `cpus_ptr (cpu_of i)` ↦ `cpuAddr (cpuOf i)`, `grow GD i !! k` ↦
   `(AxOpsem.grow (gtAdGd GT) i)[k]?`, `S k` ↦ `k + 1`, `dom m` ↦ `FiniteMap.dom_set m`,
   `B0`/`B1` ↦ `b0`/`b1`, `M unit` ↦ `SailM Unit`.  lean-sail hand nodes as `AxSpinX3`/`AxSpinX4`
   (`.impure (.ok (.memRead n 64 (rreqn n l3pAkP pa))) KK`, answers `.Ok (w, none)`;
   `AxSpinX4.acq4`, `fnc`, `stv`, `amoK`/`amoW`).
2. CONTEXTS (as `AxSpinX2` deviation 2): Rocq section variables are explicit leading arguments in
   Rocq's order, only where Rocq's section mechanism includes them (§1 `γ GD`; §2 `L GT nm`, then
   `HL Hcons` where `Proof using` names them; §3–§5 `GT nm cpu`, then `Hcons`).
   `invGS_gen HasNoLc Σ` ↦ `[InvGS_gen hlc GF]` for any `hlc`; `axannotG Σ`+`axannotGS Σ` ↦
   `[AxannotGS GF]`; `xv6G Σ` ↦ `[AxSpinX.Xv6G GF]`.  The local instances `ur_pol`/`ux_pol` ↦
   `xv6Pol GT` and `ur_G`/`ux_G` ↦ `AxSpinX2.xG L GT nm` (passed explicitly).  O2 STAGE C:
   Rocq's text argument (`xl_text L` / `Tf`) of `AxGA2`/`tierA_wpd` is gone.
3. STATEMENT SHAPES: wand chains ↦ `⊢ A -∗ B -∗ …` (pure premises stay `→`); `Rv_read_src`'s
   `own_inv -∗ Rv -∗ ⌜…⌝` ↦ `ownInv ∗ Rv ⊢ ⌜…⌝`; `Rv_retie`/`RVL_retie` ↦ `⊢`-entailments.  The
   Rocq notations `TW`/`LK`/`NH`/`RP`/`RNP`/`RCPU`/`ISL` are file-local Lean notations with the
   same expansions.  `NPh`/`FRAG`/`O1` are `def`s.
4. `wpd_ld_own1`/`wpd_sd_own1`/`wpd_reload_own1` (Rocq `Definition`s = partial applications of
   `AxSpinH`'s generic leaves) are theorems whose type is `type_of%` the same partial
   application.
5. PROOF ROUTE (not statements): `wpdCpuReloadX` splits on `gmoLt` classically (Rocq: boolean
   `gmo_lt_b`); `fxuNpRead`'s inner `iAssert (RVL ∧ ⌜np_src⌝)` is the Lean-only helper
   `AxSpinU.rvlNpSrc` used through `persistent_entails_left`; Rocq `vm_compute` facts by
   `decide +kernel`.
6. The trailing `Print Assumptions` commands are not ported.
7. Q-S2-B (owner ruling 2026-10-08, AxSpinX deviation 8: `protXv6` admits only FULL-WIDTH
   lk->cpu writes).  STATEMENT CHANGE: the one-byte owned write `fxuWrite1` takes `a ∉ clb L`
   and `okw1` gains the conjunct `a ∉ clb Lx` (Rocq: any `a ∈ XO`), so `HOw1`/`wpdSdOwn1` cover
   one-byte nextpid stores only (a one-byte lk->cpu store is no longer a protocol write; neither
   is used by a certificate or a later file).  `fxuNpIncr` discharges `xoSide`'s new `clFull`
   premise by `AxSpinX2.clFullNpb` (statement unchanged).  THE TWIN (Lean-only, owner request):
   `AxSpinU.fxuWriteCpu8` is the generic owned FULL-WIDTH lk->cpu write (an `sd` at
   `L.xlLk + 16` of `cvx w.1` or 0: annotation `RCpu e` ⇒ `RVL (clb L) w vs`; `clFull`/`cpuOk`
   discharged via `AxSpinX2.fxCpuWrite`), with `AxSpinU.okwCpu8`/`AxSpinU.HOwCpu8` at `Lx`.

**Rocq → Lean name map.**  `src_at` `srcAt`, `np_src` `npSrc`, `last_fst` `lastFst`, `Rv_retie`
`RvRetie`, `RVL_retie` `RVLRetie`, `Rv_read_src` `RvReadSrc`, `NPh` `NPh`, `FRAG` `FRAG`, `O1`
`O1`, `fxu_np_read` `fxuNpRead`, `fxu_np_incr` `fxuNpIncr`, `fxu_write1` `fxuWrite1`,
`fxu_read1` `fxuRead1`, `amo_k_word` `amoKWord`, `zero32_byte0` `zero32Byte0`,
`nth_byte_zero32` `nthByteZero32`, `ux_pol_gmo` `uxPolGmo`, `ux_pol_intro` `uxPolIntro`, `okw1`
`okw1`, `okr1` `okr1`, `HOw1` `HOw1`, `HOr1` `HOr1`, `HOp1` `HOp1`, `wpd_ld_own1` `wpdLdOwn1`,
`wpd_sd_own1` `wpdSdOwn1`, `wpd_reload_own1` `wpdReloadOwn1`, `wpd_np_lw_x` `wpdNpLwX`,
`wpd_np_sw_x` `wpdNpSwX`, `wpd_cpu_sd_x` `wpdCpuSdX`, `wpd_cpu_reload_x` `wpdCpuReloadX`,
`wpd_cpu_racy_x` `wpdCpuRacyX`, `lk_claim_of` `lkClaimOf`, `wpd_acquire_x` `wpdAcquireX`,
`wpd_reacquire_x` `wpdReacquireX`, `wpd_acquire_fail_x` `wpdAcquireFailX`, `wpd_release_x`
`wpdReleaseX`, `wpd_lk_held_x` `wpdLkHeldX`.  No duplicated Rocq names.
Lean-only (file-qualified): `AxSpinU.rvlNpSrc` (`fxu_np_read`'s inner `iAssert`: every byte of
the nextpid word has the source fact); `AxSpinU.fxuWriteCpu8`, `AxSpinU.okwCpu8`,
`AxSpinU.HOwCpu8` (deviation 7's full-width twin of `fxuWrite1`/`okw1`/`HOw1`).

**Dropped:** none (41 Rocq decls incl. the 4 local instances `ur_pol`/`ur_G`/`ux_pol`/`ux_G`
(inlined); 41 Lean = 37 + 4 Lean-only).
-/
import Weak.AxSpinH5
import Weak.AxSpinX5

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std Iris.Std.PartialMap MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D

/-! # 1. Pure / ghost facts -/

/-- The SOURCE of an owned read of byte `a` by `r` with anchor `e`: the image, or a write that is
`e` itself or gmo-before `e`. -/
def srcAt (G : Gexec) (r : Geid) (a : Int) (e : Geid) : Prop :=
  ∀ t v, greadsByte G r a t v → t = 0 ∨ ∃ w, gwriteAt G t = some w ∧ (w = e ∨ gmoLt G w e)

def npSrc (G : Gexec) (L : Xlay) (r e : Geid) : Prop := ∀ a, a ∈ npb L → srcAt G r a e

theorem lastFst {A B : Type} (l : List (A × B)) (x : A) (y : B) :
    l.getLast? = some (x, y) → (l.map Prod.fst).getLast? = some x := by
  intro h
  obtain ⟨l0, rfl⟩ := List.getLast?_eq_some_iff.mp h
  simp

section rvu
variable {GF : BundledGFunctors} [AxlogG GF Hent]

theorem RvRetie (γ : GName) (GD : Gdexec) (a : Int) (e e' : Geid) (vl : BitVec 8) :
    gmoLt GD.gdG e e' → Rv (GF := GF) γ GD a e vl ⊢ Rv γ GD a e' vl := by
  intro hlt
  unfold Rv
  iintro ⟨%H, Ha, %hp⟩
  obtain ⟨hw, hc⟩ := hp
  iexists H
  isplitl [Ha]
  · iexact Ha
  · ipureintro
    refine ⟨hw, ?_⟩
    rcases hc with h | ⟨hl, ht⟩
    · exact Or.inl h
    · exact Or.inr ⟨hl, tieLob _ _ e e' ht hlt⟩

theorem RVLRetie (γ : GName) (GD : Gdexec) (Cl : List Int) (e e' : Geid) (vs : List (BitVec 8)) :
    gmoLt GD.gdG e e' → RVL (GF := GF) γ GD Cl e vs ⊢ RVL γ GD Cl e' vs := by
  intro hlt
  unfold RVL
  iintro ⟨%hlen, H⟩
  isplitr
  · ipureintro
    exact hlen
  · iapply (BigSepL.bigSepL_mono_of_forall fun {k a} => ?_) $$ H
    iintro ⟨%v, %hv, Ha⟩
    iexists v
    isplitr
    · ipureintro
      exact hv
    · iapply (RvRetie γ GD a e e' v hlt) $$ Ha

/-- THE OWNED READ'S SOURCE: under the owned-read premises, `r` reads byte `a` from the image or
from the history's last write -- which is the anchor `e` or gmo-before it (`tieBase`). -/
theorem RvReadSrc (γ : GName) (GD : Gdexec) (X : GSet Int) (s : GSet Geid) (a : Int) (e r : Geid)
    (vl : BitVec 8) :
    rvwmoCatConsistent GD → a ∈ X → gmoLt GD.gdG e r → WPh GD.gdG s r →
    (∀ w v', gwritesByte GD.gdG w a v' → WeakRvwmoGraph.gpo GD.gdG w r → gmoLt GD.gdG w r) →
    (∃ t v, greadsByte GD.gdG r a t v) →
    ownInv (GF := GF) X γ GD s ∗ Rv γ GD a e vl ⊢ ⌜srcAt GD.gdG r a e⌝ := by
  intro hcons haX her hwp hpo hex
  unfold Rv
  iintro ⟨#Hinv, %H, Ha, %hp⟩
  obtain ⟨⟨hwr, hch⟩, hc⟩ := hp
  ihave #Hcov := AxSpinProt5.covMoX γ X a GD s r haX hwp $$ Hinv
  icases (persistent_entails_left (AxSpinX.histInOfCov (GF := GF) γ GD a r H))
    $$ [$Ha $Hcov] with ⟨⟨Ha, -⟩, %hin⟩
  rcases hc with ⟨rfl, -⟩ | ⟨⟨wl, hlast⟩, ht⟩
  · ipureintro
    intro t v hrd
    left
    cases t with
    | zero => rfl
    | succ j =>
      exfalso
      obtain ⟨w, -, hw', hvis⟩ := (hcons.2.2.1 r a (j + 1) v hrd).1
      have hlt : gmoLt GD.gdG w r := hvis.elim id (hpo w v hw')
      have := hin w v hw' hlt
      simp at this
  · have hown : ∀ w v', gwritesByte GD.gdG w a v' → WeakRvwmoGraph.gpo GD.gdG w r →
        w ∈ H.map Prod.fst := fun w v' hw' hp => hin w v' hw' (hpo w v' hw' hp)
    ihave HT := (AxSpinProt.tokTieSingleton GD γ a H e ht).1 $$ Ha
    icases (persistent_entails_left (ownedReadRule (GF := GF) GD a r γ H {[e := (1 : Qp)]} wl vl
        hcons hwr hch hown hlast hex
        (Or.inl ⟨e, by rw [domSingleton, elemOfSingleton], her⟩)))
      $$ [$HT $Hcov] with ⟨-, %hv⟩
    ipureintro
    intro t v hrd
    right
    obtain ⟨t', v', hrd', hwa⟩ := hv.1
    obtain ⟨rfl, -⟩ := greadsByteDet _ _ _ _ _ _ _ hrd hrd'
    refine ⟨wl, hwa, ?_⟩
    have hl1 := lastFst H wl vl hlast
    rcases ht with he | ⟨wl', he, hlt⟩
    · rw [hl1] at he
      exact Or.inl (Option.some.inj he)
    · rw [hl1] at he
      rw [Option.some.inj he]
      exact Or.inr hlt

/-- (Lean-only) `fxu_np_read`'s inner `iAssert`: under the owned-read premises, every byte of
the nextpid word read by `r` has its source at `e` or gmo-before it. -/
theorem AxSpinU.rvlNpSrc (γ : GName) (GD : Gdexec) (X : GSet Int) (s : GSet Geid) (L : Xlay)
    (e r : Geid) (ts : List Nat) (w8 : BitVec 32) (vs : List (BitVec 8)) :
    rvwmoCatConsistent GD → (∀ a, a ∈ npb L → a ∈ X) → gmoLt GD.gdG e r → WPh GD.gdG s r →
    (∀ w a v', a ∈ npb L → gwritesByte GD.gdG w a v' → WeakRvwmoGraph.gpo GD.gdG w r →
      gmoLt GD.gdG w r) →
    gxLbl GD.gdG r = some (.LLoad false L.xlNp ts (WeakInterpProj.wbytes 4 w8)) →
    ownInv (GF := GF) X γ GD s ∗ RVL γ GD (npb L) e vs ⊢ ⌜npSrc GD.gdG L r e⌝ := by
  intro hcons hX her hwp hpo hl
  unfold RVL
  iintro ⟨#Hinv, -, HR⟩
  ihave HR := (BigSepL.bigSepL_impl
    (Φ := fun j a => iprop(∃ b, ⌜vs[j]? = some b⌝ ∗ Rv (GF := GF) γ GD a e b))
    (Ψ := fun _ a => iprop(⌜srcAt GD.gdG r a e⌝ : IProp GF)) (l := npb L)) $$ HR
  ihave HR := HR $$ []
  · imodintro
    iintro %j %a %hj ⟨%b, -, Ha⟩
    have ha : a ∈ npb L := List.mem_of_getElem? hj
    have hj' : (clRange L.xlNp 4)[j]? = some a := hj
    obtain ⟨heq, hjl⟩ := AxSpinX4.clRangeLookup _ _ _ _ hj'
    obtain ⟨t, ht⟩ := loadnReads GD.gdG hcons.1 r L.xlNp ts 4 w8 j hl hjl
    rw [← heq] at ht
    iapply (RvReadSrc γ GD X s a e r b hcons (hX a ha) her hwp
      (fun w v' hw hp => hpo w a v' ha hw hp) ⟨t, _, ht⟩)
    isplitl []
    · iexact Hinv
    · iexact Ha
  ihave %hP := (BigSepL.bigSepL_pure_intro (φ := fun _ a => srcAt GD.gdG r a e) (l := npb L)
    (PROP := IProp GF)) $$ HR
  ipureintro
  intro a ha
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 ha
  exact hP j a hj

end rvu

/-- The nextpid VALUE handle's content: `RNpv` at value `v`, `v`'s 32-bit word = `w8`. -/
def NPh {GF : BundledGFunctors} [AxSpinX.Xv6G GF] (L : Xlay) (GT : GdexecT) (nm : Xv6N)
    (e : Geid) (w8 : BitVec 32) : IProp GF :=
  iprop(∃ v, RNpv L GT nm e v ∗ ⌜BitVec.ofInt 32 v = w8⌝)

/-- The minted fragment with its value. -/
def FRAG {GF : BundledGFunctors} [AxSpinX.Xv6G GF] (nm : Xv6N) (w8 : BitVec 32) : IProp GF :=
  iprop(∃ v, issuedFrag nm.xnI v ∗ ⌜(0 ≤ v ∧ v < 2 ^ 32) ∧ BitVec.ofInt 32 v = w8⌝)

/-- One owned byte of `RPid` with its exact value (the generic interface's `O`). -/
def O1 {GF : BundledGFunctors} [AxSpinX.Xv6G GF] (nm : Xv6N) (GD : Gdexec) (a : Int) (e : Geid)
    (mv : Option (BitVec 8)) : IProp GF :=
  iprop(∃ vl, Rv nm.xnH GD a e vl ∗ ⌜∀ v, mv = some v → vl = v⌝)

/-! # 2. New rules at `protXv6 L` -/

section uRules
variable {hlc : HasLC} {GF : BundledGFunctors.{0,0,0}} [InvGS_gen hlc GF] [AxannotGS GF]
  [AxSpinX.Xv6G GF]

/-- THE CS's `lw nextpid`: value handle + source fact at the read. -/
theorem fxuNpRead (L : Xlay) (GT : GdexecT) (nm : Xv6N) (_HL : xlayOk L)
    (Hcons : rvwmoCatConsistent (gtAdGd GT)) (r e : Geid) (ts : List Nat) (w8 : BitVec 32)
    (Q : IProp GF) (flowIn : Mea GF) :
    gxLbl (gtAdGd GT).gdG r = some (.LLoad false L.xlNp ts (WeakInterpProj.wbytes 4 w8)) →
    gmoLt (gtAdGd GT).gdG e r →
    (∀ w a v', a ∈ npb L → gwritesByte (gtAdGd GT).gdG w a v' →
      WeakRvwmoGraph.gpo (gtAdGd GT).gdG w r → gmoLt (gtAdGd GT).gdG w r) →
    ⊢ (([∗map] Rin ∈ flowIn, Rin) -∗ Q ∗ RNp L nm.xnH nm.xnM nm.xnI (gtAdGd GT) e) -∗
      @flowEqDyn hlc GF _ (AxSpinX2.xG L GT nm) (gtAdGd GT) r
        (@Axpol.sPol (xv6Pol GT) (gtAdGd GT) r) flowIn
        iprop(Q ∗ NPh L GT nm r w8 ∗ ⌜npSrc (gtAdGd GT).gdG L r e⌝) := by
  intro Hl Her Hpo
  have Hnw : gisW (gtAdGd GT).gdG r = false := by unfold gisW; rw [Hl]; rfl
  obtain ⟨Hnx, Hok, Hwk⟩ := nwSide L GT r Hnw
  have Hwf := Hcons.1
  unfold RNp NPh RNpv
  iintro Hfi
  iapply fxBuild
  iintro %s %Hn %_ %Hwp %_ %_ %_ #Ho Hlk Hin
  ihave ⟨HQ, %v, %Hv, HR, Hm, HS⟩ := Hfi $$ Hin
  icases (persistent_entails_left (AxSpinU.rvlNpSrc (GF := GF) nm.xnH (gtAdGd GT) (XO L) s L e r
      ts w8 _ Hcons (npbXO L) Her Hwp Hpo Hl)) $$ [$Ho $HR] with ⟨⟨-, HR⟩, %Hsrc⟩
  ihave ⟨HR, %Hf⟩ := (RVLRead nm.xnH (gtAdGd GT) (XO L) s (npb L) e r _ Hcons (npbXO L) Her Hwp
    Hpo) $$ [$Ho $HR]
  have Hw8 : BitVec.ofInt 32 v = w8 :=
    (wbytes4Inj _ _ (readFactWord (gtAdGd GT).gdG Hwf r L.xlNp ts 4 w8 _ Hl (wbytesLength 4 _)
      Hf)).symm
  imodintro
  inext
  imodintro
  isplitr
  · ipureintro
    exact ⟨Hok, Hwk⟩
  isplitl []
  · iapply (ownInvOther (XO L) nm.xnH (gtAdGd GT) s r Hn Hnx) $$ Ho
  isplitl [Hlk]
  · iapply (lkInvRead nm.xnReg L.xlLk (gtAdGd GT) s r Hcons Hwp Hn Hnw) $$ Hlk
  isplitl [HQ]
  · iexact HQ
  isplitl [HR Hm HS]
  · iexists v
    isplitl [HR Hm HS]
    · isplitr
      · ipureintro
        exact Hv
      isplitl [HR]
      · iapply (RVLRetie nm.xnH (gtAdGd GT) (npb L) e r _ Her) $$ HR
      isplitl [Hm]
      · iexact Hm
      · iexact HS
    · ipureintro
      exact Hw8
  · ipureintro
    exact Hsrc

/-- THE CS's `sw nextpid ← w8+1` from a VALUE handle (Theorem 2's ghost step: ●mono v → v+1,
the exclusive ◯{v} minted). -/
theorem fxuNpIncr (L : Xlay) (GT : GdexecT) (nm : Xv6N) (HL : xlayOk L)
    (_Hcons : rvwmoCatConsistent (gtAdGd GT)) (w e : Geid) (w8 : BitVec 32) (cls : WmClass)
    (Q : IProp GF) (flowIn : Mea GF) :
    gxLbl (gtAdGd GT).gdG w =
      some (.LStore false L.xlNp (WeakInterpProj.wbytes 4 (w8 + one32)) cls) →
    gmoLt (gtAdGd GT).gdG e w → w8.toNat + 1 < 2 ^ 32 →
    ⊢ (([∗map] Rin ∈ flowIn, Rin) -∗ Q ∗ NPh L GT nm e w8) -∗
      @flowEqDyn hlc GF _ (AxSpinX2.xG L GT nm) (gtAdGd GT) w
        (@Axpol.sPol (xv6Pol GT) (gtAdGd GT) w) flowIn
        iprop(Q ∗ RNp L nm.xnH nm.xnM nm.xnI (gtAdGd GT) w ∗ FRAG nm w8) := by
  intro Hl Hew Hnwr
  obtain ⟨Hwb, Hsg⟩ := gwbStoren _ _ _ _ _ Hl
  have Honly : ∀ a v', gwritesByte (gtAdGd GT).gdG w a v' → a ∈ npb L := by
    intro a v' Hw
    obtain ⟨j, Hj, rfl⟩ := Hsg a v' Hw
    have hj := (List.getElem?_eq_some_iff.1 Hj).1
    rw [wbytesLength] at hj
    unfold npb
    rw [inClr]
    omega
  obtain ⟨Hnlk, Hwk⟩ := xoSide L GT HL w (npb L) Honly (npbXO L)
    (AxSpinX2.clFullNpb L HL _ w Honly)
  have Hok : cpuOk (clb L) cvx (gtAdGd GT).gdG w := by
    apply cpuOkNw
    intro a v Ha Hw
    exact clbNpbDisj L HL a Ha (Honly a v Hw)
  have Hisw : gisW (gtAdGd GT).gdG w = true := by unfold gisW; rw [Hl]; rfl
  unfold NPh RNpv FRAG RNp
  iintro Hfi
  iapply fxBuild
  iintro %s %Hn %_ %_ %_ %_ %_ Ho Hlk Hin
  ihave ⟨HQ, %v, ⟨%Hv, HR, Hm, %S, HS, %HS⟩, %Hvw⟩ := Hfi $$ Hin
  obtain ⟨Hlt, Heq⟩ := npSucc v w8 Hv Hvw Hnwr
  have Hlen : (WeakInterpProj.wbytes 4 (BitVec.ofInt 32 (v + 1))).length = (npb L).length := by
    rw [wbytesLength]
    simp [npb, clRange]
  have Hwr : ∀ (j : Nat) a b, (npb L)[j]? = some a →
      (WeakInterpProj.wbytes 4 (BitVec.ofInt 32 (v + 1)))[j]? = some b →
      gwritesByte (gtAdGd GT).gdG w a b := by
    intro j a b Hj Hb
    rw [Heq] at Hb
    have Hj' : (clRange L.xlNp 4)[j]? = some a := Hj
    obtain ⟨rfl, -⟩ := AxSpinX4.clRangeLookup _ _ _ _ Hj'
    exact Hwb j b Hb
  imod (RVLWrite nm.xnH (gtAdGd GT) (XO L) (npb L) s e w _
    (WeakInterpProj.wbytes 4 (BitVec.ofInt 32 (v + 1))) Hn Hew Hlen Hwr Honly)
    $$ [$Ho $HR] with ⟨Ho, HR⟩
  imod (npIssue nm.xnM nm.xnI v S Hv.1 HS) $$ [$Hm $HS] with ⟨Hm, HS, Hfrag, %HS'⟩
  imodintro
  inext
  imodintro
  isplitr
  · ipureintro
    exact ⟨Hok, Hwk⟩
  isplitl [Ho]
  · iexact Ho
  isplitl [Hlk]
  · iapply (lkInvOther nm.xnReg L.xlLk (gtAdGd GT) s w Hn Hnlk
      (fun ⟨_, Hnw'⟩ => by rw [Hisw] at Hnw'; cases Hnw')) $$ Hlk
  isplitl [HQ]
  · iexact HQ
  isplitl [HR Hm HS]
  · iexists (v + 1)
    isplitr
    · ipureintro
      omega
    isplitl [HR]
    · iexact HR
    isplitl [Hm]
    · iexact Hm
    · iexists (({v} : GSet Int) ∪ S)
      isplitl [HS]
      · iexact HS
      · ipureintro
        exact HS'
  · iexists v
    isplitl [Hfrag]
    · iexact Hfrag
    · ipureintro
      exact ⟨Hv, Hvw⟩

/-- The one-byte owned write (the generic interface's `HOw`). -/
theorem fxuWrite1 (L : Xlay) (GT : GdexecT) (nm : Xv6N) (HL : xlayOk L)
    (Hcons : rvwmoCatConsistent (gtAdGd GT)) (w e : Geid) (a : Int) (b : BitVec 8)
    (cls : WmClass) (mv : Option (BitVec 8)) :
    gxLbl (gtAdGd GT).gdG w = some (.LStore false a [b] cls) → a ∈ XO L → a ∉ clb L →
    cpuOk (clb L) cvx (gtAdGd GT).gdG w → gmoLt (gtAdGd GT).gdG e w →
    ⊢ @flowEqDyn hlc GF _ (AxSpinX2.xG L GT nm) (gtAdGd GT) w
        (@Axpol.sPol (xv6Pol GT) (gtAdGd GT) w)
        ({[e := O1 nm (gtAdGd GT) a e mv]} : Mea GF) (O1 nm (gtAdGd GT) a w (some b)) := by
  intro Hl HaX Hnc Hok Hew
  obtain ⟨Hw, Hsg⟩ := gwbStore _ _ _ _ _ Hl
  have Hisw : gisW (gtAdGd GT).gdG w = true := by unfold gisW; rw [Hl]; rfl
  have Hlen : [b].length = [a].length := rfl
  have Hall : ∀ (j : Nat) a' v', [a][j]? = some a' → [b][j]? = some v' →
      gwritesByte (gtAdGd GT).gdG w a' v' := by
    intro j a' v' Hj Hv'
    match j, Hj, Hv' with
    | 0, Hj, Hv' =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at Hj Hv'
      subst Hj Hv'
      exact Hw
    | _ + 1, Hj, _ => simp at Hj
  have Honly : ∀ a' v', gwritesByte (gtAdGd GT).gdG w a' v' → a' ∈ [a] :=
    fun a' v' Hw' => List.mem_singleton.2 (Hsg a' v' Hw').1
  have HX : ∀ a', a' ∈ [a] → a' ∈ XO L := by
    intro a' Ha'
    rw [List.mem_singleton.1 Ha']
    exact HaX
  have Hw0 : ⊢ ([∗map] Rin ∈ ({[e := O1 nm (gtAdGd GT) a e mv]} : Mea GF), Rin) -∗
      iprop(True ∗ ∃ vold, RVL nm.xnH (gtAdGd GT) [a] e vold) := by
    iintro H
    ihave H := (BigSepM.bigSepM_singleton (M := GMapF Geid)).1 $$ H
    iunfold O1 at H
    icases H with ⟨%vl, Ha, -⟩
    isplitr
    · itrivial
    · iexists [vl]
      iunfold RVL
      isplitr
      · ipureintro
        rfl
      · iapply BigSepL.bigSepL_singleton.2
        iexists vl
        isplitr
        · ipureintro
          rfl
        · iexact Ha
  ihave Hw := Hw0
  ihave Hfe := (fxRVLWrite (hlc := hlc) L GT nm HL Hcons w e [a] [b] iprop(True)
    ({[e := O1 nm (gtAdGd GT) a e mv]} : Mea GF) Hisw Hew Hlen Hall Honly HX Hok
    (AxSpinX.clFullNo L _ w fun a' v' Ha' Hw' => by
      rw [(Hsg a' v' Hw').1] at Ha'
      exact Hnc Ha')) $$ Hw
  iapply (@flowEqDynMono hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) (gtAdGd GT) w _ _
    iprop(True ∗ RVL nm.xnH (gtAdGd GT) [a] w [b]) (O1 nm (gtAdGd GT) a w (some b))) $$ [] Hfe
  inext
  iintro ⟨-, H⟩
  iunfold RVL at H
  icases H with ⟨-, H⟩
  ihave H := BigSepL.bigSepL_singleton.1 $$ H
  icases H with ⟨%v, %Hv, Ha⟩
  have Hbv : b = v := by simpa using Hv
  subst Hbv
  iunfold O1
  iexists b
  isplitl [Ha]
  · iexact Ha
  · ipureintro
    intro v0 Hv0
    exact Option.some.inj Hv0

/-- (Lean-only, Q-S2-B) The TWIN of `fxuWrite1` for lk->cpu: the owned FULL-WIDTH write of all
8 bytes `clb L` (an `sd` at `L.xlLk + 16`) of a value the protocol admits (`cvx w.1`, the
writer's cpu pointer, or 0); `clFull` and `cpuOk` are discharged from the label and the value
(by `AxSpinX2.fxCpuWrite`). -/
theorem AxSpinU.fxuWriteCpu8 (L : Xlay) (GT : GdexecT) (nm : Xv6N) (HL : xlayOk L)
    (Hcons : rvwmoCatConsistent (gtAdGd GT)) (w e : Geid) (vs : List (BitVec 8))
    (cls : WmClass) :
    gxLbl (gtAdGd GT).gdG w = some (.LStore false (L.xlLk + 16) vs cls) →
    (vs = cvx w.1 ∨ vs = List.replicate 8 b0) → gmoLt (gtAdGd GT).gdG e w →
    ⊢ @flowEqDyn hlc GF _ (AxSpinX2.xG L GT nm) (gtAdGd GT) w
        (@Axpol.sPol (xv6Pol GT) (gtAdGd GT) w)
        ({[e := RCpu L nm.xnH (gtAdGd GT) e]} : Mea GF) (RVL nm.xnH (gtAdGd GT) (clb L) w vs) := by
  intro Hl Hv Hew
  obtain ⟨Hw, Hsg⟩ := gwbStoren _ _ _ _ _ Hl
  have Hisw : gisW (gtAdGd GT).gdG w = true := by unfold gisW; rw [Hl]; rfl
  have Hlen : vs.length = 8 := by
    rcases Hv with rfl | rfl
    · exact cvxLength _
    · exact List.length_replicate
  have Hall : ∀ (j : Nat) a v, (clb L)[j]? = some a → vs[j]? = some v →
      gwritesByte (gtAdGd GT).gdG w a v := by
    intro j a v Hj Hv'
    have Hj' : (clRange (L.xlLk + 16) 8)[j]? = some a := Hj
    obtain ⟨rfl, -⟩ := AxSpinX4.clRangeLookup _ _ _ _ Hj'
    exact Hw j v Hv'
  have Honly : ∀ a v, gwritesByte (gtAdGd GT).gdG w a v → a ∈ clb L := by
    intro a v Hw'
    obtain ⟨j, Hj, rfl⟩ := Hsg a v Hw'
    have hj := (List.getElem?_eq_some_iff.1 Hj).1
    rw [Hlen] at hj
    unfold clb
    rw [inClr]
    omega
  have Hw0 : ⊢ ([∗map] Rin ∈ ({[e := RCpu L nm.xnH (gtAdGd GT) e]} : Mea GF), Rin) -∗
      iprop(True ∗ ∃ vold, RVL nm.xnH (gtAdGd GT) (clb L) e vold) := by
    iintro H
    ihave H := (BigSepM.bigSepM_singleton (M := GMapF Geid)).1 $$ H
    isplitr
    · itrivial
    · iunfold RCpu at H
      iexact H
  ihave Hw := Hw0
  ihave Hfe := (fxCpuWrite (hlc := hlc) L GT nm HL Hcons w e vs iprop(True)
    ({[e := RCpu L nm.xnH (gtAdGd GT) e]} : Mea GF) Hisw Hew Hv Hall Honly) $$ Hw
  iapply (@flowEqDynMono hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) (gtAdGd GT) w _ _
    iprop(True ∗ RVL nm.xnH (gtAdGd GT) (clb L) w vs) (RVL nm.xnH (gtAdGd GT) (clb L) w vs))
    $$ [] Hfe
  inext
  iintro ⟨-, H⟩
  iexact H

/-- The one-byte owned read (the generic interface's `HOr`). -/
theorem fxuRead1 (L : Xlay) (GT : GdexecT) (nm : Xv6N) (_HL : xlayOk L)
    (Hcons : rvwmoCatConsistent (gtAdGd GT)) (r e : Geid) (a : Int) (t : Nat) (v : BitVec 8)
    (mv : Option (BitVec 8)) :
    gxLbl (gtAdGd GT).gdG r = some (.LLoad false a [t] [v]) → a ∈ XO L →
    gmoLt (gtAdGd GT).gdG e r →
    (∀ w v', gwritesByte (gtAdGd GT).gdG w a v' → WeakRvwmoGraph.gpo (gtAdGd GT).gdG w r →
      gmoLt (gtAdGd GT).gdG w r) →
    ⊢ @flowEqDyn hlc GF _ (AxSpinX2.xG L GT nm) (gtAdGd GT) r
        (@Axpol.sPol (xv6Pol GT) (gtAdGd GT) r)
        ({[e := O1 nm (gtAdGd GT) a e mv]} : Mea GF)
        iprop(O1 nm (gtAdGd GT) a r (some v) ∗ ⌜∀ v0, mv = some v0 → v = v0⌝) := by
  intro Hl HaX Her Hfw
  have Hrd := grbLoad _ _ _ _ _ Hl
  have Hnw : gisW (gtAdGd GT).gdG r = false := by unfold gisW; rw [Hl]; rfl
  obtain ⟨Hnx, Hok, Hwk⟩ := nwSide L GT r Hnw
  unfold O1
  iapply fxBuild
  iintro %s %Hn %_ %Hwp %_ %_ %_ #Ho Hlk Hin
  ihave Hin := (BigSepM.bigSepM_singleton (M := GMapF Geid)).1 $$ Hin
  icases Hin with ⟨%vl, Ha, %Hmv⟩
  ihave ⟨Ha, %Hf⟩ := (RvRead nm.xnH (gtAdGd GT) (XO L) s a e r vl Hcons HaX Her Hwp Hfw)
    $$ [$Ho $Ha]
  have Hvl : v = vl := Hf t v Hrd
  subst Hvl
  imodintro
  inext
  imodintro
  isplitr
  · ipureintro
    exact ⟨Hok, Hwk⟩
  isplitl []
  · iapply (ownInvOther (XO L) nm.xnH (gtAdGd GT) s r Hn Hnx) $$ Ho
  isplitl [Hlk]
  · iapply (lkInvRead nm.xnReg L.xlLk (gtAdGd GT) s r Hcons Hwp Hn Hnw) $$ Hlk
  isplitl [Ha]
  · iexists v
    isplitl [Ha]
    · iapply (RvRetie nm.xnH (gtAdGd GT) a e r v Her) $$ Ha
    · ipureintro
      intro v0 Hv0
      exact Option.some.inj Hv0
  · ipureintro
    exact Hmv

end uRules

/-! # 3–5. THE SURFACE AT Ixv6 -/

theorem amoKWord (kok kf : SailM Unit) (w : BitVec 32) :
    amoK kok kf (.Ok (wordOfBytes 4 (WeakInterpProj.wbytes 4 w), none)) = amoW kok kf w := by
  rw [wordOfBytesWbytes]

theorem zero32Byte0 : (WeakInterpProj.wbytes 4 zero32)[0]? = some b0 := by decide +kernel

theorem nthByteZero32 : nthByte (n := 4) zero32 0 = b0 := by decide +kernel

/-! ## §3 the generic owned-class interface (AxSpinH §2) at Ixv6 -/

theorem uxPolGmo (GT : GdexecT) (e r : Geid) :
    e ∈ @Axpol.lobp (xv6Pol GT) (gtAdGd GT) r → gmoLt (gtAdGd GT).gdG e r :=
  fun He => splPolGmo GT e r He

theorem uxPolIntro (GT : GdexecT) (e r : Geid) (l : Lbl) :
    gxLbl (gtAdGd GT).gdG e = some l → lbIsMem l = true →
    WeakRvwmoGraph.gpo (gtAdGd GT).gdG e r → gmoLt (gtAdGd GT).gdG e r →
    e ∈ @Axpol.lobp (xv6Pol GT) (gtAdGd GT) r :=
  fun H1 H2 H3 H4 => lobpIntro (gtAdGd GT) e r l H1 H2 H3 H4

def okw1 (GT : GdexecT) (w : Geid) (a : Int) (_b : BitVec 8) : Prop :=
  a ∈ XO Lx ∧ a ∉ clb Lx ∧ cpuOk (clb Lx) cvx (gtAdGd GT).gdG w

/-- (Lean-only, Q-S2-B) the policy side condition of `AxSpinU.HOwCpu8`: the 8-byte lk->cpu value
is the writer's cpu pointer or 0 (exactly what `cpuOk` admits for a full-width write). -/
def AxSpinU.okwCpu8 (_GT : GdexecT) (w : Geid) (vs : List (BitVec 8)) : Prop :=
  vs = cvx w.1 ∨ vs = List.replicate 8 b0

def okr1 (_r : Geid) (a : Int) : Prop := a ∈ XO Lx

section leavesX
variable {hlc : HasLC} {GF : BundledGFunctors.{0,0,0}} [InvGS_gen hlc GF] [AxannotGS GF]
  [AxSpinX.Xv6G GF]

set_option hygiene false in
local notation "TW " i:max Φ:max s:max => @tierAWpd GF hlc _ _ (xv6Pol GT) (gtAdGd GT) Xv6N Unit
  (protXv6 Lx) nm s .MaybeStuck i Φ
set_option hygiene false in
local notation "LK " i:max c:max => locked (GF := GF) nm.xnReg Lx.xlLk i c
set_option hygiene false in
local notation "NH " i:max => notheld (GF := GF) nm.xnReg Lx.xlLk i
set_option hygiene false in
local notation "RP" => RPid (GF := GF) Lx nm.xnH nm.xnM nm.xnI (gtAdGd GT)
set_option hygiene false in
local notation "RNP " e:max => RNp (GF := GF) Lx nm.xnH nm.xnM nm.xnI (gtAdGd GT) e
set_option hygiene false in
local notation "RCPU " e:max => RCpu (GF := GF) Lx nm.xnH (gtAdGd GT) e
set_option hygiene false in
local notation "ISL" =>
  isLock (GF := GF) nm.xnReg Lx.xlLk (RPid Lx nm.xnH nm.xnM nm.xnI (gtAdGd GT))

theorem HOw1 (GT : GdexecT) (nm : Xv6N) (Hcons : rvwmoCatConsistent (gtAdGd GT)) (w e : Geid)
    (a : Int) (b : BitVec 8) (cls : WmClass) (mv : Option (BitVec 8)) :
    gxLbl (gtAdGd GT).gdG w = some (.LStore false a [b] cls) → okw1 GT w a b →
    gmoLt (gtAdGd GT).gdG e w →
    ⊢ @flowEqDyn hlc GF _ (AxSpinX2.xG Lx GT nm) (gtAdGd GT) w
        (@Axpol.sPol (xv6Pol GT) (gtAdGd GT) w)
        ({[e := O1 nm (gtAdGd GT) a e mv]} : Mea GF) (O1 nm (gtAdGd GT) a w (some b)) :=
  fun Hl ⟨HaX, Hnc, Hok⟩ Hew => fxuWrite1 Lx GT nm LxOk Hcons w e a b cls mv Hl HaX Hnc Hok Hew

/-- (Lean-only, Q-S2-B) `AxSpinU.fxuWriteCpu8` at Ixv6 (the full-width twin of `HOw1`). -/
theorem AxSpinU.HOwCpu8 (GT : GdexecT) (nm : Xv6N) (Hcons : rvwmoCatConsistent (gtAdGd GT))
    (w e : Geid) (vs : List (BitVec 8)) (cls : WmClass) :
    gxLbl (gtAdGd GT).gdG w = some (.LStore false (Lx.xlLk + 16) vs cls) →
    AxSpinU.okwCpu8 GT w vs → gmoLt (gtAdGd GT).gdG e w →
    ⊢ @flowEqDyn hlc GF _ (AxSpinX2.xG Lx GT nm) (gtAdGd GT) w
        (@Axpol.sPol (xv6Pol GT) (gtAdGd GT) w)
        ({[e := RCpu Lx nm.xnH (gtAdGd GT) e]} : Mea GF)
        (RVL nm.xnH (gtAdGd GT) (clb Lx) w vs) :=
  fun Hl Hok Hew => AxSpinU.fxuWriteCpu8 Lx GT nm LxOk Hcons w e vs cls Hl Hok Hew

theorem HOr1 (GT : GdexecT) (nm : Xv6N) (Hcons : rvwmoCatConsistent (gtAdGd GT)) (r e : Geid)
    (a : Int) (t : Nat) (v : BitVec 8) (mv : Option (BitVec 8)) :
    gxLbl (gtAdGd GT).gdG r = some (.LLoad false a [t] [v]) → okr1 r a →
    gmoLt (gtAdGd GT).gdG e r →
    (∀ w v', gwritesByte (gtAdGd GT).gdG w a v' → WeakRvwmoGraph.gpo (gtAdGd GT).gdG w r →
      gmoLt (gtAdGd GT).gdG w r) →
    ⊢ @flowEqDyn hlc GF _ (AxSpinX2.xG Lx GT nm) (gtAdGd GT) r
        (@Axpol.sPol (xv6Pol GT) (gtAdGd GT) r)
        ({[e := O1 nm (gtAdGd GT) a e mv]} : Mea GF)
        iprop(O1 nm (gtAdGd GT) a r (some v) ∗ ⌜∀ v0, mv = some v0 → v = v0⌝) :=
  fun Hl HaX Her Hfw => fxuRead1 Lx GT nm LxOk Hcons r e a t v mv Hl HaX Her Hfw

theorem HOp1 (GT : GdexecT) (nm : Xv6N) (Hcons : rvwmoCatConsistent (gtAdGd GT)) (r : Geid)
    (a : Int) (t : Nat) (v : BitVec 8) :
    gxLbl (gtAdGd GT).gdG r = some (.LLoad false a [t] [v]) → okr1 r a →
    ⊢ @flowEqDyn hlc GF _ (AxSpinX2.xG Lx GT nm) (gtAdGd GT) r
        (@Axpol.sPol (xv6Pol GT) (gtAdGd GT) r) (∅ : Mea GF) iprop(True) :=
  fun Hl _ => fxRead Lx GT nm LxOk Hcons r (by unfold gisW; rw [Hl]; rfl)

/-- `AxSpinH`'s generic one-byte owned load, AT Ixv6 (Rocq `Definition wpd_ld_own1`). -/
theorem wpdLdOwn1 (GT : GdexecT) (nm : Xv6N) (cpu : CPU) (Hcons : rvwmoCatConsistent (gtAdGd GT)) :
    type_of% (wpdLdOwn (hlc := hlc) (GF := GF) (pol := xv6Pol GT) (gtAdGd GT) Xv6N Unit
      (protXv6 Lx) nm (xv6AxpolWf GT) cpu (O1 nm (gtAdGd GT)) okr1 (uxPolGmo GT)
      (HOr1 GT nm Hcons)) :=
  wpdLdOwn (hlc := hlc) (GF := GF) (pol := xv6Pol GT) (gtAdGd GT) Xv6N Unit (protXv6 Lx) nm
    (xv6AxpolWf GT) cpu (O1 nm (gtAdGd GT)) okr1 (uxPolGmo GT) (HOr1 GT nm Hcons)

/-- `AxSpinH`'s generic one-byte owned store, AT Ixv6 (Rocq `Definition wpd_sd_own1`). -/
theorem wpdSdOwn1 (GT : GdexecT) (nm : Xv6N) (cpu : CPU) (Hcons : rvwmoCatConsistent (gtAdGd GT)) :
    type_of% (wpdSdOwn (hlc := hlc) (GF := GF) (pol := xv6Pol GT) (gtAdGd GT) Xv6N Unit
      (protXv6 Lx) nm (xv6AxpolWf GT) cpu (O1 nm (gtAdGd GT)) (okw1 GT) (uxPolGmo GT)
      (HOw1 GT nm Hcons)) :=
  wpdSdOwn (hlc := hlc) (GF := GF) (pol := xv6Pol GT) (gtAdGd GT) Xv6N Unit (protXv6 Lx) nm
    (xv6AxpolWf GT) cpu (O1 nm (gtAdGd GT)) (okw1 GT) (uxPolGmo GT) (HOw1 GT nm Hcons)

/-- `AxSpinH`'s generic forwarded-reload leaf, AT Ixv6 (Rocq `Definition wpd_reload_own1`). -/
theorem wpdReloadOwn1 (GT : GdexecT) (nm : Xv6N) (cpu : CPU)
    (Hcons : rvwmoCatConsistent (gtAdGd GT)) :
    type_of% (wpdReloadOwn (hlc := hlc) (GF := GF) (pol := xv6Pol GT) (gtAdGd GT) Xv6N Unit
      (protXv6 Lx) nm (xv6AxpolWf GT) cpu Hcons (O1 nm (gtAdGd GT)) okr1 (uxPolGmo GT)
      (uxPolIntro GT) (HOr1 GT nm Hcons) (HOp1 GT nm Hcons)) :=
  wpdReloadOwn (hlc := hlc) (GF := GF) (pol := xv6Pol GT) (gtAdGd GT) Xv6N Unit (protXv6 Lx) nm
    (xv6AxpolWf GT) cpu Hcons (O1 nm (gtAdGd GT)) okr1 (uxPolGmo GT) (uxPolIntro GT)
    (HOr1 GT nm Hcons) (HOp1 GT nm Hcons)

/-! ## §4 nextpid (4 bytes) -/

/-- `lw nextpid`: the handle `RNp e` at a lob-predecessor ⇒ the VALUE handle at the read (value =
the pinned read word `w8`) and the SOURCE fact, both deposited at the read. -/
theorem wpdNpLwX (GT : GdexecT) (nm : Xv6N) (cpu : CPU) (Hcons : rvwmoCatConsistent (gtAdGd GT))
    (i : Agent) (k : Nat) (KK : Result (BitVec (8 * 4) × Option Bool) Arch.abort → SailM Unit)
    (ts : List Nat) (w8 : BitVec 32) (e : Geid) (Φ : Athread → IProp GF) :
    k ≠ (AxOpsem.grow (gtAdGd GT) i).length →
    (AxOpsem.grow (gtAdGd GT) i)[k]? =
      some (.LLoad false (paZ nppa) ts (WeakInterpProj.wbytes 4 w8)) →
    e ∈ @Axpol.lobp (xv6Pol GT) (gtAdGd GT) (i, k) →
    (∀ w a v', a ∈ npb Lx → gwritesByte (gtAdGd GT).gdG w a v' →
      WeakRvwmoGraph.gpo (gtAdGd GT).gdG w (i, k) → gmoLt (gtAdGd GT).gdG w (i, k)) →
    ⊢ AxAnnot.annotOwn e (RNP e) -∗
      (AxAnnot.annotOwn (i, k) (NPh Lx GT nm (i, k) w8) -∗
        AxAnnot.annotOwn (i, k) iprop(⌜npSrc (gtAdGd GT).gdG Lx (i, k) e⌝) -∗
        ∀ rs : RegFile, TW i Φ ⟨hp cpu (KK (.Ok (w8, none))) rs, k + 1⟩) -∗
      ∀ rs : RegFile,
        TW i Φ ⟨hp cpu (.impure (.ok (.memRead 4 64 (rreqn 4 l3pAkP nppa))) KK) rs, k⟩ := by
  intro Hne Hrow Hin Hpo
  have Hl : gxLbl (gtAdGd GT).gdG (i, k) =
      some (.LLoad false (paZ nppa) ts (WeakInterpProj.wbytes 4 w8)) := by
    rw [gxLblGrow]; exact Hrow
  have Hadv := advLoad (gtAdGd GT) i k false (paZ nppa) ts (WeakInterpProj.wbytes 4 w8) Hrow
  have H := nshRead (hlc := hlc) (pol := xv6Pol GT) (gtAdGd GT) Xv6N Unit (protXv6 Lx) nm cpu i
    Φ 4 (by decide) nppa nppaRam KK k Hne Hadv
    iprop(AxAnnot.annotOwn e (RNP e) ∗
      (AxAnnot.annotOwn (i, k) (NPh Lx GT nm (i, k) w8) -∗
        AxAnnot.annotOwn (i, k) iprop(⌜npSrc (gtAdGd GT).gdG Lx (i, k) e⌝) -∗
        ∀ rs : RegFile, TW i Φ ⟨hp cpu (KK (.Ok (w8, none))) rs, k + 1⟩))
    (fun vs rs Hgv => by
      have Hv : vs = WeakInterpProj.wbytes 4 w8 := by
        have Hgv' := Hgv
        unfold graphValue at Hgv'
        rw [Hl] at Hgv'
        simp only [Option.bind_some, lblValue, Option.some.injEq] at Hgv'
        exact Hgv'.symm
      subst Hv
      rw [wordOfBytesWbytes]
      have Hsing : ⊢ ([∗map] Rin ∈ ({[e := RNP e]} : Mea GF), Rin) -∗ iprop(True ∗ RNP e) := by
        iintro H
        ihave H := (BigSepM.bigSepM_singleton (M := GMapF Geid)).1 $$ H
        isplitr
        · itrivial
        · iexact H
      iintro ⟨He, HΨ⟩
      ihave Hw := Hsing
      ihave Hfe := (fxuNpRead (hlc := hlc) Lx GT nm LxOk Hcons (i, k) e ts w8 iprop(True)
        ({[e := RNP e]} : Mea GF) Hl (uxPolGmo GT e (i, k) Hin) Hpo) $$ Hw
      iapply (evDraw (hlc := hlc) (pol := xv6Pol GT) (gtAdGd GT) Xv6N Unit (protXv6 Lx) nm
        (xv6AxpolWf GT) i k e _ (NPh Lx GT nm (i, k) w8)
        iprop(⌜npSrc (gtAdGd GT).gdG Lx (i, k) e⌝) _ _ Hgv Hin) $$ He [Hfe]
      · iapply (@flowEqDynMono hlc GF _ (AxSpinX2.xG Lx GT nm) (xv6Pol GT) (gtAdGd GT) (i, k) _ _
          iprop(True ∗ NPh Lx GT nm (i, k) w8 ∗ ⌜npSrc (gtAdGd GT).gdG Lx (i, k) e⌝)
          iprop(NPh Lx GT nm (i, k) w8 ∗ ⌜npSrc (gtAdGd GT).gdG Lx (i, k) e⌝)) $$ [] Hfe
        inext
        iintro ⟨-, H1, H2⟩
        isplitl [H1]
        · iexact H1
        · iexact H2
      iintro H1 H2
      iapply HΨ $$ H1 H2 %rs)
  iintro He HΨ
  iapply H $$ [$He $HΨ]

/-- `sw nextpid ← w8+1` from a VALUE handle at a lob-predecessor: `RNp` at the store, the
minted fragment (value = the read word) deposited beside it. -/
theorem wpdNpSwX (GT : GdexecT) (nm : Xv6N) (cpu : CPU) (Hcons : rvwmoCatConsistent (gtAdGd GT))
    (i : Agent) (k : Nat) (w8 : BitVec 32) (m' : SailM Unit) (cls : WmClass) (e : Geid)
    (Φ : Athread → IProp GF) :
    k ≠ (AxOpsem.grow (gtAdGd GT) i).length →
    (AxOpsem.grow (gtAdGd GT) i)[k]? =
      some (.LStore false (paZ nppa) (WeakInterpProj.wbytes 4 (w8 + one32)) cls) →
    w8.toNat + 1 < 2 ^ 32 → e ∈ @Axpol.lobp (xv6Pol GT) (gtAdGd GT) (i, k) →
    ⊢ AxAnnot.annotOwn e (NPh Lx GT nm e w8) -∗
      (AxAnnot.annotOwn (i, k) (RNP (i, k)) -∗ AxAnnot.annotOwn (i, k) (FRAG nm w8) -∗
        ∀ rs : RegFile, TW i Φ ⟨hp cpu m' rs, k + 1⟩) -∗
      ∀ rs : RegFile, TW i Φ ⟨hp cpu (stv 4 nppa (w8 + one32) m') rs, k⟩ := by
  intro Hne Hrow Hnwr Hin
  have Hl : gxLbl (gtAdGd GT).gdG (i, k) =
      some (.LStore false (paZ nppa) (WeakInterpProj.wbytes 4 (w8 + one32)) cls) := by
    rw [gxLblGrow]; exact Hrow
  have H := nshWrite (hlc := hlc) (pol := xv6Pol GT) (gtAdGd GT) Xv6N Unit (protXv6 Lx) nm cpu i
    Φ 4 nppa nppaRam (w8 + one32 : BitVec 32) m' k Hne
    iprop(AxAnnot.annotOwn e (NPh Lx GT nm e w8) ∗
      (AxAnnot.annotOwn (i, k) (RNP (i, k)) -∗ AxAnnot.annotOwn (i, k) (FRAG nm w8) -∗
        ∀ rs : RegFile, TW i Φ ⟨hp cpu m' rs, k + 1⟩))
    (fun rs => by
      have Hval : graphData (gtAdGd GT) (i, k) =
          some (WeakInterpProj.wbytes 4 (w8 + one32 : BitVec 32)) := by
        unfold graphData; rw [Hl]; rfl
      have Hsing : ⊢ ([∗map] Rin ∈ ({[e := NPh Lx GT nm e w8]} : Mea GF), Rin) -∗
          iprop(True ∗ NPh Lx GT nm e w8) := by
        iintro H
        ihave H := (BigSepM.bigSepM_singleton (M := GMapF Geid)).1 $$ H
        isplitr
        · itrivial
        · iexact H
      iintro ⟨He, HΨ⟩
      ihave Hw := Hsing
      ihave Hfe := (fxuNpIncr (hlc := hlc) Lx GT nm LxOk Hcons (i, k) e w8 cls iprop(True)
        ({[e := NPh Lx GT nm e w8]} : Mea GF) Hl (uxPolGmo GT e (i, k) Hin) Hnwr) $$ Hw
      iapply (evDraw (hlc := hlc) (pol := xv6Pol GT) (gtAdGd GT) Xv6N Unit (protXv6 Lx) nm
        (xv6AxpolWf GT) i k e _ (RNP (i, k)) (FRAG nm w8) _ _ Hval Hin) $$ He [Hfe]
      · iapply (@flowEqDynMono hlc GF _ (AxSpinX2.xG Lx GT nm) (xv6Pol GT) (gtAdGd GT) (i, k) _ _
          iprop(True ∗ RNP (i, k) ∗ FRAG nm w8) iprop(RNP (i, k) ∗ FRAG nm w8)) $$ [] Hfe
        inext
        iintro ⟨-, H1, H2⟩
        isplitl [H1]
        · iexact H1
        · iexact H2
      iintro H1 H2
      iapply HΨ $$ H1 H2 %rs)
  iintro He HΨ
  iapply H $$ [$He $HΨ]

/-! ## §4 lk->cpu (8 bytes) -/

/-- The holder's `sd lk->cpu ← val`, `val` = its own cpu pointer or 0 (Φ_cpu from the value);
the handle (with any frame `Q`) moves to the store. -/
theorem wpdCpuSdX (GT : GdexecT) (nm : Xv6N) (cpu : CPU) (Hcons : rvwmoCatConsistent (gtAdGd GT))
    (i : Agent) (k : Nat) (val : BitVec 64) (m' : SailM Unit) (cls : WmClass) (e : Geid)
    (Q : IProp GF) (Φ : Athread → IProp GF) :
    k ≠ (AxOpsem.grow (gtAdGd GT) i).length →
    (AxOpsem.grow (gtAdGd GT) i)[k]? =
      some (.LStore false (paZ lcpa) (WeakInterpProj.wbytes 8 val) cls) →
    (val = cpuAddr (cpuOf i) ∨ val = zero64) → e ∈ @Axpol.lobp (xv6Pol GT) (gtAdGd GT) (i, k) →
    ⊢ AxAnnot.annotOwn e iprop(Q ∗ RCPU e) -∗
      (AxAnnot.annotOwn (i, k)
          iprop(Q ∗ RVL nm.xnH (gtAdGd GT) (clb Lx) (i, k) (WeakInterpProj.wbytes 8 val)) -∗
        ∀ rs : RegFile, TW i Φ ⟨hp cpu m' rs, k + 1⟩) -∗
      ∀ rs : RegFile, TW i Φ ⟨hp cpu (stv 8 lcpa val m') rs, k⟩ := by
  intro Hne Hrow Hv Hin
  have Hl : gxLbl (gtAdGd GT).gdG (i, k) =
      some (.LStore false (paZ lcpa) (WeakInterpProj.wbytes 8 val) cls) := by
    rw [gxLblGrow]; exact Hrow
  have H := nshWrite (hlc := hlc) (pol := xv6Pol GT) (gtAdGd GT) Xv6N Unit (protXv6 Lx) nm cpu i
    Φ 8 lcpa lcpaRam val m' k Hne
    iprop(AxAnnot.annotOwn e iprop(Q ∗ RCPU e) ∗
      (AxAnnot.annotOwn (i, k)
          iprop(Q ∗ RVL nm.xnH (gtAdGd GT) (clb Lx) (i, k) (WeakInterpProj.wbytes 8 val)) -∗
        ∀ rs : RegFile, TW i Φ ⟨hp cpu m' rs, k + 1⟩))
    (fun rs => by
      have Hval : graphData (gtAdGd GT) (i, k) = some (WeakInterpProj.wbytes 8 val) := by
        unfold graphData; rw [Hl]; rfl
      obtain ⟨Hw, Hsg⟩ := gwbStoren _ _ _ _ _ Hl
      have Hisw : gisW (gtAdGd GT).gdG (i, k) = true := by unfold gisW; rw [Hl]; rfl
      have Hv' : WeakInterpProj.wbytes 8 val = cvx ((i, k) : Geid).1 ∨
          WeakInterpProj.wbytes 8 val = List.replicate 8 b0 := by
        rcases Hv with rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr zero64Bytes
      have Hwr : ∀ (j : Nat) a v, (clb Lx)[j]? = some a →
          (WeakInterpProj.wbytes 8 val)[j]? = some v → gwritesByte (gtAdGd GT).gdG (i, k) a v := by
        intro j a v Hj Hv
        rw [clbLcpa] at Hj
        obtain ⟨rfl, -⟩ := AxSpinX4.clRangeLookup _ _ _ _ Hj
        exact Hw j v Hv
      have Hsg' : ∀ a v, gwritesByte (gtAdGd GT).gdG (i, k) a v → a ∈ clb Lx := by
        intro a v Hw'
        obtain ⟨j, Hj, rfl⟩ := Hsg a v Hw'
        have hj := (List.getElem?_eq_some_iff.1 Hj).1
        rw [wbytesLength] at hj
        rw [clbLx]
        simp only [lkZV, lcZV]
        omega
      have Hw0 : ⊢ ([∗map] Rin ∈ ({[e := iprop(Q ∗ RCPU e)]} : Mea GF), Rin) -∗
          iprop(Q ∗ ∃ vold, RVL nm.xnH (gtAdGd GT) (clb Lx) e vold) := by
        iintro H
        ihave H := (BigSepM.bigSepM_singleton (M := GMapF Geid)).1 $$ H
        icases H with ⟨HQ, HC⟩
        isplitl [HQ]
        · iexact HQ
        · iunfold RCpu at HC
          iexact HC
      iintro ⟨He, HΨ⟩
      ihave Hw := Hw0
      ihave Hfe := (fxCpuWrite (hlc := hlc) Lx GT nm LxOk Hcons (i, k) e
        (WeakInterpProj.wbytes 8 val) Q ({[e := iprop(Q ∗ RCPU e)]} : Mea GF) Hisw
        (uxPolGmo GT e (i, k) Hin) Hv' Hwr Hsg') $$ Hw
      iapply (evDraw (hlc := hlc) (pol := xv6Pol GT) (gtAdGd GT) Xv6N Unit (protXv6 Lx) nm
        (xv6AxpolWf GT) i k e _
        iprop(Q ∗ RVL nm.xnH (gtAdGd GT) (clb Lx) (i, k) (WeakInterpProj.wbytes 8 val))
        iprop(True) _ _ Hval Hin) $$ He [Hfe]
      · iapply (@flowEqDynMono hlc GF _ (AxSpinX2.xG Lx GT nm) (xv6Pol GT) (gtAdGd GT) (i, k) _ _
          iprop(Q ∗ RVL nm.xnH (gtAdGd GT) (clb Lx) (i, k) (WeakInterpProj.wbytes 8 val))
          iprop((Q ∗ RVL nm.xnH (gtAdGd GT) (clb Lx) (i, k) (WeakInterpProj.wbytes 8 val)) ∗
            True)) $$ [] Hfe
        inext
        iintro H
        isplitl [H]
        · iexact H
        · itrivial
      iintro H _
      iapply HΨ $$ H %rs)
  iintro He HΨ
  iapply H $$ [$He $HΨ]

/-- The holder's `ld lk->cpu` after its own `sd lk->cpu ← val` at `kw` (no lk->cpu store
po-between): THE gmo SPLIT inside the leaf -- ordered ⇒ owned last-value read (the handle moves
to the read); forwarded ⇒ pure forwarding, nothing drawn.  Deposits `v = val`. -/
theorem wpdCpuReloadX (GT : GdexecT) (nm : Xv6N) (cpu : CPU)
    (Hcons : rvwmoCatConsistent (gtAdGd GT)) (i : Agent) (kw k : Nat)
    (KK : Result (BitVec (8 * 8) × Option Bool) Arch.abort → SailM Unit) (val v : BitVec 64)
    (cls : WmClass) (ts : List Nat) (Q : IProp GF) (Φ : Athread → IProp GF) :
    k ≠ (AxOpsem.grow (gtAdGd GT) i).length →
    (AxOpsem.grow (gtAdGd GT) i)[kw]? =
      some (.LStore false (paZ lcpa) (WeakInterpProj.wbytes 8 val) cls) →
    (AxOpsem.grow (gtAdGd GT) i)[k]? =
      some (.LLoad false (paZ lcpa) ts (WeakInterpProj.wbytes 8 v)) → kw < k →
    (∀ w a v', a ∈ clb Lx → gwritesByte (gtAdGd GT).gdG w a v' →
      WeakRvwmoGraph.gpo (gtAdGd GT).gdG (i, kw) w →
      WeakRvwmoGraph.gpo (gtAdGd GT).gdG w (i, k) → False) →
    ⊢ AxAnnot.annotOwn (i, kw)
        iprop(Q ∗ RVL nm.xnH (gtAdGd GT) (clb Lx) (i, kw) (WeakInterpProj.wbytes 8 val)) -∗
      ((∃ (e' : Geid), ⌜e' = (i, kw) ∨ e' = (i, k)⌝ ∗ AxAnnot.annotOwn e'
          iprop(Q ∗ RVL nm.xnH (gtAdGd GT) (clb Lx) e' (WeakInterpProj.wbytes 8 val))) -∗
        AxAnnot.annotOwn (i, k) iprop(⌜v = val⌝) -∗
        ∀ rs : RegFile, TW i Φ ⟨hp cpu (KK (.Ok (v, none))) rs, k + 1⟩) -∗
      ∀ rs : RegFile,
        TW i Φ ⟨hp cpu (.impure (.ok (.memRead 8 64 (rreqn 8 l3pAkP lcpa))) KK) rs, k⟩ := by
  intro Hne Hroww Hrow Hlt Hnoint
  have Hlw : gxLbl (gtAdGd GT).gdG (i, kw) =
      some (.LStore false (paZ lcpa) (WeakInterpProj.wbytes 8 val) cls) := by
    rw [gxLblGrow]; exact Hroww
  have Hl : gxLbl (gtAdGd GT).gdG (i, k) =
      some (.LLoad false (paZ lcpa) ts (WeakInterpProj.wbytes 8 v)) := by
    rw [gxLblGrow]; exact Hrow
  have Hwf := Hcons.1
  have Hpo : WeakRvwmoGraph.gpo (gtAdGd GT).gdG (i, kw) (i, k) :=
    gpoRow (gtAdGd GT) i kw k _ _ Hlw Hl Hlt
  obtain ⟨Hww, -⟩ := gwbStoren _ _ _ _ _ Hlw
  have Hcw : ∀ (j : Nat) a b, (clb Lx)[j]? = some a →
      (WeakInterpProj.wbytes 8 val)[j]? = some b → gwritesByte (gtAdGd GT).gdG (i, kw) a b := by
    intro j a b Hj Hb
    rw [clbLcpa] at Hj
    obtain ⟨rfl, -⟩ := AxSpinX4.clRangeLookup _ _ _ _ Hj
    exact Hww j b Hb
  have Hrf : (∀ (j : Nat) a t b, (clb Lx)[j]? = some a →
      greadsByte (gtAdGd GT).gdG (i, k) a t b → (WeakInterpProj.wbytes 8 val)[j]? = some b) →
      v = val := by
    intro Hf
    apply wbytes8Inj'
    exact readFactWord (gtAdGd GT).gdG Hwf (i, k) (paZ lcpa) ts 8 v _ Hl (wbytesLength 8 _)
      (fun j a t b Hj Hrd => Hf j a t b (by rw [clbLcpa]; exact Hj) Hrd)
  have Hadv := advLoad (gtAdGd GT) i k false (paZ lcpa) ts (WeakInterpProj.wbytes 8 v) Hrow
  have H := nshRead (hlc := hlc) (pol := xv6Pol GT) (gtAdGd GT) Xv6N Unit (protXv6 Lx) nm cpu i
    Φ 8 (by decide) lcpa lcpaRam KK k Hne Hadv
    iprop(AxAnnot.annotOwn (i, kw)
        iprop(Q ∗ RVL nm.xnH (gtAdGd GT) (clb Lx) (i, kw) (WeakInterpProj.wbytes 8 val)) ∗
      ((∃ (e' : Geid), ⌜e' = (i, kw) ∨ e' = (i, k)⌝ ∗ AxAnnot.annotOwn e'
          iprop(Q ∗ RVL nm.xnH (gtAdGd GT) (clb Lx) e' (WeakInterpProj.wbytes 8 val))) -∗
        AxAnnot.annotOwn (i, k) iprop(⌜v = val⌝) -∗
        ∀ rs : RegFile, TW i Φ ⟨hp cpu (KK (.Ok (v, none))) rs, k + 1⟩))
    (fun vs rs Hgv => by
      have Hvs : vs = WeakInterpProj.wbytes 8 v := by
        have Hgv' := Hgv
        unfold graphValue at Hgv'
        rw [Hl] at Hgv'
        simp only [Option.bind_some, lblValue, Option.some.injEq] at Hgv'
        exact Hgv'.symm
      subst Hvs
      rw [wordOfBytesWbytes]
      have Hnw : gisW (gtAdGd GT).gdG (i, k) = false := by unfold gisW; rw [Hl]; rfl
      by_cases Hb : gmoLt (gtAdGd GT).gdG (i, kw) (i, k)
      · have Hin : ((i, kw) : Geid) ∈ @Axpol.lobp (xv6Pol GT) (gtAdGd GT) (i, k) :=
          uxPolIntro GT (i, kw) (i, k) _ Hlw rfl Hpo Hb
        have Hlast : ∀ w a v', a ∈ clb Lx → gwritesByte (gtAdGd GT).gdG w a v' →
            WeakRvwmoGraph.gpo (gtAdGd GT).gdG w (i, k) → gmoLt (gtAdGd GT).gdG w (i, k) := by
          intro w a v' Ha Hw' Hpo'
          have Ha' : a ∈ clRange (paZ lcpa) (WeakInterpProj.wbytes 8 val).length := by
            rw [wbytesLength, ← clbLcpa]
            exact Ha
          exact poWritesGmoBeforeN (gtAdGd GT) Hcons i kw k (paZ lcpa)
            (WeakInterpProj.wbytes 8 val) cls a Hlw Ha'
            (fun w'' v'' Hw'' H1 H2 => Hnoint w'' a v'' Ha Hw'' H1 H2) Hb w v' Hw' Hpo'
        have Hsing : ⊢ ([∗map] Rin ∈ ({[((i, kw) : Geid) :=
            iprop(Q ∗ RVL nm.xnH (gtAdGd GT) (clb Lx) (i, kw) (WeakInterpProj.wbytes 8 val))]} :
              Mea GF), Rin) -∗
            iprop(Q ∗ RVL nm.xnH (gtAdGd GT) (clb Lx) (i, kw) (WeakInterpProj.wbytes 8 val)) := by
          iintro H
          iapply (BigSepM.bigSepM_singleton (M := GMapF Geid)).1 $$ H
        iintro ⟨Hw, HΨ⟩
        ihave Hs := Hsing
        ihave Hfe := (fxOwnedRead (hlc := hlc) Lx GT nm LxOk Hcons (i, k) (i, kw) (clb Lx)
          (WeakInterpProj.wbytes 8 val) Q ({[((i, kw) : Geid) :=
            iprop(Q ∗ RVL nm.xnH (gtAdGd GT) (clb Lx) (i, kw) (WeakInterpProj.wbytes 8 val))]} :
              Mea GF) Hnw (fun a Ha => clbXO Lx a Ha) Hb Hlast) $$ Hs
        ihave Hfe := (@flowEqDynMono hlc GF _ (AxSpinX2.xG Lx GT nm) (xv6Pol GT) (gtAdGd GT)
          (i, k) _ _
          iprop((Q ∗ RVL nm.xnH (gtAdGd GT) (clb Lx) (i, kw) (WeakInterpProj.wbytes 8 val)) ∗
            ⌜∀ (j : Nat) a t b, (clb Lx)[j]? = some a →
              greadsByte (gtAdGd GT).gdG (i, k) a t b →
              (WeakInterpProj.wbytes 8 val)[j]? = some b⌝)
          iprop((Q ∗ RVL nm.xnH (gtAdGd GT) (clb Lx) (i, k) (WeakInterpProj.wbytes 8 val)) ∗
            ⌜v = val⌝)) $$ [] Hfe
        · inext
          iintro ⟨⟨HQ, HR⟩, %Hf⟩
          isplitl [HQ HR]
          · isplitl [HQ]
            · iexact HQ
            · iapply (RVLRetie nm.xnH (gtAdGd GT) (clb Lx) (i, kw) (i, k) _ Hb) $$ HR
          · ipureintro
            exact Hrf Hf
        iapply (evDraw (hlc := hlc) (pol := xv6Pol GT) (gtAdGd GT) Xv6N Unit (protXv6 Lx) nm
          (xv6AxpolWf GT) i k (i, kw) _
          iprop(Q ∗ RVL nm.xnH (gtAdGd GT) (clb Lx) (i, k) (WeakInterpProj.wbytes 8 val))
          iprop(⌜v = val⌝) _ _ Hgv Hin) $$ Hw Hfe
        iintro H1 H2
        iapply HΨ $$ [H1] H2 %rs
        iexists (i, k)
        isplitr
        · ipureintro
          exact Or.inr rfl
        · iexact H1
      · have Hlen : (WeakInterpProj.wbytes 8 val).length = (clb Lx).length := by
          rw [wbytesLength]
          simp [clb, clRange]
        iintro ⟨Hw, HΨ⟩
        ihave Hfe := fxFwdRead (hlc := hlc) (GF := GF) Lx GT nm LxOk Hcons (i, k) (i, kw)
          (clb Lx) (WeakInterpProj.wbytes 8 val) Hnw Hpo Hb Hcw Hlen Hnoint
        ihave Hfe := (@flowEqDynMono hlc GF _ (AxSpinX2.xG Lx GT nm) (xv6Pol GT) (gtAdGd GT)
          (i, k) _ (∅ : Mea GF)
          iprop(⌜∀ (j : Nat) a t b, (clb Lx)[j]? = some a →
              greadsByte (gtAdGd GT).gdG (i, k) a t b →
              (WeakInterpProj.wbytes 8 val)[j]? = some b⌝)
          iprop(⌜v = val⌝ ∗ True)) $$ [] Hfe
        · inext
          iintro %Hf
          isplitr
          · ipureintro
            exact Hrf Hf
          · itrivial
        iapply (evPlain (hlc := hlc) (pol := xv6Pol GT) (gtAdGd GT) Xv6N Unit (protXv6 Lx) nm i k
          iprop(⌜v = val⌝) iprop(True) _ _ Hgv) $$ Hfe
        iintro H _
        iapply HΨ $$ [Hw] H %rs
        iexists (i, kw)
        isplitr
        · ipureintro
          exact Or.inl rfl
        · iexact Hw)
  iintro Hw HΨ
  iapply H $$ [$Hw $HΨ]

/-- The NON-holder's racy `ld lk->cpu`: deposits `v ≠ cpuAddr (cpuOf i)` (Φ_cpu from σ at the
8-byte single source; graph premises: aligned lk->cpu writes, image 0, value table injective at
`i`, no po-earlier lk->cpu store by `i`). -/
theorem wpdCpuRacyX (GT : GdexecT) (nm : Xv6N) (cpu : CPU) (Hcons : rvwmoCatConsistent (gtAdGd GT))
    (i : Agent) (k : Nat) (KK : Result (BitVec (8 * 8) × Option Bool) Arch.abort → SailM Unit)
    (v : BitVec 64) (ts : List Nat) (Φ : Athread → IProp GF) :
    k ≠ (AxOpsem.grow (gtAdGd GT) i).length →
    (AxOpsem.grow (gtAdGd GT) i)[k]? =
      some (.LLoad false (paZ lcpa) ts (WeakInterpProj.wbytes 8 v)) →
    clAligned (clb Lx) (gtAdGd GT).gdG → (∀ a, a ∈ clb Lx → (gtAdGd GT).gdG.gxImg a = some b0) →
    (∀ k', k' ≠ i → cvx k' ≠ cvx i) →
    (∀ w a v', a ∈ clb Lx → gwritesByte (gtAdGd GT).gdG w a v' →
      WeakRvwmoGraph.gpo (gtAdGd GT).gdG w (i, k) → False) →
    ⊢ (AxAnnot.annotOwn (i, k) iprop(⌜v ≠ cpuAddr (cpuOf i)⌝) -∗
        ∀ rs : RegFile, TW i Φ ⟨hp cpu (KK (.Ok (v, none))) rs, k + 1⟩) -∗
      ∀ rs : RegFile,
        TW i Φ ⟨hp cpu (.impure (.ok (.memRead 8 64 (rreqn 8 l3pAkP lcpa))) KK) rs, k⟩ := by
  intro Hne Hrow Hal Himgc Hinj Hns
  have Hl : gxLbl (gtAdGd GT).gdG (i, k) =
      some (.LLoad false (paZ lcpa) ts (WeakInterpProj.wbytes 8 v)) := by
    rw [gxLblGrow]; exact Hrow
  have Hwf := Hcons.1
  have Hppo := Hcons.2.1
  have Hlv := Hcons.2.2.1
  have Hppo1 : ∀ e1 e2, gppo1 (gtAdGd GT).gdG e1 e2 → gmoLt (gtAdGd GT).gdG e1 e2 :=
    fun e1 e2 H => Hppo e1 e2 (.inl (.inl H))
  have Hcl8 : (clb Lx).length = 8 := by simp [clb, clRange]
  have Hcvl : ∀ k', (cvx k').length = (clb Lx).length := by
    intro k'
    rw [cvxLength, Hcl8]
  have Hrd : ∀ (j : Nat) a, (clb Lx)[j]? = some a →
      ∃ t b, greadsByte (gtAdGd GT).gdG (i, k) a t b ∧
        (WeakInterpProj.wbytes 8 v)[j]? = some b := by
    intro j a Hj
    rw [clbLcpa] at Hj
    obtain ⟨rfl, Hjl⟩ := AxSpinX4.clRangeLookup _ _ _ _ Hj
    obtain ⟨t, Ht⟩ := loadnReads (gtAdGd GT).gdG Hwf (i, k) (paZ lcpa) ts 8 v j Hl Hjl
    exact ⟨t, _, Ht, wbytesLookup 8 (m := 8) v j Hjl⟩
  have Hnz : cvx ((i, k) : Geid).1 ≠ List.replicate (clb Lx).length b0 := by
    rw [Hcl8]
    exact cvxNz i
  have Hfact : rdFact (clb Lx) cvx (gtAdGd GT).gdG (i, k) → v ≠ cpuAddr (cpuOf i) := by
    intro HF Hv
    apply cpuReadNotMine (clb Lx) cvx (gtAdGd GT).gdG (i, k) (WeakInterpProj.wbytes 8 v) Hwf Hlv
      Hppo1 Hal Hcvl (by rw [wbytesLength, Hcl8]) Hrd Himgc Hnz Hinj Hns HF
    rw [Hv]
    rfl
  have Hadv := advLoad (gtAdGd GT) i k false (paZ lcpa) ts (WeakInterpProj.wbytes 8 v) Hrow
  have H := nshRead (hlc := hlc) (pol := xv6Pol GT) (gtAdGd GT) Xv6N Unit (protXv6 Lx) nm cpu i
    Φ 8 (by decide) lcpa lcpaRam KK k Hne Hadv
    iprop(AxAnnot.annotOwn (i, k) iprop(⌜v ≠ cpuAddr (cpuOf i)⌝) -∗
      ∀ rs : RegFile, TW i Φ ⟨hp cpu (KK (.Ok (v, none))) rs, k + 1⟩)
    (fun vs rs Hgv => by
      have Hvs : vs = WeakInterpProj.wbytes 8 v := by
        have Hgv' := Hgv
        unfold graphValue at Hgv'
        rw [Hl] at Hgv'
        simp only [Option.bind_some, lblValue, Option.some.injEq] at Hgv'
        exact Hgv'.symm
      subst Hvs
      rw [wordOfBytesWbytes]
      have Hnw : gisW (gtAdGd GT).gdG (i, k) = false := by unfold gisW; rw [Hl]; rfl
      iintro HΨ
      ihave Hfe := fxCpuRacy (hlc := hlc) (GF := GF) Lx GT nm LxOk Hcons (i, k) Hnw
      iapply (evPlain (hlc := hlc) (pol := xv6Pol GT) (gtAdGd GT) Xv6N Unit (protXv6 Lx) nm i k
        iprop(⌜v ≠ cpuAddr (cpuOf i)⌝) iprop(True) _ _ Hgv) $$ [Hfe]
      · iapply (@flowEqDynMono hlc GF _ (AxSpinX2.xG Lx GT nm) (xv6Pol GT) (gtAdGd GT) (i, k) _
          (∅ : Mea GF) iprop(⌜rdFact (clb Lx) cvx (gtAdGd GT).gdG (i, k)⌝)
          iprop(⌜v ≠ cpuAddr (cpuOf i)⌝ ∗ True)) $$ [] Hfe
        inext
        iintro %HF
        isplitr
        · ipureintro
          exact Hfact HF
        · itrivial
      iintro H _
      iapply HΨ $$ H %rs)
  iintro HΨ
  iapply H $$ HΨ

/-! ## §5 lock contracts at real width -/

theorem lkClaimOf (GT : GdexecT) (i : Agent) (k t : Nat) :
    gxLbl (gtAdGd GT).gdG (i, k) =
      some (.LRmw true false (paZ lkpa) [t, t, t, t] AxSpinX4.z4 AxSpinX4.o4 .WCplain) →
    lkClaim Lx.xlLk (gtAdGd GT).gdG (i, k) (gwriteAt (gtAdGd GT).gdG t) ∧
      (∀ a v', gwritesByte (gtAdGd GT).gdG (i, k) a v' → a ∈ lwb Lx) := by
  intro Hl
  obtain ⟨Hr, Hw, Hsg, -⟩ := gwbRmwn _ _ _ _ _ _ _ Hl
  refine ⟨⟨t, ?_, rfl, ?_⟩, ?_⟩
  · have H := Hr 0 t b0 rfl (by decide +kernel)
    rw [AxSpinX5.addZero] at H
    exact H
  · have H := Hw 0 b1 (by decide +kernel)
    rw [AxSpinX5.addZero] at H
    exact H
  · intro a v' Hw'
    obtain ⟨j, Hj, rfl⟩ := Hsg a v' Hw'
    have hj := (List.getElem?_eq_some_iff.1 Hj).1
    simp only [AxSpinX4.o4, wbytesLength] at hj
    exact (lwbLx _).2 ⟨by omega, by omega⟩

/-- ACQUIRE (success), `notheld` in hand, the claim's annotation allocated pre-split along
`Hsplit`. -/
theorem wpdAcquireX (GT : GdexecT) (nm : Xv6N) (cpu : CPU) (Hcons : rvwmoCatConsistent (gtAdGd GT))
    (i : Agent) (k t : Nat) (kok kf : SailM Unit) (R1 R2 : IProp GF) (Φ : Athread → IProp GF) :
    k ≠ (AxOpsem.grow (gtAdGd GT) i).length →
    (AxOpsem.grow (gtAdGd GT) i)[k]? =
      some (.LRmw true false (paZ lkpa) [t, t, t, t] AxSpinX4.z4 AxSpinX4.o4 .WCplain) →
    (iprop(LK i (i, k) ∗ RP (i, k)) ⊢ iprop(R1 ∗ R2)) →
    ⊢ ISL -∗ NH i -∗
      (⌜lkClaim Lx.xlLk (gtAdGd GT).gdG (i, k) (gwriteAt (gtAdGd GT).gdG t)⌝ -∗
        AxAnnot.annotOwn (i, k) R1 -∗ AxAnnot.annotOwn (i, k) R2 -∗
        ∀ rs : RegFile, TW i Φ ⟨hp cpu kok rs, k + 1⟩) -∗
      ∀ rs : RegFile, TW i Φ ⟨hp cpu (AxSpinX4.acq4 kok kf) rs, k⟩ := by
  intro Hne Hrow Hsplit
  have Hl : gxLbl (gtAdGd GT).gdG (i, k) =
      some (.LRmw true false (paZ lkpa) [t, t, t, t] AxSpinX4.z4 AxSpinX4.o4 .WCplain) := by
    rw [gxLblGrow]; exact Hrow
  obtain ⟨Hcl, Hlw⟩ := lkClaimOf GT i k t Hl
  have Hval : graphData (gtAdGd GT) (i, k) = some (WeakInterpProj.wbytes 4 one32) := by
    unfold graphData; rw [Hl]; rfl
  have Hs : ⊢ iprop(locked (GF := GF) nm.xnReg Lx.xlLk ((i, k) : Geid).1 (i, k) ∗ RP (i, k)) -∗
      iprop(R1 ∗ R2) :=
    BI.wand_intro (BI.emp_sep.1.trans Hsplit)
  have HW := nshRmwWrite (hlc := hlc) (pol := xv6Pol GT) (gtAdGd GT) Xv6N Unit (protXv6 Lx) nm cpu
    i Φ 4 lkpa lkpaRam one32 (if zero32 = zero32 then kok else kf) k Hne
    iprop(ISL ∗ NH i ∗
      (⌜lkClaim Lx.xlLk (gtAdGd GT).gdG (i, k) (gwriteAt (gtAdGd GT).gdG t)⌝ -∗
        AxAnnot.annotOwn (i, k) R1 -∗ AxAnnot.annotOwn (i, k) R2 -∗
        ∀ rs : RegFile, TW i Φ ⟨hp cpu kok rs, k + 1⟩))
    (fun rs => by
      iintro ⟨#Hil, Hnh, HΨ⟩
      ihave Hfe := (fxClaim (hlc := hlc) Lx GT nm LxOk Hcons (i, k) (gwriteAt (gtAdGd GT).gdG t)
        Hcl Hlw) $$ Hnh Hil
      iapply (evPlain (hlc := hlc) (pol := xv6Pol GT) (gtAdGd GT) Xv6N Unit (protXv6 Lx) nm i k
        R1 R2 _ _ Hval) $$ [Hfe]
      · iapply (@flowEqDynMono hlc GF _ (AxSpinX2.xG Lx GT nm) (xv6Pol GT) (gtAdGd GT) (i, k) _
          (∅ : Mea GF)
          iprop(locked nm.xnReg Lx.xlLk ((i, k) : Geid).1 (i, k) ∗
            RPid Lx nm.xnH nm.xnM nm.xnI (gtAdGd GT) (i, k))
          iprop(R1 ∗ R2)) $$ [] Hfe
        inext
        ihave H := Hs
        iexact H
      iintro H1 H2
      rw [amoClaimNext]
      iapply HΨ $$ %Hcl H1 H2 %rs)
  have HR := nshRmwRead (hlc := hlc) (pol := xv6Pol GT) (gtAdGd GT) Xv6N Unit (protXv6 Lx) nm cpu
    i Φ 4 (by decide) lkpa lkpaRam (amoK kok kf) k [t, t, t, t] AxSpinX4.z4 AxSpinX4.o4 .WCplain
    Hne Hrow
    iprop(ISL ∗ NH i ∗
      (⌜lkClaim Lx.xlLk (gtAdGd GT).gdG (i, k) (gwriteAt (gtAdGd GT).gdG t)⌝ -∗
        AxAnnot.annotOwn (i, k) R1 -∗ AxAnnot.annotOwn (i, k) R2 -∗
        ∀ rs : RegFile, TW i Φ ⟨hp cpu kok rs, k + 1⟩))
    (fun rs => by
      iintro ⟨#Hil, Hnh, HΨ⟩
      rw [acqAfterClaim]
      iapply HW $$ [$Hil $Hnh $HΨ] %rs)
  iintro #Hil Hnh HΨ
  iapply HR $$ [$Hil $Hnh $HΨ]

/-- RE-ACQUIRE: `notheld` drawn from the hart's own earlier release annotation (ppo rule 1:
`sw lk` → later RMW on `lk`). -/
theorem wpdReacquireX (GT : GdexecT) (nm : Xv6N) (cpu : CPU)
    (Hcons : rvwmoCatConsistent (gtAdGd GT)) (i : Agent) (kw k t : Nat) (kok kf : SailM Unit)
    (R1 R2 : IProp GF) (Φ : Athread → IProp GF) :
    k ≠ (AxOpsem.grow (gtAdGd GT) i).length →
    (AxOpsem.grow (gtAdGd GT) i)[kw]? = some (.LStore false (paZ lkpa) AxSpinX4.z4 .WCrel) →
    kw < k →
    (AxOpsem.grow (gtAdGd GT) i)[k]? =
      some (.LRmw true false (paZ lkpa) [t, t, t, t] AxSpinX4.z4 AxSpinX4.o4 .WCplain) →
    (iprop(LK i (i, k) ∗ RP (i, k)) ⊢ iprop(R1 ∗ R2)) →
    ⊢ ISL -∗ AxAnnot.annotOwn (i, kw) (NH i) -∗
      (⌜lkClaim Lx.xlLk (gtAdGd GT).gdG (i, k) (gwriteAt (gtAdGd GT).gdG t)⌝ -∗
        AxAnnot.annotOwn (i, k) R1 -∗ AxAnnot.annotOwn (i, k) R2 -∗
        ∀ rs : RegFile, TW i Φ ⟨hp cpu kok rs, k + 1⟩) -∗
      ∀ rs : RegFile, TW i Φ ⟨hp cpu (AxSpinX4.acq4 kok kf) rs, k⟩ := by
  intro Hne Hroww Hlt Hrow Hsplit
  have Hl : gxLbl (gtAdGd GT).gdG (i, k) =
      some (.LRmw true false (paZ lkpa) [t, t, t, t] AxSpinX4.z4 AxSpinX4.o4 .WCplain) := by
    rw [gxLblGrow]; exact Hrow
  have Hlw : gxLbl (gtAdGd GT).gdG (i, kw) =
      some (.LStore false (paZ lkpa) AxSpinX4.z4 .WCrel) := by
    rw [gxLblGrow]; exact Hroww
  obtain ⟨Hcl, Hlwb⟩ := lkClaimOf GT i k t Hl
  have Hzw : zw Lx.xlLk (gtAdGd GT).gdG (i, kw) := by
    obtain ⟨Hw, -⟩ := gwbStoren _ _ _ _ _ Hlw
    have H := Hw 0 b0 zero32Byte0
    rw [AxSpinX5.addZero] at H
    exact H
  have Hin : ((i, kw) : Geid) ∈ @Axpol.lobp (xv6Pol GT) (gtAdGd GT) (i, k) :=
    relClaimLobp (gtAdGd GT) Hcons Lx.xlLk (i, kw) (i, k) (gwriteAt (gtAdGd GT).gdG t) _ Hlw rfl Hzw
      (gpoRow (gtAdGd GT) i kw k _ _ Hlw Hl Hlt) Hcl
  have Hval : graphData (gtAdGd GT) (i, k) = some (WeakInterpProj.wbytes 4 one32) := by
    unfold graphData; rw [Hl]; rfl
  have Hs : ⊢ iprop((locked (GF := GF) nm.xnReg Lx.xlLk ((i, k) : Geid).1 (i, k) ∗ RP (i, k)) ∗
      True) -∗ iprop(R1 ∗ R2) := by
    have Hs0 : ⊢ iprop(locked (GF := GF) nm.xnReg Lx.xlLk ((i, k) : Geid).1 (i, k) ∗ RP (i, k)) -∗
        iprop(R1 ∗ R2) := BI.wand_intro (BI.emp_sep.1.trans Hsplit)
    iintro ⟨H, -⟩
    ihave Hw := Hs0
    iapply Hw $$ H
  have Hsing : ⊢ ([∗map] Rin ∈ ({[((i, kw) : Geid) := NH i]} : Mea GF), Rin) -∗
      iprop(notheld (GF := GF) nm.xnReg Lx.xlLk ((i, k) : Geid).1 ∗ True) := by
    iintro H
    ihave H := (BigSepM.bigSepM_singleton (M := GMapF Geid)).1 $$ H
    isplitl [H]
    · iexact H
    · itrivial
  have HW := nshRmwWrite (hlc := hlc) (pol := xv6Pol GT) (gtAdGd GT) Xv6N Unit (protXv6 Lx) nm cpu
    i Φ 4 lkpa lkpaRam one32 (if zero32 = zero32 then kok else kf) k Hne
    iprop(ISL ∗ AxAnnot.annotOwn (i, kw) (NH i) ∗
      (⌜lkClaim Lx.xlLk (gtAdGd GT).gdG (i, k) (gwriteAt (gtAdGd GT).gdG t)⌝ -∗
        AxAnnot.annotOwn (i, k) R1 -∗ AxAnnot.annotOwn (i, k) R2 -∗
        ∀ rs : RegFile, TW i Φ ⟨hp cpu kok rs, k + 1⟩))
    (fun rs => by
      iintro ⟨#Hil, Hnh, HΨ⟩
      ihave Hw := Hsing
      ihave Hfe := (fxClaim' (hlc := hlc) Lx GT nm LxOk Hcons (i, k) (gwriteAt (gtAdGd GT).gdG t)
        iprop(True) ({[((i, kw) : Geid) := NH i]} : Mea GF) Hcl Hlwb) $$ Hil Hw
      iapply (evDraw (hlc := hlc) (pol := xv6Pol GT) (gtAdGd GT) Xv6N Unit (protXv6 Lx) nm
        (xv6AxpolWf GT) i k (i, kw) (NH i) R1 R2 _ _ Hval Hin) $$ Hnh [Hfe]
      · iapply (@flowEqDynMono hlc GF _ (AxSpinX2.xG Lx GT nm) (xv6Pol GT) (gtAdGd GT) (i, k) _ _
          iprop((locked nm.xnReg Lx.xlLk ((i, k) : Geid).1 (i, k) ∗
            RPid Lx nm.xnH nm.xnM nm.xnI (gtAdGd GT) (i, k)) ∗ True)
          iprop(R1 ∗ R2)) $$ [] Hfe
        inext
        ihave H := Hs
        iexact H
      iintro H1 H2
      rw [amoClaimNext]
      iapply HΨ $$ %Hcl H1 H2 %rs)
  have HR := nshRmwRead (hlc := hlc) (pol := xv6Pol GT) (gtAdGd GT) Xv6N Unit (protXv6 Lx) nm cpu
    i Φ 4 (by decide) lkpa lkpaRam (amoK kok kf) k [t, t, t, t] AxSpinX4.z4 AxSpinX4.o4 .WCplain
    Hne Hrow
    iprop(ISL ∗ AxAnnot.annotOwn (i, kw) (NH i) ∗
      (⌜lkClaim Lx.xlLk (gtAdGd GT).gdG (i, k) (gwriteAt (gtAdGd GT).gdG t)⌝ -∗
        AxAnnot.annotOwn (i, k) R1 -∗ AxAnnot.annotOwn (i, k) R2 -∗
        ∀ rs : RegFile, TW i Φ ⟨hp cpu kok rs, k + 1⟩))
    (fun rs => by
      iintro ⟨#Hil, Hnh, HΨ⟩
      rw [acqAfterClaim]
      iapply HW $$ [$Hil $Hnh $HΨ] %rs)
  iintro #Hil Hnh HΨ
  iapply HR $$ [$Hil $Hnh $HΨ]

/-- THE FAILED SPIN: the lock word read is nonzero (low byte ≠ 0); the RMW writes 1 (neutral
arm), the frame `P` goes to the retry. -/
theorem wpdAcquireFailX (GT : GdexecT) (nm : Xv6N) (cpu : CPU)
    (Hcons : rvwmoCatConsistent (gtAdGd GT)) (i : Agent) (k t : Nat) (wold : BitVec 32)
    (b0' : BitVec 8) (kok kf : SailM Unit) (P : IProp GF) (Φ : Athread → IProp GF) :
    k ≠ (AxOpsem.grow (gtAdGd GT) i).length →
    (AxOpsem.grow (gtAdGd GT) i)[k]? = some (.LRmw true false (paZ lkpa) [t, t, t, t]
      (WeakInterpProj.wbytes 4 wold) AxSpinX4.o4 .WCplain) →
    (WeakInterpProj.wbytes 4 wold)[0]? = some b0' → b0' ≠ b0 →
    ⊢ P -∗ (P -∗ ∀ rs : RegFile, TW i Φ ⟨hp cpu kf rs, k + 1⟩) -∗
      ∀ rs : RegFile, TW i Φ ⟨hp cpu (AxSpinX4.acq4 kok kf) rs, k⟩ := by
  intro Hne Hrow Hb0 Hnz
  have Hl : gxLbl (gtAdGd GT).gdG (i, k) = some (.LRmw true false (paZ lkpa) [t, t, t, t]
      (WeakInterpProj.wbytes 4 wold) AxSpinX4.o4 .WCplain) := by
    rw [gxLblGrow]; exact Hrow
  have Hwne : wold ≠ zero32 := by
    intro h
    subst h
    rw [zero32Byte0] at Hb0
    exact Hnz (Option.some.inj Hb0).symm
  obtain ⟨Hr, Hw, Hsg, -⟩ := gwbRmwn _ _ _ _ _ _ _ Hl
  have Hrd : greadsByte (gtAdGd GT).gdG (i, k) Lx.xlLk t b0' := by
    have H := Hr 0 t b0' rfl Hb0
    rw [AxSpinX5.addZero] at H
    exact H
  have Hwr : gwritesByte (gtAdGd GT).gdG (i, k) Lx.xlLk b1 := by
    have H := Hw 0 b1 (by decide +kernel)
    rw [AxSpinX5.addZero] at H
    exact H
  have Hlw : ∀ a v', gwritesByte (gtAdGd GT).gdG (i, k) a v' → a ∈ lwb Lx := by
    intro a v' Hw'
    obtain ⟨j, Hj, rfl⟩ := Hsg a v' Hw'
    have hj := (List.getElem?_eq_some_iff.1 Hj).1
    simp only [AxSpinX4.o4, wbytesLength] at hj
    exact (lwbLx _).2 ⟨by omega, by omega⟩
  have Hval : graphData (gtAdGd GT) (i, k) = some (WeakInterpProj.wbytes 4 one32) := by
    unfold graphData; rw [Hl]; rfl
  have HW := nshRmwWrite (hlc := hlc) (pol := xv6Pol GT) (gtAdGd GT) Xv6N Unit (protXv6 Lx) nm cpu
    i Φ 4 lkpa lkpaRam one32 (if wold = zero32 then kok else kf) k Hne
    iprop(P ∗ (P -∗ ∀ rs : RegFile, TW i Φ ⟨hp cpu kf rs, k + 1⟩))
    (fun rs => by
      iintro ⟨HP, HΨ⟩
      ihave Hfe := fxNeutral (hlc := hlc) (GF := GF) Lx GT nm LxOk Hcons (i, k) t b0' Hrd Hnz Hwr
        Hlw
      iapply (evPlain (hlc := hlc) (pol := xv6Pol GT) (gtAdGd GT) Xv6N Unit (protXv6 Lx) nm i k
        iprop(True) iprop(True) _ _ Hval) $$ [Hfe]
      · iapply (@flowEqDynMono hlc GF _ (AxSpinX2.xG Lx GT nm) (xv6Pol GT) (gtAdGd GT) (i, k) _
          (∅ : Mea GF) iprop(True) iprop(True ∗ True)) $$ [] Hfe
        inext
        iintro _
        isplitr
        · itrivial
        · itrivial
      iintro _ _
      rw [if_neg Hwne]
      iapply HΨ $$ HP %rs)
  have HR := nshRmwRead (hlc := hlc) (pol := xv6Pol GT) (gtAdGd GT) Xv6N Unit (protXv6 Lx) nm cpu
    i Φ 4 (by decide) lkpa lkpaRam (amoK kok kf) k [t, t, t, t] (WeakInterpProj.wbytes 4 wold)
    AxSpinX4.o4 .WCplain Hne Hrow
    iprop(P ∗ (P -∗ ∀ rs : RegFile, TW i Φ ⟨hp cpu kf rs, k + 1⟩))
    (fun rs => by
      iintro ⟨HP, HΨ⟩
      rw [amoKWord kok kf wold]
      iapply HW $$ [$HP $HΨ] %rs)
  iintro HP HΨ
  iapply HR $$ [$HP $HΨ]

/-- THE RELEASE (`fence rw,w; sw lk ← 0`, 4 bytes, WCrel): any family `m` of po-earlier anchors;
lk->cpu from `a1`, nextpid from `a2` (each gob-before the store through the fence); deposits
`notheld`. -/
theorem wpdReleaseX (GT : GdexecT) (nm : Xv6N) (cpu : CPU) (Hcons : rvwmoCatConsistent (gtAdGd GT))
    (i : Agent) (kf : Nat) (m' : SailM Unit) (c a1 a2 : Geid) (m : Mea GF)
    (Φ : Athread → IProp GF) :
    kf ≠ (AxOpsem.grow (gtAdGd GT) i).length → kf + 1 ≠ (AxOpsem.grow (gtAdGd GT) i).length →
    (AxOpsem.grow (gtAdGd GT) i)[kf]? = some (.LFence true true false true) →
    (AxOpsem.grow (gtAdGd GT) i)[kf + 1]? = some (.LStore false (paZ lkpa) AxSpinX4.z4 .WCrel) →
    (∀ e, e ∈ (FiniteMap.dom_set m : GSet Geid) → e.1 = i ∧ e.2 < kf ∧
      ∃ l, (AxOpsem.grow (gtAdGd GT) i)[e.2]? = some l ∧ lbIsMem l = true) →
    a1 ∈ (FiniteMap.dom_set m : GSet Geid) → a2 ∈ (FiniteMap.dom_set m : GSet Geid) →
    ⊢ ISL -∗ ([∗map] e ↦ P ∈ m, AxAnnot.annotOwn e P) -∗
      (([∗map] P ∈ m, P) -∗ LK i c ∗ RCPU a1 ∗ RNP a2) -∗
      (AxAnnot.annotOwn (i, kf + 1) (NH i) -∗ ∀ rs : RegFile, TW i Φ ⟨hp cpu m' rs, kf + 1 + 1⟩) -∗
      ∀ rs : RegFile, TW i Φ ⟨hp cpu (fnc (stv 4 lkpa zero32 m')) rs, kf⟩ := by
  intro Hne1 Hne2 Hf Hst Hdom Ha1 Ha2
  have Hlf : gxLbl (gtAdGd GT).gdG (i, kf) = some (.LFence true true false true) := by
    rw [gxLblGrow]; exact Hf
  have Hls : gxLbl (gtAdGd GT).gdG (i, kf + 1) =
      some (.LStore false (paZ lkpa) AxSpinX4.z4 .WCrel) := by
    rw [gxLblGrow]; exact Hst
  have Hgob : ∀ e, e ∈ (FiniteMap.dom_set m : GSet Geid) →
      gobCat (gtAdGd GT) e (i, kf + 1) ∧
        e ∈ @Axpol.lobp (xv6Pol GT) (gtAdGd GT) (i, kf + 1) := by
    rintro ⟨ei, ek⟩ He
    obtain ⟨Hi, Hlt, l, Hl, Hmem⟩ := Hdom _ He
    dsimp only at Hi Hlt Hl
    rw [show ((ei, ek) : Geid) = (i, ek) from by rw [Hi]]
    have Hl' : gxLbl (gtAdGd GT).gdG (i, ek) = some l := by rw [gxLblGrow]; exact Hl
    exact ⟨fenceGob (gtAdGd GT) i ek kf (kf + 1) l _ _ _ Hl' (WeakRvwmoGraph.gwfMemRW _ _ _ Hcons.1 Hl' Hmem) Hlf Hls Hlt (by omega),
      fenceLobp (gtAdGd GT) Hcons i ek kf (kf + 1) l _ _ _ Hl' Hmem Hlf Hls Hlt (by omega)⟩
  have HS := nshWrite (hlc := hlc) (pol := xv6Pol GT) (gtAdGd GT) Xv6N Unit (protXv6 Lx) nm cpu i
    Φ 4 lkpa lkpaRam zero32 m' (kf + 1) Hne2
    iprop(ISL ∗ ([∗map] e ↦ P ∈ m, AxAnnot.annotOwn e P) ∗
      (([∗map] P ∈ m, P) -∗ LK i c ∗ RCPU a1 ∗ RNP a2) ∗
      (AxAnnot.annotOwn (i, kf + 1) (NH i) -∗
        ∀ rs : RegFile, TW i Φ ⟨hp cpu m' rs, kf + 1 + 1⟩))
    (fun rs => by
      have Hval : graphData (gtAdGd GT) (i, kf + 1) = some (WeakInterpProj.wbytes 4 zero32) := by
        unfold graphData; rw [Hls]; rfl
      obtain ⟨Hws, Hsgs⟩ := gwbStoren _ _ _ _ _ Hls
      have Hzw : zw Lx.xlLk (gtAdGd GT).gdG (i, kf + 1) := by
        have H := Hws 0 b0 zero32Byte0
        rw [AxSpinX5.addZero] at H
        exact H
      have Hlw : ∀ a v', gwritesByte (gtAdGd GT).gdG (i, kf + 1) a v' → a ∈ lwb Lx := by
        intro a v' Hw'
        obtain ⟨j, Hj, rfl⟩ := Hsgs a v' Hw'
        have hj := (List.getElem?_eq_some_iff.1 Hj).1
        simp only [AxSpinX4.z4, wbytesLength] at hj
        exact (lwbLx _).2 ⟨by omega, by omega⟩
      have Hsub : (FiniteMap.dom_set m : GSet Geid) ⊆
          @Axpol.lobp (xv6Pol GT) (gtAdGd GT) (i, kf + 1) := fun e He => (Hgob e He).2
      iintro ⟨#Hil, Hm, Hw, HΨ⟩
      ihave Hfe := (fxReleasePid (hlc := hlc) Lx GT nm LxOk Hcons (i, kf + 1) i c a1 a2 m Hzw
        (fun t v => storenNoRead _ _ _ _ _ _ _ _ Hls) Hlw (Hgob a1 Ha1).1 (Hgob a2 Ha2).1)
        $$ Hil Hw
      iapply (evDrawM (hlc := hlc) (pol := xv6Pol GT) (gtAdGd GT) Xv6N Unit (protXv6 Lx) nm
        (xv6AxpolWf GT) i (kf + 1) m (NH i) iprop(True) _ _ Hval Hsub) $$ Hm [Hfe]
      · iapply (@flowEqDynMono hlc GF _ (AxSpinX2.xG Lx GT nm) (xv6Pol GT) (gtAdGd GT) (i, kf + 1)
          _ _ (NH i) iprop(NH i ∗ True)) $$ [] Hfe
        inext
        iintro H
        isplitl [H]
        · iexact H
        · itrivial
      iintro H _
      iapply HΨ $$ H %rs)
  have H := nshFence (hlc := hlc) (pol := xv6Pol GT) (gtAdGd GT) Xv6N Unit (protXv6 Lx) nm cpu i Φ
    (stv 4 lkpa zero32 m') kf Hne1
    iprop(ISL ∗ ([∗map] e ↦ P ∈ m, AxAnnot.annotOwn e P) ∗
      (([∗map] P ∈ m, P) -∗ LK i c ∗ RCPU a1 ∗ RNP a2) ∗
      (AxAnnot.annotOwn (i, kf + 1) (NH i) -∗
        ∀ rs : RegFile, TW i Φ ⟨hp cpu m' rs, kf + 1 + 1⟩))
    (fun rs => by
      iintro ⟨#Hil, Hm, Hw, HΨ⟩
      inext
      iapply HS $$ [$Hil $Hm $Hw $HΨ] %rs)
  iintro #Hil Hm Hw HΨ
  iapply H $$ [$Hil $Hm $Hw $HΨ]

/-- The holder's `lw lk` (4 bytes; release's `holding` check): `locked` (with any frame `Q`)
drawn from the claim (ppo rule 5), deposited back with `v ≠ 0`. -/
theorem wpdLkHeldX (GT : GdexecT) (nm : Xv6N) (cpu : CPU) (Hcons : rvwmoCatConsistent (gtAdGd GT))
    (i : Agent) (kc k : Nat) (KK : Result (BitVec (8 * 4) × Option Bool) Arch.abort → SailM Unit)
    (tc : Nat) (ts : List Nat) (wl : BitVec 32) (Q : IProp GF) (Φ : Athread → IProp GF) :
    k ≠ (AxOpsem.grow (gtAdGd GT) i).length →
    (AxOpsem.grow (gtAdGd GT) i)[kc]? =
      some (.LRmw true false (paZ lkpa) [tc, tc, tc, tc] AxSpinX4.z4 AxSpinX4.o4 .WCplain) →
    kc < k →
    (AxOpsem.grow (gtAdGd GT) i)[k]? =
      some (.LLoad false (paZ lkpa) ts (WeakInterpProj.wbytes 4 wl)) →
    nolk Lx.xlLk (gtAdGd GT).gdG (i, kc) (i, k) →
    ⊢ AxAnnot.annotOwn (i, kc) iprop(LK i (i, kc) ∗ Q) -∗
      (AxAnnot.annotOwn (i, k) iprop(LK i (i, kc) ∗ Q) -∗
        AxAnnot.annotOwn (i, k) iprop(⌜wl ≠ zero32⌝) -∗
        ∀ rs : RegFile, TW i Φ ⟨hp cpu (KK (.Ok (wl, none))) rs, k + 1⟩) -∗
      ∀ rs : RegFile,
        TW i Φ ⟨hp cpu (.impure (.ok (.memRead 4 64 (rreqn 4 l3pAkP lkpa))) KK) rs, k⟩ := by
  intro Hne Hrowc Hlt Hrow Hnl
  have Hlc : gxLbl (gtAdGd GT).gdG (i, kc) =
      some (.LRmw true false (paZ lkpa) [tc, tc, tc, tc] AxSpinX4.z4 AxSpinX4.o4 .WCplain) := by
    rw [gxLblGrow]; exact Hrowc
  have Hl : gxLbl (gtAdGd GT).gdG (i, k) =
      some (.LLoad false (paZ lkpa) ts (WeakInterpProj.wbytes 4 wl)) := by
    rw [gxLblGrow]; exact Hrow
  have Hwf := Hcons.1
  have Hadv := advLoad (gtAdGd GT) i k false (paZ lkpa) ts (WeakInterpProj.wbytes 4 wl) Hrow
  have H := nshRead (hlc := hlc) (pol := xv6Pol GT) (gtAdGd GT) Xv6N Unit (protXv6 Lx) nm cpu i
    Φ 4 (by decide) lkpa lkpaRam KK k Hne Hadv
    iprop(AxAnnot.annotOwn (i, kc) iprop(LK i (i, kc) ∗ Q) ∗
      (AxAnnot.annotOwn (i, k) iprop(LK i (i, kc) ∗ Q) -∗
        AxAnnot.annotOwn (i, k) iprop(⌜wl ≠ zero32⌝) -∗
        ∀ rs : RegFile, TW i Φ ⟨hp cpu (KK (.Ok (wl, none))) rs, k + 1⟩))
    (fun vs rs Hgv => by
      have Hvs : vs = WeakInterpProj.wbytes 4 wl := by
        have Hgv' := Hgv
        unfold graphValue at Hgv'
        rw [Hl] at Hgv'
        simp only [Option.bind_some, lblValue, Option.some.injEq] at Hgv'
        exact Hgv'.symm
      subst Hvs
      rw [wordOfBytesWbytes]
      have Hin : ((i, kc) : Geid) ∈ @Axpol.lobp (xv6Pol GT) (gtAdGd GT) (i, k) :=
        acqLobp (gtAdGd GT) Hcons i kc k _ _ _ _ _ _ Hlc Hl rfl Hlt
      have Hpo : WeakRvwmoGraph.gpo (gtAdGd GT).gdG (i, kc) (i, k) :=
        gpoRow (gtAdGd GT) i kc k _ _ Hlc Hl Hlt
      have Hnw : gisW (gtAdGd GT).gdG (i, k) = false := by unfold gisW; rw [Hl]; rfl
      obtain ⟨t0, Ht0⟩ := loadnReads (gtAdGd GT).gdG Hwf (i, k) (paZ lkpa) ts 4 wl 0 Hl (by decide)
      rw [AxSpinX5.addZero] at Ht0
      have Hsing : ⊢ ([∗map] Rin ∈ ({[((i, kc) : Geid) := iprop(LK i (i, kc) ∗ Q)]} : Mea GF),
          Rin) -∗ iprop(LK i (i, kc) ∗ Q) := by
        iintro H
        iapply (BigSepM.bigSepM_singleton (M := GMapF Geid)).1 $$ H
      iintro ⟨Hc, HΨ⟩
      ihave Hw := Hsing
      ihave Hfe := (fxLkreadHeld (hlc := hlc) Lx GT nm LxOk Hcons (i, k) i (i, kc) Q
        ({[((i, kc) : Geid) := iprop(LK i (i, kc) ∗ Q)]} : Mea GF) Hnw Hpo Hnl) $$ Hw
      ihave Hfe := (@flowEqDynMono hlc GF _ (AxSpinX2.xG Lx GT nm) (xv6Pol GT) (gtAdGd GT) (i, k)
        _ _
        iprop((LK i (i, kc) ∗ Q) ∗
          ⌜∀ t' v', greadsByte (gtAdGd GT).gdG (i, k) Lx.xlLk t' v' → v' ≠ b0⌝)
        iprop((LK i (i, kc) ∗ Q) ∗ ⌜wl ≠ zero32⌝)) $$ [] Hfe
      · inext
        iintro ⟨H, %Hf⟩
        isplitl [H]
        · iexact H
        · ipureintro
          intro Hz
          subst Hz
          exact Hf t0 _ Ht0 nthByteZero32
      iapply (evDraw (hlc := hlc) (pol := xv6Pol GT) (gtAdGd GT) Xv6N Unit (protXv6 Lx) nm
        (xv6AxpolWf GT) i k (i, kc) _ iprop(LK i (i, kc) ∗ Q) iprop(⌜wl ≠ zero32⌝) _ _ Hgv Hin)
        $$ Hc Hfe
      iintro H1 H2
      iapply HΨ $$ H1 H2 %rs)
  iintro Hc HΨ
  iapply H $$ [$Hc $HΨ]

end leavesX

end Weak
