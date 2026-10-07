/-
Weak: **Phase 1c, part 2 of the spinlock plan -- THE RULES of the joint instance `protXv6`
(Ixv6)**, every one a `flowEqDyn` at `AxSpinX2.xG L GT nm` (= `shG (gtAdGd GT) Xv6N Unit
(protXv6 L) nm`) with policy `xv6Pol GT` (∀σ, ∀ processed set: nothing about σ is assumed beyond
its own conjuncts; `fxBuild` re-establishes WC, Φ_cpu and WOK and DEMANDS of every event Φ_cpu
(`cpuOk`) and "writes only what its writer may write" (`wrsOk`)).

Rocq: `iris/AxSpinX2.v` @ xxvzwolszwmp.

## The Rocq header, in substance

RULES, by class:
  LOCK WORD (4 bytes `lwb L`, keyed on the low byte `lk`): `fxNeutral` (acquire-fail RMW),
  `fxClaim` (acquire-success, `notheld` in hand), `fxClaim'` (`notheld` drawn through `flowIn`),
  `fxRelease'` (the WCrel zero store, each component of `R` from its own anchor; deposits
  `notheld`), `fxReleasePid` (the same at `R := RPid`, two anchors), `fxLkreadHeld` (the holder's
  `lw lk`: deposits `locked ∗ Q` and `⌜v ≠ 0⌝` at the read), `fxRead` (any other non-write
  event).  All lock arms require "writes only `lwb L`".
  lk->cpu (owned bytes `clb L`): `fxCpuWrite` (the holder's `sd` of `cvx i` or 0, Φ_cpu FROM THE
  VALUE), `fxOwnedRead` (last-value read, gmo case), `fxFwdRead` (forwarded case),
  `holderCpuRead` (word level: the read word IS `cpuAddr (cpuOf i)`), `fxCpuRacy` (racy read:
  `rdFact`).
  nextpid (owned bytes `npb L` inside `RPid`): `fxNpRead` (the CS's `lw`, exposing the value),
  `fxNpIncr` (the CS's `sw ← v+1`: ●mono v → v+1, issued set gains `v`, the EXCLUSIVE ◯{v}
  minted -- Theorem 2's ghosts `npIssue`, `issuedFragExcl`), `fxNpWrite` (bare owned write).
  PRIVATE: `fxPrivWrite`, `fxPrivRead`/`fxPrivReadn` (owned reload: the po-latest store's value,
  via `privSrc`), `fxPrivRead0` (genesis arm).  READ-ONLY: `fxRoRead`/`fxRoReadn`.
  BLOCKED: `fxBlocked` -- any flow equation for a write of a byte `a` with `¬ wok L a e.1`
  refutes the protocol state it is run on.

## Deviations from Rocq

1. VOCABULARY (as `AxSpinX` deviation 1): `Z` ↦ `Int`, `agent` ↦ `Agent`, `bv 8` ↦ `BitVec 8`,
   `gset` ↦ `GSet`, `gd_g GD` ↦ `GD.gdG`, `gx_img G a` ↦ `G.gxImg a`, `l !! j` ↦ `l[j]?`
   (indices typed `Nat`), `B0`/`B1` ↦ `b0`/`b1`, `is_Some (gx_lbl G e)` ↦ `(gxLbl G e).isSome`,
   `wbytes 4 (Z_to_bv 32 v)` ↦ `WeakInterpProj.wbytes 4 (BitVec.ofInt 32 v)`, `0 ≤ v < 2^32` ↦
   `0 ≤ v ∧ v < 2 ^ 32`, `cpus_ptr (cpu_of i)` ↦ `cpuAddr (cpuOf i)`, `mono_nat_auth_own γ 1 n`
   ↦ `MonoNat.auth_own γ (DFrac.own 1) (.ofNat n)`, `Forall P Rs` ↦ `∀ Rj, Rj ∈ Rs → P Rj`.
2. CONTEXTS (as `AxSpinProt6` deviation 2): Rocq section variables are explicit leading
   arguments in Rocq's order, only where Rocq's section mechanism includes them (§1 `L HL GD
   Hcons`; §3 `L GT nm`, then `HL Hcons` where `Proof using` names them).  `invGS_gen HasNoLc Σ`
   ↦ `[InvGS_gen hlc GF]` for any `hlc`; `axannotG Σ`+`axannotGS Σ` ↦ `[AxannotGS GF]`.  The
   local instance `x_pol` is inlined as `xv6Pol GT` (passed explicitly); `x_G` is the reducible
   def `AxSpinX2.xG L GT nm` (passed explicitly).  O2 STAGE C (as `AxSpinProt2` deviation 1):
   Rocq's text argument `xl_text L` of `AxGA2` is gone (`shG` has no text oracle).
3. STATEMENT SHAPES: wand chains of flow-equation rules ↦ `⊢ A -∗ B -∗ …` (as `AxSpinProt6`);
   the two ghost lemmas `P -∗ Q -∗ R` / `P -∗ Q ==∗ R` ↦ `P ∗ Q ⊢ R` / `P ∗ Q ⊢ |==> R` (as
   `AxSpinX` deviation 5); pure premises stay `→`; the Rocq notations `OWN`/`LK`/`RP` are
   unfolded.
4. `R_np_unfold` is `.rfl` (as in Rocq, `done`).
5. The trailing `Print Assumptions` commands are not ported.

**Rocq → Lean name map.**  `ppo1_gmo` `ppo1Gmo`, `lbl_of_w` `lblOfW`, `lbl_of_r` `lblOfR`,
`same_hart_gmo_po` `sameHartGmoPo`, `priv_src` `privSrc`, `priv_read_val` `privReadVal`,
`priv_read_img` `privReadImg`, `ro_read_img` `roReadImg`, `fwd_read_val` `fwdReadVal`,
`holder_cpu_read` `holderCpuRead`, `issued_frag_excl` `issuedFragExcl`, `np_issue` `npIssue`,
`x_G` `AxSpinX2.xG`, `wrs_ok` `wrsOk`, `fx_build` `fxBuild`, `nw_side` `nwSide`, `lw_side`
`lwSide`, `xo_side` `xoSide`, `priv_side` `privSide`, `fx_neutral` `fxNeutral`, `fx_claim`
`fxClaim`, `fx_claim'` `fxClaim'`, `fx_release'` `fxRelease'`, `fx_release_pid` `fxReleasePid`,
`fx_lkread_held` `fxLkreadHeld`, `fx_read` `fxRead`, `fx_read_fact` `fxReadFact`,
`fx_RVL_write` `fxRVLWrite`, `fx_cpu_write` `fxCpuWrite`, `fx_np_write` `fxNpWrite`,
`fx_owned_read` `fxOwnedRead`, `fx_fwd_read` `fxFwdRead`, `fx_cpu_racy` `fxCpuRacy`,
`fx_priv_write` `fxPrivWrite`, `fx_priv_read` `fxPrivRead`, `fx_priv_readn` `fxPrivReadn`,
`fx_priv_read0` `fxPrivRead0`, `fx_ro_read` `fxRoRead`, `fx_ro_readn` `fxRoReadn`, `R_npv`
`RNpv`, `R_np_unfold` `RNpUnfold`, `fx_np_read` `fxNpRead`, `fx_np_incr` `fxNpIncr`,
`fx_blocked` `fxBlocked`.  No duplicated Rocq names; no Lean-only helpers.

**Dropped:** none (45 Rocq decls incl. the local instances `x_pol`/`x_G`; `x_pol` inlined as
`xv6Pol GT`; 44 Lean).
-/
import Weak.AxSpinX

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std Iris.Std.PartialMap MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D

/-! # 1. Pure graph cores: the private reload, the read-only read -/

theorem ppo1Gmo (GD : Gdexec) (Hcons : rvwmoCatConsistent GD) (e1 e2 : Geid) (a : Int)
    (v : BitVec 8) :
    WeakRvwmoGraph.gpo GD.gdG e1 e2 → gaccesses GD.gdG e1 a → gwritesByte GD.gdG e2 a v →
    gmoLt GD.gdG e1 e2 :=
  fun Hpo Ha Hw => obCatSubGmo GD _ _ Hcons (ppo1Gob GD e1 e2 a v Hpo Ha Hw)

theorem lblOfW (GD : Gdexec) (e : Geid) (a : Int) (v : BitVec 8) :
    gwritesByte GD.gdG e a v → (gxLbl GD.gdG e).isSome := by
  rintro ⟨l, _, _, _, hl, _⟩
  simp [hl]

theorem lblOfR (GD : Gdexec) (e : Geid) (a : Int) (t : Nat) (v : BitVec 8) :
    greadsByte GD.gdG e a t v → (gxLbl GD.gdG e).isSome := by
  rintro ⟨l, _, _, _, _, hl, _⟩
  simp [hl]

/-- A write `w` of byte `a` that is gmo-before a read `r` of `a` by the same hart is po-BEFORE
`r` (a po-later one is gmo-after: ppo rule 1). -/
theorem sameHartGmoPo (GD : Gdexec) (Hcons : rvwmoCatConsistent GD) (w r : Geid) (a : Int)
    (v : BitVec 8) (t : Nat) (vr : BitVec 8) :
    gwritesByte GD.gdG w a v → greadsByte GD.gdG r a t vr → gisW GD.gdG r = false →
    w.1 = r.1 → gmoLt GD.gdG w r → WeakRvwmoGraph.gpo GD.gdG w r := by
  intro Hw Hr Hnw Hh Hlt
  have Hlw := lblOfW GD w a v Hw
  have Hlr := lblOfR GD r a t vr Hr
  by_cases Hwr : w.2 < r.2
  · exact ⟨Hh, Hwr, Hlw, Hlr⟩
  exfalso
  by_cases Heq : w.2 = r.2
  · have Hwr' : w = r := Prod.ext Hh Heq
    subst Hwr'
    have h := WeakRvwmoGraph.gwritesByteGisW _ _ _ _ Hw
    rw [Hnw] at h
    cases h
  · have Hrw : gmoLt GD.gdG r w :=
      ppo1Gmo GD Hcons r w a v ⟨Hh.symm, by omega, Hlr, Hlw⟩ (Or.inr ⟨t, vr, Hr⟩) Hw
    exact gmoLtIrrefl _ w (gmoLtTrans _ w r w Hlt Hrw)

/-- THE PRIVATE SOURCE LEMMA: a read `r` of a byte private to `r`'s hart reads the image or a
write that is po-BEFORE `r` -- whatever the processing order, given WOK over the processed set
and the handout. -/
theorem privSrc (L : Xlay) (HL : xlayOk L) (GD : Gdexec) (Hcons : rvwmoCatConsistent GD)
    (s : GSet Geid) (r : Geid) (a : Int) (t : Nat) (v : BitVec 8) :
    WOK L GD.gdG s → WPh GD.gdG s r → priv L a r.1 → gisW GD.gdG r = false →
    greadsByte GD.gdG r a t v →
    (t = 0 ∧ GD.gdG.gxImg a = some v) ∨
    ∃ w, gwriteAt GD.gdG t = some w ∧ gwritesByte GD.gdG w a v ∧
      WeakRvwmoGraph.gpo GD.gdG w r := by
  intro Hwok Hwp Hpr Hnw Hrd
  have Hs := (Hcons.2.2.1 r a t v Hrd).1
  cases t with
  | zero => exact Or.inl ⟨rfl, Hs⟩
  | succ j =>
    right
    obtain ⟨w, Hat, Hw, Hvis⟩ := Hs
    refine ⟨w, Hat, Hw, ?_⟩
    rcases Hvis with Hlt | Hpo
    · have Hin : w ∈ s := Hwp w (WeakRvwmoGraph.gwritesByteGisW _ _ _ _ Hw) Hlt
      have Hok := Hwok w a v Hin Hw
      obtain ⟨-, Hpl, Huniq, -⟩ := HL
      obtain ⟨Hnl, Hnx⟩ := Hpl a r.1 Hpr
      rcases Hok with Hl | Hx | Hp
      · exact absurd Hl Hnl
      · exact absurd Hx Hnx
      · have Hh := Huniq a w.1 r.1 Hp Hpr
        exact sameHartGmoPo GD Hcons w r a v (j + 1) v Hw Hrd Hnw Hh Hlt
    · exact Hpo

/-- THE PRIVATE RELOAD VALUE: if `w` (writing `b` at `a`) is `r`'s po-latest store to `a`, `r`
reads `b`. -/
theorem privReadVal (L : Xlay) (HL : xlayOk L) (GD : Gdexec) (Hcons : rvwmoCatConsistent GD)
    (s : GSet Geid) (r : Geid) (a : Int) (w : Geid) (b : BitVec 8) :
    WOK L GD.gdG s → WPh GD.gdG s r → priv L a r.1 → gisW GD.gdG r = false →
    gwritesByte GD.gdG w a b → WeakRvwmoGraph.gpo GD.gdG w r →
    (∀ w' v', gwritesByte GD.gdG w' a v' → WeakRvwmoGraph.gpo GD.gdG w' r →
      w' = w ∨ WeakRvwmoGraph.gpo GD.gdG w' w) →
    ∀ t v, greadsByte GD.gdG r a t v → v = b := by
  intro Hwok Hwp Hpr Hnw Hw Hwr Hlast t v Hrd
  rcases privSrc L HL GD Hcons s r a t v Hwok Hwp Hpr Hnw Hrd with
    ⟨rfl, -⟩ | ⟨w', Hat, Hw', Hpo'⟩
  · exfalso
    have Hle := (Hcons.2.2.1 r a 0 v Hrd).2 w b Hw (Or.inr Hwr)
    have Hwg : w ∈ gwrites GD.gdG := gwritesByteGwrites _ w a b Hcons.1 Hw
    have := WeakRvwmoGraph.gwixPos _ w Hwg
    omega
  · rcases Hlast w' v Hw' Hpo' with rfl | Hpo2
    · exact gwritesByteDet _ _ _ _ _ Hw' Hw
    · exfalso
      have Hle := (Hcons.2.2.1 r a t v Hrd).2 w b Hw (Or.inr Hwr)
      have Hlt : gmoLt GD.gdG w' w := ppo1Gmo GD Hcons w' w a b Hpo2 (Or.inl ⟨v, Hw'⟩) Hw
      obtain ⟨Hin', Hix'⟩ := gwriteAtInv _ t w' Hcons.1.1 Hat
      have Hin : w ∈ gwrites GD.gdG := gwritesByteGwrites _ w a b Hcons.1 Hw
      have := gmoGwixLt _ w' w Hcons.1 Hin' Hin Hlt
      omega

/-- The genesis arm: no po-earlier store to `a` by `r`'s hart ⇒ image. -/
theorem privReadImg (L : Xlay) (HL : xlayOk L) (GD : Gdexec) (Hcons : rvwmoCatConsistent GD)
    (s : GSet Geid) (r : Geid) (a : Int) :
    WOK L GD.gdG s → WPh GD.gdG s r → priv L a r.1 → gisW GD.gdG r = false →
    (∀ w' v', gwritesByte GD.gdG w' a v' → WeakRvwmoGraph.gpo GD.gdG w' r → False) →
    ∀ t v, greadsByte GD.gdG r a t v → t = 0 ∧ GD.gdG.gxImg a = some v := by
  intro Hwok Hwp Hpr Hnw Hnone t v Hrd
  rcases privSrc L HL GD Hcons s r a t v Hwok Hwp Hpr Hnw Hrd with H | ⟨w', -, Hw', Hpo'⟩
  · exact H
  · exact absurd (Hnone w' v Hw' Hpo') id

/-- THE READ-ONLY READ: a byte nobody may write (`xlayOk`'s ro arm) is read at its image, given
the row fact that the reader has no po-earlier write of it. -/
theorem roReadImg (L : Xlay) (HL : xlayOk L) (GD : Gdexec) (Hcons : rvwmoCatConsistent GD)
    (s : GSet Geid) (r : Geid) (a : Int) :
    WOK L GD.gdG s → WPh GD.gdG s r → L.xlRo a →
    (∀ w' v', gwritesByte GD.gdG w' a v' → WeakRvwmoGraph.gpo GD.gdG w' r → False) →
    ∀ t v, greadsByte GD.gdG r a t v → t = 0 ∧ GD.gdG.gxImg a = some v := by
  intro Hwok Hwp Hro Hnone t v Hrd
  have Hs := (Hcons.2.2.1 r a t v Hrd).1
  cases t with
  | zero => exact ⟨rfl, Hs⟩
  | succ j =>
    exfalso
    obtain ⟨w, -, Hw, Hvis⟩ := Hs
    rcases Hvis with Hlt | Hpo
    · have Hin : w ∈ s := Hwp w (WeakRvwmoGraph.gwritesByteGisW _ _ _ _ Hw) Hlt
      exact HL.2.2.2.1 a w.1 Hro (Hwok w a v Hin Hw)
    · exact Hnone w v Hw Hpo

/-- The forwarded n-byte value (own store not gmo-before the load). -/
theorem fwdReadVal (GD : Gdexec) (Hcons : rvwmoCatConsistent GD) (r w : Geid) (Cw : List Int)
    (vs : List (BitVec 8)) :
    WeakRvwmoGraph.gpo GD.gdG w r → ¬ gmoLt GD.gdG w r →
    (∀ (j : Nat) a v, Cw[j]? = some a → vs[j]? = some v → gwritesByte GD.gdG w a v) →
    vs.length = Cw.length →
    (∀ w' a v', a ∈ Cw → gwritesByte GD.gdG w' a v' → WeakRvwmoGraph.gpo GD.gdG w w' →
      WeakRvwmoGraph.gpo GD.gdG w' r → False) →
    ∀ (j : Nat) a t v, Cw[j]? = some a → greadsByte GD.gdG r a t v → vs[j]? = some v := by
  intro Hpo Hnlt Hall Hlen Hnb j a t v Hj Hrd
  have hjl : j < vs.length := by
    rw [Hlen]
    exact (List.getElem?_eq_some_iff.1 Hj).1
  have Hb : vs[j]? = some vs[j] := List.getElem?_eq_getElem hjl
  have Hw := Hall j a _ Hj Hb
  have Ha : a ∈ Cw := List.mem_of_getElem? Hj
  obtain ⟨-, rfl⟩ := ownForwardCat' GD a w r _ t v Hcons Hpo Hw Hrd Hnlt
    (fun w' v' Hw' H1 H2 => Hnb w' a v' Ha Hw' H1 H2)
  exact Hb

/-- (b)'s consumer at WORD level: the 8 bytes a holder reads after its own
`sd lk->cpu ← cpus_ptr` form `cpuAddr (cpuOf i)`. -/
theorem holderCpuRead (L : Xlay) (G : Gexec) (r : Geid) (i : Agent) (vsr : List (BitVec 8)) :
    vsr.length = 8 →
    (∀ (j : Nat) a, (clb L)[j]? = some a → ∃ t v, greadsByte G r a t v ∧ vsr[j]? = some v) →
    (∀ (j : Nat) a t v, (clb L)[j]? = some a → greadsByte G r a t v → (cvx i)[j]? = some v) →
    vsr = cvx i ∧ wordOfBytes 8 vsr = cpuAddr (cpuOf i) := by
  intro Hlen Hrd Hv
  have Heq : vsr = cvx i := by
    apply List.ext_getElem?
    intro j
    cases Hj : (clb L)[j]? with
    | some a =>
      obtain ⟨t, v, Hr, Hvj⟩ := Hrd j a Hj
      rw [Hvj]
      exact (Hv j a t v Hj Hr).symm
    | none =>
      have h1 : (clb L).length ≤ j := List.getElem?_eq_none_iff.1 Hj
      have hc : (clb L).length = 8 := by simp [clb, clRange]
      rw [List.getElem?_eq_none_iff.2 (by omega),
        List.getElem?_eq_none_iff.2 (by rw [cvxLength]; omega)]
  refine ⟨Heq, ?_⟩
  rw [Heq]
  exact wordOfBytesWbytes 8 _

/-! # 2. Theorem 2's ghost step and the exclusive fragment -/

section npGhost
variable {GF : BundledGFunctors} [AxSpinX.Xv6G GF]

theorem issuedFragExcl (γ : GName) (x : Int) :
    issuedFrag (GF := GF) γ x ∗ issuedFrag γ x ⊢ False := by
  unfold issuedFrag
  iintro ⟨H1, H2⟩
  icases iOwn_cmraValid_op $$ [$H1 $H2] with %hv
  have hd := DisjointLeibnizSet.valid_op_iff_disj.1 (Auth.frag_op_valid.1 hv)
  exact ((elemOfDisjoint.1 hd) x (elemOfSingleton.2 rfl) (elemOfSingleton.2 rfl)).elim

/-- allocpid's ghost step at nextpid = v: ●mono v → v+1, the issued set gains `v` (fresh:
S ⊆ [0,v)), the exclusive ◯{v} is minted. -/
theorem npIssue (γm γi : GName) (v : Int) (S : GSet Int) :
    0 ≤ v → (∀ x, x ∈ S → 0 ≤ x ∧ x < v) →
    MonoNat.auth_own (GF := GF) γm (DFrac.own 1) (.ofNat v.toNat) ∗ issuedAuth γi S ⊢ |==> (
      MonoNat.auth_own γm (DFrac.own 1) (.ofNat (v + 1).toNat) ∗
      issuedAuth γi (({v} : GSet Int) ∪ S) ∗ issuedFrag γi v ∗
      ⌜∀ x, x ∈ ({v} : GSet Int) ∪ S → 0 ≤ x ∧ x < v + 1⌝) := by
  intro Hv HS
  have Hnin : v ∉ S := fun h => by
    have := HS v h
    omega
  have hdisj : ({v} : GSet Int) ## S := by
    rw [elemOfDisjoint]
    intro y hy hy'
    rw [elemOfSingleton.1 hy] at hy'
    exact Hnin hy'
  have hupd : (● (DisjointLeibnizSet.valid S) : Auth (DisjointLeibnizSet (GSet Int))) ~~>
      (● (DisjointLeibnizSet.valid (({v} : GSet Int) ∪ S))) •
        ◯ (DisjointLeibnizSet.valid ({v} : GSet Int)) :=
    Auth.auth_update_alloc (DisjointLeibnizSet.localUpdate_alloc_empty_of_disj _ _ hdisj)
  have hle : (MaxNat.ofNat v.toNat) ≤ MaxNat.ofNat (v + 1).toNat := by
    show v.toNat ≤ (v + 1).toNat
    omega
  unfold issuedAuth issuedFrag
  iintro ⟨Hm, Hi⟩
  imod MonoNat.own_update γm (.ofNat v.toNat) (.ofNat (v + 1).toNat) hle $$ Hm with ⟨Hm, -⟩
  imod iOwn_update hupd $$ Hi with Hi
  icases iOwn_op.1 $$ Hi with ⟨Ha, Hc⟩
  imodintro
  isplitl [Hm]
  · iexact Hm
  isplitl [Ha]
  · iexact Ha
  isplitl [Hc]
  · iexact Hc
  · ipureintro
    intro x hx
    rcases elemOfUnion.1 hx with h | h
    · rw [elemOfSingleton.1 h]
      omega
    · have := HS x h
      omega

end npGhost

/-! # 3. THE RULES at the instance -/

/-- Rocq `#[local] Instance x_G` (a named reducible def; O2 Stage C: no text argument). -/
@[reducible] def AxSpinX2.xG {GF : BundledGFunctors.{0,0,0}} [AxannotGS GF] [AxSpinX.Xv6G GF]
    (L : Xlay) (GT : GdexecT) (nm : Xv6N) : AxirisG GF :=
  shG (gtAdGd GT) Xv6N Unit (protXv6 L) nm

def wrsOk (L : Xlay) (GT : GdexecT) (e : Geid) : Prop :=
  ∀ a v, gwritesByte (gtAdGd GT).gdG e a v → wok L a e.1

/-- nextpid inside the critical section, with Theorem 2's ghosts: `RNp` unfolded at its value
`v`. -/
def RNpv {GF : BundledGFunctors} [AxSpinX.Xv6G GF] (L : Xlay) (GT : GdexecT) (nm : Xv6N)
    (e : Geid) (v : Int) : IProp GF :=
  iprop(⌜0 ≤ v ∧ v < 2 ^ 32⌝ ∗
    RVL nm.xnH (gtAdGd GT) (npb L) e (WeakInterpProj.wbytes 4 (BitVec.ofInt 32 v)) ∗
    MonoNat.auth_own nm.xnM (DFrac.own 1) (.ofNat v.toNat) ∗
    ∃ S, issuedAuth nm.xnI S ∗ ⌜∀ x, x ∈ S → 0 ≤ x ∧ x < v⌝)

theorem RNpUnfold {GF : BundledGFunctors} [AxSpinX.Xv6G GF] (L : Xlay) (GT : GdexecT)
    (nm : Xv6N) (e : Geid) :
    RNp (GF := GF) L nm.xnH nm.xnM nm.xnI (gtAdGd GT) e ⊣⊢ ∃ v, RNpv L GT nm e v := .rfl

section rulesX
variable {hlc : HasLC} {GF : BundledGFunctors.{0,0,0}} [InvGS_gen hlc GF] [AxannotGS GF]
  [AxSpinX.Xv6G GF]

/-- THE BUILDER. -/
theorem fxBuild (L : Xlay) (GT : GdexecT) (nm : Xv6N) (e : Geid) (flowIn : Mea GF)
    (R : IProp GF) :
    ⊢ (∀ s : GSet Geid, ⌜e ∉ s⌝ -∗ ⌜WC (gtAdGd GT).gdG s⌝ -∗ ⌜WPh (gtAdGd GT).gdG s e⌝ -∗
        ⌜spSpol GT (gtAdGd GT) e ⊆ s⌝ -∗ ⌜CPUOK (clb L) cvx (gtAdGd GT).gdG s⌝ -∗
        ⌜WOK L (gtAdGd GT).gdG s⌝ -∗
        ownInv (XO L) nm.xnH (gtAdGd GT) s -∗ lkInv nm.xnReg L.xlLk (gtAdGd GT) s -∗
        ([∗map] Rin ∈ flowIn, Rin) ==∗
        ▷ |==> (⌜cpuOk (clb L) cvx (gtAdGd GT).gdG e ∧ wrsOk L GT e⌝ ∗
          ownInv (XO L) nm.xnH (gtAdGd GT) (({e} : GSet Geid) ∪ s) ∗
          lkInv nm.xnReg L.xlLk (gtAdGd GT) (({e} : GSet Geid) ∪ s) ∗ R)) -∗
      @flowEqDyn hlc GF _ (AxSpinX2.xG L GT nm) (gtAdGd GT) e
        (@Axpol.sPol (xv6Pol GT) (gtAdGd GT) e) flowIn R := by
  iintro H
  unfold flowEqDyn
  iintro %σ %s %Hsub %Hnin Hob Hfi
  have Hwp := spolWP GT (gtAdGd GT) e s Hsub
  ihave Hob := (show @AxirisG.obStInterp GF (AxSpinX2.xG L GT nm) (gtAdGd GT) σ s ⊢
    protXv6 L nm (gtAdGd GT) σ s from .rfl) $$ Hob
  unfold protXv6
  icases Hob with ⟨%Hp, Ho, Hl⟩
  obtain ⟨Hwc, Hok, Hwok⟩ := Hp
  imod H $$ %s %Hnin %Hwc %Hwp %Hsub %Hok %Hwok Ho Hl Hfi with H
  iapply fupd_mask_intro LawfulSet.empty_subset
  iintro Hclose
  inext
  imod Hclose
  imod H with ⟨%He, Ho, Hl, HR⟩
  imodintro
  iexists σ
  isplitl [Ho Hl]
  · iapply (show protXv6 L nm (gtAdGd GT) σ (({e} : GSet Geid) ∪ s) ⊢
      @AxirisG.obStInterp GF (AxSpinX2.xG L GT nm) (gtAdGd GT) σ (({e} : GSet Geid) ∪ s)
      from .rfl)
    unfold protXv6
    isplitr
    · ipureintro
      exact ⟨WCInsert _ s e Hwc Hwp, CPUOKInsert (clb L) cvx _ s e Hok He.1,
        WOKInsert L _ s e Hwok He.2⟩
    isplitl [Ho]
    · iexact Ho
    · iexact Hl
  · iexact HR

/-! ## side conditions, per write shape -/

theorem nwSide (L : Xlay) (GT : GdexecT) (e : Geid) : gisW (gtAdGd GT).gdG e = false →
    (∀ a v, a ∈ XO L → ¬ gwritesByte (gtAdGd GT).gdG e a v) ∧
    cpuOk (clb L) cvx (gtAdGd GT).gdG e ∧ wrsOk L GT e := by
  intro Hnw
  have Hn : ∀ a v, ¬ gwritesByte (gtAdGd GT).gdG e a v := AxSpinProt6.nwb _ e Hnw
  exact ⟨fun a v _ => Hn a v, cpuOkNw _ _ _ e (fun a v _ => Hn a v),
    fun a v Hw => absurd Hw (Hn a v)⟩

theorem lwSide (L : Xlay) (GT : GdexecT) (HL : xlayOk L) (e : Geid) :
    (∀ a v, gwritesByte (gtAdGd GT).gdG e a v → a ∈ lwb L) →
    (∀ a v, a ∈ XO L → ¬ gwritesByte (gtAdGd GT).gdG e a v) ∧
    cpuOk (clb L) cvx (gtAdGd GT).gdG e ∧ wrsOk L GT e := by
  intro Hsg
  refine ⟨?_, ?_, ?_⟩
  · intro a v Ha Hw
    exact lwbNotinXO L HL a (Hsg a v Hw) Ha
  · apply cpuOkNw
    intro a v Ha Hw
    exact lwbNotinXO L HL a (Hsg a v Hw) (clbXO L a Ha)
  · intro a v Hw
    exact Or.inl (Hsg a v Hw)

theorem xoSide (L : Xlay) (GT : GdexecT) (HL : xlayOk L) (e : Geid) (Cw : List Int) :
    (∀ a v, gwritesByte (gtAdGd GT).gdG e a v → a ∈ Cw) → (∀ a, a ∈ Cw → a ∈ XO L) →
    (∀ v, ¬ gwritesByte (gtAdGd GT).gdG e L.xlLk v) ∧ wrsOk L GT e := by
  intro Hsg HX
  refine ⟨?_, ?_⟩
  · intro v Hw
    exact lkNotinXO L HL (HX _ (Hsg L.xlLk v Hw))
  · intro a v Hw
    exact Or.inr (Or.inl (HX _ (Hsg a v Hw)))

theorem privSide (L : Xlay) (GT : GdexecT) (HL : xlayOk L) (e : Geid) :
    (∀ a v, gwritesByte (gtAdGd GT).gdG e a v → priv L a e.1) →
    (∀ a v, a ∈ XO L → ¬ gwritesByte (gtAdGd GT).gdG e a v) ∧
    (∀ v, ¬ gwritesByte (gtAdGd GT).gdG e L.xlLk v) ∧
    cpuOk (clb L) cvx (gtAdGd GT).gdG e ∧ wrsOk L GT e := by
  intro Hsg
  have Hpl := HL.2.1
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a v Ha Hw
    exact (Hpl a e.1 (Hsg a v Hw)).2 Ha
  · intro v Hw
    exact (Hpl _ e.1 (Hsg _ v Hw)).1 (lkInLwb L)
  · apply cpuOkNw
    intro a v Ha Hw
    exact (Hpl a e.1 (Hsg a v Hw)).2 (clbXO L a Ha)
  · intro a v Hw
    exact Or.inr (Or.inr (Hsg a v Hw))

/-! ## LOCK WORD -/

/-- ACQUIRE-FAIL (neutral RMW). -/
theorem fxNeutral (L : Xlay) (GT : GdexecT) (nm : Xv6N) (HL : xlayOk L)
    (_Hcons : rvwmoCatConsistent (gtAdGd GT)) (e : Geid) (t : Nat) (v : BitVec 8) :
    greadsByte (gtAdGd GT).gdG e L.xlLk t v → v ≠ b0 →
    gwritesByte (gtAdGd GT).gdG e L.xlLk b1 →
    (∀ a v', gwritesByte (gtAdGd GT).gdG e a v' → a ∈ lwb L) →
    ⊢ @flowEqDyn hlc GF _ (AxSpinX2.xG L GT nm) (gtAdGd GT) e
        (@Axpol.sPol (xv6Pol GT) (gtAdGd GT) e) (∅ : Mea GF) iprop(True) := by
  intro Hr Hv Hw Hsg
  obtain ⟨Hnx, Hok, Hwk⟩ := lwSide L GT HL e Hsg
  iapply fxBuild
  iintro %s %Hn %_ %_ %_ %_ %_ Ho Hl _
  imodintro
  inext
  imodintro
  isplitr
  · ipureintro
    exact ⟨Hok, Hwk⟩
  isplitl [Ho]
  · iapply (ownInvOther (XO L) nm.xnH (gtAdGd GT) s e Hn Hnx) $$ Ho
  isplitl [Hl]
  · iapply (lkInvNeutral nm.xnReg L.xlLk (gtAdGd GT) s e t v Hn Hr Hv Hw) $$ Hl
  · itrivial

/-- ACQUIRE-SUCCESS, `notheld` in hand. -/
theorem fxClaim (L : Xlay) (GT : GdexecT) (nm : Xv6N) (HL : xlayOk L)
    (Hcons : rvwmoCatConsistent (gtAdGd GT)) (c : Geid) (oz : Option Geid) :
    lkClaim L.xlLk (gtAdGd GT).gdG c oz →
    (∀ a v', gwritesByte (gtAdGd GT).gdG c a v' → a ∈ lwb L) →
    ⊢ notheld nm.xnReg L.xlLk c.1 -∗
      isLock nm.xnReg L.xlLk (RPid L nm.xnH nm.xnM nm.xnI (gtAdGd GT)) -∗
      @flowEqDyn hlc GF _ (AxSpinX2.xG L GT nm) (gtAdGd GT) c
        (@Axpol.sPol (xv6Pol GT) (gtAdGd GT) c) (∅ : Mea GF)
        iprop(locked nm.xnReg L.xlLk c.1 c ∗ RPid L nm.xnH nm.xnM nm.xnI (gtAdGd GT) c) := by
  intro Hcl Hsg
  obtain ⟨Hnx, Hok, Hwk⟩ := lwSide L GT HL c Hsg
  iintro Hnh #Hil
  iapply fxBuild
  iintro %s %Hn %Hwc %Hwp %_ %_ %_ Ho Hl _
  imod (lkInvClaim nm.xnReg L.xlLk (gtAdGd GT) s c oz (RPid L nm.xnH nm.xnM nm.xnI (gtAdGd GT))
    Hcons Hwc Hwp Hn Hcl (RPidTransportable L _ _ _ (gtAdGd GT) Hcons)) $$ [$Hl $Hnh $Hil]
    with H
  imodintro
  inext
  icases H with ⟨Hl, Hlk, HR⟩
  imodintro
  isplitr
  · ipureintro
    exact ⟨Hok, Hwk⟩
  isplitl [Ho]
  · iapply (ownInvOther (XO L) nm.xnH (gtAdGd GT) s c Hn Hnx) $$ Ho
  isplitl [Hl]
  · iexact Hl
  isplitl [Hlk]
  · iexact Hlk
  · iexact HR

/-- ACQUIRE-SUCCESS with `notheld` drawn through `flowIn`. -/
theorem fxClaim' (L : Xlay) (GT : GdexecT) (nm : Xv6N) (HL : xlayOk L)
    (Hcons : rvwmoCatConsistent (gtAdGd GT)) (c : Geid) (oz : Option Geid) (Q : IProp GF)
    (flowIn : Mea GF) :
    lkClaim L.xlLk (gtAdGd GT).gdG c oz →
    (∀ a v', gwritesByte (gtAdGd GT).gdG c a v' → a ∈ lwb L) →
    ⊢ isLock nm.xnReg L.xlLk (RPid L nm.xnH nm.xnM nm.xnI (gtAdGd GT)) -∗
      (([∗map] Rin ∈ flowIn, Rin) -∗ notheld nm.xnReg L.xlLk c.1 ∗ Q) -∗
      @flowEqDyn hlc GF _ (AxSpinX2.xG L GT nm) (gtAdGd GT) c
        (@Axpol.sPol (xv6Pol GT) (gtAdGd GT) c) flowIn
        iprop((locked nm.xnReg L.xlLk c.1 c ∗ RPid L nm.xnH nm.xnM nm.xnI (gtAdGd GT) c) ∗ Q) := by
  intro Hcl Hsg
  obtain ⟨Hnx, Hok, Hwk⟩ := lwSide L GT HL c Hsg
  iintro #Hil Hfi
  iapply fxBuild
  iintro %s %Hn %Hwc %Hwp %_ %_ %_ Ho Hl Hin
  ihave ⟨Hnh, HQ⟩ := Hfi $$ Hin
  imod (lkInvClaim nm.xnReg L.xlLk (gtAdGd GT) s c oz (RPid L nm.xnH nm.xnM nm.xnI (gtAdGd GT))
    Hcons Hwc Hwp Hn Hcl (RPidTransportable L _ _ _ (gtAdGd GT) Hcons)) $$ [$Hl $Hnh $Hil]
    with H
  imodintro
  inext
  icases H with ⟨Hl, Hlk, HR⟩
  imodintro
  isplitr
  · ipureintro
    exact ⟨Hok, Hwk⟩
  isplitl [Ho]
  · iapply (ownInvOther (XO L) nm.xnH (gtAdGd GT) s c Hn Hnx) $$ Ho
  isplitl [Hl]
  · iexact Hl
  isplitl [Hlk HR]
  · isplitl [Hlk]
    · iexact Hlk
    · iexact HR
  · iexact HQ

/-- THE RELEASE (WCrel zero store), each component of `R` from its own anchor; deposits
`notheld`. -/
theorem fxRelease' (L : Xlay) (GT : GdexecT) (nm : Xv6N) (HL : xlayOk L)
    (Hcons : rvwmoCatConsistent (gtAdGd GT)) (w : Geid) (i : Agent) (c : Geid)
    (R : Geid → IProp GF) (Rs : List (Geid → IProp GF)) (flowIn : Mea GF) :
    zw L.xlLk (gtAdGd GT).gdG w → (∀ t v, ¬ greadsByte (gtAdGd GT).gdG w L.xlLk t v) →
    (∀ a v', gwritesByte (gtAdGd GT).gdG w a v' → a ∈ lwb L) →
    (∀ Rj, Rj ∈ Rs → lkTransportable (gtAdGd GT) Rj) → (([∗list] Rj ∈ Rs, Rj w) ⊢ R w) →
    ⊢ isLock nm.xnReg L.xlLk R -∗
      (([∗map] Rin ∈ flowIn, Rin) -∗
        locked nm.xnReg L.xlLk i c ∗ [∗list] Rj ∈ Rs, ∃ a, ⌜gobCat (gtAdGd GT) a w⌝ ∗ Rj a) -∗
      @flowEqDyn hlc GF _ (AxSpinX2.xG L GT nm) (gtAdGd GT) w
        (@Axpol.sPol (xv6Pol GT) (gtAdGd GT) w) flowIn iprop(notheld nm.xnReg L.xlLk i) := by
  intro Hzw Hnr Hsg Htr HRs
  obtain ⟨Hnx, Hok, Hwk⟩ := lwSide L GT HL w Hsg
  iintro #Hil Hfi
  iapply fxBuild
  iintro %s %Hn %Hwc %Hwp %_ %_ %_ Ho Hl Hin
  ihave ⟨Hlk, HRc⟩ := Hfi $$ Hin
  ihave HRc := (transportComps (gtAdGd GT) Rs w Htr) $$ HRc
  ihave HR := HRs $$ HRc
  ihave H := (lkInvRelease nm.xnReg L.xlLk (gtAdGd GT) s w i c R Hcons Hwc Hn Hzw Hnr)
    $$ [$Hl $Hlk $Hil $HR]
  imodintro
  inext
  imod H with ⟨Hl, Hnh, -⟩
  imodintro
  isplitr
  · ipureintro
    exact ⟨Hok, Hwk⟩
  isplitl [Ho]
  · iapply (ownInvOther (XO L) nm.xnH (gtAdGd GT) s w Hn Hnx) $$ Ho
  isplitl [Hl]
  · iexact Hl
  · iexact Hnh

/-- The release with `R := RPid` and its two components drawn from two anchors (lk->cpu at the
release's `sd lk->cpu ← 0`, nextpid at the CS's `sw nextpid`). -/
theorem fxReleasePid (L : Xlay) (GT : GdexecT) (nm : Xv6N) (HL : xlayOk L)
    (Hcons : rvwmoCatConsistent (gtAdGd GT)) (w : Geid) (i : Agent) (c a1 a2 : Geid)
    (flowIn : Mea GF) :
    zw L.xlLk (gtAdGd GT).gdG w → (∀ t v, ¬ greadsByte (gtAdGd GT).gdG w L.xlLk t v) →
    (∀ a v', gwritesByte (gtAdGd GT).gdG w a v' → a ∈ lwb L) →
    gobCat (gtAdGd GT) a1 w → gobCat (gtAdGd GT) a2 w →
    ⊢ isLock nm.xnReg L.xlLk (RPid L nm.xnH nm.xnM nm.xnI (gtAdGd GT)) -∗
      (([∗map] Rin ∈ flowIn, Rin) -∗
        locked nm.xnReg L.xlLk i c ∗ RCpu L nm.xnH (gtAdGd GT) a1 ∗
          RNp L nm.xnH nm.xnM nm.xnI (gtAdGd GT) a2) -∗
      @flowEqDyn hlc GF _ (AxSpinX2.xG L GT nm) (gtAdGd GT) w
        (@Axpol.sPol (xv6Pol GT) (gtAdGd GT) w) flowIn iprop(notheld nm.xnReg L.xlLk i) := by
  intro Hzw Hnr Hsg Ho1 Ho2
  let Rs : List (Geid → IProp GF) :=
    [RCpu L nm.xnH (gtAdGd GT), RNp L nm.xnH nm.xnM nm.xnI (gtAdGd GT)]
  have HF : ∀ Rj, Rj ∈ Rs → lkTransportable (gtAdGd GT) Rj := by
    intro Rj h
    rcases List.mem_cons.1 h with rfl | h
    · exact RCpuTransportable L _ (gtAdGd GT) Hcons
    rcases List.mem_cons.1 h with rfl | h
    · exact RNpTransportable L _ _ _ (gtAdGd GT) Hcons
    · exact absurd h List.not_mem_nil
  have HRs : ([∗list] Rj ∈ Rs, Rj w) ⊢ RPid L nm.xnH nm.xnM nm.xnI (gtAdGd GT) w := by
    iintro H
    icases BigSepL.bigSepL_cons.1 $$ H with ⟨H1, H⟩
    icases BigSepL.bigSepL_cons.1 $$ H with ⟨H2, -⟩
    unfold RPid
    isplitl [H1]
    · iexact H1
    · iexact H2
  iintro #Hil Hfi
  iapply (fxRelease' L GT nm HL Hcons w i c (RPid L nm.xnH nm.xnM nm.xnI (gtAdGd GT)) Rs flowIn
    Hzw Hnr Hsg HF HRs) $$ Hil
  iintro Hin
  ihave ⟨Hlk, H1, H2⟩ := Hfi $$ Hin
  isplitl [Hlk]
  · iexact Hlk
  iapply BigSepL.bigSepL_cons.2
  isplitl [H1]
  · iexists a1
    isplitr
    · ipureintro
      exact Ho1
    · iexact H1
  iapply BigSepL.bigSepL_cons.2
  isplitl [H2]
  · iexists a2
    isplitr
    · ipureintro
      exact Ho2
    · iexact H2
  · iapply BigSepL.bigSepL_nil.2
    iempintro

/-- THE HOLDER's `lw lk`: `locked` through `flowIn`, deposits it back and `⌜v ≠ 0⌝` at the
read. -/
theorem fxLkreadHeld (L : Xlay) (GT : GdexecT) (nm : Xv6N) (_HL : xlayOk L)
    (Hcons : rvwmoCatConsistent (gtAdGd GT)) (r : Geid) (i : Agent) (c : Geid) (Q : IProp GF)
    (flowIn : Mea GF) :
    gisW (gtAdGd GT).gdG r = false → WeakRvwmoGraph.gpo (gtAdGd GT).gdG c r →
    nolk L.xlLk (gtAdGd GT).gdG c r →
    ⊢ (([∗map] Rin ∈ flowIn, Rin) -∗ locked nm.xnReg L.xlLk i c ∗ Q) -∗
      @flowEqDyn hlc GF _ (AxSpinX2.xG L GT nm) (gtAdGd GT) r
        (@Axpol.sPol (xv6Pol GT) (gtAdGd GT) r) flowIn
        iprop((locked nm.xnReg L.xlLk i c ∗ Q) ∗
          ⌜∀ t v, greadsByte (gtAdGd GT).gdG r L.xlLk t v → v ≠ b0⌝) := by
  intro Hnw Hpo Hnl
  obtain ⟨Hnx, Hok, Hwk⟩ := nwSide L GT r Hnw
  iintro Hfi
  iapply fxBuild
  iintro %s %Hn %Hwc %Hwp %_ %_ %_ Ho Hl Hin
  ihave ⟨Hlk, HQ⟩ := Hfi $$ Hin
  icases (lkInvReadHeld nm.xnReg L.xlLk (gtAdGd GT) s r i c Hcons Hwp Hn Hnw Hpo Hnl)
    $$ [$Hl $Hlk] with ⟨Hl, Hlk, %Hf⟩
  imodintro
  inext
  imodintro
  isplitr
  · ipureintro
    exact ⟨Hok, Hwk⟩
  isplitl [Ho]
  · iapply (ownInvOther (XO L) nm.xnH (gtAdGd GT) s r Hn Hnx) $$ Ho
  isplitl [Hl]
  · iexact Hl
  · isplitl [Hlk HQ]
    · isplitl [Hlk]
      · iexact Hlk
      · iexact HQ
    · ipureintro
      exact Hf

/-- Any non-write event (frame: loads of any class, fences). -/
theorem fxRead (L : Xlay) (GT : GdexecT) (nm : Xv6N) (_HL : xlayOk L)
    (Hcons : rvwmoCatConsistent (gtAdGd GT)) (r : Geid) :
    gisW (gtAdGd GT).gdG r = false →
    ⊢ @flowEqDyn hlc GF _ (AxSpinX2.xG L GT nm) (gtAdGd GT) r
        (@Axpol.sPol (xv6Pol GT) (gtAdGd GT) r) (∅ : Mea GF) iprop(True) := by
  intro Hnw
  obtain ⟨Hnx, Hok, Hwk⟩ := nwSide L GT r Hnw
  iapply fxBuild
  iintro %s %Hn %Hwc %Hwp %_ %_ %_ Ho Hl _
  imodintro
  inext
  imodintro
  isplitr
  · ipureintro
    exact ⟨Hok, Hwk⟩
  isplitl [Ho]
  · iapply (ownInvOther (XO L) nm.xnH (gtAdGd GT) s r Hn Hnx) $$ Ho
  isplitl [Hl]
  · iapply (lkInvRead nm.xnReg L.xlLk (gtAdGd GT) s r Hcons Hwp Hn Hnw) $$ Hl
  · itrivial

/-- A non-write event depositing a PURE fact derived from WOK + the handout (the builder for the
private / read-only / racy reads). -/
theorem fxReadFact (L : Xlay) (GT : GdexecT) (nm : Xv6N) (_HL : xlayOk L)
    (Hcons : rvwmoCatConsistent (gtAdGd GT)) (r : Geid) (P : Prop) :
    gisW (gtAdGd GT).gdG r = false →
    (∀ s, WC (gtAdGd GT).gdG s → WPh (gtAdGd GT).gdG s r →
      CPUOK (clb L) cvx (gtAdGd GT).gdG s → WOK L (gtAdGd GT).gdG s → r ∉ s → P) →
    ⊢ @flowEqDyn hlc GF _ (AxSpinX2.xG L GT nm) (gtAdGd GT) r
        (@Axpol.sPol (xv6Pol GT) (gtAdGd GT) r) (∅ : Mea GF) iprop(⌜P⌝) := by
  intro Hnw HP
  obtain ⟨Hnx, Hok, Hwk⟩ := nwSide L GT r Hnw
  iapply fxBuild
  iintro %s %Hn %Hwc %Hwp %_ %Hcok %Hwok Ho Hl _
  imodintro
  inext
  imodintro
  isplitr
  · ipureintro
    exact ⟨Hok, Hwk⟩
  isplitl [Ho]
  · iapply (ownInvOther (XO L) nm.xnH (gtAdGd GT) s r Hn Hnx) $$ Ho
  isplitl [Hl]
  · iapply (lkInvRead nm.xnReg L.xlLk (gtAdGd GT) s r Hcons Hwp Hn Hnw) $$ Hl
  · ipureintro
    exact HP s Hwc Hwp Hcok Hwok Hn

/-! ## OWNED BYTES (lk->cpu, nextpid) -/

/-- THE OWNED WRITE of a last-value list `Cw ⊆ XO` (lk->cpu or nextpid), Φ_cpu as side
condition. -/
theorem fxRVLWrite (L : Xlay) (GT : GdexecT) (nm : Xv6N) (HL : xlayOk L)
    (_Hcons : rvwmoCatConsistent (gtAdGd GT)) (w e : Geid) (Cw : List Int)
    (vs : List (BitVec 8)) (Q : IProp GF) (flowIn : Mea GF) :
    gisW (gtAdGd GT).gdG w = true → gmoLt (gtAdGd GT).gdG e w → vs.length = Cw.length →
    (∀ (j : Nat) a v, Cw[j]? = some a → vs[j]? = some v → gwritesByte (gtAdGd GT).gdG w a v) →
    (∀ a v, gwritesByte (gtAdGd GT).gdG w a v → a ∈ Cw) → (∀ a, a ∈ Cw → a ∈ XO L) →
    cpuOk (clb L) cvx (gtAdGd GT).gdG w →
    ⊢ (([∗map] Rin ∈ flowIn, Rin) -∗ Q ∗ ∃ vold, RVL nm.xnH (gtAdGd GT) Cw e vold) -∗
      @flowEqDyn hlc GF _ (AxSpinX2.xG L GT nm) (gtAdGd GT) w
        (@Axpol.sPol (xv6Pol GT) (gtAdGd GT) w) flowIn
        iprop(Q ∗ RVL nm.xnH (gtAdGd GT) Cw w vs) := by
  intro Hisw Hew Hlen Hall Honly HX Hok
  obtain ⟨Hnlk, Hwk⟩ := xoSide L GT HL w Cw Honly HX
  iintro Hfi
  iapply fxBuild
  iintro %s %Hn %_ %_ %_ %_ %_ Ho Hl Hin
  ihave ⟨HQ, %vold, HR⟩ := Hfi $$ Hin
  imod (RVLWrite nm.xnH (gtAdGd GT) (XO L) Cw s e w vold vs Hn Hew Hlen Hall Honly)
    $$ [$Ho $HR] with ⟨Ho, HR⟩
  imodintro
  inext
  imodintro
  isplitr
  · ipureintro
    exact ⟨Hok, Hwk⟩
  isplitl [Ho]
  · iexact Ho
  isplitl [Hl]
  · iapply (lkInvOther nm.xnReg L.xlLk (gtAdGd GT) s w Hn Hnlk
      (fun ⟨_, Hnw⟩ => by rw [Hisw] at Hnw; cases Hnw)) $$ Hl
  · isplitl [HQ]
    · iexact HQ
    · iexact HR

/-- lk->cpu: the holder's `sd` of `cvx w.1` (acquire's `lk->cpu = mycpu()`) or of 0 (release's
`lk->cpu = 0`) -- Φ_cpu FROM THE VALUE. -/
theorem fxCpuWrite (L : Xlay) (GT : GdexecT) (nm : Xv6N) (HL : xlayOk L)
    (Hcons : rvwmoCatConsistent (gtAdGd GT)) (w e : Geid) (vs : List (BitVec 8)) (Q : IProp GF)
    (flowIn : Mea GF) :
    gisW (gtAdGd GT).gdG w = true → gmoLt (gtAdGd GT).gdG e w →
    (vs = cvx w.1 ∨ vs = List.replicate 8 b0) →
    (∀ (j : Nat) a v, (clb L)[j]? = some a → vs[j]? = some v →
      gwritesByte (gtAdGd GT).gdG w a v) →
    (∀ a v, gwritesByte (gtAdGd GT).gdG w a v → a ∈ clb L) →
    ⊢ (([∗map] Rin ∈ flowIn, Rin) -∗ Q ∗ ∃ vold, RVL nm.xnH (gtAdGd GT) (clb L) e vold) -∗
      @flowEqDyn hlc GF _ (AxSpinX2.xG L GT nm) (gtAdGd GT) w
        (@Axpol.sPol (xv6Pol GT) (gtAdGd GT) w) flowIn
        iprop(Q ∗ RVL nm.xnH (gtAdGd GT) (clb L) w vs) := by
  intro Hisw Hew Hv Hall Honly
  have hc : (clb L).length = 8 := by simp [clb, clRange]
  have Hlen : vs.length = (clb L).length := by
    rw [hc]
    rcases Hv with rfl | rfl
    · exact cvxLength _
    · exact List.length_replicate
  have Hok : cpuOk (clb L) cvx (gtAdGd GT).gdG w := by
    have Hw : wval (clb L) (gtAdGd GT).gdG w vs := by
      intro j a v Hj Hwb
      have hjl : j < vs.length := by
        rw [Hlen]
        exact (List.getElem?_eq_some_iff.1 Hj).1
      have Hv' : vs[j]? = some vs[j] := List.getElem?_eq_getElem hjl
      exact Hv'.trans (congrArg some (gwritesByteDet _ _ _ _ _ (Hall j a _ Hj Hv') Hwb))
    rcases Hv with rfl | rfl
    · exact Or.inr Hw
    · left
      rw [hc]
      exact Hw
  exact fxRVLWrite L GT nm HL Hcons w e (clb L) vs Q flowIn Hisw Hew Hlen Hall Honly (clbXO L)
    Hok

/-- nextpid: the owned write (exact value). -/
theorem fxNpWrite (L : Xlay) (GT : GdexecT) (nm : Xv6N) (HL : xlayOk L)
    (Hcons : rvwmoCatConsistent (gtAdGd GT)) (w e : Geid) (vs : List (BitVec 8)) (Q : IProp GF)
    (flowIn : Mea GF) :
    gisW (gtAdGd GT).gdG w = true → gmoLt (gtAdGd GT).gdG e w → vs.length = 4 →
    (∀ (j : Nat) a v, (npb L)[j]? = some a → vs[j]? = some v →
      gwritesByte (gtAdGd GT).gdG w a v) →
    (∀ a v, gwritesByte (gtAdGd GT).gdG w a v → a ∈ npb L) →
    ⊢ (([∗map] Rin ∈ flowIn, Rin) -∗ Q ∗ ∃ vold, RVL nm.xnH (gtAdGd GT) (npb L) e vold) -∗
      @flowEqDyn hlc GF _ (AxSpinX2.xG L GT nm) (gtAdGd GT) w
        (@Axpol.sPol (xv6Pol GT) (gtAdGd GT) w) flowIn
        iprop(Q ∗ RVL nm.xnH (gtAdGd GT) (npb L) w vs) := by
  intro Hisw Hew Hlen Hall Honly
  have Hlen' : vs.length = (npb L).length := by
    rw [Hlen]
    simp [npb, clRange]
  have Hok : cpuOk (clb L) cvx (gtAdGd GT).gdG w := by
    apply cpuOkNw
    intro a v Ha Hw
    exact clbNpbDisj L HL a Ha (Honly a v Hw)
  exact fxRVLWrite L GT nm HL Hcons w e (npb L) vs Q flowIn Hisw Hew Hlen' Hall Honly (npbXO L)
    Hok

/-- (b)/(e) THE OWNED LAST-VALUE READ (gmo case): the handle drawn through `flowIn` at an
anchor `e` gmo-before `r`; deposits the handle back and the read values AT THE READ. -/
theorem fxOwnedRead (L : Xlay) (GT : GdexecT) (nm : Xv6N) (_HL : xlayOk L)
    (Hcons : rvwmoCatConsistent (gtAdGd GT)) (r e : Geid) (Cw : List Int) (vs : List (BitVec 8))
    (Q : IProp GF) (flowIn : Mea GF) :
    gisW (gtAdGd GT).gdG r = false → (∀ a, a ∈ Cw → a ∈ XO L) → gmoLt (gtAdGd GT).gdG e r →
    (∀ w a v', a ∈ Cw → gwritesByte (gtAdGd GT).gdG w a v' →
      WeakRvwmoGraph.gpo (gtAdGd GT).gdG w r → gmoLt (gtAdGd GT).gdG w r) →
    ⊢ (([∗map] Rin ∈ flowIn, Rin) -∗ Q ∗ RVL nm.xnH (gtAdGd GT) Cw e vs) -∗
      @flowEqDyn hlc GF _ (AxSpinX2.xG L GT nm) (gtAdGd GT) r
        (@Axpol.sPol (xv6Pol GT) (gtAdGd GT) r) flowIn
        iprop((Q ∗ RVL nm.xnH (gtAdGd GT) Cw e vs) ∗
          ⌜∀ (j : Nat) a t v, Cw[j]? = some a → greadsByte (gtAdGd GT).gdG r a t v →
            vs[j]? = some v⌝) := by
  intro Hnw HX Her Hpo
  obtain ⟨Hnx, Hok, Hwk⟩ := nwSide L GT r Hnw
  iintro Hfi
  iapply fxBuild
  iintro %s %Hn %Hwc %Hwp %_ %_ %_ #Ho Hl Hin
  ihave ⟨HQ, HR⟩ := Hfi $$ Hin
  ihave ⟨HR, %Hv⟩ := (RVLRead nm.xnH (gtAdGd GT) (XO L) s Cw e r vs Hcons HX Her Hwp Hpo)
    $$ [$Ho $HR]
  imodintro
  inext
  imodintro
  isplitr
  · ipureintro
    exact ⟨Hok, Hwk⟩
  isplitl []
  · iapply (ownInvOther (XO L) nm.xnH (gtAdGd GT) s r Hn Hnx) $$ Ho
  isplitl [Hl]
  · iapply (lkInvRead nm.xnReg L.xlLk (gtAdGd GT) s r Hcons Hwp Hn Hnw) $$ Hl
  · isplitl [HQ HR]
    · isplitl [HQ]
      · iexact HQ
      · iexact HR
    · ipureintro
      exact Hv

/-- (b) THE FORWARDED CASE: the hart's own store `w` (data `vs` at `Cw`) is NOT gmo-before its
read `r`: nothing drawn, the value is the pure forwarding fact, deposited at the read. -/
theorem fxFwdRead (L : Xlay) (GT : GdexecT) (nm : Xv6N) (HL : xlayOk L)
    (Hcons : rvwmoCatConsistent (gtAdGd GT)) (r w : Geid) (Cw : List Int)
    (vs : List (BitVec 8)) :
    gisW (gtAdGd GT).gdG r = false → WeakRvwmoGraph.gpo (gtAdGd GT).gdG w r →
    ¬ gmoLt (gtAdGd GT).gdG w r →
    (∀ (j : Nat) a v, Cw[j]? = some a → vs[j]? = some v → gwritesByte (gtAdGd GT).gdG w a v) →
    vs.length = Cw.length →
    (∀ w' a v', a ∈ Cw → gwritesByte (gtAdGd GT).gdG w' a v' →
      WeakRvwmoGraph.gpo (gtAdGd GT).gdG w w' → WeakRvwmoGraph.gpo (gtAdGd GT).gdG w' r →
      False) →
    ⊢ @flowEqDyn hlc GF _ (AxSpinX2.xG L GT nm) (gtAdGd GT) r
        (@Axpol.sPol (xv6Pol GT) (gtAdGd GT) r) (∅ : Mea GF)
        iprop(⌜∀ (j : Nat) a t v, Cw[j]? = some a → greadsByte (gtAdGd GT).gdG r a t v →
          vs[j]? = some v⌝) := by
  intro Hnw Hpo Hnlt Hall Hlen Hnb
  exact fxReadFact L GT nm HL Hcons r _ Hnw
    (fun _ _ _ _ _ _ => fwdReadVal (gtAdGd GT) Hcons r w Cw vs Hpo Hnlt Hall Hlen Hnb)

/-- THE RACY lk->cpu READ (non-holder): `rdFact` at the read. -/
theorem fxCpuRacy (L : Xlay) (GT : GdexecT) (nm : Xv6N) (HL : xlayOk L)
    (Hcons : rvwmoCatConsistent (gtAdGd GT)) (r : Geid) :
    gisW (gtAdGd GT).gdG r = false →
    ⊢ @flowEqDyn hlc GF _ (AxSpinX2.xG L GT nm) (gtAdGd GT) r
        (@Axpol.sPol (xv6Pol GT) (gtAdGd GT) r) (∅ : Mea GF)
        iprop(⌜rdFact (clb L) cvx (gtAdGd GT).gdG r⌝) := by
  intro Hnw
  refine fxReadFact L GT nm HL Hcons r _ Hnw ?_
  intro s Hwc Hwp Hok _ _ a t v _ Hrd
  have Hs := (Hcons.2.2.1 r a t v Hrd).1
  cases t with
  | zero => exact Or.inl ⟨rfl, Hs⟩
  | succ j =>
    right
    obtain ⟨w, Hat, Hw, Hvis⟩ := Hs
    refine ⟨w, Hat, Hw, ?_⟩
    by_cases Heq : w.1 = r.1
    · exact Or.inr ⟨Heq, Hvis⟩
    · refine Or.inl ⟨Heq, Hok w (Hwp w (WeakRvwmoGraph.gwritesByteGisW _ _ _ _ Hw) ?_)⟩
      exact catGrfeGmo (gtAdGd GT) w r Hcons ⟨⟨a, j + 1, v, Hrd, Hat⟩, Heq⟩

/-! ## PRIVATE (stack words, struct-cpu fields) -/

/-- st_rule's instance side: hart `w.1`'s store to its OWN private bytes. -/
theorem fxPrivWrite (L : Xlay) (GT : GdexecT) (nm : Xv6N) (HL : xlayOk L)
    (_Hcons : rvwmoCatConsistent (gtAdGd GT)) (w : Geid) :
    gisW (gtAdGd GT).gdG w = true →
    (∀ a v, gwritesByte (gtAdGd GT).gdG w a v → priv L a w.1) →
    ⊢ @flowEqDyn hlc GF _ (AxSpinX2.xG L GT nm) (gtAdGd GT) w
        (@Axpol.sPol (xv6Pol GT) (gtAdGd GT) w) (∅ : Mea GF) iprop(True) := by
  intro Hisw Hsg
  obtain ⟨Hnx, Hnlk, Hok, Hwk⟩ := privSide L GT HL w Hsg
  iapply fxBuild
  iintro %s %Hn %_ %_ %_ %_ %_ Ho Hl _
  imodintro
  inext
  imodintro
  isplitr
  · ipureintro
    exact ⟨Hok, Hwk⟩
  isplitl [Ho]
  · iapply (ownInvOther (XO L) nm.xnH (gtAdGd GT) s w Hn Hnx) $$ Ho
  isplitl [Hl]
  · iapply (lkInvOther nm.xnReg L.xlLk (gtAdGd GT) s w Hn Hnlk
      (fun ⟨_, Hnw⟩ => by rw [Hisw] at Hnw; cases Hnw)) $$ Hl
  · itrivial

/-- ld_rule's instance side: the owned RELOAD of `a` (private to `r`'s hart) after the store `w`
(data `b`), `w` r's po-latest store to `a` (ROW fact): deposits `⌜value = b⌝` at the read. -/
theorem fxPrivRead (L : Xlay) (GT : GdexecT) (nm : Xv6N) (HL : xlayOk L)
    (Hcons : rvwmoCatConsistent (gtAdGd GT)) (r w : Geid) (a : Int) (b : BitVec 8) :
    gisW (gtAdGd GT).gdG r = false → priv L a r.1 →
    gwritesByte (gtAdGd GT).gdG w a b → WeakRvwmoGraph.gpo (gtAdGd GT).gdG w r →
    (∀ w' v', gwritesByte (gtAdGd GT).gdG w' a v' → WeakRvwmoGraph.gpo (gtAdGd GT).gdG w' r →
      w' = w ∨ WeakRvwmoGraph.gpo (gtAdGd GT).gdG w' w) →
    ⊢ @flowEqDyn hlc GF _ (AxSpinX2.xG L GT nm) (gtAdGd GT) r
        (@Axpol.sPol (xv6Pol GT) (gtAdGd GT) r) (∅ : Mea GF)
        iprop(⌜∀ t v, greadsByte (gtAdGd GT).gdG r a t v → v = b⌝) := by
  intro Hnw Hpr Hw Hwr Hlast
  exact fxReadFact L GT nm HL Hcons r _ Hnw (fun s _ Hwp _ Hwok _ =>
    privReadVal L HL (gtAdGd GT) Hcons s r a w b Hwok Hwp Hpr Hnw Hw Hwr Hlast)

/-- The n-byte reload (a `ld` of a spilled 8-byte word): every byte. -/
theorem fxPrivReadn (L : Xlay) (GT : GdexecT) (nm : Xv6N) (HL : xlayOk L)
    (Hcons : rvwmoCatConsistent (gtAdGd GT)) (r w : Geid) (Cw : List Int)
    (vs : List (BitVec 8)) :
    gisW (gtAdGd GT).gdG r = false → (∀ a, a ∈ Cw → priv L a r.1) →
    (∀ (j : Nat) a v, Cw[j]? = some a → vs[j]? = some v → gwritesByte (gtAdGd GT).gdG w a v) →
    vs.length = Cw.length → WeakRvwmoGraph.gpo (gtAdGd GT).gdG w r →
    (∀ w' a v', a ∈ Cw → gwritesByte (gtAdGd GT).gdG w' a v' →
      WeakRvwmoGraph.gpo (gtAdGd GT).gdG w' r →
      w' = w ∨ WeakRvwmoGraph.gpo (gtAdGd GT).gdG w' w) →
    ⊢ @flowEqDyn hlc GF _ (AxSpinX2.xG L GT nm) (gtAdGd GT) r
        (@Axpol.sPol (xv6Pol GT) (gtAdGd GT) r) (∅ : Mea GF)
        iprop(⌜∀ (j : Nat) a t v, Cw[j]? = some a → greadsByte (gtAdGd GT).gdG r a t v →
          vs[j]? = some v⌝) := by
  intro Hnw Hpr Hall Hlen Hwr Hlast
  refine fxReadFact L GT nm HL Hcons r _ Hnw ?_
  intro s _ Hwp _ Hwok _ j a t v Hj Hrd
  have hjl : j < vs.length := by
    rw [Hlen]
    exact (List.getElem?_eq_some_iff.1 Hj).1
  have Hb : vs[j]? = some vs[j] := List.getElem?_eq_getElem hjl
  have Ha : a ∈ Cw := List.mem_of_getElem? Hj
  rw [Hb, privReadVal L HL (gtAdGd GT) Hcons s r a w _ Hwok Hwp (Hpr a Ha) Hnw
    (Hall j a _ Hj Hb) Hwr (fun w' v' Hw' Hp => Hlast w' a v' Ha Hw' Hp) t v Hrd]

/-- The genesis arm of the private read (no po-earlier store). -/
theorem fxPrivRead0 (L : Xlay) (GT : GdexecT) (nm : Xv6N) (HL : xlayOk L)
    (Hcons : rvwmoCatConsistent (gtAdGd GT)) (r : Geid) (a : Int) :
    gisW (gtAdGd GT).gdG r = false → priv L a r.1 →
    (∀ w' v', gwritesByte (gtAdGd GT).gdG w' a v' → WeakRvwmoGraph.gpo (gtAdGd GT).gdG w' r →
      False) →
    ⊢ @flowEqDyn hlc GF _ (AxSpinX2.xG L GT nm) (gtAdGd GT) r
        (@Axpol.sPol (xv6Pol GT) (gtAdGd GT) r) (∅ : Mea GF)
        iprop(⌜∀ t v, greadsByte (gtAdGd GT).gdG r a t v →
          t = 0 ∧ (gtAdGd GT).gdG.gxImg a = some v⌝) := by
  intro Hnw Hpr Hnone
  exact fxReadFact L GT nm HL Hcons r _ Hnw (fun s _ Hwp _ Hwok _ =>
    privReadImg L HL (gtAdGd GT) Hcons s r a Hwok Hwp Hpr Hnw Hnone)

/-! ## READ-ONLY (text, PTE pages): the image arm -/

theorem fxRoRead (L : Xlay) (GT : GdexecT) (nm : Xv6N) (HL : xlayOk L)
    (Hcons : rvwmoCatConsistent (gtAdGd GT)) (r : Geid) (a : Int) :
    gisW (gtAdGd GT).gdG r = false → L.xlRo a →
    (∀ w' v', gwritesByte (gtAdGd GT).gdG w' a v' → WeakRvwmoGraph.gpo (gtAdGd GT).gdG w' r →
      False) →
    ⊢ @flowEqDyn hlc GF _ (AxSpinX2.xG L GT nm) (gtAdGd GT) r
        (@Axpol.sPol (xv6Pol GT) (gtAdGd GT) r) (∅ : Mea GF)
        iprop(⌜∀ t v, greadsByte (gtAdGd GT).gdG r a t v →
          t = 0 ∧ (gtAdGd GT).gdG.gxImg a = some v⌝) := by
  intro Hnw Hro Hnone
  exact fxReadFact L GT nm HL Hcons r _ Hnw (fun s _ Hwp _ Hwok _ =>
    roReadImg L HL (gtAdGd GT) Hcons s r a Hwok Hwp Hro Hnone)

/-- The n-byte read-only read (an 8-byte `ld` of a text / PTE word). -/
theorem fxRoReadn (L : Xlay) (GT : GdexecT) (nm : Xv6N) (HL : xlayOk L)
    (Hcons : rvwmoCatConsistent (gtAdGd GT)) (r : Geid) (Cw : List Int) :
    gisW (gtAdGd GT).gdG r = false → (∀ a, a ∈ Cw → L.xlRo a) →
    (∀ w' a v', a ∈ Cw → gwritesByte (gtAdGd GT).gdG w' a v' →
      WeakRvwmoGraph.gpo (gtAdGd GT).gdG w' r → False) →
    ⊢ @flowEqDyn hlc GF _ (AxSpinX2.xG L GT nm) (gtAdGd GT) r
        (@Axpol.sPol (xv6Pol GT) (gtAdGd GT) r) (∅ : Mea GF)
        iprop(⌜∀ a t v, a ∈ Cw → greadsByte (gtAdGd GT).gdG r a t v →
          t = 0 ∧ (gtAdGd GT).gdG.gxImg a = some v⌝) := by
  intro Hnw Hro Hnone
  exact fxReadFact L GT nm HL Hcons r _ Hnw (fun s _ Hwp _ Hwok _ a t v Ha Hrd =>
    roReadImg L HL (gtAdGd GT) Hcons s r a Hwok Hwp (Hro a Ha)
      (fun w' v' => Hnone w' a v' Ha) t v Hrd)

/-! ## nextpid inside the critical section, with Theorem 2's ghosts -/

/-- The CS's `lw nextpid`: `RNp` through `flowIn` at an anchor `e` gmo-before the read;
deposits `RNp` back EXPOSING its value `v` and `⌜lw read the bytes of v⌝`, AT THE READ. -/
theorem fxNpRead (L : Xlay) (GT : GdexecT) (nm : Xv6N) (_HL : xlayOk L)
    (Hcons : rvwmoCatConsistent (gtAdGd GT)) (r e : Geid) (Q : IProp GF) (flowIn : Mea GF) :
    gisW (gtAdGd GT).gdG r = false → gmoLt (gtAdGd GT).gdG e r →
    (∀ w a v', a ∈ npb L → gwritesByte (gtAdGd GT).gdG w a v' →
      WeakRvwmoGraph.gpo (gtAdGd GT).gdG w r → gmoLt (gtAdGd GT).gdG w r) →
    ⊢ (([∗map] Rin ∈ flowIn, Rin) -∗ Q ∗ RNp L nm.xnH nm.xnM nm.xnI (gtAdGd GT) e) -∗
      @flowEqDyn hlc GF _ (AxSpinX2.xG L GT nm) (gtAdGd GT) r
        (@Axpol.sPol (xv6Pol GT) (gtAdGd GT) r) flowIn
        iprop(Q ∗ ∃ v, RNpv L GT nm e v ∗
          ⌜∀ (j : Nat) a t b, (npb L)[j]? = some a → greadsByte (gtAdGd GT).gdG r a t b →
            (WeakInterpProj.wbytes 4 (BitVec.ofInt 32 v))[j]? = some b⌝) := by
  intro Hnw Her Hpo
  obtain ⟨Hnx, Hok, Hwk⟩ := nwSide L GT r Hnw
  unfold RNp RNpv
  iintro Hfi
  iapply fxBuild
  iintro %s %Hn %Hwc %Hwp %_ %_ %_ #Ho Hl Hin
  ihave ⟨HQ, %v, %Hv, HR, Hm, HS⟩ := Hfi $$ Hin
  ihave ⟨HR, %Hf⟩ := (RVLRead nm.xnH (gtAdGd GT) (XO L) s (npb L) e r _ Hcons (npbXO L) Her Hwp
    Hpo) $$ [$Ho $HR]
  imodintro
  inext
  imodintro
  isplitr
  · ipureintro
    exact ⟨Hok, Hwk⟩
  isplitl []
  · iapply (ownInvOther (XO L) nm.xnH (gtAdGd GT) s r Hn Hnx) $$ Ho
  isplitl [Hl]
  · iapply (lkInvRead nm.xnReg L.xlLk (gtAdGd GT) s r Hcons Hwp Hn Hnw) $$ Hl
  isplitl [HQ]
  · iexact HQ
  · iexists v
    isplitl [HR Hm HS]
    · isplitr
      · ipureintro
        exact Hv
      isplitl [HR]
      · iexact HR
      isplitl [Hm]
      · iexact Hm
      · iexact HS
    · ipureintro
      exact Hf

/-- The CS's `sw nextpid ← v+1`: draws `RNp` at value `v` together with the `lw`'s fact; the
ROW premise `Hdata` says the store writes the bytes of `v+1` whenever the `lw` read the bytes of
`v` (and that the increment does not wrap).  Re-establishes `RNp` at `w` with value `v+1`,
●mono v → v+1, and MINTS the exclusive ◯{v} (deposited with the read fact). -/
theorem fxNpIncr (L : Xlay) (GT : GdexecT) (nm : Xv6N) (HL : xlayOk L)
    (_Hcons : rvwmoCatConsistent (gtAdGd GT)) (w r e : Geid) (Q : IProp GF) (flowIn : Mea GF) :
    gisW (gtAdGd GT).gdG w = true → gmoLt (gtAdGd GT).gdG e w →
    (∀ a v', gwritesByte (gtAdGd GT).gdG w a v' → a ∈ npb L) →
    (∀ v : Int, 0 ≤ v ∧ v < 2 ^ 32 →
      (∀ (j : Nat) a t b, (npb L)[j]? = some a → greadsByte (gtAdGd GT).gdG r a t b →
        (WeakInterpProj.wbytes 4 (BitVec.ofInt 32 v))[j]? = some b) →
      v + 1 < 2 ^ 32 ∧
      ∀ (j : Nat) a b, (npb L)[j]? = some a →
        (WeakInterpProj.wbytes 4 (BitVec.ofInt 32 (v + 1)))[j]? = some b →
        gwritesByte (gtAdGd GT).gdG w a b) →
    ⊢ (([∗map] Rin ∈ flowIn, Rin) -∗
        Q ∗ ∃ v, RNpv L GT nm e v ∗
          ⌜∀ (j : Nat) a t b, (npb L)[j]? = some a → greadsByte (gtAdGd GT).gdG r a t b →
            (WeakInterpProj.wbytes 4 (BitVec.ofInt 32 v))[j]? = some b⌝) -∗
      @flowEqDyn hlc GF _ (AxSpinX2.xG L GT nm) (gtAdGd GT) w
        (@Axpol.sPol (xv6Pol GT) (gtAdGd GT) w) flowIn
        iprop(Q ∗ RNp L nm.xnH nm.xnM nm.xnI (gtAdGd GT) w ∗
          ∃ v, issuedFrag nm.xnI v ∗
            ⌜∀ (j : Nat) a t b, (npb L)[j]? = some a → greadsByte (gtAdGd GT).gdG r a t b →
              (WeakInterpProj.wbytes 4 (BitVec.ofInt 32 v))[j]? = some b⌝) := by
  intro Hisw Hew Honly Hdata
  obtain ⟨Hnlk, Hwk⟩ := xoSide L GT HL w (npb L) Honly (npbXO L)
  have Hok : cpuOk (clb L) cvx (gtAdGd GT).gdG w := by
    apply cpuOkNw
    intro a v Ha Hw
    exact clbNpbDisj L HL a Ha (Honly a v Hw)
  unfold RNp RNpv
  iintro Hfi
  iapply fxBuild
  iintro %s %Hn %_ %_ %_ %_ %_ Ho Hl Hin
  ihave ⟨HQ, %v, ⟨%Hv, HR, Hm, %S, HS, %HS⟩, %Hrd⟩ := Hfi $$ Hin
  obtain ⟨Hnw, Hwr⟩ := Hdata v Hv Hrd
  have Hlen : (WeakInterpProj.wbytes 4 (BitVec.ofInt 32 (v + 1))).length = (npb L).length := by
    rw [wbytesLength]
    simp [npb, clRange]
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
  isplitl [Hl]
  · iapply (lkInvOther nm.xnReg L.xlLk (gtAdGd GT) s w Hn Hnlk
      (fun ⟨_, Hnw'⟩ => by rw [Hisw] at Hnw'; cases Hnw')) $$ Hl
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
      exact Hrd

/-! ## BLOCKED: a flow equation for a write of a byte its writer may not write (read-only,
unknown, another hart's private byte) refutes the protocol state it runs on -- no rule for it
exists. -/

theorem fxBlocked (L : Xlay) (GT : GdexecT) (nm : Xv6N) (e : Geid) (a : Int) (v : BitVec 8)
    (σ : Unit) (s : GSet Geid) (flowIn : Mea GF) (R : IProp GF) :
    gwritesByte (gtAdGd GT).gdG e a v → ¬ wok L a e.1 →
    @Axpol.sPol (xv6Pol GT) (gtAdGd GT) e ⊆ s → e ∉ s →
    ⊢ @flowEqDyn hlc GF _ (AxSpinX2.xG L GT nm) (gtAdGd GT) e
        (@Axpol.sPol (xv6Pol GT) (gtAdGd GT) e) flowIn R -∗
      protXv6 L nm (gtAdGd GT) σ s -∗
      ([∗map] Rin ∈ flowIn, Rin) ={⊤,∅}=∗ ▷ |={∅,⊤}=> iprop(False) := by
  intro Hw Hnok Hsub Hn
  unfold flowEqDyn
  iintro Hfe Hob Hfi
  ihave Hob := (show protXv6 L nm (gtAdGd GT) σ s ⊢
    @AxirisG.obStInterp GF (AxSpinX2.xG L GT nm) (gtAdGd GT) σ s from .rfl) $$ Hob
  imod Hfe $$ %σ %s %Hsub %Hn Hob Hfi with H
  imodintro
  inext
  imod H with ⟨%σ', Hob, -⟩
  ihave Hob := (show @AxirisG.obStInterp GF (AxSpinX2.xG L GT nm) (gtAdGd GT) σ'
      (({e} : GSet Geid) ∪ s) ⊢ protXv6 L nm (gtAdGd GT) σ' (({e} : GSet Geid) ∪ s)
    from .rfl) $$ Hob
  unfold protXv6
  icases Hob with ⟨%Hp, -, -⟩
  exact (Hnok (Hp.2.2 e a v (elemOfUnionL (elemOfSingleton.2 rfl)) Hw)).elim

end rulesX

end Weak
