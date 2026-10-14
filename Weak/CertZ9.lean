/-
Weak: **W10-4 [OWN.94] (N2′), increment 1 — THE WALK INVARIANT "LOCKSTEP OR TAINTED"** (the coordinator's
revised decision (3); `PROGRESS-W10N2p.md`).  Lean-only, no Rocq twin.

The lockstep chain (`CertZ5`–`CertZ8`) asks every read's value to agree with the latest bytes; on a
racy-cyclic graph that fails somewhere, and the hart must run OFF its emission (a poisoned read, a
tainted register file) until it re-converges (pinned twin: `WeakRvwmoCert3b` §5, `csync`/`clockstep`;
`WeakRvwmoWalkb`'s `wlkInv'` with its per-site datum `wsiteSupply`).  This file widens the walk:

  §1  **`CertZ9.lockInvR`** — the walk invariant with a per-hart RELATION `Rel x n pE pC` between the
      emission's state at slot `n` and the certified state (lockstep: `pC = pE`; tainted: the site
      datum's `csync`-style relation), plus the per-hart label invariant and the order's prefix
      invariant (`CertZ8.prefInv`);
  §2  THE PER-STEP SITE DATUM **`CertZ9.hartStepR`** (W10-4's per-pc obligation, named): from the
      emission's block at the walk's fabric and a certified state related to the emission's, a
      certified step (`CertZ2.stepOkZ`) whose label is `lblReidxW` of the row's, the relation kept;
      **`CertZ9.lockstepStep`** — its lockstep instance when the values agree (`CertZ5`), the piece a
      site datum reuses wherever no read is poisoned;
  §3  **`CertZ9.walkPolOfOrdR`** — the walk policy from a walk order and the site datum (the fabric
      and enabledness as `CertZ8.schedOfOrd`);
  §4  the zero-cut supply **`CatLin.walkSupplyOfOrdStep`** (`walkSupplyCZ` from `orderSupplyCZ` and
      the named **`CatLin.stepSupplyCZ`**) and the kill **`CatLin.cycleKillOfOrdStepCZRC`**.

`stepSupplyCZ` REPLACES the lockstep-only `valueSupplyCZ` / `schedSupplyCZ` route (which cannot be
discharged on a racy-cyclic graph without the kill itself, `PROGRESS-W10N2p.md` finding 3).

Spec: the site datum is a fact of the program's Sail semantics at each site (FAITHFUL once proved per
pc; a poisoned branch read takes the GF outcome — the [OWN.63/64] value arguments); nothing assumed
of `GF`'s gmo.  Lean-only helpers file-qualified (`CertZ9.*`).
-/
import Weak.CertZ8

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open TsoShadow

/-! # 1. The widened walk invariant -/

/-- The per-hart relation between the emission's state (slot `n`) and the certified state. -/
abbrev CertZ9.HRel : Type := Nat → Nat → Pexv6 → Pexv6 → Prop

/-- **THE WALK INVARIANT, LOCKSTEP OR TAINTED.** -/
def CertZ9.lockInvR (rows : List (List Lbl)) (F : Nat → Nat → Pexv6) (Rel : CertZ9.HRel)
    (X : CertZ2.WInv) : CertZ2.WInv :=
  fun St itvOf fiOf cnt =>
    (∀ x, x < rows.length →
      cnt x ≤ (rows.getD x []).length ∧
      (∃ pC, (St.cstPst (cdEnd St.cstC))[x]? = some pC ∧ Rel x (cnt x) (F x (cnt x)) pC) ∧
      List.Forall₂ lblReidxW ((rows.getD x []).take (cnt x)) (CertZ2.hartTr St.cstC.cdTr x)) ∧
    (∀ s, s ∈ St.cstC.cdTr → s.esAg < rows.length) ∧
    X St itvOf fiOf cnt

/-! # 2. The per-step site datum -/

/-- **THE PER-STEP SITE DATUM — W10-4's per-pc obligation (named)**: at a threaded state, hart `x`'s
emission block for its slot `n` at the walk's fabric (fused, or the exclusive pair), its certified
state `pC` related to the emission's `pE` (its `wRelp` agreeing), give a certified step from `pC`
with a label `lblReidxW` of the row's (a write VERBATIM: taint never reaches it), and the relation at
the next slot. -/
def CertZ9.hartStepR (d0 : Efab) (Rel : CertZ9.HRel) : Prop :=
  ∀ (St : CycState) (itvOf : Nat → Nat → Nat) (fiOf : Nat → Nat → Bool) (x n : Nat) (lb : Lbl)
    (ws : Wstate) (ls : List Wlabel) (l : Wlabel) (pE pE' pC : Pexv6) (d' : Efab),
    CertZ.cstOkZW d0 St itvOf fiOf →
    (St.cstPst (cdEnd St.cstC))[x]? = some pC → Rel x n pE pC →
    ((candLastSt St.cstC).msWs x).wRelp = ws.wRelp → CertZ4.lblShape lb →
    ((lbFused l ∧ GraphFetchBlocks.blkOne (St.cstDv (cdEnd St.cstC)) d' ws lb ls l pE pE') ∨
      GraphFetchBlocks.blkPair (St.cstDv (cdEnd St.cstC)) d' ws lb ls l pE pE') →
    ∃ (lb' : Lbl) (pa : Pexv6) (da : Efab) (ls' : List Wlabel) (pC' : Pexv6),
      lblReidxW lb lb' ∧ CertZ2.stepOkZ St itvOf x lb' pC pa da ls' pC' d' ∧
      Rel x (n + 1) pE' pC'

/-- **`CertZ9.lockstepStep` — THE UNTAINTED STEP**: in lockstep with value agreement, the emission's
block re-answered is the step (`CertZ5.lockstepOne`/`lockstepPair`), the machine label `lblReidxW` of
the row's (`CertZ4.machLblReidx`). -/
theorem CertZ9.lockstepStep (d0 : Efab) (St : CycState) (itvOf : Nat → Nat → Nat)
    (fiOf : Nat → Nat → Bool) (x : Nat) (lb : Lbl) (ws : Wstate) (ls : List Wlabel) (l : Wlabel)
    (pE pE' : Pexv6) (d' : Efab) :
    CertZ.cstOkZW d0 St itvOf fiOf →
    ((candLastSt St.cstC).msWs x).wRelp = ws.wRelp → CertZ4.lblShape lb →
    ((lbFused l ∧ GraphFetchBlocks.blkOne (St.cstDv (cdEnd St.cstC)) d' ws lb ls l pE pE') ∨
      GraphFetchBlocks.blkPair (St.cstDv (cdEnd St.cstC)) d' ws lb ls l pE pE') →
    CertZ4.readFoot St.cstC lb →
    (∀ aq base ts vs, lb = .LLoad aq base ts vs → lrdVs St.cstC base ts.length = vs) →
    (∀ aq rl base ts rvs wvs kc, lb = .LRmw aq rl base ts rvs wvs kc →
      lrdVs St.cstC base ts.length = rvs) →
    CertZ5.fetchAgree St.cstC ls →
    ∃ (pa : Pexv6) (da : Efab),
      lblReidxW lb (CertZ4.machLbl St.cstC lb) ∧
      CertZ2.stepOkZ St itvOf x (CertZ4.machLbl St.cstC lb) pE pa da
        (ls.map (CertZ5.fetchRet St.cstC)) pE' d' := by
  intro hok hr hsh hblk hft hvl hvr hfag
  have hitv := CertZ5.itvBound d0 St itvOf fiOf hok (cdEnd St.cstC) (Nat.le_refl _) x
  rcases hblk with ⟨hfu, h1⟩ | h1
  · obtain ⟨pa, da, h⟩ := CertZ5.lockstepOne St itvOf x lb ws ls l pE pE' d' hok.1 hsh hft hr hfu h1
      hfag hvl hitv
    exact ⟨pa, da, CertZ4.machLblReidx St.cstC lb hvl hvr, h⟩
  · obtain ⟨pa, da, h⟩ := CertZ5.lockstepPair St itvOf x lb ws ls l pE pE' d' hok.1 hsh hft hr h1
      hfag hvr hitv
    exact ⟨pa, da, CertZ4.machLblReidx St.cstC lb hvl hvr, h⟩

/-! # 3. The walk policy from the order and the site datum -/

/-- **`CertZ9.walkPolOfOrdR`**: walking `L` in order, each step is the site datum's (its block at
the walk's fabric: the fabric event is the `m`-th of `gfDev`, the walk's fabric `fab m`; a
contact-free block at any fabric), the invariant kept. -/
theorem CertZ9.walkPolOfOrdR (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (GF : Gfexec)
    (D : Nat → CertZ7.EmData) (L : List Geid) (Rel : CertZ9.HRel) :
    CertZ7.emDataOk boot fab GF D → GF.gfDev.Nodup →
    CertZ8.walkOrd GF.gfGd.gdG.gxProg GF.gfDev L →
    (∀ e, e ∈ GF.gfDev → e ∈ L) →
    (∀ (x n : Nat) (lb : Lbl), (GF.gfGd.gdG.gxProg.getD x [])[n]? = some lb → CertZ4.lblShape lb) →
    CertZ9.hartStepR d0 Rel →
    CertZ2.walkPolZ d0 GF.gfGd.gdG.gxProg
      (CertZ9.lockInvR GF.gfGd.gdG.gxProg (fun x => (D x).f) Rel (CertZ8.prefInv L GF.gfDev fab)) := by
  intro hD hdnd hord hsub hshape hstep St itvOf fiOf cnt hok hinv hnd
  obtain ⟨hper, hagt, ⟨k, hkL, hcnt, hfab, hags⟩⟩ := hinv
  obtain ⟨y0, hy0, hy0c⟩ := hnd
  have hkl : k < L.length := by
    refine Nat.lt_of_le_of_ne hkL (fun he => ?_)
    rw [hcnt y0, he, List.take_length, CertZ8.countAll _ _ L y0 hord hy0] at hy0c
    omega
  obtain ⟨⟨x, a⟩, hk⟩ : ∃ e, L[k]? = some e := ⟨L[k], List.getElem?_eq_getElem hkl⟩
  have hev := (hord.2.1 _).1 (List.mem_of_getElem? hk)
  have hx : x < GF.gfGd.gdG.gxProg.length := hev.1
  have hca : cnt x = a := by rw [hcnt x]; exact CertZ8.ordCount _ _ L k x a hord hk
  obtain ⟨lb, hlb⟩ : ∃ lb, (GF.gfGd.gdG.gxProg.getD x [])[a]? = some lb :=
    ⟨_, List.getElem?_eq_getElem hev.2⟩
  rw [← hca] at hlb hk
  obtain ⟨-, ⟨pC, hp, hrel⟩, hf2⟩ := hper x hx
  have hr := CertZ6.relpAgree St.cstC x (GF.gfGd.gdG.gxProg.getD x []) (cnt x) hf2
  obtain ⟨em, -, hiff, hpin, -, -, hblk⟩ := hD x _ (CertZ7.getDSome _ x hx)
  have hdevIdx : (x, cnt x) ∈ GF.gfDev → ∃ m, GF.gfDev[m]? = some (x, cnt x) ∧
      ((L.take k).filter (fun e => decide (e ∈ GF.gfDev))).length = m := by
    intro hin
    obtain ⟨m, hm⟩ := List.mem_iff_getElem?.1 hin
    exact ⟨m, hm, CertZ8.devCount _ _ L k m _ hord hdnd hsub hm hk⟩
  -- the block at the walk's fabric, and the fabric after it
  have hB : ∃ d', (((lbFused ((D x).r (cnt x)) ∧
      GraphFetchBlocks.blkOne (St.cstDv (cdEnd St.cstC)) d'
        (rowWsAux 0 wsInit ((GF.gfGd.gdG.gxProg.getD x []).take (cnt x))) lb ((D x).g (cnt x))
        ((D x).r (cnt x)) ((D x).f (cnt x)) ((D x).f (cnt x + 1))) ∨
      GraphFetchBlocks.blkPair (St.cstDv (cdEnd St.cstC)) d'
        (rowWsAux 0 wsInit ((GF.gfGd.gdG.gxProg.getD x []).take (cnt x))) lb ((D x).g (cnt x))
        ((D x).r (cnt x)) ((D x).f (cnt x)) ((D x).f (cnt x + 1))) ∧
      d' = fab (((L.take (k + 1)).filter (fun e => decide (e ∈ GF.gfDev))).length)) := by
    rw [take_S_r hk, CertZ8.filterSnoc]
    by_cases htq : (D x).tq (cnt x) = true
    · obtain ⟨m, hm, hmc⟩ := hdevIdx ((hiff _ (lookup_lt_Some hlb)).2 (.inr (.inr htq)))
      have hD0 : (D x).dvi (cnt x) = St.cstDv (cdEnd St.cstC) := by
        rw [hfab, hmc]; exact (hpin _ m hm).1
      refine ⟨(D x).dvo (cnt x), ?_, ?_⟩
      · rw [← hD0]
        rcases hblk (cnt x) lb hlb with ⟨hfu, h1, -⟩ | ⟨h1, -⟩
        · exact .inl ⟨hfu, h1⟩
        · exact .inr h1
      · rw [hmc, if_pos (decide_eq_true (List.mem_of_getElem? hm))]
        exact (hpin _ m hm).2
    · have htq' : (D x).tq (cnt x) = false := by simpa using htq
      have hnin := CertZ8.quietNotDev boot fab GF D x (cnt x) lb hD hlb hx htq'
      refine ⟨St.cstDv (cdEnd St.cstC), ?_, ?_⟩
      · rcases hblk (cnt x) lb hlb with ⟨hfu, -, hq⟩ | ⟨-, hq⟩
        · exact .inl ⟨hfu, hq htq' _⟩
        · exact .inr (hq htq' _)
      · rw [hfab, if_neg (by simpa using hnin), Nat.add_zero]
  obtain ⟨d', hblkD, hd'⟩ := hB
  obtain ⟨lb', pa, da, ls', pC', hre, hok', hrel'⟩ :=
    hstep St itvOf fiOf x (cnt x) lb _ _ _ _ _ pC d' hok hp hrel hr (hshape x _ lb hlb) hblkD
  refine ⟨x, lb, lb', pC, pa, da, ls', pC', d', hx, hlb, hp, hre, hok',
    ⟨fun y hy => ?_, fun s hs => ?_, k + 1, hkl, fun y => ?_, ?_, ?_⟩⟩
  · obtain ⟨hle, ⟨pCy, hpy, hrely⟩, hfy⟩ := hper y hy
    have hpst : (CertZ2.stSnoc St x lb' pC' d').cstPst
        (cdEnd (CertZ2.stSnoc St x lb' pC' d').cstC) =
        (St.cstPst (cdEnd St.cstC)).set x pC' := by
      show pstSnoc St.cstC St.cstPst x _ (cdEnd (candSnoc St.cstC _)) = _
      rw [cdEndSnoc, pstSnocGt _ _ _ _ _ (by omega)]
    rw [hpst]
    show _ ∧ _ ∧ List.Forall₂ lblReidxW _ (CertZ2.hartTr (St.cstC.cdTr ++ [⟨x, lb'⟩]) y)
    rw [CertZ6.hartTrSnoc]
    by_cases hy' : y = x
    · subst hy'
      rw [CertZ2.bumpSelf, if_pos rfl]
      refine ⟨lookup_lt_Some hlb, ⟨pC', List.getElem?_set_self (lookup_lt_Some hp), hrel'⟩, ?_⟩
      rw [take_S_r hlb]
      exact CertZ6.forall₂Snoc _ _ _ _ _ hfy hre
    · rw [CertZ2.bumpNe cnt x y hy', if_neg (Ne.symm hy'),
        List.getElem?_set_ne (Ne.symm hy')]
      exact ⟨hle, ⟨pCy, hpy, hrely⟩, hfy⟩
  · change s ∈ St.cstC.cdTr ++ [⟨x, lb'⟩] at hs
    rcases List.mem_append.1 hs with hs | hs
    · exact hagt s hs
    · simp only [List.mem_singleton] at hs
      rw [hs]
      exact hx
  · rw [take_S_r hk, CertZ8.filterSnoc]
    by_cases hy : y = x
    · subst hy; rw [CertZ2.bumpSelf, hcnt y]; simp
    · rw [CertZ2.bumpNe cnt x y hy, hcnt y]
      simp [Ne.symm hy]
  · show dvSnoc St.cstC St.cstDv _ (cdEnd (candSnoc St.cstC _)) = _
    rw [cdEndSnoc, dvSnocGt _ _ _ _ (by omega)]
    exact hd'
  · show (St.cstC.cdTr ++ [(⟨x, lb'⟩ : Estep)]).map Estep.esAg = _
    rw [List.map_append, hags, take_S_r hk, List.map_append]
    rfl

/-! # 4. The zero-cut supply and the kill -/

namespace CatLin

/-- **THE STEP SUPPLY — W10-4's NAMED PREMISE (the per-site datum, proved per pc)**: on every cyclic
class graph with the residue facts, for every fitting emission datum, a per-hart relation holding at
the boot states (lockstep there) with the per-step site datum. -/
def stepSupplyCZ (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (im : Image) : Prop :=
  ∀ (GF : Gfexec) (ad : List (Geid × Geid)) (z : Geid) (ss : List Seg),
    GF.gfGd.gdG.gxImg = im → rvwmoCatAD GF.gfGd ad → GraphFabConf.gfexecConfZF boot d0 fab GF →
    ioResidueGmo GF → gdiskRead14 GF.gfGd.gdG →
    ss ≠ [] → rawChainC GF.gfGd (ioCross GF) z z ss →
    ∀ D : Nat → CertZ7.EmData, CertZ7.emDataOk boot fab GF D →
    ∃ Rel : CertZ9.HRel,
      (∀ x, x < GF.gfGd.gdG.gxProg.length → Rel x 0 (boot x) (boot x)) ∧
      CertZ9.hartStepR d0 Rel

/-- **`walkSupplyOfOrdStep`** — the zero-cut walk supply from the order supply and the step supply
(the hart count ≤ `N` and (P2) for the whole graph as in `walkSupplyOfSched`): the walk follows the
order, each step the site datum's, the final lock co by `CertZ8.lockCoOfOrd`. -/
theorem walkSupplyOfOrdStep (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (im : Image)
    (N : Nat) (P : Int → Int → Prop) :
    (∀ (GF : Gfexec) (ad : List (Geid × Geid)), GF.gfGd.gdG.gxImg = im → rvwmoCatAD GF.gfGd ad →
      GraphFabConf.gfexecConfZF boot d0 fab GF →
      GF.gfGd.gdG.gxProg.length ≤ N ∧ GraphFetchBlocks.emPremOk boot GF.gfGd.gdG) →
    orderSupplyCZ boot d0 fab im P → stepSupplyCZ boot d0 fab im →
    walkSupplyCZ boot d0 fab im N P := by
  intro hpre hord hstep GF ad z ss him hc hconf hres hdr hne hch
  obtain ⟨hN, hp2⟩ := hpre GF ad him hc hconf
  obtain ⟨D, hD⟩ := CertZ7.emDataOfConf boot d0 fab GF hconf hp2
  obtain ⟨L, hL, hco⟩ := hord GF ad z ss him hc hconf hres hdr hne hch
  obtain ⟨Rel, hR0, hsR⟩ := hstep GF ad z ss him hc hconf hres hdr hne hch D hD
  have hsub : ∀ e, e ∈ GF.gfDev → e ∈ L := by
    intro e he
    obtain ⟨n, hn⟩ := List.mem_iff_getElem?.1 he
    obtain ⟨i, k⟩ := e
    obtain ⟨row, hrow, hk⟩ := hconf.2.2.1 n i k hn
    have hi : i < GF.gfGd.gdG.gxProg.length := lookup_lt_Some hrow
    refine (hL.2.1 _).2 ⟨hi, ?_⟩
    rw [List.getD_eq_getElem?_getD, hrow, Option.getD_some]
    exact hk
  have hshape : ∀ (x n : Nat) (lb : Lbl), (GF.gfGd.gdG.gxProg.getD x [])[n]? = some lb →
      CertZ4.lblShape lb := by
    intro x n lb hlb
    have hx : x < GF.gfGd.gdG.gxProg.length := by
      refine Nat.lt_of_not_le (fun hge => ?_)
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge, Option.getD_none] at hlb
      cases hlb
    have hl : gxLbl GF.gfGd.gdG (x, n) = some lb := by
      unfold gxLbl
      rw [CertZ7.getDSome _ x hx]
      exact hlb
    have := gwfLblShape GF.gfGd.gdG (x, n) lb hc.1 hl
    cases lb <;> exact this
  refine ⟨CertZ9.lockInvR GF.gfGd.gdG.gxProg (fun x => (D x).f) Rel
      (CertZ8.prefInv L GF.gfDev fab), fun itvOf fiOf _ => ?_,
    CertZ9.walkPolOfOrdR boot d0 fab GF D L Rel hD hconf.2.1 hL hsub hshape hsR, ?_⟩
  · refine ⟨fun x hx => ⟨Nat.zero_le _, ⟨boot x, ?_, ?_⟩, ?_⟩, fun s hs => by simp [wlkStart] at hs,
      ⟨0, Nat.zero_le _, fun x => by simp, ?_, by simp [wlkStart]⟩⟩
    · show ((List.range' 0 N).map boot)[x]? = some (boot x)
      rw [List.getElem?_map, lookup_seq_lt (by omega), Nat.zero_add]
      rfl
    · obtain ⟨_, _, _, _, _, hf0, _⟩ := hD x _ (CertZ7.getDSome _ x hx)
      show Rel x 0 ((D x).f 0) (boot x)
      rw [hf0]
      exact hR0 x hx
    · show List.Forall₂ lblReidxW ((GF.gfGd.gdG.gxProg.getD x []).take 0) (CertZ2.hartTr [] x)
      simp [CertZ2.hartTr]
    · show d0 = fab _
      simp only [List.take_zero, List.filter_nil, List.length_nil]
      exact hconf.1.symm
  · intro Sf itvOf fiOf cntF hinv _ hdone
    obtain ⟨hper, hagt, ⟨k, hkL, hcnt, -, hags⟩⟩ := hinv
    have hk : k = L.length := by
      refine Nat.le_antisymm hkL (Nat.le_of_not_lt (fun hlt => ?_))
      obtain ⟨⟨x, a⟩, hx⟩ : ∃ e, L[k]? = some e := ⟨L[k], List.getElem?_eq_getElem hlt⟩
      have hev := (hL.2.1 _).1 (List.mem_of_getElem? hx)
      have hca := CertZ8.ordCount _ _ L k x a hL hx
      rw [← hcnt x] at hca
      have := hdone x hev.1
      have := hev.2
      dsimp only at this
      omega
    rw [hk, List.take_length] at hags
    refine CertZ8.lockCoOfOrd _ GF.gfDev L Sf.cstC _ hc.1 hL hco hags hagt (fun x hx => ?_)
    obtain ⟨hle, -, hf⟩ := hper x hx
    rw [List.take_of_length_le (Nat.le_antisymm hle (hdone x hx) ▸ Nat.le_refl _)] at hf
    exact hf

section glue

open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode
open Language.Notation PrimStep
open LeanRV64D

/-- **`cycleKillOfOrdStepCZRC`** — WHAT W11-F CONSUMES AT THE ZERO CUT (N2′, after W10-4 inc. 1): the
class kill from the WP package, the fetch-view premise, the hart count and (P2), the ORDER supply, the
STEP supply (the per-site datum, lockstep or tainted), the two xv6 lock facts and the L2′ claim at
the member. -/
theorem cycleKillOfOrdStepCZRC (hlc : HasLC) (GF0 : BundledGFunctors) [MachGpreS hlc GF0]
    [WeakGpreS GF0] (gen : Nat) (σ0 : WGState) (D : CPU → List Register) (hD : ∀ c, (D c).Nodup)
    (Nm : Int → Int → Namespace) (P : Int → Int → Prop)
    (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (N : Nat) :
    freshEra gen σ0 →
    (List.range' 0 N).map boot = epsInit σ0 →
    d0 = efInit σ0.wgdev →
    wpPackage hlc GF0 gen σ0 D →
    (∀ a base, P a base → wpPackageProt hlc GF0 gen σ0 D (Nm a base) a base) →
    (∀ ρ, rtc epfRun (epInit gen, σ0) ρ → efetchItvOk ρ.1 ρ.2) →
    (∀ (GF : Gfexec) (ad : List (Geid × Geid)), GF.gfGd.gdG.gxImg = imgZ σ0.wgimg →
      rvwmoCatAD GF.gfGd ad → GraphFabConf.gfexecConfZF boot d0 fab GF →
      GF.gfGd.gdG.gxProg.length ≤ N ∧ GraphFetchBlocks.emPremOk boot GF.gfGd.gdG) →
    orderSupplyCZ boot d0 fab (imgZ σ0.wgimg) P →
    stepSupplyCZ boot d0 fab (imgZ σ0.wgimg) →
    acqAqCZ boot d0 fab (imgZ σ0.wgimg) P →
    relCoversCZ boot d0 fab (imgZ σ0.wgimg) P →
    l2ClaimCZR boot d0 fab (imgZ σ0.wgimg) P (badRun gen σ0) →
    cycleKillCZC boot d0 fab (imgZ σ0.wgimg) :=
  fun hfr hb1 hb2 hwp hwpp hcov hpre hord hstep hAQ hRC hl2 =>
    cycleKillOfWalkSupCZRC hlc GF0 gen σ0 D hD Nm P boot d0 fab N hfr hb1 hb2 hwp hwpp hcov
      (walkSupplyOfOrdStep boot d0 fab _ N P hpre hord hstep) hAQ hRC hl2

end glue

end CatLin

end Weak
