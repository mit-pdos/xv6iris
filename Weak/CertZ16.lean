/-
Weak: **W10 F1/F2 [OWN.94] (N2′), increment 4 — the PRODUCER side at protocol lock co: the order, the
final lock co, the zero-cut supply and the kill** (`PROGRESS-W10N2p.md`).  Lean-only, no Rocq twin.

  §1  **`CertZ16.ordCoNP`** — the order respects lock co from every NON-PLAIN lock-byte write (to any
      write of that byte: protocol co, and F2's "a protocol write co-before a plain store is walked
      before it"); `CertZ16.memberIffOrd` (the member's write order on two GF lock-byte writes IS their
      order in `L`) and **`CertZ16.lockCoOfOrd2`** (the final `CertZ14.lockCoNP`);
  §2  `CatLin.walkSupplyCZ2` (final clause at protocol co), `certSupplyCZROfWalk2`,
      **`CatLin.orderSupplyCZ2`** (the order respecting `ordCoNP` — derived from the named facts next),
      `walkSupplyOfOrdStep2`, and **`CatLin.cycleKillOfOrdSiteCZRC2`** — the zero-cut kill at protocol
      lock co (the chain W11-F consumes).

Spec: FAITHFUL (proof organisation).
-/
import Weak.CertZ15

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open TsoShadow

/-! # 1. The order and the final lock co -/

/-- The order respects lock co out of every NON-PLAIN lock-byte write. -/
def CertZ16.ordCoNP (G : Gexec) (L : List Geid) (Lb : Int → Prop) : Prop :=
  ∀ (b : Int) (x y : Geid) (vx vy : BitVec 8) (i j : Nat), Lb b →
    gwritesByte G x b vx → gwritesByte G y b vy → CertZ14.np G x → gwix G x < gwix G y →
    L[i]? = some x → L[j]? = some y → i < j

theorem CertZ16.memberIffOrd (G : Gexec) (dev L : List Geid) (c : Cand) (b : Int) (x y : Geid)
    (vx vy : BitVec 8) :
    gwf G → CertZ8.walkOrd G.gxProg dev L →
    c.cdTr.map Estep.esAg = L.map Prod.fst →
    (∀ s, s ∈ c.cdTr → s.esAg < G.gxProg.length) →
    (∀ x, x < G.gxProg.length →
      List.Forall₂ lblReidxW (G.gxProg.getD x []) (CertZ2.hartTr c.cdTr x)) →
    gwritesByte G x b vx → gwritesByte G y b vy →
    ∃ i j : Nat, L[i]? = some x ∧ L[j]? = some y ∧
      (gwix (CertZ3.member G.gxProg.length c) x < gwix (CertZ3.member G.gxProg.length c) y ↔
        i < j) := by
  intro hwf hord hags hag hrows hx hy
  -- the GF events are in the order
  have hevOf : ∀ (e : Geid) (a : Int) (v : BitVec 8), gwritesByte G e a v →
      ∃ i : Nat, L[i]? = some e := by
    intro e a v he
    obtain ⟨l, -, -, -, hl, -⟩ := he
    unfold gxLbl at hl
    cases hr : G.gxProg[e.1]? with
    | none => rw [hr] at hl; cases hl
    | some row =>
      rw [hr] at hl
      have hlt := lookup_lt_Some hl
      have he1 : e.1 < G.gxProg.length := lookup_lt_Some hr
      have hgd : G.gxProg.getD e.1 [] = row := by
        rw [List.getD_eq_getElem?_getD, hr, Option.getD_some]
      exact List.mem_iff_getElem?.1 ((hord.2.1 e).2 ⟨he1, by rw [hgd]; exact hlt⟩)
  obtain ⟨i, hi⟩ := hevOf x b vx hx
  obtain ⟨j, hj⟩ := hevOf y b vy hy
  obtain ⟨si, hsi, hagi, hci⟩ := CertZ8.ceidOrd _ _ L c i x hord hags hi
  obtain ⟨sj, hsj, hagj, hcj⟩ := CertZ8.ceidOrd _ _ L c j y hord hags hj
  -- the trace's writes at `i`, `j` are writes (writes verbatim)
  have hW : ∀ (k : Nat) (e : Geid) (s : Estep) (a : Int) (v : BitVec 8), c.cdTr[k]? = some s →
      ceid (candExec c) k = e → gwritesByte G e a v → lbIsW s.esLb = true := by
    intro k e s a v hs hce he
    obtain ⟨l, base, vs, jj, hl, hwr, -, -⟩ := he
    have hlbl := (cgLbl (candExec c) k s hs).1
    rw [hce, ← CertZ3.memberLbl _ c e hag, CertZ3.memberLblHart _ c e hag] at hlbl
    unfold gxLbl at hl
    cases hr : G.gxProg[e.1]? with
    | none => rw [hr] at hl; cases hl
    | some row =>
      rw [hr] at hl
      have he1 : e.1 < G.gxProg.length := lookup_lt_Some hr
      have hf := hrows e.1 he1
      rw [List.getD_eq_getElem?_getD, hr, Option.getD_some] at hf
      rcases GraphFetchN2.forall₂Get _ _ _ hf e.2 with ⟨h1, -⟩ | ⟨l0, l1, h1, h2, h12⟩
      · simp only [Option.bind_some] at hl; rw [hl] at h1; cases h1
      · simp only [Option.bind_some] at hl
        rw [hl, Option.some.injEq] at h1
        subst h1
        rw [hlbl, Option.some.injEq] at h2
        subst h2
        rw [lblReidxWIsw _ _ h12]
        exact lbWrIsW _ _ hwr
  have hwi := hW i x si b vx hsi hci hx
  have hwj := hW j y sj b vy hsj hcj hy
  have key := CertZ8.memberWixIff _ c i j si sj hag hsi hsj hwi hwj
  rw [hci, hcj] at key
  exact ⟨i, j, hi, hj, key⟩

/-- **`CertZ16.lockCoOfOrd2` — THE FINAL LOCK CO, PROTOCOL**. -/
theorem CertZ16.lockCoOfOrd2 (G : Gexec) (dev L : List Geid) (c : Cand) (Lb : Int → Prop) :
    gwf G → CertZ8.walkOrd G.gxProg dev L → CertZ16.ordCoNP G L Lb →
    c.cdTr.map Estep.esAg = L.map Prod.fst →
    (∀ s, s ∈ c.cdTr → s.esAg < G.gxProg.length) →
    (∀ x, x < G.gxProg.length →
      List.Forall₂ lblReidxW (G.gxProg.getD x []) (CertZ2.hartTr c.cdTr x)) →
    CertZ14.lockCoNP G (CertZ3.member G.gxProg.length c) Lb := by
  intro hwf hord hco hags hag hrows
  refine ⟨fun b x y vx vy hb hx hy hnx hny => ?_, fun b x y vx vy hb hx hy hnx _ hlt => ?_⟩
  · obtain ⟨i, j, hi, hj, key⟩ :=
      CertZ16.memberIffOrd G dev L c b x y vx vy hwf hord hags hag hrows hx hy
    rw [key]
    constructor
    · intro hlt
      exact hco b x y vx vy i j hb hx hy hnx hlt hi hj
    · intro hij
      have hxw := gwritesByteGwrites G x b vx hwf hx
      have hyw := gwritesByteGwrites G y b vy hwf hy
      rcases Nat.lt_trichotomy (gwix G x) (gwix G y) with h | h | h
      · exact h
      · have := gwixInj G x y hwf.1 hxw hyw h
        subst this
        have := NoDup_lookup hord.1 hi hj
        omega
      · have := hco b y x vy vx j i hb hy hx hny h hj hi
        omega
  · obtain ⟨i, j, hi, hj, key⟩ :=
      CertZ16.memberIffOrd G dev L c b x y vx vy hwf hord hags hag hrows hx hy
    exact key.2 (hco b x y vx vy i j hb hx hy hnx hlt hi hj)

/-! # 2. The zero-cut supply and the kill -/

namespace CatLin

def walkSupplyCZ2 (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (im : Image) (N : Nat)
    (P : Int → Int → Prop) : Prop :=
  ∀ (GF : Gfexec) (ad : List (Geid × Geid)) (z : Geid) (ss : List Seg),
    GF.gfGd.gdG.gxImg = im → rvwmoCatAD GF.gfGd ad → GraphFabConf.gfexecConfZF boot d0 fab GF →
    ioResidueGmo GF → gdiskRead14 GF.gfGd.gdG →
    ss ≠ [] → rawChainC GF.gfGd (ioCross GF) z z ss →
    ∃ Inv : CertZ2.WInv,
      (∀ itvOf fiOf, CertZ.cstOkZW d0 (wlkStart boot d0 N GF.gfGd.gdG) itvOf fiOf →
        Inv (wlkStart boot d0 N GF.gfGd.gdG) itvOf fiOf (fun _ => 0)) ∧
      CertZ2.walkPolZ d0 GF.gfGd.gdG.gxProg Inv ∧
      (∀ Sf itvOf fiOf cntF, Inv Sf itvOf fiOf cntF → CertZ.cstOkZW d0 Sf itvOf fiOf →
        (∀ x, x < GF.gfGd.gdG.gxProg.length →
          (GF.gfGd.gdG.gxProg.getD x []).length ≤ cntF x) →
        CertZ14.lockCoNP GF.gfGd.gdG
          (CertZ3.member GF.gfGd.gdG.gxProg.length Sf.cstC) (GraphFetchN2.lockBytes P))

/-- **`certSupplyCZROfWalk`** — (G-3) AT A MEMBER FROM THE FREE WALK: the walk from the empty
candidate finishes every row; its member agrees with `GF` at `pi = id` (rows by the walk, writes
verbatim, lock co by the supply), is well-formed, in program write order, and its write order is
the run's log. -/
theorem certSupplyCZROfWalk2 (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (im : Image)
    (N : Nat) (P : Int → Int → Prop) :
    walkSupplyCZ2 boot d0 fab im N P → certSupplyCZR2 boot d0 fab im N P := by
  intro hws GF ad _ z ss him hc hconf hres hdr _ _ _ _ _ hne hch
  obtain ⟨Inv, hI0, hpol, hco⟩ := hws GF ad z ss him hc hconf hres hdr hne hch
  have hstart := wlkStartInvZ boot d0 N GF.gfGd.gdG
  obtain ⟨itv0, fi0, hok0⟩ := CertZ.cstOkZWOf d0 _ hstart.1
  obtain ⟨_, Sf, itvF, fiF, cntF, tradd, hrun, hokF, hinvF, hdone, -, htr, hf2, hagt, himg,
    hpst⟩ := CertZ2.walkRunZ d0 GF.gfGd.gdG.gxProg Inv hpol _ (wlkStart boot d0 N GF.gfGd.gdG) itv0 fi0 (fun _ => 0)
      (Nat.le_refl _) hok0 (hI0 itv0 fi0 hok0)
  have htr' : Sf.cstC.cdTr = tradd := by rw [htr]; rfl
  have hagS : ∀ s, s ∈ Sf.cstC.cdTr → s.esAg < GF.gfGd.gdG.gxProg.length := by
    rw [htr']; exact hagt
  have hcons := hokF.1
  refine ⟨Sf.cstC, Sf.cstPst, Sf.cstDv, CertZ3.member GF.gfGd.gdG.gxProg.length Sf.cstC, fun t => t,
    runDataZOfCyc boot d0 N GF.gfGd.gdG Sf (CertZ.cstOkZOfW _ _ _ _ hokF) (by rw [himg]; rfl)
      (by rw [hpst]; rfl),
    ?_, CertZ3.memberGwf _ _ hcons hagS, ⟨show Sf.cstC.cdImg = _ by rw [himg]; rfl, ?_, hco Sf itvF fiF cntF hinvF hokF hdone⟩,
    CertZ3.memberGwrowGmo _ _ hagS⟩
  · have := CertZ3.memberLogPfx GF.gfGd.gdG.gxProg.length Sf.cstC hcons hagS
    exact logOfOfPfx _ _ this
  · show List.Forall₂ _ GF.gfGd.gdG.gxProg ((List.range' 0 GF.gfGd.gdG.gxProg.length).map _)
    refine CertZ3.forall₂Range _ _ GF.gfGd.gdG.gxProg 0 (fun x row hx => ?_)
    rw [Nat.zero_add, htr']
    have hfx := hf2 x
    have hlen : (GF.gfGd.gdG.gxProg.getD x []).length ≤ cntF x := hdone x (lookup_lt_Some hx)
    rw [List.getD_eq_getElem?_getD, hx, Option.getD_some] at hfx hlen
    rw [List.drop_zero, Nat.sub_zero, List.take_of_length_le hlen] at hfx
    have hre : List.Forall₂ (fun l l' => lblReidxW (lblRen (fun t => t) l) l') row
        (CertZ2.hartTr tradd x) := by
      refine List.Forall₂.imp (fun {l l'} h => ?_) hfx
      rw [lblRenId]; exact h
    exact hre

/-- **THE ORDER SUPPLY at protocol co (F2)** — derived from the named lock-discipline facts next.

WARNING (2026-10-14, `PROGRESS-W10N2p.md`): FALSE on contended xv6 graphs — two harts each releasing one
lock (`fence rw,w; sw zero`) then spinning (`amoswap.w.aq`, failed) on the other's give the po ∪ co
cycle `R1 →po F2 →co R2 →po F1 →co R1`, RVWMO-consistent (a plain release store and a later acquire
RMW are unordered).  Do not consume; superseded by the successful-protocol order (`ordCoSP`). -/
def orderSupplyCZ2 (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (im : Image)
    (P : Int → Int → Prop) : Prop :=
  ∀ (GF : Gfexec) (ad : List (Geid × Geid)) (z : Geid) (ss : List Seg),
    GF.gfGd.gdG.gxImg = im → rvwmoCatAD GF.gfGd ad → GraphFabConf.gfexecConfZF boot d0 fab GF →
    ioResidueGmo GF → gdiskRead14 GF.gfGd.gdG →
    ss ≠ [] → rawChainC GF.gfGd (ioCross GF) z z ss →
    ∃ L, CertZ8.walkOrd GF.gfGd.gdG.gxProg GF.gfDev L ∧
      CertZ16.ordCoNP GF.gfGd.gdG L (GraphFetchN2.lockBytes P)

theorem walkSupplyOfOrdStep2 (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (im : Image)
    (N : Nat) (P : Int → Int → Prop) :
    (∀ (GF : Gfexec) (ad : List (Geid × Geid)), GF.gfGd.gdG.gxImg = im → rvwmoCatAD GF.gfGd ad →
      GraphFabConf.gfexecConfZF boot d0 fab GF →
      GF.gfGd.gdG.gxProg.length ≤ N ∧ GraphFetchBlocks.emPremOk boot GF.gfGd.gdG) →
    orderSupplyCZ2 boot d0 fab im P → stepSupplyCZ boot d0 fab im →
    walkSupplyCZ2 boot d0 fab im N P := by
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
    refine CertZ16.lockCoOfOrd2 _ GF.gfDev L Sf.cstC _ hc.1 hL hco hags hagt (fun x hx => ?_)
    obtain ⟨hle, -, hf⟩ := hper x hx
    rw [List.take_of_length_le (Nat.le_antisymm hle (hdone x hx) ▸ Nat.le_refl _)] at hf
    exact hf

section glue

open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode
open Language.Notation PrimStep
open LeanRV64D

/-- **`cycleKillOfOrdSiteCZRC2`** — WHAT W11-F CONSUMES AT THE ZERO CUT, AT PROTOCOL LOCK CO (F1/F2): the
class kill from the WP package, the fetch-view premise, the hart count and (P2), the ORDER supply
(`orderSupplyCZ2`), the SITE supply, the two xv6 lock facts and the L2′ claim at the protocol-agreeing
member. -/
theorem cycleKillOfOrdSiteCZRC2 (hlc : HasLC) (GF0 : BundledGFunctors) [MachGpreS hlc GF0]
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
    orderSupplyCZ2 boot d0 fab (imgZ σ0.wgimg) P →
    siteSupplyCZ boot d0 fab (imgZ σ0.wgimg) →
    acqAqCZ2 boot d0 fab (imgZ σ0.wgimg) P →
    relCoversCZ2 boot d0 fab (imgZ σ0.wgimg) P →
    l2ClaimCZR2 boot d0 fab (imgZ σ0.wgimg) P (badRun gen σ0) →
    cycleKillCZC boot d0 fab (imgZ σ0.wgimg) :=
  fun hfr hb1 hb2 hwp hwpp hcov hpre hord hsite hAQ hRC hl2 =>
    cycleKillOfL2CZRC2 hlc GF0 gen σ0 D hD Nm P boot d0 fab N hfr hb1 hb2 hwp hwpp hcov
      (cutSupplyOfCycleCZC boot d0 fab _)
      (certSupplyCZROfWalk2 boot d0 fab _ N P
        (walkSupplyOfOrdStep2 boot d0 fab _ N P hpre hord (stepSupplyOfSite boot d0 fab _ hsite)))
      hAQ hRC hl2

end glue

end CatLin

end Weak
