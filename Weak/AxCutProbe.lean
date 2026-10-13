/-
Weak: **K3 FEASIBILITY PROBE — which power-off CUT of an execution graph
preserves the cat model?**  PURE (no Iris).

Rocq: `iris/AxCutProbe.v` @ xxvzwolszwmp.

The Rocq header, in substance (design: `claude-notes/design/weak-memory-lb-axsl.md`
§1 K3 item (a) and §3 risk 8; tracker challenge C12).

VERDICT.

(1) A plain gmo-PREFIX cut FAILS: its per-hart part is NOT a program prefix.
    Witness `gfwd` (§1): hart 0 = `[sd x; ld x]` with the load FORWARDED from
    the store and gmo-BEFORE it; hart 1 = `[sd y]`.  `gfwd` is cat-consistent
    (`AxCutProbe.fwdCat`), and the gmo-prefix of length 2 = {sd y, ld x} holds
    the load but not its rf source (`fwdPrefixDropsSource`).  No `cs` realizes
    that prefix as a row truncation (`fwdNoCut2`); the literal attempt is
    ILL-FORMED (`fwdNaiveNotWf`).

(2) The cut that WORKS is the DOUBLY-CLOSED cut `WeakRvwmoRestr.restrOk G cs n`
    (a po-prefix per hart AND a gmo-prefix).  HERE: `restrictCatConsistent`
    (the untagged cat model over `gdRestrict`) and `restrictCatConsistentT`
    (the TAGGED model `AxDeps.rvwmoCatConsistentT` over `gtRestrict`).  Rule
    2's "no same-byte write po-between" arm and rule 12's rf restrict because
    the cut is po-closed; write indices are reused verbatim because it is
    gmo-closed.

(3) Non-vacuity on `gfwd`: n = 1 (`fwdCut1Ok`, cs = [0; 1]) is a proper 2-hart
    cut, its consistency checked by the lemma and by the decision procedure
    (`fwdCut1Cat`, `fwdCut1CatDirect`); n = 2 is NOT a cut point (`fwdNoCut2`).

DESIGN IMPLICATIONS FOR K3 (Rocq header, unchanged): the power-off model is
"the era is a doubly-closed cut of some consistent GT_g"; the persisted disk
must be the disk AGENT's own performed (po-prefix) writes.

**Deviations from Rocq.**

1. NAMES: lowerCamelCase as `Weak/WeakMem.lean` deviation 1.  The duplicated
   Rocq name (`notes/weak-port-dupnames.json`) `fwd_cat` is FILE-QUALIFIED
   (`AxCutProbe.fwdCat`); the dependencies' duplicates are referred to
   qualified (`WeakRvwmoGraph.gpo`, `WeakRvwmoAcyc.grf`).
2. VOCABULARY: as `AxGraphCat` deviation 2 (`Z` ↦ `Int`, `BV 8 k` ↦ `k#8`,
   `Z_to_bv 8 0` ↦ `0#8`, `GDExec (GExec img prog gmo) deps` ↦
   `⟨⟨img, prog, gmo⟩, deps⟩`, `GDExecT` ↦ anonymous constructor,
   `filter (λ e, b)` ↦ `List.filter` on the Boolean).
3. The §2 `Section restr` hypotheses become explicit arguments `(G cs n)
   (hcut : ...)` of the three section lemmas, in Rocq's call order; the unused
   section hypothesis `Hnd` (every lemma is `Proof using Hcut`) is not an
   argument.
4. `vm_compute; reflexivity` on closed booleans/membership ↦ `decide` /
   `decide +kernel` (the `WeakDeps` recipe).
5. The closing `Print Assumptions` block has no Lean twin (the lint's axiom
   check covers it).

**Name map** (Rocq → Lean): `gmo_cut` ↦ `gmoCut`; `gmo_cut_po_closed` ↦
`gmoCutPoClosed`; `restr_ok_po_closed` ↦ `restrOkPoClosed`; `x_addr` ↦ `xAddr`;
`y_addr` ↦ `yAddr`; `fwd_img` ↦ `fwdImg`; `frow0`; `frow1`; `eSX`; `eLX`;
`eSY`; `gfwd`; `fwd_cat` ↦ `AxCutProbe.fwdCat`; `fwd_rf` ↦ `fwdRf`;
`fwd_notin_SX` ↦ `fwdNotinSX`; `fwd_prefix_drops_source` ↦
`fwdPrefixDropsSource`; `fwd_not_po_closed` ↦ `fwdNotPoClosed`; `fwd_no_cut2`
↦ `fwdNoCut2`; `fwd_naive_not_wf` ↦ `fwdNaiveNotWf`; `gxr_grf_at` ↦
`gxrGrfAt`; `gxr_grf` ↦ `gxrGrf`; `gxr_gppo_cat6` ↦ `gxrGppoCat6`;
`gxr_gppo12` ↦ `gxrGppo12`; `restrict_core` ↦ `restrictCore`;
`gxr_gmo_lt_in` ↦ `gxrGmoLtIn`; `restrict_cat_consistent` ↦
`restrictCatConsistent`; `gt_restrict` ↦ `gtRestrict`; `gt_restrict_deps` ↦
`gtRestrictDeps`; `restrict_cat_consistent_t` ↦ `restrictCatConsistentT`;
`fwd_cut1_ok` ↦ `fwdCut1Ok`; `fwd_cut1_cat` ↦ `fwdCut1Cat`;
`fwd_cut1_cat_direct` ↦ `fwdCut1CatDirect`; `fwd_cut_full` ↦ `fwdCutFull`.

**Not ported:** nothing (every definition and lemma is ported).
-/
import Weak.WeakRvwmoRestr
import Weak.AxDeps

namespace Weak

open MachCSL MachCSL.Stdpp
open Lbl

/-! # 0. The gmo-prefix cut, and what realizing it as a row cut costs -/

/-- `gmoCut G k e`: `e` sits at a gmo position `< k` (the naive power-off cut). -/
def gmoCut (G : Gexec) (k : Nat) (e : Geid) : Prop :=
  e ∈ G.gxGmo.take k

def gmoCutPoClosed (G : Gexec) (k : Nat) : Prop :=
  ∀ e1 e2, WeakRvwmoGraph.gpo G e1 e2 → gmem G e1 → gmoCut G k e2 → gmoCut G k e1

/-- Every `restrOk` cut's gmo part is po-closed. -/
theorem restrOkPoClosed (G : Gexec) (cs : List Nat) (k : Nat) :
    restrOk G cs k → gmoCutPoClosed G k := by
  rintro hro e1 e2 ⟨hag, hlt, _⟩ hm he2
  exact restrOkIn G cs k e1 hro hm
    (gcutPoDown cs e1 e2 hag hlt (restrOkCut G cs k e2 hro he2))

/-! # 1. THE WITNESS: store forwarding breaks gmo-prefix cuts -/

def xAddr : Int := 0x100
def yAddr : Int := 0x200

def fwdImg : Image := fun _ => some (0#8)

/-- hart 0: `[sd x ← 1; ld x]` (the load forwarded: ts = 2, the store's write
index, since hart 1's store is the gmo-first write). -/
def frow0 : List Lbl :=
  [LStore false xAddr [1#8] .WCplain,
   LLoad false xAddr [2] [1#8]]

def frow1 : List Lbl := [LStore false yAddr [2#8] .WCplain]

def eSX : Geid := (0, 0)
def eLX : Geid := (0, 1)
def eSY : Geid := (1, 0)

/-- gmo: `[sd y; ld x; sd x]`: the load is gmo-BEFORE its own source. -/
def gfwd : Gdexec :=
  ⟨⟨fwdImg, [frow0, frow1], [eSY, eLX, eSX]⟩, [], []⟩

theorem AxCutProbe.fwdCat : rvwmoCatConsistent gfwd :=
  catConsistentBSound _ (by decide +kernel)

/-- The load reads the store (rf), yet is gmo-before it. -/
theorem fwdRf : WeakRvwmoAcyc.grf gfwd.gdG eSX eLX ∧ gmoLt gfwd.gdG eLX eSX := by
  refine ⟨⟨xAddr, 2, 1#8, ⟨_, xAddr, [2], [1#8], 0, rfl, rfl, rfl, rfl, by decide⟩,
    by decide +kernel⟩, ?_⟩
  unfold gmoLt
  decide +kernel

theorem fwdNotinSX : ¬ eSX ∈ gfwd.gdG.gxGmo.take 2 := by decide

/-- The gmo-prefix of length 2 keeps the load but drops its rf source. -/
theorem fwdPrefixDropsSource :
    gmoCut gfwd.gdG 2 eLX ∧ ¬ gmoCut gfwd.gdG 2 eSX ∧ WeakRvwmoAcyc.grf gfwd.gdG eSX eLX :=
  ⟨by unfold gmoCut; decide, fwdNotinSX, fwdRf.1⟩

theorem fwdNotPoClosed : ¬ gmoCutPoClosed gfwd.gdG 2 := by
  intro hc
  apply fwdNotinSX
  exact hc eSX eLX ⟨rfl, by decide, rfl, rfl⟩ ⟨_, rfl, rfl⟩ fwdPrefixDropsSource.1

/-- NO row truncation realizes the gmo-prefix of length 2. -/
theorem fwdNoCut2 : ∀ cs, ¬ restrOk gfwd.gdG cs 2 :=
  fun cs hro => fwdNotPoClosed (restrOkPoClosed _ cs 2 hro)

/-- The literal attempt: keep hart 0's row up to the load, keep hart 1, cut
gmo at 2.  ILL-FORMED: the kept store is a memory event not in the cut gmo. -/
theorem fwdNaiveNotWf : ¬ gwf (gxRestrict gfwd.gdG [2, 1] 2) := by
  rintro ⟨_, hm, _⟩
  have hmem : gmem (gxRestrict gfwd.gdG [2, 1] 2) eSX := ⟨_, rfl, rfl⟩
  exact fwdNotinSX ((hm eSX).2 hmem)

/-! # 2. THE DOUBLY-CLOSED CUT PRESERVES THE CAT MODEL -/

theorem gxrGrfAt (G : Gexec) (cs : List Nat) (n : Nat)
    (hcut : ∀ e, e ∈ G.gxGmo.take n → gcut cs e = true) (a : Int) (w r : Geid) :
    grfAt (gxRestrict G cs n) a w r → gcut cs r = true ∧ grfAt G a w r := by
  rintro ⟨t, v, hrd, hat⟩
  obtain ⟨hc, hrd⟩ := (gxrRdb G cs n r a t v).1 hrd
  exact ⟨hc, t, v, hrd, gxrGwriteAt G cs n t w hcut hat⟩

theorem gxrGrf (G : Gexec) (cs : List Nat) (n : Nat)
    (hcut : ∀ e, e ∈ G.gxGmo.take n → gcut cs e = true) (w r : Geid) :
    WeakRvwmoAcyc.grf (gxRestrict G cs n) w r →
    gcut cs r = true ∧ WeakRvwmoAcyc.grf G w r := by
  rintro ⟨a, t, v, hrd, hat⟩
  obtain ⟨hc, t', v', h1, h2⟩ := gxrGrfAt G cs n hcut a w r ⟨t, v, hrd, hat⟩
  exact ⟨hc, a, t', v', h1, h2⟩

/-- Every cat6 arm of the cut is a cat6 arm of `G` between cut events. -/
theorem gxrGppoCat6 (G : Gexec) (cs : List Nat) (n : Nat)
    (hcut : ∀ e, e ∈ G.gxGmo.take n → gcut cs e = true) (e1 e2 : Geid) :
    gppoCat6 (gxRestrict G cs n) e1 e2 →
    gppoCat6 G e1 e2 ∧ gcut cs e1 = true ∧ gcut cs e2 = true := by
  intro h
  obtain ⟨hpo, hc2⟩ := (gxrGpo G cs n e1 e2).1 (gppoCat6Gpo _ _ _ h)
  have hc1 : gcut cs e1 = true := gcutPoDown cs e1 e2 hpo.1 hpo.2.1 hc2
  refine ⟨?_, hc1, hc2⟩
  rcases h with h | h | h | h | h | h
  · -- rule 1
    obtain ⟨_, a, h1, v, h2⟩ := h
    exact Or.inl ⟨hpo, a, gxrGaccesses G cs n e1 a h1, v, ((gxrWrb G cs n e2 a v).1 h2).2⟩
  · -- rule 2
    obtain ⟨_, a, t1, v1, t2, v2, h1, h2, hne, hno⟩ := h
    refine Or.inr (Or.inl ⟨hpo, a, t1, v1, t2, v2, ((gxrRdb G cs n e1 a t1 v1).1 h1).2,
      ((gxrRdb G cs n e2 a t2 v2).1 h2).2, hne, ?_⟩)
    intro w v hw hp1 hp2
    have hcw : gcut cs w = true := gcutPoDown cs w e2 hp2.1 hp2.2.1 hc2
    exact hno w v ((gxrWrb G cs n w a v).2 ⟨hcw, hw⟩) ((gxrGpo G cs n e1 w).2 ⟨hp1, hcw⟩)
      ((gxrGpo G cs n w e2).2 ⟨hp2, hc2⟩)
  · -- rule 3
    obtain ⟨_, hrmw, a, hrf⟩ := h
    exact Or.inr (Or.inr (Or.inl ⟨hpo, ((gxrGlblIs G cs n e1 _).1 hrmw).2, a,
      (gxrGrfAt G cs n hcut a e1 e2 hrf).2⟩))
  · -- rule 4
    obtain ⟨pr, pw, sr, sw, ⟨hag, hlt, kf, hk3, hk4, hlf⟩, hk1, hk2⟩ := h
    refine Or.inr (Or.inr (Or.inr (Or.inl ⟨pr, pw, sr, sw,
      ⟨hag, hlt, kf, hk3, hk4, (gxrLblSome G cs n _ _ hlf).2⟩, ?_, ?_⟩)))
    · rcases hk1 with ⟨hx, hb⟩ | ⟨hx, hb⟩
      · exact Or.inl ⟨((gxrGlblIs G cs n e1 _).1 hx).2, hb⟩
      · exact Or.inr ⟨((gxrGlblIs G cs n e1 _).1 hx).2, hb⟩
    · rcases hk2 with ⟨hx, hb⟩ | ⟨hx, hb⟩
      · exact Or.inl ⟨((gxrGlblIs G cs n e2 _).1 hx).2, hb⟩
      · exact Or.inr ⟨((gxrGlblIs G cs n e2 _).1 hx).2, hb⟩
  · -- rule 5
    obtain ⟨_, h1, h2, h3⟩ := h
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hpo, ((gxrGlblIs G cs n e1 _).1 h1).2,
      ((gxrGlblIs G cs n e1 _).1 h2).2, ((gxrGmem G cs n e2).1 h3).2⟩))))
  · -- rule 7 RCsc
    obtain ⟨_, h1, h2⟩ := h
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hpo, ((gxrGlblIs G cs n e1 _).1 h1).2,
      ((gxrGlblIs G cs n e2 _).1 h2).2⟩))))

/-- Rule 12 over any edge list whose cut part is a sub-list of `dd`. -/
theorem gxrGppo12 (G : Gexec) (cs : List Nat) (n : Nat)
    (hcut : ∀ e, e ∈ G.gxGmo.take n → gcut cs e = true)
    (dd dd' : List (Geid × Geid)) (a b : Geid) :
    (∀ x, x ∈ dd' → x ∈ dd ∧ gcut cs x.1 = true) →
    gppo12 (gxRestrict G cs n) dd' a b →
    gppo12 G dd a b ∧ gcut cs a = true ∧ gcut cs b = true := by
  rintro hdd ⟨hag, m, hd, hrf⟩
  obtain ⟨hd', hca⟩ := hdd _ hd
  obtain ⟨hcb, hrf⟩ := gxrGrf G cs n hcut m b hrf
  exact ⟨⟨hag, m, hd', hrf⟩, hca, hcb⟩

/-- The shared non-ppo core (gwf, load value, atomicity): the proof of
`WeakRvwmoRestr.restrictConsistent` minus its ppo⁻ bullet. -/
theorem restrictCore (G : Gexec) (cs : List Nat) (n : Nat) :
    gwf G → gloadValue G → gatomicity G → restrOk G cs n →
    gwf (gxRestrict G cs n) ∧ gloadValue (gxRestrict G cs n) ∧
    gatomicity (gxRestrict G cs n) := by
  intro hwf hlv hat hro
  obtain ⟨hnd, hmem, hsh⟩ := hwf
  have hcut : ∀ e, e ∈ G.gxGmo.take n → gcut cs e = true :=
    fun e he => restrOkCut G cs n e hro he
  have hin : ∀ e, gcut cs e = true → gmem G e → e ∈ G.gxGmo.take n :=
    fun e hc hm => restrOkIn G cs n e hro hm hc
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · -- gwf
    exact takeNoDup G.gxGmo n hnd
  · intro e
    show e ∈ G.gxGmo.take n ↔ _
    rw [gxrGmem]
    constructor
    · intro he
      exact ⟨hcut e he, (hmem e).1 (takeElemGmo G n e he)⟩
    · rintro ⟨hc, hm⟩
      exact hin e hc hm
  · intro i p k l hp hk
    rw [gxrProgLookup] at hp
    cases hc : cs[i]? with
    | none => rw [hc] at hp; simp at hp
    | some c =>
      cases hp0 : G.gxProg[i]? with
      | none => rw [hc, hp0] at hp; simp at hp
      | some p0 =>
        rw [hc, hp0] at hp
        simp at hp
        subst hp
        exact hsh i p0 k l hp0 (lookup_take_Some.1 hk).1
  · -- load value
    intro e a t v hrd'
    obtain ⟨hce, hrd⟩ := (gxrRdb G cs n e a t v).1 hrd'
    have he : e ∈ G.gxGmo.take n := hin e hce (rdbGmem G e a t v hrd)
    obtain ⟨hsrc, hmax⟩ := hlv e a t v hrd
    refine ⟨?_, ?_⟩
    · cases t with
      | zero => exact hsrc
      | succ t =>
        obtain ⟨w, hwat, hwb, hvis⟩ :=
          (hsrc : ∃ w, gwriteAt G (t + 1) = some w ∧ gwritesByte G w a v ∧ gvisible G w e)
        have hwm : w ∈ G.gxGmo.take n := by
          rcases hvis with hmo | hpo
          · refine gposLtTake G n w hmo.1 ?_
            have h1 := gposTakeLt G n e hnd he
            have h2 := hmo.2.2
            omega
          · exact hin w (gcutPoDown cs w e hpo.1 hpo.2.1 hce) (wrbGmem G w a v hwb)
        have hcw : gcut cs w = true := hcut w hwm
        have hwg : w ∈ gwrites (gxRestrict G cs n) :=
          gxrGwritesIn G cs n w hcw hwm (WeakRvwmoGraph.gwritesByteGisW G w a v hwb)
        show ∃ w, gwriteAt (gxRestrict G cs n) (t + 1) = some w ∧
          gwritesByte (gxRestrict G cs n) w a v ∧ gvisible (gxRestrict G cs n) w e
        refine ⟨w, gxrGwriteAtIn G cs n (t + 1) w hnd hcut hwg hwat,
          (gxrWrb G cs n w a v).2 ⟨hcw, hwb⟩, ?_⟩
        rcases hvis with hmo | hpo
        · exact Or.inl ((gxrGmoLt G cs n w e hnd).2 ⟨hwm, he, hmo⟩)
        · exact Or.inr ((gxrGpo G cs n w e).2 ⟨hpo, hce⟩)
    · intro w' v' hwb' hvis'
      obtain ⟨hcw', hwb⟩ := (gxrWrb G cs n w' a v').1 hwb'
      have hwm' := hin w' hcw' (wrbGmem G w' a v' hwb)
      have hwg' := gxrGwritesIn G cs n w' hcw' hwm'
        (WeakRvwmoGraph.gwritesByteGisW G w' a v' hwb)
      rw [gxrGwix G cs n w' hnd hcut hwg']
      apply hmax w' v' hwb
      rcases hvis' with hmo | hpo
      · exact Or.inl ((gxrGmoLt G cs n w' e hnd).1 hmo).2.2
      · exact Or.inr ((gxrGpo G cs n w' e).1 hpo).1
  · -- atomicity
    intro e a t v hrd' hw' w' v' hwb'
    obtain ⟨hce, hrd⟩ := (gxrRdb G cs n e a t v).1 hrd'
    have hw := ((gxrGlblIs G cs n e lbIsW).1 hw').2
    obtain ⟨hcw', hwb⟩ := (gxrWrb G cs n w' a v').1 hwb'
    have he := hin e hce (rdbGmem G e a t v hrd)
    have hwm' := hin w' hcw' (wrbGmem G w' a v' hwb)
    have heg := gxrGwritesIn G cs n e hce he (glblIsWGisW G e hw)
    have hwg' := gxrGwritesIn G cs n w' hcw' hwm'
      (WeakRvwmoGraph.gwritesByteGisW G w' a v' hwb)
    rw [gxrGwix G cs n w' hnd hcut hwg', gxrGwix G cs n e hnd hcut heg]
    exact hat e a t v hrd hw w' v' hwb

/-- A `G`-gmo edge between cut events is a gmo edge of the cut. -/
theorem gxrGmoLtIn (G : Gexec) (cs : List Nat) (n : Nat) (e1 e2 : Geid) :
    gwf G → restrOk G cs n → gcut cs e1 = true → gcut cs e2 = true →
    gmoLt G e1 e2 → gmoLt (gxRestrict G cs n) e1 e2 := by
  rintro ⟨hnd, hmem, _⟩ hro hc1 hc2 hmo
  exact (gxrGmoLt G cs n e1 e2 hnd).2
    ⟨restrOkIn G cs n e1 hro ((hmem e1).1 hmo.1) hc1,
     restrOkIn G cs n e2 hro ((hmem e2).1 hmo.2.1) hc2, hmo⟩

/-- THE UNTAGGED CAT MODEL IS PRESERVED BY DOUBLY-CLOSED CUTS. -/
theorem restrictCatConsistent (GD : Gdexec) (cs : List Nat) (n : Nat) :
    rvwmoCatConsistent GD → restrOk GD.gdG cs n →
    rvwmoCatConsistent (gdRestrict GD cs n) := by
  rintro ⟨hwf, hppo, hlv, hat, hdw, hdg⟩ hro
  have hcut : ∀ e, e ∈ GD.gdG.gxGmo.take n → gcut cs e = true :=
    fun e he => restrOkCut _ cs n e hro he
  obtain ⟨hwf', hlv', hat'⟩ := restrictCore GD.gdG cs n hwf hlv hat hro
  refine ⟨hwf', ?_, hlv', hat', ?_, ?_⟩
  · rintro e1 e2 (h6 | h12)
    · obtain ⟨h, hc1, hc2⟩ := gxrGppoCat6 GD.gdG cs n hcut e1 e2 h6
      exact gxrGmoLtIn _ cs n e1 e2 hwf hro hc1 hc2 (hppo e1 e2 (Or.inl h))
    · obtain ⟨h, hc1, hc2⟩ := gxrGppo12 GD.gdG cs n hcut GD.gdDeps
        (gdRestrict GD cs n).gdDeps e1 e2
        (fun x hx => by
          obtain ⟨hx, hx1, _⟩ := (gdRestrictDeps GD cs n x).1 hx
          exact ⟨hx, hx1⟩) h12
      exact gxrGmoLtIn _ cs n e1 e2 hwf hro hc1 hc2 (hppo e1 e2 (Or.inr h))
  · intro rw hrw
    obtain ⟨hrw, hc1, hc2⟩ := (gdRestrictDeps GD cs n rw).1 hrw
    obtain ⟨h1, h2, h3, h4⟩ := hdw rw hrw
    exact ⟨h1, h2, (gxrGlblIs GD.gdG cs n rw.1 lbIsR).2 ⟨hc1, h3⟩,
      (gxrGlblIs GD.gdG cs n rw.2 lbIsW).2 ⟨hc2, h4⟩⟩
  · intro rw hrw
    obtain ⟨hrw, hc1, hc2⟩ := (gdRestrictDeps GD cs n rw).1 hrw
    exact gxrGmoLtIn _ cs n _ _ hwf hro hc1 hc2 (hdg rw hrw)

/-! ## 2.1 The TAGGED model -/

def gtRestrict (GT : GdexecT) (cs : List Nat) (n : Nat) : GdexecT :=
  ⟨gxRestrict GT.gtG cs n,
   GT.gtDeps.filter (fun e : Tdep => gcut cs e.1.1 && gcut cs e.1.2)⟩

theorem gtRestrictDeps (GT : GdexecT) (cs : List Nat) (n : Nat) (e : Tdep) :
    e ∈ (gtRestrict GT cs n).gtDeps ↔
      e ∈ GT.gtDeps ∧ gcut cs e.1.1 = true ∧ gcut cs e.1.2 = true := by
  simp [gtRestrict, List.mem_filter]

theorem restrictCatConsistentT (GT : GdexecT) (cs : List Nat) (n : Nat) :
    rvwmoCatConsistentT GT → restrOk GT.gtG cs n →
    rvwmoCatConsistentT (gtRestrict GT cs n) := by
  rintro ⟨hwf, hppo, hlv, hat, hdw, hdg⟩ hro
  have hcut : ∀ e, e ∈ GT.gtG.gxGmo.take n → gcut cs e = true :=
    fun e he => restrOkCut _ cs n e hro he
  obtain ⟨hwf', hlv', hat'⟩ := restrictCore GT.gtG cs n hwf hlv hat hro
  refine ⟨hwf', ?_, hlv', hat', ?_, ?_⟩
  · rintro e1 e2 (h6 | h12)
    · obtain ⟨h, hc1, hc2⟩ := gxrGppoCat6 GT.gtG cs n hcut e1 e2 h6
      exact gxrGmoLtIn _ cs n e1 e2 hwf hro hc1 hc2 (hppo e1 e2 (Or.inl h))
    · obtain ⟨h, hc1, hc2⟩ := gxrGppo12 GT.gtG cs n hcut (gtAdFull GT.gtG GT.gtDeps)
        (gtAdFull (gtRestrict GT cs n).gtG (gtRestrict GT cs n).gtDeps) e1 e2
        (by
          rintro ⟨a, m⟩ hx
          obtain ⟨tg, hin, had, hw⟩ := (elemOfGtAdFull _ _ _ _).1 hx
          obtain ⟨hin, hca, _⟩ := (gtRestrictDeps GT cs n _).1 hin
          obtain ⟨_, hw⟩ := (gxrGisWTrue GT.gtG cs n m).1 hw
          exact ⟨(elemOfGtAdFull _ _ _ _).2 ⟨tg, hin, had, hw⟩, hca⟩) h12
      exact gxrGmoLtIn _ cs n e1 e2 hwf hro hc1 hc2 (hppo e1 e2 (Or.inr h))
  · intro e he
    obtain ⟨he, hc1, hc2⟩ := (gtRestrictDeps GT cs n e).1 he
    obtain ⟨h1, h2, h3, h4⟩ := hdw e he
    refine ⟨h1, h2, (gxrGlblIs GT.gtG cs n e.1.1 lbIsRT).2 ⟨hc1, h3⟩, ?_⟩
    by_cases hd : dtagW e.2 = true
    · rw [if_pos hd] at h4 ⊢
      exact (gxrGlblIs GT.gtG cs n e.1.2 lbIsWT).2 ⟨hc2, h4⟩
    · rw [if_neg hd] at h4 ⊢
      exact (gxrGmem GT.gtG cs n e.1.2).2 ⟨hc2, h4⟩
  · intro e he
    obtain ⟨he, hc1, hc2⟩ := (gtRestrictDeps GT cs n e).1 he
    exact gxrGmoLtIn _ cs n _ _ hwf hro hc1 hc2 (hdg e he)

/-! # 3. NON-VACUITY: a proper doubly-closed cut of `gfwd` -/

/-- cs = [0; 1], n = 1: hart 0 cut before `sd x`, hart 1 keeps `sd y`. -/
theorem fwdCut1Ok : restrOk gfwd.gdG [0, 1] 1 := by
  refine ⟨rfl, ?_, ?_⟩
  · rintro ⟨i, k⟩ _ hc
    obtain ⟨c, hc, hlt⟩ := gcutElim _ _ hc
    dsimp only at hc hlt
    rcases i with _ | _ | i
    · have : c = 0 := by simp at hc; omega
      omega
    · have : c = 1 := by simp at hc; omega
      have hk : k = 0 := by omega
      subst hk
      decide
    · simp at hc
  · intro e he
    have : e = eSY := by simpa [gfwd] using he
    subst this
    exact gcutIntro _ _ 1 rfl (by decide)

theorem fwdCut1Cat : rvwmoCatConsistent (gdRestrict gfwd [0, 1] 1) :=
  restrictCatConsistent gfwd [0, 1] 1 AxCutProbe.fwdCat fwdCut1Ok

/-- Cross-check of the lemma's conclusion by the decision procedure. -/
theorem fwdCut1CatDirect : rvwmoCatConsistent (gdRestrict gfwd [0, 1] 1) :=
  catConsistentBSound _ (by decide +kernel)

/-- The full cut (n = 3) is the identity. -/
theorem fwdCutFull : restrOk gfwd.gdG (gfullCs gfwd.gdG) 3 :=
  restrOkFull gfwd.gdG AxCutProbe.fwdCat.1

end Weak
