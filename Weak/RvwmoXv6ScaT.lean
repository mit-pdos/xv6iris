/-
Weak: **`linCandScaT` — the TsoMem-floor half of single-copy atomicity is DERIVED at Stage 2**
(allocproc plan §C W11 (iv)b; §B(10) "`candScaT` — G1-Q RULED (e)" / "Stage-2 derivation (W11 (iv)
`linCandScaT`)"; G1-Q (e) [OWN.17], G2-Q (a′) BOTH components [OWN.20][OWN.23]).

Lean-only (no Rocq source).  `candScaT stamp c` (`Weak/TsoShadow.lean`) asks every plain `LLoad`
of a candidate to be single-copy atomic at ONE view `tvn ≤ |log|` that is AT OR ABOVE the TsoMem
shadow's floor `F = max(tv, coh over the footprint)` of the trace prefix before it.  On the
linearization `linCand G` of a graph satisfying the riscv.cat fragment it uses — `gwf`, the six
program-order arms ⊆ gmo (`gppoCat6Gmo`: rules 2, 4, 5 are the ones used), load value — and
rule 14, this is a THEOREM under the merged stamp `TsoShadow.cohSrc` (G2-Q (a′): own-store footprint
RESET + FOREIGN-source-only stamp).  The witness is (iv)a's `tvnSca G r` (the number of writes
gmo-before `r`); the floor is bounded by an invariant of the per-hart shadow fold over the trace:

  (T) `tv` ≤ `tvnSca G r` for every po-LATER read `r` of the hart — `tv` moves only at an `.aq`
      `LRmw` `e` (to `gwix e`; rule 5 `gacqPo` puts `e` gmo-before `r`) and at a fence with an
      R successor (to `ownPub` — rule 4 W→R puts the hart's last store gmo-before `r` — and/or to
      `rv`, rule 4 R→R);
  (R) `rv` is 0 or ≤ `tvnSca G e` of an EARLIER read `e` of the hart (a load's minimal view
      `shTvn` ≤ its `tvnSca`, by induction; an `LRmw`'s `top = gwix e − 1`);
  (C) `coh a` is 0 or ≤ the timestamp of a FOREIGN source of byte `a` read by an earlier read `e0`
      of the hart with NO own write to `a` po-between — the THREE-case derivation of §B(10): a
      later load `r` of `a` reads the SAME source (foreign ⇒ gmo-before `r` by load value), or a
      DIFFERENT one (rule 2 `gppo2`: `e0` gmo-before `r`, the source gmo-before `e0`), and an own
      store to `a` RESETS the stamp (`cohSrc.store`).  Own-sourced bytes are never stamped — the
      component [R11.1-alt] shows load-bearing.

Pieces: (1) the cat-level SCA bytes `RvwmoXv6ScaT.linScaBytes` ((iv)a's `linScaOk` re-proved
WITHOUT `gpoloc ⊆ gmo`: a forwarded source is visible as the hart's OWN message, `scaVis`'s right
disjunct); (2) the trace's author list; (3) the invariant `RvwmoXv6ScaT.shInv`; (4) THE THEOREM
`linCandScaT : gwf G → gppoCat6Gmo G → gloadValue G → grule14 G → candScaT cohSrc (linCand G)`,
with the corollaries `linCandScaTCatT` (from `rvwmoCatConsistentT GT`, the published model, on
`GT.gtG`) and `linCandScaTMinus` (from RVWMO⁻, the current chain's `normalizeOfAcyclic` output).

**W13 (L)** (plan §C W13 (L): "`linCandScaT` re-proved on the anchors"): every piece is stated on
the ANCHORED linearization `linCandA G anc` of an admissible anchor class (`ancOk` replaces rule 14:
anchor-14 is what the rank arguments use; a forwarded source is now emitted before its read by the
trace's po order, `glinAPoLt`): `linCandScaTA`, `linCandScaTMinusA`; `linCandScaT` (statement
unchanged) is the write instance.  The `RvwmoXv6ScaT.*` helpers and the shadow invariant take the
class `anc` as a parameter.

**W11 (iv)c** (plan §C W11 (iv)c; §B(10) "`candDiskLat` — G3-Q RULED (a″) [OWN.17]"), §(6): on the
(L) trace `linCandIO` the disk-row (agent `NCPU`) loads read the LATEST write per byte —
`candDiskLat` is a THEOREM there.  A disk-row read is an (L) anchor (`gisAnc`), so its prefix log
holds exactly the writes gmo-before it (`linNwAAnc`): the SCA witness `tvnSca G r` IS the top of
that log, and `RvwmoXv6ScaT.linScaBytes` (load value's co-maximality) at the top view is `latest`
(`RvwmoXv6ScaT.latestOfScaByte`).  `linCandDiskLatA` (any admissible class containing the disk-row
reads: `gwf`, `gloadValue`, `ancOk`), `linCandDiskLat` (on `linCandIO`, via `ancOkIO`: rule 14,
`ioResidueGmo`, `gdiskRead14`), `linCandDiskLatMinus` (from RVWMO⁻).  `linCandScaT`'s premise list is
unchanged.

No new hypothesis beyond the cat fragment (`gatomicity` and rule 12 are not used).  `Lbl.LIo`
events are handled without `gwf`'s interim `False` arm (they write nothing, and the shadow
ignores them), so W13 (I)/(M)'s flip of that arm does not touch this file.  Lean-only helpers are
file-qualified (`RvwmoXv6ScaT.*`).
-/
import Weak.RvwmoXv6Sca
import Weak.TsoShadow
import Weak.AxDeps
import Weak.WeakRvwmoLin2

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open Lbl
open TsoShadow

/-! ## (1) Cat-level single-copy atomicity bytes (no `gpoloc ⊆ gmo`) -/

/-- Lean-only: a read's named source is emitted before the read — a gmo-before source is an
anchor (a write) gmo-before the read (`glinAGmoAnc`); under cat a forwarded (po-before) source is
emitted before the read by the trace's po order (`glinAPoLt`). -/
theorem RvwmoXv6ScaT.linSourceBefore (G : Gexec) (anc : Geid → Bool) (hwf : gwf G)
    (hlv : gloadValue G) (hok : ancOk G anc) (k : Nat) (r : Geid) (a : Int) (i : Nat)
    (v : BitVec 8) :
    (glinEidsA G anc)[k]? = some r → greadsByte G r a (i + 1) v →
    ∃ kw w, gwriteAt G (i + 1) = some w ∧ (glinEidsA G anc)[kw]? = some w ∧ kw < k := by
  intro hk hrd
  obtain ⟨w, hwa, _, hvis⟩ := (hlv r a (i + 1) v hrd).1
  obtain ⟨hw, _⟩ := gwriteAtInv G (i + 1) w (linNd G hwf) hwa
  obtain ⟨kw, hkw⟩ := glinAIndex G anc hwf hok w (gwritesLbl G hwf w hw)
  refine ⟨kw, w, hwa, hkw, ?_⟩
  rcases hvis with hmo | hpo
  · exact glinAGmoAnc G anc hwf hok k kw r w hk hkw (hok.2.1 w (gwritesIsw G w hw)) hmo
  · exact glinAPoLt G anc hwf hok kw k w r hkw hk hpo.1 hpo.2.1

/-- Lean-only: a read's source fits in its prefix log (cat-level `linReadTsLe`). -/
theorem RvwmoXv6ScaT.linReadTsLe (G : Gexec) (anc : Geid → Bool) (hwf : gwf G)
    (hlv : gloadValue G) (hok : ancOk G anc) (k : Nat) (r : Geid) (a : Int) (t : Nat) (v : BitVec 8) :
    (glinEidsA G anc)[k]? = some r → greadsByte G r a t v → t ≤ (cdLog (linCandA G anc) k).length := by
  intro hk hrd
  rw [linALogLen]
  cases t with
  | zero => omega
  | succ i =>
    obtain ⟨kw, w, hwa, hkw, hlt⟩ := RvwmoXv6ScaT.linSourceBefore G anc hwf hlv hok k r a i v hk hrd
    obtain ⟨hw, hwix⟩ := gwriteAtInv G (i + 1) w (linNd G hwf) hwa
    have hsp := linAGwritesSplit G anc hwf hok kw w hkw (gwritesIsw G w hw)
    rw [gwixOfLookup G (linNwA G anc kw) w (linNd G hwf) hsp] at hwix
    have hS := linANwS G anc kw w hkw (gwritesIsw G w hw)
    have := linANwMono G anc (kw + 1) k (by omega)
    omega

/-- (1) Every byte of a linearized plain load is TsoMem's reading at the witness `tvnSca G r`
(cat level: the forwarded case is `scaVis`'s own-message disjunct). -/
theorem RvwmoXv6ScaT.linScaBytes (G : Gexec) (anc : Geid → Bool) (hwf : gwf G) (hlv : gloadValue G)
    (hok : ancOk G anc)
    (k : Nat) (r : Geid) (aq : Bool) (base : Int) (ts : List Nat) (vs : List (BitVec 8)) :
    (glinEidsA G anc)[k]? = some r → gxLbl G r = some (LLoad aq base ts vs) →
    ∀ (j t : Nat), ts[j]? = some t →
      scaByte G.gxImg (cdLog (linCandA G anc) k) r.1 (tvnSca G r) (accAddr base j) t := by
  intro hk hl j t hj
  have hnd := linNd G hwf
  have hsh : vs.length = ts.length := gwfLblShape G r _ hwf hl
  obtain ⟨rest, hfull⟩ := RvwmoXv6Sca.linLogPrefixA G anc hwf hok k
  have hLB : ∀ t a, t ≤ (cdLog (linCandA G anc) k).length →
      logByte G.gxImg (cdLog (linCandA G anc) k) t a =
        logByte G.gxImg ((gwrites G).filterMap (WeakRvwmoLin.gmsg G)) t a := by
    intro t a ht
    rw [hfull, logByteApp _ _ _ _ _ ht]
  obtain ⟨v, hv⟩ := someOfIsSome
    (lookup_lt_is_Some_2 (show j < vs.length by rw [hsh]; exact lookup_lt_Some hj))
  have hrd : greadsByte G r (accAddr base j) t v := ⟨_, base, ts, vs, j, hl, rfl, hj, hv, rfl⟩
  have htle := RvwmoXv6ScaT.linReadTsLe G anc hwf hlv hok k r _ t v hk hrd
  refine ⟨?_, ?_, ?_⟩
  · -- the source byte is in the prefix log
    rw [hLB t _ htle]
    cases t with
    | zero => rw [logByte0, (hlv r _ 0 v hrd).1]; rfl
    | succ i =>
      obtain ⟨w, hwa, hwb, _⟩ := (hlv r _ (i + 1) v hrd).1
      rw [linLogByteFinal G (i + 1) w _ v hwa hwb]; rfl
  · -- the source is at or below the witness, or the hart's own (forwarded) message
    cases t with
    | zero => exact Or.inl (Nat.zero_le _)
    | succ i =>
      obtain ⟨w, hwa, _, hvis⟩ := (hlv r _ (i + 1) v hrd).1
      obtain ⟨hw, hix⟩ := gwriteAtInv G (i + 1) w hnd hwa
      rcases hvis with hmo | hpo
      · left
        rw [← hix]
        exact (gwixLeTvnSca G r w hwf hw).2 hmo
      · right
        refine ⟨Nat.succ_pos _, ?_⟩
        have hwi : (gwrites G)[i]? = some w := hwa
        obtain ⟨m, hm⟩ := someOfIsSome ((gmsgIsW G w).2 (gwritesIsw G w hw))
        have hmf : ((gwrites G).filterMap (WeakRvwmoLin.gmsg G))[i]? = some m := by
          rw [linLogFullLookup G i w hwi, hm]
        rw [hfull] at hmf
        have hlt : i < (cdLog (linCandA G anc) k).length := by omega
        rw [lookup_app_l hlt] at hmf
        refine ⟨m, hmf, ?_⟩
        rw [RvwmoXv6Sca.gmsgTid G w m hm, hpo.1]
  · -- no later visible same-byte write
    intro t' htt' hsome hvis
    have ht'le := logByteBounded _ _ _ _ hsome
    cases t' with
    | zero => omega
    | succ i' =>
      have hi'lt : i' < (cdLog (linCandA G anc) k).length := by omega
      obtain ⟨m, hm⟩ := someOfIsSome (lookup_lt_is_Some_2 hi'lt)
      have hmf : ((gwrites G).filterMap (WeakRvwmoLin.gmsg G))[i']? = some m := by
        rw [hfull]; exact lookup_app_l_Some hm
      have hgl : i' < (gwrites G).length :=
        Nat.lt_of_lt_of_le (lookup_lt_Some hmf) (List.length_filterMap_le _ _)
      obtain ⟨w', hw'⟩ := someOfIsSome (lookup_lt_is_Some_2 hgl)
      have hgm : WeakRvwmoLin.gmsg G w' = some m := by
        rw [← linLogFullLookup G i' w' hw', hmf]
      have hw'm := gwritesLookupElem G i' w' hw'
      have hix := gwixOfLookup G i' w' hnd hw'
      rw [logByteS, hm] at hsome
      obtain ⟨v', hv'⟩ := someOfIsSome (show (msgByte m (accAddr base j)).isSome from hsome)
      have hwb := gmsgByteInv G w' m _ v' hgm hv'
      have hvis' : gvisible G w' r := by
        rcases hvis with hle | ⟨_, m0, hm0, htid⟩
        · exact Or.inl ((gwixLeTvnSca G r w' hwf hw'm).1 (by rw [hix]; exact hle))
        · simp only [Nat.add_sub_cancel] at hm0
          rw [hm, Option.some.injEq] at hm0
          subst hm0
          rw [RvwmoXv6Sca.gmsgTid G w' m hgm, Option.some.injEq] at htid
          obtain ⟨k', hk', hk'w⟩ := linLogEmittedA G anc hwf hok k (i' + 1) r w' hk hw' ht'le
          refine Or.inr ⟨htid, ?_, glinALookupLbl G anc hwf hok k' w' hk'w, glinALookupLbl G anc hwf hok k r hk⟩
          exact (glinAPoIff G anc hwf hok k' k w' r hk'w hk htid).1 hk'
      have := gcomax G hlv r _ t v w' v' hrd hwb hvis'
      omega

/-! ## (2) Graph facts: foreign sources, positions, the trace's authors -/

/-- Lean-only: a FOREIGN source of a read byte is gmo-before the read (load value; po needs the
same hart). -/
theorem RvwmoXv6ScaT.foreignGmo (G : Gexec) (hlv : gloadValue G) (e : Geid) (a : Int) (t : Nat)
    (v : BitVec 8) (w' : Geid) :
    greadsByte G e a t v → gwriteAt G t = some w' → w'.1 ≠ e.1 → gmoLt G w' e := by
  intro hrd hwa hne
  cases t with
  | zero => simp [gwriteAt] at hwa
  | succ n =>
    obtain ⟨w, hw, _, hvis⟩ := (hlv e a (n + 1) v hrd).1
    rw [hwa, Option.some.injEq] at hw
    subst hw
    rcases hvis with h | h
    · exact h
    · exact absurd h.1 hne

/-- Lean-only: a write gmo-before `r` at timestamp `t` bounds `t` by the witness. -/
theorem RvwmoXv6ScaT.tsLeTvnSca (G : Gexec) (hwf : gwf G) (r w : Geid) (t : Nat) :
    gwriteAt G t = some w → gmoLt G w r → t ≤ tvnSca G r := by
  intro hwa hmo
  obtain ⟨hw, hix⟩ := gwriteAtInv G t w (linNd G hwf) hwa
  rw [← hix]
  exact (gwixLeTvnSca G r w hwf hw).2 hmo

/-- Lean-only: a write's timestamp in the linearization is one past the writes before it. -/
theorem RvwmoXv6ScaT.gwixLin (G : Gexec) (anc : Geid → Bool) (hwf : gwf G) (hok : ancOk G anc)
    (k : Nat) (e : Geid) :
    (glinEidsA G anc)[k]? = some e → gisW G e = true → gwix G e = linNwA G anc k + 1 :=
  fun hk hw => gwixOfLookup G _ e (linNd G hwf) (linAGwritesSplit G anc hwf hok k e hk hw)

/-- Lean-only: the writes emitted before a write `e` are all gmo-before it, so their count is at
most `tvnSca G e`. -/
theorem RvwmoXv6ScaT.linNwLeTvnSca (G : Gexec) (anc : Geid → Bool) (hwf : gwf G)
    (hok : ancOk G anc) (k : Nat) (e : Geid) :
    (glinEidsA G anc)[k]? = some e → gisW G e = true → linNwA G anc k ≤ tvnSca G e := by
  intro hk hw
  have hnd := linNd G hwf
  have hsp := linAGwritesSplit G anc hwf hok k e hk hw
  have he := gwritesLookupElem G _ e hsp
  cases hn : linNwA G anc k with
  | zero => exact Nat.zero_le _
  | succ n =>
    have hlt : n < (gwrites G).length := by have := lookup_lt_Some hsp; omega
    obtain ⟨w0, hw0⟩ := someOfIsSome (lookup_lt_is_Some_2 hlt)
    have hw0m := gwritesLookupElem G n w0 hw0
    have hix0 := gwixOfLookup G n w0 hnd hw0
    have hixe := gwixOfLookup G _ e hnd hsp
    have hpos := (gwixGposLt G w0 e hnd hw0m he).1 (by omega)
    have hmo : gmoLt G w0 e := ⟨gwritesGmo G w0 hw0m, gwritesGmo G e he, hpos⟩
    have := (gwixLeTvnSca G e w0 hwf hw0m).2 hmo
    omega

/-- Lean-only: `glbl`'s write test is `gisW`. -/
theorem RvwmoXv6ScaT.lbIsWGlbl (G : Gexec) (e : Geid) : lbIsW (glbl G e) = gisW G e := by
  unfold glbl gisW
  cases gxLbl G e <;> rfl

/-- Lean-only: the trace's authors are its writes' rows. -/
theorem RvwmoXv6ScaT.stAuthorsLin (G : Gexec) (l : List Geid) :
    stAuthorsL (l.map (glinStep G)) = (l.filter (gisW G)).map Prod.fst := by
  induction l with
  | nil => rfl
  | cons e l ih =>
    have hw : lbIsW (glinStep G e).esLb = gisW G e := RvwmoXv6ScaT.lbIsWGlbl G e
    unfold stAuthorsL at ih ⊢
    rw [List.map_cons, List.filterMap_cons, List.filter_cons, hw, ih]
    cases gisW G e <;> rfl

/-- Lean-only: the author list of the trace prefix has one entry per emitted write. -/
theorem RvwmoXv6ScaT.authorsLen (G : Gexec) (anc : Geid → Bool) (k : Nat) :
    (stAuthorsL (((glinEidsA G anc).take k).map (glinStep G))).length = linNwA G anc k := by
  rw [RvwmoXv6ScaT.stAuthorsLin, List.length_map]
  rfl

/-- Lean-only: author `n` of the trace prefix is the row of write `n` in gmo order, emitted
before position `k`. -/
theorem RvwmoXv6ScaT.authorsLookup (G : Gexec) (anc : Geid → Bool) (hwf : gwf G)
    (hok : ancOk G anc) (k n x : Nat) :
    (stAuthorsL (((glinEidsA G anc).take k).map (glinStep G)))[n]? = some x →
    ∃ kw w, kw < k ∧ (glinEidsA G anc)[kw]? = some w ∧ (gwrites G)[n]? = some w ∧ w.1 = x := by
  rw [RvwmoXv6ScaT.stAuthorsLin, List.getElem?_map]
  intro h
  cases hn : (((glinEidsA G anc).take k).filter (gisW G))[n]? with
  | none => rw [hn] at h; cases h
  | some w =>
    rw [hn] at h
    simp only [Option.map_some, Option.some.injEq] at h
    have hmem : w ∈ (glinEidsA G anc).take k := (List.mem_filter.1 (elem_of_list_lookup_2 hn)).1
    obtain ⟨kw, hkw⟩ := elem_of_list_lookup_1 hmem
    have hkwlt : kw < k := by
      have := lookup_lt_Some hkw
      simp only [List.length_take] at this
      omega
    refine ⟨kw, w, hkwlt, by rw [← lookup_take hkwlt]; exact hkw, ?_, h⟩
    rw [← glinAWrites G anc hwf hok, ← List.take_append_drop k (glinEidsA G anc), List.filter_append]
    exact lookup_app_l_Some hn

/-- Lean-only: `ownPub` names a message of its agent. -/
theorem RvwmoXv6ScaT.ownPubAuxLookup (h : Nat) : ∀ (l : List Nat) (b : Nat),
    ownPubAux h l b ≠ 0 → b + 1 ≤ ownPubAux h l b ∧ l[ownPubAux h l b - b - 1]? = some h
  | [], b, hne => by simp [ownPubAux] at hne
  | a :: l, b, hne => by
    by_cases hr : ownPubAux h l (b + 1) = 0
    · have hv : ownPubAux h (a :: l) b = if a = h then b + 1 else 0 := by
        simp only [ownPubAux, hr]; simp
      rw [hv] at hne ⊢
      by_cases ha : a = h
      · rw [if_pos ha]
        refine ⟨Nat.le_refl _, ?_⟩
        rw [show b + 1 - b - 1 = 0 by omega, ha]
        rfl
      · rw [if_neg ha] at hne; exact absurd rfl hne
    · have hv : ownPubAux h (a :: l) b = ownPubAux h l (b + 1) := by
        simp only [ownPubAux]; split <;> simp_all
      obtain ⟨h1, h2⟩ := RvwmoXv6ScaT.ownPubAuxLookup h l (b + 1) hr
      rw [hv]
      refine ⟨by omega, ?_⟩
      rw [show ownPubAux h l (b + 1) - b - 1 = (ownPubAux h l (b + 1) - (b + 1) - 1) + 1 by omega]
      exact h2

theorem RvwmoXv6ScaT.ownPubLookup (h : Nat) (l : List Nat) :
    ownPub h l ≠ 0 → l[ownPub h l - 1]? = some h := by
  intro hne
  have := (RvwmoXv6ScaT.ownPubAuxLookup h l 0 hne).2
  unfold ownPub
  rw [show ownPubAux h l 0 - 1 = ownPubAux h l 0 - 0 - 1 by omega]
  exact this

/-! ## (3) Stamp facts -/

/-- Lean-only: a `cohSrc` load stamp either keeps the floor or takes the max with a FOREIGN
source's timestamp. -/
theorem RvwmoXv6ScaT.cohSrcLoadCases (i : Nat) (coh : Int → Nat) (base : Int)
    (srcs : List (Option (Nat × Nat))) (tvn : Nat) (a : Int) :
    cohSrc.load i coh base srcs tvn a = coh a ∨
    ∃ j x t, a = accAddr base j ∧ srcs[j]? = some (some (x, t)) ∧ x ≠ i ∧
      cohSrc.load i coh base srcs tvn a = max (coh a) t := by
  cases hf : footIdx base srcs.length a with
  | none => left; exact cohSrcLoadOut i coh base srcs tvn a hf
  | some j =>
    obtain ⟨_, ha⟩ := (footIdxSome base _ a j).1 hf
    cases hs : srcs[j]? with
    | none => left; simp only [cohSrc, hf, hs]
    | some o =>
      cases o with
      | none => left; simp only [cohSrc, hf, hs]
      | some p =>
        obtain ⟨x, t⟩ := p
        by_cases hx : x = i
        · left; simp only [cohSrc, hf, hs, if_pos hx]
        · right
          refine ⟨j, x, t, ha, hs, hx, ?_⟩
          simp only [cohSrc, hf, hs, if_neg hx]

/-- Lean-only: a `cohSrc` store resets its footprint and keeps the rest. -/
theorem RvwmoXv6ScaT.cohSrcStoreCases (coh : Int → Nat) (base : Int) (n : Nat) (a : Int) :
    cohSrc.store coh base n a = 0 ∨
    (footIdx base n a = none ∧ cohSrc.store coh base n a = coh a) := by
  cases h : footIdx base n a with
  | none => right; exact ⟨rfl, cohSrcStoreOut coh base n a h⟩
  | some j => left; simp only [cohSrc, h]

/-- Lean-only: the source list entry's shape. -/
theorem RvwmoXv6ScaT.shSrcSome (au : List Nat) (t0 x t : Nat) :
    shSrc au t0 = some (x, t) → t = 0 ∨ (t = t0 ∧ 0 < t0 ∧ au[t0 - 1]? = some x) := by
  unfold shSrc
  intro h
  by_cases h0 : t0 = 0
  · rw [if_pos h0, Option.some.injEq, Prod.mk.injEq] at h
    exact Or.inl h.2.symm
  · rw [if_neg h0] at h
    right
    cases hl : au[t0 - 1]? with
    | none => rw [hl] at h; cases h
    | some y =>
      rw [hl] at h
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨rfl, by omega, rfl⟩

/-- Lean-only: an event whose label writes nothing writes no byte. -/
theorem RvwmoXv6ScaT.noWrite (G : Gexec) (e : Geid) (l : Lbl) (a : Int) (v : BitVec 8) :
    gxLbl G e = some l → lbWr l = none → ¬ gwritesByte G e a v := by
  rintro hl hw ⟨l', base, vs, j, hl', hw', _⟩
  rw [hl, Option.some.injEq] at hl'
  subst hl'
  rw [hw] at hw'
  cases hw'

/-- Lean-only: a written byte is in the label's write footprint. -/
theorem RvwmoXv6ScaT.writesFoot (G : Gexec) (e : Geid) (l : Lbl) (base : Int)
    (vs : List (BitVec 8)) (a : Int) (v : BitVec 8) :
    gxLbl G e = some l → lbWr l = some (base, vs) → gwritesByte G e a v →
    footIdx base vs.length a ≠ none := by
  rintro hl hw ⟨l', base', vs', j, hl', hw', hj, ha⟩
  rw [hl, Option.some.injEq] at hl'
  subst hl'
  rw [hw, Option.some.injEq, Prod.mk.injEq] at hw'
  obtain ⟨rfl, rfl⟩ := hw'
  rw [← ha, footIdxAcc _ vs.length j (lookup_lt_Some hj)]
  simp

/-- Lean-only: the largest footprint floor is bounded by any common bound. -/
theorem RvwmoXv6ScaT.cohMaxLe (coh : Int → Nat) (base : Int) (B : Nat) :
    ∀ n, (∀ j, j < n → coh (accAddr base j) ≤ B) → cohMax coh base n ≤ B
  | 0, _ => Nat.zero_le _
  | n + 1, h => by
    simp only [cohMax]
    have := RvwmoXv6ScaT.cohMaxLe coh base B n (fun j hj => h j (by omega))
    have := h n (by omega)
    omega

/-- Lean-only: the largest foreign source timestamp is bounded by any bound on the foreign
entries. -/
theorem RvwmoXv6ScaT.shForeignLe (i B : Nat) :
    ∀ srcs : List (Option (Nat × Nat)),
      (∀ x t, some (x, t) ∈ srcs → x ≠ i → t ≤ B) → shForeign i srcs ≤ B
  | [], _ => Nat.zero_le _
  | none :: r, h => by
    simp only [shForeign]
    exact RvwmoXv6ScaT.shForeignLe i B r (fun x t hm hx => h x t (by simp [hm]) hx)
  | some (x, t) :: r, h => by
    have ih := RvwmoXv6ScaT.shForeignLe i B r (fun x t hm hx => h x t (by simp [hm]) hx)
    simp only [shForeign]
    by_cases hx : x = i
    · rw [if_pos hx]; exact ih
    · rw [if_neg hx]
      have := h x t (by simp) hx
      omega

/-! ## (4) The shadow invariant -/

/-- Lean-only: the shadow fold of hart `i` over the first `k` linearized steps. -/
def RvwmoXv6ScaT.shK (G : Gexec) (anc : Geid → Bool) (i k : Nat) : List Nat × ShSt :=
  shadowRun cohSrc i (((glinEidsA G anc).take k).map (glinStep G))

/-- (T) `tv` is below the witness of every read of the hart at or after position `k`. -/
def RvwmoXv6ScaT.tvOk (G : Gexec) (anc : Geid → Bool) (i k tv : Nat) : Prop :=
  ∀ r kr, k ≤ kr → (glinEidsA G anc)[kr]? = some r → r.1 = i → glblIs G r lbIsR → tv ≤ tvnSca G r

/-- (R) `rv` is 0 or below the witness of a read of the hart before position `k`. -/
def RvwmoXv6ScaT.rvOk (G : Gexec) (anc : Geid → Bool) (i k rv : Nat) : Prop :=
  rv = 0 ∨ ∃ e ke, ke < k ∧ (glinEidsA G anc)[ke]? = some e ∧ e.1 = i ∧ glblIs G e lbIsR ∧
    rv ≤ tvnSca G e

/-- (C) at byte `a`: the floor `c` is below a FOREIGN source timestamp of a read of `a` by the
hart before position `k`, with no own write to `a` since. -/
def RvwmoXv6ScaT.cohWit (G : Gexec) (anc : Geid → Bool) (i k : Nat) (a : Int) (c : Nat) : Prop :=
  ∃ e ke t v w', ke < k ∧ (glinEidsA G anc)[ke]? = some e ∧ e.1 = i ∧ greadsByte G e a t v ∧
    gwriteAt G t = some w' ∧ w'.1 ≠ i ∧ c ≤ t ∧
    ∀ m km v', ke < km → km < k → (glinEidsA G anc)[km]? = some m → m.1 = i → ¬ gwritesByte G m a v'

def RvwmoXv6ScaT.cohOk (G : Gexec) (anc : Geid → Bool) (i k : Nat) (coh : Int → Nat) : Prop :=
  ∀ a, coh a = 0 ∨ RvwmoXv6ScaT.cohWit G anc i k a (coh a)

theorem RvwmoXv6ScaT.tvOkStep (G : Gexec) (anc : Geid → Bool) (i k tv : Nat) :
    RvwmoXv6ScaT.tvOk G anc i k tv → RvwmoXv6ScaT.tvOk G anc i (k + 1) tv :=
  fun h r kr hkr => h r kr (by omega)

theorem RvwmoXv6ScaT.rvOkStep (G : Gexec) (anc : Geid → Bool) (i k rv : Nat) :
    RvwmoXv6ScaT.rvOk G anc i k rv → RvwmoXv6ScaT.rvOk G anc i (k + 1) rv := by
  rintro (h | ⟨e, ke, hke, h⟩)
  · exact Or.inl h
  · exact Or.inr ⟨e, ke, by omega, h⟩

/-- A witness survives a step that does not write `a` on the hart. -/
theorem RvwmoXv6ScaT.cohWitStep (G : Gexec) (anc : Geid → Bool) (i k : Nat) (e : Geid) (a : Int) (c : Nat)
    (hk : (glinEidsA G anc)[k]? = some e) (hno : e.1 = i → ∀ v', ¬ gwritesByte G e a v') :
    RvwmoXv6ScaT.cohWit G anc i k a c → RvwmoXv6ScaT.cohWit G anc i (k + 1) a c := by
  rintro ⟨e0, ke, t, v, w', hke, h0, hi, hrd, hwa, hne, hc, hnw⟩
  refine ⟨e0, ke, t, v, w', by omega, h0, hi, hrd, hwa, hne, hc, ?_⟩
  intro m km v' h1 h2 hm hmi
  by_cases hkm : km = k
  · subst hkm
    rw [hk, Option.some.injEq] at hm
    subst hm
    exact hno hmi v'
  · exact hnw m km v' h1 (by omega) hm hmi

theorem RvwmoXv6ScaT.cohOkStep (G : Gexec) (anc : Geid → Bool) (i k : Nat) (e : Geid) (coh : Int → Nat)
    (hk : (glinEidsA G anc)[k]? = some e) (hno : e.1 = i → ∀ a v', ¬ gwritesByte G e a v') :
    RvwmoXv6ScaT.cohOk G anc i k coh → RvwmoXv6ScaT.cohOk G anc i (k + 1) coh := by
  intro h a
  rcases h a with h0 | hw
  · exact Or.inl h0
  · exact Or.inr (RvwmoXv6ScaT.cohWitStep G anc i k e a _ hk (fun hi => hno hi a) hw)

section inv

variable (G : Gexec) (anc : Geid → Bool) (hwf : gwf G) (h6 : gppoCat6Gmo G) (hlv : gloadValue G)
  (hok : ancOk G anc)
include hwf h6 hlv hok

/-- THE FLOOR at a load: `F = max(tv, coh over the footprint) ≤ tvnSca G e` — the `coh` part
is §B(10)'s three-case derivation (same source / different source by rule 2; own stores reset). -/
theorem RvwmoXv6ScaT.loadFloor (i k : Nat) (sh : ShSt) (e : Geid) (aq : Bool) (base : Int)
    (ts : List Nat) (vs : List (BitVec 8)) (hk : (glinEidsA G anc)[k]? = some e) (hi : e.1 = i)
    (hl : gxLbl G e = some (LLoad aq base ts vs))
    (hT : RvwmoXv6ScaT.tvOk G anc i k sh.tv) (hC : RvwmoXv6ScaT.cohOk G anc i k sh.coh) :
    shFloor sh base ts.length ≤ tvnSca G e := by
  have hR : glblIs G e lbIsR := ⟨_, hl, rfl⟩
  have htv := hT e k (Nat.le_refl _) hk hi hR
  have hsh : vs.length = ts.length := gwfLblShape G e _ hwf hl
  have hcoh : ∀ j, j < ts.length → sh.coh (accAddr base j) ≤ tvnSca G e := by
    intro j hj
    rcases hC (accAddr base j) with h0 | ⟨e0, ke, t0, v0, w', hke, h0, hi0, hrd0, hwa, hne, hc, hnw⟩
    · rw [h0]; exact Nat.zero_le _
    · obtain ⟨t, ht⟩ := someOfIsSome (lookup_lt_is_Some_2 hj)
      obtain ⟨v, hv⟩ := someOfIsSome
        (lookup_lt_is_Some_2 (show j < vs.length by rw [hsh]; exact hj))
      have hrd : greadsByte G e (accAddr base j) t v := ⟨_, base, ts, vs, j, hl, rfl, ht, hv, rfl⟩
      have hmo0 : gmoLt G w' e0 :=
        RvwmoXv6ScaT.foreignGmo G hlv e0 _ t0 v0 w' hrd0 hwa (by rw [hi0]; exact hne)
      have hpo0 : e0.2 < e.2 :=
        (glinAPoIff G anc hwf hok ke k e0 e h0 hk (by rw [hi0, hi])).1 hke
      apply Nat.le_trans hc
      by_cases htt : t = t0
      · -- the SAME source: foreign, hence gmo-before `e`
        subst htt
        exact RvwmoXv6ScaT.tsLeTvnSca G hwf e w' t hwa
          (RvwmoXv6ScaT.foreignGmo G hlv e _ t v w' hrd hwa (by rw [hi]; exact hne))
      · -- a DIFFERENT source, no own write po-between: rule 2
        have h2 : gppo2 G e0 e := by
          refine ⟨⟨by rw [hi0, hi], hpo0, glinALookupLbl G anc hwf hok ke e0 h0,
            glinALookupLbl G anc hwf hok k e hk⟩, accAddr base j, t0, v0, t, v, hrd0, hrd,
            fun h => htt h.symm, ?_⟩
          intro m vm hwm hpo1 hpo2
          obtain ⟨km, hkm⟩ := glinAIndex G anc hwf hok m hpo1.2.2.2
          have hmi : m.1 = i := by rw [← hpo1.1, hi0]
          have h1 := (glinAPoIff G anc hwf hok ke km e0 m h0 hkm hpo1.1).2 hpo1.2.1
          have h2 := (glinAPoIff G anc hwf hok km k m e hkm hk hpo2.1).2 hpo2.2.1
          exact hnw m km vm h1 h2 hkm hmi hwm
        have hmo : gmoLt G e0 e := h6 _ _ (Or.inr (Or.inl h2))
        exact RvwmoXv6ScaT.tsLeTvnSca G hwf e w' t0 hwa (gmoLtTrans G w' e0 e hmo0 hmo)
  unfold shFloor
  have := RvwmoXv6ScaT.cohMaxLe sh.coh base (tvnSca G e) ts.length hcoh
  omega

/-- The load's MINIMAL view `shTvn` is below its witness. -/
theorem RvwmoXv6ScaT.loadTvn (i k : Nat) (sh : ShSt) (e : Geid) (aq : Bool) (base : Int)
    (ts : List Nat) (vs : List (BitVec 8)) (hk : (glinEidsA G anc)[k]? = some e) (hi : e.1 = i)
    (hl : gxLbl G e = some (LLoad aq base ts vs))
    (hT : RvwmoXv6ScaT.tvOk G anc i k sh.tv) (hC : RvwmoXv6ScaT.cohOk G anc i k sh.coh) :
    shTvn i sh base (ts.map (shSrc (stAuthorsL (((glinEidsA G anc).take k).map (glinStep G))))) ≤
      tvnSca G e := by
  have hF := RvwmoXv6ScaT.loadFloor G anc hwf h6 hlv hok i k sh e aq base ts vs hk hi hl hT hC
  have hsh : vs.length = ts.length := gwfLblShape G e _ hwf hl
  unfold shTvn
  rw [List.length_map]
  have hfor := RvwmoXv6ScaT.shForeignLe i (tvnSca G e)
    (ts.map (shSrc (stAuthorsL (((glinEidsA G anc).take k).map (glinStep G))))) (by
      intro x t hm hx
      obtain ⟨t0, ht0, hs⟩ := List.mem_map.1 hm
      rcases RvwmoXv6ScaT.shSrcSome _ t0 x t hs with h0 | ⟨rfl, hpos, hau⟩
      · rw [h0]; exact Nat.zero_le _
      · obtain ⟨_, w', _, _, hw', hw'1⟩ := RvwmoXv6ScaT.authorsLookup G anc hwf hok k (t - 1) x hau
        obtain ⟨j, hj⟩ := elem_of_list_lookup_1 ht0
        obtain ⟨v, hv⟩ := someOfIsSome
          (lookup_lt_is_Some_2 (show j < vs.length by rw [hsh]; exact lookup_lt_Some hj))
        have hrd : greadsByte G e (accAddr base j) t v := ⟨_, base, ts, vs, j, hl, rfl, hj, hv, rfl⟩
        have hwa : gwriteAt G t = some w' := by
          rw [show t = (t - 1) + 1 by omega]; exact hw'
        exact RvwmoXv6ScaT.tsLeTvnSca G hwf e w' t hwa
          (RvwmoXv6ScaT.foreignGmo G hlv e _ t v w' hrd hwa (by rw [hw'1, hi]; exact hx)))
  exact Nat.max_le.2 ⟨hF, hfor⟩

/-- Lean-only: one step of the fold. -/
theorem RvwmoXv6ScaT.shKSucc (i k : Nat) (e : Geid) (hk : (glinEidsA G anc)[k]? = some e) :
    RvwmoXv6ScaT.shK G anc i (k + 1) = shActL cohSrc i (RvwmoXv6ScaT.shK G anc i k) (glinStep G e) := by
  unfold RvwmoXv6ScaT.shK
  rw [take_S_r hk, List.map_append, List.map_cons, List.map_nil]
  exact shadowRunSnoc cohSrc i _ _

/-- (3) THE INVARIANT of hart `i`'s shadow along the linearized trace. -/
theorem RvwmoXv6ScaT.shInv (i : Nat) : ∀ k, k ≤ (glinEidsA G anc).length →
    RvwmoXv6ScaT.tvOk G anc i k (RvwmoXv6ScaT.shK G anc i k).2.tv ∧
    RvwmoXv6ScaT.rvOk G anc i k (RvwmoXv6ScaT.shK G anc i k).2.rv ∧
    RvwmoXv6ScaT.cohOk G anc i k (RvwmoXv6ScaT.shK G anc i k).2.coh
  | 0, _ => by
    refine ⟨fun _ _ _ _ _ _ => Nat.zero_le _, Or.inl rfl, fun _ => Or.inl rfl⟩
  | k + 1, hkl => by
    obtain ⟨hT, hR, hC⟩ := RvwmoXv6ScaT.shInv i k (by omega)
    obtain ⟨e, hk⟩ := someOfIsSome (lookup_lt_is_Some_2 (show k < (glinEidsA G anc).length by omega))
    have hl := linALbl G anc hwf hok k e hk
    have hau1 : (RvwmoXv6ScaT.shK G anc i k).1 =
        stAuthorsL (((glinEidsA G anc).take k).map (glinStep G)) := shadowRunAuthors cohSrc i _
    have hlen : (RvwmoXv6ScaT.shK G anc i k).1.length = linNwA G anc k := by
      rw [hau1, RvwmoXv6ScaT.authorsLen]
    have h2 : (RvwmoXv6ScaT.shK G anc i (k + 1)).2 =
        if e.1 = i then shStepL cohSrc i (RvwmoXv6ScaT.shK G anc i k).1 (RvwmoXv6ScaT.shK G anc i k).2
          (glbl G e) else (RvwmoXv6ScaT.shK G anc i k).2 := by
      rw [RvwmoXv6ScaT.shKSucc G anc hwf h6 hlv hok i k e hk]; rfl
    rw [h2]
    generalize hx : RvwmoXv6ScaT.shK G anc i k = x at hT hR hC hau1 hlen
    obtain ⟨au, sh⟩ := x
    simp only at hT hR hC hau1 hlen ⊢
    by_cases hei : e.1 = i
    · rw [if_pos hei]
      generalize hlb : glbl G e = lb at hl
      cases lb with
      | LLoad aq base ts vs =>
        have hno : ∀ a v', ¬ gwritesByte G e a v' :=
          fun a v' => RvwmoXv6ScaT.noWrite G e _ a v' hl rfl
        have hTv := RvwmoXv6ScaT.loadTvn G anc hwf h6 hlv hok i k sh e aq base ts vs hk hei hl hT hC
        rw [← hau1] at hTv
        refine ⟨RvwmoXv6ScaT.tvOkStep G anc i k _ hT, ?_, ?_⟩
        · -- rv := max rv tvn
          show RvwmoXv6ScaT.rvOk G anc i (k + 1) (max sh.rv (shTvn i sh base (ts.map (shSrc au))))
          by_cases hle : sh.rv ≤ shTvn i sh base (ts.map (shSrc au))
          · rw [Nat.max_eq_right hle]
            exact Or.inr ⟨e, k, Nat.lt_succ_self _, hk, hei, ⟨_, hl, rfl⟩, hTv⟩
          · rw [Nat.max_eq_left (by omega)]
            exact RvwmoXv6ScaT.rvOkStep G anc i k _ hR
        · -- the stamp
          show RvwmoXv6ScaT.cohOk G anc i (k + 1)
            (cohSrc.load i sh.coh base (ts.map (shSrc au)) (shTvn i sh base (ts.map (shSrc au))))
          intro a
          have hold : sh.coh a = 0 ∨ RvwmoXv6ScaT.cohWit G anc i (k + 1) a (sh.coh a) := by
            rcases hC a with h0 | hw
            · exact Or.inl h0
            · exact Or.inr (RvwmoXv6ScaT.cohWitStep G anc i k e a _ hk (fun _ => hno a) hw)
          rcases RvwmoXv6ScaT.cohSrcLoadCases i sh.coh base (ts.map (shSrc au))
              (shTvn i sh base (ts.map (shSrc au))) a with heq | ⟨j, x, t, ha, hj, hx, heq⟩
          · rw [heq]; exact hold
          · rw [heq]
            rw [List.getElem?_map] at hj
            cases ht0 : ts[j]? with
            | none => rw [ht0] at hj; cases hj
            | some t0 =>
              rw [ht0] at hj
              simp only [Option.map_some, Option.some.injEq] at hj
              rcases RvwmoXv6ScaT.shSrcSome au t0 x t hj with h0 | ⟨rfl, hpos, hau⟩
              · rw [h0, Nat.max_eq_left (Nat.zero_le _)]; exact hold
              · by_cases hle : sh.coh a ≤ t
                · rw [Nat.max_eq_right hle]
                  right
                  rw [hau1] at hau
                  obtain ⟨_, w', _, _, hw', hw'1⟩ := RvwmoXv6ScaT.authorsLookup G anc hwf hok k (t - 1) x hau
                  have hwa : gwriteAt G t = some w' := by
                    rw [show t = (t - 1) + 1 by omega]; exact hw'
                  have hsh : vs.length = ts.length := gwfLblShape G e _ hwf hl
                  obtain ⟨v, hv⟩ := someOfIsSome
                    (lookup_lt_is_Some_2 (show j < vs.length by rw [hsh]; exact lookup_lt_Some ht0))
                  refine ⟨e, k, t, v, w', Nat.lt_succ_self _, hk, hei,
                    ⟨_, base, ts, vs, j, hl, rfl, ht0, hv, ha.symm⟩, hwa, by rw [hw'1]; exact hx,
                    Nat.le_refl _, ?_⟩
                  intro m km v' h1 h2' _ _
                  omega
                · rw [Nat.max_eq_left (by omega)]
                  rcases hold with h0 | hw
                  · omega
                  · exact Or.inr hw
      | LStore rl base vs cl =>
        refine ⟨?_, RvwmoXv6ScaT.rvOkStep G anc i k _ hR, ?_⟩
        · show RvwmoXv6ScaT.tvOk G anc i (k + 1) (if false && sh.acq then au.length + 1 else sh.tv)
          simp only [Bool.false_and]
          exact RvwmoXv6ScaT.tvOkStep G anc i k _ hT
        · show RvwmoXv6ScaT.cohOk G anc i (k + 1) (cohSrc.store sh.coh base vs.length)
          intro a
          rcases RvwmoXv6ScaT.cohSrcStoreCases sh.coh base vs.length a with h0 | ⟨hf, heq⟩
          · exact Or.inl h0
          · rw [heq]
            rcases hC a with h0 | hw
            · exact Or.inl h0
            · exact Or.inr (RvwmoXv6ScaT.cohWitStep G anc i k e a _ hk
                (fun _ v' hwb => RvwmoXv6ScaT.writesFoot G e _ base vs a v' hl rfl hwb hf) hw)
      | LFence pr pw sr sw =>
        have hno : ∀ a v', ¬ gwritesByte G e a v' :=
          fun a v' => RvwmoXv6ScaT.noWrite G e _ a v' hl rfl
        refine ⟨?_, RvwmoXv6ScaT.rvOkStep G anc i k _ hR,
          RvwmoXv6ScaT.cohOkStep G anc i k e _ hk (fun _ => hno) hC⟩
        show RvwmoXv6ScaT.tvOk G anc i (k + 1)
          (MachCSL.fencePost (pw && sr) (pr && sr) sh.tv sh.rv (MachCSL.ownPub i au))
        intro r kr hkr hr hri hrR
        have hpoe : e.2 < r.2 := (glinAPoIff G anc hwf hok k kr e r hk hr (by rw [hei, hri])).1 (by omega)
        have hrl := glinALookupLbl G anc hwf hok kr r hr
        have hel : gxLbl G (r.1, e.2) = some (LFence pr pw sr sw) := by
          rw [show ((r.1, e.2) : Geid) = e from Prod.ext (by rw [hri, hei]) rfl]; exact hl
        unfold MachCSL.fencePost
        have htv := hT r kr (by omega) hr hri hrR
        -- the drain arm: the hart's last store is fence-ordered before `r`
        have hpub : (pw && sr) = true → MachCSL.ownPub i au ≤ tvnSca G r := by
          intro hd
          simp only [Bool.and_eq_true] at hd
          rw [hau1]
          by_cases hp0 : MachCSL.ownPub i (stAuthorsL (((glinEidsA G anc).take k).map (glinStep G))) = 0
          · rw [hp0]; exact Nat.zero_le _
          · have hlk := RvwmoXv6ScaT.ownPubLookup i _ hp0
            obtain ⟨kw, w, hkw, hw, hgw, hw1⟩ := RvwmoXv6ScaT.authorsLookup G anc hwf hok k _ i hlk
            have hwm := gwritesLookupElem G _ w hgw
            have hpow : w.2 < e.2 := (glinAPoIff G anc hwf hok kw k w e hw hk (by rw [hw1, hei])).1 hkw
            have hcov : gfenceCovers G w r :=
              ⟨pr, pw, sr, sw, ⟨by rw [hw1, hri], by omega, e.2, hpow, hpoe,
                by rw [show w.1 = r.1 by rw [hw1, hri]]; exact hel⟩,
                Or.inr ⟨WeakRvwmoAcyc.gisWGlblIs G w (gwritesIsw G w hwm), hd.1⟩,
                Or.inl ⟨hrR, hd.2⟩⟩
            have hmo : gmoLt G w r := h6 _ _ (Or.inr (Or.inr (Or.inr (Or.inl hcov))))
            have hix := gwixOfLookup G _ w (linNd G hwf) hgw
            have := (gwixLeTvnSca G r w hwf hwm).2 hmo
            omega
        -- the acquire arm: the read watermark's read is fence-ordered before `r`
        have hrv : (pr && sr) = true → sh.rv ≤ tvnSca G r := by
          intro ha
          simp only [Bool.and_eq_true] at ha
          rcases hR with h0 | ⟨e0, ke, hke, h0, hi0, hR0, hle⟩
          · rw [h0]; exact Nat.zero_le _
          · have hpo0 : e0.2 < e.2 := (glinAPoIff G anc hwf hok ke k e0 e h0 hk (by rw [hi0, hei])).1 hke
            have hcov : gfenceCovers G e0 r :=
              ⟨pr, pw, sr, sw, ⟨by rw [hi0, hri], by omega, e.2, hpo0, hpoe,
                by rw [show e0.1 = r.1 by rw [hi0, hri]]; exact hel⟩,
                Or.inl ⟨hR0, ha.1⟩, Or.inl ⟨hrR, ha.2⟩⟩
            have hmo : gmoLt G e0 r := h6 _ _ (Or.inr (Or.inr (Or.inr (Or.inl hcov))))
            exact Nat.le_trans hle (tvnScaMono G e0 r hmo)
        cases hd : (pw && sr) <;> cases ha : (pr && sr) <;>
          simp only [ite_true, ite_false, Bool.false_eq_true] <;>
          first
          | omega
          | (have := hpub hd; omega)
          | (have := hrv ha; omega)
          | (have := hpub hd; have := hrv ha; omega)
      | LRmw aq rl base ts rvs wvs cl =>
        have hwE : gisW G e = true := by simp only [gisW, hl]; rfl
        have hgw := RvwmoXv6ScaT.gwixLin G anc hwf hok k e hk hwE
        refine ⟨?_, ?_, ?_⟩
        · show RvwmoXv6ScaT.tvOk G anc i (k + 1)
            (if true && aq then au.length + 1 else (if aq then au.length else sh.tv))
          cases haq : aq
          · simp only [Bool.and_false, ite_false, Bool.false_eq_true]
            exact RvwmoXv6ScaT.tvOkStep G anc i k _ hT
          · simp only [Bool.and_self, ite_true]
            intro r kr hkr hr hri hrR
            have hpo : e.2 < r.2 :=
              (glinAPoIff G anc hwf hok k kr e r hk hr (by rw [hei, hri])).1 (by omega)
            have hacq : gacqPo G e r :=
              ⟨⟨by rw [hei, hri], hpo, glinALookupLbl G anc hwf hok k e hk, glinALookupLbl G anc hwf hok kr r hr⟩,
                ⟨_, hl, rfl⟩, ⟨_, hl, by rw [haq]; rfl⟩, WeakRvwmoGraph.glblIsRGmem G r hrR⟩
            have hmo : gmoLt G e r := h6 _ _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hacq)))))
            have hem := gisWGwrites G e hwf (glinALookupLbl G anc hwf hok k e hk) hwE
            have := (gwixLeTvnSca G r e hwf hem).2 hmo
            omega
        · show RvwmoXv6ScaT.rvOk G anc i (k + 1) au.length
          rw [hlen]
          exact Or.inr ⟨e, k, Nat.lt_succ_self _, hk, hei, ⟨_, hl, rfl⟩,
            RvwmoXv6ScaT.linNwLeTvnSca G anc hwf hok k e hk hwE⟩
        · show RvwmoXv6ScaT.cohOk G anc i (k + 1) (cohSrc.store sh.coh base wvs.length)
          intro a
          rcases RvwmoXv6ScaT.cohSrcStoreCases sh.coh base wvs.length a with h0 | ⟨hf, heq⟩
          · exact Or.inl h0
          · rw [heq]
            rcases hC a with h0 | hw
            · exact Or.inl h0
            · exact Or.inr (RvwmoXv6ScaT.cohWitStep G anc i k e a _ hk
                (fun _ v' hwb => RvwmoXv6ScaT.writesFoot G e _ base wvs a v' hl rfl hwb hf) hw)
      | LIo kind base vs =>
        have hno : ∀ a v', ¬ gwritesByte G e a v' :=
          fun a v' => RvwmoXv6ScaT.noWrite G e _ a v' hl rfl
        exact ⟨RvwmoXv6ScaT.tvOkStep G anc i k _ hT, RvwmoXv6ScaT.rvOkStep G anc i k _ hR,
          RvwmoXv6ScaT.cohOkStep G anc i k e _ hk (fun _ => hno) hC⟩
    · rw [if_neg hei]
      exact ⟨RvwmoXv6ScaT.tvOkStep G anc i k _ hT, RvwmoXv6ScaT.rvOkStep G anc i k _ hR,
        RvwmoXv6ScaT.cohOkStep G anc i k e _ hk (fun h => absurd h hei) hC⟩

end inv

/-! ## (5) THE THEOREM -/

/-- **W11 (iv)b, on any admissible anchor class (W13 (L))**: on the anchored linearization of a
graph satisfying riscv.cat's program-order arms and load value, with anchor-14 (`ancOk`), every
plain load is single-copy atomic at a view at or above the TsoMem shadow's floor under the merged
stamp `cohSrc` (G2-Q (a′), both components). -/
theorem linCandScaTA (G : Gexec) (anc : Geid → Bool) :
    gwf G → gppoCat6Gmo G → gloadValue G → ancOk G anc → candScaT cohSrc (linCandA G anc) := by
  intro hwf h6 hlv hok k s hs aq base ts vs hlb
  rw [candExTr] at hs
  have hkle : k ≤ (linCandA G anc).cdTr.length := by have := lookup_lt_Some hs; omega
  obtain ⟨e, he, rfl⟩ := linTrALookupInv G anc k s hs
  have hl : gxLbl G e = some (LLoad aq base ts vs) := by
    rw [linALbl G anc hwf hok k e he]
    exact congrArg some hlb
  have hkl : k ≤ (glinEidsA G anc).length := by rw [← linTrALen]; exact hkle
  show scaOkT (shadowOf cohSrc ((linCandA G anc).cdTr.take k) e.1)
    (eimg (candExec (linCandA G anc)) k) (elog (candExec (linCandA G anc)) k) e.1 base ts
  rw [candEimg _ k hkle, candElog _ k hkle]
  have htr : (linCandA G anc).cdTr.take k = ((glinEidsA G anc).take k).map (glinStep G) := by
    show ((glinEidsA G anc).map (glinStep G)).take k = _
    rw [fmap_take]
  rw [htr]
  obtain ⟨hT, _, hC⟩ := RvwmoXv6ScaT.shInv G anc hwf h6 hlv hok e.1 k hkl
  refine ⟨tvnSca G e, linTvnScaLeA G anc hwf hok k e he, ?_, ?_⟩
  · exact RvwmoXv6ScaT.loadFloor G anc hwf h6 hlv hok e.1 k _ e aq base ts vs he rfl hl hT hC
  · exact RvwmoXv6ScaT.linScaBytes G anc hwf hlv hok k e aq base ts vs he hl

/-- **W11 (iv)b**: on the linearization of a graph satisfying riscv.cat's program-order arms,
load value and rule 14 — the write-anchored instance of `linCandScaTA` (statement unchanged). -/
theorem linCandScaT (G : Gexec) :
    gwf G → gppoCat6Gmo G → gloadValue G → grule14 G → candScaT cohSrc (linCand G) :=
  fun hwf h6 hlv h14 => linCandScaTA G (gisW G) hwf h6 hlv (ancOkW G h14)

/-- From the PUBLISHED model (`rvwmoCatConsistentT`, the tagged riscv.cat), on its graph. -/
theorem linCandScaTCatT (GT : GdexecT) :
    rvwmoCatConsistentT GT → grule14 GT.gtG → candScaT cohSrc (linCand GT.gtG) := by
  intro h h14
  obtain ⟨hwf, h6, hlv, _⟩ := catTForgetAxioms GT h
  exact linCandScaT GT.gtG hwf h6 hlv h14

/-- From RVWMO⁻ (the output of today's `normalizeOfAcyclic`). -/
theorem linCandScaTMinus (G : Gexec) :
    rvwmoMinusConsistent G → grule14 G → candScaT cohSrc (linCand G) := by
  rintro ⟨hwf, hppo, hlv, _⟩ h14
  exact linCandScaT G hwf (fun e1 e2 h => hppo _ _ (gppoCat6Gppo G e1 e2 hlv h)) hlv h14

/-- From RVWMO⁻, on an admissible anchor class (W13 (L): the anchored trace W11 (v) consumes). -/
theorem linCandScaTMinusA (G : Gexec) (anc : Geid → Bool) :
    rvwmoMinusConsistent G → ancOk G anc → candScaT cohSrc (linCandA G anc) := by
  rintro ⟨hwf, hppo, hlv, _⟩ hok
  exact linCandScaTA G anc hwf (fun e1 e2 h => hppo _ _ (gppoCat6Gppo G e1 e2 hlv h)) hlv hok

/-! ## (6) W11 (iv)c — `linCandDiskLat`: disk-row loads read the LATEST write -/

/-- Lean-only: a byte read at the TOP view (`tvn = |log|`) is the latest write to it. -/
theorem RvwmoXv6ScaT.latestOfScaByte (img : Image) (log : List Wmsg) (i : Nat) (a : Int) (t : Nat) :
    scaByte img log i log.length a t → latest img log a t := by
  rintro ⟨hs, _, hno⟩
  refine ⟨hs, fun hw => ?_⟩
  obtain ⟨t', hlt, hle, hs'⟩ := (writesInLogByte img log a t log.length).1 hw
  exact hno t' hlt hs' (Or.inl hle)

/-- **W11 (iv)c, per load**: on the anchored linearization, a load that is an ANCHOR reads, at
its trace position, the latest write to each of its bytes — the prefix log holds exactly the
writes gmo-before it (`linNwAAnc`), so the SCA witness `tvnSca G r` is the TOP of that log, and
load value's co-maximality (`RvwmoXv6ScaT.linScaBytes`) leaves no later same-byte write in it. -/
theorem linAncLoadLatestA (G : Gexec) (anc : Geid → Bool) (hwf : gwf G) (hlv : gloadValue G)
    (hok : ancOk G anc) (k : Nat) (r : Geid) (aq : Bool) (base : Int) (ts : List Nat)
    (vs : List (BitVec 8)) :
    (glinEidsA G anc)[k]? = some r → gxLbl G r = some (LLoad aq base ts vs) → anc r = true →
    ∀ (j t : Nat), ts[j]? = some t →
      latest G.gxImg (cdLog (linCandA G anc) k) (accAddr base j) t := by
  intro hk hl hr j t hj
  have hsb := RvwmoXv6ScaT.linScaBytes G anc hwf hlv hok k r aq base ts vs hk hl j t hj
  have htop : tvnSca G r = (cdLog (linCandA G anc) k).length := by
    rw [linALogLen]; exact (linNwAAnc G anc hwf hok k r hk hr).symm
  rw [htop] at hsb
  exact RvwmoXv6ScaT.latestOfScaByte _ _ _ _ _ hsb

/-- **W11 (iv)c, on any admissible anchor class containing the disk-row reads**: every load of
the disk row (agent `NCPU`) of the anchored linearization reads the latest write per byte —
`candDiskLat` (G3-Q RULED (a″) [OWN.17]) is a THEOREM there, from `gwf`, load value and
anchor-14 (`ancOk`), with no further premise. -/
theorem linCandDiskLatA (G : Gexec) (anc : Geid → Bool) :
    gwf G → gloadValue G → ancOk G anc →
    (∀ e, gisR G e = true → e.1 = NCPU → anc e = true) →
    candDiskLat (linCandA G anc) := by
  intro hwf hlv hok hdisk k s hs aq base ts vs hlb hag
  rw [candExTr] at hs
  have hkle : k ≤ (linCandA G anc).cdTr.length := by have := lookup_lt_Some hs; omega
  obtain ⟨e, he, rfl⟩ := linTrALookupInv G anc k s hs
  have hl : gxLbl G e = some (LLoad aq base ts vs) := by
    rw [linALbl G anc hwf hok k e he]
    exact congrArg some hlb
  have hr : gisR G e = true := by unfold gisR; rw [hl]; rfl
  show ∀ (j t : Nat), ts[j]? = some t →
    latest (eimg (candExec (linCandA G anc)) k) (elog (candExec (linCandA G anc)) k)
      (accAddr base j) t
  rw [candEimg _ k hkle, candElog _ k hkle]
  exact linAncLoadLatestA G anc hwf hlv hok k e aq base ts vs he hl (hdisk e hr hag)

/-- **W11 (iv)c `linCandDiskLat`** (plan §C W11 (iv)c, §B(10) `candDiskLat`): on the (L) trace
`linCandIO` — whose anchors include the disk-row reads (`gisAnc`) — every disk-row load reads the
latest write per byte, from rule 14, the residue (`ioResidueGmo`) and the disk-read anchor premise
`gdiskRead14` (the three inputs of `ancOkIO`) plus `gwf` and load value. -/
theorem linCandDiskLat (GF : Gfexec) :
    gwf GF.gfGd.gdG → gloadValue GF.gfGd.gdG → grule14 GF.gfGd.gdG → ioResidueGmo GF →
    gdiskRead14 GF.gfGd.gdG → candDiskLat (linCandIO GF.gfGd.gdG) := by
  intro hwf hlv h14 hres hdr
  refine linCandDiskLatA _ _ hwf hlv (ancOkIO GF h14 hres hdr) ?_
  intro e hr hn
  unfold gisAnc
  simp [hr, hn]

/-- From RVWMO⁻ (the output of today's `normalizeOfAcyclic`), on the (L) trace. -/
theorem linCandDiskLatMinus (GF : Gfexec) :
    rvwmoMinusConsistent GF.gfGd.gdG → grule14 GF.gfGd.gdG → ioResidueGmo GF →
    gdiskRead14 GF.gfGd.gdG → candDiskLat (linCandIO GF.gfGd.gdG) :=
  fun hc h14 hres hdr => linCandDiskLat GF hc.1 hc.2.2.1 h14 hres hdr

end Weak
