/-
Weak: **Phase 1b, part 1 of the spinlock plan -- the REQUIRED (1)–(3) rule ingredients of the
Phase-1a review and the lk->cpu PURE layer.**  (Files: this one; `AxSpinProt6` the 1b instance and
its rule lemmas; `AxSpinProt7` hand programs/runs/WPds; `AxSpinProt8` the capstone.)

Rocq: `iris/AxSpinProt5.v` @ xxvzwolszwmp.

## The Rocq header, in substance

  §1 ppo admissions of lob-predecessor draws: `ppo1Gob`/`locLobp` (rule 1), `relClaimLobp`
     (REQUIRED (2): a release `sw lk` po-before a claim RMW on `lk` is in `splLobp`, rule 1),
     `acqLobp` (REQUIRED (3): the claiming `.aq` RMW is in `splLobp` of every po-later memory
     event, rule 5), `fenceLobp`.
  §2 lk->cpu: `wval`/`cpuOk` (Φ_cpu at one write: value 0 or `cv w.1`), `CPUOK` (the σ
     conjunct), `clAligned`, `rdFact` (the RACY READ fact, per byte: image / EXTERNAL source
     with Φ_cpu / SAME-HART visible source); `clSingleSource` -- THE n-BYTE SINGLE-SOURCE LEMMA
     (under aligned full-width writes every byte of the range is read at the same write index;
     load-value co-maximality only); `clAlignedOfSd` (its premise from the label shape);
     `cpuReadNotMine` -- D4's acquire-panic consumer: the value a reader reads from lk->cpu is
     not its own `cv`.
  §3 `lkBodyReadHeld`/`lkInvReadHeld`: the holder's plain read of the lock byte yields `v ≠ b0`
     IN-STEP from HELD_NZ (`holdOk`) + the handout (`WPh`); the σ conjunct `NZ` is not consulted.
  §4 `Rb a e`/`RL Cl e`: VALUE-GENERIC owned bytes (per-byte full history auth tied at `e`);
     `RLTransportable`, `RLGenesis`, `RLWrite` (n-byte owned write: every byte's history
     appended, the Own deposit enters `ownInv X`), `RbReadPlace` (owned PLACEMENT read: the rf
     source is the image, or the anchor, or gmo-before the anchor).
  §5 REQUIRED (1) at the 1a instance (`AxSpinProt2.spinOb`): `feRelease'` -- each component
     `R_j` of `R` from `flowIn` at ITS OWN anchor; `feReleaseOf'` -- the 1a single-anchor
     `feRelease` as its corollary (`Rs = [R]`).

## Deviations from Rocq

1. VOCABULARY (as `AxSpinProt`): `Z` ↦ `Int`, `agent` ↦ `Agent`, `bv 8` ↦ `BitVec 8`,
   `gset geid` ↦ `GSet Geid`, `{[e]} ∪ s` ↦ `({e} : GSet Geid) ∪ s`, `gd_g GD` ↦ `GD.gdG`,
   `gx_img G a` ↦ `G.gxImg a`, `l !! j` ↦ `l[j]?`, `last l` ↦ `l.getLast?`, `H.*1` ↦
   `H.map Prod.fst`, `B0` ↦ `b0`, `Forall P l` ↦ `∀ p, p ∈ l → P p`, `i ↪[γh] v` ↦
   `ghost_map_elem γh (DFrac.own 1) i v`.  `cl_range`'s `seq 0 n` ↦ `List.range n`.
2. CONTEXTS: Rocq section variables are explicit leading arguments in Rocq's order, only where
   Rocq's section mechanism includes them (§1 `GD [Hcons]`; §2 `Cl [cv]`; §3 `lk` / `reg lk`;
   §4 `γ GD`; §5 `lk x GT nm Hcons`).  `invGS_gen HasNoLc Σ` ↦ `[InvGS_gen hlc GF]` for any
   `hlc`; the local instances `spo_pol`/`spo_G` are `splPol GT`/`splG lk x GT nm`, passed
   explicitly.  `transportComps` drops Rocq's unused `axlogG Σ hent` binder.
3. STATEMENT SHAPES (as `AxSpinProt`/`AxSpinProt2`): §3/§4 `P -∗ Q -∗ R` ↦ `P ∗ Q ⊢ R`,
   `P -∗ Q ==∗ R` ↦ `P ∗ Q ⊢ |==> R`; §5 wand chains ↦ `⊢ A -∗ B -∗ …`; pure premises stay `→`.

**Rocq → Lean name map.**  `ppo1_gob` `ppo1Gob`, `loc_lobp` `locLobp`, `rel_claim_lobp`
`relClaimLobp`, `acq_lobp` `acqLobp`, `fence_lobp` `fenceLobp`, `wval` `wval`, `cpu_ok`
`cpuOk`, `CPU_OK` `CPUOK`, `cl_aligned` `clAligned`, `rd_fact` `rdFact`, `cpu_ok_nw`
`cpuOkNw`, `CPU_OK_insert` `CPUOKInsert`, `cl_single_source` `clSingleSource`,
`cpu_read_not_mine` `cpuReadNotMine`, `cl_range` `clRange`, `cl_aligned_of_sd`
`clAlignedOfSd`, `lk_body_read_held` `lkBodyReadHeld`, `lk_inv_read_held` `lkInvReadHeld`,
`hwfa` `hwfa`, `Rb` `Rb`, `RL` `RL`, `hwfa_nil` `hwfaNil`, `Rb_transportable`
`RbTransportable`, `RL_transportable` `RLTransportable`, `RL_genesis` `RLGenesis`, `Rb_step`
`RbStep`, `RL_write` `RLWrite`, `Rb_read_place` `RbReadPlace`, `transport_comps`
`transportComps`, `fe_release'` `feRelease'`, `fe_release_of'` `feReleaseOf'`.
Lean-only (file-qualified): `AxSpinProt5.rlSnaps` (`RL_write`'s inner `big_sepL_bupd` step, by
list induction), `AxSpinProt5.covMoX`/`covRfeX` (`AxSpinProt.covMo`/`covRfe` at any owned set
`X ∋ a`).

**Dropped:** none (31 Rocq decls; 34 Lean = 31 + 3 Lean-only).
-/
import Weak.AxSpinProt3

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std Iris.Std.PartialMap MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D

/-! # 1. Pure graph lemmas: ppo admissions of the lob-predecessor draws -/

section ppo
variable (GD : Gdexec)

/-- RULE 1 (`[M];po-loc;[W]`) as one `gobCat` step. -/
theorem ppo1Gob (e1 e2 : Geid) (a : Int) (v : BitVec 8) :
    WeakRvwmoGraph.gpo GD.gdG e1 e2 → gaccesses GD.gdG e1 a → gwritesByte GD.gdG e2 a v →
    gobCat GD e1 e2 := by
  intro Hpo Ha Hw
  exact gobCatStep _ _ _ (.inl (.inl (.inl ⟨Hpo, a, Ha, v, Hw⟩)))

/-- A po-earlier same-address access of a later WRITE is a lob-predecessor (`splLobp`) by
rule 1. -/
theorem locLobp (Hcons : rvwmoCatConsistent GD) (e1 e2 : Geid) (l1 : Lbl) (a : Int)
    (v : BitVec 8) :
    gxLbl GD.gdG e1 = some l1 → lbIsMem l1 = true → WeakRvwmoGraph.gpo GD.gdG e1 e2 →
    gaccesses GD.gdG e1 a → gwritesByte GD.gdG e2 a v → e1 ∈ splLobp GD e2 := by
  intro Hl Hm Hpo Ha Hw
  exact lobpIntro GD _ _ _ Hl Hm Hpo (gobGmo GD Hcons _ _ (ppo1Gob GD e1 e2 a v Hpo Ha Hw))

/-- REQUIRED (2)'s admissibility: a release store `w` (writes `b0` at `lk`) po-before a CLAIM
`c` is in `lobp c` -- ppo rule 1. -/
theorem relClaimLobp (Hcons : rvwmoCatConsistent GD) (lk : Int) (w c : Geid)
    (oz : Option Geid) (l : Lbl) :
    gxLbl GD.gdG w = some l → lbIsMem l = true → zw lk GD.gdG w →
    WeakRvwmoGraph.gpo GD.gdG w c → lkClaim lk GD.gdG c oz → w ∈ splLobp GD c := by
  rintro Hl Hm Hz Hpo ⟨t, -, -, Hw⟩
  exact locLobp GD Hcons w c l lk b1 Hl Hm Hpo (.inl ⟨b0, Hz⟩) Hw

/-- REQUIRED (3)'s admissibility: the claiming `.aq` RMW is in `lobp` of every po-later memory
event -- ppo rule 5. -/
theorem acqLobp (Hcons : rvwmoCatConsistent GD) (i : Agent) (k1 k2 : Nat) (base : Int)
    (ts : List Nat) (rvs wvs : List (BitVec 8)) (cls : WmClass) (l2 : Lbl) :
    gxLbl GD.gdG (i, k1) = some (.LRmw true false base ts rvs wvs cls) →
    gxLbl GD.gdG (i, k2) = some l2 → lbIsMem l2 = true → k1 < k2 →
    (i, k1) ∈ splLobp GD (i, k2) := by
  intro H1 H2 Hm Hlt
  exact lobpIntro GD _ _ _ H1 rfl (gpoRow GD i k1 k2 _ _ H1 H2 Hlt)
    (gobGmo GD Hcons _ _ (acqGob GD i k1 k2 base ts rvs wvs cls l2 H1 H2 Hm Hlt))

/-- `fence rw,w`: every po-earlier memory event is a lob-predecessor of a po-later store. -/
theorem fenceLobp (Hcons : rvwmoCatConsistent GD) (i : Agent) (k1 kf k2 : Nat) (l1 : Lbl)
    (base : Int) (vs : List (BitVec 8)) (cls : WmClass) :
    gxLbl GD.gdG (i, k1) = some l1 → lbIsMem l1 = true →
    gxLbl GD.gdG (i, kf) = some (.LFence true true false true) →
    gxLbl GD.gdG (i, k2) = some (.LStore false base vs cls) →
    k1 < kf → kf < k2 → (i, k1) ∈ splLobp GD (i, k2) := by
  intro H1 Hm Hf H2 Hl1 Hl2
  exact lobpIntro GD _ _ _ H1 Hm (gpoRow GD i k1 k2 _ _ H1 H2 (by omega))
    (gobGmo GD Hcons _ _ (fenceGob GD i k1 kf k2 l1 base vs cls H1 Hm Hf H2 Hl1 Hl2))

end ppo

/-! # 2. lk->cpu: pure vocabulary, the n-byte SINGLE-SOURCE lemma, the racy-read fact and its
consumer (D4's acquire-panic refutation) -/

section cpuPure
variable (Cl : List Int) (cv : Agent → List (BitVec 8))

/-- `w`'s bytes in `Cl` are those of `vs` (index-wise). -/
def wval (G : Gexec) (w : Geid) (vs : List (BitVec 8)) : Prop :=
  ∀ (j : Nat) a v, Cl[j]? = some a → gwritesByte G w a v → vs[j]? = some v

/-- Φ_cpu at one write: value 0 or the writer's own cpu pointer. -/
def cpuOk (G : Gexec) (w : Geid) : Prop :=
  wval Cl G w (List.replicate Cl.length b0) ∨ wval Cl G w (cv w.1)

/-- The σ conjunct: every processed event satisfies Φ_cpu. -/
def CPUOK (G : Gexec) (s : GSet Geid) : Prop := ∀ w, w ∈ s → cpuOk Cl cv G w

/-- All lk->cpu writes are ALIGNED full-width: a write touching one byte of `Cl` touches all. -/
def clAligned (G : Gexec) : Prop :=
  ∀ w a v, a ∈ Cl → gwritesByte G w a v → ∀ a', a' ∈ Cl → ∃ v', gwritesByte G w a' v'

/-- THE RACY READ FACT deposited at a read `r` of lk->cpu (per byte): genesis (image), or the
source `w` is EXTERNAL (Φ_cpu holds) or SAME-HART and visible. -/
def rdFact (G : Gexec) (r : Geid) : Prop :=
  ∀ a t v, a ∈ Cl → greadsByte G r a t v →
    (t = 0 ∧ G.gxImg a = some v) ∨
    ∃ w, gwriteAt G t = some w ∧ gwritesByte G w a v ∧
      ((w.1 ≠ r.1 ∧ cpuOk Cl cv G w) ∨ (w.1 = r.1 ∧ gvisible G w r))

theorem cpuOkNw (G : Gexec) (w : Geid) :
    (∀ a v, a ∈ Cl → ¬ gwritesByte G w a v) → cpuOk Cl cv G w := by
  intro Hn
  left
  intro j a v Hj Hw
  exact absurd Hw (Hn a v (List.mem_of_getElem? Hj))

theorem CPUOKInsert (G : Gexec) (s : GSet Geid) (e : Geid) :
    CPUOK Cl cv G s → cpuOk Cl cv G e → CPUOK Cl cv G (({e} : GSet Geid) ∪ s) := by
  intro H He w Hw
  rcases elemOfUnion.1 Hw with h | h
  · rw [elemOfSingleton.1 h]
    exact He
  · exact H w h

/-- THE SINGLE-SOURCE LEMMA: under aligned full-width writes, every byte of `Cl` a read touches
is read at the SAME write index. -/
theorem clSingleSource (G : Gexec) (r : Geid) (a a' : Int) (t t' : Nat) (v v' : BitVec 8) :
    gwf G → gloadValue G → clAligned Cl G → a ∈ Cl → a' ∈ Cl →
    greadsByte G r a t v → greadsByte G r a' t' v' → t = t' := by
  intro Hwf Hlv Hal Ha Ha' Hr Hr'
  have Hnd := Hwf.1
  have Hm := (Hlv r a t v Hr).2
  have Hm' := (Hlv r a' t' v' Hr').2
  cases t with
  | zero =>
    cases t' with
    | zero => rfl
    | succ j' =>
      obtain ⟨w', Hat', Hw', Hvis'⟩ := (Hlv r a' (j' + 1) v' Hr').1
      obtain ⟨v0, Hw0⟩ := Hal w' a' v' Ha' Hw' a Ha
      have Hle := Hm w' v0 Hw0 Hvis'
      have Hin := (gwriteAtInv G (j' + 1) w' Hnd Hat').1
      have Hp := WeakRvwmoGraph.gwixPos G w' Hin
      omega
  | succ j =>
    obtain ⟨w, Hat, Hw, Hvis⟩ := (Hlv r a (j + 1) v Hr).1
    obtain ⟨v0, Hw0⟩ := Hal w a v Ha Hw a' Ha'
    have H1 := Hm' w v0 Hw0 Hvis
    have Hix := (gwriteAtInv G (j + 1) w Hnd Hat).2
    cases t' with
    | zero =>
      have Hin := (gwriteAtInv G (j + 1) w Hnd Hat).1
      have Hp := WeakRvwmoGraph.gwixPos G w Hin
      omega
    | succ j' =>
      obtain ⟨w', Hat', Hw', Hvis'⟩ := (Hlv r a' (j' + 1) v' Hr').1
      obtain ⟨v1, Hw1⟩ := Hal w' a' v' Ha' Hw' a Ha
      have H2 := Hm w' v1 Hw1 Hvis'
      have Hix' := (gwriteAtInv G (j' + 1) w' Hnd Hat').2
      omega

/-- THE CONSUMER (D4, acquire's `if(holding(lk)) panic` for a non-holder `r.1`): the full
`Cl`-value `vs` read by `r` is NOT `r.1`'s own cpu pointer. -/
theorem cpuReadNotMine (G : Gexec) (r : Geid) (vs : List (BitVec 8)) :
    gwf G → gloadValue G → (∀ e1 e2, gppo1 G e1 e2 → gmoLt G e1 e2) → clAligned Cl G →
    (∀ k, (cv k).length = Cl.length) →
    vs.length = Cl.length →
    (∀ (j : Nat) a, Cl[j]? = some a → ∃ t v, greadsByte G r a t v ∧ vs[j]? = some v) →
    (∀ a, a ∈ Cl → G.gxImg a = some b0) →
    cv r.1 ≠ List.replicate Cl.length b0 →
    (∀ k, k ≠ r.1 → cv k ≠ cv r.1) →
    (∀ w a v, a ∈ Cl → gwritesByte G w a v → WeakRvwmoGraph.gpo G w r → False) →
    rdFact Cl cv G r → vs ≠ cv r.1 := by
  intro Hwf Hlv Hppo1 Hal Hcvl Hlen Hrd Himg Hnz Hinj Hnself Hrf
  cases H0 : Cl[0]? with
  | none =>
    have Hl0 : Cl.length = 0 := by
      have := List.getElem?_eq_none_iff.1 H0
      omega
    have Hvs : vs = [] := List.eq_nil_of_length_eq_zero (by omega)
    intro Heq
    apply Hnz
    rw [← Heq, Hvs, Hl0]
    rfl
  | some a0 =>
    obtain ⟨t0, v0, Hr0, -⟩ := Hrd 0 a0 H0
    have Ha0 : a0 ∈ Cl := List.mem_of_getElem? H0
    have Hall : ∀ (j : Nat) a, Cl[j]? = some a → ∃ v, greadsByte G r a t0 v ∧ vs[j]? = some v := by
      intro j a Hj
      obtain ⟨t, v, Hr, Hv⟩ := Hrd j a Hj
      have Ha : a ∈ Cl := List.mem_of_getElem? Hj
      have Ht := clSingleSource Cl G r a a0 t t0 v v0 Hwf Hlv Hal Ha Ha0 Hr Hr0
      subst Ht
      exact ⟨v, Hr, Hv⟩
    have Hval : ∀ tgt : List (BitVec 8), tgt.length = Cl.length →
        (∀ (j : Nat) a v, Cl[j]? = some a → greadsByte G r a t0 v → tgt[j]? = some v) → vs = tgt := by
      intro tgt Hlt Hj
      apply List.ext_getElem?
      intro j
      cases Hja : Cl[j]? with
      | some a =>
        obtain ⟨v, Hr, Hv⟩ := Hall j a Hja
        rw [Hv]
        exact (Hj j a v Hja Hr).symm
      | none =>
        have := List.getElem?_eq_none_iff.1 Hja
        rw [List.getElem?_eq_none_iff.2 (by omega), List.getElem?_eq_none_iff.2 (by omega)]
    cases t0 with
    | zero =>
      have Hz : vs = List.replicate Cl.length b0 := by
        apply Hval _ List.length_replicate
        intro j a v Hj Hr
        have Hi := (Hlv r a 0 v Hr).1
        have Ha : a ∈ Cl := List.mem_of_getElem? Hj
        simp only at Hi
        rw [Himg a Ha, Option.some.injEq] at Hi
        subst Hi
        rw [List.getElem?_replicate, if_pos (List.getElem?_eq_some_iff.1 Hj).1]
      intro Heq
      apply Hnz
      rw [← Heq, Hz]
    | succ j0 =>
      rcases Hrf a0 (j0 + 1) v0 Ha0 Hr0 with ⟨Ht, -⟩ | ⟨w, Hat, Hw0, Hcase⟩
      · cases Ht
      rcases Hcase with ⟨Hext, Hok⟩ | ⟨Hsame, Hvis⟩
      · have Hsrc : ∀ (j : Nat) a v, Cl[j]? = some a → greadsByte G r a (j0 + 1) v →
            gwritesByte G w a v := by
          intro j a v _ Hr
          obtain ⟨w', Hat', Hw', -⟩ := (Hlv r a (j0 + 1) v Hr).1
          rw [Hat] at Hat'
          cases Hat'
          exact Hw'
        rcases Hok with Hz | Hc
        · have Hz' : vs = List.replicate Cl.length b0 :=
            Hval _ List.length_replicate fun j a v Hj Hr => Hz j a v Hj (Hsrc j a v Hj Hr)
          intro Heq
          apply Hnz
          rw [← Heq, Hz']
        · have Hc' : vs = cv w.1 :=
            Hval _ (Hcvl _) fun j a v Hj Hr => Hc j a v Hj (Hsrc j a v Hj Hr)
          rw [Hc']
          exact Hinj _ Hext
      · exfalso
        have Hlw : (gxLbl G w).isSome := by
          obtain ⟨l, _, _, _, Hl, _⟩ := Hw0
          rw [Hl]
          rfl
        have Hlr : (gxLbl G r).isSome := by
          obtain ⟨l, _, _, _, _, Hl, _⟩ := Hr0
          rw [Hl]
          rfl
        rcases Hvis with Hlt | Hpo
        · by_cases Hwr : w.2 < r.2
          · exact Hnself w a0 v0 Ha0 Hw0 ⟨Hsame, Hwr, Hlw, Hlr⟩
          · by_cases Heq : w.2 = r.2
            · have : w = r := Prod.ext Hsame Heq
              subst this
              exact gmoLtIrrefl G w Hlt
            · have Hrw : gmoLt G r w :=
                Hppo1 r w ⟨⟨Hsame.symm, by omega, Hlr, Hlw⟩, a0, .inr ⟨j0 + 1, v0, Hr0⟩, v0, Hw0⟩
              exact gmoLtIrrefl G w (gmoLtTrans G w r w Hlt Hrw)
        · exact Hnself w a0 v0 Ha0 Hw0 Hpo

end cpuPure

/-- lk->cpu's byte range. -/
def clRange (lkc : Int) (n : Nat) : List Int := (List.range n).map (fun j : Nat => lkc + (j : Int))

/-- `clAligned` from the LABEL shape: every write touching the range is a full-width write based
at `lkc` (xv6's `sd`). -/
theorem clAlignedOfSd (G : Gexec) (lkc : Int) (n : Nat) :
    (∀ w a v, a ∈ clRange lkc n → gwritesByte G w a v →
      ∃ l vs, gxLbl G w = some l ∧ lbWr l = some (lkc, vs) ∧ vs.length = n) →
    clAligned (clRange lkc n) G := by
  intro Hsd w a v Ha Hw a' Ha'
  obtain ⟨l, vs, Hl, Hwr, Hlen⟩ := Hsd w a v Ha Hw
  obtain ⟨j, Hj, rfl⟩ := List.mem_map.1 Ha'
  have Hjn : j < vs.length := by
    rw [Hlen]
    exact List.mem_range.1 Hj
  exact ⟨vs[j], l, lkc, vs, j, Hl, Hwr, List.getElem?_eq_getElem Hjn, rfl⟩

/-! # 3. REQUIRED (3) at the lock component: the HOLDER's plain read of the lock byte, the
`≠ b0` fact derived IN-STEP from HELD_NZ (`holdOk`) + the handout (`WPh`). -/

section held
variable {GF : BundledGFunctors} [SpinlockG GF]

theorem lkBodyReadHeld (lk : Int) (γh : GName) (R : Geid → IProp GF) (GD : Gdexec)
    (s : GSet Geid) (r : Geid) (i : Nat) (c : Geid) :
    rvwmoCatConsistent GD → WPh GD.gdG s r → r ∉ s → gisW GD.gdG r = false →
    WeakRvwmoGraph.gpo GD.gdG c r → nolk lk GD.gdG c r →
    lkBody lk γh R GD s ∗ ghost_map_elem γh (DFrac.own 1) i (some c) ⊢
    lkBody lk γh R GD (({r} : GSet Geid) ∪ s) ∗ ghost_map_elem γh (DFrac.own 1) i (some c) ∗
    ⌜∀ t v, greadsByte GD.gdG r lk t v → v ≠ b0⌝ := by
  intro Hcons Hwp Hn Hnw Hpo Hnl
  have Hrd := lkBodyRead lk γh R GD s r Hcons Hwp Hn Hnw
  unfold lkBody at Hrd ⊢
  iintro ⟨⟨Hg, Hm, %st, %m, Ha, %hp⟩, Hi⟩
  obtain ⟨hh, hnz, hl⟩ := hp
  icombine Ha Hi gives %hmi
  obtain ⟨rfl, -⟩ := AxSpinProt.stForSome st i c (hl.1 i (some c) hmi)
  isplitl [Hg Hm Ha]
  · iapply Hrd
    isplitl [Hg]
    · iexact Hg
    isplitl [Hm]
    · iexact Hm
    · iexists (some c)
      iexists m
      isplitl [Ha]
      · iexact Ha
      · ipureintro
        exact ⟨hh, hnz, hl⟩
  isplitl [Hi]
  · iexact Hi
  · ipureintro
    intro t v Hr
    exact nzRead lk GD Hcons s c r t v Hwp hh Hpo Hnl Hr

theorem lkInvReadHeld (reg : GName) (lk : Int) (GD : Gdexec) (s : GSet Geid) (r : Geid) (i : Nat)
    (c : Geid) :
    rvwmoCatConsistent GD → WPh GD.gdG s r → r ∉ s → gisW GD.gdG r = false →
    WeakRvwmoGraph.gpo GD.gdG c r → nolk lk GD.gdG c r →
    lkInv (GF := GF) reg lk GD s ∗ locked reg lk i c ⊢
    lkInv reg lk GD (({r} : GSet Geid) ∪ s) ∗ locked reg lk i c ∗
    ⌜∀ t v, greadsByte GD.gdG r lk t v → v ≠ b0⌝ := by
  intro Hcons Hwp Hn Hnw Hpo Hnl
  unfold lkInv locked
  iintro ⟨⟨%γR, %γh, %R, #Hr, #Hs, Hb⟩, ⟨%γR1, %γh1, #Hr1, Hi⟩⟩
  ihave %h1 := ghost_map_elem_agree reg lk _ _ ((γR, γh) : GName × GName) (γR1, γh1)
    $$ [$Hr $Hr1]
  simp only [Prod.mk.injEq] at h1
  obtain ⟨rfl, rfl⟩ := h1
  icases lkBodyReadHeld lk γh R GD s r i c Hcons Hwp Hn Hnw Hpo Hnl $$ [$Hb $Hi]
    with ⟨Hb, Hi, %H⟩
  isplitl [Hb]
  · iexists γR
    iexists γh
    iexists R
    isplitr [Hb]
    · iexact Hr
    isplitr [Hb]
    · iexact Hs
    · iexact Hb
  isplitl [Hi]
  · iexists γR
    iexists γh
    isplitr [Hi]
    · iexact Hr
    · iexact Hi
  · ipureintro
    exact H

end held

/-! # 4. Value-generic owned bytes: `Rb a e` (one byte, ANY values), `RL Cl e` (a list of
them); transport, genesis, the n-byte OWNED WRITE and the PLACEMENT read. -/

def hwfa (GD : Gdexec) (a : Int) (H : List Hent) : Prop :=
  (∀ p, p ∈ H → gwritesByte GD.gdG p.1 a p.2) ∧ chainWith (gmoLt GD.gdG) (H.map Prod.fst)

theorem hwfaNil (GD : Gdexec) (a : Int) : hwfa GD a [] :=
  ⟨fun _ hp => absurd hp List.not_mem_nil, fun _ _ _ hk => by simp at hk⟩

section rl
variable {GF : BundledGFunctors} [AxlogG GF Hent]

def Rb (γ : GName) (GD : Gdexec) (a : Int) (e : Geid) : IProp GF :=
  iprop(∃ H, histAuth γ a 1 H ∗
    ⌜(H = [] ∨ tieBase GD.gdG (H.map Prod.fst) e) ∧ hwfa GD a H⌝)

def RL (γ : GName) (GD : Gdexec) (Cl : List Int) (e : Geid) : IProp GF :=
  iprop([∗list] a ∈ Cl, Rb γ GD a e)

theorem RbTransportable (γ : GName) (GD : Gdexec) (a : Int) :
    rvwmoCatConsistent GD → lkTransportable GD (Rb (GF := GF) γ GD a) := by
  intro hcons e e' hob
  unfold Rb
  iintro ⟨%H, Ha, %hp⟩
  obtain ⟨ht, hw⟩ := hp
  iexists H
  isplitl [Ha]
  · iexact Ha
  · ipureintro
    refine ⟨?_, hw⟩
    rcases ht with h | h
    · exact Or.inl h
    · exact Or.inr (tieLob _ _ e e' h (obCatSubGmo GD e e' hcons hob))

theorem RLTransportable (γ : GName) (GD : Gdexec) (Cl : List Int) :
    rvwmoCatConsistent GD → lkTransportable GD (RL (GF := GF) γ GD Cl) := by
  intro hcons e e' hob
  unfold RL
  exact BigSepL.bigSepL_mono_of_forall fun {_ a} => RbTransportable γ GD a hcons e e' hob

theorem RLGenesis (γ : GName) (GD : Gdexec) (Cl : List Int) :
    ([∗list] a ∈ Cl, histAuth (GF := GF) γ a 1 []) ⊢ ∀ e, RL γ GD Cl e := by
  have h : ∀ e, ([∗list] a ∈ Cl, histAuth (GF := GF) γ a 1 []) ⊢ RL γ GD Cl e := by
    intro e
    unfold RL
    refine BigSepL.bigSepL_mono_of_forall fun {_ a} => ?_
    unfold Rb
    iintro Ha
    iexists ([] : List Hent)
    isplitl [Ha]
    · iexact Ha
    · ipureintro
      exact ⟨Or.inl rfl, hwfaNil GD a⟩
  iintro H %e
  iapply h e
  iexact H

theorem RbStep (γ : GName) (GD : Gdexec) (a : Int) (e w : Geid) (v : BitVec 8) :
    gmoLt GD.gdG e w → gwritesByte GD.gdG w a v →
    Rb (GF := GF) γ GD a e ⊢ |==> (Rb γ GD a w ∗
      ∃ H, histSnap γ a H ∗ ⌜H.getLast? = some (w, v)⌝) := by
  intro hew hw
  unfold Rb
  iintro ⟨%H, Ha, %hp⟩
  obtain ⟨ht, hwr, hch⟩ := hp
  imod histAppend γ a H (w, v) $$ Ha with Ha
  ihave #Hsn := histSnapGet γ a 1 (H ++ [(w, v)]) $$ Ha
  imodintro
  isplitl [Ha]
  · iexists (H ++ [(w, v)])
    isplitl [Ha]
    · iexact Ha
    · ipureintro
      refine ⟨Or.inr (tieWrite GD.gdG H w v), ?_, ?_⟩
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
  · iexists (H ++ [(w, v)])
    isplitl []
    · iexact Hsn
    · ipureintro
      simp

/-- (Lean-only) `RL_write`'s inner step: every byte of `L` steps to `w`, with one deposit
snapshot per written byte. -/
theorem AxSpinProt5.rlSnaps (γ : GName) (GD : Gdexec) (L : List Int) (e w : Geid) :
    gmoLt GD.gdG e w → (∀ a, a ∈ L → ∃ v, gwritesByte GD.gdG w a v) →
    ([∗list] a ∈ L, Rb (GF := GF) γ GD a e) ⊢ |==> (([∗list] a ∈ L, Rb γ GD a w) ∗
      ∀ a v, ⌜a ∈ L⌝ → ⌜gwritesByte GD.gdG w a v⌝ →
        ∃ H, histSnap γ a H ∗ ⌜H.getLast? = some (w, v)⌝) := by
  induction L with
  | nil =>
    intro _ _
    iintro -
    imodintro
    isplitl []
    · iapply BigSepL.bigSepL_nil.2
      iempintro
    · iintro %a %v %ha
      simp at ha
  | cons a L ih =>
    intro hew hall
    obtain ⟨v, hv⟩ := hall a List.mem_cons_self
    iintro H
    icases BigSepL.bigSepL_cons.1 $$ H with ⟨Ha, HL⟩
    imod RbStep γ GD a e w v hew hv $$ Ha with ⟨Ha, %H, #Hs, %hl⟩
    imod ih hew (fun a' h => hall a' (List.mem_cons_of_mem _ h)) $$ HL with ⟨HL, #HS⟩
    imodintro
    isplitl [Ha HL]
    · iapply BigSepL.bigSepL_cons.2
      isplitl [Ha]
      · iexact Ha
      · iexact HL
    · iintro %a' %v' %ha' %hw'
      rcases List.mem_cons.1 ha' with rfl | h
      · obtain rfl := gwritesByteDet _ _ _ _ _ hw' hv
        iexists H
        isplitl []
        · iexact Hs
        · ipureintro
          exact hl
      · ihave H2 := HS $$ %a' %v' %h %hw'
        iexact H2

/-- THE n-BYTE OWNED WRITE: `w` writes every byte of `Cl` (and nothing else), `e` gmo-before
`w`: every byte's history is appended, the component re-ties at `w`, and `w`'s Own deposit
enters `ownInv X`. -/
theorem RLWrite (γ : GName) (GD : Gdexec) (X : GSet Int) (Cl : List Int) (s : GSet Geid)
    (e w : Geid) :
    w ∉ s → gmoLt GD.gdG e w → (∀ a, a ∈ Cl → ∃ v, gwritesByte GD.gdG w a v) →
    (∀ a v, gwritesByte GD.gdG w a v → a ∈ Cl) →
    ownInv (GF := GF) X γ GD s ∗ RL γ GD Cl e ⊢ |==> (
      ownInv X γ GD (({w} : GSet Geid) ∪ s) ∗ RL γ GD Cl w) := by
  intro hn hew hall honly
  unfold RL ownInv
  iintro ⟨#Hinv, HR⟩
  imod AxSpinProt5.rlSnaps γ GD Cl e w hew hall $$ HR with ⟨HR, #HS⟩
  imodintro
  isplitr [HR]
  · iapply (AxSpinProt.bigSepSUnionSingleton hn).2
    isplitl []
    · unfold Φx
      iintro %a %v %_ %hw
      ihave H2 := HS $$ %a %v %(honly a v hw) %hw
      iexact H2
    · iexact Hinv
  · iexact HR

/-- (Lean-only) `AxSpinProt.covMo` at any owned set `X ∋ a`. -/
theorem AxSpinProt5.covMoX (γ : GName) (X : GSet Int) (a : Int) (GD : Gdexec) (s : GSet Geid)
    (r : Geid) :
    a ∈ X → WPh GD.gdG s r →
    ownInv (GF := GF) X γ GD s ⊢
      ∀ w v, ⌜gwritesByte GD.gdG w a v⌝ -∗ ⌜gmoLt GD.gdG w r⌝ -∗
        ∃ H', ⌜w ∈ H'.map Prod.fst⌝ ∗ histSnap γ a H' := by
  intro haX hwp
  iintro #Hinv %w %v %hw %hlt
  iapply ownInvCov X γ GD s a w v haX hw (hwp w (WeakRvwmoGraph.gwritesByteGisW _ _ _ _ hw) hlt)
  iexact Hinv

/-- (Lean-only) `AxSpinProt.covRfe` at any owned set `X ∋ a`. -/
theorem AxSpinProt5.covRfeX (γ : GName) (X : GSet Int) (a : Int) (GD : Gdexec) (s : GSet Geid)
    (r : Geid) :
    a ∈ X → rvwmoCatConsistent GD → WPh GD.gdG s r →
    ownInv (GF := GF) X γ GD s ⊢
      ∀ w v, ⌜gwritesByte GD.gdG w a v⌝ -∗ ⌜grfe GD.gdG w r⌝ -∗
        ∃ H', ⌜w ∈ H'.map Prod.fst⌝ ∗ histSnap γ a H' := by
  intro haX hcons hwp
  iintro #Hinv %w %v %hw %hrfe
  iapply ownInvCov X γ GD s a w v haX hw
    (hwp w (WeakRvwmoGraph.gwritesByteGisW _ _ _ _ hw) (catGrfeGmo GD w r hcons hrfe))
  iexact Hinv

/-- THE OWNED PLACEMENT READ of byte `a` under `Rb a e` (`e` gmo-before `r`, `r`'s hart never
writes `a`): `r` reads the image, or a write that is `e` itself or gmo-BEFORE `e`.
VALUE-INDEPENDENT; `Rb a e` is kept. -/
theorem RbReadPlace (γ : GName) (GD : Gdexec) (X : GSet Int) (a : Int) (s : GSet Geid)
    (e r : Geid) (t : Nat) (v : BitVec 8) :
    rvwmoCatConsistent GD → a ∈ X →
    (∀ w v', gwritesByte GD.gdG w a v' → w.1 = r.1 → False) →
    greadsByte GD.gdG r a t v → gmoLt GD.gdG e r → WPh GD.gdG s r →
    ownInv (GF := GF) X γ GD s ∗ Rb γ GD a e ⊢
      Rb γ GD a e ∗ ⌜t = 0 ∨ ∃ w, gwriteAt GD.gdG t = some w ∧ gwritesByte GD.gdG w a v ∧
                                 (w = e ∨ gmoLt GD.gdG w e)⌝ := by
  intro hcons haX hnpo hrd her hwp
  unfold Rb
  iintro ⟨#Hinv, %H, Ha, %hp⟩
  obtain ⟨ht, hw⟩ := hp
  rcases ht with rfl | ht
  · ihave Hcov := AxSpinProt5.covRfeX γ X a GD s r haX hcons hwp $$ Hinv
    icases (persistent_entails_left (lockReadOwnGenesis (GF := GF) GD γ a r t v hcons hnpo hrd))
      $$ [$Ha $Hcov] with ⟨⟨Ha, -⟩, %hg⟩
    isplitl [Ha]
    · iexists ([] : List Hent)
      isplitl [Ha]
      · iexact Ha
      · ipureintro
        exact ⟨Or.inl rfl, hwfaNil GD a⟩
    · ipureintro
      exact Or.inl hg.1
  · cases hlast : H.getLast? with
    | none =>
      exfalso
      rw [List.getLast?_eq_none_iff] at hlast
      subst hlast
      rcases ht with h | ⟨_, h, _⟩ <;> simp at h
    | some p =>
      obtain ⟨wl, vl⟩ := p
      obtain ⟨hwr, hch⟩ := hw
      have hown : ∀ w v', gwritesByte GD.gdG w a v' → WeakRvwmoGraph.gpo GD.gdG w r →
          w ∈ H.map Prod.fst := fun w v' hw' hpo => (hnpo w v' hw' hpo.1).elim
      ihave Hcov := AxSpinProt5.covMoX γ X a GD s r haX hwp $$ Hinv
      ihave HT := (AxSpinProt.tokTieSingleton GD γ a H e ht).1 $$ Ha
      icases (persistent_entails_left (ownedReadRule (GF := GF) GD a r γ H {[e := (1 : Qp)]} wl vl
          hcons hwr hch hown hlast ⟨t, v, hrd⟩
          (Or.inl ⟨e, by rw [domSingleton, elemOfSingleton], her⟩)))
        $$ [$HT $Hcov] with ⟨⟨HT, -⟩, %hv⟩
      ihave Ha := (AxSpinProt.tokTieSingleton GD γ a H e ht).2 $$ HT
      isplitl [Ha]
      · iexists H
        isplitl [Ha]
        · iexact Ha
        · ipureintro
          exact ⟨Or.inr ht, hwr, hch⟩
      · ipureintro
        right
        obtain ⟨⟨t', v', hrd', hat⟩, -⟩ := hv
        obtain ⟨rfl, rfl⟩ := greadsByteDet _ _ _ _ _ _ _ hrd hrd'
        have hwl : gwritesByte GD.gdG wl a v := by
          cases t with
          | zero => simp [gwriteAt] at hat
          | succ j =>
            obtain ⟨w', hat', hw', -⟩ := (hcons.2.2.1 r a (j + 1) v hrd).1
            rw [hat] at hat'
            cases hat'
            exact hw'
        refine ⟨wl, hat, hwl, ?_⟩
        have hl1 := hentLastFst H wl vl hlast
        rcases ht with ht | ⟨wl', ht, hlt⟩
        · rw [hl1, Option.some.injEq] at ht
          exact Or.inl ht
        · rw [hl1, Option.some.injEq] at ht
          subst ht
          exact Or.inr hlt

end rl

/-- Transporting a family of components, each from its own anchor. -/
theorem transportComps {GF : BundledGFunctors} (GD : Gdexec) (Rs : List (Geid → IProp GF))
    (w : Geid) :
    (∀ Rj, Rj ∈ Rs → lkTransportable GD Rj) →
    ([∗list] Rj ∈ Rs, ∃ a, ⌜gobCat GD a w⌝ ∗ Rj a) ⊢ [∗list] Rj ∈ Rs, Rj w := by
  intro htr
  refine BigSepL.bigSepL_mono fun {k Rj} hk => ?_
  iintro ⟨%a, %hob, HR⟩
  iapply (htr Rj (List.mem_of_getElem? hk) a w hob)
  iexact HR

/-! # 5. REQUIRED (1) at the Phase-1a instance `spinOb`: `feRelease'` takes EACH component of
`R` from `flowIn` at its own anchor; the single-anchor `feRelease` is its corollary
`feReleaseOf'`. -/

section relOld
variable {hlc : HasLC} {GF : BundledGFunctors.{0,0,0}} [InvGS_gen hlc GF] [AxannotGS GF]
  [AxlogG GF Hent] [SpinlockG GF]

theorem feRelease' (lk x : Int) (GT : GdexecT) (nm : spinN)
    (Hcons : rvwmoCatConsistent (gtAdGd GT)) (w : Geid) (i : Nat) (c : Geid)
    (R : Geid → IProp GF) (Rs : List (Geid → IProp GF)) (flowIn : Mea GF) :
    zw lk (gtAdGd GT).gdG w → (∀ t v, ¬ greadsByte (gtAdGd GT).gdG w lk t v) →
    (∀ v', ¬ gwritesByte (gtAdGd GT).gdG w x v') →
    (∀ Rj, Rj ∈ Rs → lkTransportable (gtAdGd GT) Rj) → (([∗list] Rj ∈ Rs, Rj w) ⊢ R w) →
    ⊢ isLock nm.2 lk R -∗
      (([∗map] Rin ∈ flowIn, Rin) -∗
        locked nm.2 lk i c ∗ [∗list] Rj ∈ Rs, ∃ a, ⌜gobCat (gtAdGd GT) a w⌝ ∗ Rj a) -∗
      @flowEqDyn hlc GF _ (splG lk x GT nm) (gtAdGd GT) w
        (@Axpol.sPol (splPol GT) (gtAdGd GT) w) flowIn
        iprop(notheld nm.2 lk i ∗
          ⌜∀ r, r ∈ spSpol GT (gtAdGd GT) w → lkread lk (gtAdGd GT).gdG r →
            WeakRvwmoGraph.gpo (gtAdGd GT).gdG c r → nolk lk (gtAdGd GT).gdG c r →
            ∀ t v, greadsByte (gtAdGd GT).gdG r lk t v → v ≠ b0⌝) := by
  intro Hzw Hnr Hs Htr HRs
  iintro #Hil Hfi
  iapply feBuild
  iintro %s %Hn %Hwc %Hwp %Hsub Ho Hl Hin
  ihave ⟨Hlk, HRc⟩ := Hfi $$ Hin
  icases (lkInvGateNz nm.2 lk (gtAdGd GT) s i c) $$ [$Hl $Hlk] with ⟨Hl, Hlk, %Hnz⟩
  ihave HRc := (transportComps (gtAdGd GT) Rs w Htr) $$ HRc
  ihave HR := HRs $$ HRc
  ihave H := (lkInvRelease nm.2 lk (gtAdGd GT) s w i c R Hcons Hwc Hn Hzw Hnr)
    $$ [$Hl $Hlk $Hil $HR]
  imodintro
  inext
  imod H with ⟨Hl, Hnh, -⟩
  imodintro
  isplitl [Ho]
  · iapply (ownInvOther ({x} : GSet Int) nm.1 (gtAdGd GT) s w Hn (nxOf x GT w Hs)) $$ Ho
  isplitl [Hl]
  · iexact Hl
  isplitl [Hnh]
  · iexact Hnh
  · ipureintro
    intro r Hr
    exact Hnz r (Hsub r Hr)

/-- The Phase-1a single-anchor release, as a corollary (`Rs := [R]`). -/
theorem feReleaseOf' (lk x : Int) (GT : GdexecT) (nm : spinN)
    (Hcons : rvwmoCatConsistent (gtAdGd GT)) (w : Geid) (i : Nat) (c a : Geid)
    (R : Geid → IProp GF) (flowIn : Mea GF) :
    zw lk (gtAdGd GT).gdG w → (∀ t v, ¬ greadsByte (gtAdGd GT).gdG w lk t v) →
    (∀ v', ¬ gwritesByte (gtAdGd GT).gdG w x v') →
    gobCat (gtAdGd GT) a w → lkTransportable (gtAdGd GT) R →
    ⊢ isLock nm.2 lk R -∗
      (([∗map] Rin ∈ flowIn, Rin) -∗ locked nm.2 lk i c ∗ R a) -∗
      @flowEqDyn hlc GF _ (splG lk x GT nm) (gtAdGd GT) w
        (@Axpol.sPol (splPol GT) (gtAdGd GT) w) flowIn
        iprop(notheld nm.2 lk i ∗
          ⌜∀ r, r ∈ spSpol GT (gtAdGd GT) w → lkread lk (gtAdGd GT).gdG r →
            WeakRvwmoGraph.gpo (gtAdGd GT).gdG c r → nolk lk (gtAdGd GT).gdG c r →
            ∀ t v, greadsByte (gtAdGd GT).gdG r lk t v → v ≠ b0⌝) := by
  intro Hzw Hnr Hs Hob Htr
  have HF : ∀ Rj, Rj ∈ [R] → lkTransportable (gtAdGd GT) Rj := by
    intro Rj h
    rw [List.mem_singleton.1 h]
    exact Htr
  have HRs : ([∗list] Rj ∈ [R], Rj w) ⊢ R w := BigSepL.bigSepL_singleton.1
  iintro #Hil Hfi
  ihave Hfe := feRelease' (hlc := hlc) lk x GT nm Hcons w i c R [R] flowIn Hzw Hnr Hs HF HRs
  ihave Hfe := Hfe $$ Hil
  iapply Hfe
  iintro Hin
  ihave ⟨Hlk, HR⟩ := Hfi $$ Hin
  isplitl [Hlk]
  · iexact Hlk
  · iapply BigSepL.bigSepL_singleton.2
    iexists a
    isplitr [HR]
    · ipureintro
      exact Hob
    · iexact HR

end relOld

end Weak
