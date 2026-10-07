/-
Weak: Phase 1a of the spinlock plan -- the LOCK COMPONENT of the joint instance `prot_xv6`
(pure graph lemmas + the per-lock ghost protocol + its ∀σ-robust STEP RULES), plus the
Own-class byte component the certificates need.

Rocq: `iris/AxSpinProt.v` @ xxvzwolszwmp.

Rocq header, in substance.  Every rule is indexed by (address, class, READ value, WRITTEN value)
of the event at the lock byte `lk` (the low byte of the lock word), never by row position:
  - RMW writing `b1`, reading `≠ b0`          ⇒ NEUTRAL (`lkBodyNeutral`);
  - RMW writing `b1`, reading `b0` (a CLAIM)  ⇒ unique by atomicity (`lkClaimUnique`); pulls the
    `R` parked at its rf-source release (or the genesis box), transported along `gco`
    (`lkBodyClaim`);
  - the ONLY arm admitting a written `b0`: the RELEASE (`lkBodyRelease`), consuming `locked`,
    parking `R w` in the mailbox of THAT write;
  - a plain read of `lk` (`lkBodyRead`) re-establishes the READ-FACT conjunct `NZ`;
  - every other event leaves the component alone (`lkBodyOther`).
STATE (`lkBody γh R GD s`, over the processed set `s`): GENESIS BOX `gbox`; MAILBOXES `mbox`;
HOLDER `∃ st m, ghost_map_auth γh 1 m ∗ ⌜holdOk s st ∧ NZ s st ∧ link m st⌝` (`m` the per-hart
ghost whose fragments are `notheld` (`i ↪ none`) and `locked` (`i ↪ some c`)).
∀σ-ROBUSTNESS: no step lemma assumes anything about `s` beyond the global conjunct `WC` ("every
write gmo-before a processed event is processed") and the handout `WPh`; `wcGmoAfter` gives
"lock writes are processed in gmo order" from `WC` alone.  §4 the registration (`isLock`,
`notheld`, `locked`, `lkInv`) and its rules; allocation (`lkInvAlloc`); §5 the Own-class
component (`ownInv`, per-byte history snapshots); §6 the client predicate `Rx` (an owned byte
whose locked history only ever writes `b1`) with its read/write rules.

PIPELINE: hand rows only -- no instruction fetch, no decode.  No statement mentions a fetch:
the vocabulary is the graph tier's byte footprints (`gwritesByte`/`greadsByte`), `gmoLt`,
`WeakRvwmoGraph.gpo`, `gco`, `gobCat` (`Lbl` has no fetch constructor), so the removal of
fetches from the graph tier does not touch this file.

**Deviations from Rocq.**

1. NAMES: camelCase (map below).  Duplicated Rocq names declared file-qualified:
   `AxSpinProt.claimed`, `AxSpinProt.chainWithSnoc'`.  Dependencies' duplicates referred to
   qualified (`WeakRvwmoGraph.gpo`, `WeakRvwmoGraph.gwixPos`, `WeakRvwmoGraph.glblIsRGmem`,
   `WeakRvwmoGraph.gwritesByteGisW`).
2. VOCABULARY (as `AxToken`/`AxLockOwn` deviation 2): `Z` ↦ `Int`; `agent` ↦ `Nat`; `gset geid`
   ↦ `GSet Geid`; `{[e]} ∪ s` ↦ `({e} : GSet Geid) ∪ s`; `gmap agent (option geid)` ↦
   `GMapF Nat (Option Geid)`, `m !! j` ↦ `get? m j`, `<[j := o]> m` ↦ `insert m j o`, `dom m` ↦
   `FiniteMap.dom_set m`; `gd_g GD` ↦ `GD.gdG`; `gx_img G x` ↦ `G.gxImg x`; `last l` ↦
   `l.getLast?`; `H.*1` ↦ `H.map Prod.fst`; `Forall P H` ↦ `∀ p, p ∈ H → P p`; `B0`/`B1` ↦
   `b0`/`b1` (`WeakLitmus`).
3. CAMERAS: `spinlockG Σ` ↦ class `SpinlockG GF` (instance fields `SavedPredG GF Geid`,
   `GhostMapG GF Nat (Option Geid) (GMapF Nat)`, `GhostMapG GF Int (GName × GName) (GMapF Int)`);
   the notation `lk_names` is inlined as `GName × GName`;
   `spinlockΣ` / `subG_spinlockΣ` have no Lean twin (subsumed by `BundledGFunctors` synthesis).
   `lk ↪[reg]□ v` ↦ `ghost_map_elem reg DFrac.discard lk v`; `i ↪[γh] v` ↦
   `ghost_map_elem γh (DFrac.own 1) i v`; `axlogG Σ hent` ↦ `[AxlogG GF Hent]`.
4. STATEMENT SHAPES (tree convention): `P -∗ Q` ↦ `P ⊢ Q`; `P -∗ Q -∗ R` ↦ `P ∗ Q ⊢ R`;
   `P -∗ Q ==∗ R` ↦ `P ∗ Q ⊢ |==> R`; pure premises stay `→`.  Section variables are explicit
   arguments in Rocq's order (`lk` first; `GD`/`Hcons` next in §2), only where Rocq's section
   mechanism includes them (`readTNone`, `wcGmoAfter` take no `lk`, as in Rocq).
5. Lean-only helpers (file-qualified): `AxSpinProt.bigSepSUnionSingleton`,
   `AxSpinProt.holdOkInsert`, `AxSpinProt.nzInsertNotRead`, `AxSpinProt.mboxOfNotZw`,
   `AxSpinProt.lkBodyStep` (the common frame of the other/read/neutral rules),
   `AxSpinProt.stForSome`, `AxSpinProt.covMo`, `AxSpinProt.covRfe`,
   `AxSpinProt.tokTieSingleton`.
6. PROOFS (not statements): `notheldExcl`/`lockedNotheld` use `ghost_map_elem_ne` (two full
   fragments at one key) instead of `iCombine … gives %[? _]`; `lkInvAlloc` allocates the
   registration map empty and inserts `lk` persistently (instead of `ghost_map_alloc` of the
   singleton + `big_sepM_singleton`); `lkClaimSrc` reads the source's index off
   `gwriteAtInv` directly.
7. Rocq's `iRewrite` along `saved_pred_agree` ↦ `AxWp.eqWand` under `inext`.

**Rocq → Lean name map.**  `zw` `zw`, `lk_claim` `lkClaim`, `lkread` `lkread`, `nolk` `nolk`,
`claimed` `AxSpinProt.claimed`, `hold_ok` `holdOk`, `NZ` `NZ`, `st_for` `stFor`, `link` `link`,
`WC` `WC`, `WPh` `WPh`, `WC_insert` `WCInsert`, `WP_of_WC_mem` `WPOfWCMem`, `b0_ne_b1'`
`b0NeB1'`, `gwb_gmo` `gwbGmo`, `grb_gmo` `grbGmo`, `read_t_none` `readTNone`, `lk_claim_t`
`lkClaimT`, `lk_claim_unique` `lkClaimUnique`, `lk_claim_src` `lkClaimSrc`,
`lk_claim_adjacent` `lkClaimAdjacent`, `lk_claim_genesis_first` `lkClaimGenesisFirst`,
`wc_gmo_after` `wcGmoAfter`, `hold_none_of_claim` `holdNoneOfClaim`, `nz_core` `nzCore`,
`nz_read` `nzRead`, `nz_new_claim` `nzNewClaim`, `spinlockG` `SpinlockG` (fields
`spinSavedPredG`/`spinHoldG`/`spinRegG`), `lk_transportable` `lkTransportable`, `mbox` `mbox`,
`gbox` `gbox`, `lk_body` `lkBody`, `claimed_mono` `claimedMono`, `mbox_mono` `mboxMono`,
`gbox_mono` `gboxMono`, `mboxes_mono` `mboxesMono`, `mboxes_insert` `mboxesInsert`,
`lk_body_other` `lkBodyOther`, `lk_body_read` `lkBodyRead`, `lk_body_neutral`
`lkBodyNeutral`, `lk_body_claim` `lkBodyClaim`, `lk_body_release` `lkBodyRelease`,
`lk_body_gate_nz` `lkBodyGateNz`, `is_lock` `isLock`, `is_lock_persistent`
`isLockPersistent`, `notheld` `notheld`, `locked` `locked`, `notheld_excl` `notheldExcl`,
`locked_notheld` `lockedNotheld`, `lk_inv` `lkInv`, `lk_inv_other` `lkInvOther`,
`lk_inv_read` `lkInvRead`, `lk_inv_neutral` `lkInvNeutral`, `lk_inv_claim` `lkInvClaim`,
`lk_inv_release` `lkInvRelease`, `lk_inv_gate_nz` `lkInvGateNz`, `alloc_harts` `allocHarts`,
`lk_inv_alloc` `lkInvAlloc`, `Φx` `Φx`, `Φx_persistent` `ΦxPersistent`, `own_inv` `ownInv`,
`own_inv_persistent` `ownInvPersistent`, `own_inv_other` `ownInvOther`, `own_inv_write`
`ownInvWrite`, `own_inv_cov` `ownInvCov`, `chain_with_snoc'` `AxSpinProt.chainWithSnoc'`,
`hwf` `hwf`, `Rx` `Rx`, `Rx_transportable` `RxTransportable`, `hwf_nil` `hwfNil`,
`Rx_genesis` `RxGenesis`, `Rx_read` `RxRead`, `Rx_write` `RxWrite`.

**Dropped:** `spinlockΣ`, `subG_spinlockΣ`, the `lk_names` notation (no Lean twin, deviation 3).  Every other definition
and lemma of `AxSpinProt.v` is ported.
-/
import Weak.AxLockOwn
import Weak.AxToken
import Weak.AxWp
import Weak.AxGhost
import Weak.AxLockGraph
import Weak.AxGraphCat
import Weak.AxGraph
import Weak.WeakRvwmoGraph
import Weak.WeakRvwmoLock
import Weak.WeakRvwmoAcyc
import Weak.WeakLitmus
import MachCSL.StdppMap
import MachCSL.StdppSet
import Iris.Instances.Lib.GhostMap
import Iris.Instances.Lib.SavedProp
import Iris.BI.BigOp.BigSepSet
import Iris.BI.BigOp.BigSepList
import Iris.ProofMode

namespace Weak

open Iris Iris.BI Iris.Std Iris.Std.PartialMap MachCSL MachCSL.Stdpp

/-! ## 1. Pure graph vocabulary of the lock byte -/

/-- A ZERO-WRITE (a release, in a protocol-respecting graph). -/
def zw (lk : Int) (G : Gexec) (e : Geid) : Prop := gwritesByte G e lk b0

/-- A CLAIM of the source `oz` (`none` = genesis): an RMW reading `b0` at `lk` from `oz`,
writing `b1` there. -/
def lkClaim (lk : Int) (G : Gexec) (c : Geid) (oz : Option Geid) : Prop :=
  ∃ t, greadsByte G c lk t b0 ∧ gwriteAt G t = oz ∧ gwritesByte G c lk b1

/-- A plain (non-write) read of the lock byte. -/
def lkread (lk : Int) (G : Gexec) (r : Geid) : Prop :=
  (∃ t v, greadsByte G r lk t v) ∧ gisW G r = false

/-- No write to the lock byte po-between `c` and `r` (a ROW fact). -/
def nolk (lk : Int) (G : Gexec) (c r : Geid) : Prop :=
  ∀ w v, gwritesByte G w lk v → WeakRvwmoGraph.gpo G c w → WeakRvwmoGraph.gpo G w r → False

def AxSpinProt.claimed (lk : Int) (G : Gexec) (s : GSet Geid) (oz : Option Geid) : Prop :=
  ∃ c, c ∈ s ∧ lkClaim lk G c oz

/-- CLAIMS + HELD_NZ. -/
def holdOk (lk : Int) (G : Gexec) (s : GSet Geid) : Option Geid → Prop
  | none => ∀ c oz, c ∈ s → lkClaim lk G c oz → ∃ w, w ∈ s ∧ zw lk G w ∧ gmoLt G c w
  | some c =>
      c ∈ s ∧ (∃ oz, lkClaim lk G c oz) ∧
      (∀ w, w ∈ s → zw lk G w → ¬ gmoLt G c w) ∧
      (∀ c' oz, c' ∈ s → c' ≠ c → lkClaim lk G c' oz → ∃ w, w ∈ s ∧ zw lk G w ∧ gmoLt G c' w)

/-- READ FACTS. -/
def NZ (lk : Int) (G : Gexec) (s : GSet Geid) (st : Option Geid) : Prop :=
  ∀ c, st = some c → ∀ r, r ∈ s → lkread lk G r → WeakRvwmoGraph.gpo G c r → nolk lk G c r →
    ∀ t v, greadsByte G r lk t v → v ≠ b0

/-- NOTHELD_LINK, pure half. -/
def stFor (st : Option Geid) (j : Nat) : Option Geid :=
  match st with
  | some c => if c.1 = j then some c else none
  | none => none

def link (m : GMapF Nat (Option Geid)) (st : Option Geid) : Prop :=
  (∀ j o, get? m j = some o → o = stFor st j) ∧ (∀ c, st = some c → get? m c.1 = some (some c))

/-- The GLOBAL conjunct (not lock-specific): processed events have all their gmo-earlier writes
processed. -/
def WC (G : Gexec) (s : GSet Geid) : Prop :=
  ∀ e w, e ∈ s → gisW G w = true → gmoLt G w e → w ∈ s

/-- The handout fact every flow equation gets from `s_pol`. -/
def WPh (G : Gexec) (s : GSet Geid) (e : Geid) : Prop :=
  ∀ w, gisW G w = true → gmoLt G w e → w ∈ s

theorem WCInsert (G : Gexec) (s : GSet Geid) (e : Geid) :
    WC G s → WPh G s e → WC G (({e} : GSet Geid) ∪ s) := by
  intro hwc hwp e' w he' hw hlt
  rcases elemOfUnion.1 he' with h | h
  · rw [elemOfSingleton.1 h] at hlt
    exact elemOfUnionR (hwp w hw hlt)
  · exact elemOfUnionR (hwc e' w h hw hlt)

theorem WPOfWCMem (G : Gexec) (s : GSet Geid) (e w : Geid) :
    WC G s → e ∈ s → gisW G w = true → gmoLt G w e → w ∈ s :=
  fun hwc he hw hlt => hwc e w he hw hlt

/-! ## 2. Pure graph lemmas (atomicity, uniqueness, adjacency) -/

theorem b0NeB1' : b0 ≠ b1 := b0NeB1

theorem gwbGmo (G : Gexec) (e : Geid) (a : Int) (v : BitVec 8) :
    gwf G → gwritesByte G e a v → e ∈ G.gxGmo :=
  fun hwf hw => ((gwritesElemOf G e).1 (gwritesByteGwrites G e a v hwf hw)).1

theorem grbGmo (G : Gexec) (e : Geid) (a : Int) (t : Nat) (v : BitVec 8) :
    gwf G → greadsByte G e a t v → e ∈ G.gxGmo :=
  fun hwf hr => gwfMemGmo G e hwf (WeakRvwmoGraph.glblIsRGmem G e (greadsByteGlblR G e a t v hr))

theorem readTNone (GD : Gdexec) (hcons : rvwmoCatConsistent GD) (c : Geid) (a : Int) (t : Nat)
    (v : BitVec 8) :
    greadsByte GD.gdG c a t v → gwriteAt GD.gdG t = none → t = 0 := by
  intro hr ha
  cases t with
  | zero => rfl
  | succ j =>
    obtain ⟨w, hw, -⟩ := (hcons.2.2.1 c a (j + 1) v hr).1
    rw [ha] at hw
    cases hw

theorem lkClaimT (lk : Int) (GD : Gdexec) (hcons : rvwmoCatConsistent GD) (c : Geid)
    (oz : Option Geid) :
    lkClaim lk GD.gdG c oz →
    ∃ t, greadsByte GD.gdG c lk t b0 ∧ gwritesByte GD.gdG c lk b1 ∧
      (match oz with
       | none => t = 0
       | some z => t = gwix GD.gdG z ∧ z ∈ gwrites GD.gdG) := by
  rintro ⟨t, hr, ha, hw⟩
  refine ⟨t, hr, hw, ?_⟩
  cases oz with
  | some z =>
    obtain ⟨hz, hix⟩ := gwriteAtInv GD.gdG t z hcons.1.1 ha
    exact ⟨hix.symm, hz⟩
  | none => exact readTNone GD hcons c lk t b0 hr ha

theorem lkClaimUnique (lk : Int) (GD : Gdexec) (hcons : rvwmoCatConsistent GD) (c1 c2 : Geid)
    (oz : Option Geid) :
    lkClaim lk GD.gdG c1 oz → lkClaim lk GD.gdG c2 oz → c1 = c2 := by
  intro h1 h2
  obtain ⟨t1, hr1, hw1, ht1⟩ := lkClaimT lk GD hcons c1 oz h1
  obtain ⟨t2, hr2, hw2, ht2⟩ := lkClaimT lk GD hcons c2 oz h2
  have heq : t1 = t2 := by
    cases oz with
    | some z =>
      obtain ⟨e1, -⟩ : t1 = gwix GD.gdG z ∧ z ∈ gwrites GD.gdG := ht1
      obtain ⟨e2, -⟩ : t2 = gwix GD.gdG z ∧ z ∈ gwrites GD.gdG := ht2
      exact e1.trans e2.symm
    | none =>
      have e1 : t1 = 0 := ht1
      have e2 : t2 = 0 := ht2
      exact e1.trans e2.symm
  subst heq
  exact catRmwUniqueReader GD lk t1 c1 c2 b0 b0 b1 b1 hcons hr1 hw1 hr2 hw2

/-- The claimed source of a release-sourced claim: a zero-write, gmo-before and `gco`-before
the claim. -/
theorem lkClaimSrc (lk : Int) (GD : Gdexec) (hcons : rvwmoCatConsistent GD) (c z : Geid) :
    lkClaim lk GD.gdG c (some z) → zw lk GD.gdG z ∧ gmoLt GD.gdG z c ∧ gco GD.gdG z c := by
  rintro ⟨t, hr, ha, hw⟩
  have hwf := hcons.1
  obtain ⟨hz, hix⟩ := gwriteAtInv GD.gdG t z hwf.1 ha
  have hpos := WeakRvwmoGraph.gwixPos GD.gdG z hz
  have hlt := catRmwTsLt GD c lk t b0 b1 hcons hr hw
  have hcw := gwritesByteGwrites GD.gdG c lk b1 hwf hw
  have hwb : gwritesByte GD.gdG z lk b0 := by
    cases t with
    | zero => omega
    | succ j =>
      obtain ⟨w, hat, hwb, -⟩ := (hcons.2.2.1 c lk (j + 1) b0 hr).1
      rw [ha] at hat
      cases hat
      exact hwb
  exact ⟨hwb, gwixLtGmo GD.gdG z c hwf hz hcw (by omega), ⟨lk, b0, b1, hwb, hw, by omega⟩⟩

/-- ATOMICITY at the lock byte: nothing is written to `lk` gmo-strictly between a claim and its
source. -/
theorem lkClaimAdjacent (lk : Int) (GD : Gdexec) (hcons : rvwmoCatConsistent GD) (c z w : Geid)
    (v : BitVec 8) :
    lkClaim lk GD.gdG c (some z) → gwritesByte GD.gdG w lk v → gmoLt GD.gdG w c →
    w = z ∨ gmoLt GD.gdG w z := by
  intro hc hw hlt
  obtain ⟨t, hr, hwc, ht⟩ := lkClaimT lk GD hcons c (some z) hc
  obtain ⟨ht, hz⟩ : t = gwix GD.gdG z ∧ z ∈ gwrites GD.gdG := ht
  have hwf := hcons.1
  have hww := gwritesByteGwrites GD.gdG w lk v hwf hw
  have hcw := gwritesByteGwrites GD.gdG c lk b1 hwf hwc
  have hlt' := gmoGwixLt GD.gdG w c hwf hww hcw hlt
  have hna := hcons.2.2.2.1 c lk t b0 hr (gwritesByteGlblW _ _ _ _ hwc) w v hw
  subst ht
  by_cases heq : gwix GD.gdG w = gwix GD.gdG z
  · exact Or.inl (gwixInj GD.gdG w z hwf.1 hww hz heq)
  · exact Or.inr (gwixLtGmo GD.gdG w z hwf hww hz (by omega))

theorem lkClaimGenesisFirst (lk : Int) (GD : Gdexec) (hcons : rvwmoCatConsistent GD)
    (c w : Geid) (v : BitVec 8) :
    lkClaim lk GD.gdG c none → gwritesByte GD.gdG w lk v → gmoLt GD.gdG w c → False := by
  intro hc hw hlt
  obtain ⟨t, hr, hwc, ht⟩ := lkClaimT lk GD hcons c none hc
  have ht : t = 0 := ht
  have hwf := hcons.1
  have hww := gwritesByteGwrites GD.gdG w lk v hwf hw
  have hcw := gwritesByteGwrites GD.gdG c lk b1 hwf hwc
  have hlt' := gmoGwixLt GD.gdG w c hwf hww hcw hlt
  have hp := WeakRvwmoGraph.gwixPos GD.gdG w hww
  subst ht
  exact hcons.2.2.2.1 c lk 0 b0 hr (gwritesByteGlblW _ _ _ _ hwc) w v hw ⟨hp, hlt'⟩

/-- Processed lock writes are processed in gmo order (from `WC`). -/
theorem wcGmoAfter (GD : Gdexec) (hcons : rvwmoCatConsistent GD) (s : GSet Geid) (e w : Geid)
    (a : Int) (v : BitVec 8) (a' : Int) (v' : BitVec 8) :
    WC GD.gdG s → e ∈ s → w ∉ s → gwritesByte GD.gdG e a v → gwritesByte GD.gdG w a' v' →
    gmoLt GD.gdG e w := by
  intro hwc he hw hwe hww
  have hwf := hcons.1
  have he' := gwbGmo GD.gdG e a v hwf hwe
  have hw' := gwbGmo GD.gdG w a' v' hwf hww
  have hne : e ≠ w := fun h => hw (h ▸ he)
  rcases gmoLtTotal GD.gdG e w hwf.1 he' hw' hne with h | h
  · exact h
  · exact absurd (hwc e w he (WeakRvwmoGraph.gwritesByteGisW _ _ _ _ hww) h) hw

/-- A new claim finds the lock FREE. -/
theorem holdNoneOfClaim (lk : Int) (GD : Gdexec) (hcons : rvwmoCatConsistent GD)
    (s : GSet Geid) (st : Option Geid) (c : Geid) (oz : Option Geid) :
    WC GD.gdG s → WPh GD.gdG s c → c ∉ s → lkClaim lk GD.gdG c oz → holdOk lk GD.gdG s st →
    st = none := by
  intro hwc hwp hc hcl hh
  cases st with
  | none => rfl
  | some c0 =>
    exfalso
    obtain ⟨hc0, ⟨oz0, hcl0⟩, hnz, -⟩ := hh
    obtain ⟨t0, -, hw0, -⟩ := lkClaimT lk GD hcons c0 oz0 hcl0
    obtain ⟨t, hr, hw, -⟩ := lkClaimT lk GD hcons c oz hcl
    have hlt := wcGmoAfter GD hcons s c0 c lk b1 lk b1 hwc hc0 hc hw0 hw
    cases oz with
    | some z =>
      rcases lkClaimAdjacent lk GD hcons c z c0 b1 hcl hw0 hlt with heq | hlt'
      · subst heq
        obtain ⟨hzw, -⟩ := lkClaimSrc lk GD hcons c c0 hcl
        exact b0NeB1 (gwritesByteDet _ _ _ _ _ hzw hw0)
      · obtain ⟨hzw, hzc, -⟩ := lkClaimSrc lk GD hcons c z hcl
        exact hnz z (hwp z (WeakRvwmoGraph.gwritesByteGisW _ _ _ _ hzw) hzc) hzw hlt'
    | none => exact lkClaimGenesisFirst lk GD hcons c c0 b1 hcl hw0 hlt

/-- The READ-FACT core: a read of `b0` at `lk`, po-after a `b1`-write `c` of `lk` with no lock
write po-between, reads a zero-write that is gmo-strictly between `c` and the read. -/
theorem nzCore (lk : Int) (GD : Gdexec) (hcons : rvwmoCatConsistent GD) (c r : Geid) (t : Nat) :
    gwritesByte GD.gdG c lk b1 → WeakRvwmoGraph.gpo GD.gdG c r → nolk lk GD.gdG c r →
    greadsByte GD.gdG r lk t b0 →
    ∃ z, zw lk GD.gdG z ∧ gmoLt GD.gdG c z ∧ gmoLt GD.gdG z r := by
  intro hwc hpo hnl hr
  have hwf := hcons.1
  have hppo := hcons.2.1
  have hcw := gwritesByteGwrites GD.gdG c lk b1 hwf hwc
  obtain ⟨hsrc, hmax⟩ := hcons.2.2.1 r lk t b0 hr
  have hle := hmax c b1 hwc (Or.inr hpo)
  cases t with
  | zero =>
    have := WeakRvwmoGraph.gwixPos GD.gdG c hcw
    omega
  | succ j =>
    obtain ⟨z, hat, hzw, hvis⟩ := hsrc
    obtain ⟨hz, hzix⟩ := gwriteAtInv GD.gdG (j + 1) z hwf.1 hat
    have hne : c ≠ z := by
      intro h
      subst h
      exact b0NeB1 (gwritesByteDet _ _ _ _ _ hzw hwc)
    have hcz : gmoLt GD.gdG c z := by
      apply gwixLtGmo GD.gdG c z hwf hcw hz
      by_cases heq : gwix GD.gdG c = gwix GD.gdG z
      · exact absurd (gwixInj GD.gdG c z hwf.1 hcw hz heq) hne
      · omega
    refine ⟨z, hzw, hcz, ?_⟩
    rcases hvis with hzr | hzr
    · exact hzr
    · exfalso
      obtain ⟨hh1, -, hs1, -⟩ := hpo
      obtain ⟨hh2, hlt2, hs2, hs3⟩ := hzr
      by_cases hzc : z.2 < c.2
      · have hppo1 : gmoLt GD.gdG z c :=
          hppo z c (Or.inl (Or.inl ⟨⟨hh2.trans hh1.symm, hzc, hs2, hs1⟩, lk,
            Or.inl ⟨b0, hzw⟩, b1, hwc⟩))
        exact gmoLtIrrefl _ _ (gmoLtTrans _ _ _ _ hcz hppo1)
      · by_cases hzc' : z.2 = c.2
        · exact hne (Prod.ext (hh1.trans hh2.symm) hzc'.symm)
        · exact hnl z b0 hzw ⟨hh1.trans hh2.symm, by omega, hs1, hs2⟩ ⟨hh2, hlt2, hs2, hs3⟩

/-- The READ-FACT argument for a NEW read under the current claim. -/
theorem nzRead (lk : Int) (GD : Gdexec) (hcons : rvwmoCatConsistent GD) (s : GSet Geid)
    (c r : Geid) (t : Nat) (v : BitVec 8) :
    WPh GD.gdG s r → holdOk lk GD.gdG s (some c) → WeakRvwmoGraph.gpo GD.gdG c r →
    nolk lk GD.gdG c r → greadsByte GD.gdG r lk t v → v ≠ b0 := by
  rintro hwp ⟨-, ⟨oz, hcl⟩, hnz, -⟩ hpo hnl hr rfl
  obtain ⟨-, -, hwc, -⟩ := lkClaimT lk GD hcons c oz hcl
  obtain ⟨z, hzw, hcz, hzr⟩ := nzCore lk GD hcons c r t hwc hpo hnl hr
  exact hnz z (hwp z (WeakRvwmoGraph.gwritesByteGisW _ _ _ _ hzw) hzr) hzw hcz

/-- ... and for an OLD read when a new claim arrives: impossible (the read would have forced
the claim to be processed first). -/
theorem nzNewClaim (lk : Int) (GD : Gdexec) (hcons : rvwmoCatConsistent GD) (s : GSet Geid)
    (c r : Geid) (t : Nat) (v : BitVec 8) :
    WC GD.gdG s → r ∈ s → c ∉ s → gwritesByte GD.gdG c lk b1 → WeakRvwmoGraph.gpo GD.gdG c r →
    nolk lk GD.gdG c r → greadsByte GD.gdG r lk t v → v ≠ b0 := by
  intro hwc hr hc hwc' hpo hnl hrd hv
  subst hv
  obtain ⟨z, hzw, hcz, hzr⟩ := nzCore lk GD hcons c r t hwc' hpo hnl hrd
  have hz : z ∈ s := hwc r z hr (WeakRvwmoGraph.gwritesByteGisW _ _ _ _ hzw) hzr
  exact hc (hwc z c hz (WeakRvwmoGraph.gwritesByteGisW _ _ _ _ hwc') hcz)

/-! ## 3. The lock component (ghost) -/

class SpinlockG (GF : BundledGFunctors) where
  [spinSavedPredG : SavedPredG GF Geid]
  [spinHoldG : GhostMapG GF Nat (Option Geid) (GMapF Nat)]
  [spinRegG : GhostMapG GF Int (GName × GName) (GMapF Int)]

attribute [reducible, instance] SpinlockG.spinSavedPredG SpinlockG.spinHoldG SpinlockG.spinRegG

/-- The client class: `R` is transportable along `gobCat`. -/
def lkTransportable {GF : BundledGFunctors} (GD : Gdexec) (R : Geid → IProp GF) : Prop :=
  ∀ e e', gobCat GD e e' → R e ⊢ R e'

/-- (Lean-only) `[∗set]` over `{e} ∪ s`. -/
theorem AxSpinProt.bigSepSUnionSingleton {GF : BundledGFunctors} {Φ : Geid → IProp GF}
    {s : GSet Geid} {e : Geid} (h : e ∉ s) :
    ([∗set] y ∈ ({e} : GSet Geid) ∪ s, Φ y) ⊣⊢ Φ e ∗ [∗set] y ∈ s, Φ y := by
  rw [← Iris.Std.LawfulSet.insert_union]
  exact BigSepS.bigSepS_insert h

/-- (Lean-only) `holdOk` survives an event that is neither a claim nor a zero-write. -/
theorem AxSpinProt.holdOkInsert (lk : Int) (G : Gexec) (s : GSet Geid) (st : Option Geid)
    (e : Geid) :
    (∀ oz, ¬ lkClaim lk G e oz) → ¬ zw lk G e → holdOk lk G s st →
    holdOk lk G (({e} : GSet Geid) ∪ s) st := by
  intro hncl hnz hh
  cases st with
  | none =>
    intro c oz hc hcl
    rcases elemOfUnion.1 hc with h | h
    · rw [elemOfSingleton.1 h] at hcl
      exact absurd hcl (hncl oz)
    · obtain ⟨w, hw, hz, hlt⟩ := hh c oz h hcl
      exact ⟨w, elemOfUnionR hw, hz, hlt⟩
  | some c =>
    obtain ⟨hc, hcl, hnz', hoth⟩ := hh
    refine ⟨elemOfUnionR hc, hcl, ?_, ?_⟩
    · intro w hw hz
      rcases elemOfUnion.1 hw with h | h
      · rw [elemOfSingleton.1 h] at hz
        exact absurd hz hnz
      · exact hnz' w h hz
    · intro c' oz hc' hne hcl'
      rcases elemOfUnion.1 hc' with h | h
      · rw [elemOfSingleton.1 h] at hcl'
        exact absurd hcl' (hncl oz)
      · obtain ⟨w, hw, hz, hlt⟩ := hoth c' oz h hne hcl'
        exact ⟨w, elemOfUnionR hw, hz, hlt⟩

/-- (Lean-only) `NZ` survives an event that is not a plain read of the lock byte. -/
theorem AxSpinProt.nzInsertNotRead (lk : Int) (G : Gexec) (s : GSet Geid) (st : Option Geid)
    (e : Geid) :
    ¬ lkread lk G e → NZ lk G s st → NZ lk G (({e} : GSet Geid) ∪ s) st := by
  intro hnr hnz c hst r hr
  rcases elemOfUnion.1 hr with h | h
  · rw [elemOfSingleton.1 h]
    intro hl
    exact absurd hl hnr
  · exact hnz c hst r h

section body

variable {GF : BundledGFunctors} [SpinlockG GF]

def mbox (lk : Int) (GD : Gdexec) (s : GSet Geid) (R : Geid → IProp GF) (w : Geid) :
    IProp GF :=
  iprop(⌜¬ zw lk GD.gdG w ∨ AxSpinProt.claimed lk GD.gdG s (some w)⌝ ∨ R w)

def gbox (lk : Int) (GD : Gdexec) (s : GSet Geid) (R : Geid → IProp GF) : IProp GF :=
  iprop(⌜AxSpinProt.claimed lk GD.gdG s none⌝ ∨ ∀ e, R e)

def lkBody (lk : Int) (γh : GName) (R : Geid → IProp GF) (GD : Gdexec) (s : GSet Geid) :
    IProp GF :=
  iprop(gbox lk GD s R ∗ ([∗set] w ∈ s, mbox lk GD s R w) ∗
    ∃ (st : Option Geid) (m : GMapF Nat (Option Geid)),
      ghost_map_auth γh (DFrac.own 1) m ∗
      ⌜holdOk lk GD.gdG s st ∧ NZ lk GD.gdG s st ∧ link m st⌝)

/-! ### 3.1 Monotonicity of the boxes in the processed set -/

omit [SpinlockG GF] in
theorem claimedMono (lk : Int) (G : Gexec) (s s' : GSet Geid) (oz : Option Geid) :
    s ⊆ s' → AxSpinProt.claimed lk G s oz → AxSpinProt.claimed lk G s' oz := by
  rintro hs ⟨c, hc, h⟩
  exact ⟨c, hs c hc, h⟩

omit [SpinlockG GF] in
theorem mboxMono (lk : Int) (GD : Gdexec) (s s' : GSet Geid) (R : Geid → IProp GF) (w : Geid) :
    s ⊆ s' → mbox lk GD s R w ⊢ mbox lk GD s' R w := by
  intro hs
  unfold mbox
  iintro (%h | H)
  · ileft
    ipureintro
    rcases h with h | h
    · exact Or.inl h
    · exact Or.inr (claimedMono lk _ s s' _ hs h)
  · iright
    iexact H

omit [SpinlockG GF] in
theorem gboxMono (lk : Int) (GD : Gdexec) (s s' : GSet Geid) (R : Geid → IProp GF) :
    s ⊆ s' → gbox lk GD s R ⊢ gbox lk GD s' R := by
  intro hs
  unfold gbox
  iintro (%h | H)
  · ileft
    ipureintro
    exact claimedMono lk _ s s' _ hs h
  · iright
    iexact H

theorem mboxesMono (lk : Int) (GD : Gdexec) (s s' : GSet Geid) (R : Geid → IProp GF) :
    s ⊆ s' → ([∗set] w ∈ s, mbox lk GD s R w) ⊢ [∗set] w ∈ s, mbox lk GD s' R w :=
  fun hs => BigSepS.bigSepS_mono fun {w} _ => mboxMono lk GD s s' R w hs

/-- Inserting `e` with an explicit new slot. -/
theorem mboxesInsert (lk : Int) (GD : Gdexec) (s : GSet Geid) (R : Geid → IProp GF) (e : Geid) :
    e ∉ s →
    ([∗set] w ∈ s, mbox lk GD s R w) ∗ mbox lk GD (({e} : GSet Geid) ∪ s) R e ⊢
      [∗set] w ∈ ({e} : GSet Geid) ∪ s, mbox lk GD (({e} : GSet Geid) ∪ s) R w := by
  intro he
  iintro ⟨Hs, He⟩
  iapply (AxSpinProt.bigSepSUnionSingleton he).2
  isplitl [He]
  · iexact He
  · iapply mboxesMono lk GD s (({e} : GSet Geid) ∪ s) R unionSubseteqR
    iexact Hs

omit [SpinlockG GF] in
/-- (Lean-only) a slot that is not a zero-write is trivially filled. -/
theorem AxSpinProt.mboxOfNotZw (lk : Int) (GD : Gdexec) (s : GSet Geid) (R : Geid → IProp GF)
    (w : Geid) : ¬ zw lk GD.gdG w → ⊢ mbox lk GD s R w := by
  intro h
  unfold mbox
  ileft
  ipureintro
  exact Or.inl h

/-- (Lean-only) THE COMMON FRAME of the other/read/neutral rules: a non-zero-write event `e`
whose pure effect on `holdOk`/`NZ` is given. -/
theorem AxSpinProt.lkBodyStep (lk : Int) (γh : GName) (R : Geid → IProp GF) (GD : Gdexec)
    (s : GSet Geid) (e : Geid) (hn : e ∉ s) (hnz : ¬ zw lk GD.gdG e)
    (hpure : ∀ st, holdOk lk GD.gdG s st → NZ lk GD.gdG s st →
      holdOk lk GD.gdG (({e} : GSet Geid) ∪ s) st ∧ NZ lk GD.gdG (({e} : GSet Geid) ∪ s) st) :
    lkBody lk γh R GD s ⊢ lkBody lk γh R GD (({e} : GSet Geid) ∪ s) := by
  unfold lkBody
  iintro ⟨Hg, Hm, %st, %m, Ha, %hp⟩
  obtain ⟨hh, hnz', hl⟩ := hp
  obtain ⟨hh2, hnz2⟩ := hpure st hh hnz'
  isplitl [Hg]
  · iapply gboxMono lk GD s (({e} : GSet Geid) ∪ s) R unionSubseteqR
    iexact Hg
  isplitl [Hm]
  · iapply mboxesInsert lk GD s R e hn
    isplitl [Hm]
    · iexact Hm
    · ihave H := AxSpinProt.mboxOfNotZw lk GD (({e} : GSet Geid) ∪ s) R e hnz
      iexact H
  · iexists st
    iexists m
    isplitl [Ha]
    · iexact Ha
    · ipureintro
      exact ⟨hh2, hnz2, hl⟩

/-! ### 3.2 THE FRAME RULE: an event that neither writes `lk` nor is a plain read of it -/

theorem lkBodyOther (lk : Int) (γh : GName) (R : Geid → IProp GF) (GD : Gdexec) (s : GSet Geid)
    (e : Geid) :
    e ∉ s → (∀ v, ¬ gwritesByte GD.gdG e lk v) → ¬ lkread lk GD.gdG e →
    lkBody lk γh R GD s ⊢ lkBody lk γh R GD (({e} : GSet Geid) ∪ s) := by
  intro hn hnw hnr
  have hncl : ∀ oz, ¬ lkClaim lk GD.gdG e oz := fun _ ⟨_, _, _, hw⟩ => hnw _ hw
  exact AxSpinProt.lkBodyStep lk γh R GD s e hn (hnw b0) fun st hh hnz =>
    ⟨AxSpinProt.holdOkInsert lk GD.gdG s st e hncl (hnw b0) hh,
     AxSpinProt.nzInsertNotRead lk GD.gdG s st e hnr hnz⟩

/-! ### 3.3 THE PLAIN-READ RULE (records the read fact) -/

theorem lkBodyRead (lk : Int) (γh : GName) (R : Geid → IProp GF) (GD : Gdexec) (s : GSet Geid)
    (r : Geid) :
    rvwmoCatConsistent GD → WPh GD.gdG s r → r ∉ s → gisW GD.gdG r = false →
    lkBody lk γh R GD s ⊢ lkBody lk γh R GD (({r} : GSet Geid) ∪ s) := by
  intro hcons hwp hn hnw
  have hnwb : ∀ v, ¬ gwritesByte GD.gdG r lk v := fun v hw => by
    have h := WeakRvwmoGraph.gwritesByteGisW _ _ _ _ hw
    rw [hnw] at h
    cases h
  have hncl : ∀ oz, ¬ lkClaim lk GD.gdG r oz := fun _ ⟨_, _, _, hw⟩ => hnwb _ hw
  apply AxSpinProt.lkBodyStep lk γh R GD s r hn (hnwb b0)
  intro st hh hnz
  refine ⟨AxSpinProt.holdOkInsert lk GD.gdG s st r hncl (hnwb b0) hh, ?_⟩
  intro c hst r' hr'
  rcases elemOfUnion.1 hr' with h | h
  · rw [elemOfSingleton.1 h]
    intro _ hpo hnl t v hrd
    subst hst
    exact nzRead lk GD hcons s c r t v hwp hh hpo hnl hrd
  · exact hnz c hst r' h

/-! ### 3.4 THE NEUTRAL RMW (reads `≠ b0`, writes `b1`) -/

theorem lkBodyNeutral (lk : Int) (γh : GName) (R : Geid → IProp GF) (GD : Gdexec)
    (s : GSet Geid) (e : Geid) (t : Nat) (v : BitVec 8) :
    e ∉ s → greadsByte GD.gdG e lk t v → v ≠ b0 → gwritesByte GD.gdG e lk b1 →
    lkBody lk γh R GD s ⊢ lkBody lk γh R GD (({e} : GSet Geid) ∪ s) := by
  intro hn hr hv hw
  have hncl : ∀ oz, ¬ lkClaim lk GD.gdG e oz := fun _ ⟨_, hr', _, _⟩ =>
    hv (greadsByteDet _ _ _ _ _ _ _ hr hr').2
  have hnz0 : ¬ zw lk GD.gdG e := fun hz => b0NeB1 (gwritesByteDet _ _ _ _ _ hz hw)
  have hnrd : ¬ lkread lk GD.gdG e := fun ⟨_, hnw⟩ => by
    have h := WeakRvwmoGraph.gwritesByteGisW _ _ _ _ hw
    rw [hnw] at h
    cases h
  exact AxSpinProt.lkBodyStep lk γh R GD s e hn hnz0 fun st hh hnz =>
    ⟨AxSpinProt.holdOkInsert lk GD.gdG s st e hncl hnz0 hh,
     AxSpinProt.nzInsertNotRead lk GD.gdG s st e hnrd hnz⟩

/-! ### 3.5 THE CLAIM: the lock is free (`holdNoneOfClaim`); the claimer's `notheld` becomes
`locked`; the parked resource (genesis box or the source release's mailbox -- unique by
atomicity) is handed out together with the transport fact. -/

theorem lkBodyClaim (lk : Int) (γh : GName) (R : Geid → IProp GF) (GD : Gdexec) (s : GSet Geid)
    (c : Geid) (oz : Option Geid) :
    rvwmoCatConsistent GD → WC GD.gdG s → WPh GD.gdG s c → c ∉ s → lkClaim lk GD.gdG c oz →
    lkBody lk γh R GD s ∗ ghost_map_elem γh (DFrac.own 1) c.1 (none : Option Geid) ⊢ |==> (
      lkBody lk γh R GD (({c} : GSet Geid) ∪ s) ∗ ghost_map_elem γh (DFrac.own 1) c.1 (some c) ∗
      ∃ z, ⌜z = c ∨ gobCat GD z c⌝ ∗ R z) := by
  intro hcons hwc hwp hn hcl
  unfold lkBody
  iintro ⟨⟨Hg, Hm, %st, %m, Ha, %hp⟩, Hi⟩
  obtain ⟨hh, -, hl1, -⟩ := hp
  have hst := holdNoneOfClaim lk GD hcons s st c oz hwc hwp hn hcl hh
  subst hst
  imod ghost_map_update (some c) $$ Ha Hi with ⟨Ha, Hi⟩
  obtain ⟨t, hr, hw, -⟩ := lkClaimT lk GD hcons c oz hcl
  have hnz0 : ¬ zw lk GD.gdG c := fun hz => b0NeB1 (gwritesByteDet _ _ _ _ _ hz hw)
  have hcmem : c ∈ ({c} : GSet Geid) ∪ s := elemOfUnionL (elemOfSingleton.2 rfl)
  have hpure : holdOk lk GD.gdG (({c} : GSet Geid) ∪ s) (some c) ∧
      NZ lk GD.gdG (({c} : GSet Geid) ∪ s) (some c) ∧ link (insert m c.1 (some c)) (some c) := by
    refine ⟨⟨hcmem, ⟨oz, hcl⟩, ?_, ?_⟩, ?_, ?_, ?_⟩
    · intro w hw' hz hlt
      rcases elemOfUnion.1 hw' with h | h
      · rw [elemOfSingleton.1 h] at hz
        exact hnz0 hz
      · exact hn (hwc w c h (WeakRvwmoGraph.gwritesByteGisW _ _ _ _ hw) hlt)
    · intro c' oz' hc' hne hcl'
      rcases elemOfUnion.1 hc' with h | h
      · exact absurd (elemOfSingleton.1 h) hne
      · obtain ⟨w, hw', hz, hlt⟩ := hh c' oz' h hcl'
        exact ⟨w, elemOfUnionR hw', hz, hlt⟩
    · intro c' hc' r hr'
      cases hc'
      rcases elemOfUnion.1 hr' with h | h
      · rw [elemOfSingleton.1 h]
        intro _ hpo
        exact absurd hpo.2.1 (Nat.lt_irrefl _)
      · intro _ hpo hnl t' v' hrd
        exact nzNewClaim lk GD hcons s c r t' v' hwc h hn hw hpo hnl hrd
    · intro j o hj
      by_cases hji : c.1 = j
      · subst hji
        rw [lookupInsert] at hj
        cases hj
        simp [stFor]
      · rw [lookupInsertNe hji] at hj
        rw [hl1 j o hj]
        simp [stFor, hji]
    · intro c' hc'
      cases hc'
      exact lookupInsert
  cases oz with
  | some z =>
    obtain ⟨hzw, hzc, hco⟩ := lkClaimSrc lk GD hcons c z hcl
    have hzs : z ∈ s := hwp z (WeakRvwmoGraph.gwritesByteGisW _ _ _ _ hzw) hzc
    icases (BigSepS.bigSepS_delete hzs).1 $$ Hm with ⟨Hz, Hm⟩
    iunfold mbox at Hz
    icases Hz with (%hz | Hz)
    · exfalso
      rcases hz with hz | ⟨c', hc', hcl'⟩
      · exact hz hzw
      · exact hn (lkClaimUnique lk GD hcons c' c (some z) hcl' hcl ▸ hc')
    · imodintro
      isplitl [Hg Hm Ha]
      · isplitl [Hg]
        · iapply gboxMono lk GD s (({c} : GSet Geid) ∪ s) R unionSubseteqR
          iexact Hg
        isplitl [Hm]
        · iapply (AxSpinProt.bigSepSUnionSingleton hn).2
          isplitl []
          · ihave H := AxSpinProt.mboxOfNotZw lk GD (({c} : GSet Geid) ∪ s) R c hnz0
            iexact H
          · iapply (BigSepS.bigSepS_delete hzs).2
            isplitl []
            · unfold mbox
              ileft
              ipureintro
              exact Or.inr ⟨c, hcmem, hcl⟩
            · iapply BigSepS.bigSepS_mono
                (fun {w} _ => mboxMono lk GD s (({c} : GSet Geid) ∪ s) R w unionSubseteqR)
              iexact Hm
        · iexists (some c)
          iexists (insert m c.1 (some c))
          isplitl [Ha]
          · iexact Ha
          · ipureintro
            exact hpure
      isplitl [Hi]
      · iexact Hi
      · iexists z
        isplitl []
        · ipureintro
          exact Or.inr (gobCatStep GD z c (Or.inr (Or.inr (Or.inr (Or.inl hco)))))
        · iexact Hz
  | none =>
    iunfold gbox at Hg
    icases Hg with (%hg | Hg)
    · exfalso
      obtain ⟨c', hc', hcl'⟩ := hg
      exact hn (lkClaimUnique lk GD hcons c' c none hcl' hcl ▸ hc')
    · imodintro
      ihave HR := Hg $$ %c
      isplitl [Hm Ha]
      · isplitl []
        · unfold gbox
          ileft
          ipureintro
          exact ⟨c, hcmem, hcl⟩
        isplitl [Hm]
        · iapply (AxSpinProt.bigSepSUnionSingleton hn).2
          isplitl []
          · ihave H := AxSpinProt.mboxOfNotZw lk GD (({c} : GSet Geid) ∪ s) R c hnz0
            iexact H
          · iapply mboxesMono lk GD s (({c} : GSet Geid) ∪ s) R unionSubseteqR
            iexact Hm
        · iexists (some c)
          iexists (insert m c.1 (some c))
          isplitl [Ha]
          · iexact Ha
          · ipureintro
            exact hpure
      isplitl [Hi]
      · iexact Hi
      · iexists c
        isplitl []
        · ipureintro
          exact Or.inl rfl
        · iexact HR

end body

/-- (Lean-only) the holder state a fragment `i ↪ some c` pins through `link`. -/
theorem AxSpinProt.stForSome (st : Option Geid) (i : Nat) (c : Geid) :
    some c = stFor st i → st = some c ∧ c.1 = i := by
  intro h
  cases st with
  | none => cases h
  | some c0 =>
    simp only [stFor] at h
    split at h
    · rename_i hci
      cases h
      exact ⟨rfl, hci⟩
    · cases h

section body2

variable {GF : BundledGFunctors} [SpinlockG GF]

/-! ### 3.6 THE RELEASE: the only arm writing `b0`.  Consumes `locked` (the per-hart fragment
`i ↪ some c` must agree with the holder state: only the CURRENT holder releases); parks `R w`
in `w`'s own mailbox; returns `notheld`. -/

theorem lkBodyRelease (lk : Int) (γh : GName) (R : Geid → IProp GF) (GD : Gdexec)
    (s : GSet Geid) (w : Geid) (i : Nat) (c : Geid) :
    rvwmoCatConsistent GD → WC GD.gdG s → w ∉ s → zw lk GD.gdG w →
    (∀ t v, ¬ greadsByte GD.gdG w lk t v) →
    lkBody lk γh R GD s ∗ ghost_map_elem γh (DFrac.own 1) i (some c) ∗ R w ⊢ |==> (
      lkBody lk γh R GD (({w} : GSet Geid) ∪ s) ∗
      ghost_map_elem γh (DFrac.own 1) i (none : Option Geid) ∗ ⌜c.1 = i⌝) := by
  intro hcons hwc hn hzw hnr
  unfold lkBody
  iintro ⟨⟨Hg, Hm, %st, %m, Ha, %hp⟩, Hi, HR⟩
  obtain ⟨hh, -, hl1, -⟩ := hp
  icombine Ha Hi gives %hmi
  obtain ⟨rfl, hci⟩ := AxSpinProt.stForSome st i c (hl1 i (some c) hmi)
  imod ghost_map_update (none : Option Geid) $$ Ha Hi with ⟨Ha, Hi⟩
  obtain ⟨hc, ⟨oz, hcl⟩, -, hoth⟩ := hh
  obtain ⟨-, -, hwc', -⟩ := lkClaimT lk GD hcons c oz hcl
  have hcw := wcGmoAfter GD hcons s c w lk b1 lk b0 hwc hc hn hwc' hzw
  have hncl : ∀ oz, ¬ lkClaim lk GD.gdG w oz := fun _ ⟨_, hr, _⟩ => hnr _ _ hr
  have hpure : holdOk lk GD.gdG (({w} : GSet Geid) ∪ s) none ∧
      NZ lk GD.gdG (({w} : GSet Geid) ∪ s) none ∧ link (insert m i none) none := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro c' oz' hc' hcl'
      rcases elemOfUnion.1 hc' with h | h
      · rw [elemOfSingleton.1 h] at hcl'
        exact absurd hcl' (hncl oz')
      · by_cases hne : c' = c
        · subst hne
          exact ⟨w, elemOfUnionL (elemOfSingleton.2 rfl), hzw, hcw⟩
        · obtain ⟨w', hw', hz, hlt⟩ := hoth c' oz' h hne hcl'
          exact ⟨w', elemOfUnionR hw', hz, hlt⟩
    · intro c' hst
      cases hst
    · intro j o hj
      by_cases hji : i = j
      · subst hji
        rw [lookupInsert] at hj
        cases hj
        rfl
      · rw [lookupInsertNe hji] at hj
        rw [hl1 j o hj]
        have : c.1 ≠ j := fun h => hji (hci.symm.trans h)
        simp [stFor, this]
    · intro c' hst
      cases hst
  imodintro
  isplitl [Hg Hm HR Ha]
  · isplitl [Hg]
    · iapply gboxMono lk GD s (({w} : GSet Geid) ∪ s) R unionSubseteqR
      iexact Hg
    isplitl [Hm HR]
    · iapply mboxesInsert lk GD s R w hn
      isplitl [Hm]
      · iexact Hm
      · unfold mbox
        iright
        iexact HR
    · iexists none
      iexists (insert m i none)
      isplitl [Ha]
      · iexact Ha
      · ipureintro
        exact hpure
  isplitl [Hi]
  · iexact Hi
  · ipureintro
    exact hci

/-! ### 3.7 THE GATE DELIVERY of the read facts: the holder (`locked`), at ANY later
processing point, learns that every processed plain read of `lk` po-after its claim (no lock
write po-between) read `≠ b0`. -/

theorem lkBodyGateNz (lk : Int) (γh : GName) (R : Geid → IProp GF) (GD : Gdexec)
    (s : GSet Geid) (i : Nat) (c : Geid) :
    lkBody lk γh R GD s ∗ ghost_map_elem γh (DFrac.own 1) i (some c) ⊢
    lkBody lk γh R GD s ∗ ghost_map_elem γh (DFrac.own 1) i (some c) ∗
    ⌜∀ r, r ∈ s → lkread lk GD.gdG r → WeakRvwmoGraph.gpo GD.gdG c r → nolk lk GD.gdG c r →
          ∀ t v, greadsByte GD.gdG r lk t v → v ≠ b0⌝ := by
  unfold lkBody
  iintro ⟨⟨Hg, Hm, %st, %m, Ha, %hp⟩, Hi⟩
  obtain ⟨hh, hnz, hl⟩ := hp
  icombine Ha Hi gives %hmi
  obtain ⟨rfl, -⟩ := AxSpinProt.stForSome st i c (hl.1 i (some c) hmi)
  isplitl [Hg Hm Ha]
  · isplitl [Hg]
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
    exact hnz c rfl

end body2

/-! ## 4. Registration: `isLock`, `notheld`, `locked`, `lkInv` -/

section inv

variable {GF : BundledGFunctors} [SpinlockG GF]

/-- `isLock`: the PERSISTENT registration `lk ↦ (γR, γh)`, `γR` the saved predicate `R`. -/
def isLock (reg : GName) (lk : Int) (R : Geid → IProp GF) : IProp GF :=
  iprop(∃ γR γh, ghost_map_elem reg DFrac.discard lk ((γR, γh) : GName × GName) ∗
    saved_pred_own γR DFrac.discard R)

instance isLockPersistent (reg : GName) (lk : Int) (R : Geid → IProp GF) :
    Persistent (isLock reg lk R) := by
  unfold isLock
  infer_instance

/-- `notheld`/`locked`: the per-(lock,hart) fragment, EXCLUSIVE. -/
def notheld (reg : GName) (lk : Int) (i : Nat) : IProp GF :=
  iprop(∃ γR γh, ghost_map_elem reg DFrac.discard lk ((γR, γh) : GName × GName) ∗
    ghost_map_elem γh (DFrac.own 1) i (none : Option Geid))

def locked (reg : GName) (lk : Int) (i : Nat) (c : Geid) : IProp GF :=
  iprop(∃ γR γh, ghost_map_elem reg DFrac.discard lk ((γR, γh) : GName × GName) ∗
    ghost_map_elem γh (DFrac.own 1) i (some c))

theorem notheldExcl (reg : GName) (lk : Int) (i : Nat) :
    notheld (GF := GF) reg lk i ∗ notheld reg lk i ⊢ False := by
  unfold notheld
  iintro ⟨⟨%γR, %γh, #Hr, Hi⟩, ⟨%γR', %γh', #Hr', Hi'⟩⟩
  ihave %h := ghost_map_elem_agree reg lk _ _ ((γR, γh) : GName × GName) (γR', γh') $$ [$Hr $Hr']
  simp only [Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  ihave %hne := ghost_map_elem_ne γh i i (DFrac.own 1) (none : Option Geid) none $$ Hi Hi'
  exact (hne rfl).elim

theorem lockedNotheld (reg : GName) (lk : Int) (i : Nat) (c : Geid) :
    locked (GF := GF) reg lk i c ∗ notheld reg lk i ⊢ False := by
  unfold locked notheld
  iintro ⟨⟨%γR, %γh, #Hr, Hi⟩, ⟨%γR', %γh', #Hr', Hi'⟩⟩
  ihave %h := ghost_map_elem_agree reg lk _ _ ((γR, γh) : GName × GName) (γR', γh') $$ [$Hr $Hr']
  simp only [Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  ihave %hne := ghost_map_elem_ne γh i i (DFrac.own 1) (some c) none $$ Hi Hi'
  exact (hne rfl).elim

/-- THE COMPONENT of the joint state. -/
def lkInv (reg : GName) (lk : Int) (GD : Gdexec) (s : GSet Geid) : IProp GF :=
  iprop(∃ (γR : GName) (γh : GName) (R : Geid → IProp GF),
    ghost_map_elem reg DFrac.discard lk ((γR, γh) : GName × GName) ∗
    saved_pred_own γR DFrac.discard R ∗ lkBody lk γh R GD s)

theorem lkInvOther (reg : GName) (lk : Int) (GD : Gdexec) (s : GSet Geid) (e : Geid) :
    e ∉ s → (∀ v, ¬ gwritesByte GD.gdG e lk v) → ¬ lkread lk GD.gdG e →
    lkInv (GF := GF) reg lk GD s ⊢ lkInv reg lk GD (({e} : GSet Geid) ∪ s) := by
  intro h1 h2 h3
  unfold lkInv
  iintro ⟨%γR, %γh, %R, #Hr, #Hs, Hb⟩
  iexists γR
  iexists γh
  iexists R
  isplitr [Hb]
  · iexact Hr
  isplitr [Hb]
  · iexact Hs
  · iapply lkBodyOther lk γh R GD s e h1 h2 h3
    iexact Hb

theorem lkInvRead (reg : GName) (lk : Int) (GD : Gdexec) (s : GSet Geid) (r : Geid) :
    rvwmoCatConsistent GD → WPh GD.gdG s r → r ∉ s → gisW GD.gdG r = false →
    lkInv (GF := GF) reg lk GD s ⊢ lkInv reg lk GD (({r} : GSet Geid) ∪ s) := by
  intro h1 h2 h3 h4
  unfold lkInv
  iintro ⟨%γR, %γh, %R, #Hr, #Hs, Hb⟩
  iexists γR
  iexists γh
  iexists R
  isplitr [Hb]
  · iexact Hr
  isplitr [Hb]
  · iexact Hs
  · iapply lkBodyRead lk γh R GD s r h1 h2 h3 h4
    iexact Hb

theorem lkInvNeutral (reg : GName) (lk : Int) (GD : Gdexec) (s : GSet Geid) (e : Geid) (t : Nat)
    (v : BitVec 8) :
    e ∉ s → greadsByte GD.gdG e lk t v → v ≠ b0 → gwritesByte GD.gdG e lk b1 →
    lkInv (GF := GF) reg lk GD s ⊢ lkInv reg lk GD (({e} : GSet Geid) ∪ s) := by
  intro h1 h2 h3 h4
  unfold lkInv
  iintro ⟨%γR, %γh, %R, #Hr, #Hs, Hb⟩
  iexists γR
  iexists γh
  iexists R
  isplitr [Hb]
  · iexact Hr
  isplitr [Hb]
  · iexact Hs
  · iapply lkBodyNeutral lk γh R GD s e t v h1 h2 h3 h4
    iexact Hb

/-- THE CLAIM RULE, at the registration level: the client's `R'` (from `isLock`) is
transported to the claim `c`. -/
theorem lkInvClaim (reg : GName) (lk : Int) (GD : Gdexec) (s : GSet Geid) (c : Geid)
    (oz : Option Geid) (R' : Geid → IProp GF) :
    rvwmoCatConsistent GD → WC GD.gdG s → WPh GD.gdG s c → c ∉ s →
    lkClaim lk GD.gdG c oz → lkTransportable GD R' →
    lkInv reg lk GD s ∗ notheld reg lk c.1 ∗ isLock reg lk R' ⊢ |==>
      ▷ (lkInv reg lk GD (({c} : GSet Geid) ∪ s) ∗ locked reg lk c.1 c ∗ R' c) := by
  intro hcons hwc hwp hn hcl htr
  unfold lkInv notheld isLock locked
  iintro ⟨⟨%γR, %γh, %R, #Hr, #Hs, Hb⟩, ⟨%γR1, %γh1, #Hr1, Hi⟩, ⟨%γR2, %γh2, #Hr2, #Hs2⟩⟩
  ihave %h1 := ghost_map_elem_agree reg lk _ _ ((γR, γh) : GName × GName) (γR1, γh1)
    $$ [$Hr $Hr1]
  ihave %h2 := ghost_map_elem_agree reg lk _ _ ((γR, γh) : GName × GName) (γR2, γh2)
    $$ [$Hr $Hr2]
  simp only [Prod.mk.injEq] at h1 h2
  obtain ⟨rfl, rfl⟩ := h1
  obtain ⟨rfl, rfl⟩ := h2
  imod lkBodyClaim lk γh R GD s c oz hcons hwc hwp hn hcl $$ [$Hb $Hi]
    with ⟨Hb, Hi, %z, %hz, HR⟩
  ihave #Heq := saved_pred_agree γR _ _ R R' z $$ [$Hs $Hs2]
  imodintro
  inext
  ihave #W := AxWp.eqWand (R z) (R' z) $$ Heq
  ihave HR' := W $$ HR
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
  · rcases hz with rfl | hob
    · iexact HR'
    · iapply htr z c hob
      iexact HR'

/-- THE RELEASE RULE, at the registration level. -/
theorem lkInvRelease (reg : GName) (lk : Int) (GD : Gdexec) (s : GSet Geid) (w : Geid) (i : Nat)
    (c : Geid) (R' : Geid → IProp GF) :
    rvwmoCatConsistent GD → WC GD.gdG s → w ∉ s → zw lk GD.gdG w →
    (∀ t v, ¬ greadsByte GD.gdG w lk t v) →
    lkInv reg lk GD s ∗ locked reg lk i c ∗ isLock reg lk R' ∗ R' w ⊢
      ▷ |==> (lkInv reg lk GD (({w} : GSet Geid) ∪ s) ∗ notheld reg lk i ∗ ⌜c.1 = i⌝) := by
  intro hcons hwc hn hzw hnr
  unfold lkInv notheld isLock locked
  iintro ⟨⟨%γR, %γh, %R, #Hr, #Hs, Hb⟩, ⟨%γR1, %γh1, #Hr1, Hi⟩, ⟨%γR2, %γh2, #Hr2, #Hs2⟩, HR⟩
  ihave %h1 := ghost_map_elem_agree reg lk _ _ ((γR, γh) : GName × GName) (γR1, γh1)
    $$ [$Hr $Hr1]
  ihave %h2 := ghost_map_elem_agree reg lk _ _ ((γR, γh) : GName × GName) (γR2, γh2)
    $$ [$Hr $Hr2]
  simp only [Prod.mk.injEq] at h1 h2
  obtain ⟨rfl, rfl⟩ := h1
  obtain ⟨rfl, rfl⟩ := h2
  ihave #Heq := saved_pred_agree γR _ _ R' R w $$ [$Hs2 $Hs]
  inext
  ihave #W := AxWp.eqWand (R' w) (R w) $$ Heq
  ihave HR := W $$ HR
  imod lkBodyRelease lk γh R GD s w i c hcons hwc hn hzw hnr $$ [$Hb $Hi $HR]
    with ⟨Hb, Hi, %hci⟩
  imodintro
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
    exact hci

theorem lkInvGateNz (reg : GName) (lk : Int) (GD : Gdexec) (s : GSet Geid) (i : Nat) (c : Geid) :
    lkInv (GF := GF) reg lk GD s ∗ locked reg lk i c ⊢
    lkInv reg lk GD s ∗ locked reg lk i c ∗
    ⌜∀ r, r ∈ s → lkread lk GD.gdG r → WeakRvwmoGraph.gpo GD.gdG c r → nolk lk GD.gdG c r →
          ∀ t v, greadsByte GD.gdG r lk t v → v ≠ b0⌝ := by
  unfold lkInv locked
  iintro ⟨⟨%γR, %γh, %R, #Hr, #Hs, Hb⟩, ⟨%γR1, %γh1, #Hr1, Hi⟩⟩
  ihave %h1 := ghost_map_elem_agree reg lk _ _ ((γR, γh) : GName × GName) (γR1, γh1)
    $$ [$Hr $Hr1]
  simp only [Prod.mk.injEq] at h1
  obtain ⟨rfl, rfl⟩ := h1
  icases lkBodyGateNz lk γh R GD s i c $$ [$Hb $Hi] with ⟨Hb, Hi, %H⟩
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

end inv

section alloc

variable {GF : BundledGFunctors} [SpinlockG GF]

theorem allocHarts (γ : GName) (harts : List Nat) :
    harts.Nodup →
    ghost_map_auth γ (DFrac.own 1) (∅ : GMapF Nat (Option Geid)) ⊢@{IProp GF} |==>
      ∃ m : GMapF Nat (Option Geid), ghost_map_auth γ (DFrac.own 1) m ∗
        ([∗list] i ∈ harts, ghost_map_elem γ (DFrac.own 1) i (none : Option Geid)) ∗
        ⌜(∀ j o, get? m j = some o → o = none) ∧
          (∀ j, j ∈ (FiniteMap.dom_set m : GSet Nat) ↔ j ∈ harts)⌝ := by
  induction harts with
  | nil =>
    intro _
    iintro Ha
    imodintro
    iexists (∅ : GMapF Nat (Option Geid))
    isplitl [Ha]
    · iexact Ha
    isplitl []
    · iapply BigSepL.bigSepL_nil_intro (P := (emp : IProp GF))
      iempintro
    · ipureintro
      refine ⟨fun j o h => ?_, fun j => ?_⟩
      · rw [lookupEmpty] at h
        cases h
      · rw [elemOfDom, lookupEmpty]
        simp
  | cons i hs ih =>
    intro hnd
    obtain ⟨hi, hnd'⟩ := List.nodup_cons.1 hnd
    iintro Ha
    imod ih hnd' $$ Ha with ⟨%m, Ha, Hs, %hm⟩
    obtain ⟨hm1, hm2⟩ := hm
    have him : get? m i = none := by
      cases h : get? m i with
      | none => rfl
      | some o =>
        exfalso
        apply hi
        apply (hm2 i).1
        rw [elemOfDom, h]
        rfl
    imod ghost_map_insert i (none : Option Geid) him $$ Ha with ⟨Ha, Hi⟩
    imodintro
    iexists (insert m i (none : Option Geid))
    isplitl [Ha]
    · iexact Ha
    isplitl [Hi Hs]
    · iapply BigSepL.bigSepL_cons.2
      isplitl [Hi]
      · iexact Hi
      · iexact Hs
    · ipureintro
      constructor
      · intro j o h
        by_cases hji : i = j
        · subst hji
          rw [lookupInsert] at h
          cases h
          rfl
        · rw [lookupInsertNe hji] at h
          exact hm1 j o h
      · intro j
        rw [elemOfDom]
        by_cases hji : i = j
        · subst hji
          rw [lookupInsert]
          simp
        · rw [lookupInsertNe hji, ← elemOfDom (S := GSet Nat), hm2 j]
          simp only [List.mem_cons]
          constructor
          · exact Or.inr
          · rintro (h | h)
            · exact absurd h.symm hji
            · exact h

/-- GENESIS: the component at `s = ∅`, the genesis box holding `∀ e, R e` (R initially parked
in σ0), every hart `notheld`. -/
theorem lkInvAlloc (lk : Int) (GD : Gdexec) (harts : List Nat) (R : Geid → IProp GF) :
    harts.Nodup →
    (∀ e, R e) ⊢ |==> ∃ reg, lkInv reg lk GD ∅ ∗ isLock reg lk R ∗
      [∗list] i ∈ harts, notheld reg lk i := by
  intro hnd
  iintro HR
  imod saved_pred_alloc R DFrac.discard DFrac.valid_discard with ⟨%γR, #HsR⟩
  imod ghost_map_alloc_empty (GF := GF) (K := Nat) (V := Option Geid) with ⟨%γh, Ha⟩
  imod allocHarts γh harts hnd $$ Ha with ⟨%m, Ha, Hhs, %hm⟩
  obtain ⟨hm1, -⟩ := hm
  imod ghost_map_alloc_empty (GF := GF) (K := Int) (V := GName × GName) with ⟨%reg, Hreg⟩
  imod ghost_map_insert_persist lk ((γR, γh) : GName × GName) lookupEmpty $$ Hreg with ⟨-, #Hr⟩
  imodintro
  iexists reg
  isplitl [HR Ha]
  · unfold lkInv
    iexists γR
    iexists γh
    iexists R
    isplitr [HR Ha]
    · iexact Hr
    isplitr [HR Ha]
    · iexact HsR
    · unfold lkBody gbox
      isplitl [HR]
      · iright
        iexact HR
      isplitl []
      · iapply BigSepS.bigSepS_empty_intro (P := (emp : IProp GF))
        iempintro
      · iexists (none : Option Geid)
        iexists m
        isplitl [Ha]
        · iexact Ha
        · ipureintro
          refine ⟨fun c oz hc => absurd hc notElemOfEmpty, ⟨(fun c hc => nomatch hc), ⟨?_, ?_⟩⟩⟩
          · intro j o h
            rw [hm1 j o h]
            rfl
          · intro c hc
            cases hc
  isplitl []
  · unfold isLock
    iexists γR
    iexists γh
    isplitl []
    · iexact Hr
    · iexact HsR
  · iapply BigSepL.bigSepL_impl (Ψ := fun _ i => notheld (GF := GF) reg lk i) $$ Hhs
    imodintro
    iintro %k %i %hk Hi
    unfold notheld
    iexists γR
    iexists γh
    isplitr [Hi]
    · iexact Hr
    · iexact Hi

end alloc

/-! ## 5. The Own-class component (owned bytes `X`, per-byte histories) -- `AxProt.prot_inv`
RESTRICTED to the owned addresses (the joint state cannot use `prot_inv` itself: it demands a
history snapshot for EVERY write, lock-word writes included). -/

section own

variable {GF : BundledGFunctors} [AxlogG GF Hent]

def Φx (X : GSet Int) (γ : GName) (GD : Gdexec) (e : Geid) : IProp GF :=
  iprop(∀ a v, ⌜a ∈ X⌝ → ⌜gwritesByte GD.gdG e a v⌝ →
    ∃ H, histSnap γ a H ∗ ⌜H.getLast? = some (e, v)⌝)

instance ΦxPersistent (X : GSet Int) (γ : GName) (GD : Gdexec) (e : Geid) :
    Persistent (Φx (GF := GF) X γ GD e) := by
  unfold Φx
  infer_instance

def ownInv (X : GSet Int) (γ : GName) (GD : Gdexec) (s : GSet Geid) : IProp GF :=
  iprop([∗set] e ∈ s, Φx X γ GD e)

instance ownInvPersistent (X : GSet Int) (γ : GName) (GD : Gdexec) (s : GSet Geid) :
    Persistent (ownInv (GF := GF) X γ GD s) := by
  unfold ownInv
  infer_instance

theorem ownInvOther (X : GSet Int) (γ : GName) (GD : Gdexec) (s : GSet Geid) (e : Geid) :
    e ∉ s → (∀ a v, a ∈ X → ¬ gwritesByte GD.gdG e a v) →
    ownInv (GF := GF) X γ GD s ⊢ ownInv X γ GD (({e} : GSet Geid) ∪ s) := by
  intro hn hnw
  unfold ownInv
  iintro Hs
  iapply (AxSpinProt.bigSepSUnionSingleton hn).2
  isplitr [Hs]
  · unfold Φx
    iintro %a %v %ha %hw
    exact (hnw a v ha hw).elim
  · iexact Hs

theorem ownInvWrite (X : GSet Int) (γ : GName) (GD : Gdexec) (s : GSet Geid) (e : Geid) (x : Int)
    (v : BitVec 8) (H : List Hent) :
    e ∉ s → x ∈ X → gwritesByte GD.gdG e x v →
    (∀ a' v', gwritesByte GD.gdG e a' v' → a' = x) →
    ownInv (GF := GF) X γ GD s ∗ histAuth γ x 1 H ⊢ |==> (
      ownInv X γ GD (({e} : GSet Geid) ∪ s) ∗ histAuth γ x 1 (H ++ [(e, v)])) := by
  intro hn hx hw hs
  iintro ⟨Hinv, Ha⟩
  imod histAppend γ x H (e, v) $$ Ha with Ha
  ihave #Hsn := histSnapGet γ x 1 (H ++ [(e, v)]) $$ Ha
  imodintro
  isplitr [Ha]
  · unfold ownInv
    iapply (AxSpinProt.bigSepSUnionSingleton hn).2
    isplitr [Hinv]
    · unfold Φx
      iintro %a %v' %_ %hw'
      obtain rfl := hs a v' hw'
      obtain rfl := gwritesByteDet _ _ _ _ _ hw' hw
      iexists (H ++ [(e, v')])
      isplitl []
      · iexact Hsn
      · ipureintro
        simp
    · iexact Hinv
  · iexact Ha

theorem ownInvCov (X : GSet Int) (γ : GName) (GD : Gdexec) (s : GSet Geid) (x : Int) (w : Geid)
    (v : BitVec 8) :
    x ∈ X → gwritesByte GD.gdG w x v → w ∈ s →
    ownInv (GF := GF) X γ GD s ⊢ ∃ H', ⌜w ∈ H'.map Prod.fst⌝ ∗ histSnap γ x H' := by
  intro hx hw hs
  unfold ownInv
  iintro #Hinv
  ihave Hw := BigSepS.bigSepS_elem_of hs $$ Hinv
  iunfold Φx at Hw
  ihave Hw2 := Hw $$ %x %v %hx %hw
  icases Hw2 with ⟨%H, Hsn, %hl⟩
  iexists H
  isplitl []
  · ipureintro
    exact histSnapLastIn H w v hl
  · iexact Hsn

end own

/-! ## 6. A client predicate: an OWNED byte `x` whose locked history only ever writes `b1` (the
certificates' `R`).  `Rx e` holds the full history auth of `x`, tied at `e` (or still the
genesis `[]`). -/

theorem AxSpinProt.chainWithSnoc' (R : Geid → Geid → Prop) (Hl0 : List Geid) (wl : Geid)
    (Hch0 : chainWith R Hl0) (Hlink : ∀ wlast, Hl0.getLast? = some wlast → R wlast wl) :
    chainWith R (Hl0 ++ [wl]) := by
  intro i w1 w2 h1 h2
  by_cases hlt : i + 1 < Hl0.length
  · rw [List.getElem?_append_left (by omega)] at h1
    rw [List.getElem?_append_left hlt] at h2
    exact Hch0 i w1 w2 h1 h2
  · have hlen := lookup_lt_Some h2
    simp only [List.length_append, List.length_singleton] at hlen
    have hi : i + 1 = Hl0.length := by omega
    rw [List.getElem?_append_right (by omega), hi, Nat.sub_self] at h2
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h2
    subst h2
    rw [List.getElem?_append_left (by omega)] at h1
    apply Hlink
    rw [List.getLast?_eq_getElem?]
    have he : Hl0.length - 1 = i := by omega
    rw [he]
    exact h1

def hwf (x : Int) (GD : Gdexec) (H : List Hent) : Prop :=
  (∀ p, p ∈ H → gwritesByte GD.gdG p.1 x p.2) ∧ chainWith (gmoLt GD.gdG) (H.map Prod.fst)

section client

variable {GF : BundledGFunctors} [AxlogG GF Hent]

def Rx (γ : GName) (x : Int) (GD : Gdexec) (e : Geid) : IProp GF :=
  iprop(∃ H, histAuth γ x 1 H ∗
    ⌜(H = [] ∨ tieBase GD.gdG (H.map Prod.fst) e) ∧ hwf x GD H ∧ ∀ p, p ∈ H → p.2 = b1⌝)

theorem RxTransportable (γ : GName) (x : Int) (GD : Gdexec) :
    rvwmoCatConsistent GD → lkTransportable GD (Rx (GF := GF) γ x GD) := by
  intro hcons e e' hob
  unfold Rx
  iintro ⟨%H, Ha, %hp⟩
  obtain ⟨ht, hw, hf⟩ := hp
  iexists H
  isplitl [Ha]
  · iexact Ha
  · ipureintro
    refine ⟨?_, hw, hf⟩
    rcases ht with h | h
    · exact Or.inl h
    · exact Or.inr (tieLob _ _ e e' h (obCatSubGmo GD e e' hcons hob))

theorem hwfNil (x : Int) (GD : Gdexec) : hwf x GD [] :=
  ⟨fun _ hp => absurd hp List.not_mem_nil, fun _ _ _ hk => by simp at hk⟩

/-- Genesis: the raw empty history is `R` at EVERY event. -/
theorem RxGenesis (γ : GName) (x : Int) (GD : Gdexec) :
    histAuth (GF := GF) γ x 1 [] ⊢ ∀ e, Rx γ x GD e := by
  iintro Ha %e
  unfold Rx
  iexists ([] : List Hent)
  isplitl [Ha]
  · iexact Ha
  · ipureintro
    exact ⟨Or.inl rfl, hwfNil x GD, fun _ hp => absurd hp List.not_mem_nil⟩

/-- (Lean-only) the coverage wand `ownedReadRule` consumes, off `ownInv {x}` and `WPh`. -/
theorem AxSpinProt.covMo (γ : GName) (x : Int) (GD : Gdexec) (s : GSet Geid) (r : Geid) :
    WPh GD.gdG s r →
    ownInv (GF := GF) ({x} : GSet Int) γ GD s ⊢
      ∀ w v, ⌜gwritesByte GD.gdG w x v⌝ -∗ ⌜gmoLt GD.gdG w r⌝ -∗
        ∃ H', ⌜w ∈ H'.map Prod.fst⌝ ∗ histSnap γ x H' := by
  intro hwp
  iintro #Hinv %w %v %hw %hlt
  iapply ownInvCov ({x} : GSet Int) γ GD s x w v (elemOfSingleton.2 rfl) hw
    (hwp w (WeakRvwmoGraph.gwritesByteGisW _ _ _ _ hw) hlt)
  iexact Hinv

/-- (Lean-only) ... and its rfe form, for `lockReadOwnGenesis`. -/
theorem AxSpinProt.covRfe (γ : GName) (x : Int) (GD : Gdexec) (s : GSet Geid) (r : Geid) :
    rvwmoCatConsistent GD → WPh GD.gdG s r →
    ownInv (GF := GF) ({x} : GSet Int) γ GD s ⊢
      ∀ w v, ⌜gwritesByte GD.gdG w x v⌝ -∗ ⌜grfe GD.gdG w r⌝ -∗
        ∃ H', ⌜w ∈ H'.map Prod.fst⌝ ∗ histSnap γ x H' := by
  intro hcons hwp
  iintro #Hinv %w %v %hw %hrfe
  iapply ownInvCov ({x} : GSet Int) γ GD s x w v (elemOfSingleton.2 rfl) hw
    (hwp w (WeakRvwmoGraph.gwritesByteGisW _ _ _ _ hw) (catGrfeGmo GD w r hcons hrfe))
  iexact Hinv

/-- (Lean-only) a full history auth tied at `e` IS the singleton `tokTie` at `e`. -/
theorem AxSpinProt.tokTieSingleton (GD : Gdexec) (γ : GName) (x : Int) (H : List Hent) (e : Geid)
    (ht : tieBase GD.gdG (H.map Prod.fst) e) :
    histAuth (GF := GF) γ x 1 H ⊣⊢ tokTie GD γ x H {[e := (1 : Qp)]} := by
  constructor
  · unfold tokTie
    iintro Ha
    isplitl [Ha]
    · iapply (tokSingleton γ x H e 1).2
      iexact Ha
    · ipureintro
      intro e' he'
      rw [domSingleton, elemOfSingleton] at he'
      subst he'
      exact ht
  · iintro HT
    iapply (tokSingleton γ x H e 1).1
    iapply tokTieTok GD γ x H
    iexact HT

/-- THE OWNED READ of `x` under `Rx e` (`e` gmo-before the read, e.g. the claiming `.aq` RMW):
the value read is `b1` (some locked write) or the image -- and `Rx e` is KEPT (the pure fact is
extracted without spending the token). -/
theorem RxRead (γ : GName) (x : Int) (GD : Gdexec) (s : GSet Geid) (e r : Geid) (t : Nat)
    (v : BitVec 8) :
    rvwmoCatConsistent GD →
    (∀ w v', gwritesByte GD.gdG w x v' → w.1 = r.1 → False) →
    greadsByte GD.gdG r x t v → gmoLt GD.gdG e r → WPh GD.gdG s r →
    ownInv (GF := GF) ({x} : GSet Int) γ GD s ∗ Rx γ x GD e ⊢
      Rx γ x GD e ∗ ⌜v = b1 ∨ GD.gdG.gxImg x = some v⌝ := by
  intro hcons hnpo hrd her hwp
  unfold Rx
  iintro ⟨#Hinv, %H, Ha, %hp⟩
  obtain ⟨ht, hw, hf⟩ := hp
  rcases ht with rfl | ht
  · ihave Hcov := AxSpinProt.covRfe γ x GD s r hcons hwp $$ Hinv
    icases (persistent_entails_left (lockReadOwnGenesis (GF := GF) GD γ x r t v hcons hnpo hrd))
      $$ [$Ha $Hcov] with ⟨⟨Ha, -⟩, %hg⟩
    isplitl [Ha]
    · iexists ([] : List Hent)
      isplitl [Ha]
      · iexact Ha
      · ipureintro
        exact ⟨Or.inl rfl, hwfNil x GD, fun _ hp => absurd hp List.not_mem_nil⟩
    · ipureintro
      exact Or.inr hg.2
  · cases hlast : H.getLast? with
    | none =>
      exfalso
      rw [List.getLast?_eq_none_iff] at hlast
      subst hlast
      rcases ht with h | ⟨_, h, _⟩ <;> simp at h
    | some p =>
      obtain ⟨wl, vl⟩ := p
      obtain ⟨hwr, hch⟩ := hw
      have hown : ∀ w v', gwritesByte GD.gdG w x v' → WeakRvwmoGraph.gpo GD.gdG w r →
          w ∈ H.map Prod.fst := fun w v' hw' hpo => (hnpo w v' hw' hpo.1).elim
      ihave Hcov := AxSpinProt.covMo γ x GD s r hwp $$ Hinv
      ihave HT := (AxSpinProt.tokTieSingleton GD γ x H e ht).1 $$ Ha
      icases (persistent_entails_left (ownedReadRule (GF := GF) GD x r γ H {[e := (1 : Qp)]} wl vl
          hcons hwr hch hown hlast ⟨t, v, hrd⟩
          (Or.inl ⟨e, by rw [domSingleton, elemOfSingleton], her⟩)))
        $$ [$HT $Hcov] with ⟨⟨HT, -⟩, %hv⟩
      ihave Ha := (AxSpinProt.tokTieSingleton GD γ x H e ht).2 $$ HT
      isplitl [Ha]
      · iexists H
        isplitl [Ha]
        · iexact Ha
        · ipureintro
          exact ⟨Or.inr ht, ⟨hwr, hch⟩, hf⟩
      · ipureintro
        left
        rw [hv.2 t v hrd]
        obtain ⟨H0, hH⟩ := List.getLast?_eq_some_iff.mp hlast
        exact hf (wl, vl) (by rw [hH]; simp)

/-- THE OWNED WRITE of `b1` to `x` under `Rx a` (`a` gmo-before `w`): appends, re-ties at `w`. -/
theorem RxWrite (γ : GName) (x : Int) (GD : Gdexec) (s : GSet Geid) (a w : Geid) :
    w ∉ s → gmoLt GD.gdG a w → gwritesByte GD.gdG w x b1 →
    (∀ a' v', gwritesByte GD.gdG w a' v' → a' = x) →
    ownInv (GF := GF) ({x} : GSet Int) γ GD s ∗ Rx γ x GD a ⊢ |==> (
      ownInv ({x} : GSet Int) γ GD (({w} : GSet Geid) ∪ s) ∗ Rx γ x GD w) := by
  intro hn haw hw hsg
  unfold Rx
  iintro ⟨Hinv, %H, Ha, %hp⟩
  obtain ⟨ht, ⟨hwr, hch⟩, hf⟩ := hp
  imod ownInvWrite ({x} : GSet Int) γ GD s w x b1 H hn (elemOfSingleton.2 rfl) hw hsg
    $$ [$Hinv $Ha] with ⟨Hinv, Ha⟩
  imodintro
  isplitl [Hinv]
  · iexact Hinv
  · iexists (H ++ [(w, b1)])
    isplitl [Ha]
    · iexact Ha
    · ipureintro
      refine ⟨Or.inr (tieWrite GD.gdG H w b1), ⟨?_, ?_⟩, ?_⟩
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
          exact haw
        · rw [ht] at hl
          cases hl
          exact gmoLtTrans _ _ _ _ hlt haw
      · intro p hp
        rcases List.mem_append.1 hp with h | h
        · exact hf p h
        · simp only [List.mem_singleton] at h
          subst h
          rfl

end client

end Weak
