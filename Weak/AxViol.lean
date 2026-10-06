/-
Weak: **K1 (challenge C10): the GRAPH restatement of the SC-robustness
violation, its refutation from an ownership timeline, and satisfiability
witnesses** (AxSL tier).

Rocq: `iris/AxViol.v` @ xxvzwolszwmp.

The Rocq header, in substance (design: `weak-memory-lb-axsl.md` §0, K1).  PURE
(no Iris), a leaf.

THE ORIGINAL (`WeakRobust.violation_hart`): at a reachable promise-free
configuration a plain-class (`SCowned`) message of hart `i` at log position
`p`, not yet published (no later same-author `WCrel` message), touching byte
`a`, and a FOREIGN hart `j ≠ i` whose `coh` floor for `a` has reached `p + 1`.
On a promise-free run the floor is raised only by `j`'s own accesses, so for a
message writing `a` this is "`j` read `a` at some `t ≥ p + 1` or wrote `a` at
some `t > p + 1`" — the two arms of `gobsViol`.

THE MAPPING (`gviolationHart nh G`): message ↦ a write event `w ∈ gxGmo` with
write index `gwix G w`; author ↦ `tidHart nh (some w.1)`; plain class ↦
`glblIs G w lbPlain`; byte ↦ `gwritesByte G w a vw`; foreign hart ↦ an event
`e` with `e.1 ≠ w.1`; the floor ↦ `gobsViol`; "not published at `c`" ↦ no
release-class write `h` of `w`'s hart with `w ≤gmo h` gmo-BEFORE the
observation (`gpubBefore`).  The run order of a pf run is gmo except for a
store-FORWARDED read, so the read arm also asks that no publication precede
the read's SOURCE write.  Publication is `WCrel` CLASS + gmo position, not an
ob path (the operational original).

THE REFUTATION.  `AxProt.prot_inv` never looks at the store class, so
`¬ gviolationHart` is not a consequence of it alone.  What is needed is an
ownership TIMELINE `own a k` (the holder of byte `a`'s token just before the
gmo-`k`th event) with (access) a hart access to an Own-class byte happens while
that hart holds the token and (drop) a hart loses a token only AT one of its
own release-class writes (`gtlOk`).  `ownedNoViolation`: `gwf` + `gloadValue` +
`gtlOk` ⇒ `¬ gviolationHart` (when every plain hart write targets an Own-class
byte), by induction along the timeline plus the forwarding case analysis.

NON-VACUITY: `gviolationSat` (a cat-consistent 2-hart racy graph on which the
violation HOLDS); `mpTlSat` (a cat-consistent message-passing graph with a
foreign read of a plain write on which EVERY premise of `ownedNoViolationCat`
is discharged); `viol2NoTl` (the racy graph admits no timeline).

WHAT IS MISSING (K1 residual): `adequacyViolFreeOfTl` reduces the
adequacy-level shape `adequacyViolFreeStmt` to timeline extraction
(`tlExtraction`); extracting the timeline from per-hart WPds needs token-holder
uniqueness and a new protocol clause (token-carrying annotations deposited
only at `WCrel` writes).  The srvwmo SUBSUMPTION corollary is not here.

FETCHES (owner decision D1): a fetch is a graph `LLoad` read like any other;
nothing in this file distinguishes it.

**Deviations from Rocq.**

1. NAMES: lowerCamelCase as `Weak/WeakMem.lean` deviation 1.  The duplicated
   Rocq name (`notes/weak-port-dupnames.json`) `mp` is FILE-QUALIFIED
   (`AxViol.mp`); the dependencies' duplicates are referred to qualified
   (`WeakRvwmoGraph.gwritesByteGisW`, `WeakRvwmoGraph.gwixPos`,
   `WeakRvwmoGraph.gpo`).
2. VOCABULARY: as `WeakRvwmoGraph` deviation 2 (`l !! i` ↦ `l[i]?`, `S n` ↦
   `n + 1`, `Z` ↦ `Int`, `bool_decide` ↦ `decide`, `gx_gmo G` ↦ `G.gxGmo`,
   `gd_g` ↦ `Gdexec.gdG`); `agent` ↦ `Nat` (Rocq's `agent := nat`);
   `(k <? 2)%nat` ↦ `if k < 2`.
3. The closed `vm_compute` side conditions are `decide +kernel` (or `rfl`).
4. ONE HELPER with no Rocq twin: `axViolGlblIsProg` (a label satisfying a
   classifier sits in some program row), used by `viol2NoRel` in place of
   Rocq's `destruct h as [[|[|i]] [|k]]; vm_compute` enumeration.

**Name map** (Rocq → Lean): `lb_plain` ↦ `lbPlain`; `lb_relw` ↦ `lbRelw`;
`gpub_before` ↦ `gpubBefore`; `gobs_viol` ↦ `gobsViol`; `gviolation_hart_on` ↦
`gviolationHartOn`; `gviolation_hart` ↦ `gviolationHart`; `gdviolation_hart` ↦
`gdviolationHart`; `gtl_ok` ↦ `gtlOk`; `tl_drop_between` ↦ `tlDropBetween`;
`tl_pub` ↦ `tlPub`; `owned_no_violation_on` ↦ `ownedNoViolationOn`;
`owned_no_violation` ↦ `ownedNoViolation`; `owned_no_violation_cat` ↦
`ownedNoViolationCat`; `adequacy_viol_free_stmt` ↦ `adequacyViolFreeStmt`;
`tl_extraction` ↦ `tlExtraction`; `adequacy_viol_free_of_tl` ↦
`adequacyViolFreeOfTl`; `vimg`; `viol2`; `viol2_cat` ↦ `viol2Cat`;
`viol2_no_rel` ↦ `viol2NoRel`; `gviolation_sat` ↦ `gviolationSat`; `mp` ↦
`AxViol.mp`; `mp_cat` ↦ `mpCat`; `own_mp` ↦ `ownMp`; `mp_tl` ↦ `mpTl`;
`mp_tl_sat` ↦ `mpTlSat`; `mp_no_violation` ↦ `mpNoViolation`; `viol2_no_tl` ↦
`viol2NoTl`.

**Not ported:** nothing.
-/
import Weak.AxGraphCat
import Weak.AxGraphDec

namespace Weak

open MachCSL MachCSL.Stdpp
open Lbl

/-! # 1. The definition -/

/-- The class classifiers on labels (`SCowned` = `WCplain`; publication =
`WCrel`, `WeakMem.wpublished`). -/
def lbPlain (l : Lbl) : Bool :=
  lbIsW l && decide (lbCls l = .WCplain)

def lbRelw (l : Lbl) : Bool :=
  lbIsW l && decide (lbCls l = .WCrel)

/-- A publication of `w` by its own hart, gmo-before `e`. -/
def gpubBefore (G : Gexec) (w e : Geid) : Prop :=
  ∃ h : Geid, h.1 = w.1 ∧ glblIs G h lbRelw ∧ (h = w ∨ gmoLt G w h) ∧
    gmoLt G h e

/-- Event `e` raises its hart's floor for `a` to `≥ gwix w` before any
publication of `w` (see the header for the forwarding clause). -/
def gobsViol (G : Gexec) (w e : Geid) (a : Int) : Prop :=
  (∃ v, gwritesByte G e a v ∧ gwix G w < gwix G e ∧ ¬ gpubBefore G w e) ∨
  (∃ t v, greadsByte G e a t v ∧ gwix G w ≤ t ∧ ¬ gpubBefore G w e ∧
    ∀ ws, gwriteAt G t = some ws → ¬ gpubBefore G w ws)

/-- THE GRAPH VIOLATION, restricted to Own-class bytes `OC`. -/
def gviolationHartOn (OC : Int → Prop) (nh : Nat) (G : Gexec) : Prop :=
  ∃ w e a vw,
    w ∈ G.gxGmo ∧ gwritesByte G w a vw ∧ glblIs G w lbPlain ∧ OC a ∧
    tidHart nh (some w.1) ∧ tidHart nh (some e.1) ∧ e.1 ≠ w.1 ∧
    gobsViol G w e a

/-- THE GRAPH VIOLATION (`WeakRobust.violation_hart`'s restatement). -/
def gviolationHart (nh : Nat) (G : Gexec) : Prop :=
  gviolationHartOn (fun _ => True) nh G

/-- Over the dependency-carrying graph. -/
def gdviolationHart (nh : Nat) (GD : Gdexec) : Prop :=
  gviolationHart nh GD.gdG

/-! # 2. The refutation from an ownership timeline -/

/-- `own a k`: the unique holder of byte `a`'s token just before the gmo-`k`th
memory event is validated.  (access) and (drop), see the header. -/
def gtlOk (OC : Int → Prop) (nh : Nat) (G : Gexec) (own : Int → Nat → Option Nat) : Prop :=
  (∀ e a, tidHart nh (some e.1) → e ∈ G.gxGmo → OC a → gaccesses G e a →
     own a (gpos G e) = some e.1) ∧
  (∀ a k i, tidHart nh (some i) → own a k = some i → own a (k + 1) ≠ some i →
     ∃ h, G.gxGmo[k]? = some h ∧ h.1 = i ∧ glblIs G h lbRelw)

/-- Along the timeline: a hart that holds `a` at `k` and does not at
`k + (n + 1)` dropped it at a release write in between. -/
theorem tlDropBetween (OC : Int → Prop) (nh : Nat) (G : Gexec)
    (own : Int → Nat → Option Nat) (a : Int) (i j : Nat) :
    gtlOk OC nh G own → tidHart nh (some i) → j ≠ i →
    ∀ n k, own a k = some i → own a (k + (n + 1)) = some j →
    ∃ m h, k ≤ m ∧ m < k + (n + 1) ∧ G.gxGmo[m]? = some h ∧
      h.1 = i ∧ glblIs G h lbRelw := by
  rintro ⟨_, hdrop⟩ hi hji n
  induction n with
  | zero =>
    intro k hk hk'
    have hk1 : own a (k + 1) = some j := hk'
    obtain ⟨h, hh, hh1, hrel⟩ := hdrop a k i hi hk (by
      rw [hk1]; intro he; exact hji (Option.some.inj he))
    exact ⟨k, h, Nat.le_refl _, by omega, hh, hh1, hrel⟩
  | succ n ih =>
    intro k hk hk'
    by_cases hS : own a (k + 1) = some i
    · obtain ⟨m, h, h1, h2, h3, h4, h5⟩ := ih (k + 1) hS (by
        rw [show k + 1 + (n + 1) = k + (n + 1 + 1) by omega]; exact hk')
      exact ⟨m, h, by omega, by omega, h3, h4, h5⟩
    · obtain ⟨h, hh, hh1, hrel⟩ := hdrop a k i hi hk hS
      exact ⟨k, h, Nat.le_refl _, by omega, hh, hh1, hrel⟩

/-- THE KEY STEP: a foreign hart accessing an Own-class byte gmo-at-or-after
the owner's access sees a publication of the owner's hart in between. -/
theorem tlPub (OC : Int → Prop) (nh : Nat) (G : Gexec) (own : Int → Nat → Option Nat)
    (w x : Geid) (a : Int) :
    gwf G → gtlOk OC nh G own →
    w ∈ G.gxGmo → gaccesses G w a → OC a → tidHart nh (some w.1) →
    x ∈ G.gxGmo → gaccesses G x a → tidHart nh (some x.1) → x.1 ≠ w.1 →
    gpos G w ≤ gpos G x → gpubBefore G w x := by
  intro hwf htl hw hwa hOC hi hx hxa hj hne hle
  have hnd := hwf.1
  have hownw := htl.1 w a hi hw hOC hwa
  have hownx := htl.1 x a hj hx hOC hxa
  have hlt : gpos G w < gpos G x := by
    by_cases heq : gpos G w = gpos G x
    · rw [heq, hownx] at hownw
      exact absurd (Option.some.inj hownw) hne
    · omega
  obtain ⟨m, h, hm1, hm2, hh, hh1, hrel⟩ :=
    tlDropBetween OC nh G own a w.1 x.1 htl hi hne (gpos G x - gpos G w - 1) (gpos G w)
      hownw (by rw [show gpos G w + (gpos G x - gpos G w - 1 + 1) = gpos G x by omega]
                exact hownx)
  have hhin : h ∈ G.gxGmo := elem_of_list_lookup_2 hh
  have hph := gposOfLookup G m h hnd hh
  refine ⟨h, hh1, hrel, ?_, hhin, hx, by omega⟩
  by_cases hm : m = gpos G w
  · exact .inl (gposInj G h w hnd hhin hw (by omega))
  · exact .inr ⟨hw, hhin, by omega⟩

/-- THE REFUTATION, byte-restricted form. -/
theorem ownedNoViolationOn (OC : Int → Prop) (nh : Nat) (G : Gexec)
    (own : Int → Nat → Option Nat) :
    gwf G → gloadValue G → gtlOk OC nh G own → ¬ gviolationHartOn OC nh G := by
  rintro hwf hlv htl ⟨w, e, a, vw, hwg, hwb, _, hOC, hi, hj, hne, hobs⟩
  have hnd := hwf.1
  have hww : w ∈ gwrites G :=
    (gwritesElemOf G w).2 ⟨hwg, WeakRvwmoGraph.gwritesByteGisW G w a vw hwb⟩
  have hwa : gaccesses G w a := .inl ⟨vw, hwb⟩
  rcases hobs with ⟨v, heb, hlt, hnp⟩ | ⟨t, v, hrb, hle, hnp, hnps⟩
  · have hew : e ∈ gwrites G := gwixElem G e (by omega)
    have heg := ((gwritesElemOf G e).1 hew).1
    have hlt' := (gwixGposLt G w e hnd hww hew).1 hlt
    exact hnp (tlPub OC nh G own w e a hwf htl hwg hwa hOC hi heg (.inl ⟨v, heb⟩) hj hne
      (by omega))
  · have hsrc := (hlv e a t v hrb).1
    have hwpos := WeakRvwmoGraph.gwixPos G w hww
    cases t with
    | zero => omega
    | succ t' =>
      obtain ⟨ws, hwsat, hwsb, hvis⟩ := hsrc
      have hwsat' : (gwrites G)[t']? = some ws := hwsat
      have hwsw : ws ∈ gwrites G := elem_of_list_lookup_2 hwsat'
      have hwsg := ((gwritesElemOf G ws).1 hwsw).1
      have hixs := gwixOfLookup G t' ws hnd hwsat'
      have hpws : gpos G w ≤ gpos G ws := by
        by_cases heq : gwix G w = gwix G ws
        · rw [gwixInj G w ws hnd hww hwsw heq]; exact Nat.le_refl _
        · exact Nat.le_of_lt ((gwixGposLt G w ws hnd hww hwsw).1 (by omega))
      rcases hvis with ⟨_, heg, hpe⟩ | ⟨hsame, _⟩
      · exact hnp (tlPub OC nh G own w e a hwf htl hwg hwa hOC hi heg
          (.inr ⟨t' + 1, v, hrb⟩) hj hne (by omega))
      · exact hnps ws hwsat (tlPub OC nh G own w ws a hwf htl hwg hwa hOC hi hwsg
          (.inl ⟨v, hwsb⟩) (by rw [hsame]; exact hj) (by rw [hsame]; exact hne) hpws)

/-- THE REFUTATION: when every plain hart write targets an Own-class byte. -/
theorem ownedNoViolation (OC : Int → Prop) (nh : Nat) (G : Gexec)
    (own : Int → Nat → Option Nat) :
    gwf G → gloadValue G → gtlOk OC nh G own →
    (∀ w a v, w ∈ G.gxGmo → tidHart nh (some w.1) → glblIs G w lbPlain →
       gwritesByte G w a v → OC a) →
    ¬ gviolationHart nh G := by
  rintro hwf hlv htl hplain ⟨w, e, a, vw, hwg, hwb, hpl, _, hi, hj, hne, hobs⟩
  exact ownedNoViolationOn OC nh G own hwf hlv htl
    ⟨w, e, a, vw, hwg, hwb, hpl, hplain w a vw hwg hi hpl hwb, hi, hj, hne, hobs⟩

/-- At the cat model. -/
theorem ownedNoViolationCat (OC : Int → Prop) (nh : Nat) (GD : Gdexec)
    (own : Int → Nat → Option Nat) :
    rvwmoCatConsistent GD → gtlOk OC nh GD.gdG own →
    (∀ w a v, w ∈ GD.gdG.gxGmo → tidHart nh (some w.1) →
       glblIs GD.gdG w lbPlain → gwritesByte GD.gdG w a v → OC a) →
    ¬ gdviolationHart nh GD := by
  rintro ⟨hwf, _, hlv, _⟩ htl hplain
  exact ownedNoViolation OC nh GD.gdG own hwf hlv htl hplain

/-- THE ADEQUACY-LEVEL SHAPE and its reduction to timeline extraction — the
residual K1 obligation. -/
def adequacyViolFreeStmt (nh : Nat) (Verified : Gdexec → Prop) : Prop :=
  ∀ GD, rvwmoCatConsistent GD → Verified GD → ¬ gdviolationHart nh GD

def tlExtraction (nh : Nat) (Verified : Gdexec → Prop) : Prop :=
  ∀ GD, rvwmoCatConsistent GD → Verified GD →
    ∃ (OC : Int → Prop) (own : Int → Nat → Option Nat), gtlOk OC nh GD.gdG own ∧
      (∀ w a v, w ∈ GD.gdG.gxGmo → tidHart nh (some w.1) →
         glblIs GD.gdG w lbPlain → gwritesByte GD.gdG w a v → OC a)

theorem adequacyViolFreeOfTl (nh : Nat) (Verified : Gdexec → Prop) :
    tlExtraction nh Verified → adequacyViolFreeStmt nh Verified := by
  intro hext GD hcons hver
  obtain ⟨OC, own, htl, hplain⟩ := hext GD hcons hver
  exact ownedNoViolationCat OC nh GD own hcons htl hplain

/-! # 3. Satisfiability: a racy 2-hart graph on which it HOLDS -/

/-- The all-zero image. -/
def vimg : Image := fun _ => some b0

/-- H0: W x=1 plain (0,0).   H1: R x (1,0) reads it (ts 1).
gmo = [W0x; R1x]. -/
def viol2 : Gdexec :=
  ⟨⟨vimg, [[LStore false 0 [b1] .WCplain],
           [LLoad false 0 [1] [b1]]],
    [(0, 0), (1, 0)]⟩, []⟩

theorem viol2Cat : rvwmoCatConsistent viol2 :=
  catConsistentBSound _ (by decide +kernel)

/-- (No Rocq twin; header deviation 4.) -/
theorem axViolGlblIsProg (G : Gexec) (e : Geid) (P : Lbl → Bool) :
    glblIs G e P → ∃ p ∈ G.gxProg, ∃ l ∈ p, P l = true := by
  rintro ⟨l, hl, hP⟩
  unfold gxLbl at hl
  cases hp : G.gxProg[e.1]? with
  | none => rw [hp] at hl; cases hl
  | some p =>
    rw [hp] at hl
    exact ⟨p, elem_of_list_lookup_2 hp, l, elem_of_list_lookup_2 hl, hP⟩

theorem viol2NoRel (h : Geid) : ¬ glblIs viol2.gdG h lbRelw := by
  intro hr
  obtain ⟨p, hp, l, hl, hb⟩ := axViolGlblIsProg _ _ _ hr
  have hall : ∀ p ∈ viol2.gdG.gxProg, ∀ l ∈ p, lbRelw l = false := by decide +kernel
  rw [hall p hp l hl] at hb
  cases hb

theorem gviolationSat : gdviolationHart 2 viol2 := by
  refine ⟨(0, 0), (1, 0), 0, b1, by decide +kernel,
    (gwbBSpec _ _ _ _).1 (by decide +kernel), ⟨_, rfl, by decide +kernel⟩, trivial,
    ⟨0, rfl, by omega⟩, ⟨1, rfl, by omega⟩, by decide, ?_⟩
  refine .inr ⟨1, b1, (grbBSpec _ _ _ _ _).1 (by decide +kernel),
    by decide +kernel, ?_, ?_⟩
  · rintro ⟨h, _, hr, _⟩
    exact viol2NoRel h hr
  · rintro ws _ ⟨h, _, hr, _⟩
    exact viol2NoRel h hr

/-! # 4. Non-vacuity of the refutation: message passing -/

/-- H0: W x=1 plain (0,0); fence rw,w (0,1); W y=1 RELEASE-class (0,2).
H1: R.aq y (1,0) reads W y (ts 2); R x (1,1) reads W x (ts 1).
gmo = [W0x; W0y; R1y; R1x].  Hart 1's read of x is a FOREIGN observation of an
owned (plain) write. -/
def AxViol.mp : Gdexec :=
  ⟨⟨vimg, [[LStore false 0 [b1] .WCplain,
            LFence true true false true,
            LStore false 1 [b1] .WCrel],
           [LLoad true 1 [2] [b1],
            LLoad false 0 [1] [b1]]],
    [(0, 0), (0, 2), (1, 0), (1, 1)]⟩, []⟩

theorem mpCat : rvwmoCatConsistent AxViol.mp :=
  catConsistentBSound _ (by decide +kernel)

/-- The timeline: hart 0 holds every byte up to its release (gmo pos 1), hart 1
afterwards. -/
def ownMp (_a : Int) (k : Nat) : Option Nat :=
  if k < 2 then some 0 else some 1

theorem mpTl : gtlOk (fun _ => True) 2 AxViol.mp.gdG ownMp := by
  refine ⟨?_, ?_⟩
  · intro e a _ he _ _
    simp only [AxViol.mp, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl <;> (unfold ownMp; decide +kernel)
  · intro a k i _ hk hSk
    rcases k with _ | _ | k
    · simp only [ownMp, show (0 : Nat) < 2 by decide, if_true] at hk
      simp only [ownMp, show (0 + 1 : Nat) < 2 by decide, if_true] at hSk
      exact absurd hk hSk
    · simp only [ownMp, show (0 + 1 : Nat) < 2 by decide, if_true] at hk
      cases hk
      exact ⟨(0, 2), by decide +kernel, rfl, ⟨_, rfl, by decide +kernel⟩⟩
    · simp only [ownMp, show ¬ (k + 1 + 1 < 2) by omega, if_false] at hk
      simp only [ownMp, show ¬ (k + 1 + 1 + 1 < 2) by omega, if_false] at hSk
      exact absurd hk hSk

/-- EVERY premise of `ownedNoViolationCat` holds on `mp` … and `mp` HAS a
foreign read of a plain hart write. -/
theorem mpTlSat :
    rvwmoCatConsistent AxViol.mp ∧ gtlOk (fun _ => True) 2 AxViol.mp.gdG ownMp ∧
    (∀ w a v, w ∈ AxViol.mp.gdG.gxGmo → tidHart 2 (some w.1) →
       glblIs AxViol.mp.gdG w lbPlain → gwritesByte AxViol.mp.gdG w a v → True) ∧
    gwritesByte AxViol.mp.gdG (0, 0) 0 b1 ∧
    glblIs AxViol.mp.gdG (0, 0) lbPlain ∧
    greadsByte AxViol.mp.gdG (1, 1) 0 1 b1 ∧
    gwriteAt AxViol.mp.gdG 1 = some (0, 0) :=
  ⟨mpCat, mpTl, fun _ _ _ _ _ _ _ => trivial,
    (gwbBSpec _ _ _ _).1 (by decide +kernel), ⟨_, rfl, by decide +kernel⟩,
    (grbBSpec _ _ _ _ _).1 (by decide +kernel), by decide +kernel⟩

/-- … so the refutation applies to it (the publication is W y). -/
theorem mpNoViolation : ¬ gdviolationHart 2 AxViol.mp :=
  ownedNoViolationCat (fun _ => True) 2 AxViol.mp ownMp mpCat mpTl
    (fun _ _ _ _ _ _ _ => trivial)

/-- The racy `viol2` admits NO timeline (sanity: the theorem bites). -/
theorem viol2NoTl (own : Int → Nat → Option Nat) :
    ¬ gtlOk (fun _ => True) 2 viol2.gdG own := fun htl =>
  ownedNoViolationCat (fun _ => True) 2 viol2 own viol2Cat htl
    (fun _ _ _ _ _ _ _ => trivial) gviolationSat

end Weak
