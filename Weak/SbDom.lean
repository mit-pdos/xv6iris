/-
Weak: **the S-R `DomAt` lift, increment I-1 — `SbDom`, VIEW DOMINATION along the buffered twin's walk**
(ruling [OWN.150]; `~/dev/weak-orch/weakmach/proposal-A7.md` Q-A7-2 / §3.4 (iii); `PROGRESS-SPSR.md` §2;
`PROGRESS-DomAt.md`).  Lean-only, no Rocq twin.  A leaf: nothing registered imports this file.

**Spec, stated first.**  riscv.cat's load-value axiom lets a plain load return a write co-before the latest
one at its byte whenever the load is gmo-before that later write (from-reads, `r <gmo n`).  `SbCand` (like the
registered machine) admits such a STALE read at timestamp `t` iff no write to the byte lies in
`(t, max (loadVpre ws aq) (coh ws a)]` (`byteRd`).  At an S-P walk state (the landed write list a prefix of
`gwrites G`, `SpikeSP.wrW`) a timestamp IS a GF write index (`SpikeSR.logAt`), so the stale read at GF's
timestamp is admissible exactly when the hart's view is DOMINATED (`SpikeSR.DomAt`).  This file proves that
domination is an INVARIANT of the walk — the template is `WeakAxiomatic3`'s per-component induction
(`invw`: `frdomB` / `ordDom` / `rdom` / `wsrc` / `relsrc`), lifted from the unbuffered trace machine to the
buffered twin, whose stores land LATE (in GF's write order) and whose loads forward.

  §1  the vocabulary: `frB G r a V` (`V` is below every GF write to `a` co-after `r`'s source), the future
      plain loads of a row (`fut`), the fence windows (`fwin`), the five component predicates `dC` (`coh a`),
      `dR` (`wVrNew`), `dF true` (`wVrOld`, behind a `pr ∧ sr` fence), `dF false` (`wVwOld`, behind a
      `pw ∧ sw`… `pw ∧ sr` fence), `relP` (`wVRel`: the timestamp of an own `.rl` write); all `maxcl`.
  §2  the GF facts (riscv.cat): from-reads, visibility, CoRR (rules 1, 2 + load value), rule 4 / 5 / 7
      instances, an AMO's source is gmo-before it (rule 1).
  §3  the walk facts: the landed write list after an item, S-P indices (a landing's timestamp is its
      `gwix`), the state after an item.
  §4  **`SbDom.DomInv`** (the five components + THE FORWARD BANK: the last own landed write to a byte is
      banked at its `gwix` with view `0`), `domInit`, and **`SbDom.domAtOf`**: `DomInv` gives `SpikeSR.DomAt`
      at a plain-load head, so `SpikeSR.staleLoadArm` applies.
  §5  **PRESERVATION**: `domLand` (a landing in GF's write order, own or foreign: late landings raise
      `coh` / `wVwOld` — harmless by CoWR (load value) and rule 4) and `domEv` (an event: an issue, a fence —
      where the pending components are DELIVERED to `wVrNew` —, an I/O step, a load under the per-byte
      condition `SrBytes` (forwarded, or a member timestamp `≤` GF's whose write is gmo-before the load, or an
      own landed source of a non-`.aq` load: the bank contributes `0`), an AMO as the next GF write).

`SrBytes` is the load step's only hypothesis about the walk's read rule; the gate (I-2) supplies it.  Finding
F-DomAt-1 (`PROGRESS-DomAt.md` §0.1): an `.aq` load's own landed source must be gmo-before it — the case RVWMO
allows otherwise (an `lr.aq` rfi from a store gmo-after it) is excluded by `SrBytes` (it is a progress
question, not a domination one).

Spec: FAITHFUL (theorems about the existing model; riscv.cat's load value, rules 1, 2, 4, 5, 7; nothing
assumed, no xv6 fact).  Lean-only helpers `SbDom.*`.
-/
import Weak.SpikeSR

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open Lbl

namespace SbDom

open SbWalk SbAgree SbReplay SbOrd SpikeSP

/-! # 1. The vocabulary -/

/-- `V` is below every GF write to byte `a` co-after the source of `r`'s read of `a` (from-reads). -/
def frB (G : Gexec) (r : Geid) (a : Int) (V : Nat) : Prop :=
  ∀ t v n u, greadsByte G r a t v → gwritesByte G n a u → t < gwix G n → V < gwix G n

/-- A FUTURE plain load of row `x`: position at least `len` (the row's realized length). -/
def fut (G : Gexec) (x len : Nat) (r : Geid) : Prop :=
  r.1 = x ∧ len ≤ r.2 ∧ ∃ aq base ts vs, gxLbl G r = some (LLoad aq base ts vs)

/-- A fence of row `x` in `[len, r.2)` with the successor bit `sr` and the predecessor bit `pr` (`rd`) or
`pw` (`¬ rd`). -/
def fwin (G : Gexec) (x len : Nat) (rd : Bool) (r : Geid) : Prop :=
  ∃ kf pr pw sw, len ≤ kf ∧ kf < r.2 ∧ gxLbl G (x, kf) = some (LFence pr pw true sw) ∧
    (if rd then pr else pw) = true

/-- `coh a`'s component: below the fr-successors of every future load of `a`. -/
def dC (G : Gexec) (x len : Nat) (a : Int) (V : Nat) : Prop := ∀ r, fut G x len r → frB G r a V

/-- `wVrNew`'s component: below the fr-successors of every future load. -/
def dR (G : Gexec) (x len : Nat) (V : Nat) : Prop := ∀ r a, fut G x len r → frB G r a V

/-- `wVrOld`'s (`rd`) / `wVwOld`'s (`¬ rd`) component: below the fr-successors of every future load behind a
fence that delivers it. -/
def dF (G : Gexec) (x len : Nat) (rd : Bool) (V : Nat) : Prop :=
  ∀ r a, fut G x len r → fwin G x len rd r → frB G r a V

/-- `wVRel`'s component: `0`, or at most the write index of an own realized `.rl` write. -/
def relP (G : Gexec) (x len : Nat) (V : Nat) : Prop :=
  V = 0 ∨ ∃ W, W ∈ gwrites G ∧ W.1 = x ∧ W.2 < len ∧ glblIs G W lbRl ∧ V ≤ gwix G W

section Voc

variable {G : Gexec}

theorem frB0 (hwf : gwf G) (r : Geid) (a : Int) : frB G r a 0 := by
  intro t v n u _ hn _
  have := SbOrd.gwixPos G n (gwritesOf G n a u hwf hn); omega

theorem frBMax (r : Geid) (a : Int) (V1 V2 : Nat) : frB G r a V1 → frB G r a V2 → frB G r a (max V1 V2) := by
  intro h1 h2 t v n u hr hn ht
  have := h1 t v n u hr hn ht; have := h2 t v n u hr hn ht; omega

theorem frBLe (r : Geid) (a : Int) (V V' : Nat) : V' ≤ V → frB G r a V → frB G r a V' := by
  intro hle h t v n u hr hn ht; have := h t v n u hr hn ht; omega

theorem maxclDC (hwf : gwf G) (x len : Nat) (a : Int) : maxcl (dC G x len a) :=
  ⟨fun r _ => frB0 hwf r a, fun _ _ h1 h2 r hr => frBMax r a _ _ (h1 r hr) (h2 r hr)⟩

theorem maxclDR (hwf : gwf G) (x len : Nat) : maxcl (dR G x len) :=
  ⟨fun r a _ => frB0 hwf r a, fun _ _ h1 h2 r a hr => frBMax r a _ _ (h1 r a hr) (h2 r a hr)⟩

theorem maxclDF (hwf : gwf G) (x len : Nat) (rd : Bool) : maxcl (dF G x len rd) :=
  ⟨fun r a _ _ => frB0 hwf r a,
   fun _ _ h1 h2 r a hr hw => frBMax r a _ _ (h1 r a hr hw) (h2 r a hr hw)⟩

theorem maxclRelP (x len : Nat) : maxcl (relP G x len) := by
  refine ⟨.inl rfl, fun n1 n2 h1 h2 => ?_⟩
  rcases h1 with rfl | ⟨W1, h1a, h1b, h1c, h1d, h1e⟩
  · rw [Nat.zero_max]; exact h2
  · rcases h2 with rfl | ⟨W2, h2a, h2b, h2c, h2d, h2e⟩
    · rw [Nat.max_zero]; exact .inr ⟨W1, h1a, h1b, h1c, h1d, h1e⟩
    · by_cases hle : n1 ≤ n2
      · rw [Nat.max_eq_right hle]; exact .inr ⟨W2, h2a, h2b, h2c, h2d, h2e⟩
      · rw [Nat.max_eq_left (by omega)]; exact .inr ⟨W1, h1a, h1b, h1c, h1d, h1e⟩

/-- Every component weakens along the row (fewer future loads, shorter windows). -/
theorem futWk (x len len' : Nat) (r : Geid) : len ≤ len' → fut G x len' r → fut G x len r :=
  fun hle ⟨h1, h2, h3⟩ => ⟨h1, by omega, h3⟩

theorem fwinWk (x len len' : Nat) (rd : Bool) (r : Geid) : len ≤ len' → fwin G x len' rd r →
    fwin G x len rd r :=
  fun hle ⟨kf, pr, pw, sw, h1, h2, h3, h4⟩ => ⟨kf, pr, pw, sw, by omega, h2, h3, h4⟩

theorem dCWk (x len len' : Nat) (a : Int) (V : Nat) : len ≤ len' → dC G x len a V → dC G x len' a V :=
  fun hle h r hr => h r (futWk x len len' r hle hr)

theorem dRWk (x len len' : Nat) (V : Nat) : len ≤ len' → dR G x len V → dR G x len' V :=
  fun hle h r a hr => h r a (futWk x len len' r hle hr)

theorem dFWk (x len len' : Nat) (rd : Bool) (V : Nat) : len ≤ len' → dF G x len rd V →
    dF G x len' rd V :=
  fun hle h r a hr hw => h r a (futWk x len len' r hle hr) (fwinWk x len len' rd r hle hw)

theorem relPWk (x len len' : Nat) (V : Nat) : len ≤ len' → relP G x len V → relP G x len' V := by
  rintro hle (h | ⟨W, h1, h2, h3, h4, h5⟩)
  · exact .inl h
  · exact .inr ⟨W, h1, h2, by omega, h4, h5⟩

theorem dRdC (x len : Nat) (a : Int) (V : Nat) : dR G x len V → dC G x len a V :=
  fun h r hr => h r a hr

theorem dRdF (x len : Nat) (rd : Bool) (V : Nat) : dR G x len V → dF G x len rd V :=
  fun h r a hr _ => h r a hr

end Voc

/-! # 2. The GF facts (riscv.cat) -/

section Gf

variable {G : Gexec}

theorem gmoTrans (e1 e2 e3 : Geid) : gmoLt G e1 e2 → gmoLt G e2 e3 → gmoLt G e1 e3 :=
  fun h1 h2 => ⟨h1.1, h2.2.1, Nat.lt_trans h1.2.2 h2.2.2⟩

/-- A plain load is not a write. -/
theorem plainNe (r : Geid) (aq : Bool) (base : Int) (ts : List Nat) (vs : List (BitVec 8))
    (hl : gxLbl G r = some (LLoad aq base ts vs)) (n : Geid) (a : Int) (u : BitVec 8) :
    gwritesByte G n a u → r ≠ n := by
  rintro ⟨l, b, vs', j, hl', hw, -⟩ rfl
  rw [hl, Option.some.injEq] at hl'
  subst hl'; cases hw

theorem futNe (x len : Nat) (r : Geid) (hr : fut G x len r) (n : Geid) (a : Int) (u : BitVec 8) :
    gwritesByte G n a u → r ≠ n := by
  obtain ⟨-, -, aq, base, ts, vs, hl⟩ := hr
  exact plainNe r aq base ts vs hl n a u

theorem wixLt (hc : CatH G) (W n : Geid) : W ∈ gwrites G → n ∈ gwrites G → gmoLt G W n →
    gwix G W < gwix G n :=
  fun h1 h2 h => (gwixGposLt G W n hc.wf.1 h1 h2).2 h.2.2

/-- **FROM GMO**: a bound by a write gmo-before a future load bounds its fr-successors. -/
theorem frOfGmo (hc : CatH G) (x len : Nat) (r : Geid) (hr : fut G x len r) (a : Int) (W : Geid)
    (V : Nat) : W ∈ gwrites G → gmoLt G W r → V ≤ gwix G W → frB G r a V := by
  intro hW hlt hV t v n u hrd hwn htn
  have hrn := frLtW hc r n a t v u hrd hwn htn (futNe x len r hr n a u hwn)
  have := wixLt hc W n hW (gwritesOf G n a u hc.wf hwn) (gmoTrans W r n hlt hrn)
  omega

/-- **FROM VISIBILITY** (load value): a write to the byte visible to the load bounds its fr-successors. -/
theorem frOfVis (hc : CatH G) (r : Geid) (a : Int) (W : Geid) (u0 : BitVec 8) (V : Nat) :
    gwritesByte G W a u0 → gvisible G W r → V ≤ gwix G W → frB G r a V := by
  intro hW hvis hV t v n u hrd _ htn
  have := (hc.lv r a t v hrd).2 W u0 hW hvis; omega

/-- **CoRR** (rules 1 and 2 + load value): two po-ordered reads of a byte read co-ordered sources. -/
theorem corr (hc : CatH G) (r1 r2 : Geid) (a : Int) (t1 t2 : Nat) (v1 v2 : BitVec 8)
    (hpo : WeakRvwmoGraph.gpo G r1 r2) (hr2W : ∀ u, ¬ gwritesByte G r2 a u)
    (h1 : greadsByte G r1 a t1 v1) (h2 : greadsByte G r2 a t2 v2) : t1 ≤ t2 := by
  cases t1 with
  | zero => exact Nat.zero_le _
  | succ i =>
    obtain ⟨⟨s1, hs1, hsw, hvis1⟩, -⟩ := hc.lv r1 a (i + 1) v1 h1
    obtain ⟨hs1W, hix⟩ := gwriteAtInv G (i + 1) s1 hc.wf.1 hs1
    by_cases hv2 : gvisible G s1 r2
    · have := (hc.lv r2 a t2 v2 h2).2 s1 v1 hsw hv2; omega
    · have hnpo : ¬ WeakRvwmoGraph.gpo G s1 r2 := fun h => hv2 (.inr h)
      have hnmo : ¬ gmoLt G s1 r2 := fun h => hv2 (.inl h)
      have hs1r1 : gmoLt G s1 r1 := by
        rcases hvis1 with h | h
        · exact h
        · exact absurd ⟨h.1.trans hpo.1, Nat.lt_trans h.2.1 hpo.2.1, h.2.2.1, hpo.2.2.2⟩ hnpo
      have hr2m := gwfMemGmo G r2 hc.wf (SBAcq.rdGmem G r2 a t2 v2 h2)
      have hs1m := (gwrBOf G s1 a v1 hc.wf hsw).2
      have hne : r2 ≠ s1 := fun h => hr2W v1 (by rw [h]; exact hsw)
      have hr2s1 : gmoLt G r2 s1 := by
        rcases gmoLtTotal G r2 s1 hc.wf.1 hr2m hs1m hne with h | h
        · exact h
        · exact absurd h hnmo
      have hr2r1 : gmoLt G r2 r1 := gmoTrans r2 s1 r1 hr2s1 hs1r1
      by_cases heq : i + 1 = t2
      · omega
      · by_cases hmid : ∃ W u, gwritesByte G W a u ∧ WeakRvwmoGraph.gpo G r1 W ∧
            WeakRvwmoGraph.gpo G W r2
        · obtain ⟨W, u, hWw, hpo1, hpo2⟩ := hmid
          have hle := (hc.lv r2 a t2 v2 h2).2 W u hWw (.inr hpo2)
          have hr1W : gmoLt G r1 W := rule1Lt G r1 W a u hc.ppo hpo1 (.inr ⟨_, _, h1⟩) hWw
          have := wixLt hc s1 W hs1W (gwritesOf G W a u hc.wf hWw) (gmoTrans s1 r1 W hs1r1 hr1W)
          omega
        · have hp2 : gppoCat6 G r1 r2 := Or.inr (Or.inl ⟨hpo, a, i + 1, v1, t2, v2, h1, h2, heq,
            fun W u hWw hp1 hp2 => hmid ⟨W, u, hWw, hp1, hp2⟩⟩)
          have := hc.ppo r1 r2 hp2
          exact absurd (Nat.lt_trans this.2.2 hr2r1.2.2) (Nat.lt_irrefl _)

/-- A read source is gmo-before the reader, or an own po-earlier write. -/
theorem srcCases (hc : CatH G) (r : Geid) (a : Int) (t : Nat) (v : BitVec 8) (s : Geid) :
    greadsByte G r a t v → gwriteAt G t = some s → gmoLt G s r ∨ WeakRvwmoGraph.gpo G s r := by
  intro hrd hs
  cases t with
  | zero => simp [gwriteAt] at hs
  | succ i =>
    obtain ⟨⟨s', hs', -, hvis⟩, -⟩ := hc.lv r a (i + 1) v hrd
    rw [hs, Option.some.injEq] at hs'
    subst hs'; exact hvis

/-- An AMO's read source is gmo-before it (rfe, or rule 1 for an own source). -/
theorem amoSrcLt (hc : CatH G) (r : Geid) (a : Int) (t : Nat) (v u : BitVec 8) (s : Geid) :
    greadsByte G r a t v → gwritesByte G r a u → gwriteAt G t = some s → gmoLt G s r := by
  intro hrd hwr hs
  cases t with
  | zero => simp [gwriteAt] at hs
  | succ i =>
    obtain ⟨⟨s', hs', hsw, hvis⟩, -⟩ := hc.lv r a (i + 1) v hrd
    rw [hs, Option.some.injEq] at hs'
    subst hs'
    rcases hvis with h | h
    · exact h
    · exact rule1Lt G s r a u hc.ppo h (.inl ⟨_, hsw⟩) hwr

/-- RULE 4 instance: an event of row `x` before the window's fence is gmo-before the future load. -/
theorem fenceBefore (hc : CatH G) (x len : Nat) (rd : Bool) (e : Geid) (le : Lbl)
    (hle : gxLbl G e = some le) (hex : e.1 = x) (hk : e.2 < len)
    (hkind : (if rd then lbIsR le else lbIsW le) = true) (r : Geid) (hr : fut G x len r)
    (hw : fwin G x len rd r) : gmoLt G e r := by
  obtain ⟨hrx, -, aq, base, ts, vs, hrl⟩ := hr
  obtain ⟨kf, pr, pw, sw, hk1, hk2, hf, hb⟩ := hw
  have hf' : gxLbl G (e.1, kf) = some (LFence pr pw true sw) := by rw [hex]; exact hf
  refine SBAcq.fenceLt G e r le _ kf pr pw true sw hc.ppo hle hrl (by rw [hex, hrx]) (by omega) hk2 hf'
    ?_ (by simp [lbIsR])
  cases rd with
  | true => simp only [if_true] at hkind hb; simp [hkind, hb]
  | false => simp only [Bool.false_eq_true, if_false] at hkind hb; simp [hkind, hb]

/-- RULE 5 instance: an `.aq` read before a future load is gmo-before it. -/
theorem acqBefore (hc : CatH G) (x len : Nat) (e : Geid) (le : Lbl) (hle : gxLbl G e = some le)
    (hex : e.1 = x) (hk : e.2 < len) (hR : lbIsR le = true) (hA : lbAq le = true) (r : Geid)
    (hr : fut G x len r) : gmoLt G e r := by
  obtain ⟨hrx, hlen, aq, base, ts, vs, hrl⟩ := hr
  exact SBAcq.acqLt G e r le _ hc.ppo hle hrl (by rw [hex, hrx]) (by omega) hR hA (by simp [lbIsMem, lbIsR])

/-- RULE 7 instance: an own `.rl` write before an `.aq` load is gmo-before it. -/
theorem rcscBefore (hc : CatH G) (W r : Geid) (hrl : glblIs G W lbRl) (haq : glblIs G r lbAq)
    (hx : W.1 = r.1) (hk : W.2 < r.2) : gmoLt G W r := by
  obtain ⟨l1, h1, b1⟩ := hrl
  obtain ⟨l2, h2, b2⟩ := haq
  exact hc.ppo W r (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    ⟨SBAcq.gpoOf G W r l1 l2 h1 h2 hx hk, ⟨l1, h1, by simp [lbRcsc, b1]⟩,
      ⟨l2, h2, by simp [lbRcsc, b2]⟩⟩)))))

/-- A future load's `.aq`-ness is its label's. -/
theorem futAq (r : Geid) (aq : Bool) (base : Int) (ts : List Nat) (vs : List (BitVec 8)) :
    gxLbl G r = some (LLoad aq base ts vs) → aq = true → glblIs G r lbAq :=
  fun hl ha => ⟨_, hl, by simp [lbAq, ha]⟩

end Gf

/-! # 3. Walk facts -/

section Walk

variable {img : Image} {G : Gexec} {X : Geid → Prop} {w : WS}

/-- S-P indices: a member of a GF write prefix has index at most its length. -/
theorem wixLeOfPfx (L : List Geid) (W : Geid) (hnd : G.gxGmo.Nodup) : L <+: gwrites G → W ∈ L →
    gwix G W ≤ L.length := by
  rintro ⟨T, hT⟩ hW
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hW
  have hlt := lookup_lt_Some hi
  have : (gwrites G)[i]? = some W := by rw [← hT, List.getElem?_append_left hlt]; exact hi
  rw [gwixOfLookup G i W hnd this]; omega

/-- S-P indices: the next GF write has index the prefix length plus one. -/
theorem wixOfNext (L : List Geid) (s : Geid) (hnd : G.gxGmo.Nodup) : L ++ [s] <+: gwrites G →
    gwix G s = L.length + 1 := by
  rintro ⟨T, hT⟩
  have : (gwrites G)[L.length]? = some s := by rw [← hT]; simp
  exact gwixOfLookup G _ s hnd this

theorem wrWSub (W : Geid) : W ∈ wrW w → W ∈ w.gmo := fun h => (List.mem_filter.1 h).1

/-- A landed write is realized. -/
theorem wrWReal (hI : Inv img w) (W : Geid) : W ∈ wrW w → W.2 < (w.rows W.1).length := by
  intro h
  obtain ⟨l, hl, -⟩ := hI.gmoMem W (wrWSub W h)
  exact lookup_lt_Some hl

/-- A landed write of an S-P state is a GF write. -/
theorem wrWG (hW : wrW w <+: gwrites G) (W : Geid) : W ∈ wrW w → W ∈ gwrites G := by
  obtain ⟨T, hT⟩ := hW
  intro h; rw [← hT]; exact List.mem_append_left _ h

/-- The member's labels are GF's up to `lblRelX`; on writes, the GF write bytes are the member's. -/
theorem pendLblI (hI : Inv img w) (hpf : pfx G X w) (i : Nat) (p : Nat × SbEnt) : p ∈ w.pend i →
    ∃ rl base vs kc, gxLbl G (i, p.1) = some (LStore rl base vs kc) ∧
      (w.rows i)[p.1]? = some (LStore rl base vs kc) ∧ p.2.msg = ⟨base, vs, some i, kc⟩ := by
  intro hp
  obtain ⟨rl, base, vs, kc, hrow, hmsg⟩ := hI.pendSt i p hp
  obtain ⟨l, hl, hrel⟩ := hpf.1 i p.1 _ hrow
  rcases relXW _ l _ hrel (.inr rfl) with h | ⟨_, _, _, _, _, _, _, _, _, h, -⟩
  · rw [← h] at hl; exact ⟨rl, base, vs, kc, hl, hrow, hmsg⟩
  · cases h

/-- The bytes a write label writes, as the store fold's address list. -/
theorem wrBytes (e : Geid) (l : Lbl) (base : Int) (vs : List (BitVec 8)) (hl : gxLbl G e = some l)
    (hw : lbWr l = some (base, vs)) (a : Int) :
    a ∈ storeRunAs base vs.length ↔ ∃ u, gwritesByte G e a u := by
  constructor
  · intro ha
    obtain ⟨j, hj, rfl⟩ := elemOfMapSeq base vs.length a ha
    exact ⟨vs[j], l, base, vs, j, hl, hw, List.getElem?_eq_getElem hj, rfl⟩
  · rintro ⟨u, l', b', vs', j, hl', hw', hv, ha⟩
    rw [hl, Option.some.injEq] at hl'
    subst hl'
    rw [hw, Option.some.injEq, Prod.mk.injEq] at hw'
    obtain ⟨rfl, rfl⟩ := hw'
    rw [← ha]
    exact List.mem_map.2 ⟨j, List.mem_range'_1.2 ⟨Nat.zero_le _, by
      have := lookup_lt_Some hv; omega⟩, rfl⟩

/-- The landed write list after a landing. -/
theorem wrWLand (hI : Inv img w) (i k : Nat) (p : Nat × SbEnt) (hp : (w.pend i)[k]? = some p) :
    wrW (nextI w (.land i k)) = wrW w ++ [(i, p.1)] := by
  obtain ⟨rl, base, vs, kc, hrow, -⟩ := hI.pendSt i p (List.mem_of_getElem? hp)
  rw [SbOrd.landEq i k p hp]
  show (w.gmo ++ [(i, p.1)]).filter (rwW w.rows) = _
  rw [List.filter_append]
  have : rwW w.rows (i, p.1) = true := by unfold rwW; rw [hrow]; rfl
  simp only [List.filter_cons, this, if_true, List.filter_nil]
  rfl

/-- The landed write list after an event: an AMO appends itself, nothing else lands. -/
theorem wrWEv (hI : Inv img w) (s : Estep) :
    wrW (nextI w (.ev s)) = wrW w ++
      (if (gmoEv s.esLb && lbIsW s.esLb) = true then [(s.esAg, (w.rows s.esAg).length)] else []) := by
  have hcong : ∀ e, e ∈ w.gmo → rwW (nextI w (.ev s)).rows e = rwW w.rows e := by
    intro e he
    obtain ⟨l, hl, -⟩ := hI.gmoMem e he
    unfold rwW
    rw [hl, rowsEvOld w s e.1 e.2 l hl]
  have hold : w.gmo.filter (rwW (nextI w (.ev s)).rows) = wrW w := List.filter_congr hcong
  have hnew : rwW (nextI w (.ev s)).rows (s.esAg, (w.rows s.esAg).length) = lbIsW s.esLb := by
    unfold rwW
    show (match (upd w.rows s.esAg (w.rows s.esAg ++ [s.esLb]) s.esAg)[(w.rows s.esAg).length]? with
      | some l => lbIsW l
      | none => false) = _
    rw [updEq]; simp
  show (if gmoEv s.esLb = true then w.gmo ++ [(s.esAg, (w.rows s.esAg).length)] else w.gmo).filter
    (rwW (nextI w (.ev s)).rows) = _
  by_cases hg : gmoEv s.esLb = true
  · rw [if_pos hg, List.filter_append, hold, List.filter_cons, hnew, List.filter_nil]
    by_cases hw : lbIsW s.esLb = true <;> simp [hg, hw]
  · rw [if_neg hg, hold]; simp [hg]

/-- The views after a landing. -/
theorem wsLand (i k : Nat) (p : Nat × SbEnt) (hp : (w.pend i)[k]? = some p) (hI : Inv img w) (y : Nat) :
    (nextI w (.land i k)).σ.ms.msWs y =
      if y = i then SbCand.landPost (w.σ.ms.msWs i) p.2 (w.σ.ms.msLog.length + 1)
      else w.σ.ms.msWs y := by
  rw [SbOrd.landEq i k p hp]
  have he : (w.σ.sb i)[k]? = some p.2 := by rw [hI.sb i, List.getElem?_map, hp]; rfl
  show (SbCand.nextL w.σ i k).ms.msWs y = _
  unfold SbCand.nextL
  rw [he]
  by_cases hy : y = i
  · subst hy; simp [updWsEq]
  · simp [updWsNe _ _ _ _ hy, hy]

theorem rowsLand (i k : Nat) (p : Nat × SbEnt) (hp : (w.pend i)[k]? = some p) :
    (nextI w (.land i k)).rows = w.rows := by
  rw [SbOrd.landEq i k p hp]

/-- The per-agent view update of an event (`SbCand.nextE`), as a function of the label. -/
def evWs (ws : Wstate) (sb : List SbEnt) (n : Nat) : Lbl → Wstate
  | LLoad aq base ts _ => loadPostRun ws aq base (SbCand.fwdMask sb base ts)
  | LStore .. => SbCand.issuePost ws
  | LFence pr pw sr sw => fencePost ws pr pw sr sw
  | LRmw aq rl base ts _ wvs _ => storePostRun (loadPostRun ws aq base ts) rl base wvs.length (n + 1)
  | LIo .. => ws

theorem wsEv (s : Estep) (y : Nat) :
    (nextI w (.ev s)).σ.ms.msWs y =
      if y = s.esAg then evWs (w.σ.ms.msWs s.esAg) (w.σ.sb s.esAg) w.σ.ms.msLog.length s.esLb
      else w.σ.ms.msWs y := by
  show (SbCand.nextE w.σ s.esAg s.esLb).ms.msWs y = _
  by_cases hy : y = s.esAg
  · subst hy
    cases s with
    | mk i l => cases l <;> simp [SbCand.nextE, mnext, evWs, updWsEq]
  · cases s with
    | mk i l => cases l <;> simp [SbCand.nextE, mnext, updWsNe _ _ _ _ hy, hy]

theorem rowsLenEv (s : Estep) (y : Nat) :
    ((nextI w (.ev s)).rows y).length =
      if y = s.esAg then (w.rows y).length + 1 else (w.rows y).length := by
  rw [rowsEvEq s y]
  by_cases hy : y = s.esAg
  · rw [if_pos hy, if_pos hy, List.length_append, List.length_singleton]
  · rw [if_neg hy, if_neg hy]

end Walk


/-! # 4. The invariant -/

/-- **VIEW DOMINATION** of a hart's view state `ws` at row length `len` with landed write list `L`
(`WeakAxiomatic3.invw`, lifted), plus THE FORWARD BANK: every entry has view `0`, and the last own landed
write to a byte is banked at its write index. -/
structure Dom (G : Gexec) (x len : Nat) (L : List Geid) (ws : Wstate) : Prop where
  coh : ∀ a, dC G x len a (coh ws a)
  vrn : dR G x len ws.wVrNew
  vrel : relP G x len ws.wVRel
  vro : dF G x len true ws.wVrOld
  vwo : dF G x len false ws.wVwOld
  bz : ∀ a tf vf, get? ws.wFwd a = some (tf, vf) → vf = 0
  bank : ∀ a W u, W ∈ L → W.1 = x → gwritesByte G W a u →
    (∀ W' u', W' ∈ L → W'.1 = x → gwritesByte G W' a u' → gwix G W' ≤ gwix G W) →
    get? ws.wFwd a = some (gwix G W, 0)

/-- **THE WALK INVARIANT** of hart `x` at walk state `w`. -/
def DomInv (G : Gexec) (w : WS) (x : Nat) : Prop :=
  Dom G x (w.rows x).length (wrW w) (w.σ.ms.msWs x)

theorem domInit (G : Gexec) (hwf : gwf G) (img : Image) (x : Nat) : DomInv G (init img) x where
  coh _ := (maxclDC hwf x _ _).1
  vrn := (maxclDR hwf x _).1
  vrel := .inl rfl
  vro := (maxclDF hwf x _ true).1
  vwo := (maxclDF hwf x _ false).1
  bz _ _ _ h := by simp [init, wsInit, lookupEmpty] at h
  bank _ _ _ h := by simp [wrW, init] at h

/-- **`DomInv` GIVES `DomAt`** at a plain-load head: `SpikeSR.staleLoadArm`'s domination premise. -/
theorem domAtOf {G : Gexec} {w : WS} {x : Nat} (hc : CatH G) (hD : DomInv G w x) (aq : Bool) (base : Int)
    (ts : List Nat) (vs : List (BitVec 8)) (hl : gxLbl G (hd w x) = some (LLoad aq base ts vs))
    (a : Int) (t : Nat) (v : BitVec 8) (hrd : greadsByte G (hd w x) a t v) :
    SpikeSR.DomAt G w x aq a t := by
  intro n u hn htn
  have hfut : fut G x (w.rows x).length (hd w x) := ⟨rfl, Nat.le_refl _, aq, base, ts, vs, hl⟩
  have h1 := hD.vrn _ a hfut t v n u hrd hn htn
  have h2 := hD.coh a _ hfut t v n u hrd hn htn
  have h3 : (if aq then (w.σ.ms.msWs x).wVRel else 0) < gwix G n := by
    cases aq with
    | false => exact SbOrd.gwixPos G n (gwritesOf G n a u hc.wf hn)
    | true =>
      show (w.σ.ms.msWs x).wVRel < gwix G n
      rcases hD.vrel with h0 | ⟨W, hW, hWx, hWk, hWrl, hle⟩
      · rw [h0]; exact SbOrd.gwixPos G n (gwritesOf G n a u hc.wf hn)
      · have hlt := rcscBefore hc W (hd w x) hWrl (futAq _ true base ts vs hl rfl) hWx hWk
        exact frOfGmo hc x _ _ hfut a W _ hW hlt hle t v n u hrd hn htn
  unfold loadVpre
  omega

/-! # 5. Preservation -/

section Pres

variable {G : Gexec}

/-- Only the read-relevant fields matter. -/
theorem domCongr (x len : Nat) (L : List Geid) (ws ws' : Wstate) (hD : Dom G x len L ws)
    (hc : ∀ a, coh ws' a = coh ws a)
    (h1 : ws'.wVrNew = ws.wVrNew) (h2 : ws'.wVRel = ws.wVRel) (h3 : ws'.wVrOld = ws.wVrOld)
    (h4 : ws'.wVwOld = ws.wVwOld) (h5 : ws'.wFwd = ws.wFwd) : Dom G x len L ws' := by
  refine ⟨fun a => ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hc]; exact hD.coh a
  · rw [h1]; exact hD.vrn
  · rw [h2]; exact hD.vrel
  · rw [h3]; exact hD.vro
  · rw [h4]; exact hD.vwo
  · rw [h5]; exact hD.bz
  · rw [h5]; exact hD.bank

theorem domWk (x len len' : Nat) (L : List Geid) (ws : Wstate) : len ≤ len' → Dom G x len L ws →
    Dom G x len' L ws := by
  intro hle hD
  exact ⟨fun a => dCWk x len len' a _ hle (hD.coh a), dRWk x len len' _ hle hD.vrn,
    relPWk x len len' _ hle hD.vrel, dFWk x len len' true _ hle hD.vro, dFWk x len len' false _ hle hD.vwo,
    hD.bz, hD.bank⟩

theorem domL (x len : Nat) (L L' : List Geid) (ws : Wstate) (h : ∀ W, W.1 = x → (W ∈ L' ↔ W ∈ L)) :
    Dom G x len L ws → Dom G x len L' ws := by
  intro hD
  refine ⟨hD.coh, hD.vrn, hD.vrel, hD.vro, hD.vwo, hD.bz, fun a W u hW hWx hwr hmax => ?_⟩
  exact hD.bank a W u ((h W hWx).1 hW) hWx hwr
    (fun W' u' hW' hW'x hw' => hmax W' u' ((h W' hW'x).2 hW') hW'x hw')

/-- A plain load writes nothing. -/
theorem futNoW (x len : Nat) (r : Geid) (hr : fut G x len r) (a : Int) (u : BitVec 8) :
    ¬ gwritesByte G r a u := fun h => futNe x len r hr r a u h rfl

/-- A bound below every timestamp the future load reads at the byte. -/
theorem frOfLe (r : Geid) (a : Int) (V : Nat) (h : ∀ t v, greadsByte G r a t v → V ≤ t) : frB G r a V := by
  intro t v n u hrd _ htn; have := h t v hrd; omega

/-- **THE STORE HALF** (a landing, or an AMO's write): a write `s` of row `x` (realized, `s.2 < len`) that is
GF's next write lands at its write index; `coh` rises on its bytes (CoWR: load value), `wVwOld` rises
(rule 4), `wVRel` rises for an `.rl` write (rule 7), the bank records it. -/
theorem storeHalf (hc : CatH G) (x len : Nat) (L : List Geid) (ws : Wstate) (s : Geid) (le : Lbl)
    (base : Int) (vs : List (BitVec 8)) (rl : Bool) (hD : Dom G x len L ws)
    (hS : L ++ [s] <+: gwrites G) (hsx : s.1 = x) (hsk : s.2 < len) (hle : gxLbl G s = some le)
    (hwr : lbWr le = some (base, vs)) (hrl : rl = true → glblIs G s lbRl) :
    Dom G x len (L ++ [s])
      ((storeRunAs base vs.length).foldl (fun w a => storePost w rl a (gwix G s)) ws) := by
  have hsG : s ∈ gwrites G := by obtain ⟨T, hT⟩ := hS; rw [← hT]; simp
  have hLp : L <+: gwrites G := (List.prefix_append L [s]).trans hS
  have hix : gwix G s = L.length + 1 := wixOfNext L s hc.wf.1 hS
  have hLle : ∀ W, W ∈ L → gwix G W ≤ L.length := fun W hW => wixLeOfPfx L W hc.wf.1 hLp hW
  have hsle : lbIsW le = true := by cases le <;> simp_all [lbWr, lbIsW]
  have hvis : ∀ r, fut G x len r → WeakRvwmoGraph.gpo G s r := by
    rintro r ⟨hrx, hrk, aq, b, ts, vs', hrl'⟩
    exact SBAcq.gpoOf G s r le _ hle hrl' (by rw [hsx, hrx]) (by omega)
  refine ⟨fun a => ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply storeFoldCoh _ rl _ _ ws a (maxclDC hc.wf x len a) (hD.coh a)
    intro ha r hr
    obtain ⟨u, hu⟩ := (wrBytes s le base vs hle hwr a).1 ha
    exact frOfVis hc r a s u _ hu (.inr (hvis r hr)) (Nat.le_refl _)
  · rw [storeFoldVrNew]; exact hD.vrn
  · apply storeFoldVRel _ rl _ _ ws (maxclRelP x len) hD.vrel
    intro h; exact .inr ⟨s, hsG, hsx, hsk, hrl h, Nat.le_refl _⟩
  · rw [storeFoldVrOld]; exact hD.vro
  · apply storeFoldVwOld _ rl _ _ ws (maxclDF hc.wf x len false) hD.vwo
    intro r a hr hw
    exact frOfGmo hc x len r hr a s _ hsG
      (fenceBefore hc x len false s le hle hsx hsk (by simp [hsle]) r hr hw) (Nat.le_refl _)
  · intro a tf vf h
    by_cases ha : a ∈ storeRunAs base vs.length
    · rw [storeFoldFwdIn rl _ _ ws a ha, Option.some.injEq, Prod.mk.injEq] at h; exact h.2.symm
    · rw [storeFoldFwdOut rl _ _ ws a ha] at h; exact hD.bz a tf vf h
  · intro a W u hW hWx hwr' hmax
    by_cases ha : a ∈ storeRunAs base vs.length
    · obtain ⟨u0, hu0⟩ := (wrBytes s le base vs hle hwr a).1 ha
      have hWs : W = s := by
        rcases List.mem_append.1 hW with hW | hW
        · have h1 := hmax s u0 (by simp) hsx hu0
          have h2 := hLle W hW
          omega
        · simpa using hW
      subst hWs
      rw [storeFoldFwdIn rl _ _ ws a ha]
    · have hWL : W ∈ L := by
        rcases List.mem_append.1 hW with hW | hW
        · exact hW
        · simp only [List.mem_singleton] at hW
          subst hW
          exact absurd ((wrBytes _ le base vs hle hwr a).2 ⟨u, hwr'⟩) ha
      rw [storeFoldFwdOut rl _ _ ws a ha]
      exact hD.bank a W u hWL hWx hwr'
        (fun W' u' hW' hW'x hw' => hmax W' u' (List.mem_append_left _ hW') hW'x hw')

/-- The per-byte condition on the timestamp `t'` a load step feeds its view update at byte `j` (GF's
timestamps `ts`; the load `r'`): at most GF's, and `0`, or at most the index of a write gmo-before `r'`, or
(a non-`.aq` load) GF's own landed source — whose BANK entry then contributes `0`. -/
def SrOk (G : Gexec) (L : List Geid) (x : Nat) (r' : Geid) (aq : Bool) (ts : List Nat) (j t' : Nat) :
    Prop :=
  ∃ t, ts[j]? = some t ∧ t' ≤ t ∧ (t' = 0 ∨ (∃ W, W ∈ gwrites G ∧ gmoLt G W r' ∧ t' ≤ gwix G W) ∨
    (aq = false ∧ t' = t ∧ ∃ s, gwriteAt G t = some s ∧ s.1 = x ∧ s ∈ L))

theorem loadFoldFwd (aq : Bool) (vpre : Nat) (ats : List (Int × Nat)) (ws : Wstate) :
    (ats.foldl (fun w at_ => loadPostAt w aq vpre at_.1 at_.2) ws).wFwd = ws.wFwd := by
  induction ats generalizing ws with
  | nil => rfl
  | cons p l ih => exact ih _

/-- **THE LOAD HALF** (a plain load, or an AMO's read): the read `r' = (x, len)` with timestamps `mts` fed
to the view update.  `coh` rises by CoRR (rules 1, 2 + load value); `wVrOld` by contributions whose write is
gmo-before `r'` (delivered by a later fence through rule 4) or by `0` (the bank); `wVrNew` (an `.aq` read) by
rule 5. -/
theorem loadHalf (hc : CatH G) (x len : Nat) (L : List Geid) (ws : Wstate) (le : Lbl) (aq : Bool)
    (base : Int) (ts mts : List Nat) (hD : Dom G x len L ws) (hle : gxLbl G (x, len) = some le)
    (hR : lbIsR le = true) (haq : lbAq le = aq)
    (hrd : ∀ j t, ts[j]? = some t → ∃ v, greadsByte G (x, len) (accAddr base j) t v)
    (hLx : ∀ W, W ∈ L → W.1 = x → W.2 < len)
    (hby : ∀ j t', mts[j]? = some t' → t' = 0 ∨ SrOk G L x (x, len) aq ts j t') :
    Dom G x (len + 1) L (loadPostRun ws aq base mts) := by
  have hpo : ∀ r, fut G x (len + 1) r → WeakRvwmoGraph.gpo G (x, len) r := by
    rintro r ⟨hrx, hrk, aq', b, ts', vs', hrl'⟩
    exact SBAcq.gpoOf G (x, len) r le _ hle hrl' hrx.symm (show len < r.2 by omega)
  have hfv : ∀ a t, fwdView ws aq a t = t ∨ fwdView ws aq a t = 0 :=
    fun a t => fwdViewCases ws aq a t hD.bz
  -- the per-byte facts
  have hpt : ∀ p, p ∈ List.zipWith (fun (j : Nat) (t : Nat) => (base + (j : Int), t))
      (List.range' 0 mts.length) mts → ∃ j, mts[j]? = some p.2 ∧ p.1 = accAddr base j :=
    fun p hp => elemOfZipSeq base mts p hp
  -- (K1) coherence
  have hK1 : ∀ j t', mts[j]? = some t' → ∀ r, fut G x (len + 1) r → frB G r (accAddr base j) t' := by
    intro j t' hj r hr
    rcases hby j t' hj with h0 | ⟨t, htj, hle', -⟩
    · rw [h0]; exact frB0 hc.wf r _
    · obtain ⟨v, hrdj⟩ := hrd j t htj
      refine frOfLe r _ t' (fun tr vr hrr => ?_)
      have := corr hc (x, len) r _ t tr v vr (hpo r hr) (futNoW x _ r hr _) hrdj hrr
      omega
  -- (K2) contributions gmo-before the read, or 0
  have hK2 : ∀ j t', mts[j]? = some t' → ∀ r b, fut G x (len + 1) r → gmoLt G (x, len) r →
      frB G r b (fwdView ws aq (accAddr base j) t') := by
    intro j t' hj r b hr hlt
    rcases hby j t' hj with h0 | ⟨t, htj, hle', h0 | ⟨W, hW, hWlt, hWle⟩ | ⟨haf, hteq, s, hs, hsx, hsL⟩⟩
    · subst h0; rcases hfv (accAddr base j) 0 with h | h <;> rw [h] <;> exact frB0 hc.wf r b
    · subst h0; rcases hfv (accAddr base j) 0 with h | h <;> rw [h] <;> exact frB0 hc.wf r b
    · rcases hfv (accAddr base j) t' with h | h <;> rw [h]
      · exact frOfGmo hc x _ r hr b W t' hW (gmoTrans W (x, len) r hWlt hlt) hWle
      · exact frB0 hc.wf r b
    · subst haf
      rw [hteq]
      obtain ⟨v, hrdj⟩ := hrd j t htj
      obtain ⟨hsG, hsix⟩ := gwriteAtInv G t s hc.wf.1 hs
      have hlv := hc.lv (x, len) (accAddr base j) t v hrdj
      have hsw : gwritesByte G s (accAddr base j) v := by
        cases t with
        | zero => simp [gwriteAt] at hs
        | succ i =>
          obtain ⟨s', hs', hsw, -⟩ := hlv.1
          rw [hs, Option.some.injEq] at hs'
          subst hs'; exact hsw
      have hbank := hD.bank (accAddr base j) s v hsL hsx hsw (fun W' u' hW' hW'x hw' => by
        rw [hsix]
        refine hlv.2 W' u' hw' (.inr ⟨hW'x, hLx W' hW' hW'x, ?_, by rw [hle]; rfl⟩)
        obtain ⟨l, _, _, _, hl, -⟩ := hw'
        rw [hl]; rfl)
      rw [hsix] at hbank
      rw [fwdViewHit ws (accAddr base j) t t 0 hbank rfl]
      exact frB0 hc.wf r b
  -- (K3) an `.aq` read's contributions
  have hK3 : aq = true → ∀ (j : Nat) t', mts[j]? = some t' → ∀ r b, fut G x (len + 1) r →
      gmoLt G (x, len) r → frB G r b t' := by
    intro haq1 j t' hj r b hr hlt
    rcases hby j t' hj with h0 | ⟨t, htj, hle', h0 | ⟨W, hW, hWlt, hWle⟩ | ⟨haf, -, -⟩⟩
    · rw [h0]; exact frB0 hc.wf r b
    · rw [h0]; exact frB0 hc.wf r b
    · exact frOfGmo hc x _ r hr b W t' hW (gmoTrans W (x, len) r hWlt hlt) hWle
    · rw [haq1] at haf; cases haf
  -- (K4) the pre-view
  have hK4 : dR G x (len + 1) (loadVpre ws aq) := by
    unfold loadVpre
    refine (maxclDR hc.wf x (len + 1)).2 _ _ (dRWk x len (len + 1) _ (by omega) hD.vrn) ?_
    cases aq with
    | false => exact (maxclDR hc.wf x (len + 1)).1
    | true =>
      show dR G x (len + 1) ws.wVRel
      intro r b hr
      rcases hD.vrel with h0 | ⟨W, hW, hWx, hWk, hWrl, hWle⟩
      · rw [h0]; exact frB0 hc.wf r b
      · have h1 := rcscBefore hc W (x, len) hWrl ⟨le, hle, by rw [haq]⟩ hWx hWk
        have h2 := acqBefore hc x (len + 1) (x, len) le hle rfl (Nat.lt_succ_self _) hR (by rw [haq]) r hr
        exact frOfGmo hc x _ r hr b W _ hW (gmoTrans W (x, len) r h1 h2) hWle
  -- the five conjuncts
  unfold loadPostRun loadPostBytes
  refine ⟨fun a => ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show dC G x (len + 1) a (coh (List.foldl _ ws _) a)
    apply loadFoldCoh' _ aq _ _ ws a (maxclDC hc.wf x (len + 1) a)
    · intro p hp hpa
      obtain ⟨j, hj, hp1⟩ := hpt p hp
      intro r hr; rw [← hpa, hp1]; exact hK1 j p.2 hj r hr
    · intro p hp hpa
      obtain ⟨j, hj, hp1⟩ := hpt p hp
      rcases hfv p.1 p.2 with h | h <;> rw [h]
      · intro r hr; rw [← hpa, hp1]; exact hK1 j p.2 hj r hr
      · exact (maxclDC hc.wf x (len + 1) a).1
    · exact dCWk x len (len + 1) a _ (by omega) (hD.coh a)
    · exact dRdC x (len + 1) a _ hK4
  · show dR G x (len + 1) (List.foldl _ ws _).wVrNew
    cases aq with
    | false =>
      rw [loadFoldVrNewPlain]; exact dRWk x len (len + 1) _ (by omega) hD.vrn
    | true =>
      apply loadFoldVrNew' _ true _ _ ws (maxclDR hc.wf x (len + 1))
      · intro p hp r b hr
        obtain ⟨j, hj, hp1⟩ := hpt p hp
        rw [fwdViewAq]
        exact hK3 rfl j p.2 hj r b hr
          (acqBefore hc x (len + 1) (x, len) le hle rfl (Nat.lt_succ_self _) hR haq r hr)
      · exact dRWk x len (len + 1) _ (by omega) hD.vrn
      · exact hK4
  · show relP G x (len + 1) (List.foldl _ ws _).wVRel
    rw [loadFoldVRel]; exact relPWk x len (len + 1) _ (by omega) hD.vrel
  · show dF G x (len + 1) true (List.foldl _ ws _).wVrOld
    apply loadFoldVrOld' _ aq _ _ ws (maxclDF hc.wf x (len + 1) true)
    · intro p hp r b hr hw
      obtain ⟨j, hj, hp1⟩ := hpt p hp
      rw [hp1]
      exact hK2 j p.2 hj r b hr
        (fenceBefore hc x (len + 1) true (x, len) le hle rfl (Nat.lt_succ_self _) (by simp [hR]) r hr hw)
    · exact dFWk x len (len + 1) true _ (by omega) hD.vro
    · exact dRdF x (len + 1) true _ hK4
  · show dF G x (len + 1) false (List.foldl _ ws _).wVwOld
    rw [loadFoldVwOld]; exact dFWk x len (len + 1) false _ (by omega) hD.vwo
  · show ∀ a tf vf, get? (List.foldl _ ws _).wFwd a = some (tf, vf) → vf = 0
    rw [loadFoldFwd]; exact hD.bz
  · show ∀ a W u, W ∈ L → W.1 = x → gwritesByte G W a u → _ → get? (List.foldl _ ws _).wFwd a = _
    rw [loadFoldFwd]; exact hD.bank

/-! ## 5.1 The fence: where the pending components are DELIVERED -/

theorem domFence (hc : CatH G) (x len : Nat) (L : List Geid) (ws : Wstate) (pr pw sr sw : Bool)
    (hD : Dom G x len L ws) (hle : gxLbl G (x, len) = some (LFence pr pw sr sw)) :
    Dom G x (len + 1) L (fencePost ws pr pw sr sw) := by
  have hdel : ∀ (rd : Bool) (V : Nat), dF G x len rd V → (if rd then pr else pw) = true → sr = true →
      dR G x (len + 1) V := by
    intro rd V h hb hsr r b hr
    have hr' := futWk x len (len + 1) r (by omega) hr
    have hlt : len < r.2 := hr.2.1
    subst hsr
    exact h r b hr' ⟨len, pr, pw, sw, Nat.le_refl _, hlt, hle, hb⟩
  refine ⟨fun a => dCWk x len (len + 1) a _ (by omega) (hD.coh a), ?_, relPWk x len (len + 1) _
    (by omega) hD.vrel, dFWk x len (len + 1) true _ (by omega) hD.vro,
    dFWk x len (len + 1) false _ (by omega) hD.vwo, hD.bz, hD.bank⟩
  exact fencePostVrNewPred _ ws pr pw sr sw (maxclDR hc.wf x (len + 1))
    (dRWk x len (len + 1) _ (by omega) hD.vrn)
    (fun hpr hsr => hdel true _ hD.vro (by simp [hpr]) hsr)
    (fun hpw hsr => hdel false _ hD.vwo (by simp [hpw]) hsr)

/-! ## 5.2 The masked timestamps of a forwarding load -/

theorem fwdMaskFromGet (sb : List SbEnt) (base : Int) : ∀ (ts : List Nat) (k j : Nat),
    (SbCand.fwdMaskFrom sb base k ts)[j]? =
      (ts[j]?).map (fun t => if (SbCand.fwdByte sb (accAddr base (k + j))).isSome then 0 else t)
  | [], _, _ => by simp [SbCand.fwdMaskFrom]
  | t :: ts, k, 0 => by simp [SbCand.fwdMaskFrom]
  | t :: ts, k, j + 1 => by
    simp only [SbCand.fwdMaskFrom, List.getElem?_cons_succ]
    rw [fwdMaskFromGet sb base ts (k + 1) j, show k + 1 + j = k + (j + 1) by omega]

theorem fwdMaskGet (sb : List SbEnt) (base : Int) (ts : List Nat) (j t'' : Nat) :
    (SbCand.fwdMask sb base ts)[j]? = some t'' →
    ∃ t', ts[j]? = some t' ∧
      t'' = if (SbCand.fwdByte sb (accAddr base j)).isSome then 0 else t' := by
  intro h
  unfold SbCand.fwdMask at h
  rw [fwdMaskFromGet sb base ts 0 j, Nat.zero_add] at h
  cases hj : ts[j]? with
  | none => rw [hj] at h; cases h
  | some t' =>
    rw [hj] at h
    exact ⟨t', rfl, (Option.some.inj h).symm⟩

/-! ## 5.3 The walk-level statements -/

/-- The load-step condition of the walk's read rule: every byte of the member label's timestamps `ts'` is
forwarded or satisfies `SrOk` against GF's `ts`. -/
def SrBytes (G : Gexec) (w : WS) (x : Nat) (aq : Bool) (base : Int) (ts ts' : List Nat) : Prop :=
  ∀ j t', ts'[j]? = some t' →
    (SbCand.fwdByte (w.σ.sb x) (accAddr base j)).isSome ∨ SrOk G (wrW w) x (hd w x) aq ts j t'

theorem relXLd (x : Prop) (l : Lbl) (aq' : Bool) (base' : Int) (ts' : List Nat) (vs' : List (BitVec 8)) :
    lblRelX x l (LLoad aq' base' ts' vs') → ∃ ts vs, l = LLoad aq' base' ts vs ∧ ts'.length = ts.length := by
  rintro (⟨-, h⟩ | ⟨-, h⟩)
  · cases l with
    | LLoad aq base ts vs => obtain ⟨rfl, rfl, -, hl⟩ := h; exact ⟨ts, vs, rfl, hl⟩
    | LStore => cases h
    | LFence => cases h
    | LRmw => exact h.elim
    | LIo => cases h
  · cases l with
    | LLoad aq base ts vs =>
      obtain ⟨h1, h2, h3, hl, -⟩ := h
      subst h3; rw [h1, h2]; exact ⟨ts, vs, rfl, hl⟩
    | _ => exact h.elim

theorem relXRmw (x : Prop) (l : Lbl) (aq rl : Bool) (base : Int) (ts : List Nat) (rvs wvs : List (BitVec 8))
    (kc : WmClass) : lblRelX x l (LRmw aq rl base ts rvs wvs kc) →
    ∃ ts0, l = LRmw aq rl base ts0 rvs wvs kc := by
  intro h
  rcases relXW x l _ h (.inr rfl) with he | ⟨aq1, rl1, b1, ts1, ts1', rvs1, wvs1, kc1, h1, h2, -⟩
  · exact ⟨ts, he.symm⟩
  · rw [h1]
    simp only [LRmw.injEq] at h2
    obtain ⟨rfl, rfl, rfl, -, rfl, rfl, rfl⟩ := h2
    exact ⟨ts1, rfl⟩

/-- **PRESERVATION ALONG A LANDING** in GF's write order (S-P), own or foreign. -/
theorem domLand {img : Image} {X : Geid → Prop} {w : WS} (hc : CatH G) (hI : Inv img w)
    (hpf : pfx G X w) (hW : wrW w <+: gwrites G) (i k : Nat) (p : Nat × SbEnt)
    (hp : (w.pend i)[k]? = some p) (hS : wrW w ++ [(i, p.1)] <+: gwrites G) (hrl : p.2.rl = true → glblIs G (i, p.1) lbRl)
    (x : Nat) : DomInv G w x → DomInv G (nextI w (.land i k)) x := by
  intro hD
  unfold DomInv at hD ⊢
  rw [rowsLand i k p hp, wrWLand hI i k p hp, wsLand i k p hp hI x]
  by_cases hx : x = i
  · subst hx
    rw [if_pos rfl]
    obtain ⟨rl, base, vs, kc, hl, hrow, hmsg⟩ := pendLblI hI hpf x p (List.mem_of_getElem? hp)
    have hlen : w.σ.ms.msLog.length = (wrW w).length := (SpikeSR.logAt img G w hI hW).1
    have hix : gwix G (x, p.1) = w.σ.ms.msLog.length + 1 := by
      rw [hlen]; exact wixOfNext _ _ hc.wf.1 hS
    have hk : p.1 < (w.rows x).length := lookup_lt_Some hrow
    have hD' : Dom G x (w.rows x).length (wrW w) { w.σ.ms.msWs x with wRelp := p.2.relp } :=
      domCongr x _ _ (w.σ.ms.msWs x) _ hD (fun _ => rfl) rfl rfl rfl rfl rfl
    have hH := storeHalf hc x _ (wrW w) _ (x, p.1) _ base vs p.2.rl hD' hS rfl hk hl rfl hrl
    rw [hix] at hH
    have hlp : SbCand.landPost (w.σ.ms.msWs x) p.2 (w.σ.ms.msLog.length + 1) =
        { storePostRun { w.σ.ms.msWs x with wRelp := p.2.relp } p.2.rl base vs.length
            (w.σ.ms.msLog.length + 1) with wRelp := (w.σ.ms.msWs x).wRelp } := by
      simp only [SbCand.landPost, hmsg]
    rw [hlp]
    exact domCongr x _ _ _ _ hH (fun _ => rfl) rfl rfl rfl rfl rfl
  · rw [if_neg hx]
    apply domL x _ (wrW w) _ _ ?_ hD
    intro W hWx
    constructor
    · intro h
      rcases List.mem_append.1 h with h | h
      · exact h
      · simp only [List.mem_singleton] at h; subst h; exact absurd hWx.symm hx
    · exact fun h => List.mem_append_left _ h

/-- **PRESERVATION ALONG AN EVENT**: GF's label `l` at the head; the member label related to it; an AMO is
GF's verbatim label and GF's next write (S-P); a load's bytes satisfy `SrBytes`. -/
theorem domEv {img : Image} {X : Geid → Prop} {w : WS} (hc : CatH G) (hI : Inv img w)
    (hW : wrW w <+: gwrites G) (s : Estep) (l : Lbl) (hl : gxLbl G (hd w s.esAg) = some l)
    (hrel : lblRelX (X (hd w s.esAg)) l s.esLb)
    (hamo : ∀ aq rl base ts rvs wvs kc, l = LRmw aq rl base ts rvs wvs kc →
      s.esLb = l ∧ wrW w ++ [hd w s.esAg] <+: gwrites G)
    (hld : ∀ aq base ts vs ts' vs', l = LLoad aq base ts vs → s.esLb = LLoad aq base ts' vs' →
      SrBytes G w s.esAg aq base ts ts')
    (x : Nat) : DomInv G w x → DomInv G (nextI w (.ev s)) x := by
  intro hD
  unfold DomInv at hD ⊢
  rw [rowsLenEv s x, wsEv s x, wrWEv hI s]
  obtain ⟨i, lb⟩ := s
  dsimp only at hl hrel hamo hld ⊢
  by_cases hx : x = i
  · rw [if_pos hx, if_pos hx]
    cases hx
    have hLx : ∀ W, W ∈ wrW w → W.1 = x → W.2 < (w.rows x).length := by
      intro W hW' hWx; have := wrWReal hI W hW'; rw [hWx] at this; exact this
    cases lb with
    | LStore rl base vs kc =>
      simp only [gmoEv, isSt, Bool.not_true, Bool.and_false, Bool.false_and, Bool.false_eq_true,
        if_false, List.append_nil, evWs]
      exact domWk x _ _ _ _ (by omega)
        (domCongr x _ _ _ _ hD (fun _ => rfl) rfl rfl rfl rfl rfl)
    | LFence pr pw sr sw =>
      have hlf := relXFence _ l pr pw sr sw hrel
      subst hlf
      simp only [gmoEv, lbIsMem, lbIsR, lbIsW, lbIsIo, Bool.or_false, Bool.false_and, Bool.false_eq_true,
        if_false, List.append_nil, evWs]
      exact domFence hc x _ _ _ pr pw sr sw hD hl
    | LIo kd base vs =>
      simp only [gmoEv, lbIsW, Bool.and_false, Bool.false_eq_true, if_false, List.append_nil, evWs]
      exact domWk x _ _ _ _ (by omega) hD
    | LLoad aq base ts' vs' =>
      obtain ⟨ts, vs, rfl, hlen⟩ := relXLd _ l aq base ts' vs' hrel
      have hsb := hld aq base ts vs ts' vs' rfl rfl
      simp only [gmoEv, lbIsW, Bool.and_false, Bool.false_eq_true, if_false, List.append_nil, evWs]
      have hshape := lblShape G hc.wf _ _ hl
      simp only at hshape
      refine loadHalf hc x _ (wrW w) _ _ aq base ts _ hD hl rfl rfl ?_ hLx ?_
      · intro j t htj
        have hjl : j < vs.length := by rw [hshape]; exact lookup_lt_Some htj
        exact ⟨vs[j], _, base, ts, vs, j, hl, rfl, htj, List.getElem?_eq_getElem hjl, rfl⟩
      · intro j t'' hj
        obtain ⟨t', htj', heq⟩ := fwdMaskGet _ base ts' j t'' hj
        by_cases hf : (SbCand.fwdByte (w.σ.sb x) (accAddr base j)).isSome = true
        · left; rw [heq, if_pos hf]
        · right
          rw [heq, if_neg hf]
          rcases hsb j t' htj' with h | h
          · exact absurd h hf
          · exact h
    | LRmw aq rl base ts rvs wvs kc =>
      obtain ⟨ts0, rfl⟩ := relXRmw _ l aq rl base ts rvs wvs kc hrel
      obtain ⟨heq, hS⟩ := hamo aq rl base ts0 rvs wvs kc rfl
      simp only [LRmw.injEq] at heq
      obtain ⟨-, -, -, hts, -⟩ := heq
      rw [← hts] at hl
      simp only [gmoEv, lbIsMem, lbIsR, lbIsW, isSt, Bool.true_or, Bool.not_false, Bool.and_self,
        if_true, evWs]
      obtain ⟨hwne, hwl, hrl'⟩ := rmwShape hc.wf _ aq rl base ts rvs wvs kc hl
      -- the read half
      have hrd : ∀ j t, ts[j]? = some t → ∃ v, greadsByte G (x, (w.rows x).length) (accAddr base j) t v := by
        intro j t htj
        have hjl : j < rvs.length := by rw [hrl']; exact lookup_lt_Some htj
        exact ⟨rvs[j], _, base, ts, rvs, j, hl, rfl, htj, List.getElem?_eq_getElem hjl, rfl⟩
      have hwrj : ∀ j (hj : j < ts.length), gwritesByte G (x, (w.rows x).length) (accAddr base j)
          (wvs[j]'(by rw [hwl]; exact hj)) :=
        fun j hj => ⟨_, base, wvs, j, hl, rfl, List.getElem?_eq_getElem _, rfl⟩
      have h1 := loadHalf hc x _ (wrW w) _ _ aq base ts ts hD hl rfl rfl hrd hLx (by
        intro j t' hj
        right
        refine ⟨t', hj, Nat.le_refl _, ?_⟩
        cases t' with
        | zero => exact .inl rfl
        | succ i =>
          right; left
          obtain ⟨v, hrdj⟩ := hrd j _ hj
          obtain ⟨src, hs⟩ : ∃ src, gwriteAt G (i + 1) = some src := by
            obtain ⟨⟨src, hs, -⟩, -⟩ := hc.lv _ _ _ _ hrdj; exact ⟨src, hs⟩
          obtain ⟨hsG, hsix⟩ := gwriteAtInv G _ src hc.wf.1 hs
          exact ⟨src, hsG, amoSrcLt hc _ _ _ v _ src hrdj (hwrj j (lookup_lt_Some hj)) hs,
            by omega⟩)
      -- the write half
      have hlen : w.σ.ms.msLog.length = (wrW w).length := (SpikeSR.logAt img G w hI hW).1
      have hix : gwix G (x, (w.rows x).length) = w.σ.ms.msLog.length + 1 := by
        rw [hlen]; exact wixOfNext _ _ hc.wf.1 hS
      have h2 := storeHalf hc x _ (wrW w) _ (x, (w.rows x).length) _ base wvs rl h1 hS rfl
        (Nat.lt_succ_self _) hl rfl (fun h => ⟨_, hl, by simp [lbRl, h]⟩)
      rw [hix] at h2
      exact domCongr x _ _ _ _ h2 (fun _ => rfl) rfl rfl rfl rfl rfl
  · rw [if_neg hx, if_neg hx]
    apply domL x _ (wrW w) _ _ ?_ hD
    intro W hWx
    constructor
    · intro h
      rcases List.mem_append.1 h with h | h
      · exact h
      · split at h
        · simp only [List.mem_singleton] at h; subst h; exact absurd hWx.symm hx
        · simp at h
    · exact fun h => List.mem_append_left _ h

end Pres

end SbDom

end Weak
