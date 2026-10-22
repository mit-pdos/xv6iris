/-
Weak: **allocproc route P, row P-W6 — the walk input `IssueCo` (F-PW6-1 (a), [OWN.149])**
(`PROGRESS-PW6.md` §2 F-PW6-1, §7 step 1; `notes/twin-machine-conformance.md` cell j;
`weakmach/proposal-A7.md` §3.4 (ii)).  Lean-only, no Rocq twin.  A PRIMED TWIN: nothing registered imports
this file.

**Spec first.**  RVWMO's per-byte store order `co` is any total order that ppo, fences and rf allow; two
harts' plain stores to one byte are NOT ordered by the order their instructions issued.  MachCSL-P (the tip)
IS: a plain store's entry is pushed on top of the byte's history at issue and lands bottom-up
(`MState.landFootOk`, `SbRealP.landBlockedForeign`), so two harts' same-byte pending stores land in ISSUE
order — STRONGER than RVWMO (`SbConfLit.sRun`).  The walk issues plain stores freely and lands them in GF's
co order (`SbOrd.landG`), so a realization of the walk on MachCSL needs, at every landing, that no FOREIGN
entry issued EARLIER on a common byte is still pending (`SbRealP.ForeignBelowLanded`).

**`SbIssueCo.IssueCo` (NAMED walk input; FAITHFUL as a statement — a program fact of xv6, WEAKER while
named)**: along the walk, a plain store of row `j` issued at item `k1` and a plain store of ANOTHER row `i`
issued at a later item `k2`, writing a common byte, are GF co-ordered BY ISSUE whenever the first is still
pending at `k2` (not yet in the member's gmo).  xv6's census (design §2.1, R45 A13): shared bytes are
written under a lock or by one designated hart; the previous holder's stores precede its release fence, so
they land before the next holder's AMO reads the landed release — its discharge is a later item, through
`SbBlocked.Hb` (the lock hand-off chain), like `NonCensusSrc`.

**`SbIssueCo.noForeignBelow` (the walk half of `ForeignBelowLanded`)**: at an ENABLED landing (`landG`)
of row `i`'s pending store `p`, no pending store of another row issued before `p` writes a byte `p`
writes — `IssueCo` puts it co-before `p`, and `landG`'s co-prefix clause makes every co-predecessor of `p`
landed.  The realization's stamp map (P-W6's `SimRelP`: MachCSL issue stamps follow the walk's issue
items) turns this into `ForeignBelowLanded` at the matching MachCSL landing.

Lean-only helpers `SbIssueCo.*`.
-/
import Weak.SbOrd

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open Lbl SbWalk SbAgree SbReplay SbOrd

namespace SbIssueCo

/-- The GF event the walk item at position `k` steps, if it is an event item: its row and that row's
length at the state before it. -/
def evAt (c : CandW) (k : Nat) : Option Geid :=
  match c.its[k]? with
  | some (.ev s) => some (s.esAg, ((stAt c k).rows s.esAg).length)
  | _ => none

/-- **`IssueCo` (NAMED walk input, F-PW6-1 (a))**: two different rows' plain stores on a common byte,
issued in walk order `k1 < k2` with the first still pending at `k2`, are GF co-ordered by issue. -/
def IssueCo (G : Gexec) (c : CandW) : Prop :=
  ∀ (k1 k2 : Nat) (e1 e2 : Geid) (l1 l2 : Lbl) (a : Int), k1 < k2 →
    evAt c k1 = some e1 → evAt c k2 = some e2 → e1.1 ≠ e2.1 →
    gxLbl G e1 = some l1 → gxLbl G e2 = some l2 → isSt l1 = true → isSt l2 = true →
    wrsB l1 a = true → wrsB l2 a = true → e1 ∉ (stAt c k2).gmo → gmoLt G e1 e2

/-- One item only appends to the member's gmo. -/
theorem gmoStep (w : WS) (it : Item) : w.gmo <+: (nextI w it).gmo := by
  cases it with
  | ev s => cases h : gmoEv s.esLb <;> simp [nextI, h]
  | land i k =>
    cases hp : (w.pend i)[k]? with
    | none => simp [nextI, hp]
    | some p => simp [nextI, hp]

/-- The member's gmo only grows along the walk. -/
theorem gmoMonoAt (c : CandW) (k : Nat) : ∀ k', k ≤ k' → (stAt c k).gmo <+: (stAt c k').gmo := by
  intro k' hk
  induction k' with
  | zero =>
    have : k = 0 := by omega
    subst this; exact List.prefix_refl _
  | succ k' ih =>
    rcases Nat.eq_or_lt_of_le hk with h | h
    · rw [h]; exact List.prefix_refl _
    · have h1 := ih (by omega)
      cases hi : c.its[k']? with
      | none =>
        have : stAt c (k' + 1) = stAt c k' := by
          show (match c.its[k']? with
            | some it => nextI (stAt c k') it
            | none => stAt c k') = _
          rw [hi]
        rw [this]; exact h1
      | some it =>
        rw [stAtSucc c k' it hi]
        exact h1.trans (gmoStep _ it)

/-- Every GF write of the byte gmo-before the first unlanded one at the top of a co prefix is landed. -/
theorem landedBelowTop (G : Gexec) (w : WS) (a : Int) (x s : Geid) (hnd : G.gxGmo.Nodup)
    (hpre : wrAtW w a ++ [s] <+: wrAtG G a) (hsW : s ∉ wrAtW w a) (hxG : x ∈ wrAtG G a)
    (hlt : gpos G x < gpos G s) : x ∈ wrAtW w a := by
  obtain ⟨T, hT⟩ := hpre
  have hsG : s ∈ wrAtG G a := by rw [← hT]; simp
  have h1 := (wrAtGLt G a x s hnd hxG hsG).2 hlt
  have hps : posOf (wrAtG G a) s = (wrAtW w a).length := by
    rw [← hT, List.append_assoc, posOfAppNot _ _ s hsW]
    simp [posOf]
  have hget := posOfGet _ x hxG
  have hlt' : posOf (wrAtG G a) x < (wrAtW w a).length := by omega
  rw [← hT, List.append_assoc] at hget hlt'
  rw [List.getElem?_append_left hlt'] at hget
  exact List.mem_of_getElem? hget

/-- **THE WALK HALF OF `ForeignBelowLanded`**: at an enabled landing of row `i`'s pending store `p`, no
pending store `q` of another row `j`, issued BEFORE `p` (items `k1 < k2`), writes a byte `p` writes. -/
theorem noForeignBelow {N : Nat} {img : Image} {X : Geid → Prop} {dev : List Geid} (pol : SbPol)
    (G : Gexec) (c : CandW) (hco : IssueCo G c) (hnd : G.gxGmo.Nodup)
    (hP : PInv N img G X dev (cur c)) (i k : Nat) (hg : landG pol G (cur c) i k)
    (p : Nat × SbEnt) (hp : ((cur c).pend i)[k]? = some p)
    (j : Nat) (q : Nat × SbEnt) (hq : q ∈ (cur c).pend j) (hji : j ≠ i)
    (k1 k2 : Nat) (h12 : k1 < k2) (hk2 : k2 ≤ c.its.length)
    (he1 : evAt c k1 = some (j, q.1)) (he2 : evAt c k2 = some (i, p.1))
    (l1 l2 : Lbl) (hl1 : gxLbl G (j, q.1) = some l1) (hl2 : gxLbl G (i, p.1) = some l2)
    (hs1 : isSt l1 = true) (hs2 : isSt l2 = true) (a : Int) (hw1 : wrsB l1 a = true)
    (hw2 : wrsB l2 a = true) (hr : rwrB (cur c).rows a (i, p.1) = true) : False := by
  have hqG : (j, q.1) ∉ (cur c).gmo := hP.inv.pendGmo j q hq
  have hq2 : (j, q.1) ∉ (stAt c k2).gmo := fun h =>
    hqG ((gmoMonoAt c k2 c.its.length hk2).subset h)
  have hlt := hco k1 k2 _ _ l1 l2 a h12 he1 he2 hji hl1 hl2 hs1 hs2 hw1 hw2 hq2
  obtain ⟨p', hp', -, hb⟩ := hg
  rw [hp, Option.some.injEq] at hp'
  subst hp'
  have hpre := (hb a hr).1
  have hpm : p ∈ (cur c).pend i := List.mem_of_getElem? hp
  have hsW : (i, p.1) ∉ wrAtW (cur c) a := fun h => hP.inv.pendGmo i p hpm (List.mem_filter.1 h).1
  have hxG : (j, q.1) ∈ wrAtG G a :=
    List.mem_filter.2 ⟨hlt.1, by simp only [gwrB, hl1]; exact hw1⟩
  have hin := landedBelowTop G (cur c) a _ _ hnd hpre hsW hxG hlt.2.2
  exact hqG (List.mem_filter.1 hin).1

#print axioms Weak.SbIssueCo.noForeignBelow

end SbIssueCo

end Weak
