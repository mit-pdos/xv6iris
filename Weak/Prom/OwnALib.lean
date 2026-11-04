/-
Weak/Prom: **track (a), the resource library: dead messages, deposit slots, the owned-read lemma** (stage S4a;
plan rev 7 §3 "Resource part, an invariant access, pre-allocated", "The deposit", "Opening", "Points-to, a
hypothesis to validate", R-a1).

* `deadInv g t` — a message the program protocol never fulfils: its `pend` sits in an invariant that may be
  surrendered to the doom box (`dead_doom`: reading it dooms the branch) and that contradicts its `shot`
  (`dead_shot`: seeing it fulfilled dooms the branch).
* `slotInv g t R γc` — THE DEPOSIT SLOT of message `t` (plan §3, pre-allocated at adequacy start, one per `t`):
  `inv (slotN.@t) (pend t ∨ (shot t ∗ (R ∨ token γc)))`.  The author deposits `R` exactly at its fulfil
  (`slot_deposit`: it must take `pend t` out to shoot it, and the lifting lemma requires `shot t` at the fulfil).
  A reader that knows `shot t` (the frontier rule) and holds the claim token `token γc` swaps it for `R`
  (`slot_claim`).  "Only the claim-token holder gets R_t" (plan §3): `R` is exclusive once claimed — two claims
  need two tokens (G4 (5), OwnANeg.lean).  `R` is fixed when the slot is allocated; a deposit that must name ghost
  state allocated later uses a saved proposition for `R` (plan rev-4 σ_t; G4 (4), not yet done).
* `load_owned` — THE OWNED READ (plan R-a1, pure): an `n`-byte load at `x` whose pre-view covers the latest owned
  write `lw` returns `lw`'s bytes, or one of its bytes reads a message ABOVE `lw` that touches the location (a
  message whose `pend` the points-to holds, or a dead one — either way the branch is doomed).
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Prom.OwnAKit
import Iris.Instances.Lib.Token
import Iris.Instances.Lib.FUpd

namespace Weak.Prom.OA

open MachCSL MachCSL.Stdpp Iris.Std
open Weak (Image Dsrc)
open Weak.Prom Weak.Prom.PF
open PLabel
open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode

/-! ## 1. Namespaces -/

def deadN : Namespace := ndot nroot "promDead"
def slotN : Namespace := ndot nroot "promSlot"

theorem doomN_dead (t : Nat) : (↑doomN : CoPset) ⊆ ⊤ \ ↑(ndot deadN t) := by
  have hd : (↑(ndot deadN t) : CoPset) ## ↑doomN :=
    ndot_preserve_disjoint_l t (ndot_ne_disjoint nroot (by decide))
  intro p hp
  rw [CoPset.in_diff]
  exact ⟨CoPset.subseteq_top p hp, fun hc => hd p ⟨hc, hp⟩⟩

/-! ## 2. Dead messages and deposit slots -/

section inv

variable {hlc : HasLC} {GF : BundledGFunctors} [GhostVarG GF HSt] [GhostVarG GF Bool] [TokenG GF]
  [InvGS_gen hlc GF]

/-- A DEAD message: its `pend` (or doom) in an invariant. -/
def deadInv (g : AGN) (t : Nat) : IProp GF := inv (ndot deadN t) iprop(pend g t ∨ dshot g)

/-- THE DEPOSIT SLOT of message `t` with content `R` and claim token `γc` (plan §3). -/
def slotInv (g : AGN) (t : Nat) (R : IProp GF) (γc : GName) : IProp GF :=
  inv (ndot slotN t) iprop(pend g t ∨ (shot g t ∗ (R ∨ token γc)))

instance (g : AGN) (t : Nat) : Persistent (deadInv (GF := GF) g t) := by unfold deadInv; infer_instance
instance (g : AGN) (t : Nat) (R : IProp GF) (γc : GName) : Persistent (slotInv g t R γc) := by
  unfold slotInv; infer_instance

/-- Allocate a dead message. -/
theorem dead_alloc (g : AGN) (t : Nat) : pend (GF := GF) g t ⊢ |={⊤}=> deadInv g t := by
  iintro Hp
  unfold deadInv
  iapply inv_alloc
  inext; ileft; iexact Hp

/-- Allocate a deposit slot. -/
theorem slot_alloc (g : AGN) (t : Nat) (R : IProp GF) (γc : GName) : pend (GF := GF) g t ⊢ |={⊤}=> slotInv g t R γc := by
  iintro Hp
  unfold slotInv
  iapply inv_alloc
  inext; ileft; iexact Hp

/-- READING A DEAD MESSAGE dooms the branch (its `pend` goes to the doom box). -/
theorem dead_doom (g : AGN) (M : List PMsg) (t : Nat) (ht : 1 ≤ t ∧ t ≤ M.length) :
    doomInv (GF := GF) g M ∗ deadInv g t ⊢ |={⊤}=> dshot g := by
  iintro ⟨#Hdoom, #Hd⟩
  unfold deadInv
  imod inv_acc_timeless (E := ⊤) CoPset.subseteq_top $$ Hd with ⟨Hb, Hclose⟩
  icases Hb with (Hp | #Hs)
  · imod doom (doomN_dead t) g M t ht $$ [Hp] with #Hs
    · iframe Hdoom Hp
    imod Hclose $$ [] with -
    · iright; iexact Hs
    imodintro; iexact Hs
  · imod Hclose $$ [] with -
    · iright; iexact Hs
    imodintro; iexact Hs

/-- A FULFILLED DEAD MESSAGE dooms the branch. -/
theorem dead_shot (g : AGN) (t : Nat) : deadInv (GF := GF) g t ∗ shot g t ⊢ |={⊤}=> dshot g := by
  iintro ⟨#Hd, #Hsh⟩
  unfold deadInv
  imod inv_acc_timeless (E := ⊤) CoPset.subseteq_top $$ Hd with ⟨Hb, Hclose⟩
  icases Hb with (Hp | #Hs)
  · iexfalso
    iapply pend_shot
    iframe Hp Hsh
  · imod Hclose $$ [] with -
    · iright; iexact Hs
    imodintro; iexact Hs

end inv

section slot

variable {GF : BundledGFunctors} [GhostVarG GF HSt] [GhostVarG GF Bool] [TokenG GF] [InvGS GF]

/-- THE DEPOSIT (plan §3 "The deposit"): the author puts `R` into slot `t` and obtains `shot g t` (which its fulfil
of `t` must hand back). -/
theorem slot_deposit (g : AGN) (t : Nat) (R : IProp GF) (γc : GName) :
    slotInv (GF := GF) g t R γc ∗ R ∗ £ 1 ⊢ |={⊤}=> shot g t := by
  iintro ⟨#Hs, HR, Hc⟩
  unfold slotInv
  imod inv_acc (E := ⊤) CoPset.subseteq_top $$ Hs with ⟨Hb, Hclose⟩
  imod (lc_fupd_elim_later (E := ⊤ \ ↑(ndot slotN t)) (P := iprop(pend g t ∨ (shot g t ∗ (R ∨ token γc)))))
    $$ Hc Hb with Hb
  icases Hb with (Hp | ⟨#Hsh, HB⟩)
  · imod shoot $$ Hp with #Hsh
    imod Hclose $$ [HR] with -
    · inext; iright; iframe Hsh; ileft; iexact HR
    imodintro; iexact Hsh
  · imod Hclose $$ [HB] with -
    · inext; iright; iframe Hsh; iexact HB
    imodintro; iexact Hsh

/-- THE CLAIM (plan §3 "Opening"): a hart that knows `shot g t` and holds the claim token swaps it for `R`. -/
theorem slot_claim (g : AGN) (t : Nat) (R : IProp GF) (γc : GName) :
    slotInv (GF := GF) g t R γc ∗ shot g t ∗ token γc ∗ £ 1 ⊢ |={⊤}=> R := by
  iintro ⟨#Hs, #Hsh, Ht, Hc⟩
  unfold slotInv
  imod inv_acc (E := ⊤) CoPset.subseteq_top $$ Hs with ⟨Hb, Hclose⟩
  imod (lc_fupd_elim_later (E := ⊤ \ ↑(ndot slotN t)) (P := iprop(pend g t ∨ (shot g t ∗ (R ∨ token γc)))))
    $$ Hc Hb with Hb
  icases Hb with (Hp | ⟨_, (HR | Ht')⟩)
  · iexfalso
    iapply pend_shot
    iframe Hp Hsh
  · imod Hclose $$ [Ht] with -
    · inext; iright; iframe Hsh; iright; iexact Ht
    imodintro; iexact HR
  · iexfalso
    iapply token_exclusive
    iframe Ht Ht'

end slot

/-! ## 3. The owned read (pure) -/

/-- Message `m` touches byte `a`: writes it, or is a cache-block operation covering it. -/
def msgTouches (m : PMsg) (a : Int) : Prop :=
  (m.byteAt a).isSome = true ∨ ∃ k len, m.cls = .cmo k len ∧ m.pa ≤ a ∧ a < m.pa + len

/-- ONE BYTE: an answer whose floor covers the latest owned write `lw` (a non-cmo message writing `a`) is `lw`,
or a message above `lw` touching `a`. -/
theorem src_ge_owner {img : Image} {M : List PMsg} {a : Int} {t lw fl : Nat} {v : BitVec 8} {mw : PMsg}
    (hlw1 : 1 ≤ lw) (hmw : msgAt M lw = some mw) (hwa : (mw.byteAt a).isSome = true) (hnc : notCmo mw.cls = true)
    (hfl : lw ≤ fl) (hb : memByte img M t a = some v) (hr : ¬ writesIn M a t fl ∨ invalRead M a t fl) :
    t = lw ∨ ∃ s, lw < s ∧ ∃ m, msgAt M s = some m ∧ msgTouches m a := by
  have hwlw : ∀ lo, lo < lw → writesIn M a lo fl := by
    intro lo hlo
    obtain ⟨k, rfl⟩ : ∃ k, lw = k + 1 := ⟨lw - 1, by omega⟩
    exact ⟨k + 1, hlo, hfl, mw, by simpa [msgAt] using hmw, hwa⟩
  rcases hr with hr | ⟨ti, ⟨mi, ki, leni, hmi, hcls, _, h1, h2⟩, hlt, hnw, _, _⟩
  · by_cases h : t < lw
    · exact absurd (hwlw t h) hr
    · by_cases he : t = lw
      · exact .inl he
      · obtain ⟨k, rfl⟩ : ∃ k, t = k + 1 := ⟨t - 1, by omega⟩
        obtain ⟨m, hm, hba⟩ := Option.bind_eq_some_iff.1 (by simpa [memByte] using hb)
        exact .inr ⟨k + 1, by omega, m, by simpa [msgAt] using hm, .inl (by rw [hba]; rfl)⟩
  · -- the invalidate clause: the invalidate `ti` is above `lw`
    by_cases h : ti < lw
    · exact absurd (hwlw ti h) hnw
    · by_cases he : ti = lw
      · subst he
        obtain ⟨k, hk⟩ : ∃ k, ti = k + 1 := ⟨ti - 1, by omega⟩
        rw [hk] at hmi hmw
        simp only [msgAt, Nat.add_sub_cancel] at hmi hmw
        rw [hmi] at hmw; cases hmw
        rw [hcls] at hnc; cases hnc
      · obtain ⟨k, hk⟩ : ∃ k, ti = k + 1 := ⟨ti - 1, by omega⟩
        refine .inr ⟨ti, by omega, mi, ?_, .inr ⟨ki, leni, hcls, h1, h2⟩⟩
        rw [hk] at hmi ⊢; simpa [msgAt] using hmi
      -- (the answer `t < ti` is below the invalidate; the clause's own source is irrelevant here)

/-- The bytes a message `m` with base `p` and data `d` holds, from offset `k`. -/
theorem byteAt_off {m : PMsg} {p : Int} {k : Nat} (hp : m.pa = p) : m.byteAt (p + k) = m.data[k]? := by
  unfold PMsg.byteAt
  rw [hp, if_pos (by omega)]
  congr 1
  omega

/-- **THE OWNED READ** (plan R-a1): a load at `x` whose every byte's floor covers `lw` (the latest owned write, a
non-cmo message with base `x` writing at least the load's bytes) returns `lw`'s bytes, or reads a message above
`lw` touching one of its bytes. -/
theorem load_owned {img : Image} {M : List PMsg} {ws : PState} {vpre : Nat} {x : Int} {lw : Nat} {mw : PMsg}
    (hlw1 : 1 ≤ lw) (hmw : msgAt M lw = some mw) (hpa : mw.pa = x) (hnc : notCmo mw.cls = true)
    (hv : lw ≤ vpre) :
    ∀ (k : Nat) (tvs : List (Nat × BitVec 8)), k + tvs.length ≤ mw.data.length →
      bytesAll (fun a t v => memByte img M t a = some v ∧
        ((∃ fl, vpre ≤ fl ∧ ¬ writesIn M a t fl) ∨ (∃ fl, vpre ≤ fl ∧ invalRead M a t fl))) (x + k) tvs →
      tvs.map Prod.snd = (mw.data.drop k).take tvs.length ∨
        ∃ s, lw < s ∧ ∃ m, msgAt M s = some m ∧ ∃ j, j < k + tvs.length ∧ msgTouches m (x + j) := by
  intro k tvs
  induction tvs generalizing k with
  | nil => intro _ _; exact .inl (by simp)
  | cons tv r ih =>
    obtain ⟨t, v⟩ := tv
    intro hlen ⟨⟨hb, hr⟩, hrest⟩
    have hk : k < mw.data.length := by simp at hlen; omega
    have hwa : (mw.byteAt (x + k)).isSome = true := by
      rw [← hpa, byteAt_off rfl, List.getElem?_eq_getElem hk]; rfl
    have hsrc : t = lw ∨ ∃ s, lw < s ∧ ∃ m, msgAt M s = some m ∧ msgTouches m (x + k) := by
      rcases hr with ⟨fl, hfl, h⟩ | ⟨fl, hfl, h⟩
      · exact src_ge_owner hlw1 hmw hwa hnc (by omega) hb (.inl h)
      · exact src_ge_owner hlw1 hmw hwa hnc (by omega) hb (.inr h)
    rcases hsrc with heq | ⟨s0, hlt, m, hm, htch⟩
    · have ih' := ih (k + 1) (by simp at hlen; omega) (by rw [(by omega : x + ((k + 1 : Nat) : Int) = x + k + 1)]; exact hrest)
      rcases ih' with h | ⟨s, hs, m, hm, j, hj, htj⟩
      · refine .inl ?_
        rw [heq] at hb
        obtain ⟨kk, hkk⟩ : ∃ kk, lw = kk + 1 := ⟨lw - 1, by omega⟩
        rw [hkk] at hb hmw
        simp only [msgAt] at hmw
        simp only [memByte, hmw, Option.bind_some] at hb
        rw [← hpa, byteAt_off rfl, List.getElem?_eq_getElem hk] at hb
        have hv' : mw.data[k] = v := Option.some.inj hb
        simp only [List.map_cons, List.length_cons]
        rw [List.drop_eq_getElem_cons hk, List.take_succ_cons, hv', h]
      · exact .inr ⟨s, hs, m, hm, j, by simp; omega, htj⟩
    · exact .inr ⟨s0, hlt, m, hm, k, by simp, htch⟩

/-- `loadOk` gives the weakened byte predicate of `load_owned` (both floors are at least the pre-view). -/
theorem loadOk_weak {img : Image} {M : List PMsg} {ws : PState} {vpre : Nat} {base : Int}
    {tvs : List (Nat × BitVec 8)} (h : loadOk img M ws vpre base tvs) :
    bytesAll (fun a t v => memByte img M t a = some v ∧
      ((∃ fl, vpre ≤ fl ∧ ¬ writesIn M a t fl) ∨ (∃ fl, vpre ≤ fl ∧ invalRead M a t fl))) base tvs := by
  unfold loadOk at h
  refine bytesAll_mono (fun a t v hp => ⟨hp.1, ?_⟩) base tvs h
  rcases hp.2 with h1 | h1
  · exact .inl ⟨_, by split <;> omega, h1⟩
  · exact .inr ⟨_, by omega, h1⟩

end Weak.Prom.OA
