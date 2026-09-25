/-
`filewrite`'s CHUNK LOOP INVARIANT and its five moves (stage file of
`ProofFilewrite`).  A port of Rocq `ProofFilewriteChain.v`
(`/shared/xv6rocq/iris/ProofFilewriteChain.v`), whole.

Rocq's header, kept because the reasons are the content:

> `fw_au_raw Γ i γo n M ua Q t p x` is "`p` chunks have fired, they wrote
> `t` bytes in total, their concatenation is the caller's own run at `ua`,
> and here is the rest of the chain, resuming `x` nodes past them" -- `x`
> is 0 on every loop entry and becomes 1 only at the exit a SHORT chunk
> forces, when its offset move spent the chain's partial arm.  It is the
> ONLY iProp the loop carries; the two facts that make it a loop INVARIANT
> are Coq-level and ride as ordinary premises of the loop:
>
>     t = iz   /\   t = FW_MAX * Z.of_nat p
>
> THERE IS NO RECEIPT ACCUMULATOR.  The state carries the chain and the
> BYTES; everything a caller wants per chunk it records in the PREFIX
> CURSOR `Q`.
>
> THE FIVE MOVES: start it (`_init`), spend one node's FULL arm at a
> chunk's fire (`_take`), spend one node's PARTIAL arm at a short chunk's
> offset move (`_spend_part`), and read it off at each of the two exits
> (`_ok` at `t = n`, `_fail` at `t < n` or at the never-entered loop).

## Deviations from Rocq

1. `t` (the fired total) is a `Nat` (it is a byte count; Rocq's `Z` came
   with a `0 ≤ t` premise, now gone); the tie `t = FW_MAX * p` is stated at
   `Int`.  Rocq's `add_vec_int ua t` is `ua + BitVec.ofNat 64 t`
   (`SysWriteDefs.ubytesAt_app`'s spelling).
2. Names: `fw_au_raw` → `fwrRaw`, `_init/_take/_spend_part/_ok/_fail` →
   `fwrRaw_init/_take/_spendPart/_ok/_fail` (the `fw_` prefix is taken:
   FsWords / freewalk).  `Global Typeclasses Opaque` has no Lean analogue.
-/
import Xv6.SpecFilewrite

namespace Xv6

open Iris Iris.BI Iris.ProofMode MachCSL

set_option linter.unusedSectionVars false

section FilewriteChain
variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [FsTopG GF] [OffboxG GF] [Appcfg GF]

/-- THE LOOP'S CARRIED COMMIT STATE (Rocq `fw_au_raw`). -/
def fwrRaw (Γ : FsViewNames GF) (i : Nat) (γo : GName) (P : UPtd) (n : Int) (M : Nat → List (BitVec 8))
    (ua : BitVec 64) (Q : Nat → IProp GF) (t p x : Nat) : IProp GF :=
  iprop(∃ bss : List (List (BitVec 8)),
    ⌜bss.length = p⌝ ∗ ⌜bss.flatten.length = t⌝ ∗ ⌜p + x ≤ wchunks n⌝ ∗ ⌜x ≤ 1⌝ ∗
    -- THE CONTENT HALF (RULING A): what has been spliced so far IS the
    -- caller's own run at `ua`
    ⌜ubytesAt M ua bss.flatten⌝ ∗
    awriteChainAt (hlc := hlc) Γ appE i γo M ua P n Q (p + x) (wchunks n - p - x))

/-- Rocq `fw_au_raw_init`. -/
theorem fwrRaw_init (Γ : FsViewNames GF) (i : Nat) (γo : GName) (P : UPtd) (n : Int)
    (M : Nat → List (BitVec 8)) (ua : BitVec 64) (Q : Nat → IProp GF) :
    awriteChain (hlc := hlc) Γ appE i γo M ua n Q 0 (wchunks n) ⊢ fwrRaw Γ i γo P n M ua Q 0 0 0 := by
  unfold fwrRaw
  iintro Hc
  ihave Hc := awriteChainAt_of Γ appE i γo M ua n Q 0 (wchunks n) P $$ Hc
  iexists []
  isplitr
  · ipureintro; rfl
  isplitr
  · ipureintro; rfl
  isplitr
  · ipureintro; omega
  isplitr
  · ipureintro; omega
  isplitr
  · ipureintro; exact ubytesAt_nil M ua
  iexact Hc

/-- ONE CHUNK'S FIRE, both halves (Rocq `fw_au_raw_take`): the head node's
FULL arm comes out at the index the chain handed it out at (its
continuation IS the rest of the chain), and the closer takes that rest back
with the chunk's bytes.  The chain's own `Q p` conjunct is DROPPED -- the
kernel eliminates to an arm when it fires. -/
theorem fwrRaw_take (Γ : FsViewNames GF) (i : Nat) (γo : GName) (P : UPtd) (n : Int)
    (M : Nat → List (BitVec 8)) (ua : BitVec 64) (Q : Nat → IProp GF) (t p : Nat)
    (htn : (t : Int) < n) (htie : (t : Int) = FW_MAX * p) :
    fwrRaw (hlc := hlc) Γ i γo P n M ua Q t p 0 ⊢
      awriteFullAt Γ appE i γo M ua p (awriteChainAt Γ appE i γo M ua P n Q (p + 1) (wchunks n - (p + 1))) ∗
      (∀ bs : List (BitVec 8),
        ⌜ubytesAt M (ua + BitVec.ofNat 64 t) bs⌝ -∗
        awriteChainAt Γ appE i γo M ua P n Q (p + 1) (wchunks n - (p + 1)) -∗
        fwrRaw Γ i γo P n M ua Q (t + bs.length) (p + 1) 0) := by
  have hsp := wriCount_step n t p (by omega) htn htie
  unfold fwrRaw
  iintro ⟨%bss, %hlen, %htot, %hp, %hx, %hby, Hcm⟩
  have hcnt : wchunks n - p - 0 = (wchunks n - (p + 1)) + 1 := by omega
  rw [hcnt, Nat.add_zero, awriteChainAt_S]
  icases Hcm with ⟨-, Hhead, -⟩
  iframe Hhead
  iintro %bs %hbyc Htail
  iexists bss ++ [bs]
  isplitr
  · ipureintro; simp [hlen]
  isplitr
  · ipureintro; simp [htot]
  isplitr
  · ipureintro; omega
  isplitr
  · ipureintro; omega
  isplitr
  · ipureintro
    rw [List.flatten_append, List.flatten_singleton]
    exact ubytesAt_app M ua bss.flatten bs hby (by rw [htot]; exact hbyc)
  rw [Nat.add_zero, Nat.sub_zero]
  iexact Htail

/-- ONE SHORT CHUNK'S INSTANT (Rocq `fw_au_raw_spend_part`): the head
node's PARTIAL arm comes out, and the closer takes the rest of the chain
back one node further on. -/
theorem fwrRaw_spendPart (Γ : FsViewNames GF) (i : Nat) (γo : GName) (P : UPtd) (n : Int)
    (M : Nat → List (BitVec 8)) (ua : BitVec 64) (Q : Nat → IProp GF) (t p : Nat)
    (htn : (t : Int) < n) (htie : (t : Int) = FW_MAX * p) :
    fwrRaw (hlc := hlc) Γ i γo P n M ua Q t p 0 ⊢
      awritePartAt Γ appE i γo M ua P n p (awriteChainAt Γ appE i γo M ua P n Q (p + 1) (wchunks n - (p + 1))) ∗
      (awriteChainAt Γ appE i γo M ua P n Q (p + 1) (wchunks n - (p + 1)) -∗
        fwrRaw Γ i γo P n M ua Q t p 1) := by
  have hsp := wriCount_step n t p (by omega) htn htie
  unfold fwrRaw
  iintro ⟨%bss, %hlen, %htot, %hp, %hx, %hby, Hcm⟩
  have hcnt : wchunks n - p - 0 = (wchunks n - (p + 1)) + 1 := by omega
  rw [hcnt, Nat.add_zero, awriteChainAt_S]
  icases Hcm with ⟨-, -, Hpart⟩
  iframe Hpart
  iintro Htail
  iexists bss
  isplitr
  · ipureintro; exact hlen
  isplitr
  · ipureintro; exact htot
  isplitr
  · ipureintro; omega
  isplitr
  · ipureintro; omega
  isplitr
  · ipureintro; exact hby
  have hcnt' : wchunks n - p - 1 = wchunks n - (p + 1) := by omega
  rw [hcnt']
  iexact Htail

/-- THE OK EXIT (Rocq `fw_au_raw_ok`). -/
theorem fwrRaw_ok (Γ : FsViewNames GF) (i : Nat) (γo : GName) (P : UPtd) (n : Int)
    (M : Nat → List (BitVec 8)) (ua : BitVec 64) (Q : Nat → IProp GF) (t p : Nat)
    (hn : (t : Int) = n) :
    fwrRaw (hlc := hlc) Γ i γo P n M ua Q t p 0 ⊢ writePostOkAt (hlc := hlc) Γ i γo P n M ua Q := by
  unfold fwrRaw writePostOkAt
  iintro ⟨%bss, %hlen, %htot, %hp, %hx, %hby, Hcm⟩
  iexists bss
  isplitr
  · ipureintro; rw [htot]; exact hn
  isplitr
  · ipureintro; omega
  isplitr
  · ipureintro; exact hby
  rw [hlen, Nat.add_zero, Nat.sub_zero]
  iexact Hcm

/-- THE FAIL EXIT, AT BOTH OF ITS TWO SHAPES (Rocq `fw_au_raw_fail`): the
loop's own short-write break (`t < n`), and the never-entered loop at
`n < 0` (`p = 0`). -/
theorem fwrRaw_fail (Γ : FsViewNames GF) (i : Nat) (γo : GName) (P : UPtd) (n : Int)
    (M : Nat → List (BitVec 8)) (ua : BitVec 64) (Q : Nat → IProp GF) (t p x : Nat)
    (hex : (t : Int) < n ∨ (n < 0 ∧ p = 0)) :
    fwrRaw (hlc := hlc) Γ i γo P n M ua Q t p x ⊢ writePostFailAt (hlc := hlc) Γ i γo P n M ua Q := by
  unfold fwrRaw writePostFailAt
  iintro ⟨%bss, %hlen, %htot, %hp, %hx, %hby, Hcm⟩
  iexists bss, x
  isplitr
  · ipureintro
    rcases hex with h | ⟨h, h0⟩
    · left; rw [htot]; exact h
    · right; refine ⟨h, ?_⟩
      exact List.eq_nil_of_length_eq_zero (by rw [hlen, h0])
  isplitr
  · ipureintro; omega
  isplitr
  · ipureintro; exact hx
  isplitr
  · ipureintro; exact hby
  rw [hlen]
  iexact Hcm

end FilewriteChain

end Xv6
