/-
The page allocator's invariant (the Rocq `KallocInv.v`).

`kmem.lock` protects `kmem.freelist`, a singly linked list of free 4 KiB
pages threaded through their first words.  The lock's payload is
`kmemRes γk`: the freelist word, the chain of pages it heads, and the
allocator's half of the availability ghost.  The ghost (`kallocAvail`)
lets a client who knows how many pages are free (`some n`) predict the
allocator's answer; a client who does not (`none`, after `sealAvail`)
gets a page or `0`.

The payload is a function of the context (`CtxId`), as every lock
payload is, so the chain is written over the context-parametric
`wordAtN`/`pageRestAt` (`wordPointsTo`/`byteBuf` at the ambient context).
-/
import Xv6.UartTrace
import MachCSL.CallConv
import MachCSL.CtxLaws
import MachCSL.WpStoreFree

namespace Xv6

open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode Std MachCSL

/-! ## The allocator's addresses -/

/-- `&kmem.lock`. -/
def kmemLockAddr : BitVec 64 := 0x80012410#64
/-- `&kmem.freelist` (`kmem.lock` is 24 bytes). -/
def kmemFreelistAddr : BitVec 64 := 0x80012428#64
/-- The linker's `end`: the first byte after the kernel image. -/
def kernelEndAddr : BitVec 64 := 0x80023640#64
/-- `PHYSTOP`. -/
def physTop : BitVec 64 := 0x88000000#64

/-- A page the allocator manages: 4 KiB aligned, between `end` and `PHYSTOP`
(the checks `kfree` panics on). -/
def pageValid (p : BitVec 64) : Prop :=
  p &&& 0xfff#64 = 0#64 ∧ ¬ p.ult kernelEndAddr ∧ p.ult physTop

/-- The allocator's ghost names: the availability counter (two halves) and
the pending token (owned while the count is tracked, discarded once sealed). -/
structure KmemNames where
  cnt : GName
  pend : GName

/-- The client's knowledge of the number of free pages after an operation. -/
def availInc (on : Option Nat) : Option Nat := on.map (· + 1)
def availDec (on : Option Nat) : Option Nat := on.map (· - 1)
/-- Whether the allocator may answer `0`. -/
def availZero (on : Option Nat) : Prop := on = none ∨ on = some 0

set_option linter.unusedSectionVars false

section
variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF]

/-! ## Context-parametric cells -/

/-- `wordPointsTo va n dq w` with the bytes at context `ξ` (the lock
payload's form; at `curCtx` it is `wordPointsTo` itself). -/
def wordAtN [CurCtx] (ξ : CtxId) (va : BitVec 64) (n : Nat) (dq : DFrac) (w : BitVec (8 * n)) : IProp GF := iprop%
  ∃ ppn : BitVec 44, kmapAt (vpnOf va) (kLeaf ppn .rw 0#1 0#1) ∗
    ⌜tierPin curTier ppn va ∧ va.toNat < 2 ^ 38 ∧ inRam (paOf ppn va) n ∧ va.toNat % n = 0⌝ ∗
    ctxBytes ξ (paOf ppn va) n dq w

theorem wordAtN_cur [CurCtx] (va : BitVec 64) (n : Nat) (dq : DFrac) (w : BitVec (8 * n)) :
    wordAtN (GF := GF) curCtx va n dq w = wordPointsTo va n dq w := rfl

instance instCtxMorphWordAtN [CurCtx] (va : BitVec 64) (n : Nat) (dq : DFrac) (w : BitVec (8 * n)) :
    CtxMorph (GF := GF) (fun ξ => wordAtN ξ va n dq w) :=
  instCtxMorphExists (fun (ppn : BitVec 44) ξ => iprop(kmapAt (vpnOf va) (kLeaf ppn .rw 0#1 0#1) ∗
    ⌜tierPin curTier ppn va ∧ va.toNat < 2 ^ 38 ∧ inRam (paOf ppn va) n ∧ va.toNat % n = 0⌝ ∗
    ctxBytes ξ (paOf ppn va) n dq w))

/-- The bytes `8 ..< 4096` of a free page, at context `ξ` (`byteBuf` of the
page's tail at `curCtx`). -/
def pageRestAt [CurCtx] (ξ : CtxId) (p : BitVec 64) : IProp GF := iprop%
  ∃ bs : List (BitVec 8), ⌜bs.length = 4088⌝ ∗
    [∗list] j ↦ b ∈ bs, wordAtN ξ (p + 8#64 + BitVec.ofNat 64 j) 1 (DFrac.own 1) b

theorem pageRestAt_cur [CurCtx] (p : BitVec 64) :
    pageRestAt (GF := GF) curCtx p =
      iprop(∃ bs : List (BitVec 8), ⌜bs.length = 4088⌝ ∗ byteBuf (p + 8#64) (DFrac.own 1) bs) := rfl

instance instCtxMorphPageRestAt [CurCtx] (p : BitVec 64) :
    CtxMorph (GF := GF) (fun ξ => pageRestAt ξ p) :=
  @instCtxMorphExists hlc GF _ _ (fun (bs : List (BitVec 8)) ξ => iprop(⌜bs.length = 4088⌝ ∗
    [∗list] j ↦ b ∈ bs, wordAtN ξ (p + 8#64 + BitVec.ofNat 64 j) 1 (DFrac.own 1) b))
    (fun bs => @instCtxMorphSep hlc GF _ (fun _ => iprop(⌜bs.length = 4088⌝)) _ (instCtxMorphConst _)
      (ctxMorph_bigSepL bs (fun j b ξ => wordAtN ξ (p + 8#64 + BitVec.ofNat 64 j) 1 (DFrac.own 1) b)
        (fun _ _ => inferInstance)))

/-- A whole page, owned (the `kfree` precondition; the ambient context). -/
def pageOwn [CurCtx] (p : BitVec 64) : IProp GF := iprop%
  ∃ bs : List (BitVec 8), ⌜bs.length = 4096⌝ ∗ byteBuf p (DFrac.own 1) bs

/-- **A whole VISIBILITY-FREE page** (the `kfree`-over-reclaimed-memory
precondition): 4096 mappable visibility-free bytes.  A valued page forgets
to it; the reclaimed page whose per-byte era keys are gone is one. -/
def pageFree [CurCtx] (p : BitVec 64) : IProp GF := iprop%
  ∃ bs : List (BitVec 8), ⌜bs.length = 4096⌝ ∗ bytesFree p bs

/-- An owned (valued) page forgets to a visibility-free one. -/
theorem pageOwn_pageFree [CurCtx] (p : BitVec 64) :
    pageOwn (GF := GF) p ⊢ pageFree p := by
  unfold pageOwn pageFree
  iintro ⟨%bs, %hbs, Hbuf⟩
  iexists bs
  isplit
  · ipureintro; exact hbs
  · iapply byteBuf_bytesFree p bs $$ Hbuf

/-! ## The freelist chain -/

/-- The chain of free pages from `head`: each page's first word is the next
page, the rest of the page is owned (its contents unconstrained). -/
def chainAt [CurCtx] (ξ : CtxId) : BitVec 64 → List (BitVec 64) → IProp GF
  | head, [] => iprop(⌜head = 0#64⌝)
  | head, p :: ps => iprop(⌜head = p ∧ pageValid p⌝ ∗
      ∃ nxt : BitVec 64, wordAtN ξ p 8 (DFrac.own 1) nxt ∗ pageRestAt ξ p ∗ chainAt ξ nxt ps)

theorem chainAt_nil [CurCtx] (ξ : CtxId) (head : BitVec 64) :
    chainAt (GF := GF) ξ head [] = iprop(⌜head = 0#64⌝) := rfl

theorem chainAt_cons [CurCtx] (ξ : CtxId) (head p : BitVec 64) (ps : List (BitVec 64)) :
    chainAt (GF := GF) ξ head (p :: ps) = iprop(⌜head = p ∧ pageValid p⌝ ∗
      ∃ nxt : BitVec 64, wordAtN ξ p 8 (DFrac.own 1) nxt ∗ pageRestAt ξ p ∗ chainAt ξ nxt ps) := rfl

theorem chainAt_morph [CurCtx] (ps : List (BitVec 64)) (head : BitVec 64) :
    CtxMorph (GF := GF) (fun ξ => chainAt ξ head ps) := by
  induction ps generalizing head with
  | nil => exact instCtxMorphConst _
  | cons p ps ih =>
    exact @instCtxMorphSep hlc GF _ (fun _ => iprop(⌜head = p ∧ pageValid p⌝)) _ (instCtxMorphConst _)
      (@instCtxMorphExists hlc GF _ _ (fun (nxt : BitVec 64) ξ =>
        iprop(wordAtN ξ p 8 (DFrac.own 1) nxt ∗ pageRestAt ξ p ∗ chainAt ξ nxt ps))
        (fun nxt => @instCtxMorphSep hlc GF _ _ _ inferInstance
          (@instCtxMorphSep hlc GF _ _ _ inferInstance (ih nxt))))

instance instCtxMorphChainAt [CurCtx] (ps : List (BitVec 64)) (head : BitVec 64) :
    CtxMorph (GF := GF) (fun ξ => chainAt ξ head ps) := chainAt_morph ps head

/-! ## The availability ghost -/

/-- The allocator's side of the count: its half while the count is
tracked, or the knowledge that it has been sealed. -/
def kmemAuth (γk : KmemNames) (n : Nat) : IProp GF := iprop%
  (γk.cnt ↪VAR{.own (1 : Qp).half} n) ∨ (γk.pend ↪VAR{.discard} ())

/-- The client's knowledge of the free count. -/
def kallocAvail (γk : KmemNames) : Option Nat → IProp GF
  | some n => iprop((γk.pend ↪VAR ()) ∗ (γk.cnt ↪VAR{.own (1 : Qp).half} n))
  | none => iprop(γk.pend ↪VAR{.discard} ())

theorem kallocAvail_some (γk : KmemNames) (n : Nat) :
    kallocAvail (GF := GF) γk (some n) = iprop((γk.pend ↪VAR ()) ∗ (γk.cnt ↪VAR{.own (1 : Qp).half} n)) := rfl
theorem kallocAvail_none (γk : KmemNames) :
    kallocAvail (GF := GF) γk none = iprop(γk.pend ↪VAR{.discard} ()) := rfl

instance kallocAvail_none_persistent (γk : KmemNames) : Persistent (kallocAvail (GF := GF) γk none) := by
  unfold kallocAvail; infer_instance

/-- Forgetting the count. -/
theorem kallocAvail_seal (γk : KmemNames) (n : Nat) :
    kallocAvail (GF := GF) γk (some n) ⊢ |==> kallocAvail γk none := by
  rw [kallocAvail_some, kallocAvail_none]
  iintro ⟨Hp, _⟩
  iapply ghost_var_persist $$ Hp

/-- The allocator's payload: the freelist word heads a chain of `pages`, and
the count is their number. -/
def kmemRes [CurCtx] (γk : KmemNames) (ξ : CtxId) : IProp GF := iprop%
  ∃ (head : BitVec 64) (pages : List (BitVec 64)),
    wordAtN ξ kmemFreelistAddr 8 (DFrac.own 1) head ∗ chainAt ξ head pages ∗ kmemAuth γk pages.length

instance instCtxMorphKmemRes [CurCtx] (γk : KmemNames) : CtxMorph (GF := GF) (kmemRes γk) :=
  @instCtxMorphExists hlc GF _ _ (fun (head : BitVec 64) ξ => iprop(∃ pages : List (BitVec 64),
      wordAtN ξ kmemFreelistAddr 8 (DFrac.own 1) head ∗ chainAt ξ head pages ∗ kmemAuth γk pages.length))
    (fun head => @instCtxMorphExists hlc GF _ _ (fun (pages : List (BitVec 64)) ξ =>
        iprop(wordAtN ξ kmemFreelistAddr 8 (DFrac.own 1) head ∗ chainAt ξ head pages ∗ kmemAuth γk pages.length))
      (fun _ => @instCtxMorphSep hlc GF _ _ _ inferInstance
        (@instCtxMorphSep hlc GF _ _ _ inferInstance (instCtxMorphConst _))))

/-- The client's count agrees with the allocator's, and the pair steps together. -/
theorem kmemAuth_inc (γk : KmemNames) (n : Nat) (on : Option Nat) :
    kallocAvail (GF := GF) γk on ∗ kmemAuth γk n ⊢
      |==> (⌜∀ m, on = some m → m = n⌝ ∗ kallocAvail γk (availInc on) ∗ kmemAuth γk (n + 1)) := by
  cases on with
  | none =>
    simp only [availInc, Option.map, kallocAvail_none, kmemAuth]
    iintro ⟨#Hs, _⟩
    imodintro
    isplitl []
    · ipureintro; intro m h; cases h
    isplitl []
    · iexact Hs
    iright; iexact Hs
  | some m =>
    simp only [availInc, Option.map, kallocAvail_some, kmemAuth]
    iintro ⟨⟨Hp, Hc⟩, Ha⟩
    icases Ha with ⟨Hc' | #Hs⟩
    · ihave %hmn := ghost_var_agree _ _ _ _ _ $$ Hc Hc'
      subst hmn
      imod ghost_var_update_halves (m + 1) _ _ _ $$ Hc Hc' with ⟨Hc, Hc'⟩
      imodintro
      isplitl []
      · ipureintro; intro m' h; cases h; rfl
      isplitl [Hp Hc]
      · iframe
      ileft; iexact Hc'
    · ihave %hv := ghost_var_valid_2 _ _ _ _ _ $$ Hp Hs
      exact absurd hv.1 (by simp [DFrac.valid_own_op_discard])

theorem kmemAuth_dec (γk : KmemNames) (n : Nat) (on : Option Nat) :
    kallocAvail (GF := GF) γk on ∗ kmemAuth γk (n + 1) ⊢
      |==> (⌜∀ m, on = some m → m = n + 1⌝ ∗ kallocAvail γk (availDec on) ∗ kmemAuth γk n) := by
  cases on with
  | none =>
    simp only [availDec, Option.map, kallocAvail_none, kmemAuth]
    iintro ⟨#Hs, _⟩
    imodintro
    isplitl []
    · ipureintro; intro m h; cases h
    isplitl []
    · iexact Hs
    iright; iexact Hs
  | some m =>
    simp only [availDec, Option.map, kallocAvail_some, kmemAuth]
    iintro ⟨⟨Hp, Hc⟩, Ha⟩
    icases Ha with ⟨Hc' | #Hs⟩
    · ihave %hmn := ghost_var_agree _ _ _ _ _ $$ Hc Hc'
      subst hmn
      imod ghost_var_update_halves n _ _ _ $$ Hc Hc' with ⟨Hc, Hc'⟩
      imodintro
      isplitl []
      · ipureintro; intro m' h; cases h; rfl
      isplitl [Hp Hc]
      · simp only [Nat.add_sub_cancel]; iframe
      ileft; iexact Hc'
    · ihave %hv := ghost_var_valid_2 _ _ _ _ _ $$ Hp Hs
      exact absurd hv.1 (by simp [DFrac.valid_own_op_discard])

/-- The client's count, if tracked, is the allocator's. -/
theorem kmemAuth_agree (γk : KmemNames) (n : Nat) (on : Option Nat) :
    kallocAvail (GF := GF) γk on ∗ kmemAuth γk n ⊢
      ⌜∀ m, on = some m → m = n⌝ ∗ kallocAvail γk on ∗ kmemAuth γk n := by
  cases on with
  | none =>
    iintro ⟨Hs, Ha⟩
    isplitl []
    · ipureintro; intro m h; cases h
    iframe
  | some m =>
    simp only [kallocAvail_some, kmemAuth]
    iintro ⟨⟨Hp, Hc⟩, Ha⟩
    icases Ha with ⟨Hc' | #Hs⟩
    · ihave %hmn := ghost_var_agree _ _ _ _ _ $$ Hc Hc'
      subst hmn
      isplitl []
      · ipureintro; intro m' h; cases h; rfl
      isplitl [Hp Hc]
      · iframe
      ileft; iexact Hc'
    · ihave %hv := ghost_var_valid_2 _ _ _ _ _ $$ Hp Hs
      exact absurd hv.1 (by simp [DFrac.valid_own_op_discard])

end

end Xv6
