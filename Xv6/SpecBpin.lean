/-
Specification of `bpin` (kernel/bio.c): the public contract.  Mirrors Rocq
`SpecBpin.v`.

    void bpin(struct buf *b) {
      acquire(&bcache.lock);
      b->refcnt++;
      release(&bcache.lock);
    }

Minting a reference with no sleeplock involved: the caller supplies one
`bslot` -- the finite unit that keeps the unchecked increment a faithful
`int` (`Xv6/BcacheInv.lean`, the recipe `fdSlot` already uses for
`f->ref++`) -- and receives a `bref`.  Unlike `filedup` there is no
`ref < 1` check and no held-lock requirement: `bpin` at `refcnt == 0`
legally mints the first reference.  4 frame slots plus `acquire`'s 10.

The Rocq post is `∃ q dev bno, bref bn k q dev bno`: the reference also
carries a fraction of `b->dev`/`b->blockno`.  This port's `bref` is the
count fragment alone -- see the header of `Xv6/BcacheInv.lean`.

Imports only definitional files (never a `Code*` or `Proof*` file).
-/
import MachCSL.WpSmodeFrame
import MachCSL.Lock
import Xv6.BcacheInv

namespace Xv6

open Iris Iris.ProgramLogic Iris.BI Std MachCSL
open LeanRV64D

/-- Address of `bpin`. -/
def bpinAddr : BitVec 64 := KA.«bpin»

/-- **WP of `bpin(b = a0)`**. -/
def wp_bpin_body {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF] [BcacheG GF] [CurCtx]
    (cpu : CPU) (k : KCtx) (γl : GName) (γ : BcacheNames) (kk : Nat)
    (hnoff : k.noff + 1 < 2 ^ 31) (hK : 14 ≤ k.avail) (hlk : "bcache" ∉ k.locks)
    (hkk : kk < NBUF) (ha0 : k.regs 10#5 = bnode kk) : Prop :=
  kctx cpu k ∗ pcIs cpu bpinAddr ∗ isBcache γl γ ∗ bslot γ ∗
  wpNext k.sie k.proc cpu (fun cpu' => iprop(∀ spie : Bool, ∀ spp : Bool, ∀ R' : RegMap,
    ⌜k.sie = false → spie = k.spie ∧ spp = k.spp⌝ -∗
    kctx cpu' ((k.withSpie spie spp).withRegs R') -∗ pcIs cpu' (jumpPc (k.regs 1#5)) -∗
    ⌜calleeSaved k.regs R'⌝ -∗ bref γ kk -∗ wpLoop cpu'))
  ⊢ wpLoop (GF := GF) cpu

/-- The interface of `bpin`. -/
structure BPIN : Prop where
  wp_bpin : ∀ {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF] [BcacheG GF] [CurCtx]
    (cpu : CPU) (k : KCtx) (γl : GName) (γ : BcacheNames) (kk : Nat) hnoff hK hlk hkk ha0,
    wp_bpin_body (hlc := hlc) (GF := GF) cpu k γl γ kk hnoff hK hlk hkk ha0

end Xv6
