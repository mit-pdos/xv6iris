/-
**THE BUFFER CACHE, BORN** (a port of Rocq `BioInv.bio_init`): the ghost
state, the thirty escrows, the thirty sleeplocks, the LRU cycle and
`bcache.lock` itself, assembled out of what `binit` leaves behind and the
`.bss` cells `binit` never touches.

**WHAT `binit`'s POST LACKS** (reported).  `Xv6.wp_binit_body`'s `bufOut i`
hands back exactly the three things `binit` WRITES: the initialised
sleeplock (`Xv6.sleepLockInited`), `b->prev` and `b->next`.  The rest of
`struct buf` is `.bss` that `binit` never touches and that its specification
therefore never mentions -- `b->valid` (+0), `b->disk` (+4), `b->dev` (+8),
`b->blockno` (+12), `b->refcnt` (+64) and the 1024 data bytes (+88), all
zero out of `.bss`.  Those are the boot chain's to hand over, not `binit`'s,
so `Xv6.SpecBinit` does NOT grow: `Xv6.bioInit` takes them as a premise
beside `binit`'s post, exactly as Rocq's `bio_init` does.

Beside them it takes the covered blocks' disk fragments (the initial POOL:
no buffer caches anything yet) and requires `0 ∉ V.cov`, because `binit`
leaves every buffer's blockno cell at `0` and an uncovered blockno owes no
fragment -- which is what lets thirty buffers all naming block `0` coexist.

**GNAMES BEFORE THE RECORD** (Rocq's own dance).  `Xv6.bufSlpBox γ k` --
the payload the sleeplocks are sealed over -- names buffer `k`'s checkout
token and its escrow, so those ghosts are allocated FIRST as bare
`Nat → _` functions, the locks are sealed over `Xv6.bufSlpRaw`, and only
then is `Xv6.BcacheNames` assembled.

**THE LOCK IS BORN THROUGH ITS HOOK.**  `Xv6.bcacheResAt`'s floor slot must
cover the boot stamps of all thirty escrows, and a floor above the creator's
own view can only be minted on a stamped record -- so `bcache.lock` is
created with `MachCSL.kctx_newlock_hook` over `Xv6.bcacheRes_fold_in`.
-/
import Xv6.BufEscrow
import MachCSL.LockBornHook

namespace Xv6

open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode Std MachCSL
open LeanRV64D

set_option linter.unusedSectionVars false

section
variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF] [BcacheG GF]
variable [SleepLockG GF] [DiskG GF] [CurCtx]

/-! ## The slot supply -/

/-- The finite supply, minted one key at a time (Rocq's `bslots_alloc`). -/
theorem bslots_build (γ : BcacheNames) :
    ∀ (n : Nat), n ≤ BSLOTS → ∀ (M : RegMapF Unit),
      (∀ i, i < n → PartialMap.get? M i = none) →
      ((γ.slot ↪●MAP M) ⊢ |==> ∃ M' : RegMapF Unit,
        ⌜∀ i, n ≤ i → PartialMap.get? M' i = PartialMap.get? M i⌝ ∗
        (γ.slot ↪●MAP M') ∗ bslots (GF := GF) γ n) := by
  intro n
  induction n with
  | zero =>
    intro _ M _
    iintro Ha
    imodintro
    iexists M
    isplitl []
    · ipureintro; intro i _; rfl
    iframe Ha
    iapply bslots_zero
  | succ n ih =>
    intro hn M hfresh
    iintro Ha
    imod ih (by omega) M (fun i hi => hfresh i (by omega)) $$ Ha with ⟨%M', %hM', Ha, Hs⟩
    imod ghost_map_insert n () (by rw [hM' n (Nat.le_refl n)]; exact hfresh n (by omega))
      $$ Ha with ⟨Ha, He⟩
    imodintro
    iexists (PartialMap.insert M' n ())
    isplitl []
    · ipureintro
      intro i hi
      rw [LawfulPartialMap.get?_insert_ne (show n ≠ i by omega)]
      exact hM' i (by omega)
    iframe Ha
    iapply bslots_cons γ n
    isplitl [He]
    · unfold bslot bslots
      iexists [n]
      isplitl []
      · ipureintro
        refine ⟨rfl, by simp, ?_⟩
        intro j hj
        rw [List.mem_singleton] at hj
        subst hj
        omega
      · iapply BigSepL.bigSepL_singleton.2
        iexact He
    · iexact Hs

/-! ## The LRU cycle, out of `binit`'s links -/

/-- Buffer `i`'s two link cells, as `binit` leaves them. -/
def bdLinks (ξ : CtxId) (i : Nat) : IProp GF := iprop%
  wordAtN ξ (bPrev (bnode i)) 8 (DFrac.own 1) (bufPrevVal i) ∗
  wordAtN ξ (bNext (bnode i)) 8 (DFrac.own 1) (bufNextVal i)

theorem bd_prevVal (n : Nat) (hn : n < NBUF) :
    bufPrevVal n = (if n + 1 = NBUF then bhead else bnode (n + 1)) := by
  unfold bufPrevVal bhead bnode NBUF at *
  by_cases h : n = 29
  · subst h; simp
  · rw [if_neg h, if_neg (by omega)]

theorem bd_nextVal (n : Nat) :
    bufNextVal n = bhd bhead (List.map bnode (List.range n).reverse) := by
  unfold bufNextVal bhead bnode
  cases n with
  | zero => simp
  | succ m =>
    rw [if_neg (by omega)]
    rw [show (List.range (m + 1)).reverse = m :: (List.range m).reverse from by
      rw [List.range_succ]; simp]
    simp

set_option maxHeartbeats 1000000 in
/-- The cycle's body, by induction on the buffers spliced so far. -/
theorem bd_lru_seg (ξ : CtxId) :
    ∀ n : Nat, n ≤ NBUF →
      (([∗list] i ∈ List.range n, bdLinks (GF := GF) ξ i) ⊢
        bsegAt ξ bhead (if n = NBUF then bhead else bnode n)
          (List.map bnode (List.range n).reverse)) := by
  intro n
  induction n with
  | zero =>
    intro _
    simp only [List.range_zero, List.reverse_nil, List.map_nil]
    iintro -
    iempintro
  | succ m ih =>
    intro hm
    have hmlt : m < NBUF := by omega
    rw [List.range_succ]
    iintro H
    icases BigSepL.bigSepL_append.1 $$ H with ⟨H1, H2⟩
    ihave H2 := BigSepL.bigSepL_singleton.1 $$ H2
    icases (show bdLinks (GF := GF) ξ m ⊢
        wordAtN ξ (bPrev (bnode m)) 8 (DFrac.own 1) (bufPrevVal m) ∗
        wordAtN ξ (bNext (bnode m)) 8 (DFrac.own 1) (bufNextVal m) from by
      unfold bdLinks; iintro H; iexact H) $$ H2 with ⟨Hp, Hn⟩
    ihave Hseg := ih (by omega) $$ H1
    ihave Hseg := (show bsegAt (GF := GF) ξ bhead (if m = NBUF then bhead else bnode m)
          (List.map bnode (List.range m).reverse) ⊢
        bsegAt ξ bhead (bnode m) (List.map bnode (List.range m).reverse) from by
      rw [if_neg (by omega)]) $$ Hseg
    rw [show (List.range m ++ [m]).reverse = m :: (List.range m).reverse from by simp]
    rw [List.map_cons, bsegAt_cons ξ bhead _ (bnode m) _]
    ihave Hp := (show wordAtN (GF := GF) ξ (bPrev (bnode m)) 8 (DFrac.own 1) (bufPrevVal m) ⊢
        wordAtN ξ (bPrev (bnode m)) 8 (DFrac.own 1)
          (if m + 1 = NBUF then bhead else bnode (m + 1)) from by
      rw [bd_prevVal m hmlt]) $$ Hp
    ihave Hn := (show wordAtN (GF := GF) ξ (bNext (bnode m)) 8 (DFrac.own 1) (bufNextVal m) ⊢
        wordAtN ξ (bNext (bnode m)) 8 (DFrac.own 1)
          (bhd bhead (List.map bnode (List.range m).reverse)) from by
      rw [bd_nextVal m]) $$ Hn
    iframe Hp Hn Hseg

/-- The whole cycle. -/
theorem bd_lru_boot (ξ : CtxId) :
    wordAtN (GF := GF) ξ (bNext bhead) 8 (DFrac.own 1) (bufAddr (NBUF - 1)) ∗
    wordAtN ξ (bPrev bhead) 8 (DFrac.own 1) (bufAddr 0) ∗
    ([∗list] i ∈ List.range NBUF, bdLinks ξ i) ⊢
      bcacheLruAt ξ bhead (List.map bnode (List.range NBUF).reverse) := by
  iintro ⟨Hhn, Hhp, H⟩
  ihave Hseg := (show ([∗list] i ∈ List.range NBUF, bdLinks (GF := GF) ξ i) ⊢
      bsegAt ξ bhead bhead (List.map bnode (List.range NBUF).reverse) from by
    have h := bd_lru_seg (GF := GF) ξ NBUF (Nat.le_refl _)
    rw [if_pos rfl] at h
    exact h) $$ H
  unfold bcacheLruAt
  ihave Hhn := (show wordAtN (GF := GF) ξ (bNext bhead) 8 (DFrac.own 1) (bufAddr (NBUF - 1)) ⊢
      wordAtN ξ (bNext bhead) 8 (DFrac.own 1)
        (bhd bhead (List.map bnode (List.range NBUF).reverse)) from by
    rw [show bhd bhead (List.map bnode (List.range NBUF).reverse) = bufAddr (NBUF - 1) from by
      unfold NBUF bnode; decide]) $$ Hhn
  ihave Hhp := (show wordAtN (GF := GF) ξ (bPrev bhead) 8 (DFrac.own 1) (bufAddr 0) ⊢
      wordAtN ξ (bPrev bhead) 8 (DFrac.own 1)
        (blast (List.map bnode (List.range NBUF).reverse) bhead) from by
    rw [show blast (List.map bnode (List.range NBUF).reverse) bhead = bufAddr 0 from by
      unfold NBUF bnode; decide]) $$ Hhp
  iframe Hhn Hhp Hseg

/-! ## Allocating one ghost per buffer

Rocq's `tok_fun_alloc` / `seq_fun_alloc`: the thirty ghosts are allocated
one at a time and collected into a `Nat → _` function, so that the names
exist BEFORE `Xv6.BcacheNames` does. -/

/-- The pure-ghost form (the checkout tokens). -/
theorem bd_funAlloc {A : Type} [Inhabited A] (P : Nat → A → IProp GF)
    (halloc : ∀ j : Nat, ⊢ |==> ∃ a : A, P j a) :
    ∀ n : Nat, ⊢ |==> ∃ f : Nat → A, [∗list] j ∈ List.range n, P j (f j) := by
  intro n
  induction n with
  | zero =>
    imodintro
    iexists (fun _ => (default : A))
    simp only [List.range_zero]
    iapply BigSepL.bigSepL_nil.2
    itrivial
  | succ n ih =>
    imod ih with ⟨%f, Hf⟩
    imod halloc n with ⟨%a, Ha⟩
    imodintro
    iexists (fun j => if j = n then a else f j)
    rw [List.range_succ]
    iapply BigSepL.bigSepL_append.2
    isplitl [Hf]
    · iapply bigSepL_range_congr (fun j => P j (f j))
        (fun j => P j (if j = n then a else f j)) n (fun j hj => by rw [if_neg (by omega)])
      iexact Hf
    · iapply BigSepL.bigSepL_singleton.2
      simp only [reduceIte]
      iexact Ha

/-- The form that threads the kernel context (the sleeplocks). -/
theorem bd_funAllocK {A : Type} [Inhabited A] (Q : Nat → IProp GF) (P : Nat → A → IProp GF)
    (cpu : CPU) (k : KCtx)
    (hstep : ∀ j : Nat, kctx (GF := GF) cpu k ∗ Q j ⊢ |={⊤}=> (kctx cpu k ∗ ∃ a : A, P j a)) :
    ∀ n : Nat, (kctx (GF := GF) cpu k ∗ ([∗list] j ∈ List.range n, Q j) ⊢
      |={⊤}=> (kctx cpu k ∗ ∃ f : Nat → A, [∗list] j ∈ List.range n, P j (f j))) := by
  intro n
  induction n with
  | zero =>
    iintro ⟨Hk, -⟩
    imodintro
    iframe Hk
    iexists (fun _ => (default : A))
    simp only [List.range_zero]
    iapply BigSepL.bigSepL_nil.2
    itrivial
  | succ n ih =>
    rw [List.range_succ]
    iintro ⟨Hk, H⟩
    icases BigSepL.bigSepL_append.1 $$ H with ⟨H1, H2⟩
    imod ih $$ [Hk H1] with ⟨Hk, ⟨%f, Hf⟩⟩
    · iframe Hk H1
    ihave H2 := BigSepL.bigSepL_singleton.1 $$ H2
    imod hstep n $$ [Hk H2] with ⟨Hk, ⟨%a, Ha⟩⟩
    · iframe Hk H2
    imodintro
    iframe Hk
    iexists (fun j => if j = n then a else f j)
    iapply BigSepL.bigSepL_append.2
    isplitl [Hf]
    · iapply bigSepL_range_congr (fun j => P j (f j))
        (fun j => P j (if j = n then a else f j)) n (fun j hj => by rw [if_neg (by omega)])
      iexact Hf
    · iapply BigSepL.bigSepL_singleton.2
      simp only [reduceIte]
      iexact Ha

end

end Xv6
