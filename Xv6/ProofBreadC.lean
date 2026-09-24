/-
`bread`'s TWO SCANS, as loops by induction on the LRU order.

    // the hit scan
    for (b = bcache.head.next; b != &bcache.head; b = b->next)
      if (b->dev == dev && b->blockno == blockno) { b->refcnt++; ... }
    // the recycle scan
    for (b = bcache.head.prev; b != &bcache.head; b = b->prev)
      if (b->refcnt == 0) { ... }
    panic("bget: no buffers");

Both run with `bcache.lock` held and interrupts off, so the hart cannot
migrate inside either: every step is a `k_step` at a FIXED `cpu`, and the
only thing that moves is the cursor.  Each carries the OPEN form
(`Xv6.bdScan`) and hands it back untouched to whichever continuation it
exits through, which is what lets the exit facts be STATEMENTS ABOUT
`devs`/`bnos` -- see `Xv6/ProofBreadA.lean`'s header.
-/
import Xv6.ProofBreadB

namespace Xv6

open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode Std MachCSL
open LeanRV64D

attribute [local semireducible] LeanRV64D.Functions.hartSupports LeanRV64D.Functions.currentlyEnabled

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-- The registers the forward scan reads: the cursor, the head sentinel and
the two arguments. -/
def bdFwdRegs (dev bno : BitVec 32) (kk : Nat) (R : RegMap) : Prop :=
  R 9#5 = bnode kk ∧ R 14#5 = bhead ∧ R 18#5 = BitVec.signExtend 64 dev ∧
  R 19#5 = BitVec.signExtend 64 bno

/-- Everything but the cursor and the scratch register is untouched. -/
def bdOther (R0 R : RegMap) : Prop := ∀ i, i ≠ 9#5 → i ≠ 15#5 → R i = R0 i

theorem bdOther_refl (R0 : RegMap) : bdOther R0 R0 := fun _ _ _ => rfl

theorem bdOther_trans (R0 R1 R2 : RegMap) (h1 : bdOther R0 R1) (h2 : bdOther R1 R2) :
    bdOther R0 R2 := fun i a b => (h2 i a b).trans (h1 i a b)

theorem bdOther_set (R0 R : RegMap) (h : bdOther R0 R) (i : BitVec 5) (v : BitVec 64)
    (hi : i = 9#5 ∨ i = 15#5) : bdOther R0 (R.set i v) := by
  intro j a b
  rw [RegMap.set_apply]
  have : ¬ (j = i) := by rcases hi with rfl | rfl <;> assumption
  rw [if_neg this]
  exact h j a b

section
variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF] [BcacheG GF]
variable [SleepLockG GF] [DiskG GF] [CurCtx]

set_option maxHeartbeats 8000000 in
/-- One iteration's compare, from `bread+0x3c`: `b->dev == dev &&
b->blockno == blockno`.  Either arm leaves the scan resource untouched. -/
theorem bd_fwd_step (c : CPU) (kc : KCtx) (hsie : kc.sie = false)
    (γ : BcacheNames) (V : BioView) (tl : Nat) (M : RegMapF Nat) (Ls : Nat → List Nat)
    (ord : List Nat) (devs bnos : Nat → BitVec 32) (dev bno : BitVec 32)
    (R0 Rc : RegMap) (kk : Nat) (hkk : kk < NBUF)
    (hregs : bdFwdRegs dev bno kk Rc) (hoth : bdOther R0 Rc) :
    kctx c (kc.withRegs Rc) ∗ pcIs c (KA.«bread» + 0x3c#64) ∗
    bdScan γ V tl M Ls ord devs bnos ∗
    (∀ (Rc2 : RegMap) (pc2 : BitVec 64) (hit : Bool),
      ⌜(hit = true ↔ (devs kk = dev ∧ bnos kk = bno)) ∧
        pc2 = (if hit then KA.«bread» + 0x48#64 else KA.«bread» + 0x36#64) ∧
        bdFwdRegs dev bno kk Rc2 ∧ bdOther R0 Rc2⌝ -∗
      kctx c (kc.withRegs Rc2) -∗ pcIs c pc2 -∗
      bdScan γ V tl M Ls ord devs bnos -∗ wpLoop c)
    ⊢ wpLoop (GF := GF) c := by
  obtain ⟨h9, h14, h18, h19⟩ := hregs
  iintro ⟨Hk, Hpc, Hscan, Hcont⟩
  icases kctx_kernelText _ _ $$ Hk with ⟨#Htext, Hk⟩
  icases bdScan_unpack γ V tl M Ls ord devs bnos $$ Hscan with ⟨Ha, Hlru, Hpool, Hkey, Hs⟩
  icases bkey_acc γ curCtx tl devs bnos kk hkk $$ Hkey with ⟨Hkey0, Hkcl⟩
  icases bkeyAt_elim γ curCtx tl kk (devs kk) (bnos kk) $$ Hkey0 with ⟨Hkd, Hkb, Hkr⟩
  ihave Hkd := (show wordAtN (GF := GF) curCtx (aBufDev (bnode kk)) 4
        (DFrac.own (1 : Qp).half) (devs kk) ⊢
      wordPointsTo (bnode kk + 8#64) 4 (DFrac.own (1 : Qp).half) (devs kk) from by
    rw [wordAtN_cur, bd_dev_eq']) $$ Hkd
  -- c.lw a5,8(s1)
  k_step (wp_s_lw c _ (KA.«bread» + 0x3c#64) true 8#12 15#5 9#5 (by decide) (by decide)
      (DFrac.own (1 : Qp).half) (devs kk))
    from (text_instr _ _ _ _ rfl rfl) Htext $$ [- $Hk $Hpc] with [h9]
  iintro Hk Hpc Hkd
  ihave Hkd := (show wordPointsTo (GF := GF) (bnode kk + 8#64) 4
        (DFrac.own (1 : Qp).half) (devs kk) ⊢
      wordAtN curCtx (aBufDev (bnode kk)) 4 (DFrac.own (1 : Qp).half) (devs kk) from by
    rw [wordAtN_cur, bd_dev_eq']) $$ Hkd
  by_cases hdv : devs kk = dev
  · -- the device matches: test the block number
    k_step (wp_s_branch c _ (KA.«bread» + 0x3e#64) false 8184#13 15#5 18#5 (by decide) bop.BNE)
      from (text_instr _ _ _ _ rfl rfl) Htext $$ [- $Hk $Hpc]
      with [h18, bd_bne_of_eq _ _ hdv]
    iintro Hk Hpc
    ihave Hkb := (show wordAtN (GF := GF) curCtx (aBufBlockno (bnode kk)) 4
          (DFrac.own (1 : Qp).half) (bnos kk) ⊢
        wordPointsTo (bnode kk + 12#64) 4 (DFrac.own (1 : Qp).half) (bnos kk) from by
      rw [wordAtN_cur, bd_bno_eq']) $$ Hkb
    k_step (wp_s_lw c _ (KA.«bread» + 0x42#64) true 12#12 15#5 9#5 (by decide) (by decide)
        (DFrac.own (1 : Qp).half) (bnos kk))
      from (text_instr _ _ _ _ rfl rfl) Htext $$ [- $Hk $Hpc] with [h9]
    iintro Hk Hpc Hkb
    ihave Hkb := (show wordPointsTo (GF := GF) (bnode kk + 12#64) 4
          (DFrac.own (1 : Qp).half) (bnos kk) ⊢
        wordAtN curCtx (aBufBlockno (bnode kk)) 4 (DFrac.own (1 : Qp).half) (bnos kk) from by
      rw [wordAtN_cur, bd_bno_eq']) $$ Hkb
    ihave Hkey0 := bkeyAt_intro γ curCtx tl kk (devs kk) (bnos kk) $$ [Hkd Hkb Hkr]
    case' _ => iframe Hkd Hkb Hkr
    ihave Hkey := Hkcl $$ Hkey0
    ihave Hscan := bdScan_pack γ V tl M Ls ord devs bnos $$ [Ha Hlru Hpool Hkey Hs]
    case' _ => iframe Ha Hlru Hpool Hkey Hs
    by_cases hbn : bnos kk = bno
    · -- **HIT**
      k_step (wp_s_branch c _ (KA.«bread» + 0x44#64) false 8178#13 15#5 19#5 (by decide) bop.BNE)
        from (text_instr _ _ _ _ rfl rfl) Htext $$ [- $Hk $Hpc]
        with [h19, bd_bne_of_eq _ _ hbn]
      iintro Hk Hpc
      k_norm
      iapply Hcont $$ %_ %(KA.«bread» + 0x48#64) %true [] Hk Hpc Hscan
      ipureintro
      refine ⟨⟨fun _ => ⟨hdv, hbn⟩, fun _ => rfl⟩, rfl, ⟨?_, ?_, ?_, ?_⟩, ?_⟩ <;>
        first
          | exact bdOther_set R0 Rc hoth 15#5 _ (Or.inr rfl)
          | exact bdOther_set R0 _ (bdOther_set R0 Rc hoth 15#5 _ (Or.inr rfl)) 15#5 _ (Or.inr rfl)
          | assumption
          | (simp only [RegMap.set_apply, BitVec.reduceEq, ite_false]; assumption)
    · -- the block number differs: back edge
      k_step (wp_s_branch c _ (KA.«bread» + 0x44#64) false 8178#13 15#5 19#5 (by decide) bop.BNE)
        from (text_instr _ _ _ _ rfl rfl) Htext $$ [- $Hk $Hpc]
        with [h19, bd_bne_of_ne _ _ hbn, bd_t_back2]
      iintro Hk Hpc
      k_norm
      iapply Hcont $$ %_ %(KA.«bread» + 0x36#64) %false [] Hk Hpc Hscan
      ipureintro
      refine ⟨⟨fun h => absurd h (by decide), fun hc => absurd hc.2 hbn⟩, rfl,
        ⟨?_, ?_, ?_, ?_⟩, ?_⟩ <;>
        first
          | exact bdOther_set R0 Rc hoth 15#5 _ (Or.inr rfl)
          | exact bdOther_set R0 _ (bdOther_set R0 Rc hoth 15#5 _ (Or.inr rfl)) 15#5 _ (Or.inr rfl)
          | assumption
          | (simp only [RegMap.set_apply, BitVec.reduceEq, ite_false]; assumption)
  · -- the device differs: back edge
    ihave Hkey0 := bkeyAt_intro γ curCtx tl kk (devs kk) (bnos kk) $$ [Hkd Hkb Hkr]
    case' _ => iframe Hkd Hkb Hkr
    ihave Hkey := Hkcl $$ Hkey0
    ihave Hscan := bdScan_pack γ V tl M Ls ord devs bnos $$ [Ha Hlru Hpool Hkey Hs]
    case' _ => iframe Ha Hlru Hpool Hkey Hs
    k_step (wp_s_branch c _ (KA.«bread» + 0x3e#64) false 8184#13 15#5 18#5 (by decide) bop.BNE)
      from (text_instr _ _ _ _ rfl rfl) Htext $$ [- $Hk $Hpc]
      with [h18, bd_bne_of_ne _ _ hdv, bd_t_back1]
    iintro Hk Hpc
    k_norm
    iapply Hcont $$ %_ %(KA.«bread» + 0x36#64) %false [] Hk Hpc Hscan
    ipureintro
    refine ⟨⟨fun h => absurd h (by decide), fun hc => absurd hc.1 hdv⟩, rfl,
      ⟨?_, ?_, ?_, ?_⟩, ?_⟩ <;>
      first
        | exact bdOther_set R0 Rc hoth 15#5 _ (Or.inr rfl)
        | exact bdOther_set R0 _ (bdOther_set R0 Rc hoth 15#5 _ (Or.inr rfl)) 15#5 _ (Or.inr rfl)
        | assumption
        | (simp only [RegMap.set_apply, BitVec.reduceEq, ite_false]; assumption)

set_option maxHeartbeats 8000000 in
/-- **THE HIT SCAN**, from `bread+0x3c` with the cursor on buffer `kk`, by
induction on the buffers still to visit. -/
theorem bd_fwd (c : CPU) (kc : KCtx) (hsie : kc.sie = false)
    (γ : BcacheNames) (V : BioView) (tl : Nat) (M : RegMapF Nat) (Ls : Nat → List Nat)
    (ord : List Nat) (devs bnos : Nat → BitVec 32) (dev bno : BitVec 32)
    (hord : ord.Perm (List.range NBUF)) (R0 : RegMap) :
    ∀ (rest o1 : List Nat) (kk : Nat) (Rc : RegMap),
      ord = o1 ++ kk :: rest →
      (∀ i, i ∈ o1 → ¬(devs i = dev ∧ bnos i = bno)) →
      bdFwdRegs dev bno kk Rc → bdOther R0 Rc →
      (kctx c (kc.withRegs Rc) ∗ pcIs c (KA.«bread» + 0x3c#64) ∗
        bdScan γ V tl M Ls ord devs bnos ∗
        (∀ (kk2 : Nat) (Rc2 : RegMap),
          ⌜kk2 < NBUF ∧ devs kk2 = dev ∧ bnos kk2 = bno ∧
            bdFwdRegs dev bno kk2 Rc2 ∧ bdOther R0 Rc2⌝ -∗
          kctx c (kc.withRegs Rc2) -∗ pcIs c (KA.«bread» + 0x48#64) -∗
          bdScan γ V tl M Ls ord devs bnos -∗ wpLoop c) ∗
        (∀ Rc2 : RegMap,
          ⌜(∀ i, i < NBUF → ¬(devs i = dev ∧ bnos i = bno)) ∧ bdOther R0 Rc2⌝ -∗
          kctx c (kc.withRegs Rc2) -∗ pcIs c (KA.«bread» + 0x64#64) -∗
          bdScan γ V tl M Ls ord devs bnos -∗ wpLoop c)
        ⊢ wpLoop (GF := GF) c) := by
  intro rest
  induction rest with
  | nil =>
    intro o1 kk Rc hsplit hmiss hregs hoth
    have hkk : kk < NBUF := bd_ord_lt ord hord kk (by rw [hsplit]; simp)
    iintro ⟨Hk, Hpc, Hscan, Hhit, Hmiss'⟩
    iapply (bd_fwd_step c kc hsie γ V tl M Ls ord devs bnos dev bno R0 Rc kk hkk hregs hoth)
    iframe Hk Hpc Hscan
    iintro %Rc2 %pc2 %hit %hp Hk Hpc Hscan
    cases hit with
    | true =>
      obtain ⟨hiff, hpc2, hregs2, hoth2⟩ := hp
      have hpc' : pc2 = KA.«bread» + 0x48#64 := by rw [hpc2]; simp
      subst hpc'
      iapply Hhit $$ %kk %Rc2 [] Hk Hpc Hscan
      ipureintro
      exact ⟨hkk, (hiff.1 rfl).1, (hiff.1 rfl).2, hregs2, hoth2⟩
    | false =>
      obtain ⟨hiff, hpc2, hregs2, hoth2⟩ := hp
      have hpc' : pc2 = KA.«bread» + 0x36#64 := by rw [hpc2]; simp
      subst hpc'
      have hne : ¬(devs kk = dev ∧ bnos kk = bno) := fun hc => by
        have := hiff.2 hc; exact absurd this (by decide)
      obtain ⟨g9, g14, g18, g19⟩ := hregs2
      icases kctx_kernelText _ _ $$ Hk with ⟨#Htext, Hk⟩
      icases bdScan_unpack γ V tl M Ls ord devs bnos $$ Hscan with ⟨Ha, Hlru, Hpool, Hkey, Hs⟩
      ihave Hlru := (show bcacheLruAt (GF := GF) curCtx bhead (ord.map bnode) ⊢
          bcacheLruAt curCtx bhead (o1.map bnode ++ bnode kk :: ([] : List Nat).map bnode) from by
        rw [show ord.map bnode = o1.map bnode ++ bnode kk :: ([] : List Nat).map bnode from by
          rw [hsplit]; simp]) $$ Hlru
      icases bcacheLru_next_acc curCtx bhead (bnode kk) (o1.map bnode) (([] : List Nat).map bnode)
        $$ Hlru with ⟨Hnx, Hlcl⟩
      ihave Hnx := (show wordAtN (GF := GF) curCtx (bNext (bnode kk)) 8 (DFrac.own 1)
            (bhd bhead (([] : List Nat).map bnode)) ⊢
          wordPointsTo (bnode kk + 80#64) 8 (DFrac.own 1) bhead from by
        rw [wordAtN_cur, bd_next_eq']; rfl) $$ Hnx
      k_step (wp_s_ld c _ (KA.«bread» + 0x36#64) true 80#12 9#5 9#5 (by decide) (by decide)
          (DFrac.own 1) bhead)
        from (text_instr _ _ _ _ rfl rfl) Htext $$ [- $Hk $Hpc] with [g9]
      iintro Hk Hpc Hnx
      ihave Hnx := (show wordPointsTo (GF := GF) (bnode kk + 80#64) 8 (DFrac.own 1) bhead ⊢
          wordAtN curCtx (bNext (bnode kk)) 8 (DFrac.own 1)
            (bhd bhead (([] : List Nat).map bnode)) from by
        rw [wordAtN_cur, bd_next_eq']; rfl) $$ Hnx
      ihave Hlru := Hlcl $$ Hnx
      ihave Hlru := (show bcacheLruAt (GF := GF) curCtx bhead
            (o1.map bnode ++ bnode kk :: ([] : List Nat).map bnode) ⊢
          bcacheLruAt curCtx bhead (ord.map bnode) from by
        rw [show ord.map bnode = o1.map bnode ++ bnode kk :: ([] : List Nat).map bnode from by
          rw [hsplit]; simp]) $$ Hlru
      ihave Hscan := bdScan_pack γ V tl M Ls ord devs bnos $$ [Ha Hlru Hpool Hkey Hs]
      case' _ => iframe Ha Hlru Hpool Hkey Hs
      -- beq s1,a4 : the cursor is the sentinel, so the scan is over
      k_step (wp_s_branch c _ (KA.«bread» + 0x38#64) false 44#13 9#5 14#5 (by decide) bop.BEQ)
        from (text_instr _ _ _ _ rfl rfl) Htext $$ [- $Hk $Hpc]
        with [g14, bd_beq_eq, bd_t_miss2]
      iintro Hk Hpc
      k_norm
      iapply Hmiss' $$ %_ [] Hk Hpc Hscan
      ipureintro
      refine ⟨?_, ?_⟩
      · intro i hi hc
        have : i ∈ ord := (hord.mem_iff).2 (List.mem_range.2 hi)
        rw [hsplit] at this
        simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at this
        rcases this with h | h
        · exact hmiss i h hc
        · exact hne (by rw [← h]; exact hc)
      · exact bdOther_set R0 Rc2 hoth2 9#5 _ (Or.inl rfl)
  | cons k2 rest2 ih =>
    intro o1 kk Rc hsplit hmiss hregs hoth
    have hkk : kk < NBUF := bd_ord_lt ord hord kk (by rw [hsplit]; simp)
    have hk2 : k2 < NBUF := bd_ord_lt ord hord k2 (by rw [hsplit]; simp)
    iintro ⟨Hk, Hpc, Hscan, Hhit, Hmiss'⟩
    iapply (bd_fwd_step c kc hsie γ V tl M Ls ord devs bnos dev bno R0 Rc kk hkk hregs hoth)
    iframe Hk Hpc Hscan
    iintro %Rc2 %pc2 %hit %hp Hk Hpc Hscan
    cases hit with
    | true =>
      obtain ⟨hiff, hpc2, hregs2, hoth2⟩ := hp
      have hpc' : pc2 = KA.«bread» + 0x48#64 := by rw [hpc2]; simp
      subst hpc'
      iapply Hhit $$ %kk %Rc2 [] Hk Hpc Hscan
      ipureintro
      exact ⟨hkk, (hiff.1 rfl).1, (hiff.1 rfl).2, hregs2, hoth2⟩
    | false =>
      obtain ⟨hiff, hpc2, hregs2, hoth2⟩ := hp
      have hpc' : pc2 = KA.«bread» + 0x36#64 := by rw [hpc2]; simp
      subst hpc'
      have hne : ¬(devs kk = dev ∧ bnos kk = bno) := fun hc => by
        have := hiff.2 hc; exact absurd this (by decide)
      obtain ⟨g9, g14, g18, g19⟩ := hregs2
      icases kctx_kernelText _ _ $$ Hk with ⟨#Htext, Hk⟩
      icases bdScan_unpack γ V tl M Ls ord devs bnos $$ Hscan with ⟨Ha, Hlru, Hpool, Hkey, Hs⟩
      have hmp : ord.map bnode = o1.map bnode ++ bnode kk :: (k2 :: rest2).map bnode := by
        rw [hsplit]; simp
      ihave Hlru := (show bcacheLruAt (GF := GF) curCtx bhead (ord.map bnode) ⊢
          bcacheLruAt curCtx bhead (o1.map bnode ++ bnode kk :: (k2 :: rest2).map bnode) from by
        rw [hmp]) $$ Hlru
      icases bcacheLru_next_acc curCtx bhead (bnode kk) (o1.map bnode) ((k2 :: rest2).map bnode)
        $$ Hlru with ⟨Hnx, Hlcl⟩
      ihave Hnx := (show wordAtN (GF := GF) curCtx (bNext (bnode kk)) 8 (DFrac.own 1)
            (bhd bhead ((k2 :: rest2).map bnode)) ⊢
          wordPointsTo (bnode kk + 80#64) 8 (DFrac.own 1) (bnode k2) from by
        rw [wordAtN_cur, bd_next_eq']; rfl) $$ Hnx
      k_step (wp_s_ld c _ (KA.«bread» + 0x36#64) true 80#12 9#5 9#5 (by decide) (by decide)
          (DFrac.own 1) (bnode k2))
        from (text_instr _ _ _ _ rfl rfl) Htext $$ [- $Hk $Hpc] with [g9]
      iintro Hk Hpc Hnx
      ihave Hnx := (show wordPointsTo (GF := GF) (bnode kk + 80#64) 8 (DFrac.own 1) (bnode k2) ⊢
          wordAtN curCtx (bNext (bnode kk)) 8 (DFrac.own 1)
            (bhd bhead ((k2 :: rest2).map bnode)) from by
        rw [wordAtN_cur, bd_next_eq']; rfl) $$ Hnx
      ihave Hlru := Hlcl $$ Hnx
      ihave Hlru := (show bcacheLruAt (GF := GF) curCtx bhead
            (o1.map bnode ++ bnode kk :: (k2 :: rest2).map bnode) ⊢
          bcacheLruAt curCtx bhead (ord.map bnode) from by rw [hmp]) $$ Hlru
      ihave Hscan := bdScan_pack γ V tl M Ls ord devs bnos $$ [Ha Hlru Hpool Hkey Hs]
      case' _ => iframe Ha Hlru Hpool Hkey Hs
      -- beq s1,a4 : the cursor is a real buffer, so the loop goes round
      k_step (wp_s_branch c _ (KA.«bread» + 0x38#64) false 44#13 9#5 14#5 (by decide) bop.BEQ)
        from (text_instr _ _ _ _ rfl rfl) Htext $$ [- $Hk $Hpc]
        with [g14, bd_beq_ne _ _ (bnode_ne_bhead k2 hk2)]
      iintro Hk Hpc
      k_norm
      iapply (ih (o1 ++ [kk]) k2 _ (by rw [hsplit]; simp)
        (by intro i hi
            simp only [List.mem_append, List.mem_singleton] at hi
            rcases hi with hi | rfl
            · exact hmiss i hi
            · exact hne)
        (by refine ⟨?_, ?_, ?_, ?_⟩ <;>
              first
                | (simp only [RegMap.set_apply, BitVec.reduceEq, ite_true, ite_false]; rfl)
                | (simp only [RegMap.set_apply, BitVec.reduceEq, ite_false]; assumption))
        (bdOther_set R0 Rc2 hoth2 9#5 _ (Or.inl rfl)))
      iframe Hk Hpc Hscan Hhit Hmiss'

set_option maxHeartbeats 8000000 in
/-- One iteration's `refcnt` test, from `bread+0x7a`. -/
theorem bd_bwd_step (c : CPU) (kc : KCtx) (hsie : kc.sie = false)
    (γ : BcacheNames) (V : BioView) (tl : Nat) (M : RegMapF Nat) (Ls : Nat → List Nat)
    (ord : List Nat) (devs bnos : Nat → BitVec 32) (dev bno : BitVec 32)
    (R0 Rc : RegMap) (kk : Nat) (hkk : kk < NBUF)
    (hregs : bdFwdRegs dev bno kk Rc) (hoth : bdOther R0 Rc) :
    kctx c (kc.withRegs Rc) ∗ pcIs c (KA.«bread» + 0x7a#64) ∗
    bdScan γ V tl M Ls ord devs bnos ∗
    (∀ (Rc2 : RegMap) (pc2 : BitVec 64) (zero : Bool),
      ⌜(zero = true ↔ Ls kk = []) ∧
        pc2 = (if zero then KA.«bread» + 0x90#64 else KA.«bread» + 0x7e#64) ∧
        bdFwdRegs dev bno kk Rc2 ∧ bdOther R0 Rc2⌝ -∗
      kctx c (kc.withRegs Rc2) -∗ pcIs c pc2 -∗
      bdScan γ V tl M Ls ord devs bnos -∗ wpLoop c)
    ⊢ wpLoop (GF := GF) c := by
  obtain ⟨h9, h14, h18, h19⟩ := hregs
  iintro ⟨Hk, Hpc, Hscan, Hcont⟩
  icases kctx_kernelText _ _ $$ Hk with ⟨#Htext, Hk⟩
  icases bdScan_unpack γ V tl M Ls ord devs bnos $$ Hscan with ⟨Ha, Hlru, Hpool, Hkey, Hs⟩
  icases bslot_upd_acc γ curCtx Ls kk hkk $$ Hs with ⟨Hsl0, Hcl⟩
  icases bslotAt_elim γ curCtx kk (Ls kk) $$ Hsl0
    with ⟨%⟨hnd, hlt⟩, Hrefc, Hhalves, Hslots, Hcnt⟩
  ihave Hrefc := (show wordAtN (GF := GF) curCtx (aBufRefcnt (bnode kk)) 4 (DFrac.own 1)
        (BitVec.ofNat 32 (Ls kk).length) ⊢
      wordPointsTo (bnode kk + 64#64) 4 (DFrac.own 1) (BitVec.ofNat 32 (Ls kk).length) from by
    rw [wordAtN_cur, aBufRefcnt_eq']) $$ Hrefc
  -- c.lw a5,64(s1)
  k_step (wp_s_lw c _ (KA.«bread» + 0x7a#64) true 64#12 15#5 9#5 (by decide) (by decide)
      (DFrac.own 1) (BitVec.ofNat 32 (Ls kk).length))
    from (text_instr _ _ _ _ rfl rfl) Htext $$ [- $Hk $Hpc] with [h9]
  iintro Hk Hpc Hrefc
  ihave Hrefc := (show wordPointsTo (GF := GF) (bnode kk + 64#64) 4 (DFrac.own 1)
        (BitVec.ofNat 32 (Ls kk).length) ⊢
      wordAtN curCtx (aBufRefcnt (bnode kk)) 4 (DFrac.own 1)
        (BitVec.ofNat 32 (Ls kk).length) from by
    rw [wordAtN_cur, aBufRefcnt_eq']) $$ Hrefc
  ihave Hsl0 := bslotAt_intro γ curCtx kk (Ls kk) hnd hlt $$ [Hrefc Hhalves Hslots Hcnt]
  case' _ => iframe Hrefc Hhalves Hslots Hcnt
  ihave Hs := Hcl $$ %(Ls kk) Hsl0
  ihave Hs := (show ([∗list] j ∈ List.range NBUF, bslotAt (GF := GF) γ curCtx j
        (updAtB Ls kk (Ls kk) j)) ⊢
      [∗list] j ∈ List.range NBUF, bslotAt γ curCtx j (Ls j) from by
    rw [updAtB_id]) $$ Hs
  ihave Hscan := bdScan_pack γ V tl M Ls ord devs bnos $$ [Ha Hlru Hpool Hkey Hs]
  case' _ => iframe Ha Hlru Hpool Hkey Hs
  by_cases hz : (Ls kk).length = 0
  · k_step (wp_s_branch c _ (KA.«bread» + 0x7c#64) true 20#13 15#5 0#5 (by decide) bop.BEQ)
      from (text_instr _ _ _ _ rfl rfl) Htext $$ [- $Hk $Hpc]
      with [bd_beqz_refcnt _ hlt, hz, bd_t_recyc]
    iintro Hk Hpc
    k_norm
    iapply Hcont $$ %_ %_ %true [] Hk Hpc Hscan
    ipureintro
    refine ⟨⟨fun _ => List.eq_nil_of_length_eq_zero hz, fun _ => rfl⟩, by simp [hz, bd_beqz_zero],
      ⟨?_, ?_, ?_, ?_⟩, ?_⟩ <;>
      first
        | exact bdOther_set R0 Rc hoth 15#5 _ (Or.inr rfl)
        | assumption
        | (simp only [RegMap.set_apply, BitVec.reduceEq, ite_false]; assumption)
  · k_step (wp_s_branch c _ (KA.«bread» + 0x7c#64) true 20#13 15#5 0#5 (by decide) bop.BEQ)
      from (text_instr _ _ _ _ rfl rfl) Htext $$ [- $Hk $Hpc]
      with [bd_beqz_refcnt _ hlt, hz]
    iintro Hk Hpc
    k_norm
    iapply Hcont $$ %_ %_ %false [] Hk Hpc Hscan
    ipureintro
    refine ⟨⟨fun h => absurd h (by decide), fun he => absurd (by rw [he]; rfl) hz⟩, by simp [hz, bd_beqz_zero],
      ⟨?_, ?_, ?_, ?_⟩, ?_⟩ <;>
      first
        | exact bdOther_set R0 Rc hoth 15#5 _ (Or.inr rfl)
        | assumption
        | (simp only [RegMap.set_apply, BitVec.reduceEq, ite_false]; assumption)

set_option maxHeartbeats 8000000 in
/-- **THE RECYCLE SCAN**, from `bread+0x7a` with the cursor on buffer `kk`,
by induction on the buffers still to visit -- backwards, so the recursion is
on the prefix of the LRU order. -/
theorem bd_bwd (c : CPU) (kc : KCtx) (hsie : kc.sie = false)
    (γ : BcacheNames) (V : BioView) (tl : Nat) (M : RegMapF Nat) (Ls : Nat → List Nat)
    (ord : List Nat) (devs bnos : Nat → BitVec 32) (dev bno : BitVec 32)
    (hord : ord.Perm (List.range NBUF)) (R0 : RegMap) :
    ∀ (o1 o2 : List Nat) (kk : Nat) (Rc : RegMap),
      ord = o1 ++ kk :: o2 → bdFwdRegs dev bno kk Rc → bdOther R0 Rc →
      (kctx c (kc.withRegs Rc) ∗ pcIs c (KA.«bread» + 0x7a#64) ∗
        bdScan γ V tl M Ls ord devs bnos ∗
        (∀ (kk2 : Nat) (Rc2 : RegMap),
          ⌜kk2 < NBUF ∧ Ls kk2 = [] ∧ bdFwdRegs dev bno kk2 Rc2 ∧ bdOther R0 Rc2⌝ -∗
          kctx c (kc.withRegs Rc2) -∗ pcIs c (KA.«bread» + 0x90#64) -∗
          bdScan γ V tl M Ls ord devs bnos -∗ wpLoop c) ∗
        (∀ Rc2 : RegMap, ⌜bdOther R0 Rc2⌝ -∗
          kctx c (kc.withRegs Rc2) -∗ pcIs c (KA.«bread» + 0x84#64) -∗
          bdScan γ V tl M Ls ord devs bnos -∗ wpLoop c)
        ⊢ wpLoop (GF := GF) c) := by
  intro o1
  induction o1 using FromMathlib.List.reverseRec with
  | nil =>
    intro o2 kk Rc hsplit hregs hoth
    have hkk : kk < NBUF := bd_ord_lt ord hord kk (by rw [hsplit]; simp)
    iintro ⟨Hk, Hpc, Hscan, Hrec, Hpan⟩
    iapply (bd_bwd_step c kc hsie γ V tl M Ls ord devs bnos dev bno R0 Rc kk hkk hregs hoth)
    iframe Hk Hpc Hscan
    iintro %Rc2 %pc2 %zero %hp Hk Hpc Hscan
    cases zero with
    | true =>
      obtain ⟨hiff, hpc2, hregs2, hoth2⟩ := hp
      have hpc' : pc2 = KA.«bread» + 0x90#64 := by rw [hpc2]; simp
      subst hpc'
      iapply Hrec $$ %kk %Rc2 [] Hk Hpc Hscan
      ipureintro; exact ⟨hkk, hiff.1 rfl, hregs2, hoth2⟩
    | false =>
      obtain ⟨hiff, hpc2, hregs2, hoth2⟩ := hp
      have hpc' : pc2 = KA.«bread» + 0x7e#64 := by rw [hpc2]; simp
      subst hpc'
      obtain ⟨g9, g14, g18, g19⟩ := hregs2
      icases kctx_kernelText _ _ $$ Hk with ⟨#Htext, Hk⟩
      icases bdScan_unpack γ V tl M Ls ord devs bnos $$ Hscan with ⟨Ha, Hlru, Hpool, Hkey, Hs⟩
      have hmp : ord.map bnode = ([] : List Nat).map bnode ++ bnode kk :: o2.map bnode := by
        rw [hsplit]; simp
      ihave Hlru := (show bcacheLruAt (GF := GF) curCtx bhead (ord.map bnode) ⊢
          bcacheLruAt curCtx bhead
            (([] : List Nat).map bnode ++ bnode kk :: o2.map bnode) from by
        rw [hmp]) $$ Hlru
      icases bcacheLru_prev_acc curCtx bhead (bnode kk) (([] : List Nat).map bnode)
        (o2.map bnode) $$ Hlru with ⟨Hpv, Hlcl⟩
      ihave Hpv := (show wordAtN (GF := GF) curCtx (bPrev (bnode kk)) 8 (DFrac.own 1)
            (blast (([] : List Nat).map bnode) bhead) ⊢
          wordPointsTo (bnode kk + 72#64) 8 (DFrac.own 1) bhead from by
        rw [wordAtN_cur, bd_prev_eq']; rfl) $$ Hpv
      k_step (wp_s_ld c _ (KA.«bread» + 0x7e#64) true 72#12 9#5 9#5 (by decide) (by decide)
          (DFrac.own 1) bhead)
        from (text_instr _ _ _ _ rfl rfl) Htext $$ [- $Hk $Hpc] with [g9]
      iintro Hk Hpc Hpv
      ihave Hpv := (show wordPointsTo (GF := GF) (bnode kk + 72#64) 8 (DFrac.own 1) bhead ⊢
          wordAtN curCtx (bPrev (bnode kk)) 8 (DFrac.own 1)
            (blast (([] : List Nat).map bnode) bhead) from by
        rw [wordAtN_cur, bd_prev_eq']; rfl) $$ Hpv
      ihave Hlru := Hlcl $$ Hpv
      ihave Hlru := (show bcacheLruAt (GF := GF) curCtx bhead
            (([] : List Nat).map bnode ++ bnode kk :: o2.map bnode) ⊢
          bcacheLruAt curCtx bhead (ord.map bnode) from by rw [hmp]) $$ Hlru
      ihave Hscan := bdScan_pack γ V tl M Ls ord devs bnos $$ [Ha Hlru Hpool Hkey Hs]
      case' _ => iframe Ha Hlru Hpool Hkey Hs
      -- bne s1,a4 : the cursor is the sentinel, so every buffer is pinned
      k_step (wp_s_branch c _ (KA.«bread» + 0x80#64) false 8186#13 9#5 14#5 (by decide) bop.BNE)
        from (text_instr _ _ _ _ rfl rfl) Htext $$ [- $Hk $Hpc] with [g14, bd_bne_eq]
      iintro Hk Hpc
      k_norm
      iapply Hpan $$ %_ [] Hk Hpc Hscan
      ipureintro
      exact bdOther_set R0 Rc2 hoth2 9#5 _ (Or.inl rfl)
  | append_singleton o1' kj ih =>
    intro o2 kk Rc hsplit hregs hoth
    have hkk : kk < NBUF := bd_ord_lt ord hord kk (by rw [hsplit]; simp)
    have hkj : kj < NBUF := bd_ord_lt ord hord kj (by rw [hsplit]; simp)
    iintro ⟨Hk, Hpc, Hscan, Hrec, Hpan⟩
    iapply (bd_bwd_step c kc hsie γ V tl M Ls ord devs bnos dev bno R0 Rc kk hkk hregs hoth)
    iframe Hk Hpc Hscan
    iintro %Rc2 %pc2 %zero %hp Hk Hpc Hscan
    cases zero with
    | true =>
      obtain ⟨hiff, hpc2, hregs2, hoth2⟩ := hp
      have hpc' : pc2 = KA.«bread» + 0x90#64 := by rw [hpc2]; simp
      subst hpc'
      iapply Hrec $$ %kk %Rc2 [] Hk Hpc Hscan
      ipureintro; exact ⟨hkk, hiff.1 rfl, hregs2, hoth2⟩
    | false =>
      obtain ⟨hiff, hpc2, hregs2, hoth2⟩ := hp
      have hpc' : pc2 = KA.«bread» + 0x7e#64 := by rw [hpc2]; simp
      subst hpc'
      obtain ⟨g9, g14, g18, g19⟩ := hregs2
      icases kctx_kernelText _ _ $$ Hk with ⟨#Htext, Hk⟩
      icases bdScan_unpack γ V tl M Ls ord devs bnos $$ Hscan with ⟨Ha, Hlru, Hpool, Hkey, Hs⟩
      have hmp : ord.map bnode
          = (o1' ++ [kj]).map bnode ++ bnode kk :: o2.map bnode := by rw [hsplit]; simp
      ihave Hlru := (show bcacheLruAt (GF := GF) curCtx bhead (ord.map bnode) ⊢
          bcacheLruAt curCtx bhead
            ((o1' ++ [kj]).map bnode ++ bnode kk :: o2.map bnode) from by rw [hmp]) $$ Hlru
      icases bcacheLru_prev_acc curCtx bhead (bnode kk) ((o1' ++ [kj]).map bnode)
        (o2.map bnode) $$ Hlru with ⟨Hpv, Hlcl⟩
      ihave Hpv := (show wordAtN (GF := GF) curCtx (bPrev (bnode kk)) 8 (DFrac.own 1)
            (blast ((o1' ++ [kj]).map bnode) bhead) ⊢
          wordPointsTo (bnode kk + 72#64) 8 (DFrac.own 1) (bnode kj) from by
        rw [wordAtN_cur, bd_prev_eq', bd_blast_map]) $$ Hpv
      k_step (wp_s_ld c _ (KA.«bread» + 0x7e#64) true 72#12 9#5 9#5 (by decide) (by decide)
          (DFrac.own 1) (bnode kj))
        from (text_instr _ _ _ _ rfl rfl) Htext $$ [- $Hk $Hpc] with [g9]
      iintro Hk Hpc Hpv
      ihave Hpv := (show wordPointsTo (GF := GF) (bnode kk + 72#64) 8 (DFrac.own 1) (bnode kj) ⊢
          wordAtN curCtx (bPrev (bnode kk)) 8 (DFrac.own 1)
            (blast ((o1' ++ [kj]).map bnode) bhead) from by
        rw [wordAtN_cur, bd_prev_eq', bd_blast_map]) $$ Hpv
      ihave Hlru := Hlcl $$ Hpv
      ihave Hlru := (show bcacheLruAt (GF := GF) curCtx bhead
            ((o1' ++ [kj]).map bnode ++ bnode kk :: o2.map bnode) ⊢
          bcacheLruAt curCtx bhead (ord.map bnode) from by rw [hmp]) $$ Hlru
      ihave Hscan := bdScan_pack γ V tl M Ls ord devs bnos $$ [Ha Hlru Hpool Hkey Hs]
      case' _ => iframe Ha Hlru Hpool Hkey Hs
      -- bne s1,a4 : the cursor is a real buffer, so the loop goes round
      k_step (wp_s_branch c _ (KA.«bread» + 0x80#64) false 8186#13 9#5 14#5 (by decide) bop.BNE)
        from (text_instr _ _ _ _ rfl rfl) Htext $$ [- $Hk $Hpc]
        with [g14, bd_bne_ne _ _ (bnode_ne_bhead kj hkj), bd_t_bwd]
      iintro Hk Hpc
      k_norm
      iapply (ih (kk :: o2) kj _ (by rw [hsplit]; simp)
        (by refine ⟨?_, ?_, ?_, ?_⟩ <;>
              first
                | (simp only [RegMap.set_apply, BitVec.reduceEq, ite_true, ite_false]; rfl)
                | (simp only [RegMap.set_apply, BitVec.reduceEq, ite_false]; assumption))
        (bdOther_set R0 Rc2 hoth2 9#5 _ (Or.inl rfl)))
      iframe Hk Hpc Hscan Hrec Hpan

end

end Xv6
