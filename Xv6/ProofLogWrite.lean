/-
Proof of `log_write`'s specification (`Xv6.LOG_WRITE`), given the
interfaces of `acquire`, `release` and `bpin`.  A port of Rocq
`ProofLogWrite.v` against the Lean image.

    void log_write(struct buf *b) {
      acquire(&log.lock);
      if (log.lh.n >= LOGSIZE) panic("too big a transaction");
      if (log.outstanding < 1) panic("log_write outside of trans");
      for (i = 0; i < log.lh.n; i++)
        if (log.lh.block[i] == b->blockno) break;
      log.lh.block[i] = b->blockno;
      if (i == log.lh.n) { bpin(b); log.lh.n++; }
      release(&log.lock);
    }

Structure (65 instructions, `+0x00 .. +0xc2`): a four-slot `ra`/`s0`/`s1`
frame, `s1 = b`, `acquire(&log)`, the two dead guards, the scan at
`+0x44`, the common store at `+0x94` and the append tail at `+0x66`
(`bpin`, `lh.n++`), then `release` and the epilogue at `+0xba`.

THE SHAPE.  `log_write` does not park, so the whole critical section runs
at one hart with `SIE` off; only the prologue and the epilogue see the
caller's `k.sie`, which is why the entry and the exit use the `_gen`
step forms (`Xv6/ProofBpin.lean`'s shape) and the interior does not.

THE SCAN is an `iloeb` over the index `i` with the rest of the world
abstracted into ONE proposition `Q` (`Xv6.lw_scan`): the loop reads
`lh.block[]` and nothing else, so nothing else has to appear in its
invariant.  Its two exits are the ABSORB index (`i < n` with
`W[i] = b->blockno`) and the APPEND fall-through (`i = n`).

THE GHOST STEP.  Both arms spend a budget unit (`Xv6.logSpendStep`), mint
a registry row at the current epoch (`Xv6.logMintLogged`) and move the
logged view (`Xv6.fsCache_update`) off the caller's client half and the
payload's machinery half.  The append arm additionally flips the block's
pin (`Xv6.fsDirty_flip`), grows `W`/`LB` by the block, takes the junk
slot `lh.block[n]` out of the header's spare run and hands one pool unit
back in place of the one `bpin` absorbed.
-/
import Xv6.SpecLogWrite
import Xv6.LogLedger
import Xv6.BcacheLock
import Xv6.CodeTactics
import MachCSL.WpSmodeFrame12b

namespace Xv6

open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode Std MachCSL
open LeanRV64D

attribute [local semireducible] LeanRV64D.Functions.hartSupports LeanRV64D.Functions.currentlyEnabled

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-! ## The constants the image computes

Every `auipc`/`addi` pair that materialises `&log` normalises to the same
offset (`+0x1e4f0`), because the relocation is computed from each pair's
own `auipc`. -/


theorem lw_br_acq : KA.«log_write» + 0xffffffffffffcd48#64 = KA.«acquire» := by decide
theorem lw_br_bpin : KA.«log_write» + 0xffffffffffffeedc#64 = KA.«bpin» := by decide
theorem lw_br_rel : KA.«log_write» + 0xffffffffffffcdd0#64 = KA.«release» := by decide
theorem lw_ret_18 : jumpPc (KA.«log_write» + 0x18#64) = KA.«log_write» + 0x18#64 := by decide
theorem lw_ret_6c : jumpPc (KA.«log_write» + 0x6c#64) = KA.«log_write» + 0x6c#64 := by decide
theorem lw_ret_ba : jumpPc (KA.«log_write» + 0xba#64) = KA.«log_write» + 0xba#64 := by decide

theorem lw_log : KA.«log_write» + 0x1e4f0#64 = logAddr := by unfold logAddr; decide
theorem lw_lhn : KA.«log_write» + 0x1e51c#64 = lhNAddr := by unfold lhNAddr logAddr; decide
theorem lw_lout : KA.«log_write» + 0x1e50c#64 = lOut := by unfold lOut logAddr; decide
theorem lw_blk0 : KA.«log_write» + 0x1e520#64 = lhBlock 0 := by unfold lhBlock logAddr; decide

theorem lw_succ64 (m : Nat) : BitVec.ofNat 64 m + 1#64 = BitVec.ofNat 64 (m + 1) := by
  show _ + BitVec.ofNat 64 1 = _
  rw [← ofNat64_add]

theorem lw_shl2 (i : Nat) (h : i ≤ LOGBLOCKS) :
    (BitVec.ofNat 64 i) <<< 2 = BitVec.ofNat 64 (4 * i) := by
  unfold LOGBLOCKS at h
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.reducePow]
  omega

theorem lw_add32 (i : Nat) :
    BitVec.ofNat 64 (4 * i) + 32#64 = BitVec.ofNat 64 (4 * i + 32) := by
  show _ + BitVec.ofNat 64 32 = _
  rw [← ofNat64_add]

theorem lw_blk_addr (i : Nat) :
    logAddr + BitVec.ofNat 64 (4 * i + 32) + 16#64 = lhBlock i := by
  unfold lhBlock
  rw [BitVec.add_assoc]
  congr 1
  show _ + BitVec.ofNat 64 16 = _
  rw [← ofNat64_add]
  congr 1 <;> omega

theorem lw_cursor (i : Nat) : lhBlock i + 4#64 = lhBlock (i + 1) := by
  unfold lhBlock
  rw [BitVec.add_assoc]
  congr 1
  show _ + BitVec.ofNat 64 4 = _
  rw [← ofNat64_add]
  congr 1 <;> omega

theorem lw_ext_sext (x : BitVec 32) : BitVec.extractLsb' 0 32 (BitVec.signExtend 64 x) = x := by
  bv_decide

theorem lw_beq_sext (x y : BitVec 32) :
    bcond bop.BEQ (BitVec.signExtend 64 x) (BitVec.signExtend 64 y) = decide (x = y) := by
  show (_ == _) = _
  by_cases h : x = y
  · subst h; simp
  · rw [decide_eq_false h]
    refine beq_eq_false_iff_ne.2 (fun hc => h ?_)
    have hx := congrArg (BitVec.extractLsb' 0 32) hc
    rwa [lw_ext_sext, lw_ext_sext] at hx

theorem lw_beq_nat (a b : Nat) (ha : a ≤ LOGBLOCKS) (hb : b ≤ LOGBLOCKS) :
    bcond bop.BEQ (BitVec.ofNat 64 a) (BitVec.ofNat 64 b) = decide (a = b) := by
  unfold LOGBLOCKS at ha hb
  show (_ == _) = _
  by_cases h : a = b
  · subst h; simp
  · rw [decide_eq_false h]
    refine beq_eq_false_iff_ne.2 (fun hc => h ?_)
    have := congrArg BitVec.toNat hc
    simp only [BitVec.toNat_ofNat] at this
    omega

theorem lw_bne_nat (a b : Nat) (ha : a ≤ LOGBLOCKS) (hb : b ≤ LOGBLOCKS) :
    bcond bop.BNE (BitVec.ofNat 64 a) (BitVec.ofNat 64 b) = decide (¬ (a = b)) := by
  show (_ != _) = _
  show (!(_ == _)) = _
  rw [show ((BitVec.ofNat 64 a == BitVec.ofNat 64 b) =
      bcond bop.BEQ (BitVec.ofNat 64 a) (BitVec.ofNat 64 b)) from rfl,
    lw_beq_nat a b ha hb, ← decide_not]

theorem lw_toInt_small (a : Nat) (h : a < 2 ^ 63) : (BitVec.ofNat 64 a).toInt = (a : Int) := by
  rw [BitVec.toInt_eq_toNat_cond]
  simp only [BitVec.toNat_ofNat]
  rw [if_pos (by omega)]
  omega

theorem lw_blt29 (n : Nat) (h : n ≤ LOGBLOCKS) :
    bcond bop.BLT (BitVec.ofNat 64 29) (BitVec.ofNat 64 n) = decide (29 < n) := by
  unfold LOGBLOCKS at h
  show BitVec.slt _ _ = _
  rw [BitVec.slt]
  rw [lw_toInt_small 29 (by omega), lw_toInt_small n (by omega)]
  by_cases hn : 29 < n <;> simp [hn] <;> omega

theorem lw_blez (m : Nat) (h : m ≤ LOGBLOCKS) :
    bcond bop.BGE 0#64 (BitVec.ofNat 64 m) = decide (m = 0) := by
  unfold LOGBLOCKS at h
  show (!(BitVec.slt _ _)) = _
  rw [BitVec.slt]
  rw [show ((0#64 : BitVec 64).toInt = 0) from by decide, lw_toInt_small m (by omega)]
  by_cases hm : m = 0 <;> simp [hm] <;> omega



/-! ## The context and the register pins -/

/-- The held set goes back to the caller's once the final `release` fires. -/
theorem lw_filter (l : List String) (h : ¬ ("log" ∈ l)) :
    ("log" :: l).filter (fun x => x ≠ "log") = l := by
  rw [List.filter_cons_of_neg (by simp)]
  exact List.filter_eq_self.2 (fun x hx => by simp; intro e; subst e; exact h hx)

/-- The context `log_write` runs in once its frame is up and it holds the
"log" spinlock. -/
def lwK (k : KCtx) (a b : Bool) : KCtx :=
  ((k.pushOffAt a b).pushed 4).withLocks ("log" :: k.locks)

@[simp] theorem lwK_sie (k : KCtx) (a b : Bool) : (lwK k a b).sie = false := rfl
@[simp] theorem lwK_noff (k : KCtx) (a b : Bool) : (lwK k a b).noff = k.noff + 1 := rfl
@[simp] theorem lwK_intena (k : KCtx) (a b : Bool) : (lwK k a b).intena = k.intena := rfl
@[simp] theorem lwK_locks (k : KCtx) (a b : Bool) : (lwK k a b).locks = "log" :: k.locks := rfl
@[simp] theorem lwK_tier (k : KCtx) (a b : Bool) : (lwK k a b).tier = k.tier := rfl
@[simp] theorem lwK_proc (k : KCtx) (a b : Bool) : (lwK k a b).proc = k.proc := rfl
@[simp] theorem lwK_regs (k : KCtx) (a b : Bool) : (lwK k a b).regs = k.regs := rfl
@[simp] theorem lwK_avail (k : KCtx) (a b : Bool) :
    (lwK k a b).avail = trapRes k.sie + k.avail - 4 := rfl

/-- What `acquire` hands back, folded. -/
theorem lwK_fold (k : KCtx) (a b : Bool) (R0 R : RegMap) (hK : 4 ≤ k.avail) :
    ((((k.pushed 4).withRegs R0).pushOffAt a b).withRegs R).withLocks ("log" :: k.locks) =
      (lwK k a b).withRegs R := by
  unfold lwK
  obtain ⟨regs, sie, spie, spp, avail, noff, intena, locks, tier, root, proc⟩ := k
  simp only at hK ⊢
  simp only [KCtx.pushed, KCtx.withRegs, KCtx.pushOffAt, KCtx.withLocks, KCtx.mk.injEq,
    _root_.true_and, _root_.and_true]
  omega

/-- ...and what `release` hands back: `log_write`'s own `push_off` unwound
and the held set back to the caller's. -/
theorem lwK_popExit (k : KCtx) (a b : Bool) (hwf : k.wf) (hlk : ¬ ("log" ∈ k.locks)) :
    ((lwK k a b).popExit k.sie).withLocks (("log" :: k.locks).filter (fun x => x ≠ "log")) =
      (k.withSpie a b).pushed 4 := by
  rw [lw_filter k.locks hlk]
  unfold lwK
  rw [KCtx.popExit_withLocks, KCtx.popExit_pushed, KCtx.pushOffAt_popExit k a b hwf]
  obtain ⟨regs, sie, spie, spp, avail, noff, intena, locks, tier, root, proc⟩ := k
  rfl

/-- The registers `log_write` keeps live across its calls: the frame
pointers, `s1 = b`, and the callee-saved registers it never touches. -/
def lwPins (kR : RegMap) (kk : Nat) (R : RegMap) : Prop :=
  R 2#5 = kR 2#5 + 0xFFFFFFFFFFFFFFE0#64 ∧ R 8#5 = kR 2#5 ∧ R 9#5 = bnode kk ∧
  R 18#5 = kR 18#5 ∧ R 19#5 = kR 19#5 ∧ R 20#5 = kR 20#5 ∧ R 21#5 = kR 21#5 ∧
  R 22#5 = kR 22#5 ∧ R 23#5 = kR 23#5 ∧ R 24#5 = kR 24#5 ∧ R 25#5 = kR 25#5 ∧
  R 26#5 = kR 26#5 ∧ R 27#5 = kR 27#5

theorem lwPins_cs (kR : RegMap) (kk : Nat) (R R' : RegMap) (h : lwPins kR kk R)
    (hcs : calleeSaved R R') : lwPins kR kk R' := by
  obtain ⟨a2, a8, a9, a18, a19, a20, a21, a22, a23, a24, a25, a26, a27⟩ := h
  obtain ⟨b2, b8, b9, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27⟩ := hcs
  exact ⟨b2.trans a2, b8.trans a8, b9.trans a9, b18.trans a18, b19.trans a19, b20.trans a20,
    b21.trans a21, b22.trans a22, b23.trans a23, b24.trans a24, b25.trans a25, b26.trans a26,
    b27.trans a27⟩

theorem lwPins_set (kR : RegMap) (kk : Nat) (R : RegMap) (h : lwPins kR kk R)
    (i : BitVec 5) (v : BitVec 64)
    (hi : i ≠ 2#5 ∧ i ≠ 8#5 ∧ i ≠ 9#5 ∧ i ≠ 18#5 ∧ i ≠ 19#5 ∧ i ≠ 20#5 ∧ i ≠ 21#5 ∧
      i ≠ 22#5 ∧ i ≠ 23#5 ∧ i ≠ 24#5 ∧ i ≠ 25#5 ∧ i ≠ 26#5 ∧ i ≠ 27#5) :
    lwPins kR kk (R.set i v) := by
  obtain ⟨a2, a8, a9, a18, a19, a20, a21, a22, a23, a24, a25, a26, a27⟩ := h
  obtain ⟨n2, n8, n9, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27⟩ := hi
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [RegMap.set_apply] <;>
    first
      | (rw [if_neg (Ne.symm n2)]; exact a2)
      | (rw [if_neg (Ne.symm n8)]; exact a8)
      | (rw [if_neg (Ne.symm n9)]; exact a9)
      | (rw [if_neg (Ne.symm n18)]; exact a18)
      | (rw [if_neg (Ne.symm n19)]; exact a19)
      | (rw [if_neg (Ne.symm n20)]; exact a20)
      | (rw [if_neg (Ne.symm n21)]; exact a21)
      | (rw [if_neg (Ne.symm n22)]; exact a22)
      | (rw [if_neg (Ne.symm n23)]; exact a23)
      | (rw [if_neg (Ne.symm n24)]; exact a24)
      | (rw [if_neg (Ne.symm n25)]; exact a25)
      | (rw [if_neg (Ne.symm n26)]; exact a26)
      | (rw [if_neg (Ne.symm n27)]; exact a27)

/-! ## The ledger's and the batch's bookkeeping -/


/-! ## Pure bookkeeping -/

theorem lw_mem_map (W : List (BitVec 32)) (b : BitVec 32) :
    b.toNat ∈ W.map (fun w => w.toNat) ↔ b ∈ W := by
  constructor
  · intro h
    obtain ⟨w, hw, he⟩ := List.mem_map.1 h
    have : w = b := by
      apply BitVec.eq_of_toNat_eq; exact he
    exact this ▸ hw
  · intro h; exact List.mem_map.2 ⟨b, h, rfl⟩

/-- A replacement at a live key leaves the list view's length alone. -/
theorem lw_toList_length_update {V : Type} (m : RegMapF V) (k : Nat) (v w : V)
    (h : PartialMap.get? m k = some v) :
    (FiniteMap.toList (PartialMap.insert m k w)).length = (FiniteMap.toList m).length := by
  have hd : PartialMap.get? (PartialMap.delete m k) k = none := get?_delete_eq rfl
  rw [(toListP_insert_delete m k w).length_eq,
    toList_length_insert _ k w hd, ← toList_length_delete m k v h]

/-- A live entry's budget is at most the whole reservation sum. -/
theorem lw_opSum_ge (om : RegMapF OpEntry) (i : Nat) (e : OpEntry)
    (h : PartialMap.get? om i = some e) : e.bud ≤ opSum om := by
  rw [opSum_delete om i e h]; omega

/-- A live entry keeps the outstanding cell above zero. -/
theorem lw_out_pos (om : RegMapF OpEntry) (i : Nat) (e : OpEntry)
    (h : PartialMap.get? om i = some e) : 1 ≤ (FiniteMap.toList om).length := by
  rw [toList_length_delete om i e h]; omega

/-- The watermark bounds a live key. -/
theorem lw_key_lt (om : RegMapF OpEntry) (nx i : Nat) (e : OpEntry)
    (hfresh : ∀ j, nx ≤ j → PartialMap.get? om j = none)
    (h : PartialMap.get? om i = some e) : i < nx := by
  rcases Nat.lt_or_ge i nx with hc | hc
  · exact hc
  · rw [hfresh i hc] at h; exact absurd h (by simp)

/-- ...so the watermark survives the replacement. -/
theorem lw_fresh_update {V : Type} (m : RegMapF V) (nx i : Nat) (w : V) (hi : i < nx)
    (hfresh : ∀ j, nx ≤ j → PartialMap.get? m j = none) :
    ∀ j, nx ≤ j → PartialMap.get? (PartialMap.insert m i w) j = none := by
  intro j hj
  rw [get?_insert_ne (by omega : i ≠ j)]
  exact hfresh j hj

/-- `Std.ExtTreeSet.toList` has no duplicates. -/
theorem lw_cov_nodup (cov : Std.ExtTreeSet Nat compare) : cov.toList.Nodup := by
  have h := Std.ExtTreeSet.distinct_toList (t := cov)
  refine List.Pairwise.imp (fun {a b} hab => ?_) h
  intro he
  exact hab (by subst he; simp)

section
variable {GF : BundledGFunctors} [FsBlocksG GF]

/-- Outside `b`, growing the batch by `b` does not move a pin half. -/
theorem lw_dirty_eq (γfs : FsNames) (l LB LB' : List Nat) (b : Nat) (hb : ¬ (b ∈ l))
    (hLB : ∀ x, ¬ (x = b) → (x ∈ LB' ↔ x ∈ LB)) :
    ([∗list] x ∈ l, fsDirtyHalf (GF := GF) γfs x (decide (x ∈ LB))) =
      ([∗list] x ∈ l, fsDirtyHalf (GF := GF) γfs x (decide (x ∈ LB'))) := by
  refine BigSepL.bigSepL_eq (fun {k x} hget => ?_)
  have hx : x ∈ l := List.mem_of_getElem? hget
  have hne : ¬ (x = b) := fun he => hb (he ▸ hx)
  congr 1
  exact (decide_eq_decide.2 (hLB x hne)).symm

/-- **The append arm's pin flip, at the big-op**: the block's log-side half
comes out at `false` and goes back at `true`, with the batch grown by the
block. -/
theorem lw_dirty_grow (γfs : FsNames) (LB LB' : List Nat) (b : Nat)
    (hb : ¬ (b ∈ LB)) (hb' : b ∈ LB')
    (hLB : ∀ x, ¬ (x = b) → (x ∈ LB' ↔ x ∈ LB)) :
    ∀ (l : List Nat), l.Nodup → b ∈ l →
      (([∗list] x ∈ l, fsDirtyHalf (GF := GF) γfs x (decide (x ∈ LB))) ⊢
        fsDirtyHalf γfs b false ∗
        (fsDirtyHalf γfs b true -∗
          [∗list] x ∈ l, fsDirtyHalf (GF := GF) γfs x (decide (x ∈ LB'))))
  | [], _, hm => absurd hm (by simp)
  | a :: l, hnd, hm => by
    obtain ⟨hal, hndl⟩ := List.nodup_cons.1 hnd
    show (fsDirtyHalf (GF := GF) γfs a (decide (a ∈ LB)) ∗
        ([∗list] x ∈ l, fsDirtyHalf (GF := GF) γfs x (decide (x ∈ LB)))) ⊢
      fsDirtyHalf γfs b false ∗
      (fsDirtyHalf γfs b true -∗ (fsDirtyHalf γfs a (decide (a ∈ LB')) ∗
        ([∗list] x ∈ l, fsDirtyHalf (GF := GF) γfs x (decide (x ∈ LB')))))
    by_cases hab : a = b
    · subst hab
      rw [lw_dirty_eq (GF := GF) γfs l LB LB' a hal hLB,
        show (decide (a ∈ LB) = false) from decide_eq_false hb,
        show (decide (a ∈ LB') = true) from decide_eq_true hb']
      iintro ⟨H1, H2⟩
      iframe H1
      iintro H1
      iframe H1 H2
    · have hm' : b ∈ l := by
        rcases List.mem_cons.1 hm with he | he
        · exact absurd he.symm hab
        · exact he
      have ih := lw_dirty_grow γfs LB LB' b hb hb' hLB l hndl hm'
      rw [show (decide (a ∈ LB') = decide (a ∈ LB)) from decide_eq_decide.2 (hLB a hab)]
      iintro ⟨H1, H2⟩
      icases ih $$ H2 with ⟨Hb, Hcl⟩
      iframe Hb
      iintro Hb
      isplitr [Hcl Hb]
      · iexact H1
      · iapply Hcl; iexact Hb

end


/-! ## Opening the lock's payload and the handle -/

section
variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF]
variable [BcacheG GF] [SleepLockG GF] [DiskG GF] [FsBlocksG GF] [LogG GF] [CurCtx]

/-! ## The three call sites -/

theorem lw_ac (AC : ACQUIRE) (c : CPU) (k' : KCtx) (γ : LogNames) (γb : BcacheNames)
    (γfs : FsNames) (cov : Std.ExtTreeSet Nat compare) (ls : Nat) (dev : BitVec 32)
    (ha0 : k'.regs 10#5 = logAddr)
    (hnoff : k'.noff + 1 < 2 ^ 31) (hK : 10 ≤ k'.avail) (hs : ¬ ("log" ∈ k'.locks)) :
    kctx c k' ∗ pcIs c KA.«acquire» ∗ logCtx γ γb γfs cov ls dev ∗
    wpNext k'.sie k'.proc c (fun cpu' => iprop(∀ (spie spp : Bool) (R' : RegMap),
      ⌜k'.sie = false → spie = k'.spie ∧ spp = k'.spp⌝ -∗
      kctx cpu' (((k'.pushOffAt spie spp).withRegs R').withLocks ("log" :: k'.locks)) -∗
      pcIs cpu' (jumpPc (k'.regs 1#5)) -∗ ⌜calleeSaved k'.regs R'⌝ -∗
      locked γ.lk cpu' -∗ logResAt γ γb γfs cov ls curCtx -∗ (∃ K : Nat, viewLb cpu' K) -∗
      sieArm cpu' k'.sie k'.proc -∗ wpLoop cpu'))
    ⊢ wpLoop (GF := GF) c := by
  have h := AC.wp_acquire (hlc := hlc) (GF := GF) c k' γ.lk "log"
    (logResAt γ γb γfs cov ls) hnoff hK hs
  unfold wp_acquire_body at h
  simp only [acquireAddr] at h
  rw [ha0] at h
  iintro ⟨Hk, Hpc, #Hctx, HΦ⟩
  ihave #Hlk := logCtx_lock γ γb γfs cov ls dev $$ Hctx
  iapply h
  iframe Hk Hpc Hlk HΦ

theorem lw_re (RE : RELEASE) (c : CPU) (k' : KCtx) (γ : LogNames) (γb : BcacheNames)
    (γfs : FsNames) (cov : Std.ExtTreeSet Nat compare) (ls : Nat) (dev : BitVec 32)
    (ha0 : k'.regs 10#5 = logAddr)
    (hsie : k'.sie = false) (hnoff : 1 ≤ k'.noff) (hK : 10 ≤ k'.avail)
    (reen : Bool) (hreen : reen = (decide (k'.noff = 1) && k'.intena))
    (hon : reen = true → k'.tier = .kpt ∧ trapRes true + 6 ≤ k'.avail) :
    kctx c k' ∗ pcIs c KA.«release» ∗ logCtx γ γb γfs cov ls dev ∗
    locked γ.lk c ∗ logResAt γ γb γfs cov ls curCtx ∗ popArm c k' reen ∗
    wpNext (k'.popExit reen).sie k'.proc c (fun cpu' => iprop(∀ R' : RegMap,
      kctx cpu' (((k'.popExit reen).withRegs R').withLocks
        (k'.locks.filter (fun x => x ≠ "log"))) -∗
      pcIs cpu' (jumpPc (k'.regs 1#5)) -∗ ⌜calleeSaved k'.regs R'⌝ -∗ wpLoop cpu'))
    ⊢ wpLoop (GF := GF) c := by
  have h := RE.wp_release (hlc := hlc) (GF := GF) c k' γ.lk "log"
    (logResAt γ γb γfs cov ls) hsie hnoff hK reen hreen hon
  unfold wp_release_body at h
  simp only [releaseAddr] at h
  rw [ha0] at h
  iintro ⟨Hk, Hpc, #Hctx, Hlocked, Hpay, Harm, HΦ⟩
  ihave #Hlk := logCtx_lock γ γb γfs cov ls dev $$ Hctx
  iapply h
  iframe Hk Hpc Hlk Hlocked Hpay Harm HΦ

theorem lw_bp (BP : BPIN) (c : CPU) (k' : KCtx) (γl : GName) (γb : BcacheNames)
    (V : BioView GF) (kk : Nat)
    (hnoff : k'.noff + 1 < 2 ^ 31) (hK : 14 ≤ k'.avail) (hlk : ¬ ("bcache" ∈ k'.locks))
    (hkk : kk < NBUF) (ha0 : k'.regs 10#5 = bnode kk) :
    kctx c k' ∗ pcIs c KA.«bpin» ∗ bioCtx γl γb V ∗ bslot γb ∗
    wpNext k'.sie k'.proc c (fun cpu' => iprop(∀ (spie spp : Bool) (R' : RegMap),
      ⌜k'.sie = false → spie = k'.spie ∧ spp = k'.spp⌝ -∗
      kctx cpu' ((k'.withSpie spie spp).withRegs R') -∗ pcIs cpu' (jumpPc (k'.regs 1#5)) -∗
      ⌜calleeSaved k'.regs R'⌝ -∗ ∀ (dv : BitVec 32), ∀ (bn : BitVec 32), bref γb kk dv bn -∗ wpLoop cpu'))
    ⊢ wpLoop (GF := GF) c := by
  have h := BP.wp_bpin (hlc := hlc) (GF := GF) c k' γl γb V kk hnoff hK hlk hkk ha0
  unfold wp_bpin_body at h
  simp only [bpinAddr] at h
  exact h







/-! ## The exit: `release(&log.lock)` and the epilogue -/

set_option maxHeartbeats 8000000 in
theorem lw_exit (RE : RELEASE) (c : CPU) (k : KCtx) (a b : Bool) (R : RegMap) (kk : Nat)
    (γ : LogNames) (γb : BcacheNames) (γfs : FsNames) (cov : Std.ExtTreeSet Nat compare)
    (ls : Nat) (dev : BitVec 32)
    (hK : logWriteSlots ≤ k.avail) (hwf : k.wf) (hlk : ¬ ("log" ∈ k.locks))
    (hR : lwPins k.regs kk R) :
    kctx c ((lwK k a b).withRegs R) ∗ pcIs c (KA.«log_write» + 0xae#64) ∗
    logCtx γ γb γfs cov ls dev ∗ locked γ.lk c ∗ logResAt γ γb γfs cov ls curCtx ∗
    sieArm c k.sie k.proc ∗
    frame4s1 (k.regs 2#5) (k.regs 1#5) (k.regs 8#5) (k.regs 9#5) ∗
    wpNext k.sie k.proc c (fun cpu' => iprop(∀ R'' : RegMap,
      kctx cpu' ((k.withSpie a b).withRegs R'') -∗ pcIs cpu' (jumpPc (k.regs 1#5)) -∗
      ⌜calleeSaved k.regs R''⌝ -∗ wpLoop cpu'))
    ⊢ wpLoop (GF := GF) c := by
  have hK4 : 4 ≤ k.avail := by unfold logWriteSlots at hK; omega
  have hsie : (lwK k a b).sie = false := rfl
  obtain ⟨p2, p8, p9, p18, p19, p20, p21, p22, p23, p24, p25, p26, p27⟩ := id hR
  iintro ⟨Hk, Hpc, #Hctx, Hlocked, Hres, Harm, Hframe, Hnext⟩
  icases kctx_kernelText _ _ $$ Hk with ⟨#Htext, Hk⟩
  -- +0xae auipc a0,0x1e ; +0xb2 addi a0,a0,1090 ; +0xb6 jal release
  k_step (wp_s_auipc c _ (KA.«log_write» + 0xae#64) false 0x1e#20 10#5 (by decide))
    from (text_instr _ _ _ _ rfl rfl) Htext $$ [- $Hk $Hpc] with [lwK_sie k a b]
  iintro Hk Hpc
  k_step (wp_s_addi c _ (KA.«log_write» + 0xb2#64) false 1090#12 10#5 10#5 (by decide))
    from (text_instr _ _ _ _ rfl rfl) Htext $$ [- $Hk $Hpc] with [lwK_sie k a b, lw_log]
  iintro Hk Hpc
  k_step (wp_s_jal c _ (KA.«log_write» + 0xb6#64) false 2084122#21 1#5 (by decide))
    from (text_instr _ _ _ _ rfl rfl) Htext $$ [- $Hk $Hpc] with [lwK_sie k a b, lw_br_rel]
  iintro Hk Hpc
  iapply (lw_re RE c _ γ γb γfs cov ls dev ?ha0 ?hsr ?hnr ?hKr k.sie ?hrr ?hor)
    $$ [- $Hk $Hpc $Hlocked $Hres]
  rotate_right 1
  k_norm [lwK_sie k a b, lw_ret_ba, lwK_popExit k a b hwf hlk]
  iframe #
  isplitl [Harm]
  · iapply (popArm_sie c k _ (by rfl)) $$ Harm
  case ha0 => k_norm
  case hsr => k_norm [lwK_sie k a b]
  case hnr => k_norm; omega
  case hKr => k_norm; unfold logWriteSlots at hK; cases hs : k.sie <;> simp [trapRes] <;> omega
  case hrr => k_norm; exact KCtx.reen_of_wf k hwf
  case hor =>
    k_norm
    intro h
    obtain ⟨-, -, -, ht⟩ := hwf.2.2.1 h
    rw [h]
    simp only [trapRes, kvFrameSlots, ite_true]
    unfold logWriteSlots at hK
    exact ⟨ht, by omega⟩
  -- past the release: the epilogue
  iapply wpNext_mono _ _ _ _ _ $$ Hnext
  iintro %cr HΦ %R4 Hk Hpc %hcs4
  k_norm [lwK_sie k a b, lw_ret_ba, lwK_popExit k a b hwf hlk]
  unfold calleeSaved at hcs4
  k_norm at hcs4
  obtain ⟨e2, e8, e9, e18, e19, e20, e21, e22, e23, e24, e25, e26, e27⟩ := hcs4
  icases kctx_kernelText _ _ $$ Hk with ⟨#HT, Hk⟩
  iapply (wp_epilogue4s1_gen cr (k.withSpie a b) (KA.«log_write» + 0xba#64)
      (by simp only [KCtx.withSpie_avail]; exact hK4) R4 (by
        simp only [KCtx.withSpie_regs]; exact e2.trans p2)
      (k.regs 1#5) (k.regs 8#5) (k.regs 9#5)) $$ [- $Hk $Hpc $Hframe]
  k_code (text_instr _ _ _ _ rfl rfl) HT
  k_norm_g
  iframe
  inext
  iapply wpNext_off_intro
  iintro Hk Hpc
  iapply HΦ $$ %_ Hk Hpc
  ipureintro
  exact bc_calleeSaved_epi k.regs R4 (e18.trans p18) (e19.trans p19) (e20.trans p20)
    (e21.trans p21) (e22.trans p22) (e23.trans p23) (e24.trans p24) (e25.trans p25)
    (e26.trans p26) (e27.trans p27)




/-- `Xv6.bufHold0`, opened just for `b->blockno` (the two `lw a?,12(s1)`). -/
theorem lw_hold_bno (γb : BcacheNames) (V : BioView GF) (kk : Nat) (pidv dev bno : BitVec 32)
    (bs bsd : List (BitVec 8)) :
    bufHold0 (GF := GF) γb V kk pidv dev bno bs bsd ⊢
      wordPointsTo (aBufBlockno (bnode kk)) 4 (DFrac.own (1 : Qp).half) bno ∗
      (wordPointsTo (aBufBlockno (bnode kk)) 4 (DFrac.own (1 : Qp).half) bno -∗
        bufHold0 γb V kk pidv dev bno bs bsd) := by
  unfold bufHold0 bufOwn
  iintro ⟨%h0, H1, H2, H3, H4, H5, H6, ⟨%hl, Hb, H7, H8⟩, H9⟩
  iframe Hb
  iintro Hb
  isplitr [H1 H2 H3 H4 H5 H6 Hb H7 H8 H9]
  · ipureintro; exact h0
  iframe H1 H2 H3 H4 H5 H6 H9
  isplitr [Hb H7 H8]
  · ipureintro; exact hl
  iframe Hb H7 H8

/-- `b->blockno`'s address, as `lw a1,12(s1)` computes it. -/
theorem lw_bno_addr (a : BitVec 64) : a + BitVec.signExtend 64 12#12 = aBufBlockno a := by
  unfold aBufBlockno
  congr 1

/-- `Xv6.logStateAt`, taken apart. -/
theorem lw_state_elim (γb : BcacheNames) (γfs : FsNames) (cov : Std.ExtTreeSet Nat compare)
    (ls n : Nat) (LB : List Nat) (pend : Nat → Prop) (ξ : CtxId) :
    logStateAt (GF := GF) γb γfs cov ls n LB pend ξ ⊢
      ∃ (W : List (BitVec 32)) (L : BlockMap) (D : RegMapF Bool),
        ⌜n = W.length ∧ n ≤ LOGBLOCKS⌝ ∗
        ⌜LB = W.map (fun w => w.toNat)⌝ ∗
        ⌜(W.map (fun w => w.toNat)).Nodup⌝ ∗
        ⌜∀ w ∈ W, fsHome cov ls w.toNat⌝ ∗
        wordAtN ξ lhNAddr 4 (DFrac.own 1) (BitVec.ofNat 32 n) ∗
        ([∗list] i ↦ w ∈ W, wordAtN ξ (lhBlock i) 4 (DFrac.own 1) w) ∗
        ([∗list] i ∈ List.range (LOGBLOCKS - n),
           ∃ junk : BitVec 32, wordAtN ξ (lhBlock (n + i)) 4 (DFrac.own 1) junk) ∗
        fsCacheAuth γfs L ∗ fsDirtyAuth γfs D ∗
        ([∗list] b ∈ cov.toList, fsDirtyHalf γfs b (decide (b ∈ LB))) ∗
        (∃ bsh : List (BitVec 8), fsChalf γfs (logHdrBno ls) bsh) ∗
        ([∗list] i ∈ List.range LOGBLOCKS, ∃ bs : List (BitVec 8),
           fsChalf γfs (logSlotBno ls i) bs) ∗
        bslots γb ((LOGBLOCKS - n) + 2) := by
  unfold logStateAt; iintro H; iexact H

/-- ...and put back together. -/
theorem lw_state_intro (γb : BcacheNames) (γfs : FsNames) (cov : Std.ExtTreeSet Nat compare)
    (ls n : Nat) (LB : List Nat) (pend : Nat → Prop) (ξ : CtxId)
    (W : List (BitVec 32)) (L : BlockMap) (D : RegMapF Bool)
    (h1 : n = W.length ∧ n ≤ LOGBLOCKS) (h2 : LB = W.map (fun w => w.toNat))
    (h3 : (W.map (fun w => w.toNat)).Nodup) (h4 : ∀ w ∈ W, fsHome cov ls w.toNat) :
    wordAtN ξ lhNAddr 4 (DFrac.own 1) (BitVec.ofNat 32 n) ∗
    ([∗list] i ↦ w ∈ W, wordAtN ξ (lhBlock i) 4 (DFrac.own 1) w) ∗
    ([∗list] i ∈ List.range (LOGBLOCKS - n),
       ∃ junk : BitVec 32, wordAtN ξ (lhBlock (n + i)) 4 (DFrac.own 1) junk) ∗
    fsCacheAuth γfs L ∗ fsDirtyAuth γfs D ∗
    ([∗list] b ∈ cov.toList, fsDirtyHalf γfs b (decide (b ∈ LB))) ∗
    (∃ bsh : List (BitVec 8), fsChalf γfs (logHdrBno ls) bsh) ∗
    ([∗list] i ∈ List.range LOGBLOCKS, ∃ bs : List (BitVec 8),
       fsChalf γfs (logSlotBno ls i) bs) ∗
    bslots γb ((LOGBLOCKS - n) + 2)
    ⊢ logStateAt (GF := GF) γb γfs cov ls n LB pend ξ := by
  unfold logStateAt
  iintro ⟨Hn, Hblk, Hjunk, HL, HD, Hd, Hhdr, Hsl, Hpool⟩
  iexists W, L, D
  isplitr [Hn Hblk Hjunk HL HD Hd Hhdr Hsl Hpool]
  · ipureintro; exact h1
  isplitr [Hn Hblk Hjunk HL HD Hd Hhdr Hsl Hpool]
  · ipureintro; exact h2
  isplitr [Hn Hblk Hjunk HL HD Hd Hhdr Hsl Hpool]
  · ipureintro; exact h3
  isplitr [Hn Hblk Hjunk HL HD Hd Hhdr Hsl Hpool]
  · ipureintro; exact h4
  iframe Hn Hblk Hjunk HL HD Hd Hhdr Hsl Hpool




/-- The `cmt = false` arm of `logResAt`, named. -/
def lwBatch (γ : LogNames) (γb : BcacheNames) (γfs : FsNames)
    (cov : Std.ExtTreeSet Nat compare) (ls : Nat) (om : RegMapF OpEntry) (E : Nat)
    (X : RegMapF (Nat × Nat)) (ξ : CtxId) : IProp GF := iprop%
  ∃ (n : Nat) (LB : List Nat),
    ⌜n + opSum om ≤ LOGBLOCKS⌝ ∗
    ⌜∀ i e, PartialMap.get? om i = some e → ∀ x ∈ e.set, x ∈ LB⌝ ∗
    ⌜∀ i p, PartialMap.get? X i = some p → p.1 = E → p.2 ∈ LB⌝ ∗
    logStateAt γb γfs cov ls n LB (opPending om) ξ

theorem lwBatch_elim (γ : LogNames) (γb : BcacheNames) (γfs : FsNames)
    (cov : Std.ExtTreeSet Nat compare) (ls : Nat) (om : RegMapF OpEntry) (E : Nat)
    (X : RegMapF (Nat × Nat)) (ξ : CtxId) :
    lwBatch (GF := GF) γ γb γfs cov ls om E X ξ ⊢
      ∃ (n : Nat) (LB : List Nat),
        ⌜n + opSum om ≤ LOGBLOCKS⌝ ∗
        ⌜∀ i e, PartialMap.get? om i = some e → ∀ x ∈ e.set, x ∈ LB⌝ ∗
        ⌜∀ i p, PartialMap.get? X i = some p → p.1 = E → p.2 ∈ LB⌝ ∗
        logStateAt γb γfs cov ls n LB (opPending om) ξ := by
  unfold lwBatch; iintro H; iexact H

theorem lwBatch_intro (γ : LogNames) (γb : BcacheNames) (γfs : FsNames)
    (cov : Std.ExtTreeSet Nat compare) (ls : Nat) (om : RegMapF OpEntry) (E : Nat)
    (X : RegMapF (Nat × Nat)) (ξ : CtxId) (n : Nat) (LB : List Nat) (pend : Nat → Prop)
    (h1 : n + opSum om ≤ LOGBLOCKS)
    (h2 : ∀ i e, PartialMap.get? om i = some e → ∀ x ∈ e.set, x ∈ LB)
    (h3 : ∀ i p, PartialMap.get? X i = some p → p.1 = E → p.2 ∈ LB) :
    logStateAt (GF := GF) γb γfs cov ls n LB pend ξ ⊢
      lwBatch γ γb γfs cov ls om E X ξ := by
  have hpend : logStateAt (GF := GF) γb γfs cov ls n LB (opPending om) ξ =
      logStateAt γb γfs cov ls n LB pend ξ := rfl
  unfold lwBatch
  iintro H
  iexists n, LB
  isplitr [H]
  · ipureintro; exact h1
  isplitr [H]
  · ipureintro; exact h2
  isplitr [H]
  · ipureintro; exact h3
  rw [← hpend]
  iexact H

/-- `Xv6.logResAt`, taken apart.  The `committing` cell and the batch are
handed out as the DISJUNCTION the code's `bnez` tests, so no branch of the
proof ever carries an `if`. -/
theorem lw_res_elim (γ : LogNames) (γb : BcacheNames) (γfs : FsNames)
    (cov : Std.ExtTreeSet Nat compare) (ls : Nat) (ξ : CtxId) :
    logResAt (GF := GF) γ γb γfs cov ls ξ ⊢
      ∃ (out : Nat) (nc : BitVec 32) (om : RegMapF OpEntry) (E : Nat)
        (X : RegMapF (Nat × Nat)) (T : RegMapF Unit) (nxo nxt nxl : Nat),
      wordAtN ξ lOut 4 (DFrac.own 1) (BitVec.ofNat 32 out) ∗
      wordAtN ξ lNcommit 4 (DFrac.own 1) nc ∗
      (γ.ops ↪●MAP om) ∗ logEpochAuth γ E ∗ logRegAuth γ X ∗ (γ.tx ↪●MAP T) ∗
      ⌜(FiniteMap.toList om).length = out⌝ ∗
      ⌜∀ i e, PartialMap.get? om i = some e → e.bud ≤ MAXOPBLOCKS⌝ ∗ ⌜out ≤ 3⌝ ∗
      ⌜∀ i, nxo ≤ i → PartialMap.get? om i = none⌝ ∗ ⌜1 ≤ E⌝ ∗
      ⌜∀ i, nxl ≤ i → PartialMap.get? X i = none⌝ ∗
      ⌜∀ i e, PartialMap.get? om i = some e → e.ep = E⌝ ∗
      ⌜∀ i p, PartialMap.get? X i = some p → p.1 ≤ E⌝ ∗
      ⌜∀ i, nxt ≤ i → PartialMap.get? T i = none⌝ ∗
      ⌜(FiniteMap.toList T).length = (FiniteMap.toList om).length⌝ ∗
      ((wordAtN ξ lCmt 4 (DFrac.own 1) (0#32 : BitVec 32) ∗
          lwBatch γ γb γfs cov ls om E X ξ) ∨
        (wordAtN ξ lCmt 4 (DFrac.own 1) (1#32 : BitVec 32) ∗ ⌜out = 0⌝)) := by
  unfold logResAt lwBatch
  iintro ⟨%out, %cmt, %nc, %om, %E, %X, %T, %nxo, %nxt, %nxl,
    Hout, Hcmt, Hnc, Hops, %hlen, %hp, %hfresho, Hep, %hE, Hreg, %hfreshl, %hlive, %hcap,
    Htx, %hfresht, %hTlen, Harm⟩
  obtain ⟨hbud, hout3, hcmt0⟩ := hp
  iexists out, nc, om, E, X, T, nxo, nxt, nxl
  iframe Hout Hnc Hops Hep Hreg Htx
  isplitr [Hcmt Harm]
  · ipureintro; exact hlen
  isplitr [Hcmt Harm]
  · ipureintro; exact hbud
  isplitr [Hcmt Harm]
  · ipureintro; exact hout3
  isplitr [Hcmt Harm]
  · ipureintro; exact hfresho
  isplitr [Hcmt Harm]
  · ipureintro; exact hE
  isplitr [Hcmt Harm]
  · ipureintro; exact hfreshl
  isplitr [Hcmt Harm]
  · ipureintro; exact hlive
  isplitr [Hcmt Harm]
  · ipureintro; exact hcap
  isplitr [Hcmt Harm]
  · ipureintro; exact hfresht
  isplitr [Hcmt Harm]
  · ipureintro; exact hTlen
  cases cmt
  · ileft
    isimp only [Bool.false_eq_true, if_false] at Hcmt
    isimp only [Bool.false_eq_true, if_false] at Harm
    iframe Hcmt Harm
  · iright
    isimp only [if_true] at Hcmt
    iframe Hcmt
    ipureintro
    exact hcmt0 rfl

/-- ...and put back together. -/
theorem lw_res_intro (γ : LogNames) (γb : BcacheNames) (γfs : FsNames)
    (cov : Std.ExtTreeSet Nat compare) (ls : Nat) (ξ : CtxId)
    (out : Nat) (cmt : Bool) (nc : BitVec 32) (om : RegMapF OpEntry) (E : Nat)
    (X : RegMapF (Nat × Nat)) (T : RegMapF Unit) (nxo nxt nxl : Nat)
    (hlen : (FiniteMap.toList om).length = out)
    (hp : (∀ i e, PartialMap.get? om i = some e → e.bud ≤ MAXOPBLOCKS) ∧ out ≤ 3 ∧
      (cmt = true → out = 0))
    (hfresho : ∀ i, nxo ≤ i → PartialMap.get? om i = none)
    (hE : 1 ≤ E)
    (hfreshl : ∀ i, nxl ≤ i → PartialMap.get? X i = none)
    (hlive : ∀ i e, PartialMap.get? om i = some e → e.ep = E)
    (hcap : ∀ i p, PartialMap.get? X i = some p → p.1 ≤ E)
    (hfresht : ∀ i, nxt ≤ i → PartialMap.get? T i = none)
    (hTlen : (FiniteMap.toList T).length = (FiniteMap.toList om).length) :
    wordAtN ξ lOut 4 (DFrac.own 1) (BitVec.ofNat 32 out) ∗
    wordAtN ξ lCmt 4 (DFrac.own 1) (if cmt then 1#32 else 0#32) ∗
    wordAtN ξ lNcommit 4 (DFrac.own 1) nc ∗
    (γ.ops ↪●MAP om) ∗ logEpochAuth γ E ∗ logRegAuth γ X ∗ (γ.tx ↪●MAP T) ∗
    (if cmt then iprop(emp) else lwBatch γ γb γfs cov ls om E X ξ)
    ⊢ logResAt (GF := GF) γ γb γfs cov ls ξ := by
  unfold logResAt lwBatch
  iintro ⟨Hout, Hcmt, Hnc, Hops, Hep, Hreg, Htx, Harm⟩
  iexists out, cmt, nc, om, E, X, T, nxo, nxt, nxl
  iframe Hout Hcmt Hnc Hops Hep Hreg Htx
  isplitr [Harm]
  · ipureintro; exact hlen
  isplitr [Harm]
  · ipureintro; exact hp
  isplitr [Harm]
  · ipureintro; exact hfresho
  isplitr [Harm]
  · ipureintro; exact hE
  isplitr [Harm]
  · ipureintro; exact hfreshl
  isplitr [Harm]
  · ipureintro; exact hlive
  isplitr [Harm]
  · ipureintro; exact hcap
  isplitr [Harm]
  · ipureintro; exact hfresht
  isplitr [Harm]
  · ipureintro; exact hTlen
  iexact Harm

/-- The `committing = 0` re-close. -/
theorem lw_res_intro_f (γ : LogNames) (γb : BcacheNames) (γfs : FsNames)
    (cov : Std.ExtTreeSet Nat compare) (ls : Nat) (ξ : CtxId)
    (out : Nat) (nc : BitVec 32) (om : RegMapF OpEntry) (E : Nat)
    (X : RegMapF (Nat × Nat)) (T : RegMapF Unit) (nxo nxt nxl : Nat)
    (hlen : (FiniteMap.toList om).length = out)
    (hbud : ∀ i e, PartialMap.get? om i = some e → e.bud ≤ MAXOPBLOCKS)
    (hout3 : out ≤ 3)
    (hfresho : ∀ i, nxo ≤ i → PartialMap.get? om i = none)
    (hE : 1 ≤ E)
    (hfreshl : ∀ i, nxl ≤ i → PartialMap.get? X i = none)
    (hlive : ∀ i e, PartialMap.get? om i = some e → e.ep = E)
    (hcap : ∀ i p, PartialMap.get? X i = some p → p.1 ≤ E)
    (hfresht : ∀ i, nxt ≤ i → PartialMap.get? T i = none)
    (hTlen : (FiniteMap.toList T).length = (FiniteMap.toList om).length) :
    wordAtN ξ lOut 4 (DFrac.own 1) (BitVec.ofNat 32 out) ∗
    wordAtN ξ lCmt 4 (DFrac.own 1) (0#32 : BitVec 32) ∗
    wordAtN ξ lNcommit 4 (DFrac.own 1) nc ∗
    (γ.ops ↪●MAP om) ∗ logEpochAuth γ E ∗ logRegAuth γ X ∗ (γ.tx ↪●MAP T) ∗
    lwBatch γ γb γfs cov ls om E X ξ
    ⊢ logResAt (GF := GF) γ γb γfs cov ls ξ :=
  lw_res_intro γ γb γfs cov ls ξ out false nc om E X T nxo nxt nxl hlen
    ⟨hbud, hout3, by simp⟩ hfresho hE hfreshl hlive hcap hfresht hTlen

/-- The `committing = 1` re-close (the batch is checked out by the
committer, so there is nothing to give back but the cells). -/
theorem lw_res_intro_t (γ : LogNames) (γb : BcacheNames) (γfs : FsNames)
    (cov : Std.ExtTreeSet Nat compare) (ls : Nat) (ξ : CtxId)
    (out : Nat) (nc : BitVec 32) (om : RegMapF OpEntry) (E : Nat)
    (X : RegMapF (Nat × Nat)) (T : RegMapF Unit) (nxo nxt nxl : Nat)
    (hlen : (FiniteMap.toList om).length = out)
    (hbud : ∀ i e, PartialMap.get? om i = some e → e.bud ≤ MAXOPBLOCKS)
    (hout3 : out ≤ 3) (hout0 : out = 0)
    (hfresho : ∀ i, nxo ≤ i → PartialMap.get? om i = none)
    (hE : 1 ≤ E)
    (hfreshl : ∀ i, nxl ≤ i → PartialMap.get? X i = none)
    (hlive : ∀ i e, PartialMap.get? om i = some e → e.ep = E)
    (hcap : ∀ i p, PartialMap.get? X i = some p → p.1 ≤ E)
    (hfresht : ∀ i, nxt ≤ i → PartialMap.get? T i = none)
    (hTlen : (FiniteMap.toList T).length = (FiniteMap.toList om).length) :
    wordAtN ξ lOut 4 (DFrac.own 1) (BitVec.ofNat 32 out) ∗
    wordAtN ξ lCmt 4 (DFrac.own 1) (1#32 : BitVec 32) ∗
    wordAtN ξ lNcommit 4 (DFrac.own 1) nc ∗
    (γ.ops ↪●MAP om) ∗ logEpochAuth γ E ∗ logRegAuth γ X ∗ (γ.tx ↪●MAP T)
    ⊢ logResAt (GF := GF) γ γb γfs cov ls ξ := by
  iintro ⟨Hout, Hcmt, Hnc, Hops, Hep, Hreg, Htx⟩
  iapply (lw_res_intro γ γb γfs cov ls ξ out true nc om E X T nxo nxt nxl hlen
    ⟨hbud, hout3, fun _ => hout0⟩ hfresho hE hfreshl hlive hcap hfresht hTlen)
  isimp only [if_true]
  iframe Hout Hcmt Hnc Hops Hep Hreg Htx



end

end Xv6
