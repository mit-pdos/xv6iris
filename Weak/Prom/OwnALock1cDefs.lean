/-
Weak/Prom: **G4 target (1c) on track (a): xv6's EXACT acquire/release text — definitions** (stage S4a part 3;
plan rev 7 §4 "Gate G4" (1c): acquire `amoswap.w.aq a5,a5,(s1); sext.w; bnez; …; sd a0,16(s1)` and release
`sd zero,16(s1); fence rw,w; sw zero,0(s1)`, Xv6/KernelImage.lean:2259–2280 (acquire+0x16..+0x28),
:2357–2364 (release+0x12..+0x1a); "This form is where 'release-class = pre-view ⊒ vrOld ⊔ vwOld' is actually
tested").

What changes from (1a)/(1b) (OwnALockDefs.lean; this file is a parallel copy in namespace `OA.C`, so the (1a)/(1b)
files are untouched):
* RELEASES ARE PLAIN STORES: a lock message (`lmP`) is 4 bytes at `Lk` by hart 0 or 1 of class `excl` (the AMO's
  write) OR `plain` (`sw zero,0(s1)`); `isA` / `isR` / junk as before.  The release `sw` is release-class through
  `fence rw,w` (plan §3: `fencePost` raises `vwNew` to `vrOld ⊔ vwOld`, and a plain store's pre-view `stPreA`
  contains `vwNew`).
* THE LOCK-PROTECTED `cpu` FIELD (`struct spinlock { uint locked; char *name; struct cpu *cpu; }`, offset 16):
  class `isP` (8 bytes at `Pc = Lk + 16`, plain, hart 0 or 1).  Its messages' `pend`s form a SECOND BAG in the lock
  resource: `Rs s` = the counter's points-to with latest write `≤ s` ∗ the `pend` of every cpu-field message
  above `s` (`pPts s`).  Nobody reads the field in (1c) (that is `holding()`, G4 (3)), so the bag has no
  latest-write fact: the holder's stores `sd a0,16(s1)` / `sd zero,16(s1)` take their `pend`s out of it.
* `isDd` (DEAD) = neither lock, counter nor cpu-field message.
The test runs the xv6 text with the mutual-exclusion client of (1a) (`ld; addi; sd` of a counter) as the critical
section; `mycpu()` (`jal mycpu`, a call) is not part of the text: its result `a0` is an initial register.
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Prom.OwnALock1b

namespace Weak.Prom.OA.C

open MachCSL MachCSL.Stdpp Iris.Std
open Weak (Image Dsrc)
open Weak.Prom Weak.Prom.PF Weak.Prom.Mach Weak.Prom.Mach.Cert
open Weak.Prom.Ref (Instr Test two64)
open Weak.Prom.Ref.Lit (X Y)
open PLabel
open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode

/-! ## 1. The text, the test -/

/-- The cpu field `lk->cpu` (offset 16 of `struct spinlock`). -/
abbrev Pc : Int := Lk + 16

/-- **(1c) xv6's acquire/release text** (Xv6/KernelImage.lean: acquire+0x16 `li a4,1`, +0x1a `mv a5,a4`
(`c.mv` = `add a5,x0,a4`), +0x1c `amoswap.w.aq a5,a5,(s1)`, +0x20 `sext.w a5,a5` (`c.addiw a5,0`), +0x22
`bnez a5,acquire+0x1a`, +0x28 `sd a0,16(s1)`; release+0x12 `sd zero,16(s1)`, +0x16 `fence rw,w`, +0x1a
`sw zero,0(s1)`), with (1a)'s critical section `ld t2,(a1); addi t2,t2,1; sd t2,(a1)`; `s1 = x9 = Lk`,
`a0 = x10` (`mycpu()`), `a1 = x11 = Ct`, `a4 = x14`, `a5 = x15`, `t2 = x7`:
`0: li a4,1  1: mv a5,a4  2: amoswap.w.aq a5,a5,(s1)  3: sext.w a5,a5  4: bnez a5,1  5: sd a0,16(s1)
 6: ld t2,(a1)  7: addi t2,t2,1  8: sd t2,(a1)  9: sd zero,16(s1)  10: fence rw,w  11: sw zero,0(s1)`. -/
def p1c : List XI :=
  [.i (Weak.Prom.Ref.Lit.li 14 1), .i (.alu .add 15 0 14), .i (Weak.Prom.Ref.Lit.amoswapW true false 15 15 9),
   .addiw 15 15 0, .i (.br .ne 15 0 1), .i (Weak.Prom.Ref.Lit.sd 10 9 16),
   .i (Weak.Prom.Ref.Lit.ld 7 11), .i (Weak.Prom.Ref.Lit.addi 7 7 1), .i (Weak.Prom.Ref.Lit.sd 7 11),
   .i (Weak.Prom.Ref.Lit.sd 0 9 16), .i Weak.Prom.Ref.Lit.fRWW, .i (Weak.Prom.Ref.Lit.sw 0 9 0)]

abbrev b1c : List Instr := p1c.map XI.base

/-- The test: two harts run `p1c`; `a0` (`mycpu()`) differs per hart; image all zero. -/
def t1c : Test :=
  { harts := [b1c, b1c]
    regs0 := [[(9, X), (10, 0x3000), (11, Y)], [(9, X), (10, 0x3100), (11, Y)]]
    img := []
    cond := Weak.Prom.Ref.Lit.mpFF.cond }

abbrev xs1c : List (List XI) := [p1c]

theorem xOf_1c : xOf xs1c b1c = some p1c := by decide

theorem p1c_at {s : LP} (h : s.prog = b1c) : xOf xs1c s.prog = some p1c := by rw [h]; exact xOf_1c

/-- Hart `h`'s world (the image is the all-zero `imgL`). -/
abbrev wL1c (M : List PMsg) (h : Nat) : HW LP Unit Unit := xW xs1c imgL M h

/-! ## 2. Message classes -/

/-- A lock message's shape: an AMO's write (`excl`) or a plain store (`plain`, the release `sw`). -/
def lmP (m : PMsg) : Prop :=
  m.pa = Lk ∧ m.data.length = 4 ∧ (m.cls = .excl ∨ m.cls = .plain) ∧ (m.tid = some 0 ∨ m.tid = some 1)

/-- A cpu-field message's shape. -/
def pmP (m : PMsg) : Prop := m.pa = Pc ∧ m.data.length = 8 ∧ m.cls = .plain ∧ (m.tid = some 0 ∨ m.tid = some 1)

instance : DecidablePred lmP := fun m => by unfold lmP; infer_instance
instance : DecidablePred pmP := fun m => by unfold pmP; infer_instance

def isL (M : List PMsg) (t : Nat) : Bool := clsB lmP M t
def isA (M : List PMsg) (t : Nat) : Bool := clsB (fun m => lmP m ∧ m.data = toBytes 1 4) M t
def isR (M : List PMsg) (t : Nat) : Bool := clsB (fun m => lmP m ∧ m.data = toBytes 0 4) M t
def isP (M : List PMsg) (t : Nat) : Bool := clsB pmP M t
def isDd (M : List PMsg) (t : Nat) : Bool := !isL M t && !isC M t && !isP M t
/-- Junk or dead: its `pend` goes to a `deadInv`. -/
def isJ (M : List PMsg) (t : Nat) : Bool := (isL M t && !isA M t && !isR M t) || isDd M t

theorem isA_L {M : List PMsg} {t : Nat} (h : isA M t = true) : isL M t = true := by
  obtain ⟨m, hm, hp, _⟩ := clsB_iff.1 h
  exact clsB_iff.2 ⟨m, hm, hp⟩

theorem isR_L {M : List PMsg} {t : Nat} (h : isR M t = true) : isL M t = true := by
  obtain ⟨m, hm, hp, _⟩ := clsB_iff.1 h
  exact clsB_iff.2 ⟨m, hm, hp⟩

theorem isA_R {M : List PMsg} {t : Nat} (h : isA M t = true) : isR M t = false := by
  obtain ⟨m, hm, _, hd⟩ := clsB_iff.1 h
  rw [isR, clsB_of hm]
  simp only [decide_eq_false_iff_not]
  rintro ⟨_, hd'⟩
  rw [hd] at hd'; exact absurd hd' (by decide)

theorem isC_L {M : List PMsg} {t : Nat} (h : isC M t = true) : isL M t = false := by
  obtain ⟨m, hm, hp⟩ := clsB_iff.1 h
  rw [isL, clsB_of hm]
  simp only [decide_eq_false_iff_not]
  intro hl
  have := hl.1.symm.trans hp.1
  simp [Lk, Ct, X, Y] at this

theorem isP_L {M : List PMsg} {t : Nat} (h : isP M t = true) : isL M t = false := by
  obtain ⟨m, hm, hp⟩ := clsB_iff.1 h
  rw [isL, clsB_of hm]
  simp only [decide_eq_false_iff_not]
  intro hl
  have := hl.1.symm.trans hp.1
  simp [Pc, Lk, X] at this

theorem isP_C {M : List PMsg} {t : Nat} (h : isP M t = true) : isC M t = false := by
  obtain ⟨m, hm, hp⟩ := clsB_iff.1 h
  rw [isC, clsB_of hm]
  simp only [decide_eq_false_iff_not]
  intro hl
  have := hl.1.symm.trans hp.1
  simp [Pc, Lk, Ct, X, Y] at this

/-- A lock message writes bytes `Lk .. Lk+3`. -/
theorem isL_byte {M : List PMsg} {t : Nat} {j : Nat} (hj : j < 4) (h : isL M t = true) :
    ∃ m, msgAt M t = some m ∧ (m.byteAt (Lk + j)).isSome = true := by
  obtain ⟨m, hm, h1, h2, _⟩ := clsB_iff.1 h
  refine ⟨m, hm, ?_⟩
  rw [← h1, byteAt_off rfl, List.getElem?_eq_getElem (by omega)]; rfl

/-- A lock message does not touch the counter. -/
theorem isL_noC {M : List PMsg} {t : Nat} {m : PMsg} (hm : msgAt M t = some m) (h : isL M t = true) (j : Nat)
    (hj : j < 8) : m.byteAt (Ct + j) = none := by
  rw [isL, clsB_of hm] at h
  have hp := of_decide_eq_true h
  unfold PMsg.byteAt
  rw [hp.1]
  split
  · apply List.getElem?_eq_none; rw [hp.2.1]; simp only [Lk, Ct, X, Y]; omega
  · rfl

/-- A cpu-field message does not touch the lock word. -/
theorem isP_noL {M : List PMsg} {t : Nat} {m : PMsg} (hm : msgAt M t = some m) (h : isP M t = true) (j : Nat)
    (hj : j < 4) : m.byteAt (Lk + j) = none := by
  rw [isP, clsB_of hm] at h
  have hp := of_decide_eq_true h
  unfold PMsg.byteAt
  rw [hp.1, if_neg (by simp only [Pc, Lk, X]; omega)]

/-- A cpu-field message does not touch the counter. -/
theorem isP_noC {M : List PMsg} {t : Nat} {m : PMsg} (hm : msgAt M t = some m) (h : isP M t = true) (j : Nat)
    (hj : j < 8) : m.byteAt (Ct + j) = none := by
  rw [isP, clsB_of hm] at h
  have hp := of_decide_eq_true h
  unfold PMsg.byteAt
  rw [hp.1]
  split
  · apply List.getElem?_eq_none; rw [hp.2.1]; simp only [Pc, Lk, Ct, X, Y]; omega
  · rfl

theorem isA_byte {M : List PMsg} {t j : Nat} {m : PMsg} (hm : msgAt M t = some m) (h : isA M t = true) (hj : j < 4) :
    m.byteAt (Lk + j) = (toBytes 1 4)[j]? := by
  obtain ⟨m', hm', ⟨h1, _⟩, hd⟩ := clsB_iff.1 h
  rw [hm] at hm'; cases hm'
  rw [← h1, byteAt_off rfl, hd]

theorem isR_byte {M : List PMsg} {t j : Nat} {m : PMsg} (hm : msgAt M t = some m) (h : isR M t = true) (hj : j < 4) :
    m.byteAt (Lk + j) = (toBytes 0 4)[j]? := by
  obtain ⟨m', hm', ⟨h1, _⟩, hd⟩ := clsB_iff.1 h
  rw [hm] at hm'; cases hm'
  rw [← h1, byteAt_off rfl, hd]

/-- Every message is an acquire, a release, a counter, a cpu-field, or a junk/dead message. -/
theorem cls_cases (M : List PMsg) (t : Nat) :
    isA M t = true ∨ isR M t = true ∨ isC M t = true ∨ isP M t = true ∨ isJ M t = true := by
  unfold isJ isDd
  cases hA : isA M t <;> cases hR : isR M t <;> cases hC : isC M t <;> cases hL : isL M t <;>
    cases hP : isP M t <;> simp

/-- A lock-touching message (`wrB` at `Lk + j`) is a lock message or junk/dead. -/
theorem wrL_cls {M : List PMsg} {t j : Nat} (hj : j < 4) (h : wrB M (Lk + j) t) :
    isA M t = true ∨ isR M t = true ∨ isJ M t = true := by
  rcases cls_cases M t with h1 | h1 | h1 | h1 | h1
  · exact .inl h1
  · exact .inr (.inl h1)
  · obtain ⟨m, hm, hb⟩ := h
    rw [isC_noL hm h1 j hj] at hb; cases hb
  · obtain ⟨m, hm, hb⟩ := h
    rw [isP_noL hm h1 j hj] at hb; cases hb
  · exact .inr (.inr h1)

theorem isR_A {M : List PMsg} {t : Nat} (hR : isR M t = true) : isA M t = false := by
  cases h : isA M t
  · rfl
  · rw [isA_R h] at hR; cases hR

theorem isC_A {M : List PMsg} {t : Nat} (hC : isC M t = true) : isA M t = false ∧ isR M t = false := by
  have hL := isC_L hC
  refine ⟨?_, ?_⟩
  · cases h : isA M t
    · rfl
    · rw [isA_L h] at hL; cases hL
  · cases h : isR M t
    · rfl
    · rw [isR_L h] at hL; cases hL

theorem isP_A {M : List PMsg} {t : Nat} (hP : isP M t = true) :
    isA M t = false ∧ isR M t = false ∧ isC M t = false := by
  have hL := isP_L hP
  refine ⟨?_, ?_, isP_C hP⟩
  · cases h : isA M t
    · rfl
    · rw [isA_L h] at hL; cases hL
  · cases h : isR M t
    · rfl
    · rw [isR_L h] at hL; cases hL

/-! ## 3. The text's messages -/

theorem msgAt_of {M : List PMsg} {ts : Nat} {m : PMsg} (h1 : 1 ≤ ts) (hm : M[ts - 1]? = some m) :
    msgAt M ts = some m := by
  obtain ⟨k, rfl⟩ : ∃ k, ts = k + 1 := ⟨ts - 1, by omega⟩
  simpa [msgAt] using hm

/-- The release `sw zero,0(s1)` writes a release message. -/
theorem isR_of_msg {M : List PMsg} {ts h : Nat} (hh : h < 2) (h1 : 1 ≤ ts)
    (hm : M[ts - 1]? = some ⟨Lk, toBytes 0 4, some h, .plain⟩) : isR M ts = true ∧ byH M h ts = true := by
  have hmt := msgAt_of h1 hm
  refine ⟨?_, ?_⟩
  · rw [isR, clsB_of hmt]
    exact decide_eq_true ⟨⟨rfl, toBytes_length 0 4, .inr rfl, by simp only [Option.some.injEq]; omega⟩, rfl⟩
  · simp [byH, tidAt, hmt]

/-- The acquiring AMO writes an acquire message. -/
theorem isA_of_msg {M : List PMsg} {ts h : Nat} (hh : h < 2) (h1 : 1 ≤ ts)
    (hm : M[ts - 1]? = some ⟨Lk, toBytes 1 4, some h, .excl⟩) : isA M ts = true ∧ byH M h ts = true := by
  have hmt := msgAt_of h1 hm
  refine ⟨?_, ?_⟩
  · rw [isA, clsB_of hmt]
    exact decide_eq_true ⟨⟨rfl, toBytes_length 1 4, .inl rfl, by simp only [Option.some.injEq]; omega⟩, rfl⟩
  · simp [byH, tidAt, hmt]

/-- A cpu-field store writes a cpu-field message. -/
theorem isP_of_msg {M : List PMsg} {ts h : Nat} {d : List (BitVec 8)} (hh : h < 2) (hd : d.length = 8)
    (h1 : 1 ≤ ts) (hm : M[ts - 1]? = some ⟨Pc, d, some h, .plain⟩) : isP M ts = true := by
  have hmt := msgAt_of h1 hm
  rw [isP, clsB_of hmt]; simp only [decide_eq_true_eq]
  refine ⟨rfl, hd, rfl, ?_⟩
  simp only [Option.some.injEq]; omega

/-- The dead predicate of (1c) (timestamp `0` is the image, never a witness). -/
def ddL (M : List PMsg) (t : Nat) : Prop := 1 ≤ t ∧ isDd M t = true

/-- A lock message written by the text is not dead. -/
theorem lm_notDd {M : List PMsg} {ts h : Nat} {d : List (BitVec 8)} {c : PClass} (hh : h < 2) (hd : d.length = 4)
    (hc : c = .excl ∨ c = .plain) (hm : M[ts - 1]? = some ⟨Lk, d, some h, c⟩) : ¬ ddL M ts := by
  rintro ⟨h1, hD⟩
  have hmt := msgAt_of h1 hm
  have : isL M ts = true := by
    rw [isL, clsB_of hmt]; simp only [decide_eq_true_eq]
    refine ⟨rfl, hd, hc, ?_⟩
    simp only [Option.some.injEq]; omega
  simp [isDd, this] at hD

/-- A counter message written by the text is not dead. -/
theorem cm_notDd {M : List PMsg} {ts h : Nat} {d : List (BitVec 8)} (hh : h < 2) (hd : d.length = 8)
    (hm : M[ts - 1]? = some ⟨Ct, d, some h, .plain⟩) : ¬ ddL M ts := by
  rintro ⟨h1, hD⟩
  have := isC_of_msg hh hd h1 hm
  simp [isDd, this] at hD

/-- A cpu-field message written by the text is not dead. -/
theorem pm_notDd {M : List PMsg} {ts h : Nat} {d : List (BitVec 8)} (hh : h < 2) (hd : d.length = 8)
    (hm : M[ts - 1]? = some ⟨Pc, d, some h, .plain⟩) : ¬ ddL M ts := by
  rintro ⟨h1, hD⟩
  have := isP_of_msg hh hd h1 hm
  simp [isDd, this] at hD

/-- A cmo message is dead. -/
theorem cmo_dead {M : List PMsg} {ti : Nat} {a : Int} (h1 : 1 ≤ ti) (h : cmoAt M isInvalK ti a) :
    isJ M ti = true ∧ isDd M ti = true ∧ ti ≤ M.length := by
  obtain ⟨m, k, len, hm, hc, _⟩ := h
  have hmt := msgAt_of h1 hm
  have hL : isL M ti = false := by
    rw [isL, clsB_of hmt]; simp only [decide_eq_false_iff_not]; intro h
    rcases h.2.2.1 with h' | h' <;> rw [h'] at hc <;> cases hc
  have hC : isC M ti = false := by
    rw [isC, clsB_of hmt]; simp only [decide_eq_false_iff_not]; intro h; rw [h.2.2.1] at hc; cases hc
  have hP : isP M ti = false := by
    rw [isP, clsB_of hmt]; simp only [decide_eq_false_iff_not]; intro h; rw [h.2.2.1] at hc; cases hc
  refine ⟨by simp [isJ, isDd, hL, hC, hP], by simp [isDd, hL, hC, hP], (msgAt_le hmt).2⟩

/-! ## 4. Bags -/

/-- Hart `h`'s acquire messages above `lo`, except `ex`. -/
def bagA (M : List PMsg) (h lo ex : Nat) : List Nat :=
  (rng M).filter (fun t => decide (lo < t) && decide (t ≠ ex) && isA M t && byH M h t)

/-- Hart `h`'s lock messages (acquire or release) above `lo`, except `ex`. -/
def bagL (M : List PMsg) (h lo ex : Nat) : List Nat :=
  (rng M).filter (fun t => decide (lo < t) && decide (t ≠ ex) && (isA M t || isR M t) && byH M h t)

/-- The cpu field's bag above `s`. -/
def pBag (M : List PMsg) (s : Nat) : List Nat := (rng M).filter (fun t => decide (s < t) && isP M t)

/-! ## 5. Resources -/

section res

variable {GF : BundledGFunctors} [GhostVarG GF HSt] [GhostVarG GF Bool] [TokenG GF] [InvGS GF]

/-- THE CPU FIELD'S BAG above `s`: the `pend` of every cpu-field message above `s`. -/
def pPts (g : AGN) (M : List PMsg) (s : Nat) : IProp GF := iprop([∗list] t ∈ pBag M s, pend g t)

/-- The lock's resource deposited at `s`: the counter's points-to with latest write `≤ s`, and the cpu field's bag
above `s`. -/
def Rs (g : AGN) (M : List PMsg) (s : Nat) : IProp GF := iprop((∃ lw, ⌜lw ≤ s⌝ ∗ cPts g M lw) ∗ pPts g M s)

def lkN : Namespace := ndot nroot "promLockC"

/-- THE IMAGE'S SLOT: the lock is born unlocked with `Rs 0`. -/
def iSlot (g : AGN) (M : List PMsg) (tk : Nat → GName) : IProp GF :=
  inv (ndot lkN 0) iprop(Rs g M 0 ∨ nxtTok M tk 0)

/-- RELEASE `r`'S SLOT (plan §3 "The deposit"). -/
def rSlot (g : AGN) (M : List PMsg) (tk : Nat → GName) (r : Nat) : IProp GF :=
  inv (ndot lkN r) iprop(pend g r ∨ (shot g r ∗ token (tk r) ∗ (Rs g M r ∨ nxtTok M tk r)))

/-- THE PROTOCOL'S PERSISTENT PART. -/
def lkCtx (g : AGN) (M : List PMsg) (tk : Nat → GName) : IProp GF :=
  iprop(doomInv g M ∗ iSlot g M tk ∗ ([∗list] r ∈ (rng M).filter (isR M), rSlot g M tk r) ∗
    ([∗list] d ∈ (rng M).filter (isJ M), deadInv g d))

/-- THE OWN-MESSAGE BAG of hart `h` above `lo` (except `ex`). -/
def obag (g : AGN) (M : List PMsg) (tk : Nat → GName) (h lo ex : Nat) : IProp GF :=
  iprop(([∗list] t ∈ bagA M h lo ex, pend g t) ∗ [∗list] t ∈ bagL M h lo ex, token (tk t))

instance (g : AGN) (M : List PMsg) (tk : Nat → GName) : Persistent (iSlot (GF := GF) g M tk) := by
  unfold iSlot; infer_instance
instance (g : AGN) (M : List PMsg) (tk : Nat → GName) (r : Nat) : Persistent (rSlot (GF := GF) g M tk r) := by
  unfold rSlot; infer_instance
instance (g : AGN) (M : List PMsg) (tk : Nat → GName) : Persistent (lkCtx (GF := GF) g M tk) := by
  unfold lkCtx; infer_instance

instance (g : AGN) (M : List PMsg) (s : Nat) : Timeless (pPts (GF := GF) g M s) := by
  unfold pPts; exact BigSepL.bigSepL_timeless (fun _ => inferInstance)

instance (g : AGN) (M : List PMsg) (s : Nat) : Timeless (Rs (GF := GF) g M s) := by unfold Rs; infer_instance

/-- The cpu field's bag shrinks to a higher floor. -/
theorem pPts_mono (g : AGN) (M : List PMsg) {s s' : Nat} (h : s ≤ s') : pPts (GF := GF) g M s ⊢ pPts g M s' := by
  unfold pPts pBag
  exact bsl_filter_mono (pend g) _ _ (fun t ht => by
    simp only [Bool.and_eq_true, decide_eq_true_eq] at ht ⊢; exact ⟨by omega, ht.2⟩) (rng M)

end res

end Weak.Prom.OA.C
