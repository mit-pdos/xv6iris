/-
Weak/Prom: **G4 target (4) on track (a): a lock BORN BY PLAIN STORES over junk and PUBLISHED THROUGH ANOTHER LOCK
— definitions** (stage S4a part 4; plan rev 7 §4 "Gate G4" (4): "A lock initialised by plain stores (`sw zero` over
junk) and published through another lock: the pipealloc shape … The deposited resource must name ghost state
allocated after adequacy start: the lock's `isLock γ lk s R` with γ from a runtime `initlock`, as in `pipealloc`.
This is what tests the saved-proposition slots σ_t"; §3 "Lock birth and deferred deposits", "The rev-4 design:
per-t one-shot saved propositions", R-a4, R-a5).

THE TEST (xv6 `pipealloc` shape, Xv6/SpecPipealloc.lean: `kalloc` junk, `initlock(&pi->lock)`, field init,
publication; the text of acquire/release is xv6's, Xv6/KernelImage.lean acquire+0x1a..+0x22, release+0x16..+0x1a):
* LOCK `L1` (4 bytes at `Z`) is a boot lock, born HELD by hart 0 (image word 1);
* LOCK `L2` (4 bytes at `Lk = X`) protects the field `C` (8 bytes at `Ct = Y`);
* hart 0 (`p4o`): `li t1,J; sw t1,0(s1)` (`kfree`'s junk `memset(1)` in the lock word); `sd t1,0(a1)` (junk in the
  field); `sw zero,0(s1)` (INITLOCK: L2 is BORN by a plain store — the message `b`); `li t2,5; sd t2,0(a1)` (field
  init: the message `c`); `fence rw,w; sw zero,0(a2)` (RELEASE L1: the message `r1`, release-class);
* hart 1 (`p4h`): xv6's acquire spin loop on L1 (`mv; amoswap.w.aq; sext.w; bnez`), then on L2, the critical section
  `ld t2,(a1); addi; sd`, and xv6's release of L2 (`fence rw,w; sw zero`).
THE OWNERSHIP STORY (plan §3):
* L2's birth `b` is a PLAIN store: its deposit is DEFERRED to hart 0's next release-class write `r1` (plan: "A plain
  write t by hart h deposits at the fulfil of h's next release-class write r(t)").  Its slot is a pre-allocated
  SAVED-PROPOSITION slot `bSlot t` (one per birth-class `t`, plan R-a5): `dpendD t` (not yet deposited) or the
  persistent `dshotD t` with `saved_prop_own (σ t) □ P` and `P` or the claim token.  The depositor holds the full
  saved proposition `σ t ↦ True` and picks `P := C's points-to ∗ token γ` AT THE DEPOSIT, where `γ` is allocated AT
  RUNTIME by hart 0's `initlock` step (plan: "the deposit chooses R_t then, so R_t may name any ghost state that
  exists at the deposit").
* The L2 HANDLE `isLockA sv γ Lk R` (criterion (ii): `isLock γ lk s R`'s shape, `R` and `lk` parameters, `γ` from a
  runtime initlock) is published through L1: L1's release slot holds `Pub1 s` = "some `γ b c` with `b, c < s`, the
  handle `isLockAt … b`, and the pends of hart 0's later L2 words" — fixed at adequacy start, the runtime names
  are existential.
* R-a4 (junk in the lock word): the acquirer's L2 read lies above `b` (its view is above the L1 release `> b`, so
  coherence excludes the junk `j < b` and the image); messages above `b` are hart 0's (whose `pend`s the handle
  hands over), hart 1's own, or dead.
Message classes (`kind`, fixed by content, plan §3 "pre-allocated"): 1 field (`cmP`), 2 hart 1's L1 AMO writes,
3 hart 0's L1 releases, 4 hart 1's L2 AMO writes, 5 hart 1's L2 releases, 6 hart 0's L2 words (junk or birth),
0 DEAD.
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Prom.OwnALock1c
import Iris.Instances.Lib.SavedProp

namespace Weak.Prom.OA.P

open MachCSL MachCSL.Stdpp Iris.Std
open Weak (Image Dsrc)
open Weak.Prom Weak.Prom.PF Weak.Prom.Mach Weak.Prom.Mach.Cert
open Weak.Prom.Ref (Instr Test two64)
open Weak.Prom.Ref.Lit (X Y Z)
open PLabel
open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode

/-! ## 1. The addresses, the texts, the test -/

/-- The boot lock `L1`'s word. -/
abbrev L1 : Int := (Z : Int)

/-- `kfree`'s junk word (`memset(pa, 1, PGSIZE)`). -/
def J : Nat := 0x01010101

/-- **Hart 0** (pipealloc): `s1 = x9 = L2`, `a1 = x11 = C`, `a2 = x12 = L1`, `t1 = x6`, `t2 = x7`:
`0: li t1,J  1: sw t1,0(s1)  2: sd t1,0(a1)  3: sw zero,0(s1)  4: li t2,5  5: sd t2,0(a1)  6: fence rw,w
 7: sw zero,0(a2)`. -/
def p4o : List XI :=
  [.i (Weak.Prom.Ref.Lit.li 6 J), .i (Weak.Prom.Ref.Lit.sw 6 9), .i (Weak.Prom.Ref.Lit.sd 6 11),
   .i (Weak.Prom.Ref.Lit.sw 0 9), .i (Weak.Prom.Ref.Lit.li 7 5), .i (Weak.Prom.Ref.Lit.sd 7 11),
   .i Weak.Prom.Ref.Lit.fRWW, .i (Weak.Prom.Ref.Lit.sw 0 12)]

/-- **Hart 1**: xv6's acquire on L1 then on L2, the critical section, xv6's release of L2 (`a4 = x14`, `a5 = x15`):
`0: li a4,1  1: mv a5,a4  2: amoswap.w.aq a5,a5,(a2)  3: sext.w a5,a5  4: bnez a5,1  5: mv a5,a4
 6: amoswap.w.aq a5,a5,(s1)  7: sext.w a5,a5  8: bnez a5,5  9: ld t2,(a1)  10: addi t2,t2,1  11: sd t2,(a1)
 12: fence rw,w  13: sw zero,0(s1)`. -/
def p4h : List XI :=
  [.i (Weak.Prom.Ref.Lit.li 14 1), .i (.alu .add 15 0 14), .i (Weak.Prom.Ref.Lit.amoswapW true false 15 15 12),
   .addiw 15 15 0, .i (.br .ne 15 0 1), .i (.alu .add 15 0 14),
   .i (Weak.Prom.Ref.Lit.amoswapW true false 15 15 9), .addiw 15 15 0, .i (.br .ne 15 0 5),
   .i (Weak.Prom.Ref.Lit.ld 7 11), .i (Weak.Prom.Ref.Lit.addi 7 7 1), .i (Weak.Prom.Ref.Lit.sd 7 11),
   .i Weak.Prom.Ref.Lit.fRWW, .i (Weak.Prom.Ref.Lit.sw 0 9)]

abbrev b4o : List Instr := p4o.map XI.base
abbrev b4h : List Instr := p4h.map XI.base

/-- The test: L1 born held (image word 1 at `Z`), everything else 0. -/
def t4 : Test :=
  { harts := [b4o, b4h]
    regs0 := [[(9, X), (11, Y), (12, Z)], [(9, X), (11, Y), (12, Z)]]
    img := [(Z, 1)]
    cond := Weak.Prom.Ref.Lit.mpFF.cond }

abbrev xs4 : List (List XI) := [p4o, p4h]

theorem xOf_4o : xOf xs4 b4o = some p4o := by decide
theorem xOf_4h : xOf xs4 b4h = some p4h := by decide

theorem p4o_at {s : LP} (h : s.prog = b4o) : xOf xs4 s.prog = some p4o := by rw [h]; exact xOf_4o
theorem p4h_at {s : LP} (h : s.prog = b4h) : xOf xs4 s.prog = some p4h := by rw [h]; exact xOf_4h

abbrev img4 : Image := testImg t4

/-- Hart `h`'s world. -/
abbrev w4 (M : List PMsg) (h : Nat) : HW LP Unit Unit := xW xs4 img4 M h

theorem img4_L1 (j : Nat) (hj : j < 4) : img4 (L1 + j) = (toBytes 1 4)[j]? := by
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl <;>
    simp [img4, testImg, Test.imgF, t4, bv8, L1, Z] <;> decide

/-! ## 2. Message classes -/

def a1P (m : PMsg) : Prop := m.pa = L1 ∧ m.data = toBytes 1 4 ∧ m.cls = .excl ∧ m.tid = some 1
def r1P (m : PMsg) : Prop := m.pa = L1 ∧ m.data = toBytes 0 4 ∧ m.cls = .plain ∧ m.tid = some 0
def a2P (m : PMsg) : Prop := m.pa = Lk ∧ m.data = toBytes 1 4 ∧ m.cls = .excl ∧ m.tid = some 1
def r2P (m : PMsg) : Prop := m.pa = Lk ∧ m.data = toBytes 0 4 ∧ m.cls = .plain ∧ m.tid = some 1
def z0P (m : PMsg) : Prop := m.pa = Lk ∧ m.data.length = 4 ∧ m.cls = .plain ∧ m.tid = some 0

instance : DecidablePred a1P := fun m => by unfold a1P; infer_instance
instance : DecidablePred r1P := fun m => by unfold r1P; infer_instance
instance : DecidablePred a2P := fun m => by unfold a2P; infer_instance
instance : DecidablePred r2P := fun m => by unfold r2P; infer_instance
instance : DecidablePred z0P := fun m => by unfold z0P; infer_instance

/-- THE CLASS of a message (0 = dead). -/
def kind (m : PMsg) : Nat :=
  if cmP m then 1 else if a1P m then 2 else if r1P m then 3 else if a2P m then 4 else if r2P m then 5
  else if z0P m then 6 else 0

/-- The class of the message at `t` (0 when there is none). -/
def knd (M : List PMsg) (t : Nat) : Nat :=
  match msgAt M t with
  | some m => kind m
  | none => 0

def isK (M : List PMsg) (k t : Nat) : Bool := decide (knd M t = k)

/-- BIRTH CLASS: hart 0's L2 words with data 0 (the `initlock` store `sw zero`). -/
def bth (M : List PMsg) (t : Nat) : Bool :=
  match msgAt M t with
  | some m => decide (kind m = 6 ∧ m.data = toBytes 0 4)
  | none => false

theorem knd_of {M : List PMsg} {t : Nat} {m : PMsg} (h : msgAt M t = some m) : knd M t = kind m := by
  unfold knd; rw [h]

theorem kind_1 {m : PMsg} (h : kind m = 1) : cmP m := by
  unfold kind at h; split at h
  · assumption
  · repeat (first | (split at h <;> try omega) | omega)

theorem kind_ne1 {m : PMsg} (h : kind m ≠ 1) : ¬ cmP m := fun hc => h (by unfold kind; rw [if_pos hc])

theorem kind_2 {m : PMsg} (h : kind m = 2) : a1P m := by
  unfold kind at h
  by_cases h1 : cmP m
  · rw [if_pos h1] at h; cases h
  rw [if_neg h1] at h
  by_cases h2 : a1P m
  · exact h2
  rw [if_neg h2] at h
  repeat (first | (split at h <;> try omega) | omega)

theorem kind_3 {m : PMsg} (h : kind m = 3) : r1P m := by
  unfold kind at h
  by_cases h1 : cmP m
  · rw [if_pos h1] at h; cases h
  rw [if_neg h1] at h
  by_cases h2 : a1P m
  · rw [if_pos h2] at h; cases h
  rw [if_neg h2] at h
  by_cases h3 : r1P m
  · exact h3
  rw [if_neg h3] at h
  repeat (first | (split at h <;> try omega) | omega)

theorem kind_4 {m : PMsg} (h : kind m = 4) : a2P m := by
  unfold kind at h
  by_cases h1 : cmP m
  · rw [if_pos h1] at h; cases h
  rw [if_neg h1] at h
  by_cases h2 : a1P m
  · rw [if_pos h2] at h; cases h
  rw [if_neg h2] at h
  by_cases h3 : r1P m
  · rw [if_pos h3] at h; cases h
  rw [if_neg h3] at h
  by_cases h4 : a2P m
  · exact h4
  rw [if_neg h4] at h
  repeat (first | (split at h <;> try omega) | omega)

theorem kind_5 {m : PMsg} (h : kind m = 5) : r2P m := by
  unfold kind at h
  by_cases h1 : cmP m
  · rw [if_pos h1] at h; cases h
  rw [if_neg h1] at h
  by_cases h2 : a1P m
  · rw [if_pos h2] at h; cases h
  rw [if_neg h2] at h
  by_cases h3 : r1P m
  · rw [if_pos h3] at h; cases h
  rw [if_neg h3] at h
  by_cases h4 : a2P m
  · rw [if_pos h4] at h; cases h
  rw [if_neg h4] at h
  by_cases h5 : r2P m
  · exact h5
  rw [if_neg h5] at h
  split at h
  · cases h
  · cases h

theorem kind_6 {m : PMsg} (h : kind m = 6) : z0P m := by
  unfold kind at h
  by_cases h1 : cmP m
  · rw [if_pos h1] at h; cases h
  rw [if_neg h1] at h
  by_cases h2 : a1P m
  · rw [if_pos h2] at h; cases h
  rw [if_neg h2] at h
  by_cases h3 : r1P m
  · rw [if_pos h3] at h; cases h
  rw [if_neg h3] at h
  by_cases h4 : a2P m
  · rw [if_pos h4] at h; cases h
  rw [if_neg h4] at h
  by_cases h5 : r2P m
  · rw [if_pos h5] at h; cases h
  rw [if_neg h5] at h
  by_cases h6 : z0P m
  · exact h6
  rw [if_neg h6] at h; cases h

/-- A byte outside `[p, p + n)` of a message with base `p` and `n` bytes is not written. -/
theorem byteAt_out {m : PMsg} {a : Int} (h : a < m.pa ∨ m.pa + m.data.length ≤ a) : m.byteAt a = none := by
  unfold PMsg.byteAt
  split
  · apply List.getElem?_eq_none; omega
  · rfl

/-- A message writing an L1 byte is of class 2, 3 or dead. -/
theorem kind_L1 {m : PMsg} {j : Nat} (hj : j < 4) (hb : (m.byteAt (L1 + j)).isSome = true) :
    kind m = 2 ∨ kind m = 3 ∨ kind m = 0 := by
  have hk : kind m ≤ 6 := by unfold kind; repeat (first | split | omega)
  have ex : ∀ p n, m.pa = p → m.data.length = n → (L1 + j < p ∨ p + n ≤ L1 + j) → False := by
    intro p n hp hn hout
    rw [byteAt_out (by rw [hp, hn]; exact hout)] at hb; cases hb
  rcases (by omega : kind m = 0 ∨ kind m = 1 ∨ kind m = 2 ∨ kind m = 3 ∨ kind m = 4 ∨ kind m = 5 ∨
    kind m = 6) with h | h | h | h | h | h | h
  · exact .inr (.inr h)
  · have := kind_1 h; exact (ex _ _ this.1 this.2.1 (by simp [L1, Z, Ct, Y]; omega)).elim
  · exact .inl h
  · exact .inr (.inl h)
  · have := kind_4 h
    exact (ex _ _ this.1 (by rw [this.2.1, toBytes_length]) (by simp [L1, Z, Lk, X]; omega)).elim
  · have := kind_5 h
    exact (ex _ _ this.1 (by rw [this.2.1, toBytes_length]) (by simp [L1, Z, Lk, X]; omega)).elim
  · have := kind_6 h; exact (ex _ _ this.1 this.2.1 (by simp [L1, Z, Lk, X]; omega)).elim

/-- A message writing an L2 byte is of class 4, 5, 6 or dead. -/
theorem kind_L2 {m : PMsg} {j : Nat} (hj : j < 4) (hb : (m.byteAt (Lk + j)).isSome = true) :
    kind m = 4 ∨ kind m = 5 ∨ kind m = 6 ∨ kind m = 0 := by
  have hk : kind m ≤ 6 := by unfold kind; repeat (first | split | omega)
  have ex : ∀ p n, m.pa = p → m.data.length = n → (Lk + j < p ∨ p + n ≤ Lk + j) → False := by
    intro p n hp hn hout
    rw [byteAt_out (by rw [hp, hn]; exact hout)] at hb; cases hb
  rcases (by omega : kind m = 0 ∨ kind m = 1 ∨ kind m = 2 ∨ kind m = 3 ∨ kind m = 4 ∨ kind m = 5 ∨
    kind m = 6) with h | h | h | h | h | h | h
  · exact .inr (.inr (.inr h))
  · have := kind_1 h; exact (ex _ _ this.1 this.2.1 (by simp [Lk, X, Ct, Y]; omega)).elim
  · have := kind_2 h
    exact (ex _ _ this.1 (by rw [this.2.1, toBytes_length]) (by simp [L1, Z, Lk, X]; omega)).elim
  · have := kind_3 h
    exact (ex _ _ this.1 (by rw [this.2.1, toBytes_length]) (by simp [L1, Z, Lk, X]; omega)).elim
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr (.inl h))

/-- A message writing a field byte is of class 1 or dead. -/
theorem kind_C {m : PMsg} {j : Nat} (hj : j < 8) (hb : (m.byteAt (Ct + j)).isSome = true) :
    kind m = 1 ∨ kind m = 0 := by
  have hk : kind m ≤ 6 := by unfold kind; repeat (first | split | omega)
  have ex : ∀ p n, m.pa = p → m.data.length = n → (Ct + j < p ∨ p + n ≤ Ct + j) → False := by
    intro p n hp hn hout
    rw [byteAt_out (by rw [hp, hn]; exact hout)] at hb; cases hb
  rcases (by omega : kind m = 0 ∨ kind m = 1 ∨ kind m = 2 ∨ kind m = 3 ∨ kind m = 4 ∨ kind m = 5 ∨
    kind m = 6) with h | h | h | h | h | h | h
  · exact .inr h
  · exact .inl h
  · have := kind_2 h
    exact (ex _ _ this.1 (by rw [this.2.1, toBytes_length]) (by simp [L1, Z, Ct, Y]; omega)).elim
  · have := kind_3 h
    exact (ex _ _ this.1 (by rw [this.2.1, toBytes_length]) (by simp [L1, Z, Ct, Y]; omega)).elim
  · have := kind_4 h
    exact (ex _ _ this.1 (by rw [this.2.1, toBytes_length]) (by simp [Lk, X, Ct, Y]; omega)).elim
  · have := kind_5 h
    exact (ex _ _ this.1 (by rw [this.2.1, toBytes_length]) (by simp [Lk, X, Ct, Y]; omega)).elim
  · have := kind_6 h; exact (ex _ _ this.1 this.2.1 (by simp [Lk, X, Ct, Y]; omega)).elim

/-- `isC` (the field class of OwnALockDefs.lean) is class 1. -/
theorem isC_knd {M : List PMsg} {t : Nat} : isC M t = true ↔ knd M t = 1 := by
  unfold isC knd
  rw [clsB_iff]
  constructor
  · rintro ⟨m, hm, hc⟩; rw [hm]; show kind m = 1; unfold kind; rw [if_pos hc]
  · intro h
    cases hm : msgAt M t with
    | none => rw [hm] at h; cases h
    | some m => rw [hm] at h; exact ⟨m, rfl, kind_1 h⟩

/-! ## 3. The text's messages -/

theorem msgAt_of {M : List PMsg} {ts : Nat} {m : PMsg} (h1 : 1 ≤ ts) (hm : M[ts - 1]? = some m) :
    msgAt M ts = some m := C.msgAt_of h1 hm

theorem kind_a1 : kind ⟨L1, toBytes 1 4, some 1, .excl⟩ = 2 := by decide
theorem kind_r1 : kind ⟨L1, toBytes 0 4, some 0, .plain⟩ = 3 := by decide
theorem kind_a2 : kind ⟨Lk, toBytes 1 4, some 1, .excl⟩ = 4 := by decide
theorem kind_r2 : kind ⟨Lk, toBytes 0 4, some 1, .plain⟩ = 5 := by decide
theorem kind_jk : kind ⟨Lk, toBytes J 4, some 0, .plain⟩ = 6 := by decide
theorem kind_bt : kind ⟨Lk, toBytes 0 4, some 0, .plain⟩ = 6 := by decide
theorem kind_cm {d : List (BitVec 8)} {h : Nat} (hd : d.length = 8) (hh : h < 2) :
    kind ⟨Ct, d, some h, .plain⟩ = 1 := by
  unfold kind; rw [if_pos ⟨rfl, hd, rfl, by simp only [Option.some.injEq]; omega⟩]

/-- The dead predicate of (4). -/
def dd4 (M : List PMsg) (t : Nat) : Prop := 1 ≤ t ∧ knd M t = 0

theorem notDd_of {M : List PMsg} {ts : Nat} {m : PMsg} (hm : M[ts - 1]? = some m) (hk : kind m ≠ 0) :
    ¬ dd4 M ts := by
  rintro ⟨h1, hD⟩
  rw [knd_of (msgAt_of h1 hm)] at hD; exact hk hD

/-! ## 4. Lists of timestamps -/

/-- Class-`k` timestamps above `lo`. -/
def bagK (M : List PMsg) (k lo : Nat) : List Nat := (rng M).filter (fun t => decide (lo < t) && isK M k t)

theorem mem_bagK {M : List PMsg} {k lo t : Nat} : t ∈ bagK M k lo ↔ t ∈ rng M ∧ lo < t ∧ knd M t = k := by
  unfold bagK isK; simp [List.mem_filter]

theorem cBag_K (M : List PMsg) (lw : Nat) : cBag M lw = bagK M 1 lw := by
  unfold cBag bagK
  refine List.filter_congr (fun t _ => ?_)
  unfold isK
  cases h : isC M t
  · have : knd M t ≠ 1 := fun e => by rw [isC_knd.2 e] at h; cases h
    simp [this]
  · simp [isC_knd.1 h]

/-! ## 5. Resources -/

/-- THE PRE-ALLOCATED NAME FAMILIES of (4) (plan R-a5: allocated at adequacy start, one per timestamp): claim tokens
`tk`, saved-proposition names `σ` (plan §3 σ_t), deposit one-shots `δ` (plan §3 `deposited_t`). -/
structure SV where
  tk : Nat → GName
  σ : Nat → GName
  δ : Nat → GName

def bN : Namespace := ndot nroot "promBirth"
def l1N : Namespace := ndot nroot "promL1"

section res

variable {GF : BundledGFunctors} [GhostVarG GF HSt] [GhostVarG GF Bool] [TokenG GF] [SavedPropG GF] [InvGS GF]

/-- Not yet deposited (plan §3 `notYet_t`). -/
def dpendD (sv : SV) (t : Nat) : IProp GF := ghost_var (sv.δ t) (.own 1) false

/-- Deposited (plan §3 `deposited_t`), persistent. -/
def dshotD (sv : SV) (t : Nat) : IProp GF := ghost_var (sv.δ t) .discard true

/-- **THE SAVED-PROPOSITION SLOT** of birth-class `t` (plan §3 "The rev-4 design": `inv (N.@t) (∃ P, σ_t … P ∗
(notYet_t ∨ P ∨ claim_t))`): not yet deposited, or deposited with a persisted saved proposition `P` and `P` or the
claim token.  Pre-allocated at adequacy start for every birth-class `t`; `P` is chosen at the deposit.  The claim
token is (1a)'s `nxtTok`: the token of the first L2 write after `t` — the AMO whose read source is `t` (plan §3
"Atomicity": "The lock protocol gives the claim token to 'the AMO whose read source is s'"). -/
def bSlot (M : List PMsg) (sv : SV) (t : Nat) : IProp GF :=
  inv (ndot bN t) iprop(dpendD sv t ∨
    (dshotD sv t ∗ ∃ P : IProp GF, saved_prop_own (sv.σ t) .discard P ∗ (P ∨ nxtTok M sv.tk t)))

/-- Birth-class at address `lk`: hart 0's plain zero word. -/
def bthAt (M : List PMsg) (lk : Int) (b : Nat) : Prop :=
  ∃ m, msgAt M b = some m ∧ m.pa = lk ∧ m.data = toBytes 0 4 ∧ m.cls = .plain ∧ m.tid = some 0

/-- **THE LOCK HANDLE of a lock born at `b`** (criterion (ii)): its birth `b` (a plain store at `lk`), the
deposit done (`dshotD b`), the deposited resource NAMED — `R ∗ token γ`, `γ` from the runtime initlock — and the
slot. -/
def isLockAt (M : List PMsg) (sv : SV) (γ : GName) (lk : Int) (R : IProp GF) (b : Nat) : IProp GF :=
  iprop(⌜bthAt M lk b⌝ ∗ dshotD sv b ∗ saved_prop_own (sv.σ b) .discard iprop(R ∗ token γ) ∗ bSlot M sv b)

/-- **`isLockA sv γ lk R`** — the statement shape of MachCSL's `isLock γ lk s R` (Lock.lean:3325): persistent,
`γ` the lock's ghost name (allocated at runtime by `initlock`), `lk` the lock word, `R` the protected resource. -/
def isLockA (M : List PMsg) (sv : SV) (γ : GName) (lk : Int) (R : IProp GF) : IProp GF :=
  iprop(∃ b, isLockAt M sv γ lk R b)

/-- Hart 0's L2 words above `lo`: their `pend`s. -/
def zBag (g : AGN) (M : List PMsg) (lo : Nat) : IProp GF := iprop([∗list] t ∈ bagK M 6 lo, pend g t)

/-- The field message `c` holds 5 (hart 0's initialisation). -/
def cAt5 (M : List PMsg) (c : Nat) : Prop := msgAt M c = some ⟨Ct, toBytes 5 8, some 0, .plain⟩

/-- **L1's RESOURCE deposited at its release `s`**: the L2 handle with runtime `γ`, born at `b < s`, protecting the
field's points-to with latest write `c < s` (holding 5), and the `pend`s of hart 0's L2 words above `b`. -/
def Pub1 (g : AGN) (M : List PMsg) (sv : SV) (s : Nat) : IProp GF :=
  iprop(∃ γ b c, ⌜b < s ∧ c < s ∧ cAt5 M c⌝ ∗ isLockAt M sv γ Lk (cPts g M c) b ∗ zBag g M b)

/-- L1's RELEASE SLOT of `t` (plan §3 "The deposit", release-class): `pend t`, or `shot t` and the resource or the
claim token. -/
def l1Slot (g : AGN) (M : List PMsg) (sv : SV) (t : Nat) : IProp GF :=
  inv (ndot l1N t) iprop(pend g t ∨ (shot g t ∗ (Pub1 g M sv t ∨ token (sv.tk t))))

/-- THE PROTOCOL'S PERSISTENT PART. -/
def pCtx (g : AGN) (M : List PMsg) (sv : SV) : IProp GF :=
  iprop(doomInv g M ∗ ([∗list] t ∈ (rng M).filter (isK M 3), l1Slot g M sv t) ∗
    ([∗list] t ∈ (rng M).filter (bth M), bSlot M sv t) ∗
    ([∗list] t ∈ (rng M).filter (isK M 0), deadInv g t))

/-- Class-`k` timestamps above `lo`, except `ex`. -/
def bagKX (M : List PMsg) (k lo ex : Nat) : List Nat :=
  (rng M).filter (fun t => decide (lo < t) && decide (t ≠ ex) && isK M k t)

/-- HART 1's L2 OWN-MESSAGE BAG above `lo` (except `ex`), as (1a)'s `obag`: the `pend` and the token of each of
its L2 AMO writes. -/
def ob2 (g : AGN) (M : List PMsg) (sv : SV) (lo ex : Nat) : IProp GF :=
  iprop(([∗list] t ∈ bagKX M 4 lo ex, pend g t) ∗ [∗list] t ∈ bagKX M 4 lo ex, token (sv.tk t))

instance (sv : SV) (t : Nat) : Persistent (dshotD (GF := GF) sv t) := by unfold dshotD; infer_instance
instance (sv : SV) (t : Nat) : Timeless (dshotD (GF := GF) sv t) := by unfold dshotD; infer_instance
instance (sv : SV) (t : Nat) : Timeless (dpendD (GF := GF) sv t) := by unfold dpendD; infer_instance
instance (M : List PMsg) (sv : SV) (t : Nat) : Persistent (bSlot (GF := GF) M sv t) := by
  unfold bSlot; infer_instance
instance (M : List PMsg) (sv : SV) (γ : GName) (lk : Int) (R : IProp GF) (b : Nat) :
    Persistent (isLockAt M sv γ lk R b) := by unfold isLockAt; infer_instance
instance (M : List PMsg) (sv : SV) (γ : GName) (lk : Int) (R : IProp GF) :
    Persistent (isLockA M sv γ lk R) := by unfold isLockA; infer_instance
instance (g : AGN) (M : List PMsg) (sv : SV) (t : Nat) : Persistent (l1Slot (GF := GF) g M sv t) := by
  unfold l1Slot; infer_instance
instance (g : AGN) (M : List PMsg) (sv : SV) : Persistent (pCtx (GF := GF) g M sv) := by unfold pCtx; infer_instance
instance (g : AGN) (M : List PMsg) (lo : Nat) : Timeless (zBag (GF := GF) g M lo) := by
  unfold zBag; exact BigSepL.bigSepL_timeless (fun _ => inferInstance)

theorem dpendD_dshotD (sv : SV) (t : Nat) : dpendD (GF := GF) sv t ∗ dshotD sv t ⊢ False := by
  unfold dpendD dshotD
  iintro ⟨H1, H2⟩
  ihave %h := ghost_var_valid_2 $$ H1 H2
  exact absurd h.2 (by decide)

end res

/-! ## 6. The trace invariant -/

/-- **THE VERDICT's trace invariant**: every field load reads hart 0's initialisation 5 (never the image's 0 nor
the junk `J`). -/
def q4 (ev : Trace) : Prop := ∀ e ∈ ev, ∀ tvs, isCLd e tvs → tvs.map Prod.snd = toBytes 5 8

def qs4 : Nat → Trace → Prop := fun _ => q4

theorem q4_nil : q4 [] := fun _ h => by cases h

theorem q4_snoc {ev : Trace} {e : PEv} (h : q4 ev) (he : ∀ tvs, isCLd e tvs → tvs.map Prod.snd = toBytes 5 8) :
    q4 (ev ++ [e]) := by
  intro e' he' tvs hl
  rcases List.mem_append.1 he' with h1 | h1
  · exact h e' h1 tvs hl
  · rw [List.mem_singleton] at h1; subst h1; exact he tvs hl

theorem notCLd_st {b : Int} {d : List (BitVec 8)} {a c : List Dsrc} {ts : Nat} (tvs : List (Nat × BitVec 8)) :
    isCLd (LStore false false b d a c, some ts) tvs → tvs.map Prod.snd = toBytes 5 8 := by
  rintro ⟨_, h⟩; cases h

theorem notCLd_rmw {aq rl : Bool} {b : Int} {tvs0 : List (Nat × BitVec 8)} {d : List (BitVec 8)}
    {a c : List Dsrc} {ts : Nat} (tvs : List (Nat × BitVec 8)) :
    isCLd (LRmw aq rl b tvs0 d a c, some ts) tvs → tvs.map Prod.snd = toBytes 5 8 := by
  rintro ⟨_, h⟩; cases h

/-! ## 7. The functor bundle -/

section gf
open Iris COFE Auth HeapView

/-- track (a)'s bundle (`ownGF`, OwnAMP.lean) plus SAVED PROPOSITIONS at index 7 (plan R-a5: "It also needs
`SavedPropG` in the tree's functor bundle"). -/
noncomputable def ownGF4 : BundledGFunctors := fun n =>
  match n with
  | 0 => ⟨InvMapF, by infer_instance⟩
  | 1 => ⟨constOF CoPsetDisjL, by infer_instance⟩
  | 2 => ⟨constOF (DisjointLeibnizSet PosSet), by infer_instance⟩
  | 3 => ⟨AuthURF (constOF Credit), by infer_instance⟩
  | 4 => ⟨GhostVarF HSt, by infer_instance⟩
  | 5 => ⟨GhostVarF Bool, by infer_instance⟩
  | 6 => ⟨TokenF, by infer_instance⟩
  | 7 => ⟨DFracAgree.DFracAgreeRF (LaterOF IdOF), by infer_instance⟩
  | _ => ⟨constOF Unit, by infer_instance⟩

instance : WsatGpreS ownGF4 where
  inv := { τ := 0, transp := by unfold ownGF4; rfl }
  enabled := { τ := 1, transp := by unfold ownGF4; rfl }
  disabled := { τ := 2, transp := by unfold ownGF4; rfl }

instance : LcGpreS ownGF4 where
  lc_elem := { τ := 3, transp := by unfold ownGF4; rfl }

instance : InvGpreS ownGF4 where
  toWsatGpreS := inferInstance
  toLcGpreS := inferInstance

instance : GhostVarG ownGF4 HSt where
  elemG := { τ := 4, transp := by unfold ownGF4; rfl }

instance : GhostVarG ownGF4 Bool where
  elemG := { τ := 5, transp := by unfold ownGF4; rfl }

instance : TokenG ownGF4 where
  elemG := { τ := 6, transp := by unfold ownGF4; rfl }

instance : SavedPropG ownGF4 where
  elemG := { τ := 7, transp := by unfold ownGF4; rfl }

end gf

end Weak.Prom.OA.P
