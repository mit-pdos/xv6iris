/-
Weak/Prom: **E-a2, THE CONTENDED RUNTIME-BORN LOCK on track (a), dead set empty — the test, the owners, the
protocol of the lock born at runtime** (stage E-a2; owner ruling [OWN.P13], context.md item 20; G4-review2.md §1
note 3, §6 A-3′, §7; plan rev 7 §3 "Lock birth and deferred deposits", "Acquire", "Atomicity", "The deposit",
R-a4, R-a5).

THE TEST `t5` (xv6's actual shape for every lock: born by `initlock` at runtime, contended):
* hart 0 runs (4)'s pipealloc text `p4o` VERBATIM (OwnAPipeDefs.lean): `kfree` junk in L2's word and in the field,
  INITLOCK `sw zero,0(s1)` (the birth `b`, a plain store), the field's initialisation `c` (5), and
  `fence rw,w; sw zero,0(a2)` — the PUBLICATION `f`: the boot word at `Z` (image 1) released to 0;
* harts 1 and 2 run `p5h`: `lw t0,0(a2); bnez t0,0; fence rw,rw` (wait for the publication — xv6 `main.c`'s
  `while(started == 0); __sync_synchronize();` shape, polarity inverted), then (1c)'s xv6 acquire/release text
  `p1c` on L2 VERBATIM (branch target shifted by 3) around the `ld; addi; sd` client of the field.
PER-BYTE OWNERS FROM BOOT (E-a style, OwnAEBase.lean): every message touching the word at `Z` is the flag
protocol's (a 4-byte word at `Z` → its slot `fSlot5`, holding the persistent publication once fulfilled; anything
else → `lkJunk`); every message touching L2's word (not `Z`'s) is hart 0's page's (`pend` and claim token, any
shape, any author); the field's to hart 0's points-to; the cpu field's to hart 0's bag; the rest unused.
THE RE-SPLIT AT INITLOCK (`lkB5 b`, built by hart 0 at its birth store, OwnAE2Lock.lean): the L2 word's bag ABOVE
`b` becomes the lock's persistent protocol — release-shaped words → release slots `rSlot5`, junk → `lkJunk`, and
for EVERY hart `h < 3` of the machine an invariant `hSlot5 h b` holding `h`'s own-message bag above `b`, claimable
once by `h` with its boot token `ak h b`.  No acquirer identity is fixed: every hart is offered its part.
THE PROTOCOL is (4)'s `π4` (a message touching a lock word — L2 or `Z` — is a 4-byte message at it).
THE VERDICT's trace invariant `q5`: (1c)'s mutual exclusion `qLk3` (per byte, over the text-shaped field stores of
ALL three harts) and (4)'s "the field never reads junk or the image" `qGd` (every loaded byte's source is a
text-shaped field store that is hart 0's initialisation 5 or an acquirer's).
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Prom.OwnAEPipeH1

namespace Weak.Prom.OA.E2

open MachCSL MachCSL.Stdpp Iris.Std
open Weak (Image Dsrc)
open Weak.Prom Weak.Prom.PF Weak.Prom.Mach Weak.Prom.Mach.Cert
open Weak.Prom.Ref (Instr Test two64)
open Weak.Prom.Ref.Lit (X Y Z)
open Weak.Prom.OA.P (L1 J p4o b4o SV bSlot bth bthAt isLockAt cAt5 dshotD msgAt_of)
open Weak.Prom.OA.E
open Weak.Prom.OA.EP (tL1 tL2 isL2O isCO tL1_of tL2_of tch_far_of lk_L2O cB)
open PLabel
open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode

/-! ## 1. The texts, the test -/

/-- **Harts 1, 2**: wait for the publication, then (1c)'s xv6 acquire/release text on L2 (`t0 = x5`, `a0 = x10`
(`mycpu()`), `s1 = x9 = L2`, `a1 = x11 = C`, `a2 = x12 = Z`):
`0: lw t0,0(a2)  1: bnez t0,0  2: fence rw,rw  3: li a4,1  4: mv a5,a4  5: amoswap.w.aq a5,a5,(s1)  6: sext.w a5,a5
 7: bnez a5,4  8: sd a0,16(s1)  9: ld t2,(a1)  10: addi t2,t2,1  11: sd t2,(a1)  12: sd zero,16(s1)  13: fence rw,w
 14: sw zero,0(s1)`. -/
def p5h : List XI :=
  [.i (Weak.Prom.Ref.Lit.lw 5 12), .i (.br .ne 5 0 0), .i Weak.Prom.Ref.Lit.fRWRW,
   .i (Weak.Prom.Ref.Lit.li 14 1), .i (.alu .add 15 0 14), .i (Weak.Prom.Ref.Lit.amoswapW true false 15 15 9),
   .addiw 15 15 0, .i (.br .ne 15 0 4), .i (Weak.Prom.Ref.Lit.sd 10 9 16),
   .i (Weak.Prom.Ref.Lit.ld 7 11), .i (Weak.Prom.Ref.Lit.addi 7 7 1), .i (Weak.Prom.Ref.Lit.sd 7 11),
   .i (Weak.Prom.Ref.Lit.sd 0 9 16), .i Weak.Prom.Ref.Lit.fRWW, .i (Weak.Prom.Ref.Lit.sw 0 9 0)]

abbrev b5h : List Instr := p5h.map XI.base

/-- The test: the word at `Z` is born 1 (unpublished), everything else 0. -/
def t5 : Test :=
  { harts := [b4o, b5h, b5h]
    regs0 := [[(9, X), (11, Y), (12, Z)], [(9, X), (10, 0x5000), (11, Y), (12, Z)],
      [(9, X), (10, 0x5100), (11, Y), (12, Z)]]
    img := [(Z, 1)]
    cond := Weak.Prom.Ref.Lit.mpFF.cond }

abbrev xs5 : List (List XI) := [p4o, p5h]

theorem p5o_at {s : LP} (h : s.prog = b4o) : xOf xs5 s.prog = some p4o := by rw [h]; decide
theorem p5h_at {s : LP} (h : s.prog = b5h) : xOf xs5 s.prog = some p5h := by rw [h]; decide

abbrev img5 : Image := testImg t5

/-- Hart `h`'s world. -/
abbrev w5 (M : List PMsg) (h : Nat) : HW LP Unit Unit := xW xs5 img5 M h

theorem img5_L1 : img5 L1 = some 1 := by simp [img5, testImg, Test.imgF, t5, bv8, L1, Z]

/-! ## 2. Owners and classes -/

/-- The flag protocol's slot class: a 4-byte word at `Z`. -/
def fPub (M : List PMsg) (t : Nat) : Bool := clsB (fun m => m.pa = L1 ∧ m.data.length = 4) M t
/-- The flag protocol's junk: touches `Z`'s word, not a 4-byte word at `Z`. -/
def fJ (M : List PMsg) (t : Nat) : Bool := tL1 M t && !fPub M t

/-- A lock-word message's shape: 4 bytes at `Lk`, by a hart of the machine (any class). -/
def lmS (m : PMsg) : Prop := m.pa = Lk ∧ m.data.length = 4 ∧ (m.tid = some 0 ∨ m.tid = some 1 ∨ m.tid = some 2)
instance : DecidablePred lmS := fun m => by unfold lmS; infer_instance

/-- L2's acquire-shaped words (value 1), release-shaped words (value 0), junk (anything else touching it). -/
def isA2 (M : List PMsg) (t : Nat) : Bool := isL2O M t && clsB (fun m => lmS m ∧ m.data = toBytes 1 4) M t
def isR2 (M : List PMsg) (t : Nat) : Bool := isL2O M t && clsB (fun m => lmS m ∧ m.data = toBytes 0 4) M t
def isJ2 (M : List PMsg) (t : Nat) : Bool := isL2O M t && !isA2 M t && !isR2 M t

/-- A text-shaped field store, by any of the three harts. -/
def cmP3 (m : PMsg) : Prop :=
  m.pa = Ct ∧ m.data.length = 8 ∧ m.cls = .plain ∧ (m.tid = some 0 ∨ m.tid = some 1 ∨ m.tid = some 2)
instance : DecidablePred cmP3 := fun m => by unfold cmP3; infer_instance
def isC3 (M : List PMsg) (t : Nat) : Bool := clsB cmP3 M t

/-- The cpu field's: touches it, neither lock word nor the field. -/
def isPO (M : List PMsg) (t : Nat) : Bool :=
  clsB (fun m => tchB m C.Pc 8 = true) M t && !tL1 M t && !tL2 M t && !isCO M t

theorem lmS_L2O {M : List PMsg} {t : Nat} {m : PMsg} (hm : msgAt M t = some m) (h : m.pa = Lk)
    (hl : m.data.length = 4) : isL2O M t = true := by
  obtain ⟨pa, d, tid, c⟩ := m; simp only at h hl; subst h; exact lk_L2O hl hm

/-- The text's L2 words. -/
theorem A2_of {M : List PMsg} {t h : Nat} {c : PClass} (hh : h < 3)
    (hm : msgAt M t = some ⟨Lk, toBytes 1 4, some h, c⟩) : isA2 M t = true ∧ byH M h t = true := by
  refine ⟨?_, by simp [byH, tidAt, hm]⟩
  rw [isA2, lmS_L2O hm rfl (toBytes_length 1 4), clsB_of hm]
  exact decide_eq_true ⟨⟨rfl, toBytes_length 1 4, by simp only [Option.some.injEq]; omega⟩, rfl⟩

theorem R2_of {M : List PMsg} {t h : Nat} {c : PClass} (hh : h < 3)
    (hm : msgAt M t = some ⟨Lk, toBytes 0 4, some h, c⟩) : isR2 M t = true ∧ byH M h t = true := by
  refine ⟨?_, by simp [byH, tidAt, hm]⟩
  rw [isR2, lmS_L2O hm rfl (toBytes_length 0 4), clsB_of hm]
  exact decide_eq_true ⟨⟨rfl, toBytes_length 0 4, by simp only [Option.some.injEq]; omega⟩, rfl⟩

theorem C3_of {M : List PMsg} {t h : Nat} {d : List (BitVec 8)} (hh : h < 3) (hd : d.length = 8)
    (hm : msgAt M t = some ⟨Ct, d, some h, .plain⟩) : isC3 M t = true := by
  rw [isC3, clsB_of hm]; exact decide_eq_true ⟨rfl, hd, rfl, by simp only [Option.some.injEq]; omega⟩

/-- A text-shaped field store is the field's. -/
theorem C3_CO {M : List PMsg} {t : Nat} (h : isC3 M t = true) : isCO M t = true := by
  obtain ⟨m, hm, h1, h2, _⟩ := clsB_iff.1 h
  have n1 : tL1 M t = false := tch_far_of hm (.inl (by rw [h1, h2]; simp [Ct, L1, Y, Z]))
  have n2 : tL2 M t = false := tch_far_of hm (.inr (by rw [h1]; simp [Lk, Ct, X, Y]))
  rw [isCO, clsB_of hm, n1, n2]; simp only [Bool.not_false, Bool.and_true]
  refine decide_eq_true (tchB_of (j := 0) (by decide) ?_)
  rw [← h1, byteAt_off rfl, List.getElem?_eq_getElem (by omega)]; rfl

/-- The text's cpu-field store is the cpu field's. -/
theorem PO_of {M : List PMsg} {t h : Nat} {d : List (BitVec 8)} (hd : d.length = 8)
    (hm : msgAt M t = some ⟨C.Pc, d, some h, .plain⟩) : isPO M t = true := by
  have n1 : tL1 M t = false := tch_far_of hm (.inl (by simp [hd, C.Pc, Lk, L1, X, Z]))
  have n2 : tL2 M t = false := tch_far_of hm (.inr (by simp [C.Pc, Lk, X]))
  have n3 : isCO M t = false := by
    rw [isCO, clsB_of hm]; simp only [decide_eq_false_iff_not, Bool.and_eq_false_iff]
    left; left; rw [tchB_far (by simp [hd, C.Pc, Lk, Ct, X, Y])]; simp
  rw [isPO, clsB_of hm, n1, n2, n3]; simp only [Bool.not_false, Bool.and_true]
  exact decide_eq_true (tchB_of (j := 0) (by decide)
    (by rw [byteAt_off rfl, List.getElem?_eq_getElem (by rw [hd]; decide)]; rfl))

/-- A source of an L2 byte: the L2 word's, or the flag's junk. -/
theorem l2_src {M : List PMsg} {t j : Nat} {m : PMsg} (hm : msgAt M t = some m) (hj : j < 4)
    (hb : (m.byteAt (Lk + j)).isSome = true) : isL2O M t = true ∨ fJ M t = true := by
  have h2 := tL2_of hm hj hb
  cases h1 : tL1 M t
  · left; simp [isL2O, h2, h1]
  · right
    have hf : fPub M t = false := by
      rw [fPub, clsB_of hm]; simp only [decide_eq_false_iff_not]
      rintro ⟨hp, hl⟩
      rw [byteAt_none (by rw [hp, hl]; simp [Lk, L1, X, Z]; omega)] at hb; cases hb
    simp [fJ, h1, hf]

/-- An L2-owned message is an acquire, a release, or junk. -/
theorem l2_cls {M : List PMsg} {t : Nat} (h : isL2O M t = true) :
    isA2 M t = true ∨ isR2 M t = true ∨ isJ2 M t = true := by
  unfold isJ2; rw [h]; cases isA2 M t <;> cases isR2 M t <;> simp

theorem A2_R2 {M : List PMsg} {t : Nat} (h : isA2 M t = true) : isR2 M t = false := by
  unfold isA2 at h; unfold isR2
  obtain ⟨m, hm, _, hd⟩ := clsB_iff.1 (Bool.and_eq_true_iff.1 h).2
  rw [clsB_of hm]; simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]
  right; rintro ⟨_, hd'⟩; rw [hd] at hd'; exact absurd hd' (by decide)

theorem R2_A2 {M : List PMsg} {t : Nat} (hR : isR2 M t = true) : isA2 M t = false := by
  cases h : isA2 M t
  · rfl
  · rw [A2_R2 h] at hR; cases hR

/-- The byte an L2 read returns from the birth, an acquire or a release (`k` its word, `0` or `1`). -/
theorem l2_val {M : List PMsg} {b t j : Nat} {v : BitVec 8} (hj : j < 4) (hb : bthAt M Lk b)
    (hv : memByte img5 M t (Lk + j) = some v) (hc : t = b ∨ isA2 M t = true ∨ isR2 M t = true) :
    some v = (toBytes (if isA2 M t = true then 1 else 0) 4)[j]? := by
  have hsrc : ∀ m d, msgAt M t = some m → m.pa = Lk → m.data = d → some v = d[j]? := fun m d hm hp hd => by
    cases t with
    | zero => cases hm
    | succ k =>
      obtain ⟨m', hm', hba⟩ := Option.bind_eq_some_iff.1 (by simpa [memByte] using hv)
      have : m' = m := by simpa [msgAt, hm'] using hm
      subst this; rw [← hba, ← hp, byteAt_off rfl, hd]
  rcases hc with rfl | hA | hR
  · obtain ⟨m, hm, hp, hd, _⟩ := hb
    have hA : isA2 M t = false := by
      cases h : isA2 M t
      · rfl
      · unfold isA2 at h; obtain ⟨m', hm', _, hd'⟩ := clsB_iff.1 (Bool.and_eq_true_iff.1 h).2
        rw [hm] at hm'; cases hm'; rw [hd] at hd'; exact absurd hd' (by decide)
    rw [hA]; exact hsrc m _ hm hp hd
  · unfold isA2 at hA
    obtain ⟨m, hm, ⟨hp, _⟩, hd⟩ := clsB_iff.1 (Bool.and_eq_true_iff.1 hA).2
    rw [show isA2 M t = true by unfold isA2; exact hA, if_pos rfl]; exact hsrc m _ hm hp hd
  · rw [R2_A2 hR]; unfold isR2 at hR
    obtain ⟨m, hm, ⟨hp, _⟩, hd⟩ := clsB_iff.1 (Bool.and_eq_true_iff.1 hR).2
    exact hsrc m _ hm hp hd

/-! ## 3. The verdict's trace invariant -/

/-- `lw` is the latest text-shaped field store below `ts`. -/
def latestC3 (M : List PMsg) (lw ts : Nat) : Prop :=
  isC3 M lw = true ∧ lw < ts ∧ ∀ u, lw < u → u < ts → isC3 M u = false

/-- **(1c)'s MUTUAL EXCLUSION, per byte** (as `qLk`, over all three harts' text-shaped field stores): if the trace
has a field load and a field store at `ts`, every byte of the load was read from the latest such store below `ts`. -/
def qLk3 (M : List PMsg) (ev : Trace) : Prop :=
  ∀ tvs ts, (∃ e ∈ ev, isCLd e tvs) → (∃ e ∈ ev, isCSt e ts) → ∃ lw, (∀ p ∈ tvs, p.1 = lw) ∧ latestC3 M lw ts

/-- A GOOD field source: a text-shaped field store that is hart 0's initialisation (5) or an acquirer's — not the
image (`0`), not `kfree`'s junk (hart 0's other field store). -/
def gd (M : List PMsg) (t : Nat) : Prop := isC3 M t = true ∧ (cAt5 M t ∨ tidAt M t ≠ some 0)

/-- **(4)'s "the field never reads junk or the image"**: every byte of every field load has a good source. -/
def qGd (M : List PMsg) (ev : Trace) : Prop := ∀ e ∈ ev, ∀ tvs, isCLd e tvs → ∀ p ∈ tvs, gd M p.1

def q5 (M : List PMsg) (ev : Trace) : Prop := qLk3 M ev ∧ qGd M ev
def qs5 (M : List PMsg) : Nat → Trace → Prop := fun _ => q5 M

/-- No field load. -/
def noLd (ev : Trace) : Prop := ∀ e ∈ ev, ∀ tvs, ¬ isCLd e tvs

theorem q5_noLd {M : List PMsg} {ev : Trace} (h : noLd ev) : q5 M ev :=
  ⟨fun tvs _ ⟨e, he, hl⟩ _ => absurd hl (h e he tvs), fun e he tvs hl => absurd hl (h e he tvs)⟩

theorem noLd_snoc {ev : Trace} {e : PEv} (h : noLd ev) (he : ∀ tvs, ¬ isCLd e tvs) : noLd (ev ++ [e]) := by
  intro e' he'
  rcases List.mem_append.1 he' with h1 | h1
  · exact h e' h1
  · rw [List.mem_singleton] at h1; subst h1; exact he

theorem noLd_st {b : Int} {d : List (BitVec 8)} {a c : List Dsrc} {ts : Nat} :
    ∀ tvs, ¬ isCLd (LStore false false b d a c, some ts) tvs := fun _ ⟨_, h⟩ => by cases h

theorem noC_noLd {ev : Trace} (h : noC ev) : noLd ev := fun e he => (h e he).1

theorem q5_snoc {M : List PMsg} {ev : Trace} {e : PEv} (hq : q5 M ev)
    (he : (∀ tvs, ¬ isCLd e tvs) ∧ (∀ ts, ¬ isCSt e ts)) : q5 M (ev ++ [e]) := by
  refine ⟨fun tvs ts ⟨e1, h1, hl⟩ ⟨e2, h2, hs⟩ => hq.1 tvs ts ⟨e1, ?_, hl⟩ ⟨e2, ?_, hs⟩, fun e1 h1 tvs hl => ?_⟩
  · rcases List.mem_append.1 h1 with h | h
    · exact h
    · rw [List.mem_singleton] at h; subst h; exact absurd hl (he.1 tvs)
  · rcases List.mem_append.1 h2 with h | h
    · exact h
    · rw [List.mem_singleton] at h; subst h; exact absurd hs (he.2 ts)
  · rcases List.mem_append.1 h1 with h | h
    · exact hq.2 e1 h tvs hl
    · rw [List.mem_singleton] at h; subst h; exact absurd hl (he.1 tvs)

/-- The critical section's load, all of whose bytes have good sources. -/
theorem q5_ld {M : List PMsg} {ev : Trace} {tvs : List (Nat × BitVec 8)} {a : List Dsrc} (h : noC ev)
    (hg : ∀ p ∈ tvs, gd M p.1) : q5 M (ev ++ [(LLoad false false Ct tvs a, none)]) := by
  refine ⟨fun _ ts _ ⟨e2, h2, hs⟩ => ?_, fun e1 h1 tvs' hl => ?_⟩
  · rcases List.mem_append.1 h2 with h2 | h2
    · exact absurd hs ((h e2 h2).2 ts)
    · rw [List.mem_singleton] at h2; subst h2; obtain ⟨_, _, _, h⟩ := hs; cases h
  · rcases List.mem_append.1 h1 with h1 | h1
    · exact absurd hl ((h e1 h1).1 tvs')
    · rw [List.mem_singleton] at h1; subst h1; obtain ⟨_, h⟩ := hl; cases h; exact hg

/-- The critical section's pair: the load read the latest text-shaped field store below the store. -/
theorem q5_pair {M : List PMsg} {ev : Trace} {tvs : List (Nat × BitVec 8)} {a : List Dsrc} {d : List (BitVec 8)}
    {b c : List Dsrc} {ts lw : Nat} (h : noC ev) (hall : ∀ p ∈ tvs, p.1 = lw) (hl : latestC3 M lw ts)
    (hg : gd M lw) :
    q5 M (ev ++ [(LLoad false false Ct tvs a, none)] ++ [(LStore false false Ct d b c, some ts)]) := by
  have hq := q5_ld (M := M) (a := a) h (fun p hp => by rw [hall p hp]; exact hg)
  refine ⟨fun tvs' ts' h1 h2 => ?_, fun e1 h1 tvs' hl1 => ?_⟩
  · obtain ⟨e1, h1, hl1⟩ := h1
    obtain ⟨e2, h2, hs2⟩ := h2
    have e1v : e1 = (LLoad false false Ct tvs a, none) := by
      rcases List.mem_append.1 h1 with h1 | h1
      · rcases List.mem_append.1 h1 with h1 | h1
        · exact absurd hl1 ((h e1 h1).1 tvs')
        · rw [List.mem_singleton] at h1; exact h1
      · rw [List.mem_singleton] at h1; subst h1; obtain ⟨_, h⟩ := hl1; cases h
    have e2v : e2 = (LStore false false Ct d b c, some ts) := by
      rcases List.mem_append.1 h2 with h2 | h2
      · rcases List.mem_append.1 h2 with h2 | h2
        · exact absurd hs2 ((h e2 h2).2 ts')
        · rw [List.mem_singleton] at h2; subst h2; obtain ⟨_, _, _, h⟩ := hs2; cases h
      · rw [List.mem_singleton] at h2; exact h2
    subst e1v e2v
    obtain ⟨_, h⟩ := hl1; cases h
    obtain ⟨_, _, _, h⟩ := hs2; cases h
    exact ⟨lw, hall, hl⟩
  · rcases List.mem_append.1 h1 with h1 | h1
    · exact hq.2 e1 h1 tvs' hl1
    · rw [List.mem_singleton] at h1; subst h1; obtain ⟨_, h⟩ := hl1; cases h

theorem q5_of_memEv {M : List PMsg} {τ : Trace} (h : q5 M (memEv τ)) : q5 M τ := by
  refine ⟨fun tvs ts h1 h2 => ?_, fun e he tvs hl => ?_⟩
  · obtain ⟨e1, h1, hl⟩ := h1
    obtain ⟨e2, h2, hs⟩ := h2
    refine h.1 tvs ts ⟨e1, List.mem_filter.2 ⟨h1, ?_⟩, hl⟩ ⟨e2, List.mem_filter.2 ⟨h2, ?_⟩, hs⟩
    · obtain ⟨_, rfl⟩ := hl; rfl
    · obtain ⟨_, _, _, rfl⟩ := hs; rfl
  · refine h.2 e (List.mem_filter.2 ⟨he, ?_⟩) tvs hl
    obtain ⟨_, rfl⟩ := hl; rfl

/-! ## 4. Bags and resources -/

/-- Hart `h`'s L2 acquire-shaped words above `lo`, except `ex`; its L2 lock words (acquire or release). -/
def bgA (M : List PMsg) (h lo ex : Nat) : List Nat :=
  (rng M).filter (fun t => decide (lo < t) && decide (t ≠ ex) && isA2 M t && byH M h t)
def bgL (M : List PMsg) (h lo ex : Nat) : List Nat :=
  (rng M).filter (fun t => decide (lo < t) && decide (t ≠ ex) && (isA2 M t || isR2 M t) && byH M h t)
/-- The cpu field's messages above `s`. -/
def pB (M : List PMsg) (s : Nat) : List Nat := (rng M).filter (fun t => decide (s < t) && isPO M t)

def lkN5 : Namespace := ndot nroot "promLock5"
def hN5 : Namespace := ndot nroot "promHart5"
def fN5 : Namespace := ndot nroot "promFlag5"

section res

variable {GF : BundledGFunctors} [GhostVarG GF HSt] [GhostVarG GF Bool] [TokenG GF] [SavedPropG GF] [InvGS GF]

/-- **HART `h`'s OWN-MESSAGE BAG for L2 above `lo`** (except `ex`), as (1c)'s `obag`. -/
def obg (g : AGN) (M : List PMsg) (tk : Nat → GName) (h lo ex : Nat) : IProp GF :=
  iprop(([∗list] t ∈ bgA M h lo ex, pend g t) ∗ [∗list] t ∈ bgL M h lo ex, token (tk t))

/-- **THE FIELD'S POINTS-TO, PER BYTE**: a good latest write `lw`, the `pend` of every later message touching it. -/
def cPts5 (g : AGN) (M : List PMsg) (lw : Nat) : IProp GF := iprop(⌜gd M lw⌝ ∗ [∗list] t ∈ cB M lw, pend g t)

/-- The cpu field's bag above `s`. -/
def pPts5 (g : AGN) (M : List PMsg) (s : Nat) : IProp GF := iprop([∗list] t ∈ pB M s, pend g t)

/-- The lock's resource deposited at a release `s` (as (1c)'s `Rs`). -/
def Rs5 (g : AGN) (M : List PMsg) (s : Nat) : IProp GF := iprop((∃ lw, ⌜lw ≤ s⌝ ∗ cPts5 g M lw) ∗ pPts5 g M s)

/-- The lock's resource deposited at the birth (deferred to the publication): the field's points-to at its
initialisation `c`, and the cpu field's whole bag. -/
def Rb5 (g : AGN) (M : List PMsg) (c : Nat) : IProp GF := iprop(cPts5 g M c ∗ pPts5 g M 0)

/-- RELEASE `r`'S SLOT (as (1c)'s `rSlot`). -/
def rSlot5 (g : AGN) (M : List PMsg) (tk : Nat → GName) (r : Nat) : IProp GF :=
  inv (ndot lkN5 r) iprop(pend g r ∨ (shot g r ∗ token (tk r) ∗ (Rs5 g M r ∨ nxtTok M tk r)))

/-- **HART `h`'s PART of the lock born at `b`**: its own-message bag above `b`, until `h` claims it with `ak h b`. -/
def hSlot5 (g : AGN) (M : List PMsg) (tk : Nat → GName) (ak : Nat → Nat → GName) (h b : Nat) : IProp GF :=
  inv (ndot (ndot hN5 h) b) iprop(obg g M tk h b 0 ∨ token (ak h b))

/-- **THE PROTOCOL OF THE LOCK BORN AT `b`** (built at initlock): release slots and junk slots above `b`, and every
hart's part. -/
def lkB5 (g : AGN) (M : List PMsg) (sv : SV) (ak : Nat → Nat → GName) (b : Nat) : IProp GF :=
  iprop(([∗list] r ∈ (rng M).filter (fun t => decide (b < t) && isR2 M t), rSlot5 g M sv.tk r) ∗
    ([∗list] d ∈ (rng M).filter (fun t => decide (b < t) && isJ2 M t), lkJunk g d) ∗
    ([∗list] h ∈ List.range 3, hSlot5 g M sv.tk ak h b))

/-- **THE PUBLICATION** deposited at `t` (persistent: any number of readers): the L2 handle (runtime `γ`, birth
`b < t`, protecting the field at `c < t`), and the lock's protocol. -/
def Pub5 (g : AGN) (M : List PMsg) (sv : SV) (ak : Nat → Nat → GName) (t : Nat) : IProp GF :=
  iprop(∃ γ b c, ⌜b < t ∧ c < t ∧ cAt5 M c⌝ ∗ isLockAt M sv γ Lk (Rb5 g M c) b ∗ lkB5 g M sv ak b)

def fSlot5 (g : AGN) (M : List PMsg) (sv : SV) (ak : Nat → Nat → GName) (t : Nat) : IProp GF :=
  inv (ndot fN5 t) iprop(pend g t ∨ (shot g t ∗ Pub5 g M sv ak t))

/-- THE BOOT PROTOCOL'S PERSISTENT PART: the flag's slots and junk, the birth slots. -/
def ctx5 (g : AGN) (M : List PMsg) (sv : SV) (ak : Nat → Nat → GName) : IProp GF :=
  iprop(doomInv g M ∗ ([∗list] t ∈ (rng M).filter (fPub M), fSlot5 g M sv ak t) ∗
    ([∗list] t ∈ (rng M).filter (fJ M), lkJunk g t) ∗ ([∗list] t ∈ (rng M).filter (bth M), bSlot M sv t))

instance (g : AGN) (M : List PMsg) (tk : Nat → GName) (r : Nat) : Persistent (rSlot5 (GF := GF) g M tk r) := by
  unfold rSlot5; infer_instance
instance (g : AGN) (M : List PMsg) (tk : Nat → GName) (ak : Nat → Nat → GName) (h b : Nat) :
    Persistent (hSlot5 (GF := GF) g M tk ak h b) := by unfold hSlot5; infer_instance
instance (g : AGN) (M : List PMsg) (sv : SV) (ak : Nat → Nat → GName) (b : Nat) :
    Persistent (lkB5 (GF := GF) g M sv ak b) := by unfold lkB5; infer_instance
instance (g : AGN) (M : List PMsg) (sv : SV) (ak : Nat → Nat → GName) (t : Nat) :
    Persistent (Pub5 (GF := GF) g M sv ak t) := by unfold Pub5; infer_instance
instance (g : AGN) (M : List PMsg) (sv : SV) (ak : Nat → Nat → GName) (t : Nat) :
    Persistent (fSlot5 (GF := GF) g M sv ak t) := by unfold fSlot5; infer_instance
instance (g : AGN) (M : List PMsg) (sv : SV) (ak : Nat → Nat → GName) :
    Persistent (ctx5 (GF := GF) g M sv ak) := by unfold ctx5; infer_instance
instance (g : AGN) (M : List PMsg) (lw : Nat) : Timeless (cPts5 (GF := GF) g M lw) := by
  unfold cPts5
  have : Timeless ([∗list] t ∈ cB M lw, pend (GF := GF) g t) := BigSepL.bigSepL_timeless (fun _ => inferInstance)
  infer_instance
instance (g : AGN) (M : List PMsg) (s : Nat) : Timeless (pPts5 (GF := GF) g M s) := by
  unfold pPts5; exact BigSepL.bigSepL_timeless (fun _ => inferInstance)
instance (g : AGN) (M : List PMsg) (s : Nat) : Timeless (Rs5 (GF := GF) g M s) := by unfold Rs5; infer_instance
instance (g : AGN) (M : List PMsg) (c : Nat) : Timeless (Rb5 (GF := GF) g M c) := by unfold Rb5; infer_instance
instance (g : AGN) (M : List PMsg) (tk : Nat → GName) (h lo ex : Nat) : Timeless (obg (GF := GF) g M tk h lo ex) := by
  unfold obg
  have : Timeless ([∗list] t ∈ bgA M h lo ex, pend (GF := GF) g t) := BigSepL.bigSepL_timeless (fun _ => inferInstance)
  have : Timeless ([∗list] t ∈ bgL M h lo ex, token (GF := GF) (tk t)) :=
    BigSepL.bigSepL_timeless (fun _ => inferInstance)
  infer_instance

theorem pPts5_mono (g : AGN) (M : List PMsg) {s s' : Nat} (h : s ≤ s') : pPts5 (GF := GF) g M s ⊢ pPts5 g M s' := by
  unfold pPts5 pB
  exact bsl_filter_mono (pend g) _ _ (fun t ht => by
    simp only [Bool.and_eq_true, decide_eq_true_eq] at ht ⊢; exact ⟨by omega, ht.2⟩) (rng M)

theorem pPts5_take (g : AGN) (M : List PMsg) {sp ts : Nat} (hlt : sp < ts) (hP : isPO M ts = true)
    (htM : 1 ≤ ts ∧ ts ≤ M.length) : pPts5 (GF := GF) g M sp ⊢ pend g ts ∗ pPts5 g M ts := by
  unfold pPts5 pB
  exact bsl_filter_take (pend g) (fun t => decide (sp < t) && isPO M t) (fun t => decide (ts < t) && isPO M t) ts
    (by simp [hP, hlt])
    (fun t ht => by simp only [Bool.and_eq_true, decide_eq_true_eq] at ht ⊢; exact ⟨⟨by omega, ht.2⟩, by omega⟩)
    (rng M) (mem_rng.2 htM) (nodup_rng M)

/-- The field's bag above `lw`: take a later field message `ts`; the bag above `ts` remains. -/
theorem cB_take (g : AGN) (M : List PMsg) {lw ts : Nat} (hlt : lw < ts) (hC : isCO M ts = true)
    (htM : 1 ≤ ts ∧ ts ≤ M.length) :
    ([∗list] t ∈ cB M lw, pend (GF := GF) g t) ⊢ pend g ts ∗ [∗list] t ∈ cB M ts, pend g t := by
  unfold cB
  exact bsl_filter_take (pend g) (fun t => decide (lw < t) && isCO M t) (fun t => decide (ts < t) && isCO M t) ts
    (by simp [hlt, hC])
    (fun t ht => by simp only [Bool.and_eq_true, decide_eq_true_eq] at ht ⊢; exact ⟨⟨by omega, ht.2⟩, by omega⟩)
    (rng M) (mem_rng.2 htM) (nodup_rng M)

/-- The own-message bag: take its own message `ts` (`pend` and token). -/
theorem obg_take (g : AGN) (M : List PMsg) (tk : Nat → GName) {h lo ts : Nat} (hlt : lo < ts)
    (hA : isA2 M ts = true) (hh : byH M h ts = true) (htM : 1 ≤ ts ∧ ts ≤ M.length) :
    obg (GF := GF) g M tk h lo 0 ⊢ (pend g ts ∗ token (tk ts)) ∗ obg g M tk h lo ts := by
  unfold obg bgA bgL
  iintro ⟨HA, HL⟩
  icases bsl_filter_take (pend g) _ (fun t => decide (lo < t) && decide (t ≠ ts) && isA2 M t && byH M h t) ts
    (by simp [hlt, hA, hh]; omega) (fun t ht => by
      simp only [Bool.and_eq_true, decide_eq_true_eq] at ht ⊢; exact ⟨⟨⟨⟨ht.1.1.1, by omega⟩, ht.1.2⟩, ht.2⟩, ht.1.1.2⟩)
    (rng M) (mem_rng.2 htM) (nodup_rng M) $$ HA with ⟨Hp, HA⟩
  icases bsl_filter_take (fun t => token (tk t)) _
    (fun t => decide (lo < t) && decide (t ≠ ts) && (isA2 M t || isR2 M t) && byH M h t) ts
    (by simp [hlt, hA, hh]; omega) (fun t ht => by
      simp only [Bool.and_eq_true, decide_eq_true_eq] at ht ⊢; exact ⟨⟨⟨⟨ht.1.1.1, by omega⟩, ht.1.2⟩, ht.2⟩, ht.1.1.2⟩)
    (rng M) (mem_rng.2 htM) (nodup_rng M) $$ HL with ⟨Ht, HL⟩
  iframe Hp Ht HA HL

/-- The own-message bag above `lo` except `ex` covers the bag above `lo' ≥ lo, ex`. -/
theorem obg_up (g : AGN) (M : List PMsg) (tk : Nat → GName) {h lo lo' ex : Nat} (h1 : lo ≤ lo') (h2 : ex ≤ lo') :
    obg (GF := GF) g M tk h lo ex ⊢ obg g M tk h lo' 0 := by
  unfold obg bgA bgL
  iintro ⟨HA, HL⟩
  isplitl [HA]
  · iapply bsl_filter_mono (pend g) _ _ (fun t ht => by
      simp only [Bool.and_eq_true, decide_eq_true_eq] at ht ⊢; exact ⟨⟨⟨by omega, by omega⟩, ht.1.2⟩, ht.2⟩)
      (rng M) $$ HA
  · iapply bsl_filter_mono (fun t => token (tk t)) _ _ (fun t ht => by
      simp only [Bool.and_eq_true, decide_eq_true_eq] at ht ⊢; exact ⟨⟨⟨by omega, by omega⟩, ht.1.2⟩, ht.2⟩)
      (rng M) $$ HL

end res

end Weak.Prom.OA.E2
