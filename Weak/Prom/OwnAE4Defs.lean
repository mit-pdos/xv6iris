/-
Weak/Prom: **E-a4, THE LOCK LIFECYCLE on track (a), dead set empty — the test, the lifetime windows, the
shape-only slots** (stage E-a4; owner ruling [OWN.P14], context.md item 21; G4-review3.md §1 (E-a2 rows on
`bth`/`bthAt`), §5 A-3″, §6 item 1; plan rev 7 §3 "Lock birth and deferred deposits", "Acquire", "Atomicity",
R-a4, R-a5).

THE TEST `t7` (xv6's pipe lifecycle, TWO lifetimes of one lock at one address — hart text loops over rounds
`k = a3 ∈ {1, 2}`):
* hart 0 (`p0`, pipealloc + pipeclose): `kfree` junk `J` in the lock word (round 1: kalloc's junk; round 2: THE
  DEATH of lifetime 1) and in the field, INITLOCK `sw zero,0(s1)` (the birth `b`), field init 5, `fence rw,w;
  sb a3,0(a2)` (PUBLICATION of round `k`, byte `Z`), then waits for both acquirers' DONE bytes (`Z+1`, `Z+2` equal
  `k`), `fence rw,rw`, and closes like `pipeclose`: xv6's acquire, `sd a0/zero,16(s1)`, xv6's release (a plain
  `sw zero` — the SAME message shape as its births);
* harts 1, 2 (`pA`): wait for the publication of round `k`, (1c)'s xv6 acquire/release text `p1c` around
  `ld; addi; sd` of the field, then `fence rw,w; sb a3,0(a6)` (its done byte).
LIFETIME WINDOWS (pure functions of `M`): the life of a lock born at `b` is `W(b) = {t > b | no junk in (b, t]}`
(`inW`), "junk" being any message touching the lock word that is not lock-shaped (`isJ2`, e.g. `kfree`'s memset);
its DEATH is the first junk above `b` (`isD`); everything else above `b` is BEYOND (`bey`).
SLOTS (all classified by shape, never by "is a birth"): the zero words of `W(b)` get release slots `rSl` (content
decided by the author at the fulfil: the protected resource `Rs5`, or the DEATH MARK `dM k` of a closing release);
`b`'s own resource goes through the shape-only birth slot family `bSlot` (pre-allocated over EVERY plain zero word
at the lock address, any author); the death gets `dSl` (fulfilled only with `dM k`); each hart's own lock-shaped
words are its PART `prt` (unbounded above, its beyond-window releases included), handed out at the birth
(`hSl`) and RETURNED through the done byte (`Dn7`).  A reader identifies the birth through the publication.
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Prom.OwnAE2

namespace Weak.Prom.OA.E4

open MachCSL MachCSL.Stdpp Iris.Std
open Weak (Image Dsrc)
open Weak.Prom Weak.Prom.PF Weak.Prom.Mach Weak.Prom.Mach.Cert
open Weak.Prom.Ref (Instr Test two64)
open Weak.Prom.Ref.Lit (X Y Z)
open Weak.Prom.OA.P (L1 J SV bSlot dshotD dpendD msgAt_of cAt5)
open Weak.Prom.OA.C (Pc)
open Weak.Prom.OA.E
open Weak.Prom.OA.EP (tL1 tL2 isL2O isCO cB tch_far_of lk_L2O tL1_of tL2_of)
open Weak.Prom.OA.E2
open PLabel
open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode

/-! ## 1. The texts, the test -/

/-- **Hart 0** (`s1 = x9 = Lk`, `a1 = x11 = C`, `a2 = x12 = Z`, `a3 = x13` the round, `t3 = x28 = 3`):
`0: li t1,J  1: sw t1,0(s1)  2: sd t1,0(a1)  3: sw zero,0(s1)  4: li t2,5  5: sd t2,0(a1)  6: fence rw,w
 7: sb a3,0(a2)  8: lbu t0,1(a2)  9: bne t0,a3,8  10: lbu t0,2(a2)  11: bne t0,a3,10  12: fence rw,rw
 13: li a4,1  14: mv a5,a4  15: amoswap.w.aq a5,a5,(s1)  16: sext.w a5,a5  17: bnez a5,14  18: sd a0,16(s1)
 19: sd zero,16(s1)  20: fence rw,w  21: sw zero,0(s1)  22: addi a3,a3,1  23: bne a3,t3,0`. -/
def p0 : List XI :=
  [.i (Weak.Prom.Ref.Lit.li 6 J), .i (Weak.Prom.Ref.Lit.sw 6 9), .i (Weak.Prom.Ref.Lit.sd 6 11),
   .i (Weak.Prom.Ref.Lit.sw 0 9), .i (Weak.Prom.Ref.Lit.li 7 5), .i (Weak.Prom.Ref.Lit.sd 7 11),
   .i Weak.Prom.Ref.Lit.fRWW, .i (Weak.Prom.Ref.Lit.sb 13 12), .i (.load 1 false 5 12 1), .i (.br .ne 5 13 8),
   .i (.load 1 false 5 12 2), .i (.br .ne 5 13 10), .i Weak.Prom.Ref.Lit.fRWRW, .i (Weak.Prom.Ref.Lit.li 14 1),
   .i (.alu .add 15 0 14), .i (Weak.Prom.Ref.Lit.amoswapW true false 15 15 9), .addiw 15 15 0,
   .i (.br .ne 15 0 14), .i (Weak.Prom.Ref.Lit.sd 10 9 16), .i (Weak.Prom.Ref.Lit.sd 0 9 16),
   .i Weak.Prom.Ref.Lit.fRWW, .i (Weak.Prom.Ref.Lit.sw 0 9), .i (Weak.Prom.Ref.Lit.addi 13 13 1),
   .i (.br .ne 13 28 0)]

/-- **Harts 1, 2** (`a0 = x10` the cpu, `a6 = x16` the hart's done byte):
`0: lbu t0,0(a2)  1: bne t0,a3,0  2: fence rw,rw  3: li a4,1  4: mv a5,a4  5: amoswap.w.aq a5,a5,(s1)
 6: sext.w a5,a5  7: bnez a5,4  8: sd a0,16(s1)  9: ld t2,(a1)  10: addi t2,t2,1  11: sd t2,(a1)
 12: sd zero,16(s1)  13: fence rw,w  14: sw zero,0(s1)  15: fence rw,w  16: sb a3,0(a6)  17: addi a3,a3,1
 18: bne a3,t3,0`. -/
def pA : List XI :=
  [.i (.load 1 false 5 12 0), .i (.br .ne 5 13 0), .i Weak.Prom.Ref.Lit.fRWRW, .i (Weak.Prom.Ref.Lit.li 14 1),
   .i (.alu .add 15 0 14), .i (Weak.Prom.Ref.Lit.amoswapW true false 15 15 9), .addiw 15 15 0,
   .i (.br .ne 15 0 4), .i (Weak.Prom.Ref.Lit.sd 10 9 16), .i (Weak.Prom.Ref.Lit.ld 7 11),
   .i (Weak.Prom.Ref.Lit.addi 7 7 1), .i (Weak.Prom.Ref.Lit.sd 7 11), .i (Weak.Prom.Ref.Lit.sd 0 9 16),
   .i Weak.Prom.Ref.Lit.fRWW, .i (Weak.Prom.Ref.Lit.sw 0 9), .i Weak.Prom.Ref.Lit.fRWW,
   .i (Weak.Prom.Ref.Lit.sb 13 16), .i (Weak.Prom.Ref.Lit.addi 13 13 1), .i (.br .ne 13 28 0)]

abbrev b0 : List Instr := p0.map XI.base
abbrev bA : List Instr := pA.map XI.base

/-- The test: everything 0 initially; two rounds (`a3 = 1, 2`, `t3 = 3`). -/
def t7 : Test :=
  { harts := [b0, bA, bA]
    regs0 := [[(9, X), (10, 0x5200), (11, Y), (12, Z), (13, 1), (28, 3)],
      [(9, X), (10, 0x5000), (11, Y), (12, Z), (13, 1), (16, Z + 1), (28, 3)],
      [(9, X), (10, 0x5100), (11, Y), (12, Z), (13, 1), (16, Z + 2), (28, 3)]]
    img := []
    cond := Weak.Prom.Ref.Lit.mpFF.cond }

abbrev xs7 : List (List XI) := [p0, pA]
abbrev img7 : Image := testImg t7
abbrev w7 (M : List PMsg) (h : Nat) : HW LP Unit Unit := xW xs7 img7 M h

theorem xOf_p0 : xOf xs7 b0 = some p0 := by decide
theorem xOf_pA : xOf xs7 bA = some pA := by decide

theorem img7_eq (a : Int) : img7 a = some 0 := by simp [img7, testImg, Test.imgF, t7, bv8]

/-- The instruction of a text at `pc`. -/
theorem atI {s : LP} {X : List XI} {ins : Instr} (hp : s.prog = X.map XI.base) (hx : X[s.pc]? = some (.i ins)) :
    s.prog[s.pc]? = some ins := by rw [hp, List.getElem?_map, hx]; rfl

/-! ## 2. The flag bytes -/

def fBP (o : Nat) (m : PMsg) : Prop := m.pa = (Z : Int) + o ∧ m.data.length = 1
instance (o : Nat) : DecidablePred (fBP o) := fun m => by unfold fBP; infer_instance

/-- A 1-byte message at `Z + o` (`o = 0`: publication; `o = 1, 2`: done bytes). -/
def fB (o : Nat) (M : List PMsg) (t : Nat) : Bool := clsB (fBP o) M t
/-- The flag word's junk: touches it, none of the three byte shapes. -/
def fJ7 (M : List PMsg) (t : Nat) : Bool := tL1 M t && !fB 0 M t && !fB 1 M t && !fB 2 M t

/-- A message's first byte (the flag value). -/
def val7 (M : List PMsg) (t : Nat) : Nat :=
  match msgAt M t with
  | some m => (m.data.headD 0).toNat
  | none => 0

theorem fB_L1 {M : List PMsg} {o t : Nat} (ho : o < 4) (h : fB o M t = true) : tL1 M t = true := by
  obtain ⟨m, hm, hp, hl⟩ := clsB_iff.1 h
  exact tL1_of hm (j := o) ho (by
    rw [show L1 + (o : Int) = m.pa + ((0 : Nat) : Int) by rw [hp]; simp [L1], byteAt_off rfl,
      List.getElem?_eq_getElem (by omega)]; rfl)

theorem fB_ne {M : List PMsg} {o o' t : Nat} (hne : o ≠ o') (h : fB o M t = true) : fB o' M t = false := by
  obtain ⟨m, hm, hp, _⟩ := clsB_iff.1 h
  cases hc : fB o' M t
  · rfl
  · obtain ⟨m', hm', hp', _⟩ := clsB_iff.1 hc
    rw [hm] at hm'; cases hm'; rw [hp] at hp'; omega

theorem fB_of {M : List PMsg} {o t : Nat} {d : List (BitVec 8)} {tid : Option Nat} {c : PClass} (hd : d.length = 1)
    (hm : msgAt M t = some ⟨(Z : Int) + o, d, tid, c⟩) : fB o M t = true := by
  rw [fB, clsB_of hm]; exact decide_eq_true ⟨rfl, hd⟩

/-- A flag source: the byte at `Z + o` read from `t` (a message) is the flag message's value, or `t` is junk. -/
theorem flag_src {M : List PMsg} {o t : Nat} {m : PMsg} {v : BitVec 8} (ho : o < 3) (hm : msgAt M t = some m)
    (hb : m.byteAt ((Z : Int) + o) = some v) : (fB o M t = true ∧ val7 M t = v.toNat) ∨ fJ7 M t = true := by
  have hT : tL1 M t = true := tL1_of hm (j := o) (by omega) (by rw [hb]; rfl)
  by_cases h : fB o M t = true
  · left; refine ⟨h, ?_⟩
    obtain ⟨m', hm', hp, hl⟩ := clsB_iff.1 h
    have e : m = m' := Option.some.inj (hm.symm.trans hm'); subst e
    rw [show ((Z : Int) + o) = m.pa + ((0 : Nat) : Int) by rw [hp]; simp, byteAt_off rfl] at hb
    have : m.data = [v] := by
      match hd : m.data, hl with
      | [x], _ => rw [hd] at hb; simp at hb; rw [hb]
    simp [val7, hm, this]
  · right
    have hne : ∀ o', o' < 3 → o' ≠ o → fB o' M t = false := fun o' _ hne => by
      cases hc : fB o' M t
      · rfl
      · obtain ⟨m', hm', hp, hl⟩ := clsB_iff.1 hc
        have e : m = m' := Option.some.inj (hm.symm.trans hm'); subst e
        rw [byteAt_none (m := m) (a := (Z : Int) + o) (by rw [hp, hl]; omega)] at hb; cases hb
    have h0 : fB 0 M t = false := by
      rcases (by omega : o = 0 ∨ 0 ≠ o) with rfl | h'
      · simpa using h
      · exact hne 0 (by decide) h'
    have h1 : fB 1 M t = false := by
      rcases (by omega : o = 1 ∨ 1 ≠ o) with rfl | h'
      · simpa using h
      · exact hne 1 (by decide) h'
    have h2 : fB 2 M t = false := by
      rcases (by omega : o = 2 ∨ 2 ≠ o) with rfl | h'
      · simpa using h
      · exact hne 2 (by decide) h'
    simp [fJ7, hT, h0, h1, h2]

/-- An L2-byte source touching the flag word is flag junk (a flag byte message is far from the lock word). -/
theorem fJ_of_L2 {M : List PMsg} {t j : Nat} {m : PMsg} (hm : msgAt M t = some m) (hj : j < 4)
    (hb : (m.byteAt (Lk + j)).isSome = true) (hT : tL1 M t = true) : fJ7 M t = true := by
  have hn : ∀ o, fB o M t = true → o < 4 → False := fun o h ho => by
    obtain ⟨m', hm', hp, hl⟩ := clsB_iff.1 h
    have e : m = m' := Option.some.inj (hm.symm.trans hm'); subst e
    rw [byteAt_none (m := m) (a := Lk + j) (by rw [hp, hl]; simp [Lk, X, Z]; omega)] at hb; cases hb
  have h0 : fB 0 M t = false := by cases h : fB 0 M t; rfl; exact (hn 0 h (by decide)).elim
  have h1 : fB 1 M t = false := by cases h : fB 1 M t; rfl; exact (hn 1 h (by decide)).elim
  have h2 : fB 2 M t = false := by cases h : fB 2 M t; rfl; exact (hn 2 h (by decide)).elim
  simp [fJ7, hT, h0, h1, h2]

/-! ## 3. The protocol -/

/-- **THE PROTOCOL of E-a4**: a message touching the lock word is a 4-byte message at it; a message touching the
flag word lies inside it. -/
def π7 : Proto :=
  ⟨fun m => (tchB m Lk 4 = true → m.pa = Lk ∧ m.data.length = 4) ∧
    (tchB m L1 4 = true → L1 ≤ m.pa ∧ m.pa + m.data.length ≤ L1 + 4), fun _ => True⟩

theorem ok7_lk {d : List (BitVec 8)} {tid : Option Nat} {c : PClass} (hd : d.length = 4) : π7.okMsg ⟨Lk, d, tid, c⟩ :=
  ⟨fun _ => ⟨rfl, hd⟩, fun ht => by rw [tchB_far (.inl (by simp [hd, Lk, L1, X, Z]))] at ht; cases ht⟩

theorem ok7_z {o : Nat} {d : List (BitVec 8)} {tid : Option Nat} {c : PClass} (ho : o < 3) (hd : d.length = 1) :
    π7.okMsg ⟨(Z : Int) + o, d, tid, c⟩ :=
  ⟨(fun ht => by rw [tchB_far (.inr (by simp [Lk, X, Z]; omega))] at ht; cases ht),
   (fun _ => ⟨by simp [L1]; omega, by simp [L1, hd]; omega⟩)⟩

theorem ok7_far {a : Int} {d : List (BitVec 8)} {tid : Option Nat} {c : PClass} (hd : d.length = 8)
    (ha : a = Ct ∨ a = Pc) : π7.okMsg ⟨a, d, tid, c⟩ := by
  rcases ha with rfl | rfl
  · exact ⟨(fun ht => by rw [tchB_far (.inr (by simp [Lk, Ct, X, Y]))] at ht; cases ht),
      (fun ht => by rw [tchB_far (.inl (by simp [hd, Ct, L1, Y, Z]))] at ht; cases ht)⟩
  · exact ⟨(fun ht => by rw [tchB_far (.inr (by simp [Pc, Lk, X]))] at ht; cases ht),
      (fun ht => by rw [tchB_far (.inl (by simp [hd, Pc, Lk, L1, X, Z]))] at ht; cases ht)⟩

/-- **THE GUARDED REFUTATION**: a message touching a field byte and a lock or flag word violates `π7`. -/
theorem straddle7 {img : Image} {M : List PMsg} {t j : Nat} {m : PMsg} (hm : msgAt M t = some m)
    (hL : tchB m Lk 4 = true ∨ tchB m L1 4 = true) (hj : j < 8) (hb : (m.byteAt (Ct + j)).isSome = true) :
    grd π7 img M t False :=
  grd_imp (fun hok => by
    rcases hL with hL | hL
    · obtain ⟨hp, hl⟩ := hok.1 hL
      have := byteAt_in hp hl hb
      simp only [Lk, Ct, X, Y] at this; omega
    · obtain ⟨hp, hl⟩ := hok.2 hL
      have := byteAt_in (k := m.data.length) rfl rfl hb
      simp only [L1, Ct, Z, Y] at this hp hl; omega) (grd_self hm)

/-! ## 4. Lifetime windows -/

/-- No junk of the lock word in `(b, t)`. -/
def noJ (M : List PMsg) (b t : Nat) : Bool := (List.range t).all (fun u => decide (u ≤ b) || !isJ2 M u)

theorem noJ_iff {M : List PMsg} {b t : Nat} : noJ M b t = true ↔ ∀ u, b < u → u < t → isJ2 M u = false := by
  unfold noJ
  rw [List.all_eq_true]
  constructor
  · intro h u h1 h2
    have := h u (List.mem_range.2 h2)
    simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at this
    rcases this with h3 | h3
    · omega
    · exact h3
  · intro h u hu
    have hu := List.mem_range.1 hu
    simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.not_eq_true']
    by_cases h1 : u ≤ b
    · exact .inl h1
    · exact .inr (h u (by omega) hu)

/-- **THE WINDOW** of the lock born at `b`: above `b`, no junk below. -/
def inW (M : List PMsg) (b t : Nat) : Bool := decide (b < t) && noJ M b t
/-- **THE DEATH** of the lock born at `b`: the first junk above `b`. -/
def isD (M : List PMsg) (b t : Nat) : Bool := inW M b t && isJ2 M t
/-- **BEYOND** the lock born at `b`: above some junk above `b`. -/
def bey (M : List PMsg) (b t : Nat) : Bool := decide (b < t) && !noJ M b t

theorem bey_of {M : List PMsg} {b u t : Nat} (hbu : b < u) (hut : u < t) (hJ : isJ2 M u = true) :
    bey M b t = true := by
  have : noJ M b t = false := by
    cases h : noJ M b t
    · rfl
    · rw [noJ_iff.1 h u hbu hut] at hJ; cases hJ
  simp [bey, this]; omega

theorem inW_or_bey {M : List PMsg} {b t : Nat} (h : b < t) : inW M b t = true ∨ bey M b t = true := by
  cases hn : noJ M b t
  · right; simp [bey, hn, h]
  · left; simp [inW, hn, h]

/-- Beyond the window lies above the death. -/
theorem bey_death {M : List PMsg} {b : Nat} : ∀ n t, t ≤ n → bey M b t = true → ∃ d, d < t ∧ isD M b d = true := by
  intro n
  induction n with
  | zero => intro t ht h; simp [bey] at h; omega
  | succ n ih =>
    intro t ht h
    have hn : noJ M b t = false := by simp [bey] at h; simpa using h.2
    obtain ⟨u, hbu, hut, hJ⟩ : ∃ u, b < u ∧ u < t ∧ isJ2 M u = true := by
      apply Classical.byContradiction; intro hne
      rw [noJ_iff.2 (fun u h1 h2 => by
        cases hc : isJ2 M u
        · rfl
        · exact absurd ⟨u, h1, h2, hc⟩ hne)] at hn; cases hn
    cases hu : noJ M b u
    · obtain ⟨d, hd, hD⟩ := ih u (by omega) (by simp [bey, hu]; omega)
      exact ⟨d, by omega, hD⟩
    · exact ⟨u, hut, by simp [isD, inW, hu, hJ]; omega⟩

theorem isD_J {M : List PMsg} {b d : Nat} (h : isD M b d = true) : isJ2 M d = true := by
  simp only [isD, Bool.and_eq_true] at h; exact h.2

/-! ## 5. The verdict's trace invariant -/

/-- A critical section's pair is mutually exclusive: every byte of the load read the latest text-shaped field
store below the store. -/
def pairOk (M : List PMsg) (tvs : List (Nat × BitVec 8)) (ts : Nat) : Prop :=
  ∃ lw, (∀ p ∈ tvs, p.1 = lw) ∧ latestC3 M lw ts

/-- **(1c)'s MUTUAL EXCLUSION per critical section** (a field load immediately followed, among the memory events,
by a field store): `pairOk`. -/
def qMx (M : List PMsg) (ev : Trace) : Prop :=
  ∀ i tvs ts (a c e : List Dsrc) (d : List (BitVec 8)), ev[i]? = some (LLoad false false Ct tvs a, none) →
    ev[i + 1]? = some (LStore false false Ct d c e, some ts) → pairOk M tvs ts

/-- THE VERDICT's trace invariant: per-section mutual exclusion and (4)'s "the field never reads junk or the
image" (`qGd`, E-a2). -/
def q7 (M : List PMsg) (ev : Trace) : Prop := qMx M ev ∧ qGd M ev
/-- The per-hart trace obligation: hart 0 (no field load at all), the acquirers `q7`. -/
abbrev qs7 (M : List PMsg) : Nat → Trace → Prop := fun h => if h = 0 then noLd else q7 M

theorem getA (ev : Trace) (e : PEv) (i : Nat) :
    (ev ++ [e])[i]? = if i < ev.length then ev[i]? else if i = ev.length then some e else none := by
  by_cases h1 : i < ev.length
  · rw [if_pos h1, List.getElem?_append_left h1]
  · rw [if_neg h1, List.getElem?_append_right (by omega)]
    by_cases h2 : i = ev.length
    · rw [if_pos h2, h2]; simp
    · rw [if_neg h2]; simp; omega

/-- **APPEND**: the new pair, if any (the last event a field load, the new one a field store) is mutually
exclusive, and a new load's bytes have good sources. -/
theorem q7_app {M : List PMsg} {ev : Trace} {e : PEv} (hq : q7 M ev)
    (hl : ∀ tvs, isCLd e tvs → ∀ p ∈ tvs, gd M p.1)
    (hp : ∀ tvs ts (a c e' : List Dsrc) (d : List (BitVec 8)), ev[ev.length - 1]? = some (LLoad false false Ct tvs a, none) →
      ev ≠ [] → e = (LStore false false Ct d c e', some ts) → pairOk M tvs ts) : q7 M (ev ++ [e]) := by
  refine ⟨fun i tvs ts a c e' d h1 h2 => ?_, fun e1 h1 tvs hc => ?_⟩
  · rw [getA] at h1 h2
    by_cases hi : i + 1 < ev.length
    · rw [if_pos (by omega)] at h1; rw [if_pos hi] at h2; exact hq.1 i tvs ts a c e' d h1 h2
    · rw [if_neg hi] at h2
      by_cases hi' : i + 1 = ev.length
      · rw [if_pos hi'] at h2; rw [if_pos (by omega)] at h1
        exact hp tvs ts a c e' d (by rw [← hi']; simpa using h1) (by intro h; subst h; simp at hi') (Option.some.inj h2)
      · rw [if_neg hi'] at h2; cases h2
  · rcases List.mem_append.1 h1 with h | h
    · exact hq.2 e1 h tvs hc
    · rw [List.mem_singleton] at h; subst h; exact hl tvs hc

theorem q7_noLd {M : List PMsg} {ev : Trace} (h : noLd ev) : q7 M ev :=
  ⟨fun i tvs _ a _ _ _ h1 _ => absurd ⟨a, rfl⟩ (h _ (List.mem_of_getElem? h1) tvs),
   fun e he tvs hl => absurd hl (h e he tvs)⟩

theorem q7_snoc {M : List PMsg} {ev : Trace} {e : PEv} (hq : q7 M ev) (he : ∀ tvs, ¬ isCLd e tvs)
    (hs : ∀ ts, ¬ isCSt e ts) : q7 M (ev ++ [e]) :=
  q7_app hq (fun tvs hc => absurd hc (he tvs)) (fun _ ts _ c e' d _ _ h => absurd ⟨d, c, e', h⟩ (hs ts))

theorem q7_ld {M : List PMsg} {ev : Trace} {tvs : List (Nat × BitVec 8)} {a : List Dsrc} (hq : q7 M ev)
    (hg : ∀ p ∈ tvs, gd M p.1) : q7 M (ev ++ [(LLoad false false Ct tvs a, none)]) :=
  q7_app hq (fun tvs' ⟨_, h⟩ => by cases h; exact hg) (fun _ _ _ _ _ _ _ _ h => by cases h)

theorem q7_pair {M : List PMsg} {ev : Trace} {tvs : List (Nat × BitVec 8)} {a b c : List Dsrc} {d : List (BitVec 8)}
    {ts : Nat} (hq : q7 M (ev ++ [(LLoad false false Ct tvs a, none)])) (hp : pairOk M tvs ts) :
    q7 M (ev ++ [(LLoad false false Ct tvs a, none)] ++ [(LStore false false Ct d b c, some ts)]) :=
  q7_app hq (fun _ ⟨_, h⟩ => by cases h) (fun tvs' ts' _ _ _ _ h1 _ h3 => by
    simp at h1; obtain ⟨rfl, -⟩ := h1; cases h3; exact hp)

/-! ## 6. Owners: the lock word's shapes, bags -/

/-- A plain zero word at the lock address (ANY author): the shape-only birth-slot class. -/
def zwP (m : PMsg) : Prop := m.pa = Lk ∧ m.data = toBytes 0 4 ∧ m.cls = .plain
instance : DecidablePred zwP := fun m => by unfold zwP; infer_instance
def zw (M : List PMsg) (t : Nat) : Bool := clsB zwP M t

theorem zw_wr {M : List PMsg} {b j : Nat} (hj : j < 4) (hb : zw M b = true) : wrB M (Lk + j) b := by
  obtain ⟨m, hm, hp, hd, _⟩ := clsB_iff.1 hb
  refine ⟨m, hm, ?_⟩
  rw [← hp, byteAt_off rfl, hd, List.getElem?_eq_getElem (by rw [toBytes_length]; exact hj)]; rfl

/-- Hart `h`'s release-shaped words above `lo` (all; beyond the window of `b`). -/
def rA (M : List PMsg) (h lo : Nat) : List Nat :=
  (rng M).filter (fun t => decide (lo < t) && isR2 M t && byH M h t)
def rB (M : List PMsg) (h b lo : Nat) : List Nat :=
  (rng M).filter (fun t => decide (lo < t) && isR2 M t && byH M h t && bey M b t)
/-- The lock word's junk above `lo` (all; beyond the window of `b`). -/
def jA (M : List PMsg) (lo : Nat) : List Nat := (rng M).filter (fun t => decide (lo < t) && isJ2 M t)
def jB (M : List PMsg) (b lo : Nat) : List Nat := (rng M).filter (fun t => decide (lo < t) && isJ2 M t && bey M b t)
/-- Hart 0's unclaimed done messages of hart `o`, value at least `k`. -/
def tkF (M : List PMsg) (o k : Nat) : List Nat := (rng M).filter (fun t => fB o M t && decide (k ≤ val7 M t))

def rN7 : Namespace := ndot nroot "promRel7"
def dN7 : Namespace := ndot nroot "promDeath7"
def hN7 : Namespace := ndot nroot "promPart7"
def pN7 : Namespace := ndot nroot "promPub7"
def nN7 : Namespace := ndot nroot "promDone7"

section res

variable {GF : BundledGFunctors} [GhostVarG GF HSt] [GhostVarG GF Bool] [TokenG GF] [SavedPropG GF] [InvGS GF]

/-- **HART `h`'s PART of the lock born at `b`, above `lo`**: the `pend` of its acquire words and its tokens of its
lock words (all above `lo`), and the `pend` of its release words BEYOND the window (their slots do not exist). -/
def prt (g : AGN) (M : List PMsg) (tk : Nat → GName) (h b lo : Nat) : IProp GF :=
  iprop(obg g M tk h lo 0 ∗ [∗list] t ∈ rB M h b lo, pend g t)

/-- The same, every release word (the re-split's input). -/
def fpt (g : AGN) (M : List PMsg) (tk : Nat → GName) (h lo : Nat) : IProp GF :=
  iprop(obg g M tk h lo 0 ∗ [∗list] t ∈ rA M h lo, pend g t)

/-- The birth's resource (deferred to the publication). -/
def Rb7 (g : AGN) (M : List PMsg) (c sp : Nat) : IProp GF := iprop(cPts5 g M c ∗ pPts5 g M sp)

/-- **PARTICIPATION** of hart `h` in round `k` (a one-shot, not yet given up). -/
def eP (ek : Nat → Nat → GName) (h k : Nat) : IProp GF := ghost_var (ek h k) (.own 1) false
/-- Hart `h`'s participation in round `k` given up (persistent). -/
def eD (ek : Nat → Nat → GName) (h k : Nat) : IProp GF := ghost_var (ek h k) .discard true

/-- **THE DEATH MARK of round `k`**: every hart's participation given up (persistent, timeless). -/
def dM (ek : Nat → Nat → GName) (k : Nat) : IProp GF := iprop(eD ek 0 k ∗ eD ek 1 k ∗ eD ek 2 k)

/-- **A RELEASE SLOT of round `k`** (a zero word in the window): the AUTHOR decides the content at the fulfil —
the protected resource, or the death mark (a closing release). -/
def rSl (g : AGN) (M : List PMsg) (tk : Nat → GName) (ek : Nat → Nat → GName) (k r : Nat) : IProp GF :=
  inv (ndot rN7 r) iprop(pend g r ∨ (shot g r ∗ token (tk r) ∗ (Rs5 g M r ∨ dM ek k ∨ nxtTok M tk r)))

/-- **THE DEATH'S SLOT**: fulfilled only with the death mark. -/
def dSl (g : AGN) (ek : Nat → Nat → GName) (k d : Nat) : IProp GF :=
  inv (ndot dN7 d) iprop(pend g d ∨ (shot g d ∗ dM ek k))

/-- HART `h`'s part of round `k` (born at `b`), until it claims it. -/
def hSl (g : AGN) (M : List PMsg) (tk : Nat → GName) (ak : Nat → Nat → GName) (h b k : Nat) : IProp GF :=
  inv (ndot (ndot hN7 h) k) iprop(prt g M tk h b b ∨ token (ak h k))

/-- **THE PROTOCOL OF THE LOCK BORN AT `b` IN ROUND `k`** (built at initlock): the release slots of its window
(by author), the death's slot, the acquirers' parts. -/
def lkB (g : AGN) (M : List PMsg) (tk : Nat → GName) (ak ek : Nat → Nat → GName) (b k : Nat) : IProp GF :=
  iprop(([∗list] h ∈ List.range 3,
      [∗list] r ∈ (rng M).filter (fun t => inW M b t && isR2 M t && byH M h t), rSl g M tk ek k r) ∗
    ([∗list] d ∈ (rng M).filter (isD M b), dSl g ek k d) ∗ hSl g M tk ak 1 b k ∗ hSl g M tk ak 2 b k)

/-- **THE BIRTH HANDLE**: `b` is a plain zero word at the lock address (shape only), its deferred deposit done,
naming `P`. -/
def hdl (M : List PMsg) (sv : SV) (b : Nat) (P : IProp GF) : IProp GF :=
  iprop(⌜zw M b = true⌝ ∗ dshotD sv b ∗ saved_prop_own (sv.σ b) .discard P ∗ bSlot M sv b)

/-- **THE PUBLICATION of round `val7 M t`** at `t`: the handle and the protocol of the lock born at `b < t`. -/
def Pub7 (g : AGN) (M : List PMsg) (sv : SV) (ak ek : Nat → Nat → GName) (t : Nat) : IProp GF :=
  iprop(∃ b c sp, ⌜b < t ∧ c < t ∧ sp < t ∧ cAt5 M c⌝ ∗ hdl M sv b (Rb7 g M c sp) ∗
    lkB g M sv.tk ak ek b (val7 M t))

def pSl (g : AGN) (M : List PMsg) (sv : SV) (ak ek : Nat → Nat → GName) (t : Nat) : IProp GF :=
  inv (ndot pN7 t) iprop(pend g t ∨ (shot g t ∗ Pub7 g M sv ak ek t))

/-- **THE DONE MESSAGE's content**: hart `h` returns its part and its participation token of round `val7 M t`. -/
def Dn7 (g : AGN) (M : List PMsg) (tk : Nat → GName) (ek : Nat → Nat → GName) (h t : Nat) : IProp GF :=
  iprop(∃ b lo, ⌜b ≤ lo ∧ lo < t⌝ ∗ prt g M tk h b lo ∗ eP ek h (val7 M t))

def nSl (g : AGN) (M : List PMsg) (tk : Nat → GName) (ek : Nat → Nat → GName) (h t : Nat) : IProp GF :=
  inv (ndot (ndot nN7 h) t) iprop(pend g t ∨ (shot g t ∗ (Dn7 g M tk ek h t ∨ token (tk t))))

/-- THE BOOT PROTOCOL'S PERSISTENT PART. -/
def ctx7 (g : AGN) (M : List PMsg) (sv : SV) (ak ek : Nat → Nat → GName) : IProp GF :=
  iprop(doomInv g M ∗ ([∗list] t ∈ (rng M).filter (fB 0 M), pSl g M sv ak ek t) ∗
    ([∗list] t ∈ (rng M).filter (fB 1 M), nSl g M sv.tk ek 1 t) ∗
    ([∗list] t ∈ (rng M).filter (fB 2 M), nSl g M sv.tk ek 2 t) ∗
    ([∗list] t ∈ (rng M).filter (fJ7 M), lkJunk g t) ∗ ([∗list] t ∈ (rng M).filter (zw M), bSlot M sv t))

instance (ek : Nat → Nat → GName) (h k : Nat) : Persistent (eD (GF := GF) ek h k) := by unfold eD; infer_instance
instance (ek : Nat → Nat → GName) (h k : Nat) : Timeless (eD (GF := GF) ek h k) := by unfold eD; infer_instance
instance (ek : Nat → Nat → GName) (h k : Nat) : Timeless (eP (GF := GF) ek h k) := by unfold eP; infer_instance
instance (ek : Nat → Nat → GName) (k : Nat) : Persistent (dM (GF := GF) ek k) := by unfold dM; infer_instance
instance (ek : Nat → Nat → GName) (k : Nat) : Timeless (dM (GF := GF) ek k) := by unfold dM; infer_instance
instance (g : AGN) (M : List PMsg) (tk : Nat → GName) (ek : Nat → Nat → GName) (k r : Nat) :
    Persistent (rSl (GF := GF) g M tk ek k r) := by unfold rSl; infer_instance
instance (g : AGN) (ek : Nat → Nat → GName) (k d : Nat) : Persistent (dSl (GF := GF) g ek k d) := by
  unfold dSl; infer_instance
instance (g : AGN) (M : List PMsg) (tk : Nat → GName) (ak : Nat → Nat → GName) (h b k : Nat) :
    Persistent (hSl (GF := GF) g M tk ak h b k) := by unfold hSl; infer_instance
instance (g : AGN) (M : List PMsg) (tk : Nat → GName) (ak ek : Nat → Nat → GName) (b k : Nat) :
    Persistent (lkB (GF := GF) g M tk ak ek b k) := by unfold lkB; infer_instance
instance (M : List PMsg) (sv : SV) (b : Nat) (P : IProp GF) : Persistent (hdl M sv b P) := by
  unfold hdl; infer_instance
instance (g : AGN) (M : List PMsg) (sv : SV) (ak ek : Nat → Nat → GName) (t : Nat) :
    Persistent (Pub7 (GF := GF) g M sv ak ek t) := by unfold Pub7; infer_instance
instance (g : AGN) (M : List PMsg) (sv : SV) (ak ek : Nat → Nat → GName) (t : Nat) :
    Persistent (pSl (GF := GF) g M sv ak ek t) := by unfold pSl; infer_instance
instance (g : AGN) (M : List PMsg) (tk : Nat → GName) (ek : Nat → Nat → GName) (h t : Nat) :
    Persistent (nSl (GF := GF) g M tk ek h t) := by unfold nSl; infer_instance
instance (g : AGN) (M : List PMsg) (sv : SV) (ak ek : Nat → Nat → GName) :
    Persistent (ctx7 (GF := GF) g M sv ak ek) := by unfold ctx7; infer_instance
instance (g : AGN) (M : List PMsg) (tk : Nat → GName) (h b lo : Nat) : Timeless (prt (GF := GF) g M tk h b lo) := by
  unfold prt
  have : Timeless ([∗list] t ∈ rB M h b lo, pend (GF := GF) g t) := BigSepL.bigSepL_timeless (fun _ => inferInstance)
  infer_instance
instance (g : AGN) (M : List PMsg) (c sp : Nat) : Timeless (Rb7 (GF := GF) g M c sp) := by
  unfold Rb7; infer_instance
instance (g : AGN) (M : List PMsg) (tk : Nat → GName) (ek : Nat → Nat → GName) (h t : Nat) :
    Timeless (Dn7 (GF := GF) g M tk ek h t) := by unfold Dn7; infer_instance

/-- **A RETURNED PART FEEDS THE NEXT BIRTH `b'`**: everything above `b'` lies beyond the old window. -/
theorem prt_fpt (g : AGN) (M : List PMsg) (tk : Nat → GName) {h b lo b' : Nat} (hl : lo ≤ b')
    (hb : ∀ t, b' < t → bey M b t = true) : prt (GF := GF) g M tk h b lo ⊢ fpt g M tk h b' := by
  unfold prt fpt rB rA
  iintro ⟨Ho, Hr⟩
  isplitl [Ho]
  · iapply obg_up g M tk hl (Nat.zero_le _) $$ Ho
  · iapply bsl_filter_mono (pend g) _ _ (fun t ht => by
      simp only [Bool.and_eq_true, decide_eq_true_eq] at ht ⊢; exact ⟨⟨⟨by omega, ht.1.2⟩, ht.2⟩, hb t ht.1.1⟩)
      (rng M) $$ Hr

end res

end Weak.Prom.OA.E4
