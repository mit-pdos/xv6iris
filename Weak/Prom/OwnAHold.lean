/-
Weak/Prom: **G4 target (3) on track (a): a `holding()`-shaped RACY READ THAT DRIVES A BRANCH** (stage S4a part 3;
plan rev 7 §4 G4 (3); §3 "The xv6 sites that need this are racy reads that drive a branch (`holding()`-shaped …)").

xv6's `holding(lk)` (Xv6/KernelImage.lean, holding+0x0..+0x1e): `lw a5,0(a0); bnez a5,…; li a0,0; ret; …;
ld a5,16(a0); mv s1,a5; jal mycpu; sub a0,s1,a0; seqz a0,a0`, called from `acquire` before the spin loop:
`jal holding; …; bnez a0,panic` (acquire+0x12..+0x18).  Both loads are RACY: another hart may be inside
`acquire`/`release` of the same lock, writing the lock word (`amoswap.w.aq`, `sw zero,0(s1)`) and the cpu field
(`sd a0,16(s1)`, `sd zero,16(s1)`), and each load's value drives a branch.
The test (`t3`): hart 0 runs xv6's lock operations once, straight-line (`li a4,1; amoswap.w.aq a5,a4,(s1);
sd a0,16(s1); sd zero,16(s1); fence rw,w; sw zero,0(s1)`, `a0 = mycpu() = 0x3000`); hart 1 (`a0 = mycpu() =
0x3100`) runs `holding()` and acquire's panic test, the panic being a store to a marker address `Fp`:
`0: lw a5,0(s1)  1: beqz a5,7  2: ld a5,16(s1)  3: sub a3,a5,a0  4: seqz a3,a3 (sltiu)  5: beqz a3,7
 6: sd a0,0(a2)  7: (end)` (`bnez a5,+8; li a0,0; ret` folded into `beqz a5,7`: the same control dependency).
`own_hold`: in every valid run, hart 1 never stores to `Fp`: `holding()` returns 0 in `acquire` (no panic).

FINDING (for the G4 comparison, R-b1): on track (a) this target needs NEITHER the frontier rule NOR ownership.
All of `M` is known, so the classification by CONTENT decides every message: hart 0's text writes exactly four
messages (`shp`), hart 1's only `Fp` messages (`isF`); every other message is DEAD (`deadInv`).  A racy read of the
cpu field returns, byte by byte, the image, one of hart 0's two cpu-field messages (bytes of `0x3000` or `0`), or a
dead message — and a dead read DOOMS the run on the spot (`dead_doom`, free mode), with no frontier and no guard.
So the branch is decided unguarded at the read: the value is `0` or `0x3000`, never `0x3100`.  (The frontier rule
is needed only for RESOURCES — the claims of (1)/(2) — and for protocol facts not determined by content.)
0 named inputs; loop-free, so no prefix-lemma caveat.
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Prom.OwnALock1c

namespace Weak.Prom.OA.H

open MachCSL MachCSL.Stdpp Iris.Std
open Weak (Image Dsrc)
open Weak.Prom Weak.Prom.PF Weak.Prom.Mach Weak.Prom.Mach.Cert
open Weak.Prom.Ref (Instr Test two64 aluOp)
open Weak.Prom.Ref.Lit (X Y)
open Weak.Prom.OA.C (Pc wpKA_alu alg_pc base_pc msgAt_of)
open PLabel
open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode

/-! ## 1. The texts, the test -/

/-- The panic marker. -/
abbrev Fp : Int := 0x4000

/-- Hart 0: xv6's lock operations once (straight line). -/
def p3o : List XI :=
  [.i (Weak.Prom.Ref.Lit.li 14 1), .i (Weak.Prom.Ref.Lit.amoswapW true false 15 14 9),
   .i (Weak.Prom.Ref.Lit.sd 10 9 16), .i (Weak.Prom.Ref.Lit.sd 0 9 16), .i Weak.Prom.Ref.Lit.fRWW,
   .i (Weak.Prom.Ref.Lit.sw 0 9 0)]

/-- Hart 1: `holding()` and acquire's panic test (see the header). -/
def p3h : List XI :=
  [.i (Weak.Prom.Ref.Lit.lw 15 9), .i (.br .eq 15 0 7), .i (Weak.Prom.Ref.Lit.ld 15 9 16), .i (.alu .sub 13 15 10),
   .i (.alui .sltu 13 13 1), .i (.br .eq 13 0 7), .i (Weak.Prom.Ref.Lit.sd 10 12)]

abbrev b3o : List Instr := p3o.map XI.base
abbrev b3h : List Instr := p3h.map XI.base

def t3 : Test :=
  { harts := [b3o, b3h]
    regs0 := [[(9, X), (10, 0x3000)], [(9, X), (10, 0x3100), (12, 0x4000)]]
    img := []
    cond := Weak.Prom.Ref.Lit.mpFF.cond }

abbrev xs3 : List (List XI) := [p3o, p3h]

theorem xOf_3o : xOf xs3 b3o = some p3o := by decide
theorem xOf_3h : xOf xs3 b3h = some p3h := by decide
theorem p3o_at {s : LP} (h : s.prog = b3o) : xOf xs3 s.prog = some p3o := by rw [h]; exact xOf_3o
theorem p3h_at {s : LP} (h : s.prog = b3h) : xOf xs3 s.prog = some p3h := by rw [h]; exact xOf_3h

abbrev w3 (M : List PMsg) (h : Nat) : HW LP Unit Unit := xW xs3 imgL M h

/-! ## 2. Classes (by content) -/

def mA : PMsg := ⟨Lk, toBytes 1 4, some 0, .excl⟩
def mC1 : PMsg := ⟨Pc, toBytes 0x3000 8, some 0, .plain⟩
def mC0 : PMsg := ⟨Pc, toBytes 0 8, some 0, .plain⟩
def mR : PMsg := ⟨Lk, toBytes 0 4, some 0, .plain⟩

/-- Message `t` is exactly `m0`. -/
def shp (M : List PMsg) (m0 : PMsg) (t : Nat) : Bool := decide (msgAt M t = some m0)

/-- A marker message of hart 1. -/
def fmP (m : PMsg) : Prop := m.pa = Fp ∧ m.data.length = 8 ∧ m.cls = .plain ∧ m.tid = some 1
instance : DecidablePred fmP := fun m => by unfold fmP; infer_instance
def isF (M : List PMsg) (t : Nat) : Bool := clsB fmP M t

/-- DEAD: none of the texts' messages. -/
def isDd (M : List PMsg) (t : Nat) : Bool :=
  !shp M mA t && !shp M mC1 t && !shp M mC0 t && !shp M mR t && !isF M t

def ddL (M : List PMsg) (t : Nat) : Prop := 1 ≤ t ∧ isDd M t = true

/-- No marker store. -/
def noF (ev : Trace) : Prop := ∀ e ∈ ev, ∀ d a b ts, e ≠ (LStore false false Fp d a b, some ts)

def qs3 : Nat → Trace → Prop := fun h ev => h = 1 → noF ev

theorem noF_nil : noF [] := fun _ h => by cases h

theorem noF_snoc {ev : Trace} {e : PEv} (h : noF ev) (he : ∀ d a b ts, e ≠ (LStore false false Fp d a b, some ts)) :
    noF (ev ++ [e]) := by
  intro e' he'
  rcases List.mem_append.1 he' with h1 | h1
  · exact h e' h1
  · rw [List.mem_singleton] at h1; subst h1; exact he

theorem noF_of_memEv {τ : Trace} (h : noF (memEv τ)) : noF τ := by
  intro e he d a b ts heq
  refine h e (List.mem_filter.2 ⟨he, ?_⟩) d a b ts heq
  rw [heq]; rfl

theorem shp_of {M : List PMsg} {m0 : PMsg} {ts : Nat} (h1 : 1 ≤ ts) (hm : M[ts - 1]? = some m0) :
    shp M m0 ts = true := by
  unfold shp; rw [msgAt_of h1 hm]; simp

theorem isF_of {M : List PMsg} {ts : Nat} {d : List (BitVec 8)} (hd : d.length = 8) (h1 : 1 ≤ ts)
    (hm : M[ts - 1]? = some ⟨Fp, d, some 1, .plain⟩) : isF M ts = true := by
  rw [isF, clsB_of (msgAt_of h1 hm)]
  exact decide_eq_true ⟨rfl, hd, rfl, rfl⟩

theorem shp_ne {M : List PMsg} {m1 m2 : PMsg} {t : Nat} (hne : m1 ≠ m2) (h1 : shp M m1 t = true) :
    shp M m2 t = false := by
  unfold shp at *
  simp only [decide_eq_true_eq] at h1
  simp only [h1, decide_eq_false_iff_not, Option.some.injEq]
  exact hne

theorem shp_F {M : List PMsg} {m0 : PMsg} {t : Nat} (hp : m0.pa ≠ Fp) (h1 : shp M m0 t = true) :
    isF M t = false := by
  unfold shp at h1
  simp only [decide_eq_true_eq] at h1
  rw [isF, clsB_of h1]
  simp only [decide_eq_false_iff_not]
  exact fun h => hp h.1

/-! ## 3. The racy read of the cpu field (pure) -/

/-- A byte of the cpu field from the image or one of hart 0's two cpu-field messages. -/
def okB (j : Nat) (v : BitVec 8) : Prop := some v = (toBytes 0 8)[j]? ∨ some v = (toBytes 0x3000 8)[j]?

theorem lk_byte_none {d : List (BitVec 8)} (hd : d.length = 4) (tid : Option Nat) (c : PClass) {j : Nat} :
    (⟨Lk, d, tid, c⟩ : PMsg).byteAt (Pc + j) = none := by
  rw [show Pc + (j : Int) = Lk + ((16 + j : Nat) : Int) by simp only [Pc]; omega, byteAt_off rfl]
  exact List.getElem?_eq_none (by simp only [hd]; omega)

theorem shp_eq {M : List PMsg} {m0 m : PMsg} {t : Nat} (hmt : msgAt M t = some m) (h : shp M m0 t = true) :
    m = m0 := by
  unfold shp at h; simp only [decide_eq_true_eq, hmt, Option.some.injEq] at h; exact h

theorem pc_byte {M : List PMsg} {t j : Nat} {v : BitVec 8} (hj : j < 8)
    (hb : memByte imgL M t (Pc + j) = some v) : okB j v ∨ (1 ≤ t ∧ t ≤ M.length ∧ isDd M t = true) := by
  cases t with
  | zero =>
    left; left
    simp only [memByte, imgL_zero, Option.some.injEq] at hb
    subst hb
    rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  | succ k =>
    obtain ⟨m, hm, hba⟩ := memByte_succ hb
    have hmt : msgAt M (k + 1) = some m := by simpa [msgAt] using hm
    by_cases hD : isDd M (k + 1) = true
    · exact .inr ⟨by omega, (msgAt_le hmt).2, hD⟩
    · left
      have hcases : shp M mA (k + 1) = true ∨ shp M mC1 (k + 1) = true ∨ shp M mC0 (k + 1) = true ∨
          shp M mR (k + 1) = true ∨ isF M (k + 1) = true := by
        revert hD; unfold isDd
        cases shp M mA (k + 1) <;> cases shp M mC1 (k + 1) <;> cases shp M mC0 (k + 1) <;>
          cases shp M mR (k + 1) <;> cases isF M (k + 1) <;> simp
      rcases hcases with h | h | h | h | h
      · rw [shp_eq hmt h] at hba; rw [mA, lk_byte_none (by decide)] at hba; cases hba
      · rw [shp_eq hmt h] at hba; right; rw [← hba, mC1, byteAt_off rfl]
      · rw [shp_eq hmt h] at hba; left; rw [← hba, mC0, byteAt_off rfl]
      · rw [shp_eq hmt h] at hba; rw [mR, lk_byte_none (by decide)] at hba; cases hba
      · rw [isF, clsB_of hmt] at h
        have hp := (of_decide_eq_true h).1
        unfold PMsg.byteAt at hba
        rw [hp, if_neg (by simp only [Pc, Lk, Fp, X]; omega)] at hba; cases hba

/-- **THE RACY READ OF THE CPU FIELD**: its value is `0` or `0x3000` (hart 0's `mycpu()`), or it read a DEAD
message. -/
theorem pc_read {M : List PMsg} {tvs : List (Nat × BitVec 8)} (hl : tvs.length = 8)
    (hw : ∀ (j t : Nat) (v : BitVec 8), tvs[j]? = some (t, v) → memByte imgL M t (Pc + j) = some v) :
    (ldVal true 8 tvs = 0 ∨ ldVal true 8 tvs = 0x3000) ∨ ∃ t, 1 ≤ t ∧ t ≤ M.length ∧ isDd M t = true := by
  obtain ⟨t0, v0, t1, v1, t2, v2, t3, v3, t4, v4, t5, v5, t6, v6, t7, v7, rfl⟩ :
      ∃ t0 v0 t1 v1 t2 v2 t3 v3 t4 v4 t5 v5 t6 v6 t7 v7,
        tvs = [(t0, v0), (t1, v1), (t2, v2), (t3, v3), (t4, v4), (t5, v5), (t6, v6), (t7, v7)] := by
    match tvs, hl with
    | [(a0, b0), (a1, b1), (a2, b2), (a3, b3), (a4, b4), (a5, b5), (a6, b6), (a7, b7)], _ =>
      exact ⟨a0, b0, a1, b1, a2, b2, a3, b3, a4, b4, a5, b5, a6, b6, a7, b7, rfl⟩
  have k0 := pc_byte (j := 0) (by decide) (hw 0 _ _ rfl)
  have k1 := pc_byte (j := 1) (by decide) (hw 1 _ _ rfl)
  have k2 := pc_byte (j := 2) (by decide) (hw 2 _ _ rfl)
  have k3 := pc_byte (j := 3) (by decide) (hw 3 _ _ rfl)
  have k4 := pc_byte (j := 4) (by decide) (hw 4 _ _ rfl)
  have k5 := pc_byte (j := 5) (by decide) (hw 5 _ _ rfl)
  have k6 := pc_byte (j := 6) (by decide) (hw 6 _ _ rfl)
  have k7 := pc_byte (j := 7) (by decide) (hw 7 _ _ rfl)
  rcases k0 with k0 | k0
  rotate_left; · exact .inr ⟨_, k0⟩
  rcases k1 with k1 | k1
  rotate_left; · exact .inr ⟨_, k1⟩
  rcases k2 with k2 | k2
  rotate_left; · exact .inr ⟨_, k2⟩
  rcases k3 with k3 | k3
  rotate_left; · exact .inr ⟨_, k3⟩
  rcases k4 with k4 | k4
  rotate_left; · exact .inr ⟨_, k4⟩
  rcases k5 with k5 | k5
  rotate_left; · exact .inr ⟨_, k5⟩
  rcases k6 with k6 | k6
  rotate_left; · exact .inr ⟨_, k6⟩
  rcases k7 with k7 | k7
  rotate_left; · exact .inr ⟨_, k7⟩
  left
  have e0 : toBytes 0 8 = [0, 0, 0, 0, 0, 0, 0, 0] := by decide
  have e3 : toBytes 0x3000 8 = [0, 0x30, 0, 0, 0, 0, 0, 0] := by decide
  unfold okB at k0 k1 k2 k3 k4 k5 k6 k7
  rw [e0, e3] at k0 k1 k2 k3 k4 k5 k6 k7
  simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.some.injEq, or_self] at k0 k1 k2 k3 k4 k5 k6 k7
  subst k0 k2 k3 k4 k5 k6 k7
  have hmap : [(t0, (0 : BitVec 8)), (t1, v1), (t2, 0), (t3, 0), (t4, 0), (t5, 0), (t6, 0), (t7, 0)].map Prod.snd =
      [0, v1, 0, 0, 0, 0, 0, 0] := rfl
  unfold ldVal
  rw [if_pos rfl, hmap]
  rcases k1 with rfl | rfl
  · left; decide
  · right; decide

/-! ## 4. Resources and the setup -/

section res

variable {GF : BundledGFunctors} [GhostVarG GF HSt] [GhostVarG GF Bool] [TokenG GF] [InvGS GF]

/-- The bag of the messages of shape `m0`. -/
def bS (g : AGN) (M : List PMsg) (m0 : PMsg) : IProp GF := iprop([∗list] t ∈ (rng M).filter (shp M m0), pend g t)

/-- Hart 1's marker bag. -/
def bF (g : AGN) (M : List PMsg) : IProp GF := iprop([∗list] t ∈ (rng M).filter (isF M), pend g t)

/-- The dead invariants and the doom box. -/
def ctx3 (g : AGN) (M : List PMsg) : IProp GF :=
  iprop(doomInv g M ∗ [∗list] d ∈ (rng M).filter (isDd M), deadInv g d)

instance (g : AGN) (M : List PMsg) : Persistent (ctx3 (GF := GF) g M) := by unfold ctx3; infer_instance

/-- Take `ts` out of a bag of messages of one shape. -/
theorem bS_take (g : AGN) (M : List PMsg) (m0 : PMsg) {ts : Nat} (h1 : 1 ≤ ts) (hm : M[ts - 1]? = some m0) :
    bS (GF := GF) g M m0 ⊢ pend g ts := by
  unfold bS
  iintro H
  icases bsl_filter_take (pend g) (shp M m0) (fun _ => false) ts (shp_of h1 hm) (fun _ h => by cases h) (rng M)
    (mem_rng.2 (msgAt_le (msgAt_of h1 hm))) (nodup_rng M) $$ H with ⟨Hp, -⟩
  iexact Hp

theorem bF_take (g : AGN) (M : List PMsg) {ts : Nat} {d : List (BitVec 8)} (hd : d.length = 8) (h1 : 1 ≤ ts)
    (hm : M[ts - 1]? = some ⟨Fp, d, some 1, .plain⟩) : bF (GF := GF) g M ⊢ pend g ts := by
  unfold bF
  iintro H
  icases bsl_filter_take (pend g) (isF M) (fun _ => false) ts (isF_of hd h1 hm) (fun _ h => by cases h) (rng M)
    (mem_rng.2 (msgAt_le (msgAt_of h1 hm))) (nodup_rng M) $$ H with ⟨Hp, -⟩
  iexact Hp

/-- **THE SETUP** (plan R-a5): hart 0's four shapes and hart 1's markers to their authors' bags, the rest dead. -/
theorem setup3 (g : AGN) (M : List PMsg) (hm : g.mn.length = M.length) :
    doomInv (GF := GF) g M ∗ ([∗list] k ↦ _x ∈ g.mn, pend g (k + 1)) ⊢
      |={⊤}=> ctx3 g M ∗ (bS g M mA ∗ bS g M mC1 ∗ bS g M mC0 ∗ bS g M mR) ∗ bF g M := by
  iintro ⟨#Hdoom, Hp⟩
  have h0 : ([∗list] k ↦ _x ∈ g.mn, pend (GF := GF) g (k + 1)) ⊢ [∗list] t ∈ rng M, pend g t := by
    have := bsl_range (pend (GF := GF) g) g.mn 1; rw [hm] at this; exact this
  ihave Hp := h0 $$ Hp
  have s1 := bsl_filter_split (pend (GF := GF) g) (shp M mA) (rng M)
  have s2 := bsl_filter_split (pend (GF := GF) g) (shp M mC1) ((rng M).filter (fun t => !shp M mA t))
  rw [filter_filter_of (r := shp M mC1) (fun t => by
      cases h : shp M mC1 t
      · simp
      · rw [shp_ne (by decide) h]; rfl)] at s2
  rw [filter_filter_of (r := fun t => !shp M mA t && !shp M mC1 t) (fun t => rfl)] at s2
  have s3 := bsl_filter_split (pend (GF := GF) g) (shp M mC0)
    ((rng M).filter (fun t => !shp M mA t && !shp M mC1 t))
  rw [filter_filter_of (r := shp M mC0) (fun t => by
      cases h : shp M mC0 t
      · simp
      · rw [shp_ne (by decide) h, shp_ne (by decide) h]; rfl)] at s3
  rw [filter_filter_of (r := fun t => !shp M mA t && !shp M mC1 t && !shp M mC0 t) (fun t => rfl)] at s3
  have s4 := bsl_filter_split (pend (GF := GF) g) (shp M mR)
    ((rng M).filter (fun t => !shp M mA t && !shp M mC1 t && !shp M mC0 t))
  rw [filter_filter_of (r := shp M mR) (fun t => by
      cases h : shp M mR t
      · simp
      · rw [shp_ne (by decide) h, shp_ne (by decide) h, shp_ne (by decide) h]; rfl)] at s4
  rw [filter_filter_of (r := fun t => !shp M mA t && !shp M mC1 t && !shp M mC0 t && !shp M mR t)
    (fun t => rfl)] at s4
  have s5 := bsl_filter_split (pend (GF := GF) g) (isF M)
    ((rng M).filter (fun t => !shp M mA t && !shp M mC1 t && !shp M mC0 t && !shp M mR t))
  have hFs : ∀ t, isF M t = true → shp M mA t = false ∧ shp M mC1 t = false ∧ shp M mC0 t = false ∧
      shp M mR t = false := by
    intro t hF
    have k : ∀ m0 : PMsg, m0.pa ≠ Fp → shp M m0 t = false := fun m0 hp => by
      cases h : shp M m0 t
      · rfl
      · rw [shp_F hp h] at hF; cases hF
    exact ⟨k _ (by decide), k _ (by decide), k _ (by decide), k _ (by decide)⟩
  rw [filter_filter_of (r := isF M) (fun t => by
      cases hF : isF M t
      · simp
      · obtain ⟨e1, e2, e3, e4⟩ := hFs t hF
        rw [e1, e2, e3, e4]; rfl)] at s5
  rw [filter_filter_of (r := isDd M) (fun t => rfl)] at s5
  ihave ⟨HA, Hp⟩ := s1 $$ Hp
  ihave ⟨HC1, Hp⟩ := s2 $$ Hp
  ihave ⟨HC0, Hp⟩ := s3 $$ Hp
  ihave ⟨HR, Hp⟩ := s4 $$ Hp
  ihave ⟨HF, Hp⟩ := s5 $$ Hp
  imod bsl_fupd (G := fun t => deadInv (GF := GF) g t) (fun t => dead_alloc g t) _ $$ Hp with #Hdd
  imodintro
  unfold ctx3 bS bF
  iframe Hdoom Hdd HA HC1 HC0 HR HF

end res

/-! ## 5. Hart 0: the lock operations -/

section hart0

variable {GF : BundledGFunctors} [GhostVarG GF HSt] [GhostVarG GF Bool] [TokenG GF] [InvGS GF]

abbrev Φ3 (g : AGN) (M : List PMsg) : Unit → IProp GF := fun _ => iprop(⌜∃ V, grd Proto.triv imgL M V True⌝ ∨ dshot g)

theorem q0 (ev : Trace) : qs3 0 ev := fun h => absurd h (by decide)

/-- Hart 0's text from `pc = k` on: every fulfil takes its `pend` from the bag of its shape. -/
theorem h0_run (g : AGN) (M : List PMsg) (s0 : LP) {P0 : GSet Nat} (hprog : s0.prog = b3o) (hpc : s0.pc = 0)
    (hq : s0.q = []) (hlen : s0.regs.length = 32) (h9 : s0.rd 9 = X) (h10 : s0.rd 10 = 0x3000) :
    (bS (GF := GF) g M mA ∗ bS g M mC1 ∗ bS g M mC0 ∗ bS g M mR) ∗
      lhA g Proto.triv (w3 M 0) (qs3 0) psInit P0 [] ⊢ wpKA g Proto.triv (w3 M 0) qs3 s0 (Φ3 g M) := by
  have hw := litW_x xs3 imgL M 0
  iintro ⟨⟨HA, HC1, HC0, HR⟩, Hl⟩
  -- `li a4,1`
  iapply (wpKA_alui hw (litAg_x hq (p3o_at hprog) (by rw [hpc]; rfl) rfl) hq (by rw [hprog, hpc]; rfl)
    (by decide))
  iframe Hl
  inext
  iintro %s1 %hs1 _ _
  imodintro
  iintro Hl
  obtain ⟨hP1, hc1, hq1⟩ := LPstep_at hs1 hprog (by rw [hpc])
  have e9 : s1.rd 9 = X := by rw [LPstep_rd hs1 9 (.inl (by decide)), h9]
  have e10 : s1.rd 10 = 0x3000 := by rw [LPstep_rd hs1 10 (.inl (by decide)), h10]
  have e14 : s1.rd 14 = 1 := li_val hs1 (by decide) (by omega) (by decide)
  -- `amoswap.w.aq a5,a4,(s1)`
  iapply (wpKA_amo (base := Lk) hw (litAg_x hq1 (p3o_at hP1) (by rw [hc1]; rfl) rfl) hq1 (by rw [hP1, hc1]; rfl)
    (by rw [e9]; decide) (by rw [e9]))
  iframe Hl
  inext
  iintro %tvs %ts %_ %_ %hmsg %_ %_ %hcoh %_ _ _
  have hd1 : amoD .swap 4 (s1.rd 14) tvs = toBytes 1 4 := by rw [amoD_swap, e14]
  rw [hd1] at hmsg hcoh
  have hts1 : 1 ≤ ts := by
    have := cohBelow_at (j := 0) hcoh (by decide); omega
  ihave Hp := bS_take g M mA hts1 hmsg $$ HA
  imod shoot $$ Hp with #Hsh
  imodintro
  isplitr
  · ileft; ipureintro; exact ⟨⟨0, grd_intro (q0 _)⟩, grd_intro trivial⟩
  isplitr
  · unfold fulT; ileft; iexact Hsh
  iintro %s2 %hs2 _ _
  imodintro
  iintro Hl
  obtain ⟨hP2, hc2, hq2⟩ := LPstep_at hs2 hP1 (by rw [hc1])
  have f9 : s2.rd 9 = X := by rw [LPstep_rd hs2 9 (.inl (by decide)), e9]
  have f10 : s2.rd 10 = 0x3000 := by rw [LPstep_rd hs2 10 (.inl (by decide)), e10]
  -- `sd a0,16(s1)`
  iapply (wpKA_sw (sz := 8) (rs2 := 10) (rs1 := 9) (off := 16) (base := Pc) hw
    (litAg_x hq2 (p3o_at hP2) (by rw [hc2]; rfl) rfl) hq2 (by rw [hP2, hc2]; rfl) (alg_pc f9) (base_pc f9))
  iframe Hl
  inext
  iintro %t1 %_ %hmsg1 %hcoh1 %_ _ _
  rw [f10] at hmsg1
  have ht1 : 1 ≤ t1 := by have := cohBelow_at (j := 0) hcoh1 (by rw [toBytes_length]; decide); omega
  ihave Hp := bS_take g M mC1 ht1 hmsg1 $$ HC1
  imod shoot $$ Hp with #Hsh1
  imodintro
  isplitr
  · ileft; ipureintro; exact ⟨⟨0, grd_intro (q0 _)⟩, grd_intro trivial⟩
  isplitr
  · unfold fulT; ileft; iexact Hsh1
  iintro %s3 %hs3 _ _
  imodintro
  iintro Hl
  obtain ⟨hP3, hc3, hq3⟩ := LPstep_at hs3 hP2 (by rw [hc2])
  have g9 : s3.rd 9 = X := by rw [LPstep_rd hs3 9 (.inr rfl), f9]
  -- `sd zero,16(s1)`
  iapply (wpKA_sw (sz := 8) (rs2 := 0) (rs1 := 9) (off := 16) (base := Pc) hw
    (litAg_x hq3 (p3o_at hP3) (by rw [hc3]; rfl) rfl) hq3 (by rw [hP3, hc3]; rfl) (alg_pc g9) (base_pc g9))
  iframe Hl
  inext
  iintro %t2 %_ %hmsg2 %hcoh2 %_ _ _
  have ht2 : 1 ≤ t2 := by have := cohBelow_at (j := 0) hcoh2 (by rw [toBytes_length]; decide); omega
  ihave Hp := bS_take g M mC0 ht2 hmsg2 $$ HC0
  imod shoot $$ Hp with #Hsh2
  imodintro
  isplitr
  · ileft; ipureintro; exact ⟨⟨0, grd_intro (q0 _)⟩, grd_intro trivial⟩
  isplitr
  · unfold fulT; ileft; iexact Hsh2
  iintro %s4 %hs4 _ _
  imodintro
  iintro Hl
  obtain ⟨hP4, hc4, hq4⟩ := LPstep_at hs4 hP3 (by rw [hc3])
  have k9 : s4.rd 9 = X := by rw [LPstep_rd hs4 9 (.inr rfl), g9]
  -- `fence rw,w`
  iapply (wpKA_fence hw (litAg_x hq4 (p3o_at hP4) (by rw [hc4]; rfl) rfl) hq4 (by rw [hP4, hc4]; rfl))
  iframe Hl
  inext
  iintro %s5 %hs5 _ _
  imodintro
  iintro Hl
  obtain ⟨hP5, hc5, hq5⟩ := LPstep_at hs5 hP4 (by rw [hc4])
  have l9 : s5.rd 9 = X := by rw [LPstep_rd hs5 9 (.inr rfl), k9]
  -- `sw zero,0(s1)`
  iapply (wpKA_sw (sz := 4) (rs2 := 0) (rs1 := 9) (off := 0) (base := Lk) hw
    (litAg_x hq5 (p3o_at hP5) (by rw [hc5]; rfl) rfl) hq5 (by rw [hP5, hc5]; rfl)
    (alg_of l9 (by decide) (by decide)) (base_of l9 (by decide)))
  iframe Hl
  inext
  iintro %t3 %_ %hmsg3 %hcoh3 %_ _ _
  have ht3 : 1 ≤ t3 := by have := cohBelow_at (j := 0) hcoh3 (by rw [toBytes_length]; decide); omega
  ihave Hp := bS_take g M mR ht3 hmsg3 $$ HR
  imod shoot $$ Hp with #Hsh3
  imodintro
  isplitr
  · ileft; ipureintro; exact ⟨⟨0, grd_intro (q0 _)⟩, grd_intro trivial⟩
  isplitr
  · unfold fulT; ileft; iexact Hsh3
  iintro %s6 %hs6 _ _
  imodintro
  iintro Hl
  obtain ⟨hP6, hc6, hq6⟩ := LPstep_at hs6 hP5 (by rw [hc5])
  have hend : s6.prog.length ≤ s6.pc := by rw [hP6, hc6]; decide
  iapply (wpKA_end (v := ()) (litAg_xn hq6 (fun x hx => by rw [p3o_at hP6, hc6] at hx; cases hx)) hq6 hend
    (by show litDone s6 = some (); unfold litDone; rw [if_pos ⟨hq6, hend⟩]))
  iframe Hl
  imodintro
  ileft; ipureintro; exact ⟨0, grd_intro trivial⟩

end hart0

/-! ## 6. Hart 1: `holding()` and the panic test -/

section hart1

variable {GF : BundledGFunctors} [GhostVarG GF HSt] [GhostVarG GF Bool] [TokenG GF] [InvGS GF]

theorem ld_nonF (b : Int) (tvs : List (Nat × BitVec 8)) (a : List Dsrc) :
    ∀ d a' b' ts, (LLoad false false b tvs a, (none : Option Nat)) ≠ (LStore false false Fp d a' b', some ts) :=
  fun _ _ _ _ h => by cases h

/-- `pc = 7`: the end. -/
theorem h1_end (g : AGN) (M : List PMsg) (s : LP) (ws : PState) (pr : GSet Nat) (ev : Trace)
    (hprog : s.prog = b3h) (hq : s.q = []) (hpc : s.pc = 7) :
    lhA (GF := GF) g Proto.triv (w3 M 1) (qs3 1) ws pr ev ∗ (⌜∃ V, grd Proto.triv imgL M V True⌝ ∨ dshot g) ⊢
      wpKA g Proto.triv (w3 M 1) qs3 s (Φ3 g M) := by
  iintro ⟨Hl, Hr⟩
  have hend : s.prog.length ≤ s.pc := by rw [hprog, hpc]; decide
  iapply (wpKA_end (v := ()) (litAg_xn hq (fun x hx => by rw [p3h_at hprog, hpc] at hx; cases hx)) hq hend
    (by show litDone s = some (); unfold litDone; rw [if_pos ⟨hq, hend⟩]))
  iframe Hl
  imodintro
  iexact Hr

/-- `pc = 3..7` after a DEAD read (doomed): the rest of the text, the marker store from hart 1's bag. -/
theorem h1_doomed (g : AGN) (M : List PMsg) (s : LP) (ws : PState) (pr : GSet Nat) (ev : Trace)
    (hprog : s.prog = b3h) (hq : s.q = []) (hpc : s.pc = 3) (h12 : s.rd 12 = 0x4000) :
    dshot (GF := GF) g ∗ bF g M ∗ lhA g Proto.triv (w3 M 1) (qs3 1) ws pr ev ⊢
      wpKA g Proto.triv (w3 M 1) qs3 s (Φ3 g M) := by
  have hw := litW_x xs3 imgL M 1
  iintro ⟨#Hd, HF, Hl⟩
  iapply (wpKA_alu hw (litAg_x hq (p3h_at hprog) (by rw [hpc]; rfl) rfl) hq (by rw [hprog, hpc]; rfl) (by decide))
  iframe Hl
  inext
  iintro %s1 %hs1 _ _
  imodintro
  iintro Hl
  obtain ⟨hP1, hc1, hq1⟩ := LPstep_at hs1 hprog (by rw [hpc])
  iapply (wpKA_alui hw (litAg_x hq1 (p3h_at hP1) (by rw [hc1]; rfl) rfl) hq1 (by rw [hP1, hc1]; rfl) (by decide))
  iframe Hl
  inext
  iintro %s2 %hs2 _ _
  imodintro
  iintro Hl
  obtain ⟨hP2, hc2, hq2⟩ := LPstep_at hs2 hP1 (by rw [hc1])
  have e12 : s2.rd 12 = 0x4000 := by
    rw [LPstep_rd hs2 12 (.inl (by decide)), LPstep_rd hs1 12 (.inl (by decide)), h12]
  iapply (wpKA_brx (Xs := xs3) hw (xAg_x xs3 imgL M 1 s2) hq2 (p3h_at hP2) (by rw [hc2]; rfl)
    (by rw [hP2]; decide))
  iframe Hl
  inext
  iintro %s3 %hs3 _ _
  imodintro
  iintro Hl
  by_cases hb : Weak.Prom.Ref.brEval .eq (s2.rd 13) (s2.rd 0) = true
  · rw [if_pos hb] at hs3
    obtain ⟨hP3, hc3, hq3⟩ := LPstep_at hs3 hP2 rfl
    iapply (h1_end g M s3 _ _ _ hP3 hq3 hc3)
    iframe Hl; iright; iexact Hd
  · rw [if_neg hb] at hs3
    obtain ⟨hP3, hc3, hq3⟩ := LPstep_at hs3 hP2 (by rw [hc2])
    have f12 : s3.rd 12 = 0x4000 := by rw [LPstep_rd hs3 12 (.inr rfl), e12]
    -- the marker store (reachable only when doomed)
    iapply (wpKA_sw (sz := 8) (rs2 := 10) (rs1 := 12) (off := 0) (base := Fp) hw
      (litAg_x hq3 (p3h_at hP3) (by rw [hc3]; rfl) rfl) hq3 (by rw [hP3, hc3]; rfl)
      (alg_of f12 (by decide) (by decide)) (base_of f12 (by decide)))
    iframe Hl
    inext
    iintro %tf %_ %hmsg %hcoh %_ _ _
    rw [toBytes_length] at hcoh
    have htf : 1 ≤ tf := by have := cohBelow_at (j := 0) hcoh (by decide); omega
    ihave Hp := bF_take g M (toBytes_length _ _) htf hmsg $$ HF
    imod shoot $$ Hp with #Hsh
    imodintro
    isplitr
    · iright; iexact Hd
    isplitr
    · unfold fulT; ileft; iexact Hsh
    iintro %s4 %hs4 _ _
    imodintro
    iintro Hl
    obtain ⟨hP4, hc4, hq4⟩ := LPstep_at hs4 hP3 (by rw [hc3])
    iapply (h1_end g M s4 _ _ _ hP4 hq4 hc4)
    iframe Hl; iright; iexact Hd

/-- **HART 1**: `holding()` reads the lock word and the cpu field racily; acquire's panic branch is not taken. -/
theorem h1_run (g : AGN) (M : List PMsg) (hdd : g.dd = ddL M) (s0 : LP) {P0 : GSet Nat} (hprog : s0.prog = b3h)
    (hpc : s0.pc = 0) (hq : s0.q = []) (hlen : s0.regs.length = 32) (h9 : s0.rd 9 = X)
    (h10 : s0.rd 10 = 0x3100) (h12 : s0.rd 12 = 0x4000) :
    ctx3 (GF := GF) g M ∗ bF g M ∗ lhA g Proto.triv (w3 M 1) (qs3 1) psInit P0 [] ⊢
      wpKA g Proto.triv (w3 M 1) qs3 s0 (Φ3 g M) := by
  have hw := litW_x xs3 imgL M 1
  iintro ⟨#Hctx, HF, Hl⟩
  -- `lw a5,0(s1)`: the racy read of the lock word (any value)
  iapply (wpKA_ld (sz := 4) (sgn := true) (rd := 15) (rs1 := 9) (off := 0) (base := Lk) hw
    (litAg_x hq (p3h_at hprog) (by rw [hpc]; rfl) rfl) hq (by rw [hprog, hpc]; rfl)
    (alg_of h9 (by decide) (by decide)) (base_of h9 (by decide)))
  iframe Hl
  inext
  iintro %tvs0 %_ %_ _ _
  imodintro
  isplitr
  · ileft; ipureintro; exact ⟨0, grd_intro (fun _ => noF_snoc noF_nil (ld_nonF _ _ _))⟩
  iintro %s1 %hs1 _ _
  imodintro
  iintro Hl
  obtain ⟨hP1, hc1, hq1⟩ := LPstep_at hs1 hprog (by rw [hpc])
  have e9 : s1.rd 9 = X := by rw [LPstep_rd hs1 9 (.inl (by decide)), h9]
  have e10 : s1.rd 10 = 0x3100 := by rw [LPstep_rd hs1 10 (.inl (by decide)), h10]
  have e12 : s1.rd 12 = 0x4000 := by rw [LPstep_rd hs1 12 (.inl (by decide)), h12]
  have hlen1 : s1.regs.length = 32 := hs1.2.2.2.1.trans hlen
  -- `beqz a5,7`: the first branch on a racy value
  iapply (wpKA_brx (Xs := xs3) hw (xAg_x xs3 imgL M 1 s1) hq1 (p3h_at hP1) (by rw [hc1]; rfl)
    (by rw [hP1]; decide))
  iframe Hl
  inext
  iintro %s2 %hs2 _ _
  imodintro
  iintro Hl
  by_cases hb : Weak.Prom.Ref.brEval .eq (s1.rd 15) (s1.rd 0) = true
  · -- `holding()` = 0 at once (the lock word read 0)
    rw [if_pos hb] at hs2
    obtain ⟨hP2, hc2, hq2⟩ := LPstep_at hs2 hP1 rfl
    iapply (h1_end g M s2 _ _ _ hP2 hq2 hc2)
    iframe Hl; ileft; ipureintro; exact ⟨0, grd_intro trivial⟩
  rw [if_neg hb] at hs2
  obtain ⟨hP2, hc2, hq2⟩ := LPstep_at hs2 hP1 (by rw [hc1])
  have f9 : s2.rd 9 = X := by rw [LPstep_rd hs2 9 (.inr rfl), e9]
  have f10 : s2.rd 10 = 0x3100 := by rw [LPstep_rd hs2 10 (.inr rfl), e10]
  have f12 : s2.rd 12 = 0x4000 := by rw [LPstep_rd hs2 12 (.inr rfl), e12]
  have hlen2 : s2.regs.length = 32 := hs2.2.2.2.1.trans hlen1
  -- `ld a5,16(s1)`: THE RACY READ OF THE CPU FIELD
  iapply (wpKA_ld (sz := 8) (sgn := true) (rd := 15) (rs1 := 9) (off := 16) (base := Pc) hw
    (litAg_x hq2 (p3h_at hP2) (by rw [hc2]; rfl) rfl) hq2 (by rw [hP2, hc2]; rfl) (alg_pc f9) (base_pc f9))
  iframe Hl
  inext
  iintro %tvs %hl8 %hlo _ _
  have hrd := pc_read hl8 (fun j t v hg => (bytesAll_get (loadOk_weak hlo) hg).1)
  imodintro
  isplitr
  · ileft; ipureintro; exact ⟨0, grd_intro (fun _ => noF_snoc (noF_snoc noF_nil (ld_nonF _ _ _)) (ld_nonF _ _ _))⟩
  iintro %s3 %hs3 _ _
  obtain ⟨hP3, hc3, hq3⟩ := LPstep_at hs3 hP2 (by rw [hc2])
  have g12 : s3.rd 12 = 0x4000 := by rw [LPstep_rd hs3 12 (.inl (by decide)), f12]
  have g10 : s3.rd 10 = 0x3100 := by rw [LPstep_rd hs3 10 (.inl (by decide)), f10]
  have g15 := LPstep_rd_eq hs3 (by decide) (by omega)
  have hlen3 : s3.regs.length = 32 := hs3.2.2.2.1.trans hlen2
  rcases hrd with hv | ⟨t, ht1, htM, hD⟩
  rotate_left
  · -- a DEAD message: doom (free mode), no frontier needed
    unfold ctx3
    icases Hctx with ⟨Hdoom, Hdd⟩
    ihave #Hdi := bsl_mem (F := fun t => deadInv g t) (List.mem_filter.2 ⟨mem_rng.2 ⟨ht1, htM⟩, hD⟩) $$ Hdd
    imod dead_doom g M t ⟨ht1, htM⟩ (by rw [hdd]; exact ⟨ht1, hD⟩) $$ [] with ⟨-, #Hd⟩
    · iframe Hdoom Hdi
    imodintro
    iintro Hl
    iapply (h1_doomed g M s3 _ _ _ hP3 hq3 hc3 g12)
    iframe Hd HF Hl
  imodintro
  iintro Hl
  -- the value is `0` or `0x3000`: `sub`, `seqz` give `0`, `beqz` skips the panic
  have v15 : s3.rd 15 = 0 ∨ s3.rd 15 = 0x3000 := by
    rw [g15]; rcases hv with h | h <;> rw [h] <;> decide
  iapply (wpKA_alu hw (litAg_x hq3 (p3h_at hP3) (by rw [hc3]; rfl) rfl) hq3 (by rw [hP3, hc3]; rfl) (by decide))
  iframe Hl
  inext
  iintro %s4 %hs4 _ _
  imodintro
  iintro Hl
  obtain ⟨hP4, hc4, hq4⟩ := LPstep_at hs4 hP3 (by rw [hc3])
  have v13 : s4.rd 13 ≠ 0 := by
    rw [LPstep_rd_eq hs4 (by decide) (by omega), g10]
    rcases v15 with h | h <;> rw [h] <;> decide
  have hlen4 : s4.regs.length = 32 := hs4.2.2.2.1.trans hlen3
  iapply (wpKA_alui hw (litAg_x hq4 (p3h_at hP4) (by rw [hc4]; rfl) rfl) hq4 (by rw [hP4, hc4]; rfl) (by decide))
  iframe Hl
  inext
  iintro %s5 %hs5 _ _
  imodintro
  iintro Hl
  obtain ⟨hP5, hc5, hq5⟩ := LPstep_at hs5 hP4 (by rw [hc4])
  have v13' : s5.rd 13 = 0 := by
    rw [LPstep_rd_eq hs5 (by decide) (by omega)]
    simp only [aluOp]
    rw [if_neg (by omega)]; rfl
  iapply (wpKA_brx (Xs := xs3) hw (xAg_x xs3 imgL M 1 s5) hq5 (p3h_at hP5) (by rw [hc5]; rfl)
    (by rw [hP5]; decide))
  iframe Hl
  inext
  iintro %s6 %hs6 _ _
  imodintro
  iintro Hl
  have hbr : (if Weak.Prom.Ref.brEval .eq (s5.rd 13) (s5.rd 0) then 7 else s5.pc + 1) = 7 := by
    rw [v13']; rfl
  rw [hbr] at hs6
  obtain ⟨hP6, hc6, hq6⟩ := LPstep_at hs6 hP5 rfl
  iapply (h1_end g M s6 _ _ _ hP6 hq6 hc6)
  iframe Hl; ileft; ipureintro; exact ⟨0, grd_intro trivial⟩

end hart1

/-! ## 7. The verdict -/

theorem progs_3 : ∃ p0 p1 : LP, progs t3 = [p0, p1] := ⟨_, _, rfl⟩

/-- THE ADEQUACY PREMISE for (3). -/
theorem premise3 (M : List PMsg) :
    wpPremise .hasLC ownGF (xStep xs3) litDone imgL M (progs t3) Proto.triv (fun _ _ => True)
      (fun h => ΨK M (qs3 h)) (ddL M) := by
  intro Hinv g P0 hn hm hdd hP0
  obtain ⟨p0, p1, hps⟩ := progs_3
  have hg0 : (progs t3)[0]? = some p0 := by rw [hps]; rfl
  have hg1 : (progs t3)[1]? = some p1 := by rw [hps]; rfl
  obtain ⟨hpr0, hpc0, hq0, hl0, hrd0⟩ := progs_get hg0
  obtain ⟨hpr1, hpc1, hq1, hl1, hrd1⟩ := progs_get hg1
  have hlen : g.hn.length = 2 := by rw [hn, hps]; rfl
  obtain ⟨γ0, γ1, hgn⟩ : ∃ a b, g.hn = [a, b] := by
    match h : g.hn, hlen with
    | [a, b], _ => exact ⟨a, b, rfl⟩
  rw [hps]
  iintro #Hdoom Hh Hp
  imod setup3 g M hm $$ [Hp] with ⟨#Hctx, Hb0, HF⟩
  · iframe Hdoom Hp
  have k0 := h0_run (GF := ownGF) g M p0 (P0 := P0 0) hpr0 hpc0 hq0 hl0
    (by rw [hrd0 9 (by decide) (by decide)]; rfl) (by rw [hrd0 10 (by decide) (by decide)]; rfl)
  have k1 := h1_run (GF := ownGF) g M hdd p1 (P0 := P0 1) hpr1 hpc1 hq1 hl1
    (by rw [hrd1 9 (by decide) (by decide)]; rfl) (by rw [hrd1 10 (by decide) (by decide)]; rfl)
    (by rw [hrd1 12 (by decide) (by decide)]; rfl)
  have k0' : (bS (GF := ownGF) g M mA ∗ bS g M mC1 ∗ bS g M mC0 ∗ bS g M mR) ∗
      lhA g Proto.triv (w3 M 0) (qs3 0) psInit (P0 0) [] ⊢
      wpA (hlc := .hasLC) g Proto.triv (hw (xStep xs3) litDone imgL M 0) (fun h => ΨK M (qs3 h)) p0
        (fun v => iprop(⌜∃ V, grd Proto.triv imgL M V ((fun (_ : Nat) (_ : Unit) => True) 0 v)⌝ ∨ dshot g)) := k0
  have k1' : ctx3 (GF := ownGF) g M ∗ bF g M ∗ lhA g Proto.triv (w3 M 1) (qs3 1) psInit (P0 1) [] ⊢
      wpA (hlc := .hasLC) g Proto.triv (hw (xStep xs3) litDone imgL M (0 + 1)) (fun h => ΨK M (qs3 h)) p1
        (fun v => iprop(⌜∃ V, grd Proto.triv imgL M V ((fun (_ : Nat) (_ : Unit) => True) (0 + 1) v)⌝ ∨
          dshot g)) := k1
  rw [hgn]
  icases (BigSepL.bigSepL_cons).1 $$ Hh with ⟨H0, Hh⟩
  icases (BigSepL.bigSepL_cons).1 $$ Hh with ⟨H1, -⟩
  imodintro
  have s0 := lhA_start (GF := ownGF) (g := g) (π := Proto.triv) (w := w3 M 0) (Qs := qs3) (P0 := P0 0) (q0 [])
  have s1 := lhA_start (GF := ownGF) (g := g) (π := Proto.triv) (w := w3 M 1) (Qs := qs3) (P0 := P0 (0 + 1))
    (fun _ => noF_nil)
  iapply (BigSepL.bigSepL_cons).2
  isplitl [H0 Hb0]
  · iapply k0'
    iframe Hb0
    iapply s0
    iexact H0
  iapply (BigSepL.bigSepL_cons).2
  isplitl [H1 HF]
  · iapply k1'
    iframe Hctx HF
    iapply s1
    iexact H1
  iapply (BigSepL.bigSepL_nil).2
  itrivial

/-- **G4 TARGET (3) ON TRACK (a): A `holding()`-SHAPED RACY READ THAT DRIVES A BRANCH** (plan §4 G4 (3)).  Over
every final memory `M` and every valid run of machine v2 of the test `t3` (hart 0: xv6's acquire/release lock
operations, writing the lock word and the cpu field; hart 1: xv6's `holding()` — racy `lw` of the lock word driving
`beqz`, racy `ld` of the cpu field driving `sub; seqz; beqz` — and acquire's panic test), hart 1 never executes the
panic store: `holding()` returns 0 in `acquire` of a hart that does not hold the lock, whatever the racing hart
writes.  0 named inputs; loop-free.  See the header for why the frontier rule is not needed here. -/
theorem own_hold (M : List PMsg) (run : PFRun LP Unit)
    (hrun : PF.validRun (xStep xs3) imgL () (progs t3) M run) : noF (run.trace 1) := by
  obtain ⟨_, hΨ, _⟩ := adequacyA (hlc := .hasLC) (GF := ownGF) Proto.triv (fun _ _ => True)
    (fun h => ΨK M (qs3 h)) (ddL M) trivial (fun h => ⟨fun _ => noF_nil, wrOk_nil M⟩) (premise3 M) hrun
  have hq := (hΨ 1 (run.trace 1).length).1
  rw [List.take_length] at hq
  exact noF_of_memEv (hq rfl)

#print axioms own_hold

end Weak.Prom.OA.H
