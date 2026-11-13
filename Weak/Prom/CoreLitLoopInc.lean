/-
Weak/Prom: **MP FOREVER WITH A COUNTER — the program, the trace property, and the pure glue** (owner request
2026-11-13: "Can we modify the lit_mpLoop program to increment t1 at the hart 0's loop?" … "We can do a wrapping
add" … "Just to make the trace property better"; plan rev 7 §2 "Leaf rules", "Adequacy A0", §5 row 8 per iteration).

The program `tLoopInc` is CoreLitLoop's `tLoop` with ONE change, hart 0 increments t1 (x6) every iteration
(`addi` = RefTests.lean:40 `.alui .add`, `aluOp .add a b = (a + b) % 2^64`; `sw` stores the low 32 bits):
  hart 0:  0: sw t1,0(a2)  1: fence w,w  2: sw t1,0(a3)  3: addi t1,t1,1  4: beq zero,zero,0     (t1 = 1 initially)
  hart 1:  0: lw a0,0(a3)  1: fence r,r  2: lw a1,0(a2)  3: beq zero,zero,0                      (unchanged)
Iteration `i` of hart 0 holds `t1 = rv i = (1 + i) mod 2^64` and stores the word `wv i = (1 + i) mod 2^32`.

The property `qLoopInc M τ` (over the FINAL memory `M`): for every flag load immediately followed (among the memory
entries) by a data load, if the flag load's byte 0 read a message (not the initial 0), then the data load's byte 0
read a message too, both are flag/data messages, the flag load returned `wv k` and the data load `wv k'`, where `k`
(`k'`) is the INDEX of the message read — the number of flag (data) messages below it in `M` — and `k ≤ k'`.
The index is defined from `M` alone (`idxOf`); that it is hart 0's iteration number is proved (`idx_at`, `idx_par`).
This file: the program, the hart Ψs (`Q0`, `Q1`), the property, and the A0-export glue (`reader_ok`).  The harts'
Löb proofs and the theorems are in CoreLitLoopIncH.lean.  No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Prom.CoreLitLoop

namespace Weak.Prom.PF.LoopInc

open MachCSL MachCSL.Stdpp Iris.Std
open Weak (Image Dsrc)
open Weak.Prom Weak.Prom.PF Weak.Prom.Mach Weak.Prom.Mach.Cert
open Weak.Prom.OA (XI xNext xStep xW xOf)
open Weak.Prom.Ref (Instr Test two64 brEval aluOp)
open Weak.Prom.Ref.Lit (X Y)
open Weak.Prom.PF.Loop (adj adj_snoc ldRet ldF ldD ldF_D)
open PLabel

/-! ## 1. The program -/

/-- Hart 0: `sw t1,0(a2); fence w,w; sw t1,0(a3); addi t1,t1,1; beq zero,zero,0`. -/
def pI0 : List XI :=
  [.i (Weak.Prom.Ref.Lit.sw 6 12), .i Weak.Prom.Ref.Lit.fWW, .i (Weak.Prom.Ref.Lit.sw 6 13),
   .i (Weak.Prom.Ref.Lit.addi 6 6 1), .i (Weak.Prom.Ref.Lit.beq 0 0 0)]

abbrev bI0 : List Instr := pI0.map XI.base
abbrev xsLoopInc : List (List XI) := [pI0, Loop.pL1]

/-- THE TEST: two harts, image all zero; hart 1 is CoreLitLoop's. -/
def tLoopInc : Test :=
  { harts := [bI0, Loop.bL1]
    regs0 := [[(6, 1), (12, X), (13, Y)], [(12, X), (13, Y)]]
    img := []
    cond := Weak.Prom.Ref.Lit.mpFF.cond }

abbrev imgLoopInc : Image := testImg tLoopInc

theorem xOf_I0 : xOf xsLoopInc bI0 = some pI0 := by decide
theorem xOf_I1 : xOf xsLoopInc Loop.bL1 = some Loop.pL1 := by decide

/-! ## 2. Values (the wrapping add) -/

/-- t1 in iteration `i` (64-bit wrapping add). -/
def rv (i : Nat) : Nat := (1 + i) % two64

/-- The word iteration `i` stores (`sw`: the low 32 bits of t1). -/
def wv (i : Nat) : Nat := (1 + i) % 2 ^ 32

theorem addi_rv (i : Nat) : aluOp .add (rv i) 1 % two64 = rv (i + 1) := by
  show ((1 + i) % two64 + 1) % two64 % two64 = (1 + (i + 1)) % two64
  rw [Nat.mod_mod, Nat.mod_add_mod, show 1 + i + 1 = 1 + (i + 1) by omega]

theorem rv_wv (i : Nat) : rv i % 2 ^ 32 = wv i := by
  unfold rv wv two64
  exact Nat.mod_mod_of_dvd _ ⟨2 ^ 32, by decide⟩

/-- `toBytes w 4`, spelled out. -/
theorem toBytes4 (w : Nat) :
    toBytes w 4 = [bv8 (w % 256), bv8 ((w >>> 8) % 256), bv8 ((w >>> 16) % 256), bv8 ((w >>> 24) % 256)] := rfl

/-- The value of a word read from `toBytes w 4`: `w mod 2^32`. -/
theorem obs4 (w t0 t1 t2 t3 : Nat) :
    obsOf [(t0, bv8 (w % 256)), (t1, bv8 ((w >>> 8) % 256)), (t2, bv8 ((w >>> 16) % 256)),
      (t3, bv8 ((w >>> 24) % 256))] = w % 2 ^ 32 := by
  simp only [obsOf, List.foldr_cons, List.foldr_nil, bv8, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow,
    Nat.reducePow]
  omega

/-! ## 3. The hart Ψs -/

/-- Iteration `i`'s data store (the word `toBytes (rv i) 4` at DATA). -/
def stD (i : Nat) (e : PEv) : Prop := isSt (X : Int) (toBytes (rv i) 4) [.DReg 12] [.DReg 6] e

/-- Iteration `i`'s flag store. -/
def stF (i : Nat) (e : PEv) : Prop := isSt (Y : Int) (toBytes (rv i) 4) [.DReg 13] [.DReg 6] e

/-- Entry `j` of hart 0's memory entries: iteration `j / 2`'s data store (even `j`) or flag store (odd `j`). -/
def sh0 (j : Nat) (e : PEv) : Prop := (j % 2 = 0 → stD (j / 2) e) ∧ (j % 2 = 1 → stF (j / 2) e)

/-- **Hart 0's Ψ**: its memory entries are `D 0, F 0, D 1, F 1, …` (`sh0`); same-address stores (same parity) are
timestamp-increasing in program order (coherence, rule 1; through the fence w,w of each iteration); iteration `i`'s
data store is below its flag store (fence w,w, rule 4). -/
def Q0 (ev : Trace) : Prop :=
  (∀ j e, ev[j]? = some e → sh0 j e) ∧
  (∀ j j' e e', ev[j]? = some e → ev[j']? = some e' → j < j' → j % 2 = j' % 2 → tsOf e < tsOf e') ∧
  (∀ j e e', ev[2 * j]? = some e → ev[2 * j + 1]? = some e' → tsOf e < tsOf e')

/-- Single-copy atomicity of a load (machine v2's M9 common read point, `loadOk`): no write to any byte of the run
between that byte's source and the max source. -/
def scaP (M : List PMsg) (base : Int) (tvs : List (Nat × BitVec 8)) : Prop :=
  bytesAll (fun a t _ => ¬ writesIn M a t (bytesMax (fun _ t => t) base tvs)) base tvs

/-- A flag load (with its single-copy-atomicity fact). -/
def ldFs (M : List PMsg) (e : PEv) : Prop :=
  ∃ tvs, e = (LLoad false false (Y : Int) tvs (srcR 13), none) ∧ tvs.length = 4 ∧ (noCmo M → scaP M Y tvs)

/-- A data load (with its single-copy-atomicity fact). -/
def ldDs (M : List PMsg) (e : PEv) : Prop :=
  ∃ tvs, e = (LLoad false false (X : Int) tvs (srcR 12), none) ∧ tvs.length = 4 ∧ (noCmo M → scaP M X tvs)

/-- **Hart 1's Ψ**: every memory entry is a flag or a data load (each single-copy atomic); a data load right after a
flag load sees no write to the data between its byte-0 source and the flag load's (fence r,r, rule 4). -/
def Q1 (M : List PMsg) (ev : Trace) : Prop :=
  (∀ e ∈ ev, ldFs M e ∨ ldDs M e) ∧
    adj (fun e0 e1 => ldF e0 → ldD e1 → noCmo M → ¬ writesIn M (X : Int) (src0 e1) (src0 e0)) ev

def Qs (M : List PMsg) : Nat → Trace → Prop
  | 0 => Q0
  | 1 => Q1 M
  | _ => q0

theorem Q0_nil : Q0 [] :=
  ⟨fun _ _ h => by simp at h, fun _ _ _ _ h => by simp at h, fun _ _ _ h => by simp at h⟩

theorem Q1_nil (M : List PMsg) : Q1 M [] := ⟨fun _ he => (by cases he), fun _ _ _ h => (by simp at h)⟩

theorem Qs_nil (M : List PMsg) : ∀ h, Qs M h []
  | 0 => Q0_nil
  | 1 => Q1_nil M
  | _ + 2 => rfl

theorem get_snoc {ev : Trace} {e x : PEv} {j : Nat} (h : (ev ++ [e])[j]? = some x) :
    (j < ev.length ∧ ev[j]? = some x) ∨ (j = ev.length ∧ x = e) := by
  by_cases hj : j < ev.length
  · rw [List.getElem?_append_left hj] at h; exact .inl ⟨hj, h⟩
  · rw [List.getElem?_append_right (by omega)] at h
    have hl := (List.getElem?_eq_some_iff.1 h).1
    simp only [List.length_singleton] at hl
    rw [show j - ev.length = 0 by omega] at h
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    exact .inr ⟨by omega, h.symm⟩

theorem sh0_even {i : Nat} {e : PEv} (h : stD i e) : sh0 (2 * i) e :=
  ⟨fun _ => by rw [show 2 * i / 2 = i by omega]; exact h, fun h' => absurd h' (by omega)⟩

theorem sh0_odd {i : Nat} {e : PEv} (h : stF i e) : sh0 (2 * i + 1) e :=
  ⟨fun h' => absurd h' (by omega), fun _ => by rw [show (2 * i + 1) / 2 = i by omega]; exact h⟩

theorem Q0_snoc {ev : Trace} {e : PEv} (h : Q0 ev) (hs : sh0 ev.length e)
    (hm : ∀ j e', ev[j]? = some e' → j % 2 = ev.length % 2 → tsOf e' < tsOf e)
    (hp : ∀ e', ev.length % 2 = 1 → ev[ev.length - 1]? = some e' → tsOf e' < tsOf e) : Q0 (ev ++ [e]) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨fun j x hx => ?_, fun j j' x x' hx hx' hjj hpar => ?_, fun j x x' hx hx' => ?_⟩
  · rcases get_snoc hx with ⟨_, hx⟩ | ⟨rfl, rfl⟩
    · exact h1 j x hx
    · exact hs
  · rcases get_snoc hx' with ⟨hj', hx'⟩ | ⟨rfl, rfl⟩
    · rw [List.getElem?_append_left (by omega)] at hx
      exact h2 j j' x x' hx hx' hjj hpar
    · rw [List.getElem?_append_left hjj] at hx
      exact hm j x hx hpar
  · rcases get_snoc hx' with ⟨hj', hx'⟩ | ⟨hj', rfl⟩
    · rw [List.getElem?_append_left (by omega)] at hx
      exact h3 j x x' hx hx'
    · rw [List.getElem?_append_left (by omega)] at hx
      exact hp x (by omega) (by rw [show ev.length - 1 = 2 * j by omega]; exact hx)

/-! ## 4. The property -/

/-- **The index of a message** at address `a` and timestamp `t`: the number of messages to `a` below `t` in the final
memory (timestamps `1 … t - 1` are `M[0] … M[t - 2]`). -/
def idxOf (a : Int) (M : List PMsg) (t : Nat) : Nat := ((M.take (t - 1)).filter (fun m => decide (m.pa = a))).length

/-- Timestamp `t` is a message to `a`. -/
def msgAtA (M : List PMsg) (a : Int) (t : Nat) : Prop := ∃ m, M[t - 1]? = some m ∧ m.pa = a

/-- **THE PROPERTY**: among the memory entries of `τ`, for every flag load `e0` immediately followed by a data load
`e1`: if `e0`'s byte 0 read a message (`src0 e0 ≠ 0`; a flag load that reads the initial 0 constrains nothing),
then `e1`'s byte 0 read a message too, they are a flag and a data message, `e0` returned `wv k` and `e1` returned
`wv k'` with `k` (`k'`) the index of the flag (data) message read, and `k ≤ k'`. -/
def qLoopInc (M : List PMsg) (τ : Trace) : Prop :=
  ∀ i e0 e1 v0 v1, (memEv τ)[i]? = some e0 → (memEv τ)[i + 1]? = some e1 →
    ldRet (Y : Int) e0 = some v0 → ldRet (X : Int) e1 = some v1 → src0 e0 ≠ 0 →
    src0 e1 ≠ 0 ∧ msgAtA M Y (src0 e0) ∧ msgAtA M X (src0 e1) ∧
      v0 = wv (idxOf Y M (src0 e0)) ∧ v1 = wv (idxOf X M (src0 e1)) ∧ idxOf Y M (src0 e0) ≤ idxOf X M (src0 e1)

/-- **The value form**: the data load returned the flag load's value plus the index distance, mod `2^32`. -/
theorem qLoopInc_val {M : List PMsg} {τ : Trace} (hq : qLoopInc M τ) {i : Nat} {e0 e1 : PEv} {v0 v1 : Nat}
    (h0 : (memEv τ)[i]? = some e0) (h1 : (memEv τ)[i + 1]? = some e1) (hr0 : ldRet (Y : Int) e0 = some v0)
    (hr1 : ldRet (X : Int) e1 = some v1) (hs : src0 e0 ≠ 0) :
    v1 = (v0 + (idxOf X M (src0 e1) - idxOf Y M (src0 e0))) % 2 ^ 32 := by
  obtain ⟨-, -, -, hv0, hv1, hle⟩ := hq i e0 e1 v0 v1 h0 h1 hr0 hr1 hs
  rw [hv0, hv1]
  unfold wv
  rw [Nat.mod_add_mod]
  congr 1
  omega

/-! ## 5. Counting messages -/

def cntA (a : Int) (M : List PMsg) (k : Nat) : Nat := ((M.take k).filter (fun m => decide (m.pa = a))).length

theorem idxOf_eq (a : Int) (M : List PMsg) (t : Nat) : idxOf a M t = cntA a M (t - 1) := rfl

theorem cntA_succ (a : Int) (M : List PMsg) (k : Nat) :
    cntA a M (k + 1) = cntA a M k + ((M[k]?.toList).filter (fun m => decide (m.pa = a))).length := by
  unfold cntA; rw [List.take_add_one, List.filter_append, List.length_append]

theorem cntA_hit {a : Int} {M : List PMsg} {k : Nat} {m : PMsg} (hm : M[k]? = some m) (hpa : m.pa = a) :
    cntA a M (k + 1) = cntA a M k + 1 := by
  rw [cntA_succ, hm]; simp [hpa]

theorem cntA_miss {a : Int} {M : List PMsg} {k : Nat} (h : ∀ m, M[k]? = some m → m.pa ≠ a) :
    cntA a M (k + 1) = cntA a M k := by
  rw [cntA_succ]
  cases hm : M[k]? with
  | none => simp
  | some m => simp [h m hm]

theorem cntA_gap {a : Int} {M : List PMsg} (k : Nat) :
    ∀ d, (∀ k', k ≤ k' → k' < k + d → ∀ m, M[k']? = some m → m.pa ≠ a) → cntA a M (k + d) = cntA a M k
  | 0, _ => rfl
  | d + 1, h => by
    rw [← Nat.add_assoc, cntA_miss (h (k + d) (by omega) (by omega)),
      cntA_gap k d (fun k' h1 h2 => h k' h1 (by omega))]

/-- **THE INDEX IS THE ITERATION NUMBER**: if the messages to `a` are exactly the timestamps `f 0 < f 1 < … < f (n-1)`,
then the message at `f i` has index `i`. -/
theorem idx_at {a : Int} {M : List PMsg} {f : Nat → Nat} {n : Nat}
    (hpos : ∀ j, j < n → 0 < f j) (hmono : ∀ i j, i < j → j < n → f i < f j)
    (hcov : ∀ (k : Nat) (m : PMsg), M[k]? = some m → m.pa = a → ∃ j, j < n ∧ f j = k + 1)
    (hmsg : ∀ j, j < n → ∃ m, M[f j - 1]? = some m ∧ m.pa = a) :
    ∀ i, i < n → idxOf a M (f i) = i
  | 0, h0 => by
    have hgap : ∀ k', 0 ≤ k' → k' < 0 + (f 0 - 1) → ∀ m, M[k']? = some m → m.pa ≠ a := by
      intro k' _ hk m hm hpa
      obtain ⟨j, hj, hfj⟩ := hcov k' m hm hpa
      rcases Nat.eq_zero_or_pos j with rfl | hjp
      · omega
      · have := hmono 0 j hjp hj; omega
    rw [idxOf_eq, show f 0 - 1 = 0 + (f 0 - 1) by omega, cntA_gap 0 _ hgap]
    rfl
  | i + 1, hi => by
    have ih := idx_at hpos hmono hcov hmsg i (by omega)
    have hlt := hmono i (i + 1) (by omega) hi
    have hp := hpos i (by omega)
    obtain ⟨m, hm, hpa⟩ := hmsg i (by omega)
    have hgap : ∀ k', f i - 1 + 1 ≤ k' → k' < f i - 1 + 1 + (f (i + 1) - 1 - f i) →
        ∀ m', M[k']? = some m' → m'.pa ≠ a := by
      intro k' h1 h2 m' hm' hpa'
      obtain ⟨j, hj, hfj⟩ := hcov k' m' hm' hpa'
      rcases Nat.lt_or_ge j i with hji | hji
      · have := hmono j i hji (by omega); omega
      · rcases Nat.lt_or_ge (i + 1) j with hji' | hji'
        · have := hmono (i + 1) j hji' hj; omega
        · rcases (by omega : j = i ∨ j = i + 1) with rfl | rfl <;> omega
    rw [idxOf_eq, show f (i + 1) - 1 = (f i - 1 + 1) + (f (i + 1) - 1 - f i) by omega, cntA_gap _ _ hgap,
      cntA_hit hm hpa]
    rw [idxOf_eq] at ih
    omega

/-- The index over hart 0's entries of one parity (`p = 0`: data, `p = 1`: flag). -/
def fP (ev : Trace) (p j : Nat) : Nat := ((ev[2 * j + p]?).map tsOf).getD 0

theorem sh0_par {ev : Trace} (hQ : Q0 ev) {p : Nat} (hp : p < 2) {j : Nat} {e : PEv}
    (he : ev[2 * j + p]? = some e) :
    ∃ t asrc, 0 < t ∧ e = (LStore false false (if p = 0 then (X : Int) else Y) (toBytes (rv j) 4) asrc [.DReg 6], some t) := by
  have hs := hQ.1 _ _ he
  match p, hp with
  | 0, _ =>
    have h := hs.1 (by omega)
    rw [show (2 * j + 0) / 2 = j by omega] at h
    obtain ⟨t, ht, rfl⟩ := h
    exact ⟨t, _, ht, rfl⟩
  | 1, _ =>
    have h := hs.2 (by omega)
    rw [show (2 * j + 1) / 2 = j by omega] at h
    obtain ⟨t, ht, rfl⟩ := h
    exact ⟨t, _, ht, rfl⟩

theorem XY_ne : (X : Int) ≠ Y := by simp [Weak.Prom.Ref.Lit.X, Weak.Prom.Ref.Lit.Y]

/-- **The index of hart 0's `j`-th store of parity `p` is `j`** (from `Q0` and the message classification). -/
theorem idx_par {M : List PMsg} {ev : Trace} (hQ0 : Q0 ev)
    (hcls : ∀ (k : Nat) (m : PMsg), M[k]? = some m →
      ∃ j e, ev[j]? = some e ∧ tsOf e = k + 1 ∧ m.pa = (if j % 2 = 0 then (X : Int) else Y))
    (hmsg : ∀ j e, ev[j]? = some e → ∃ m, M[tsOf e - 1]? = some m ∧ m.pa = (if j % 2 = 0 then (X : Int) else Y))
    {p : Nat} (hp : p < 2) {j : Nat} {e : PEv} (he : ev[2 * j + p]? = some e) :
    idxOf (if p = 0 then (X : Int) else Y) M (tsOf e) = j := by
  have hlen : 2 * j + p < ev.length := (List.getElem?_eq_some_iff.1 he).1
  have hf : fP ev p j = tsOf e := by simp [fP, he]
  rw [← hf]
  have hget : ∀ i, 2 * i + p < ev.length → ∃ x, ev[2 * i + p]? = some x ∧ fP ev p i = tsOf x :=
    fun i hi => ⟨_, List.getElem?_eq_getElem hi, by simp [fP, List.getElem?_eq_getElem hi]⟩
  have hpar : ∀ i, ((2 * i + p) % 2 = 0) ↔ (p = 0) := fun i => by omega
  refine idx_at (f := fP ev p) (n := (ev.length + 1 - p) / 2) (fun i hi => ?_) (fun i i' hii hi' => ?_)
    (fun k m hm hpa => ?_) (fun i hi => ?_) j (by omega)
  · obtain ⟨x, hx, hfx⟩ := hget i (by omega)
    obtain ⟨t, _, ht, rfl⟩ := sh0_par hQ0 hp hx
    rw [hfx]; exact ht
  · obtain ⟨x, hx, hfx⟩ := hget i (by omega)
    obtain ⟨x', hx', hfx'⟩ := hget i' (by omega)
    rw [hfx, hfx']
    exact hQ0.2.1 _ _ _ _ hx hx' (by omega) (by omega)
  · obtain ⟨j', e', he', hts, hpa'⟩ := hcls k m hm
    have hjl := (List.getElem?_eq_some_iff.1 he').1
    have hh : (if p = 0 then (X : Int) else Y) = (if j' % 2 = 0 then (X : Int) else Y) := hpa.symm.trans hpa'
    have hj'p : j' % 2 = p := by
      by_cases h1 : p = 0 <;> by_cases h2 : j' % 2 = 0 <;>
        simp [h1, h2, Weak.Prom.Ref.Lit.X, Weak.Prom.Ref.Lit.Y] at hh <;> omega
    refine ⟨j' / 2, by omega, ?_⟩
    show ((ev[2 * (j' / 2) + p]?).map tsOf).getD 0 = k + 1
    rw [show 2 * (j' / 2) + p = j' by omega, he']
    simpa using hts
  · obtain ⟨x, hx, hfx⟩ := hget i (by omega)
    obtain ⟨m, hm, hpa⟩ := hmsg _ _ hx
    rw [hfx]
    refine ⟨m, hm, ?_⟩
    simp only [hpar i] at hpa
    exact hpa

/-! ## 6. Bytes of a word -/

theorem cover_pa {m : PMsg} {a : Int} (ha : a = X ∨ a = Y) (hpa : m.pa = X ∨ m.pa = Y) (hd : m.data.length = 4)
    {b : Int} (hb' : ∃ j : Nat, j < 4 ∧ b = a + j) (hb : (m.byteAt b).isSome = true) : m.pa = a := by
  obtain ⟨j, hj, rfl⟩ := hb'
  rw [byteAt_eq] at hb
  split at hb
  · next hle =>
    have hlt : (a + j - m.pa).toNat < m.data.length := by
      rcases Nat.lt_or_ge (a + j - m.pa).toNat m.data.length with h | h
      · exact h
      · rw [List.getElem?_eq_none h] at hb; cases hb
    rw [hd] at hlt
    simp only [Weak.Prom.Ref.Lit.X, Weak.Prom.Ref.Lit.Y] at ha hpa
    omega
  · cases hb

/-- One byte of a single-copy-atomic word read whose byte 0 read the message at `k + 1`: it read the same message. -/
theorem byte_same {M : List PMsg} {img : Image} {a b : Int} {k T : Nat} {m : PMsg} {j : Nat} (hj : j < 4)
    (hab : b = a + j)
    (hcov : ∀ (k' : Nat) (m' : PMsg), M[k']? = some m' → (m'.byteAt b).isSome = true → m'.pa = a ∧ m'.data.length = 4)
    (hm : M[k]? = some m) (hpa : m.pa = a) (hd : m.data.length = 4)
    {t : Nat} {v : BitVec 8} (hb : memByte img M t b = some v) (hT : k + 1 ≤ T) (htT : t ≤ T)
    (hw : ¬ writesIn M b t T) (hw0 : ¬ writesIn M a (k + 1) T) : m.byteAt b = some v := by
  subst hab
  have hmb : (m.byteAt (a + j)).isSome = true := by
    rw [byteAt_eq, hpa, if_pos (by omega)]
    rw [List.getElem?_eq_getElem (by rw [hd]; omega)]; rfl
  rcases Nat.lt_trichotomy t (k + 1) with hlt | heq | hgt
  · exact absurd (writesIn_of hm hmb hlt hT) hw
  · subst heq
    obtain ⟨m', hm', hb'⟩ := memByte_succ hb
    rw [hm] at hm'; cases hm'
    exact hb'
  · obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
    obtain ⟨m', hm', hb'⟩ := memByte_succ hb
    obtain ⟨hpa', hd'⟩ := hcov t' m' hm' (by rw [hb']; rfl)
    have hm0 : (m'.byteAt a).isSome = true := by
      rw [byteAt_eq, hpa', if_pos (Int.le_refl _), Int.sub_self]
      rw [List.getElem?_eq_getElem (by rw [hd']; decide)]; rfl
    exact absurd (writesIn_of hm' hm0 hgt htT) hw0

theorem byteAt_word {m : PMsg} {a : Int} {w : Nat} (hpa : m.pa = a) (hd : m.data = toBytes w 4) (j : Nat)
    {b : Int} (hb : b = a + j) : m.byteAt b = (toBytes w 4)[j]? := by
  rw [byteAt_pd hpa hd, if_pos (by omega), show (b - a).toNat = j by omega]

/-- **A single-copy-atomic word read whose byte 0 read the message `toBytes w 4` returns `w mod 2^32`.** -/
theorem word_read {M : List PMsg} {img : Image} {a : Int} {k w : Nat} {m : PMsg}
    (hcov : ∀ b, (∃ j : Nat, j < 4 ∧ b = a + j) → ∀ (k' : Nat) (m' : PMsg), M[k']? = some m' → (m'.byteAt b).isSome = true →
      m'.pa = a ∧ m'.data.length = 4)
    (hm : M[k]? = some m) (hpa : m.pa = a) (hd : m.data = toBytes w 4)
    {t1 t2 t3 : Nat} {v0 v1 v2 v3 : BitVec 8}
    (hrd : bytesAll (fun a t v => memByte img M t a = some v) a [(k + 1, v0), (t1, v1), (t2, v2), (t3, v3)])
    (hsca : scaP M a [(k + 1, v0), (t1, v1), (t2, v2), (t3, v3)]) :
    obsOf [(k + 1, v0), (t1, v1), (t2, v2), (t3, v3)] = w % 2 ^ 32 := by
  obtain ⟨r0, r1, r2, r3, -⟩ := hrd
  obtain ⟨s0, s1, s2, s3, -⟩ := hsca
  simp only [bytesMax] at s0 s1 s2 s3
  have hdl : m.data.length = 4 := by rw [hd]; rfl
  have e0 : a + 0 = a + ((0 : Nat) : Int) := by omega
  have e1 : a + 1 = a + ((1 : Nat) : Int) := by omega
  have e2 : a + 1 + 1 = a + ((2 : Nat) : Int) := by omega
  have e3 : a + 1 + 1 + 1 = a + ((3 : Nat) : Int) := by omega
  have c0 := hcov a ⟨0, by decide, by omega⟩
  have c1 := hcov (a + 1) ⟨1, by decide, e1⟩
  have c2 := hcov (a + 1 + 1) ⟨2, by decide, e2⟩
  have c3 := hcov (a + 1 + 1 + 1) ⟨3, by decide, e3⟩
  have b0 := byte_same (j := 0) (by decide) (by omega) c0 hm hpa hdl r0 (by omega) (by omega) s0 s0
  have b1 := byte_same (j := 1) (by decide) e1 c1 hm hpa hdl r1 (by omega) (by omega) s1 s0
  have b2 := byte_same (j := 2) (by decide) e2 c2 hm hpa hdl r2 (by omega) (by omega) s2 s0
  have b3 := byte_same (j := 3) (by decide) e3 c3 hm hpa hdl r3 (by omega) (by omega) s3 s0
  rw [byteAt_word (b := a) hpa hd 0 (by omega), toBytes4] at b0
  rw [byteAt_word hpa hd 1 e1, toBytes4] at b1
  rw [byteAt_word hpa hd 2 e2, toBytes4] at b2
  rw [byteAt_word hpa hd 3 e3, toBytes4] at b3
  simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.some.injEq] at b0 b1 b2 b3
  subst b0 b1 b2 b3
  exact obs4 w _ _ _ _

/-! ## 7. The glue (from A0's exports only) -/

section glue

variable {run : PFRun LP Unit} {M : List PMsg}

/-- **Every message is hart 0's**: entry `j` of its memory entries, iteration `j / 2`'s data (even) or flag (odd)
word (A0 (ii), (iii), (v)). -/
theorem msg_cls (hQ : ∀ h, Qs M h (memEv (run.trace h)))
    (hpart : ∀ t, 1 ≤ t → t ≤ M.length → exU (fun h => t ∈ run.fulfils h ∧ tidAt M t = some h))
    (hwf : run.traceWf M) {k : Nat} {m : PMsg} (hm : M[k]? = some m) :
    ∃ j e, (memEv (run.trace 0))[j]? = some e ∧ tsOf e = k + 1 ∧
      m.pa = (if j % 2 = 0 then (X : Int) else Y) ∧ m.data = toBytes (rv (j / 2)) 4 := by
  obtain ⟨h, e, he, het, hlw⟩ := kit_writer hpart hwf hm
  match h, he with
  | 0, he =>
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 he
    have hs := (hQ 0 : Q0 _).1 j e hj
    refine ⟨j, e, hj, by simp [tsOf, het], ?_⟩
    rcases Nat.mod_two_eq_zero_or_one j with hp | hp
    · obtain ⟨t, _, rfl⟩ := hs.1 hp
      simp only [labelWrite, Option.some.injEq, Prod.mk.injEq] at hlw
      rw [if_pos hp]; exact ⟨hlw.1.symm, hlw.2.symm⟩
    · obtain ⟨t, _, rfl⟩ := hs.2 hp
      simp only [labelWrite, Option.some.injEq, Prod.mk.injEq] at hlw
      rw [if_neg (by omega)]; exact ⟨hlw.1.symm, hlw.2.symm⟩
  | 1, he =>
    rcases (hQ 1).1 e he with ⟨_, rfl, _⟩ | ⟨_, rfl, _⟩ <;> cases het
  | n + 2, he =>
    have h0 : memEv (run.trace (n + 2)) = [] := hQ (n + 2)
    rw [h0] at he; cases he

/-- Hart 0's entry `j` is a message: iteration `j / 2`'s word at DATA (even) or FLAG (odd). -/
theorem st_msg (hQ0 : Q0 (memEv (run.trace 0))) (hwf : run.traceWf M) {j : Nat} {e : PEv}
    (he : (memEv (run.trace 0))[j]? = some e) :
    ∃ m, M[tsOf e - 1]? = some m ∧ m.pa = (if j % 2 = 0 then (X : Int) else Y) ∧ m.data = toBytes (rv (j / 2)) 4 := by
  have hs := hQ0.1 j e he
  have hm := List.mem_of_getElem? he
  rcases Nat.mod_two_eq_zero_or_one j with hp | hp
  · obtain ⟨t, _, rfl⟩ := hs.1 hp
    obtain ⟨m, h1, h2, h3⟩ := kit_msg hwf hm rfl rfl
    exact ⟨m, h1, by rw [if_pos hp]; exact h2, h3⟩
  · obtain ⟨t, _, rfl⟩ := hs.2 hp
    obtain ⟨m, h1, h2, h3⟩ := kit_msg hwf hm rfl rfl
    exact ⟨m, h1, by rw [if_neg (by omega)]; exact h2, h3⟩

/-- **THE READER'S PAIRS** (plan §2 steps 1–6 for MP, per iteration, with indices): the flag load's message is
iteration `k`'s flag store (index `k`), which sits above iteration `k`'s data store (hart 0's Ψ); the data load's
byte-0 source is therefore at or above that data store (hart 1's Ψ: no data write between its source and the flag
load's), so it is iteration `k' ≥ k`'s data store (index `k'`); both loads are single-copy atomic, so they return
`wv k` and `wv k'`. -/
theorem reader_ok (hQ : ∀ h, Qs M h (memEv (run.trace h))) (hnc : noCmo M)
    (hpart : ∀ t, 1 ≤ t → t ≤ M.length → exU (fun h => t ∈ run.fulfils h ∧ tidAt M t = some h))
    (hwf : run.traceWf M) : qLoopInc M (run.trace 1) := by
  intro i e0 e1 v0 v1 h0 h1 hr0 hr1 hs0
  have hm0 := List.mem_of_getElem? h0
  have hm1 := List.mem_of_getElem? h1
  have hQ1 : Q1 M (memEv (run.trace 1)) := hQ 1
  have hQ0 : Q0 (memEv (run.trace 0)) := hQ 0
  have hcls : ∀ (k : Nat) (m : PMsg), M[k]? = some m → ∃ j e, (memEv (run.trace 0))[j]? = some e ∧ tsOf e = k + 1 ∧
      m.pa = (if j % 2 = 0 then (X : Int) else Y) := fun k m hm =>
    let ⟨j, e, h1, h2, h3, _⟩ := msg_cls hQ hpart hwf hm; ⟨j, e, h1, h2, h3⟩
  have hmsg : ∀ j e, (memEv (run.trace 0))[j]? = some e →
      ∃ m, M[tsOf e - 1]? = some m ∧ m.pa = (if j % 2 = 0 then (X : Int) else Y) := fun j e he =>
    let ⟨m, h1, h2, _⟩ := st_msg hQ0 hwf he; ⟨m, h1, h2⟩
  have hsh : ∀ (k : Nat) (m : PMsg), M[k]? = some m → (m.pa = X ∨ m.pa = Y) ∧ m.data.length = 4 := fun k m hm => by
    obtain ⟨j, e, _, _, hpa, hd⟩ := msg_cls hQ hpart hwf hm
    refine ⟨?_, by rw [hd]; rfl⟩
    split at hpa
    · exact .inl hpa
    · exact .inr hpa
  have hcov : ∀ (a : Int), (a = (X : Int) ∨ a = (Y : Int)) → ∀ b, (∃ j : Nat, j < 4 ∧ b = a + j) → ∀ (k' : Nat) (m' : PMsg), M[k']? = some m' →
      (m'.byteAt b).isSome = true → m'.pa = a ∧ m'.data.length = 4 := fun a ha b hb k' m' hm' hbs =>
    ⟨cover_pa ha (hsh k' m' hm').1 (hsh k' m' hm').2 hb hbs, (hsh k' m' hm').2⟩
  obtain ⟨tvs0, rfl, hl0, hsc0⟩ : ldFs M e0 := by
    rcases hQ1.1 e0 hm0 with hh | ⟨tvs, rfl, _, _⟩
    · exact hh
    · simp [ldRet, Weak.Prom.Ref.Lit.X, Weak.Prom.Ref.Lit.Y] at hr0
  obtain ⟨tvs1, rfl, hl1, hsc1⟩ : ldDs M e1 := by
    rcases hQ1.1 e1 hm1 with ⟨tvs, rfl, _, _⟩ | hh
    · simp [ldRet, Weak.Prom.Ref.Lit.X, Weak.Prom.Ref.Lit.Y] at hr1
    · exact hh
  have hord := hQ1.2 i _ _ h0 h1 ⟨tvs0, rfl, hl0⟩ ⟨tvs1, rfl, hl1⟩ hnc
  simp only [ldRet, if_true, Option.some.injEq] at hr0 hr1
  subst hr0 hr1
  have hrd0 := kit_read hwf hm0 (base := (Y : Int)) (tvs := tvs0) rfl
  have hrd1 := kit_read hwf hm1 (base := (X : Int)) (tvs := tvs1) rfl
  have hsc0 := hsc0 hnc
  have hsc1 := hsc1 hnc
  match tvs0, hl0, tvs1, hl1 with
  | [(t0, a0), (u1, a1), (u2, a2), (u3, a3)], _, [(d0, b0), (w1, b1), (w2, b2), (w3, b3)], _ =>
    simp only [src0_ld] at hs0 hord ⊢
    -- the flag message: iteration `qF`'s flag store
    obtain ⟨k0, rfl⟩ : ∃ k0, t0 = k0 + 1 := ⟨t0 - 1, by omega⟩
    obtain ⟨mF, hmF, hbF⟩ := memByte_succ hrd0.1
    have hpaF : mF.pa = Y := cover_pa (b := (Y : Int)) (.inr rfl) (hsh k0 mF hmF).1 (hsh k0 mF hmF).2 ⟨0, by decide, by simp⟩
      (by rw [hbF]; rfl)
    obtain ⟨jF, eF, heF, htsF, hpaF', hdF⟩ := msg_cls hQ hpart hwf hmF
    have hjF : jF % 2 = 1 := by
      rcases Nat.mod_two_eq_zero_or_one jF with h | h
      · rw [if_pos h, hpaF] at hpaF'; exact absurd hpaF'.symm XY_ne
      · exact h
    have heF' : (memEv (run.trace 0))[2 * (jF / 2) + 1]? = some eF := by
      rw [show 2 * (jF / 2) + 1 = jF by omega]; exact heF
    have hiF := idx_par hQ0 hcls hmsg (p := 1) (by decide) heF'
    rw [if_neg (by decide), htsF] at hiF
    have hvF := word_read (hcov _ (.inr rfl)) hmF hpaF hdF hrd0 hsc0
    -- iteration `qF`'s data store is below its flag store
    have hlenF := (List.getElem?_eq_some_iff.1 heF).1
    obtain ⟨eD, heD⟩ : ∃ x, (memEv (run.trace 0))[2 * (jF / 2)]? = some x :=
      ⟨_, List.getElem?_eq_getElem (by omega)⟩
    have hDF := hQ0.2.2 _ _ _ heD heF'
    rw [htsF] at hDF
    obtain ⟨mD, hmD, hpaD, -⟩ := st_msg hQ0 hwf heD
    rw [if_pos (by omega)] at hpaD
    have hD0 : 0 < tsOf eD := by
      obtain ⟨t, _, ht, rfl⟩ := sh0_par hQ0 (p := 0) (j := jF / 2) (e := eD) (by decide) (by simpa using heD)
      exact ht
    have hmDb : (mD.byteAt (X : Int)).isSome = true := by
      rw [byteAt_eq, hpaD, if_pos (Int.le_refl _), Int.sub_self]
      rw [List.getElem?_eq_getElem (by rw [(hsh _ _ hmD).2]; decide)]; rfl
    -- the data load's byte 0 is at or above it (fence r,r)
    have hDd : tsOf eD ≤ d0 := by
      rcases Nat.lt_or_ge d0 (tsOf eD) with h | h
      · exact absurd (writesIn_of hmD hmDb (by omega) (by omega)) hord
      · exact h
    obtain ⟨kD, rfl⟩ : ∃ kD, d0 = kD + 1 := ⟨d0 - 1, by omega⟩
    obtain ⟨mX, hmX, hbX⟩ := memByte_succ hrd1.1
    have hpaX : mX.pa = X := cover_pa (b := (X : Int)) (.inl rfl) (hsh kD mX hmX).1 (hsh kD mX hmX).2 ⟨0, by decide, by simp⟩
      (by rw [hbX]; rfl)
    obtain ⟨jX, eX, heX, htsX, hpaX', hdX⟩ := msg_cls hQ hpart hwf hmX
    have hjX : jX % 2 = 0 := by
      rcases Nat.mod_two_eq_zero_or_one jX with h | h
      · exact h
      · rw [if_neg (by omega), hpaX] at hpaX'; exact absurd hpaX' XY_ne
    have heX' : (memEv (run.trace 0))[2 * (jX / 2) + 0]? = some eX := by
      rw [show 2 * (jX / 2) + 0 = jX by omega]; exact heX
    have hiX := idx_par hQ0 hcls hmsg (p := 0) (by decide) heX'
    rw [if_pos rfl, htsX] at hiX
    have hvX := word_read (hcov _ (.inl rfl)) hmX hpaX hdX hrd1 hsc1
    -- the index order
    have hle : jF / 2 ≤ jX / 2 := by
      rcases Nat.lt_or_ge (jX / 2) (jF / 2) with h | h
      · have := hQ0.2.1 _ _ _ _ heX' heD (by omega) (by omega)
        omega
      · exact h
    refine ⟨by omega, ⟨mF, by simpa using hmF, hpaF⟩, ⟨mX, by simpa using hmX, hpaX⟩, ?_, ?_, ?_⟩
    · rw [hiF, hvF, rv_wv]
    · rw [hiX, hvX, rv_wv]
    · rw [hiF, hiX]; exact hle

end glue

end Weak.Prom.PF.LoopInc
